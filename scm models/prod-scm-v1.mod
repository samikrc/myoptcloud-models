/* Supply Chain Production Planning */
/*
	In this problem, we find out the optimum amount of each product that needs to be produced at each plant,
	and then shipped at warehouses and then to customers to satisfy customer demands. The model considers
	inventory capacity at each warehouse, inventory (holding) cost at each warehouse, production cost at
	plants, shipment cost between various supply chain levels, and raw material cost.
*/

/* Define sets */
# Product set
set products;
# Planning horizon in months. Have to be an integer set.
set months;
# Plant set
set plants;
# Warehouse set
set whs;
# Customer set
set customers;
# Vendor set
set vendors;
# Raw material set
set rawmats;

/* Define parameters */

# Final price of each product
param price{p in products};
# Customer demand per month
param demand{p in products, m in months, c in customers};
# Production cost
param prodCost{pl in plants, p in products};
# Daily production rate
param prodRate{pl in plants, p in products};
# Production days available per month
param availableProdDays{m in months};
# Inventory holding cost
param invHoldingCost{w in whs, p in products};
# Inventory capacity, in product units. Assumption here is that the products are equivalent in terms of volume.
param invCapacity{w in whs};
# Shipment cost to warehouse
param whsShipCost{pl in plants, w in whs};
# Shipment cost to customer
param custShipCost{w in whs, c in customers};
# Raw material requirement
param rawmatReq{r in rawmats, p in products};
# Raw material cost - includes shipment cost to plants.
param rawmatCost{r in rawmats, v in vendors, pl in plants};

/* Define variables */
# Production at each plant per month
var production{p in products, m in months, pl in plants} integer >= 0;
# Inventory
var inventory{w in whs, p in products, m in months} integer >= 0;
# Actual sales (not required, but easier to extract from the solution)
var sales{p in products, m in months, c in customers} integer >= 0;
# Shipments to warehouse
var whsShipment{w in whs, p in products, m in months, pl in plants} integer >= 0;
# Shipment to customers
var custShipment{w in whs, p in products, m in months, c in customers} integer >= 0;
# Raw material supply 
var rawmatSupply{r in rawmats, m in months, v in vendors, pl in plants} integer >= 0;

/* Define relationships */
var totalRevenue >= 0;
s.t. tr: totalRevenue = sum{p in products, m in months, c in customers} price[p] * sales[p, m, c];
var totalProductionCost >= 0;
s.t. tp: totalProductionCost = sum{p in products, m in months, pl in plants} prodCost[pl, p] * production[p, m, pl];
var totalInvCost >= 0;
s.t. tic: totalInvCost = sum{w in whs, p in products, m in months} invHoldingCost[w, p] * inventory[w, p, m];
var totalWShipmentCost >= 0;
s.t. twsc: totalWShipmentCost = sum{w in whs, p in products, m in months, pl in plants} whsShipCost[pl, w] * whsShipment[w, p, m, pl];
var totalCShipmentCost >= 0;
s.t. tcsc: totalCShipmentCost = sum{w in whs, p in products, m in months, c in customers} custShipCost[w, c] * custShipment[w, p, m, c];
var totalRawMatCost >= 0;
s.t. rrmc: totalRawMatCost = sum{r in rawmats, m in months, v in vendors, pl in plants} rawmatCost[r, v, pl] * rawmatSupply[r, m, v, pl];

/* Define objective function */
maximize profit: totalRevenue - totalProductionCost - totalInvCost - totalWShipmentCost - totalCShipmentCost - totalRawMatCost;

/* Define constraints */
# Production capacity
s.t. ProdCapacity{m in months, pl in plants}: sum{p in products} production[p, m, pl] <= availableProdDays[m] * sum{p in products} prodRate[pl, p];

# Raw material balance
s.t. RawMatBal{r in rawmats, m in months, pl in plants}: sum{p in products} (production[p, m, pl] * rawmatReq[r, p]) <= sum{v in vendors} rawmatSupply[r, m, v, pl];

# Plant production and shipment balance
s.t. PlantProdShipBal{p in products, m in months, pl in plants}: production[p, m, pl] = sum{w in whs} whsShipment[w, p, m, pl];

# Warehouse shipment balance
s.t. WhsShipBal{w in whs, p in products, m in months : m > 1}: sum{pl in plants} whsShipment[w, p, m, pl] + inventory[w, p, m - 1] = sum{c in customers} custShipment[w, p, m, c] + inventory[w, p, m];

# Warehouse initial inventory
s.t. WhsInitialInv{w in whs, p in products, m in months : m = 1}: inventory[w, p, m] = 0;

# Warehouse initial shipment balance
s.t. WhsInitialShipBal{w in whs, p in products, m in months : m = 1}: sum{pl in plants} whsShipment[w, p, m, pl] = sum{c in customers} custShipment[w, p, m, c] + inventory[w, p, m];

# Customer sales balance
s.t. CustSalesBal{p in products, m in months, c in customers}: sum{w in whs} custShipment[w, p, m, c] = sales[p, m, c];

# Maximum inventory
s.t. MaxInventory{w in whs, m in months}: sum{p in products} inventory[w, p, m] <= invCapacity[w];

# Maximum demand
s.t. MaxDemand{p in products, m in months, c in customers}: sales[p, m, c] <= demand[p, m, c];

# Minimum demand, that needs to be fulfilled.
s.t. MinDemand{p in products, m in months, c in customers}: sales[p, m, c] >= 0.5 * demand[p, m, c];

solve;

end;
