/* Supply Chain Production Planning */
/*
	In this problem, we find out the optimum amount of each product that needs to be produced at each plant,
	and then shipped at warehouses and then to customers to satisfy customer demands. The model considers
	inventory capacity at each warehouse, inventory (holding) cost at each warehouse, production cost at
	plants, shipment cost between various supply chain levels, and raw material cost.
*/

/* Define sets */
# Product set
set P;
# Planning horizon in months
set M;
# Plant set
set PL;
# Warehouse set
set W;
# Customer set
set C;
# Vendor set
set V;
# Raw material set
set R;

/* Define parameters */

# Final price of each product
param price{p in P};
# Customer demand per month
param demand{p in P, m in M, c in C};
# Production cost
param prodCost{pl in PL, p in P};
# Daily production rate
param prodRate{pl in PL, p in P};
# Production days available per month
param availableProdDays{m in M};
# Inventory holding cost
param invHoldingCost{w in W, p in P};
# Inventory capacity, in product units. Assumption here is that the products are equivalent in terms of volume.
param invCapacity{w in W};
# Shipment cost to warehouse
param whsShipCost{pl in PL, w in W};
# Shipment cost to customer
param custShipCost{w in W, c in C};
# Raw material requirement
param rawmatReq{r in R, p in P};
# Raw material cost
param rawmatCost{r in R, v in V, pl in PL};

/* Define variables */
# Production at each plant per month
var production{p in P, m in M, pl n PL} >= 0;
# Inventory
var inventory{p in P, m in M, w in W} >= 0;
# Actual sales (not required, but easier to extract from the solution)
var sales{p in P, m in M, c in C} >= 0;
# Shipments to warehouse
var whsShipment{p in P, m in M, pl in PL, w in W} >= 0;
# Shipment to customers
var custShipment{p in P, m in M, w in W, c in C} >= 0;
# Raw material supply 
var rawmatSupply{r in R, m in M, v in V, pl in PL} >= 0;

/* Define relationships */
var totalRevenue >= 0;
s.t. totalRevenue = sum{p in P, m in M, c in C} price[p] * sales[p, m, c];
var totalProductionCost >= 0;
s.t. totalProductionCost = sum{pl in PL, p in P, m in M} prodCost[pl, p] * production[pl, p, m];
var totalInvCost >= 0;
s.t. totalInvCost = sum{w in W, p in P, m in M} invHoldingCost[w, p] * inventory[w, p, m];
var totalWShipmentCost >= 0;
s.t. totalWShipmentCost = sum{p in P, m in M, pl in PL, w in W} whsShipCost[pl, w] * whsShipment[p, m, pl, w];
var totalCShipmentCost >= 0;
s.t. totalCShipmentCost = sum{p in P, m in M, w in W, c in C} custShipCost[w, c] * custShipment[p, m, w, c];
var totalRawMatCost >= 0;
s.t. totalRawMatCost = sum{r in R, v in V, pl in PL, m in M} rawmatCost[r, v, pl] * rawmatSupply[r, v, pl, m];

/* Define objective function */
maximize profit: totalRevenue - totalProductionCost - totalInvCost - totalWShipmentCost - totalCShipmentCost - totalRawMatCost;

/* Define constraints */
# Production capacity
s.t. ProdCapacity{m in M, pl in PL}: sum{p in P} production[p, m, pl] <= availableProdDays[m] * sum{p in P} prodRate[pl, p];

# Raw material balance
s.t. RawMatBal{r in R, m in M, pl in PL}: sum{p in P} (production[p, m, pl] * rawmatReq[r, p]) <= sum{v in V} rawmatSupply[r, m, v, pl];

# Plant production and shipment balance
s.t. PlantProdShipBal{p in P, m in M, pl in PL}: production[p, m, pl] >= sum{w in W} whsShipment[p, m, pl, w];

# Warehouse shipment balance
s.t. WhsShipBal{p in P, m in M, w in W}: sum{pl in PL} whsShipment[p, m, pl, w] + inventory[p, m - 1, w] = sum{c in C} custShipment[p, m, w, c] + inventory[p, m, w];

# Customer sales balance
s.t. CustSalesBal{p in P, m in M, c in C}: sum{w in W} custShipment[p, m, w, c] = sales[p, m, c];

# Maximum inventory
s.t. MaxInventory{m in M, w in W}: sum{p in P} inventory[p, m, w] <= invCapacity[w];

# Maximum demand
s.t. MaxDemand{p in P, m in M, c in C}: sales[p, m, c] <= demand[p, m, c];

# Minimum demand, that needs to be fulfilled.
s.t. MinDemand{p in P, m in M, c in C}: sales[p, m, c] >= 0.5 * demand[p, m, c];

solve;

