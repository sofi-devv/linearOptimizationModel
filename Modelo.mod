# ------------ Conjuntos ------------- #

set J := 1..4;  # Aleaciones
set L := 1..6;  # Meses
set K := 1..4;  # Plantas
set I := 1..4;  # Materias primas
set C := 1..5;  # Centros de distribución
set M := 1..10; # Mayoristas
set P := 1..5;  # Políticas
set A{C};       # Subconjunto de centros de arrendamiento asociados con cada centro c

# ------------ Parámetros ------------- #

param PMIN{I, J};        # Porcentaje mínimo permitido de la materia prima i en la aleación j
param PMAX{I, J};        # Porcentaje máximo permitido de la materia prima i en la aleación j
param PT{I};             # Precio por tonelada de la materia prima i
param CPP{K};            # Capacidad de producción mensual de la planta k
param CAP{K};            # Capacidad de almacenamiento mensual de la planta k
param CSPP{K};           # Costo de producción por tonelada en la planta k
param D{J, M, L};        # Demanda de la aleación j del mayorista m en el mes l
param CFC{C};            # Costo semestral de arriendo del centro c
param CAC{C};            # Capacidad de almacenamiento mensual del centro c
param CSAC{C};           # Costo de almacenamiento mensual por tonelada en el centro c
param CSAP{K};           # Costo de almacenamiento por tonelada mensual en la planta k
param CTPC{K, C};        # Costo de transporte por tonelada desde la planta k al centro c
param CTCM{C, M};        # Costo de transporte por tonelada desde el centro c al mayorista m
param BCM{C, M};         # Binario que indica si el centro c puede despachar al mayorista m
param PE{J, M};          # Penalización por tonelada de la aleación j no despachada al mayorista m
param MUY;               # Número muy grande

# ------------ Variables de decisión ------------- #

var Pol{P} binary;        # Variable binaria que indica si la política p es cumplida (1) o no (0)
var U{C} binary;          # Indica si el centro de distribución c se arrienda para todo el horizonte (1) o no (0)
var X{I, J, K, L} >= 0;   # Toneladas de materia prima i utilizadas para producir la aleación j en la planta k durante el mes l
var T{J, C, M, L} >= 0;   # Cantidad de la aleación j enviada desde el centro de distribución c al mayorista m en el mes l
var W{J, C, L} >= 0;      # Cantidad de la aleación j almacenada en el centro de distribución c al final del mes l (toneladas)
var Y{J, K, C, L} >= 0;   # Cantidad de la aleación j enviada desde la planta k al centro de distribución c en el mes l (toneladas)
var S{J, K, L} >= 0;      # Cantidad de la aleación j almacenada en la planta k al final del mes l (toneladas)
var R{J, M, L} >= 0;      # Cantidad de aleación j que se deja de enviar al mayorista m en el mes l
var costOP;               # Costo máximo de operación de una planta

# ------------ Función Objetivo ------------- #

minimize z: costOP;

# ------------ Restricciones ------------- #


# Proporciones de materiales y capacidad de producción
s.t. Proporcion_Min{h in I, j in J, k in K, l in L}:
    X[h, j, k, l] >= sum{i in I} PMIN[h, j] * X[i, j, k, l];

s.t. Proporcion_Max{h in I, j in J, k in K, l in L}:
    X[h, j, k, l] <= sum{i in I} PMAX[h, j] * X[i, j, k, l];

s.t. Res_Cap_Produc{k in K, l in L}:
    sum{i in I, j in J} X[i, j, k, l] <= CPP[k];

# Inventario Plantas
s.t. Inv_Primer_Mes_Plantas{k in K, j in J}:
    S[j, k, 1] = sum{i in I} X[i, j, k, 1] - sum{c in C} Y[j, k, c, 1];

s.t. Inv_Demas_Mes_Plantas{k in K, j in J, l in L: l > 1}:
    S[j, k, l] = S[j, k, l - 1] + sum{i in I} X[i, j, k, l] - sum{c in C} Y[j, k, c, l];

# Inventario Centros de distribución
s.t. Inv_Primer_Mes_Centros{c in C, j in J}:
    W[j, c, 1] = sum{k in K} Y[j, k, c, 1] - sum{m in M} T[j, c, m, 1];

s.t. Inv_Demas_Mes_Centros{c in C, j in J, l in L: l > 1}:
    W[j, c, l] = W[j, c, l - 1] + sum{k in K} Y[j, k, c, l] - sum{m in M} T[j, c, m, l];

# Capacidad de almacenamiento en plantas
s.t. Cap_Almacen_Plantas{k in K, l in L}:
    sum{j in J} S[j, k, l] <= CAP[k];

# Capacidad de almacenamiento en centros de distribución (además debe existir el centro de almacenamiento)
s.t. Cap_Almacen_Centros{c in C, l in L}:
    sum{j in J} W[j, c, l] <= CAC[c] * U[c];

# Posibilidad de despachar a un mayorista
s.t. Posible_Despacho_Mayorista{c in C, m in M, l in L, j in J}:
    T[j, c, m, l] <= BCM[c, m] * MUY;

# No se puede despachar desde un centro de distribución que no existe
s.t. Centros_Distribucion_Existen{c in C, l in L}:
    sum{j in J, m in M} T[j, c, m, l] <= U[c] * MUY;

# Si se arrienda se despacha
s.t. Despacho_Solo_Si_Arrendado{l in L, c in C}:
    sum{m in M, j in J} T[j, c, m, l] >= U[c];

# Demanda
s.t. Demanda{j in J, m in M, l in L}:
    D[j, m, l] - sum{c in C} T[j, c, m, l] = R[j, m, l];

# No superar demanda
s.t. Demanda_Max{m in M, l in L, j in J}: 
    sum{c in C} T[j, c, m, l] <= D[j, m, l];


# Costo de operación de plantas (costo compra, producción, almacenamiento, distribución)
s.t. CostoOperacionPlantas{k in K}:
    costOP >= sum{i in I, j in J, l in L} (PT[i] * X[i, j, k, l] + CSPP[k] * X[i, j, k, l]) +
             sum{j in J, l in L} S[j, k, l] * CSAP[k] +
             sum{j in J, c in C, l in L} Y[j, k, c, l] * CTPC[k, c];
# Políticas
# 1. Grupo de mayoristas cuya demanda se debe satisfacer en su totalidad
s.t. Demanda_Mayoristas_Tot{l in L, j in J, m in {2, 3, 5, 7, 9}}:
    sum{c in C} T[j, c, m, l] >= D[j, m, l] - MUY * (1 - Pol[1]);

# 2. Restricción de acuerdos de arriendo entre centros de distribución
s.t. AcuerdosArrendatarios{c in C, s in A[c]}:
    U[c] <= U[s] + MUY * (1 - Pol[2]);

# 3. Restricción del 95% de la demanda por mayorista
s.t. Demanda95{m in M, l in L, j in J}:
    sum{c in C} T[j, c, m, l] >= 0.95 * D[j, m, l] - MUY * (1 - Pol[3]);

# 4. Restricción de pago de arriendos hasta 1700
s.t. PagoArriendos:
    sum{c in C} U[c] * CFC[c] <= 1700 + MUY * (1 - Pol[4]);

# 5. Costo de demanda faltante
s.t. Costo_Demanda_Faltante {l in L}:
    sum{j in J, m in M} PE[j, m] * R[j, m, l] <=
    0.1 * (
        sum{k in K} (
            sum{i in I, j in J} X[i, j, k, l] * PT[i] +   # Costo de compra de materias primas
            sum{j in J, i in I} X[i, j, k, l] * CSPP[k] + # Costo de producción en la planta
            sum{j in J} S[j, k, l] * CSAP[k] +            # Costo de almacenamiento en la planta
            sum{j in J, c in C} Y[j, k, c, l] * CTPC[k, c]# Costo transporte planta -> centro de distribución
        ) +
        sum{c in C, j in J} W[j, c, l] * CSAC[c] +        # Costo almacenamiento centros de distribución
        sum{j in J, c in C, m in M} T[j, c, m, l] * CTCM[c, m] # Costo transporte centro de distribución -> mayorista
       + sum{j in J, m in M} PE[j, m] * R[j, m, l] # penalización
    ) + MUY * (1 - Pol[5]);




# Cumplimiento mínimo de políticas
s.t. Cumplimiento_Minimo:
    sum{p in P} Pol[p] >= 3;

solve;

data;

param PMIN:	1	2	3	4:=
1			0.15	0.05	0	0.30
2			0.05	0.05	0.2	0.15
3			0.1	0.2	0.25	0.2
4			0.3	0	0.25	0.2;

param PMAX:	1	2	3	4:=
1			0.4	0.5	0.25	0.4
2			0.35	0.3	0.45	0.35
3			0.15	0.25	0.65	0.3
4			0.3	0.15	0.6	0.6;

param PT:=
1	140
2	173
3	101
4	188;

param CPP:=
1	342
2	362
3	336
4	372;

param CSPP:=
1	130
2	107
3	80
4	120;

param CAP:=
1	72
2	71
3	67
4	67;

param CSAP:=
1	180
2	170
3	190
4	104;


param D:=[1,*,*]: 1 2 3 4 5 6:=

1 36 32 36 44 31 38

2 34 31 39 34 38 34

3 41 30 44 36 32 29

4 32 39 28 34 32 34

5 42 45 26 26 35 31

6 43 35 37 35 42 35

7 40 35 20 37 30 31

8 23 34 31 34 32 38

9 36 26 32 42 32 30

10 28 40 27 33 30 35



[2,*,*]: 1 2 3 4 5 6:=

1 40 36 34 32 36 39

2 39 34 35 26 33 36

3 38 36 37 37 33 36

4 31 36 26 32 36 40

5 38 44 37 39 35 43

6 42 32 35 44 28 34

7 37 42 34 38 38 36

8 36 36 33 25 36 31

9 33 39 39 34 37 39

10 40 34 34 43 30 39



[3,*,*]: 1 2 3 4 5 6:=

1 44 33 31 51 33 39

2 33 37 39 38 39 34

3 39 39 41 35 45 39

4 33 36 43 38 38 39

5 38 31 31 35 29 36

6 37 40 32 36 32 32

7 36 49 30 43 32 32

8 32 40 44 33 36 28

9 33 39 35 32 25 35

10 41 32 34 37 39 37



[4,*,*]: 1 2 3 4 5 6:=

1 30 33 38 29 34 39

2 40 38 42 33 32 35

3 44 33 35 43 25 28

4 30 41 34 31 40 39

5 32 38 34 42 36 42

6 32 41 41 30 33 38

7 42 38 33 30 29 27

8 29 33 28 39 29 36

9 35 29 35 36 32 40

10 36 34 33 26 35 31;

param CFC:=
1	464
2	696
3	525
4	600
5	480;

param CAC:=
1	37
2	31
3	27
4	47
5	36;

param CSAC:=
1	180
2	140
3	120
4	103
5	130;


param CTPC:	1	2	3	4	5:=
1			92	110	72	110	90
2			71	107	92	106	105
3			68	75	79	71	88
4			74	83	47	94	64;

param CTCM:	1	2	3	4	5	6	7	8	9	10:=
1			74	81	85	65	100000	100000	67	89	67	98
2			81	77	77	100000	104	115	106	99	1000000	100000
3			100000	81	75	61	105	100000	109	100000	94	109
4			90	100000	100000	100000	100000	102	100000	86	52	98
5			100000	79	100000	67	89	100000	107	100000	100000	103;


param BCM:	1	2	3	4	5	6	7	8	9	10:=
1			1	1	1	1	0	0	1	1	1	1
2			1	1	1	0	1	1	1	1	0	0
3			0	1	1	1	1	0	1	0	1	1
4			1	0	0	0	0	1	0	1	1	1
5			0	1	0	1	1	0	1	0	0	1;


param PE:	1	2	3	4	5	6	7	8	9	10:=
1			189	192	225	156	206	188	116	121	370	295
2			420	109	127	240	169	370	390	380	287	291
3			150	213	200	273	160	157	142	228	402	278
4			113	259	102	270	101	470	252	252	207	185;


param MUY:=99999999;


set A[1]:= 3 4;
set A[2]:= 5;
set A[3]:= 1 4;
set A[4]:= 1 3;
set A[5]:= 2;

end;


