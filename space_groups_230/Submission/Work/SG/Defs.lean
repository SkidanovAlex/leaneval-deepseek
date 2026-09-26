import ChallengeDeps

/-! Shared definitions + generated data for the space-groups route (design: Submission/Work/SG/DESIGN.md). -/

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem

/-! Shared definitions for the `space_groups_230` route (see `DESIGN.md`).
Everything is phrased with integer matrices `IMat` acting on coordinate vectors; `E 3` points are
converted with `WithLp.toLp 2` / `.ofLp`. -/

/-- Integer `3 × 3` matrices. -/
abbrev IMat := Matrix (Fin 3) (Fin 3) ℤ

/-- An integer vector viewed as a real coordinate vector. -/
def intVec (n : Fin 3 → ℤ) : Fin 3 → ℝ := fun i => (n i : ℝ)

/-- An integral point group: a finite set of unimodular integer matrices containing `1` and closed
under products (hence a finite subgroup of `GL₃(ℤ)`). -/
def IsIntPointGroup (P : Set IMat) : Prop :=
  P.Finite ∧ (1 : IMat) ∈ P ∧ (∀ A ∈ P, ∀ B ∈ P, A * B ∈ P) ∧ ∀ A ∈ P, IsUnit A.det

/-- `τ` is a cocycle `P → ℝ³/ℤ³` (given by real lifts): `τ(AB) ≡ τ(A) + A τ(B) (mod ℤ³)`. -/
def IsIntCocycle (P : Set IMat) (τ : IMat → Fin 3 → ℝ) : Prop :=
  ∀ A ∈ P, ∀ B ∈ P, ∃ n : Fin 3 → ℤ,
    τ (A * B) = τ A + (A.map (Int.cast : ℤ → ℝ)).mulVec (τ B) + intVec n

/-- The lattice-normalised space group of the datum `(P, τ)`: all affine maps
`x ↦ A x + τ(A) + n` with `A ∈ P`, `n ∈ ℤ³`. -/
def sgSet (P : Set IMat) (τ : IMat → Fin 3 → ℝ) : Set (AffineGroup 3) :=
  {g | ∃ A ∈ P, ∃ n : Fin 3 → ℤ, ∀ x : E 3,
    g x = WithLp.toLp 2 ((A.map (Int.cast : ℤ → ℝ)).mulVec x.ofLp + τ A + intVec n)}

/-- Conjugate of a set of affine maps (exactly the left-hand side shape used in
`AffinelyEquivalent` / `AffOPEquivalent`). -/
def conjSet (φ : AffineGroup 3) (S : Set (AffineGroup 3)) : Set (AffineGroup 3) :=
  {h | ∃ g ∈ S, h = φ * g * φ⁻¹}

/-- The image in `Aff(ℝ³)` of a group of Euclidean motions (the right-hand side shape used in
`AffinelyEquivalent` / `AffOPEquivalent`). -/
def affImage (G : Subgroup (EuclideanIsom 3)) : Set (AffineGroup 3) :=
  {h | ∃ g ∈ G, h = g.toAffineEquiv}

/-- Integral equivalence of data: conjugation by `x ↦ U x + s` (with `U` unimodular) takes
`(P, τ)` to `(P', τ')`: `P' = U P U⁻¹` and
`τ'(U B U⁻¹) ≡ U τ(B) + s − (U B U⁻¹) s (mod ℤ³)`. -/
def IntEquiv (P : Set IMat) (τ : IMat → Fin 3 → ℝ) (P' : Set IMat) (τ' : IMat → Fin 3 → ℝ)
    (U : IMat) (s : Fin 3 → ℝ) : Prop :=
  (∀ A, A ∈ P' ↔ ∃ B ∈ P, A = U * B * U⁻¹) ∧
  ∀ B ∈ P, ∃ n : Fin 3 → ℤ,
    τ' (U * B * U⁻¹) = (U.map (Int.cast : ℤ → ℝ)).mulVec (τ B) + s
      - ((U * B * U⁻¹).map (Int.cast : ℤ → ℝ)).mulVec s + intVec n

/-! ### Selling reduction data -/

/-- The six connected support graphs (on the superbase indices `0..3`) of a Selling-reduced
positive definite ternary form, up to relabelling: `K₄`, `K₄ − 01`, the 4-cycle `0123`, the paw,
the path `0123`, the star at `0`. -/
def sellingGraphList : List (List (Fin 4 × Fin 4)) :=
  [[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)],
   [(0,2),(0,3),(1,2),(1,3),(2,3)],
   [(0,1),(1,2),(2,3),(0,3)],
   [(0,1),(0,2),(1,2),(0,3)],
   [(0,1),(1,2),(2,3)],
   [(0,1),(0,2),(0,3)]]

/-- The `i`-th Selling support graph. -/
def sellingGraph (i : Fin 6) : List (Fin 4 × Fin 4) := sellingGraphList.getD i []

/-- Coset-minimal vectors for support graph `E`: nonzero `y ∈ ℤ³` such that, with superbase
coordinates `x = (0, y₀, y₁, y₂)`, every edge `ab ∈ E` has `|x a − x b| ≤ 1`. -/
def sellingVecs (E : List (Fin 4 × Fin 4)) : Set (Fin 3 → ℤ) :=
  {y | y ≠ 0 ∧ ∀ e ∈ E,
    |(Fin.cons (0 : ℤ) y : Fin 4 → ℤ) e.1 - (Fin.cons (0 : ℤ) y : Fin 4 → ℤ) e.2| ≤ 1}

/-- Unimodular integer matrices mapping `sellingVecs E` into itself (a finite group; orders
48, 16, 48, 24, 48, 48 for the six graphs). -/
def sellingStab (E : List (Fin 4 × Fin 4)) : Set IMat :=
  {A | IsUnit A.det ∧ ∀ y ∈ sellingVecs E, A.mulVec y ∈ sellingVecs E}

/-! ### Computable closure of generator tables

The tables are computed on flat data (`List ℤ` of 9 entries row-major, `List ℚ` of 3 entries) so
that evaluation does not build nested `Matrix` closures. -/

/-- Product of flat `3 × 3` matrices (row-major `List ℤ`). -/
def m9mul (a b : List ℤ) : List ℤ :=
  (List.range 3).flatMap fun i => (List.range 3).map fun j =>
    ((List.range 3).map fun k => a.getD (3 * i + k) 0 * b.getD (3 * k + j) 0).sum

/-- Flat matrix times a rational vector. -/
def m9vec (a : List ℤ) (v : List ℚ) : List ℚ :=
  (List.range 3).map fun i => ((List.range 3).map fun k => (a.getD (3 * i + k) 0 : ℚ) * v.getD k 0).sum

/-- Product of two affine maps `(A, a)·(B, b) = (AB, a + A b)`, translation reduced mod `ℤ³`. -/
def sgMulPair (p q : List ℤ × List ℚ) : List ℤ × List ℚ :=
  (m9mul p.1 q.1, (List.zipWith (· + ·) p.2 (m9vec p.1 q.2)).map Int.fract)

/-- Breadth-first closure (with fuel) of a list of affine generators, starting from `acc`. -/
def sgClose (gens : List (List ℤ × List ℚ)) : ℕ → List (List ℤ × List ℚ) → List (List ℤ × List ℚ)
  | 0, acc => acc
  | k + 1, acc => sgClose gens k (acc ++ acc.flatMap fun a => gens.map fun g => sgMulPair a g).dedup

/-- The flat identity matrix and zero translation. -/
def sgOne : List ℤ × List ℚ := ([1, 0, 0, 0, 1, 0, 0, 0, 1], [0, 0, 0])

/-! GENERATED by `scripts/emit.py` (from `scripts/s1.py`–`s4.py`); do not edit by hand. -/

/-- Generators of the 73 arithmetic-class representatives. Each matrix is encoded as
`∑ᵢ (aᵢ + 3)·7^i` over its 9 entries `aᵢ ∈ [-3, 3]` in row-major order (see `codeToList`). -/
def arithGensList : List (List ℕ) := [
  [],
  [14409600],
  [25941254],
  [14414404],
  [14411652],
  [25939202],
  [20277638],
  [25941267],
  [14409600, 14411652],
  [14409600, 25939202],
  [14412338],
  [19351244],
  [20899160, 25958110],
  [14411652, 25941254],
  [25939202, 25944004],
  [25939202, 25941254],
  [20899160, 25826012],
  [25939202, 14411652],
  [25939202, 14414402],
  [20899160, 19468550],
  [20899160, 19336452],
  [25840804],
  [25941940],
  [20042340],
  [14414067],
  [14411665],
  [20277638, 25941254],
  [25941267, 25944011],
  [25941267, 25943661],
  [21000738, 19336452],
  [25941267, 14414409],
  [25941267, 14414059],
  [25943669],
  [25840804, 19351244],
  [14412338, 25941940],
  [14409600, 25939202, 14411652],
  [20899160, 25826012, 14409600],
  [14409600, 25939202, 14414402],
  [20899160, 14409600, 25958110],
  [14412338, 25944004],
  [20899216, 20899160],
  [19351244, 25826012],
  [20983538, 25939202],
  [25840804, 25826012],
  [25941940, 25944004],
  [20983540, 25939202],
  [25826068, 20899160],
  [14411665, 14414067],
  [20042340, 19336452],
  [14414067, 25943661],
  [14414067, 14414059],
  [14411665, 14414059],
  [14411665, 14414409],
  [25943669, 25943661],
  [25943669, 14414059],
  [20277638, 20075954],
  [20061260, 25823618],
  [25958074, 20044411],
  [20899216, 25826068, 20899160],
  [20983538, 20983540, 25939202],
  [14411665, 14414067, 14414059],
  [25134524, 20899210],
  [20042340, 20311252],
  [25134916, 20042340],
  [20983538, 14412338],
  [20882402, 20075624],
  [20075624, 15220802],
  [25941940, 20296804],
  [25840804, 25134574],
  [25134574, 20885147],
  [20042340, 20311252, 20983538],
  [25134916, 20042340, 20882402],
  [25134524, 20899210, 20075624]]

/-- The 230 representatives: `(arithmetic class, denominator d, numerators, affine class)`.
The numerators list has 3 entries per generator of the class (aligned with `arithGensList`);
the generator's translation mod `ℤ³` is `numerators / d`. -/
def sgDataList : List (ℕ × ℕ × List ℤ × ℕ) := [
  (0, 1, [], 0),
  (1, 1, [0, 0, 0], 1),
  (2, 1, [0, 0, 0], 2),
  (2, 2, [0, 0, 1], 3),
  (3, 1, [0, 0, 0], 4),
  (3, 2, [0, 1, 0], 5),
  (4, 1, [0, 0, 0], 6),
  (5, 1, [0, 0, 0], 7),
  (5, 2, [0, 0, 1], 8),
  (6, 1, [0, 0, 0], 9),
  (7, 1, [0, 0, 0], 10),
  (7, 3, [0, 0, 1], 11),
  (7, 3, [0, 0, 2], 11),
  (8, 1, [0, 0, 0, 0, 0, 0], 12),
  (8, 2, [0, 0, 0, 0, 0, 1], 13),
  (9, 1, [0, 0, 0, 0, 0, 0], 14),
  (9, 2, [0, 0, 0, 0, 0, 1], 15),
  (9, 2, [0, 0, 0, 0, 1, 0], 16),
  (9, 2, [0, 0, 0, 0, 1, 1], 17),
  (10, 1, [0, 0, 0], 18),
  (11, 1, [0, 0, 0], 19),
  (12, 1, [0, 0, 0, 0, 0, 0], 20),
  (12, 2, [0, 0, 0, 0, 1, 1], 21),
  (12, 2, [0, 0, 0, 1, 0, 1], 22),
  (13, 1, [0, 0, 0, 0, 0, 0], 23),
  (13, 2, [0, 0, 0, 0, 0, 1], 24),
  (13, 2, [0, 0, 0, 1, 1, 0], 25),
  (13, 2, [0, 0, 0, 1, 1, 1], 26),
  (14, 1, [0, 0, 0, 0, 0, 0], 27),
  (14, 2, [0, 0, 0, 0, 0, 1], 28),
  (14, 2, [0, 0, 0, 0, 1, 0], 29),
  (14, 2, [0, 0, 0, 0, 1, 1], 30),
  (14, 2, [0, 0, 0, 1, 1, 0], 31),
  (14, 2, [0, 0, 0, 1, 1, 1], 32),
  (14, 2, [0, 0, 1, 0, 0, 0], 33),
  (14, 2, [0, 0, 1, 0, 1, 0], 34),
  (14, 2, [0, 0, 1, 0, 1, 1], 35),
  (14, 2, [0, 0, 1, 1, 1, 0], 36),
  (15, 1, [0, 0, 0, 0, 0, 0], 37),
  (15, 2, [0, 0, 0, 0, 0, 1], 38),
  (15, 2, [0, 0, 1, 0, 0, 0], 39),
  (16, 1, [0, 0, 0, 0, 0, 0], 40),
  (16, 4, [0, 0, 0, 2, 1, 3], 41),
  (17, 1, [0, 0, 0, 0, 0, 0], 42),
  (17, 2, [0, 0, 1, 0, 0, 0], 43),
  (18, 1, [0, 0, 0, 0, 0, 0], 44),
  (18, 2, [0, 0, 0, 0, 1, 0], 45),
  (18, 2, [0, 0, 0, 1, 1, 0], 46),
  (18, 2, [0, 0, 1, 1, 1, 0], 47),
  (19, 1, [0, 0, 0, 0, 0, 0], 48),
  (19, 2, [0, 0, 0, 1, 0, 1], 49),
  (20, 1, [0, 0, 0, 0, 0, 0], 50),
  (21, 1, [0, 0, 0], 51),
  (21, 4, [2, 1, 3], 52),
  (22, 1, [0, 0, 0], 53),
  (22, 2, [0, 0, 1], 54),
  (22, 4, [0, 0, 1], 55),
  (22, 4, [0, 0, 3], 55),
  (23, 1, [0, 0, 0], 56),
  (24, 1, [0, 0, 0], 57),
  (25, 1, [0, 0, 0], 58),
  (26, 1, [0, 0, 0, 0, 0, 0], 59),
  (26, 2, [1, 0, 1, 0, 0, 1], 60),
  (27, 1, [0, 0, 0, 0, 0, 0], 61),
  (27, 2, [0, 0, 0, 0, 0, 1], 62),
  (28, 1, [0, 0, 0, 0, 0, 0], 63),
  (28, 2, [0, 0, 0, 0, 0, 1], 64),
  (29, 1, [0, 0, 0, 0, 0, 0], 65),
  (30, 1, [0, 0, 0, 0, 0, 0], 66),
  (30, 3, [0, 0, 1, 0, 0, 0], 67),
  (30, 3, [0, 0, 2, 0, 0, 0], 67),
  (31, 1, [0, 0, 0, 0, 0, 0], 68),
  (31, 3, [0, 0, 1, 0, 0, 0], 69),
  (31, 3, [0, 0, 2, 0, 0, 0], 69),
  (32, 1, [0, 0, 0], 70),
  (32, 3, [0, 0, 2], 71),
  (32, 3, [0, 0, 1], 71),
  (32, 2, [0, 0, 1], 72),
  (32, 6, [0, 0, 1], 73),
  (32, 6, [0, 0, 5], 73),
  (33, 1, [0, 0, 0, 0, 0, 0], 74),
  (33, 4, [2, 1, 3, 0, 3, 3], 75),
  (34, 1, [0, 0, 0, 0, 0, 0], 76),
  (34, 2, [0, 0, 1, 0, 0, 1], 77),
  (34, 2, [0, 1, 0, 1, 0, 0], 78),
  (34, 2, [0, 1, 1, 1, 0, 1], 79),
  (35, 1, [0, 0, 0, 0, 0, 0, 0, 0, 0], 80),
  (35, 2, [0, 0, 0, 0, 0, 0, 0, 0, 1], 81),
  (35, 2, [0, 0, 0, 0, 0, 1, 0, 0, 0], 82),
  (35, 2, [0, 0, 0, 1, 1, 0, 0, 0, 0], 83),
  (35, 2, [0, 0, 0, 1, 1, 0, 0, 0, 1], 84),
  (35, 2, [0, 0, 0, 1, 1, 1, 0, 0, 0], 85),
  (36, 1, [0, 0, 0, 0, 0, 0, 0, 0, 0], 86),
  (36, 4, [0, 0, 0, 2, 1, 3, 2, 0, 2], 87),
  (37, 1, [0, 0, 0, 0, 0, 0, 0, 0, 0], 88),
  (37, 2, [0, 0, 0, 0, 0, 0, 0, 0, 1], 89),
  (37, 2, [0, 0, 0, 0, 0, 0, 0, 1, 0], 90),
  (37, 2, [0, 0, 0, 0, 0, 0, 0, 1, 1], 91),
  (37, 2, [0, 0, 0, 0, 0, 0, 1, 1, 0], 92),
  (37, 2, [0, 0, 0, 0, 0, 0, 1, 1, 1], 93),
  (37, 2, [0, 0, 0, 0, 0, 1, 0, 1, 0], 94),
  (37, 2, [0, 0, 0, 0, 0, 1, 0, 1, 1], 95),
  (37, 2, [0, 0, 0, 0, 0, 1, 1, 1, 0], 96),
  (37, 2, [0, 0, 0, 0, 1, 0, 0, 0, 1], 97),
  (37, 2, [0, 0, 0, 0, 1, 0, 0, 1, 1], 98),
  (37, 2, [0, 0, 0, 0, 1, 0, 1, 0, 1], 99),
  (37, 2, [0, 0, 0, 0, 1, 0, 1, 1, 1], 100),
  (37, 2, [0, 0, 0, 0, 1, 1, 1, 0, 1], 101),
  (37, 2, [0, 0, 0, 0, 1, 1, 1, 1, 0], 102),
  (37, 2, [0, 0, 0, 1, 1, 0, 1, 0, 1], 103),
  (38, 1, [0, 0, 0, 0, 0, 0, 0, 0, 0], 104),
  (38, 2, [0, 0, 0, 0, 0, 0, 0, 1, 1], 105),
  (38, 2, [0, 0, 0, 0, 0, 0, 1, 0, 1], 106),
  (38, 2, [0, 0, 0, 1, 0, 1, 0, 1, 1], 107),
  (39, 1, [0, 0, 0, 0, 0, 0], 108),
  (39, 2, [0, 0, 1, 0, 0, 1], 109),
  (39, 2, [1, 1, 0, 1, 1, 0], 110),
  (39, 2, [1, 1, 1, 1, 1, 1], 111),
  (40, 1, [0, 0, 0, 0, 0, 0], 112),
  (40, 2, [0, 1, 1, 0, 0, 0], 113),
  (41, 1, [0, 0, 0, 0, 0, 0], 114),
  (41, 4, [0, 3, 3, 2, 1, 3], 115),
  (42, 1, [0, 0, 0, 0, 0, 0], 116),
  (42, 2, [1, 0, 0, 0, 0, 0], 117),
  (42, 2, [0, 0, 1, 0, 0, 1], 118),
  (42, 2, [1, 0, 1, 0, 0, 1], 119),
  (43, 1, [0, 0, 0, 0, 0, 0], 120),
  (43, 2, [0, 1, 1, 0, 0, 0], 121),
  (43, 4, [2, 1, 3, 2, 1, 3], 122),
  (43, 4, [2, 3, 1, 2, 1, 3], 123),
  (44, 1, [0, 0, 0, 0, 0, 0], 124),
  (44, 2, [0, 0, 1, 0, 0, 0], 125),
  (44, 2, [0, 0, 1, 0, 0, 1], 126),
  (44, 2, [0, 0, 0, 0, 0, 1], 127),
  (44, 2, [1, 1, 0, 1, 1, 0], 128),
  (44, 2, [1, 1, 1, 1, 1, 0], 129),
  (44, 2, [1, 1, 1, 1, 1, 1], 130),
  (44, 2, [1, 1, 0, 1, 1, 1], 131),
  (45, 1, [0, 0, 0, 0, 0, 0], 132),
  (45, 4, [1, 0, 0, 0, 0, 0], 133),
  (45, 2, [1, 0, 0, 0, 0, 0], 134),
  (45, 4, [3, 0, 0, 0, 0, 0], 133),
  (45, 2, [0, 1, 0, 0, 0, 1], 135),
  (45, 4, [1, 2, 0, 0, 0, 2], 136),
  (45, 2, [1, 1, 0, 0, 0, 1], 137),
  (45, 4, [3, 2, 0, 0, 0, 2], 136),
  (46, 1, [0, 0, 0, 0, 0, 0], 138),
  (46, 4, [2, 1, 3, 0, 0, 0], 139),
  (47, 1, [0, 0, 0, 0, 0, 0], 140),
  (47, 2, [0, 0, 1, 0, 0, 0], 141),
  (48, 1, [0, 0, 0, 0, 0, 0], 142),
  (48, 2, [1, 1, 0, 1, 0, 0], 143),
  (49, 1, [0, 0, 0, 0, 0, 0], 144),
  (49, 2, [0, 0, 0, 0, 0, 1], 145),
  (50, 1, [0, 0, 0, 0, 0, 0], 146),
  (50, 2, [0, 0, 1, 0, 0, 0], 147),
  (51, 1, [0, 0, 0, 0, 0, 0], 148),
  (51, 2, [0, 0, 1, 0, 0, 0], 149),
  (52, 1, [0, 0, 0, 0, 0, 0], 150),
  (52, 2, [0, 0, 0, 0, 0, 1], 151),
  (53, 1, [0, 0, 0, 0, 0, 0], 152),
  (53, 2, [0, 0, 1, 0, 0, 0], 153),
  (53, 2, [0, 0, 0, 0, 0, 1], 154),
  (53, 2, [0, 0, 1, 0, 0, 1], 155),
  (54, 1, [0, 0, 0, 0, 0, 0], 156),
  (54, 3, [0, 0, 2, 0, 0, 0], 157),
  (54, 3, [0, 0, 1, 0, 0, 0], 157),
  (54, 2, [0, 0, 1, 0, 0, 0], 158),
  (54, 6, [0, 0, 1, 0, 0, 0], 159),
  (54, 6, [0, 0, 5, 0, 0, 0], 159),
  (55, 1, [0, 0, 0, 0, 0, 0], 160),
  (55, 4, [1, 1, 0, 3, 1, 2], 161),
  (56, 1, [0, 0, 0, 0, 0, 0], 162),
  (56, 4, [0, 1, 3, 1, 0, 3], 163),
  (57, 1, [0, 0, 0, 0, 0, 0], 164),
  (58, 1, [0, 0, 0, 0, 0, 0, 0, 0, 0], 165),
  (58, 2, [0, 1, 1, 0, 1, 1, 0, 0, 0], 166),
  (58, 4, [1, 0, 0, 3, 1, 3, 0, 0, 0], 167),
  (58, 4, [1, 2, 2, 3, 3, 1, 0, 0, 0], 168),
  (59, 1, [0, 0, 0, 0, 0, 0, 0, 0, 0], 169),
  (59, 2, [1, 0, 0, 1, 0, 0, 0, 0, 0], 170),
  (59, 2, [0, 0, 1, 0, 1, 0, 0, 0, 1], 171),
  (59, 2, [1, 0, 1, 1, 1, 0, 0, 0, 1], 172),
  (59, 2, [0, 1, 0, 0, 0, 1, 0, 1, 0], 173),
  (59, 2, [1, 1, 0, 1, 0, 1, 0, 1, 0], 174),
  (59, 2, [0, 1, 1, 0, 1, 1, 0, 1, 1], 175),
  (59, 2, [1, 1, 1, 1, 1, 1, 0, 1, 1], 176),
  (59, 2, [1, 0, 0, 1, 0, 0, 1, 0, 0], 177),
  (59, 2, [0, 0, 0, 0, 0, 0, 1, 0, 0], 178),
  (59, 2, [1, 0, 1, 1, 1, 0, 1, 0, 1], 179),
  (59, 2, [0, 0, 1, 0, 1, 0, 1, 0, 1], 180),
  (59, 2, [1, 1, 0, 1, 0, 1, 1, 1, 0], 181),
  (59, 2, [0, 1, 0, 0, 0, 1, 1, 1, 0], 182),
  (59, 2, [1, 1, 1, 1, 1, 1, 1, 1, 1], 183),
  (59, 2, [0, 1, 1, 0, 1, 1, 1, 1, 1], 184),
  (60, 1, [0, 0, 0, 0, 0, 0, 0, 0, 0], 185),
  (60, 2, [0, 0, 0, 0, 0, 1, 0, 0, 0], 186),
  (60, 2, [0, 0, 1, 0, 0, 0, 0, 0, 0], 187),
  (60, 2, [0, 0, 1, 0, 0, 1, 0, 0, 0], 188),
  (61, 1, [0, 0, 0, 0, 0, 0], 189),
  (61, 2, [0, 0, 0, 1, 0, 0], 190),
  (62, 1, [0, 0, 0, 0, 0, 0], 191),
  (62, 2, [0, 0, 0, 1, 0, 1], 192),
  (62, 2, [0, 0, 0, 0, 1, 1], 193),
  (63, 1, [0, 0, 0, 0, 0, 0], 194),
  (63, 4, [3, 3, 2, 1, 3, 0], 195),
  (64, 1, [0, 0, 0, 0, 0, 0], 196),
  (64, 2, [1, 0, 0, 0, 0, 1], 197),
  (65, 1, [0, 0, 0, 0, 0, 0], 198),
  (65, 4, [0, 0, 2, 3, 2, 1], 199),
  (66, 1, [0, 0, 0, 0, 0, 0], 200),
  (66, 2, [0, 0, 0, 0, 1, 0], 201),
  (67, 1, [0, 0, 0, 0, 0, 0], 202),
  (67, 2, [0, 0, 1, 1, 1, 1], 203),
  (67, 4, [2, 2, 1, 3, 3, 1], 204),
  (67, 4, [2, 2, 3, 1, 1, 3], 204),
  (68, 1, [0, 0, 0, 0, 0, 0], 205),
  (68, 8, [4, 6, 2, 7, 0, 5], 206),
  (69, 1, [0, 0, 0, 0, 0, 0], 207),
  (69, 2, [1, 0, 0, 1, 1, 0], 208),
  (70, 1, [0, 0, 0, 0, 0, 0, 0, 0, 0], 209),
  (70, 2, [1, 1, 0, 1, 1, 0, 1, 0, 0], 210),
  (70, 2, [0, 0, 0, 0, 1, 1, 1, 1, 0], 211),
  (70, 2, [1, 1, 0, 1, 0, 1, 0, 1, 0], 212),
  (71, 1, [0, 0, 0, 0, 0, 0, 0, 0, 0], 213),
  (71, 4, [1, 1, 2, 3, 1, 0, 1, 3, 2], 214),
  (72, 1, [0, 0, 0, 0, 0, 0, 0, 0, 0], 215),
  (72, 2, [0, 0, 0, 1, 0, 0, 1, 1, 1], 216),
  (72, 2, [1, 0, 0, 0, 0, 1, 0, 0, 0], 217),
  (72, 2, [1, 0, 0, 1, 0, 1, 1, 1, 1], 218)]

/-- Decode the 9 entries of a generator code `∑ᵢ (aᵢ + 3)·7^i` (row-major, `aᵢ ∈ [-3, 3]`). -/
def codeToList (c : ℕ) : List ℤ := (List.range 9).map fun i => ((c / 7 ^ i % 7 : ℕ) : ℤ) - 3

/-- The integer matrix with the given 9 entries (row-major). -/
def imatOfList (l : List ℤ) : IMat := Matrix.of fun i j => l.getD (3 * i.val + j.val) 0

/-- Arithmetic-class index of the space-group representative `k`. -/
def sgArith (k : Fin 230) : Fin 73 :=
  ⟨(sgDataList.getD k.val (0, 1, [], 0)).1 % 73, Nat.mod_lt _ (by decide)⟩

/-- Affine-class index (`0..218`) of the space-group representative `k`. -/
def sgAffClass (k : Fin 230) : Fin 219 :=
  ⟨(sgDataList.getD k.val (0, 1, [], 0)).2.2.2 % 219, Nat.mod_lt _ (by decide)⟩

/-- Flat generator matrices of the `j`-th arithmetic class. -/
def arithGens (j : Fin 73) : List (List ℤ) := (arithGensList.getD j.val []).map codeToList

/-- Generator translations (mod `ℤ³`) of the `k`-th representative, aligned with
`arithGens (sgArith k)`. -/
def sgGenTrans (k : Fin 230) : List (List ℚ) :=
  let e := sgDataList.getD k.val (0, 1, [], 0)
  (List.range (arithGensList.getD e.1 []).length).map fun g =>
    (List.range 3).map fun i => ((e.2.2.1.getD (3 * g + i) 0 : ℚ) / (e.2.1 : ℚ))

/-- The `j`-th arithmetic-class representative, a finite subgroup of `GL₃(ℤ)`. -/
def arithRep (j : Fin 73) : Set IMat :=
  {A | ∃ p ∈ sgClose ((arithGens j).map fun g => (g, [0, 0, 0])) 48 [sgOne], A = imatOfList p.1}

/-- Full flat element table `(A, τ(A) mod ℤ³)` of the `k`-th space-group representative. -/
def sgTable (k : Fin 230) : List (List ℤ × List ℚ) :=
  sgClose (List.zip (arithGens (sgArith k)) (sgGenTrans k)) 48 [sgOne]

/-- The translation cocycle of the `k`-th representative (values in `ℚ³ ⊂ ℝ³`; `0` off the
group). -/
noncomputable def sgTau (k : Fin 230) (A : IMat) : Fin 3 → ℝ :=
  fun i => ((((sgTable k).find? fun p => decide (imatOfList p.1 = A)).map
    (fun p => p.2.getD i.val 0)).getD 0 : ℚ)


end Work.SG
