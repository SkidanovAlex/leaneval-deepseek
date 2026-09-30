import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

/-!
# Convex polytopes from integer H-representations, and their barycentric subdivision

This file sets up the data structure `Work.ConvexCells.PolytopeData` used by the `ConvexCells`
area.  A polytope is described by an H-representation whose data is *integral* after clearing the
common denominator `D` (so that all the correctness conditions of `PolytopeData.Ok` are decidable
integer arithmetic, which the kernel can evaluate), together with

* a finite list of faces, each given by its *tight set* `tight f : Finset (Fin m)` (the constraints
  that are equalities on the face) and an integral point `pos f` in its relative interior;
* a distinguished `top` face (the whole polytope, with empty tight set);
* for each constraint `i`, a face `gface i` realising the tight set of the face on which `i` is
  tight, with Farkas-style certificates (`caN`, `caD`, `cbI`) showing that on that face all the
  constraints of `tight (gface i)` are tight as well;
* a certificate (`bndPos`, `bndNeg`) that the polytope is bounded.

All conditions are collected in the decidable proposition `PolytopeData.Ok`; `PolytopeData.checks`
is its `decide`, so `checks = true` is a kernel-checkable finite condition and `checks_sound` turns
it into `Ok`.

## Conventions

* ambient space `E d = EuclideanSpace ℝ (Fin d)`;
* `P.nR i = D⁻¹ • toE (P.nrm i) : E d` is the real normal vector of constraint `i`;
* `P.bR i = (P.rhs i)/D : ℝ` is its real right hand side;
* `P.posR f = D⁻¹ • toE (P.pos f)`;
* `P.Pset = {x | ∀ i, ⟪P.nR i, x⟫ ≤ P.bR i}` is the polytope;
* `P.tightAt x = {i | P.bR i ≤ ⟪P.nR i, x⟫}` is the tight set of `x`;
* `P.Fset f = {x ∈ P.Pset | ∀ i ∈ P.tight f, ⟪P.nR i, x⟫ = P.bR i}` is the closed face of `f`;
* a *flag* is a strictly increasing chain of faces, `P.IsFlag l = l.Pairwise P.SubFace`;
* `P.FlagPt` is the set of points of the open simplices of the barycentric subdivision: a flag
  together with strictly positive weights summing to one, and `FlagPt.toE'` realizes it in `P`.

## Face completeness

`Carriers` (face completeness: every point of the polytope has its tight set among the listed faces)
is the property, beyond `Ok` itself, that the covering theorem needs.  It *is* implied by the
decidable `checks`: the last two groups of conjuncts of `Ok` (`OkEmp`, `OkAdd`) carry, for every face
`f` and every constraint `i`, either a Farkas infeasibility certificate for the region
`Fset f ∩ {n_i = b_i}` or a face `addF f i` together with coefficients showing that the constraints
of `tight (addF f i)` are tight on that region.  `Carriers_of_Ok` turns this into `Carriers`.
-/

namespace Work.ConvexCells

open scoped BigOperators

/-- The real ambient space of the `d`-dimensional theory. -/
abbrev E (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/-- Cast an integral vector into the ambient real space. -/
noncomputable def toE {d : ℕ} (v : Fin d → ℤ) : E d :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm fun i => (v i : ℝ)

@[simp] theorem toE_apply {d : ℕ} (v : Fin d → ℤ) (i : Fin d) : toE v i = (v i : ℝ) := rfl

theorem toE_add {d : ℕ} (u v : Fin d → ℤ) : toE (u + v) = toE u + toE v := by
  ext i; simp [toE]

theorem toE_sub {d : ℕ} (u v : Fin d → ℤ) : toE (u - v) = toE u - toE v := by
  ext i; simp [toE]

theorem toE_neg {d : ℕ} (u : Fin d → ℤ) : toE (-u) = -toE u := by
  ext i; simp [toE]

theorem toE_smul {d : ℕ} (c : ℤ) (u : Fin d → ℤ) : toE (c • u) = (c : ℝ) • toE u := by
  ext i; simp [toE]

theorem toE_zero {d : ℕ} : toE (0 : Fin d → ℤ) = 0 := by
  ext i; simp [toE]

theorem toE_sum {d : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Fin d → ℤ) :
    toE (∑ i ∈ s, f i) = ∑ i ∈ s, toE (f i) := by
  ext j; simp [toE, Finset.sum_apply, Int.cast_sum]

/-- The `j`-th standard basis vector of the integral lattice, as a point. -/
noncomputable def basisVec {d : ℕ} (j : Fin d) : E d := toE (Pi.single j (1 : ℤ))

theorem inner_toE {d : ℕ} (u v : Fin d → ℤ) :
    inner ℝ (toE u) (toE v) = ((∑ j, u j * v j : ℤ) : ℝ) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [toE, dotProduct, Int.cast_sum, Int.cast_mul, mul_comm]

theorem inner_toE_right {d : ℕ} (u : Fin d → ℤ) (x : E d) :
    inner ℝ (toE u) x = ∑ i, (u i : ℝ) * x i := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [toE, mul_comm]

theorem inner_basisVec {d : ℕ} (j : Fin d) (x : E d) : inner ℝ (basisVec j) x = x j := by
  rw [basisVec, inner_toE_right]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij; simp [Pi.single_eq_of_ne hij]
  · intro hj; exact absurd (Finset.mem_univ j) hj

theorem continuous_inner_left {d : ℕ} (a : E d) : Continuous fun x : E d => inner ℝ a x := by
  simpa using (continuous_const : Continuous fun _ : E d => a).inner
    (continuous_id : Continuous fun x : E d => x)

/-- Data describing a `d`-dimensional convex polytope by an integral H-representation together with
a finite face lattice.

* `D` is the common denominator (positive);
* `m` constraints given by the integral vectors `nrm` and the integral right hand sides `rhs`;
* `K` faces, each with a tight set `tight` and an integral relative interior point `pos`;
* `top` is the whole polytope (tight set `∅`);
* `gface i` is the face on which constraint `i` is tight;
* `caN`, `caD`, `cbI` are the Farkas certificates for the tight-set implications;
* `bndPos`/`bndNeg` certify boundedness. -/
structure PolytopeData (d : ℕ) where
  /-- common denominator -/
  D : ℕ
  /-- number of constraints -/
  m : ℕ
  /-- number of faces -/
  K : ℕ
  /-- integral normals of the H-representation -/
  nrm : Fin m → Fin d → ℤ
  /-- integral right hand sides of the H-representation -/
  rhs : Fin m → ℤ
  /-- tight set of each face -/
  tight : Fin K → Finset (Fin m)
  /-- integral relative interior point of each face -/
  pos : Fin K → Fin d → ℤ
  /-- the face which is the whole polytope -/
  top : Fin K
  /-- for each constraint `i`, a face realising the tight set of `{x : n_i · x = rhs i}` -/
  gface : Fin m → Fin K
  /-- numerator of the Farkas coefficient for the pair `(i,j)` -/
  caN : Fin m → Fin m → ℤ
  /-- common denominator of the Farkas coefficients -/
  caD : ℤ
  /-- numerators of the Farkas coefficients for the pair `(i,j)` -/
  cbI : Fin m → Fin m → Fin m → ℤ
  /-- boundedness certificate: weights for `e_j` -/
  bndPos : Fin d → Fin m → ℤ
  /-- boundedness certificate: weights for `-e_j` -/
  bndNeg : Fin d → Fin m → ℤ
  /-- for each face `f` and constraint `i`: whether the region `Fset f ∩ {n_i = b_i}` is
  (certifiably) empty -/
  empSel : Fin K → Fin m → Bool
  /-- emptiness certificate: coefficients of the constraints of `tight f` -/
  empA : Fin K → Fin m → Fin m → ℤ
  /-- emptiness certificate: coefficient of constraint `i` -/
  empI : Fin K → Fin m → ℤ
  /-- emptiness certificate: nonnegative coefficients of all constraints -/
  empG : Fin K → Fin m → Fin m → ℤ
  /-- for each face `f` and constraint `i`: a face whose tight set contains `tight f ∪ {i}` -/
  addF : Fin K → Fin m → Fin K
  /-- adding-constraint certificate: coefficients of the constraints of `tight f` -/
  addA : Fin K → Fin m → Fin m → Fin m → ℤ
  /-- adding-constraint certificate: coefficient of constraint `i` -/
  addI : Fin K → Fin m → Fin m → ℤ
  /-- adding-constraint certificate: nonnegative coefficients of all constraints -/
  addG : Fin K → Fin m → Fin m → Fin m → ℤ
  /-- adding-constraint certificate: positive denominators -/
  addD : Fin K → Fin m → Fin m → ℤ

namespace PolytopeData

open scoped BigOperators

variable {d : ℕ} (P : PolytopeData d)

/-- The real normal vector of constraint `i`. -/
noncomputable def nR (i : Fin P.m) : E d := ((P.D : ℝ))⁻¹ • toE (P.nrm i)

/-- The real right hand side of constraint `i`. -/
noncomputable def bR (i : Fin P.m) : ℝ := (P.rhs i : ℝ) / (P.D : ℝ)

/-- The real point attached to the face `f`. -/
noncomputable def posR (f : Fin P.K) : E d := ((P.D : ℝ))⁻¹ • toE (P.pos f)

/-- The polytope cut out by the H-representation. -/
def Pset : Set (E d) := {x | ∀ i, inner ℝ (P.nR i) x ≤ P.bR i}

/-- The set of constraints that are tight at `x`. -/
noncomputable def tightAt (x : E d) : Finset (Fin P.m) :=
  Finset.univ.filter fun i => P.bR i ≤ inner ℝ (P.nR i) x

/-- The closed face of `P` cut out by the tight set of `f`. -/
def Fset (f : Fin P.K) : Set (E d) :=
  {x | x ∈ P.Pset ∧ ∀ i ∈ P.tight f, inner ℝ (P.nR i) x = P.bR i}

/-- `f` is a proper sub-face of `g` (as subsets of the polytope). -/
def SubFace (f g : Fin P.K) : Prop := P.tight g ⊂ P.tight f

/-- A flag: a strictly increasing chain of faces `F₀ ⊂ F₁ ⊂ ⋯`. -/
def IsFlag (l : List (Fin P.K)) : Prop := l.Pairwise P.SubFace

/-- The real Farkas coefficient `a` of the pair `(i,j)`. -/
noncomputable def ca (i j : Fin P.m) : ℝ := (P.caN i j : ℝ) / (P.caD : ℝ)

/-- The real Farkas coefficient of `n_k` in the certificate of the pair `(i,j)`. -/
noncomputable def cb (i j k : Fin P.m) : ℝ := (P.cbI i j k : ℝ) / (P.caD : ℝ)

/-- The basic decidable correctness conditions on the data. -/
@[reducible] def OkBasic : Prop :=
  -- the common denominator is positive
  (0 < P.D) ∧
  -- the top face is the whole polytope
  (P.tight P.top = ∅) ∧
  -- tight sets determine faces
  (∀ f g, P.tight f = P.tight g → f = g) ∧
  -- `pos` points realise the tight set of their face
  (∀ f, (∀ i ∈ P.tight f, ∑ j, P.nrm i j * P.pos f j = (P.D : ℤ) * P.rhs i) ∧
        (∀ i, i ∉ P.tight f → ∑ j, P.nrm i j * P.pos f j < (P.D : ℤ) * P.rhs i)) ∧
  -- the Farkas certificates for the faces `gface i`
  (0 < P.caD ∧
        ∀ i, i ∈ P.tight (P.gface i) ∧
        ∀ j, j ∈ P.tight (P.gface i) →
          (∀ k, 0 ≤ P.cbI i j k) ∧
          (∀ j', P.caN i j * P.nrm i j' - ∑ k, P.cbI i j k * P.nrm k j'
              = P.caD * P.nrm j j') ∧
          (P.caD * P.rhs j ≤ P.caN i j * P.rhs i - ∑ k, P.cbI i j k * P.rhs k)) ∧
  -- the boundedness certificate
  (∀ j k, 0 ≤ P.bndPos j k) ∧ (∀ j k, 0 ≤ P.bndNeg j k) ∧
  (∀ j j', ∑ k, P.bndPos j k * P.nrm k j' = (P.D : ℤ) * (if j = j' then 1 else 0)) ∧
  (∀ j j', ∑ k, P.bndNeg j k * P.nrm k j' = (P.D : ℤ) * (if j = j' then -1 else 0))

set_option synthInstance.maxSize 4000 in
/-- Emptiness certificates for the regions `Fset f ∩ {n_i = b_i}` (Farkas infeasibility). -/
@[reducible] def OkEmp : Prop :=
  (∀ f i, P.empSel f i = true →
      (∀ l, 0 ≤ P.empG f i l) ∧
      (∀ j', ∑ k ∈ P.tight f, P.empA f i k * P.nrm k j' + P.empI f i * P.nrm i j'
          - ∑ l, P.empG f i l * P.nrm l j' = 0) ∧
      (0 < ∑ k ∈ P.tight f, P.empA f i k * P.rhs k + P.empI f i * P.rhs i
          - ∑ l, P.empG f i l * P.rhs l))

set_option synthInstance.maxSize 4000 in
/-- Certificates for enlarging a face by one constraint. -/
@[reducible] def OkAdd : Prop :=
  -- the certificates for enlarging a face by one constraint
  (∀ f i, P.empSel f i = false →
      (P.tight f ∪ {i} ⊆ P.tight (P.addF f i)) ∧
      (∀ j, j ∈ P.tight (P.addF f i) → 0 < P.addD f i j) ∧
      (∀ j, j ∈ P.tight (P.addF f i) → ∀ l, 0 ≤ P.addG f i j l) ∧
      (∀ j, j ∈ P.tight (P.addF f i) → ∀ j',
          P.addD f i j * P.nrm j j'
            - (∑ k ∈ P.tight f, P.addA f i j k * P.nrm k j' + P.addI f i j * P.nrm i j')
            + ∑ l, P.addG f i j l * P.nrm l j' = 0) ∧
      (∀ j, j ∈ P.tight (P.addF f i) →
          P.addD f i j * P.rhs j
            - (∑ k ∈ P.tight f, P.addA f i j k * P.rhs k + P.addI f i j * P.rhs i)
            + ∑ l, P.addG f i j l * P.rhs l ≤ 0))

/-- The list of all decidable correctness conditions on the data. -/
@[reducible] def Ok : Prop := P.OkBasic ∧ P.OkEmp ∧ P.OkAdd
/-- The face family is closed under unions of tight sets; equivalently, intersections of faces are
faces.  This is *not* implied by `Ok`, and it is not satisfiable by data for a polytope with two
disjoint faces (the union of the tight sets of two disjoint faces would have to be the tight set of
an empty face, which `Ok`'s `pos` conditions forbid), so it is only an auxiliary hypothesis; it is
the right closure condition for simple polytopes together with elements for the empty intersections.
See `Carriers_of_unionClosed`. -/
def UnionClosed : Prop := ∀ f g, ∃ h, P.tight h = P.tight f ∪ P.tight g

/-- Face completeness: every point of the polytope has its tight set among the listed faces, so that
the minimal face containing the point is part of the data.

This is the hypothesis, beyond the decidable `checks`, under which the barycentric subdivision of the
data is a bijection onto `Pset`: the open simplex attached to a flag lies in the relative interior of
its *largest* face, so a covering flag can only exist if the carrier of a point is among the listed
faces.  See `Carriers_of_unionClosed` and `Carriers_of_addF`. -/
def Carriers : Prop := ∀ x ∈ P.Pset, ∃ f : Fin P.K, P.tight f = P.tightAt x


set_option synthInstance.maxSize 4000 in

/-- The basic checks as a boolean. -/
def checksBasic : Bool := decide P.OkBasic

/-- The emptiness-certificate checks as a boolean. -/
def checksEmp : Bool := decide P.OkEmp

/-- The adding-constraint-certificate checks as a boolean. -/
def checksAdd : Bool := decide P.OkAdd

/-- The kernel-checkable boolean condition on `PolytopeData`: the three groups of checks above. -/
def checks : Bool := P.checksBasic && P.checksEmp && P.checksAdd

theorem checks_eq (h : P.checks = true) : P.checksBasic = true ∧ P.checksEmp = true ∧
    P.checksAdd = true := by
  have h' := h
  rw [checks, Bool.and_eq_true, Bool.and_eq_true] at h'
  exact ⟨h'.1.1, h'.1.2, h'.2⟩

theorem checks_sound (h : P.checks = true) : P.Ok := by
  obtain ⟨h1, h2, h3⟩ := checks_eq P h
  exact ⟨of_decide_eq_true h1, of_decide_eq_true h2, of_decide_eq_true h3⟩

structure FlagPt where
  /-- the flag -/
  flag : List (Fin P.K)
  /-- it is a flag -/
  isFlag : P.IsFlag flag
  /-- weights on the faces of the flag -/
  wt : Fin flag.length → ℝ
  /-- all weights are positive -/
  wt_pos : ∀ i, 0 < wt i
  /-- the weights sum to one -/
  wt_sum : ∑ i, wt i = 1


/-! ### Accessors for the conjuncts of `Ok` -/

theorem Ok.D_pos (h : P.Ok) : 0 < P.D := h.1.1

theorem Ok.tight_top (h : P.Ok) : P.tight P.top = ∅ := h.1.2.1

theorem Ok.tight_inj (h : P.Ok) {f g : Fin P.K} (hfg : P.tight f = P.tight g) : f = g :=
  h.1.2.2.1 f g hfg

theorem Ok.pos_pos (h : P.Ok) (f : Fin P.K) :
    ∀ i ∈ P.tight f, ∑ j, P.nrm i j * P.pos f j = (P.D : ℤ) * P.rhs i :=
  (h.1.2.2.2.1 f).1

theorem Ok.pos_neg (h : P.Ok) (f : Fin P.K) :
    ∀ i, i ∉ P.tight f → ∑ j, P.nrm i j * P.pos f j < (P.D : ℤ) * P.rhs i :=
  (h.1.2.2.2.1 f).2

theorem Ok.caD_pos (h : P.Ok) : 0 < P.caD := h.1.2.2.2.2.1.1

theorem Ok.gface_mem (h : P.Ok) (i : Fin P.m) : i ∈ P.tight (P.gface i) :=
  (h.1.2.2.2.2.1.2 i).1

theorem Ok.gface_cb_nonneg (h : P.Ok) {i j : Fin P.m} (hj : j ∈ P.tight (P.gface i))
    (k : Fin P.m) : 0 ≤ P.cbI i j k := ((h.1.2.2.2.2.1.2 i).2 j hj).1 k

theorem Ok.gface_vec (h : P.Ok) {i j : Fin P.m} (hj : j ∈ P.tight (P.gface i))
    (j' : Fin d) : P.caN i j * P.nrm i j' - ∑ k, P.cbI i j k * P.nrm k j' = P.caD * P.nrm j j' :=
  ((h.1.2.2.2.2.1.2 i).2 j hj).2.1 j'

theorem Ok.gface_num (h : P.Ok) {i j : Fin P.m} (hj : j ∈ P.tight (P.gface i)) :
    P.caD * P.rhs j ≤ P.caN i j * P.rhs i - ∑ k, P.cbI i j k * P.rhs k :=
  ((h.1.2.2.2.2.1.2 i).2 j hj).2.2

theorem Ok.bndPos_nonneg (h : P.Ok) (j : Fin d) (k : Fin P.m) : 0 ≤ P.bndPos j k :=
  h.1.2.2.2.2.2.1 j k

theorem Ok.bndNeg_nonneg (h : P.Ok) (j : Fin d) (k : Fin P.m) : 0 ≤ P.bndNeg j k :=
  h.1.2.2.2.2.2.2.1 j k

theorem Ok.bndPos_vec (h : P.Ok) (j j' : Fin d) :
    ∑ k, P.bndPos j k * P.nrm k j' = (P.D : ℤ) * (if j = j' then 1 else 0) :=
  h.1.2.2.2.2.2.2.2.1 j j'

theorem Ok.bndNeg_vec (h : P.Ok) (j j' : Fin d) :
    ∑ k, P.bndNeg j k * P.nrm k j' = (P.D : ℤ) * (if j = j' then -1 else 0) :=
  h.1.2.2.2.2.2.2.2.2 j j'

/-- The emptiness certificate for the region `Fset f ∩ {n_i = b_i}`. -/
theorem Ok.emp_cert (h : P.Ok) (f : Fin P.K) (i : Fin P.m) (hsel : P.empSel f i = true) :
    (∀ l, 0 ≤ P.empG f i l) ∧
    (∀ j', ∑ k ∈ P.tight f, P.empA f i k * P.nrm k j' + P.empI f i * P.nrm i j'
        - ∑ l, P.empG f i l * P.nrm l j' = 0) ∧
    (0 < ∑ k ∈ P.tight f, P.empA f i k * P.rhs k + P.empI f i * P.rhs i
        - ∑ l, P.empG f i l * P.rhs l) :=
  h.2.1 f i hsel

/-- The certificate for enlarging the face `f` by the constraint `i`. -/
theorem Ok.add_cert (h : P.Ok) (f : Fin P.K) (i : Fin P.m) (hsel : P.empSel f i = false) :
    (P.tight f ∪ {i} ⊆ P.tight (P.addF f i)) ∧
    (∀ j, j ∈ P.tight (P.addF f i) → 0 < P.addD f i j) ∧
    (∀ j, j ∈ P.tight (P.addF f i) → ∀ l, 0 ≤ P.addG f i j l) ∧
    (∀ j, j ∈ P.tight (P.addF f i) → ∀ j',
        P.addD f i j * P.nrm j j'
          - (∑ k ∈ P.tight f, P.addA f i j k * P.nrm k j' + P.addI f i j * P.nrm i j')
          + ∑ l, P.addG f i j l * P.nrm l j' = 0) ∧
    (∀ j, j ∈ P.tight (P.addF f i) →
        P.addD f i j * P.rhs j
          - (∑ k ∈ P.tight f, P.addA f i j k * P.rhs k + P.addI f i j * P.rhs i)
          + ∑ l, P.addG f i j l * P.rhs l ≤ 0) :=
  h.2.2 f i hsel

/-! ### The relation between the integral data and the real polytope -/

/-- The integral identity behind `inner_nR_posR_of_mem`: multiplying the inner product of the
scaled normal and the scaled point by `D²` gives the integral dot product. -/
theorem D_sq_mul_inner (P : PolytopeData d) (hD : 0 < P.D) (i : Fin P.m) (f : Fin P.K) :
    ((P.D : ℝ) ^ 2) * inner ℝ (P.nR i) (P.posR f)
      = ((∑ j, P.nrm i j * P.pos f j : ℤ) : ℝ) := by
  have hDne : (P.D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hD)
  rw [nR, posR, inner_smul_left, inner_smul_right, inner_toE]
  simp only [RCLike.conj_to_real]
  field_simp

theorem inner_nR_posR_of_mem (h : P.Ok) (f : Fin P.K) (i : Fin P.m) (hi : i ∈ P.tight f) :
    inner ℝ (P.nR i) (P.posR f) = P.bR i := by
  have hDpos : (0 : ℝ) < (P.D : ℝ) := by exact_mod_cast Ok.D_pos P h
  have hpos : ((∑ j, P.nrm i j * P.pos f j : ℤ) : ℝ) = (P.D : ℝ) * (P.rhs i : ℝ) := by
    have := Ok.pos_pos P h f i hi
    push_cast
    exact_mod_cast this
  refine mul_left_cancel₀ (by positivity : ((P.D : ℝ) ^ 2) ≠ 0) ?_
  rw [D_sq_mul_inner P (Ok.D_pos P h) i f, hpos, bR]
  field_simp

theorem inner_nR_posR_of_not_mem (h : P.Ok) (f : Fin P.K) (i : Fin P.m) (hi : i ∉ P.tight f) :
    inner ℝ (P.nR i) (P.posR f) < P.bR i := by
  have hDpos : (0 : ℝ) < (P.D : ℝ) := by exact_mod_cast Ok.D_pos P h
  have hpos : ((∑ j, P.nrm i j * P.pos f j : ℤ) : ℝ) < (P.D : ℝ) * (P.rhs i : ℝ) := by
    have := Ok.pos_neg P h f i hi
    push_cast
    exact_mod_cast this
  have hkey : ((P.D : ℝ) ^ 2) * inner ℝ (P.nR i) (P.posR f) < ((P.D : ℝ) ^ 2) * P.bR i := by
    rw [D_sq_mul_inner P (Ok.D_pos P h) i f, bR]
    have hDne : (P.D : ℝ) ≠ 0 := ne_of_gt hDpos
    have : ((P.D : ℝ) ^ 2) * ((P.rhs i : ℝ) / (P.D : ℝ)) = (P.D : ℝ) * (P.rhs i : ℝ) := by
      field_simp
    rw [this]
    exact hpos
  exact lt_of_mul_lt_mul_left hkey (by positivity)

/-- Backwards-compatible alias of `inner_nR_posR_of_mem`. -/
theorem inner_posR_of_mem (h : P.Ok) (f : Fin P.K) (i : Fin P.m) (hi : i ∈ P.tight f) :
    inner ℝ (P.nR i) (P.posR f) = P.bR i := inner_nR_posR_of_mem P h f i hi

/-- Backwards-compatible alias of `inner_nR_posR_of_not_mem`. -/
theorem inner_posR_of_not_mem (h : P.Ok) (f : Fin P.K) (i : Fin P.m) (hi : i ∉ P.tight f) :
    inner ℝ (P.nR i) (P.posR f) < P.bR i := inner_nR_posR_of_not_mem P h f i hi


/-! ### The basic API of the polytope -/

theorem mem_Pset_iff (x : E d) : x ∈ P.Pset ↔ ∀ i, inner ℝ (P.nR i) x ≤ P.bR i := Iff.rfl

theorem mem_Fset_iff (f : Fin P.K) (x : E d) :
    x ∈ P.Fset f ↔ x ∈ P.Pset ∧ ∀ i ∈ P.tight f, inner ℝ (P.nR i) x = P.bR i := Iff.rfl

theorem mem_tightAt_iff (x : E d) (i : Fin P.m) :
    i ∈ P.tightAt x ↔ P.bR i ≤ inner ℝ (P.nR i) x := by
  rw [tightAt]; simp

/-- For a point of the polytope, being in the tight set means being an equality. -/
theorem tightAt_of_mem {x : E d} (hx : x ∈ P.Pset) (i : Fin P.m) :
    i ∈ P.tightAt x ↔ inner ℝ (P.nR i) x = P.bR i := by
  rw [mem_tightAt_iff, le_antisymm_iff, and_iff_right]
  exact hx i

theorem Fset_mono {f g : Fin P.K} (h : P.tight f ⊆ P.tight g) : P.Fset g ⊆ P.Fset f := by
  intro x hx
  exact ⟨hx.1, fun i hi => hx.2 i (h hi)⟩

theorem Pset_eq_iInter :
    P.Pset = ⋂ i, {x : E d | inner ℝ (P.nR i) x ≤ P.bR i} := by
  ext x; simp [Pset, Set.mem_iInter]

theorem Pset_convex : Convex ℝ P.Pset := by
  intro x hx y hy a b ha hb hab
  rw [Pset] at hx hy ⊢
  intro i
  calc inner ℝ (P.nR i) (a • x + b • y)
      = a * inner ℝ (P.nR i) x + b * inner ℝ (P.nR i) y := by
        simp [inner_add_right, inner_smul_right]
    _ ≤ a * P.bR i + b * P.bR i :=
        add_le_add (mul_le_mul_of_nonneg_left (hx i) ha) (mul_le_mul_of_nonneg_left (hy i) hb)
    _ = P.bR i := by rw [← add_mul, hab, one_mul]

theorem Pset_isClosed : IsClosed P.Pset := by
  rw [Pset_eq_iInter]
  exact isClosed_iInter fun i =>
    isClosed_le (continuous_inner_left (P.nR i)) (continuous_const : Continuous fun _ : E d => P.bR i)

theorem Fset_convex (f : Fin P.K) : Convex ℝ (P.Fset f) := by
  intro x hx y hy a b ha hb hab
  refine ⟨P.Pset_convex hx.1 hy.1 ha hb hab, fun i hi => ?_⟩
  rw [inner_add_right, inner_smul_right, inner_smul_right, hx.2 i hi, hy.2 i hi, ← add_mul, hab,
    one_mul]

theorem Fset_isClosed (f : Fin P.K) : IsClosed (P.Fset f) := by
  have h : P.Fset f = (⋂ i, {x : E d | inner ℝ (P.nR i) x ≤ P.bR i}) ∩
      (⋂ i ∈ P.tight f, {x : E d | inner ℝ (P.nR i) x = P.bR i}) := by
    ext x
    simp [Fset, Pset, Set.mem_iInter]
  rw [h]
  exact (isClosed_iInter fun i =>
      isClosed_le (continuous_inner_left (P.nR i))
        (continuous_const : Continuous fun _ : E d => P.bR i)).inter
    (isClosed_biInter fun i _ =>
      isClosed_eq (continuous_inner_left (P.nR i)) (continuous_const : Continuous fun _ : E d => P.bR i))

/-- The `pos` point of a face realises exactly the tight set of that face. -/
theorem tightAt_posR (h : P.Ok) (f : Fin P.K) : P.tightAt (P.posR f) = P.tight f := by
  ext i
  rw [mem_tightAt_iff]
  constructor
  · intro hi
    by_contra hc
    exact absurd hi (not_le.mpr (inner_nR_posR_of_not_mem P h f i hc))
  · intro hi; exact le_of_eq (inner_nR_posR_of_mem P h f i hi).symm

theorem posR_mem_Pset (h : P.Ok) (f : Fin P.K) : P.posR f ∈ P.Pset := by
  intro i
  by_cases hi : i ∈ P.tight f
  · rw [inner_nR_posR_of_mem P h f i hi]
  · exact le_of_lt (inner_nR_posR_of_not_mem P h f i hi)

theorem posR_mem_Fset (h : P.Ok) (f : Fin P.K) : P.posR f ∈ P.Fset f :=
  ⟨posR_mem_Pset P h f, fun i hi => inner_nR_posR_of_mem P h f i hi⟩

theorem tight_top (h : P.Ok) : P.tight P.top = ∅ := Ok.tight_top P h

theorem Pset_nonempty (h : P.Ok) : P.Pset.Nonempty :=
  ⟨P.posR P.top, posR_mem_Pset P h P.top⟩

theorem Fset_nonempty (h : P.Ok) (f : Fin P.K) : (P.Fset f).Nonempty :=
  ⟨P.posR f, posR_mem_Fset P h f⟩

/-- Linearity of the inner product in its first variable over a linear combination. -/
theorem inner_lincomb_left {ι : Type*} (s : Finset ι) (c : ι → ℝ) (u : ι → E d) (y : E d) :
    inner ℝ (∑ i ∈ s, c i • u i) y = ∑ i ∈ s, c i * inner ℝ (u i) y := by
  rw [sum_inner]
  exact Finset.sum_congr rfl fun i _ => by simp [inner_smul_left]

/-- Linearity of the inner product over a convex combination. -/
theorem inner_sum_smul {ι : Type*} (s : Finset ι) (w : ι → ℝ) (z : ι → E d) (k : Fin P.m) :
    inner ℝ (P.nR k) (∑ i ∈ s, w i • z i) = ∑ i ∈ s, w i * inner ℝ (P.nR k) (z i) := by
  change (innerSL ℝ (P.nR k)) (∑ i ∈ s, w i • z i) =
    ∑ i ∈ s, w i * (innerSL ℝ (P.nR k)) (z i)
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]

/-- The tight set of a convex combination: a constraint is tight at the combination iff every point
with nonzero weight is tight there. -/
theorem tightAt_combo {ι : Type*} {s : Finset ι} {w : ι → ℝ} {z : ι → E d}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, z i ∈ P.Pset)
    (k : Fin P.m) :
    k ∈ P.tightAt (∑ i ∈ s, w i • z i) ↔
      ∀ i ∈ s, w i ≠ 0 → inner ℝ (P.nR k) (z i) = P.bR k := by
  have hlin : inner ℝ (P.nR k) (∑ i ∈ s, w i • z i)
      = ∑ i ∈ s, w i * inner ℝ (P.nR k) (z i) := inner_sum_smul P s w z k
  have hb : inner ℝ (P.nR k) (∑ i ∈ s, w i • z i) ≤ P.bR k := by
    rw [hlin]
    calc ∑ i ∈ s, w i * inner ℝ (P.nR k) (z i) ≤ ∑ i ∈ s, w i * P.bR k :=
          Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hz i hi k) (hw i hi)
      _ = P.bR k := by rw [← Finset.sum_mul, hsum, one_mul]
  have hzero : P.bR k - inner ℝ (P.nR k) (∑ i ∈ s, w i • z i)
      = ∑ i ∈ s, w i * (P.bR k - inner ℝ (P.nR k) (z i)) := by
    rw [hlin]
    have h1 : ∀ i ∈ s, w i * (P.bR k - inner ℝ (P.nR k) (z i))
        = w i * P.bR k - w i * inner ℝ (P.nR k) (z i) := fun i _ => by ring
    rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
  have hnn : ∀ i ∈ s, 0 ≤ w i * (P.bR k - inner ℝ (P.nR k) (z i)) :=
    fun i hi => mul_nonneg (hw i hi) (sub_nonneg.mpr (hz i hi k))
  rw [mem_tightAt_iff]
  constructor
  · intro heq i hi hwi
    have heq' : inner ℝ (P.nR k) (∑ i ∈ s, w i • z i) = P.bR k := le_antisymm hb heq
    have h1 : ∑ i ∈ s, w i * (P.bR k - inner ℝ (P.nR k) (z i)) = 0 := by
      rw [← hzero, heq', sub_self]
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h1 i hi
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 hwi
    · exact (sub_eq_zero.mp h3).symm
  · intro h
    have h0 : ∑ i ∈ s, w i * (P.bR k - inner ℝ (P.nR k) (z i)) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      by_cases hwi : w i = 0
      · rw [hwi, zero_mul]
      · rw [h i hi hwi, sub_self, mul_zero]
    have h1 : P.bR k - inner ℝ (P.nR k) (∑ i ∈ s, w i • z i) = 0 := by rw [hzero, h0]
    exact le_of_eq (sub_eq_zero.mp h1)

/-! ### The real form of the Farkas certificates -/

/-- The vector identity of the Farkas certificate, in the undivided form: `caD • n_j` is
`caN i j • n_i` minus a combination of the other normals. -/
theorem cert_vec (h : P.Ok) (i j : Fin P.m) (hj : j ∈ P.tight (P.gface i)) :
    (P.caD : ℝ) • P.nR j = (P.caN i j : ℝ) • P.nR i
      - ∑ k, (P.cbI i j k : ℝ) • P.nR k := by
  have hInt : (P.caD : ℤ) • P.nrm j
      = (P.caN i j : ℤ) • P.nrm i - ∑ k, P.cbI i j k • P.nrm k := by
    ext j'
    have hh := Ok.gface_vec P h hj j'
    simp only [Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, smul_eq_mul]
    linarith [hh]
  have hDne : (P.D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Ok.D_pos P h))
  have h1 := congrArg (fun v : Fin d → ℤ => toE v) hInt
  simp only [toE_sub, toE_smul, toE_sum] at h1
  calc (P.caD : ℝ) • P.nR j
      = ((P.D : ℝ))⁻¹ • ((P.caD : ℝ) • toE (P.nrm j)) := by
        rw [nR]; exact smul_comm _ _ _
    _ = ((P.D : ℝ))⁻¹ • ((P.caN i j : ℝ) • toE (P.nrm i)
          - ∑ k, (P.cbI i j k : ℝ) • toE (P.nrm k)) := by rw [h1]
    _ = (P.caN i j : ℝ) • P.nR i - ∑ k, (P.cbI i j k : ℝ) • P.nR k := by
        rw [smul_sub, Finset.smul_sum]
        refine congr_arg₂ (· - ·) ?_ ?_
        · rw [nR]; exact smul_comm _ _ _
        · refine Finset.sum_congr rfl fun k _ => ?_
          rw [nR]; exact smul_comm _ _ _

/-- The numerical part of the Farkas certificate, in the undivided form. -/
theorem cert_num (h : P.Ok) (i j : Fin P.m) (hj : j ∈ P.tight (P.gface i)) :
    (P.caD : ℝ) * P.bR j ≤ (P.caN i j : ℝ) * P.bR i
      - ∑ k, (P.cbI i j k : ℝ) * P.bR k := by
  have hDpos : (0 : ℝ) < (P.D : ℝ) := by exact_mod_cast Ok.D_pos P h
  have hR : (P.caD : ℝ) * (P.rhs j : ℝ)
      ≤ (P.caN i j : ℝ) * (P.rhs i : ℝ)
        - ∑ k, (P.cbI i j k : ℝ) * (P.rhs k : ℝ) := by
    have h2 : (((P.caN i j * P.rhs i - ∑ k, P.cbI i j k * P.rhs k : ℤ)) : ℝ)
        = (P.caN i j : ℝ) * (P.rhs i : ℝ)
          - ∑ k, (P.cbI i j k : ℝ) * (P.rhs k : ℝ) := by
      push_cast; ring
    have h1 : (((P.caD * P.rhs j : ℤ)) : ℝ) = (P.caD : ℝ) * (P.rhs j : ℝ) := by
      push_cast; ring
    rw [← h1, ← h2]
    exact_mod_cast Ok.gface_num P h hj
  have hsum : ∑ k, (P.cbI i j k : ℝ) * P.bR k
      = (∑ k, (P.cbI i j k : ℝ) * (P.rhs k : ℝ)) / (P.D : ℝ) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => by rw [bR, mul_div_assoc]
  rw [hsum, bR, bR, ← mul_div_assoc, ← mul_div_assoc, ← sub_div,
    div_le_div_iff_of_pos_right hDpos]
  exact hR

/-- On the face where constraint `i` is tight, every constraint of the tight set of `gface i` is
tight as well. -/
theorem tight_gface_subset (h : P.Ok) (i : Fin P.m) {y : E d} (hy : y ∈ P.Pset)
    (hi : inner ℝ (P.nR i) y = P.bR i) (j : Fin P.m) (hj : j ∈ P.tight (P.gface i)) :
    inner ℝ (P.nR j) y = P.bR j := by
  have hCpos : (0 : ℝ) < (P.caD : ℝ) := by exact_mod_cast Ok.caD_pos P h
  have hvec := cert_vec P h i j hj
  have hnum := cert_num P h i j hj
  have hle : inner ℝ (P.nR j) y ≤ P.bR j := hy j
  have hkey : (P.caD : ℝ) * inner ℝ (P.nR j) y
      = (P.caN i j : ℝ) * P.bR i
        - ∑ k, (P.cbI i j k : ℝ) * inner ℝ (P.nR k) y := by
    have h1 : inner ℝ ((P.caD : ℝ) • P.nR j) y = (P.caD : ℝ) * inner ℝ (P.nR j) y := by
      rw [inner_smul_left]; simp
    rw [← h1, hvec, inner_sub_left, inner_smul_left, sum_inner, hi]
    simp [inner_smul_left]
  have hge : P.bR j ≤ inner ℝ (P.nR j) y := by
    have h1 : (P.caD : ℝ) * P.bR j ≤ (P.caD : ℝ) * inner ℝ (P.nR j) y := by
      rw [hkey]
      calc (P.caD : ℝ) * P.bR j
          ≤ (P.caN i j : ℝ) * P.bR i - ∑ k, (P.cbI i j k : ℝ) * P.bR k := hnum
        _ ≤ (P.caN i j : ℝ) * P.bR i
              - ∑ k, (P.cbI i j k : ℝ) * inner ℝ (P.nR k) y := by
            refine sub_le_sub_left ?_ _
            exact Finset.sum_le_sum fun k _ =>
              mul_le_mul_of_nonneg_left (hy k) (by exact_mod_cast Ok.gface_cb_nonneg P h hj k)
    exact le_of_mul_le_mul_left h1 hCpos
  exact le_antisymm hle hge

namespace FlagPt

variable {P}

/-- The point of the ambient space attached to a flag point: the affine realization of the simplex
spanned by `pos` of the faces of the flag. -/
noncomputable def toE' (s : P.FlagPt) : E d :=
  ∑ i : Fin s.flag.length, s.wt i • P.posR (s.flag.get i)

/-- A flag point is a nonempty flag. -/
theorem flag_ne_nil (s : P.FlagPt) : s.flag ≠ [] := by
  cases s with
  | mk flag isFlag wt hpos hsum =>
    cases flag with
    | nil => simp at hsum
    | cons a l => simp

/-- The last (largest) face of the flag. -/
def topFace (s : P.FlagPt) : Fin P.K := s.flag.getLast s.flag_ne_nil

/-- The first (smallest) face of the flag. -/
def botFace (s : P.FlagPt) : Fin P.K := s.flag.head s.flag_ne_nil

end FlagPt


end PolytopeData

end Work.ConvexCells
