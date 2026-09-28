import Mathlib
import Submission.Work.Thom.ThomClass
import Submission.Work.Thom.tautologicalQuotient
import Submission.Work.Thom.exists_tautQuotientCore
import Submission.Work.Thom.thomClassOf
import Submission.Work.Thom.thomClass_of_complex_fintype
import Submission.Work.Thom.bijective_proj_zeroComplementA
import Submission.Work.Thom.complexification
import Submission.Work.Thom.CohMap_oneH
import Submission.Work.Thom.complexBundleAux

set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# The Chern classes of a complex vector bundle (the recursion)

For a complex vector bundle `V -> B` of rank `m`, presented by gluing data over a **finite** index
type, this module defines the Chern classes `c_j(V) in H^{2j}(B;Z)` by recursion on the rank, using
the **tautological quotient** `Q = pi^*V / C.s` over the punctured total space `X = V \ 0`
(`Work.Thom.tautologicalQuotient`) and the **descent** `pi^* : H^{2j}(B) = H^{2j}(X)`
(`Work.Thom.bijective_proj_zeroComplementA`, the island-clean form of the Gysin descent):

* `c_j(V) := (pi^*)^{-1} c_j(Q)`   for `j <= rank Q = m - 1`;
* `c_m(V) := e(V_R)`               the **top** Chern class, the Euler class of the realification
                                   (`Work.Thom.ThomClass.eulerClass`, from the Thom class
                                   `Work.Thom.thomClassRank` of the complex bundle);
* `c_j(V) := 0`                    for `j > m`;
* `c_0(V) := 1`                    the unit class.

The defining equations are `Work.Thom.chernClass_succ_le` (the descent, `j <= m`) and
`Work.Thom.chernClass_succ_top` (the top class, `j = m + 1`).

The **only** mathematical input is the standard relation `pi^*V = eps + Q`, in the form that
`pi^*` is *injective* in the degrees `2j <= 2m - 2` at which the descent is applied: this is
`Work.Thom.bijective_proj_zeroComplementA`.  The splitting principle (naturality, the Whitney
formula, stability of the recursion) is *not* proved here; see `README.md` ADDENDUM 20.

## Canonicity (READ THIS BEFORE USING `chernClass` FOR ANYTHING FUNCTORIAL)

`Work.Thom.tautQuotient` and `Work.Thom.thomClassRank` are built with `Classical.choose` /
`Classical.choice` on the *existence* theorems of the Thom-class ladder.  Consequently

* `chernClass` is a perfectly well-defined **function**, and everything this chapter states about
  it (the recursion equations, the vanishing, `c_0 = 1`) is a theorem about that function; but
* `chernClass` is **not provably natural** in the bundle, for the simple reason that the two Euler
  classes of two independently chosen Thom classes of `f^*V` and of `V` are only related up to a
  *unit of `H^0`*.  In particular `c_j` is determined only up to multiplication by a unit of
  `H^0(B)` — for a **connected** base, up to sign — so `p₁(TM)` of a connected manifold is
  determined only up to sign, and `p₁(M)²` (the only quantity the dimension-`8` congruence
  `7 | p₁² - 4σ` uses) is **independent of all choices** (`Work.SignatureBordism.p₁SqNumber_neg`).

Making the construction choice-free — so that naturality, the Whitney formula and stability become
provable — is item (G1) of `README.md` ADDENDUM 20.

## What is defined

* `Work.Thom.tautQuotient` — the tautological quotient, with its defining equations
  `tautQuotient_baseSet`, `tautQuotient_indexAt`, `tautQuotient_coordChange`;
* `Work.Thom.thomClassRank` — the Thom class of the realification of a complex bundle;
* `Work.Thom.chernClass m j Z` — the `j`-th Chern class of `Z`, a complex bundle of rank `m`.
-/

namespace Work.Thom

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type}

/-! ## The tautological quotient, as a named object -/

/-- **The tautological quotient** `Q = pi^*V / C.s` of a complex bundle `V` of rank `m + 1` over
the punctured total space `X = V \ 0`, with an **explicit index map**: the chosen index at a point
`p` is *definitionally* the pair of the base index of `Z` at `p` together with the chosen
non-vanishing coordinate `Work.Thom.tqCoord` (`Work.Thom.exists_tautQuotientCore`).  This is what
makes the construction natural under pullback, and it removes one of the `Classical.choose`s of the
Chern recursion. -/
noncomputable def tautQuotientCore {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) :
    VectorBundleCore ℂ ↥(zeroComplement (realification Z)) (EuclideanSpace ℂ (Fin m))
      (ι × Fin (m + 1)) :=
  Classical.choose (exists_tautQuotientCore Z)

/-- The index map of the tautological quotient, **explicitly**. -/
theorem tautQuotientCore_indexAt {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (p : ↥(zeroComplement (realification Z))) :
    (tautQuotientCore Z).indexAt p =
      (Z.indexAt ((p : (realification Z).TotalSpace).1), Work.Thom.tqCoord Z p) :=
  (Classical.choose_spec (exists_tautQuotientCore Z)).1 p

/-- The base set of the tautological quotient over the piece `(i,k)`. -/
theorem tautQuotientCore_baseSet {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) (i : ι) (k : Fin (m + 1)) :
    (tautQuotientCore Z).baseSet (i, k) = Work.Thom.tqBaseSet Z i k :=
  (Classical.choose_spec (exists_tautQuotientCore Z)).2.1 i k

/-- The transition functions of the tautological quotient (`quoFun`). -/
theorem tautQuotientCore_coordChange {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (i j : ι) (k l : Fin (m + 1)) (p : ↥(zeroComplement (realification Z)))
    (z : EuclideanSpace ℂ (Fin m)) :
    (tautQuotientCore Z).coordChange (i, k) (j, l) p z =
      Work.Thom.quoFun l ((Z.localTriv j (p : (realification Z).TotalSpace)).2)
        (Z.coordChange i j ((p : (realification Z).TotalSpace)).1
          (Work.Thom.fillFun k z)) :=
  (Classical.choose_spec (exists_tautQuotientCore Z)).2.2 i j k l p z

/-- **The tautological quotient** `Q = pi^*V / C.s` of a complex bundle `V` of rank `m + 1` over
the punctured total space `X = V \ 0`, as a complex bundle of rank `m` indexed by `ι × Fin (m+1)`.
This is `Work.Thom.tautQuotientCore`. -/
noncomputable def tautQuotient {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) :
    VectorBundleCore ℂ ↥(zeroComplement (realification Z)) (EuclideanSpace ℂ (Fin m))
      (ι × Fin (m + 1)) :=
  tautQuotientCore Z

/-- The base set of the tautological quotient over the piece `(i,k)` (the defining equation of
`Work.Thom.tautologicalQuotient`). -/
theorem tautQuotient_baseSet {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) (i : ι) (k : Fin (m + 1)) :
    (tautQuotient Z).baseSet (i, k) =
      {p : ↥(zeroComplement (realification Z)) |
        ((p : (realification Z).TotalSpace).1) ∈ Z.baseSet i ∧
          (Z.localTriv i ((p : (realification Z).TotalSpace))).2 k ≠ 0} :=
  tautQuotientCore_baseSet Z i k

/-- The index map of the tautological quotient, **explicitly** (this is stronger than
`tautQuotient_indexAt`: it identifies the second component too). -/
theorem tautQuotient_indexAt_eq {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (p : ↥(zeroComplement (realification Z))) :
    (tautQuotient Z).indexAt p =
      (Z.indexAt ((p : (realification Z).TotalSpace).1), Work.Thom.tqCoord Z p) :=
  tautQuotientCore_indexAt Z p

/-- The index map of the tautological quotient (the defining equation of
`Work.Thom.tautologicalQuotient`). -/
theorem tautQuotient_indexAt {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (p : ↥(zeroComplement (realification Z))) :
    ((tautQuotient Z).indexAt p).1 = Z.indexAt ((p : (realification Z).TotalSpace).1) ∧
      (Z.localTriv (Z.indexAt ((p : (realification Z).TotalSpace).1))
        ((p : (realification Z).TotalSpace))).2 ((tautQuotient Z).indexAt p).2 ≠ 0 := by
  rw [tautQuotient_indexAt_eq]
  exact ⟨rfl, Work.Thom.tqCoord_spec Z p⟩

/-- The transition functions of the tautological quotient (the defining equation of
`Work.Thom.tautologicalQuotient`): `quoFun`. -/
theorem tautQuotient_coordChange {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (i j : ι) (k l : Fin (m + 1)) (p : ↥(zeroComplement (realification Z)))
    (z : EuclideanSpace ℂ (Fin m)) :
    (tautQuotient Z).coordChange (i, k) (j, l) p z =
      Work.Thom.quoFun l ((Z.localTriv j (p : (realification Z).TotalSpace)).2)
        (Z.coordChange i j ((p : (realification Z).TotalSpace)).1
          (Work.Thom.fillFun k z)) :=
  tautQuotientCore_coordChange Z i j k l p z

/-- **The canonical identification of the cohomology in two equal degrees**, as a **`ℤ`-linear
map**: since `Coh ℤ n B` and `Coh ℤ n' B` are *equal objects* of `ModuleCat ℤ` when `n = n'`, the
transport is an isomorphism in the category, hence linear.  (This is the form to use when the
transported class has to interact with the module structure; `Work.Thom.cohTransport` is the same
map as a function.) -/
noncomputable def cohTransportLM {B : Type} [TopologicalSpace B] {n n' : ℕ} (h : n = n') :
    Coh ℤ n B →ₗ[ℤ] Coh ℤ n' B :=
  (CategoryTheory.eqToIso (congrArg (fun t : ℕ => Coh ℤ t B) h)).hom.hom

/-- **The canonical identification of the cohomology in two equal degrees**, as a function. -/
noncomputable def cohTransport {B : Type} [TopologicalSpace B] {n n' : ℕ} (h : n = n') :
    Coh ℤ n B → Coh ℤ n' B :=
  cohTransportLM h

@[simp] theorem cohTransportLM_rfl {B : Type} [TopologicalSpace B] {n : ℕ} :
    cohTransportLM (rfl : n = n) = (LinearMap.id : Coh ℤ n B →ₗ[ℤ] Coh ℤ n B) := by
  rw [cohTransportLM, CategoryTheory.eqToIso_refl]
  rfl

@[simp] theorem cohTransport_rfl {B : Type} [TopologicalSpace B] {n : ℕ} (x : Coh ℤ n B) :
    cohTransport (rfl : n = n) x = x := by
  rw [cohTransport, cohTransportLM_rfl]
  rfl

theorem cohTransportLM_apply {B : Type} [TopologicalSpace B] {n n' : ℕ} (h : n = n')
    (x : Coh ℤ n B) : cohTransportLM h x = cohTransport h x := rfl

/-! ## The recursion -/

/-- **The Thom class of the realification** of a complex bundle of rank `j ≥ 1` over a finite
gluing-data cover.  It is the **canonical** (choice-free up to uniqueness-backed `Classical.choose`s)
construction `Work.Thom.thomClassOf` of `Submission/Work/Thom/thomClassOf.lean`, not
`Classical.choice` of the existence theorem — this is what makes the top Chern class functorial.
Its Euler class is the top Chern class `c_j`. -/
noncomputable def thomClassRank (j : ℕ) (hj : 1 ≤ j) [Fintype ι]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin j)) ι) :
    ThomClass (realification Z) (2 * j) :=
  thomClassOf hj Z

/-- `Work.Thom.thomClassRank` is the canonical construction `Work.Thom.thomClassOf`. -/
theorem thomClassRank_def (j : ℕ) (hj : 1 ≤ j) [Fintype ι]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin j)) ι) :
    thomClassRank j hj Z = thomClassOf hj Z := rfl

/-- **The rank-`0` case of the Chern classes**: `c_0 = 1` (the unit class `Work.Cohomology.oneH`)
and `c_j = 0` for `j ≥ 1`. -/
noncomputable def chernClassZero (j : ℕ) {B : Type} [TopologicalSpace B] {ι : Type}
    [Fintype ι] (_Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 0)) ι) : Coh ℤ (2 * j) B :=
  if h : j = 0 then
    cohTransport (congrArg (fun t : ℕ => 2 * t) h.symm)
      (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of B)))
  else 0

/-- **The step of the recursion**: the Chern classes of a bundle of rank `m + 1`, from those of the
tautological quotient `Q` of rank `m` (over the punctured total space, whose index type
`ι × Fin (m+1)` is finite). -/
noncomputable def chernClassStep (m : ℕ)
    (rec : (j : ℕ) → {B : Type} → [TopologicalSpace B] → {ι : Type} → [Fintype ι] →
      VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι → Coh ℤ (2 * j) B)
    (j : ℕ) {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) : Coh ℤ (2 * j) B :=
  if h : j ≤ m then
    ((LinearEquiv.ofBijective
      ((CohMap ((bundleProj (realification Z)).comp
        (subtypeMap (zeroComplement (realification Z)))) ℤ (2 * j)).hom)
      (bijective_proj_zeroComplementA (realification Z) (finrank_real_euclidean_complex (m + 1))
        (thomClassRank (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) Z) (by omega))).symm)
      (rec j (tautQuotient (m := m) Z))
  else if hj : j = m + 1 then
    cohTransport (congrArg (fun t : ℕ => 2 * t) hj.symm)
      (thomClassRank (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) Z).eulerClass
  else 0

/-- **The Chern classes of a complex vector bundle** of rank `m` over a finite gluing-data cover:
`c_j(V) ∈ H^{2j}(B;ℤ)`, defined by recursion on the rank (see the module docstring). -/
noncomputable def chernClass (m : ℕ) : (j : ℕ) → {B : Type} → [TopologicalSpace B] →
    {ι : Type} → [Fintype ι] → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι →
      Coh ℤ (2 * j) B :=
  Nat.rec (motive := fun m => (j : ℕ) → {B : Type} → [TopologicalSpace B] → {ι : Type} →
      [Fintype ι] → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι → Coh ℤ (2 * j) B)
    chernClassZero (fun m rec => chernClassStep m rec) m

/-- The unfolding of `chernClass` at `0`: the rank-`0` case. -/
theorem chernClass_zero_rank {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 0)) ι) (j : ℕ) :
    chernClass 0 j Z = chernClassZero j Z := rfl

/-- The unfolding of `chernClass` at a successor rank. -/
theorem chernClass_succ_def {m : ℕ} {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) (j : ℕ) :
    chernClass (m + 1) j Z = chernClassStep m (chernClass m) j Z := rfl

/-- The **descent equation** of the recursion: for `j ≤ m` (so that `j` is at most the rank of the
tautological quotient), `c_j` of a bundle of rank `m+1` is the inverse image of `c_j` of the
tautological quotient under the Gysin descent `pi^*`. -/
theorem chernClass_succ_of_le {m : ℕ} {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) {j : ℕ} (h : j ≤ m) :
    chernClass (m + 1) j Z =
      ((LinearEquiv.ofBijective
        ((CohMap ((bundleProj (realification Z)).comp
          (subtypeMap (zeroComplement (realification Z)))) ℤ (2 * j)).hom)
        (bijective_proj_zeroComplementA (realification Z)
          (finrank_real_euclidean_complex (m + 1))
          (thomClassRank (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) Z) (by omega))).symm)
        (chernClass m j (tautQuotient (m := m) Z)) := by
  rw [chernClass_succ_def]
  unfold chernClassStep
  rw [dif_pos h]

/-- The **top** equation of the recursion: `c_{m+1}` of a bundle of rank `m+1` is the Euler class
of its realification, i.e. the top Chern class. -/
theorem chernClass_succ_top {m : ℕ} {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) :
    chernClass (m + 1) (m + 1) Z =
      cohTransport (rfl : 2 * (m + 1) = 2 * (m + 1))
        (thomClassRank (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) Z).eulerClass := by
  rw [chernClass_succ_def]
  unfold chernClassStep
  rw [dif_neg (by omega : ¬ (m + 1 ≤ m)), dif_pos rfl]

/-- The **top** equation of the recursion, in the form used by callers: `c_{m+1}` is the Euler
class of the realification, with the degree cast collapsed. -/
theorem chernClass_succ_top' {m : ℕ} {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) :
    chernClass (m + 1) (m + 1) Z =
      (thomClassRank (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) Z).eulerClass := by
  rw [chernClass_succ_top, cohTransport_rfl]

/-- **The top Chern class of a rank-one complex bundle is the Euler class of its realification** —
the base case of the recursion, in the form a caller can use without unfolding. -/
theorem chernClass_one_top {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) :
    chernClass 1 1 Z = (thomClassRank 1 (Nat.succ_le_succ (Nat.zero_le 0)) Z).eulerClass :=
  chernClass_succ_top' Z

/-- The **vanishing** of the Chern classes above the rank. -/
theorem chernClass_succ_of_gt {m j : ℕ} {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) (h : m + 1 < j) :
    chernClass (m + 1) j Z = 0 := by
  rw [chernClass_succ_def]
  unfold chernClassStep
  rw [dif_neg (by omega : ¬ (j ≤ m)), dif_neg (by omega : ¬ (j = m + 1))]

end

end Work.Thom
