import Mathlib
import Submission.Work.StemsB.Rat.CollarDefs
import Submission.Work.StemsB.Rat.CollarSplit
import Submission.Work.StemsB.Rat.CollarSqGeom
import Submission.Work.StemsB.Rat.H0EvalRat
import Submission.Work.StemsB.Rat.RatMixedCupAssoc
import Submission.Work.StemsB.Rat.H0UnitRat
import Submission.Work.StemsB.AToolsR
import Submission.Work.StemsB.PairDeltaNaturalR
import Submission.Work.StemsB.MixedCupR
import Submission.Work.Cohomology.cupNaturalH
import Submission.Work.Cohomology.punit

/-!
# The `ℚ`-coefficient crux of the collar suspension class

This is the `ℚ`-coefficient (and, over `ℚ`, *simpler*) version of
`Submission/Work/StemsB/collarSqCrux2.lean`:

* `collarThom_delta_of` : for a class `gen ∈ H^{b-1}(C)` of the collar over a point whose
  transgression is a generator of `H^b(Q,C;ℚ)`, the transgression of the pullback of `gen` along
  the collar projection is a **Thom class** of the collar over `Y`.

The only difference with the `ℤ` argument is in the "unit transfer" `collarThom_of_unit`: over `ℤ`
one knows `u ⌣ u = 1` for the comparison class `u ∈ H⁰(Y;ℤ)`, whereas over `ℚ` one only knows that
all the point evaluations of `u` are non-zero (`hunit` below, where the fibre computation now gives
`u(y) * Φ₁(fibre_y τ₀) = 1` directly, without the `±1` argument), so the multiplication map
`x ↦ x ⌣ u` is inverted by `x ↦ x ⌣ v` for a class `v` with `u ⌣ v = 1`
(`Work.StemsB.Rat.H0UnitRat`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Work.StemsB.Rat

open CategoryTheory CategoryTheory.Limits
open scoped Topology Simplicial

noncomputable section

/-! ## Casts -/

theorem eqToHom_homology_apply {K : CochainComplex (ModuleCat ℚ) ℕ} {a b : ℕ} (h : a = b)
    (x : K.homology a) :
    (CategoryTheory.eqToHom (congrArg (fun t => K.homology t) h)) x = (h ▸ x : K.homology b) := by
  cases h; rfl

theorem relDegEquiv_eq_eqToHom {X : Type} [TopologicalSpace X] (A : Set X) {a b : ℕ} (h : a = b)
    (x : Work.Thom.RelCoh ℚ a X A) :
    (relDegEquiv A h) x
      = (CategoryTheory.eqToHom (congrArg (fun t =>
          (Work.Cohomology.relComplex ℚ (TopCat.of X) A).homology t) h)) x := by
  cases h; rfl

theorem eqToHom_symm_relDegEquiv {X : Type} [TopologicalSpace X] (A : Set X) {a b : ℕ}
    (h : a = b) (x : Work.Thom.RelCoh ℚ a X A) :
    (CategoryTheory.eqToHom (congrArg (fun t =>
        (Work.Cohomology.relComplex ℚ (TopCat.of X) A).homology t) h.symm))
      ((relDegEquiv A h) x) = x := by
  rw [relDegEquiv_eq_eqToHom A h x]
  exact eqToHom_symm_hom (K := Work.Cohomology.relComplex ℚ (TopCat.of X) A) h x

theorem mixedCupC_relDegEquiv_right {X : Type} [TopologicalSpace X] (A : Set X) (m : ℕ)
    {k k' : ℕ} (h : k = k') (a : Work.Thom.Coh ℚ m X) (z : Work.Thom.RelCoh ℚ k X A) :
    (Work.Thom.mixedCupC ℚ A m k') a ((relDegEquiv A h) z)
      = (congrArg (fun t => m + t) h) ▸ ((Work.Thom.mixedCupC ℚ A m k) a z) := by
  cases h; rfl

/-- Degree transports commute with the pullback of relative cohomology along a map of pairs. -/
theorem relCohMap_relDegEquiv {X X' : Type} [TopologicalSpace X] [TopologicalSpace X']
    (A : Set X) (A' : Set X') (f : C(X, X')) (hf : ∀ x ∈ A, f x ∈ A') {i j : ℕ} (h : i = j)
    (x : Work.Thom.RelCoh ℚ i X' A') :
    (Work.Thom.relCohMap f A A' hf ℚ j).hom ((relDegEquiv A' h) x)
      = (relDegEquiv A h) ((Work.Thom.relCohMap f A A' hf ℚ i).hom x) := by
  cases h; rfl

/-- Equal continuous maps induce the same pullback on cohomology. -/
theorem CohMap_congr {B₁ B₂ : Type} [TopologicalSpace B₁] [TopologicalSpace B₂] {f g : C(B₁, B₂)}
    (h : f = g) (R : Type) [CommRing R] (n : ℕ) :
    (Work.Thom.CohMap f R n).hom = (Work.Thom.CohMap g R n).hom := by
  rcases h with rfl; rfl

/-- The mixed cup product is linear in its first argument. -/
theorem mixedCupC_smul_left {X : Type} [TopologicalSpace X] (A : Set X) (m n : ℕ) (c : ℚ)
    (a : Work.Thom.Coh ℚ m X) (z : Work.Thom.RelCoh ℚ n X A) :
    (Work.Thom.mixedCupC ℚ A m n) (c • a) z
      = c • ((Work.Thom.mixedCupC ℚ A m n) a z) := by
  rw [map_smul]
  rfl

/-- The fibre inclusion of the collar, written in the shape produced by
`Work.StemsB.pairDeltaNaturalR`.  It is definitionally `collarFibSub`. -/
abbrev collarFibSubA (b : ℕ) (Y : Type) [TopologicalSpace Y] (y : Y) :
    C(↥(sphLoopCollarProd b PUnit), ↥(sphLoopCollarProd b Y)) :=
  ⟨fun a => (⟨(collarFib (Y := Y) b y) ↑a, collarFib_mem (Y := Y) b y ↑a a.2⟩ :
      ↥(sphLoopCollarProd b Y)), by fun_prop⟩

/-! ## The mixed cup product with the unit class over `ℚ` -/

/-- Transporting a cohomology class along an equality of degrees commutes with `homologyπ`. -/
theorem cast_homologyπ_ccQ {R : Type} [CommRing R] (K : CochainComplex (ModuleCat R) ℕ)
    {a b : ℕ} (h : a = b) (x : K.cycles a) :
    h ▸ ((K.homologyπ a).hom x) = (K.homologyπ b).hom (h ▸ x) := by
  cases h; rfl

/-- Transporting a cycle along an equality of degrees commutes with `iCycles`. -/
theorem cast_iCycles_ccQ {R : Type} [CommRing R] (K : CochainComplex (ModuleCat R) ℕ)
    {a b : ℕ} (h : a = b) (x : K.cycles a) :
    h ▸ ((K.iCycles a).hom x) = (K.iCycles b).hom (h ▸ x) := by
  cases h; rfl

/-- Transporting a relative cohomology class along an equality of degrees and back is the
identity. -/
theorem relCoh_symm_cast_castQ {X : TopCat} (A : Set X) {p q : ℕ} (h : p = q)
    (x : Work.Cohomology.relCohomology ℚ X A p) :
    h.symm ▸ (h ▸ x) = x := by cases h; rfl

/-- **The mixed cup product with the unit class `1 ∈ H⁰(ℚ)` is the identity** on relative
cohomology, over `ℚ`. -/
theorem mixedCupR_oneH_zero (X : TopCat) (A : Set X) (n : ℕ)
    (y : Work.Cohomology.relCohomology ℚ X A n) :
    Work.Cohomology.mixedCupR ℚ X A 0 n (Work.Cohomology.oneH ℚ (TopCat.toSSet.obj X)) y
      = (Nat.zero_add n).symm ▸ y := by
  obtain ⟨b, hb, rfl⟩ := Work.Cohomology.exists_relClassOf ℚ X A n y
  obtain ⟨hmem, h, hcup⟩ :=
    Work.Cohomology.mixedCupR_apply ℚ X A 0 n
      (Work.Cohomology.unitCochain ℚ (TopCat.toSSet.obj X)) b
      (Work.Cohomology.cochainDiff_unitCochain ℚ (TopCat.toSSet.obj X)) hb
  rw [show Work.Cohomology.oneH ℚ (TopCat.toSSet.obj X)
        = Work.Cohomology.cohomologyClassOf ℚ (TopCat.toSSet.obj X)
            (Work.Cohomology.unitCochain ℚ (TopCat.toSSet.obj X))
            (Work.Cohomology.cochainDiff_unitCochain ℚ (TopCat.toSSet.obj X)) from rfl]
  rw [hcup]
  have hmain : (Nat.zero_add n) ▸ Work.Cohomology.relClassOf ℚ X A
        ⟨Work.Cohomology.cup ℚ (TopCat.toSSet.obj X)
          (Work.Cohomology.unitCochain ℚ (TopCat.toSSet.obj X)) b.1, hmem⟩ h
      = Work.Cohomology.relClassOf ℚ X A b hb := by
    have hcyc : (Nat.zero_add n) ▸ Work.Cohomology.relCocycleOf ℚ X A
          ⟨Work.Cohomology.cup ℚ (TopCat.toSSet.obj X)
            (Work.Cohomology.unitCochain ℚ (TopCat.toSSet.obj X)) b.1, hmem⟩ h
        = Work.Cohomology.relCocycleOf ℚ X A b hb := by
      apply Work.Cohomology.iCycles_injective_K (Work.Cohomology.relComplex ℚ X A) n
      rw [← cast_iCycles_ccQ (Work.Cohomology.relComplex ℚ X A) (Nat.zero_add n)
            (Work.Cohomology.relCocycleOf ℚ X A
              ⟨Work.Cohomology.cup ℚ (TopCat.toSSet.obj X)
                (Work.Cohomology.unitCochain ℚ (TopCat.toSSet.obj X)) b.1, hmem⟩ h)]
      rw [Work.Cohomology.iCycles_relCocycleOf ℚ X A
            ⟨Work.Cohomology.cup ℚ (TopCat.toSSet.obj X)
              (Work.Cohomology.unitCochain ℚ (TopCat.toSSet.obj X)) b.1, hmem⟩ h,
          Work.Cohomology.iCycles_relCocycleOf ℚ X A b hb]
      apply Subtype.ext
      rw [Work.Cohomology.eqRec_relKern_coe]
      exact (Work.Cohomology.cupUnit ℚ (TopCat.toSSet.obj X) b.1).1
    show (Nat.zero_add n) ▸ ((Work.Cohomology.relComplex ℚ X A).homologyπ (0 + n)).hom
        (Work.Cohomology.relCocycleOf ℚ X A
          ⟨Work.Cohomology.cup ℚ (TopCat.toSSet.obj X)
            (Work.Cohomology.unitCochain ℚ (TopCat.toSSet.obj X)) b.1, hmem⟩ h)
      = Work.Cohomology.relClassOf ℚ X A b hb
    rw [cast_homologyπ_ccQ (Work.Cohomology.relComplex ℚ X A) (Nat.zero_add n)
          (Work.Cohomology.relCocycleOf ℚ X A _ h), hcyc]
    rfl
  have h2 : (Nat.zero_add n).symm ▸ ((Nat.zero_add n) ▸ Work.Cohomology.relClassOf ℚ X A
        ⟨Work.Cohomology.cup ℚ (TopCat.toSSet.obj X)
          (Work.Cohomology.unitCochain ℚ (TopCat.toSSet.obj X)) b.1, hmem⟩ h)
      = (Nat.zero_add n).symm ▸ Work.Cohomology.relClassOf ℚ X A b hb :=
    congrArg (fun w => (Nat.zero_add n).symm ▸ w) hmain
  rwa [relCoh_symm_cast_castQ A (Nat.zero_add n) _] at h2

/-- The unit law of the mixed cup product, in the form of `Work.Thom.RelCoh`. -/
theorem mixedCupC_oneH_zeroQ {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ)
    (y : Work.Thom.RelCoh ℚ n X A) :
    (Work.Thom.mixedCupC ℚ A 0 n)
        (Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of X))) y
      = (Nat.zero_add n).symm ▸ y :=
  mixedCupR_oneH_zero (TopCat.of X) A n y

/-! ## Degree-zero evaluation facts -/

/-- The pullback along a constant map of a class in `H⁰` is a scalar multiple of the unit. -/
theorem CohMap_h0Const {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (y : Y) (hf : ∀ x, f x = y) (u : Work.Thom.Coh ℚ 0 Y) :
    (Work.Thom.CohMap f ℚ 0).hom u
      = (h0EvQ (TopCat.toSSet.obj (TopCat.of Y))
          (TopCat.toSSetObj₀Equiv.symm y) u)
        • (Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of X))) := by
  refine h0EvQ_ext (fun t => ?_)
  show h0EvQ (TopCat.toSSet.obj (TopCat.of X)) t
      ((Work.Thom.CohMap f ℚ 0).hom u) = _
  rw [h0EvQ_CohMap]
  rw [show (TopCat.toSSet.map (TopCat.ofHom f)).app (Opposite.op (SimplexCategory.mk 0)) t
      = TopCat.toSSetObj₀Equiv.symm y from by
    apply TopCat.toSSetObj₀Equiv.injective
    rw [toSSetObj₀Equiv_mapQ, Equiv.apply_symm_apply]
    exact hf _]
  simp only [map_smul, h0EvQ_oneH, smul_eq_mul, mul_one]

/-! ## The unit transfer -/

/-- **The unit transfer**: if `τ₀` is a Thom class of the collar pair and `u, v ∈ H⁰(Y)` satisfy
`u ⌣ v = 1`, then `π^*(u) ⌣ τ₀` is again a Thom class. -/
theorem collarThom_of_unit (b : ℕ) (hb : 2 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ₀ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ₀ : CollarThom (Y := Y) b τ₀)
    (u v : Work.Thom.Coh ℚ 0 Y)
    (huv : Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (TopCat.of Y)) 0 0 u v
      = Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of Y))) :
    CollarThom (Y := Y) b
      ((relDegEquiv (sphLoopCollarProd b Y) (Nat.zero_add b))
        ((Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) 0 b)
          ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ 0).hom u) τ₀)) := by
  let τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y) :=
    (relDegEquiv (sphLoopCollarProd b Y) (Nat.zero_add b))
      ((Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) 0 b)
        ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ 0).hom u) τ₀)
  have hgoal : CollarThom (Y := Y) b τ := by
    intro m
    -- `v` is a two-sided inverse: `v ⌣ u = 1` follows from `u ⌣ v = 1` by separation
    have hvu : Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (TopCat.of Y)) 0 0 v u
        = Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of Y)) := by
      refine h0EvQ_ext (fun s => ?_)
      have h2 : h0EvQ (TopCat.toSSet.obj (TopCat.of Y)) s u
          * h0EvQ (TopCat.toSSet.obj (TopCat.of Y)) s v = 1 := by
        have h3 := congrArg (h0EvQ (TopCat.toSSet.obj (TopCat.of Y)) s) huv
        rwa [h0EvQ_cup, h0EvQ_oneH] at h3
      rw [h0EvQ_cup, h0EvQ_oneH]
      rw [mul_comm (h0EvQ (TopCat.toSSet.obj (TopCat.of Y)) s v)
        (h0EvQ (TopCat.toSSet.obj (TopCat.of Y)) s u)]
      exact h2
    have hΨ1 : ∀ y : Work.Thom.Coh ℚ m Y,
        Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (TopCat.of Y)) m 0
          (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (TopCat.of Y)) m 0 y v) u = y := by
      intro y
      have h := Work.Cohomology.cupH'_assoc (R := ℚ)
        (X := TopCat.toSSet.obj (TopCat.of Y)) m 0 0 y v u
      rw [hvu, Work.Cohomology.cupH'_one_right] at h
      simpa using h
    have hΨ2 : ∀ y : Work.Thom.Coh ℚ m Y,
        Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (TopCat.of Y)) m 0
          (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (TopCat.of Y)) m 0 y u) v = y := by
      intro y
      have h := Work.Cohomology.cupH'_assoc (R := ℚ)
        (X := TopCat.toSSet.obj (TopCat.of Y)) m 0 0 y u v
      rw [huv, Work.Cohomology.cupH'_one_right] at h
      simpa using h
    have hΨbij : Function.Bijective (fun y : Work.Thom.Coh ℚ m Y =>
        Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (TopCat.of Y)) m 0 y u) := by
      refine ⟨fun x y hxy => ?_, fun y => ⟨(Work.Cohomology.cupH' ℚ
        (TopCat.toSSet.obj (TopCat.of Y)) m 0 y) v, hΨ1 y⟩⟩
      have h1 : Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (TopCat.of Y)) m 0
            (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (TopCat.of Y)) m 0 x u) v
          = Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (TopCat.of Y)) m 0
            (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (TopCat.of Y)) m 0 y u) v :=
        congrArg (fun w => Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (TopCat.of Y)) m 0 w v) hxy
      rw [hΨ2 x, hΨ2 y] at h1
      exact h1
    have hpt : ∀ x : Work.Thom.Coh ℚ m Y,
        (collarPhi (Y := Y) b τ m) x
          = (relDegEquiv (sphLoopCollarProd b Y) (congrArg (fun t => m + t) (Nat.zero_add b)))
              ((relDegEquiv (sphLoopCollarProd b Y) (Nat.add_assoc m 0 b))
                ((collarPhi (Y := Y) b τ₀ m)
                  (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (TopCat.of Y)) m 0 x u))) := by
      intro x
      show (Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) m b)
          ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ m).hom x)
          ((relDegEquiv (sphLoopCollarProd b Y) (Nat.zero_add b))
            ((Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) 0 b)
              ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ 0).hom u) τ₀)) = _
      rw [mixedCupC_relDegEquiv_right (sphLoopCollarProd b Y) m (Nat.zero_add b)
        ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ m).hom x)
        ((Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) 0 b)
          ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ 0).hom u) τ₀)]
      rw [show (Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) m (0 + b))
          ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ m).hom x)
          ((Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) 0 b)
            ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ 0).hom u) τ₀)
        = (Nat.add_assoc m 0 b) ▸ ((Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) m b)
            ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (TopCat.of (↥(sphLoopBig b) × Y))) m 0)
              ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ m).hom x)
              ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ 0).hom u)) τ₀) from
        RatMixedCupAssoc (sphLoopCollarProd b Y) m b
          ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ m).hom x)
          ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ 0).hom u) τ₀]
      rw [show (Work.Cohomology.cupH' ℚ
            (TopCat.toSSet.obj (TopCat.of (↥(sphLoopBig b) × Y))) m 0)
            ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ m).hom x)
            ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ 0).hom u)
          = (Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ m).hom
              (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (TopCat.of Y)) m 0 x u) from
        (Work.Cohomology.cupNaturalH ℚ (TopCat.ofHom (collarProjY (Y := Y) b)) m 0 x u).symm]
      rfl
    have hF : Function.Bijective (fun z : Work.Thom.RelCoh ℚ (m + b)
          (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y) =>
        (relDegEquiv (sphLoopCollarProd b Y) (congrArg (fun t => m + t) (Nat.zero_add b)))
          ((relDegEquiv (sphLoopCollarProd b Y) (Nat.add_assoc m 0 b)) z)) :=
      (relDegEquiv (sphLoopCollarProd b Y)
        (congrArg (fun t => m + t) (Nat.zero_add b))).bijective.comp
        (relDegEquiv (sphLoopCollarProd b Y) (Nat.add_assoc m 0 b)).bijective
    have hfun : ⇑(collarPhi (Y := Y) b τ m)
        = (fun z : Work.Thom.RelCoh ℚ (m + b) (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y) =>
            (relDegEquiv (sphLoopCollarProd b Y) (congrArg (fun t => m + t) (Nat.zero_add b)))
              ((relDegEquiv (sphLoopCollarProd b Y) (Nat.add_assoc m 0 b)) z))
          ∘ (⇑(collarPhi (Y := Y) b τ₀ m)) ∘ (fun y : Work.Thom.Coh ℚ m Y =>
              Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (TopCat.of Y)) m 0 y u) := by
      funext x; exact hpt x
    rw [hfun]
    simpa only [Function.comp_assoc] using hF.comp ((hτ₀ m).comp hΨbij)
  exact hgoal

/-! ## The crux: `δ` of the suspension class is a Thom class -/

/-- **The crux**: for a class `gen ∈ H^{b-1}(C)` of the collar over a point whose transgression is a
generator of `H^b(Q,C;ℚ)`, the transgression of the pullback of `gen` along the collar projection is
a Thom class of the collar over `Y`. -/
theorem collarThom_delta_of (b : ℕ) (hb : 2 ≤ b) (Y : Type) [TopologicalSpace Y] (y₀ : Y)
    (Φ₁ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × PUnit) (sphLoopCollarProd b PUnit) ≃ₗ[ℚ] ℚ)
    (gen : Work.Thom.Coh ℚ (b - 1) (↥(sphLoopCollarProd b PUnit)))
    (hgen : (Work.Cohomology.pairδ ℚ (TopCat.of (↥(sphLoopBig b) × PUnit))
        (sphLoopCollarProd b PUnit) (b - 1)).hom gen
      = (relDegEquiv (sphLoopCollarProd b PUnit) (by omega : b - 1 + 1 = b)).symm (Φ₁.symm 1)) :
    ∃ τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y),
      CollarThom (Y := Y) b τ ∧
      CollarTransgresses (Y := Y) b (by omega)
        ((Work.Thom.CohMap (collarDropSub (Y := Y) b) ℚ (b - 1)).hom gen) τ := by
  classical
  obtain ⟨τ₀, hτ₀⟩ := exists_collarThom b (by omega) Y
  have hb1 : b - 1 + 1 = b := by omega
  let s : Work.Thom.Coh ℚ (b - 1) (↥(sphLoopCollarProd b Y)) :=
    (Work.Thom.CohMap (collarDropSub (Y := Y) b) ℚ (b - 1)).hom gen
  let d : Work.Thom.RelCoh ℚ (b - 1 + 1) (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y) :=
    (Work.Cohomology.pairδ ℚ (TopCat.of (↥(sphLoopBig b) × Y))
      (sphLoopCollarProd b Y) (b - 1)).hom s
  let τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y) :=
    (relDegEquiv (sphLoopCollarProd b Y) hb1) d
  refine ⟨τ, ?_, ?_⟩
  · -- ### `CollarThom τ`
    let Φ₀ : Work.Thom.Coh ℚ 0 Y ≃ₗ[ℚ] Work.Thom.RelCoh ℚ (0 + b)
        (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y) :=
      LinearEquiv.ofBijective (collarPhi (Y := Y) b τ₀ 0) (hτ₀ 0)
    let u : Work.Thom.Coh ℚ 0 Y :=
      Φ₀.symm ((relDegEquiv (sphLoopCollarProd b Y) (Nat.zero_add b)).symm τ)
    have hτu : τ = (relDegEquiv (sphLoopCollarProd b Y) (Nat.zero_add b))
        ((Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) 0 b)
          ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ 0).hom u) τ₀) := by
      have hu0 : Φ₀ u
          = (relDegEquiv (sphLoopCollarProd b Y) (Nat.zero_add b)).symm τ :=
        LinearEquiv.apply_symm_apply Φ₀ _
      have hu0' : (collarPhi (Y := Y) b τ₀ 0) u
          = (relDegEquiv (sphLoopCollarProd b Y) (Nat.zero_add b)).symm τ := by
        rw [show (collarPhi (Y := Y) b τ₀ 0) u = Φ₀ u from rfl]
        exact hu0
      rw [show (collarPhi (Y := Y) b τ₀ 0) u
          = (Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) 0 b)
              ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ 0).hom u) τ₀ from rfl] at hu0'
      rw [hu0']
      exact (LinearEquiv.apply_symm_apply _ τ).symm
    -- the fibre restriction of `s` is `gen`
    have hfibs : ∀ y : Y,
        (Work.Thom.CohMap (collarFibSubA b Y y) ℚ (b - 1)).hom s = gen := by
      intro y
      rw [show s = (Work.Thom.CohMap (collarDropSub (Y := Y) b) ℚ (b - 1)).hom gen from rfl]
      rw [show (Work.Thom.CohMap (collarFibSubA b Y y) ℚ (b - 1)).hom
          ((Work.Thom.CohMap (collarDropSub (Y := Y) b) ℚ (b - 1)).hom gen)
          = ((Work.Thom.CohMap (collarFibSubA b Y y) ℚ (b - 1)).hom ∘ₗ
              (Work.Thom.CohMap (collarDropSub (Y := Y) b) ℚ (b - 1)).hom) gen from rfl]
      rw [Work.Thom.CohMap_linear_comp (collarFibSubA b Y y)
        (collarDropSub (Y := Y) b) ℚ (b - 1)]
      rw [show (collarDropSub (Y := Y) b).comp (collarFibSubA b Y y) = ContinuousMap.id _ from by
        rw [show collarFibSubA b Y y = collarFibSub (Y := Y) b y from rfl]
        exact collarDropSub_comp_collarFibSub b y]
      simp
    -- the fibre restriction of `d` is a generator
    have hd : ∀ y : Y,
        (Work.Thom.relCohMap (collarFib (Y := Y) b y) (sphLoopCollarProd b PUnit)
            (sphLoopCollarProd b Y) (collarFib_mem (Y := Y) b y) ℚ (b - 1 + 1)).hom d
          = (relDegEquiv (sphLoopCollarProd b PUnit) hb1).symm (Φ₁.symm 1) := by
      intro y
      have h1 := Work.StemsB.pairDeltaNaturalR ℚ (collarFib (Y := Y) b y)
        (sphLoopCollarProd b PUnit) (sphLoopCollarProd b Y)
        (collarFib_mem (Y := Y) b y) (b - 1) s
      rw [show d = (Work.Cohomology.pairδ ℚ (TopCat.of (↥(sphLoopBig b) × Y))
          (sphLoopCollarProd b Y) (b - 1)).hom s from rfl]
      refine h1.trans ?_
      rw [hfibs y]
      exact hgen
    -- the fibre restriction of `τ` is `Φ₁.symm 1`
    have hfibτ : ∀ y : Y,
        (Work.Thom.relCohMap (collarFib (Y := Y) b y) (sphLoopCollarProd b PUnit)
            (sphLoopCollarProd b Y) (collarFib_mem (Y := Y) b y) ℚ b).hom τ = Φ₁.symm 1 := by
      intro y
      rw [show τ = (relDegEquiv (sphLoopCollarProd b Y) hb1) d from rfl]
      rw [relCohMap_relDegEquiv (sphLoopCollarProd b PUnit) (sphLoopCollarProd b Y)
        (collarFib (Y := Y) b y) (collarFib_mem (Y := Y) b y) hb1 d]
      rw [hd y]
      exact LinearEquiv.apply_symm_apply (relDegEquiv (sphLoopCollarProd b PUnit) hb1) (Φ₁.symm 1)
    -- the pointwise evaluation of `u` is non-zero
    have hunit : ∀ y : Y,
        h0EvQ (TopCat.toSSet.obj (TopCat.of Y))
            (TopCat.toSSetObj₀Equiv.symm y) u ≠ 0 := by
      intro y
      let A : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × PUnit) (sphLoopCollarProd b PUnit) :=
        (Work.Thom.relCohMap (collarFib (Y := Y) b y) (sphLoopCollarProd b PUnit)
          (sphLoopCollarProd b Y) (collarFib_mem (Y := Y) b y) ℚ b).hom τ₀
      let E : Work.Thom.RelCoh ℚ (0 + b) (↥(sphLoopBig b) × PUnit)
            (sphLoopCollarProd b PUnit) ≃ₗ[ℚ]
          Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × PUnit) (sphLoopCollarProd b PUnit) :=
        relDegEquiv (sphLoopCollarProd b PUnit) (Nat.zero_add b)
      let lam : ℚ := h0EvQ (TopCat.toSSet.obj (TopCat.of Y))
        (TopCat.toSSetObj₀Equiv.symm y) u
      have hB : (Work.Thom.relCohMap (collarFib (Y := Y) b y) (sphLoopCollarProd b PUnit)
          (sphLoopCollarProd b Y) (collarFib_mem (Y := Y) b y) ℚ b).hom τ
          = E (lam • (E.symm A)) := by
        rw [hτu]
        have hstep : (Work.Thom.relCohMap (collarFib (Y := Y) b y) (sphLoopCollarProd b PUnit)
            (sphLoopCollarProd b Y) (collarFib_mem (Y := Y) b y) ℚ b).hom
            ((relDegEquiv (sphLoopCollarProd b Y) (Nat.zero_add b))
              ((Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) 0 b)
                ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ 0).hom u) τ₀))
            = (relDegEquiv (sphLoopCollarProd b PUnit) (Nat.zero_add b))
              ((Work.Thom.relCohMap (collarFib (Y := Y) b y)
                (sphLoopCollarProd b PUnit) (sphLoopCollarProd b Y)
                (collarFib_mem (Y := Y) b y) ℚ (0 + b)).hom
              ((Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) 0 b)
                ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ 0).hom u) τ₀)) :=
          relCohMap_relDegEquiv (sphLoopCollarProd b PUnit) (sphLoopCollarProd b Y)
            (collarFib (Y := Y) b y) (collarFib_mem (Y := Y) b y) (Nat.zero_add b)
            ((Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) 0 b)
              ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ 0).hom u) τ₀)
        rw [hstep]
        have hZ : (Work.Thom.relCohMap (collarFib (Y := Y) b y) (sphLoopCollarProd b PUnit)
            (sphLoopCollarProd b Y) (collarFib_mem (Y := Y) b y) ℚ (0 + b)).hom
            ((Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) 0 b)
              ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ 0).hom u) τ₀)
            = lam • (E.symm A) := by
          rw [Work.StemsB.mixedCupC_pairNaturalR ℚ (collarFib (Y := Y) b y)
            (sphLoopCollarProd b PUnit) (sphLoopCollarProd b Y)
            (collarFib_mem (Y := Y) b y) 0 b
            ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ 0).hom u) τ₀]
          rw [show (Work.Thom.CohMap (collarFib (Y := Y) b y) ℚ 0).hom
              ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ 0).hom u)
              = (Work.Thom.CohMap (collarFibBase (Y := Y) b y) ℚ 0).hom u from by
            rw [show (Work.Thom.CohMap (collarFib (Y := Y) b y) ℚ 0).hom
                  ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ 0).hom u)
                = ((Work.Thom.CohMap (collarFib (Y := Y) b y) ℚ 0).hom ∘ₗ
                    (Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ 0).hom) u from rfl]
            rw [Work.Thom.CohMap_linear_comp (collarFib (Y := Y) b y)
              (collarProjY (Y := Y) b) ℚ 0]
            rw [show (collarProjY (Y := Y) b).comp (collarFib (Y := Y) b y)
                = collarFibBase (Y := Y) b y from collarProjY_comp_collarFib b y]]
          rw [CohMap_h0Const (collarFibBase (Y := Y) b y) y (fun _ => rfl) u]
          simp only [lam]
          rw [mixedCupC_smul_left]
          rw [show (Work.Thom.mixedCupC ℚ (sphLoopCollarProd b PUnit) 0 b)
              (Work.Cohomology.oneH ℚ
                (TopCat.toSSet.obj (TopCat.of (↥(sphLoopBig b) × PUnit))))
              ((Work.Thom.relCohMap (collarFib (Y := Y) b y) (sphLoopCollarProd b PUnit)
                (sphLoopCollarProd b Y) (collarFib_mem (Y := Y) b y) ℚ b).hom τ₀)
              = E.symm A from by
            rw [mixedCupC_oneH_zeroQ]
            rfl]
        rw [hZ]
      have hcomb : Φ₁.symm 1 = E (lam • (E.symm A)) := (hfibτ y).symm.trans hB
      have hE2 : E.symm (Φ₁.symm 1) = lam • (E.symm A) := by
        rw [hcomb]
        exact LinearEquiv.symm_apply_apply E _
      have hkey := congrArg (fun z => Φ₁ (E z)) hE2
      rw [LinearEquiv.apply_symm_apply] at hkey
      have h2 : E (lam • (E.symm A)) = lam • A := by
        rw [map_smul, LinearEquiv.apply_symm_apply]
      rw [h2] at hkey
      rw [map_smul] at hkey
      rw [LinearEquiv.apply_symm_apply] at hkey
      rw [smul_eq_mul] at hkey
      -- over `ℚ` the fibre computation `1 = lam * Φ₁ A` already says that `lam` is a unit
      change lam ≠ 0
      intro h
      rw [h, zero_mul] at hkey
      exact one_ne_zero hkey
    have huAll : ∀ s : (TopCat.toSSet.obj (TopCat.of Y)).obj
        (Opposite.op (SimplexCategory.mk 0)),
        h0EvQ (TopCat.toSSet.obj (TopCat.of Y)) s u ≠ 0 := by
      intro s
      have h := hunit (TopCat.toSSetObj₀Equiv s)
      rwa [Equiv.symm_apply_apply] at h
    have hu : ∃ v : Work.Thom.Coh ℚ 0 Y,
        Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (TopCat.of Y)) 0 0 u v
          = Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of Y)) :=
      H0UnitRat u huAll
    obtain ⟨v, huv⟩ := hu
    rw [hτu]
    exact collarThom_of_unit b hb Y τ₀ hτ₀ u v huv
  · -- ### `CollarTransgresses s τ`
    unfold CollarTransgresses
    exact (eqToHom_symm_relDegEquiv (sphLoopCollarProd b Y) hb1 d).symm

end

end Work.StemsB.Rat
