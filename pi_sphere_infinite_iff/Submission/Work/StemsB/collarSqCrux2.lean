import Mathlib
import Submission.Work.StemsB.collarSqGeom
import Submission.Work.StemsB.collarSqEval
import Submission.Work.StemsB.collarSqMixed
import Submission.Work.StemsB.collarSplit
import Submission.Work.Thom.pairDeltaNatural
import Submission.Work.Thom.mixedCupC_pairNatural
import Submission.Work.Cohomology.cupNaturalH
import Submission.Work.Cohomology.punit

set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

namespace Work.StemsB

open CategoryTheory CategoryTheory.Limits
open scoped Topology Simplicial

noncomputable section

/-! ## Casts -/

theorem eqToHom_homology_apply {K : CochainComplex (ModuleCat ℤ) ℕ} {a b : ℕ} (h : a = b)
    (x : K.homology a) :
    (CategoryTheory.eqToHom (congrArg (fun t => K.homology t) h)) x = (h ▸ x : K.homology b) := by
  cases h; rfl

theorem relDegEquiv_eq_eqToHom {X : Type} [TopologicalSpace X] (A : Set X) {a b : ℕ} (h : a = b)
    (x : Work.Thom.RelCoh ℤ a X A) :
    (relDegEquiv A h) x
      = (CategoryTheory.eqToHom (congrArg (fun t =>
          (Work.Cohomology.relComplex ℤ (TopCat.of X) A).homology t) h)) x := by
  cases h; rfl

theorem eqToHom_symm_relDegEquiv {X : Type} [TopologicalSpace X] (A : Set X) {a b : ℕ}
    (h : a = b) (x : Work.Thom.RelCoh ℤ a X A) :
    (CategoryTheory.eqToHom (congrArg (fun t =>
        (Work.Cohomology.relComplex ℤ (TopCat.of X) A).homology t) h.symm))
      ((relDegEquiv A h) x) = x := by
  rw [relDegEquiv_eq_eqToHom A h x]
  exact eqToHom_symm_hom (K := Work.Cohomology.relComplex ℤ (TopCat.of X) A) h x

theorem mixedCupC_relDegEquiv_right {X : Type} [TopologicalSpace X] (A : Set X) (m : ℕ)
    {k k' : ℕ} (h : k = k') (a : Work.Thom.Coh ℤ m X) (z : Work.Thom.RelCoh ℤ k X A) :
    (Work.Thom.mixedCupC ℤ A m k') a ((relDegEquiv A h) z)
      = (congrArg (fun t => m + t) h) ▸ ((Work.Thom.mixedCupC ℤ A m k) a z) := by
  cases h; rfl

/-- Degree transports commute with the pullback of relative cohomology along a map of pairs. -/
theorem relCohMap_relDegEquiv {X X' : Type} [TopologicalSpace X] [TopologicalSpace X']
    (A : Set X) (A' : Set X') (f : C(X, X')) (hf : ∀ x ∈ A, f x ∈ A') {i j : ℕ} (h : i = j)
    (x : Work.Thom.RelCoh ℤ i X' A') :
    (Work.Thom.relCohMap f A A' hf ℤ j).hom ((relDegEquiv A' h) x)
      = (relDegEquiv A h) ((Work.Thom.relCohMap f A A' hf ℤ i).hom x) := by
  cases h; rfl

/-- Equal continuous maps induce the same pullback on cohomology. -/
theorem CohMap_congr {B₁ B₂ : Type} [TopologicalSpace B₁] [TopologicalSpace B₂] {f g : C(B₁, B₂)}
    (h : f = g) (R : Type) [CommRing R] (n : ℕ) :
    (Work.Thom.CohMap f R n).hom = (Work.Thom.CohMap g R n).hom := by
  rcases h with rfl; rfl

/-- The mixed cup product is linear in its first argument. -/
theorem mixedCupC_smul_left {X : Type} [TopologicalSpace X] (A : Set X) (m n : ℕ) (c : ℤ)
    (a : Work.Thom.Coh ℤ m X) (z : Work.Thom.RelCoh ℤ n X A) :
    (Work.Thom.mixedCupC ℤ A m n) (c • a) z
      = c • ((Work.Thom.mixedCupC ℤ A m n) a z) := by
  rw [map_zsmul]
  rfl

/-- The fibre inclusion of the collar, written in the shape produced by
`Work.Thom.pairDeltaNatural`.  It is definitionally `collarFibSub`. -/
abbrev collarFibSubA (b : ℕ) (Y : Type) [TopologicalSpace Y] (y : Y) :
    C(↥(sphLoopCollarProd b PUnit), ↥(sphLoopCollarProd b Y)) :=
  ⟨fun a => (⟨(collarFib (Y := Y) b y) ↑a, collarFib_mem (Y := Y) b y ↑a a.2⟩ :
      ↥(sphLoopCollarProd b Y)), by fun_prop⟩

/-! ## Degree-zero evaluation facts -/

/-- The pullback along a constant map of a class in `H⁰` is a scalar multiple of the unit. -/
theorem CohMap_h0Const {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (y : Y) (hf : ∀ x, f x = y) (u : Work.Thom.Coh ℤ 0 Y) :
    (Work.Thom.CohMap f ℤ 0).hom u
      = (Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of Y))
          (TopCat.toSSetObj₀Equiv.symm y) u)
        • (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of X))) := by
  refine h0Ev_ext' (fun t => ?_)
  show Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of X)) t
      ((Work.Thom.CohMap f ℤ 0).hom u) = _
  rw [h0Ev_CohMap']
  rw [show (TopCat.toSSet.map (TopCat.ofHom f)).app (Opposite.op (SimplexCategory.mk 0)) t
      = TopCat.toSSetObj₀Equiv.symm y from by
    apply TopCat.toSSetObj₀Equiv.injective
    rw [toSSetObj₀Equiv_map', Equiv.apply_symm_apply]
    exact hf _]
  simp only [map_zsmul, h0Ev_oneH', smul_eq_mul, mul_one]

/-- If every evaluation of `u ∈ H⁰(Y)` is `±1` then `u ⌣ u = 1`. -/
theorem cupH'_self_eq_one (Y : Type) [TopologicalSpace Y] (u : Work.Thom.Coh ℤ 0 Y)
    (h : ∀ s : (TopCat.toSSet.obj (TopCat.of Y)).obj (Opposite.op (SimplexCategory.mk 0)),
      Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of Y)) s u = 1 ∨
        Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of Y)) s u = -1) :
    Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of Y)) 0 0 u u
      = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of Y)) := by
  refine sub_eq_zero.mp (h0Ev_eq_zero' _ (fun s => ?_))
  rw [map_sub, h0Ev_cup', h0Ev_oneH', sub_eq_zero]
  rcases h s with hs | hs <;> rw [hs] <;> norm_num

/-! ## The unit transfer -/

/-- **The unit transfer**: if `τ₀` is a Thom class of the collar pair and `u ∈ H⁰(Y)` satisfies
`u ⌣ u = 1`, then `π^*(u) ⌣ τ₀` is again a Thom class. -/
theorem collarThom_of_unit (b : ℕ) (hb : 2 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ₀ : Work.Thom.RelCoh ℤ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ₀ : CollarThom (Y := Y) b τ₀)
    (u : Work.Thom.Coh ℤ 0 Y)
    (hu : Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of Y)) 0 0 u u
      = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of Y))) :
    CollarThom (Y := Y) b
      ((relDegEquiv (sphLoopCollarProd b Y) (Nat.zero_add b))
        ((Work.Thom.mixedCupC ℤ (sphLoopCollarProd b Y) 0 b)
          ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℤ 0).hom u) τ₀)) := by
  let τ : Work.Thom.RelCoh ℤ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y) :=
    (relDegEquiv (sphLoopCollarProd b Y) (Nat.zero_add b))
      ((Work.Thom.mixedCupC ℤ (sphLoopCollarProd b Y) 0 b)
        ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℤ 0).hom u) τ₀)
  have hgoal : CollarThom (Y := Y) b τ := by
    intro m
    have hΨ : ∀ y : Work.Thom.Coh ℤ m Y,
        Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of Y)) m 0
          (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of Y)) m 0 y u) u = y := by
      intro y
      have h := Work.Cohomology.cupH'_assoc (R := ℤ)
        (X := TopCat.toSSet.obj (TopCat.of Y)) m 0 0 y u u
      rw [hu, Work.Cohomology.cupH'_one_right] at h
      simpa using h
    have hΨbij : Function.Bijective (fun y : Work.Thom.Coh ℤ m Y =>
        Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of Y)) m 0 y u) := by
      refine ⟨fun x y hxy => ?_, fun y => ⟨_, hΨ y⟩⟩
      have h1 : Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of Y)) m 0
            (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of Y)) m 0 x u) u
          = Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of Y)) m 0
            (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of Y)) m 0 y u) u :=
        congrArg (fun w => Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of Y)) m 0 w u) hxy
      rw [hΨ x, hΨ y] at h1
      exact h1
    have hpt : ∀ x : Work.Thom.Coh ℤ m Y,
        (collarPhi (Y := Y) b τ m) x
          = (relDegEquiv (sphLoopCollarProd b Y) (congrArg (fun t => m + t) (Nat.zero_add b)))
              ((relDegEquiv (sphLoopCollarProd b Y) (Nat.add_assoc m 0 b))
                ((collarPhi (Y := Y) b τ₀ m)
                  (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of Y)) m 0 x u))) := by
      intro x
      show (Work.Thom.mixedCupC ℤ (sphLoopCollarProd b Y) m b)
          ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℤ m).hom x)
          ((relDegEquiv (sphLoopCollarProd b Y) (Nat.zero_add b))
            ((Work.Thom.mixedCupC ℤ (sphLoopCollarProd b Y) 0 b)
              ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℤ 0).hom u) τ₀)) = _
      rw [mixedCupC_relDegEquiv_right (sphLoopCollarProd b Y) m (Nat.zero_add b)
        ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℤ m).hom x)
        ((Work.Thom.mixedCupC ℤ (sphLoopCollarProd b Y) 0 b)
          ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℤ 0).hom u) τ₀)]
      rw [show (Work.Thom.mixedCupC ℤ (sphLoopCollarProd b Y) m (0 + b))
          ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℤ m).hom x)
          ((Work.Thom.mixedCupC ℤ (sphLoopCollarProd b Y) 0 b)
            ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℤ 0).hom u) τ₀)
        = (Nat.add_assoc m 0 b) ▸ ((Work.Thom.mixedCupC ℤ (sphLoopCollarProd b Y) m b)
            ((Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of (↥(sphLoopBig b) × Y))) m 0)
              ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℤ m).hom x)
              ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℤ 0).hom u)) τ₀) from
        mixedCupC_assoc_zero (sphLoopCollarProd b Y) m b
          ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℤ m).hom x)
          ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℤ 0).hom u) τ₀]
      rw [show (Work.Cohomology.cupH' ℤ
            (TopCat.toSSet.obj (TopCat.of (↥(sphLoopBig b) × Y))) m 0)
            ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℤ m).hom x)
            ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℤ 0).hom u)
          = (Work.Thom.CohMap (collarProjY (Y := Y) b) ℤ m).hom
              (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of Y)) m 0 x u) from
        (Work.Cohomology.cupNaturalH ℤ (TopCat.ofHom (collarProjY (Y := Y) b)) m 0 x u).symm]
      rfl
    have hF : Function.Bijective (fun z : Work.Thom.RelCoh ℤ (m + b)
          (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y) =>
        (relDegEquiv (sphLoopCollarProd b Y) (congrArg (fun t => m + t) (Nat.zero_add b)))
          ((relDegEquiv (sphLoopCollarProd b Y) (Nat.add_assoc m 0 b)) z)) :=
      (relDegEquiv (sphLoopCollarProd b Y)
        (congrArg (fun t => m + t) (Nat.zero_add b))).bijective.comp
        (relDegEquiv (sphLoopCollarProd b Y) (Nat.add_assoc m 0 b)).bijective
    have hfun : ⇑(collarPhi (Y := Y) b τ m)
        = (fun z : Work.Thom.RelCoh ℤ (m + b) (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y) =>
            (relDegEquiv (sphLoopCollarProd b Y) (congrArg (fun t => m + t) (Nat.zero_add b)))
              ((relDegEquiv (sphLoopCollarProd b Y) (Nat.add_assoc m 0 b)) z))
          ∘ (⇑(collarPhi (Y := Y) b τ₀ m)) ∘ (fun y : Work.Thom.Coh ℤ m Y =>
              Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of Y)) m 0 y u) := by
      funext x; exact hpt x
    rw [hfun]
    simpa only [Function.comp_assoc] using hF.comp ((hτ₀ m).comp hΨbij)
  exact hgoal

/-! ## The crux: `δ` of the suspension class is a Thom class -/

/-- **The crux**: for a class `gen ∈ H^{b-1}(C)` of the collar over a point whose transgression is a
generator of `H^b(Q,C)`, the transgression of the pullback of `gen` along the collar projection is a
Thom class of the collar over `Y`. -/
theorem collarThom_delta_of (b : ℕ) (hb : 2 ≤ b) (Y : Type) [TopologicalSpace Y] (y₀ : Y)
    (Φ₁ : Work.Thom.RelCoh ℤ b (↥(sphLoopBig b) × PUnit) (sphLoopCollarProd b PUnit) ≃ₗ[ℤ] ℤ)
    (gen : Work.Thom.Coh ℤ (b - 1) (↥(sphLoopCollarProd b PUnit)))
    (hgen : (Work.Cohomology.pairδ ℤ (TopCat.of (↥(sphLoopBig b) × PUnit))
        (sphLoopCollarProd b PUnit) (b - 1)).hom gen
      = (relDegEquiv (sphLoopCollarProd b PUnit) (by omega : b - 1 + 1 = b)).symm (Φ₁.symm 1)) :
    ∃ τ : Work.Thom.RelCoh ℤ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y),
      CollarThom (Y := Y) b τ ∧
      CollarTransgresses (Y := Y) b (by omega)
        ((Work.Thom.CohMap (collarDropSub (Y := Y) b) ℤ (b - 1)).hom gen) τ := by
  classical
  obtain ⟨τ₀, hτ₀⟩ := exists_collarThom b (by omega) Y
  have hb1 : b - 1 + 1 = b := by omega
  let s : Work.Thom.Coh ℤ (b - 1) (↥(sphLoopCollarProd b Y)) :=
    (Work.Thom.CohMap (collarDropSub (Y := Y) b) ℤ (b - 1)).hom gen
  let d : Work.Thom.RelCoh ℤ (b - 1 + 1) (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y) :=
    (Work.Cohomology.pairδ ℤ (TopCat.of (↥(sphLoopBig b) × Y))
      (sphLoopCollarProd b Y) (b - 1)).hom s
  let τ : Work.Thom.RelCoh ℤ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y) :=
    (relDegEquiv (sphLoopCollarProd b Y) hb1) d
  refine ⟨τ, ?_, ?_⟩
  · -- ### `CollarThom τ`
    let Φ₀ : Work.Thom.Coh ℤ 0 Y ≃ₗ[ℤ] Work.Thom.RelCoh ℤ (0 + b)
        (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y) :=
      LinearEquiv.ofBijective (collarPhi (Y := Y) b τ₀ 0) (hτ₀ 0)
    let u : Work.Thom.Coh ℤ 0 Y :=
      Φ₀.symm ((relDegEquiv (sphLoopCollarProd b Y) (Nat.zero_add b)).symm τ)
    have hτu : τ = (relDegEquiv (sphLoopCollarProd b Y) (Nat.zero_add b))
        ((Work.Thom.mixedCupC ℤ (sphLoopCollarProd b Y) 0 b)
          ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℤ 0).hom u) τ₀) := by
      have hu0 : Φ₀ u
          = (relDegEquiv (sphLoopCollarProd b Y) (Nat.zero_add b)).symm τ :=
        LinearEquiv.apply_symm_apply Φ₀ _
      have hu0' : (collarPhi (Y := Y) b τ₀ 0) u
          = (relDegEquiv (sphLoopCollarProd b Y) (Nat.zero_add b)).symm τ := by
        rw [show (collarPhi (Y := Y) b τ₀ 0) u = Φ₀ u from rfl]
        exact hu0
      rw [show (collarPhi (Y := Y) b τ₀ 0) u
          = (Work.Thom.mixedCupC ℤ (sphLoopCollarProd b Y) 0 b)
              ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℤ 0).hom u) τ₀ from rfl] at hu0'
      rw [hu0']
      exact (LinearEquiv.apply_symm_apply _ τ).symm
    -- the fibre restriction of `s` is `gen`
    have hfibs : ∀ y : Y,
        (Work.Thom.CohMap (collarFibSubA b Y y) ℤ (b - 1)).hom s = gen := by
      intro y
      rw [show s = (Work.Thom.CohMap (collarDropSub (Y := Y) b) ℤ (b - 1)).hom gen from rfl]
      rw [show (Work.Thom.CohMap (collarFibSubA b Y y) ℤ (b - 1)).hom
          ((Work.Thom.CohMap (collarDropSub (Y := Y) b) ℤ (b - 1)).hom gen)
          = ((Work.Thom.CohMap (collarFibSubA b Y y) ℤ (b - 1)).hom ∘ₗ
              (Work.Thom.CohMap (collarDropSub (Y := Y) b) ℤ (b - 1)).hom) gen from rfl]
      rw [Work.Thom.CohMap_linear_comp (collarFibSubA b Y y)
        (collarDropSub (Y := Y) b) ℤ (b - 1)]
      rw [show (collarDropSub (Y := Y) b).comp (collarFibSubA b Y y) = ContinuousMap.id _ from by
        rw [show collarFibSubA b Y y = collarFibSub (Y := Y) b y from rfl]
        exact collarDropSub_comp_collarFibSub b y]
      simp
    -- the fibre restriction of `d` is `w`
    have hd : ∀ y : Y,
        (Work.Thom.relCohMap (collarFib (Y := Y) b y) (sphLoopCollarProd b PUnit)
            (sphLoopCollarProd b Y) (collarFib_mem (Y := Y) b y) ℤ (b - 1 + 1)).hom d
          = (relDegEquiv (sphLoopCollarProd b PUnit) hb1).symm (Φ₁.symm 1) := by
      intro y
      have h1 := Work.Thom.pairDeltaNatural (collarFib (Y := Y) b y) (sphLoopCollarProd b PUnit)
        (sphLoopCollarProd b Y) (collarFib_mem (Y := Y) b y) (b - 1) s
      rw [show d = (Work.Cohomology.pairδ ℤ (TopCat.of (↥(sphLoopBig b) × Y))
          (sphLoopCollarProd b Y) (b - 1)).hom s from rfl]
      refine h1.trans ?_
      rw [hfibs y]
      exact hgen
    -- the fibre restriction of `τ` is `gen_b`
    have hfibτ : ∀ y : Y,
        (Work.Thom.relCohMap (collarFib (Y := Y) b y) (sphLoopCollarProd b PUnit)
            (sphLoopCollarProd b Y) (collarFib_mem (Y := Y) b y) ℤ b).hom τ = Φ₁.symm 1 := by
      intro y
      rw [show τ = (relDegEquiv (sphLoopCollarProd b Y) hb1) d from rfl]
      rw [relCohMap_relDegEquiv (sphLoopCollarProd b PUnit) (sphLoopCollarProd b Y)
        (collarFib (Y := Y) b y) (collarFib_mem (Y := Y) b y) hb1 d]
      rw [hd y]
      exact LinearEquiv.apply_symm_apply (relDegEquiv (sphLoopCollarProd b PUnit) hb1) (Φ₁.symm 1)
    -- the pointwise evaluation of `u` is a unit
    have hunit : ∀ y : Y,
        Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of Y))
            (TopCat.toSSetObj₀Equiv.symm y) u = 1 ∨
        Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of Y))
            (TopCat.toSSetObj₀Equiv.symm y) u = -1 := by
      intro y
      let A : Work.Thom.RelCoh ℤ b (↥(sphLoopBig b) × PUnit) (sphLoopCollarProd b PUnit) :=
        (Work.Thom.relCohMap (collarFib (Y := Y) b y) (sphLoopCollarProd b PUnit)
          (sphLoopCollarProd b Y) (collarFib_mem (Y := Y) b y) ℤ b).hom τ₀
      let E : Work.Thom.RelCoh ℤ (0 + b) (↥(sphLoopBig b) × PUnit)
            (sphLoopCollarProd b PUnit) ≃ₗ[ℤ]
          Work.Thom.RelCoh ℤ b (↥(sphLoopBig b) × PUnit) (sphLoopCollarProd b PUnit) :=
        relDegEquiv (sphLoopCollarProd b PUnit) (Nat.zero_add b)
      let lam : ℤ := Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of Y))
        (TopCat.toSSetObj₀Equiv.symm y) u
      have hB : (Work.Thom.relCohMap (collarFib (Y := Y) b y) (sphLoopCollarProd b PUnit)
          (sphLoopCollarProd b Y) (collarFib_mem (Y := Y) b y) ℤ b).hom τ
          = E (lam • (E.symm A)) := by
        rw [hτu]
        have hstep : (Work.Thom.relCohMap (collarFib (Y := Y) b y) (sphLoopCollarProd b PUnit)
            (sphLoopCollarProd b Y) (collarFib_mem (Y := Y) b y) ℤ b).hom
            ((relDegEquiv (sphLoopCollarProd b Y) (Nat.zero_add b))
              ((Work.Thom.mixedCupC ℤ (sphLoopCollarProd b Y) 0 b)
                ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℤ 0).hom u) τ₀))
            = (relDegEquiv (sphLoopCollarProd b PUnit) (Nat.zero_add b))
              ((Work.Thom.relCohMap (collarFib (Y := Y) b y)
                (sphLoopCollarProd b PUnit) (sphLoopCollarProd b Y)
                (collarFib_mem (Y := Y) b y) ℤ (0 + b)).hom
              ((Work.Thom.mixedCupC ℤ (sphLoopCollarProd b Y) 0 b)
                ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℤ 0).hom u) τ₀)) :=
          relCohMap_relDegEquiv (sphLoopCollarProd b PUnit) (sphLoopCollarProd b Y)
            (collarFib (Y := Y) b y) (collarFib_mem (Y := Y) b y) (Nat.zero_add b)
            ((Work.Thom.mixedCupC ℤ (sphLoopCollarProd b Y) 0 b)
              ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℤ 0).hom u) τ₀)
        rw [hstep]
        have hZ : (Work.Thom.relCohMap (collarFib (Y := Y) b y) (sphLoopCollarProd b PUnit)
            (sphLoopCollarProd b Y) (collarFib_mem (Y := Y) b y) ℤ (0 + b)).hom
            ((Work.Thom.mixedCupC ℤ (sphLoopCollarProd b Y) 0 b)
              ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℤ 0).hom u) τ₀)
            = lam • (E.symm A) := by
          rw [Work.Thom.mixedCupC_pairNatural (collarFib (Y := Y) b y) (sphLoopCollarProd b PUnit)
            (sphLoopCollarProd b Y) (collarFib_mem (Y := Y) b y) 0 b
            ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℤ 0).hom u) τ₀]
          rw [show (Work.Thom.CohMap (collarFib (Y := Y) b y) ℤ 0).hom
              ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℤ 0).hom u)
              = (Work.Thom.CohMap (collarFibBase (Y := Y) b y) ℤ 0).hom u from by
            rw [show (Work.Thom.CohMap (collarFib (Y := Y) b y) ℤ 0).hom
                  ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℤ 0).hom u)
                = ((Work.Thom.CohMap (collarFib (Y := Y) b y) ℤ 0).hom ∘ₗ
                    (Work.Thom.CohMap (collarProjY (Y := Y) b) ℤ 0).hom) u from rfl]
            rw [Work.Thom.CohMap_linear_comp (collarFib (Y := Y) b y)
              (collarProjY (Y := Y) b) ℤ 0]
            rw [show (collarProjY (Y := Y) b).comp (collarFib (Y := Y) b y)
                = collarFibBase (Y := Y) b y from collarProjY_comp_collarFib b y]]
          rw [CohMap_h0Const (collarFibBase (Y := Y) b y) y (fun _ => rfl) u]
          simp only [lam]
          rw [mixedCupC_smul_left]
          rw [show (Work.Thom.mixedCupC ℤ (sphLoopCollarProd b PUnit) 0 b)
              (Work.Cohomology.oneH ℤ
                (TopCat.toSSet.obj (TopCat.of (↥(sphLoopBig b) × PUnit))))
              ((Work.Thom.relCohMap (collarFib (Y := Y) b y) (sphLoopCollarProd b PUnit)
                (sphLoopCollarProd b Y) (collarFib_mem (Y := Y) b y) ℤ b).hom τ₀)
              = E.symm A from by
            rw [Work.Thom.mixedCupC_oneH_zero]
            rfl]
        rw [hZ]
      have hcomb : Φ₁.symm 1 = E (lam • (E.symm A)) := (hfibτ y).symm.trans hB
      have hE2 : E.symm (Φ₁.symm 1) = lam • (E.symm A) := by
        rw [hcomb]
        exact LinearEquiv.symm_apply_apply E _
      have hkey := congrArg (fun z => Φ₁ (E z)) hE2
      rw [LinearEquiv.apply_symm_apply] at hkey
      have h2 : E (lam • (E.symm A)) = lam • A := by
        rw [map_zsmul, LinearEquiv.apply_symm_apply]
      rw [h2] at hkey
      rw [map_zsmul] at hkey
      rw [LinearEquiv.apply_symm_apply] at hkey
      rw [smul_eq_mul] at hkey
      exact Int.eq_one_or_neg_one_of_mul_eq_one hkey.symm
    have hu : Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of Y)) 0 0 u u
        = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of Y)) :=
      cupH'_self_eq_one Y u (fun s => by
        have h := hunit (TopCat.toSSetObj₀Equiv s)
        rwa [Equiv.symm_apply_apply] at h)
    rw [hτu]
    exact collarThom_of_unit b hb Y τ₀ hτ₀ u hu
  · -- ### `CollarTransgresses s τ`
    unfold CollarTransgresses
    exact (eqToHom_symm_relDegEquiv (sphLoopCollarProd b Y) hb1 d).symm

end

end Work.StemsB
