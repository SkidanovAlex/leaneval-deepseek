import Mathlib
import Submission.Work.Thom.ModelThomDefs
import Submission.Work.Thom.ModelThomStep
import Submission.Work.Thom.TrivProductHomeo
import Submission.Work.Thom.LineThomClass
import Submission.Work.Thom.bijective_relCohMap_spherePunctured

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
set_option linter.style.haveILetI false

/-!
# The base case of the model induction

The rank-one model pair `(B × ℝ¹, B × S⁰)` carries a Thom class: it is the Thom class of the
trivial line bundle (`Work.Thom.nonempty_thomClass_trivial_line`), transported along the pair
homeomorphisms `(E,E∖0) ≅ (B × ℝ, B × ℝ^*)` (`Work.Thom.trivProductHomeo`), `(B × ℝ) ≅ (B × ℝ¹)`
(`Work.Thom.eucOneHomeo`) and `(B × ℝ¹, B × ℝ^*) ≅ (B × ℝ¹, B × S⁰)`
(`Work.Thom.bijective_relCohMap_spherePunctured`).  At each step `Work.Thom.cupMap_transfer_bwd`
controls the cup map.

Together with `Work.Thom.modelThom_step` this gives `Work.Thom.modelThom_all`: every rank `n ≥ 1`
carries a model Thom class.
-/

namespace Work.Thom

open CategoryTheory
open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B]

/-- The bracket condition for the sphere/punctured bridge at any rank. -/
theorem sph_subset_punctured (n : ℕ) :
    ∀ p ∈ {p : B × EuclideanSpace ℝ (Fin n) | p.2 ∈ mSph n},
      p ∈ {p : B × EuclideanSpace ℝ (Fin n) | p.2 ≠ 0} := by
  intro p hp
  intro h0
  have hp' : ‖p.2‖ = 1 := hp
  rw [h0, norm_zero] at hp'
  exact zero_ne_one hp'

/-- **The base case of the model induction**: the rank-one model Thom class. -/
theorem modelThom_base (B : Type) [TopologicalSpace B] (ι : Type) [Inhabited ι] :
    ModelThom B 1 := by
  obtain ⟨T⟩ := nonempty_thomClass_trivial_line (B := B) (ι₀ := ι)
  -- step 1: `(E, E∖0) → (B × ℝ, B × ℝ^*)`
  have hf₁ : ∀ p ∈ (zeroComplement (RealBundle.trivial B ℝ ι)),
      (trivProductHomeo B ℝ ι : C((RealBundle.trivial B ℝ ι).TotalSpace, B × ℝ)) p
        ∈ {q : B × ℝ | q.2 ≠ 0} :=
    fun p hp => (trivProductHomeo_zeroComplement B ℝ ι p).mp hp
  have hfb₁ : ∀ m, Function.Bijective (relCohMap
      (trivProductHomeo B ℝ ι : C((RealBundle.trivial B ℝ ι).TotalSpace, B × ℝ))
      (zeroComplement (RealBundle.trivial B ℝ ι)) {q : B × ℝ | q.2 ≠ 0} hf₁ ℤ m).hom :=
    fun m => bijective_relCohMap_of_homeomorph
      (zeroComplement (RealBundle.trivial B ℝ ι)) {q : B × ℝ | q.2 ≠ 0}
      (trivProductHomeo B ℝ ι) (fun p => trivProductHomeo_zeroComplement B ℝ ι p) ℤ m
  have hpi₁ : (⟨Prod.fst, continuous_fst⟩ : C(B × ℝ, B)).comp
      ((trivProductHomeo B ℝ ι : C((RealBundle.trivial B ℝ ι).TotalSpace, B × ℝ)))
      = bundleProj (RealBundle.trivial B ℝ ι) := by
    apply ContinuousMap.ext
    intro p
    exact congrArg Prod.fst (trivProductHomeo_apply B ℝ ι p)
  obtain ⟨τ₁, _, hτ₁⟩ :=
    cupMap_transfer_bwd
      ((trivProductHomeo B ℝ ι : C((RealBundle.trivial B ℝ ι).TotalSpace, B × ℝ)))
      {q : B × ℝ | q.2 ≠ 0}
      (zeroComplement (RealBundle.trivial B ℝ ι))
      hf₁ hfb₁
      ⟨Prod.fst, continuous_fst⟩ (bundleProj (RealBundle.trivial B ℝ ι))
      hpi₁ 1 T.τ (fun k => T.isThom k)
  -- step 2: `(B × ℝ) → (B × ℝ¹)`
  have hf₂ : ∀ q ∈ {q : B × ℝ | q.2 ≠ 0},
      ((Homeomorph.prodCongr (Homeomorph.refl B) eucOneHomeo.symm) :
        C(B × ℝ, B × EuclideanSpace ℝ (Fin 1))) q
        ∈ {q : B × EuclideanSpace ℝ (Fin 1) | q.2 ≠ 0} := by
    intro q hq
    simp only [Homeomorph.coe_prodCongr, Prod.map_apply, Homeomorph.refl_apply,
      Set.mem_setOf_eq]
    exact fun h => hq (eucOneHomeo_symm_eq_zero.mp h)
  have hfb₂ : ∀ m, Function.Bijective (relCohMap
      ((Homeomorph.prodCongr (Homeomorph.refl B) eucOneHomeo.symm) :
        C(B × ℝ, B × EuclideanSpace ℝ (Fin 1)))
      {q : B × ℝ | q.2 ≠ 0} {q : B × EuclideanSpace ℝ (Fin 1) | q.2 ≠ 0} hf₂ ℤ m).hom :=
    fun m => bijective_relCohMap_of_homeomorph
        {q : B × ℝ | q.2 ≠ 0} {q : B × EuclideanSpace ℝ (Fin 1) | q.2 ≠ 0}
        (Homeomorph.prodCongr (Homeomorph.refl B) eucOneHomeo.symm)
        (fun q => by
          simp only [Homeomorph.coe_prodCongr, Prod.map_apply, Homeomorph.refl_apply,
            Set.mem_setOf_eq]
          exact ⟨fun h h0 => h (eucOneHomeo_symm_eq_zero.mp h0),
            fun h h0 => h (eucOneHomeo_symm_eq_zero.mpr h0)⟩)
        ℤ m
  have hpi₂ : (⟨Prod.fst, continuous_fst⟩ : C(B × EuclideanSpace ℝ (Fin 1), B)).comp
      ((Homeomorph.prodCongr (Homeomorph.refl B) eucOneHomeo.symm) :
        C(B × ℝ, B × EuclideanSpace ℝ (Fin 1)))
      = ⟨Prod.fst, continuous_fst⟩ := by
    apply ContinuousMap.ext
    intro q
    simp only [ContinuousMap.comp_apply, Homeomorph.coe_prodCongr, Prod.map_apply,
      Homeomorph.refl_apply]
    rfl
  obtain ⟨τ₂, _, hτ₂⟩ :=
    cupMap_transfer_bwd
      ((Homeomorph.prodCongr (Homeomorph.refl B) eucOneHomeo.symm) :
        C(B × ℝ, B × EuclideanSpace ℝ (Fin 1)))
      {q : B × EuclideanSpace ℝ (Fin 1) | q.2 ≠ 0}
      {q : B × ℝ | q.2 ≠ 0}
      hf₂ hfb₂
      ⟨Prod.fst, continuous_fst⟩ ⟨Prod.fst, continuous_fst⟩ hpi₂
      1 τ₁ hτ₁
  -- step 3: `(B × ℝ¹, B × ℝ^*) → (B × ℝ¹, B × S⁰)`
  have hf₃ : ∀ q ∈ {p : B × EuclideanSpace ℝ (Fin 1) | p.2 ∈ mSph 1},
      (ContinuousMap.id (B × EuclideanSpace ℝ (Fin 1))) q
        ∈ {q : B × EuclideanSpace ℝ (Fin 1) | q.2 ≠ 0} :=
    sph_subset_punctured 1
  have hτ₃ := cupMap_transfer_fwd (ContinuousMap.id (B × EuclideanSpace ℝ (Fin 1)))
      {q : B × EuclideanSpace ℝ (Fin 1) | q.2 ≠ 0}
      {p : B × EuclideanSpace ℝ (Fin 1) | p.2 ∈ mSph 1}
      hf₃
      (bijective_relCohMap_spherePunctured B 1)
      (projFst B 1) (projFst B 1) (by ext q; rfl)
      1 τ₂ hτ₂
  exact ⟨_, hτ₃⟩

/-- **Every positive rank carries a model Thom class.** -/
theorem modelThom_all (B : Type) [TopologicalSpace B] (ι : Type) [Inhabited ι] {n : ℕ}
    (hn : 1 ≤ n) : ModelThom B n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  induction k with
  | zero => exact modelThom_base B ι
  | succ j ih => exact modelThom_step B (j + 1) (by omega) (ih (by omega))

end

end Work.Thom
