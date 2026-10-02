/-
# Elementary API of the Böttcher chapter

Small facts that follow directly from the definitions in `Work.Bottcher.Defs`:
the Böttcher coordinate vanishes exactly at `0`; the rays/equipotentials are
subsets of the respective exteriors; the angle maps are periodic.
-/
import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Green.green_comm
import Submission.Work.Bottcher.Core.bottcher_comm_pMap

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Function
open scoped Topology ComplexConjugate

namespace Work.Bottcher

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## The Böttcher coordinate vanishes only at `0` -/

theorem bottcher_ne_zero (c : ℂ) {z : ℂ} (hz : z ≠ 0) : bottcher c z ≠ 0 :=
  mul_ne_zero hz (Complex.exp_ne_zero _)

theorem bottcher_eq_zero_iff (c z : ℂ) : bottcher c z = 0 ↔ z = 0 := by
  constructor
  · intro h
    by_contra hz
    exact bottcher_ne_zero c hz h
  · rintro rfl
    simp [bottcher]

/-- `0` is never in `CritDomain c` (the defining inequality is strict). -/
theorem zero_notMem_CritDomain (c : ℂ) : (0 : ℂ) ∉ CritDomain c :=
  fun h => lt_irrefl (green c 0) h

/-! ## The unit circle -/

theorem norm_rayDirection (θ : ℝ) : ‖rayDirection θ‖ = 1 := by
  simp [rayDirection, Complex.norm_exp]

theorem rayDirection_ne_zero (θ : ℝ) : rayDirection θ ≠ 0 := by
  intro h
  have h1 := norm_rayDirection θ
  rw [h, norm_zero] at h1
  exact one_ne_zero h1.symm

theorem rayDirection_add_int (θ : ℝ) (m : ℤ) : rayDirection (θ + m) = rayDirection θ := by
  have h1 : Complex.exp ((m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
    rw [Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]
  have h : ((2 * Real.pi * (θ + m) : ℝ) : ℂ) * Complex.I =
      ((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I + (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  simp only [rayDirection, h, Complex.exp_add, h1, mul_one]

/-! ## The external angle -/

theorem extAngle_mem_Ico (c : ℂ) : extAngle c ∈ Set.Ico (0 : ℝ) 1 := by
  have := toIcoMod_mem_Ico (p := (1 : ℝ)) one_pos (0 : ℝ)
    (Complex.arg (Phi c) / (2 * Real.pi))
  simpa [extAngle] using this

/-! ## Rays and equipotentials -/

theorem dynamicRay_subset_CritDomain (c : ℂ) (θ : ℝ) :
    dynamicRay c θ ⊆ CritDomain c := fun _ h => h.1

theorem mem_dynamicRay {c : ℂ} {θ : ℝ} {z : ℂ} :
    z ∈ dynamicRay c θ ↔
      z ∈ CritDomain c ∧ ∃ r : ℝ, 1 < r ∧ bottcher c z = (r : ℂ) * rayDirection θ := Iff.rfl

theorem paramRay_subset (θ : ℝ) : paramRay θ ⊆ {c : ℂ | c ∉ Mandelbar} := fun _ h => h.1

theorem mem_paramRay {c : ℂ} {θ : ℝ} :
    c ∈ paramRay θ ↔
      c ∉ Mandelbar ∧ ∃ r : ℝ, 1 < r ∧ Phi c = (r : ℂ) * rayDirection θ := Iff.rfl

theorem paramEquipotential_subset (R : ℝ) :
    paramEquipotential R ⊆ {c : ℂ | c ∉ Mandelbar} := fun _ h => h.1

theorem paramEquipotentialArc_subset (R β₁ β₂ : ℝ) :
    paramEquipotentialArc R β₁ β₂ ⊆ {c : ℂ | c ∉ Mandelbar} := fun _ h => h.1

theorem mem_paramEquipotentialArc {R β₁ β₂ : ℝ} {c : ℂ} :
    c ∈ paramEquipotentialArc R β₁ β₂ ↔
      c ∉ Mandelbar ∧ ‖Phi c‖ = R ∧ extAngle c ∈ Set.Icc β₁ β₂ := Iff.rfl

theorem dynamicEquipotential_eq_level (c : ℂ) (lam : ℝ) :
    dynamicEquipotential c lam = {z : ℂ | green c z = lam} := rfl

/-- A point of modulus `R > 1` on the ray of angle `θ` is on `dynamicRay c θ` whenever
its `bottcher` value is (i.e. the `r > 1` in the definition is the modulus). -/
theorem mem_dynamicRay_iff_norm {c : ℂ} {θ : ℝ} {z : ℂ} (hz : z ∈ CritDomain c) :
    z ∈ dynamicRay c θ ↔ ∃ r : ℝ, 1 < r ∧ bottcher c z = (r : ℂ) * rayDirection θ :=
  ⟨fun h => h.2, fun h => ⟨hz, h⟩⟩

end Work.Bottcher
