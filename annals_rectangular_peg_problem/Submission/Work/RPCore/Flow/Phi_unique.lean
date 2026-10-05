import Mathlib
import Submission.Work.RPCore.Flow.HamFlow

namespace Work.RPCore.Flow

/-- Uniqueness on `[-1,2]`: any global solution `Φ'` of the genuine Hamiltonian ODE of `Hh.H`
with `Φ' 0 = id` agrees with the clamped two-time flow `Phi Hh 0` on the clamp interval `[-1,2]`.

The point is that `(s, Φ' s x)` and the clamped flow `s ↦ clampFlow Hh s (0,x)` are both
solutions on `[-1,2]` of the *same autonomous* vector field `clampedField Hh` (they agree there
because the clamp is the identity on `[-1,2]`), so Mathlib's ODE uniqueness applies. -/
theorem Phi_unique (Hh : Work.RPV.CptPerHam) (Φ' : ℝ → Work.RPV.PS → Work.RPV.PS)
    (hΦ' : ∀ x t, HasDerivAt (fun s => Φ' s x) (Work.RPV.hamVF (Hh.H t) (Φ' t x)) t)
    (h0' : ∀ x, Φ' 0 x = x) {b : ℝ} (hb : b ∈ Set.Icc (-1 : ℝ) 2) (x : Work.RPV.PS) :
    Φ' b x = Work.RPCore.Phi Hh 0 b x := by
  let γ₁ : ℝ → ℝ × Work.RPV.PS := fun s => (s, Φ' s x)
  let γ₂ : ℝ → ℝ × Work.RPV.PS := fun s => Work.RPCore.clampFlow Hh s (0, x)
  -- `γ₁` solves the clamped field on `Ioo (-1) 2`, where the clamp is the identity.
  have hf' : ∀ t ∈ Set.Ioo (-1 : ℝ) 2, HasDerivAt γ₁ (Work.RPCore.clampedField Hh (γ₁ t)) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (-1 : ℝ) 2 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hder : Work.RPCore.clampedField Hh (γ₁ t)
        = (1, Work.RPV.hamVF (Hh.H t) (Φ' t x)) := by
      show Work.RPCore.autoVF (Work.RPCore.clampHam Hh) (t, Φ' t x)
        = (1, Work.RPV.hamVF (Hh.H t) (Φ' t x))
      rw [Work.RPCore.autoVF_apply, Work.RPCore.clampHam_self Hh ht']
    rw [hder]
    exact (hasDerivAt_id t).prodMk (hΦ' x t)
  have hcont1 : Continuous γ₁ := by
    have h2 : Continuous (fun s : ℝ => Φ' s x) :=
      continuous_iff_continuousAt.mpr (fun t => (hΦ' x t).continuousAt)
    exact continuous_id.prodMk h2
  have hcont2 : Continuous γ₂ := (Work.RPCore.clampFlow_curve Hh (0, x)).continuous
  have heq0 : γ₁ 0 = γ₂ 0 := by
    show (0, Φ' 0 x) = Work.RPCore.clampFlow Hh 0 (0, x)
    rw [h0' x, Work.RPCore.clampFlow_zero]
  have hEqOn : Set.EqOn γ₁ γ₂ (Set.Icc (-1 : ℝ) 2) :=
    ODE_solution_unique_of_mem_Icc
      (v := fun _ : ℝ => Work.RPCore.clampedField Hh)
      (s := fun _ : ℝ => Set.univ)
      (K := (Work.RPCore.clampedData Hh).K.toNNReal)
      (a := (-1 : ℝ)) (b := (2 : ℝ)) (t₀ := (0 : ℝ))
      (fun t _ => (Work.RPCore.clampedField_lipschitz Hh).lipschitzOnWith)
      ⟨by norm_num, by norm_num⟩
      hcont1.continuousOn hf' (fun t _ => Set.mem_univ _)
      hcont2.continuousOn (fun t _ => (Work.RPCore.clampFlow_curve Hh (0, x)) t)
        (fun t _ => Set.mem_univ _) heq0
  have h := congrArg Prod.snd (hEqOn hb)
  show Φ' b x = (Work.RPCore.clampFlow Hh (b - 0) (0, x)).2
  rw [sub_zero]
  exact h

end Work.RPCore.Flow
