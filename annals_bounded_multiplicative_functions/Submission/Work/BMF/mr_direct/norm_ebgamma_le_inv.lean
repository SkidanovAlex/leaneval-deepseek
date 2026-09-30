import Mathlib
import Submission.Work.BMF.mr_direct.ebound_defs
import Submission.Work.BMF.mr_direct.buchstab_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

/-- Each coefficient `ebγ b c P Q i = c i.1 · b i.2 · (ω(i.2;P,Q)+1)^{-1}` of the merged
range-extension error is bounded by `(ω(i.2;P,Q)+1)^{-1}`: take norms and use
`‖c i.1‖ ≤ 1`, `‖b i.2‖ ≤ 1` together with `‖(N : ℂ)^{-1}‖ = (N : ℝ)^{-1}`. -/
theorem norm_ebgamma_le_inv (b c : ℕ → ℂ) (P Q : ℝ) (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (i : Σ _ : ℕ, ℕ) :
    ‖Work.BMF.mr_direct.ebγ b c P Q i‖ ≤
      (((Work.BMF.mrDirect.omegaCount P Q i.2 : ℕ) + 1 : ℕ) : ℝ)⁻¹ := by
  rw [Work.BMF.mr_direct.ebγ, norm_mul, norm_mul]
  have hnorm : ‖(((Work.BMF.mrDirect.omegaCount P Q i.2 : ℕ) + 1 : ℕ) : ℂ)⁻¹‖
      = (((Work.BMF.mrDirect.omegaCount P Q i.2 : ℕ) + 1 : ℕ) : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_natCast]
  rw [hnorm]
  have hNpos : (0 : ℝ) < (((Work.BMF.mrDirect.omegaCount P Q i.2 : ℕ) + 1 : ℕ) : ℝ) := by
    have : (0 : ℕ) < (Work.BMF.mrDirect.omegaCount P Q i.2 : ℕ) + 1 := Nat.succ_pos _
    exact_mod_cast this
  have hnn : (0 : ℝ) ≤ (((Work.BMF.mrDirect.omegaCount P Q i.2 : ℕ) + 1 : ℕ) : ℝ)⁻¹ :=
    (inv_pos.mpr hNpos).le
  have hprod : ‖c i.1‖ * ‖b i.2‖ ≤ 1 := by
    have h := mul_le_mul (hc i.1) (hb i.2) (norm_nonneg _) zero_le_one
    simpa using h
  calc ‖c i.1‖ * ‖b i.2‖ * (((Work.BMF.mrDirect.omegaCount P Q i.2 : ℕ) + 1 : ℕ) : ℝ)⁻¹
      ≤ 1 * (((Work.BMF.mrDirect.omegaCount P Q i.2 : ℕ) + 1 : ℕ) : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right hprod hnn
    _ = (((Work.BMF.mrDirect.omegaCount P Q i.2 : ℕ) + 1 : ℕ) : ℝ)⁻¹ := one_mul _

end Work.BMF.mr_direct
