import Mathlib
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_FarRepel_dhBasic
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_FarRepel_dhKey

open DirichletCharacter Complex Filter
open scoped Classical BigOperators Topology

noncomputable section

namespace Work.LinnikAreas.FarRepel

/-! ## The target: the differentiated explicit formula in inequality form -/

/-- Differentiated explicit formula, inequality form (Kadiri–Ng–Wong arXiv:1902.08640
(2.5)–(2.6)), quadratic-field setting `ζ_K = ζ · L(·,χ)` with `χ` a *real* primitive character.
Hypotheses `χ ^ 2 = 1` and `5 ≤ c` are required (real `χ` gives `1 + χ(p) ≥ 0`, so the
Euler-product side of the differentiated explicit formula is `≥ 0`; complex `χ` makes the
statement false).  `mult_u` is the multiplicity of `u` as a non-trivial zero of `ζ_K`: its order
as a zero of the completed Riemann zeta function plus `Work.LinnikContract.zeroMult χ u`.

Proof: differentiate `-ζ_K'/ζ_K(s) = 1/(s-1) - Σ_ω (1/(s-ω) + 1/ω) + (Γ-terms)` `2j-1` times
(Lagarias–Montgomery–Odlyzko p. 289), evaluate at `s = c` and `s = c + iγ'`; the arithmetic side
`(1/(2j-1)!)Σ_p Σ_m (log p)(log p^m)^{2j-1}p^{-mc}(1 + Re(p^m)^{-iγ'})` is `≥ 0` termwise; trivial
zeros contribute `≥ 0`; and `|1/(c+it-1)^{2j} - 1/(c+it-β₁)^{2j}| ≤ 2j(1-β₁)/(c-1)^{2j+1}` for
`t = 0, γ'`. -/
theorem dhDiffInequality :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
      (hprim : χ.IsPrimitive) (hχ2 : χ ^ 2 = 1) (j : ℕ) (hj : 1 ≤ j) (c γ' : ℝ) (hc : 5 ≤ c)
      {β₁ : ℝ} (hβ₁ : β₁ < 1)
      (hz₁ : DirichletCharacter.completedLFunction χ (β₁ : ℂ) = 0),
      Summable (fun u : ℂ => (((analyticOrderNatAt completedRiemannZeta u : ℕ) : ℝ)
              + (Work.LinnikContract.zeroMult χ u : ℝ)) *
            ((1 / ((c : ℂ) - u) ^ (2 * j)).re
              + (1 / ((c : ℂ) + Complex.I * (γ' : ℂ) - u) ^ (2 * j)).re)) ∧
      4 * (j : ℝ) * (1 - β₁) / (c - 1) ^ (2 * j + 1) ≥
        (∑' u : ℂ, ((analyticOrderNatAt completedRiemannZeta u : ℝ)
              + (Work.LinnikContract.zeroMult χ u : ℝ)) *
            ((1 / ((c : ℂ) - u) ^ (2 * j)).re
              + (1 / ((c : ℂ) + Complex.I * (γ' : ℂ) - u) ^ (2 * j)).re))
          - ((analyticOrderNatAt completedRiemannZeta (β₁ : ℂ) : ℝ)
              + (Work.LinnikContract.zeroMult χ (β₁ : ℂ) : ℝ))
            * ((1 / ((c : ℂ) - (β₁ : ℂ)) ^ (2 * j)).re
                + (1 / ((c : ℂ) + Complex.I * (γ' : ℂ) - (β₁ : ℂ)) ^ (2 * j)).re) := by
  refine ⟨0, ?_⟩
  intro q _hq _inst χ hχ hprim hχ2 j hj c γ' hc β₁ hβ₁ hz₁
  have hc1 : (1 : ℝ) < c := by linarith
  rcases χ.even_or_odd with hev | hod
  · obtain ⟨hsumm, hkey⟩ := dhKey (c := c) (γ' := γ') χ hχ hprim hχ2 j hj 0 (fun _ => rfl)
      (fun ho => absurd (hev.symm.trans ho) (by norm_num)) hc1
    exact ⟨by simpa only [multZ, Wt, Nat.cast_add, one_div_pow] using hsumm,
      by simpa only [multZ, Wt, Nat.cast_add, one_div_pow] using
        final_step χ hχ hprim hc hβ₁ hz₁ hsumm hkey⟩
  · obtain ⟨hsumm, hkey⟩ := dhKey (c := c) (γ' := γ') χ hχ hprim hχ2 j hj 1
      (fun he => absurd (he.symm.trans hod) (by norm_num)) (fun _ => rfl) hc1
    exact ⟨by simpa only [multZ, Wt, Nat.cast_add, one_div_pow] using hsumm,
      by simpa only [multZ, Wt, Nat.cast_add, one_div_pow] using
        final_step χ hχ hprim hc hβ₁ hz₁ hsumm hkey⟩

end Work.LinnikAreas.FarRepel
