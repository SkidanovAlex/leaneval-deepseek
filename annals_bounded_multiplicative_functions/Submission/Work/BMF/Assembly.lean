import Mathlib
import ChallengeDeps
import Submission.Work.BMF.Defs
import Submission.Work.BMF.M_le_of_pretends
import Submission.Work.BMF.weyl_inverse
import Submission.Work.BMF.build_quadruples
import Submission.Work.BMF.prime_tuple_count
import Submission.Work.BMF.adi_cycles
import Submission.Work.BMF.solve_adi
import Submission.Work.BMF.mixing_count
import Submission.Work.BMF.global_structure
import Submission.Work.BMF.mr_twisted
import Submission.Work.BMF.vk_prime_sums
import Submission.Work.BMF.liouville_facts
import Submission.Work.BMF.corollary_of_uniform

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Final assembly (lead, from requests/bmf/assembly_check.lean.txt, which was checked against the sorried nodes). -/

namespace Work.BMF.Final

open _root_.ArithmeticFunction
open _root_.BoundedMultiplicativeFunctions
set_option autoImplicit false

namespace BoundedMultiplicativeFunctions

open Polynomial Finset Real Complex Filter ArithmeticFunction

open scoped ComplexConjugate

theorem theorem_1_3 (k : ℕ) (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1 / 2) (η : ℝ) (hη : η > 0) :
    ∃ (Q : ℕ+) (_hQ : 1 ≤ Q) (C : ℝ) (_hC : 0 < C) (B : ℝ),
      ∀ (f : ArithmeticFunction ℂ) (_hf : f.IsMultiplicative) (_hf' : IsOneBounded f)
        (X : ℝ) (_hX : X ≥ 1) (H : ℝ) (_hXH : X ^ θ ≤ H) (_hHX : H ≤ X ^ (1 - θ)),
          ∫ x in X..(2 * X), weakGowersUniformityNorm k x H f.intExtension ≥ η * X →
            M f (C * X ^ (k + 1) / H ^ (k + 1)) Q ≤ B := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- `k = 0`: directly Matomäki–Radziwiłł with `ψ = 1`, `T₀ = 0`, `Y = X`, `H' = H`.
    obtain ⟨B₄, C₄, X₄, hC₄, Q₄, hQ₄, hMR⟩ := Work.BMF.mr_twisted θ η hθ₀ (by linarith) hη 1
    have hC₀ : 0 < C₄ + 1 := by positivity
    obtain ⟨B, hB⟩ := Work.BMF.M_le_of_pretends 0 θ B₄ (C₄ + 1) X₄ hθ₀ hθ₁ hC₀
    refine ⟨⟨Q₄, hQ₄⟩, one_le, C₄ + 1, hC₀, B, ?_⟩
    intro f hf hf' X hX H hXH hHX hint
    have hcl := hB f hf' ⟨Q₄, hQ₄⟩ X H hX hXH hHX
    by_cases hXs : X ≤ X₄
    · exact hcl.1 hXs
    push Not at hXs
    have hTC := hcl.2.2 η hint
    have hψ : Work.BMF.IsPeriodicBdd 1 (fun _ ↦ (1 : ℂ)) := ⟨one_pos, fun _ ↦ rfl, fun _ ↦ by simp⟩
    have hHpos : 0 < H := lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith) θ) hXH
    have hHX' : H ≤ X := le_trans hHX (by
      simpa using Real.rpow_le_rpow_of_exponent_le hX (show 1 - θ ≤ 1 by linarith))
    have hXθ : X ^ θ ≤ H := hXH
    obtain ⟨t, ht, hpre⟩ := hMR f hf hf' 1 _ le_rfl hψ 0 X H hXs.le hXθ hHX' hTC
    have hsq : X ^ (1 / 2 : ℝ) ≤ X := by
      simpa using Real.rpow_le_rpow_of_exponent_le hX (show (1 / 2 : ℝ) ≤ 1 by norm_num)
    refine hcl.2.1 X t hsq le_rfl ?_ hpre
    have hXH0 : 0 ≤ X / H := div_nonneg (by linarith) hHpos.le
    have e3 : C₄ * X / H = C₄ * (X / H) := mul_div_assoc _ _ _
    have e4 : (C₄ + 1) * X ^ (0 + 1) / H ^ (0 + 1) = (C₄ + 1) * (X / H) := by
      rw [zero_add, pow_one, pow_one, mul_div_assoc]
    rw [e4]
    rw [sub_zero, e3] at ht
    nlinarith [ht, hXH0]
  obtain ⟨ε₀, hε₀, hBQ⟩ := Work.BMF.build_quadruples k hk θ η hθ₀ hθ₁ hη
  have hθ100 : 0 < θ / 100 := by positivity
  obtain ⟨c₁, C₁, X₁, hc₁, hQD⟩ :=
    hBQ (min ε₀ (θ / 100)) (lt_min hε₀ hθ100) (min_le_left _ _)
  obtain ⟨ℓ, hℓ, c₂, C₂, X₂, hc₂, hADI⟩ :=
    Work.BMF.adi_cycles k θ (min ε₀ (θ / 100)) c₁ C₁ hθ₀ (lt_min hε₀ hθ100)
      (min_le_right _ _) hc₁
  obtain ⟨c₃, C₃, hc₃, hC₃, R₀, hGS⟩ :=
    Work.BMF.global_structure k θ (min ε₀ (θ / 100)) c₂ C₂ ℓ hθ₀ hθ₁ (lt_min hε₀ hθ100)
      (min_le_right _ _) hc₂ hℓ
  obtain ⟨B₄, C₄, X₄, hC₄, Q₄, hQ₄, hMR⟩ :=
    Work.BMF.mr_twisted (θ / 2) c₃ (by positivity) (by linarith) hc₃ R₀
  obtain ⟨X₃, hGS'⟩ := hGS X₄
  have hC₀ : 0 < C₃ + C₄ * C₃ := by positivity
  obtain ⟨B, hB⟩ := Work.BMF.M_le_of_pretends k θ B₄ (C₃ + C₄ * C₃) (max (max X₁ X₂) X₃)
    hθ₀ hθ₁ hC₀
  refine ⟨⟨Q₄, hQ₄⟩, one_le, C₃ + C₄ * C₃, hC₀, B, ?_⟩
  intro f hf hf' X hX H hXH hHX hint
  have hcl := hB f hf' ⟨Q₄, hQ₄⟩ X H hX hXH hHX
  by_cases hXs : X ≤ max (max X₁ X₂) X₃
  · exact hcl.1 hXs
  push Not at hXs
  have hX1 : X₁ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hXs.le
  have hX2 : X₂ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hXs.le
  have hX3 : X₃ ≤ X := le_trans (le_max_right _ _) hXs.le
  obtain ⟨P₁, P₂, h1, h2, h3, h4, ⟨D⟩⟩ := hQD f hf hf' X H hX1 hXH hHX hint
  obtain ⟨A⟩ := hADI f X H P₁ P₂ hX2 hXH hHX h1 h2 h3 h4 D
  obtain ⟨T₀, r, ψ, Y, H', hT₀, hr, hψ, hY₀, hY1, hY2, hH'1, hH'2, hYH, hTC⟩ :=
    hGS' f hf' X H P₁ P₂ hX3 hXH hHX h1 h2 h3 h4 A
  obtain ⟨t, ht, hpre⟩ := hMR f hf hf' r ψ hr hψ T₀ Y H' hY₀ hH'1 hH'2 hTC
  refine hcl.2.1 Y t hY1 hY2 ?_ hpre
  -- `|t| ≤ |T₀| + |t - T₀| ≤ C₃ W + C₄ (Y/H') ≤ (C₃ + C₄ C₃) W`, `W = X^{k+1}/H^{k+1}`
  have e1 : C₃ * X ^ (k + 1) / H ^ (k + 1) = C₃ * (X ^ (k + 1) / H ^ (k + 1)) :=
    mul_div_assoc _ _ _
  have e2 : (C₃ + C₄ * C₃) * X ^ (k + 1) / H ^ (k + 1)
      = (C₃ + C₄ * C₃) * (X ^ (k + 1) / H ^ (k + 1)) := mul_div_assoc _ _ _
  have e3 : C₄ * Y / H' = C₄ * (Y / H') := mul_div_assoc _ _ _
  rw [e1] at hT₀ hYH
  rw [e3] at ht
  rw [e2]
  have h5 : C₄ * (Y / H') ≤ C₄ * (C₃ * (X ^ (k + 1) / H ^ (k + 1))) :=
    mul_le_mul_of_nonneg_left hYH hC₄
  have h6 : |t| ≤ |T₀| + |t - T₀| := by
    have := abs_add_le T₀ (t - T₀)
    simpa using this
  nlinarith [h5, h6, hT₀, ht]

theorem corollary_1_1 (k : ℕ) (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    (fun X ↦ ∫ x in X..(2 * X), weakGowersUniformityNorm k x (X ^ θ) (fun n ↦ liouville ⌊n⌋₊))
      =o[atTop] (fun X ↦ X) := by
  obtain ⟨⟨_, hbd⟩, _⟩ := Work.BMF.liouville_facts 0 (1 / 4) 1 (by norm_num) (by norm_num)
    one_pos 1 0
  have hg : ∀ n : ℤ, ‖((liouville ⌊n⌋₊ : ℤ) : ℂ)‖ ≤ 1 := by
    intro n
    have := hbd ⌊n⌋₊
    simpa [ArithmeticFunction.intCoe_apply] using this
  refine Work.BMF.corollary_of_uniform k (fun n ↦ ((liouville ⌊n⌋₊ : ℤ) : ℂ)) hg ?_ θ hθ₀ hθ₁
  intro θ₁ h0 h1 η hη
  obtain ⟨Q, _, C, hC, B, h⟩ := theorem_1_3 k θ₁ h0 h1 η hη
  obtain ⟨⟨hmul, hbd'⟩, Y₀, hY₀⟩ := Work.BMF.liouville_facts k θ₁ C h0 h1 hC Q B
  refine ⟨max Y₀ 1, fun Y H hY hYH hHY ↦ ?_⟩
  by_contra hcon
  push Not at hcon
  have hext : (liouville : ArithmeticFunction ℂ).intExtension
      = fun n : ℤ ↦ ((liouville ⌊n⌋₊ : ℤ) : ℂ) := by
    funext n
    simp [ArithmeticFunction.intExtension, ArithmeticFunction.intCoe_apply]
  have hle := h (liouville : ArithmeticFunction ℂ) hmul hbd' Y (le_of_max_le_right hY) H hYH hHY
    (by rw [hext]; exact hcon)
  exact absurd hle (not_le.2 (hY₀ Y H (le_of_max_le_left hY) hYH hHY))

end BoundedMultiplicativeFunctions

end Work.BMF.Final
