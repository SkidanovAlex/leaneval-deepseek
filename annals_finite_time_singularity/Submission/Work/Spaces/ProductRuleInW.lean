/-
Copyright: work module for the Elgindi finite-time singularity project.

# The product rule in the weighted space `𝒲^{4,∞}`

`Work.Spaces.ProductRuleInW`: there is a universal constant `C > 0` such that for every
`0 < α ≤ 1` and all `SmoothInt` functions `f g` lying in `𝒲^{4,∞}`,

`|f · g|_{𝒲^{4,∞}} ≤ C · |f|_{𝒲^{4,∞}} · |g|_{𝒲^{4,∞}}`.

The estimate is proved by expanding the derivatives of `f · g` with the Leibniz rule
(`pz_mixed_mul_le_4`) and bounding each of the resulting factors with
`WlInf_z_bound`/`factor_bound`: a factor carrying `m` radial derivatives and `i`
angular derivatives absorbs the weight `(z+1)^m` and contributes at most
`|·|_𝒲 · (α + sin 2θ) sin(2θ)^{α/5}` when `i ≥ 1` (and at most `|·|_𝒲` when `i = 0`).
The single `𝒲`-weight `sin(2θ)^{-α/5}/(α+sin 2θ)` of the mixed part is then shared by
the two factors of each term, and `psi_mw_le` shows that the leftover factor is `≤ 2`
uniformly in `α ∈ (0,1]` and `θ ∈ [0,π/2]` — this is what makes the constant universal.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.DthIter_mul_le
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.psi_mw_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
namespace Work.Spaces
set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Elementary nonnegativity facts -/

/-- The `𝒲^{l,∞}`-norm is nonnegative whenever it is honest. -/
theorem WlInf_nonneg (α : ℝ) (l : ℕ) (h : ℝ → ℝ → ℝ) (hmem : WlInfMem α l h) :
    0 ≤ WlInf α l h := by
  rw [WlInf]
  exact add_nonneg (wlZSum_nonneg α l h hmem) (wlThSum_nonneg α l h hmem)

/-- The angular factor `Φ_i(θ) = 1` for `i = 0`, `= (α + sin 2θ) sin(2θ)^{α/5}` for `i ≥ 1`
is nonnegative. -/
theorem psi_nonneg (α θ : ℝ) (hα : 0 < α) (hθ : θ ∈ Iθ) (i : ℕ) :
    0 ≤ (if i = 0 then (1 : ℝ) else (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
  by_cases h : i = 0
  · rw [if_pos h]; norm_num
  · rw [if_neg h]
    have hs0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2])
    exact mul_nonneg (by linarith) (Real.rpow_nonneg hs0 _)

/-! ## The product rule -/

theorem ProductRuleInW : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 → Work.Spaces.SmoothInt f → Work.Spaces.SmoothInt g →
    Work.Spaces.WlInfMem α 4 f → Work.Spaces.WlInfMem α 4 g →
    Work.Spaces.WlInf α 4 (fun z θ => f z θ * g z θ) ≤
      C * Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g := by
  refine ⟨327676, by norm_num, ?_⟩
  intro α f g hα hα1 hf hg hmf hmg
  have hWfnn : 0 ≤ WlInf α 4 f := WlInf_nonneg α 4 f hmf
  have hWgnn : 0 ≤ WlInf α 4 g := WlInf_nonneg α 4 g hmg
  have hWWnn : 0 ≤ WlInf α 4 f * WlInf α 4 g := mul_nonneg hWfnn hWgnn
  have hZ : ∀ k ∈ Finset.range 5,
      supAbs (fun z θ => (z + 1) ^ k * pzIter k (fun z θ => f z θ * g z θ) z θ) ≤
        1285 * (WlInf α 4 f * WlInf α 4 g) := by
    intro k hk
    have hk4 : k ≤ 4 := by have := Finset.mem_range.mp hk; omega
    refine supAbs_le (fun z hz θ hθ => ?_)
    have hz0 : (0 : ℝ) ≤ z := hz
    have hzp : (0 : ℝ) ≤ (z + 1) ^ k := pow_nonneg (by linarith) k
    have hleib := pz_mixed_mul_le_4 k 0 hk4 (by omega) f g hf hg z hz θ hθ
    have h1 : |pzIter k (fun z θ => f z θ * g z θ) z θ| ≤ 257 * ∑ c ∈ Finset.range (k + 1),
        |pzIter c f z θ| * |pzIter (k - c) g z θ| := by
      simpa using hleib
    have hstep : ∀ c ∈ Finset.range (k + 1),
        (z + 1) ^ k * (|pzIter c f z θ| * |pzIter (k - c) g z θ|)
          ≤ WlInf α 4 f * WlInf α 4 g := by
      intro c hc
      have hc_le : c ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hc)
      have hc4 : c ≤ 4 := by omega
      have hkc4 : k - c ≤ 4 := by omega
      have hc0 : (0 : ℝ) ≤ (z + 1) ^ c := pow_nonneg (by linarith) c
      have hkc0 : (0 : ℝ) ≤ (z + 1) ^ (k - c) := pow_nonneg (by linarith) (k - c)
      have hA := WlInf_z_bound α 4 f hmf c hc4 z θ hz hθ
      have hB := WlInf_z_bound α 4 g hmg (k - c) hkc4 z θ hz hθ
      rw [abs_mul, abs_of_nonneg hc0] at hA
      rw [abs_mul, abs_of_nonneg hkc0] at hB
      have heq : (z + 1) ^ k * (|pzIter c f z θ| * |pzIter (k - c) g z θ|)
          = ((z + 1) ^ c * |pzIter c f z θ|) * ((z + 1) ^ (k - c) * |pzIter (k - c) g z θ|) := by
        rw [show (z + 1) ^ k = (z + 1) ^ c * (z + 1) ^ (k - c) by
              rw [← pow_add, Nat.add_sub_cancel' hc_le]]
        ring
      rw [heq]
      exact mul_le_mul hA hB (mul_nonneg hkc0 (abs_nonneg _)) hWfnn
    calc |(z + 1) ^ k * pzIter k (fun z θ => f z θ * g z θ) z θ|
        = (z + 1) ^ k * |pzIter k (fun z θ => f z θ * g z θ) z θ| := by
            rw [abs_mul, abs_of_nonneg hzp]
      _ ≤ (z + 1) ^ k * (257 * ∑ c ∈ Finset.range (k + 1),
            |pzIter c f z θ| * |pzIter (k - c) g z θ|) := mul_le_mul_of_nonneg_left h1 hzp
      _ = 257 * ((z + 1) ^ k * ∑ c ∈ Finset.range (k + 1),
            |pzIter c f z θ| * |pzIter (k - c) g z θ|) := by ring
      _ = 257 * ∑ c ∈ Finset.range (k + 1),
            (z + 1) ^ k * (|pzIter c f z θ| * |pzIter (k - c) g z θ|) := by
          rw [Finset.mul_sum]
      _ ≤ 257 * ∑ c ∈ Finset.range (k + 1), WlInf α 4 f * WlInf α 4 g :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hstep) (by norm_num)
      _ = (257 * (((k + 1 : ℕ)) : ℝ)) * (WlInf α 4 f * WlInf α 4 g) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      _ ≤ 1285 * (WlInf α 4 f * WlInf α 4 g) := by
          apply mul_le_mul_of_nonneg_right _ hWWnn
          have hk5 : (((k + 1 : ℕ)) : ℝ) ≤ 5 := by
            exact_mod_cast (show k + 1 ≤ 5 by omega)
          nlinarith
  have hTh : ∀ j ∈ Finset.range 5, ∀ k ∈ Finset.range 5,
      (if 1 ≤ j ∧ k + j ≤ 4 then
        supAbs (fun z θ => (z + 1) ^ k * pzIter k (DthIter j (fun z θ => f z θ * g z θ)) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      else 0) ≤ 12850 * (WlInf α 4 f * WlInf α 4 g) := by
    intro j hjmem k hkmem
    have hj4 : j ≤ 4 := by have := Finset.mem_range.mp hjmem; omega
    have hk4 : k ≤ 4 := by have := Finset.mem_range.mp hkmem; omega
    by_cases hcond : 1 ≤ j ∧ k + j ≤ 4
    · rw [if_pos hcond]
      obtain ⟨hj1, hjk⟩ := hcond
      refine supAbs_le (fun z hz θ hθ => ?_)
      have hz0 : (0 : ℝ) ≤ z := hz
      have hs0 : 0 ≤ Real.sin (2 * θ) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2])
      have hspos : 0 < α + Real.sin (2 * θ) := by linarith
      have hmwnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) :=
        div_nonneg (Real.rpow_nonneg hs0 _) (le_of_lt hspos)
      have hzp : 0 ≤ (z + 1) ^ k := pow_nonneg (by linarith) k
      have hleib := pz_mixed_mul_le_4 k j hk4 hj4 f g hf hg z hz θ hθ
      have h1 : |pzIter k (DthIter j (fun z θ => f z θ * g z θ)) z θ| ≤
          257 * ∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
            |pzIter c (DthIter a f) z θ| * |pzIter (k - c) (DthIter (j - a) g) z θ| := by
        simpa using hleib
      have step : ∀ c ∈ Finset.range (k + 1), ∀ a ∈ Finset.range (j + 1),
          (z + 1) ^ k * (|pzIter c (DthIter a f) z θ|
              * |pzIter (k - c) (DthIter (j - a) g) z θ|)
              * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
            ≤ 2 * (WlInf α 4 f * WlInf α 4 g) := by
        intro c hc a ha
        have hc_le : c ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hc)
        have ha_le : a ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
        have hc4 : c ≤ 4 := by omega
        have hkc4 : k - c ≤ 4 := by omega
        have hca : 1 ≤ a → c + a ≤ 4 := by intro h; omega
        have hka : 1 ≤ j - a → (k - c) + (j - a) ≤ 4 := by intro h; omega
        have hFA := factor_bound α hα f hmf c a hc4 hca z θ hz hθ
        have hGA := factor_bound α hα g hmg (k - c) (j - a) hkc4 hka z θ hz hθ
        have hψa : 0 ≤ (if a = 0 then (1 : ℝ) else
            (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
          psi_nonneg α θ hα hθ a
        have hψb : 0 ≤ (if j - a = 0 then (1 : ℝ) else
            (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
          psi_nonneg α θ hα hθ (j - a)
        have hprod : (z + 1) ^ k * (|pzIter c (DthIter a f) z θ|
              * |pzIter (k - c) (DthIter (j - a) g) z θ|)
            = |(z + 1) ^ c * pzIter c (DthIter a f) z θ|
              * |(z + 1) ^ (k - c) * pzIter (k - c) (DthIter (j - a) g) z θ| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg (by linarith : (0:ℝ) ≤ z + 1) c),
            abs_of_nonneg (pow_nonneg (by linarith : (0:ℝ) ≤ z + 1) (k - c))]
          rw [show (z + 1) ^ k = (z + 1) ^ c * (z + 1) ^ (k - c) by
                rw [← pow_add, Nat.add_sub_cancel' hc_le]]
          ring
        rw [hprod]
        have hstep1 : |(z + 1) ^ c * pzIter c (DthIter a f) z θ|
              * |(z + 1) ^ (k - c) * pzIter (k - c) (DthIter (j - a) g) z θ|
            ≤ (WlInf α 4 f * (if a = 0 then (1 : ℝ) else
                  (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
              * (WlInf α 4 g * (if j - a = 0 then (1 : ℝ) else
                  (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
          mul_le_mul hFA hGA (abs_nonneg _) (mul_nonneg hWfnn hψa)
        have hpsi := psi_mw_le α hα hα1 θ hθ a j ha_le hj1
        calc (|(z + 1) ^ c * pzIter c (DthIter a f) z θ|
                * |(z + 1) ^ (k - c) * pzIter (k - c) (DthIter (j - a) g) z θ|)
              * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
            ≤ ((WlInf α 4 f * (if a = 0 then (1 : ℝ) else
                    (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
                * (WlInf α 4 g * (if j - a = 0 then (1 : ℝ) else
                    (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))))
                * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) :=
              mul_le_mul_of_nonneg_right hstep1 hmwnn
          _ = (WlInf α 4 f * WlInf α 4 g)
                * ((if a = 0 then (1 : ℝ) else
                    (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                  * (if j - a = 0 then (1 : ℝ) else
                    (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                  * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) := by ring
          _ ≤ (WlInf α 4 f * WlInf α 4 g) * 2 := mul_le_mul_of_nonneg_left hpsi hWWnn
          _ = 2 * (WlInf α 4 f * WlInf α 4 g) := by ring
      have hsum : ∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
            (z + 1) ^ k * (|pzIter c (DthIter a f) z θ|
              * |pzIter (k - c) (DthIter (j - a) g) z θ|)
              * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
          ≤ ∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
              2 * (WlInf α 4 f * WlInf α 4 g) :=
        Finset.sum_le_sum (fun c hc => Finset.sum_le_sum (fun a ha => step c hc a ha))
      have hAB : (z + 1) ^ k * (∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
              |pzIter c (DthIter a f) z θ| * |pzIter (k - c) (DthIter (j - a) g) z θ|)
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
          = ∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
              (z + 1) ^ k * (|pzIter c (DthIter a f) z θ|
                * |pzIter (k - c) (DthIter (j - a) g) z θ|)
              * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
      calc |(z + 1) ^ k * pzIter k (DthIter j (fun z θ => f z θ * g z θ)) z θ
              * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
          = (z + 1) ^ k * |pzIter k (DthIter j (fun z θ => f z θ * g z θ)) z θ|
              * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := by
            rw [abs_div, abs_mul, abs_mul, abs_of_nonneg hzp,
              abs_of_nonneg (Real.rpow_nonneg hs0 _), abs_of_pos hspos]
            ring
        _ ≤ (z + 1) ^ k * (257 * ∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
              |pzIter c (DthIter a f) z θ| * |pzIter (k - c) (DthIter (j - a) g) z θ|)
              * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hzp) hmwnn
        _ = 257 * (∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
              (z + 1) ^ k * (|pzIter c (DthIter a f) z θ|
                * |pzIter (k - c) (DthIter (j - a) g) z θ|)
              * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) := by
            rw [show (z + 1) ^ k * (257 * (∑ c ∈ Finset.range (k + 1),
                    ∑ a ∈ Finset.range (j + 1),
                    |pzIter c (DthIter a f) z θ| * |pzIter (k - c) (DthIter (j - a) g) z θ|))
                  * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
                = 257 * ((z + 1) ^ k * (∑ c ∈ Finset.range (k + 1),
                    ∑ a ∈ Finset.range (j + 1),
                    |pzIter c (DthIter a f) z θ| * |pzIter (k - c) (DthIter (j - a) g) z θ|)
                  * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) by ring,
              hAB]
        _ ≤ 257 * ∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
              2 * (WlInf α 4 f * WlInf α 4 g) := mul_le_mul_of_nonneg_left hsum (by norm_num)
        _ = (257 * (((k + 1 : ℕ)) : ℝ) * (((j + 1 : ℕ)) : ℝ))
              * (2 * (WlInf α 4 f * WlInf α 4 g)) := by
            rw [Finset.sum_const, Finset.card_range, Finset.sum_const, Finset.card_range,
              nsmul_eq_mul, nsmul_eq_mul]
            ring
        _ = (257 * (((k + 1 : ℕ)) : ℝ) * (((j + 1 : ℕ)) : ℝ) * 2)
              * (WlInf α 4 f * WlInf α 4 g) := by ring
        _ ≤ 12850 * (WlInf α 4 f * WlInf α 4 g) := by
            apply mul_le_mul_of_nonneg_right _ hWWnn
            have hk5 : (((k + 1 : ℕ)) : ℝ) ≤ 5 := by
              exact_mod_cast (show k + 1 ≤ 5 by omega)
            have hj5 : (((j + 1 : ℕ)) : ℝ) ≤ 5 := by
              exact_mod_cast (show j + 1 ≤ 5 by omega)
            have hk0 : (0 : ℝ) ≤ (((k + 1 : ℕ)) : ℝ) := Nat.cast_nonneg (α := ℝ) _
            have hj0 : (0 : ℝ) ≤ (((j + 1 : ℕ)) : ℝ) := Nat.cast_nonneg (α := ℝ) _
            nlinarith [hk5, hj5, hk0, hj0]
    · rw [if_neg hcond]
      exact mul_nonneg (by norm_num) hWWnn
  have e1 : (∑ k ∈ Finset.range 5,
        supAbs (fun z θ => (z + 1) ^ k * pzIter k (fun z θ => f z θ * g z θ) z θ))
      ≤ 5 * (1285 * (WlInf α 4 f * WlInf α 4 g)) := by
    calc _ ≤ ∑ k ∈ Finset.range 5, 1285 * (WlInf α 4 f * WlInf α 4 g) := Finset.sum_le_sum hZ
      _ = 5 * (1285 * (WlInf α 4 f * WlInf α 4 g)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
  have e2 : (∑ j ∈ Finset.range 5, ∑ k ∈ Finset.range 5,
        if 1 ≤ j ∧ k + j ≤ 4 then
          supAbs (fun z θ => (z + 1) ^ k * pzIter k (DthIter j (fun z θ => f z θ * g z θ)) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        else 0)
      ≤ 25 * (12850 * (WlInf α 4 f * WlInf α 4 g)) := by
    calc _ ≤ ∑ j ∈ Finset.range 5, ∑ k ∈ Finset.range 5,
          12850 * (WlInf α 4 f * WlInf α 4 g) :=
          Finset.sum_le_sum (fun j hj => Finset.sum_le_sum (fun k hk => hTh j hj k hk))
      _ = 25 * (12850 * (WlInf α 4 f * WlInf α 4 g)) := by
          rw [Finset.sum_const, Finset.card_range, Finset.sum_const, Finset.card_range,
            nsmul_eq_mul, nsmul_eq_mul]
          ring
  conv_lhs => rw [WlInf]
  have htarget : 327676 * WlInf α 4 f * WlInf α 4 g
      = 327676 * (WlInf α 4 f * WlInf α 4 g) := by ring
  rw [htarget]
  nlinarith [e1, e2, hWWnn]

end Work.Spaces
