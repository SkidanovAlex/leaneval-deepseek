import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.StrongPersist.N6.ProdDefs6
import Submission.Work.FTS.StrongPersist.N6.Slots
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz
import Submission.Work.FTS.OpenPkg.ProdOpen.z_sum_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Work.Spaces

/-
The level-six shift of `Work.FTS.OpenPkg.ProdOpen.z_sum_bound`: the proof is that proof with
`4 ↦ 6` and `3 ↦ 5`, i.e. the binomial constant `256 ↦ 4096` (`binom_sq_le_4096`), `(i+1) ≤ 5 ↦ ≤ 7`
and `6400 ↦ 200704`, using `PwAny6` in place of `PwAny` and `SInv6`/`Texc6` in place of
`SInv`/`Texc`.
-/
theorem z_sum_bound6 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
    ∀ i : ℕ, i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ C * (Work.FTS.StrongPersist.N6.SInv6 α f g z θ
            + Work.FTS.StrongPersist.N6.Texc6 α f g z θ) := by
  obtain ⟨CPw, hCPwpos, hPw⟩ := PwAny6
  refine ⟨200704 * CPw, by positivity, ?_⟩
  intro α f g hα hα1 hF hFmem hG hGmem i hi z θ hz hθ0 hθ1
  change (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ * Hv6 z θ) ^ 2
      ≤ 200704 * CPw * (SInv6 α f g z θ + Texc6 α f g z θ)
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hSl : 0 ≤ SInv6 α f g z θ := SInv6_nonneg hα f g z θ
  have hTl : 0 ≤ Texc6 α f g z θ := Texc6_nonneg α f g z θ
  have hγ : 0 < gam α - 1 := gam_sub_one_pos6 hα
  have hKnn : ∀ (u : ℝ → ℝ → ℝ), 0 ≤ CPw / (gam α - 1) * HkSq α 6 u := fun u =>
    mul_nonneg (div_nonneg hCPwpos.le hγ.le) (HkSq_nonneg α 6 u)
  -- ### Step 1: Leibniz plus Cauchy–Schwarz
  have hcs : (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ * Hv6 z θ) ^ 2
      ≤ ((i + 1 : ℕ) : ℝ)
        * ∑ b ∈ Finset.range (i + 1),
            ((i.choose b : ℝ) * (DzIter b f z θ * DzIter (i - b) g z θ * Hv6 z θ)) ^ 2 := by
    have hsum : Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ * Hv6 z θ
        = ∑ b ∈ Finset.range (i + 1),
            ((i.choose b : ℝ) * (DzIter b f z θ * DzIter (i - b) g z θ * Hv6 z θ)) := by
      rw [Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz i f g hF hG z θ hz hθ0 hθ1,
        Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [hsum]
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
      (f := fun b => (i.choose b : ℝ) * (DzIter b f z θ * DzIter (i - b) g z θ * Hv6 z θ))
    simpa using h
  -- ### Step 2: each Leibniz summand is dominated by `CPw * SInv6`
  have hterm : ∀ b ∈ Finset.range (i + 1),
      ((i.choose b : ℝ) * (DzIter b f z θ * DzIter (i - b) g z θ * Hv6 z θ)) ^ 2
        ≤ 4096 * (CPw * SInv6 α f g z θ) := by
    intro b hb
    have hbi : b ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have hcb : (i.choose b : ℝ) ^ 2 ≤ 4096 := binom_sq_le_4096 i b hbi hi
    have hcore : (DzIter b f z θ * DzIter (i - b) g z θ * Hv6 z θ) ^ 2
        ≤ CPw * SInv6 α f g z θ := by
      by_cases hcase : b ≤ i - b
      · -- the `f`-factor is the one of low order `b ≤ 3`
        have hb3 : b ≤ 3 := by omega
        have hx : (DzIter b f z θ) ^ 2 ≤ CPw / (gam α - 1) * HkSq α 6 f := by
          have h := hPw α f b 0 hα hα1 hF hFmem (by omega) z hz θ hθ
          simpa only [Work.Spaces.mixed_zero_right] using h
        have hy : (DzIter (i - b) g z θ * Hv6 z θ) ^ 2 ≤ HkIntegrand α 6 g z θ := by
          have h := sq_le_HkIntegrand_z α 6 g z θ (i - b) (by omega)
          simpa only [Hv6] using h
        have h1 : (DzIter b f z θ * DzIter (i - b) g z θ * Hv6 z θ) ^ 2
            = (DzIter b f z θ) ^ 2 * (DzIter (i - b) g z θ * Hv6 z θ) ^ 2 := by ring
        rw [h1]
        refine le_trans (le_trans (mul_le_mul_of_nonneg_right hx (sq_nonneg _))
          (mul_le_mul_of_nonneg_left hy (hKnn f))) ?_
        rw [show CPw / (gam α - 1) * HkSq α 6 f * HkIntegrand α 6 g z θ
            = CPw * ((gam α - 1)⁻¹ * (HkSq α 6 f * HkIntegrand α 6 g z θ)) by
          rw [div_eq_mul_inv]; ring]
        exact mul_le_mul_of_nonneg_left (mul_inv_mul_le_SInv6_left hα f g z θ) hCPwpos.le
      · -- the `g`-factor is the one of low order `i - b ≤ 3`
        have hib3 : i - b ≤ 3 := by omega
        have hy : (DzIter (i - b) g z θ) ^ 2 ≤ CPw / (gam α - 1) * HkSq α 6 g := by
          have h := hPw α g (i - b) 0 hα hα1 hG hGmem (by omega) z hz θ hθ
          simpa only [Work.Spaces.mixed_zero_right] using h
        have hx : (DzIter b f z θ * Hv6 z θ) ^ 2 ≤ HkIntegrand α 6 f z θ := by
          have h := sq_le_HkIntegrand_z α 6 f z θ b (by omega)
          simpa only [Hv6] using h
        have h1 : (DzIter b f z θ * DzIter (i - b) g z θ * Hv6 z θ) ^ 2
            = (DzIter (i - b) g z θ) ^ 2 * (DzIter b f z θ * Hv6 z θ) ^ 2 := by ring
        rw [h1]
        refine le_trans (le_trans (mul_le_mul_of_nonneg_right hy (sq_nonneg _))
          (mul_le_mul_of_nonneg_left hx (hKnn g))) ?_
        rw [show CPw / (gam α - 1) * HkSq α 6 g * HkIntegrand α 6 f z θ
            = CPw * ((gam α - 1)⁻¹ * (HkSq α 6 g * HkIntegrand α 6 f z θ)) by
          rw [div_eq_mul_inv]; ring]
        exact mul_le_mul_of_nonneg_left (mul_inv_mul_le_SInv6_right hα f g z θ) hCPwpos.le
    have h1 : ((i.choose b : ℝ) * (DzIter b f z θ * DzIter (i - b) g z θ * Hv6 z θ)) ^ 2
        = (i.choose b : ℝ) ^ 2 * (DzIter b f z θ * DzIter (i - b) g z θ * Hv6 z θ) ^ 2 := by
      ring
    rw [h1]
    exact le_trans (mul_le_mul_of_nonneg_right hcb (sq_nonneg _))
      (mul_le_mul_of_nonneg_left hcore (by norm_num))
  -- ### Step 3: sum the terms
  have hsum_bd : ∑ b ∈ Finset.range (i + 1),
      ((i.choose b : ℝ) * (DzIter b f z θ * DzIter (i - b) g z θ * Hv6 z θ)) ^ 2
        ≤ ((i + 1 : ℕ) : ℝ) * (4096 * (CPw * SInv6 α f g z θ)) := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ _ hterm) ?_
    simp [nsmul_eq_mul]
  have hm : ((i + 1 : ℕ) : ℝ) ≤ 7 := by
    have : (i : ℝ) ≤ 6 := by exact_mod_cast hi
    push_cast
    linarith
  have hKnn' : 0 ≤ 4096 * (CPw * SInv6 α f g z θ) :=
    mul_nonneg (by norm_num) (mul_nonneg hCPwpos.le hSl)
  have hstep : ((i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) * (4096 * (CPw * SInv6 α f g z θ)))
      ≤ 200704 * (CPw * SInv6 α f g z θ) := by
    have hmnn : (0 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by positivity
    have h1 : ((i + 1 : ℕ) : ℝ) * (4096 * (CPw * SInv6 α f g z θ))
        ≤ 7 * (4096 * (CPw * SInv6 α f g z θ)) := mul_le_mul_of_nonneg_right hm hKnn'
    have h2 : ((i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) * (4096 * (CPw * SInv6 α f g z θ)))
        ≤ 7 * (7 * (4096 * (CPw * SInv6 α f g z θ))) :=
      mul_le_mul hm h1 (mul_nonneg hmnn hKnn') (by norm_num)
    have h3 : 7 * (7 * (4096 * (CPw * SInv6 α f g z θ)))
        = 200704 * (CPw * SInv6 α f g z θ) := by
      ring
    linarith [h2, h3]
  calc (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ * Hv6 z θ) ^ 2
      ≤ ((i + 1 : ℕ) : ℝ)
          * ∑ b ∈ Finset.range (i + 1),
              ((i.choose b : ℝ) * (DzIter b f z θ * DzIter (i - b) g z θ * Hv6 z θ)) ^ 2 := hcs
    _ ≤ ((i + 1 : ℕ) : ℝ)
          * (((i + 1 : ℕ) : ℝ) * (4096 * (CPw * SInv6 α f g z θ))) :=
        mul_le_mul_of_nonneg_left hsum_bd (by positivity)
    _ ≤ 200704 * (CPw * SInv6 α f g z θ) := hstep
    _ ≤ 200704 * (CPw * (SInv6 α f g z θ + Texc6 α f g z θ)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hTl) hCPwpos.le) (by norm_num)
    _ = 200704 * CPw * (SInv6 α f g z θ + Texc6 α f g z θ) := by ring

end Work.FTS.StrongPersist.N6
