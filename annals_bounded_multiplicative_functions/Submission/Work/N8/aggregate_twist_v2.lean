import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.N8.aggregate_twist

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# N8: aggregation of local twists into a global twisted correlation (v2)

This is `Work.N8.aggregate_twist_v2`: the same aggregation statement as `Work.N8.aggregate_twist`,
with the *additional* conclusion that the dyadic scale `Y` is bounded above by `64 * (N*L/10)`.

The proof is the proof of `Work.N8.aggregate_twist`; the extra conjunct is exactly the upper
bound on `Y` produced by the dyadic aggregation lemma `Work.N8.dyadic_aggregate`, which v1
computed internally but did not expose in its statement.
-/

namespace Work.N8

open MeasureTheory intervalIntegral
open scoped BigOperators

theorem aggregate_twist_v2 (R₀ : ℕ) (hR₀ : 1 ≤ R₀) (cA : ℝ) (hcA : 0 < cA) :
    ∃ c' : ℝ, 0 < c' ∧
    ∀ (Y₀ N L H' T₀ X : ℝ) (f : ℕ → ℂ) (Xt : Finset ℝ) (Ψ : Finset (ℕ → ℂ)) (r : ℕ),
      0 < L → 0 < H' → H' ≤ L → 1 ≤ N → 16 ≤ cA * N → r ≤ R₀ →
      (Ψ.card : ℝ) ≤ (R₀ : ℝ) ^ R₀ →
      (∀ ψ ∈ Ψ, Work.BMF.IsPeriodicBdd r ψ) →
      (∀ x ∈ Xt, ∃ ψ ∈ Ψ, Work.BMF.LocalTwist f ψ T₀ x L H' cA) →
      (∀ x ∈ Xt, N * L / 10 ≤ x ∧ x + L ≤ 10 * (N * L)) →
      (∀ x ∈ Xt, ∀ x' ∈ Xt, x ≠ x' → 2 * L ≤ |x - x'|) →
      cA * N ≤ (Xt.card : ℝ) →
      10 * (X ^ (1 / 2 : ℝ)) ≤ N * L → 10 * (N * L) ≤ X → Y₀ ≤ N * L / 10 →
      ∃ ψ : ℕ → ℂ, ψ ∈ Ψ ∧ ∃ Y : ℝ,
        Y₀ ≤ Y ∧ X ^ (1 / 2 : ℝ) ≤ Y ∧ Y ≤ X ∧ Y ≤ 64 * (N * L / 10) ∧
        Work.BMF.TwistCorr f ψ T₀ Y H' c' := by
  have hR₀pos : (0 : ℝ) < (R₀ : ℝ) := by exact_mod_cast hR₀
  have hMpos : (0 : ℝ) < (R₀ : ℝ) ^ R₀ := pow_pos hR₀pos R₀
  refine ⟨cA ^ 2 / (100 * (R₀ : ℝ) ^ R₀),
    div_pos (pow_pos hcA 2) (mul_pos (by norm_num) hMpos), ?_⟩
  intro Y₀ N L H' T₀ X f Xt Ψ r hL hH' hH'L hN hcAN hrR hΨcard hper hex hplace hsep hcard
    hXsqrt hXbig hY₀
  -- pigeonhole over the fibers of `Ψ`
  obtain ⟨ψ, hψΨ, S, hSsub, hScard, hSprop⟩ :=
    Work.N8.exists_large_fiber (fun ψ x => Work.BMF.LocalTwist f ψ T₀ x L H' cA) Xt Ψ cA N
      ((R₀ : ℝ) ^ R₀) hcA hN hMpos hΨcard hcard hex
  set G : ℝ → ℝ :=
    fun y => ‖∑ n ∈ Work.BMF.natIcc y (y + H'),
      f n * ψ n * (n : ℂ) ^ (-(Complex.I * T₀))‖ with hGdef
  have hint : ∀ a b : ℝ, IntegrableOn G (Set.uIcc a b) := by
    intro a b
    have h := integrableOn_natIcc_norm H' (fun n => f n * ψ n * (n : ℂ) ^ (-(Complex.I * T₀))) a b
    simpa only [hGdef] using h
  have hGnn : ∀ y, 0 ≤ G y := fun y => norm_nonneg _
  have hNLpos : 0 < N * L := by
    have : (0 : ℝ) < N := by linarith
    positivity
  have hu : 0 < N * L / 10 := by linarith [hNLpos]
  have hXu : 64 * (N * L / 10) ≤ X := by nlinarith [hXbig, hNLpos]
  have hmemS : ∀ x ∈ S, N * L / 10 ≤ x ∧ x + L ≤ 100 * (N * L / 10) := by
    intro x hx
    obtain ⟨h1, h2⟩ := hplace x (hSsub hx)
    refine ⟨h1, ?_⟩
    have : 100 * (N * L / 10) = 10 * (N * L) := by ring
    rw [this]; exact h2
  have hsepS : ∀ x ∈ S, ∀ x' ∈ S, x ≠ x' → 2 * L ≤ |x - x'| :=
    fun x hx x' hx' hne => hsep x (hSsub hx) x' (hSsub hx') hne
  obtain ⟨Y, hYu, hY64, hYX, hYineq⟩ :=
    dyadic_aggregate G hGnn hint (N * L / 10) X L hu hL hXu S hmemS hsepS
  refine ⟨ψ, hψΨ, Y, le_trans hY₀ hYu, ?_, hYX, hY64, ?_⟩
  · have : X ^ (1 / 2 : ℝ) ≤ N * L / 10 := by linarith [hXsqrt]
    exact le_trans this hYu
  · -- the main inequality
    have hSprop' : ∀ x ∈ S, cA * L * H' ≤ ∫ y in x..(x + L), G y :=
      fun x hx => hSprop x hx
    have hsum_lb : (∑ x ∈ S, cA * L * H') ≤ ∑ x ∈ S, ∫ y in x..(x + L), G y :=
      Finset.sum_le_sum hSprop'
    have hsum_const : (∑ x ∈ S, cA * L * H') = (S.card : ℝ) * (cA * L * H') := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have hYnn : 0 ≤ Y := le_trans (le_of_lt hu) hYu
    have hAnn : 0 ≤ ∫ y in Y..(2 * Y), G y :=
      intervalIntegral.integral_nonneg (by linarith) (fun u _ => hGnn u)
    have hlow : (S.card : ℝ) * (cA * L * H') ≤ 7 * ∫ y in Y..(2 * Y), G y := by
      rw [← hsum_const]
      exact le_trans hsum_lb hYineq
    -- clear the denominator
    have h4 : cA ^ 2 * N * L * H' ≤ 7 * (∫ y in Y..(2 * Y), G y) * (R₀ : ℝ) ^ R₀ := by
      have h1 : cA * N / (R₀ : ℝ) ^ R₀ * (cA * L * H')
          ≤ (S.card : ℝ) * (cA * L * H') :=
        mul_le_mul_of_nonneg_right hScard
          (mul_nonneg (mul_nonneg (le_of_lt hcA) (le_of_lt hL)) (le_of_lt hH'))
      have h2 : cA * N / (R₀ : ℝ) ^ R₀ * (cA * L * H')
          = cA ^ 2 * N * L * H' / (R₀ : ℝ) ^ R₀ := by
        field_simp
      have h5 : cA ^ 2 * N * L * H' / (R₀ : ℝ) ^ R₀
          ≤ 7 * (∫ y in Y..(2 * Y), G y) := by
        rw [← h2]
        exact le_trans h1 hlow
      rwa [div_le_iff₀ hMpos] at h5
    have hYb : Y ≤ 32 * N * L / 5 := by nlinarith [hY64]
    have hb1 : cA ^ 2 * H' * Y ≤ cA ^ 2 * H' * (32 * N * L / 5) :=
      mul_le_mul_of_nonneg_left hYb (mul_nonneg (sq_nonneg cA) (le_of_lt hH'))
    have hb2 : cA ^ 2 * H' * (32 * N * L / 5) = 32 / 5 * (cA ^ 2 * N * L * H') := by
      ring
    have hb3 : 32 / 5 * (cA ^ 2 * N * L * H')
        ≤ 32 / 5 * (7 * (∫ y in Y..(2 * Y), G y) * (R₀ : ℝ) ^ R₀) :=
      mul_le_mul_of_nonneg_left h4 (by norm_num)
    have hAM : 0 ≤ (∫ y in Y..(2 * Y), G y) * (R₀ : ℝ) ^ R₀ :=
      mul_nonneg hAnn (le_of_lt hMpos)
    have hb4 : 32 / 5 * (7 * (∫ y in Y..(2 * Y), G y) * (R₀ : ℝ) ^ R₀)
        ≤ (∫ y in Y..(2 * Y), G y) * (100 * (R₀ : ℝ) ^ R₀) := by
      nlinarith [hAM]
    have hmain2 : cA ^ 2 * H' * Y
        ≤ (∫ y in Y..(2 * Y), G y) * (100 * (R₀ : ℝ) ^ R₀) :=
      le_trans hb1 (le_trans (le_of_eq hb2) (le_trans hb3 hb4))
    have hkey : cA ^ 2 / (100 * (R₀ : ℝ) ^ R₀) * H' * Y ≤ ∫ y in Y..(2 * Y), G y := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div,
        div_le_iff₀ (mul_pos (by norm_num) hMpos)]
      linarith [hmain2]
    rw [Work.BMF.TwistCorr]
    exact hkey

end Work.N8
