import Mathlib
import Submission.Work.GM.S3.Defs
import Submission.Work.GM.S3.prop101_defs
import Submission.Work.GM.S3.RtildeSq_continuous
import Submission.Work.GM.S3.RtildeSq_eq_zero_of_notMem
import Submission.Work.GM.S3.integral_comp_inv
import Submission.Work.GM.S3.bsum_reflect
import Submission.Work.GM.S3.S34_le_affine

namespace Work.GM.S3

open Complex Finset MeasureTheory
open scoped BigOperators
open Submission.GM (affineSum)

/-!
# GM 10.1: reduction of `S₃,₃` to an `affineSum` integral

Auxiliary lemmas for `prop101_S33_le_affine`:

* `prop101_Rtilde_continuous` -- `R̃ = √(R̃²)` is continuous;
* `prop101_continuous_affineSum` -- `u ↦ affineSum K M₁ M₂ M₃ f u` is continuous for continuous `f`;
* `prop101_continuous_asumInvPos`, `prop101_continuous_asumInv` -- the `u = 1/v` forms of `Asum`
  are continuous;
* `prop101_asumInvPos_nonneg` -- `0 ≤ AsumInvPos`;
* `prop101_asum_eq_asuminv` -- `Asum v = AsumInv (1/v)` for `v ≠ 0`;
* `prop101_asuminv_eq_two_mul` -- the reflection `(m₁,m₂,m₃) ↦ (-m₁,-m₂,-m₃)` doubles the `m₂ > 0`
  part of `AsumInv`;
* `prop101_asuminvPos_le_affineSum` -- pointwise domination of `AsumInvPos` by `affineSum`;
* `prop101_affineSum_hasCompactSupport` -- compact support of the dominating affine sum.
-/

/-- Continuity of `x ↦ R̃ x = √(R̃² x)` (the square root of the continuous `R̃²`). -/
theorem prop101_Rtilde_continuous (W : Finset ℝ) (N : ℕ) (B : ℝ) (ψ₁ ψ₂ : ℝ → ℝ)
    (hψ₁ : IsBumpAtZero ψ₁ 16) (hψ₂ : IsBumpAtOne ψ₂ 16) :
    Continuous (fun x => Rtilde W N B ψ₁ ψ₂ x) :=
  Real.continuous_sqrt.comp (RtildeSq_continuous W N B 16 ψ₁ ψ₂ hψ₁ hψ₂)

/-- Continuity of `u ↦ affineSum K M₁ M₂ M₃ f u` for continuous `f`. -/
theorem prop101_continuous_affineSum (K M₁ M₂ M₃ : ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    Continuous (fun u => affineSum K M₁ M₂ M₃ f u) := by
  simp only [affineSum]
  refine continuous_finsetSum _ (fun a _ => ?_)
  refine continuous_finsetSum _ (fun b hb => ?_)
  refine continuous_finsetSum _ (fun c _ => ?_)
  have hb1 : (1 : ℤ) ≤ b := (mem_Icc.mp (mem_filter.mp hb).1).1
  have hbne : ((b : ℤ) : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb1
    linarith
  have harg : Continuous (fun u : ℝ => (((a : ℝ) * u + (c : ℝ)) / (b : ℝ))) := by
    rw [show (fun u : ℝ => (((a : ℝ) * u + (c : ℝ)) / (b : ℝ)))
        = fun u => (((a : ℝ) * u + (c : ℝ)) * ((b : ℝ))⁻¹) from by
      funext u; rw [div_eq_mul_inv]]
    fun_prop
  exact hf.comp harg

/-- Continuity of `u ↦ AsumInvPos N W B M₁ M ψ₁ ψ₂ u`. -/
theorem prop101_continuous_asumInvPos (N : ℕ) (W : Finset ℝ) (B M₁ M : ℝ) (ψ₁ ψ₂ : ℝ → ℝ)
    (hψ₁ : IsBumpAtZero ψ₁ 16) (hψ₂ : IsBumpAtOne ψ₂ 16) :
    Continuous (fun u => AsumInvPos N W B M₁ M ψ₁ ψ₂ u) := by
  have hRt : Continuous (fun x => Rtilde W N B ψ₁ ψ₂ x) :=
    prop101_Rtilde_continuous W N B ψ₁ ψ₂ hψ₁ hψ₂
  simp only [AsumInvPos]
  refine continuous_finsetSum _ (fun a _ => ?_)
  refine continuous_finsetSum _ (fun b hb => ?_)
  refine continuous_finsetSum _ (fun c _ => ?_)
  have hb1 : (1 : ℤ) ≤ b := (mem_Icc.mp (mem_filter.mp hb).1).1
  have hbne : ((b : ℤ) : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb1
    linarith
  have harg : Continuous (fun u : ℝ => (((c : ℝ) * u + (a : ℝ)) / (b : ℝ))) := by
    rw [show (fun u : ℝ => (((c : ℝ) * u + (a : ℝ)) / (b : ℝ)))
        = fun u => (((c : ℝ) * u + (a : ℝ)) * ((b : ℝ))⁻¹) from by
      funext u; rw [div_eq_mul_inv]]
    fun_prop
  exact (hRt.comp harg).pow 2

/-- Continuity of `u ↦ AsumInv N W B M₁ M ψ₁ ψ₂ u` (the `m₂`-range is `idxM M`, so `M ≥ 1`
ensures `m₂ ≠ 0`). -/
theorem prop101_continuous_asumInv (N : ℕ) (W : Finset ℝ) (B M₁ M : ℝ) (ψ₁ ψ₂ : ℝ → ℝ)
    (hψ₁ : IsBumpAtZero ψ₁ 16) (hψ₂ : IsBumpAtOne ψ₂ 16) (hM : 1 ≤ M) :
    Continuous (fun u => AsumInv N W B M₁ M ψ₁ ψ₂ u) := by
  have hRt : Continuous (fun x => Rtilde W N B ψ₁ ψ₂ x) :=
    prop101_Rtilde_continuous W N B ψ₁ ψ₂ hψ₁ hψ₂
  simp only [AsumInv]
  refine continuous_finsetSum _ (fun a _ => ?_)
  refine continuous_finsetSum _ (fun b hb => ?_)
  refine continuous_finsetSum _ (fun c _ => ?_)
  have hbne : ((b : ℤ) : ℝ) ≠ 0 := by
    have h := (mem_filter.mp hb).2
    intro h0
    rw [h0] at h
    simp at h
    linarith
  have harg : Continuous (fun u : ℝ => (((c : ℝ) * u + (a : ℝ)) / (b : ℝ))) := by
    rw [show (fun u : ℝ => (((c : ℝ) * u + (a : ℝ)) / (b : ℝ)))
        = fun u => (((c : ℝ) * u + (a : ℝ)) * ((b : ℝ))⁻¹) from by
      funext u; rw [div_eq_mul_inv]]
    fun_prop
  exact (hRt.comp harg).pow 2

/-- `0 ≤ AsumInvPos u` (a finite sum of squares). -/
theorem prop101_asumInvPos_nonneg (N : ℕ) (W : Finset ℝ) (B M₁ M : ℝ) (ψ₁ ψ₂ : ℝ → ℝ)
    (u : ℝ) : 0 ≤ AsumInvPos N W B M₁ M ψ₁ ψ₂ u := by
  simp only [AsumInvPos]
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

/-- `Asum v = AsumInv (1/v)` for `v ≠ 0`: the substitution `u = 1/v` turns `arg1` into the
argument `((m₃ u + m₁)/m₂)` of `AsumInv`. -/
theorem prop101_asum_eq_asuminv (N : ℕ) (W : Finset ℝ) (B M₁ M : ℝ) (ψ₁ ψ₂ : ℝ → ℝ)
    (hM : 1 ≤ M) {v : ℝ} (hv : v ≠ 0) :
    Asum N W B M₁ M ψ₁ ψ₂ v = AsumInv N W B M₁ M ψ₁ ψ₂ (1 / v) := by
  simp only [Asum, AsumInv, arg1]
  apply Finset.sum_congr rfl; intro m₁ _
  apply Finset.sum_congr rfl; intro m₂ hm₂
  apply Finset.sum_congr rfl; intro m₃ _
  congr 1
  have hm2ne : ((m₂ : ℤ) : ℝ) ≠ 0 := by
    have h := (mem_filter.mp hm₂).2
    intro h0
    rw [h0] at h
    simp at h
    linarith
  field_simp
  ring_nf

/-- `AsumInv = 2 · AsumInvPos`: the reflection `(m₁,m₂,m₃) ↦ (-m₁,-m₂,-m₃)` preserves the
argument `((m₃ u + m₁)/m₂)` and exchanges the two halves of the `m₂`-sum. -/
theorem prop101_asuminv_eq_two_mul (N : ℕ) (W : Finset ℝ) (B M₁ M : ℝ) (ψ₁ ψ₂ : ℝ → ℝ)
    (hM : 1 ≤ M) (u : ℝ) :
    AsumInv N W B M₁ M ψ₁ ψ₂ u = 2 * AsumInvPos N W B M₁ M ψ₁ ψ₂ u := by
  have hF : ∀ m₁ m₂ m₃ : ℤ,
      Rtilde W N B ψ₁ ψ₂ ((((-m₃ : ℤ) : ℝ) * u + ((-m₁ : ℤ) : ℝ)) / ((-m₂ : ℤ) : ℝ)) ^ 2
        = Rtilde W N B ψ₁ ψ₂ (((m₃ : ℝ) * u + (m₁ : ℝ)) / (m₂ : ℝ)) ^ 2 := by
    intro m₁ m₂ m₃
    have ha : ((((-m₃ : ℤ) : ℝ) * u + ((-m₁ : ℤ) : ℝ)) / ((-m₂ : ℤ) : ℝ))
        = (((m₃ : ℝ) * u + (m₁ : ℝ)) / (m₂ : ℝ)) := by
      simp only [Int.cast_neg]; ring_nf
    rw [ha]
  simpa only [AsumInv, AsumInvPos] using
    sum_triple_reflect M₁ M
      (fun m₁ m₂ m₃ : ℤ =>
        Rtilde W N B ψ₁ ψ₂ (((m₃ : ℝ) * u + (m₁ : ℝ)) / (m₂ : ℝ)) ^ 2) hF hM

/-- Pointwise domination `AsumInvPos u ≤ affineSum 2 M M M₁ f u` with `f = testfun`, by
interchanging the roles of `m₁` and `m₃` in the index sets and using `R̃² ≤ f`. -/
theorem prop101_asuminvPos_le_affineSum (N : ℕ) (W : Finset ℝ) (B M₁ M : ℝ)
    (ψ₁ ψ₂ ψ' : ℝ → ℝ)
    (hB : 0 ≤ (N : ℝ) * B)
    (hψ₁ : IsBumpAtZero ψ₁ 16) (hψ₂ : IsBumpAtOne ψ₂ 16) (hψ' : IsBumpAtOne ψ' 16)
    (hψ'one : ∀ x ∈ Set.Icc (1 / 8 : ℝ) (33 / 8), ψ' x = 1)
    (hRsupp : ∀ x, RtildeSq W N B ψ₁ ψ₂ x ≠ 0 → x ∈ Set.Icc (1 / 8 : ℝ) (33 / 8))
    (u : ℝ) :
    AsumInvPos N W B M₁ M ψ₁ ψ₂ u ≤
      affineSum 2 M M M₁ (testfun N W B ψ₁ ψ₂ ψ') u := by
  have hRnn : ∀ x, 0 ≤ RtildeSq W N B ψ₁ ψ₂ x := fun x =>
    integral_nonneg fun u' =>
      mul_nonneg (mul_nonneg (mul_nonneg hB (hψ₁.2.1 _)) (hψ₂.2.1 u')) (sq_nonneg _)
  have hpt : ∀ x, Rtilde W N B ψ₁ ψ₂ x ^ 2 = testfun N W B ψ₁ ψ₂ ψ' x := by
    intro x
    rw [Rtilde_sq W N B ψ₁ ψ₂ x (hRnn x)]
    simp only [testfun]
    by_cases hx : RtildeSq W N B ψ₁ ψ₂ x = 0
    · simp [hx]
    · simp [hψ'one x (hRsupp x hx)]
  have htestfun_nn : ∀ x, 0 ≤ testfun N W B ψ₁ ψ₂ ψ' x :=
    fun x => mul_nonneg (hψ'.2.1 x) (hRnn x)
  have hL1 : AsumInvPos N W B M₁ M ψ₁ ψ₂ u =
      ∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxMpos M, ∑ m₃ ∈ idxM M,
        testfun N W B ψ₁ ψ₂ ψ' (((m₃ : ℝ) * u + (m₁ : ℝ)) / (m₂ : ℝ)) := by
    simp only [AsumInvPos]
    apply Finset.sum_congr rfl; intro m₁ _
    apply Finset.sum_congr rfl; intro m₂ _
    apply Finset.sum_congr rfl; intro m₃ _
    exact hpt _
  have hL2 : (∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxMpos M, ∑ m₃ ∈ idxM M,
        testfun N W B ψ₁ ψ₂ ψ' (((m₃ : ℝ) * u + (m₁ : ℝ)) / (m₂ : ℝ)))
      = ∑ m₃ ∈ idxM M, ∑ m₂ ∈ idxMpos M, ∑ m₁ ∈ idx1 M₁,
        testfun N W B ψ₁ ψ₂ ψ' (((m₃ : ℝ) * u + (m₁ : ℝ)) / (m₂ : ℝ)) := by
    conv_lhs => enter [2, x]; rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]
    conv_lhs => enter [2, x]; rw [Finset.sum_comm]
  have hL := hL1.trans hL2
  have hR : affineSum 2 M M M₁ (testfun N W B ψ₁ ψ₂ ψ') u =
      ∑ m₃ ∈ idxM M, ∑ m₂ ∈ idxMpos M, ∑ m₁ ∈ Finset.Icc (-⌊2 * M₁⌋) ⌊2 * M₁⌋,
        testfun N W B ψ₁ ψ₂ ψ' (((m₃ : ℝ) * u + (m₁ : ℝ)) / (m₂ : ℝ)) := by
    simp only [affineSum, idxM, idxMpos]
  rw [hL, hR]
  refine Finset.sum_le_sum (fun c _ => Finset.sum_le_sum (fun b _ => ?_))
  rw [idx1]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun a _ _ => htestfun_nn _)

/-- Compact support of `u ↦ affineSum 2 M M M₁ (testfun N W B ψ₁ ψ₂ ψ') u`: any nonzero summand
forces `(m₁ u + m₃)/m₂ ∈ [1/8, 33/8]`, whence `|u| ≤ |m₁ u| ≤ (33/8)·2M + 2M₁ = 33M/4 + 2M₁`
(using `|m₁| ≥ 1`, `|m₂| ≤ 2M`, `|m₃| ≤ 2M₁`). -/
theorem prop101_affineSum_hasCompactSupport (N : ℕ) (W : Finset ℝ) (B M₁ M : ℝ)
    (ψ₁ ψ₂ ψ' : ℝ → ℝ) (hM : 1 ≤ M)
    (hRsupp : ∀ x, RtildeSq W N B ψ₁ ψ₂ x ≠ 0 → x ∈ Set.Icc (1 / 8 : ℝ) (33 / 8)) :
    HasCompactSupport (fun u => affineSum 2 M M M₁ (testfun N W B ψ₁ ψ₂ ψ') u) := by
  refine HasCompactSupport.intro
    (K := Set.Icc (-(33 / 4 * M + 2 * M₁)) (33 / 4 * M + 2 * M₁)) isCompact_Icc
    (fun u hu => ?_)
  simp only [affineSum]
  refine Finset.sum_eq_zero (fun m₁ hm₁ => ?_)
  refine Finset.sum_eq_zero (fun m₂ hm₂ => ?_)
  refine Finset.sum_eq_zero (fun m₃ hm₃ => ?_)
  refine testfun_eq_zero_of_notMem_support N W B ψ₁ ψ₂ ψ' hRsupp (fun hx => hu ?_)
  have hm1abs : (1 : ℝ) ≤ |(m₁ : ℝ)| := by
    have h := (mem_filter.mp hm₁).2
    have : (1 : ℝ) < |(m₁ : ℝ)| := lt_of_le_of_lt hM h
    linarith
  have hm2ge1 : (1 : ℝ) ≤ (m₂ : ℝ) := by
    have h := (mem_Icc.mp (mem_filter.mp hm₂).1).1
    exact_mod_cast h
  have hm2pos : (0 : ℝ) < (m₂ : ℝ) := by linarith
  have hm2le : (m₂ : ℝ) ≤ 2 * M := by
    have h := (mem_Icc.mp (mem_filter.mp hm₂).1).2
    calc (m₂ : ℝ) ≤ (⌊2 * M⌋ : ℝ) := by exact_mod_cast h
      _ ≤ 2 * M := Int.floor_le _
  have hm3le : |(m₃ : ℝ)| ≤ 2 * M₁ := by
    have h := mem_Icc.mp hm₃
    have h1' : (-(⌊2 * M₁⌋ : ℝ)) ≤ (m₃ : ℝ) := by exact_mod_cast h.1
    have h2' : (m₃ : ℝ) ≤ (⌊2 * M₁⌋ : ℝ) := by exact_mod_cast h.2
    have hf : (⌊2 * M₁⌋ : ℝ) ≤ 2 * M₁ := Int.floor_le _
    rw [abs_le]; exact ⟨by linarith, by linarith⟩
  have hxabs : |((↑m₁ * u + ↑m₃) / ↑m₂)| ≤ 33 / 8 := by
    rw [abs_le]; exact ⟨by linarith [hx.1], hx.2⟩
  have hkey : |(m₁ : ℝ) * u| ≤ 33 / 4 * M + 2 * M₁ := by
    have hane : (m₂ : ℝ) ≠ 0 := ne_of_gt hm2pos
    have heq : (m₁ : ℝ) * u = ((↑m₁ * u + ↑m₃) / ↑m₂) * ↑m₂ - ↑m₃ := by
      rw [div_mul_cancel₀ _ hane]; ring
    rw [heq]
    calc |((↑m₁ * u + ↑m₃) / ↑m₂) * ↑m₂ - ↑m₃|
        ≤ |((↑m₁ * u + ↑m₃) / ↑m₂) * ↑m₂| + |↑m₃| := abs_sub _ _
      _ = |((↑m₁ * u + ↑m₃) / ↑m₂)| * |↑m₂| + |↑m₃| := by rw [abs_mul]
      _ ≤ (33 / 8) * (2 * M) + 2 * M₁ := by
          have h2 : |((↑m₁ * u + ↑m₃) / ↑m₂)| * |↑m₂| ≤ (33 / 8) * (2 * M) := by
            rw [abs_of_pos hm2pos]
            exact mul_le_mul hxabs hm2le (le_of_lt hm2pos) (by norm_num)
          linarith
      _ ≤ 33 / 4 * M + 2 * M₁ := by linarith
  have hu' : |u| ≤ 33 / 4 * M + 2 * M₁ := by
    have h1 : |(m₁ : ℝ) * u| = |(m₁ : ℝ)| * |u| := abs_mul _ _
    have h2 : |u| ≤ |(m₁ : ℝ)| * |u| := by
      have h3 : (0 : ℝ) ≤ |u| := abs_nonneg u
      nlinarith [hm1abs, h3]
    linarith [h1 ▸ hkey]
  exact abs_le.mp hu'

/-- **GM 10.1, recognition of `S₃,₃` as an `affineSum` integral** (after `u = 1/v` the `u`-coefficient of the argument is `m₃ ∈ idxM M`, so the dominating sum is `affineSum 2 M M M₁`).  `S₃,₃ = ∫_{1/2}^{2}(Σ_m R̃(a₁(m,v))²)² dv` with `a₁ = (m₁v+m₃)/(m₂v)`; the reflection `(m₁,m₂,m₃) ↦ (-m₁,-m₂,-m₃)` doubles the `m₂>0` part, the substitution `u = 1/v` turns `a₁` into `(m₃u+m₁)/m₂` and costs `1/u² ≤ 4`, and `R̃² = RtildeSq ≤ testfun` pointwise, so `S₃,₃ ≤ 16 ∫_ℝ (affineSum 2 M M M₁ (testfun N W B ψ₁ ψ₂ ψ') u)² du`. -/
theorem prop101_S33_le_affine (N : ℕ) (W : Finset ℝ) (B M₁ M : ℝ) (ψ₁ ψ₂ ψ' : ℝ → ℝ)
    (hB : 0 ≤ (N : ℝ) * B) (hM₁ : 1 ≤ M₁) (hM : 1 ≤ M)
    (hψ₁ : IsBumpAtZero ψ₁ 16) (hψ₂ : IsBumpAtOne ψ₂ 16) (hψ' : IsBumpAtOne ψ' 16)
    (hψ'one : ∀ x ∈ Set.Icc (1 / 8 : ℝ) (33 / 8), ψ' x = 1)
    (hRsupp : ∀ x, RtildeSq W N B ψ₁ ψ₂ x ≠ 0 → x ∈ Set.Icc (1 / 8 : ℝ) (33 / 8)) :
    S33 N W B M₁ M ψ₁ ψ₂ ≤
      16 * ∫ u, (Submission.GM.affineSum 2 M M M₁ (testfun N W B ψ₁ ψ₂ ψ') u) ^ 2 := by
  have hAInv_cont : Continuous (fun u => AsumInv N W B M₁ M ψ₁ ψ₂ u) :=
    prop101_continuous_asumInv N W B M₁ M ψ₁ ψ₂ hψ₁ hψ₂ hM
  have hAInvPos_cont : Continuous (fun u => AsumInvPos N W B M₁ M ψ₁ ψ₂ u) :=
    prop101_continuous_asumInvPos N W B M₁ M ψ₁ ψ₂ hψ₁ hψ₂
  have htest_cont : Continuous (fun u => testfun N W B ψ₁ ψ₂ ψ' u) := by
    simp only [testfun]
    exact hψ'.1.continuous.mul (RtildeSq_continuous W N B 16 ψ₁ ψ₂ hψ₁ hψ₂)
  have hG_cont : Continuous
      (fun u => affineSum 2 M M M₁ (testfun N W B ψ₁ ψ₂ ψ') u) :=
    prop101_continuous_affineSum 2 M M M₁ (testfun N W B ψ₁ ψ₂ ψ') htest_cont
  have hG_cs : HasCompactSupport
      (fun u => affineSum 2 M M M₁ (testfun N W B ψ₁ ψ₂ ψ') u) :=
    prop101_affineSum_hasCompactSupport N W B M₁ M ψ₁ ψ₂ ψ' hM hRsupp
  have hG_cs2 : HasCompactSupport
      (fun u => (affineSum 2 M M M₁ (testfun N W B ψ₁ ψ₂ ψ') u) ^ 2) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hG_cs ⊢
    filter_upwards [hG_cs] with u hu
    simp [hu]
  have hG_int : Integrable
      (fun u => (affineSum 2 M M M₁ (testfun N W B ψ₁ ψ₂ ψ') u) ^ 2) volume :=
    (hG_cont.pow 2).integrable_of_hasCompactSupport hG_cs2
  -- (i) `Asum v = AsumInv (1/v)`
  have hstep1 : S33 N W B M₁ M ψ₁ ψ₂ =
      ∫ v in (1 / 2 : ℝ)..2, (AsumInv N W B M₁ M ψ₁ ψ₂ (1 / v)) ^ 2 := by
    rw [S33]
    apply intervalIntegral.integral_congr
    intro v hv
    have hv' : v ∈ Set.Icc (1 / 2 : ℝ) 2 := by
      rwa [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at hv
    have hv0 : v ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hv'.1)
    dsimp only
    rw [prop101_asum_eq_asuminv N W B M₁ M ψ₁ ψ₂ hM hv0]
  -- (ii) the substitution `u = 1/v` on `[1/2,2]`
  have hstep2 : (∫ v in (1 / 2 : ℝ)..2, (AsumInv N W B M₁ M ψ₁ ψ₂ (1 / v)) ^ 2) =
      ∫ u in (1 / 2 : ℝ)..2, (AsumInv N W B M₁ M ψ₁ ψ₂ u) ^ 2 / u ^ 2 :=
    integral_comp_inv (K := fun u => (AsumInv N W B M₁ M ψ₁ ψ₂ u) ^ 2)
      (hAInv_cont.pow 2).continuousOn
  -- (iii) `1/u² ≤ 4` on `[1/2,2]`
  have hstep3 : (∫ u in (1 / 2 : ℝ)..2, (AsumInv N W B M₁ M ψ₁ ψ₂ u) ^ 2 / u ^ 2) ≤
      4 * ∫ u in (1 / 2 : ℝ)..2, (AsumInv N W B M₁ M ψ₁ ψ₂ u) ^ 2 := by
    have hmono : (∫ u in (1 / 2 : ℝ)..2, (AsumInv N W B M₁ M ψ₁ ψ₂ u) ^ 2 / u ^ 2) ≤
        ∫ u in (1 / 2 : ℝ)..2, 4 * (AsumInv N W B M₁ M ψ₁ ψ₂ u) ^ 2 := by
      refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ (fun u hu => ?_)
      · refine (((hAInv_cont.pow 2).continuousOn).div (continuousOn_id.pow 2) ?_).intervalIntegrable
        intro u hu
        have hu' : u ∈ Set.Icc (1 / 2 : ℝ) 2 := by
          rwa [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at hu
        have : (0 : ℝ) < u := lt_of_lt_of_le (by norm_num) hu'.1
        exact pow_ne_zero 2 (ne_of_gt this)
      · exact ((hAInv_cont.pow 2).const_mul 4).intervalIntegrable _ _
      · rw [div_eq_mul_inv]
        have hquarter : (1 : ℝ) / 4 ≤ u ^ 2 := by nlinarith [hu.1]
        have hinv : (u ^ 2)⁻¹ ≤ 4 := by
          simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 4) hquarter
        calc (AsumInv N W B M₁ M ψ₁ ψ₂ u) ^ 2 * (u ^ 2)⁻¹
            ≤ (AsumInv N W B M₁ M ψ₁ ψ₂ u) ^ 2 * 4 :=
              mul_le_mul_of_nonneg_left hinv (sq_nonneg _)
          _ = 4 * (AsumInv N W B M₁ M ψ₁ ψ₂ u) ^ 2 := by ring
    rwa [intervalIntegral.integral_const_mul] at hmono
  -- (iv) `AsumInv = 2 · AsumInvPos`
  have hstep4 : (∫ u in (1 / 2 : ℝ)..2, (AsumInv N W B M₁ M ψ₁ ψ₂ u) ^ 2) =
      4 * ∫ u in (1 / 2 : ℝ)..2, (AsumInvPos N W B M₁ M ψ₁ ψ₂ u) ^ 2 := by
    have heq : (fun u => (AsumInv N W B M₁ M ψ₁ ψ₂ u) ^ 2)
        = fun u => 4 * (AsumInvPos N W B M₁ M ψ₁ ψ₂ u) ^ 2 := by
      funext u
      rw [prop101_asuminv_eq_two_mul N W B M₁ M ψ₁ ψ₂ hM u]; ring
    rw [heq, intervalIntegral.integral_const_mul]
  -- (v) `AsumInvPos ≤ affineSum`
  have hstep5 : (∫ u in (1 / 2 : ℝ)..2, (AsumInvPos N W B M₁ M ψ₁ ψ₂ u) ^ 2) ≤
      ∫ u in (1 / 2 : ℝ)..2, (affineSum 2 M M M₁ (testfun N W B ψ₁ ψ₂ ψ') u) ^ 2 := by
    refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ (fun u _ => ?_)
    · exact (hAInvPos_cont.pow 2).intervalIntegrable _ _
    · exact (hG_cont.pow 2).intervalIntegrable _ _
    · exact pow_le_pow_left₀ (prop101_asumInvPos_nonneg N W B M₁ M ψ₁ ψ₂ u)
        (prop101_asuminvPos_le_affineSum N W B M₁ M ψ₁ ψ₂ ψ' hB hψ₁ hψ₂ hψ' hψ'one
          hRsupp u) 2
  -- (vi) extend `[1/2,2]` to `ℝ`
  have hstep6 : (∫ u in (1 / 2 : ℝ)..2,
        (affineSum 2 M M M₁ (testfun N W B ψ₁ ψ₂ ψ') u) ^ 2) ≤
      ∫ u, (affineSum 2 M M M₁ (testfun N W B ψ₁ ψ₂ ψ') u) ^ 2 := by
    rw [intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)]
    exact setIntegral_le_integral hG_int (Filter.Eventually.of_forall (fun u => sq_nonneg _))
  calc S33 N W B M₁ M ψ₁ ψ₂
      = ∫ v in (1 / 2 : ℝ)..2, (AsumInv N W B M₁ M ψ₁ ψ₂ (1 / v)) ^ 2 := hstep1
    _ = ∫ u in (1 / 2 : ℝ)..2, (AsumInv N W B M₁ M ψ₁ ψ₂ u) ^ 2 / u ^ 2 := hstep2
    _ ≤ 4 * ∫ u in (1 / 2 : ℝ)..2, (AsumInv N W B M₁ M ψ₁ ψ₂ u) ^ 2 := hstep3
    _ = 4 * (4 * ∫ u in (1 / 2 : ℝ)..2, (AsumInvPos N W B M₁ M ψ₁ ψ₂ u) ^ 2) := by rw [hstep4]
    _ = 16 * ∫ u in (1 / 2 : ℝ)..2, (AsumInvPos N W B M₁ M ψ₁ ψ₂ u) ^ 2 := by ring
    _ ≤ 16 * ∫ u in (1 / 2 : ℝ)..2,
          (affineSum 2 M M M₁ (testfun N W B ψ₁ ψ₂ ψ') u) ^ 2 := by linarith [hstep5]
    _ ≤ 16 * ∫ u, (affineSum 2 M M M₁ (testfun N W B ψ₁ ψ₂ ψ') u) ^ 2 := by linarith [hstep6]

end Work.GM.S3
