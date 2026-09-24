import Mathlib
import Submission.Work.GM.S3.Defs
import Submission.Work.GM.S3.prop101_defs
import Submission.Work.GM.S3.RtildeSq_continuous
import Submission.Work.GM.S3.RtildeSq_eq_zero_of_notMem
import Submission.Work.GM.S3.bsum_reflect
import Submission.Work.GM.S3.bsumPos_le_affineSum

namespace Work.GM.S3

open Complex Finset MeasureTheory
open scoped BigOperators
open Submission.GM (Rfun affineSum)

/-- The support of the test function `f = testfun N W B ψ₁ ψ₂ ψ'`: `ψ' = 1` (and `RtildeSq` is
allowed to be nonzero) only inside `[1/8, 33/8]`, by `hψ'one`/`hRsupp`. -/
theorem testfun_eq_zero_of_notMem_support (N : ℕ) (W : Finset ℝ) (B : ℝ) (ψ₁ ψ₂ ψ' : ℝ → ℝ)
    (hRsupp : ∀ x, RtildeSq W N B ψ₁ ψ₂ x ≠ 0 → x ∈ Set.Icc (1 / 8 : ℝ) (33 / 8))
    {x : ℝ} (hx : x ∉ Set.Icc (1 / 8 : ℝ) (33 / 8)) :
    testfun N W B ψ₁ ψ₂ ψ' x = 0 := by
  by_contra h
  have h2 : RtildeSq W N B ψ₁ ψ₂ x ≠ 0 :=
    fun h0 => h (by simp [testfun, h0])
  exact hx (hRsupp x h2)

/-- Continuity of `v ↦ BsumPos N W B M₁ M ψ₁ ψ₂ v` (a finite sum of squares of the continuous
function `Rtilde W N B ψ₁ ψ₂` composed with the affine maps `arg2 m₁ m₂ m₃`). -/
theorem continuous_BsumPos (N : ℕ) (W : Finset ℝ) (B M₁ M : ℝ) (ψ₁ ψ₂ : ℝ → ℝ)
    (hψ₁ : IsBumpAtZero ψ₁ 16) (hψ₂ : IsBumpAtOne ψ₂ 16) :
    Continuous (fun v => BsumPos N W B M₁ M ψ₁ ψ₂ v) := by
  have hRt : Continuous (fun x => RtildeSq W N B ψ₁ ψ₂ x) :=
    RtildeSq_continuous W N B 16 ψ₁ ψ₂ hψ₁ hψ₂
  have hRcont : Continuous (fun x => Rtilde W N B ψ₁ ψ₂ x) := by
    have h : (fun x => Rtilde W N B ψ₁ ψ₂ x)
        = fun x => Real.sqrt (RtildeSq W N B ψ₁ ψ₂ x) := rfl
    rw [h]; exact Real.continuous_sqrt.comp hRt
  simp only [BsumPos]
  refine continuous_finset_sum _ (fun m₁ _ => ?_)
  refine continuous_finset_sum _ (fun m₂ hm₂ => ?_)
  refine continuous_finset_sum _ (fun m₃ _ => ?_)
  have hm2 : (1 : ℤ) ≤ m₂ := (mem_Icc.mp (mem_filter.mp hm₂).1).1
  have hm2ne : ((m₂ : ℤ) : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast hm2
    linarith
  have harg : Continuous (fun v : ℝ => arg2 m₁ m₂ m₃ v) := by
    simp only [arg2]
    rw [show (fun v : ℝ => ((m₁ : ℝ) * v + (m₃ : ℝ)) / ((m₂ : ℝ)))
        = fun v => ((m₁ : ℝ) * v + (m₃ : ℝ)) * ((m₂ : ℝ))⁻¹ from by
      funext v; rw [div_eq_mul_inv]]
    fun_prop
  exact (hRcont.comp harg).pow 2

/-- Continuity of `u ↦ affineSum 2 M₁ M M (testfun N W B ψ₁ ψ₂ ψ') u`. -/
theorem continuous_affineSum_testfun (N : ℕ) (W : Finset ℝ) (B M₁ M : ℝ) (ψ₁ ψ₂ ψ' : ℝ → ℝ)
    (hψ₁ : IsBumpAtZero ψ₁ 16) (hψ₂ : IsBumpAtOne ψ₂ 16) (hψ' : IsBumpAtOne ψ' 16) :
    Continuous (fun u => affineSum 2 M₁ M M (testfun N W B ψ₁ ψ₂ ψ') u) := by
  have hRt : Continuous (fun x => RtildeSq W N B ψ₁ ψ₂ x) :=
    RtildeSq_continuous W N B 16 ψ₁ ψ₂ hψ₁ hψ₂
  have htest : Continuous (fun u => testfun N W B ψ₁ ψ₂ ψ' u) := by
    simp only [testfun]
    exact hψ'.1.continuous.mul hRt
  simp only [affineSum]
  refine continuous_finset_sum _ (fun m₁ _ => ?_)
  refine continuous_finset_sum _ (fun m₂ hm₂ => ?_)
  refine continuous_finset_sum _ (fun m₃ _ => ?_)
  have hm2 : (1 : ℤ) ≤ m₂ := (mem_Icc.mp (mem_filter.mp hm₂).1).1
  have hm2ne : ((m₂ : ℤ) : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast hm2
    linarith
  have harg : Continuous (fun u : ℝ => (((m₁ : ℝ) * u + (m₃ : ℝ)) / (m₂ : ℝ))) := by
    rw [show (fun u : ℝ => (((m₁ : ℝ) * u + (m₃ : ℝ)) / (m₂ : ℝ)))
        = fun u => (((m₁ : ℝ) * u + (m₃ : ℝ)) * ((m₂ : ℝ))⁻¹) from by
      funext u; rw [div_eq_mul_inv]]
    fun_prop
  exact htest.comp harg

/-- Compact support of `u ↦ affineSum 2 M₁ M M (testfun N W B ψ₁ ψ₂ ψ') u`: all its summands
vanish for `|u| > 11 M`.  Namely `m₁ ≠ 0` (as `M₁ ≥ 1`), `1 ≤ m₂ ≤ 2M` and `|m₃| ≤ 2M`; if
`testfun ((m₁u+m₃)/m₂) ≠ 0` then `(m₁u+m₃)/m₂ ∈ [1/8, 33/8]`, whence `|m₁u| ≤ (33/8)·2M + 2M < 11M`
and `|u| ≤ |m₁u| ≤ 11M`. -/
theorem affineSum_testfun_hasCompactSupport (N : ℕ) (W : Finset ℝ) (B M₁ M : ℝ)
    (ψ₁ ψ₂ ψ' : ℝ → ℝ) (hM₁ : 1 ≤ M₁)
    (hRsupp : ∀ x, RtildeSq W N B ψ₁ ψ₂ x ≠ 0 → x ∈ Set.Icc (1 / 8 : ℝ) (33 / 8)) :
    HasCompactSupport (fun u => affineSum 2 M₁ M M (testfun N W B ψ₁ ψ₂ ψ') u) := by
  refine HasCompactSupport.intro (K := Set.Icc (-(11 * M)) (11 * M)) isCompact_Icc (fun u hu => ?_)
  simp only [affineSum]
  refine Finset.sum_eq_zero (fun m₁ hm₁ => ?_)
  refine Finset.sum_eq_zero (fun m₂ hm₂ => ?_)
  refine Finset.sum_eq_zero (fun m₃ hm₃ => ?_)
  refine testfun_eq_zero_of_notMem_support N W B ψ₁ ψ₂ ψ' hRsupp (fun hx => ?_)
  have hm1abs : (1 : ℝ) ≤ |(m₁ : ℝ)| := by
    have := (mem_filter.mp hm₁).2; linarith
  have hm2mem : (1 : ℤ) ≤ m₂ := (mem_Icc.mp (mem_filter.mp hm₂).1).1
  have hm2pos : (0 : ℝ) < (m₂ : ℝ) := by
    have : (1 : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast hm2mem
    linarith
  have hm2le : (m₂ : ℝ) ≤ 2 * M := by
    have h := (mem_Icc.mp (mem_filter.mp hm₂).1).2
    calc (m₂ : ℝ) ≤ (⌊2 * M⌋ : ℝ) := by exact_mod_cast h
      _ ≤ 2 * M := Int.floor_le _
  have hm3le : |(m₃ : ℝ)| ≤ 2 * M := by
    have h := mem_Icc.mp hm₃
    have h1' : (-(⌊2 * M⌋ : ℝ)) ≤ (m₃ : ℝ) := by exact_mod_cast h.1
    have h2' : (m₃ : ℝ) ≤ (⌊2 * M⌋ : ℝ) := by exact_mod_cast h.2
    have hf : (⌊2 * M⌋ : ℝ) ≤ 2 * M := Int.floor_le _
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hmain : |(m₁ : ℝ) * u| ≤ 11 * M := by
    have hane : (m₂ : ℝ) ≠ 0 := ne_of_gt hm2pos
    have hxa : ((m₁ : ℝ) * u + (m₃ : ℝ)) =
        (((m₁ : ℝ) * u + (m₃ : ℝ)) / (m₂ : ℝ)) * (m₂ : ℝ) :=
      (div_mul_cancel₀ _ hane).symm
    have hb : (m₁ : ℝ) * u =
        (((m₁ : ℝ) * u + (m₃ : ℝ)) / (m₂ : ℝ)) * (m₂ : ℝ) - (m₃ : ℝ) := by
      rw [← hxa]; ring
    rw [hb]
    have hxabs : |(((m₁ : ℝ) * u + (m₃ : ℝ)) / (m₂ : ℝ))| ≤ 33 / 8 := by
      rw [abs_le]; exact ⟨by linarith [hx.1], hx.2⟩
    have h2abs : |(m₂ : ℝ)| = (m₂ : ℝ) := abs_of_pos hm2pos
    calc |(((m₁ : ℝ) * u + (m₃ : ℝ)) / (m₂ : ℝ)) * (m₂ : ℝ) - (m₃ : ℝ)|
        ≤ |(((m₁ : ℝ) * u + (m₃ : ℝ)) / (m₂ : ℝ)) * (m₂ : ℝ)| + |(m₃ : ℝ)| := abs_sub _ _
      _ = |(((m₁ : ℝ) * u + (m₃ : ℝ)) / (m₂ : ℝ))| * |(m₂ : ℝ)| + |(m₃ : ℝ)| := by rw [abs_mul]
      _ ≤ (33 / 8) * (2 * M) + 2 * M := by
          have h4 : |(((m₁ : ℝ) * u + (m₃ : ℝ)) / (m₂ : ℝ))| * |(m₂ : ℝ)| ≤ (33 / 8) * (2 * M) := by
            rw [h2abs]
            exact mul_le_mul hxabs hm2le (le_of_lt hm2pos) (by norm_num)
          linarith
      _ ≤ 11 * M := by linarith
  have hu' : u ∈ Set.Icc (-(11 * M)) (11 * M) := by
    have habs : |u| ≤ 11 * M := by
      have h1 : |(m₁ : ℝ) * u| = |(m₁ : ℝ)| * |u| := abs_mul _ _
      have h2 : |u| ≤ |(m₁ : ℝ)| * |u| := by
        have h3 : (0 : ℝ) ≤ |u| := abs_nonneg u
        nlinarith [hm1abs, h3]
      linarith [h1 ▸ hmain]
    rw [abs_le] at habs
    exact habs
  exact hu hu'

/-- **GM 10.1, reduction of `S₃,₄` to an affine sum.**  With `f = testfun N W B ψ₁ ψ₂ ψ'` (i.e.
`f u = ψ' u * RtildeSq W N B ψ₁ ψ₂ u`), and `Rtilde² = RtildeSq`,

`S₃,₄ = ∫_{1/2}^2 (Σ_m R̃(a₂(m,v))²)² dv ≤ 4 ∫_ℝ (affineSum 2 M₁ M M f)²`.

Proof: (i) `Bsum = 2·BsumPos` because `(m₁,m₂,m₃) ↦ (-m₁,-m₂,-m₃)` is a bijection from the
`m₂ < 0` part of the index set to the `m₂ > 0` part (`idxMpos M`) preserving `a₂`, and the index
sets are symmetric under negation; (ii) `idxMpos M = (idxM M).filter (0 < ·)` for `1 ≤ M`;
(iii) on the support of `RtildeSq` one has `ψ' = 1` (from `hψ'one` and `hRsupp`), so
`RtildeSq ≤ f` pointwise, and the index set of `BsumPos` is contained in that of `affineSum`
(the `m₃`-range `Icc (-⌊2M⌋) ⌊2M⌋` is *larger* than `idxM M`, and all terms are non-negative), so
`BsumPos v ≤ affineSum 2 M₁ M M f v` for every `v`; (iv) `[1/2,2] ⊆ ℝ` and the integrand is
non-negative. -/
theorem S34_le_affine (N : ℕ) (W : Finset ℝ) (B M₁ M : ℝ) (ψ₁ ψ₂ ψ' : ℝ → ℝ)
    (hB : 0 ≤ (N : ℝ) * B) (hM₁ : 1 ≤ M₁) (hM : 1 ≤ M)
    (hψ₁ : IsBumpAtZero ψ₁ 16) (hψ₂ : IsBumpAtOne ψ₂ 16) (hψ' : IsBumpAtOne ψ' 16)
    (hψ'one : ∀ x ∈ Set.Icc (1 / 8 : ℝ) (33 / 8), ψ' x = 1)
    (hRsupp : ∀ x, RtildeSq W N B ψ₁ ψ₂ x ≠ 0 → x ∈ Set.Icc (1 / 8 : ℝ) (33 / 8)) :
    S34 N W B M₁ M ψ₁ ψ₂ ≤
      4 * ∫ u, (Submission.GM.affineSum 2 M₁ M M (testfun N W B ψ₁ ψ₂ ψ') u) ^ 2 := by
  -- Step 0: the objects
  have hReflect : ∀ v, Bsum N W B M₁ M ψ₁ ψ₂ v = 2 * BsumPos N W B M₁ M ψ₁ ψ₂ v :=
    fun v => bsum_reflect N W B M₁ M ψ₁ ψ₂ hM v
  have hPoint : ∀ v, BsumPos N W B M₁ M ψ₁ ψ₂ v ≤
      affineSum 2 M₁ M M (testfun N W B ψ₁ ψ₂ ψ') v :=
    fun v => bsumPos_le_affineSum N W B M₁ M ψ₁ ψ₂ ψ' hB hψ₁ hψ₂ hψ' hψ'one hRsupp v
  have hPcont : Continuous (fun v => BsumPos N W B M₁ M ψ₁ ψ₂ v) :=
    continuous_BsumPos N W B M₁ M ψ₁ ψ₂ hψ₁ hψ₂
  have hGcont : Continuous (fun u => affineSum 2 M₁ M M (testfun N W B ψ₁ ψ₂ ψ') u) :=
    continuous_affineSum_testfun N W B M₁ M ψ₁ ψ₂ ψ' hψ₁ hψ₂ hψ'
  have hGcs : HasCompactSupport (fun u => affineSum 2 M₁ M M (testfun N W B ψ₁ ψ₂ ψ') u) :=
    affineSum_testfun_hasCompactSupport N W B M₁ M ψ₁ ψ₂ ψ' hM₁ hRsupp
  have hGcs2 : HasCompactSupport (fun u =>
      (affineSum 2 M₁ M M (testfun N W B ψ₁ ψ₂ ψ') u) ^ 2) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hGcs ⊢
    filter_upwards [hGcs] with u hu
    simp [hu]
  have hGint : Integrable (fun u =>
      (affineSum 2 M₁ M M (testfun N W B ψ₁ ψ₂ ψ') u) ^ 2) volume :=
    (hGcont.pow 2).integrable_of_hasCompactSupport hGcs2
  have hPnneg : ∀ v, 0 ≤ BsumPos N W B M₁ M ψ₁ ψ₂ v := by
    intro v
    simp only [BsumPos]
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      Finset.sum_nonneg (fun k _ => sq_nonneg _)))
  -- Step 1: `S₃,₄ = 4 ∫_{1/2}^2 (BsumPos v)² dv`
  have h1 : S34 N W B M₁ M ψ₁ ψ₂ =
      4 * ∫ v in (1 / 2 : ℝ)..2, (BsumPos N W B M₁ M ψ₁ ψ₂ v) ^ 2 := by
    rw [S34]
    have heq : (fun v => (Bsum N W B M₁ M ψ₁ ψ₂ v) ^ 2)
        = fun v => 4 * (BsumPos N W B M₁ M ψ₁ ψ₂ v) ^ 2 := by
      funext v; rw [hReflect v]; ring
    rw [heq, intervalIntegral.integral_const_mul]
  -- Step 2: `∫_{1/2}^2 (BsumPos)² ≤ ∫_ℝ (affineSum f)²`
  have h2 : ∫ v in (1 / 2 : ℝ)..2, (BsumPos N W B M₁ M ψ₁ ψ₂ v) ^ 2 ≤
      ∫ u, (affineSum 2 M₁ M M (testfun N W B ψ₁ ψ₂ ψ') u) ^ 2 := by
    have hmono : ∫ v in (1 / 2 : ℝ)..2, (BsumPos N W B M₁ M ψ₁ ψ₂ v) ^ 2 ≤
        ∫ v in (1 / 2 : ℝ)..2, (affineSum 2 M₁ M M (testfun N W B ψ₁ ψ₂ ψ') v) ^ 2 := by
      refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ (fun v _ => ?_)
      · exact (hPcont.pow 2).intervalIntegrable _ _
      · exact (hGcont.pow 2).intervalIntegrable _ _
      · exact pow_le_pow_left₀ (hPnneg v) (hPoint v) 2
    have hle : ∫ v in (1 / 2 : ℝ)..2, (affineSum 2 M₁ M M (testfun N W B ψ₁ ψ₂ ψ') v) ^ 2 ≤
        ∫ u, (affineSum 2 M₁ M M (testfun N W B ψ₁ ψ₂ ψ') u) ^ 2 := by
      rw [intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)]
      exact setIntegral_le_integral hGint
        (Filter.Eventually.of_forall (fun u => sq_nonneg _))
    linarith
  rw [h1]
  linarith

end Work.GM.S3
