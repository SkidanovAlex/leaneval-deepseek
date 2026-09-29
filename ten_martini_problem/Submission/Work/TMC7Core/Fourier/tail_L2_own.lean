import Mathlib
import Submission.Work.TMC7Core.Fourier.ldt_setup
import Submission.Work.TMC7Core.Fourier.tail_L2_aux
import Submission.Work.TMC7Core.Fourier.mave_coeff2
import Submission.Work.TMC7Core.Fourier.tail_sum2
import Submission.Work.TMC7Core.Fourier.finset_fourier_coeff

/-!
# TMC7Core: the L² bound on the exponential tail of the moving average (own copy)

For `g` a `1`-periodic `L²` function with Fourier coefficients decaying like `1/|k|`, the moving
average `mAve g α R` differs from its low frequencies `|k| ≤ K` (weighted by the Fejér kernel)
by at most `2/K` in `L²(0,1)`.

The proof passes to the additive circle `AddCircle 1`, where `mAve g α R` becomes the finite sum
`R⁻² ∑_{j,j'} G(· + (j-j')α)` with Fourier coefficients `fourierCoeff G m * fejerKer R (m α)`
(`mave_coeff`).  Subtracting the frequencies `|m| ≤ K` kills those coefficients, so Parseval
identifies the `L²` norm with `∑_{|m|>K} ‖fourierCoeff G m‖² fejerKer R (m α)²`, which is bounded
by `∑_{|m|>K} 1/m² ≤ 2/K` (`tail_sum`).
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC7Core.Fourier

theorem tail_L2b (g : ℝ → ℂ) (hg : ∀ x, g (x + 1) = g x) (α : ℝ) (R : ℕ) (hR : 1 ≤ R) (K : ℕ)
    (hK : 0 < K) (hg2 : MeasureTheory.MemLp g 2 (MeasureTheory.volume.restrict (Set.Ioc 0 1)))
    (hdec : ∀ k : ℤ, k ≠ 0 → ‖fourierCoeffOn (by norm_num : (0:ℝ) < 1) g k‖ ≤ 1 / |(k:ℝ)|) :
    ∫ x in (0:ℝ)..1, ‖mAve g α R x - (fourierCoeffOn (by norm_num : (0:ℝ) < 1) g 0)
        - (∑ k ∈ (Finset.Icc (-(K:ℤ)) (K:ℤ)).filter (fun k => k ≠ 0),
            (fourierCoeffOn (by norm_num : (0:ℝ) < 1) g k) * (fejerKer R ((k:ℝ)*α) : ℂ)
              * Complex.exp (2*Real.pi*Complex.I*(k:ℝ)*x))‖ ^ 2
      ≤ 2 / (K:ℝ) := by
  haveI : Fact (0 < (1:ℝ)) := ⟨by norm_num⟩
  have hgper : Function.Periodic g 1 := hg
  set G : AddCircle (1:ℝ) → ℂ := hgper.lift with hGdef
  have hG2 : MemLp G 2 (AddCircle.haarAddCircle) := by
    rw [hGdef]; exact memLp_lift g hgper hg2
  have hGint : Integrable G AddCircle.haarAddCircle := hG2.integrable (by norm_num)
  set S : Finset ℤ := Finset.Icc (-(K:ℤ)) (K:ℤ) with hSdef
  set a : ℤ → ℂ := fun k => (fourierCoeffOn (by norm_num : (0:ℝ) < 1) g k) * (fejerKer R ((k:ℝ)*α) : ℂ) with hadef
  set M : AddCircle (1:ℝ) → ℂ := fun t => ((R:ℂ)^2)⁻¹ * ∑ j ∈ Finset.range R, ∑ j' ∈ Finset.range R,
      G (t + ((((j:ℝ) - (j':ℝ)) * α : ℝ) : AddCircle (1:ℝ))) with hMdef
  set B : AddCircle (1:ℝ) → ℂ := fun t => ∑ k ∈ S, a k * fourier k t with hBdef
  set FF : AddCircle (1:ℝ) → ℂ := M - B with hFFdef
  have htr : ∀ c : ℝ, MemLp (fun t : AddCircle (1:ℝ) => G (t + (c : AddCircle (1:ℝ)))) 2 (AddCircle.haarAddCircle) := by
    intro c
    have hmp : MeasurePreserving (fun t : AddCircle (1:ℝ) => t + (c : AddCircle (1:ℝ)))
        AddCircle.haarAddCircle AddCircle.haarAddCircle :=
      MeasureTheory.MeasurePreserving.add_right AddCircle.haarAddCircle (c : AddCircle (1:ℝ))
        (MeasurePreserving.id AddCircle.haarAddCircle)
    exact hG2.comp_measurePreserving hmp
  have hM2 : MemLp M 2 (AddCircle.haarAddCircle) := by
    rw [hMdef]
    refine MemLp.const_mul ?_ _
    refine MeasureTheory.memLp_finsetSum _ (fun j _ => ?_)
    refine MeasureTheory.memLp_finsetSum _ (fun j' _ => ?_)
    exact htr _
  have hB2 : MemLp B 2 (AddCircle.haarAddCircle) := by
    rw [hBdef]
    refine MeasureTheory.memLp_finsetSum _ (fun k _ => ?_)
    refine MemLp.of_bound ?_ ‖a k‖ ?_
    · exact (continuous_const.mul (map_continuous (fourier k))).aestronglyMeasurable
    · filter_upwards with t
      rw [norm_mul, show ‖fourier k t‖ = 1 from by rw [fourier_apply]; exact Circle.norm_coe _, mul_one]
  have hMint : Integrable M AddCircle.haarAddCircle := hM2.integrable (by norm_num)
  have hBint : Integrable B AddCircle.haarAddCircle := hB2.integrable (by norm_num)
  have hMcoeff : ∀ m : ℤ, fourierCoeff M m = fourierCoeff G m * (fejerKer R ((m:ℝ)*α) : ℂ) := by
    intro m; rw [hMdef]; exact mave_coeff2 G hGint α R hR m
  have hGcoeff : ∀ m : ℤ, fourierCoeff G m = fourierCoeffOn (by norm_num : (0:ℝ) < 1) g m := by
    intro m; rw [hGdef]; exact fourierCoeff_lift_eq_fourierCoeffOn g hgper m
  have hBcoeff : ∀ m : ℤ, fourierCoeff B m = (if m ∈ S then a m else 0) := by
    intro m; rw [hBdef]; exact finset_fourier_coeff S a m
  have hFFcoeff : ∀ m : ℤ, fourierCoeff FF m = (if (K:ℤ) < |m| then a m else 0) := by
    intro m
    have hmS : (m ∈ S) ↔ ¬ ((K:ℤ) < |m|) := by
      rw [hSdef, Finset.mem_Icc]
      constructor
      · rintro ⟨h1, h2⟩ hlt
        have h3 : |m| ≤ (K:ℤ) := by rw [abs_le]; exact ⟨h1, h2⟩
        omega
      · intro h
        rw [not_lt] at h
        rw [abs_le] at h
        exact ⟨h.1, h.2⟩
    rw [hFFdef, fourierCoeff_sub _ _ hMint hBint m, hMcoeff m, hGcoeff m, hBcoeff m]
    by_cases hm : (K:ℤ) < |m|
    · rw [if_neg (fun hmem => hmS.mp hmem hm), if_pos hm, hadef]
      simp only [sub_zero]
    · rw [if_pos (hmS.mpr hm), if_neg hm, hadef]
      simp only []
      ring
  have hFF2 : MemLp FF 2 (AddCircle.haarAddCircle) := by
    rw [hFFdef]; exact hM2.sub hB2
  have hMx : ∀ x : ℝ, M (x : AddCircle (1:ℝ)) = mAve g α R x := by
    intro x
    rw [hMdef, hGdef, mAve]
    apply congrArg (fun z : ℂ => ((R:ℂ)^2)⁻¹ * z)
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun j' _ => ?_))
    rw [← AddCircle.coe_add, Function.Periodic.lift_coe]
  have hpt : ∀ x ∈ Ioc (0:ℝ) 1,
      mAve g α R x - (fourierCoeffOn (by norm_num : (0:ℝ) < 1) g 0)
        - (∑ k ∈ (Finset.Icc (-(K:ℤ)) (K:ℤ)).filter (fun k => k ≠ 0),
            (fourierCoeffOn (by norm_num : (0:ℝ) < 1) g k) * (fejerKer R ((k:ℝ)*α) : ℂ)
              * Complex.exp (2*Real.pi*Complex.I*(k:ℝ)*x))
        = FF (x : AddCircle (1:ℝ)) := by
    intro x hx
    have hfourier : ∀ k : ℤ, fourier k (x : AddCircle (1:ℝ)) = Complex.exp (2*Real.pi*Complex.I*(k:ℝ)*x) := by
      intro k; rw [fourier_coe_apply]; congr 1; push_cast; ring
    have h0mem : (0:ℤ) ∈ S := by
      rw [hSdef, Finset.mem_Icc]; constructor <;> omega
    have hf0 : a 0 * fourier 0 (x : AddCircle (1:ℝ)) = fourierCoeffOn (by norm_num : (0:ℝ) < 1) g 0 := by
      rw [hadef]
      simp only [fejerKer_zero R hR, Complex.ofReal_one, Int.cast_zero, zero_mul, fourier_zero, mul_one]
    have hsum : (∑ k ∈ S, a k * fourier k (x : AddCircle (1:ℝ)))
        = fourierCoeffOn (by norm_num : (0:ℝ) < 1) g 0
          + ∑ k ∈ S.filter (fun k => k ≠ 0), (fourierCoeffOn (by norm_num : (0:ℝ) < 1) g k) * (fejerKer R ((k:ℝ)*α) : ℂ) * Complex.exp (2*Real.pi*Complex.I*(k:ℝ)*x) := by
      rw [← Finset.add_sum_erase S (fun k => a k * fourier k (x : AddCircle (1:ℝ))) h0mem]
      beta_reduce
      rw [hf0]
      congr 1
      rw [Finset.filter_ne' S 0]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [hadef, hfourier k]
    rw [hFFdef, Pi.sub_apply, hMx x, hBdef]
    simp only
    rw [hsum]
    ring
  have hbridge : ∫ x in (0:ℝ)..1, ‖mAve g α R x - (fourierCoeffOn (by norm_num : (0:ℝ) < 1) g 0)
        - (∑ k ∈ (Finset.Icc (-(K:ℤ)) (K:ℤ)).filter (fun k => k ≠ 0),
            (fourierCoeffOn (by norm_num : (0:ℝ) < 1) g k) * (fejerKer R ((k:ℝ)*α) : ℂ)
              * Complex.exp (2*Real.pi*Complex.I*(k:ℝ)*x))‖ ^ 2
      = ∫ t : AddCircle (1:ℝ), ‖FF t‖^2 ∂AddCircle.haarAddCircle := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    have h2 : ∫ t : AddCircle (1:ℝ), ‖FF t‖^2 ∂AddCircle.haarAddCircle
        = ∫ t : AddCircle (1:ℝ), ‖FF t‖^2 ∂volume := by
      rw [AddCircle.integral_haarAddCircle]; simp
    rw [h2, ← AddCircle.integral_preimage (T := 1) (t := 0) (f := fun t => ‖FF t‖^2)]
    simp only [zero_add]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    dsimp only
    rw [hpt x hx]
  have hPS : HasSum (fun m : ℤ => ‖fourierCoeff FF m‖^2) (∫ t : AddCircle (1:ℝ), ‖FF t‖^2 ∂AddCircle.haarAddCircle) := by
    have h1 := hasSum_sq_fourierCoeff hFF2.toLp
    have hf : (fun i : ℤ => ‖fourierCoeff (⇑hFF2.toLp) i‖^2) = (fun i : ℤ => ‖fourierCoeff FF i‖^2) := by
      funext m; rw [fourierCoeff_congr_ae hFF2.coeFn_toLp]
    rw [hf] at h1
    have h2 : ∫ t : AddCircle (1:ℝ), ‖(⇑hFF2.toLp) t‖^2 ∂AddCircle.haarAddCircle
        = ∫ t : AddCircle (1:ℝ), ‖FF t‖^2 ∂AddCircle.haarAddCircle := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hFF2.coeFn_toLp] with t ht
      rw [ht]
    rwa [h2] at h1
  have hbd : ∀ m : ℤ, ‖fourierCoeff FF m‖^2 ≤ (if (K:ℤ) < |m| then (1:ℝ)/((m:ℝ)^2) else 0) := by
    intro m
    rw [hFFcoeff m]
    by_cases hm : (K:ℤ) < |m|
    · rw [if_pos hm, if_pos hm]
      have hm0 : m ≠ 0 := by
        intro h; rw [h] at hm; simp at hm; omega
      rw [hadef]
      have h1 : ‖fourierCoeffOn (by norm_num : (0:ℝ) < 1) g m * (fejerKer R ((m:ℝ)*α) : ℂ)‖^2
          ≤ ((1/|(m:ℝ)|) * 1)^2 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (fejerKer_nonneg R _)]
        apply pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (fejerKer_nonneg R _))
        exact mul_le_mul (hdec m hm0) (fejerKer_le_one R ((m:ℝ)*α)) (fejerKer_nonneg R _)
          (div_nonneg zero_le_one (abs_nonneg _))
      refine le_trans h1 ?_
      simp only [mul_one, one_div, inv_pow, sq_abs]
      exact le_refl _
    · rw [if_neg hm, if_neg hm]; simp
  have htail := tail_sum2 K hK
  have hsum_bd : (∑' m : ℤ, ‖fourierCoeff FF m‖^2) ≤ 2/(K:ℝ) :=
    le_trans (Summable.tsum_le_tsum hbd hPS.summable htail.1) htail.2
  calc ∫ x in (0:ℝ)..1, ‖mAve g α R x - (fourierCoeffOn (by norm_num : (0:ℝ) < 1) g 0)
        - (∑ k ∈ (Finset.Icc (-(K:ℤ)) (K:ℤ)).filter (fun k => k ≠ 0),
            (fourierCoeffOn (by norm_num : (0:ℝ) < 1) g k) * (fejerKer R ((k:ℝ)*α) : ℂ)
              * Complex.exp (2*Real.pi*Complex.I*(k:ℝ)*x))‖ ^ 2
      = ∫ t : AddCircle (1:ℝ), ‖FF t‖^2 ∂AddCircle.haarAddCircle := hbridge
    _ = ∑' m : ℤ, ‖fourierCoeff FF m‖^2 := hPS.tsum_eq.symm
    _ ≤ 2/(K:ℝ) := hsum_bd

end Work.TMC7Core.Fourier
