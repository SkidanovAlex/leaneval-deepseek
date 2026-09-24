import Mathlib
import Submission.Work.GM.Trace.Defs
import Submission.Commons.Analysis.Fourier.poisson_summation_scaled
import Submission.Commons.Analysis.Calculus.exists_schwartzMap_eq_of_contDiff_hasCompactSupport

/-!
# Poisson summation for `h_t` (GM §4)

`h_t(u) = w(u)² u^{it}` is smooth and compactly supported in `[1,2]`, hence agrees with a
Schwartz function; Poisson summation applied to the dilation `u ↦ h_t(u/N)` gives

`Σ_{n ∈ ℤ} h_t(n/N) = N · Σ_{m ∈ ℤ} ĥ_t(mN)`,

and the sum on the left is finite, over `N ≤ n ≤ 2N`.

Paper reference: `REFS/GuthMaynard_2405.20552.txt`, §4 (used in the proof of Lemma 4.5).
-/

namespace Work.GM.Trace

open Submission.GM Submission.LargeValues
open scoped BigOperators FourierTransform

/-- `h_t` is smooth (with regularity `C^∞`, not analytic). -/
theorem hfun_contDiff' (t : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Submission.GM.hfun t) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases lt_or_ge x 1 with hx | hx
  · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Iio.mem_nhds hx] with u hu
    have h1 : u ∉ Set.Icc (1 : ℝ) 2 := fun h => absurd h.1 (not_le.mpr (Set.mem_Iio.mp hu))
    rw [Submission.GM.hfun, Submission.LargeValues.bumpW_eq_zero_of_notMem h1]; simp
  · have hx0 : (0:ℝ) < x := by linarith
    have hOn : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u : ℝ => ((Work.GM.Trace.w2 u : ℝ) : ℂ) *
          Complex.exp (Complex.I * (t : ℂ) * ((Real.log u : ℝ) : ℂ))) (Set.Ioi 0) := by
      have hlogOn : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun u : ℝ => ((Real.log u : ℝ) : ℂ)) (Set.Ioi 0) :=
        Complex.ofRealCLM.contDiff.comp_contDiffOn (Real.contDiffOn_log.mono (fun u hu => by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact ne_of_gt hu))
      have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => Complex.I * (t : ℂ) * z) :=
        contDiff_const.mul contDiff_id
      have hinner : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun u : ℝ => Complex.I * (t : ℂ) * ((Real.log u : ℝ) : ℂ)) (Set.Ioi 0) :=
        hc.comp_contDiffOn hlogOn
      have hexp := Complex.contDiff_exp.comp_contDiffOn hinner
      have hw : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun u : ℝ => ((Work.GM.Trace.w2 u : ℝ) : ℂ)) (Set.Ioi 0) :=
        (Complex.ofRealCLM.contDiff.comp Work.GM.Trace.w2_contDiff).contDiffOn
      exact hw.mul hexp
    have hOn' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Submission.GM.hfun t) (Set.Ioi 0) :=
      hOn.congr (fun u _ => Work.GM.Trace.hfun_eq_hfunLog t u)
    exact hOn'.contDiffAt (isOpen_Ioi.mem_nhds hx0)

/-- `h_t` is supported in `[1,2]`, hence compactly supported. -/
theorem hfun_hasCompactSupport' (t : ℝ) : HasCompactSupport (Submission.GM.hfun t) := by
  refine HasCompactSupport.intro (K := Set.Icc (1:ℝ) 2) isCompact_Icc ?_
  intro u hu
  rw [Submission.GM.hfun, Submission.LargeValues.bumpW_eq_zero_of_notMem hu]; simp

/-- The image of the integer interval `[N, 2N]` under `ℕ → ℤ`. -/
lemma Icc_map_natCast (N : ℕ) :
    (Finset.Icc N (2 * N)).map (⟨Nat.cast, Nat.cast_injective⟩ : ℕ ↪ ℤ)
      = Finset.Icc (N : ℤ) ((2 * N : ℕ) : ℤ) := by
  ext n
  simp only [Finset.mem_map, Finset.mem_Icc, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨k, ⟨hk1, hk2⟩, hk⟩
    subst hk
    exact ⟨by exact_mod_cast hk1, by exact_mod_cast hk2⟩
  · rintro ⟨hn1, hn2⟩
    have hn0 : 0 ≤ n := le_trans (by positivity : (0:ℤ) ≤ (N:ℤ)) hn1
    have hn : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg hn0
    refine ⟨n.toNat, ⟨?_, ?_⟩, hn⟩
    · have h : (N:ℤ) ≤ ((n.toNat : ℕ) : ℤ) := by rw [hn]; exact hn1
      exact_mod_cast h
    · have h : ((n.toNat : ℕ) : ℤ) ≤ ((2 * N : ℕ) : ℤ) := by rw [hn]; exact hn2
      exact_mod_cast h

/-- `h_t` vanishes at `n/N` unless `N ≤ n ≤ 2N`, so the `ℤ`-sum over `n` is the finite
sum over `n ∈ [N, 2N]`. -/
lemma tsum_hfun_eq_sum {N : ℕ} (hN : 1 ≤ N) (t : ℝ) :
    ∑' n : ℤ, Submission.GM.hfun t ((n:ℝ)/(N:ℝ))
      = ∑ n ∈ Finset.Icc N (2*N), Submission.GM.hfun t ((n:ℝ)/(N:ℝ)) := by
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hmem : ∀ n : ℤ, ((n:ℝ)/(N:ℝ)) ∈ Set.Icc (1:ℝ) 2 →
      n ∈ Finset.Icc (N:ℤ) ((2*N:ℕ):ℤ) := by
    intro n hn
    simp only [Set.mem_Icc] at hn
    simp only [Finset.mem_Icc]
    constructor
    · have h : (1:ℝ) * (N:ℝ) ≤ (n:ℝ) := (le_div_iff₀ hNpos).mp hn.1
      have h2 : (N:ℝ) ≤ (n:ℝ) := by simpa using h
      exact_mod_cast h2
    · have h : (n:ℝ) ≤ 2 * (N:ℝ) := (div_le_iff₀ hNpos).mp hn.2
      have h2 : (n:ℝ) ≤ ((2*N:ℕ):ℝ) := by push_cast; linarith
      exact_mod_cast h2
  have h1 : ∑ n ∈ Finset.Icc (N:ℤ) ((2*N:ℕ):ℤ), Submission.GM.hfun t ((n:ℝ)/(N:ℝ))
      = ∑ n ∈ Finset.Icc N (2*N), Submission.GM.hfun t ((n:ℝ)/(N:ℝ)) := by
    rw [← Icc_map_natCast N, Finset.sum_map]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    norm_num
  rw [tsum_eq_sum (s := Finset.Icc (N:ℤ) ((2*N:ℕ):ℤ)) (fun n hn => ?_)]
  · exact h1
  · have hni : ((n:ℝ)/(N:ℝ)) ∉ Set.Icc (1:ℝ) 2 := fun h => hn (hmem n h)
    rw [Submission.GM.hfun, Submission.LargeValues.bumpW_eq_zero_of_notMem hni]; simp

/-- Poisson summation for `h_t` (GM §4): since `h_t` is supported in `[1,2]` the sum over `n ∈ ℤ`
is the finite sum over `n ∈ [N,2N]`, and Poisson summation (Mathlib's normalisation
`e(x) = exp(2πix)`, which agrees with the paper's) gives the displayed identity. -/
theorem poisson_hfun {N : ℕ} (hN : 1 ≤ N) (t : ℝ) :
    ∑ n ∈ Finset.Icc N (2 * N), Submission.GM.hfun t ((n : ℝ) / (N : ℝ))
      = (N : ℂ) * ∑' m : ℤ, Submission.GM.hhat t ((m : ℝ) * (N : ℝ)) := by
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  obtain ⟨g, hg⟩ :=
    Commons.Analysis.Calculus.exists_schwartzMap_eq_of_contDiff_hasCompactSupport
      (hfun_contDiff' t) (hfun_hasCompactSupport' t)
  have hpois := Commons.Analysis.Fourier.poisson_summation_scaled g (N : ℝ) hNpos
  have hfg : ∀ y : ℝ, FourierTransform.fourier g y = Submission.GM.hhat t y := by
    intro y
    rw [Submission.GM.hhat, SchwartzMap.fourier_coe, Real.fourier_eq, Real.fourier_eq]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with v
    rw [hg v]
  calc ∑ n ∈ Finset.Icc N (2 * N), Submission.GM.hfun t ((n : ℝ) / (N : ℝ))
      = ∑' n : ℤ, Submission.GM.hfun t ((n:ℝ)/(N:ℝ)) := (tsum_hfun_eq_sum hN t).symm
    _ = ∑' n : ℤ, g ((n:ℝ)/(N:ℝ)) := tsum_congr (fun n => (hg _).symm)
    _ = (N:ℂ) * ∑' m : ℤ, FourierTransform.fourier g ((m:ℝ) * (N:ℝ)) := hpois
    _ = (N:ℂ) * ∑' m : ℤ, Submission.GM.hhat t ((m:ℝ) * (N:ℝ)) := by
        congr 1
        exact tsum_congr (fun m => hfg _)

end Work.GM.Trace
