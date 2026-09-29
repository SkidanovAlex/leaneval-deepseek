import Submission.Work.C17.lc_main
import Submission.Work.C17I.tsum_shift_lemmas
import Submission.Work.C17I.pw_continuation
import Submission.Work.C17I.J_package
import Submission.Work.C17I.dy_iter_log_struct
import Submission.Work.C17I.integral_log_struct
import Submission.Work.C17I.DyIter_comp_yC
import Submission.Work.C17I.Gfun_repr
import Submission.Work.C17I.seventeen_subst_eval_disc
import Submission.Work.C17I.seventeen_coeff_bounds_sharp
import Submission.Work.C17I.pullback_rel_disc
import Submission.Work.C17I.logP_coeff_bound_sharp
import Submission.Work.C17I.logP_radius_of_hloc

namespace Work.C17I

open scoped BigOperators Topology
open Polynomial Filter

noncomputable section

/-- The `y`-series of the seventeen entries, evaluated at `yC z`. -/
def PhiS (m n : ℕ) (ra rb rab r0 : ℤ) (i : Fin 17) : ℂ → ℂ :=
  fun z => ∑' k : ℕ, ((PowerSeries.coeff k
    (Submission.CDTPlan.seventeen m n ra rb rab r0 i) : ℚ) : ℂ) * Work.C17.yC z ^ k

theorem relation_to_LC_core
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hlt : m < n)
    (hgap : 10 ^ 6 * ((m : ℤ) - n).natAbs ≤ n)
    (ra rb rab r0 : ℤ) (P : Fin 17 → Polynomial ℚ)
    (hrel : ∑ i : Fin 17, (P i : PowerSeries ℚ)
        * Submission.CDTPlan.seventeen m n ra rb rab r0 i = 0)
    {S : Set ℂ} (hSconv : Convex ℝ S) (hSo : IsOpen S)
    (hS1 : Metric.ball ((Work.C17.xsOf m n : ℂ)) ((1 - Work.C17.xsOf m n) / 2) ⊆ S)
    (hS2 : Metric.ball Work.C17.p0C (1 / 20) ⊆ S) (hS0 : (0 : ℂ) ∉ S)
    (hSsub : S ⊆ Metric.ball (0 : ℂ) 1)
    {Ψ : ℂ → ℂ} (hΨd : DifferentiableOn ℂ Ψ S)
    (hΨv : ∀ z ∈ S, ‖z / (z - 1)‖ < Work.C17.xsOf m n →
        Ψ z = Work.C17.Pfun (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0 (z / (z - 1)))
    (y1 : ℂ → ℂ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : 2 * δ ≤ Work.C17.xsOf m n)
    (hδ2 : 2 * δ ≤ 1 - Work.C17.xsOf m n)
    (κ : ℂ) (hκ : κ ≠ 0)
    (hy1d : DifferentiableOn ℂ y1 (Metric.ball ((Work.C17.xsOf m n : ℂ)) δ))
    (hy1ne : y1 ((Work.C17.xsOf m n : ℂ)) ≠ 0)
    (hode : ∀ z ∈ Metric.ball ((Work.C17.xsOf m n : ℂ)) δ,
      (Work.C17.P2x (Work.C17.aOf m) (Work.C17.aOf n)).eval₂ (algebraMap ℚ ℂ) z
          * deriv (deriv y1) z
        + (Work.C17.P1x (Work.C17.aOf m) (Work.C17.aOf n)).eval₂ (algebraMap ℚ ℂ) z * deriv y1 z
        + (Work.C17.P0x (Work.C17.aOf m) (Work.C17.aOf n)).eval₂ (algebraMap ℚ ℂ) z * y1 z = 0)
    (hloc : ∃ hh : ℂ → ℂ,
      DifferentiableOn ℂ hh (Metric.ball ((Work.C17.xsOf m n : ℂ)) δ) ∧
      ∀ z ∈ Metric.ball ((Work.C17.xsOf m n : ℂ)) δ ∩ Metric.ball (0 : ℂ) (Work.C17.xsOf m n),
        Work.C17.Pfun (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0 z
          = κ * y1 z * Complex.log (((Work.C17.xsOf m n : ℝ) : ℂ) - z) + hh z) :
    ∃ J : Fin 6 → ℂ → ℂ,
      (∀ i, DifferentiableOn ℂ (J i) (Metric.ball ((Work.C17.xsOf m n : ℂ)) δ)) ∧
      (∀ i, J i ((Work.C17.xsOf m n : ℂ)) = 0) ∧
      (∀ i, ∀ z ∈ Metric.ball ((Work.C17.xsOf m n : ℂ)) δ,
        HasDerivAt (J i)
          ((((Work.C17.yQ ^ ((i : ℤ) - 4)) * Work.C17.dyQ).num.eval₂ (algebraMap ℚ ℂ) z)
            / (((Work.C17.yQ ^ ((i : ℤ) - 4)) * Work.C17.dyQ).denom.eval₂ (algebraMap ℚ ℂ) z)
            * y1 z) z) ∧
      ∀ z ∈ Metric.ball ((Work.C17.xsOf m n : ℂ)) δ,
        (∑ k : Fin 4, Work.C17.pAtY (P ⟨5 + (k : ℕ), by omega⟩) z
            * Work.C17.DyIter (k : ℕ) y1 z)
          + (∑ i : Fin 6, Work.C17.pAtY (P ⟨11 + (i : ℕ), by omega⟩) z
              * J ⟨5 - (i : ℕ), by omega⟩ z) = 0 := by
  obtain ⟨hh, hhhd, hhloc⟩ := hloc
  set s : ℝ := Work.C17.xsOf m n with hsdef
  have hs_pos : 0 < s := Work.C17.xsOf_pos m n hm hlt
  have hs_lt1 : s < 1 := Work.C17.xsOf_lt_one m n hm hlt
  have hs89 : (8 : ℝ) / 9 ≤ s := Work.C17I.xsOf_ge_eight_ninths m n hm hlt hgap
  have hδs : δ < 1 - s := by linarith
  have hδs2 : δ < s := by linarith
  have hδ1' : 2 * δ ≤ s := hδ1
  have hδ2' : 2 * δ ≤ 1 - s := hδ2
  -- coefficient bounds for `logP` and for the seventeen entries
  obtain ⟨C, hCpos, hCb⟩ := Work.C17I.logP_radius_of_hloc m n hm hn hlt hgap ra rb rab r0
    κ hκ y1 hδ hδ1 hδ2 hy1d hy1ne hh hhhd hhloc
  obtain ⟨ρ, hρlo, hρhi, C₂, hC₂pos, hC₂b⟩ := Work.C17I.logP_coeff_bound_sharp m n hm hn hlt
    hgap ra rb rab r0 κ hκ y1 hδ hδ1 hδ2 hy1d hy1ne hh hhhd hhloc
  have hρpos : 0 < ρ := by nlinarith [hρlo, hδ1, hs_pos]
  have hbous := Work.C17I.seventeen_coeff_bounds_sharp m n hm hn hlt hgap ra rb rab r0 hCpos hCb
  obtain ⟨J, hJd, hJ0, hJderiv, hJval⟩ :=
    Work.C17I.J_package m n hm hn hlt hgap hδ hδ1 hδ2 hy1d
  -- the non-log part and the continued `G`
  set Gs : PowerSeries ℚ := Submission.CDT.sympSym
    (Submission.CDT.logP (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0) with hGs
  set Gf : ℂ → ℂ := fun z => Work.C17.Pfun (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0 z
    + Ψ z with hGf
  set Ω : Set ℂ := S ∩ Metric.ball (0 : ℂ) ρ with hΩdef
  have hΩcvx : Convex ℝ Ω := hSconv.inter (convex_ball (0:ℂ) ρ)
  have hΩopen : IsOpen Ω := hSo.inter Metric.isOpen_ball
  have hp0Ω : Work.C17.p0C ∈ Ω := by
    refine ⟨hS2 (Metric.mem_ball_self (by norm_num)), ?_⟩
    rw [Metric.mem_ball, dist_zero_right]
    have h1 : ‖Work.C17.p0C‖ ≤ (33:ℝ)/100 := Work.C17.norm_p0C_le
    have h2 : (33:ℝ)/100 < ρ := by nlinarith [hρlo, hδ1, hs89]
    linarith
  have hPfun_d : DifferentiableOn ℂ (Work.C17.Pfun (Work.C17.aOf m) (Work.C17.aOf n)
      ra rb rab r0) (Metric.ball (0 : ℂ) ρ) := by
    rw [show Work.C17.Pfun (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0
        = fun z => ∑' k : ℕ, ((PowerSeries.coeff k
            (Submission.CDT.logP (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0) : ℚ) : ℂ)
            * z ^ k from rfl]
    have h := Work.C17.differentiableOn_tsum_of_coeff_growth hC₂pos.le
      (by positivity : (0:ℝ) < 1 / ρ) hC₂b
    rwa [one_div_one_div] at h
  have hGfd : DifferentiableOn ℂ Gf Ω := by
    rw [hGf, hΩdef]
    exact (hPfun_d.mono (fun z hz => hz.2)).add (hΨd.mono (fun z hz => hz.1))
  -- the `G`-block: logarithm structure
  have hVsub : ∀ z ∈ Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) ρ, z ∈ Ω := by
    intro z hz
    refine ⟨?_, hz.2⟩
    have h2 : δ ≤ (1 - s) / 2 := by linarith
    exact hS1 (Metric.ball_subset_ball h2 hz.1)
  have hΩ0 : ∀ z ∈ Ω, z ≠ 0 := by
    intro z hz h
    exact hS0 (by rw [← h]; exact hz.1)
  have hΩ1 : ∀ z ∈ Ω, z ≠ 1 := by
    intro z hz h
    have h2 := hSsub hz.1
    rw [h] at h2
    rw [Metric.mem_ball, dist_zero_right] at h2
    rw [show ‖(1:ℂ)‖ = 1 from by norm_num] at h2
    exact absurd h2 (not_lt.mpr le_rfl)
  have hΩ2 : ∀ z ∈ Ω, z ≠ 2 := by
    intro z hz h
    have h2 := hSsub hz.1
    rw [h] at h2
    rw [Metric.mem_ball, dist_zero_right] at h2
    rw [show ‖(2:ℂ)‖ = 2 from by norm_num] at h2
    linarith
  have hzeq : s - (s - ρ + δ) / 2 = (s + ρ - δ) / 2 := by
    have h1 : (s - ρ + δ) / 2 = s / 2 - ρ / 2 + δ / 2 := by ring
    have h2 : (s + ρ - δ) / 2 = s / 2 + ρ / 2 - δ / 2 := by ring
    rw [h1, h2]; ring
  have hVne : (Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) ρ).Nonempty := by
    refine ⟨(((s - (s - ρ + δ) / 2 : ℝ)) : ℂ), ?_, ?_⟩
    · rw [Metric.mem_ball, Complex.dist_eq]
      have hc : (((s - (s - ρ + δ) / 2 : ℝ)) : ℂ) - ((s : ℝ) : ℂ)
          = (((ρ - s - δ) / 2 : ℝ) : ℂ) := by push_cast; ring
      have hneg : (ρ - s - δ) / 2 ≤ 0 := by linarith
      rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hneg]
      linarith
    · have hpos : (0:ℝ) < (s + ρ - δ) / 2 := by linarith
      rw [hzeq, Metric.mem_ball, Complex.dist_eq, sub_zero, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hpos]
      linarith
  have hAG : ∀ z ∈ Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) ρ,
      Gf z = (fun z => κ * y1 z) z * Complex.log ((s : ℂ) - z) + (fun z => hh z + Ψ z) z := by
    intro z hz
    have h1 : z ∈ Metric.ball (s : ℂ) δ := hz.1
    have h2 : ‖z‖ < s := by
      have h3 : ‖z‖ < ρ := by
        have h4 := hz.2
        rwa [Metric.mem_ball, dist_zero_right] at h4
      linarith [hρhi]
    have h3 := hhloc z ⟨h1, by rwa [Metric.mem_ball, dist_zero_right]⟩
    rw [hGf]
    dsimp only
    rw [h3]
    ring
  have hGkraw : ∀ k : ℕ, ∃ Gk : ℂ → ℂ, DifferentiableOn ℂ Gk (Metric.ball (s : ℂ) δ) ∧
      ∀ z ∈ Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) ρ,
        Work.C17.DyIter k Gf z
          = Work.C17.DyIter k (fun z => κ * y1 z) z * Complex.log ((s : ℂ) - z)
            + Gk z / (z - (s : ℂ)) ^ k :=
    Work.C17I.dy_iter_log_struct (s := s) (δ := δ) (ρ := ρ) hδ hs_pos hρhi hVne
      (fun z hz => fun h => Work.C17.zero_notMem_ball_xs m n hm hlt hδ1 (by rw [← h]; exact hz))
      (fun z hz => fun h => Work.C17.two_notMem_ball_xs m n hm hlt hδ2 (by rw [← h]; exact hz))
      (F := Gf) (A := fun z => κ * y1 z) (G := fun z => hh z + Ψ z)
      (hGfd.mono hVsub) (hy1d.const_mul κ)
      (hhhd.add (hΨd.mono (fun z hz => hS1 (Metric.ball_subset_ball (by linarith) hz))))
      hAG
  choose Gk hGkd hGkraw' using hGkraw
  have hGk : ∀ k : Fin 4, ∀ z ∈ Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) ρ,
      Work.C17.DyIter (k : ℕ) Gf z = κ * Work.C17.DyIter (k : ℕ) y1 z * Complex.log ((s : ℂ) - z)
        + Gk (k : ℕ) z / (z - (s : ℂ)) ^ (k : ℕ) := by
    intro k z hz
    rw [hGkraw' (k : ℕ) z hz, Work.C17.DyIter_const_mul κ (k : ℕ) y1]
  -- the `B`-block: the substituted series
  set Fb : Fin 7 → ℂ → ℂ := fun b z => ∑' k : ℕ, ((PowerSeries.coeff k
      ((Submission.CDTPlan.pureB b).subst Submission.CDT.sympY) : ℚ) : ℂ) * z ^ k with hFb
  have hFbd : ∀ b, DifferentiableOn ℂ (Fb b) (Metric.ball (s : ℂ) δ) := by
    intro b
    refine (Work.C17.Bsubst_differentiableOn b).mono ?_
    intro z hz
    rw [Metric.mem_ball, dist_zero_right]
    have h1 : ‖z - ((s : ℝ) : ℂ)‖ < δ := by
      have h2 := hz
      rwa [Metric.mem_ball, Complex.dist_eq] at h2
    have h2 : ‖z‖ ≤ ‖z - ((s : ℝ) : ℂ)‖ + ‖((s : ℝ) : ℂ)‖ := by
      calc ‖z‖ = ‖(z - ((s : ℝ) : ℂ)) + ((s : ℝ) : ℂ)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    have h3 : ‖((s : ℝ) : ℂ)‖ = s := by
      rw [Complex.norm_real, Real.norm_of_nonneg (le_of_lt hs_pos)]
    rw [h3] at h2
    have h4 : δ ≤ (1 - s) / 2 := by linarith
    linarith
  -- the integral block: primitives with the correct derivative
  set gd : Fin 6 → ℂ → ℂ := fun i z => if (i : ℕ) = 0 then Work.C17.yC z * Work.C17.dyC z
    else Work.C17.dyC z / (Work.C17.yC z) ^ ((i : ℕ) - 1) with hgd
  have hgd_d : ∀ i : Fin 6, DifferentiableOn ℂ (gd i) (Metric.ball (s : ℂ) δ) := by
    intro i
    rw [hgd]
    by_cases hi : (i : ℕ) = 0
    · simp only [hi, ↓reduceIte]
      exact (Work.C17.yC_differentiableOn_of_ne_one fun z hz => fun h =>
        Work.C17.one_notMem_ball_xs m n hm hlt hδ2 (by rw [← h]; exact hz)).mul
        (Work.C17.dyC_differentiableOn_of_ne_one fun z hz => fun h =>
          Work.C17.one_notMem_ball_xs m n hm hlt hδ2 (by rw [← h]; exact hz))
    · simp only [hi, ↓reduceIte]
      refine (Work.C17.dyC_differentiableOn_of_ne_one fun z hz => fun h =>
        Work.C17.one_notMem_ball_xs m n hm hlt hδ2 (by rw [← h]; exact hz)).div
        ((Work.C17.yC_differentiableOn_of_ne_one fun z hz => fun h =>
          Work.C17.one_notMem_ball_xs m n hm hlt hδ2 (by rw [← h]; exact hz)).pow _) ?_
      intro z hz
      refine pow_ne_zero _ (Work.C17.yC_ne_zero_iff z ?_ ?_)
      · exact fun h => Work.C17.zero_notMem_ball_xs m n hm hlt hδ1 (by rw [← h]; exact hz)
      · exact fun h => Work.C17.one_notMem_ball_xs m n hm hlt hδ2 (by rw [← h]; exact hz)
  set polyJet : Fin 6 → Polynomial ℚ := fun i => ∑ m ∈ Finset.range ((i : ℕ) - 1),
    Polynomial.C (PowerSeries.coeff m Gs) * Polynomial.X ^ m with hpolyJet
  set jet : Fin 6 → ℂ → ℂ := fun i => Work.C17.pAtY (polyJet i) with hjet
  have hjet_eval : ∀ (i : Fin 6) (z : ℂ), jet i z
      = ∑ m ∈ Finset.range ((i : ℕ) - 1),
          ((PowerSeries.coeff m Gs : ℚ) : ℂ) * Work.C17.yC z ^ m := by
    intro i z
    simp only [hjet, hpolyJet, Work.C17.pAtY, Polynomial.eval₂_finsetSum,
      Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    have hq : (algebraMap ℚ ℂ) (PowerSeries.coeff m Gs) = ((PowerSeries.coeff m Gs : ℚ) : ℂ) :=
      map_ratCast _ _
    rw [hq]
  have hjet_d : ∀ i, DifferentiableOn ℂ (jet i) (Metric.ball (s : ℂ) δ) :=
    fun i => Work.C17I.pAtY_differentiableOn hδ hδs (polyJet i)
  have hjet_Ω : ∀ i : Fin 6, DifferentiableOn ℂ (jet i) Ω :=
    fun i => Work.C17.pAtY_differentiableOn_of_ne_one hΩ1 (polyJet i)
  have hgdd : ∀ i : Fin 6, DifferentiableOn ℂ (fun z => gd i z * (Gf z - jet i z)) Ω := by
    intro i
    have h1 : DifferentiableOn ℂ (gd i) Ω := by
      rw [hgd]
      by_cases hi : (i : ℕ) = 0
      · simp only [hi, ↓reduceIte]
        exact (Work.C17.yC_differentiableOn_of_ne_one hΩ1).mul
          (Work.C17.dyC_differentiableOn_of_ne_one hΩ1)
      · simp only [hi, ↓reduceIte]
        refine (Work.C17.dyC_differentiableOn_of_ne_one hΩ1).div
          ((Work.C17.yC_differentiableOn_of_ne_one hΩ1).pow _) ?_
        intro z hz
        exact pow_ne_zero _ (Work.C17.yC_ne_zero_iff z (hΩ0 z hz) (hΩ1 z hz))
    exact h1.mul (hGfd.sub (hjet_Ω i))
  choose FI hFId hFIval hFIderiv using fun i : Fin 6 =>
    Work.C17.exists_primitive_conv hΩcvx hΩopen (hgdd i) hp0Ω
      (PhiS m n ra rb rab r0 (Work.C17.iIdx i) Work.C17.p0C)
  -- the logarithm structure of the integral block
  have hHnl : ∀ i : Fin 6, ∃ Hn : ℂ → ℂ, DifferentiableOn ℂ Hn (Metric.ball (s : ℂ) δ) ∧
      ∀ z ∈ Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) ρ,
        FI i z = κ * J (Work.C17.jrev i) z * Complex.log ((s : ℂ) - z)
          + Hn z / (z - (s : ℂ)) := by
    intro i
    refine Work.C17I.integral_log_struct (s := s) (δ := δ) (ρ := ρ) hδ hs_pos hρhi hVne
      (g := gd i) (h := fun z => hh z + Ψ z - jet i z) (y1 := y1)
      (J := J (Work.C17.jrev i)) (F := FI i) (κ := κ) (hgd_d i) ?_ hy1d (hJd _) ?_ ?_
      ((hFId i).mono hVsub) ?_
    · refine (hhhd.add ?_).sub (hjet_d i)
      exact hΨd.mono (fun z hz => hS1 (Metric.ball_subset_ball (by linarith) hz))
    · intro z hz
      have h1 := hJderiv (Work.C17.jrev i) z hz
      have h2 := hJval (Work.C17.jrev i) z hz
      have h3 : (Work.C17.jrev i : ℤ) - 4 = 1 - (i : ℤ) := by
        simp only [Work.C17.jrev]
        have h4 : ((5 - (i : ℕ) : ℕ) : ℤ) = 5 - (i : ℤ) := by omega
        rw [h4]; ring
      rw [h2, h3] at h1
      have h4 : ((z ^ 2 - 2 * z) / (z - 1) ^ 2) = Work.C17.dyC z := rfl
      rw [h4] at h1
      rw [hgd]
      by_cases hi : (i : ℕ) = 0
      · simp only [hi, ↓reduceIte]
        -- `1 - (i:ℤ) = 1` and `yC z ^ (1:ℤ) = yC z`
        rw [show (1 : ℤ) - (i : ℤ) = 1 by omega, zpow_one] at h1
        exact h1
      · simp only [hi, ↓reduceIte]
        rw [show (1 : ℤ) - (i : ℤ) = -((i : ℤ) - 1) by omega, zpow_neg] at h1
        have h5 : ((i : ℤ) - 1) = (((i : ℕ) - 1 : ℕ) : ℤ) := by omega
        rw [h5, zpow_natCast] at h1
        rw [div_eq_mul_inv]
        exact h1.congr_deriv (by ring)
    · rw [hsdef]
      exact hJ0 (Work.C17.jrev i)
    · intro z hz
      have h1 := hFIderiv i z (hVsub z hz)
      have h2 : Gf z - jet i z
          = κ * y1 z * Complex.log ((s:ℂ) - z) + (hh z + Ψ z - jet i z) := by
        have h3 := hhloc z ⟨hz.1, by
          rw [Metric.mem_ball, dist_zero_right]
          have h4 : ‖z‖ < ρ := by
            have h5 := hz.2
            rwa [Metric.mem_ball, dist_zero_right] at h5
          linarith [hρhi]⟩
        rw [hGf]
        dsimp only
        rw [h3]
        ring
      rw [h2] at h1
      exact h1
  choose Hn hHnd hHn using hHnl
  -- the identifications of the three blocks
  have hU0sub : Metric.ball Work.C17.p0C (1/100) ⊆ Ω := by
    intro z hz
    refine ⟨hS2 (Metric.ball_subset_ball (by norm_num) hz), ?_⟩
    rw [Metric.mem_ball, dist_zero_right]
    have h1 : ‖z - Work.C17.p0C‖ < (1:ℝ)/100 := by
      have h2 := hz
      rwa [Metric.mem_ball, Complex.dist_eq] at h2
    have h3 : ‖z‖ ≤ ‖z - Work.C17.p0C‖ + ‖Work.C17.p0C‖ := by
      calc ‖z‖ = ‖(z - Work.C17.p0C) + Work.C17.p0C‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    have h4 : ‖Work.C17.p0C‖ ≤ (33:ℝ)/100 := Work.C17.norm_p0C_le
    have h5 : (33:ℝ)/100 < ρ := by nlinarith [hρlo, hδ1, hs89]
    linarith
  have hU0_34 : ∀ z ∈ Metric.ball Work.C17.p0C (1/100), ‖z‖ ≤ (34:ℝ)/100 := by
    intro z hz
    have h1 : ‖z - Work.C17.p0C‖ < (1:ℝ)/100 := by
      have h2 := hz
      rwa [Metric.mem_ball, Complex.dist_eq] at h2
    have h3 : ‖z‖ ≤ ‖z - Work.C17.p0C‖ + ‖Work.C17.p0C‖ := by
      calc ‖z‖ = ‖(z - Work.C17.p0C) + Work.C17.p0C‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    have h4 : ‖Work.C17.p0C‖ ≤ (33:ℝ)/100 := Work.C17.norm_p0C_le
    linarith
  have hU0z0 : ∀ z ∈ Metric.ball Work.C17.p0C (1/100), z ≠ 0 := by
    intro z hz h
    rw [h] at hz
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    rw [show ‖(0:ℂ) - Work.C17.p0C‖ = ‖Work.C17.p0C‖ from by rw [zero_sub, norm_neg]] at hz
    have h4 : (1:ℝ)/3 ≤ ‖Work.C17.p0C‖ := by
      have h5 := Work.C17.norm_p0C_sq
      nlinarith [norm_nonneg Work.C17.p0C, sq_nonneg (‖Work.C17.p0C‖ - 1/3)]
    linarith
  have hU0z1 : ∀ z ∈ Metric.ball Work.C17.p0C (1/100), z ≠ 1 := by
    intro z hz h
    rw [h] at hz
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    rw [show ‖(1:ℂ) - Work.C17.p0C‖ = ‖Work.C17.p0C - 1‖ from norm_sub_rev _ _] at hz
    have h3 := Work.C17.norm_p0C_sub_one_gt
    linarith
  have hU0z2 : ∀ z ∈ Metric.ball Work.C17.p0C (1/100), z ≠ 2 := by
    intro z hz h
    rw [h] at hz
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    have h1 : ‖Work.C17.p0C‖ ≤ (33:ℝ)/100 := Work.C17.norm_p0C_le
    have h2 : ‖(2:ℂ) - Work.C17.p0C‖ ≥ 2 - (33:ℝ)/100 := by
      have h3 : ‖(2:ℂ)‖ ≤ ‖(2:ℂ) - Work.C17.p0C‖ + ‖Work.C17.p0C‖ := by
        calc ‖(2:ℂ)‖ = ‖((2:ℂ) - Work.C17.p0C) + Work.C17.p0C‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      rw [show ‖(2:ℂ)‖ = 2 from by norm_num] at h3
      linarith
    linarith
  have hyc : ∀ z ∈ Metric.ball Work.C17.p0C (1/100), ‖Work.C17.yC z‖ < (1:ℝ)/5 := by
    intro z hz
    have h34 := hU0_34 z hz
    have hge : (66:ℝ)/100 ≤ ‖z - 1‖ := by
      have h5 : ‖(1:ℂ)‖ ≤ ‖(1:ℂ) - z‖ + ‖z‖ := by
        calc ‖(1:ℂ)‖ = ‖((1:ℂ) - z) + z‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      rw [norm_one] at h5
      rw [show ‖(1:ℂ) - z‖ = ‖z - 1‖ from norm_sub_rev _ _] at h5
      linarith
    have hne1 : (0:ℝ) < ‖z - 1‖ := by linarith
    have h1 : Work.C17.yC z = z ^ 2 / (z - 1) := rfl
    rw [h1, norm_div, norm_pow, div_lt_iff₀ hne1]
    nlinarith [h34, hge, norm_nonneg z]
  have hFBid : ∀ b : Fin 7, ∀ z ∈ Metric.ball Work.C17.p0C (1/100),
      Fb b z = PhiS m n ra rb rab r0 (Work.C17.bIdx b) z := by
    intro b z hz
    have h := Work.C17I.seventeen_subst_eval_disc m n hm hn hlt hgap ra rb rab r0 hCpos hCb
      (Work.C17.bIdx b) z (hU0_34 z hz)
    rw [Work.C17.seventeen_bIdx_eq m n ra rb rab r0 b] at h
    rw [hFb]
    dsimp only
    rw [PhiS, Work.C17.seventeen_bIdx_eq m n ra rb rab r0 b]
    exact h.tsum_eq
  -- the `G`-block identification
  obtain ⟨C₀, R₀, hC₀pos, hR₀1, hR₀2, hR₀b⟩ := hbous (Work.C17.gIdx 0)
  have hR₀pos : 0 < R₀ := lt_trans (by norm_num) hR₀1
  have hGb : ∀ t : ℕ, ‖((PowerSeries.coeff t Gs : ℚ) : ℂ)‖ * R₀ ^ t ≤ C₀ := by
    intro t
    have h := hR₀b t
    rw [Work.C17.seventeen_gIdx_eq' m (n) ra rb rab r0 (0 : Fin 4)] at h
    exact h
  have hGf_repr : ∀ z ∈ Metric.ball Work.C17.p0C (1/20),
      (∑' n : ℕ, ((PowerSeries.coeff n Gs : ℚ) : ℂ) * Work.C17.yC z ^ n) = Gf z := by
    intro z hz
    rw [hGf, hGs]
    exact Work.C17I.Gfun_repr m n hm hn hlt hgap ra rb rab r0 hCpos hCb hS2 hΨd hΨv z hz
  have hFGid : ∀ k : Fin 4, ∀ z ∈ Metric.ball Work.C17.p0C (1/100),
      Work.C17.DyIter (k : ℕ) Gf z = PhiS m n ra rb rab r0 (Work.C17.gIdx k) z := by
    intro k z hz
    have hz20 : z ∈ Metric.ball Work.C17.p0C (1/20) := Metric.ball_subset_ball (by norm_num) hz
    have hev : Gf =ᶠ[𝓝 z] (fun w => ∑' n : ℕ, ((PowerSeries.coeff n Gs : ℚ) : ℂ)
        * Work.C17.yC w ^ n) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz20] with w hw
      exact (hGf_repr w (Metric.ball_subset_ball (by norm_num) hw)).symm
    rw [Work.C17.DyIter_congr hev (k : ℕ)]
    have hmain := Work.C17I.DyIter_comp_yC Gs hC₀pos hR₀pos hGb z
      (lt_trans (hyc z hz) hR₀1) (hU0z0 z hz) (hU0z1 z hz) (hU0z2 z hz) (k : ℕ)
    rw [hmain, PhiS, Work.C17.seventeen_gIdx_eq' m n ra rb rab r0 k]
  -- the integral-block identification
  have hFIid : ∀ i : Fin 6, ∀ z ∈ Metric.ball Work.C17.p0C (1/100),
      FI i z = PhiS m n ra rb rab r0 (Work.C17.iIdx i) z := by
    intro i
    obtain ⟨C', R, hC'pos, hR1, hR2, hRb⟩ := hbous (Work.C17.iIdx i)
    have hRpos : 0 < R := lt_trans (by norm_num) hR1
    have hΦd : DifferentiableOn ℂ (PhiS m n ra rb rab r0 (Work.C17.iIdx i))
        (Metric.ball Work.C17.p0C (1/100)) := by
      intro z hz
      exact (Work.C17.differentiableAt_ySeriesFun hC'pos hRpos
        (fun k => hRb k) (lt_trans (hyc z hz) hR1) (hU0z1 z hz)).differentiableWithinAt
    have hΦderiv : ∀ z ∈ Metric.ball Work.C17.p0C (1/100),
        deriv (PhiS m n ra rb rab r0 (Work.C17.iIdx i)) z = gd i z * (Gf z - jet i z) := by
      intro z hz
      have hder := Work.C17.deriv_ySeriesFun
        (c := fun k => ((PowerSeries.coeff k
          (Submission.CDTPlan.seventeen m n ra rb rab r0 (Work.C17.iIdx i)) : ℚ) : ℂ))
        hC'pos hRpos (fun k => hRb k) (lt_trans (hyc z hz) hR1) (hU0z1 z hz)
      have hΦeq : PhiS m n ra rb rab r0 (Work.C17.iIdx i) = Work.C17.ySeriesFun
          (fun k => ((PowerSeries.coeff k
            (Submission.CDTPlan.seventeen m n ra rb rab r0 (Work.C17.iIdx i)) : ℚ) : ℂ)) := rfl
      rw [hΦeq, hder]
      -- reduce to the `y`-series identity
      rw [hgd]
      by_cases hi : (i : ℕ) = 0
      · simp only [hi, ↓reduceIte]
        have hjet0 : jet i z = 0 := by
          rw [hjet_eval, hi]
          simp
        rw [hjet0]
        -- `dY f = X * Gs`
        have hii : Work.C17.iIdx i = Work.C17.iIdx 0 := by
          apply Fin.ext
          simp only [Work.C17.iIdx]
          omega
        have hdY : PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.seventeen m n ra rb rab r0
            (Work.C17.iIdx i)) = PowerSeries.X * Gs := by
          rw [hii, Work.C17.seventeen_iIdx_zero' m n ra rb rab r0]
          exact Work.C17.dY_intY _
        have hS : (∑' k : ℕ, ((k : ℂ) + 1) * ((PowerSeries.coeff (k + 1)
              (Submission.CDTPlan.seventeen m n ra rb rab r0 (Work.C17.iIdx i)) : ℚ) : ℂ)
              * Work.C17.yC z ^ k)
            = Work.C17.yC z * Gf z := by
          rw [show (∑' k : ℕ, ((k : ℂ) + 1) * ((PowerSeries.coeff (k + 1)
                (Submission.CDTPlan.seventeen m n ra rb rab r0 (Work.C17.iIdx i)) : ℚ) : ℂ)
                * Work.C17.yC z ^ k)
              = (∑' k : ℕ, ((PowerSeries.coeff k (PowerSeries.derivative (R := ℚ)
                  (Submission.CDTPlan.seventeen m n ra rb rab r0 (Work.C17.iIdx i))) : ℚ) : ℂ)
                  * Work.C17.yC z ^ k) from by
            refine tsum_congr (fun k => ?_)
            rw [PowerSeries.coeff_derivative]
            push_cast
            ring]
          rw [hdY, (Work.C17I.tsum_shift_lemmas Gs hC₀pos hR₀pos hGb 0
            (lt_trans (hyc z hz) hR₀1)).2, hGf_repr z (Metric.ball_subset_ball (by norm_num) hz)]
        rw [hS]
        ring
      · simp only [hi, ↓reduceIte]
        have hdY : PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.seventeen m n ra rb rab r0
            (Work.C17.iIdx i)) = Submission.CDTPlan.tq ((i : ℕ) - 1) Gs := by
          rw [Work.C17.seventeen_iIdx_pos' m n ra rb rab r0 i hi]
          exact Work.C17.dY_intY _
        have hkey : (∑' k : ℕ, ((k : ℂ) + 1) * ((PowerSeries.coeff (k + 1)
              (Submission.CDTPlan.seventeen m n ra rb rab r0 (Work.C17.iIdx i)) : ℚ) : ℂ)
              * Work.C17.yC z ^ k)
            = (Gf z - jet i z) / (Work.C17.yC z) ^ ((i : ℕ) - 1) := by
          rw [show (∑' k : ℕ, ((k : ℂ) + 1) * ((PowerSeries.coeff (k + 1)
                (Submission.CDTPlan.seventeen m n ra rb rab r0 (Work.C17.iIdx i)) : ℚ) : ℂ)
                * Work.C17.yC z ^ k)
              = (∑' k : ℕ, ((PowerSeries.coeff k (PowerSeries.derivative (R := ℚ)
                  (Submission.CDTPlan.seventeen m n ra rb rab r0 (Work.C17.iIdx i))) : ℚ) : ℂ)
                  * Work.C17.yC z ^ k) from by
            refine tsum_congr (fun k => ?_)
            rw [PowerSeries.coeff_derivative]
            push_cast
            ring]
          rw [hdY]
          have hshift := (Work.C17I.tsum_shift_lemmas Gs hC₀pos hR₀pos hGb ((i : ℕ) - 1)
            (lt_trans (hyc z hz) hR₀1)).1
          have hA : (∑' k : ℕ, ((PowerSeries.coeff k Gs : ℚ) : ℂ) * (Work.C17.yC z) ^ k)
              = Gf z := hGf_repr z (Metric.ball_subset_ball (by norm_num) hz)
          have hB : (∑ m ∈ Finset.range ((i : ℕ) - 1),
                ((PowerSeries.coeff m Gs : ℚ) : ℂ) * (Work.C17.yC z) ^ m) = jet i z :=
            (hjet_eval i z).symm
          rw [hA, hB] at hshift
          rw [div_eq_mul_inv, ← hshift]
          have hw : Work.C17.yC z ^ ((i : ℕ) - 1) ≠ 0 :=
            pow_ne_zero _ (Work.C17.yC_ne_zero_iff z (hU0z0 z hz) (hU0z1 z hz))
          field_simp
        rw [hkey]
        ring
    have hFId' : DifferentiableOn ℂ (FI i) (Metric.ball Work.C17.p0C (1/100)) :=
      (hFId i).mono hU0sub
    have hFIdr : ∀ z ∈ Metric.ball Work.C17.p0C (1/100),
        deriv (FI i) z = gd i z * (Gf z - jet i z) := by
      intro z hz
      exact (hFIderiv i z (hU0sub hz)).deriv
    intro z hz
    have h := (Metric.isOpen_ball.eqOn_of_deriv_eq (convex_ball _ _).isPreconnected hΦd hFId'
      (fun w hw => (hΦderiv w hw).trans (hFIdr w hw).symm)
      (Metric.mem_ball_self (by norm_num)) (hFIval i).symm) hz
    exact h.symm
  have hpaΩ : ∀ q : Fin 17, DifferentiableOn ℂ (Work.C17.pAtY (P q)) Ω :=
    fun q => Work.C17.pAtY_differentiableOn_of_ne_one hΩ1 (P q)
  have hFbΩ : ∀ b, DifferentiableOn ℂ (Fb b) Ω :=
    fun b => (Work.C17.Bsubst_differentiableOn b).mono (fun z hz => hSsub hz.1)
  -- the combined function
  set Rfun : ℂ → ℂ := fun z =>
      (∑ k : Fin 4, Work.C17.pAtY (P (Work.C17.gIdx k)) z * Work.C17.DyIter (k : ℕ) Gf z)
        + (∑ b : Fin 7, Work.C17.pAtY (P (Work.C17.bIdx b)) z * Fb b z)
        + (∑ i : Fin 6, Work.C17.pAtY (P (Work.C17.iIdx i)) z * FI i z) with hRfun
  have hDyGf : ∀ k : ℕ, DifferentiableOn ℂ (Work.C17.DyIter k Gf) Ω :=
    fun k => Work.C17.DyIter_differentiableOn hΩopen
      (fun z hz => fun h => hS0 (by rw [← h]; exact hz.1))
      (fun z hz => fun h => hΩ2 z hz h) k hGfd
  have hRfun_d : DifferentiableOn ℂ Rfun Ω := by
    simp only [hRfun]
    refine DifferentiableOn.add (DifferentiableOn.add ?_ ?_) ?_
    · exact DifferentiableOn.fun_sum (fun k _ => (hpaΩ (Work.C17.gIdx k)).mul (hDyGf (k : ℕ)))
    · exact DifferentiableOn.fun_sum (fun b _ => (hpaΩ (Work.C17.bIdx b)).mul (hFbΩ b))
    · exact DifferentiableOn.fun_sum (fun i _ => (hpaΩ (Work.C17.iIdx i)).mul (hFId i))
  have hRfun_U0 : ∀ z ∈ Metric.ball Work.C17.p0C (1/100), Rfun z = 0 := by
    intro z hz
    have hrel := Work.C17I.pullback_rel_disc m n ra rb rab r0 P hrel hbous z (hU0_34 z hz)
    have hsum17 : (∑ i : Fin 17, Work.C17.pAtY (P i) z * PhiS m n ra rb rab r0 i z) = 0 := by
      rw [← hrel]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Work.C17.pAtY, PhiS]
    have hG' : (∑ k : Fin 4, Work.C17.pAtY (P (Work.C17.gIdx k)) z
          * Work.C17.DyIter (k : ℕ) Gf z)
        = (∑ k : Fin 4, Work.C17.pAtY (P (Work.C17.gIdx k)) z
            * PhiS m n ra rb rab r0 (Work.C17.gIdx k) z) :=
      Finset.sum_congr rfl (fun k _ => by rw [hFGid k z hz])
    have hB' : (∑ b : Fin 7, Work.C17.pAtY (P (Work.C17.bIdx b)) z * Fb b z)
        = (∑ b : Fin 7, Work.C17.pAtY (P (Work.C17.bIdx b)) z
            * PhiS m n ra rb rab r0 (Work.C17.bIdx b) z) :=
      Finset.sum_congr rfl (fun b _ => by rw [hFBid b z hz])
    have hI' : (∑ i : Fin 6, Work.C17.pAtY (P (Work.C17.iIdx i)) z * FI i z)
        = (∑ i : Fin 6, Work.C17.pAtY (P (Work.C17.iIdx i)) z
            * PhiS m n ra rb rab r0 (Work.C17.iIdx i) z) :=
      Finset.sum_congr rfl (fun i _ => by rw [hFIid i z hz])
    simp only [hRfun]
    rw [hG', hB', hI', ← Work.C17.sum_fin17_split
      (fun i : Fin 17 => Work.C17.pAtY (P i) z * PhiS m n ra rb rab r0 i z)]
    exact hsum17
  have hRfun_zero : ∀ z ∈ Ω, Rfun z = 0 := by
    intro z hz
    have hana : AnalyticOnNhd ℂ Rfun Ω := hRfun_d.analyticOnNhd hΩopen
    have hev : Rfun =ᶠ[𝓝 Work.C17.p0C] 0 := by
      filter_upwards [Metric.isOpen_ball.mem_nhds
        (Metric.mem_ball_self (by norm_num : (0:ℝ) < 1/100))] with w hw
      exact hRfun_U0 w hw
    exact hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero hΩcvx.isPreconnected hp0Ω hev hz
  have hR0V : ∀ z ∈ Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) ρ,
      (∑ k : Fin 4, Work.C17.pAtY (P (Work.C17.gIdx k)) z * Work.C17.DyIter (k : ℕ) Gf z)
        + (∑ b : Fin 7, Work.C17.pAtY (P (Work.C17.bIdx b)) z * Fb b z)
        + (∑ i : Fin 6, Work.C17.pAtY (P (Work.C17.iIdx i)) z * FI i z) = 0 := by
    intro z hz
    show Rfun z = 0
    exact hRfun_zero z (hVsub z hz)
  refine ⟨J, hJd, hJ0, hJderiv, ?_⟩
  exact Work.C17I.LC_extract (P := P) (s := s) (δ := δ) (ρ := ρ) hδ hs_pos hρhi hδs
    (fun z hz => fun h => Work.C17.zero_notMem_ball_xs m n hm hlt hδ1 (by rw [← h]; exact hz))
    (fun z hz => fun h => Work.C17.two_notMem_ball_xs m n hm hlt hδ2 (by rw [← h]; exact hz))
    hVne (𝔾 := Gf) (κ := κ) hκ hy1d (J := J) hJd (Fb := Fb) hFbd (Gk := fun k => Gk (k : ℕ))
    (fun k => hGkd (k : ℕ)) hGk (FI := FI) (Hn := Hn) hHnd hHn hR0V
