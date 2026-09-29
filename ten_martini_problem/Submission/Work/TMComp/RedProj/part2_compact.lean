import Mathlib
import Submission.Work.TMContract.Components
import Submission.Work.TMComp.RedProj.Basic
import Submission.Work.TMComp.RedProj.FourierAux
import Submission.Work.TMComp.RedProj.ClaimB
import Submission.Work.TMComp.RedProj.Extract
import Submission.Work.TMComp.RedProj.KEnum
import Submission.Work.TMComp.RedProj.bound_all_of_bound_large
import Submission.Work.TMComp.RedProj.volume_eq_zero_of_compact_null
import Submission.Work.TMComp.RedProj.integral_shift_eq_of_periodic_strip
import Submission.Work.TMComp.RedProj.fourierCoeffOn_eq_exp_integral
import Submission.Work.TMComp.RedProj.summable_int_exp_neg
import Submission.Work.TMComp.RedProj.Part2.ExpLowerDioph
import Submission.Work.TMComp.RedProj.Part2.FourierSeriesPointwise
import Submission.Work.TMComp.RedProj.Part2.AnalyticTsumFourier
import Submission.Work.TMComp.RedProj.Part2.GluePolydisc

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# C11 part 2 (AJ Thm 4.2(2)): the compact form, with the complexification machinery.

This file proves `Work.TMComp.RedProj.part2_compact` (a lemma of the Ten Martini project).
It builds, from scratch, the complexification of a jointly real-analytic function of two real
variables, the exponential decay of Fourier coefficients on a strip, and the Cartan-type
assembly, using the auxiliary lemmas in `Submission/Work/TMComp/RedProj/Part2/`.
-/

open MeasureTheory Filter Topology Set intervalIntegral
open scoped NNReal ENNReal

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Work.TMComp.RedProj

open Work.TMContract

/-- `‖(x : ℂ)‖ = |x|`. -/
theorem norm_ofRealC (x : ℝ) : ‖(x:ℂ)‖ = |x| := by simp

theorem dist_ofRealC (x y : ℝ) : dist (x:ℂ) (y:ℂ) = dist x y := by
  rw [Real.dist_eq, Complex.dist_eq]
  have h : (x:ℂ) - (y:ℂ) = ((x - y : ℝ) : ℂ) := by push_cast; ring
  rw [h, norm_ofRealC]

/-- A nonempty intersection of two balls with real centres contains a real point. -/
theorem exists_real_mem_ball_inter {a a' s s' : ℝ}
    (hne : (Metric.ball (a:ℂ) s ∩ Metric.ball (a':ℂ) s').Nonempty) :
    ∃ x : ℝ, (x:ℂ) ∈ Metric.ball (a:ℂ) s ∩ Metric.ball (a':ℂ) s' := by
  obtain ⟨z, hz⟩ := hne
  have hz1 : dist z (a:ℂ) < s := Metric.mem_ball.mp hz.1
  have hz2 : dist z (a':ℂ) < s' := Metric.mem_ball.mp hz.2
  refine ⟨z.re, ?_, ?_⟩
  · rw [Metric.mem_ball, Complex.dist_eq]
    have heq : (z.re:ℂ) - (a:ℂ) = (((z - (a:ℂ)).re : ℝ) : ℂ) := by
      rw [Complex.sub_re, Complex.ofReal_re, Complex.ofReal_sub]
    calc ‖(z.re:ℂ) - (a:ℂ)‖ = ‖(((z - (a:ℂ)).re : ℝ) : ℂ)‖ := by rw [heq]
      _ = |(z - (a:ℂ)).re| := norm_ofRealC _
      _ ≤ ‖z - (a:ℂ)‖ := Complex.abs_re_le_norm _
      _ < s := by rw [Complex.dist_eq] at hz1; exact hz1
  · rw [Metric.mem_ball, Complex.dist_eq]
    have heq : (z.re:ℂ) - (a':ℂ) = (((z - (a':ℂ)).re : ℝ) : ℂ) := by
      rw [Complex.sub_re, Complex.ofReal_re, Complex.ofReal_sub]
    calc ‖(z.re:ℂ) - (a':ℂ)‖ = ‖(((z - (a':ℂ)).re : ℝ) : ℂ)‖ := by rw [heq]
      _ = |(z - (a':ℂ)).re| := norm_ofRealC _
      _ ≤ ‖z - (a':ℂ)‖ := Complex.abs_re_le_norm _
      _ < s' := by rw [Complex.dist_eq] at hz2; exact hz2

/-- Distance from `x` to the lattice `X + ℤ`. -/
def tubeLatDist (X x : ℝ) : ℝ := Metric.infDist x (Set.range (fun n : ℤ => X + (n : ℝ)))

/-- Vertical reach of the periodic tube `⋃ n, ball (X + n) t` at real coordinate `x`. -/
def tubeReach (X t x : ℝ) : ℝ := Real.sqrt (max 0 (t ^ 2 - (tubeLatDist X x) ^ 2))

lemma tubeLatDist_nonneg (X x : ℝ) : 0 ≤ tubeLatDist X x := Metric.infDist_nonneg

lemma tubeLatDist_le_abs (X x : ℝ) : tubeLatDist X x ≤ |x - X| := by
  have h : (X + ((0 : ℤ) : ℝ)) ∈ Set.range (fun n : ℤ => X + (n : ℝ)) := Set.mem_range_self 0
  have := Metric.infDist_le_dist_of_mem (x := x) h
  simpa [tubeLatDist, Real.dist_eq] using this

lemma tubeLatDist_continuous (X : ℝ) : Continuous (fun x => tubeLatDist X x) := by
  unfold tubeLatDist
  exact Metric.continuous_infDist_pt _

lemma tubeReach_continuous (X t : ℝ) : Continuous (fun x => tubeReach X t x) := by
  have h1 : Continuous (fun x => (tubeLatDist X x) ^ 2) := (tubeLatDist_continuous X).pow 2
  have h2 : Continuous (fun x => max 0 (t ^ 2 - (tubeLatDist X x) ^ 2)) :=
    Continuous.max continuous_const (continuous_const.sub h1)
  have h3 : Continuous (fun x => Real.sqrt (max 0 (t ^ 2 - (tubeLatDist X x) ^ 2))) :=
    Real.continuous_sqrt.comp h2
  simpa only [tubeReach] using h3

lemma tubeReach_pos {X t x : ℝ} (ht : 0 < t) (hx : |x - X| < t) : 0 < tubeReach X t x := by
  have hd : tubeLatDist X x < t := lt_of_le_of_lt (tubeLatDist_le_abs X x) hx
  have hnn : 0 ≤ tubeLatDist X x := tubeLatDist_nonneg X x
  have hpos : 0 < t ^ 2 - (tubeLatDist X x) ^ 2 := by nlinarith
  rw [tubeReach, Real.sqrt_pos]
  exact lt_of_lt_of_le hpos (le_max_right _ _)

lemma tubeReach_gt_iff_quad {X t x y : ℝ} (hy : 0 ≤ y) :
    y < tubeReach X t x ↔ (tubeLatDist X x) ^ 2 + y ^ 2 < t ^ 2 := by
  rw [tubeReach, Real.lt_sqrt hy, lt_max_iff]
  constructor
  · rintro (h | h)
    · linarith [sq_nonneg y]
    · linarith
  · intro h; right; linarith

/-- Covering a periodic tube by a finite family of polydiscs (infimum-distance argument). -/
theorem TubeCoverMain {ι : Type*} [Fintype ι] (c d : ℝ) (hcd : c ≤ d)
    (E X s t : ι → ℝ) (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i)
    (hcover : ∀ E₀ ∈ Set.Icc c d, ∀ x₀ ∈ Set.Icc (0:ℝ) 1, ∃ i, |E₀ - E i| < s i ∧ |x₀ - X i| < t i) :
    ∃ Δ : Set ℂ, IsOpen Δ ∧ (Set.Icc c d : Set ℝ) ⊆ {E | (E : ℂ) ∈ Δ} ∧
      ∃ ρ : ℝ, 0 < ρ ∧ (Δ ×ˢ {w : ℂ | |w.im| < ρ}) ⊆
        ⋃ i, ⋃ n : ℤ, (Metric.ball (E i : ℂ) (s i) ×ˢ Metric.ball (((X i + n : ℝ) : ℂ)) (t i)) := by
  classical
  have hc : c ∈ Set.Icc c d := ⟨le_refl c, hcd⟩
  have h0 : (0 : ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
  obtain ⟨i₀, _⟩ := hcover c hc 0 h0
  haveI : Nonempty ι := ⟨i₀⟩
  let M : ℝ × ℝ → ℝ := fun p =>
    Finset.univ.sup' Finset.univ_nonempty
      (fun i => min (s i - |p.1 - E i|) (tubeReach (X i) (t i) p.2))
  have hMcont : Continuous M := by
    change Continuous (fun p : ℝ × ℝ => Finset.univ.sup' Finset.univ_nonempty
      (fun i => min (s i - |p.1 - E i|) (tubeReach (X i) (t i) p.2)))
    apply Continuous.finset_sup'_apply
    intro i _
    exact (continuous_const.sub ((continuous_fst.sub continuous_const).abs)).min
      ((tubeReach_continuous (X i) (t i)).comp continuous_snd)
  have hMpos : ∀ p ∈ (Set.Icc c d ×ˢ Set.Icc (0:ℝ) 1), 0 < M p := by
    rintro ⟨E₀, x⟩ ⟨hE₀, hx⟩
    obtain ⟨i, hi1, hi2⟩ := hcover E₀ hE₀ x hx
    have hreach : 0 < tubeReach (X i) (t i) x := tubeReach_pos (ht i) hi2
    have hterm : 0 < min (s i - |E₀ - E i|) (tubeReach (X i) (t i) x) :=
      lt_min (by linarith) hreach
    have hle := Finset.le_sup' (s := (Finset.univ : Finset ι))
      (f := fun i => min (s i - |E₀ - E i|) (tubeReach (X i) (t i) x)) (Finset.mem_univ i)
    change 0 < Finset.univ.sup' Finset.univ_nonempty
      (fun i => min (s i - |E₀ - E i|) (tubeReach (X i) (t i) x))
    exact lt_of_lt_of_le hterm hle
  obtain ⟨ρ, hρpos, hρ⟩ := (isCompact_Icc.prod isCompact_Icc).exists_forall_le'
    hMcont.continuousOn (a := 0) hMpos
  let Δ : Set ℂ := {z | ∃ p ∈ Set.Icc c d, dist z (p : ℂ) < ρ / 2}
  have hOpenΔ : IsOpen Δ := by
    refine isOpen_iff_mem_nhds.2 fun z hz => ?_
    obtain ⟨p, hp, hzp⟩ := hz
    exact Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hzp) (fun y hy => ⟨p, hp, hy⟩)
  have hsubΔ : (Set.Icc c d : Set ℝ) ⊆ {E | (E : ℂ) ∈ Δ} := by
    intro e he
    refine ⟨e, he, ?_⟩
    rw [dist_self]
    exact half_pos hρpos
  refine ⟨Δ, hOpenΔ, hsubΔ, ρ / 2, half_pos hρpos, ?_⟩
  have hExt : ∀ z ∈ Δ, ∀ x ∈ Set.Icc (0:ℝ) 1,
      ∃ i, s i - dist z (E i : ℂ) > ρ / 2 ∧ tubeReach (X i) (t i) x ≥ ρ := by
    rintro z ⟨p, hp, hzp⟩ x hx
    have hMp : ρ ≤ M (p, x) := hρ (p, x) ⟨hp, hx⟩
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset ι))
      Finset.univ_nonempty (fun i => min (s i - |p - E i|) (tubeReach (X i) (t i) x))
    have hMp' : ρ ≤ min (s i - |p - E i|) (tubeReach (X i) (t i) x) := by
      rw [← hi]; exact hMp
    refine ⟨i, ?_, le_trans hMp' (min_le_right _ _)⟩
    have h1 : ρ ≤ s i - |p - E i| := le_trans hMp' (min_le_left _ _)
    have hdp : dist (p : ℂ) (E i : ℂ) = |p - E i| := by
      rw [dist_eq_norm, show (p : ℂ) - (E i : ℂ) = ((p - E i : ℝ) : ℂ) by push_cast; ring,
        norm_ofRealC]
    have htri : dist z (E i : ℂ) ≤ dist z (p : ℂ) + |p - E i| := by
      calc dist z (E i : ℂ) ≤ dist z (p : ℂ) + dist (p : ℂ) (E i : ℂ) := dist_triangle _ _ _
        _ = dist z (p : ℂ) + |p - E i| := by rw [hdp]
    linarith
  rintro ⟨z, w⟩ ⟨hzΔ, hw⟩
  have hwim : |w.im| < ρ / 2 := hw
  set m : ℤ := ⌊w.re⌋ with hm
  set w' : ℂ := w - (m : ℂ) with hw'
  have hwre : w'.re = w.re - m := by simp [hw', Complex.sub_re]
  have hxim : w'.im = w.im := by simp [hw', Complex.sub_im]
  have hx0 : 0 ≤ w'.re := by
    rw [hwre]; have := Int.floor_le w.re; push_cast; linarith
  have hx1 : w'.re ≤ 1 := by
    rw [hwre]; have := Int.lt_floor_add_one w.re; push_cast at this; linarith
  obtain ⟨i, hsi, hri⟩ := hExt z hzΔ w'.re ⟨hx0, hx1⟩
  have hreach_gt : |w'.im| < tubeReach (X i) (t i) w'.re := by
    rw [hxim]
    linarith [hri, hρpos]
  have hquad : (tubeLatDist (X i) w'.re) ^ 2 + (w'.im) ^ 2 < (t i) ^ 2 := by
    have h := (tubeReach_gt_iff_quad (abs_nonneg (w'.im))).1 hreach_gt
    rwa [sq_abs] at h
  have hlt : tubeLatDist (X i) w'.re < Real.sqrt ((t i) ^ 2 - (w'.im) ^ 2) := by
    rw [Real.lt_sqrt (tubeLatDist_nonneg (X i) w'.re)]
    linarith
  obtain ⟨c', hc', hcdist⟩ := (Metric.infDist_lt_iff (s := Set.range (fun n : ℤ => X i + (n : ℝ)))
    ⟨_, Set.mem_range_self 0⟩).1 (by simpa only [tubeLatDist] using hlt)
  obtain ⟨n₀, rfl⟩ := hc'
  have hball' : w' ∈ Metric.ball (((X i + n₀ : ℝ) : ℂ)) (t i) := by
    rw [Metric.mem_ball, Complex.dist_eq_re_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
    rw [Real.sqrt_lt' (ht i)]
    have hasq : (w'.re - (X i + n₀ : ℝ)) ^ 2 < (t i) ^ 2 - (w'.im) ^ 2 := by
      have h := (Real.lt_sqrt (abs_nonneg (w'.re - (X i + n₀ : ℝ)))).1
        (by rw [Real.dist_eq] at hcdist; exact hcdist)
      rwa [sq_abs] at h
    linarith [sq_nonneg (w'.im)]
  have hzball : z ∈ Metric.ball (E i : ℂ) (s i) := by
    rw [Metric.mem_ball]; linarith
  have hcast : ((((X i : ℝ) + ((n₀ + m : ℤ) : ℝ) : ℝ) : ℂ)) = (((X i + n₀ : ℝ) : ℂ)) + (m : ℂ) := by
    push_cast; ring
  have hwball : w ∈ Metric.ball ((((X i : ℝ) + ((n₀ + m : ℤ) : ℝ) : ℝ) : ℂ)) (t i) := by
    rw [hcast, show w = w' + (m : ℂ) by rw [hw']; abel, Metric.mem_ball, dist_add_right]
    exact Metric.mem_ball.1 hball'
  exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨n₀ + m, hzball, hwball⟩⟩


def e1 : ℝ × ℝ := (1, 0)
def e2 : ℝ × ℝ := (0, 1)

@[simp] theorem norm_e1 : ‖e1‖ = 1 := by simp [e1]
@[simp] theorem norm_e2 : ‖e2‖ = 1 := by simp [e2]

/-- An `n`-fold `ℂ`-multilinear "monomial" `w ↦ ∏ j, (if ε j then (w j).2 else (w j).1)`. -/
def monoMLM (n : ℕ) (ε : Fin n → Bool) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => ℂ × ℂ) ℂ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).compContinuousLinearMap
    (fun j => if ε j then ContinuousLinearMap.snd ℂ ℂ ℂ else ContinuousLinearMap.fst ℂ ℂ ℂ)

theorem monoMLM_apply (n : ℕ) (ε : Fin n → Bool) (w : Fin n → ℂ × ℂ) :
    monoMLM n ε w = ∏ j, (if ε j then (w j).2 else (w j).1) := by
  simp only [monoMLM, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply]
  apply Finset.prod_congr rfl
  intro j _
  by_cases h : ε j <;> simp [h]

/-- The complexified formal power series. -/
def cplxSeries (p : FormalMultilinearSeries ℝ (ℝ × ℝ) ℂ) : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ :=
  fun n => ∑ ε : Fin n → Bool, (p n (fun j => if ε j then e2 else e1)) • monoMLM n ε

theorem norm_monoMLM (n : ℕ) (ε : Fin n → Bool) : ‖monoMLM n ε‖ ≤ 1 := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by norm_num) fun w => ?_
  rw [monoMLM_apply, one_mul]
  calc ‖∏ j, (if ε j then (w j).2 else (w j).1)‖
      = ∏ j, ‖(if ε j then (w j).2 else (w j).1)‖ := norm_prod _ _
    _ ≤ ∏ j, ‖w j‖ := by
        refine Finset.prod_le_prod₀ (fun j _ => ?_) (fun j _ => ?_)
        · by_cases h : ε j <;> simp [h]
        · by_cases h : ε j <;> simp [h, norm_fst_le, norm_snd_le]

theorem cplxSeries_norm_le (p : FormalMultilinearSeries ℝ (ℝ × ℝ) ℂ) (n : ℕ) :
    ‖cplxSeries p n‖ ≤ 2 ^ n * ‖p n‖ := by
  have h1 : ∀ ε : Fin n → Bool, ‖p n (fun j => if ε j then e2 else e1)‖ ≤ ‖p n‖ := by
    intro ε
    refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
    have h : ∏ j : Fin n, ‖(if ε j then e2 else e1)‖ = 1 := by
      apply Finset.prod_eq_one
      intro j _
      by_cases h : ε j <;> simp [h]
    rw [h, mul_one]
  have h2 : ∀ (ε : Fin n → Bool) (w : Fin n → ℂ × ℂ),
      ‖monoMLM n ε w‖ ≤ ∏ j, ‖w j‖ := by
    intro ε w
    rw [monoMLM_apply]
    calc ‖∏ j, (if ε j then (w j).2 else (w j).1)‖
        = ∏ j, ‖(if ε j then (w j).2 else (w j).1)‖ := norm_prod _ _
      _ ≤ ∏ j, ‖w j‖ := by
          refine Finset.prod_le_prod₀ (fun j _ => ?_) (fun j _ => ?_)
          · by_cases h : ε j <;> simp [h]
          · by_cases h : ε j <;> simp [h, norm_fst_le, norm_snd_le]
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun w => ?_
  have hsum : (cplxSeries p n) w
      = ∑ ε : Fin n → Bool, (p n (fun j => if ε j then e2 else e1)) * monoMLM n ε w := by
    simp only [cplxSeries, ContinuousMultilinearMap.sum_apply,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [hsum]
  calc ‖∑ ε : Fin n → Bool, (p n (fun j => if ε j then e2 else e1)) * monoMLM n ε w‖
      ≤ ∑ ε : Fin n → Bool, ‖(p n (fun j => if ε j then e2 else e1)) * monoMLM n ε w‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _ε : Fin n → Bool, ‖p n‖ * ∏ j, ‖w j‖ := by
        refine Finset.sum_le_sum fun ε _ => ?_
        rw [norm_mul]
        exact mul_le_mul (h1 ε) (h2 ε w) (norm_nonneg _) (norm_nonneg _)
    _ = (2 ^ n * ‖p n‖) * ∏ j, ‖w j‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun]
        simp only [Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul]
        push_cast
        ring

theorem ofReal_prod_ite {n : ℕ} (ε : Fin n → Bool) (a b : ℝ) :
    ((∏ j, if ε j then b else a : ℝ) : ℂ) = ∏ j, (if ε j then (b : ℂ) else (a : ℂ)) := by
  rw [Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro j _
  by_cases h : ε j <;> simp [h]

theorem cplxSeries_diag (p : FormalMultilinearSeries ℝ (ℝ × ℝ) ℂ) (n : ℕ) (a b : ℝ) :
    (cplxSeries p n) (fun _ => ((a : ℂ), (b : ℂ))) = p n (fun _ => ((a, b) : ℝ × ℝ)) := by
  have hR : p n (fun _ : Fin n => ((a, b) : ℝ × ℝ))
      = ∑ ε : Fin n → Bool,
          ((∏ j, if ε j then b else a : ℝ) : ℂ) * p n (fun j => if ε j then e2 else e1) := by
    have hexp : (fun _ : Fin n => ((a, b) : ℝ × ℝ))
        = fun i => ∑ j : Bool, (if j then b • e2 else a • e1) := by
      funext i
      rw [Fintype.sum_bool]
      simp [e1, e2]
    rw [hexp, ContinuousMultilinearMap.map_sum]
    apply Finset.sum_congr rfl
    intro ε _
    rw [show (fun i : Fin n => if ε i then b • e2 else a • e1)
        = (fun i => (if ε i then b else a) • (if ε i then e2 else e1)) from by
          funext i; by_cases h : ε i <;> simp [h]]
    rw [ContinuousMultilinearMap.map_smul_univ, Complex.real_smul]
  have hL : (cplxSeries p n) (fun _ => ((a : ℂ), (b : ℂ)))
      = ∑ ε : Fin n → Bool,
          ((∏ j, if ε j then b else a : ℝ) : ℂ) * p n (fun j => if ε j then e2 else e1) := by
    simp only [cplxSeries, ContinuousMultilinearMap.sum_apply,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro ε _
    rw [monoMLM_apply, ← ofReal_prod_ite]
    ring
  rw [hL, hR]


theorem complexify_analyticAt_local (f : ℝ × ℝ → ℂ) (x₀ : ℝ × ℝ) (hf : AnalyticAt ℝ f x₀) :
    ∃ (r : ℝ) (_ : 0 < r) (F : ℂ × ℂ → ℂ),
      AnalyticOnNhd ℂ F (Metric.ball ((x₀.1 : ℂ), (x₀.2 : ℂ)) r) ∧
      (∀ x : ℝ × ℝ, x ∈ Metric.ball x₀ r → F ((x.1 : ℂ), (x.2 : ℂ)) = f x) := by
  obtain ⟨p, r₀, hp⟩ := hf
  have hr₀ne : min r₀ 1 ≠ ⊤ := ne_of_lt (lt_of_le_of_lt (min_le_right _ _) ENNReal.one_lt_top)
  set r₁ : ℝ≥0 := (min r₀ 1).toNNReal with hr₁
  have hr₁coe : (r₁ : ENNReal) = min r₀ 1 := ENNReal.coe_toNNReal hr₀ne
  have hr₁pos : 0 < r₁ := by
    refine ENNReal.toNNReal_pos ?_ hr₀ne
    exact ne_of_gt (lt_min hp.r_pos (by norm_num))
  have hr₁le : (r₁ : ENNReal) ≤ r₀ := by rw [hr₁coe]; exact min_le_left _ _
  set R : ℝ≥0 := r₁ / 4 with hR
  have hRpos : 0 < R := by rw [hR]; positivity
  have hRle : (R : ENNReal) ≤ r₀ := by
    have h1 : (R : ENNReal) ≤ (r₁ : ENNReal) := by
      rw [ENNReal.coe_le_coe, hR]; exact div_le_self hr₁pos.le (by norm_num)
    exact le_trans h1 hr₁le
  have hRlt : (R : ENNReal) < p.radius := by
    have h1 : (R : ENNReal) < (r₁ : ENNReal) := by
      rw [ENNReal.coe_lt_coe, hR]; exact div_lt_self hr₁pos (by norm_num)
    exact lt_of_lt_of_le h1 (le_trans hr₁le hp.r_le)
  have hhalflt : ((r₁ / 2 : ℝ≥0) : ENNReal) < p.radius := by
    have h1 : ((r₁ / 2 : ℝ≥0) : ENNReal) < (r₁ : ENNReal) := by
      rw [ENNReal.coe_lt_coe]; exact half_lt_self hr₁pos
    exact lt_of_lt_of_le h1 (le_trans hr₁le hp.r_le)
  obtain ⟨C, hCpos, hC⟩ := p.norm_mul_pow_le_of_lt_radius hhalflt
  have hRval : ((R : ℝ≥0) : ℝ) = (r₁ : ℝ) / 4 := by rw [hR]; push_cast; ring
  have hhalfval : (((r₁ / 2 : ℝ≥0)) : ℝ) = (r₁ : ℝ) / 2 := by push_cast; ring
  have hQbound : ∀ n : ℕ, ‖cplxSeries p n‖ * ((R : ℝ≥0) : ℝ) ^ n ≤ C := by
    intro n
    calc ‖cplxSeries p n‖ * ((R : ℝ≥0) : ℝ) ^ n
        ≤ (2 ^ n * ‖p n‖) * ((R : ℝ≥0) : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right (cplxSeries_norm_le p n) (by positivity)
      _ = ‖p n‖ * (((r₁ / 2 : ℝ≥0)) : ℝ) ^ n := by
          rw [hRval, hhalfval]
          have : (2:ℝ) ^ n * ((r₁:ℝ)/4) ^ n = ((r₁:ℝ)/2) ^ n := by
            rw [← mul_pow]; congr 1; ring
          linear_combination ‖p n‖ * this
      _ ≤ C := hC n
  have hQle : (R : ENNReal) ≤ (cplxSeries p).radius :=
    FormalMultilinearSeries.le_radius_of_bound (cplxSeries p) C hQbound
  have hQball : HasFPowerSeriesOnBall (cplxSeries p).sum (cplxSeries p) 0 (R : ENNReal) := by
    refine ⟨hQle, ?_, fun {y} hy => ?_⟩
    · rw [ENNReal.coe_pos]; exact hRpos
    · have hy' : y ∈ Metric.eball (0 : ℂ × ℂ) (cplxSeries p).radius := lt_of_lt_of_le hy hQle
      have := ((cplxSeries p).summable_norm_apply hy').of_norm.hasSum
      simpa only [FormalMultilinearSeries.sum, zero_add] using this
  have hQan : AnalyticOnNhd ℂ (cplxSeries p).sum (Metric.eball (0 : ℂ × ℂ) (R : ENNReal)) :=
    hQball.analyticOnNhd
  refine ⟨(R : ℝ), hRpos, fun w => (cplxSeries p).sum (w - ((x₀.1 : ℂ), (x₀.2 : ℂ))), ?_, ?_⟩
  · have hg : AnalyticOnNhd ℂ (fun w : ℂ × ℂ => w - ((x₀.1 : ℂ), (x₀.2 : ℂ)))
        (Metric.ball ((x₀.1 : ℂ), (x₀.2 : ℂ)) (R : ℝ)) :=
      fun w _ => analyticAt_id.sub analyticAt_const
    refine hQan.comp hg (fun w hw => ?_)
    rw [Metric.mem_eball, edist_dist, dist_zero_right]
    have hd : ‖w - ((x₀.1 : ℂ), (x₀.2 : ℂ))‖ = dist w ((x₀.1 : ℂ), (x₀.2 : ℂ)) := by
      rw [dist_eq_norm]
    rw [hd, ← ENNReal.ofReal_coe_nnreal (p := R)]
    exact (ENNReal.ofReal_lt_ofReal_iff hRpos).mpr (Metric.mem_ball.mp hw)
  · intro x hx
    have hx' : ‖x - x₀‖ < (R : ℝ) := by
      rw [← dist_eq_norm]; exact Metric.mem_ball.mp hx
    have hx₀mem : x - x₀ ∈ Metric.eball (0 : ℝ × ℝ) r₀ := by
      rw [Metric.mem_eball, edist_dist, dist_zero_right]
      refine lt_of_lt_of_le ?_ hRle
      rw [← ENNReal.ofReal_coe_nnreal (p := R)]
      exact (ENNReal.ofReal_lt_ofReal_iff hRpos).mpr hx'
    have hfval : f x = p.sum (x - x₀) := by
      rw [FormalMultilinearSeries.sum]
      have h := (hp.hasSum hx₀mem).tsum_eq
      rw [h]
      congr 1
      abel
    have hv : (((x.1 : ℂ), (x.2 : ℂ)) - ((x₀.1 : ℂ), (x₀.2 : ℂ)))
        = (((x.1 - x₀.1 : ℝ) : ℂ), ((x.2 - x₀.2 : ℝ) : ℂ)) := by
      ext <;> simp [sub_eq_add_neg]
    rw [hfval]
    show (cplxSeries p).sum _ = p.sum (x - x₀)
    rw [FormalMultilinearSeries.sum, FormalMultilinearSeries.sum, hv]
    apply tsum_congr
    intro n
    rw [cplxSeries_diag]
    congr 1


theorem agree_real_polydisc {a a' b b' s s' t t' : ℝ} {F F' : ℂ × ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F (Metric.ball (a:ℂ) s ×ˢ Metric.ball (b:ℂ) t))
    (hF' : AnalyticOnNhd ℂ F' (Metric.ball (a':ℂ) s' ×ˢ Metric.ball (b':ℂ) t'))
    (hne : ((Metric.ball (a:ℂ) s ×ˢ Metric.ball (b:ℂ) t) ∩
        (Metric.ball (a':ℂ) s' ×ˢ Metric.ball (b':ℂ) t')).Nonempty)
    (hreal : ∀ x y : ℝ, (x:ℂ) ∈ Metric.ball (a:ℂ) s → (y:ℂ) ∈ Metric.ball (b:ℂ) t →
        (x:ℂ) ∈ Metric.ball (a':ℂ) s' → (y:ℂ) ∈ Metric.ball (b':ℂ) t' →
        F ((x:ℂ),(y:ℂ)) = F' ((x:ℂ),(y:ℂ))) :
    Set.EqOn F F' ((Metric.ball (a:ℂ) s ×ˢ Metric.ball (b:ℂ) t) ∩
        (Metric.ball (a':ℂ) s' ×ˢ Metric.ball (b':ℂ) t')) := by
  obtain ⟨p, hp⟩ := hne
  simp only [Set.mem_inter_iff, Set.mem_prod] at hp
  have hp1 : p.1 ∈ Metric.ball (a:ℂ) s ∩ Metric.ball (a':ℂ) s' := ⟨hp.1.1, hp.2.1⟩
  have hp2 : p.2 ∈ Metric.ball (b:ℂ) t ∩ Metric.ball (b':ℂ) t' := ⟨hp.1.2, hp.2.2⟩
  obtain ⟨x₀, hx₀⟩ := exists_real_mem_ball_inter ⟨p.1, hp1⟩
  obtain ⟨y₀, hy₀⟩ := exists_real_mem_ball_inter ⟨p.2, hp2⟩
  have step2 : ∀ y : ℝ, (y:ℂ) ∈ Metric.ball (b:ℂ) t ∩ Metric.ball (b':ℂ) t' →
      ∀ z ∈ Metric.ball (a:ℂ) s ∩ Metric.ball (a':ℂ) s', F (z, (y:ℂ)) = F' (z, (y:ℂ)) := by
    intro y hy z hz
    have hFy : AnalyticOnNhd ℂ (fun z => F (z, (y:ℂ)))
        (Metric.ball (a:ℂ) s ∩ Metric.ball (a':ℂ) s') := by
      intro w hw
      exact (hF (w, (y:ℂ)) ⟨hw.1, hy.1⟩).comp (f := fun z : ℂ => (z, (y:ℂ)))
        (analyticAt_id.prod (analyticAt_const (v := (y:ℂ))))
    have hF'y : AnalyticOnNhd ℂ (fun z => F' (z, (y:ℂ)))
        (Metric.ball (a:ℂ) s ∩ Metric.ball (a':ℂ) s') := by
      intro w hw
      exact (hF' (w, (y:ℂ)) ⟨hw.2, hy.2⟩).comp (f := fun z : ℂ => (z, (y:ℂ)))
        (analyticAt_id.prod (analyticAt_const (v := (y:ℂ))))
    have hApre : IsPreconnected (Metric.ball (a:ℂ) s ∩ Metric.ball (a':ℂ) s') :=
      ((convex_ball (a:ℂ) s).inter (convex_ball (a':ℂ) s')).isPreconnected
    refine (hFy.eqOn_of_preconnected_of_mem_closure hF'y hApre hx₀ ?_) hz
    have hAopen : IsOpen (Metric.ball (a:ℂ) s ∩ Metric.ball (a':ℂ) s') :=
      Metric.isOpen_ball.inter Metric.isOpen_ball
    obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp (hAopen.mem_nhds hx₀)
    refine Metric.mem_closure_iff.mpr fun ε hε => ?_
    set x : ℝ := x₀ + min δ ε / 2 with hx
    have hminpos : 0 < min δ ε := lt_min hδpos hε
    have hxd : dist x x₀ < δ := by
      rw [Real.dist_eq, hx, abs_lt]; constructor <;> linarith [min_le_left δ ε, hminpos]
    have hxe : dist x x₀ < ε := by
      rw [Real.dist_eq, hx, abs_lt]; constructor <;> linarith [min_le_right δ ε, hminpos]
    have hxne : (x:ℂ) ≠ x₀ := by
      intro h
      have hx' : x = x₀ := by exact_mod_cast h
      have h2 : min δ ε / 2 = 0 := by linarith [hx]
      linarith
    have hxA : (x:ℂ) ∈ Metric.ball (a:ℂ) s ∩ Metric.ball (a':ℂ) s' :=
      hδsub (Metric.mem_ball.mpr (by rw [dist_ofRealC]; exact hxd))
    have hxreal : F ((x:ℂ), (y:ℂ)) = F' ((x:ℂ), (y:ℂ)) := hreal x y hxA.1 hy.1 hxA.2 hy.2
    exact ⟨(x:ℂ), ⟨hxreal, hxne⟩, by rw [dist_ofRealC, dist_comm]; exact hxe⟩
  intro q hq
  simp only [Set.mem_inter_iff, Set.mem_prod] at hq
  have hq1 : q.1 ∈ Metric.ball (a:ℂ) s ∩ Metric.ball (a':ℂ) s' := ⟨hq.1.1, hq.2.1⟩
  have hq2 : q.2 ∈ Metric.ball (b:ℂ) t ∩ Metric.ball (b':ℂ) t' := ⟨hq.1.2, hq.2.2⟩
  have hFz : AnalyticOnNhd ℂ (fun w => F (q.1, w)) (Metric.ball (b:ℂ) t ∩ Metric.ball (b':ℂ) t') := by
    intro w hw
    exact (hF (q.1, w) ⟨hq1.1, hw.1⟩).comp
      ((analyticAt_const (v := q.1)).prod analyticAt_id)
  have hF'z : AnalyticOnNhd ℂ (fun w => F' (q.1, w)) (Metric.ball (b:ℂ) t ∩ Metric.ball (b':ℂ) t') := by
    intro w hw
    exact (hF' (q.1, w) ⟨hq1.2, hw.2⟩).comp
      ((analyticAt_const (v := q.1)).prod analyticAt_id)
  have hBpre : IsPreconnected (Metric.ball (b:ℂ) t ∩ Metric.ball (b':ℂ) t') :=
    ((convex_ball (b:ℂ) t).inter (convex_ball (b':ℂ) t')).isPreconnected
  refine (hFz.eqOn_of_preconnected_of_mem_closure hF'z hBpre hy₀ ?_) hq2
  have hBopen : IsOpen (Metric.ball (b:ℂ) t ∩ Metric.ball (b':ℂ) t') :=
    Metric.isOpen_ball.inter Metric.isOpen_ball
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp (hBopen.mem_nhds hy₀)
  refine Metric.mem_closure_iff.mpr fun ε hε => ?_
  set y : ℝ := y₀ + min δ ε / 2 with hy
  have hminpos : 0 < min δ ε := lt_min hδpos hε
  have hyd : dist y y₀ < δ := by
    rw [Real.dist_eq, hy, abs_lt]; constructor <;> linarith [min_le_left δ ε, hminpos]
  have hye : dist y y₀ < ε := by
    rw [Real.dist_eq, hy, abs_lt]; constructor <;> linarith [min_le_right δ ε, hminpos]
  have hyne : (y:ℂ) ≠ y₀ := by
    intro h
    have hy' : y = y₀ := by exact_mod_cast h
    have h2 : min δ ε / 2 = 0 := by linarith [hy]
    linarith
  have hyB : (y:ℂ) ∈ Metric.ball (b:ℂ) t ∩ Metric.ball (b':ℂ) t' :=
    hδsub (Metric.mem_ball.mpr (by rw [dist_ofRealC]; exact hyd))
  exact ⟨(y:ℂ), ⟨step2 y hyB q.1 hq1, hyne⟩, by rw [dist_ofRealC, dist_comm]; exact hye⟩

/-- Glue a family of holomorphic functions on overlapping polydiscs with real centres. -/
theorem GluePolydiscSingle {ι : Type*} (a b s t : ι → ℝ) (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i)
    (F : ι → ℂ × ℂ → ℂ)
    (hF : ∀ i, AnalyticOnNhd ℂ (F i) (Metric.ball (a i : ℂ) (s i) ×ˢ Metric.ball (b i : ℂ) (t i)))
    (hagree : ∀ i j, ((Metric.ball (a i : ℂ) (s i) ×ˢ Metric.ball (b i : ℂ) (t i)) ∩
        (Metric.ball (a j : ℂ) (s j) ×ˢ Metric.ball (b j : ℂ) (t j))).Nonempty →
        Set.EqOn (F i) (F j)
          ((Metric.ball (a i : ℂ) (s i) ×ˢ Metric.ball (b i : ℂ) (t i)) ∩
           (Metric.ball (a j : ℂ) (s j) ×ˢ Metric.ball (b j : ℂ) (t j)))) :
    ∃ G : ℂ × ℂ → ℂ,
      AnalyticOnNhd ℂ G (⋃ i, Metric.ball (a i : ℂ) (s i) ×ˢ Metric.ball (b i : ℂ) (t i)) ∧
      ∀ i, Set.EqOn G (F i) (Metric.ball (a i : ℂ) (s i) ×ˢ Metric.ball (b i : ℂ) (t i)) := by
  classical
  by_cases hne : Nonempty ι
  · obtain ⟨i₀⟩ := hne
    have hex : ∀ p : ℂ × ℂ, ∃ i : ι,
        p ∈ (⋃ j, Metric.ball (a j : ℂ) (s j) ×ˢ Metric.ball (b j : ℂ) (t j)) →
        p ∈ Metric.ball (a i : ℂ) (s i) ×ˢ Metric.ball (b i : ℂ) (t i) := by
      intro p
      by_cases hp : p ∈ (⋃ j, Metric.ball (a j : ℂ) (s j) ×ˢ Metric.ball (b j : ℂ) (t j))
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
        exact ⟨i, fun _ => hi⟩
      · exact ⟨i₀, fun h => absurd h hp⟩
    choose ii hii using hex
    refine ⟨fun p => F (ii p) p, ?_, ?_⟩
    · intro p hp
      have hpP : p ∈ Metric.ball (a (ii p) : ℂ) (s (ii p)) ×ˢ Metric.ball (b (ii p) : ℂ) (t (ii p)) :=
        hii p hp
      refine ((hF (ii p)) p hpP).congr ?_
      filter_upwards [(Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds hpP] with q hq
      have hqU : q ∈ (⋃ j, Metric.ball (a j : ℂ) (s j) ×ˢ Metric.ball (b j : ℂ) (t j)) :=
        Set.mem_iUnion.mpr ⟨ii p, hq⟩
      have hqP : q ∈ Metric.ball (a (ii q) : ℂ) (s (ii q)) ×ˢ Metric.ball (b (ii q) : ℂ) (t (ii q)) :=
        hii q hqU
      exact hagree (ii p) (ii q) ⟨q, hq, hqP⟩ ⟨hq, hqP⟩
    · intro i q hq
      have hqU : q ∈ (⋃ j, Metric.ball (a j : ℂ) (s j) ×ˢ Metric.ball (b j : ℂ) (t j)) :=
        Set.mem_iUnion.mpr ⟨i, hq⟩
      have hqP : q ∈ Metric.ball (a (ii q) : ℂ) (s (ii q)) ×ˢ Metric.ball (b (ii q) : ℂ) (t (ii q)) :=
        hii q hqU
      exact hagree (ii q) i ⟨q, hqP, hq⟩ ⟨hqP, hq⟩
  · haveI : IsEmpty ι := not_nonempty_iff.mp hne
    refine ⟨fun _ => 0, ?_, ?_⟩
    · intro p hp
      obtain ⟨i, _⟩ := Set.mem_iUnion.mp hp
      exact isEmptyElim i
    · intro i
      exact isEmptyElim i


/-- A ball in `ℂ × ℂ` (sup norm) is a product of balls. -/
theorem ball_prod_eq (u v : ℂ) (r : ℝ) :
    Metric.ball (u, v) r = Metric.ball u r ×ˢ Metric.ball v r := by
  ext p
  rw [Set.mem_prod, Metric.mem_ball, Prod.dist_eq, max_lt_iff, Metric.mem_ball, Metric.mem_ball]

theorem ofReal_mem_ball_iff (x u r : ℝ) : (x:ℂ) ∈ Metric.ball (u:ℂ) r ↔ |x - u| < r := by
  rw [Metric.mem_ball, Complex.dist_eq]
  have h : (x:ℂ) - (u:ℂ) = ((x - u : ℝ) : ℂ) := by push_cast; ring
  rw [h, norm_ofRealC]

/-- Complexification of a jointly real-analytic function on an interval. -/
theorem complexify_analyticOn (f : ℝ × ℝ → ℂ) (a b c d : ℝ) (hac : a < c) (hcd : c ≤ d)
    (hdb : d < b) (hf : AnalyticOnNhd ℝ f (Set.Ioo a b ×ˢ Set.univ))
    (hper : ∀ E x, f (E, x + 1) = f (E, x)) :
    ∃ (Δ : Set ℂ) (ρ : ℝ) (F : ℂ × ℂ → ℂ), IsOpen Δ ∧
      (Set.Icc c d : Set ℝ) ⊆ {E : ℝ | (E : ℂ) ∈ Δ} ∧ 0 < ρ ∧
      DifferentiableOn ℂ F {p : ℂ × ℂ | p.1 ∈ Δ ∧ |p.2.im| < ρ} ∧
      (∀ E ∈ Set.Icc c d, ∀ x : ℝ, F ((E : ℂ), (x : ℂ)) = f (E, x)) ∧
      (∀ p ∈ {p : ℂ × ℂ | p.1 ∈ Δ ∧ |p.2.im| < ρ}, F (p.1, p.2 + 1) = F (p.1, p.2)) := by
  classical
  set K : Set (ℝ × ℝ) := (Set.Icc c d) ×ˢ (Set.Icc (0:ℝ) 1) with hKdef
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hloc : ∀ p : ℝ × ℝ, ∃ r : ℝ, 0 < r ∧ ∃ (F : ℂ × ℂ → ℂ),
      (p ∈ K → AnalyticOnNhd ℂ F (Metric.ball ((p.1:ℂ),(p.2:ℂ)) r)) ∧
      (p ∈ K → (∀ x : ℝ × ℝ, x ∈ Metric.ball p r → F ((x.1:ℂ),(x.2:ℂ)) = f x)) := by
    intro p
    by_cases hp : p ∈ K
    · have hp' : p.1 ∈ Set.Ioo a b := ⟨lt_of_lt_of_le hac hp.1.1, lt_of_le_of_lt hp.1.2 hdb⟩
      obtain ⟨r, hr, F, hFa, hFag⟩ := complexify_analyticAt_local f p (hf p ⟨hp', trivial⟩)
      exact ⟨r, hr, F, fun _ => hFa, fun _ => hFag⟩
    · exact ⟨1, one_pos, fun _ => 0, fun h => absurd h hp, fun h => absurd h hp⟩
  choose r hr Fp hFp using hloc
  have hcoverK : K ⊆ ⋃ p : ↥K, Metric.ball (p:ℝ×ℝ) (r p) := fun p hp =>
    Set.mem_iUnion.mpr ⟨⟨p, hp⟩, Metric.mem_ball_self (hr p)⟩
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover
    (fun p : ↥K => Metric.ball (p:ℝ×ℝ) (r p))
    (fun _ => Metric.isOpen_ball) hcoverK
  set s : Finset (ℝ × ℝ) := t.image Subtype.val with hs
  have hsK : ∀ i : ↥s, (i:ℝ × ℝ) ∈ K := by
    intro i
    have hi : (i:ℝ × ℝ) ∈ t.image Subtype.val := by rw [← hs]; exact i.2
    obtain ⟨q, hqt, hqeq⟩ := Finset.mem_image.mp hi
    rw [← hqeq]
    exact (q:↥K).2
  have hcoverT : ∀ E₀ ∈ Set.Icc c d, ∀ x₀ ∈ Set.Icc (0:ℝ) 1, ∃ i : ↥s,
      |E₀ - (i:ℝ×ℝ).1| < r (i:ℝ×ℝ) ∧ |x₀ - (i:ℝ×ℝ).2| < r (i:ℝ×ℝ) := by
    intro E₀ hE₀ x₀ hx₀
    have hmem : (E₀, x₀) ∈ K := ⟨hE₀, hx₀⟩
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp (ht hmem)
    obtain ⟨hqt, hqball⟩ := Set.mem_iUnion.mp hq
    have hdist : max |E₀ - (q:ℝ×ℝ).1| |x₀ - (q:ℝ×ℝ).2| < r q := by
      have h := Metric.mem_ball.mp hqball
      rwa [Prod.dist_eq, Real.dist_eq, Real.dist_eq] at h
    have hqs : (q:ℝ × ℝ) ∈ s := by
      rw [hs]; exact Finset.mem_image.mpr ⟨q, hqt, rfl⟩
    refine ⟨⟨(q:ℝ×ℝ), hqs⟩, ?_, ?_⟩
    · exact lt_of_le_of_lt (le_max_left _ _) hdist
    · exact lt_of_le_of_lt (le_max_right _ _) hdist
  obtain ⟨Δ, hΔopen, hΔmem, ρ, hρpos, hΔsub⟩ := TubeCoverMain c d hcd
    (fun i : ↥s => (i:ℝ×ℝ).1) (fun i : ↥s => (i:ℝ×ℝ).2)
    (fun i : ↥s => r (i:ℝ×ℝ)) (fun i : ↥s => r (i:ℝ×ℝ))
    (fun i => hr _) (fun i => hr _) hcoverT
  have hperZ : ∀ (E x : ℝ) (n : ℤ), f (E, x + (n:ℝ)) = f (E, x) := by
    intro E x n
    have hg : Function.Periodic (fun y : ℝ => f (E, y)) 1 := fun y => hper E y
    simpa using (hg.int_mul n) x
  let FF : (↥s × ℤ) → ℂ × ℂ → ℂ := fun mn z =>
    Fp (mn.1:ℝ×ℝ) (z.1, z.2 - (mn.2:ℂ))
  have hval : ∀ (i : ↥s) (n : ℤ) (x y : ℝ),
      (x:ℂ) ∈ Metric.ball ((i:ℝ×ℝ).1 : ℂ) (r (i:ℝ×ℝ)) →
      (y:ℂ) ∈ Metric.ball ((((i:ℝ×ℝ).2 + (n:ℝ)) : ℝ) : ℂ) (r (i:ℝ×ℝ)) →
      FF (i, n) ((x:ℂ),(y:ℂ)) = f (x, y) := by
    intro i n x y hx hy
    have hy' : |y - ((i:ℝ×ℝ).2 + (n:ℝ))| < r (i:ℝ×ℝ) := (ofReal_mem_ball_iff y _ _).mp hy
    have hmem : ((x, y - (n:ℝ)) : ℝ × ℝ) ∈ Metric.ball (i:ℝ×ℝ) (r (i:ℝ×ℝ)) := by
      rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff]
      refine ⟨(ofReal_mem_ball_iff x _ _).mp hx, ?_⟩
      have hq : y - (n:ℝ) - (i:ℝ×ℝ).2 = y - ((i:ℝ×ℝ).2 + (n:ℝ)) := by ring
      rw [hq]; exact hy'
    have h1 : FF (i, n) ((x:ℂ),(y:ℂ)) = f (x, y - (n:ℝ)) := by
      show Fp (i:ℝ×ℝ) ((x:ℂ), (y:ℂ) - (n:ℂ)) = f (x, y - (n:ℝ))
      have hyc : (y:ℂ) - (n:ℂ) = ((y - (n:ℝ) : ℝ) : ℂ) := by push_cast; ring
      rw [hyc]
      exact ((hFp (i:ℝ×ℝ)).2 (hsK i)) ((x, y - (n:ℝ))) hmem
    rw [h1]
    have hper' := hperZ x (y - (n:ℝ)) n
    rw [show y - (n:ℝ) + (n:ℝ) = y by ring] at hper'
    exact hper'.symm
  have hFF : ∀ mn : ↥s × ℤ, AnalyticOnNhd ℂ (FF mn)
      (Metric.ball ((mn.1:ℝ×ℝ).1 : ℂ) (r (mn.1:ℝ×ℝ)) ×ˢ
        Metric.ball ((((mn.1:ℝ×ℝ).2 + (mn.2:ℝ)) : ℝ) : ℂ) (r (mn.1:ℝ×ℝ))) := by
    intro mn
    have han : AnalyticOnNhd ℂ (Fp (mn.1:ℝ×ℝ))
        (Metric.ball ((mn.1:ℝ×ℝ).1 : ℂ) (r (mn.1:ℝ×ℝ)) ×ˢ
          Metric.ball ((mn.1:ℝ×ℝ).2 : ℂ) (r (mn.1:ℝ×ℝ))) := by
      rw [← ball_prod_eq]
      exact ((hFp (mn.1:ℝ×ℝ)).1 (hsK mn.1))
    have hmap : AnalyticOnNhd ℂ (fun z : ℂ × ℂ => (z.1, z.2 - (mn.2:ℂ)))
        (Metric.ball ((mn.1:ℝ×ℝ).1 : ℂ) (r (mn.1:ℝ×ℝ)) ×ˢ
          Metric.ball ((((mn.1:ℝ×ℝ).2 + (mn.2:ℝ)) : ℝ) : ℂ) (r (mn.1:ℝ×ℝ))) := by
      intro z _
      exact ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt z).prod
        (((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt z).sub analyticAt_const)
    refine han.comp hmap ?_
    intro z hz
    have hz1 : z.1 ∈ Metric.ball ((mn.1:ℝ×ℝ).1 : ℂ) (r (mn.1:ℝ×ℝ)) := (Set.mem_prod.mp hz).1
    have hz2 : z.2 ∈ Metric.ball ((((mn.1:ℝ×ℝ).2 + (mn.2:ℝ)):ℝ):ℂ) (r (mn.1:ℝ×ℝ)) := (Set.mem_prod.mp hz).2
    refine ⟨hz1, ?_⟩
    rw [Metric.mem_ball, Complex.dist_eq] at hz2 ⊢
    have heq : (z.2 - (mn.2:ℂ)) - ((mn.1:ℝ×ℝ).2 : ℂ) =
        z.2 - ((((mn.1:ℝ×ℝ).2 + (mn.2:ℝ)):ℝ):ℂ) := by push_cast; ring
    rw [heq]; exact hz2
  obtain ⟨G, hGan, hGeq⟩ := GluePolydiscSingle
    (fun mn : ↥s × ℤ => (mn.1:ℝ×ℝ).1) (fun mn : ↥s × ℤ => (mn.1:ℝ×ℝ).2 + (mn.2:ℝ))
    (fun mn : ↥s × ℤ => r (mn.1:ℝ×ℝ)) (fun mn : ↥s × ℤ => r (mn.1:ℝ×ℝ))
    (fun mn => hr (mn.1:ℝ×ℝ)) (fun mn => hr (mn.1:ℝ×ℝ)) FF hFF (by
      intro mn mn' hne
      refine agree_real_polydisc (hFF mn) (hFF mn') hne ?_
      intro x y hx hy hx' hy'
      exact (hval mn.1 mn.2 x y hx hy).trans (hval mn'.1 mn'.2 x y hx' hy').symm)
  have hΔsub' : Δ ×ˢ {w : ℂ | |w.im| < ρ} ⊆
      (⋃ mn : ↥s × ℤ, Metric.ball ((mn.1:ℝ×ℝ).1 : ℂ) (r (mn.1:ℝ×ℝ)) ×ˢ
        Metric.ball ((((mn.1:ℝ×ℝ).2 + (mn.2:ℝ)):ℝ):ℂ) (r (mn.1:ℝ×ℝ))) := by
    intro p hp
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hΔsub hp)
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hi
    exact Set.mem_iUnion.mpr ⟨(i, n), hn⟩
  refine ⟨Δ, ρ, G, hΔopen, hΔmem, hρpos, ?_, ?_, ?_⟩
  · exact (hGan.mono hΔsub').differentiableOn
  · intro E hE x
    have hEΔ : (E:ℂ) ∈ Δ := hΔmem hE
    have hxw : (x:ℂ) ∈ {w : ℂ | |w.im| < ρ} := by
      simp only [Set.mem_setOf_eq, Complex.ofReal_im, abs_zero]; exact hρpos
    have hpE : ((E:ℂ),(x:ℂ)) ∈ Δ ×ˢ {w : ℂ | |w.im| < ρ} := ⟨hEΔ, hxw⟩
    obtain ⟨mn, hmn⟩ := Set.mem_iUnion.mp (hΔsub' hpE)
    rw [hGeq mn hmn]
    exact hval mn.1 mn.2 E x hmn.1 hmn.2
  · intro p hp
    obtain ⟨mn, hmn⟩ := Set.mem_iUnion.mp (hΔsub' hp)
    have hmn2 : p.2 ∈ Metric.ball (((((mn.1:ℝ×ℝ).2 + (mn.2:ℝ)) : ℝ)) : ℂ) (r (mn.1:ℝ×ℝ)) :=
      (Set.mem_prod.mp hmn).2
    have hmn' : (p.1, p.2 + 1) ∈ Metric.ball ((mn.1:ℝ×ℝ).1 : ℂ) (r (mn.1:ℝ×ℝ)) ×ˢ
        Metric.ball (((((mn.1:ℝ×ℝ).2 + ((mn.2 + 1: ℤ):ℝ)) : ℝ)) : ℂ) (r (mn.1:ℝ×ℝ)) := by
      refine ⟨(Set.mem_prod.mp hmn).1, ?_⟩
      rw [Metric.mem_ball, Complex.dist_eq] at hmn2 ⊢
      have heq : (p.2 + 1) - (((((mn.1:ℝ×ℝ).2 + ((mn.2 + 1: ℤ):ℝ)) : ℝ)) : ℂ)
          = p.2 - (((((mn.1:ℝ×ℝ).2 + (mn.2:ℝ)) : ℝ)) : ℂ) := by push_cast; ring
      rw [heq]; exact hmn2
    rw [hGeq mn hmn, hGeq (mn.1, mn.2 + 1) hmn']
    show Fp (mn.1:ℝ×ℝ) (p.1, p.2 + 1 - (((mn.2 + 1 : ℤ)):ℂ)) =
      Fp (mn.1:ℝ×ℝ) (p.1, p.2 - (mn.2:ℂ))
    congr 1
    push_cast
    ring



/-- Contour-shift norm bound: the integral at height `s` is bounded by the sup of `Φ` on the
shifted segment. -/
theorem norm_integral_shift_le (Φ : ℂ → ℂ) (s : ℝ) (k : ℤ) :
    ‖∫ x in (0:ℝ)..1, Φ ((x : ℂ) + (s : ℂ) * Complex.I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((x : ℂ) + (s : ℂ) * Complex.I)))‖
    ≤ (∫ x in (0:ℝ)..1, ‖Φ ((x : ℂ) + (s : ℂ) * Complex.I)‖)
        * Real.exp (2 * Real.pi * (k : ℝ) * s) := by
  have h1 : ‖∫ x in (0:ℝ)..1, Φ ((x : ℂ) + (s : ℂ) * Complex.I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((x : ℂ) + (s : ℂ) * Complex.I)))‖
      ≤ ∫ x in (0:ℝ)..1, ‖Φ ((x : ℂ) + (s : ℂ) * Complex.I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((x : ℂ) + (s : ℂ) * Complex.I)))‖ :=
    intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0:ℝ) ≤ 1)
  have h2 : ∀ x : ℝ, ‖Φ ((x : ℂ) + (s : ℂ) * Complex.I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((x : ℂ) + (s : ℂ) * Complex.I)))‖
      = ‖Φ ((x : ℂ) + (s : ℂ) * Complex.I)‖ * Real.exp (2 * Real.pi * (k : ℝ) * s) := by
    intro x
    rw [norm_mul, Complex.norm_exp]
    have hre : (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((x : ℂ) + (s : ℂ) * Complex.I))).re
        = 2 * Real.pi * (k : ℝ) * s := by
      simp only [Complex.neg_re, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.intCast_re,
        Complex.intCast_im, Complex.re_ofNat, Complex.im_ofNat, Complex.natCast_re, Complex.natCast_im]
      ring
    rw [hre]
  calc ‖∫ x in (0:ℝ)..1, Φ ((x : ℂ) + (s : ℂ) * Complex.I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((x : ℂ) + (s : ℂ) * Complex.I)))‖
      ≤ ∫ x in (0:ℝ)..1, ‖Φ ((x : ℂ) + (s : ℂ) * Complex.I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((x : ℂ) + (s : ℂ) * Complex.I)))‖ := h1
    _ = ∫ x in (0:ℝ)..1, ‖Φ ((x : ℂ) + (s : ℂ) * Complex.I)‖ * Real.exp (2 * Real.pi * (k : ℝ) * s) := by
        apply intervalIntegral.integral_congr
        intro x _
        exact h2 x
    _ = (∫ x in (0:ℝ)..1, ‖Φ ((x : ℂ) + (s : ℂ) * Complex.I)‖)
        * Real.exp (2 * Real.pi * (k : ℝ) * s) := by
        rw [intervalIntegral.integral_mul_const]

/-- **Exponential decay of Fourier coefficients on a strip** (AJ (4.16)-(4.17)). -/
theorem fourierCoeff_decay_of_strip (φ : ℝ → ℂ) (Φ : ℂ → ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hΦ : DifferentiableOn ℂ Φ {w : ℂ | |w.im| < ρ})
    (hper : ∀ w : ℂ, |w.im| < ρ → Φ (w + 1) = Φ w)
    (hφ : ∀ x : ℝ, Φ (x : ℂ) = φ x) :
    ∃ C η : ℝ, 0 < η ∧ ∀ k : ℤ,
      ‖fourierCoeffOn (show (0:ℝ) < 1 by norm_num) φ k‖ ≤ C * Real.exp (-(η * |(k : ℝ)|)) := by
  set σ : ℝ := ρ / 2 with hσ
  have hσpos : 0 < σ := by rw [hσ]; linarith
  have hσlt : σ < ρ := by rw [hσ]; linarith
  have hσabs : |σ| < ρ := by rw [abs_of_pos hσpos]; exact hσlt
  have hmσabs : |-σ| < ρ := by rw [abs_neg, abs_of_pos hσpos]; exact hσlt
  set Cp : ℝ := ∫ x in (0:ℝ)..1, ‖Φ ((x : ℂ) + (σ : ℂ) * Complex.I)‖ with hCp
  set Cm : ℝ := ∫ x in (0:ℝ)..1, ‖Φ ((x : ℂ) + ((-σ : ℝ) : ℂ) * Complex.I)‖ with hCm
  have hCpnn : 0 ≤ Cp := by
    rw [hCp]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun u _ => norm_nonneg _)
  have hCmnn : 0 ≤ Cm := by
    rw [hCm]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun u _ => norm_nonneg _)
  have hηpos : 0 < 2 * Real.pi * σ := by
    have h2π : (0:ℝ) < 2 * Real.pi := by positivity
    exact mul_pos h2π hσpos
  have hbridge : ∀ k : ℤ, fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) φ k =
      ∫ x in (0 : ℝ)..1, Φ (x : ℂ) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (x : ℂ))) := by
    intro k
    rw [fourierCoeffOn_eq_exp_integral]
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [hφ x]
  refine ⟨Cp + Cm + 1, 2 * Real.pi * σ, hηpos, fun k => ?_⟩
  have hCple : Cp ≤ Cp + Cm + 1 := by linarith
  have hCmle : Cm ≤ Cp + Cm + 1 := by linarith
  rcases lt_or_ge (0 : ℤ) k with hk | hk
  · have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    calc ‖fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) φ k‖
        = ‖∫ x in (0 : ℝ)..1, Φ (x : ℂ) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (x : ℂ)))‖ := by
            rw [hbridge k]
      _ = ‖∫ x in (0 : ℝ)..1, Φ ((x : ℂ) + ((-σ : ℝ) : ℂ) * Complex.I) *
              Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((x : ℂ) + ((-σ : ℝ) : ℂ) * Complex.I)))‖ := by
            rw [integral_shift_eq_of_periodic_strip Φ ρ hρ hΦ hper k (-σ) hmσabs]
      _ ≤ Cm * Real.exp (2 * Real.pi * (k : ℝ) * (-σ)) := by
            simpa [hCm] using norm_integral_shift_le Φ (-σ) k
      _ ≤ (Cp + Cm + 1) * Real.exp (-((2 * Real.pi * σ) * |(k : ℝ)|)) := by
            have hexp : Real.exp (2 * Real.pi * (k : ℝ) * (-σ)) =
                Real.exp (-((2 * Real.pi * σ) * |(k : ℝ)|)) := by
              congr 1
              rw [abs_of_pos hkpos]
              ring
            rw [hexp]
            exact mul_le_mul_of_nonneg_right hCmle (Real.exp_pos _).le
  · have hknp : (k : ℝ) ≤ 0 := by exact_mod_cast hk
    calc ‖fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) φ k‖
        = ‖∫ x in (0 : ℝ)..1, Φ (x : ℂ) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (x : ℂ)))‖ := by
            rw [hbridge k]
      _ = ‖∫ x in (0 : ℝ)..1, Φ ((x : ℂ) + (σ : ℂ) * Complex.I) *
              Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((x : ℂ) + (σ : ℂ) * Complex.I)))‖ := by
            rw [integral_shift_eq_of_periodic_strip Φ ρ hρ hΦ hper k σ hσabs]
      _ ≤ Cp * Real.exp (2 * Real.pi * (k : ℝ) * σ) := by
            simpa [hCp] using norm_integral_shift_le Φ σ k
      _ ≤ (Cp + Cm + 1) * Real.exp (-((2 * Real.pi * σ) * |(k : ℝ)|)) := by
            have hexp : Real.exp (2 * Real.pi * (k : ℝ) * σ) =
                Real.exp (-((2 * Real.pi * σ) * |(k : ℝ)|)) := by
              congr 1
              rw [abs_of_nonpos hknp]
              ring
            rw [hexp]
            exact mul_le_mul_of_nonneg_right hCple (Real.exp_pos _).le


theorem continuous_ek (k : ℤ) : Continuous (ek k) := by
  unfold ek
  fun_prop

/-- **Fourier coefficients of a coboundary** (AJ (4.18)): if `φ x - ∫φ = ψ (x+α) - ψ x` with
`ψ` 1-periodic, then for `k ≠ 0` the `k`-th Fourier coefficient of `φ` is
`(exp (2πi k α) - 1)` times that of `ψ`. -/
theorem fcoef_coboundary (α : ℝ) (φ ψ : ℝ → ℝ) (hψp : ∀ x, ψ (x + 1) = ψ x)
    (hcontψ : Continuous ψ)
    (heq : ∀ x, φ x - (∫ t in (0 : ℝ)..1, φ t) = ψ (x + α) - ψ x)
    (k : ℤ) (hk : k ≠ 0) :
    fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) (fun x => ((φ x : ℝ) : ℂ)) k
      = (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (α : ℂ)) - 1)
        * fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) (fun x => ((ψ x : ℝ) : ℂ)) k := by
  have hf : ∀ x, (fun x => ((ψ x : ℝ) : ℂ)) (x + 1) = (fun x => ((ψ x : ℝ) : ℂ)) x :=
    fun x => by show ((ψ (x + 1) : ℝ) : ℂ) = ((ψ x : ℝ) : ℂ); rw [hψp x]
  have hpt : ∀ x : ℝ, ((φ x : ℝ) : ℂ) * ek k x
      = (((∫ t in (0 : ℝ)..1, φ t) : ℝ) : ℂ) * ek k x
        + ((ψ (x + α) : ℝ) : ℂ) * ek k x - ((ψ x : ℝ) : ℂ) * ek k x := by
    intro x
    have h := heq x
    have hx : φ x = (∫ t in (0 : ℝ)..1, φ t) + ψ (x + α) - ψ x := by linarith
    rw [hx]
    push_cast
    ring
  have hint : ∀ c : ℂ, IntervalIntegrable (fun x : ℝ => c * ek k x) volume (0 : ℝ) 1 :=
    fun c => (continuous_const.mul (continuous_ek k)).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun x : ℝ => ((ψ (x + α) : ℝ) : ℂ) * ek k x) volume (0 : ℝ) 1 :=
    ((Complex.continuous_ofReal.comp
      (hcontψ.comp (continuous_id.add continuous_const))).mul (continuous_ek k)).intervalIntegrable _ _
  have hint3 : IntervalIntegrable (fun x : ℝ => ((ψ x : ℝ) : ℂ) * ek k x) volume (0 : ℝ) 1 :=
    ((Complex.continuous_ofReal.comp hcontψ).mul (continuous_ek k)).intervalIntegrable _ _
  calc fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) (fun x => ((φ x : ℝ) : ℂ)) k
      = (∫ x in (0 : ℝ)..1, ((φ x : ℝ) : ℂ) * ek k x) := fcoef_eq_int _ k
    _
      = ∫ x in (0 : ℝ)..1, ((((∫ t in (0 : ℝ)..1, φ t) : ℝ) : ℂ) * ek k x
          + ((ψ (x + α) : ℝ) : ℂ) * ek k x - ((ψ x : ℝ) : ℂ) * ek k x) :=
        intervalIntegral.integral_congr fun x _ => hpt x
    _ = (∫ x in (0 : ℝ)..1, (((∫ t in (0 : ℝ)..1, φ t) : ℝ) : ℂ) * ek k x)
          + (∫ x in (0 : ℝ)..1, ((ψ (x + α) : ℝ) : ℂ) * ek k x)
          - (∫ x in (0 : ℝ)..1, ((ψ x : ℝ) : ℂ) * ek k x) := by
        rw [intervalIntegral.integral_sub (hint _ |>.add hint2) hint3,
          intervalIntegral.integral_add (hint _) hint2]
    _ = (((∫ t in (0 : ℝ)..1, φ t) : ℝ) : ℂ) * (∫ x in (0 : ℝ)..1, ek k x)
          + (∫ x in (0 : ℝ)..1, ((ψ (x + α) : ℝ) : ℂ) * ek k x)
          - (∫ x in (0 : ℝ)..1, ((ψ x : ℝ) : ℂ) * ek k x) := by
        rw [intervalIntegral.integral_const_mul]
    _ = 0 + (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (α : ℂ))
            * ∫ x in (0 : ℝ)..1, ((ψ x : ℝ) : ℂ) * ek k x)
          - (∫ x in (0 : ℝ)..1, ((ψ x : ℝ) : ℂ) * ek k x) := by
        have hshift : (∫ x in (0 : ℝ)..1, ((ψ (x + α) : ℝ) : ℂ) * ek k x)
            = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (α : ℂ))
              * ∫ x in (0 : ℝ)..1, ((ψ x : ℝ) : ℂ) * ek k x := by
          rw [← fcoef_eq_int (fun x => ((ψ (x + α) : ℝ) : ℂ)) k,
            ← fcoef_eq_int (fun x => ((ψ x : ℝ) : ℂ)) k,
            fcoef_shift (fun x => ((ψ x : ℝ) : ℂ)) hf α k]
        rw [hshift, integral_ek_zero k hk, mul_zero, zero_add]
    _ = (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (α : ℂ)) - 1)
          * fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) (fun x => ((ψ x : ℝ) : ℂ)) k := by
        rw [fcoef_eq_int (fun x => ((ψ x : ℝ) : ℂ)) k]
        ring

/-- **Claim A** (AJ (4.22)–(4.23)).  If `E` is in the reducible set and the cocycle at `E` is
analytically conjugate to rotations with angle `φ`, then the Fourier coefficients of `φ`
satisfy the small-divisor bound. -/
theorem fourier_bound_of_mem_RedSet
    (hcob : ∀ (α : ℝ), Irrational α → ∀ (φ : ℝ → ℝ), Continuous φ →
      (∀ x, φ (x + 1) = φ x) → ∀ (O : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ),
      (∀ i j, AnalyticOnNhd ℝ (fun x => O x i j) Set.univ) →
      (∀ x, O (x + 1) = O x) → (∀ x, (O x).det = 1) →
      (∀ x, O (x + α) * rot (φ x) = rot c * O x) →
      ∃ ψ : ℝ → ℝ, (∀ x, ψ (x + 1) = ψ x) ∧ AnalyticOnNhd ℝ ψ Set.univ ∧
        ∀ x, φ x - (∫ t in (0 : ℝ)..1, φ t) = ψ (x + α) - ψ x)
    (α lam E a b : ℝ) (hα : Irrational α)
    (hE : E ∈ Set.Ioo a b)
    (C : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (φ : ℝ → ℝ)
    (hCan : ∀ i j, AnalyticOnNhd ℝ (fun x => C x i j) Set.univ)
    (hCp : ∀ x, C (x + 1) = C x) (hCdet : ∀ x, (C x).det = 1)
    (hconj : ∀ x, C (x + α) * tmR lam E x = rot (φ x) * C x)
    (hφan : AnalyticOnNhd ℝ φ Set.univ) (hφp : ∀ x, φ (x + 1) = φ x)
    (hred : E ∈ RedSet α lam) :
    ∃ C₀ η : ℝ, 0 < η ∧ ∀ k : ℤ, k ≠ 0 →
      ‖fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) (fun x => ((φ x : ℝ) : ℂ)) k‖
        ≤ C₀ * ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (α : ℂ)) - 1‖
            * Real.exp (-(η * |(k : ℝ)|)) := by
  obtain ⟨B, c, hBan, hBp, hBdet, _hBdeg, hBconj⟩ := hred
  have hCadj : ∀ x, C x * Matrix.adjugate (C x) = 1 := by
    intro x
    rw [Matrix.mul_adjugate, hCdet x, one_smul]
  have hAdjC : ∀ x, Matrix.adjugate (C x) * C x = 1 := by
    intro x
    rw [Matrix.adjugate_mul, hCdet x, one_smul]
  have hAan : ∀ i j, AnalyticOnNhd ℝ (fun x => Matrix.adjugate (C x) i j) Set.univ := by
    intro i j
    have hrep : (fun x => Matrix.adjugate (C x) i j)
        = fun x => (!![C x 1 1, -C x 0 1; -C x 1 0, C x 0 0] :
            Matrix (Fin 2) (Fin 2) ℝ) i j := by
      funext x
      rw [Matrix.adjugate_fin_two]
    rw [hrep]
    fin_cases i <;> fin_cases j <;>
      first
        | exact hCan 1 1
        | exact (hCan 0 1).neg
        | exact (hCan 1 0).neg
        | exact hCan 0 0
  set O : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun x => B x * Matrix.adjugate (C x) with hOdef
  have hOan : ∀ i j, AnalyticOnNhd ℝ (fun x => O x i j) Set.univ :=
    analyticOnNhd_matrix_mul hBan hAan
  have hOp : ∀ x, O (x + 1) = O x := by
    intro x
    simp only [O]
    rw [hBp x, hCp x]
  have hOdet : ∀ x, (O x).det = 1 := by
    intro x
    simp only [O]
    rw [Matrix.det_mul, hBdet x, Matrix.det_adjugate]
    simp [hCdet x]
  have hOconj : ∀ x, O (x + α) * rot (φ x) = rot c * O x := by
    intro x
    have h2 : Matrix.adjugate (C (x + α)) * rot (φ x)
        = tmR lam E x * Matrix.adjugate (C x) := by
      calc Matrix.adjugate (C (x + α)) * rot (φ x)
          = Matrix.adjugate (C (x + α)) * rot (φ x) * (C x * Matrix.adjugate (C x)) := by
              rw [hCadj x, mul_one]
        _ = Matrix.adjugate (C (x + α)) * (rot (φ x) * C x) * Matrix.adjugate (C x) := by
              noncomm_ring
        _ = Matrix.adjugate (C (x + α)) * (C (x + α) * tmR lam E x) * Matrix.adjugate (C x) := by
              rw [hconj x]
        _ = (Matrix.adjugate (C (x + α)) * C (x + α)) * tmR lam E x * Matrix.adjugate (C x) := by
              noncomm_ring
        _ = tmR lam E x * Matrix.adjugate (C x) := by rw [hAdjC (x + α), one_mul]
    simp only [O]
    rw [mul_assoc, h2, ← mul_assoc, hBconj x, mul_assoc]
  obtain ⟨ψ, hψp, hψan, hψeq⟩ :=
    hcob α hα φ hφan.continuous hφp O c hOan hOp hOdet hOconj
  have hψjoint : AnalyticOnNhd ℝ (fun p : ℝ × ℝ => ((ψ p.2 : ℝ) : ℂ))
      (Set.Ioo a b ×ˢ Set.univ) :=
    (Complex.ofRealCLM.analyticOnNhd (s := Set.univ)).comp
      (hψan.comp analyticOnNhd_snd (fun p _ => trivial)) (fun p _ => trivial)
  have hψ2p : ∀ E' x, (fun p : ℝ × ℝ => ((ψ p.2 : ℝ) : ℂ)) (E', x + 1)
      = (fun p : ℝ × ℝ => ((ψ p.2 : ℝ) : ℂ)) (E', x) :=
    fun E' x => by
      show ((ψ (x + 1) : ℝ) : ℂ) = ((ψ x : ℝ) : ℂ)
      rw [hψp x]
  obtain ⟨Δ, ρ, F, hΔopen, hΔmem, hρ, hFdiff, hFagree, hFper⟩ :=
    complexify_analyticOn (fun p : ℝ × ℝ => ((ψ p.2 : ℝ) : ℂ)) a b E E hE.1 le_rfl hE.2
      hψjoint hψ2p
  have hEΔ : (E : ℂ) ∈ Δ := hΔmem (Set.mem_Icc.mpr ⟨le_rfl, le_rfl⟩)
  have hΦdiff : DifferentiableOn ℂ (fun w : ℂ => F ((E : ℂ), w)) {w : ℂ | |w.im| < ρ} := by
    have hg : DifferentiableOn ℂ (fun w : ℂ => ((E : ℂ), w)) {w : ℂ | |w.im| < ρ} :=
      DifferentiableOn.prodMk (differentiableOn_const (c := (E : ℂ))) differentiableOn_id
    exact DifferentiableOn.comp hFdiff hg (fun w hw => ⟨hEΔ, hw⟩)
  have hΦper : ∀ w : ℂ, |w.im| < ρ → F ((E : ℂ), w + 1) = F ((E : ℂ), w) := by
    intro w hw
    have h := hFper ((E : ℂ), w) ⟨hEΔ, hw⟩
    simpa using h
  have hΦagree : ∀ x : ℝ, F ((E : ℂ), (x : ℂ)) = ((ψ x : ℝ) : ℂ) := by
    intro x
    have h := hFagree E (Set.mem_Icc.mpr ⟨le_rfl, le_rfl⟩) x
    simpa using h
  obtain ⟨C₁, η₁, hη₁, hbound⟩ :=
    fourierCoeff_decay_of_strip (fun x => ((ψ x : ℝ) : ℂ)) (fun w => F ((E : ℂ), w)) ρ hρ
      hΦdiff hΦper hΦagree
  refine ⟨C₁, η₁, hη₁, fun k hk => ?_⟩
  have hkey := fcoef_coboundary α φ ψ hψp hψan.continuous hψeq k hk
  have h1 := hbound k
  rw [hkey, norm_mul]
  calc ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (α : ℂ)) - 1‖
        * ‖fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) (fun x => ((ψ x : ℝ) : ℂ)) k‖
      ≤ ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (α : ℂ)) - 1‖
        * (C₁ * Real.exp (-(η₁ * |(k : ℝ)|))) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = C₁ * ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (α : ℂ)) - 1‖
        * Real.exp (-(η₁ * |(k : ℝ)|)) := by ring





/-- **Exponential decay of the Fourier coefficients gives an analytic coboundary** (AJ (4.18)). -/
theorem analytic_coboundary_of_decay (α : ℝ) (hα : Irrational α) (φ : ℝ → ℂ) (hφ : Continuous φ)
    (hper : ∀ x, φ (x + 1) = φ x)
    (η : ℝ) (hη : 0 < η) (C : ℝ) (hC : 0 < C)
    (hbd : ∀ k : ℤ, k ≠ 0 → ‖fourierCoeffOn (show (0:ℝ) < 1 by norm_num) φ k‖
      ≤ C * ‖Complex.exp (2 * Real.pi * (k : ℝ) * α * Complex.I) - 1‖ * Real.exp (-(η * |(k : ℝ)|))) :
    ∃ ψ : ℝ → ℂ, (∀ x, ψ (x + 1) = ψ x) ∧ AnalyticOnNhd ℝ ψ Set.univ ∧
      ∀ x, φ x - (∫ t in (0 : ℝ)..1, φ t) = ψ (x + α) - ψ x := by
  classical
  have hne : ∀ k : ℤ, k ≠ 0 → Complex.exp (2 * Real.pi * (k : ℝ) * α * Complex.I) - 1 ≠ 0 :=
    fun k hk => sub_ne_zero.mpr (exp_two_pi_mul_I_mul_ne_one α hα k hk)
  set w : ℤ → ℂ := fun k => if k = 0 then 0 else
    fourierCoeffOn (show (0:ℝ) < 1 by norm_num) φ k /
      (Complex.exp (2 * Real.pi * (k : ℝ) * α * Complex.I) - 1) with hw
  have hwbd : ∀ k : ℤ, ‖w k‖ ≤ C * Real.exp (-(η * |(k : ℝ)|)) := by
    intro k
    by_cases hk : k = 0
    · simp only [hw, hk, if_true, norm_zero]
      exact mul_nonneg hC.le (Real.exp_pos _).le
    · have hden : 0 < ‖Complex.exp (2 * Real.pi * (k : ℝ) * α * Complex.I) - 1‖ :=
        norm_pos_iff.mpr (hne k hk)
      simp only [hw, hk, if_false]
      rw [norm_div, div_le_iff₀ hden]
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hbd k hk
  set Ψ : ℂ → ℂ := fun z => ∑' k : ℤ, w k * Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * z) with hΨ
  have hΨan : AnalyticOnNhd ℂ Ψ {z : ℂ | 2 * Real.pi * |z.im| < η} :=
    Part2.AnalyticTsumFourier w η C hη hwbd
  have hsumm : ∀ z : ℂ, 2 * Real.pi * |z.im| < η →
      Summable (fun k : ℤ => w k * Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * z)) := by
    intro z hz
    have hc : 0 < η - 2 * Real.pi * |z.im| := by linarith
    refine Summable.of_norm_bounded
      (g := fun k : ℤ => C * Real.exp (-((η - 2 * Real.pi * |z.im|) * |(k:ℝ)|))) ?_ ?_
    · exact (summable_int_exp_neg _ hc).mul_left C
    · intro k
      rw [norm_mul, Complex.norm_exp]
      have hexp : (2 * Real.pi * Complex.I * (k : ℂ) * z).re = -(2 * Real.pi * (k : ℝ) * z.im) := by
        rw [show 2 * Real.pi * Complex.I * (k : ℂ) * z
              = ((2 * Real.pi * (k:ℝ) : ℝ) : ℂ) * (Complex.I * z) by push_cast; ring]
        rw [Complex.re_ofReal_mul, Complex.I_mul_re]
        ring
      rw [hexp]
      calc ‖w k‖ * Real.exp (-(2 * Real.pi * (k : ℝ) * z.im))
          ≤ (C * Real.exp (-(η * |(k : ℝ)|))) * Real.exp (-(2 * Real.pi * (k : ℝ) * z.im)) :=
            mul_le_mul_of_nonneg_right (hwbd k) (Real.exp_pos _).le
        _ = C * Real.exp (-(η * |(k:ℝ)|) - 2 * Real.pi * (k:ℝ) * z.im) := by
            rw [mul_assoc, ← Real.exp_add,
              show -(η * |(k:ℝ)|) + -(2 * Real.pi * (k:ℝ) * z.im)
                = -(η * |(k:ℝ)|) - 2 * Real.pi * (k:ℝ) * z.im by ring]
        _ ≤ C * Real.exp (-((η - 2 * Real.pi * |z.im|) * |(k:ℝ)|)) := by
            apply mul_le_mul_of_nonneg_left _ hC.le
            apply Real.exp_le_exp.mpr
            have h1 : -((k:ℝ) * z.im) ≤ |(k:ℝ)| * |z.im| := by
              rw [← abs_mul]; exact neg_le_abs _
            have h2 : (η - 2 * Real.pi * |z.im|) * |(k:ℝ)|
                ≤ η * |(k:ℝ)| + 2 * Real.pi * ((k:ℝ) * z.im) := by
              nlinarith [h1, Real.pi_pos, abs_nonneg z.im, abs_nonneg (k:ℝ)]
            linarith
  have hsummφ : Summable (fourierCoeffOn (show (0:ℝ) < 1 by norm_num) φ) := by
    refine Summable.of_norm_bounded (g := fun k : ℤ =>
        max ‖fourierCoeffOn (show (0:ℝ) < 1 by norm_num) φ 0‖ (2 * C)
          * Real.exp (-(η * |(k:ℝ)|))) ?_ ?_
    · exact (summable_int_exp_neg η hη).mul_left
        (max ‖fourierCoeffOn (show (0:ℝ) < 1 by norm_num) φ 0‖ (2 * C))
    · intro k
      by_cases hk : k = 0
      · rw [hk]
        simp only [Int.cast_zero, abs_zero, mul_zero, neg_zero, Real.exp_zero, mul_one]
        exact le_max_left _ _
      · have h2 : ‖fourierCoeffOn (show (0:ℝ) < 1 by norm_num) φ k‖
            ≤ C * 2 * Real.exp (-(η * |(k:ℝ)|)) := by
          refine (hbd k hk).trans ?_
          have hb : ‖Complex.exp (2 * Real.pi * (k : ℝ) * α * Complex.I) - 1‖ ≤ 2 := by
            calc ‖Complex.exp (2 * Real.pi * (k : ℝ) * α * Complex.I) - 1‖
                ≤ ‖Complex.exp (2 * Real.pi * (k : ℝ) * α * Complex.I)‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
              _ = 2 := by
                  rw [norm_one, Complex.norm_exp]
                  have hre : (2 * Real.pi * (k : ℝ) * α * Complex.I).re = 0 := by
                    rw [show 2 * Real.pi * (k:ℝ) * α * Complex.I
                          = ((2 * Real.pi * (k:ℝ) * α : ℝ) : ℂ) * Complex.I by push_cast; ring]
                    rw [Complex.re_ofReal_mul, Complex.I_re, mul_zero]
                  rw [hre, Real.exp_zero]
                  norm_num
          have h3 : C * ‖Complex.exp (2 * Real.pi * (k : ℝ) * α * Complex.I) - 1‖ ≤ C * 2 :=
            mul_le_mul_of_nonneg_left hb hC.le
          calc C * ‖Complex.exp (2 * Real.pi * (k : ℝ) * α * Complex.I) - 1‖
                * Real.exp (-(η * |(k : ℝ)|))
              ≤ (C * 2) * Real.exp (-(η * |(k : ℝ)|)) :=
                mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
            _ = C * 2 * Real.exp (-(η * |(k : ℝ)|)) := by ring
        calc ‖fourierCoeffOn (show (0:ℝ) < 1 by norm_num) φ k‖
            ≤ C * 2 * Real.exp (-(η * |(k:ℝ)|)) := h2
          _ ≤ max ‖fourierCoeffOn (show (0:ℝ) < 1 by norm_num) φ 0‖ (2 * C)
                * Real.exp (-(η * |(k:ℝ)|)) :=
              mul_le_mul_of_nonneg_right (by rw [mul_comm]; exact le_max_right _ _)
                (Real.exp_pos _).le
  refine ⟨fun x => Ψ (x : ℂ), ?_, ?_, ?_⟩
  · intro x
    have h1 : Ψ ((x : ℂ) + 1) = Ψ (x : ℂ) := by
      rw [hΨ]
      apply tsum_congr
      intro k
      congr 1
      rw [show 2 * Real.pi * Complex.I * (k : ℂ) * ((x : ℂ) + 1)
            = 2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ) + (k : ℤ) * (2 * Real.pi * Complex.I) by
              push_cast; ring,
        Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    simpa using h1
  · intro x _
    have hxmem : (x:ℂ) ∈ {z : ℂ | 2 * Real.pi * |z.im| < η} := by
      simp only [Set.mem_setOf_eq, Complex.ofReal_im, abs_zero, mul_zero]
      positivity
    exact (AnalyticAt.restrictScalars (𝕜 := ℝ) (hΨan (x:ℂ) hxmem)).comp
      (f := fun x : ℝ => (x:ℂ)) (Complex.ofRealCLM.analyticAt x)
  · intro x
    set B : ℤ → ℂ := fun k => w k * (Complex.exp (2 * Real.pi * (k:ℝ) * α * Complex.I) - 1)
        * Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * (x:ℂ)) with hB
    have hφ0 : fourierCoeffOn (show (0:ℝ) < 1 by norm_num) φ 0 = ∫ t in (0:ℝ)..1, φ t := by
      rw [fcoef_eq_int]
      apply intervalIntegral.integral_congr
      intro t _
      simp [ek]
    have hB0 : HasSum B (φ x - ∫ t in (0:ℝ)..1, φ t) := by
      have hA := Part2.FourierSeriesPointwise φ hφ hper hsummφ x
      have hD : HasSum (fun k : ℤ => if k = 0 then fourierCoeffOn (show (0:ℝ) < 1 by norm_num) φ 0 else 0)
          (fourierCoeffOn (show (0:ℝ) < 1 by norm_num) φ 0) :=
        hasSum_ite_eq (0:ℤ) (fourierCoeffOn (show (0:ℝ) < 1 by norm_num) φ 0)
      have hsub := hA.sub hD
      have hfun : (fun k : ℤ => fourierCoeffOn (show (0:ℝ) < 1 by norm_num) φ k
            * Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * (x:ℂ))
          - (if k = 0 then fourierCoeffOn (show (0:ℝ) < 1 by norm_num) φ 0 else 0)) = B := by
        funext k
        by_cases hk : k = 0
        · subst hk
          simp [hB, hw]
        · have hd : Complex.exp (2 * Real.pi * (k:ℝ) * α * Complex.I) - 1 ≠ 0 := hne k hk
          simp only [hB, hw, hk, if_false]
          rw [div_mul_cancel₀ _ hd]
          ring
      rw [hfun, hφ0] at hsub
      exact hsub
    have hB1 : HasSum B (Ψ ((x:ℂ) + (α:ℂ)) - Ψ (x:ℂ)) := by
      have hx1 : 2 * Real.pi * |((x:ℂ) + (α:ℂ)).im| < η := by
        simp only [Complex.add_im, Complex.ofReal_im, add_zero, abs_zero, mul_zero]
        exact hη
      have hx0 : 2 * Real.pi * |((x:ℂ)).im| < η := by
        simp only [Complex.ofReal_im, abs_zero, mul_zero]
        exact hη
      have hS1 : HasSum (fun k : ℤ => w k * Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * ((x:ℂ)+(α:ℂ))))
          (Ψ ((x:ℂ)+(α:ℂ))) := by
        simpa [hΨ] using (hsumm _ hx1).hasSum
      have hS2 : HasSum (fun k : ℤ => w k * Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * (x:ℂ)))
          (Ψ (x:ℂ)) := by
        simpa [hΨ] using (hsumm _ hx0).hasSum
      have hsub := hS1.sub hS2
      have hfun : (fun k : ℤ => w k * Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * ((x:ℂ)+(α:ℂ)))
          - w k * Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * (x:ℂ))) = B := by
        funext k
        simp only [hB]
        have hexp : Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * ((x:ℂ) + (α:ℂ)))
            = Complex.exp (2 * Real.pi * (k:ℝ) * α * Complex.I)
              * Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * (x:ℂ)) := by
          rw [show 2 * Real.pi * Complex.I * (k:ℂ) * ((x:ℂ) + (α:ℂ))
                = 2 * Real.pi * (k:ℝ) * α * Complex.I + 2 * Real.pi * Complex.I * (k:ℂ) * (x:ℂ) by
                  push_cast; ring,
            Complex.exp_add]
        rw [hexp]
        ring
      rwa [hfun] at hsub
    refine hB0.unique ?_
    simpa [Complex.ofReal_add] using hB1



/-- From a complex-valued analytic 1-periodic coboundary, extract a real-valued one. -/
theorem exists_real_coboundary (α : ℝ) (θ : ℝ) {φ : ℝ → ℝ} {ψC : ℝ → ℂ}
    (hψp : ∀ x, ψC (x + 1) = ψC x) (hψan : AnalyticOnNhd ℝ ψC Set.univ)
    (heq : ∀ x, ((φ x : ℝ) : ℂ) - ((θ : ℝ) : ℂ) = ψC (x + α) - ψC x) :
    ∃ ψ : ℝ → ℝ, (∀ x, ψ (x + 1) = ψ x) ∧ AnalyticOnNhd ℝ ψ Set.univ ∧
      ∀ x, φ x - θ = ψ (x + α) - ψ x := by
  refine ⟨fun x => (ψC x).re, fun x => ?_, ?_, fun x => ?_⟩
  · show (ψC (x + 1)).re = (ψC x).re
    rw [hψp x]
  · exact (Complex.reCLM.analyticOnNhd (s := Set.univ)).comp hψan (fun x _ => trivial)
  · have h := congrArg Complex.re (heq x)
    simpa using h


/-- C11 part 2 (AJ Thm 4.2(2)), on a compact `[c,d] ⊂ (a,b)`.  Route (see the module
`RedProj.KEnum` for the enumeration `kEnum : ℕ → ℤ` of `ℤ∖{0}` and the auxiliary estimates,
and `ClaimA`/`ClaimB` for the two implications):

1. `joint_analytic_of_mAnalytic h9` (`RedProj.Extract`) gives the jointly real-analytic
   conjugacy `(Cj, φj)` on `(a,b) × ℝ`; complexify `φj` with `complexify_analyticOn` to `F₀`
   holomorphic on `Δ₀ × {|Im w| < ρ₀}`, then replace `Δ₀` by
   `Δ := Δ₀ ∩ {z | z.re ∈ Ioo (c-ε) (d+ε)}` with `ε := min ((c-a)/2) ((b-d)/2)`, so that
   `Δ ∩ ℝ ⊆ (a,b)` (`Δ` is open, `Ioo`-preimage of a continuous map).
2. `f n z := ∫₀¹ F₀ (z,x) * ek (kEnum n) x dx` is holomorphic on `Δ` by `hhol`, and satisfies
   `‖f n z‖ ≤ M` on compacts (route the integral through `norm_integral_le_integral_norm`,
   `norm_ek` and the sup of `‖F₀‖` on `K × [0,1]`, `IsCompact.exists_bound_of_continuousOn`).
3. Apply `h10` (`P_RealCartan`) with `w n = ‖e^{2πi kEnum n α} - 1‖` and `s n = n+1`; the
   growth bound `‖f n z‖ ≤ w n * e^{M s n}` follows from the Diophantine lower bound
   `exp_lower_of_diophBelow α b₀` (with rate `b₀ + 1`, note `DiophBelow` forces `b₀ > 0`,
   `pos_of_diophBelow`) and `|kEnum n| ≤ n+1` (`natAbs_kEnum`, `abs_intCast_eq`).
4. On `[c,d]` the Cartan set equals `RedSet ∩ (a,b)`:
   * ⇐ (`RedSet →` decay): `fourier_bound_of_mem_RedSet` (Claim A) applied to the
     single-energy data `(fun y => Cj x y, fun y => φj x y)`, using `f n x = φ̂ (kEnum n)`
     (agreement clause of the complexification + `fcoef_eq_int`), `|kEnum n| ≥ (n+1)/2`, and
     `eventually_const_mul_exp_le` to absorb the constant.
   * ⇒ (decay `→ RedSet`): from `∀ᶠ n` at rate `η` get the bound for all `k ≠ 0` with
     `|k| ≥ 2(N+1)` (`kEnum_surj`, `natAbs_kEnum`, arithmetic), feed it to
     `bound_all_of_bound_large` to extend to all `k`, then `analytic_coboundary_of_decay`
     gives the analytic coboundary `ψC : ℝ → ℂ`; take `ψ := Re ψC` (via the real-part trick)
     and finish with `mem_RedSet_of_coboundary` (Claim B); `y ∈ (a,b)` comes from
     `Δ ∩ ℝ ⊆ (a,b)`.
5. Null case: `RedSet ∩ Set.Icc c d ⊆ A` and `measure_mono`; interval case: the Cartan
   interval lies in `A ⊆ RedSet ∩ Ioo a b`.-/
theorem part2_compact
    (hhol : ∀ (F : ℂ × ℂ → ℂ) (Δ : Set ℂ) (ρ : ℝ), IsOpen Δ → 0 < ρ →
      DifferentiableOn ℂ F {p : ℂ × ℂ | p.1 ∈ Δ ∧ |p.2.im| < ρ} → ∀ k : ℤ,
      DifferentiableOn ℂ (fun z : ℂ => ∫ x in (0 : ℝ)..1,
        F (z, (x : ℂ)) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (x : ℂ)))) Δ)
    (hcob : ∀ (α : ℝ), Irrational α → ∀ (φ : ℝ → ℝ), Continuous φ →
      (∀ x, φ (x + 1) = φ x) → ∀ (O : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ),
      (∀ i j, AnalyticOnNhd ℝ (fun x => O x i j) Set.univ) →
      (∀ x, O (x + 1) = O x) → (∀ x, (O x).det = 1) →
      (∀ x, O (x + α) * Work.TMContract.rot (φ x) = Work.TMContract.rot c * O x) →
      ∃ ψ : ℝ → ℝ, (∀ x, ψ (x + 1) = ψ x) ∧ AnalyticOnNhd ℝ ψ Set.univ ∧
        ∀ x, φ x - (∫ t in (0 : ℝ)..1, φ t) = ψ (x + α) - ψ x)
    (h9 : Work.TMContract.P_mAnalytic) (h10 : Work.TMContract.P_RealCartan)
    (α b₀ lam : ℝ) (hα : Irrational α) (hD : Work.TMContract.DiophBelow α b₀)
    (h0 : 0 < lam) (h1 : lam ≤ 1) (a b : ℝ) (hab : a < b)
    (hspec : Set.Ioo a b ⊆ Work.TMContract.amoSpec α lam)
    (c d : ℝ) (hac : a < c) (hcd : c ≤ d) (hdb : d < b) :
    MeasureTheory.volume (Work.TMContract.RedSet α lam ∩ Set.Icc c d) = 0 ∨
      ∃ c' d' : ℝ, c' < d' ∧ Set.Ioo c' d' ⊆ Work.TMContract.RedSet α lam ∩ Set.Ioo a b 
:= by
  classical
  have hb0 : 0 < b₀ := pos_of_diophBelow α b₀ hD
  obtain ⟨Cj, φj, hCjan, hφjan, hCjp, hφjp, hCjdet, hCjdeg, hCjconj⟩ :=
    joint_analytic_of_mAnalytic h9 α lam a b hα h0 h1 hab hspec
  set Φ : ℝ × ℝ → ℂ := fun p => ((φj p.1 p.2 : ℝ) : ℂ) with hΦdef
  have hΦan : AnalyticOnNhd ℝ Φ (Set.Ioo a b ×ˢ Set.univ) :=
    (Complex.ofRealCLM.analyticOnNhd (s := Set.univ)).comp hφjan (fun p _ => trivial)
  have hΦper : ∀ E x : ℝ, Φ (E, x + 1) = Φ (E, x) := by
    intro E x
    show ((φj E (x + 1) : ℝ) : ℂ) = ((φj E x : ℝ) : ℂ)
    rw [hφjp E x]
  set ε : ℝ := min ((c - a) / 2) ((b - d) / 2) with hεdef
  have hεpos : 0 < ε := lt_min (by linarith) (by linarith)
  have hC1a : a < c - ε := by
    have h : ε ≤ (c - a) / 2 := by rw [hεdef]; exact min_le_left _ _
    linarith
  have hD1b : d + ε < b := by
    have h : ε ≤ (b - d) / 2 := by rw [hεdef]; exact min_le_right _ _
    linarith
  have hCD : c - ε ≤ d + ε := by linarith
  obtain ⟨Δ₀, ρ₀, F₀, hΔ₀open, hΔ₀mem, hρ₀pos, hF₀diff, hF₀ag, hF₀per⟩ :=
    complexify_analyticOn Φ a b (c - ε) (d + ε) hC1a hCD hD1b hΦan hΦper
  set Δ : Set ℂ := Δ₀ ∩ {z : ℂ | z.re ∈ Set.Ioo (c - ε) (d + ε)} with hΔdef
  have hΔopen : IsOpen Δ := hΔ₀open.inter (isOpen_Ioo.preimage Complex.continuous_re)
  have hΔsub₀ : Δ ⊆ Δ₀ := Set.inter_subset_left
  have hIcc_cd : (Set.Icc c d : Set ℝ) ⊆ Set.Icc (c - ε) (d + ε) :=
    Set.Icc_subset_Icc (by linarith) (by linarith)
  have hcdmem : ∀ E ∈ Set.Icc c d, (E:ℂ) ∈ Δ := by
    intro E hE
    exact ⟨hΔ₀mem (hIcc_cd hE), by
      simp only [Set.mem_setOf_eq, Complex.ofReal_re]
      exact ⟨by linarith [hE.1], by linarith [hE.2]⟩⟩
  have hΔab : ∀ x : ℝ, (x:ℂ) ∈ Δ → x ∈ Set.Ioo a b := by
    intro x hx
    have h : c - ε < x ∧ x < d + ε := by
      simpa only [Set.mem_Ioo, Set.mem_setOf_eq, Complex.ofReal_re] using hx.2
    exact ⟨by linarith [hC1a, h.1], by linarith [hD1b, h.2]⟩
  set fn : ℕ → ℂ → ℂ := fun n z => ∫ x in (0:ℝ)..1,
      F₀ (z, (x:ℂ)) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((kEnum n : ℤ) : ℂ) * (x : ℂ))) with hfn
  have hfn_diff : ∀ n, DifferentiableOn ℂ (fn n) Δ := by
    intro n
    exact hhol F₀ Δ ρ₀ hΔopen hρ₀pos
      (hF₀diff.mono (fun p hp => ⟨hΔsub₀ hp.1, hp.2⟩)) (kEnum n)
  set w : ℕ → ℝ := fun n => ‖Complex.exp (2 * Real.pi * (kEnum n : ℝ) * α * Complex.I) - 1‖ with hw
  set sd : ℕ → ℝ := fun n => (n : ℝ) + 1 with hsd
  have hwpos : ∀ n, 0 < w n := by
    intro n
    rw [hw]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr (exp_two_pi_mul_I_mul_ne_one α hα (kEnum n) (kEnum_ne_zero n)))
  have hspos : ∀ n, 0 < sd n := by intro n; rw [hsd]; positivity
  have hw' : ∀ n : ℕ, w n
      = ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (kEnum n : ℂ) * (α : ℂ)) - 1‖ := by
    intro n
    rw [hw]
    exact congrArg (fun z : ℂ => ‖z - 1‖) (exp_factor_eq α (kEnum n))
  obtain ⟨Cdioph, hCdiophpos, hCdioph⟩ :=
    Part2.ExpLowerDioph α b₀ hα hb0 hD (b₀ + 1) (by linarith)
  have hwlower : ∀ n : ℕ, Cdioph * Real.exp (-((b₀ + 1) * ((n : ℝ) + 1))) ≤ w n := by
    intro n
    rw [hw]
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hCdiophpos.le)
      (hCdioph (kEnum n) (kEnum_ne_zero n))
    apply Real.exp_le_exp.mpr
    have h1 : |((kEnum n : ℤ) : ℝ)| = ((n / 2 + 1 : ℕ) : ℝ) := by
      rw [abs_intCast_eq, natAbs_kEnum]
    have h2 : ((n / 2 + 1 : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by
      have h3 : n / 2 + 1 ≤ n + 1 := by omega
      exact_mod_cast h3
    rw [h1]
    nlinarith [hb0, h2]
  have hbound : ∀ K ⊆ Δ, IsCompact K → ∃ M : ℝ, ∀ n, ∀ z ∈ K,
      ‖fn n z‖ ≤ w n * Real.exp (M * sd n) := by
    intro K hKΔ hKc
    by_cases hKne : K.Nonempty
    swap
    · exact ⟨0, fun n z hz => absurd ⟨z, hz⟩ hKne⟩
    · have htube : K ×ˢ (Complex.ofReal '' (Set.Icc (0:ℝ) 1)) ⊆
          {p : ℂ × ℂ | p.1 ∈ Δ₀ ∧ |p.2.im| < ρ₀} := by
        intro p hp
        refine ⟨hΔsub₀ (hKΔ hp.1), ?_⟩
        obtain ⟨t, ht, hpt⟩ := hp.2
        rw [← hpt]
        simpa only [Complex.ofReal_im, abs_zero] using hρ₀pos
      obtain ⟨M₀, hM₀⟩ := (hKc.prod (isCompact_Icc.image Complex.continuous_ofReal)).exists_bound_of_continuousOn
        ((hF₀diff.mono htube).continuousOn)
      set M₁ : ℝ := max M₀ 0 with hM₁
      have hM₁nn : 0 ≤ M₁ := le_max_right _ _
      refine ⟨(b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1, fun n z hz => ?_⟩
      have hsup : ∀ x ∈ Set.uIoc (0:ℝ) 1,
          ‖F₀ (z, (x:ℂ)) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((kEnum n : ℤ) : ℂ) * (x : ℂ)))‖ ≤ M₁ := by
        intro x hx
        have hxI : x ∈ Set.Icc (0:ℝ) 1 := by
          have h := Set.uIoc_subset_uIcc hx
          rwa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at h
        rw [norm_mul]
        have hC : ‖Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((kEnum n : ℤ) : ℂ) * (x : ℂ)))‖ = 1 := by
          rw [show -(2 * (Real.pi : ℂ) * Complex.I * ((kEnum n : ℤ) : ℂ) * (x : ℂ))
                = ((-(2 * Real.pi * (kEnum n : ℝ) * x) : ℝ) : ℂ) * Complex.I by push_cast; ring]
          exact Complex.norm_exp_ofReal_mul_I _
        rw [hC, mul_one]
        exact le_trans (hM₀ _ ⟨hz, x, hxI, rfl⟩) (le_max_left _ _)
      have hnorm : ‖fn n z‖ ≤ M₁ := by
        calc ‖fn n z‖ = ‖∫ x in (0:ℝ)..1, F₀ (z, (x:ℂ)) *
              Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((kEnum n : ℤ) : ℂ) * (x : ℂ)))‖ := rfl
          _ ≤ M₁ * |(1:ℝ) - 0| := intervalIntegral.norm_integral_le_of_norm_le_const hsup
          _ = M₁ := by norm_num
      have hlogle : Real.log (M₁ / Cdioph) ≤ (b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1 - (b₀ + 1) := by
        linarith [le_max_right (0:ℝ) (Real.log (M₁ / Cdioph))]
      have hnn : 0 ≤ (b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1 - (b₀ + 1) := by
        have := le_max_left (0:ℝ) (Real.log (M₁ / Cdioph)); linarith
      have hargle : Real.log (M₁ / Cdioph)
          ≤ ((b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1 - (b₀ + 1)) * ((n : ℝ) + 1) := by
        have hn1 : (1:ℝ) ≤ (n : ℝ) + 1 := by
          have hnn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
          linarith
        calc Real.log (M₁ / Cdioph)
            ≤ (b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1 - (b₀ + 1) := hlogle
          _ = ((b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1 - (b₀ + 1)) * 1 := by ring
          _ ≤ ((b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1 - (b₀ + 1)) * ((n : ℝ) + 1) :=
              mul_le_mul_of_nonneg_left hn1 hnn
      have hfin : M₁ ≤ Cdioph * Real.exp (((b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1 - (b₀ + 1))
          * ((n : ℝ) + 1)) := by
        rcases eq_or_lt_of_le hM₁nn with h0 | hpos
        · rw [← h0]
          exact mul_nonneg hCdiophpos.le (Real.exp_pos _).le
        · have hdiv : 0 < M₁ / Cdioph := div_pos hpos hCdiophpos
          calc M₁ = Cdioph * (M₁ / Cdioph) := by field_simp
            _ ≤ Cdioph * Real.exp (((b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1 - (b₀ + 1))
                  * ((n : ℝ) + 1)) := by
                apply mul_le_mul_of_nonneg_left _ hCdiophpos.le
                have h1 : Real.exp (Real.log (M₁ / Cdioph))
                    ≤ Real.exp (((b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1 - (b₀ + 1))
                        * ((n : ℝ) + 1)) := Real.exp_le_exp.mpr hargle
                rwa [Real.exp_log hdiv] at h1
      have hstep : Cdioph * Real.exp (((b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1 - (b₀ + 1))
            * ((n : ℝ) + 1))
          ≤ w n * Real.exp (((b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1) * ((n : ℝ) + 1)) := by
        have hw' := hwlower n
        have hexp : Cdioph * Real.exp (-((b₀ + 1) * ((n : ℝ) + 1)))
              * Real.exp (((b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1) * ((n : ℝ) + 1))
            = Cdioph * Real.exp (((b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1 - (b₀ + 1))
                * ((n : ℝ) + 1)) := by
          rw [mul_assoc, ← Real.exp_add,
            show -( (b₀ + 1) * ((n : ℝ) + 1))
                + ((b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1) * ((n : ℝ) + 1)
              = ((b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1 - (b₀ + 1)) * ((n : ℝ) + 1) by ring]
        rw [← hexp]
        exact mul_le_mul_of_nonneg_right hw' (Real.exp_pos _).le
      have hfin2 : w n * Real.exp (((b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1) * ((n : ℝ) + 1))
          = w n * Real.exp (((b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1) * sd n) := by rw [hsd]
      calc ‖fn n z‖ ≤ M₁ := hnorm
        _ ≤ Cdioph * Real.exp (((b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1 - (b₀ + 1))
              * ((n : ℝ) + 1)) := hfin
        _ ≤ w n * Real.exp (((b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1) * ((n : ℝ) + 1)) := hstep
        _ = w n * Real.exp (((b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1) * sd n) := hfin2
  have hfval : ∀ (x : ℝ) (hx : (x:ℂ) ∈ Δ) (n : ℕ),
      fn n x = fourierCoeffOn (show (0:ℝ) < 1 by norm_num) (fun y : ℝ => ((φj x y : ℝ) : ℂ)) (kEnum n) := by
    intro x hx n
    have hxIcc : x ∈ Set.Icc (c - ε) (d + ε) := by
      have h : c - ε < x ∧ x < d + ε := by
        simpa only [Set.mem_Ioo, Set.mem_setOf_eq, Complex.ofReal_re] using hx.2
      exact ⟨le_of_lt h.1, le_of_lt h.2⟩
    rw [hfn, fcoef_eq_int]
    apply intervalIntegral.integral_congr
    intro t _
    show F₀ ((x:ℂ), (t:ℂ)) * _ = ((φj x t : ℝ) : ℂ) * ek (kEnum n) t
    rw [hF₀ag x hxIcc t]
    rfl
  rcases h10 Δ hΔopen fn w sd hfn_diff hwpos hspos hbound with hA0 | ⟨c', d', hc'd', hAint⟩
  · left
    have hnull : (RedSet α lam ∩ Set.Icc c d : Set ℝ) ⊆
        {x : ℝ | (x:ℂ) ∈ Δ ∧ ∃ η : ℝ, 0 < η ∧ ∀ᶠ n in atTop, ‖fn n x‖ ≤ w n * Real.exp (-(η * sd n))} := by
      intro x hx
      obtain ⟨hxred, hxIcc⟩ := hx
      have hxΔ : (x:ℂ) ∈ Δ := hcdmem x hxIcc
      refine ⟨hxΔ, ?_⟩
      have hxab : x ∈ Set.Ioo a b := ⟨lt_of_lt_of_le hac hxIcc.1, lt_of_le_of_lt hxIcc.2 hdb⟩
      set Cl : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun y => Cj x y with hCldef
      set φl : ℝ → ℝ := fun y => φj x y with hφldef
      have hfE : AnalyticOnNhd ℝ (fun y : ℝ => (x, y)) Set.univ :=
        analyticOnNhd_const.prod analyticOnNhd_id
      have hEim : Set.MapsTo (fun y : ℝ => (x, y)) Set.univ (Set.Ioo a b ×ˢ Set.univ) :=
        fun y _ => ⟨hxab, trivial⟩
      obtain ⟨C₀, η₀, hη₀, hbnd⟩ := fourier_bound_of_mem_RedSet hcob α lam x a b hα hxab
        Cl φl (fun i j => (hCjan i j).comp hfE hEim) (fun y => hCjp x y)
        (fun y => hCjdet x hxab y) (fun y => hCjconj x hxab y)
        (hφjan.comp hfE hEim) (fun y => hφjp x y) hxred
      have hbndc : ∀ k : ℤ, k ≠ 0 →
          ‖fourierCoeffOn (show (0:ℝ) < 1 by norm_num) (fun y : ℝ => ((φl y : ℝ) : ℂ)) k‖
            ≤ max C₀ 0 * ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (α : ℂ)) - 1‖
                * Real.exp (-(η₀ * |(k : ℝ)|)) := by
        intro k hk
        exact (hbnd k hk).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (norm_nonneg _))
          (Real.exp_pos _).le)
      refine ⟨(η₀ / 2) / 2, by positivity, ?_⟩
      filter_upwards [eventually_const_mul_exp_le (max C₀ 0) (η₀ / 2) (by positivity)] with n hn
      have hmain : ‖fn n x‖ ≤ max C₀ 0 * w n * Real.exp (-((η₀ / 2) * ((n : ℝ) + 1))) := by
        have hk := hbndc (kEnum n) (kEnum_ne_zero n)
        rw [← hw' n] at hk
        rw [hfval x hxΔ n]
        refine hk.trans ?_
        have h2 : ((n : ℝ) + 1) / 2 ≤ |((kEnum n : ℤ) : ℝ)| := by
          rw [abs_intCast_eq, natAbs_kEnum]
          have h4 : n + 1 ≤ 2 * (n / 2 + 1) := by omega
          have h5 : (n : ℝ) + 1 ≤ 2 * ((n / 2 + 1 : ℕ) : ℝ) := by exact_mod_cast h4
          linarith
        apply mul_le_mul_of_nonneg_left _ (by have h2' := (hwpos n).le; positivity)
        apply Real.exp_le_exp.mpr
        nlinarith [h2, hη₀]
      calc ‖fn n x‖ ≤ max C₀ 0 * w n * Real.exp (-((η₀ / 2) * ((n : ℝ) + 1))) := hmain
        _ = w n * (max C₀ 0 * Real.exp (-((η₀ / 2) * ((n : ℝ) + 1)))) := by ring
        _ ≤ w n * Real.exp (-(((η₀ / 2) / 2) * ((n : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left hn (le_of_lt (hwpos n))
        _ = w n * Real.exp (-(((η₀ / 2) / 2) * sd n)) := by simp only [hsd]
    refine le_antisymm ?_ (by simp)
    calc MeasureTheory.volume (RedSet α lam ∩ Set.Icc c d)
        ≤ MeasureTheory.volume {x : ℝ | (x:ℂ) ∈ Δ ∧
            ∃ η : ℝ, 0 < η ∧ ∀ᶠ n in atTop, ‖fn n x‖ ≤ w n * Real.exp (-(η * sd n))} :=
          MeasureTheory.measure_mono hnull
      _ = 0 := hA0
  · right
    refine ⟨c', d', hc'd', ?_⟩
    intro x hx
    have hxA : (x:ℂ) ∈ Δ ∧ ∃ η : ℝ, 0 < η ∧ ∀ᶠ n in atTop, ‖fn n x‖ ≤ w n * Real.exp (-(η * sd n)) := hAint hx
    have hxΔ : (x:ℂ) ∈ Δ := hxA.1
    refine ⟨?_, hΔab x hxΔ⟩
    obtain ⟨η, hηpos, hev⟩ := hxA.2
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
    have hxab : x ∈ Set.Ioo a b := hΔab x hxΔ
    set C : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun y => Cj x y with hCdef
    set φ : ℝ → ℝ := fun y => φj x y with hφdef
    have hfE : AnalyticOnNhd ℝ (fun y : ℝ => (x, y)) Set.univ :=
      analyticOnNhd_const.prod analyticOnNhd_id
    have hEim : Set.MapsTo (fun y : ℝ => (x, y)) Set.univ (Set.Ioo a b ×ˢ Set.univ) :=
      fun y _ => ⟨hxab, trivial⟩
    have hCan : ∀ i j, AnalyticOnNhd ℝ (fun y => C y i j) Set.univ :=
      fun i j => (hCjan i j).comp hfE hEim
    have hCp : ∀ y, C (y + 1) = C y := by intro y; rw [hCdef]; exact hCjp x y
    have hCdet : ∀ y, (C y).det = 1 := by intro y; rw [hCdef]; exact hCjdet x hxab y
    have hCdeg : HasDegree C 0 := by rw [hCdef]; exact hCjdeg x hxab
    have hconj : ∀ y, C (y + α) * tmR lam x y = rot (φ y) * C y := by
      intro y; rw [hCdef, hφdef]; exact hCjconj x hxab y
    have hφan : AnalyticOnNhd ℝ φ Set.univ := by rw [hφdef]; exact hφjan.comp hfE hEim
    have hφp : ∀ y, φ (y + 1) = φ y := by intro y; rw [hφdef]; exact hφjp x y
    have hbdlarge : ∀ k : ℤ, ((N : ℤ) + 1) ≤ |k| →
        ‖fourierCoeffOn (show (0:ℝ) < 1 by norm_num) (fun y : ℝ => ((φ y : ℝ) : ℂ)) k‖
          ≤ ‖Complex.exp (2 * Real.pi * (k : ℝ) * α * Complex.I) - 1‖ * Real.exp (-(η * |(k : ℝ)|)) := by
      intro k hk
      have hk0 : k ≠ 0 := by
        intro h; rw [h] at hk; simp at hk; omega
      obtain ⟨n, hn⟩ := kEnum_surj k hk0
      have hnN : N ≤ n := by
        have h1 : (kEnum n).natAbs = n / 2 + 1 := natAbs_kEnum n
        rw [hn] at h1
        have h2 : ((N : ℤ) + 1) ≤ (k.natAbs : ℤ) := by
          have h3 : |k| = (k.natAbs : ℤ) := Int.abs_eq_natAbs k
          rw [h3] at hk; exact hk
        have h4 : (N : ℤ) + 1 ≤ ((n / 2 + 1 : ℕ) : ℤ) := by rw [← h1]; exact h2
        omega
      have h := hN n hnN
      rw [hfval x hxΔ n, hn] at h
      have hw'' : w n = ‖Complex.exp (2 * Real.pi * (k : ℝ) * α * Complex.I) - 1‖ := by
        simp only [hw, hn, exp_factor_eq]
      simp only [hw'', hsd] at h
      refine h.trans ?_
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Real.exp_le_exp.mpr
      have h2 : |(k : ℝ)| ≤ (n : ℝ) + 1 := by
        have h3 : (k.natAbs : ℝ) = ((n / 2 + 1 : ℕ) : ℝ) := by
          rw [← hn]
          exact_mod_cast (natAbs_kEnum n)
        rw [abs_intCast_eq, h3]
        have h4 : n / 2 + 1 ≤ n + 1 := by omega
        exact_mod_cast h4
      have h3 : η * |(k : ℝ)| ≤ η * ((n : ℝ) + 1) := mul_le_mul_of_nonneg_left h2 hηpos.le
      linarith
    obtain ⟨C₁, hC₁pos, hC₁⟩ := bound_all_of_bound_large
      (fun k : ℤ => ‖fourierCoeffOn (show (0:ℝ) < 1 by norm_num) (fun y : ℝ => ((φ y : ℝ) : ℂ)) k‖)
      (fun k : ℤ => if k = 0 then 1 else ‖Complex.exp (2 * Real.pi * (k : ℝ) * α * Complex.I) - 1‖)
      η hηpos (fun k => by
        by_cases hk : k = 0
        · simp [hk]
        · simp only [if_neg hk]
          exact norm_pos_iff.mpr (sub_ne_zero.mpr (exp_two_pi_mul_I_mul_ne_one α hα k hk)))
      ((N : ℤ) + 1) (by
        intro k hk
        have hk0 : k ≠ 0 := by intro h; rw [h] at hk; simp at hk; omega
        simpa [if_neg hk0] using hbdlarge k hk)
    have hcont : Continuous (fun y : ℝ => ((φ y : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp hφan.continuous
    have hper2 : ∀ y : ℝ, (fun y : ℝ => ((φ y : ℝ) : ℂ)) (y + 1) = (fun y : ℝ => ((φ y : ℝ) : ℂ)) y := by
      intro y
      show ((φ (y + 1) : ℝ) : ℂ) = ((φ y : ℝ) : ℂ)
      rw [hφp y]
    obtain ⟨ψC, hψCp, hψCan, hψCeq⟩ := analytic_coboundary_of_decay α hα
      (fun y : ℝ => ((φ y : ℝ) : ℂ)) hcont hper2 η hηpos C₁ hC₁pos
      (fun k hk => by simpa only [if_neg hk, mul_assoc] using hC₁ k)
    obtain ⟨ψ, hψp, hψan, hψeq⟩ := exists_real_coboundary α (∫ t in (0 : ℝ)..1, φ t) (φ := φ)
      hψCp hψCan (fun y => by
        have h := hψCeq y
        have hint : ((∫ t in (0 : ℝ)..1, φ t : ℝ) : ℂ) = ∫ t in (0 : ℝ)..1, ((φ t : ℝ) : ℂ) :=
          (ContinuousLinearMap.intervalIntegral_comp_comm Complex.ofRealCLM
            (hφan.continuous.intervalIntegrable _ _)).symm
        rw [← hint] at h
        exact h)
    exact mem_RedSet_of_coboundary α lam x C φ ψ hCan hCp hCdet hCdeg hconj hψan hψp hψeq

end Work.TMComp.RedProj
