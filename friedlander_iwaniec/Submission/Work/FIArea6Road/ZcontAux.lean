/-
# `Submission.Work.FIArea6Road.ZcontAux`

Auxiliary lemmas for `Work.FIArea6Road.ZcontExistsBound`.
-/
import Mathlib
import Submission.Work.FIArea6.TauPieces.ZcontDefs
import Submission.Work.FIArea5.S16Hecke.heckeL_inv_halfPlane
import Submission.Work.FIArea5.S16Hecke.heckeLSeries_eulerProduct_hasProd
import Submission.Work.FIArea5.S16Hecke.heckeLam_bound
import Submission.Work.FIArea5.S16Hecke.summable_card_divisors_mul_rpow_neg
import Submission.Work.FIArea6Hecke.StripCoreDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea6Road

open Finset Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

noncomputable section

theorem zcontLSeries_mul_inv {chi : GaussianInt → ℂ} {m : ℤ}
    (hchi1 : chi 1 = 1)
    (hchimul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Work.FIArea5.S16Hecke.heckeLSeries chi m s *
      (Work.FIArea5.S16Hecke.heckeLSeries chi m s)⁻¹ = 1 := by
  have hFp : Multipliable (fun p : Nat.Primes => Work.FIArea5.S16Hecke.heckeFp chi m p s) :=
    (Work.FIArea5.S16Hecke.heckeLSeries_eulerProduct_hasProd chi m hchi1 hchimul hchibd hs).multipliable
  have hGp : Multipliable (fun p : Nat.Primes => Work.FIArea5.S16Hecke.heckeGp chi m p s) :=
    Work.FIArea5.S16Hecke.multipliable_heckeGp chi m s hchimul hchibd hs
  have h := Multipliable.tprod_mul hFp hGp
  rw [tprod_congr (fun p => Work.FIArea5.S16Hecke.heckeFp_mul_heckeGp chi m p s hchimul hchi1
    hchibd (by linarith))] at h
  rw [tprod_one] at h
  have hL : (∏' p : Nat.Primes, Work.FIArea5.S16Hecke.heckeFp chi m p s)
      = Work.FIArea5.S16Hecke.heckeLSeries chi m s :=
    (Work.FIArea5.S16Hecke.heckeLSeries_eulerProduct_hasProd chi m hchi1 hchimul hchibd hs).tprod_eq
  have hG : (∏' p : Nat.Primes, Work.FIArea5.S16Hecke.heckeGp chi m p s)
      = (Work.FIArea5.S16Hecke.heckeLSeries chi m s)⁻¹ :=
    Work.FIArea5.S16Hecke.tprod_heckeGp_eq_inv chi m s hchimul hchi1 hchibd hs
  rw [hL, hG] at h
  exact h.symm

theorem zcontLSeries_ne_zero {chi : GaussianInt → ℂ} {m : ℤ}
    (hchi1 : chi 1 = 1)
    (hchimul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Work.FIArea5.S16Hecke.heckeLSeries chi m s ≠ 0 := by
  intro h
  have hh := zcontLSeries_mul_inv (m := m) hchi1 hchimul hchibd hs
  rw [h] at hh
  simp only [zero_mul] at hh
  exact zero_ne_one hh

lemma zcontPreconn_one_lt_re : IsPreconnected {s : ℂ | 1 < s.re} :=
  (convex_halfSpace_re_gt 1).isPreconnected

/-- `heckeArch d m s ≠ 0` for `re s > 0`. -/
lemma zcontArch_ne_zero {d : ℕ} (hd : 1 ≤ d) (m : ℤ) {s : ℂ} (hs : 0 < s.re) :
    Work.FITop4.Bridge.heckeArch d m s ≠ 0 := by
  have hbase' : ((((4 * (d : ℝ)) / Real.pi) : ℂ)) ≠ 0 := by
    have h4 : (0 : ℝ) < (4 : ℝ) * (d : ℝ) / Real.pi := by
      have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
      positivity
    exact_mod_cast ne_of_gt h4
  unfold Work.FITop4.Bridge.heckeArch
  refine mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hbase')) ?_
  refine Complex.Gamma_ne_zero_of_re_pos ?_
  simp only [Complex.add_re, Complex.ofReal_re]
  have := abs_nonneg (m : ℝ)
  linarith

lemma zcontArch_diff {d : ℕ} (hd : 1 ≤ d) (m : ℤ) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun t : ℂ => Work.FITop4.Bridge.heckeArch d m t) s := by
  have hbase' : ((((4 * (d : ℝ)) / Real.pi) : ℂ)) ≠ 0 := by
    have h4 : (0 : ℝ) < (4 : ℝ) * (d : ℝ) / Real.pi := by
      have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
      positivity
    exact_mod_cast ne_of_gt h4
  unfold Work.FITop4.Bridge.heckeArch
  refine DifferentiableAt.mul ?_ ?_
  · exact DifferentiableAt.const_cpow differentiableAt_id (Or.inl hbase')
  · have hshift : DifferentiableAt ℂ (fun t : ℂ => t + ((|(m : ℝ)| / 2 : ℝ) : ℂ)) s :=
      differentiableAt_id.add_const _
    have hG : DifferentiableAt ℂ Complex.Gamma (s + ((|(m : ℝ)| / 2 : ℝ) : ℂ)) := by
      refine Complex.differentiableAt_Gamma _ ?_
      intro k hk
      have hre : (s + ((|(m : ℝ)| / 2 : ℝ) : ℂ)).re = s.re + |(m : ℝ)| / 2 := by simp
      have hk2 : (s + ((|(m : ℝ)| / 2 : ℝ) : ℂ)).re = -(k : ℝ) := by rw [hk]; simp
      have hm0 : (0 : ℝ) ≤ |(m : ℝ)| / 2 := by positivity
      rw [hre] at hk2
      have hpos : (0 : ℝ) < s.re + |(m : ℝ)| / 2 := by linarith
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have := hG.comp s hshift
    simpa [Function.comp_def] using this

theorem zcontLval_eq {d : ℕ} (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (m : ℤ)
    (hchi1 : chi 1 = 1)
    (hchimul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {Lam : ℂ → ℂ}
    (hAn : AnalyticOn ℂ Lam Set.univ)
    (hagr : ∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
      Lam s = Work.FITop4.Bridge.heckeArch d m s *
        Work.FIArea5.S16Hecke.heckeLSeries chi m s)
    {s : ℂ} (hs : 1 < s.re) :
    Work.FIArea6Hecke.Lval d m Lam s = Work.FIArea5.S16Hecke.heckeLSeries chi m s := by
  set U : Set ℂ := {z : ℂ | 1 < z.re} with hUdef
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hmemi : ∀ {z : ℂ}, z ∈ U → 1 < z.re :=
    fun {z} hz => by simpa only [hUdef, Set.mem_ofPred_eq] using hz
  have hsumm : ∀ y : ℝ, 1 < y → Summable (fun n : ℕ =>
      ‖Work.FIArea5.S16Hecke.heckeLam chi m n‖ * (n : ℝ) ^ (-y)) := by
    intro y hy
    have hbase : Summable (fun n : ℕ => 4 * ((n.divisors.card : ℝ) * (n : ℝ) ^ (-y))) :=
      (Work.FIArea5.S16Hecke.summable_card_divisors_mul_rpow_neg (σ := y) hy).mul_left 4
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hbase
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      rw [Work.FIArea5.S16Hecke.heckeLam_zero]
      simp
    · have hb := Work.FIArea5.S16Hecke.heckeLam_bound chi m hchibd hnpos
      have h3 : 0 ≤ (n : ℝ) ^ (-y) := by positivity
      calc ‖Work.FIArea5.S16Hecke.heckeLam chi m n‖ * (n : ℝ) ^ (-y)
          ≤ (4 * ((n.divisors.card : ℕ) : ℝ)) * (n : ℝ) ^ (-y) :=
            mul_le_mul_of_nonneg_right hb h3
        _ = 4 * ((n.divisors.card : ℝ) * (n : ℝ) ^ (-y)) := by ring
  have habs : LSeries.abscissaOfAbsConv (Work.FIArea5.S16Hecke.heckeLam chi m) ≤ (1 : ℝ) := by
    refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable ?_
    intro y hy
    rw [LSeriesSummable]
    refine Summable.of_norm_bounded (hsumm y hy) (fun n => ?_)
    rw [LSeries.norm_term_eq]
    by_cases hn : n = 0
    · subst hn
      simp [Real.zero_rpow (by linarith : (-y) ≠ 0)]
    · rw [if_neg hn]
      have h4 : (0:ℝ) < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      rw [div_eq_mul_inv, ← Real.rpow_neg h4.le]
      exact le_refl _
  have hAnLval : AnalyticOnNhd ℂ (Work.FIArea6Hecke.Lval d m Lam) U := by
    refine DifferentiableOn.analyticOnNhd ?_ hUopen
    refine DifferentiableOn.div ?_ ?_ ?_
    · exact hAn.differentiableOn.mono (Set.subset_univ U)
    · intro w hw
      exact (zcontArch_diff hd m (by linarith [hmemi hw])).differentiableWithinAt
    · intro w hw
      exact zcontArch_ne_zero hd m (by linarith [hmemi hw])
  have hAnLser : AnalyticOnNhd ℂ (Work.FIArea5.S16Hecke.heckeLSeries chi m) U := by
    refine (LSeries_analyticOnNhd (Work.FIArea5.S16Hecke.heckeLam chi m)).mono ?_
    intro z hz
    simp only [Set.mem_ofPred_eq]
    exact lt_of_le_of_lt habs (by exact_mod_cast hmemi hz :
      ((1 : ℝ) : EReal) < (z.re : EReal))
  set z0 : ℂ := ((max 2 (2 + |(m : ℝ)|) : ℝ) : ℂ) with hz0def
  have hz0re : z0.re = max 2 (2 + |(m : ℝ)|) := by simp [hz0def]
  have hz0U : z0 ∈ U := by
    simp only [hUdef, Set.mem_ofPred_eq]
    rw [hz0re]
    exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hz0big : 1 + |(m : ℝ)| / 2 < z0.re := by
    rw [hz0re]
    have h1 : 2 + |(m : ℝ)| ≤ max 2 (2 + |(m : ℝ)|) := le_max_right _ _
    have h2 : (0:ℝ) ≤ |(m : ℝ)| := abs_nonneg _
    linarith
  have hV : {z : ℂ | 1 + |(m : ℝ)| / 2 < z.re} ∈ 𝓝 z0 := by
    have hopen : IsOpen {z : ℂ | 1 + |(m : ℝ)| / 2 < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    exact hopen.mem_nhds hz0big
  have hev : Work.FIArea6Hecke.Lval d m Lam =ᶠ[𝓝 z0]
      Work.FIArea5.S16Hecke.heckeLSeries chi m := by
    filter_upwards [hV] with z hz
    have hzpos : 0 < z.re := by
      have h1 := abs_nonneg (m : ℝ)
      linarith
    rw [Work.FIArea6Hecke.Lval, hagr z hz,
      mul_div_cancel_left₀ _ (zcontArch_ne_zero hd m hzpos)]
  have heqOn := hAnLval.eqOn_of_preconnected_of_eventuallyEq hAnLser
    (zcontPreconn_one_lt_re) hz0U hev
  exact heqOn (by simpa only [hUdef, Set.mem_ofPred_eq] using hs)

/-! ## 5. The local factors do not vanish for `re s > 1/2` -/

lemma zcontLamPrime_lt {chi : GaussianInt → ℂ} {m : ℤ}
    (hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {p : ℕ} (hp : p.Prime) {σ : ℝ}
    (hσ : 1 / 2 < σ) :
    ‖Work.FIArea5.S16Hecke.heckeLam chi m p‖ * (p : ℝ) ^ (-σ) < 1 := by
  rcases lt_or_ge p 5 with hp5 | hp5
  · interval_cases p
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · rw [Work.FIArea5.S16Hecke.heckeLam_even chi m (⟨1, by norm_num⟩ : Even 2)]
      simp
    · rw [Work.FIArea5.S16Hecke.heckeLam_prime_eq_zero_of_ne_one_mod_four hp
        (by norm_num : ¬ (3 : ℕ) % 4 = 1)]
      simp
    · exact absurd hp (by norm_num)
  · have hle : (p : ℝ) ^ (-σ) ≤ (5 : ℝ) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hp5) (by linarith)
    have hlam : ‖Work.FIArea5.S16Hecke.heckeLam chi m p‖ ≤ 2 := by
      by_cases h4 : p % 4 = 1
      · exact Work.FIArea5.S16Hecke.heckeLam_prime_norm_le_two hp h4 hchibd
      · rw [Work.FIArea5.S16Hecke.heckeLam_prime_eq_zero_of_ne_one_mod_four hp h4]
        norm_num
    have h5lt : (5 : ℝ) ^ (-σ) < 1 / 2 := by
      have hmono : (5 : ℝ) ^ ((1 : ℝ) / 2) < (5 : ℝ) ^ σ :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
      rw [← Real.sqrt_eq_rpow] at hmono
      have h2 : (2 : ℝ) < Real.sqrt 5 :=
        (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
      have hgt : (2 : ℝ) < (5 : ℝ) ^ σ := by linarith
      have heq : (5 : ℝ) ^ (-σ) = ((5 : ℝ) ^ σ)⁻¹ := Real.rpow_neg (by norm_num) σ
      rw [heq]
      have := one_div_lt_one_div_of_lt (by norm_num : (0:ℝ) < 2) hgt
      simpa [one_div] using this
    calc ‖Work.FIArea5.S16Hecke.heckeLam chi m p‖ * (p : ℝ) ^ (-σ)
        ≤ 2 * (p : ℝ) ^ (-σ) :=
          mul_le_mul_of_nonneg_right hlam (Real.rpow_nonneg (Nat.cast_nonneg p) _)
      _ ≤ 2 * (5 : ℝ) ^ (-σ) := by linarith
      _ < 1 := by linarith

lemma zcontLocF_ne_zero {chi : GaussianInt → ℂ} {m : ℤ}
    (hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {p : ℕ} (hp : p.Prime) {s : ℂ}
    (hs : 1 / 2 < s.re) :
    1 - Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s) = 1 := by
    rw [sub_eq_zero] at h; exact h.symm
  have h2 : ‖Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s)‖
      = ‖Work.FIArea5.S16Hecke.heckeLam chi m p‖ * (p : ℝ) ^ (-s.re) := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp.pos]
    simp
  rw [h1, norm_one] at h2
  have hlt := zcontLamPrime_lt (m := m) hchibd hp hs
  linarith

lemma zcontCpow_neg_diff {p : ℕ} (hp : p ≠ 0) :
    DifferentiableOn ℂ (fun t : ℂ => ((p : ℂ)) ^ (-t)) {z : ℂ | 1 / 2 < z.re} := by
  intro s hs
  have hne : ((p : ℂ)) ≠ 0 := by exact_mod_cast hp
  have h := DifferentiableAt.const_cpow (x := s) (c := ((p : ℂ))) (f := fun t : ℂ => -t)
    (DifferentiableAt.neg differentiableAt_id) (Or.inl hne)
  exact h.differentiableWithinAt

lemma zcontLocF_diff {chi : GaussianInt → ℂ} {m : ℤ}
    (hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {p : ℕ} (hp : p.Prime) :
    DifferentiableOn ℂ
      (fun s : ℂ => (1 - Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s))⁻¹)
      {z : ℂ | 1 / 2 < z.re} := by
  refine DifferentiableOn.inv ?_ ?_
  · exact ((zcontCpow_neg_diff hp.ne_zero).const_mul _).const_sub 1
  · intro s hs
    exact zcontLocF_ne_zero hchibd hp hs

/-- `Pfac` is differentiable on `re s > 1/2`. -/
lemma zcontPfac_diff (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ)
    (hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) :
    DifferentiableOn ℂ (fun s : ℂ => Work.FIArea6.TauPieces.Pfac Pa chi m s)
      {z : ℂ | 1 / 2 < z.re} := by
  have hmain := DifferentiableOn.finset_prod (𝕜 := ℂ)
    (s := {z : ℂ | 1 / 2 < z.re})
    (u := Nat.primesBelow (Pa.Pz + 1))
    (f := fun p : ℕ => fun s : ℂ =>
      (1 - Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s))⁻¹)
    (fun p hp => zcontLocF_diff hchibd (Nat.prime_of_mem_primesBelow hp))
  refine hmain.congr ?_
  intro s hs
  simp only [Finset.prod_apply, Work.FIArea6.TauPieces.Pfac]

/-- `Qfac` is differentiable on `re s > 1/2`. -/
lemma zcontQfac_diff (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ)
    (hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) :
    DifferentiableOn ℂ (fun s : ℂ => Work.FIArea6.TauPieces.Qfac Pa chi m s)
      {z : ℂ | 1 / 2 < z.re} := by
  have hmain := DifferentiableOn.sum (𝕜 := ℂ)
    (s := {z : ℂ | 1 / 2 < z.re})
    (u := (Finset.Icc 1 ⌊Pa.C⌋₊).filter
      (fun c => Squarefree c ∧ Nat.Coprime c (∏ p ∈ Nat.primesBelow (Pa.Pz + 1), p)))
    (A := fun c : ℕ => fun s : ℂ =>
      Work.FIArea5.S16Hecke.heckeLam chi m c * (c : ℂ) ^ (-s)
        * ∏ p ∈ c.primeFactors,
            (1 - Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s))⁻¹)
    (fun c hc => by
      have hcI : c ∈ Finset.Icc 1 ⌊Pa.C⌋₊ := (Finset.mem_filter.mp hc).1
      have hcne : c ≠ 0 := by
        have h1 : 1 ≤ c := (Finset.mem_Icc.mp hcI).1
        omega
      refine DifferentiableOn.mul ?_ ?_
      · exact (zcontCpow_neg_diff hcne).const_mul _
      · have hprod := DifferentiableOn.finset_prod (𝕜 := ℂ) (s := {z : ℂ | 1 / 2 < z.re})
          (u := c.primeFactors)
          (f := fun p : ℕ => fun s : ℂ =>
            (1 - Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s))⁻¹)
          (fun p hp => zcontLocF_diff hchibd (Nat.prime_of_mem_primeFactors hp))
        refine hprod.congr ?_
        intro s hs
        simp only [Finset.prod_apply])
  refine hmain.congr ?_
  intro s hs
  simp only [Finset.sum_apply, Work.FIArea6.TauPieces.Qfac]

lemma zcontConvex_pos_re : Convex ℝ {s : ℂ | 0 < s.re} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  have hre : (a • x + b • y).re = a * x.re + b * y.re := by simp
  rw [hre]
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · subst ha0
    have hb1 : b = 1 := by linarith
    simp only [zero_mul, zero_add, hb1, one_mul]
    exact hy
  · nlinarith [mul_pos ha0 hx, mul_nonneg hb hy.le]

lemma zcontPreconn_pos_re : IsPreconnected {s : ℂ | 0 < s.re} :=
  zcontConvex_pos_re.isPreconnected

/-- **`Lam/heckeArch` has no zero on the analyticity region of `ZcontExistsBound`.** -/
lemma zcontLval_ne_zero {d : ℕ} (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ)
    (ε c_h C_h : ℝ) (hε : 0 < ε) (hc_h : 0 < c_h) (hC_h : 0 < C_h)
    (hchi1 : chi 1 = 1)
    (hchimul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1)
    (hAn : AnalyticOn ℂ Lam Set.univ)
    (hagr : ∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
      Lam s = Work.FITop4.Bridge.heckeArch d m s * Work.FIArea5.S16Hecke.heckeLSeries chi m s)
    (hinv : ∀ s : ℂ,
        1 - c_h / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) < s.re → s.re ≤ 2 →
        ‖(Lam s / Work.FITop4.Bridge.heckeArch d m s)⁻¹‖
          ≤ C_h * (d : ℝ) * (Real.log (|(m : ℝ)| + |s.im| + 3)) ^ (2 : ℕ))
    {s : ℂ} (hs : 1 / 2 < s.re ∧
        1 - c_h / (2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) < s.re) :
    Lam s / Work.FITop4.Bridge.heckeArch d m s ≠ 0 := by
  by_cases hle : s.re ≤ 1
  · set f : ℂ → ℂ := fun t => Lam t / Work.FITop4.Bridge.heckeArch d m t with hf
    by_contra hs0
    have hs0' : f s = 0 := by simpa only [hf] using hs0
    have hfAn : AnalyticOnNhd ℂ f {z : ℂ | 0 < z.re} := by
      refine DifferentiableOn.analyticOnNhd ?_ (isOpen_lt continuous_const Complex.continuous_re)
      refine DifferentiableOn.div ?_ ?_ ?_
      · exact hAn.differentiableOn.mono (Set.subset_univ _)
      · intro w hw
        exact (zcontArch_diff hd m hw).differentiableWithinAt
      · intro w hw
        exact zcontArch_ne_zero hd m hw
    have hsr : (0 : ℝ) < s.re := by linarith [hs.1]
    rcases (hfAn s hsr).eventually_eq_zero_or_eventually_ne_zero with h0 | h0
    · have hzero := hfAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero zcontPreconn_pos_re
        hsr h0
      have h2 : f 2 = 0 := by
        have := hzero (show (2 : ℂ) ∈ {z : ℂ | 0 < z.re} from by norm_num)
        simpa using this
      have hLval2 : Work.FIArea6Hecke.Lval d m Lam 2 = 0 := by
        change f 2 = 0
        exact h2
      have hL2 := zcontLval_eq hd chi m hchi1 hchimul hchibd hAn hagr
        (s := 2) (by norm_num : (1 : ℝ) < (2 : ℂ).re)
      rw [hL2] at hLval2
      exact zcontLSeries_ne_zero hchi1 hchimul hchibd
        (by norm_num : (1 : ℝ) < (2 : ℂ).re) hLval2
    · set M : ℝ := C_h * (d : ℝ) * (Real.log (|(m : ℝ)| + |s.im| + 1 + 3)) ^ (2 : ℕ) with hMdef
      have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
      have hlogM : 1 < |(m : ℝ)| + |s.im| + 1 + 3 := by
        have h1 := abs_nonneg (m : ℝ)
        have h2 := abs_nonneg s.im
        linarith
      have hMpos : 0 < M := by
        rw [hMdef]
        have h3 : 0 < Real.log (|(m : ℝ)| + |s.im| + 1 + 3) := Real.log_pos hlogM
        positivity
      have h1 : ∀ᶠ w in 𝓝 s, ‖f w‖ < 1 / M := by
        have hcont := (hfAn s hsr).continuousAt
        rw [Metric.continuousAt_iff] at hcont
        obtain ⟨δ, hδ, hδ'⟩ := hcont (1 / M) (by positivity)
        filter_upwards [Metric.ball_mem_nhds s hδ] with w hw
        have := hδ' hw
        simpa [Complex.dist_eq, hs0'] using this
      have hcontlog : Continuous (fun w : ℂ =>
          1 - c_h / (2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |w.im| + 3))) := by
        have hin : Continuous (fun w : ℂ => |(m : ℝ)| + |w.im| + 3) :=
          (continuous_const.add Complex.continuous_im.abs).add continuous_const
        have hlogc : Continuous (fun w : ℂ => Real.log (|(m : ℝ)| + |w.im| + 3)) :=
          Continuous.log hin (fun w => by
            have h1 := abs_nonneg (m : ℝ)
            have h2 := abs_nonneg w.im
            linarith)
        refine Continuous.sub continuous_const ?_
        refine Continuous.div continuous_const ?_ ?_
        · exact (continuous_const.mul hlogc)
        · intro w
          have h1 : 0 < (d : ℝ) ^ ε := Real.rpow_pos_of_pos hdR _
          have h2 : 0 < Real.log (|(m : ℝ)| + |w.im| + 3) := by
            apply Real.log_pos
            have h3 := abs_nonneg (m : ℝ)
            have h4 := abs_nonneg w.im
            linarith
          positivity
      have h2 : ∀ᶠ w in 𝓝 s, ‖(f w)⁻¹‖ ≤ M := by
        have hopen : {z : ℂ | 1 - c_h / (2 * (d : ℝ) ^ ε *
            Real.log (|(m : ℝ)| + |z.im| + 3)) < z.re} ∈ 𝓝 s :=
          (isOpen_lt hcontlog Complex.continuous_re).mem_nhds hs.2
        have hlt2 : {z : ℂ | z.re < 2} ∈ 𝓝 s :=
          (isOpen_lt Complex.continuous_re continuous_const).mem_nhds (by linarith : s.re < 2)
        have hball : Metric.ball s 1 ∈ 𝓝 s := Metric.ball_mem_nhds s (by norm_num)
        filter_upwards [hopen, hlt2, hball] with w hwU hw2 hwball
        have hdw : dist w s < 1 := hwball
        rw [Complex.dist_eq] at hdw
        have hwim : |w.im| ≤ |s.im| + 1 := by
          have h1 : |(w - s).im| ≤ ‖w - s‖ := Complex.abs_im_le_norm _
          have hsplit : w.im = (w - s).im + s.im := by simp
          have h2 : |(w - s).im + s.im| ≤ |(w - s).im| + |s.im| := abs_add_le _ _
          rw [hsplit]
          linarith
        have hlog_le : Real.log (|(m : ℝ)| + |w.im| + 3)
            ≤ Real.log (|(m : ℝ)| + |s.im| + 1 + 3) := by
          apply Real.log_le_log (by positivity)
          linarith
        have hlog_nn : 0 ≤ Real.log (|(m : ℝ)| + |w.im| + 3) := by
          apply Real.log_nonneg
          have h3 := abs_nonneg (m : ℝ)
          have h4 := abs_nonneg w.im
          linarith
        have hX : 0 < (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |w.im| + 3) := by
          have h1 : 0 < (d : ℝ) ^ ε := Real.rpow_pos_of_pos hdR _
          have h2 : 0 < Real.log (|(m : ℝ)| + |w.im| + 3) := by
            apply Real.log_pos
            have h3 := abs_nonneg (m : ℝ)
            have h4 := abs_nonneg w.im
            linarith
          positivity
        have hhinv : 1 - c_h / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |w.im| + 3)) < w.re := by
          have hlt : c_h / (2 * ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |w.im| + 3)))
              < c_h / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |w.im| + 3)) := by
            have hkey : c_h / (2 * ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |w.im| + 3)))
                = c_h / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |w.im| + 3)) / 2 := by
              rw [mul_comm, div_mul_eq_div_div]
            rw [hkey]
            exact half_lt_self (div_pos hc_h hX)
          have hmul : 2 * (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |w.im| + 3)
              = 2 * ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |w.im| + 3)) := by ring
          rw [hmul] at hwU
          linarith
        have hb := hinv w hhinv (le_of_lt hw2)
        calc ‖(f w)⁻¹‖ = ‖(Lam w / Work.FITop4.Bridge.heckeArch d m w)⁻¹‖ := rfl
          _ ≤ C_h * (d : ℝ) * (Real.log (|(m : ℝ)| + |w.im| + 3)) ^ (2 : ℕ) := hb
          _ ≤ C_h * (d : ℝ) * (Real.log (|(m : ℝ)| + |s.im| + 1 + 3)) ^ (2 : ℕ) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact pow_le_pow_left₀ hlog_nn hlog_le 2
          _ = M := by rw [hMdef]
      have hcomb : ∀ᶠ w in 𝓝[≠] s, f w ≠ 0 ∧ ‖f w‖ < 1 / M ∧ ‖(f w)⁻¹‖ ≤ M :=
        h0.and ((h1.filter_mono nhdsWithin_le_nhds).and
          (h2.filter_mono nhdsWithin_le_nhds))
      obtain ⟨w, hw0, hw1, hw2'⟩ := Filter.Eventually.exists hcomb
      have hfw : 0 < ‖f w‖ := norm_pos_iff.mpr hw0
      have hineq : (1 : ℝ) ≤ ‖f w‖ * M := by
        have h3 : ‖f w‖ * ‖(f w)⁻¹‖ ≤ ‖f w‖ * M := mul_le_mul_of_nonneg_left hw2' hfw.le
        rwa [norm_inv, mul_inv_cancel₀ (ne_of_gt hfw)] at h3
      have hfin : 1 / M ≤ ‖f w‖ := by
        rw [div_le_iff₀ hMpos]
        linarith
      linarith
  · have hgt : 1 < s.re := not_le.mp hle
    have hL := zcontLval_eq hd chi m hchi1 hchimul hchibd hAn hagr hgt
    change Work.FIArea6Hecke.Lval d m Lam s ≠ 0
    rw [hL]
    exact zcontLSeries_ne_zero hchi1 hchimul hchibd hgt

end

end Work.FIArea6Road
