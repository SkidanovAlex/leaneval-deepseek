import Mathlib
import Submission.Work.FIArea6Hecke.R.exists_completion_strict
import Submission.Work.FIArea6Hecke.R.thetaHol_zero_one_div
import Submission.Work.FIArea6Hecke.R.thetaDual_decay
import Submission.Work.FIArea6Hecke.ZFRDefs
import Submission.Work.FIArea6Hecke.R.A6HeckeDual
import Submission.Work.FIArea5.S16Hecke.mellin_thetaHol
import Submission.Work.FIArea6Hecke.R.unitSum_eq_four
import Submission.Work.FIArea6Hecke.R.latticeCubic_summable
import Submission.Work.FIArea6Hecke.R.gammaRatio_negHalf
import Submission.Work.FIArea6Hecke.R.LvalStripDualMellinAux

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

/-! ## Auxiliary analytic facts -/

/-- A complex power of a positive real never vanishes. -/
private lemma cpow_ofReal_pos_ne_zero {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ((r : ℝ) : ℂ) ^ z ≠ 0 := by
  intro hc
  have h := Complex.norm_cpow_eq_rpow_re_of_pos hr z
  rw [hc, norm_zero] at h
  have hp : 0 < r ^ z.re := Real.rpow_pos_of_pos hr _
  linarith

/-- At the point `3/2 - it`, the norm of `(ξ₁² + ξ₂²)^{-s}` is `(ξ₁² + ξ₂²)^{-3/2}`. -/
private lemma norm_cpow_lattice (t : ℝ) (ξ : ℤ × ℤ) :
    ‖(((((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2 : ℝ))) : ℂ) ^
        (-(((3 / 2 : ℝ) : ℂ) - (t : ℂ) * Complex.I))‖
      = (((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) ^ (-(3 / 2 : ℝ))) := by
  rcases eq_or_ne ((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) 0 with h | h
  · have hzero : ((0 : ℂ)) ^ (-(((3 / 2 : ℝ) : ℂ) - (t : ℂ) * Complex.I)) = 0 :=
      Complex.zero_cpow (x := -(((3 / 2 : ℝ) : ℂ) - (t : ℂ) * Complex.I)) (by
        have h2 : (-(((3 / 2 : ℝ) : ℂ) - (t : ℂ) * Complex.I)).re = -(3 / 2 : ℝ) := by
          simp [Complex.sub_re, Complex.mul_re]
        intro hc
        rw [hc, Complex.zero_re] at h2
        norm_num at h2)
    rw [h, Complex.ofReal_zero, hzero, norm_zero,
      Real.zero_rpow (by norm_num : (-(3 / 2 : ℝ)) ≠ 0)]
  · have hpos : (0 : ℝ) < (ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2 :=
      lt_of_le_of_ne (by positivity) (Ne.symm h)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    congr 1
    simp [Complex.sub_re, Complex.mul_re]

/-- The exponent bookkeeping `π^{-1/2}·π^{-3/2} = π^{-2}`. -/
private lemma pi_rpow_neg_half_mul :
    Real.pi ^ (-(1 / 2 : ℝ)) * Real.pi ^ (-(3 / 2 : ℝ)) = 1 / Real.pi ^ 2 := by
  rw [← Real.rpow_add Real.pi_pos]
  norm_num

/-! ## The main theorem -/

/-- **The `re s = -1/2` line bound for the canonical Hecke completion, with an absolute constant.**
For a strict `χ` mod `4d` with `‖χ‖ ≤ 1` whose unit sum is nonzero and whose `0`-th Gauss sum
vanishes, every entire `Lam` agreeing with `heckeArch d 0 s · heckeLSeries χ 0 s` on `re s > 1`
satisfies `‖Lval d 0 Lam (-1/2+it)‖ ≤ K·d^3·(1+|t|)^2` with `K` absolute (independent of `d`, `χ`). -/
theorem heckeLval_negHalf_bound' :
    ∃ K : ℝ, 0 < K ∧
      ∀ (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ),
        Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
        (∀ z : GaussianInt, ‖chi z‖ ≤ 1) →
        Work.FIArea5.S16Hecke.unitSum chi 0 ≠ 0 →
        Work.FIArea5.S16Hecke.gaussSum d chi 0 = 0 →
        ∀ (Lam : ℂ → ℂ), AnalyticOn ℂ Lam Set.univ →
        (∀ s : ℂ, 1 < s.re →
          Lam s = Work.FITop4.Bridge.heckeArch d 0 s *
            Work.FIArea5.S16Hecke.heckeLSeries chi 0 s) →
        ∀ t : ℝ,
          ‖Work.FIArea6Hecke.Lval d 0 Lam (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
            ≤ K * (d : ℝ) ^ (3 : ℕ) * (1 + |t|) ^ (2 : ℕ) := by
  have hSlat_summable : Summable (fun p : ℤ × ℤ =>
      (((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) ^ (-(3 / 2 : ℝ)))) :=
    latticeCubic_summable (by norm_num : (1 : ℝ) < 3 / 2)
  set Slat : ℝ := ∑' p : ℤ × ℤ, (((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) ^ (-(3 / 2 : ℝ))) with hSlatdef
  have hSlatnn : 0 ≤ Slat := by
    rw [hSlatdef]
    exact tsum_nonneg (fun p => Real.rpow_nonneg (by positivity) _)
  refine ⟨16 * Slat / Real.pi ^ 2 + 1, ?_, ?_⟩
  · have h : 0 ≤ 16 * Slat / Real.pi ^ 2 := div_nonneg (by linarith) (by positivity)
    linarith
  intro d hd chi hchi hb hU h0 Lam hAn hagr t
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have h4dpos : (0 : ℝ) < 4 * (d : ℝ) := by linarith
  have h16pos : (0 : ℝ) < 16 * (d : ℝ) ^ 2 := by positivity
  have hU4 : Work.FIArea5.S16Hecke.unitSum chi 0 = 4 := unitSum_eq_four hchi hU
  have h4dne : ((4 * (d : ℝ)) : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr (ne_of_gt hdR))
  obtain ⟨hf_cont, hf_dec⟩ := thetaHol_zero_basic hd hchi
  have hf_int : MeasureTheory.LocallyIntegrableOn
      (fun u : ℝ => Work.FIArea5.S16Hecke.thetaHol chi 0 u) (Set.Ioi 0) :=
    hf_cont.locallyIntegrableOn measurableSet_Ioi
  have htd_cont : ContinuousOn (thetaDual d chi) (Set.Ioi 0) := continuousOn_thetaDual d hb
  have hg_cont : ContinuousOn (thetaDualG d chi) (Set.Ioi 0) := by
    have hscale : Continuous (fun x : ℝ => x / (16 * (d : ℝ) ^ 2)) := continuous_id.div_const _
    have hmaps : Set.MapsTo (fun x : ℝ => x / (16 * (d : ℝ) ^ 2)) (Set.Ioi 0) (Set.Ioi 0) := by
      intro x hx
      simp only [Set.mem_Ioi] at hx ⊢
      positivity
    have hcomp : ContinuousOn (fun x : ℝ => thetaDual d chi (x / (16 * (d : ℝ) ^ 2)))
        (Set.Ioi 0) := htd_cont.comp hscale.continuousOn hmaps
    unfold thetaDualG
    exact continuousOn_const.mul hcomp
  have hg_int : MeasureTheory.LocallyIntegrableOn (thetaDualG d chi) (Set.Ioi 0) :=
    hg_cont.locallyIntegrableOn measurableSet_Ioi
  obtain ⟨C, hC⟩ := thetaDual_decay hd hb h0
  have hg_dec : ∃ C' u₀ : ℝ, 0 < u₀ ∧ ∀ u : ℝ, u₀ ≤ u →
      ‖thetaDualG d chi u‖ ≤ C' * Real.exp (-(Real.pi / (16 * (d : ℝ) ^ 2)) * u) := by
    refine ⟨‖(Work.FIArea5.S16Hecke.unitSum chi 0)⁻¹ * (1 / (16 * (d : ℝ) ^ 2))‖ * C,
      16 * (d : ℝ) ^ 2, h16pos, ?_⟩
    intro u hu
    have harg : 1 ≤ u / (16 * (d : ℝ) ^ 2) := by
      rw [le_div_iff₀ h16pos]; linarith
    have h1 : ‖thetaDual d chi (u / (16 * (d : ℝ) ^ 2))‖
        ≤ C * Real.exp (-Real.pi * (u / (16 * (d : ℝ) ^ 2))) := hC _ harg
    rw [thetaDualG]
    calc ‖(Work.FIArea5.S16Hecke.unitSum chi 0)⁻¹ * (1 / (16 * (d : ℝ) ^ 2)) *
          thetaDual d chi (u / (16 * (d : ℝ) ^ 2))‖
        = ‖(Work.FIArea5.S16Hecke.unitSum chi 0)⁻¹ * (1 / (16 * (d : ℝ) ^ 2))‖ *
            ‖thetaDual d chi (u / (16 * (d : ℝ) ^ 2))‖ := norm_mul _ _
      _ ≤ ‖(Work.FIArea5.S16Hecke.unitSum chi 0)⁻¹ * (1 / (16 * (d : ℝ) ^ 2))‖ *
            (C * Real.exp (-Real.pi * (u / (16 * (d : ℝ) ^ 2)))) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = (‖(Work.FIArea5.S16Hecke.unitSum chi 0)⁻¹ * (1 / (16 * (d : ℝ) ^ 2))‖ * C) *
            Real.exp (-(Real.pi / (16 * (d : ℝ) ^ 2)) * u) := by
          rw [show -Real.pi * (u / (16 * (d : ℝ) ^ 2))
              = -(Real.pi / (16 * (d : ℝ) ^ 2)) * u by ring]
          ring
  have hfe : ∀ x ∈ Set.Ioi (0 : ℝ),
      (fun u : ℝ => Work.FIArea5.S16Hecke.thetaHol chi 0 u) (1 / x)
        = (1 * ((x ^ (1 : ℝ) : ℝ) : ℂ)) • (thetaDualG d chi) x := by
    intro x hx
    have hx0 : 0 < x := hx
    change Work.FIArea5.S16Hecke.thetaHol chi 0 (1 / x)
      = (1 * ((x ^ (1 : ℝ) : ℝ) : ℂ)) • thetaDualG d chi x
    rw [thetaHol_zero_one_div hd hchi hU hx0]
    simp only [Real.rpow_one, one_mul, smul_eq_mul]
    rw [thetaDualG]
  let P : WeakFEPair ℂ :=
    { f := fun u : ℝ => Work.FIArea5.S16Hecke.thetaHol chi 0 u
      g := thetaDualG d chi
      k := 1
      ε := 1
      f₀ := 0
      g₀ := 0
      hf_int := hf_int
      hg_int := hg_int
      hk := one_pos
      hε := one_ne_zero
      h_feq := hfe
      hf_top := fun r => by
        simpa only [sub_zero] using isBigO_rpow_of_exp_decay Real.pi_pos hf_dec r
      hg_top := fun r => by
        simpa only [sub_zero] using
          isBigO_rpow_of_exp_decay (show (0 : ℝ) < Real.pi / (16 * (d : ℝ) ^ 2) by positivity)
            hg_dec r }
  have hP : IsStrongFEPair P := ⟨rfl, rfl⟩
  have hΛeq : P.Λ = mellin (fun u : ℝ => Work.FIArea5.S16Hecke.thetaHol chi 0 u) := hP.Λ_eq
  have hΛan : AnalyticOn ℂ (fun s : ℂ => ((4 * (d : ℝ)) : ℂ) ^ s * P.Λ s) Set.univ := by
    refine DifferentiableOn.analyticOn ?_ isOpen_univ
    intro s _
    exact ((differentiableAt_id.const_cpow (Or.inl h4dne)).mul
      (hP.differentiable_Λ s)).differentiableWithinAt
  have hΛagr : ∀ s : ℂ, 1 < s.re →
      ((4 * (d : ℝ)) : ℂ) ^ s * P.Λ s
        = Work.FITop4.Bridge.heckeArch d 0 s * Work.FIArea5.S16Hecke.heckeLSeries chi 0 s := by
    intro s hs
    have hmellin : mellin (fun u : ℝ => Work.FIArea5.S16Hecke.thetaHol chi 0 u) s
        = Complex.Gamma s * (Real.pi : ℂ) ^ (-s) *
            Work.FIArea5.S16Hecke.heckeLSeries chi 0 s := by
      have h := Work.FIArea5.S16Hecke.mellin_thetaHol chi 0 hb (s := s) (by simpa using hs)
      rw [mellin]
      have hswap : (fun x : ℝ => (x : ℂ) ^ (s - 1) • Work.FIArea5.S16Hecke.thetaHol chi 0 x)
          = fun x : ℝ => Work.FIArea5.S16Hecke.thetaHol chi 0 x * (x : ℂ) ^ (s - 1) := by
        funext x
        rw [smul_eq_mul, mul_comm]
      rw [hswap]
      simpa using h
    have hPΛ : P.Λ s = Complex.Gamma s * (Real.pi : ℂ) ^ (-s) *
        Work.FIArea5.S16Hecke.heckeLSeries chi 0 s := by
      rw [hΛeq, hmellin]
    rw [hPΛ, Work.FITop4.Bridge.heckeArch]
    have hgam : Complex.Gamma (s + ((|(((0 : ℤ) : ℝ))| / 2 : ℝ) : ℂ)) = Complex.Gamma s := by
      norm_num
    rw [hgam]
    have hbase : ((4 * (d : ℝ)) : ℂ) = (((4 * (d : ℝ) : ℝ)) : ℂ) := by push_cast; ring
    have hkey : (((4 * (d : ℝ) : ℝ) : ℂ) / (Real.pi : ℂ)) ^ s
        = (((4 * (d : ℝ) : ℝ) : ℂ)) ^ s * (Real.pi : ℂ) ^ (-s) := by
      rw [Complex.div_cpow_ofReal_nonneg (le_of_lt h4dpos) Real.pi_nonneg,
        Complex.cpow_neg, div_eq_mul_inv]
    rw [hbase, hkey]
    ring
  have hLam : Lam = fun s : ℂ => ((4 * (d : ℝ)) : ℂ) ^ s * P.Λ s :=
    eq_of_agrees_right (fun s : ℂ => ((4 * (d : ℝ)) : ℂ) ^ s * P.Λ s) Lam hΛan hAn
      (fun s hs => by rw [hagr s hs, hΛagr s hs])
  have hFE : ∀ s : ℂ, mellin (fun u : ℝ => Work.FIArea5.S16Hecke.thetaHol chi 0 u) (1 - s)
      = mellin (thetaDualG d chi) s := by
    intro s
    have hsymm : P.symm.Λ = mellin (thetaDualG d chi) := hP.symm.Λ_eq
    have h1 : P.Λ (1 - s) = P.symm.Λ s := by
      have hPk : P.k = (1 : ℝ) := rfl
      have hPε : P.ε = (1 : ℂ) := rfl
      have h := P.functional_equation s
      rw [hPk] at h
      have hc : (↑(1 : ℝ) : ℂ) - s = 1 - s := by push_cast; ring
      rw [hc, hPε, one_smul] at h
      exact h
    rw [hΛeq] at h1
    rw [hsymm] at h1
    exact h1
  set s0 : ℂ := ((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I with hs0def
  set s1 : ℂ := (((3 / 2 : ℝ)) : ℂ) - (t : ℂ) * Complex.I with hs1def
  have hs0re : s0.re = -(1 / 2 : ℝ) := by
    rw [hs0def]
    simp [Complex.add_re, Complex.mul_re]
    norm_num
  have hs1re : s1.re = (3 / 2 : ℝ) := by
    rw [hs1def]
    simp [Complex.sub_re, Complex.mul_re]
  have hs1gt : 1 < s1.re := by rw [hs1re]; norm_num
  have hs0s1 : s0 = 1 - s1 := by
    rw [hs0def, hs1def]
    push_cast
    ring
  have hsumL : Summable (fun ξ : ℤ × ℤ =>
      (((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) ^ (-s1.re))) := by
    rw [hs1re]
    exact latticeCubic_summable (by norm_num : (1 : ℝ) < 3 / 2)
  have hGauss : ∀ ξ : ℤ × ℤ,
      ‖Work.FIArea5.S16Hecke.gaussSum d chi ⟨ξ.1, ξ.2⟩‖ ≤ (4 * (d : ℝ)) ^ 2 := by
    intro ξ
    have h := thetaDualGaussBound_aux d hb ⟨ξ.1, ξ.2⟩
    have he : (((4 * d : ℕ) : ℝ)) ^ 2 = (4 * (d : ℝ)) ^ 2 := by push_cast; ring
    rwa [he] at h
  have hpoint : ∀ ξ : ℤ × ℤ,
      ‖Work.FIArea5.S16Hecke.gaussSum d chi ⟨ξ.1, ξ.2⟩ *
          ((((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s1))‖
        ≤ (4 * (d : ℝ)) ^ 2 * (((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) ^ (-(3 / 2 : ℝ))) := by
    intro ξ
    rw [norm_mul]
    have hcp : ‖(((((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2 : ℝ))) : ℂ) ^ (-s1)‖
        = (((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) ^ (-(3 / 2 : ℝ))) := by
      rw [hs1def]
      exact norm_cpow_lattice t ξ
    rw [hcp]
    exact mul_le_mul_of_nonneg_right (hGauss ξ) (Real.rpow_nonneg (by positivity) _)
  have hSigSumm : Summable (fun ξ : ℤ × ℤ =>
      ‖Work.FIArea5.S16Hecke.gaussSum d chi ⟨ξ.1, ξ.2⟩ *
        ((((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s1))‖) :=
    Summable.of_nonneg_of_le (fun ξ => norm_nonneg _) hpoint (hSlat_summable.mul_left _)
  have hSig : ‖∑' ξ : ℤ × ℤ, Work.FIArea5.S16Hecke.gaussSum d chi ⟨ξ.1, ξ.2⟩ *
      ((((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s1))‖
        ≤ (4 * (d : ℝ)) ^ 2 * Slat := by
    refine (norm_tsum_le_tsum_norm hSigSumm).trans ?_
    have h2 : Summable (fun ξ : ℤ × ℤ => (4 * (d : ℝ)) ^ 2 *
        (((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) ^ (-(3 / 2 : ℝ)))) :=
      hSlat_summable.mul_left _
    calc ∑' ξ : ℤ × ℤ, ‖Work.FIArea5.S16Hecke.gaussSum d chi ⟨ξ.1, ξ.2⟩ *
          ((((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s1))‖
        ≤ ∑' ξ : ℤ × ℤ, (4 * (d : ℝ)) ^ 2 *
            (((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) ^ (-(3 / 2 : ℝ))) :=
          Summable.tsum_le_tsum hpoint hSigSumm h2
      _ = (4 * (d : ℝ)) ^ 2 * Slat := by
          rw [hSlatdef]
          exact tsum_mul_left
  have hmellinG := mellin_thetaDualG' hd hb h0 hs1gt hsumL
  have hmG : ‖mellin (thetaDualG d chi) s1‖ ≤
      (1 / 4) * (1 / (16 * (d : ℝ) ^ 2)) * ((16 * (d : ℝ) ^ 2) ^ ((3 : ℝ) / 2)) *
        (‖Complex.Gamma s1‖ * Real.pi ^ (-(3 / 2 : ℝ)) * ((4 * (d : ℝ)) ^ 2 * Slat)) := by
    rw [hmellinG]
    have hUinv : ‖(Work.FIArea5.S16Hecke.unitSum chi 0)⁻¹‖ = 1 / 4 := by
      rw [norm_inv, hU4]
      norm_num
    have hc1 : ‖(1 : ℂ) / ((16 : ℂ) * (((d : ℝ) : ℂ)) ^ 2)‖ = 1 / (16 * (d : ℝ) ^ 2) := by
      have hden : ((16 : ℂ) * (((d : ℝ) : ℂ)) ^ 2) = ((((16 * (d : ℝ) ^ 2 : ℝ)) : ℂ)) := by
        push_cast; ring
      rw [hden, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h16pos]
    have hc2 : ‖((((16 * (d : ℝ) ^ 2 : ℝ))) : ℂ) ^ s1‖ =
        (16 * (d : ℝ) ^ 2) ^ ((3 : ℝ) / 2) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos h16pos, hs1re]
    have hc3 : ‖((Real.pi : ℂ)) ^ (-s1)‖ = Real.pi ^ (-(3 / 2 : ℝ)) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, Complex.neg_re, hs1re]
    simp only [norm_mul]
    rw [hUinv, hc1, hc2, hc3]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSig ?_) ?_
    · exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg Real.pi_pos.le _)
    · positivity
  have hLam_s0 : Lam s0 = ((4 * (d : ℝ)) : ℂ) ^ s0 * mellin (thetaDualG d chi) s1 := by
    rw [hLam]
    dsimp only
    have hPΛs : P.Λ s0 = mellin (thetaDualG d chi) s1 := by
      rw [hs0s1, congrFun hΛeq (1 - s1)]
      exact hFE s1
    rw [hPΛs]
  have hπne : (Real.pi : ℂ) ^ s0 ≠ 0 := cpow_ofReal_pos_ne_zero Real.pi_pos s0
  have hbase : ((4 * (d : ℝ)) : ℂ) = (((4 * (d : ℝ) : ℝ)) : ℂ) := by push_cast; ring
  have hXne : ((((4 * (d : ℝ) : ℝ)) : ℂ) / (Real.pi : ℂ)) ^ s0 ≠ 0 := by
    rw [Complex.div_cpow_ofReal_nonneg (by positivity) Real.pi_nonneg]
    exact div_ne_zero (cpow_ofReal_pos_ne_zero (by positivity) s0) hπne
  have hkeyπ : ((((4 * (d : ℝ) : ℝ)) : ℂ) / (Real.pi : ℂ)) ^ s0 * (Real.pi : ℂ) ^ s0
      = (((4 * (d : ℝ) : ℝ)) : ℂ) ^ s0 := by
    rw [Complex.div_cpow_ofReal_nonneg (by positivity) Real.pi_nonneg]
    exact div_mul_cancel₀ _ hπne
  have hLval : Lval d 0 Lam s0
      = (Real.pi : ℂ) ^ s0 * mellin (thetaDualG d chi) s1 / Complex.Gamma s0 := by
    rw [Lval, hLam_s0, Work.FITop4.Bridge.heckeArch]
    have hgam : Complex.Gamma (s0 + ((|(((0 : ℤ) : ℝ))| / 2 : ℝ) : ℂ)) = Complex.Gamma s0 := by
      norm_num
    rw [hgam, hbase, ← hkeyπ, mul_assoc, mul_div_mul_left _ _ hXne]
  have hΓ0 : Complex.Gamma s0 ≠ 0 := by
    refine Complex.Gamma_ne_zero (fun m hm => ?_)
    have h1 : (-(m : ℂ)).re = -(m : ℝ) := by simp
    have h2 := congrArg Complex.re hm
    rw [hs0re, h1] at h2
    rcases Nat.eq_zero_or_pos m with hm0 | hm1
    · subst hm0
      norm_num at h2
    · have hm1' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      linarith
  have hnormLval : ‖Lval d 0 Lam s0‖ =
      Real.pi ^ (-(1 / 2 : ℝ)) * ‖mellin (thetaDualG d chi) s1‖ / ‖Complex.Gamma s0‖ := by
    rw [hLval, norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, hs0re]
  have hratio : ‖Complex.Gamma s1‖ / ‖Complex.Gamma s0‖ = 1 / 4 + t ^ 2 := by
    rw [← norm_div]
    have h1 : s1 = (3 / 2 : ℂ) - (t : ℂ) * Complex.I := by
      rw [hs1def]; push_cast; ring
    have h0' : s0 = (-1 / 2 : ℂ) + (t : ℂ) * Complex.I := by
      rw [hs0def]; push_cast; ring
    rw [h1, h0', gammaRatio_negHalf t]
  have hGeq : ‖Complex.Gamma s1‖ = (1 / 4 + t ^ 2) * ‖Complex.Gamma s0‖ := by
    have hG0 : ‖Complex.Gamma s0‖ ≠ 0 := ne_of_gt (norm_pos_iff.mpr hΓ0)
    rw [← hratio, div_mul_cancel₀ _ hG0]
  have h16pow : (16 * (d : ℝ) ^ 2) ^ ((3 : ℝ) / 2) = (4 * (d : ℝ)) ^ 3 := by
    have h4 : (0 : ℝ) ≤ 4 * (d : ℝ) := by positivity
    have he : 16 * (d : ℝ) ^ 2 = (4 * (d : ℝ)) ^ 2 := by ring
    have h3 : (3 : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
    have hhalf : ((4 * (d : ℝ)) ^ 2) ^ ((1 / 2 : ℝ)) = 4 * (d : ℝ) := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq h4]
    rw [he, show ((3 : ℝ) / 2) = ((1 / 2 : ℝ) * 3) by norm_num]
    rw [Real.rpow_mul (by positivity : (0 : ℝ) ≤ (4 * (d : ℝ)) ^ 2)]
    rw [hhalf]
    rw [h3, Real.rpow_natCast]
  have hgeom : (1 / 4) * (1 / (16 * (d : ℝ) ^ 2)) * ((16 * (d : ℝ) ^ 2) ^ ((3 : ℝ) / 2)) *
      ((4 * (d : ℝ)) ^ 2) = 16 * (d : ℝ) ^ 3 := by
    rw [h16pow]
    field_simp
    ring
  have harith : Real.pi ^ (-(1 / 2 : ℝ)) *
        ((1 / 4) * (1 / (16 * (d : ℝ) ^ 2)) * ((16 * (d : ℝ) ^ 2) ^ ((3 : ℝ) / 2)) *
          (‖Complex.Gamma s1‖ * Real.pi ^ (-(3 / 2 : ℝ)) * ((4 * (d : ℝ)) ^ 2 * Slat)))
      = (16 * (d : ℝ) ^ 3 * (1 / 4 + t ^ 2) * Slat / Real.pi ^ 2) * ‖Complex.Gamma s0‖ := by
    rw [hGeq]
    have hkey : Real.pi ^ (-(1 / 2 : ℝ)) *
          ((1 / 4) * (1 / (16 * (d : ℝ) ^ 2)) * ((16 * (d : ℝ) ^ 2) ^ ((3 : ℝ) / 2)) *
            ((1 / 4 + t ^ 2) * ‖Complex.Gamma s0‖ * Real.pi ^ (-(3 / 2 : ℝ)) *
              ((4 * (d : ℝ)) ^ 2 * Slat)))
        = (1 / 4 + t ^ 2) * ‖Complex.Gamma s0‖ * Slat *
            (Real.pi ^ (-(1 / 2 : ℝ)) * Real.pi ^ (-(3 / 2 : ℝ))) *
            ((1 / 4) * (1 / (16 * (d : ℝ) ^ 2)) * ((16 * (d : ℝ) ^ 2) ^ ((3 : ℝ) / 2)) *
              (4 * (d : ℝ)) ^ 2) := by ring
    rw [hkey, pi_rpow_neg_half_mul, hgeom]
    ring
  have hfinal : ‖Lval d 0 Lam s0‖ ≤ 16 * (d : ℝ) ^ 3 * (1 / 4 + t ^ 2) * Slat / Real.pi ^ 2 := by
    rw [hnormLval, div_le_iff₀ (norm_pos_iff.mpr hΓ0)]
    calc Real.pi ^ (-(1 / 2 : ℝ)) * ‖mellin (thetaDualG d chi) s1‖
        ≤ Real.pi ^ (-(1 / 2 : ℝ)) *
            ((1 / 4) * (1 / (16 * (d : ℝ) ^ 2)) * ((16 * (d : ℝ) ^ 2) ^ ((3 : ℝ) / 2)) *
              (‖Complex.Gamma s1‖ * Real.pi ^ (-(3 / 2 : ℝ)) * ((4 * (d : ℝ)) ^ 2 * Slat))) :=
          mul_le_mul_of_nonneg_left hmG (Real.rpow_nonneg Real.pi_pos.le _)
      _ = (16 * (d : ℝ) ^ 3 * (1 / 4 + t ^ 2) * Slat / Real.pi ^ 2) * ‖Complex.Gamma s0‖ :=
          harith
  have hstep : 16 * (d : ℝ) ^ 3 * (1 / 4 + t ^ 2) * Slat / Real.pi ^ 2
      ≤ (16 * Slat / Real.pi ^ 2 + 1) * (d : ℝ) ^ 3 * (1 + |t|) ^ 2 := by
    have ht2 : (1 / 4 + t ^ 2 : ℝ) ≤ (1 + |t|) ^ 2 := by
      have h1 : (1 + |t|) ^ 2 = 1 + 2 * |t| + |t| ^ 2 := by ring
      rw [h1, sq_abs]
      have := abs_nonneg t
      linarith
    have hd3 : (0 : ℝ) ≤ (d : ℝ) ^ 3 := by positivity
    have hsp : 0 ≤ 16 * Slat / Real.pi ^ 2 := div_nonneg (by linarith) (by positivity)
    calc 16 * (d : ℝ) ^ 3 * (1 / 4 + t ^ 2) * Slat / Real.pi ^ 2
        = (16 * Slat / Real.pi ^ 2) * ((d : ℝ) ^ 3 * (1 / 4 + t ^ 2)) := by ring
      _ ≤ (16 * Slat / Real.pi ^ 2) * ((d : ℝ) ^ 3 * (1 + |t|) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht2 hd3) hsp
      _ ≤ (16 * Slat / Real.pi ^ 2 + 1) * ((d : ℝ) ^ 3 * (1 + |t|) ^ 2) :=
          mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hd3 (by positivity))
      _ = (16 * Slat / Real.pi ^ 2 + 1) * (d : ℝ) ^ 3 * (1 + |t|) ^ 2 := by ring
  exact hfinal.trans hstep

end

end Work.FIArea6Hecke.R
