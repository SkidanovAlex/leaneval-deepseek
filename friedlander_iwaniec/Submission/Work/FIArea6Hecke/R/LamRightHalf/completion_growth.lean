/-
# `Submission.Work.FIArea6Hecke.R.LamRightHalf.completion_growth`

Growth of the completed Hecke `L`-function of `ℚ(i)` on the half-plane `re s ≥ 1/2`, for **every
strict character** `χ` mod `4d` (no primitivity) and every weight `m ≥ 0`, under the hypothesis
that `ψ_m(z) = χ(z)(z/|z|)^m` is non-trivial on the primary units mod `4d`.

The completion is constructed as the Mellin transform of the weight-`m` holomorphic theta series,

  `Λ_c(t) = (4d)^t·π^{m/2}·mellin (thetaHol χ' m) (t + m/2)`,   `χ' = twist χ m`,

which is entire because `thetaHol χ' m` and its Poisson dual `thetaDualMG d χ' m` form a weak
functional-equation pair (`thetaHol χ' m (1/x) = x^{m+1}·thetaDualMG d χ' m x`,
`R/LamRightHalf.thetaHol_one_div_dual`) with rapidly decaying kernels.  The two ingredients of the
growth bound are then

* `PL.MellinGrowth.lambda0_strip_bound`: the Mellin transform is **bounded** on every vertical
  strip `a ≤ re ≤ b` (uniformly in the imaginary part) — this gives the bound on
  `1/2 ≤ re t ≤ 2 + m/2`;
* the product formula `Λ_c(s) = heckeArch d m s·L(s,ψ)` on `re s > 1` together with the Stirling
  bound `Gamma_log_norm_le_vertical` and the boundedness `heckeLSeries_bound_re_ge_two` of the
  Dirichlet series on `re ≥ 2` — this gives the bound on `re t ≥ 2 + m/2`.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.LamRightHalf.Defs
import Submission.Work.FIArea6Hecke.R.LamRightHalf.thetaHol_one_div_dual
import Submission.Work.FIArea6Hecke.R.LamRightHalf.thetaDualM_continuous
import Submission.Work.FIArea6Hecke.R.LamRightHalf.thetaDualM_decay
import Submission.Work.FIArea6Hecke.R.LamRightHalf.estimates
import Submission.Work.FIArea6Hecke.R.exists_completion_strict
import Submission.Work.FIArea6Hecke.R.heckeLambda_eq_LambdaHecke
import Submission.Work.FIArea5.S16Hecke.twist_unitSum
import Submission.Work.FIArea5.S16Hecke.twistAux
import Submission.Work.FIArea5.S16Hecke.thetaHol_twist_eq
import Submission.Work.FIArea5.HeckeZFR.GammaLogBound
import Submission.Work.FIArea6Hecke.ZFRDefs
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_critical_poly

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea6Hecke.R

open scoped BigOperators
open MeasureTheory Set

attribute [local instance] Classical.propDecidable

noncomputable section

/-- Two entire functions agreeing on a right half-plane are equal. -/
lemma eq_of_agrees_right {G Lam : ℂ → ℂ} {T : ℝ}
    (hG : AnalyticOn ℂ G Set.univ) (hL : AnalyticOn ℂ Lam Set.univ)
    (h : ∀ s : ℂ, T < s.re → Lam s = G s) : Lam = G := by
  have hG' : AnalyticOnNhd ℂ G Set.univ := analyticOn_univ.mp hG
  have hL' : AnalyticOnNhd ℂ Lam Set.univ := analyticOn_univ.mp hL
  have hev : (fun s : ℂ => Lam s - G s) =ᶠ[nhds (((T + 1 : ℝ)) : ℂ)] 0 := by
    filter_upwards [Metric.ball_mem_nhds (((T + 1 : ℝ)) : ℂ) (by norm_num : (0 : ℝ) < 1)]
      with s hs
    have h1 : ‖s - (((T + 1 : ℝ)) : ℂ)‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hs
    have h2 : |s.re - (T + 1)| ≤ ‖s - (((T + 1 : ℝ)) : ℂ)‖ := by
      simpa using Complex.abs_re_le_norm (s - (((T + 1 : ℝ)) : ℂ))
    have h3 : T < s.re := by
      have h4 := lt_of_le_of_lt h2 h1
      rw [abs_lt] at h4
      linarith [h4.1]
    simp [h s h3]
  have hzero : (fun s : ℂ => Lam s - G s) = 0 :=
    AnalyticOnNhd.eq_of_eventuallyEq (hL'.sub hG') (fun z _ => analyticAt_const) hev
  funext s
  exact sub_eq_zero.mp (congrFun hzero s)

/-- `X = 4d/π`, as a complex number (the base of the archimedean exponential factor). -/
noncomputable def PX (d : ℕ) : ℂ := (((4 * (d : ℝ)) / Real.pi : ℝ) : ℂ)

/-- `heckeArch d m s = X^s·Γ(s + m/2)` for `m ≥ 0`, in the normalisation of `PX`. -/
lemma heckeArch_eq_PX (d : ℕ) (m : ℕ) (s : ℂ) :
    Work.FITop4.Bridge.heckeArch d (m : ℤ) s = PX d ^ s * Complex.Gamma (s + (m : ℂ) / 2) := by
  rw [Work.FITop4.Bridge.heckeArch]
  have h1 : ((|(((m : ℤ) : ℝ))| / 2 : ℝ) : ℂ) = (m : ℂ) / 2 := by
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((m : ℤ) : ℝ))]
    push_cast
    ring
  rw [h1]
  unfold PX
  push_cast
  ring_nf

/-- `(4d)^s π^{m/2} π^{-(s+m/2)} = X^s`, the exponential bookkeeping of the completion. -/
lemma fourd_eq_PX (d : ℕ) (hd : 1 ≤ d) (m : ℕ) (s : ℂ) :
    (((4 * d : ℕ) : ℂ)) ^ s * ((Real.pi : ℂ) ^ ((m : ℂ) / 2)) *
      (Real.pi : ℂ) ^ (-(s + (m : ℂ) / 2)) = PX d ^ s := by
  rw [Work.FIArea5.S16Hecke.fourd_pow_pi_pow d hd m s]
  unfold PX
  push_cast
  ring_nf

/-- The modulus of `X^z` is `(4d/π)^{re z}`. -/
lemma norm_PX_cpow (d : ℕ) (hd : 1 ≤ d) (z : ℂ) :
    ‖PX d ^ z‖ = (4 * (d : ℝ) / Real.pi) ^ z.re := by
  unfold PX
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by
    have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have h2 : (1 : ℝ) ≤ 4 * (d : ℝ) := by linarith
    have h3 : (1 : ℝ) ≤ 4 * (d : ℝ) / Real.pi := by
      rw [le_div_iff₀ Real.pi_pos]
      nlinarith [Real.pi_lt_four]
    linarith)]

/-- `X ≠ 0` for `d ≥ 1`. -/
lemma PX_ne_zero (d : ℕ) (hd : 1 ≤ d) : PX d ≠ 0 := by
  unfold PX
  exact Complex.ofReal_ne_zero.mpr (by
    have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have h2 : (1 : ℝ) ≤ 4 * (d : ℝ) := by linarith
    have h3 : (1 : ℝ) ≤ 4 * (d : ℝ) / Real.pi := by
      rw [le_div_iff₀ Real.pi_pos]
      nlinarith [Real.pi_lt_four]
    linarith)

/-- For `m = 0`, non-triviality of `ψ_m = χ` on the primary units supplies the vanishing of the
first Fourier coefficient of the twisted character, which is what the exponential decay of the
Poisson dual kernel needs. -/
private lemma gaussSum_zero_of_psi_ne {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ} (m : ℕ)
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hne : ∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧
      Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧ Work.FIArea5.S16Hecke.psi chi (m : ℤ) z ≠ 1) :
    m = 0 → Work.FIArea5.S16Hecke.gaussSum d (Work.FIArea5.S16Hecke.twist chi m) 0 = 0 := by
  intro hm0
  subst hm0
  obtain ⟨z, hz1, hz2, hz3⟩ := hne
  have hzchi : chi z ≠ 1 := by
    have h1 : Work.FIArea5.S16Hecke.psi chi (0 : ℤ) z = chi z := by
      simp [Work.FIArea5.S16Hecke.psi]
    simp only [Nat.cast_zero] at hz3
    rwa [h1] at hz3
  have hchi' : Work.FIArea5.S16Hecke.IsCharMod4dStrict d
      (Work.FIArea5.S16Hecke.twist chi 0) :=
    Work.FIArea5.S16Hecke.twist_isCharMod4dStrict d hd chi 0 hchi
  refine gaussSum_zero_of_nontrivial hd hchi' ⟨z, hz1, hz2, ?_⟩
  rw [Work.FIArea5.S16Hecke.twist_eq_of_isPrimary chi 0 hz1]
  exact hzchi

/-- **The completed Hecke `L`-function of a strict character, weight `m ≥ 0`.**  There is an
entire `Λc` agreeing with `heckeArch d m s·heckeLSeries χ m s` for `re s > 1` and bounded on the
strip `1/2 + m/2 ≤ re ≤ 3 + m/2` (uniformly in the imaginary part). -/
theorem completion_entire_nat (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (m : ℕ)
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hne : ∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧ Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧
      Work.FIArea5.S16Hecke.psi chi (m : ℤ) z ≠ 1) :
    ∃ Λc : ℂ → ℂ, AnalyticOn ℂ Λc Set.univ ∧
      (∀ s : ℂ, 1 < s.re →
        Λc s = Work.FITop4.Bridge.heckeArch d (m : ℤ) s *
          Work.FIArea5.S16Hecke.heckeLSeries chi (m : ℤ) s) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 3 → ‖Λc z‖ ≤ C := by
  have hchi' : Work.FIArea5.S16Hecke.IsCharMod4dStrict d (Work.FIArea5.S16Hecke.twist chi m) :=
    Work.FIArea5.S16Hecke.twist_isCharMod4dStrict d hd chi m hchi
  have hb' : ∀ z : GaussianInt, ‖Work.FIArea5.S16Hecke.twist chi m z‖ ≤ 1 := hchi'.1.2.2.1
  have hU' : Work.FIArea5.S16Hecke.unitSum (Work.FIArea5.S16Hecke.twist chi m) m ≠ 0 := by
    rw [Work.FIArea5.S16Hecke.twist_unitSum d hd chi m hchi.1]
    norm_num
  have hL : Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea5.S16Hecke.twist chi m) (m : ℤ)
      = Work.FIArea5.S16Hecke.heckeLSeries chi (m : ℤ) :=
    Work.FIArea6Hecke.heckeLSeries_twist chi m
  have h0' := gaussSum_zero_of_psi_ne hd m hchi hne
  -- integrability of the two kernels of the weak functional equation pair
  have hf_int : LocallyIntegrableOn (fun u : ℝ => Work.FIArea5.S16Hecke.thetaHol
      (Work.FIArea5.S16Hecke.twist chi m) m u) (Set.Ioi 0) :=
    (continuousOn_thetaHol_Ioi (m := m) hb').locallyIntegrableOn measurableSet_Ioi
  have hg_cont : ContinuousOn (thetaDualMG d (Work.FIArea5.S16Hecke.twist chi m) m)
      (Set.Ioi 0) := by
    refine ((thetaDualM_continuous d hb' m).comp
      (continuous_id.div_const _).continuousOn ?_).const_mul _
    intro x hx
    simp only [Set.mem_Ioi] at hx ⊢
    positivity
  have hg_int : LocallyIntegrableOn (thetaDualMG d (Work.FIArea5.S16Hecke.twist chi m) m)
      (Set.Ioi 0) := hg_cont.locallyIntegrableOn measurableSet_Ioi
  -- exponential decay of the two kernels
  obtain ⟨Cf, hCf0, hdecf⟩ := Work.FIArea5.S16Hecke.thetaHol_exp_decay d hd
    (Work.FIArea5.S16Hecke.twist chi m) m hb'
  have hf_dec : ∃ C u₀ : ℝ, 0 < u₀ ∧ ∀ u : ℝ, u₀ ≤ u →
      ‖Work.FIArea5.S16Hecke.thetaHol (Work.FIArea5.S16Hecke.twist chi m) m u‖
        ≤ C * Real.exp (-Real.pi * u) := by
    refine ⟨Cf * Real.exp (Real.pi * Work.FIArea5.S16Hecke.thetaC d),
      Work.FIArea5.S16Hecke.thetaC d, Work.FIArea5.S16Hecke.thetaC_pos hd, fun u hu => ?_⟩
    refine (hdecf u hu).trans_eq ?_
    rw [show -Real.pi * (u - Work.FIArea5.S16Hecke.thetaC d)
        = -Real.pi * u + Real.pi * Work.FIArea5.S16Hecke.thetaC d by ring, Real.exp_add]
    ring
  obtain ⟨Cg, hdecg⟩ := thetaDualM_decay d hd hb' m h0'
  have hg_dec : ∃ C u₀ : ℝ, 0 < u₀ ∧ ∀ u : ℝ, u₀ ≤ u →
      ‖thetaDualMG d (Work.FIArea5.S16Hecke.twist chi m) m u‖
        ≤ C * Real.exp (-(Real.pi / (16 * (d : ℝ) ^ 2)) * u) := by
    refine ⟨‖dualConst d (Work.FIArea5.S16Hecke.twist chi m) m‖ * Cg,
      16 * (d : ℝ) ^ 2, by positivity, fun u hu => ?_⟩
    have harg : (1 : ℝ) ≤ u / (16 * (d : ℝ) ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    rw [thetaDualMG, norm_mul]
    calc ‖dualConst d (Work.FIArea5.S16Hecke.twist chi m) m‖ *
            ‖thetaDualM d (Work.FIArea5.S16Hecke.twist chi m) m (u / (16 * (d : ℝ) ^ 2))‖
        ≤ ‖dualConst d (Work.FIArea5.S16Hecke.twist chi m) m‖ *
            (Cg * Real.exp (-Real.pi * (u / (16 * (d : ℝ) ^ 2)))) :=
          mul_le_mul_of_nonneg_left (hdecg _ harg) (norm_nonneg _)
      _ = (‖dualConst d (Work.FIArea5.S16Hecke.twist chi m) m‖ * Cg) *
            Real.exp (-(Real.pi / (16 * (d : ℝ) ^ 2)) * u) := by
          rw [show -Real.pi * (u / (16 * (d : ℝ) ^ 2))
              = -(Real.pi / (16 * (d : ℝ) ^ 2)) * u by ring]
          ring
  -- the weak functional equation pair
  let P : WeakFEPair ℂ :=
    { f := fun u : ℝ => Work.FIArea5.S16Hecke.thetaHol (Work.FIArea5.S16Hecke.twist chi m) m u
      g := thetaDualMG d (Work.FIArea5.S16Hecke.twist chi m) m
      k := ((m + 1 : ℕ) : ℝ)
      ε := 1
      f₀ := 0
      g₀ := 0
      hf_int := hf_int
      hg_int := hg_int
      hk := by positivity
      hε := one_ne_zero
      h_feq := fun x hx => thetaHol_one_div_dual d hd hchi' m hU' hx
      hf_top := fun r => by
        simpa only [sub_zero] using isBigO_rpow_of_exp_decay Real.pi_pos hf_dec r
      hg_top := fun r => by
        simpa only [sub_zero] using isBigO_rpow_of_exp_decay (by positivity) hg_dec r }
  have hstrong : IsStrongFEPair P := ⟨rfl, rfl⟩
  have hΛ : P.Λ = mellin (fun u : ℝ =>
      Work.FIArea5.S16Hecke.thetaHol (Work.FIArea5.S16Hecke.twist chi m) m u) :=
    IsStrongFEPair.Λ_eq hstrong
  have hΛ₀eq : P.Λ = P.Λ₀ := by
    funext s
    simp only [WeakFEPair.Λ]
    rw [show P.f₀ = (0 : ℂ) from rfl, show P.g₀ = (0 : ℂ) from rfl]
    simp
  obtain ⟨C₀, hC₀0, hC₀bd⟩ :=
    PL.MellinGrowth.lambda0_strip_bound P (a := 1 / 2 + (m : ℝ) / 2) (b := 3 + (m : ℝ) / 2)
  have hstrip : ∀ z : ℂ, 1 / 2 + (m : ℝ) / 2 ≤ z.re → z.re ≤ 3 + (m : ℝ) / 2 →
      ‖P.Λ z‖ ≤ C₀ := by
    intro z hz1 hz2
    rw [hΛ₀eq]
    exact hC₀bd z hz1 hz2
  have hhalf : ((m : ℂ) / 2) = (((m : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  have hmre : ∀ t : ℂ, (t + (m : ℂ) / 2).re = t.re + (m : ℝ) / 2 := by
    intro t
    rw [Complex.add_re, hhalf, Complex.ofReal_re]
  have hre2 : ((m : ℂ) / 2).re = (m : ℝ) / 2 := by rw [hhalf, Complex.ofReal_re]
  refine ⟨fun t : ℂ => (((4 * d : ℕ) : ℂ)) ^ t *
    (((Real.pi : ℂ) ^ ((m : ℂ) / 2)) * P.Λ (t + (m : ℂ) / 2)), ?_, ?_, ?_⟩
  · -- entire
    refine DifferentiableOn.analyticOn ?_ isOpen_univ
    intro t _
    have h4d : (((4 * d : ℕ) : ℂ)) ≠ 0 := by
      rw [← Complex.ofReal_natCast]
      exact Complex.ofReal_ne_zero.mpr (by positivity)
    have h1 : DifferentiableAt ℂ (fun t : ℂ => (((4 * d : ℕ) : ℂ)) ^ t) t :=
      differentiableAt_id.const_cpow (Or.inl h4d)
    have h3 : DifferentiableAt ℂ (fun t : ℂ => ((Real.pi : ℂ) ^ ((m : ℂ) / 2)) *
        P.Λ (t + (m : ℂ) / 2)) t :=
      (differentiableAt_const _).mul ((hstrong.differentiable_Λ.differentiableAt).comp t
        (differentiableAt_id.add_const _))
    exact (h1.mul h3).differentiableWithinAt
  · -- agreement with the product for `re s > 1`
    intro s hs
    have hs' : 1 + (m : ℝ) / 2 < (s + (m : ℂ) / 2).re := by
      rw [hmre s]
      linarith
    have hmellin := mellin_thetaHol_eq (Work.FIArea5.S16Hecke.twist chi m) m hb' hs'
    have hsub : s + (m : ℂ) / 2 - (m : ℂ) / 2 = s := by ring
    calc (((4 * d : ℕ) : ℂ)) ^ s * (((Real.pi : ℂ) ^ ((m : ℂ) / 2)) * P.Λ (s + (m : ℂ) / 2))
        = (((4 * d : ℕ) : ℂ)) ^ s * (((Real.pi : ℂ) ^ ((m : ℂ) / 2)) *
            mellin (fun u : ℝ => Work.FIArea5.S16Hecke.thetaHol
              (Work.FIArea5.S16Hecke.twist chi m) m u) (s + (m : ℂ) / 2)) := by rw [hΛ]
      _ = (((4 * d : ℕ) : ℂ)) ^ s * (((Real.pi : ℂ) ^ ((m : ℂ) / 2)) *
            (Complex.Gamma (s + (m : ℂ) / 2) *
              (Real.pi : ℂ) ^ (-(s + (m : ℂ) / 2)) *
              Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea5.S16Hecke.twist chi m) (m : ℤ)
                (s + (m : ℂ) / 2 - (m : ℂ) / 2))) := by rw [hmellin]
      _ = (((4 * d : ℕ) : ℂ)) ^ s * (((Real.pi : ℂ) ^ ((m : ℂ) / 2)) *
            (Complex.Gamma (s + (m : ℂ) / 2) * (Real.pi : ℂ) ^ (-(s + (m : ℂ) / 2)) *
              Work.FIArea5.S16Hecke.heckeLSeries chi (m : ℤ) s)) := by rw [hsub, hL]
      _ = Work.FITop4.Bridge.heckeArch d (m : ℤ) s *
            Work.FIArea5.S16Hecke.heckeLSeries chi (m : ℤ) s := by
          rw [heckeArch_eq_PX d m s]
          rw [← fourd_eq_PX d hd m s]
          ring
  · -- strip bound
    refine ⟨((4 * (d : ℝ)) ^ (3 + (m : ℝ) / 2)) * (Real.pi ^ ((m : ℝ) / 2)) * C₀,
      by positivity, fun z hz1 hz2 => ?_⟩
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have h4dpos : (0 : ℝ) < 4 * (d : ℝ) := by linarith
    have h4d1 : (1 : ℝ) ≤ 4 * (d : ℝ) := by linarith
    have hm0 : (0 : ℝ) ≤ (m : ℝ) / 2 := by positivity
    have hz : 1 / 2 + (m : ℝ) / 2 ≤ (z + (m : ℂ) / 2).re := by
      rw [hmre z]
      linarith
    have hz' : (z + (m : ℂ) / 2).re ≤ 3 + (m : ℝ) / 2 := by
      rw [hmre z]
      linarith
    have hzre : z.re ≤ 3 := hz2
    calc ‖(((4 * d : ℕ) : ℂ)) ^ z * (((Real.pi : ℂ) ^ ((m : ℂ) / 2)) * P.Λ (z + (m : ℂ) / 2))‖
        = ‖(((4 * d : ℕ) : ℂ)) ^ z‖ *
            ‖((Real.pi : ℂ) ^ ((m : ℂ) / 2)) * P.Λ (z + (m : ℂ) / 2)‖ := by rw [norm_mul]
      _ = ‖(((4 * d : ℕ) : ℂ)) ^ z‖ * (‖((Real.pi : ℂ) ^ ((m : ℂ) / 2))‖ *
            ‖P.Λ (z + (m : ℂ) / 2)‖) := by rw [norm_mul]
      _ ≤ ((4 * (d : ℝ)) ^ (3 + (m : ℝ) / 2)) * (Real.pi ^ ((m : ℝ) / 2)) * C₀ := by
          have h1 : ‖(((4 * d : ℕ) : ℂ)) ^ z‖ ≤ (4 * (d : ℝ)) ^ (3 + (m : ℝ) / 2) := by
            rw [show (((4 * d : ℕ) : ℂ)) = (((4 * (d : ℝ)) : ℝ) : ℂ) by push_cast; ring]
            rw [Complex.norm_cpow_eq_rpow_re_of_pos h4dpos]
            have hzre' : z.re ≤ 3 + (m : ℝ) / 2 := by linarith
            exact Real.rpow_le_rpow_of_exponent_le h4d1 hzre'
          have h2 : ‖((Real.pi : ℂ) ^ ((m : ℂ) / 2))‖ = Real.pi ^ ((m : ℝ) / 2) := by
            rw [hhalf, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, Complex.ofReal_re]
          have h3 : ‖P.Λ (z + (m : ℂ) / 2)‖ ≤ C₀ := hstrip _ hz hz'
          rw [h2]
          have hπ0 : (0 : ℝ) ≤ Real.pi ^ ((m : ℝ) / 2) := Real.rpow_nonneg Real.pi_pos.le _
          have hC00 : (0 : ℝ) ≤ C₀ := hC₀0
          have h4d0 : (0 : ℝ) ≤ (4 * (d : ℝ)) ^ (3 + (m : ℝ) / 2) :=
            Real.rpow_nonneg (by linarith) _
          calc ‖(((4 * d : ℕ) : ℂ)) ^ z‖ * (Real.pi ^ ((m : ℝ) / 2) * ‖P.Λ (z + (m : ℂ) / 2)‖)
              ≤ (4 * (d : ℝ)) ^ (3 + (m : ℝ) / 2) *
                  (Real.pi ^ ((m : ℝ) / 2) * C₀) :=
                mul_le_mul h1 (mul_le_mul le_rfl h3 (norm_nonneg _) hπ0) (by positivity) h4d0
            _ = ((4 * (d : ℝ)) ^ (3 + (m : ℝ) / 2)) * (Real.pi ^ ((m : ℝ) / 2)) * C₀ := by ring

/-- **Growth of the completion on the right half-plane** (weight `m ≥ 0`). -/
theorem completion_growth_nat (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (m : ℕ)
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hne : ∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧ Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧
      Work.FIArea5.S16Hecke.psi chi (m : ℤ) z ≠ 1) :
    ∃ c K : ℝ, 0 < c ∧ 0 ≤ K ∧
      ∀ Lam : ℂ → ℂ, AnalyticOn ℂ Lam Set.univ →
      (∀ s : ℂ, 1 + (m : ℝ) / 2 < s.re →
        Lam s = Work.FITop4.Bridge.heckeArch d (m : ℤ) s *
          Work.FIArea5.S16Hecke.heckeLSeries chi (m : ℤ) s) →
      ∀ w : ℂ, (1 / 2 : ℝ) ≤ w.re →
        Real.log ‖Lam w‖ ≤ c * (‖w‖ + 3) * (Real.log (‖w‖ + 5) + K) := by
  obtain ⟨Λc, hAn, hagr, C, hC0, hCbd⟩ := completion_entire_nat d hd chi m hchi hne
  obtain ⟨A₀, hA₀0, hA₀bd⟩ := heckeLSeries_bound_re_ge_two
    (chi := Work.FIArea5.S16Hecke.twist chi m)
    (Work.FIArea5.S16Hecke.twist_isCharMod4dStrict d hd chi m hchi).1.2.2.1 m
  set A : ℝ := max A₀ 1 with hAdef
  have hA1 : (1 : ℝ) ≤ A := le_max_right _ _
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le one_pos hA1
  have hlogA : (0 : ℝ) ≤ Real.log A := Real.log_nonneg hA1
  have hAbd : ∀ s : ℂ, 2 ≤ s.re →
      ‖Work.FIArea5.S16Hecke.heckeLSeries chi (m : ℤ) s‖ ≤ A := by
    intro s hs
    rw [← Work.FIArea6Hecke.heckeLSeries_twist chi m]
    refine (hA₀bd s hs).trans ?_
    rw [hAdef]
    exact le_max_left _ _
  obtain ⟨CΓ, hCΓpos, hCΓ⟩ := Work.FIArea5.S16Hecke.Gamma_log_norm_le_vertical
  have hX : (0 : ℝ) ≤ Real.log (4 * (d : ℝ)) :=
    Real.log_nonneg (by
      have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      linarith)
  have hμ : (0 : ℝ) ≤ (m : ℝ) / 2 := by positivity
  have hhalf : ((m : ℂ) / 2) = (((m : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  have hmre : ∀ t : ℂ, (t + (m : ℂ) / 2).re = t.re + (m : ℝ) / 2 := by
    intro t
    rw [Complex.add_re, hhalf, Complex.ofReal_re]
  -- the bound in the right-hand region `re z ≥ 2 + m/2`
  have hright : ∀ z : ℂ, 3 ≤ z.re →
      Real.log ‖Λc z‖ ≤ ‖z‖ * Real.log (4 * (d : ℝ)) +
        (CΓ * (1 + (‖z‖ + (m : ℝ) / 2 + 1) * (1 + Real.log (2 + ‖z‖ + (m : ℝ) / 2)))
          + Real.log A) := by
    intro z hz
    have hz1 : 1 < z.re := by linarith
    have hArch : Work.FITop4.Bridge.heckeArch d (m : ℤ) z ≠ 0 :=
      Work.FIArea6Hecke.heckeArch_ne_zero_of_pos_re hd (m : ℤ) (by linarith)
    rw [hagr z hz1]
    by_cases hL : Work.FIArea5.S16Hecke.heckeLSeries chi (m : ℤ) z = 0
    · rw [hL, mul_zero, norm_zero, Real.log_zero]
      have h1 : (0 : ℝ) ≤ ‖z‖ * Real.log (4 * (d : ℝ)) :=
        mul_nonneg (norm_nonneg _) hX
      have h2 : (0 : ℝ) ≤ CΓ * (1 + (‖z‖ + (m : ℝ) / 2 + 1) *
          (1 + Real.log (2 + ‖z‖ + (m : ℝ) / 2))) := by
        refine mul_nonneg hCΓpos.le ?_
        have h3 : (0 : ℝ) ≤ ‖z‖ + (m : ℝ) / 2 + 1 := by positivity
        have h4 : (0 : ℝ) ≤ 1 + Real.log (2 + ‖z‖ + (m : ℝ) / 2) := by
          have := Real.log_nonneg (by linarith [norm_nonneg z,
            (by positivity : (0 : ℝ) ≤ (m : ℝ) / 2)] : (1 : ℝ) ≤ 2 + ‖z‖ + (m : ℝ) / 2)
          linarith
        positivity
      linarith
    · have hlogmul : Real.log ‖Work.FITop4.Bridge.heckeArch d (m : ℤ) z *
          Work.FIArea5.S16Hecke.heckeLSeries chi (m : ℤ) z‖
          = Real.log ‖Work.FITop4.Bridge.heckeArch d (m : ℤ) z‖ +
            Real.log ‖Work.FIArea5.S16Hecke.heckeLSeries chi (m : ℤ) z‖ := by
        rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hArch) (norm_ne_zero_iff.mpr hL)]
      rw [hlogmul]
      -- the archimedean factor
      have harchBound : Real.log ‖Work.FITop4.Bridge.heckeArch d (m : ℤ) z‖
          ≤ ‖z‖ * Real.log (4 * (d : ℝ)) + CΓ * (1 + (‖z‖ + (m : ℝ) / 2 + 1) *
              (1 + Real.log (2 + ‖z‖ + (m : ℝ) / 2))) := by
        have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
        have hPX_ne : PX d ^ z ≠ 0 := by
          rw [Complex.cpow_def_of_ne_zero (PX_ne_zero d hd)]
          exact Complex.exp_ne_zero _
        have hgam_ne : Complex.Gamma (z + (m : ℂ) / 2) ≠ 0 := by
          apply Complex.Gamma_ne_zero_of_re_pos
          rw [hmre z]
          linarith
        have hsplit : Real.log ‖Work.FITop4.Bridge.heckeArch d (m : ℤ) z‖
            = Real.log ‖PX d ^ z‖ + Real.log ‖Complex.Gamma (z + (m : ℂ) / 2)‖ := by
          rw [heckeArch_eq_PX d m z, norm_mul,
            Real.log_mul (norm_ne_zero_iff.mpr hPX_ne) (norm_ne_zero_iff.mpr hgam_ne)]
        rw [hsplit]
        have hExp : Real.log ‖PX d ^ z‖ = z.re * Real.log (4 * (d : ℝ) / Real.pi) := by
          rw [norm_PX_cpow d hd z, Real.log_rpow (by
            have h1 : (1 : ℝ) ≤ 4 * (d : ℝ) := by linarith
            have h2 : (1 : ℝ) ≤ 4 * (d : ℝ) / Real.pi := by
              rw [le_div_iff₀ Real.pi_pos]
              nlinarith [Real.pi_lt_four]
            linarith)]
        have hGamma := hCΓ (z + (m : ℂ) / 2) (by rw [hmre z]; linarith)
        have hGamma' : Real.log ‖Complex.Gamma (z + (m : ℂ) / 2)‖
            ≤ CΓ * (1 + (‖z‖ + (m : ℝ) / 2 + 1) *
              (1 + Real.log (2 + ‖z‖ + (m : ℝ) / 2))) := by
          refine (hGamma.trans ?_)
          refine mul_le_mul_of_nonneg_left ?_ hCΓpos.le
          have h5 : (z + (m : ℂ) / 2).re + 1 ≤ ‖z‖ + (m : ℝ) / 2 + 1 := by
            rw [hmre z]
            linarith [Complex.re_le_norm z]
          have hnormm : ‖((m : ℂ) / 2)‖ = (m : ℝ) / 2 := by
            rw [norm_div, Complex.norm_natCast]
            norm_num
          have h6a : 2 + ‖z + (m : ℂ) / 2‖ ≤ 2 + ‖z‖ + (m : ℝ) / 2 := by
            have := norm_add_le z ((m : ℂ) / 2)
            linarith
          have h6 : 1 + Real.log (2 + ‖z + (m : ℂ) / 2‖)
              ≤ 1 + Real.log (2 + ‖z‖ + (m : ℝ) / 2) := by
            have h6' := Real.log_le_log (by positivity : (0 : ℝ) < 2 + ‖z + (m : ℂ) / 2‖) h6a
            linarith
          have h60 : (0 : ℝ) ≤ 1 + Real.log (2 + ‖z + (m : ℂ) / 2‖) := by
            have := Real.log_nonneg (by linarith [norm_nonneg (z + (m : ℂ) / 2)] :
              (1 : ℝ) ≤ 2 + ‖z + (m : ℂ) / 2‖)
            linarith
          have hA' : (0 : ℝ) ≤ ‖z‖ + (m : ℝ) / 2 + 1 := by
            linarith [norm_nonneg z, (by positivity : (0 : ℝ) ≤ (m : ℝ) / 2)]
          nlinarith [h5, h6, h60, hA']
        have hlogbase : Real.log (4 * (d : ℝ) / Real.pi) ≤ Real.log (4 * (d : ℝ)) := by
          refine Real.log_le_log (by positivity) ?_
          rw [div_le_iff₀ Real.pi_pos]
          nlinarith [Real.pi_gt_three, Real.pi_pos]
        have hzre' : (0 : ℝ) ≤ z.re := by linarith
        have hstep1 : z.re * Real.log (4 * (d : ℝ) / Real.pi)
            ≤ ‖z‖ * Real.log (4 * (d : ℝ)) := by
          calc z.re * Real.log (4 * (d : ℝ) / Real.pi)
              ≤ z.re * Real.log (4 * (d : ℝ)) := mul_le_mul_of_nonneg_left hlogbase hzre'
            _ ≤ ‖z‖ * Real.log (4 * (d : ℝ)) :=
                mul_le_mul_of_nonneg_right (Complex.re_le_norm z) hX
        linarith [hExp, hGamma', hstep1]
      -- the `L`-factor
      have hLbound : Real.log ‖Work.FIArea5.S16Hecke.heckeLSeries chi (m : ℤ) z‖ ≤ Real.log A :=
        Real.log_le_log (norm_pos_iff.mpr hL) (hAbd z (by linarith))
      linarith [harchBound, hLbound]
  -- constants
  set c : ℝ := ((Real.log (4 * (d : ℝ)) + 1) + CΓ + CΓ * ((m : ℝ) / 2 + 1) *
      (2 + Real.log ((m : ℝ) / 2 + 1)) + Real.log A + 1) + |Real.log C| + 1 with hc
  have hlogμc : (0 : ℝ) ≤ Real.log ((m : ℝ) / 2 + 1) := Real.log_nonneg (by linarith)
  have hprodc : (0 : ℝ) ≤ CΓ * ((m : ℝ) / 2 + 1) * (2 + Real.log ((m : ℝ) / 2 + 1)) := by
    have h2 : (0 : ℝ) ≤ 2 + Real.log ((m : ℝ) / 2 + 1) := by linarith
    positivity
  have hcpos : 0 < c := by
    rw [hc]
    linarith [abs_nonneg (Real.log C), hlogA]
  refine ⟨c, 1, hcpos, by norm_num, ?_⟩
  intro Lam hLam hLamagr w hw
  have heq : Lam = Λc := by
    refine eq_of_agrees_right (T := 1 + (m : ℝ) / 2) hAn hLam ?_
    intro s hs
    rw [hLamagr s hs, hagr s (by linarith)]
  rw [heq]
  have hm0 : (0 : ℝ) ≤ (m : ℝ) / 2 := by positivity
  by_cases hstrip : w.re ≤ 3
  · -- strip regime: `Λc` is bounded there
    have hCbound := hCbd w hw hstrip
    have hlogC : Real.log ‖Λc w‖ ≤ |Real.log C| := by
      by_cases hCw : ‖Λc w‖ = 0
      · rw [hCw, Real.log_zero]
        exact abs_nonneg _
      · refine le_trans (Real.log_le_log (norm_pos_iff.mpr (norm_ne_zero_iff.mp hCw)) hCbound)
          (le_abs_self _)
    have h1 : |Real.log C| ≤ c := by
      rw [hc]; linarith [hlogA, hprodc]
    calc Real.log ‖Λc w‖ ≤ |Real.log C| := hlogC
      _ = |Real.log C| * 1 := by ring
      _ ≤ |Real.log C| * ((‖w‖ + 3) * (Real.log (‖w‖ + 5) + 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          have := Real.log_nonneg (by linarith [norm_nonneg w] : (1 : ℝ) ≤ ‖w‖ + 5)
          nlinarith [norm_nonneg w]
      _ ≤ c * ((‖w‖ + 3) * (Real.log (‖w‖ + 5) + 1)) :=
          mul_le_mul_of_nonneg_right h1 (by
            have hl : (0 : ℝ) ≤ Real.log (‖w‖ + 5) :=
              Real.log_nonneg (by linarith [norm_nonneg w])
            nlinarith [norm_nonneg w, hl])
      _ = c * (‖w‖ + 3) * (Real.log (‖w‖ + 5) + 1) := by ring
  · -- right regime
    push_neg at hstrip
    have h1 := hright w (le_of_lt hstrip)
    have h2 := logGrowthArith (Real.log (4 * (d : ℝ))) CΓ A ((m : ℝ) / 2) ‖w‖ hX hCΓpos hm0
      (norm_nonneg w)
    have h3 : ((Real.log (4 * (d : ℝ)) + 1) + CΓ + CΓ * ((m : ℝ) / 2 + 1) *
        (2 + Real.log ((m : ℝ) / 2 + 1)) + |Real.log A| + 1) * (‖w‖ + 3) *
        (Real.log (‖w‖ + 5) + 1) ≤ c * (‖w‖ + 3) * (Real.log (‖w‖ + 5) + 1) := by
      have h4 : ((Real.log (4 * (d : ℝ)) + 1) + CΓ + CΓ * ((m : ℝ) / 2 + 1) *
          (2 + Real.log ((m : ℝ) / 2 + 1)) + |Real.log A| + 1) ≤ c := by
        rw [hc, abs_of_nonneg hlogA]
        linarith [abs_nonneg (Real.log C), hprodc]
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h4 ?_)
        (by
          have hl : (0 : ℝ) ≤ Real.log (‖w‖ + 5) :=
            Real.log_nonneg (by linarith [norm_nonneg w])
          nlinarith [norm_nonneg w, hl])
      have hl : (0 : ℝ) ≤ Real.log (‖w‖ + 5) :=
        Real.log_nonneg (by linarith [norm_nonneg w])
      nlinarith [norm_nonneg w, hl]
    have h2' : ‖w‖ * Real.log (4 * (d : ℝ)) +
        (CΓ * (1 + (‖w‖ + (m : ℝ) / 2 + 1) * (1 + Real.log (2 + ‖w‖ + (m : ℝ) / 2)))
          + Real.log A)
        ≤ c * (‖w‖ + 3) * (Real.log (‖w‖ + 5) + 1) := le_trans h2 h3
    linarith [h1, h2']

end

end Work.FIArea6Hecke.R
