import Mathlib
import Submission.Work.FIArea6Hecke.R.ZFRStatementDefs
import Submission.Work.FIArea6Hecke.ZFRDefs
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea5.S16Hecke.heckeLStripAux
import Submission.Work.FIArea5.S16Hecke.h1166TwistDefs
import Submission.Work.FIArea5.S16Hecke.twist_unitSum
import Submission.Work.FIArea5.S16Hecke.twistAux
import Submission.Work.FIArea5.S16Hecke.thetaHol_twist_eq
import Submission.Work.FIArea6Hecke.S16HeckeCompletionPrimitive
import Submission.Work.FIArea6Hecke.R.gaussSum_zero_of_nontrivial
import Submission.Work.FIArea6Hecke.R.LvalStripNegHalfAux
import Submission.Work.FIArea6Hecke.R.heckeLval_strip_growth
import Submission.Work.FIArea6Hecke.R.strip_bound_of_two_lines_uniform
import Submission.Work.FIArea6Hecke.R.noCompletion_principalStrict
import Submission.Work.FIArea5.HeckeZFR.LSeriesBound

set_option autoImplicit false

open scoped BigOperators

namespace Work.FIArea6Hecke.R

noncomputable section

attribute [local instance] Classical.propDecidable

/-- `heckeArch d 0 s ≠ 0` for `0 < re s`. -/
private lemma heckeArch_ne_zero_pos {d : ℕ} (hd : 1 ≤ d) {s : ℂ} (hs : 0 < s.re) :
    Work.FITop4.Bridge.heckeArch d 0 s ≠ 0 := by
  rw [Work.FITop4.Bridge.heckeArch]
  simp only [Int.cast_zero, abs_zero, zero_div, Complex.ofReal_zero, add_zero]
  refine mul_ne_zero ?_ (Complex.Gamma_ne_zero_of_re_pos hs)
  rw [Complex.cpow_ne_zero_iff]
  refine Or.inl ?_
  rw [show (4 * ((d:ℝ):ℂ) / (Real.pi:ℂ)) = (((4 * (d:ℝ)) / Real.pi : ℝ) : ℂ) by
        push_cast; ring]
  exact Complex.ofReal_ne_zero.mpr (by
    have h1 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
    positivity)

/-- **The convexity strip bound (*FI* (16.18)) with an absolute constant, uniform in the
modulus.**  The point of this lemma (as opposed to the per-modulus shape of
`Work.FIArea6Hecke.R.heckeLval_strip_bound`) is that the SAME constant `C` works for every
modulus `d`, every strict real `χ` and every completion `Lam`: the Siegel argument of *FI* Lemma
16.1 needs a uniform-in-`d` constant in order to produce a single `c(ε)`.

The proof route is the one of `R/heckeLval_strip_bound` (the mean of `χ` over the primary
fundamental domain; if it vanishes the disc sums have a power saving `O(d^10 X^θ)` with `θ < 1/2`
-- see `R/heckeDiscSum_bound_mean0` and `R/heckeStripBound_of_discSum` -- and the strip bound
follows by Phragmén–Lindelöf; if it does not vanish, no entire completion exists and the statement
is vacuous, see `R/heckeDiscSum_growth_mean` and `R/heckeNoCompletion_of_growth`).  **The
constants must be tracked**: the inputs (`discDiscrepancy_saving`, the Phragmén–Lindelöf step, the
Gauss-circle estimate) all carry absolute constants, so a uniform statement is available; if a
step of the existing chain is only stated with a per-modulus `∃C`, re-prove that step here with the
constant explicit rather than invoking the weaker statement. -/
theorem heckeLval_strip_bound_uniform_clean :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ),
        Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
        (∀ z : GaussianInt, chi z = star (chi z)) →
        (∀ z : GaussianInt, ‖chi z‖ ≤ 1) →
        ∀ (Lam : ℂ → ℂ), AnalyticOn ℂ Lam Set.univ →
        (∀ s : ℂ, 1 < s.re →
          Lam s = Work.FITop4.Bridge.heckeArch d 0 s *
            Work.FIArea5.S16Hecke.heckeLSeries chi 0 s) →
        ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 →
          ‖Work.FIArea6Hecke.Lval d 0 Lam s‖
            ≤ C * (d : ℝ) ^ (10 : ℕ) * (1 + |s.im|) ^ (10 : ℕ) := by
  classical
  -- absolute constants: the `re s = -1/2` line bound and the Phragmén–Lindelöf constant
  obtain ⟨K₁, hK₁pos, hK₁⟩ := Work.FIArea6Hecke.R.heckeLval_negHalf_bound'
  obtain ⟨CPL, hCPLpos, hPL⟩ := strip_bound_of_two_lines_uniform
  have hLMpos : 0 < Work.FIArea5.S16Hecke.heckeLMajorant :=
    Work.FIArea5.S16Hecke.heckeLMajorant_pos
  refine ⟨max 1 (CPL * (Work.FIArea5.S16Hecke.heckeLMajorant + K₁)), le_max_left _ _, ?_⟩
  intro d hd chi hchi hreal hb Lam hAn hagr s hs1 hs2
  by_cases hcase : ∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧
      Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧ chi z ≠ 1
  · -- ## Case 1: `χ` is nontrivial on some primary unit mod `4d`
    -- then the twist `ψ = χ·ν` has nonzero unit sum and vanishing `0`-th Gauss sum, so the
    -- construction of the completion applies and the functional equation gives the line bounds
    obtain ⟨z₀, hz₀p, hz₀u, hz₀ne⟩ := hcase
    set psi : GaussianInt → ℂ := Work.FIArea5.S16Hecke.twist chi 0 with hpsi
    have hpsiStrict : Work.FIArea5.S16Hecke.IsCharMod4dStrict d psi := by
      rw [hpsi]
      exact Work.FIArea5.S16Hecke.twist_isCharMod4dStrict d hd chi 0 hchi
    have hbpsi : ∀ z : GaussianInt, ‖psi z‖ ≤ 1 := hpsiStrict.1.2.2.1
    have hU : Work.FIArea5.S16Hecke.unitSum psi 0 ≠ 0 := by
      rw [hpsi, Work.FIArea5.S16Hecke.twist_unitSum d hd chi 0 hchi.1]
      norm_num
    have h0 : Work.FIArea5.S16Hecke.gaussSum d psi 0 = 0 := by
      refine gaussSum_zero_of_nontrivial (d := d) hd hpsiStrict ⟨z₀, hz₀p, hz₀u, ?_⟩
      rw [hpsi, Work.FIArea5.S16Hecke.twist_eq_of_isPrimary chi 0 hz₀p]
      exact hz₀ne
    have hseries : Work.FIArea5.S16Hecke.heckeLSeries psi 0
        = Work.FIArea5.S16Hecke.heckeLSeries chi 0 := by
      rw [hpsi]
      simpa using Work.FIArea6Hecke.heckeLSeries_twist chi 0
    have hagr' : ∀ s : ℂ, 1 < s.re →
        Lam s = Work.FITop4.Bridge.heckeArch d 0 s *
          Work.FIArea5.S16Hecke.heckeLSeries psi 0 s := by
      intro s hs
      rw [hagr s hs, hseries]
    -- the continuation `Lval d 0 Lam` is entire
    have hf_an : AnalyticOn ℂ (Work.FIArea6Hecke.Lval d 0 Lam) Set.univ := by
      have hdiff : Differentiable ℂ (Work.FIArea5.S16Hecke.Lcont d Lam 0) :=
        Work.FIArea5.S16Hecke.differentiable_Lcont hd
          (differentiableOn_univ.mp hAn.differentiableOn) 0
      have hfe : Work.FIArea6Hecke.Lval d 0 Lam = Work.FIArea5.S16Hecke.Lcont d Lam 0 := by
        funext z
        simp only [Work.FIArea6Hecke.Lval, Work.FIArea5.S16Hecke.Lcont,
          Work.FIArea5.S16Hecke.completeDenom, Work.FITop4.Bridge.heckeArch]
        norm_num
      rw [hfe]
      exact DifferentiableOn.analyticOn (Differentiable.differentiableOn hdiff) isOpen_univ
    -- bound on the line `re s = 3/2`: the absolutely convergent Dirichlet series
    have hline1 : ∀ t : ℝ,
        ‖Work.FIArea6Hecke.Lval d 0 Lam (((3 : ℝ) / 2 : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ Work.FIArea5.S16Hecke.heckeLMajorant := by
      intro t
      set s1 : ℂ := ((3 : ℝ) / 2 : ℂ) + (t : ℂ) * Complex.I with hs1
      have hs1re : s1.re = 3 / 2 := by simp [hs1]
      have hgt : (1 : ℝ) < s1.re := by rw [hs1re]; norm_num
      have hne : Work.FITop4.Bridge.heckeArch d 0 s1 ≠ 0 :=
        heckeArch_ne_zero_pos hd (by rw [hs1re]; norm_num)
      have hval : Work.FIArea6Hecke.Lval d 0 Lam s1
          = Work.FIArea5.S16Hecke.heckeLSeries psi 0 s1 := by
        simp only [Work.FIArea6Hecke.Lval]
        rw [hagr' s1 hgt]
        exact mul_div_cancel_left₀ _ hne
      rw [hval]
      exact Work.FIArea5.S16Hecke.heckeLSeries_norm_le_re_ge_three_halves psi 0 hbpsi
        (by rw [hs1re])
    -- bound on the line `re s = -1/2`: the functional equation
    have hline2 : ∀ t : ℝ,
        ‖Work.FIArea6Hecke.Lval d 0 Lam (((-1 : ℝ) / 2 : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ (K₁ * (d : ℝ) ^ (3 : ℕ)) * (1 + |t|) ^ (2 : ℕ) := by
      intro t
      have h := hK₁ d hd psi hpsiStrict hbpsi hU h0 Lam hAn hagr' t
      have harg : ((((-1 / 2 : ℝ)) : ℂ) + (t : ℂ) * Complex.I)
          = (((-1 : ℝ) / 2 : ℂ) + (t : ℂ) * Complex.I) := by push_cast; ring
      rw [harg] at h
      exact h
    -- Phragmén–Lindelöf growth condition in the strip
    have hgr : ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, -1 / 2 ≤ z.re → z.re ≤ 3 / 2 →
        ‖Work.FIArea6Hecke.Lval d 0 Lam z‖ ≤ Real.exp (K * (1 + |z.im|)) :=
      heckeLval_strip_growth d hd psi hpsiStrict hbpsi hU h0 Lam hAn hagr'
    have hB₂pos : 0 < K₁ * (d : ℝ) ^ (3 : ℕ) := by positivity
    have hbnd := hPL (Work.FIArea6Hecke.Lval d 0 Lam) hf_an
      Work.FIArea5.S16Hecke.heckeLMajorant (K₁ * (d : ℝ) ^ (3 : ℕ))
      hLMpos hB₂pos hline1 hline2 hgr s.re s.im hs1 hs2
    have hz : ((s.re : ℂ) + (s.im : ℂ) * Complex.I) = s := by
      apply Complex.ext <;> simp
    rw [hz] at hbnd
    -- absorb the `d`-powers into `C·d^10`
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hd3 : (1 : ℝ) ≤ (d : ℝ) ^ (3 : ℕ) := one_le_pow₀ hd1
    have hd10 : (d : ℝ) ^ (3 : ℕ) ≤ (d : ℝ) ^ (10 : ℕ) :=
      pow_le_pow_right₀ (by linarith) (by norm_num)
    have hK₁nn : 0 ≤ K₁ := le_of_lt hK₁pos
    have hCPLnn : 0 ≤ CPL := le_of_lt hCPLpos
    have hz10 : 0 ≤ (1 + |s.im|) ^ (10 : ℕ) := by positivity
    have hd10nn : 0 ≤ (d : ℝ) ^ (10 : ℕ) := by positivity
    refine le_trans hbnd ?_
    calc CPL * (Work.FIArea5.S16Hecke.heckeLMajorant + K₁ * (d : ℝ) ^ (3 : ℕ))
          * (1 + |s.im|) ^ (10 : ℕ)
        ≤ CPL * ((Work.FIArea5.S16Hecke.heckeLMajorant + K₁) * (d : ℝ) ^ (3 : ℕ))
          * (1 + |s.im|) ^ (10 : ℕ) := by
          have h1 : Work.FIArea5.S16Hecke.heckeLMajorant + K₁ * (d : ℝ) ^ (3 : ℕ)
              ≤ (Work.FIArea5.S16Hecke.heckeLMajorant + K₁) * (d : ℝ) ^ (3 : ℕ) := by
            nlinarith [hLMpos, hK₁nn, hd3]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hCPLnn) hz10
      _ ≤ CPL * ((Work.FIArea5.S16Hecke.heckeLMajorant + K₁) * (d : ℝ) ^ (10 : ℕ))
          * (1 + |s.im|) ^ (10 : ℕ) := by
          have h2 : (Work.FIArea5.S16Hecke.heckeLMajorant + K₁) * (d : ℝ) ^ (3 : ℕ)
              ≤ (Work.FIArea5.S16Hecke.heckeLMajorant + K₁) * (d : ℝ) ^ (10 : ℕ) :=
            mul_le_mul_of_nonneg_left hd10 (by linarith)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hCPLnn) hz10
      _ = CPL * (Work.FIArea5.S16Hecke.heckeLMajorant + K₁) * (d : ℝ) ^ (10 : ℕ)
          * (1 + |s.im|) ^ (10 : ℕ) := by ring
      _ ≤ max 1 (CPL * (Work.FIArea5.S16Hecke.heckeLMajorant + K₁)) * (d : ℝ) ^ (10 : ℕ)
          * (1 + |s.im|) ^ (10 : ℕ) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_right _ _) hd10nn) hz10
  · -- ## Case 2: `χ` is trivial on every primary unit mod `4d`
    -- then its `L`-series is that of the principal strict character, whose completion does not
    -- exist, so the hypothesis is contradictory
    push_neg at hcase
    have hlam : Work.FIArea5.S16Hecke.heckeLam chi 0
        = Work.FIArea5.S16Hecke.heckeLam (Work.FIArea6Hecke.principalStrict d) 0 := by
      funext n
      simp only [Work.FIArea5.S16Hecke.heckeLam, Work.FIArea5.S16Hecke.psi, zpow_zero, mul_one]
      refine Finset.sum_congr rfl fun z hz => ?_
      rw [Finset.mem_filter] at hz
      obtain ⟨-, hzp, hzn⟩ := hz
      by_cases hu : Work.FIArea5.S16Hecke.IsUnitMod4d d z
      · rw [hcase z hzp hu, Work.FIArea6Hecke.principalStrict_of_unit hu]
      · rw [hchi.2 z hu, Work.FIArea6Hecke.principalStrict_of_not_unit hu]
    have hseries : Work.FIArea5.S16Hecke.heckeLSeries chi 0
        = Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.principalStrict d) 0 := by
      funext z
      simp only [Work.FIArea5.S16Hecke.heckeLSeries]
      rw [hlam]
    exact absurd ⟨Lam, hAn, fun s hs => by rw [hagr s hs, hseries]⟩
      (noCompletion_principalStrict d hd)

end

end Work.FIArea6Hecke.R
