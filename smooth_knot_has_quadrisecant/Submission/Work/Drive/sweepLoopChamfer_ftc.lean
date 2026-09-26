import Mathlib
import Submission.Work.Drive.chordSweepSmooth
import Submission.Work.Drive.chordSweepDefs
import Submission.Work.Drive.sweepWindowKnots

/-!
# The fundamental theorem of calculus along the chamfered sweep loop

`Work.Drive.sweepLoopChamfer r D lam s ·` is `period`-periodic and piecewise smooth in the loop
parameter `t`, with breakpoints at the three profile values `1/2`, `1/2 + lam/2`, `1 - lam/2`
(plus the period jumps of `sweepParam`).  The *right* derivative of the loop is a piecewise
formula (`sweepLoopChamferDerivR`), which agrees with `sweepLoopChamferDeriv` away from those
three profile values.  The target

`Γ(s, τ₂) - Γ(s, τ₁) = ∫ τ in τ₁..τ₂, Γ'(s, τ)`

then follows from the right-derivative form of FTC-2 (`integral_eq_sub_of_hasDeriv_right`).
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology unitInterval

variable {r : ℝ → Space} {d : BandArcData}

/-! ## The four branch values of the derivative with respect to the profile

These are the derivatives of the four branches of `sweepUnwrap` with respect to the profile
variable `u` (note the extra `1 / period` relating this to the loop parameter `t`). -/

/-- First branch value: the derivative of the arc side. -/
noncomputable def sweepBranch1 (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam s u : ℝ) : Space :=
  (2 * (1 - 2 * lam)) •
    ((sweepW' D s) • deriv r (taR D s + (lam + (1 - 2 * lam) * (2 * u)) * sweepW' D s))

/-- Second branch value: the derivative of the first chamfer. -/
noncomputable def sweepBranch2 (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam s : ℝ) : Space :=
  (2 / lam) • (sweepChord' r D s (1 - lam) - sweepArc' r D s (1 - lam))

/-- Third branch value: the derivative of the chord side. -/
noncomputable def sweepBranch3 (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam s : ℝ) : Space :=
  (-(1 - 2 * lam) / (1 / 2 - lam)) • (r (tbR D s) - r (taR D s))

/-- Fourth branch value: the derivative of the second chamfer. -/
noncomputable def sweepBranch4 (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam s : ℝ) : Space :=
  (2 / lam) • (sweepArc' r D s lam - sweepChord' r D s lam)

/-- The right derivative of the unwrapped loop, as a function of the profile `u`. -/
noncomputable def sweepUnwrapDeriv (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam s u : ℝ) : Space :=
  if u < 1 / 2 then sweepBranch1 r D lam s u
  else if u < 1 / 2 + lam / 2 then sweepBranch2 r D lam s
  else if u < 1 - lam / 2 then sweepBranch3 r D lam s
  else sweepBranch4 r D lam s

/-- The right derivative of the chamfered loop with respect to its loop parameter. -/
noncomputable def sweepLoopChamferDerivR (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam s : ℝ) : ℝ → Space :=
  fun t => (1 / period) • sweepUnwrapDeriv r D lam s (sweepParam t)

/-! ## The four branches of `sweepUnwrap`, as explicit functions of the profile -/

noncomputable def sweepphi1 (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam s : ℝ) : ℝ → Space :=
  fun u => sweepArc' r D s (lam + (1 - 2 * lam) * (2 * u))

noncomputable def sweepphi2 (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam s : ℝ) : ℝ → Space :=
  fun u => (1 - (2 * u - 1) / lam) • sweepArc' r D s (1 - lam)
    + ((2 * u - 1) / lam) • sweepChord' r D s (1 - lam)

noncomputable def sweepphi3 (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam s : ℝ) : ℝ → Space :=
  fun u =>
    sweepChord' r D s ((1 - lam) - ((u - (1 / 2 + lam / 2)) / (1 / 2 - lam)) * (1 - 2 * lam))

noncomputable def sweepphi4 (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam s : ℝ) : ℝ → Space :=
  fun u => (1 - (u - (1 - lam / 2)) / (lam / 2)) • sweepChord' r D s lam
    + ((u - (1 - lam / 2)) / (lam / 2)) • sweepArc' r D s lam

/-- `sweepUnwrap` is the `if`-chain of the four branch functions. -/
lemma sweepUnwrap_eq_ite (D : SweepData d) (lam s u : ℝ) :
    sweepUnwrap r D lam s u
      = if u ≤ 1 / 2 then sweepphi1 r D lam s u
        else if u ≤ 1 / 2 + lam / 2 then sweepphi2 r D lam s u
        else if u ≤ 1 - lam / 2 then sweepphi3 r D lam s u
        else sweepphi4 r D lam s u := by
  simp only [sweepUnwrap, sweepphi1, sweepphi2, sweepphi3, sweepphi4]

/-! ## Derivatives of the four branch functions -/

lemma hasDerivAt_sweepphi1 {D : SweepData d} (hd : Differentiable ℝ r) (lam s u : ℝ) :
    HasDerivAt (sweepphi1 r D lam s) (sweepBranch1 r D lam s u) u := by
  change HasDerivAt (fun u' : ℝ => r (taR D s + (lam + (1 - 2 * lam) * (2 * u')) * sweepW' D s))
    (sweepBranch1 r D lam s u) u
  have h0 : HasDerivAt
      (fun u' : ℝ => taR D s + (lam + (1 - 2 * lam) * (2 * u')) * sweepW' D s)
      (((1 - 2 * lam) * 2) * sweepW' D s) u := by
    have h1 : HasDerivAt (fun u' : ℝ => (1 - 2 * lam) * (2 * u')) ((1 - 2 * lam) * 2) u :=
      (((hasDerivAt_id u).const_mul 2).const_mul (1 - 2 * lam)).congr_deriv (by ring)
    have h2 : HasDerivAt (fun u' : ℝ => lam + (1 - 2 * lam) * (2 * u')) ((1 - 2 * lam) * 2) u :=
      h1.const_add lam
    have h3 : HasDerivAt (fun u' : ℝ => (lam + (1 - 2 * lam) * (2 * u')) * sweepW' D s)
        (((1 - 2 * lam) * 2) * sweepW' D s) u := h2.mul_const (sweepW' D s)
    exact h3.const_add (taR D s)
  have hr : HasDerivAt r
      (deriv r (taR D s + (lam + (1 - 2 * lam) * (2 * u)) * sweepW' D s))
      (taR D s + (lam + (1 - 2 * lam) * (2 * u)) * sweepW' D s) :=
    (hd _).hasDerivAt
  refine (hr.scomp u h0).congr_deriv ?_
  simp only [sweepBranch1, smul_smul]
  congr 1
  ring

lemma hasDerivAt_sweepphi2 {D : SweepData d} (lam s u : ℝ) :
    HasDerivAt (sweepphi2 r D lam s) (sweepBranch2 r D lam s) u := by
  have hw : HasDerivAt (fun u' : ℝ => (2 * u' - 1) / lam) (2 / lam) u := by
    have h : HasDerivAt (fun u' : ℝ => 2 * u' - 1) 2 u :=
      (((hasDerivAt_id u).const_mul 2).sub_const 1).congr_deriv (by ring)
    simpa using h.div_const lam
  have h1 : HasDerivAt (fun u' : ℝ => 1 - (2 * u' - 1) / lam) (0 - 2 / lam) u :=
    (hasDerivAt_const u 1).sub hw
  have h2 : HasDerivAt
      (fun u' : ℝ => (1 - (2 * u' - 1) / lam) • sweepArc' r D s (1 - lam))
      ((0 - 2 / lam) • sweepArc' r D s (1 - lam)) u :=
    h1.smul_const _
  have h3 : HasDerivAt
      (fun u' : ℝ => ((2 * u' - 1) / lam) • sweepChord' r D s (1 - lam))
      ((2 / lam) • sweepChord' r D s (1 - lam)) u :=
    hw.smul_const _
  have h4 := h2.add h3
  refine h4.congr_deriv ?_
  simp only [sweepBranch2]
  simp only [zero_sub, neg_smul, smul_sub]
  abel

lemma hasDerivAt_sweepphi3 {D : SweepData d} (lam s u : ℝ) (hden : (1 / 2 : ℝ) - lam ≠ 0) :
    HasDerivAt (sweepphi3 r D lam s) (sweepBranch3 r D lam s) u := by
  have hg : HasDerivAt (fun u' : ℝ => (u' - (1 / 2 + lam / 2)) / (1 / 2 - lam))
      (1 / (1 / 2 - lam)) u := by
    have h : HasDerivAt (fun u' : ℝ => u' - (1 / 2 + lam / 2)) 1 u :=
      (hasDerivAt_id u).sub_const _
    simpa using h.div_const (1 / 2 - lam)
  have hξ : HasDerivAt
      (fun u' : ℝ => (1 - lam) - ((u' - (1 / 2 + lam / 2)) / (1 / 2 - lam)) * (1 - 2 * lam))
      (-((1 / (1 / 2 - lam)) * (1 - 2 * lam))) u := by
    have h := (hg.mul_const (1 - 2 * lam)).const_sub (1 - lam)
    -- h : HasDerivAt (fun u => (1-lam) - (...)*(1-2lam)) (0 - (1/(1/2-lam))*(1-2lam)) u
    refine h.congr_deriv ?_
    ring
  have h1 : HasDerivAt (fun u' : ℝ => 1 -
        ((1 - lam) - ((u' - (1 / 2 + lam / 2)) / (1 / 2 - lam)) * (1 - 2 * lam)))
      (0 - -((1 / (1 / 2 - lam)) * (1 - 2 * lam))) u :=
    (hasDerivAt_const u 1).sub hξ
  have h2 : HasDerivAt (fun u' : ℝ => (1 -
        ((1 - lam) - ((u' - (1 / 2 + lam / 2)) / (1 / 2 - lam)) * (1 - 2 * lam))) • r (taR D s))
      ((0 - -((1 / (1 / 2 - lam)) * (1 - 2 * lam))) • r (taR D s)) u := h1.smul_const _
  have h3 : HasDerivAt (fun u' : ℝ =>
        ((1 - lam) - ((u' - (1 / 2 + lam / 2)) / (1 / 2 - lam)) * (1 - 2 * lam)) • r (tbR D s))
      ((-((1 / (1 / 2 - lam)) * (1 - 2 * lam))) • r (tbR D s)) u := hξ.smul_const _
  have h4 := h2.add h3
  refine h4.congr_deriv ?_
  rw [sweepBranch3]
  rw [show -(1 - 2 * lam) / (1 / 2 - lam) = -((1 / (1 / 2 - lam)) * (1 - 2 * lam)) by
    simp only [div_eq_mul_inv]
    ring]
  simp only [zero_sub, neg_neg, neg_smul, smul_sub]
  abel

lemma hasDerivAt_sweepphi4 {D : SweepData d} (lam s u : ℝ) :
    HasDerivAt (sweepphi4 r D lam s) (sweepBranch4 r D lam s) u := by
  have hw : HasDerivAt (fun u' : ℝ => (u' - (1 - lam / 2)) / (lam / 2)) (1 / (lam / 2)) u := by
    have h : HasDerivAt (fun u' : ℝ => u' - (1 - lam / 2)) 1 u := (hasDerivAt_id u).sub_const _
    simpa using h.div_const (lam / 2)
  have h1 : HasDerivAt (fun u' : ℝ => 1 - (u' - (1 - lam / 2)) / (lam / 2))
      (0 - 1 / (lam / 2)) u := (hasDerivAt_const u 1).sub hw
  have h2 : HasDerivAt (fun u' : ℝ => (1 - (u' - (1 - lam / 2)) / (lam / 2)) • sweepChord' r D s lam)
      ((0 - 1 / (lam / 2)) • sweepChord' r D s lam) u := h1.smul_const _
  have h3 : HasDerivAt (fun u' : ℝ => ((u' - (1 - lam / 2)) / (lam / 2)) • sweepArc' r D s lam)
      ((1 / (lam / 2)) • sweepArc' r D s lam) u := hw.smul_const _
  have h4 := h2.add h3
  refine h4.congr_deriv ?_
  simp only [sweepBranch4]
  rw [show (2 / lam) = 1 / (lam / 2) by
    simp only [div_eq_mul_inv]
    ring]
  rw [zero_sub, neg_smul, smul_sub]
  abel

/-! ## The junction values of the branches -/

lemma sweepphi1_eq_sweepphi2_half (D : SweepData d) (lam s : ℝ) :
    sweepphi1 r D lam s (1 / 2) = sweepphi2 r D lam s (1 / 2) := by
  simp only [sweepphi1, sweepphi2]
  have h2 : (2 : ℝ) * (1 / 2) - 1 = 0 := by norm_num
  have h3 : lam + (1 - 2 * lam) * (2 * (1 / 2)) = 1 - lam := by ring
  rw [h2, h3, zero_div]
  simp

lemma sweepphi2_eq_sweepphi3 (D : SweepData d) {lam : ℝ} (_h0 : 0 < lam) (s : ℝ) :
    sweepphi2 r D lam s (1 / 2 + lam / 2) = sweepphi3 r D lam s (1 / 2 + lam / 2) := by
  simp only [sweepphi2, sweepphi3]
  have h2 : (2 * (1 / 2 + lam / 2) - 1) / lam = 1 := by
    field_simp
    ring
  have h3 : (1 - lam) - (((1 / 2 + lam / 2) - (1 / 2 + lam / 2)) / (1 / 2 - lam)) * (1 - 2 * lam)
      = 1 - lam := by
    rw [sub_self, zero_div, zero_mul, sub_zero]
  rw [h2, h3]
  simp

lemma sweepphi3_eq_sweepphi4 (D : SweepData d) {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1 / 2)
    (s : ℝ) :
    sweepphi3 r D lam s (1 - lam / 2) = sweepphi4 r D lam s (1 - lam / 2) := by
  simp only [sweepphi3, sweepphi4]
  have h3 : (1 - lam) - (((1 - lam / 2) - (1 / 2 + lam / 2)) / (1 / 2 - lam)) * (1 - 2 * lam)
      = lam := by
    have hd : (1 - lam / 2) - (1 / 2 + lam / 2) = 1 / 2 - lam := by ring
    rw [hd, div_self (by linarith : (1 / 2 : ℝ) - lam ≠ 0), one_mul]
    ring
  have h4 : ((1 - lam / 2) - (1 - lam / 2)) / (lam / 2) = 0 := by
    rw [sub_self, zero_div]
  rw [h3, h4]
  simp

/-! ## The right derivative of the unwrapped loop -/

theorem sweepUnwrap_hasDerivWithinAt {D : SweepData d} (hd : Differentiable ℝ r)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1 / 2) (s u : ℝ) :
    HasDerivWithinAt (fun u' => sweepUnwrap r D lam s u') (sweepUnwrapDeriv r D lam s u)
      (Set.Ioi u) u := by
  rcases lt_trichotomy u (1 / 2) with h1 | h1 | h1
  · -- first branch
    have hder : HasDerivAt (sweepphi1 r D lam s) (sweepBranch1 r D lam s u) u :=
      hasDerivAt_sweepphi1 (D := D) hd lam s u
    have hev : (fun u' => sweepUnwrap r D lam s u') =ᶠ[𝓝[>] u] sweepphi1 r D lam s := by
      filter_upwards [Ioo_mem_nhdsGT h1] with u' hu'
      rw [sweepUnwrap_eq_ite, if_pos (le_of_lt hu'.2)]
    have hx : sweepUnwrap r D lam s u = sweepphi1 r D lam s u := by
      rw [sweepUnwrap_eq_ite, if_pos (le_of_lt h1)]
    rw [show sweepUnwrapDeriv r D lam s u = sweepBranch1 r D lam s u by
      simp only [sweepUnwrapDeriv]; rw [if_pos h1]]
    exact (hder.hasDerivWithinAt).congr_of_eventuallyEq hev hx
  · -- junction at 1/2
    subst h1
    have hder : HasDerivAt (sweepphi2 r D lam s) (sweepBranch2 r D lam s) (1 / 2) :=
      hasDerivAt_sweepphi2 (D := D) lam s (1 / 2)
    have hev : (fun u' => sweepUnwrap r D lam s u') =ᶠ[𝓝[>] (1 / 2 : ℝ)] sweepphi2 r D lam s := by
      filter_upwards [Ioo_mem_nhdsGT (by linarith : (1 / 2 : ℝ) < 1 / 2 + lam / 2)] with u' hu'
      rw [sweepUnwrap_eq_ite, if_neg (not_le.mpr hu'.1), if_pos (le_of_lt hu'.2)]
    have hx : sweepUnwrap r D lam s (1 / 2) = sweepphi2 r D lam s (1 / 2) := by
      rw [sweepUnwrap_eq_ite, if_pos le_rfl]
      exact sweepphi1_eq_sweepphi2_half D lam s
    rw [show sweepUnwrapDeriv r D lam s (1 / 2) = sweepBranch2 r D lam s by
      simp only [sweepUnwrapDeriv]
      rw [if_neg (lt_irrefl _), if_pos (by linarith : (1 / 2 : ℝ) < 1 / 2 + lam / 2)]]
    exact (hder.hasDerivWithinAt).congr_of_eventuallyEq hev hx
  · rcases lt_trichotomy u (1 / 2 + lam / 2) with h2 | h2 | h2
    · -- second branch
      have hder : HasDerivAt (sweepphi2 r D lam s) (sweepBranch2 r D lam s) u :=
        hasDerivAt_sweepphi2 (D := D) lam s u
      have hev : (fun u' => sweepUnwrap r D lam s u') =ᶠ[𝓝[>] u] sweepphi2 r D lam s := by
        filter_upwards [Ioo_mem_nhdsGT h2] with u' hu'
        rw [sweepUnwrap_eq_ite, if_neg (not_le.mpr (lt_trans h1 hu'.1)), if_pos (le_of_lt hu'.2)]
      have hx : sweepUnwrap r D lam s u = sweepphi2 r D lam s u := by
        rw [sweepUnwrap_eq_ite, if_neg (not_le.mpr h1), if_pos (le_of_lt h2)]
      rw [show sweepUnwrapDeriv r D lam s u = sweepBranch2 r D lam s by
        simp only [sweepUnwrapDeriv]
        rw [if_neg (not_lt.mpr h1.le), if_pos h2]]
      exact (hder.hasDerivWithinAt).congr_of_eventuallyEq hev hx
    · -- junction at 1/2 + lam/2
      subst h2
      have hlt : (1 / 2 : ℝ) < 1 / 2 + lam / 2 := by linarith
      have hder : HasDerivAt (sweepphi3 r D lam s) (sweepBranch3 r D lam s) (1 / 2 + lam / 2) :=
        hasDerivAt_sweepphi3 (D := D) lam s _ (by linarith)
      have hev : (fun u' => sweepUnwrap r D lam s u') =ᶠ[𝓝[>] (1 / 2 + lam / 2 : ℝ)]
          sweepphi3 r D lam s := by
        filter_upwards [Ioo_mem_nhdsGT (by linarith : (1 / 2 + lam / 2 : ℝ) < 1 - lam / 2)]
          with u' hu'
        rw [sweepUnwrap_eq_ite, if_neg (not_le.mpr (lt_trans hlt hu'.1)),
          if_neg (not_le.mpr hu'.1), if_pos (le_of_lt hu'.2)]
      have hx : sweepUnwrap r D lam s (1 / 2 + lam / 2) = sweepphi3 r D lam s (1 / 2 + lam / 2) := by
        rw [sweepUnwrap_eq_ite, if_neg (not_le.mpr hlt), if_pos le_rfl]
        exact sweepphi2_eq_sweepphi3 D hlam0 s
      rw [show sweepUnwrapDeriv r D lam s (1 / 2 + lam / 2) = sweepBranch3 r D lam s by
        simp only [sweepUnwrapDeriv]
        rw [if_neg (not_lt.mpr hlt.le), if_neg (lt_irrefl _),
          if_pos (by linarith : (1 / 2 + lam / 2 : ℝ) < 1 - lam / 2)]]
      exact (hder.hasDerivWithinAt).congr_of_eventuallyEq hev hx
    · rcases lt_trichotomy u (1 - lam / 2) with h3 | h3 | h3
      · -- third branch
        have hder : HasDerivAt (sweepphi3 r D lam s) (sweepBranch3 r D lam s) u :=
          hasDerivAt_sweepphi3 (D := D) lam s u (by linarith)
        have hev : (fun u' => sweepUnwrap r D lam s u') =ᶠ[𝓝[>] u] sweepphi3 r D lam s := by
          filter_upwards [Ioo_mem_nhdsGT h3] with u' hu'
          rw [sweepUnwrap_eq_ite, if_neg (not_le.mpr (lt_trans h1 hu'.1)),
            if_neg (not_le.mpr (lt_trans h2 hu'.1)), if_pos (le_of_lt hu'.2)]
        have hx : sweepUnwrap r D lam s u = sweepphi3 r D lam s u := by
          rw [sweepUnwrap_eq_ite, if_neg (not_le.mpr h1), if_neg (not_le.mpr h2),
            if_pos (le_of_lt h3)]
        rw [show sweepUnwrapDeriv r D lam s u = sweepBranch3 r D lam s by
          simp only [sweepUnwrapDeriv]
          rw [if_neg (not_lt.mpr h1.le), if_neg (not_lt.mpr h2.le), if_pos h3]]
        exact (hder.hasDerivWithinAt).congr_of_eventuallyEq hev hx
      · -- junction at 1 - lam/2
        subst h3
        have hlt2 : (1 / 2 + lam / 2 : ℝ) < 1 - lam / 2 := by linarith
        have hder : HasDerivAt (sweepphi4 r D lam s) (sweepBranch4 r D lam s) (1 - lam / 2) :=
          hasDerivAt_sweepphi4 (D := D) lam s (1 - lam / 2)
        have hev : (fun u' => sweepUnwrap r D lam s u') =ᶠ[𝓝[>] (1 - lam / 2 : ℝ)]
            sweepphi4 r D lam s := by
          filter_upwards [Ioo_mem_nhdsGT (by linarith : (1 - lam / 2 : ℝ) < 1)] with u' hu'
          rw [sweepUnwrap_eq_ite, if_neg (not_le.mpr (lt_trans h1 hu'.1)),
            if_neg (not_le.mpr (lt_trans hlt2 hu'.1)), if_neg (not_le.mpr hu'.1)]
        have hx : sweepUnwrap r D lam s (1 - lam / 2) = sweepphi4 r D lam s (1 - lam / 2) := by
          rw [sweepUnwrap_eq_ite, if_neg (not_le.mpr h1), if_neg (not_le.mpr hlt2),
            if_pos le_rfl]
          exact sweepphi3_eq_sweepphi4 D hlam0 hlam1 s
        rw [show sweepUnwrapDeriv r D lam s (1 - lam / 2) = sweepBranch4 r D lam s by
          simp only [sweepUnwrapDeriv]
          rw [if_neg (not_lt.mpr h1.le), if_neg (not_lt.mpr hlt2.le), if_neg (lt_irrefl _)]]
        exact (hder.hasDerivWithinAt).congr_of_eventuallyEq hev hx
      · -- fourth branch
        have hder : HasDerivAt (sweepphi4 r D lam s) (sweepBranch4 r D lam s) u :=
          hasDerivAt_sweepphi4 (D := D) lam s u
        have hev : (fun u' => sweepUnwrap r D lam s u') =ᶠ[𝓝[>] u] sweepphi4 r D lam s := by
          filter_upwards [self_mem_nhdsWithin] with u' hu'
          rw [sweepUnwrap_eq_ite, if_neg (not_le.mpr (lt_trans h1 hu')),
            if_neg (not_le.mpr (lt_trans h2 hu')), if_neg (not_le.mpr (lt_trans h3 hu'))]
        have hx : sweepUnwrap r D lam s u = sweepphi4 r D lam s u := by
          rw [sweepUnwrap_eq_ite, if_neg (not_le.mpr h1), if_neg (not_le.mpr h2),
            if_neg (not_le.mpr h3)]
        rw [show sweepUnwrapDeriv r D lam s u = sweepBranch4 r D lam s by
          simp only [sweepUnwrapDeriv]
          rw [if_neg (not_lt.mpr h1.le), if_neg (not_lt.mpr h2.le), if_neg (not_lt.mpr h3.le)]]
        exact (hder.hasDerivWithinAt).congr_of_eventuallyEq hev hx


/-! ## The a.e. identity with `sweepLoopChamferDeriv` -/

/-- For `u` different from the three profile breakpoints, the two `if`-chains (`≤` versus `<`)
agree. -/
lemma ite_chain_eq {α : Type*} (u c₁ c₂ c₃ : ℝ) (h₁ : u ≠ c₁) (h₂ : u ≠ c₂) (h₃ : u ≠ c₃)
    (a b c e : α) :
    (if u ≤ c₁ then a else if u ≤ c₂ then b else if u ≤ c₃ then c else e)
      = (if u < c₁ then a else if u < c₂ then b else if u < c₃ then c else e) := by
  by_cases hlt₁ : u < c₁
  · rw [if_pos (le_of_lt hlt₁), if_pos hlt₁]
  · rw [if_neg (not_le.mpr (lt_of_le_of_ne (not_lt.mp hlt₁) h₁.symm)), if_neg hlt₁]
    by_cases hlt₂ : u < c₂
    · rw [if_pos (le_of_lt hlt₂), if_pos hlt₂]
    · rw [if_neg (not_le.mpr (lt_of_le_of_ne (not_lt.mp hlt₂) h₂.symm)), if_neg hlt₂]
      by_cases hlt₃ : u < c₃
      · rw [if_pos (le_of_lt hlt₃), if_pos hlt₃]
      · rw [if_neg (not_le.mpr (lt_of_le_of_ne (not_lt.mp hlt₃) h₃.symm)), if_neg hlt₃]

lemma sweepLoopChamferDeriv_eq_derivR_of_ne {D : SweepData d} (lam s t : ℝ)
    (h₁ : sweepParam t ≠ 1 / 2) (h₂ : sweepParam t ≠ 1 / 2 + lam / 2)
    (h₃ : sweepParam t ≠ 1 - lam / 2) :
    sweepLoopChamferDeriv r D lam s t = sweepLoopChamferDerivR r D lam s t := by
  simp only [sweepLoopChamferDeriv, sweepLoopChamferDerivR, sweepUnwrapDeriv,
    sweepBranch1, sweepBranch2, sweepBranch3, sweepBranch4]
  congr 1
  exact ite_chain_eq (sweepParam t) (1 / 2) (1 / 2 + lam / 2) (1 - lam / 2) h₁ h₂ h₃ _ _ _ _

/-- The level set of `sweepParam` at a value `c` is countable. -/
lemma countable_sweepParam_eq (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    {t : ℝ | sweepParam t = c}.Countable := by
  have hset : {t : ℝ | sweepParam t = c} = Set.range (fun k : ℤ => ((k : ℝ) + c) * period) := by
    ext t
    constructor
    · intro ht
      have ht' : t / period - ((⌊t / period⌋ : ℤ) : ℝ) = c := ht
      have hdiv : t / period = ((⌊t / period⌋ : ℤ) : ℝ) + c := by linarith
      refine ⟨⌊t / period⌋, ?_⟩
      dsimp only
      rw [← hdiv]
      exact div_mul_cancel₀ t (ne_of_gt period_pos)
    · rintro ⟨k, rfl⟩
      show sweepParam (((k : ℝ) + c) * period) = c
      simp only [sweepParam]
      rw [mul_div_cancel_right₀ _ (ne_of_gt period_pos)]
      have hfloor : ⌊(k : ℝ) + c⌋ = k := by
        rw [Int.floor_eq_iff]
        constructor <;> linarith
      rw [hfloor]
      ring
  rw [hset]
  exact Set.countable_range _

lemma sweepLoopChamferDeriv_ae_eq_derivR {D : SweepData d} {lam : ℝ} (hlam0 : 0 < lam)
    (hlam1 : lam < 1 / 2) (s : ℝ) :
    sweepLoopChamferDeriv r D lam s =ᵐ[MeasureTheory.volume] sweepLoopChamferDerivR r D lam s := by
  have hc : ({t : ℝ | sweepParam t = 1 / 2} ∪ {t : ℝ | sweepParam t = 1 / 2 + lam / 2}
      ∪ {t : ℝ | sweepParam t = 1 - lam / 2}).Countable :=
    ((countable_sweepParam_eq (1 / 2) (by norm_num) (by norm_num)).union
      (countable_sweepParam_eq (1 / 2 + lam / 2) (by linarith) (by linarith))).union
      (countable_sweepParam_eq (1 - lam / 2) (by linarith) (by linarith))
  have hbad : MeasureTheory.volume ({t : ℝ | sweepParam t = 1 / 2} ∪ {t : ℝ | sweepParam t = 1 / 2 + lam / 2}
      ∪ {t : ℝ | sweepParam t = 1 - lam / 2}) = 0 := Set.Countable.measure_zero hc MeasureTheory.volume
  show ∀ᵐ x ∂MeasureTheory.volume,
    sweepLoopChamferDeriv r D lam s x = sweepLoopChamferDerivR r D lam s x
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_ hbad
  intro t ht
  simp only [Set.mem_setOf_eq] at ht
  simp only [Set.mem_union, Set.mem_setOf_eq]
  rcases em (sweepParam t = 1 / 2) with h1 | h1
  · exact Or.inl (Or.inl h1)
  rcases em (sweepParam t = 1 / 2 + lam / 2) with h2 | h2
  · exact Or.inl (Or.inr h2)
  rcases em (sweepParam t = 1 - lam / 2) with h3 | h3
  · exact Or.inr h3
  · exact absurd (sweepLoopChamferDeriv_eq_derivR_of_ne lam s t h1 h2 h3) ht

/-! ## Measurability and boundedness of the right derivative -/

lemma measurable_sweepBranch1 {D : SweepData d} (hderiv : Continuous (deriv r))
    (lam s : ℝ) : Measurable (sweepBranch1 r D lam s) := by
  have h : (fun u : ℝ => (2 * (1 - 2 * lam)) •
      ((sweepW' D s) • deriv r (taR D s + (lam + (1 - 2 * lam) * (2 * u)) * sweepW' D s)))
      = sweepBranch1 r D lam s := rfl
  rw [← h]
  refine Continuous.measurable ?_
  have h1 : Continuous (fun u : ℝ => (2 : ℝ) * u) := continuous_const.mul continuous_id
  have h2 : Continuous (fun u : ℝ => (1 - 2 * lam) * (2 * u)) := continuous_const.mul h1
  have h3 : Continuous (fun u : ℝ => lam + (1 - 2 * lam) * (2 * u)) := continuous_const.add h2
  have h4 : Continuous (fun u : ℝ =>
      (lam + (1 - 2 * lam) * (2 * u)) * sweepW' D s) := h3.mul continuous_const
  exact (continuous_const : Continuous (fun _ : ℝ => (2 * (1 - 2 * lam)))).smul
    ((continuous_const : Continuous (fun _ : ℝ => (sweepW' D s))).smul
      (hderiv.comp (h4.const_add (taR D s))))

lemma measurable_sweepUnwrapDeriv {D : SweepData d} (hderiv : Continuous (deriv r))
    (lam s : ℝ) : Measurable (sweepUnwrapDeriv r D lam s) := by
  have hb1 := measurable_sweepBranch1 (r := r) (D := D) hderiv lam s
  have h : sweepUnwrapDeriv r D lam s = (fun u : ℝ =>
      if u < 1 / 2 then sweepBranch1 r D lam s u
      else if u < 1 / 2 + lam / 2 then sweepBranch2 r D lam s
      else if u < 1 - lam / 2 then sweepBranch3 r D lam s
      else sweepBranch4 r D lam s) := rfl
  rw [h]
  exact Measurable.ite measurableSet_Iio hb1
    (Measurable.ite measurableSet_Iio measurable_const
      (Measurable.ite measurableSet_Iio measurable_const measurable_const))

lemma measurable_sweepLoopChamferDerivR {D : SweepData d} (hderiv : Continuous (deriv r))
    (lam s : ℝ) : Measurable (sweepLoopChamferDerivR r D lam s) := by
  have h : sweepLoopChamferDerivR r D lam s
      = fun t : ℝ => (1 / period) • sweepUnwrapDeriv r D lam s (sweepParam t) := rfl
  rw [h]
  exact ((measurable_sweepUnwrapDeriv (r := r) (D := D) hderiv lam s).comp
    sweepLoopChamfer_sweepParam_measurable).const_smul (1 / period)

/-- A convex combination of two reals lies between them. -/
lemma conv_mem_uIcc {a b ξ : ℝ} (h0 : 0 ≤ ξ) (h1 : ξ ≤ 1) :
    (1 - ξ) * a + ξ * b ∈ Set.uIcc a b := by
  rcases le_total a b with hab | hab
  · rw [Set.uIcc_of_le hab, Set.mem_Icc]
    constructor <;> nlinarith
  · rw [Set.uIcc_of_ge hab, Set.mem_Icc]
    constructor <;> nlinarith

lemma norm_sweepArc'_le {D : SweepData d} {s Br : ℝ}
    (hBr : ∀ y ∈ Set.uIcc (taR D s) (tbR D s), ‖r y‖ ≤ Br) {ξ : ℝ}
    (hξ : ξ ∈ Set.Icc (0 : ℝ) 1) : ‖sweepArc' r D s ξ‖ ≤ Br := by
  have hmem : taR D s + ξ * sweepW' D s ∈ Set.uIcc (taR D s) (tbR D s) := by
    have h : taR D s + ξ * sweepW' D s = (1 - ξ) * taR D s + ξ * tbR D s := by
      simp only [sweepW']; ring
    rw [h]
    exact conv_mem_uIcc hξ.1 hξ.2
  simpa only [sweepArc'] using hBr _ hmem

lemma norm_sweepChord'_le {D : SweepData d} {s Br : ℝ}
    (hBr : ∀ y ∈ Set.uIcc (taR D s) (tbR D s), ‖r y‖ ≤ Br) {ξ : ℝ}
    (hξ : ξ ∈ Set.Icc (0 : ℝ) 1) : ‖sweepChord' r D s ξ‖ ≤ Br := by
  have h : sweepChord' r D s ξ = (1 - ξ) • r (taR D s) + ξ • r (tbR D s) := rfl
  rw [h]
  calc ‖(1 - ξ) • r (taR D s) + ξ • r (tbR D s)‖
      ≤ ‖(1 - ξ) • r (taR D s)‖ + ‖ξ • r (tbR D s)‖ := norm_add_le _ _
    _ = (1 - ξ) * ‖r (taR D s)‖ + ξ * ‖r (tbR D s)‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by linarith [hξ.1, hξ.2]), abs_of_nonneg hξ.1]
    _ ≤ (1 - ξ) * Br + ξ * Br := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_left (hBr _ Set.left_mem_uIcc) (by linarith [hξ.2])
        · exact mul_le_mul_of_nonneg_left (hBr _ Set.right_mem_uIcc) hξ.1
    _ = Br := by ring

lemma norm_sweepUnwrapDeriv_le {D : SweepData d} {s : ℝ} {Bd Br : ℝ}
    (hBd : ∀ y ∈ Set.uIcc (taR D s) (tbR D s), ‖deriv r y‖ ≤ Bd)
    (hBr : ∀ y ∈ Set.uIcc (taR D s) (tbR D s), ‖r y‖ ≤ Br)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1 / 2) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖sweepUnwrapDeriv r D lam s u‖ ≤
      max (2 * |1 - 2 * lam| * |sweepW' D s| * Bd)
        (max (2 / lam * (2 * Br)) (max (|(1 - 2 * lam) / (1 / 2 - lam)| * (2 * Br))
          (2 / lam * (2 * Br)))) := by
  have hξl : (1 - lam) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hξl' : lam ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hlam0, by linarith⟩
  have hmem2 : ‖sweepChord' r D s (1 - lam) - sweepArc' r D s (1 - lam)‖ ≤ 2 * Br := by
    calc ‖sweepChord' r D s (1 - lam) - sweepArc' r D s (1 - lam)‖
        ≤ ‖sweepChord' r D s (1 - lam)‖ + ‖sweepArc' r D s (1 - lam)‖ := norm_sub_le _ _
      _ ≤ Br + Br := add_le_add (norm_sweepChord'_le (s := s) hBr hξl)
        (norm_sweepArc'_le (s := s) hBr hξl)
      _ = 2 * Br := by ring
  have hmem4 : ‖sweepArc' r D s lam - sweepChord' r D s lam‖ ≤ 2 * Br := by
    calc ‖sweepArc' r D s lam - sweepChord' r D s lam‖
        ≤ ‖sweepArc' r D s lam‖ + ‖sweepChord' r D s lam‖ := norm_sub_le _ _
      _ ≤ Br + Br := add_le_add (norm_sweepArc'_le (s := s) hBr hξl')
        (norm_sweepChord'_le (s := s) hBr hξl')
      _ = 2 * Br := by ring
  rw [sweepUnwrapDeriv]
  split_ifs with h1 h2 h3
  · have hξ1 : lam + (1 - 2 * lam) * (2 * u) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> nlinarith [h1, hu0]
    have hy : taR D s + (lam + (1 - 2 * lam) * (2 * u)) * sweepW' D s
        ∈ Set.uIcc (taR D s) (tbR D s) := by
      have h : taR D s + (lam + (1 - 2 * lam) * (2 * u)) * sweepW' D s
          = (1 - (lam + (1 - 2 * lam) * (2 * u))) * taR D s
            + (lam + (1 - 2 * lam) * (2 * u)) * tbR D s := by
        simp only [sweepW']; ring
      rw [h]
      exact conv_mem_uIcc hξ1.1 hξ1.2
    have hb : ‖sweepBranch1 r D lam s u‖ ≤ 2 * |1 - 2 * lam| * |sweepW' D s| * Bd := by
      simp only [sweepBranch1]
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      have h2' : |2 * (1 - 2 * lam)| = 2 * |1 - 2 * lam| := by
        rw [abs_mul]; norm_num
      rw [h2']
      calc 2 * |1 - 2 * lam| * (|sweepW' D s| * ‖deriv r (taR D s + (lam + (1 - 2 * lam) * (2 * u)) * sweepW' D s)‖)
          = 2 * |1 - 2 * lam| * |sweepW' D s| * ‖deriv r (taR D s + (lam + (1 - 2 * lam) * (2 * u)) * sweepW' D s)‖ := by ring
        _ ≤ 2 * |1 - 2 * lam| * |sweepW' D s| * Bd :=
            mul_le_mul_of_nonneg_left (hBd _ hy)
              (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) (abs_nonneg _))
    exact le_trans hb (le_max_left _ _)
  · have hb : ‖sweepBranch2 r D lam s‖ ≤ 2 / lam * (2 * Br) := by
      simp only [sweepBranch2]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos two_pos hlam0)]
      exact mul_le_mul_of_nonneg_left hmem2 (le_of_lt (div_pos two_pos hlam0))
    exact le_trans hb (le_trans (le_max_left _ _) (le_max_right _ _))
  · have hb : ‖sweepBranch3 r D lam s‖ ≤ |(1 - 2 * lam) / (1 / 2 - lam)| * (2 * Br) := by
      simp only [sweepBranch3]
      rw [norm_smul, Real.norm_eq_abs, neg_div, abs_neg]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      calc ‖r (tbR D s) - r (taR D s)‖
          ≤ ‖r (tbR D s)‖ + ‖r (taR D s)‖ := norm_sub_le _ _
        _ ≤ Br + Br := add_le_add (hBr _ Set.right_mem_uIcc) (hBr _ Set.left_mem_uIcc)
        _ = 2 * Br := by ring
    refine le_trans hb (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_max_right _ _)))
  · have hb : ‖sweepBranch4 r D lam s‖ ≤ 2 / lam * (2 * Br) := by
      simp only [sweepBranch4]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos two_pos hlam0)]
      exact mul_le_mul_of_nonneg_left hmem4 (le_of_lt (div_pos two_pos hlam0))
    exact le_trans hb (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_max_right _ _)))

lemma norm_sweepLoopChamferDerivR_le {D : SweepData d} (hr : Continuous r)
    (hderiv : Continuous (deriv r)) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1 / 2)
    (s : ℝ) : ∃ C, ∀ t, ‖sweepLoopChamferDerivR r D lam s t‖ ≤ C := by
  obtain ⟨Bd, hBd⟩ := isCompact_uIcc.exists_bound_of_continuousOn
    (s := Set.uIcc (taR D s) (tbR D s)) hderiv.continuousOn
  obtain ⟨Br, hBr⟩ := isCompact_uIcc.exists_bound_of_continuousOn
    (s := Set.uIcc (taR D s) (tbR D s)) hr.continuousOn
  refine ⟨1 / period * max (2 * |1 - 2 * lam| * |sweepW' D s| * Bd)
      (max (2 / lam * (2 * Br)) (max (|(1 - 2 * lam) / (1 / 2 - lam)| * (2 * Br))
        (2 / lam * (2 * Br)))), fun t => ?_⟩
  have hu := sweepParam_mem t
  have hbound := norm_sweepUnwrapDeriv_le (D := D) (s := s) hBd hBr hlam0 hlam1 hu.1 hu.2.le
  simp only [sweepLoopChamferDerivR]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr period_pos)]
  exact mul_le_mul_of_nonneg_left hbound (le_of_lt (one_div_pos.mpr period_pos))

/-! ## The right derivative of the chamfered loop -/

theorem sweepLoopChamfer_hasDerivWithinAt {r : ℝ → Space}
    (hr : ContDiff ℝ 1 r) {d : BandArcData} (D : SweepData d)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1 / 2) (s x : ℝ) :
    HasDerivWithinAt (fun t => sweepLoopChamfer r D lam s t)
      (sweepLoopChamferDerivR r D lam s x) (Set.Ioi x) x := by
  have hd : Differentiable ℝ r := hr.differentiable (by norm_num)
  set k : ℤ := ⌊x / period⌋ with hk
  have hu : sweepParam x = x / period - (k : ℝ) := by simp only [sweepParam]; rw [← hk]
  have hin : HasDerivWithinAt (fun u' => sweepUnwrap r D lam s u')
      (sweepUnwrapDeriv r D lam s (x / period - (k : ℝ))) (Set.Ioi (x / period - (k : ℝ)))
      (x / period - (k : ℝ)) := by
    have := sweepUnwrap_hasDerivWithinAt (D := D) hd hlam0 hlam1 s (sweepParam x)
    simpa [hu] using this
  have hφ : HasDerivWithinAt (fun t : ℝ => t / period - (k : ℝ)) (1 / period) (Set.Ioi x) x :=
    (((hasDerivAt_id x).div_const period).sub_const (k : ℝ)).hasDerivWithinAt
  have hmap : Set.MapsTo (fun t : ℝ => t / period - (k : ℝ)) (Set.Ioi x)
      (Set.Ioi (x / period - (k : ℝ))) := by
    intro t ht
    simp only [Set.mem_Ioi] at ht ⊢
    have h := div_lt_div_of_pos_right ht period_pos
    linarith
  have hcomp := HasDerivWithinAt.scomp x hin hφ hmap
  have hev : (fun t => sweepLoopChamfer r D lam s t)
      =ᶠ[𝓝[>] x] (fun t => sweepUnwrap r D lam s (t / period - (k : ℝ))) := by
    have hpos : (0 : ℝ) < period * (1 - sweepParam x) / 2 := by
      have h := (sweepParam_mem x).2
      have hp := period_pos
      nlinarith
    filter_upwards [Ioo_mem_nhdsGT (by linarith : x < x + period * (1 - sweepParam x) / 2)]
      with t ht
    rw [sweepLoopChamfer_eq_unwrap]
    congr 1
    rw [sweepParam]
    have hfloor : ⌊t / period⌋ = k := by
      rw [Int.floor_eq_iff]
      refine ⟨?_, ?_⟩
      · have hxk : (k : ℝ) ≤ x / period := by
          have := Int.floor_le (x / period)
          simpa [hk] using this
        have := div_lt_div_of_pos_right ht.1 period_pos
        linarith
      · have hlt : t / period < x / period + (1 - sweepParam x) / 2 := by
          rw [div_lt_iff₀ period_pos]
          rw [show (x / period + (1 - sweepParam x) / 2) * period
              = x + period * (1 - sweepParam x) / 2 by
            rw [add_mul, div_mul_cancel₀ x (ne_of_gt period_pos)]
            ring]
          exact ht.2
        have hfloor' : x / period = (k : ℝ) + sweepParam x := by rw [hu]; ring
        rw [hfloor'] at hlt
        have h2 := (sweepParam_mem x).2
        nlinarith
    rw [hfloor]
  have hx : sweepLoopChamfer r D lam s x = sweepUnwrap r D lam s (x / period - (k : ℝ)) := by
    rw [sweepLoopChamfer_eq_unwrap, hu]
  rw [show sweepLoopChamferDerivR r D lam s x
      = (1 / period) • sweepUnwrapDeriv r D lam s (x / period - (k : ℝ)) by
    simp only [sweepLoopChamferDerivR, hu]]
  exact hcomp.congr_of_eventuallyEq hev hx

/-! ## The fundamental theorem of calculus -/

theorem sweepLoopChamfer_ftc {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : ContDiff ℝ 1 r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1 / 2) (s τ₁ τ₂ : ℝ) :
    Work.Drive.sweepLoopChamfer r D lam s τ₂ - Work.Drive.sweepLoopChamfer r D lam s τ₁
      = ∫ τ in τ₁..τ₂, Work.Drive.sweepLoopChamferDeriv r D lam s τ := by
  have hcont : ContinuousOn (fun t => sweepLoopChamfer r D lam s t) (Set.uIcc τ₁ τ₂) :=
    (sweepLoopChamfer_continuous_t hr.continuous D hlam0 hlam1).continuousOn
  have hderiv : ∀ x ∈ Set.Ioo (min τ₁ τ₂) (max τ₁ τ₂),
      HasDerivWithinAt (fun t => sweepLoopChamfer r D lam s t)
        (sweepLoopChamferDerivR r D lam s x) (Set.Ioi x) x :=
    fun x _ => sweepLoopChamfer_hasDerivWithinAt hr D hlam0 hlam1 s x
  have hint : IntervalIntegrable (sweepLoopChamferDerivR r D lam s) MeasureTheory.volume τ₁ τ₂ := by
    rw [intervalIntegrable_iff]
    obtain ⟨C, hC⟩ := norm_sweepLoopChamferDerivR_le (D := D) hr.continuous
      (hr.continuous_deriv (by norm_num)) hlam0 hlam1 s
    have hfin : MeasureTheory.volume (Set.uIoc τ₁ τ₂) < (⊤ : ENNReal) := by
      show MeasureTheory.volume (Set.Ioc (min τ₁ τ₂) (max τ₁ τ₂)) < (⊤ : ENNReal)
      exact lt_of_le_of_lt (MeasureTheory.measure_mono Set.Ioc_subset_Icc_self)
        isCompact_Icc.measure_lt_top
    refine MeasureTheory.IntegrableOn.of_bound hfin ?_ C (Filter.Eventually.of_forall hC)
    exact (measurable_sweepLoopChamferDerivR (D := D)
      (hr.continuous_deriv (by norm_num)) lam s).aestronglyMeasurable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right hcont hderiv hint
  have hae : (∫ τ in τ₁..τ₂, sweepLoopChamferDeriv r D lam s τ)
      = ∫ τ in τ₁..τ₂, sweepLoopChamferDerivR r D lam s τ :=
    intervalIntegral.integral_congr_ae (by
      filter_upwards [sweepLoopChamferDeriv_ae_eq_derivR (D := D) hlam0 hlam1 s]
        with x hx _
      exact hx)
  rw [hae, hFTC]


end Work.Drive
