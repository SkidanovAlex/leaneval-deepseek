import Mathlib
import Submission.Work.Drive.sweepWideEndDefs
import Submission.Work.Drive.chordSweepSmooth
import Submission.Work.Drive.chordSweepDefs
import Submission.Work.Drive.chamferVelBranch
import Submission.KnotMap

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

lemma cvb_loopChamfer_add_period (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam s t : ℝ) : sweepLoopChamfer r D lam s (t + period) = sweepLoopChamfer r D lam s t := by
  simp only [sweepLoopChamfer, sweepParam_add_period]
open scoped Real Topology unitInterval

/-! ### Periodicity helpers -/

private lemma cvb_periodic_deriv {f : ℝ → Space} (h : Function.Periodic f period) :
    Function.Periodic (deriv f) period := by
  intro x
  have h1 : deriv f (x + period) = deriv (fun y : ℝ => f (y + period)) x := by
    have h2 : (fun y : ℝ => f (period + y)) = (fun y : ℝ => f (y + period)) := by
      funext y; rw [add_comm]
    have h3 := deriv_comp_const_add f period x
    rw [h2, add_comm period x] at h3
    exact h3.symm
  rw [h1, h.funext]

private lemma cvb_periodic_velocity {r : ℝ → Space} (hr : IsSmoothKnot r) :
    Function.Periodic (velocity r) period := by
  have h := cvb_periodic_deriv (f := r) hr.periodic
  simpa [velocity] using h

private lemma cvb_exists_norm_bound_of_periodic {f : ℝ → Space} (hf : Continuous f)
    (hper : Function.Periodic f period) : ∃ C : ℝ, ∀ x : ℝ, ‖f x‖ ≤ C := by
  obtain ⟨x₀, hx₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    ⟨0, Set.left_mem_Icc.mpr period_pos.le⟩ (hf.norm.continuousOn)
  refine ⟨‖f x₀‖, fun x => ?_⟩
  have hx : x - (⌊x / period⌋ : ℤ) * period ∈ Set.Icc (0:ℝ) period := by
    constructor
    · have h1 : ((⌊x / period⌋ : ℤ) : ℝ) ≤ x / period := Int.floor_le _
      nlinarith [period_pos, div_mul_cancel₀ x period_ne_zero]
    · have h1 : x / period < ((⌊x / period⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
      nlinarith [period_pos, div_mul_cancel₀ x period_ne_zero]
  have hper' : f (x - (⌊x / period⌋ : ℤ) * period) = f x := hper.sub_int_mul_eq _
  rw [← hper']
  exact hmax hx

private lemma cvb_exists_norm_lower_of_periodic {f : ℝ → Space} (hf : Continuous f)
    (hper : Function.Periodic f period) (hne : ∀ x, f x ≠ 0) :
    ∃ m : ℝ, 0 < m ∧ ∀ x : ℝ, m ≤ ‖f x‖ := by
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    ⟨0, Set.left_mem_Icc.mpr period_pos.le⟩ (hf.norm.continuousOn)
  refine ⟨‖f x₀‖, norm_pos_iff.mpr (hne x₀), fun x => ?_⟩
  have hx : x - (⌊x / period⌋ : ℤ) * period ∈ Set.Icc (0:ℝ) period := by
    constructor
    · have h1 : ((⌊x / period⌋ : ℤ) : ℝ) ≤ x / period := Int.floor_le _
      nlinarith [period_pos, div_mul_cancel₀ x period_ne_zero]
    · have h1 : x / period < ((⌊x / period⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
      nlinarith [period_pos, div_mul_cancel₀ x period_ne_zero]
  have hper' : f (x - (⌊x / period⌋ : ℤ) * period) = f x := hper.sub_int_mul_eq _
  rw [← hper']
  exact hmin hx

/-! ### Elementary quantitative facts about a smooth knot -/

private lemma cvb_knot_eq_iff {r : ℝ → Space} (hr : IsSmoothKnot r) (x y : ℝ) :
    r x = r y ↔ (x : AddCircle period) = (y : AddCircle period) := by
  constructor
  · intro h
    have h1 : knotMap r (x : AddCircle period) = knotMap r (y : AddCircle period) := by
      rw [knotMap_coe' hr.periodic x, knotMap_coe' hr.periodic y, h]
    exact knotMap_injective hr h1
  · intro h
    rw [← knotMap_coe' hr.periodic x, ← knotMap_coe' hr.periodic y, h]

private lemma cvb_continuous_deriv2 {r : ℝ → Space} (hr : IsSmoothKnot r) :
    Continuous (deriv (velocity r)) := by
  have hC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r := hr.smooth.of_le le_top
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv r) := (contDiff_infty_iff_deriv.mp hC).2
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv (deriv r)) :=
    (contDiff_infty_iff_deriv.mp h1).2
  have hcont : Continuous (deriv (deriv r)) := h2.continuous
  change Continuous (deriv (deriv r))
  exact hcont

private lemma cvb_chord_lipschitz {r : ℝ → Space} (hr : IsSmoothKnot r) {L : ℝ}
    (hL : ∀ x, ‖velocity r x‖ ≤ L) (x y : ℝ) :
    ‖r y - r x‖ ≤ L * |y - x| := by
  have hdiff : ∀ x : ℝ, DifferentiableAt ℝ r x :=
    fun x => (hr.smooth.differentiable (by simp)).differentiableAt
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := r) (s := Set.univ) (C := L)
    (fun z _ => hdiff z)
    (fun z _ => by simpa [velocity] using hL z)
    convex_univ (Set.mem_univ x) (Set.mem_univ y)
  simpa [Real.norm_eq_abs] using h

/-- The small-separation estimate: for parameter separations below a definite threshold the
chord is at least a definite multiple of the separation. -/
private lemma cvb_chord_small {r : ℝ → Space} (hr : IsSmoothKnot r) {m C : ℝ} (hm : 0 < m) (hC : 0 < C)
    (hvel : ∀ x, m ≤ ‖velocity r x‖)
    (hacc : ∀ x, ‖deriv (velocity r) x‖ ≤ C) :
    ∀ x s : ℝ, 0 ≤ s → s ≤ m / (2 * C) → (m / 2) * s ≤ ‖r (x + s) - r x‖ := by
  have hvcont : Continuous (velocity r) := hr.smooth.continuous_deriv le_top
  intro x s hs0 hs
  have hvdiff : ∀ y : ℝ, DifferentiableAt ℝ (velocity r) y := by
    intro y
    have hC' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r := hr.smooth.of_le le_top
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv r) := (contDiff_infty_iff_deriv.mp hC').2
    have h3 : Differentiable ℝ (deriv r) := h1.differentiable (by simp)
    change DifferentiableAt ℝ (deriv r) y
    exact h3.differentiableAt
  have hmvt : ∀ y, ‖velocity r y - velocity r x‖ ≤ C * |y - x| := by
    intro y
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := velocity r) (s := Set.univ) (C := C)
      (fun z _ => hvdiff z) (fun z _ => hacc z) convex_univ (Set.mem_univ x) (Set.mem_univ y)
    simpa [Real.norm_eq_abs] using h
  have hderiv : ∀ y ∈ Set.Ioo x (x + s), HasDerivAt r (velocity r y) y := by
    intro y hy
    have : DifferentiableAt ℝ r y := (hr.smooth.differentiable (by simp)).differentiableAt
    simpa [velocity] using this.hasDerivAt
  have hFTC : ∫ y in x..(x + s), velocity r y = r (x + s) - r x :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by linarith)
      hr.smooth.continuous.continuousOn hderiv (hvcont.intervalIntegrable _ _)
  have hsub : (∫ y in x..(x + s), (velocity r y - velocity r x))
      = (∫ y in x..(x + s), velocity r y) - s • velocity r x := by
    rw [intervalIntegral.integral_sub (hvcont.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _), intervalIntegral.integral_const]
    norm_num
  have hbnd : ‖∫ y in x..(x + s), (velocity r y - velocity r x)‖ ≤ C * s * s := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun y => velocity r y - velocity r x) (a := x) (b := x + s) (C := C * s) ?_
    · rw [add_sub_cancel_left, abs_of_nonneg hs0] at h
      exact h
    · intro y hy
      rw [Set.uIoc_of_le (by linarith)] at hy
      have h1 : |y - x| ≤ s := by
        rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
      calc ‖velocity r y - velocity r x‖ ≤ C * |y - x| := hmvt y
        _ ≤ C * s := by nlinarith [hC.le, h1]
  have hstar : s * m - C * s * s ≤ ‖r (x + s) - r x‖ := by
    have hEq : r (x + s) - r x
        = (∫ y in x..(x + s), (velocity r y - velocity r x)) + s • velocity r x := by
      rw [hsub, hFTC]; abel
    rw [hEq]
    have hnorm : ‖s • velocity r x‖ = s * ‖velocity r x‖ := by
      rw [norm_smul, Real.norm_of_nonneg hs0]
    have h2 : ‖s • velocity r x‖
        ≤ ‖(∫ y in x..(x + s), (velocity r y - velocity r x)) + s • velocity r x‖
          + ‖∫ y in x..(x + s), (velocity r y - velocity r x)‖ := by
      have := norm_sub_le ((∫ y in x..(x + s), (velocity r y - velocity r x)) + s • velocity r x)
        (∫ y in x..(x + s), (velocity r y - velocity r x))
      simpa using this
    nlinarith [hnorm, h2, hbnd, hvel x]
  have hs' : s * (2 * C) ≤ m := by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < 2 * C)] at hs
    linarith
  nlinarith [hstar, hs', hm, hs0, hC]

/-- The medium-separation estimate: separations between `δ` and half a period are bounded away
from zero. -/
private lemma cvb_chord_medium {r : ℝ → Space} (hr : IsSmoothKnot r) {δ : ℝ} (hδ : 0 < δ)
    (hδ2 : δ ≤ period / 2) :
    ∃ κ₁ : ℝ, 0 < κ₁ ∧ ∀ x s : ℝ, δ ≤ s → s ≤ period / 2 → κ₁ ≤ ‖r (x + s) - r x‖ := by
  have hcont : Continuous (fun p : ℝ × ℝ => ‖r (p.1 + p.2) - r p.1‖) := by
    have h1 : Continuous (fun p : ℝ × ℝ => p.1 + p.2) := continuous_fst.add continuous_snd
    have h2 : Continuous (fun p : ℝ × ℝ => r (p.1 + p.2)) := hr.smooth.continuous.comp h1
    have h3 : Continuous (fun p : ℝ × ℝ => r p.1) := hr.smooth.continuous.comp continuous_fst
    exact (h2.sub h3).norm
  have hK : IsCompact (Set.Icc ((0:ℝ), δ) (period, period / 2)) := isCompact_Icc
  have hne : (Set.Icc ((0:ℝ), δ) (period, period / 2)).Nonempty :=
    ⟨(0, δ), ⟨⟨le_rfl, le_rfl⟩, ⟨period_pos.le, hδ2⟩⟩⟩
  obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hne hcont.continuousOn
  have hp1 : p.1 ∈ Set.Icc (0:ℝ) period := ⟨hp.1.1, hp.2.1⟩
  have hp2 : p.2 ∈ Set.Icc δ (period / 2) := ⟨hp.1.2, hp.2.2⟩
  have hpos2 : 0 < p.2 := lt_of_lt_of_le hδ hp2.1
  have hdist : r (p.1 + p.2) ≠ r p.1 := by
    intro heq
    have hcl : ((p.1 + p.2 : ℝ) : AddCircle period) = (p.1 : AddCircle period) :=
      (cvb_knot_eq_iff hr _ _).mp heq
    have hz : (p.2 : AddCircle period) = 0 := by
      have h1 : ((p.1 + p.2 : ℝ) : AddCircle period) - (p.1 : AddCircle period) = 0 := by
        rw [hcl, sub_self]
      rwa [← AddCircle.coe_sub, add_sub_cancel_left] at h1
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (p := period)).mp hz
    rcases eq_or_ne k 0 with hk0 | hk0
    · subst hk0
      have hkz : p.2 = 0 := by simpa using hk.symm
      linarith [hp2.1, hδ]
    · have hk' : ((k : ℤ) : ℝ) * period = p.2 := by rw [← hk, zsmul_eq_mul]
      have hkposR : 0 < ((k : ℤ) : ℝ) * period := by rw [hk']; exact hpos2
      have hkpos : 0 < ((k : ℤ) : ℝ) := pos_of_mul_pos_left hkposR period_pos.le
      have hk1 : (1:ℝ) ≤ ((k : ℤ) : ℝ) := by
        have h1 : (1:ℤ) ≤ k := by
          have : (0:ℤ) < k := by exact_mod_cast hkpos
          omega
        exact_mod_cast h1
      have hple : period ≤ p.2 := by
        rw [← hk']
        nlinarith [hk1, period_pos]
      linarith [hp2.2, period_pos]
  set κ₁ : ℝ := ‖r (p.1 + p.2) - r p.1‖ with hκ₁def
  have hκ₁pos : 0 < κ₁ := by
    rw [hκ₁def]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hdist)
  have key : ∀ q : ℝ × ℝ, q ∈ Set.Icc ((0:ℝ), δ) (period, period / 2) →
      κ₁ ≤ ‖r (q.1 + q.2) - r q.1‖ := by
    intro q hq
    rw [hκ₁def]
    exact hmin hq
  refine ⟨κ₁, hκ₁pos, fun x s hs1 hs2 => ?_⟩
  set k : ℤ := ⌊x / period⌋ with hkdef
  have hx : x - (k : ℝ) * period ∈ Set.Icc (0:ℝ) period := by
    constructor
    · have h1 : ((k : ℤ) : ℝ) ≤ x / period := by rw [hkdef]; exact Int.floor_le _
      nlinarith [period_pos, div_mul_cancel₀ x period_ne_zero]
    · have h1 : x / period < ((k : ℤ) : ℝ) + 1 := by rw [hkdef]; exact Int.lt_floor_add_one _
      nlinarith [period_pos, div_mul_cancel₀ x period_ne_zero]
  have hper : r (x - (k : ℝ) * period) = r x := hr.periodic.sub_int_mul_eq k
  have hswap : r (x + s) = r ((x - (k : ℝ) * period) + s) := by
    have h := hr.periodic.sub_int_mul_eq (x := (x - (k : ℝ) * period) + s) (-k)
    rw [← h]
    push_cast
    ring
  have hq : (x - (k : ℝ) * period, s) ∈ Set.Icc ((0:ℝ), δ) (period, period / 2) :=
    ⟨⟨hx.1, hs1⟩, ⟨hx.2, hs2⟩⟩
  have hgoal : κ₁ ≤ ‖r ((x - (k : ℝ) * period) + s) - r (x - (k : ℝ) * period)‖ := key (x - (k : ℝ) * period, s) hq
  rw [← hswap, hper] at hgoal
  exact hgoal

/-- The clamping map `ℝ → I` is continuous. -/
private lemma cvb_clampI_continuous : Continuous (clampI : ℝ → I) :=
  Continuous.subtype_mk (continuous_const.min (continuous_const.max continuous_id)) _

/-- The width of the retained arc at a real parameter in `(0,1)` is strictly between `0` and
`period`. -/
private lemma cvb_sweepW'_pos_lt {d : BandArcData} (D : SweepData d) {sig : ℝ} (h1 : 0 < sig) (h2 : sig < 1) :
    0 < sweepW' D sig ∧ sweepW' D sig < period := by
  have hI : clampI sig = (⟨sig, ⟨le_of_lt h1, le_of_lt h2⟩⟩ : I) := by
    apply Subtype.ext
    simp only [clampI]
    rw [max_eq_right h1.le, min_eq_right h2.le]
  have hw : sweepW' D sig = sweepW D (⟨sig, ⟨le_of_lt h1, le_of_lt h2⟩⟩ : I) := by
    simp only [sweepW', sweepW, taR, tbR, hI]
  rw [hw]
  exact sweepW_pos_lt D ⟨sig, ⟨le_of_lt h1, le_of_lt h2⟩⟩ ⟨h1, h2⟩

private theorem cvb_chamferDiff_lower {r : ℝ → Space}
    (hr : IsSmoothKnot r)
    {d : BandArcData} (D : SweepData d)
    {L κ lam siglo sighi θ : ℝ} (hL : 0 < L) (hκ : 0 < κ) (hlam : 0 < lam) (hlam2 : lam < 1 / 2)
    (hsl : siglo ≤ sighi) (hslo : 0 < siglo) (hshi : sighi < 1)
    (hθp : θ ≤ period) (hθκ : θ ≤ κ * period / (4 * L))
    (hlip : ∀ x s : ℝ, 0 ≤ s → s ≤ period → ‖r (x + s) - r x‖ ≤ L * min s (period - s))
    (hsep : ∀ x s : ℝ, 0 ≤ s → s ≤ period → κ * min s (period - s) ≤ ‖r (x + s) - r x‖)
    (hwidth : ∀ sig ∈ Set.Icc siglo sighi, period - sweepW' D sig ≤ θ * lam) :
    ∀ sig ∈ Set.Icc siglo sighi,
      lam * κ * period / 4 ≤ ‖sweepChord' r D sig (1 - lam) - sweepArc' r D sig (1 - lam)‖ ∧
      lam * κ * period / 4 ≤ ‖sweepArc' r D sig lam - sweepChord' r D sig lam‖ := by
  intro sig hsig
  have he_le : period - sweepW' D sig ≤ θ * lam := hwidth sig hsig
  obtain ⟨hsiglo, hsighi⟩ := hsig
  have hsigpos : 0 < sig := lt_of_lt_of_le hslo hsiglo
  have hsiglt : sig < 1 := lt_of_le_of_lt hsighi hshi
  obtain ⟨hwpos, hwlt⟩ := cvb_sweepW'_pos_lt D hsigpos hsiglt
  set w := sweepW' D sig with hwdef
  have hw_ge : period / 2 < w := by
    have h1 : w < period := hwlt
    have h2 : period - w ≤ θ * lam := he_le
    have h3 : θ * lam ≤ period * lam := mul_le_mul_of_nonneg_right hθp hlam.le
    have h4 : period * lam < period * (1 / 2) := by
      exact mul_lt_mul_of_pos_left hlam2 period_pos
    rw [hwdef]
    linarith [h1, h2, h3, h4]
  have hepos : 0 < period - w := by linarith
  -- the multiplicative bounds
  have hlam_half : lam * (period / 2) ≤ period / 4 := by
    have h := mul_lt_mul_of_pos_right hlam2 (by linarith : (0:ℝ) < period / 2)
    linarith
  have hlw : lam * (period / 2) ≤ lam * w := mul_le_mul_of_nonneg_left hw_ge.le hlam.le
  have hlpw : lam * w ≤ lam * period := mul_le_mul_of_nonneg_left hwlt.le hlam.le
  have hll : lam * (period / 2) ≤ period / 2 := by
    have h1 : lam * (period / 2) ≤ (1 / 2) * (period / 2) :=
      mul_le_mul_of_nonneg_right hlam2.le (by linarith : (0:ℝ) ≤ period / 2)
    linarith
  -- the two "long vector" estimates
  have hlong1 : κ * (lam * period / 2) ≤
      ‖r (taR D sig) - r (taR D sig + (1 - lam) * w)‖ := by
    have hδ0 : 0 ≤ (1 - lam) * w := by
      have h1 : (1 - lam) * w ≤ 1 * w :=
        mul_le_mul_of_nonneg_right (by linarith : (1:ℝ) - lam ≤ 1) hwpos.le
      linarith [hwpos]
    have hδle : (1 - lam) * w ≤ period := by
      have := mul_le_of_le_one_left hwpos.le (by linarith : (1:ℝ) - lam ≤ 1)
      linarith [hwlt]
    have hτ0 : 0 ≤ period - (1 - lam) * w := by linarith
    have hτle : period - (1 - lam) * w ≤ period := by linarith
    have hτmin : period - (period - (1 - lam) * w) = (1 - lam) * w := by ring
    have hmin1 : lam * period / 2 ≤ period - (1 - lam) * w := by
      have h2 : (period - w) + lam * w = period - (1 - lam) * w := by ring
      have h3 : lam * (period / 2) ≤ lam * w := hlw
      linarith [h2, h3, hepos]
    have hmin2 : lam * period / 2 ≤ (1 - lam) * w := by
      have h1 : (1 - lam) * (period / 2) ≤ (1 - lam) * w :=
        mul_le_mul_of_nonneg_left hw_ge.le (by linarith : (0:ℝ) ≤ 1 - lam)
      have h2 : period / 4 ≤ (1 - lam) * (period / 2) := by
        have h3 : (1 - lam) * (period / 2) = period / 2 - lam * (period / 2) := by ring
        rw [h3]; linarith [hll]
      linarith [h1, h2, hlam_half]
    have hmin : lam * period / 2 ≤ min (period - (1 - lam) * w) (period - (period - (1 - lam) * w)) := by
      rw [hτmin]
      exact le_min hmin1 hmin2
    have hper : r (taR D sig + (1 - lam) * w) = r (taR D sig - (period - (1 - lam) * w)) := by
      conv_lhs => rw [show taR D sig + (1 - lam) * w
        = (taR D sig - (period - (1 - lam) * w)) + period by ring]
      exact hr.periodic _
    have h1 := hsep (taR D sig - (period - (1 - lam) * w)) (period - (1 - lam) * w) hτ0 hτle
    have h2 : (taR D sig - (period - (1 - lam) * w)) + (period - (1 - lam) * w) = taR D sig := by
      ring
    rw [h2, ← hper] at h1
    exact le_trans (mul_le_mul_of_nonneg_left hmin hκ.le) h1
  have hlong2 : κ * (lam * period / 2) ≤
      ‖r (taR D sig + lam * w) - r (taR D sig)‖ := by
    have hσ0 : 0 ≤ lam * w := by positivity
    have hσle : lam * w ≤ period := by linarith [hlpw, hwlt]
    have hmin : lam * period / 2 ≤ min (lam * w) (period - lam * w) := by
      refine le_min ?_ ?_
      · linarith [hlw]
      have h2 : period - lam * w = (period - lam * period) + (lam * period - lam * w) := by ring
      rw [h2]
      nlinarith [hlpw, hll, hlam.le, period_pos]
    have h1 := hsep (taR D sig) (lam * w) hσ0 hσle
    exact le_trans (mul_le_mul_of_nonneg_left hmin hκ.le) h1
  -- the "short" chord vector
  have hhb : tbR D sig = taR D sig + w := by
    rw [hwdef]; simp only [sweepW']; ring
  have hshort : ‖r (tbR D sig) - r (taR D sig)‖ ≤ L * (period - w) := by
    rw [hhb]
    have hper : r (taR D sig + w) = r (taR D sig - (period - w)) := by
      conv_lhs => rw [show taR D sig + w = (taR D sig - (period - w)) + period by ring]
      exact hr.periodic _
    rw [hper]
    have h2 : (taR D sig - (period - w)) + (period - w) = taR D sig := by ring
    have hmm : min (period - w) (period - (period - w)) = period - w := by
      rw [show period - (period - w) = w by ring, min_eq_left (by linarith [hw_ge])]
    have := hlip (taR D sig - (period - w)) (period - w) (by linarith) (by linarith)
    rw [h2, hmm, norm_sub_rev] at this
    exact this
  -- the constant bounds
  have hθker : θ * L ≤ κ * period / 4 := by
    have h1 := hθκ
    rw [le_div_iff₀ (by linarith : (0:ℝ) < 4 * L)] at h1
    linarith [h1]
  have hθBnd : L * (period - w) ≤ lam * κ * period / 4 := by
    have h2 : L * (period - w) ≤ L * (θ * lam) := mul_le_mul_of_nonneg_left he_le hL.le
    have h4 : lam * (θ * L) ≤ lam * (κ * period / 4) := mul_le_mul_of_nonneg_left hθker hlam.le
    calc L * (period - w) ≤ L * (θ * lam) := h2
      _ = lam * (θ * L) := by ring
      _ ≤ lam * (κ * period / 4) := h4
      _ = lam * κ * period / 4 := by ring
  have hθBnd2 : lam * L * (period - w) ≤ lam * κ * period / 8 := by
    have h2 : lam * (L * (period - w)) ≤ lam * (L * (θ * lam)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he_le hL.le) hlam.le
    have h5 : L * θ * lam ≤ κ * period / 8 := by
      have h66 : L * θ ≤ κ * period / 4 := by linarith [hθker]
      have h6 : L * θ * lam ≤ (κ * period / 4) * lam :=
        mul_le_mul_of_nonneg_right h66 hlam.le
      have h8 : lam * (κ * period) ≤ (1 / 2) * (κ * period) :=
        mul_le_mul_of_nonneg_right hlam2.le (le_of_lt (mul_pos hκ period_pos))
      nlinarith [h6, h8]
    calc lam * L * (period - w) = lam * (L * (period - w)) := by ring
      _ ≤ lam * (L * (θ * lam)) := h2
      _ = lam * (L * θ * lam) := by ring
      _ ≤ lam * (κ * period / 8) := mul_le_mul_of_nonneg_left h5 hlam.le
      _ = lam * κ * period / 8 := by ring
  have hD1 : sweepChord' r D sig (1 - lam) - sweepArc' r D sig (1 - lam)
      = ((1 - lam) • (r (tbR D sig) - r (taR D sig)))
        + (r (taR D sig) - r (taR D sig + (1 - lam) * w)) := by
    simp only [sweepChord', sweepArc', hwdef]
    module
  have hD2 : sweepArc' r D sig lam - sweepChord' r D sig lam
      = (r (taR D sig + lam * w) - r (taR D sig))
        - lam • (r (tbR D sig) - r (taR D sig)) := by
    simp only [sweepChord', sweepArc', hwdef]
    module
  constructor
  · rw [hD1]
    have hB : ‖(1 - lam) • (r (tbR D sig) - r (taR D sig))‖ ≤ L * (period - w) := by
      rw [norm_smul, Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ 1 - lam)]
      calc (1 - lam) * ‖r (tbR D sig) - r (taR D sig)‖
          ≤ 1 * ‖r (tbR D sig) - r (taR D sig)‖ :=
            mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
        _ = ‖r (tbR D sig) - r (taR D sig)‖ := by ring
        _ ≤ L * (period - w) := hshort
    have h3 : ‖r (taR D sig) - r (taR D sig + (1 - lam) * w)‖
        ≤ ‖((1 - lam) • (r (tbR D sig) - r (taR D sig)))
            + (r (taR D sig) - r (taR D sig + (1 - lam) * w))‖
          + ‖(1 - lam) • (r (tbR D sig) - r (taR D sig))‖ := by
      have h := norm_sub_le
        (((1 - lam) • (r (tbR D sig) - r (taR D sig)))
            + (r (taR D sig) - r (taR D sig + (1 - lam) * w)))
        ((1 - lam) • (r (tbR D sig) - r (taR D sig)))
      rw [add_sub_cancel_left] at h
      exact h
    have hX : 0 < lam * κ * period := mul_pos (mul_pos hlam hκ) period_pos
    linarith [hlong1, hB, hθBnd, h3, hX]
  · rw [hD2]
    have hB : ‖lam • (r (tbR D sig) - r (taR D sig))‖ ≤ lam * L * (period - w) := by
      rw [norm_smul, Real.norm_of_nonneg hlam.le]
      calc lam * ‖r (tbR D sig) - r (taR D sig)‖ ≤ lam * (L * (period - w)) :=
            mul_le_mul_of_nonneg_left hshort hlam.le
        _ = lam * L * (period - w) := by ring
    have h3 : ‖r (taR D sig + lam * w) - r (taR D sig)‖
        ≤ ‖(r (taR D sig + lam * w) - r (taR D sig))
            - lam • (r (tbR D sig) - r (taR D sig))‖
          + ‖lam • (r (tbR D sig) - r (taR D sig))‖ := by
      have h := norm_add_le
        ((r (taR D sig + lam * w) - r (taR D sig))
            - lam • (r (tbR D sig) - r (taR D sig)))
        (lam • (r (tbR D sig) - r (taR D sig)))
      rw [sub_add_cancel] at h
      exact h
    have hX : 0 < lam * κ * period := mul_pos (mul_pos hlam hκ) period_pos
    linarith [hlong2, hB, hθBnd2, h3, hX]



/-! ### The chamfered loop as a function of the unrolled profile

On one period `[0, period]` the profile `sweepParam` is the affine map `t ↦ t / period` (except at
the endpoint `t = period`, where it is `0` but every branch formula takes its limit value there).
The four branches of `sweepLoopChamfer` are therefore the following four explicit functions of `t`,
on the four intervals cut out by `period/2`, `period/2 + lam*period/2` and `period - lam*period/2`.
-/

/-- The arc-side branch of the chamfered loop, with the unrolled profile `t ↦ t / period`. -/
def cvb_loopArc (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lam sig t : ℝ) : Space :=
  sweepArc' r D sig (lam + (1 - 2 * lam) * (2 * (t / period)))

/-- The first-chamfer branch of the chamfered loop, with the unrolled profile. -/
def cvb_loopChamfer₁ (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lam sig t : ℝ) :
    Space :=
  (1 - (2 * (t / period) - 1) / lam) • sweepArc' r D sig (1 - lam)
    + ((2 * (t / period) - 1) / lam) • sweepChord' r D sig (1 - lam)

/-- The chord-side branch of the chamfered loop, with the unrolled profile. -/
def cvb_loopChord (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lam sig t : ℝ) : Space :=
  sweepChord' r D sig
    ((1 - lam) - (((t / period) - (1 / 2 + lam / 2)) / (1 / 2 - lam)) * (1 - 2 * lam))

/-- The second-chamfer branch of the chamfered loop, with the unrolled profile. -/
def cvb_loopChamfer₂ (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lam sig t : ℝ) :
    Space :=
  (1 - ((t / period) - (1 - lam / 2)) / (lam / 2)) • sweepChord' r D sig lam
    + (((t / period) - (1 - lam / 2)) / (lam / 2)) • sweepArc' r D sig lam

/-- On a period interval the profile is the affine map `t ↦ t / period`. -/
private lemma cvb_sweepParam_div {t : ℝ} (h0 : 0 ≤ t) (h1 : t < period) :
    sweepParam t = t / period := by
  rw [sweepParam]
  have hf : ⌊t / period⌋ = 0 := by
    rw [Int.floor_eq_zero_iff]
    exact ⟨div_nonneg h0 period_pos.le, by rw [div_lt_one period_pos]; exact h1⟩
  rw [hf]
  norm_num

/-- Zone 1: on `[0, period/2]` the loop is the arc branch. -/
private lemma cvb_zone1 {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {lam sig t : ℝ}
    (h0 : 0 ≤ t) (h1 : t ≤ period / 2) :
    sweepLoopChamfer r D lam sig t = cvb_loopArc r D lam sig t := by
  have ht : t < period := lt_of_le_of_lt h1 (by linarith [period_pos])
  have hp : sweepParam t = t / period := cvb_sweepParam_div h0 ht
  have hc : t / period ≤ 1 / 2 := by
    rw [div_le_iff₀ period_pos, show (1:ℝ) / 2 * period = period / 2 by ring]
    exact h1
  have hc' : sweepParam t ≤ 1 / 2 := by rw [hp]; exact hc
  simp only [sweepLoopChamfer]
  rw [if_pos hc', hp]
  rfl

/-- On a period interval, `(period / 2) / period = 1 / 2`. -/
private lemma cvb_div_half : period / 2 / period = 1 / 2 := by
  rw [show period / 2 = (1 : ℝ) / 2 * period by ring, mul_div_cancel_right₀ _ period_ne_zero]

/-- On a period interval, `(period / 2 + lam * period / 2) / period = 1 / 2 + lam / 2`. -/
private lemma cvb_div_half_lam (lam : ℝ) :
    (period / 2 + lam * period / 2) / period = 1 / 2 + lam / 2 := by
  rw [show period / 2 + lam * period / 2 = ((1 : ℝ) / 2 + lam / 2) * period by ring,
    mul_div_cancel_right₀ _ period_ne_zero]

/-- On a period interval, `(period - lam * period / 2) / period = 1 - lam / 2`. -/
private lemma cvb_div_one_sub (lam : ℝ) :
    (period - lam * period / 2) / period = 1 - lam / 2 := by
  rw [show period - lam * period / 2 = ((1 : ℝ) - lam / 2) * period by ring,
    mul_div_cancel_right₀ _ period_ne_zero]

/-- Junction agreement at the profile value `1/2`. -/
private lemma cvb_agree1 {r : ℝ → Space} {d : BandArcData} (D : SweepData d) (lam sig : ℝ) :
    cvb_loopArc r D lam sig (period / 2) = cvb_loopChamfer₁ r D lam sig (period / 2) := by
  have h1 : (2 * (period / 2 / period) - 1) / lam = 0 := by rw [cvb_div_half]; norm_num
  have h2 : lam + (1 - 2 * lam) * (2 * (period / 2 / period)) = 1 - lam := by
    rw [cvb_div_half]; ring
  simp only [cvb_loopArc, cvb_loopChamfer₁, h1, h2]
  norm_num

/-- Junction agreement at the profile value `1/2 + lam/2`. -/
private lemma cvb_agree2 {r : ℝ → Space} {d : BandArcData} (D : SweepData d) (lam sig : ℝ)
    (hl : 0 < lam) (hl2 : lam < 1 / 2) :
    cvb_loopChamfer₁ r D lam sig (period / 2 + lam * period / 2)
      = cvb_loopChord r D lam sig (period / 2 + lam * period / 2) := by
  have h1 : (2 * ((period / 2 + lam * period / 2) / period) - 1) / lam = 1 := by
    rw [cvb_div_half_lam]
    have h2 : 2 * ((1:ℝ) / 2 + lam / 2) - 1 = lam := by ring
    rw [h2, div_self (ne_of_gt hl)]
  have h2 : (1 - lam)
      - (((period / 2 + lam * period / 2) / period - (1 / 2 + lam / 2)) / (1 / 2 - lam))
        * (1 - 2 * lam) = 1 - lam := by
    rw [cvb_div_half_lam]; ring
  simp only [cvb_loopChamfer₁, cvb_loopChord, h1, h2]
  norm_num

/-- Junction agreement at the profile value `1 - lam/2`. -/
private lemma cvb_agree3 {r : ℝ → Space} {d : BandArcData} (D : SweepData d) (lam sig : ℝ)
    (hl : 0 < lam) (hl2 : lam < 1 / 2) :
    cvb_loopChord r D lam sig (period - lam * period / 2)
      = cvb_loopChamfer₂ r D lam sig (period - lam * period / 2) := by
  have h1 : (1 - lam)
      - (((period - lam * period / 2) / period - (1 / 2 + lam / 2)) / (1 / 2 - lam))
        * (1 - 2 * lam) = lam := by
    rw [cvb_div_one_sub]
    have h2 : (1 - lam / 2 - (1 / 2 + lam / 2)) / (1 / 2 - lam) = 1 := by
      have h3 : 1 - lam / 2 - (1 / 2 + lam / 2) = (1 / 2 - lam : ℝ) := by ring
      rw [h3, div_self (ne_of_gt (by linarith : (0:ℝ) < 1 / 2 - lam))]
    rw [h2]; ring
  have h2 : ((period - lam * period / 2) / period - (1 - lam / 2)) / (lam / 2) = 0 := by
    rw [cvb_div_one_sub]; ring
  simp only [cvb_loopChord, cvb_loopChamfer₂, h1, h2]
  norm_num

/-- The loop at `t = period` is the arc value `sweepArc' lam`, and so is the second-chamfer
formula at `t = period` (the junction at profile `0` / `1`). -/
private lemma cvb_agree4 {r : ℝ → Space} {d : BandArcData} (D : SweepData d) (lam sig : ℝ)
    (hl : 0 < lam) :
    sweepArc' r D sig lam = cvb_loopChamfer₂ r D lam sig period := by
  have h1 : ((period / period) - (1 - lam / 2)) / (lam / 2) = 1 := by
    rw [div_self period_ne_zero]
    have h2 : (1 - (1 - lam / 2)) / (lam / 2) = 1 := by
      have h3 : 1 - (1 - lam / 2) = (lam / 2 : ℝ) := by ring
      rw [h3, div_self (ne_of_gt (by linarith : (0:ℝ) < lam / 2))]
    exact h2
  have h2 : (1 - lam) * (2 * 0) = 0 := by ring
  simp only [cvb_loopChamfer₂, h1, h2]
  norm_num

/-- Zone 2: on `[period/2, period/2 + lam*period/2]` the loop is the first chamfer. -/
private lemma cvb_zone2 {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {lam sig t : ℝ}
    (hl : 0 < lam) (hl2 : lam < 1 / 2) (h0 : 0 ≤ t) (h1 : period / 2 ≤ t)
    (h2 : t ≤ period / 2 + lam * period / 2) :
    sweepLoopChamfer r D lam sig t = cvb_loopChamfer₁ r D lam sig t := by
  rcases eq_or_lt_of_le h1 with hb | hb
  · rw [← hb, cvb_zone1 D (by linarith [period_pos]) le_rfl]
    exact cvb_agree1 D lam sig
  · have hc1 : 1 / 2 < t / period := by
      rw [lt_div_iff₀ period_pos, show (1:ℝ) / 2 * period = period / 2 by ring]
      exact hb
    have hc2 : t / period ≤ 1 / 2 + lam / 2 := by
      rw [div_le_iff₀ period_pos,
        show ((1:ℝ) / 2 + lam / 2) * period = period / 2 + lam * period / 2 by ring]
      exact h2
    have hpos : 0 < lam * period / 2 := div_pos (mul_pos hl period_pos) (by norm_num)
    have hlt : lam * period / 2 < period / 2 := by
      have h := mul_lt_mul_of_pos_right (show lam < 1 by linarith) period_pos
      linarith
    have ht : t < period := lt_of_le_of_lt h2 (by linarith)
    have hp : sweepParam t = t / period := cvb_sweepParam_div h0 ht
    have hca : ¬ sweepParam t ≤ 1 / 2 := by rw [hp]; exact not_le.mpr hc1
    have hcb : sweepParam t ≤ 1 / 2 + lam / 2 := by rw [hp]; exact hc2
    simp only [sweepLoopChamfer]
    rw [if_neg hca, if_pos hcb, hp]
    rfl

/-- Zone 3: on `[period/2 + lam*period/2, period - lam*period/2]` the loop is the chord branch. -/
private lemma cvb_zone3 {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {lam sig t : ℝ}
    (hl : 0 < lam) (hl2 : lam < 1 / 2) (h0 : 0 ≤ t) (h1 : period / 2 + lam * period / 2 ≤ t)
    (h2 : t ≤ period - lam * period / 2) :
    sweepLoopChamfer r D lam sig t = cvb_loopChord r D lam sig t := by
  have hpos : 0 < lam * period / 2 := div_pos (mul_pos hl period_pos) (by norm_num)
  have hc23 : period / 2 + lam * period / 2 ≤ period - lam * period / 2 := by
    have h := mul_lt_mul_of_pos_right hl2 period_pos
    have h2 : (1:ℝ) / 2 * period = period / 2 := by ring
    linarith
  rcases eq_or_lt_of_le h1 with hb | hb
  · rw [← hb, cvb_zone2 D hl hl2 (by linarith [period_pos, hpos]) (by linarith [hpos]) le_rfl]
    exact cvb_agree2 D lam sig hl hl2
  · have hc1 : (1:ℝ) / 2 + lam / 2 < t / period := by
      rw [lt_div_iff₀ period_pos,
        show ((1:ℝ) / 2 + lam / 2) * period = period / 2 + lam * period / 2 by ring]
      exact hb
    have h31 : (1:ℝ) / 2 < 1 / 2 + lam / 2 := by linarith
    have hcl : 1 / 2 < t / period := lt_trans h31 hc1
    have hc3 : t / period ≤ 1 - lam / 2 := by
      rw [div_le_iff₀ period_pos,
        show ((1:ℝ) - lam / 2) * period = period - lam * period / 2 by ring]
      exact h2
    have hlt : lam * period / 2 < period / 2 := by
      have h := mul_lt_mul_of_pos_right (show lam < 1 by linarith) period_pos
      linarith
    have ht : t < period := lt_of_le_of_lt h2 (by linarith)
    have hp : sweepParam t = t / period := cvb_sweepParam_div h0 ht
    have hca : ¬ sweepParam t ≤ 1 / 2 := by rw [hp]; exact not_le.mpr hcl
    have hcb : ¬ sweepParam t ≤ 1 / 2 + lam / 2 := by rw [hp]; exact not_le.mpr hc1
    have hcc : sweepParam t ≤ 1 - lam / 2 := by rw [hp]; exact hc3
    simp only [sweepLoopChamfer]
    rw [if_neg hca, if_neg hcb, if_pos hcc, hp]
    rfl

/-- Zone 4: on `[period - lam*period/2, period]` the loop is the second chamfer. -/
private lemma cvb_zone4 {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {lam sig t : ℝ}
    (hl : 0 < lam) (hl2 : lam < 1 / 2) (h0 : 0 ≤ t) (h1 : period - lam * period / 2 ≤ t)
    (h2 : t ≤ period) :
    sweepLoopChamfer r D lam sig t = cvb_loopChamfer₂ r D lam sig t := by
  have hpos : 0 < lam * period / 2 := div_pos (mul_pos hl period_pos) (by norm_num)
  have hc23 : period / 2 + lam * period / 2 ≤ period - lam * period / 2 := by
    have h := mul_lt_mul_of_pos_right hl2 period_pos
    have h2 : (1:ℝ) / 2 * period = period / 2 := by ring
    linarith
  rcases eq_or_lt_of_le h2 with hb | hb
  · subst hb
    have hp : sweepParam period = 0 := by
      rw [sweepParam, div_self period_ne_zero, Int.floor_one]; norm_num
    have hc : sweepParam period ≤ 1 / 2 := by rw [hp]; norm_num
    simp only [sweepLoopChamfer]
    rw [if_pos hc, hp]
    have h1' : lam + (1 - 2 * lam) * (2 * 0) = lam := by ring
    rw [h1']
    exact cvb_agree4 D lam sig hl
  · rcases eq_or_lt_of_le h1 with hb1 | hb1
    · rw [← hb1, cvb_zone3 D hl hl2 (by linarith [period_pos, hpos]) hc23 le_rfl]
      exact cvb_agree3 D lam sig hl hl2
    · have hc3 : (1:ℝ) - lam / 2 < t / period := by
        rw [lt_div_iff₀ period_pos,
          show ((1:ℝ) - lam / 2) * period = period - lam * period / 2 by ring]
        exact hb1
      have hb' : (1:ℝ) / 2 + lam / 2 < 1 - lam / 2 := by linarith
      have hcb : (1:ℝ) / 2 + lam / 2 < t / period := lt_trans hb' hc3
      have hca : (1:ℝ) / 2 < t / period := lt_trans (by linarith) hc3
      have hp : sweepParam t = t / period := cvb_sweepParam_div h0 hb
      have hna : ¬ sweepParam t ≤ 1 / 2 := by rw [hp]; exact not_le.mpr hca
      have hnb : ¬ sweepParam t ≤ 1 / 2 + lam / 2 := by rw [hp]; exact not_le.mpr hcb
      have hnc : ¬ sweepParam t ≤ 1 - lam / 2 := by rw [hp]; exact not_le.mpr hc3
      simp only [sweepLoopChamfer]
      rw [if_neg hna, if_neg hnb, if_neg hnc, hp]
      rfl

/-! ### Lipschitz bounds for the four branches -/

/-- `tbR` is `taR` plus the width of the retained arc. -/
private lemma cvb_tbR_eq {d : BandArcData} (D : SweepData d) (sig : ℝ) :
    tbR D sig = taR D sig + sweepW' D sig := by
  simp only [sweepW']; ring

/-- The chord of the retained arc is at most `L * period` long. -/
private lemma cvb_chord_bound {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {sig L : ℝ}
    (hL : 0 ≤ L)
    (hlip : ∀ x s : ℝ, 0 ≤ s → s ≤ period → ‖r (x + s) - r x‖ ≤ L * min s (period - s))
    (h1 : 0 ≤ sweepW' D sig) (h2 : sweepW' D sig ≤ period) :
    ‖r (tbR D sig) - r (taR D sig)‖ ≤ L * period := by
  rw [cvb_tbR_eq]
  have h := hlip (taR D sig) (sweepW' D sig) h1 h2
  have hmin : min (sweepW' D sig) (period - sweepW' D sig) ≤ period :=
    le_trans (min_le_left _ _) h2
  exact le_trans h (mul_le_mul_of_nonneg_left hmin hL)

/-- The first chamfer vector is at most `2 * L * period` long. -/
private lemma cvb_d1_bound {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {sig L lam : ℝ}
    (hL : 0 ≤ L) (hl : 0 < lam) (hl2 : lam < 1 / 2)
    (hlip : ∀ x s : ℝ, 0 ≤ s → s ≤ period → ‖r (x + s) - r x‖ ≤ L * min s (period - s))
    (h1 : 0 ≤ sweepW' D sig) (h2 : sweepW' D sig ≤ period) :
    ‖sweepChord' r D sig (1 - lam) - sweepArc' r D sig (1 - lam)‖ ≤ 2 * L * period := by
  have hδ0 : 0 ≤ (1 - lam) * sweepW' D sig := mul_nonneg (by linarith) h1
  have hδ1 : (1 - lam) * sweepW' D sig ≤ period := by
    have := mul_le_of_le_one_left h1 (by linarith : (1:ℝ) - lam ≤ 1)
    linarith
  have hA : ‖r (taR D sig) - r (taR D sig + (1 - lam) * sweepW' D sig)‖ ≤ L * period := by
    have h := hlip (taR D sig) ((1 - lam) * sweepW' D sig) hδ0 hδ1
    have hmin : min ((1 - lam) * sweepW' D sig) (period - (1 - lam) * sweepW' D sig) ≤ period :=
      le_trans (min_le_left _ _) hδ1
    rw [norm_sub_rev]
    exact le_trans h (mul_le_mul_of_nonneg_left hmin hL)
  have hB : ‖r (tbR D sig) - r (taR D sig)‖ ≤ L * period :=
    cvb_chord_bound D hL hlip h1 h2
  have hid : sweepChord' r D sig (1 - lam) - sweepArc' r D sig (1 - lam)
      = ((1 - lam) • (r (tbR D sig) - r (taR D sig)))
        + (r (taR D sig) - r (taR D sig + (1 - lam) * sweepW' D sig)) := by
    simp only [sweepChord', sweepArc']; module
  rw [hid]
  have h1' : ‖(1 - lam) • (r (tbR D sig) - r (taR D sig))‖ ≤ L * period := by
    rw [norm_smul, Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ 1 - lam)]
    calc (1 - lam) * ‖r (tbR D sig) - r (taR D sig)‖
        ≤ 1 * ‖r (tbR D sig) - r (taR D sig)‖ :=
          mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ = ‖r (tbR D sig) - r (taR D sig)‖ := by ring
      _ ≤ L * period := hB
  calc ‖(1 - lam) • (r (tbR D sig) - r (taR D sig))
        + (r (taR D sig) - r (taR D sig + (1 - lam) * sweepW' D sig))‖
      ≤ ‖(1 - lam) • (r (tbR D sig) - r (taR D sig))‖
        + ‖r (taR D sig) - r (taR D sig + (1 - lam) * sweepW' D sig)‖ := norm_add_le _ _
    _ ≤ L * period + L * period := add_le_add h1' hA
    _ = 2 * L * period := by ring

/-- The second chamfer vector is at most `2 * L * period` long. -/
private lemma cvb_d2_bound {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {sig L lam : ℝ}
    (hL : 0 ≤ L) (hl : 0 < lam) (hl2 : lam < 1 / 2)
    (hlip : ∀ x s : ℝ, 0 ≤ s → s ≤ period → ‖r (x + s) - r x‖ ≤ L * min s (period - s))
    (h1 : 0 ≤ sweepW' D sig) (h2 : sweepW' D sig ≤ period) :
    ‖sweepArc' r D sig lam - sweepChord' r D sig lam‖ ≤ 2 * L * period := by
  have hσ0 : 0 ≤ lam * sweepW' D sig := mul_nonneg hl.le h1
  have hσ1 : lam * sweepW' D sig ≤ period := by
    have h3 : lam * sweepW' D sig ≤ lam * period := mul_le_mul_of_nonneg_left h2 hl.le
    have h4 : lam * period ≤ period := by
      have h5 : lam * period ≤ 1 * period :=
        mul_le_mul_of_nonneg_right (by linarith : lam ≤ 1) period_pos.le
      linarith
    linarith
  have hA : ‖r (taR D sig + lam * sweepW' D sig) - r (taR D sig)‖ ≤ L * period := by
    have h := hlip (taR D sig) (lam * sweepW' D sig) hσ0 hσ1
    have hmin : min (lam * sweepW' D sig) (period - lam * sweepW' D sig) ≤ period :=
      le_trans (min_le_left _ _) hσ1
    exact le_trans h (mul_le_mul_of_nonneg_left hmin hL)
  have hB : ‖lam • (r (tbR D sig) - r (taR D sig))‖ ≤ L * period := by
    have h := cvb_chord_bound D hL hlip h1 h2
    rw [norm_smul, Real.norm_of_nonneg hl.le]
    calc lam * ‖r (tbR D sig) - r (taR D sig)‖ ≤ 1 * ‖r (tbR D sig) - r (taR D sig)‖ :=
          mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ = ‖r (tbR D sig) - r (taR D sig)‖ := by ring
      _ ≤ L * period := h
  have hid : sweepArc' r D sig lam - sweepChord' r D sig lam
      = (r (taR D sig + lam * sweepW' D sig) - r (taR D sig))
        - lam • (r (tbR D sig) - r (taR D sig)) := by
    simp only [sweepChord', sweepArc']; module
  rw [hid]
  calc ‖(r (taR D sig + lam * sweepW' D sig) - r (taR D sig))
        - lam • (r (tbR D sig) - r (taR D sig))‖
      ≤ ‖r (taR D sig + lam * sweepW' D sig) - r (taR D sig)‖
        + ‖lam • (r (tbR D sig) - r (taR D sig))‖ := norm_sub_le _ _
    _ ≤ L * period + L * period := add_le_add hA hB
    _ = 2 * L * period := by ring

/-- Lipschitz constant `Λ` for the arc branch on `[0, period/2]`, from the Lipschitz property of
the knot. -/
private lemma cvb_lip_arc {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {lam sig Λ L : ℝ}
    (hl : 0 < lam) (hl2 : lam < 1 / 2) (hL : 0 ≤ L) (hΛ : 2 * L ≤ Λ)
    (hlip : ∀ x s : ℝ, 0 ≤ s → s ≤ period → ‖r (x + s) - r x‖ ≤ L * min s (period - s))
    (hw0 : 0 ≤ sweepW' D sig) (hw1 : sweepW' D sig ≤ period)
    {a b : ℝ} (ha0 : 0 ≤ a) (hb1 : b ≤ period / 2) (hab : a ≤ b) :
    ‖cvb_loopArc r D lam sig b - cvb_loopArc r D lam sig a‖ ≤ Λ * (b - a) := by
  have hq : 0 ≤ 2 * ((b - a) / period) := by
    have h : 0 ≤ (b - a) / period := div_nonneg (by linarith) period_pos.le
    linarith
  have hcoef1 : (1 - 2 * lam) * (2 * ((b - a) / period)) ≤ 2 * ((b - a) / period) := by
    have h1 : (1 - 2 * lam) * (2 * ((b - a) / period)) ≤ 1 * (2 * ((b - a) / period)) :=
      mul_le_mul_of_nonneg_right (by linarith : (1:ℝ) - 2 * lam ≤ 1) hq
    linarith
  have hcoef3 : (1 - 2 * lam) * (2 * ((b - a) / period)) * sweepW' D sig ≤ 2 * (b - a) := by
    have h2 : (1 - 2 * lam) * (2 * ((b - a) / period)) * sweepW' D sig
        ≤ (2 * ((b - a) / period)) * sweepW' D sig :=
      mul_le_mul_of_nonneg_right hcoef1 hw0
    have h3 : (2 * ((b - a) / period)) * sweepW' D sig ≤ (2 * ((b - a) / period)) * period :=
      mul_le_mul_of_nonneg_left hw1 hq
    have h4 : (2 * ((b - a) / period)) * period = 2 * (b - a) := by
      rw [mul_assoc, div_mul_cancel₀ _ period_ne_zero]
    linarith [h2, h3, h4.le, h4.ge]
  have hs0 : 0 ≤ (1 - 2 * lam) * (2 * ((b - a) / period)) * sweepW' D sig :=
    mul_nonneg (mul_nonneg (by linarith) hq) hw0
  have hs1 : (1 - 2 * lam) * (2 * ((b - a) / period)) * sweepW' D sig ≤ period := by
    have hba : b - a ≤ period / 2 := by linarith
    linarith [hcoef3]
  have hξ : lam + (1 - 2 * lam) * (2 * (b / period))
      = (lam + (1 - 2 * lam) * (2 * (a / period)))
        + (1 - 2 * lam) * (2 * ((b - a) / period)) := by
    field_simp [period_ne_zero]; ring
  have hbase := hlip (taR D sig + (lam + (1 - 2 * lam) * (2 * (a / period))) * sweepW' D sig)
    ((1 - 2 * lam) * (2 * ((b - a) / period)) * sweepW' D sig) hs0 hs1
  have hmin : min ((1 - 2 * lam) * (2 * ((b - a) / period)) * sweepW' D sig)
      (period - (1 - 2 * lam) * (2 * ((b - a) / period)) * sweepW' D sig) ≤ 2 * (b - a) :=
    le_trans (min_le_left _ _) hcoef3
  have harg : taR D sig + (lam + (1 - 2 * lam) * (2 * (b / period))) * sweepW' D sig
      = taR D sig + (lam + (1 - 2 * lam) * (2 * (a / period))) * sweepW' D sig
        + (1 - 2 * lam) * (2 * ((b - a) / period)) * sweepW' D sig := by
    rw [hξ]; ring
  have hgoal : ‖cvb_loopArc r D lam sig b - cvb_loopArc r D lam sig a‖
      = ‖r (taR D sig + (lam + (1 - 2 * lam) * (2 * (a / period))) * sweepW' D sig
          + (1 - 2 * lam) * (2 * ((b - a) / period)) * sweepW' D sig)
        - r (taR D sig + (lam + (1 - 2 * lam) * (2 * (a / period))) * sweepW' D sig)‖ := by
    simp only [cvb_loopArc, sweepArc']
    rw [harg]
  rw [hgoal]
  calc ‖r (taR D sig + (lam + (1 - 2 * lam) * (2 * (a / period))) * sweepW' D sig
        + (1 - 2 * lam) * (2 * ((b - a) / period)) * sweepW' D sig)
      - r (taR D sig + (lam + (1 - 2 * lam) * (2 * (a / period))) * sweepW' D sig)‖
      ≤ L * (2 * (b - a)) := le_trans hbase (mul_le_mul_of_nonneg_left hmin hL)
    _ = 2 * L * (b - a) := by ring
    _ ≤ Λ * (b - a) := mul_le_mul_of_nonneg_right hΛ (by linarith)

/-- Lipschitz constant `Λ ≥ 4*L/lam` for the first chamfer branch on
`[period/2, period/2 + lam*period/2]`. -/
private lemma cvb_lip_chamfer₁ {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lam sig Λ L : ℝ}
    (hl : 0 < lam) (hl2 : lam < 1 / 2) (hL : 0 ≤ L) (hΛ : 4 * L / lam ≤ Λ)
    (hlip : ∀ x s : ℝ, 0 ≤ s → s ≤ period → ‖r (x + s) - r x‖ ≤ L * min s (period - s))
    (hw0 : 0 ≤ sweepW' D sig) (hw1 : sweepW' D sig ≤ period)
    {a b : ℝ} (hab : a ≤ b) :
    ‖cvb_loopChamfer₁ r D lam sig b - cvb_loopChamfer₁ r D lam sig a‖ ≤ Λ * (b - a) := by
  have hD := cvb_d1_bound D hL hl hl2 hlip hw0 hw1
  have hgen : ∀ x y : ℝ,
      ((1 - x) • sweepArc' r D sig (1 - lam) + x • sweepChord' r D sig (1 - lam))
        - ((1 - y) • sweepArc' r D sig (1 - lam) + y • sweepChord' r D sig (1 - lam))
      = (x - y) • (sweepChord' r D sig (1 - lam) - sweepArc' r D sig (1 - lam)) := by
    intro x y; module
  have hα : (2 * (b / period) - 1) / lam - (2 * (a / period) - 1) / lam
      = 2 * (b - a) / (lam * period) := by
    field_simp [period_ne_zero, ne_of_gt hl]; ring
  have hid : cvb_loopChamfer₁ r D lam sig b - cvb_loopChamfer₁ r D lam sig a
      = (2 * (b - a) / (lam * period)) •
        (sweepChord' r D sig (1 - lam) - sweepArc' r D sig (1 - lam)) := by
    simp only [cvb_loopChamfer₁]
    rw [hgen, hα]
  have hcoef : 0 ≤ 2 * (b - a) / (lam * period) :=
    div_nonneg (by linarith) (le_of_lt (mul_pos hl period_pos))
  rw [hid, norm_smul, Real.norm_of_nonneg hcoef]
  calc (2 * (b - a) / (lam * period)) * ‖sweepChord' r D sig (1 - lam)
        - sweepArc' r D sig (1 - lam)‖
      ≤ (2 * (b - a) / (lam * period)) * (2 * L * period) :=
        mul_le_mul_of_nonneg_left hD hcoef
    _ = 4 * L / lam * (b - a) := by
        rw [div_mul_eq_mul_div]
        rw [show 2 * (b - a) * (2 * L * period) = (4 * L * (b - a)) * period by ring]
        rw [mul_div_mul_right _ _ period_ne_zero]
        ring
    _ ≤ Λ * (b - a) := mul_le_mul_of_nonneg_right hΛ (by linarith)

/-- Lipschitz constant `Λ ≥ 2*L` for the chord branch on
`[period/2 + lam*period/2, period - lam*period/2]`. -/
private lemma cvb_lip_chord {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lam sig Λ L : ℝ}
    (hl : 0 < lam) (hl2 : lam < 1 / 2) (hL : 0 ≤ L) (hΛ : 2 * L ≤ Λ)
    (hlip : ∀ x s : ℝ, 0 ≤ s → s ≤ period → ‖r (x + s) - r x‖ ≤ L * min s (period - s))
    (hw0 : 0 ≤ sweepW' D sig) (hw1 : sweepW' D sig ≤ period)
    {a b : ℝ} (hab : a ≤ b) :
    ‖cvb_loopChord r D lam sig b - cvb_loopChord r D lam sig a‖ ≤ Λ * (b - a) := by
  have hch := cvb_chord_bound D hL hlip hw0 hw1
  have hgen : ∀ x y : ℝ, sweepChord' r D sig x - sweepChord' r D sig y
      = (x - y) • (r (tbR D sig) - r (taR D sig)) := by
    intro x y; simp only [sweepChord']; module
  have hξ : (1 - lam) - (((b / period) - (1 / 2 + lam / 2)) / (1 / 2 - lam)) * (1 - 2 * lam)
      - ((1 - lam) - (((a / period) - (1 / 2 + lam / 2)) / (1 / 2 - lam)) * (1 - 2 * lam))
      = -(2 * (b - a) / period) := by
    have hc : (0:ℝ) < 1 / 2 - lam := by linarith
    rw [show ((1 - lam) - (((b / period) - (1 / 2 + lam / 2)) / (1 / 2 - lam)) * (1 - 2 * lam))
        - ((1 - lam) - (((a / period) - (1 / 2 + lam / 2)) / (1 / 2 - lam)) * (1 - 2 * lam))
        = -((((b / period) - (1 / 2 + lam / 2)) / (1 / 2 - lam)
            - ((a / period) - (1 / 2 + lam / 2)) / (1 / 2 - lam)) * (1 - 2 * lam)) by ring]
    rw [div_sub_div_same]
    rw [show (b / period - (1 / 2 + lam / 2)) - (a / period - (1 / 2 + lam / 2))
        = (b - a) / period by field_simp [period_ne_zero]; ring]
    rw [div_mul_eq_mul_div]
    rw [show (1 - 2 * lam) = 2 * (1 / 2 - lam) by ring]
    have h3 : (b - a) / period * (2 * (1 / 2 - lam)) / (1 / 2 - lam)
        = 2 * ((b - a) / period) := by
      rw [show (b - a) / period * (2 * (1 / 2 - lam)) = ((b - a) / period * 2) * (1 / 2 - lam)
        by ring]
      rw [mul_div_cancel_right₀ _ (ne_of_gt hc)]
      ring
    rw [h3]
    ring
  have hid : cvb_loopChord r D lam sig b - cvb_loopChord r D lam sig a
      = (-(2 * (b - a) / period)) • (r (tbR D sig) - r (taR D sig)) := by
    simp only [cvb_loopChord]
    rw [hgen, hξ]
  rw [hid, norm_smul]
  have hcoef : ‖-(2 * (b - a) / period)‖ = 2 * (b - a) / period := by
    rw [norm_neg, Real.norm_of_nonneg (div_nonneg (by linarith) period_pos.le)]
  rw [hcoef]
  calc (2 * (b - a) / period) * ‖r (tbR D sig) - r (taR D sig)‖
      ≤ (2 * (b - a) / period) * (L * period) :=
        mul_le_mul_of_nonneg_left hch (div_nonneg (by linarith) period_pos.le)
    _ = 2 * L * (b - a) := by
        rw [div_mul_eq_mul_div]
        rw [show 2 * (b - a) * (L * period) = (2 * L * (b - a)) * period by ring]
        rw [mul_div_cancel_right₀ _ period_ne_zero]
    _ ≤ Λ * (b - a) := mul_le_mul_of_nonneg_right hΛ (by linarith)

/-- Lipschitz constant `Λ ≥ 4*L/lam` for the second chamfer branch on
`[period - lam*period/2, period]`. -/
private lemma cvb_lip_chamfer₂ {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lam sig Λ L : ℝ}
    (hl : 0 < lam) (hl2 : lam < 1 / 2) (hL : 0 ≤ L) (hΛ : 4 * L / lam ≤ Λ)
    (hlip : ∀ x s : ℝ, 0 ≤ s → s ≤ period → ‖r (x + s) - r x‖ ≤ L * min s (period - s))
    (hw0 : 0 ≤ sweepW' D sig) (hw1 : sweepW' D sig ≤ period)
    {a b : ℝ} (hab : a ≤ b) :
    ‖cvb_loopChamfer₂ r D lam sig b - cvb_loopChamfer₂ r D lam sig a‖ ≤ Λ * (b - a) := by
  have hD := cvb_d2_bound D hL hl hl2 hlip hw0 hw1
  have hgen : ∀ x y : ℝ,
      ((1 - x) • sweepChord' r D sig lam + x • sweepArc' r D sig lam)
        - ((1 - y) • sweepChord' r D sig lam + y • sweepArc' r D sig lam)
      = (x - y) • (sweepArc' r D sig lam - sweepChord' r D sig lam) := by
    intro x y; module
  have hβ : ((b / period) - (1 - lam / 2)) / (lam / 2)
      - ((a / period) - (1 - lam / 2)) / (lam / 2)
      = 2 * (b - a) / (lam * period) := by
    field_simp [period_ne_zero, ne_of_gt hl]; ring
  have hid : cvb_loopChamfer₂ r D lam sig b - cvb_loopChamfer₂ r D lam sig a
      = (2 * (b - a) / (lam * period)) •
        (sweepArc' r D sig lam - sweepChord' r D sig lam) := by
    simp only [cvb_loopChamfer₂]
    rw [hgen, hβ]
  have hcoef : 0 ≤ 2 * (b - a) / (lam * period) :=
    div_nonneg (by linarith) (le_of_lt (mul_pos hl period_pos))
  rw [hid, norm_smul, Real.norm_of_nonneg hcoef]
  calc (2 * (b - a) / (lam * period)) * ‖sweepArc' r D sig lam
        - sweepChord' r D sig lam‖
      ≤ (2 * (b - a) / (lam * period)) * (2 * L * period) :=
        mul_le_mul_of_nonneg_left hD hcoef
    _ = 4 * L / lam * (b - a) := by
        rw [div_mul_eq_mul_div]
        rw [show 2 * (b - a) * (2 * L * period) = (4 * L * (b - a)) * period by ring]
        rw [mul_div_mul_right _ _ period_ne_zero]
        ring
    _ ≤ Λ * (b - a) := mul_le_mul_of_nonneg_right hΛ (by linarith)

/-- The chamfered loop is `Λ`-Lipschitz on one period, by chaining the four branch estimates at
the three corners of the profile. -/
private lemma cvb_lip_period {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lam sig Λ L : ℝ} (hl : 0 < lam) (hl2 : lam < 1 / 2) (hL : 0 ≤ L)
    (hΛ2 : 2 * L ≤ Λ) (hΛ4 : 4 * L / lam ≤ Λ)
    (hlip : ∀ x s : ℝ, 0 ≤ s → s ≤ period → ‖r (x + s) - r x‖ ≤ L * min s (period - s))
    (hw0 : 0 ≤ sweepW' D sig) (hw1 : sweepW' D sig ≤ period)
    {x y : ℝ} (hx0 : 0 ≤ x) (hxy : x ≤ y) (hy1 : y ≤ period) :
    ‖sweepLoopChamfer r D lam sig y - sweepLoopChamfer r D lam sig x‖ ≤ Λ * (y - x) := by
  have hΛ0 : 0 ≤ Λ := le_trans (mul_nonneg (by norm_num) hL) hΛ2
  have hpos : 0 < lam * period / 2 := div_pos (mul_pos hl period_pos) (by norm_num)
  -- the three corners
  have hc01 : (0:ℝ) ≤ period / 2 := by linarith [period_pos]
  have hc12 : period / 2 ≤ period / 2 + lam * period / 2 := by linarith [hpos]
  have hc23 : period / 2 + lam * period / 2 ≤ period - lam * period / 2 := by
    have h := mul_lt_mul_of_pos_right hl2 period_pos
    have h2 : (1:ℝ) / 2 * period = period / 2 := by ring
    linarith
  have hc34 : period - lam * period / 2 ≤ period := by linarith [hpos]
  -- the clamped points
  set a1 := min y (max x (period / 2)) with ha1
  set a2 := min y (max x (period / 2 + lam * period / 2)) with ha2
  set a3 := min y (max x (period - lam * period / 2)) with ha3
  have hx1 : x ≤ a1 := le_min hxy (le_max_left x _)
  have h12 : a1 ≤ a2 := by rw [ha1, ha2]; exact min_le_min le_rfl (max_le_max le_rfl hc12)
  have h23 : a2 ≤ a3 := by rw [ha2, ha3]; exact min_le_min le_rfl (max_le_max le_rfl hc23)
  have h3y : a3 ≤ y := min_le_left y _
  -- the zone identities
  have hz1 : ∀ t ∈ Set.Icc (0:ℝ) (period / 2),
      sweepLoopChamfer r D lam sig t = cvb_loopArc r D lam sig t :=
    fun t ht => cvb_zone1 D ht.1 ht.2
  have hz2 : ∀ t ∈ Set.Icc (period / 2) (period / 2 + lam * period / 2),
      sweepLoopChamfer r D lam sig t = cvb_loopChamfer₁ r D lam sig t :=
    fun t ht => cvb_zone2 D hl hl2 (le_trans hc01 ht.1) ht.1 ht.2
  have hz3 : ∀ t ∈ Set.Icc (period / 2 + lam * period / 2) (period - lam * period / 2),
      sweepLoopChamfer r D lam sig t = cvb_loopChord r D lam sig t :=
    fun t ht => cvb_zone3 D hl hl2 (le_trans hc01 (le_trans hc12 ht.1)) ht.1 ht.2
  have hz4 : ∀ t ∈ Set.Icc (period - lam * period / 2) period,
      sweepLoopChamfer r D lam sig t = cvb_loopChamfer₂ r D lam sig t :=
    fun t ht => cvb_zone4 D hl hl2 (le_trans hc01 (le_trans hc12 (le_trans hc23 ht.1))) ht.1 ht.2
  -- the four chain steps
  have step : ∀ (P : ℝ → Space) {c c' a b : ℝ}, 0 ≤ c → c ≤ c' → c' ≤ period →
      (∀ t ∈ Set.Icc c c', sweepLoopChamfer r D lam sig t = P t) →
      (∀ s ∈ Set.Icc c c', ∀ t ∈ Set.Icc c c', s ≤ t → ‖P t - P s‖ ≤ Λ * (t - s)) →
      a = min y (max x c) → b = min y (max x c') → ‖sweepLoopChamfer r D lam sig b
        - sweepLoopChamfer r D lam sig a‖ ≤ Λ * (b - a) := by
    intro P c c' a b hc0 hcc' hc'p hF hP ha hb
    have hab : a ≤ b := by
      rw [ha, hb]; exact min_le_min le_rfl (max_le_max le_rfl hcc')
    rcases eq_or_lt_of_le hab with hdeg | hlt
    · rw [← hdeg, sub_self, norm_zero]
      exact mul_nonneg hΛ0 (by rw [hdeg]; simp)
    · have ha_ge : c ≤ a := by
        rw [ha]
        rcases le_total c y with hcy | hyc
        · exact le_min hcy (le_max_right x c)
        · have ha' : min y (max x c) = y := by
            rw [max_eq_right (le_trans hxy hyc), min_eq_left hyc]
          have hb' : min y (max x c') = y := by
            rw [max_eq_right (le_trans (le_trans hxy hyc) hcc'), min_eq_left (le_trans hyc hcc')]
          rw [ha, hb, ha', hb'] at hlt
          exact absurd hlt (lt_irrefl y)
      have hb_le : b ≤ c' := by
        rw [hb]
        rcases le_total c' x with hxc' | hc'x
        · have ha' : min y (max x c) = x := by
            rw [max_eq_left (le_trans hcc' hxc'), min_eq_right hxy]
          have hb' : min y (max x c') = x := by
            rw [max_eq_left hxc', min_eq_right hxy]
          rw [ha, hb, ha', hb'] at hlt
          exact absurd hlt (lt_irrefl x)
        · rw [max_eq_right hc'x]
          exact min_le_right y c'
      have ha' : a ∈ Set.Icc c c' := ⟨ha_ge, le_trans hlt.le hb_le⟩
      have hb' : b ∈ Set.Icc c c' := ⟨le_trans ha_ge hlt.le, hb_le⟩
      rw [hF a ha', hF b hb']
      exact hP a ha' b hb' hlt.le
  have ex0 : x = min y (max x (0:ℝ)) := by
    rw [max_eq_left hx0, min_eq_right hxy]
  have ey : y = min y (max x period) := by
    rw [max_eq_right (le_trans hxy hy1), min_eq_left hy1]
  have e1 := step (cvb_loopArc r D lam sig) (c := 0) (c' := period / 2)
    le_rfl hc01 (by linarith [period_pos]) hz1
    (fun s hs t ht hst => cvb_lip_arc D hl hl2 hL hΛ2 hlip hw0 hw1 hs.1 ht.2 hst)
    ex0 ha1
  have e2 := step (cvb_loopChamfer₁ r D lam sig) (c := period / 2)
    (c' := period / 2 + lam * period / 2) hc01 hc12 (by linarith [hpos]) hz2
    (fun s hs t ht hst => cvb_lip_chamfer₁ D hl hl2 hL hΛ4 hlip hw0 hw1 hst)
    ha1 ha2
  have e3 := step (cvb_loopChord r D lam sig) (c := period / 2 + lam * period / 2)
    (c' := period - lam * period / 2) (by linarith [hpos]) hc23 hc34 hz3
    (fun s hs t ht hst => cvb_lip_chord D hl hl2 hL hΛ2 hlip hw0 hw1 hst)
    ha2 ha3
  have e4 := step (cvb_loopChamfer₂ r D lam sig) (c := period - lam * period / 2)
    (c' := period) (by linarith [hpos]) hc34 le_rfl hz4
    (fun s hs t ht hst => cvb_lip_chamfer₂ D hl hl2 hL hΛ4 hlip hw0 hw1 hst)
    ha3 ey
  have htel : ‖sweepLoopChamfer r D lam sig y - sweepLoopChamfer r D lam sig x‖
      ≤ ‖sweepLoopChamfer r D lam sig y - sweepLoopChamfer r D lam sig a3‖
        + (‖sweepLoopChamfer r D lam sig a3 - sweepLoopChamfer r D lam sig a2‖
          + (‖sweepLoopChamfer r D lam sig a2 - sweepLoopChamfer r D lam sig a1‖
            + ‖sweepLoopChamfer r D lam sig a1 - sweepLoopChamfer r D lam sig x‖)) := by
    have h5 : ‖sweepLoopChamfer r D lam sig y - sweepLoopChamfer r D lam sig x‖
        ≤ ‖sweepLoopChamfer r D lam sig y - sweepLoopChamfer r D lam sig a3‖
          + ‖sweepLoopChamfer r D lam sig a3 - sweepLoopChamfer r D lam sig x‖ := by
      calc ‖sweepLoopChamfer r D lam sig y - sweepLoopChamfer r D lam sig x‖
          = ‖(sweepLoopChamfer r D lam sig y - sweepLoopChamfer r D lam sig a3)
              + (sweepLoopChamfer r D lam sig a3 - sweepLoopChamfer r D lam sig x)‖ := by
            congr 1; abel
        _ ≤ _ := norm_add_le _ _
    have h6 : ‖sweepLoopChamfer r D lam sig a3 - sweepLoopChamfer r D lam sig x‖
        ≤ ‖sweepLoopChamfer r D lam sig a3 - sweepLoopChamfer r D lam sig a2‖
          + ‖sweepLoopChamfer r D lam sig a2 - sweepLoopChamfer r D lam sig x‖ := by
      calc ‖sweepLoopChamfer r D lam sig a3 - sweepLoopChamfer r D lam sig x‖
          = ‖(sweepLoopChamfer r D lam sig a3 - sweepLoopChamfer r D lam sig a2)
              + (sweepLoopChamfer r D lam sig a2 - sweepLoopChamfer r D lam sig x)‖ := by
            congr 1; abel
        _ ≤ _ := norm_add_le _ _
    have h7 : ‖sweepLoopChamfer r D lam sig a2 - sweepLoopChamfer r D lam sig x‖
        ≤ ‖sweepLoopChamfer r D lam sig a2 - sweepLoopChamfer r D lam sig a1‖
          + ‖sweepLoopChamfer r D lam sig a1 - sweepLoopChamfer r D lam sig x‖ := by
      calc ‖sweepLoopChamfer r D lam sig a2 - sweepLoopChamfer r D lam sig x‖
          = ‖(sweepLoopChamfer r D lam sig a2 - sweepLoopChamfer r D lam sig a1)
              + (sweepLoopChamfer r D lam sig a1 - sweepLoopChamfer r D lam sig x)‖ := by
            congr 1; abel
        _ ≤ _ := norm_add_le _ _
    calc ‖sweepLoopChamfer r D lam sig y - sweepLoopChamfer r D lam sig x‖
        ≤ ‖sweepLoopChamfer r D lam sig y - sweepLoopChamfer r D lam sig a3‖
          + ‖sweepLoopChamfer r D lam sig a3 - sweepLoopChamfer r D lam sig x‖ := h5
      _ ≤ ‖sweepLoopChamfer r D lam sig y - sweepLoopChamfer r D lam sig a3‖
          + (‖sweepLoopChamfer r D lam sig a3 - sweepLoopChamfer r D lam sig a2‖
            + ‖sweepLoopChamfer r D lam sig a2 - sweepLoopChamfer r D lam sig x‖) :=
          add_le_add le_rfl h6
      _ ≤ _ := add_le_add le_rfl (add_le_add le_rfl h7)
  calc ‖sweepLoopChamfer r D lam sig y - sweepLoopChamfer r D lam sig x‖
      ≤ ‖sweepLoopChamfer r D lam sig y - sweepLoopChamfer r D lam sig a3‖
        + (‖sweepLoopChamfer r D lam sig a3 - sweepLoopChamfer r D lam sig a2‖
          + (‖sweepLoopChamfer r D lam sig a2 - sweepLoopChamfer r D lam sig a1‖
            + ‖sweepLoopChamfer r D lam sig a1 - sweepLoopChamfer r D lam sig x‖)) := htel
    _ ≤ Λ * (y - a3) + (Λ * (a3 - a2) + (Λ * (a2 - a1) + Λ * (a1 - x))) :=
        add_le_add e4 (add_le_add e3 (add_le_add e2 e1))
    _ = Λ * (y - x) := by ring

/-- Periodicity reduction: a function that is `Λ`-Lipschitz on one period is `Λ`-Lipschitz on the
whole line. -/
private lemma cvb_lip_all {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {lam sig Λ : ℝ}
    (hΛ : 0 ≤ Λ) (hper : Function.Periodic (sweepLoopChamfer r D lam sig) period)
    (hint : ∀ x y : ℝ, 0 ≤ x → x ≤ y → y ≤ period →
      ‖sweepLoopChamfer r D lam sig y - sweepLoopChamfer r D lam sig x‖ ≤ Λ * (y - x)) :
    ∀ a b : ℝ, ‖sweepLoopChamfer r D lam sig a - sweepLoopChamfer r D lam sig b‖
      ≤ Λ * |a - b| := by
  have key : ∀ a b : ℝ, a ≤ b →
      ‖sweepLoopChamfer r D lam sig a - sweepLoopChamfer r D lam sig b‖ ≤ Λ * |a - b| := by
    intro a b hab
    set ka : ℤ := ⌊a / period⌋ with hka
    set kb : ℤ := ⌊b / period⌋ with hkb
    set a' := a - (ka : ℝ) * period with ha'
    set b' := b - (kb : ℝ) * period with hb'
    have ha0 : 0 ≤ a' := by
      have h : ((ka : ℤ) : ℝ) ≤ a / period := by rw [hka]; exact Int.floor_le _
      rw [ha']
      nlinarith [period_pos, div_mul_cancel₀ a period_ne_zero]
    have ha1 : a' ≤ period := by
      have h : a / period < ((ka : ℤ) : ℝ) + 1 := by rw [hka]; exact Int.lt_floor_add_one _
      rw [ha']
      nlinarith [period_pos, div_mul_cancel₀ a period_ne_zero]
    have hb0 : 0 ≤ b' := by
      have h : ((kb : ℤ) : ℝ) ≤ b / period := by rw [hkb]; exact Int.floor_le _
      rw [hb']
      nlinarith [period_pos, div_mul_cancel₀ b period_ne_zero]
    have hb1 : b' ≤ period := by
      have h : b / period < ((kb : ℤ) : ℝ) + 1 := by rw [hkb]; exact Int.lt_floor_add_one _
      rw [hb']
      nlinarith [period_pos, div_mul_cancel₀ b period_ne_zero]
    have hFa : sweepLoopChamfer r D lam sig a' = sweepLoopChamfer r D lam sig a :=
      hper.sub_int_mul_eq ka
    have hFb : sweepLoopChamfer r D lam sig b' = sweepLoopChamfer r D lam sig b :=
      hper.sub_int_mul_eq kb
    have hswap : ‖sweepLoopChamfer r D lam sig a - sweepLoopChamfer r D lam sig b‖
        = ‖sweepLoopChamfer r D lam sig b' - sweepLoopChamfer r D lam sig a'‖ := by
      rw [← hFa, ← hFb, norm_sub_rev]
    have hgap : (b - a) - (b' - a') = ((kb : ℝ) - ka) * period := by
      rw [ha', hb']; ring
    rcases lt_trichotomy ka kb with hlt | heq | hgt
    · -- `ka < kb`
      have hkab : ((kb : ℝ) - ka) ≥ 1 := by
        have h1 : ka + 1 ≤ kb := by omega
        have h2 : ((ka + 1 : ℤ) : ℝ) ≤ (kb : ℝ) := by exact_mod_cast h1
        push_cast at h2
        linarith
      have hbig : b' - a' ≤ b - a := by
        have h1 : (b - a) - (b' - a') ≥ period := by
          rw [hgap]
          nlinarith [hkab, period_pos]
        linarith
      rcases le_total a' b' with hle | hge
      · rw [hswap, abs_sub_comm, abs_of_nonneg (by linarith : (0:ℝ) ≤ b - a)]
        exact le_trans (hint a' b' ha0 hle hb1) (mul_le_mul_of_nonneg_left hbig hΛ)
      · rw [hswap, abs_sub_comm, abs_of_nonneg (by linarith : (0:ℝ) ≤ b - a)]
        have h1 := hint a' period ha0 ha1 le_rfl
        have h2 := hint 0 b' le_rfl hb0 hb1
        have hFp : sweepLoopChamfer r D lam sig period = sweepLoopChamfer r D lam sig 0 := by
          simpa using hper 0
        have hsplit : ‖sweepLoopChamfer r D lam sig b' - sweepLoopChamfer r D lam sig a'‖
            ≤ Λ * (period - a') + Λ * b' := by
          have ht : ‖sweepLoopChamfer r D lam sig b' - sweepLoopChamfer r D lam sig a'‖
              ≤ ‖sweepLoopChamfer r D lam sig b' - sweepLoopChamfer r D lam sig 0‖
                + ‖sweepLoopChamfer r D lam sig 0 - sweepLoopChamfer r D lam sig a'‖ := by
            calc ‖sweepLoopChamfer r D lam sig b' - sweepLoopChamfer r D lam sig a'‖
                = ‖(sweepLoopChamfer r D lam sig b' - sweepLoopChamfer r D lam sig 0)
                    + (sweepLoopChamfer r D lam sig 0
                      - sweepLoopChamfer r D lam sig a')‖ := by congr 1; abel
              _ ≤ _ := norm_add_le _ _
          have h2' : ‖sweepLoopChamfer r D lam sig b' - sweepLoopChamfer r D lam sig 0‖
              ≤ Λ * b' := by
            simpa using h2
          have h1' : ‖sweepLoopChamfer r D lam sig 0 - sweepLoopChamfer r D lam sig a'‖
              ≤ Λ * (period - a') := by
            simpa [hFp] using h1
          linarith [ht, h1', h2']
        have hsum : Λ * (period - a') + Λ * b' ≤ Λ * (b - a) := by
          have hmul : ((kb : ℝ) - ka) * period ≥ 1 * period :=
            mul_le_mul_of_nonneg_right hkab period_pos.le
          have h1 : (period - a') + b' ≤ b - a := by linarith [hgap, hmul]
          calc Λ * (period - a') + Λ * b' = Λ * ((period - a') + b') := by ring
            _ ≤ Λ * (b - a) := mul_le_mul_of_nonneg_left h1 hΛ
        linarith [hsplit, hsum]
    · -- `ka = kb`
      have hdiff : b' - a' = b - a := by
        have h' : ((kb : ℤ) : ℝ) = (ka : ℝ) := by exact_mod_cast heq.symm
        have h : ((kb : ℝ) - ka) * period = 0 := by
          rw [show (kb : ℝ) - (ka : ℝ) = 0 by linarith, zero_mul]
        linarith [hgap, h]
      have hle : a' ≤ b' := by linarith [hdiff, hab]
      rw [hswap, abs_sub_comm, abs_of_nonneg (by linarith : (0:ℝ) ≤ b - a), ← hdiff]
      exact hint a' b' ha0 hle hb1
    · -- `ka > kb` is impossible
      have h1 : kb + 1 ≤ ka := by omega
      have h2 : ((kb + 1 : ℤ) : ℝ) ≤ (ka : ℝ) := by exact_mod_cast h1
      push_cast at h2
      have hcontr : b < a := by
        have h3 : (ka : ℝ) * period ≤ a := by linarith [ha0, ha']
        have h4 : b < ((kb : ℝ) + 1) * period := by
          have h5 : b / period < (kb : ℝ) + 1 := by rw [hkb]; exact Int.lt_floor_add_one _
          have h5' : b / period * period < ((kb : ℝ) + 1) * period :=
            mul_lt_mul_of_pos_right h5 period_pos
          rw [div_mul_cancel₀ _ period_ne_zero] at h5'
          linarith [h5']
        have h7 : (((kb : ℝ) + 1) * period) ≤ (ka : ℝ) * period :=
          mul_le_mul_of_nonneg_right h2 period_pos.le
        exact lt_of_lt_of_le (lt_of_lt_of_le h4 h7) h3
      exact absurd hab (not_le.mpr hcontr)
  intro a b
  rcases le_total a b with hab | hba
  · exact key a b hab
  · have h := key b a hba
    rw [abs_sub_comm, norm_sub_rev] at h
    exact h

/-- **Quantitative data of a smooth knot.** -/
private theorem cvb_knot_quantitative {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ∃ L κ m : ℝ, 1 ≤ L ∧ 0 < κ ∧ 0 < m ∧ m ≤ L ∧
      (∀ x : ℝ, ‖velocity r x‖ ≤ L) ∧
      (∀ x : ℝ, m ≤ ‖velocity r x‖) ∧
      (∀ x s : ℝ, 0 ≤ s → s ≤ period → ‖r (x + s) - r x‖ ≤ L * min s (period - s)) ∧
      (∀ x s : ℝ, 0 ≤ s → s ≤ period / 2 → κ * s ≤ ‖r (x + s) - r x‖) ∧
      (∀ x s : ℝ, period / 2 ≤ s → s ≤ period → κ * (period - s) ≤ ‖r (x + s) - r x‖) := by
  have hvcont : Continuous (velocity r) := hr.smooth.continuous_deriv le_top
  have hvper : Function.Periodic (velocity r) period := cvb_periodic_velocity hr
  obtain ⟨L₀, hL₀⟩ := cvb_exists_norm_bound_of_periodic hvcont hvper
  obtain ⟨m, hmpos, hm⟩ := cvb_exists_norm_lower_of_periodic hvcont hvper (fun x => hr.regular x)
  have h2per : Function.Periodic (deriv (velocity r)) period := cvb_periodic_deriv hvper
  obtain ⟨C₀, hC₀⟩ := cvb_exists_norm_bound_of_periodic (cvb_continuous_deriv2 hr) h2per
  set L : ℝ := max 1 L₀ with hLdef
  set C : ℝ := max 1 C₀ with hCdef
  have hL1 : 1 ≤ L := le_max_left _ _
  have hC1 : 0 < C := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hvelL : ∀ x, ‖velocity r x‖ ≤ L := fun x => le_trans (hL₀ x) (le_max_right _ _)
  have haccC : ∀ x, ‖deriv (velocity r) x‖ ≤ C := fun x => le_trans (hC₀ x) (le_max_right _ _)
  have hchord : ∀ x y, ‖r y - r x‖ ≤ L * |y - x| := fun x y => cvb_chord_lipschitz hr hvelL x y
  have hsmall : ∀ x s : ℝ, 0 ≤ s → s ≤ m / (2 * C) → (m / 2) * s ≤ ‖r (x + s) - r x‖ :=
    cvb_chord_small hr hmpos hC1 hm haccC
  set δ : ℝ := min (period / 2) (m / (2 * C)) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith [period_pos]) (div_pos hmpos (by linarith))
  have hδ2 : δ ≤ period / 2 := min_le_left _ _
  have hδm : δ ≤ m / (2 * C) := min_le_right _ _
  obtain ⟨κ₁, hκ₁pos, hκ₁⟩ := cvb_chord_medium hr hδpos hδ2
  set κ : ℝ := min (m / 2) (2 * κ₁ / period) with hκdef
  have hκpos : 0 < κ := lt_min (by linarith) (div_pos (by linarith) period_pos)
  have hκm : κ ≤ m / 2 := min_le_left _ _
  have hκκ₁ : κ * (period / 2) ≤ κ₁ := by
    have h1 : κ ≤ 2 * κ₁ / period := min_le_right _ _
    rw [le_div_iff₀ period_pos] at h1
    linarith
  have hshort : ∀ x s : ℝ, 0 ≤ s → s ≤ period / 2 → κ * s ≤ ‖r (x + s) - r x‖ := by
    intro x s hs0 hs2
    rcases le_total s δ with hsδ | hsδ
    · calc κ * s ≤ (m / 2) * s := by nlinarith [hκm, hs0]
        _ ≤ ‖r (x + s) - r x‖ := hsmall x s hs0 (le_trans hsδ hδm)
    · calc κ * s ≤ κ * (period / 2) := by nlinarith [hκpos.le, hs2]
        _ ≤ κ₁ := hκκ₁
        _ ≤ ‖r (x + s) - r x‖ := hκ₁ x s hsδ hs2
  refine ⟨L, κ, m, hL1, hκpos, hmpos, le_trans (hm 0) (hvelL 0), hvelL, hm, ?_, hshort, ?_⟩
  · intro x s hs0 hs
    have hs' : 0 ≤ period - s := by linarith
    have hper : r (x + s) = r (x - (period - s)) := by
      have h := hr.periodic (x - (period - s))
      rw [← h]; congr 1; ring
    have h1 : ‖r (x + s) - r x‖ ≤ L * s := by
      have := hchord x (x + s)
      rwa [add_sub_cancel_left, abs_of_nonneg hs0] at this
    have h2 : ‖r (x + s) - r x‖ ≤ L * (period - s) := by
      rw [hper]
      have hz : (x - (period - s)) - x = -(period - s) := by ring
      have := hchord x (x - (period - s))
      rwa [hz, abs_neg, abs_of_nonneg hs'] at this
    rw [mul_min_of_nonneg s (period - s) (by linarith : (0:ℝ) ≤ L)]
    exact le_min h1 h2
  · intro x s hs1 hs2
    have hs' : 0 ≤ period - s := by linarith
    have hs'2 : period - s ≤ period / 2 := by linarith
    have hper : r (x + s) = r (x - (period - s)) := by
      have h := hr.periodic (x - (period - s))
      rw [← h]; congr 1; ring
    rw [hper]
    have h2 : (x - (period - s)) + (period - s) = x := by ring
    have := hshort (x - (period - s)) (period - s) hs' hs'2
    rw [h2, norm_sub_rev] at this
    exact this

theorem chamferVel_bounds {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d) :
    ∃ θ θΛ : ℝ, 0 < θ ∧ 0 < θΛ ∧
      ∀ (lam siglo sighi : ℝ), 0 < lam → lam < 1 / 2 → 0 < siglo → siglo ≤ sighi → sighi < 1 →
        (∀ sig ∈ Set.Icc siglo sighi,
            LeanEval.KnotTheory.Quadrisecant.period - Work.Drive.sweepW' D sig ≤ θ * lam) →
        ∃ Λ c₀ : ℝ, 0 < c₀ ∧ 0 < Λ ∧ Λ ≤ θΛ / lam ∧
          (∀ sig ∈ Set.Icc siglo sighi, ∀ t : ℝ, ‖Work.Drive.chamferVel r D lam sig t‖ ≤ Λ) ∧
          (∀ sig ∈ Set.Icc siglo sighi, ∀ a b : ℝ,
            ‖Work.Drive.sweepLoopChamfer r D lam sig a - Work.Drive.sweepLoopChamfer r D lam sig b‖
              ≤ Λ * |a - b|) ∧
          (∀ sig ∈ Set.Icc siglo sighi, ∀ t : ℝ,
            c₀ ≤ ‖Work.Drive.chamferVel r D lam sig t‖) := by
  obtain ⟨L, κ, m, hL1, hκ, hm, hmL, hvelL, hvelm, hlip, hsep1, hsep2⟩ := cvb_knot_quantitative hr
  have hL0 : 0 ≤ L := le_trans zero_le_one hL1
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  have hsep : ∀ x s : ℝ, 0 ≤ s → s ≤ period → κ * min s (period - s) ≤ ‖r (x + s) - r x‖ := by
    intro x s hs0 hs
    rcases le_total s (period / 2) with h | h
    · rw [min_eq_left (by linarith)]
      exact hsep1 x s hs0 h
    · rw [min_eq_right (by linarith)]
      exact hsep2 x s h hs
  set θ : ℝ := min period (κ * period / (4 * L)) with hθdef
  have hθpos : 0 < θ := lt_min period_pos (div_pos (mul_pos hκ period_pos) (by linarith))
  have hθp : θ ≤ period := min_le_left _ _
  have hθκ : θ ≤ κ * period / (4 * L) := min_le_right _ _
  set θΛ : ℝ := 6 * L with hθΛdef
  have hθΛpos : 0 < θΛ := by rw [hθΛdef]; linarith
  refine ⟨θ, θΛ, hθpos, hθΛpos, ?_⟩
  intro lam siglo sighi hlam hlam2 hslo hsle hshi hwidth
  have hwint : ∀ sig ∈ Set.Icc siglo sighi, 0 < sweepW' D sig ∧ sweepW' D sig < period :=
    fun sig hsig => cvb_sweepW'_pos_lt D (lt_of_lt_of_le hslo hsig.1) (lt_of_le_of_lt hsig.2 hshi)
  have hcont : Continuous (fun sig : ℝ => period - sweepW' D sig) := by
    have h1 : Continuous (sweepW' D) :=
      ((D.cont_tb.comp cvb_clampI_continuous).sub (D.cont_ta.comp cvb_clampI_continuous))
    exact continuous_const.sub h1
  obtain ⟨sig₀, hsig₀, hmin₀⟩ := isCompact_Icc.exists_isMinOn
    ⟨siglo, ⟨le_rfl, hsle⟩⟩ hcont.continuousOn
  have he₀pos : 0 < period - sweepW' D sig₀ := by
    have := (hwint sig₀ hsig₀).2
    linarith
  set e₀ : ℝ := period - sweepW' D sig₀ with he₀def
  set Λ : ℝ := 6 * L / lam with hΛdef
  have hΛpos : 0 < Λ := by rw [hΛdef]; exact div_pos (mul_pos (by norm_num) hLpos) hlam
  set c₀ : ℝ := min ((1 - 2 * lam) * m) (min ((2 / period) * κ * e₀) (κ / 2)) with hc₀def
  have hc₀pos : 0 < c₀ := by
    rw [hc₀def]
    refine lt_min ?_ ?_
    · exact mul_pos (by linarith [hlam2] : (0:ℝ) < 1 - 2 * lam) hm
    · refine lt_min ?_ ?_
      · exact mul_pos (mul_pos (div_pos (by norm_num : (0:ℝ) < 2) period_pos) hκ) he₀pos
      · exact div_pos hκ (by norm_num)
  have hΛθΛ : Λ ≤ θΛ / lam := by
    rw [hΛdef, hθΛdef]
  have hbounds : ∀ sig ∈ Set.Icc siglo sighi, ∀ t : ℝ,
      ‖chamferVel r D lam sig t‖ ≤ Λ ∧ c₀ ≤ ‖chamferVel r D lam sig t‖ := by
    intro sig hsig t
    obtain ⟨hwpos, hwlt⟩ := hwint sig hsig
    have hw0 : 0 ≤ sweepW' D sig := le_of_lt hwpos
    have hw1 : sweepW' D sig ≤ period := le_of_lt hwlt
    have hwd : period - sweepW' D sig ≤ θ * lam := hwidth sig hsig
    have he : e₀ ≤ period - sweepW' D sig := by
      rw [he₀def]
      exact hmin₀ hsig
    have hθlam : θ * lam < period / 2 := by
      have h1 : θ * lam ≤ period * lam := mul_le_mul_of_nonneg_right hθp hlam.le
      have h2 : period * lam < period * (1 / 2) := mul_lt_mul_of_pos_left hlam2 period_pos
      linarith
    have hwge : period / 2 ≤ sweepW' D sig := by linarith
    have hA0 : (0:ℝ) ≤ 1 - 2 * lam := by linarith
    have hp0 : (0:ℝ) ≤ 2 / period := div_nonneg (by norm_num : (0:ℝ) ≤ 2) period_pos.le
    have hB0 : 0 ≤ (1 - 2 * lam) * (2 / period) := mul_nonneg hA0 hp0
    have hl0 : (0:ℝ) ≤ lam * period := mul_nonneg hlam.le period_pos.le
    have hlm0 : (0:ℝ) ≤ lam * period * (1 / 4) := by positivity
    have hD1 := cvb_d1_bound D hL0 hlam hlam2 hlip hw0 hw1
    have hD2 := cvb_d2_bound D hL0 hlam hlam2 hlip hw0 hw1
    have hDlow := cvb_chamferDiff_lower hr D hLpos hκ hlam hlam2 hsle hslo hshi hθp hθκ
      hlip hsep (fun sig' hsig' => hwidth sig' hsig')
    have hch := cvb_chord_bound D hL0 hlip hw0 hw1
    have hκp0 : (0:ℝ) ≤ κ * period := mul_nonneg hκ.le period_pos.le
    -- the four scalar identities
    have hsc2 : (2 / lam) * (1 / period) = 2 / (lam * period) := by
      field_simp [ne_of_gt hlam, period_ne_zero] <;> ring_nf
    have hsc3 : -((1 - 2 * lam) / ((1 / 2 - lam) * period)) = -(2 / period) := by
      have hc : (0:ℝ) < 1 / 2 - lam := by linarith
      congr 1
      rw [show (1:ℝ) - 2 * lam = 2 * (1 / 2 - lam) by ring]
      rw [mul_comm (1 / 2 - lam) period]
      exact mul_div_mul_right (2 : ℝ) period (ne_of_gt hc)
    -- upper bounds
    have hArcU : ∀ t : ℝ, ‖chamferVelArc r D lam sig t‖ ≤ Λ := by
      intro t
      have hf : (0:ℝ) ≤ 2 / (lam * period) := div_nonneg (by norm_num : (0:ℝ) ≤ 2)
        (mul_pos hlam period_pos).le
      have hcoef : ‖(((1 - 2 * lam) * (2 / period)) * sweepW' D sig)‖ ≤ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hB0 hw0)]
        have hA : (1 - 2 * lam) * (2 / period) ≤ 1 * (2 / period) :=
          mul_le_mul_of_nonneg_right (by linarith : (1:ℝ) - 2 * lam ≤ 1) hp0
        rw [one_mul] at hA
        calc (1 - 2 * lam) * (2 / period) * sweepW' D sig
            ≤ (2 / period) * sweepW' D sig := mul_le_mul_of_nonneg_right hA hw0
          _ ≤ (2 / period) * period := mul_le_mul_of_nonneg_left hw1 hp0
          _ = 2 := by rw [div_mul_cancel₀ _ period_ne_zero]
      have hkey : 2 * L ≤ 6 * L / lam := by
        rw [le_div_iff₀ hlam]
        nlinarith [hL0, hlam2]
      rw [chamferVelArc, norm_smul, hΛdef]
      exact le_trans (mul_le_mul hcoef (hvelL _) (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)) hkey
    have hC1U : ∀ t : ℝ, ‖chamferVelChamfer₁ r D lam sig t‖ ≤ Λ := by
      intro t
      have hf : (0:ℝ) ≤ 2 / (lam * period) := div_nonneg (by norm_num : (0:ℝ) ≤ 2)
        (mul_pos hlam period_pos).le
      have hkey : (2 / (lam * period)) * (2 * L * period) ≤ 6 * L / lam := by
        have h1 : (2 / (lam * period)) * (2 * L * period) = 4 * L / lam := by
          field_simp [ne_of_gt hlam, period_ne_zero] <;> ring_nf
        rw [h1]
        have h2 : 0 ≤ 4 * L / lam := div_nonneg (mul_nonneg (by norm_num) hL0) hlam.le
        have h3 : 6 * L / lam = 4 * L / lam + 2 * L / lam := by ring
        rw [h3]
        have h4 : 0 ≤ 2 * L / lam := div_nonneg (mul_nonneg (by norm_num) hL0) hlam.le
        linarith
      rw [chamferVelChamfer₁, hsc2, norm_smul, Real.norm_of_nonneg hf, hΛdef]
      exact le_trans (mul_le_mul_of_nonneg_left hD1 hf) hkey
    have hChU : ∀ t : ℝ, ‖chamferVelChord r D lam sig t‖ ≤ Λ := by
      intro t
      have hkey : (2 / period) * (L * period) ≤ 6 * L / lam := by
        have h1 : (2 / period) * (L * period) = 2 * L := by
          field_simp [period_ne_zero] <;> ring_nf
        rw [h1, le_div_iff₀ hlam]
        nlinarith [hL0, hlam2]
      rw [chamferVelChord, hsc3, norm_smul, norm_neg, Real.norm_of_nonneg hp0, hΛdef]
      exact le_trans (mul_le_mul_of_nonneg_left hch hp0) hkey
    have hC2U : ∀ t : ℝ, ‖chamferVelChamfer₂ r D lam sig t‖ ≤ Λ := by
      intro t
      have hf : (0:ℝ) ≤ 2 / (lam * period) := div_nonneg (by norm_num : (0:ℝ) ≤ 2)
        (mul_pos hlam period_pos).le
      have hkey : (2 / (lam * period)) * (2 * L * period) ≤ 6 * L / lam := by
        have h1 : (2 / (lam * period)) * (2 * L * period) = 4 * L / lam := by
          field_simp [ne_of_gt hlam, period_ne_zero] <;> ring_nf
        rw [h1]
        have h3 : 6 * L / lam = 4 * L / lam + 2 * L / lam := by ring
        rw [h3]
        have h4 : 0 ≤ 2 * L / lam := div_nonneg (mul_nonneg (by norm_num) hL0) hlam.le
        linarith [h4]
      rw [chamferVelChamfer₂, hsc2, norm_smul, Real.norm_of_nonneg hf, hΛdef]
      exact le_trans (mul_le_mul_of_nonneg_left hD2 hf) hkey
    -- lower bounds
    have hArcL : ∀ t : ℝ, c₀ ≤ ‖chamferVelArc r D lam sig t‖ := by
      intro t
      rw [chamferVelArc, norm_smul, Real.norm_of_nonneg (mul_nonneg hB0 hw0)]
      have h6 : (1 - 2 * lam) * (2 / period) * (period / 2) = 1 - 2 * lam := by
        field_simp [period_ne_zero] <;> ring_nf
      have h5 : (1 - 2 * lam) ≤ (1 - 2 * lam) * (2 / period) * sweepW' D sig := by
        have h := mul_le_mul_of_nonneg_left hwge hB0
        rw [h6] at h
        exact h
      have h7 : (1 - 2 * lam) * m
          ≤ (1 - 2 * lam) * ‖velocity r (taR D sig + (lam + (1 - 2 * lam)
            * (2 * sweepParam t)) * sweepW' D sig)‖ :=
        mul_le_mul_of_nonneg_left (hvelm _) hA0
      have h8 : c₀ ≤ (1 - 2 * lam) * m := by
        rw [hc₀def]; exact min_le_left _ _
      calc c₀ ≤ (1 - 2 * lam) * m := h8
        _ ≤ (1 - 2 * lam) * ‖velocity r (taR D sig + (lam + (1 - 2 * lam)
            * (2 * sweepParam t)) * sweepW' D sig)‖ := h7
        _ ≤ (1 - 2 * lam) * (2 / period) * sweepW' D sig
            * ‖velocity r (taR D sig + (lam + (1 - 2 * lam)
              * (2 * sweepParam t)) * sweepW' D sig)‖ := by
            have h9 : 0 ≤ ‖velocity r (taR D sig + (lam + (1 - 2 * lam)
                * (2 * sweepParam t)) * sweepW' D sig)‖ := norm_nonneg _
            calc (1 - 2 * lam) * ‖velocity r (taR D sig + (lam + (1 - 2 * lam)
                  * (2 * sweepParam t)) * sweepW' D sig)‖
                ≤ ((1 - 2 * lam) * (2 / period) * sweepW' D sig)
                  * ‖velocity r (taR D sig + (lam + (1 - 2 * lam)
                    * (2 * sweepParam t)) * sweepW' D sig)‖ :=
                  mul_le_mul_of_nonneg_right h5 h9
              _ = _ := by ring
    have hC1L : ∀ t : ℝ, c₀ ≤ ‖chamferVelChamfer₁ r D lam sig t‖ := by
      intro t
      have hf : (0:ℝ) ≤ 2 / (lam * period) := div_nonneg (by norm_num : (0:ℝ) ≤ 2)
        (mul_pos hlam period_pos).le
      have h7 : κ / 2 ≥ c₀ := by
        rw [hc₀def]
        exact le_trans (min_le_right _ _) (min_le_right _ _)
      have h3 : 2 / (lam * period) * (lam * κ * period / 4) = κ / 2 := by
        field_simp [ne_of_gt hlam, period_ne_zero] <;> ring_nf
      rw [chamferVelChamfer₁, hsc2, norm_smul, Real.norm_of_nonneg hf]
      calc c₀ ≤ κ / 2 := h7
        _ = 2 / (lam * period) * (lam * κ * period / 4) := h3.symm
        _ ≤ 2 / (lam * period) * ‖sweepChord' r D sig (1 - lam)
              - sweepArc' r D sig (1 - lam)‖ :=
            mul_le_mul_of_nonneg_left (hDlow sig hsig).1 hf
    have hChL : ∀ t : ℝ, c₀ ≤ ‖chamferVelChord r D lam sig t‖ := by
      intro t
      have hepos : 0 < period - sweepW' D sig := by linarith
      have hper : r (taR D sig + sweepW' D sig)
          = r (taR D sig - (period - sweepW' D sig)) := by
        conv_lhs => rw [show taR D sig + sweepW' D sig
          = (taR D sig - (period - sweepW' D sig)) + period by ring]
        exact hr.periodic _
      have h2 : (taR D sig - (period - sweepW' D sig)) + (period - sweepW' D sig)
          = taR D sig := by ring
      have hsep' := hsep (taR D sig - (period - sweepW' D sig)) (period - sweepW' D sig)
        (by linarith) (by linarith)
      have hmin : min (period - sweepW' D sig) (period - (period - sweepW' D sig))
          = period - sweepW' D sig := by
        rw [show period - (period - sweepW' D sig) = sweepW' D sig by ring]
        exact min_eq_left (by linarith [hwge])
      rw [h2, hmin] at hsep'
      rw [← hper, norm_sub_rev] at hsep'
      have h10 : κ * e₀ ≤ ‖r (tbR D sig) - r (taR D sig)‖ := by
        rw [cvb_tbR_eq]
        exact le_trans (mul_le_mul_of_nonneg_left he hκ.le) hsep'
      have h8 : c₀ ≤ (2 / period) * (κ * e₀) := by
        rw [hc₀def]
        have h9 : (2 / period) * κ * e₀ = (2 / period) * (κ * e₀) := by ring
        rw [h9]
        exact le_trans (min_le_right _ _) (min_le_left _ _)
      rw [chamferVelChord, hsc3, norm_smul, norm_neg, Real.norm_of_nonneg hp0]
      exact le_trans h8 (mul_le_mul_of_nonneg_left h10 hp0)
    have hC2L : ∀ t : ℝ, c₀ ≤ ‖chamferVelChamfer₂ r D lam sig t‖ := by
      intro t
      have hf : (0:ℝ) ≤ 2 / (lam * period) := div_nonneg (by norm_num : (0:ℝ) ≤ 2)
        (mul_pos hlam period_pos).le
      have h7 : κ / 2 ≥ c₀ := by
        rw [hc₀def]
        exact le_trans (min_le_right _ _) (min_le_right _ _)
      have h3 : 2 / (lam * period) * (lam * κ * period / 4) = κ / 2 := by
        field_simp [ne_of_gt hlam, period_ne_zero] <;> ring_nf
      rw [chamferVelChamfer₂, hsc2, norm_smul, Real.norm_of_nonneg hf]
      calc c₀ ≤ κ / 2 := h7
        _ = 2 / (lam * period) * (lam * κ * period / 4) := h3.symm
        _ ≤ 2 / (lam * period) * ‖sweepArc' r D sig lam - sweepChord' r D sig lam‖ :=
            mul_le_mul_of_nonneg_left (hDlow sig hsig).2 hf
    rw [chamferVel_eq_ite]
    split_ifs
    · exact ⟨hArcU t, hArcL t⟩
    · exact ⟨hC1U t, hC1L t⟩
    · exact ⟨hChU t, hChL t⟩
    · exact ⟨hC2U t, hC2L t⟩
  have hlipclause : ∀ sig ∈ Set.Icc siglo sighi, ∀ a b : ℝ,
      ‖sweepLoopChamfer r D lam sig a - sweepLoopChamfer r D lam sig b‖ ≤ Λ * |a - b| := by
    intro sig hsig
    have hw0 : 0 ≤ sweepW' D sig := le_of_lt (hwint sig hsig).1
    have hw1 : sweepW' D sig ≤ period := le_of_lt (hwint sig hsig).2
    refine cvb_lip_all D ?_ (cvb_loopChamfer_add_period r D lam sig) ?_
    · rw [hΛdef]
      exact div_nonneg (mul_nonneg (by norm_num) hL0) hlam.le
    · intro x y hx0 hxy hy1
      refine cvb_lip_period D hlam hlam2 hL0 ?_ ?_ hlip hw0 hw1 hx0 hxy hy1
      · have h1 : 2 * L ≤ 6 * L / lam := by
          rw [le_div_iff₀ hlam]
          have h2 : (0:ℝ) ≤ 2 * L := by linarith
          have h3 : lam ≤ 3 := by linarith
          calc 2 * L * lam ≤ 2 * L * 3 := mul_le_mul_of_nonneg_left h3 h2
            _ ≤ 6 * L := by linarith
        rwa [hΛdef]
      · have h1 : 4 * L / lam ≤ 6 * L / lam := by
          rw [div_le_div_iff_of_pos_right hlam]
          linarith
        rwa [hΛdef]
  exact ⟨Λ, c₀, hc₀pos, hΛpos, hΛθΛ, fun sig hsig t => (hbounds sig hsig t).1, hlipclause,
    fun sig hsig t => (hbounds sig hsig t).2⟩

end Work.Drive
