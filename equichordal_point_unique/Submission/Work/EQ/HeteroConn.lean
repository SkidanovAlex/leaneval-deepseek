import Mathlib
import Submission.Work.EQ.Defs
import Submission.Work.EQ.hetero_gamma
import Submission.Work.EQ.hetero_box
import Submission.Work.EQ.arc_near_A1
import Submission.Work.EQ.germPt_basic
import Submission.Work.EQ.germPt_eqU
import Submission.Work.EQ.arc_eqU_maps
import Submission.Work.EQ.arc_iterate_tendsto_A1
import Submission.Work.EQ.eqU_arcInv
import Submission.Work.EQ.arcInv_mem_arc
import Submission.Work.EQ.arc_box_eq_germPt

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The heteroclinic connection of a symmetric normalised equichordal curve

Given the symmetric normalised curve `(ρ₁, ρ₂)` and a stable germ `h`, the heteroclinic
connection `Γ` is obtained by pulling the germ curve back along the inverse `arcInv` of the
half-map `eqU` on the open upper arc.  With `eqLam a` (written below as `eqLam a`) and a small
threshold `ε > 0`,

`Γ t := arcInv^[n] (germPt a h (eqLam a ^ n * t))`,  `n` least with `eqLam a ^ n * t < ε`.

The value is independent of the admissible `n` (`heteroGamma_indep`), satisfies the recursion
`eqU (Γ t) = Γ (eqLam a * t)` (`heteroGamma_step`), agrees with the germ near `0⁺`
(`heteroGamma_eq_germPt`), is continuous on `t > 0` (`heteroGamma_continuousOn`) and maps onto
the whole open upper arc (`heteroGamma_surj`). -/

namespace Work.EQ

open Complex Filter
open scoped Topology

noncomputable section

variable {a : ℝ}

/-! ### Elementary facts about points of the arc -/

/-- A point of the arc, with its `O₁`-radius. -/
theorem arcSet_norm_add_O2_eq {ρ₁ ρ₂ : ℝ → ℝ} (hC : NormEqCurve a ρ₁ ρ₂) {z : ℂ}
    (hz : z ∈ arcSet a ρ₁) :
    ∃ θ : ℝ, z = polarPt (-(a / 2)) (ρ₁ θ) θ ∧ ‖z + (((a / 2 : ℝ)) : ℂ)‖ = ρ₁ θ := by
  rw [arcSet, Set.mem_range] at hz
  obtain ⟨θ, hθ⟩ := hz
  change polarPt (-(a / 2)) (ρ₁ θ) θ = z at hθ
  refine ⟨θ, hθ.symm, ?_⟩
  rw [← hθ]
  have hb := (polarPt_basic (c := -(a / 2)) (r := ρ₁ θ) (θ := θ) (hC.2.2.1 θ)).2.2.1
  convert hb using 2
  push_cast
  ring

/-- Points of the arc are at distance `< 1` from `O₁ = -a/2`. -/
theorem arcSet_norm_add_O2_lt_one {ρ₁ ρ₂ : ℝ → ℝ} (hC : NormEqCurve a ρ₁ ρ₂) {z : ℂ}
    (hz : z ∈ arcSet a ρ₁) : ‖z + (((a / 2 : ℝ)) : ℂ)‖ < 1 := by
  obtain ⟨θ, -, hnorm⟩ := arcSet_norm_add_O2_eq hC hz
  rw [hnorm]
  have h1 := hC.2.2.2.2.1 θ
  have h2 := hC.2.2.1 (θ + Real.pi)
  linarith

/-- `z + a/2 ≠ 0` for points of the arc. -/
theorem arcSet_add_O2_ne_zero {ρ₁ ρ₂ : ℝ → ℝ} (hC : NormEqCurve a ρ₁ ρ₂) {z : ℂ}
    (hz : z ∈ arcSet a ρ₁) : z + (((a / 2 : ℝ)) : ℂ) ≠ 0 := by
  obtain ⟨θ, -, hnorm⟩ := arcSet_norm_add_O2_eq hC hz
  have hpos := hC.2.2.1 θ
  intro h
  rw [h, norm_zero] at hnorm
  linarith

/-- Points of the arc are at distance `< 1` from `O₂ = a/2`. -/
theorem arcSet_norm_sub_O2_lt_one {ρ₁ ρ₂ : ℝ → ℝ} (hC : NormEqCurve a ρ₁ ρ₂) {z : ℂ}
    (hz : z ∈ arcSet a ρ₁) : ‖z - (((a / 2 : ℝ)) : ℂ)‖ < 1 := by
  obtain ⟨θ, hzθ, -⟩ := arcSet_norm_add_O2_eq hC hz
  have hmem : polarPt (-(a / 2)) (ρ₁ θ) θ ∈ Set.range (fun φ => polarPt (a / 2) (ρ₂ φ) φ) := by
    rw [← hC.2.2.2.2.2.2]; exact ⟨θ, rfl⟩
  obtain ⟨φ, hφ⟩ := Set.mem_range.mp hmem
  change polarPt (a / 2) (ρ₂ φ) φ = polarPt (-(a / 2)) (ρ₁ θ) θ at hφ
  rw [hzθ, ← hφ, (polarPt_basic (c := a / 2) (r := ρ₂ φ) (θ := φ) (hC.2.2.2.1 φ)).2.2.1]
  have h1 := hC.2.2.2.2.2.1 φ
  have h2 := hC.2.2.2.1 (φ + Real.pi)
  linarith

theorem im_sub_O2_pos {z : ℂ} (hz : 0 < z.im) : 0 < (z - (((a / 2 : ℝ)) : ℂ)).im := by
  rw [Complex.sub_im, Complex.ofReal_im, sub_zero]; exact hz

/-- `arcInv (eqU z) = z` for `z` on the open upper arc. -/
theorem arcInv_eqU_of_mem_arc {ρ₁ ρ₂ : ℝ → ℝ} (hC : NormEqCurve a ρ₁ ρ₂) {z : ℂ}
    (hz : z ∈ arcSet a ρ₁) (hzim : 0 < z.im) : arcInv a (eqU a z) = z :=
  arcInv_eqU' (im_sub_O2_pos hzim) (arcSet_norm_sub_O2_lt_one hC hz)

/-- `arcInv` is continuous at every point of the arc. -/
theorem continuousAt_arcInv {ρ₁ ρ₂ : ℝ → ℝ} (hC : NormEqCurve a ρ₁ ρ₂) {z : ℂ}
    (hz : z ∈ arcSet a ρ₁) : ContinuousAt (arcInv a) z := by
  have hz0 : z + (((a / 2 : ℝ)) : ℂ) ≠ 0 := arcSet_add_O2_ne_zero hC hz
  have hnorm : ContinuousAt (fun w : ℂ => ‖w + (((a / 2 : ℝ)) : ℂ)‖) z :=
    continuous_norm.continuousAt.comp (continuousAt_id.add continuousAt_const)
  have hnormC : ContinuousAt (fun w : ℂ => ((‖w + (((a / 2 : ℝ)) : ℂ)‖ : ℝ) : ℂ)) z :=
    Complex.continuous_ofReal.continuousAt.comp hnorm
  have hz0C : ((‖z + (((a / 2 : ℝ)) : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by
    simp only [Complex.ofReal_ne_zero, norm_ne_zero_iff]; exact hz0
  have hnum : ContinuousAt (fun w : ℂ => ((1 - ‖w + (((a / 2 : ℝ)) : ℂ)‖ : ℝ) : ℂ)) z :=
    Complex.continuous_ofReal.continuousAt.comp (continuousAt_const.sub hnorm)
  have hdiv : ContinuousAt
      (fun w : ℂ => (w + (((a / 2 : ℝ)) : ℂ)) / ((‖w + (((a / 2 : ℝ)) : ℂ)‖ : ℝ) : ℂ)) z :=
    (continuousAt_id.add continuousAt_const).div hnormC hz0C
  have h : ContinuousAt (fun w : ℂ => (((a / 2 : ℝ)) : ℂ) +
      ((1 - ‖w + (((a / 2 : ℝ)) : ℂ)‖ : ℝ) : ℂ) *
        ((w + (((a / 2 : ℝ)) : ℂ)) / ((‖w + (((a / 2 : ℝ)) : ℂ)‖ : ℝ) : ℂ))) z :=
    (continuousAt_const (y := (((a / 2 : ℝ)) : ℂ))).add (hnum.mul hdiv)
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun w => ?_))
  simp only [arcInv, Complex.ofReal_sub, Complex.ofReal_one]

/-- `arcInvN a n` is continuous at every point of the arc. -/
theorem continuousAt_arcInvN {ρ₁ ρ₂ : ℝ → ℝ} (hC : NormEqCurve a ρ₁ ρ₂)
    (hs₁ : ∀ θ, ρ₁ (-θ) = ρ₁ θ) (hs₂ : ∀ θ, ρ₂ θ = ρ₁ (Real.pi - θ)) (n : ℕ) :
    ∀ z : ℂ, z ∈ arcSet a ρ₁ → 0 < z.im → ContinuousAt (arcInvN a n) z := by
  induction n with
  | zero => intro z hz hzim
            have h : arcInvN a 0 = (id : ℂ → ℂ) := by funext w; simp [arcInvN]
            rw [h]; exact continuousAt_id
  | succ n ih =>
      intro z hz hzim
      have h2 := arcInv_mem_arc hC hs₁ hs₂ hz hzim
      have hcomp : ContinuousAt ((fun w => arcInvN a n w) ∘ (arcInv a)) z :=
        (ih (arcInv a z) h2.1 h2.2).comp (continuousAt_arcInv hC hz)
      refine hcomp.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun w => ?_))
      simp only [Function.comp_apply, arcInvN, Function.iterate_succ_apply]

/-- The `n`-th iterate of `arcInv` maps the open upper arc into itself. -/
theorem arcInvN_mem_arc {ρ₁ ρ₂ : ℝ → ℝ} (hC : NormEqCurve a ρ₁ ρ₂)
    (hs₁ : ∀ θ, ρ₁ (-θ) = ρ₁ θ) (hs₂ : ∀ θ, ρ₂ θ = ρ₁ (Real.pi - θ)) (n : ℕ) :
    ∀ z : ℂ, z ∈ arcSet a ρ₁ → 0 < z.im → arcInvN a n z ∈ arcSet a ρ₁ ∧ 0 < (arcInvN a n z).im := by
  induction n with
  | zero => intro z hz hzim
            have h : arcInvN a 0 = (id : ℂ → ℂ) := by funext w; simp [arcInvN]
            rw [h]; exact ⟨hz, hzim⟩
  | succ n ih =>
      intro z hz hzim
      have h2 := arcInv_mem_arc hC hs₁ hs₂ hz hzim
      have h3 := ih (arcInv a z) h2.1 h2.2
      have heq : arcInvN a (n + 1) z = arcInvN a n (arcInv a z) := by
        simp only [arcInvN, Function.iterate_succ_apply]
      rw [heq]; exact h3

/-- `eqU` iterates of an arc point stay on the arc with positive height. -/
theorem eqU_iter_mem_arc {ρ₁ ρ₂ : ℝ → ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hC : NormEqCurve a ρ₁ ρ₂)
    (hs₁ : ∀ θ, ρ₁ (-θ) = ρ₁ θ) (hs₂ : ∀ θ, ρ₂ θ = ρ₁ (Real.pi - θ)) (m : ℕ) :
    ∀ z : ℂ, z ∈ arcSet a ρ₁ → 0 < z.im →
      (eqU a)^[m] z ∈ arcSet a ρ₁ ∧ 0 < ((eqU a)^[m] z).im := by
  induction m with
  | zero => intro z hz hzim; simpa using ⟨hz, hzim⟩
  | succ m ih =>
      intro z hz hzim
      have h2 := ih z hz hzim
      have h3 := eqU_mem_arc ha0 ha1 hC hs₁ hs₂ h2.1 h2.2
      have heq : (eqU a)^[m + 1] z = eqU a ((eqU a)^[m] z) := by
        rw [Function.iterate_succ_apply']
      rw [heq]; exact h3

/-- `arcInv^m ∘ eqU^m = id` on the open upper arc. -/
theorem arcInvN_apply_eqU_iter {ρ₁ ρ₂ : ℝ → ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hC : NormEqCurve a ρ₁ ρ₂) (hs₁ : ∀ θ, ρ₁ (-θ) = ρ₁ θ)
    (hs₂ : ∀ θ, ρ₂ θ = ρ₁ (Real.pi - θ)) (m : ℕ) :
    ∀ z : ℂ, z ∈ arcSet a ρ₁ → 0 < z.im → arcInvN a m ((eqU a)^[m] z) = z := by
  induction m with
  | zero => intro z hz hzim
            have h : arcInvN a 0 = (id : ℂ → ℂ) := by funext w; simp [arcInvN]
            rw [h]; simp
  | succ m ih =>
      intro z hz hzim
      have h2 := eqU_iter_mem_arc ha0 ha1 hC hs₁ hs₂ m z hz hzim
      have heq : arcInvN a (m + 1) ((eqU a)^[m + 1] z)
          = arcInvN a m (arcInv a ((eqU a)^[m + 1] z)) := by
        simp only [arcInvN, Function.iterate_succ_apply]
      rw [heq]
      have hstep : (eqU a)^[m + 1] z = eqU a ((eqU a)^[m] z) := by
        rw [Function.iterate_succ_apply']
      rw [hstep, arcInv_eqU_of_mem_arc hC h2.1 h2.2]
      exact ih z hz hzim

/-! ### The germ threshold -/

/-- A single small threshold with all the germ properties we need. -/
theorem germ_threshold {ρ₁ ρ₂ : ℝ → ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hC : NormEqCurve a ρ₁ ρ₂)
    (hs₁ : ∀ θ, ρ₁ (-θ) = ρ₁ θ) (hs₂ : ∀ θ, ρ₂ θ = ρ₁ (Real.pi - θ)) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ ε : ℝ, 0 < ε ∧ ContinuousOn (germPt a h) (Set.Ioo 0 ε) ∧
      (∀ t, 0 < t → t < ε → eqU a (germPt a h t) = germPt a h (eqLam a * t)) ∧
      (∀ t, 0 < t → t < ε → germPt a h t ∈ arcSet a ρ₁) ∧
      (∀ t, 0 < t → t < ε → 0 < (germPt a h t).im) := by
  obtain ⟨ε₁, hε₁, h1⟩ := germPt_eqU ha0 ha1 hh
  obtain ⟨ε₂, hε₂, h2⟩ := germPt_mem_arc ha0 ha1 hC hs₁ hs₂ hh
  obtain ⟨ε₃, hε₃, h3, h4, -⟩ := germPt_basic ha0 ha1 hh
  refine ⟨min ε₁ (min ε₂ ε₃), lt_min hε₁ (lt_min hε₂ hε₃), ?_, ?_, ?_, ?_⟩
  · refine h3.mono ?_
    intro t ht
    simp only [Set.mem_Ioo] at ht ⊢
    exact ⟨ht.1, lt_of_lt_of_le ht.2 (le_trans (min_le_right _ _) (min_le_right _ _))⟩
  · intro t ht hlt
    exact h1 t ht (lt_of_lt_of_le hlt (min_le_left _ _))
  · intro t ht hlt
    exact h2 t ht (lt_of_lt_of_le hlt (le_trans (min_le_right _ _) (min_le_left _ _)))
  · intro t ht hlt
    exact h4 t ht (lt_of_lt_of_le hlt (le_trans (min_le_right _ _) (min_le_right _ _)))

/-- One backward step: `arcInv (germPt (eqLam a * u)) = germPt u`. -/
theorem arcInv_step {ρ₁ ρ₂ : ℝ → ℝ} (hC : NormEqCurve a ρ₁ ρ₂) {h : ℂ → ℂ} {ε : ℝ}
    (hε₁ : ∀ t, 0 < t → t < ε → eqU a (germPt a h t) = germPt a h (eqLam a * t))
    (hε₂ : ∀ t, 0 < t → t < ε → germPt a h t ∈ arcSet a ρ₁)
    (hε₃ : ∀ t, 0 < t → t < ε → 0 < (germPt a h t).im)
    {u : ℝ} (hu0 : 0 < u) (hu : u < ε) :
    arcInv a (germPt a h (eqLam a * u)) = germPt a h u := by
  have hstep := hε₁ u hu0 hu
  rw [← hstep]
  exact arcInv_eqU' (im_sub_O2_pos (hε₃ u hu0 hu)) (arcSet_norm_sub_O2_lt_one hC (hε₂ u hu0 hu))

/-! ### The number of backward steps -/

/-- The least `n` with `eqLam a ^ n * t < ε`. -/
noncomputable def GammaNt (a : ℝ) (ε t : ℝ) : ℕ := by
  classical
  exact if h : ∃ n : ℕ, eqLam a ^ n * t < ε then Nat.find h else 0

theorem GammaNt_def {a ε t : ℝ} (h : ∃ n : ℕ, eqLam a ^ n * t < ε) :
    GammaNt a ε t = Nat.find h := by
  classical
  show (if h' : ∃ n : ℕ, eqLam a ^ n * t < ε then Nat.find h' else 0) = Nat.find h
  rw [dif_pos h]

theorem exists_nt {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ε : ℝ} (hε : 0 < ε) {t : ℝ}
    (ht : 0 < t) : ∃ n : ℕ, eqLam a ^ n * t < ε := by
  have hlam1 : eqLam a < 1 := eqLam_lt_one_hb ha0 ha1
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < ε / t by positivity) hlam1
  exact ⟨n, by rw [lt_div_iff₀ ht] at hn; linarith⟩

theorem GammaNt_spec {a ε t : ℝ} (h : ∃ n : ℕ, eqLam a ^ n * t < ε) :
    eqLam a ^ (GammaNt a ε t) * t < ε := by
  rw [GammaNt_def h]; exact Nat.find_spec h

theorem GammaNt_min {a ε t : ℝ} {m : ℕ} (hm : eqLam a ^ m * t < ε) :
    GammaNt a ε t ≤ m := by
  rw [GammaNt_def ⟨m, hm⟩]; exact Nat.find_min' ⟨m, hm⟩ hm

theorem GammaNt_eq_zero {a ε t : ℝ} (h : ∃ n : ℕ, eqLam a ^ n * t < ε) :
    GammaNt a ε t = 0 ↔ t < ε := by
  rw [GammaNt_def h, Nat.find_eq_zero h]
  simp

/-- The recursion for the index: `n(eqLam a * t) = n(t) - 1` when `n(t) ≥ 1`. -/
theorem GammaNt_pred {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ε : ℝ} (hε : 0 < ε) {t : ℝ}
    (ht : 0 < t) (hpos : 1 ≤ GammaNt a ε t) :
    GammaNt a ε (eqLam a * t) = GammaNt a ε t - 1 := by
  have hlam0 : 0 < eqLam a := eqLam_pos_hb ha0 ha1
  have hlamt : 0 < eqLam a * t := mul_pos hlam0 ht
  have hn_spec : eqLam a ^ (GammaNt a ε t) * t < ε := GammaNt_spec (exists_nt ha0 ha1 hε ht)
  have hex' : ∃ k : ℕ, eqLam a ^ k * (eqLam a * t) < ε := exists_nt ha0 ha1 hε hlamt
  rw [GammaNt_def hex', Nat.find_eq_iff hex']
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : GammaNt a ε t ≠ 0) with ⟨k, hk⟩
  have hk' : GammaNt a ε t - 1 = k := by omega
  constructor
  · have hkey : eqLam a ^ k * (eqLam a * t) = eqLam a ^ (k + 1) * t := by
      rw [pow_succ]; ring
    rw [hk', hkey]
    rw [show k + 1 = GammaNt a ε t by omega]
    exact hn_spec
  · intro n hn hcon
    have hkey : eqLam a ^ n * (eqLam a * t) = eqLam a ^ (n + 1) * t := by
      rw [pow_succ]; ring
    rw [hkey] at hcon
    have := GammaNt_min hcon
    omega

/-! ### The connection -/

/-- The heteroclinic connection. -/
noncomputable def heteroGamma (a : ℝ) (h : ℂ → ℂ) (ε : ℝ) (t : ℝ) : ℂ :=
  arcInvN a (GammaNt a ε t) (germPt a h (eqLam a ^ GammaNt a ε t * t))

theorem heteroGamma_eq (a : ℝ) (h : ℂ → ℂ) (ε t : ℝ) :
    heteroGamma a h ε t
      = arcInvN a (GammaNt a ε t) (germPt a h (eqLam a ^ GammaNt a ε t * t)) := rfl

/-- Consecutive values of the backward chain agree. -/
theorem GammaG_succ {ρ₁ ρ₂ : ℝ → ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hC : NormEqCurve a ρ₁ ρ₂)
    {h : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hε₁ : ∀ t, 0 < t → t < ε → eqU a (germPt a h t) = germPt a h (eqLam a * t))
    (hε₂ : ∀ t, 0 < t → t < ε → germPt a h t ∈ arcSet a ρ₁)
    (hε₃ : ∀ t, 0 < t → t < ε → 0 < (germPt a h t).im)
    {t : ℝ} (ht : 0 < t) {m : ℕ} (hm : GammaNt a ε t ≤ m) :
    arcInvN a (m + 1) (germPt a h (eqLam a ^ (m + 1) * t))
      = arcInvN a m (germPt a h (eqLam a ^ m * t)) := by
  have hlam0 : 0 < eqLam a := eqLam_pos_hb ha0 ha1
  have hlam1 : eqLam a < 1 := eqLam_lt_one_hb ha0 ha1
  have hmε : eqLam a ^ m * t < ε := by
    have hp : eqLam a ^ m ≤ eqLam a ^ GammaNt a ε t :=
      pow_le_pow_of_le_one hlam0.le hlam1.le hm
    have hspec := GammaNt_spec (exists_nt ha0 ha1 hε ht)
    have h2 : eqLam a ^ m * t ≤ eqLam a ^ GammaNt a ε t * t :=
      mul_le_mul_of_nonneg_right hp ht.le
    linarith
  have hm0 : 0 < eqLam a ^ m * t := mul_pos (pow_pos hlam0 m) ht
  have hkey : eqLam a * (eqLam a ^ m * t) = eqLam a ^ (m + 1) * t := by
    rw [pow_succ]; ring
  rw [show arcInvN a (m + 1) (germPt a h (eqLam a ^ (m + 1) * t))
      = arcInvN a m (arcInv a (germPt a h (eqLam a ^ (m + 1) * t))) from
        (by simp only [arcInvN, Function.iterate_succ_apply]),
    ← hkey, arcInv_step (u := eqLam a ^ m * t) hC hε₁ hε₂ hε₃ hm0 hmε]

/-- Independence of the number of steps. -/
theorem heteroGamma_indep {ρ₁ ρ₂ : ℝ → ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hC : NormEqCurve a ρ₁ ρ₂) {h : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hε₁ : ∀ t, 0 < t → t < ε → eqU a (germPt a h t) = germPt a h (eqLam a * t))
    (hε₂ : ∀ t, 0 < t → t < ε → germPt a h t ∈ arcSet a ρ₁)
    (hε₃ : ∀ t, 0 < t → t < ε → 0 < (germPt a h t).im)
    {t : ℝ} (ht : 0 < t) :
    ∀ k : ℕ, GammaNt a ε t ≤ k →
      arcInvN a k (germPt a h (eqLam a ^ k * t)) = heteroGamma a h ε t := by
  refine Nat.le_induction (m := GammaNt a ε t)
    (P := fun k _ => arcInvN a k (germPt a h (eqLam a ^ k * t)) = heteroGamma a h ε t)
    ?_ ?_
  · rw [heteroGamma_eq]
  · intro k hk IH
    have h1 : arcInvN a (k + 1) (germPt a h (eqLam a ^ (k + 1) * t))
        = arcInvN a k (germPt a h (eqLam a ^ k * t)) :=
      GammaG_succ ha0 ha1 hC hε hε₁ hε₂ hε₃ ht hk
    rw [h1]; exact IH

/-- `Γ` agrees with the germ for small `t`. -/
theorem heteroGamma_eq_germPt {h : ℂ → ℂ} {ε t : ℝ} (hlt : t < ε) :
    heteroGamma a h ε t = germPt a h t := by
  have h0 : GammaNt a ε t = 0 := (GammaNt_eq_zero ⟨0, by simpa using hlt⟩).mpr hlt
  rw [heteroGamma_eq, h0]
  simp [arcInvN]

/-- `Γ t` lies on the arc and has positive height. -/
theorem heteroGamma_mem_arc {ρ₁ ρ₂ : ℝ → ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hC : NormEqCurve a ρ₁ ρ₂) (hs₁ : ∀ θ, ρ₁ (-θ) = ρ₁ θ)
    (hs₂ : ∀ θ, ρ₂ θ = ρ₁ (Real.pi - θ)) {h : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hε₂ : ∀ t, 0 < t → t < ε → germPt a h t ∈ arcSet a ρ₁)
    (hε₃ : ∀ t, 0 < t → t < ε → 0 < (germPt a h t).im) {t : ℝ} (ht : 0 < t) :
    heteroGamma a h ε t ∈ arcSet a ρ₁ ∧ 0 < (heteroGamma a h ε t).im := by
  have hlam0 : 0 < eqLam a := eqLam_pos_hb ha0 ha1
  have hspec := GammaNt_spec (exists_nt ha0 ha1 hε ht)
  have hpos : 0 < eqLam a ^ GammaNt a ε t * t := mul_pos (pow_pos hlam0 _) ht
  rw [heteroGamma_eq]
  exact arcInvN_mem_arc hC hs₁ hs₂ _ _ (hε₂ _ hpos hspec) (hε₃ _ hpos hspec)

theorem arcInvN_eq_arcInv (n : ℕ) (hn : 1 ≤ n) (z : ℂ) :
    arcInvN a n z = arcInv a (arcInvN a (n - 1) z) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, arcInvN, Function.iterate_succ_apply']

/-- The recursion `eqU (Γ t) = Γ (eqLam a * t)`. -/
theorem heteroGamma_step {ρ₁ ρ₂ : ℝ → ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hC : NormEqCurve a ρ₁ ρ₂) (hs₁ : ∀ θ, ρ₁ (-θ) = ρ₁ θ)
    (hs₂ : ∀ θ, ρ₂ θ = ρ₁ (Real.pi - θ)) {h : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hε₁ : ∀ t, 0 < t → t < ε → eqU a (germPt a h t) = germPt a h (eqLam a * t))
    (hε₂ : ∀ t, 0 < t → t < ε → germPt a h t ∈ arcSet a ρ₁)
    (hε₃ : ∀ t, 0 < t → t < ε → 0 < (germPt a h t).im) {t : ℝ} (ht : 0 < t) :
    eqU a (heteroGamma a h ε t) = heteroGamma a h ε (eqLam a * t) := by
  have hlam0 : 0 < eqLam a := eqLam_pos_hb ha0 ha1
  have hlam1 : eqLam a < 1 := eqLam_lt_one_hb ha0 ha1
  have hlamt : 0 < eqLam a * t := mul_pos hlam0 ht
  rcases Nat.eq_zero_or_pos (GammaNt a ε t) with hn | hn
  · have hlt : t < ε := (GammaNt_eq_zero (exists_nt ha0 ha1 hε ht)).mp hn
    have hlt' : eqLam a * t < ε := lt_of_lt_of_le (mul_lt_of_lt_one_left ht hlam1) hlt.le
    rw [heteroGamma_eq_germPt hlt, heteroGamma_eq_germPt hlt']
    exact hε₁ t ht hlt
  · have hGt : heteroGamma a h ε t = arcInv a (heteroGamma a h ε (eqLam a * t)) := by
      have hpred : GammaNt a ε (eqLam a * t) = GammaNt a ε t - 1 :=
        GammaNt_pred ha0 ha1 hε ht hn
      have hpow : eqLam a ^ (GammaNt a ε t - 1) * (eqLam a * t)
          = eqLam a ^ GammaNt a ε t * t := by
        rcases Nat.exists_eq_succ_of_ne_zero (by omega : GammaNt a ε t ≠ 0) with ⟨k, hk⟩
        rw [hk]
        have hk'' : k + 1 - 1 = k := by omega
        rw [hk'']
        simp only [Nat.succ_eq_add_one]
        rw [pow_succ]; ring
      rw [heteroGamma_eq (a) (h) (ε) t, heteroGamma_eq (a) (h) (ε) (eqLam a * t), hpred, hpow,
        arcInvN_eq_arcInv (GammaNt a ε t) hn
          (germPt a h (eqLam a ^ GammaNt a ε t * t))]
    rw [hGt, eqU_arcInv]
    exact arcSet_norm_add_O2_lt_one hC (heteroGamma_mem_arc ha0 ha1 hC hs₁ hs₂ hε hε₂ hε₃ hlamt).1

/-- `Γ` is continuous on `t > 0`. -/
theorem heteroGamma_continuousOn {ρ₁ ρ₂ : ℝ → ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hC : NormEqCurve a ρ₁ ρ₂) (hs₁ : ∀ θ, ρ₁ (-θ) = ρ₁ θ)
    (hs₂ : ∀ θ, ρ₂ θ = ρ₁ (Real.pi - θ)) {h : ℂ → ℂ} {ε : ℝ}
    (hεc : ContinuousOn (germPt a h) (Set.Ioo 0 ε)) (hε : 0 < ε)
    (hε₁ : ∀ t, 0 < t → t < ε → eqU a (germPt a h t) = germPt a h (eqLam a * t))
    (hε₂ : ∀ t, 0 < t → t < ε → germPt a h t ∈ arcSet a ρ₁)
    (hε₃ : ∀ t, 0 < t → t < ε → 0 < (germPt a h t).im) :
    ContinuousOn (heteroGamma a h ε) (Set.Ioi 0) := by
  rw [IsOpen.continuousOn_iff isOpen_Ioi]
  intro t₀ ht₀
  have hlam0 : 0 < eqLam a := eqLam_pos_hb ha0 ha1
  set n := GammaNt a ε t₀ with hn
  have hn_spec : eqLam a ^ n * t₀ < ε := by
    rw [hn]; exact GammaNt_spec (exists_nt ha0 ha1 hε ht₀)
  have hGcont : ContinuousAt (fun t : ℝ => arcInvN a n (germPt a h (eqLam a ^ n * t))) t₀ := by
    have harg : ContinuousAt (fun t : ℝ => eqLam a ^ n * t) t₀ :=
      (continuous_const.mul continuous_id).continuousAt
    have hlt0 : 0 < eqLam a ^ n * t₀ := mul_pos (pow_pos hlam0 n) ht₀
    have hg : ContinuousAt (germPt a h) (eqLam a ^ n * t₀) :=
      hεc.continuousAt (Ioo_mem_nhds hlt0 hn_spec)
    have hz : germPt a h (eqLam a ^ n * t₀) ∈ arcSet a ρ₁ := hε₂ _ hlt0 hn_spec
    have hzim : 0 < (germPt a h (eqLam a ^ n * t₀)).im := hε₃ _ hlt0 hn_spec
    have hcomp : ContinuousAt (fun t : ℝ => germPt a h (eqLam a ^ n * t)) t₀ := hg.comp harg
    have houter : ContinuousAt (arcInvN a n) (germPt a h (eqLam a ^ n * t₀)) :=
      continuousAt_arcInvN hC hs₁ hs₂ n _ hz hzim
    exact ContinuousAt.comp (f := fun t : ℝ => germPt a h (eqLam a ^ n * t)) houter hcomp
  refine hGcont.congr_of_eventuallyEq ?_
  have hev1 : ∀ᶠ t in 𝓝 t₀, eqLam a ^ n * t < ε := by
    have hcont : Continuous (fun t : ℝ => eqLam a ^ n * t) := continuous_const.mul continuous_id
    exact (isOpen_lt hcont continuous_const).mem_nhds hn_spec
  have hev2 : ∀ᶠ t in 𝓝 t₀, (0 : ℝ) < t := isOpen_Ioi.mem_nhds ht₀
  filter_upwards [hev1, hev2] with t htε htpos
  exact (heteroGamma_indep ha0 ha1 hC hε hε₁ hε₂ hε₃ htpos n (GammaNt_min htε)).symm

/-! ### Surjectivity onto the open upper arc -/

/-- Pull-back identity: `Γ (s / eqLam a ^ m) = arcInv^m (germPt s)`. -/
theorem heteroGamma_inv_step {ρ₁ ρ₂ : ℝ → ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hC : NormEqCurve a ρ₁ ρ₂) {h : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hε₁ : ∀ t, 0 < t → t < ε → eqU a (germPt a h t) = germPt a h (eqLam a * t))
    (hε₂ : ∀ t, 0 < t → t < ε → germPt a h t ∈ arcSet a ρ₁)
    (hε₃ : ∀ t, 0 < t → t < ε → 0 < (germPt a h t).im)
    {s : ℝ} (hs0 : 0 < s) (hsε : s < ε) (m : ℕ) :
    heteroGamma a h ε (s / eqLam a ^ m) = arcInvN a m (germPt a h s) := by
  have hlam0 : 0 < eqLam a := eqLam_pos_hb ha0 ha1
  have hkey : eqLam a ^ m * (s / eqLam a ^ m) = s := by
    rw [mul_comm, div_mul_cancel₀ _ (pow_ne_zero m (ne_of_gt hlam0))]
  have ht : 0 < s / eqLam a ^ m := div_pos hs0 (pow_pos hlam0 m)
  have hm : GammaNt a ε (s / eqLam a ^ m) ≤ m := GammaNt_min (by rw [hkey]; exact hsε)
  have hind := heteroGamma_indep ha0 ha1 hC hε hε₁ hε₂ hε₃ ht m hm
  rw [← hind, hkey]

/-- Every point of the open upper arc is a value of `Γ`. -/
theorem heteroGamma_surj {ρ₁ ρ₂ : ℝ → ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hC : NormEqCurve a ρ₁ ρ₂) (hs₁ : ∀ θ, ρ₁ (-θ) = ρ₁ θ)
    (hs₂ : ∀ θ, ρ₂ θ = ρ₁ (Real.pi - θ)) {h : ℂ → ℂ} {r : ℝ} (hh : IsStableGerm a h r)
    {ε : ℝ} (hε : 0 < ε)
    (hε₁ : ∀ t, 0 < t → t < ε → eqU a (germPt a h t) = germPt a h (eqLam a * t))
    (hε₂ : ∀ t, 0 < t → t < ε → germPt a h t ∈ arcSet a ρ₁)
    (hε₃ : ∀ t, 0 < t → t < ε → 0 < (germPt a h t).im) :
    ∀ z : ℂ, z ∈ arcSet a ρ₁ → 0 < z.im → ∃ s, 0 < s ∧ heteroGamma a h ε s = z := by
  intro z hz hzim
  obtain ⟨ρ', h', hρ', hh'pos, h2ρ', hbox⟩ := arc_box_eq_germPt ha0 ha1 hC hs₁ hs₂ hh ε hε
  have hconv := arc_iterate_tendsto_A1 ha0 ha1 hC hs₁ hs₂ hz hzim
  have hre : Tendsto (fun m : ℕ => ((eqU a)^[m] z).re) atTop (nhds (-(1/2))) := by
    have h1 := (Complex.continuous_re.tendsto ((-(1/2) : ℝ) : ℂ)).comp hconv
    simpa only [Function.comp_def, Complex.ofReal_re] using h1
  have him : Tendsto (fun m : ℕ => ((eqU a)^[m] z).im) atTop (nhds 0) := by
    have h1 := (Complex.continuous_im.tendsto ((-(1/2) : ℝ) : ℂ)).comp hconv
    simpa only [Function.comp_def, Complex.ofReal_im] using h1
  have hre2 : Tendsto (fun m : ℕ => ((eqU a)^[m] z).re + 1/2) atTop (nhds 0) := by
    have h1 : Tendsto (fun m : ℕ => ((eqU a)^[m] z).re + 1/2) atTop (nhds (-(1/2) + 1/2)) :=
      hre.add tendsto_const_nhds
    simpa using h1
  obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.mp hre2 ρ' hρ'
  obtain ⟨N2, hN2⟩ := Metric.tendsto_atTop.mp him h' hh'pos
  set m := max N1 N2 with hmdef
  have hzarc := eqU_iter_mem_arc ha0 ha1 hC hs₁ hs₂ m z hz hzim
  have hbound1 : |(((eqU a)^[m] z).re + 1/2)| ≤ ρ' := by
    have h1 := hN1 m (le_max_left _ _)
    rw [Real.dist_eq, sub_zero] at h1
    exact h1.le
  have hbound2 : ((eqU a)^[m] z).im ≤ h' := by
    have h1 := hN2 m (le_max_right _ _)
    rw [Real.dist_eq, sub_zero] at h1
    rw [abs_of_pos hzarc.2] at h1
    exact h1.le
  obtain ⟨s, hs0, hsε, hseq⟩ := hbox ((eqU a)^[m] z) hzarc.1 hzarc.2 hbound2 hbound1
  refine ⟨s / eqLam a ^ m, div_pos hs0 (pow_pos (eqLam_pos_hb ha0 ha1) m), ?_⟩
  rw [heteroGamma_inv_step ha0 ha1 hC hε hε₁ hε₂ hε₃ hs0 hsε m, hseq]
  exact arcInvN_apply_eqU_iter ha0 ha1 hC hs₁ hs₂ m z hz hzim

/-- The bisector symmetry: `-conj (Γ t)` is again a value of `Γ`. -/
theorem heteroGamma_symm {ρ₁ ρ₂ : ℝ → ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hC : NormEqCurve a ρ₁ ρ₂) (hs₁ : ∀ θ, ρ₁ (-θ) = ρ₁ θ)
    (hs₂ : ∀ θ, ρ₂ θ = ρ₁ (Real.pi - θ)) {h : ℂ → ℂ} {r : ℝ} (hh : IsStableGerm a h r)
    {ε : ℝ} (hε : 0 < ε)
    (hε₁ : ∀ t, 0 < t → t < ε → eqU a (germPt a h t) = germPt a h (eqLam a * t))
    (hε₂ : ∀ t, 0 < t → t < ε → germPt a h t ∈ arcSet a ρ₁)
    (hε₃ : ∀ t, 0 < t → t < ε → 0 < (germPt a h t).im) :
    ∀ t, 0 < t → ∃ s, 0 < s ∧
      heteroGamma a h ε s = -(starRingEnd ℂ) (heteroGamma a h ε t) := by
  intro t ht
  have hzarc := heteroGamma_mem_arc ha0 ha1 hC hs₁ hs₂ hε hε₂ hε₃ ht
  obtain ⟨-, -, -, -, -, harcθ, -, -⟩ := arc_near_A1 ha0 ha1 hC hs₁ hs₂
  obtain ⟨θ, hθ0, hθπ, hθeq⟩ := harcθ _ hzarc.1 hzarc.2
  obtain ⟨-, -, hsymm⟩ := arc_eqU_maps ha0 ha1 hC hs₁ hs₂
  obtain ⟨θ', hθ'0, hθ'π, hθ'eq⟩ := hsymm θ hθ0 hθπ
  have hmem : -(starRingEnd ℂ) (heteroGamma a h ε t) ∈ arcSet a ρ₁ := by
    rw [hθeq]; exact ⟨θ', hθ'eq.symm⟩
  have him : 0 < (-(starRingEnd ℂ) (heteroGamma a h ε t)).im := by
    rw [Complex.neg_im, Complex.conj_im]
    linarith [hzarc.2]
  obtain ⟨s, hs0, hseq⟩ :=
    heteroGamma_surj ha0 ha1 hC hs₁ hs₂ hh hε hε₁ hε₂ hε₃ _ hmem him
  exact ⟨s, hs0, hseq⟩

end

end Work.EQ
