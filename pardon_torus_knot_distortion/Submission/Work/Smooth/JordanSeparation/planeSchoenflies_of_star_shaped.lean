import Mathlib
import Submission.Work.Smooth.JordanSeparation.Unconditional
import Submission.Work.Smooth.JordanSeparation.planeSchoenflies_of_injective_extension
import Submission.Work.Smooth.JordanSeparation.curve_arg_continuous

/-!
# The star-shaped (radially monotone) case of the Jordan–Schoenflies extension

This file proves the **star-shaped case** of the extension statement (E) of `SCHOENFLIES.md`
(§3.6): if the bounded side `S.V` of a `C¹` simple closed plane curve `c` is swept out by the open
radial segments from a point `p` — i.e. `V = ⋃_{r<1, θ} {p + r(γ θ − p)}`, with the segments meeting
the curve only at `r = 1` — then `γ` extends to a continuous injection of the disc.

The extension is the *radial map*

`starMap c p w = p + ‖w‖ • (γ (arg w) − p)`,

sending `0` to `p` and the boundary circle `circlePoint θ` to `γ θ` (up to `2π`-periodicity of
`γ`, which absorbs the `2π`-jump of `Complex.arg` across the negative real axis).

* **injectivity** uses only `hseg`: if two boundary arguments `arg u`, `arg v` gave collinear radial
  segments with different radii, the nearer curve point would equal `p + r·(farther − p)` with
  `0 < r < 1`, contradicting `hseg`; equal radii forces `γ (arg u) = γ (arg v)`, whence the
  arguments differ by a multiple of `2π` and the two disc points coincide.
* **the boundary values** are `Complex.norm_mul_exp_arg_mul_I` plus periodic reduction.
* **the image** needs nothing extra: `range_eq_closure_V_of_injective_extension` gives
  `Set.range (starMap c p) = closure S.V` from injectivity and the boundary values alone — so the
  hypotheses `hp` and `hmem` are, logically speaking, redundant, but are kept in the statement to
  record the intended geometry.
-/

namespace Work.Smooth.JordanSeparation

open Set Filter
open Work.Smooth.Jordan

noncomputable section

/-- The **radial map** of a star-shaped side: it sends `w : 𝔻` to the point at radius `‖w‖` of the
radial segment from `p` through `γ (arg w)`, and the centre `0` to `p`.  `Complex.arg 0 = 0` is
irrelevant because of the factor `‖0‖ = 0`. -/
def starMap (c : SmoothPlaneCurve) (p : ℂ) : Disc → ℂ :=
  fun w => p + ((‖(w : ℂ)‖ : ℝ) : ℂ) * (c.γ (Complex.arg (w : ℂ)) - p)

theorem starMap_apply (c : SmoothPlaneCurve) (p : ℂ) (w : Disc) :
    starMap c p w
      = p + ((‖(w : ℂ)‖ : ℝ) : ℂ) * (c.γ (Complex.arg (w : ℂ)) - p) := rfl

/-- Two real parameters differing by an integer multiple of `2π` have the same exponential. -/
lemma exp_arg_eq_of_mod {a b : ℝ} {k : ℤ} (h : b = a + (k : ℝ) * (2 * Real.pi)) :
    Complex.exp ((b : ℂ) * Complex.I) = Complex.exp ((a : ℂ) * Complex.I) := by
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨k, ?_⟩
  rw [h]; push_cast; ring

/-- `‖γ (arg z) − p‖` is bounded uniformly in `z`: `arg` takes values in `(−π, π]`, a bounded
interval. -/
lemma bound_arg (c : SmoothPlaneCurve) (p : ℂ) :
    ∃ M : ℝ, ∀ z : ℂ, ‖c.γ (Complex.arg z) - p‖ ≤ M := by
  have hc : Continuous (fun θ : ℝ => ‖c.γ θ - p‖) := (c.cont.sub continuous_const).norm
  obtain ⟨M, hM⟩ := (isCompact_Icc.image hc).bddAbove
  refine ⟨M, fun z => ?_⟩
  have hz : Complex.arg z ∈ Set.Icc (-Real.pi) Real.pi :=
    ⟨(Complex.arg_mem_Ioc z).1.le, (Complex.arg_mem_Ioc z).2⟩
  exact hM ⟨Complex.arg z, hz, rfl⟩

/-- The radial map is continuous.  At a point `w` of the open disc with `w ≠ 0` this is the
continuity of `z ↦ γ (arg z)` on `ℂ ∖ {0}` (`continuousAt_curve_arg_periodic`) multiplied by the
continuous norm; at the centre only the bound `‖starMap w − p‖ ≤ M ‖w‖` is used. -/
theorem continuous_starMap (c : SmoothPlaneCurve) (p : ℂ) : Continuous (starMap c p) := by
  obtain ⟨M, hM⟩ := bound_arg c p
  set M' : ℝ := max M 0 with hM'
  have hM'le : ∀ z : ℂ, ‖c.γ (Complex.arg z) - p‖ ≤ M' :=
    fun z => le_trans (hM z) (le_max_left _ _)
  have hcont0 : ContinuousAt (starMap c p) (0 : Disc) := by
    have hbound : ∀ w : Disc, ‖((‖(w : ℂ)‖ : ℝ) : ℂ) * (c.γ (Complex.arg (w : ℂ)) - p)‖
        ≤ ‖(w : ℂ)‖ * M' := by
      intro w
      have hnorm : ‖(((‖(w : ℂ)‖ : ℝ)) : ℂ)‖ = ‖(w : ℂ)‖ := by
        rw [show (((‖(w : ℂ)‖ : ℝ)) : ℂ) = Complex.ofReal ‖(w : ℂ)‖ from rfl]
        rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
      rw [norm_mul, hnorm]
      exact mul_le_mul_of_nonneg_left (hM'le (w : ℂ)) (norm_nonneg _)
    have htend : Tendsto (fun w : Disc => ‖(w : ℂ)‖ * M') (nhds (0 : Disc)) (nhds 0) := by
      have h1 : Tendsto (fun w : Disc => ‖(w : ℂ)‖) (nhds (0 : Disc)) (nhds 0) := by
        simpa [ContinuousAt] using (continuous_subtype_val.continuousAt (x := (0 : Disc))).norm
      simpa using h1.mul_const M'
    have h2 : Tendsto (fun w : Disc => ‖((‖(w : ℂ)‖ : ℝ) : ℂ) * (c.γ (Complex.arg (w : ℂ)) - p)‖)
        (nhds (0 : Disc)) (nhds 0) :=
      squeeze_zero (fun w => norm_nonneg _) hbound htend
    have hdiff : Tendsto (fun w : Disc => ((‖(w : ℂ)‖ : ℝ) : ℂ) * (c.γ (Complex.arg (w : ℂ)) - p))
        (nhds (0 : Disc)) (nhds 0) := tendsto_zero_iff_norm_tendsto_zero.mpr h2
    change ContinuousAt (fun w : Disc =>
      p + ((‖(w : ℂ)‖ : ℝ) : ℂ) * (c.γ (Complex.arg (w : ℂ)) - p)) (0 : Disc)
    simpa [ContinuousAt] using hdiff.const_add p
  have hcont_ne : ∀ w₀ : Disc, (w₀ : ℂ) ≠ 0 → ContinuousAt (starMap c p) w₀ := by
    intro w₀ hw₀
    have harg : ContinuousAt (fun z : ℂ => c.γ (Complex.arg z)) (w₀ : ℂ) :=
      continuousAt_curve_arg_periodic c.periodic c.cont hw₀
    have harg' : ContinuousAt (fun w : Disc => c.γ (Complex.arg (w : ℂ))) w₀ :=
      harg.comp continuous_subtype_val.continuousAt
    have hnorm : Continuous (fun w : Disc => ((‖(w : ℂ)‖ : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp continuous_subtype_val.norm
    have hca : ContinuousAt (fun w : Disc =>
        p + ((‖(w : ℂ)‖ : ℝ) : ℂ) * (c.γ (Complex.arg (w : ℂ)) - p)) w₀ :=
      continuousAt_const.add (hnorm.continuousAt.mul (harg'.sub continuousAt_const))
    change ContinuousAt (fun w : Disc =>
      p + ((‖(w : ℂ)‖ : ℝ) : ℂ) * (c.γ (Complex.arg (w : ℂ)) - p)) w₀
    exact hca
  rw [continuous_iff_continuousAt]
  intro w
  by_cases hw : (w : ℂ) = 0
  · have hw0 : w = 0 := Subtype.ext (by simpa using hw)
    rw [hw0]; exact hcont0
  · exact hcont_ne w hw

/-- The radial map takes the boundary circle to the curve (up to the periodic identification of the
argument). -/
theorem starMap_circlePoint (c : SmoothPlaneCurve) (p : ℂ) (θ : ℝ) :
    starMap c p (circlePoint θ) = c.γ θ := by
  have hnorm : ((‖(circlePoint θ : ℂ)‖ : ℝ) : ℂ) = 1 := by
    rw [circlePoint_coe, Complex.norm_exp_ofReal_mul_I]
    norm_num
  have harg : c.γ (Complex.arg (circlePoint θ : ℂ)) = c.γ θ := by
    have h := Complex.norm_mul_exp_arg_mul_I (circlePoint θ : ℂ)
    rw [hnorm, one_mul, circlePoint_coe] at h
    exact eq_of_exp_eq_periodic c.periodic h
  rw [starMap_apply, hnorm, harg]
  ring

/-- `starMap` attains the centre `p` exactly at the centre of the disc, because `p` is off the
trace. -/
lemma starMap_eq_p_iff (c : SmoothPlaneCurve) (p : ℂ) (hpnt : p ∉ c.trace) (w : Disc) :
    starMap c p w = p ↔ (w : ℂ) = 0 := by
  constructor
  · intro h
    by_contra hw
    have key : ((‖(w : ℂ)‖ : ℝ) : ℂ) * (c.γ (Complex.arg (w : ℂ)) - p) = 0 := by
      have h' : p + ((‖(w : ℂ)‖ : ℝ) : ℂ) * (c.γ (Complex.arg (w : ℂ)) - p) = p := by
        rw [← starMap_apply]; exact h
      exact add_left_cancel (h'.trans (add_zero p).symm)
    have hwne : ((‖(w : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; exact norm_ne_zero_iff.mpr hw
    have hγ : c.γ (Complex.arg (w : ℂ)) = p :=
      sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hwne)
    exact hpnt ⟨Complex.arg (w : ℂ), hγ⟩
  · intro hw
    rw [starMap_apply, hw]; simp

/-- **Injectivity of the radial map.**  This is the heart of the star-shaped case: `hseg` says that
the open radial segments `{p + r (γ θ − p) : 0 < r < 1}` meet the curve only at `r = 1`, so two
distinct radii on the same direction would output a curve point on an open segment. -/
theorem starMap_injective (c : SmoothPlaneCurve) (hs : c.toPlaneCurve.IsSimple) (p : ℂ)
    (hpnt : p ∉ c.trace)
    (hseg : ∀ (θ θ' : ℝ) (r : ℝ), 0 < r → r < 1 → c.γ θ' ≠ p + (r : ℂ) * (c.γ θ - p)) :
    Function.Injective (starMap c p) := by
  intro u v huv
  by_cases hu0 : (u : ℂ) = 0
  · have : starMap c p u = p := (starMap_eq_p_iff c p hpnt u).mpr hu0
    have hv : (v : ℂ) = 0 := (starMap_eq_p_iff c p hpnt v).mp (by rw [← huv]; exact this)
    exact Subtype.ext (by rw [hu0, hv])
  · by_cases hv0 : (v : ℂ) = 0
    · exfalso
      have : starMap c p v = p := (starMap_eq_p_iff c p hpnt v).mpr hv0
      exact hu0 ((starMap_eq_p_iff c p hpnt u).mp (by rw [huv]; exact this))
    · set A : ℂ := c.γ (Complex.arg (u : ℂ)) - p with hA
      set B : ℂ := c.γ (Complex.arg (v : ℂ)) - p with hB
      set ru : ℝ := ‖(u : ℂ)‖ with hru
      set rv : ℝ := ‖(v : ℂ)‖ with hrv
      have hru0 : 0 < ru := by rw [hru]; exact norm_pos_iff.mpr hu0
      have hrv0 : 0 < rv := by rw [hrv]; exact norm_pos_iff.mpr hv0
      have hruc : ((ru : ℝ) : ℂ) ≠ 0 := by rw [Complex.ofReal_ne_zero]; exact hru0.ne'
      have hrvc : ((rv : ℝ) : ℂ) ≠ 0 := by rw [Complex.ofReal_ne_zero]; exact hrv0.ne'
      have heq : ((ru : ℝ) : ℂ) * A = ((rv : ℝ) : ℂ) * B := by
        have h := huv
        rw [starMap_apply, starMap_apply] at h
        rw [← hA, ← hB, ← hru, ← hrv] at h
        exact add_left_cancel h
      rcases lt_trichotomy ru rv with hlt | heqr | hgt
      · -- the radial distance of `v` exceeds that of `u`
        have hB' : B = ((ru / rv : ℝ) : ℂ) * A := by
          have hcoe : ((ru / rv : ℝ) : ℂ) = ((ru : ℝ) : ℂ) * ((rv : ℝ) : ℂ)⁻¹ := by
            rw [Complex.ofReal_div, div_eq_mul_inv]
          rw [hcoe]
          calc B = ((rv : ℝ) : ℂ)⁻¹ * (((rv : ℝ) : ℂ) * B) := by rw [inv_mul_cancel_left₀ hrvc]
            _ = ((rv : ℝ) : ℂ)⁻¹ * (((ru : ℝ) : ℂ) * A) := by rw [← heq]
            _ = ((ru : ℝ) : ℂ) * ((rv : ℝ) : ℂ)⁻¹ * A := by ring
        have hs1 : 0 < ru / rv := div_pos hru0 hrv0
        have hs2 : ru / rv < 1 := (div_lt_one hrv0).mpr hlt
        refine absurd ?_ (hseg (Complex.arg (u : ℂ)) (Complex.arg (v : ℂ)) (ru / rv) hs1 hs2)
        have h1 : c.γ (Complex.arg (v : ℂ)) - p
            = ((ru / rv : ℝ) : ℂ) * (c.γ (Complex.arg (u : ℂ)) - p) := by
          simpa [hA, hB] using hB'
        rw [← h1]; ring
      · -- equal radial distances: the arguments differ by a multiple of `2π`
        have hruv : ((ru : ℝ) : ℂ) = ((rv : ℝ) : ℂ) := by rw [heqr]
        have hAeqB : A = B := mul_left_cancel₀ hruc (by rw [heq, hruv])
        have hγeq : c.γ (Complex.arg (u : ℂ)) = c.γ (Complex.arg (v : ℂ)) := by
          have : c.γ (Complex.arg (u : ℂ)) - p = c.γ (Complex.arg (v : ℂ)) - p := by
            simpa [hA, hB] using hAeqB
          exact sub_left_inj.mp this
        obtain ⟨k, hk⟩ := hs.eq_mod_period hγeq
        have hexp : Complex.exp ((Complex.arg (v : ℂ) : ℂ) * Complex.I)
            = Complex.exp ((Complex.arg (u : ℂ) : ℂ) * Complex.I) := exp_arg_eq_of_mod hk
        have hcoe_eq : ((‖(u : ℂ)‖ : ℝ) : ℂ) = ((‖(v : ℂ)‖ : ℝ) : ℂ) := by
          rw [← hru, ← hrv]; exact hruv
        have huv_coe : (u : ℂ) = (v : ℂ) := by
          have h1 := Complex.norm_mul_exp_arg_mul_I (u : ℂ)
          have h2 := Complex.norm_mul_exp_arg_mul_I (v : ℂ)
          calc (u : ℂ) = ((‖(u : ℂ)‖ : ℝ) : ℂ)
                * Complex.exp ((Complex.arg (u : ℂ) : ℂ) * Complex.I) := h1.symm
            _ = ((‖(v : ℂ)‖ : ℝ) : ℂ)
                * Complex.exp ((Complex.arg (v : ℂ) : ℂ) * Complex.I) := by
                  rw [hcoe_eq, ← hexp]
            _ = (v : ℂ) := h2
        exact Subtype.ext huv_coe
      · -- the radial distance of `u` exceeds that of `v` (symmetric to the first case)
        have hA' : A = ((rv / ru : ℝ) : ℂ) * B := by
          have hcoe : ((rv / ru : ℝ) : ℂ) = ((rv : ℝ) : ℂ) * ((ru : ℝ) : ℂ)⁻¹ := by
            rw [Complex.ofReal_div, div_eq_mul_inv]
          rw [hcoe]
          calc A = ((ru : ℝ) : ℂ)⁻¹ * (((ru : ℝ) : ℂ) * A) := by rw [inv_mul_cancel_left₀ hruc]
            _ = ((ru : ℝ) : ℂ)⁻¹ * (((rv : ℝ) : ℂ) * B) := by rw [heq]
            _ = ((rv : ℝ) : ℂ) * ((ru : ℝ) : ℂ)⁻¹ * B := by ring
        have hs1 : 0 < rv / ru := div_pos hrv0 hru0
        have hs2 : rv / ru < 1 := (div_lt_one hru0).mpr hgt
        refine absurd ?_ (hseg (Complex.arg (v : ℂ)) (Complex.arg (u : ℂ)) (rv / ru) hs1 hs2)
        have h1 : c.γ (Complex.arg (u : ℂ)) - p
            = ((rv / ru : ℝ) : ℂ) * (c.γ (Complex.arg (v : ℂ)) - p) := by
          simpa [hA, hB] using hA'
        rw [← h1]; ring

/-- **The star-shaped case of the Jordan–Schoenflies extension.**  If the bounded side `S.V` of a
`C¹` simple closed plane curve `c` is the union of the open radial segments from a point `p`
(`hmem`), and those segments meet the curve only at their endpoints (`hseg`), then `γ` extends to a
continuous injection `F : 𝔻 → ℂ` with `Set.range F = closure S.V`.

The hypotheses `hp` and `hmem` are not used in the proof below (the image statement follows from
injectivity plus the boundary values through `range_eq_closure_V_of_injective_extension`); they are
kept because they record the geometry the statement is about. -/
theorem planeSchoenflies_of_star_shaped (c : SmoothPlaneCurve)
    (hs : c.toPlaneCurve.IsSimple) (S : PlaneSeparation c.toPlaneCurve) (p : ℂ) (hp : p ∈ S.V)
    (hseg : ∀ (θ θ' : ℝ) (r : ℝ), 0 < r → r < 1 → c.γ θ' ≠ p + (r : ℂ) * (c.γ θ - p))
    (hmem : ∀ x : ℂ, x ∈ S.V ↔ ∃ (r : ℝ) (θ : ℝ), 0 ≤ r ∧ r < 1 ∧
      x = p + (r : ℂ) * (c.γ θ - p)) :
    ∃ F : C(Disc, ℂ), Function.Injective F ∧ (∀ θ : ℝ, F (circlePoint θ) = c.γ θ) ∧
      Set.range F = closure S.V := by
  have hpnt : p ∉ c.trace := by
    have : p ∈ c.traceᶜ := by rw [← S.union_eq]; exact Or.inr hp
    exact this
  refine ⟨⟨starMap c p, continuous_starMap c p⟩,
    starMap_injective c hs p hpnt hseg, ?_, ?_⟩
  · intro θ
    exact starMap_circlePoint c p θ
  · exact range_eq_closure_V_of_injective_extension c hs S ⟨starMap c p, continuous_starMap c p⟩
      (starMap_injective c hs p hpnt hseg) (fun θ => starMap_circlePoint c p θ)

end

end Work.Smooth.JordanSeparation
