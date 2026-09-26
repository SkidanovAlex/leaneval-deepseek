import Mathlib
import Submission.Work.Smooth.JordanSeparation.Separation
import Submission.Work.Smooth.JordanSeparation.Corollaries

/-!
# The frontier of a side of a Jordan separation is the curve

For a `C¹` immersed simple closed plane curve `c` and *any* Jordan separation
`S : PlaneSeparation c.toPlaneCurve` of it (two disjoint non-empty preconnected open sets `U`, `V`
covering the complement of the trace, with `V` bounded), the frontier of the unbounded side `U` is
exactly the trace of the curve:

`frontier S.U = c.trace`.

## The proof

`frontier S.U ⊆ c.trace`: if `x ∈ frontier S.U` then `x ∈ closure S.U` and — `S.U` being open —
`x ∉ S.U`.  If `x` were off the trace it would lie in one of the two sides; in `U` it would be an
interior point of `U`, and in `V` (which is open) it would exhibit a common point of `U` and `V`.
Both are impossible.

`c.trace ⊆ frontier S.U`: a point of the curve is not in `U`, and it is a limit point of `U`,
because the index of `c` jumps across the curve.  The jump is proved in the sibling module
`Jump.lean` at the parameter `0`; **the parameter is shifted** here: for `a : ℝ` the curve
`t ↦ c.γ (t + a)` (`shiftCurve`) is again a `C¹` immersed simple closed curve with the same trace
and the same index off the trace (`wind_shiftCurve`, `ind_shiftCurve`), so `ind_jump` applied to it
(`ind_jump_at`) shows that the two normal offsets `c.γ a ± s·normalField c a` have different
indices for `0 < s` small.  Two points of the complement of the trace with different indices lie on
different sides (`ind_const_on_preconnected`, and `ind = 0` on `U`), so one of the two offsets is in
`S.U`; letting `s → 0` puts `c.γ a` in the closure of `S.U`.
-/

open Set

namespace Work.Smooth.Jordan

/-- **Simplicity gives equality modulo the period.**  Two parameters at which a simple closed
curve takes the same value differ by an integer multiple of the period. -/
theorem PlaneCurve.IsSimple.eq_mod_period {c : PlaneCurve} (hs : c.IsSimple) {a b : ℝ}
    (h : c.γ a = c.γ b) : ∃ k : ℤ, b = a + (k : ℝ) * (2 * Real.pi) := by
  have hpos : (0 : ℝ) < 2 * Real.pi := two_pi_pos
  set ka : ℤ := ⌊a / (2 * Real.pi)⌋ with hka
  set kb : ℤ := ⌊b / (2 * Real.pi)⌋ with hkb
  have ha : a - (ka : ℝ) * (2 * Real.pi) ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := by
    constructor
    · have := (le_div_iff₀ hpos).mp (Int.floor_le (a / (2 * Real.pi))); linarith
    · have := (div_lt_iff₀ hpos).mp (Int.lt_floor_add_one (a / (2 * Real.pi))); linarith
  have hb : b - (kb : ℝ) * (2 * Real.pi) ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := by
    constructor
    · have := (le_div_iff₀ hpos).mp (Int.floor_le (b / (2 * Real.pi))); linarith
    · have := (div_lt_iff₀ hpos).mp (Int.lt_floor_add_one (b / (2 * Real.pi))); linarith
  have ha' : c.γ (a - (ka : ℝ) * (2 * Real.pi)) = c.γ a := by
    have := c.apply_add_int_mul (a - (ka : ℝ) * (2 * Real.pi)) ka
    rw [show a - (ka : ℝ) * (2 * Real.pi) + (ka : ℝ) * (2 * Real.pi) = a from by ring] at this
    exact this.symm
  have hb' : c.γ (b - (kb : ℝ) * (2 * Real.pi)) = c.γ b := by
    have := c.apply_add_int_mul (b - (kb : ℝ) * (2 * Real.pi)) kb
    rw [show b - (kb : ℝ) * (2 * Real.pi) + (kb : ℝ) * (2 * Real.pi) = b from by ring] at this
    exact this.symm
  have heq : c.γ (a - (ka : ℝ) * (2 * Real.pi)) = c.γ (b - (kb : ℝ) * (2 * Real.pi)) := by
    rw [ha', hb', h]
  have hab : a - (ka : ℝ) * (2 * Real.pi) = b - (kb : ℝ) * (2 * Real.pi) := hs ha hb heq
  refine ⟨kb - ka, ?_⟩
  have hcast : ((kb - ka : ℤ) : ℝ) = (kb : ℝ) - (ka : ℝ) := by push_cast; ring
  rw [hcast, sub_mul]
  linarith

end Work.Smooth.Jordan

namespace Work.Smooth.JordanSeparation

open Work.Smooth.Jordan

noncomputable section

/-! ## The parameter shift of a curve -/

/-- The **parameter shift** `t ↦ c.γ (t + a)` of a smooth plane curve: it has the same trace as
`c`, and the same index off the trace. -/
def shiftCurve (c : SmoothPlaneCurve) (a : ℝ) : SmoothPlaneCurve where
  γ := fun t => c.γ (t + a)
  cont := c.cont.comp (continuous_id.add continuous_const)
  periodic := fun t => by
    show c.γ (t + 2 * Real.pi + a) = c.γ (t + a)
    rw [show t + 2 * Real.pi + a = t + a + 2 * Real.pi from by ring, c.periodic_apply]
  contDiff := c.contDiff.comp (contDiff_id.add contDiff_const)

@[simp] theorem shiftCurve_apply (c : SmoothPlaneCurve) (a t : ℝ) :
    (shiftCurve c a).γ t = c.γ (t + a) := rfl

@[simp] theorem shiftCurve_trace (c : SmoothPlaneCurve) (a : ℝ) :
    (shiftCurve c a).trace = c.trace := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t + a, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t - a, by simp⟩

theorem deriv_shiftCurve (c : SmoothPlaneCurve) (a t : ℝ) :
    deriv (shiftCurve c a).γ t = deriv c.γ (t + a) := by
  have hfun : (shiftCurve c a).γ = fun x : ℝ => c.γ (x + a) := rfl
  rw [hfun, deriv_comp_add_const]

theorem shiftCurve_isImmersion (c : SmoothPlaneCurve) (a : ℝ) (h : c.IsImmersion) :
    (shiftCurve c a).IsImmersion := by
  intro t
  rw [deriv_shiftCurve]
  exact h (t + a)

theorem unitTangent_shiftCurve (c : SmoothPlaneCurve) (a : ℝ) :
    unitTangent (shiftCurve c a) 0 = unitTangent c a := by
  simp only [unitTangent, deriv_shiftCurve, zero_add]

theorem normalField_shiftCurve (c : SmoothPlaneCurve) (a : ℝ) :
    normalField (shiftCurve c a) 0 = normalField c a := by
  simp only [normalField, unitTangent_shiftCurve]

theorem shiftCurve_isSimple (c : SmoothPlaneCurve) (a : ℝ) (hs : c.toPlaneCurve.IsSimple) :
    (shiftCurve c a).toPlaneCurve.IsSimple := by
  intro s hsI s' hs'I h
  have h' : c.γ (s + a) = c.γ (s' + a) := h
  obtain ⟨k, hk⟩ := hs.eq_mod_period h'
  have hks : s' = s + (k : ℝ) * (2 * Real.pi) := by linarith
  have hk0 : k = 0 := by
    have hkabs : |(k : ℝ)| * (2 * Real.pi) = |s' - s| := by
      have hc : (k : ℝ) * (2 * Real.pi) = s' - s := by linarith
      rw [← hc, abs_mul, abs_of_pos two_pi_pos]
    have hlt : |s' - s| < 2 * Real.pi := by
      rw [abs_lt]
      constructor <;> linarith [hsI.1, hsI.2, hs'I.1, hs'I.2]
    have h1 : |(k : ℝ)| < 1 := by nlinarith [two_pi_pos]
    have h2 : ((|k| : ℤ) : ℝ) < 1 := by rwa [Int.cast_abs]
    have h3 : |k| < 1 := by exact_mod_cast h2
    simpa using Int.abs_lt_one_iff.mp h3
  rw [hk0] at hks
  simpa using hks.symm

/-! ## The index is invariant under the parameter shift -/

theorem windingIntegrand_shiftCurve (c : SmoothPlaneCurve) (a : ℝ) (x : ℂ) (t : ℝ) :
    windingIntegrand (shiftCurve c a) x t = windingIntegrand c x (t + a) := by
  simp only [windingIntegrand_apply, shiftCurve_apply, deriv_shiftCurve]

theorem periodic_windingIntegrand (c : SmoothPlaneCurve) (x : ℂ) :
    Function.Periodic (windingIntegrand c x) (2 * Real.pi) := by
  intro t
  have hfun : (fun s : ℝ => c.γ (s + 2 * Real.pi)) = c.γ := funext fun s => c.periodic_apply s
  have hderiv : deriv c.γ (t + 2 * Real.pi) = deriv c.γ t := by
    rw [← deriv_comp_add_const c.γ (2 * Real.pi) t, hfun]
  simp only [windingIntegrand_apply, hderiv, c.periodic_apply t]

/-- **The winding integral is invariant under the parameter shift.** -/
theorem wind_shiftCurve (c : SmoothPlaneCurve) (a : ℝ) (x : ℂ) :
    wind (shiftCurve c a) x = wind c x := by
  have hper := periodic_windingIntegrand c x
  rw [wind_def, wind_def, windingPrimitive, windingPrimitive]
  congr 1
  have h1 : (∫ t in (0 : ℝ)..(2 * Real.pi), windingIntegrand (shiftCurve c a) x t)
      = ∫ t in (0 : ℝ)..(2 * Real.pi), windingIntegrand c x (t + a) := by
    apply intervalIntegral.integral_congr
    intro t _
    rw [windingIntegrand_shiftCurve]
  rw [h1, intervalIntegral.integral_comp_add_right, zero_add,
    show (2 : ℝ) * Real.pi + a = a + 2 * Real.pi from by ring]
  have h2 := hper.intervalIntegral_add_eq a 0
  rw [zero_add] at h2
  exact h2

/-- **The index is invariant under the parameter shift.** -/
theorem ind_shiftCurve (c : SmoothPlaneCurve) (a : ℝ) {x : ℂ} (hx : x ∉ c.trace) :
    ind (shiftCurve c a) x = ind c x := by
  have hx' : x ∉ (shiftCurve c a).trace := by rwa [shiftCurve_trace]
  have h1 := ind_spec (shiftCurve c a) (wind_mem_int (shiftCurve c a) hx')
  have h2 := ind_spec c (wind_mem_int c hx)
  rw [wind_shiftCurve c a x] at h1
  rw [← h2] at h1
  exact Int.cast_injective h1

/-! ## The index jump at an arbitrary parameter -/

/-- **The index jumps by one across the curve at every parameter.**  For a `C¹` immersed simple
closed plane curve `c` and every `t : ℝ` there is `δ > 0` such that for `0 < s < δ` the points
`c.γ t ± s·normalField c t` lie off the trace and their indices differ. -/
theorem ind_jump_at (c : SmoothPlaneCurve) (himm : c.IsImmersion) (hs : c.toPlaneCurve.IsSimple)
    (t : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s → s < δ →
      c.γ t + s * normalField c t ∉ c.trace ∧
      c.γ t - s * normalField c t ∉ c.trace ∧
      ind c (c.γ t + s * normalField c t) ≠ ind c (c.γ t - s * normalField c t) := by
  obtain ⟨δ, hδ, hjump⟩ :=
    ind_jump (shiftCurve c t) (shiftCurve_isImmersion c t himm) (shiftCurve_isSimple c t hs)
  refine ⟨δ, hδ, fun s hs0 hsδ => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hjump s hs0 hsδ
  have h1' : c.γ t + s * normalField c t ∉ c.trace := by
    simpa only [shiftCurve_apply, zero_add, normalField_shiftCurve, shiftCurve_trace] using h1
  have h2' : c.γ t - s * normalField c t ∉ c.trace := by
    simpa only [shiftCurve_apply, zero_add, normalField_shiftCurve, shiftCurve_trace] using h2
  refine ⟨h1', h2', ?_⟩
  have h3' : ind (shiftCurve c t) (c.γ t + s * normalField c t)
      = ind (shiftCurve c t) (c.γ t - s * normalField c t) + 1 := by
    simpa only [shiftCurve_apply, zero_add, normalField_shiftCurve] using h3
  have e1 : ind (shiftCurve c t) (c.γ t + s * normalField c t)
      = ind c (c.γ t + s * normalField c t) := ind_shiftCurve c t h1'
  have e2 : ind (shiftCurve c t) (c.γ t - s * normalField c t)
      = ind c (c.γ t - s * normalField c t) := ind_shiftCurve c t h2'
  rw [e1, e2] at h3'
  intro heq
  rw [heq] at h3'
  omega

/-! ## The main theorem -/

theorem frontier_eq_trace (c : Work.Smooth.Jordan.SmoothPlaneCurve)
    (himm : Work.Smooth.Jordan.SmoothPlaneCurve.IsImmersion c) (hs : c.toPlaneCurve.IsSimple)
    {S : Work.Smooth.Jordan.PlaneSeparation c.toPlaneCurve} :
    frontier S.U = c.trace := by
  apply Set.Subset.antisymm
  · -- a point of the frontier of `U` lies on the curve
    rw [S.isOpen_U.frontier_eq]
    rintro x ⟨hxcl, hxU⟩
    by_contra hxt
    have hxu : x ∈ S.U ∪ S.V := by rw [S.union_eq]; exact hxt
    rcases hxu with h | h
    · exact hxU h
    · obtain ⟨y, hyV, hyU⟩ := mem_closure_iff.mp hxcl S.V S.isOpen_V h
      exact Set.disjoint_left.mp S.disjoint_UV hyU hyV
  · -- every point of the curve is in `U`'s closure and off `U`
    rintro x ⟨t, rfl⟩
    have hxU : c.γ t ∉ S.U := by
      intro h
      have : c.γ t ∈ c.traceᶜ := by rw [← S.union_eq]; exact Or.inl h
      exact this ⟨t, rfl⟩
    have hxcl : c.γ t ∈ closure S.U := by
      rw [mem_closure_iff]
      intro o ho hxo
      obtain ⟨ε, hε, hεo⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds hxo)
      obtain ⟨δ, hδ, hjump⟩ := ind_jump_at c himm hs t
      set s : ℝ := min (δ / 2) (ε / 2) with hsdef
      have hs0 : 0 < s := lt_min (by linarith) (by linarith)
      have hsδ : s < δ := by
        rw [hsdef]
        exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hsε : s < ε := by
        rw [hsdef]
        exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
      obtain ⟨h1, h2, h3⟩ := hjump s hs0 hsδ
      -- one of the two normal offsets lies on the `U` side
      have hside : c.γ t + s * normalField c t ∈ S.U ∨
          c.γ t - s * normalField c t ∈ S.U := by
        have hp : c.γ t + s * normalField c t ∈ S.U ∨
            c.γ t + s * normalField c t ∈ S.V := by
          have hmem : c.γ t + s * normalField c t ∈ c.traceᶜ := h1
          rw [← S.union_eq] at hmem
          exact hmem
        have hm : c.γ t - s * normalField c t ∈ S.U ∨
            c.γ t - s * normalField c t ∈ S.V := by
          have hmem : c.γ t - s * normalField c t ∈ c.traceᶜ := h2
          rw [← S.union_eq] at hmem
          exact hmem
        rcases hp with h | h
        · exact Or.inl h
        · rcases hm with h' | h'
          · exact Or.inr h'
          · exact absurd (ind_const_on_preconnected c S.preconn_V
              (fun w hw => by rw [← S.union_eq]; exact Or.inr hw) h h') h3
      have hdist : ∀ u : ℝ, ‖u * normalField c t‖ = |u| := by
        intro u
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_normalField c himm t, mul_one]
      rcases hside with hU | hU
      · refine ⟨c.γ t + s * normalField c t, hεo ?_, hU⟩
        rw [Metric.mem_ball, dist_eq_norm,
          show c.γ t + s * normalField c t - c.γ t = s * normalField c t from by ring, hdist,
          abs_of_pos hs0]
        exact hsε
      · refine ⟨c.γ t - s * normalField c t, hεo ?_, hU⟩
        rw [Metric.mem_ball, dist_eq_norm,
          show c.γ t - s * normalField c t - c.γ t = -(s * normalField c t) from by ring,
          norm_neg, hdist, abs_of_pos hs0]
        exact hsε
    rw [S.isOpen_U.frontier_eq]
    exact ⟨hxcl, hxU⟩

end

end Work.Smooth.JordanSeparation
