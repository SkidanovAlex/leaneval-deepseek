import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.Jordan.All
import Submission.Work.Smooth.SphereJordan.BoundedSide
import Submission.Work.Smooth.SphereJordan.PCopy.annulusTheoremOfPlaneHypothesis

/-!
# The planar annulus theorem, from the planar Jordan–Schoenflies theorem

`Work.Smooth.SphereJordan.annulus_of_planeHypothesis`: for a simple closed plane curve `γ` whose
trace lies in the open unit disc and a Schoenflies datum `S` for it, there is a homeomorphism `Θ`
of the closed unit disc which fixes the boundary circle pointwise and carries `closure S.V` (the
closed disc bounded by `γ`) onto the closed disc of radius `1/2`.

The mathematical content is the two-dimensional **annulus theorem**: the region between a Jordan
curve inside the open unit disc and the boundary circle of the disc is a standard annulus.

This file collects the *setup* of the configuration: the bounded side lies in the open disc, the
boundary circle of the model disc lies on the unbounded side, and consequently `closure S.V` is a
closed disc contained in the *open* disc (which is what makes the annulus between `γ` and `∂𝔻`
non-degenerate).
-/

open Set
open LeanEval.KnotTheory.PardonDistortion

namespace Work.Smooth.SphereJordan

noncomputable section

/-- The set of points of the plane of norm `1` is the sphere of radius `1`. -/
theorem mem_sphere_one_iff (z : ℂ) : z ∈ Metric.sphere (0 : ℂ) 1 ↔ ‖z‖ = 1 := by
  rw [Metric.mem_sphere, dist_eq_norm]
  simp

/-- The sphere of radius `1` in the plane is preconnected. -/
theorem isPreconnected_sphere_one : IsPreconnected (Metric.sphere (0 : ℂ) 1) := by
  have hrank : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
  exact isPreconnected_sphere hrank 0 1

/-- **The unbounded side is closed in the complement of the trace**: it is the complement of the
open bounded side there. -/
theorem exists_isClosed_U {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSeparation γ) :
    ∃ Z : Set ℂ, IsClosed Z ∧ S.U = γ.traceᶜ ∩ Z :=
  ⟨S.Vᶜ, S.isOpen_V.isClosed_compl, by
    ext z
    constructor
    · intro hz
      exact ⟨by rw [← S.union_eq]; exact Or.inl hz,
        fun hzv => Set.disjoint_left.mp S.disjoint_UV hz hzv⟩
    · rintro ⟨hz, hzv⟩
      have : z ∈ S.U ∪ S.V := by rw [S.union_eq]; exact hz
      rcases this with h | h
      · exact h
      · exact absurd h hzv⟩

/-- **The boundary circle of the model disc lies on the unbounded side** of a simple closed plane
curve whose trace lies in the open unit disc. -/
theorem sphere_subset_U {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) :
    Metric.sphere (0 : ℂ) 1 ⊆ S.U := by
  have hext_pre : IsPreconnected {w : ℂ | 1 < ‖w‖} :=
    Work.Smooth.Jordan.isPreconnected_exterior_unitBall
  have hext_sub : {w : ℂ | 1 < ‖w‖} ⊆ γ.traceᶜ := by
    rintro w hw ⟨θ, hθ⟩
    rw [← hθ] at hw
    exact absurd (hball θ) (not_lt.mpr hw.le)
  obtain hU | hV :=
    Work.Smooth.Jordan.plane_separation_preconnected_subset S.toPlaneSeparation hext_pre hext_sub
  · intro z hz
    have hz' : ‖z‖ = 1 := mem_sphere_one_iff z |>.mp hz
    have hztrace : z ∉ γ.trace := by
      rintro ⟨θ, hθ⟩
      rw [← hθ] at hz'
      linarith [hball θ]
    have hzUV : z ∈ S.U ∪ S.V := by rw [S.union_eq]; exact hztrace
    rcases hzUV with h | h
    · exact h
    · -- `z ∈ V` is impossible: a neighbourhood of `z` lies in `V` and contains exterior points,
      -- which lie on the unbounded side
      exfalso
      obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp (S.isOpen_V.mem_nhds h)
      have hnormε : ‖((ε / 2 : ℝ) : ℂ)‖ = ε / 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      have hnorm1 : ‖((1 + ε / 2 : ℝ) : ℂ)‖ = 1 + ε / 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      set w : ℂ := z * (((1 + ε / 2 : ℝ)) : ℂ) with hwdef
      have hmem : w ∈ Metric.ball z ε := by
        rw [Metric.mem_ball, dist_eq_norm]
        have h1 : w - z = z * ((ε / 2 : ℝ) : ℂ) := by
          rw [hwdef]; push_cast; ring
        rw [h1, norm_mul, hz', one_mul, hnormε]
        linarith
      have hwV : w ∈ S.V := hεV hmem
      have hwnorm : 1 < ‖w‖ := by
        rw [hwdef, norm_mul, hz', one_mul, hnorm1]; linarith
      exact Set.disjoint_left.mp S.disjoint_UV (hU hwnorm) hwV
  · -- the exterior would be contained in the bounded side, which is bounded
    exfalso
    obtain ⟨C, hC⟩ := S.bounded_V.exists_norm_le
    obtain ⟨x, hx⟩ := S.nonempty_V
    have hC0 : 0 ≤ C := le_trans (norm_nonneg x) (hC x hx)
    set w : ℂ := ((C + 2 : ℝ) : ℂ) with hwdef
    have hwnorm : ‖w‖ = C + 2 := by
      rw [hwdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have h1 : 1 < ‖w‖ := by rw [hwnorm]; linarith
    have := hC w (hV h1)
    rw [hwnorm] at this
    linarith

/-- **The closure of the bounded side is the union of the bounded side and the trace.** -/
theorem closure_V_eq {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    closure S.V = S.V ∪ γ.trace := by
  refine Set.Subset.antisymm ?_ ?_
  · intro z hz
    have hz' : z ∈ Set.range S.e := by rw [S.range_e]; exact hz
    obtain ⟨w, rfl⟩ := hz'
    have hw1 : ‖(w : ℂ)‖ ≤ 1 := by
      have h : dist (w : ℂ) 0 ≤ 1 := w.2
      rwa [dist_zero_right] at h
    rcases lt_or_eq_of_le hw1 with hlt | heq
    · left
      rw [← Work.Smooth.Jordan.plane_schoenflies_openDisc_eq S]
      exact ⟨w, hlt, rfl⟩
    · right
      obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq w heq
      rw [← hθ]
      exact ⟨θ, (S.boundary θ).symm⟩
  · refine union_subset subset_closure ?_
    rintro _ ⟨θ, rfl⟩
    rw [← S.range_e]
    exact ⟨Work.Smooth.Jordan.circlePoint θ, S.boundary θ⟩

/-- **The closed disc bounded by the curve is contained in the open unit disc.** -/
theorem closure_V_subset_openBall {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) :
    closure S.V ⊆ {z : ℂ | ‖z‖ < 1} := by
  rw [closure_V_eq S]
  intro z hz
  rcases hz with hz | hz
  · refine lt_of_le_of_ne
      (Work.Smooth.SphereJordan.planeSeparation_V_subset_closedBall S.toPlaneSeparation hball z hz) ?_
    intro h1
    exact Set.disjoint_left.mp S.disjoint_UV
      (sphere_subset_U S hball (mem_sphere_one_iff z |>.mpr h1)) hz
  · obtain ⟨θ, rfl⟩ := hz
    exact hball θ

/-- The trace of the curve is contained in the closed annulus `𝔻 ∖ S.V`. -/
theorem trace_subset_annulusRing {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) :
    γ.trace ⊆ Metric.closedBall (0 : ℂ) 1 \ S.V := by
  rintro _ ⟨θ, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right]
    exact (hball θ).le
  · intro hmem
    have hVsub : S.V ⊆ γ.traceᶜ := by
      intro x hx
      have : x ∈ S.U ∪ S.V := Or.inr hx
      rw [S.union_eq] at this
      exact this
    exact hVsub hmem ⟨θ, rfl⟩


/-! ## Crosscuts of the annulus `𝔻 ∖ S.V`

The region between the Jordan curve `γ` and the boundary circle of the disc is cut into two closed
discs by the two "outer" parts of a line through a point of the bounded side.  In this section we
construct those two crosscuts explicitly.

The crosscut along the ray from the base point `base = S.e 0` in the direction of a unit vector `u`
is the straight segment from the *last* point of `closure S.V` on the ray to the point where the
ray leaves the closed unit disc.  The two facts that make it a crosscut are that the segment meets
`closure S.V` exactly in its inner endpoint and `∂𝔻` exactly in its outer endpoint, and that the
whole segment lies in `𝔻`. -/

/-- The point of the model disc corresponding to the centre of the disc. -/
def discCentre : Work.Smooth.SphereJordan.Disc :=
  ⟨0, by rw [Metric.mem_closedBall, dist_zero_right]; norm_num⟩

@[simp] theorem discCentre_coe : ((discCentre : Work.Smooth.SphereJordan.Disc) : ℂ) = 0 := rfl

/-- The base point of the annulus: the image of the centre of the model disc under the Schoenflies
embedding.  It lies in the bounded side. -/
def base {γ : Work.Smooth.Jordan.PlaneCurve} (S : Work.Smooth.Jordan.PlaneSchoenflies γ) : ℂ :=
  S.e discCentre

theorem base_mem_V {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) : base S ∈ S.V := by
  have h := Work.Smooth.Jordan.plane_schoenflies_openDisc_eq S
  rw [← h]
  exact ⟨discCentre, by simp [discCentre_coe], rfl⟩

/-- `base` lies in the closed disc bounded by the curve (which is contained in the open disc). -/
theorem base_mem_K {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) : base S ∈ closure S.V :=
  subset_closure (base_mem_V S)

/-- A small neighbourhood of the base point lies in the closed disc bounded by the curve. -/
theorem exists_ball_base_subset_K {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : ℂ, ‖z - base S‖ < ρ → z ∈ closure S.V := by
  have hV : S.V ⊆ closure S.V := subset_closure
  obtain ⟨ε, hε, hε'⟩ := Metric.mem_nhds_iff.mp (S.isOpen_V.mem_nhds (base_mem_V S))
  refine ⟨ε, hε, fun z hz => hV (hε' ?_)⟩
  rw [Metric.mem_ball, dist_eq_norm]
  exact hz

/-- **The set of parameters for which the ray from the base point in a given direction meets the
closed disc bounded by the curve is compact.** -/
theorem isCompact_rayParams {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1)
    (u : ℂ) (hu : u ≠ 0) :
    IsCompact {t : ℝ | 0 ≤ t ∧ base S + t • u ∈ closure S.V} := by
  have hKc : IsCompact (closure S.V) := by
    rw [← S.range_e]
    exact isCompact_range S.e.continuous
  obtain ⟨C, hC⟩ := hKc.isBounded.exists_norm_le
  have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr hu
  refine IsCompact.of_isClosed_subset
    (isCompact_Icc (a := 0) (b := (C + ‖base S‖) / ‖u‖ + 1)) ?_ ?_
  · exact IsClosed.inter isClosed_Ici
      (isClosed_closure.preimage (by fun_prop : Continuous fun t : ℝ => base S + t • u))
  · rintro t ⟨ht0, htK⟩
    refine ⟨ht0, ?_⟩
    have h1 : ‖base S + t • u‖ ≤ C := hC _ htK
    have h2 : ‖t • u‖ ≤ ‖base S + t • u‖ + ‖base S‖ := by
      have := norm_add_le (base S + t • u) (-(base S))
      rw [show base S + t • u + -(base S) = t • u by abel, norm_neg] at this
      exact this
    rw [norm_smul, Real.norm_eq_abs] at h2
    have h3 : |t| * ‖u‖ ≤ C + ‖base S‖ := by linarith
    have h4 : |t| ≤ (C + ‖base S‖) / ‖u‖ := by
      rw [le_div_iff₀ hu0]; linarith
    have h5 : t ≤ (C + ‖base S‖) / ‖u‖ := le_trans (le_abs_self t) h4
    linarith

/-- **The last point of the closed disc bounded by the curve on the ray from the base point** in a
given direction. -/
theorem exists_lastExit {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1)
    (u : ℂ) (hu : u ≠ 0) :
    ∃ t : ℝ, 0 ≤ t ∧ base S + t • u ∈ closure S.V ∧
      ∀ t' : ℝ, t < t' → base S + t' • u ∉ closure S.V := by
  have hc := isCompact_rayParams S hball u hu
  have hne : ({t : ℝ | 0 ≤ t ∧ base S + t • u ∈ closure S.V}).Nonempty :=
    ⟨0, le_refl 0, by simpa using base_mem_K S⟩
  obtain ⟨t, ht, htmax⟩ := hc.exists_isMaxOn hne continuous_id.continuousOn
  refine ⟨t, ht.1, ht.2, ?_⟩
  intro t' ht' hcon
  have hmem : t' ∈ {t : ℝ | 0 ≤ t ∧ base S + t • u ∈ closure S.V} :=
    ⟨le_trans ht.1 ht'.le, hcon⟩
  exact absurd (htmax hmem) (not_le.mpr ht')

/-- **The point where the ray leaves the closed unit disc.**  Starting from a parameter at which
the ray is inside the open disc, the first parameter at which the norm is `1` bounds a segment
lying in the open disc. -/
theorem exists_outExit {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1)
    (u : ℂ) (hu : u ≠ 0) {t₀ : ℝ} (ht₀0 : 0 ≤ t₀) (ht₀ : ‖base S + t₀ • u‖ < 1) :
    ∃ s : ℝ, t₀ ≤ s ∧ ‖base S + s • u‖ = 1 ∧ ∀ t : ℝ, t₀ ≤ t → t < s →
      ‖base S + t • u‖ < 1 := by
  have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr hu
  set Sset : Set ℝ := {t : ℝ | t₀ ≤ t ∧ ‖base S + t • u‖ = 1} with hSset
  have hclosed : IsClosed Sset :=
    IsClosed.inter isClosed_Ici
      (isClosed_eq (by fun_prop : Continuous fun t : ℝ => ‖base S + t • u‖) continuous_const)
  have hne : Sset.Nonempty := by
    set t₁ : ℝ := t₀ + (1 + ‖base S‖) / ‖u‖ with ht₁def
    have ht₁ge : t₀ ≤ t₁ := by
      rw [ht₁def]
      have : 0 ≤ (1 + ‖base S‖) / ‖u‖ := by positivity
      linarith
    have hval : 1 ≤ ‖base S + t₁ • u‖ := by
      have h2 : ‖t₁ • u‖ = t₁ * ‖u‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_trans ht₀0 ht₁ge)]
      have h3 : 1 + ‖base S‖ ≤ t₁ * ‖u‖ := by
        have h4 : (1 + ‖base S‖) / ‖u‖ ≤ t₁ := by rw [ht₁def]; linarith
        calc 1 + ‖base S‖ = (1 + ‖base S‖) / ‖u‖ * ‖u‖ :=
              (div_mul_cancel₀ _ (ne_of_gt hu0)).symm
          _ ≤ t₁ * ‖u‖ := by nlinarith [hu0]
      have h1 : ‖t₁ • u‖ - ‖base S‖ ≤ ‖base S + t₁ • u‖ := by
        have h := norm_add_le (base S + t₁ • u) (-(base S))
        rw [show base S + t₁ • u + -(base S) = t₁ • u by abel, norm_neg] at h
        linarith
      rw [h2] at h1
      linarith
    have hcont : Continuous fun t : ℝ => ‖base S + t • u‖ := by fun_prop
    obtain ⟨s, hs, hsv⟩ := intermediate_value_Icc ht₁ge hcont.continuousOn
      (show (1:ℝ) ∈ Set.Icc (‖base S + t₀ • u‖) (‖base S + t₁ • u‖) from ⟨ht₀.le, hval⟩)
    exact ⟨s, hs.1, hsv⟩
  have hbdd : BddBelow Sset := ⟨t₀, fun t ht => ht.1⟩
  set s : ℝ := sInf Sset with hsdef
  have hsS : s ∈ Sset := hclosed.csInf_mem hne hbdd
  refine ⟨s, hsS.1, hsS.2, ?_⟩
  intro t ht0 hts
  by_contra hcon
  have hge : 1 ≤ ‖base S + t • u‖ := not_lt.mp hcon
  rcases lt_or_eq_of_le hge with hlt | heq
  · have hcont : Continuous fun x : ℝ => ‖base S + x • u‖ := by fun_prop
    have hmem : (1:ℝ) ∈ Set.Icc (‖base S + t₀ • u‖) (‖base S + t • u‖) :=
      ⟨ht₀.le, le_of_lt hlt⟩
    obtain ⟨x, hx, hxv⟩ := intermediate_value_Icc ht0 hcont.continuousOn hmem
    have hxS : x ∈ Sset := ⟨hx.1, hxv⟩
    have hxs : x < s := lt_of_le_of_lt hx.2 hts
    exact absurd (csInf_le hbdd hxS) (not_le.mpr hxs)
  · have hs1 : ‖base S + t • u‖ = 1 := heq.symm
    have htS : t ∈ Sset := ⟨ht0, hs1⟩
    exact absurd (csInf_le hbdd htS) (not_le.mpr hts)

/-! ## The two crosscuts of the annulus

For a direction `u`, the *crosscut* is the straight segment from the last point of `closure S.V` on
the ray from the base point in direction `u` to the point where the ray leaves the closed unit disc.
The two facts that make it a crosscut are that the segment meets `closure S.V` exactly in its inner
endpoint (which lies on the trace `γ`) and `∂𝔻` exactly in its outer endpoint. -/

open Filter in
/-- **The inner endpoint of the crosscut.**  Along the ray from the base point in a nonzero
direction there is a last point of the closed disc bounded by the curve; it lies on the trace, and
beyond it the ray misses the closed disc. -/
theorem exists_crosscut_inner {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1)
    (u : ℂ) (hu : u ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ base S + t • u ∈ γ.trace ∧
      ∀ t' : ℝ, t < t' → base S + t' • u ∉ closure S.V := by
  obtain ⟨t, ht0, htK, htmax⟩ := exists_lastExit S hball u hu
  -- a small positive parameter already puts the ray inside the bounded side
  have hsmall : ∃ ε : ℝ, 0 < ε ∧ base S + ε • u ∈ S.V := by
    obtain ⟨ρ, hρ, hρV⟩ := Metric.mem_nhds_iff.mp (S.isOpen_V.mem_nhds (base_mem_V S))
    refine ⟨ρ / (2 * (1 + ‖u‖)), by positivity, hρV ?_⟩
    rw [Metric.mem_ball, dist_eq_norm]
    have h1 : ‖(base S + (ρ / (2 * (1 + ‖u‖))) • u) - base S‖
        = ρ / (2 * (1 + ‖u‖)) * ‖u‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ ρ / (2 * (1 + ‖u‖)))]
    rw [h1]
    calc ρ / (2 * (1 + ‖u‖)) * ‖u‖ ≤ ρ / (2 * (1 + ‖u‖)) * (1 + ‖u‖) :=
          mul_le_mul_of_nonneg_left (by linarith [norm_nonneg u]) (by positivity)
      _ = ρ / 2 := by field_simp
      _ < ρ := by linarith
  obtain ⟨ε, hε, hεV⟩ := hsmall
  have htge : ε ≤ t := by
    by_contra hcon
    exact htmax ε (not_le.mp hcon) (subset_closure hεV)
  have htpos : 0 < t := lt_of_lt_of_le hε htge
  have hcont : Continuous fun σ : ℝ => base S + σ • u := by fun_prop
  -- the inner endpoint is not in the open bounded side
  have hnotV : base S + t • u ∉ S.V := by
    intro htV
    obtain ⟨ρ, hρ, hρV⟩ := Metric.mem_nhds_iff.mp (S.isOpen_V.mem_nhds htV)
    have hmem : ∀ᶠ σ : ℝ in nhds t, base S + σ • u ∈ S.V := by
      have h1 : ∀ᶠ σ : ℝ in nhds t, base S + σ • u ∈ Metric.ball (base S + t • u) ρ :=
        hcont.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hρ)
      filter_upwards [h1] with σ hσ using hρV hσ
    have hmem' : ∀ᶠ σ : ℝ in nhdsWithin t (Ioi t), base S + σ • u ∈ S.V :=
      hmem.filter_mono nhdsWithin_le_nhds
    obtain ⟨σ, hσV, hσt⟩ := (hmem'.and self_mem_nhdsWithin).exists
    exact htmax σ hσt (subset_closure hσV)
  have htΓ : base S + t • u ∈ γ.trace := by
    have hmem : base S + t • u ∈ closure S.V \ S.V := ⟨htK, hnotV⟩
    rw [closure_V_eq S] at hmem
    rcases hmem.1 with h | h
    · exact absurd h hnotV
    · exact h
  exact ⟨t, htpos, htΓ, htmax⟩

/-- **The outer endpoint of the crosscut.**  Starting at the inner endpoint, the ray meets the
boundary circle of the disc, and before that point it lies in the open disc. -/
theorem exists_crosscut_outer {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1)
    (u : ℂ) (hu : u ≠ 0) {t : ℝ} (ht0 : 0 ≤ t) (htK : base S + t • u ∈ closure S.V) :
    ∃ s : ℝ, t ≤ s ∧ base S + s • u ∈ Metric.sphere (0 : ℂ) 1 ∧
      ∀ t' : ℝ, t ≤ t' → t' < s → base S + t' • u ∈ Metric.ball (0 : ℂ) 1 := by
  have ht_norm : ‖base S + t • u‖ < 1 := closure_V_subset_openBall S hball htK
  obtain ⟨s, hts, hsn, hs⟩ := exists_outExit S hball u hu ht0 ht_norm
  refine ⟨s, hts, ?_, ?_⟩
  · rw [mem_sphere_one_iff]; exact hsn
  · intro t' ht' ht's
    rw [Metric.mem_ball, dist_zero_right]
    exact hs t' ht' ht's

/-- **The crosscut is contained in the annulus.**  There are parameters `0 < t < s` with
`base + t • u` on the curve and `base + s • u` on the boundary circle; every parameter in between
gives a point of the open disc outside the bounded side, and every parameter in `[t,s]` gives a
point of the closed disc. -/
theorem crosscut_mem_annulus {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1)
    (u : ℂ) (hu : u ≠ 0) :
    ∃ t s : ℝ, 0 < t ∧ t < s ∧ base S + t • u ∈ γ.trace ∧
      base S + s • u ∈ Metric.sphere (0 : ℂ) 1 ∧
      (∀ σ : ℝ, t < σ → σ < s → base S + σ • u ∈ Metric.ball (0 : ℂ) 1 \ S.V) ∧
      (∀ σ : ℝ, t ≤ σ → σ ≤ s → base S + σ • u ∈ Metric.closedBall (0 : ℂ) 1) := by
  obtain ⟨t, htpos, htΓ, htmax⟩ := exists_crosscut_inner S hball u hu
  have htK : base S + t • u ∈ closure S.V := by
    rw [closure_V_eq S]; exact Or.inr htΓ
  obtain ⟨s, hts, hsn, hs⟩ := exists_crosscut_outer S hball u hu htpos.le htK
  have hts' : t < s := by
    rcases lt_or_eq_of_le hts with h | h
    · exact h
    · exfalso
      have h1 : ‖base S + t • u‖ = 1 := by rw [h]; exact mem_sphere_one_iff _ |>.mp hsn
      have h2 : ‖base S + t • u‖ < 1 := closure_V_subset_openBall S hball htK
      exact absurd h1 (ne_of_lt h2)
  refine ⟨t, s, htpos, hts', htΓ, hsn, ?_, ?_⟩
  · intro σ htσ hσs
    refine ⟨?_, fun hV => htmax σ htσ (subset_closure hV)⟩
    simpa [dist_eq_norm] using Metric.mem_ball.mp (hs σ htσ.le hσs)
  · intro σ htσ hσs
    rw [Metric.mem_closedBall, dist_zero_right]
    rcases lt_or_eq_of_le hσs with h | h
    · have hlt : ‖base S + σ • u‖ < 1 := by
        have hb := Metric.mem_ball.mp (hs σ htσ h)
        rw [dist_eq_norm] at hb
        simpa using hb
      exact le_of_lt hlt
    · have hsn' : ‖base S + s • u‖ = 1 := mem_sphere_one_iff _ |>.mp hsn
      rw [h, hsn']

/-! ## The theorem

For a simple closed plane curve `γ` whose trace lies in the open unit disc and a Schoenflies datum
`S` for it, there is a homeomorphism `Θ` of the closed unit disc which fixes the boundary circle
pointwise and carries `closure S.V` (the closed disc bounded by `γ`) onto the closed disc of radius
`1/2`.

The mathematical content is the two-dimensional **annulus theorem**: the region between a Jordan
curve inside the open unit disc and the boundary circle of the disc is a standard annulus, and the
homeomorphism may be prescribed on the outer boundary circle.

### How the proof is obtained (and why it is not written out here)

The two-cuts construction that proves the annulus theorem — cut the annulus along two crosscuts
joining `γ` to `∂𝔻`, straighten each of the two resulting discs by the planar Jordan–Schoenflies
theorem and glue — is *already formalised in this workspace*, in the modules of
`Submission/Work/SphereJordan/` and `Submission/Work/Smooth/SphereJordan/`:

  `Work.Smooth.SphereJordan.annulusTheoremOfPlaneHypothesis`,
  `…annulusInjectionTwoCutsAlt`, `…annulusClosureCore_of_injection`, `…strictClause_of_closureClause`
  (and `…annulusStrictCore` ⟶ `…annulusTheoremOfPlaneHypothesis` ⟶ `…plainAnnulusSchoenflies`).

None of those modules, however, can be imported *here*: every one of them imports **this** file, for
the setup lemmas above (`closure_V_eq`, `closure_V_subset_openBall`, `sphere_subset_U`, `base`,
`exists_crosscut_inner`, `crosscut_mem_annulus`, …, used by name in more than forty modules), so
importing them back would close an import cycle.

The way out taken here is a *renamed copy* of the part of that chain on which the theorem depends.
The directory `Submission/Work/Smooth/SphereJordan/PCopy/` contains

* `Setup.lean` — a copy of the setup lemmas above (identical names: this is a *different* module, so
  there is no clash with this file);
* one module per workspace module of the two-cuts chain (the transitive dependency closure of
  `annulusTheoremOfPlaneHypothesis` inside the modules importing this file), copied verbatim except
  that (i) their import of *this* file is redirected to `PCopy/Setup.lean`, and (ii) every
  declaration they introduce is renamed by a `pc` prefix on its last component.  The renaming keeps
  the copies from clashing with the originals in modules that import both (every module importing
  this file also sees the renamed copies through it), and the redirection of the single import of
  this file breaks the cycle at exactly one point.

The declaration used below is therefore the renamed form
`pcannulusTheoremOfPlaneHypothesis` of `annulusTheoremOfPlaneHypothesis`; it has the same statement
(the strict clause and the closure clause), and `#print axioms` shows that it rests only on
`propext`, `Classical.choice` and `Quot.sound`.  Only its first and third clauses (the boundary
fixity and the closure clause) are needed here.
-/
theorem annulus_of_planeHypothesis (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    {γ : Work.Smooth.Jordan.PlaneCurve} (hs : γ.IsSimple) (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1)
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    ∃ Θ : Work.Smooth.SphereJordan.Disc ≃ₜ Work.Smooth.SphereJordan.Disc,
      (∀ θ : ℝ, Θ (Work.Smooth.SphereJordan.circlePoint θ) = Work.Smooth.SphereJordan.circlePoint θ) ∧
      (∀ x : Work.Smooth.SphereJordan.Disc,
        (((x : Work.Smooth.SphereJordan.Disc) : ℂ) ∈ closure S.V) ↔
        ‖((Θ x : Work.Smooth.SphereJordan.Disc) : ℂ)‖ ≤ 1 / 2) := by
  obtain ⟨Θ, hfix, -, hcl⟩ :=
    Work.Smooth.SphereJordan.pcannulusTheoremOfPlaneHypothesis h hs hball S
  exact ⟨Θ, hfix, hcl⟩

end

end Work.Smooth.SphereJordan
