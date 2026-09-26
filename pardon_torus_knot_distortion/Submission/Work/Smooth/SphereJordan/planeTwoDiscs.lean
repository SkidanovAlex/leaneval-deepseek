import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.mobiusAddInv

/-!
# The planar two-disc theorem: a simple closed plane curve bounds two discs

The planar Jordan--Schoenflies theorem (`PlaneHypothesis`) provides, for a simple closed plane
curve `γ`, an embedded disc spanning the bounded side of `γ`.  Here we prove the *two*-disc
statement on the Riemann sphere `ℂ ∪ {∞}`: a simple closed plane curve is the common boundary of
two embedded discs, the second one being the closure of the unbounded side together with `∞`.

The construction is the classical one.  Choose a point `z₀` of the bounded side `V` of `γ`; the
inversion `φ(w) = (w - z₀)⁻¹` is a self-homeomorphism of the Riemann sphere which carries `γ` to
the simple closed plane curve `γ'(t) = (γ t - z₀)⁻¹` and interchanges the two sides: the bounded
side `V` of `γ` (which contains `z₀`) is carried to the *unbounded* side `Ũ` of `γ'`, and the
unbounded side `U` of `γ` to the bounded side `Ṽ` of `γ'`.  Applying the planar theorem a second
time to `γ'` produces a spanning disc of `Ṽ`, and pulling it back along `φ⁻¹(w) = z₀ + w⁻¹` gives
the disc spanning the closure of the unbounded side of `γ`.

The only point requiring a little care is the identification of the sides under the inversion;
it is proved by connectedness: the image of `V` under `φ` is a connected subset of the complement
of `γ'` containing `∞`, hence (as `Ṽ` is bounded) it is contained in `Ũ = Ũ ∪ {∞}`; the same
argument applied to the two-disc cut of the sphere by `γ` and the preconnectedness of the image
of `U` then identifies the images of `U` and `V` with `Ṽ` and `Ũ` respectively.
-/

open Set Filter
open scoped Topology

namespace Work.Smooth.SphereJordan

noncomputable section

/-! ## Elementary consequences of a plane Schoenflies datum -/

/-- The closure of the bounded side of a plane Schoenflies datum is the bounded side together with
the curve. -/
theorem planeTwoDiscs_closure_V (c : Work.Smooth.Jordan.PlaneCurve)
    (d : Work.Smooth.Jordan.PlaneSchoenflies c) :
    closure d.V = d.V ∪ c.trace := by
  apply Set.Subset.antisymm
  · have hclosed : IsClosed (d.V ∪ c.trace) := by
      have hcompl : (d.V ∪ c.trace)ᶜ = d.U := by
        ext x
        constructor
        · intro hx
          have hxV : x ∉ d.V := fun h => hx (Or.inl h)
          have hxt : x ∉ c.trace := fun h => hx (Or.inr h)
          have hxt' : x ∈ c.traceᶜ := hxt
          rw [← d.union_eq] at hxt'
          rcases hxt' with h | h
          · exact h
          · exact absurd h hxV
        · intro hx
          rintro (h | h)
          · exact Set.disjoint_left.mp d.disjoint_UV hx h
          · have : x ∈ d.U ∪ d.V := Or.inl hx
            rw [d.union_eq] at this
            exact this h
      have heq : d.V ∪ c.trace = d.Uᶜ := by
        rw [← compl_compl (d.V ∪ c.trace), hcompl]
      rw [heq]
      exact d.isOpen_U.isClosed_compl
    exact hclosed.closure_subset_iff.mpr Set.subset_union_left
  · intro x hx
    rcases hx with hx | hx
    · exact subset_closure hx
    · obtain ⟨θ, rfl⟩ := hx
      rw [← d.range_e]
      exact ⟨Work.Smooth.Jordan.circlePoint θ, d.boundary θ⟩

/-- A plane Jordan separation has an explicit bound on the complement of its unbounded side. -/
theorem planeTwoDiscs_norm_bound (c : Work.Smooth.Jordan.PlaneCurve)
    (d : Work.Smooth.Jordan.PlaneSeparation c) :
    ∃ R : ℝ, ∀ x : ℂ, x ∉ d.U → ‖x‖ ≤ R := by
  obtain ⟨r, hr⟩ := d.bounded_V.subset_closedBall (0 : ℂ)
  obtain ⟨s, hs⟩ := c.isCompact_trace.isBounded.subset_closedBall (0 : ℂ)
  refine ⟨max r s, fun x hx => ?_⟩
  by_cases hxt : x ∈ c.trace
  · exact le_trans (by simpa using hs hxt) (le_max_right _ _)
  · have hx' : x ∈ c.traceᶜ := hxt
    rw [← d.union_eq] at hx'
    rcases hx' with h | h
    · exact absurd h hx
    · exact le_trans (by simpa using hr h) (le_max_left _ _)

/-- The union of the coercion of an open set of `ℂ` with `∞` is open in the Riemann sphere,
provided the complement of the set is bounded. -/
theorem planeTwoDiscs_isOpen_coe_union_infty {s : Set ℂ} (hs : IsOpen s)
    (hb : ∃ R : ℝ, ∀ x : ℂ, x ∉ s → ‖x‖ ≤ R) :
    IsOpen ((fun z : ℂ => (z : RiemannSphere)) '' s ∪ {infty} : Set RiemannSphere) := by
  obtain ⟨R, hR⟩ := hb
  have hsub : ((fun z : ℂ => (z : RiemannSphere)) '' (Metric.closedBall (0 : ℂ) R)ᶜ ∪
      {infty} : Set RiemannSphere) ⊆
      ((fun z : ℂ => (z : RiemannSphere)) '' s ∪ {infty} : Set RiemannSphere) := by
    rintro y (⟨w, hw, rfl⟩ | hw)
    · refine Or.inl ⟨w, ?_, rfl⟩
      by_contra hws
      have hw' : w ∈ Metric.closedBall (0 : ℂ) R := by simpa using hR w hws
      exact hw hw'
    · exact Or.inr hw
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rcases hx with ⟨z, hz, rfl⟩ | hx
  · have h1 : ((fun z : ℂ => (z : RiemannSphere)) '' s : Set RiemannSphere) ∈
        𝓝 ((z : ℂ) : RiemannSphere) :=
      (OnePoint.isOpen_image_coe.mpr hs).mem_nhds ⟨z, hz, rfl⟩
    exact Filter.mem_of_superset h1 Set.subset_union_left
  · have hxinfty : x = infty := by simpa using hx
    subst hxinfty
    have hK : ((fun z : ℂ => (z : RiemannSphere)) '' (Metric.closedBall (0 : ℂ) R)ᶜ ∪
        {infty} : Set RiemannSphere) ∈ 𝓝 (infty : RiemannSphere) := by
      refine OnePoint.hasBasis_nhds_infty.mem_iff.mpr
        ⟨Metric.closedBall (0 : ℂ) R,
          ⟨Metric.isClosed_closedBall, isCompact_closedBall 0 R⟩, subset_rfl⟩
    exact Filter.mem_of_superset hK hsub

/-- The two pieces of the sphere cut by a plane curve and one of its Schoenflies discs are
disjoint. -/
theorem planeTwoDiscs_disjoint (c : Work.Smooth.Jordan.PlaneCurve)
    (d : Work.Smooth.Jordan.PlaneSchoenflies c) :
    Disjoint (((fun z : ℂ => (z : RiemannSphere)) '' d.U) ∪ {infty})
      ((fun z : ℂ => (z : RiemannSphere)) '' d.V) := by
  refine Set.disjoint_left.mpr ?_
  rintro x (⟨u, huU, rfl⟩ | hxinf) ⟨v, hvV, hveq⟩
  · exact Set.disjoint_left.mp d.disjoint_UV huU (OnePoint.coe_injective hveq ▸ hvV)
  · have h1 : x = infty := by simpa using hxinf
    have hxi : ((v : ℂ) : RiemannSphere) = infty := by
      calc ((v : ℂ) : RiemannSphere) = x := hveq
        _ = infty := h1
    exact OnePoint.coe_ne_infty v hxi

/-! ## The planar two-disc theorem -/

/-- **A simple closed curve in the plane bounds two embedded discs in the Riemann sphere.**

The bounded side is spanned by the disc supplied by the planar Jordan--Schoenflies theorem
(`PlaneHypothesis`); the unbounded side, together with `∞`, is spanned by the pull-back of the
spanning disc of the inverse curve `t ↦ (γ t - z₀)⁻¹`, for any point `z₀` of the bounded side. -/
theorem planeTwoDiscs (h : PlaneHypothesis) {γ : ℝ → ℂ} (hcont : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi))) :
    Nonempty (TwoDiscs (fun t : ℝ => (γ t : RiemannSphere))) := by
  classical
  let co : ℂ → RiemannSphere := fun z => (z : RiemannSphere)
  change Nonempty (TwoDiscs (fun t : ℝ => co (γ t)))
  let c : Work.Smooth.Jordan.PlaneCurve := ⟨γ, hcont, hper⟩
  have hsimple : c.IsSimple := hinj
  obtain ⟨d⟩ := h c hsimple
  obtain ⟨z₀, hz₀V⟩ := d.nonempty_V
  have hVsub : d.V ⊆ c.traceᶜ := by rw [← d.union_eq]; exact Set.subset_union_right
  have hUsub : d.U ⊆ c.traceᶜ := by rw [← d.union_eq]; exact Set.subset_union_left
  have hz₀ : ∀ t : ℝ, γ t ≠ z₀ := fun t ht => hVsub hz₀V ⟨t, ht⟩
  let γ' : ℝ → ℂ := fun t => (γ t - z₀)⁻¹
  have hγ'cont : Continuous γ' :=
    (hcont.sub continuous_const).inv₀ (fun t => sub_ne_zero.mpr (hz₀ t))
  have hγ'per : Function.Periodic γ' (2 * Real.pi) := by
    intro t
    show (γ (t + 2 * Real.pi) - z₀)⁻¹ = (γ t - z₀)⁻¹
    rw [hper t]
  have hγ'inj : Set.InjOn γ' (Set.Ico 0 (2 * Real.pi)) := by
    intro a ha b hb hab
    refine hinj ha hb ?_
    have h := inv_injective (show ((γ a - z₀)⁻¹ : ℂ) = (γ b - z₀)⁻¹ from hab)
    have h2 := congrArg (fun t : ℂ => t + z₀) h
    simpa using h2
  let c' : Work.Smooth.Jordan.PlaneCurve := ⟨γ', hγ'cont, hγ'per⟩
  obtain ⟨d'⟩ := h c' hγ'inj
  obtain ⟨Φ, hΦinfty, hΦzero, hΦcoe⟩ := mobiusAddInv z₀
  have hΦco : ∀ u : ℂ, u ≠ 0 → Φ (co u) = co (z₀ + u⁻¹) := fun u hu => hΦcoe u hu
  have hΦzero' : Φ (co 0) = infty := hΦzero
  have hΦinfty' : Φ infty = co z₀ := hΦinfty
  have hΦev : ∀ w : ℂ, w ≠ z₀ → Φ (co ((w - z₀)⁻¹)) = co w := by
    intro w hw
    have hne : (w - z₀)⁻¹ ≠ 0 := inv_ne_zero (sub_ne_zero.mpr hw)
    rw [hΦco _ hne, inv_inv]
    congr 1
    ring
  have hΦsymm : ∀ w : ℂ, w ≠ z₀ → Φ.symm (co w) = co ((w - z₀)⁻¹) := by
    intro w hw
    rw [← hΦev w hw, Homeomorph.symm_apply_apply]
  have hΦσ : ∀ t : ℝ, Φ (co (γ' t)) = co (γ t) := fun t => hΦev (γ t) (hz₀ t)
  have hsymm : ∀ t : ℝ, Φ.symm (co (γ t)) = co (γ' t) := by
    intro t
    rw [← hΦσ t, Homeomorph.symm_apply_apply]
  have hV'sub : d'.V ⊆ c'.traceᶜ := by rw [← d'.union_eq]; exact Set.subset_union_right
  have h0trace' : (0 : ℂ) ∉ c'.trace := by
    rintro ⟨t, ht⟩
    have h1 : (γ t - z₀)⁻¹ = 0 := ht
    exact inv_ne_zero (sub_ne_zero.mpr (hz₀ t)) h1
  have htraceθ : (fun w : ℂ => (w - z₀)⁻¹) '' c.trace = c'.trace := by
    ext x
    constructor
    · rintro ⟨w, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨γ t, ⟨t, rfl⟩, rfl⟩
  have hnotrace : ∀ w : ℂ, w ∉ c.trace → (w - z₀)⁻¹ ∉ c'.trace := by
    intro w hw hc
    rw [← htraceθ] at hc
    obtain ⟨x, hx, hxw⟩ := hc
    have hxeq : x = w := by
      have h := inv_injective (show ((x - z₀)⁻¹ : ℂ) = (w - z₀)⁻¹ from hxw)
      have h2 := congrArg (fun t : ℂ => t + z₀) h
      simpa using h2
    exact hw (hxeq ▸ hx)
  have hneU : ∀ u ∈ d.U, u ≠ z₀ := fun u hu hu' =>
    Set.disjoint_left.mp d.disjoint_UV hu (hu' ▸ hz₀V)
  have huz : ∀ v : ℂ, v ≠ 0 → v⁻¹ + z₀ ≠ z₀ := by
    intro v hv hv'
    have h1 : v⁻¹ = 0 := by
      have := congrArg (fun x : ℂ => x - z₀) hv'
      simpa using this
    exact hv (inv_eq_zero.mp h1)
  have hTUpre : IsPreconnected (Φ.symm '' (co '' d.U)) :=
    (d.preconn_U.image _ OnePoint.continuous_coe.continuousOn).image _
      Φ.symm.continuous.continuousOn
  have hTVpre : IsPreconnected (Φ.symm '' (co '' d.V)) :=
    (d.preconn_V.image _ OnePoint.continuous_coe.continuousOn).image _
      Φ.symm.continuous.continuousOn
  have hdisjCV : Disjoint (co '' d'.U ∪ {infty}) (co '' d'.V) := planeTwoDiscs_disjoint c' d'
  have hdisjCV' : Disjoint (co '' d.U ∪ {infty}) (co '' d.V) := planeTwoDiscs_disjoint c d
  -- The image of the bounded side of `γ` lies in the unbounded side of `γ'`.
  have hC2 : ∀ w : ℂ, w ∈ d.V → w ≠ z₀ → (w - z₀)⁻¹ ∈ d'.U := by
    have hcover : Φ.symm '' (co '' d.V) ⊆ (co '' d'.U ∪ {infty}) ∪ co '' d'.V := by
      rintro x ⟨w, ⟨w', hw'V, rfl⟩, rfl⟩
      by_cases hwz : w' = z₀
      · have h1 : Φ.symm (co w') = infty := by
          rw [hwz, ← hΦinfty', Homeomorph.symm_apply_apply]
        rw [h1]
        exact Or.inl (Or.inr rfl)
      · rw [hΦsymm w' hwz]
        have hnot : (w' - z₀)⁻¹ ∉ c'.trace := hnotrace w' (hVsub hw'V)
        have h1 : (w' - z₀)⁻¹ ∈ d'.U ∪ d'.V := by
          have h2 : (w' - z₀)⁻¹ ∈ c'.traceᶜ := hnot
          rw [← d'.union_eq] at h2
          exact h2
        rcases h1 with h | h
        · exact Or.inl (Or.inl ⟨_, h, rfl⟩)
        · exact Or.inr ⟨_, h, rfl⟩
    have hTV : Φ.symm '' (co '' d.V) ⊆ co '' d'.U ∪ {infty} := by
      rcases hTVpre.subset_or_subset
        (planeTwoDiscs_isOpen_coe_union_infty d'.isOpen_U (planeTwoDiscs_norm_bound c' d'.toPlaneSeparation))
        (OnePoint.isOpen_image_coe.mpr d'.isOpen_V) hdisjCV hcover with hh | hh
      · exact hh
      · exfalso
        have hinf : (infty : RiemannSphere) ∈ Φ.symm '' (co '' d.V) :=
          ⟨co z₀, ⟨z₀, hz₀V, rfl⟩, by rw [← hΦinfty', Homeomorph.symm_apply_apply]⟩
        exact OnePoint.infty_notMem_image_coe (hh hinf)
    intro w hwV hwz
    have h1 := hTV ⟨co w, ⟨w, hwV, rfl⟩, hΦsymm w hwz⟩
    rcases h1 with ⟨u, huU, hueq⟩ | h1
    · exact OnePoint.coe_injective hueq ▸ huU
    · exact absurd h1 (OnePoint.coe_ne_infty _)
  have hV'ne : (d'.V \ {0}).Nonempty := by
    by_cases h0 : (0 : ℂ) ∈ d'.V
    · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp d'.isOpen_V 0 h0
      refine ⟨((ε/2 : ℝ) : ℂ), ?_, ?_⟩
      · refine hball ?_
        rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith)]
        linarith
      · exact Complex.ofReal_ne_zero.mpr (by linarith)
    · obtain ⟨v, hv⟩ := d'.nonempty_V
      refine ⟨v, hv, ?_⟩
      intro hv0
      exact h0 (hv0 ▸ hv)
  -- The inverse map `w ↦ w⁻¹ + z₀` sends the bounded side of `γ'` into the unbounded side of `γ`.
  have hC3 : ∀ v : ℂ, v ∈ d'.V → v ≠ 0 → v⁻¹ + z₀ ∈ d.U := by
    intro v hvV hv0
    have hθv : (v⁻¹ + z₀ - z₀)⁻¹ = v := by
      rw [show v⁻¹ + z₀ - z₀ = v⁻¹ from by ring, inv_inv]
    have hnot : v⁻¹ + z₀ ∉ c.trace := by
      intro hc
      have hmem : v ∈ c'.trace := by
        rw [← htraceθ]
        exact ⟨v⁻¹ + z₀, hc, hθv⟩
      exact hV'sub hvV hmem
    have h1 : v⁻¹ + z₀ ∈ c.traceᶜ := hnot
    rw [← d.union_eq] at h1
    rcases h1 with h | h
    · exact h
    · exfalso
      have h2 := hC2 (v⁻¹ + z₀) h (huz v hv0)
      rw [hθv] at h2
      exact Set.disjoint_left.mp d'.disjoint_UV h2 hvV
  -- The image of the unbounded side of `γ` lies in the bounded side of `γ'`.
  have hC1 : ∀ u : ℂ, u ∈ d.U → (u - z₀)⁻¹ ∈ d'.V := by
    have hmeet : (Φ.symm '' (co '' d.U) ∩ (co '' d'.V)).Nonempty := by
      obtain ⟨v, hvV, hv0⟩ := hV'ne
      have hz : (v⁻¹ + z₀ - z₀)⁻¹ = v := by
        rw [show v⁻¹ + z₀ - z₀ = v⁻¹ from by ring, inv_inv]
      refine ⟨Φ.symm (co (v⁻¹ + z₀)), ?_, ?_⟩
      · exact ⟨co (v⁻¹ + z₀), ⟨v⁻¹ + z₀, hC3 v hvV hv0, rfl⟩, rfl⟩
      · refine ⟨v, hvV, ?_⟩
        rw [hΦsymm (v⁻¹ + z₀) (huz v hv0), hz]
    have hcover : Φ.symm '' (co '' d.U) ⊆ (co '' d'.U ∪ {infty}) ∪ co '' d'.V := by
      rintro x ⟨u, ⟨u', hu'U, rfl⟩, rfl⟩
      rw [hΦsymm u' (hneU u' hu'U)]
      have h1 : (u' - z₀)⁻¹ ∈ d'.U ∪ d'.V := by
        have hnot : (u' - z₀)⁻¹ ∉ c'.trace := hnotrace u' (hUsub hu'U)
        have h2 : (u' - z₀)⁻¹ ∈ c'.traceᶜ := hnot
        rw [← d'.union_eq] at h2
        exact h2
      rcases h1 with h | h
      · exact Or.inl (Or.inl ⟨_, h, rfl⟩)
      · exact Or.inr ⟨_, h, rfl⟩
    rcases hTUpre.subset_or_subset
      (planeTwoDiscs_isOpen_coe_union_infty d'.isOpen_U (planeTwoDiscs_norm_bound c' d'.toPlaneSeparation))
      (OnePoint.isOpen_image_coe.mpr d'.isOpen_V) hdisjCV hcover with hh | hh
    · exfalso
      obtain ⟨x, hxC, hxV⟩ := hmeet
      exact Set.disjoint_left.mp hdisjCV (hh hxC) hxV
    · intro u huU
      have h1 : Φ.symm (co u) ∈ co '' d'.V :=
        hh ⟨co u, ⟨u, huU, rfl⟩, rfl⟩
      obtain ⟨v, hvV, hveq⟩ := h1
      rw [hΦsymm u (hneU u huU)] at hveq
      exact OnePoint.coe_injective hveq ▸ hvV
  have h0closure : (0 : ℂ) ∈ closure ((fun w : ℂ => (w - z₀)⁻¹) '' d.U) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨u, huU, huR⟩ :=
      Work.Smooth.Jordan.plane_separation_unbounded d.toPlaneSeparation (‖z₀‖ + 1 + ε⁻¹)
    refine ⟨(u - z₀)⁻¹, ⟨u, huU, rfl⟩, ?_⟩
    rw [dist_zero_left, norm_inv]
    have h2 : ε⁻¹ < ‖u - z₀‖ := by
      have h3 : ‖z₀‖ + 1 + ε⁻¹ ≤ ‖u - z₀‖ + ‖z₀‖ := by
        calc ‖z₀‖ + 1 + ε⁻¹ ≤ ‖u‖ := huR
          _ = ‖(u - z₀) + z₀‖ := by congr 1; ring
          _ ≤ ‖u - z₀‖ + ‖z₀‖ := norm_add_le _ _
      linarith
    have hpos : (0 : ℝ) < ‖u - z₀‖ := lt_trans (inv_pos.mpr hε) h2
    exact (inv_lt_comm₀ hpos hε).mpr h2
  -- `0` lies in the bounded side of `γ'`.
  have h0closure' : (0 : ℂ) ∈ closure d'.V :=
    closure_mono (Set.image_subset_iff.mpr (fun u hu => hC1 u hu)) h0closure
  have h0V' : (0 : ℂ) ∈ d'.V := by
    rw [planeTwoDiscs_closure_V c' d'] at h0closure'
    rcases h0closure' with h | h
    · exact h
    · exact absurd h h0trace'
  have hC5 : ∀ v : ℂ, v ∈ d'.V → Φ (co v) ∈ co '' d.U ∪ {infty} := by
    intro v hvV
    by_cases hv : v = 0
    · rw [hv, hΦzero']
      exact Or.inr rfl
    · refine Or.inl ⟨v⁻¹ + z₀, hC3 v hvV hv, ?_⟩
      rw [hΦco v hv]
      congr 1
      ring
  have hrangeV' : Φ '' (co '' d'.V) = co '' d.U ∪ {infty} := by
    apply Set.Subset.antisymm
    · rintro x ⟨y, ⟨v, hvV, rfl⟩, rfl⟩
      exact hC5 v hvV
    · intro x hx
      rcases hx with ⟨u, huU, rfl⟩ | hxinf
      · refine ⟨co ((u - z₀)⁻¹), ⟨(u - z₀)⁻¹, hC1 u huU, rfl⟩, ?_⟩
        exact hΦev u (hneU u huU)
      · have hxi : x = infty := by simpa using hxinf
        subst hxi
        exact ⟨co 0, ⟨0, h0V', rfl⟩, hΦzero'⟩
  let e : C(Disc, RiemannSphere) :=
    ⟨fun z => co (d.e z), OnePoint.continuous_coe.comp d.e.continuous⟩
  let e' : C(Disc, RiemannSphere) :=
    ⟨fun z => Φ (co (d'.e z)),
      Φ.continuous.comp (OnePoint.continuous_coe.comp d'.e.continuous)⟩
  have hrange_e : Set.range e = co '' d.V ∪ Set.range (fun t : ℝ => co (γ t)) := by
    have h1 : Set.range e = co '' Set.range d.e := by
      ext x
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨d.e z, ⟨z, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
        exact ⟨z, rfl⟩
    rw [h1, d.range_e, planeTwoDiscs_closure_V c d, Set.image_union]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨t, ht⟩, rfl⟩
      exact ⟨t, congrArg co ht⟩
    · rintro ⟨t, rfl⟩
      exact ⟨γ t, ⟨t, rfl⟩, rfl⟩
  have hrange_e' : Set.range e' =
      (co '' d.U ∪ {infty}) ∪ Set.range (fun t : ℝ => co (γ t)) := by
    have h1 : Set.range e' = Φ '' (co '' Set.range d'.e) := by
      ext x
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨co (d'.e z), ⟨d'.e z, ⟨z, rfl⟩, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨v, ⟨z, rfl⟩, rfl⟩, rfl⟩
        exact ⟨z, rfl⟩
    rw [h1, d'.range_e, planeTwoDiscs_closure_V c' d', Set.image_union, Set.image_union, hrangeV']
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨w, ⟨t, ht⟩, rfl⟩, rfl⟩
      refine ⟨t, ?_⟩
      rw [← ht]
      exact (hΦσ t).symm
    · rintro ⟨t, rfl⟩
      exact ⟨co (γ' t), ⟨γ' t, ⟨t, rfl⟩, rfl⟩, hΦσ t⟩
  refine ⟨{ simple := ?_, e := e, e' := e', inj := ?_, inj' := ?_, boundary := ?_, boundary' := ?_, open_interior := ?_, open_interior' := ?_, cover := ?_, meet := ?_ }⟩
  · exact ⟨OnePoint.continuous_coe.comp hcont,
      fun t => by dsimp only; rw [hper t],
      fun a ha b hb hab => hinj ha hb (OnePoint.coe_injective hab)⟩
  · intro a b hab
    exact d.inj (OnePoint.coe_injective hab)
  · intro a b hab
    exact d'.inj (OnePoint.coe_injective (Φ.injective hab))
  · intro θ
    show co (d.e (Work.Smooth.Jordan.circlePoint θ)) = co (γ θ)
    rw [d.boundary θ]
  · intro θ
    show Φ (co (d'.e (Work.Smooth.Jordan.circlePoint θ))) = co (γ θ)
    rw [d'.boundary θ]
    exact hΦσ θ
  · have h1 : {x : RiemannSphere | ∃ z : Disc, ‖((z : Disc) : ℂ)‖ < 1 ∧ e z = x} =
        co '' d.V := by
      rw [← Work.Smooth.Jordan.plane_schoenflies_openDisc_eq d]
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨d.e z, ⟨z, hz, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        exact ⟨z, hz, rfl⟩
    rw [h1]
    exact OnePoint.isOpen_image_coe.mpr d.isOpen_V
  · have h1 : {x : RiemannSphere | ∃ z : Disc, ‖((z : Disc) : ℂ)‖ < 1 ∧ e' z = x} =
        Φ '' (co '' d'.V) := by
      rw [← Work.Smooth.Jordan.plane_schoenflies_openDisc_eq d']
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨co (d'.e z), ⟨d'.e z, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨v, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
        exact ⟨z, hz, rfl⟩
    rw [h1]
    exact Φ.isOpenMap (co '' d'.V) (OnePoint.isOpen_image_coe.mpr d'.isOpen_V)
  · rw [hrange_e, hrange_e']
    have hPQ : (co '' d.V ∪ co '' d.U : Set RiemannSphere) =
        (Set.univ \ {infty}) \ Set.range (fun t : ℝ => co (γ t)) := by
      rw [← Set.image_union, Set.union_comm d.V d.U, d.union_eq]
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        refine ⟨⟨trivial, OnePoint.coe_ne_infty z⟩, ?_⟩
        rintro ⟨t, ht⟩
        have h1 : γ t = z := OnePoint.coe_injective ht
        exact hz (h1 ▸ ⟨t, rfl⟩)
      · rintro ⟨⟨-, hne⟩, hnr⟩
        obtain ⟨z, hz⟩ := OnePoint.ne_infty_iff_exists.mp (by simpa using hne)
        refine ⟨z, ?_, hz⟩
        intro hzt
        obtain ⟨t, ht⟩ := hzt
        refine hnr ⟨t, ?_⟩
        calc co (γ t) = co z := congrArg co ht
          _ = x := hz
    have hcover' : (co '' d.V ∪ co '' d.U : Set RiemannSphere) ∪
        Set.range (fun t : ℝ => co (γ t)) ∪ {infty} = Set.univ := by
      rw [hPQ]
      ext x
      constructor
      · intro _
        exact trivial
      · intro _
        by_cases hx : x = infty
        · exact Or.inr hx
        · by_cases hxS : x ∈ Set.range (fun t : ℝ => co (γ t))
          · exact Or.inl (Or.inr hxS)
          · exact Or.inl (Or.inl ⟨⟨trivial, hx⟩, hxS⟩)
    rw [← hcover']
    ext x
    simp only [Set.mem_union]
    tauto
  · rw [hrange_e, hrange_e']
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨hx1, hx2⟩ := hx
      rcases hx1 with ⟨v, hvV, rfl⟩ | hxS
      · rcases hx2 with (⟨u, huU, hueq⟩ | hxinf) | hxS
        · exfalso
          exact Set.disjoint_left.mp d.disjoint_UV huU (OnePoint.coe_injective hueq ▸ hvV)
        · exfalso
          have h1 : co v = (infty : RiemannSphere) := by simpa using hxinf
          exact OnePoint.coe_ne_infty v h1
        · exact hxS
      · exact hxS
    · intro x hx
      exact ⟨Or.inr hx, Or.inr hx⟩

end

end Work.Smooth.SphereJordan
