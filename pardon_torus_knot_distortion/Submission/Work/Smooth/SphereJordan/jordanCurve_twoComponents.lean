import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.sphereTransport
import Submission.Work.Smooth.SphereJordan.planeTwoDiscs

/-!
# Jordan separation on the Riemann sphere

A continuous, `2π`-periodic curve `γ : ℝ → ℂ ∪ {∞}` which is injective on one period splits the
sphere into **two** non-empty open preconnected sets whose union is the complement of its trace:
`Work.Smooth.SphereJordan.jordanCurve_twoComponents`.

The proof is a transport of the *planar* Jordan separation theorem — proved unconditionally in this
workspace (`Work.Smooth.SphereJordan.nonempty_planeSeparation_of_continuous`) — along a
homeomorphism of the Riemann sphere carrying the curve off `∞`:

* `exists_notMem_range_of_isSimpleClosedCurve` — a simple closed curve of the sphere misses a point;
* `exists_planeCurve_conj` / `exists_separation_conj` — after conjugating by a homeomorphism `Φ`
  sending that point to `∞`, the curve is the image of a plane curve `γ'` to which the planar
  theorem applies: `Φ (γ t) = (γ' t : ℂ ∪ {∞})` and `S : PlaneSeparation γ'`.

The two pieces of the plane given by `S` are then pushed into the sphere (`⋃ S.U ∪ {∞}` and `S.V`),
and pulled back along `Φ`: the union of the two is the complement of `Φ '' range γ = range γ`, and
openness, preconnectedness and non-emptiness are preserved by the homeomorphism.

The only point needing the local theory of `OnePoint` is that the *unbounded* side of `S`, together
with `∞`, is open — this is `planeTwoDiscs_isOpen_coe_union_infty` — and preconnected, which is
`isPreconnected_coe_union_infty` below.
-/

noncomputable section

open Set Classical

namespace Work.Smooth.SphereJordan

/-- **`∞` is in the closure of the image of an unbounded set.** -/
theorem infty_mem_closure_coe_image {s : Set ℂ} (h : ∀ R : ℝ, ∃ x ∈ s, R ≤ ‖x‖) :
    (OnePoint.infty : RiemannSphere) ∈
      closure ((fun z : ℂ => (z : RiemannSphere)) '' s) := by
  rw [mem_closure_iff_nhds]
  intro V hV
  obtain ⟨K, ⟨-, hKcomp⟩, hKV⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.mp hV
  obtain ⟨R, hR⟩ := hKcomp.isBounded.exists_norm_le
  obtain ⟨x, hx, hxR⟩ := h (R + 1)
  refine ⟨(x : RiemannSphere), hKV (Or.inl ⟨x, ?_, rfl⟩), ⟨x, hx, rfl⟩⟩
  intro hxK
  have h1 := hR x hxK
  linarith

/-- **The unbounded side of a plane Jordan separation, together with `∞`, is preconnected.**  It
contains the preconnected image of `S.U` and is contained in its closure. -/
theorem isPreconnected_coe_union_infty {c : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSeparation c) :
    IsPreconnected ((fun z : ℂ => (z : RiemannSphere)) '' S.U ∪ {infty}) :=
  IsPreconnected.subset_closure
    (S.preconn_U.image _ OnePoint.continuous_coe.continuousOn)
    Set.subset_union_left
    (fun x hx => by
      rcases hx with hx | hx
      · exact subset_closure hx
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact infty_mem_closure_coe_image (Work.Smooth.Jordan.plane_separation_unbounded S))

/-- **The two pieces of the sphere cut out by a simple closed plane curve**: the bounded and the
unbounded side together with `∞` are disjoint and their union is the complement of the trace. -/
theorem coe_V_union_coe_U_infty_eq_compl {c : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSeparation c) :
    ((fun z : ℂ => (z : RiemannSphere)) '' S.V) ∪
        ((fun z : ℂ => (z : RiemannSphere)) '' S.U ∪ {infty}) =
      (((fun z : ℂ => (z : RiemannSphere)) '' c.trace))ᶜ := by
  ext x
  constructor
  · intro hx hxT
    rcases hx with ⟨v, hv, rfl⟩ | (⟨u, hu, rfl⟩ | hxinf)
    · obtain ⟨w, hw, hwe⟩ := hxT
      have h1 : v ∈ S.U ∪ S.V := Or.inr hv
      rw [S.union_eq, Set.mem_compl_iff] at h1
      exact h1 (OnePoint.coe_injective hwe ▸ hw)
    · obtain ⟨w, hw, hwe⟩ := hxT
      have h1 : u ∈ S.U ∪ S.V := Or.inl hu
      rw [S.union_eq, Set.mem_compl_iff] at h1
      exact h1 (OnePoint.coe_injective hwe ▸ hw)
    · have hxi : x = infty := hxinf
      rw [hxi] at hxT
      obtain ⟨w, -, hwe⟩ := hxT
      exact OnePoint.coe_ne_infty w hwe
  · intro hx
    cases x with
    | infty => exact Or.inr (Or.inr rfl)
    | coe z =>
      by_cases hz : z ∈ c.trace
      · exact absurd ⟨z, hz, rfl⟩ hx
      · have hz' : z ∈ c.traceᶜ := hz
        rw [← S.union_eq] at hz'
        rcases hz' with h | h
        · exact Or.inr (Or.inl ⟨z, h, rfl⟩)
        · exact Or.inl ⟨z, h, rfl⟩

/-- **Step 5**: pushing the planar separation through the conjugating homeomorphism. -/
theorem exists_twoComponents_of_separation
    {γ : ℝ → RiemannSphere} {Φ : RiemannSphere ≃ₜ RiemannSphere} {γ' : ℝ → ℂ}
    {hc : Continuous γ'} {hper : Function.Periodic γ' (2 * Real.pi)}
    (hlift : ∀ t : ℝ, Φ (γ t) = (γ' t : RiemannSphere))
    (S : Work.Smooth.Jordan.PlaneSeparation ⟨γ', hc, hper⟩) :
    ∃ U V : Set RiemannSphere,
      U.Nonempty ∧ V.Nonempty ∧ IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧
      U ∪ V = (Set.range γ)ᶜ ∧ IsPreconnected U ∧ IsPreconnected V := by
  -- the two pieces of the sphere
  set Z : Set RiemannSphere := (fun z : ℂ => (z : RiemannSphere)) '' S.V with hZ
  set W : Set RiemannSphere := (fun z : ℂ => (z : RiemannSphere)) '' S.U ∪ {infty} with hW
  have hZne : Z.Nonempty := by
    obtain ⟨v, hv⟩ := S.nonempty_V
    exact ⟨(v : RiemannSphere), by rw [hZ]; exact ⟨v, hv, rfl⟩⟩
  have hWne : W.Nonempty := by
    rw [hW]
    exact ⟨infty, Or.inr rfl⟩
  have hZopen : IsOpen Z := by
    rw [hZ]
    exact OnePoint.isOpen_image_coe.mpr S.isOpen_V
  have hWopen : IsOpen W := by
    rw [hW]
    exact planeTwoDiscs_isOpen_coe_union_infty S.isOpen_U (planeTwoDiscs_norm_bound _ S)
  have hZpre : IsPreconnected Z := by
    rw [hZ]
    exact S.preconn_V.image _ OnePoint.continuous_coe.continuousOn
  have hWpre : IsPreconnected W := by
    rw [hW]
    exact isPreconnected_coe_union_infty S
  have hZWdisj : Disjoint Z W := by
    rw [Set.disjoint_left]
    intro x hxZ hxW
    rw [hZ] at hxZ
    rw [hW] at hxW
    obtain ⟨v, hv, rfl⟩ := hxZ
    rcases hxW with ⟨u, hu, hux⟩ | hxinf
    · exact Set.disjoint_left.mp S.disjoint_UV hu (OnePoint.coe_injective hux ▸ hv)
    · exact OnePoint.coe_ne_infty v hxinf
  -- the cover
  have hΦrange : Φ '' Set.range γ =
      (fun z : ℂ => (z : RiemannSphere)) '' Set.range γ' := by
    ext x
    constructor
    · rintro ⟨y, ⟨t, rfl⟩, hxy⟩
      exact ⟨γ' t, ⟨t, rfl⟩, (hlift t).symm.trans hxy⟩
    · rintro ⟨z, ⟨t, ht⟩, hzx⟩
      exact ⟨γ t, ⟨t, rfl⟩, (hlift t).trans (by rw [ht]; exact hzx)⟩
  have hpreT : Φ ⁻¹' ((fun z : ℂ => (z : RiemannSphere)) '' Set.range γ') = Set.range γ := by
    rw [← hΦrange, Set.preimage_image_eq _ Φ.injective]
  have hcover : Z ∪ W = ((fun z : ℂ => (z : RiemannSphere)) '' Set.range γ')ᶜ := by
    rw [hZ, hW]
    exact coe_V_union_coe_U_infty_eq_compl S
  have hsubZ : Z ⊆ Set.range (Φ : RiemannSphere → RiemannSphere) := by
    rw [Set.range_eq_univ.mpr Φ.surjective]
    exact Set.subset_univ _
  have hsubW : W ⊆ Set.range (Φ : RiemannSphere → RiemannSphere) := by
    rw [Set.range_eq_univ.mpr Φ.surjective]
    exact Set.subset_univ _
  refine ⟨Φ ⁻¹' Z, Φ ⁻¹' W, hZne.preimage Φ.surjective, hWne.preimage Φ.surjective,
    hZopen.preimage Φ.continuous, hWopen.preimage Φ.continuous, hZWdisj.preimage Φ, ?_,
    hZpre.preimage_of_isOpenMap Φ.injective Φ.isOpenMap hsubZ,
    hWpre.preimage_of_isOpenMap Φ.injective Φ.isOpenMap hsubW⟩
  rw [← Set.preimage_union, hcover, Set.preimage_compl, hpreT]

/-- **Jordan separation on the Riemann sphere**: a simple closed curve splits `ℂ ∪ {∞}` into two
non-empty open preconnected pieces. -/
theorem jordanCurve_twoComponents {γ : ℝ → Work.Smooth.SphereJordan.RiemannSphere}
    (hγ : Work.Smooth.SphereJordan.IsSimpleClosedCurve γ) :
    ∃ U V : Set Work.Smooth.SphereJordan.RiemannSphere,
      U.Nonempty ∧ V.Nonempty ∧ IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧
      U ∪ V = (Set.range γ)ᶜ ∧ IsPreconnected U ∧ IsPreconnected V := by
  obtain ⟨Φ, γ', hc, hper, -, hlift, ⟨S⟩⟩ := exists_separation_conj hγ
  exact exists_twoComponents_of_separation hlift S

end Work.Smooth.SphereJordan
