import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.mobiusAddInv
import Submission.Work.Smooth.SphereJordan.brouwer_disc
import Submission.Work.Smooth.SphereJordan.DiscSpansAPI
import Submission.Work.Smooth.SphereJordan.openImage_isOpen
import Submission.Work.Topology.PlaneCurve.compl_jordan_atMostTwo

/-!
# The complement of an embedded disc on the Riemann sphere is preconnected

`Work.Smooth.SphereJordan.disc_complement_preconnected`: for an injective continuous map
`f : 𝔻 → ℂ ∪ {∞}` of the model disc, the complement of the range of `f` is preconnected.

## The route

`disc_complement_preconnected` **is proved here** from two auxiliary statements.

1. `exists_coe_notMem_range` (**proved, axiom-clean**) — an injective continuous map of the disc
   into the sphere misses a point `c` of the finite part.  If every finite point were attained
   then `range f`, being compact and containing the dense set `ℂ`, would be all of `S²`, so `f`
   would be a homeomorphism `𝔻 ≃ₜ S²`; conjugating the *antipodal* map of the round sphere (via
   `Work.Smooth.SphereJordan.riemannSphereHomeomorph`) by such a homeomorphism produces a
   continuous fixed-point-free self-map of `𝔻`, contradicting Brouwer's fixed point theorem for
   the disc (`Work.Smooth.SphereJordan.brouwer_disc`).  Equivalently: the fixed point property
   distinguishes `𝔻` from `S²`.
2. `compl_disc_image_preconnected_plane` — **the planar case**: the complement of the image of an
   injective continuous map `𝔻 → ℂ` is preconnected.  This is exactly "the outside of a Jordan
   curve is connected", i.e. the Jordan curve theorem for the simple closed curve
   `f '' {‖z‖ = 1}`; it is the single genuinely hard input of this file.

The reduction (proved here) is: move the missed point `c` to `∞` by the Möbius homeomorphism
`M (x) = (x - c)⁻¹` (built from `Work.Smooth.SphereJordan.mobiusAddInv`), so that `g := M ∘ f`
avoids `∞` and can be read as a map `g' : 𝔻 → ℂ`; the planar case gives that
`ℂ ∖ range g'` is preconnected, and since it is an unbounded subset of `ℂ`, the union with `∞`
— which is `(range g)ᶜ` — is preconnected; transporting back along `M⁻¹` gives the conclusion.

## Supporting lemmas (all proved here)

* `isOpen_connectedComponentIn_of_isOpen` — a connected component of an open subset of `ℂ` is open;
* `componentIn_meets_of_isOpen` — every connected component of the complement of a nonempty closed
  `C ⊆ ℂ` meets every open neighbourhood of `C` (the abstract form of the step used by the `C¹`
  Jordan separation `Work.Smooth.JordanSeparation.componentIn_meets_annulus`);
* `atMostTwo_components_of_neighbourhood` — if a nonempty closed `C ⊆ ℂ` has an open neighbourhood
  `U` such that `U \ C` is covered by two preconnected sets, then `Cᶜ` has at most two connected
  components; this is the abstract form of the `C¹` "offset annulus" argument
  (`Work.Smooth.JordanSeparation.atMostTwo_connectedComponentIn_of_offset`).  It is the route by
  which the planar case above can be attacked for `C¹` data; it is kept here for that purpose.
-/

open Set
open LeanEval.KnotTheory.PardonDistortion

namespace Work.Smooth.SphereJordan

noncomputable section

/-! ## A component of an open subset of `ℂ` is open -/

theorem isOpen_connectedComponentIn_of_isOpen {F : Set ℂ} (hF : IsOpen F) (x : ℂ) :
    IsOpen (connectedComponentIn F x) := by
  rcases eq_or_ne (connectedComponentIn F x) ∅ with h | _
  · rw [h]; exact isOpen_empty
  · rw [isOpen_iff_mem_nhds]
    intro y hy
    have hyF : y ∈ F := connectedComponentIn_subset F x hy
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hF y hyF
    have hsub : Metric.ball y ε ⊆ connectedComponentIn F y :=
      Metric.isPreconnected_ball.subset_connectedComponentIn (Metric.mem_ball_self hε) hball
    have hyx : connectedComponentIn F y = connectedComponentIn F x :=
      (connectedComponentIn_eq hy).symm
    rw [← hyx]
    exact Filter.mem_of_superset (Metric.ball_mem_nhds y hε) hsub

/-! ## Every component of the complement of a nonempty closed set meets a neighbourhood -/

theorem componentIn_meets_of_isOpen {C U : Set ℂ} (hC : C.Nonempty) (hCcl : IsClosed C)
    (hCU : C ⊆ U) (hU : IsOpen U) {x : ℂ} (hx : x ∉ C) :
    (connectedComponentIn Cᶜ x ∩ U).Nonempty := by
  set W := connectedComponentIn Cᶜ x with hWdef
  have hWC : W ⊆ Cᶜ := connectedComponentIn_subset Cᶜ x
  have hWopen : IsOpen W := isOpen_connectedComponentIn_of_isOpen hCcl.isOpen_compl x
  have hxW : x ∈ W := mem_connectedComponentIn hx
  -- `W` is closed in `Cᶜ`: `closure W ∩ Cᶜ ⊆ W`.
  have hclosed : closure W ∩ Cᶜ ⊆ W := by
    rintro y ⟨hycl, hyC⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hCcl.isOpen_compl y hyC
    obtain ⟨z, hzW, hzy⟩ := Metric.mem_closure_iff.mp hycl ε hε
    have hzball : z ∈ Metric.ball y ε := by
      rw [Metric.mem_ball, dist_comm]; exact hzy
    have hsub : Metric.ball y ε ⊆ connectedComponentIn Cᶜ z :=
      Metric.isPreconnected_ball.subset_connectedComponentIn hzball hball
    have hzW' : connectedComponentIn Cᶜ z = W :=
      (connectedComponentIn_eq hzW).symm.trans hWdef.symm
    rw [hzW'] at hsub
    exact hsub (Metric.mem_ball_self hε)
  -- `frontier W ⊆ C`.
  have hfrC : frontier W ⊆ C := by
    intro y hy
    have hycl : y ∈ closure W := frontier_subset_closure hy
    by_contra hyC
    have hyW : y ∈ W := hclosed ⟨hycl, hyC⟩
    rw [hWopen.frontier_eq] at hy
    exact hy.2 hyW
  -- `frontier W ≠ ∅`: otherwise `W` is clopen and `ℂ` is connected.
  have hfrne : (frontier W).Nonempty := by
    by_contra hcon
    rw [not_nonempty_iff_eq_empty] at hcon
    have hfr : frontier W = ∅ := hcon
    have hclW : closure W ⊆ W := by
      have h1 : closure W ⊆ interior W := by
        have h2 : closure W \ W = ∅ := by rw [← hWopen.frontier_eq]; exact hfr
        intro a ha
        have haW : a ∈ W := by
          by_contra hcon2
          have : a ∈ closure W \ W := ⟨ha, hcon2⟩
          rw [h2] at this
          exact this
        rwa [hWopen.interior_eq]
      rwa [hWopen.interior_eq] at h1
    have hcl : IsClosed W := closure_subset_iff_isClosed.mp hclW
    rcases isClopen_iff.mp (show IsClopen W from ⟨hcl, hWopen⟩) with h | h
    · rw [h] at hxW
      exact notMem_empty x hxW
    · have hsub : univ ⊆ Cᶜ := by rw [← h]; exact hWC
      have hC0 : C = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        intro c hc
        exact hsub (mem_univ c) hc
      exact hC.ne_empty hC0
  obtain ⟨y, hyfr⟩ := hfrne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU y (hCU (hfrC hyfr))
  obtain ⟨a, haW, hay⟩ := Metric.mem_closure_iff.mp (frontier_subset_closure hyfr) ε hε
  refine ⟨a, haW, hball ?_⟩
  rw [Metric.mem_ball, dist_comm]
  exact hay

/-! ## At most two components from a two-piece neighbourhood -/

theorem atMostTwo_components_of_neighbourhood {C U P Q : Set ℂ} (hC : C.Nonempty)
    (hCcl : IsClosed C) (hCU : C ⊆ U) (hUopen : IsOpen U)
    (hP : IsPreconnected P) (hQ : IsPreconnected Q)
    (hPne : P.Nonempty) (hQne : Q.Nonempty)
    (hPU : P ⊆ Cᶜ) (hQU : Q ⊆ Cᶜ) (hcov : U \ C ⊆ P ∪ Q) :
    ∀ x y z : ℂ, x ∉ C → y ∉ C → z ∉ C →
      connectedComponentIn Cᶜ x = connectedComponentIn Cᶜ y ∨
      connectedComponentIn Cᶜ x = connectedComponentIn Cᶜ z ∨
      connectedComponentIn Cᶜ y = connectedComponentIn Cᶜ z := by
  obtain ⟨p, hp⟩ := hPne
  obtain ⟨q, hq⟩ := hQne
  have key : ∀ w : ℂ, w ∉ C →
      connectedComponentIn Cᶜ w = connectedComponentIn Cᶜ p ∨
      connectedComponentIn Cᶜ w = connectedComponentIn Cᶜ q := by
    intro w hw
    obtain ⟨a, haW, haU⟩ := componentIn_meets_of_isOpen hC hCcl hCU hUopen hw
    have haC : a ∉ C := connectedComponentIn_subset Cᶜ w haW
    rcases hcov ⟨haU, haC⟩ with ha | ha
    · have hpa : p ∈ connectedComponentIn Cᶜ a := hP.subset_connectedComponentIn ha hPU hp
      exact Or.inl ((connectedComponentIn_eq haW).trans (connectedComponentIn_eq hpa))
    · have hqa : q ∈ connectedComponentIn Cᶜ a := hQ.subset_connectedComponentIn ha hQU hq
      exact Or.inr ((connectedComponentIn_eq haW).trans (connectedComponentIn_eq hqa))
  intro x y z hx hy hz
  rcases key x hx with hx1 | hx1
  · rcases key y hy with hy1 | hy1
    · exact Or.inl (hx1.trans hy1.symm)
    · rcases key z hz with hz1 | hz1
      · exact Or.inr (Or.inl (hx1.trans hz1.symm))
      · exact Or.inr (Or.inr (hy1.trans hz1.symm))
  · rcases key y hy with hy1 | hy1
    · rcases key z hz with hz1 | hz1
      · exact Or.inr (Or.inr (hy1.trans hz1.symm))
      · exact Or.inr (Or.inl (hx1.trans hz1.symm))
    · exact Or.inl (hx1.trans hy1.symm)

/-! ## An injective disc map into the sphere misses a finite point -/

/-- An injective continuous map from the closed disc into the Riemann sphere misses a point of the
finite part.  Indeed, if every finite point were attained then `range f`, being compact and
containing the dense set `ℂ`, would be all of `S²`; then the image of the open disc and the image
of the circle would be two non-empty disjoint closed subsets covering `S²`, and the image of the
open disc would be closed although the open disc is dense in the disc — forcing a point of the
circle to be the image of an interior point. -/
theorem exists_coe_notMem_range {f : C(Disc, RiemannSphere)} (hf : Function.Injective f) :
    ∃ c : ℂ, (c : RiemannSphere) ∉ Set.range f := by
  by_contra hcon
  push_neg at hcon
  -- every finite point is attained
  have hcoe : Set.range ((↑) : ℂ → RiemannSphere) ⊆ Set.range f := by
    rintro x ⟨c, rfl⟩
    exact hcon c
  have hdense : closure (Set.range ((↑) : ℂ → RiemannSphere)) = univ :=
    OnePoint.denseRange_coe.closure_range
  have hclosed : IsClosed (Set.range f) := (isCompact_range f.continuous).isClosed
  have huniv : Set.range f = univ := by
    have hle : univ ⊆ Set.range f := by
      rw [← hdense]
      exact closure_minimal hcoe hclosed
    exact eq_univ_of_univ_subset hle
  have hsurj : Function.Surjective f := fun y => by
    show y ∈ Set.range f
    rw [huniv]
    trivial
  -- hence `f` induces a homeomorphism `𝔻 ≃ₜ S²`
  haveI : CompactSpace Disc := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) 1)
  let e : Disc ≃ₜ RiemannSphere :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f ⟨hf, hsurj⟩) f.continuous
  -- the antipodal map of the round sphere, transported to `S²`
  have hnormS : ∀ x : Work.Smooth.Jordan.RoundSphere, ‖(Subtype.val x : R3)‖ = 1 := by
    intro x
    have h := x.2
    change (Subtype.val x : R3) ∈ Metric.sphere (0 : R3) 1 at h
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at h
    exact h
  let antiS : Work.Smooth.Jordan.RoundSphere → Work.Smooth.Jordan.RoundSphere :=
    fun x => ⟨-(Subtype.val x : R3), by
      change -(Subtype.val x : R3) ∈ Metric.sphere (0 : R3) 1
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_neg]
      exact hnormS x⟩
  have hcont_antiS : Continuous antiS :=
    Continuous.subtype_mk (continuous_neg.comp continuous_subtype_val) _
  have hfixS : ∀ x : Work.Smooth.Jordan.RoundSphere, antiS x ≠ x := by
    intro x hx
    have h1 : dist (Subtype.val (antiS x) : R3) (Subtype.val x : R3) = 0 := by
      rw [hx, dist_self]
    have h2 : dist (Subtype.val (antiS x) : R3) (Subtype.val x : R3) = 2 := by
      have hunfold : (Subtype.val (antiS x) : R3) = -(Subtype.val x : R3) := rfl
      rw [hunfold, dist_eq_norm]
      have hsub : -(Subtype.val x : R3) - (Subtype.val x : R3)
          = -((Subtype.val x : R3) + (Subtype.val x : R3)) := by
        rw [neg_add]; abel
      rw [hsub, norm_neg, ← two_smul ℝ (Subtype.val x : R3), norm_smul, Real.norm_eq_abs,
        hnormS x, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      norm_num
    rw [h2] at h1
    norm_num at h1
  let anti : RiemannSphere → RiemannSphere :=
    fun x => riemannSphereHomeomorph.symm (antiS (riemannSphereHomeomorph x))
  have hanti_cont : Continuous anti :=
    riemannSphereHomeomorph.symm.continuous.comp
      (hcont_antiS.comp riemannSphereHomeomorph.continuous)
  have hanti_fix : ∀ x : RiemannSphere, anti x ≠ x := by
    intro x hx
    have h1 : antiS (riemannSphereHomeomorph x) = riemannSphereHomeomorph x := by
      have := congrArg riemannSphereHomeomorph hx
      simpa [anti] using this
    exact hfixS (riemannSphereHomeomorph x) h1
  -- Brouwer applied to the conjugated map `𝔻 → 𝔻`
  let g : C(Disc, Disc) :=
    ⟨fun x => e.symm (anti (e x)), e.symm.continuous.comp (hanti_cont.comp e.continuous)⟩
  obtain ⟨x, hx⟩ := brouwer_disc g
  have h2 : anti (e x) = e x := by
    have := congrArg e hx
    simpa [g] using this
  exact hanti_fix (e x) h2


/-! ## The planar case: the complement of an embedded disc in `ℂ` is preconnected

This is the form of the Jordan curve theorem needed for the target.  For an injective continuous
`f : 𝔻 → ℂ`, the boundary circle `θ ↦ f (e^{iθ})` is a simple closed plane curve and

  `(f '' {‖z‖ = 1})ᶜ = openImage f ⊔ (range f)ᶜ`

is a disjoint union of two open sets: the image of the *open* disc is open (invariance of domain,
`openImage_isOpen`) and `range f` is compact.  Now a component of the complement of the curve which
meets `(range f)ᶜ` stays there (`IsPreconnected.subset_or_subset`), so the "at most two components"
half of the Jordan curve theorem for the boundary curve
(`Work.Topology.PlaneCurve.compl_jordan_atMostTwo`, proved from Brouwer's fixed point theorem by
Maehara's argument) forces `(range f)ᶜ` to be a *single* component of the complement of the curve.
-/

/-- The parametrisation `θ ↦ e^{iθ}` of the boundary circle of the model disc is injective on one
period `[0, 2π)` (Mathlib's `Circle.exp_injOn_Ico`). -/
private lemma circlePoint_injOn_Ico_aux :
    Set.InjOn (circlePoint : ℝ → Disc) (Set.Ico 0 (2 * Real.pi)) := by
  intro a ha b hb hab
  have h : Circle.exp a = Circle.exp b := by
    apply Subtype.ext
    rw [Circle.coe_exp, Circle.coe_exp]
    have h2 := congrArg (fun z : Disc => (z : ℂ)) hab
    simpa [Work.Smooth.Jordan.circlePoint_coe] using h2
  exact Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi)
    (by linarith [Real.two_pi_pos]) ha hb h

/-- The image of the boundary circle of the model disc is the trace of the `2π`-periodic curve
`θ ↦ f (e^{iθ})`. -/
private lemma range_circlePoint_image (f : C(Disc, ℂ)) :
    Set.range (fun θ : ℝ => f (circlePoint θ)) = f '' {z : Disc | ‖(z : ℂ)‖ = 1} := by
  ext x
  constructor
  · rintro ⟨θ, rfl⟩
    exact ⟨circlePoint θ, by
      show ‖((circlePoint θ : Disc) : ℂ)‖ = 1
      rw [Work.Smooth.Jordan.circlePoint_coe, Complex.norm_exp_ofReal_mul_I], rfl⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq z hz
    exact ⟨θ, congrArg f hθ⟩

/-- The image of the model disc is the image of its open part together with the image of its
boundary circle. -/
private lemma openImage_union_circle_eq_range (f : C(Disc, ℂ)) :
    openImage f ∪ f '' {z : Disc | ‖(z : ℂ)‖ = 1} = Set.range f := by
  ext x
  constructor
  · rintro (⟨z, -, rfl⟩ | ⟨z, -, rfl⟩) <;> exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    have hz1 : ‖(z : ℂ)‖ ≤ 1 := by
      have h := z.2
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
      exact h
    rcases lt_or_eq_of_le hz1 with hlt | heq
    · exact Or.inl ⟨z, hlt, rfl⟩
    · exact Or.inr ⟨z, heq, rfl⟩

/-- The image of the open disc and the image of the boundary circle are disjoint. -/
private lemma disjoint_openImage_circleImage {f : C(Disc, ℂ)} (hf : Function.Injective f) :
    Disjoint (openImage f) (f '' {z : Disc | ‖(z : ℂ)‖ = 1}) := by
  rw [Set.disjoint_left]
  rintro x ⟨z, hz, rfl⟩ ⟨z', hz', hzz'⟩
  simp only [Set.mem_setOf_eq] at hz hz'
  have hzz : z' = z := hf hzz'
  rw [hzz] at hz'
  rw [hz'] at hz
  exact absurd hz (lt_irrefl 1)

/-- **The complement of the boundary circle is the union of the open image and the complement of
the image of the disc.** -/
private lemma compl_circleImage_eq {f : C(Disc, ℂ)} (hf : Function.Injective f) :
    (f '' {z : Disc | ‖(z : ℂ)‖ = 1})ᶜ = openImage f ∪ (Set.range f)ᶜ := by
  have hdisj := disjoint_openImage_circleImage (f := f) hf
  ext x
  rw [Set.mem_compl_iff, Set.mem_union]
  constructor
  · intro hx
    by_cases hxf : x ∈ Set.range f
    · have h1 : x ∈ openImage f ∪ f '' {z : Disc | ‖(z : ℂ)‖ = 1} := by
        rw [openImage_union_circle_eq_range f]
        exact hxf
      rcases h1 with h | h
      · exact Or.inl h
      · exact absurd h hx
    · exact Or.inr hxf
  · rintro (hx | hx)
    · rintro ⟨z, hz, rfl⟩
      exact (Set.disjoint_left.mp hdisj) hx ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact hx ⟨z, rfl⟩

/-- **The planar case**: the complement of the image of an injective continuous map `𝔻 → ℂ` is
preconnected. -/
theorem compl_disc_image_preconnected_plane
    {f : C(Disc, ℂ)} (hf : Function.Injective f) : IsPreconnected ((Set.range f)ᶜ) := by
  set γ : ℝ → ℂ := fun θ => f (circlePoint θ) with hγdef
  have hγcont : Continuous γ := f.continuous.comp NoRetraction.continuous_circlePoint
  have hγper : Function.Periodic γ (2 * Real.pi) := fun θ => by
    show f (circlePoint (θ + 2 * Real.pi)) = f (circlePoint θ)
    rw [NoRetraction.circlePoint_add_two_pi θ]
  have hγinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)) := fun a ha b hb hab =>
    circlePoint_injOn_Ico_aux ha hb (hf hab)
  have hC : Set.range γ = f '' {z : Disc | ‖(z : ℂ)‖ = 1} := by
    rw [hγdef]
    exact range_circlePoint_image f
  have hcompl : (Set.range γ)ᶜ = openImage f ∪ (Set.range f)ᶜ := by
    rw [hC]
    exact compl_circleImage_eq hf
  have hOopen : IsOpen (openImage f) := openImage_isOpen hf
  have hEopen : IsOpen ((Set.range f)ᶜ) := (isCompact_range f.continuous).isClosed.isOpen_compl
  have hOdisj : Disjoint (openImage f) ((Set.range f)ᶜ) := by
    rw [Set.disjoint_left]
    rintro x ⟨z, -, rfl⟩ hx
    exact hx ⟨z, rfl⟩
  -- a component of the complement of the curve meeting the outside of the disc lies outside it
  have hkey : ∀ y : ℂ, y ∈ (Set.range f)ᶜ →
      connectedComponentIn (Set.range γ)ᶜ y ⊆ (Set.range f)ᶜ := by
    intro y hy
    have hyC : y ∈ (Set.range γ)ᶜ := by rw [hcompl]; exact Or.inr hy
    have hKpre : IsPreconnected (connectedComponentIn (Set.range γ)ᶜ y) :=
      isPreconnected_connectedComponentIn
    have hsub : connectedComponentIn (Set.range γ)ᶜ y ⊆ openImage f ∪ (Set.range f)ᶜ := by
      intro z hz
      have h1 : z ∈ (Set.range γ)ᶜ := connectedComponentIn_subset (Set.range γ)ᶜ y hz
      rwa [hcompl] at h1
    rcases hKpre.subset_or_subset hOopen hEopen hOdisj hsub with h | h
    · exfalso
      have hmem : y ∈ openImage f := h (mem_connectedComponentIn hyC)
      exact hy (by rw [← openImage_union_circle_eq_range f]; exact Or.inl hmem)
    · exact h
  -- two points of the outside lie in the same component of the complement of the curve
  have hsame : ∀ y z : ℂ, y ∈ (Set.range f)ᶜ → z ∈ (Set.range f)ᶜ →
      connectedComponentIn (Set.range γ)ᶜ y = connectedComponentIn (Set.range γ)ᶜ z := by
    intro y z hy hz
    by_contra hne
    have hw : f 0 ∈ openImage f := ⟨0, by simp, rfl⟩
    have hwγ : f 0 ∉ Set.range γ := by
      rw [hC]
      rintro ⟨w, hw1, hw2⟩
      have hw3 : w = 0 := hf hw2
      rw [hw3] at hw1
      exact absurd hw1 (by simp)
    have hyγ : y ∉ Set.range γ := by
      rw [hC]
      intro hyc
      exact hy (by rw [← openImage_union_circle_eq_range f]; exact Or.inr hyc)
    have hzγ : z ∉ Set.range γ := by
      rw [hC]
      intro hzc
      exact hz (by rw [← openImage_union_circle_eq_range f]; exact Or.inr hzc)
    have hwC : f 0 ∈ (Set.range γ)ᶜ := by rw [hcompl]; exact Or.inl hw
    have hwy : connectedComponentIn (Set.range γ)ᶜ (f 0) ≠
        connectedComponentIn (Set.range γ)ᶜ y := by
      intro hcon
      have hmem : f 0 ∈ connectedComponentIn (Set.range γ)ᶜ y := by
        rw [← hcon]
        exact mem_connectedComponentIn hwC
      exact (hkey y hy hmem) ⟨0, rfl⟩
    have hwz : connectedComponentIn (Set.range γ)ᶜ (f 0) ≠
        connectedComponentIn (Set.range γ)ᶜ z := by
      intro hcon
      have hmem : f 0 ∈ connectedComponentIn (Set.range γ)ᶜ z := by
        rw [← hcon]
        exact mem_connectedComponentIn hwC
      exact (hkey z hz hmem) ⟨0, rfl⟩
    rcases Work.Topology.PlaneCurve.compl_jordan_atMostTwo hγcont hγper hγinj hwγ hyγ hzγ with
      h | h | h
    · exact hwy h
    · exact hwz h
    · exact hne h
  -- an explicit point outside the disc
  obtain ⟨R, hR⟩ := (isCompact_range f.continuous).isBounded.exists_norm_le
  have hR0 : 0 ≤ R := le_trans (norm_nonneg (f 0)) (hR (f 0) ⟨0, rfl⟩)
  have hc : (((R + 1 : ℝ)) : ℂ) ∉ Set.range f := by
    intro hcon
    have h1 := hR _ hcon
    have h2 : ‖(((R + 1 : ℝ)) : ℂ)‖ = R + 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    rw [h2] at h1
    linarith
  have hset : (Set.range f)ᶜ = connectedComponentIn (Set.range γ)ᶜ (((R + 1 : ℝ)) : ℂ) := by
    apply Subset.antisymm
    · intro z hz
      rw [← hsame z _ hz hc]
      exact mem_connectedComponentIn (by rw [hcompl]; exact Or.inr hz)
    · exact hkey _ hc
  rw [hset]
  exact isPreconnected_connectedComponentIn

/-! ## The target, from the planar case -/

/-- **The complement of an embedded disc in the Riemann sphere is preconnected.**

The planar case (`compl_disc_image_preconnected_plane`) is transported along the Möbius
homeomorphism `z ↦ (z - c)⁻¹`, where `c` is a finite point missed by `f`
(`exists_coe_notMem_range`): after the change of coordinates the image of `f` avoids `∞`, so `f`
can be read as a map into `ℂ`, and the planar statement applies. -/
theorem disc_complement_preconnected
    {f : C(Work.Smooth.SphereJordan.Disc, Work.Smooth.SphereJordan.RiemannSphere)}
    (hf : Function.Injective f) : IsPreconnected ((Set.range f)ᶜ) := by
  obtain ⟨c, hc⟩ := exists_coe_notMem_range (f := f) hf
  -- the Möbius homeomorphism `M (x) = (x - c)⁻¹`, sending `c` to `∞` and `∞` to `0`
  let M : RiemannSphere ≃ₜ RiemannSphere :=
    (Homeomorph.onePointCongr (Homeomorph.addRight (-c))).trans invHomeomorph
  have hMc : M (c : RiemannSphere) = infty := by
    show invHomeomorph
      ((Homeomorph.onePointCongr (Homeomorph.addRight (-c))) (c : RiemannSphere)) = infty
    have h1 : (Homeomorph.onePointCongr (Homeomorph.addRight (-c))) (c : RiemannSphere)
        = ((0 : ℂ) : RiemannSphere) := by
      show Homeomorph.onePointCongr (Homeomorph.addRight (-c)) (OnePoint.some c)
        = OnePoint.some 0
      simp [Homeomorph.onePointCongr]
    rw [h1, invHomeomorph_coe_zero]
  -- `g := M ∘ f` misses `∞`
  let g : C(Disc, RiemannSphere) := ⟨fun z => M (f z), M.continuous.comp f.continuous⟩
  have hg_apply : ∀ z, g z = M (f z) := fun z => rfl
  have hg_ne : ∀ z, g z ≠ infty := by
    intro z hz
    have h2 : M (f z) = M (c : RiemannSphere) := by rw [← hg_apply z, hz, hMc]
    exact hc ⟨z, M.injective h2⟩
  -- read `g` as a map into `ℂ` (it misses `∞`)
  set gfun : Disc → ℂ := fun z => Classical.choose (OnePoint.ne_infty_iff_exists.mp (hg_ne z))
    with hgfun
  have hgfun_spec : ∀ z, ((gfun z : ℂ) : RiemannSphere) = g z := fun z =>
    Classical.choose_spec (OnePoint.ne_infty_iff_exists.mp (hg_ne z))
  have hcont' : Continuous gfun := by
    rw [Topology.IsInducing.continuous_iff OnePoint.isOpenEmbedding_coe.isEmbedding.isInducing]
    have h1 : ((↑) : ℂ → RiemannSphere) ∘ gfun = ⇑g := funext hgfun_spec
    rw [h1]; exact g.continuous
  let g' : C(Disc, ℂ) := ⟨gfun, hcont'⟩
  have hcoe_g' : ∀ z, ((g' z : ℂ) : RiemannSphere) = g z := hgfun_spec
  have hg'_inj : Function.Injective g' := by
    intro x y hxy
    have h1 : g x = g y := by rw [← hcoe_g' x, ← hcoe_g' y, hxy]
    exact hf (M.injective h1)
  -- the planar case applies to `g'`
  have hplan : IsPreconnected ((Set.range g')ᶜ : Set ℂ) :=
    compl_disc_image_preconnected_plane (f := g') hg'_inj
  -- and transfers back to the sphere
  have hgcompl : (Set.range g)ᶜ = (↑) '' ((Set.range g')ᶜ : Set ℂ) ∪ {infty} := by
    have hrg : Set.range g = (↑) '' (Set.range g') := by
      ext x
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨g' z, ⟨z, rfl⟩, hcoe_g' z⟩
      · rintro ⟨w, ⟨z, rfl⟩, rfl⟩
        exact ⟨z, (hcoe_g' z).symm⟩
    rw [hrg, OnePoint.compl_image_coe]
  have hpre : IsPreconnected ((Set.range g)ᶜ) := by
    rw [hgcompl]
    -- the image of the unbounded set `(range g')ᶜ` accumulates at `∞`
    have hcl : infty ∈ closure (OnePoint.some '' ((Set.range g')ᶜ : Set ℂ)) := by
      rw [mem_closure_iff_nhds]
      intro V hV
      obtain ⟨K, ⟨hKcl, hKcomp⟩, hKV⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.mp hV
      have hKbdd : Bornology.IsBounded K := hKcomp.isBounded
      obtain ⟨R, hR⟩ := hKbdd.exists_norm_le
      have hgbdd : Bornology.IsBounded (Set.range g') :=
        (isCompact_range g'.continuous).isBounded
      obtain ⟨R', hR'⟩ := hgbdd.exists_norm_le
      set N : ℝ := max (max R 0) (max R' 0) + 1 with hN
      have hNpos : 0 < N := by
        have : (0:ℝ) ≤ max (max R 0) (max R' 0) := le_max_of_le_left (le_max_right _ _)
        rw [hN]; linarith
      have hNR : R < N := by
        have h1 : R ≤ max R 0 := le_max_left _ _
        have h2 : max R 0 ≤ max (max R 0) (max R' 0) := le_max_left _ _
        rw [hN]; linarith
      have hNR' : R' < N := by
        have h1 : R' ≤ max R' 0 := le_max_left _ _
        have h2 : max R' 0 ≤ max (max R 0) (max R' 0) := le_max_right _ _
        rw [hN]; linarith
      have hanorm : ‖(N : ℂ)‖ = N := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hNpos]
      have haK : (N : ℂ) ∉ K := by
        intro hmem
        have hle := hR _ hmem
        rw [hanorm] at hle
        linarith
      have haS : (N : ℂ) ∉ Set.range g' := by
        intro hmem
        obtain ⟨z, hz⟩ := hmem
        have hle := hR' (g' z) ⟨z, rfl⟩
        rw [hz, hanorm] at hle
        linarith
      exact ⟨(OnePoint.some (N : ℂ)), hKV (Or.inl ⟨(N : ℂ), haK, rfl⟩),
        ⟨(N : ℂ), haS, rfl⟩⟩
    refine IsPreconnected.subset_closure (s := OnePoint.some '' ((Set.range g')ᶜ : Set ℂ))
      (t := OnePoint.some '' ((Set.range g')ᶜ : Set ℂ) ∪ {infty}) ?_ ?_ ?_
    · exact hplan.image OnePoint.some OnePoint.continuous_coe.continuousOn
    · intro x hx
      exact Or.inl hx
    · intro x hx
      rcases hx with hx | rfl
      · exact subset_closure hx
      · exact hcl
  -- transport back along `M`
  have hfinal : (Set.range f)ᶜ = M.symm '' (Set.range g)ᶜ := by
    have h1 : Set.range g = M '' Set.range f := by
      ext x
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨f z, ⟨z, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
        exact ⟨z, rfl⟩
    have h2 : M.symm '' (Set.range g)ᶜ = (Set.range f)ᶜ := by
      rw [h1, Set.image_compl_eq M.symm.bijective, Set.image_image]
      simp
    exact h2.symm
  rw [hfinal]
  exact (M.symm.isPreconnected_image).mpr hpre


end

end Work.Smooth.SphereJordan
