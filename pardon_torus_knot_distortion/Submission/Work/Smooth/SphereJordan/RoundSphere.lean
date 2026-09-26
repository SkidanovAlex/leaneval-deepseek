import Submission.Work.Smooth.SphereJordan.RiemannSphere

/-!
# Jordan–Schoenflies on the round sphere, and its consequences

`Work.Topology.Classical.JordanSchoenfliesSphere` is the *stated* sphere-side classical input of the
delivered chapters: Jordan–Schoenflies on `RoundSphere = Metric.sphere (0 : ℝ³) 1` together with the
standard position (nesting) of finitely many pairwise disjoint Jordan curves on it.  This file proves
it from `Work.Smooth.SphereJordan.JordanSchoenfliesRiemannSphere` — the same statement for
`ℂ ∪ {∞}` — by transporting every datum along Mathlib's stereographic homeomorphism
`riemannSphereHomeomorph : (ℂ ∪ {∞}) ≃ₜ S²`.

The transfer is purely bookkeeping: curves are moved by `Φ.symm`, the discs and the rank are pushed
forward by `Φ`, and every clause of the statement is checked in the subtype
`RoundSphere = {x : ℝ³ // ‖x‖ = 1}`: injectivity, the boundary in the given parametrisation, the
containment of the discs in the sphere, the openness of the image of the open disc (openness is
preserved by the homeomorphism `Φ`), the covering, the fact that the two discs meet exactly in the
curve (the coercion `RoundSphere → ℝ³` is injective), and the nesting of the ranks.
-/

open Set
open LeanEval.KnotTheory.PardonDistortion

namespace Work.Smooth.SphereJordan

noncomputable section

/-- **Jordan–Schoenflies on the round sphere and standard position of a finite family of pairwise
disjoint Jordan curves**, from the Riemann-sphere version. -/
theorem jordanSchoenfliesSphere_of_riemannSphere (h : JordanSchoenfliesRiemannSphere) :
    Work.Topology.Classical.JordanSchoenfliesSphere := by
  classical
  intro ι _ c hc hd
  let Φ : RiemannSphere ≃ₜ Work.Smooth.Jordan.RoundSphere := riemannSphereHomeomorph
  let c' : ι → ℝ → RiemannSphere := fun i t => Φ.symm ⟨c i t, (hc i).1 t⟩
  have hc' : ∀ i : ι, IsSimpleClosedCurve (c' i) := by
    intro i
    refine ⟨?_, ?_, ?_⟩
    · exact Φ.symm.continuous.comp (Continuous.subtype_mk (hc i).2.1 (fun t => (hc i).1 t))
    · intro t
      exact congrArg Φ.symm (Subtype.ext (by simpa using (hc i).2.2.1 t))
    · intro a ha b hb hab
      exact (hc i).2.2.2 ha hb (Subtype.ext_iff.mp (Φ.symm.injective hab))
  have hd' : Pairwise fun i j : ι => Disjoint (Set.range (c' i)) (Set.range (c' j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    rintro x ⟨t, rfl⟩ ⟨s, hs⟩
    have h1 : c' i t = c' j s := hs.symm
    have h2 : c i t = c j s := Subtype.ext_iff.mp (Φ.symm.injective h1)
    exact Set.disjoint_left.mp (hd hij) ⟨t, rfl⟩ ⟨s, h2.symm⟩
  obtain ⟨D⟩ := h ι c' hc' hd'
  let e : ι → C(Disc, R3) := fun i =>
    ⟨fun z => ((Φ (D.e i z) : Work.Smooth.Jordan.RoundSphere) : R3),
      continuous_subtype_val.comp (Φ.continuous.comp (D.e i).continuous)⟩
  let e' : ι → C(Disc, R3) := fun i =>
    ⟨fun z => ((Φ (D.e' i z) : Work.Smooth.Jordan.RoundSphere) : R3),
      continuous_subtype_val.comp (Φ.continuous.comp (D.e' i).continuous)⟩
  have hcoe : ∀ (i : ι) (t : ℝ),
      ((Φ (c' i t) : Work.Smooth.Jordan.RoundSphere) : R3) = c i t := by
    intro i t
    simp only [c']
    rw [Homeomorph.apply_symm_apply]
  have hrange_e : ∀ i : ι, Set.range (e i) =
      (fun y : RiemannSphere => ((Φ y : Work.Smooth.Jordan.RoundSphere) : R3)) '' Set.range (D.e i) := by
    intro i
    ext x; constructor
    · rintro ⟨z, rfl⟩
      exact ⟨D.e i z, ⟨z, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, rfl⟩
  have hrange_e' : ∀ i : ι, Set.range (e' i) =
      (fun y : RiemannSphere => ((Φ y : Work.Smooth.Jordan.RoundSphere) : R3)) '' Set.range (D.e' i) := by
    intro i
    ext x; constructor
    · rintro ⟨z, rfl⟩
      exact ⟨D.e' i z, ⟨z, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, rfl⟩
  have hrange_c : ∀ i : ι, Set.range (c i) =
      (fun y : RiemannSphere => ((Φ y : Work.Smooth.Jordan.RoundSphere) : R3)) '' Set.range (c' i) := by
    intro i
    ext x; constructor
    · rintro ⟨t, rfl⟩
      exact ⟨c' i t, ⟨t, rfl⟩, hcoe i t⟩
    · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, (hcoe i t).symm⟩
  refine ⟨e, e', D.rank, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i a b hab
    exact D.inj i (Φ.injective (Subtype.ext hab))
  · intro i a b hab
    exact D.inj' i (Φ.injective (Subtype.ext hab))
  · intro i θ
    have h1 : D.e i (circlePoint θ) = c' i θ := D.boundary i θ
    have h2 := congrArg (fun y : Work.Smooth.Jordan.RoundSphere => (y : R3)) (congrArg Φ h1)
    simp only [e]
    exact h2.trans (hcoe i θ)
  · intro i θ
    have h1 : D.e' i (circlePoint θ) = c' i θ := D.boundary' i θ
    have h2 := congrArg (fun y : Work.Smooth.Jordan.RoundSphere => (y : R3)) (congrArg Φ h1)
    simp only [e']
    exact h2.trans (hcoe i θ)
  · intro i z
    change ((Φ (D.e i z) : Work.Smooth.Jordan.RoundSphere) : R3) ∈ Work.Smooth.Jordan.RoundSphere
    exact (Φ (D.e i z)).2
  · intro i z
    change ((Φ (D.e' i z) : Work.Smooth.Jordan.RoundSphere) : R3) ∈ Work.Smooth.Jordan.RoundSphere
    exact (Φ (D.e' i z)).2
  · intro i
    have h1 : {x : Work.Smooth.Jordan.RoundSphere |
        ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧
          ((Φ (D.e i z) : Work.Smooth.Jordan.RoundSphere) : R3) = (x : R3)} =
        Φ '' {y : RiemannSphere | ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ D.e i z = y} := by
      ext x; constructor
      · rintro ⟨z, hz, hxz⟩
        exact ⟨D.e i z, ⟨z, hz, rfl⟩, Subtype.ext hxz⟩
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        exact ⟨z, hz, rfl⟩
    change IsOpen {x : Work.Smooth.Jordan.RoundSphere |
        ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧
          ((Φ (D.e i z) : Work.Smooth.Jordan.RoundSphere) : R3) = (x : R3)}
    rw [h1]
    exact Φ.isOpenMap _ (D.open_interior i)
  · intro i
    have h1 : {x : Work.Smooth.Jordan.RoundSphere |
        ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧
          ((Φ (D.e' i z) : Work.Smooth.Jordan.RoundSphere) : R3) = (x : R3)} =
        Φ '' {y : RiemannSphere | ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ D.e' i z = y} := by
      ext x; constructor
      · rintro ⟨z, hz, hxz⟩
        exact ⟨D.e' i z, ⟨z, hz, rfl⟩, Subtype.ext hxz⟩
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        exact ⟨z, hz, rfl⟩
    change IsOpen {x : Work.Smooth.Jordan.RoundSphere |
        ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧
          ((Φ (D.e' i z) : Work.Smooth.Jordan.RoundSphere) : R3) = (x : R3)}
    rw [h1]
    exact Φ.isOpenMap _ (D.open_interior' i)
  · intro i
    rw [hrange_e i, hrange_e' i]
    apply Set.Subset.antisymm
    · rintro x (⟨y, -, rfl⟩ | ⟨y, -, rfl⟩)
      · exact (Φ y).2
      · exact (Φ y).2
    · intro x hx
      have h1 : Φ.symm (⟨x, hx⟩ : Work.Smooth.Jordan.RoundSphere) ∈
          Set.range (D.e i) ∪ Set.range (D.e' i) := by
        rw [D.cover i]; exact Set.mem_univ _
      rcases h1 with ⟨z, hz⟩ | ⟨z, hz⟩
      · refine Or.inl ⟨D.e i z, ⟨z, rfl⟩, ?_⟩
        have h2 : Φ (D.e i z) = (⟨x, hx⟩ : Work.Smooth.Jordan.RoundSphere) := by
          rw [hz, Homeomorph.apply_symm_apply]
        exact congrArg Subtype.val h2
      · refine Or.inr ⟨D.e' i z, ⟨z, rfl⟩, ?_⟩
        have h2 : Φ (D.e' i z) = (⟨x, hx⟩ : Work.Smooth.Jordan.RoundSphere) := by
          rw [hz, Homeomorph.apply_symm_apply]
        exact congrArg Subtype.val h2
  · intro i
    have hinj_map : Function.Injective
        (fun y : RiemannSphere => ((Φ y : Work.Smooth.Jordan.RoundSphere) : R3)) := by
      intro a b hab
      exact Φ.injective (Subtype.ext hab)
    rw [hrange_e i, hrange_e' i, ← Set.image_inter hinj_map, D.meet i, hrange_c i]
  · intro i j hij
    obtain ⟨z, hz, hmem⟩ := hij
    change ((Φ (D.e i z) : Work.Smooth.Jordan.RoundSphere) : R3) ∈ Set.range (c j) at hmem
    obtain ⟨t, ht⟩ := hmem
    have ht' : Φ (D.e i z) = Φ (c' j t) := by
      apply Subtype.ext
      rw [ht.symm]
      exact (hcoe j t).symm
    exact D.nested i j ⟨z, hz, ⟨t, (Φ.injective ht').symm⟩⟩

/-- **Jordan–Schoenflies on the round sphere**, from the planar Jordan–Schoenflies theorem. -/
theorem jordanSchoenfliesSphere (h : PlaneHypothesis) :
    Work.Topology.Classical.JordanSchoenfliesSphere :=
  jordanSchoenfliesSphere_of_riemannSphere (jordanSchoenfliesRiemannSphere h)

/-! ## Consequences: the statements consumed by the delivered chapters -/

/-- **Schoenflies on any surface homeomorphic to the round sphere** — the form in which the
smooth Jordan chapter (`Work.Smooth.Jordan.SchoenfliesOnInput`) consumes the sphere-side input. -/
theorem schoenfliesOnInput_of_homeomorph (h : PlaneHypothesis) {A : Set R3}
    (φ : Work.Smooth.Jordan.RoundSphere ≃ₜ A) : Work.Smooth.Jordan.SchoenfliesOnInput A :=
  Work.Smooth.Jordan.schoenfliesOnInput_of_homeomorph φ (jordanSchoenfliesSphere h)

/-- **Schoenflies on any surface homeomorphic to the round sphere**, with the homeomorphism pointing
the other way (`A ≃ₜ RoundSphere`). -/
theorem schoenfliesOnInput_of_homeomorph' (h : PlaneHypothesis) {A : Set R3}
    (φ : A ≃ₜ Work.Smooth.Jordan.RoundSphere) : Work.Smooth.Jordan.SchoenfliesOnInput A :=
  schoenfliesOnInput_of_homeomorph h φ.symm

/-- **Jordan–Schoenflies and the standard position of a finite family of pairwise disjoint Jordan
curves on the boundary `∂PBox s c σ` of Pardon's box**, from the planar theorem. -/
theorem nonempty_schoenfliesData_BoxSphere (h : PlaneHypothesis) {s : ℝ} (hs : 0 < s)
    (c : R3) (σ : Equiv.Perm (Fin 3)) {ι : Type} [Fintype ι] {γ : ι → ℝ → R3}
    (hc : ∀ i : ι, Work.Topology.Classical.IsJordanCurveOn
      (Work.Topology.SphereSlicing.BoxSphere s c σ) (γ i))
    (hd : Pairwise fun i j : ι => Disjoint (Set.range (γ i)) (Set.range (γ j))) :
    Nonempty (Work.Topology.Classical.SchoenfliesData
      (Work.Topology.SphereSlicing.BoxSphere s c σ) ι γ) :=
  Work.Topology.Classical.nonempty_schoenfliesData_BoxSphere (jordanSchoenfliesSphere h) hs c σ hc hd

/-- **Nested spanning discs for a finite family of pairwise disjoint Jordan curves on a surface
homeomorphic to the round sphere** (`Work.Smooth.Jordan.FamilyDiscs`), from the planar theorem. -/
theorem familyDiscs_of_homeomorph (h : PlaneHypothesis) {A : Set R3} {ι : Type} [Fintype ι]
    {c : ι → ℝ → R3} (φ : Work.Smooth.Jordan.RoundSphere ≃ₜ A)
    (hs : ∀ i : ι, Work.Smooth.Jordan.IsSimpleClosedCurveOn A (c i))
    (hd : Pairwise fun i j : ι => Disjoint (Set.range (c i)) (Set.range (c j))) :
    Nonempty (Work.Smooth.Jordan.FamilyDiscs A ι c) :=
  Work.Smooth.Jordan.familyDiscs_of_jordanSchoenfliesSphere φ (jordanSchoenfliesSphere h) hs hd

end

end Work.Smooth.SphereJordan
