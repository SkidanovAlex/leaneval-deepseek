import Mathlib
import Submission.Work.RatHurewicz.AssemblyDefs
import Submission.Work.RatHurewicz.cubePinchDefs
import Submission.Work.ThomBordism.TwoSet.ConeDescent
import Submission.Work.RatHurewicz.GluingPinch.PinchAll
import Submission.Work.RatHurewicz.GluingPinch.pinchAll
import Submission.Work.RatHurewicz.glue_homotopic_const
import Submission.Work.Stems.Hur2b.homotopic_const_of_boundary_const

namespace Work.RatHurewicz


/-!
## The cancellation half

`Work.RatHurewicz.glue_homotopic_const` (proved, sorry-free) says that the gluing `glue` is freely
null-homotopic.  Pulling that homotopy back along a collapse `φ` (constant on `∂I^{m+2}`) gives a
homotopy `I^{m+2} × I → X` from `glue ∘ φ` to a constant which is constant on `∂I^{m+2}` at every
time, so `Work.Stems.Hur2b.homotopic_const_of_boundary_const` makes the class trivial.

Hence, for the collapse `φ` of the statement, `cl (glue ∘ φ) = 1`, and the statement of
`glue_class_of_collapse` becomes *equivalent* to the vanishing of the alternating product
`∏ (cl piece) ^ esign` — which is exactly Hutchings' `(2.5)`
(`Work.RatHurewicz.Psi_kills_boundary`).  See `PINCH_NOTES.md` for the remaining "pinch".
-/


/-!
## The bridge to the cubical homotopy-addition statement

`Work.RatHurewicz.cubePinch` is the general form of Hutchings `(2.2b)` for a cube that is `x₀` on
its `(k-1)`-skeleton: the signed product of its face classes is `1`.  The bridge from the pinch of
`glue_class_of_collapse` to it is the following observation, which shows that the `(i,b)`-face of an
*extension* of `glue` over `I^{m+3}` **is** the piece `(i,b)` (not merely a reparametrisation of it):
on the face `{z i = cval b}` of `∂I^{m+3}` the gluing is `piece (i,b) ∘ delG i`, and `delG i` is a
left inverse of the face inclusion.
-/

/-- **An extension of the gluing has the pieces as its faces.** -/
theorem faceCube_glue_eq_piece {X : Type} [TopologicalSpace X] {x₀ : X}
    (N m : ℕ) (K : Tower x₀ N) (hN : m + 1 ≤ N) (τ : C(Work.Stems.Cubical.IC (m + 3), X))
    (G : C(Work.Stems.Cubical.IC (m + 3), X))
    (hG : ∀ z : ↥(Cube.boundary (Fin (m + 3))),
      G (z : Work.Stems.Cubical.IC (m + 3)) = glue N m K hN τ z)
    (h : ∀ z : Work.Stems.Cubical.IC (m + 3), InSkel (m + 2) z → G z = x₀)
    (i : Fin (m + 3)) (b : Bool) :
    faceCube (m + 2) G h i b = piece N m K hN τ (i, if b then 1 else 0) := by
  apply GenLoop.ext
  intro u
  show G (Work.Stems.Cubical.faceCM i (if b then 1 else 0) u)
    = (piece N m K hN τ (i, if b then 1 else 0)).1 u
  have hmem : Work.Stems.Cubical.faceCM i (if b then 1 else 0) u
      ∈ Cube.boundary (Fin (m + 3)) := by
    rcases b with _ | _
    · exact mem_cubeBoundary_faceCM_cval i (0 : Fin 2) u
    · exact mem_cubeBoundary_faceCM_cval i (1 : Fin 2) u
  rw [hG ⟨_, hmem⟩]
  have hface : (Work.Stems.Cubical.faceCM i (if b then 1 else 0) u)
      ∈ faceSet m i (if b then 1 else 0) := by
    rw [mem_faceSet_iff, Work.Stems.Cubical.faceCM_apply, faceFun_apply_same]
    rcases b with _ | _ <;> rfl
  rw [glue_apply_face N m K hN τ (i, if b then 1 else 0) ⟨_, hmem⟩ hface]
  show (piece N m K hN τ (i, if b then 1 else 0)).1
      (delG (m + 2) i (Work.Stems.Cubical.faceCM i (if b then 1 else 0) u))
    = (piece N m K hN τ (i, if b then 1 else 0)).1 u
  rw [faceCM_delG]


/-! ## The two cheap ingredients of the reduction

With the bridge `faceCube_glue_eq_piece` above, the target reduces to the *general* cubical
homotopy-addition statement (`Work.RatHurewicz.cubePinch`), plus the existence of an extension of
`glue` over the cube.  The extension is supplied by the already-proved coning lemma
`Work.ThomBordism.TwoSet.ConeDescent` applied to the free null-homotopy `glue_homotopic_const`.
-/

/-- **The gluing extends over the cube.** -/
theorem glue_extends {X : Type} [TopologicalSpace X] {x₀ : X}
    (N m : ℕ) (K : Tower x₀ N) (hN : m + 1 ≤ N) (τ : C(Work.Stems.Cubical.IC (m + 3), X)) :
    ∃ G : C(Work.Stems.Cubical.IC (m + 3), X),
      ∀ z : ↥(Cube.boundary (Fin (m + 3))),
        G (z : Work.Stems.Cubical.IC (m + 3)) = glue N m K hN τ z := by
  obtain ⟨H, z, h0, h1⟩ := glue_homotopic_const N m K hN τ
  obtain ⟨G, hG⟩ := Work.ThomBordism.TwoSet.ConeDescent (m := m + 3) (by omega) H
    (fun x => h1 x)
  exact ⟨G, fun z => (hG z).trans (h0 z)⟩

/-- A point of `I^{m+3}` on two coordinates `0` or `1` is on two *faces* of the boundary, hence
the gluing is `x₀` there. -/
theorem glue_eq_x₀_of_InSkel {X : Type} [TopologicalSpace X] {x₀ : X}
    (N m : ℕ) (K : Tower x₀ N) (hN : m + 1 ≤ N) (τ : C(Work.Stems.Cubical.IC (m + 3), X))
    {z : Work.Stems.Cubical.IC (m + 3)} (hz : InSkel (m + 2) z) :
    glue N m K hN τ ⟨z, by
      obtain ⟨j, _, _, hj, _⟩ := hz
      exact ⟨j, hj⟩⟩ = x₀ := by
  obtain ⟨j, j', hjj, hj, hj'⟩ := hz
  have hmem : ∀ (i : Fin (m + 3)) (hi : z i = 0 ∨ z i = 1),
      z ∈ faceSet m i (if z i = 0 then 0 else 1) := by
    intro i hi
    rw [mem_faceSet_iff]
    by_cases h : z i = 0
    · rw [if_pos h]; exact h.trans (cval_zero).symm
    · rw [if_neg h]
      exact hi.resolve_left h |>.trans (cval_one).symm
  exact glue_eq_x₀_of_mem_two N m K hN τ ⟨z, _⟩
    (hmem j hj) (hmem j' hj') hjj

/-- **The cancellation half**: for a collapse `φ`, the class of `glue ∘ φ` is trivial. -/
theorem glue_comp_collapse_class_eq_one {X : Type} [TopologicalSpace X] {x₀ : X}
    (N m : ℕ) (K : Work.RatHurewicz.Tower x₀ N) (hN : m + 1 ≤ N)
    (τ : C(Work.Stems.Cubical.IC (m + 3), X))
    (φ : C(Work.Stems.Cubical.IC (m + 2), ↥(Cube.boundary (Fin (m + 3)))))
    (hφ : ∀ u ∈ Cube.boundary (Fin (m + 2)), φ u = φ 0)
    (hv : Work.RatHurewicz.glue N m K hN τ (φ 0) = x₀) :
    Work.RatHurewicz.cl (m + 2) X x₀
      ⟨(Work.RatHurewicz.glue N m K hN τ).comp φ, fun u hu => by
        rw [ContinuousMap.comp_apply, hφ u hu, hv]⟩ = 1 := by
  obtain ⟨H, z, h0, h1⟩ := Work.RatHurewicz.glue_homotopic_const N m K hN τ
  let Hc : C(Work.Stems.Cubical.IC (m + 2) × unitInterval, X) :=
    H.comp (φ.prodMap (ContinuousMap.id unitInterval))
  have hHc : ∀ (u : Work.Stems.Cubical.IC (m + 2)) (t : unitInterval),
      Hc (u, t) = H (φ u, t) := fun _ _ => rfl
  have hb : ∀ (y y' : Work.Stems.Cubical.IC (m + 2)) (t : unitInterval),
      y ∈ Cube.boundary (Fin (m + 2)) → y' ∈ Cube.boundary (Fin (m + 2)) →
      Hc (y, t) = Hc (y', t) := by
    intro y y' t hy hy'
    rw [hHc, hHc, hφ y hy, hφ y' hy']
  have hom := Work.Stems.Hur2b.homotopic_const_of_boundary_const (m + 2)
    ⟨(Work.RatHurewicz.glue N m K hN τ).comp φ, fun u hu => by
      rw [ContinuousMap.comp_apply, hφ u hu, hv]⟩ z Hc
    (fun y => by rw [hHc, h0]; rfl) (fun y => by rw [hHc, h1]) hb
  have : (show HomotopyGroup (Fin (m + 2)) X x₀ from
      Quotient.mk _ ⟨(Work.RatHurewicz.glue N m K hN τ).comp φ, fun u hu => by
        rw [ContinuousMap.comp_apply, hφ u hu, hv]⟩) = 1 := by
    rw [HomotopyGroup.one_def]
    exact Quotient.sound hom
  simpa only [Work.RatHurewicz.cl] using this

/-- **The reduction**: if the alternating product of the classes of the pieces is trivial (Hutchings'
`(2.5)`), then `glue_class_of_collapse` follows from the cancellation half. -/
theorem glue_class_of_collapse_of_prod_eq_one {X : Type} [TopologicalSpace X] {x₀ : X}
    (N m : ℕ) (K : Work.RatHurewicz.Tower x₀ N) (hN : m + 1 ≤ N)
    [Nontrivial (Fin (m + 2))]
    (τ : C(Work.Stems.Cubical.IC (m + 3), X))
    (φ : C(Work.Stems.Cubical.IC (m + 2), ↥(Cube.boundary (Fin (m + 3)))))
    (hφ : ∀ u ∈ Cube.boundary (Fin (m + 2)), φ u = φ 0)
    (hv : Work.RatHurewicz.glue N m K hN τ (φ 0) = x₀)
    (hP : (∏ i : Fin (m + 3), ∏ b : Fin 2,
            (Work.RatHurewicz.cl (m + 2) X x₀ (Work.RatHurewicz.piece N m K hN τ (i, b)))
              ^ (Work.RatHurewicz.esign m i b)) = 1) :
    (Work.RatHurewicz.cl (m + 2) X x₀
        ⟨(Work.RatHurewicz.glue N m K hN τ).comp φ, fun u hu => by
          rw [ContinuousMap.comp_apply, hφ u hu, hv]⟩
      = ∏ i : Fin (m + 3), ∏ b : Fin 2,
          (Work.RatHurewicz.cl (m + 2) X x₀ (Work.RatHurewicz.piece N m K hN τ (i, b)))
            ^ (Work.RatHurewicz.esign m i b))
    ∨ (Work.RatHurewicz.cl (m + 2) X x₀
        ⟨(Work.RatHurewicz.glue N m K hN τ).comp φ, fun u hu => by
          rw [ContinuousMap.comp_apply, hφ u hu, hv]⟩
      = (∏ i : Fin (m + 3), ∏ b : Fin 2,
          (Work.RatHurewicz.cl (m + 2) X x₀ (Work.RatHurewicz.piece N m K hN τ (i, b)))
            ^ (Work.RatHurewicz.esign m i b))⁻¹) := by
  left
  rw [glue_comp_collapse_class_eq_one N m K hN τ φ hφ hv, hP]


/-- **The target from the nullity of the assembly** (the intended use, cf. `ASSEMBLY_NOTES.md`):
if the assembly of the pieces of `τ` is null-homotopic, then the alternating product of the
classes of the pieces is `1`, and `glue_class_of_collapse` follows from the cancellation half. -/
theorem glue_class_of_collapse_of_assembly_null {X : Type} [TopologicalSpace X] {x₀ : X}
    (N m : ℕ) (K : Work.RatHurewicz.Tower x₀ N) (hN : m + 1 ≤ N)
    [Nontrivial (Fin (m + 2))]
    (τ : C(Work.Stems.Cubical.IC (m + 3), X))
    (h : GenLoop.Homotopic (Work.RatHurewicz.assembly N m K hN τ) GenLoop.const)
    (φ : C(Work.Stems.Cubical.IC (m + 2), ↥(Cube.boundary (Fin (m + 3)))))
    (hφ : ∀ u ∈ Cube.boundary (Fin (m + 2)), φ u = φ 0)
    (hv : Work.RatHurewicz.glue N m K hN τ (φ 0) = x₀) :
    (Work.RatHurewicz.cl (m + 2) X x₀
        ⟨(Work.RatHurewicz.glue N m K hN τ).comp φ, fun u hu => by
          rw [ContinuousMap.comp_apply, hφ u hu, hv]⟩
      = ∏ i : Fin (m + 3), ∏ b : Fin 2,
          (Work.RatHurewicz.cl (m + 2) X x₀ (Work.RatHurewicz.piece N m K hN τ (i, b)))
            ^ (Work.RatHurewicz.esign m i b))
    ∨ (Work.RatHurewicz.cl (m + 2) X x₀
        ⟨(Work.RatHurewicz.glue N m K hN τ).comp φ, fun u hu => by
          rw [ContinuousMap.comp_apply, hφ u hu, hv]⟩
      = (∏ i : Fin (m + 3), ∏ b : Fin 2,
          (Work.RatHurewicz.cl (m + 2) X x₀ (Work.RatHurewicz.piece N m K hN τ (i, b)))
            ^ (Work.RatHurewicz.esign m i b))⁻¹) := by
  have hnull : Work.RatHurewicz.cl (m + 2) X x₀ (Work.RatHurewicz.assembly N m K hN τ) = 1 := by
    have h' : (⟦Work.RatHurewicz.assembly N m K hN τ⟧ :
        Quotient (GenLoop.Homotopic.setoid (Fin (m + 2)) x₀)) = ⟦GenLoop.const⟧ :=
      Quotient.sound h
    exact h'
  have hP : (∏ i : Fin (m + 3), ∏ b : Fin 2,
      (Work.RatHurewicz.cl (m + 2) X x₀ (Work.RatHurewicz.piece N m K hN τ (i, b)))
        ^ (Work.RatHurewicz.esign m i b)) = 1 := by
    rw [← Work.RatHurewicz.assembly_class N m K hN τ, hnull]
  exact glue_class_of_collapse_of_prod_eq_one N m K hN τ φ hφ hv hP


/-! ## The exact remaining gap: the general cubical homotopy addition

`PinchAll` is Hutchings `(2.2b)` in its sharpest form (for every `k`): a cube that is `x₀` on its
`(k-1)`-skeleton has face classes whose signed product is `1`.  This is the statement of the
colleague's target `Work.RatHurewicz.cubePinch` (there `k` is fixed, but the proof is uniform),
and its `k = 2` case is *proved* (`Stems/Hur2b`: the T-net and its collar).

The theorem below is the **exact reduction**: `PinchAll` ⟹ the requested pinch
`glue_class_of_collapse`.  All the other ingredients are proved in this file:
`glue_extends` (the coning lemma applied to `glue_homotopic_const`) and
`faceCube_glue_eq_piece` (the faces of an extension of `glue` *are* the pieces), together with the
cancellation half `glue_comp_collapse_class_eq_one`.
-/

/-- **The reduction.**  The general homotopy-addition statement implies the pinch. -/
theorem glue_class_of_collapse_of_pinch (hpinch : PinchAll)
    {X : Type} [TopologicalSpace X] {x₀ : X}
    (N m : ℕ) (K : Tower x₀ N) (hN : m + 1 ≤ N) [Nontrivial (Fin (m + 2))]
    (τ : C(Work.Stems.Cubical.IC (m + 3), X))
    (φ : C(Work.Stems.Cubical.IC (m + 2), ↥(Cube.boundary (Fin (m + 3)))))
    (hφ : ∀ u ∈ Cube.boundary (Fin (m + 2)), φ u = φ 0)
    (hv : glue N m K hN τ (φ 0) = x₀)
    (hinj : ∀ u v : Work.Stems.Cubical.IC (m + 2),
      u ∉ Cube.boundary (Fin (m + 2)) → φ u = φ v → u = v) :
    (cl (m + 2) X x₀
        ⟨(glue N m K hN τ).comp φ, fun u hu => by
          rw [ContinuousMap.comp_apply, hφ u hu, hv]⟩
      = ∏ i : Fin (m + 3), ∏ b : Fin 2,
          (cl (m + 2) X x₀ (piece N m K hN τ (i, b))) ^ (esign m i b))
    ∨ (cl (m + 2) X x₀
        ⟨(glue N m K hN τ).comp φ, fun u hu => by
          rw [ContinuousMap.comp_apply, hφ u hu, hv]⟩
      = (∏ i : Fin (m + 3), ∏ b : Fin 2,
          (cl (m + 2) X x₀ (piece N m K hN τ (i, b))) ^ (esign m i b))⁻¹) := by
  obtain ⟨G, hG⟩ := glue_extends N m K hN τ
  have hInSkel : ∀ z : Work.Stems.Cubical.IC (m + 3), InSkel (m + 2) z → G z = x₀ := by
    intro z hz
    have hb : z ∈ Cube.boundary (Fin (m + 3)) := by
      obtain ⟨j, _, _, hj, _⟩ := hz
      exact ⟨j, hj⟩
    rw [hG ⟨z, hb⟩]
    exact glue_eq_x₀_of_InSkel N m K hN τ hz
  have hp := hpinch (m + 2) X x₀ G hInSkel
  have hb0 : ∀ i : Fin (m + 3),
      faceCube (m + 2) G hInSkel i false = piece N m K hN τ (i, 0) :=
    fun i => faceCube_glue_eq_piece N m K hN τ G hG hInSkel i false
  have hb1 : ∀ i : Fin (m + 3),
      faceCube (m + 2) G hInSkel i true = piece N m K hN τ (i, 1) :=
    fun i => faceCube_glue_eq_piece N m K hN τ G hG hInSkel i true
  have hprod : (∏ i : Fin (m + 3),
      (cl (m + 2) X x₀ (piece N m K hN τ (i, 0))) ^ ((-1 : ℤ) ^ (i : ℕ)) *
      (cl (m + 2) X x₀ (piece N m K hN τ (i, 1))) ^ (-((-1 : ℤ) ^ (i : ℕ)))) = 1 := by
    rw [← hp]
    exact Finset.prod_congr rfl fun i _ => by rw [hb0 i, hb1 i]
  have he0 : ∀ i : Fin (m + 3), esign m i (0 : Fin 2) = (-1 : ℤ) ^ (i : ℕ) := by
    intro i
    rw [esign, Fin.val_zero, Nat.add_zero]
  have he1 : ∀ i : Fin (m + 3), esign m i (1 : Fin 2) = -((-1 : ℤ) ^ (i : ℕ)) := by
    intro i
    rw [esign, Fin.val_one, pow_succ]
    ring
  have hP : (∏ i : Fin (m + 3), ∏ b : Fin 2,
      (cl (m + 2) X x₀ (piece N m K hN τ (i, b))) ^ (esign m i b)) = 1 := by
    rw [← hprod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fin.prod_univ_two, he0 i, he1 i]
  exact glue_class_of_collapse_of_prod_eq_one N m K hN τ φ hφ hv hP

theorem glue_class_of_collapse {X : Type} [TopologicalSpace X] {x₀ : X}
    (N m : ℕ) (K : Work.RatHurewicz.Tower x₀ N) (hN : m + 1 ≤ N) [Nontrivial (Fin (m + 2))]
    (τ : C(Work.Stems.Cubical.IC (m + 3), X))
    (φ : C(Work.Stems.Cubical.IC (m + 2), ↥(Cube.boundary (Fin (m + 3)))))
    (hφ : ∀ u ∈ Cube.boundary (Fin (m + 2)), φ u = φ 0)
    (hv : Work.RatHurewicz.glue N m K hN τ (φ 0) = x₀)
    (hinj : ∀ u v : Work.Stems.Cubical.IC (m + 2),
      u ∉ Cube.boundary (Fin (m + 2)) → φ u = φ v → u = v) :
    (Work.RatHurewicz.cl (m + 2) X x₀
        ⟨(Work.RatHurewicz.glue N m K hN τ).comp φ, fun u hu => by
          rw [ContinuousMap.comp_apply, hφ u hu, hv]⟩
      = ∏ i : Fin (m + 3), ∏ b : Fin 2,
          (Work.RatHurewicz.cl (m + 2) X x₀ (Work.RatHurewicz.piece N m K hN τ (i, b)))
            ^ (Work.RatHurewicz.esign m i b))
    ∨ (Work.RatHurewicz.cl (m + 2) X x₀
        ⟨(Work.RatHurewicz.glue N m K hN τ).comp φ, fun u hu => by
          rw [ContinuousMap.comp_apply, hφ u hu, hv]⟩
      = (∏ i : Fin (m + 3), ∏ b : Fin 2,
          (Work.RatHurewicz.cl (m + 2) X x₀ (Work.RatHurewicz.piece N m K hN τ (i, b)))
            ^ (Work.RatHurewicz.esign m i b))⁻¹) :=
  glue_class_of_collapse_of_pinch Work.RatHurewicz.GluingPinch.pinchAll
    N m K hN τ φ hφ hv hinj

end Work.RatHurewicz
