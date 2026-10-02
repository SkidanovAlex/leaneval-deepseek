import Mathlib
import Submission.Work.StemsB.HurewiczFibration

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Triviality of a Hurewicz fibration over a based-contractible base

The input that the Serre exact sequence in the stable range
(`Submission/Work/StemsB/SerreExact.lean`) needs, in the shape in which it is applied: for a
**Hurewicz** fibration `p : E → B` the identity of `E` is homotopic, *over the base*, to a map into
the fibre `p⁻¹(d₀)` over the endpoint of a contraction of `B`.

* `Work.StemsB.fibreTrivial_of_contraction` — the triviality, over the whole base;
* `Work.StemsB.preimageIncl_homotopyEquiv_of_deformation` — the *controlled* form used at every
  thickening step: if `A ⊆ W ⊆ B` and `ρ` is a homotopy of `W` from the identity to a map into `A`
  which fixes `A` pointwise, then the inclusion `p⁻¹A ↪ p⁻¹W` is a homotopy equivalence, with the
  homotopies covering `ρ` (hence lying over the base, so that they restrict to the preimages of all
  subsets of `B` on which `ρ` is stable).

Both are immediate from the homotopy lifting property with respect to the total space, which is what
a Hurewicz fibration provides; `Work.StemsB.isHurewiczFibration_evalOne` shows that the path–loop
fibration has it, so the chapter applies to `evalOne X x₀ → X` for every `X`.
-/

open scoped Topology unitInterval

namespace Work.StemsB

noncomputable section

variable {E : Type} {B : Type} [TopologicalSpace E] [TopologicalSpace B]

theorem fibreTrivial_of_contraction (p : C(E, B)) (hp : IsHurewiczFibration p) (d₀ : B)
    (c : C(B × unitInterval, B)) (hc0 : ∀ b, c (b, 0) = b) (hc1 : ∀ b, c (b, 1) = d₀)
    (hcb : ∀ t, c (d₀, t) = d₀) :
    ∃ (g : C(E, fibre p d₀)) (G : C(E × unitInterval, E)),
      (∀ e, G (e, 0) = e) ∧ (∀ e, G (e, 1) = fibreIncl p d₀ (g e)) ∧
      (∀ e t, p (G (e, t)) = c (p e, t)) := by
  let K : C(unitInterval × E, B) := ⟨fun q => c (p q.2, q.1), by fun_prop⟩
  obtain ⟨g₀, H', hH'⟩ := hp E (ContinuousMap.id E) (ContinuousMap.const E d₀)
    (ContinuousMap.Homotopy.mk K (fun e => hc0 (p e)) (fun e => hc1 (p e)))
  have hcov : ∀ (t : unitInterval) (e : E), p (H'.toContinuousMap (t, e)) = c (p e, t) := by
    intro t e
    have h := congrFun (congrArg DFunLike.coe hH') (t, e)
    simp only [ContinuousMap.comp_apply, ContinuousMap.id_apply, K] at h
    exact h
  have hmem1 : ∀ e : E, p (g₀ e) = d₀ := fun e =>
    (congrArg p (H'.map_one_left e)).symm.trans ((hcov 1 e).trans (hc1 (p e)))
  refine ⟨⟨fun e => ⟨g₀ e, hmem1 e⟩, g₀.continuous.subtype_mk hmem1⟩,
    (H'.toContinuousMap).comp ⟨fun q => (q.2, q.1), by fun_prop⟩, ?_, ?_, ?_⟩
  · intro e
    exact H'.map_zero_left e
  · intro e
    exact H'.map_one_left e
  · intro e t
    exact hcov t e

theorem preimageIncl_homotopyEquiv_of_deformation (p : C(E, B)) (hp : IsHurewiczFibration p)
    (A W : Set B) (hAW : A ⊆ W) (ρ : C(↥W × unitInterval, ↥W)) (hρ0 : ∀ w, ρ (w, 0) = w)
    (hρ1 : ∀ w, (ρ (w, 1)).1 ∈ A)
    (hρA : ∀ (a : ↥A) (t), ρ (⟨a.1, hAW a.2⟩, t) = ⟨a.1, hAW a.2⟩) :
    ∃ (f : C(↥(p ⁻¹' W), ↥(p ⁻¹' A))) (g : C(↥(p ⁻¹' A), ↥(p ⁻¹' W))),
      (∀ x, (g x).1 = x.1) ∧
      (∃ (H : C((↥(p ⁻¹' W)) × unitInterval, ↥(p ⁻¹' W))),
        (∀ x, H (x, 0) = x) ∧ (∀ x, H (x, 1) = g (f x))) ∧
      (∃ (H' : C((↥(p ⁻¹' A)) × unitInterval, ↥(p ⁻¹' A))),
        (∀ x, H' (x, 0) = x) ∧ (∀ x, H' (x, 1) = f (g x))) := by
  let wOf : ↥(p ⁻¹' W) → ↥W := fun x => ⟨p x.1, x.2⟩
  let inc : C(↥(p ⁻¹' W), E) := ⟨Subtype.val, continuous_subtype_val⟩
  let b : C(↥(p ⁻¹' W), B) := ⟨fun x => (ρ (wOf x, 1) : ↥W).1, by fun_prop⟩
  let K : C(unitInterval × ↥(p ⁻¹' W), B) :=
    ⟨fun q => (ρ (wOf q.2, q.1) : ↥W).1, by fun_prop⟩
  obtain ⟨g₀, H', hH'⟩ := hp ↥(p ⁻¹' W) inc b
    (ContinuousMap.Homotopy.mk K
      (fun x => by
        show (ρ (wOf x, 0) : ↥W).1 = p x.1
        rw [hρ0])
      (fun x => rfl))
  have hcov : ∀ (x : ↥(p ⁻¹' W)) (t : unitInterval),
      p (H'.toContinuousMap (t, x)) = (ρ (wOf x, t) : ↥W).1 := by
    intro x t
    have h := congrFun (congrArg DFunLike.coe hH') (t, x)
    simp only [ContinuousMap.comp_apply, K] at h
    exact h
  have hmem : ∀ x : ↥(p ⁻¹' W), p (g₀ x) ∈ A := by
    intro x
    have heq : p (g₀ x) = (ρ (wOf x, 1) : ↥W).1 :=
      (congrArg p (H'.map_one_left x)).symm.trans (hcov x 1)
    rw [heq]
    exact hρ1 (wOf x)
  let f : C(↥(p ⁻¹' W), ↥(p ⁻¹' A)) :=
    ⟨fun x => ⟨g₀ x, hmem x⟩, g₀.continuous.subtype_mk hmem⟩
  let g : C(↥(p ⁻¹' A), ↥(p ⁻¹' W)) :=
    ⟨fun x => ⟨x.1, hAW x.2⟩, continuous_subtype_val.subtype_mk _⟩
  -- the first homotopy: the lift covers `ρ`, so it stays over `W`
  have hH1mem : ∀ q : ↥(p ⁻¹' W) × unitInterval, p (H'.toContinuousMap (q.2, q.1)) ∈ W := by
    intro q
    rw [hcov q.1 q.2]
    exact (ρ (wOf q.1, q.2) : ↥W).2
  have hH1cont : Continuous fun q : ↥(p ⁻¹' W) × unitInterval =>
      (⟨H'.toContinuousMap (q.2, q.1), hH1mem q⟩ : ↥(p ⁻¹' W)) :=
    Continuous.subtype_mk ((H'.toContinuousMap.comp
      ⟨fun q : ↥(p ⁻¹' W) × unitInterval => (q.2, q.1), by fun_prop⟩).continuous) hH1mem
  -- the second homotopy: on `p⁻¹A` the base coordinate is fixed by `ρ`
  have hH2mem : ∀ q : ↥(p ⁻¹' A) × unitInterval, p (H'.toContinuousMap (q.2, g q.1)) ∈ A := by
    intro q
    rw [hcov (g q.1) q.2]
    rw [show wOf (g q.1) = (⟨p q.1.1, hAW q.1.2⟩ : ↥W) from Subtype.ext rfl]
    rw [hρA (⟨p q.1.1, q.1.2⟩ : ↥A) q.2]
    exact q.1.2
  have hH2cont : Continuous fun q : ↥(p ⁻¹' A) × unitInterval =>
      (⟨H'.toContinuousMap (q.2, g q.1), hH2mem q⟩ : ↥(p ⁻¹' A)) :=
    Continuous.subtype_mk ((H'.toContinuousMap.comp
      ⟨fun q : ↥(p ⁻¹' A) × unitInterval => (q.2, g q.1), by fun_prop⟩).continuous) hH2mem
  refine ⟨f, g, ?_, ⟨⟨_, hH1cont⟩, ?_, ?_⟩, ⟨⟨_, hH2cont⟩, ?_, ?_⟩⟩
  · intro x; rfl
  · intro x
    exact Subtype.ext (H'.map_zero_left x)
  · intro x
    exact Subtype.ext (H'.map_one_left x)
  · intro x
    exact Subtype.ext (H'.map_zero_left (g x))
  · intro x
    exact Subtype.ext (H'.map_one_left (g x))

end

end Work.StemsB
