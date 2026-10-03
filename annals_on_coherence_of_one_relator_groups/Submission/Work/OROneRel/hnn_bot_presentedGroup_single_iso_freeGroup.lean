import Mathlib
import Submission.Work.OROneRel.HNNTrivial
import Submission.Work.OROneRel.Basic

/-!
# `HNN(⟨β | x⟩, ⊥, ⊥, φ) ≃ F(β)`

The one-relator group `P = ⟨β | x⟩` presented by a single relation `x = 1` is the free group on the
remaining generators `β \ {x}`; adjoining the stable letter `t` of the HNN extension with trivial
associated subgroups adds one free generator back, and hence returns the free group on `β`.

The isomorphism is exhibited explicitly on generators: the two maps

* `HNN(P, ⊥, ⊥, φ) →* F(β)`, which kills `x`, fixes every other generator and sends the stable
  letter to `of x`;
* `F(β) →* HNN(P, ⊥, ⊥, φ)`, which sends the generator `x` to the stable letter and every other
  generator to its image in the base group `P`;

are inverse to each other on generators.
-/

namespace Work.OROneRel

universe u

/-- `HNN(⟨β | x⟩, ⊥, ⊥, φ) ≅ F(β)`. -/
theorem hnn_bot_presentedGroup_single_iso_freeGroup {β : Type u} (x : β)
    (φ : (⊥ : Subgroup (PresentedGroup ({FreeGroup.of x} : Set (FreeGroup β)))) ≃*
         (⊥ : Subgroup (PresentedGroup ({FreeGroup.of x} : Set (FreeGroup β))))) :
    Nonempty (HNNExtension (PresentedGroup ({FreeGroup.of x} : Set (FreeGroup β))) ⊥ ⊥ φ ≃*
      FreeGroup β) := by
  classical
  let P := PresentedGroup ({FreeGroup.of x} : Set (FreeGroup β))
  -- The function on generators of the map `P →* F(β)`: `x ↦ 1`, `a ↦ a`.
  let f : β → FreeGroup β := fun a => if h : a = x then 1 else FreeGroup.of a
  have hf : ∀ r ∈ ({FreeGroup.of x} : Set (FreeGroup β)), FreeGroup.lift f r = 1 := by
    intro r hr
    rw [Set.mem_singleton_iff] at hr
    subst hr
    rw [FreeGroup.lift_apply_of]
    exact dif_pos rfl
  let τ : P →* FreeGroup β := PresentedGroup.toGroup (f := f) hf
  have hτ (a : β) : τ (PresentedGroup.of a) = f a := PresentedGroup.toGroup.of (f := f) hf
  -- The map out of the HNN extension: `P ↦ F(β)` by `τ`, and `t ↦ of x`.
  let toF : HNNExtension P ⊥ ⊥ φ →* FreeGroup β :=
    HNNExtension.lift τ (FreeGroup.of x) (by
      intro a
      have ha : ((a : P)) = 1 := Subgroup.mem_bot.mp a.2
      have hb : (((φ a : (⊥ : Subgroup P)) : P)) = 1 := Subgroup.mem_bot.mp (φ a).2
      rw [ha, hb, map_one, mul_one, one_mul])
  have toF_of (p : P) : toF (HNNExtension.of p) = τ p := by simp [toF]
  have toF_t : toF HNNExtension.t = FreeGroup.of x := by simp [toF]
  -- The map into the HNN extension: `x ↦ t`, `a ↦ of a` for `a ≠ x`.
  let fromF : FreeGroup β →* HNNExtension P ⊥ ⊥ φ :=
    FreeGroup.lift fun a : β =>
      if h : a = x then HNNExtension.t else HNNExtension.of (PresentedGroup.of a : P)
  have fromF_of (a : β) : fromF (FreeGroup.of a) =
      (if h : a = x then HNNExtension.t else HNNExtension.of (PresentedGroup.of a : P)) :=
    FreeGroup.lift_apply_of
  -- In `P` the generator `x` is trivial.
  have hofx : (PresentedGroup.of x : P) = 1 := by
    show PresentedGroup.mk ({FreeGroup.of x} : Set (FreeGroup β)) (FreeGroup.of x) = 1
    exact PresentedGroup.one_of_mem (Set.mem_singleton _)
  have h1 : toF.comp fromF = MonoidHom.id (FreeGroup β) := by
    refine FreeGroup.ext_hom _ _ fun a => ?_
    rw [MonoidHom.comp_apply, MonoidHom.id_apply, fromF_of]
    by_cases ha : a = x
    · rw [dif_pos ha, toF_t, ha]
    · rw [dif_neg ha, toF_of, hτ a]
      change (if h : a = x then 1 else FreeGroup.of a) = FreeGroup.of a
      rw [dif_neg ha]
  have h2 : fromF.comp toF = MonoidHom.id (HNNExtension P ⊥ ⊥ φ) := by
    refine HNNExtension.hom_ext ?_ ?_
    · refine PresentedGroup.ext fun a => ?_
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
      by_cases ha : a = x
      · rw [ha, toF_of, hτ x]
        have hfx : f x = 1 := by
          change (if h : x = x then 1 else FreeGroup.of x) = 1
          rw [dif_pos rfl]
        rw [hfx, map_one, hofx, map_one]
      · rw [toF_of, hτ a]
        change fromF (if h : a = x then 1 else FreeGroup.of a) =
          HNNExtension.of (PresentedGroup.of a : P)
        rw [dif_neg ha, fromF_of, dif_neg ha]
    · rw [MonoidHom.comp_apply, MonoidHom.id_apply, toF_t, fromF_of, dif_pos rfl]
  exact ⟨MonoidHom.toMulEquiv toF fromF h2 h1⟩

end Work.OROneRel
