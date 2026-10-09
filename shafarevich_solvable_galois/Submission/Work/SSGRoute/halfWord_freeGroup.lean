import Mathlib
import Submission.Work.SSGRoute.freeOperatorGroup_no_fixed_points
import Submission.Work.SSGRoute.split_sigmaPalindrome
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The half-word lemma for a free group with an involution of its basis

`Work.SSGRoute.halfWord_freeGroup`: if `σ : X ≃ X` is an involution with no fixed points, `F = FreeGroup X`
and `Φ = FreeGroup.freeGroupCongr σ`, then every `Φ`-anti-invariant element `w` (i.e. `Φ w = w⁻¹`) is of
the form `w = (Φ v)⁻¹ * v`.

The proof works on the reduced normal form `L = w.toWord`.
* `toWord (freeGroupCongr σ w) = L.map (fun p => (σ p.1, p.2))` and `toWord (w⁻¹) = FreeGroup.invRev L`,
  so `Φ w = w⁻¹` says `L.map (fun p => (σ p.1, p.2)) = FreeGroup.invRev L`.
* Mapping by `fun p => (p.1, !p.2)` and using `FreeGroup.invRev L = (L.map (fun p => (p.1, !p.2))).reverse`
  turns this into the `σ`-palindrome `L.map (fun p => (σ p.1, !p.2)) = L.reverse`.
* `split_sigmaPalindrome` splits such an `L = L₁ ++ L₂` with `FreeGroup.invRev (L₂.map σ) = L₁`.

Then `v := FreeGroup.mk L₂` satisfies `(Φ v)⁻¹ * v = FreeGroup.mk (FreeGroup.invRev (L₂.map σ)) * FreeGroup.mk L₂
= FreeGroup.mk (L₁ ++ L₂) = FreeGroup.mk L = w`.
-/

namespace Work.SSGRoute

open FreeGroup

theorem halfWord_freeGroup {X : Type*} (σ : X ≃ X) (hσ : ∀ x, σ (σ x) = x)
    (hfree : ∀ x, σ x ≠ x) :
    ∀ w : FreeGroup X, FreeGroup.freeGroupCongr σ w = w⁻¹ →
      ∃ v : FreeGroup X, w = (FreeGroup.freeGroupCongr σ v)⁻¹ * v := by
  classical
  intro w hw
  set L : List (X × Bool) := w.toWord with hLdef
  -- `Φ w = w⁻¹` as an identity of reduced words
  have hL1 : L.map (fun p => (σ p.1, p.2)) = FreeGroup.invRev L := by
    have h1 := toWord_freeGroupCongr σ w
    rw [hw, FreeGroup.toWord_inv] at h1
    rw [hLdef]
    exact h1.symm
  -- the `σ`-palindrome
  have hpal : L.map (fun p => (σ p.1, !p.2)) = L.reverse := by
    have hid : (fun x : X × Bool => (x.1, x.2)) = id := by funext x; exact Prod.mk.eta
    have h2 := congrArg (List.map (fun p : X × Bool => (p.1, !p.2))) hL1
    simp only [List.map_map, FreeGroup.invRev, List.map_reverse, Function.comp_def,
      Bool.not_not] at h2
    rw [hid, List.map_id] at h2
    exact h2
  obtain ⟨L₁, L₂, hL, hsp⟩ := split_sigmaPalindrome σ hσ L hpal
  refine ⟨FreeGroup.mk L₂, ?_⟩
  have hmk : FreeGroup.mk L = w := by rw [hLdef]; exact FreeGroup.mk_toWord
  have hc : FreeGroup.freeGroupCongr σ (FreeGroup.mk L₂)
      = FreeGroup.mk (L₂.map (fun p => (σ p.1, p.2))) := rfl
  calc w = FreeGroup.mk L := hmk.symm
    _ = FreeGroup.mk (L₁ ++ L₂) := by rw [hL]
    _ = FreeGroup.mk L₁ * FreeGroup.mk L₂ := by rw [FreeGroup.mul_mk]
    _ = FreeGroup.mk (FreeGroup.invRev (L₂.map (fun p => (σ p.1, p.2)))) * FreeGroup.mk L₂ := by
          rw [hsp]
    _ = (FreeGroup.mk (L₂.map (fun p => (σ p.1, p.2))))⁻¹ * FreeGroup.mk L₂ := by
          rw [FreeGroup.inv_mk]
    _ = (FreeGroup.freeGroupCongr σ (FreeGroup.mk L₂))⁻¹ * FreeGroup.mk L₂ := by rw [hc]

end Work.SSGRoute
