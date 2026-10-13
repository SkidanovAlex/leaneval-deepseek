/-
  WilE7 (`Submission.Work.WilE7.FaceAux.botY1_component`): the connected component of the cut
  set `botY1 Z = {u | takeZ u ∈ Z.set ∧ u (botIdx) = -1}` through the pinned point
  `botPinPt u₀` is exactly the pinned copy of the component of `Z.set` through `u₀`.

  The mathematics is that the cut set is a *graph over* the base set: every `u ∈ (botY1 Z).set`
  is `botPinPt (takeZ u)` (`botPinPt_takeZ`), and conversely `botPinPt` maps `Z.set` into
  `(botY1 Z).set` (`botPinPt_mem`).  So `(botY1 Z).set = botPinPt '' Z.set`, and `takeZ` — a
  global continuous retraction of `botPinPt` (`takeZ_botPinPt`) — witnesses that `botPinPt` is a
  homeomorphism onto its image.  Connected components are therefore transported:

  `image_connectedComponentIn_eq_of_retraction` (proved here) says that if `f` has a continuous
  left inverse `g` (`g ∘ f = id`), then `f` carries the component of `x` in `s` onto the
  component of `f x` in `f '' s`.  Applying it to `f = botPinPt`, `g = takeZ`, `s = Z.set`
  gives the claim, after rewriting `botPinPt '' Z.set` to `(botY1 Z).set`
  (`botPinPt_image_set`, proved here).

  Both inputs are independent of each other; the two nontrivial ones are the general topology
  lemma and the set identity, and the assembly is three lines.
-/
import Mathlib
import Submission.Work.WilE7.FaceAux.BotDefs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.FaceAux
open WilkiesDesign WilkiesDesign.E

/-! ## §1. The general topology input: components under a retraction -/

/-- If `f : α → β` is continuous with a *continuous* left inverse `g` (`∀ x, g (f x) = x`), then
`f` carries the connected component of `x` in `s` onto the connected component of `f x` in
`f '' s`.

This is the general form of “a semi-Pfaffian cut set presented as the image of the base set under
the pinning map has the components one expects”. -/
theorem image_connectedComponentIn_eq_of_retraction {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {f : α → β} {g : β → α} (hf : Continuous f) (hg : Continuous g)
    (hgf : ∀ x, g (f x) = x) (s : Set α) {x : α} (hx : x ∈ s) :
    f '' connectedComponentIn s x = connectedComponentIn (f '' s) (f x) := by
  apply Set.Subset.antisymm
  · -- the image of a preconnected set is preconnected and lies in `f '' s`
    exact ContinuousOn.image_connectedComponentIn_subset hf.continuousOn hx
  · intro y hy
    -- `y` has a preimage `x'` in `s`, and `f x' = y`
    obtain ⟨x', hx', hyx'⟩ := connectedComponentIn_subset (f '' s) (f x) hy
    -- `g` carries the component of `f x` into the component of `x`: it is continuous, the image
    -- is preconnected, contains `g (f x) = x`, and `f '' s` retracts into `s` under `g`
    have hpre : IsPreconnected (g '' connectedComponentIn (f '' s) (f x)) :=
      isPreconnected_connectedComponentIn.image g hg.continuousOn
    have hmem : x ∈ g '' connectedComponentIn (f '' s) (f x) :=
      ⟨f x, mem_connectedComponentIn ⟨x, hx, rfl⟩, hgf x⟩
    have hsub : g '' connectedComponentIn (f '' s) (f x) ⊆ s := by
      rintro w ⟨z, hz, rfl⟩
      obtain ⟨w', hw', hzw'⟩ := connectedComponentIn_subset (f '' s) (f x) hz
      rw [← hzw', hgf w']
      exact hw'
    have hgy : g y ∈ connectedComponentIn s x :=
      (hpre.subset_connectedComponentIn (F := s) hmem hsub) ⟨y, hy, rfl⟩
    -- and `f (g y) = f x' = y`
    refine ⟨x', ?_, hyx'⟩
    rw [← hgf x', hyx']
    exact hgy

/-! ## §2. The cut set as the pinned image of the base set -/

/-- **The point set of `botY1` is the pinned copy of `Z.set`.**  Both inclusions come from the
two halves of `mem_botY1` plus `takeZ`/`botPinPt` being inverse to each other on the relevant
sets. -/
theorem botPinPt_image_set {p m : ℕ} (Z : WilkiesDesign.E.SemiPf (p + (m + 1))) :
    botPinPt '' Z.set = (botY1 Z).set := by
  apply Set.Subset.antisymm
  · rintro u ⟨x, hx, rfl⟩
    exact botPinPt_mem Z hx
  · intro u hu
    -- `u` is the pinning of its own truncation, which lies in `Z.set`
    exact ⟨Work.WilE7.takeZ (botN_le_botK p m) u, takeZ_mem_of_mem_botY1 Z hu,
      botPinPt_takeZ Z hu⟩

/-! ## §3. The requested lemma -/

theorem botY1_component {p m : ℕ} (Z : WilkiesDesign.E.SemiPf (p + (m + 1)))
    (u₀ : Fin (p + (m + 1)) → ℝ) (hu₀ : u₀ ∈ Z.set) :
    connectedComponentIn (Work.WilE7.FaceAux.botY1 Z).set
        (Work.WilE7.FaceAux.botPinPt u₀)
      = Work.WilE7.FaceAux.botPinPt '' connectedComponentIn Z.set u₀ := by
  rw [← botPinPt_image_set Z, eq_comm]
  exact image_connectedComponentIn_eq_of_retraction (f := botPinPt)
    (g := fun y => Work.WilE7.takeZ (botN_le_botK p m) y)
    (continuous_botPinPt p m) (Work.WilE7.continuous_takeZ (botN_le_botK p m))
    (fun x => takeZ_botPinPt x) Z.set hu₀

end Work.WilE7.FaceAux
