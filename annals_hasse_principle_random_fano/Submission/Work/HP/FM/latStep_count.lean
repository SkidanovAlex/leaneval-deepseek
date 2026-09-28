import Mathlib
import Submission.Work.HP.FM.latStepAux
import Submission.Work.HP.LatRecurse.ncard_fiber_le

/-!
# The one-step lattice-point count of the Schmidt recursion

Peeling off a shortest vector `D.p = D.Φ u` of the lattice presented by `D.Φ` and projecting
onto `D.p^⊥` gives the projected presentation `D.step`.  The projection maps the lattice
points of `D.Φ` of norm `≤ T` onto the lattice points of `D.step` of norm `≤ T`
(`RecData.coords_snd_mem_latSet_step`), and every fibre consists of the integers `a` in an
interval of length `2T/‖D.p‖`, hence has at most `⌊2T/‖D.p‖⌋ + 1` elements
(`fiber_ncard_le`).  Counting the total space of this map by its fibres gives

  `#{x : ‖Φ x‖ ≤ T} ≤ (2T/‖p‖ + 1) · #{t : ‖step t‖ ≤ T}`.

The only place where the specific combinatorics of `D` enters is the `ℤ`-basis decomposition
`x = a • u + ∑ i, (t x) i • v i` of `RecDefs`, together with the real independence of the
realifications of `u` and the `v i` (used to see that `D.step` is injective, so that
`latSet D.step T` is finite).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Finset
open scoped BigOperators

namespace Work.HP.FM

theorem latStep_count {ι : Type*} [Fintype ι] [DecidableEq ι] {R : ℕ} (D : Work.HP.FM.RecData R ι) {T : ℝ} (hT : 0 ≤ T) :
    (Work.HP.latCount D.Φ T : ℝ) ≤ (2 * T / ‖D.p‖ + 1) * (Work.HP.latCount D.step T : ℝ) := by
  classical
  set K : ℕ := Nat.floor (2 * (T / ‖D.p‖)) + 1 with hKdef
  set S' : Set (ℤ × (Fin (R - 1) → ℤ)) := D.coords '' (Work.HP.latSet D.Φ T) with hS'def
  -- every vertical fibre has at most `K` elements
  have hfiber : ∀ t : Fin (R - 1) → ℤ, {a : ℤ | (a, t) ∈ S'}.ncard ≤ K := by
    intro t
    have hset : {a : ℤ | (a, t) ∈ S'}
        = {a : ℤ | D.decompFun (a, t) ∈ Work.HP.latSet D.Φ T} := by
      ext a
      simp only [Set.mem_ofPred_eq, hS'def]
      exact D.mem_coords_image (Work.HP.latSet D.Φ T) a t
    rw [hset]
    exact fiber_ncard_le D hT t
  have h1 : S'.ncard ≤ K * (S'.image Prod.snd).ncard :=
    Work.HP.LatRecurse.ncard_fiber_le S' K hfiber
  -- the projection of `S'` lies in `latSet D.step T`
  have hsub : S'.image Prod.snd ⊆ Work.HP.latSet D.step T := by
    rintro t ⟨p, hp, rfl⟩
    rw [hS'def] at hp
    obtain ⟨x, hx, rfl⟩ := hp
    exact D.coords_snd_mem_latSet_step hx
  have h2 : (S'.image Prod.snd).ncard ≤ (Work.HP.latSet D.step T).ncard :=
    Set.ncard_le_ncard hsub (D.step_latSet_finite T)
  have hSncard : S'.ncard = (Work.HP.latSet D.Φ T).ncard := by
    rw [hS'def]
    exact Set.ncard_image_of_injective _ D.coords_injective
  have hKle : (K : ℝ) ≤ 2 * T / ‖D.p‖ + 1 := by
    have hM : 0 ≤ 2 * (T / ‖D.p‖) := by positivity
    have h := Nat.floor_le hM
    have h2 : 2 * (T / ‖D.p‖) = 2 * T / ‖D.p‖ := by ring
    rw [hKdef]
    push_cast
    linarith [h, h2]
  calc (Work.HP.latCount D.Φ T : ℝ)
      = (S'.ncard : ℝ) := by rw [Work.HP.latCount, ← hSncard]
    _ ≤ (K * (S'.image Prod.snd).ncard : ℝ) := by exact_mod_cast h1
    _ = (K : ℝ) * ((S'.image Prod.snd).ncard : ℝ) := by push_cast; ring
    _ ≤ (K : ℝ) * (Work.HP.latCount D.step T : ℝ) := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg K)
        rw [Work.HP.latCount]
        exact_mod_cast h2
    _ ≤ (2 * T / ‖D.p‖ + 1) * (Work.HP.latCount D.step T : ℝ) :=
        mul_le_mul_of_nonneg_right hKle (Nat.cast_nonneg _)

end Work.HP.FM
