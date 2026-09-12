import Mathlib
import Submission.XTransfer
import Submission.Phases

/-!
# Spike-direction set of the conjugate hedgehog

The hedgehog `star S` is the union of the segments `[0, z²]`, `[0, z⁴]`
(`z ∈ S`).  Its *spike endpoints* are the numbers `z², z⁴` and its
*directions* are their arguments (an angle in `(-π, π]`):

    spikeEndpoints S := {z², z⁴ : z ∈ S}            (a Finset ℂ)
    dirSet S         := {arg c : c ∈ spikeEndpoints S}   (a Finset ℝ)

`card_arg_sq_union_pow4_le` (Submission.Phases) bounds the number of
directions by `2 · |argSet|`, so `dirSet_card_le_two_argSet`.

For the E2b angular-gap decomposition one needs: *between two consecutive
directions no further direction occurs*.  Rather than sorting, this module
uses the **successor** formulation: if `φ` is a direction and `ψ` is the least
direction strictly above `φ`, then every direction is `≤ φ` or `≥ ψ` — there
is nothing strictly between them; hence any cell whose angular range
`[c, d]` satisfies `φ < c ∧ d < ψ` meets no direction, giving the
`hno` hypothesis of the per-cell Cauchy identity
(`Submission.PolyaShell.sector_cell_boundary_integral_eq_zero`).
-/

noncomputable section

open scoped Complex Real
open Complex

namespace Submission.DirSet

open Submission.XTransfer

/-- The spike endpoints of the hedgehog over `S`: `{z², z⁴ : z ∈ S}`. -/
def spikeEndpoints (S : Finset ℂ) : Finset ℂ :=
  (S.image fun z : ℂ => z ^ 2) ∪ (S.image fun z : ℂ => z ^ 4)

/-- The spike directions of the hedgehog over `S`: the arguments of its spike
endpoints, as a finite set of real angles in `(-π, π]`. -/
def dirSet (S : Finset ℂ) : Finset ℝ := (spikeEndpoints S).image Complex.arg

/-- The directions of the hedgehog are the arguments of the `z²` and `z⁴`
endpoints. -/
lemma mem_dirSet_iff (S : Finset ℂ) (θ : ℝ) :
    θ ∈ dirSet S ↔ ∃ z ∈ S, Complex.arg (z ^ 2) = θ ∨ Complex.arg (z ^ 4) = θ := by
  classical
  rw [dirSet, Finset.mem_image]
  constructor
  · rintro ⟨c, hc, hθ⟩
    rw [spikeEndpoints, Finset.mem_union] at hc
    rcases hc with hc | hc
    · rcases (Finset.mem_image.mp hc) with ⟨z, hz, rfl⟩
      exact ⟨z, hz, Or.inl hθ⟩
    · rcases (Finset.mem_image.mp hc) with ⟨z, hz, rfl⟩
      exact ⟨z, hz, Or.inr hθ⟩
  · rintro ⟨z, hz, hzθ⟩
    rcases hzθ with hzθ | hzθ
    · refine ⟨z ^ 2, ?_, hzθ⟩
      rw [spikeEndpoints, Finset.mem_union]
      exact Or.inl (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
    · refine ⟨z ^ 4, ?_, hzθ⟩
      rw [spikeEndpoints, Finset.mem_union]
      exact Or.inr (Finset.mem_image.mpr ⟨z, hz, rfl⟩)

/-- `arg (z²)` and `arg (z⁴)` (for `z ∈ S`) are directions. -/
lemma arg_sq_mem_dirSet {S : Finset ℂ} {z : ℂ} (hz : z ∈ S) :
    Complex.arg (z ^ 2) ∈ dirSet S := by
  classical
  exact (mem_dirSet_iff S (Complex.arg (z ^ 2))).mpr ⟨z, hz, Or.inl rfl⟩

lemma arg_pow4_mem_dirSet {S : Finset ℂ} {z : ℂ} (hz : z ∈ S) :
    Complex.arg (z ^ 4) ∈ dirSet S := by
  classical
  exact (mem_dirSet_iff S (Complex.arg (z ^ 4))).mpr ⟨z, hz, Or.inr rfl⟩

/-- The hedgehog over the conjugates has at most twice as many directions as
the conjugates have phases (`Submission.Phases.card_arg_sq_union_pow4_le`). -/
lemma dirSet_card_le_two_phases (S : Finset ℂ) :
    (dirSet S).card ≤ 2 * (S.image Complex.arg).card := by
  classical
  simpa [dirSet, spikeEndpoints] using
    (Submission.Phases.card_arg_sq_union_pow4_le S)

/-- **Bridge to the per-cell Cauchy identity.**  If no direction lies in the
closed angular range `[c, d]`, then no spike endpoint points into it, i.e.
the `hno` hypothesis of
`Submission.PolyaShell.sector_cell_boundary_integral_eq_zero` holds. -/
lemma endpoints_no_arg_of_dirSet_free {S : Finset ℂ} {c d : ℝ}
    (h : ∀ θ ∈ dirSet S, θ ∉ Set.Icc c d) :
    ∀ z ∈ S,
      Complex.arg (z ^ 2) ∉ Set.Icc c d ∧ Complex.arg (z ^ 4) ∉ Set.Icc c d := by
  intro z hz
  exact ⟨h (Complex.arg (z ^ 2)) (arg_sq_mem_dirSet hz),
    h (Complex.arg (z ^ 4)) (arg_pow4_mem_dirSet hz)⟩

/-! ## Successor formulation of the gaps

Let `D` be a finite set of directions.  If `ψ` is the *least* direction
strictly above `φ ∈ D`, then no direction lies strictly between `φ` and `ψ`
(and, a fortiori, none lies in any closed interval `[c, d]` with
`φ < c` and `d < ψ`). -/

/-- **Successor gap.**  If `ψ` is a direction above `φ` that is minimal among
the directions strictly above `φ`, then every direction is `≤ φ` or `≥ ψ`
(nothing strictly between them). -/
lemma dir_le_or_succ {D : Finset ℝ} {φ ψ : ℝ}
    (hψmin : ∀ θ ∈ D.filter (fun θ => φ < θ), ψ ≤ θ) :
    ∀ θ ∈ D, θ ≤ φ ∨ ψ ≤ θ := by
  intro θ hθ
  by_cases hφθ : θ ≤ φ
  · exact Or.inl hφθ
  · right
    have hφθ' : φ < θ := lt_of_not_ge hφθ
    exact hψmin θ (by simpa [Finset.mem_filter] using ⟨hθ, hφθ'⟩)

/-- A cell whose closed angular range lies strictly between `φ` and its
successor `ψ` meets no direction of `D`. -/
lemma dirSet_free_Icc_of_succ {D : Finset ℝ} {φ ψ : ℝ}
    (hψmin : ∀ θ ∈ D.filter (fun θ => φ < θ), ψ ≤ θ) {c d : ℝ}
    (hφc : φ < c) (hdψ : d < ψ) :
    ∀ θ ∈ D, θ ∉ Set.Icc c d := by
  intro θ hθ hcd
  rcases dir_le_or_succ (D := D) hψmin θ hθ with hle | hge
  · have hθc : θ < c := lt_of_le_of_lt hle hφc
    exact (not_lt_of_ge hcd.1) hθc
  · have hdθ : d < θ := lt_of_lt_of_le hdψ hge
    exact (not_lt_of_ge hcd.2) hdθ

/-- **Concrete successor by minimum.**  If `φ` is a direction of the hedgehog
and there is a direction strictly above it, let `ψ` be the least such
direction (`min'`).  Then any closed angular range strictly inside the gap
`(φ, ψ)` meets no direction of the hedgehog. -/
lemma dirSet_free_Icc_of_min_above (S : Finset ℂ) {φ : ℝ}
    (hne : ((dirSet S).filter (fun θ => φ < θ)).Nonempty) {c d : ℝ}
    (hφc : φ < c) (hdψ : d < ((dirSet S).filter (fun θ => φ < θ)).min' hne) :
    ∀ θ ∈ dirSet S, θ ∉ Set.Icc c d := by
  classical
  let ψ : ℝ := ((dirSet S).filter (fun θ => φ < θ)).min' hne
  apply dirSet_free_Icc_of_succ (D := dirSet S) (φ := φ) (ψ := ψ) ?_ hφc hdψ
  intro θ hθ
  dsimp [ψ]
  exact Finset.min'_le (((dirSet S).filter (fun θ => φ < θ))) θ hθ


end Submission.DirSet

end
