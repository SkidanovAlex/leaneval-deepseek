import Mathlib
import Submission.Work.RatHurewicz.excisionDefs
import Submission.Work.Stems.Cubical.CubeFace
import Submission.Work.RatHurewicz.CubeFaceAux

/-!
# The vocabulary of the triad-compression argument (Puppe's preparation theorem)

This file fixes the notation used by the proof of `Work.RatHurewicz.triadCompression`
(tom Dieck, *Algebraic Topology*, §6.9, the proof of the excision theorem by Puppe).

The setting is a triad `(X; B, C)`: `B, C ⊆ X` open with `B ∪ C = X`, and a base point
`x₀ ∈ B ∩ C`.  A map `Φ : I^{n+1} → X` (with the *last* coordinate playing the role of the
"time" of a path in the based path space) is called **admissible** when it starts at `x₀`,
ends in `C`, and takes values in `B` on the "wall" `∂Iⁿ × I`.

The preparation theorem deforms `Φ`, through admissible maps, into a map `Ψ` which, on each
small cell of a uniform grid of mesh `1/N`, satisfies the "`K`/`G`" conditions of tom Dieck's
Lemma 6.9.1: the preimage of `B ∖ C` lies in the region where many coordinates are in the
*lower* half of their grid interval, and the preimage of `C ∖ B` where many are in the *upper*
half.  `IsSmall`/`IsLarge` below are those two half-conditions, stated pointwise.

The pointwise formulation is what the dimension count (6.9.3) uses: for two points `z, z'` of
`I^{n+1}` with the same projection to `Iⁿ`, a coordinate `i ≤ n` with `IsSmall N z i` and
`IsLarge N z' i` is impossible, because `z i = z' i` and the two conditions are complementary.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz.Triad

open Work.Stems.Cubical

noncomputable section

/-- **The `i`-th coordinate of `z` lies in the lower half of its grid interval of the uniform
`N`-grid**, and is not a grid node: writing `N zᵢ = m + f` with `m = ⌊N zᵢ⌋` and `0 ≤ f < 1`, this
says `0 < f < 1/2`.  (Equivalently, `zᵢ` is not a node and `zᵢ < (⌊N zᵢ⌋ + 1/2)/N`.) -/
def IsSmall (N : ℕ) {m : ℕ} (z : ICube m) (i : Fin m) : Prop :=
  (N : ℝ) * (z i : ℝ) ≠ (⌊(N : ℝ) * (z i : ℝ)⌋₊ : ℝ) ∧
    (N : ℝ) * (z i : ℝ) < (⌊(N : ℝ) * (z i : ℝ)⌋₊ : ℝ) + 1 / 2

/-- **The `i`-th coordinate of `z` lies in the upper half of its grid interval** of the uniform
`N`-grid: with `m = ⌊N zᵢ⌋` this says `N zᵢ > m + 1/2`. -/
def IsLarge (N : ℕ) {m : ℕ} (z : ICube m) (i : Fin m) : Prop :=
  (⌊(N : ℝ) * (z i : ℝ)⌋₊ : ℝ) + 1 / 2 < (N : ℝ) * (z i : ℝ)

/-- The two half-conditions are mutually exclusive: a coordinate cannot lie in both halves of
its grid interval. -/
theorem not_isSmall_of_isLarge {N m : ℕ} {z : ICube m} {i : Fin m}
    (h : IsLarge N z i) : ¬ IsSmall N z i := by
  rintro ⟨-, hs⟩
  have hl := h
  unfold IsLarge at hl
  linarith

theorem not_isLarge_of_isSmall {N m : ℕ} {z : ICube m} {i : Fin m}
    (h : IsSmall N z i) : ¬ IsLarge N z i := by
  intro hl
  exact not_isSmall_of_isLarge hl h

/-- **Admissibility** of `Φ : I^{n+1} → X` for the triad `(X; B, C)` with base point `x₀`: the map
takes the initial face to `x₀`, the final face into `C`, and the "wall" `∂Iⁿ × I` into `B`.

With the last coordinate of `I^{n+1}` read as the parameter of a path in the path space based at
`x₀`, these are exactly tom Dieck's conditions (1)–(3) for the proof of (6.9.3). -/
def TriadAdmissible {X : Type} [TopologicalSpace X] (B C : Set X) (x₀ : ↥(B ∩ C)) {n : ℕ}
    (Φ : C(ICube (n + 1), X)) : Prop :=
  (∀ x : ICube n, Φ (Fin.snoc x 0) = (x₀ : X)) ∧
  (∀ x : ICube n, Φ (Fin.snoc x 1) ∈ C) ∧
  (∀ x : ICube n, x ∈ Cube.boundary (Fin n) → ∀ t : unitInterval, Φ (Fin.snoc x t) ∈ B)

/-- The "wall" of `I^{n+1} = Iⁿ × I`: the points whose space part lies on the boundary of `Iⁿ`. -/
def wall (n : ℕ) : Set (ICube (n + 1)) :=
  {z | initC n z ∈ Cube.boundary (Fin n)}

/-- `Fin.castSucc` is injective, in the form used by the dimension count. -/
theorem castSucc_injective {n : ℕ} : Function.Injective (Fin.castSucc : Fin n → Fin (n + 1)) :=
  fun _ _ h => Fin.castSucc_injective _ h

end

end Work.RatHurewicz.Triad
