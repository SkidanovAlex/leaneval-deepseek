import Mathlib
import Submission.Work.ThomBordism.TwoSet.exists_cellHomeo
import Submission.Work.RatHurewicz.Triad.Helpers

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The compression of a pair at a cell

`Triad/Helpers.lean` proves `compressRelBd_congr`: the compression property of a pair transports to
any space homeomorphic to `I^d`, with the boundary transported along the homeomorphism. This file
applies it to a grid cell, using `exists_cellHomeo`: the compression of `(↥B, ↥(B ∩ C))` at level
`d` (with the boundary values restricted to `B ∩ C ∩ pathComponent x₀`) gives, for any map on the
cell whose relative boundary values lie in that set, a homotopy relative to `cellRelbd c` into the
`B ∩ C`-valued maps.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

open Work.ThomBordism.TwoSet

theorem cellCompression {X : Type} [TopologicalSpace X] {B C : Set X} (x₀ : ↥(B ∩ C)) (p : ℕ)
    (hBc : ∀ d, 1 ≤ d → d ≤ p + 1 → CompressRelBd
      {y : ↥B | (y : X) ∈ B ∩ C}
      {y : ↥B | (y : X) ∈ B ∩ C ∧ (y : X) ∈ pathComponent (x₀ : X)} d)
    {j N : ℕ} (hN : 1 ≤ N) (c : CellIdx j N)
    (hd : 1 ≤ cellDim c) (hle : cellDim c ≤ p + 1)
    (f : C(cellSet c, ↥B))
    (hf : ∀ u : cellSet c, (u : IC j) ∈ cellRelbd c →
      ((f u : X) ∈ B ∩ C ∧ (f u : X) ∈ pathComponent (x₀ : X))) :
    ∃ H : C(cellSet c × I, ↥B),
      (∀ u, H (u, 0) = f u) ∧
      (∀ (u : cellSet c) (hu : (u : IC j) ∈ cellRelbd c) (t : I), H (u, t) = f u) ∧
      (∀ u, ((H (u, 1) : ↥B) : X) ∈ B ∩ C) := by
  obtain ⟨e, he⟩ := exists_cellHomeo (j := j) (N := N) hN c
  obtain ⟨G, hG0, hGbd, hG1⟩ :=
    Triad.compressRelBd_congr (hBc (cellDim c) hd hle) e
      {z : cellSet c | (z : IC j) ∈ cellRelbd c} he f (fun x hx => hf x hx)
  exact ⟨G, hG0, hGbd, hG1⟩

/-- **The `C`-dual of `cellCompression`**: the compression of `(↥C, ↥(B ∩ C))` at a cell, from the
hypothesis `hCc` on the pair `(C, B ∩ C)`. -/
theorem cellCompressionRight {X : Type} [TopologicalSpace X] {B C : Set X} (x₀ : ↥(B ∩ C)) (q : ℕ)
    (hCc : ∀ d, 1 ≤ d → d ≤ q + 1 → CompressRelBd
      {y : ↥C | (y : X) ∈ B ∩ C}
      {y : ↥C | (y : X) ∈ B ∩ C ∧ (y : X) ∈ pathComponent (x₀ : X)} d)
    {j N : ℕ} (hN : 1 ≤ N) (c : CellIdx j N)
    (hd : 1 ≤ cellDim c) (hle : cellDim c ≤ q + 1)
    (f : C(cellSet c, ↥C))
    (hf : ∀ u : cellSet c, (u : IC j) ∈ cellRelbd c →
      ((f u : X) ∈ B ∩ C ∧ (f u : X) ∈ pathComponent (x₀ : X))) :
    ∃ H : C(cellSet c × I, ↥C),
      (∀ u, H (u, 0) = f u) ∧
      (∀ (u : cellSet c) (hu : (u : IC j) ∈ cellRelbd c) (t : I), H (u, t) = f u) ∧
      (∀ u, ((H (u, 1) : ↥C) : X) ∈ B ∩ C) := by
  obtain ⟨e, he⟩ := exists_cellHomeo (j := j) (N := N) hN c
  obtain ⟨G, hG0, hGbd, hG1⟩ :=
    Triad.compressRelBd_congr (hCc (cellDim c) hd hle) e
      {z : cellSet c | (z : IC j) ∈ cellRelbd c} he f (fun x hx => hf x hx)
  exact ⟨G, hG0, hGbd, hG1⟩

end

end Work.RatHurewicz
