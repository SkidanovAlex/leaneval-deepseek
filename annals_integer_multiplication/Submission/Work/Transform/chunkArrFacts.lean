import Mathlib
import Submission.Work.Transform.phiChunkDefs
import Submission.Work.Transform.phiAux

namespace Work.Transform

theorem chunkArrFacts {p M r : ℕ} {x : List (ℤ × ℤ)} (hx : x.length = M * r)
    (hix : HvdH.InDiscVec p (M * r) x) (hp : 100 ≤ p) (hr : 2 ≤ r) :
    HvdH.InDiscArr p M r (Work.Transform.chunkArr M r x) ∧
    HvdH.vsz (HvdH.rarrVal (Work.Transform.chunkArr M r x)) ≤ 400 * (M * r * p ^ 2 + 1) ∧
    (∀ i < M, ((Work.Transform.chunkArr M r x).getD i []).length = r) ∧
    (∀ i < M, ∀ c < r, ((Work.Transform.chunkArr M r x).getD i []).getD c (0, 0) =
      x.getD (i * r + c) (0, 0)) := by
  have hlen : (chunkArr M r x).length = M := chunkArr_length M r x
  have hlen2 : ∀ i < M, ((chunkArr M r x).getD i []).length = r := by
    intro i hi
    rw [chunkArr_getD hi, List.length_take, List.length_drop]
    have hlt : i * r + r ≤ x.length := by
      rw [hx]
      have h1 : i + 1 ≤ M := by omega
      calc i * r + r = (i + 1) * r := by ring
        _ ≤ M * r := Nat.mul_le_mul_right r h1
    omega
  have hidx : ∀ i < M, ∀ c < r, ((chunkArr M r x).getD i []).getD c (0, 0)
      = x.getD (i * r + c) (0, 0) := by
    intro i hi c hc
    rw [chunkArr_getD hi]
    exact getD_drop_take x (i * r) r c (0, 0) hc
  have hIA : HvdH.InDiscArr p M r (chunkArr M r x) :=
    inDiscArr_of_chunks hix hlen hlen2 hidx
  exact ⟨hIA, vsz_rarrVal_le hIA hp hr, hlen2, hidx⟩

end Work.Transform
