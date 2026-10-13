import Mathlib
import Submission.Work.DSM4p.Basic
import Submission.Work.DSM4p.iterTr_add_apply

namespace Work.DSM4p

universe a
theorem qretCoker_mono {p : ℕ} {B : Type a} [CommRing B] (ϖ gr : ℕ → B) {D : ℕ → Type a}
    [∀ n, CommRing (D n)] [∀ n, Algebra B (D n)] (tr : ∀ n, D (n + 1) →ₐ[B] D n) {m k c c' : ℕ}
    (hcc : c ≤ c')
    (h : ∀ n (y : D (n + c)), ∃ x : B, algebraMap B (D n) (ϖ k * gr k) * DSMap.Mix.iterTr tr n c y -
        algebraMap B (D n) x ∈ Ideal.span {((p : D n)) ^ m}) :
    ∀ n (y : D (n + c')), ∃ x : B, algebraMap B (D n) (ϖ k * gr k) * DSMap.Mix.iterTr tr n c' y -
        algebraMap B (D n) x ∈ Ideal.span {((p : D n)) ^ m} := by
  -- The cokernel clause of the QRET condition is monotone in the tower level: the image of
  -- `iterTr tr n c' = iterTr tr n c ∘ iterTr tr (n+c) (c'-c)` is contained in the image of
  -- `iterTr tr n c`, so any `B`-element satisfying the latter works for the former.
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hcc
  clear hcc
  induction d with
  | zero => intro n y; exact h n y
  | succ d ih =>
      intro n y
      obtain ⟨x, hx⟩ := ih n (tr (n + (c + d)) y)
      exact ⟨x, hx⟩

end Work.DSM4p
