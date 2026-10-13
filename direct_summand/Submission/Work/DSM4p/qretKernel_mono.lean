import Mathlib
import Submission.Work.DSM4p.Basic
import Submission.Work.DSM4p.iterTr_add_apply

namespace Work.DSM4p

universe a
theorem qretKernel_mono {p : ℕ} {B : Type a} [CommRing B] (ϖ gr : ℕ → B) {D : ℕ → Type a}
    [∀ n, CommRing (D n)] [∀ n, Algebra B (D n)] (tr : ∀ n, D (n + 1) →ₐ[B] D n) {m k c c' : ℕ}
    (hcc : c ≤ c')
    (h : ∀ n (x : B), algebraMap B (D (n + c)) x ∈ Ideal.span {((p : D (n + c))) ^ m} →
        ϖ k * gr k * x ∈ Ideal.span {((p : B)) ^ m}) :
    ∀ n (x : B), algebraMap B (D (n + c')) x ∈ Ideal.span {((p : D (n + c'))) ^ m} →
        ϖ k * gr k * x ∈ Ideal.span {((p : B)) ^ m} := by
  intro n x hx
  -- The hypothesis at level `n + (c' - c)` is exactly the goal at level `n`, since
  -- `(n + (c' - c)) + c = n + (c + (c' - c)) = n + c'`.
  have hidx : (n + (c' - c)) + c = n + c' := by omega
  exact h (n + (c' - c)) x (by rw [hidx]; exact hx)

end Work.DSM4p
