import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.GalBasis.FamEAux.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real ContDiff

namespace Work.FTS.GalBasis.GalApprox

set_option maxHeartbeats 1000000

/-! ## Iterated plain derivatives lose exactly as many orders as derivatives are taken

`Work.FTS.GalBasis.contDiffOn_uncurry_pzIter_le` / `..._pthIter_le` prove that the `i`-th
plain partial derivative of a `C^N` function is `C^{N-i}`, but only under the *strict*
hypothesis `i < N`.  The boundary case `i = N` (where the conclusion is merely `C^0`, i.e.
continuity) is needed here, because the target statement allows `k = 0` with `i + j = n`.
The two lemmas below are the versions with `i ≤ N`; the proofs are those of the existing
lemmas, with the strict inequality relaxed (in the induction step one always has
`N - n ≥ 1`, which is all the existing machinery needs). -/

/-- The `i`-th plain `z`-partial of a `C^N` function is `C^{N-i}`, including the boundary
case `i = N`. -/
theorem contDiffOn_uncurry_pzIter_le_self {X : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) :
    ∀ (i N : ℕ), i ≤ N → ContDiffOn ℝ (N : ℕ∞ω) (Function.uncurry X) V →
      ContDiffOn ℝ ((N - i : ℕ) : ℕ∞ω) (Function.uncurry (Work.Spaces.pzIter i X)) V := by
  intro i
  induction i with
  | zero => intro N _ h; simpa using h
  | succ n ih =>
      intro N hN h
      have h1 : ContDiffOn ℝ ((N - n : ℕ) : ℕ∞ω)
          (Function.uncurry (Work.Spaces.pzIter n X)) V :=
        ih N (by omega) h
      have h2 : ContDiffOn ℝ (((N - n) - 1 : ℕ) : ℕ∞ω)
          (Function.uncurry (Work.Spaces.pz (Work.Spaces.pzIter n X))) V :=
        Work.FTS.GalBasis.famAux_contDiffOn_uncurry_pz_le hV (N - n - 1) (by
          rw [show (N - n - 1 + 1 : ℕ) = N - n from by omega]
          exact h1)
      have h3 : (N - (n + 1) : ℕ) = (N - n) - 1 := by omega
      rw [h3]
      simpa [Work.Spaces.pzIter_succ] using h2

/-- The `i`-th plain `θ`-partial of a `C^N` function is `C^{N-i}`, including the boundary
case `i = N`. -/
theorem contDiffOn_uncurry_pthIter_le_self {X : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) :
    ∀ (i N : ℕ), i ≤ N → ContDiffOn ℝ (N : ℕ∞ω) (Function.uncurry X) V →
      ContDiffOn ℝ ((N - i : ℕ) : ℕ∞ω) (Function.uncurry (Work.Spaces.pthIter i X)) V := by
  intro i
  induction i with
  | zero => intro N _ h; simpa using h
  | succ n ih =>
      intro N hN h
      have h1 : ContDiffOn ℝ ((N - n : ℕ) : ℕ∞ω)
          (Function.uncurry (Work.Spaces.pthIter n X)) V :=
        ih N (by omega) h
      have h2 : ContDiffOn ℝ (((N - n) - 1 : ℕ) : ℕ∞ω)
          (Function.uncurry (Work.Spaces.pth (Work.Spaces.pthIter n X))) V :=
        Work.FTS.GalBasis.famAux_contDiffOn_uncurry_pth_le hV (N - n - 1) (by
          rw [show (N - n - 1 + 1 : ℕ) = N - n from by omega]
          exact h1)
      have h3 : (N - (n + 1) : ℕ) = (N - n) - 1 := by omega
      rw [h3]
      simpa [Work.Spaces.pthIter_succ] using h2

/-- **Successive plain partial derivatives of a `C^n` function are as smooth as the
remaining order allows.**  Concretely, `∂_z^i ∂_θ^j X ∈ C^k` at any point of the open set
`V` on which `X ∈ C^n`, provided `i + j + k ≤ n`. -/
theorem contDiffAt_pzIter_pthIter {X : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    {n i j k : ℕ} (hijk : i + j + k ≤ n) (hX : ContDiffOn ℝ n (Function.uncurry X) V)
    {z θ : ℝ} (hz : (z, θ) ∈ V) :
    ContDiffAt ℝ k (Function.uncurry (Work.Spaces.pzIter i (Work.Spaces.pthIter j X))) (z, θ) := by
  -- `∂_θ^j X` is `C^{n-j}` on `V`
  have hj : ContDiffOn ℝ ((n - j : ℕ) : ℕ∞ω)
      (Function.uncurry (Work.Spaces.pthIter j X)) V :=
    contDiffOn_uncurry_pthIter_le_self hV j n (by omega) hX
  -- and then `∂_z^i ∂_θ^j X` is `C^{(n-j)-i}` on `V`
  have hi : ContDiffOn ℝ (((n - j) - i : ℕ) : ℕ∞ω)
      (Function.uncurry (Work.Spaces.pzIter i (Work.Spaces.pthIter j X))) V :=
    contDiffOn_uncurry_pzIter_le_self hV i (n - j) (by omega) hj
  -- descend to the requested order `k` (no loss: `k` is an order, so `≤` is `of_le`)
  have hk : ContDiffOn ℝ (k : ℕ∞ω)
      (Function.uncurry (Work.Spaces.pzIter i (Work.Spaces.pthIter j X))) V :=
    hi.of_le (by exact_mod_cast (show k ≤ (n - j) - i by omega))
  exact hk.contDiffAt (hV.mem_nhds hz)

end Work.FTS.GalBasis.GalApprox
