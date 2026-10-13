/-
# `FTS/PhiStar/CoreAux/F0_zpz.lean` — the flat class `F0` is stable under `z ↦ z · ∂_z f`

`Work.FTS.PhiStar.F0 n K f` (see `CoreAux/Defs.lean`) says that all the mixed weighted
derivatives `(z+1)^k ∂_z^k D_θ^i f` with `k + i ≤ n` are bounded by `K` on the open quadrant
`Q0 = (0,∞) × (0,π/2)`.  This file proves

`F0 (n+1) K f  →  F0 n ((n+1)·K) (fun z θ => z · ∂_z f z θ)`,

i.e. that multiplying the radial derivative of `f` by `z` (the operator `D_z = z ∂_z`) loses
one order of the flat class and multiplies the constant by `n+1`.

**The mathematics.**  Write `g := ∂_z f`.  Two facts are used.

* `D_θ^i (D_z f) = D_z (D_θ^i f)` on the open quadrant, for `f` of class `C^∞` there.  This is
  the commutation of the curvilinear operators `D_z = z∂_z` and `D_θ = sin(2θ)∂_θ`, a
  Clairaut identity; it is `DthIter_DzIter_eqOn_of_isOpen` of
  `ThetaU/OpenSliceAux/DthIter_DzIter_eqOn_of_isOpen.lean` (with `j = 1`, using only that
  `SmoothOpen` is `C^n` for every `n`), specialised here as `DthIter_Dz_comm_smoothOpen`.
* `∂_z^k (z · ∂_z g) = z · ∂_z^{k+1} g + k · ∂_z^k g` — the elementary product rule for `z`
  followed by a first-order Leibniz rule (`k` copies of the `∂_z z = 1` term).  This is
  `pzIter_zpz_expand` below, proved by induction on `k` using the differentiability of the
  `z`-slices supplied by `SmoothOpen`.

Combining the two, the derivative to be bounded is written as

`(z+1)^k (z ∂_z^{k+1} g + k ∂_z^k g)`, and since `z ≤ z+1`,

`|(z+1)^k z ∂_z^{k+1} g| ≤ |(z+1)^{k+1} ∂_z^{k+1} g| ≤ K`,
`|(z+1)^k k ∂_z^k g| ≤ k·K`,

so the total is at most `K + k·K = (k+1)K ≤ (n+1)K` because `k + i ≤ n`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.PhiStar.CoreAux.Defs
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.CoreAux

/-- **Commutation of `D_θ^i` with `D_z = z ∂_z` on the open quadrant**, for a datum of class
`C^∞` there:  `D_θ^i (z ∂_z f) = z ∂_z (D_θ^i f)` at every interior point.

This is `DthIter_DzIter_eqOn_of_isOpen` (`j = 1`), whose left side is
`D_θ^i (D_z^1 f) = D_θ^i (z ∂_z f)` and whose right side is `mixed 1 i f = z ∂_z (D_θ^i f)`;
`SmoothOpen` is exactly the finite-order smoothness `∀ n, ContDiffOn ℝ n _ Q0` required by
that lemma. -/
theorem DthIter_Dz_comm_smoothOpen {f : ℝ → ℝ → ℝ} (hsf : Work.FTS.EllipticEst.SmoothOpen f)
    (i : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DthIter i (fun z θ => z * Work.Spaces.pz f z θ) z θ
        = z * Work.Spaces.pz (Work.Spaces.DthIter i f) z θ := by
  intro z θ hz hθ hθ'
  have h := Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
    Work.FTS.EllipticEst.isOpen_Q0 ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hsf) 1 i
    (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ'⟩)
  exact h

/-- **The `k`-fold product rule for `z ↦ z ∂_z g`.**  If `A` agrees with `z ∂_z B` on the open
quadrant and `B` is `C^∞` there, then for every interior point

`∂_z^k A = z · ∂_z^{k+1} B + k · ∂_z^k B`.

The proof is an induction on `k`.  The base case is the hypothesis.  In the step, the
induction hypothesis identifies the slice `z' ↦ ∂_z^k A z' θ` with
`z' ↦ z' ∂_z^{k+1} B z' θ + k ∂_z^k B z' θ` near `z` (it holds for every interior `z'`), so
its derivative is computed from the two `HasDerivAt`-statements for the `z`-slices of
`∂_z^{k+1} B` and `∂_z^k B` (`SmoothOpen.hasDerivAt_slice_pzIter`), giving
`∂_z^{k+1} B + z ∂_z^{k+2} B + k ∂_z^{k+1} B = z ∂_z^{k+2} B + (k+1) ∂_z^{k+1} B`. -/
theorem pzIter_zpz_expand {A B : ℝ → ℝ → ℝ}
    (hA : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → A z θ = z * Work.Spaces.pz B z θ)
    (hB : Work.FTS.EllipticEst.SmoothOpen B) (k : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pzIter k A z θ
        = z * Work.Spaces.pzIter (k + 1) B z θ + (k : ℝ) * Work.Spaces.pzIter k B z θ := by
  induction k with
  | zero =>
      intro z θ hz hθ hθ'
      simp only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Nat.cast_zero, zero_mul,
        add_zero]
      exact hA z θ hz hθ hθ'
  | succ k ih =>
      intro z θ hz hθ hθ'
      have heq : (fun z' : ℝ => Work.Spaces.pzIter k A z' θ)
          =ᶠ[𝓝 z] (fun z' => z' * Work.Spaces.pzIter (k + 1) B z' θ
              + (k : ℝ) * Work.Spaces.pzIter k B z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz' hθ hθ'
      have hAd : HasDerivAt (fun z' : ℝ => Work.Spaces.pzIter (k + 1) B z' θ)
          (Work.Spaces.pzIter (k + 1 + 1) B z θ) z :=
        hB.hasDerivAt_slice_pzIter (k + 1) ⟨hθ, hθ'⟩ hz
      have hBd : HasDerivAt (fun z' : ℝ => Work.Spaces.pzIter k B z' θ)
          (Work.Spaces.pzIter (k + 1) B z θ) z :=
        hB.hasDerivAt_slice_pzIter k ⟨hθ, hθ'⟩ hz
      have h1 : HasDerivAt (fun z' : ℝ => z' * Work.Spaces.pzIter (k + 1) B z' θ)
          (1 * Work.Spaces.pzIter (k + 1) B z θ
            + z * Work.Spaces.pzIter (k + 1 + 1) B z θ) z :=
        (hasDerivAt_id z).mul hAd
      have h2 : HasDerivAt (fun z' : ℝ => (k : ℝ) * Work.Spaces.pzIter k B z' θ)
          ((k : ℝ) * Work.Spaces.pzIter (k + 1) B z θ) z := hBd.const_mul (k : ℝ)
      have hderiv : deriv (fun z' : ℝ => z' * Work.Spaces.pzIter (k + 1) B z' θ
            + (k : ℝ) * Work.Spaces.pzIter k B z' θ) z
          = 1 * Work.Spaces.pzIter (k + 1) B z θ
            + z * Work.Spaces.pzIter (k + 1 + 1) B z θ
            + (k : ℝ) * Work.Spaces.pzIter (k + 1) B z θ := (h1.add h2).deriv
      rw [Work.Spaces.pzIter_succ]
      simp only [Work.Spaces.pz]
      rw [heq.deriv_eq, hderiv]
      push_cast
      ring

theorem F0_zpz {n : ℕ} {K : ℝ} {f : ℝ → ℝ → ℝ} (hK : 0 ≤ K) (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hf : Work.FTS.PhiStar.F0 (n + 1) K f) : Work.FTS.PhiStar.F0 n (((n : ℝ) + 1) * K) (fun z θ => z * Work.Spaces.pz f z θ) := by
  intro k i hki x y hx hy hxy
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  -- rewrite the `k`-fold `∂_z` by the product rule `∂_z^k(z ∂_z B) = z ∂_z^{k+1} B + k ∂_z^k B`
  have hexp := pzIter_zpz_expand
    (A := Work.Spaces.DthIter i (fun z θ => z * Work.Spaces.pz f z θ))
    (B := Work.Spaces.DthIter i f) (DthIter_Dz_comm_smoothOpen hsf i) (hsf.DthIter i) k x y
    hx hy hxy
  rw [hexp]
  -- the two pieces of the flat bound for `B = D_θ^i f`
  have hbA : (x + 1) ^ (k + 1) * |Work.Spaces.pzIter (k + 1) (Work.Spaces.DthIter i f) x y| ≤ K := by
    have h := hf (k + 1) i (by omega) x y hx hy hxy
    rwa [abs_mul, abs_of_pos (pow_pos hx1 (k + 1))] at h
  have hbB : (x + 1) ^ k * |Work.Spaces.pzIter k (Work.Spaces.DthIter i f) x y| ≤ K := by
    have h := hf k i (by omega) x y hx hy hxy
    rwa [abs_mul, abs_of_pos (pow_pos hx1 k)] at h
  have htri : |x * Work.Spaces.pzIter (k + 1) (Work.Spaces.DthIter i f) x y
        + (k : ℝ) * Work.Spaces.pzIter k (Work.Spaces.DthIter i f) x y|
      ≤ (x + 1) * |Work.Spaces.pzIter (k + 1) (Work.Spaces.DthIter i f) x y|
        + (k : ℝ) * |Work.Spaces.pzIter k (Work.Spaces.DthIter i f) x y| := by
    have h1 : |x * Work.Spaces.pzIter (k + 1) (Work.Spaces.DthIter i f) x y|
        ≤ (x + 1) * |Work.Spaces.pzIter (k + 1) (Work.Spaces.DthIter i f) x y| := by
      rw [abs_mul, abs_of_nonneg hx.le]
      exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    have h2 : |(k : ℝ) * Work.Spaces.pzIter k (Work.Spaces.DthIter i f) x y|
        = (k : ℝ) * |Work.Spaces.pzIter k (Work.Spaces.DthIter i f) x y| := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
    calc |x * Work.Spaces.pzIter (k + 1) (Work.Spaces.DthIter i f) x y
            + (k : ℝ) * Work.Spaces.pzIter k (Work.Spaces.DthIter i f) x y|
        ≤ |x * Work.Spaces.pzIter (k + 1) (Work.Spaces.DthIter i f) x y|
          + |(k : ℝ) * Work.Spaces.pzIter k (Work.Spaces.DthIter i f) x y| := abs_add_le _ _
      _ ≤ (x + 1) * |Work.Spaces.pzIter (k + 1) (Work.Spaces.DthIter i f) x y|
          + (k : ℝ) * |Work.Spaces.pzIter k (Work.Spaces.DthIter i f) x y| := by
            rw [h2]; exact add_le_add h1 le_rfl
  rw [abs_mul, abs_of_pos (pow_pos hx1 k)]
  calc (x + 1) ^ k * |x * Work.Spaces.pzIter (k + 1) (Work.Spaces.DthIter i f) x y
          + (k : ℝ) * Work.Spaces.pzIter k (Work.Spaces.DthIter i f) x y|
      ≤ (x + 1) ^ k * ((x + 1) * |Work.Spaces.pzIter (k + 1) (Work.Spaces.DthIter i f) x y|
          + (k : ℝ) * |Work.Spaces.pzIter k (Work.Spaces.DthIter i f) x y|) :=
          mul_le_mul_of_nonneg_left htri (pow_nonneg hx1.le k)
    _ = (x + 1) ^ (k + 1) * |Work.Spaces.pzIter (k + 1) (Work.Spaces.DthIter i f) x y|
          + (k : ℝ) * ((x + 1) ^ k
            * |Work.Spaces.pzIter k (Work.Spaces.DthIter i f) x y|) := by
          rw [pow_succ]; ring
    _ ≤ K + (k : ℝ) * K := add_le_add hbA (mul_le_mul_of_nonneg_left hbB (Nat.cast_nonneg k))
    _ = ((k : ℝ) + 1) * K := by ring
    _ ≤ ((n : ℝ) + 1) * K := by
          have hkn : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : k ≤ n)
          exact mul_le_mul_of_nonneg_right (by linarith) hK

end Work.FTS.PhiStar.CoreAux
