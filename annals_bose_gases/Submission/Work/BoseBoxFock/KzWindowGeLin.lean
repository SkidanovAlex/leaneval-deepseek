import Mathlib.Algebra.Algebra.Basic
import Mathlib.Analysis.Real.Sqrt
import Submission.Work.BoseBoxFock.Defs
import Submission.Work.BoseBoxFock.window_a_energy_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBoxFock.KzWindowGeLin` — off-diagonal `a_k` on the window

This is the *linear* (off-diagonal) companion of `window_a_energy_le`: under the
Bessel-type hypothesis

  `hBessel : ∀ f, ⟨(Σ_k n_k) f, f⟩ ≤ Cn ⟨n₊ f, f⟩`

and on the `n₊`-window `[0,𝓜]`, every single annihilation operator satisfies

  `|⟨a_k Ψ, Ψ⟩| ≤ √(Cn (𝓜+1)) · ‖Ψ‖²`.

The proof is one line of Cauchy–Schwarz (`Work.BoseB7.bp_cauchy_abs`) against the
diagonal bound `⟨a_kΨ, a_kΨ⟩ ≤ Cn(𝓜+1)‖Ψ‖²` of `window_a_energy_le`:

  `|⟨a_kΨ, Ψ⟩| ≤ ‖a_kΨ‖·‖Ψ‖ = √(⟨a_kΨ,a_kΨ⟩)·‖Ψ‖
     ≤ √(Cn(𝓜+1))·‖Ψ‖²`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

/-- **Off-diagonal one-mode bound on the window.**  With the same Bessel
hypothesis as `window_a_energy_le`, on the `n₊`-window `[0,𝓜]` each single mode
obeys `|⟨a_k Ψ, Ψ⟩| ≤ √(Cn(𝓜+1)) ‖Ψ‖²`.  Pure Cauchy–Schwarz applied to the
diagonal estimate. -/
theorem KzWindowGeLin {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F) (Cn : ℝ) (hCn0 : 0 ≤ Cn)
    (hBessel : ∀ f : F.H, F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f)
    {M : ℝ} (hM : 0 ≤ M) {g : F.H} (hg : T.NWindow M g) (j : Mode) :
    |F.bp (F.a j g) g| ≤ Real.sqrt (Cn * (M + 1)) * F.normSq g := by
  -- the diagonal bound on the single mode
  have hdiag : F.bp (F.a j g) (F.a j g) ≤ Cn * (M + 1) * F.normSq g :=
    window_a_energy_le F T Cn hCn0 hBessel hM hg j
  have hg0 : 0 ≤ F.normSq g := F.bp_nonneg g
  have hc : 0 ≤ Cn * (M + 1) := mul_nonneg hCn0 (by linarith)
  -- `normSq` is, definitionally, the Fock form at `(g, g)`
  have hnorm : F.bp g g = F.normSq g := by rw [Work.BoseB7.FockData.normSq]
  calc |F.bp (F.a j g) g|
      ≤ Real.sqrt (F.bp (F.a j g) (F.a j g)) * Real.sqrt (F.bp g g) :=
        Work.BoseB7.bp_cauchy_abs F (F.a j g) g
    _ ≤ Real.sqrt (Cn * (M + 1) * F.normSq g) * Real.sqrt (F.normSq g) := by
        rw [hnorm]
        exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hdiag) (Real.sqrt_nonneg _)
    _ = Real.sqrt (Cn * (M + 1)) * Real.sqrt (F.normSq g) * Real.sqrt (F.normSq g) := by
        rw [Real.sqrt_mul hc (F.normSq g)]
    _ = Real.sqrt (Cn * (M + 1)) * F.normSq g := by
        rw [mul_assoc, Real.mul_self_sqrt hg0]

end Work.BoseBoxFock
