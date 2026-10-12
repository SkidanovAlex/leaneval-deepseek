import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7A.NWindow_bp_N_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBoxFock.window_a_energy_le` — one mode of `a` on the window

The Bessel-type hypothesis

  `hBessel : ∀ f, ⟨(Σ_k n_k) f, f⟩ ≤ Cn ⟨n₊ f, f⟩`

(`n_k = a_k†a_k`, and `Σ_k` is over **all** modes, the condensate mode `0` included)
compares the *total* number operator of the model with FS's true excited number
`T.N = n₊`.  Since `hBessel` is only available for the whole sum, the individual
terms have to be extracted by hand — this is exactly what the window estimate
`NWindow_bp_N_le` (`⟨n₊Φ,Φ⟩ ≤ 𝓜‖Φ‖²`) then turns into a per-mode bound.

Concretely, for `Ψ` in the `M`-window

  `⟨a_k Ψ, a_k Ψ⟩ = ⟨n_k Ψ, Ψ⟩ ≤ Σ_j ⟨n_j Ψ, Ψ⟩ = ⟨(Σ_j n_j) Ψ, Ψ⟩ ≤ Cn ⟨n₊ Ψ, Ψ⟩
    ≤ Cn·M·‖Ψ‖² ≤ Cn·(M+1)·‖Ψ‖²`,

where the middle inequality is `Finset.single_le_sum` and uses that every
`⟨n_j Ψ, Ψ⟩ = ‖a_jΨ‖² ≥ 0` (adjointness of `a_j†` + positivity of the Fock form).
No hypothesis beyond `0 ≤ Cn`, `0 ≤ M` and the window is used.

Restricted to a single term this is the `M + 1` form used by the bridge
(`window_a_pair_le` is the corresponding off-diagonal statement).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

/-- **One annihilation operator on the window.**  If the total number operator is
Bessel-dominated by FS's `n₊` with constant `Cn`, then on the `n₊`-window `[0,𝓜]`
each single mode obeys `‖a_k Ψ‖² ≤ Cn (𝓜+1) ‖Ψ‖²`.  The `+1` is the slack that
absorbs the difference between `𝓜` and its floor; no sharpness is claimed here. -/
theorem window_a_energy_le {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F) (Cn : ℝ) (hCn0 : 0 ≤ Cn)
    (hBessel : ∀ f : F.H, F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f)
    {M : ℝ} (hM : 0 ≤ M) {Ψ : F.H} (hΨ : T.NWindow M Ψ) (k : Mode) :
    F.bp (F.a k Ψ) (F.a k Ψ) ≤ Cn * (M + 1) * F.normSq Ψ := by
  -- the window bound for the true excited number `n₊`
  have hNle : F.bp (T.N Ψ) Ψ ≤ M * F.normSq Ψ :=
    Work.BoseB7A.NWindow_bp_N_le F T hM hΨ
  -- `⟨a_k Ψ, a_k Ψ⟩ = ⟨n_k Ψ, Ψ⟩` (adjointness of `a_k†`)
  have hk : F.bp (F.a k Ψ) (F.a k Ψ) = F.bp (F.nOp k Ψ) Ψ := by
    show F.bp (F.a k Ψ) (F.a k Ψ) = F.bp (F.aDag k (F.a k Ψ)) Ψ
    rw [F.aDag_adjoint k (F.a k Ψ) Ψ]
  rw [hk]
  -- the total number form is the sum of the per-mode forms
  have hsum : F.bp ((∑ j : Mode, F.nOp j) Ψ) Ψ = ∑ j : Mode, F.bp (F.nOp j Ψ) Ψ := by
    simp [map_sum]
  -- hence the `k`-th term is dominated by the whole sum (all terms are `≥ 0`)
  have hle_sum : F.bp (F.nOp k Ψ) Ψ ≤ F.bp ((∑ j : Mode, F.nOp j) Ψ) Ψ := by
    rw [hsum]
    exact Finset.single_le_sum (fun j _ => Work.BoseB7.bp_nOp_nonneg F j Ψ)
      (Finset.mem_univ k)
  have hnorm : 0 ≤ F.normSq Ψ := F.bp_nonneg Ψ
  calc F.bp (F.nOp k Ψ) Ψ ≤ F.bp ((∑ j : Mode, F.nOp j) Ψ) Ψ := hle_sum
    _ ≤ Cn * F.bp (T.N Ψ) Ψ := hBessel Ψ
    _ ≤ Cn * (M * F.normSq Ψ) := mul_le_mul_of_nonneg_left hNle hCn0
    _ ≤ Cn * (M + 1) * F.normSq Ψ := by nlinarith

end Work.BoseBoxFock
