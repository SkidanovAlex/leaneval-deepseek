/-
# Shared definitions for area A8 (`VarBilinInterp`, the `V^r`-valued bilinear interpolation)

This module contains the vocabulary in which the proof of `Work.KMTContract.VarBilinInterp`
(area A8 of the frozen KMT contract) is phrased:

* `pair a l = ∑_n a n * l n` — the duality pairing of a sequence `a : ℕ → ℂ` with a *finitely
  supported* coefficient vector `l : ℕ →₀ ℂ`.  Being a finite sum, it is linear in `a` and in `l`
  without any summability hypothesis;

* `supK K a = max_{n ≤ K} ‖a n‖` and `varK r K a` — the *clamped* variational norm, i.e. the
  variational norm computed from the coordinates `a 0, …, a K` only.  It is a maximum over a
  *finite* set of continuous functions of the coordinates, hence finite and attained; this is
  what makes the "linearisation" of the variational norm (`exists_testObject`) possible;

* `vNormK r K a = supK K a + varK r K a`, and the theorem (`A8Clamp`) that the values
  `ENNReal.ofReal (vNormK r K a)` increase to `variationalNorm r a` as `K → ∞`.

Everything here is on `ℤ → ℂ` with counting measure; the functions live on `ℤ`, the *coefficient
sequences* are indexed by `ℕ`.

This file is the interface shared by `area_A8` and its sub-lemmas; it contains no `sorry`.
-/
import Mathlib
import Submission.Work.KMTContract.Areas

set_option autoImplicit false

namespace Work.KMTAreas

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-- **The duality pairing** of a sequence `a : ℕ → ℂ` with a finitely supported coefficient
vector `l : ℕ →₀ ℂ`.  It is the finite sum `∑_n a n * l n`, hence linear in each variable. -/
noncomputable def pair (a : ℕ → ℂ) (l : ℕ →₀ ℂ) : ℂ := l.sum fun n c => a n * c

/-- **The clamped variation patterns.**  For `K : ℕ` this is the finite type of pairs
`(J, w)` with `J ≤ K` and `w : Fin (J+1) → Fin (K+1)` monotone: a chain of at most `K+1`
indices of `{0, …, K}`.  The clamped `r`-variation is the maximum of the `ℓ^r`-norms of the
increments along such a chain. -/
def Chain (K : ℕ) : Type := Σ J : Fin (K+1), {w : Fin (J.1 + 1) → Fin (K+1) // Monotone w}

instance chainFintype (K : ℕ) : Fintype (Chain K) := by
  classical
  unfold Chain
  infer_instance

instance chainNonempty (K : ℕ) : Nonempty (Chain K) :=
  ⟨⟨0, fun _ => 0, fun _ _ _ => le_rfl⟩⟩

/-- The clamped supremum part: the maximum of `‖a n‖` over `n ≤ K`. -/
noncomputable def supK (K : ℕ) (a : ℕ → ℂ) : ℝ :=
  (Finset.range (K+1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos K)⟩ fun n => ‖a n‖

/-- The clamped variational part: the maximum, over all chains of at most `K+1` indices in
`{0, …, K}`, of the `ℓ^r`-norm of the successive increments of `a` along the chain. -/
noncomputable def varK (r : ℝ≥0) (K : ℕ) (a : ℕ → ℂ) : ℝ :=
  (Finset.univ : Finset (Chain K)).sup' Finset.univ_nonempty fun p =>
    (∑ i : Fin p.1.1, ‖a (p.2.1 i.succ) - a (p.2.1 i.castSucc)‖ ^ (r : ℝ)) ^ (1 / (r : ℝ))

/-- The **clamped variational norm**: the variational norm computed from the coordinates
`a 0, …, a K`. -/
noncomputable def vNormK (r : ℝ≥0) (K : ℕ) (a : ℕ → ℂ) : ℝ := supK K a + varK r K a

/-- The conjugate exponent of `Q ∈ [1, ∞]`: `Q' = (1 - Q⁻¹)⁻¹`, which is `∞` for `Q = 1`. -/
noncomputable def conjExp (Q : ℝ≥0∞) : ℝ≥0∞ := (1 - Q⁻¹)⁻¹

end Work.KMTAreas
