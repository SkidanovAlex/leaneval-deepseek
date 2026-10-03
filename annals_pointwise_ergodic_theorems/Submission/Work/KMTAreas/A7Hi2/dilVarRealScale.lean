import Mathlib
import Submission.Work.KMTAreas.A7Hi.eLpNorm_chainPart_le_uniform
import Submission.Work.KMTAreas.A7.variationalNorm_mul_le
import Submission.Work.KMTAreas.A7Lpd.supChainSq

/-!
# The real-scale lacunary dilation variational estimate (JSW Theorem 1.1)

`Work.KMTAreas.A7Hi.dilFam` / `Work.KMTAreas.A7Hi.DilVarClean` are stated for **integer** scale
sequences `σ : ℕ → ℕ`; the fibre computations of the low-pass Ionescu--Wainger walk
(`Submission/Work/A7Hi2/SieveDefs.lean`, the sieve/decimated-dilation decomposition of the IW comb)
need the **real**-scale form: for a fixed Schwartz kernel `K` and every real sequence `σ` with
`1 ≤ σ n` and `2 σ n ≤ σ (n+1)`,

  `‖ Vʳ (n ↦ Σ'_j (1/σ n) K (j/σ n) · f (x - j)) ‖_{ℓᵖ(ℤ)} ≤ C ‖f‖_{ℓᵖ(ℤ)}`,

`C` depending only on `p, r, K`.  This is JSW Theorem 1.1 (TAMS 360 (2008), 6711–6742) for real
lacunary sequences, and it is exactly the shape of the `Prop`
`Work.A7Hi2.DilVarRealScale` fixed in `Submission/Work/A7Hi2/SieveDefs.lean`.

## The decomposition of the proof (three pieces)

1. **Rounding = `Nat.floor`** (`roundRealScale`, proved below).  For `1 ≤ σ n` and
   `2 σ n ≤ σ (n+1)`, the integer family `c n := ⌊σ n⌋` satisfies `1 ≤ c n`, `c n ≤ σ n < c n + 1`
   and `2 c n ≤ c (n+1)`.  (The floor is the right rounding precisely because the *upper* bound
   `σ n < c n + 1` is the tight one, and `⌊2x⌋ ≥ 2⌊x⌋` gives the lacunarity.)
2. **The perturbation half** `dilPerturbVar` (delegated): the variational norm of the *difference*
   family `n ↦ (K_{σ n} − K_{c n}) * f` is bounded by `C‖f‖` — the kernel difference has `ℓ¹`-mass
   `O(1/σ n)` (`dilPerturbL1`, the mean-value/Schwartz estimate) and `Σ_n 1/σ n < ∞` (geometric).
3. **The integer half** is the *proved* `Work.KMTAreas.A7Hi.DilVarClean`, applied to `c`, plus the
   subadditivity `variationalNorm_add_le` of `Submission.VarNorm`.
-/

namespace Work.KMTAreas.A7Hi2

open MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

/-! ## 1. Rounding a real lacunary sequence to a `2`-lacunary integer one (the floor) -/

/-- **Rounding.**  If `σ : ℕ → ℝ` is lacunary with `1 ≤ σ n` and `2 σ n ≤ σ (n+1)`, then the
integer sequence `c n := ⌊σ n⌋` is lacunary in the same sense, is bounded above by `σ n`, and
satisfies the *tight* upper bound `σ n < c n + 1`. -/
lemma roundRealScale (σ : ℕ → ℝ) (hσ1 : ∀ n, 1 ≤ σ n) (hσ2 : ∀ n, 2 * σ n ≤ σ (n + 1)) :
    (∀ n, 1 ≤ Nat.floor (σ n)) ∧ (∀ n, (Nat.floor (σ n) : ℝ) ≤ σ n) ∧
      (∀ n, σ n < (Nat.floor (σ n) : ℝ) + 1) ∧
      (∀ n, 2 * Nat.floor (σ n) ≤ Nat.floor (σ (n + 1))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    have h : ((1 : ℕ) : ℝ) ≤ σ n := by simpa using hσ1 n
    have := Nat.floor_mono h
    simpa using this
  · intro n
    exact Nat.floor_le (by linarith [hσ1 n])
  · intro n
    exact Nat.lt_floor_add_one (σ n)
  · intro n
    have hb : (Nat.floor (σ n) : ℝ) ≤ σ n := Nat.floor_le (by linarith [hσ1 n])
    have hle : ((2 * Nat.floor (σ n) : ℕ) : ℝ) ≤ σ (n + 1) := by
      push_cast
      linarith [hb, hσ2 n]
    have := Nat.floor_mono hle
    rwa [Nat.floor_natCast] at this

/-! ## 2. The real-scale statement (the `Work.A7Hi2.DilVarRealScale` Prop)

The statement below is the real-scale JSW estimate, i.e. *verbatim* the `Prop`
`Work.A7Hi2.DilVarRealScale` of `Submission/Work/A7Hi2/SieveDefs.lean`, so that the sieve
decomposition can consume it by one application.

Its proof is the composition of the four bricks recorded in the module docstring:

* `roundRealScale` (**proved above**),
* `Work.KMTAreas.A7Hi2.dilPerturbVar` (the perturbation half; delegated),
* `Work.KMTAreas.A7Hi2.dilVarRealScale_of_perturb` (the assembly socket; delegated),
* `Work.KMTAreas.A7Hi2.schwartzDilateMass` (the Schwartz ℓ¹-mass bound discharging the socket's
  summability input; delegated),

and the integer half `Work.KMTAreas.A7Hi.DilVarClean` (proved in the tree).  All four bricks are in
the tree; the composition into the real-scale statement (and the interface
`Work.A7Hi2.DilVarRealScale` of `Submission/Work/A7Hi2/SieveDefs.lean`) is in the sibling module
`Submission/Work/KMTAreas/A7Hi2/dilVarRealScaleFinal.lean` — it is kept out of this file because the
delegated socket `dilVarRealScale_of_perturb` imports this one (for `roundRealScale`). -/

end

end Work.KMTAreas.A7Hi2
