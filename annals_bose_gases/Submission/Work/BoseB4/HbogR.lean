import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.l2Space
import Submission.Work.BoseB4.half_smul_sum
import Submission.Work.BoseB4.split_term1
import Submission.Work.BoseB4.split_term2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.HbogR` — the Bogoliubov row under `split`, with the *real* `½`

## Why a second operator (history — the definition is now repaired)

`Work.BoseB4.Hbog` (in `Submission/Work/BoseB4/H2nd.lean`) is FS
`eq:HLambdaSecond`'s Bogoliubov pair row
`½(2π)⁻³∫Ŵ₁(k)(a₀†a₀†a_ka_{−k} + h.c.)dk`.  **In an earlier revision** its
defining scalar was the *un-annotated* literal `(1 / 2) • …`, which Lean
elaborates at the default **natural-number** type: what was then stored in the
environment was `@HSMul.hSMul Nat _ _ ((1 : ℕ) / 2) (…)`, and `(1 : ℕ) / 2 = 0`,
so that `Work.BoseB4.Hbog D = 0` for every `D` (machine-checked at the time,
together with a counterexample to the transport identity for the row): the
definition silently lost the whole Bogoliubov row.

That revision has been **repaired**: `H2nd.lean` now carries the annotation
`(1 / 2 : ℝ)`, so `Hbog` denotes the row it is meant to.  `HbogR` below is the
same operator under a name of its own — it was introduced while `Hbog` was still
degenerate, and it is what `split_HbogR` is proved for; after the repair `Hbog`
and `HbogR` are definitionally equal, which is how `Work.BoseB4.split_Hbog`
transfers `split_HbogR` to `Hbog`.  The two files recording the degenerate state
(`Hbog_degenerate.lean`, `Hbog_counterexample.lean`) have been removed.

`split_HbogR` is the transport identity for the row — the content of
`Work.BoseB4.split_Hbog`.  While `Hbog` was the natural-number version the
statement of `split_Hbog` was FALSE: its left-hand side was `split 0 = 0`
identically, while `monoOp 0 2 (Kbog1 D) + monoOp 2 0 (Kbog2 D)` is not zero
(take `m = 2` and `D` with `Ŵ₁(1) ≠ 0`: then `Kbog1 D = ½ • (annX 1 ∘ annX 1)`
with `annX 1 = annC (Excited 2) ⟨1, ·⟩ ≠ 0`).
-/

noncomputable section

open scoped lp BigOperators

namespace Work.BoseB4

set_option autoImplicit false

variable {m : ℕ} [NeZero m]

/-! ## The intended operator -/

/-- **FS's Bogoliubov pair row with the intended real coefficient `½`**: the body
of `Work.BoseB4.Hbog` with `(1 / 2 : ℝ)` in place of the natural-number `(1/2)`. -/
noncomputable def HbogR (D : H2ndData m) : RealFock m →ₗ[ℝ] RealFock m :=
  (1 / 2 : ℝ) • ∑ k ∈ exc m, D.W1 k •
    (((cre m 0).comp ((cre m 0).comp ((ann m k).comp (ann m (-k))))) +
      ((cre m k).comp ((cre m (-k)).comp ((ann m 0).comp (ann m 0)))))

/-! ## `split` is `ℝ`-linear, pointwise -/

lemma split_apply_smul (c : ℝ) (y : RealFock m) : split (c • y) = c • split y :=
  map_smul split c y

lemma split_apply_sum {ι : Type*} (s : Finset ι) (f : ι → RealFock m) :
    split (∑ i ∈ s, f i) = ∑ i ∈ s, split (f i) :=
  map_sum split f s

lemma split_apply_add (y z : RealFock m) : split (y + z) = split y + split z :=
  map_add split y z

/-! ## The two transported rows -/

/-- The `(0,2)` row `monoOp 0 2 (annX k ∘ annX (−k))` applied to `split x`. -/
noncomputable def HbogRow02 (x : RealFock m) (k : Fin m) : FockCore (cfock (Excited m)) :=
  (monoOp 0 2 ((annX m k).comp (annX m (-k)))) (split x)

/-- The `(2,0)` row `monoOp 2 0 (creX k ∘ creX (−k))` applied to `split x`. -/
noncomputable def HbogRow20 (x : RealFock m) (k : Fin m) : FockCore (cfock (Excited m)) :=
  (monoOp 2 0 ((creX m k).comp (creX m (-k)))) (split x)

/-- `c • ∑ k, w k • v k = ∑ k, (↑(c * w k) : ℂ) • v k` — pulling a *real* scalar
out of a weighted sum in the complex Fock core, turning it into a complex one. -/
lemma sum_smul_add {M : Type*} [AddCommMonoid M] [Module ℂ M] {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (u v : ι → M) :
    ∑ k ∈ s, c k • (u k + v k) = (∑ k ∈ s, c k • u k) + ∑ k ∈ s, c k • v k := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => smul_add _ _ _

/-! ## The transport identity -/

/-- **The Bogoliubov row of FS `eq:HLambdaSecond`, transported by `split`.**  For
the intended operator `HbogR` (real `½`), the two Bogoliubov halves `a₀†a₀†a_ka_{−k}`
and `a_k†a_{−k}†a₀a₀` become the anti-normal monomials `monoOp 0 2 (Kbog1 D)` and
`monoOp 2 0 (Kbog2 D)`.

Term by term: `split` pushes through the two `1/2`-weighted finite sums and each
lattice word is transported by `split_term1` / `split_term2` (`SplitHbogPre` +
`split_term1` / `split_term2`); on the right-hand side the spectator operators
`Kbog1 D`, `Kbog2 D` are expanded out of `monoOp` with `monoOp_sum_smul`, and the
scalar bookkeeping `½ • (w • v) = ↑(½ w) • v` is `half_smul_sum`. -/
theorem split_HbogR (D : H2ndData m) (x : RealFock m) :
    split (HbogR D x) = (monoOp 0 2 (Kbog1 D) + monoOp 2 0 (Kbog2 D)) (split x) := by
  have hL : split (HbogR D x)
      = (1/2 : ℝ) • ∑ k ∈ exc m, D.W1 k • (HbogRow02 x k + HbogRow20 x k) := by
    rw [HbogR]
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.add_apply,
      LinearMap.comp_apply]
    rw [split_apply_smul, split_apply_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    have hk0 : k ≠ 0 := by simpa [exc] using hk
    have hnk0 : -k ≠ 0 := by simpa using hk0
    rw [split_apply_smul]
    congr 1
    rw [split_apply_add, split_term1 k hk0 hnk0 x, split_term2 k hk0 hnk0 x]
    rfl
  have hR : (monoOp 0 2 (Kbog1 D) + monoOp 2 0 (Kbog2 D)) (split x)
      = (1/2 : ℝ) • ∑ k ∈ exc m, D.W1 k • (HbogRow02 x k + HbogRow20 x k) := by
    rw [LinearMap.add_apply]
    have h1 : (monoOp 0 2 (Kbog1 D)) (split x)
        = ∑ k ∈ exc m, (((1/2) * D.W1 k : ℝ) : ℂ) • HbogRow02 x k := by
      rw [Kbog1, monoOp_sum_smul, LinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro k hk
      rw [LinearMap.smul_apply]
      rfl
    have h2 : (monoOp 2 0 (Kbog2 D)) (split x)
        = ∑ k ∈ exc m, (((1/2) * D.W1 k : ℝ) : ℂ) • HbogRow20 x k := by
      rw [Kbog2, monoOp_sum_smul, LinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro k hk
      rw [LinearMap.smul_apply]
      rfl
    rw [h1, h2]
    rw [half_smul_sum (exc m) D.W1 (1/2) (fun k => HbogRow02 x k + HbogRow20 x k),
      sum_smul_add (exc m) (fun k => (((1/2) * D.W1 k : ℝ) : ℂ)) (fun k => HbogRow02 x k)
        (fun k => HbogRow20 x k)]
  rw [hL, hR]

end Work.BoseB4
