import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.l2Space
import Submission.Work.BoseBoxFock.split_sandwiches
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.kf_Hbog2` — the `(2,0)` Bogoliubov row with two superposed modes

FS `eq:HLambdaSecond`'s Bogoliubov pair row is, in the honest box model `H2ndF`
(see `Work.BoseBoxFock.KafzHonest`'s dictionary table), the weighted sum

    `Σ_k Ŵ₁(k) (a₀† a₀† a_k a_{−k} + h.c.)`

whose **`h.c.` half** — the `(2,0)` slot, i.e. the term with the two condensate
annihilations on the left — is the row

    `Σ_k w_k • (creOf φ_k ∘ creOf ψ_k ∘ ann 0 ∘ ann 0)`

with *two distinct* superposed spectator creations `creOf m (φ k)`, `creOf m (ψ k)`
against the pair `ann 0 ∘ ann 0` of condensate annihilations.  Under the
`⟨condensate | excited⟩` split `Work.BoseB4.split` the two lattice productions
become the single `lift` of the composed spectator operator `creOfE (φ k) ∘ₗ creOfE (ψ k)`
and the two condensate annihilations become `a₀ ∘ a₀`, which is exactly the
anti-normal monomial `monoOp 2 0 (·)`:

    `split (Σ_k w_k • (creOf φ_k ∘ creOf ψ_k ∘ ann 0 ∘ ann 0) x)`
      `= (monoOp 2 0 (Σ_k ↑w_k • (creOfE φ_k ∘ creOfE ψ_k))) (split x)`.

That is the statement of `kf_Hbog2` below.  The proof is the per-mode
dictionary computation (`split_creOf` twice, `split_ann_zero` twice, `lift_comp`,
`lift_comm_a0`, the definition of `monoOp`) plus the reassembly of the weighted
sum of transported monomials (`Work.BoseBoxFock.ss_sum_single`, the one-slot
case of the additivity and `ℂ`-homogeneity of `monoOp` in its spectator slot,
`Work.BoseB4.monoOp_sum` / `monoOp_smul`, with the real coefficients `w k` of the
lattice sum read as the complex coefficients `↑(w k)` via `Complex.coe_smul`).

The per-mode core identity is recorded separately as
`Work.BoseBoxFock.split_creOf_creOf_ann_ann` (it is the `creOf`/`creOf`,
`ann 0`/`ann 0` companion of `Work.BoseB4.split_term2` and
`Work.BoseBoxFock.ss_conj2`).
-/

noncomputable section

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false

variable {m : ℕ} [NeZero m]

/-! ## The per-mode core identity -/

/-- **The `(2,0)` word with two superposed spectator modes.**  For `φ 0 = ψ 0 = 0`
the lattice word `creOf φ ∘ creOf ψ ∘ ann 0 ∘ ann 0` — the `h.c.` Bogoliubov half
`a_k† a_{k'}† a₀ a₀` of the honest model — transports under `split` to the
anti-normal monomial `monoOp 2 0 (creOfE φ ∘ creOfE ψ)`.

Proof: the two `creOf`s are carried to `lift (creOfE ·)` and the two condensate
annihilations to `a₀` (`split_creOf`, `split_ann_zero`); the two `lift`s merge
(`lift_comp`) and the resulting `lift B` is moved across `a₀ ∘ a₀`
(`lift_comm_a0`), giving `(a₀ ∘ a₀) ∘ lift B = a0pow 2 ∘ lift B = monoOp 2 0 B`. -/
theorem split_creOf_creOf_ann_ann (φ ψ : Fin m → ℝ) (hφ : φ 0 = 0) (hψ : ψ 0 = 0)
    (x : RealFock m) :
    split (((creOf m φ).comp ((creOf m ψ).comp ((ann m 0).comp (ann m 0)))) x)
      = (monoOp 2 0 ((creOfE φ).comp (creOfE ψ))) (split x) := by
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    split_creOf φ hφ, split_creOf ψ hψ, split_ann_zero, split_ann_zero]
  rw [monoOp]
  simp only [a0dpow_zero, LinearMap.comp_apply]
  rw [lift_comp_apply]
  rw [lift_a0_apply, lift_a0_apply]
  simp [a0pow, LinearMap.comp_apply]

/-! ## The row -/

theorem kf_Hbog2 {m : ℕ} [NeZero m] {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (s : Finset Mode) (w : Mode → ℝ) (φ ψ : Mode → Fin m → ℝ)
    (hφ : ∀ k ∈ s, φ k 0 = 0) (hψ : ∀ k ∈ s, ψ k 0 = 0) (x : Work.BoseB4.RealFock m) :
    Work.BoseB4.split ((∑ k ∈ s, w k • (((Work.BoseB4.creOf m (φ k)) ∘ₗ (Work.BoseB4.creOf m (ψ k)) ∘ₗ (Work.BoseB4.ann m 0) ∘ₗ (Work.BoseB4.ann m 0)) x)))
      = (Work.BoseB4.monoOp 2 0 (∑ k ∈ s, ((w k : ℝ) : ℂ) • ((Work.BoseBoxFock.creOfE (φ k)) ∘ₗ (Work.BoseBoxFock.creOfE (ψ k))))) (Work.BoseB4.split x) := by
  rw [map_sum]
  have h2 : ∀ k ∈ s,
      split (w k • (((creOf m (φ k)).comp ((creOf m (ψ k)).comp
          ((ann m 0).comp (ann m 0)))) x))
        = w k • ((monoOp 2 0 ((creOfE (φ k)).comp (creOfE (ψ k)))) (split x)) := by
    intro k hk
    rw [Work.BoseB4.split_map_smul,
      split_creOf_creOf_ann_ann (φ k) (ψ k) (hφ k hk) (hψ k hk) x]
  rw [Finset.sum_congr rfl h2]
  exact ss_sum_single s w (fun k => (creOfE (φ k)).comp (creOfE (ψ k))) (split x) 2 0

end Work.BoseBoxFock
