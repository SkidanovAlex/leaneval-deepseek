import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.l2Space
import Submission.Work.BoseBoxFock.KafzHonest

/-!
# `Work.BoseBoxFock.kf_Q3a` — the dictionary row `a₀† ã_s† a_{s−k} a_k` (`Q̃₃`, forward half)

FS `eq:3Qtilde` on the honest modes has, besides the kinetic/potential rows, the
three-mode row

    ℓ⁻³ Σ_s Σ_k f_L(s) Ŵ₁(k) a₀† ã_s† a_{s−k} a_k + h.c. ,

whose **forward half** is the word `a₀† ã_s† a_{s−k} a_k` with
`ã_s = annOf m (g s)`-type superposed modes.  Under the ⟨condensate | excited⟩ split
`Work.BoseB4.split` the condensate ladder `a₀†` becomes `a₀†` on the spectator core and
every superposed excited mode `annOf m (f k)` / `creOf m (g s)` becomes `lift` of the
corresponding operator on `cfock (Excited m)` (`KafzHonest.split_annOf`,
`KafzHonest.split_creOf`), so the row is a single anti-normal monomial

    `a₀† ∘ (ã_s† ∘ a_{s−k} ∘ a_k)  ↦  monoOp 0 1 (specC g s ∘ annOfE (f (s−k)) ∘ annOfE (f k))`

(`monoOp 0 1 B = a₀† ∘ lift B`, `Work.BoseB4.monoOp_zero_one`).  The theorem below is
that statement for an arbitrary weighted double sum: the *dictionary* (FS §8's
anti-normal reordering) restricted to this row, in the applied form in which the
`thm:Kafz` assembly consumes it.

## Proof

`hstep` handles one pair `(s, k)`: the three splits
(`split_cre_zero`, `split_creOf`, `split_annOf`, `split_annOf`) turn the left-hand side
into `a₀† (lift A (lift B (lift C (split x))))`, the two `lift_lift` rewrites compose
the three spectator lifts into one (`lift` is levelwise, `Work.BoseB4.lift_comp`), and
`monoOp_zero_one` identifies `a₀† ∘ lift ·` with `monoOp 0 1 ·`.  The sum is then
reassembled: `map_sum` + `split_map_smul` push `split` through the two `Finset.sum`s and
the real scalars, and `monoOp_sum`/`monoOp_smul` (together with `Complex.coe_smul`,
converting the lattice's real weights into complex ones) push `monoOp 0 1` back inside
the sum.  The `s = k` special case (where `a_{s−k} = a₀` is the condensate) is *not*
special here: the forward half is a genuine single monomial for every pair, the Wick
correction being confined to the `h.c.` half (`kf_Q3b`) and to the `Q3B11/Q3B00`
families of `Work.BoseB4.Q3C_eq_family`.
-/

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false

variable {m : ℕ} [NeZero m]

/-- `lift` of a composite is the composite of the lifts, at the level of vectors:
`lift A (lift B z) = lift (A ∘ B) z` (`Work.BoseB4.lift_comp`, applied). -/
private lemma lift_lift {A B : cfock (Excited m) →ₗ[ℂ] cfock (Excited m)}
    (z : FockCore (cfock (Excited m))) :
    lift A (lift B z) = lift (A.comp B) z :=
  (LinearMap.congr_fun (lift_comp A B) z).symm

/-- **The `Q̃₃` forward half transports to `monoOp 0 1`.**  For honest superposed modes
(`g s 0 = 0`, `f k 0 = 0`), the split of `a₀† ã_s† a_{s−k} a_k` is the anti-normal
monomial `monoOp 0 1 (creOfE (g s) ∘ annOfE (f (s−k)) ∘ annOfE (f k))`, summed with
the lattice weights `γ`. -/
theorem kf_Q3a {m : ℕ} [NeZero m] {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (S Ks : Finset Mode) (γ : Mode → Mode → ℝ) (g f : Mode → Fin m → ℝ)
    (hg : ∀ s ∈ S, g s 0 = 0) (hf : ∀ k : Mode, f k 0 = 0) (x : Work.BoseB4.RealFock m) :
    Work.BoseB4.split ((∑ s ∈ S, ∑ k ∈ Ks, γ s k •
        (((Work.BoseB4.cre m 0) ∘ₗ (Work.BoseB4.creOf m (g s)) ∘ₗ (Work.BoseB4.annOf m (f (s - k))) ∘ₗ (Work.BoseB4.annOf m (f k))) x)))
      = (Work.BoseB4.monoOp 0 1 (∑ s ∈ S, ∑ k ∈ Ks, ((γ s k : ℝ) : ℂ) •
              ((Work.BoseBoxFock.creOfE (g s)) ∘ₗ (Work.BoseBoxFock.annOfE (f (s - k))) ∘ₗ (Work.BoseBoxFock.annOfE (f k))))) (Work.BoseB4.split x) := by
  classical
  -- one pair `(s, k)`: the three spectator splits compose into a single `lift`, and
  -- `a₀† ∘ lift B = monoOp 0 1 B`.
  have hstep : ∀ (s k : Mode), s ∈ S → k ∈ Ks →
      split (cre m 0 (creOf m (g s) (annOf m (f (s - k)) (annOf m (f k) x))))
        = monoOp 0 1 ((creOfE (g s)) ∘ₗ (annOfE (f (s - k))) ∘ₗ (annOfE (f k))) (split x) := by
    intro s k hs hk
    rw [split_cre_zero, split_creOf (g s) (hg s hs), split_annOf (f (s - k)) (hf (s - k)),
      split_annOf (f k) (hf k), lift_lift, lift_lift, LinearMap.comp_assoc, monoOp_zero_one]
    rfl
  -- transport the right-hand side into the double sum of monomials,
  -- with the lattice weights converted to complex scalars.
  simp only [monoOp_sum, monoOp_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Complex.coe_smul]
  -- and the left-hand side likewise, using `hstep` term by term.
  rw [map_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [split_map_smul]
  simp only [LinearMap.comp_apply]
  rw [hstep s k hs hk]
  rfl

end Work.BoseBoxFock
