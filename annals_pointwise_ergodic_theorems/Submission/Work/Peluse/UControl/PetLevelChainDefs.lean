import Mathlib
import Submission.Work.Peluse.UControl.HistInv
import Submission.Work.Peluse.UControl.peluseProp34Defs2

/-!
# The level chain of the PET chapter (the remaining gap of `PetChapter5`)

`petChapter5_quadratic` proves `PetChapter5 P` for `P.natDegree = 2`.  For `d = P.natDegree ≥ 3`
the phase-1 chain plus the closing step only produces a state whose slots are the level-`1` datum
(the nonempty subsets of `Fin n`, of degree `d - 1`); the remaining `d - 2` levels are Peluse's
Lemma 4.8 iterated, followed by the final comparison with `linFamAvg D d c`.

`PetLevelChain P` isolates exactly that remaining piece: **from a `Phase1Terminal` state with a
correlation lower bound `B`, produce a number `Nstep ≥ 1` of PET steps, the level-`(d-1)` datum `D`
and a constant `C₀` (all functions of the terminal state, hence of `P` alone) such that for every
admissible configuration satisfying the chain's window condition, the average along the
level-`(d-1)` linear configuration dominates `petChainLevel B Nstep`.**

## Why `Nstep` is *produced* and why the window is tied to it

Earlier versions of this statement either
* quantified `∀ Nmax` and returned `Nstep ≤ Nmax` (so that the instance `Nmax = 0` makes the window
  hypothesis vacuous, forces `Nstep = 0` and demands the *lossless* comparison
  `B ≤ C₀ · linFamAvg`), or
* omitted the window condition altogether (so that the *shift clause* becomes unsatisfiable for a
  large window: `ShiftBound` bounds the *values* of the terminal slot polynomials while `petDir` is
  built from their *leading coefficients*, cf. `NOTES_petLevelChain_REFUTATION.md`).

Here `Nstep` is produced *by the statement* and the window condition

  `hwin : ∀ k < Nstep, γ' ≤ petChainLevel B k ^ 2 / (20000 * (2^k * Dsb + 1))`

is tied to it.  This is exactly `HistInv`'s `hw` field, so it is the hypothesis under which the
analytic chain actually runs (`HistInv.hw` + `HistInv.hc : histLen + 1 ≤ c`, which is the
hypothesis `Nstep + 1 ≤ c` below).  Choosing `Nstep` too small only makes the conclusion
`petChainLevel B Nstep ≤ C₀ · linFamAvg` *stronger* (`petChainLevel B k` decreases in `k` for
`B ≤ 1`) and the window hypothesis weaker, so a proof cannot cheat by shrinking `Nstep`.

Everything else in `PetChapter5` (the phase-1 chain, the closing step, the corner, and the window
bookkeeping of `NOTES_petChapter5_session16.md`) is already formalised:
`petHistInit_inv`, `histPhase1RunInv`, `histPhase1Inv`, `histCloseLinkWin`, `level1Compare`,
`linFamAvg_radius_le`, `petWindowBookkeeping`, `petCornerZero`; see `petChapter5_quadratic` for the
`d = 2` instance of the assembly.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

/-- **The level chain.**  For every `Phase1Terminal` state `Y` (degree `d-1`, slots the nonempty
Boolean histories) there are a number `Nstep ≥ 1` of PET steps, the level-`(d-1)` datum `D` — whose
slot set is the terminal slot set of the iterated Lemma 4.8 — and a constant `C₀`, such that for
every admissible configuration satisfying the chain's window condition the average along the
level-`(d-1)` linear configuration with the datum's directions dominates
`petChainLevel B Nstep`.  The shift constant of the conclusion is `2 ^ Nstep * Dsb`: each PET step
halves the range and doubles the constant (`PetState.ShiftBound.step`).

The data carry the *paper's standing hypotheses* on the slot and base functions — the bound
`‖·‖ ≤ 1`, the support `SupportIn · Nx` and the non-degeneracy `1 ≤ Nx` — exactly as `HistInv` (the
phase-1 invariant whose `hc`/`hw` fields are the two window hypotheses below) carries `hFb`, `hFs`,
`hfb`, `hfs`, `hN`.  They are not cosmetic: Peluse's Lemma 4.2 (`PET.pet_step`, the engine of one
PET step) is proved with them, and its van der Corput step needs the size `≪ Nx` of the support,
while its Cauchy–Schwarz step is *not* scale invariant (the gain `γ²/2000` is one power of `γ` while
a product of `k` slot functions scales by `λ^k`).

For `P.natDegree = 2` this is `level1Compare` with `Nstep = 1`, `D = levelOneDatum n`,
`C₀ = 3^n` (the lossless comparison is upgraded to `petChainLevel B 1 = B^2/2000` using `B ≤ 1`). -/
def PetLevelChain (P : Polynomial ℤ) : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (lc : ℤ) (Y : HistData P.natDegree n),
    Phase1Terminal P.natDegree n lc Y →
    ∃ (Nstep : ℕ) (D : IdxDatum) (C₀ : ℝ),
      1 ≤ Nstep ∧ 1 ≤ C₀ ∧ 2 ≤ Fintype.card (D.I (P.natDegree - 1)) ∧
      ∀ (Nx M : ℕ) (γ' : ℝ) (Ftop : ℤ → ℂ)
        (G : (Y.toSym).S.ι → ℤ → ℂ)
        (g : WinTower ⌊γ' * (M : ℝ)⌋.toNat n → ℤ → ℂ)
        (c Dsb : ℕ) (B : ℝ),
        1 ≤ Nx →
        (∀ i : (Y.toSym).S.ι, ∀ x : ℤ, ‖G i x‖ ≤ 1) →
        (∀ i : (Y.toSym).S.ι, SupportIn (G i) Nx) →
        (∀ a : WinTower ⌊γ' * (M : ℝ)⌋.toNat n, ∀ x : ℤ, ‖g a x‖ ≤ 1) →
        (∀ a : WinTower ⌊γ' * (M : ℝ)⌋.toNat n, SupportIn (g a) Nx) →
        1 ≤ M → 1 ≤ ⌊γ' * (M : ℝ)⌋.toNat → Nstep + 1 ≤ c → 0 ≤ B → B ≤ 1 →
        (∀ k : ℕ, k < Nstep →
          γ' ≤ petChainLevel B k ^ 2 / (20000 * (((2 ^ k * Dsb : ℕ) : ℝ) + 1))) →
        (histPet Y ⌊γ' * (M : ℝ)⌋.toNat G g).toState.ShiftBound Nx M c Dsb →
        (∀ i, (∀ x, G i x = Ftop x) ∨ (∀ x, G i x = star (Ftop x))) →
        (∃ c₀ : Bool, ∀ a x, g a x = (if c₀ then star (Ftop x) else Ftop x)) →
        B ≤ (histPet Y ⌊γ' * (M : ℝ)⌋.toNat G g).toState.lam Nx M →
        ∃ (b : Fin (Fintype.card (D.I (P.natDegree - 1))) → Bool)
          (β : D.Idx P.natDegree → Fin (Fintype.card (D.I (P.natDegree - 1))) → ℤ),
          (∀ a ∈ D.parBox P.natDegree ⌊γ' * (M : ℝ)⌋.toNat,
              ∀ i : Fin (Fintype.card (D.I (P.natDegree - 1))), ∀ y ∈ Finset.Icc 1 M,
                |petDir D P.natDegree lc a i * (y : ℤ) + β a i|
                  ≤ ((2 ^ Nstep * Dsb : ℕ) : ℤ) * (Nx : ℤ)) ∧
          petChainLevel B Nstep ≤ C₀ * linFamAvg D P.natDegree lc Nx M
            ⌊γ' * (M : ℝ)⌋.toNat Ftop b β

end

end Work.Peluse.UControl
