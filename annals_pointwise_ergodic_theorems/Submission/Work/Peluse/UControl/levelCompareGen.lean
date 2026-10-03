import Mathlib
import Submission.Work.Peluse.UControl.levelCompareGenHolds

/-!
# The terminal comparison of the level chain (`d ≥ 3`)

`level1Compare` handles the `d = 2` case: the `Phase1Terminal` state *is* the level-`1` datum, and one
compares the state's correlation `lam` with `linFamAvg (levelOneDatum n)`.  For `d ≥ 3` the terminal
state of the level chain is a `LevCube`-state of degree `1` whose slots are the punctured cube of an
arbitrary datum `D`'s last level, and the comparison has to be stated for that datum:

* `towerIdx` reindexes the window tower `Fin (2H+1) × WinTower H L` onto the datum's parameter box
  (`htower0`: the level-`0` coordinate is the window position; `htower_indep`: the level-`0`
  coordinate does not influence the higher levels; `htower_mem`, `htower_surj`, `htower_inj`);
* `islot` is the bijection between the live slots of `Y` and `D.I (dd-1)`;
* `heval` is the identification of the slot polynomial evaluated at a tower point with the datum's
  direction `petDir D dd lc` times `y` plus a constant `β`.

The conclusion is the transfer of the correlation `lam` to `linFamAvg`, losing only `3 ^ L` (the
ratio of the uniform box weight `(2H+1)⁻¹` to the window weight `μ_H ≤ H⁻¹`), **plus** the shift
clause for the *explicit* constant `β' a i = β a (islot.symm i)`, which the consumer feeds into
Peluse's Proposition 3.4.  (`levelNCompare` states the first half; the shift clause is added here,
because it must be asserted for the *same* `β'`.)

This is the `d ≥ 3` generalisation of `level1Compare_aux` (`level1Compare.lean`): the only new inputs
are `htower_inj` (for `sum_parBox_ge`), `hcard` (the cardinality of the parameter box, which is
`(2H+1)^{L+1}` for the concrete level chain) and the two `β`-invariance facts.
-/

set_option autoImplicit false
open scoped BigOperators
open Polynomial

namespace Work.Peluse.UControl

noncomputable section

attribute [local instance] Classical.propDecidable

/-- **The terminal comparison of the level chain.**  See the module docstring. -/
theorem levelCompareGen {dd L : ℕ} (hdd : 0 < dd) (H : ℕ)
    (D : Work.Peluse.UControl.IdxDatum) (lc : ℤ)
    (A : Finset (Fin L)) (f₀ : Fin L → Bool)
    (atoms : {x : Fin L // x ∈ A} → MvPolynomial (Fin L) ℤ)
    (Y : Work.Peluse.UControl.HistData dd L)
    (hY : Work.Peluse.UControl.LevCube dd 1 L A f₀ atoms Y)
    (towerIdx : Fin (2 * H + 1) × Work.Peluse.UControl.WinTower H L →
      ((j : Fin dd) → D.S j → ℤ))
    (htower0 : ∀ p : Fin (2 * H + 1) × Work.Peluse.UControl.WinTower H L,
      towerIdx p ⟨0, hdd⟩ = fun _ => Work.Peluse.UControl.IdxDatum.boxVal H p.1)
    (htower_indep : ∀ (k k' : Fin (2 * H + 1)) (t : Work.Peluse.UControl.WinTower H L),
      ∀ j : Fin dd, j ≠ ⟨0, hdd⟩ → towerIdx (k, t) j = towerIdx (k', t) j)
    (htower_mem : ∀ p : Fin (2 * H + 1) × Work.Peluse.UControl.WinTower H L,
      towerIdx p ∈ D.parBox dd H)
    (htower_surj : ∀ a ∈ D.parBox dd H, ∃ p : Fin (2 * H + 1) ×
      Work.Peluse.UControl.WinTower H L, towerIdx p = a)
    (htower_inj : Function.Injective towerIdx)
    (hcard : (D.parBox dd H).card ≤ (2 * H + 1) ^ (L + 1))
    (N M : ℕ) (Ftop : ℤ → ℂ) (G : (Y.toSym).S.ι → ℤ → ℂ)
    (g : Work.Peluse.UControl.WinTower H L → ℤ → ℂ)
    (htop : ∀ i : (Y.toSym).S.ι, (∀ x, G i x = Ftop x) ∨ (∀ x, G i x = star (Ftop x)))
    (hg : ∃ c₀ : Bool, ∀ a x, g a x = (if c₀ then star (Ftop x) else Ftop x))
    (islot : (Y.toSym).S.ι ≃ Fin (Fintype.card (D.I (dd - 1))))
    (β : ((j : Fin dd) → D.S j → ℤ) → (Y.toSym).S.ι → ℤ)
    (hβ0 : ∀ a a' : (j : Fin dd) → D.S j → ℤ,
      (∀ (j : Fin dd), j ≠ ⟨0, hdd⟩ → a j = a' j) → ∀ i : (Y.toSym).S.ι, β a i = β a' i)
    (heval : ∀ (i : (Y.toSym).S.ι) (t : Work.Peluse.UControl.WinTower H L) (y : ℤ),
      ((Polynomial.map (MvPolynomial.eval (Work.Peluse.UControl.WinTower.param H L t))
          (Y.Q i.1.1 i.1.2)).eval y)
        = Work.Peluse.UControl.petDir D dd lc (towerIdx (0, t)) (islot i) * y
            + β (towerIdx (0, t)) i)
    {c Dsb : ℕ} (hSB : (Work.Peluse.UControl.histPet Y H G g).toState.ShiftBound N M c Dsb)
    (hc : 1 ≤ c) {B : ℝ}
    (hlam : B ≤ (Work.Peluse.UControl.histPet Y H G g).toState.lam N M) :
    ∃ b : Fin (Fintype.card (D.I (dd - 1))) → Bool,
      (∀ a ∈ D.parBox dd H, ∀ i : Fin (Fintype.card (D.I (dd - 1))),
          ∀ y ∈ Finset.Icc 1 M,
        |Work.Peluse.UControl.petDir D dd lc a i * (y : ℤ) + β a (islot.symm i)|
          ≤ (Dsb : ℤ) * (N : ℤ)) ∧
      B ≤ (3 : ℝ) ^ L * Work.Peluse.UControl.linFamAvg D dd lc N M H Ftop b
        (fun a i => β a (islot.symm i)) :=
  levelCompareGenHolds hdd H D lc A f₀ atoms Y hY towerIdx htower0 htower_indep htower_mem
    htower_surj htower_inj hcard N M Ftop G g htop hg islot β hβ0 heval hSB hc hlam

end

end Work.Peluse.UControl
