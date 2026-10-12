import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.lowBandChiAuxAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.FRK.oneFrame_le_excitedSum` — the singleton Bessel bound against `n₊`

For a weight vector `w` with `w 0 = 0` (i.e. the superposed one-particle function
`η_w = Σ_l w_l e_l` is orthogonal to the condensate mode `e 0`), the superposed box annihilation
`a_w = boxAnnOf e w d` satisfies the *sharp* Bessel bound

    ‖a_w Ψ‖² ≤ (Σ_l w_l²) · ⟪Ψ, n₊ Ψ⟫ ,

where `n₊ = boxSlotSum e (boxT0 m)` is the first-quantised excited number.  Equivalently, the
one-element frame `f k = w` (a "singleton frame") satisfies the χ-frame Bessel inequality
`Work.BoseBoxFock.PotCubicLowBandAux.frameSum_le_excitedSum`: the only frame-theoretic input is
the elementary Cauchy–Schwarz bound `(Σ_l w_l v_l)² ≤ (Σ_l w_l²)(Σ_l v_l²)` for the constant
`C_B = Σ_l w_l²`, and the right-hand side is rewritten into `(Σ w_l²)·⟪Ψ, n₊Ψ⟫` by the
self-pairing identity `cIPn_boxSlotSum_boxT0_selfPair`.
-/

namespace Work.BoseBoxFock.FRK

open scoped BigOperators

set_option autoImplicit false

theorem oneFrame_le_excitedSum {m d : ℕ} [NeZero m] {ℓ : ℝ}
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hMemLp : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (w : Fin m → ℝ) (hw : w 0 = 0)
    {Ψ : Work.BoseDict.Xn (d + 1) → ℂ} (hΨm : Measurable Ψ) {CΨ : ℝ}
    (hΨb : ∀ x, ‖Ψ x‖ ≤ CΨ)
    (hΨsupp : Function.support Ψ ⊆ Work.MB.boxPow (d + 1) ℓ)
    (hΨsym : ∀ (σ : Equiv.Perm (Fin (d + 1))) (x : Work.BoseDict.Xn (d + 1)),
      Ψ (x ∘ σ) = Ψ x) :
    (Work.BoseDict.cIPn d (Work.BoseDict.boxAnnOf e w d Ψ)
        (Work.BoseDict.boxAnnOf e w d Ψ)).re
      ≤ (∑ l : Fin m, (w l) ^ 2)
        * (Work.BoseDict.cIPn (d + 1) Ψ
            (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Ψ)).re := by
  classical
  -- the nonnegativity of the frame constant `C_B = ‖w‖²`
  have hCB : 0 ≤ ∑ l : Fin m, (w l) ^ 2 := Finset.sum_nonneg fun l _ => sq_nonneg _
  -- the elementary Cauchy–Schwarz bound `(⟪w, v⟫)² ≤ ‖w‖² ‖v‖²`
  have hcs : ∀ v : Fin m → ℝ,
      (Work.BoseB4.gram w v) ^ 2 ≤ (∑ l : Fin m, (w l) ^ 2) * ∑ l : Fin m, (v l) ^ 2 := by
    intro v
    rw [Work.BoseB4.gram]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ w v
  -- hence the frame bound for the one-element frame `f k = w`
  have hframe : ∀ v : Fin m → ℝ,
      ∑ k : Fin 1, (Work.BoseB4.gram ((fun _ : Fin 1 => w) k) v) ^ 2
        ≤ (∑ l : Fin m, (w l) ^ 2) * ∑ l : Fin m, (v l) ^ 2 := by
    intro v
    rw [Fin.sum_univ_one]
    exact hcs v
  -- the χ-frame Bessel inequality at the one-element frame `f k = w`
  have hbessel := Work.BoseBoxFock.PotCubicLowBandAux.frameSum_le_excitedSum (d := d)
    (e := e) (ι := Fin 1) hmeas hbdd hsupp horth hMemLp (fun _ : Fin 1 => w)
    (∑ l : Fin m, (w l) ^ 2) hCB hframe (fun _ => hw) hΨm hΨb hΨsupp hΨsym
  -- the self-pairing identity converts the RHS into the excited number
  have hself : (∑ l ∈ Finset.univ.erase (0 : Fin m),
        (Work.BoseDict.cIPn d (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) d Ψ)
          (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) d Ψ)).re)
      = (Work.BoseDict.cIPn (d + 1) Ψ
          (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Ψ)).re :=
    (Work.BoseBoxFock.PotCubicLowBandAux.cIPn_boxSlotSum_boxT0_selfPair (d := d)
      hmeas hbdd hsupp hMemLp hΨm hΨb hΨsupp hΨsym).symm
  rw [hself] at hbessel
  calc (Work.BoseDict.cIPn d (Work.BoseDict.boxAnnOf e w d Ψ)
        (Work.BoseDict.boxAnnOf e w d Ψ)).re
      = ∑ k : Fin 1, (Work.BoseDict.cIPn d
            (Work.BoseDict.boxAnnOf e ((fun _ : Fin 1 => w) k) d Ψ)
            (Work.BoseDict.boxAnnOf e ((fun _ : Fin 1 => w) k) d Ψ)).re := by
          rw [Fin.sum_univ_one]
    _ ≤ (∑ l : Fin m, (w l) ^ 2)
        * (Work.BoseDict.cIPn (d + 1) Ψ
            (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Ψ)).re := hbessel

end Work.BoseBoxFock.FRK
