import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.FRK.cubicZeroDefs
import Submission.Work.BoseBoxFock.FRK.oneFrame_le_excitedSum
import Submission.Work.BoseBoxFock.FRK.pairSumExcited_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.FRK.zeroCellSX_le` — the `X`-row of the `k = 0` cell

The `k = 0` lattice cell of FS's cubic row is the off-diagonal word
`ℓ⁻³Ŵ₁(0)·Σ_s f_L(s)·a₀†ã_s†a(q₀)a(q_s) + h.c.`; its size is controlled by
Cauchy–Schwarz against the **excited number** `n₊`, and the quantum part of the estimate is the
`X`-row of `PotCubicZeroCell`:

    Σ_{s ≠ 0} ‖a(η_{f s}) a(η_{f 0}) Θ‖²  ≤  C_B² · ⟪Θ, n₊(n₊Θ)⟫ ,

for a frame family `{f s}` with Bessel constant `C_B` (`Σ_k ⟪f k, w⟫² ≤ C_B‖w‖²`) whose members
are orthogonal to the condensate mode (`f k 0 = 0`).

## Route

Write `Ψ := a(f 0) Θ` (a symmetric state on `Xn (d+1)`).

1. `Σ_{s ∈ excited} ‖a_s Ψ‖² ≤ Σ_{k : Mode} ‖a_k Ψ‖²` (dropping the nonnegative `k = 0` term;
   `cIPn X X` is an `L²`-norm squared, hence `≥ 0`).
2. **Bessel row** (`frameSum_le_excitedSum`): `Σ_k ‖a_k Ψ‖² ≤ C_B·Σ_{l ≠ 0} ‖a_{e_l} Ψ‖²`.
3. **Self-pairing** (`cIPn_boxSlotSum_boxT0_selfPair`): `Σ_{l ≠ 0}‖a_{e_l}Ψ‖² = ⟪Ψ, n₊Ψ⟫`.
4. **Commutation** (`boxAnnOf_boxAnnOf_comm`): `a_{e_l}a_{f 0}Θ = a_{f 0}a_{e_l}Θ` (uses the
   symmetry of `Θ`).
5. **Singleton Bessel** (`FRK.oneFrame_le_excitedSum`): applied to each `Ξ_l := a_{e_l}Θ`,
   `‖a_{f 0}Ξ_l‖² ≤ ‖f 0‖²·⟪Ξ_l, n₊Ξ_l⟫` — this is the sharp `n₊`-bound (the crude bound would
   carry a factor `‖n₊‖` and is *false* as a form estimate; see the FINDING of the FRK chapter).
6. **Self-pairing again**, and the **second excited moment** (`FRK.pairSumExcited_le`, the
   `private` `pairSumExcited` of the low-band chapter made public):
   `Σ_{l,l' ≠ 0}‖a_{l'}a_lΘ‖² ≤ ⟪Θ, n₊(n₊Θ)⟫`.
7. `‖f 0‖² = Σ_l (f 0 l)² ≤ C_B`, from the frame bound at `w = f 0`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock.FRK

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-! ## 0. Elementary nonnegativity -/

/-- `cIPn` of a function with itself is an `L²`-norm squared, hence has nonnegative real part. -/
private theorem cIPn_self_nonneg {n : ℕ} (X : Work.BoseDict.Xn n → ℂ) :
    0 ≤ (Work.BoseDict.cIPn n X X).re := by
  rw [Work.BoseBoxFock.cIPn_self_re]
  exact MeasureTheory.integral_nonneg fun y => by positivity

/-! ## 1. The scalar bound `‖f 0‖² ≤ C_B` -/

private theorem gram_f_zero_le {m : ℕ} [NeZero m] {Mode : Type*} [AddCommGroup Mode]
    [Fintype Mode] [DecidableEq Mode] (f : Mode → Fin m → ℝ) (C_B : ℝ) (hC_B : 0 ≤ C_B)
    (hframe : ∀ w : Fin m → ℝ,
      ∑ k : Mode, (Work.BoseB4.gram (f k) w) ^ 2 ≤ C_B * ∑ l : Fin m, (w l) ^ 2) :
    (∑ l : Fin m, (f 0 l) ^ 2) ≤ C_B := by
  have hgram : Work.BoseB4.gram (f 0) (f 0) = ∑ l : Fin m, (f 0 l) ^ 2 := by
    rw [Work.BoseB4.gram]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hle : (Work.BoseB4.gram (f 0) (f 0)) ^ 2
      ≤ ∑ k : Mode, (Work.BoseB4.gram (f k) (f 0)) ^ 2 :=
    Finset.single_le_sum (f := fun k : Mode => (Work.BoseB4.gram (f k) (f 0)) ^ 2)
      (fun k _ => by positivity) (Finset.mem_univ (0 : Mode))
  have hfr := hframe (f 0)
  rw [hgram] at hle
  set c : ℝ := ∑ l : Fin m, (f 0 l) ^ 2 with hc
  have hcpos : 0 ≤ c := by rw [hc]; positivity
  rcases eq_or_lt_of_le hcpos with h | h
  · rw [← h]; exact hC_B
  · have hmul : c * c ≤ C_B * c := by simpa [pow_two] using le_trans hle hfr
    exact le_of_mul_le_mul_right hmul h

/-! ## 3. The target -/

theorem zeroCellSX_le {m d : ℕ} [NeZero m] {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] {ℓ : ℝ} {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hMemLp : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (f : Mode → Fin m → ℝ) (C_B : ℝ) (hC_B : 0 ≤ C_B)
    (hframe : ∀ w : Fin m → ℝ,
      ∑ k : Mode, (Work.BoseB4.gram (f k) w) ^ 2 ≤ C_B * ∑ l : Fin m, (w l) ^ 2)
    (h0 : ∀ k : Mode, f k 0 = 0)
    {Θ : Work.BoseDict.Xn (d + 2) → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘsupp : Function.support Θ ⊆ Work.MB.boxPow (d + 2) ℓ)
    (hΘsym : ∀ (σ : Equiv.Perm (Fin (d + 2))) (x : Work.BoseDict.Xn (d + 2)),
      Θ (x ∘ σ) = Θ x) :
    (∑ s ∈ Work.BoseB7.excited Mode,
        (Work.BoseDict.cIPn d
          (Work.BoseDict.boxAnnOf e (f s) d (Work.BoseDict.boxAnnOf e (f 0) (d + 1) Θ))
          (Work.BoseDict.boxAnnOf e (f s) d
            (Work.BoseDict.boxAnnOf e (f 0) (d + 1) Θ))).re)
      ≤ C_B ^ 2 * (Work.BoseDict.cIPn (d + 2) Θ
          (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m)
            (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ))).re := by
  classical
  obtain ⟨CΘ, hCΘ⟩ := hΘb
  -- ### the state `Ψ = a(f 0) Θ` on `Xn (d+1)`
  have hWΨ : Work.BoseBoxFock.WRegG ℓ
      (Work.BoseDict.boxAnnOf e (f 0) (d + 1) Θ) :=
    Work.BoseBoxFock.boxAnnOf_wregG hmeas hbdd hsupp (f 0) ⟨hΘm, ⟨CΘ, hCΘ⟩, hΘsupp⟩
  obtain ⟨CΨ, hCΨ⟩ := hWΨ.bdd
  have hΨsym : ∀ (σ : Equiv.Perm (Fin (d + 1))) (x : Work.BoseDict.Xn (d + 1)),
      Work.BoseDict.boxAnnOf e (f 0) (d + 1) Θ (x ∘ σ)
        = Work.BoseDict.boxAnnOf e (f 0) (d + 1) Θ x :=
    Work.BoseBoxFock.boxAnnOf_symm (f 0) Θ hΘsym
  -- ### step 1: drop the `k = 0` term
  have hstep1 : (∑ s ∈ Work.BoseB7.excited Mode,
        (Work.BoseDict.cIPn d
          (Work.BoseDict.boxAnnOf e (f s) d (Work.BoseDict.boxAnnOf e (f 0) (d + 1) Θ))
          (Work.BoseDict.boxAnnOf e (f s) d
            (Work.BoseDict.boxAnnOf e (f 0) (d + 1) Θ))).re)
      ≤ ∑ k : Mode, (Work.BoseDict.cIPn d
          (Work.BoseDict.boxAnnOf e (f k) d (Work.BoseDict.boxAnnOf e (f 0) (d + 1) Θ))
          (Work.BoseDict.boxAnnOf e (f k) d
            (Work.BoseDict.boxAnnOf e (f 0) (d + 1) Θ))).re :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun k _ => Finset.mem_univ k)
      (fun k _ _ => cIPn_self_nonneg _)
  -- ### step 2: the Bessel row at the state `Ψ`
  have hstep2 : (∑ k : Mode, (Work.BoseDict.cIPn d
          (Work.BoseDict.boxAnnOf e (f k) d (Work.BoseDict.boxAnnOf e (f 0) (d + 1) Θ))
          (Work.BoseDict.boxAnnOf e (f k) d
            (Work.BoseDict.boxAnnOf e (f 0) (d + 1) Θ))).re)
      ≤ C_B * ∑ l ∈ Finset.univ.erase (0 : Fin m),
          (Work.BoseDict.cIPn d
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) d
              (Work.BoseDict.boxAnnOf e (f 0) (d + 1) Θ))
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) d
              (Work.BoseDict.boxAnnOf e (f 0) (d + 1) Θ))).re :=
    Work.BoseBoxFock.PotCubicLowBandAux.frameSum_le_excitedSum (d := d)
      (Ψ := Work.BoseDict.boxAnnOf e (f 0) (d + 1) Θ)
      hmeas hbdd hsupp horth hMemLp f C_B hC_B hframe h0 hWΨ.meas hCΨ hWΨ.supp hΨsym
  -- ### step 3: the self-pairing identity `Σ_{l ≠ 0}‖a_{e_l}Ψ‖² = ⟪Ψ, n₊Ψ⟫`
  have hstep3 : (Work.BoseDict.cIPn (d + 1) (Work.BoseDict.boxAnnOf e (f 0) (d + 1) Θ)
          (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m)
            (Work.BoseDict.boxAnnOf e (f 0) (d + 1) Θ))).re
      = ∑ l ∈ Finset.univ.erase (0 : Fin m),
          (Work.BoseDict.cIPn d
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) d
              (Work.BoseDict.boxAnnOf e (f 0) (d + 1) Θ))
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) d
              (Work.BoseDict.boxAnnOf e (f 0) (d + 1) Θ))).re :=
    Work.BoseBoxFock.PotCubicLowBandAux.cIPn_boxSlotSum_boxT0_selfPair (d := d)
      hmeas hbdd hsupp hMemLp hWΨ.meas hCΨ hWΨ.supp hΨsym
  -- ### step 4: commute the two annihilations
  have hcomm : ∀ l : Fin m,
      Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) d
          (Work.BoseDict.boxAnnOf e (f 0) (d + 1) Θ)
        = Work.BoseDict.boxAnnOf e (f 0) d
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (d + 1) Θ) :=
    fun l => Work.BoseBoxFock.PotCubicLowBandAux.boxAnnOf_boxAnnOf_comm hmeas hbdd hsupp
      (Work.BoseB4.evec m l) (f 0) hΘm ⟨CΘ, hCΘ⟩ hΘsupp hΘsym
  have hstep4 : (Work.BoseDict.cIPn (d + 1) (Work.BoseDict.boxAnnOf e (f 0) (d + 1) Θ)
          (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m)
            (Work.BoseDict.boxAnnOf e (f 0) (d + 1) Θ))).re
      = ∑ l ∈ Finset.univ.erase (0 : Fin m),
          (Work.BoseDict.cIPn d
            (Work.BoseDict.boxAnnOf e (f 0) d
              (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (d + 1) Θ))
            (Work.BoseDict.boxAnnOf e (f 0) d
              (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (d + 1) Θ))).re := by
    rw [hstep3]
    exact Finset.sum_congr rfl fun l _ => by rw [hcomm l]
  -- ### step 5: the singleton Bessel bound at each `Ξ_l = a_{e_l}Θ`
  have hstep5 : ∀ l : Fin m,
      (Work.BoseDict.cIPn d
          (Work.BoseDict.boxAnnOf e (f 0) d
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (d + 1) Θ))
          (Work.BoseDict.boxAnnOf e (f 0) d
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (d + 1) Θ))).re
      ≤ (∑ l' : Fin m, (f 0 l') ^ 2)
        * (Work.BoseDict.cIPn (d + 1)
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (d + 1) Θ)
            (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m)
              (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (d + 1) Θ))).re := by
    intro l
    have hW : Work.BoseBoxFock.WRegG ℓ
        (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (d + 1) Θ) :=
      Work.BoseBoxFock.boxAnnOf_wregG hmeas hbdd hsupp _ ⟨hΘm, ⟨CΘ, hCΘ⟩, hΘsupp⟩
    obtain ⟨CΞ, hCΞ⟩ := hW.bdd
    exact oneFrame_le_excitedSum hmeas hbdd hsupp horth hMemLp (f 0) (h0 0)
      hW.meas hCΞ hW.supp (Work.BoseBoxFock.boxAnnOf_symm (Work.BoseB4.evec m l) Θ hΘsym)
  -- ### step 6: the self-pairing identity at each `Ξ_l`
  have hstep6 : ∀ l : Fin m,
      (Work.BoseDict.cIPn (d + 1)
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (d + 1) Θ)
            (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m)
              (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (d + 1) Θ))).re
      = ∑ l' ∈ Finset.univ.erase (0 : Fin m),
          (Work.BoseDict.cIPn d
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l') d
              (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (d + 1) Θ))
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l') d
              (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (d + 1) Θ))).re := by
    intro l
    have hW : Work.BoseBoxFock.WRegG ℓ
        (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (d + 1) Θ) :=
      Work.BoseBoxFock.boxAnnOf_wregG hmeas hbdd hsupp _ ⟨hΘm, ⟨CΘ, hCΘ⟩, hΘsupp⟩
    obtain ⟨CΞ, hCΞ⟩ := hW.bdd
    exact Work.BoseBoxFock.PotCubicLowBandAux.cIPn_boxSlotSum_boxT0_selfPair (d := d)
      hmeas hbdd hsupp hMemLp hW.meas hCΞ hW.supp
      (Work.BoseBoxFock.boxAnnOf_symm (Work.BoseB4.evec m l) Θ hΘsym)
  -- ### step 7: the second excited moment
  have hstep7 : (∑ l ∈ Finset.univ.erase (0 : Fin m), ∑ l' ∈ Finset.univ.erase (0 : Fin m),
        (Work.BoseDict.cIPn d
          (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l') d
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (d + 1) Θ))
          (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l') d
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (d + 1) Θ))).re)
      ≤ (Work.BoseDict.cIPn (d + 2) Θ
          (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m)
            (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ))).re :=
    pairSumExcited_le hmeas hbdd hsupp horth hMemLp hΘm ⟨CΘ, hCΘ⟩ hΘsupp hΘsym
  -- ### the scalar bound
  have hc0 : (∑ l : Fin m, (f 0 l) ^ 2) ≤ C_B := gram_f_zero_le f C_B hC_B hframe
  have hXnn : 0 ≤ (Work.BoseDict.cIPn (d + 2) Θ
      (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m)
        (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ))).re :=
    le_trans (Finset.sum_nonneg fun l _ =>
      Finset.sum_nonneg fun l' _ => cIPn_self_nonneg _) hstep7
  -- ### assembly
  calc (∑ s ∈ Work.BoseB7.excited Mode,
        (Work.BoseDict.cIPn d
          (Work.BoseDict.boxAnnOf e (f s) d (Work.BoseDict.boxAnnOf e (f 0) (d + 1) Θ))
          (Work.BoseDict.boxAnnOf e (f s) d
            (Work.BoseDict.boxAnnOf e (f 0) (d + 1) Θ))).re)
      ≤ ∑ k : Mode, (Work.BoseDict.cIPn d
          (Work.BoseDict.boxAnnOf e (f k) d (Work.BoseDict.boxAnnOf e (f 0) (d + 1) Θ))
          (Work.BoseDict.boxAnnOf e (f k) d
            (Work.BoseDict.boxAnnOf e (f 0) (d + 1) Θ))).re := hstep1
    _ ≤ C_B * ∑ l ∈ Finset.univ.erase (0 : Fin m),
          (Work.BoseDict.cIPn d
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) d
              (Work.BoseDict.boxAnnOf e (f 0) (d + 1) Θ))
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) d
              (Work.BoseDict.boxAnnOf e (f 0) (d + 1) Θ))).re := hstep2
    _ = C_B * (Work.BoseDict.cIPn (d + 1) (Work.BoseDict.boxAnnOf e (f 0) (d + 1) Θ)
          (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m)
            (Work.BoseDict.boxAnnOf e (f 0) (d + 1) Θ))).re := by rw [← hstep3]
    _ = C_B * ∑ l ∈ Finset.univ.erase (0 : Fin m),
          (Work.BoseDict.cIPn d
            (Work.BoseDict.boxAnnOf e (f 0) d
              (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (d + 1) Θ))
            (Work.BoseDict.boxAnnOf e (f 0) d
              (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (d + 1) Θ))).re := by
        rw [hstep4]
    _ ≤ C_B * ∑ l ∈ Finset.univ.erase (0 : Fin m),
          (∑ l' : Fin m, (f 0 l') ^ 2)
            * (Work.BoseDict.cIPn (d + 1)
                (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (d + 1) Θ)
                (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m)
                  (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (d + 1) Θ))).re :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ => hstep5 l) hC_B
    _ = C_B * ((∑ l' : Fin m, (f 0 l') ^ 2)
          * ∑ l ∈ Finset.univ.erase (0 : Fin m),
            (Work.BoseDict.cIPn (d + 1)
                (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (d + 1) Θ)
                (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m)
                  (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (d + 1) Θ))).re) := by
        congr 1
        rw [Finset.mul_sum]
    _ = C_B * ((∑ l' : Fin m, (f 0 l') ^ 2)
          * ∑ l ∈ Finset.univ.erase (0 : Fin m), ∑ l' ∈ Finset.univ.erase (0 : Fin m),
            (Work.BoseDict.cIPn d
              (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l') d
                (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (d + 1) Θ))
              (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l') d
                (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (d + 1) Θ))).re) := by
        have hsum6 : (∑ l ∈ Finset.univ.erase (0 : Fin m),
              (Work.BoseDict.cIPn (d + 1)
                (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (d + 1) Θ)
                (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m)
                  (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (d + 1) Θ))).re)
            = ∑ l ∈ Finset.univ.erase (0 : Fin m), ∑ l' ∈ Finset.univ.erase (0 : Fin m),
                (Work.BoseDict.cIPn d
                  (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l') d
                    (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (d + 1) Θ))
                  (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l') d
                    (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (d + 1) Θ))).re :=
          Finset.sum_congr rfl (fun l _ => hstep6 l)
        rw [hsum6]
    _ ≤ C_B * ((∑ l' : Fin m, (f 0 l') ^ 2)
          * (Work.BoseDict.cIPn (d + 2) Θ
              (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m)
                (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ))).re) := by
        refine mul_le_mul_of_nonneg_left ?_ hC_B
        refine mul_le_mul_of_nonneg_left hstep7 ?_
        positivity
    _ ≤ C_B ^ 2 * (Work.BoseDict.cIPn (d + 2) Θ
          (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m)
            (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ))).re := by
        have h1 : C_B * (∑ l' : Fin m, (f 0 l') ^ 2) ≤ C_B * C_B :=
          mul_le_mul_of_nonneg_left hc0 hC_B
        calc C_B * ((∑ l' : Fin m, (f 0 l') ^ 2)
              * (Work.BoseDict.cIPn (d + 2) Θ
                  (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m)
                    (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ))).re)
            = (C_B * (∑ l' : Fin m, (f 0 l') ^ 2))
                * (Work.BoseDict.cIPn (d + 2) Θ
                    (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m)
                      (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ))).re := by
              ring
          _ ≤ (C_B * C_B) * (Work.BoseDict.cIPn (d + 2) Θ
                  (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m)
                    (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ))).re :=
              mul_le_mul_of_nonneg_right h1 hXnn
          _ = C_B ^ 2 * (Work.BoseDict.cIPn (d + 2) Θ
                  (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m)
                    (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ))).re := by
              ring

end Work.BoseBoxFock.FRK
