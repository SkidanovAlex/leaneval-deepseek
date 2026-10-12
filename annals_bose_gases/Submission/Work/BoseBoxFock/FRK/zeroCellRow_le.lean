import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.FRK.cubicZeroDefs
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.lowBandRowSplitAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.FRK.zeroCellRow_le` — the zero-cell (`k = 0`) row of the cubic term

`Work.BoseBoxFock.potCubic B f g PHs E Θ = ℓ⁻³ Σ_{s ∈ excited} Σ_{k ∈ PHs} (f_L s · Ŵ₁ k) •
atom_{s,k} Θ`.  The design `cbc/bose_deadrow_cubicfree.md` §B3 splits the "all `k`" dictionary
(`PHs = univ`) as `potCubic(univ) = potCubic(excited) + potCubic({0})`: the extra summand is the
**zero cell** `k = 0`, which `excited` does *not* contain.  This lemma bounds the row

    F_excited − F_univ = −F_{k=0},     F_L := (∫ star Θ · potCubic … L … Θ).re,

by the Cauchy–Schwarz product of the `f`-side and `g`-side sums of double-annihilation norms,
with the weights `|f_L(s)| · |Ŵ₁(0)|`.

The proof is the `k = 0` instance of the row machinery of
`Work.BoseBoxFock.PotCubicLowBandAux.lowBandRowSplitAux`:

* the split `potCubic(excited) = potCubic(univ) − potCubic({0})` (`potCubic_finset_split` with
  `excited ∪ {0} = univ`), hence (linearity of the Bochner integral, `potCubicIntegrableGen`)
  `F_excited − F_univ = −(∫ star Θ · potCubic({0}) Θ).re`;
* the atom expansion `cIPnAux_expand` at `L = {0}`;
* the per-pair bound `cIPnAux_atomNorm` and the weighted discrete Cauchy–Schwarz
  `cIPnAux_weightedCS`;
* the arithmetic `|Re z| ≤ ‖z‖` and `0 ≤ ℓ⁻³`.

Since the `k`-index set is the singleton `{0}`, the two sums of the target are the collapsed
(`Finset.sum_product` + `Finset.sum_singleton`) versions of the sums over `excited ×ˢ {0}`.
-/

namespace Work.BoseBoxFock.FRK

open MeasureTheory
open scoped BigOperators

set_option linter.unusedVariables false

theorem zeroCellRow_le {m d : ℕ} [NeZero m] {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] {ℓ : ℝ} {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ} (hℓ : 0 < ℓ)
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hMemLp : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (f g : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) (hEℓ : 0 < E.ell)
    {Θ : Work.BoseDict.Xn (d + 2) → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘsupp : Function.support Θ ⊆ Work.MB.boxPow (d + 2) ℓ)
    (hΘsym : ∀ (σ : Equiv.Perm (Fin (d + 2))) (x : Work.BoseDict.Xn (d + 2)),
      Θ (x ∘ σ) = Θ x) :
    (∫ x : Work.BoseDict.Xn (d + 2), star (Θ x) *
        Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g
          (Work.BoseB7.excited Mode) E Θ x).re
      - (∫ x : Work.BoseDict.Xn (d + 2), star (Θ x) *
        Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g
          (Finset.univ : Finset Mode) E Θ x).re
    ≤ 2 * (E.ell ^ (-(3 : ℝ))) *
        Real.sqrt (∑ s ∈ Work.BoseB7.excited Mode,
          |E.fL s| * |E.W1 0| * (Work.BoseDict.cIPn d
            (Work.BoseDict.boxAnnOf e (f s) d
              (Work.BoseDict.boxAnnOf e (f 0) (d + 1) Θ))
            (Work.BoseDict.boxAnnOf e (f s) d
              (Work.BoseDict.boxAnnOf e (f 0) (d + 1) Θ))).re) *
        Real.sqrt (∑ s ∈ Work.BoseB7.excited Mode,
          |E.fL s| * |E.W1 0| * (Work.BoseDict.cIPn d
            (Work.BoseDict.boxAnnOf e (g s) d
              (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))
            (Work.BoseDict.boxAnnOf e (g s) d
              (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))).re) := by
  classical
  -- ## Step 0: local notation for the `k = 0` cell
  let P : Finset (Mode × Mode) := (Work.BoseB7.excited Mode) ×ˢ ({0} : Finset Mode)
  let w : Mode × Mode → ℝ := fun p => E.fL p.1 * E.W1 p.2
  let A : Mode × Mode → ℝ := fun p => (Work.BoseDict.cIPn d
      (Work.BoseDict.boxAnnOf e (f (p.1 - p.2)) d
        (Work.BoseDict.boxAnnOf e (f p.2) (d + 1) Θ))
      (Work.BoseDict.boxAnnOf e (f (p.1 - p.2)) d
        (Work.BoseDict.boxAnnOf e (f p.2) (d + 1) Θ))).re
  let Bq : Mode × Mode → ℝ := fun p => (Work.BoseDict.cIPn d
      (Work.BoseDict.boxAnnOf e (g p.1) d
        (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))
      (Work.BoseDict.boxAnnOf e (g p.1) d
        (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))).re
  let z : Mode × Mode → ℂ := fun p => Work.BoseDict.cIPn (d + 2) Θ
      (Work.BoseBoxFock.FRK.potCubicAtom (fun T => Work.BoseDict.boxSlotSum e T)
        f g p.1 p.2 Θ)
  -- ## Step 1: `excited ∪ {0} = univ`, and the operator split
  have hunion : Work.BoseB7.excited Mode ∪ ({0} : Finset Mode) = Finset.univ := by
    ext x
    constructor
    · intro _; exact Finset.mem_univ x
    · intro _
      rw [Finset.mem_union, Finset.mem_singleton]
      by_cases h : x = 0
      · exact Or.inr h
      · exact Or.inl (by rw [Work.BoseB7.excited, Finset.mem_erase]; exact ⟨h, Finset.mem_univ x⟩)
  have hdis : Disjoint (Work.BoseB7.excited Mode) ({0} : Finset Mode) := by
    rw [Finset.disjoint_left]
    intro x hx hx0
    rw [Finset.mem_singleton] at hx0
    rw [Work.BoseB7.excited, Finset.mem_erase] at hx
    exact hx.1 hx0
  have hsplitfun : ∀ Θ' : Work.BoseDict.Xn (d + 2) → ℂ,
      Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g
          (Work.BoseB7.excited Mode) E Θ'
        = Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g
            (Finset.univ : Finset Mode) E Θ'
          - Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g
            ({0} : Finset Mode) E Θ' := by
    intro Θ'
    have h := Work.BoseBoxFock.potCubic_finset_split (fun T => Work.BoseDict.boxSlotSum e T) f g
      (Work.BoseB7.excited Mode) ({0} : Finset Mode) hdis E Θ'
    rw [hunion] at h
    rw [h]
    ring
  -- ## Step 2: integrability and the integral split
  have hIntExc := Work.BoseBoxFock.PotCubicLowBandAux.potCubicIntegrableGen hmeas hbdd hsupp
    hΘm hΘb hΘsupp f g (Work.BoseB7.excited Mode) E
  have hInt0 := Work.BoseBoxFock.PotCubicLowBandAux.potCubicIntegrableGen hmeas hbdd hsupp
    hΘm hΘb hΘsupp f g ({0} : Finset Mode) E
  have hsplit : ∀ x : Work.BoseDict.Xn (d + 2),
      star (Θ x) * Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g
          (Finset.univ : Finset Mode) E Θ x
        = star (Θ x) * Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g
            (Work.BoseB7.excited Mode) E Θ x
          + star (Θ x) * Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g
            ({0} : Finset Mode) E Θ x := by
    intro x
    have h := hsplitfun Θ
    have h2 := congrFun h x
    rw [Pi.sub_apply] at h2
    rw [h2]
    ring
  have hintEq : (∫ x : Work.BoseDict.Xn (d + 2), star (Θ x) *
        Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g
          (Finset.univ : Finset Mode) E Θ x)
      = (∫ x : Work.BoseDict.Xn (d + 2), star (Θ x) *
          Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g
            (Work.BoseB7.excited Mode) E Θ x)
        + (∫ x : Work.BoseDict.Xn (d + 2), star (Θ x) *
            Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g
              ({0} : Finset Mode) E Θ x) := by
    have hfun : (fun x : Work.BoseDict.Xn (d + 2) => star (Θ x) *
          Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g
            (Finset.univ : Finset Mode) E Θ x)
        = (fun x : Work.BoseDict.Xn (d + 2) => star (Θ x) *
            Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g
              (Work.BoseB7.excited Mode) E Θ x)
          + (fun x : Work.BoseDict.Xn (d + 2) => star (Θ x) *
            Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g
              ({0} : Finset Mode) E Θ x) := by
      funext x
      rw [Pi.add_apply]
      exact hsplit x
    rw [hfun]
    exact MeasureTheory.integral_add hIntExc hInt0
  have hRowEq : (∫ x : Work.BoseDict.Xn (d + 2), star (Θ x) *
        Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g
          (Work.BoseB7.excited Mode) E Θ x).re
      - (∫ x : Work.BoseDict.Xn (d + 2), star (Θ x) *
        Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g
          (Finset.univ : Finset Mode) E Θ x).re
      = -(∫ x : Work.BoseDict.Xn (d + 2), star (Θ x) *
        Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g
          ({0} : Finset Mode) E Θ x).re := by
    rw [hintEq, Complex.add_re]
    ring
  -- ## Step 3: the atom expansion of the `k = 0` row
  have hexp := Work.BoseBoxFock.PotCubicLowBandAux.cIPnAux_expand hmeas hbdd hsupp f g
    ({0} : Finset Mode) E hΘm hΘb hΘsupp
  have hRowEq2 : (∫ x : Work.BoseDict.Xn (d + 2), star (Θ x) *
        Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g
          (Work.BoseB7.excited Mode) E Θ x).re
      - (∫ x : Work.BoseDict.Xn (d + 2), star (Θ x) *
        Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g
          (Finset.univ : Finset Mode) E Θ x).re
      = -(E.ell ^ (-(3 : ℝ)) * (∑ p ∈ P, ((w p : ℝ) : ℂ) * z p).re) := by
    rw [hRowEq, hexp, Complex.re_ofReal_mul]
  -- ## Step 4: the weighted Cauchy–Schwarz
  have hAnnA : ∀ p ∈ P, 0 ≤ A p := by
    intro p hp
    dsimp only [A]
    have hX : Work.BoseBoxFock.WRegG ℓ
        (Work.BoseDict.boxAnnOf e (f (p.1 - p.2)) d
          (Work.BoseDict.boxAnnOf e (f p.2) (d + 1) Θ)) :=
      Work.BoseBoxFock.boxAnnOf_wregG hmeas hbdd hsupp (f (p.1 - p.2))
        (Work.BoseBoxFock.boxAnnOf_wregG hmeas hbdd hsupp (f p.2)
          ⟨hΘm, hΘb, hΘsupp⟩)
    rw [Work.BoseBoxFock.PotCubicLowBandAux.cIPnAux_self_re
      (Work.BoseBoxFock.PotCubicLowBandAux.cIPnAux_integrable_star_mul_self hX.meas.aemeasurable
        (Work.BoseBoxFock.PotCubicLowBandAux.cIPnAux_wreg_integrable_normSq hX))]
    exact MeasureTheory.integral_nonneg (fun x => sq_nonneg (‖Work.BoseDict.boxAnnOf e
      (f (p.1 - p.2)) d (Work.BoseDict.boxAnnOf e (f p.2) (d + 1) Θ) x‖))
  have hAnnB : ∀ p ∈ P, 0 ≤ Bq p := by
    intro p hp
    dsimp only [Bq]
    have hY : Work.BoseBoxFock.WRegG ℓ
        (Work.BoseDict.boxAnnOf e (g p.1) d
          (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ)) :=
      Work.BoseBoxFock.boxAnnOf_wregG hmeas hbdd hsupp (g p.1)
        (Work.BoseBoxFock.boxAnnOf_wregG hmeas hbdd hsupp (Work.BoseB4.evec m 0)
          ⟨hΘm, hΘb, hΘsupp⟩)
    rw [Work.BoseBoxFock.PotCubicLowBandAux.cIPnAux_self_re
      (Work.BoseBoxFock.PotCubicLowBandAux.cIPnAux_integrable_star_mul_self hY.meas.aemeasurable
        (Work.BoseBoxFock.PotCubicLowBandAux.cIPnAux_wreg_integrable_normSq hY))]
    exact MeasureTheory.integral_nonneg (fun x => sq_nonneg (‖Work.BoseDict.boxAnnOf e
      (g p.1) d (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ) x‖))
  have hzbd : ∀ p ∈ P, ‖z p‖ ≤ 2 * (Real.sqrt (A p) * Real.sqrt (Bq p)) := by
    intro p hp
    dsimp only [z, A, Bq]
    exact Work.BoseBoxFock.PotCubicLowBandAux.cIPnAux_atomNorm hmeas hbdd hsupp horth hMemLp
      f g p.1 p.2 hΘm hΘb hΘsupp hΘsym
  have hCS := Work.BoseBoxFock.PotCubicLowBandAux.cIPnAux_weightedCS (S := P) (w := w)
    (A := A) (B := Bq) (z := z) hAnnA hAnnB hzbd
  -- ## Step 5: collapse the `k = 0` sum
  have hSX : (∑ p ∈ P, |w p| * A p)
      = ∑ s ∈ Work.BoseB7.excited Mode, |E.fL s| * |E.W1 0| * (Work.BoseDict.cIPn d
          (Work.BoseDict.boxAnnOf e (f s) d
            (Work.BoseDict.boxAnnOf e (f 0) (d + 1) Θ))
          (Work.BoseDict.boxAnnOf e (f s) d
            (Work.BoseDict.boxAnnOf e (f 0) (d + 1) Θ))).re := by
    dsimp only [P]
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_singleton]
    dsimp only [w, A]
    rw [abs_mul, sub_zero]
  have hSY : (∑ p ∈ P, |w p| * Bq p)
      = ∑ s ∈ Work.BoseB7.excited Mode, |E.fL s| * |E.W1 0| * (Work.BoseDict.cIPn d
          (Work.BoseDict.boxAnnOf e (g s) d
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))
          (Work.BoseDict.boxAnnOf e (g s) d
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))).re := by
    dsimp only [P]
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_singleton]
    dsimp only [w, Bq]
    rw [abs_mul]
  rw [hSX, hSY] at hCS
  -- ## Step 6: the final chain
  have hsq : 0 ≤ E.ell ^ (-(3 : ℝ)) := Real.rpow_nonneg hEℓ.le _
  calc (∫ x : Work.BoseDict.Xn (d + 2), star (Θ x) *
        Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g
          (Work.BoseB7.excited Mode) E Θ x).re
      - (∫ x : Work.BoseDict.Xn (d + 2), star (Θ x) *
        Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g
          (Finset.univ : Finset Mode) E Θ x).re
      = -(E.ell ^ (-(3 : ℝ)) * (∑ p ∈ P, ((w p : ℝ) : ℂ) * z p).re) := hRowEq2
    _ ≤ |E.ell ^ (-(3 : ℝ)) * (∑ p ∈ P, ((w p : ℝ) : ℂ) * z p).re| := neg_le_abs _
    _ = E.ell ^ (-(3 : ℝ)) * |(∑ p ∈ P, ((w p : ℝ) : ℂ) * z p).re| := by
        rw [abs_mul, abs_of_nonneg hsq]
    _ ≤ E.ell ^ (-(3 : ℝ)) * ‖∑ p ∈ P, ((w p : ℝ) : ℂ) * z p‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hsq
    _ ≤ E.ell ^ (-(3 : ℝ)) * (2 * Real.sqrt (∑ s ∈ Work.BoseB7.excited Mode,
          |E.fL s| * |E.W1 0| * (Work.BoseDict.cIPn d
            (Work.BoseDict.boxAnnOf e (f s) d
              (Work.BoseDict.boxAnnOf e (f 0) (d + 1) Θ))
            (Work.BoseDict.boxAnnOf e (f s) d
              (Work.BoseDict.boxAnnOf e (f 0) (d + 1) Θ))).re)
        * Real.sqrt (∑ s ∈ Work.BoseB7.excited Mode,
          |E.fL s| * |E.W1 0| * (Work.BoseDict.cIPn d
            (Work.BoseDict.boxAnnOf e (g s) d
              (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))
            (Work.BoseDict.boxAnnOf e (g s) d
              (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))).re)) :=
        mul_le_mul_of_nonneg_left hCS hsq
    _ = 2 * (E.ell ^ (-(3 : ℝ))) *
        Real.sqrt (∑ s ∈ Work.BoseB7.excited Mode,
          |E.fL s| * |E.W1 0| * (Work.BoseDict.cIPn d
            (Work.BoseDict.boxAnnOf e (f s) d
              (Work.BoseDict.boxAnnOf e (f 0) (d + 1) Θ))
            (Work.BoseDict.boxAnnOf e (f s) d
              (Work.BoseDict.boxAnnOf e (f 0) (d + 1) Θ))).re) *
        Real.sqrt (∑ s ∈ Work.BoseB7.excited Mode,
          |E.fL s| * |E.W1 0| * (Work.BoseDict.cIPn d
            (Work.BoseDict.boxAnnOf e (g s) d
              (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))
            (Work.BoseDict.boxAnnOf e (g s) d
              (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))).re) := by
        ring

end Work.BoseBoxFock.FRK
