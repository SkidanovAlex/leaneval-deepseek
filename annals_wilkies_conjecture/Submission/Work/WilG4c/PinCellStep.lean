/-
  WilG4c / `PinCellStep` — the *pin* (graph) cell branch of the §5.3 assembly, with the degree
  bookkeeping done.

  `Work.WilkG4c.PinCellCharts` is the pin branch: if `pt` is a definable function whose graph is
  `Ω`-bounded and whose values lie in `I`, and if the *pinned slice*
  `(l,u) ↦ F i l (Fin.cons (pt l) u)` of the family is `Ω`-bounded at the *same* format and degree
  as `F` itself, then the charts of the `n`-dimensional F-lemma cover every cube point `x` with
  `x 0 = pt l`.

  The hypothesis "the same format and degree" is what makes `PinCellCharts` unusable directly:
  the pin `pt` comes from `Work.WilG4c.PinPtOfCell` (format a constant, degree a *polynomial* in
  the cell's degree) and the pinned slice from `Work.WilG4c.PinSliceGraphMem` (degree a polynomial
  in `D` and the pin's degree), so both bounds depend on `D`.  This file performs the two
  bookkeeping steps:

  * raise the three `Ω`-bounds to the common format `max F0 A0` and degree
    `MvPolynomial.eval ![D,r] (X 0 + dpt + dslice)` (a *sum*, hence `≥` each of `D`, `dpt`,
    `dslice` — `Ω` is monotone in both arguments);
  * compose `PinCellCharts`' conclusion back into a function of the outer `(D, r, k, -log ε)`:
    `PolySubstBoth C_X (X 1)` for the degree polynomial and `PolySubstFirst4 C_X` for the count
    polynomial.

  Everything here is `sorry`-free.
-/
import Mathlib
import Submission.Work.WilG4c.FLemAPI
import Submission.Work.WilkG4c.PinCellCharts
import Submission.Work.WilG4c.PolySubstBoth
import Submission.Work.WilG4c.PolySubstFirst4
import Submission.Work.WilG4c.StepLipAux

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilkG4c

/-- **The pin-cell branch of the §5.3 assembly.**  Given the family `F` at format `F0` and degree
`D`, a pin function `pt` (format `A0`, degree polynomial `dpt`) with `pt l ∈ I` on `Λ`, and the
pinned slice at degree polynomial `dslice`, produce a finite family `Φ` of charts of `F` which is
`ChartsOK` on `Λ` with a format that is a constant and a degree polynomial in `(D, r)`, has a
cardinality bound polynomial in `(D, r, k, -log ε)`, and covers every cube point `x` with
`x 0 = pt l`. -/
theorem PinCellStep (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv)
    (n p : ℕ) (hn : 1 ≤ n) (ih : ∀ q, FLem S q n) :
    ∀ (F0 A0 : ℕ) (dpt dslice : MvPolynomial (Fin 2) ℕ),
      ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : MvPolynomial (Fin 4) ℝ),
      ∀ (D r k : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
      ∀ (Λ : Set (Fin p → ℝ)) (F : Family k p (n + 1)) (pt : (Fin p → ℝ) → ℝ),
        (∀ i, famGraph (F i) ∈ S.Ω F0 D (p + (n + 1) + 1)) →
        graphOf pt ∈ S.Ω A0 (MvPolynomial.eval ![D, r] dpt) (p + 1) →
        (∀ l ∈ Λ, pt l ∈ I) →
        (∀ i, famGraph (fun l u => F i l (Fin.cons (pt l) u))
          ∈ S.Ω F0 (MvPolynomial.eval ![D, r] dslice) (p + n + 1)) →
        ValuesIn01 Λ F →
        ∃ Φ : Finset (ChartTuple p (n + 1)),
          (Φ.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c ∧
          ChartsOK S a (MvPolynomial.eval ![D, r] b) r Λ F Φ ∧
          (∀ l ∈ Λ, ∀ x ∈ openCube (n + 1), x 0 = pt l →
            ∃ φ ∈ Φ, ∃ t ∈ openCube (n + 1),
              ∀ i, |F i l (fun j => φ j l t) - F i l x| < ε) := by
  intro F0 A0 dpt dslice
  set CX : MvPolynomial (Fin 2) ℕ :=
    MvPolynomial.X 0 + dpt + dslice with hCX
  obtain ⟨a, b₀, c₀, H⟩ :=
    PinCellCharts S hcd hder n p hn ih (max F0 A0) (max F0 A0)
  obtain ⟨b, hb⟩ := PolySubstBoth CX (MvPolynomial.X 1) b₀
  obtain ⟨c, hc⟩ := PolySubstFirst4 CX c₀
  refine ⟨a, b, c, ?_⟩
  intro D r k ε hε hε1 Λ F pt hF hpt hptI hG hval
  have hCXeval : ∀ D r : ℕ,
      MvPolynomial.eval ![D, r] CX
        = D + MvPolynomial.eval ![D, r] dpt + MvPolynomial.eval ![D, r] dslice := by
    intro D r
    rw [hCX]
    simp [MvPolynomial.eval_add, MvPolynomial.eval_X]
  have hleD : D ≤ MvPolynomial.eval ![D, r] CX := by rw [hCXeval]; omega
  have hlept : MvPolynomial.eval ![D, r] dpt ≤ MvPolynomial.eval ![D, r] CX := by
    rw [hCXeval]; omega
  have hlesl : MvPolynomial.eval ![D, r] dslice ≤ MvPolynomial.eval ![D, r] CX := by
    rw [hCXeval]; omega
  obtain ⟨Φ, hcard₀, hok₀, hcov⟩ :=
    H (MvPolynomial.eval ![D, r] CX) r k ε hε hε1 Λ F pt
      (fun i => Omega_mono_le S (le_max_left _ _) hleD (hF i))
      (Omega_mono_le S (le_max_right _ _) hlept hpt)
      hptI
      (fun i => Omega_mono_le S (le_max_left _ _) hlesl (hG i))
      hval
  have hbev : MvPolynomial.eval ![D, r] b
      = MvPolynomial.eval ![MvPolynomial.eval ![D, r] CX, r] b₀ := by
    simpa using hb D r
  have hcev : MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c
      = MvPolynomial.eval ![((MvPolynomial.eval ![D, r] CX : ℕ) : ℝ), (r : ℝ), (k : ℝ),
          -Real.log ε] c₀ := hc D r k (-Real.log ε)
  refine ⟨Φ, ?_, ?_, hcov⟩
  · rw [hcev]; exact hcard₀
  · refine ChartsOK_mono hok₀ le_rfl (le_of_eq hbev.symm)

end Work.WilG4c
