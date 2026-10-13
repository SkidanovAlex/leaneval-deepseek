/-
  `Work.WilE7.SheetData.aboveBandX`: the *open above band* of the "top" sheet, stated for an
  arbitrary semi-Pfaffian set `X` and with the two redundant sheet-data hypotheses
  (`hcard`, `hlvl`) of `Work.WilE7.SheetData.aboveBand_bd` dropped.

  The `*`-half of the above cell never uses the enumeration hypotheses: the single piece
  `Work.WilE7.aboveBandStar_piece` (`Submission/Work/WilE7/aboveBand_bd.lean`) produces a
  `StarPiece` whose set is exactly the band `{y | Fin.init y ∈ C ∧ s_{k-1} < y_last < 1}`, with
  format `≤ 2 * max X.fmt Z.fmt + 1` and degree bounded by an explicit expression in
  `max X.fmt Z.fmt` and `Z.deg + X.deg`.  That lemma is quantified over a stratum `S`, which it
  only ever uses through its underlying set `S.X`; instantiating at the degenerate stratum
  `⟨X, 0, Fin.elim0⟩` (whose `.X` is `X` definitionally) removes it, exactly as in
  `Submission/Work/WilE7/SheetData/aboveBand_bd.lean`.

  Note that `hcard` and `hlvl` really are redundant *as hypotheses*: `hsub` + `hinj` say the
  fibre over `x ∈ C` contains the `k` distinct points `s j x`, and `hcov` says it contains
  nothing else, so `hcard` follows.  Only `hlvl` (that the enumeration is level-increasing) is a
  genuinely additional hypothesis, and the conclusion stated here --- the band above the *listed*
  sheet `k - 1` --- is exactly the conclusion of the enumeration-free construction, which is why
  it can be dispensed with.
-/
import Mathlib
import Submission.Work.WilE7.SheetData.aboveBand_bd

-- the hypotheses of the target live inside the `∀` of an `∃ … ∀ …` statement; the unused-variable
-- linter mis-reports such binders, which cannot be renamed without changing the statement
set_option linter.unusedVariables false
noncomputable section
open Classical

namespace Work.WilE7.SheetData

theorem aboveBandX (F : ℕ) :
    ∃ (A : ℕ) (Cb : Polynomial ℕ), ∀ (p m : ℕ) (X : WilkiesDesign.E.SemiPf (p + (m + 1)))
      (Z : WilkiesDesign.E.SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ) (hu₀ : u₀ ∈ Z.set)
      (C : Set (Fin p → ℝ))
      (hC : C = Set.image (WilkiesDesign.E.projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
      (hCpf : WilkiesDesign.E.SubPf p C)
      (k : ℕ) (hk : 0 < k) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
      (hcont : ∀ j, ContinuousOn (s j) C)
      (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
      (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ X.set)
      (hcov : ∀ z ∈ X.set, WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
        ∃ j : Fin k, s j (WilkiesDesign.E.projFirst p (m + 1) z) =
          WilkiesDesign.E.projSnd p (m + 1) z)
      (hgt : ∀ x ∈ C, (s ⟨k - 1, by omega⟩ x) (Fin.last m) < 1) (D : ℕ),
      X.fmt ≤ F → X.deg ≤ D → Z.fmt ≤ F → Z.deg ≤ D →
      ∃ P : WilkiesDesign.E.StarPiece (p + 1),
        P.set = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
          (s ⟨k - 1, by omega⟩ (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
          y (Fin.last p) < 1} ∧
        P.X.fmt ≤ A ∧ P.X.deg ≤ Cb.eval D := by
  classical
  -- the same format/degree bounds as `Work.WilE7.SheetData.aboveBand_bd`
  refine ⟨2 * F + 1, Polynomial.C (5 * (1 + 2 * (2 * F + 3) ^ 2)) *
    (1 + 2 * Polynomial.X) ^ 4, ?_⟩
  intro p m X Z u₀ hu₀ C hC hCpf k hk s hcont hinj hsub hcov hgt D
    hXF hXD hZF hZD
  -- the stratum with no equations attached to `X`: the above-band construction only uses `.X`
  let S₀ : WilkiesDesign.E.Stratum p (m + 1) := ⟨X, 0, Fin.elim0⟩
  have hS₀ : S₀.X = X := rfl
  -- the enumeration-free above-band construction gives the piece outright
  obtain ⟨P, hPset, hPfmt, hPdeg⟩ :=
    Work.WilE7.aboveBandStar_piece S₀ Z u₀ hu₀ C hC k hk s hcont hinj hsub hcov hgt
  rw [hS₀] at hPfmt hPdeg
  refine ⟨P, hPset, ?_, ?_⟩
  · -- format: `max X.fmt Z.fmt ≤ F`
    have hmax : max X.fmt Z.fmt ≤ F := max_le hXF hZF
    omega
  · -- degree: assemble the polynomial arithmetic
    have hDval : (Polynomial.C (5 * (1 + 2 * (2 * F + 3) ^ 2)) *
        (1 + 2 * Polynomial.X) ^ 4 : Polynomial ℕ).eval D
        = 5 * (1 + 2 * (2 * F + 3) ^ 2) * (1 + 2 * D) ^ 4 := by simp
    rw [hDval]
    have hDF : max X.fmt Z.fmt ≤ F := max_le hXF hZF
    have hDD : Z.deg + X.deg ≤ 2 * D := by omega
    exact le_trans hPdeg
      (Work.WilE7.aboveBand_deg_arith F D (max X.fmt Z.fmt) (Z.deg + X.deg) hDF hDD)

end Work.WilE7.SheetData
