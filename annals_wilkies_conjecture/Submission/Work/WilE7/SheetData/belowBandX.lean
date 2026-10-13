/-
  `Work.WilE7.SheetData.belowBandX`: the open below band of the lowest sheet, for an arbitrary
  semi-Pfaffian set `X`.

  This is the statement `Work.WilE7.SheetData.belowBand_bd` with the two *superfluous* sheet
  hypotheses `hcard` (the fibre has exactly `k` points) and `hlvl` (the last coordinates of the
  sheets are strictly increasing in `j`) removed: the proof of `belowBand_bd` never uses them.

  Indeed, the two inclusions producing the piece are

  * `BelowAux.belowOpenComp_subProved` (the component projects *into* the band), which consumes
    `hcont`, `hinj`, `hsub`, `hcov`, `hlt` and neither `hcard` nor `hlvl`;
  * `BelowAux.belowOpenComp_cov` (the band is covered by the component), which consumes only
    `hcont`, `hsub`, `hlt`;

  and the format/degree bounds come from `BelowAux.belowSopen_deg_bound` and
  `Work.WilE7.sp_reindex_deg`, which are likewise independent of `hcard`/`hlvl`.  So the whole
  assembly of `belowBand_bd` goes through verbatim.

  The conclusion is the `*`-piece `⟨belowFib p m, reindex e (belowSopen Z S), …⟩` whose set is the
  open below band, of format `≤ 2 * F + 1` (the ambient dimension `belowDim p m` plus `Z.r + X.r`)
  and degree `≤ Cb.eval D`.
-/
import Mathlib
import Submission.Work.WilE7.SheetData.belowBand_bd

-- the hypotheses of the target live inside the `∀` of an `∃ … ∀ …` statement; the unused-variable
-- linter mis-reports such binders, which cannot be renamed without changing the statement
set_option linter.unusedVariables false
noncomputable section
open Classical

namespace Work.WilE7.SheetData

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.BelowAux

theorem belowBandX (F : ℕ) :
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
      (hlt : ∀ x ∈ C, -1 < (s ⟨0, hk⟩ x) (Fin.last m)) (D : ℕ),
      X.fmt ≤ F → X.deg ≤ D → Z.fmt ≤ F → Z.deg ≤ D →
      ∃ P : WilkiesDesign.E.StarPiece (p + 1),
        P.set = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
          y (Fin.last p) < (s ⟨0, hk⟩ (Fin.init y)) (Fin.last m)} ∧
        P.X.fmt ≤ A ∧ P.X.deg ≤ Cb.eval D := by
  classical
  obtain ⟨Cb, hCb⟩ := belowSopen_deg_bound F
  refine ⟨2 * F + 1, Cb, ?_⟩
  intro p m X Z u₀ hu₀ C hC hCpf k hk s hcont hinj hsub hcov hlt D
    hXF hXD hZF hZD
  -- the degenerate stratum carrying `X`, which is how the `BelowAux` lemmas see `X`
  set S : WilkiesDesign.E.Stratum p (m + 1) := stratOfSemiPf X with hSdef
  -- the base point of the component
  set x₀ : Fin p → ℝ := WilkiesDesign.E.projFirst p (m + 1) u₀ with hx₀def
  have hx₀C : x₀ ∈ C := by
    rw [hC]
    exact ⟨u₀, mem_connectedComponentIn hu₀, hx₀def.symm⟩
  -- the coordinate permutation and the canonical interior point of `belowSopen`
  obtain ⟨e, he⟩ := belowPerm p m
  set p₀ : Fin (belowDim p m) → ℝ :=
    belowPt u₀ (s ⟨0, hk⟩ x₀) (belowT0 s ⟨0, hk⟩ u₀) with hp₀def
  -- the candidate piece: the reindexed open below presentation based at `p₀`
  set P : WilkiesDesign.E.StarPiece (p + 1) :=
    ⟨belowFib p m, Work.WilE7.SemiPf.reindex e (belowSopen Z S),
      (Work.WilE7.pullHomeo e).symm p₀⟩ with hPdef
  have hPset : P.set =
      belowExtract '' connectedComponentIn (belowSopen Z S).set p₀ := by
    rw [hPdef]
    exact belowStarPiece_extract (X := belowSopen Z S) (q := p₀) e he
  -- the component projects onto the band
  have hOsub : belowExtract '' connectedComponentIn (belowSopen Z S).set p₀ ⊆
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
        y (Fin.last p) < (s ⟨0, hk⟩ (Fin.init y)) (Fin.last m)} := by
    have h := belowOpenComp_subProved S Z u₀ hu₀ C hC k hk s hcont hinj hsub hcov hlt
    simpa only [hp₀def, hx₀def] using h
  have hOsup :
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
        y (Fin.last p) < (s ⟨0, hk⟩ (Fin.init y)) (Fin.last m)} ⊆
      belowExtract '' connectedComponentIn (belowSopen Z S).set p₀ := by
    have h := belowOpenComp_cov S Z u₀ hu₀ C hC k hk s hcont hsub hlt
    simpa only [hp₀def, hx₀def] using h
  have hY : belowExtract '' connectedComponentIn (belowSopen Z S).set p₀ =
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
        y (Fin.last p) < (s ⟨0, hk⟩ (Fin.init y)) (Fin.last m)} :=
    Set.Subset.antisymm hOsub hOsup
  refine ⟨P, ?_, ?_, ?_⟩
  · rw [hPset, hY]
  · -- format: `(belowSopen Z S).fmt = Z.fmt + X.fmt + 1 ≤ 2 * F + 1`
    rw [hPdef]
    show (Work.WilE7.SemiPf.reindex e (belowSopen Z S)).fmt ≤ 2 * F + 1
    rw [belowSopen_reindex_fmt]
    have h1 : (belowSopen Z S).r = (belowS Z S).r := rfl
    have h2 : (belowS Z S).r = (belowPadded Z S).r := rfl
    have h3 : (belowPadded Z S).r = (belowW1 Z S).r + (Work.WilE7.bandCube1).r := rfl
    have h4 : (Work.WilE7.bandCube1).r = 0 := rfl
    have h5 : (belowW1 Z S).r = Z.r + X.r := rfl
    have h6 : Z.fmt = (p + (m + 1)) + Z.r := rfl
    have h7 : X.fmt = (p + (m + 1)) + X.r := rfl
    show belowDim p m + (belowSopen Z S).r ≤ 2 * F + 1
    rw [h1, h2, h3, h4, h5]
    simp only [belowDim, belowK] at h6 h7 ⊢
    omega
  · -- degree: the presentation's degree is bounded by the delegated polynomial
    rw [hPdef]
    show (Work.WilE7.SemiPf.reindex e (belowSopen Z S)).deg ≤ Cb.eval D
    rw [Work.WilE7.sp_reindex_deg]
    exact hCb Z S D hZF hXF hZD hXD

end Work.WilE7.SheetData
