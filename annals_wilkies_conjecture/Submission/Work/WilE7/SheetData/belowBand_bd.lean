/-
  WilE7 (`Submission.Work.WilE7.SheetData.belowBand_bd`): the *open below band* of the lowest
  sheet, for an arbitrary semi-Pfaffian set `X` (no stratum, no `Good` hypothesis).

  This is the stratum-free form of `Work.WilE7.belowBand_bd`: the whole below-cell development
  (`Submission/Work/WilE7/BelowAux`) attaches a stratum `S : Stratum p (m+1)` to the sheet data,
  but it only ever uses `S` through its underlying set `S.X`:

  * `belowW1 Z S = fiberProdZ Z S.X` (`BelowAux.BelowDefs`), and every other object of the
    development (`belowS`, `belowSopen`, `belowPerm`, `belowPt`, `belowT0`, `belowPhi`, …) is
    built from it with no further use of `S`;
  * the sub-lemmas consumed by the assembly -- `belowOpenComp_subProved` (the component projects
    *into* the band), `belowOpenComp_cov` (it covers the band), `belowSopen_deg_bound` (the degree
    is polynomial in `D`) and `belowSopen_reindex_fmt` -- are all quantified over an *arbitrary*
    `S : Stratum p (m+1)`, with no `Good` and no condition on `S.j`.

  So it suffices to instantiate those sub-lemmas at the degenerate stratum `⟨X, 0, ∅⟩` attached
  to the semi-Pfaffian set `X`, whose underlying set is `X`.  The hypotheses `hsub`/`hcov` of the
  target are then exactly the sheet data those sub-lemmas ask for, and the degree bound
  `S.deg = S.X.deg + ∑_{a ∈ Fin 0} ⋯ = X.deg` is the target's `X.deg ≤ D`.

  The conclusion is the `*`-piece `⟨belowFib p m, reindex e (belowSopen Z ⟨X,0,∅⟩), …⟩` whose
  set is the open below band, of format `≤ 2 * F + 1` (the ambient dimension `belowDim p m` plus
  `Z.r + X.r`) and degree `≤ Cb.eval D`.
-/
import Mathlib
import Submission.Work.WilE7.belowBand_bd
import Submission.Work.WilE7.BelowAux.belowOpenComp_subProved
import Submission.Work.WilE7.BelowAux.belowOpenComp_cov
import Submission.Work.WilE7.BelowAux.belowSopen_deg_bound
import Submission.Work.WilE7.BelowAux.belowStarPiece_extract
import Submission.Work.WilE7.star_proj
import Submission.Work.WilE7.reindex_component

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical
namespace Work.WilE7.SheetData

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.BelowAux

/-- The degenerate stratum attached to a semi-Pfaffian set `X`: no equations at all (`j = 0`).

  The below-cell development of `WilE7` uses a stratum only through its underlying set `S.X`, so
  this is the stratum that puts an arbitrary `X` in the place where the `BelowAux` lemmas expect
  a `Stratum`. -/
def stratOfSemiPf {p q : ℕ} (X : WilkiesDesign.E.SemiPf (p + q)) : WilkiesDesign.E.Stratum p q :=
  ⟨X, 0, fun a => a.elim0⟩

/-- The underlying semi-Pfaffian set of `stratOfSemiPf X` is `X`. -/
theorem stratOfSemiPf_X {p q : ℕ} (X : WilkiesDesign.E.SemiPf (p + q)) :
    (stratOfSemiPf X).X = X := rfl

/-- The degree of `stratOfSemiPf X` is the degree of `X` (the sum over `Fin 0` is empty). -/
theorem stratOfSemiPf_deg {p q : ℕ} (X : WilkiesDesign.E.SemiPf (p + q)) :
    (stratOfSemiPf X).deg = X.deg := by
  simp [WilkiesDesign.E.Stratum.deg, stratOfSemiPf]

/-- The *below band* of the lowest sheet is a single `*`-piece with format and degree bounds
depending only on the format bound `F` --- for an arbitrary semi-Pfaffian set `X`: no stratum and
no `Good` hypothesis are needed (the sheet data `hsub`, `hcov`, `hinj`, `hcont`, `hlt` is all the
development consumes). -/
theorem belowBand_bd (F : ℕ) :
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
      (hcard : ∀ x ∈ C, (WilkiesDesign.E.fiber X.set x).ncard = k)
      (hlvl : ∀ x ∈ C, StrictMono fun j : Fin k => (s j x) (Fin.last m))
      (hlt : ∀ x ∈ C, -1 < (s ⟨0, hk⟩ x) (Fin.last m)) (D : ℕ),
      X.fmt ≤ F → X.deg ≤ D → Z.fmt ≤ F → Z.deg ≤ D →
      ∃ P : WilkiesDesign.E.StarPiece (p + 1),
        P.set = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
          y (Fin.last p) < (s ⟨0, hk⟩ (Fin.init y)) (Fin.last m)} ∧
        P.X.fmt ≤ A ∧ P.X.deg ≤ Cb.eval D := by
  classical
  obtain ⟨Cb, hCb⟩ := belowSopen_deg_bound F
  refine ⟨2 * F + 1, Cb, ?_⟩
  intro p m X Z u₀ hu₀ C hC hCpf k hk s hcont hinj hsub hcov hcard hlvl hlt D
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
