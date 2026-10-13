/-
  WilE7 (`Submission.Work.WilE7.belowBand_bd`): the *open below band* of the lowest sheet is a
  **single** `*`-piece, with format `≤ A` and degree `≤ Cb.eval D` where `A` and `Cb` depend only
  on the format bound `F`.

  This is the bounded companion of `Work.WilE7.BelowAux.belowBand_star` and of
  `Work.WilE7.belowCell_star_open` (which produce a `Star`, i.e. a *list* of pieces, whose format
  and degree are the data-dependent `(belowSopen Z S).fmt` and `(belowSopen Z S).deg`).  The
  induction of `Submission/Work/WilE7/E7main_DESIGN.md` consumes the *piece* itself -- a cell of
  the cylindrical decomposition has to be the projection of *one* connected component -- together
  with complexity bounds that are uniform in `p`, `m`: `A` depends only on `F`, and `Cb` only
  on `F`.

  The proof has three steps.

  * **The piece.**  The presentation is `belowSopen Z S = belowS Z S ∩ {t > -1}`
    (`BelowAux.belowOpenDefs`), whose connected component through the canonical interior point
    `p₀ = belowPt u₀ (s 0 (π u₀)) (belowT0 s 0 u₀)` projects exactly onto the band: the two
    inclusions are `BelowAux.belowOpenComp_subProved` and `BelowAux.belowOpenComp_cov`.  The
    coordinate permutation `belowPerm` moves the vertical coordinate next to the base
    coordinates, so that the projection of the component becomes a `projFirst`
    (`BelowAux.belowStarPiece_extract`): the piece is
    `⟨belowFib p m, SemiPf.reindex e (belowSopen Z S), (pullHomeo e).symm p₀⟩`.
  * **Format.**  `(belowSopen Z S).fmt = Z.fmt + S.X.fmt + 1` (the presentation is the fibre
    product `Z ×_C S.X` with a vertical coordinate, and `SemiPf.fmt` is `ambient + chain`), so
    `A := 2 * F + 1` works under `S.X.fmt ≤ F`, `Z.fmt ≤ F`.
  * **Degree.**  `BelowAux.belowSopen_deg_bound` (the arithmetic of the DNF product
    `fiberProdZ Z S.X`, of `SemiPf.prod` with the vertical cube and of the two `addConds` cuts)
    supplies a polynomial `Cb` with `(belowSopen Z S).deg ≤ Cb.eval D` whenever
    `Z.fmt ≤ F`, `S.X.fmt ≤ F`, `Z.deg ≤ D`, `S.X.deg ≤ D`; reindexing preserves the degree
    (`sp_reindex_deg`).
-/
import Mathlib
import Submission.Work.WilE7.belowCell_star_open
import Submission.Work.WilE7.BelowAux.belowStarPiece_extract
import Submission.Work.WilE7.BelowAux.belowSopen_deg_bound

set_option autoImplicit false
-- the hypotheses of the target live inside the `∀` of an `∃ … ∀ …` statement; some of them
-- (`hGood`, `hj`, the sheet data) are only consumed indirectly, through the below-cell lemmas
set_option linter.unusedVariables false
noncomputable section
open Classical
namespace Work.WilE7

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.BelowAux

theorem belowBand_bd (F : ℕ) :
    ∃ (A : ℕ) (Cb : Polynomial ℕ), ∀ (p m : ℕ) (S : WilkiesDesign.E.Stratum p (m + 1))
      (hGood : S.Good) (hj : S.j = m + 1)
      (Z : WilkiesDesign.E.SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ) (hu₀ : u₀ ∈ Z.set)
      (C : Set (Fin p → ℝ))
      (hC : C = Set.image (WilkiesDesign.E.projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
      (hCpf : WilkiesDesign.E.SubPf p C)
      (k : ℕ) (hk : 0 < k) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
      (hcont : ∀ j, ContinuousOn (s j) C)
      (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
      (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set)
      (hcov : ∀ z ∈ S.X.set, WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
        ∃ j : Fin k, s j (WilkiesDesign.E.projFirst p (m + 1) z) =
          WilkiesDesign.E.projSnd p (m + 1) z)
      (hcard : ∀ x ∈ C, (WilkiesDesign.E.fiber S.X.set x).ncard = k)
      (hlvl : ∀ x ∈ C, StrictMono fun j : Fin k => (s j x) (Fin.last m))
      (hlt : ∀ x ∈ C, -1 < (s ⟨0, hk⟩ x) (Fin.last m)) (D : ℕ),
      S.X.fmt ≤ F → S.deg ≤ D → Z.fmt ≤ F → Z.deg ≤ D →
      ∃ P : WilkiesDesign.E.StarPiece (p + 1),
        P.set = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
          y (Fin.last p) < (s ⟨0, hk⟩ (Fin.init y)) (Fin.last m)} ∧
        P.X.fmt ≤ A ∧ P.X.deg ≤ Cb.eval D := by
  classical
  obtain ⟨Cb, hCb⟩ := belowSopen_deg_bound F
  refine ⟨2 * F + 1, Cb, ?_⟩
  intro p m S hGood hj Z u₀ hu₀ C hC hCpf k hk s hcont hinj hsub hcov hcard hlvl hlt D
    hSF hSD hZF hZD
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
      (pullHomeo e).symm p₀⟩ with hPdef
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
  -- `S.X.deg ≤ D` from `S.deg ≤ D`
  have hSXdeg : S.X.deg ≤ D := by
    have hsd := hSD
    simp only [WilkiesDesign.E.Stratum.deg] at hsd
    omega
  refine ⟨P, ?_, ?_, ?_⟩
  · rw [hPset, hY]
  · -- format: `(belowSopen Z S).fmt = Z.fmt + S.X.fmt + 1 ≤ 2 * F + 1`
    rw [hPdef]
    show (Work.WilE7.SemiPf.reindex e (belowSopen Z S)).fmt ≤ 2 * F + 1
    rw [belowSopen_reindex_fmt]
    have h1 : (belowSopen Z S).r = (belowS Z S).r := rfl
    have h2 : (belowS Z S).r = (belowPadded Z S).r := rfl
    have h3 : (belowPadded Z S).r = (belowW1 Z S).r + (bandCube1).r := rfl
    have h4 : (bandCube1).r = 0 := rfl
    have h5 : (belowW1 Z S).r = Z.r + S.X.r := rfl
    have h6 : Z.fmt = (p + (m + 1)) + Z.r := rfl
    have h7 : S.X.fmt = (p + (m + 1)) + S.X.r := rfl
    show belowDim p m + (belowSopen Z S).r ≤ 2 * F + 1
    rw [h1, h2, h3, h4, h5]
    simp only [belowDim, belowK] at *
    omega
  · -- degree: the presentation's degree is bounded by the delegated polynomial
    rw [hPdef]
    show (Work.WilE7.SemiPf.reindex e (belowSopen Z S)).deg ≤ Cb.eval D
    rw [sp_reindex_deg]
    exact hCb Z S D hZF hSF hZD hSXdeg

end Work.WilE7
