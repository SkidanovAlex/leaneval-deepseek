/-
  WilE7 (`Submission.Work.WilE7.BelowAux.belowBand_star`): the *open* below band of the lowest
  sheet is a `*`-set.

  Given a stratum `S : Stratum p (m+1)`, a `SemiPf` base `Z` with
  `C = π_p (connectedComponentIn Z.set u₀)`, and continuous sheets `s j : C → ℝ^{m+1}` covering
  `S.X.set` over `C` with the lowest one strictly above the level `-1`, the region

    `{y : Fin (p+1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
        y (Fin.last p) < (s 0 (Fin.init y)) (Fin.last m)}`

  satisfies `WilkiesDesign.E.Star a (c.eval D) (p+1)` for a pair `(a, c)` chosen *before* the
  format/degree bounds `F`, `D` (one may take the format and the constant polynomial of the degree
  of the semi-Pfaffian presentation `belowSopen Z S`).

  The lower bound is *strict*, so the cell is not the `belowExtract`-image of the component of the
  closed presentation `belowS` through its `-1`-point (that component meets the hyperplane
  `t = -1`).  The presentation used here is the open one

    `belowSopen Z S = belowS Z S ∩ {t > -1}`

  (one extra strict atom, `belowOpenDefs`), whose connected component through the interior point
  `belowPt u₀ (s 0 x₀) (belowT0 s 0 u₀)` projects exactly onto the cell
  (`belowOpenComp_sub` / `belowOpenComp_cov`: the same component argument as for the closed cell,
  with the preconnected strict region `belowHlt`).  A coordinate permutation `belowPerm` moves the
  vertical coordinate next to the base coordinates, turning that projection into a `projFirst`
  (`belowStarPiece_extract`); that is the single `*`-piece of the presentation.

  The hypotheses `hinj` and `hcov` are used by `belowOpenComp_sub` (the component stays on sheet
  `0`); the format/degree bounds are not needed at all, since `a` and `c` are independent of
  `D` and `F`.
-/
import Mathlib
import Submission.Work.WilE7.BelowAux.BelowDefs
import Submission.Work.WilE7.BelowAux.belowPhi_mem
import Submission.Work.WilE7.BelowAux.belowPhi_continuous
import Submission.Work.WilE7.BelowAux.belowComp_sub
import Submission.Work.WilE7.BelowAux.preconn_under_graph
import Submission.Work.WilE7.reindex_component
import Submission.Work.WilE7.star_proj
import Submission.Work.WilE7.imageSubsetConnectedComponentIn
import Submission.Work.WilE7.BandAux.BandDefs
import Submission.Work.WilE7.BelowAux.belowOpenDefs
import Submission.Work.WilE7.BelowAux.belowOpenAux
import Submission.Work.WilE7.BelowAux.belowOpenComp_cov
import Submission.Work.WilE7.BelowAux.belowOpenComp_sub
import Submission.Work.WilE7.BelowAux.belowStarPiece_extract

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilE7.BelowAux
open WilkiesDesign WilkiesDesign.E

theorem belowBand_star
    {p m : ℕ} (S : WilkiesDesign.E.Stratum p (m + 1))
    (Z : WilkiesDesign.E.SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ) (hu₀ : u₀ ∈ Z.set)
    (C : Set (Fin p → ℝ))
    (hC : C = Set.image (WilkiesDesign.E.projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (k : ℕ) (hk : 0 < k) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ j, ContinuousOn (s j) C)
    (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set)
    (hcov : ∀ z ∈ S.X.set, WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
      ∃ j : Fin k, s j (WilkiesDesign.E.projFirst p (m + 1) z) =
        WilkiesDesign.E.projSnd p (m + 1) z)
    (hlt : ∀ x ∈ C, -1 < (s ⟨0, hk⟩ x) (Fin.last m)) :
    ∃ (a : ℕ) (c : Polynomial ℕ), ∀ (D F : ℕ),
      S.X.fmt ≤ F → S.deg ≤ D → Z.fmt ≤ F → Z.deg ≤ D →
      WilkiesDesign.E.Star a (c.eval D) (p + 1)
        {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
          y (Fin.last p) < (s ⟨0, hk⟩ (Fin.init y)) (Fin.last m)} := by
  classical
  -- the base point `x₀ = π_p u₀` lies in `C`
  have hx₀C : projFirst p (m + 1) u₀ ∈ C := by
    rw [hC]
    exact ⟨u₀, mem_connectedComponentIn hu₀, rfl⟩
  -- the level of the lowest sheet is `≤ 1` (it lies in the cube)
  have hlev : (s ⟨0, hk⟩ (projFirst p (m + 1) u₀)) (Fin.last m) ≤ 1 := by
    have h := (hsub ⟨0, hk⟩ _ hx₀C).1 (Fin.natAdd p (Fin.last m))
    rw [Fin.append_right] at h
    exact (abs_le.mp h).2
  -- the canonical *interior* vertical coordinate: the midpoint of `-1` and the level
  set t₀ : ℝ := belowT0 s ⟨0, hk⟩ u₀ with ht₀def
  have ht₀_gt : -1 < t₀ := belowT0_gt (hlt _ hx₀C)
  have ht₀_lt : t₀ < (s ⟨0, hk⟩ (projFirst p (m + 1) u₀)) (Fin.last m) :=
    belowT0_lt (hlt _ hx₀C)
  have ht₀_abs : |t₀| ≤ 1 := belowT0_abs (hlt _ hx₀C) hlev
  -- the canonical point of the open presentation
  set p₀ : Fin (belowDim p m) → ℝ :=
    belowPt u₀ (s ⟨0, hk⟩ (projFirst p (m + 1) u₀)) t₀ with hp₀def
  have hp₀ : p₀ ∈ (belowSopen Z S).set := by
    rw [hp₀def]
    exact belowPt_mem_open Z S u₀ hu₀ _ t₀ (hsub ⟨0, hk⟩ _ hx₀C) ht₀_abs ht₀_gt ht₀_lt
  set O : Set (Fin (belowDim p m) → ℝ) := connectedComponentIn (belowSopen Z S).set p₀ with hOdef
  -- the coordinate permutation and the `*`-piece
  obtain ⟨e, he⟩ := belowPerm p m
  have he' : ∀ y : Fin ((p + 1) + belowFib p m) → ℝ,
      projFirst (p + 1) (belowFib p m) y = belowExtract (fun i => y (e i)) := fun y => he y
  set P : StarPiece (p + 1) :=
    ⟨belowFib p m, Work.WilE7.SemiPf.reindex e (belowSopen Z S), (pullHomeo e).symm p₀⟩ with hPdef
  have hPset : P.set = belowExtract '' O := by
    rw [hPdef]
    exact belowStarPiece_extract (X := belowSopen Z S) (q := p₀) e he'
  -- the component's `belowExtract`-image is the open below cell
  have hOsub : belowExtract '' O ⊆
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
        y (Fin.last p) < (s ⟨0, hk⟩ (Fin.init y)) (Fin.last m)} := by
    simpa only [hOdef, hp₀def, ht₀def] using
      belowOpenComp_sub S Z u₀ hu₀ C hC k hk s hcont hinj hsub hcov hlt
  have hOsup :
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
        y (Fin.last p) < (s ⟨0, hk⟩ (Fin.init y)) (Fin.last m)} ⊆ belowExtract '' O := by
    simpa only [hOdef, hp₀def, ht₀def] using
      belowOpenComp_cov S Z u₀ hu₀ C hC k hk s hcont hsub hlt
  have hY : belowExtract '' O =
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
        y (Fin.last p) < (s ⟨0, hk⟩ (Fin.init y)) (Fin.last m)} :=
    Set.Subset.antisymm hOsub hOsup
  -- the `Star` presentation
  have hstar : WilkiesDesign.E.Star (belowSopen Z S).fmt (belowSopen Z S).deg (p + 1)
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
        y (Fin.last p) < (s ⟨0, hk⟩ (Fin.init y)) (Fin.last m)} := by
    refine ⟨[P], ?_, ?_, ?_⟩
    · rw [← hY]
      rw [show (⋃ Q ∈ ([P] : List (StarPiece (p + 1))), Q.set) = P.set from by
        ext x
        simp]
      exact hPset.symm
    · intro Q hQ
      rw [List.mem_singleton] at hQ
      subst hQ
      show (Work.WilE7.SemiPf.reindex e (belowSopen Z S)).fmt ≤ (belowSopen Z S).fmt
      rw [belowSopen_reindex_fmt]
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      show (Work.WilE7.SemiPf.reindex e (belowSopen Z S)).deg ≤ (belowSopen Z S).deg
      rw [sp_reindex_deg]
  exact ⟨(belowSopen Z S).fmt, Polynomial.C ((belowSopen Z S).deg), fun D F _ _ _ _ =>
    by simpa using hstar⟩

end Work.WilE7.BelowAux
