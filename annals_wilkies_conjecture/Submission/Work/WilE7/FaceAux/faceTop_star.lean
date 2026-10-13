/-
  Area E7, item 2 (fifth piece): the *top face* of the top cell is a `*`-set.

  This is the top-face analogue of `Submission/Work/WilE7/FaceAux/faceBot_star.lean` (see also
  `Submission/Work/WilE7/aboveCell_star_proved.lean`).  Under the sheet data (a stratum
  `S : Stratum p (m+1)`, a `SemiPf` base `Z` with `C = π_p (connectedComponentIn Z.set u₀)`, and
  continuous sheets `s j : C → ℝ^{m+1}` whose top sheet stays strictly below the level `1`), the
  top face of the cell

    `faceTop = {y : Fin (p+1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = 1}`

  is `Star a (c.eval D) (p+1)`, with `a`, `c` independent of `D` and `F`.

  The presentation (`Work.WilE7.FaceAux.FaceDefs`) is: base `Z`, zero-padded by one vertical
  coordinate `t` (`faceZp`), cut by the equation `t = 1` (`faceY1`), then reindexed by the
  coordinate permutation `facePerm` which moves `t` next to the base coordinates, so that
  `projFirst (p+1) (m+1)` reads off `(base, t)`.  The connected component through
  `facePoint u₀` is, by `faceY1_component`, exactly the `facePoint`-image of the component of `Z`
  through `u₀`, and `faceExtract_facePoint` turns its projection into `u ↦ Fin.snoc (π_p u) 1`,
  whose image is `faceTop`.  The hypotheses `hcont`, `hsub`, `hgt` (and `S`) are not needed for
  this piece: the face lies above every sheet, so its `*`-presentation does not mention them.
-/
import Mathlib
import Submission.Work.WilE7.AboveAux.AboveDefs
import Submission.Work.WilE7.BelowAux.BelowDefs
import Submission.Work.WilE7.AboveAux.abovePhi_mem
import Submission.Work.WilE7.AboveAux.abovePhi_continuous
import Submission.Work.WilE7.reindex_component
import Submission.Work.WilE7.star_proj
import Submission.Work.WilE7.imageSubsetConnectedComponentIn
import Submission.Work.WilE7.BandAux.BandDefs
import Submission.Work.WilE7.FaceAux.FaceDefs
import Submission.Work.WilE7.FaceAux.faceY1_component

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.FaceAux
open WilkiesDesign WilkiesDesign.E

/-- The coordinate permutation `swap (facePermIdx p m) (faceIdx p m)` moves the last (padded)
coordinate, holding the vertical coordinate `t`, onto position `p`, directly after the base
coordinates.  Hence projecting a target-ordered point to its first `p+1` coordinates is the same
as reading `base + t` off the permuted (padded-ordered) point. -/
theorem facePermAux (p m : ℕ) :
    ∀ y : Fin (faceK p m) → ℝ,
      projFirst (p + 1) (m + 1) y =
        faceExtract
          (fun i => y (Equiv.swap (facePermIdx p m) (faceIdx p m) i)) := by
  intro y
  set sw : Fin (faceK p m) ≃ Fin (faceK p m) :=
    Equiv.swap (facePermIdx p m) (faceIdx p m) with hsw
  have hfix : ∀ i : Fin (faceK p m), i.val < p → sw i = i := by
    intro i hi
    rw [hsw]
    refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
    · intro h
      have h2 := congrArg Fin.val h
      rw [facePermIdx_val] at h2
      omega
    · intro h
      have h2 := congrArg Fin.val h
      rw [faceIdx_val] at h2
      simp only [faceN] at h2
      omega
  have hidx : sw (faceIdx p m) = facePermIdx p m := by
    rw [hsw]
    exact Equiv.swap_apply_right (facePermIdx p m) (faceIdx p m)
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · unfold faceExtract
    rw [Fin.snoc_castSucc]
    change y (Fin.castAdd (m+1) (Fin.castSucc j))
      = y (sw (Fin.castLE (faceN_le_faceK p m) (Fin.castAdd (m+1) j)))
    have hlt : (Fin.castLE (faceN_le_faceK p m) (Fin.castAdd (m+1) j)).val < p := by
      rw [Fin.val_castLE, Fin.val_castAdd]
      exact j.isLt
    rw [hfix _ hlt]
    exact congrArg y (Fin.ext rfl)
  · unfold faceExtract
    rw [Fin.snoc_last]
    change y (Fin.castAdd (m+1) (Fin.last p)) = y (sw (faceIdx p m))
    rw [hidx]
    exact congrArg y (Fin.ext rfl)

theorem faceTop_star
    {p m : ℕ} (S : WilkiesDesign.E.Stratum p (m + 1))
    (Z : WilkiesDesign.E.SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ) (hu₀ : u₀ ∈ Z.set)
    (C : Set (Fin p → ℝ))
    (hC : C = Set.image (WilkiesDesign.E.projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (k : ℕ) (hk : 0 < k) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ j, ContinuousOn (s j) C)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set)
    (hgt : ∀ x ∈ C, (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ x) (Fin.last m) < 1) :
    ∃ (a : ℕ) (c : Polynomial ℕ), ∀ (D F : ℕ),
      S.X.fmt ≤ F → S.deg ≤ D → Z.fmt ≤ F → Z.deg ≤ D →
      WilkiesDesign.E.Star a (c.eval D) (p + 1)
        {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = 1} := by
  have _ := hcont; have _ := hsub; have _ := hgt; have _ := hk; have _ := S
  -- the coordinate permutation moving the vertical coordinate next to the base coordinates
  set e : Fin (faceK p m) ≃ Fin (faceK p m) :=
    Equiv.swap (facePermIdx p m) (faceIdx p m) with hedef
  have he : ∀ y : Fin (faceK p m) → ℝ,
      projFirst (p + 1) (m + 1) y = faceExtract (fun i => y (e i)) := by
    intro y
    rw [hedef]
    exact facePermAux p m y
  -- the `*`-piece: the reindexed cut set, based at the reindexed canonical point
  set P : StarPiece (p + 1) :=
    ⟨m + 1, SemiPf.reindex e (faceY1 Z),
      (Work.WilE7.pullHomeo e).symm (facePoint u₀)⟩ with hP
  -- the piece's set is the `faceExtract`-image of the component of the cut set
  have hPset : P.set = faceExtract '' connectedComponentIn (faceY1 Z).set (facePoint u₀) := by
    have h1 := Work.WilE7.sp_reindex_component e (faceY1 Z) (facePoint u₀)
    show projFirst (p + 1) (m + 1) ''
        connectedComponentIn (SemiPf.reindex e (faceY1 Z)).set
          ((Work.WilE7.pullHomeo e).symm (facePoint u₀)) = _
    rw [h1]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨Work.WilE7.pullHomeo e y, hy, (he y).symm⟩
    · rintro ⟨w, hw, rfl⟩
      refine ⟨(Work.WilE7.pullHomeo e).symm w, ?_, ?_⟩
      · rw [Set.mem_preimage, Homeomorph.apply_symm_apply]
        exact hw
      · rw [he ((Work.WilE7.pullHomeo e).symm w)]
        exact congrArg faceExtract (Homeomorph.apply_symm_apply (Work.WilE7.pullHomeo e) w)
  -- the component of the cut set is the `facePoint`-image of the component of `Z`
  have hcomp := faceY1_component Z u₀ hu₀
  have hfun : ∀ u : Fin (p + (m+1)) → ℝ,
      faceExtract (facePoint u) = Fin.snoc (projFirst p (m+1) u) 1 := faceExtract_facePoint
  -- the projection of that component is the top face
  have hfin : faceExtract '' (facePoint '' connectedComponentIn Z.set u₀) =
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = 1} := by
    ext y
    constructor
    · rintro ⟨w, ⟨u, hu, rfl⟩, hwy⟩
      rw [hfun u] at hwy
      rw [← hwy]
      refine ⟨?_, by rw [Fin.snoc_last]⟩
      rw [hC]
      exact ⟨u, hu, by rw [Fin.init_snoc]⟩
    · rintro ⟨hin, hlast⟩
      rw [hC] at hin
      obtain ⟨u, hu, hux⟩ := hin
      exact ⟨facePoint u, ⟨u, hu, rfl⟩, by rw [hfun u, hux, ← hlast, Fin.snoc_init_self]⟩
  have hPG : P.set = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = 1} := by
    rw [hPset, hcomp]
    exact hfin
  refine ⟨P.X.fmt, Polynomial.C P.X.deg, ?_⟩
  intro D F _ _ _ _
  have hunion : (⋃ Q ∈ ([P] : List (StarPiece (p + 1))), Q.set) = P.set := by
    ext x
    simp
  refine ⟨[P], ?_, ?_, ?_⟩
  · rw [hunion]
    exact hPG.symm
  · intro Q hQ
    rw [List.mem_singleton] at hQ
    subst hQ
    exact le_rfl
  · simp

end Work.WilE7.FaceAux
