/-
  WilE7, area E7 (`Submission.Work.WilE7.AboveAux.aboveBand_star`): the *open above band* of the
  top sheet is a `*`-set.

  Given a stratum `S : Stratum p (m+1)`, a `SemiPf` base `Z` whose component gives
  `C = π_p (connectedComponentIn Z.set u₀)`, and continuous sheets `s j : C → ℝ^{m+1}` covering
  `S.X.set` over `C`, the *open above band* of the highest sheet `k - 1`

    `{y : Fin (p+1) → ℝ | Fin.init y ∈ C ∧
        (s (k-1) (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧ y (Fin.last p) < 1}`

  is `Star a (c.eval D) (p+1)`, with `a` and `c` chosen independently of `D` and `F`.

  The presentation is `Work.WilE7.AboveAux.aboveBandS` (see
  `Submission.Work.WilE7.AboveAux.AboveBandDefs`): the fibre product `Z ×_C S.X` with the vertical
  coordinate appended, cut by `v₂ < t < 1` (strict on both sides).  The two halves of "the
  connected component through the canonical point `aboveBandPt u₀ s hk` projects exactly onto the
  band" are proved here as `aboveBandComp_sub_aux` (the component stays on the highest sheet,
  below the level `1`) and `aboveBandComp_cov_aux` (every band point is hit, by the preconnected
  parametrising region `aboveBandH`), and `Work.WilE7.BelowAux.belowPerm` turns the projection of
  that component into a `projFirst`.  Since `a` and `c` are chosen *before* `D` and `F`, they may
  be taken to be the format and the (constant polynomial of the) degree of the constructed
  semi-Pfaffian set.

  This is the open twin of `Submission/Work/WilE7/aboveCell_star_proved.lean` (the *closed* above
  cell of the top sheet, `aboveS`) and of `Work.WilE7.bandCell_star` (an open band between two
  sheets).
-/
import Mathlib
import Submission.Work.WilE7.AboveAux.AboveDefs
import Submission.Work.WilE7.AboveAux.AboveBandDefs
import Submission.Work.WilE7.AboveAux.aboveComp_sub
import Submission.Work.WilE7.AboveAux.aboveComp_cov
import Submission.Work.WilE7.BelowAux.BelowDefs
import Submission.Work.WilE7.AboveAux.abovePhi_mem
import Submission.Work.WilE7.AboveAux.abovePhi_continuous
import Submission.Work.WilE7.reindex_component
import Submission.Work.WilE7.star_proj
import Submission.Work.WilE7.imageSubsetConnectedComponentIn
import Submission.Work.WilE7.BandAux.BandDefs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.AboveAux
open WilkiesDesign WilkiesDesign.E
open Work.WilE7.BelowAux

/-! ## §1. The two halves of the component argument for the open band -/

/-- The connected component of `aboveBandS` through the canonical point stays on the highest
sheet and strictly below the level `1`: it is contained in the *closed* above-cell component
through the `1`-point of the top sheet (`aboveComp_sub`), and its vertical coordinate is `< 1`
by construction.

Equivalently: the vertical segment over `u₀` between `aboveBandT` and `1` shows that the `1`-point
belongs to the closed component through `aboveBandPt`, and `aboveBandS.set ⊆ aboveS.set`. -/
theorem aboveBandComp_sub_aux
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
    (hgt : ∀ x ∈ C, (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ x) (Fin.last m) < 1) :
    Work.WilE7.BelowAux.belowExtract ''
        (connectedComponentIn (Work.WilE7.AboveAux.aboveBandS Z S).set
          (Work.WilE7.AboveAux.aboveBandPt u₀ s hk))
      ⊆ {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
          (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
          y (Fin.last p) < 1} := by
  classical
  have hx₀C : projFirst p (m + 1) u₀ ∈ C := by
    rw [hC]
    exact ⟨u₀, mem_connectedComponentIn hu₀, rfl⟩
  have hgtx₀ :
      (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ (projFirst p (m + 1) u₀)) (Fin.last m) < 1 :=
    hgt _ hx₀C
  -- the parametrising region of the *closed* above cell is preconnected
  have hpi : ∀ u ∈ connectedComponentIn Z.set u₀, projFirst p (m + 1) u ∈ C := by
    intro u hu
    rw [hC]
    exact ⟨u, hu, rfl⟩
  have hσ : ContinuousOn
      (fun u : Fin (p + (m + 1)) → ℝ =>
        (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ (projFirst p (m + 1) u)) (Fin.last m))
      (connectedComponentIn Z.set u₀) :=
    (continuous_apply (Fin.last m)).comp_continuousOn
      ((hcont ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩).comp
        (Work.WilE7.continuous_projFirst p (m + 1)).continuousOn hpi)
  have hpc : IsPreconnected (aboveH Z s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ u₀) := by
    rw [aboveH]
    exact preconn_over_graph isPreconnected_connectedComponentIn hσ
      (fun u hu => hgt _ (hpi u hu))
  have hphi : ContinuousOn (abovePhi s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩)
      (aboveH Z s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ u₀) :=
    abovePhi_continuous Z u₀ C hC s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩
      (hcont ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩)
  have hq0 : ((u₀, aboveBandT u₀ s hk) : (Fin (p + (m + 1)) → ℝ) × ℝ) ∈
      aboveH Z s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ u₀ := by
    rw [aboveH]
    exact ⟨mem_connectedComponentIn hu₀, lt_aboveBandT (u₀ := u₀) (s := s) (hk := hk) hgtx₀,
      le_of_lt (aboveBandT_lt_one (u₀ := u₀) (s := s) (hk := hk) hgtx₀)⟩
  have hq1 : ((u₀, (1 : ℝ)) : (Fin (p + (m + 1)) → ℝ) × ℝ) ∈
      aboveH Z s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ u₀ := by
    rw [aboveH]
    exact ⟨mem_connectedComponentIn hu₀, hgtx₀, le_refl 1⟩
  -- the `1`-point of the top sheet lies in the same closed component as `aboveBandPt`
  have hp₁c :
      belowPt u₀ (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ (projFirst p (m + 1) u₀)) 1 ∈
        connectedComponentIn (aboveS Z S).set (aboveBandPt u₀ s hk) := by
    have h := Work.WilE7.imageSubsetConnectedComponentIn hpc hphi hq0
      (abovePhi_mem S Z u₀ C hC s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ hsub)
      ((u₀, (1 : ℝ)) : (Fin (p + (m + 1)) → ℝ) × ℝ) hq1
    rwa [aboveBandPt_eq_abovePhi] at h
  -- the closed-cell component projects into the closed above cell
  have hsub_closed := aboveComp_sub S Z u₀ hu₀ C hC k hk s hcont hinj hsub hcov hgt
  rintro y ⟨w, hw, rfl⟩
  have hwband : w ∈ (aboveBandS Z S).set := connectedComponentIn_subset _ _ hw
  have hwp₀band : aboveBandPt u₀ s hk ∈ (aboveBandS Z S).set :=
    aboveBandPt_mem S Z u₀ hu₀ C hC k hk s hsub hgt
  have hwS : w ∈ connectedComponentIn (aboveS Z S).set (aboveBandPt u₀ s hk) :=
    connectedComponentIn_mono (aboveBandPt u₀ s hk) (aboveBandS_subset_aboveS Z S) hw
  have hclose : w ∈ connectedComponentIn (aboveS Z S).set
      (belowPt u₀ (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ (projFirst p (m + 1) u₀)) 1) :=
    IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn hp₁c
      (connectedComponentIn_subset (aboveS Z S).set (aboveBandPt u₀ s hk)) hwS
  obtain ⟨h1, h2, -⟩ := hsub_closed ⟨w, hclose, rfl⟩
  refine ⟨h1, h2, ?_⟩
  rw [belowExtract_apply_last]
  exact ((aboveBandS_mem_iff Z S w).mp hwband).2.2.2.2.2

/-- Every point of the open band is the `belowExtract`-image of a point of the component of
`aboveBandS` through the canonical point: the preconnected region `aboveBandH` parametrises the
band (`abovePhi_mem_aboveBandS`), so it lies in the component through `abovePhi (u₀, aboveBandT)`
(`imageSubsetConnectedComponentIn`). -/
theorem aboveBandComp_cov_aux
    {p m : ℕ} (S : WilkiesDesign.E.Stratum p (m + 1))
    (Z : WilkiesDesign.E.SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ) (hu₀ : u₀ ∈ Z.set)
    (C : Set (Fin p → ℝ))
    (hC : C = Set.image (WilkiesDesign.E.projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (k : ℕ) (hk : 0 < k) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ j, ContinuousOn (s j) C)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set)
    (hgt : ∀ x ∈ C, (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ x) (Fin.last m) < 1) :
    {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
        (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
        y (Fin.last p) < 1}
      ⊆ Work.WilE7.BelowAux.belowExtract ''
        (connectedComponentIn (Work.WilE7.AboveAux.aboveBandS Z S).set
          (Work.WilE7.AboveAux.aboveBandPt u₀ s hk)) := by
  classical
  have hx₀C : projFirst p (m + 1) u₀ ∈ C := by
    rw [hC]
    exact ⟨u₀, mem_connectedComponentIn hu₀, rfl⟩
  have hgtx₀ :
      (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ (projFirst p (m + 1) u₀)) (Fin.last m) < 1 :=
    hgt _ hx₀C
  have hpc := aboveBandH_preconn Z u₀ C hC s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩
    (hcont ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩) (fun x hx => hgt x hx)
  have hphi := abovePhi_continuousOn_aboveBandH Z u₀ C hC s
    ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ (hcont ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩)
  have hFmem := abovePhi_mem_aboveBandS S Z u₀ C hC s
    ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ hsub
  have hq0 : ((u₀, aboveBandT u₀ s hk) : (Fin (p + (m + 1)) → ℝ) × ℝ) ∈
      aboveBandH Z s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ u₀ := by
    rw [mem_aboveBandH]
    exact ⟨mem_connectedComponentIn hu₀, lt_aboveBandT (u₀ := u₀) (s := s) (hk := hk) hgtx₀,
      aboveBandT_lt_one (u₀ := u₀) (s := s) (hk := hk) hgtx₀⟩
  rintro y ⟨hyC0, hy1, hy2⟩
  obtain ⟨u, hucomp, hux⟩ : ∃ u ∈ connectedComponentIn Z.set u₀,
      projFirst p (m + 1) u = Fin.init y := by
    have h := hyC0
    rw [hC] at h
    exact h
  have hq : ((u, y (Fin.last p)) : (Fin (p + (m + 1)) → ℝ) × ℝ) ∈
      aboveBandH Z s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ u₀ := by
    rw [mem_aboveBandH]
    exact ⟨hucomp, by rw [hux]; exact hy1, hy2⟩
  have hmem := Work.WilE7.imageSubsetConnectedComponentIn hpc hphi hq0
    (fun q hq' => hFmem q hq') ((u, y (Fin.last p)) : (Fin (p + (m + 1)) → ℝ) × ℝ) hq
  refine ⟨belowPt u (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ (projFirst p (m + 1) u))
    (y (Fin.last p)), ?_, ?_⟩
  · rwa [aboveBandPt_eq_abovePhi] at hmem
  · rw [belowExtract_belowPt, hux, Fin.snoc_init_self]

/-! ## §2. The target -/

theorem aboveBand_star
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
    (hgt : ∀ x ∈ C, (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ x) (Fin.last m) < 1) :
    ∃ (a : ℕ) (c : Polynomial ℕ), ∀ (D F : ℕ),
      S.X.fmt ≤ F → S.deg ≤ D → Z.fmt ≤ F → Z.deg ≤ D →
      WilkiesDesign.E.Star a (c.eval D) (p + 1)
        {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
          (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
          y (Fin.last p) < 1} := by
  classical
  -- the canonical point of the band and the component through it
  set p₀ : Fin (belowDim p m) → ℝ := aboveBandPt u₀ s hk with hp₀def
  have hp₀ : p₀ ∈ (aboveBandS Z S).set := by
    rw [hp₀def]
    exact aboveBandPt_mem S Z u₀ hu₀ C hC k hk s hsub hgt
  set O : Set (Fin (belowDim p m) → ℝ) := connectedComponentIn (aboveBandS Z S).set p₀ with hOdef
  -- the coordinate permutation and the `*`-piece
  obtain ⟨e, he⟩ := belowPerm p m
  have he' : ∀ y : Fin ((p + 1) + belowFib p m) → ℝ,
      WilkiesDesign.E.projFirst (p + 1) (belowFib p m) y = belowExtract (fun i => y (e i)) :=
    fun y => he y
  set P : StarPiece (p + 1) :=
    ⟨belowFib p m, Work.WilE7.SemiPf.reindex e (aboveBandS Z S), (pullHomeo e).symm p₀⟩ with hPdef
  have hPset : P.set = belowExtract '' O := by
    have hc := sp_reindex_component e (aboveBandS Z S) p₀
    show WilkiesDesign.E.projFirst (p + 1) (belowFib p m) ''
        connectedComponentIn (Work.WilE7.SemiPf.reindex e (aboveBandS Z S)).set
          ((pullHomeo e).symm p₀) = _
    rw [hc]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨pullHomeo e y, hy, (he' y).symm⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(pullHomeo e).symm z, ?_, ?_⟩
      · rw [Set.mem_preimage, Homeomorph.apply_symm_apply]
        exact hz
      · rw [he' ((pullHomeo e).symm z)]
        exact congrArg belowExtract (Homeomorph.apply_symm_apply (pullHomeo e) z)
  -- the two halves of "the component projects exactly onto the band"
  have hOsub : belowExtract '' O ⊆
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
        (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
        y (Fin.last p) < 1} := by
    have h := aboveBandComp_sub_aux S Z u₀ hu₀ C hC k hk s hcont hinj hsub hcov hgt
    simpa only [hOdef, hp₀def] using h
  have hOsup :
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
        (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
        y (Fin.last p) < 1} ⊆ belowExtract '' O := by
    have h := aboveBandComp_cov_aux S Z u₀ hu₀ C hC k hk s hcont hsub hgt
    simpa only [hOdef, hp₀def] using h
  have hY : belowExtract '' O =
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
        (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
        y (Fin.last p) < 1} :=
    Set.Subset.antisymm hOsub hOsup
  -- the `Star` presentation
  have hstar : WilkiesDesign.E.Star (aboveBandS Z S).fmt (aboveBandS Z S).deg (p + 1)
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
        (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
        y (Fin.last p) < 1} := by
    refine ⟨[P], ?_, ?_, ?_⟩
    · rw [← hY]
      rw [show (⋃ Q ∈ ([P] : List (StarPiece (p + 1))), Q.set) = P.set from by
        ext x
        simp]
      exact hPset.symm
    · intro Q hQ
      rw [List.mem_singleton] at hQ
      subst hQ
      show (Work.WilE7.SemiPf.reindex e (aboveBandS Z S)).fmt ≤ (aboveBandS Z S).fmt
      rw [aboveBandS_reindex_fmt]
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      show (Work.WilE7.SemiPf.reindex e (aboveBandS Z S)).deg ≤ (aboveBandS Z S).deg
      rw [sp_reindex_deg]
  refine ⟨(aboveBandS Z S).fmt, Polynomial.C ((aboveBandS Z S).deg), fun D F _ _ _ _ => ?_⟩
  simpa using hstar

end Work.WilE7.AboveAux
