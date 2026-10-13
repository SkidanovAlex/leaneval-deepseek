/-
  WilE7 (`Submission.Work.WilE7.belowCell_star_open`): the *open* below cell of the lowest
  sheet is a `*`-set and a sub-Pfaffian set.

  This is the strict-lower-bound analogue of `Submission/Work/WilE7/belowCell_star_proved.lean`.
  Under the sheet data of `Work.WilE7.sheetAssembly` the open below cell

    `Y = {y : Fin (p+1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
        y (Fin.last p) < (s 0 (Fin.init y)) (Fin.last m)}`

  is `Star a (c.eval D) (p+1)` and `SubPf (p+1)`, with `a`, `c` independent of `D` and `F`.

  * `Star`: the presentation is `belowSopen` (the fibre product `Z ×_C S.X` with the vertical
    coordinate appended, cut by `t < v₂` and `t > -1`).  The two inclusions
    `belowExtract '' component ⊆ Y` (`BelowAux.belowOpenComp_subProved`) and
    `Y ⊆ belowExtract '' component` (`BelowAux.belowOpenComp_cov`) show that the component
    through the interior point `belowPt u₀ (s 0 x₀) (belowT0 s 0 u₀)` projects exactly onto `Y`;
    `belowPerm` then turns that projection into a `projFirst`.  No `hcomp` is used: the format is
    bounded by `(belowSopen Z S).fmt` and the degree by `(belowSopen Z S).deg`.
  * `SubPf`: the counting realisation `BelowAux.belowOpenCell_subPf` (fibre product with `k`
    copies of `S.X.set`, the diagonal equations and the strict atoms `t > -1`,
    `t < last(block 0)`, `last(block i) < last(block j)`), whose projection is `Y` because the
    fibre of `S.X.set` over `x ∈ C` has exactly `k` points.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.star_proj
import Submission.Work.WilE7.BelowAux.BelowDefs
import Submission.Work.WilE7.BelowAux.belowOpenDefs
import Submission.Work.WilE7.BelowAux.belowOpenComp_cov
import Submission.Work.WilE7.BelowAux.belowOpenComp_subProved
import Submission.Work.WilE7.BelowAux.belowOpenCounting

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.BelowAux

theorem belowCell_star_open {p m : ℕ} (S : WilkiesDesign.E.Stratum p (m + 1)) (hGood : S.Good)
    (hj : S.j = m + 1)
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
    (hlt : ∀ x ∈ C, -1 < (s ⟨0, hk⟩ x) (Fin.last m)) :
    ∃ (a : ℕ) (c : Polynomial ℕ), ∀ (D F : ℕ),
      S.X.fmt ≤ F → S.deg ≤ D → Z.fmt ≤ F → Z.deg ≤ D →
      WilkiesDesign.E.Star a (c.eval D) (p + 1)
        {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
          y (Fin.last p) < (s ⟨0, hk⟩ (Fin.init y)) (Fin.last m)} ∧
      WilkiesDesign.E.SubPf (p + 1)
        {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
          y (Fin.last p) < (s ⟨0, hk⟩ (Fin.init y)) (Fin.last m)} := by
  classical
  have _ := hGood
  have _ := hj
  -- the base point `x₀ = π_p u₀` lies in `C`
  set x₀ : Fin p → ℝ := WilkiesDesign.E.projFirst p (m + 1) u₀ with hx₀def
  have hx₀C : x₀ ∈ C := by
    rw [hC]
    exact ⟨u₀, mem_connectedComponentIn hu₀, hx₀def.symm⟩
  have hlt0 : -1 < (s ⟨0, hk⟩ x₀) (Fin.last m) := hlt x₀ hx₀C
  -- the level of the lowest sheet at `x₀` is at most `1`
  have hlev_le : (s ⟨0, hk⟩ x₀) (Fin.last m) ≤ 1 := by
    have h := mem_cubeC_of_mem_set (hsub ⟨0, hk⟩ x₀ hx₀C) (Fin.natAdd p (Fin.last m))
    rw [Fin.append_right] at h
    exact le_trans (le_abs_self _) h
  -- the canonical point of `belowSopen`
  set p₀ : Fin (belowDim p m) → ℝ :=
    belowPt u₀ (s ⟨0, hk⟩ x₀) (belowT0 s ⟨0, hk⟩ u₀) with hp₀def
  have hp₀ : p₀ ∈ (belowSopen Z S).set := by
    rw [hp₀def]
    refine belowPt_mem_open Z S u₀ hu₀ (s ⟨0, hk⟩ x₀) (belowT0 s ⟨0, hk⟩ u₀)
      (hsub ⟨0, hk⟩ x₀ hx₀C) (belowT0_abs hlt0 hlev_le) (belowT0_gt hlt0)
      (belowT0_lt hlt0)
  -- the connected component of `p₀`
  set O : Set (Fin (belowDim p m) → ℝ) := connectedComponentIn (belowSopen Z S).set p₀ with hOdef
  -- the coordinate permutation and the `*`-piece
  obtain ⟨e, he⟩ := belowPerm p m
  have he' : ∀ y : Fin ((p + 1) + belowFib p m) → ℝ,
      WilkiesDesign.E.projFirst (p + 1) (belowFib p m) y = belowExtract (fun i => y (e i)) :=
    fun y => he y
  set P : StarPiece (p + 1) :=
    ⟨belowFib p m, Work.WilE7.SemiPf.reindex e (belowSopen Z S), (pullHomeo e).symm p₀⟩ with hPdef
  have hPset : P.set = belowExtract '' O := by
    have hc := sp_reindex_component e (belowSopen Z S) p₀
    show WilkiesDesign.E.projFirst (p + 1) (belowFib p m) ''
        connectedComponentIn (Work.WilE7.SemiPf.reindex e (belowSopen Z S)).set
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
  -- the component's `belowExtract`-image is the open below cell
  have hOsub : belowExtract '' O ⊆
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
        y (Fin.last p) < (s ⟨0, hk⟩ (Fin.init y)) (Fin.last m)} := by
    have h := belowOpenComp_subProved S Z u₀ hu₀ C hC k hk s hcont hinj hsub hcov hlt
    simpa only [hOdef, hp₀def, hx₀def] using h
  have hOsup :
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
        y (Fin.last p) < (s ⟨0, hk⟩ (Fin.init y)) (Fin.last m)} ⊆ belowExtract '' O := by
    have h := belowOpenComp_cov S Z u₀ hu₀ C hC k hk s hcont hsub hlt
    simpa only [hOdef, hp₀def, hx₀def] using h
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
  -- the `SubPf` half, by counting the fibre points
  have hsubpf : WilkiesDesign.E.SubPf (p + 1)
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
        y (Fin.last p) < (s ⟨0, hk⟩ (Fin.init y)) (Fin.last m)} :=
    belowOpenCell_subPf S C hCpf k hk s hsub hcard hlvl
  exact ⟨(belowSopen Z S).fmt, Polynomial.C ((belowSopen Z S).deg), fun D F _ _ _ _ =>
    ⟨by simpa using hstar, hsubpf⟩⟩

end Work.WilE7
