/-
  Area E7, item 2 (third piece), **restated and closed**: the *below cell* of the lowest sheet is
  a `*`-set and a sub-Pfaffian set.

  This is the below-cell analogue of `Submission/Work/WilE7/bandCell_star.lean` (see also
  `graphCell_star_proved.lean`).  Under the sheet data of `Work.WilE7.sheetAssembly` (a stratum
  `S : Stratum p (m+1)` with `S.j = m+1`, a `SemiPf` base `Z` with
  `C = π_p (connectedComponentIn Z.set u₀)`, and continuous sheets `s j : C → ℝ^{m+1}` covering
  `S.X.set` over `C`), the below cell

    `below 0 = {y : Fin (p+1) → ℝ | Fin.init y ∈ C ∧ -1 ≤ y (Fin.last p) ∧
        y (Fin.last p) < (s 0 (Fin.init y)) (Fin.last m)}`

  is `Star a (c.eval D) (p+1)` and `SubPf (p+1)`, with `a`, `c` independent of `D` and `F`.

  The presentation is `Work.WilE7.BelowAux.belowS`: the fibre product `Z ×_C S.X` with the vertical
  coordinate appended, cut by `t < v₂` (the closed lower bound `-1 ≤ t` comes from the cube
  constraint on the vertical coordinate, and the sheet level `v₂ ≤ 1` makes the two equivalent).
  The two halves of "the connected component through `belowPt u₀ (s 0 x₀) (-1)` projects exactly
  onto the below cell" are `Work.WilE7.BelowAux.belowComp_sub` (the component stays on sheet `0`)
  and `Work.WilE7.BelowAux.belowComp_cov` (every cell point is hit, by the preconnected
  parametrising region `belowH`), and `belowPerm` turns the projection of that component into a
  `projFirst`.  Since `a` and `c` are chosen *before* `D` and `F`, they may be taken to be the
  format and the (constant polynomial of the) degree of the constructed semi-Pfaffian set.

  Note that the target's hypotheses `hGood`, `hj`, `hlvl`, `hCpf` and the format/degree bounds are
  not needed here: they belong to the *assembly* of the cell decomposition which consumes this
  lemma (there the sheets come from a `Good` stratum and `C` from the induction hypothesis).
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.sheetAssembly
import Submission.Work.WilE7.sheetComponent
import Submission.Work.WilE7.sheetLevels
import Submission.Work.WilE7.graphCell_star_proved
import Submission.Work.WilE7.bandCell_star
import Submission.Work.WilE7.fiberProduct_semiPf
import Submission.Work.WilE7.BelowAux.BelowDefs
import Submission.Work.WilE7.BelowAux.belowComp_sub
import Submission.Work.WilE7.BelowAux.belowComp_cov
import Submission.Work.WilE7.BandAux.subPf_of_star_of_comp
import Submission.Work.WilE7.star_proj

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.BelowAux
open Work.WilE7.BandAux

theorem belowCell_star_proved
    {p m : ℕ} (S : WilkiesDesign.E.Stratum p (m + 1)) (hGood : S.Good) (hj : S.j = m + 1)
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
    (hcomp : ∀ {n : ℕ} (X : WilkiesDesign.E.SemiPf n) (x : Fin n → ℝ),
      WilkiesDesign.E.SubPf n (connectedComponentIn X.set x))
    (hlvl : ∀ x ∈ C, StrictMono fun j : Fin k => (s j x) (Fin.last m))
    (hlt : ∀ x ∈ C, -1 < (s ⟨0, hk⟩ x) (Fin.last m)) :
    ∃ (a : ℕ) (c : Polynomial ℕ), ∀ (D F : ℕ),
      S.X.fmt ≤ F → S.deg ≤ D → Z.fmt ≤ F → Z.deg ≤ D →
      WilkiesDesign.E.Star a (c.eval D) (p + 1)
        {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 ≤ y (Fin.last p) ∧
          y (Fin.last p) < (s ⟨0, hk⟩ (Fin.init y)) (Fin.last m)} ∧
      WilkiesDesign.E.SubPf (p + 1)
        {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 ≤ y (Fin.last p) ∧
          y (Fin.last p) < (s ⟨0, hk⟩ (Fin.init y)) (Fin.last m)} := by
  classical
  have _ := hGood
  have _ := hj
  have _ := hCpf
  have _ := hlvl
  -- the base point `x₀ = π_p u₀` lies in `C`
  set x₀ : Fin p → ℝ := WilkiesDesign.E.projFirst p (m + 1) u₀ with hx₀def
  have hx₀C : x₀ ∈ C := by
    rw [hC]
    exact ⟨u₀, mem_connectedComponentIn hu₀, hx₀def.symm⟩
  -- the canonical point of `belowS`: base `u₀`, sheet `s 0`, vertical coordinate `-1`
  set p₀ : Fin (belowDim p m) → ℝ := belowPt u₀ (s ⟨0, hk⟩ x₀) (-1) with hp₀def
  have hp₀ : p₀ ∈ (belowS Z S).set := by
    rw [hp₀def]
    refine belowPt_mem Z S u₀ hu₀ (s ⟨0, hk⟩ x₀) (-1) (hsub ⟨0, hk⟩ x₀ hx₀C) ?_ ?_
    · rw [abs_neg, abs_one]
    · rw [hx₀def]
      exact hlt x₀ hx₀C
  -- the connected component of `p₀`
  set O : Set (Fin (belowDim p m) → ℝ) := connectedComponentIn (belowS Z S).set p₀ with hOdef
  -- the coordinate permutation and the `*`-piece
  obtain ⟨e, he⟩ := belowPerm p m
  have he' : ∀ y : Fin ((p + 1) + belowFib p m) → ℝ,
      WilkiesDesign.E.projFirst (p + 1) (belowFib p m) y = belowExtract (fun i => y (e i)) :=
    fun y => he y
  set P : StarPiece (p + 1) :=
    ⟨belowFib p m, Work.WilE7.SemiPf.reindex e (belowS Z S), (pullHomeo e).symm p₀⟩ with hPdef
  have hPset : P.set = belowExtract '' O := by
    have hc := sp_reindex_component e (belowS Z S) p₀
    show WilkiesDesign.E.projFirst (p + 1) (belowFib p m) ''
        connectedComponentIn (Work.WilE7.SemiPf.reindex e (belowS Z S)).set
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
  -- the component's `belowExtract`-image is the below cell
  have hOsub : belowExtract '' O ⊆
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 ≤ y (Fin.last p) ∧
        y (Fin.last p) < (s ⟨0, hk⟩ (Fin.init y)) (Fin.last m)} := by
    have h := belowComp_sub S Z u₀ hu₀ C hC k hk s hcont hinj hsub hcov hlt
    simpa only [hOdef, hp₀def, hx₀def] using h
  have hOsup :
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 ≤ y (Fin.last p) ∧
        y (Fin.last p) < (s ⟨0, hk⟩ (Fin.init y)) (Fin.last m)} ⊆ belowExtract '' O := by
    have h := belowComp_cov S Z u₀ hu₀ C hC k hk s hcont hsub hlt
    simpa only [hOdef, hp₀def, hx₀def] using h
  have hY : belowExtract '' O =
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 ≤ y (Fin.last p) ∧
        y (Fin.last p) < (s ⟨0, hk⟩ (Fin.init y)) (Fin.last m)} :=
    Set.Subset.antisymm hOsub hOsup
  -- the `Star` presentation
  have hstar : WilkiesDesign.E.Star (belowS Z S).fmt (belowS Z S).deg (p + 1)
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 ≤ y (Fin.last p) ∧
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
      show (Work.WilE7.SemiPf.reindex e (belowS Z S)).fmt ≤ (belowS Z S).fmt
      rw [belowS_reindex_fmt]
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      show (Work.WilE7.SemiPf.reindex e (belowS Z S)).deg ≤ (belowS Z S).deg
      rw [sp_reindex_deg]
  have hsubpf : WilkiesDesign.E.SubPf (p + 1)
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 ≤ y (Fin.last p) ∧
        y (Fin.last p) < (s ⟨0, hk⟩ (Fin.init y)) (Fin.last m)} :=
    subPf_of_star_of_comp hstar hcomp
  exact ⟨(belowS Z S).fmt, Polynomial.C ((belowS Z S).deg), fun D F _ _ _ _ =>
    ⟨by simpa using hstar, hsubpf⟩⟩

end Work.WilE7
