/-
  Area E7, item 2 (second half): the band cells are `*`-sets and sub-Pfaffian.

  This is the band analogue of `Submission/Work/WilE7/graphCell_star_proved.lean`.  Given the
  sheet data of `Work.WilE7.sheetAssembly` (a stratum `S : Stratum p (m+1)` with `S.j = m+1`,
  a `SemiPf` base `Z` with `C = π_p (connectedComponentIn Z.set u₀)`, and continuous sheets
  `s j : C → ℝ^{m+1}` covering `S.X.set` over `C`), the *band cell* between the sheets `i < j`

    `band i j = {y : Fin (p+1) → ℝ | Fin.init y ∈ C ∧
        (s i (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
        y (Fin.last p) < (s j (Fin.init y)) (Fin.last m)}`

  is `Star a (c.eval D) (p+1)` and `SubPf (p+1)`.

  The presentation is `Work.WilE7.BandAux.bandS3`: the double fibre product of `Z` with `S.X`
  with the vertical coordinate appended, cut by `v₂ < t < v₂'`.  Its connected component through
  the parametrised point `bandPt u₀ (s i x₀) (s j x₀) t₀` projects (`bandExtract`) onto the band
  (`Work.WilE7.BandAux.bandComp_base/sheets/cover`), and a coordinate permutation
  (`Work.WilE7.bandPerm`) turns that projection into a `projFirst`.  Since `a` and `c` are chosen
  *before* `D` and `F`, they may be taken to be the format and the (constant polynomial of the)
  degree of the constructed semi-Pfaffian set.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.sheetAssembly
import Submission.Work.WilE7.sheetComponent
import Submission.Work.WilE7.sheetLevels
import Submission.Work.WilE7.graphCell_star_proved
import Submission.Work.WilE7.fiberProduct_semiPf
import Submission.Work.WilE7.BandAux.BandDefs
import Submission.Work.WilE7.BandAux.bandComponent
import Submission.Work.WilE7.BandAux.subPf_of_star_of_comp

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
namespace Work.WilE7
open WilkiesDesign WilkiesDesign.E
open Work.WilE7.BandAux

theorem bandCell_star
    {p m : ℕ} (S : WilkiesDesign.E.Stratum p (m + 1)) (hGood : S.Good) (hj : S.j = m + 1)
    (Z : WilkiesDesign.E.SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ) (hu₀ : u₀ ∈ Z.set)
    (C : Set (Fin p → ℝ))
    (hC : C = Set.image (WilkiesDesign.E.projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (hCpf : WilkiesDesign.E.SubPf p C)
    (k : ℕ) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ j, ContinuousOn (s j) C)
    (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set)
    (hcov : ∀ z ∈ S.X.set, WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
      ∃ j : Fin k, s j (WilkiesDesign.E.projFirst p (m + 1) z) =
        WilkiesDesign.E.projSnd p (m + 1) z)
    (hcomp : ∀ {n : ℕ} (X : WilkiesDesign.E.SemiPf n) (x : Fin n → ℝ),
      WilkiesDesign.E.SubPf n (connectedComponentIn X.set x))
    (hlvl : ∀ x ∈ C, StrictMono fun j : Fin k => (s j x) (Fin.last m))
    (i j : Fin k) (hij : i < j) :
    ∃ (a : ℕ) (c : Polynomial ℕ), ∀ (D F : ℕ),
      S.X.fmt ≤ F → S.deg ≤ D → Z.fmt ≤ F → Z.deg ≤ D →
      WilkiesDesign.E.Star a (c.eval D) (p + 1)
        {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
          (s i (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
          y (Fin.last p) < (s j (Fin.init y)) (Fin.last m)} ∧
      WilkiesDesign.E.SubPf (p + 1)
        {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
          (s i (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
          y (Fin.last p) < (s j (Fin.init y)) (Fin.last m)} := by
  classical
  have _ := hGood
  have _ := hj
  have _ := hCpf
  -- the base point `x₀ = π_p u₀` lies in `C`
  have hx₀C : projFirst p (m + 1) u₀ ∈ C := by
    rw [hC]
    exact ⟨u₀, mem_connectedComponentIn hu₀, rfl⟩
  have hmono : (s i (projFirst p (m + 1) u₀)) (Fin.last m) <
      (s j (projFirst p (m + 1) u₀)) (Fin.last m) := (hlvl _ hx₀C) hij
  -- both levels lie in `[-1,1]`
  have hbnd_i : |(s i (projFirst p (m + 1) u₀)) (Fin.last m)| ≤ 1 := by
    have h := (hsub i _ hx₀C).1 (Fin.natAdd p (Fin.last m))
    rwa [Fin.append_right] at h
  have hbnd_j : |(s j (projFirst p (m + 1) u₀)) (Fin.last m)| ≤ 1 := by
    have h := (hsub j _ hx₀C).1 (Fin.natAdd p (Fin.last m))
    rwa [Fin.append_right] at h
  -- the vertical coordinate `t₀`: the midpoint of the two levels
  set t₀ : ℝ := ((s i (projFirst p (m + 1) u₀)) (Fin.last m) +
    (s j (projFirst p (m + 1) u₀)) (Fin.last m)) / 2 with ht₀def
  have ht₀ : (s i (projFirst p (m + 1) u₀)) (Fin.last m) < t₀ := by
    rw [ht₀def]; linarith
  have ht₀' : t₀ < (s j (projFirst p (m + 1) u₀)) (Fin.last m) := by
    rw [ht₀def]; linarith
  have ht₀cube : |t₀| ≤ 1 := by
    have hi := (abs_le.mp hbnd_i).1
    have hj' := (abs_le.mp hbnd_j).2
    rw [ht₀def, abs_le]
    constructor <;> linarith
  -- the canonical point of the constructed semi-Pfaffian set
  have hp₀ : bandPt u₀ (s i (projFirst p (m + 1) u₀)) (s j (projFirst p (m + 1) u₀)) t₀
      ∈ (bandS3 Z S).set :=
    bandPt_mem Z S u₀ hu₀ _ _ t₀ (hsub i _ hx₀C) (hsub j _ hx₀C) ht₀cube ht₀ ht₀'
  set p₀ : Fin (bandDim p m) → ℝ :=
    bandPt u₀ (s i (projFirst p (m + 1) u₀)) (s j (projFirst p (m + 1) u₀)) t₀ with hp₀def
  set O : Set (Fin (bandDim p m) → ℝ) := connectedComponentIn (bandS3 Z S).set p₀ with hOdef
  -- the coordinate permutation and the `*`-piece
  obtain ⟨e, he⟩ := bandPerm p m
  have he' : ∀ y : Fin ((p + 1) + bandFib p m) → ℝ,
      projFirst (p + 1) (bandFib p m) y = bandExtract (pullHomeo e y) := fun y => he y
  set P : StarPiece (p + 1) :=
    ⟨bandFib p m, SemiPf.reindex e (bandS3 Z S), (pullHomeo e).symm p₀⟩ with hPdef
  have hPset : P.set = bandExtract '' O := by
    have hc := sp_reindex_component e (bandS3 Z S) p₀
    show projFirst (p + 1) (bandFib p m) ''
        connectedComponentIn (SemiPf.reindex e (bandS3 Z S)).set ((pullHomeo e).symm p₀) = _
    rw [hc]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨pullHomeo e y, hy, (he' y).symm⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(pullHomeo e).symm z, ?_, ?_⟩
      · rw [Set.mem_preimage, Homeomorph.apply_symm_apply]
        exact hz
      · rw [he' ((pullHomeo e).symm z), Homeomorph.apply_symm_apply]
  -- the component of `bandS3` projects exactly onto the band
  have hOsub : bandExtract '' O ⊆ {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
      (s i (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
      y (Fin.last p) < (s j (Fin.init y)) (Fin.last m)} := by
    rintro x ⟨w, hw, rfl⟩
    obtain ⟨-, -, -, -, -, -, -, -, h9, h10⟩ :=
      (bandS3_mem_iff Z S w).mp (connectedComponentIn_subset _ _ hw)
    obtain ⟨hsi, hsj⟩ :=
      bandComp_sheets S Z u₀ C hC k s hcont hinj hsub hcov i j t₀ hp₀ w hw
    have hbase : bandBase w ∈ C :=
      bandComp_base S Z u₀ C hC (s i (projFirst p (m + 1) u₀))
        (s j (projFirst p (m + 1) u₀)) t₀ hp₀ w hw
    have h1 : (s i (Fin.init (bandExtract w))) (Fin.last m) = bandV2 w := by
      simp only [bandExtract_eq_snoc, Fin.init_snoc, bandV2, hsi, Fin.append_right, bandBase]
    have h2 : bandExtract w (Fin.last p) = bandT w := by
      simp only [bandExtract_eq_snoc, Fin.snoc_last]
    have h3 : (s j (Fin.init (bandExtract w))) (Fin.last m) = bandV2' w := by
      simp only [bandExtract_eq_snoc, Fin.init_snoc, bandV2', hsj, Fin.append_right, bandBase]
    refine ⟨?_, ?_, ?_⟩
    · simp only [bandExtract_eq_snoc, Fin.init_snoc]
      exact hbase
    · rw [h1, h2]
      exact h9
    · rw [h2, h3]
      exact h10
  have hOsup : {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
      (s i (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
      y (Fin.last p) < (s j (Fin.init y)) (Fin.last m)} ⊆ bandExtract '' O := by
    rintro y ⟨hy1, hy2, hy3⟩
    exact bandComp_cover S Z u₀ C hC k s hcont hsub i j t₀ hp₀
      (fun x hx => (hlvl x hx) hij) y hy1 hy2 hy3
  have hband : bandExtract '' O = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
      (s i (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
      y (Fin.last p) < (s j (Fin.init y)) (Fin.last m)} :=
    Set.Subset.antisymm hOsub hOsup
  -- the `Star` presentation
  have hstar : Star (bandS3 Z S).fmt (bandS3 Z S).deg (p + 1)
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
        (s i (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
        y (Fin.last p) < (s j (Fin.init y)) (Fin.last m)} := by
    refine ⟨[P], ?_, ?_, ?_⟩
    · rw [← hband]
      rw [show (⋃ Q ∈ ([P] : List (StarPiece (p + 1))), Q.set) = P.set from by
        ext x
        simp]
      exact hPset.symm
    · intro Q hQ
      rw [List.mem_singleton] at hQ
      subst hQ
      show (SemiPf.reindex e (bandS3 Z S)).fmt ≤ (bandS3 Z S).fmt
      rw [bandS3_reindex_fmt]
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      show (SemiPf.reindex e (bandS3 Z S)).deg ≤ (bandS3 Z S).deg
      rw [sp_reindex_deg]
  have hsubpf : SubPf (p + 1)
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
        (s i (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
        y (Fin.last p) < (s j (Fin.init y)) (Fin.last m)} :=
    subPf_of_star_of_comp hstar hcomp
  exact ⟨(bandS3 Z S).fmt, Polynomial.C ((bandS3 Z S).deg), fun D F _ _ _ _ =>
    ⟨by simpa using hstar, hsubpf⟩⟩

end Work.WilE7
