import Mathlib
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.bandCell_star
import Submission.Work.WilE7.BandAux.BandDefs
import Submission.Work.WilE7.BandAux.bandComponent
import Submission.Work.WilE7.BandAux.BandDefsTwo
import Submission.Work.WilE7.BandAux.bandBaseTwo
import Submission.Work.WilE7.BandAux.bandCompTwo_sheets
import Submission.Work.WilE7.BandAux.bandCompTwo_cover
import Submission.Work.WilE7.sheetComponent
import Submission.Work.WilE7.star_proj

set_option autoImplicit false
noncomputable section
open Classical Filter Topology

namespace Work.WilE7
open WilkiesDesign WilkiesDesign.E
open Work.WilE7.BandAux

theorem bandCellStar_twoStrata {p m : ℕ} (S₁ S₂ : WilkiesDesign.E.Stratum p (m + 1))
    (hGood₁ : S₁.Good) (hGood₂ : S₂.Good) (hj₁ : S₁.j = m + 1) (hj₂ : S₂.j = m + 1)
    (Z : WilkiesDesign.E.SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ) (hu₀ : u₀ ∈ Z.set)
    (C : Set (Fin p → ℝ))
    (hC : C = Set.image (WilkiesDesign.E.projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (hCpf : WilkiesDesign.E.SubPf p C)
    (k₁ : ℕ) (s₁ : Fin k₁ → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hcont₁ : ∀ j, ContinuousOn (s₁ j) C)
    (hinj₁ : ∀ x ∈ C, Function.Injective fun j : Fin k₁ => s₁ j x)
    (hsub₁ : ∀ j : Fin k₁, ∀ x ∈ C, Fin.append x (s₁ j x) ∈ S₁.X.set)
    (hcov₁ : ∀ z ∈ S₁.X.set, WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
      ∃ j : Fin k₁, s₁ j (WilkiesDesign.E.projFirst p (m + 1) z) =
        WilkiesDesign.E.projSnd p (m + 1) z)
    (hlvl₁ : ∀ x ∈ C, StrictMono fun j : Fin k₁ => (s₁ j x) (Fin.last m))
    (k₂ : ℕ) (s₂ : Fin k₂ → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hcont₂ : ∀ j, ContinuousOn (s₂ j) C)
    (hinj₂ : ∀ x ∈ C, Function.Injective fun j : Fin k₂ => s₂ j x)
    (hsub₂ : ∀ j : Fin k₂, ∀ x ∈ C, Fin.append x (s₂ j x) ∈ S₂.X.set)
    (hcov₂ : ∀ z ∈ S₂.X.set, WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
      ∃ j : Fin k₂, s₂ j (WilkiesDesign.E.projFirst p (m + 1) z) =
        WilkiesDesign.E.projSnd p (m + 1) z)
    (hlvl₂ : ∀ x ∈ C, StrictMono fun j : Fin k₂ => (s₂ j x) (Fin.last m))
    (i : Fin k₁) (j : Fin k₂)
    (hle : ∀ x ∈ C, (s₁ i x) (Fin.last m) < (s₂ j x) (Fin.last m)) :
    ∃ (a : ℕ) (c : Polynomial ℕ), ∀ (D F : ℕ),
      S₁.X.fmt ≤ F → S₁.deg ≤ D → S₂.X.fmt ≤ F → S₂.deg ≤ D → Z.fmt ≤ F → Z.deg ≤ D →
      WilkiesDesign.E.Star a (c.eval D) (p + 1)
        {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
          (s₁ i (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
          y (Fin.last p) < (s₂ j (Fin.init y)) (Fin.last m)} := by
  classical
  have _ := hGood₁
  have _ := hGood₂
  have _ := hj₁
  have _ := hj₂
  have _ := hCpf
  have _ := hlvl₁
  have _ := hlvl₂
  -- the base point `x₀ = π_p u₀` lies in `C`
  have hx₀C : projFirst p (m + 1) u₀ ∈ C := by
    rw [hC]
    exact ⟨u₀, mem_connectedComponentIn hu₀, rfl⟩
  have hmono : (s₁ i (projFirst p (m + 1) u₀)) (Fin.last m) <
      (s₂ j (projFirst p (m + 1) u₀)) (Fin.last m) := hle _ hx₀C
  -- both levels lie in `[-1,1]`
  have hbnd_i : |(s₁ i (projFirst p (m + 1) u₀)) (Fin.last m)| ≤ 1 := by
    have h := (hsub₁ i _ hx₀C).1 (Fin.natAdd p (Fin.last m))
    rwa [Fin.append_right] at h
  have hbnd_j : |(s₂ j (projFirst p (m + 1) u₀)) (Fin.last m)| ≤ 1 := by
    have h := (hsub₂ j _ hx₀C).1 (Fin.natAdd p (Fin.last m))
    rwa [Fin.append_right] at h
  -- the vertical coordinate `t₀`: the midpoint of the two levels
  set t₀ : ℝ := ((s₁ i (projFirst p (m + 1) u₀)) (Fin.last m) +
    (s₂ j (projFirst p (m + 1) u₀)) (Fin.last m)) / 2 with ht₀def
  have ht₀ : (s₁ i (projFirst p (m + 1) u₀)) (Fin.last m) < t₀ := by
    rw [ht₀def]; linarith
  have ht₀' : t₀ < (s₂ j (projFirst p (m + 1) u₀)) (Fin.last m) := by
    rw [ht₀def]; linarith
  have ht₀cube : |t₀| ≤ 1 := by
    have hi := (abs_le.mp hbnd_i).1
    have hj' := (abs_le.mp hbnd_j).2
    rw [ht₀def, abs_le]
    constructor <;> linarith
  -- the canonical point of the constructed semi-Pfaffian set
  have hp₀ : bandPt u₀ (s₁ i (projFirst p (m + 1) u₀)) (s₂ j (projFirst p (m + 1) u₀)) t₀
      ∈ (bandS3two Z S₁ S₂).set :=
    bandPt_mem_two Z S₁ S₂ u₀ hu₀ _ _ t₀ (hsub₁ i _ hx₀C) (hsub₂ j _ hx₀C) ht₀cube ht₀ ht₀'
  set p₀ : Fin (bandDim p m) → ℝ :=
    bandPt u₀ (s₁ i (projFirst p (m + 1) u₀)) (s₂ j (projFirst p (m + 1) u₀)) t₀ with hp₀def
  set O : Set (Fin (bandDim p m) → ℝ) := connectedComponentIn (bandS3two Z S₁ S₂).set p₀
    with hOdef
  -- the coordinate permutation and the `*`-piece
  obtain ⟨e, he⟩ := bandPerm p m
  have he' : ∀ y : Fin ((p + 1) + bandFib p m) → ℝ,
      projFirst (p + 1) (bandFib p m) y = bandExtract (pullHomeo e y) := fun y => he y
  set P : StarPiece (p + 1) :=
    ⟨bandFib p m, SemiPf.reindex e (bandS3two Z S₁ S₂), (pullHomeo e).symm p₀⟩ with hPdef
  have hPset : P.set = bandExtract '' O := by
    have hc := sp_reindex_component e (bandS3two Z S₁ S₂) p₀
    show projFirst (p + 1) (bandFib p m) ''
        connectedComponentIn (SemiPf.reindex e (bandS3two Z S₁ S₂)).set
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
      · rw [he' ((pullHomeo e).symm z), Homeomorph.apply_symm_apply]
  -- the component of `bandS3two` projects exactly onto the band
  have hOsub : bandExtract '' O ⊆ {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
      (s₁ i (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
      y (Fin.last p) < (s₂ j (Fin.init y)) (Fin.last m)} := by
    rintro x ⟨w, hw, rfl⟩
    obtain ⟨-, -, -, -, -, -, -, -, h9, h10⟩ :=
      (bandS3two_mem_iff Z S₁ S₂ w).mp (connectedComponentIn_subset _ _ hw)
    obtain ⟨hsi, hsj⟩ :=
      bandCompTwo_sheets S₁ S₂ Z u₀ C hC k₁ s₁ hcont₁ hinj₁ hsub₁ hcov₁ k₂ s₂ hcont₂ hinj₂
        hsub₂ hcov₂ i j t₀ hp₀ w hw
    have hbase : bandBase w ∈ C :=
      bandCompTwo_base S₁ S₂ Z u₀ C hC
        (s₁ i (projFirst p (m + 1) u₀)) (s₂ j (projFirst p (m + 1) u₀)) t₀ hp₀ w hw
    have h1 : (s₁ i (Fin.init (bandExtract w))) (Fin.last m) = bandV2 w := by
      simp only [bandExtract_eq_snoc, Fin.init_snoc, bandV2, hsi, Fin.append_right, bandBase]
    have h2 : bandExtract w (Fin.last p) = bandT w := by
      simp only [bandExtract_eq_snoc, Fin.snoc_last]
    have h3 : (s₂ j (Fin.init (bandExtract w))) (Fin.last m) = bandV2' w := by
      simp only [bandExtract_eq_snoc, Fin.init_snoc, bandV2', hsj, Fin.append_right, bandBase]
    refine ⟨?_, ?_, ?_⟩
    · simp only [bandExtract_eq_snoc, Fin.init_snoc]
      exact hbase
    · rw [h1, h2]
      exact h9
    · rw [h2, h3]
      exact h10
  have hOsup : {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
      (s₁ i (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
      y (Fin.last p) < (s₂ j (Fin.init y)) (Fin.last m)} ⊆ bandExtract '' O := by
    rintro y ⟨hy1, hy2, hy3⟩
    exact bandCompTwo_cover S₁ S₂ Z u₀ C hC k₁ s₁ hcont₁ hsub₁ k₂ s₂ hcont₂ hsub₂ i j t₀ hp₀
      hle y hy1 hy2 hy3
  have hband : bandExtract '' O = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
      (s₁ i (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
      y (Fin.last p) < (s₂ j (Fin.init y)) (Fin.last m)} :=
    Set.Subset.antisymm hOsub hOsup
  -- the `Star` presentation
  have hstar : Star (bandS3two Z S₁ S₂).fmt (bandS3two Z S₁ S₂).deg (p + 1)
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
        (s₁ i (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
        y (Fin.last p) < (s₂ j (Fin.init y)) (Fin.last m)} := by
    refine ⟨[P], ?_, ?_, ?_⟩
    · rw [← hband]
      rw [show (⋃ Q ∈ ([P] : List (StarPiece (p + 1))), Q.set) = P.set from by
        ext x
        simp]
      exact hPset.symm
    · intro Q hQ
      rw [List.mem_singleton] at hQ
      subst hQ
      show (SemiPf.reindex e (bandS3two Z S₁ S₂)).fmt ≤ (bandS3two Z S₁ S₂).fmt
      rw [bandS3two_reindex_fmt]
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      show (SemiPf.reindex e (bandS3two Z S₁ S₂)).deg ≤ (bandS3two Z S₁ S₂).deg
      rw [sp_reindex_deg]
  exact ⟨(bandS3two Z S₁ S₂).fmt, Polynomial.C ((bandS3two Z S₁ S₂).deg), fun D F _ _ _ _ _ _ =>
    by simpa using hstar⟩

end Work.WilE7
