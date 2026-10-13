/-
  `Work.WilE7.SheetData.bandCell_bd`: the band cell between two sheets of two *semi-Pfaffian
  sets* — no `Stratum`/`Good` hypothesis — is a single `*`-piece with polynomial bounds.

  The stratum-level statement is `Work.WilE7.bandCell_bd`, resting on
  `Work.WilE7.bandCellStar_piece_twoStrata`.  Every ingredient of that development
  (`bandS3two`, `bandPt`, `bandCompTwo_sheets`, `bandCompTwo_cover`, `bandCompTwo_base`,
  `bandS3two_bd`, `bandPerm`, ...) uses the two strata *only* through their underlying
  semi-Pfaffian sets `.X`.  We expose this by attaching to a bare `SemiPf` set the `Stratum`
  with no equations (`dummyStratum`), whose `.X` field is that set definitionally; the whole
  assembly then goes through verbatim with the sets in place of the strata.
-/
import Mathlib
import Submission.Work.WilE7.bandCell_bd

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical Filter Topology

namespace Work.WilE7.SheetData

open WilkiesDesign WilkiesDesign.E
open Work.WilE7 Work.WilE7.BandAux

/-- A `Stratum` with no equations attached to a bare semi-Pfaffian set.  The band construction
only ever uses the underlying set `.X`, so this lets the stratum-level band lemmas be applied to
arbitrary semi-Pfaffian sets. -/
def dummyStratum {p q : ℕ} (X : SemiPf (p + q)) : Stratum p q := ⟨X, 0, Fin.elim0⟩

/-- The underlying set of `dummyStratum X` is `X`, definitionally. -/
@[simp] theorem dummyStratum_X {p q : ℕ} (X : SemiPf (p + q)) :
    (dummyStratum X).X = X := rfl

/-- **The two-strata band cell is a single `*`-piece** (semi-Pfaffian-set form).
Under the sheet data of `Work.WilE7.sheetAssembly` for two semi-Pfaffian sets `X₁`, `X₂` over the
base cell `C = π_p (connectedComponentIn Z.set u₀)`, the band between the sheets `s₁ i` and `s₂ j`
is the set of a single `StarPiece`, with format `≤ 4 F + 1` and degree `≤ bdBound F (1 + D)⁸`
whenever the formats of `Z`, `X₁`, `X₂` are `≤ F` and their degrees are `≤ D`. -/
theorem bandCellStar_piece_semiPf {p m F D : ℕ}
    (X₁ X₂ : SemiPf (p + (m + 1)))
    (Z : SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ) (hu₀ : u₀ ∈ Z.set)
    (C : Set (Fin p → ℝ))
    (hC : C = Set.image (projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (hCpf : SubPf p C)
    (k₁ : ℕ) (s₁ : Fin k₁ → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hcont₁ : ∀ j, ContinuousOn (s₁ j) C)
    (hinj₁ : ∀ x ∈ C, Function.Injective fun j : Fin k₁ => s₁ j x)
    (hsub₁ : ∀ j : Fin k₁, ∀ x ∈ C, Fin.append x (s₁ j x) ∈ X₁.set)
    (hcov₁ : ∀ z ∈ X₁.set, projFirst p (m + 1) z ∈ C →
      ∃ j : Fin k₁, s₁ j (projFirst p (m + 1) z) = projSnd p (m + 1) z)
    (k₂ : ℕ) (s₂ : Fin k₂ → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hcont₂ : ∀ j, ContinuousOn (s₂ j) C)
    (hinj₂ : ∀ x ∈ C, Function.Injective fun j : Fin k₂ => s₂ j x)
    (hsub₂ : ∀ j : Fin k₂, ∀ x ∈ C, Fin.append x (s₂ j x) ∈ X₂.set)
    (hcov₂ : ∀ z ∈ X₂.set, projFirst p (m + 1) z ∈ C →
      ∃ j : Fin k₂, s₂ j (projFirst p (m + 1) z) = projSnd p (m + 1) z)
    (i : Fin k₁) (j : Fin k₂)
    (hle : ∀ x ∈ C, (s₁ i x) (Fin.last m) < (s₂ j x) (Fin.last m))
    (hZf : Z.fmt ≤ F) (hX1f : X₁.fmt ≤ F) (hX2f : X₂.fmt ≤ F)
    (hZd : Z.deg ≤ D) (hX1d : X₁.deg ≤ D) (hX2d : X₂.deg ≤ D) :
    ∃ P : StarPiece (p + 1),
      P.set = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
        (s₁ i (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
        y (Fin.last p) < (s₂ j (Fin.init y)) (Fin.last m)} ∧
      P.X.fmt ≤ 4 * F + 1 ∧ P.X.deg ≤ bdBound F * (1 + D) ^ 8 := by
  classical
  have _ := hCpf
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
      ∈ (bandS3two Z (dummyStratum X₁) (dummyStratum X₂)).set :=
    bandPt_mem_two Z (dummyStratum X₁) (dummyStratum X₂) u₀ hu₀ _ _ t₀
      (hsub₁ i _ hx₀C) (hsub₂ j _ hx₀C) ht₀cube ht₀ ht₀'
  set p₀ : Fin (bandDim p m) → ℝ :=
    bandPt u₀ (s₁ i (projFirst p (m + 1) u₀)) (s₂ j (projFirst p (m + 1) u₀)) t₀ with hp₀def
  set O : Set (Fin (bandDim p m) → ℝ) :=
    connectedComponentIn (bandS3two Z (dummyStratum X₁) (dummyStratum X₂)).set p₀ with hOdef
  -- the coordinate permutation and the `*`-piece
  obtain ⟨e, he⟩ := bandPerm p m
  have he' : ∀ y : Fin ((p + 1) + bandFib p m) → ℝ,
      projFirst (p + 1) (bandFib p m) y = bandExtract (pullHomeo e y) := fun y => he y
  set P : StarPiece (p + 1) :=
    ⟨bandFib p m, SemiPf.reindex e (bandS3two Z (dummyStratum X₁) (dummyStratum X₂)),
      (pullHomeo e).symm p₀⟩ with hPdef
  have hPset : P.set = bandExtract '' O := by
    have hc := sp_reindex_component e (bandS3two Z (dummyStratum X₁) (dummyStratum X₂)) p₀
    show projFirst (p + 1) (bandFib p m) ''
        connectedComponentIn
          (SemiPf.reindex e (bandS3two Z (dummyStratum X₁) (dummyStratum X₂))).set
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
      (bandS3two_mem_iff Z (dummyStratum X₁) (dummyStratum X₂) w).mp
        (connectedComponentIn_subset _ _ hw)
    obtain ⟨hsi, hsj⟩ :=
      bandCompTwo_sheets (dummyStratum X₁) (dummyStratum X₂) Z u₀ C hC
        k₁ s₁ hcont₁ hinj₁ hsub₁ hcov₁ k₂ s₂ hcont₂ hinj₂ hsub₂ hcov₂ i j t₀ hp₀ w hw
    have hbase : bandBase w ∈ C :=
      bandCompTwo_base (dummyStratum X₁) (dummyStratum X₂) Z u₀ C hC
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
    exact bandCompTwo_cover (dummyStratum X₁) (dummyStratum X₂) Z u₀ C hC
      k₁ s₁ hcont₁ hsub₁ k₂ s₂ hcont₂ hsub₂ i j t₀ hp₀ hle y hy1 hy2 hy3
  have hband : bandExtract '' O = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
      (s₁ i (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
      y (Fin.last p) < (s₂ j (Fin.init y)) (Fin.last m)} :=
    Set.Subset.antisymm hOsub hOsup
  have hbd :=
    bandS3two_bd Z (dummyStratum X₁) (dummyStratum X₂) F D hZf hX1f hX2f hZd hX1d hX2d
  refine ⟨P, hPset.trans hband, ?_, ?_⟩
  · show (SemiPf.reindex e (bandS3two Z (dummyStratum X₁) (dummyStratum X₂))).fmt ≤ 4 * F + 1
    rw [bandS3two_reindex_fmt]
    exact hbd.1
  · show (SemiPf.reindex e (bandS3two Z (dummyStratum X₁) (dummyStratum X₂))).deg
        ≤ bdBound F * (1 + D) ^ 8
    rw [sp_reindex_deg]
    exact hbd.2

theorem bandCell_bd (F : ℕ) :
    ∃ (A : ℕ) (Cb : Polynomial ℕ), ∀ (p m : ℕ) (X₁ X₂ : WilkiesDesign.E.SemiPf (p + (m + 1)))
      (Z : WilkiesDesign.E.SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ) (hu₀ : u₀ ∈ Z.set)
      (C : Set (Fin p → ℝ))
      (hC : C = Set.image (WilkiesDesign.E.projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
      (hCpf : WilkiesDesign.E.SubPf p C)
      (k₁ : ℕ) (s₁ : Fin k₁ → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
      (hcont₁ : ∀ j, ContinuousOn (s₁ j) C)
      (hinj₁ : ∀ x ∈ C, Function.Injective fun j : Fin k₁ => s₁ j x)
      (hsub₁ : ∀ j : Fin k₁, ∀ x ∈ C, Fin.append x (s₁ j x) ∈ X₁.set)
      (hcov₁ : ∀ z ∈ X₁.set, WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
        ∃ j : Fin k₁, s₁ j (WilkiesDesign.E.projFirst p (m + 1) z) =
          WilkiesDesign.E.projSnd p (m + 1) z)
      (k₂ : ℕ) (s₂ : Fin k₂ → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
      (hcont₂ : ∀ j, ContinuousOn (s₂ j) C)
      (hinj₂ : ∀ x ∈ C, Function.Injective fun j : Fin k₂ => s₂ j x)
      (hsub₂ : ∀ j : Fin k₂, ∀ x ∈ C, Fin.append x (s₂ j x) ∈ X₂.set)
      (hcov₂ : ∀ z ∈ X₂.set, WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
        ∃ j : Fin k₂, s₂ j (WilkiesDesign.E.projFirst p (m + 1) z) =
          WilkiesDesign.E.projSnd p (m + 1) z)
      (i : Fin k₁) (j : Fin k₂)
      (hle : ∀ x ∈ C, (s₁ i x) (Fin.last m) < (s₂ j x) (Fin.last m)) (D : ℕ),
      X₁.fmt ≤ F → X₂.fmt ≤ F → Z.fmt ≤ F → X₁.deg ≤ D → X₂.deg ≤ D → Z.deg ≤ D →
      ∃ P : WilkiesDesign.E.StarPiece (p + 1),
        P.set = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
          (s₁ i (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
          y (Fin.last p) < (s₂ j (Fin.init y)) (Fin.last m)} ∧
        P.X.fmt ≤ A ∧ P.X.deg ≤ Cb.eval D := by
  refine ⟨4 * F + 1, Polynomial.C (bdBound F) * (1 + Polynomial.X) ^ 8, ?_⟩
  intro p m X₁ X₂ Z u₀ hu₀ C hC hCpf
    k₁ s₁ hcont₁ hinj₁ hsub₁ hcov₁ k₂ s₂ hcont₂ hinj₂ hsub₂ hcov₂ i j hle D
    hF₁ hF₂ hFZ hD₁ hD₂ hDZ
  obtain ⟨P, hPset, hPfmt, hPdeg⟩ :=
    bandCellStar_piece_semiPf X₁ X₂ Z u₀ hu₀ C hC hCpf
      k₁ s₁ hcont₁ hinj₁ hsub₁ hcov₁ k₂ s₂ hcont₂ hinj₂ hsub₂ hcov₂ i j hle
      hFZ hF₁ hF₂ hDZ hD₁ hD₂
  refine ⟨P, hPset, hPfmt, ?_⟩
  have hev : (Polynomial.C (bdBound F) * (1 + Polynomial.X) ^ 8 : Polynomial ℕ).eval D
      = bdBound F * (1 + D) ^ 8 := by simp
  rw [hev]
  exact hPdeg

end Work.WilE7.SheetData
