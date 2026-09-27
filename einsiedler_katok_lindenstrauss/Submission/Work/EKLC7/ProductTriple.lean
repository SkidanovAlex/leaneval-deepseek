import Mathlib
import Submission.Work.EKLC7.Defs
import Submission.Work.EKLC7.HeisMul
import Submission.Work.EKLC7.HeisShift
import Submission.Work.EKLC7.Horo
import Submission.Work.EKLC7.ProductInstances
import Submission.Work.EKLC7.HeisFactor
import Submission.Work.EKLC7.TripleCollapse

/-!
# C7: the two triple product formulae for the Heisenberg leafwise measure

Let `μ` be an `A`-invariant probability measure on `X₃ = SL₃(ℝ)/SL₃(ℤ)`, `i, j, k : Fin 3`
pairwise distinct, and let `νN, νij, νjk, νik, νV1, νV2` be the leafwise measures of `μ` along
`Heis3 = U_ij ⊔ U_jk ⊔ U_ik`, `U_ij`, `U_jk`, `U_ik`, `VjkIk = U_jk ⊔ U_ik` and
`VijIk = U_ij ⊔ U_ik` respectively.

The product structure `P_Product` (Pisa Cor. 8.8) applied to the two semidirect decompositions

* `Heis3 = U_ij ⋉ VjkIk` and inside it `VjkIk = U_jk ⋉ U_ik`,
* `Heis3 = U_jk ⋉ VijIk` and inside it `VijIk = U_ij ⋉ U_ik`

expresses `νN` in the two orders `νij ⊗ νjk ⊗ νik` and `νjk ⊗ νij ⊗ νik`, which is precisely the
content of `TripleA` resp. `TripleB`; comparing the two is the heart of C7 (EKL Lemma 3.3,
Pisa 9.11).

The side conditions of `P_Product` (relative normality, the semidirect decomposition and the
triviality of the intersection) are supplied by `Work.EKLC7.HeisFactor`, the four explicit
contracting vectors by `Work.EKLC7.ProductInstances`, `IsHoro` by `Work.EKLC7.Horo`, and the
final collapse of two product formulae into a triple product by `Work.EKLC7.TripleCollapse`.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

noncomputable section

namespace Work.EKLC7

open MeasureTheory Filter Topology
open Work.EKLContract

/-! ## Inclusions of the root groups

The lattice inclusions among `U_ij`, `U_jk`, `U_ik` and their joins.  Each is stated with the
explicit join so that the (defeq-checked) matching against the abbreviations `Heis3`, `VjkIk`,
`VijIk` is cheap. -/

theorem le_Heis3_of_Uij_hij {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (Uij hij : Subgroup SL3) ≤ Heis3 hij hjk hik := by
  show (Uij hij : Subgroup SL3) ≤ (Uij hij ⊔ Uij hjk) ⊔ Uij hik
  exact le_trans le_sup_left le_sup_left

theorem le_Heis3_of_Uij_hjk {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (Uij hjk : Subgroup SL3) ≤ Heis3 hij hjk hik := by
  show (Uij hjk : Subgroup SL3) ≤ (Uij hij ⊔ Uij hjk) ⊔ Uij hik
  exact le_trans le_sup_right le_sup_left

theorem le_Heis3_of_VjkIk {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (VjkIk hjk hik : Subgroup SL3) ≤ Heis3 hij hjk hik := by
  show (Uij hjk ⊔ Uij hik : Subgroup SL3) ≤ (Uij hij ⊔ Uij hjk) ⊔ Uij hik
  exact sup_le (le_trans le_sup_right le_sup_left) le_sup_right

theorem le_Heis3_of_VijIk {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (VijIk hij hik : Subgroup SL3) ≤ Heis3 hij hjk hik := by
  show (Uij hij ⊔ Uij hik : Subgroup SL3) ≤ (Uij hij ⊔ Uij hjk) ⊔ Uij hik
  exact sup_le (le_trans le_sup_left le_sup_left) le_sup_right

theorem le_VjkIk_of_Uij_hjk {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (Uij hjk : Subgroup SL3) ≤ VjkIk hjk hik := by
  show (Uij hjk : Subgroup SL3) ≤ Uij hjk ⊔ Uij hik
  exact le_sup_left

theorem le_VjkIk_of_Uij_hik {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (Uij hik : Subgroup SL3) ≤ VjkIk hjk hik := by
  show (Uij hik : Subgroup SL3) ≤ Uij hjk ⊔ Uij hik
  exact le_sup_right

theorem le_VijIk_of_Uij_hij {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (Uij hij : Subgroup SL3) ≤ VijIk hij hik := by
  show (Uij hij : Subgroup SL3) ≤ Uij hij ⊔ Uij hik
  exact le_sup_left

theorem le_VijIk_of_Uij_hik {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (Uij hik : Subgroup SL3) ≤ VijIk hij hik := by
  show (Uij hik : Subgroup SL3) ≤ Uij hij ⊔ Uij hik
  exact le_sup_right

/-! ## The four product formulae -/

/-- The four product formulae obtained from `P_Product` in the two Heisenberg decompositions.
At the same a.e. point `x` one has, simultaneously,

* `νN x = c₁ · ∫ (∫ f (g * u) ∂νV1 x) ∂νij x` (from `Heis3 = U_ij ⋉ VjkIk`),
* `νV1 x = c₂ · ∫ (∫ f (g * u) ∂νik x) ∂νjk x` (from `VjkIk = U_jk ⋉ U_ik`),
* `νN x = c₃ · ∫ (∫ f (g * u) ∂νV2 x) ∂νjk x` (from `Heis3 = U_jk ⋉ VijIk`),
* `νV2 x = c₄ · ∫ (∫ f (g * u) ∂νik x) ∂νij x` (from `VijIk = U_ij ⋉ U_ik`). -/
theorem productFormulas (hP : Work.EKLContract.P_Product)
    (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ]
    (hμ : Work.EKLContract.IsAInvariant μ)
    {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (νij νjk νik νN νV1 νV2 :
      Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3)
    (Xi Xj Xk XN XV1 XV2 : Set Work.EKLContract.X3)
    (hLij : Work.EKLContract.IsLeafwise μ (Work.EKLContract.Uij hij) νij Xi)
    (hLjk : Work.EKLContract.IsLeafwise μ (Work.EKLContract.Uij hjk) νjk Xj)
    (hLik : Work.EKLContract.IsLeafwise μ (Work.EKLContract.Uij hik) νik Xk)
    (hLN : Work.EKLContract.IsLeafwise μ (Work.EKLC7.Heis3 hij hjk hik) νN XN)
    (hLV1 : Work.EKLContract.IsLeafwise μ (Work.EKLC7.VjkIk hjk hik) νV1 XV1)
    (hLV2 : Work.EKLContract.IsLeafwise μ (Work.EKLC7.VijIk hij hik) νV2 XV2) :
    ∀ᵐ x ∂μ,
      (∃ c : ℝ, 0 < c ∧ ∀ f : CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ,
        ∫ g, f g ∂(νN x) = c * ∫ g, (∫ u, f (g * u) ∂(νV1 x)) ∂(νij x)) ∧
      (∃ c : ℝ, 0 < c ∧ ∀ f : CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ,
        ∫ g, f g ∂(νV1 x) = c * ∫ g, (∫ u, f (g * u) ∂(νik x)) ∂(νjk x)) ∧
      (∃ c : ℝ, 0 < c ∧ ∀ f : CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ,
        ∫ g, f g ∂(νN x) = c * ∫ g, (∫ u, f (g * u) ∂(νV2 x)) ∂(νjk x)) ∧
      (∃ c : ℝ, 0 < c ∧ ∀ f : CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ,
        ∫ g, f g ∂(νV2 x) = c * ∫ g, (∫ u, f (g * u) ∂(νik x)) ∂(νij x)) := by
  obtain ⟨hHoroH, hHoroV1, hHoroV2⟩ := Horo hij hjk hik
  have e1 : ∀ᵐ x ∂μ, ∃ c : ℝ, 0 < c ∧
      ∀ f : CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ,
        ∫ g, f g ∂(νN x) = c * ∫ g, (∫ u, f (g * u) ∂(νV1 x)) ∂(νij x) :=
    hP μ hμ (Heis3 hij hjk hik) (Uij hij) (VjkIk hjk hik) hHoroH
      (Work.EKLContract.Lemmas.isHoro_Uij hij) hHoroV1
      (le_Heis3_of_Uij_hij hij hjk hik) (le_Heis3_of_VjkIk hij hjk hik)
      (prodConj1 hij hjk hik) (normalize_14 hij hjk hik)
      (split_VjkIk hij hjk hik) (disjoint_Uij_VjkIk hij hjk hik)
      νN νij νV1 XN Xi XV1 hLN hLij hLV1
  have e2 : ∀ᵐ x ∂μ, ∃ c : ℝ, 0 < c ∧
      ∀ f : CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ,
        ∫ g, f g ∂(νV1 x) = c * ∫ g, (∫ u, f (g * u) ∂(νik x)) ∂(νjk x) :=
    hP μ hμ (VjkIk hjk hik) (Uij hjk) (Uij hik) hHoroV1
      (Work.EKLContract.Lemmas.isHoro_Uij hjk) (Work.EKLContract.Lemmas.isHoro_Uij hik)
      (le_VjkIk_of_Uij_hjk hij hjk hik) (le_VjkIk_of_Uij_hik hij hjk hik)
      (prodConj3 hij hjk hik) (normalize_16 hij hjk hik)
      (split_VjkIk_2 hij hjk hik) (disjoint_Ujk_Uik hij hjk hik)
      νV1 νjk νik XV1 Xj Xk hLV1 hLjk hLik
  have e3 : ∀ᵐ x ∂μ, ∃ c : ℝ, 0 < c ∧
      ∀ f : CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ,
        ∫ g, f g ∂(νN x) = c * ∫ g, (∫ u, f (g * u) ∂(νV2 x)) ∂(νjk x) :=
    hP μ hμ (Heis3 hij hjk hik) (Uij hjk) (VijIk hij hik) hHoroH
      (Work.EKLContract.Lemmas.isHoro_Uij hjk) hHoroV2
      (le_Heis3_of_Uij_hjk hij hjk hik) (le_Heis3_of_VijIk hij hjk hik)
      (prodConj2 hij hjk hik) (normalize_15 hij hjk hik)
      (split_VijIk hij hjk hik) (disjoint_Ujk_VijIk hij hjk hik)
      νN νjk νV2 XN Xj XV2 hLN hLjk hLV2
  have e4 : ∀ᵐ x ∂μ, ∃ c : ℝ, 0 < c ∧
      ∀ f : CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ,
        ∫ g, f g ∂(νV2 x) = c * ∫ g, (∫ u, f (g * u) ∂(νik x)) ∂(νij x) :=
    hP μ hμ (VijIk hij hik) (Uij hij) (Uij hik) hHoroV2
      (Work.EKLContract.Lemmas.isHoro_Uij hij) (Work.EKLContract.Lemmas.isHoro_Uij hik)
      (le_VijIk_of_Uij_hij hij hjk hik) (le_VijIk_of_Uij_hik hij hjk hik)
      (prodConj4 hij hjk hik) (normalize_17 hij hjk hik)
      (split_VijIk_2 hij hjk hik) (disjoint_Uij_Uik hij hjk hik)
      νV2 νij νik XV2 Xi Xk hLV2 hLij hLik
  filter_upwards [e1, e2, e3, e4] with x h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

/-! ## The triple product formulae -/

theorem ProductTriple :
    Work.EKLContract.P_Product →
    ∀ (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ],
      Work.EKLContract.IsAInvariant μ →
      ∀ {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
        (νij νjk νik νN νV1 νV2 : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3)
        (Xi Xj Xk XN XV1 XV2 : Set Work.EKLContract.X3),
        Work.EKLContract.IsLeafwise μ (Work.EKLContract.Uij hij) νij Xi →
        Work.EKLContract.IsLeafwise μ (Work.EKLContract.Uij hjk) νjk Xj →
        Work.EKLContract.IsLeafwise μ (Work.EKLContract.Uij hik) νik Xk →
        Work.EKLContract.IsLeafwise μ (Work.EKLC7.Heis3 hij hjk hik) νN XN →
        Work.EKLContract.IsLeafwise μ (Work.EKLC7.VjkIk hjk hik) νV1 XV1 →
        Work.EKLContract.IsLeafwise μ (Work.EKLC7.VijIk hij hik) νV2 XV2 →
        ∀ᵐ x ∂μ, ∃ cA : ℝ, 0 < cA ∧ ∃ cB : ℝ, 0 < cB ∧
          Work.EKLC7.TripleA (νN x) (νij x) (νjk x) (νik x) cA ∧
          Work.EKLC7.TripleB (νN x) (νij x) (νjk x) (νik x) cB := by
  intro hP μ hprob hμ i j k hij hjk hik νij νjk νik νN νV1 νV2
    Xi Xj Xk XN XV1 XV2 hLij hLjk hLik hLN hLV1 hLV2
  haveI : MeasureTheory.IsProbabilityMeasure μ := hprob
  filter_upwards [productFormulas hP μ hμ hij hjk hik νij νjk νik νN νV1 νV2
    Xi Xj Xk XN XV1 XV2 hLij hLjk hLik hLN hLV1 hLV2] with x hx
  obtain ⟨h1, h2, h3, h4⟩ := hx
  obtain ⟨⟨cA, hcA, hTA⟩, ⟨cB, hcB, hTB⟩⟩ :=
    TripleCollapse (νN := νN x) (νij := νij x) (νjk := νjk x) (νik := νik x)
      (νV1 := νV1 x) (νV2 := νV2 x) h1 h2 h3 h4
  exact ⟨cA, hcA, cB, hcB, hTA, hTB⟩

end Work.EKLC7
