import Mathlib
import Submission.Work.ThomBordism.nwtDefs
import Submission.Work.Tubular.totalSpace_mapFibre_homeo
import Submission.Work.Agree.whitneySumRAssoc
import Submission.Work.Agree.complexificationIso
import Submission.Work.Whitney.whitneySumFormula
import Submission.Work.Whitney.two_smul_pontryagin1_whitneySumR
import Submission.Work.Whitney.two_smul_pontryagin2_whitneySumR
import Submission.Work.Thom.trivialChern

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open scoped Manifold ContDiff Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Work.ThomBordism

open Work.ThomBordism.PontryaginThom Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B]

/-! ## The Whitney formula in degrees `2` and `4` over a paracompact Hausdorff base -/

/-- **Additivity of `p₁` under a real Whitney sum, modulo `2`-torsion.**  This is
`Work.Whitney.two_smul_pontryagin1_whitneySumR` with its degree-`2` Whitney-formula hypothesis
discharged by `Work.Whitney.chernClass_whitneySum_paracompact`. -/
theorem two_smul_pontryagin1_whitneySumR_par
    [ParacompactSpace B] [T2Space B]
    {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] {k l : ℕ}
    (E : VectorBundleCore ℝ B (Euc k) ι₁) (F : VectorBundleCore ℝ B (Euc l) ι₂) :
    (2 : ℤ) • Work.Thom.pontryagin1 (Work.Whitney.whitneySumR E F)
      = (2 : ℤ) • (Work.Thom.pontryagin1 E + Work.Thom.pontryagin1 F) := by
  rw [Work.Thom.pontryagin1_def, Work.Thom.pontryagin1_def, Work.Thom.pontryagin1_def,
    Work.Whitney.complexificationCore_whitneySumR]
  rw [Work.Whitney.chernClass_whitneySum_paracompact
        (Work.Thom.complexificationCore E) (Work.Thom.complexificationCore F) 2,
      Work.Whitney.chernProductSum_two_eq (Work.Thom.complexificationCore E)
        (Work.Thom.complexificationCore F)]
  have hx : Work.Thom.chernClass k 1 (Work.Thom.complexificationCore E)
      + Work.Thom.chernClass k 1 (Work.Thom.complexificationCore E) = 0 :=
    Work.Whitney.chernClass_complexification_add_self (B := B) (k := k) (j := 1) (by decide) E
  have hcup : Work.Whitney.cupChern 1 1
        (Work.Thom.chernClass k 1 (Work.Thom.complexificationCore E))
        (Work.Thom.chernClass l 1 (Work.Thom.complexificationCore F))
      + Work.Whitney.cupChern 1 1
        (Work.Thom.chernClass k 1 (Work.Thom.complexificationCore E))
        (Work.Thom.chernClass l 1 (Work.Thom.complexificationCore F)) = 0 := by
    rw [← Work.Whitney.cupChern_add_left, hx, Work.Whitney.cupChern_zero_left]
  exact Work.Whitney.two_zsmul_neg_add_cancel _ _ _ hcup

/-- **Additivity of `p₂` under a real Whitney sum, modulo `2`-torsion.**  This is
`Work.Whitney.two_smul_pontryagin2_whitneySumR` with its degree-`4` Whitney-formula hypothesis
discharged by `Work.Whitney.chernClass_whitneySum_paracompact`. -/
theorem two_smul_pontryagin2_whitneySumR_par
    [ParacompactSpace B] [T2Space B]
    {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] {k l : ℕ}
    (E : VectorBundleCore ℝ B (Euc k) ι₁) (F : VectorBundleCore ℝ B (Euc l) ι₂) :
    (2 : ℤ) • Work.Thom.pontryaginClass 2 (Work.Whitney.whitneySumR E F)
      = (2 : ℤ) • (Work.Thom.pontryaginClass 2 E
          + Work.Whitney.cupChern 2 2 (Work.Thom.pontryagin1 E) (Work.Thom.pontryagin1 F)
          + Work.Thom.pontryaginClass 2 F) := by
  rw [Work.Whitney.pontryaginClass_two_eq (Work.Whitney.whitneySumR E F),
    Work.Whitney.complexificationCore_whitneySumR E F,
    Work.Whitney.chernClass_whitneySum_paracompact
      (Work.Thom.complexificationCore E) (Work.Thom.complexificationCore F) 4]
  rw [Work.Whitney.two_smul_chernProductSum_four_complexification E F]
  have hB : Work.Whitney.cupChern 2 2
        (Work.Thom.chernClass k 2 (Work.Thom.complexificationCore E))
        (Work.Thom.chernClass l 2 (Work.Thom.complexificationCore F))
      = Work.Whitney.cupChern 2 2 (Work.Thom.pontryagin1 E) (Work.Thom.pontryagin1 F) := by
    rw [Work.Thom.pontryagin1_def E, Work.Thom.pontryagin1_def F,
      Work.Whitney.cupChern_neg_left, Work.Whitney.cupChern_neg_right, neg_neg]
  have hmain : Work.Thom.chernClass k 4 (Work.Thom.complexificationCore E)
        + Work.Whitney.cupChern 2 2 (Work.Thom.chernClass k 2 (Work.Thom.complexificationCore E))
            (Work.Thom.chernClass l 2 (Work.Thom.complexificationCore F))
        + Work.Thom.chernClass l 4 (Work.Thom.complexificationCore F)
      = Work.Thom.pontryaginClass 2 E
        + Work.Whitney.cupChern 2 2 (Work.Thom.pontryagin1 E) (Work.Thom.pontryagin1 F)
        + Work.Thom.pontryaginClass 2 F := by
    rw [hB, ← Work.Whitney.pontryaginClass_two_eq E, ← Work.Whitney.pontryaginClass_two_eq F]
  rw [hmain]

/-! ## The two consequences for a trivial sum -/

/-- **`2 • (p₁ Z + p₁ W) = 0` when `Z ⊕ W` is trivial.** -/
theorem two_smul_pontryagin1_eq_zero_of_sum_trivial
    [ParacompactSpace B] [T2Space B]
    {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] {k₁ k₂ : ℕ}
    (Z : RealBundle B (Euc k₁) ι₁) (W : RealBundle B (Euc k₂) ι₂)
    (h : Nonempty (BundleIso (Work.Whitney.whitneySumR Z W)
      (RealBundle.trivial B (Euc (k₁ + k₂)) Unit))) :
    (2 : ℤ) • (Work.Thom.pontryagin1 Z + Work.Thom.pontryagin1 W) = 0 := by
  have h1 := two_smul_pontryagin1_whitneySumR_par (B := B) Z W
  obtain ⟨e⟩ := h
  have h3 := Work.Agree.chernClass_complexificationCore_eq (rfl : k₁ + k₂ = k₁ + k₂)
    (Work.Whitney.whitneySumR Z W) (RealBundle.trivial B (Euc (k₁ + k₂)) Unit) e 2
  have h2 : Work.Thom.pontryagin1 (Work.Whitney.whitneySumR Z W) = 0 := by
    rw [Work.Thom.pontryagin1_def, h3, ← Work.Thom.pontryagin1_def]
    exact Work.Thom.pontryagin1_trivial (B := B) (k := k₁ + k₂) (ι := Unit)
  have h1' : (2 : ℤ) • (Work.Thom.pontryagin1 Z + Work.Thom.pontryagin1 W) = 0 := by
    rw [← h1, h2]
    rw [two_zsmul, add_zero]
  exact h1'

/-- **`2 • (p₂ Z + p₁ Z ⌣ p₁ W + p₂ W) = 0` when `Z ⊕ W` is trivial.** -/
theorem two_smul_pontryagin2_eq_zero_of_sum_trivial
    [ParacompactSpace B] [T2Space B]
    {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] {k₁ k₂ : ℕ}
    (Z : RealBundle B (Euc k₁) ι₁) (W : RealBundle B (Euc k₂) ι₂)
    (h : Nonempty (BundleIso (Work.Whitney.whitneySumR Z W)
      (RealBundle.trivial B (Euc (k₁ + k₂)) Unit))) :
    (2 : ℤ) • (Work.Thom.pontryaginClass 2 Z
        + Work.Whitney.cupChern 2 2 (Work.Thom.pontryagin1 Z) (Work.Thom.pontryagin1 W)
        + Work.Thom.pontryaginClass 2 W) = 0 := by
  have h1 := two_smul_pontryagin2_whitneySumR_par (B := B) Z W
  obtain ⟨e⟩ := h
  have h3 := Work.Agree.chernClass_complexificationCore_eq (rfl : k₁ + k₂ = k₁ + k₂)
    (Work.Whitney.whitneySumR Z W) (RealBundle.trivial B (Euc (k₁ + k₂)) Unit) e 4
  have h2 : Work.Thom.pontryaginClass 2 (Work.Whitney.whitneySumR Z W) = 0 := by
    rw [Work.Whitney.pontryaginClass_two_eq, h3, ← Work.Whitney.pontryaginClass_two_eq]
    exact Work.Thom.pontryaginClass_trivial (B := B) 2 (k := k₁ + k₂) (ι := Unit) (by norm_num)
  have h1' : (2 : ℤ) • (Work.Thom.pontryaginClass 2 Z
        + Work.Whitney.cupChern 2 2 (Work.Thom.pontryagin1 Z) (Work.Thom.pontryagin1 W)
        + Work.Thom.pontryaginClass 2 W) = 0 := by
    rw [← h1, h2]
    rw [two_zsmul, add_zero]
  exact h1'

/-! ## `p₁`, `p₂` of the two presentations of the tangent bundle -/

/-- `Zt1 = Zt0.mapFibre` up to the fibre transport, so the Pontryagin classes agree. -/
theorem pontryagin1_Zt1_eq_Zt0 (V : Work.ThomBordism.Man8) :
    Work.Thom.pontryagin1 (Zt1 V) = Work.Thom.pontryagin1 (Zt0 V) := by
  have h := Work.Agree.chernClass_complexificationCore_eq
    (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 8))
    (Zt1 V) (Zt0 V)
    (Work.Tubular.bundleIsoMapFibre (Work.Thom.modelLinearEquiv (E := Euc 8)) (Zt0 V)).symm 2
  rw [Work.Thom.pontryagin1_def, Work.Thom.pontryagin1_def, h]

/-- The second Pontryagin class of `Zt1`, as `c₄` of its complexification. -/
theorem chernClass_Zt1_eq_Zt0 (V : Work.ThomBordism.Man8) :
    Work.Thom.chernClass (Module.finrank ℝ (Euc 8)) 4
        (Work.Thom.complexificationCore (Zt1 V))
      = Work.Thom.chernClass 8 4 (Work.Thom.complexificationCore (Zt0 V)) :=
  Work.Agree.chernClass_complexificationCore_eq
    (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 8))
    (Zt1 V) (Zt0 V)
    (Work.Tubular.bundleIsoMapFibre (Work.Thom.modelLinearEquiv (E := Euc 8)) (Zt0 V)).symm 4

end

end Work.ThomBordism
