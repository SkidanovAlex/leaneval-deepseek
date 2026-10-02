import Mathlib
import Submission.Work.Whitney.WBData
import Submission.Work.Whitney.SectionStability

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Whitney
namespace WB

open Work.TangentClasses Work.Thom

noncomputable section

variable {Y : Type} [TopologicalSpace Y]
variable {ι_A ι_B : Type} [Fintype ι_A] [Fintype ι_B]
variable {r s : ℕ}

/-! ## The fibrewise gauge and its inverse -/

/-- The pair `(quotient by the line, second summand)` on the standard splitting of the sum. -/
def homPair (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B) (σ : PunctC A)
    (hσ : IsSec A σ) (y : Y) :
    (EuclideanSpace ℂ (Fin (r + 1)) × EuclideanSpace ℂ (Fin (s + 1))) →L[ℂ]
      (EuclideanSpace ℂ (Fin r) × EuclideanSpace ℂ (Fin (s + 1))) :=
  (quoCLM (secIdx r A σ y) (secA r A σ y)).prodMap
    (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin (s + 1))))

theorem homPair_apply (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B) (σ : PunctC A)
    (hσ : IsSec A σ) (y : Y)
    (v : EuclideanSpace ℂ (Fin (r + 1)) × EuclideanSpace ℂ (Fin (s + 1))) :
    homPair r s A B σ hσ y v = (quoFun (secIdx r A σ y) (secA r A σ y) v.1, v.2) := rfl

/-- **The fibrewise map** `X_y → W_y`: read the class in the chart of the section, split off the
`A`-part along the line `ℂ·σ_y` and keep the `B`-part. -/
def homCLM (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B) (σ : PunctC A)
    (hσ : IsSec A σ) (y : Y) :
    EuclideanSpace ℂ (Fin ((r + 1) + s)) →L[ℂ] EuclideanSpace ℂ (Fin (r + (s + 1))) :=
  (joinQuotCLM r s).comp
    ((homPair r s A B σ hσ y).comp
      ((splitSumCLM r s).comp (fillCLM (idxSum r s A B σ hσ y))))

theorem homCLM_apply (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B) (σ : PunctC A)
    (hσ : IsSec A σ) (y : Y) (z : EuclideanSpace ℂ (Fin ((r + 1) + s))) :
    homCLM r s A B σ hσ y z
      = joinQuotCLM r s
          (quoFun (secIdx r A σ y) (secA r A σ y)
              (((splitSumCLM r s) (fillFun (idxSum r s A B σ hσ y) z)).1),
            ((splitSumCLM r s) (fillFun (idxSum r s A B σ hσ y) z)).2) := rfl

/-- The map filling the `A`-coordinate and keeping the `B`-coordinate. -/
def invPair (r s : ℕ) (A : BunC Y (r + 1) ι_A) (σ : PunctC A) (y : Y) :
    (EuclideanSpace ℂ (Fin r) × EuclideanSpace ℂ (Fin (s + 1))) →L[ℂ]
      (EuclideanSpace ℂ (Fin (r + 1)) × EuclideanSpace ℂ (Fin (s + 1))) :=
  ContinuousLinearMap.prodMap (fillCLM (secIdx r A σ y))
    (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin (s + 1))))

theorem invPair_apply (r s : ℕ) (A : BunC Y (r + 1) ι_A) (σ : PunctC A) (y : Y)
    (v : EuclideanSpace ℂ (Fin r) × EuclideanSpace ℂ (Fin (s + 1))) :
    invPair r s A σ y v = (fillFun (secIdx r A σ y) v.1, v.2) := rfl

/-- **The fibrewise inverse** `W_y → X_y`: fill the quotient class at the coordinate of the section
and re-read it in the chart of the section. -/
def invCLM (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B) (σ : PunctC A)
    (hσ : IsSec A σ) (y : Y) :
    EuclideanSpace ℂ (Fin (r + (s + 1))) →L[ℂ] EuclideanSpace ℂ (Fin ((r + 1) + s)) :=
  (quoCLM (idxSum r s A B σ hσ y) (aFull r s A B σ hσ y)).comp
    ((joinSumCLM r s).comp ((invPair r s A σ y).comp (splitQuotCLM r s)))

theorem invCLM_apply (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B) (σ : PunctC A)
    (hσ : IsSec A σ) (y : Y) (u : EuclideanSpace ℂ (Fin (r + (s + 1)))) :
    invCLM r s A B σ hσ y u
      = quoFun (idxSum r s A B σ hσ y) (aFull r s A B σ hσ y)
          (joinSumCLM r s
            (fillFun (secIdx r A σ y) ((splitQuotCLM r s) u).1,
              ((splitQuotCLM r s) u).2)) := rfl

/-! ## The two fibrewise maps are mutually inverse -/

/-- `quoFun` is unchanged by adding a multiple of the line it quotients by. -/
theorem quoFun_add_smul {n : ℕ} (k : Fin (n + 1)) (w u : EuclideanSpace ℂ (Fin (n + 1)))
    (c : ℂ) (hw : w k ≠ 0) : quoFun k w (u + c • w) = quoFun k w u := by
  have h : u + c • w = u - (-c) • w := by rw [neg_smul, sub_neg_eq_add]
  rw [h, quoFun_sub_smul_self k w u (-c) hw]

theorem splitSumCLM_secA_zero (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B)
    (σ : PunctC A) (hσ : IsSec A σ) (y : Y) :
    splitSumCLM r s (aFull r s A B σ hσ y) = (secA r A σ y, 0) := by
  rw [aFull_apply, sumIncl_apply, splitSumCLM_apply]

theorem aFull_ne_zero (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B)
    (σ : PunctC A) (hσ : IsSec A σ) (y : Y) : aFull r s A B σ hσ y ≠ 0 := by
  rw [aFull_apply]
  exact sumIncl_ne_zero (secA_ne_zero r A σ y)

theorem invCLM_homCLM (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B) (σ : PunctC A)
    (hσ : IsSec A σ) (y : Y) (z : EuclideanSpace ℂ (Fin ((r + 1) + s))) :
    invCLM r s A B σ hσ y (homCLM r s A B σ hσ y z) = z := by
  obtain ⟨v, w, hsplit⟩ :
      ∃ v w, (splitSumCLM r s) (fillFun (idxSum r s A B σ hσ y) z) = (v, w) := ⟨_, _, rfl⟩
  have haK : aFull r s A B σ hσ y (idxSum r s A B σ hσ y) ≠ 0 := idxSum_spec r s A B σ hσ y
  have hsub : fillFun (secIdx r A σ y) (quoFun (secIdx r A σ y) (secA r A σ y) v)
      = v - (v (secIdx r A σ y) / (secA r A σ y) (secIdx r A σ y)) • secA r A σ y := by
    rw [eq_sub_iff_add_eq]
    exact (sub_eq_iff_eq_add'.mp (sub_fillFun_quoFun (secIdx r A σ y) (secA r A σ y) v
      (secA_secIdx_ne_zero r A σ hσ y))).symm
  have hsplit_join : sumFibreC (r + 1) (s + 1) (v, w) = fillFun (idxSum r s A B σ hσ y) z := by
    have h1 : sumFibreC (r + 1) (s + 1) (v, w)
        = sumFibreC (r + 1) (s + 1)
            ((splitSumCLM r s) (fillFun (idxSum r s A B σ hσ y) z)) := by
      rw [hsplit]
    rw [h1, sumFibreC_splitSum]
  have hkey : sumFibreC (r + 1) (s + 1)
        (fillFun (secIdx r A σ y) (quoFun (secIdx r A σ y) (secA r A σ y) v), w)
      = fillFun (idxSum r s A B σ hσ y) z
        - (v (secIdx r A σ y) / (secA r A σ y) (secIdx r A σ y)) • aFull r s A B σ hσ y := by
    rw [hsub]
    rw [show (v - (v (secIdx r A σ y) / (secA r A σ y) (secIdx r A σ y)) • secA r A σ y, w)
        = (v, w) - (v (secIdx r A σ y) / (secA r A σ y) (secIdx r A σ y)) •
            (secA r A σ y, 0) from by simp]
    rw [map_sub, map_smul, sumFibreC_secA_zero r s A B σ hσ y, hsplit_join]
  rw [homCLM_apply, invCLM_apply]
  simp only [joinQuotCLM_apply, splitQuotCLM_apply]
  rw [show (splitSumCLM r s) (fillFun (idxSum r s A B σ hσ y) z) = (v, w) from hsplit]
  simp only [joinSumCLM_apply]
  rw [hkey, quoFun_sub_smul_self _ _ _ _ haK, quoFun_fillFun _ _ _ haK]

theorem homCLM_invCLM (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B) (σ : PunctC A)
    (hσ : IsSec A σ) (y : Y) (u : EuclideanSpace ℂ (Fin (r + (s + 1)))) :
    homCLM r s A B σ hσ y (invCLM r s A B σ hσ y u) = u := by
  obtain ⟨ζ, μ, hsplit⟩ : ∃ ζ μ, (splitQuotCLM r s) u = (ζ, μ) := ⟨_, _, rfl⟩
  have haK : aFull r s A B σ hσ y (idxSum r s A B σ hσ y) ≠ 0 :=
    idxSum_spec r s A B σ hσ y
  set E : EuclideanSpace ℂ (Fin ((r + 1) + (s + 1))) :=
    sumFibreC (r + 1) (s + 1) (fillFun (secIdx r A σ y) ζ, μ) with hE
  have hfill : fillFun (idxSum r s A B σ hσ y) (invCLM r s A B σ hσ y u)
      = E - (E (idxSum r s A B σ hσ y) / aFull r s A B σ hσ y (idxSum r s A B σ hσ y))
          • aFull r s A B σ hσ y := by
    rw [invCLM_apply]
    simp only [joinSumCLM_apply, splitQuotCLM_apply, hsplit, ← hE]
    rw [eq_sub_iff_add_eq]
    exact (sub_eq_iff_eq_add'.mp (sub_fillFun_quoFun (idxSum r s A B σ hσ y)
      (aFull r s A B σ hσ y) E haK)).symm
  have hsplit2 : (splitSumCLM r s)
      (fillFun (idxSum r s A B σ hσ y) (invCLM r s A B σ hσ y u))
      = (fillFun (secIdx r A σ y) ζ
          - (E (idxSum r s A B σ hσ y) / aFull r s A B σ hσ y (idxSum r s A B σ hσ y))
              • secA r A σ y, μ) := by
    rw [hfill, map_sub, map_smul]
    simp only [hE, splitSumCLM_apply, splitSumCLM_secA_zero r s A B σ hσ y]
    simp
  have hq : quoFun (secIdx r A σ y) (secA r A σ y)
      (fillFun (secIdx r A σ y) ζ
        - (E (idxSum r s A B σ hσ y) / aFull r s A B σ hσ y (idxSum r s A B σ hσ y))
            • secA r A σ y)
      = ζ := by
    rw [quoFun_sub_smul_self _ _ _ _ (secA_secIdx_ne_zero r A σ hσ y)]
    exact quoFun_fillFun (secIdx r A σ y) (secA r A σ y) ζ (secA_secIdx_ne_zero r A σ hσ y)
  rw [homCLM_apply, hsplit2]
  simp only [joinQuotCLM_apply]
  rw [hq, ← hsplit, sumFibreC_splitQuot]

/-! ## Base-set memberships -/

theorem sumSection_proj' (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B)
    (σ : PunctC A) (hσ : IsSec A σ) (y : Y) :
    (((sumSection r s A B σ hσ y : ↥(zeroComplement (realification (SumB r s A B)))) :
      (realification (SumB r s A B)).TotalSpace)).proj = y :=
  sumSection_proj r s A B σ hσ y

theorem sumSection_snd' (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B)
    (σ : PunctC A) (hσ : IsSec A σ) (y : Y) :
    (((sumSection r s A B σ hσ y : ↥(zeroComplement (realification (SumB r s A B)))) :
      (realification (SumB r s A B)).TotalSpace)).snd = aFull r s A B σ hσ y := rfl

/-- The set on which the chart expression of the forward gauge is studied. -/
abbrev homSet (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B) (σ : PunctC A)
    (hσ : IsSec A σ) (i₁ : (ι_A × ι_B) × Fin ((r + 1) + (s + 1)))
    (i₂ : (ι_A × Fin (r + 1)) × ι_B) : Set Y :=
  (Xb r s A B σ hσ).baseSet i₁ ∩ (Wb r s A B σ).baseSet i₂

theorem mem_Xb_sum (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B) (σ : PunctC A)
    (hσ : IsSec A σ) (i₁ : (ι_A × ι_B) × Fin ((r + 1) + (s + 1))) {y : Y}
    (hy : y ∈ (Xb r s A B σ hσ).baseSet i₁) :
    y ∈ (SumB r s A B).baseSet i₁.1 := by
  obtain ⟨i₁AB, i₁K⟩ := i₁
  have h1 : sumSection r s A B σ hσ y ∈ (tautQuotient (SumB r s A B)).baseSet (i₁AB, i₁K) := hy
  rw [tautQuotient_baseSet] at h1
  have h2 : (((sumSection r s A B σ hσ y : ↥(zeroComplement (realification (SumB r s A B)))) :
      (realification (SumB r s A B)).TotalSpace)).proj ∈ (SumB r s A B).baseSet i₁AB := h1.1
  rwa [sumSection_proj' r s A B σ hσ y] at h2

theorem mem_Xb_coord (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B) (σ : PunctC A)
    (hσ : IsSec A σ) (i₁ : (ι_A × ι_B) × Fin ((r + 1) + (s + 1))) {y : Y}
    (hy : y ∈ (Xb r s A B σ hσ).baseSet i₁) :
    ((SumB r s A B).localTriv i₁.1 (((sumSection r s A B σ hσ y :
      ↥(zeroComplement (realification (SumB r s A B)))) :
      (realification (SumB r s A B)).TotalSpace))).2 i₁.2 ≠ 0 := by
  obtain ⟨i₁AB, i₁K⟩ := i₁
  have h1 : sumSection r s A B σ hσ y ∈ (tautQuotient (SumB r s A B)).baseSet (i₁AB, i₁K) := hy
  rw [tautQuotient_baseSet] at h1
  have h2 : (((SumB r s A B).localTriv i₁AB (((sumSection r s A B σ hσ y :
      ↥(zeroComplement (realification (SumB r s A B)))) :
      (realification (SumB r s A B)).TotalSpace))).2 i₁K ≠ 0) := h1.2
  exact h2

theorem mem_sum_A (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B)
    (i : ι_A × ι_B) : (SumB r s A B).baseSet i ⊆ A.baseSet i.1 := by
  intro y hy
  rw [whitneySum_baseSet] at hy
  exact hy.1

theorem mem_sum_B (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B)
    (i : ι_A × ι_B) : (SumB r s A B).baseSet i ⊆ B.baseSet i.2 := by
  intro y hy
  rw [whitneySum_baseSet] at hy
  exact hy.2

theorem mem_Wb_Q (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B) (σ : PunctC A)
    (i₂ : (ι_A × Fin (r + 1)) × ι_B) :
    (Wb r s A B σ).baseSet i₂ ⊆ (bundleComap (tautQuotient (m := r) A) σ).baseSet i₂.1 := by
  intro y hy
  rw [Wb, whitneySum_baseSet] at hy
  exact hy.1

theorem mem_Wb_B (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B) (σ : PunctC A)
    (i₂ : (ι_A × Fin (r + 1)) × ι_B) :
    (Wb r s A B σ).baseSet i₂ ⊆ B.baseSet i₂.2 := by
  intro y hy
  rw [Wb, whitneySum_baseSet] at hy
  exact hy.2

theorem mem_Q_A (r : ℕ) (A : BunC Y (r + 1) ι_A) (σ : PunctC A) (hσ : IsSec A σ)
    (a : ι_A × Fin (r + 1)) :
    (bundleComap (tautQuotient (m := r) A) σ).baseSet a ⊆ A.baseSet a.1 := by
  intro y hy
  obtain ⟨a₁, a₂⟩ := a
  have h1 : σ y ∈ (tautQuotient (m := r) A).baseSet (a₁, a₂) := hy
  rw [tautQuotient_baseSet] at h1
  have h2 : ((σ y : ↥(zeroComplement (realification A))) :
      (realification A).TotalSpace).proj ∈ A.baseSet a₁ := h1.1
  rwa [hσ] at h2

theorem mem_Q_coord (r : ℕ) (A : BunC Y (r + 1) ι_A) (σ : PunctC A) (hσ : IsSec A σ)
    {a : ι_A × Fin (r + 1)} {y : Y}
    (hy : y ∈ (bundleComap (tautQuotient (m := r) A) σ).baseSet a) :
    zCoord a.1 (σ y) a.2 ≠ 0 := by
  obtain ⟨a₁, a₂⟩ := a
  have h1 : σ y ∈ (tautQuotient (m := r) A).baseSet (a₁, a₂) := hy
  rw [tautQuotient_baseSet] at h1
  have h2 : ((A.localTriv a₁ ((σ y : ↥(zeroComplement (realification A))) :
      (realification A).TotalSpace)).2 a₂ ≠ 0) := h1.2
  exact h2

/-! ## The chart expression of the forward gauge and its continuity -/

/-- The "nice form" of the chart expression of the forward gauge, on the standard splitting. -/
def homNicePair (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B) (σ : PunctC A)
    (i₁AB : ι_A × ι_B) (i₂A : ι_A) (k₂ : Fin (r + 1)) (i₂B : ι_B) (y : Y) :
    (EuclideanSpace ℂ (Fin (r + 1)) × EuclideanSpace ℂ (Fin (s + 1))) →L[ℂ]
      (EuclideanSpace ℂ (Fin r) × EuclideanSpace ℂ (Fin (s + 1))) :=
  ((quoCLM k₂ (zCoord i₂A (σ y))).comp (A.coordChange i₁AB.1 i₂A y)).prodMap
    (B.coordChange i₁AB.2 i₂B y)

theorem homNicePair_apply (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B)
    (σ : PunctC A) (i₁AB : ι_A × ι_B) (i₂A : ι_A) (k₂ : Fin (r + 1)) (i₂B : ι_B) (y : Y)
    (v : EuclideanSpace ℂ (Fin (r + 1)) × EuclideanSpace ℂ (Fin (s + 1))) :
    homNicePair r s A B σ i₁AB i₂A k₂ i₂B y v
      = (quoFun k₂ (zCoord i₂A (σ y)) (A.coordChange i₁AB.1 i₂A y v.1),
          B.coordChange i₁AB.2 i₂B y v.2) := rfl

/-- The "nice form" of the chart expression of the forward gauge `X → W`. -/
def homNice (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B) (σ : PunctC A)
    (i₁ : (ι_A × ι_B) × Fin ((r + 1) + (s + 1))) (i₂ : (ι_A × Fin (r + 1)) × ι_B)
    (y : Y) :
    EuclideanSpace ℂ (Fin ((r + 1) + s)) →L[ℂ] EuclideanSpace ℂ (Fin (r + (s + 1))) :=
  (joinQuotCLM r s).comp
    ((homNicePair r s A B σ i₁.1 i₂.1.1 i₂.1.2 i₂.2 y).comp
      ((splitSumCLM r s).comp (fillCLM i₁.2)))

theorem homNice_apply (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B)
    (σ : PunctC A) (i₁ : (ι_A × ι_B) × Fin ((r + 1) + (s + 1)))
    (i₂ : (ι_A × Fin (r + 1)) × ι_B) (y : Y) (z : EuclideanSpace ℂ (Fin ((r + 1) + s))) :
    homNice r s A B σ i₁ i₂ y z
      = joinQuotCLM r s
          (quoFun i₂.1.2 (zCoord i₂.1.1 (σ y))
              ((A.coordChange i₁.1.1 i₂.1.1 y)
                (((splitSumCLM r s) (fillFun i₁.2 z)).1)),
            (B.coordChange i₁.1.2 i₂.2 y)
              (((splitSumCLM r s) (fillFun i₁.2 z)).2)) := rfl

theorem continuousOn_homNice (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B)
    (σ : PunctC A) (hσ : IsSec A σ) (i₁ : (ι_A × ι_B) × Fin ((r + 1) + (s + 1)))
    (i₂ : (ι_A × Fin (r + 1)) × ι_B) :
    ContinuousOn (homNice r s A B σ i₁ i₂) (homSet r s A B σ hσ i₁ i₂) := by
  classical
  have hA1 : ∀ y ∈ homSet r s A B σ hσ i₁ i₂, y ∈ A.baseSet i₁.1.1 :=
    fun y hy => mem_sum_A r s A B i₁.1 (mem_Xb_sum r s A B σ hσ i₁ hy.1)
  have hB1 : ∀ y ∈ homSet r s A B σ hσ i₁ i₂, y ∈ B.baseSet i₁.1.2 :=
    fun y hy => mem_sum_B r s A B i₁.1 (mem_Xb_sum r s A B σ hσ i₁ hy.1)
  have hQ2 : ∀ y ∈ homSet r s A B σ hσ i₁ i₂,
      y ∈ (bundleComap (tautQuotient (m := r) A) σ).baseSet i₂.1 :=
    fun y hy => mem_Wb_Q r s A B σ i₂ hy.2
  have hA2 : ∀ y ∈ homSet r s A B σ hσ i₁ i₂, y ∈ A.baseSet i₂.1.1 :=
    fun y hy => mem_Q_A r A σ hσ i₂.1 (hQ2 y hy)
  have hB2 : ∀ y ∈ homSet r s A B σ hσ i₁ i₂, y ∈ B.baseSet i₂.2 :=
    fun y hy => mem_Wb_B r s A B σ i₂ hy.2
  have hzneq : ∀ y ∈ homSet r s A B σ hσ i₁ i₂, zCoord i₂.1.1 (σ y) i₂.1.2 ≠ 0 :=
    fun y hy => mem_Q_coord r A σ hσ (hQ2 y hy)
  have hsub : Continuous (fun p : ↥(homSet r s A B σ hσ i₁ i₂) ×
      EuclideanSpace ℂ (Fin ((r + 1) + s)) => ((p.1 : ↥(homSet r s A B σ hσ i₁ i₂)) : Y)) :=
    continuous_subtype_val.comp continuous_fst
  have hzc : Continuous (fun p : ↥(homSet r s A B σ hσ i₁ i₂) ×
      EuclideanSpace ℂ (Fin ((r + 1) + s)) => zCoord i₂.1.1 (σ p.1.1)) :=
    (NZ.continuousOn_zCoord_sec (V := A) hσ i₂.1.1).comp_continuous hsub
      (fun p => hA2 p.1 p.1.2)
  have hq : Continuous (fun p : ↥(homSet r s A B σ hσ i₁ i₂) ×
      EuclideanSpace ℂ (Fin ((r + 1) + s)) => quoCLM i₂.1.2 (zCoord i₂.1.1 (σ p.1.1))) :=
    (continuousOn_quoCLM i₂.1.2).comp_continuous hzc (fun p => hzneq p.1 p.1.2)
  have hAc : Continuous (fun p : ↥(homSet r s A B σ hσ i₁ i₂) ×
      EuclideanSpace ℂ (Fin ((r + 1) + s)) => A.coordChange i₁.1.1 i₂.1.1 p.1.1) :=
    (A.continuousOn_coordChange i₁.1.1 i₂.1.1).comp_continuous hsub
      (fun p => ⟨hA1 p.1 p.1.2, hA2 p.1 p.1.2⟩)
  have hBc : Continuous (fun p : ↥(homSet r s A B σ hσ i₁ i₂) ×
      EuclideanSpace ℂ (Fin ((r + 1) + s)) => B.coordChange i₁.1.2 i₂.2 p.1.1) :=
    (B.continuousOn_coordChange i₁.1.2 i₂.2).comp_continuous hsub
      (fun p => ⟨hB1 p.1 p.1.2, hB2 p.1 p.1.2⟩)
  have hX : Continuous (fun p : ↥(homSet r s A B σ hσ i₁ i₂) ×
      EuclideanSpace ℂ (Fin ((r + 1) + s)) => (splitSumCLM r s) (fillFun i₁.2 p.2)) :=
    (splitSumCLM r s).continuous.comp ((fillCLM i₁.2).continuous.comp continuous_snd)
  have hzA : Continuous (fun p : ↥(homSet r s A B σ hσ i₁ i₂) ×
      EuclideanSpace ℂ (Fin ((r + 1) + s)) => ((splitSumCLM r s) (fillFun i₁.2 p.2)).1) :=
    continuous_fst.comp hX
  have hzB : Continuous (fun p : ↥(homSet r s A B σ hσ i₁ i₂) ×
      EuclideanSpace ℂ (Fin ((r + 1) + s)) => ((splitSumCLM r s) (fillFun i₁.2 p.2)).2) :=
    continuous_snd.comp hX
  have h1 : Continuous (fun p : ↥(homSet r s A B σ hσ i₁ i₂) ×
      EuclideanSpace ℂ (Fin ((r + 1) + s)) =>
      (A.coordChange i₁.1.1 i₂.1.1 p.1.1) ((splitSumCLM r s) (fillFun i₁.2 p.2)).1) :=
    hAc.clm_apply hzA
  have h2 : Continuous (fun p : ↥(homSet r s A B σ hσ i₁ i₂) ×
      EuclideanSpace ℂ (Fin ((r + 1) + s)) =>
      quoFun i₂.1.2 (zCoord i₂.1.1 (σ p.1.1))
        ((A.coordChange i₁.1.1 i₂.1.1 p.1.1) ((splitSumCLM r s) (fillFun i₁.2 p.2)).1)) :=
    hq.clm_apply h1
  have h3 : Continuous (fun p : ↥(homSet r s A B σ hσ i₁ i₂) ×
      EuclideanSpace ℂ (Fin ((r + 1) + s)) =>
      (B.coordChange i₁.1.2 i₂.2 p.1.1) ((splitSumCLM r s) (fillFun i₁.2 p.2)).2) :=
    hBc.clm_apply hzB
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_clm_of_continuous_apply_gen (fun y : ↥(homSet r s A B σ hσ i₁ i₂) =>
      homNice r s A B σ i₁ i₂ (y : Y))
    (((joinQuotCLM r s).continuous.comp (h2.prodMk h3)).congr
      (fun p => (homNice_apply r s A B σ i₁ i₂ p.1.1 p.2).symm))


/-! ## The chart-transition formulas -/

theorem SumB_coordChange_apply' (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B)
    (i₁ : (ι_A × ι_B) × Fin ((r + 1) + (s + 1))) (y : Y)
    (zA : EuclideanSpace ℂ (Fin (r + 1))) (zB : EuclideanSpace ℂ (Fin (s + 1))) :
    (SumB r s A B).coordChange i₁.1 ((SumB r s A B).indexAt y) y
        (sumFibreC (r + 1) (s + 1) (zA, zB))
      = sumFibreC (r + 1) (s + 1)
          ((A.coordChange i₁.1.1 (A.indexAt y) y) zA,
            (B.coordChange i₁.1.2 (B.indexAt y) y) zB) := by
  rw [whitneySum_coordChange, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply,
    ContinuousLinearMap.coe_prodMap', Prod.map_apply]
  rfl

theorem SumB_coordChange_apply (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B)
    (i₁ : (ι_A × ι_B) × Fin ((r + 1) + (s + 1))) (y : Y)
    (z : EuclideanSpace ℂ (Fin ((r + 1) + s))) :
    (SumB r s A B).coordChange i₁.1 ((SumB r s A B).indexAt y) y (fillFun i₁.2 z)
      = sumFibreC (r + 1) (s + 1)
          ((A.coordChange i₁.1.1 (A.indexAt y) y)
              (((splitSumCLM r s) (fillFun i₁.2 z)).1),
            (B.coordChange i₁.1.2 (B.indexAt y) y)
              (((splitSumCLM r s) (fillFun i₁.2 z)).2)) := by
  have h := SumB_coordChange_apply' r s A B i₁ y
    (((splitSumCLM r s) (fillFun i₁.2 z)).1) (((splitSumCLM r s) (fillFun i₁.2 z)).2)
  rw [show sumFibreC (r + 1) (s + 1)
      (((splitSumCLM r s) (fillFun i₁.2 z)).1, ((splitSumCLM r s) (fillFun i₁.2 z)).2)
      = fillFun i₁.2 z from by rw [Prod.mk.eta, sumFibreC_splitSum]] at h
  exact h

theorem Xb_coordChange_apply (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B)
    (σ : PunctC A) (hσ : IsSec A σ) (i₁ : (ι_A × ι_B) × Fin ((r + 1) + (s + 1)))
    (y : Y) (z : EuclideanSpace ℂ (Fin ((r + 1) + s))) :
    (Xb r s A B σ hσ).coordChange i₁ ((Xb r s A B σ hσ).indexAt y) y z
      = quoFun (idxSum r s A B σ hσ y) (aFull r s A B σ hσ y)
          ((SumB r s A B).coordChange i₁.1 ((SumB r s A B).indexAt y) y (fillFun i₁.2 z)) := by
  rw [Xb, bundleComap_coordChange, bundleComap_indexAt, tautQuotient_indexAt_eq]
  rw [show i₁ = (i₁.1, i₁.2) from (Prod.mk.eta).symm]
  rw [tautQuotient_coordChange]
  rw [localTriv_indexAt_snd (SumB r s A B)
    (((sumSection r s A B σ hσ y) : ↥(zeroComplement (realification (SumB r s A B)))) :
      (realification (SumB r s A B)).TotalSpace)]
  rw [sumSection_proj' r s A B σ hσ y]
  rfl

theorem Wb_indexAt_eq (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B)
    (σ : PunctC A) (hσ : IsSec A σ) (y : Y) :
    (Wb r s A B σ).indexAt y = ((A.indexAt y, secIdx r A σ y), B.indexAt y) := by
  rw [Wb, whitneySum_indexAt, bundleComap_indexAt, tautQuotient_indexAt_eq]
  rw [hσ y]
  rfl

theorem QA_indexAt_eq (r : ℕ) (A : BunC Y (r + 1) ι_A) (σ : PunctC A) (hσ : IsSec A σ) (y : Y) :
    (bundleComap (tautQuotient (m := r) A) σ).indexAt y = (A.indexAt y, secIdx r A σ y) := by
  rw [bundleComap_indexAt, tautQuotient_indexAt_eq]
  rw [hσ y]
  rfl

theorem QA_coordChange_apply (r : ℕ) (A : BunC Y (r + 1) ι_A) (σ : PunctC A) (hσ : IsSec A σ)
    (a : ι_A × Fin (r + 1)) (y : Y) (w : EuclideanSpace ℂ (Fin r)) :
    (bundleComap (tautQuotient (m := r) A) σ).coordChange
        ((bundleComap (tautQuotient (m := r) A) σ).indexAt y) a y w
      = quoFun a.2 (zCoord a.1 (σ y))
          ((A.coordChange (A.indexAt y) a.1 y) (fillFun (secIdx r A σ y) w)) := by
  rw [bundleComap_coordChange, bundleComap_indexAt, tautQuotient_indexAt_eq,
    tautQuotient_coordChange]
  rw [hσ y]
  rfl

/-- The preferred-chart reading of the section is the chart change of the fibre vector. -/
theorem zCoord_sigma (r : ℕ) (A : BunC Y (r + 1) ι_A) (σ : PunctC A) (hσ : IsSec A σ)
    (i : ι_A) (y : Y) :
    zCoord i (σ y) = (A.coordChange (A.indexAt y) i y) (secA r A σ y) := by
  rw [zCoord, VectorBundleCore.localTriv_apply]
  rw [hσ y]
  rfl

theorem zCoord_sigma_symm (r : ℕ) (A : BunC Y (r + 1) ι_A) (σ : PunctC A) (hσ : IsSec A σ)
    {i : ι_A} {y : Y} (hy : y ∈ A.baseSet i) :
    (A.coordChange i (A.indexAt y) y) (zCoord i (σ y)) = secA r A σ y := by
  rw [zCoord_sigma r A σ hσ i y]
  rw [A.coordChange_comp (A.indexAt y) i (A.indexAt y) y
    ⟨⟨A.mem_baseSet_at y, hy⟩, A.mem_baseSet_at y⟩]
  rw [A.coordChange_self (A.indexAt y) y (A.mem_baseSet_at y)]

/-- The component formula for the chart change of the right-hand side. -/
theorem Wb_coordChange_eq (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B)
    (σ : PunctC A) (hσ : IsSec A σ) (i₂ : (ι_A × Fin (r + 1)) × ι_B) (y : Y) :
    (Wb r s A B σ).coordChange ((Wb r s A B σ).indexAt y) i₂ y
      = (joinQuotCLM r s).comp
          (((bundleComap (tautQuotient (m := r) A) σ).coordChange
              ((A.indexAt y, secIdx r A σ y)) i₂.1 y).prodMap
            (B.coordChange (B.indexAt y) i₂.2 y) |>.comp (splitQuotCLM r s)) := by
  rw [show (Wb r s A B σ).indexAt y = ((A.indexAt y, secIdx r A σ y), B.indexAt y) from
    Wb_indexAt_eq r s A B σ hσ y]
  rw [Wb, whitneySum_coordChange]
  rfl

theorem Wb_coordChange_apply (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B)
    (σ : PunctC A) (hσ : IsSec A σ) (i₂ : (ι_A × Fin (r + 1)) × ι_B) (y : Y)
    (vA : EuclideanSpace ℂ (Fin r)) (vB : EuclideanSpace ℂ (Fin (s + 1))) :
    (Wb r s A B σ).coordChange ((Wb r s A B σ).indexAt y) i₂ y
        (joinQuotCLM r s (vA, vB))
      = joinQuotCLM r s
          ((bundleComap (tautQuotient (m := r) A) σ).coordChange
              ((bundleComap (tautQuotient (m := r) A) σ).indexAt y) i₂.1 y vA,
            (B.coordChange (B.indexAt y) i₂.2 y) vB) := by
  rw [Wb_coordChange_eq r s A B σ hσ i₂ y]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_prodMap', Prod.map_apply,
    joinQuotCLM_apply, splitQuotCLM_apply]
  rw [← QA_indexAt_eq r A σ hσ y, QA_coordChange_apply r A σ hσ i₂.1 y vA]

/-! ## The inner chart identity -/

/-- The chart expression of the forward gauge composed with the chart change of `X`. -/
def homInner (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B) (σ : PunctC A)
    (i₁ : (ι_A × ι_B) × Fin ((r + 1) + (s + 1))) (y : Y) :
    EuclideanSpace ℂ (Fin ((r + 1) + s)) →L[ℂ] EuclideanSpace ℂ (Fin (r + (s + 1))) :=
  (joinQuotCLM r s).comp
    (((quoCLM (secIdx r A σ y) (secA r A σ y)).comp
        ((A.coordChange i₁.1.1 (A.indexAt y) y).comp
          ((ContinuousLinearMap.fst ℂ (EuclideanSpace ℂ (Fin (r + 1)))
            (EuclideanSpace ℂ (Fin (s + 1)))).comp
              ((splitSumCLM r s).comp (fillCLM i₁.2))))).prod
      ((B.coordChange i₁.1.2 (B.indexAt y) y).comp
        ((ContinuousLinearMap.snd ℂ (EuclideanSpace ℂ (Fin (r + 1)))
          (EuclideanSpace ℂ (Fin (s + 1)))).comp
            ((splitSumCLM r s).comp (fillCLM i₁.2)))))

theorem homInner_apply (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B)
    (σ : PunctC A) (i₁ : (ι_A × ι_B) × Fin ((r + 1) + (s + 1))) (y : Y)
    (z : EuclideanSpace ℂ (Fin ((r + 1) + s))) :
    homInner r s A B σ i₁ y z
      = joinQuotCLM r s
          (quoFun (secIdx r A σ y) (secA r A σ y)
              ((A.coordChange i₁.1.1 (A.indexAt y) y)
                (((splitSumCLM r s) (fillFun i₁.2 z)).1)),
            (B.coordChange i₁.1.2 (B.indexAt y) y)
              (((splitSumCLM r s) (fillFun i₁.2 z)).2)) := rfl

theorem hom_inner (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B)
    (σ : PunctC A) (hσ : IsSec A σ) (i₁ : (ι_A × ι_B) × Fin ((r + 1) + (s + 1))) (y : Y) :
    (homCLM r s A B σ hσ y).comp
        ((Xb r s A B σ hσ).coordChange i₁ ((Xb r s A B σ hσ).indexAt y) y)
      = homInner r s A B σ i₁ y := by
  refine ContinuousLinearMap.ext fun z => ?_
  obtain ⟨zA, zB, hz_split⟩ : ∃ zA zB, (splitSumCLM r s) (fillFun i₁.2 z) = (zA, zB) :=
    ⟨_, _, rfl⟩
  have hSum : (SumB r s A B).coordChange i₁.1 ((SumB r s A B).indexAt y) y (fillFun i₁.2 z)
      = sumFibreC (r + 1) (s + 1)
          ((A.coordChange i₁.1.1 (A.indexAt y) y) zA,
            (B.coordChange i₁.1.2 (B.indexAt y) y) zB) := by
    rw [SumB_coordChange_apply, hz_split]
  set Y₂ := sumFibreC (r + 1) (s + 1)
      ((A.coordChange i₁.1.1 (A.indexAt y) y) zA,
        (B.coordChange i₁.1.2 (B.indexAt y) y) zB) with hY₂
  set c : ℂ := Y₂ (idxSum r s A B σ hσ y) / aFull r s A B σ hσ y (idxSum r s A B σ hσ y)
    with hc
  have hfill : fillFun (idxSum r s A B σ hσ y)
      (quoFun (idxSum r s A B σ hσ y) (aFull r s A B σ hσ y) Y₂)
      = Y₂ - c • aFull r s A B σ hσ y := by
    rw [hc, eq_sub_iff_add_eq]
    exact (sub_eq_iff_eq_add'.mp
      (sub_fillFun_quoFun _ _ Y₂ (idxSum_spec r s A B σ hσ y))).symm
  have hsplit : (splitSumCLM r s)
      (fillFun (idxSum r s A B σ hσ y)
        (quoFun (idxSum r s A B σ hσ y) (aFull r s A B σ hσ y) Y₂))
      = ((A.coordChange i₁.1.1 (A.indexAt y) y) zA - c • secA r A σ y,
          (B.coordChange i₁.1.2 (B.indexAt y) y) zB) := by
    rw [hfill, map_sub, map_smul, hY₂, splitSumCLM_apply,
      splitSumCLM_secA_zero r s A B σ hσ y]
    simp
  have hquo : quoFun (secIdx r A σ y) (secA r A σ y)
      ((A.coordChange i₁.1.1 (A.indexAt y) y) zA - c • secA r A σ y)
      = quoFun (secIdx r A σ y) (secA r A σ y) ((A.coordChange i₁.1.1 (A.indexAt y) y) zA) :=
    quoFun_sub_smul_self _ _ _ _ (secA_secIdx_ne_zero r A σ hσ y)
  rw [ContinuousLinearMap.comp_apply, homCLM_apply, Xb_coordChange_apply, hSum, hsplit, hquo]
  rw [homInner_apply, hz_split]

/-! ## The full chart identity of the forward gauge -/

theorem hom_chart_clm_eq (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B)
    (σ : PunctC A) (hσ : IsSec A σ) (i₁ : (ι_A × ι_B) × Fin ((r + 1) + (s + 1)))
    (i₂ : (ι_A × Fin (r + 1)) × ι_B) {y : Y} (hy : y ∈ homSet r s A B σ hσ i₁ i₂) :
    ((Wb r s A B σ).coordChange ((Wb r s A B σ).indexAt y) i₂ y).comp
        ((homCLM r s A B σ hσ y).comp
          ((Xb r s A B σ hσ).coordChange i₁ ((Xb r s A B σ hσ).indexAt y) y))
      = homNice r s A B σ i₁ i₂ y := by
  have hyQ : y ∈ (bundleComap (tautQuotient (m := r) A) σ).baseSet i₂.1 :=
    mem_Wb_Q r s A B σ i₂ hy.2
  have hyA1 : y ∈ A.baseSet i₁.1.1 :=
    mem_sum_A r s A B i₁.1 (mem_Xb_sum r s A B σ hσ i₁ hy.1)
  have hyQ' : y ∈ A.baseSet i₂.1.1 := mem_Q_A r A σ hσ i₂.1 hyQ
  have hz2 : zCoord i₂.1.1 (σ y) i₂.1.2 ≠ 0 := mem_Q_coord r A σ hσ hyQ
  rw [hom_inner r s A B σ hσ i₁ y]
  refine ContinuousLinearMap.ext fun z => ?_
  obtain ⟨zA, zB, hz_split⟩ : ∃ zA zB, (splitSumCLM r s) (fillFun i₁.2 z) = (zA, zB) :=
    ⟨_, _, rfl⟩
  set Ac₁ : EuclideanSpace ℂ (Fin (r + 1)) →L[ℂ] EuclideanSpace ℂ (Fin (r + 1)) :=
    A.coordChange i₁.1.1 (A.indexAt y) y with hAc₁
  set Ac : EuclideanSpace ℂ (Fin (r + 1)) →L[ℂ] EuclideanSpace ℂ (Fin (r + 1)) :=
    A.coordChange (A.indexAt y) i₂.1.1 y with hAc
  set Bc₁ : EuclideanSpace ℂ (Fin (s + 1)) →L[ℂ] EuclideanSpace ℂ (Fin (s + 1)) :=
    B.coordChange i₁.1.2 (B.indexAt y) y with hBc₁
  set Bc : EuclideanSpace ℂ (Fin (s + 1)) →L[ℂ] EuclideanSpace ℂ (Fin (s + 1)) :=
    B.coordChange (B.indexAt y) i₂.2 y with hBc
  -- the inner class, in the preferred chart of A
  set q : EuclideanSpace ℂ (Fin r) :=
    quoFun (secIdx r A σ y) (secA r A σ y) (Ac₁ zA) with hq
  have hWapply : (Wb r s A B σ).coordChange ((Wb r s A B σ).indexAt y) i₂ y
      (joinQuotCLM r s (q, Bc₁ zB))
      = joinQuotCLM r s
          (quoFun i₂.1.2 (zCoord i₂.1.1 (σ y)) (Ac (fillFun (secIdx r A σ y) q)),
            Bc (Bc₁ zB)) := by
    rw [Wb_coordChange_apply r s A B σ hσ i₂ y q (Bc₁ zB),
      QA_coordChange_apply r A σ hσ i₂.1 y q]
  have hcycle : (A.coordChange i₁.1.1 i₂.1.1 y) zA = Ac (Ac₁ zA) := by
    rw [hAc, hAc₁]
    exact (A.coordChange_comp i₁.1.1 (A.indexAt y) i₂.1.1 y
      ⟨⟨hyA1, A.mem_baseSet_at y⟩, hyQ'⟩ zA).symm
  have hcycleB : (B.coordChange i₁.1.2 i₂.2 y) zB = Bc (Bc₁ zB) := by
    rw [hBc, hBc₁]
    exact (B.coordChange_comp i₁.1.2 (B.indexAt y) i₂.2 y
      ⟨⟨mem_sum_B r s A B i₁.1 (mem_Xb_sum r s A B σ hσ i₁ hy.1), B.mem_baseSet_at y⟩,
        mem_Wb_B r s A B σ i₂ hy.2⟩ zB).symm
  have hzc2 : zCoord i₂.1.1 (σ y) = Ac (secA r A σ y) := by
    rw [hAc]
    exact zCoord_sigma r A σ hσ i₂.1.1 y
  have hfillA : fillFun (secIdx r A σ y) q = Ac₁ zA - (Ac₁ zA (secIdx r A σ y) /
      secA r A σ y (secIdx r A σ y)) • secA r A σ y := by
    rw [hq]
    rw [eq_sub_iff_add_eq]
    exact (sub_eq_iff_eq_add'.mp (sub_fillFun_quoFun (secIdx r A σ y) (secA r A σ y) (Ac₁ zA)
      (secA_secIdx_ne_zero r A σ hσ y))).symm
  have hkey : quoFun i₂.1.2 (zCoord i₂.1.1 (σ y)) (Ac (fillFun (secIdx r A σ y) q))
      = quoFun i₂.1.2 (zCoord i₂.1.1 (σ y)) ((A.coordChange i₁.1.1 i₂.1.1 y) zA) := by
    rw [hfillA, map_sub, map_smul, ← hzc2, quoFun_sub_smul_self _ _ _ _ hz2, ← hcycle]
  rw [ContinuousLinearMap.comp_apply, homInner_apply, hz_split]
  change (Wb r s A B σ).coordChange ((Wb r s A B σ).indexAt y) i₂ y
      (joinQuotCLM r s (quoFun (secIdx r A σ y) (secA r A σ y) (Ac₁ zA), Bc₁ zB)) =
    (homNice r s A B σ i₁ i₂ y) z
  rw [← hq, hWapply, hkey, ← hcycleB, homNice_apply, hz_split]


/-! ## The chart expression of the backward gauge and its continuity -/

theorem sum_localTriv_section (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B)
    (σ : PunctC A) (hσ : IsSec A σ) (i : ι_A × ι_B) (y : Y) :
    ((SumB r s A B).localTriv i (((sumSection r s A B σ hσ y :
      ↥(zeroComplement (realification (SumB r s A B)))) :
      (realification (SumB r s A B)).TotalSpace))).2
      = sumFibreC (r + 1) (s + 1) (zCoord i.1 (σ y), 0) := by
  rw [VectorBundleCore.localTriv_apply]
  rw [sumSection_proj' r s A B σ hσ y, sumSection_snd' r s A B σ hσ y]
  rw [whitneySum_coordChange, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  change (sumFibreC (r + 1) (s + 1))
      (((A.coordChange ((SumB r s A B).indexAt y).1 i.1 y).prodMap
        (B.coordChange ((SumB r s A B).indexAt y).2 i.2 y))
        (splitSumCLM r s (aFull r s A B σ hσ y)))
      = sumFibreC (r + 1) (s + 1) (zCoord i.1 (σ y), 0)
  rw [splitSumCLM_secA_zero r s A B σ hσ y, ContinuousLinearMap.coe_prodMap', Prod.map_apply,
    show ((SumB r s A B).indexAt y).1 = A.indexAt y from rfl,
    show ((SumB r s A B).indexAt y).2 = B.indexAt y from rfl,
    ← zCoord_sigma r A σ hσ i.1 y]
  simp only [map_zero]

theorem zCoord_indexAt_sigma (r : ℕ) (A : BunC Y (r + 1) ι_A) (σ : PunctC A) (hσ : IsSec A σ)
    (y : Y) : zCoord (A.indexAt y) (σ y) = secA r A σ y := by
  rw [zCoord_sigma r A σ hσ (A.indexAt y) y]
  rw [A.coordChange_self (A.indexAt y) y (A.mem_baseSet_at y)]

theorem QA_coordChange_apply_gen (r : ℕ) (A : BunC Y (r + 1) ι_A) (σ : PunctC A)
    (hσ : IsSec A σ) (a b : ι_A × Fin (r + 1)) (y : Y) (w : EuclideanSpace ℂ (Fin r)) :
    (bundleComap (tautQuotient (m := r) A) σ).coordChange a b y w
      = quoFun b.2 (zCoord b.1 (σ y))
          ((A.coordChange a.1 b.1 y) (fillFun a.2 w)) := by
  obtain ⟨a₁, a₂⟩ := a
  obtain ⟨b₁, b₂⟩ := b
  rw [bundleComap_coordChange, tautQuotient_coordChange]
  rw [hσ y]
  rfl

/-- The "nice form" of the chart expression of the backward gauge `W → X`. -/
def invNice (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B) (σ : PunctC A)
    (i₁ : (ι_A × Fin (r + 1)) × ι_B) (i₂ : (ι_A × ι_B) × Fin ((r + 1) + (s + 1)))
    (y : Y) :
    EuclideanSpace ℂ (Fin (r + (s + 1))) →L[ℂ] EuclideanSpace ℂ (Fin ((r + 1) + s)) :=
  (quoCLM i₂.2 (joinSumCLM r s (zCoord i₂.1.1 (σ y), 0))).comp
    ((joinSumCLM r s).comp
      (((((A.coordChange i₁.1.1 i₂.1.1 y).comp (fillCLM i₁.1.2)).comp
          ((ContinuousLinearMap.fst ℂ (EuclideanSpace ℂ (Fin r))
            (EuclideanSpace ℂ (Fin (s + 1)))).comp (splitQuotCLM r s))).prod
        ((B.coordChange i₁.2 i₂.1.2 y).comp
          ((ContinuousLinearMap.snd ℂ (EuclideanSpace ℂ (Fin r))
            (EuclideanSpace ℂ (Fin (s + 1)))).comp (splitQuotCLM r s))))))

theorem invNice_apply (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B)
    (σ : PunctC A) (i₁ : (ι_A × Fin (r + 1)) × ι_B)
    (i₂ : (ι_A × ι_B) × Fin ((r + 1) + (s + 1))) (y : Y)
    (u : EuclideanSpace ℂ (Fin (r + (s + 1)))) :
    invNice r s A B σ i₁ i₂ y u
      = quoFun i₂.2 (joinSumCLM r s (zCoord i₂.1.1 (σ y), 0))
          (joinSumCLM r s
            ((A.coordChange i₁.1.1 i₂.1.1 y) (fillFun i₁.1.2 ((splitQuotCLM r s) u).1),
              (B.coordChange i₁.2 i₂.1.2 y) ((splitQuotCLM r s) u).2)) := rfl

/-- The set on which the chart expression of the backward gauge is studied. -/
abbrev invSet (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B) (σ : PunctC A)
    (hσ : IsSec A σ) (i₁ : (ι_A × Fin (r + 1)) × ι_B)
    (i₂ : (ι_A × ι_B) × Fin ((r + 1) + (s + 1))) : Set Y :=
  (Wb r s A B σ).baseSet i₁ ∩ (Xb r s A B σ hσ).baseSet i₂

theorem mem_Xb_coord_join (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B)
    (σ : PunctC A) (hσ : IsSec A σ) (i₂ : (ι_A × ι_B) × Fin ((r + 1) + (s + 1)))
    {y : Y} (hy : y ∈ (Xb r s A B σ hσ).baseSet i₂) :
    (joinSumCLM r s (zCoord i₂.1.1 (σ y), 0)) i₂.2 ≠ 0 := by
  have h := mem_Xb_coord r s A B σ hσ i₂ hy
  rwa [sum_localTriv_section r s A B σ hσ i₂.1 y] at h

theorem continuousOn_invNice (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B)
    (σ : PunctC A) (hσ : IsSec A σ) (i₁ : (ι_A × Fin (r + 1)) × ι_B)
    (i₂ : (ι_A × ι_B) × Fin ((r + 1) + (s + 1))) :
    ContinuousOn (invNice r s A B σ i₁ i₂) (invSet r s A B σ hσ i₁ i₂) := by
  classical
  have hyA1 : ∀ y ∈ invSet r s A B σ hσ i₁ i₂, y ∈ A.baseSet i₁.1.1 :=
    fun y hy => mem_Q_A r A σ hσ i₁.1 (mem_Wb_Q r s A B σ i₁ hy.1)
  have hyB1 : ∀ y ∈ invSet r s A B σ hσ i₁ i₂, y ∈ B.baseSet i₁.2 :=
    fun y hy => mem_Wb_B r s A B σ i₁ hy.1
  have hyA2 : ∀ y ∈ invSet r s A B σ hσ i₁ i₂, y ∈ A.baseSet i₂.1.1 :=
    fun y hy => mem_sum_A r s A B i₂.1 (mem_Xb_sum r s A B σ hσ i₂ hy.2)
  have hyB2 : ∀ y ∈ invSet r s A B σ hσ i₁ i₂, y ∈ B.baseSet i₂.1.2 :=
    fun y hy => mem_sum_B r s A B i₂.1 (mem_Xb_sum r s A B σ hσ i₂ hy.2)
  have hzdiv : ∀ y ∈ invSet r s A B σ hσ i₁ i₂,
      (joinSumCLM r s (zCoord i₂.1.1 (σ y), 0)) i₂.2 ≠ 0 :=
    fun y hy => mem_Xb_coord_join r s A B σ hσ i₂ hy.2
  have hsub : Continuous (fun p : ↥(invSet r s A B σ hσ i₁ i₂) ×
      EuclideanSpace ℂ (Fin (r + (s + 1))) => ((p.1 : ↥(invSet r s A B σ hσ i₁ i₂)) : Y)) :=
    continuous_subtype_val.comp continuous_fst
  have hzc : Continuous (fun p : ↥(invSet r s A B σ hσ i₁ i₂) ×
      EuclideanSpace ℂ (Fin (r + (s + 1))) => zCoord i₂.1.1 (σ p.1.1)) :=
    (NZ.continuousOn_zCoord_sec (V := A) hσ i₂.1.1).comp_continuous hsub
      (fun p => hyA2 p.1 p.1.2)
  have hdiv : Continuous (fun p : ↥(invSet r s A B σ hσ i₁ i₂) ×
      EuclideanSpace ℂ (Fin (r + (s + 1))) =>
      joinSumCLM r s (zCoord i₂.1.1 (σ p.1.1), 0)) :=
    (joinSumCLM r s).continuous.comp (hzc.prodMk continuous_const)
  have hq : Continuous (fun p : ↥(invSet r s A B σ hσ i₁ i₂) ×
      EuclideanSpace ℂ (Fin (r + (s + 1))) =>
      quoCLM i₂.2 (joinSumCLM r s (zCoord i₂.1.1 (σ p.1.1), 0))) :=
    (continuousOn_quoCLM i₂.2).comp_continuous hdiv (fun p => hzdiv p.1 p.1.2)
  have hAc : Continuous (fun p : ↥(invSet r s A B σ hσ i₁ i₂) ×
      EuclideanSpace ℂ (Fin (r + (s + 1))) => A.coordChange i₁.1.1 i₂.1.1 p.1.1) :=
    (A.continuousOn_coordChange i₁.1.1 i₂.1.1).comp_continuous hsub
      (fun p => ⟨hyA1 p.1 p.1.2, hyA2 p.1 p.1.2⟩)
  have hBc : Continuous (fun p : ↥(invSet r s A B σ hσ i₁ i₂) ×
      EuclideanSpace ℂ (Fin (r + (s + 1))) => B.coordChange i₁.2 i₂.1.2 p.1.1) :=
    (B.continuousOn_coordChange i₁.2 i₂.1.2).comp_continuous hsub
      (fun p => ⟨hyB1 p.1 p.1.2, hyB2 p.1 p.1.2⟩)
  have hu : Continuous (fun p : ↥(invSet r s A B σ hσ i₁ i₂) ×
      EuclideanSpace ℂ (Fin (r + (s + 1))) => (splitQuotCLM r s) p.2) :=
    (splitQuotCLM r s).continuous.comp continuous_snd
  have huA : Continuous (fun p : ↥(invSet r s A B σ hσ i₁ i₂) ×
      EuclideanSpace ℂ (Fin (r + (s + 1))) => ((splitQuotCLM r s) p.2).1) :=
    continuous_fst.comp hu
  have huB : Continuous (fun p : ↥(invSet r s A B σ hσ i₁ i₂) ×
      EuclideanSpace ℂ (Fin (r + (s + 1))) => ((splitQuotCLM r s) p.2).2) :=
    continuous_snd.comp hu
  have h1 : Continuous (fun p : ↥(invSet r s A B σ hσ i₁ i₂) ×
      EuclideanSpace ℂ (Fin (r + (s + 1))) =>
      (A.coordChange i₁.1.1 i₂.1.1 p.1.1) (fillFun i₁.1.2 ((splitQuotCLM r s) p.2).1)) :=
    hAc.clm_apply ((fillCLM i₁.1.2).continuous.comp huA)
  have h2 : Continuous (fun p : ↥(invSet r s A B σ hσ i₁ i₂) ×
      EuclideanSpace ℂ (Fin (r + (s + 1))) =>
      (B.coordChange i₁.2 i₂.1.2 p.1.1) ((splitQuotCLM r s) p.2).2) :=
    hBc.clm_apply huB
  rw [continuousOn_iff_continuous_domRestrict]
  refine continuous_clm_of_continuous_apply_gen (fun y : ↥(invSet r s A B σ hσ i₁ i₂) =>
      invNice r s A B σ i₁ i₂ (y : Y)) ?_
  refine (hq.clm_apply ((joinSumCLM r s).continuous.comp (h1.prodMk h2))).congr (fun p => ?_)
  exact (invNice_apply r s A B σ i₁ i₂ p.1.1 p.2).symm

/-! ## The chart-transition formulas for the backward gauge -/

theorem Wb_coordChange_eq_from (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B)
    (σ : PunctC A) (i₁ : (ι_A × Fin (r + 1)) × ι_B) (y : Y) :
    (Wb r s A B σ).coordChange i₁ ((Wb r s A B σ).indexAt y) y
      = (joinQuotCLM r s).comp
          ((((bundleComap (tautQuotient (m := r) A) σ).coordChange i₁.1
              ((bundleComap (tautQuotient (m := r) A) σ).indexAt y) y).prodMap
            (B.coordChange i₁.2 (B.indexAt y) y)).comp (splitQuotCLM r s)) := by
  rw [Wb, whitneySum_coordChange]
  rfl

theorem Wb_coordChange_apply_from (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B)
    (σ : PunctC A) (i₁ : (ι_A × Fin (r + 1)) × ι_B) (y : Y)
    (uA : EuclideanSpace ℂ (Fin r)) (uB : EuclideanSpace ℂ (Fin (s + 1))) :
    (Wb r s A B σ).coordChange i₁ ((Wb r s A B σ).indexAt y) y (joinQuotCLM r s (uA, uB))
      = joinQuotCLM r s
          ((bundleComap (tautQuotient (m := r) A) σ).coordChange i₁.1
              ((bundleComap (tautQuotient (m := r) A) σ).indexAt y) y uA,
            (B.coordChange i₁.2 (B.indexAt y) y) uB) := by
  rw [Wb_coordChange_eq_from r s A B σ i₁ y]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_prodMap', Prod.map_apply,
    joinQuotCLM_apply, splitQuotCLM_apply]

theorem SumB_coordChange_apply_gen (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B)
    (p q : ι_A × ι_B) (y : Y) (zA : EuclideanSpace ℂ (Fin (r + 1)))
    (zB : EuclideanSpace ℂ (Fin (s + 1))) :
    (SumB r s A B).coordChange p q y (sumFibreC (r + 1) (s + 1) (zA, zB))
      = sumFibreC (r + 1) (s + 1) ((A.coordChange p.1 q.1 y) zA, (B.coordChange p.2 q.2 y) zB) := by
  rw [whitneySum_coordChange, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  simp only [splitSumCLM, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply,
    ContinuousLinearMap.coe_prodMap', Prod.map_apply]

theorem Xb_indexAt_eq (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B)
    (σ : PunctC A) (hσ : IsSec A σ) (y : Y) :
    (Xb r s A B σ hσ).indexAt y = ((SumB r s A B).indexAt y, idxSum r s A B σ hσ y) := by
  rw [Xb, bundleComap_indexAt, tautQuotient_indexAt_eq]
  rw [sumSection_proj' r s A B σ hσ y]
  rfl

theorem Xb_coordChange_gen (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B)
    (σ : PunctC A) (hσ : IsSec A σ)
    (i j : (ι_A × ι_B) × Fin ((r + 1) + (s + 1))) (y : Y)
    (z : EuclideanSpace ℂ (Fin ((r + 1) + s))) :
    (Xb r s A B σ hσ).coordChange i j y z
      = quoFun j.2 ((SumB r s A B).localTriv j.1
            (((sumSection r s A B σ hσ y : ↥(zeroComplement (realification (SumB r s A B)))) :
              (realification (SumB r s A B)).TotalSpace))).2
          ((SumB r s A B).coordChange i.1 j.1 y (fillFun i.2 z)) := by
  obtain ⟨iAB, iK⟩ := i
  obtain ⟨jAB, jK⟩ := j
  rw [Xb, bundleComap_coordChange, tautQuotient_coordChange]
  rw [sumSection_proj' r s A B σ hσ y]
  rw [show (jAB, jK).1 = jAB from rfl, show (jAB, jK).2 = jK from rfl,
    show (iAB, iK).1 = iAB from rfl, show (iAB, iK).2 = iK from rfl]
  rfl

theorem Xb_coordChange_from_indexAt (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B)
    (σ : PunctC A) (hσ : IsSec A σ) (i₂ : (ι_A × ι_B) × Fin ((r + 1) + (s + 1)))
    (y : Y) (z : EuclideanSpace ℂ (Fin ((r + 1) + s))) :
    (Xb r s A B σ hσ).coordChange ((Xb r s A B σ hσ).indexAt y) i₂ y z
      = quoFun i₂.2 ((SumB r s A B).localTriv i₂.1
            (((sumSection r s A B σ hσ y : ↥(zeroComplement (realification (SumB r s A B)))) :
              (realification (SumB r s A B)).TotalSpace))).2
          ((SumB r s A B).coordChange ((SumB r s A B).indexAt y) i₂.1 y
            (fillFun (idxSum r s A B σ hσ y) z)) := by
  rw [Xb_coordChange_gen r s A B σ hσ ((Xb r s A B σ hσ).indexAt y) i₂ y z,
    Xb_indexAt_eq r s A B σ hσ y]

theorem SumB_coordChange_apply_section (r s : ℕ) (A : BunC Y (r + 1) ι_A)
    (B : BunC Y (s + 1) ι_B) (σ : PunctC A) (hσ : IsSec A σ)
    (i₂ : (ι_A × ι_B) × Fin ((r + 1) + (s + 1))) (y : Y) :
    (SumB r s A B).coordChange ((SumB r s A B).indexAt y) i₂.1 y (aFull r s A B σ hσ y)
      = sumFibreC (r + 1) (s + 1) (zCoord i₂.1.1 (σ y), 0) := by
  rw [aFull_apply, sumIncl_apply]
  rw [show (SumB r s A B).indexAt y = (A.indexAt y, B.indexAt y) from rfl]
  rw [SumB_coordChange_apply_gen r s A B (A.indexAt y, B.indexAt y) i₂.1 y
    (secA r A σ y) (0 : EuclideanSpace ℂ (Fin (s + 1)))]
  rw [← zCoord_sigma r A σ hσ i₂.1.1 y]
  simp only [map_zero]

theorem quoFun_kills_divisor {n : ℕ} (k : Fin (n + 1)) (w u : EuclideanSpace ℂ (Fin (n + 1)))
    (c : ℂ) (hw : w k ≠ 0) : quoFun k w (u - c • w) = quoFun k w u :=
  quoFun_sub_smul_self k w u c hw

theorem inv_chart_clm_eq (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B)
    (σ : PunctC A) (hσ : IsSec A σ) (i₁ : (ι_A × Fin (r + 1)) × ι_B)
    (i₂ : (ι_A × ι_B) × Fin ((r + 1) + (s + 1))) {y : Y}
    (hy : y ∈ invSet r s A B σ hσ i₁ i₂) :
    ((Xb r s A B σ hσ).coordChange ((Xb r s A B σ hσ).indexAt y) i₂ y).comp
        ((invCLM r s A B σ hσ y).comp
          ((Wb r s A B σ).coordChange i₁ ((Wb r s A B σ).indexAt y) y))
      = invNice r s A B σ i₁ i₂ y := by
  have hyA1 : y ∈ A.baseSet i₁.1.1 := mem_Q_A r A σ hσ i₁.1 (mem_Wb_Q r s A B σ i₁ hy.1)
  have hyA2 : y ∈ A.baseSet i₂.1.1 :=
    mem_sum_A r s A B i₂.1 (mem_Xb_sum r s A B σ hσ i₂ hy.2)
  have hyB2 : y ∈ B.baseSet i₂.1.2 :=
    mem_sum_B r s A B i₂.1 (mem_Xb_sum r s A B σ hσ i₂ hy.2)
  have hz₂ : (joinSumCLM r s (zCoord i₂.1.1 (σ y), 0)) i₂.2 ≠ 0 :=
    mem_Xb_coord_join r s A B σ hσ i₂ hy.2
  refine ContinuousLinearMap.ext fun u => ?_
  obtain ⟨uA, uB, hu_split⟩ : ∃ uA uB, (splitQuotCLM r s) u = (uA, uB) := ⟨_, _, rfl⟩
  set ζ : EuclideanSpace ℂ (Fin r) :=
    quoFun (secIdx r A σ y) (secA r A σ y)
      ((A.coordChange i₁.1.1 (A.indexAt y) y) (fillFun i₁.1.2 uA)) with hζ
  set μ : EuclideanSpace ℂ (Fin (s + 1)) := (B.coordChange i₁.2 (B.indexAt y) y) uB with hμ
  set Yv : EuclideanSpace ℂ (Fin ((r + 1) + (s + 1))) :=
    joinSumCLM r s (fillFun (secIdx r A σ y) ζ, μ) with hY
  have hW : (Wb r s A B σ).coordChange i₁ ((Wb r s A B σ).indexAt y) y u
      = joinQuotCLM r s
          ((bundleComap (tautQuotient (m := r) A) σ).coordChange i₁.1
              ((bundleComap (tautQuotient (m := r) A) σ).indexAt y) y uA
            , μ) := by
    have hu' : joinQuotCLM r s (uA, uB) = u := by
      rw [← hu_split, joinQuotCLM_splitQuotCLM]
    rw [← hu', Wb_coordChange_apply_from r s A B σ i₁ y uA uB, hμ]
  have hQA : (bundleComap (tautQuotient (m := r) A) σ).coordChange i₁.1
      ((bundleComap (tautQuotient (m := r) A) σ).indexAt y) y uA
      = quoFun (secIdx r A σ y) (secA r A σ y)
          ((A.coordChange i₁.1.1 (A.indexAt y) y) (fillFun i₁.1.2 uA)) := by
    rw [QA_coordChange_apply_gen r A σ hσ i₁.1
      ((bundleComap (tautQuotient (m := r) A) σ).indexAt y) y uA]
    rw [QA_indexAt_eq r A σ hσ y]
    rw [show ((A.indexAt y, secIdx r A σ y)).2 = secIdx r A σ y from rfl,
      show ((A.indexAt y, secIdx r A σ y)).1 = A.indexAt y from rfl]
    rw [zCoord_indexAt_sigma r A σ hσ y]
  have hinv : invCLM r s A B σ hσ y
      ((Wb r s A B σ).coordChange i₁ ((Wb r s A B σ).indexAt y) y u)
      = quoFun (idxSum r s A B σ hσ y) (aFull r s A B σ hσ y) Yv := by
    rw [hW, hQA, ← hζ]
    rw [show invCLM r s A B σ hσ y (joinQuotCLM r s (ζ, μ))
        = quoFun (idxSum r s A B σ hσ y) (aFull r s A B σ hσ y)
            (joinSumCLM r s (fillFun (secIdx r A σ y) ζ, μ)) from by
      rw [invCLM_apply, joinQuotCLM_apply, splitQuotCLM_apply]]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hinv]
  rw [Xb_coordChange_from_indexAt r s A B σ hσ i₂ y]
  rw [sum_localTriv_section r s A B σ hσ i₂.1 y]
  rw [show sumFibreC (r + 1) (s + 1)
        (zCoord i₂.1.1 (σ y), (0 : EuclideanSpace ℂ (Fin (s + 1))))
      = joinSumCLM r s (zCoord i₂.1.1 (σ y), (0 : EuclideanSpace ℂ (Fin (s + 1)))) from
    (joinSumCLM_apply r s (zCoord i₂.1.1 (σ y)) 0).symm]
  -- the filling and the two cancellations
  set c : ℂ := Yv (idxSum r s A B σ hσ y) / aFull r s A B σ hσ y (idxSum r s A B σ hσ y)
    with hc
  have hfill : fillFun (idxSum r s A B σ hσ y)
      (quoFun (idxSum r s A B σ hσ y) (aFull r s A B σ hσ y) Yv)
      = Yv - c • aFull r s A B σ hσ y := by
    rw [hc, eq_sub_iff_add_eq]
    exact (sub_eq_iff_eq_add'.mp
      (sub_fillFun_quoFun _ _ Yv (idxSum_spec r s A B σ hσ y))).symm
  set κ : ℂ := (A.coordChange i₁.1.1 (A.indexAt y) y) (fillFun i₁.1.2 uA) (secIdx r A σ y)
      / secA r A σ y (secIdx r A σ y) with hκ
  have hAcfill : (A.coordChange (A.indexAt y) i₂.1.1 y) (fillFun (secIdx r A σ y) ζ)
      = (A.coordChange (A.indexAt y) i₂.1.1 y)
          ((A.coordChange i₁.1.1 (A.indexAt y) y) (fillFun i₁.1.2 uA))
        - κ • zCoord i₂.1.1 (σ y) := by
    rw [hζ, hκ]
    rw [show fillFun (secIdx r A σ y)
        (quoFun (secIdx r A σ y) (secA r A σ y)
          ((A.coordChange i₁.1.1 (A.indexAt y) y) (fillFun i₁.1.2 uA)))
        = (A.coordChange i₁.1.1 (A.indexAt y) y) (fillFun i₁.1.2 uA)
          - ((A.coordChange i₁.1.1 (A.indexAt y) y) (fillFun i₁.1.2 uA) (secIdx r A σ y)
              / secA r A σ y (secIdx r A σ y)) • secA r A σ y from by
      rw [eq_sub_iff_add_eq]
      exact (sub_eq_iff_eq_add'.mp (sub_fillFun_quoFun (secIdx r A σ y) (secA r A σ y)
        ((A.coordChange i₁.1.1 (A.indexAt y) y) (fillFun i₁.1.2 uA))
        (secA_secIdx_ne_zero r A σ hσ y))).symm]
    rw [map_sub, map_smul, ← zCoord_sigma r A σ hσ i₂.1.1 y]
  have hYval : (SumB r s A B).coordChange ((SumB r s A B).indexAt y) i₂.1 y Yv
      = sumFibreC (r + 1) (s + 1)
          ((A.coordChange (A.indexAt y) i₂.1.1 y) (fillFun (secIdx r A σ y) ζ),
            (B.coordChange (B.indexAt y) i₂.1.2 y) μ) := by
    rw [hY]
    change (SumB r s A B).coordChange ((SumB r s A B).indexAt y) i₂.1 y
        (sumFibreC (r + 1) (s + 1) (fillFun (secIdx r A σ y) ζ, μ))
      = sumFibreC (r + 1) (s + 1)
          ((A.coordChange (A.indexAt y) i₂.1.1 y) (fillFun (secIdx r A σ y) ζ),
            (B.coordChange (B.indexAt y) i₂.1.2 y) μ)
    rw [SumB_coordChange_apply_gen r s A B ((SumB r s A B).indexAt y) i₂.1 y
      (fillFun (secIdx r A σ y) ζ) μ]
    rw [show ((SumB r s A B).indexAt y).1 = A.indexAt y from rfl,
      show ((SumB r s A B).indexAt y).2 = B.indexAt y from rfl]
  have hpair : ((A.coordChange (A.indexAt y) i₂.1.1 y)
          ((A.coordChange i₁.1.1 (A.indexAt y) y) (fillFun i₁.1.2 uA)),
        (B.coordChange (B.indexAt y) i₂.1.2 y) μ)
      = ((A.coordChange i₁.1.1 i₂.1.1 y) (fillFun i₁.1.2 uA),
        (B.coordChange i₁.2 i₂.1.2 y) uB) := by
    refine Prod.ext ?_ ?_
    · exact A.coordChange_comp i₁.1.1 (A.indexAt y) i₂.1.1 y
        ⟨⟨hyA1, A.mem_baseSet_at y⟩, hyA2⟩ (fillFun i₁.1.2 uA)
    · rw [hμ]
      exact B.coordChange_comp i₁.2 (B.indexAt y) i₂.1.2 y
        ⟨⟨mem_Wb_B r s A B σ i₁ hy.1, B.mem_baseSet_at y⟩, hyB2⟩ uB
  have hstep : (SumB r s A B).coordChange ((SumB r s A B).indexAt y) i₂.1 y
        (fillFun (idxSum r s A B σ hσ y)
          (quoFun (idxSum r s A B σ hσ y) (aFull r s A B σ hσ y) Yv))
      = joinSumCLM r s ((A.coordChange i₁.1.1 i₂.1.1 y) (fillFun i₁.1.2 uA),
            (B.coordChange i₁.2 i₂.1.2 y) uB)
        - κ • joinSumCLM r s (zCoord i₂.1.1 (σ y), 0)
        - c • joinSumCLM r s (zCoord i₂.1.1 (σ y), 0) := by
    rw [hfill, map_sub, map_smul, SumB_coordChange_apply_section r s A B σ hσ i₂ y,
      hYval, hAcfill]
    rw [show sumFibreC (r + 1) (s + 1)
          ((A.coordChange (A.indexAt y) i₂.1.1 y)
              ((A.coordChange i₁.1.1 (A.indexAt y) y) (fillFun i₁.1.2 uA)) - κ • zCoord i₂.1.1 (σ y),
            (B.coordChange (B.indexAt y) i₂.1.2 y) μ)
        = sumFibreC (r + 1) (s + 1)
            ((A.coordChange (A.indexAt y) i₂.1.1 y)
              ((A.coordChange i₁.1.1 (A.indexAt y) y) (fillFun i₁.1.2 uA)),
              (B.coordChange (B.indexAt y) i₂.1.2 y) μ)
          - κ • sumFibreC (r + 1) (s + 1) (zCoord i₂.1.1 (σ y),
              (0 : EuclideanSpace ℂ (Fin (s + 1)))) from by
      rw [show ((A.coordChange (A.indexAt y) i₂.1.1 y)
              ((A.coordChange i₁.1.1 (A.indexAt y) y) (fillFun i₁.1.2 uA)) - κ • zCoord i₂.1.1 (σ y),
            (B.coordChange (B.indexAt y) i₂.1.2 y) μ)
          = ((A.coordChange (A.indexAt y) i₂.1.1 y)
              ((A.coordChange i₁.1.1 (A.indexAt y) y) (fillFun i₁.1.2 uA)),
              (B.coordChange (B.indexAt y) i₂.1.2 y) μ)
            - κ • (zCoord i₂.1.1 (σ y), (0 : EuclideanSpace ℂ (Fin (s + 1)))) from by simp]
      rw [map_sub, map_smul]]
    rw [show sumFibreC (r + 1) (s + 1)
          ((A.coordChange (A.indexAt y) i₂.1.1 y)
            ((A.coordChange i₁.1.1 (A.indexAt y) y) (fillFun i₁.1.2 uA)),
            (B.coordChange (B.indexAt y) i₂.1.2 y) μ)
        = joinSumCLM r s ((A.coordChange (A.indexAt y) i₂.1.1 y)
            ((A.coordChange i₁.1.1 (A.indexAt y) y) (fillFun i₁.1.2 uA)),
            (B.coordChange (B.indexAt y) i₂.1.2 y) μ) from rfl,
      hpair,
      show sumFibreC (r + 1) (s + 1) (zCoord i₂.1.1 (σ y),
          (0 : EuclideanSpace ℂ (Fin (s + 1))))
        = joinSumCLM r s (zCoord i₂.1.1 (σ y), (0 : EuclideanSpace ℂ (Fin (s + 1)))) from rfl]
  rw [hstep]
  rw [quoFun_sub_smul_self _ _ _ _ hz₂, quoFun_sub_smul_self _ _ _ _ hz₂]
  rw [invNice_apply, hu_split]

/-! ## The chart conditions and the bundle isomorphism -/

theorem continuousOn_hom_chart (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B)
    (σ : PunctC A) (hσ : IsSec A σ) (i₁ : (ι_A × ι_B) × Fin ((r + 1) + (s + 1)))
    (i₂ : (ι_A × Fin (r + 1)) × ι_B) :
    ContinuousOn (fun y : Y =>
      ((Wb r s A B σ).coordChange ((Wb r s A B σ).indexAt y) i₂ y).comp
        ((homCLM r s A B σ hσ y).comp
          ((Xb r s A B σ hσ).coordChange i₁ ((Xb r s A B σ hσ).indexAt y) y)))
      ((Xb r s A B σ hσ).baseSet i₁ ∩ (Wb r s A B σ).baseSet i₂) :=
  (continuousOn_homNice r s A B σ hσ i₁ i₂).congr
    (fun y hy => hom_chart_clm_eq r s A B σ hσ i₁ i₂ hy)

theorem continuousOn_inv_chart (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B)
    (σ : PunctC A) (hσ : IsSec A σ) (i₁ : (ι_A × Fin (r + 1)) × ι_B)
    (i₂ : (ι_A × ι_B) × Fin ((r + 1) + (s + 1))) :
    ContinuousOn (fun y : Y =>
      ((Xb r s A B σ hσ).coordChange ((Xb r s A B σ hσ).indexAt y) i₂ y).comp
        ((invCLM r s A B σ hσ y).comp
          ((Wb r s A B σ).coordChange i₁ ((Wb r s A B σ).indexAt y) y)))
      ((Wb r s A B σ).baseSet i₁ ∩ (Xb r s A B σ hσ).baseSet i₂) :=
  (continuousOn_invNice r s A B σ hσ i₁ i₂).congr
    (fun y hy => inv_chart_clm_eq r s A B σ hσ i₁ i₂ hy)

/-- **The identification `s^*(Q_{A ⊕ B}) ≅ σ^*(Q_A) ⊕ B` of bundles over `Y`.** -/
noncomputable def bundleIsoAB (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B)
    (σ : PunctC A) (hσ : IsSec A σ) :
    BundleIso (Xb r s A B σ hσ) (Wb r s A B σ) where
  hom y := (homCLM r s A B σ hσ y).toLinearMap
  inv y := (invCLM r s A B σ hσ y).toLinearMap
  left_inv y z := invCLM_homCLM r s A B σ hσ y z
  right_inv y u := homCLM_invCLM r s A B σ hσ y u
  continuous_hom := by
    refine (Work.Thom.continuous_totalSpaceMap_clm_gen (Xb r s A B σ hσ) (Wb r s A B σ)
      (ContinuousMap.id Y) (homCLM r s A B σ hσ) ?_).congr (fun p => rfl)
    intro i₁ i₂
    exact continuousOn_hom_chart r s A B σ hσ i₁ i₂
  continuous_inv := by
    refine (Work.Thom.continuous_totalSpaceMap_clm_gen (Wb r s A B σ) (Xb r s A B σ hσ)
      (ContinuousMap.id Y) (invCLM r s A B σ hσ) ?_).congr (fun p => rfl)
    intro i₁ i₂
    exact continuousOn_inv_chart r s A B σ hσ i₁ i₂


-- MARKER__

end

end WB

theorem exists_bundleIso_comap_tautQuotient_whitneySum {Y : Type} [TopologicalSpace Y]
    {ι_A ι_B : Type} [Fintype ι_A] [Fintype ι_B] {r s : ℕ}
    (A : VectorBundleCore ℂ Y (EuclideanSpace ℂ (Fin (r + 1))) ι_A)
    (B : VectorBundleCore ℂ Y (EuclideanSpace ℂ (Fin (s + 1))) ι_B)
    (σ : C(Y, ↥(Work.Thom.zeroComplement (Work.Thom.realification A))))
    (hσ : ∀ y, (((σ y : ↥(Work.Thom.zeroComplement (Work.Thom.realification A))) :
      (Work.Thom.realification A).TotalSpace)).1 = y) :
    ∃ (sB : C(Y, ↥(Work.Thom.zeroComplement
        (Work.Thom.realification (Work.Whitney.whitneySum (m₁ := r+1) (m₂ := s+1) A B))))),
      (∀ y, (((sB y : ↥(Work.Thom.zeroComplement
          (Work.Thom.realification (Work.Whitney.whitneySum (m₁ := r+1) (m₂ := s+1) A B)))) :
        (Work.Thom.realification (Work.Whitney.whitneySum (m₁ := r+1) (m₂ := s+1) A B)).TotalSpace)).1 = y) ∧
      Nonempty (Work.Thom.BundleIso
        (Work.Thom.bundleComap
          (Work.Thom.tautQuotient (m := (r+1)+s)
            (Work.Whitney.whitneySum (m₁ := r+1) (m₂ := s+1) A B)) sB)
        (Work.Whitney.whitneySum (m₁ := r) (m₂ := s+1)
          (Work.Thom.bundleComap (Work.Thom.tautQuotient (m := r) A) σ) B)) := by
  exact ⟨WB.sumSection r s A B σ hσ, fun y => rfl, ⟨WB.bundleIsoAB r s A B σ hσ⟩⟩

end Work.Whitney
