import Mathlib
import Submission.Work.KT.EG.KLG.kappa_bott_defs
import Submission.Work.KT.KL.LiftMul

/-!
# `Work.KT.EG.KLG.bottUnit_bdry` — the equator bookkeeping for the Bott unit

For an idempotent `E` over `C(X, ℂ)` the Bott unit `u = (1-E) + z·E` over `C(X × S¹, ℂ)` is the
discrepancy between the upper- and lower-disc data `Work.KT.EG.KLG.kappa_bott_defs` attaches to
`E`: on the equator `S¹ ⊂ D` (`s = √(1-|ζ|²) = 0`, so `1 + s ↦ 1`, `ζ ↦ z`, `ζ̄ ↦ z⁻¹`,
`(1+s)⁻¹ ↦ 1`)

* `u * upRet|S¹ = dnRet|S¹`,
* `upFrame|S¹ = dnFrame|S¹ * u`,
* `upTgt|S¹ = dnTgt|S¹`.

The first two are the elementary algebra of the orthogonal idempotents `A' = 1 - E`, `B' = E`;
the third follows by multiplying them.
-/

namespace Work.KT.EG.KLG

open _root_.Matrix

noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-! ## The boundary value of `gUp` -/

/-- The boundary value of a matrix lifted to the disc is its pull-back to the circle. -/
@[simp] lemma bdry_gUp_entry {m : ℕ} (M : Matrix (Fin m) (Fin m) C(X, ℂ)) (i j : Fin m) :
    Work.KT.Fund.bdryRestrict X (Work.KT.Fund.KC.gUp X M i j)
      = Work.KT.Fund.pullMat X M i j :=
  congrFun (congrFun (Work.KT.Fund.KC.gUp_bdry X M) i) j

/-! ## The four boundary matrices -/

/-- The boundary value of `upRet A B`: the block matrix `[A, B, 0]`. -/
def upRetB {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) :
    Matrix (Fin n) (Fin n ⊕ (Fin n × Fin 2)) C(X × Sph ℂ, ℂ) :=
  fun i j => match j with
    | Sum.inl a => A i a
    | Sum.inr aα => B i aα.1 * (if aα.2 = 0 then 1 else 0)

/-- The boundary value of `dnRet A B`: the block matrix `[A, z B, 0]` (`w = z`). -/
def dnRetB {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
    (w : C(X × Sph ℂ, ℂ)) :
    Matrix (Fin n) (Fin n ⊕ (Fin n × Fin 2)) C(X × Sph ℂ, ℂ) :=
  fun i j => match j with
    | Sum.inl a => A i a
    | Sum.inr aα => B i aα.1 * (if aα.2 = 0 then w else 0)

/-- The boundary value of `upFrame A B`: the block column `[[A], [B], [z B]]`. -/
def upFrameB {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
    (w : C(X × Sph ℂ, ℂ)) :
    Matrix (Fin n ⊕ (Fin n × Fin 2)) (Fin n) C(X × Sph ℂ, ℂ) :=
  fun i j => match i with
    | Sum.inl a => A a j
    | Sum.inr aα => B aα.1 j * (if aα.2 = 0 then 1 else w)

/-- The boundary value of `dnFrame A B`: the block column `[[A], [z⁻¹ B], [B]]` (`v = z⁻¹`). -/
def dnFrameB {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
    (v : C(X × Sph ℂ, ℂ)) :
    Matrix (Fin n ⊕ (Fin n × Fin 2)) (Fin n) C(X × Sph ℂ, ℂ) :=
  fun i j => match i with
    | Sum.inl a => A a j
    | Sum.inr aα => B aα.1 j * (if aα.2 = 0 then v else 1)

/-! ## The boundary identifications -/

lemma bdry_upRet {n : ℕ} (E : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    (upRet X (Amat X E) (Bmat X E)).map ⇑(Work.KT.Fund.bdryRestrict X)
      = upRetB X (Work.KT.Fund.pullMat X (1 - E)) (Work.KT.Fund.pullMat X E) := by
  ext i j
  rcases j with a | ⟨a, α⟩
  · simp only [Matrix.map_apply, upRet, upRetB, Amat, bdry_gUp_entry]
  · simp only [Matrix.map_apply, upRet, upRetB, Bmat]
    by_cases hα : α = 0
    · subst hα; simp [Work.KT.Fund.KL.bdryRestrict_zsinv]
    · simp [hα]

lemma bdry_dnRet {n : ℕ} (E : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    (dnRet X (Amat X E) (Bmat X E)).map ⇑(Work.KT.Fund.bdryRestrict X)
      = dnRetB X (Work.KT.Fund.pullMat X (1 - E)) (Work.KT.Fund.pullMat X E)
          (Work.KT.zUnit X : C(X × Sph ℂ, ℂ)) := by
  ext i j
  rcases j with a | ⟨a, α⟩
  · simp only [Matrix.map_apply, dnRet, dnRetB, Amat, bdry_gUp_entry]
  · simp only [Matrix.map_apply, dnRet, dnRetB, Bmat]
    by_cases hα : α = 0
    · subst hα; simp [Work.KT.Fund.KL.bdryRestrict_zc]
    · simp [hα, Work.KT.Fund.KL.bdryRestrict_zs]

lemma bdry_upFrame {n : ℕ} (E : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    (upFrame X (Amat X E) (Bmat X E)).map ⇑(Work.KT.Fund.bdryRestrict X)
      = upFrameB X (Work.KT.Fund.pullMat X (1 - E)) (Work.KT.Fund.pullMat X E)
          (Work.KT.zUnit X : C(X × Sph ℂ, ℂ)) := by
  ext i j
  rcases i with a | ⟨a, α⟩
  · simp only [Matrix.map_apply, upFrame, upFrameB, Amat, bdry_gUp_entry]
  · simp only [Matrix.map_apply, upFrame, upFrameB, Bmat]
    by_cases hα : α = 0
    · subst hα; simp [Work.KT.Fund.KL.bdryRestrict_zs]
    · simp [hα, Work.KT.Fund.KL.bdryRestrict_zc]

lemma bdry_dnFrame {n : ℕ} (E : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    (dnFrame X (Amat X E) (Bmat X E)).map ⇑(Work.KT.Fund.bdryRestrict X)
      = dnFrameB X (Work.KT.Fund.pullMat X (1 - E)) (Work.KT.Fund.pullMat X E)
          (↑((Work.KT.zUnit X)⁻¹) : C(X × Sph ℂ, ℂ)) := by
  ext i j
  rcases i with a | ⟨a, α⟩
  · simp only [Matrix.map_apply, dnFrame, dnFrameB, Amat, bdry_gUp_entry]
  · simp only [Matrix.map_apply, dnFrame, dnFrameB, Bmat]
    by_cases hα : α = 0
    · subst hα; simp [Work.KT.Fund.KL.bdryRestrict_zcb]
    · simp [hα, Work.KT.Fund.KL.bdryRestrict_zs]

/-! ## The algebra of the boundary matrices -/

/-- On the equator the unit `(1-E) + z·E` sends the upper retraction `[A, B, 0]` to the lower
retraction `[A, z B, 0]`. -/
lemma bottUnit_mul_upRetB {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
    (w : C(X × Sph ℂ, ℂ)) (hA : A * A = A) (hAB : A * B = 0) (hBA : B * A = 0)
    (hB : B * B = B) :
    (A + w • B) * upRetB X A B = dnRetB X A B w := by
  have h1 : (A + w • B) * A = A := by
    rw [add_mul, smul_mul_assoc, hBA, smul_zero, add_zero, hA]
  have h2 : (A + w • B) * B = w • B := by
    rw [add_mul, smul_mul_assoc, hB, hAB, zero_add]
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply]
  rcases j with b | ⟨b, β⟩
  · simp only [upRetB, dnRetB]
    rw [← Matrix.mul_apply, h1]
  · simp only [upRetB, dnRetB]
    have hfac : (∑ k, (A + w • B) i k * (B k b * (if β = 0 then (1 : C(X × Sph ℂ, ℂ)) else 0)))
        = ((A + w • B) * B) i b * (if β = 0 then 1 else 0) := by
      rw [show (∑ k, (A + w • B) i k * (B k b * (if β = 0 then (1 : C(X × Sph ℂ, ℂ)) else 0)))
          = ∑ k, ((A + w • B) i k * B k b) * (if β = 0 then (1 : C(X × Sph ℂ, ℂ)) else 0)
          from Finset.sum_congr rfl (fun k _ => by rw [mul_assoc])]
      rw [← Finset.sum_mul, ← Matrix.mul_apply]
    rw [hfac]
    by_cases hβ : β = 0
    · subst hβ
      simp only [Fin.isValue, if_true]
      rw [h2, Matrix.smul_apply, smul_eq_mul]
      ring
    · rw [if_neg hβ, if_neg hβ, mul_zero, mul_zero]

/-- On the equator the upper frame is the lower frame twisted by the Bott unit `(1-E) + z·E`. -/
lemma upFrameB_eq_dnFrameB_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
    (w v : C(X × Sph ℂ, ℂ)) (hA : A * A = A) (hAB : A * B = 0) (hBA : B * A = 0)
    (hB : B * B = B) (hvw : v * w = 1) :
    upFrameB X A B w = dnFrameB X A B v * (A + w • B) := by
  have h3 : A * (A + w • B) = A := by
    rw [mul_add, Algebra.mul_smul_comm, hAB, smul_zero, add_zero, hA]
  have h4 : B * (A + w • B) = w • B := by
    rw [mul_add, Algebra.mul_smul_comm, hBA, hB, zero_add]
  have h5 : (v • B) * (A + w • B) = B := by
    rw [Algebra.smul_mul_assoc, h4, smul_smul, hvw, one_smul]
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply]
  rcases i with a | ⟨a, α⟩
  · simp only [upFrameB, dnFrameB]
    rw [← Matrix.mul_apply, h3]
  · by_cases hα : α = 0
    · simp only [upFrameB, dnFrameB, if_pos hα, mul_one]
      rw [show (∑ k, (B a k * v) * (A + w • B) k j) = ((v • B) * (A + w • B)) a j from by
        rw [Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro k _
        rw [Matrix.smul_apply, smul_eq_mul, mul_comm (B a k) v]]
      rw [h5]
    · simp only [upFrameB, dnFrameB, if_neg hα, mul_one]
      rw [← Matrix.mul_apply, h4, Matrix.smul_apply, smul_eq_mul, mul_comm]

/-! ## The target -/

theorem bottUnit_bdry (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {n : ℕ} (E : Matrix (Fin n) (Fin n) C(X, ℂ)) (hE : E * E = E) :
    ((Work.KT.Fund.pullMat X (1 - E) + (Work.KT.zUnit X : C(X × Work.KT.Sph ℂ, ℂ)) •
        Work.KT.Fund.pullMat X E) *
      ((Work.KT.EG.KLG.upRet X (Work.KT.EG.KLG.Amat X E) (Work.KT.EG.KLG.Bmat X E)).map
        (fun f => Work.KT.Fund.bdryRestrict X f))
    = (Work.KT.EG.KLG.dnRet X (Work.KT.EG.KLG.Amat X E) (Work.KT.EG.KLG.Bmat X E)).map
        (fun f => Work.KT.Fund.bdryRestrict X f)) ∧
    ((Work.KT.EG.KLG.upFrame X (Work.KT.EG.KLG.Amat X E) (Work.KT.EG.KLG.Bmat X E)).map
        (fun f => Work.KT.Fund.bdryRestrict X f)
      = (Work.KT.EG.KLG.dnFrame X (Work.KT.EG.KLG.Amat X E) (Work.KT.EG.KLG.Bmat X E)).map
          (fun f => Work.KT.Fund.bdryRestrict X f) *
        (Work.KT.Fund.pullMat X (1 - E) + (Work.KT.zUnit X : C(X × Work.KT.Sph ℂ, ℂ)) •
          Work.KT.Fund.pullMat X E)) ∧
    ((Work.KT.EG.KLG.upTgt X (Work.KT.EG.KLG.Amat X E) (Work.KT.EG.KLG.Bmat X E)).map
        (fun f => Work.KT.Fund.bdryRestrict X f)
      = (Work.KT.EG.KLG.dnTgt X (Work.KT.EG.KLG.Amat X E) (Work.KT.EG.KLG.Bmat X E)).map
          (fun f => Work.KT.Fund.bdryRestrict X f)) := by
  have hAA : Work.KT.Fund.pullMat X (1 - E) * Work.KT.Fund.pullMat X (1 - E)
      = Work.KT.Fund.pullMat X (1 - E) := by
    rw [← Work.KT.KL.pullMat_mul X,
      show (1 - E) * (1 - E) = 1 - E by
        rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hE]; abel]
  have hAB : Work.KT.Fund.pullMat X (1 - E) * Work.KT.Fund.pullMat X E = 0 := by
    rw [← Work.KT.KL.pullMat_mul X,
      show (1 - E) * E = 0 by rw [Matrix.sub_mul, Matrix.one_mul, hE, sub_self],
      Work.KT.KL.pullMat_zero X]
  have hBA : Work.KT.Fund.pullMat X E * Work.KT.Fund.pullMat X (1 - E) = 0 := by
    rw [← Work.KT.KL.pullMat_mul X,
      show E * (1 - E) = 0 by rw [Matrix.mul_sub, Matrix.mul_one, hE, sub_self],
      Work.KT.KL.pullMat_zero X]
  have hBB : Work.KT.Fund.pullMat X E * Work.KT.Fund.pullMat X E
      = Work.KT.Fund.pullMat X E := by
    rw [← Work.KT.KL.pullMat_mul X, hE]
  have hvw : (↑((Work.KT.zUnit X)⁻¹) : C(X × Sph ℂ, ℂ))
      * (↑(Work.KT.zUnit X) : C(X × Sph ℂ, ℂ)) = 1 := by
    simpa using congrArg (fun a : (C(X × Sph ℂ, ℂ))ˣ => (a : C(X × Sph ℂ, ℂ)))
      (Units.inv_mul (Work.KT.zUnit X))
  refine ⟨?_, ?_, ?_⟩
  · rw [bdry_upRet X E, bdry_dnRet X E]
    exact bottUnit_mul_upRetB X _ _ _ hAA hAB hBA hBB
  · rw [bdry_upFrame X E, bdry_dnFrame X E]
    exact upFrameB_eq_dnFrameB_mul X _ _ _ _ hAA hAB hBA hBB hvw
  · have hU : (upTgt X (Amat X E) (Bmat X E)).map (fun f => Work.KT.Fund.bdryRestrict X f)
        = (upFrame X (Amat X E) (Bmat X E)).map (fun f => Work.KT.Fund.bdryRestrict X f)
          * (upRet X (Amat X E) (Bmat X E)).map (fun f => Work.KT.Fund.bdryRestrict X f) := by
      rw [upTgt]
      exact (Matrix.map_mul' (Work.KT.Fund.bdryRestrict X)
        (upFrame X (Amat X E) (Bmat X E)) (upRet X (Amat X E) (Bmat X E))).symm
    have hD : (dnTgt X (Amat X E) (Bmat X E)).map (fun f => Work.KT.Fund.bdryRestrict X f)
        = (dnFrame X (Amat X E) (Bmat X E)).map (fun f => Work.KT.Fund.bdryRestrict X f)
          * (dnRet X (Amat X E) (Bmat X E)).map (fun f => Work.KT.Fund.bdryRestrict X f) := by
      rw [dnTgt]
      exact (Matrix.map_mul' (Work.KT.Fund.bdryRestrict X)
        (dnFrame X (Amat X E) (Bmat X E)) (dnRet X (Amat X E) (Bmat X E))).symm
    rw [hU, hD, bdry_upFrame X E, bdry_dnFrame X E, bdry_upRet X E, bdry_dnRet X E]
    rw [upFrameB_eq_dnFrameB_mul X (Work.KT.Fund.pullMat X (1 - E)) (Work.KT.Fund.pullMat X E)
      (Work.KT.zUnit X : C(X × Sph ℂ, ℂ)) (↑((Work.KT.zUnit X)⁻¹) : C(X × Sph ℂ, ℂ))
      hAA hAB hBA hBB hvw]
    rw [Matrix.mul_assoc]
    rw [bottUnit_mul_upRetB X (Work.KT.Fund.pullMat X (1 - E)) (Work.KT.Fund.pullMat X E)
      (Work.KT.zUnit X : C(X × Sph ℂ, ℂ)) hAA hAB hBA hBB]

end

end Work.KT.EG.KLG
