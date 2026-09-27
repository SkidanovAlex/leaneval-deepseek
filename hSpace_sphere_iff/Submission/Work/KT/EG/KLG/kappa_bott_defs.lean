import Mathlib
import Submission.Work.KT.EG.kappaRedDefs
import Submission.Work.KT.KL.Defs
import Submission.Work.KT.Fund.kappa_const

/-!
# `Work.KT.EG.KLG.kappa_bott_defs` — the explicit frames for the Bott unit computation

Vocabulary for the proof of `Work.KT.EG.KLG.kappa_bott_gen`: for a matrix `E` over `C(X, ℂ)` with
`E * E = E` and `A := gUp X (1 - E)`, `B := gUp X E` (so `A + B = 1`, `A * A = A`, `B * B = B`,
`A * B = B * A = 0`), the geometric target on the two discs is

* `upTgt A B = A ⊕ (B ⊗ R₁)`  with `R₁ = !![1, 0; ζ (1+s)⁻¹, 0]`  (upper disc),
* `dnTgt A B = A ⊕ (B ⊗ R₂)`  with `R₂ = !![ζζ̄, ζ̄ s²(1+s)⁻¹; (1+s) ζ, s²]`  (lower disc),

realised through the frames

* `upFrame A B = !![A; B ⊗ (1+s, ζ)]`, `dnFrame A B = !![A; B ⊗ (ζ̄, 1+s)]`

and the retractions `upRet`, `dnRet` (with `upRet * upFrame = 1`, `dnRet * dnFrame = 1`).  The
clutching unit `u = pullMat (1 - E) + z • pullMat E` is the discrepancy of the two retractions on
the equator, so the whole computation runs through `Work.KT.clutchIdem_mvN`.
-/

namespace Work.KT.EG.KLG

open _root_.Matrix
open Work.KT.Fund.KL

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- The disc-level pull-back of `1 - E`: the "`0`-eigenbundle" part of the Bott unit. -/
def Amat {n : ℕ} (E : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ) :=
  Work.KT.Fund.KC.gUp X (1 - E)

/-- The disc-level pull-back of `E`: the "Hopf-twisted" part of the Bott unit. -/
def Bmat {n : ℕ} (E : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ) :=
  Work.KT.Fund.KC.gUp X E

/-- The upper-disc frame `v ↦ (A v, B v ⊗ (1+s, ζ))`. -/
def upFrame {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) :
    Matrix (Fin n ⊕ (Fin n × Fin 2)) (Fin n) C(X × Ball ℂ, ℂ) :=
  fun i j => match i with
    | Sum.inl a => A a j
    | Sum.inr aα => B aα.1 j * (if aα.2 = 0 then 1 + Work.KT.Fund.KL.zs X else Work.KT.Fund.KL.zc X)

/-- The lower-disc frame `v ↦ (A v, B v ⊗ (ζ̄, 1+s))`. -/
def dnFrame {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) :
    Matrix (Fin n ⊕ (Fin n × Fin 2)) (Fin n) C(X × Ball ℂ, ℂ) :=
  fun i j => match i with
    | Sum.inl a => A a j
    | Sum.inr aα => B aα.1 j * (if aα.2 = 0 then Work.KT.Fund.KL.zcb X else 1 + Work.KT.Fund.KL.zs X)

/-- The upper-disc retraction `[A, B (1+s)⁻¹, 0]`. -/
def upRet {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) :
    Matrix (Fin n) (Fin n ⊕ (Fin n × Fin 2)) C(X × Ball ℂ, ℂ) :=
  fun i j => match j with
    | Sum.inl a => A i a
    | Sum.inr aα => B i aα.1 * (if aα.2 = 0 then Work.KT.Fund.KL.zsinv X else 0)

/-- The lower-disc retraction `[A, ζ B, s²(1+s)⁻¹ B]`. -/
def dnRet {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) :
    Matrix (Fin n) (Fin n ⊕ (Fin n × Fin 2)) C(X × Ball ℂ, ℂ) :=
  fun i j => match j with
    | Sum.inl a => A i a
    | Sum.inr aα => B i aα.1 *
        (if aα.2 = 0 then Work.KT.Fund.KL.zc X
         else Work.KT.Fund.KL.zs X * Work.KT.Fund.KL.zs X * Work.KT.Fund.KL.zsinv X)

/-- The upper-disc target `A ⊕ (B ⊗ R₁)`, `R₁ = !![1, 0; ζ(1+s)⁻¹, 0]`. -/
def upTgt {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) :
    Matrix (Fin n ⊕ (Fin n × Fin 2)) (Fin n ⊕ (Fin n × Fin 2)) C(X × Ball ℂ, ℂ) :=
  upFrame X A B * upRet X A B

/-- The lower-disc target `A ⊕ (B ⊗ R₂)`, `R₂ = !![ζζ̄, ζ̄ s²(1+s)⁻¹; (1+s)ζ, s²]`. -/
def dnTgt {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) :
    Matrix (Fin n ⊕ (Fin n × Fin 2)) (Fin n ⊕ (Fin n × Fin 2)) C(X × Ball ℂ, ℂ) :=
  dnFrame X A B * dnRet X A B

/-- The `2 × 2` block `R₁` of the upper target. -/
def R1 : Matrix (Fin 2) (Fin 2) C(X × Ball ℂ, ℂ) :=
  !![1, 0; Work.KT.Fund.KL.zc X * Work.KT.Fund.KL.zsinv X, 0]

/-- The `2 × 2` block `R₂` of the lower target. -/
def R2 : Matrix (Fin 2) (Fin 2) C(X × Ball ℂ, ℂ) :=
  !![Work.KT.Fund.KL.zc X * Work.KT.Fund.KL.zcb X,
      Work.KT.Fund.KL.zcb X * (Work.KT.Fund.KL.zs X * Work.KT.Fund.KL.zs X) *
        Work.KT.Fund.KL.zsinv X;
     (1 + Work.KT.Fund.KL.zs X) * Work.KT.Fund.KL.zc X,
      Work.KT.Fund.KL.zs X * Work.KT.Fund.KL.zs X]

/-- The unit whose clutched class is computed: `(1-E) + zE`, as a matrix over `C(X × S¹, ℂ)`. -/
def bottUnitVal {n : ℕ} (E : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ) :=
  Work.KT.Fund.pullMat X (1 - E) + (Work.KT.zUnit X : C(X × Sph ℂ, ℂ)) • Work.KT.Fund.pullMat X E

/-! ## The bijection `Fin n ⊕ (Fin n × Fin 2) ≃ Fin (n + n * 2)` -/

/-- The index bijection used to compare the block-indexed target matrices with `Fin`-indexed ones. -/
def idxEquiv (n : ℕ) : (Fin n ⊕ (Fin n × Fin 2)) ≃ Fin (n + n * 2) :=
  (Equiv.sumCongr (Equiv.refl (Fin n)) finProdFinEquiv).trans finSumFinEquiv

/-! ## The glued targets -/

/-- The glued target over `pullAlg2 X` attached to a pair of matching disc targets. -/
def tgtPair {n : ℕ} (E : Matrix (Fin n) (Fin n) C(X, ℂ))
    (h : (upTgt X (Amat X E) (Bmat X E)).map (fun f => Work.KT.Fund.bdryRestrict X f)
      = (dnTgt X (Amat X E) (Bmat X E)).map (fun f => Work.KT.Fund.bdryRestrict X f)) :
    Matrix (Fin n ⊕ (Fin n × Fin 2)) (Fin n ⊕ (Fin n × Fin 2)) ↥(Work.KT.Fund.pullAlg2 X) :=
  Work.KT.Fund.pairMat X (upTgt X (Amat X E) (Bmat X E)) (dnTgt X (Amat X E) (Bmat X E)) h

/-- The glued Hopf idempotent `(RhopUp, RhopDn)` over `pullAlg2 X`. -/
def RhopPair
    (h : (Work.KT.Fund.KL.RhopUp X).map (fun f => Work.KT.Fund.bdryRestrict X f)
      = (Work.KT.Fund.KL.RhopDn X).map (fun f => Work.KT.Fund.bdryRestrict X f)) :
    Matrix (Fin 2) (Fin 2) ↥(Work.KT.Fund.pullAlg2 X) :=
  Work.KT.Fund.pairMat X (Work.KT.Fund.KL.RhopUp X) (Work.KT.Fund.KL.RhopDn X) h

/-- The glued `2 × 2` block `(R₁, R₂)` over `pullAlg2 X`. -/
def R12Pair
    (h : (R1 X).map (fun f => Work.KT.Fund.bdryRestrict X f)
      = (R2 X).map (fun f => Work.KT.Fund.bdryRestrict X f)) :
    Matrix (Fin 2) (Fin 2) ↥(Work.KT.Fund.pullAlg2 X) :=
  Work.KT.Fund.pairMat X (R1 X) (R2 X) h

/-- The pull-back of a matrix over `C(X, ℂ)` to the glued algebra `pullAlg2 X`. -/
def trivPair {n : ℕ} (M : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin n) (Fin n) ↥(Work.KT.Fund.pullAlg2 X) :=
  Work.KT.Fund.pairMat X (Work.KT.Fund.KC.gUp X M) (Work.KT.Fund.KC.gUp X M) rfl

/-- The geometric target over `pullAlg2 X`: `A ⊕ (B ⊗ Rhop)` on the two discs. -/
def geoPair {n : ℕ} (E : Matrix (Fin n) (Fin n) C(X, ℂ))
    (h : (Work.KT.Fund.KL.TupD X (Amat X E) (Bmat X E)).map
          (fun f => Work.KT.Fund.bdryRestrict X f)
      = (Work.KT.Fund.KL.TdnD X (Amat X E) (Bmat X E)).map
          (fun f => Work.KT.Fund.bdryRestrict X f)) :
    Matrix (Fin n ⊕ (Fin n × Fin 2)) (Fin n ⊕ (Fin n × Fin 2)) ↥(Work.KT.Fund.pullAlg2 X) :=
  Work.KT.Fund.pairMat X (Work.KT.Fund.KL.TupD X (Amat X E) (Bmat X E))
    (Work.KT.Fund.KL.TdnD X (Amat X E) (Bmat X E)) h

/-! ## The elementary algebra of `Amat`, `Bmat` -/

section AmatBmat

variable {n : ℕ} (E : Matrix (Fin n) (Fin n) C(X, ℂ))

/-- `gUp` is additive. -/
lemma KLgUp_add {n : ℕ} (M N : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Work.KT.Fund.KC.gUp X (M + N) = Work.KT.Fund.KC.gUp X M + Work.KT.Fund.KC.gUp X N := by
  rw [Work.KT.Fund.KC.gUp_apply, Work.KT.Fund.KC.gUp_apply, Work.KT.Fund.KC.gUp_apply]
  exact Matrix.map_add (⇑(Work.KT.Fund.KC.discHom X))
    (fun a b => map_add (Work.KT.Fund.KC.discHom X) a b) M N

/-- `gUp` of `0` is `0`. -/
lemma KLgUp_zero {n : ℕ} :
    Work.KT.Fund.KC.gUp X (0 : Matrix (Fin n) (Fin n) C(X, ℂ)) = 0 := by
  rw [Work.KT.Fund.KC.gUp_apply]
  exact Work.KT.Bott.matrix_map_zero (Work.KT.Fund.KC.discHom X)

lemma Amat_add_Bmat : Amat X E + Bmat X E = 1 := by
  rw [Amat, Bmat, ← KLgUp_add, sub_add_cancel, Work.KT.Fund.KC.gUp_one]

variable (hE : E * E = E)
include hE

lemma Amat_mul_self : Amat X E * Amat X E = Amat X E := by
  rw [Amat, ← Work.KT.Fund.KC.gUp_mul]
  congr 1
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hE]
  abel

lemma Bmat_mul_self : Bmat X E * Bmat X E = Bmat X E := by
  rw [Bmat, ← Work.KT.Fund.KC.gUp_mul, hE]

lemma Amat_mul_Bmat : Amat X E * Bmat X E = 0 := by
  rw [Amat, Bmat, ← Work.KT.Fund.KC.gUp_mul,
    show (1 - E) * E = 0 by rw [Matrix.sub_mul, Matrix.one_mul, hE, sub_self], KLgUp_zero]

lemma Bmat_mul_Amat : Bmat X E * Amat X E = 0 := by
  rw [Amat, Bmat, ← Work.KT.Fund.KC.gUp_mul,
    show E * (1 - E) = 0 by rw [Matrix.mul_sub, Matrix.mul_one, hE, sub_self], KLgUp_zero]

end AmatBmat

/-! ## The Kronecker product of Murray–von Neumann data -/

section Kron

variable {A : Type} [Ring A]

/-- The Kronecker product of Murray–von Neumann data: `p ~ p'` and `q ~ q'` imply
`p ⊗ q ~ p' ⊗ q'`. -/
theorem kron_mvN (hcomm : ∀ x y : A, x * y = y * x)
    {p p' q q' : Work.KT.Mat A} (hp : p.MvN p') (hq : q.MvN q') :
    (Work.KT.Mat.kron p q).MvN (Work.KT.Mat.kron p' q') := by
  obtain ⟨a₁, b₁, h₁, h₁'⟩ := hp
  obtain ⟨a₂, b₂, h₂, h₂'⟩ := hq
  refine ⟨Work.KT.kronMatR a₁ a₂, Work.KT.kronMatR b₁ b₂, ?_, ?_⟩
  · change Work.KT.kronMatR b₁ b₂ * Work.KT.kronMatR a₁ a₂ = Work.KT.kronMatR p.2 q.2
    rw [← Work.KT.kronMatR_mul hcomm, h₁, h₂]
  · change Work.KT.kronMatR a₁ a₂ * Work.KT.kronMatR b₁ b₂ = Work.KT.kronMatR p'.2 q'.2
    rw [← Work.KT.kronMatR_mul hcomm, h₁', h₂']

end Kron

/-! ## Entries and idempotency of the elementary `2 × 2` blocks -/

section R12

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

@[simp] lemma R1_apply_00 : R1 X 0 0 = 1 := by simp [R1]
@[simp] lemma R1_apply_01 : R1 X 0 1 = 0 := by simp [R1]
@[simp] lemma R1_apply_10 : R1 X 1 0 = Work.KT.Fund.KL.zc X * Work.KT.Fund.KL.zsinv X := by
  simp [R1]
@[simp] lemma R1_apply_11 : R1 X 1 1 = 0 := by simp [R1]

@[simp] lemma R2_apply_00 : R2 X 0 0 = Work.KT.Fund.KL.zc X * Work.KT.Fund.KL.zcb X := by
  simp [R2]
@[simp] lemma R2_apply_01 :
    R2 X 0 1 = Work.KT.Fund.KL.zcb X * (Work.KT.Fund.KL.zs X * Work.KT.Fund.KL.zs X) *
      Work.KT.Fund.KL.zsinv X := by
  simp [R2]
@[simp] lemma R2_apply_10 :
    R2 X 1 0 = (1 + Work.KT.Fund.KL.zs X) * Work.KT.Fund.KL.zc X := by
  simp [R2]
@[simp] lemma R2_apply_11 : R2 X 1 1 = Work.KT.Fund.KL.zs X * Work.KT.Fund.KL.zs X := by
  simp [R2]

/-- `R₁` is idempotent. -/
theorem R1_mul_self : R1 X * R1 X = R1 X := by
  refine Work.KT.Fund.twoByTwo_idem_of_trace_det (R1 X) ?_ ?_
  · rw [R1_apply_00, R1_apply_11, add_zero]
  · rw [R1_apply_00, R1_apply_11, R1_apply_01, R1_apply_10, mul_zero, zero_mul]

/-- `R₂` is idempotent. -/
theorem R2_mul_self : R2 X * R2 X = R2 X := by
  refine Work.KT.Fund.twoByTwo_idem_of_trace_det (R2 X) ?_ ?_
  · rw [R2_apply_00, R2_apply_11, Work.KT.Fund.KL.zc_mul_zcb_eq]
    ring
  · rw [R2_apply_00, R2_apply_11, R2_apply_01, R2_apply_10]
    rw [show (Work.KT.Fund.KL.zcb X * (Work.KT.Fund.KL.zs X * Work.KT.Fund.KL.zs X) *
          Work.KT.Fund.KL.zsinv X) * ((1 + Work.KT.Fund.KL.zs X) * Work.KT.Fund.KL.zc X)
        = (Work.KT.Fund.KL.zc X * Work.KT.Fund.KL.zcb X) *
            ((Work.KT.Fund.KL.zs X * Work.KT.Fund.KL.zs X) *
              (Work.KT.Fund.KL.zsinv X * (1 + Work.KT.Fund.KL.zs X))) from by ring,
      Work.KT.Fund.KL.zsinv_mul_one_add_zs, mul_one]

end R12

/-! ## Idempotency of the glued representatives -/

section Idem

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- The pull-back of an idempotent matrix to the glued algebra is idempotent. -/
theorem trivPair_mul_self {n : ℕ} (E : Matrix (Fin n) (Fin n) C(X, ℂ)) (hE : E * E = E) :
    trivPair X E * trivPair X E = trivPair X E := by
  show (Work.KT.Fund.pairMat X (Work.KT.Fund.KC.gUp X E) (Work.KT.Fund.KC.gUp X E) rfl) *
      (Work.KT.Fund.pairMat X (Work.KT.Fund.KC.gUp X E) (Work.KT.Fund.KC.gUp X E) rfl)
      = Work.KT.Fund.pairMat X (Work.KT.Fund.KC.gUp X E) (Work.KT.Fund.KC.gUp X E) rfl
  rw [Work.KT.pairMat_pull_mul rfl rfl]
  exact Work.KT.pairMat_pull_congr
    (show Work.KT.Fund.KC.gUp X E * Work.KT.Fund.KC.gUp X E = Work.KT.Fund.KC.gUp X E from by
      rw [← Work.KT.Fund.KC.gUp_mul, hE])
    (show Work.KT.Fund.KC.gUp X E * Work.KT.Fund.KC.gUp X E = Work.KT.Fund.KC.gUp X E from by
      rw [← Work.KT.Fund.KC.gUp_mul, hE]) _ _

/-- The glued `2 × 2` block `(R₁, R₂)` is idempotent. -/
theorem R12Pair_mul_self
    (h12 : (R1 X).map (fun f => Work.KT.Fund.bdryRestrict X f)
      = (R2 X).map (fun f => Work.KT.Fund.bdryRestrict X f)) :
    R12Pair X h12 * R12Pair X h12 = R12Pair X h12 := by
  show Work.KT.Fund.pairMat X (R1 X) (R2 X) h12 * Work.KT.Fund.pairMat X (R1 X) (R2 X) h12
    = Work.KT.Fund.pairMat X (R1 X) (R2 X) h12
  rw [Work.KT.pairMat_pull_mul h12 h12]
  exact Work.KT.pairMat_pull_congr (R1_mul_self X) (R2_mul_self X) _ _

end Idem

end

end Work.KT.EG.KLG
