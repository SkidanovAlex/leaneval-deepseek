import Mathlib
import Submission.Work.KT.Fund.Kappa
import Submission.Work.KT.Fund.kappa_indep
import Submission.Work.KT.Fund.kappa_const
import Submission.Work.KT.Fund.kappa_homotopic
import Submission.Work.KT.Fund.orthProj_mul_unit
import Submission.Work.KT.Fund.map_orthProj
import Submission.Work.KT.Fund.clutch_agree
import Submission.Work.KT.Fund.Basic
import Submission.Work.KT.clutchIdem_cls_indep

/-!
# `Work.KT.EG.kappa_abs` — absorption of a unit pulled back from `X`

Let `X` be a compact Hausdorff space, `g` a unit of matrices over `C(X, ℂ)`, and `w` a unit over
`C(X × S¹, ℂ)`.  Then the clutched class `κ` of `u = pullMat g * w` agrees with `κ w`.

The gauge transformation `diag (1, ĝ)` (where `ĝ` is the extension of `g` to the disc, constant in
the disc variable) relates the two clutching data compatibly on both discs, so the two clutched
idempotents are Murray–von Neumann equivalent.

The file is organised so that all the linear algebra is done over an *arbitrary* commutative ring
with star (`R` below); only the final step instantiates `R = C(X × D, ℂ)`.
-/

namespace Work.KT.EG

open _root_.Matrix

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

/-! ## Generic linear algebra -/

/-- **The orthogonal projection of a block unit times a framed column.**  If `E * Δ = 1` then
multiplying a frame `B` on the left by `Δ` leaves the projection `orthProj` fixed, after left
multiplication by `Δ`: `orthProj (Δ * B) * (Δ * orthProj B) = Δ * orthProj B` and
`orthProj B * (E * orthProj (Δ * B)) = E * orthProj (Δ * B)`. -/
theorem orthProj_mul_unit_block {R : Type} [CommRing R] [StarRing R] {n : ℕ}
    (Δ E : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) (B : Matrix (Fin n ⊕ Fin n) (Fin n) R)
    (hEΔ : E * Δ = 1) (hΔE : Δ * E = 1)
    (hB : IsUnit (Bᴴ * B)) (hΔB : IsUnit ((Δ * B)ᴴ * (Δ * B))) :
    Work.KT.Fund.orthProj R (Δ * B) * (Δ * Work.KT.Fund.orthProj R B)
        = Δ * Work.KT.Fund.orthProj R B ∧
    Work.KT.Fund.orthProj R B * (E * Work.KT.Fund.orthProj R (Δ * B))
        = E * Work.KT.Fund.orthProj R (Δ * B) := by
  have hYB : (Ring.inverse (Bᴴ * B) * Bᴴ) * B = 1 := by
    rw [Matrix.mul_assoc, Ring.inverse_mul_cancel _ hB]
  have hY'DB : (Ring.inverse ((Δ * B)ᴴ * (Δ * B)) * (Δ * B)ᴴ) * (Δ * B) = 1 := by
    rw [Matrix.mul_assoc, Ring.inverse_mul_cancel _ hΔB]
  have hpB : B * (Ring.inverse (Bᴴ * B) * Bᴴ) = Work.KT.Fund.orthProj R B :=
    Work.KT.Fund.KC.orthProj_eq_mul R B
  have hpDB : (Δ * B) * (Ring.inverse ((Δ * B)ᴴ * (Δ * B)) * (Δ * B)ᴴ)
      = Work.KT.Fund.orthProj R (Δ * B) := Work.KT.Fund.KC.orthProj_eq_mul R (Δ * B)
  constructor
  · rw [← hpDB, ← hpB]
    rw [show ((Δ * B) * (Ring.inverse ((Δ * B)ᴴ * (Δ * B)) * (Δ * B)ᴴ))
          * (Δ * (B * (Ring.inverse (Bᴴ * B) * Bᴴ)))
        = (Δ * B) * ((Ring.inverse ((Δ * B)ᴴ * (Δ * B)) * (Δ * B)ᴴ) * (Δ * B))
            * (Ring.inverse (Bᴴ * B) * Bᴴ) from by simp only [Matrix.mul_assoc]]
    rw [hY'DB, Matrix.mul_one, Matrix.mul_assoc]
  · rw [← hpDB, ← hpB]
    have h1 : E * ((Δ * B) * (Ring.inverse ((Δ * B)ᴴ * (Δ * B)) * (Δ * B)ᴴ))
        = B * (Ring.inverse ((Δ * B)ᴴ * (Δ * B)) * (Δ * B)ᴴ) := by
      rw [← Matrix.mul_assoc E (Δ * B)
            (Ring.inverse ((Δ * B)ᴴ * (Δ * B)) * (Δ * B)ᴴ),
        ← Matrix.mul_assoc E Δ B, hEΔ, Matrix.one_mul]
    rw [h1]
    rw [show (B * (Ring.inverse (Bᴴ * B) * Bᴴ))
          * (B * (Ring.inverse ((Δ * B)ᴴ * (Δ * B)) * (Δ * B)ᴴ))
        = B * (((Ring.inverse (Bᴴ * B) * Bᴴ) * B)
            * (Ring.inverse ((Δ * B)ᴴ * (Δ * B)) * (Δ * B)ᴴ)) from by
          simp only [Matrix.mul_assoc]]
    rw [hYB, Matrix.one_mul]

lemma graphB_inl {R : Type} [Ring R] {n : ℕ} (F : Matrix (Fin n) (Fin n) R) (a j : Fin n) :
    Work.KT.Fund.graphB R F (Sum.inl a) j = if a = j then 1 else 0 := rfl

lemma graphB_inr {R : Type} [Ring R] {n : ℕ} (F : Matrix (Fin n) (Fin n) R) (a j : Fin n) :
    Work.KT.Fund.graphB R F (Sum.inr a) j = F a j := rfl

lemma recipB_inl {R : Type} [Ring R] {n : ℕ} (G : Matrix (Fin n) (Fin n) R) (a j : Fin n) :
    Work.KT.Fund.recipB R G (Sum.inl a) j = G a j := rfl

lemma recipB_inr {R : Type} [Ring R] {n : ℕ} (G : Matrix (Fin n) (Fin n) R) (a j : Fin n) :
    Work.KT.Fund.recipB R G (Sum.inr a) j = if a = j then 1 else 0 := rfl

/-- The block diagonal matrix `diag (1, A)` times `diag (1, C)` is the identity when `A * C = 1`. -/
lemma fromBlocks_diag_mul {R : Type} [Ring R] {n : ℕ} (A C : Matrix (Fin n) (Fin n) R)
    (h : A * C = 1) :
    (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 A
        : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
      * (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 C
        : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) = 1 := by
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul, Matrix.mul_one]
  rw [h, Matrix.fromBlocks_one]

/-- `diag (1, A)` times the graph column `[[1],[F]]` is the graph column `[[1],[A F]]`. -/
lemma fromBlocks_one_graphB {R : Type} [Ring R] {n : ℕ} (A F : Matrix (Fin n) (Fin n) R) :
    (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 A
        : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) * Work.KT.Fund.graphB R F
      = Work.KT.Fund.graphB R (A * F) := by
  ext i j
  rcases i with a | a
  · rw [Matrix.mul_apply, Fintype.sum_sum_type]
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul,
      Finset.sum_const_zero, zero_add, add_zero, graphB_inl, Matrix.one_apply, ite_mul, one_mul,
      Fintype.sum_ite_eq]
  · rw [Matrix.mul_apply, Fintype.sum_sum_type]
    simp only [Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul,
      Finset.sum_const_zero, zero_add, add_zero, graphB_inl, graphB_inr, Matrix.mul_apply]

/-- `diag (1, A)` times the reciprocal column `[[G],[1]]`, right multiplied by `C` with
`A * C = 1`, is the reciprocal column `[[G C],[1]]`. -/
lemma fromBlocks_one_recipB {R : Type} [Ring R] {n : ℕ}
    (A G C : Matrix (Fin n) (Fin n) R) (hAC : A * C = 1) :
    (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 A
        : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) * Work.KT.Fund.recipB R G * C
      = Work.KT.Fund.recipB R (G * C) := by
  rw [Matrix.mul_assoc]
  ext i j
  rcases i with a | a
  · rw [Matrix.mul_apply, Fintype.sum_sum_type]
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul,
      Finset.sum_const_zero, zero_add, add_zero, Matrix.mul_apply, recipB_inl, Matrix.one_apply,
      ite_mul, one_mul, Fintype.sum_ite_eq]
  · rw [Matrix.mul_apply, Fintype.sum_sum_type]
    simp only [Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul,
      Finset.sum_const_zero, zero_add, add_zero, Matrix.mul_apply, recipB_inl, recipB_inr,
      ite_mul, one_mul, Fintype.sum_ite_eq]
    rw [← Matrix.mul_apply, hAC, Matrix.one_apply]

/-- The graph projection of `A * F` against the block unit `diag (1, A)`. -/
theorem graphProj_mul_diag {R : Type} [CommRing R] [StarRing R] {n : ℕ}
    (A C F : Matrix (Fin n) (Fin n) R) (hAC : A * C = 1) (hCA : C * A = 1)
    (hB : IsUnit ((Work.KT.Fund.graphB R F)ᴴ * Work.KT.Fund.graphB R F))
    (hΔB : IsUnit (((Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 A)
          * Work.KT.Fund.graphB R F)ᴴ
        * ((Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 A)
          * Work.KT.Fund.graphB R F))) :
    Work.KT.Fund.graphProj R (A * F)
        * ((Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 A)
          * Work.KT.Fund.graphProj R F)
      = (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 A)
        * Work.KT.Fund.graphProj R F := by
  have hblock := fromBlocks_one_graphB A F
  have hgen := orthProj_mul_unit_block (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 A)
    (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 C) (Work.KT.Fund.graphB R F)
    (fromBlocks_diag_mul C A hCA) (fromBlocks_diag_mul A C hAC) hB hΔB
  rw [hblock] at hgen
  simpa only [Work.KT.Fund.graphProj] using hgen.1

/-- The companion identity for the inverse block unit. -/
theorem graphProj_mul_diag_inv {R : Type} [CommRing R] [StarRing R] {n : ℕ}
    (A C F : Matrix (Fin n) (Fin n) R) (hAC : A * C = 1) (hCA : C * A = 1)
    (hB : IsUnit ((Work.KT.Fund.graphB R F)ᴴ * Work.KT.Fund.graphB R F))
    (hΔB : IsUnit (((Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 A)
          * Work.KT.Fund.graphB R F)ᴴ
        * ((Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 A)
          * Work.KT.Fund.graphB R F))) :
    Work.KT.Fund.graphProj R F
        * ((Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 C)
          * Work.KT.Fund.graphProj R (A * F))
      = (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 C)
        * Work.KT.Fund.graphProj R (A * F) := by
  have hblock := fromBlocks_one_graphB A F
  have hgen := orthProj_mul_unit_block (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 A)
    (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 C) (Work.KT.Fund.graphB R F)
    (fromBlocks_diag_mul C A hCA) (fromBlocks_diag_mul A C hAC) hB hΔB
  rw [hblock] at hgen
  simpa only [Work.KT.Fund.graphProj] using hgen.2

/-- The reciprocal-graph projection of `G * C` against the block unit `diag (1, A)`. -/
theorem recipProj_mul_diag {R : Type} [CommRing R] [StarRing R] {n : ℕ}
    (A C G : Matrix (Fin n) (Fin n) R) (hAC : A * C = 1) (hCA : C * A = 1) (hC : IsUnit C)
    (hB : IsUnit ((Work.KT.Fund.recipB R G)ᴴ * Work.KT.Fund.recipB R G))
    (hΔB : IsUnit (((Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 A)
          * Work.KT.Fund.recipB R G)ᴴ
        * ((Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 A)
          * Work.KT.Fund.recipB R G))) :
    Work.KT.Fund.recipProj R (G * C)
        * ((Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 A)
          * Work.KT.Fund.recipProj R G)
      = (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 A)
        * Work.KT.Fund.recipProj R G := by
  have hblock := fromBlocks_one_recipB A G C hAC
  have hQ : Work.KT.Fund.orthProj R
        ((Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 A) * Work.KT.Fund.recipB R G)
      = Work.KT.Fund.orthProj R (Work.KT.Fund.recipB R (G * C)) := by
    conv_rhs => rw [← hblock]
    exact (Work.KT.Fund.orthProj_mul_unit R
      ((Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 A) * Work.KT.Fund.recipB R G)
      C hC).symm
  have hgen := orthProj_mul_unit_block (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 A)
    (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 C) (Work.KT.Fund.recipB R G)
    (fromBlocks_diag_mul C A hCA) (fromBlocks_diag_mul A C hAC) hB hΔB
  rw [hQ] at hgen
  simpa only [Work.KT.Fund.recipProj] using hgen.1

/-- The companion identity for the inverse block unit, reciprocal-graph side. -/
theorem recipProj_mul_diag_inv {R : Type} [CommRing R] [StarRing R] {n : ℕ}
    (A C G : Matrix (Fin n) (Fin n) R) (hAC : A * C = 1) (hCA : C * A = 1) (hC : IsUnit C)
    (hB : IsUnit ((Work.KT.Fund.recipB R G)ᴴ * Work.KT.Fund.recipB R G))
    (hΔB : IsUnit (((Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 A)
          * Work.KT.Fund.recipB R G)ᴴ
        * ((Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 A)
          * Work.KT.Fund.recipB R G))) :
    Work.KT.Fund.recipProj R G
        * ((Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 C)
          * Work.KT.Fund.recipProj R (G * C))
      = (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 C)
        * Work.KT.Fund.recipProj R (G * C) := by
  have hblock := fromBlocks_one_recipB A G C hAC
  have hQ : Work.KT.Fund.orthProj R
        ((Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 A) * Work.KT.Fund.recipB R G)
      = Work.KT.Fund.orthProj R (Work.KT.Fund.recipB R (G * C)) := by
    conv_rhs => rw [← hblock]
    exact (Work.KT.Fund.orthProj_mul_unit R
      ((Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 A) * Work.KT.Fund.recipB R G)
      C hC).symm
  have hgen := orthProj_mul_unit_block (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 A)
    (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 C) (Work.KT.Fund.recipB R G)
    (fromBlocks_diag_mul C A hCA) (fromBlocks_diag_mul A C hAC) hB hΔB
  rw [hQ] at hgen
  simpa only [Work.KT.Fund.recipProj] using hgen.2

/-! ## The Murray–von Neumann equivalence of the two clutched idempotents -/

/-- **The Murray–von Neumann equivalence underlying `kappa_abs`.**  For lifts `F` of `w` and `Gw`
of `w⁻¹`, and `A`, `C` mutually inverse matrices over the disc (a gauge transformation that extends
over the disc), the clutched pair idempotent built from the modified lifts `A F`, `Gw C` is
Murray–von Neumann equivalent to the one built from `F`, `Gw`. -/
theorem mvN_pairIdem_abs {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] {n : ℕ}
    (A C F Gw : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ))
    (hAC : A * C = 1) (hCA : C * A = 1)
    (h : (Fund.graphProj C(X × Ball ℂ, ℂ) F).map ⇑(Fund.bdryRestrict X)
       = (Fund.recipProj C(X × Ball ℂ, ℂ) Gw).map ⇑(Fund.bdryRestrict X))
    (h' : (Fund.graphProj C(X × Ball ℂ, ℂ) (A * F)).map ⇑(Fund.bdryRestrict X)
       = (Fund.recipProj C(X × Ball ℂ, ℂ) (Gw * C)).map ⇑(Fund.bdryRestrict X)) :
    Work.KT.Mat.MvN
      (Fund.pairIdem X (Fund.graphProj C(X × Ball ℂ, ℂ) (A * F))
        (Fund.recipProj C(X × Ball ℂ, ℂ) (Gw * C)) h')
      (Fund.pairIdem X (Fund.graphProj C(X × Ball ℂ, ℂ) F)
        (Fund.recipProj C(X × Ball ℂ, ℂ) Gw) h) := by
  classical
  set P₁ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) C(X × Ball ℂ, ℂ) :=
    Fund.graphProj C(X × Ball ℂ, ℂ) (A * F) with hP₁
  set P₂ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) C(X × Ball ℂ, ℂ) :=
    Fund.graphProj C(X × Ball ℂ, ℂ) F with hP₂
  set Q₁ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) C(X × Ball ℂ, ℂ) :=
    Fund.recipProj C(X × Ball ℂ, ℂ) (Gw * C) with hQ₁
  set Q₂ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) C(X × Ball ℂ, ℂ) :=
    Fund.recipProj C(X × Ball ℂ, ℂ) Gw with hQ₂
  set Δ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) C(X × Ball ℂ, ℂ) :=
    Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) 0 0 A with hΔ
  set Δi : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) C(X × Ball ℂ, ℂ) :=
    Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) 0 0 C with hΔi
  have hΔΔi : Δ * Δi = 1 := by rw [hΔ, hΔi]; exact fromBlocks_diag_mul A C hAC
  have hΔiΔ : Δi * Δ = 1 := by rw [hΔ, hΔi]; exact fromBlocks_diag_mul C A hCA
  have hB₂ : IsUnit ((Fund.graphB C(X × Ball ℂ, ℂ) F)ᴴ * Fund.graphB C(X × Ball ℂ, ℂ) F) :=
    Fund.KC.isUnit_graphB_gram X F
  have hB₁ : IsUnit ((Fund.graphB C(X × Ball ℂ, ℂ) (A * F))ᴴ
      * Fund.graphB C(X × Ball ℂ, ℂ) (A * F)) := Fund.KC.isUnit_graphB_gram X (A * F)
  have hΔBgraph : IsUnit (((Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) 0 0 A)
        * Fund.graphB C(X × Ball ℂ, ℂ) F)ᴴ
      * ((Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) 0 0 A)
        * Fund.graphB C(X × Ball ℂ, ℂ) F)) := by
    rw [fromBlocks_one_graphB A F]
    exact hB₁
  have hB₂r : IsUnit ((Fund.recipB C(X × Ball ℂ, ℂ) Gw)ᴴ * Fund.recipB C(X × Ball ℂ, ℂ) Gw) :=
    Fund.KC.isUnit_recipB_gram X Gw
  have hAu : IsUnit A := ⟨⟨A, C, hAC, hCA⟩, rfl⟩
  have hCu : IsUnit C := ⟨⟨C, A, hCA, hAC⟩, rfl⟩
  have hΔBrecip : IsUnit (((Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) 0 0 A)
        * Fund.recipB C(X × Ball ℂ, ℂ) Gw)ᴴ
      * ((Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) 0 0 A)
        * Fund.recipB C(X × Ball ℂ, ℂ) Gw)) := by
    have hrep : (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) 0 0 A)
        * Fund.recipB C(X × Ball ℂ, ℂ) Gw
        = Fund.recipB C(X × Ball ℂ, ℂ) (Gw * C) * A := by
      calc (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) 0 0 A)
            * Fund.recipB C(X × Ball ℂ, ℂ) Gw
          = (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) 0 0 A)
              * Fund.recipB C(X × Ball ℂ, ℂ) Gw
              * (1 : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) := by rw [Matrix.mul_one]
        _ = (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) 0 0 A)
              * Fund.recipB C(X × Ball ℂ, ℂ) Gw * (C * A) := by rw [hCA]
        _ = ((Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) 0 0 A)
              * Fund.recipB C(X × Ball ℂ, ℂ) Gw * C) * A := by simp only [Matrix.mul_assoc]
        _ = Fund.recipB C(X × Ball ℂ, ℂ) (Gw * C) * A := by
              rw [fromBlocks_one_recipB A Gw C hAC]
    rw [hrep]
    exact Fund.KC.isUnit_conjTranspose_mul_mul _ _ _ (Fund.KC.isUnit_recipB_gram X (Gw * C))
      hAu
  have ha₁ : P₁ * (Δ * P₂) = Δ * P₂ := by
    rw [hP₁, hP₂, hΔ]
    exact graphProj_mul_diag A C F hAC hCA hB₂ hΔBgraph
  have ha₂ : Q₁ * (Δ * Q₂) = Δ * Q₂ := by
    rw [hQ₁, hQ₂, hΔ]
    exact recipProj_mul_diag A C Gw hAC hCA hCu hB₂r hΔBrecip
  have hb₁ : P₂ * (Δi * P₁) = Δi * P₁ := by
    rw [hP₁, hP₂, hΔi]
    exact graphProj_mul_diag_inv A C F hAC hCA hB₂ hΔBgraph
  have hb₂ : Q₂ * (Δi * Q₁) = Δi * Q₁ := by
    rw [hQ₁, hQ₂, hΔi]
    exact recipProj_mul_diag_inv A C Gw hAC hCA hCu hB₂r hΔBrecip
  have hP₁idem : P₁ * P₁ = P₁ := by rw [hP₁]; exact Fund.graphProj_isIdem X _
  have hP₂idem : P₂ * P₂ = P₂ := by rw [hP₂]; exact Fund.graphProj_isIdem X _
  have hQ₁idem : Q₁ * Q₁ = Q₁ := by rw [hQ₁]; exact Fund.recipProj_isIdem X _
  have hQ₂idem : Q₂ * Q₂ = Q₂ := by rw [hQ₂]; exact Fund.recipProj_isIdem X _
  have hagrA : (P₁ * (Δ * P₂)).map ⇑(Fund.bdryRestrict X)
      = (Q₁ * (Δ * Q₂)).map ⇑(Fund.bdryRestrict X) := by
    rw [ha₁, ha₂, Matrix.map_mul, Matrix.map_mul, h]
  have hagrB : (P₂ * (Δi * P₁)).map ⇑(Fund.bdryRestrict X)
      = (Q₂ * (Δi * Q₁)).map ⇑(Fund.bdryRestrict X) := by
    rw [hb₁, hb₂, Matrix.map_mul, Matrix.map_mul, h']
  have hAB₁ : (P₁ * (Δ * P₂)) * (P₂ * (Δi * P₁)) = P₁ := by
    rw [ha₁, Matrix.mul_assoc, ← Matrix.mul_assoc P₂ P₂ (Δi * P₁), hP₂idem, hb₁,
      ← Matrix.mul_assoc Δ Δi P₁, hΔΔi, Matrix.one_mul]
  have hBA₁ : (P₂ * (Δi * P₁)) * (P₁ * (Δ * P₂)) = P₂ := by
    rw [hb₁, Matrix.mul_assoc, ← Matrix.mul_assoc P₁ P₁ (Δ * P₂), hP₁idem, ha₁,
      ← Matrix.mul_assoc Δi Δ P₂, hΔiΔ, Matrix.one_mul]
  have hAB₂ : (Q₁ * (Δ * Q₂)) * (Q₂ * (Δi * Q₁)) = Q₁ := by
    rw [ha₂, Matrix.mul_assoc, ← Matrix.mul_assoc Q₂ Q₂ (Δi * Q₁), hQ₂idem, hb₂,
      ← Matrix.mul_assoc Δ Δi Q₁, hΔΔi, Matrix.one_mul]
  have hBA₂ : (Q₂ * (Δi * Q₁)) * (Q₁ * (Δ * Q₂)) = Q₂ := by
    rw [hb₂, Matrix.mul_assoc, ← Matrix.mul_assoc Q₁ Q₁ (Δ * Q₂), hQ₁idem, ha₂,
      ← Matrix.mul_assoc Δi Δ Q₂, hΔiΔ, Matrix.one_mul]
  refine ⟨Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Fund.KC.pairMatR X (P₂ * (Δi * P₁)) (Q₂ * (Δi * Q₁)) hagrB),
    Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Fund.KC.pairMatR X (P₁ * (Δ * P₂)) (Q₁ * (Δ * Q₂)) hagrA), ?_, ?_⟩
  · show Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Fund.KC.pairMatR X (P₁ * (Δ * P₂)) (Q₁ * (Δ * Q₂)) hagrA)
        * Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Fund.KC.pairMatR X (P₂ * (Δi * P₁)) (Q₂ * (Δi * Q₁)) hagrB)
      = (Fund.pairIdem X P₁ Q₁ h').2
    have hsum : (Fund.KC.pairMatR X (P₁ * (Δ * P₂)) (Q₁ * (Δ * Q₂)) hagrA)
        * (Fund.KC.pairMatR X (P₂ * (Δi * P₁)) (Q₂ * (Δi * Q₁)) hagrB)
        = Fund.pairMat X P₁ Q₁ h' := by
      apply Fund.mat_ext X
      · rw [Matrix.map_mul, Fund.KC.pairMatR_map_prF, Fund.KC.pairMatR_map_prF,
          Fund.pairMat_map_prF, hAB₁]
      · rw [Matrix.map_mul, Fund.KC.pairMatR_map_prS, Fund.KC.pairMatR_map_prS,
          Fund.pairMat_map_prS, hAB₂]
    rw [Work.KT.reindex_finSum_mul,
      show (Fund.pairIdem X P₁ Q₁ h').2
        = Matrix.reindex finSumFinEquiv finSumFinEquiv (Fund.pairMat X P₁ Q₁ h') from rfl]
    exact congrArg (Matrix.reindex finSumFinEquiv finSumFinEquiv) hsum
  · show Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Fund.KC.pairMatR X (P₂ * (Δi * P₁)) (Q₂ * (Δi * Q₁)) hagrB)
        * Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Fund.KC.pairMatR X (P₁ * (Δ * P₂)) (Q₁ * (Δ * Q₂)) hagrA)
      = (Fund.pairIdem X P₂ Q₂ h).2
    have hsum : (Fund.KC.pairMatR X (P₂ * (Δi * P₁)) (Q₂ * (Δi * Q₁)) hagrB)
        * (Fund.KC.pairMatR X (P₁ * (Δ * P₂)) (Q₁ * (Δ * Q₂)) hagrA)
        = Fund.pairMat X P₂ Q₂ h := by
      apply Fund.mat_ext X
      · rw [Matrix.map_mul, Fund.KC.pairMatR_map_prF, Fund.KC.pairMatR_map_prF,
          Fund.pairMat_map_prF, hBA₁]
      · rw [Matrix.map_mul, Fund.KC.pairMatR_map_prS, Fund.KC.pairMatR_map_prS,
          Fund.pairMat_map_prS, hBA₂]
    rw [Work.KT.reindex_finSum_mul,
      show (Fund.pairIdem X P₂ Q₂ h).2
        = Matrix.reindex finSumFinEquiv finSumFinEquiv (Fund.pairMat X P₂ Q₂ h) from rfl]
    exact congrArg (Matrix.reindex finSumFinEquiv finSumFinEquiv) hsum

/-! ## Absorption of a pulled-back unit -/

/-- **Absorption of a constant (in the circle variable) unit.** Multiplying a clutching function on
the left by the pull-back to `X × S¹` of a unit `g` of matrices over `C(X, ℂ)` does not change its
clutched class: the clutching function changes by a gauge transformation that extends over the
disc, so the glued bundle — and hence `κ` — is unchanged.

This is stated with the disc extensions `A`, `C` of `g`, `g⁻¹` as explicit data, to keep the
elaboration of the heavy `C(X × D, ℂ)`-valued terms out of the main proof. -/
lemma kappa_abs_aux (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (n : ℕ)
    (g : (Matrix (Fin n) (Fin n) C(X, ℂ))ˣ)
    (A C : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ))
    (hA : A = Fund.KC.gUp X (↑g))
    (hC : C = Fund.KC.gUp X (↑(g⁻¹) : Matrix (Fin n) (Fin n) C(X, ℂ)))
    (w u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    (hu : (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
      = Work.KT.Fund.pullMat X (g : Matrix (Fin n) (Fin n) C(X, ℂ)) *
          (w : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))) :
    Work.KT.Fund.kappa X n u = Work.KT.Fund.kappa X n w := by
  rw [Fund.kappa_val X n u, Fund.kappa_val X n w]
  apply congrArg (Fund.k0Glue X).symm
  set Fw : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ) := Fund.liftOf X (↑w) with hFw
  set Gw : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ) := Fund.liftOf X (↑(w⁻¹)) with hGw
  set Fu : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ) := Fund.liftOf X (↑u) with hFu
  set Gu : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ) := Fund.liftOf X (↑(u⁻¹)) with hGu
  have hFw_spec : Fw.map ⇑(Fund.bdryRestrict X)
      = (↑w : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) := by rw [hFw]; exact Fund.liftOf_spec X _
  have hGw_spec : Gw.map ⇑(Fund.bdryRestrict X)
      = (↑(w⁻¹) : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) := by
    rw [hGw]; exact Fund.liftOf_spec X _
  have hFu_spec : Fu.map ⇑(Fund.bdryRestrict X)
      = (↑u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) := by rw [hFu]; exact Fund.liftOf_spec X _
  have hGu_spec : Gu.map ⇑(Fund.bdryRestrict X)
      = (↑(u⁻¹) : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) := by
    rw [hGu]; exact Fund.liftOf_spec X _
  have hAC : A * C = 1 := by
    rw [hA, hC, ← Fund.KC.gUp_mul, Units.mul_inv g, Fund.KC.gUp_one]
  have hCA : C * A = 1 := by
    rw [hA, hC, ← Fund.KC.gUp_mul, Units.inv_mul g, Fund.KC.gUp_one]
  have hAbdry : A.map ⇑(Fund.bdryRestrict X) = Fund.pullMat X (↑g) := by
    rw [hA]; exact Fund.KC.gUp_bdry X (↑g : Matrix (Fin n) (Fin n) C(X, ℂ))
  have hCbdry : C.map ⇑(Fund.bdryRestrict X)
      = Fund.pullMat X (↑(g⁻¹) : Matrix (Fin n) (Fin n) C(X, ℂ)) := by
    rw [hC]; exact Fund.KC.gUp_bdry X (↑(g⁻¹) : Matrix (Fin n) (Fin n) C(X, ℂ))
  have hFn : (A * Fw).map ⇑(Fund.bdryRestrict X)
      = (↑u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) := by
    rw [Matrix.map_mul, hAbdry, hFw_spec]
    exact hu.symm
  have hPg : (↑(Units.map (Fund.KC.pullHomM X n) g) : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
      = Fund.pullMat X (↑g : Matrix (Fin n) (Fin n) C(X, ℂ)) := by
    rw [Units.coe_map, Fund.KC.pullMat_eq_pullHomM]
  have hPgu : Units.map (Fund.KC.pullHomM X n) g * w = u := by
    refine Units.ext ?_
    rw [Units.val_mul, hPg]
    exact hu.symm
  have hinv : (↑(u⁻¹) : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
      = (↑(w⁻¹) : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
        * Fund.pullMat X (↑(g⁻¹) : Matrix (Fin n) (Fin n) C(X, ℂ)) := by
    rw [← hPgu, _root_.mul_inv_rev]
    rw [show (Units.map (Fund.KC.pullHomM X n) g)⁻¹
          = Units.map (Fund.KC.pullHomM X n) (g⁻¹) from
      (map_inv (Units.map (Fund.KC.pullHomM X n)) g).symm]
    rw [Units.val_mul, Units.coe_map, ← Fund.KC.pullMat_eq_pullHomM]
  have hGn : (Gw * C).map ⇑(Fund.bdryRestrict X)
      = (↑(u⁻¹) : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) := by
    rw [Matrix.map_mul, hGw_spec, hCbdry]
    exact hinv.symm
  have hAglue : (Fund.graphProj C(X × Ball ℂ, ℂ) (A * Fw)).map ⇑(Fund.bdryRestrict X)
      = (Fund.recipProj C(X × Ball ℂ, ℂ) (Gw * C)).map ⇑(Fund.bdryRestrict X) :=
    Fund.clutch_agree X n u (A * Fw) (Gw * C) hFn hGn
  have hBglue : (Fund.graphProj C(X × Ball ℂ, ℂ) Fw).map ⇑(Fund.bdryRestrict X)
      = (Fund.recipProj C(X × Ball ℂ, ℂ) Gw).map ⇑(Fund.bdryRestrict X) :=
    Fund.clutch_agree X n w Fw Gw hFw_spec hGw_spec
  have hstep := Work.KT.Fund.kappa_indep X n u Fu (A * Fw) Gu (Gw * C)
    hFu_spec hFn hGu_spec hGn
  have hmv := mvN_pairIdem_abs A C Fw Gw hAC hCA hBglue hAglue
  have hcls : Work.KT.cls (Fund.clutchIdem X n u (A * Fw) (Gw * C) hFn hGn)
      = Work.KT.cls (Fund.clutchIdem X n w Fw Gw hFw_spec hGw_spec) := by
    rw [Fund.clutchIdem_eq_pairIdem X u _ _ hFn hGn hAglue,
      Fund.clutchIdem_eq_pairIdem X w _ _ hFw_spec hGw_spec hBglue]
    exact Work.KT.cls_eq_of_mvn (Fund.pairIdem_isIdem X _ _ hAglue)
      (Fund.pairIdem_isIdem X _ _ hBglue) hmv
  exact hstep.trans hcls

/-- **Absorption of a constant (in the circle variable) unit.** Multiplying a clutching function on
the left by the pull-back to `X × S¹` of a unit `g` of matrices over `C(X, ℂ)` does not change its
clutched class: the clutching function changes by a gauge transformation that extends over the
disc, so the glued bundle — and hence `κ` — is unchanged. -/
theorem kappa_abs (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (n : ℕ)
    (g : (Matrix (Fin n) (Fin n) C(X, ℂ))ˣ)
    (w u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    (hu : (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
      = Work.KT.Fund.pullMat X (g : Matrix (Fin n) (Fin n) C(X, ℂ)) *
          (w : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))) :
    Work.KT.Fund.kappa X n u = Work.KT.Fund.kappa X n w :=
  kappa_abs_aux X n g (Fund.KC.gUp X (↑g))
    (Fund.KC.gUp X (↑(g⁻¹) : Matrix (Fin n) (Fin n) C(X, ℂ))) rfl rfl w u hu

end

end Work.KT.EG
