import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.poSheet
import Submission.Work.Mostow.poCenter
import Submission.Work.Mostow.poBdAlg
import Submission.Work.Mostow.poBdReg
import Submission.Work.Mostow.poActCont
import Submission.Work.Mostow.poContDescent

/-!
# Area T1: the action of `PO(n,1)` on hyperbolic space

Assembly of `POActionProp n` from the matrix algebra in `poAux` and the delegated lemmas
`poSheet` (the sheet lemma and its corollaries), `poCenter`, `poBdAlg`, `poBdReg`,
`poActCont` and `poContDescent`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open Matrix

noncomputable section

variable {n : ℕ}

/-! ### The assembly -/


lemma tpart_single (i : Fin n) : tpart (EuclideanSpace.single i (1:ℝ) : E n) = √2 := by
  rw [tpart, EuclideanSpace.norm_single]; norm_num

lemma hlift_single_sub (i : Fin n) :
    hlift (EuclideanSpace.single i (1:ℝ) : E n) - (√2 : ℝ) • hlift (0 : E n) =
      Pi.single (Sum.inl i) (1:ℝ) := by
  funext a
  rcases a with j | k
  · have h0 : hlift (0 : E n) (Sum.inl j) = 0 := by
      rw [hlift_zero, Pi.single_apply]; simp
    rw [Pi.sub_apply, Pi.smul_apply, hlift_inl, h0, smul_eq_mul, mul_zero, sub_zero,
      EuclideanSpace.single_apply, Pi.single_apply]
    by_cases h : j = i <;> simp [h]
  · obtain rfl : k = 0 := Subsingleton.elim _ _
    have h0 : hlift (0 : E n) (Sum.inr 0) = 1 := by
      rw [hlift_zero, Pi.single_apply]; simp
    rw [Pi.sub_apply, Pi.smul_apply, hlift_inr, h0, tpart_single, smul_eq_mul, mul_one,
      sub_self, Pi.single_apply]
    simp

lemma mat_inj :
    Function.Injective (mat : O1 n → Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) := by
  intro A B h
  have h' : MatrixSum.ofMatrix.symm (A : MatrixSum (Fin n) (Fin 1) ℝ) =
      MatrixSum.ofMatrix.symm (B : MatrixSum (Fin n) (Fin 1) ℝ) := h
  exact Subtype.ext (MatrixSum.ofMatrix.symm.injective h')

/-- If a matrix acts as a scalar on every hyperboloid lift, it is that scalar times `1`. -/
lemma mat_eq_smul_one_of (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) (c : ℝ)
    (h : ∀ u : E n, M *ᵥ hlift u = c • hlift u) : M = c • 1 := by
  have hcol : ∀ b : Fin n ⊕ Fin 1, M *ᵥ Pi.single b (1:ℝ) = c • Pi.single b (1:ℝ) := by
    intro b
    rcases b with i | k
    · have h1 := h (EuclideanSpace.single i (1:ℝ))
      have h0 := h (0 : E n)
      have hsub : M *ᵥ (hlift (EuclideanSpace.single i (1:ℝ)) - (√2:ℝ) • hlift (0:E n)) =
          c • (hlift (EuclideanSpace.single i (1:ℝ)) - (√2:ℝ) • hlift (0:E n)) := by
        rw [Matrix.mulVec_sub, Matrix.mulVec_smul, h1, h0, smul_sub, smul_smul, smul_smul,
          mul_comm (√2) c]
      rwa [hlift_single_sub] at hsub
    · obtain rfl : k = 0 := Subsingleton.elim _ _
      simpa [hlift_zero, Matrix.mulVec_single_one] using h (0 : E n)
  ext a b
  have h2 := congrFun (hcol b) a
  rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply] at h2
  rw [h2]
  simp [Pi.single_apply, Matrix.one_apply]

lemma tsign_eq_one_or (A : O1 n) : tsign A = 1 ∨ tsign A = -1 := by
  have h := tsign_sq A
  have h2 : (tsign A - 1) * (tsign A + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h2 with h3 | h3
  · left; linarith
  · right; linarith

/-! ### the assembly -/

theorem poAction (n : ℕ) (hn : 3 ≤ n) : POActionProp n := by
  have hn2 : 2 ≤ n := by omega
  obtain ⟨hsheet, htsignmul, hactOmul, hactOone, hactOneg⟩ := poSheet n
  obtain ⟨hbdmem, hbdneg, hbdmul, hbdone⟩ := poBdAlg n
  obtain ⟨hbdcont, hbdmeas⟩ := poBdReg n
  obtain ⟨hactcont, _htsigncont⟩ := poActCont n
  have hcen : ∀ A : O1 n, A ∈ Subgroup.center (O1 n) ↔ A = 1 ∨ A = -1 := poCenter n hn2
  -- central elements do not change `actO` or `bdO`
  have hactOcen : ∀ (B c : O1 n), c ∈ Subgroup.center (O1 n) → actO (B * c) = actO B := by
    intro B c hc
    funext u
    rcases (hcen c).1 hc with rfl | rfl
    · rw [mul_one]
    · rw [O1_mul_neg_one]; exact hactOneg B u
  have hbdOcen : ∀ (B c : O1 n), c ∈ Subgroup.center (O1 n) → bdO (B * c) = bdO B := by
    intro B c hc
    funext ξ
    rcases (hcen c).1 hc with rfl | rfl
    · rw [mul_one]
    · rw [O1_mul_neg_one]; exact hbdneg B ξ
  have hcen_of_mk : ∀ A : O1 n,
      (rep (A : PO n 1))⁻¹ * A ∈ Subgroup.center (O1 n) := by
    intro A
    exact QuotientGroup.eq.1 (QuotientGroup.out_eq' (A : PO n 1))
  have hactO_of_mk : ∀ A : O1 n, actO (rep (A : PO n 1)) = actO A := by
    intro A
    have hc := hcen_of_mk A
    have hA : A = rep (A : PO n 1) * ((rep (A : PO n 1))⁻¹ * A) := by
      rw [← mul_assoc, mul_inv_cancel, one_mul]
    have h2 : actO A = actO (rep (A : PO n 1)) := by
      conv_lhs => rw [hA]
      exact hactOcen _ _ hc
    exact h2.symm
  have hbdO_of_mk : ∀ A : O1 n, bdO (rep (A : PO n 1)) = bdO A := by
    intro A
    have hc := hcen_of_mk A
    have hA : A = rep (A : PO n 1) * ((rep (A : PO n 1))⁻¹ * A) := by
      rw [← mul_assoc, mul_inv_cancel, one_mul]
    have h2 : bdO A = bdO (rep (A : PO n 1)) := by
      conv_lhs => rw [hA]
      exact hbdOcen _ _ hc
    exact h2.symm
  -- clause 2
  have hsmul : ∀ (A : O1 n) (u : E n), (A : PO n 1) • u = actO A u := by
    intro A u
    show actO (rep (A : PO n 1)) u = actO A u
    rw [hactO_of_mk]
  -- clause 3
  have hbd_eq : ∀ (A : O1 n) (ξ : E n), ξ ∈ Sph n → bd (A : PO n 1) ξ = bdO A ξ := by
    intro A ξ _
    show bdO (rep (A : PO n 1)) ξ = bdO A ξ
    rw [hbdO_of_mk]
  -- clause 4
  have hone : ∀ u : E n, (1 : PO n 1) • u = u := by
    intro u
    rw [show (1 : PO n 1) = ((1 : O1 n) : PO n 1) from
          (QuotientGroup.mk_one (Subgroup.center (O1 n))).symm, hsmul, hactOone]
  -- clause 5
  have hmul : ∀ (g h : PO n 1) (u : E n), (g * h) • u = g • (h • u) := by
    intro g h u
    obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨B, rfl⟩ := QuotientGroup.mk_surjective h
    rw [← QuotientGroup.mk_mul, hsmul, hactOmul, ← hsmul, ← hsmul]
  -- clause 6
  have hfaith : ∀ g : PO n 1, (∀ u : E n, g • u = u) → g = 1 := by
    intro g hg
    have hfix : ∀ u : E n, actO (rep g) u = u := by
      intro u
      have hrep : ((rep g : O1 n) : PO n 1) = g := QuotientGroup.out_eq' g
      rw [← hsmul (rep g) u, hrep, hg u]
    have hlin : ∀ u : E n, mat (rep g) *ᵥ hlift u = tsign (rep g) • hlift u := by
      intro u
      have h1 : hlift u = tsign (rep g) • (mat (rep g) *ᵥ hlift u) := by
        conv_lhs => rw [← hfix u]
        exact hsheet (rep g) u
      have h2 := congrArg (fun v => tsign (rep g) • v) h1
      rw [smul_smul, tsign_sq, one_smul] at h2
      exact h2.symm
    have hmat : mat (rep g) = tsign (rep g) • 1 := mat_eq_smul_one_of _ _ hlin
    have hmat' := hmat
    have hA : rep g = 1 ∨ rep g = -1 := by
      rcases tsign_eq_one_or (rep g) with ht | ht
      · left
        rw [ht, one_smul] at hmat'
        exact mat_inj (by rw [hmat', mat_one])
      · right
        rw [ht] at hmat'
        simp only [neg_smul, one_smul] at hmat'
        exact mat_inj (by rw [hmat', mat_neg, mat_one])
    have hc : rep g ∈ Subgroup.center (O1 n) := (hcen (rep g)).2 hA
    rw [← QuotientGroup.out_eq' g]
    exact (QuotientGroup.eq_one_iff (rep g)).2 hc
  refine ⟨hcen, hsmul, hbd_eq, hone, hmul, hfaith,
    poContDescent n hactcont hsmul, ?_, ?_, ?_, ?_, ?_⟩
  · intro g ξ hξ; exact hbdmem (rep g) ξ hξ
  · intro ξ hξ
    have hrep1 : rep (1 : PO n 1) ∈ Subgroup.center (O1 n) :=
      (QuotientGroup.eq_one_iff (rep (1 : PO n 1))).1 (QuotientGroup.out_eq' 1)
    show bdO (rep (1 : PO n 1)) ξ = ξ
    have h1 : bdO (rep (1 : PO n 1)) = bdO 1 := by
      have hh := hbdOcen (1 : O1 n) (rep (1 : PO n 1)) hrep1
      rwa [one_mul] at hh
    rw [h1, hbdone]
  · intro g h ξ hξ
    obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨B, rfl⟩ := QuotientGroup.mk_surjective h
    rw [← QuotientGroup.mk_mul (Subgroup.center (O1 n)) A B]
    show bdO (rep ((A * B : O1 n) : PO n 1)) ξ = bdO (rep (A : PO n 1)) (bdO (rep (B : PO n 1)) ξ)
    rw [hbdO_of_mk, hbdO_of_mk, hbdO_of_mk]
    exact hbdmul A B ξ hξ
  · intro g; exact hbdcont (rep g)
  · intro g; exact hbdmeas (rep g)

end

end Work.Mostow
