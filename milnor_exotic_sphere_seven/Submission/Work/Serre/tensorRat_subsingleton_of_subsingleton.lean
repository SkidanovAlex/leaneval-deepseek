import Mathlib
import Submission.Work.Kunneth.Chapter
import Submission.Work.Serre.rowKernelTorsion
import Submission.Work.Serre.tpDApplyComp
import Submission.Work.Serre.cyclesTorsionOfHomologyTorsion
import Submission.Work.Serre.homologySubsingletonOfCycleTorsion
import Submission.Work.StemsB.TorsionBridge
import Submission.Work.RatHurewicz.torsion_of_subsingleton_ratHomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Serre

noncomputable section

section basic

variable {C K : ChainComplex (ModuleCat ℤ) ℕ}

/-- `tpD` applied twice vanishes, in the spelling of the Koszul differential. -/
theorem tpD_comp_tpD' (C K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ)
    (z : Work.Kunneth.tpX C K (n + 2)) :
    Work.Kunneth.tpD C K n (Work.Kunneth.tpD C K (n + 1) z) = 0 := by
  have hd1 : ((Work.Kunneth.tpC C K).d (n + 1) n).hom = Work.Kunneth.tpD C K n := by
    rw [Work.Kunneth.tpC_d]
    rfl
  have hd2 : ((Work.Kunneth.tpC C K).d (n + 2) (n + 1)).hom = Work.Kunneth.tpD C K (n + 1) := by
    rw [Work.Kunneth.tpC_d]
    rfl
  have h := HomologicalComplex.d_comp_d (Work.Kunneth.tpC C K) (n + 2) (n + 1) n
  have h1 : ((Work.Kunneth.tpC C K).d (n + 2) (n + 1) ≫
      (Work.Kunneth.tpC C K).d (n + 1) n).hom z = 0 := by
    rw [h, ModuleCat.hom_zero]
    rfl
  rw [ModuleCat.hom_comp] at h1
  rw [hd1, hd2] at h1
  change (Work.Kunneth.tpD C K n) ((Work.Kunneth.tpD C K (n + 1)) z) = 0 at h1
  exact h1

/-- `TensorProduct.map f 0` applied to any element is `0`. -/
theorem tensor_map_zero' {M N P : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup N]
    [Module ℤ N] [AddCommGroup P] [Module ℤ P] (f : M →ₗ[ℤ] P) (u : M ⊗[ℤ] N) :
    (TensorProduct.map f (0 : N →ₗ[ℤ] N)) u = 0 := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a n => simp
  | add x y hx hy => simp [hx, hy]

/-- If `(-1)^k • y = 0` then `y = 0`. -/
theorem eq_zero_of_neg_one_pow_smul {M : Type*} [AddCommGroup M] [Module ℤ M] (k : ℕ) {y : M}
    (h : (-1 : ℤ) ^ k • y = 0) : y = 0 := by
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · rw [show (-1 : ℤ) ^ k = 1 from by rw [hj]; exact Even.neg_one_pow ⟨j, rfl⟩, one_smul] at h
    exact h
  · rw [show (-1 : ℤ) ^ k = -1 from by rw [hj]; exact Odd.neg_one_pow ⟨j, rfl⟩] at h
    simpa using h

theorem nsmul_ds_apply {n : ℕ} (m : ℕ) (x : Work.Kunneth.tpX C K n) (pq : Work.Kunneth.tpIdx n) :
    (m • x) pq = m • (x pq) := DFinsupp.nsmul_apply m x pq

theorem neg_one_pow_mul_self (k : ℕ) : (-1 : ℤ) ^ k * (-1 : ℤ) ^ k = 1 := by
  rw [← pow_add]
  exact Even.neg_one_pow ⟨k, rfl⟩

end basic

/-- **The single-column step.** -/
theorem colStep (C K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (pq : Work.Kunneth.tpIdx (n + 1))
    (hF : Module.Free ℤ ↥(C.X pq.1.1))
    (hcyc : ∀ z : ↥(K.X pq.1.2), (K.d pq.1.2 (pq.1.2 - 1)).hom z = 0 →
      ∃ m : ℕ, 0 < m ∧ ∃ y : ↥(K.X (pq.1.2 + 1)), (K.d (pq.1.2 + 1) pq.1.2).hom y = m • z)
    (u : Work.Kunneth.tpSummand C K pq.1.1 pq.1.2)
    (hu : TensorProduct.map (LinearMap.id) ((K.d pq.1.2 (pq.1.2 - 1)).hom) u = 0) :
    ∃ M : ℕ, 0 < M ∧ ∃ z : Work.Kunneth.tpX C K (n + 2),
      (Work.Kunneth.tpD C K (n + 1) z) pq = M • u ∧
      (∀ rs : Work.Kunneth.tpIdx (n + 1), pq.1.1 < rs.1.1 →
        (Work.Kunneth.tpD C K (n + 1) z) rs = 0) := by
  obtain ⟨M, hMpos, w, hw⟩ := rowKernelTorsion C K pq.1.1 pq.1.2 hF hcyc u hu
  refine ⟨M, hMpos,
    (-1 : ℤ) ^ pq.1.1 • Work.Kunneth.tpLof C K (n + 2) ⟨(pq.1.1, pq.1.2 + 1), by omega⟩ w,
    ?_, ?_⟩
  · rw [map_zsmul, zsmul_ds_apply]
    rw [tpD_tpLof_snd C K (n + 1) pq w]
    rw [smul_smul, neg_one_pow_mul_self, one_smul, hw]
  · intro rs hrs
    rw [map_zsmul, zsmul_ds_apply]
    rw [tpD_tpLof_eq_zero C K (n + 1) rs ⟨(pq.1.1, pq.1.2 + 1), by omega⟩ ?_ ?_ w, zsmul_zero]
    · intro hcon
      have h' : pq.1.1 = rs.1.1 := congrArg (fun t : Work.Kunneth.tpIdx (n + 2) => t.1.1) hcon
      omega
    · intro hcon
      have h' : pq.1.1 = rs.1.1 + 1 :=
        congrArg (fun t : Work.Kunneth.tpIdx (n + 2) => t.1.1) hcon
      omega

/-- **Degree zero**: every element of `C_0 ⊗ K_0` has a positive multiple that is a boundary in
the tensor product complex. -/
theorem degreeZero (C K : ChainComplex (ModuleCat ℤ) ℕ)
    (hF : Module.Free ℤ ↥(C.X 0))
    (hcyc : ∀ z : ↥(K.X 0), (K.d 0 (0 - 1)).hom z = 0 →
      ∃ m : ℕ, 0 < m ∧ ∃ y : ↥(K.X 1), (K.d 1 0).hom y = m • z)
    (x : Work.Kunneth.tpX C K 0) :
    ∃ M : ℕ, 0 < M ∧ ∃ z : Work.Kunneth.tpX C K 1, Work.Kunneth.tpD C K 0 z = M • x := by
  have hidx : (0 : ℕ) + 0 = 0 := rfl
  have hfst : (⟨(0, 0), hidx⟩ : Work.Kunneth.tpIdx 0).1.1 = 0 := rfl
  have hsnd : (⟨(0, 0), hidx⟩ : Work.Kunneth.tpIdx 0).1.2 = 0 := rfl
  have hsingle : ∀ j : Work.Kunneth.tpIdx 0, j ≠ ⟨(0, 0), hidx⟩ → x j = 0 := by
    intro j hj
    have h1 : (j.1.1 : ℕ) = 0 := by have := j.2; omega
    have h2 : (j.1.2 : ℕ) = 0 := by have := j.2; omega
    exact absurd (Subtype.ext (Prod.ext h1 h2)) hj
  have hd0 : (K.d 0 (0 - 1)) = 0 := HomologicalComplex.shape K 0 0 (by simp [ComplexShape.down])
  have hu : TensorProduct.map (LinearMap.id) ((K.d 0 (0 - 1)).hom) (x ⟨(0, 0), hidx⟩) = 0 := by
    rw [hd0, ModuleCat.hom_zero]
    exact tensor_map_zero' _ _
  obtain ⟨M, hMpos, w, hw⟩ := rowKernelTorsion C K 0 0 hF hcyc (x ⟨(0, 0), hidx⟩) hu
  refine ⟨M, hMpos, Work.Kunneth.tpLof C K 1 ⟨(0, 1), by omega⟩ w, ?_⟩
  apply DirectSum.ext
  intro rs
  have hrs : rs = ⟨(0, 0), hidx⟩ := Subtype.ext (Prod.ext (by omega) (by omega))
  subst hrs
  rw [tpD_tpLof_snd C K 0 ⟨(0, 0), hidx⟩ w]
  rw [pow_zero, one_smul]
  rw [hw]
  rw [nsmul_ds_apply]

/-- **The filtration induction.** -/
theorem mainAux (C K : ChainComplex (ModuleCat ℤ) ℕ) (N : ℕ)
    (hC : ∀ i, Module.Free ℤ ↥(C.X i))
    (hcyc : ∀ q, q ≤ N → ∀ z : ↥(K.X q), (K.d q (q - 1)).hom z = 0 →
      ∃ m : ℕ, 0 < m ∧ ∃ y : ↥(K.X (q + 1)), (K.d (q + 1) q).hom y = m • z) :
    ∀ s (n : ℕ), n + 1 ≤ N → ∀ x : Work.Kunneth.tpX C K (n + 1),
      Work.Kunneth.tpD C K n x = 0 →
      (∀ pq : Work.Kunneth.tpIdx (n + 1), s < pq.1.1 → x pq = 0) →
      ∃ m : ℕ, 0 < m ∧ ∃ y : Work.Kunneth.tpX C K (n + 2),
        Work.Kunneth.tpD C K (n + 1) y = m • x := by
  intro s
  induction s with
  | zero =>
    intro n hn x hx hs
    have hidx : (0 : ℕ) + (n + 1) = n + 1 := Nat.zero_add (n + 1)
    have hidxn : (0 : ℕ) + n = n := Nat.zero_add n
    have hfst : (⟨(0, n + 1), hidx⟩ : Work.Kunneth.tpIdx (n + 1)).1.1 = 0 := rfl
    have hsnd : (⟨(0, n + 1), hidx⟩ : Work.Kunneth.tpIdx (n + 1)).1.2 = n + 1 := rfl
    have hsingle : ∀ j : Work.Kunneth.tpIdx (n + 1), j ≠ ⟨(0, n + 1), hidx⟩ → x j = 0 := by
      intro j hj
      apply hs
      by_contra hcon
      push_neg at hcon
      exact hj (Subtype.ext (Prod.ext (by omega) (by omega)))
    have hu : TensorProduct.map (LinearMap.id) ((K.d (n + 1) n).hom)
        (x ⟨(0, n + 1), hidx⟩) = 0 := by
      have hcomp := tpDApplyComp C K n ⟨(0, n), hidxn⟩ x
      rw [hx] at hcomp
      simp only [DFinsupp.zero_apply] at hcomp
      have h2 : x ⟨(0 + 1, n), by omega⟩ = 0 := by
        apply hsingle
        intro hcon
        have h' : (0 : ℕ) + 1 = 0 :=
          congrArg (fun t : Work.Kunneth.tpIdx (n + 1) => t.1.1) hcon
        omega
      rw [h2, map_zero, add_zero] at hcomp
      exact eq_zero_of_neg_one_pow_smul 0 hcomp.symm
    obtain ⟨M, hMpos, z, hz1, hz2⟩ := colStep C K n ⟨(0, n + 1), hidx⟩ (hC 0)
      (fun y hy => hcyc (n + 1) hn y hy) (x ⟨(0, n + 1), hidx⟩) hu
    refine ⟨M, hMpos, z, ?_⟩
    apply DirectSum.ext
    intro rs
    by_cases hrs : rs = ⟨(0, n + 1), hidx⟩
    · subst hrs
      rw [hz1, nsmul_ds_apply]
    · have h0 : (⟨(0, n + 1), hidx⟩ : Work.Kunneth.tpIdx (n + 1)).1.1 < rs.1.1 := by
        rw [hfst]
        by_contra hc
        push_neg at hc
        exact hrs (Subtype.ext (Prod.ext (by omega) (by omega)))
      rw [hz2 rs h0, nsmul_ds_apply, hsingle rs hrs, nsmul_zero]
  | succ s ih =>
    intro n hn x hx hs
    by_cases hle : s + 1 ≤ n
    · obtain ⟨m, rfl⟩ : ∃ m, n = s + m + 1 := ⟨n - s - 1, by omega⟩
      have htop : (s + 1) + (m + 1) = (s + m + 1) + 1 := by omega
      have hsndtop : (⟨(s + 1, m + 1), htop⟩ : Work.Kunneth.tpIdx ((s + m + 1) + 1)).1.2
          = m + 1 := rfl
      have hcyc_u : TensorProduct.map (LinearMap.id) ((K.d (m + 1) m).hom)
          (x ⟨(s + 1, m + 1), htop⟩) = 0 := by
        have hcomp := tpDApplyComp C K (s + m + 1) ⟨(s + 1, m), by omega⟩ x
        rw [hx] at hcomp
        simp only [DFinsupp.zero_apply] at hcomp
        have h2 : x ⟨(s + 2, m), by omega⟩ = 0 := by
          apply hs
          show s + 1 < s + 2
          omega
        rw [h2, map_zero, add_zero] at hcomp
        exact eq_zero_of_neg_one_pow_smul (s + 1) hcomp.symm
      obtain ⟨M, hMpos, z, hz1, hz2⟩ := colStep C K (s + m + 1) ⟨(s + 1, m + 1), htop⟩
        (hC (s + 1)) (fun y hy => hcyc (m + 1) (by omega) y hy) (x ⟨(s + 1, m + 1), htop⟩)
        hcyc_u
      have hcycU' : Work.Kunneth.tpD C K (s + m + 1)
          (M • x - Work.Kunneth.tpD C K ((s + m + 1) + 1) z) = 0 := by
        rw [map_sub, map_nsmul, hx, nsmul_zero, tpD_comp_tpD', sub_zero]
      have hsupp : ∀ pq : Work.Kunneth.tpIdx ((s + m + 1) + 1), s < pq.1.1 →
          (M • x - Work.Kunneth.tpD C K ((s + m + 1) + 1) z) pq = 0 := by
        intro pq hpq
        rw [DirectSum.sub_apply, nsmul_ds_apply]
        have hle' : s + 1 ≤ pq.1.1 := hpq
        rcases lt_or_eq_of_le hle' with hlt | heq
        · rw [hz2 pq hlt, hs pq hlt, nsmul_zero, sub_zero]
        · obtain rfl : pq = ⟨(s + 1, m + 1), htop⟩ :=
            Subtype.ext (Prod.ext heq.symm (by omega))
          rw [hz1, sub_self]
      obtain ⟨m', hm'pos, y, hy⟩ := ih (s + m + 1) (by omega) _ hcycU' hsupp
      refine ⟨m' * M, Nat.mul_pos hm'pos hMpos, y + m' • z, ?_⟩
      rw [map_add, hy, map_nsmul]
      rw [nsmul_sub, sub_add_cancel, ← mul_nsmul, Nat.mul_comm]
    · push_neg at hle
      by_cases heq : n = s
      · subst heq
        have hidxtop : (n + 1) + 0 = n + 1 := Nat.add_zero (n + 1)
        have hsndtop : (⟨(n + 1, 0), hidxtop⟩ : Work.Kunneth.tpIdx (n + 1)).1.2 = 0 := rfl
        have hd : (K.d 0 (0 - 1)) = 0 := HomologicalComplex.shape K 0 0 (by simp [ComplexShape.down])
        have hcyc_u : TensorProduct.map (LinearMap.id) ((K.d 0 (0 - 1)).hom)
            (x ⟨(n + 1, 0), hidxtop⟩) = 0 := by
          rw [hd, ModuleCat.hom_zero]
          exact tensor_map_zero' _ _
        obtain ⟨M, hMpos, z, hz1, hz2⟩ := colStep C K n ⟨(n + 1, 0), hidxtop⟩ (hC (n + 1))
          (fun y hy => hcyc 0 (by omega) y hy) (x ⟨(n + 1, 0), hidxtop⟩) hcyc_u
        have hcycU' : Work.Kunneth.tpD C K n
            (M • x - Work.Kunneth.tpD C K (n + 1) z) = 0 := by
          rw [map_sub, map_nsmul, hx, nsmul_zero, tpD_comp_tpD', sub_zero]
        have hsupp : ∀ pq : Work.Kunneth.tpIdx (n + 1), n < pq.1.1 →
            (M • x - Work.Kunneth.tpD C K (n + 1) z) pq = 0 := by
          intro pq hpq
          rw [DirectSum.sub_apply, nsmul_ds_apply]
          have hle' : n + 1 ≤ pq.1.1 := hpq
          rcases lt_or_eq_of_le hle' with hlt | heq'
          · rw [hz2 pq hlt, hs pq hlt, nsmul_zero, sub_zero]
          · obtain rfl : pq = ⟨(n + 1, 0), hidxtop⟩ := Subtype.ext (Prod.ext heq'.symm (by omega))
            rw [hz1, sub_self]
        obtain ⟨m', hm'pos, y, hy⟩ := ih n hn _ hcycU' hsupp
        refine ⟨m' * M, Nat.mul_pos hm'pos hMpos, y + m' • z, ?_⟩
        rw [map_add, hy, map_nsmul]
        rw [nsmul_sub, sub_add_cancel, ← mul_nsmul, Nat.mul_comm]
      · exact ih n hn x hx (fun pq hpq => by exfalso; have := pq.2; omega)

/-- **The acyclicity lemma of the Künneth spectral sequence.** -/
theorem tensorRat_subsingleton_of_subsingleton (C K : ChainComplex (ModuleCat ℤ) ℕ) (N : ℕ)
    (hC : ∀ i, Module.Free ℤ ↥(C.X i))
    (hK : ∀ j, j ≤ N → Subsingleton (TensorProduct ℤ ↥((K.homology j)) ℚ)) :
    ∀ j, j ≤ N → Subsingleton (TensorProduct ℤ ↥((Work.Kunneth.tpC C K).homology j) ℚ) := by
  intro j hj
  have hcyc : ∀ q, q ≤ N → ∀ z : ↥(K.X q), (K.d q (q - 1)).hom z = 0 →
      ∃ m : ℕ, 0 < m ∧ ∃ y : ↥(K.X (q + 1)), (K.d (q + 1) q).hom y = m • z := by
    intro q hq
    exact cyclesTorsionOfHomologyTorsion K q
      (fun a => Work.RatHurewicz.exists_nat_smul_eq_zero_of_subsingleton_tensorRat_module _
        (hK q hq) a)
  apply homologySubsingletonOfCycleTorsion
  intro z
  rcases j with _ | n
  · obtain ⟨M, hMpos, w, hw⟩ :=
      degreeZero C K (hC 0) (hcyc 0 (by omega)) (z : ↥((Work.Kunneth.tpC C K).X 0))
    refine ⟨M, hMpos, w, ?_⟩
    rw [show ((Work.Kunneth.tpC C K).d 1 0).hom = Work.Kunneth.tpD C K 0 from by
      rw [Work.Kunneth.tpC_d]
      rfl]
    exact hw
  · have hx : Work.Kunneth.tpD C K n
        (show Work.Kunneth.tpX C K (n + 1) from (z : ↥((Work.Kunneth.tpC C K).X (n + 1)))) = 0 := by
      have h2 : ((Work.Kunneth.tpC C K).d (n + 1) n).hom
          (z : ↥((Work.Kunneth.tpC C K).X (n + 1))) = 0 := z.2
      rw [show ((Work.Kunneth.tpC C K).d (n + 1) n).hom = Work.Kunneth.tpD C K n from by
        rw [Work.Kunneth.tpC_d]
        rfl] at h2
      exact h2
    obtain ⟨M, hMpos, y, hy⟩ := mainAux C K N hC hcyc (n + 1) n hj
      (show Work.Kunneth.tpX C K (n + 1) from (z : ↥((Work.Kunneth.tpC C K).X (n + 1))))
      hx (fun pq hpq => by exfalso; have := pq.2; omega)
    refine ⟨M, hMpos, y, ?_⟩
    rw [show ((Work.Kunneth.tpC C K).d (n + 2) (n + 1)).hom = Work.Kunneth.tpD C K (n + 1) from by
      rw [Work.Kunneth.tpC_d]
      rfl]
    exact hy

end

end Work.Serre
