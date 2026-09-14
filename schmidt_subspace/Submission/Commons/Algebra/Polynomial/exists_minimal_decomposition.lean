import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

open Polynomial

namespace Commons.Algebra.Polynomial

open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K] {n : ℕ}

/-- `φ ⊗ ψ` as an element of `R[X]`, `R = K[x₀,…,x_{n-1}]`. -/
private def decompTensor (φ : MvPolynomial (Fin n) K) (ψ : Polynomial K) :
    Polynomial (MvPolynomial (Fin n) K) :=
  Polynomial.C φ * ψ.map (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)

private lemma tensor_add_left (φ₁ φ₂ : MvPolynomial (Fin n) K) (ψ : Polynomial K) :
    decompTensor (φ₁ + φ₂) ψ = decompTensor φ₁ ψ + decompTensor φ₂ ψ := by
  simp [decompTensor, Polynomial.C_add, add_mul]

private lemma tensor_add_right (φ : MvPolynomial (Fin n) K) (ψ₁ ψ₂ : Polynomial K) :
    decompTensor φ (ψ₁ + ψ₂) = decompTensor φ ψ₁ + decompTensor φ ψ₂ := by
  simp [decompTensor, mul_add]

private lemma tensor_smul_left (a : K) (φ : MvPolynomial (Fin n) K) (ψ : Polynomial K) :
    decompTensor (a • φ) ψ = a • decompTensor φ ψ := by
  have h : Polynomial.C (a • φ) = a • Polynomial.C φ :=
    map_smul (Polynomial.CAlgHom (R := K) (A := MvPolynomial (Fin n) K)) a φ
  simp only [decompTensor, h]
  rw [Algebra.smul_mul_assoc]

private lemma tensor_smul_right (a : K) (φ : MvPolynomial (Fin n) K) (ψ : Polynomial K) :
    decompTensor φ (a • ψ) = a • decompTensor φ ψ := by
  rw [decompTensor, decompTensor, Polynomial.map_smul]
  rw [Algebra.mul_smul_comm]
  have h : (MvPolynomial.C a : MvPolynomial (Fin n) K) =
      (algebraMap K (MvPolynomial (Fin n) K)) a := rfl
  rw [h]
  exact algebraMap_smul (A := MvPolynomial (Fin n) K) a _

private lemma tensor_sum_left {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin n) K)
    (ψ : Polynomial K) :
    decompTensor (∑ j ∈ s, f j) ψ = ∑ j ∈ s, decompTensor (f j) ψ := by
  simp only [decompTensor, map_sum, Finset.sum_mul]

private lemma tensor_sum_right {ι : Type*} (s : Finset ι) (φ : MvPolynomial (Fin n) K)
    (g : ι → Polynomial K) :
    decompTensor φ (∑ j ∈ s, g j) = ∑ j ∈ s, decompTensor φ (g j) := by
  simp only [decompTensor, Polynomial.map_sum, Finset.mul_sum]

private lemma tensor_sum_smul_left {ι : Type*} (s : Finset ι) (a : ι → K)
    (f : ι → MvPolynomial (Fin n) K) (ψ : Polynomial K) :
    decompTensor (∑ j ∈ s, a j • f j) ψ = ∑ j ∈ s, a j • decompTensor (f j) ψ := by
  rw [tensor_sum_left]
  exact Finset.sum_congr rfl (fun j _ => tensor_smul_left (a j) (f j) ψ)

private lemma tensor_sum_smul_right {ι : Type*} (s : Finset ι) (φ : MvPolynomial (Fin n) K)
    (a : ι → K) (g : ι → Polynomial K) :
    decompTensor φ (∑ j ∈ s, a j • g j) = ∑ j ∈ s, a j • decompTensor φ (g j) := by
  rw [tensor_sum_right]
  exact Finset.sum_congr rfl (fun j _ => tensor_smul_right (a j) φ (g j))

section Absorb

variable {ι : Type*} [DecidableEq ι]

private lemma linear_relation_of_sum_eq_zero {M : Type*} [AddCommGroup M] [Module K M]
    (S : Finset ι) {j0 : ι} (hj0 : j0 ∈ S)
    (φ : ι → M) (c : ι → K) (hc : c j0 ≠ 0)
    (hrel : ∑ j ∈ S, c j • φ j = 0) :
    φ j0 = ∑ j ∈ S.erase j0, (-(c j0)⁻¹ * c j) • φ j := by
  have hsplit : (∑ j ∈ S.erase j0, c j • φ j) + c j0 • φ j0 = 0 := by
    rw [Finset.sum_erase_add S (fun j => c j • φ j) hj0]; exact hrel
  have h1 : c j0 • φ j0 = - (∑ j ∈ S.erase j0, c j • φ j) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact hsplit
  have h2 : (c j0)⁻¹ • (∑ j ∈ S.erase j0, c j • φ j)
      = ∑ j ∈ S.erase j0, ((c j0)⁻¹ * c j) • φ j := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [smul_smul])
  calc φ j0 = (c j0)⁻¹ • (c j0 • φ j0) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    _ = (c j0)⁻¹ • (- (∑ j ∈ S.erase j0, c j • φ j)) := by rw [h1]
    _ = - ((c j0)⁻¹ • (∑ j ∈ S.erase j0, c j • φ j)) := by rw [smul_neg]
    _ = - (∑ j ∈ S.erase j0, ((c j0)⁻¹ * c j) • φ j) := by rw [h2]
    _ = ∑ j ∈ S.erase j0, - (((c j0)⁻¹ * c j) • φ j) := by rw [← Finset.sum_neg_distrib]
    _ = ∑ j ∈ S.erase j0, (-(c j0)⁻¹ * c j) • φ j := by
          exact Finset.sum_congr rfl (fun j _ => by rw [neg_mul, neg_smul])

/-- Absorb a linear dependence among the left factors. -/
private lemma sum_absorb_left (S : Finset ι) {j0 : ι} (hj0 : j0 ∈ S)
    (φ : ι → MvPolynomial (Fin n) K) (ψ : ι → Polynomial K) (c : ι → K)
    (hrel : ∑ j ∈ S, c j • φ j = 0) (hc : c j0 ≠ 0) :
    (∑ j ∈ S, decompTensor (φ j) (ψ j)) =
      ∑ j ∈ S.erase j0, decompTensor (φ j) (ψ j + (-(c j0)⁻¹ * c j) • ψ j0) := by
  have hphi := linear_relation_of_sum_eq_zero S hj0 φ c hc hrel
  calc ∑ j ∈ S, decompTensor (φ j) (ψ j)
      = (∑ j ∈ S.erase j0, decompTensor (φ j) (ψ j)) + decompTensor (φ j0) (ψ j0) := by
          rw [Finset.sum_erase_add S (fun j => decompTensor (φ j) (ψ j)) hj0]
    _ = (∑ j ∈ S.erase j0, decompTensor (φ j) (ψ j))
          + ∑ j ∈ S.erase j0, (-(c j0)⁻¹ * c j) • decompTensor (φ j) (ψ j0) := by
          rw [hphi, tensor_sum_smul_left]
    _ = ∑ j ∈ S.erase j0,
          (decompTensor (φ j) (ψ j) + (-(c j0)⁻¹ * c j) • decompTensor (φ j) (ψ j0)) := by
          rw [Finset.sum_add_distrib]
    _ = ∑ j ∈ S.erase j0, decompTensor (φ j) (ψ j + (-(c j0)⁻¹ * c j) • ψ j0) := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [tensor_add_right, tensor_smul_right]

/-- Absorb a linear dependence among the right factors. -/
private lemma sum_absorb_right (S : Finset ι) {j0 : ι} (hj0 : j0 ∈ S)
    (φ : ι → MvPolynomial (Fin n) K) (ψ : ι → Polynomial K) (c : ι → K)
    (hrel : ∑ j ∈ S, c j • ψ j = 0) (hc : c j0 ≠ 0) :
    (∑ j ∈ S, decompTensor (φ j) (ψ j)) =
      ∑ j ∈ S.erase j0, decompTensor (φ j + (-(c j0)⁻¹ * c j) • φ j0) (ψ j) := by
  have hpsi := linear_relation_of_sum_eq_zero S hj0 ψ c hc hrel
  calc ∑ j ∈ S, decompTensor (φ j) (ψ j)
      = (∑ j ∈ S.erase j0, decompTensor (φ j) (ψ j)) + decompTensor (φ j0) (ψ j0) := by
          rw [Finset.sum_erase_add S (fun j => decompTensor (φ j) (ψ j)) hj0]
    _ = (∑ j ∈ S.erase j0, decompTensor (φ j) (ψ j))
          + ∑ j ∈ S.erase j0, (-(c j0)⁻¹ * c j) • decompTensor (φ j0) (ψ j) := by
          rw [hpsi, tensor_sum_smul_right]
    _ = ∑ j ∈ S.erase j0,
          (decompTensor (φ j) (ψ j) + (-(c j0)⁻¹ * c j) • decompTensor (φ j0) (ψ j)) := by
          rw [Finset.sum_add_distrib]
    _ = ∑ j ∈ S.erase j0, decompTensor (φ j + (-(c j0)⁻¹ * c j) • φ j0) (ψ j) := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [tensor_add_left, tensor_smul_left]

end Absorb

/-- A family that is independent "on a finset" is independent when indexed by that finset. -/
private lemma linearIndependent_coe_of {ι : Type*} [DecidableEq ι] {M : Type*}
    [AddCommGroup M] [Module K M] {S : Finset ι} {φ : ι → M}
    (h : ∀ c : ι → K, (∑ j ∈ S, c j • φ j = 0) → ∀ j ∈ S, c j = 0) :
    LinearIndependent K (fun i : ↥S => φ i.val) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  set c' : ι → K := fun j => if hj : j ∈ S then c ⟨j, hj⟩ else 0 with hc'_def
  have h1 : (∑ x : ↥S, c x • φ x.val) = ∑ z ∈ S.attach, c z • φ z.val := by
    rw [Finset.attach_eq_univ]
  have h2 : (∑ z ∈ S.attach, c z • φ z.val) = ∑ j ∈ S, c' j • φ j := by
    rw [← Finset.sum_attach S (fun j => c' j • φ j)]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [hc'_def]
    simp
  have hrel : ∑ j ∈ S, c' j • φ j = 0 := by rw [← h2, ← h1]; exact hc
  have hzero := h c' hrel i.val i.property
  rw [hc'_def] at hzero
  simpa using hzero


/-- **Minimal decomposition of a polynomial in a distinguished variable.**

Every `f ∈ R[X]` with `R = K[x_0, …, x_{n-1}]` can be written as
`f = ∑_{j < k} C (φ j) * (ψ j).map MvPolynomial.C` with both families `φ` and `ψ` linearly
independent over `K`; a shortest such decomposition has length `k ≤ f.natDegree + 1`. -/
theorem exists_minimal_decomposition {K : Type*} [Field K] {n : ℕ}
    (f : Polynomial (MvPolynomial (Fin n) K)) :
    ∃ (k : ℕ) (φ : Fin k → MvPolynomial (Fin n) K) (ψ : Fin k → Polynomial K),
      f = ∑ j : Fin k,
        Polynomial.C (φ j) * (ψ j).map (MvPolynomial.C : K →+* MvPolynomial (Fin n) K) ∧
      LinearIndependent K φ ∧ LinearIndependent K ψ ∧
      (f ≠ 0 → k ≤ f.natDegree + 1) := by
  classical
  let N : ℕ := f.natDegree + 1
  have htriv : f = ∑ j ∈ Finset.range N, decompTensor (f.coeff j) (Polynomial.X ^ j) := by
    have h1 : (∑ j ∈ Finset.range N, decompTensor (f.coeff j) (Polynomial.X ^ j))
        = ∑ j ∈ Finset.range (f.natDegree + 1),
            Polynomial.C (f.coeff j) * Polynomial.X ^ j := by
      simp only [N, decompTensor, Polynomial.map_pow, Polynomial.map_X]
    rw [h1, ← Polynomial.as_sum_range_C_mul_X_pow f]
  let P : ℕ → Prop := fun m =>
    ∃ (S : Finset ℕ) (φ : ℕ → MvPolynomial (Fin n) K) (ψ : ℕ → Polynomial K),
      S.card = m ∧ f = ∑ j ∈ S, decompTensor (φ j) (ψ j)
  have hP : ∃ m, P m :=
    ⟨N, Finset.range N, f.coeff, (fun j => Polynomial.X ^ j), Finset.card_range N, htriv⟩
  obtain ⟨S0, φ0, ψ0, hcard0, hdecomp0⟩ := Nat.find_spec hP
  -- minimality forces both families to be independent
  have hphi_ind : ∀ c : ℕ → K, (∑ j ∈ S0, c j • φ0 j = 0) → ∀ j ∈ S0, c j = 0 := by
    intro c hc
    by_contra hcon
    push Not at hcon
    obtain ⟨j0, hj0, hcj0⟩ := hcon
    have hnew : f = ∑ j ∈ S0.erase j0,
        decompTensor (φ0 j) (ψ0 j + (-(c j0)⁻¹ * c j) • ψ0 j0) := by
      rw [hdecomp0, sum_absorb_left S0 hj0 φ0 ψ0 c hc hcj0]
    have hlt : (S0.erase j0).card < Nat.find hP := by
      rw [Finset.card_erase_of_mem hj0, ← hcard0]
      exact Nat.sub_lt (Finset.card_pos.mpr ⟨j0, hj0⟩) Nat.one_pos
    exact (Nat.find_min hP hlt)
      ⟨S0.erase j0, φ0, (fun j => ψ0 j + (-(c j0)⁻¹ * c j) • ψ0 j0), rfl, hnew⟩
  have hpsi_ind : ∀ c : ℕ → K, (∑ j ∈ S0, c j • ψ0 j = 0) → ∀ j ∈ S0, c j = 0 := by
    intro c hc
    by_contra hcon
    push Not at hcon
    obtain ⟨j0, hj0, hcj0⟩ := hcon
    have hnew : f = ∑ j ∈ S0.erase j0,
        decompTensor (φ0 j + (-(c j0)⁻¹ * c j) • φ0 j0) (ψ0 j) := by
      rw [hdecomp0, sum_absorb_right S0 hj0 φ0 ψ0 c hc hcj0]
    have hlt : (S0.erase j0).card < Nat.find hP := by
      rw [Finset.card_erase_of_mem hj0, ← hcard0]
      exact Nat.sub_lt (Finset.card_pos.mpr ⟨j0, hj0⟩) Nat.one_pos
    exact (Nat.find_min hP hlt)
      ⟨S0.erase j0, (fun j => φ0 j + (-(c j0)⁻¹ * c j) • φ0 j0), ψ0, rfl, hnew⟩
  refine ⟨S0.card, fun j => φ0 (S0.equivFin.symm j).val,
      fun j => ψ0 (S0.equivFin.symm j).val, ?_, ?_, ?_, ?_⟩
  · have hsum : (∑ j : Fin S0.card,
          decompTensor (φ0 (S0.equivFin.symm j).val) (ψ0 (S0.equivFin.symm j).val))
        = ∑ j ∈ S0, decompTensor (φ0 j) (ψ0 j) := by
      rw [← Finset.sum_attach S0 (fun j => decompTensor (φ0 j) (ψ0 j))]
      rw [Finset.attach_eq_univ]
      rw [Equiv.sum_comp S0.equivFin.symm
        (fun i : ↥S0 => decompTensor (φ0 i.val) (ψ0 i.val))]
    rw [hdecomp0]
    exact hsum.symm
  · have hS : LinearIndependent K (fun i : ↥S0 => φ0 i.val) :=
      linearIndependent_coe_of hphi_ind
    exact hS.comp S0.equivFin.symm S0.equivFin.symm.injective
  · have hS : LinearIndependent K (fun i : ↥S0 => ψ0 i.val) :=
      linearIndependent_coe_of hpsi_ind
    exact hS.comp S0.equivFin.symm S0.equivFin.symm.injective
  · intro _
    exact le_trans (le_of_eq hcard0)
      (Nat.find_min' hP ⟨Finset.range N, f.coeff, (fun j => Polynomial.X ^ j),
        Finset.card_range N, htriv⟩)

end

end Commons.Algebra.Polynomial