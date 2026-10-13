/-
Area DSCOH — a self-contained copy of the monomial basis theorem for the chart localizations.

This is a copy of `Work.DSCOH.locAt_monomial_basis` (`Submission/Work/DSCOH/locAt_monomial_basis.lean`)
whose two `sorry`-carrying helper imports are replaced by the proved lemmas `lmbA_bAt_X_smul` and
`lmbA_bAt_resAt` of `Submission/Work/DSCOH/LocBasisAux.lean`.  It carries no `sorry`.
-/
import Mathlib
import Submission.Work.DSCOH.Basic
import Submission.Work.DSCOH.Shift
import Submission.Work.DSCOH.ShiftToolkit
import Submission.Work.DSCOH.LocBasisDefs
import Submission.Work.DSCOH.LocBasisAux
import Submission.Work.DSCOH.lmb_isRegular_subS
import Submission.Work.DSCOH.lmb_subS_eq_xpow
import Submission.Work.DSCOH.lmb_mk_den_eq_zero
import Submission.Work.DSCOH.lmb_xpow_linearIndependent
import Submission.Work.DSCOH.lmb_support_degree
open MvPolynomial

namespace Work.DSCOH

variable {A : Type*} [CommRing A] {n : ℕ}

/-! ## The exponent shift by a variable -/

/-- The index vector `β` with the `i`-th exponent increased by one. -/
noncomputable def shiftIdx (S : Finset (Fin n)) (i : Fin n) (β : Idx S) : Idx S :=
  ⟨fun j => if j = i then β.1 j + 1 else β.1 j, by
    intro j hj
    by_cases h : j = i
    · subst h
      simp only [ite_true]
      linarith [β.2 j hj]
    · simp only [h, ite_false]
      exact β.2 j hj⟩

lemma shiftIdx_val (S : Finset (Fin n)) (i : Fin n) (β : Idx S) :
    (shiftIdx S i β).1 = fun j => if j = i then β.1 j + 1 else β.1 j := rfl

lemma bloc_congr {S : Finset (Fin n)} {β β' : Idx S} (h : β.1 = β'.1) :
    bloc (A := A) (n := n) S β = bloc (A := A) (n := n) S β' := by
  rw [Subtype.ext h]

/-! ## The linear map `Phi` from the free module on `Idx S` to `locAt S` -/

/-- The `A`-linear map sending the standard basis vector `β` to the monomial `bloc S β`. -/
noncomputable def Phi (S : Finset (Fin n)) :
    (Idx S →₀ A) →ₗ[A] locAt (A := A) (M := Poly A n) S :=
  Finsupp.linearCombination A (fun β : Idx S => bloc (A := A) (n := n) S β)

lemma Phi_apply (S : Finset (Fin n)) (c : Idx S →₀ A) :
    Phi (A := A) (n := n) S c = c.sum (fun β a => a • bloc (A := A) (n := n) S β) := by
  rw [Phi, Finsupp.linearCombination_apply]

lemma Phi_single (S : Finset (Fin n)) (β : Idx S) (a : A) :
    Phi (A := A) (n := n) S (Finsupp.single β a) = a • bloc (A := A) (n := n) S β := by
  rw [Phi_apply, Finsupp.sum_single_index (by simp)]

/-! ## Exponent sums -/

lemma eIdx_injective {S : Finset (Fin n)} {k : ℕ} {β β' : Fin n → ℤ} (h : Adm S k β)
    (h' : Adm S k β') (he : eIdx S k β = eIdx S k β') : β = β' := by
  funext i
  have h1 := h.cast_eIdx i
  have h2 := h'.cast_eIdx i
  have h3 : eIdx S k β i = eIdx S k β' i := by rw [he]
  rw [h3] at h1
  linarith

lemma sum_ite_mem_card (S : Finset (Fin n)) (k : ℕ) :
    (∑ i : Fin n, (if i ∈ S then (k : ℤ) else 0)) = (k : ℤ) * S.card := by
  have hS : (∑ i : Fin n, (if i ∈ S then (k : ℤ) else 0)) = ∑ i ∈ S, (k : ℤ) := by
    rw [← Finset.sum_subset (Finset.subset_univ S)
      (f := fun i => if i ∈ S then (k : ℤ) else 0)
      (fun x _ hx => by rw [ite_eq_right (by simpa using hx)])]
    exact Finset.sum_congr rfl (fun i hi => by rw [ite_eq_left hi])
  rw [hS, Finset.sum_const, nsmul_eq_mul, mul_comm]

lemma sum_cast_eIdx {S : Finset (Fin n)} {k : ℕ} {β : Fin n → ℤ} (h : Adm S k β) :
    ((∑ i, eIdx S k β i : ℕ) : ℤ) = (∑ i, β i) + (k : ℤ) * S.card := by
  rw [Nat.cast_sum, Finset.sum_congr rfl (fun i _ => h.cast_eIdx i), Finset.sum_add_distrib,
    sum_ite_mem_card]

/-- The degree of the numerator of `bAt S β k`. -/
lemma sum_eIdx_eq {S : Finset (Fin n)} {k : ℕ} {β : Fin n → ℤ} {d : ℕ} (h : Adm S k β)
    (hd : (∑ i, β i) = -(d : ℤ)) : (∑ i, eIdx S k β i) = k * S.card - d := by
  have h1 := sum_cast_eIdx h
  have hle : d ≤ k * S.card := by
    have h4 : (0 : ℤ) ≤ ((∑ i, eIdx S k β i : ℕ) : ℤ) := Int.natCast_nonneg _
    rw [h1, hd] at h4
    have : (d : ℤ) ≤ ((k * S.card : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast this
  apply Nat.cast_injective (R := ℤ)
  rw [h1, hd, Nat.cast_sub hle]
  push_cast
  ring

lemma xpow_eIdx_mem_shift {S : Finset (Fin n)} {k : ℕ} {β : Fin n → ℤ} {d : ℕ}
    (h : Adm S k β) (hd : (∑ i, β i) = -(d : ℤ)) :
    xpow (A := A) (eIdx S k β) ∈ shift (A := A) (n := n) d (k * S.card) := by
  have hsum := sum_eIdx_eq h hd
  have hle : d ≤ k * S.card := by
    have h1 := sum_cast_eIdx h
    have h4 : (0 : ℤ) ≤ ((∑ i, eIdx S k β i : ℕ) : ℤ) := Int.natCast_nonneg _
    rw [h1, hd] at h4
    have : (d : ℤ) ≤ ((k * S.card : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast this
  rw [shift_of_le hle, ← hsum]
  exact xpow_mem_homSub (A := A) (n := n) _

/-! ## `bloc` lies in the degree-zero part -/

lemma bloc_mem_degZero (S : Finset (Fin n)) (d : ℕ) (β : Idx S)
    (hβ : (∑ i, β.1 i) = -(d : ℤ)) :
    bloc (A := A) (n := n) S β ∈
      degZero (A := A) (M := Poly A n) (shift (A := A) (n := n) d) S := by
  have hmem := xpow_eIdx_mem_shift (A := A) (n := n) (d := d) (Adm.KIdx β.2) hβ
  have h := divPow_toLoc_mem (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d)
    S (KIdx S β.1) hmem
  simpa only [bloc, bAt] using h

/-! ## Linearity of `mk` in its numerator -/

lemma mk_add (S : Finset (Fin n)) (m₁ m₂ : Poly A n) (s : subS (A := A) S) :
    LocalizedModule.mk (m₁ + m₂) s = LocalizedModule.mk m₁ s + LocalizedModule.mk m₂ s := by
  rw [LocalizedModule.mk_add_mk, ← smul_add]
  exact (LocalizedModule.mk_cancel_common_left s s (m₁ + m₂)).symm

lemma mk_smul (S : Finset (Fin n)) (a : A) (m : Poly A n) (s : subS (A := A) S) :
    LocalizedModule.mk (a • m) s = a • LocalizedModule.mk m s := by
  rw [LocalizedModule.smul'_mk]

lemma mk_finset_sum (S : Finset (Fin n)) {ι : Type*} (t : Finset ι) (f : ι → Poly A n)
    (s : subS (A := A) S) :
    LocalizedModule.mk (∑ i ∈ t, f i) s = ∑ i ∈ t, LocalizedModule.mk (f i) s := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, mk_add, ih]

/-! ## Expansion of a polynomial into monomials -/

/-- The `Finsupp` exponent vector of a monomial exponent function. -/
noncomputable abbrev toFs (α : Fin n → ℕ) : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm α

lemma monomial_eq_smul_xpow (v : Fin n →₀ ℕ) (a : A) :
    (MvPolynomial.monomial v) a = a • xpow (A := A) (n := n) (fun i => v i) := by
  have h1 : (MvPolynomial.monomial v) a = MvPolynomial.C a * (MvPolynomial.monomial v) (1 : A) := by
    rw [MvPolynomial.C_mul_monomial, mul_one]
  rw [h1, MvPolynomial.C_mul', mvpoly_monomial_eq_xpow]

/-- A polynomial is the sum of its monomials, written with `xpow`. -/
lemma as_sum_smul (m : Poly A n) :
    m = ∑ v ∈ m.support, (m.coeff v) • xpow (A := A) (n := n) (fun i => v i) := by
  conv_lhs => rw [MvPolynomial.as_sum m]
  exact Finset.sum_congr rfl (fun v _ => monomial_eq_smul_xpow v (m.coeff v))

lemma xpow_eq_monomial_toFs (α : Fin n → ℕ) :
    xpow (A := A) (n := n) α = (MvPolynomial.monomial (toFs α)) (1 : A) := by
  have h : (fun i => (toFs α) i) = α := by
    funext i
    exact congrFun (Equiv.apply_symm_apply Finsupp.equivFunOnFinite α) i
  rw [← h]
  exact (mvpoly_monomial_eq_xpow (A := A) (n := n) (toFs α)).symm

lemma lcoeff_xpow (v : Fin n →₀ ℕ) (α : Fin n → ℕ) :
    MvPolynomial.lcoeff A v (xpow (A := A) (n := n) α) = if toFs α = v then 1 else 0 := by
  rw [xpow_eq_monomial_toFs, MvPolynomial.lcoeff_apply, MvPolynomial.coeff_monomial]

/-- Distinct (admissible) monomials with coefficients summing to zero have zero coefficients. -/
lemma xpow_sum_eq_zero {S : Finset (Fin n)} {k : ℕ} {c : Idx S →₀ A}
    (hadm : ∀ β ∈ c.support, Adm S k β.1)
    (h : ∑ β ∈ c.support, (c β) • xpow (A := A) (n := n) (eIdx S k β.1) = 0) : c = 0 := by
  classical
  refine Finsupp.ext (fun β₀ => ?_)
  by_cases hβ₀ : β₀ ∈ c.support
  · have h0 : ∑ β ∈ c.support,
        (c β) * (if toFs (eIdx S k β.1) = toFs (eIdx S k β₀.1) then 1 else 0) = 0 := by
      have := congrArg (MvPolynomial.lcoeff A (toFs (eIdx S k β₀.1))) h
      simpa only [map_sum, map_smul, lcoeff_xpow, smul_eq_mul, map_zero] using this
    have hterm : ∀ b ∈ c.support, b ≠ β₀ →
        (c b) * (if toFs (eIdx S k b.1) = toFs (eIdx S k β₀.1) then 1 else 0) = 0 := by
      intro b hb hbne
      have hne : toFs (eIdx S k b.1) ≠ toFs (eIdx S k β₀.1) := by
        intro h2
        have h3 : eIdx S k b.1 = eIdx S k β₀.1 := by
          have := congrArg Finsupp.equivFunOnFinite h2
          simpa [toFs] using this
        exact hbne (Subtype.ext (eIdx_injective (hadm b hb) (hadm β₀ hβ₀) h3))
      rw [ite_eq_right hne, mul_zero]
    rw [Finset.sum_eq_single β₀ hterm (fun hnot => absurd hβ₀ hnot)] at h0
    simpa using h0
  · exact Finsupp.notMem_support_iff.mp hβ₀

/-! ## Surjectivity of `Phi` -/

/-- Every element of a chart localization is an explicit fraction `m / s`. -/
lemma exists_mk (S : Finset (Fin n)) (y : locAt (A := A) (M := Poly A n) S) :
    ∃ (m : Poly A n) (s : subS (A := A) S), y = LocalizedModule.mk m s := by
  obtain ⟨⟨m, s⟩, hx⟩ := IsLocalizedModule.surj (subS (A := A) S)
    (LocalizedModule.mkLinearMap (subS (A := A) S) (Poly A n)) y
  refine ⟨m, s, ?_⟩
  have h1 : LocalizedModule.divBy s (s • y) = y := by
    have h := LocalizedModule.divBy_mul_by s y
    rwa [Module.algebraMap_end_apply] at h
  rw [← h1, hx, LocalizedModule.mkLinearMap_apply, LocalizedModule.divBy_apply,
    LocalizedModule.liftOn_mk, one_mul]

/-- The element of the free module on `Idx S` whose image under `Phi` is `m / X_S^k`. -/
noncomputable def cOf (S : Finset (Fin n)) (k : ℕ) (m : Poly A n) : Idx S →₀ A :=
  ∑ v ∈ m.support, (m.coeff v) • Finsupp.single (subIdx S k (fun i => v i)) 1

lemma Phi_cOf (S : Finset (Fin n)) (k : ℕ) (m : Poly A n) :
    Phi (A := A) (n := n) S (cOf S k m) = LocalizedModule.mk m (den (A := A) S k) := by
  have h1 : Phi (A := A) (n := n) S (cOf S k m)
      = ∑ v ∈ m.support, (m.coeff v) •
          bloc (A := A) (n := n) S (subIdx S k (fun i => v i)) := by
    rw [cOf, map_sum]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [map_smul, Phi_single, one_smul]
  have h2 : (∑ v ∈ m.support, (m.coeff v) •
        bloc (A := A) (n := n) S (subIdx S k (fun i => v i)))
      = ∑ v ∈ m.support, (m.coeff v) •
          LocalizedModule.mk (xpow (A := A) (n := n) (fun i => v i)) (den (A := A) S k) :=
    Finset.sum_congr rfl (fun v _ => by rw [bloc_subIdx])
  rw [h1, h2,
    show (∑ v ∈ m.support, (m.coeff v) •
        LocalizedModule.mk (xpow (A := A) (n := n) (fun i => v i)) (den (A := A) S k))
      = ∑ v ∈ m.support, LocalizedModule.mk
          ((m.coeff v) • xpow (A := A) (n := n) (fun i => v i)) (den (A := A) S k) from
      Finset.sum_congr rfl (fun v _ =>
        (mk_smul (A := A) (n := n) S (m.coeff v) _ (den (A := A) S k)).symm),
    ← mk_finset_sum, ← as_sum_smul m]

lemma Phi_surjective (S : Finset (Fin n)) :
    Function.Surjective (Phi (A := A) (n := n) S) := by
  intro y
  obtain ⟨m, s, hs⟩ := exists_mk (A := A) (n := n) S y
  obtain ⟨e, he, hse⟩ := lmb_subS_eq_xpow (A := A) (n := n) S s
  set k : ℕ := ∑ i ∈ S, e i with hk
  have hkle : ∀ i ∈ S, e i ≤ k := fun i hi => by
    rw [hk]
    exact Finset.single_le_sum (f := e) (fun j _ => Nat.zero_le _) hi
  have hxe : xpow (A := A) e = ∏ i ∈ S, (MvPolynomial.X i : Poly A n) ^ (e i) := by
    rw [xpow]
    exact (Finset.prod_subset (Finset.subset_univ S)
      (f := fun i => (MvPolynomial.X i : Poly A n) ^ (e i))
      (fun x _ hx => by rw [he x hx, pow_zero])).symm
  have hprod : (∏ i ∈ S, (MvPolynomial.X i : Poly A n) ^ (e i)) *
      (∏ i ∈ S, (MvPolynomial.X i : Poly A n) ^ (k - e i)) = monomial (A := A) S ^ k := by
    rw [← Finset.prod_mul_distrib]
    have hterm : ∀ i ∈ S, (MvPolynomial.X i : Poly A n) ^ (e i) *
        (MvPolynomial.X i : Poly A n) ^ (k - e i) = (MvPolynomial.X i : Poly A n) ^ k := by
      intro i hi
      rw [← pow_add, Nat.add_sub_cancel' (hkle i hi)]
    rw [Finset.prod_congr rfl hterm]
    simp only [monomial, Var]
    rw [← Finset.prod_pow]
  have hpoly : monomial (A := A) S ^ k =
      xpow (A := A) e * (∏ i ∈ S, (MvPolynomial.X i : Poly A n) ^ (k - e i)) := by
    rw [hxe, hprod]
  have hmk : LocalizedModule.mk m s =
      LocalizedModule.mk ((∏ i ∈ S, (MvPolynomial.X i : Poly A n) ^ (k - e i)) * m)
        (den (A := A) S k) := by
    rw [LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    simp only [Submonoid.smul_def, one_smul, smul_eq_mul]
    rw [den_coe, hse, hpoly]
    ring
  refine ⟨cOf S k ((∏ i ∈ S, (MvPolynomial.X i : Poly A n) ^ (k - e i)) * m), ?_⟩
  rw [Phi_cOf, ← hmk]
  exact hs.symm

/-! ## Injectivity of `Phi` -/

lemma KIdx_le_of_mem_support {S : Finset (Fin n)} {c : Idx S →₀ A} {β : Idx S}
    (hβ : β ∈ c.support) : KIdx S β.1 ≤ ∑ β' ∈ c.support, KIdx S β'.1 :=
  Finset.single_le_sum (f := fun β' : Idx S => KIdx S β'.1) (fun _ _ => Nat.zero_le _) hβ

lemma Phi_eq_zero (S : Finset (Fin n)) (c : Idx S →₀ A)
    (hc : Phi (A := A) (n := n) S c = 0) : c = 0 := by
  classical
  set k : ℕ := ∑ β ∈ c.support, KIdx S β.1 with hk
  have h1 : Phi (A := A) (n := n) S c
      = ∑ β ∈ c.support, (c β) • bAt (A := A) (n := n) S β.1 k := by
    rw [Phi_apply]
    change (∑ β ∈ c.support, (c β) • bloc (A := A) (n := n) S β) = _
    exact Finset.sum_congr rfl (fun β hβ =>
      congrArg (fun x => (c β) • x)
        (bloc_eq_bAt β (Adm.of_le (Adm.KIdx β.2) (KIdx_le_of_mem_support hβ))))
  have h2 : (∑ β ∈ c.support, (c β) • bAt (A := A) (n := n) S β.1 k)
      = LocalizedModule.mk (∑ β ∈ c.support, (c β) • xpow (A := A) (eIdx S k β.1))
          (den (A := A) S k) := by
    have hb : ∀ β ∈ c.support, (c β) • bAt (A := A) (n := n) S β.1 k
        = LocalizedModule.mk ((c β) • xpow (A := A) (eIdx S k β.1)) (den (A := A) S k) := by
      intro β _
      rw [bAt_eq_mk, mk_smul]
    rw [Finset.sum_congr rfl hb, ← mk_finset_sum]
  have h3 : (∑ β ∈ c.support, (c β) • xpow (A := A) (eIdx S k β.1)) = 0 :=
    lmb_mk_den_eq_zero (by rw [← h2, ← h1]; exact hc)
  exact xpow_sum_eq_zero (fun β hβ => Adm.of_le (Adm.KIdx β.2) (KIdx_le_of_mem_support hβ)) h3

lemma Phi_injective (S : Finset (Fin n)) : Function.Injective (Phi (A := A) (n := n) S) := by
  intro c c' hcc
  have h0 : Phi (A := A) (n := n) S (c - c') = 0 := by rw [map_sub, hcc, sub_self]
  exact sub_eq_zero.mp (Phi_eq_zero (A := A) (n := n) S (c - c') h0)

/-! ## The basis -/

noncomputable def locBasis (S : Finset (Fin n)) :
    Module.Basis (Idx S) A (locAt (A := A) (M := Poly A n) S) :=
  Module.Basis.ofRepr (LinearEquiv.ofBijective (Phi (A := A) (n := n) S)
    ⟨Phi_injective (A := A) (n := n) S, Phi_surjective (A := A) (n := n) S⟩).symm

lemma locBasis_apply (S : Finset (Fin n)) (β : Idx S) :
    locBasis (A := A) (n := n) S β = bloc (A := A) (n := n) S β := by
  rw [locBasis, Module.Basis.coe_ofRepr, LinearEquiv.symm_symm]
  change Phi (A := A) (n := n) S (Finsupp.single β 1) = bloc (A := A) (n := n) S β
  rw [Phi_single, one_smul]

/-! ## The three properties of the basis -/

lemma shiftIdx_val_apply (S : Finset (Fin n)) (i : Fin n) (β : Idx S) (j : Fin n) :
    (shiftIdx S i β).1 j = if j = i then β.1 j + 1 else β.1 j := rfl

lemma Adm_shiftIdx (S : Finset (Fin n)) (i : Fin n) (β : Idx S) :
    Adm S (KIdx S β.1) (shiftIdx S i β).1 := by
  intro j
  rw [shiftIdx_val_apply]
  by_cases hji : j = i
  · rw [ite_eq_left hji]
    by_cases hj : j ∈ S
    · rw [ite_eq_left hj]
      have := le_KIdx S β.1 hj
      linarith
    · rw [ite_eq_right (by simpa using hj)]
      have := β.2 j hj
      linarith
  · rw [ite_eq_right (by simpa using hji)]
    by_cases hj : j ∈ S
    · rw [ite_eq_left hj]
      exact le_KIdx S β.1 hj
    · rw [ite_eq_right (by simpa using hj)]
      have := β.2 j hj
      linarith

lemma locBasis_X_smul (S : Finset (Fin n)) (β : Idx S) (i : Fin n) :
    (MvPolynomial.X i : Poly A n) • locBasis (A := A) (n := n) S β =
      locBasis (A := A) (n := n) S (shiftIdx S i β) := by
  have h1 : (MvPolynomial.X i : Poly A n) • locBasis (A := A) (n := n) S β
      = bAt (A := A) (n := n) S (shiftIdx S i β).1 (KIdx S β.1) := by
    rw [locBasis_apply, bloc_eq_bAt β (Adm.KIdx β.2),
      lmbA_bAt_X_smul S (Adm.KIdx β.2) i]
    rfl
  have h2 : locBasis (A := A) (n := n) S (shiftIdx S i β)
      = bAt (A := A) (n := n) S (shiftIdx S i β).1 (KIdx S β.1) := by
    rw [locBasis_apply]
    exact bloc_eq_bAt (shiftIdx S i β) (Adm_shiftIdx S i β)
  rw [h1, h2]

lemma locBasis_resAt (S T : Finset (Fin n)) (h : S ⊆ T) (β : Idx S) :
    resAt (M := Poly A n) h (locBasis (A := A) (n := n) S β) =
      locBasis (A := A) (n := n) T
        ⟨β.1, fun i hi => β.2 i (fun hmem => hi (h hmem))⟩ := by
  have h1 : resAt (M := Poly A n) h (locBasis (A := A) (n := n) S β)
      = bAt (A := A) (n := n) T β.1 (KIdx S β.1) := by
    rw [locBasis_apply, bloc_eq_bAt β (Adm.KIdx β.2), lmbA_bAt_resAt S T h (Adm.KIdx β.2)]
  have h2 : locBasis (A := A) (n := n) T
        ⟨β.1, fun i hi => β.2 i (fun hmem => hi (h hmem))⟩
      = bAt (A := A) (n := n) T β.1 (KIdx S β.1) := by
    rw [locBasis_apply,
      show (⟨β.1, fun i hi => β.2 i (fun hmem => hi (h hmem))⟩ : Idx T) =
        ⟨β.1, (Adm.mono (Adm.KIdx β.2) h).idx⟩ from Subtype.ext rfl,
      bloc_eq_bAt ⟨β.1, (Adm.mono (Adm.KIdx β.2) h).idx⟩ (Adm.mono (Adm.KIdx β.2) h)]
  rw [h1, h2]

lemma degZero_span (S : Finset (Fin n)) (d : ℕ) :
    degZero (A := A) (M := Poly A n) (shift (A := A) (n := n) d) S
      = Submodule.span A {y | ∃ β : Idx S, (∑ i, β.1 i) = -(d : ℤ) ∧
          y = locBasis (A := A) (n := n) S β} := by
  refine le_antisymm ?_ ?_
  · rw [degZero]
    refine iSup_le (fun k => ?_)
    rw [Submodule.map_le_iff_le_comap]
    intro m hm
    rw [Submodule.mem_comap, LinearMap.comp_apply]
    by_cases hlt : d ≤ k * S.card
    · rw [shift_of_le hlt] at hm
      have hm' : m ∈ homSub A n (k * S.card - d) := by simpa using hm
      have h1 : toLoc (A := A) (M := Poly A n) S m
          = ∑ v ∈ m.support, (m.coeff v) •
              toLoc (A := A) (M := Poly A n) S (xpow (A := A) (n := n) (fun i => v i)) := by
        conv_lhs => rw [as_sum_smul m]
        rw [map_sum]
        exact Finset.sum_congr rfl (fun v _ => by rw [map_smul])
      have h2 : divPow (A := A) (M := Poly A n) S k (toLoc (A := A) (M := Poly A n) S m)
          = ∑ v ∈ m.support, (m.coeff v) •
              locBasis (A := A) (n := n) S (subIdx S k (fun i => v i)) := by
        rw [h1, map_sum]
        refine Finset.sum_congr rfl (fun v hv => ?_)
        rw [map_smul, divPow_toLoc_eq_mk, locBasis_apply, bloc_subIdx]
      rw [h2]
      refine Submodule.sum_mem _ (fun v hv => ?_)
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨subIdx S k (fun i => v i), ?_, rfl⟩)
      simp only [subIdx_val]
      rw [Finset.sum_sub_distrib, sum_ite_mem_card, ← Nat.cast_sum,
        lmb_support_degree (A := A) (n := n) hm' hv, Nat.cast_sub hlt]
      push_cast
      ring
    · rw [shift_of_not_le hlt] at hm
      rw [Submodule.mem_bot] at hm
      rw [hm, map_zero, map_zero]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    rintro y ⟨β, hβ, rfl⟩
    rw [locBasis_apply]
    exact bloc_mem_degZero S d β hβ

theorem dsMonBasis {A : Type*} [CommRing A] {n : ℕ} :
    ∃ B : (S : Finset (Fin n)) →
        Module.Basis {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i} A
          (locAt (A := A) (M := Poly A n) S),
      (∀ (S : Finset (Fin n)) (β : {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i}) (i : Fin n),
        (MvPolynomial.X i : Poly A n) • (B S β) =
          B S ⟨fun j => if j = i then β.1 j + 1 else β.1 j, by
            intro j hj
            by_cases h : j = i
            · subst h; simp only [ite_true]; linarith [β.2 j hj]
            · simp only [h, ite_false]; linarith [β.2 j hj]⟩) ∧
      (∀ (S T : Finset (Fin n)) (h : S ⊆ T) (β : {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i}),
        resAt (M := Poly A n) h (B S β) =
          B T ⟨β.1, fun i hi => β.2 i (fun hmem => hi (h hmem))⟩) ∧
      (∀ (S : Finset (Fin n)) (d : ℕ),
        degZero (A := A) (M := Poly A n) (shift (A := A) (n := n) d) S =
          Submodule.span A {y | ∃ β : {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i},
            (∑ i, β.1 i) = -(d : ℤ) ∧ y = B S β}) := by
  refine ⟨fun S => locBasis (A := A) (n := n) S, ?_, ?_, ?_⟩
  · intro S β i
    exact locBasis_X_smul (A := A) (n := n) S β i
  · intro S T h β
    exact locBasis_resAt (A := A) (n := n) S T h β
  · intro S d
    rw [degZero_span]

end Work.DSCOH
