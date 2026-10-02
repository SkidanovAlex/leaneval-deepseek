import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Submission.Commons.Algebra.Polynomial.resultant_eq_norm_adjoinRoot
import Submission.Commons.FieldTheory.Polynomial.monic_index_ge_card_le

namespace Commons.NumberTheory.CharacterSum

open Polynomial
open UniqueFactorizationMonoid
open scoped BigOperators

set_option maxHeartbeats 1000000

noncomputable section

/-- `AdjoinRoot g` of a monic polynomial over a finite field is a finite type, transported
from `Fin g.natDegree →₀ F` along the power basis. -/
instance instFintypeAdjoinRootMonic {F : Type*} [Field F] [Fintype F] (g : Polynomial F)
    [Fact g.Monic] : Fintype (AdjoinRoot g) :=
  Fintype.ofEquiv (Fin g.natDegree →₀ F)
    ((AdjoinRoot.powerBasis' (Fact.out : g.Monic)).basis.repr.symm.toEquiv)

/-- **Resultant product formula.**  For a monic polynomial `f` over a field `F` and any
`A ∈ F[X]`, the resultant `resultant f A` factors over the distinct monic irreducible
factors `P` of `f` as the product of `Algebra.norm F (AdjoinRoot.mk P A)` raised to the
multiplicity of `P` in `f`. -/
theorem resultant_eq_prod_norm_normalizedFactors {F : Type*} [Field F] [DecidableEq F]
    (f A : Polynomial F) (hf : f.Monic) :
    Polynomial.resultant f A = ∏ P ∈ (UniqueFactorizationMonoid.normalizedFactors f).toFinset,
      (Algebra.norm F (AdjoinRoot.mk P A))
        ^ (UniqueFactorizationMonoid.normalizedFactors f).count P := by
  classical
  set s := (UniqueFactorizationMonoid.normalizedFactors f).toFinset with hs
  set k : Polynomial F → ℕ := fun P => (UniqueFactorizationMonoid.normalizedFactors f).count P
    with hk
  have hfac : f = ∏ P ∈ s, P ^ k P := by
    rw [hs]
    have h1 : (UniqueFactorizationMonoid.normalizedFactors f).prod = f :=
      Commons.FieldTheory.Polynomial.prod_normalizedFactors_of_monic f hf
    conv_lhs => rw [← h1]
    rw [hk]
    exact Finset.prod_multiset_count _
  have hlc : (∏ P ∈ s, ((P ^ k P : Polynomial F)).leadingCoeff) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun P hP => ?_
    have hPmonic : P.Monic :=
      Commons.FieldTheory.Polynomial.monic_of_mem_normalizedFactors hf.ne_zero (by
        rw [hs] at hP; exact Multiset.mem_toFinset.mp hP)
    rw [(hPmonic.pow (k P)).leadingCoeff]
    exact one_ne_zero
  have hmain := Polynomial.resultant_prod_left s (fun P => P ^ k P) A A.natDegree hlc le_rfl
  rw [← hfac] at hmain
  rw [hmain]
  refine Finset.prod_congr rfl fun P hP => ?_
  have hPmonic : P.Monic :=
    Commons.FieldTheory.Polynomial.monic_of_mem_normalizedFactors hf.ne_zero (by
      rw [hs] at hP; exact Multiset.mem_toFinset.mp hP)
  have hPow : (P ^ k P : Polynomial F).resultant A (P ^ k P).natDegree A.natDegree
      = (P.resultant A P.natDegree A.natDegree) ^ k P := by
    rw [Polynomial.resultant_pow_left P A (k P) A.natDegree _ le_rfl]
    rw [hPmonic.leadingCoeff, one_pow]
    exact one_ne_zero
  rw [hPow, Commons.Algebra.Polynomial.resultant_eq_norm_adjoinRoot P hPmonic A]

/-- For a nonconstant polynomial `f`, the resultant is multiplicative in its second
argument. -/
lemma resultant_mul_right_eq_mul {F : Type*} [Field F] (f : Polynomial F)
    (hf : f.natDegree ≠ 0) (a b : Polynomial F) :
    Polynomial.resultant f (a * b) = Polynomial.resultant f a * Polynomial.resultant f b := by
  have hzero : Polynomial.resultant f (0 : Polynomial F) = 0 := by
    have h := Polynomial.resultant_zero_right f f.natDegree 0
    simpa [zero_pow hf] using h
  rcases eq_or_ne a 0 with rfl | ha
  · rw [zero_mul, hzero]; ring
  rcases eq_or_ne b 0 with rfl | hb
  · rw [mul_zero, hzero]; ring
  · have h1 := Polynomial.resultant_mul_right f a b f.natDegree le_rfl
    rw [← Polynomial.natDegree_mul ha hb] at h1
    exact h1

/-- **Fibre sum of a surjective additive homomorphism**, `ℂ`-valued version. -/
lemma sum_comp_surjective_addHom_complex {V W : Type*} [AddCommGroup V] [Fintype V]
    [DecidableEq V] [AddCommGroup W] [Fintype W] [DecidableEq W] (ψ : V →+ W)
    (hψ : Function.Surjective ψ) (f : W → ℂ) :
    ∑ v : V, f (ψ v) =
      ((Finset.univ.filter (fun v => ψ v = 0)).card : ℂ) * ∑ w : W, f w := by
  classical
  have hfib : ∀ w ∈ Set.range ψ,
      (Finset.univ.filter (fun v => ψ v = w)).card
        = (Finset.univ.filter (fun v => ψ v = 0)).card :=
    fun w hw => AddMonoidHom.card_fiber_eq_of_mem_range ψ hw (Set.mem_range.mpr ⟨0, by simp⟩)
  have h1 : ∑ w : W, ∑ v ∈ Finset.univ.filter (fun v => ψ v = w), f (ψ v)
      = ∑ v : V, f (ψ v) := Finset.sum_fiberwise Finset.univ ψ _
  have hinner : ∀ w : W,
      (∑ v ∈ Finset.univ.filter (fun v => ψ v = w), f (ψ v))
        = ((Finset.univ.filter (fun v => ψ v = 0)).card : ℂ) * f w := by
    intro w
    have hc := hfib w (Set.mem_range.mpr (hψ w))
    rw [Finset.sum_congr rfl (fun v hv => by rw [(Finset.mem_filter.mp hv).2])]
    rw [Finset.sum_const, hc, nsmul_eq_mul]
  calc ∑ v : V, f (ψ v)
      = ∑ w : W, ∑ v ∈ Finset.univ.filter (fun v => ψ v = w), f (ψ v) := h1.symm
    _ = ∑ w : W, ((Finset.univ.filter (fun v => ψ v = 0)).card : ℂ) * f w :=
        Finset.sum_congr rfl (fun w _ => hinner w)
    _ = ((Finset.univ.filter (fun v => ψ v = 0)).card : ℂ) * ∑ w : W, f w := by
        rw [Finset.mul_sum]

/-- **Degree bound for the L-function of a multiplicative character.**
Let `F` be a finite field, `χ : MulChar F ℂ` nontrivial of order `e ≥ 2`, and `f ∈ F[X]` monic,
nonzero, not a constant multiple of a `p`-th power for any prime `p ∣ e`.  Then for every
`n ≥ (radical f).natDegree`, the sum of `χ (resultant A f)` over the monic polynomials `A` of
degree `n` vanishes.

Proof route: write `f = ∏_i P_i^{k_i}` (distinct monic irreducibles `P_i`, `k_i ≥ 1`).  The
hypothesis gives some `i` with `e ∤ k_i`.  For monic `A`,
`resultant A f = ∏_i resultant A P_i ^ {k_i}` (multiplicativity of the resultant), and
`resultant A P_i = (-1)^{deg A · deg P_i} · N_{F[X]/P_i}(A mod P_i)`.  Since
`deg (radical f) = ∑_i deg P_i`, for `n ≥ deg (radical f)` every element of `F[X]/(radical f)`
has exactly `q^{n - deg (radical f)}` monic lifts of degree `n`, and the sum becomes
`(χ (-1)^{n · deg f} · q^{n - deg (radical f)}) · ∏_i ∑_{B_i ∈ F[X]/P_i} (χ ∘ N_i)^{k_i}(B_i)`.
The `i`-th factor is `0` because `(χ ∘ N_i)^{k_i}` is a nontrivial multiplicative character of the
finite field `F[X]/P_i` (the norm `N_i` is surjective and `orderOf χ = e ∤ k_i`). -/
theorem mulchar_sum_monic_resultant_eq_zero {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (e : ℕ) (he : 2 ≤ e) (hdiv : e ∣ Fintype.card F - 1) (χ : MulChar F ℂ) (hχ : χ ≠ 1)
    (hord : orderOf χ = e) (f : Polynomial F) (hf : f ≠ 0) (hmon : f.Monic)
    (hnd : ∀ p : ℕ, p.Prime → p ∣ e → ∀ (a : F) (h : Polynomial F),
      f ≠ Polynomial.C a * h ^ p)
    (n : ℕ) (hn : (UniqueFactorizationMonoid.radical f).natDegree ≤ n) :
    ∑ c : Fin n → F, χ (Polynomial.resultant
      (Polynomial.X ^ n + ∑ i : Fin n, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)) f) = 0 := by
  classical
  set R : Polynomial F := UniqueFactorizationMonoid.radical f with hRdef
  have hRmonic : R.Monic := by
    rw [hRdef]; exact Commons.FieldTheory.Polynomial.radical_monic f hmon
  haveI hRfact : Fact R.Monic := ⟨hRmonic⟩
  have hDn : R.natDegree ≤ n := by rw [hRdef]; exact hn
  have hfdeg : f.natDegree ≠ 0 := by
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (by omega : e ≠ 1)
    intro h
    exact hnd p hp hpdvd 1 1 (by
      rw [Polynomial.eq_one_of_monic_natDegree_zero hmon h]; simp)
  -- the character `G` on `F[X]/(radical f)`
  let G : AdjoinRoot R → ℂ := fun x =>
    χ (Polynomial.resultant f (AdjoinRoot.modByMonicHom hRmonic x))
  have G_congr : ∀ {A B : Polynomial F}, AdjoinRoot.mk R A = AdjoinRoot.mk R B →
      Polynomial.resultant f A = Polynomial.resultant f B := by
    intro A B hAB
    rw [resultant_eq_prod_norm_normalizedFactors f A hmon,
        resultant_eq_prod_norm_normalizedFactors f B hmon]
    refine Finset.prod_congr rfl fun P hP => ?_
    have hPR : P ∣ R := by
      rw [hRdef, Commons.FieldTheory.Polynomial.radical_eq_toFinset_prod]
      exact Finset.dvd_prod_of_mem id hP
    have hAB' : R ∣ A - B := AdjoinRoot.mk_eq_mk.mp hAB
    have hPAB : AdjoinRoot.mk P A = AdjoinRoot.mk P B := by
      rw [AdjoinRoot.mk_eq_mk]
      exact dvd_trans hPR hAB'
    rw [hPAB]
  have G_mul : ∀ x y : AdjoinRoot R, G (x * y) = G x * G y := by
    intro x y
    have hc : AdjoinRoot.mk R (AdjoinRoot.modByMonicHom hRmonic (x * y))
        = AdjoinRoot.mk R (AdjoinRoot.modByMonicHom hRmonic x
            * AdjoinRoot.modByMonicHom hRmonic y) := by
      rw [AdjoinRoot.mk_leftInverse hRmonic, map_mul, AdjoinRoot.mk_leftInverse hRmonic,
        AdjoinRoot.mk_leftInverse hRmonic]
    have hres := G_congr hc
    show χ (Polynomial.resultant f (AdjoinRoot.modByMonicHom hRmonic (x * y)))
        = χ (Polynomial.resultant f (AdjoinRoot.modByMonicHom hRmonic x))
          * χ (Polynomial.resultant f (AdjoinRoot.modByMonicHom hRmonic y))
    rw [hres, resultant_mul_right_eq_mul f hfdeg, map_mul]
  set s := (UniqueFactorizationMonoid.normalizedFactors f).toFinset with hs
  set kf : Polynomial F → ℕ := fun P => (UniqueFactorizationMonoid.normalizedFactors f).count P
    with hkf
  have hfac : f = ∏ P ∈ s, P ^ kf P := by
    rw [hs, hkf]
    have h1 : (UniqueFactorizationMonoid.normalizedFactors f).prod = f :=
      Commons.FieldTheory.Polynomial.prod_normalizedFactors_of_monic f hmon
    conv_lhs => rw [← h1]
    exact Finset.prod_multiset_count _
  have hex : ∃ P ∈ s, ¬ e ∣ kf P := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd (by omega : e ≠ 1)
    refine hnd p hpprime hpdvd 1 (∏ P ∈ s, P ^ (kf P / p)) ?_
    rw [Polynomial.C_1, one_mul, hfac, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun P hP => ?_
    rw [← pow_mul, Nat.div_mul_cancel (dvd_trans hpdvd (hcon P hP))]
  obtain ⟨P0, hP0mem, hP0ndvd⟩ := hex
  have hP0mem' : P0 ∈ (UniqueFactorizationMonoid.normalizedFactors f).toFinset := by
    rw [← hs]; exact hP0mem
  have hP0monic : P0.Monic :=
    Commons.FieldTheory.Polynomial.monic_of_mem_normalizedFactors hf
      (Multiset.mem_toFinset.mp hP0mem')
  have hP0irr : Irreducible P0 :=
    Commons.FieldTheory.Polynomial.irreducible_of_mem_normalizedFactors hf
      (Multiset.mem_toFinset.mp hP0mem')
  haveI hP0factM : Fact P0.Monic := ⟨hP0monic⟩
  haveI hP0factI : Fact (Irreducible P0) := ⟨hP0irr⟩
  haveI hP0fin : Module.Finite F (AdjoinRoot P0) := hP0monic.finite_adjoinRoot
  set k0 : ℕ := kf P0 with hk0def
  have hk0ndvd : ¬ e ∣ k0 := by rw [hk0def]; exact hP0ndvd
  -- find `z ≠ 0` with `(χ z) ^ k0 ≠ 1`
  have hz : ∃ z : F, z ≠ 0 ∧ (χ z) ^ k0 ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hpow : χ ^ k0 = 1 := by
      refine MulChar.ext fun a => ?_
      rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
      exact hcon (a : F) a.ne_zero
    have hdiv : e ∣ k0 := by
      rw [← hord]
      exact orderOf_dvd_iff_pow_eq_one.mpr hpow
    exact hk0ndvd hdiv
  obtain ⟨z, hzne, hzval⟩ := hz
  -- find `y` with `Algebra.norm F y = z`
  obtain ⟨y, hy⟩ := FiniteField.norm_surjective F (AdjoinRoot P0) z
  have hyne : y ≠ 0 := fun h => hzne (by rw [← hy, h, Algebra.norm_zero])
  -- find `A0` with `mk P0 A0 = y`
  obtain ⟨A0, hA0⟩ := AdjoinRoot.mk_surjective (g := P0) y
  -- CRT: build `E`
  have hcop : Pairwise (fun P Q : ↥s => IsCoprime
      (Ideal.span ({((P : Polynomial F))} : Set (Polynomial F)))
      (Ideal.span ({((Q : Polynomial F))} : Set (Polynomial F)))) := by
    intro P Q hPQ
    rw [Ideal.isCoprime_span_singleton_iff]
    have hPm : (P : Polynomial F).Monic :=
      Commons.FieldTheory.Polynomial.monic_of_mem_normalizedFactors hf
        (Multiset.mem_toFinset.mp (by rw [← hs]; exact P.2))
    have hQm : (Q : Polynomial F).Monic :=
      Commons.FieldTheory.Polynomial.monic_of_mem_normalizedFactors hf
        (Multiset.mem_toFinset.mp (by rw [← hs]; exact Q.2))
    have hPi : Irreducible (P : Polynomial F) :=
      Commons.FieldTheory.Polynomial.irreducible_of_mem_normalizedFactors hf
        (Multiset.mem_toFinset.mp (by rw [← hs]; exact P.2))
    have hQi : Irreducible (Q : Polynomial F) :=
      Commons.FieldTheory.Polynomial.irreducible_of_mem_normalizedFactors hf
        (Multiset.mem_toFinset.mp (by rw [← hs]; exact Q.2))
    have hne : (P : Polynomial F) ≠ (Q : Polynomial F) := fun h => hPQ (Subtype.ext h)
    rw [hPi.coprime_iff_not_dvd]
    intro hdvd
    exact hne (Polynomial.eq_of_monic_of_associated hPm hQm
      ((hPi.dvd_irreducible_iff_associated hQi).mp hdvd))
  obtain ⟨E, hE⟩ := Ideal.exists_forall_sub_mem_ideal hcop
    (fun P : ↥s => if (P : Polynomial F) = P0 then A0 else 1)
  have hmkE_P0 : AdjoinRoot.mk P0 E = y := by
    have hmem : E - A0 ∈ Ideal.span ({P0} : Set (Polynomial F)) := by
      have := hE ⟨P0, hP0mem⟩
      simpa using this
    rw [← hA0, AdjoinRoot.mk_eq_mk]
    exact Ideal.mem_span_singleton.mp hmem
  -- `mk R E` is a unit
  have hEmk_ne0 : ∀ P ∈ s, AdjoinRoot.mk P E ≠ 0 := by
    intro P hPm
    by_cases hEq : (P : Polynomial F) = P0
    · rw [hEq, hmkE_P0]; exact hyne
    · have hPm' : P.Monic :=
        Commons.FieldTheory.Polynomial.monic_of_mem_normalizedFactors hf
          (Multiset.mem_toFinset.mp (by rw [← hs]; exact hPm))
      have hPi' : Irreducible P :=
        Commons.FieldTheory.Polynomial.irreducible_of_mem_normalizedFactors hf
          (Multiset.mem_toFinset.mp (by rw [← hs]; exact hPm))
      haveI : Fact P.Monic := ⟨hPm'⟩
      haveI : Fact (Irreducible P) := ⟨hPi'⟩
      have hif : (if (P : Polynomial F) = P0 then A0 else 1) = 1 := if_neg hEq
      have hmem : E - 1 ∈ Ideal.span ({(P : Polynomial F)} : Set (Polynomial F)) := by
        have := hE ⟨P, hPm⟩
        rwa [hif] at this
      have hP1 : (P : Polynomial F) ∣ E - 1 := Ideal.mem_span_singleton.mp hmem
      have hmk1 : AdjoinRoot.mk P E = 1 := by
        have h := (AdjoinRoot.mk_eq_mk (f := (P : Polynomial F)) (g := E) (h := 1)).mpr hP1
        simpa using h
      rw [hmk1]; exact one_ne_zero
  have hEmk_ne : ∀ P ∈ s, ¬ P ∣ E := fun P hPm hdvd =>
    hEmk_ne0 P hPm (AdjoinRoot.mk_eq_zero.mpr hdvd)
  have hEcp : IsCoprime E R := by
    have hRprod : R = ∏ P ∈ s, P := by
      rw [hRdef, Commons.FieldTheory.Polynomial.radical_eq_toFinset_prod]; rfl
    rw [hRprod]
    refine IsCoprime.prod_right fun P hP => ?_
    have hPi : Irreducible P :=
      Commons.FieldTheory.Polynomial.irreducible_of_mem_normalizedFactors hf
        (Multiset.mem_toFinset.mp (by rw [← hs]; exact hP))
    exact (hPi.coprime_iff_not_dvd.mpr (hEmk_ne P hP)).symm
  obtain ⟨c1, c2, hc12⟩ := hEcp
  have hmul1 : AdjoinRoot.mk R c1 * AdjoinRoot.mk R E = 1 := by
    have h : c1 * E = 1 - c2 * R := by rw [← hc12]; ring
    rw [← map_mul, h, map_sub, map_mul, AdjoinRoot.mk_self, mul_zero, sub_zero, map_one]
  have hmul2 : AdjoinRoot.mk R E * AdjoinRoot.mk R c1 = 1 := by
    rw [mul_comm, hmul1]
  let u : (AdjoinRoot R)ˣ := Units.mk (AdjoinRoot.mk R E) (AdjoinRoot.mk R c1) hmul2 hmul1
  have huval : (u : AdjoinRoot R) = AdjoinRoot.mk R E := rfl
  -- `G u ≠ 1`
  have hresE : Polynomial.resultant f E = z ^ k0 := by
    rw [resultant_eq_prod_norm_normalizedFactors f E hmon]
    have hsingle : ∏ P ∈ (UniqueFactorizationMonoid.normalizedFactors f).toFinset,
        (Algebra.norm F (AdjoinRoot.mk P E))
          ^ (UniqueFactorizationMonoid.normalizedFactors f).count P
        = (Algebra.norm F (AdjoinRoot.mk P0 E))
          ^ (UniqueFactorizationMonoid.normalizedFactors f).count P0 := by
      refine Finset.prod_eq_single P0 ?_ ?_
      · intro Q hQ hQne
        have hQmem : Q ∈ s := by rw [hs]; exact hQ
        have hif : (if Q = P0 then A0 else 1) = 1 := if_neg hQne
        have hmem : E - 1 ∈ Ideal.span ({Q} : Set (Polynomial F)) := by
          have := hE ⟨Q, hQmem⟩
          rwa [hif] at this
        have hQ1 : Q ∣ E - 1 := Ideal.mem_span_singleton.mp hmem
        have hmk1 : AdjoinRoot.mk Q E = 1 := by
          have h := (AdjoinRoot.mk_eq_mk (f := Q) (g := E) (h := 1)).mpr hQ1
          simpa using h
        rw [hmk1, map_one, one_pow]
      · intro hmem
        exact absurd hP0mem' hmem
    rw [hsingle, hmkE_P0, hy]
  have hGu : G (u : AdjoinRoot R) ≠ 1 := by
    have hval : G (u : AdjoinRoot R) = (χ z) ^ k0 := by
      have h1 : Polynomial.resultant f (AdjoinRoot.modByMonicHom hRmonic (AdjoinRoot.mk R E))
          = Polynomial.resultant f E :=
        G_congr (by rw [AdjoinRoot.mk_leftInverse hRmonic])
      show χ (Polynomial.resultant f (AdjoinRoot.modByMonicHom hRmonic (u : AdjoinRoot R)))
          = (χ z) ^ k0
      rw [huval, ← map_pow, h1, hresE]
    rw [hval]; exact hzval
  -- the sum over `F[X]/(radical f)` vanishes
  have hGsum : ∑ x : AdjoinRoot R, G x = 0 := by
    have hbij : ∑ x : AdjoinRoot R, G ((u : AdjoinRoot R) * x) = ∑ x : AdjoinRoot R, G x := by
      let ee : AdjoinRoot R ≃ AdjoinRoot R :=
        { toFun := fun x => (u : AdjoinRoot R) * x
          invFun := fun x => (↑(u⁻¹) : AdjoinRoot R) * x
          left_inv := fun x => by
            change (↑u⁻¹ : AdjoinRoot R) * ((u : AdjoinRoot R) * x) = x
            rw [← mul_assoc, Units.inv_mul, one_mul]
          right_inv := fun x => by
            change (u : AdjoinRoot R) * ((↑u⁻¹ : AdjoinRoot R) * x) = x
            rw [← mul_assoc, Units.mul_inv, one_mul] }
      exact Equiv.sum_comp ee G
    have h2 : ∑ x : AdjoinRoot R, G x = G (u : AdjoinRoot R) * ∑ x : AdjoinRoot R, G x := by
      rw [Finset.mul_sum, ← hbij]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← G_mul]
    have h2' : G (u : AdjoinRoot R) * ∑ x : AdjoinRoot R, G x = ∑ x : AdjoinRoot R, G x := h2.symm
    have h3 : (1 - G (u : AdjoinRoot R)) * ∑ x : AdjoinRoot R, G x = 0 := by
      rw [sub_mul, one_mul, h2', sub_self]
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd (sub_eq_zero.mp h).symm hGu
    · exact h
  -- the linear map `ψ`
  let ψ : (Fin n → F) →ₗ[F] AdjoinRoot R :=
    { toFun := fun c => ∑ i : Fin n, c i • (AdjoinRoot.root R) ^ (i : ℕ)
      map_add' := by intro a b; simp [Finset.sum_add_distrib, add_smul]
      map_smul' := by
        intro a c
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl (fun i _ => by
          simp only [Pi.smul_apply, Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply,
            map_mul, mul_assoc]) }
  have hψ : ∀ c : Fin n → F, ψ c = ∑ i : Fin n, c i • (AdjoinRoot.root R) ^ (i : ℕ) :=
    fun _ => rfl
  have hψ_surj : Function.Surjective ψ := by
    have htop : (⊤ : Submodule F (AdjoinRoot R)) ≤ LinearMap.range ψ := by
      rw [← (AdjoinRoot.powerBasis' hRmonic).basis.span_eq]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨j, rfl⟩
      rw [(AdjoinRoot.powerBasis' hRmonic).basis_eq_pow j]
      refine ⟨Pi.single (⟨(j : ℕ), lt_of_lt_of_le j.isLt hDn⟩ : Fin n) 1, ?_⟩
      rw [hψ]
      rw [Finset.sum_eq_single (⟨(j : ℕ), lt_of_lt_of_le j.isLt hDn⟩ : Fin n)]
      · simp
      · intro b _ hb
        rw [Pi.single_eq_of_ne hb, zero_smul]
      · intro h; exact absurd (Finset.mem_univ _) h
    intro B
    exact htop Submodule.mem_top
  have hmk : ∀ c : Fin n → F,
      AdjoinRoot.mk R (Commons.FieldTheory.Polynomial.repPoly n c)
        = (AdjoinRoot.root R) ^ n + ψ c := by
    intro c
    have hterm : ∀ i : Fin n,
        AdjoinRoot.mk R (Polynomial.C (c i) * Polynomial.X ^ (i : ℕ))
          = c i • (AdjoinRoot.root R) ^ (i : ℕ) := by
      intro i
      rw [map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
      rw [Algebra.smul_def, AdjoinRoot.algebraMap_eq]
    rw [Commons.FieldTheory.Polynomial.repPoly, map_add, map_pow, AdjoinRoot.mk_X, map_sum, hψ]
    refine congrArg (HAdd.hAdd _) ?_
    exact Finset.sum_congr rfl (fun i _ => hterm i)
  have hper : ∀ c : Fin n → F,
      χ (Polynomial.resultant (Commons.FieldTheory.Polynomial.repPoly n c) f)
        = χ ((-1 : F) ^ (n * f.natDegree))
          * G (AdjoinRoot.mk R (Commons.FieldTheory.Polynomial.repPoly n c)) := by
    intro c
    have hcomm : Polynomial.resultant (Commons.FieldTheory.Polynomial.repPoly n c) f
        = (-1 : F) ^ (n * f.natDegree)
          * Polynomial.resultant f (Commons.FieldTheory.Polynomial.repPoly n c) := by
      rw [Commons.FieldTheory.Polynomial.repPoly_natDegree n c]
      exact Polynomial.resultant_comm (f := Commons.FieldTheory.Polynomial.repPoly n c)
        (g := f) (m := n) (n := f.natDegree)
    have hGA : Polynomial.resultant f (Commons.FieldTheory.Polynomial.repPoly n c)
        = Polynomial.resultant f (AdjoinRoot.modByMonicHom hRmonic
            (AdjoinRoot.mk R (Commons.FieldTheory.Polynomial.repPoly n c))) :=
      G_congr (AdjoinRoot.mk_leftInverse hRmonic _).symm
    rw [hcomm, map_mul, hGA]
  change ∑ c : Fin n → F,
      χ (Polynomial.resultant (Commons.FieldTheory.Polynomial.repPoly n c) f) = 0
  calc ∑ c : Fin n → F,
        χ (Polynomial.resultant (Commons.FieldTheory.Polynomial.repPoly n c) f)
      = ∑ c : Fin n → F, χ ((-1 : F) ^ (n * f.natDegree))
          * G (AdjoinRoot.mk R (Commons.FieldTheory.Polynomial.repPoly n c)) :=
        Finset.sum_congr rfl (fun c _ => hper c)
    _ = χ ((-1 : F) ^ (n * f.natDegree))
          * ∑ c : Fin n → F, G (AdjoinRoot.mk R (Commons.FieldTheory.Polynomial.repPoly n c)) := by
        rw [Finset.mul_sum]
    _ = χ ((-1 : F) ^ (n * f.natDegree))
          * ∑ c : Fin n → F, G ((AdjoinRoot.root R) ^ n + ψ c) := by
        refine congrArg (HMul.hMul _) ?_
        exact Finset.sum_congr rfl (fun c _ => by rw [hmk c])
    _ = χ ((-1 : F) ^ (n * f.natDegree))
          * (((Finset.univ.filter (fun c : Fin n → F => ψ c = 0)).card : ℂ)
            * ∑ w : AdjoinRoot R, G ((AdjoinRoot.root R) ^ n + w)) := by
        refine congrArg (HMul.hMul _) ?_
        exact sum_comp_surjective_addHom_complex ψ.toAddMonoidHom hψ_surj
          (fun w => G ((AdjoinRoot.root R) ^ n + w))
    _ = χ ((-1 : F) ^ (n * f.natDegree))
          * (((Finset.univ.filter (fun c : Fin n → F => ψ c = 0)).card : ℂ)
            * ∑ w : AdjoinRoot R, G w) := by
        refine congrArg (HMul.hMul _) ?_
        refine congrArg (HMul.hMul _) ?_
        exact Equiv.sum_comp (Equiv.addLeft ((AdjoinRoot.root R) ^ n)) G
    _ = 0 := by rw [hGsum, mul_zero, mul_zero]

end

end Commons.NumberTheory.CharacterSum