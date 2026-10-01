import Mathlib
import Submission.Commons.FieldTheory.PrimitiveRoot.exists_isPrimitiveRoot_of_dvd_card_sub_one
import Submission.Commons.FieldTheory.Kummer.exists_prime_pow_of_irreducible_dvd_X_pow_sub_C
import Submission.Commons.FieldTheory.PolyFraction.exists_const_mul_pow_of_pow_eq_div

open Polynomial

namespace Commons.NumberTheory.Stepanov

namespace GpowModXqAux

section Basic

variable {R : Type*} [CommRing R]

/-- The "conjugate product" `∏_{i<e} P(ζ^i T)`. -/
noncomputable def symmProd (e : ℕ) (ζ : R) (P : Polynomial R) : Polynomial R :=
  ∏ i ∈ Finset.range e, P.comp (Polynomial.C (ζ ^ i) * Polynomial.X)

omit [CommRing R] in
lemma coeff_comp_C_mul_X {S : Type*} [CommRing S] (p : Polynomial S) (ζ : S) (j : ℕ) :
    (p.comp (Polynomial.C ζ * Polynomial.X)).coeff j = p.coeff j * ζ^j := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [Polynomial.add_comp, hp, hq, add_mul]
  | monomial n a =>
      rw [Polynomial.monomial_comp, Polynomial.coeff_C_mul, mul_pow, ← C_pow,
        Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial, Polynomial.coeff_monomial]
      split_ifs with h <;> subst_vars <;> ring

omit [CommRing R] in
lemma comp_comp_C_mul_X {S : Type*} [CommRing S] (P : Polynomial S) (ζ : S) (i : ℕ) :
    (P.comp (Polynomial.C (ζ^i) * Polynomial.X)).comp (Polynomial.C ζ * Polynomial.X)
      = P.comp (Polynomial.C (ζ^(i+1)) * Polynomial.X) := by
  rw [Polynomial.comp_assoc]
  congr 1
  rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp, ← mul_assoc, ← C_mul, ← pow_succ]

omit [CommRing R] in
lemma prod_comp {S : Type*} [CommRing S] (s : Finset ℕ) (f : ℕ → Polynomial S) (q : Polynomial S) :
    (∏ i ∈ s, f i).comp q = ∏ i ∈ s, (f i).comp q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, Polynomial.mul_comp, ih]

end Basic

section Domain

variable {R : Type*} [CommRing R] [IsDomain R]

lemma shift_prod {e : ℕ} {ζ : R} (hζ : IsPrimitiveRoot ζ e) (P : Polynomial R) (hP : P ≠ 0) :
    (∏ i ∈ Finset.range e, P.comp (Polynomial.C (ζ ^ (i+1)) * Polynomial.X))
      = ∏ i ∈ Finset.range e, P.comp (Polynomial.C (ζ ^ i) * Polynomial.X) := by
  set f : ℕ → Polynomial R := fun i => P.comp (Polynomial.C (ζ ^ i) * Polynomial.X) with hf
  have hfe : f e = f 0 := by
    simp only [hf]
    rw [hζ.pow_eq_one, pow_zero]
  have hf0eq : f 0 = P := by simp [hf]
  have hf0 : f 0 ≠ 0 := by rw [hf0eq]; exact hP
  have h1 := Finset.prod_range_succ' f e
  have h2 := Finset.prod_range_succ f e
  rw [h2, hfe] at h1
  exact (mul_right_cancel₀ hf0 h1).symm

lemma symmProd_coeff_eq_zero {e : ℕ} {ζ : R} (hζ : IsPrimitiveRoot ζ e) (P : Polynomial R)
    (hP : P ≠ 0) {j : ℕ} (hj : ¬ e ∣ j) : (symmProd e ζ P).coeff j = 0 := by
  rw [symmProd]
  set g : ℕ → Polynomial R := fun i => P.comp (Polynomial.C (ζ ^ i) * Polynomial.X) with hg
  have hinv : (∏ i ∈ Finset.range e, g i).comp (Polynomial.C ζ * Polynomial.X)
      = ∏ i ∈ Finset.range e, g i := by
    rw [prod_comp]
    rw [show (∏ i ∈ Finset.range e, (g i).comp (Polynomial.C ζ * Polynomial.X))
        = ∏ i ∈ Finset.range e, g (i+1) from
      Finset.prod_congr rfl (fun i _ => by
        simp only [hg]; exact comp_comp_C_mul_X P ζ i)]
    exact shift_prod hζ P hP
  have hcoeff := congrArg (fun p => p.coeff j) hinv
  rw [coeff_comp_C_mul_X] at hcoeff
  have hz : ζ^j ≠ 1 := fun h => hj ((hζ.pow_eq_one_iff_dvd j).mp h)
  have h2 : (∏ i ∈ Finset.range e, g i).coeff j * (ζ^j - 1) = 0 := by
    rw [mul_sub, mul_one, hcoeff, sub_self]
  rcases mul_eq_zero.mp h2 with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h) hz

lemma coeff_comp_le (P : Polynomial R) (ζ : R) (i : ℕ) :
    (P.comp (Polynomial.C (ζ ^ i) * Polynomial.X)).natDegree ≤ P.natDegree := by
  refine (Polynomial.natDegree_comp_le).trans ?_
  have hq : (Polynomial.C (ζ ^ i) * Polynomial.X).natDegree ≤ 1 := by
    have h1 : Polynomial.C (ζ^i) * Polynomial.X = Polynomial.monomial 1 (ζ^i) := by
      rw [show (Polynomial.X : Polynomial R) = Polynomial.X ^ 1 from (pow_one _).symm,
        Polynomial.C_mul_X_pow_eq_monomial]
    rw [h1]
    exact Polynomial.natDegree_monomial_le (ζ^i) (m := 1)
  calc P.natDegree * (Polynomial.C (ζ ^ i) * Polynomial.X).natDegree ≤ P.natDegree * 1 :=
        Nat.mul_le_mul_left _ hq
    _ = P.natDegree := Nat.mul_one _

lemma symmProd_natDegree_le {e : ℕ} {ζ : R} (P : Polynomial R) (hPd : P.natDegree < e) :
    (symmProd e ζ P).natDegree ≤ e * (e - 1) := by
  rw [symmProd]
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  calc ∑ i ∈ Finset.range e, (P.comp (Polynomial.C (ζ ^ i) * Polynomial.X)).natDegree
      ≤ ∑ _i ∈ Finset.range e, P.natDegree :=
        Finset.sum_le_sum (fun i _ => coeff_comp_le P ζ i)
    _ = e * P.natDegree := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    _ ≤ e * (e - 1) := Nat.mul_le_mul_left _ (by omega)

lemma symmProd_eq_sum {e : ℕ} {ζ : R} (hζ : IsPrimitiveRoot ζ e) (P : Polynomial R) (hP : P ≠ 0)
    (hPd : P.natDegree < e) :
    symmProd e ζ P
      = ∑ k ∈ Finset.range e, Polynomial.C ((symmProd e ζ P).coeff (e*k)) * Polynomial.X ^ (e*k) := by
  have hdeg := symmProd_natDegree_le (ζ := ζ) P hPd
  apply Polynomial.ext
  intro j
  rw [Polynomial.finsetSum_coeff]
  by_cases hje : e ∣ j
  · obtain ⟨k, rfl⟩ := hje
    rcases lt_or_ge k e with hklt | hkge
    · rw [Finset.sum_eq_single k]
      · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
      · intro b hb hbk
        rw [Polynomial.coeff_C_mul_X_pow, if_neg]
        intro h
        exact hbk (Nat.mul_left_cancel (by omega : 0 < e) h).symm
      · intro hknot
        exact absurd (Finset.mem_range.mpr hklt) hknot
    · have hj0 : (symmProd e ζ P).coeff (e*k) = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        calc (symmProd e ζ P).natDegree ≤ e * (e - 1) := hdeg
          _ < e * k := (Nat.mul_lt_mul_left (by omega : 0 < e)).mpr (by omega)
      rw [hj0]
      rw [Finset.sum_eq_zero]
      intro b hb
      rw [Polynomial.coeff_C_mul_X_pow, if_neg]
      intro h
      have hbe : b < e := Finset.mem_range.mp hb
      have h1 : k = b := Nat.mul_left_cancel (by omega : 0 < e) h
      omega
  · rw [symmProd_coeff_eq_zero hζ P hP hje]
    rw [Finset.sum_eq_zero]
    intro b hb
    rw [Polynomial.coeff_C_mul_X_pow, if_neg]
    intro h
    exact hje ⟨b, h⟩

end Domain


namespace CdegAux

section
variable {T : Type*} [CommSemiring T]

/-- `Cdeg p a` means every coefficient of `p : (Polynomial T)[X]` has `natDegree ≤ a`. -/
def Cdeg (p : Polynomial (Polynomial T)) (a : ℕ) : Prop := ∀ n, (p.coeff n).natDegree ≤ a

lemma cdeg_zero (a : ℕ) : Cdeg (0 : Polynomial (Polynomial T)) a := by
  intro n; rw [Polynomial.coeff_zero]; exact Nat.zero_le _

lemma cdeg_add {p q : Polynomial (Polynomial T)} {a b : ℕ} (hp : Cdeg p a) (hq : Cdeg q b) :
    Cdeg (p + q) (max a b) := by
  intro n
  rw [Polynomial.coeff_add]
  exact (Polynomial.natDegree_add_le _ _).trans (max_le_max (hp n) (hq n))

lemma natDegree_finset_sum_le {ι : Type*} (s : Finset ι) (f : ι → Polynomial T) (a : ℕ)
    (h : ∀ i ∈ s, (f i).natDegree ≤ a) : (∑ i ∈ s, f i).natDegree ≤ a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (Polynomial.natDegree_add_le _ _).trans
        (max_le (h i (Finset.mem_insert_self i s))
          (ih (fun j hj => h j (Finset.mem_insert_of_mem hj))))

lemma cdeg_mul {p q : Polynomial (Polynomial T)} {a b : ℕ} (hp : Cdeg p a) (hq : Cdeg q b) :
    Cdeg (p * q) (a + b) := by
  intro n
  rw [Polynomial.coeff_mul]
  refine natDegree_finset_sum_le _ _ _ (fun x _ => ?_)
  exact (Polynomial.natDegree_mul_le).trans (Nat.add_le_add (hp x.1) (hq x.2))

lemma cdeg_C {s : Polynomial T} {a : ℕ} (h : s.natDegree ≤ a) :
    Cdeg (Polynomial.C s) a := by
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · rw [Polynomial.coeff_C_zero]; exact h
  · rw [Polynomial.coeff_C, if_neg hn]; exact Nat.zero_le _

lemma cdeg_X_pow (n a : ℕ) : Cdeg (Polynomial.X ^ n : Polynomial (Polynomial T)) a := by
  intro m
  rw [Polynomial.coeff_X_pow]
  split_ifs
  · rw [Polynomial.natDegree_one]; exact Nat.zero_le _
  · rw [Polynomial.natDegree_zero]; exact Nat.zero_le _

lemma cdeg_sum {ι : Type*} (s : Finset ι) (f : ι → Polynomial (Polynomial T)) (a : ℕ)
    (h : ∀ i ∈ s, Cdeg (f i) a) : Cdeg (∑ i ∈ s, f i) a := by
  intro n
  rw [Polynomial.finsetSum_coeff]
  exact natDegree_finset_sum_le s _ a (fun i hi => h i hi n)

lemma cdeg_prod {ι : Type*} (s : Finset ι) (f : ι → Polynomial (Polynomial T)) (a : ℕ)
    (h : ∀ i ∈ s, Cdeg (f i) a) : Cdeg (∏ i ∈ s, f i) (s.card * a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty, Finset.card_empty, Nat.zero_mul]
      intro n
      rw [Polynomial.coeff_one]
      split_ifs with hn
      · exact le_of_eq Polynomial.natDegree_one
      · exact le_of_eq Polynomial.natDegree_zero
  | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, Nat.succ_mul,
        Nat.add_comm (s.card * a) a]
      exact cdeg_mul (h i (Finset.mem_insert_self i s))
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

end

end CdegAux


namespace FrobeniusAux

/-- `X ^ #F` divides `g ^ #F - C (g.eval 0)` over a finite field `F`. -/
lemma X_pow_card_dvd_pow_sub_C {F : Type*} [Field F] [Fintype F] (g : Polynomial F) :
    Polynomial.X ^ (Fintype.card F) ∣ g ^ (Fintype.card F) - Polynomial.C (g.eval 0) := by
  set n := Fintype.card F with hn
  have h1 : g ^ n - Polynomial.C (g.eval 0)
      = Polynomial.expand F n (g - Polynomial.C (g.eval 0)) := by
    rw [map_sub, Polynomial.expand_C]
    congr 1
    rw [← FiniteField.expand_card]
  rw [h1]
  have hX : Polynomial.X ∣ g - Polynomial.C (g.eval 0) := by
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
    simp
  obtain ⟨h', hh'⟩ := hX
  rw [hh', map_mul, Polynomial.expand_X]
  exact dvd_mul_right _ _

end FrobeniusAux


namespace CdegAux

section
variable {T : Type*} [CommSemiring T]


section
variable {T : Type*} [CommRing T]

lemma cdeg_comp_C_mul_X_const {p : Polynomial (Polynomial T)} {a : ℕ} (hp : Cdeg p a)
    {d : Polynomial T} (hd : ∀ n, (d^n).natDegree ≤ 0) :
    Cdeg (p.comp (Polynomial.C d * Polynomial.X)) a := by
  intro n
  rw [GpowModXqAux.coeff_comp_C_mul_X (S := Polynomial T)]
  calc (p.coeff n * d ^ n).natDegree ≤ (p.coeff n).natDegree + (d^n).natDegree :=
        Polynomial.natDegree_mul_le
    _ ≤ a + 0 := Nat.add_le_add (hp n) (hd n)
    _ = a := Nat.add_zero a

end

end
end CdegAux

namespace Mbound

variable {F : Type*} [Field F]

end Mbound

end GpowModXqAux

open GpowModXqAux

theorem gpow_mod_Xq_indep {F : Type*} [Field F] [Fintype F] (e : ℕ) (he : 2 ≤ e)
    (hdiv : e ∣ Fintype.card F - 1) (g : Polynomial F) (hg0 : g.eval 0 ≠ 0)
    (hnd : ∀ p : ℕ, p.Prime → p ∣ e → ∀ (a : F) (h : Polynomial F),
      g ≠ Polynomial.C a * h ^ p)
    (A₀ : ℕ) (hA₀ : e * A₀ + e ^ 3 * (g.natDegree + 1) < Fintype.card F)
    (c : Fin e → Polynomial F) (hc : ∀ r, (c r).natDegree ≤ A₀)
    (h : Polynomial.X ^ Fintype.card F ∣
      ∑ r : Fin e, c r * g ^ ((r : ℕ) * ((Fintype.card F - 1) / e))) :
    ∀ r, c r = 0 := by
  classical
  set q := (Fintype.card F - 1) / e with hq
  have hqe : q * e = Fintype.card F - 1 := by rw [hq]; exact Nat.div_mul_cancel hdiv
  obtain ⟨ζ, hζ⟩ := Commons.FieldTheory.PrimitiveRoot.exists_isPrimitiveRoot_of_dvd_card_sub_one
    (F := F) (by omega) hdiv
  -- the polynomial P(T) = Σ_r c r * T^r over F[X]
  set P : Polynomial (Polynomial F) := ∑ r : Fin e, Polynomial.C (c r) * Polynomial.X ^ (r : ℕ) with hP
  have hPeval : P.eval (g ^ q) = ∑ r : Fin e, c r * g ^ ((r : ℕ) * q) := by
    rw [hP, Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro r _
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      ← pow_mul, mul_comm q (r : ℕ)]
  have hdvd : Polynomial.X ^ (Fintype.card F) ∣ P.eval (g ^ q) := by
    rw [hPeval]
    have : (∑ r : Fin e, c r * g ^ ((r : ℕ) * q))
        = ∑ r : Fin e, c r * g ^ ((r : ℕ) * ((Fintype.card F - 1) / e)) := by
      apply Finset.sum_congr rfl; intro r _; rw [hq]
    rw [this]; exact h
  -- contradiction setup
  by_contra hcontra
  push Not at hcontra
  obtain ⟨r₀, hr₀⟩ := hcontra
  have hPcoeff : P.coeff (r₀ : ℕ) = c r₀ := by
    rw [hP, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single r₀ (fun b _ hb => ?_) (fun hnot => ?_)]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      have hne : ¬ ((r₀ : ℕ) = (b : ℕ)) := fun hh => hb (Fin.ext hh).symm
      rw [if_neg hne, mul_zero]
    · exact absurd (Finset.mem_univ r₀) hnot
  have hPne : P ≠ 0 := by
    intro h0
    rw [h0] at hPcoeff
    simp only [Polynomial.coeff_zero] at hPcoeff
    exact hr₀ hPcoeff.symm
  have hPd : P.natDegree < e := by
    have hPle : P.natDegree ≤ e - 1 := by
      rw [hP, Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro m hm
      rw [Polynomial.finsetSum_coeff]
      apply Finset.sum_eq_zero
      intro r _
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      have hne : ¬ (m = (r : ℕ)) := by
        intro h
        have he1 : 0 < e := Nat.lt_of_le_of_lt (Nat.zero_le _) r.isLt
        omega
      rw [if_neg hne, mul_zero]
    omega
  -- R1 = ∏_{i<e} P(ζ^i T)
  have hζC : IsPrimitiveRoot (Polynomial.C ζ) e := hζ.map_of_injective Polynomial.C_injective
  set R1 : Polynomial (Polynomial F) := symmProd e (Polynomial.C ζ) P with hR1
  have hR1deg : R1.natDegree ≤ e * (e - 1) := by
    rw [hR1]; exact symmProd_natDegree_le (ζ := Polynomial.C ζ) P hPd
  have hR1sum : R1 = ∑ k ∈ Finset.range e,
      Polynomial.C (R1.coeff (e*k)) * Polynomial.X ^ (e*k) := by
    rw [hR1]; exact symmProd_eq_sum hζC P hPne hPd
  have hR1eval : R1.eval (g^q)
      = ∏ i ∈ Finset.range e, (P.comp (Polynomial.C ((Polynomial.C ζ)^i) * Polynomial.X)).eval (g^q) := by
    rw [hR1, symmProd, Polynomial.eval_prod]
  have hR1eval_dvd : Polynomial.X ^ (Fintype.card F) ∣ R1.eval (g^q) := by
    rw [hR1eval]
    have hmem : (0 : ℕ) ∈ Finset.range e := Finset.mem_range.mpr (by omega)
    have hd0 : (P.comp (Polynomial.C ((Polynomial.C ζ)^0) * Polynomial.X)).eval (g^q) = P.eval (g^q) := by
      congr 1
      rw [pow_zero, map_one, one_mul, Polynomial.comp_X]
    have hdvd' : Polynomial.X ^ (Fintype.card F)
        ∣ (P.comp (Polynomial.C ((Polynomial.C ζ)^0) * Polynomial.X)).eval (g^q) := by
      rw [hd0]; exact hdvd
    exact dvd_trans hdvd' (Finset.dvd_prod_of_mem _ hmem)
  have hR1eval2 : R1.eval (g^q)
      = ∑ k ∈ Finset.range e, R1.coeff (e*k) * g ^ ((Fintype.card F - 1) * k) := by
    conv_lhs => rw [hR1sum]
    rw [Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    congr 1
    rw [← pow_mul, ← mul_assoc, hqe]
  -- M
  set M : Polynomial F := ∑ k ∈ Finset.range e,
      R1.coeff (e*k) * Polynomial.C (g.eval 0) ^ k * g ^ (e - 1 - k) with hM
  -- M and its vanishing
  set M : Polynomial F := ∑ k ∈ Finset.range e,
      R1.coeff (e*k) * Polynomial.C (g.eval 0) ^ k * g ^ (e - 1 - k) with hM
  have hCdegP : CdegAux.Cdeg P A₀ := by
    rw [hP]
    apply CdegAux.cdeg_sum
    intro r _
    have h1 : CdegAux.Cdeg (Polynomial.C (c r) : Polynomial (Polynomial F)) A₀ :=
      CdegAux.cdeg_C (hc r)
    have h2 : CdegAux.Cdeg (Polynomial.X ^ (r : ℕ) : Polynomial (Polynomial F)) 0 :=
      CdegAux.cdeg_X_pow (r : ℕ) 0
    have h3 := CdegAux.cdeg_mul h1 h2
    rwa [Nat.add_zero] at h3
  have hCdegPi : ∀ i : ℕ, CdegAux.Cdeg
      (P.comp (Polynomial.C ((Polynomial.C ζ)^i) * Polynomial.X)) A₀ := by
    intro i
    apply CdegAux.cdeg_comp_C_mul_X_const hCdegP
    intro n
    rw [← pow_mul, ← Polynomial.C_pow]
    exact le_of_eq (Polynomial.natDegree_C _)
  have hCdegR1 : CdegAux.Cdeg R1 (e * A₀) := by
    rw [hR1, symmProd]
    have := CdegAux.cdeg_prod (Finset.range e)
      (fun i => P.comp (Polynomial.C ((Polynomial.C ζ)^i) * Polynomial.X)) A₀
      (fun i _ => hCdegPi i)
    simpa using this
  have hMlt : M.natDegree < Fintype.card F := by
    have hbound : M.natDegree ≤ e * A₀ + g.natDegree * (e - 1) := by
      rw [hM]
      refine CdegAux.natDegree_finset_sum_le _ _ _ (fun k hk => ?_)
      have hklt : k < e := Finset.mem_range.mp hk
      calc (R1.coeff (e*k) * Polynomial.C (g.eval 0)^k * g^(e-1-k)).natDegree
          ≤ (R1.coeff (e*k) * Polynomial.C (g.eval 0)^k).natDegree + (g^(e-1-k)).natDegree :=
            Polynomial.natDegree_mul_le
        _ ≤ ((R1.coeff (e*k)).natDegree + (Polynomial.C (g.eval 0)^k).natDegree)
              + (g^(e-1-k)).natDegree :=
            Nat.add_le_add_right Polynomial.natDegree_mul_le _
        _ ≤ (e*A₀ + 0) + g.natDegree * (e - 1) := by
            refine Nat.add_le_add (Nat.add_le_add (hCdegR1 (e*k)) ?_) ?_
            · rw [← Polynomial.C_pow]; exact le_of_eq (Polynomial.natDegree_C _)
            · calc (g^(e-1-k)).natDegree ≤ (e-1-k) * g.natDegree := Polynomial.natDegree_pow_le
                _ = g.natDegree * (e-1-k) := by rw [mul_comm]
                _ ≤ g.natDegree * (e-1) := Nat.mul_le_mul_left _ (by omega)
        _ = e * A₀ + g.natDegree * (e - 1) := by ring
    have hD : g.natDegree * (e - 1) ≤ e^3 * (g.natDegree + 1) := by
      have h1 : e - 1 ≤ e := by omega
      have h2 : e ≤ e^3 := Nat.le_self_pow (a := e) (n := 3) (by norm_num)
      calc g.natDegree * (e - 1) ≤ g.natDegree * e := Nat.mul_le_mul_left _ h1
        _ ≤ g.natDegree * e^3 := Nat.mul_le_mul_left _ h2
        _ ≤ (g.natDegree + 1) * e^3 := Nat.mul_le_mul_right _ (Nat.le_succ _)
        _ = e^3 * (g.natDegree + 1) := by ring
    omega
  have hbase : ∀ k : ℕ, Polynomial.X ^ (Fintype.card F)
      ∣ g ^ (Fintype.card F * k) - (Polynomial.C (g.eval 0))^k := by
    intro k
    have h := sub_dvd_pow_sub_pow (g ^ (Fintype.card F)) (Polynomial.C (g.eval 0)) k
    rw [show (g ^ Fintype.card F)^k = g^(Fintype.card F * k) from (pow_mul g _ k).symm] at h
    exact (FrobeniusAux.X_pow_card_dvd_pow_sub_C g).trans h
  have hterm : ∀ k ∈ Finset.range e, Polynomial.X ^ (Fintype.card F)
      ∣ R1.coeff (e*k) * (g ^ (e-1) * g ^ ((Fintype.card F - 1) * k)
          - Polynomial.C (g.eval 0)^k * g^(e-1-k)) := by
    intro k hk
    have hklt : k < e := Finset.mem_range.mp hk
    refine dvd_mul_of_dvd_right ?_ _
    have hfac : g ^ (e-1) * g ^ ((Fintype.card F - 1)*k) - Polynomial.C (g.eval 0)^k * g^(e-1-k)
        = g ^ (e-1-k) * (g^(Fintype.card F * k) - Polynomial.C (g.eval 0)^k) := by
      rw [mul_sub]
      congr 1
      · rw [← pow_add, ← pow_add, Nat.sub_one_mul]
        congr 1
        have hk1 : k ≤ (Fintype.card F) * k := Nat.le_mul_of_pos_left k Fintype.card_pos
        rw [← Nat.add_sub_assoc hk1, Nat.sub_add_comm (show k ≤ e - 1 by omega)]
      · rw [mul_comm]
    rw [hfac]
    exact dvd_mul_of_dvd_right (hbase k) _
  have hdiff : g ^ (e-1) * R1.eval (g^q) - M
      = ∑ k ∈ Finset.range e, R1.coeff (e*k) * (g ^ (e-1) * g ^ ((Fintype.card F - 1) * k)
          - Polynomial.C (g.eval 0)^k * g^(e-1-k)) := by
    rw [hM, hR1eval2, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hMdvd : Polynomial.X ^ (Fintype.card F) ∣ M := by
    have hsum := Finset.dvd_sum hterm
    rw [← hdiff] at hsum
    have : M = g^(e-1) * R1.eval (g^q) - (g^(e-1) * R1.eval (g^q) - M) := by ring
    rw [this]
    exact dvd_sub (dvd_mul_of_dvd_right hR1eval_dvd _) hsum
  have hMzero : M = 0 := by
    obtain ⟨W, hW⟩ := hMdvd
    by_contra hMne
    have hWne : W ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hW
      exact hMne hW
    have hXne : (Polynomial.X : Polynomial F) ^ (Fintype.card F) ≠ 0 :=
      pow_ne_zero _ Polynomial.X_ne_zero
    have := congrArg Polynomial.natDegree hW
    rw [Polynomial.natDegree_mul hXne hWne, Polynomial.natDegree_X_pow] at this
    omega
  -- Q and the divisibility in the fraction field
  set Q : Polynomial (Polynomial F) := ∑ k ∈ Finset.range e,
      Polynomial.C (R1.coeff (e*k)) * Polynomial.X ^ k with hQ
  have hR1Q : R1 = Q.comp (Polynomial.X ^ e) := by
    conv_lhs => rw [hR1sum]
    rw [hQ, Polynomial.sum_comp]
    apply Finset.sum_congr rfl
    intro k _
    rw [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.C_comp, Polynomial.X_comp, ← pow_mul]
  let K := FractionRing (Polynomial F)
  let yb : K := algebraMap (Polynomial F) K (Polynomial.C (g.eval 0)) / algebraMap (Polynomial F) K g
  have hgne : g ≠ 0 := by
    intro h0; rw [h0] at hg0; simpa using hg0
  have hgK : algebraMap (Polynomial F) K g ≠ 0 := by
    intro h0
    exact hgne (IsFractionRing.injective (Polynomial F) K (by simpa using h0))
  have hgy : yb * algebraMap (Polynomial F) K g
      = algebraMap (Polynomial F) K (Polynomial.C (g.eval 0)) := by
    show algebraMap (Polynomial F) K (Polynomial.C (g.eval 0)) / algebraMap (Polynomial F) K g
      * algebraMap (Polynomial F) K g = _
    rw [div_mul_cancel₀ _ hgK]
  have hQy : (Q.map (algebraMap (Polynomial F) K)).eval yb = 0 := by
    have hterm : ∀ k ∈ Finset.range e,
        (algebraMap (Polynomial F) K (R1.coeff (e*k)) * yb^k)
          * (algebraMap (Polynomial F) K g)^(e-1)
        = algebraMap (Polynomial F) K (R1.coeff (e*k))
          * (algebraMap (Polynomial F) K (Polynomial.C (g.eval 0)))^k
          * (algebraMap (Polynomial F) K g)^(e-1-k) := by
      intro k hk
      have hklt : k < e := Finset.mem_range.mp hk
      have hyk : yb^k * (algebraMap (Polynomial F) K g)^(e-1)
          = (algebraMap (Polynomial F) K (Polynomial.C (g.eval 0)))^k
            * (algebraMap (Polynomial F) K g)^(e-1-k) := by
        calc yb^k * (algebraMap (Polynomial F) K g)^(e-1)
            = yb^k * ((algebraMap (Polynomial F) K g)^k
                * (algebraMap (Polynomial F) K g)^(e-1-k)) := by
              rw [← pow_add, show k + (e - 1 - k) = e - 1 by omega]
          _ = (yb * algebraMap (Polynomial F) K g)^k
                * (algebraMap (Polynomial F) K g)^(e-1-k) := by
              rw [← mul_assoc, ← mul_pow]
          _ = (algebraMap (Polynomial F) K (Polynomial.C (g.eval 0)))^k
                * (algebraMap (Polynomial F) K g)^(e-1-k) := by
              rw [hgy]
      rw [show (algebraMap (Polynomial F) K (R1.coeff (e*k)) * yb^k)
            * (algebraMap (Polynomial F) K g)^(e-1)
          = algebraMap (Polynomial F) K (R1.coeff (e*k))
            * (yb^k * (algebraMap (Polynomial F) K g)^(e-1)) by ring, hyk]
      ring
    have hkey : (Q.map (algebraMap (Polynomial F) K)).eval yb * (algebraMap (Polynomial F) K g)^(e-1)
        = algebraMap (Polynomial F) K M := by
      simp only [hQ, hM, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
        Polynomial.map_pow, Polynomial.map_X, Polynomial.eval_finsetSum, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, map_sum, map_mul, map_pow]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun k hk => hterm k hk)
    rw [hMzero, map_zero] at hkey
    exact (mul_eq_zero.mp hkey).resolve_right (pow_ne_zero _ hgK)
  have hcomp1 : ((Q.map (algebraMap (Polynomial F) K))
        - Polynomial.C ((Q.map (algebraMap (Polynomial F) K)).eval yb)).comp (Polynomial.X ^ e)
      = R1.map (algebraMap (Polynomial F) K) := by
    rw [Polynomial.sub_comp, Polynomial.C_comp, hQy, Polynomial.C_0, sub_zero]
    rw [hR1Q, Polynomial.map_comp, Polynomial.map_pow, Polynomial.map_X]
  have hcomp2 : (Polynomial.X - Polynomial.C yb).comp (Polynomial.X ^ e : Polynomial K)
      = Polynomial.X ^ e - Polynomial.C yb := by
    rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
  have hdvdT : Polynomial.X ^ e - Polynomial.C yb ∣ R1.map (algebraMap (Polynomial F) K) := by
    have h1 : Polynomial.X - Polynomial.C yb
        ∣ (Q.map (algebraMap (Polynomial F) K))
          - Polynomial.C ((Q.map (algebraMap (Polynomial F) K)).eval yb) := by
      rw [Polynomial.dvd_iff_isRoot]
      simp [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_C]
    obtain ⟨w, hw⟩ := h1
    refine ⟨w.comp (Polynomial.X ^ e), ?_⟩
    rw [← hcomp2, ← Polynomial.mul_comp, ← hw, hcomp1]
  -- the irreducible factor
  have hinjK : Function.Injective (algebraMap (Polynomial F) K) := IsFractionRing.injective _ _
  have hPneK : P.map (algebraMap (Polynomial F) K) ≠ 0 := by
    intro h0
    exact hPne (Polynomial.map_injective _ hinjK (by simpa using h0))
  have hR1map : R1.map (algebraMap (Polynomial F) K)
      = ∏ i ∈ Finset.range e,
          (P.map (algebraMap (Polynomial F) K)).comp
            (Polynomial.C ((algebraMap F K ζ)^i) * Polynomial.X) := by
    rw [hR1, symmProd, Polynomial.map_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [Polynomial.map_comp, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
      map_pow, IsScalarTower.algebraMap_apply F (Polynomial F) K ζ]
    simp
  have hnotunit : ¬ IsUnit (Polynomial.X ^ e - Polynomial.C yb : Polynomial K) := by
    intro hu
    have h1 := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [Polynomial.natDegree_X_pow_sub_C] at h1
    omega
  have hne0 : (Polynomial.X ^ e - Polynomial.C yb : Polynomial K) ≠ 0 := by
    intro h0
    have h1 := congrArg Polynomial.natDegree h0
    rw [Polynomial.natDegree_X_pow_sub_C, Polynomial.natDegree_zero] at h1
    omega
  obtain ⟨f₀, hf₀irr, hf₀dvd⟩ := WfDvdMonoid.exists_irreducible_factor hnotunit hne0
  have hf₀dvdR1 : f₀ ∣ R1.map (algebraMap (Polynomial F) K) := dvd_trans hf₀dvd hdvdT
  rw [hR1map] at hf₀dvdR1
  obtain ⟨i, _, hf₀i⟩ := (hf₀irr.prime.dvd_finsetProd_iff _).mp hf₀dvdR1
  have hζK : IsPrimitiveRoot (algebraMap F K ζ) e :=
    hζ.map_of_injective (algebraMap F K).injective
  have hyne : yb ≠ 0 := by
    intro h0
    have := hgy
    rw [h0, zero_mul] at this
    have : algebraMap (Polynomial F) K (Polynomial.C (g.eval 0)) = 0 := this.symm
    have h2 : Polynomial.C (g.eval 0) = 0 := hinjK (by simpa using this)
    exact hg0 (Polynomial.C_eq_zero.mp h2)
  have hf₀deg : f₀.natDegree < e := by
    have hfac_ne : (P.map (algebraMap (Polynomial F) K)).comp
        (Polynomial.C ((algebraMap F K ζ)^i) * Polynomial.X) ≠ 0 := by
      intro h0
      apply hPneK
      have hζne : ζ ≠ 0 := hζ.ne_zero (by omega : e ≠ 0)
      have hζK' : algebraMap F K ζ ≠ 0 := by
        intro hc
        rw [IsScalarTower.algebraMap_apply F (Polynomial F) K ζ] at hc
        have h2 : (algebraMap F (Polynomial F)) ζ = 0 :=
          IsFractionRing.injective (Polynomial F) K (by rw [hc, map_zero])
        exact hζne (Polynomial.C_injective (by simpa using h2))
      have hainv : (Polynomial.C ((algebraMap F K ζ)^i) * Polynomial.X : Polynomial K).comp
          (Polynomial.C (((algebraMap F K ζ)^i)⁻¹) * Polynomial.X) = Polynomial.X := by
        rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp, ← mul_assoc,
          ← Polynomial.C_mul, mul_inv_cancel₀ (pow_ne_zero _ hζK'), Polynomial.C_1, one_mul]
      have := congrArg (fun r : Polynomial K =>
        r.comp (Polynomial.C (((algebraMap F K ζ)^i)⁻¹) * Polynomial.X)) h0
      rw [Polynomial.comp_assoc, hainv, Polynomial.comp_X, Polynomial.zero_comp] at this
      exact this
    have h1 : f₀.natDegree ≤ ((P.map (algebraMap (Polynomial F) K)).comp
        (Polynomial.C ((algebraMap F K ζ)^i) * Polynomial.X)).natDegree :=
      Polynomial.natDegree_le_of_dvd hf₀i hfac_ne
    have h2 : ((P.map (algebraMap (Polynomial F) K)).comp
        (Polynomial.C ((algebraMap F K ζ)^i) * Polynomial.X)).natDegree ≤ P.natDegree := by
      have hle1 : (P.map (algebraMap (Polynomial F) K)).natDegree ≤ P.natDegree :=
        Polynomial.natDegree_map_le
      have hle2 : (Polynomial.C ((algebraMap F K ζ)^i) * Polynomial.X : Polynomial K).natDegree ≤ 1 :=
        (Polynomial.natDegree_mul_le).trans (by
          rw [Polynomial.natDegree_C, Polynomial.natDegree_X])
      calc ((P.map (algebraMap (Polynomial F) K)).comp
              (Polynomial.C ((algebraMap F K ζ)^i) * Polynomial.X)).natDegree
          ≤ (P.map (algebraMap (Polynomial F) K)).natDegree
              * (Polynomial.C ((algebraMap F K ζ)^i) * Polynomial.X : Polynomial K).natDegree :=
            Polynomial.natDegree_comp_le
        _ ≤ P.natDegree * 1 := Nat.mul_le_mul hle1 hle2
        _ = P.natDegree := mul_one _
    omega
  obtain ⟨p, hpp, hpe, b, hb⟩ :=
    Commons.FieldTheory.Kummer.exists_prime_pow_of_irreducible_dvd_X_pow_sub_C
      hζK hyne hf₀irr hf₀dvd hf₀deg
  -- contradiction with hnd
  have hb2 : b ^ p * algebraMap (Polynomial F) K g = algebraMap (Polynomial F) K (Polynomial.C (g.eval 0)) := by
    rw [hb, hgy]
  obtain ⟨a, h, hgh⟩ := Commons.FieldTheory.PolyFraction.exists_const_mul_pow_of_pow_eq_div
    (g := g) hg0 (p := p) (b := b) hb2
  exact hnd p hpp hpe a h hgh

end Commons.NumberTheory.Stepanov
