import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.BridgeDefs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.Vero.MulDefs
import Submission.Work.HP.Vero.MulMono
import Submission.Work.HP.Lat.card_Mon

/-!
# Infrastructure for counting reducible quartic forms in `5` variables

This file develops the coefficient-vector bookkeeping needed for
`Work.Q44Geom.reducible_count`.  Everything is stated for forms in `5` variables (`n + 1 = 5`),
so a coefficient vector of degree `d` is a function `Mon d 4 → R`.

Main objects:

* `polyOfR A`: the polynomial with coefficient vector `A : Mon d 4 → R` (over any commutative
  semiring `R`);
* `ofHomog`: the coefficient vector of a homogeneous polynomial;
* `wt`, `wtMon`, `wtFinsupp`: the weight of a monomial used to embed monomials into univariate
  exponents (`5 ^ i`; injective in degree `≤ 4` by base-`5` digits);
* `substQ`, `substZ`: the univariate substitution `X_i ↦ T ^ (5 ^ i)`, over `ℚ` and over `ℤ`;
* `IsMinDeg r P`: `r` is the least degree of a monomial of `P`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MvPolynomial Finset

namespace Work.Q44Geom

open Work.HP

/-! ## Coefficient vectors of forms -/

/-- The polynomial with coefficient vector `A : Mon d 4 → R`. -/
def polyOfR {d : ℕ} {R : Type*} [CommSemiring R] (A : Mon d 4 → R) : MvPolynomial (Fin 5) R :=
  ∑ m : Mon d 4, MvPolynomial.monomial m.toFinsupp (A m)

@[simp] lemma coeff_polyOfR {d : ℕ} {R : Type*} [CommSemiring R] (A : Mon d 4 → R)
    (m : Mon d 4) : (polyOfR A).coeff m.toFinsupp = A m := by
  rw [polyOfR, MvPolynomial.coeff_sum, Finset.sum_eq_single m]
  · simp [MvPolynomial.coeff_monomial]
  · intro m' _ hm'
    rw [MvPolynomial.coeff_monomial]
    split_ifs with hc
    · exact absurd (Mon_toFinsupp_injective hc) hm'
    · rfl
  · intro h; exact absurd (Finset.mem_univ m) h

lemma polyOfR_injective {d : ℕ} {R : Type*} [CommSemiring R] :
    Function.Injective (polyOfR (R := R) (d := d)) := by
  intro A B h
  funext m
  have := congrArg (fun p : MvPolynomial (Fin 5) R => p.coeff m.toFinsupp) h
  simpa using this

@[simp] lemma polyOfR_zero {d : ℕ} {R : Type*} [CommSemiring R] :
    polyOfR (0 : Mon d 4 → R) = 0 := by
  simp [polyOfR]

lemma polyOfR_eq_zero_iff {d : ℕ} {R : Type*} [CommSemiring R] (A : Mon d 4 → R) :
    polyOfR A = 0 ↔ A = 0 := by
  constructor
  · intro h
    funext m
    have := congrArg (fun p : MvPolynomial (Fin 5) R => p.coeff m.toFinsupp) h
    simpa using this
  · rintro rfl; simp

lemma polyOfR_C_mul {d : ℕ} {R : Type*} [CommSemiring R] (c : R) (A : Mon d 4 → R) :
    polyOfR (fun m => c * A m) = MvPolynomial.C c * polyOfR A := by
  rw [polyOfR, polyOfR, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => MvPolynomial.C_mul_monomial.symm

@[simp] lemma isHomogeneous_polyOfR {d : ℕ} {R : Type*} [CommSemiring R] (A : Mon d 4 → R) :
    (polyOfR A).IsHomogeneous d := by
  rw [polyOfR]
  exact MvPolynomial.IsHomogeneous.sum _ _ _
    (fun m _ => MvPolynomial.isHomogeneous_monomial (A m) (Mon_degree_toFinsupp m))

lemma formOf_eq_polyOfR {d : ℕ} (A : Mon d 4 → ℤ) :
    formOf d 4 A = polyOfR (fun m => (A m : ℚ)) := rfl

lemma polyOfR_map_intCast {d : ℕ} (A : Mon d 4 → ℤ) :
    MvPolynomial.map (Int.castRingHom ℚ) (polyOfR A) = polyOfR (fun m => (A m : ℚ)) := by
  rw [polyOfR, polyOfR, map_sum]
  exact Finset.sum_congr rfl fun m _ => MvPolynomial.map_monomial _ _ _

/-! ## The inverse direction: coefficient vectors of homogeneous polynomials -/

/-- A finitely supported exponent vector of total degree `d` gives a degree-`d` monomial. -/
def monOfFinsupp {d n : ℕ} (s : Fin (n + 1) →₀ ℕ) (h : s.degree = d) : Mon d n :=
  ⟨fun i => ⟨s i, by have h1 : s i ≤ s.degree := Finsupp.le_degree i s; omega⟩,
   by
     show ∑ i : Fin (n + 1), s i = d
     rw [← Finsupp.degree_eq_sum]
     exact h⟩

@[simp] lemma toFinsupp_monOfFinsupp {d n : ℕ} (s : Fin (n + 1) →₀ ℕ) (h : s.degree = d) :
    Mon.toFinsupp (monOfFinsupp s h) = s := by
  ext i
  rw [Mon_toFinsupp_apply]
  rfl

lemma monOfFinsupp_toFinsupp {d n : ℕ} (m : Mon d n) (h : (Mon.toFinsupp m).degree = d) :
    monOfFinsupp (Mon.toFinsupp m) h = m := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  rw [← Mon_toFinsupp_apply (monOfFinsupp (Mon.toFinsupp m) h) i,
    toFinsupp_monOfFinsupp, Mon_toFinsupp_apply]

/-- A homogeneous polynomial of degree `d` is `polyOfR` of its own coefficient vector. -/
lemma polyOfR_ofHomog {R : Type*} [CommSemiring R] {d : ℕ} {P : MvPolynomial (Fin 5) R}
    (hP : P.IsHomogeneous d) :
    polyOfR (fun m : Mon d 4 => P.coeff m.toFinsupp) = P := by
  refine MvPolynomial.ext _ _ fun s => ?_
  rw [polyOfR, MvPolynomial.coeff_sum]
  by_cases hs : s.degree = d
  · rw [Finset.sum_eq_single (monOfFinsupp s hs)]
    · simp [MvPolynomial.coeff_monomial]
    · intro m _ hm
      rw [MvPolynomial.coeff_monomial]
      split_ifs with hc
      · exfalso
        exact hm (Mon_toFinsupp_injective (by rw [hc, toFinsupp_monOfFinsupp s hs]))
      · rfl
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_zero]
    · exact (MvPolynomial.IsHomogeneous.coeff_eq_zero hP hs).symm
    · intro m _
      rw [MvPolynomial.coeff_monomial]
      split_ifs with hc
      · exfalso
        exact hs (by rw [← hc]; exact Mon_degree_toFinsupp m)
      · rfl

/-- Two homogeneous polynomials of the same degree with the same coefficient vector agree. -/
lemma polyOfR_inj_of_homog {R : Type*} [CommSemiring R] {d : ℕ} {P Q : MvPolynomial (Fin 5) R}
    (hP : P.IsHomogeneous d) (hQ : Q.IsHomogeneous d)
    (h : ∀ m : Mon d 4, P.coeff m.toFinsupp = Q.coeff m.toFinsupp) : P = Q := by
  rw [← polyOfR_ofHomog hP, ← polyOfR_ofHomog hQ]
  exact congrArg polyOfR (funext h)

/-! ## Weights and the univariate substitution -/

/-- The weight `5 ^ i` of the `i`-th variable. -/
def wt (i : Fin 5) : ℕ := 5 ^ (i : ℕ)

/-- The weighted degree `∑ i, wt i * s i` of an exponent vector. -/
def wtFinsupp (s : Fin 5 →₀ ℕ) : ℕ := ∑ i : Fin 5, wt i * s i

/-- The weighted degree of a monomial, by exponent vector. -/
def wtMon {d : ℕ} (m : Mon d 4) : ℕ := ∑ i : Fin 5, wt i * (m.1 i : ℕ)

lemma wtMon_eq_wtFinsupp {d : ℕ} (m : Mon d 4) : wtMon m = wtFinsupp m.toFinsupp := by
  simp only [wtMon, wtFinsupp, Mon_toFinsupp_apply]

lemma ofDigits_ofFn_five (n : Fin 5 → ℕ) :
    Nat.ofDigits 5 (List.ofFn n) = ∑ i : Fin 5, 5 ^ (i : ℕ) * n i := by
  simp [List.ofFn_succ, Nat.ofDigits, Fin.sum_univ_five]
  ring

lemma wt_injective {n : Fin 5 → ℕ} {n' : Fin 5 → ℕ} (h5 : ∀ i, n i < 5) (h5' : ∀ i, n' i < 5)
    (h : ∑ i : Fin 5, 5 ^ (i : ℕ) * n i = ∑ i : Fin 5, 5 ^ (i : ℕ) * n' i) : n = n' := by
  have heq : Nat.ofDigits 5 (List.ofFn n) = Nat.ofDigits 5 (List.ofFn n') := by
    rw [ofDigits_ofFn_five, ofDigits_ofFn_five]; exact h
  have h1 : ∀ l ∈ List.ofFn n, l < 5 := by
    intro l hl; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl; exact h5 i
  have h2 : ∀ l ∈ List.ofFn n', l < 5 := by
    intro l hl; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl; exact h5' i
  exact List.ofFn_inj.mp (Nat.ofDigits_inj_of_len_eq (by norm_num) (by simp) h1 h2 heq)

lemma wtMon_injective {d : ℕ} (hd : d ≤ 4) : Function.Injective (wtMon (d := d)) := by
  intro m m' h
  have hlt : ∀ i : Fin 5, (m.1 i : ℕ) < 5 := by
    intro i
    have h1 : (m.1 i : ℕ) ≤ ∑ j : Fin 5, (m.1 j : ℕ) :=
      Finset.single_le_sum (f := fun j : Fin 5 => (m.1 j : ℕ)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    have h2 : ∑ j : Fin 5, (m.1 j : ℕ) = d := m.2
    omega
  have hlt' : ∀ i : Fin 5, (m'.1 i : ℕ) < 5 := by
    intro i
    have h1 : (m'.1 i : ℕ) ≤ ∑ j : Fin 5, (m'.1 j : ℕ) :=
      Finset.single_le_sum (f := fun j : Fin 5 => (m'.1 j : ℕ)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    have h2 : ∑ j : Fin 5, (m'.1 j : ℕ) = d := m'.2
    omega
  have hh : (fun i : Fin 5 => (m.1 i : ℕ)) = (fun i : Fin 5 => (m'.1 i : ℕ)) :=
    wt_injective hlt hlt' (by simpa only [wtMon, wt] using h)
  apply Subtype.ext
  funext i
  exact Fin.ext (congrFun hh i)

/-- The univariate substitution `X_i ↦ T ^ (5 ^ i)` on integral polynomials. -/
def substZ : MvPolynomial (Fin 5) ℤ →+* Polynomial ℤ :=
  MvPolynomial.eval₂Hom (Polynomial.C : ℤ →+* Polynomial ℤ) (fun i => Polynomial.X ^ wt i)

/-- The univariate substitution `X_i ↦ T ^ (5 ^ i)` on rational polynomials. -/
def substQ : MvPolynomial (Fin 5) ℚ →+* Polynomial ℚ :=
  MvPolynomial.eval₂Hom (Polynomial.C : ℚ →+* Polynomial ℚ) (fun i => Polynomial.X ^ wt i)

lemma eval₂Hom_C_monomial {R : Type*} [CommSemiring R] (s : Fin 5 →₀ ℕ) (a : R) :
    MvPolynomial.eval₂Hom (Polynomial.C : R →+* Polynomial R) (fun i => Polynomial.X ^ wt i)
        (MvPolynomial.monomial s a)
      = Polynomial.monomial (wtFinsupp s) a := by
  have hprod : Finsupp.prod s (fun i k => ((Polynomial.X : Polynomial R) ^ wt i) ^ k)
      = (Polynomial.X : Polynomial R) ^ wtFinsupp s := by
    rw [Finsupp.prod]
    rw [show (∏ i ∈ s.support, ((Polynomial.X : Polynomial R) ^ wt i) ^ (s i))
        = ∏ i : Fin 5, ((Polynomial.X : Polynomial R) ^ wt i) ^ (s i) from
      Finset.prod_subset (f := fun i => ((Polynomial.X : Polynomial R) ^ wt i) ^ (s i))
        (Finset.subset_univ s.support) (fun i _ hi => by
          rw [Finsupp.notMem_support_iff.1 hi]; simp)]
    rw [Finset.prod_congr rfl (fun i _ => (pow_mul Polynomial.X (wt i) (s i)).symm)]
    rw [Finset.prod_pow_eq_pow_sum]
    rfl
  rw [MvPolynomial.eval₂Hom_monomial, hprod, ← Polynomial.C_mul_X_pow_eq_monomial]

lemma substZ_monomial (s : Fin 5 →₀ ℕ) (a : ℤ) :
    substZ (MvPolynomial.monomial s a) = Polynomial.monomial (wtFinsupp s) a :=
  eval₂Hom_C_monomial s a

lemma substQ_monomial (s : Fin 5 →₀ ℕ) (a : ℚ) :
    substQ (MvPolynomial.monomial s a) = Polynomial.monomial (wtFinsupp s) a :=
  eval₂Hom_C_monomial s a

lemma substZ_polyOfR {d : ℕ} (A : Mon d 4 → ℤ) :
    substZ (polyOfR A) = ∑ m : Mon d 4, Polynomial.monomial (wtMon m) (A m) := by
  rw [polyOfR, map_sum]
  exact Finset.sum_congr rfl fun m _ => by
    rw [substZ_monomial, wtMon_eq_wtFinsupp]

lemma substQ_polyOfR {d : ℕ} (A : Mon d 4 → ℚ) :
    substQ (polyOfR A) = ∑ m : Mon d 4, Polynomial.monomial (wtMon m) (A m) := by
  rw [polyOfR, map_sum]
  exact Finset.sum_congr rfl fun m _ => by
    rw [substQ_monomial, wtMon_eq_wtFinsupp]

lemma coeff_substZ_polyOfR {d : ℕ} (hd : d ≤ 4) (A : Mon d 4 → ℤ) (m : Mon d 4) :
    (substZ (polyOfR A)).coeff (wtMon m) = A m := by
  rw [substZ_polyOfR, Polynomial.finsetSum_coeff, Finset.sum_eq_single m]
  · simp [Polynomial.coeff_monomial]
  · intro m' _ hm'
    rw [Polynomial.coeff_monomial]
    split_ifs with hc
    · exact absurd (wtMon_injective hd hc) hm'
    · rfl
  · intro h; exact absurd (Finset.mem_univ m) h

lemma coeff_substQ_polyOfR {d : ℕ} (hd : d ≤ 4) (A : Mon d 4 → ℚ) (m : Mon d 4) :
    (substQ (polyOfR A)).coeff (wtMon m) = A m := by
  rw [substQ_polyOfR, Polynomial.finsetSum_coeff, Finset.sum_eq_single m]
  · simp [Polynomial.coeff_monomial]
  · intro m' _ hm'
    rw [Polynomial.coeff_monomial]
    split_ifs with hc
    · exact absurd (wtMon_injective hd hc) hm'
    · rfl
  · intro h; exact absurd (Finset.mem_univ m) h

lemma substQ_map_intCast (P : MvPolynomial (Fin 5) ℤ) :
    substQ (MvPolynomial.map (Int.castRingHom ℚ) P)
      = (substZ P).map (Int.castRingHom ℚ) := by
  have h1 : substQ (MvPolynomial.map (Int.castRingHom ℚ) P)
      = MvPolynomial.eval₂Hom
          ((Polynomial.C : ℚ →+* Polynomial ℚ).comp (Int.castRingHom ℚ))
          (fun i : Fin 5 => (Polynomial.X : Polynomial ℚ) ^ wt i) P :=
    MvPolynomial.eval₂Hom_map_hom (Int.castRingHom ℚ)
      (fun i : Fin 5 => (Polynomial.X : Polynomial ℚ) ^ wt i) (Polynomial.C) P
  have h2 : (substZ P).map (Int.castRingHom ℚ)
      = MvPolynomial.eval₂Hom
          ((Polynomial.mapRingHom (Int.castRingHom ℚ)).comp (Polynomial.C : ℤ →+* Polynomial ℤ))
          (fun i : Fin 5 => Polynomial.mapRingHom (Int.castRingHom ℚ)
            ((Polynomial.X : Polynomial ℤ) ^ wt i)) P :=
    MvPolynomial.map_eval₂Hom (Polynomial.C) _ (Polynomial.mapRingHom (Int.castRingHom ℚ)) P
  have hf : ((Polynomial.C : ℚ →+* Polynomial ℚ).comp (Int.castRingHom ℚ))
      = (Polynomial.mapRingHom (Int.castRingHom ℚ)).comp (Polynomial.C : ℤ →+* Polynomial ℤ) := by
    ext r
    simp
  have hg : (fun i : Fin 5 => (Polynomial.X : Polynomial ℚ) ^ wt i)
      = (fun i : Fin 5 => Polynomial.mapRingHom (Int.castRingHom ℚ)
          ((Polynomial.X : Polynomial ℤ) ^ wt i)) := by
    funext i
    simp
  rw [h1, h2, hf, hg]

lemma isPrimitive_substZ_polyOfR {ℓ : Mon 1 4 → ℤ} (hℓ : IsPrim ℓ) :
    (substZ (polyOfR ℓ)).IsPrimitive := by
  rw [Polynomial.isPrimitive_iff_isUnit_of_C_dvd]
  intro r hr
  rw [Polynomial.C_dvd_iff_dvd_coeff] at hr
  have h1 : r ∣ Finset.univ.gcd ℓ :=
    Finset.dvd_gcd fun m _ => by
      have h2 := hr (wtMon m)
      rw [coeff_substZ_polyOfR (by norm_num) ℓ m] at h2
      exact h2
  rw [show Finset.univ.gcd ℓ = 1 from hℓ] at h1
  exact isUnit_of_dvd_one h1

/-! ## Minimal degrees -/

/-- `IsMinDeg r P` says that `r` is the least degree of a monomial occurring in `P`
(and that such a monomial exists). -/
def IsMinDeg {R : Type*} [CommSemiring R] (r : ℕ) (P : MvPolynomial (Fin 5) R) : Prop :=
  (∃ t ∈ P.support, t.degree = r) ∧ (∀ t ∈ P.support, r ≤ t.degree)

lemma exists_isMinDeg {R : Type*} [CommSemiring R] (P : MvPolynomial (Fin 5) R) (hP : P ≠ 0) :
    ∃ r, IsMinDeg r P := by
  have hne : P.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr fun h => hP (by
    rw [MvPolynomial.as_sum P, h]; simp)
  let F : Finset ℕ := P.support.image (fun t : Fin 5 →₀ ℕ => t.degree)
  have hFne : F.Nonempty := hne.image _
  refine ⟨F.min' hFne, ?_, ?_⟩
  · obtain ⟨t, ht, hts⟩ := Finset.mem_image.mp (Finset.min'_mem F hFne)
    exact ⟨t, ht, hts⟩
  · intro t ht
    exact Finset.min'_le F t.degree (Finset.mem_image.mpr ⟨t, ht, rfl⟩)

lemma IsMinDeg.ne_zero {R : Type*} [CommSemiring R] {r : ℕ} {P : MvPolynomial (Fin 5) R}
    (h : IsMinDeg r P) : P ≠ 0 := by
  intro h0
  rw [h0] at h
  obtain ⟨t, ht, _⟩ := h.1
  simpa using ht

lemma IsMinDeg.coeff_ne_zero {R : Type*} [CommSemiring R] {r : ℕ} {P : MvPolynomial (Fin 5) R}
    (h : IsMinDeg r P) : (MvPolynomial.homogeneousComponent r P) ≠ 0 := by
  obtain ⟨t, ht, htr⟩ := h.1
  intro h0
  have h1 : (MvPolynomial.homogeneousComponent r P).coeff t = 0 := by rw [h0]; simp
  rw [MvPolynomial.coeff_homogeneousComponent, if_pos htr] at h1
  exact (MvPolynomial.mem_support_iff.mp ht) h1

/-- The product of the lowest-degree homogeneous parts of two nonzero polynomials is the
lowest-degree part of their product. -/
lemma homogeneousComponent_mul_of_minDeg {R : Type*} [CommSemiring R]
    {a b : MvPolynomial (Fin 5) R} {r s : ℕ} (ha : IsMinDeg r a) (hb : IsMinDeg s b) :
    MvPolynomial.homogeneousComponent (r + s) (a * b)
      = MvPolynomial.homogeneousComponent r a * MvPolynomial.homogeneousComponent s b := by
  refine MvPolynomial.ext _ _ fun T => ?_
  rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_mul, MvPolynomial.coeff_mul]
  by_cases hT : T.degree = r + s
  · rw [if_pos hT]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' : x.1 + x.2 = T := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    have hdeg : x.1.degree + x.2.degree = r + s := by
      rw [← hT, ← hx', map_add]
    rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_homogeneousComponent]
    by_cases h1 : a.coeff x.1 = 0
    · simp [h1]
    · by_cases h2 : b.coeff x.2 = 0
      · simp [h2]
      · have hx1 : x.1 ∈ a.support := MvPolynomial.mem_support_iff.mpr h1
        have hge1 : r ≤ x.1.degree := ha.2 x.1 hx1
        have hx2 : x.2 ∈ b.support := MvPolynomial.mem_support_iff.mpr h2
        have hge2 : s ≤ x.2.degree := hb.2 x.2 hx2
        have e1 : x.1.degree = r := by omega
        have e2 : x.2.degree = s := by omega
        rw [if_pos e1, if_pos e2]
  · rw [if_neg hT]
    have hzero : (∑ x ∈ Finset.HasAntidiagonal.antidiagonal T,
        (MvPolynomial.homogeneousComponent r a).coeff x.1
          * (MvPolynomial.homogeneousComponent s b).coeff x.2) = 0 := by
      rw [Finset.sum_eq_zero]
      intro x hx
      have hx' : x.1 + x.2 = T := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
      have hdeg : x.1.degree + x.2.degree = T.degree := by rw [← hx', map_add]
      rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_homogeneousComponent]
      by_cases h1 : x.1.degree = r
      · have h2 : x.2.degree ≠ s := by omega
        rw [if_pos h1, if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]
    rw [hzero]

end Work.Q44Geom
