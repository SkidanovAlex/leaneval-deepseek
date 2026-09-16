import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

set_option autoImplicit false

open Polynomial
open UniqueFactorizationMonoid

namespace Commons.FieldTheory.Polynomial

noncomputable section

/-- The radical of a polynomial equals the product of its distinct normalized
(monic) irreducible factors, i.e. the expression appearing in
`monic_index_ge_card_le`. -/
lemma radical_eq_toFinset_prod {F : Type*} [Field F] [DecidableEq F] (p : F[X]) :
    UniqueFactorizationMonoid.radical p = ((normalizedFactors p).toFinset.prod id : F[X]) := by
  rw [UniqueFactorizationMonoid.radical]
  rw [toFinset_normalizedFactors (a := p)]

/-- For a monic polynomial, the product of its normalized factors is itself. -/
lemma prod_normalizedFactors_of_monic {F : Type*} [Field F] [DecidableEq F] (p : F[X])
    (hp : p.Monic) : (normalizedFactors p).prod = p := by
  have h := UniqueFactorizationMonoid.prod_normalizedFactors_eq (a := p) (hp.ne_zero)
  rwa [Polynomial.Monic.normalize_eq_self hp] at h

/-- Elements of the normalized factors of a nonzero polynomial over a field are
monic irreducible polynomials. -/
lemma monic_of_mem_normalizedFactors {F : Type*} [Field F] [DecidableEq F] {p : F[X]} {q : F[X]}
    (hp : p ≠ 0) (hq : q ∈ normalizedFactors p) : q.Monic :=
  ((Polynomial.mem_normalizedFactors_iff hp).mp hq).2.1

lemma irreducible_of_mem_normalizedFactors {F : Type*} [Field F] [DecidableEq F] {p : F[X]}
    (hp : p ≠ 0) {q : F[X]} (hq : q ∈ normalizedFactors p) : Irreducible q :=
  ((Polynomial.mem_normalizedFactors_iff hp).mp hq).1

/-- Product of a multiset of monic polynomials is monic. -/
lemma multiset_prod_monic {F : Type*} [CommSemiring F] (m : Multiset (F[X]))
    (h : ∀ p ∈ m, p.Monic) : m.prod.Monic := by
  classical
  induction m using Multiset.induction_on with
  | empty => simp
  | cons p m ih =>
      have hp : p.Monic := h p (by simp)
      have hm : ∀ q ∈ m, q.Monic := fun q hq => h q (by simp [hq])
      simpa [Multiset.prod_cons] using hp.mul (ih hm)

/-- natDegree of a multiset product of monic polynomials equals the sum of the natDegrees. -/
lemma natDegree_multiset_prod_monic {F : Type*} [Field F] (m : Multiset (F[X]))
    (h : ∀ p ∈ m, p.Monic) : m.prod.natDegree = (m.map Polynomial.natDegree).sum := by
  classical
  induction m using Multiset.induction_on with
  | empty => simp
  | cons p m ih =>
      have hp : p.Monic := h p (by simp)
      have hm : ∀ q ∈ m, q.Monic := fun q hq => h q (by simp [hq])
      have hprod : m.prod.Monic := multiset_prod_monic m hm
      simp only [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons]
      rw [Polynomial.natDegree_mul hp.ne_zero hprod.ne_zero, ih hm]

/-- The radical of a monic polynomial is monic. -/
lemma radical_monic {F : Type*} [Field F] [DecidableEq F] (p : F[X]) (hp : p.Monic) :
    (UniqueFactorizationMonoid.radical p).Monic := by
  rw [radical_eq_toFinset_prod]
  rw [← Finset.prod_val]
  refine multiset_prod_monic ((normalizedFactors p).toFinset).val ?_
  intro q hq
  exact monic_of_mem_normalizedFactors hp.ne_zero (Multiset.mem_toFinset.mp hq)

/-- The radical of a polynomial divides it. -/
lemma radical_dvd {F : Type*} [Field F] [DecidableEq F] (p : F[X]) :
    UniqueFactorizationMonoid.radical p ∣ p :=
  UniqueFactorizationMonoid.radical_dvd_self

/-- natDegree of the radical is at most natDegree of the polynomial. -/
lemma natDegree_radical_le {F : Type*} [Field F] [DecidableEq F] (p : F[X]) (hp : p ≠ 0) :
    (UniqueFactorizationMonoid.radical p).natDegree ≤ p.natDegree :=
  Polynomial.natDegree_le_of_dvd (radical_dvd p) hp

/-- Cardinality of the set of distinct monic irreducible factors of a nonzero
polynomial `p` is at most `natDegree p`. -/
lemma card_normalizedFactors_toFinset_le_natDegree {F : Type*} [Field F] [DecidableEq F]
    (p : F[X]) (hp : p ≠ 0) :
    ((normalizedFactors p).toFinset.card) ≤ p.natDegree := by
  let G : Finset (F[X]) := (normalizedFactors p).toFinset
  have hmonic : ∀ g ∈ G, g.Monic := by
    intro g hg
    exact monic_of_mem_normalizedFactors hp (Multiset.mem_toFinset.mp hg)
  have hirr : ∀ g ∈ G, Irreducible g := by
    intro g hg
    exact irreducible_of_mem_normalizedFactors hp (Multiset.mem_toFinset.mp hg)
  have hprod_eq : (∏ g ∈ G, g) = UniqueFactorizationMonoid.radical p := by
    rw [radical_eq_toFinset_prod]
    rfl
  have hdeg : (∏ g ∈ G, g).natDegree = ∑ g ∈ G, g.natDegree := by
    exact Polynomial.natDegree_prod G (fun g => g) (by
      intro g hg
      exact (hmonic g hg).ne_zero)
  calc
    G.card = ∑ g ∈ G, (1 : ℕ) := by simp
    _ ≤ ∑ g ∈ G, g.natDegree := by
      apply Finset.sum_le_sum
      intro g hg
      exact Nat.succ_le_of_lt (Irreducible.natDegree_pos (hirr g hg))
    _ = (∏ g ∈ G, g).natDegree := hdeg.symm
    _ = (UniqueFactorizationMonoid.radical p).natDegree := by rw [hprod_eq]
    _ ≤ p.natDegree := natDegree_radical_le p hp

/-- Every monic irreducible factor of a monic polynomial `p` belongs to the
normalized factors of its radical. -/
lemma mem_normalizedFactors_of_radical {F : Type*} [Field F] [DecidableEq F] (p : F[X])
    (hp : p.Monic) {g : F[X]} (hg : g ∈ normalizedFactors p) :
    g ∈ normalizedFactors (UniqueFactorizationMonoid.radical p) := by
  have hg_monic : g.Monic := monic_of_mem_normalizedFactors hp.ne_zero hg
  have hg_irr : Irreducible g := irreducible_of_mem_normalizedFactors hp.ne_zero hg
  have hg_mem_set : g ∈ (normalizedFactors p).toFinset := Multiset.mem_toFinset.mpr hg
  have hg_dvd_rad : g ∣ UniqueFactorizationMonoid.radical p := by
    rw [radical_eq_toFinset_prod]
    exact Finset.dvd_prod_of_mem (fun x : F[X] => x) hg_mem_set
  exact (Polynomial.mem_normalizedFactors_iff (radical_ne_zero (a := p))).2
    ⟨hg_irr, hg_monic, hg_dvd_rad⟩

/-- Every monic irreducible factor of a monic polynomial `p` belongs to the
distinct-factor set of its radical. -/
lemma mem_toFinset_normalizedFactors_of_radical {F : Type*} [Field F] [DecidableEq F] (p : F[X])
    (hp : p.Monic) {g : F[X]} (hg : g ∈ normalizedFactors p) :
    g ∈ (normalizedFactors (UniqueFactorizationMonoid.radical p)).toFinset :=
  Multiset.mem_toFinset.mpr (mem_normalizedFactors_of_radical p hp hg)

/-- The multiplicity of any normalized factor of a monic polynomial `p` is at most
`natDegree p`. -/
lemma count_normalizedFactors_le_natDegree {F : Type*} [Field F] [DecidableEq F] (p : F[X])
    (hp : p.Monic) (g : F[X]) : (normalizedFactors p).count g ≤ p.natDegree := by
  by_cases hg : g ∈ normalizedFactors p
  · have hg_monic : g.Monic := monic_of_mem_normalizedFactors hp.ne_zero hg
    have hg_irr : Irreducible g := irreducible_of_mem_normalizedFactors hp.ne_zero hg
    let e := (normalizedFactors p).count g
    have hrep : Multiset.replicate e g ≤ normalizedFactors p := by
      exact (Multiset.le_count_iff_replicate_le (a := g) (s := normalizedFactors p) (n := e)).1
        (Nat.le_refl (Multiset.count g (normalizedFactors p)))
    have hpow_dvd : g ^ e ∣ p := by
      calc
        g ^ e = (Multiset.replicate e g).prod := by rw [Multiset.prod_replicate]
        _ ∣ (normalizedFactors p).prod := Multiset.prod_dvd_prod_of_le hrep
        _ = p := prod_normalizedFactors_of_monic p hp
    have hdegpow : (g ^ e).natDegree ≤ p.natDegree :=
      Polynomial.natDegree_le_of_dvd hpow_dvd hp.ne_zero
    have hdpos : 0 < g.natDegree := Irreducible.natDegree_pos hg_irr
    have hpow_deg : (g ^ e).natDegree = e * g.natDegree := by
      rw [Polynomial.natDegree_pow g e]
    have : e ≤ e * g.natDegree := Nat.le_mul_of_pos_right (m := g.natDegree) (n := e) hdpos
    calc
      e ≤ e * g.natDegree := this
      _ = (g ^ e).natDegree := hpow_deg.symm
      _ ≤ p.natDegree := hdegpow
  · have hz : (normalizedFactors p).count g = 0 := (Multiset.count_eq_zero).2 hg
    rw [hz]
    exact Nat.zero_le _

/-- The elements of the normalized factors of a monic polynomial are all among the
distinct factors of its radical, hence the count of any polynomial outside that set
is zero. -/
lemma count_normalizedFactors_eq_zero_of_not_mem_radical {F : Type*} [Field F] [DecidableEq F]
    (p : F[X]) (hp : p.Monic) {g : F[X]}
    (hg : g ∉ (normalizedFactors (UniqueFactorizationMonoid.radical p)).toFinset) :
    (normalizedFactors p).count g = 0 := by
  by_contra hc
  have hmem : g ∈ normalizedFactors p := (Multiset.count_pos.mp (Nat.pos_of_ne_zero hc))
  exact hg (mem_toFinset_normalizedFactors_of_radical p hp hmem)

/-- The coefficient of a finite sum of polynomials is the sum of the coefficients. -/
lemma coeff_finset_sum {F : Type*} [Semiring F] {ι : Type*} (s : Finset ι) (f : ι → F[X]) (n : ℕ) :
    (∑ i ∈ s, f i).coeff n = ∑ i ∈ s, (f i).coeff n := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a t hat ih
    rw [Finset.sum_insert hat, Polynomial.coeff_add, Finset.sum_insert hat, ih]

/-- natDegree of a sum of polynomials each with natDegree at most `t` is at most `t`. -/
lemma natDegree_finset_sum_le {F : Type*} [Semiring F] {ι : Type*} (s : Finset ι) (f : ι → F[X])
    (t : ℕ) (h : ∀ i ∈ s, (f i).natDegree ≤ t) : (∑ i ∈ s, f i).natDegree ≤ t := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_finset_sum]
  apply Finset.sum_eq_zero
  intro i hi
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (h i hi) hN)

/-- Reconstruction of the monic polynomial of degree `d` from its `d` lower
coefficients:  `X^d + c₀ + c₁X + ⋯ + c_{d-1}X^{d-1}`. -/
noncomputable def repPoly {F : Type*} [CommSemiring F] (d : ℕ) (c : Fin d → F) : F[X] :=
  X ^ d + ∑ i : Fin d, C (c i) * X ^ (i : ℕ)

/-- The sum of lower monomial terms `C (c i) * X^i` for `i < d` has natDegree at most `d - 1`. -/
lemma natDegree_sum_C_mul_X_pow_le_pred {F : Type*} [Semiring F] (d : ℕ) (c : Fin d → F) :
    (∑ i : Fin d, C (c i) * X ^ (i : ℕ)).natDegree ≤ d - 1 := by
  simpa using (natDegree_finset_sum_le (F := F) (s := (Finset.univ : Finset (Fin d)))
    (fun i => C (c i) * X ^ (i : ℕ)) (d - 1) (by
      intro i hi
      exact le_trans (Polynomial.natDegree_C_mul_X_pow_le (c i) (i : ℕ))
        (Nat.le_pred_of_lt (Fin.isLt i))))

/-- natDegree of the reconstruction is exactly `d`. -/
lemma repPoly_natDegree {F : Type*} [Field F] (d : ℕ) (c : Fin d → F) :
    (repPoly d c).natDegree = d := by
  by_cases hd : d = 0
  · subst d
    simp [repPoly]
  · unfold repPoly
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt (p := X ^ d)
      (q := ∑ i : Fin d, C (c i) * X ^ (i : ℕ))]
    · rw [Polynomial.natDegree_X_pow]
    · simpa [Polynomial.natDegree_X_pow] using
        lt_of_le_of_lt (natDegree_sum_C_mul_X_pow_le_pred d c) (Nat.sub_one_lt hd)

/-- The reconstruction is monic. -/
lemma repPoly_monic {F : Type*} [Field F] (d : ℕ) (c : Fin d → F) : (repPoly d c).Monic := by
  have hdeg := repPoly_natDegree d c
  rw [Polynomial.Monic.def, Polynomial.leadingCoeff, hdeg]
  unfold repPoly
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow_self]
  have hS0 : (∑ i : Fin d, C (c i) * X ^ (i : ℕ)).coeff d = 0 := by
    rw [coeff_finset_sum]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Polynomial.coeff_C_mul_X_pow]
    exact if_neg (by intro h_eq; exact (Nat.ne_of_lt (Fin.isLt i)) h_eq.symm)
  rw [hS0, add_zero]

/-- A monic polynomial of degree `d` equals the reconstruction of its coefficients. -/
lemma monic_eq_repPoly {F : Type*} [Field F] (p : F[X]) (hp : p.Monic) :
    p = repPoly p.natDegree (fun i : Fin p.natDegree => p.coeff (i : ℕ)) := by
  rw [repPoly]
  rw [← Finset.sum_range (fun i : ℕ => C (p.coeff i) * X ^ i)]
  exact hp.as_sum

/-- A sum over `i < d` of an expression that is nonzero only when `i = j` collapses. -/
lemma fin_sum_eq_single {F : Type*} [AddCommMonoid F] {d : ℕ} (c : Fin d → F) {j : ℕ} (hj : j < d) :
    (∑ i : Fin d, (if j = (i : ℕ) then c i else (0 : F))) = c ⟨j, hj⟩ := by
  classical
  have hsing : (∑ i : Fin d, (if j = (i : ℕ) then c i else (0 : F))) =
      (if j = ((⟨j, hj⟩ : Fin d) : ℕ) then c ⟨j, hj⟩ else (0 : F)) := by
    refine Finset.sum_eq_single (s := (Finset.univ : Finset (Fin d)))
      (f := fun b : Fin d => if j = (b : ℕ) then c b else 0) (a := (⟨j, hj⟩ : Fin d)) ?_ ?_
    · intro b hb hne
      have hbj : (b : ℕ) ≠ j := by
        intro h_eq
        exact hne (Fin.ext h_eq)
      exact if_neg (by intro h_eq; exact hbj h_eq.symm)
    · intro hmem
      exact (hmem (Finset.mem_univ _)).elim
  simpa using hsing

/-- The coefficient at `j < d` of a reconstruction is `c j`. -/
lemma repPoly_coeff {F : Type*} [Field F] (d : ℕ) (c : Fin d → F) {j : ℕ} (hj : j < d) :
    (repPoly d c).coeff j = c ⟨j, hj⟩ := by
  rw [repPoly]
  rw [Polynomial.coeff_add]
  have hXj : ((X : F[X]) ^ d).coeff j = (0 : F) := by
    rw [Polynomial.coeff_X_pow]
    exact if_neg (by omega)
  rw [hXj, zero_add]
  calc
    (∑ i : Fin d, C (c i) * X ^ (i : ℕ)).coeff j
        = ∑ i : Fin d, (C (c i) * X ^ (i : ℕ)).coeff j := by simp
    _ = ∑ i : Fin d, (if j = (i : ℕ) then c i else (0 : F)) := by
        simp
    _ = c ⟨j, hj⟩ := fin_sum_eq_single c hj

/-- Reconstructions with equal polynomials have equal coefficient vectors (same degree). -/
lemma repPoly_coeff_injective {F : Type*} [Field F] {d : ℕ} {c₁ c₂ : Fin d → F}
    (h : repPoly d c₁ = repPoly d c₂) : c₁ = c₂ := by
  funext i
  have h1 : (repPoly d c₁).coeff (i : ℕ) = c₁ i := repPoly_coeff d c₁ (Fin.isLt i)
  have h2 : (repPoly d c₂).coeff (i : ℕ) = c₂ i := repPoly_coeff d c₂ (Fin.isLt i)
  calc
    c₁ i = (repPoly d c₁).coeff (i : ℕ) := h1.symm
    _ = (repPoly d c₂).coeff (i : ℕ) := by rw [h]
    _ = c₂ i := h2

/-- Two monic polynomials with the same degree and equal coefficients below the
degree are equal. -/
lemma monic_ext {F : Type*} [Field F] {p q : F[X]} (hp : p.Monic) (hq : q.Monic)
    (hd : p.natDegree = q.natDegree) (hc : ∀ i : ℕ, i < p.natDegree → p.coeff i = q.coeff i) :
    p = q := by
  apply Polynomial.ext
  intro i
  by_cases hi : i < p.natDegree
  · exact hc i hi
  · have hge : p.natDegree ≤ i := Nat.le_of_not_gt hi
    by_cases heq : i = p.natDegree
    · subst i
      rw [Polynomial.coeff_natDegree, hp.leadingCoeff, hd]
      rw [Polynomial.coeff_natDegree, hq.leadingCoeff]
    · have hgt : p.natDegree < i := Nat.lt_of_le_of_ne hge (Ne.symm heq)
      have hgt' : q.natDegree < i := by rwa [hd] at hgt
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hgt,
        Polynomial.coeff_eq_zero_of_natDegree_lt hgt']

/-- The number of monic polynomials of degree at most `M` over a finite field with
`q` elements is at most `(M+1) * q^M`. -/
lemma monic_natDegree_le_card {F : Type*} [Field F] [Fintype F] [DecidableEq F] (M : ℕ) :
    Nat.card {p : F[X] // p.Monic ∧ p.natDegree ≤ M} ≤ (M + 1) * Fintype.card F ^ M := by
  classical
  let T := (Fin M → F) × Fin (M + 1)
  let enc : {p : F[X] // p.Monic ∧ p.natDegree ≤ M} → T :=
    fun p => ((fun i : Fin M => p.1.coeff (i : ℕ)), ⟨p.1.natDegree, Nat.lt_succ_of_le p.2.2⟩)
  have hle1 : Nat.card {p : F[X] // p.Monic ∧ p.natDegree ≤ M} ≤ Nat.card T := by
    apply Nat.card_le_card_of_injective enc
    intro p q hpq
    apply Subtype.ext
    have hd : p.1.natDegree = q.1.natDegree := by
      have h := congrArg (fun t : T => (t.2 : ℕ)) hpq
      simpa [enc] using h
    have hc : ∀ i : ℕ, i < p.1.natDegree → p.1.coeff i = q.1.coeff i := by
      intro i hi
      have hm : i < M := lt_of_lt_of_le hi p.2.2
      have h := congrArg (fun t : T => t.1 (⟨i, hm⟩ : Fin M)) hpq
      simpa [enc] using h
    exact monic_ext p.2.1 q.2.1 hd hc
  have hle2 : Nat.card ((Fin M → F) × Fin (M + 1)) = (M + 1) * Fintype.card F ^ M := by
    calc
      Nat.card ((Fin M → F) × Fin (M + 1)) = Fintype.card ((Fin M → F) × Fin (M + 1)) :=
        Nat.card_eq_fintype_card
      _ = Fintype.card (Fin M → F) * Fintype.card (Fin (M + 1)) := Fintype.card_prod _ _
      _ = Fintype.card F ^ M * (M + 1) := by
        simp [Fintype.card_fin]
      _ = (M + 1) * Fintype.card F ^ M := by rw [mul_comm]
  exact le_trans hle1 (by simpa [T] using le_of_eq hle2)

/-- The finite set of distinct monic irreducible (normalized) factors of a
polynomial. -/
def factorSet {F : Type*} [Field F] [DecidableEq F] (p : F[X]) : Finset (F[X]) :=
  (normalizedFactors p).toFinset

/-- The number of distinct factors of a nonzero polynomial is at most its degree. -/
lemma factorSet_card_le_natDegree {F : Type*} [Field F] [DecidableEq F] (p : F[X])
    (hp : p ≠ 0) : (factorSet p).card ≤ p.natDegree := by
  simpa [factorSet] using card_normalizedFactors_toFinset_le_natDegree p hp

/-- Membership in the factor set of a monic polynomial: the factors of the
polynomial are among the factors of its radical. -/
lemma mem_factorSet_radical {F : Type*} [Field F] [DecidableEq F] (p : F[X]) (hp : p.Monic)
    {g : F[X]} (hg : g ∈ normalizedFactors p) :
    g ∈ factorSet (UniqueFactorizationMonoid.radical p) := by
  unfold factorSet
  exact Multiset.mem_toFinset.mpr (mem_normalizedFactors_of_radical p hp hg)

/-- For a monic polynomial `p` whose radical is `r`, the multiplicities of the
distinct factors of `r` in `p` determine `p`. -/
lemma radical_eq_of_factors_eq {F : Type*} [Field F] [DecidableEq F] {p q : F[X]} (hp : p.Monic)
    (hq : q.Monic) {r : F[X]} (hpr : UniqueFactorizationMonoid.radical p = r)
    (hqr : UniqueFactorizationMonoid.radical q = r)
    (hc : ∀ g ∈ factorSet r, (normalizedFactors p).count g = (normalizedFactors q).count g) :
    p = q := by
  classical
  have hm : (normalizedFactors p) = (normalizedFactors q) := by
    refine (Multiset.ext (s := normalizedFactors p) (t := normalizedFactors q)).mpr ?_
    intro a
    by_cases ha : a ∈ factorSet r
    · exact hc a ha
    · have hpa : (normalizedFactors p).count a = 0 := by
        exact count_normalizedFactors_eq_zero_of_not_mem_radical p hp (g := a) (by
          simpa [factorSet, hpr] using ha)
      have hqa : (normalizedFactors q).count a = 0 := by
        exact count_normalizedFactors_eq_zero_of_not_mem_radical q hq (g := a) (by
          simpa [factorSet, hqr] using ha)
      rw [hpa, hqa]
  calc
    p = (normalizedFactors p).prod := (prod_normalizedFactors_of_monic p hp).symm
    _ = (normalizedFactors q).prod := by rw [hm]
    _ = q := prod_normalizedFactors_of_monic q hq

/-- For a fixed radical `r`, a monic degree-`n` polynomial with radical `r` is
determined by the multiplicities (capped at `n`) of the distinct factors of `r`. -/
lemma radical_fiber_card {F : Type*} [Field F] [Fintype F] [DecidableEq F] (n : ℕ) (r : F[X])
    (hr : r.Monic) (hrdeg : r.natDegree ≤ n) :
    Nat.card {f : F[X] // f.Monic ∧ f.natDegree = n ∧
        UniqueFactorizationMonoid.radical f = r} ≤ (n + 1) ^ n := by
  classical
  -- inject into functions factorSet r → Fin (n+1)
  let expFun : {f : F[X] // f.Monic ∧ f.natDegree = n ∧
        UniqueFactorizationMonoid.radical f = r} → (factorSet r → Fin (n + 1)) :=
    fun f g => ⟨(normalizedFactors f.1).count (g : F[X]),
      Nat.lt_succ_of_le ((count_normalizedFactors_le_natDegree f.1 f.2.1 (g : F[X])).trans
        (le_of_eq f.2.2.1))⟩
  have hinj : Function.Injective expFun := by
    intro f₁ f₂ h
    apply Subtype.ext
    refine radical_eq_of_factors_eq f₁.2.1 f₂.2.1 f₁.2.2.2 f₂.2.2.2 ?_
    intro g hg
    have hg1 := congrFun h ⟨g, by simpa using hg⟩
    -- hg1 : (expFun f₁ ⟨g, hg⟩).1 = (expFun f₂ ⟨g, hg⟩).1
    simpa [expFun] using hg1
  have hle1 : Nat.card {f : F[X] // f.Monic ∧ f.natDegree = n ∧
        UniqueFactorizationMonoid.radical f = r} ≤ Nat.card (factorSet r → Fin (n + 1)) :=
    Nat.card_le_card_of_injective expFun hinj
  calc
    Nat.card {f : F[X] // f.Monic ∧ f.natDegree = n ∧
        UniqueFactorizationMonoid.radical f = r} ≤ Nat.card (factorSet r → Fin (n + 1)) := hle1
    _ = Fintype.card (factorSet r → Fin (n + 1)) := Nat.card_eq_fintype_card
    _ = (n + 1) ^ (factorSet r).card := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
    _ ≤ (n + 1) ^ n := by
      apply Nat.pow_le_pow_right
      · omega
      · exact le_trans (factorSet_card_le_natDegree r hr.ne_zero) hrdeg
/-- Bound on the number of monic degree-`n` polynomials over a finite field whose
radical has degree at most `M ≤ n`. -/
lemma raddeg_le_ncard_le {F : Type*} [Field F] [Fintype F] [DecidableEq F] (n M : ℕ)
    (hMn : M ≤ n) :
    ({f : F[X] | f.Monic ∧ f.natDegree = n ∧
        (UniqueFactorizationMonoid.radical f).natDegree ≤ M} : Set (F[X])).ncard
      ≤ (n + 1) ^ (n + 1) * Fintype.card F ^ M := by
  classical
  let q := Fintype.card F
  let S : Set (F[X]) := {f | f.Monic ∧ f.natDegree = n ∧
        (UniqueFactorizationMonoid.radical f).natDegree ≤ M}
  -- Radicals: monic polynomials of degree at most M, as a type
  let RadT := {r : F[X] // r.Monic ∧ r.natDegree ≤ M}
  let Fib : RadT → Set (F[X]) := fun r =>
        {f | f.Monic ∧ f.natDegree = n ∧ UniqueFactorizationMonoid.radical f = (r : F[X])}
  -- RadT is finite (an instance used below)
  haveI hFinRadT : Finite RadT := by
    refine Finite.of_injective (fun r : RadT =>
      (((fun i : Fin M => r.1.coeff (i : ℕ)),
        ⟨r.1.natDegree, Nat.lt_succ_of_le r.2.2⟩) : (Fin M → F) × Fin (M + 1))) ?_
    intro r₁ r₂ h
    apply Subtype.ext
    have hd : r₁.1.natDegree = r₂.1.natDegree := by
      have hh := congrArg (fun t : (Fin M → F) × Fin (M + 1) => (t.2 : ℕ)) h
      simpa using hh
    have hc : ∀ i : ℕ, i < r₁.1.natDegree → r₁.1.coeff i = r₂.1.coeff i := by
      intro i hi
      have hm : i < M := lt_of_lt_of_le hi r₁.2.2
      have hh := congrArg (fun t : (Fin M → F) × Fin (M + 1) => t.1 (⟨i, hm⟩ : Fin M)) h
      simpa using hh
    exact monic_ext r₁.2.1 r₂.2.1 hd hc
  haveI hFintypeRad : Fintype RadT := Fintype.ofFinite RadT
  have hS : S = ⋃ r : RadT, Fib r := by
    ext f
    rw [Set.mem_iUnion]
    constructor
    · intro hf
      refine ⟨⟨UniqueFactorizationMonoid.radical f, ⟨radical_monic f hf.1, hf.2.2⟩⟩,
        ⟨hf.1, hf.2.1, rfl⟩⟩
    · rintro ⟨r, hfr⟩
      exact ⟨hfr.1, hfr.2.1, by
        rw [hfr.2.2]
        exact r.2.2⟩
  -- RadT is small
  have hRadCard : Fintype.card RadT ≤ (M + 1) * q ^ M := by
    have h := monic_natDegree_le_card (F := F) M
    rw [← Nat.card_eq_fintype_card]
    simpa [RadT, q] using h
  -- each fiber is finite and has at most (n+1)^n elements
  have hFibFin : ∀ r : RadT, (Fib r).Finite := by
    intro r
    let inj : ↥(Fib r) → (factorSet (r : F[X]) → Fin (n + 1)) := fun f g =>
      ⟨(normalizedFactors (f : F[X])).count (g : F[X]),
        Nat.lt_succ_of_le ((count_normalizedFactors_le_natDegree (f : F[X]) f.2.1 (g : F[X])).trans
          (le_of_eq f.2.2.1))⟩
    have hinj : Function.Injective inj := by
      intro f₁ f₂ h
      apply Subtype.ext
      refine radical_eq_of_factors_eq f₁.2.1 f₂.2.1 f₁.2.2.2 f₂.2.2.2 ?_
      intro g hg
      have hh := congrFun h ⟨g, by simpa [Fib] using hg⟩
      simpa [inj] using hh
    haveI : Finite ↥(Fib r) := Finite.of_injective inj hinj
    exact Set.toFinite (Fib r)
  have hFibBound : ∀ r : RadT, (Fib r).ncard ≤ (n + 1) ^ n := by
    intro r
    have hle := radical_fiber_card (F := F) n (r : F[X]) r.2.1 (le_trans r.2.2 hMn)
    -- (Fib r).ncard is definitionally Nat.card of the fiber subtype
    rw [show (Fib r).ncard =
        Nat.card {f : F[X] // f.Monic ∧ f.natDegree = n ∧
          UniqueFactorizationMonoid.radical f = (r : F[X])} by rfl]
    exact hle
  -- disjointness of the fibers
  have hdisj : Set.PairwiseDisjoint (Set.univ : Set RadT) Fib := by
    intro r₁ hr₁ r₂ hr₂ hne
    change Disjoint (Fib r₁) (Fib r₂)
    rw [Set.disjoint_left]
    intro f hf₁ hf₂
    apply hne
    apply Subtype.ext
    exact (hf₁.2.2.symm).trans hf₂.2.2
  -- assemble the bound
  calc
    S.ncard = (⋃ r : RadT, Fib r).ncard := by rw [hS]
    _ = (⋃ r ∈ (Set.univ : Set RadT), Fib r).ncard := by rw [Set.biUnion_univ]
    _ = ∑ᶠ (r : RadT) (_ : r ∈ (Set.univ : Set RadT)), (Fib r).ncard := by
        exact Set.Finite.ncard_biUnion (t := (Set.univ : Set RadT)) (s := Fib)
          (Set.finite_univ) (fun i hi => hFibFin i) hdisj
    _ = ∑ᶠ (r : RadT), (Fib r).ncard := by
        simp
    _ = ∑ r : RadT, (Fib r).ncard := by
        rw [finsum_eq_sum_of_fintype]
    _ ≤ ∑ r : RadT, (n + 1) ^ n := by
        exact Finset.sum_le_sum (fun r hr => hFibBound r)
    _ = Fintype.card RadT * (n + 1) ^ n := by
        simp [Finset.sum_const]
    _ ≤ ((M + 1) * q ^ M) * (n + 1) ^ n := by
        exact Nat.mul_le_mul_right _ hRadCard
    _ = (M + 1) * (q ^ M * (n + 1) ^ n) := by ring
    _ ≤ (n + 1) * (q ^ M * (n + 1) ^ n) := by
        exact Nat.mul_le_mul_right (q ^ M * (n + 1) ^ n) (by omega)
    _ = (n + 1) * (n + 1) ^ n * q ^ M := by ring
    _ = (n + 1) ^ (n + 1) * q ^ M := by
        rw [pow_succ]
        ring

/-- The number of monic degree-`n` polynomials over a finite field whose radical has
degree at most `n - k` is bounded by `2^((n+1)^4) * q^(n-k)`. -/
theorem monic_index_ge_card_le {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (n k : ℕ) (hk : k ≤ n) :
    Nat.card {f : F[X] // f.Monic ∧ f.natDegree = n ∧
        k ≤ f.natDegree - (((normalizedFactors f).toFinset.prod id : F[X]).natDegree)} ≤
      2 ^ ((n + 1) ^ 4) * Fintype.card F ^ (n - k) := by
  classical
  set M : ℕ := n - k with hMdef
  have hEq : {f : F[X] // f.Monic ∧ f.natDegree = n ∧
        k ≤ f.natDegree - (((normalizedFactors f).toFinset.prod id : F[X]).natDegree)} ≃
        {f : F[X] // f.Monic ∧ f.natDegree = n ∧
          (UniqueFactorizationMonoid.radical f).natDegree ≤ M} := by
    refine Equiv.subtypeEquivRight ?_
    intro f
    constructor
    · intro hf
      refine ⟨hf.1, hf.2.1, ?_⟩
      have hrad_le_n : (UniqueFactorizationMonoid.radical f).natDegree ≤ n := by
        have h := natDegree_radical_le f hf.1.ne_zero
        rwa [hf.2.1] at h
      have hprod : (((normalizedFactors f).toFinset.prod id : F[X]).natDegree) =
          (UniqueFactorizationMonoid.radical f).natDegree := by
        congr 1
        rw [← radical_eq_toFinset_prod f]
      have h₃ : k ≤ f.natDegree - (((normalizedFactors f).toFinset.prod id : F[X]).natDegree) :=
        hf.2.2
      rw [hf.2.1, hprod] at h₃
      rw [hMdef]
      omega
    · intro hf
      refine ⟨hf.1, hf.2.1, ?_⟩
      have hrad_le_n : (UniqueFactorizationMonoid.radical f).natDegree ≤ n := by
        have h := natDegree_radical_le f hf.1.ne_zero
        rwa [hf.2.1] at h
      have hM : (UniqueFactorizationMonoid.radical f).natDegree ≤ n - k := by
        simpa [M] using hf.2.2
      have hle' : k ≤ n - (UniqueFactorizationMonoid.radical f).natDegree := by omega
      have hprod : (((normalizedFactors f).toFinset.prod id : F[X]).natDegree) =
          (UniqueFactorizationMonoid.radical f).natDegree := by
        congr 1
        rw [← radical_eq_toFinset_prod f]
      rw [hf.2.1, hprod]
      exact hle'

  rw [Nat.card_congr hEq]
  have hb : Nat.card {f : F[X] // f.Monic ∧ f.natDegree = n ∧
        (UniqueFactorizationMonoid.radical f).natDegree ≤ M} ≤
        (n + 1) ^ (n + 1) * Fintype.card F ^ M := by
    change ({f : F[X] | f.Monic ∧ f.natDegree = n ∧
        (UniqueFactorizationMonoid.radical f).natDegree ≤ M} : Set (F[X])).ncard ≤
        (n + 1) ^ (n + 1) * Fintype.card F ^ M
    exact raddeg_le_ncard_le (F := F) n M (by simpa [M] using Nat.sub_le n k)
  have hpow : (n + 1) ^ (n + 1) ≤ 2 ^ ((n + 1) ^ 4) := by
    have h1 : n + 1 ≤ 2 ^ (n + 1) := by
      have h := (Nat.lt_two_pow_self : (n + 1) < 2 ^ (n + 1))
      omega
    have hmm : (n + 1) ^ 2 ≤ (n + 1) ^ 4 := by
      exact Nat.pow_le_pow_right (by omega : 0 < n + 1) (by omega : 2 ≤ 4)
    calc
      (n + 1) ^ (n + 1) ≤ (2 ^ (n + 1)) ^ (n + 1) := by
        exact Nat.pow_le_pow_left h1 (n + 1)
      _ = 2 ^ ((n + 1) * (n + 1)) := by rw [pow_mul]
      _ = 2 ^ ((n + 1) ^ 2) := by congr 1; ring
      _ ≤ 2 ^ ((n + 1) ^ 4) := by
        exact pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hmm
  calc
    Nat.card {f : F[X] // f.Monic ∧ f.natDegree = n ∧
        (UniqueFactorizationMonoid.radical f).natDegree ≤ M}
        ≤ (n + 1) ^ (n + 1) * Fintype.card F ^ M := hb
    _ ≤ 2 ^ ((n + 1) ^ 4) * Fintype.card F ^ M := by
      exact Nat.mul_le_mul_right _ hpow
    _ = 2 ^ ((n + 1) ^ 4) * Fintype.card F ^ (n - k) := by rw [hMdef]


end

end Commons.FieldTheory.Polynomial