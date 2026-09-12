import Mathlib
import Submission.Commons.Combinatorics.MvPolynomial.interval_convex_of_rayleigh
import Submission.Commons.Combinatorics.MvPolynomial.union_shift_mconvex
import Submission.Commons.LorentzianPolynomials.strict_subset_L

open Finsupp MvPolynomial
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Commons.Combinatorics.MvPolynomial

noncomputable section

/-- the directional-derivative polynomial -/
abbrev dd (n : ℕ) (u : Fin n → ℝ) (p : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ j : Fin n, MvPolynomial.C (u j) * MvPolynomial.pderiv j p

/-- coefficient of the directional derivative -/
lemma dd_coeff (n : ℕ) (u : Fin n → ℝ) (p : MvPolynomial (Fin n) ℝ) (m : Fin n →₀ ℕ) :
    (dd n u p).coeff m =
      ∑ j : Fin n, u j * (p.coeff (m + e j) * (((m j : ℝ) + 1))) := by
  unfold dd
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [MvPolynomial.coeff_C_mul]
  rw [MvPolynomial.coeff_pderiv]

/-- each summand in `dd_coeff` is nonnegative -/
lemma dd_coeff_nonneg (n : ℕ) (u : Fin n → ℝ) (hu : ∀ j : Fin n, 0 ≤ u j)
    (p : MvPolynomial (Fin n) ℝ) (hp : ∀ m : Fin n →₀ ℕ, 0 ≤ p.coeff m)
    (m : Fin n →₀ ℕ) : 0 ≤ (dd n u p).coeff m := by
  rw [dd_coeff]
  apply Finset.sum_nonneg
  intro j hj
  have h1 : 0 ≤ u j := hu j
  have h2 : 0 ≤ p.coeff (m + e j) := hp _
  have h3 : 0 ≤ ((m j : ℝ) + 1) := by positivity
  exact mul_nonneg h1 (mul_nonneg h2 h3)

/-! ## Set-level theory: contractions of an M-convex support -/

/-- contraction of `S` at `j`: exponents that extend by `e_j` to an element of `S` -/
abbrev contract {n : ℕ} (S : Set (Fin n →₀ ℕ)) (j : Fin n) : Set (Fin n →₀ ℕ) :=
  {m : Fin n →₀ ℕ | m + e j ∈ S}

/-- (m - e i + e l) + e j = (m + e j) - e i + e l, when m i ≥ 1 -/
lemma sub_add_add_eq (n : ℕ) (m : Fin n →₀ ℕ) (i l j : Fin n) (hmi : 1 ≤ m i) :
    (m - e i + e l) + e j = (m + e j) - e i + e l := by
  ext t
  by_cases hti : t = i <;> by_cases htj : t = j <;> by_cases htl : t = l
  all_goals
    simp_all [e, Finsupp.single_apply]
    try omega

/-- a single contraction of an M-convex set is M-convex -/
lemma contract_mconvex {n : ℕ} {S : Set (Fin n →₀ ℕ)} (hS : Commons.LorentzianPolynomials.IsMConvex S)
    (j : Fin n) : Commons.LorentzianPolynomials.IsMConvex (contract S j) := by
  unfold Commons.LorentzianPolynomials.IsMConvex
  intro m hm m' hm' i hgt
  have hmi : 1 ≤ m i := by
    have : m i > m' i := hgt
    omega
  have hx : m + e j ∈ S := hm
  have hx' : m' + e j ∈ S := hm'
  have hgtx : (m + e j) i > (m' + e j) i := by
    simp [e, Finsupp.single_apply]
    omega
  rcases hS (m + e j) hx (m' + e j) hx' i hgtx with ⟨l, hlt, hmem⟩
  refine ⟨l, ?_, ?_⟩
  · -- m l < m' l
    have hlt' : (m + e j) l < (m' + e j) l := hlt
    simp [e, Finsupp.single_apply] at hlt'
    omega
  · -- m - e i + e l ∈ contract S j
    change (m - e i + e l) + e j ∈ S
    have heq : (m - e i + e l) + e j = (m + e j) - e i + e l := sub_add_add_eq n m i l j hmi
    rw [heq]
    exact hmem

/-- an element of `S` with positive `a`-coordinate contracts into `contract S a` -/
lemma contract_sub_self {n : ℕ} {S : Set (Fin n →₀ ℕ)} (a : Fin n) {γ : Fin n →₀ ℕ}
    (hγ : γ ∈ S) (hγa : 1 ≤ γ a) : γ - e a ∈ contract S a := by
  change (γ - e a) + e a ∈ S
  have h := sub_single_add_self γ a hγa
  rwa [h]

/-- arithmetic: (m + e a) - e i + e l = (m - e i + e l) + e a when i ≠ a -/
lemma sub_add_comm_ne (n : ℕ) (m : Fin n →₀ ℕ) (a i l : Fin n) (hia : i ≠ a) :
    (m + e a) - e i + e l = (m - e i + e l) + e a := by
  ext t
  by_cases hti : t = i <;> by_cases hta : t = a <;> by_cases htl : t = l
  all_goals
    simp_all [e, Finsupp.single_apply]
    try omega
/-- generic: moving an added unit vector past a subtraction -/
lemma add_out_sub (n : ℕ) (m v : Fin n →₀ ℕ) (k w : Fin n) (hmk : 1 ≤ m k) :
    (m - e k + v) + e w = (m + e w) - e k + v := by
  ext t
  by_cases htk : t = k
  · subst t
    by_cases hwk : w = k <;> simp_all [e, Finsupp.single_apply] <;> omega
  · by_cases hwt : w = t <;> simp_all [e, Finsupp.single_apply] <;> omega

/-- (m - e i + e l) + e a = (m + e a) - e i + e l -/
lemma good_target_a (n : ℕ) (m : Fin n →₀ ℕ) (i l a : Fin n) (hmi : 1 ≤ m i) :
    (m - e i + e l) + e a = (m + e a) - e i + e l :=
  add_out_sub n m (e l) i a hmi

/-- (m - e i + e a) + e b = (m + e a) - e i + e b -/
lemma leftover_target_a (n : ℕ) (m : Fin n →₀ ℕ) (i a b : Fin n) (hmi : 1 ≤ m i) :
    (m - e i + e a) + e b = (m + e a) - e i + e b := by
  ext t
  by_cases hti : t = i <;> by_cases hta : t = a <;> by_cases htb : t = b
  all_goals
    simp_all [e, Finsupp.single_apply]
    try omega

/-- (m - e i + e q) + e b = ((m + e a) - e i + e b) - e a + e q, for i ≠ a, a ≠ b -/
lemma leftover_target_q (n : ℕ) (m : Fin n →₀ ℕ) (i a b q : Fin n) (hmi : 1 ≤ m i)
    (hia : i ≠ a) (hab : a ≠ b) :
    (m - e i + e q) + e b = ((m + e a) - e i + e b) - e a + e q := by
  ext t
  by_cases hti : t = i <;> by_cases hta : t = a <;> by_cases htb : t = b <;> by_cases htq : t = q
  all_goals
    simp_all [e, Finsupp.single_apply]
    try omega
/-- mixed exchange when the exchange coordinate differs from both witness directions -/
lemma pair_exch_out {n : ℕ} {S : Set (Fin n →₀ ℕ)}
    (hS : Commons.LorentzianPolynomials.IsMConvex S)
    {a b i : Fin n} (hia : i ≠ a) (hib : i ≠ b) (hab : a ≠ b)
    {m m' : Fin n →₀ ℕ} (hm : m ∈ contract S a) (hm' : m' ∈ contract S b)
    (hgt : m i > m' i) :
    ∃ l : Fin n, m l < m' l ∧ m - e i + e l ∈ contract S a ∪ contract S b := by
  have hmi : 1 ≤ m i := by omega
  have hx : m + e a ∈ S := hm
  have hy : m' + e b ∈ S := hm'
  have hgtx : (m + e a) i > (m' + e b) i := by
    simp [e, Finsupp.single_apply, hia, hib]
    omega
  rcases hS (m + e a) hx (m' + e b) hy i hgtx with ⟨l, hlt, hmem⟩
  by_cases hbad : l = b ∧ m b = m' b
  · rcases hbad with ⟨hlb, hmm⟩
    subst l
    by_cases hlt_a : m a < m' a
    · refine ⟨a, hlt_a, ?_⟩
      right
      change (m - e i + e a) + e b ∈ S
      rw [leftover_target_a n m i a b hmi]
      exact hmem
    · have hge : m' a ≤ m a := by omega
      have hγa : ((m + e a) - e i + e b) a > (m' + e b) a := by
        simp [e, Finsupp.single_apply, hia, hib, hab]
        omega
      rcases hS ((m + e a) - e i + e b) hmem (m' + e b) hy a hγa with ⟨q, hltq, hmemq⟩
      refine ⟨q, ?_, ?_⟩
      · have hne_a : q ≠ a := by
          intro hqa
          subst q
          simp [e, Finsupp.single_apply, hia, hib, hab] at hltq
          omega
        have hne_b : q ≠ b := by
          intro hqb
          subst q
          simp [e, Finsupp.single_apply, hia, hib, hab] at hltq
          omega
        have hne_i : q ≠ i := by
          intro hqi
          subst q
          simp [e, Finsupp.single_apply, hia, hib, hab] at hltq
          omega
        simp [e, Finsupp.single_apply, hne_a, hne_b, hne_i] at hltq
        exact hltq
      · right
        change (m - e i + e q) + e b ∈ S
        rw [leftover_target_q n m i a b q hmi hia hab]
        exact hmemq
  · refine ⟨l, ?_, ?_⟩
    · by_cases hla : l = a
      · subst l
        simp [e, Finsupp.single_apply, hia, hab] at hlt
        omega
      · by_cases hlb : l = b
        · subst l
          have hnot : ¬ m b = m' b := by
            intro h
            exact hbad ⟨rfl, h⟩
          simp [e, Finsupp.single_apply, hla] at hlt
          omega
        · simp [e, Finsupp.single_apply, hla, hlb] at hlt
          exact hlt
    · left
      change (m - e i + e l) + e a ∈ S
      rw [good_target_a n m i l a hmi]
      exact hmem
/-- mixed exchange when the exchange coordinate is the witness direction of `m'` -/
lemma pair_exch_b {n : ℕ} {S : Set (Fin n →₀ ℕ)}
    (hS : Commons.LorentzianPolynomials.IsMConvex S)
    {a b : Fin n} (hab : a ≠ b)
    {m m' : Fin n →₀ ℕ} (hm : m ∈ contract S a) (hm' : m' ∈ contract S b)
    (hgt : m b > m' b) :
    ∃ l : Fin n, m l < m' l ∧ m - e b + e l ∈ contract S a ∪ contract S b := by
  have hx : m + e a ∈ S := hm
  have hy : m' + e b ∈ S := hm'
  have hmb : 1 ≤ m b := by omega
  by_cases hbig : m' b + 2 ≤ m b
  · have hgtx : (m + e a) b > (m' + e b) b := by
      simp [e, Finsupp.single_apply, hab]
      omega
    rcases hS (m + e a) hx (m' + e b) hy b hgtx with ⟨l, hlt, hmem⟩
    refine ⟨l, ?_, ?_⟩
    · by_cases hla : l = a
      · subst l
        simp [e, Finsupp.single_apply, hab] at hlt
        omega
      · by_cases hlb : l = b
        · subst l
          simp [e, Finsupp.single_apply, hab] at hlt
          omega
        · simp [e, Finsupp.single_apply, hla, hlb] at hlt
          exact hlt
    · left
      change (m - e b + e l) + e a ∈ S
      rw [add_out_sub n m (e l) b a hmb]
      exact hmem
  · have heq : m b = m' b + 1 := by omega
    by_cases hlt_a : m a < m' a
    · refine ⟨a, hlt_a, ?_⟩
      right
      change (m - e b + e a) + e b ∈ S
      rw [add_out_sub n m (e a) b b hmb, add_sub_single m b]
      exact hx
    · have hge : m' a ≤ m a := by omega
      have hgtx_a : (m + e a) a > (m' + e b) a := by
        simp [e, Finsupp.single_apply, hab]
        omega
      rcases hS (m + e a) hx (m' + e b) hy a hgtx_a with ⟨l, hlt, hmem⟩
      refine ⟨l, ?_, ?_⟩
      · by_cases hla : l = a
        · subst l
          simp [e, Finsupp.single_apply, hab] at hlt
          omega
        · by_cases hlb : l = b
          · subst l
            simp [e, Finsupp.single_apply, hab] at hlt
            omega
          · simp [e, Finsupp.single_apply, hla, hlb] at hlt
            exact hlt
      · right
        change (m - e b + e l) + e b ∈ S
        rw [add_out_sub n m (e l) b b hmb, add_sub_single m b]
        -- now goal: m + e l ∈ S; hmem : ((m + e a) - e a) + e l ∈ S
        simpa [add_sub_single] using hmem

/-- mixed exchange when the exchange coordinate is the witness direction of `m` -/
lemma pair_exch_a {n : ℕ} {S : Set (Fin n →₀ ℕ)}
    (hS : Commons.LorentzianPolynomials.IsMConvex S)
    {a b : Fin n} (hab : a ≠ b)
    {m m' : Fin n →₀ ℕ} (hm : m ∈ contract S a) (hm' : m' ∈ contract S b)
    (hmnb : m ∉ contract S b) (hgt : m a > m' a) :
    ∃ l : Fin n, m l < m' l ∧ m - e a + e l ∈ contract S a ∪ contract S b := by
  have hx : m + e a ∈ S := hm
  have hy : m' + e b ∈ S := hm'
  have hma : 1 ≤ m a := by omega
  have hgtx : (m + e a) a > (m' + e b) a := by
    simp [e, Finsupp.single_apply, hab]
    omega
  rcases hS (m + e a) hx (m' + e b) hy a hgtx with ⟨l, hlt, hmem⟩
  by_cases hlb : l = b
  · subst l
    exfalso
    apply hmnb
    change m + e b ∈ S
    simpa [add_sub_single] using hmem
  · refine ⟨l, ?_, ?_⟩
    · by_cases hla : l = a
      · subst l
        simp [e, Finsupp.single_apply, hab] at hlt
        omega
      · simp [e, Finsupp.single_apply, hla, hlb] at hlt
        exact hlt
    · left
      change (m - e a + e l) + e a ∈ S
      rw [add_out_sub n m (e l) a a hma, add_sub_single m a]
      simpa [add_sub_single] using hmem
/-- the two-directional mixed exchange, no overlap hypotheses -/
lemma pair_exchange {n : ℕ} {S : Set (Fin n →₀ ℕ)}
    (hS : Commons.LorentzianPolynomials.IsMConvex S)
    {a b : Fin n} (hab : a ≠ b)
    {m m' : Fin n →₀ ℕ} (hm : m ∈ contract S a) (hm' : m' ∈ contract S b)
    (hmnb : m ∉ contract S b) (hm'na : m' ∉ contract S a)
    {i : Fin n} (hgt : m i > m' i) :
    ∃ l : Fin n, m l < m' l ∧ m - e i + e l ∈ contract S a ∪ contract S b := by
  by_cases hia : i = a
  · subst i
    exact pair_exch_a hS hab hm hm' hmnb hgt
  · by_cases hib : i = b
    · subst i
      exact pair_exch_b hS hab hm hm' hgt
    · exact pair_exch_out hS hia hib hab hm hm' hgt

/-- the union of two contractions of an M-convex set is M-convex -/
lemma pair_union_mconvex {n : ℕ} {S : Set (Fin n →₀ ℕ)}
    (hS : Commons.LorentzianPolynomials.IsMConvex S) {a b : Fin n} (hab : a ≠ b) :
    Commons.LorentzianPolynomials.IsMConvex (contract S a ∪ contract S b) := by
  unfold Commons.LorentzianPolynomials.IsMConvex
  intro m hm m' hm' i hgt
  rcases hm with hma | hmb
  · rcases hm' with hma' | hmb'
    · rcases (contract_mconvex hS a) m hma m' hma' i hgt with ⟨l, hlt, hmem⟩
      exact ⟨l, hlt, Or.inl hmem⟩
    · by_cases hm_b : m ∈ contract S b
      · rcases (contract_mconvex hS b) m hm_b m' hmb' i hgt with ⟨l, hlt, hmem⟩
        exact ⟨l, hlt, Or.inr hmem⟩
      · by_cases hm'_a : m' ∈ contract S a
        · rcases (contract_mconvex hS a) m hma m' hm'_a i hgt with ⟨l, hlt, hmem⟩
          exact ⟨l, hlt, Or.inl hmem⟩
        · exact pair_exchange hS hab hma hmb' hm_b hm'_a hgt
  · rcases hm' with hma' | hmb'
    · by_cases hm_a : m ∈ contract S a
      · rcases (contract_mconvex hS a) m hm_a m' hma' i hgt with ⟨l, hlt, hmem⟩
        exact ⟨l, hlt, Or.inl hmem⟩
      · by_cases hm'_b : m' ∈ contract S b
        · rcases (contract_mconvex hS b) m hmb m' hm'_b i hgt with ⟨l, hlt, hmem⟩
          exact ⟨l, hlt, Or.inr hmem⟩
        · rcases (pair_exchange hS hab.symm hmb hma' hm_a hm'_b hgt) with ⟨l, hlt, hmem⟩
          exact ⟨l, hlt, by simpa [Set.union_comm] using hmem⟩
    · rcases (contract_mconvex hS b) m hmb m' hmb' i hgt with ⟨l, hlt, hmem⟩
      exact ⟨l, hlt, Or.inr hmem⟩

/-- the set of exponents extendable to `S` in an active direction -/
abbrev dirSet {n : ℕ} (S : Set (Fin n →₀ ℕ)) (A : Fin n → Prop) : Set (Fin n →₀ ℕ) :=
  {m : Fin n →₀ ℕ | ∃ j : Fin n, A j ∧ m + e j ∈ S}

/-- the union of contractions over active directions is M-convex -/
lemma dirSet_mconvex {n : ℕ} {S : Set (Fin n →₀ ℕ)}
    (hS : Commons.LorentzianPolynomials.IsMConvex S) (A : Fin n → Prop) :
    Commons.LorentzianPolynomials.IsMConvex (dirSet S A) := by
  unfold Commons.LorentzianPolynomials.IsMConvex
  intro m hm m' hm' i hgt
  rcases hm with ⟨j, hAj, hxj⟩
  rcases hm' with ⟨j', hAj', hx'j'⟩
  by_cases hjj : j = j'
  · subst j'
    rcases (contract_mconvex hS j) m hxj m' hx'j' i hgt with ⟨l, hlt, hmem⟩
    refine ⟨l, hlt, ?_⟩
    change ∃ t : Fin n, A t ∧ (m - e i + e l) + e t ∈ S
    exact ⟨j, hAj, by simpa using hmem⟩
  · have hU : Commons.LorentzianPolynomials.IsMConvex (contract S j ∪ contract S j') :=
      pair_union_mconvex hS hjj
    unfold Commons.LorentzianPolynomials.IsMConvex at hU
    rcases hU m (Or.inl hxj) m' (Or.inr hx'j') i hgt with ⟨l, hlt, hmem⟩
    refine ⟨l, hlt, ?_⟩
    change ∃ t : Fin n, A t ∧ (m - e i + e l) + e t ∈ S
    rcases hmem with hmem_j | hmem_j'
    · exact ⟨j, hAj, by simpa using hmem_j⟩
    · exact ⟨j', hAj', by simpa using hmem_j'⟩
/-- the support of the directional derivative is the union of contractions in the active directions -/
lemma dd_support (n : ℕ) (u : Fin n → ℝ) (hu : ∀ j : Fin n, 0 ≤ u j)
    (p : MvPolynomial (Fin n) ℝ) (hp : ∀ m : Fin n →₀ ℕ, 0 ≤ p.coeff m) :
    ((dd n u p).support : Set (Fin n →₀ ℕ)) =
      dirSet (p.support : Set (Fin n →₀ ℕ)) (fun j : Fin n => u j ≠ 0) := by
  ext m
  change m ∈ (dd n u p).support ↔ ∃ j : Fin n, u j ≠ 0 ∧ m + e j ∈ (p.support : Set (Fin n →₀ ℕ))
  rw [MvPolynomial.mem_support_iff]
  rw [dd_coeff]
  constructor
  · intro hne
    rcases (Finset.exists_ne_zero_of_sum_ne_zero hne) with ⟨j, hj, hterm⟩
    refine ⟨j, ?_, ?_⟩
    · intro huj
      apply hterm
      rw [huj]
      ring
    · change m + e j ∈ p.support
      rw [MvPolynomial.mem_support_iff]
      intro hco
      apply hterm
      rw [hco]
      ring
  · intro h
    rcases h with ⟨j, huj, hco⟩
    have hc : p.coeff (m + e j) ≠ 0 := by
      change m + e j ∈ p.support at hco
      exact (MvPolynomial.mem_support_iff.mp hco)
    have hmj : ((m j : ℝ) + 1) ≠ 0 := by positivity
    have hterm : u j * (p.coeff (m + e j) * (((m j : ℝ) + 1))) ≠ 0 := by
      exact mul_ne_zero huj (mul_ne_zero hc hmj)
    by_contra hzero
    have hnf : ∀ j' : Fin n, 0 ≤ u j' * (p.coeff (m + e j') * (((m j') : ℝ) + 1)) := by
      intro j'
      have h1 : 0 ≤ u j' := hu j'
      have h2 : 0 ≤ p.coeff (m + e j') := hp _
      have h3 : 0 ≤ (((m j') : ℝ) + 1) := by positivity
      positivity
    have hz : (∑ j' ∈ (Finset.univ : Finset (Fin n)),
        u j' * (p.coeff (m + e j') * (((m j') : ℝ) + 1))) = 0 := by
      simpa using hzero
    have hall : ∀ j' ∈ (Finset.univ : Finset (Fin n)),
        u j' * (p.coeff (m + e j') * (((m j') : ℝ) + 1)) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (s := (Finset.univ : Finset (Fin n)))
        (f := fun j' : Fin n => u j' * (p.coeff (m + e j') * (((m j') : ℝ) + 1)))
        (fun i hi => hnf i)).mp hz
    exact hterm (hall j (Finset.mem_univ j))

/-- The support of a nonnegative directional derivative of a homogeneous polynomial
with nonnegative coefficients and M-convex support is again M-convex.

Concretely: if `p` has M-convex support and `u ⱼ ≥ 0`, then the support of
`Σⱼ uⱼ ∂ⱼ p` is M-convex (the union over `j` with `u ⱼ > 0` of the contractions
of the support of `p` by `eⱼ`). -/
theorem support_directionalDeriv_MConvex (n d : ℕ) (hd : 1 ≤ d)
    (p : MvPolynomial (Fin n) ℝ) (hp : p.IsHomogeneous d)
    (hnn : ∀ m : Fin n →₀ ℕ, 0 ≤ p.coeff m)
    (hM : Commons.LorentzianPolynomials.IsMConvex (p.support : Set (Fin n →₀ ℕ)))
    (u : Fin n → ℝ) (hu : ∀ j : Fin n, 0 ≤ u j) :
    Commons.LorentzianPolynomials.IsMConvex
      (((∑ j : Fin n, MvPolynomial.C (u j) * MvPolynomial.pderiv j p).support) :
        Set (Fin n →₀ ℕ)) := by
  have hset : (((∑ j : Fin n, MvPolynomial.C (u j) * MvPolynomial.pderiv j p).support) :
        Set (Fin n →₀ ℕ)) =
      dirSet (p.support : Set (Fin n →₀ ℕ)) (fun j : Fin n => u j ≠ 0) := by
    simpa [dd] using (dd_support n u hu p hnn)
  rw [hset]
  exact dirSet_mconvex hM (fun j : Fin n => u j ≠ 0)

end
end Commons.Combinatorics.MvPolynomial
