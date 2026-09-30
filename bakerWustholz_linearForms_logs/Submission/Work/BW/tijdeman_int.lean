import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.auxpolydefs
import Submission.Work.BW.ulcm_le_four_pow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Tijdeman's integrality lemma

For integers `x`, `k l m ≥ 0` the number
`u(k)^m · Θ(x;k,l,m)`, with `u(k) = lcm(1,…,k)` and
`Θ(x;k,l,m) = (1/m!)(d/dx)^m Δ(x;k)^l`, `Δ(x;k) = binom(x+k,k)`, is an integer.
This is the `q = 1`, `x ∈ ℤ` case of the integrality statement in Baker–Wüstholz §12
(see Tijdeman).

We prove it by reducing to the `l = 1` case with the Hasse–Leibniz rule, and then
establishing the `l = 1` statement
`k! ∣ u(k)^j · ∑_{t ∈ powersetCard (k-j) (range k)} ∏_{i∈t}(x+i+1)`
by a `p`-adic counting argument.
-/

namespace Work.BW

open Polynomial Finset

/-! ## `p`-adic valuation helpers -/

/-- `padicValRat p (z : ℚ)` is the `p`-adic valuation of `(z.natAbs).factorization p`. -/
lemma padicValRat_int_eq_factorization {p : ℕ} (hp : p.Prime) (z : ℤ) :
    padicValRat p (z : ℚ) = (((z.natAbs).factorization p : ℕ) : ℤ) := by
  have h : padicValRat p (z : ℚ) = ((padicValNat p z.natAbs : ℕ) : ℤ) := by
    rw [padicValRat.of_int]
    rfl
  rw [h, ← Nat.factorization_def _ hp]

/-- `p^s ∣ z.natAbs` iff the integer `p^s` divides `z`. -/
lemma pow_dvd_natAbs_iff {p s : ℕ} {z : ℤ} :
    p ^ s ∣ z.natAbs ↔ ((p ^ s : ℕ) : ℤ) ∣ z := by
  constructor
  · intro h
    have h' : ((p ^ s : ℕ) : ℤ) ∣ ((z.natAbs : ℕ) : ℤ) := by exact_mod_cast h
    rwa [Int.dvd_natAbs] at h'
  · intro h
    have h' : ((p ^ s : ℕ) : ℤ) ∣ ((z.natAbs : ℕ) : ℤ) := by
      rw [Int.dvd_natAbs]; exact h
    exact_mod_cast h'

/-- For `0 < n ≤ S`, `(n.factorization p : ℤ)` counts the `s ∈ {1,…,S}` with `p^s ∣ n`. -/
lemma factorization_eq_sum_ite {p : ℕ} (hp : p.Prime) {n S : ℕ} (hn : 0 < n) (hS : n ≤ S) :
    ((n.factorization p : ℕ) : ℤ)
      = ∑ s ∈ Finset.Icc 1 S, (if p ^ s ∣ n then (1 : ℤ) else 0) := by
  have h1 : ((n.factorization p : ℕ) : ℤ)
      = ∑ s ∈ Finset.Ico 1 n, (if p ^ s ∣ n then (1 : ℤ) else 0) := by
    rw [Nat.factorization_eq_card_pow_dvd _ hp, Finset.card_filter]
    push_cast
    rfl
  rw [h1]
  refine Finset.sum_subset ?_ ?_
  · intro y hy
    simp only [Finset.mem_Ico] at hy
    simp only [Finset.mem_Icc]
    omega
  · intro y hyS hy1
    simp only [Finset.mem_Icc] at hyS
    simp only [Finset.mem_Ico, not_and] at hy1
    have hyx : n ≤ y := by
      have := hy1 hyS.1
      omega
    rw [if_neg]
    intro hdiv
    have hle : p ^ y ≤ n := Nat.le_of_dvd hn hdiv
    have hlt : y < p ^ y := Nat.lt_pow_self (a := p) (n := y) hp.one_lt
    omega

/-- `padicValRat p` is additive over finite products of nonzero rationals. -/
lemma padicValRat_prod_finset {ι : Type*} {p : ℕ} [Fact p.Prime] (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValRat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat p (f i) := by
  classical
  have key : ∀ s : Finset ι, (∀ i ∈ s, f i ≠ 0) →
      padicValRat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat p (f i) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro _
      simp
    · intro a s' ha ih hf
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        padicValRat.mul (hf a (Finset.mem_insert_self a s'))
          (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
        ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]
  exact key s hf

/-- The ultrametric lower bound for finite sums: if every term has valuation at least `B`, so does
the sum (when the sum is nonzero). -/
lemma le_padicValRat_sum_finset {ι : Type*} {p : ℕ} [Fact p.Prime] {s : Finset ι} {f : ι → ℚ}
    {B : ℤ} (h : ∀ i ∈ s, B ≤ padicValRat p (f i)) (hne : (∑ i ∈ s, f i) ≠ 0) :
    B ≤ padicValRat p (∑ i ∈ s, f i) := by
  classical
  have key : ∀ s : Finset ι, (∀ i ∈ s, B ≤ padicValRat p (f i)) →
      (∑ i ∈ s, f i) ≠ 0 → B ≤ padicValRat p (∑ i ∈ s, f i) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro _ hne
      exact absurd rfl hne
    · intro a s' ha ih hsum hne
      rw [Finset.sum_insert ha] at hne ⊢
      by_cases hs : (∑ i ∈ s', f i) = 0
      · rw [hs, add_zero]
        exact hsum a (Finset.mem_insert_self a s')
      · have hB : B ≤ padicValRat p (∑ i ∈ s', f i) :=
          ih (fun i hi => hsum i (Finset.mem_insert_of_mem hi)) hs
        exact le_trans (le_min (hsum a (Finset.mem_insert_self a s')) hB)
          (padicValRat.min_le_padicValRat_add hne)
  exact key s h hne

/-- Among `k` consecutive integers at least `k/m` are divisible by `m`. -/
lemma card_multiples_shift (k m : ℕ) (hm : 0 < m) (c : ℤ) :
    k / m ≤ ((Finset.range k).filter (fun i : ℕ => (m : ℤ) ∣ c + (i : ℤ))).card := by
  classical
  set r : ℤ := (-c) % (m : ℤ) with hr
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (by exact_mod_cast hm.ne')
  have hrm : r < (m : ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast hm)
  have hdvd : (m : ℤ) ∣ c + r := by
    have h : (-c) = (m : ℤ) * ((-c) / (m : ℤ)) + r := by
      rw [hr]
      exact (Int.mul_ediv_add_emod (-c) (m : ℤ)).symm
    have h2 : c + r = -((m : ℤ) * ((-c) / (m : ℤ))) := by linarith
    rw [h2]
    exact dvd_neg.mpr (dvd_mul_right _ _)
  set rN : ℕ := r.toNat with hrN
  have hrNcast : (rN : ℤ) = r := Int.toNat_of_nonneg hr0
  have hrNlt : rN < m := by omega
  set φ : ℕ → ℕ := fun j => j * m + rN with hφ
  have hφinj : Function.Injective φ := by
    intro a b hab
    simp only [hφ] at hab
    exact Nat.eq_of_mul_eq_mul_right hm (Nat.add_right_cancel hab)
  have hsub : (Finset.range (k / m)).image φ
      ⊆ (Finset.range k).filter (fun i : ℕ => (m : ℤ) ∣ c + (i : ℤ)) := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨j, hj, rfl⟩ := hy
    rw [Finset.mem_range] at hj
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, ?_⟩
    · have hj1 : j + 1 ≤ k / m := by omega
      have h2 : (j + 1) * m ≤ k :=
        le_trans (Nat.mul_le_mul_right m hj1) (Nat.div_mul_le_self k m)
      have h3 : j * m + m ≤ k := by
        have : (j + 1) * m = j * m + m := by ring
        omega
      simp only [hφ]
      omega
    · have hcast : ((φ j : ℕ) : ℤ) = (j : ℤ) * (m : ℤ) + r := by
        simp only [hφ]
        push_cast [hrNcast]
        ring
      rw [hcast]
      have h2 : c + ((j : ℤ) * (m : ℤ) + r) = (c + r) + (j : ℤ) * (m : ℤ) := by ring
      rw [h2]
      exact dvd_add hdvd (dvd_mul_left _ _)
  calc k / m = ((Finset.range (k / m)).image φ).card := by
        rw [Finset.card_image_of_injective _ hφinj, Finset.card_range]
    _ ≤ _ := Finset.card_le_card hsub

/-! ## The subset-sum of `k` consecutive integers -/

/-- `Hj x k j = ∑_{t ⊆ {0,…,k-1}, #t = k-j} ∏_{i∈t} (x+i+1) = e_{k-j}(x+1,…,x+k)`. -/
noncomputable def Hj (x : ℤ) (k j : ℕ) : ℤ :=
  ∑ t ∈ (Finset.range k).powersetCard (k - j), ∏ i ∈ t, (x + (i : ℤ) + 1)

/-- The `p`-adic level-sum lower bound for a product over a subset of a family of nonzero
integers, from lower bounds on the number of elements divisible by each `p^s`. -/
lemma level_sum_le {ι : Type*} [DecidableEq ι] (u : Finset ι) (b : ι → ℤ)
    (hb : ∀ i ∈ u, b i ≠ 0) {p : ℕ} (hp : p.Prime) (C : ℕ → ℕ) (e j : ℕ)
    (hcount : ∀ s ∈ Finset.Icc 1 e, C s ≤ (u.filter (fun i => ((p ^ s : ℕ) : ℤ) ∣ b i)).card)
    (t : Finset ι) (ht : t ⊆ u) (htc : t.card + j = u.card) :
    (∑ s ∈ Finset.Icc 1 e, max ((C s : ℤ) - (j : ℤ)) 0)
      ≤ ∑ i ∈ t, padicValRat p ((b i : ℤ) : ℚ) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hcount' : ∀ s ∈ Finset.Icc 1 e,
      C s ≤ (u.filter (fun i => p ^ s ∣ (b i).natAbs)).card := by
    intro s hs
    refine le_trans (hcount s hs) (le_of_eq ?_)
    congr 1
    ext i
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rwa [pow_dvd_natAbs_iff]⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rwa [← pow_dvd_natAbs_iff]⟩
  set S : ℕ := e + u.sup (fun i => (b i).natAbs) + 1 with hS
  have hleS : ∀ i ∈ u, (b i).natAbs ≤ S := by
    intro i hi
    have := Finset.le_sup (f := fun i => (b i).natAbs) hi
    omega
  have heS : e ≤ S := by omega
  have hgc : ∀ s, (∑ i ∈ t, (if p ^ s ∣ (b i).natAbs then (1 : ℤ) else 0))
      = ((t.filter (fun i => p ^ s ∣ (b i).natAbs)).card : ℤ) := by
    intro s
    have hcast : (∑ i ∈ t, (if p ^ s ∣ (b i).natAbs then (1 : ℤ) else 0))
        = ((∑ i ∈ t, (if p ^ s ∣ (b i).natAbs then (1 : ℕ) else 0) : ℕ) : ℤ) := by
      push_cast
      rfl
    rw [hcast, ← Finset.card_filter]
  have hlev : ∀ i ∈ t, (∑ s ∈ Finset.Icc 1 S, (if p ^ s ∣ (b i).natAbs then (1 : ℤ) else 0))
      = padicValRat p ((b i : ℤ) : ℚ) := by
    intro i hi
    rw [padicValRat_int_eq_factorization hp,
      factorization_eq_sum_ite hp (by simpa [Int.natAbs_ne_zero] using hb i (ht hi))
        (hleS i (ht hi))]
  have hper : ∀ s ∈ Finset.Icc 1 e, max ((C s : ℤ) - (j : ℤ)) 0
      ≤ ∑ i ∈ t, (if p ^ s ∣ (b i).natAbs then (1 : ℤ) else 0) := by
    intro s hs
    have h1 : C s ≤ (t.filter (fun i => p ^ s ∣ (b i).natAbs)).card + j := by
      have h2 := hcount' s hs
      have h3 : (u.filter (fun i => p ^ s ∣ (b i).natAbs)).card
          ≤ (t.filter (fun i => p ^ s ∣ (b i).natAbs)).card + (u \ t).card := by
        have hdisj : Disjoint (t.filter (fun i => p ^ s ∣ (b i).natAbs))
            ((u \ t).filter (fun i => p ^ s ∣ (b i).natAbs)) := by
          rw [Finset.disjoint_left]
          intro x hx1 hx2
          simp only [Finset.mem_filter] at hx1 hx2
          exact (Finset.mem_sdiff.mp hx2.1).2 hx1.1
        have hun : u.filter (fun i => p ^ s ∣ (b i).natAbs)
            = (t.filter (fun i => p ^ s ∣ (b i).natAbs))
              ∪ ((u \ t).filter (fun i => p ^ s ∣ (b i).natAbs)) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_union]
          constructor
          · intro hx
            by_cases hxt : x ∈ t
            · exact Or.inl ⟨hxt, hx.2⟩
            · exact Or.inr ⟨Finset.mem_sdiff.mpr ⟨hx.1, hxt⟩, hx.2⟩
          · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
            · exact ⟨ht h1, h2⟩
            · exact ⟨(Finset.mem_sdiff.mp h1).1, h2⟩
        rw [hun, Finset.card_union_of_disjoint hdisj]
        exact Nat.add_le_add_left (Finset.card_filter_le _ _) _
      have h4 : (u \ t).card = j := by
        rw [Finset.card_sdiff_of_subset ht]
        omega
      omega
    rw [hgc s]
    have h5 : ((C s : ℤ) - (j : ℤ))
        ≤ ((t.filter (fun i => p ^ s ∣ (b i).natAbs)).card : ℤ) := by omega
    exact max_le h5 (by positivity)
  have hstep1 : (∑ s ∈ Finset.Icc 1 e, max ((C s : ℤ) - (j : ℤ)) 0)
      ≤ ∑ s ∈ Finset.Icc 1 e,
          ∑ i ∈ t, (if p ^ s ∣ (b i).natAbs then (1 : ℤ) else 0) :=
    Finset.sum_le_sum hper
  have hstep2 : (∑ s ∈ Finset.Icc 1 e,
        ∑ i ∈ t, (if p ^ s ∣ (b i).natAbs then (1 : ℤ) else 0))
      ≤ ∑ s ∈ Finset.Icc 1 S,
          ∑ i ∈ t, (if p ^ s ∣ (b i).natAbs then (1 : ℤ) else 0) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right heS)
      (fun s _ _ => by rw [hgc s]; positivity)
  have hstep3 : (∑ s ∈ Finset.Icc 1 S,
        ∑ i ∈ t, (if p ^ s ∣ (b i).natAbs then (1 : ℤ) else 0))
      = ∑ i ∈ t, padicValRat p ((b i : ℤ) : ℚ) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi => ?_
    exact hlev i hi
  linarith [hstep1, hstep2, hstep3]

/-! ## The value formula for `hasseDeriv` of `deltaPoly` -/

lemma taylor_deltaPoly (k : ℕ) (x : ℤ) :
    Polynomial.taylor (x : ℚ) (deltaPoly k)
      = ((k.factorial : ℚ)⁻¹) • ∏ i ∈ Finset.range k,
          (Polynomial.X + Polynomial.C ((x : ℚ) + ((i : ℚ) + 1))) := by
  unfold deltaPoly
  rw [Polynomial.taylor_apply]
  simp only [Polynomial.smul_eq_C_mul]
  rw [Polynomial.C_mul_comp, Polynomial.prod_comp]
  refine congrArg (fun z : Polynomial ℚ => Polynomial.C ((k.factorial : ℚ)⁻¹) * z) ?_
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp, add_assoc, ← Polynomial.C_add]

theorem aeval_hasseDeriv_deltaPoly (k j : ℕ) (hjk : j ≤ k) (x : ℤ) :
    Polynomial.aeval (x : ℚ) (Polynomial.hasseDeriv j (deltaPoly k))
      = ((Hj x k j : ℤ) : ℚ) / ((k.factorial : ℚ)) := by
  have hcoeff : (Polynomial.taylor (x : ℚ) (deltaPoly k)).coeff j
      = ((k.factorial : ℚ)⁻¹) * ((Hj x k j : ℤ) : ℚ) := by
    rw [taylor_deltaPoly, Polynomial.coeff_smul,
      Finset.prod_X_add_C_coeff _ _ (by simpa using hjk), Finset.card_range]
    unfold Hj
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    refine Finset.prod_congr rfl fun i _ => ?_
    ring
  rw [Polynomial.coe_aeval_eq_eval, ← Polynomial.taylor_coeff (x : ℚ) (deltaPoly k) j,
    hcoeff, div_eq_inv_mul]

/-! ## The `l = 1` integrality core -/

theorem tijdeman_core (k j : ℕ) (hjk : j ≤ k) (x : ℤ) :
    (k.factorial : ℤ) ∣ (ulcm k : ℤ)^j * Hj x k j := by
  classical
  rcases k with _ | k
  · have hj0 : j = 0 := by omega
    subst hj0
    simp [Hj]
  · by_cases hH : Hj x (k+1) j = 0
    · rw [hH, mul_zero]; exact dvd_zero _
    · rw [← Int.natAbs_dvd_natAbs]
      simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
      have hn : ulcm (k+1) ^ j * (Hj x (k+1) j).natAbs ≠ 0 :=
        Nat.mul_ne_zero (pow_ne_zero _ (ulcm_ne_zero (k+1))) (Int.natAbs_ne_zero.mpr hH)
      refine (Nat.factorization_prime_le_iff_dvd (Nat.factorial_ne_zero (k+1)) hn).mp ?_
      intro p hp
      haveI : Fact p.Prime := ⟨hp⟩
      rw [Nat.factorization_mul (pow_ne_zero _ (ulcm_ne_zero (k+1)))
          (Int.natAbs_ne_zero.mpr hH),
        Nat.factorization_pow]
      simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, ulcm_factorization (k+1) hp]
      have hmain : (((k+1).factorial).factorization p : ℤ)
          ≤ (j : ℤ) * (Nat.log p (k+1) : ℤ)
            + (((Hj x (k+1) j).natAbs).factorization p : ℤ) := by
        have hset : Finset.Ico 1 (Nat.log p (k+1) + 1) = Finset.Icc 1 (Nat.log p (k+1)) := by
          ext y
          simp only [Finset.mem_Ico, Finset.mem_Icc, Nat.lt_succ_iff]
        have hfac : (((k+1).factorial).factorization p : ℤ)
            = ∑ s ∈ Finset.Icc 1 (Nat.log p (k+1)), (((k+1) / p ^ s : ℕ) : ℤ) := by
          have h := Nat.factorization_factorial hp (n := k+1)
            (b := Nat.log p (k+1) + 1) (by omega)
          rw [h, hset]
          push_cast
          rfl
        have hU : (∑ s ∈ Finset.Icc 1 (Nat.log p (k+1)),
              max ((((k+1) / p ^ s : ℕ) : ℤ) - (j : ℤ)) 0)
            ≤ (((Hj x (k+1) j).natAbs).factorization p : ℤ) := by
          rw [← padicValRat_int_eq_factorization hp (Hj x (k+1) j)]
          by_cases hzero : ∃ i ∈ Finset.range (k+1), x + (i : ℤ) + 1 = 0
          · obtain ⟨i0, hi0, hi0z⟩ := hzero
            have hi0' : i0 < k+1 := Finset.mem_range.mp hi0
            have hj1 : 1 ≤ j := by
              by_contra hcon
              have hj0 : j = 0 := by omega
              exact hH (by
                rw [hj0, Hj, Nat.sub_zero]
                have hps : (Finset.range (k+1)).powersetCard (k+1)
                    = {Finset.range (k+1)} := by
                  have h := Finset.powersetCard_self (Finset.range (k+1))
                  rwa [Finset.card_range] at h
                rw [hps, Finset.sum_singleton]
                exact Finset.prod_eq_zero hi0 hi0z)
            set u : Finset ℕ := (Finset.range (k+1)).erase i0 with hu
            have hbu : ∀ i ∈ u, x + (i : ℤ) + 1 ≠ 0 := by
              intro i hi
              have hi' := (Finset.mem_erase.mp hi).1
              intro h
              exact hi' (by omega)
            have hHj : Hj x (k+1) j
                = ∑ t ∈ u.powersetCard (k+1 - j), ∏ i ∈ t, (x + (i : ℤ) + 1) := by
              rw [Hj]
              refine (Finset.sum_subset ?_ ?_).symm
              · intro t ht
                exact Finset.powersetCard_mono (Finset.erase_subset _ _) ht
              · intro t ht htu
                have ht2 : t ⊆ Finset.range (k+1) := (Finset.mem_powersetCard.mp ht).1
                have hex : ∃ i ∈ t, i = i0 := by
                  by_contra hcon
                  push_neg at hcon
                  exact htu (Finset.mem_powersetCard.mpr
                    ⟨fun i hi => Finset.mem_erase.mpr ⟨hcon i hi, ht2 hi⟩,
                      (Finset.mem_powersetCard.mp ht).2⟩)
                obtain ⟨i, hit, rfl⟩ := hex
                exact Finset.prod_eq_zero hit hi0z
            have hcount : ∀ s ∈ Finset.Icc 1 (Nat.log p (k+1)), (k+1) / p ^ s - 1
                ≤ (u.filter (fun i : ℕ => ((p ^ s : ℕ) : ℤ) ∣ x + (i : ℤ) + 1)).card := by
              intro s hs
              have hcs := card_multiples_shift (k+1) (p ^ s) (Nat.pow_pos (n := s) hp.pos) (x + 1)
              have hfilt : (Finset.range (k+1)).filter
                    (fun i : ℕ => ((p ^ s : ℕ) : ℤ) ∣ (x + 1) + (i : ℤ))
                  = (Finset.range (k+1)).filter
                    (fun i : ℕ => ((p ^ s : ℕ) : ℤ) ∣ x + (i : ℤ) + 1) := by
                refine Finset.filter_congr ?_
                intro i _
                constructor <;> intro h <;> (convert h using 1; ring)
              rw [hfilt] at hcs
              have hsplit : ((Finset.range (k+1)).filter
                    (fun i : ℕ => ((p ^ s : ℕ) : ℤ) ∣ x + (i : ℤ) + 1)).card
                  = (u.filter
                      (fun i : ℕ => ((p ^ s : ℕ) : ℤ) ∣ x + (i : ℤ) + 1)).card + 1 := by
                have heq : (Finset.range (k+1)).filter
                      (fun i : ℕ => ((p ^ s : ℕ) : ℤ) ∣ x + (i : ℤ) + 1)
                    = insert i0 (u.filter
                        (fun i : ℕ => ((p ^ s : ℕ) : ℤ) ∣ x + (i : ℤ) + 1)) := by
                  ext i
                  simp only [Finset.mem_filter, Finset.mem_insert, hu, Finset.mem_erase,
                    Finset.mem_range]
                  constructor
                  · intro h
                    by_cases hi : i = i0
                    · exact Or.inl hi
                    · exact Or.inr ⟨⟨hi, h.1⟩, h.2⟩
                  · rintro (rfl | ⟨⟨hi, hi2⟩, h3⟩)
                    · exact ⟨hi0', by rw [hi0z]; exact dvd_zero _⟩
                    · exact ⟨hi2, h3⟩
                rw [heq, Finset.card_insert_of_notMem (by
                  rw [Finset.mem_filter]
                  rintro ⟨h1, -⟩
                  rw [hu] at h1
                  exact (Finset.mem_erase.mp h1).1 rfl)]
              omega
            have hsum_eq : ((Hj x (k+1) j : ℤ) : ℚ)
                = ∑ t ∈ u.powersetCard (k+1 - j),
                    ∏ i ∈ t, (((x + (i : ℤ) + 1 : ℤ)) : ℚ) := by
              rw [hHj]
              push_cast
              rfl
            rw [hsum_eq]
            refine le_padicValRat_sum_finset (s := u.powersetCard (k+1 - j)) ?_ ?_
            · intro t ht
              rw [padicValRat_prod_finset _ _
                (fun i hi => by
                  simp only [Int.cast_ne_zero]
                  exact hbu i ((Finset.mem_powersetCard.mp ht).1 hi))]
              refine le_trans (le_of_eq ?_)
                (level_sum_le u (fun i => x + (i : ℤ) + 1) hbu hp
                  (fun s => (k+1) / p ^ s - 1) (Nat.log p (k+1)) (j - 1) hcount t
                  (Finset.mem_powersetCard.mp ht).1 ?_)
              · refine Finset.sum_congr rfl fun s hs => ?_
                have hs1 : 1 ≤ (k+1) / p ^ s := by
                  have hpk : p ^ s ≤ k+1 := le_trans
                    (pow_le_pow_right' hp.one_lt.le (Finset.mem_Icc.mp hs).2)
                    (Nat.pow_log_le_self p (Nat.succ_ne_zero k))
                  calc 1 = p ^ s / p ^ s := (Nat.div_self (show 0 < p ^ s from Nat.pow_pos (n := s) hp.pos)).symm
                    _ ≤ (k+1) / p ^ s := Nat.div_le_div_right hpk
                have h1 : (((k+1) / p ^ s - 1 : ℕ) : ℤ) = (((k+1) / p ^ s : ℕ) : ℤ) - 1 := by
                  rw [Nat.cast_sub hs1, Nat.cast_one]
                have h2 : ((j - 1 : ℕ) : ℤ) = (j : ℤ) - 1 := by
                  rw [Nat.cast_sub hj1, Nat.cast_one]
                have hab : (((k+1) / p ^ s - 1 : ℕ) : ℤ) - ((j - 1 : ℕ) : ℤ)
                    = (((k+1) / p ^ s : ℕ) : ℤ) - (j : ℤ) := by rw [h1, h2]; ring
                rw [hab]
              · rw [(Finset.mem_powersetCard.mp ht).2, hu, Finset.card_erase_of_mem hi0,
                  Finset.card_range]
                omega
            · have hq : ((Hj x (k+1) j : ℤ) : ℚ) ≠ 0 := by simpa using hH
              rwa [hsum_eq] at hq
          · push_neg at hzero
            have hsum_eq : ((Hj x (k+1) j : ℤ) : ℚ)
                = ∑ t ∈ (Finset.range (k+1)).powersetCard (k+1 - j),
                    ∏ i ∈ t, (((x + (i : ℤ) + 1 : ℤ)) : ℚ) := by
              rw [Hj]; push_cast; rfl
            rw [hsum_eq]
            refine le_padicValRat_sum_finset
              (s := (Finset.range (k+1)).powersetCard (k+1 - j)) ?_ ?_
            · intro t ht
              rw [padicValRat_prod_finset _ _
                (fun i hi => by
                  exact_mod_cast hzero i ((Finset.mem_powersetCard.mp ht).1 hi))]
              exact level_sum_le (Finset.range (k+1)) (fun i => x + (i : ℤ) + 1)
                (fun i hi => hzero i hi) hp (fun s => (k+1) / p ^ s) (Nat.log p (k+1)) j
                (fun s _ => by
                  have hcs := card_multiples_shift (k+1) (p ^ s) (Nat.pow_pos (n := s) hp.pos) (x + 1)
                  have hfilt : (Finset.range (k+1)).filter
                        (fun i : ℕ => ((p ^ s : ℕ) : ℤ) ∣ (x + 1) + (i : ℤ))
                      = (Finset.range (k+1)).filter
                        (fun i : ℕ => ((p ^ s : ℕ) : ℤ) ∣ x + (i : ℤ) + 1) := by
                    refine Finset.filter_congr ?_
                    intro i _
                    constructor <;> intro h <;> (convert h using 1; ring)
                  rwa [hfilt] at hcs)
                t (Finset.mem_powersetCard.mp ht).1
                (by rw [(Finset.mem_powersetCard.mp ht).2, Finset.card_range]; omega)
            · have hq : ((Hj x (k+1) j : ℤ) : ℚ) ≠ 0 := by simpa using hH
              rwa [hsum_eq] at hq
        have hle : (∑ s ∈ Finset.Icc 1 (Nat.log p (k+1)),
              ((((k+1) / p ^ s : ℕ) : ℤ) - (j : ℤ)))
            ≤ ∑ s ∈ Finset.Icc 1 (Nat.log p (k+1)),
                max ((((k+1) / p ^ s : ℕ) : ℤ) - (j : ℤ)) 0 :=
          Finset.sum_le_sum fun s _ => le_max_left _ _
        have hsum : (∑ s ∈ Finset.Icc 1 (Nat.log p (k+1)),
              ((((k+1) / p ^ s : ℕ) : ℤ) - (j : ℤ)))
            = (∑ s ∈ Finset.Icc 1 (Nat.log p (k+1)), (((k+1) / p ^ s : ℕ) : ℤ))
              - (Nat.log p (k+1) : ℤ) * (j : ℤ) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul,
            show Nat.log p (k+1) + 1 - 1 = Nat.log p (k+1) from by omega]
        linarith [hfac, hU, hle, hsum]
      omega

/-! ## Assembly -/

theorem tijdeman_one (k j : ℕ) (x : ℤ) :
    ∃ N : ℤ, (ulcm k : ℚ)^j *
      Polynomial.aeval (x : ℚ) (Polynomial.hasseDeriv j (deltaPoly k)) = (N : ℚ) := by
  by_cases hjk : j ≤ k
  · obtain ⟨N, hN⟩ := tijdeman_core k j hjk x
    refine ⟨N, ?_⟩
    rw [aeval_hasseDeriv_deltaPoly k j hjk x]
    have hq : (ulcm k : ℚ)^j * ((Hj x k j : ℤ) : ℚ) = (N : ℚ) * (k.factorial : ℚ) := by
      have h := congrArg (fun z : ℤ => (z : ℚ)) hN
      push_cast at h
      rw [h]; ring
    have hC : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    rw [← mul_div_assoc, div_eq_iff hC]
    exact hq
  · refine ⟨0, ?_⟩
    have hdeg : (deltaPoly k).natDegree < j := by
      have hle : (deltaPoly k).natDegree ≤ k := by
        unfold deltaPoly
        refine le_trans (Polynomial.natDegree_smul_le _ _) ?_
        refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
        have h1 : (∑ i ∈ Finset.range k,
              (Polynomial.X + Polynomial.C ((i : ℚ) + 1)).natDegree)
            = ∑ _i ∈ Finset.range k, 1 := by
          refine Finset.sum_congr rfl fun i _ => Polynomial.natDegree_X_add_C _
        rw [h1]
        simp
      omega
    rw [Polynomial.hasseDeriv_eq_zero_of_lt_natDegree _ _ hdeg, map_zero, mul_zero]
    norm_num

theorem tijdeman_aux (k : ℕ) : ∀ l m : ℕ, ∀ x : ℤ, ∃ N : ℤ,
    (ulcm k : ℚ)^m * Polynomial.aeval (x : ℚ)
      (Polynomial.hasseDeriv m ((deltaPoly k) ^ l)) = (N : ℚ) := by
  intro l
  induction l with
  | zero =>
    intro m x
    rw [pow_zero]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      refine ⟨1, ?_⟩
      rw [pow_zero, Polynomial.hasseDeriv_zero']
      norm_num
    · refine ⟨0, ?_⟩
      rw [Polynomial.hasseDeriv_apply_one (k := m) hm, map_zero, mul_zero]
      norm_num
  | succ l ih =>
    intro m x
    rw [pow_succ]
    choose N1 hN1 using fun (ij : ℕ × ℕ) => ih ij.1 x
    choose N2 hN2 using fun (ij : ℕ × ℕ) => tijdeman_one k ij.2 x
    refine ⟨∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m, N1 ij * N2 ij, ?_⟩
    have key : (ulcm k : ℚ)^m * (Polynomial.aeval (x : ℚ))
          (Polynomial.hasseDeriv m ((deltaPoly k)^l * deltaPoly k))
        = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m, ((N1 ij * N2 ij : ℤ) : ℚ) := by
      rw [Polynomial.hasseDeriv_mul, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ij hij => ?_
      have hsum : ij.1 + ij.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      rw [map_mul]
      calc (ulcm k : ℚ)^m * ((Polynomial.aeval (x : ℚ))
              (Polynomial.hasseDeriv ij.1 ((deltaPoly k)^l)) *
            (Polynomial.aeval (x : ℚ)) (Polynomial.hasseDeriv ij.2 (deltaPoly k)))
          = ((ulcm k : ℚ)^ij.1 * (Polynomial.aeval (x : ℚ))
                (Polynomial.hasseDeriv ij.1 ((deltaPoly k)^l))) *
            ((ulcm k : ℚ)^ij.2 * (Polynomial.aeval (x : ℚ))
                (Polynomial.hasseDeriv ij.2 (deltaPoly k))) := by
              rw [← hsum, pow_add]; ring
        _ = (N1 ij : ℚ) * (N2 ij : ℚ) := by rw [hN1 ij, hN2 ij]
        _ = ((N1 ij * N2 ij : ℤ) : ℚ) := by push_cast; ring
    rw [key, ← Int.cast_sum]

theorem tijdeman_int (x : ℤ) (k l m : ℕ) :
    ∃ N : ℤ, (ulcm k : ℚ) ^ m * thetaRat x k l m = (N : ℚ) :=
  tijdeman_aux k l m x

end Work.BW
