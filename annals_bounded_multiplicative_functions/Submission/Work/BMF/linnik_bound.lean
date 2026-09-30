import Mathlib
import Submission.Work.BMF.linnik_defs
import Submission.Work.BMF.linnik.mul_esymm_eq_sum_range_pw

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Linnik's lemma (well-conditioned count)

For a prime `p` and `k < p`, the number of `k`-tuples `x` of residues mod `p^k` whose entries are
pairwise distinct mod `p` and whose power sums satisfy `∑ᵢ xᵢ^j ≡ H_j (mod p^{j+1})` for
`j = 1, …, k` is at most `k! · p^{k(k-1)/2}`.

The proof has three ingredients.

* *Well-conditioning*: two tuples with entries in `[0, p^k)` that are pairwise distinct mod `p`
  and whose power sums of orders `1, …, k` agree mod `p^k` have the same *set* of values.  Newton's
  identity shows that the elementary symmetric functions agree mod `p^k`, Vieta's formula turns
  this into the congruence `∏ᵢ (c - aᵢ) ≡ ∏ᵢ (c - bᵢ) mod p^k`, and a unique-lifting argument
  (for a simple root mod `p`) identifies the value sets.
* Consequently the map `x ↦ (power sums of x mod p^k)` has fibres of size at most `k!`: the values
  of such a tuple are pairwise distinct, so the tuple is an ordering of its value set.
* The image of that map is contained in the set of `v` with `v j ≡ H j (mod p^{j+1})`, and there
  are exactly `∏_{j<k} p^{k-j-1} = p^{k(k-1)/2}` such `v`.
-/

set_option maxHeartbeats 1600000

namespace Work.BMF

open Finset

/-! ### Auxiliary arithmetic -/

/-- For `0 < m`, the integer `m` divides `n % m - n`. -/
lemma dvd_mod_sub_self {m : ℕ} (hm : 0 < m) (n : ℕ) :
    (m : ℤ) ∣ ((n % m : ℕ) : ℤ) - (n : ℤ) := by
  refine ⟨-((n / m : ℕ) : ℤ), ?_⟩
  have h : ((n % m : ℕ) : ℤ) + ((n / m : ℕ) : ℤ) * (m : ℤ) = (n : ℤ) := by
    have h1 : ((n % m + m * (n / m) : ℕ) : ℤ) = (n : ℤ) := by rw [Nat.mod_add_div]
    rw [← h1]
    push_cast
    ring
  rw [← h]
  ring

/-! ### Root lifting -/

/-- **Root lifting.** Let `p` be a prime, `0 < k`, and let `a : Fin k → ℤ` have all values in
`[0, p^k)` with pairwise distinct residues mod `p`.  If `c ∈ [0, p^k)` and `p^k ∣ ∏ᵢ (c - aᵢ)`
then `c` is one of the `aᵢ`. -/
theorem exists_eq_of_dvd_prod_sub {p k : ℕ} (hp : p.Prime) (hk : 0 < k) {a : Fin k → ℤ} {c : ℤ}
    (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i < (p : ℤ) ^ k)
    (had : ∀ i j, i ≠ j → ¬ (p : ℤ) ∣ a i - a j)
    (hc0 : 0 ≤ c) (hc1 : c < (p : ℤ) ^ k)
    (h : (p : ℤ) ^ k ∣ ∏ i, (c - a i)) : ∃ i, a i = c := by
  classical
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp1 : (1 : ℤ) < p := by exact_mod_cast hp.one_lt
  -- `p` divides the product
  have hpow : (p : ℤ) ^ k = (p : ℤ) ^ (k - 1) * (p : ℤ) := by
    conv_lhs => rw [← Nat.sub_add_cancel hk]
    rw [pow_add, pow_one]
  have hpdvd : (p : ℤ) ∣ ∏ i, (c - a i) := by
    obtain ⟨t, ht⟩ := h
    refine ⟨(p : ℤ) ^ (k - 1) * t, ?_⟩
    rw [ht, hpow]
    ring
  obtain ⟨i₀, -, hi₀⟩ := (Prime.dvd_finsetProd_iff hpz (fun i => c - a i)).mp hpdvd
  -- all other factors are not divisible by `p`
  have hother : ∀ j ∈ (Finset.univ : Finset (Fin k)).erase i₀, ¬ (p : ℤ) ∣ (c - a j) := by
    intro j hj hjdiv
    have hjne : j ≠ i₀ := (Finset.mem_erase.mp hj).1
    have h1 : (p : ℤ) ∣ a j - a i₀ := by
      have := dvd_sub hi₀ hjdiv
      rwa [show c - a i₀ - (c - a j) = a j - a i₀ from by ring] at this
    exact had i₀ j (Ne.symm hjne) (by rw [← neg_sub]; exact dvd_neg.mpr h1)
  have hcof : ¬ (p : ℤ) ∣ ∏ j ∈ (Finset.univ : Finset (Fin k)).erase i₀, (c - a j) := by
    intro hcon
    obtain ⟨j, hjS, hjdiv⟩ := (Prime.dvd_finsetProd_iff hpz (fun j => c - a j)).mp hcon
    exact hother j hjS hjdiv
  -- split off the `i₀`-th factor
  have hfac : (p : ℤ) ^ k ∣ (c - a i₀) *
      ∏ j ∈ (Finset.univ : Finset (Fin k)).erase i₀, (c - a j) := by
    have h' := h
    rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin k)) (fun i => c - a i)
      (Finset.mem_univ i₀)] at h'
    exact h'
  have hcop : IsCoprime ((p : ℤ) ^ k)
      (∏ j ∈ (Finset.univ : Finset (Fin k)).erase i₀, (c - a j)) :=
    IsCoprime.pow_left (m := k) ((hpz.coprime_iff_not_dvd).mpr hcof)
  have hdiv : (p : ℤ) ^ k ∣ (c - a i₀) :=
    IsCoprime.dvd_of_dvd_mul_left hcop (by rw [mul_comm]; exact hfac)
  refine ⟨i₀, ?_⟩
  have hzero : c - a i₀ = 0 := by
    refine Int.eq_zero_of_abs_lt_dvd hdiv ?_
    rw [abs_lt]
    constructor
    · have := ha1 i₀; linarith
    · have := ha0 i₀; linarith
  linarith

/-! ### Newton's identity and the determination of the elementary symmetric functions -/

/-- The elementary symmetric functions of the negated tuple. -/
lemma esymm_neg {k : ℕ} (a : Fin k → ℤ) (j : ℕ) :
    esymm (fun i => -a i) j = (-1 : ℤ) ^ j * esymm a j := by
  rw [esymm_eq_multiset_esymm, esymm_eq_multiset_esymm]
  have h : (Finset.univ.val.map fun i => -a i) = (Finset.univ.val.map a).map Neg.neg := by
    rw [Multiset.map_map]
    rfl
  rw [h, Multiset.esymm_neg]

/-- **Determination of the elementary symmetric functions mod `p^k`.**  If the power sums of
orders `1, …, k` of two `k`-tuples agree mod `p^k` and `k < p` (with `p` prime), then their
elementary symmetric functions of orders `0, …, k` agree mod `p^k`. -/
theorem dvd_esymm_sub_of_dvd_pw_sub {p k : ℕ} (hp : p.Prime) (hkp : k < p)
    {a b : Fin k → ℤ} (h : ∀ i, 1 ≤ i → i ≤ k → (p : ℤ) ^ k ∣ pw a i - pw b i) :
    ∀ j, j ≤ k → (p : ℤ) ^ k ∣ esymm a j - esymm b j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0
      simp
    · have hNa := linnik.mul_esymm_eq_sum_range_pw a j
      have hNb := linnik.mul_esymm_eq_sum_range_pw b j
      have hterm : ∀ i ∈ Finset.range j,
          (p : ℤ) ^ k ∣ (-1 : ℤ) ^ (j + 1 + i) * esymm a i * pw a (j - i)
            - (-1 : ℤ) ^ (j + 1 + i) * esymm b i * pw b (j - i) := by
        intro i hi
        have hij : i < j := Finset.mem_range.mp hi
        have hik : i ≤ k := le_trans hij.le hj
        have h1 : (p : ℤ) ^ k ∣ esymm a i - esymm b i := ih i hij hik
        have hpos : 1 ≤ j - i := by omega
        have hle : j - i ≤ k := by omega
        have h2 : (p : ℤ) ^ k ∣ pw a (j - i) - pw b (j - i) := h (j - i) hpos hle
        have h3 : (-1 : ℤ) ^ (j + 1 + i) * esymm a i * pw a (j - i)
              - (-1 : ℤ) ^ (j + 1 + i) * esymm b i * pw b (j - i)
            = (-1 : ℤ) ^ (j + 1 + i) * ((esymm a i - esymm b i) * pw a (j - i)
              + esymm b i * (pw a (j - i) - pw b (j - i))) := by ring
        rw [h3]
        exact dvd_mul_of_dvd_right
          (dvd_add (dvd_mul_of_dvd_left h1 (pw a (j - i)))
            (dvd_mul_of_dvd_right h2 (esymm b i))) ((-1 : ℤ) ^ (j + 1 + i))
      have hsum : (p : ℤ) ^ k ∣ ∑ i ∈ Finset.range j,
          ((-1 : ℤ) ^ (j + 1 + i) * esymm a i * pw a (j - i)
            - (-1 : ℤ) ^ (j + 1 + i) * esymm b i * pw b (j - i)) :=
        Finset.dvd_sum hterm
      have heq : (j : ℤ) * (esymm a j - esymm b j) = ∑ i ∈ Finset.range j,
          ((-1 : ℤ) ^ (j + 1 + i) * esymm a i * pw a (j - i)
            - (-1 : ℤ) ^ (j + 1 + i) * esymm b i * pw b (j - i)) := by
        rw [mul_sub, hNa, hNb, Finset.sum_sub_distrib]
      have hnotnat : ¬ p ∣ j := by
        intro hd
        have hle : p ≤ j := Nat.le_of_dvd hjpos hd
        omega
      have hnotdvd : ¬ (p : ℤ) ∣ (j : ℤ) := fun hd => hnotnat ((Int.natCast_dvd_natCast).mp hd)
      have hcop : IsCoprime ((p : ℤ) ^ k) (j : ℤ) :=
        IsCoprime.pow_left (m := k)
          (((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd).mpr hnotdvd)
      refine IsCoprime.dvd_of_dvd_mul_left hcop ?_
      rw [heq]
      exact hsum

/-! ### Vieta's formula -/

/-- **Vieta's formula**, evaluated form: for a multiset `s` and any `c`,
`∏ t ∈ s, (c - t) = ∑_{j ≤ #s} (-1)^j (s.esymm j) c^{#s - j}`. -/
lemma multiset_prod_sub_eq_sum_esymm (s : Multiset ℤ) (c : ℤ) :
    (s.map (fun t => c - t)).prod =
      ∑ j ∈ Finset.range (s.card + 1), (-1 : ℤ) ^ j * (s.esymm j * c ^ (s.card - j)) := by
  have hV := congrArg (Polynomial.eval c) (Multiset.prod_X_sub_X_eq_sum_esymm s)
  simpa [Multiset.map_map, Polynomial.eval_multiset_prod, Polynomial.eval_finsetSum,
    Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_one,
    Polynomial.eval_X, Polynomial.eval_C] using hV

/-- The product `∏ᵢ (c - aᵢ)` vanishes when `c` is one of the `aᵢ`. -/
lemma prod_sub_eq_zero_of_mem {k : ℕ} (a : Fin k → ℤ) {c : ℤ} (hc : c ∈ Finset.univ.image a) :
    ((Finset.univ.val.map a).map (fun t => c - t)).prod = 0 := by
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hc
  have : a i ∈ Finset.univ.val.map a := Multiset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩
  obtain ⟨s, hs⟩ := Multiset.exists_cons_of_mem this
  rw [hs, Multiset.map_cons, Multiset.prod_cons, ← hi, sub_self, zero_mul]

/-- The product `∏ᵢ (c - bᵢ)` in the multiset encoding. -/
lemma prod_map_univ {k : ℕ} (b : Fin k → ℤ) (c : ℤ) :
    ((Finset.univ.val.map b).map (fun t => c - t)).prod = ∏ i, (c - b i) := by
  rw [Multiset.map_map]
  rfl

/-! ### Comparing value sets from congruence of the elementary symmetric functions -/

/-- **One direction of well-conditioning.**  Let `p` be a prime, `0 < k`, let `a b : Fin k → ℤ`
have all values in `[0, p^k)`, let the values of `b` be pairwise distinct mod `p`, and suppose
that the elementary symmetric functions of `a` and `b` of orders `1, …, k` agree mod `p^k`.  Then
every value of `a` is a value of `b`. -/
lemma image_subset_image_of_dvd_esymm_sub {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    {a b : Fin k → ℤ}
    (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i < (p : ℤ) ^ k)
    (hb0 : ∀ i, 0 ≤ b i) (hb1 : ∀ i, b i < (p : ℤ) ^ k)
    (hbd : ∀ i j, i ≠ j → ¬ (p : ℤ) ∣ b i - b j)
    (h : ∀ j : Fin k, (p : ℤ) ^ k ∣ esymm a (j.val + 1) - esymm b (j.val + 1)) :
    Finset.univ.image a ⊆ Finset.univ.image b := by
  classical
  intro c hc
  obtain ⟨i₀, -, rfl⟩ := Finset.mem_image.mp hc
  -- congruence of the multiset elementary symmetric functions
  have hesymm : ∀ j, 1 ≤ j → j ≤ k →
      (p : ℤ) ^ k ∣ (Finset.univ.val.map a).esymm j - (Finset.univ.val.map b).esymm j := by
    intro j hj1 hjk
    have hidx : j - 1 < k := by omega
    have hval : ((⟨j - 1, hidx⟩ : Fin k).val + 1) = j := by
      show j - 1 + 1 = j
      omega
    have hthis := h ⟨j - 1, hidx⟩
    rw [hval] at hthis
    rw [esymm_eq_multiset_esymm, esymm_eq_multiset_esymm] at hthis
    exact hthis
  -- the two products agree mod `p^k`
  have hcardA : (Finset.univ.val.map a).card = k := by simp
  have hcardB : (Finset.univ.val.map b).card = k := by simp
  have hprod : (p : ℤ) ^ k ∣ ((Finset.univ.val.map a).map (fun t => a i₀ - t)).prod
      - ((Finset.univ.val.map b).map (fun t => a i₀ - t)).prod := by
    have hA' := multiset_prod_sub_eq_sum_esymm (Finset.univ.val.map a) (a i₀)
    have hB' := multiset_prod_sub_eq_sum_esymm (Finset.univ.val.map b) (a i₀)
    rw [hcardA] at hA'
    rw [hcardB] at hB'
    rw [hA', hB', ← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun j hj => ?_
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · rw [hj0]
      simp
    · have hd := hesymm j hjpos hjk
      have h3 : (-1 : ℤ) ^ j * ((Finset.univ.val.map a).esymm j * (a i₀) ^ (k - j))
            - (-1 : ℤ) ^ j * ((Finset.univ.val.map b).esymm j * (a i₀) ^ (k - j))
          = (-1 : ℤ) ^ j
            * (((Finset.univ.val.map a).esymm j - (Finset.univ.val.map b).esymm j)
              * (a i₀) ^ (k - j)) := by ring
      rw [h3]
      exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hd _) _
  -- the first product vanishes, the second is the product we need
  have hvan : ((Finset.univ.val.map a).map (fun t => a i₀ - t)).prod = 0 :=
    prod_sub_eq_zero_of_mem a (Finset.mem_image.mpr ⟨i₀, Finset.mem_univ i₀, rfl⟩)
  have hbprod : ((Finset.univ.val.map b).map (fun t => a i₀ - t)).prod =
      ∏ i, (a i₀ - b i) := prod_map_univ b (a i₀)
  have hkey : (p : ℤ) ^ k ∣ ∏ i, (a i₀ - b i) := by
    have h' := hprod
    rw [hvan, hbprod, zero_sub] at h'
    simpa using h'
  obtain ⟨i₁, hi₁⟩ :=
    exists_eq_of_dvd_prod_sub hp hk hb0 hb1 hbd (ha0 i₀) (ha1 i₀) hkey
  exact Finset.mem_image.mpr ⟨i₁, Finset.mem_univ i₁, hi₁⟩

/-- **Well-conditioning of value sets.**  If two `k`-tuples with entries in `[0, p^k)` and pairwise
distinct residues mod `p` have elementary symmetric functions of orders `1, …, k` congruent
mod `p^k`, then they have the same set of values. -/
theorem image_eq_of_dvd_esymm_sub {p k : ℕ} (hp : p.Prime) (hk : 0 < k) {a b : Fin k → ℤ}
    (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i < (p : ℤ) ^ k)
    (hb0 : ∀ i, 0 ≤ b i) (hb1 : ∀ i, b i < (p : ℤ) ^ k)
    (had : ∀ i j, i ≠ j → ¬ (p : ℤ) ∣ a i - a j)
    (hbd : ∀ i j, i ≠ j → ¬ (p : ℤ) ∣ b i - b j)
    (h : ∀ j : Fin k, (p : ℤ) ^ k ∣ esymm a (j.val + 1) - esymm b (j.val + 1)) :
    (Finset.univ.image a) = (Finset.univ.image b) := by
  refine Finset.Subset.antisymm
    (image_subset_image_of_dvd_esymm_sub hp hk ha0 ha1 hb0 hb1 hbd h) ?_
  exact image_subset_image_of_dvd_esymm_sub hp hk hb0 hb1 ha0 ha1 had
    (fun j => by
      have h' := dvd_neg.mpr (h j)
      rwa [neg_sub] at h')

/-- **Well-conditioning.**  Same statement with the power sums in place of the elementary
symmetric functions. -/
theorem image_eq_of_dvd_pw_sub {p k : ℕ} (hp : p.Prime) (hkp : k < p) {a b : Fin k → ℤ}
    (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i < (p : ℤ) ^ k)
    (hb0 : ∀ i, 0 ≤ b i) (hb1 : ∀ i, b i < (p : ℤ) ^ k)
    (had : ∀ i j, i ≠ j → ¬ (p : ℤ) ∣ a i - a j)
    (hbd : ∀ i j, i ≠ j → ¬ (p : ℤ) ∣ b i - b j)
    (h : ∀ j : Fin k, (p : ℤ) ^ k ∣ pw a (j.val + 1) - pw b (j.val + 1)) :
    (Finset.univ.image a) = (Finset.univ.image b) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    simp
  · exact image_eq_of_dvd_esymm_sub hp hkpos ha0 ha1 hb0 hb1 had hbd fun j =>
      dvd_esymm_sub_of_dvd_pw_sub hp hkp (fun i hi hik => by
        have hlt : i - 1 < k := by omega
        have hfin : ((⟨i - 1, hlt⟩ : Fin k).val + 1) = i := by
          show i - 1 + 1 = i
          omega
        have h' := h ⟨i - 1, hlt⟩
        rwa [hfin] at h') (j.val + 1) (by omega)

/-! ### Counting: fibres of the value-set map and residues -/

/-- The bijection used to bound the fibres of the value-set map by permutations. -/
private def permOf {α : Type*} [DecidableEq α] {k : ℕ} {F : Finset α} {s : Finset (Fin k → α)}
    (e₀ : {x // x ∈ F} ≃ Fin k) (h : ∀ f ∈ s, Finset.univ.image f = F)
    (f : {f : Fin k → α // f ∈ s}) (i : Fin k) : Fin k :=
  e₀ ⟨f.1 i, by rw [← h f.1 f.2]; exact Finset.mem_image_of_mem f.1 (Finset.mem_univ i)⟩

/-- The number of `k`-tuples of elements of `α` whose image is a prescribed set `F` of
cardinality `k` is at most `k!`: each such tuple is an ordering of `F`. -/
theorem card_le_factorial_of_image_eq {α : Type*} [DecidableEq α] {k : ℕ} (F : Finset α)
    (hF : F.card = k) (s : Finset (Fin k → α)) (h : ∀ f ∈ s, Finset.univ.image f = F) :
    s.card ≤ k.factorial := by
  classical
  let e₀ : {x // x ∈ F} ≃ Fin k := Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hF])
  have hcard : ∀ f : {f : Fin k → α // f ∈ s},
      (Finset.univ.image f.1).card = (Finset.univ : Finset (Fin k)).card := by
    intro f
    rw [h f.1 f.2, hF, Finset.card_univ, Fintype.card_fin]
  have hinjT : ∀ f : {f : Fin k → α // f ∈ s}, Function.Injective f.1 := by
    intro f i j hij
    exact (Finset.card_image_iff.mp (hcard f)) (Finset.mem_univ i) (Finset.mem_univ j) hij
  have hmove : ∀ (f : {f : Fin k → α // f ∈ s}) (i : Fin k),
      (e₀.symm (permOf e₀ h f i)).1 = f.1 i := by
    intro f i
    simp [permOf]
  have hginj : ∀ f : {f : Fin k → α // f ∈ s}, Function.Injective (permOf e₀ h f) := by
    intro f i j hij
    apply hinjT f
    rw [← hmove f i, ← hmove f j, hij]
  have hgsurj : ∀ f : {f : Fin k → α // f ∈ s}, Function.Surjective (permOf e₀ h f) := by
    intro f y
    have hy : (e₀.symm y).1 ∈ Finset.univ.image f.1 := by
      rw [h f.1 f.2]
      exact (e₀.symm y).2
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hy
    refine ⟨i, ?_⟩
    have hs : e₀.symm (permOf e₀ h f i) = e₀.symm y := Subtype.ext (by rw [hmove f i, hi])
    calc permOf e₀ h f i = e₀ (e₀.symm (permOf e₀ h f i)) := (Equiv.apply_symm_apply e₀ _).symm
      _ = e₀ (e₀.symm y) := by rw [hs]
      _ = y := Equiv.apply_symm_apply e₀ y
  let Φ : {f : Fin k → α // f ∈ s} → Equiv.Perm (Fin k) := fun f =>
    Equiv.ofBijective (permOf e₀ h f) ⟨hginj f, hgsurj f⟩
  have hΦapply : ∀ (f : {f : Fin k → α // f ∈ s}) (i : Fin k), Φ f i = permOf e₀ h f i :=
    fun f i => rfl
  have hinjOn : Set.InjOn Φ (s.attach : Set {f : Fin k → α // f ∈ s}) := by
    intro f _ f' _ hff'
    have h1 : f.1 = f'.1 := by
      funext i
      have h3 : permOf e₀ h f i = permOf e₀ h f' i := by
        have h' := congrArg (fun σ : Equiv.Perm (Fin k) => σ i) hff'
        rwa [hΦapply, hΦapply] at h'
      rw [← hmove f i, ← hmove f' i, h3]
    exact Subtype.ext h1
  have h1 : s.attach.card ≤ (Finset.univ : Finset (Equiv.Perm (Fin k))).card :=
    Finset.card_le_card_of_injOn Φ (fun x _ => Finset.mem_univ _) hinjOn
  rw [Finset.card_attach, Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at h1
  exact h1

/-- **Number of residue tuples with prescribed congruences.**  For `p > 0` and `H : Fin k → ℕ`,
the number of `v : Fin k → Fin (p^k)` with `v j ≡ H j (mod p^{j+1})` for all `j` is at most
`p^{k(k-1)/2}`. -/
theorem card_filter_dvd_le {p k : ℕ} (hp : 0 < p) (H : Fin k → ℕ) :
    ((Finset.univ : Finset (Fin k → Fin (p ^ k))).filter
        (fun v => ∀ j : Fin k, (p : ℤ) ^ (j.val + 1) ∣ ((v j).val : ℤ) - (H j : ℤ))).card
      ≤ p ^ (k * (k - 1) / 2) := by
  classical
  set s := (Finset.univ : Finset (Fin k → Fin (p ^ k))).filter
      (fun v => ∀ j : Fin k, (p : ℤ) ^ (j.val + 1) ∣ ((v j).val : ℤ) - (H j : ℤ)) with hs
  -- the map recording the higher digits
  let Ψ : (Fin k → Fin (p ^ k)) → (∀ j : Fin k, Fin (p ^ (k - (j.val + 1)))) := fun v j =>
    ⟨(v j).val / p ^ (j.val + 1), by
      rw [Nat.div_lt_iff_lt_mul (pow_pos hp _)]
      calc (v j).val < p ^ k := (v j).isLt
        _ = p ^ (k - (j.val + 1)) * p ^ (j.val + 1) := by
            rw [← pow_add]
            congr 1
            omega⟩
  have hΨval : ∀ (v : Fin k → Fin (p ^ k)) (j : Fin k), (Ψ v j).val = (v j).val / p ^ (j.val + 1) :=
    fun _ _ => rfl
  have hmod {v : Fin k → Fin (p ^ k)}
      (hv : ∀ j : Fin k, (p : ℤ) ^ (j.val + 1) ∣ ((v j).val : ℤ) - (H j : ℤ)) (j : Fin k) :
      (v j).val ≡ H j [MOD p ^ (j.val + 1)] := by
    rw [Nat.modEq_iff_dvd]
    have h := hv j
    have hcast : ((p : ℤ) ^ (j.val + 1)) = ((p ^ (j.val + 1) : ℕ) : ℤ) := by push_cast; ring
    rw [hcast] at h
    simpa [neg_sub] using dvd_neg.mpr h
  have hinjOn : Set.InjOn Ψ (s : Set (Fin k → Fin (p ^ k))) := by
    intro v hv w hw hvw
    have hv' : ∀ j : Fin k, (p : ℤ) ^ (j.val + 1) ∣ ((v j).val : ℤ) - (H j : ℤ) :=
      (Finset.mem_filter.mp hv).2
    have hw' : ∀ j : Fin k, (p : ℤ) ^ (j.val + 1) ∣ ((w j).val : ℤ) - (H j : ℤ) :=
      (Finset.mem_filter.mp hw).2
    funext j
    have hres : (v j).val % p ^ (j.val + 1) = (w j).val % p ^ (j.val + 1) :=
      (hmod hv' j).trans (hmod hw' j).symm
    have hq : (v j).val / p ^ (j.val + 1) = (w j).val / p ^ (j.val + 1) := by
      have h' := congrArg Fin.val (congrFun hvw j)
      rw [hΨval, hΨval] at h'
      exact h'
    have h1 := Nat.mod_add_div (v j).val (p ^ (j.val + 1))
    have h2 := Nat.mod_add_div (w j).val (p ^ (j.val + 1))
    rw [hres, hq] at h1
    exact Fin.ext (by omega)
  have hcard : s.card = (s.image Ψ).card := (Finset.card_image_iff.mpr hinjOn).symm
  have hsub : s.image Ψ ⊆ (Finset.univ : Finset (∀ j : Fin k, Fin (p ^ (k - (j.val + 1))))) :=
    Finset.subset_univ _
  have hbound : (Finset.univ : Finset (∀ j : Fin k, Fin (p ^ (k - (j.val + 1))))).card
      ≤ p ^ (k * (k - 1) / 2) := by
    rw [Finset.card_univ, Fintype.card_pi]
    calc ∏ j : Fin k, Fintype.card (Fin (p ^ (k - (j.val + 1))))
        ≤ ∏ j : Fin k, p ^ (k - (j.val + 1)) :=
          Finset.prod_le_prod (fun j _ => by rw [Fintype.card_fin])
      _ = p ^ ∑ j : Fin k, (k - (j.val + 1)) :=
          Finset.prod_pow_eq_pow_sum Finset.univ (fun j : Fin k => k - (j.val + 1)) p
      _ = p ^ (k * (k - 1) / 2) := by
          congr 1
          have hsum : (∑ j : Fin k, (k - (j.val + 1))) = ∑ i ∈ Finset.range k, (k - (i + 1)) :=
            Fin.sum_univ_eq_sum_range (fun m => k - (m + 1)) k
          rw [hsum]
          have h1 : ∑ i ∈ Finset.range k, (k - (i + 1)) = ∑ i ∈ Finset.range k, i := by
            rw [← Finset.sum_range_reflect (fun i => i) k]
            refine Finset.sum_congr rfl fun i hi => ?_
            have hi' : i < k := Finset.mem_range.mp hi
            omega
          rw [h1, Finset.sum_range_id]
  calc s.card = (s.image Ψ).card := hcard
    _ ≤ (Finset.univ : Finset (∀ j : Fin k, Fin (p ^ (k - (j.val + 1))))).card :=
        Finset.card_le_card hsub
    _ ≤ p ^ (k * (k - 1) / 2) := hbound

/-! ### The main count -/

/-- The residue of the `j`-th power sum of `x` modulo `p^k`, as a natural number. -/
private def psiVal {k : ℕ} (p : ℕ) (x : Fin k → Fin (p ^ k)) (j : Fin k) : ℕ :=
  (∑ i, (x i).val ^ (j.val + 1)) % p ^ k

/-- The power-sum residue map `x ↦ (∑ᵢ xᵢ^{j+1} mod p^k)_j`. -/
private def psiMap {p k : ℕ} (hp : 0 < p) (x : Fin k → Fin (p ^ k)) : Fin k → Fin (p ^ k) :=
  fun j => ⟨psiVal p x j, Nat.mod_lt _ (pow_pos hp k)⟩

private lemma psiMap_val {p k : ℕ} (hp : 0 < p) (x : Fin k → Fin (p ^ k)) (j : Fin k) :
    (psiMap hp x j).val = psiVal p x j := rfl

private lemma psiVal_dvd {p k : ℕ} (hp : 0 < p) (x : Fin k → Fin (p ^ k)) (j : Fin k) :
    (p : ℤ) ^ k ∣ (psiVal p x j : ℤ) - (∑ i, ((x i).val : ℤ) ^ (j.val + 1)) := by
  have h1 := dvd_mod_sub_self (pow_pos hp k) (∑ i, (x i).val ^ (j.val + 1))
  have hcast : (((∑ i, (x i).val ^ (j.val + 1) : ℕ)) : ℤ)
      = ∑ i, ((x i).val : ℤ) ^ (j.val + 1) := by push_cast; rfl
  rwa [hcast] at h1

/-- **Linnik's lemma (well-conditioned count).** Let `p` be a prime with `k < p`. Then for any
prescribed residues `H`, the number of `x : Fin k → ℤ/p^k` whose coordinates are pairwise distinct
modulo `p` and whose power sums `∑ᵢ xᵢ^j` are congruent to `H j` modulo `p^{j+1}` (for every
`j : Fin k`) is at most `k! · p^{k(k-1)/2}`. -/
theorem linnik_bound (p k : ℕ) (hp : p.Prime) (hk : k < p) (H : Fin k → ℕ) :
    ((Finset.univ : Finset (Fin k → Fin (p^k))).filter (fun x =>
      (∀ i j : Fin k, i ≠ j → ¬ (p : ℤ) ∣ ((x i).val : ℤ) - ((x j).val : ℤ)) ∧
      (∀ j : Fin k, ((p : ℤ)^(j.val+1)) ∣ ((∑ i, ((x i).val : ℤ)^(j.val+1)) - (H j : ℤ))))).card
    ≤ k.factorial * p^(k*(k-1)/2) := by
  classical
  set A : Finset (Fin k → Fin (p^k)) := (Finset.univ : Finset (Fin k → Fin (p^k))).filter
      (fun x =>
        (∀ i j : Fin k, i ≠ j → ¬ (p : ℤ) ∣ ((x i).val : ℤ) - ((x j).val : ℤ)) ∧
        (∀ j : Fin k, ((p : ℤ)^(j.val+1)) ∣
          ((∑ i, ((x i).val : ℤ)^(j.val+1)) - (H j : ℤ)))) with hA
  have hmain : A.card ≤ k.factorial * p ^ (k * (k - 1) / 2) := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      have hle : A.card ≤ 1 := by
        calc A.card ≤ (Finset.univ : Finset (Fin 0 → Fin (p ^ 0))).card :=
              Finset.card_le_card (Finset.filter_subset _ _)
          _ = 1 := by
              rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, pow_zero]
      simpa using hle
    · -- the modulus can be lowered
      have hpk : ∀ j : Fin k, (p : ℤ) ^ (j.val + 1) ∣ (p : ℤ) ^ k := by
        intro j
        refine ⟨(p : ℤ) ^ (k - (j.val + 1)), ?_⟩
        rw [← pow_add]
        congr 1
        omega
      -- `psiMap` reproduces the prescribed residues
      have hψprop : ∀ x ∈ A, ∀ j : Fin k,
          (p : ℤ) ^ (j.val + 1) ∣ (psiVal p x j : ℤ) - (H j : ℤ) := by
        intro x hx j
        have hxcond := (Finset.mem_filter.mp hx).2
        have hj := hxcond.2 j
        have h1 : (p : ℤ) ^ (j.val + 1) ∣ (psiVal p x j : ℤ)
            - (∑ i, ((x i).val : ℤ) ^ (j.val + 1)) :=
          (hpk j).trans (psiVal_dvd hp.pos x j)
        have h3 := dvd_add h1 hj
        rwa [show (psiVal p x j : ℤ) - (∑ i, ((x i).val : ℤ) ^ (j.val + 1))
              + ((∑ i, ((x i).val : ℤ) ^ (j.val + 1)) - (H j : ℤ))
              = (psiVal p x j : ℤ) - (H j : ℤ) from by ring] at h3
      -- fibres of `psiMap` have size at most `k!`
      have hfiber : ∀ x ∈ A,
          (A.filter (fun y => psiMap hp.pos y = psiMap hp.pos x)).card ≤ k.factorial := by
        intro x hx
        have hxcond := (Finset.mem_filter.mp hx).2
        have xinj : Function.Injective x := by
          intro i j hij
          by_contra hne
          exact hxcond.1 i j hne ⟨0, by rw [hij]; ring⟩
        have hFcard : (Finset.univ.image x).card = k := by
          rw [Finset.card_image_of_injective _ xinj, Finset.card_univ, Fintype.card_fin]
        have hx0 : ∀ i, 0 ≤ ((x i).val : ℤ) := fun i => Int.natCast_nonneg _
        have hx1 : ∀ i, ((x i).val : ℤ) < (p : ℤ) ^ k := fun i => by
          exact_mod_cast (x i).isLt
        have hsame : ∀ y ∈ A.filter (fun y => psiMap hp.pos y = psiMap hp.pos x),
            Finset.univ.image (fun i : Fin k => ((y i).val : ℤ))
              = Finset.univ.image (fun i : Fin k => ((x i).val : ℤ)) := by
          intro y hy
          obtain ⟨hyA, hyψ⟩ := Finset.mem_filter.mp hy
          have hycond := (Finset.mem_filter.mp hyA).2
          have hy0 : ∀ i, 0 ≤ ((y i).val : ℤ) := fun i => Int.natCast_nonneg _
          have hy1 : ∀ i, ((y i).val : ℤ) < (p : ℤ) ^ k := fun i => by
            exact_mod_cast (y i).isLt
          have hpw : ∀ j : Fin k,
              (p : ℤ) ^ k ∣ pw (fun i => ((y i).val : ℤ)) (j.val + 1)
                - pw (fun i => ((x i).val : ℤ)) (j.val + 1) := by
            intro j
            have hcong : (p : ℤ) ^ k ∣ (psiVal p y j : ℤ) - (psiVal p x j : ℤ) := by
              have heq : psiVal p y j = psiVal p x j := by
                have h' : (psiMap hp.pos y j).val = (psiMap hp.pos x j).val := by rw [hyψ]
                rwa [psiMap_val, psiMap_val] at h'
              rw [heq]
              exact ⟨0, by ring⟩
            have h4 : (p : ℤ) ^ k ∣ (psiVal p y j : ℤ)
                - (∑ i, ((y i).val : ℤ) ^ (j.val + 1)) := psiVal_dvd hp.pos y j
            have h5 : (p : ℤ) ^ k ∣ (psiVal p x j : ℤ)
                - (∑ i, ((x i).val : ℤ) ^ (j.val + 1)) := psiVal_dvd hp.pos x j
            have h6 : (p : ℤ) ^ k ∣ (∑ i, ((y i).val : ℤ) ^ (j.val + 1))
                - (∑ i, ((x i).val : ℤ) ^ (j.val + 1)) := by
              have h7 : (∑ i, ((y i).val : ℤ) ^ (j.val + 1))
                    - (∑ i, ((x i).val : ℤ) ^ (j.val + 1))
                  = ((∑ i, ((y i).val : ℤ) ^ (j.val + 1)) - (psiVal p y j : ℤ))
                    + (((psiVal p y j : ℤ) - (psiVal p x j : ℤ))
                      + ((psiVal p x j : ℤ) - (∑ i, ((x i).val : ℤ) ^ (j.val + 1)))) := by
                ring
              have h4' : (p : ℤ) ^ k ∣ (∑ i, ((y i).val : ℤ) ^ (j.val + 1))
                  - (psiVal p y j : ℤ) := by
                have hh := dvd_neg.mpr h4
                rwa [neg_sub] at hh
              rw [h7]
              exact dvd_add h4' (dvd_add hcong h5)
            show (p : ℤ) ^ k ∣ (∑ i, ((y i).val : ℤ) ^ (j.val + 1))
              - (∑ i, ((x i).val : ℤ) ^ (j.val + 1))
            exact h6
          exact image_eq_of_dvd_pw_sub hp hk hy0 hy1 hx0 hx1 hycond.1 hxcond.1 hpw
        -- transport to `Fin (p^k)`-valued tuples
        have hsame' : ∀ y ∈ A.filter (fun y => psiMap hp.pos y = psiMap hp.pos x),
            Finset.univ.image y = Finset.univ.image x := by
          intro y hy
          have h := hsame y hy
          have h2 : (Finset.univ.image y).image (fun c : Fin (p ^ k) => (c.val : ℤ))
              = (Finset.univ.image x).image (fun c : Fin (p ^ k) => (c.val : ℤ)) := by
            rw [Finset.image_image, Finset.image_image]
            exact h
          exact Finset.image_injective (f := fun c : Fin (p ^ k) => (c.val : ℤ))
            (fun a b hab => Fin.ext (Int.ofNat.inj hab)) h2
        exact card_le_factorial_of_image_eq (Finset.univ.image x) hFcard _ hsame'
      -- image bound
      have himage : (A.image (psiMap hp.pos)).card ≤ p ^ (k * (k - 1) / 2) := by
        refine le_trans (Finset.card_le_card ?_) (card_filter_dvd_le hp.pos H)
        intro v hv
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => by
          rw [psiMap_val]
          exact hψprop x hx j⟩
      calc A.card ≤ k.factorial * (A.image (psiMap hp.pos)).card :=
            Finset.card_le_mul_card_image A k.factorial fun v hv => by
              obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
              exact hfiber x hx
        _ ≤ k.factorial * p ^ (k * (k - 1) / 2) := Nat.mul_le_mul_left _ himage
  exact hmain

end Work.BMF
