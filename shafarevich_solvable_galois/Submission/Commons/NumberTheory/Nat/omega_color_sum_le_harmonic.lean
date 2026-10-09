import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.Factorization.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped BigOperators

namespace Commons.NumberTheory.Nat

noncomputable section



def harm (B : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 B, (1 : ℝ) / (k : ℝ)

def tupleFinset (m B : ℕ) : Finset (Fin m → ℕ) :=
  (Fintype.piFinset (fun _ : Fin m => Finset.Icc 1 B)).filter
    (fun f => (∏ i : Fin m, f i) ≤ B)

lemma mem_tupleFinset (m B : ℕ) (f : Fin m → ℕ) :
    f ∈ tupleFinset m B ↔ (∀ i, f i ∈ Finset.Icc 1 B) ∧ (∏ i : Fin m, f i) ≤ B := by
  simp [tupleFinset]

lemma coordinate_mem {m B : ℕ} {f : Fin m → ℕ} (hf : f ∈ tupleFinset m B) (i : Fin m) :
    f i ∈ Finset.Icc 1 B :=
  (((mem_tupleFinset m B f).1 hf).1) i

lemma product_le {m B : ℕ} {f : Fin m → ℕ} (hf : f ∈ tupleFinset m B) :
    (∏ i : Fin m, f i) ≤ B :=
  ((mem_tupleFinset m B f).1 hf).2

/-- Restricting an `(m+1)`-tuple whose last entry is `k` and whose product is ≤ B
gives an `m`-tuple in `tupleFinset m (B / k)`. -/
lemma restrict_mem {m B k : ℕ} {f : Fin (m+1) → ℕ} (hf : f ∈ tupleFinset (m+1) B)
    (hlast : f (Fin.last m) = k) (hk : 1 ≤ k) :
    (fun i : Fin m => f i.castSucc) ∈ tupleFinset m (B / k) := by
  rw [mem_tupleFinset]
  have hsplit' : (∏ j : Fin (m+1), f j) = (∏ j : Fin m, f j.castSucc) * k := by
    simpa [hlast] using (Fin.prod_univ_castSucc f)
  have hle : (∏ j : Fin m, f j.castSucc) * k ≤ B := by
    rw [← hsplit']
    exact product_le hf
  have hrest : (∏ j : Fin m, f j.castSucc) ≤ B / k := by
    exact (Nat.le_div_iff_mul_le (by omega : 0 < k)).2 hle
  constructor
  · intro i
    have hi : f i.castSucc ∈ Finset.Icc 1 B := coordinate_mem hf i.castSucc
    have hge1 : 1 ≤ f i.castSucc := (Finset.mem_Icc.mp hi).1
    have hle1 : f i.castSucc ≤ ∏ j : Fin m, f j.castSucc := by
      apply Finset.single_le_prod' (s := Finset.univ) (f := fun j : Fin m => f j.castSucc)
      · intro j hj
        exact (Finset.mem_Icc.mp (coordinate_mem hf j.castSucc)).1
      · exact Finset.mem_univ i
    exact Finset.mem_Icc.mpr ⟨hge1, le_trans hle1 hrest⟩
  · exact hrest

/-- Snoc restores a tuple from its restriction and its last entry. -/
lemma snoc_restore {m B : ℕ} {f : Fin (m+1) → ℕ} (hf : f ∈ tupleFinset (m+1) B) :
    Fin.snoc (fun i : Fin m => f i.castSucc) (f (Fin.last m)) = f := by
  have h := Fin.snoc_init_self f
  convert h using 1
  rfl

/-- Restriction is injective on tuples with a fixed last entry. -/
lemma restrict_inj_fiber {m B k : ℕ} :
    Set.InjOn (fun f : Fin (m+1) → ℕ => (fun i : Fin m => f i.castSucc))
      ↑((tupleFinset (m+1) B).filter (fun f => f (Fin.last m) = k)) := by
  intro f hf g hg heq
  have hfF : f ∈ (tupleFinset (m+1) B).filter (fun f => f (Fin.last m) = k) := by
    simpa using hf
  have hgF : g ∈ (tupleFinset (m+1) B).filter (fun f => f (Fin.last m) = k) := by
    simpa using hg
  rw [Finset.mem_filter] at hfF hgF
  rcases hfF with ⟨hf1, hfk⟩
  rcases hgF with ⟨hg1, hgk⟩
  have hrest_eq : (fun i : Fin m => f i.castSucc) = fun i : Fin m => g i.castSucc := by
    simpa using heq
  calc
    f = Fin.snoc (fun i : Fin m => f i.castSucc) (f (Fin.last m)) := by
        rw [snoc_restore hf1]
    _ = Fin.snoc (fun i : Fin m => g i.castSucc) (f (Fin.last m)) := by rw [hrest_eq]
    _ = Fin.snoc (fun i : Fin m => g i.castSucc) (g (Fin.last m)) := by rw [hfk, hgk]
    _ = g := by rw [snoc_restore hg1]


lemma sum_card_filter_of_mem_image {α β : Type*} [DecidableEq β] (s : Finset α) (t : Finset β)
    (f : α → β) (h : ∀ x ∈ s, f x ∈ t) :
    s.card = ∑ b ∈ t, (s.filter (fun x => f x = b)).card := by
  classical
  have hcov : s = t.biUnion (fun b => s.filter (fun x => f x = b)) := by
    ext x
    constructor
    · intro hx
      refine Finset.mem_biUnion.mpr ⟨f x, h x hx, ?_⟩
      simpa using hx
    · intro hx
      rcases Finset.mem_biUnion.mp hx with ⟨b, hb, hxb⟩
      exact (Finset.mem_filter.mp hxb).1
  have hdisj : (t : Set β).PairwiseDisjoint (fun b => s.filter (fun x => f x = b)) := by
    simpa using (Set.pairwiseDisjoint_filter (f := f) (s := (t : Set β)) (t := s))
  calc
    s.card = (t.biUnion (fun b => s.filter (fun x => f x = b))).card := by
      conv_lhs => rw [hcov]
    _ = ∑ b ∈ t, (s.filter (fun x => f x = b)).card := Finset.card_biUnion hdisj

/-- Partition an `(m+1)`-tuple by its last coordinate. -/
lemma tupleFinset_card_eq_sum_last (m B : ℕ) (hB : 1 ≤ B) :
    (tupleFinset (m+1) B).card =
      ∑ k ∈ Finset.Icc 1 B,
        ((tupleFinset (m+1) B).filter (fun f => f (Fin.last m) = k)).card := by
  apply sum_card_filter_of_mem_image (s := tupleFinset (m+1) B)
    (t := Finset.Icc 1 B) (f := fun f : Fin (m+1) → ℕ => f (Fin.last m))
  intro f hf
  exact coordinate_mem hf (Fin.last m)

/-- Each fiber (fixed last coordinate `k`) embeds into the `m`-tuples with
product bound `B / k`. -/
lemma fiber_card_le {m B k : ℕ} (hk : 1 ≤ k) :
    ((tupleFinset (m+1) B).filter (fun f => f (Fin.last m) = k)).card ≤
      (tupleFinset m (B / k)).card := by
  classical
  let r : (Fin (m+1) → ℕ) → (Fin m → ℕ) := fun f => (fun i : Fin m => f i.castSucc)
  let F : Finset (Fin (m+1) → ℕ) :=
    (tupleFinset (m+1) B).filter (fun f => f (Fin.last m) = k)
  have hsub : F.image r ⊆ tupleFinset m (B / k) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨f, hfF, rfl⟩
    have hf : f ∈ tupleFinset (m+1) B := (Finset.mem_filter.mp hfF).1
    have hlast : f (Fin.last m) = k := (Finset.mem_filter.mp hfF).2
    exact restrict_mem hf hlast hk
  have hinj : Set.InjOn r ↑F := by
    simpa [F, r] using (restrict_inj_fiber (m := m) (B := B) (k := k))
  calc
    (F).card = (F.image r).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (tupleFinset m (B / k)).card := Finset.card_le_card hsub

/-- Removing the last coordinate from an `(m+1)`-tuple bounds its count by the
sum over possible last entries `k` of the `m`-tuple counts with bound `B/k`. -/
lemma tupleFinset_succ_card_le_sum (m B : ℕ) (hB : 1 ≤ B) :
    (tupleFinset (m+1) B).card ≤
      ∑ k ∈ Finset.Icc 1 B, (tupleFinset m (B / k)).card := by
  rw [tupleFinset_card_eq_sum_last m B hB]
  exact Finset.sum_le_sum (fun k hk => fiber_card_le (m := m) (B := B) (k := k)
    ((Finset.mem_Icc.mp hk).1))

/-- The harmonic partial sum is nonnegative. -/
lemma harm_nonneg (B : ℕ) : 0 ≤ harm B := by
  unfold harm
  exact Finset.sum_nonneg (fun k hk => by
    have hkpos : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hk).1)
    exact div_nonneg (by norm_num) (le_of_lt hkpos))

/-- The harmonic partial sum is monotone in the upper bound. -/
lemma harm_mono {B B' : ℕ} (h : B ≤ B') : harm B ≤ harm B' := by
  unfold harm
  refine Finset.sum_le_sum_of_subset_of_nonneg (s := Finset.Icc 1 B)
    (t := Finset.Icc 1 B') ?_ ?_
  · intro k hk
    rcases Finset.mem_Icc.mp hk with ⟨h1, hkB⟩
    exact Finset.mem_Icc.mpr ⟨h1, le_trans hkB h⟩
  · intro k hk hnk
    have hkpos : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hk).1)
    exact div_nonneg (by norm_num) (le_of_lt hkpos)

/-- The integer quotient is at most the real quotient. -/
lemma nat_div_cast_le {A k : ℕ} (hk : 1 ≤ k) :
    ((A / k : ℕ) : ℝ) ≤ (A : ℝ) / (k : ℝ) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  rw [le_div_iff₀ hk0]
  exact_mod_cast (Nat.div_mul_le_self A k)

/-- The `(m+1)`-tuple count is at most `B` times the `m`-th power of the
harmonic partial sum. -/
lemma tupleFinset_card_le_harm (m B : ℕ) (hB : 1 ≤ B) :
    ((tupleFinset (m+1) B).card : ℝ) ≤ (B : ℝ) * (harm B) ^ m := by
  induction m generalizing B with
  | zero =>
      have hle : (tupleFinset 1 B).card ≤ B := by
        calc
          (tupleFinset 1 B).card
              ≤ (Fintype.piFinset (fun _ : Fin 1 => Finset.Icc 1 B)).card := by
                  exact Finset.card_le_card (Finset.filter_subset _ _)
          _ = B := by simp
      have hpow : (B : ℝ) * (harm B) ^ 0 = B := by simp
      rw [hpow]
      exact_mod_cast hle
  | succ m ih =>
      let S : Finset ℕ := Finset.Icc 1 B
      have hsum_term : ∀ k ∈ S,
          ((tupleFinset (m + 1) (B / k)).card : ℝ) ≤ ((B / k : ℕ) : ℝ) * (harm B) ^ m := by
        intro k hk
        have hbk : 1 ≤ B / k := by
          rcases Finset.mem_Icc.mp hk with ⟨hk1, hkB⟩
          rw [Nat.le_div_iff_mul_le (by omega : 0 < k)]
          rw [one_mul]
          exact hkB
        have hib := ih (B / k) hbk
        have hmono : harm (B / k) ≤ harm B := harm_mono (Nat.div_le_self B k)
        have hpowm : (harm (B / k)) ^ m ≤ (harm B) ^ m :=
          pow_le_pow_left₀ (harm_nonneg (B / k)) hmono m
        have hpos : 0 ≤ ((B / k : ℕ) : ℝ) := by positivity
        exact le_trans hib (mul_le_mul_of_nonneg_left hpowm hpos)
      calc
        ((tupleFinset (m.succ + 1) B).card : ℝ)
            ≤ (∑ k ∈ S, ((tupleFinset (m + 1) (B / k)).card : ℝ)) := by
                exact_mod_cast (tupleFinset_succ_card_le_sum (m + 1) B hB)
        _ ≤ ∑ k ∈ S, (((B / k : ℕ) : ℝ) * (harm B) ^ m) := by
                simpa [S] using (Finset.sum_le_sum hsum_term)
        _ ≤ ∑ k ∈ S, (((B : ℝ) * ((1 : ℝ) / (k : ℝ))) * (harm B) ^ m) := by
                apply Finset.sum_le_sum
                intro k hk
                have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
                have hle : ((B / k : ℕ) : ℝ) ≤ (B : ℝ) * ((1 : ℝ) / (k : ℝ)) := by
                  calc
                    ((B / k : ℕ) : ℝ) ≤ (B : ℝ) / (k : ℝ) := nat_div_cast_le hk1
                    _ = (B : ℝ) * ((1 : ℝ) / (k : ℝ)) := by ring
                have hpos : 0 ≤ (harm B) ^ m := pow_nonneg (harm_nonneg B) m
                exact mul_le_mul_of_nonneg_right hle hpos
        _ = ∑ k ∈ S, ((B : ℝ) * (harm B) ^ m * ((1 : ℝ) / (k : ℝ))) := by
                apply Finset.sum_congr rfl
                intro k hk
                ring
        _ = (B : ℝ) * (harm B) ^ m * (∑ k ∈ S, ((1 : ℝ) / (k : ℝ))) := by
                rw [← Finset.mul_sum]
        _ = (B : ℝ) * (harm B) ^ (m + 1) := by
                have hH : (∑ k ∈ S, ((1 : ℝ) / (k : ℝ))) = harm B := by
                  simp [harm, S]
                rw [hH, pow_succ']
                ring

/-- The `c`-tuple count is at most `A` times the `(c-1)`-st power of the
harmonic partial sum (colour-indexed version of `tupleFinset_card_le_harm`). -/
lemma tupleFinset_card_le_harm_color (c : ℕ) : ∀ (A : ℕ), 1 ≤ A → 1 ≤ c →
    ((tupleFinset c A).card : ℝ) ≤ (A : ℝ) * (harm A) ^ (c - 1) := by
  induction c with
  | zero =>
      intro A hA hc
      omega
  | succ c ih =>
      intro A hA hc
      by_cases hc0 : c = 0
      · subst c
        -- one coordinate: count is `A`
        have hle : (tupleFinset 1 A).card ≤ A := by
          calc
            (tupleFinset 1 A).card
                ≤ (Fintype.piFinset (fun _ : Fin 1 => Finset.Icc 1 A)).card := by
                    exact Finset.card_le_card (Finset.filter_subset _ _)
            _ = A := by simp
        have hpow : (A : ℝ) * (harm A) ^ (1 - 1) = A := by simp
        rw [hpow]
        exact_mod_cast hle
      · have hc1 : 1 ≤ c := by omega
        -- fibres of the last coordinate: `c`-tuples of bound `A / k`
        let S : Finset ℕ := Finset.Icc 1 A
        have hsum_term : ∀ k ∈ S,
            ((tupleFinset c (A / k)).card : ℝ) ≤ ((A / k : ℕ) : ℝ) * (harm A) ^ (c - 1) := by
          intro k hk
          have hbk : 1 ≤ A / k := by
            rcases Finset.mem_Icc.mp hk with ⟨hk1, hkA⟩
            rw [Nat.le_div_iff_mul_le (by omega : 0 < k)]
            rw [one_mul]
            exact hkA
          have hib := ih (A / k) hbk hc1
          have hmono : harm (A / k) ≤ harm A := harm_mono (Nat.div_le_self A k)
          have hpowm : (harm (A / k)) ^ (c - 1) ≤ (harm A) ^ (c - 1) :=
            pow_le_pow_left₀ (harm_nonneg (A / k)) hmono (c - 1)
          have hpos : 0 ≤ ((A / k : ℕ) : ℝ) := by positivity
          exact le_trans hib (mul_le_mul_of_nonneg_left hpowm hpos)
        calc
          ((tupleFinset (c + 1) A).card : ℝ)
              ≤ (∑ k ∈ S, ((tupleFinset c (A / k)).card : ℝ)) := by
                  have hnat : (tupleFinset (c + 1) A).card ≤
                      ∑ k ∈ S, (tupleFinset c (A / k)).card := by
                    simpa [S] using (tupleFinset_succ_card_le_sum c A hA)
                  exact_mod_cast hnat
          _ ≤ ∑ k ∈ S, (((A / k : ℕ) : ℝ) * (harm A) ^ (c - 1)) := by
                  simpa [S] using (Finset.sum_le_sum hsum_term)
          _ ≤ ∑ k ∈ S, (((A : ℝ) * ((1 : ℝ) / (k : ℝ))) * (harm A) ^ (c - 1)) := by
                  apply Finset.sum_le_sum
                  intro k hk
                  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
                  have hle : ((A / k : ℕ) : ℝ) ≤ (A : ℝ) * ((1 : ℝ) / (k : ℝ)) := by
                    calc
                      ((A / k : ℕ) : ℝ) ≤ (A : ℝ) / (k : ℝ) := nat_div_cast_le hk1
                      _ = (A : ℝ) * ((1 : ℝ) / (k : ℝ)) := by ring
                  have hpos : 0 ≤ (harm A) ^ (c - 1) := pow_nonneg (harm_nonneg A) (c - 1)
                  exact mul_le_mul_of_nonneg_right hle hpos
          _ = ∑ k ∈ S, ((A : ℝ) * (harm A) ^ (c - 1) * ((1 : ℝ) / (k : ℝ))) := by
                  apply Finset.sum_congr rfl
                  intro k hk
                  ring
          _ = (A : ℝ) * (harm A) ^ (c - 1) * (∑ k ∈ S, ((1 : ℝ) / (k : ℝ))) := by
                  rw [← Finset.mul_sum]
          _ = (A : ℝ) * (harm A) ^ c := by
                  have hH : (∑ k ∈ S, ((1 : ℝ) / (k : ℝ))) = harm A := by
                    simp [harm, S]
                  have hpowc : (harm A) ^ c = (harm A) ^ ((c - 1) + 1) := by
                    congr 1
                    omega
                  rw [hH, hpowc, pow_succ']
                  ring



/-- The `i`-th coordinate of the pure `c`-tuple decomposition of `a` given by a
coloring `φ` of the prime factors of `a`: the product of `p^(v_p(a))` over the
prime factors `p` of `a` whose color is `i`. -/
def pureCoord (a c : ℕ) (φ : ↥(a.primeFactors) → Fin c) : Fin c → ℕ :=
  fun i => (a.primeFactors.attach.filter (fun x => φ x = i)).prod
    (fun x => (x : ℕ) ^ a.factorization (x : ℕ))

/-- The product over the coordinates of the pure decomposition of `a ≠ 0` is `a`. -/
lemma pureCoord_prod_eq (a c : ℕ) (ha : a ≠ 0) (φ : ↥(a.primeFactors) → Fin c) :
    (∏ i : Fin c, pureCoord a c φ i) = a := by
  unfold pureCoord
  rw [Finset.prod_fiberwise (s := a.primeFactors.attach) (g := φ)
    (f := fun x : ↥(a.primeFactors) => (x : ℕ) ^ a.factorization (x : ℕ))]
  calc
    (∏ x ∈ a.primeFactors.attach, (x : ℕ) ^ a.factorization (x : ℕ))
        = ∏ p ∈ a.primeFactors, p ^ a.factorization p := by
          simpa using (Finset.prod_attach a.primeFactors (fun p : ℕ => p ^ a.factorization p))
    _ = a := (Nat.prod_primeFactors_pow_factorization ha).symm

/-- Each coordinate of the pure decomposition is at least `1`. -/
lemma pureCoord_one_le (a c : ℕ) (φ : ↥(a.primeFactors) → Fin c) (i : Fin c) :
    1 ≤ pureCoord a c φ i := by
  unfold pureCoord
  exact Finset.one_le_prod₀ (fun x hx => by
    rcases x with ⟨p, hp⟩
    have hp0 : 0 < p := (Nat.prime_of_mem_primeFactors hp).pos
    have hpow : 0 < p ^ a.factorization p := pow_pos hp0 (a.factorization p)
    exact Nat.succ_le_iff.mpr hpow)

/-- The pure decomposition of an element of `Icc 1 A` lies in `tupleFinset c A`. -/
lemma pureCoord_mem_tuple (c A : ℕ) {a : ℕ} (ha1 : 1 ≤ a) (haA : a ≤ A)
    (φ : ↥(a.primeFactors) → Fin c) :
    pureCoord a c φ ∈ tupleFinset c A := by
  rw [mem_tupleFinset]
  constructor
  · intro i
    have hge1 : 1 ≤ pureCoord a c φ i := pureCoord_one_le a c φ i
    have hleA : pureCoord a c φ i ≤ A := by
      have hprod : (∏ j : Fin c, pureCoord a c φ j) = a :=
        pureCoord_prod_eq a c (by omega) φ
      have hle : pureCoord a c φ i ≤ ∏ j : Fin c, pureCoord a c φ j := by
        apply Finset.single_le_prod' (s := Finset.univ) (f := fun j => pureCoord a c φ j)
        · intro j hj
          exact pureCoord_one_le a c φ j
        · exact Finset.mem_univ i
      omega
    exact Finset.mem_Icc.mpr ⟨hge1, hleA⟩
  · have hprod : (∏ j : Fin c, pureCoord a c φ j) = a :=
      pureCoord_prod_eq a c (by omega) φ
    omega

/-- `Nat.prod_primeFactors_pow_factorization` in usable orientation. -/
lemma prod_primeFactors_pow_factorization_symm (a : ℕ) (ha : a ≠ 0) :
    (∏ p ∈ a.primeFactors, p ^ a.factorization p) = a :=
  (Nat.prod_primeFactors_pow_factorization ha).symm


/-- A prime divisor of `a` divides the coordinate of its color in the pure
decomposition. -/
lemma pureCoord_dvd_color (a c : ℕ) {p : ℕ} (hp : p ∈ a.primeFactors)
    (φ : ↥(a.primeFactors) → Fin c) :
    p ∣ pureCoord a c φ (φ ⟨p, hp⟩) := by
  unfold pureCoord
  let S : Finset (↥(a.primeFactors)) :=
    a.primeFactors.attach.filter (fun x => φ x = φ ⟨p, hp⟩)
  have hx0 : (⟨p, hp⟩ : ↥(a.primeFactors)) ∈ S := by
    simp [S]
  have he : 0 < a.factorization p := by
    rcases (Nat.mem_primeFactors.mp hp) with ⟨hpP, hpdvd, ha⟩
    exact (hpP.factorization_pos_of_dvd ha hpdvd)
  have hpow : p ∣ p ^ a.factorization p := dvd_pow_self p he.ne'
  have hdvdpow : p ^ a.factorization p ∣
      S.prod (fun x => (x : ℕ) ^ a.factorization (x : ℕ)) := by
    exact Finset.dvd_prod_of_mem (fun x : ↥(a.primeFactors) =>
      (x : ℕ) ^ a.factorization (x : ℕ)) hx0
  exact dvd_trans hpow hdvdpow

/-- A prime divisor of `a` does not divide coordinates of other colors. -/
lemma pureCoord_not_dvd_of_ne_color (a c : ℕ) {p : ℕ} (hp : p ∈ a.primeFactors)
    (φ : ↥(a.primeFactors) → Fin c) {i : Fin c} (hi : φ ⟨p, hp⟩ ≠ i) :
    ¬ p ∣ pureCoord a c φ i := by
  unfold pureCoord
  let S : Finset (↥(a.primeFactors)) :=
    a.primeFactors.attach.filter (fun x => φ x = i)
  have hS : ∀ x ∈ S, x.val ≠ p := by
    intro x hx
    have hxφ : φ x = i := (Finset.mem_filter.mp hx).2
    intro hxp
    have hxeq : x = (⟨p, hp⟩ : ↥(a.primeFactors)) := Subtype.ext hxp
    exact hi (by simpa [hxeq] using hxφ)
  have hpP : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  refine hpP.prime.not_dvd_finsetProd
    (g := fun x : ↥(a.primeFactors) => (x : ℕ) ^ a.factorization (x : ℕ)) ?_
  intro x hx
  have hne : x.val ≠ p := hS x hx
  have hq : Nat.Prime x.val := Nat.prime_of_mem_primeFactors x.2
  by_contra hdvd
  exact hne (Nat.prime_eq_prime_of_dvd_pow (p := p) (q := x.val)
    (m := a.factorization x.val) hpP hq hdvd).symm

/-- The pure decomposition map is injective on colorings of `a`. -/
lemma pureCoord_injective_of (a c : ℕ) (ha : a ≠ 0) :
    Function.Injective (pureCoord a c) := by
  intro φ ψ h
  by_contra hne
  have hex : ∃ x : ↥(a.primeFactors), φ x ≠ ψ x := by
    by_contra h'
    apply hne
    funext x
    by_contra hx
    exact h' ⟨x, hx⟩
  rcases hex with ⟨x, hxφ⟩
  have hdvd₁ : x.val ∣ pureCoord a c φ (φ x) := pureCoord_dvd_color a c x.2 φ
  have hndvd₂ : ¬ x.val ∣ pureCoord a c ψ (φ x) := by
    apply pureCoord_not_dvd_of_ne_color a c x.2 ψ (i := φ x)
    simpa using hxφ.symm
  have hc : pureCoord a c φ (φ x) = pureCoord a c ψ (φ x) := congrFun h (φ x)
  exact hndvd₂ (by simpa [hc] using hdvd₁)

/-- Cardinality of the colouring space of the prime factors of `a`. -/
lemma card_coloring (s : Finset ℕ) (c : ℕ) :
    Fintype.card (↥s → Fin c) = c ^ s.card := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]

/-- The real power `c^ω(a)` equals the number of colourings of the prime
factors of `a`. -/
lemma coloring_pow_eq_card (a c : ℕ) :
    (c : ℝ) ^ (a.primeFactors).card =
      (Fintype.card (↥(a.primeFactors) → Fin c) : ℝ) := by
  exact_mod_cast (card_coloring (a.primeFactors) c).symm

/-- The sum over `a ≤ A` of the colouring counts is at most the number of
`c`-tuples with product `≤ A`. -/
lemma coloring_sum_le_tupleCard (c A : ℕ) (hc : 1 ≤ c) (hA : 1 ≤ A) :
    (∑ a ∈ Finset.Icc 1 A, (c : ℝ) ^ (a.primeFactors).card) ≤
      ((tupleFinset c A).card : ℝ) := by
  classical
  let ι := {a : ℕ // a ∈ Finset.Icc 1 A}
  letI : Fintype ι := by
    dsimp [ι]
    infer_instance
  letI : DecidableEq ι := by
    dsimp [ι]
    infer_instance
  let g : (Σ a : ι, ↥(a.1.primeFactors) → Fin c) → ↥(tupleFinset c A) := fun x =>
    ⟨pureCoord x.1.1 c x.2, pureCoord_mem_tuple c A
      (by rcases (Finset.mem_Icc.mp x.1.2) with ⟨h1, hA'⟩; omega)
      (by rcases (Finset.mem_Icc.mp x.1.2) with ⟨h1, hA'⟩; omega) x.2⟩
  have hinj : Fintype.card (Σ a : ι, ↥(a.1.primeFactors) → Fin c) ≤
      (tupleFinset c A).card := by
    have hle := Fintype.card_le_of_injective g (by
      intro x y hxy
      rcases x with ⟨a, φ⟩
      rcases y with ⟨b, ψ⟩
      have hfun : pureCoord a.1 c φ = pureCoord b.1 c ψ := by
        simpa [g] using congrArg Subtype.val hxy
      have hprod : a.1 = b.1 := by
        have h1 := pureCoord_prod_eq a.1 c (by
          rcases (Finset.mem_Icc.mp a.2) with ⟨h1, hA'⟩; omega) φ
        have h2 := pureCoord_prod_eq b.1 c (by
          rcases (Finset.mem_Icc.mp b.2) with ⟨h1, hA'⟩; omega) ψ
        calc
          a.1 = ∏ i : Fin c, pureCoord a.1 c φ i := h1.symm
          _ = ∏ i : Fin c, pureCoord b.1 c ψ i := by rw [hfun]
          _ = b.1 := h2
      have hab : b = a := (Subtype.ext hprod).symm
      subst b
      have hfun' : pureCoord a.1 c φ = pureCoord a.1 c ψ := by simpa using hfun
      have hphi : φ = ψ := pureCoord_injective_of a.1 c (by
        rcases (Finset.mem_Icc.mp a.2) with ⟨h1, hA'⟩; omega) hfun'
      rw [hphi])
    rw [Fintype.card_coe] at hle
    exact hle
  calc
    (∑ a ∈ Finset.Icc 1 A, (c : ℝ) ^ (a.primeFactors).card)
        = ∑ a ∈ Finset.Icc 1 A, (Fintype.card (↥(a.primeFactors) → Fin c) : ℝ) := by
            apply Finset.sum_congr rfl
            intro a ha
            exact coloring_pow_eq_card a c
    _ = ∑ a : ι, (Fintype.card (↥(a.1.primeFactors) → Fin c) : ℝ) := by
            rw [← Finset.sum_coe_sort]
    _ = (Fintype.card (Σ a : ι, ↥(a.1.primeFactors) → Fin c) : ℝ) := by
            rw [Fintype.card_sigma]
            norm_cast
    _ ≤ ((tupleFinset c A).card : ℝ) := by exact_mod_cast hinj




theorem omega_color_sum_le_harmonic (c A : ℕ) (hc : 1 ≤ c) (hA : 1 ≤ A) :
    (∑ a ∈ Finset.Icc 1 A, (c : ℝ) ^ (a.primeFactors).card) ≤
      (A : ℝ) * ((∑ k ∈ Finset.Icc 1 A, (1 : ℝ) / (k : ℝ)) ^ (c - 1)) := by
  calc
    (∑ a ∈ Finset.Icc 1 A, (c : ℝ) ^ (a.primeFactors).card)
        ≤ ((tupleFinset c A).card : ℝ) := coloring_sum_le_tupleCard c A hc hA
    _ ≤ (A : ℝ) * (harm A) ^ (c - 1) := tupleFinset_card_le_harm_color c A hA hc
    _ = (A : ℝ) * ((∑ k ∈ Finset.Icc 1 A, (1 : ℝ) / (k : ℝ)) ^ (c - 1)) := by
        simp [harm]


end

end Commons.NumberTheory.Nat