import Mathlib

/-!
# The fibre of a polynomial modulo `p ^ k` and its cover by `p`-adic balls

Vocabulary for `Work.KMTPlan.A6.ConcAux.fibre_ballCover`:
* `fibre p k G = {x < p^k : p^k ∣ G x}` — the representatives of the zero set of `G` mod `p^k`;
* `ball p k m a = {x < p^k : p^m ∣ x - a}` — a `p`-adic ball (residue class mod `p^m`);
* `taylorCoeff H r i` — the `i`-th coefficient of `H(r + X)`, and
  `rescale p H r = H(r + pX)/p` — the rescaled polynomial controlling the fibre above `r mod p`.
-/

namespace Work.KMTPlan.A6.ConcAux

open Polynomial Finset

noncomputable section

variable {p : ℕ}

/-! ## The fibre and its balls -/

/-- The representatives `x < p ^ k` of the fibre `{G = 0}` modulo `p ^ k`. -/
def fibre (p : ℕ) (k : ℕ) (G : ℤ[X]) : Finset ℕ :=
  (Finset.range (p ^ k)).filter (fun x => (p : ℤ) ^ k ∣ G.eval (x : ℤ))

/-- The ball of level `m` around `a` inside `ℤ/p^k`, i.e. the residue class of `a` mod `p^m`. -/
def ball (p : ℕ) (k m : ℕ) (a : ℕ) : Finset ℕ :=
  (Finset.range (p ^ k)).filter (fun x => (p : ℤ) ^ m ∣ (x : ℤ) - (a : ℤ))

@[simp] lemma mem_fibre {k : ℕ} {G : ℤ[X]} {x : ℕ} :
    x ∈ fibre p k G ↔ x < p ^ k ∧ (p : ℤ) ^ k ∣ G.eval (x : ℤ) := by
  simp [fibre]

@[simp] lemma mem_ball {k m a x : ℕ} :
    x ∈ ball p k m a ↔ x < p ^ k ∧ (p : ℤ) ^ m ∣ (x : ℤ) - (a : ℤ) := by
  simp [ball]

lemma ball_self {k m a : ℕ} (ha : a < p ^ k) : a ∈ ball p k m a := by
  rw [mem_ball]
  exact ⟨ha, by simp⟩

lemma ball_mono_level {k m m' a : ℕ} (h : m' ≤ m) : ball p k m a ⊆ ball p k m' a := by
  intro x hx
  rw [mem_ball] at hx ⊢
  exact ⟨hx.1, dvd_trans (pow_dvd_pow (p : ℤ) h) hx.2⟩

lemma ball_subset_range {k m a : ℕ} : ball p k m a ⊆ Finset.range (p ^ k) :=
  fun _ hx => Finset.mem_range.mpr (mem_ball.mp hx).1

lemma fibre_subset_range {k : ℕ} {G : ℤ[X]} : fibre p k G ⊆ Finset.range (p ^ k) :=
  fun _ hx => Finset.mem_range.mpr (mem_fibre.mp hx).1

/-- Membership in a ball depends only on the residue of the centre modulo `p^m`. -/
lemma ball_eq_of_dvd_sub {k m a b : ℕ} (h : (p : ℤ) ^ m ∣ (a : ℤ) - (b : ℤ)) :
    ball p k m a = ball p k m b := by
  ext x
  rw [mem_ball, mem_ball]
  constructor
  · rintro ⟨hx, hxa⟩
    refine ⟨hx, ?_⟩
    have : (x : ℤ) - (b : ℤ) = ((x : ℤ) - (a : ℤ)) + ((a : ℤ) - (b : ℤ)) := by ring
    rw [this]
    exact dvd_add hxa h
  · rintro ⟨hx, hxb⟩
    refine ⟨hx, ?_⟩
    have : (x : ℤ) - (a : ℤ) = ((x : ℤ) - (b : ℤ)) + ((b : ℤ) - (a : ℤ)) := by ring
    rw [this]
    exact dvd_add hxb (by simpa using dvd_neg.mpr h)

/-- Two representatives in `[0, p^k)` that are congruent modulo `p^k` are equal. -/
lemma eq_of_dvd_sub_of_lt (p : ℕ) [Fact p.Prime] {k a x : ℕ} (hx : x < p ^ k) (ha : a < p ^ k)
    (h : (p : ℤ) ^ k ∣ (x : ℤ) - (a : ℤ)) : x = a := by
  obtain ⟨t, ht⟩ := h
  have hpk : (0 : ℤ) < (p : ℤ) ^ k := by
    have h2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast (Fact.out (p := p.Prime)).two_le
    positivity
  have h1 : (x : ℤ) - (a : ℤ) < (p : ℤ) ^ k := by
    have hx' : (x : ℤ) < (p : ℤ) ^ k := by exact_mod_cast hx
    have ha' : (0 : ℤ) ≤ (a : ℤ) := Int.natCast_nonneg a
    linarith
  have h2 : -((p : ℤ) ^ k) < (x : ℤ) - (a : ℤ) := by
    have hx' : (0 : ℤ) ≤ (x : ℤ) := Int.natCast_nonneg x
    have ha' : (a : ℤ) < (p : ℤ) ^ k := by exact_mod_cast ha
    linarith
  have ht0 : t = 0 := by
    rcases lt_trichotomy t 0 with h | h | h
    · nlinarith [ht]
    · exact h
    · have : (1 : ℤ) ≤ t := by omega
      nlinarith [ht]
  rw [ht0, mul_zero] at ht
  have : (x : ℤ) = (a : ℤ) := by linarith
  exact_mod_cast this

/-- The largest level `m ≤ k` of a ball around `a` that is contained in the fibre. -/
def lvl (p : ℕ) (k : ℕ) (G : ℤ[X]) (a : ℕ) : ℕ :=
  Nat.findGreatest (fun m => m ≤ k ∧ ball p k m a ⊆ fibre p k G) k

lemma lvl_le (k : ℕ) (G : ℤ[X]) (a : ℕ) : lvl p k G a ≤ k :=
  Nat.findGreatest_le _

lemma lvl_spec (p : ℕ) [Fact p.Prime] {k : ℕ} {G : ℤ[X]} {a : ℕ} (ha : a ∈ fibre p k G) :
    ball p k (lvl p k G a) a ⊆ fibre p k G := by
  have hmem : a < p ^ k := (mem_fibre.mp ha).1
  have hP : (fun m => m ≤ k ∧ ball p k m a ⊆ fibre p k G) k := by
    refine ⟨le_refl k, ?_⟩
    intro x hx
    rw [mem_ball] at hx
    rw [mem_fibre] at ha ⊢
    have hxa : x = a := eq_of_dvd_sub_of_lt p hx.1 hmem hx.2
    subst hxa
    exact ha
  have := Nat.findGreatest_spec (P := fun m => m ≤ k ∧ ball p k m a ⊆ fibre p k G)
    (le_refl k) hP
  exact this.2

/-- The canonical cover of the fibre by maximal balls. -/
def maxBalls (p : ℕ) (k : ℕ) (G : ℤ[X]) : Finset (Finset ℕ) :=
  (fibre p k G).image (fun a => ball p k (lvl p k G a) a)

lemma mem_maxBalls {k : ℕ} {G : ℤ[X]} {B : Finset ℕ} :
    B ∈ maxBalls p k G ↔ ∃ a ∈ fibre p k G, ball p k (lvl p k G a) a = B := by
  simp [maxBalls]

lemma maxBalls_subset_fibre (p : ℕ) [Fact p.Prime] {k : ℕ} {G : ℤ[X]} {B : Finset ℕ}
    (hB : B ∈ maxBalls p k G) :
    B ⊆ fibre p k G := by
  obtain ⟨a, ha, rfl⟩ := mem_maxBalls.mp hB
  exact lvl_spec p ha

lemma fibre_subset_maxBalls {k : ℕ} {G : ℤ[X]} {x : ℕ} (hx : x ∈ fibre p k G) :
    ∃ B ∈ maxBalls p k G, x ∈ B := by
  refine ⟨ball p k (lvl p k G x) x, mem_maxBalls.mpr ⟨x, hx, rfl⟩, ?_⟩
  exact ball_self (mem_fibre.mp hx).1

/-- The number of balls in the canonical cover of the fibre. -/
def ballCount (p : ℕ) (k : ℕ) (G : ℤ[X]) : ℕ := (maxBalls p k G).card

/-! ## Taylor coefficients and the rescaled polynomial -/

/-- The `i`-th Taylor coefficient of `H` at `r`, i.e. the coefficient of `X^i` in `H(r + X)`. -/
def taylorCoeff (H : ℤ[X]) (r : ℤ) (i : ℕ) : ℤ := (taylor r H).coeff i

lemma taylorCoeff_zero (H : ℤ[X]) (r : ℤ) : taylorCoeff H r 0 = H.eval r :=
  taylor_coeff_zero r H

lemma taylorCoeff_natDegree (H : ℤ[X]) (r : ℤ) :
    taylorCoeff H r H.natDegree = H.leadingCoeff :=
  coeff_taylor_natDegree r H

lemma taylorCoeff_eq_zero_of_lt {H : ℤ[X]} {r : ℤ} {i : ℕ} (hi : H.natDegree < i) :
    taylorCoeff H r i = 0 := by
  rw [taylorCoeff]
  exact coeff_eq_zero_of_natDegree_lt (by rwa [natDegree_taylor])

/-- The rescaled polynomial `H(r + pX)/p`: its fibre at level `j` describes the fibre of `H`
at level `j + 1` above the residue `r mod p`. -/
def rescale (p : ℕ) (H : ℤ[X]) (r : ℤ) : ℤ[X] :=
  ∑ i ∈ Finset.range (H.natDegree + 1),
    C (if i = 0 then H.eval r / (p : ℤ) else taylorCoeff H r i * (p : ℤ) ^ (i - 1)) * X ^ i

lemma rescale_coeff_zero (p : ℕ) (H : ℤ[X]) (r : ℤ) :
    (rescale p H r).coeff 0 = H.eval r / (p : ℤ) := by
  rw [rescale, finsetSum_coeff]
  rw [Finset.sum_eq_single 0]
  · rw [if_pos rfl, coeff_C_mul_X_pow, if_pos rfl]
  · intro b hb hb0
    rw [if_neg hb0, coeff_C_mul_X_pow, if_neg (Ne.symm hb0)]
  · intro hmem
    simp at hmem

lemma rescale_coeff_of_pos (p : ℕ) (H : ℤ[X]) (r : ℤ) {i : ℕ} (hi : 1 ≤ i) :
    (rescale p H r).coeff i = taylorCoeff H r i * (p : ℤ) ^ (i - 1) := by
  rw [rescale, finsetSum_coeff]
  rw [Finset.sum_eq_single i]
  · rw [if_neg (by omega : ¬ i = 0), coeff_C_mul_X_pow, if_pos rfl]
  · intro b hb hbi
    rw [coeff_C_mul_X_pow, if_neg (Ne.symm hbi)]
  · intro hmem
    rw [Finset.mem_range, not_lt] at hmem
    rw [if_neg (by omega : ¬ i = 0)]
    have h0 : taylorCoeff H r i = 0 := taylorCoeff_eq_zero_of_lt (by omega)
    simp [h0]

/-- Coefficients of the dilation `X ↦ pX`. -/
lemma coeff_comp_C_mul_X (Q : ℤ[X]) (p : ℕ) (i : ℕ) :
    (Q.comp (C (p : ℤ) * X)).coeff i = Q.coeff i * (p : ℤ) ^ i := by
  rw [comp_eq_sum_left, coeff_sum, sum_def]
  rw [Finset.sum_eq_single i]
  · rw [show (C (p : ℤ) * X : ℤ[X]) ^ i = C ((p : ℤ) ^ i) * X ^ i by
        rw [mul_pow, ← C_pow]]
    rw [← mul_assoc, ← C_mul, coeff_C_mul_X_pow, if_pos rfl]
  · intro b hb hbi
    rw [show (C (p : ℤ) * X : ℤ[X]) ^ b = C ((p : ℤ) ^ b) * X ^ b by
        rw [mul_pow, ← C_pow]]
    rw [← mul_assoc, ← C_mul, coeff_C_mul_X_pow, if_neg (Ne.symm hbi)]
  · intro hmem
    rw [mem_support_iff, not_not] at hmem
    simp [hmem]

/-- The fundamental identity: `H(r + pX) = p · rescale p H r` when `p ∣ H r`. -/
lemma rescale_comp (p : ℕ) [Fact p.Prime] (H : ℤ[X]) (r : ℤ)
    (hp : (p : ℤ) ∣ H.eval r) :
    H.comp (C r + C (p : ℤ) * X) = C (p : ℤ) * rescale p H r := by
  have hq : (C r + C (p : ℤ) * X : ℤ[X]) = (X + C r).comp (C (p : ℤ) * X) := by
    rw [add_comp, X_comp, C_comp, add_comm]
  have h1 : H.comp (C r + C (p : ℤ) * X) = (taylor r H).comp (C (p : ℤ) * X) := by
    rw [hq, ← comp_assoc, ← taylor_apply]
  rw [h1]
  ext i
  rw [coeff_comp_C_mul_X, coeff_C_mul]
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    rw [rescale_coeff_zero, taylor_coeff_zero, pow_zero, mul_one]
    exact (Int.mul_ediv_cancel' hp).symm
  · rw [rescale_coeff_of_pos p H r hi, taylorCoeff]
    have hpow : (p : ℤ) * (p : ℤ) ^ (i - 1) = (p : ℤ) ^ i := by
      rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hi]
    rw [← hpow]
    ring

/-- Evaluation of the rescaled polynomial. -/
lemma rescale_eval (p : ℕ) [Fact p.Prime] (H : ℤ[X]) (r : ℤ)
    (hp : (p : ℤ) ∣ H.eval r) (t : ℤ) :
    (rescale p H r).eval t = H.eval (r + (p : ℤ) * t) / (p : ℤ) := by
  have h2 : (p : ℤ) * (rescale p H r).eval t = H.eval (r + (p : ℤ) * t) := by
    have h := congrArg (fun q : ℤ[X] => q.eval t) (rescale_comp p H r hp)
    simpa [eval_comp, eval_add, eval_mul] using h.symm
  rw [← h2, Int.mul_ediv_cancel_left]
  have h2' : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast (Fact.out (p := p.Prime)).two_le
  omega

/-- The degree of the rescaled polynomial is unchanged. -/
lemma rescale_natDegree (p : ℕ) [Fact p.Prime] (H : ℤ[X]) (r : ℤ) (hH : H ≠ 0)
    (hd : 1 ≤ H.natDegree) :
    (rescale p H r).natDegree = H.natDegree := by
  refine le_antisymm ?_ ?_
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rcases Nat.eq_zero_or_pos N with h | h
    · omega
    · rw [rescale_coeff_of_pos p H r h]
      rw [taylorCoeff_eq_zero_of_lt hN, zero_mul]
  · refine le_natDegree_of_ne_zero ?_
    rw [rescale_coeff_of_pos p H r hd]
    have hp0 : (p : ℤ) ≠ 0 := by
      have h2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast (Fact.out (p := p.Prime)).two_le
      omega
    rw [taylorCoeff_natDegree]
    exact mul_ne_zero (leadingCoeff_ne_zero.mpr hH) (pow_ne_zero _ hp0)

/-- The roots of `H` modulo `p`, as representatives in `[0, p)`. -/
def roots (p : ℕ) (H : ℤ[X]) : Finset ℕ :=
  (Finset.range p).filter (fun r => (p : ℤ) ∣ H.eval (r : ℤ))

@[simp] lemma mem_roots {H : ℤ[X]} {r : ℕ} :
    r ∈ roots p H ↔ r < p ∧ (p : ℤ) ∣ H.eval (r : ℤ) := by
  simp [roots]

end

end Work.KMTPlan.A6.ConcAux
