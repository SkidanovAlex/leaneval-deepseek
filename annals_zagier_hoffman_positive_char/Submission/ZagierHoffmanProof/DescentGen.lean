import Submission.ZagierHoffmanProof.Descent
import Submission.Commons.Data.Nat.div_pow_add_mul_mod

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Polynomial
open scoped BigOperators

/-!
# The general Frobenius descent for the Anderson–Thakur coefficients

`Descent.lean` implements Chen's descent for the *single* residue pattern `(q-1, 0, 0, …)`, which
computes `c_{q^M - 1}`.  The general case of Chen's Theorem 3.3 (arXiv:1506.06463) requires the
descent for an **arbitrary** residue vector `res` (`res_i < q`), i.e. the grouping of the no-carry
multiplicity vectors `a` of `N` by their residues `a mod q`:

* `a = q * b + res` with `b = a / q`;
* `NoCarryVec a ↔ NoCarryVec res ∧ NoCarryVec b` (the base-`p` digits separate!);
* `C_a = C_res * C_b` (Dickson's reduction `Combinatorics.Multinomial.digit_reduction`);
* `∏ E_i^{a_i} = (∏ E_i^{res_i}) * (∏ E_i^{b_i})^q`.

Summing over `b` and applying the freshman's dream turns the level-`N` partition sum into a sum over
residues of `(coefficient) * (level-`m'` partition sum)^q`, with `m' = (N - ∑ res_i q^i)/q`.  This is
the engine of Chen's Step 1 (single `N_i`) and Step 2 (general `N_i`).
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

/-- A residue vector `res : Fin B → ℕ` has all entries `< q = Nat.card F`. -/
def IsResidueVec {B : ℕ} (res : Fin B → ℕ) : Prop := ∀ i, res i < Nat.card F

/-- The **general ascent** of a multiplicity vector along a residue vector:
`b ↦ (k ↦ q * b k + res k)`. -/
noncomputable def ascentGen {B : ℕ} (res b : Fin B → ℕ) : Fin B → ℕ :=
  fun k => Nat.card F * b k + res k

lemma ascentGen_apply {B : ℕ} (res b : Fin B → ℕ) (k : Fin B) :
    ascentGen F res b k = Nat.card F * b k + res k := rfl

/-- The base-`p` digit formula for the general ascent. -/
lemma ascentGen_digit {B l : ℕ} (hp : 2 ≤ ringChar F) (hpq : Nat.card F = ringChar F ^ l)
    {res b : Fin B → ℕ} (hres : IsResidueVec F res) (k : Fin B) (j : ℕ) :
    ascentGen F res b k / (ringChar F) ^ j % (ringChar F)
      = if j < l then res k / (ringChar F) ^ j % (ringChar F)
        else b k / (ringChar F) ^ (j - l) % (ringChar F) := by
  have hk : res k < ringChar F ^ l := by rw [← hpq]; exact hres k
  rw [ascentGen_apply, hpq]
  exact Commons.Data.Nat.div_pow_add_mul_mod (ringChar F) l hp hk j

/-- The sum of the `j`-th base-`p` digits of the general ascent. -/
lemma sum_digit_ascentGen {B l : ℕ} (hp : 2 ≤ ringChar F) (hpq : Nat.card F = ringChar F ^ l)
    {res b : Fin B → ℕ} (hres : IsResidueVec F res) (j : ℕ) :
    (∑ k : Fin B, ascentGen F res b k / (ringChar F) ^ j % (ringChar F))
      = if j < l then ∑ k : Fin B, res k / (ringChar F) ^ j % (ringChar F)
        else ∑ k : Fin B, b k / (ringChar F) ^ (j - l) % (ringChar F) := by
  by_cases hj : j < l
  · rw [if_pos hj, Finset.sum_congr rfl (fun k _ => by rw [ascentGen_digit F hp hpq hres k j, if_pos hj])]
  · rw [if_neg hj, Finset.sum_congr rfl (fun k _ => by rw [ascentGen_digit F hp hpq hres k j, if_neg hj])]

/-- **The no-carry condition separates along the descent**: `q * b + res` has no carries in base
`p` exactly when both `res` and `b` have no carries. -/
theorem noCarryVec_ascentGen_iff {B l : ℕ} (hp : 2 ≤ ringChar F)
    (hpq : Nat.card F = ringChar F ^ l) {res b : Fin B → ℕ} (hres : IsResidueVec F res) :
    NoCarryVec F (ascentGen F res b) ↔ NoCarryVec F res ∧ NoCarryVec F b := by
  have hp1 : 1 ≤ ringChar F := by omega
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  constructor
  · intro h
    refine ⟨fun j => ?_, fun j => ?_⟩
    · rcases lt_or_ge j l with hj | hj
      · have := h j
        rwa [sum_digit_ascentGen F hp hpq hres j, if_pos hj] at this
      · have hzero : ∀ k : Fin B, res k / (ringChar F) ^ j % (ringChar F) = 0 := by
          intro k
          have h1 : res k < (ringChar F) ^ j := by
            have h3 : (ringChar F) ^ l ≤ (ringChar F) ^ j := Nat.pow_le_pow_right hp1 hj
            have h4 : Nat.card F ≤ (ringChar F) ^ j := by rw [hpq]; exact h3
            have := hres k; omega
          rw [Nat.div_eq_of_lt h1, Nat.zero_mod]
        rw [Finset.sum_congr rfl (fun k _ => hzero k), Finset.sum_const_zero]
        omega
    · have := h (j + l)
      rw [sum_digit_ascentGen F hp hpq hres (j + l), if_neg (by omega : ¬ j + l < l),
        Nat.add_sub_cancel] at this
      exact this
  · rintro ⟨hr, hb⟩ j
    rw [sum_digit_ascentGen F hp hpq hres j]
    by_cases hj : j < l
    · rw [if_pos hj]; exact hr j
    · rw [if_neg hj]; exact hb (j - l)

/-- The base-`p` digits of the quotient `a k / q` are the shifted digits of `a k`:
`(a k / q) / p^j % p = a k / p^(j+l) % p`. -/
lemma quotient_digit {B l : ℕ} (hp : 2 ≤ ringChar F) (hpq : Nat.card F = ringChar F ^ l)
    (a : Fin B → ℕ) (k : Fin B) (j : ℕ) :
    (a k / Nat.card F) / (ringChar F) ^ j % (ringChar F)
      = a k / (ringChar F) ^ (j + l) % (ringChar F) := by
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  have hlt : a k % Nat.card F < ringChar F ^ l := by rw [← hpq]; exact Nat.mod_lt _ (by omega)
  have h1 : a k = ringChar F ^ l * (a k / Nat.card F) + a k % Nat.card F := by
    rw [← hpq]; exact (Nat.div_add_mod (a k) (Nat.card F)).symm
  conv_rhs => rw [h1]
  rw [Commons.Data.Nat.div_pow_add_mul_mod (ringChar F) l hp hlt (j + l),
    if_neg (by omega : ¬ j + l < l), Nat.add_sub_cancel]

/-- The low base-`p` digits of `a k` are the digits of its remainder `a k % q`:
`(a k % q) / p^j % p = a k / p^j % p` for `j < l`. -/
lemma mod_digit {B l : ℕ} (hp : 2 ≤ ringChar F) (hpq : Nat.card F = ringChar F ^ l)
    (a : Fin B → ℕ) (k : Fin B) {j : ℕ} (hj : j < l) :
    (a k % Nat.card F) / (ringChar F) ^ j % (ringChar F)
      = a k / (ringChar F) ^ j % (ringChar F) := by
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  have hlt : a k % Nat.card F < ringChar F ^ l := by rw [← hpq]; exact Nat.mod_lt _ (by omega)
  have h1 : a k = ringChar F ^ l * (a k / Nat.card F) + a k % Nat.card F := by
    rw [← hpq]; exact (Nat.div_add_mod (a k) (Nat.card F)).symm
  conv_rhs => rw [h1]
  rw [Commons.Data.Nat.div_pow_add_mul_mod (ringChar F) l hp hlt j, if_pos hj]

/-- The **descent preserves the no-carry condition**: `a ↦ a / q`. -/
lemma noCarryVec_div {B l : ℕ} (hp : 2 ≤ ringChar F) (hpq : Nat.card F = ringChar F ^ l)
    (a : Fin B → ℕ) (hnc : NoCarryVec F a) :
    NoCarryVec F (fun k => a k / Nat.card F) := by
  intro j
  calc (∑ i : Fin B, (fun k => a k / Nat.card F) i / (ringChar F) ^ j % (ringChar F))
      = ∑ i : Fin B, a i / (ringChar F) ^ (j + l) % (ringChar F) :=
        Finset.sum_congr rfl (fun i _ => quotient_digit F hp hpq a i j)
    _ < ringChar F := hnc (j + l)

/-- The **remainder vector of a no-carry vector has no carries**. -/
lemma noCarryVec_mod {B l : ℕ} (hp : 2 ≤ ringChar F) (hpq : Nat.card F = ringChar F ^ l)
    (a : Fin B → ℕ) (hnc : NoCarryVec F a) :
    NoCarryVec F (fun k => a k % Nat.card F) := by
  have hp1 : 1 ≤ ringChar F := by omega
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  intro j
  rcases lt_or_ge j l with hj | hj
  · calc (∑ i : Fin B, (fun k => a k % Nat.card F) i / (ringChar F) ^ j % (ringChar F))
        = ∑ i : Fin B, a i / (ringChar F) ^ j % (ringChar F) :=
          Finset.sum_congr rfl (fun i _ => mod_digit F hp hpq a i hj)
      _ < ringChar F := hnc j
  · have hzero : ∀ i : Fin B, a i % Nat.card F / (ringChar F) ^ j % (ringChar F) = 0 := by
      intro i
      have h1 : a i % Nat.card F < Nat.card F := Nat.mod_lt _ (by omega)
      have h3 : Nat.card F ≤ (ringChar F) ^ j := by rw [hpq]; exact Nat.pow_le_pow_right hp1 hj
      rw [Nat.div_eq_of_lt (lt_of_lt_of_le h1 h3), Nat.zero_mod]
    calc (∑ i : Fin B, (fun k => a k % Nat.card F) i / (ringChar F) ^ j % (ringChar F))
        = ∑ i : Fin B, (0 : ℕ) := Finset.sum_congr rfl (fun i _ => hzero i)
      _ = 0 := Finset.sum_const_zero
      _ < ringChar F := by omega

/-- **A no-carry vector with all entries `< p^l` has entry sum `≤ p^l - 1`.**  Indeed
`∑_i v_i = ∑_{j<l} p^j · ∑_i (v_i/p^j % p)` and each inner column sum is `< p` by the no-carry
condition.  (Proved by induction on `l`, peeling off the lowest digit.) -/
lemma sum_le_pow_sub_one_of_digits (p : ℕ) (hp : 2 ≤ p) :
    ∀ l (B : ℕ) (v : Fin B → ℕ), (∀ i, v i < p ^ l)
      → (∀ j, (∑ i, v i / p ^ j % p) < p) → (∑ i, v i) ≤ p ^ l - 1 := by
  intro l
  induction l with
  | zero =>
    intro B v hlt _
    have hzero : ∀ i : Fin B, v i = 0 := fun i => Nat.lt_one_iff.mp (by simpa using hlt i)
    simp [hzero]
  | succ l ih =>
    intro B v hlt hnc
    have hsplit : ∀ i : Fin B, v i = v i % p + p * (v i / p) := fun i =>
      (Nat.mod_add_div (v i) p).symm
    have hsum : (∑ i : Fin B, v i)
        = (∑ i : Fin B, v i % p) + p * (∑ i : Fin B, v i / p) := by
      rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib, Finset.mul_sum]
    have hd0 : (∑ i : Fin B, v i % p) ≤ p - 1 := by
      have := hnc 0
      simp only [pow_zero, Nat.div_one] at this
      omega
    have hdiv_lt : ∀ i : Fin B, v i / p < p ^ l := by
      intro i
      have h1 : v i < p * p ^ l := by
        rw [← pow_succ']; exact hlt i
      exact Nat.div_lt_of_lt_mul h1
    have hdiv_nc : ∀ j, (∑ i : Fin B, v i / p / p ^ j % p) < p := by
      intro j
      have h := hnc (j + 1)
      refine lt_of_eq_of_lt (Finset.sum_congr rfl (fun i _ => ?_)) h
      rw [pow_succ', Nat.div_div_eq_div_mul]
    obtain hih := ih B (fun i : Fin B => v i / p) hdiv_lt hdiv_nc
    have h3 : p * (p ^ l - 1) = p * p ^ l - p := by
      rw [Nat.mul_sub_left_distrib, mul_one]
    have h2 : p * (∑ i : Fin B, v i / p) ≤ p * p ^ l - p := by
      rw [← h3]; exact Nat.mul_le_mul_left _ hih
    have h4 : (p - 1) + (p * p ^ l - p) = p * p ^ l - 1 := by
      have hP : p ≤ p * p ^ l := Nat.le_mul_of_pos_right p (Nat.pow_pos (by omega : 0 < p))
      omega
    rw [hsum, pow_succ]
    calc (∑ i : Fin B, v i % p) + p * (∑ i : Fin B, v i / p)
        ≤ (p - 1) + (p * p ^ l - p) := Nat.add_le_add hd0 h2
      _ = p ^ l * p - 1 := by rw [h4, mul_comm]

/-- ★★ **A no-carry residue vector has entry sum at most `q - 1`.**  This is the fact (implicit in
Chen's proof) that makes every reduced index produced by the descent have the shape
`q^(M-1) - ∑ N'_j q^j - 1` with `∑ N'_j ≤ q - 1`, so that the induction hypothesis applies. -/
theorem sum_le_card_sub_one_of_noCarryVec {B : ℕ} {res : Fin B → ℕ}
    (hres : IsResidueVec F res) (hnc : NoCarryVec F res) :
    (∑ i, res i) ≤ Nat.card F - 1 := by
  obtain ⟨l, hp, hpq⟩ := card_eq_ringChar_pow F
  have hp2 : 2 ≤ ringChar F := hp.two_le
  have h := sum_le_pow_sub_one_of_digits (ringChar F) hp2 l B res
    (fun i => by rw [← hpq]; exact hres i) hnc
  rwa [← hpq] at h

/-- The partition relation along the general ascent:
`∑_k (q * b_k + res_k) q^k = q * (∑_k b_k q^k) + ∑_k res_k q^k`. -/
lemma ascentGen_sum {B : ℕ} (res b : Fin B → ℕ) :
    (∑ k : Fin B, ascentGen F res b k * Nat.card F ^ ((k : ℕ)))
      = Nat.card F * (∑ k : Fin B, b k * Nat.card F ^ ((k : ℕ)))
        + (∑ k : Fin B, res k * Nat.card F ^ ((k : ℕ))) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [ascentGen_apply]; ring

/-- The quotient/remainder laws of the general ascent. -/
lemma ascentGen_div {B : ℕ} {res : Fin B → ℕ} (hres : IsResidueVec F res) (b : Fin B → ℕ)
    (k : Fin B) : ascentGen F res b k / Nat.card F = b k := by
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  rw [ascentGen_apply, Nat.add_comm, Nat.add_mul_div_left _ _ (by omega : 0 < Nat.card F),
    Nat.div_eq_of_lt (hres k), zero_add]

lemma ascentGen_mod {B : ℕ} (res b : Fin B → ℕ) (k : Fin B) :
    ascentGen F res b k % Nat.card F = res k % Nat.card F := by
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  rw [ascentGen_apply, Nat.add_comm, Nat.add_mul_mod_self_left]

lemma ascentGen_mod_of_lt {B : ℕ} {res : Fin B → ℕ} (hres : IsResidueVec F res) (b : Fin B → ℕ)
    (k : Fin B) : ascentGen F res b k % Nat.card F = res k := by
  rw [ascentGen_mod, Nat.mod_eq_of_lt (hres k)]

lemma descentGen_ascentGen {B : ℕ} {res : Fin B → ℕ} (hres : IsResidueVec F res) (b : Fin B → ℕ) :
    (fun k => ascentGen F res b k / Nat.card F) = b :=
  funext (fun k => ascentGen_div F hres b k)

/-- The coefficient `γ_i / D_i` of the Anderson–Thakur recursion. -/
noncomputable def atE (i : ℕ) : atQ F := atGamma F i * (atD F i)⁻¹

lemma atE_apply (i : ℕ) : atE F i = atGamma F i * (atD F i)⁻¹ := rfl

/-- The product `∏_i (γ_i/D_i)^{a_i}` along the general ascent picks up a `q`-th power. -/
lemma prod_ascentGen {B : ℕ} (res b : Fin B → ℕ) :
    (∏ i : Fin B, atE F ((i : ℕ)) ^ (ascentGen F res b i))
      = (∏ i : Fin B, atE F ((i : ℕ)) ^ (res i))
        * (∏ i : Fin B, atE F ((i : ℕ)) ^ (b i)) ^ (Nat.card F) := by
  rw [Finset.prod_congr rfl (fun i _ => by
    rw [ascentGen_apply, pow_add, mul_comm (Nat.card F) (b i), pow_mul]), Finset.prod_mul_distrib,
    Finset.prod_pow, mul_comm]

/-- **Dickson's reduction along the general ascent**: `C_{q b + res} = C_res * C_b` in `atQ F`. -/
lemma multinomial_ascentGen {B l : ℕ} (hp : (ringChar F).Prime) (hpq : Nat.card F = ringChar F ^ l)
    {res : Fin B → ℕ} (hres : IsResidueVec F res) (b : Fin B → ℕ) :
    ((Nat.multinomial Finset.univ (ascentGen F res b) : ℕ) : atQ F)
      = ((Nat.multinomial Finset.univ res : ℕ) : atQ F)
        * ((Nat.multinomial Finset.univ b : ℕ) : atQ F) := by
  have hmod : (fun i : Fin B => ascentGen F res b i % ringChar F ^ l) = res := by
    funext i; rw [← hpq]; exact ascentGen_mod_of_lt F hres b i
  have hdiv : (fun i : Fin B => ascentGen F res b i / ringChar F ^ l) = b := by
    funext i; rw [← hpq]; exact ascentGen_div F hres b i
  have hz : ((Nat.multinomial Finset.univ (ascentGen F res b) : ℕ) : ZMod (ringChar F))
      = ((Nat.multinomial Finset.univ res * Nat.multinomial Finset.univ b : ℕ) : ZMod (ringChar F)) := by
    rw [Nat.cast_mul,
      Commons.Combinatorics.Multinomial.digit_reduction (ringChar F) l hp (ascentGen F res b), hmod, hdiv]
  have heq := (CharP.cast_eq_iff_mod_eq (R := atQ F) (p := ringChar F)).mpr
    ((ZMod.natCast_eq_natCast_iff _ _ (ringChar F)).mp hz)
  rwa [Nat.cast_mul] at heq

/-- The level-`M` index set of the multinomial expansion of `atCoeff F M`: the no-carry
multiplicity vectors with entries `≤ M` and `∑_i b_i q^i = M`. -/
noncomputable def atSumSet (M B : ℕ) : Finset (Fin B → ℕ) := by
  classical
  exact (Fintype.piFinset fun _ : Fin B => Finset.range (M + 1)).filter
    (fun b : Fin B → ℕ => (∑ i, b i * Nat.card F ^ (i : ℕ)) = M ∧ NoCarryVec F b)

/-- The level-`M` partition sum `∑_b C_b ∏_i (γ_i/D_i)^{b_i}`. -/
noncomputable def atSum (M B : ℕ) : atQ F :=
  ∑ b ∈ atSumSet F M B, ((Nat.multinomial Finset.univ b : ℕ) : atQ F)
    * ∏ i : Fin B, atE F ((i : ℕ)) ^ (b i)

/-- **Chen's Lemma 2.6(a)**, in terms of the level sum. -/
theorem atCoeff_eq_atSum (N B : ℕ) (hB : N + 1 ≤ B) : atCoeff F N = atSum F N B :=
  atCoeff_eq_sum_multi F N B hB

/-- The set of residue vectors that occur in the descent from level `N`. -/
noncomputable def residueSet (N B : ℕ) : Finset (Fin B → ℕ) := by
  classical
  exact (Fintype.piFinset fun _ : Fin B => Finset.range (Nat.card F)).filter
    (fun res : Fin B → ℕ => (∑ i, res i * Nat.card F ^ (i : ℕ)) ≤ N
      ∧ Nat.card F ∣ (N - ∑ i, res i * Nat.card F ^ (i : ℕ))
      ∧ IsResidueVec F res ∧ NoCarryVec F res)

lemma mem_residueSet {N B : ℕ} {res : Fin B → ℕ} :
    res ∈ residueSet F N B ↔ (∑ i, res i * Nat.card F ^ (i : ℕ)) ≤ N
      ∧ Nat.card F ∣ (N - ∑ i, res i * Nat.card F ^ (i : ℕ))
      ∧ IsResidueVec F res ∧ NoCarryVec F res := by
  classical
  rw [residueSet, Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h
    exact ⟨fun i => Finset.mem_range.mpr (h.2.2.1 i), h⟩

lemma mem_atSumSet {M B : ℕ} {b : Fin B → ℕ} :
    b ∈ atSumSet F M B ↔ (∀ i, b i ≤ M) ∧ (∑ i, b i * Nat.card F ^ (i : ℕ)) = M
      ∧ NoCarryVec F b := by
  classical
  rw [atSumSet, Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨hb, h⟩
    exact ⟨fun i => Nat.lt_succ_iff.mp (Finset.mem_range.mp (hb i)), h⟩
  · rintro ⟨hb, h⟩
    exact ⟨fun i => Finset.mem_range.mpr (Nat.lt_succ_of_le (hb i)), h⟩

/-- The residue vector of a level-`N` no-carry vector belongs to the residue set. -/
theorem mod_mem_residueSet {N B : ℕ} {a : Fin B → ℕ} (ha : a ∈ atSumSet F N B) :
    (fun i => a i % Nat.card F) ∈ residueSet F N B := by
  classical
  obtain ⟨l, hp, hpq⟩ := card_eq_ringChar_pow F
  have hp2 : 2 ≤ ringChar F := hp.two_le
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  obtain ⟨-, hsum, hnc⟩ := (mem_atSumSet F).mp ha
  rw [mem_residueSet]
  have hdecomp : ∀ i : Fin B,
      a i * Nat.card F ^ (i : ℕ)
        = Nat.card F * ((a i / Nat.card F) * Nat.card F ^ (i : ℕ))
          + (a i % Nat.card F) * Nat.card F ^ (i : ℕ) := by
    intro i
    conv_lhs => rw [← Nat.div_add_mod (a i) (Nat.card F)]
    ring
  have hsplit : (∑ i : Fin B, a i * Nat.card F ^ (i : ℕ))
      = Nat.card F * (∑ i : Fin B, (a i / Nat.card F) * Nat.card F ^ (i : ℕ))
        + (∑ i : Fin B, (a i % Nat.card F) * Nat.card F ^ (i : ℕ)) := by
    calc (∑ i : Fin B, a i * Nat.card F ^ (i : ℕ))
        = ∑ i : Fin B, (Nat.card F * ((a i / Nat.card F) * Nat.card F ^ (i : ℕ))
            + (a i % Nat.card F) * Nat.card F ^ (i : ℕ)) :=
          Finset.sum_congr rfl (fun i _ => hdecomp i)
      _ = Nat.card F * (∑ i : Fin B, (a i / Nat.card F) * Nat.card F ^ (i : ℕ))
            + (∑ i : Fin B, (a i % Nat.card F) * Nat.card F ^ (i : ℕ)) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : (∑ i : Fin B, (a i % Nat.card F) * Nat.card F ^ (i : ℕ))
        ≤ ∑ i : Fin B, a i * Nat.card F ^ (i : ℕ) := by
      rw [hsplit]
      exact Nat.le_add_left _ _
    rw [hsum] at h1
    exact h1
  · refine ⟨∑ i : Fin B, (a i / Nat.card F) * Nat.card F ^ (i : ℕ), ?_⟩
    rw [hsum] at hsplit
    omega
  · intro i; exact Nat.mod_lt _ (by omega)
  · exact noCarryVec_mod F hp2 hpq a hnc


/-- **The descent lands in the reduced level set.**  If `a` is a level-`N` no-carry vector whose
residue vector is `res`, then `a / q` is a level-`m'` no-carry vector with
`m' = (N - ∑ res_i q^i) / q`. -/
lemma descentMem {N B : ℕ} {res : Fin B → ℕ} (hres : res ∈ residueSet F N B) {a : Fin B → ℕ}
    (ha : a ∈ atSumSet F N B) (hmod : (fun i => a i % Nat.card F) = res) :
    (fun i => a i / Nat.card F)
      ∈ atSumSet F ((N - ∑ i, res i * Nat.card F ^ (i : ℕ)) / Nat.card F) B := by
  classical
  obtain ⟨l, hp, hpq⟩ := card_eq_ringChar_pow F
  have hp2 : 2 ≤ ringChar F := hp.two_le
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  obtain ⟨hle, hdvd, hresv, hresnc⟩ := (mem_residueSet F).mp hres
  obtain ⟨hab, hsum, hnc⟩ := (mem_atSumSet F).mp ha
  rw [mem_atSumSet]
  have hdecomp : ∀ i : Fin B, a i = Nat.card F * (a i / Nat.card F) + res i := by
    intro i
    have h1 : a i % Nat.card F = res i := congrFun hmod i
    conv_lhs => rw [← Nat.div_add_mod (a i) (Nat.card F)]
    rw [h1]
  have hsplit : (∑ i : Fin B, a i * Nat.card F ^ (i : ℕ))
      = Nat.card F * (∑ i : Fin B, (a i / Nat.card F) * Nat.card F ^ (i : ℕ))
        + (∑ i : Fin B, res i * Nat.card F ^ (i : ℕ)) := by
    calc (∑ i : Fin B, a i * Nat.card F ^ (i : ℕ))
        = ∑ i : Fin B, (Nat.card F * ((a i / Nat.card F) * Nat.card F ^ (i : ℕ))
            + res i * Nat.card F ^ (i : ℕ)) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          conv_lhs => rw [hdecomp i]
          ring
      _ = Nat.card F * (∑ i : Fin B, (a i / Nat.card F) * Nat.card F ^ (i : ℕ))
            + (∑ i : Fin B, res i * Nat.card F ^ (i : ℕ)) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hmul : Nat.card F * ((N - ∑ i : Fin B, res i * Nat.card F ^ (i : ℕ)) / Nat.card F)
      = N - ∑ i : Fin B, res i * Nat.card F ^ (i : ℕ) := Nat.mul_div_cancel' hdvd
  have hsum' : (∑ i : Fin B, (a i / Nat.card F) * Nat.card F ^ (i : ℕ))
      = (N - ∑ i : Fin B, res i * Nat.card F ^ (i : ℕ)) / Nat.card F := by
    rw [hsum] at hsplit
    have h2 : Nat.card F * (∑ i : Fin B, (a i / Nat.card F) * Nat.card F ^ (i : ℕ))
        = Nat.card F * ((N - ∑ i : Fin B, res i * Nat.card F ^ (i : ℕ)) / Nat.card F) := by
      rw [hmul]; omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) h2
  refine ⟨?_, hsum', noCarryVec_div F hp2 hpq a hnc⟩
  intro i
  have h3 : (a i / Nat.card F) * Nat.card F ^ (i : ℕ)
      ≤ ∑ j : Fin B, (a j / Nat.card F) * Nat.card F ^ (j : ℕ) :=
    Finset.single_le_sum (f := fun j : Fin B => (a j / Nat.card F) * Nat.card F ^ (j : ℕ))
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [hsum'] at h3
  refine le_trans ?_ h3
  calc a i / Nat.card F = (a i / Nat.card F) * 1 := (mul_one _).symm
    _ ≤ (a i / Nat.card F) * Nat.card F ^ (i : ℕ) :=
        Nat.mul_le_mul_left _ (Nat.one_le_pow i (Nat.card F) (by omega))

/-- **The ascent lands back in the level-`N` set** with residue vector `res`. -/
lemma ascentMem {N B : ℕ} {res : Fin B → ℕ} (hres : res ∈ residueSet F N B) {b : Fin B → ℕ}
    (hb : b ∈ atSumSet F ((N - ∑ i, res i * Nat.card F ^ (i : ℕ)) / Nat.card F) B) :
    ascentGen F res b ∈ atSumSet F N B
      ∧ (fun i => ascentGen F res b i % Nat.card F) = res := by
  classical
  obtain ⟨l, hp, hpq⟩ := card_eq_ringChar_pow F
  have hp2 : 2 ≤ ringChar F := hp.two_le
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  obtain ⟨hle, hdvd, hresv, hresnc⟩ := (mem_residueSet F).mp hres
  obtain ⟨hbb, hbsum, hbnc⟩ := (mem_atSumSet F).mp hb
  have hmul : Nat.card F * ((N - ∑ i : Fin B, res i * Nat.card F ^ (i : ℕ)) / Nat.card F)
      = N - ∑ i : Fin B, res i * Nat.card F ^ (i : ℕ) := Nat.mul_div_cancel' hdvd
  have hsum_res : (∑ i : Fin B, ascentGen F res b i * Nat.card F ^ (i : ℕ))
      = Nat.card F * ((N - ∑ i : Fin B, res i * Nat.card F ^ (i : ℕ)) / Nat.card F)
        + (∑ i : Fin B, res i * Nat.card F ^ (i : ℕ)) := by
    rw [ascentGen_sum, hbsum]
  have hsumN : (∑ i : Fin B, ascentGen F res b i * Nat.card F ^ (i : ℕ)) = N := by
    rw [hsum_res, hmul]; omega
  refine ⟨?_, ?_⟩
  · rw [mem_atSumSet]
    refine ⟨?_, hsumN, (noCarryVec_ascentGen_iff F hp2 hpq hresv).mpr ⟨hresnc, hbnc⟩⟩
    intro i
    have hb1 : b i ≤ (N - ∑ j : Fin B, res j * Nat.card F ^ (j : ℕ)) / Nat.card F := by
      have h3 : b i * Nat.card F ^ (i : ℕ)
          ≤ ∑ j : Fin B, b j * Nat.card F ^ (j : ℕ) :=
        Finset.single_le_sum (f := fun j : Fin B => b j * Nat.card F ^ (j : ℕ))
          (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
      rw [hbsum] at h3
      refine le_trans ?_ h3
      calc b i = b i * 1 := (mul_one _).symm
        _ ≤ b i * Nat.card F ^ (i : ℕ) :=
            Nat.mul_le_mul_left _ (Nat.one_le_pow i (Nat.card F) (by omega))
    have hres1 : res i ≤ ∑ j : Fin B, res j * Nat.card F ^ (j : ℕ) :=
      calc res i = res i * 1 := (mul_one _).symm
        _ ≤ res i * Nat.card F ^ (i : ℕ) :=
            Nat.mul_le_mul_left _ (Nat.one_le_pow i (Nat.card F) (by omega))
        _ ≤ ∑ j : Fin B, res j * Nat.card F ^ (j : ℕ) :=
            Finset.single_le_sum (f := fun j : Fin B => res j * Nat.card F ^ (j : ℕ))
              (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    have h4 : Nat.card F * ((N - ∑ j : Fin B, res j * Nat.card F ^ (j : ℕ)) / Nat.card F)
        = N - ∑ j : Fin B, res j * Nat.card F ^ (j : ℕ) := Nat.mul_div_cancel' hdvd
    calc ascentGen F res b i = Nat.card F * b i + res i := ascentGen_apply F res b i
      _ ≤ Nat.card F * ((N - ∑ j : Fin B, res j * Nat.card F ^ (j : ℕ)) / Nat.card F)
            + (∑ j : Fin B, res j * Nat.card F ^ (j : ℕ)) :=
          Nat.add_le_add (Nat.mul_le_mul_left _ hb1) hres1
      _ = N := by rw [h4]; omega
  · funext i
    exact ascentGen_mod_of_lt F hresv b i


/-- The ascent of the descent of a vector with residue vector `res` gives back the vector. -/
lemma ascentGen_self {B : ℕ} {res a : Fin B → ℕ} (hmod : ∀ i, a i % Nat.card F = res i) :
    ascentGen F res (fun i => a i / Nat.card F) = a := by
  funext i
  show Nat.card F * (a i / Nat.card F) + res i = a i
  rw [← hmod i]
  exact Nat.div_add_mod (a i) (Nat.card F)

open Classical in
/-- **The fibre sum**: grouping the level-`N` partition sum by the residue vector gives, for each
residue `res`, a `q`-th power of the reduced partition sum times the residue coefficient. -/
lemma atSum_fiber {N B : ℕ} {res : Fin B → ℕ} (hres : res ∈ residueSet F N B) :
    (∑ a ∈ (atSumSet F N B).filter (fun a => (fun i => a i % Nat.card F) = res),
        ((Nat.multinomial Finset.univ a : ℕ) : atQ F)
          * ∏ i : Fin B, atE F ((i : ℕ)) ^ (a i))
      = (((Nat.multinomial Finset.univ res : ℕ) : atQ F)
            * ∏ i : Fin B, atE F ((i : ℕ)) ^ (res i))
          * (atSum F ((N - ∑ i, res i * Nat.card F ^ (i : ℕ)) / Nat.card F) B) ^ (Nat.card F) := by
  classical
  obtain ⟨l, hp, hpq⟩ := card_eq_ringChar_pow F
  obtain ⟨hle, hdvd, hresv, hresnc⟩ := (mem_residueSet F).mp hres
  have hbij := Finset.sum_bij'
    (s := (atSumSet F N B).filter (fun a => (fun i => a i % Nat.card F) = res))
    (t := atSumSet F ((N - ∑ i, res i * Nat.card F ^ (i : ℕ)) / Nat.card F) B)
    (f := fun a => ((Nat.multinomial Finset.univ a : ℕ) : atQ F)
          * ∏ i : Fin B, atE F ((i : ℕ)) ^ (a i))
    (g := fun b => (((Nat.multinomial Finset.univ res : ℕ) : atQ F)
            * ∏ i : Fin B, atE F ((i : ℕ)) ^ (res i))
          * (((Nat.multinomial Finset.univ b : ℕ) : atQ F)
              * ∏ i : Fin B, atE F ((i : ℕ)) ^ (b i)) ^ (Nat.card F))
    (fun a _ => fun i => a i / Nat.card F)
    (fun b _ => ascentGen F res b)
    (fun a ha => by
      obtain ⟨haS, hamod⟩ := Finset.mem_filter.mp ha
      exact descentMem F hres haS hamod)
    (fun b hb => by
      obtain ⟨hS, hmod⟩ := ascentMem F hres hb
      exact Finset.mem_filter.mpr ⟨hS, hmod⟩)
    (fun a ha => ascentGen_self F (fun i => congrFun (Finset.mem_filter.mp ha).2 i))
    (fun b hb => descentGen_ascentGen F hresv b)
    (fun a ha => by
      obtain ⟨haS, hamod⟩ := Finset.mem_filter.mp ha
      obtain ⟨hab, hsum, hnc⟩ := (mem_atSumSet F).mp haS
      have haeq : a = ascentGen F res (fun i => a i / Nat.card F) :=
        (ascentGen_self F (fun i => congrFun hamod i)).symm
      have hC : ((Nat.multinomial Finset.univ a : ℕ) : atQ F)
          = ((Nat.multinomial Finset.univ res : ℕ) : atQ F)
            * ((Nat.multinomial Finset.univ (fun i => a i / Nat.card F) : ℕ) : atQ F) := by
        conv_lhs => rw [haeq]
        exact multinomial_ascentGen F hp hpq hresv (fun i => a i / Nat.card F)
      have hP : (∏ i : Fin B, atE F ((i : ℕ)) ^ (a i))
          = (∏ i : Fin B, atE F ((i : ℕ)) ^ (res i))
            * (∏ i : Fin B, atE F ((i : ℕ)) ^ (a i / Nat.card F)) ^ (Nat.card F) := by
        conv_lhs => rw [haeq]
        exact prod_ascentGen F res (fun i => a i / Nat.card F)
      rw [hC, hP, mul_pow, natCast_pow_card_eq F (Nat.multinomial Finset.univ (fun i => a i / Nat.card F))]
      ring)
  rw [hbij]
  rw [← Finset.mul_sum, ← carlitz_sum_pow_card F (atSumSet F ((N - ∑ i, res i * Nat.card F ^ (i : ℕ)) / Nat.card F) B)]
  rfl

open Classical in
/-- ★★★ **The general Frobenius descent** (Chen's Theorem 3.3, the descent step): the level-`N`
Anderson–Thakur partition sum decomposes as a sum over residue vectors of the residue coefficient
times the `q`-th power of the reduced partition sum. -/
theorem atSum_descent (N B : ℕ) :
    atSum F N B
      = ∑ res ∈ residueSet F N B,
          (((Nat.multinomial Finset.univ res : ℕ) : atQ F)
              * ∏ i : Fin B, atE F ((i : ℕ)) ^ (res i))
            * (atSum F ((N - ∑ i, res i * Nat.card F ^ (i : ℕ)) / Nat.card F) B) ^ (Nat.card F) := by
  classical
  rw [show atSum F N B = ∑ a ∈ atSumSet F N B, ((Nat.multinomial Finset.univ a : ℕ) : atQ F)
      * ∏ i : Fin B, atE F ((i : ℕ)) ^ (a i) from rfl]
  rw [← Finset.sum_fiberwise_of_maps_to (s := atSumSet F N B) (t := residueSet F N B)
      (g := fun a => fun i => a i % Nat.card F) (fun a ha => mod_mem_residueSet F ha)
      (fun a => ((Nat.multinomial Finset.univ a : ℕ) : atQ F)
        * ∏ i : Fin B, atE F ((i : ℕ)) ^ (a i))]
  refine Finset.sum_congr rfl (fun res hres => ?_)
  exact atSum_fiber F hres

/-- **Chen's Lemma 2.6(a) + the general descent**, in terms of `atCoeff`. -/
theorem atCoeff_descend (N B : ℕ) (hB : N + 1 ≤ B) :
    atCoeff F N
      = ∑ res ∈ residueSet F N B,
          (((Nat.multinomial Finset.univ res : ℕ) : atQ F)
              * ∏ i : Fin B, atE F ((i : ℕ)) ^ (res i))
            * (atCoeff F ((N - ∑ i, res i * Nat.card F ^ (i : ℕ)) / Nat.card F)) ^ (Nat.card F) := by
  classical
  have hm : ∀ res : Fin B → ℕ,
      ((N - ∑ i, res i * Nat.card F ^ (i : ℕ)) / Nat.card F) + 1 ≤ B := by
    intro res
    have h1 : (N - ∑ i, res i * Nat.card F ^ (i : ℕ)) / Nat.card F ≤ N := by
      have h2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
      exact Nat.le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _)
    omega
  rw [atCoeff_eq_atSum F N B hB, atSum_descent F N B]
  refine Finset.sum_congr rfl (fun res _ => ?_)
  rw [atCoeff_eq_atSum F _ B (hm res)]

end ZagierHoffmanPositiveChar
