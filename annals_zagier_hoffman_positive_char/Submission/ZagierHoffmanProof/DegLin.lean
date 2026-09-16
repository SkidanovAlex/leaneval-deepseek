import Submission.ZagierHoffmanProof.PrimeZeta
import Submission.Commons.Data.Nat.pred_mul_mod
import Submission.Commons.Data.Nat.pred_mul_le_of_mod
import Submission.Commons.Data.Nat.noCarry_pred_mul
import Submission.Commons.Data.Nat.noCarry_pow_mul_pred
import Submission.Commons.Data.Nat.noCarry_iff_mod_sum
import Submission.ZagierHoffmanProof.StepM4

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial RatFunc
open scoped BigOperators WithZero
open WithZero

/-!
# The degree of an MZV with entries `≤ q` is linear in the entries

For a finite field `F` with `q = |F|` prime and `T y = y + jMin F y`, the key
structural input is the closed form of the least good shift

  `jMin F x = (q-1) * x`  for `1 ≤ x ≤ q`,

which gives `T x = q * x` and hence `T^i x = q^i * x` on `[1,q]`.  Consequently the
degree at infinity of an MZV `ζ_A(𝔰)` whose entries are all `≤ q` is the *linear*
function of the entries

  `v (ζ_A 𝔰) = exp (-(1/(q-1)) * ∑_{j < r-1} 𝔰_j * q * (q^{r-1-j} - 1))`.

In particular the degree map is injective on such tuples — this is the structural
statement behind the fact that the MZVs in `𝒯_w` are pairwise distinct and linearly
independent over the prime field.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

section DigitHelpers

variable {q x i : ℕ}

/-- Decomposition of `q^i * x - 1` into the `i` low base-`q` digits `q-1` and the
remaining digit `x-1`. -/
lemma pow_mul_sub_one_decomp (hq : 0 < q) (hx : 1 ≤ x) :
    q ^ i * x - 1 = q ^ i * (x - 1) + (q ^ i - 1) := by
  have hpi : 0 < q ^ i := pow_pos hq i
  have hmul : q ^ i * (x - 1) = q ^ i * x - q ^ i := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  have hle : q ^ i * 1 ≤ q ^ i * x := Nat.mul_le_mul_left _ hx
  rw [hmul]
  omega

lemma pow_mul_sub_one_mod (hq : 0 < q) (hx : 1 ≤ x) :
    (q ^ i * x - 1) % q ^ i = q ^ i - 1 := by
  have hpi : 0 < q ^ i := pow_pos hq i
  rw [pow_mul_sub_one_decomp hq hx, Nat.mul_add_mod_self_left,
    Nat.mod_eq_of_lt (by omega)]

lemma pow_mul_sub_one_div (hq : 0 < q) (hx : 1 ≤ x) :
    (q ^ i * x - 1) / q ^ i = x - 1 := by
  have hpi : 0 < q ^ i := pow_pos hq i
  rw [pow_mul_sub_one_decomp hq hx, Nat.mul_add_div hpi,
    Nat.div_eq_of_lt (by omega), Nat.add_zero]

end DigitHelpers

section JMinLeCard

/-- **The least good shift at `x` is `(q-1) * x`** for `1 ≤ x ≤ q`. -/
theorem isGoodJ_pred_mul (hp : (Nat.card F).Prime) {x : ℕ} (hx : 1 ≤ x)
    (hxq : x ≤ Nat.card F) :
    IsGoodJ F x ((Nat.card F - 1) * x) := by
  have hq2 : 2 ≤ Nat.card F := two_le_card F
  rw [isGoodJ_iff_noCarry F hp x ((Nat.card F - 1) * x) hx]
  refine ⟨?_, dvd_mul_right _ _, ?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  · exact Commons.Data.Nat.noCarry_pred_mul hq2 hx hxq

/-- **`jMin` on `[1,q]`.** -/
theorem jMin_eq_pred_mul (hp : (Nat.card F).Prime) {x : ℕ} (hx : 1 ≤ x)
    (hxq : x ≤ Nat.card F) :
    jMin F ⟨x, hx⟩ = (Nat.card F - 1) * x := by
  have hq2 : 2 ≤ Nat.card F := two_le_card F
  refine le_antisymm (jMin_le F (isGoodJ_pred_mul F hp hx hxq)) ?_
  by_contra hcon
  have hlt : jMin F ⟨x, hx⟩ < (Nat.card F - 1) * x := not_le.mp hcon
  have hj1 : 1 ≤ jMin F ⟨x, hx⟩ := jMin_pos F ⟨x, hx⟩
  have hgood := jMin_spec F ⟨x, hx⟩
  have hnc : noCarry (Nat.card F) (jMin F ⟨x, hx⟩) (x - 1) :=
    ((isGoodJ_iff_noCarry F hp x (jMin F ⟨x, hx⟩) hx).mp hgood).2.2
  have hdvd : (Nat.card F - 1) ∣ jMin F ⟨x, hx⟩ := hgood.2.1
  have hmod : jMin F ⟨x, hx⟩ % Nat.card F ≤ Nat.card F - x := by
    have h := (Commons.Data.Nat.noCarry_iff_mod_sum hq2).mp hnc 1
    rw [Nat.pow_one] at h
    have hx1 : (x - 1) % Nat.card F = x - 1 := Nat.mod_eq_of_lt (by omega)
    rw [hx1] at h
    omega
  have := Commons.Data.Nat.pred_mul_le_of_mod hq2 hx hxq hj1 hdvd hmod
  omega

end JMinLeCard

section JMinPow

/-- **`jMin` at `q^i * x`** for `1 ≤ x ≤ q`. -/
theorem isGoodJ_pow_mul_pred (hp : (Nat.card F).Prime) {x i : ℕ} (hx : 1 ≤ x)
    (hxq : x ≤ Nat.card F) :
    IsGoodJ F (Nat.card F ^ i * x) (Nat.card F ^ i * ((Nat.card F - 1) * x)) := by
  have hq2 : 2 ≤ Nat.card F := two_le_card F
  have hx0 : x ≠ 0 := by omega
  have hpos : 1 ≤ Nat.card F ^ i * x :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (pow_ne_zero i hp.pos.ne') hx0)
  rw [isGoodJ_iff_noCarry F hp (Nat.card F ^ i * x) _ hpos]
  refine ⟨?_, ?_, ?_⟩
  · refine Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero i hp.pos.ne') ?_)
    exact mul_ne_zero (by omega) hx0
  · exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
  · intro j
    exact Commons.Data.Nat.noCarry_pow_mul_pred hq2 hx hxq

/-- **`jMin (q^i x) = q^i (q-1) x`** for `1 ≤ x ≤ q`. -/
theorem jMin_pow_mul_pred (hp : (Nat.card F).Prime) {x i : ℕ} (hx : 1 ≤ x)
    (hxq : x ≤ Nat.card F) (hpos : 0 < Nat.card F ^ i * x) :
    jMin F ⟨Nat.card F ^ i * x, hpos⟩ = Nat.card F ^ i * ((Nat.card F - 1) * x) := by
  have hq2 : 2 ≤ Nat.card F := two_le_card F
  have hq1 : 1 ≤ Nat.card F := by omega
  have hq0 : 0 < Nat.card F := hp.pos
  have hpi : 0 < Nat.card F ^ i := pow_pos hq0 i
  have hp1 : 1 ≤ Nat.card F ^ i * x := Nat.one_le_iff_ne_zero.mpr hpos.ne'
  refine le_antisymm (jMin_le F (isGoodJ_pow_mul_pred F hp hx hxq)) ?_
  by_contra hcon
  have hlt : jMin F ⟨Nat.card F ^ i * x, hpos⟩ < Nat.card F ^ i * ((Nat.card F - 1) * x) :=
    not_le.mp hcon
  have hgood := jMin_spec F ⟨Nat.card F ^ i * x, hpos⟩
  have hnc : noCarry (Nat.card F) (jMin F ⟨Nat.card F ^ i * x, hpos⟩) (Nat.card F ^ i * x - 1) :=
    ((isGoodJ_iff_noCarry F hp (Nat.card F ^ i * x) _ hp1).mp hgood).2.2
  have hdvdq : (Nat.card F - 1) ∣ jMin F ⟨Nat.card F ^ i * x, hpos⟩ := hgood.2.1
  -- the low `i` digits of `q^i * x - 1` are `q - 1`, so `q^i` divides `jMin`
  have hjmod : jMin F ⟨Nat.card F ^ i * x, hpos⟩ % Nat.card F ^ i = 0 := by
    have h := (Commons.Data.Nat.noCarry_iff_mod_sum hq2).mp hnc i
    rw [pow_mul_sub_one_mod hq0 hx] at h
    have h2 : jMin F ⟨Nat.card F ^ i * x, hpos⟩ % Nat.card F ^ i < 1 := by omega
    exact Nat.lt_one_iff.mp h2
  have hdvd : Nat.card F ^ i ∣ jMin F ⟨Nat.card F ^ i * x, hpos⟩ := Nat.dvd_of_mod_eq_zero hjmod
  have hjval : Nat.card F ^ i * (jMin F ⟨Nat.card F ^ i * x, hpos⟩ / Nat.card F ^ i)
      = jMin F ⟨Nat.card F ^ i * x, hpos⟩ := Nat.mul_div_cancel' hdvd
  set j0 := jMin F ⟨Nat.card F ^ i * x, hpos⟩ / Nat.card F ^ i with hj0def
  have hjval' : Nat.card F ^ i * j0 = jMin F ⟨Nat.card F ^ i * x, hpos⟩ := hjval
  have hj0pos : 1 ≤ j0 := Nat.one_le_iff_ne_zero.mpr (by
    intro hzero
    have hpos1 : 1 ≤ jMin F ⟨Nat.card F ^ i * x, hpos⟩ := jMin_pos F _
    rw [hzero, mul_zero] at hjval'
    omega)
  have hcop : Nat.Coprime (Nat.card F - 1) (Nat.card F ^ i) := by
    have h1 : Nat.Coprime (Nat.card F - 1) (Nat.card F) := by
      have h := Nat.coprime_self_add_right (m := Nat.card F - 1) (n := 1)
      rw [Nat.sub_add_cancel hq1] at h
      exact h.mpr (Nat.coprime_one_right _)
    exact h1.pow_right i
  have hdvd0 : (Nat.card F - 1) ∣ j0 := by
    refine hcop.dvd_of_dvd_mul_left ?_
    rw [hj0def, hjval]
    exact hdvdq
  have hnc0 : noCarry (Nat.card F) j0 (x - 1) := by
    intro m
    have hpoweq : Nat.card F ^ (m + i) = Nat.card F ^ i * Nat.card F ^ m := by
      rw [Nat.pow_add, Nat.mul_comm]
    have e1 : jMin F ⟨Nat.card F ^ i * x, hpos⟩ / Nat.card F ^ (m + i) = j0 / Nat.card F ^ m := by
      rw [hpoweq, ← Nat.div_div_eq_div_mul, ← hj0def]
    have e2 : (Nat.card F ^ i * x - 1) / Nat.card F ^ (m + i) = (x - 1) / Nat.card F ^ m := by
      rw [hpoweq, ← Nat.div_div_eq_div_mul, pow_mul_sub_one_div hq0 hx]
    have h := hnc (m + i)
    rw [e1, e2] at h
    exact h
  have hgood0 : IsGoodJ F x j0 := by
    rw [isGoodJ_iff_noCarry F hp x j0 hx]
    exact ⟨hj0pos, hdvd0, hnc0⟩
  have hle : (Nat.card F - 1) * x ≤ j0 := by
    have h := jMin_le F (k := ⟨x, hx⟩) hgood0
    rw [jMin_eq_pred_mul F hp hx hxq] at h
    exact h
  have hfin : Nat.card F ^ i * ((Nat.card F - 1) * x) ≤ jMin F ⟨Nat.card F ^ i * x, hpos⟩ := by
    rw [← hjval']
    exact Nat.mul_le_mul_left _ hle
  omega

end JMinPow

section TBounded

/-- **`T x = q * x`** for `1 ≤ x ≤ q`. -/
theorem TT_eq_mul (hp : (Nat.card F).Prime) {x : ℕ} (hx : 1 ≤ x) (hxq : x ≤ Nat.card F) :
    TT (Nat.card F) (two_le_card F) x = Nat.card F * x := by
  have hq1 : 1 ≤ Nat.card F := by omega
  rw [TT_eq_add_jMin F hp hx, jMin_eq_pred_mul F hp hx hxq]
  calc x + (Nat.card F - 1) * x = 1 * x + (Nat.card F - 1) * x := by rw [one_mul]
    _ = (1 + (Nat.card F - 1)) * x := by rw [Nat.add_mul]
    _ = Nat.card F * x := by rw [Nat.add_comm, Nat.sub_add_cancel hq1]

/-- **`T^i x = q^i * x`** for `1 ≤ x ≤ q`. -/
theorem TT_iterate_eq_mul (hp : (Nat.card F).Prime) {x : ℕ} (hx : 1 ≤ x)
    (hxq : x ≤ Nat.card F) (i : ℕ) :
    Nat.iterate (TT (Nat.card F) (two_le_card F)) i x = Nat.card F ^ i * x := by
  have hq0 : 0 < Nat.card F := hp.pos
  have hq1 : 1 ≤ Nat.card F := by omega
  induction i with
  | zero => rw [Function.iterate_zero_apply, pow_zero, one_mul]
  | succ i ih =>
      rw [Function.iterate_succ_apply', ih]
      have hpos : 0 < Nat.card F ^ i * x := Nat.mul_pos (pow_pos hq0 i) hx
      have hp1 : 1 ≤ Nat.card F ^ i * x := hpos
      rw [TT_eq_add_jMin F hp hp1, jMin_pow_mul_pred F hp hx hxq hpos]
      have h2 : x + (Nat.card F - 1) * x = Nat.card F * x := by
        calc x + (Nat.card F - 1) * x = 1 * x + (Nat.card F - 1) * x := by rw [one_mul]
          _ = (1 + (Nat.card F - 1)) * x := by rw [Nat.add_mul]
          _ = Nat.card F * x := by rw [Nat.add_comm, Nat.sub_add_cancel hq1]
      rw [← Nat.mul_add, h2, pow_succ, Nat.mul_assoc]

end TBounded

section Degree

/-- **The degree exponent of a depth-one power sum is linear.** -/
theorem sExpG_eq_lin (hp : (Nat.card F).Prime) {x : ℕ} (hx : 1 ≤ x)
    (hxq : x ≤ Nat.card F) (d : ℕ) :
    ((Nat.card F - 1 : ℕ) : ℤ) * sExpG F d x
      = (x : ℤ) * (Nat.card F : ℤ) * ((Nat.card F : ℤ) ^ d - 1) := by
  have hq1 : 1 ≤ Nat.card F := by omega
  unfold sExpG
  have hterm : ∀ i ∈ Finset.range d,
      ((Nat.iterate (TT (Nat.card F) (two_le_card F)) (i + 1) x : ℕ) : ℤ)
        = (x : ℤ) * (Nat.card F : ℤ) ^ (i + 1) := by
    intro i _
    rw [TT_iterate_eq_mul F hp hx hxq (i + 1)]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hsum : (∑ i ∈ Finset.range d, (Nat.card F : ℤ) ^ (i + 1))
      = (Nat.card F : ℤ) * (∑ i ∈ Finset.range d, (Nat.card F : ℤ) ^ i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [pow_succ, mul_comm]
  rw [hsum]
  have hg := mul_geom_sum (Nat.card F : ℤ) d
  have hcast : ((Nat.card F - 1 : ℕ) : ℤ) = (Nat.card F : ℤ) - 1 := by
    rw [Nat.cast_sub hq1, Nat.cast_one]
  rw [hcast]
  calc ((Nat.card F : ℤ) - 1)
        * ((x : ℤ) * ((Nat.card F : ℤ) * ∑ i ∈ Finset.range d, (Nat.card F : ℤ) ^ i))
      = ((x : ℤ) * (Nat.card F : ℤ))
        * (((Nat.card F : ℤ) - 1) * ∑ i ∈ Finset.range d, (Nat.card F : ℤ) ^ i) := by ring
    _ = ((x : ℤ) * (Nat.card F : ℤ)) * ((Nat.card F : ℤ) ^ d - 1) := by rw [hg]
    _ = (x : ℤ) * (Nat.card F : ℤ) * ((Nat.card F : ℤ) ^ d - 1) := by ring

/-- **The degree exponent of an MZV with entries `≤ q` is linear in the entries.**

The sum runs over all entries: the (vanishing) contribution of the last entry is
`q^{0} - 1 = 0`. -/
theorem sSeqG_eq_lin (hp : (Nat.card F).Prime) : ∀ (r : ℕ) (hr : 1 ≤ r) (𝔰 : Fin r → ℕ+),
    (∀ i, (𝔰 i : ℕ) ≤ Nat.card F) →
    ((Nat.card F - 1 : ℕ) : ℤ) * sSeqG F r 𝔰 (r - 1)
      = ∑ j : Fin r, (𝔰 j : ℤ) * (Nat.card F : ℤ)
          * ((Nat.card F : ℤ) ^ (r - 1 - (j : ℕ)) - 1) := by
  intro r
  induction r with
  | zero => intro hr; omega
  | succ r ih =>
      intro hr 𝔰 hle
      rcases Nat.eq_zero_or_pos r with hr0 | hr0
      · subst hr0
        rw [sSeqG_one]
        simp [sExpG]
      · obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
        have hk1 : 1 ≤ k + 1 := by omega
        show ((Nat.card F - 1 : ℕ) : ℤ) * sSeqG F (k + 2) 𝔰 (k + 1)
            = ∑ j : Fin (k + 2), (𝔰 j : ℤ) * (Nat.card F : ℤ)
                * ((Nat.card F : ℤ) ^ (k + 2 - 1 - (j : ℕ)) - 1)
        rw [sSeqG_succ F k 𝔰 (k + 1), mul_add]
        have hs := sExpG_eq_lin F hp (x := ↑(𝔰 0)) (𝔰 0).pos (hle 0) (k + 1)
        rw [hs]
        have hIH : ((Nat.card F - 1 : ℕ) : ℤ) * sSeqG F (k + 1) (expTail 𝔰) k
            = ∑ j : Fin (k + 1), ((expTail 𝔰) j : ℤ) * (Nat.card F : ℤ)
                * ((Nat.card F : ℤ) ^ (k + 1 - 1 - (j : ℕ)) - 1) :=
          ih hk1 (expTail 𝔰) (fun j => hle ⟨(j : ℕ) + 1, by omega⟩)
        rw [hIH]
        conv_rhs => rw [Fin.sum_univ_succ]
        have hhead : ((𝔰 (0 : Fin (k + 2)) : ℕ+) : ℤ) * (Nat.card F : ℤ)
              * ((Nat.card F : ℤ) ^ (k + 2 - 1 - ((0 : Fin (k + 2)) : ℕ)) - 1)
            = ((𝔰 (0 : Fin (k + 2)) : ℕ+) : ℤ) * (Nat.card F : ℤ)
              * ((Nat.card F : ℤ) ^ (k + 1) - 1) := by
          rw [show k + 2 - 1 - ((0 : Fin (k + 2)) : ℕ) = k + 1 from by
            rw [Fin.val_zero]; omega]
        have hsum : (∑ j : Fin (k + 1), (𝔰 (Fin.succ j) : ℤ) * (Nat.card F : ℤ)
              * ((Nat.card F : ℤ) ^ (k + 2 - 1 - ((Fin.succ j : Fin (k + 2)) : ℕ)) - 1))
            = (∑ j : Fin (k + 1), ((expTail 𝔰) j : ℤ) * (Nat.card F : ℤ)
              * ((Nat.card F : ℤ) ^ (k + 1 - 1 - (j : ℕ)) - 1)) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [show (expTail 𝔰) j = 𝔰 (Fin.succ j) from rfl]
          rw [show k + 2 - 1 - ((Fin.succ j : Fin (k + 2)) : ℕ) = k + 1 - 1 - (j : ℕ) from by
            rw [Fin.val_succ]; omega]
        rw [hhead, hsum]

end Degree

section Code

/-- **Geometric sum identity in `ℕ`**: `(∑_{i<n} q^i) * (q-1) = q^n - 1`. -/
lemma geom_sum_mul_pred_mul (q n : ℕ) :
    (∑ i ∈ Finset.range n, q ^ i) * (q - 1) = q ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, add_mul, ih]
      rcases Nat.eq_zero_or_pos q with hq | hq
      · subst hq
        cases n <;> simp
      · have h1 : q ^ n * (q - 1) = q ^ (n + 1) - q ^ n := by
          rw [pow_succ, Nat.mul_sub_left_distrib, Nat.mul_one, Nat.mul_comm]
        rw [h1]
        have h2 : q ^ n ≤ q ^ (n + 1) := by
          rw [pow_succ, mul_comm]
          exact Nat.le_mul_of_pos_left _ hq
        have h3 : 0 < q ^ n := pow_pos hq n
        omega

/-- The base-`q` code `∑_{j<r} 𝔰_j q^{r-1-j}` of a tuple of positive entries. -/
noncomputable def tupleCode {r : ℕ} (𝔰 : Fin r → ℕ+) : ℕ :=
  ∑ j : Fin r, (𝔰 j : ℕ) * Nat.card F ^ (r - 1 - (j : ℕ))

/-- The weight `∑_{j<r} 𝔰_j` of a tuple. -/
noncomputable def tupleWeight {r : ℕ} (𝔰 : Fin r → ℕ+) : ℕ :=
  ∑ j : Fin r, (𝔰 j : ℕ)

/-- **`(q-1) · (degree) = q · (code - weight)`** — the degree exponent of a tuple with
entries `≤ q` is linear in the tuple. -/
theorem sSeqG_pred_mul_eq_code (hp : (Nat.card F).Prime) {r : ℕ} (hr : 1 ≤ r)
    (𝔰 : Fin r → ℕ+) (hle : ∀ i, (𝔰 i : ℕ) ≤ Nat.card F) :
    ((Nat.card F - 1 : ℕ) : ℤ) * sSeqG F r 𝔰 (r - 1)
      = (Nat.card F : ℤ)
        * (((tupleCode F 𝔰 : ℕ) : ℤ) - ((tupleWeight 𝔰 : ℕ) : ℤ)) := by
  rw [sSeqG_eq_lin F hp r hr 𝔰 hle]
  have h1 : ∀ j : Fin r, (𝔰 j : ℤ) * (Nat.card F : ℤ)
      * ((Nat.card F : ℤ) ^ (r - 1 - (j : ℕ)) - 1)
      = (Nat.card F : ℤ)
        * ((𝔰 j : ℤ) * (Nat.card F : ℤ) ^ (r - 1 - (j : ℕ)) - (𝔰 j : ℤ)) := by
    intro j
    ring
  have hcode : ((tupleCode F 𝔰 : ℕ) : ℤ)
      = ∑ j : Fin r, (𝔰 j : ℤ) * (Nat.card F : ℤ) ^ (r - 1 - (j : ℕ)) := by
    simp only [tupleCode, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]
  have hwt : ((tupleWeight 𝔰 : ℕ) : ℤ) = ∑ j : Fin r, (𝔰 j : ℤ) := by
    simp only [tupleWeight, Nat.cast_sum]
  calc (∑ j : Fin r, (𝔰 j : ℤ) * (Nat.card F : ℤ)
        * ((Nat.card F : ℤ) ^ (r - 1 - (j : ℕ)) - 1))
      = (∑ j : Fin r, (Nat.card F : ℤ)
          * ((𝔰 j : ℤ) * (Nat.card F : ℤ) ^ (r - 1 - (j : ℕ)) - (𝔰 j : ℤ))) :=
        Finset.sum_congr rfl fun j _ => h1 j
    _ = (Nat.card F : ℤ) * (∑ j : Fin r,
          ((𝔰 j : ℤ) * (Nat.card F : ℤ) ^ (r - 1 - (j : ℕ)) - (𝔰 j : ℤ))) :=
        (Finset.mul_sum _ _ _).symm
    _ = (Nat.card F : ℤ)
        * (((tupleCode F 𝔰 : ℕ) : ℤ) - ((tupleWeight 𝔰 : ℕ) : ℤ)) := by
        rw [Finset.sum_sub_distrib, ← hcode, ← hwt]

end Code

section Digits

/-- **Base-`q` uniqueness** of expansions with digits in `[0, q-1]`. -/
lemma sum_pow_digit_inj {q r : ℕ} {v v' : Fin r → ℕ} (hv : ∀ j, v j < q)
    (hv' : ∀ j, v' j < q)
    (h : ∑ j : Fin r, v j * q ^ (r - 1 - (j : ℕ))
      = ∑ j : Fin r, v' j * q ^ (r - 1 - (j : ℕ))) :
    v = v' := by
  induction r with
  | zero => funext j; exact j.elim0
  | succ r ih =>
      rw [Fin.sum_univ_castSucc] at h
      rw [Fin.sum_univ_castSucc] at h
      -- peel off the lowest digit `v (Fin.last r)`
      have hpow : ∀ j : Fin r, q ^ (r + 1 - 1 - ((j.castSucc : Fin (r + 1)) : ℕ))
          = q * q ^ (r - 1 - (j : ℕ)) := by
        intro j
        have hval : ((j.castSucc : Fin (r + 1)) : ℕ) = (j : ℕ) := rfl
        have h1 : r + 1 - 1 - (j : ℕ) = r - (j : ℕ) := by omega
        have h2 : r - (j : ℕ) = r - 1 - (j : ℕ) + 1 := by omega
        rw [hval, h1, h2, pow_succ, mul_comm]
      have hlast : q ^ (r + 1 - 1 - ((Fin.last r : Fin (r + 1)) : ℕ)) = 1 := by
        rw [Fin.val_last]
        simp
      have hA : (∑ j : Fin r, v j.castSucc * q ^ (r + 1 - 1 - ((j.castSucc : Fin (r + 1)) : ℕ)))
          = q * (∑ j : Fin r, v j.castSucc * q ^ (r - 1 - (j : ℕ))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [hpow j]
        ring
      have hB : (∑ j : Fin r, v' j.castSucc * q ^ (r + 1 - 1 - ((j.castSucc : Fin (r + 1)) : ℕ)))
          = q * (∑ j : Fin r, v' j.castSucc * q ^ (r - 1 - (j : ℕ))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [hpow j]
        ring
      rw [hA, hB, hlast, mul_one, mul_one] at h
      have hvq : v (Fin.last r) < q := hv _
      have hvq' : v' (Fin.last r) < q := hv' _
      have hmod : v (Fin.last r) ≡ v' (Fin.last r) [MOD q] := by
        have h2 : q * (∑ j : Fin r, v j.castSucc * q ^ (r - 1 - (j : ℕ))) + v (Fin.last r)
            ≡ q * (∑ j : Fin r, v' j.castSucc * q ^ (r - 1 - (j : ℕ))) + v' (Fin.last r)
            [MOD q] := by rw [h]
        simpa [Nat.ModEq, Nat.add_mul_mod_self_left, Nat.mul_add_mod] using h2
      have hlast_eq : v (Fin.last r) = v' (Fin.last r) := Nat.ModEq.eq_of_lt_of_lt hmod hvq hvq'
      have hsum_eq : (∑ j : Fin r, v j.castSucc * q ^ (r - 1 - (j : ℕ)))
          = (∑ j : Fin r, v' j.castSucc * q ^ (r - 1 - (j : ℕ))) := by
        have hqpos : 0 < q := by
          rcases Nat.eq_zero_or_pos q with h0 | h0
          · subst h0
            exact absurd (hv (Fin.last r)) (by simp)
          · exact h0
        have h3 : q * (∑ j : Fin r, v j.castSucc * q ^ (r - 1 - (j : ℕ))) + v' (Fin.last r)
            = q * (∑ j : Fin r, v' j.castSucc * q ^ (r - 1 - (j : ℕ))) + v' (Fin.last r) := by
          rw [hlast_eq] at h
          exact h
        exact Nat.mul_left_cancel hqpos (Nat.add_right_cancel h3)
      have hrest : (fun j : Fin r => v j.castSucc) = (fun j : Fin r => v' j.castSucc) :=
        ih (fun j => hv j.castSucc) (fun j => hv' j.castSucc) hsum_eq
      funext i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · exact congrFun hrest j
      · exact hlast_eq

/-- **The code determines the tuple**: for tuples with entries in `[1, q]`, equal codes force
equal depths and equal entries. -/
theorem tupleCode_injective {r r' : ℕ} (𝔰 : Fin r → ℕ+) (𝔰' : Fin r' → ℕ+)
    (hle : ∀ i, (𝔰 i : ℕ) ≤ Nat.card F) (hle' : ∀ i, (𝔰' i : ℕ) ≤ Nat.card F)
    (h : tupleCode F 𝔰 = tupleCode F 𝔰') :
    ∃ h : r = r', ∀ i : Fin r, 𝔰 i = 𝔰' (h ▸ i) := by
  classical
  have hq : 2 ≤ Nat.card F := two_le_card F
  have hq1 : 1 ≤ Nat.card F := by omega
  -- the geometric sum `∑_{j<n} q^{n-1-j} = (q^n - 1)/(q-1)`
  have hgeom : ∀ n : ℕ,
      (Nat.card F - 1) * (∑ j : Fin n, Nat.card F ^ (n - 1 - (j : ℕ))) = Nat.card F ^ n - 1 := by
    intro n
    rw [Fin.sum_univ_eq_sum_range (fun i => Nat.card F ^ (n - 1 - i)) n]
    have hreflect : (∑ i ∈ Finset.range n, Nat.card F ^ (n - 1 - i))
        = ∑ i ∈ Finset.range n, Nat.card F ^ i :=
      Finset.sum_range_reflect (fun i => Nat.card F ^ i) n
    rw [hreflect]
    rw [Nat.mul_comm]
    exact geom_sum_mul_pred_mul (Nat.card F) n
  -- bounds on `(q-1) * code`
  have bound : ∀ {n : ℕ} (𝔰 : Fin n → ℕ+) (hle : ∀ i, (𝔰 i : ℕ) ≤ Nat.card F),
      (Nat.card F - 1) * (tupleCode F 𝔰) ≥ Nat.card F ^ n - 1
      ∧ (Nat.card F - 1) * (tupleCode F 𝔰) ≤ Nat.card F * (Nat.card F ^ n - 1) := by
    intro n 𝔰 hle
    have hlow : (∑ j : Fin n, Nat.card F ^ (n - 1 - (j : ℕ))) ≤ tupleCode F 𝔰 := by
      simp only [tupleCode]
      apply Finset.sum_le_sum
      intro j _
      exact Nat.le_mul_of_pos_left _ (𝔰 j).pos
    have hhigh : tupleCode F 𝔰 ≤ Nat.card F * (∑ j : Fin n, Nat.card F ^ (n - 1 - (j : ℕ))) := by
      simp only [tupleCode]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      calc (𝔰 j : ℕ) * Nat.card F ^ (n - 1 - (j : ℕ))
          ≤ Nat.card F * Nat.card F ^ (n - 1 - (j : ℕ)) :=
            Nat.mul_le_mul_right _ (hle j)
        _ = Nat.card F * Nat.card F ^ (n - 1 - (j : ℕ)) := rfl
    refine ⟨?_, ?_⟩
    · calc Nat.card F ^ n - 1
          = (Nat.card F - 1) * (∑ j : Fin n, Nat.card F ^ (n - 1 - (j : ℕ))) := (hgeom n).symm
        _ ≤ (Nat.card F - 1) * tupleCode F 𝔰 := Nat.mul_le_mul_left _ hlow
    · calc (Nat.card F - 1) * (tupleCode F 𝔰)
          ≤ (Nat.card F - 1) * (Nat.card F * (∑ j : Fin n, Nat.card F ^ (n - 1 - (j : ℕ)))) :=
            Nat.mul_le_mul_left _ hhigh
        _ = Nat.card F * ((Nat.card F - 1) * (∑ j : Fin n, Nat.card F ^ (n - 1 - (j : ℕ)))) := by ring
        _ = Nat.card F * (Nat.card F ^ n - 1) := by rw [hgeom n]
  obtain ⟨hlb, hub⟩ := bound 𝔰 hle
  obtain ⟨hlb', hub'⟩ := bound 𝔰' hle'
  -- equal codes
  have hcode_eq : tupleCode F 𝔰 = tupleCode F 𝔰' := h
  have hr_eq : r = r' := by
    rcases lt_trichotomy r r' with hlt | heq | hgt
    · exfalso
      have h2 : Nat.card F ^ (r + 1) ≤ Nat.card F ^ r' :=
        Nat.pow_le_pow_right (by omega) (by omega : r + 1 ≤ r')
      have hlt' : Nat.card F * (Nat.card F ^ r - 1) < Nat.card F ^ r' - 1 := by
        have hA : Nat.card F * (Nat.card F ^ r - 1)
            ≤ Nat.card F * Nat.card F ^ r - Nat.card F := by
          rw [Nat.mul_sub_left_distrib, Nat.mul_one]
        have hB : Nat.card F * Nat.card F ^ r = Nat.card F ^ (r + 1) := by
          rw [pow_succ, Nat.mul_comm]
        have hC : Nat.card F * (Nat.card F ^ r - 1) ≤ Nat.card F ^ r' - Nat.card F := by
          rw [hB] at hA
          exact le_trans hA (Nat.sub_le_sub_right h2 _)
        have h4 : Nat.card F ≤ Nat.card F ^ r' := by
          calc Nat.card F = Nat.card F ^ 1 := (pow_one _).symm
            _ ≤ Nat.card F ^ r' := Nat.pow_le_pow_right (by omega) (by omega : 1 ≤ r')
        omega
      have hle' : Nat.card F ^ r' - 1 ≤ Nat.card F * (Nat.card F ^ r - 1) := by
        have h1 := hlb'
        rw [← hcode_eq] at h1
        exact le_trans h1 hub
      omega
    · exact heq
    · exfalso
      have h2 : Nat.card F ^ (r' + 1) ≤ Nat.card F ^ r :=
        Nat.pow_le_pow_right (by omega) (by omega : r' + 1 ≤ r)
      have hlt' : Nat.card F * (Nat.card F ^ r' - 1) < Nat.card F ^ r - 1 := by
        have hA : Nat.card F * (Nat.card F ^ r' - 1)
            ≤ Nat.card F * Nat.card F ^ r' - Nat.card F := by
          rw [Nat.mul_sub_left_distrib, Nat.mul_one]
        have hB : Nat.card F * Nat.card F ^ r' = Nat.card F ^ (r' + 1) := by
          rw [pow_succ, Nat.mul_comm]
        have hC : Nat.card F * (Nat.card F ^ r' - 1) ≤ Nat.card F ^ r - Nat.card F := by
          rw [hB] at hA
          exact le_trans hA (Nat.sub_le_sub_right h2 _)
        have h4 : Nat.card F ≤ Nat.card F ^ r := by
          calc Nat.card F = Nat.card F ^ 1 := (pow_one _).symm
            _ ≤ Nat.card F ^ r := Nat.pow_le_pow_right (by omega) (by omega : 1 ≤ r)
        omega
      have hle : Nat.card F ^ r - 1 ≤ Nat.card F * (Nat.card F ^ r' - 1) := by
        have h1 := hlb
        rw [hcode_eq] at h1
        exact le_trans h1 hub'
      omega
  subst hr_eq
  refine ⟨rfl, ?_⟩
  -- now both tuples have the same arity: use base-`q` digit uniqueness
  have hv : ∀ j : Fin r, (𝔰 j : ℕ) - 1 < Nat.card F := fun j => by
    have := hle j; omega
  have hv' : ∀ j : Fin r, (𝔰' j : ℕ) - 1 < Nat.card F := fun j => by
    have := hle' j; omega
  have hdigit : (∑ j : Fin r, ((𝔰 j : ℕ) - 1) * Nat.card F ^ (r - 1 - (j : ℕ)))
      = ∑ j : Fin r, ((𝔰' j : ℕ) - 1) * Nat.card F ^ (r - 1 - (j : ℕ)) := by
    have hsplit : ∀ (𝔰 : Fin r → ℕ+) (hle : ∀ i, (𝔰 i : ℕ) ≤ Nat.card F),
        tupleCode F 𝔰
          = (∑ j : Fin r, Nat.card F ^ (r - 1 - (j : ℕ)))
            + ∑ j : Fin r, ((𝔰 j : ℕ) - 1) * Nat.card F ^ (r - 1 - (j : ℕ)) := by
      intro 𝔰 hle
      simp only [tupleCode]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      have hj : 1 ≤ (𝔰 j : ℕ) := (𝔰 j).pos
      have h1 : (𝔰 j : ℕ) * Nat.card F ^ (r - 1 - (j : ℕ))
          = (1 + ((𝔰 j : ℕ) - 1)) * Nat.card F ^ (r - 1 - (j : ℕ)) := by
        rw [Nat.add_sub_cancel' hj]
      rw [h1, add_mul, one_mul]
    rw [hsplit 𝔰 hle, hsplit 𝔰' hle'] at h
    exact Nat.add_left_cancel h
  have : (fun j : Fin r => (𝔰 j : ℕ) - 1) = (fun j : Fin r => (𝔰' j : ℕ) - 1) :=
    sum_pow_digit_inj hv hv' hdigit
  intro i
  have hi : (𝔰 i : ℕ) - 1 = (𝔰' i : ℕ) - 1 := congrFun this i
  have h1 : 1 ≤ (𝔰 i : ℕ) := (𝔰 i).pos
  have h2 : 1 ≤ (𝔰' i : ℕ) := (𝔰' i).pos
  have h3 : (𝔰 i : ℕ) = (𝔰' i : ℕ) := by omega
  exact Subtype.ext h3

/-- **The degree of an MZV determines the tuple**: for tuples with entries `≤ q` and equal
weight, equal degrees `(q-1) · sSeqG` force equal depths and equal entries. -/
theorem sSeqG_degree_injective (hp : (Nat.card F).Prime) :
    ∀ {r r' : ℕ} (hr : 1 ≤ r) (hr' : 1 ≤ r') (𝔰 : Fin r → ℕ+) (𝔰' : Fin r' → ℕ+),
      (∀ i, (𝔰 i : ℕ) ≤ Nat.card F) → (∀ i, (𝔰' i : ℕ) ≤ Nat.card F) →
      tupleWeight 𝔰 = tupleWeight 𝔰' →
      ((Nat.card F - 1 : ℕ) : ℤ) * sSeqG F r 𝔰 (r - 1)
        = ((Nat.card F - 1 : ℕ) : ℤ) * sSeqG F r' 𝔰' (r' - 1) →
      ∃ h : r = r', ∀ i : Fin r, 𝔰 i = 𝔰' (h ▸ i) := by
  intro r r' hr hr' 𝔰 𝔰' hle hle' hw hdeg
  have hqne : ((Nat.card F : ℤ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt hp.pos)
  have h3 : ((tupleCode F 𝔰 : ℕ) : ℤ) - ((tupleWeight 𝔰 : ℕ) : ℤ)
      = ((tupleCode F 𝔰' : ℕ) : ℤ) - ((tupleWeight 𝔰' : ℕ) : ℤ) := by
    have h1 := sSeqG_pred_mul_eq_code F hp hr 𝔰 hle
    have h2 := sSeqG_pred_mul_eq_code F hp hr' 𝔰' hle'
    have h4 : (Nat.card F : ℤ)
          * (((tupleCode F 𝔰 : ℕ) : ℤ) - ((tupleWeight 𝔰 : ℕ) : ℤ))
        = (Nat.card F : ℤ)
          * (((tupleCode F 𝔰' : ℕ) : ℤ) - ((tupleWeight 𝔰' : ℕ) : ℤ)) := by
      rw [← h1, ← h2, hdeg]
    exact mul_left_cancel₀ hqne h4
  have hcode : tupleCode F 𝔰 = tupleCode F 𝔰' := by
    have hw' : ((tupleWeight 𝔰 : ℕ) : ℤ) = ((tupleWeight 𝔰' : ℕ) : ℤ) := by rw [hw]
    have h3' : ((tupleCode F 𝔰 : ℕ) : ℤ) = ((tupleCode F 𝔰' : ℕ) : ℤ) := by omega
    exact_mod_cast h3'
  exact tupleCode_injective F 𝔰 𝔰' hle hle' hcode

end Digits

/-- **The MZV attached to a tuple with entries `≤ q` determines the tuple** (same weight). -/
theorem zeta_A_injective (hp : (Nat.card F).Prime) :
    ∀ {r r' : ℕ} (hr : 1 ≤ r) (hr' : 1 ≤ r') (𝔰 : Fin r → ℕ+) (𝔰' : Fin r' → ℕ+),
      (∀ i, (𝔰 i : ℕ) ≤ Nat.card F) → (∀ i, (𝔰' i : ℕ) ≤ Nat.card F) →
      tupleWeight 𝔰 = tupleWeight 𝔰' →
      ζ_A F 𝔰 = ζ_A F 𝔰' →
      ∃ h : r = r', ∀ i : Fin r, 𝔰 i = 𝔰' (h ▸ i) := by
  intro r r' hr hr' 𝔰 𝔰' hle hle' hw hzeta
  have h1 := val_zeta_prime F hp hr 𝔰
  have h2 := val_zeta_prime F hp hr' 𝔰'
  rw [hzeta] at h1
  have h3 : sSeqG F r 𝔰 (r - 1) = sSeqG F r' 𝔰' (r' - 1) := by
    have := WithZero.exp_inj.mp (h1.symm.trans h2)
    omega
  exact sSeqG_degree_injective F hp hr hr' 𝔰 𝔰' hle hle' hw (by rw [h3])

section LinearIndependent

/-- **Linear independence over the prime field.**  A finite family of MZVs attached to tuples
with entries `≤ q` and pairwise distinct degrees (at infinity) is linearly independent over the
prime field `F`.  (This is the elementary consequence of the degree computation: the terms of a
nontrivial relation have pairwise distinct valuations.) -/
theorem zeta_linearIndependent_of_degree_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hp : (Nat.card F).Prime) (𝔰 : ι → Σ r : ℕ, Fin r → ℕ+)
    (hr : ∀ i, 1 ≤ (𝔰 i).1) (hle : ∀ i j, ((𝔰 i).2 j : ℕ) ≤ Nat.card F)
    (hdeg : Function.Injective
      (fun i => sSeqG F (𝔰 i).1 (𝔰 i).2 ((𝔰 i).1 - 1)))
    (c : ι → F) (h : (∑ i, cst F (c i) * ζ_A F (𝔰 i).2) = 0) :
    ∀ i, c i = 0 := by
  classical
  set I : Finset ι := Finset.univ.filter (fun i => c i ≠ 0) with hI
  by_contra hcon
  simp only [not_forall] at hcon
  obtain ⟨i0, hi0⟩ := hcon
  have hInon : I.Nonempty := ⟨i0, by simp [hI, hi0]⟩
  obtain ⟨j0, hj0I, hj0min⟩ := Finset.exists_min_image I
    (fun i => sSeqG F (𝔰 i).1 (𝔰 i).2 ((𝔰 i).1 - 1)) hInon
  have hcj0 : c j0 ≠ 0 := by
    have h' := hj0I
    rw [hI] at h'
    simpa using h'
  have hsub : (∑ i ∈ I, cst F (c i) * ζ_A F (𝔰 i).2)
      = ∑ i, cst F (c i) * ζ_A F (𝔰 i).2 := by
    rw [hI]
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro i _ hi
    have hci : c i = 0 := by
      by_contra hc
      exact hi (by simp [hc])
    have hz : cst F (0 : F) = 0 := map_zero (cstHom F)
    rw [hci, hz, zero_mul]
  have hv : ∀ i ∈ I \ {j0},
      Valued.v (cst F (c i) * ζ_A F (𝔰 i).2) < Valued.v (cst F (c j0) * ζ_A F (𝔰 j0).2) := by
    intro i hi
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
    obtain ⟨hiI, hij⟩ := hi
    have hci : c i ≠ 0 := by
      have h' := hiI
      rw [hI] at h'
      simpa using h'
    rw [map_mul, map_mul, v_cst_of_ne_zero F hci, v_cst_of_ne_zero F hcj0, one_mul, one_mul,
      val_zeta_prime F hp (hr i) (𝔰 i).2, val_zeta_prime F hp (hr j0) (𝔰 j0).2,
      WithZero.exp_lt_exp]
    have h2 := hj0min i hiI
    have h3 : sSeqG F (𝔰 i).1 (𝔰 i).2 ((𝔰 i).1 - 1)
        ≠ sSeqG F (𝔰 j0).1 (𝔰 j0).2 ((𝔰 j0).1 - 1) := fun hh => hij (hdeg hh)
    omega
  have hval := Valuation.map_sum_eq_of_lt (v := Valued.v) hj0I hv
  have hzero : Valued.v (∑ i ∈ I, cst F (c i) * ζ_A F (𝔰 i).2) = 0 := by
    rw [hsub, h, map_zero]
  rw [hval, map_mul, v_cst_of_ne_zero F hcj0, one_mul,
    val_zeta_prime F hp (hr j0) (𝔰 j0).2] at hzero
  exact WithZero.exp_ne_zero hzero

end LinearIndependent


section CardDvd

/-- **The lowest base-`p` digit of the greedy fill is the first capacity.** -/
lemma greedy_mod {p : ℕ} (hp : 2 ≤ p) (n : ℕ) : greedy p hp n % p = capp p n 0 := by
  have hp0 : 0 < p := by omega
  have hgen : ∀ r n, Gg p hp r n % p = if r ≤ capp p n 0 then r % p else capp p n 0 := by
    intro r n
    induction r, n using Gg.induct p hp with
    | case1 n =>
        rw [Gg.eq_def, if_pos rfl, if_pos (Nat.zero_le _)]
    | case2 r n hr0 hc0 ih =>
        rw [Gg.eq_def, if_neg hr0, if_pos hc0, Nat.mul_mod_right,
          if_neg (by omega), hc0]
    | case3 r n hr0 hc0 hle =>
        rw [Gg.eq_def, if_neg hr0, if_neg hc0, if_pos hle, if_pos hle]
    | case4 r n hr0 hc0 hnc ih =>
        rw [Gg.eq_def, if_neg hr0, if_neg hc0, if_neg hnc]
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt, if_neg hnc]
        simp only [capp]
        have := Nat.mod_lt n hp0
        omega
  show Gg p hp (p - 1) n % p = capp p n 0
  rw [hgen (p - 1) n]
  by_cases hle : p - 1 ≤ capp p n 0
  · rw [if_pos hle, Nat.mod_eq_of_lt (by omega)]
    simp only [capp] at hle ⊢
    have := Nat.mod_lt n hp0
    omega
  · rw [if_neg hle]

/-- **`jMin F k` modulo `q`** (for `q` prime). -/
lemma jMin_mod_card (hp : (Nat.card F).Prime) (k : ℕ+) :
    jMin F k % Nat.card F = (Nat.card F - 1) - ((k : ℕ) - 1) % Nat.card F := by
  rw [jMin_eq_greedy F hp k, greedy_mod (two_le_card F) ((k : ℕ) - 1)]
  simp only [capp, Nat.pow_zero, Nat.div_one]

/-- **Thakur: `q` divides `s_1(k) = k + jMin F k`** (equivalently `T k ≡ 0 mod q`). -/
theorem card_dvd_TT (hp : (Nat.card F).Prime) {k : ℕ} (hk : 1 ≤ k) :
    Nat.card F ∣ TT (Nat.card F) (two_le_card F) k := by
  rw [TT_eq_add_jMin F hp hk, Nat.dvd_iff_mod_eq_zero]
  have hq2 : 2 ≤ Nat.card F := two_le_card F
  have hq0 : 0 < Nat.card F := by omega
  have hj : jMin F ⟨k, hk⟩ % Nat.card F = (Nat.card F - 1) - (k - 1) % Nat.card F :=
    jMin_mod_card F hp ⟨k, hk⟩
  rw [Nat.add_mod, hj]
  by_cases hr : k % Nat.card F = 0
  · -- `k ≡ 0`: `(k-1) % q = q-1`
    have hkk : k = Nat.card F * (k / Nat.card F) := by
      have h := Nat.div_add_mod k (Nat.card F)
      rw [hr, add_zero] at h
      exact h.symm
    have hkq : 1 ≤ k / Nat.card F := by
      rcases Nat.eq_zero_or_pos (k / Nat.card F) with h0 | h0
      · rw [h0, Nat.mul_zero] at hkk; omega
      · exact h0
    have h1 : (k - 1) % Nat.card F = Nat.card F - 1 := by
      rw [hkk]
      have hdec : Nat.card F * (k / Nat.card F) - 1
          = Nat.card F * (k / Nat.card F - 1) + (Nat.card F - 1) := by
        have hq1 : 1 ≤ Nat.card F := by omega
        have hle : Nat.card F ≤ Nat.card F * (k / Nat.card F) :=
          Nat.le_mul_of_pos_right (Nat.card F) (by omega : 0 < k / Nat.card F)
        rw [Nat.mul_sub_left_distrib, Nat.mul_one]
        omega
      rw [hdec, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    rw [h1, Nat.sub_self, Nat.add_zero, hr, Nat.zero_mod]
  · have h1 : (k - 1) % Nat.card F = k % Nat.card F - 1 :=
      sub_one_mod (Nat.card F) k (by omega) hq0
    rw [h1]
    have h2 : Nat.card F - 1 - (k % Nat.card F - 1) = Nat.card F - k % Nat.card F := by
      have := Nat.mod_lt k hq0
      omega
    rw [h2]
    have h3 : k % Nat.card F + (Nat.card F - k % Nat.card F) = Nat.card F :=
      Nat.add_sub_cancel' (by have := Nat.mod_lt k hq0; omega)
    rw [h3, Nat.mod_self]

end CardDvd

section Regression

attribute [local instance 100] Classical.decEq

/-- The geometric-sum identity in `ℕ`. -/
example : (∑ i ∈ Finset.range 3, (5 : ℕ) ^ i) * (5 - 1) = 5 ^ 3 - 1 :=
  geom_sum_mul_pred_mul 5 3

/-- Over `F₃`: `jMin 2 = (3-1)·2 = 4`. -/
example : jMin (ZMod 3) ⟨2, by norm_num⟩ = 4 := by
  have hp : (Nat.card (ZMod 3)).Prime := by
    rw [Nat.card_eq_fintype_card, ZMod.card]; norm_num
  have h := jMin_eq_pred_mul (ZMod 3) hp (x := 2) (by norm_num) (by norm_num)
  have hc : Nat.card (ZMod 3) = 3 := by rw [Nat.card_eq_fintype_card, ZMod.card]
  rw [hc] at h
  norm_num at h
  exact h

/-- Over `F₃`: `T x = 3 x` on `[1,3]`. -/
example : TT (Nat.card (ZMod 3)) (two_le_card (ZMod 3)) 2 = 6 := by
  have hp : (Nat.card (ZMod 3)).Prime := by
    rw [Nat.card_eq_fintype_card, ZMod.card]; norm_num
  rw [TT_eq_mul (ZMod 3) hp (x := 2) (by norm_num) (by norm_num)]
  have hc : Nat.card (ZMod 3) = 3 := by rw [Nat.card_eq_fintype_card, ZMod.card]
  rw [hc]

/-- Over `F₃`: `T^i x = q^i x`. -/
example : Nat.iterate (TT (Nat.card (ZMod 3)) (two_le_card (ZMod 3))) 4 2
    = Nat.card (ZMod 3) ^ 4 * 2 :=
  TT_iterate_eq_mul (ZMod 3) (by rw [Nat.card_eq_fintype_card, ZMod.card]; norm_num)
    (by norm_num) (by norm_num) 4

/-- Over `F₃`, the depth-two tuple `(1,1)` has degree exponent `3`: `(q-1)·s_1(1) = 6`. -/
example : sSeqG (ZMod 3) 2 (fun _ : Fin 2 => (1 : ℕ+)) 1 = 3 := by
  have hp : (Nat.card (ZMod 3)).Prime := by
    rw [Nat.card_eq_fintype_card, ZMod.card]; norm_num
  have h := sSeqG_eq_lin (ZMod 3) hp 2 (by norm_num) (fun _ : Fin 2 => (1 : ℕ+))
    (by intro i; fin_cases i <;> norm_num)
  have hc : Nat.card (ZMod 3) = 3 := by rw [Nat.card_eq_fintype_card, ZMod.card]
  rw [hc] at h
  norm_num [Fin.sum_univ_two] at h
  linarith

/-- Thakur's divisibility over `F₃`: `3 ∣ T k`. -/
example : Nat.card (ZMod 3) ∣ TT (Nat.card (ZMod 3)) (two_le_card (ZMod 3)) 5 :=
  card_dvd_TT (ZMod 3) (by rw [Nat.card_eq_fintype_card, ZMod.card]; norm_num) (by norm_num)

/-- The codes of two distinct weight-`3` tuples over `F₃` are distinct. -/
example : tupleCode (ZMod 3) ![2, 1] ≠ tupleCode (ZMod 3) ![1, 2] := by
  simp [tupleCode, Fin.sum_univ_two]

end Regression
end ZagierHoffmanPositiveChar
