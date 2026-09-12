import Mathlib
import Submission.IntFun
import Submission.Ell2Update

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open scoped BigOperators
open Submission.IntFun
open Submission.Ell2Update

noncomputable section

/-!
# cor: anticoncentration — geometric kernel on ℤ (Stage 1: summability & mass)

Tikhomirov 2020, Corollary "cor: anticoncentration" (lines ~607-671).  The
corollary applies `th: averaging` to the geometric kernel

    f(t) := (1/m₀) · 2^{-|t|/√n},   t ∈ ℤ,   m₀ := Σ_{t∈ℤ} 2^{-|t|/√n},

whose `log₂ f` is `n^{-1/2}`-Lipschitz and whose ℓ₁-mass is 1.  This module
fixes the kernel (Stage 1): summability of `2^{-r|t|}` over ℤ for `r > 0`,
positivity and total mass of the normalizing constant, and `‖f_r‖₁ = 1`.

The parameter is kept generic (`r : ℝ`, `0 < r`); the corollary later
instantiates `r := 1 / √(n:ℝ)`.  Everything here is `Mathlib`-only except the
`Submission.IntFun.norm₁` interface (and `Submission.Ell2Update.ratioLip` is
imported for Stage 2).
-/

namespace Submission.Anticoncent

/-- the two-sided geometric kernel `2^{-r·|t|}` on ℤ. -/
noncomputable def geom2 (r : ℝ) (t : ℤ) : ℝ :=
  (2 : ℝ) ^ (-r * (|t| : ℝ))

/-- the normalizing constant `m₀(r) := Σ_t 2^{-r|t|}`. -/
noncomputable def m0 (r : ℝ) : ℝ :=
  ∑' t : ℤ, geom2 r t

/-- the normalized kernel `f_r(t) := m₀(r)^{-1} · 2^{-r|t|}`. -/
noncomputable def fk (r : ℝ) (t : ℤ) : ℝ :=
  (1 / m0 r) * geom2 r t

/-- the kernel is positive pointwise. -/
lemma geom2_pos {r : ℝ} (hr : 0 < r) (t : ℤ) : 0 < geom2 r t := by
  dsimp [geom2]
  exact Real.rpow_pos_of_pos (by norm_num) (-r * (|t| : ℝ))

/-- the kernel is nonnegative pointwise. -/
lemma geom2_nonneg {r : ℝ} (hr : 0 < r) (t : ℤ) : 0 ≤ geom2 r t :=
  (geom2_pos hr t).le

/-- the cast of the nonnegative integer `n : ℕ` to ℤ then ℝ has nonnegative abs
equal to `n`. -/
lemma abs_int_nat_cast {n : ℕ} : |(((n : ℤ) : ℝ))| = (n : ℝ) := by
  have hc : (((n : ℤ) : ℝ)) = (n : ℝ) := by norm_num
  rw [hc]
  have hn : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  exact abs_of_nonneg hn

/-- value of the kernel on the nonnegative integer `n`. -/
lemma geom2_ofNat {r : ℝ} (n : ℕ) : geom2 r (n : ℤ) = (2 : ℝ) ^ (-r * (n : ℝ)) := by
  dsimp [geom2]
  congr 1
  congr 1
  rw [abs_int_nat_cast]

/-- value of the kernel on the negative integer `-n` (which is `0` for `n = 0`). -/
lemma geom2_neg_ofNat {r : ℝ} (n : ℕ) : geom2 r (-(n : ℤ)) = (2 : ℝ) ^ (-r * (n : ℝ)) := by
  dsimp [geom2]
  congr 1
  congr 1
  rw [Int.cast_neg, abs_neg]
  exact abs_int_nat_cast

/-- the geometric ratio `q := 2^{-r}` is a positive ratio `< 1` for `r > 0`. -/
lemma rpow_neg_two_lt_one {r : ℝ} (hr : 0 < r) : (2 : ℝ) ^ (-r) < 1 := by
  have h1 : 1 < (2 : ℝ) ^ r := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hr
  have hneg : (2 : ℝ) ^ (-r) = ((2 : ℝ) ^ r)⁻¹ := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hneg]
  exact inv_lt_one_of_one_lt₀ h1

lemma rpow_neg_two_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ (2 : ℝ) ^ (-r) :=
  (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-r)).le

/-- pointwise identity `2^{-r·n} = (2^{-r})^n` on ℕ. -/
lemma geom2_ratio_nat {r : ℝ} (n : ℕ) :
    (2 : ℝ) ^ (-r * (n : ℝ)) = ((2 : ℝ) ^ (-r)) ^ n := by
  calc
    (2 : ℝ) ^ (-r * (n : ℝ)) = ((2 : ℝ) ^ (-r)) ^ ((n : ℝ)) := by
      rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    _ = ((2 : ℝ) ^ (-r)) ^ n := by rw [Real.rpow_natCast]

/-- summability over ℕ of the kernel's nonnegative branch. -/
lemma summable_geom2_nat {r : ℝ} (hr : 0 < r) : Summable (fun n : ℕ => geom2 r (n : ℤ)) := by
  have hq : Summable (fun n : ℕ => ((2 : ℝ) ^ (-r)) ^ n) :=
    summable_geometric_of_lt_one (rpow_neg_two_nonneg hr) (rpow_neg_two_lt_one hr)
  have hpt : (fun n : ℕ => geom2 r (n : ℤ)) = fun n : ℕ => ((2 : ℝ) ^ (-r)) ^ n := by
    funext n
    rw [geom2_ofNat, geom2_ratio_nat]
  rwa [hpt]

/-- summability over ℕ of the kernel's negative branch. -/
lemma summable_geom2_neg {r : ℝ} (hr : 0 < r) : Summable (fun n : ℕ => geom2 r (-(n : ℤ))) := by
  have hq : Summable (fun n : ℕ => ((2 : ℝ) ^ (-r)) ^ n) :=
    summable_geometric_of_lt_one (rpow_neg_two_nonneg hr) (rpow_neg_two_lt_one hr)
  have hpt : (fun n : ℕ => geom2 r (-(n : ℤ))) = fun n : ℕ => ((2 : ℝ) ^ (-r)) ^ n := by
    funext n
    rw [geom2_neg_ofNat, geom2_ratio_nat]
  rwa [hpt]

/-- the two-sided kernel is summable over ℤ for `r > 0`. -/
lemma summable_geom2 {r : ℝ} (hr : 0 < r) : Summable (geom2 r) := by
  rw [summable_int_iff_summable_nat_and_neg]
  exact ⟨summable_geom2_nat hr, summable_geom2_neg hr⟩

/-- the normalizing constant is positive. -/
lemma m0_pos {r : ℝ} (hr : 0 < r) : 0 < m0 r := by
  dsimp [m0]
  exact Summable.tsum_pos (summable_geom2 hr) (geom2_nonneg hr) 0 (geom2_pos hr 0)

lemma m0_ne_zero {r : ℝ} (hr : 0 < r) : m0 r ≠ 0 := ne_of_gt (m0_pos hr)

/-- the normalized kernel is summable. -/
lemma summable_fk {r : ℝ} (hr : 0 < r) : Summable (fk r) := by
  change Summable (fun t : ℤ => (1 / m0 r) * geom2 r t)
  exact Summable.mul_left (1 / m0 r) (summable_geom2 hr)

lemma fk_nonneg {r : ℝ} (hr : 0 < r) (t : ℤ) : 0 ≤ fk r t := by
  change 0 ≤ (1 / m0 r) * geom2 r t
  exact mul_nonneg (div_nonneg zero_le_one (le_of_lt (m0_pos hr))) (geom2_nonneg hr t)

/-- total mass of the unnormalized kernel equals `m₀`. -/
lemma norm₁_geom2 {r : ℝ} : norm₁ (geom2 r) = m0 r := by
  rfl

/-- the normalized kernel has ℓ₁-mass exactly one. -/
lemma norm₁_fk {r : ℝ} (hr : 0 < r) : norm₁ (fk r) = 1 := by
  calc
    norm₁ (fk r) = (1 / m0 r) * norm₁ (geom2 r) := by
      change norm₁ (fun t : ℤ => (1 / m0 r) * geom2 r t) = (1 / m0 r) * norm₁ (geom2 r)
      exact norm₁_const_mul (1 / m0 r) (summable_geom2 hr)
    _ = (1 / m0 r) * (m0 r) := by rw [norm₁_geom2]
    _ = 1 := by field_simp [m0_ne_zero hr]


/-- reverse-triangle for the kernel's abs-terms: `|s| − |t| ≤ |t − s|`. -/
lemma abs_int_le {s t : ℤ} : |(s : ℝ)| - |(t : ℝ)| ≤ |(t : ℝ) - (s : ℝ)| := by
  have htri' : |(((s : ℝ) - (t : ℝ)) + (t : ℝ))| ≤ |(s : ℝ) - (t : ℝ)| + |(t : ℝ)| := abs_add_le _ _
  have hrewrite : |(((s : ℝ) - (t : ℝ)) + (t : ℝ))| = |(s : ℝ)| := by congr 1; ring
  have hcc : |(s : ℝ) - (t : ℝ)| = |(t : ℝ) - (s : ℝ)| := abs_sub_comm _ _
  have h2 : |(s : ℝ)| ≤ |(t : ℝ) - (s : ℝ)| + |(t : ℝ)| := by
    rwa [hrewrite, hcc] at htri'
  nlinarith

/-- `2^{-r|s|} ≤ 2^{r·|t−s|}·2^{−r|t|}` (kernel log₂-Lipschitz step). -/
lemma geom2_step {r : ℝ} (hr : 0 ≤ r) (s t : ℤ) :
    (2 : ℝ) ^ (-r * |(s : ℝ)|) ≤ (2 : ℝ) ^ (r * |(t : ℝ) - (s : ℝ)|) * (2 : ℝ) ^ (-r * |(t : ℝ)|) := by
  have hB : |(t : ℝ)| - |(s : ℝ)| ≤ |(t : ℝ) - (s : ℝ)| := by
    have h := abs_int_le (s := t) (t := s)
    rwa [abs_sub_comm] at h
  have hmul' : r * (|(t : ℝ)| - |(s : ℝ)|) ≤ r * |(t : ℝ) - (s : ℝ)| :=
    mul_le_mul_of_nonneg_left hB hr
  have hexp : -r * |(s : ℝ)| ≤ r * |(t : ℝ) - (s : ℝ)| - r * |(t : ℝ)| := by nlinarith
  have hpow := rpow_two_mono hexp
  have hsplit : (2 : ℝ) ^ (r * |(t : ℝ) - (s : ℝ)| - r * |(t : ℝ)|) =
      (2 : ℝ) ^ (r * |(t : ℝ) - (s : ℝ)|) * (2 : ℝ) ^ (-r * |(t : ℝ)|) := by
    rw [rpow_two_add]
    congr 1
    ring
  exact le_trans hpow (le_of_eq hsplit)

/-- the two-sided kernel is `ratioLip r`. -/
lemma ratioLip_geom2 {r : ℝ} (hr : 0 ≤ r) : ratioLip r (geom2 r) := by
  intro s t
  change (2 : ℝ) ^ (-r * (|s| : ℝ)) ≤ (2 : ℝ) ^ (r * |(t : ℝ) - (s : ℝ)|) * (2 : ℝ) ^ (-r * (|t| : ℝ))
  exact geom2_step hr s t

/-- the normalized kernel is `ratioLip r`. -/
lemma ratioLip_fk {r : ℝ} (hr : 0 < r) : ratioLip r (fk r) := by
  change ratioLip r (fun t : ℤ => (1 / m0 r) * geom2 r t)
  exact ratioLip_mul_const (div_nonneg zero_le_one (le_of_lt (m0_pos hr))) (ratioLip_geom2 hr.le)



/-! ## Stage 3: `m₀(r) ≤ C/r` (upper bound of the normalizing constant)

For `r ∈ (0,1]`, `m₀(r) = Σ_t 2^{-r|t|}` satisfies `m₀(r) ≤ (4/ln2)/r`.
Proof: split the ℤ-sum into the two ℕ branches (via the canonical
`ℤ ≃ ℕ ⊕ ℕ` equivalence), bound each branch's ℓ₁ by the geometric series
`Σ_n q^n = (1-q)^{-1}` (`q := 2^{-r}`), and use `1 - q = 1 - 2^{-r} ≥ r·ln2/2`
on `r ∈ [0,1]` (from `2^{-r} ≥ 1/2` and `2^r - 1 ≥ r·ln2`). -/

/-- `2^{-r} ≥ 1/2` for `r ∈ [0,1]`. -/
lemma rpow_two_neg_ge_half {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : (1 : ℝ) / 2 ≤ (2 : ℝ) ^ (-r) := by
  have hpow : (2 : ℝ) ^ r ≤ 2 := by
    have hmono := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ (2 : ℝ)) hr1
    have h1 : (2 : ℝ) ^ (1 : ℝ) = 2 := by norm_num
    rwa [h1] at hmono
  have hneg : (2 : ℝ) ^ (-r) = ((2 : ℝ) ^ r)⁻¹ := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hneg]
  have hpos : 0 < (2 : ℝ) ^ r := Real.rpow_pos_of_pos (by norm_num) r
  have hle' : (2 : ℝ)⁻¹ ≤ ((2 : ℝ) ^ r)⁻¹ :=
    (inv_le_inv₀ (by norm_num : (0 : ℝ) < 2) hpos).2 hpow
  norm_num at hle'
  exact hle'

/-- `log 2 > 0`. -/
lemma log_two_pos : 0 < Real.log (2 : ℝ) := by
  exact (Real.log_pos_iff (by norm_num : (0 : ℝ) ≤ 2)).mpr (by norm_num : (1 : ℝ) < 2)

/-- `1 − 2^{−r} ≥ r·ln2/2` on `r ∈ [0,1]`. -/
lemma one_sub_rpow_two_neg_ge {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    r * Real.log (2 : ℝ) / 2 ≤ 1 - (2 : ℝ) ^ (-r) := by
  let L : ℝ := Real.log (2 : ℝ)
  have hLpos : 0 < L := by dsimp [L]; exact log_two_pos
  have hhalf : (1 : ℝ) / 2 ≤ (2 : ℝ) ^ (-r) := rpow_two_neg_ge_half hr0 hr1
  have h2r : (2 : ℝ) ^ r = Real.exp (L * r) := by
    dsimp [L]
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hgr : L * r ≤ (2 : ℝ) ^ r - 1 := by
    have hx : L * r + 1 ≤ Real.exp (L * r) := Real.add_one_le_exp (L * r)
    rw [← h2r] at hx
    exact (le_sub_iff_add_le.mpr hx)
  have hneg : (2 : ℝ) ^ (-r) * (2 : ℝ) ^ r = 1 := by
    have h := rpow_two_add_neg r
    rwa [mul_comm] at h
  have hprod : (2 : ℝ) ^ (-r) * ((2 : ℝ) ^ r - 1) = 1 - (2 : ℝ) ^ (-r) := by
    calc
      (2 : ℝ) ^ (-r) * ((2 : ℝ) ^ r - 1) = (2 : ℝ) ^ (-r) * (2 : ℝ) ^ r - (2 : ℝ) ^ (-r) * 1 := by rw [mul_sub]
      _ = 1 - (2 : ℝ) ^ (-r) := by rw [hneg]; ring
  calc
    (r * L) / 2 = (r * L) * (1 / 2) := by ring
    _ ≤ (r * L) * (2 : ℝ) ^ (-r) := by
          exact mul_le_mul_of_nonneg_left hhalf (by positivity : 0 ≤ r * L)
    _ = (2 : ℝ) ^ (-r) * (r * L) := by ring
    _ ≤ (2 : ℝ) ^ (-r) * ((2 : ℝ) ^ r - 1) := by
          have h2pos : 0 ≤ (2 : ℝ) ^ (-r) := (Real.rpow_pos_of_pos (by norm_num) (-r)).le
          have hmul' : (2 : ℝ) ^ (-r) * (L * r) ≤ (2 : ℝ) ^ (-r) * ((2 : ℝ) ^ r - 1) := by
            exact mul_le_mul_of_nonneg_left hgr h2pos
          simpa [mul_comm, mul_left_comm, mul_assoc] using hmul'
    _ = 1 - (2 : ℝ) ^ (-r) := hprod

/-- canonical bijection `ℤ ≃ ℕ ⊕ ℕ` (`inl n ↦ n`, `inr n ↦ −(n+1)`). -/
def intToFun (t : ℤ) : ℕ ⊕ ℕ :=
  if h : 0 ≤ t then Sum.inl (Int.toNat t) else Sum.inr (Int.toNat (-t - 1))

/-- the inverse of `intToFun`. -/
def intInvFun (s : ℕ ⊕ ℕ) : ℤ :=
  Sum.elim (fun n : ℕ => (n : ℤ)) (fun n : ℕ => -((n : ℤ) + 1)) s

/-- canonical bijection `ℤ ≃ ℕ ⊕ ℕ`. -/
def intEquivNatSumNat : ℤ ≃ (ℕ ⊕ ℕ) where
  toFun := intToFun
  invFun := intInvFun
  left_inv := by
    intro t
    by_cases h : 0 ≤ t
    · have ht : (Int.toNat t : ℤ) = t := Int.toNat_of_nonneg h
      simp [intToFun, intInvFun, h, ht]
    · have ht2 : (Int.toNat (-t - 1) : ℤ) = -t - 1 := Int.toNat_of_nonneg (by omega)
      simp [intToFun, intInvFun, h, ht2]
      omega
  right_inv := by
    intro s
    cases s with
    | inl n =>
        have hn : 0 ≤ (n : ℤ) := by exact_mod_cast (Nat.zero_le n)
        have hn2 : (Int.toNat (n : ℤ) : ℤ) = (n : ℤ) := Int.toNat_of_nonneg hn
        simp [intToFun, intInvFun, hn, hn2]
    | inr n =>
        have hx : ¬ 0 ≤ (-((n : ℤ) + 1)) := by omega
        have hz : -(-((n : ℤ) + 1)) - 1 = (n : ℤ) := by omega
        have hinner : (Int.toNat (-(-((n : ℤ) + 1)) - 1) : ℤ) = (n : ℤ) := by
          have h0 : 0 ≤ -(-((n : ℤ) + 1)) - 1 := by omega
          calc
            (Int.toNat (-(-((n : ℤ) + 1)) - 1) : ℤ) = -(-((n : ℤ) + 1)) - 1 := Int.toNat_of_nonneg h0
            _ = (n : ℤ) := hz
        simp [intToFun, intInvFun, hx, hinner]
        omega

/-- value of the kernel on the negative integer `−(n+1)`. -/
lemma geom2_neg_succ {r : ℝ} (n : ℕ) : geom2 r (-((n : ℤ) + 1)) = (2 : ℝ) ^ (-r * ((n : ℝ) + 1)) := by
  dsimp [geom2]
  congr 1
  congr 1
  have hc : (((-((n : ℤ) + 1)) : ℤ) : ℝ) = -((n : ℝ) + 1) := by norm_num
  calc
    |(((-((n : ℤ) + 1)) : ℤ) : ℝ)| = |(-((n : ℝ) + 1))| := by rw [hc]
    _ = (n : ℝ) + 1 := by
          have hn : 0 ≤ (n : ℝ) + 1 := by positivity
          rw [abs_neg]
          exact abs_of_nonneg hn

/-- total mass of the two-sided kernel splits over the two nonnegative branches. -/
lemma m0_eq_split {r : ℝ} (hr : 0 < r) :
    m0 r = (∑' n : ℕ, geom2 r (n : ℤ)) + (∑' n : ℕ, geom2 r (-((n : ℤ) + 1))) := by
  classical
  have hsumB' : Summable (fun n : ℕ => geom2 r (-((n : ℤ) + 1))) := by
    exact (summable_nat_add_iff 1).mpr (summable_geom2_neg hr)
  have hA : HasSum (fun n : ℕ => geom2 r (n : ℤ)) (∑' n : ℕ, geom2 r (n : ℤ)) := (summable_geom2_nat hr).hasSum
  have hB : HasSum (fun n : ℕ => geom2 r (-((n : ℤ) + 1))) (∑' n : ℕ, geom2 r (-((n : ℤ) + 1))) := hsumB'.hasSum
  let F : (ℕ ⊕ ℕ) → ℝ := fun s => geom2 r (intInvFun s)
  have hF : HasSum F ((∑' n : ℕ, geom2 r (n : ℤ)) + (∑' n : ℕ, geom2 r (-((n : ℤ) + 1)))) := by
    apply HasSum.sum
    · have hc : (fun n : ℕ => geom2 r (n : ℤ)) = F ∘ Sum.inl := by
        funext n
        rfl
      rwa [hc]
    · have hc : (fun n : ℕ => geom2 r (-((n : ℤ) + 1))) = F ∘ Sum.inr := by
        funext n
        rfl
      rwa [hc]
  have hZ : HasSum (geom2 r) ((∑' n : ℕ, geom2 r (n : ℤ)) + (∑' n : ℕ, geom2 r (-((n : ℤ) + 1)))) := by
    have hc : (fun s : ℕ ⊕ ℕ => geom2 r (intEquivNatSumNat.symm s)) = F := by
      funext s
      dsimp [F]
      congr 1
    have hleft : HasSum (fun s : ℕ ⊕ ℕ => geom2 r (intEquivNatSumNat.symm s))
        ((∑' n : ℕ, geom2 r (n : ℤ)) + (∑' n : ℕ, geom2 r (-((n : ℤ) + 1)))) := by
      simpa [hc] using hF
    exact (Equiv.hasSum_iff (e := intEquivNatSumNat.symm) (f := geom2 r)
      (a := (∑' n : ℕ, geom2 r (n : ℤ)) + (∑' n : ℕ, geom2 r (-((n : ℤ) + 1))))).mp hleft
  calc
    m0 r = ∑' t : ℤ, geom2 r t := rfl
    _ = (∑' n : ℕ, geom2 r (n : ℤ)) + (∑' n : ℕ, geom2 r (-((n : ℤ) + 1))) := by
          exact HasSum.tsum_eq hZ

/-- value of the nonnegative ℕ branch of the kernel. -/
lemma geom2_nat_tsum {r : ℝ} (hr : 0 < r) :
    (∑' n : ℕ, geom2 r (n : ℤ)) = (1 - (2 : ℝ) ^ (-r))⁻¹ := by
  have hrew : (fun n : ℕ => geom2 r (n : ℤ)) = fun n : ℕ => ((2 : ℝ) ^ (-r)) ^ n := by
    funext n
    rw [geom2_ofNat, geom2_ratio_nat]
  rw [hrew]
  exact tsum_geometric_of_lt_one (rpow_neg_two_nonneg hr) (rpow_neg_two_lt_one hr)

/-- pointwise: the `−(n+1)`-branch term is below the `n`-branch term. -/
lemma geom2_neg_succ_le_ofNat {r : ℝ} (hr : 0 < r) (n : ℕ) :
    geom2 r (-((n : ℤ) + 1)) ≤ geom2 r (n : ℤ) := by
  rw [geom2_neg_succ, geom2_ofNat]
  apply rpow_two_mono
  nlinarith [hr.le]

/-- `m₀(r) ≤ 2·(1 − 2^{−r})⁻¹`. -/
lemma m0_le_two_geom {r : ℝ} (hr : 0 < r) : m0 r ≤ 2 * (1 - (2 : ℝ) ^ (-r))⁻¹ := by
  let q : ℝ := (2 : ℝ) ^ (-r)
  let A : ℝ := ∑' n : ℕ, geom2 r (n : ℤ)
  let B : ℝ := ∑' n : ℕ, geom2 r (-((n : ℤ) + 1))
  have hq : q < 1 := by dsimp [q]; exact rpow_neg_two_lt_one hr
  have hsplit : m0 r = A + B := by
    dsimp [A, B]
    exact m0_eq_split hr
  have hA : A = (1 - q)⁻¹ := by
    dsimp [A, q]
    exact geom2_nat_tsum hr
  have hsumB : Summable (fun n : ℕ => geom2 r (-((n : ℤ) + 1))) := by
    exact (summable_nat_add_iff 1).mpr (summable_geom2_neg hr)
  have hBA : B ≤ A := by
    dsimp [B, A]
    exact Summable.tsum_le_tsum (fun n => geom2_neg_succ_le_ofNat hr n) hsumB (summable_geom2_nat hr)
  have h2 : 0 ≤ A := by
    dsimp [A]
    apply tsum_nonneg
    intro n
    exact geom2_nonneg hr (n : ℤ)
  calc
    m0 r = A + B := hsplit
    _ ≤ A + A := by linarith
    _ = 2 * (1 - q)⁻¹ := by rw [hA]; ring

/-- `m₀(r) ≤ (4/ln2)/r` on `r ∈ (0,1]`. -/
lemma m0_le_div {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) : m0 r ≤ (4 / Real.log (2 : ℝ)) / r := by
  let q : ℝ := (2 : ℝ) ^ (-r)
  have hl : r * Real.log (2 : ℝ) / 2 ≤ 1 - q := by
    dsimp [q]
    exact one_sub_rpow_two_neg_ge hr0.le hr1
  have hposq : 0 < 1 - q := by
    have hq1 : q < 1 := by dsimp [q]; exact rpow_neg_two_lt_one hr0
    linarith
  have hLne : Real.log (2 : ℝ) ≠ 0 := ne_of_gt log_two_pos
  have hm := m0_le_two_geom hr0
  have hcore : 2 * (1 - q)⁻¹ ≤ (4 / Real.log (2 : ℝ)) / r := by
    have h1' : 2 * r ≤ (4 / Real.log (2 : ℝ)) * (1 - q) := by
      have hmul := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 4 / Real.log (2 : ℝ))
      have hcalc : (4 / Real.log (2 : ℝ)) * (r * Real.log (2 : ℝ) / 2) = 2 * r := by
        field_simp [hLne]
        ring
      rwa [hcalc] at hmul
    have hmul2 : 2 * r * (1 - q)⁻¹ ≤ (4 / Real.log (2 : ℝ)) := by
      have hstep := mul_le_mul_of_nonneg_right h1' (by positivity : 0 ≤ (1 - q)⁻¹)
      have hc : (4 / Real.log (2 : ℝ)) * (1 - q) * (1 - q)⁻¹ = (4 / Real.log (2 : ℝ)) := by
        field_simp [hposq.ne']
      rwa [hc] at hstep
    have hmul3 := mul_le_mul_of_nonneg_left hmul2 (by positivity : 0 ≤ r⁻¹)
    have hlc : r⁻¹ * (2 * r * (1 - q)⁻¹) = 2 * (1 - q)⁻¹ := by
      field_simp [ne_of_gt hr0]
    have hrc : r⁻¹ * (4 / Real.log (2 : ℝ)) = (4 / Real.log (2 : ℝ)) / r := by
      field_simp [ne_of_gt hr0]
    rwa [hlc, hrc] at hmul3
  exact le_trans hm hcore

/-- existential form: some constant `C` bounds `m₀(r) ≤ C/r` on `(0,1]`. -/
lemma exists_m0_le_div : ∃ C : ℝ, 0 < C ∧ ∀ {r : ℝ}, 0 < r → r ≤ 1 → m0 r ≤ C / r := by
  refine ⟨4 / Real.log (2 : ℝ), by positivity, ?_⟩
  intro r hr0 hr1
  exact m0_le_div hr0 hr1



/-! ## Stage 4: the pointwise lower bound `f_{1/√n}(t) ≥ c/√n` on `|t| ≤ √n+1`

For `n ≥ 1`, `r := 1/√n`, and integer `t` with `|t| ≤ √n + 1`, the kernel
satisfies `f_r(t) = m₀(r)^{-1}·2^{-r|t|} ≥ (ln2/16)/√n`.  Ingredients:
`1/m₀(r) ≥ (ln2/4)·r` (from `m₀(r) ≤ (4/ln2)/r`) and `2^{-r|t|} ≥ 1/4`
(since `r|t| ≤ (√n+1)/√n ≤ 2`). -/

/-- `1/m₀(r) ≥ (ln2/4)·r` on `r ∈ (0,1]` (inverse of `m₀ ≤ (4/ln2)/r`). -/
lemma one_div_m0_ge {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    (Real.log (2 : ℝ) / 4) * r ≤ 1 / m0 r := by
  have hm0pos : 0 < m0 r := m0_pos hr0
  have hinv := m0_le_div hr0 hr1
  have hpos_rC : 0 < (4 / Real.log (2 : ℝ)) / r := by positivity
  have hinv2 : ((4 / Real.log (2 : ℝ)) / r)⁻¹ ≤ (m0 r)⁻¹ :=
    (inv_le_inv₀ (a := (4 / Real.log (2 : ℝ)) / r) (b := m0 r) hpos_rC hm0pos).2 hinv
  have hsimpl : ((4 / Real.log (2 : ℝ)) / r)⁻¹ = (Real.log (2 : ℝ) / 4) * r := by
    have hLne : Real.log (2 : ℝ) ≠ 0 := ne_of_gt log_two_pos
    field_simp [ne_of_gt hr0, hLne]
  have hg : (Real.log (2 : ℝ) / 4) * r ≤ (m0 r)⁻¹ := by
    rwa [hsimpl] at hinv2
  simpa [one_div] using hg

/-- `2^{-2} = 1/4`. -/
lemma rpow_two_neg2 : (2 : ℝ) ^ (-2 : ℝ) = (1 : ℝ) / 4 := by
  have hneg : (2 : ℝ) ^ (-(2 : ℝ)) = ((2 : ℝ) ^ (2 : ℝ))⁻¹ := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  have h2 : (2 : ℝ) ^ (2 : ℝ) = (2 : ℝ) ^ 2 := by
    simpa using (Real.rpow_natCast (2 : ℝ) 2)
  have h2v : (2 : ℝ) ^ 2 = 4 := by norm_num
  calc
    (2 : ℝ) ^ (-2 : ℝ) = (2 : ℝ) ^ (-(2 : ℝ)) := by norm_num
    _ = ((2 : ℝ) ^ (2 : ℝ))⁻¹ := hneg
    _ = ((2 : ℝ) ^ 2)⁻¹ := by rw [h2]
    _ = (1 : ℝ) / 4 := by
          rw [h2v]
          norm_num

/-- **the interval lower bound**: for `n ≥ 1`, `r := 1/√n`, and `t ∈ ℤ` with
`|t| ≤ √n + 1`, `f_r(t) ≥ (ln2/16)/√n`. -/
lemma fk_lower_bound_on_interval {n : ℕ} (hn : 1 ≤ n) {t : ℤ}
    (ht : (|t| : ℝ) ≤ Real.sqrt (n : ℝ) + 1) :
    (Real.log (2 : ℝ) / 16) / Real.sqrt (n : ℝ) ≤ fk (1 / Real.sqrt (n : ℝ)) t := by
  let r : ℝ := 1 / Real.sqrt (n : ℝ)
  have hsqrt0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hmono : Real.sqrt (1 : ℝ) ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt (by linarith : (1 : ℝ) ≤ (n : ℝ))
    have hsq1 : Real.sqrt (1 : ℝ) = 1 := by norm_num
    rwa [hsq1] at hmono
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by
    dsimp [r]
    exact (div_le_one hsqrt0).2 hsqrt1
  have hrt : r * (|t| : ℝ) ≤ 2 := by
    have hdiv : (|t| : ℝ) / Real.sqrt (n : ℝ) ≤ (Real.sqrt (n : ℝ) + 1) / Real.sqrt (n : ℝ) :=
      div_le_div_of_nonneg_right ht hsqrt0.le
    have hquot : (Real.sqrt (n : ℝ) + 1) / Real.sqrt (n : ℝ) = 1 + 1 / Real.sqrt (n : ℝ) := by
      field_simp [ne_of_gt hsqrt0]
    have hquot2 : 1 + 1 / Real.sqrt (n : ℝ) ≤ 2 := by
      have h1 : 1 / Real.sqrt (n : ℝ) ≤ 1 := (div_le_one hsqrt0).2 hsqrt1
      linarith
    calc
      r * (|t| : ℝ) = (|t| : ℝ) / Real.sqrt (n : ℝ) := by
        dsimp [r]
        field_simp [ne_of_gt hsqrt0]
      _ ≤ (Real.sqrt (n : ℝ) + 1) / Real.sqrt (n : ℝ) := hdiv
      _ = 1 + 1 / Real.sqrt (n : ℝ) := hquot
      _ ≤ 2 := hquot2
  have hpow : (1 : ℝ) / 4 ≤ (2 : ℝ) ^ (-r * (|t| : ℝ)) := by
    have harg : (-2 : ℝ) ≤ -r * (|t| : ℝ) := by nlinarith [hrt]
    have hmono : (2 : ℝ) ^ (-2 : ℝ) ≤ (2 : ℝ) ^ (-r * (|t| : ℝ)) := rpow_two_mono harg
    have h24 : (2 : ℝ) ^ (-2 : ℝ) = (1 : ℝ) / 4 := rpow_two_neg2
    rw [h24] at hmono
    exact hmono
  have h1m0 : (Real.log (2 : ℝ) / 4) * r ≤ 1 / m0 r := one_div_m0_ge hr0 hr1
  have h1m0pos : 0 ≤ 1 / m0 r := (one_div_pos.mpr (m0_pos hr0)).le
  have hprod : ((Real.log (2 : ℝ) / 4) * r) * (1 / 4) ≤ (1 / m0 r) * (2 : ℝ) ^ (-r * (|t| : ℝ)) := by
    exact mul_le_mul h1m0 hpow (by norm_num : (0 : ℝ) ≤ 1 / 4) h1m0pos
  have hcalc : ((Real.log (2 : ℝ) / 4) * r) * (1 / 4) = (Real.log (2 : ℝ) / 16) / Real.sqrt (n : ℝ) := by
    dsimp [r]
    field_simp [ne_of_gt hsqrt0]
    norm_num
  have htarget : (1 / m0 r) * (2 : ℝ) ^ (-r * (|t| : ℝ)) = fk r t := by
    dsimp [fk, geom2]
  have hfinal : (Real.log (2 : ℝ) / 16) / Real.sqrt (n : ℝ) ≤ fk r t := by
    rwa [hcalc, htarget] at hprod
  simpa [r] using hfinal

/-- existential form: some universal constant `c > 0` with
`c/√n ≤ f_{1/√n}(t)` on the interval `|t| ≤ √n + 1`. -/
lemma exists_fk_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (t : ℤ), (|t| : ℝ) ≤ Real.sqrt (n : ℝ) + 1 →
      c / Real.sqrt (n : ℝ) ≤ fk (1 / Real.sqrt (n : ℝ)) t := by
  refine ⟨Real.log (2 : ℝ) / 16, by positivity, ?_⟩
  intro n hn t ht
  exact fk_lower_bound_on_interval hn ht



/-! ## Stage 5: `1/√n ≤ η` for `n ≥ 1/η²` (the `η`-condition for averaging)

When `averaging` is applied to `f := fk (1/√n)`, its output `η` must be an
upper bound of the kernel's own `ratioLip` constant `1/√n`.  The following two
lemmas provide exactly that: `one_div_sqrt_le` is the real inequality
(`√n ≥ 1/η` for `n ≥ 1/η²`), and `ratioLip_fk_of_eta` upgrades the kernel's
`ratioLip (1/√n)` (Stage 2) to `ratioLip η` via `Ell2Update.ratioLip_mono`. -/

/-- `1/√n ≤ η` once `n ≥ 1/η²` (real form). -/
lemma one_div_sqrt_le {η : ℝ} (hη : 0 < η) {n : ℕ} (hn : 1 / η ^ 2 ≤ (n : ℝ)) :
    1 / Real.sqrt (n : ℝ) ≤ η := by
  have hnpos : 0 < (n : ℝ) := by
    have h1 : 0 < 1 / η ^ 2 := by positivity
    linarith
  have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
  rw [div_le_iff₀ hsqrtpos]
  have hη2 : 0 < η ^ 2 := by positivity
  have hm : (1 : ℝ) ≤ η ^ 2 * (n : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hn hη2.le
    have hc : η ^ 2 * (1 / η ^ 2) = 1 := by field_simp [pow_ne_zero 2 (ne_of_gt hη)]
    rwa [hc] at hmul
  have hsq : (η * Real.sqrt (n : ℝ)) ^ 2 = η ^ 2 * (n : ℝ) := by
    rw [mul_pow]
    have hsr : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
    rw [hsr]
  have hgoal2 : (1 : ℝ) ^ 2 ≤ (η * Real.sqrt (n : ℝ)) ^ 2 := by
    rw [hsq]
    norm_num
    exact hm
  have hb0 : 0 ≤ η * Real.sqrt (n : ℝ) := by positivity
  exact le_of_sq_le_sq hgoal2 hb0

/-- the kernel's `ratioLip` constant `1/√n` is below `η` once `n ≥ 1/η²`. -/
lemma ratioLip_fk_of_eta {η : ℝ} (hη : 0 < η) {n : ℕ} (hn : 1 / η ^ 2 ≤ (n : ℝ)) :
    ratioLip η (fk (1 / Real.sqrt (n : ℝ))) := by
  have hsqrtpos : 0 < Real.sqrt (n : ℝ) := by
    have hnpos : 0 < (n : ℝ) := by
      have h1 : 0 < 1 / η ^ 2 := by positivity
      linarith
    exact Real.sqrt_pos.2 hnpos
  have hr : 0 < 1 / Real.sqrt (n : ℝ) := by positivity
  have hle : 1 / Real.sqrt (n : ℝ) ≤ η := one_div_sqrt_le hη hn
  exact ratioLip_mono (fk_nonneg hr) hle (ratioLip_fk hr)



/-! ## Stage 6: `Summable (f^2)` for the kernel + Nat-threshold conversion
(the two `averaging` side conditions that still needed work).

`averaging` requires `hf2 : Summable (fun t => f t ^ 2)` for `f := fk r`;
this holds because `fk r t = (1/m₀ r)·2^{-r|t|}`, so `(fk r t)^2` is a scalar
multiple of `geom2 (2r) t`, which is summable.  `eta_real_of_ceil` converts the
natural-number threshold `⌈1/η²⌉ ≤ n` (used to choose the averaging `n₀`) into
the real inequality `1/η² ≤ (n:ℝ)` required by `ratioLip_fk_of_eta`. -/

/-- `(geom2 r t)² = geom2 (2r) t`. -/
lemma geom2_sq {r : ℝ} (t : ℤ) : (geom2 r t) ^ 2 = geom2 (2 * r) t := by
  let x : ℝ := -r * (|t| : ℝ)
  calc
    ((2 : ℝ) ^ x) ^ 2 = ((2 : ℝ) ^ x) ^ (2 : ℝ) := (Real.rpow_natCast ((2 : ℝ) ^ x) 2).symm
    _ = (2 : ℝ) ^ (x * (2 : ℝ)) := (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) x (2 : ℝ)).symm
    _ = geom2 (2 * r) t := by
          dsimp [geom2]
          congr 1
          dsimp [x]
          ring

/-- `(fk r t)² = (1/m₀ r)²·geom2 (2r) t`. -/
lemma fk_sq_eq {r : ℝ} (t : ℤ) : (fk r t) ^ 2 = (1 / m0 r) ^ 2 * geom2 (2 * r) t := by
  dsimp [fk]
  rw [mul_pow]
  rw [geom2_sq]

/-- square of the normalized kernel is summable for `r > 0`. -/
lemma summable_fk_sq {r : ℝ} (hr : 0 < r) : Summable (fun t : ℤ => (fk r t) ^ 2) := by
  have h2r : 0 < 2 * r := mul_pos (by norm_num) hr
  have hg : Summable (geom2 (2 * r)) := summable_geom2 h2r
  have hs : Summable (fun t => (1 / m0 r) ^ 2 * geom2 (2 * r) t) :=
    Summable.mul_left ((1 / m0 r) ^ 2) hg
  have hpt : (fun t : ℤ => (fk r t) ^ 2) = fun t => (1 / m0 r) ^ 2 * geom2 (2 * r) t := by
    funext t
    exact fk_sq_eq t
  rwa [hpt]

/-- Nat threshold → real inequality: `⌈1/η²⌉ ≤ n` gives `1/η² ≤ (n:ℝ)`. -/
lemma eta_real_of_ceil {η : ℝ} {n : ℕ} (h : Nat.ceil (1 / η ^ 2) ≤ n) :
    1 / η ^ 2 ≤ (n : ℝ) :=
  (Nat.ceil_le (a := 1 / η ^ 2) (n := n)).mp h


end Submission.Anticoncent
