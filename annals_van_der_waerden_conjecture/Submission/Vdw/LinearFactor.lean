import Mathlib
import Submission.Vdw.Counting
import Submission.Vdw.Structure
import Submission.Commons.Data.Real.sum_one_div_pow_le_two

open vanDerWaerdenConjecture
open Function Polynomial Filter Asymptotics
open scoped BigOperators

set_option autoImplicit false

/-!
# Polynomials with a nonzero integer root are rare

Let `Box n H` be the box of monic degree-`n` integer polynomials whose
non-leading coefficients are bounded by `H` (see `Submission.Vdw.Counting`).
This module proves that the number of polynomials in the box having a nonzero
integer root is `O(H^(n-1))` for `n ≥ 3` — the "polynomials with a rational
linear factor" part of the van der Waerden/Chela intransitive count.

The argument is entirely elementary (no complex root bounds).  For
`p = (X - r) · q` with `p` in the box and `r ≠ 0`, comparing constant
coefficients gives `|q₀|·|r| ≤ H`, and comparing the coefficients at
`X^(j+1)` gives inductively `|qⱼ|·|r| ≤ (j+1)·H` for every `j < n-1`
(`rootQuotient_coeff_natAbs_bound`); hence the coefficients of the quotient
`q` are at most `(n·H)/|r|`, so for each root `r` there are at most
`(2·((nH)/|r|)+1)^(n-1)` polynomials divisible by `X-r` in the box
(`rootDiv_ncard_le`).  Polynomials with zero constant term are counted
separately (`ZeroConst`, exactly `(2H+1)^(n-1)` of them); any *nonzero* root
of a polynomial with nonzero constant term satisfies `|r| ≤ H`
(`hasIntRoot_subset`).  Summing the per-root bounds over the `2H` possible
roots yields `O(H^(n-1))` because `∑_{ρ≤H} 1/ρ^(n-1)` is bounded for
`n-1 ≥ 2` (`rootSum_real_le`, `Commons.Data.Real.sum_one_div_pow_le_two`).

The main result is `hasIntRoot_isBigO`.  Since every such polynomial is
reducible, `hasIntRoot_subset_Bad` records that they are all counted by
`E n H` (`Submission.Vdw.Structure.reducible_mem_Bad`).
-/


namespace Submission.Vdw

/-- A monic box polynomial having a nonzero integer root. -/
def HasIntRoot (n H : ℕ) : Set ℤ[X] :=
  {p | p ∈ Box n H ∧ ∃ r : ℤ, r ≠ 0 ∧ (X - C r) ∣ p}

/-- The polynomials in the box divisible by the fixed linear polynomial `X - r`. -/
def RootDiv (n H : ℕ) (r : ℤ) : Set ℤ[X] :=
  {p | p ∈ Box n H ∧ (X - C r) ∣ p}

/-- The polynomials in the box with zero constant term. -/
def ZeroConst (n H : ℕ) : Set ℤ[X] :=
  {p | p ∈ Box n H ∧ p.coeff 0 = 0}

/-- The nonzero integers of absolute value at most `H`. -/
noncomputable def rootFinset (H : ℕ) : Finset ℤ :=
  (Finset.Icc (-(H : ℤ)) (H : ℤ)).filter (fun r : ℤ => r ≠ 0)

section CoeffAlgebra

/-- Coefficients of `C r · q`. -/
lemma coeff_C_mul (r : ℤ) (q : ℤ[X]) (k : ℕ) : (C r * q).coeff k = r * q.coeff k := by
  simp

/-- Coefficient at `0` of `(X - r)·q`. -/
lemma coeff_X_sub_C_mul_zero (r : ℤ) (q : ℤ[X]) :
    ((X - C r) * q).coeff 0 = -r * q.coeff 0 := by
  rw [sub_mul, coeff_sub, Polynomial.coeff_X_mul_zero, coeff_C_mul]
  ring

/-- Coefficient at `k+1` of `(X - r)·q`. -/
lemma coeff_X_sub_C_mul_succ (r : ℤ) (q : ℤ[X]) (k : ℕ) :
    ((X - C r) * q).coeff (k + 1) = q.coeff k - r * q.coeff (k + 1) := by
  rw [sub_mul, coeff_sub, Polynomial.coeff_X_mul, coeff_C_mul]

/-- From the box's coefficient bound (an inequality in `ℤ`) to a bound in `ℕ`. -/
lemma natAbs_coeff_le (p : ℤ[X]) (i : ℕ) {H : ℕ} (h : |p.coeff i| ≤ (H : ℤ)) :
    (p.coeff i).natAbs ≤ H := by
  rw [Int.abs_eq_natAbs] at h
  exact_mod_cast h

/-- The quotient of a monic degree-`n` polynomial (`n ≥ 1`) by the monic linear
polynomial `X - r` is monic of degree `n - 1` (whenever the division is exact). -/
lemma monic_deg_of_X_sub_C_dvd {n : ℕ} {p q : ℤ[X]} (r : ℤ)
    (hn : 1 ≤ n) (hpmon : p.Monic) (hpdeg : p.natDegree = n)
    (hprod : p = (X - C r) * q) :
    q.Monic ∧ q.natDegree = n - 1 := by
  have hXne : X - C r ≠ 0 := Polynomial.Monic.ne_zero (Polynomial.monic_X_sub_C r)
  have hqne : q ≠ 0 := by
    intro hq
    have : p = 0 := by simpa [hq] using hprod
    exact Polynomial.Monic.ne_zero hpmon this
  have hnd1 : (X - C r).natDegree = 1 := Polynomial.natDegree_X_sub_C r
  have hnd : 1 + q.natDegree = n := by
    calc
      1 + q.natDegree = (X - C r).natDegree + q.natDegree := by rw [hnd1]
      _ = ((X - C r) * q).natDegree := by
        rw [Polynomial.natDegree_mul hXne hqne]
      _ = p.natDegree := by rw [hprod]
      _ = n := hpdeg
  have hndq : q.natDegree = n - 1 := by omega
  have hc : p.coeff n = 1 := by
    calc
      p.coeff n = p.coeff p.natDegree := by rw [hpdeg]
      _ = p.leadingCoeff := Polynomial.coeff_natDegree
      _ = 1 := by simpa [Polynomial.Monic.def] using hpmon
  have htop : p.coeff n = q.coeff (n - 1) := by
    rw [hprod]
    have hn1 : n = (n - 1) + 1 := by omega
    conv_lhs => rw [hn1]
    rw [coeff_X_sub_C_mul_succ]
    have hqhigh : q.coeff ((n - 1) + 1) = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [hndq]
      omega
    rw [hqhigh]
    ring
  constructor
  · rw [Polynomial.Monic.def]
    rw [← Polynomial.coeff_natDegree, hndq]
    rw [← htop]
    exact hc
  · exact hndq

/-- The recursion step: if `(X-r)·q` is in the box then
`|r| · |qⱼ| ≤ (j+1)·H` for all `j < n-1`.  Bound in `ℕ`. -/
lemma rootQuotient_coeff_natAbs_bound (n H : ℕ) {r : ℤ} (hr : r ≠ 0) (q : ℤ[X])
    (hbox : (X - C r) * q ∈ Box n H) :
    ∀ j : ℕ, j < n - 1 →
      r.natAbs * (q.coeff j).natAbs ≤ (j + 1) * H := by
  intro j hj
  induction' j with j ih generalizing q
  · -- base: constant coefficients
    have hb : |((X - C r) * q).coeff 0| ≤ (H : ℤ) := hbox.2.2 0 (by omega)
    have hb' : (((X - C r) * q).coeff 0).natAbs ≤ H := natAbs_coeff_le _ 0 hb
    have hmain : r.natAbs * (q.coeff 0).natAbs = (((X - C r) * q).coeff 0).natAbs := by
      rw [coeff_X_sub_C_mul_zero]
      rw [Int.natAbs_mul, Int.natAbs_neg]
    rw [hmain]
    simpa using hb'
  · -- step: j+1
    have hlt1 : j < n - 1 := by omega
    have hlt2 : j + 1 < n := by omega
    have hb : |((X - C r) * q).coeff (j + 1)| ≤ (H : ℤ) := hbox.2.2 (j + 1) hlt2
    have hb' : (((X - C r) * q).coeff (j + 1)).natAbs ≤ H := natAbs_coeff_le _ (j + 1) hb
    have hrel : r * q.coeff (j + 1) = q.coeff j - ((X - C r) * q).coeff (j + 1) := by
      rw [coeff_X_sub_C_mul_succ r q j]
      ring
    have hnm : r.natAbs * (q.coeff (j + 1)).natAbs =
        ((q.coeff j - ((X - C r) * q).coeff (j + 1))).natAbs := by
      rw [← hrel, Int.natAbs_mul]
    rw [hnm]
    calc
      ((q.coeff j - ((X - C r) * q).coeff (j + 1))).natAbs
          ≤ (q.coeff j).natAbs + (((X - C r) * q).coeff (j + 1)).natAbs :=
        Int.natAbs_sub_le _ _
      _ ≤ (j + 1) * H + H := by
        have hrho : 0 < r.natAbs := Int.natAbs_pos.mpr hr
        have h1 : 1 ≤ r.natAbs := by omega
        have hqj : (q.coeff j).natAbs ≤ (j + 1) * H := by
          calc
            (q.coeff j).natAbs = 1 * (q.coeff j).natAbs := by rw [one_mul]
            _ ≤ r.natAbs * (q.coeff j).natAbs :=
              Nat.mul_le_mul_right (q.coeff j).natAbs h1
            _ ≤ (j + 1) * H := ih q hbox hlt1
        exact Nat.add_le_add hqj hb'
      _ = (j + 2) * H := by ring
      _ = ((j + 1) + 1) * H := by ring

end CoeffAlgebra

section Counting

/-- The union (over `ρ = 1..H`) of the two root-divisibility sets with roots
`±ρ`.  Every box polynomial with a nonzero integer root and nonzero constant
term lies in one of these. -/
def rootUnion (n H : ℕ) : Set ℤ[X] :=
  {p | ∃ ρ : ℕ, ρ ∈ Finset.Icc 1 H ∧ (p ∈ RootDiv n H (ρ : ℤ) ∨ p ∈ RootDiv n H (-(ρ : ℤ)))}

/-- Quotients `q = p / (X - r)` for `p` in the box divisible by `X - r`. -/
def rootQuotients (n H : ℕ) (r : ℤ) : Set ℤ[X] :=
  {q | q.Monic ∧ q.natDegree = n - 1 ∧ (X - C r) * q ∈ Box n H}

/-- `RootDiv n H r` is the image of the quotients under `q ↦ (X-r)·q`. -/
lemma rootDiv_eq_image (n H : ℕ) (r : ℤ) (hn : 1 ≤ n) :
    RootDiv n H r = (fun q : ℤ[X] => (X - C r) * q) '' rootQuotients n H r := by
  ext p
  constructor
  · intro hp
    rcases hp with ⟨hbox, hdiv⟩
    rcases hdiv with ⟨c, hc⟩
    have hdeg : p.natDegree = n := Polynomial.natDegree_eq_of_degree_eq_some hbox.2.1
    have hm := monic_deg_of_X_sub_C_dvd r hn hbox.1 hdeg hc
    refine ⟨c, ?_, ?_⟩
    · exact ⟨hm.1, hm.2, by
        rw [← hc]
        exact hbox⟩
    · exact hc.symm
  · intro hp
    rcases hp with ⟨q, hq, hpq⟩
    have hpq' : p = (X - C r) * q := hpq.symm
    exact ⟨by
      rw [hpq']
      exact hq.2.2, ⟨q, hpq'⟩⟩

/-- For `p = (X - r)·q` in the box with `r ≠ 0`, coefficients of `q` below the
top satisfy `|q_j|·|r| ≤ (j+1)·H` and hence `|q_j| ≤ (n·H)/|r|`. -/
lemma rootQuotient_coeff_le (n H : ℕ) (r : ℤ) (hr : r ≠ 0) (q : ℤ[X])
    (hbox : (X - C r) * q ∈ Box n H) {j : ℕ} (hj : j < n - 1) :
    (q.coeff j).natAbs ≤ (n * H) / r.natAbs := by
  have hb := rootQuotient_coeff_natAbs_bound n H hr q hbox j hj
  have hρ0 : 0 < r.natAbs := Int.natAbs_pos.mpr hr
  have hle : (q.coeff j).natAbs ≤ ((j + 1) * H) / r.natAbs := by
    exact (Nat.le_div_iff_mul_le hρ0).mpr (by simpa [mul_comm] using hb)
  have hjle : (j + 1) ≤ n := by omega
  calc
    (q.coeff j).natAbs ≤ ((j + 1) * H) / r.natAbs := hle
    _ ≤ (n * H) / r.natAbs := Nat.div_le_div_right (Nat.mul_le_mul_right H hjle)

/-- The box polynomials divisible by `X - r` are at most `(2·(nH/|r|)+1)^(n-1)`
in number. -/
lemma rootDiv_ncard_le (n H : ℕ) (r : ℤ) (hr : r ≠ 0) (hn : 1 ≤ n) :
    (RootDiv n H r).ncard ≤ (2 * ((n * H) / r.natAbs) + 1) ^ (n - 1) := by
  have hset := rootDiv_eq_image n H r hn
  have hQsub : rootQuotients n H r ⊆ Box (n - 1) ((n * H) / r.natAbs) := by
    intro q hq
    refine ⟨hq.1, ?_, ?_⟩
    · have hqne : q ≠ 0 := Polynomial.Monic.ne_zero hq.1
      rw [Polynomial.degree_eq_natDegree hqne, hq.2.1]
    · intro j hj
      have hb := rootQuotient_coeff_le n H r hr q hq.2.2 hj
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hb
  calc
    (RootDiv n H r).ncard = ((fun q : ℤ[X] => (X - C r) * q) '' rootQuotients n H r).ncard := by
      rw [hset]
    _ = (rootQuotients n H r).ncard := by
      apply Set.ncard_image_of_injective
      intro a b hab
      have hX : (X - C r) ≠ 0 := Polynomial.Monic.ne_zero (Polynomial.monic_X_sub_C r)
      exact mul_left_cancel₀ hX hab
    _ ≤ (Box (n - 1) ((n * H) / r.natAbs)).ncard :=
      Set.ncard_le_ncard hQsub (box_finite (n - 1) ((n * H) / r.natAbs))
    _ = (2 * ((n * H) / r.natAbs) + 1) ^ (n - 1) := Box_ncard_eq (n - 1) ((n * H) / r.natAbs)

/-- The zero-constant-term box polynomials are exactly the `X`-multiples of the
`(n-1)`-box; there are `(2H+1)^(n-1)` of them. -/
lemma ZeroConst_ncard (n H : ℕ) (hn : 1 ≤ n) :
    (ZeroConst n H).ncard = (2 * H + 1) ^ (n - 1) := by
  have hset : ZeroConst n H = (fun q : ℤ[X] => X * q) '' Box (n - 1) H := by
    ext p
    constructor
    · intro hp
      rcases hp with ⟨hbox, hc0⟩
      have hXdvd : X ∣ p := (Polynomial.X_dvd_iff).mpr hc0
      rcases hXdvd with ⟨c, hc⟩
      refine ⟨c, ?_, ?_⟩
      · have hdeg : p.natDegree = n := Polynomial.natDegree_eq_of_degree_eq_some hbox.2.1
        have hcprod : p = (X - C (0 : ℤ)) * c := by
          rw [hc]
          simp
        have hm := monic_deg_of_X_sub_C_dvd (0 : ℤ) hn hbox.1 hdeg hcprod
        have hqne : c ≠ 0 := Polynomial.Monic.ne_zero hm.1
        refine ⟨hm.1, ?_, ?_⟩
        · rw [Polynomial.degree_eq_natDegree hqne, hm.2]
        · intro j hj
          have hpb : |p.coeff (j + 1)| ≤ (H : ℤ) := hbox.2.2 (j + 1) (by omega)
          calc
            |c.coeff j| = |(X * c).coeff (j + 1)| := by
              congr 1
              rw [Polynomial.coeff_X_mul]
            _ = |p.coeff (j + 1)| := by
              congr 1
              rw [← hc]
            _ ≤ (H : ℤ) := hpb
      · exact hc.symm
    · intro hp
      rcases hp with ⟨q, hq, hpq⟩
      have hpq' : p = X * q := hpq.symm
      refine ⟨?_, ?_⟩
      · rw [hpq']
        exact X_mul_mem_box q hq (by omega : 1 ≤ n)
      · rw [← hpq]
        simp
  calc
    (ZeroConst n H).ncard = ((fun q : ℤ[X] => X * q) '' Box (n - 1) H).ncard := by rw [hset]
    _ = (Box (n - 1) H).ncard := Set.ncard_image_of_injective (Box (n - 1) H) X_mul_left_injective
    _ = (2 * H + 1) ^ (n - 1) := Box_ncard_eq (n - 1) H

/-- A finite union bound for `ncard` (union written with a set builder). -/
lemma ncard_biUnion_finset_le {α ι : Type*} (F : Finset ι) (U : ι → Set α) :
    {x | ∃ i ∈ F, x ∈ U i}.ncard ≤ ∑ i ∈ F, (U i).ncard := by
  classical
  refine Finset.induction_on F ?_ ?_
  · simp
  · intro i F hi ih
    have hset : {x | ∃ j ∈ insert i F, x ∈ U j} =
        {x | ∃ j ∈ F, x ∈ U j} ∪ U i := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨j, hj, hxj⟩
        rw [Finset.mem_insert] at hj
        rcases hj with rfl | hjF
        · exact Or.inr hxj
        · exact Or.inl ⟨j, hjF, hxj⟩
      · intro hx
        rcases hx with hx | hx
        · rcases hx with ⟨j, hjF, hxj⟩
          exact ⟨j, Finset.mem_insert.mpr (Or.inr hjF), hxj⟩
        · exact ⟨i, Finset.mem_insert.mpr (Or.inl rfl), hx⟩
    calc
      {x | ∃ j ∈ insert i F, x ∈ U j}.ncard =
          ({x | ∃ j ∈ F, x ∈ U j} ∪ U i).ncard := by rw [hset]
      _ ≤ {x | ∃ j ∈ F, x ∈ U j}.ncard + (U i).ncard := Set.ncard_union_le _ _
      _ ≤ (∑ j ∈ F, (U j).ncard) + (U i).ncard := Nat.add_le_add_right ih _
      _ = ∑ j ∈ insert i F, (U j).ncard := by
        rw [Finset.sum_insert hi]
        ac_rfl

/-- The union over the roots is no larger than twice the sum of the per-size
bounds. -/
lemma ncard_rootUnion_le (n H : ℕ) (hn : 1 ≤ n) :
    (rootUnion n H).ncard ≤ 2 * (∑ ρ ∈ Finset.Icc 1 H,
      (2 * ((n * H) / ρ) + 1) ^ (n - 1)) := by
  have hstep : ∀ ρ ∈ Finset.Icc 1 H,
      (RootDiv n H (ρ : ℤ) ∪ RootDiv n H (-(ρ : ℤ))).ncard
        ≤ 2 * ((2 * ((n * H) / ρ) + 1) ^ (n - 1)) := by
    intro ρ hρ
    have hρ1 : 1 ≤ ρ := (Finset.mem_Icc.mp hρ).1
    have hρpos : 0 < ρ := by omega
    have hz : (0 : ℤ) < (ρ : ℤ) := by exact_mod_cast hρpos
    have hρne : (ρ : ℤ) ≠ 0 := ne_of_gt hz
    have hρne' : -(ρ : ℤ) ≠ 0 := (neg_ne_zero).mpr hρne
    have h1 := rootDiv_ncard_le n H (ρ : ℤ) hρne hn
    have h2 : (RootDiv n H (-(ρ : ℤ))).ncard ≤ (2 * ((n * H) / ρ) + 1) ^ (n - 1) := by
      have h2' := rootDiv_ncard_le n H (-(ρ : ℤ)) hρne' hn
      simpa [Int.natAbs_neg, Int.natAbs_natCast] using h2'
    calc
      (RootDiv n H (ρ : ℤ) ∪ RootDiv n H (-(ρ : ℤ))).ncard
          ≤ (RootDiv n H (ρ : ℤ)).ncard + (RootDiv n H (-(ρ : ℤ))).ncard :=
        Set.ncard_union_le _ _
      _ ≤ (2 * ((n * H) / ρ) + 1) ^ (n - 1) + (2 * ((n * H) / ρ) + 1) ^ (n - 1) := by
        exact Nat.add_le_add h1 h2
      _ = 2 * ((2 * ((n * H) / ρ) + 1) ^ (n - 1)) := by ring
  have h0 := ncard_biUnion_finset_le (Finset.Icc 1 H)
    (fun ρ : ℕ => (RootDiv n H (ρ : ℤ) ∪ RootDiv n H (-(ρ : ℤ))))
  calc
    (rootUnion n H).ncard = {x | ∃ ρ ∈ Finset.Icc 1 H,
        x ∈ (RootDiv n H (ρ : ℤ) ∪ RootDiv n H (-(ρ : ℤ)))}.ncard := by rfl
    _ ≤ ∑ ρ ∈ Finset.Icc 1 H,
        (RootDiv n H (ρ : ℤ) ∪ RootDiv n H (-(ρ : ℤ))).ncard := h0
    _ ≤ ∑ ρ ∈ Finset.Icc 1 H, 2 * ((2 * ((n * H) / ρ) + 1) ^ (n - 1)) := by
      exact Finset.sum_le_sum hstep
    _ = 2 * (∑ ρ ∈ Finset.Icc 1 H, (2 * ((n * H) / ρ) + 1) ^ (n - 1)) := by
      rw [Finset.mul_sum]

/-- Containment: a box polynomial with a nonzero integer root either has zero
constant term or is divisible by `X - ρ` or `X + ρ` for some `1 ≤ ρ ≤ H`. -/
lemma hasIntRoot_subset (n H : ℕ) (hn : 1 ≤ n) :
    HasIntRoot n H ⊆ ZeroConst n H ∪ rootUnion n H := by
  intro p hp
  rcases hp with ⟨hbox, r0, hr0, hdiv⟩
  by_cases hc0 : p.coeff 0 = 0
  · exact Or.inl ⟨hbox, hc0⟩
  · right
    show ∃ ρ', ρ' ∈ Finset.Icc 1 H ∧
      (p ∈ RootDiv n H (ρ' : ℤ) ∨ p ∈ RootDiv n H (-(ρ' : ℤ)))
    rcases hdiv with ⟨q0, hpq0⟩
    have hc0rel' : p.coeff 0 = -(q0.coeff 0 * r0) := by
      rw [hpq0]
      have hX : (X - C r0).coeff 0 = -r0 := by simp
      have hprod : ((X - C r0) * q0).coeff 0 = (X - C r0).coeff 0 * q0.coeff 0 := by
        simp
      rw [hprod, hX]
      ring
    have hq0ne : q0.coeff 0 ≠ 0 := by
      intro h
      apply hc0
      rw [hc0rel']
      rw [h]
      norm_num
    have hc0b : |p.coeff 0| ≤ (H : ℤ) := hbox.2.2 0 (by omega)
    have hmul : |r0| * |q0.coeff 0| = |p.coeff 0| := by
      calc
        |r0| * |q0.coeff 0| = |r0 * q0.coeff 0| := by rw [abs_mul]
        _ = |q0.coeff 0 * r0| := by rw [mul_comm]
        _ = |-(q0.coeff 0 * r0)| := by rw [abs_neg]
        _ = |p.coeff 0| := by rw [← hc0rel']
    have hq0abs : (1 : ℤ) ≤ |q0.coeff 0| := Int.one_le_abs hq0ne
    have hle1 : |r0| ≤ |r0| * |q0.coeff 0| := by
      calc
        |r0| = |r0| * 1 := by ring
        _ ≤ |r0| * |q0.coeff 0| :=
          mul_le_mul_of_nonneg_left hq0abs (abs_nonneg _)
    have hr0b : |r0| ≤ (H : ℤ) := by
      calc
        |r0| ≤ |r0| * |q0.coeff 0| := hle1
        _ ≤ (H : ℤ) := by
          rw [hmul]
          exact hc0b
    let ρ : ℕ := r0.natAbs
    have hρ1 : 1 ≤ ρ := by
      dsimp [ρ]
      exact Int.natAbs_pos.mpr hr0
    have hρH : ρ ≤ H := by
      have hb' : ((r0.natAbs : ℤ) ≤ (H : ℤ)) := by
        rw [Int.abs_eq_natAbs] at hr0b
        exact hr0b
      have hn' : r0.natAbs ≤ H := by exact_mod_cast hb'
      simpa [ρ] using hn'
    have hρmem : ρ ∈ Finset.Icc 1 H := Finset.mem_Icc.mpr ⟨hρ1, hρH⟩
    by_cases hpos : 0 ≤ r0
    · refine ⟨ρ, hρmem, Or.inl ⟨hbox, ?_⟩⟩
      have hcast : (ρ : ℤ) = r0 := by
        dsimp [ρ]
        exact Int.ofNat_natAbs_of_nonneg hpos
      rw [hcast]
      exact ⟨q0, hpq0⟩
    · refine ⟨ρ, hρmem, Or.inr ⟨hbox, ?_⟩⟩
      have hcast' : (ρ : ℤ) = -r0 := by
        dsimp [ρ]
        rw [← Int.natAbs_neg]
        exact Int.ofNat_natAbs_of_nonneg (by omega : 0 ≤ -r0)
      have hcast : -(ρ : ℤ) = r0 := by omega
      rw [hcast]
      exact ⟨q0, hpq0⟩
lemma hasIntRoot_ncard_le (n H : ℕ) (hn : 1 ≤ n) :
    (HasIntRoot n H).ncard ≤ (2 * H + 1) ^ (n - 1) +
      2 * (∑ ρ ∈ Finset.Icc 1 H, (2 * ((n * H) / ρ) + 1) ^ (n - 1)) := by
  have hsub := hasIntRoot_subset n H hn
  have hunion_fin : (ZeroConst n H ∪ rootUnion n H).Finite := by
    refine (box_finite n H).subset ?_
    intro p hp
    rcases hp with hz | hu
    · exact hz.1
    · rcases hu with ⟨ρ, hρ, hr | hr⟩
      · exact hr.1
      · exact hr.1
  have h1 : (HasIntRoot n H).ncard ≤ (ZeroConst n H ∪ rootUnion n H).ncard :=
    Set.ncard_le_ncard hsub hunion_fin
  have h2 : (ZeroConst n H ∪ rootUnion n H).ncard
      ≤ (ZeroConst n H).ncard + (rootUnion n H).ncard := Set.ncard_union_le _ _
  have h3 := ncard_rootUnion_le n H hn
  calc
    (HasIntRoot n H).ncard ≤ (ZeroConst n H ∪ rootUnion n H).ncard := h1
    _ ≤ (ZeroConst n H).ncard + (rootUnion n H).ncard := h2
    _ ≤ (2 * H + 1) ^ (n - 1) + 2 * (∑ ρ ∈ Finset.Icc 1 H,
        (2 * ((n * H) / ρ) + 1) ^ (n - 1)) := by
      rw [ZeroConst_ncard n H hn]
      exact Nat.add_le_add_left h3 ((2 * H + 1) ^ (n - 1))

/-- Two-step extraction: `Σ (A·B·f) = A·B·Σf`. -/
lemma sum_mul_two {ι : Type*} (F : Finset ι) (A B : ℝ) (f : ι → ℝ) :
    (∑ i ∈ F, A * B * f i) = A * B * (∑ i ∈ F, f i) := by
  rw [Finset.mul_sum]

/-- The root sum is `O(H^(n-1))` for `n ≥ 3`:
`∑_{ρ=1}^H (2·(nH/ρ)+1)^(n-1) ≤ 2·(3n)^(n-1)·H^(n-1)`. -/
lemma rootSum_real_le (n H : ℕ) (hn3 : 3 ≤ n) (hH : 1 ≤ H) :
    (∑ ρ ∈ Finset.Icc 1 H,
        (((2 * ((n * H) / ρ) + 1) ^ (n - 1) : ℕ) : ℝ))
      ≤ 2 * (3 * (n : ℝ)) ^ (n - 1) * (H : ℝ) ^ (n - 1) := by
  have hn1 : 1 ≤ n := by omega
  have hnsum : 2 ≤ n - 1 := by omega
  have hY : ∀ ρ ∈ Finset.Icc 1 H,
      (((2 * ((n * H) / ρ) + 1) ^ (n - 1) : ℕ) : ℝ)
        ≤ ((3 * (n : ℝ) * (H : ℝ)) / (ρ : ℝ)) ^ (n - 1) := by
    intro ρ hρ
    have hρ1 : 1 ≤ ρ := (Finset.mem_Icc.mp hρ).1
    have hρH : ρ ≤ H := (Finset.mem_Icc.mp hρ).2
    have hρ0 : 0 < (ρ : ℝ) := by exact_mod_cast hρ1
    have hqmul : ((((n * H) / ρ : ℕ) : ℝ) * (ρ : ℝ)) ≤ ((n * H : ℕ) : ℝ) := by
      exact_mod_cast Nat.div_mul_le_self (n * H) ρ
    have hq : (((n * H) / ρ : ℕ) : ℝ) ≤ ((n * H : ℝ) / (ρ : ℝ)) := by
      have hqmul' : ((((n * H) / ρ : ℕ) : ℝ) * (ρ : ℝ)) ≤ (n : ℝ) * (H : ℝ) := by
        simpa [Nat.cast_mul] using hqmul
      exact (le_div_iff₀ hρ0).mpr hqmul'
    have hn1r : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have h1 : (1 : ℝ) ≤ (H : ℝ) / (ρ : ℝ) := by
      have hle : (ρ : ℝ) ≤ (H : ℝ) := by exact_mod_cast hρH
      exact (one_le_div hρ0).2 hle
    have hnH_ge : (1 : ℝ) ≤ ((n : ℝ) * (H : ℝ)) / (ρ : ℝ) := by
      calc
        (1 : ℝ) ≤ (n : ℝ) := hn1r
        _ ≤ (n : ℝ) * (1 : ℝ) := by rw [mul_one]
        _ ≤ (n : ℝ) * ((H : ℝ) / (ρ : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (by exact_mod_cast (Nat.zero_le n))
        _ = ((n : ℝ) * (H : ℝ)) / (ρ : ℝ) := by ring
    have hlebase : (2 * (((n * H) / ρ : ℕ) : ℝ) + 1)
        ≤ (3 * (n : ℝ) * (H : ℝ)) / (ρ : ℝ) := by
      have hh1 : (2 * (((n * H) / ρ : ℕ) : ℝ) + 1) ≤ 2 * ((n * H : ℝ) / (ρ : ℝ)) + 1 := by
        nlinarith
      have hh2 : 2 * ((n * H : ℝ) / (ρ : ℝ)) + 1 ≤ 3 * ((n * H : ℝ) / (ρ : ℝ)) := by
        nlinarith
      have hh3 : 3 * ((n * H : ℝ) / (ρ : ℝ)) = (3 * (n : ℝ) * (H : ℝ)) / (ρ : ℝ) := by
        field_simp
      calc
        (2 * (((n * H) / ρ : ℕ) : ℝ) + 1) ≤ 2 * ((n * H : ℝ) / (ρ : ℝ)) + 1 := hh1
        _ ≤ 3 * ((n * H : ℝ) / (ρ : ℝ)) := hh2
        _ = (3 * (n : ℝ) * (H : ℝ)) / (ρ : ℝ) := hh3
    have hbase0 : (0 : ℝ) ≤ (2 * (((n * H) / ρ : ℕ) : ℝ) + 1) := by positivity
    calc
      (((2 * ((n * H) / ρ) + 1) ^ (n - 1) : ℕ) : ℝ)
          = (2 * (((n * H) / ρ : ℕ) : ℝ) + 1) ^ (n - 1) := by
            norm_num [Nat.cast_pow]
      _ ≤ ((3 * (n : ℝ) * (H : ℝ)) / (ρ : ℝ)) ^ (n - 1) := by
        exact pow_le_pow_left₀ hbase0 hlebase (n - 1)
  have hEq : ∀ ρ ∈ Finset.Icc 1 H,
      ((3 * (n : ℝ) * (H : ℝ)) / (ρ : ℝ)) ^ (n - 1)
        = (3 * (n : ℝ)) ^ (n - 1) * (H : ℝ) ^ (n - 1) * (1 / (ρ : ℝ)) ^ (n - 1) := by
    intro ρ hρ
    have hρ1 : 1 ≤ ρ := (Finset.mem_Icc.mp hρ).1
    have hρpos : 0 < (ρ : ℝ) := by exact_mod_cast hρ1
    have hρne : (ρ : ℝ) ≠ 0 := ne_of_gt hρpos
    have hdiv : (3 * (n : ℝ) * (H : ℝ)) / (ρ : ℝ) =
        (3 * (n : ℝ)) * (H : ℝ) * (1 / (ρ : ℝ)) := by
      field_simp [hρne]
    calc
      ((3 * (n : ℝ) * (H : ℝ)) / (ρ : ℝ)) ^ (n - 1)
          = ((3 * (n : ℝ)) * (H : ℝ) * (1 / (ρ : ℝ))) ^ (n - 1) := by rw [hdiv]
      _ = (3 * (n : ℝ)) ^ (n - 1) * (H : ℝ) ^ (n - 1) * (1 / (ρ : ℝ)) ^ (n - 1) := by
            rw [mul_pow, mul_pow]
  have hterm : ∀ ρ ∈ Finset.Icc 1 H,
      (((2 * ((n * H) / ρ) + 1) ^ (n - 1) : ℕ) : ℝ)
        ≤ (3 * (n : ℝ)) ^ (n - 1) * (H : ℝ) ^ (n - 1) * (1 / (ρ : ℝ)) ^ (n - 1) := by
    intro ρ hρ
    exact le_trans (hY ρ hρ) (le_of_eq (hEq ρ hρ))
  have hcomm := Commons.Data.Real.sum_one_div_pow_le_two H (n - 1) hnsum
  have hc : (∑ ρ ∈ Finset.Icc 1 H, (1 / (ρ : ℝ)) ^ (n - 1)) ≤ 2 := by
    convert hcomm using 1
    apply Finset.sum_congr rfl
    intro ρ hρ
    have hρpos : 0 < (ρ : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hρ).1
    have hρne : (ρ : ℝ) ≠ 0 := ne_of_gt hρpos
    have hpow : (1 / (ρ : ℝ)) ^ (n - 1) = 1 / (ρ : ℝ) ^ (n - 1) := by
      rw [div_pow, one_pow]
    rw [hpow]
  calc
    (∑ ρ ∈ Finset.Icc 1 H,
        (((2 * ((n * H) / ρ) + 1) ^ (n - 1) : ℕ) : ℝ))
        ≤ ∑ ρ ∈ Finset.Icc 1 H,
            ((3 * (n : ℝ)) ^ (n - 1) * (H : ℝ) ^ (n - 1) * (1 / (ρ : ℝ)) ^ (n - 1)) := by
          exact Finset.sum_le_sum hterm
    _ = (3 * (n : ℝ)) ^ (n - 1) * (H : ℝ) ^ (n - 1) *
          (∑ ρ ∈ Finset.Icc 1 H, (1 / (ρ : ℝ)) ^ (n - 1)) := by
          rw [sum_mul_two]
    _ ≤ (3 * (n : ℝ)) ^ (n - 1) * (H : ℝ) ^ (n - 1) * 2 := by
          have hA0 : (0 : ℝ) ≤ (3 * (n : ℝ)) ^ (n - 1) := by positivity
          have hB0 : (0 : ℝ) ≤ (H : ℝ) ^ (n - 1) := by positivity
          exact mul_le_mul_of_nonneg_left hc (mul_nonneg hA0 hB0)
    _ = 2 * (3 * (n : ℝ)) ^ (n - 1) * (H : ℝ) ^ (n - 1) := by
          ring


/-- Pointwise real bound (eventually in `H`): with `n ≥ 3` and `H ≥ 1`,
`#HasIntRoot ≤ (3^(n-1) + 4·(3n)^(n-1))·H^(n-1)`. -/
lemma hasIntRoot_real_bound (n H : ℕ) (hn3 : 3 ≤ n) (hH : 1 ≤ H) :
    ((HasIntRoot n H).ncard : ℝ) ≤
      ((3 ^ (n - 1) + 4 * (3 * n) ^ (n - 1) : ℕ) : ℝ) * (H : ℝ) ^ (n - 1) := by
  have hn1 : 1 ≤ n := by omega
  have hnc := hasIntRoot_ncard_le n H hn1
  have hzero : ((2 * H + 1 : ℕ) ^ (n - 1) : ℝ) ≤ (3 ^ (n - 1) : ℝ) * (H : ℝ) ^ (n - 1) := by
    have hcast2 : ((2 * H + 1 : ℕ) : ℝ) = 2 * (H : ℝ) + 1 := by
      norm_num [Nat.cast_add, Nat.cast_mul]
    have hle : ((2 * H + 1 : ℕ) : ℝ) ≤ 3 * (H : ℝ) := by
      rw [hcast2]
      have hH1 : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
      nlinarith
    have hb0 : (0 : ℝ) ≤ ((2 * H + 1 : ℕ) : ℝ) := by positivity
    calc
      ((2 * H + 1 : ℕ) ^ (n - 1) : ℝ) = ((2 * H + 1 : ℕ) : ℝ) ^ (n - 1) := by norm_num
      _ ≤ (3 * (H : ℝ)) ^ (n - 1) := pow_le_pow_left₀ hb0 hle (n - 1)
      _ = (3 ^ (n - 1) : ℝ) * (H : ℝ) ^ (n - 1) := by
        rw [mul_pow]
  have hsum := rootSum_real_le n H hn3 hH
  have hcast : (((HasIntRoot n H).ncard : ℕ) : ℝ) ≤
      ((2 * H + 1 : ℕ) ^ (n - 1) : ℝ) +
        2 * (∑ ρ ∈ Finset.Icc 1 H,
          (((2 * ((n * H) / ρ) + 1) ^ (n - 1) : ℕ) : ℝ)) := by
    exact_mod_cast hnc
  have h2s : 2 * (∑ ρ ∈ Finset.Icc 1 H,
        (((2 * ((n * H) / ρ) + 1) ^ (n - 1) : ℕ) : ℝ))
      ≤ 4 * (3 * (n : ℝ)) ^ (n - 1) * (H : ℝ) ^ (n - 1) := by
    have hA0 : (0 : ℝ) ≤ 2 := by norm_num
    have hm := mul_le_mul_of_nonneg_left hsum hA0
    calc
      2 * (∑ ρ ∈ Finset.Icc 1 H,
          (((2 * ((n * H) / ρ) + 1) ^ (n - 1) : ℕ) : ℝ))
          ≤ 2 * (2 * (3 * (n : ℝ)) ^ (n - 1) * (H : ℝ) ^ (n - 1)) := hm
      _ = 4 * (3 * (n : ℝ)) ^ (n - 1) * (H : ℝ) ^ (n - 1) := by ring
  have hK : ((3 ^ (n - 1) + 4 * (3 * n) ^ (n - 1) : ℕ) : ℝ) =
      (3 ^ (n - 1) : ℝ) + 4 * ((3 * n : ℕ) : ℝ) ^ (n - 1) := by
    norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
  have h3n : ((3 * n : ℕ) : ℝ) = 3 * (n : ℝ) := by norm_num [Nat.cast_mul]
  calc
    ((HasIntRoot n H).ncard : ℝ)
        ≤ ((2 * H + 1 : ℕ) ^ (n - 1) : ℝ) +
            2 * (∑ ρ ∈ Finset.Icc 1 H,
              (((2 * ((n * H) / ρ) + 1) ^ (n - 1) : ℕ) : ℝ)) := hcast
    _ ≤ ((2 * H + 1 : ℕ) ^ (n - 1) : ℝ) +
            4 * (3 * (n : ℝ)) ^ (n - 1) * (H : ℝ) ^ (n - 1) := by
          nlinarith
    _ ≤ (3 ^ (n - 1) : ℝ) * (H : ℝ) ^ (n - 1) +
            4 * (3 * (n : ℝ)) ^ (n - 1) * (H : ℝ) ^ (n - 1) := by
          nlinarith
    _ = ((3 ^ (n - 1) + 4 * (3 * n) ^ (n - 1) : ℕ) : ℝ) * (H : ℝ) ^ (n - 1) := by
          rw [hK, h3n]
          ring

/-- Theorem: box polynomials with a nonzero integer root are `O(H^(n-1))`,
for `n ≥ 3`. -/
theorem hasIntRoot_isBigO (n : ℕ) (hn : 3 ≤ n) :
    (fun H : ℕ => ((HasIntRoot n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  refine IsBigO.of_bound (((3 ^ (n - 1) + 4 * (3 * n) ^ (n - 1) : ℕ) : ℝ)) ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with H hH
  have hb := hasIntRoot_real_bound n H hn hH
  have hf0 : (0 : ℝ) ≤ ((HasIntRoot n H).ncard : ℝ) := by exact_mod_cast Nat.zero_le _
  have hg0 : (0 : ℝ) ≤ ((H : ℕ) ^ (n - 1) : ℝ) := by positivity
  rw [Real.norm_of_nonneg hf0, Real.norm_of_nonneg hg0]
  exact hb

/-- Polynomials in the box with a nonzero integer root are reducible, hence
counted among the "bad" polynomials `Bad n H` whose Galois group has order
`< n!` (for `n ≥ 2`). -/
theorem hasIntRoot_subset_Bad (n H : ℕ) (hn : 2 ≤ n) :
    HasIntRoot n H ⊆ Bad n H := by
  intro p hp
  rcases hp with ⟨hbox, r, hr, hdiv⟩
  rcases hdiv with ⟨c, hc⟩
  have hn1 : 1 ≤ n := by omega
  have hdeg : p.natDegree = n := Polynomial.natDegree_eq_of_degree_eq_some hbox.2.1
  have hm := monic_deg_of_X_sub_C_dvd r hn1 hbox.1 hdeg hc
  apply reducible_mem_Bad n H p hbox
  refine ⟨X - C r, c, Polynomial.monic_X_sub_C r, hm.1, ?_, ?_, ?_⟩
  · rw [Polynomial.natDegree_X_sub_C r]
  · have : 1 ≤ n - 1 := by omega
    rw [hm.2]
    exact this
  · exact hc.symm


end Counting

end Submission.Vdw
