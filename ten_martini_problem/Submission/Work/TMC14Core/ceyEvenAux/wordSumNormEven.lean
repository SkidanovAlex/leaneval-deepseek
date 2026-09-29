import Mathlib
import Submission.Work.TMC14Core.InvSumF
import Submission.Work.TMC14Core.WeylCount

/-!
# `Work.TMC14Core.ceyEvenAux.wordSumNormEven`

For `q = 2m+2` and `ω = om p q = e^{2πi p/q}` a primitive `q`-th root of unity
(`gcd(p, q) = 1`), the word-inversion sum

`wordSum ω (2m) m = ∑_{f : #U(f) = m} ω ^ invCount (2m) f`

satisfies `‖wordSum ω (2m) m‖ ≥ 1`.

The proof computes the sum in closed form.  The Gauss identity `Hh_eq`
(`Dprod ω m · wordSum ω (2m) m = Qprod ω m m`) together with the reflection
`k ↦ 2m+2-k` of the factors `1 - ω^{m+1+k}` of `Qprod ω m m` and the telescoping
identity for the range products gives

`wordSum ω (2m) m · (1 - ω) = (-1)^m · ω^{e} · (1 - ω^{m+1})`   (`e = ∑_{k<m} (m+1+k)`);

taking norms and using `ω^{m+1} = -1` (so `‖1 - ω^{m+1}‖ = 2`) and `‖1 - ω‖ ≤ 2`
yields `‖wordSum ω (2m) m‖ = 2/‖1 - ω‖ ≥ 1`.
-/

noncomputable section

namespace Work.TMC14Core.ceyEvenAux

open Finset

/-! ## Elementary facts about `ω = om p q` -/

/-- `‖om p q‖ = 1`. -/
theorem om_norm (p : ℤ) (q : ℕ) : ‖om p q‖ = 1 := by
  rw [om_eq_wPh]
  exact wPh_norm _

/-- For `q = 2m+2` and `gcd(p, q) = 1` the primitive `q`-th root of unity `om p q`
satisfies `(om p q)^{m+1} = -1` (it is a square root of `ω^q = 1`, and it is not `1`
because `q ∤ m+1`). -/
theorem omPowSuccNegOne (p : ℤ) (q m : ℕ) (hm : q = 2*m+2) (hpq : Nat.Coprime p.natAbs q) :
    (om p q) ^ (m+1) = -1 := by
  have hq : 0 < q := by omega
  have hsq : ((om p q) ^ (m+1)) ^ 2 = 1 := by
    rw [← pow_mul, show (m+1) * 2 = q from by omega]
    exact om_pow_q' p q
  rcases (sq_eq_one_iff.mp hsq) with h | h
  · exfalso
    have hd : q ∣ (m+1) := (om_pow_eq_one_iff p q hpq hq (m+1)).mp h
    have hle : q ≤ m+1 := Nat.le_of_dvd (by omega) hd
    omega
  · exact h

/-! ## Reindexing `Dprod` and `Qprod` as products over `Finset.range` -/

/-- `Dprod ω m = ∏_{k<m} (1 - ω^{k+1})`. -/
theorem Dprod_range (ω : ℂ) (m : ℕ) :
    Dprod ω m = ∏ k ∈ Finset.range m, (1 - ω^(k+1)) := by
  induction m with
  | zero => simp [Dprod]
  | succ m ih =>
    rw [Dprod_succ, ih, Finset.prod_range_succ]
    ring

/-- `Qprod ω m m = ∏_{k<m} (1 - ω^{m+1+k})`. -/
theorem Qprod_range (ω : ℂ) (m : ℕ) :
    Qprod ω m m = ∏ k ∈ Finset.range m, (1 - ω^(m+1+k)) := by
  rw [Qprod, ← Finset.Ico_add_one_right_eq_Icc (1:ℕ) m,
    Finset.prod_Ico_eq_prod_range (fun k => (1 - ω^(m+k))) 1 (m+1)]
  simp only [Nat.add_sub_cancel, Nat.add_assoc]

/-! ## The reflection of `Qprod ω m m` for `ω^(2m+2) = 1` -/

/-- **Reflection of `Qprod`.**  For `ω^(2m+2) = 1` the diagonal product `Qprod ω m m`
can be reflected about the index `m+1`: using `ω^{m+1+k}·ω^{m+1-k} = ω^{2m+2} = 1` one has
`1 - ω^{m+1+k} = -ω^{m+1+k}(1 - ω^{m+1-k})`, and the index reversal `k ↦ m-1-k`
turns `∏_{k<m}(1 - ω^{m+1-k})` into `∏_{k<m}(1 - ω^{k+2})`. -/
theorem QprodReflectEven (ω : ℂ) (m : ℕ) (hω : ω^(2*m+2) = 1) :
    Qprod ω m m = (-1)^m * ω^(∑ k ∈ Finset.range m, (m+1+k)) *
      ∏ k ∈ Finset.range m, (1 - ω^(k+2)) := by
  have hterm : ∀ k ∈ Finset.range m,
      (1 - ω^(m+1+k)) = -ω^(m+1+k) * (1 - ω^(m+1-k)) := by
    intro k hk
    have hk' : k < m := Finset.mem_range.mp hk
    have hmul : ω^(m+1+k) * ω^(m+1-k) = 1 := by
      rw [← pow_add]
      have hsum : m+1+k + (m+1-k) = 2*m+2 := by omega
      rw [hsum, hω]
    have h' : ω^(m+1+k) * (1 - ω^(m+1-k)) = ω^(m+1+k) - 1 := by
      rw [mul_sub, mul_one, hmul]
    have h'' : -ω^(m+1+k) * (1 - ω^(m+1-k)) = 1 - ω^(m+1+k) := by
      have e : -ω^(m+1+k) * (1 - ω^(m+1-k))
          = -(ω^(m+1+k) * (1 - ω^(m+1-k))) := by ring
      rw [e, h']; ring
    exact h''.symm
  have hstep : ∏ k ∈ Finset.range m, (1 - ω^(m+1+k))
      = ∏ k ∈ Finset.range m, (-ω^(m+1+k) * (1 - ω^(m+1-k))) :=
    Finset.prod_congr rfl hterm
  have hrefl : ∏ k ∈ Finset.range m, (1 - ω^(m+1-k))
      = ∏ k ∈ Finset.range m, (1 - ω^(k+2)) := by
    rw [← Finset.prod_range_reflect (fun j => (1 - ω^(j+2))) m]
    refine Finset.prod_congr rfl (fun j hj => ?_)
    have hjj : j < m := Finset.mem_range.mp hj
    have he : (m - 1 - j) + 2 = m + 1 - j := by omega
    rw [he]
  rw [Qprod_range, hstep, Finset.prod_mul_distrib, Finset.prod_neg, Finset.card_range,
    Finset.prod_pow_eq_pow_sum, hrefl]

/-! ## Telescoping the two range products -/

/-- `(1-ω)·∏_{k<m}(1-ω^{k+2}) = (1-ω^{m+1})·∏_{k<m}(1-ω^{k+1})`: both sides are
`∏_{k=1}^{m+1}(1-ω^k)` with the first or the last factor singled out. -/
theorem telescope (ω : ℂ) (m : ℕ) :
    (1 - ω) * (∏ k ∈ Finset.range m, (1 - ω^(k+2))) =
      (1 - ω^(m+1)) * (∏ k ∈ Finset.range m, (1 - ω^(k+1))) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ (fun k => (1 - ω^(k+2))) m,
        Finset.prod_range_succ (fun k => (1 - ω^(k+1))) m, ← mul_assoc, ih]
    ring

/-! ## The closed form of `wordSum ω (2m) m`, multiplied by `1 - ω` -/

/-- For `ω^(2m+2) = 1` and `ω^j ≠ 1` for `1 ≤ j ≤ m`,
`wordSum ω (2m) m · (1 - ω) = (-1)^m · ω^{∑_{k<m}(m+1+k)} · (1 - ω^{m+1})`. -/
theorem wordSum_mul_one_sub (ω : ℂ) (m : ℕ) (hω : ω^(2*m+2) = 1)
    (hne : ∀ j : ℕ, 1 ≤ j → j ≤ m → ω^j ≠ 1) :
    wordSum ω (2*m) m * (1 - ω) =
      (-1)^m * ω^(∑ k ∈ Finset.range m, (m+1+k)) * (1 - ω^(m+1)) := by
  have hH := Hh_eq ω m m
  rw [show m + m = 2*m from by omega] at hH
  rw [Dprod_range, QprodReflectEven ω m hω] at hH
  have htel := telescope ω m
  have hP : (∏ k ∈ Finset.range m, (1 - ω^(k+1))) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro k hk
    have hk' : k < m := Finset.mem_range.mp hk
    exact sub_ne_zero.mpr (Ne.symm (hne (k+1) (by omega) (by omega)))
  refine mul_left_cancel₀ hP ?_
  rw [← mul_assoc, hH]
  have hre : ((-1)^m * ω^(∑ k ∈ Finset.range m, (m+1+k)) *
        (∏ k ∈ Finset.range m, (1 - ω^(k+2)))) * (1 - ω)
      = (-1)^m * ω^(∑ k ∈ Finset.range m, (m+1+k)) *
        ((1 - ω) * (∏ k ∈ Finset.range m, (1 - ω^(k+2)))) := by ring
  rw [hre, htel]
  ring

/-! ## The target -/

theorem wordSumNormEven (p : ℤ) (q m : ℕ) (hm : q = 2*m+2) (hpq : Nat.Coprime p.natAbs q) :
    1 ≤ ‖wordSum (om p q) (2*m) m‖ := by
  have hq : 0 < q := by omega
  have hω : (om p q)^(2*m+2) = 1 := by
    rw [← hm]; exact om_pow_q' p q
  have hne : ∀ j : ℕ, 1 ≤ j → j ≤ m → (om p q)^j ≠ 1 := by
    intro j hj1 hjm h
    have hd : q ∣ j := (om_pow_eq_one_iff p q hpq hq j).mp h
    have hle : q ≤ j := Nat.le_of_dvd (by omega) hd
    omega
  have hmain := wordSum_mul_one_sub (om p q) m hω hne
  have hneg := omPowSuccNegOne p q m hm hpq
  -- norms of both sides of the closed form
  have hnorm : ‖wordSum (om p q) (2*m) m‖ * ‖1 - om p q‖ = 2 := by
    have h := congrArg (fun z : ℂ => ‖z‖) hmain
    rw [hneg] at h
    rw [show (1 : ℂ) - -1 = 2 by norm_num] at h
    have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, mul_one,
      om_norm, h2n] at h
    simpa using h
  -- `‖1 - ω‖ ≤ 2`
  have hle : ‖1 - om p q‖ ≤ 2 := by
    have h := norm_sub_le (1 : ℂ) (om p q)
    rw [norm_one, om_norm] at h
    linarith
  have hpos : 0 < ‖1 - om p q‖ := by
    rw [norm_pos_iff]
    intro hcon
    have hb : ‖1 - om p q‖ = 0 := by rw [hcon]; exact norm_zero
    have hzero : ‖wordSum (om p q) (2*m) m‖ * ‖1 - om p q‖ = 0 := by rw [hb, mul_zero]
    rw [hnorm] at hzero
    norm_num at hzero
  have key : (1 : ℝ) * ‖1 - om p q‖
      ≤ ‖wordSum (om p q) (2*m) m‖ * ‖1 - om p q‖ := by
    rw [one_mul, hnorm]
    exact hle
  exact le_of_mul_le_mul_right key hpos

end Work.TMC14Core.ceyEvenAux
