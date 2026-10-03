/-
# `Work.FIChain.rhoTrunc_recip` — the reciprocity of the truncated Möbius sum `ρ(c; ·)`

For `c` squarefree, `c ≠ 1`, `u > 0` and `u` **not** a divisor of `c`,

  `ρ(c; c/u) = Σ_{d | c, d ≤ c/u} μ(d) = −μ(c)·ρ(c; u)`,   `ρ(c; t) = Σ_{d | c, d ≤ t} μ(d)`.

This is the `ρ`-reciprocity used to move a `c`-range into its reciprocal range (the change of
variables `t = c/u` in `∫ ρ(c;t) dt/t`).  The proof is the divisor bijection `d ↦ c/d`, which
sends `{d | c : d ≤ c/u}` onto `{e | c : u ≤ e}`; on squarefree `c` one has `μ(c/d) = μ(c)μ(d)`,
and the hypothesis that `u` is not a divisor excludes the boundary tie `e = u` so that
`{e | c : u ≤ e}` is the complement of `{e | c : e ≤ u}` inside the divisor set, whose `μ`-sum is
`[c = 1] = 0`.
-/
import Mathlib
import Submission.Work.FIChain.S3plusC_route_defs

set_option autoImplicit false

namespace Work.FIChain

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Auxiliary lemmas -/

/-- **Möbius multiplicativity along a divisor.**  For `m ∣ c` with `c` squarefree,
`μ(c)·μ(m) = μ(c/m)` (as real numbers). -/
lemma moebius_mul_div_cast_real (c m : ℕ) (hc : Squarefree c) (hm : m ∣ c) :
    (ArithmeticFunction.moebius c : ℝ) * (ArithmeticFunction.moebius m : ℝ)
      = (ArithmeticFunction.moebius (c / m) : ℝ) := by
  have hZ : (ArithmeticFunction.moebius c : ℤ) * (ArithmeticFunction.moebius m : ℤ)
      = (ArithmeticFunction.moebius (c / m) : ℤ) := by
    have hc' : Squarefree (m * (c / m)) := by rw [Nat.mul_div_cancel' hm]; exact hc
    have hcop : m.Coprime (c / m) := Nat.coprime_of_squarefree_mul hc'
    have hmul : ArithmeticFunction.moebius (m * (c / m))
        = ArithmeticFunction.moebius m * ArithmeticFunction.moebius (c / m) :=
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
    rw [Nat.mul_div_cancel' hm] at hmul
    have hmsq : Squarefree m := hc.squarefree_of_dvd hm
    have hsq : ArithmeticFunction.moebius m * ArithmeticFunction.moebius m = 1 := by
      simpa [pow_two] using ArithmeticFunction.moebius_sq_eq_one_of_squarefree hmsq
    rw [hmul, mul_assoc,
      mul_comm (ArithmeticFunction.moebius (c / m)) (ArithmeticFunction.moebius m),
      ← mul_assoc, hsq, one_mul]
  exact_mod_cast hZ

/-- **The divisor bijection `d ↦ c/d`.**  For `c ≠ 0` and `u > 0`, the map `d ↦ c/d` is a
bijection from the divisors `d ∣ c` with `d ≤ c/u` onto the divisors `e ∣ c` with `u ≤ e`. -/
lemma rhoTrunc_reindex' (c : ℕ) (hc0 : c ≠ 0) (u : ℝ) (hu : 0 < u) (F : ℕ → ℝ) :
    (∑ d ∈ c.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ (c : ℝ) / u), F d)
      = ∑ e ∈ c.divisors.filter (fun e => u ≤ ((e : ℕ) : ℝ)), F (c / e) := by
  refine Finset.sum_bij (fun d _ => c / d) ?_ ?_ ?_ ?_
  · intro d hd
    obtain ⟨hdmem, hdle⟩ := Finset.mem_filter.mp hd
    obtain ⟨hddvd, -⟩ := Nat.mem_divisors.mp hdmem
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hdmem
    refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hddvd, hc0⟩, ?_⟩
    rw [Nat.cast_div hddvd (Nat.cast_ne_zero.mpr hdpos.ne')]
    rw [le_div_iff₀ (by exact_mod_cast hdpos : (0:ℝ) < (d:ℝ))]
    have h1 : (d : ℝ) * u ≤ (c : ℝ) := (le_div_iff₀ hu).mp hdle
    linarith
  · intro a₁ ha₁ a₂ ha₂ heq
    have h₁ : a₁ ∣ c := (Nat.mem_divisors.mp (Finset.mem_filter.mp ha₁).1).1
    have h₂ : a₂ ∣ c := (Nat.mem_divisors.mp (Finset.mem_filter.mp ha₂).1).1
    rw [← Nat.div_div_self h₁ hc0, heq, Nat.div_div_self h₂ hc0]
  · intro b hb
    obtain ⟨hbmem, hbble⟩ := Finset.mem_filter.mp hb
    obtain ⟨hbdvd, -⟩ := Nat.mem_divisors.mp hbmem
    refine ⟨c / b, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hbdvd, hc0⟩, ?_⟩
      rw [le_div_iff₀ hu]
      have hmul : (b : ℝ) * ((c / b : ℕ) : ℝ) = (c : ℝ) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' hbdvd]
      have hbR : (0:ℝ) ≤ ((c / b : ℕ) : ℝ) := by positivity
      have h2 := mul_le_mul_of_nonneg_left hbble hbR
      linarith [hmul, h2]
    · exact Nat.div_div_self hbdvd hc0
  · intro a ha
    have hadvd : a ∣ c := (Nat.mem_divisors.mp (Finset.mem_filter.mp ha).1).1
    show F a = F (c / (c / a))
    rw [Nat.div_div_self hadvd hc0]

/-- **The upper half of the divisor set.**  For squarefree `c ≠ 1` and `u` not a divisor of `c`,
`Σ_{e | c, u ≤ e} μ(e) = −ρ(c; u)`: the divisors split into `{u ≤ e}` and `{e ≤ u}`, and the
full `μ`-sum is `[c = 1] = 0`. -/
lemma rhoTrunc_filter_ge (c : ℕ) (hc : Squarefree c) (hc1 : c ≠ 1) (u : ℝ)
    (hnd : ∀ d ∈ c.divisors, (d : ℝ) ≠ u) :
    (∑ e ∈ c.divisors.filter (fun e => u ≤ ((e : ℕ) : ℝ)), (ArithmeticFunction.moebius e : ℝ))
      = - Submission.ASP.rhoTrunc c u := by
  have hdisj : Disjoint (c.divisors.filter (fun e => u ≤ ((e : ℕ) : ℝ)))
      (c.divisors.filter (fun e => ((e : ℕ) : ℝ) ≤ u)) := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    have h1 : u ≤ ((e : ℕ) : ℝ) := (Finset.mem_filter.mp he1).2
    have h2 : ((e : ℕ) : ℝ) ≤ u := (Finset.mem_filter.mp he2).2
    have hemem : e ∈ c.divisors := (Finset.mem_filter.mp he1).1
    exact hnd e hemem (le_antisymm h2 h1)
  have hunion : (c.divisors.filter (fun e => u ≤ ((e : ℕ) : ℝ))) ∪
      (c.divisors.filter (fun e => ((e : ℕ) : ℝ) ≤ u)) = c.divisors := by
    apply Finset.Subset.antisymm
    · intro e he
      rcases Finset.mem_union.mp he with h | h <;> exact (Finset.mem_filter.mp h).1
    · intro e he
      rcases le_total u ((e : ℕ) : ℝ) with h | h
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨he, h⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨he, h⟩))
  have hsum := Finset.sum_union hdisj (f := fun e => (ArithmeticFunction.moebius e : ℝ))
  rw [hunion] at hsum
  have h0 : (∑ x ∈ c.divisors, (ArithmeticFunction.moebius x : ℝ)) = 0 := by
    rw [Submission.ASP.sum_moebius_divisors_eq, if_neg hc1]
  have hB' : (∑ e ∈ c.divisors.filter (fun e => ((e : ℕ) : ℝ) ≤ u),
        (ArithmeticFunction.moebius e : ℝ)) = Submission.ASP.rhoTrunc c u := rfl
  linarith [hsum, h0, hB']

/-! ## The reciprocity -/

lemma rhoTrunc_recip (c : ℕ) (hc : Squarefree c) (hc1 : c ≠ 1) (u : ℝ) (hu : 0 < u)
    (hnd : ∀ d ∈ c.divisors, (d : ℝ) ≠ u) :
    Submission.ASP.rhoTrunc c (c / u)
      = -(ArithmeticFunction.moebius c : ℝ) * Submission.ASP.rhoTrunc c u := by
  have hc0 : c ≠ 0 := hc.ne_zero
  -- Step 1: unfold and reindex `d ↦ c/d`.
  have hstep1 : Submission.ASP.rhoTrunc c (c / u)
      = ∑ e ∈ c.divisors.filter (fun e => u ≤ ((e : ℕ) : ℝ)),
          (ArithmeticFunction.moebius (c / e) : ℝ) := by
    rw [Submission.ASP.rhoTrunc]
    exact rhoTrunc_reindex' c hc0 u hu (fun d => (ArithmeticFunction.moebius d : ℝ))
  -- Step 2: `μ(c/e) = μ(c)·μ(e)` on the squarefree support.
  have hstep2 : (∑ e ∈ c.divisors.filter (fun e => u ≤ ((e : ℕ) : ℝ)),
          (ArithmeticFunction.moebius (c / e) : ℝ))
      = (ArithmeticFunction.moebius c : ℝ) *
          ∑ e ∈ c.divisors.filter (fun e => u ≤ ((e : ℕ) : ℝ)),
            (ArithmeticFunction.moebius e : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e he => ?_)
    have hemem : e ∈ c.divisors := (Finset.mem_filter.mp he).1
    have hedvd : e ∣ c := (Nat.mem_divisors.mp hemem).1
    exact (moebius_mul_div_cast_real c e hc hedvd).symm
  -- Step 3: the upper half is the negative of `ρ(c; u)`.
  rw [hstep1, hstep2, rhoTrunc_filter_ge c hc hc1 u hnd]
  ring

end

end Work.FIChain
