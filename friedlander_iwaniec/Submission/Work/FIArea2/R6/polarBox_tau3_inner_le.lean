/-
# `Work.FIArea2.R6.polarBox_tau3_inner_le`

The *inner* `τ₃²`-sum of the §10 pair sum: for a primitive `z₁` with `|z₁|² > N` lying in the
polar box (5.14),

  `∑_{z₂ ∈ polarBox} τ₃(|Δ(z₁,z₂)|)² ≤ C·(θ·N + 1)·(log N + 2)^16`.

Three ingredients, all of them elementary:

* **(6.2)** `Work.FIArea2.absDelta_lt_four_pi`: for `z₁, z₂` in the polar box,
  `|Δ(z₁,z₂)| < 4πθN`.  With `θ ≤ 1/10` and `π < 4` this gives
  `|Δ| ≤ X := ⌈4πθN⌉₊ ≤ 3N`, so all the values of `|Δ|` lie in a window of length `≍ θN`.
* **Injectivity of the fibre** (`Work.FIArea3.delta_fibre_injective`): `z₂ ↦ Δ(z₁,z₂)` is
  injective on the polar box, because two box points are at distance `< √N` while differences
  with equal `Δ` are integer multiples of `z₁`, i.e. either `0` or of modulus `≥ |z₁| > √N`.
  Hence the fibre of `z₂ ↦ |Δ(z₁,z₂)|` over any `n` has at most two elements.
* **The summatory bound** `∑_{n ≤ X} τ₃(n)² ≤ C·(X+1)·(log X + 2)^16`, immediate from
  `τ₃(n) ≤ τ(n)²` and the elementary `∑_{n ≤ X} τ(n)⁴ ≤ C·X·(log X + 2)^16`
  (`Work.FIArea2.sum_tau_pow_le`).

A general fibre-counting lemma (`sum_le_two_mul_sum_Icc_of_fiber_card_le_two`) turns the second
and third ingredients into the bound `2·C·(X+1)·(log X+2)^16`, and the elementary inequalities
`X + 1 ≤ (4π+2)·(θN + 1)` and `log X + 2 ≤ 2(log N + 2)` (from `X ≤ 3N`) give the stated form.
-/
import Mathlib
import Submission.Work.FIArea2.R6.SixDefs
import Submission.Work.FIArea3.BoxDefs
import Submission.Work.FIArea3.delta_fibre_injective
import Submission.Work.FIArea2.absDelta_lt_four_pi
import Submission.Work.FIArea2.sum_tau_pow_le
import Submission.Work.FIArea2.R6.tau3_le_sum_Icc_four

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **Fibre counting on `Icc 0 X`.**  If a nonnegative weight `g ∘ F` is summed over a finite set
`S` whose `F`-fibres have at most two elements, and every value of `F` on `S` is `≤ X`, then the
sum is at most twice the full sum of `g` over `0 ≤ n ≤ X`. -/
theorem sum_le_two_mul_sum_Icc_of_fiber_card_le_two
    {α : Type*} (S : Finset α) (F : α → ℕ) (g : ℕ → ℝ) (X : ℕ)
    (hX : ∀ a ∈ S, F a ≤ X)
    (hfib : ∀ n : ℕ, (S.filter (fun a => F a = n)).card ≤ 2)
    (hg : ∀ n : ℕ, 0 ≤ g n) :
    (∑ a ∈ S, g (F a)) ≤ 2 * ∑ n ∈ Finset.Icc 0 X, g n := by
  have key : (∑ n ∈ Finset.Icc 0 X, ∑ a ∈ S.filter (fun a => F a = n), g (F a))
      = ∑ a ∈ S, g (F a) :=
    Finset.sum_fiberwise_of_maps_to (s := S) (t := Finset.Icc 0 X) (g := F)
      (f := fun a => g (F a)) (fun a ha => Finset.mem_Icc.mpr ⟨Nat.zero_le _, hX a ha⟩)
  rw [← key]
  calc ∑ n ∈ Finset.Icc 0 X, ∑ a ∈ S.filter (fun a => F a = n), g (F a)
      = ∑ n ∈ Finset.Icc 0 X, ∑ a ∈ S.filter (fun a => F a = n), g n := by
        refine Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun a ha => ?_))
        rw [(Finset.mem_filter.mp ha).2]
    _ = ∑ n ∈ Finset.Icc 0 X, ((S.filter (fun a => F a = n)).card : ℝ) * g n := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ Finset.Icc 0 X, 2 * g n := by
        refine Finset.sum_le_sum (fun n _ => ?_)
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hfib n) (hg n)
    _ = 2 * ∑ n ∈ Finset.Icc 0 X, g n := by rw [Finset.mul_sum]

/-- **The fibre of `z ↦ |Δ(z₁,z)|` over the polar box has at most two elements.**  Indeed
`|Δ| = n` means `Δ = n` or `Δ = -n`, and each of these two level sets is a singleton by
`Work.FIArea3.delta_fibre_injective`. -/
theorem polarBox_absDelta_fibre_card_le_two {Pa : Work.FITop.Params} {φ : ℝ} {z1 : GaussianInt}
    (hz1n : (Pa.N : ℝ) < (Work.FIPlan.gnorm z1 : ℝ)) (hz1p : Work.FIPlan.IsPrimitive z1)
    (n : ℕ) :
    ((Work.FIArea3.polarBoxFinset Pa φ).filter
      (fun z => Work.FIPlan.absDelta z1 z = n)).card ≤ 2 := by
  classical
  have hinj : ∀ z ∈ Work.FIArea3.polarBoxFinset Pa φ,
      ∀ z' ∈ Work.FIArea3.polarBoxFinset Pa φ,
      Work.FIPlan.Delta z1 z = Work.FIPlan.Delta z1 z' → z = z' := by
    intro z hz z' hz' h
    exact Work.FIArea3.delta_fibre_injective hz1n hz1p
      (Work.FIArea3.mem_polarBoxFinset.mp hz).2
      (Work.FIArea3.mem_polarBoxFinset.mp hz').2 h
  have hA : ((Work.FIArea3.polarBoxFinset Pa φ).filter
      (fun z => Work.FIPlan.Delta z1 z = (n : ℤ))).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    exact hinj a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
      (by rw [(Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2])
  have hB : ((Work.FIArea3.polarBoxFinset Pa φ).filter
      (fun z => Work.FIPlan.Delta z1 z = -((n : ℤ)))).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    exact hinj a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
      (by rw [(Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2])
  have hsub : (Work.FIArea3.polarBoxFinset Pa φ).filter
        (fun z => Work.FIPlan.absDelta z1 z = n)
      ⊆ ((Work.FIArea3.polarBoxFinset Pa φ).filter
            (fun z => Work.FIPlan.Delta z1 z = (n : ℤ)))
        ∪ ((Work.FIArea3.polarBoxFinset Pa φ).filter
            (fun z => Work.FIPlan.Delta z1 z = -((n : ℤ)))) := by
    intro z hz
    have hz1 : z ∈ Work.FIArea3.polarBoxFinset Pa φ := (Finset.mem_filter.mp hz).1
    have hz2 : (Work.FIPlan.Delta z1 z).natAbs = n := by
      have h := (Finset.mem_filter.mp hz).2
      rwa [Work.FIPlan.absDelta] at h
    rcases Int.natAbs_eq_iff.mp hz2 with h | h
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hz1, h⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hz1, h⟩))
  have hupper : ((Work.FIArea3.polarBoxFinset Pa φ).filter
        (fun z => Work.FIPlan.absDelta z1 z = n)).card
      ≤ ((Work.FIArea3.polarBoxFinset Pa φ).filter
            (fun z => Work.FIPlan.Delta z1 z = (n : ℤ))).card
        + ((Work.FIArea3.polarBoxFinset Pa φ).filter
            (fun z => Work.FIPlan.Delta z1 z = -((n : ℤ)))).card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  omega

/-- **Summatory bound for `τ₃²`.**  `∑_{n ≤ X} τ₃(n)² ≤ C·(X+1)·(log X + 2)^16`.

This is `τ₃(n)² ≤ τ(n)⁴` for `n ≥ 1` (via `τ₃ ≤ τ²`) together with the classical
elementary bound `∑_{n ≤ X} τ(n)⁴ ≤ C·X·(log X + 2)^16` of `Work.FIArea2.sum_tau_pow_le`; the
single term `n = 0` contributes `τ₃(0)² = 1`. -/
theorem sum_tau3_sq_Icc_le :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ,
      (∑ n ∈ Finset.Icc 0 X, ((tau3 n : ℕ) : ℝ) ^ (2 : ℕ))
        ≤ C * ((X : ℝ) + 1) * (Real.log (X : ℝ) + 2) ^ (16 : ℕ) := by
  obtain ⟨C4, hC4pos, hC4⟩ := Work.FIArea2.sum_tau_pow_le 4
  refine ⟨1 + C4, by linarith, fun X => ?_⟩
  have hX0 : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
  have hlogX0 : (0 : ℝ) ≤ Real.log (X : ℝ) := Real.log_natCast_nonneg X
  have hB1 : (1 : ℝ) ≤ (Real.log (X : ℝ) + 2) ^ (16 : ℕ) := by
    have h2 : (1 : ℝ) ≤ Real.log (X : ℝ) + 2 := by linarith
    calc (1 : ℝ) = 1 ^ (16 : ℕ) := by norm_num
      _ ≤ (Real.log (X : ℝ) + 2) ^ (16 : ℕ) := pow_le_pow_left₀ (by norm_num) h2 16
  have htau0 : ((tau3 0 : ℕ) : ℝ) = 1 := by
    have h : tau3 0 = 1 := by rw [tau3, if_pos rfl]
    rw [h]
    norm_num
  -- the part `n ≥ 1`
  have hstep : (∑ n ∈ Finset.Icc 1 X, ((tau3 n : ℕ) : ℝ) ^ (2 : ℕ))
      ≤ C4 * (X : ℝ) * (Real.log (X : ℝ) + 2) ^ (16 : ℕ) := by
    have h1 : (∑ n ∈ Finset.Icc 1 X, ((tau3 n : ℕ) : ℝ) ^ (2 : ℕ))
        ≤ ∑ n ∈ Finset.Icc 1 X, (((n.divisors.card : ℕ) : ℝ)) ^ (4 : ℕ) := by
      refine Finset.sum_le_sum (fun n hn => ?_)
      have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
      have hsq := tau3_le_sq hn0
      have hcast : ((tau3 n : ℕ) : ℝ) ≤ (((n.divisors.card : ℕ) : ℝ)) ^ (2 : ℕ) := by
        calc ((tau3 n : ℕ) : ℝ) ≤ (((n.divisors.card ^ (2 : ℕ) : ℕ)) : ℝ) := by
              exact_mod_cast hsq
          _ = (((n.divisors.card : ℕ) : ℝ)) ^ (2 : ℕ) := by rw [Nat.cast_pow]
      calc ((tau3 n : ℕ) : ℝ) ^ (2 : ℕ)
          ≤ ((((n.divisors.card : ℕ) : ℝ)) ^ (2 : ℕ)) ^ (2 : ℕ) :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hcast 2
        _ = (((n.divisors.card : ℕ) : ℝ)) ^ (4 : ℕ) := by ring
    exact le_trans h1 (hC4 X)
  -- split off `n = 0`
  have hsub0 : Finset.Icc 0 X ⊆ insert 0 (Finset.Icc 1 X) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [Finset.mem_insert, Finset.mem_Icc]
    rcases Nat.eq_zero_or_pos n with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hn.2⟩
  have h1 : (∑ n ∈ Finset.Icc 0 X, ((tau3 n : ℕ) : ℝ) ^ (2 : ℕ))
      ≤ ∑ n ∈ insert 0 (Finset.Icc 1 X), ((tau3 n : ℕ) : ℝ) ^ (2 : ℕ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub0
      (fun n _ _ => pow_nonneg (Nat.cast_nonneg _) 2)
  have h2 : (∑ n ∈ insert 0 (Finset.Icc 1 X), ((tau3 n : ℕ) : ℝ) ^ (2 : ℕ))
      = 1 + ∑ n ∈ Finset.Icc 1 X, ((tau3 n : ℕ) : ℝ) ^ (2 : ℕ) := by
    rw [Finset.sum_insert (by simp : (0 : ℕ) ∉ Finset.Icc 1 X)]
    rw [htau0]
    norm_num
  -- `1 + C4·X·B ≤ (1 + C4)·(X+1)·B`
  have hmul : 1 + C4 * (X : ℝ) * (Real.log (X : ℝ) + 2) ^ (16 : ℕ)
      ≤ (1 + C4) * ((X : ℝ) + 1) * (Real.log (X : ℝ) + 2) ^ (16 : ℕ) := by
    have hBnn : (0 : ℝ) ≤ (Real.log (X : ℝ) + 2) ^ (16 : ℕ) :=
      pow_nonneg (by linarith) 16
    have hge1 : (1 : ℝ) ≤ 1 + C4 + (X : ℝ) := by linarith
    have hmul1 : (1 : ℝ) ≤ (Real.log (X : ℝ) + 2) ^ (16 : ℕ) * (1 + C4 + (X : ℝ)) := by
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ (Real.log (X : ℝ) + 2) ^ (16 : ℕ) * (1 + C4 + (X : ℝ)) :=
            mul_le_mul hB1 hge1 (by norm_num) hBnn
    have hkey : (1 + C4) * ((X : ℝ) + 1) * (Real.log (X : ℝ) + 2) ^ (16 : ℕ)
        = C4 * (X : ℝ) * (Real.log (X : ℝ) + 2) ^ (16 : ℕ)
          + (Real.log (X : ℝ) + 2) ^ (16 : ℕ) * (1 + C4 + (X : ℝ)) := by ring
    rw [hkey]
    linarith [hmul1]
  calc (∑ n ∈ Finset.Icc 0 X, ((tau3 n : ℕ) : ℝ) ^ (2 : ℕ))
      ≤ ∑ n ∈ insert 0 (Finset.Icc 1 X), ((tau3 n : ℕ) : ℝ) ^ (2 : ℕ) := h1
    _ = 1 + ∑ n ∈ Finset.Icc 1 X, ((tau3 n : ℕ) : ℝ) ^ (2 : ℕ) := h2
    _ ≤ 1 + C4 * (X : ℝ) * (Real.log (X : ℝ) + 2) ^ (16 : ℕ) := by linarith [hstep]
    _ ≤ (1 + C4) * ((X : ℝ) + 1) * (Real.log (X : ℝ) + 2) ^ (16 : ℕ) := hmul

theorem polarBox_tau3_inner_le :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Pa : Work.FITop.Params) (φ : ℝ) (z1 : GaussianInt),
      (Pa.N : ℝ) < (Work.FIPlan.gnorm z1 : ℝ) →
      Work.FIPlan.IsPrimitive z1 →
      Work.FITop3.InPolarBox Pa φ z1 →
      (∑ z2 ∈ Work.FIArea3.polarBoxFinset Pa φ,
          ((Work.FIArea2.R6.tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ) ^ (2 : ℕ))
        ≤ C * (Pa.θ * Pa.N + 1) * (Real.log Pa.N + 2) ^ (16 : ℕ) := by
  obtain ⟨C1, hC1pos, hC1⟩ := sum_tau3_sq_Icc_le
  refine ⟨2 * C1 * (4 * Real.pi + 2) * 65536, ?_, ?_⟩
  · have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
    nlinarith [hC1pos, hπ]
  intro Pa φ z1 hgn hprim hbox
  set Xn : ℕ := ⌈4 * Real.pi * Pa.θ * Pa.N⌉₊ with hXn
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hN0 : (0 : ℝ) < Pa.N := by linarith
  have hθ0 : (0 : ℝ) < Pa.θ := Pa.hθ0
  have hθt : Pa.θ ≤ 1 / 10 := Work.FIArea3.theta_le_tenth Pa
  have hpi4 : Real.pi < 4 := Real.pi_lt_four
  have hπpos : (0 : ℝ) < Real.pi := Real.pi_pos
  -- 1. every value of `|Δ|` on the box is `≤ Xn`
  have hrange : ∀ z ∈ Work.FIArea3.polarBoxFinset Pa φ, Work.FIPlan.absDelta z1 z ≤ Xn := by
    intro z hz
    have hzbox : Work.FITop3.InPolarBox Pa φ z := (Work.FIArea3.mem_polarBoxFinset.mp hz).2
    have hlt := Work.FIArea2.absDelta_lt_four_pi hbox hzbox
    have hceil : 4 * Real.pi * Pa.θ * Pa.N ≤ (Xn : ℝ) := by
      rw [hXn]
      exact Nat.le_ceil _
    have hleR : ((Work.FIPlan.absDelta z1 z : ℕ) : ℝ) ≤ (Xn : ℝ) :=
      le_trans (le_of_lt hlt) hceil
    exact_mod_cast hleR
  -- 2. the fibres have at most two elements
  have hfib : ∀ n : ℕ,
      ((Work.FIArea3.polarBoxFinset Pa φ).filter
        (fun z => Work.FIPlan.absDelta z1 z = n)).card ≤ 2 :=
    fun n => polarBox_absDelta_fibre_card_le_two hgn hprim n
  have hmain := sum_le_two_mul_sum_Icc_of_fiber_card_le_two
    (S := Work.FIArea3.polarBoxFinset Pa φ)
    (F := fun z => Work.FIPlan.absDelta z1 z)
    (g := fun n => ((tau3 n : ℕ) : ℝ) ^ (2 : ℕ))
    (X := Xn) hrange hfib (fun n => pow_nonneg (Nat.cast_nonneg _) 2)
  -- 3. the size of the window: `Xn ≤ 4πθN + 1`, `Xn ≤ 3N`
  have hXnle : (Xn : ℝ) ≤ 4 * Real.pi * Pa.θ * Pa.N + 1 := by
    have hnn : (0 : ℝ) ≤ 4 * Real.pi * Pa.θ * Pa.N :=
      le_of_lt (mul_pos (mul_pos (mul_pos (by norm_num) hπpos) hθ0) hN0)
    have hceil := Nat.ceil_lt_add_one (R := ℝ) hnn
    rw [hXn]
    exact le_of_lt hceil
  have h4πθ : 4 * Real.pi * Pa.θ ≤ 2 := by
    have hπθ : Real.pi * Pa.θ ≤ 4 * (1 / 10) := by
      calc Real.pi * Pa.θ ≤ 4 * Pa.θ := mul_le_mul_of_nonneg_right hpi4.le hθ0.le
        _ ≤ 4 * (1 / 10) := mul_le_mul_of_nonneg_left hθt (by norm_num)
    linarith [hπθ]
  have h4πθN : 4 * Real.pi * Pa.θ * Pa.N ≤ 2 * Pa.N :=
    mul_le_mul_of_nonneg_right h4πθ hN0.le
  have hXn3N : (Xn : ℝ) ≤ 3 * Pa.N := by linarith [hXnle, h4πθN, hN1]
  have hθN1 : (0 : ℝ) < Pa.θ * Pa.N + 1 := by
    have h : (0 : ℝ) < Pa.θ * Pa.N := mul_pos hθ0 hN0
    linarith
  have hA : (Xn : ℝ) + 1 ≤ (4 * Real.pi + 2) * (Pa.θ * Pa.N + 1) := by
    have hθNnn : (0 : ℝ) ≤ Pa.θ * Pa.N := le_of_lt (mul_pos hθ0 hN0)
    have hkey : (4 * Real.pi + 2) * (Pa.θ * Pa.N + 1)
        = 4 * Real.pi * Pa.θ * Pa.N + 4 * Real.pi + 2 * (Pa.θ * Pa.N) + 2 := by ring
    rw [hkey]
    linarith [hXnle, hπpos, hθNnn]
  -- 4. the logarithmic factor
  have hlog3 : Real.log (3 : ℝ) ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    linarith
  have hlogXn : Real.log (Xn : ℝ) ≤ Real.log (3 : ℝ) + Real.log Pa.N := by
    rcases Nat.eq_zero_or_pos Xn with h | h
    · rw [h, Nat.cast_zero, Real.log_zero]
      have h1 : (0 : ℝ) ≤ Real.log (3 : ℝ) := Real.log_nonneg (by norm_num)
      have h2 : (0 : ℝ) ≤ Real.log Pa.N := Real.log_nonneg hN1
      linarith
    · have hpos : (0 : ℝ) < (Xn : ℝ) := by exact_mod_cast h
      calc Real.log (Xn : ℝ) ≤ Real.log (3 * Pa.N) := Real.log_le_log hpos hXn3N
        _ = Real.log (3 : ℝ) + Real.log Pa.N :=
            Real.log_mul (by norm_num) (by linarith)
  have hlogB : Real.log (Xn : ℝ) + 2 ≤ 2 * (Real.log Pa.N + 2) := by
    have h2 : (0 : ℝ) ≤ Real.log Pa.N := Real.log_nonneg hN1
    linarith [hlogXn, hlog3, h2]
  have hL0 : (0 : ℝ) ≤ Real.log (Xn : ℝ) + 2 := by
    have := Real.log_natCast_nonneg Xn
    linarith
  have hbase : (Real.log (Xn : ℝ) + 2) ^ (16 : ℕ)
      ≤ (2 * (Real.log Pa.N + 2)) ^ (16 : ℕ) :=
    pow_le_pow_left₀ hL0 hlogB 16
  have hC1Xn := hC1 Xn
  have h4π2 : (0 : ℝ) < 4 * Real.pi + 2 := by linarith
  have hprod : C1 * ((Xn : ℝ) + 1) * (Real.log (Xn : ℝ) + 2) ^ (16 : ℕ)
      ≤ C1 * ((4 * Real.pi + 2) * (Pa.θ * Pa.N + 1)) * (2 * (Real.log Pa.N + 2)) ^ (16 : ℕ) := by
    refine mul_le_mul (mul_le_mul_of_nonneg_left hA hC1pos.le) hbase ?_ ?_
    · exact pow_nonneg hL0 16
    · exact mul_nonneg hC1pos.le (mul_nonneg h4π2.le hθN1.le)
  calc (∑ z2 ∈ Work.FIArea3.polarBoxFinset Pa φ,
        ((Work.FIArea2.R6.tau3 (Work.FIPlan.absDelta z1 z2) : ℕ) : ℝ) ^ (2 : ℕ))
      ≤ 2 * (∑ n ∈ Finset.Icc 0 Xn, ((tau3 n : ℕ) : ℝ) ^ (2 : ℕ)) := hmain
    _ ≤ 2 * (C1 * ((Xn : ℝ) + 1) * (Real.log (Xn : ℝ) + 2) ^ (16 : ℕ)) :=
        mul_le_mul_of_nonneg_left hC1Xn (by norm_num)
    _ ≤ 2 * (C1 * ((4 * Real.pi + 2) * (Pa.θ * Pa.N + 1))
          * (2 * (Real.log Pa.N + 2)) ^ (16 : ℕ)) :=
        mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ = (2 * C1 * (4 * Real.pi + 2) * 65536) * (Pa.θ * Pa.N + 1)
          * (Real.log Pa.N + 2) ^ (16 : ℕ) := by ring

end

end Work.FIArea2.R6
