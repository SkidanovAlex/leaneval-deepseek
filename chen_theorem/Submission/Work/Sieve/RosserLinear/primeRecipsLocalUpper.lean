import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.prof
import Submission.Work.NumberTheory.Chen.APSwitchUpper.ErrProfile
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_powLog

/-!
# Local (relative) upper bound for prime reciprocals over a window

`primeRecipsLocalUpper`: for every `N > 0` there are `C > 0` and `X₀` such that for all
`X₀ ≤ X ≤ Y`,

  `Σ_{X ≤ q ≤ Y-1, q prime} 1/(q-1) ≤ log(log Y / log X) + C (log Y / log X)^{-N} ...`

more precisely

  `Σ 1/(q-1) ≤ log(log Y/log X) + C·log(log Y/log X)/(log X)^N + C/(log X)^(N+1)`.

The estimate is *relative*: the error scales with the size of the main term's logarithm.
The input is the Prime Number Theorem with a power-of-log error in Mertens form,
`Commons.NumberTheory.Mertens.primeRecips_sub_loglog_powLog`, which gives
`|Σ_{p ≤ x} 1/p - log log x - L| ≤ C₀/(log x)^{-A}` for every `A > 0`.  Transporting this to
the window `[X, Y-1]` and splitting `1/(q-1) = 1/q + 1/(q(q-1))` (the correction costing only
`1/(X-1)`) gives the result with error of the same power `A`, uniformly in `Y ≥ X`.
-/

open Finset

namespace Work.Sieve.RosserLinear

/-- Telescoping identity: `Σ_{a ≤ n ≤ b} 1/(n(n-1)) = 1/(a-1) - 1/b` for `2 ≤ a`, `a - 1 ≤ b`. -/
private lemma sum_Icc_inv_mul_sub_one (a : ℕ) (ha : 2 ≤ a) : ∀ b : ℕ, a - 1 ≤ b →
    ∑ n ∈ Finset.Icc a b, (1:ℝ)/((n:ℝ) * ((n:ℝ)-1)) = 1/((a:ℝ)-1) - 1/(b:ℝ) := by
  intro b hb
  induction b, hb using Nat.le_induction with
  | base =>
      rw [Finset.Icc_eq_empty (by omega : ¬ a ≤ a - 1), Finset.sum_empty]
      have hcast : ((a - 1 : ℕ) : ℝ) = (a:ℝ) - 1 := by
        have h1 : 1 ≤ a := by omega
        push_cast [Nat.cast_sub h1]
        ring
      rw [hcast]; ring
  | succ b hb ih =>
      have hb1 : 1 ≤ b := by omega
      have hb0 : (b:ℝ) ≠ 0 := by
        have h : (0:ℝ) < (b:ℝ) := by exact_mod_cast (by omega : 0 < b)
        exact ne_of_gt h
      have hcast : (((b + 1 : ℕ)) : ℝ) = (b:ℝ) + 1 := by push_cast; ring
      rw [Finset.sum_Icc_succ_top (by omega : a ≤ b + 1), ih, hcast]
      have hkey : (1:ℝ)/(((b:ℝ)+1) * (b:ℝ)) = 1/(b:ℝ) - 1/((b:ℝ)+1) := by
        have h2 : (b:ℝ)+1 ≠ 0 := by positivity
        field_simp
        ring
      rw [show ((b:ℝ)+1-1) = (b:ℝ) by ring, hkey]
      ring

/-- The prime-reciprocal sum grows by at most `1/(n+1)` when the cut moves from `n` to `n+1`. -/
private lemma primeRecips_succ_sub_le (n : ℕ) :
    Commons.NumberTheory.Mertens.primeRecips ((n+1:ℕ):ℝ)
      - Commons.NumberTheory.Mertens.primeRecips (n:ℝ) ≤ 1/((n+1:ℕ):ℝ) := by
  have hsub : (n:ℕ).primesLE ⊆ (n+1:ℕ).primesLE := by
    intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨le_trans hp.1 (Nat.le_succ n), hp.2⟩
  have hsdiff := Finset.sum_sdiff (s₁ := (n:ℕ).primesLE) (s₂ := (n+1:ℕ).primesLE)
    (f := fun p : ℕ => (1:ℝ)/(p:ℝ)) hsub
  have hdiff : Commons.NumberTheory.Mertens.primeRecips ((n+1:ℕ):ℝ)
        - Commons.NumberTheory.Mertens.primeRecips (n:ℝ)
      = ∑ x ∈ ((n+1:ℕ).primesLE \ (n:ℕ).primesLE), (1:ℝ)/(x:ℝ) := by
    rw [Commons.NumberTheory.Mertens.primeRecips, Commons.NumberTheory.Mertens.primeRecips,
      Nat.floor_natCast, Nat.floor_natCast]
    linarith [hsdiff]
  rw [hdiff]
  have hsub2 : ((n+1:ℕ).primesLE \ (n:ℕ).primesLE) ⊆ ({(n+1)} : Finset ℕ) := by
    intro p hp
    rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE] at hp
    obtain ⟨⟨hp1, hpp⟩, hp2⟩ := hp
    rw [Finset.mem_singleton]
    have : ¬ (p ≤ n) := fun h => hp2 ⟨h, hpp⟩
    omega
  have hle : ∑ x ∈ ((n+1:ℕ).primesLE \ (n:ℕ).primesLE), (1:ℝ)/(x:ℝ)
      ≤ ∑ x ∈ ({(n+1)} : Finset ℕ), (1:ℝ)/(x:ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun x hx _ => by
      rw [Finset.mem_singleton] at hx
      subst hx
      positivity)
  simpa using hle

/-- `(log X)^A ≤ X - 1` for all sufficiently large `X`. -/
private lemma eventually_log_rpow_le (A : ℝ) (hA : 0 < A) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → (Real.log (X:ℝ)) ^ A ≤ (X:ℝ) - 1 := by
  have h1 : ∀ᶠ x : ℝ in Filter.atTop, (Real.log x)^A ≤ x/4 := by
    have h := isLittleO_log_rpow_rpow_atTop A (by norm_num : (0:ℝ) < 3/4)
    filter_upwards [h.bound (by norm_num : (0:ℝ) < 1/4),
      Filter.eventually_ge_atTop (1:ℝ)] with x hx hx1
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hx0 : 0 ≤ x := by linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlogx A),
        abs_of_nonneg (Real.rpow_nonneg hx0 _)] at hx
    have h34 : x ^ (3/4:ℝ) ≤ x := by
      calc x ^ (3/4:ℝ) ≤ x ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
        _ = x := Real.rpow_one x
    calc (Real.log x)^A ≤ (1/4) * x^(3/4:ℝ) := hx
      _ ≤ (1/4) * x := by linarith [h34]
      _ = x/4 := by ring
  have h2 : ∀ᶠ X : ℕ in Filter.atTop, (Real.log (X:ℝ))^A ≤ (X:ℝ)/4 :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually h1
  have h3 : ∀ᶠ X : ℕ in Filter.atTop, (Real.log (X:ℝ))^A ≤ (X:ℝ) - 1 := by
    filter_upwards [h2, Filter.eventually_ge_atTop (2:ℕ)] with X hX hX2
    have hcast : (2:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX2
    linarith
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp h3
  exact ⟨X₀, hX₀⟩

/-- **The local relative upper bound** with an arbitrary power of log in the error. -/
private lemma localUpper (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ X Y : ℕ, X₀ ≤ X → X ≤ Y →
      (∑ q ∈ (Finset.Icc X (Y - 1)).filter Nat.Prime, (1 : ℝ) / ((q : ℝ) - 1))
        ≤ Real.log (Real.log (Y : ℝ) / Real.log (X : ℝ))
          + C / (Real.log (X : ℝ)) ^ A := by
  obtain ⟨L, C0, hC0pos, hC0⟩ := Commons.NumberTheory.Mertens.primeRecips_sub_loglog_powLog A hA
  obtain ⟨Xl, hXl⟩ := eventually_log_rpow_le A hA
  refine ⟨2 * C0 + 2, by linarith, max Xl 12, ?_⟩
  intro X Y hX hXY
  have hX12 : 12 ≤ X := le_trans (le_max_right _ _) hX
  have hY12 : 12 ≤ Y := le_trans hX12 hXY
  have hX0 : 1 < X := by omega
  have hY0 : 1 < Y := by omega
  have hXR : (1:ℝ) < (X:ℝ) := by exact_mod_cast hX0
  have hYR : (1:ℝ) < (Y:ℝ) := by exact_mod_cast hY0
  have hXYr : (X:ℝ) ≤ (Y:ℝ) := by exact_mod_cast hXY
  have hlogX : 0 < Real.log (X:ℝ) := Real.log_pos hXR
  have hlogY : 0 < Real.log (Y:ℝ) := Real.log_pos hYR
  have hlogXY : Real.log (X:ℝ) ≤ Real.log (Y:ℝ) := Real.log_le_log (by positivity) hXYr
  have hY11 : (11:ℝ) ≤ (Y:ℝ) := by
    have : (11:ℕ) ≤ Y := by omega
    exact_mod_cast this
  have hX11 : (11:ℝ) ≤ (X:ℝ) := by
    have : (11:ℕ) ≤ X := by omega
    exact_mod_cast this
  -- Mertens at `Y` and at `X`
  have hMY : Commons.NumberTheory.Mertens.primeRecips (Y:ℝ)
      ≤ Real.log (Real.log (Y:ℝ)) + L + C0/(Real.log (Y:ℝ))^A := by
    have h := hC0 (Y:ℝ) hY11
    have h' := (abs_le.mp h).2
    unfold Commons.NumberTheory.Mertens.primeRecips
    linarith
  have hMX : Real.log (Real.log (X:ℝ)) + L - C0/(Real.log (X:ℝ))^A
      ≤ Commons.NumberTheory.Mertens.primeRecips (X:ℝ) := by
    have h := hC0 (X:ℝ) hX11
    have h' := (abs_le.mp h).1
    unfold Commons.NumberTheory.Mertens.primeRecips
    linarith
  set S : Finset ℕ := (Finset.Icc X (Y - 1)).filter Nat.Prime with hSdef
  -- `Σ_S 1/q`
  have hSq : ∑ q ∈ S, (1:ℝ)/(q:ℝ)
      ≤ Commons.NumberTheory.Mertens.primeRecips (Y:ℝ)
        - Commons.NumberTheory.Mertens.primeRecips (X:ℝ) + 1/(X:ℝ) := by
    have hsubI : S ⊆ (Finset.Icc X Y).filter Nat.Prime := by
      intro q hq
      rw [hSdef] at hq
      rw [Finset.mem_filter, Finset.mem_Icc] at hq ⊢
      obtain ⟨⟨h1, h2⟩, h3⟩ := hq
      exact ⟨⟨h1, by omega⟩, h3⟩
    have hle1 : ∑ q ∈ S, (1:ℝ)/(q:ℝ)
        ≤ ∑ q ∈ (Finset.Icc X Y).filter Nat.Prime, (1:ℝ)/(q:ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubI (fun x hx _ => by
        rw [Finset.mem_filter, Finset.mem_Icc] at hx
        have hx0 : (0:ℝ) < (x:ℝ) := by exact_mod_cast (by omega : 0 < x)
        positivity)
    have hset : (Finset.Icc X Y).filter Nat.Prime = (Y:ℕ).primesLE \ (X-1:ℕ).primesLE := by
      ext p
      rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE]
      constructor
      · rintro ⟨⟨h1, h2⟩, hp⟩
        exact ⟨⟨h2, hp⟩, fun h => by omega⟩
      · rintro ⟨⟨h2, hp⟩, hnot⟩
        have : ¬ (p ≤ X - 1) := fun h => hnot ⟨h, hp⟩
        exact ⟨⟨by omega, h2⟩, hp⟩
    have heq : ∑ q ∈ (Finset.Icc X Y).filter Nat.Prime, (1:ℝ)/(q:ℝ)
        = Commons.NumberTheory.Mertens.primeRecips (Y:ℝ)
          - Commons.NumberTheory.Mertens.primeRecips ((X-1:ℕ):ℝ) := by
      have hsub' : (X-1:ℕ).primesLE ⊆ (Y:ℕ).primesLE := by
        intro p hp
        rw [Nat.mem_primesLE] at hp ⊢
        exact ⟨by omega, hp.2⟩
      have hsdiff := Finset.sum_sdiff (s₁ := (X-1:ℕ).primesLE) (s₂ := (Y:ℕ).primesLE)
        (f := fun p : ℕ => (1:ℝ)/(p:ℝ)) hsub'
      rw [hset, Commons.NumberTheory.Mertens.primeRecips,
        Commons.NumberTheory.Mertens.primeRecips, Nat.floor_natCast, Nat.floor_natCast]
      linarith [hsdiff]
    have hinc : Commons.NumberTheory.Mertens.primeRecips (X:ℝ)
        - Commons.NumberTheory.Mertens.primeRecips ((X-1:ℕ):ℝ) ≤ 1/(X:ℝ) := by
      have h := primeRecips_succ_sub_le (X-1)
      rwa [show X - 1 + 1 = X from Nat.sub_add_cancel (by omega : 1 ≤ X)] at h
    linarith
  -- `Σ_S 1/(q(q-1))`
  have hSq2 : ∑ q ∈ S, (1:ℝ)/((q:ℝ)*((q:ℝ)-1)) ≤ 1/((X:ℝ)-1) := by
    have hsub : S ⊆ Finset.Icc X (Y-1) := by
      rw [hSdef]; exact Finset.filter_subset _ _
    have hnn : ∀ n ∈ Finset.Icc X (Y-1), n ∉ S → (0:ℝ) ≤ 1/((n:ℝ)*((n:ℝ)-1)) := by
      intro n hn _
      rw [Finset.mem_Icc] at hn
      have hn2 : (2:ℝ) ≤ (n:ℝ) := by
        have : 2 ≤ n := by omega
        exact_mod_cast this
      exact div_nonneg zero_le_one (mul_nonneg (by linarith) (by linarith))
    have hle1 := Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
    have htel := sum_Icc_inv_mul_sub_one X (by omega) (Y-1) (by omega)
    have hpos : (0:ℝ) ≤ 1/(((Y-1:ℕ)):ℝ) := by positivity
    linarith
  -- term splitting
  have hsplit : ∑ q ∈ S, (1:ℝ)/((q:ℝ)-1)
      = ∑ q ∈ S, (1:ℝ)/(q:ℝ) + ∑ q ∈ S, (1:ℝ)/((q:ℝ)*((q:ℝ)-1)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun q hq => ?_)
    rw [hSdef, Finset.mem_filter, Finset.mem_Icc] at hq
    obtain ⟨⟨h1, h2⟩, hqprime⟩ := hq
    have hq2 : 2 ≤ q := hqprime.two_le
    have hq2r : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq2
    have ha : ((q:ℝ)-1) ≠ 0 := by linarith
    have hb : (q:ℝ) ≠ 0 := by linarith
    field_simp
    ring
  -- error absorption
  have herr : C0/(Real.log (Y:ℝ))^A + C0/(Real.log (X:ℝ))^A
      + 1/(X:ℝ) + 1/((X:ℝ)-1) ≤ (2*C0+2)/(Real.log (X:ℝ))^A := by
    have hpowY : 0 < (Real.log (Y:ℝ))^A := Real.rpow_pos_of_pos hlogY A
    have hpowX : 0 < (Real.log (X:ℝ))^A := Real.rpow_pos_of_pos hlogX A
    have hpowXY : (Real.log (X:ℝ))^A ≤ (Real.log (Y:ℝ))^A :=
      Real.rpow_le_rpow hlogX.le hlogXY hA.le
    have h1 : C0/(Real.log (Y:ℝ))^A ≤ C0/(Real.log (X:ℝ))^A := by
      have h1' : ((Real.log (Y:ℝ))^A)⁻¹ ≤ ((Real.log (X:ℝ))^A)⁻¹ := by
        simpa [one_div] using one_div_le_one_div_of_le hpowX hpowXY
      have h2 := mul_le_mul_of_nonneg_left h1' hC0pos.le
      simpa [div_eq_mul_inv] using h2
    have hXl' : (Real.log (X:ℝ))^A ≤ (X:ℝ) - 1 := hXl X (le_trans (le_max_left _ _) hX)
    have hXpos : (0:ℝ) < (X:ℝ) := by linarith
    have h2 : 1/(X:ℝ) ≤ 1/(Real.log (X:ℝ))^A :=
      one_div_le_one_div_of_le hpowX (le_trans hXl' (by linarith))
    have h3 : 1/((X:ℝ)-1) ≤ 1/(Real.log (X:ℝ))^A :=
      one_div_le_one_div_of_le hpowX hXl'
    have h4 : (2*C0+2)/(Real.log (X:ℝ))^A
        = 2*(C0/(Real.log (X:ℝ))^A) + 2*(1/(Real.log (X:ℝ))^A) := by ring_nf
    rw [h4]; linarith [h1, h2, h3]
  have hlogratio : Real.log (Real.log (Y:ℝ)) - Real.log (Real.log (X:ℝ))
      = Real.log (Real.log (Y:ℝ)/Real.log (X:ℝ)) :=
    (Real.log_div (ne_of_gt hlogY) (ne_of_gt hlogX)).symm
  calc ∑ q ∈ S, (1:ℝ)/((q:ℝ)-1)
      = ∑ q ∈ S, (1:ℝ)/(q:ℝ) + ∑ q ∈ S, (1:ℝ)/((q:ℝ)*((q:ℝ)-1)) := hsplit
    _ ≤ (Commons.NumberTheory.Mertens.primeRecips (Y:ℝ)
          - Commons.NumberTheory.Mertens.primeRecips (X:ℝ) + 1/(X:ℝ)) + 1/((X:ℝ)-1) := by
        linarith [hSq, hSq2]
    _ ≤ Real.log (Real.log (Y:ℝ)) - Real.log (Real.log (X:ℝ))
          + (C0/(Real.log (Y:ℝ))^A + C0/(Real.log (X:ℝ))^A + 1/(X:ℝ) + 1/((X:ℝ)-1)) := by
        linarith [hMY, hMX]
    _ ≤ Real.log (Real.log (Y:ℝ)/Real.log (X:ℝ)) + (2*C0+2)/(Real.log (X:ℝ))^A := by
        rw [hlogratio]; linarith [herr]

theorem primeRecipsLocalUpper (N : ℝ) (hN : 0 < N) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ X Y : ℕ, X₀ ≤ X → X ≤ Y →
      (∑ q ∈ (Finset.Icc X (Y - 1)).filter Nat.Prime, (1 : ℝ) / ((q : ℝ) - 1))
        ≤ Real.log (Real.log (Y : ℝ) / Real.log (X : ℝ))
          + C * Real.log (Real.log (Y : ℝ) / Real.log (X : ℝ)) / (Real.log (X : ℝ)) ^ N
          + C / (Real.log (X : ℝ)) ^ (N + 1) := by
  obtain ⟨C, hCpos, X₀, hX₀⟩ := localUpper (N + 1) (by linarith)
  refine ⟨C, hCpos, max X₀ 12, ?_⟩
  intro X Y hX hXY
  have hX12 : 12 ≤ X := le_trans (le_max_right _ _) hX
  have hX₀' : X₀ ≤ X := le_trans (le_max_left _ _) hX
  have h := hX₀ X Y hX₀' hXY
  have hX1 : (1:ℝ) < (X:ℝ) := by exact_mod_cast (by omega : 1 < X)
  have hlogX : 0 < Real.log (X:ℝ) := Real.log_pos hX1
  have hXYr : (X:ℝ) ≤ (Y:ℝ) := by exact_mod_cast hXY
  have hlogXY : Real.log (X:ℝ) ≤ Real.log (Y:ℝ) := Real.log_le_log (by positivity) hXYr
  have hratio : (1:ℝ) ≤ Real.log (Y:ℝ)/Real.log (X:ℝ) := by
    rw [le_div_iff₀ hlogX]; linarith
  have hlogratio : 0 ≤ Real.log (Real.log (Y:ℝ)/Real.log (X:ℝ)) := Real.log_nonneg hratio
  have hpowpos : 0 < (Real.log (X:ℝ))^N := Real.rpow_pos_of_pos hlogX N
  have hmid : 0 ≤ C * Real.log (Real.log (Y:ℝ)/Real.log (X:ℝ)) / (Real.log (X:ℝ))^N :=
    div_nonneg (mul_nonneg hCpos.le hlogratio) hpowpos.le
  linarith

end Work.Sieve.RosserLinear
