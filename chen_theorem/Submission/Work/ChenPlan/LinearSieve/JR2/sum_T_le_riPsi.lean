import Mathlib
import Submission.Work.ChenPlan.LinearSieve.JR2.Defs
import Submission.Work.ChenPlan.LinearSieve.RIMain.LayerAux
import Submission.Work.ChenPlan.LinearSieve.Assembly.sum_layers_le

namespace Work.ChenPlan.LinearSieve.JR2

open Finset
open scoped BigOperators

noncomputable section

open Work.NumberTheory.Chen.APSwitchUpper

/-!
# The summed layer bound over the even layers

Given the per-layer sharp bound `LayerSharpBound C ρ`, the sum of the Rosser–Iwaniec layer sums
`T_n` over the *even* layers `1 ≤ n` (i.e. the layers contributing to the `λ⁻` sieve, whose
profile sum is `riPsi`) is bounded by `VfR A Z·(riPsi s + ε·C·10100·errH s)`.

The two ingredients are

* `Σ_{n even, 0<n<N} profC (n-1) s ≤ riPsi s` — `Assembly.sum_layers_le` at `ε = 0`;
* `Σ_{n even, 0<n<N} (n+1) ρ^{n-1} ≤ 10100` for `0 ≤ ρ ≤ 99/100` — the geometric bookkeeping,
  `Σ_{m ≥ 0} (m+2)ρ^m = (1-ρ)^{-2} + (1-ρ)^{-1} ≤ 10100` (`tsum_add_two_mul_pow`).
-/

/-- `Σ_{m ≥ 0} ((m+2) ρ^m) = (1-ρ)^{-2} + (1-ρ)^{-1}` for `0 ≤ ρ < 1`. -/
theorem tsum_add_two_mul_pow {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∑' m : ℕ, ((m : ℝ) + 2) * ρ ^ m = (1 - ρ)⁻¹ ^ 2 + (1 - ρ)⁻¹ := by
  have hnorm : ‖ρ‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hρ0]; exact hρ1
  have h2 : Summable (fun m : ℕ => ρ ^ m) := summable_geometric_of_lt_one hρ0 hρ1
  have hval2 : ∑' m : ℕ, ρ ^ m = (1 - ρ)⁻¹ := tsum_geometric_of_lt_one hρ0 hρ1
  have hval1 : ∑' m : ℕ, ((m : ℝ) + 1) * ρ ^ m = (1 - ρ)⁻¹ ^ 2 :=
    Work.ChenPlan.LinearSieve.RI.tsum_succ_mul_pow ρ hnorm
  have hP : Summable (fun m : ℕ => ((m : ℝ) + 1) * ρ ^ m) := by
    have h : Summable (fun m : ℕ => (m : ℝ) * ρ ^ m + ρ ^ m) :=
      ((hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable).add h2
    exact h.congr (fun m => by ring)
  have hadd := hP.tsum_add h2
  rw [hval1, hval2] at hadd
  have h4 : ∑' m : ℕ, ((m : ℝ) + 2) * ρ ^ m
      = ∑' m : ℕ, (((m : ℝ) + 1) * ρ ^ m + ρ ^ m) := tsum_congr (fun m => by ring)
  rw [h4, ← hadd]

/-- `Σ_{n even, 0 < n < N} (n+1) ρ^{n-1} ≤ 10100` for `0 ≤ ρ ≤ 99/100`. -/
theorem sum_even_succ_mul_pow_le_10100 (N : ℕ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 99/100) :
    ∑ n ∈ (Finset.range N).filter (fun n : ℕ => Even n ∧ n ≠ 0),
        ((n : ℝ) + 1) * ρ ^ (n - 1) ≤ 10100 := by
  have hρlt : ρ < 1 := by linarith
  have hnorm : ‖ρ‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hρ0]; exact hρlt
  have hsumm0 : Summable (fun m : ℕ => ρ ^ m) := summable_geometric_of_lt_one hρ0 hρlt
  have hsumm1 : Summable (fun m : ℕ => ((m : ℝ) + 1) * ρ ^ m) := by
    have h : Summable (fun m : ℕ => (m : ℝ) * ρ ^ m + ρ ^ m) :=
      ((hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable).add hsumm0
    exact h.congr (fun m => by ring)
  have hsumm : Summable (fun m : ℕ => ((m : ℝ) + 2) * ρ ^ m) := by
    have h : Summable (fun m : ℕ => ((m : ℝ) + 1) * ρ ^ m + ρ ^ m) := hsumm1.add hsumm0
    exact h.congr (fun m => by ring)
  have hsub : (Finset.range N).filter (fun n : ℕ => Even n ∧ n ≠ 0)
      ⊆ (Finset.range N).filter (fun n : ℕ => 1 ≤ n) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
    obtain ⟨h1, hev, hne⟩ := hn
    obtain ⟨k, hk⟩ := hev
    exact ⟨h1, by omega⟩
  have hstep1 : ∑ n ∈ (Finset.range N).filter (fun n : ℕ => Even n ∧ n ≠ 0),
        ((n : ℝ) + 1) * ρ ^ (n - 1)
      ≤ ∑ n ∈ (Finset.range N).filter (fun n : ℕ => 1 ≤ n),
        ((n : ℝ) + 1) * ρ ^ (n - 1) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun n _ _ => mul_nonneg (by positivity) (pow_nonneg hρ0 _))
  have hstep2 : ∑ n ∈ (Finset.range N).filter (fun n : ℕ => 1 ≤ n),
        ((n : ℝ) + 1) * ρ ^ (n - 1)
      ≤ ∑' m : ℕ, ((m : ℝ) + 2) * ρ ^ m := by
    have hinj : Set.InjOn (fun n : ℕ => n - 1) ((Finset.range N).filter (fun n : ℕ => 1 ≤ n)) := by
      intro x hx y hy h
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx hy
      change x - 1 = y - 1 at h
      omega
    have hkey : ∑ n ∈ (Finset.range N).filter (fun n : ℕ => 1 ≤ n),
          ((n : ℝ) + 1) * ρ ^ (n - 1)
        = ∑ m ∈ ((Finset.range N).filter (fun n : ℕ => 1 ≤ n)).image (fun n : ℕ => n - 1),
            ((m : ℝ) + 2) * ρ ^ m := by
      rw [Finset.sum_image (s := (Finset.range N).filter (fun n : ℕ => 1 ≤ n))
        (g := fun n : ℕ => n - 1) (f := fun m : ℕ => ((m : ℝ) + 2) * ρ ^ m) hinj]
      refine Finset.sum_congr rfl (fun n hn => ?_)
      simp only [Finset.mem_filter, Finset.mem_range] at hn
      have hc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := Nat.cast_pred hn.2
      show ((n : ℝ) + 1) * ρ ^ (n - 1) = ((↑(n - 1) : ℝ) + 2) * ρ ^ (n - 1)
      rw [hc]; ring
    rw [hkey]
    exact hsumm.sum_le_tsum
      (((Finset.range N).filter (fun n : ℕ => 1 ≤ n)).image (fun n : ℕ => n - 1))
      (fun m _ => mul_nonneg (by positivity) (pow_nonneg hρ0 m))
  have hnum : (1 - ρ)⁻¹ ^ 2 + (1 - ρ)⁻¹ ≤ 10100 := by
    have hpos : 0 < 1 - ρ := by linarith
    have h100 : (1 - ρ)⁻¹ ≤ 100 := by
      rw [inv_le_iff_one_le_mul₀' hpos]
      nlinarith
    have hnn : 0 ≤ (1 - ρ)⁻¹ := inv_nonneg.mpr (le_of_lt hpos)
    nlinarith [h100, hnn]
  have hval := tsum_add_two_mul_pow hρ0 hρlt
  linarith [hstep1, hstep2, hval, hnum]

theorem sum_T_le_riPsi {C ρ : ℝ} (hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 99/100)
    (hLayer : Work.ChenPlan.LinearSieve.JR2.LayerSharpBound C ρ) (A : BoundingSieve)
    {ε Z D : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1/100) (hZ : 2 ≤ Z) (hD : 1 ≤ D)
    (hSharp : Work.ChenPlan.LinearSieve.JR2.SharpNorm A Z ε)
    (hs : 2 ≤ Real.log D / Real.log Z) :
    ∑ n ∈ (Finset.range (Nat.log 2 ⌈D⌉₊ + 3)).filter (fun n : ℕ => Even n ∧ n ≠ 0),
        Work.ChenPlan.LinearSieve.T A n D Z
      ≤ Work.ChenPlan.LinearSieve.VfR A Z *
          (Work.NumberTheory.Chen.APSwitchUpper.riPsi (Real.log D / Real.log Z)
            + ε * (C * 10100)
              * Work.NumberTheory.Chen.APSwitchUpper.errH (Real.log D / Real.log Z)) := by
  set s : ℝ := Real.log D / Real.log Z with hsdef
  set F : Finset ℕ :=
    (Finset.range (Nat.log 2 ⌈D⌉₊ + 3)).filter (fun n : ℕ => Even n ∧ n ≠ 0) with hFdef
  have hs2 : 2 ≤ s := by rw [hsdef]; exact hs
  have hVpos : 0 < VfR A Z := VfR_pos A Z
  have hterm : ∀ n ∈ F, T A n D Z ≤ VfR A Z *
      (profC (n - 1) s + ε * C * ((n : ℝ) + 1) * ρ ^ (n - 1) * errH s) := by
    intro n hn
    rw [hFdef, Finset.mem_filter] at hn
    obtain ⟨-, hev, hne⟩ := hn
    have hn1 : 1 ≤ n := by obtain ⟨k, hk⟩ := hev; omega
    have hb := hLayer (A := A) (ε := ε) (D := D) (z := Z) hε0 hε1 hZ hD hSharp n hn1
      (fun _ => le_trans (by norm_num : (1 : ℝ) ≤ 2) hs) (fun _ => hs)
    rw [hsdef]
    exact hb
  have hsum1 : ∑ n ∈ F, T A n D Z ≤ ∑ n ∈ F, VfR A Z *
      (profC (n - 1) s + ε * C * ((n : ℝ) + 1) * ρ ^ (n - 1) * errH s) :=
    Finset.sum_le_sum hterm
  have hinner : ∑ n ∈ F,
        (profC (n - 1) s + ε * C * ((n : ℝ) + 1) * ρ ^ (n - 1) * errH s)
      ≤ riPsi s + ε * (C * 10100) * errH s := by
    rw [Finset.sum_add_distrib]
    have hA : ∑ n ∈ F, profC (n - 1) s ≤ riPsi s := by
      have h := (Work.ChenPlan.LinearSieve.Assembly.sum_layers_le (Nat.log 2 ⌈D⌉₊ + 3)
        (s := s) (ε := 0) (by linarith) le_rfl).2
      rw [hFdef]
      simpa using h
    have hB : ∑ n ∈ F, ε * C * ((n : ℝ) + 1) * ρ ^ (n - 1) * errH s
        ≤ ε * (C * 10100) * errH s := by
      have hfac : ∑ n ∈ F, ε * C * ((n : ℝ) + 1) * ρ ^ (n - 1) * errH s
          = (ε * C * errH s) * ∑ n ∈ F, ((n : ℝ) + 1) * ρ ^ (n - 1) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun n _ => by ring)
      rw [hfac]
      have hgeom : ∑ n ∈ F, ((n : ℝ) + 1) * ρ ^ (n - 1) ≤ 10100 := by
        rw [hFdef]
        exact sum_even_succ_mul_pow_le_10100 (Nat.log 2 ⌈D⌉₊ + 3) hρ hρ1
      have hcoef : 0 ≤ ε * C * errH s :=
        mul_nonneg (mul_nonneg hε0 hC) (errH_nonneg s)
      calc (ε * C * errH s) * ∑ n ∈ F, ((n : ℝ) + 1) * ρ ^ (n - 1)
          ≤ (ε * C * errH s) * 10100 := mul_le_mul_of_nonneg_left hgeom hcoef
        _ = ε * (C * 10100) * errH s := by ring
    linarith
  calc ∑ n ∈ F, T A n D Z
      ≤ ∑ n ∈ F, VfR A Z *
          (profC (n - 1) s + ε * C * ((n : ℝ) + 1) * ρ ^ (n - 1) * errH s) := hsum1
    _ = VfR A Z * ∑ n ∈ F,
          (profC (n - 1) s + ε * C * ((n : ℝ) + 1) * ρ ^ (n - 1) * errH s) := by
        rw [Finset.mul_sum]
    _ ≤ VfR A Z * (riPsi s + ε * (C * 10100) * errH s) :=
        mul_le_mul_of_nonneg_left hinner (le_of_lt hVpos)

end

end Work.ChenPlan.LinearSieve.JR2
