/-
# `Submission.Work.FIArea6.Ucut_eq_Vd_sum` — the exact bookkeeping (16.1)/(16.2)

*FI* §16 starts from the `U`-cut of (10.15),

  `U(β) = 2 Σ_{z₁,z₂} (z₁,z₂)=1  β_{z₁}β̄_{z₂} Σ_{d ∈ Sset(z₁,z₂)} (φ(d)/d)[d ≤ X] (z₂/z₁|d) log(8|z₁z₂|/Δ)`

(the round-6 `Work.FITop4.Ucut`), and rewrites it as the sum over the moduli `d ≤ X` of the
*per-modulus* piece `U_d(β)` of (16.2),

  `U(β) = 2 Σ_{d ≤ X} (φ(d)/d) U_d(β)`,
  `U_d(β) = Σ_{(z₁,z₂)=1, 4d ∣ |Δ(z₁,z₂)|} β_{z₁}β̄_{z₂}(z₂/z₁|d) log(8|z₁z₂|/Δ)`

(the round-6 `Work.FIArea6.Vd`).  This file proves that identity (`Ucut_eq_Vd_sum`).

**The bookkeeping is exact** (there is no error term here, unlike (16.5)–(16.10)):

* `Sset(z₁,z₂) = {d : 1 ≤ d ≤ |Δ|/4+1, 4d ∣ |Δ|}` (`Work.FITop4.Sset`), so for `d ≤ X` the
  membership `d ∈ Sset(z₁,z₂)` is equivalent to `1 ≤ d ≤ X ∧ 4d ∣ |Δ|` **as long as `Δ ≠ 0`**:
  from `4d ∣ |Δ|` and `|Δ| ≠ 0` we get `4d ≤ |Δ|`, hence `d ≤ |Δ|/4 ≤ |Δ|/4+1`, so the automatic
  filter `Icc 1 (|Δ|/4+1)` of `Sset` never removes anything (`sum_Sset_cut_eq`).
* For `Δ = 0` the two sides still agree because `logFac6 z z = log 0 = 0`: `Sset` degenerates to
  `{1}` (and `{1} ∩ [1,X]` is empty for `X = 0`), while the right-hand side sums over every
  `d ∈ [1,X]` — both sums vanish since `logFac6` is a factor of every term.

The formal proof is the `d`-sum/pair-sum exchange: rewrite the `ℝ`-valued inner sum of `Tcut` as a
coercion (`Tcut6_eq_sum_ofReal`), replace it pair by pair (`pair_eq`), and swap the resulting
triple sum (`triple_swap`), pulling the modulus weight `φ(d)/d` out of the pair sums
(`hD` in the main theorem).
-/
import Mathlib
import Submission.Work.FIArea6.S16UDefs

set_option autoImplicit false

namespace Work.FIArea6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The inner sum of `Tcut` as a coercion -/

/-- (7.10) on the diagonal: `Δ(z₁,z₂) = 0` forces `logFac6 z₁ z₂ = log 0 = 0`. -/
lemma logFac6_eq_zero_of_absDelta_eq_zero (z1 z2 : GaussianInt)
    (h : Work.FIPlan.absDelta z1 z2 = 0) : Work.FITop4.logFac6 z1 z2 = 0 := by
  simp only [Work.FITop4.logFac6, h]
  norm_num

/-- `Work.FITop4.Tcut` is the coercion of the corresponding `ℝ`-valued inner sum (the round-6
analogue of `Work.FIArea4.Tcut_eq_sum_ofReal`; reproduced here so that this module depends only on
the §16 vocabulary). -/
theorem Tcut6_eq_sum_ofReal (Rz : ℤ) (cut : GaussianInt → GaussianInt → ℕ → ℝ)
    (β : GaussianInt → ℂ) :
    Work.FITop4.Tcut Rz cut β
      = 2 * ∑ z1 ∈ Work.FIPlan.gBox Rz, ∑ z2 ∈ Work.FIPlan.gBox Rz,
          (if Work.FIPlan.GaussCoprime z1 z2 then
            β z1 * star (β z2)
              * ((∑ d ∈ Work.FITop4.Sset z1 z2,
                    ((Nat.totient d : ℝ) / (d : ℝ)) * cut z1 z2 d
                      * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ)
           else 0) := by
  simp only [Work.FITop4.Tcut]
  congr 1
  apply Finset.sum_congr rfl; intro z1 _
  apply Finset.sum_congr rfl; intro z2 _
  by_cases hg : Work.FIPlan.GaussCoprime z1 z2
  · simp only [hg, if_true]
    congr 1
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl; intro d _
    push_cast; ring
  · simp only [hg, if_false]

/-- `Work.FITop4.Ucut` unwound, with its inner `ℝ`-valued pair sum isolated. -/
theorem Ucut6_eq_sum_ofReal (Rz : ℤ) (X : ℕ) (β : GaussianInt → ℂ) :
    Work.FITop4.Ucut Rz X β
      = 2 * ∑ z1 ∈ Work.FIPlan.gBox Rz, ∑ z2 ∈ Work.FIPlan.gBox Rz,
          (if Work.FIPlan.GaussCoprime z1 z2 then
            β z1 * star (β z2)
              * ((∑ d ∈ Work.FITop4.Sset z1 z2,
                    ((Nat.totient d : ℝ) / (d : ℝ)) * (if d ≤ X then (1 : ℝ) else 0)
                      * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ)
           else 0) := by
  simp only [Work.FITop4.Ucut]
  exact Tcut6_eq_sum_ofReal Rz (fun _ _ d => if d ≤ X then (1 : ℝ) else 0) β

/-! ## 2. The index-set identity `Sset ∩ [1,X] = {d ≤ X : 4d ∣ |Δ|}` -/

/-- **The bookkeeping of `Sset`.**  For any `A : ℕ` and any weight `K` vanishing at `A = 0`, the
cut `d ≤ X` inside the index set `{1 ≤ d ≤ A/4+1, 4d ∣ A}` can be replaced by the single condition
`4d ∣ A` on the range `[1,X]`.  For `A ≠ 0` the two index sets coincide, because `4d ∣ A` forces
`4d ≤ A`; for `A = 0` the `d = 1` term of the left-hand side and all terms of the right-hand side
carry the factor `K d = 0`. -/
lemma sum_Sset_cut_eq (A X : ℕ) (K : ℕ → ℂ) (h0 : A = 0 → ∀ d, K d = 0) :
    ∑ d ∈ (Finset.Icc 1 (A / 4 + 1)).filter (fun d => 4 * d ∣ A),
        ((if d ≤ X then (1 : ℝ) else 0 : ℝ) : ℂ) * K d
      = ∑ d ∈ Finset.Icc 1 X, (if 4 * d ∣ A then K d else 0) := by
  have hT : ((Finset.Icc 1 (A / 4 + 1)).filter (fun d => 4 * d ∣ A)).filter (fun d => d ≤ X)
      ⊆ (Finset.Icc 1 X).filter (fun d => 4 * d ∣ A) := by
    intro d hd
    simp only [Finset.mem_filter, Finset.mem_Icc] at hd ⊢
    exact ⟨⟨hd.1.1.1, hd.2⟩, hd.1.2⟩
  have hzero : ∀ d ∈ (Finset.Icc 1 X).filter (fun d => 4 * d ∣ A),
      d ∉ ((Finset.Icc 1 (A / 4 + 1)).filter (fun d => 4 * d ∣ A)).filter (fun d => d ≤ X) →
      K d = 0 := by
    intro d hd hnot
    simp only [Finset.mem_filter, Finset.mem_Icc] at hd
    obtain ⟨⟨h1, h2⟩, h3⟩ := hd
    have hA0 : A = 0 := by
      by_contra hne
      have hpos : 0 < A := Nat.pos_of_ne_zero hne
      have hle : 4 * d ≤ A := Nat.le_of_dvd hpos h3
      have hd4 : d ≤ A / 4 := by omega
      exact hnot (by
        simp only [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨⟨h1, by omega⟩, h3⟩, h2⟩)
    exact h0 hA0 d
  calc ∑ d ∈ (Finset.Icc 1 (A / 4 + 1)).filter (fun d => 4 * d ∣ A),
        ((if d ≤ X then (1 : ℝ) else 0 : ℝ) : ℂ) * K d
      = ∑ d ∈ (Finset.Icc 1 (A / 4 + 1)).filter (fun d => 4 * d ∣ A),
          (if d ≤ X then K d else 0) := by
        apply Finset.sum_congr rfl; intro d _
        by_cases h : d ≤ X <;> simp [h]
    _ = ∑ d ∈ ((Finset.Icc 1 (A / 4 + 1)).filter (fun d => 4 * d ∣ A)).filter
          (fun d => d ≤ X), K d :=
        (Finset.sum_filter (s := (Finset.Icc 1 (A / 4 + 1)).filter (fun d => 4 * d ∣ A))
          (p := fun d => d ≤ X) (f := K)).symm
    _ = ∑ d ∈ (Finset.Icc 1 X).filter (fun d => 4 * d ∣ A), K d :=
        Finset.sum_subset hT hzero
    _ = ∑ d ∈ Finset.Icc 1 X, (if 4 * d ∣ A then K d else 0) :=
        Finset.sum_filter (s := Finset.Icc 1 X) (p := fun d => 4 * d ∣ A) (f := K)

/-! ## 3. The pair identity -/

/-- **(16.1) pair by pair**: the inner `d`-sum of `Ucut` at a pair `(z₁,z₂)` equals the sum over
`d ∈ [1,X]` with `4d ∣ |Δ(z₁,z₂)|` of the (16.2) weight — the `ω`/`d`-sum is *exactly* the
`d ≤ X` part of the `Sset`-sum, no term being lost or gained. -/
lemma pair_eq (z1 z2 : GaussianInt) (X : ℕ) (β : GaussianInt → ℂ) :
    (if Work.FIPlan.GaussCoprime z1 z2 then
        β z1 * star (β z2)
          * ((∑ d ∈ Work.FITop4.Sset z1 z2,
                ((Nat.totient d : ℝ) / (d : ℝ)) * (if d ≤ X then (1 : ℝ) else 0)
                  * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ)
      else 0)
      = ∑ d ∈ Finset.Icc 1 X,
          (if Work.FIPlan.GaussCoprime z1 z2 ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2 then
            ((Nat.totient d : ℝ) / (d : ℝ) : ℂ) * (β z1 * star (β z2)
              * (Work.FITop4.ratioSym z1 z2 d : ℂ) * (Work.FITop4.logFac6 z1 z2 : ℂ))
           else 0) := by
  by_cases hc : Work.FIPlan.GaussCoprime z1 z2
  · simp only [hc, if_true, true_and]
    set K : ℕ → ℂ := fun d => β z1 * star (β z2) * ((Nat.totient d : ℝ) / (d : ℝ) : ℂ)
        * (Work.FITop4.ratioSym z1 z2 d : ℂ) * (Work.FITop4.logFac6 z1 z2 : ℂ) with hK
    have h0 : Work.FIPlan.absDelta z1 z2 = 0 → ∀ d, K d = 0 := by
      intro hA d
      simp only [hK]
      rw [logFac6_eq_zero_of_absDelta_eq_zero z1 z2 hA]
      simp
    rw [Complex.ofReal_sum, Finset.mul_sum]
    rw [show (∑ d ∈ Work.FITop4.Sset z1 z2, β z1 * star (β z2)
          * ((((Nat.totient d : ℝ) / (d : ℝ)) * (if d ≤ X then (1 : ℝ) else 0)
              * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ))
        = ∑ d ∈ Work.FITop4.Sset z1 z2,
            (((if d ≤ X then (1 : ℝ) else 0 : ℝ)) : ℂ) * K d from by
      apply Finset.sum_congr rfl; intro d _
      simp only [hK]; push_cast; ring]
    simp only [Work.FITop4.Sset]
    rw [sum_Sset_cut_eq (Work.FIPlan.absDelta z1 z2) X K h0]
    apply Finset.sum_congr rfl; intro d _
    by_cases hd : 4 * d ∣ Work.FIPlan.absDelta z1 z2
    · rw [if_pos hd, if_pos hd]; simp only [hK]; ring
    · rw [if_neg hd, if_neg hd]
  · simp [hc]

/-! ## 4. Swapping the triple sum -/

/-- `∑_i ∑_j ∑_k = ∑_k ∑_i ∑_j` for sums over finite sets. -/
lemma triple_swap {ι κ ν : Type*} [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]
    (s : Finset ι) (t : Finset κ) (u : Finset ν) (f : ι → κ → ν → ℂ) :
    (∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ u, f i j k) = ∑ k ∈ u, ∑ i ∈ s, ∑ j ∈ t, f i j k := by
  calc ∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ u, f i j k
      = ∑ j ∈ t, ∑ i ∈ s, ∑ k ∈ u, f i j k := Finset.sum_comm
    _ = ∑ j ∈ t, ∑ k ∈ u, ∑ i ∈ s, f i j k := by
          apply Finset.sum_congr rfl; intro j _; exact Finset.sum_comm
    _ = ∑ k ∈ u, ∑ j ∈ t, ∑ i ∈ s, f i j k := Finset.sum_comm
    _ = ∑ k ∈ u, ∑ i ∈ s, ∑ j ∈ t, f i j k := by
          apply Finset.sum_congr rfl; intro k _; exact Finset.sum_comm

/-! ## 5. The identity (16.1)/(16.2) -/

/-- *FI* (16.1)/(16.2): the `U`-cut is the sum over the moduli `d ≤ X` of `(φ(d)/d)·U_d(β)`, where `U_d(β)` is the pair sum with the condition `4d ∣ |Δ(z₁,z₂)|`.  The bookkeeping is exact: for a pair with `Δ ≠ 0` and `4d ∣ |Δ|` one has `d ≤ |Δ|/4 ≤ |Δ|/4 + 1`, so the filter `Icc 1 (|Δ|/4+1)` of `Sset` is automatic; for `Δ = 0` both sides vanish because `logFac6 z1 z2 = log 0 = 0`. -/
theorem Ucut_eq_Vd_sum (Pa : Work.FITop.Params) (X : ℕ) (β : GaussianInt → ℂ) :
    Work.FITop4.Ucut (Work.FITop.radN Pa) X β
      = 2 * ∑ d ∈ Finset.Icc 1 X,
          ((Nat.totient d : ℝ) / (d : ℝ) : ℂ) * Work.FIArea6.Vd Pa d β := by
  rw [Ucut6_eq_sum_ofReal (Work.FITop.radN Pa) X β]
  rw [show Work.FIPlan.gBox (Work.FITop.radN Pa) = Work.FITop.boxN Pa from rfl]
  simp only [Work.FIArea6.Vd]
  congr 1
  have hS : (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
        (if Work.FIPlan.GaussCoprime z1 z2 then
          β z1 * star (β z2)
            * ((∑ d ∈ Work.FITop4.Sset z1 z2,
                  ((Nat.totient d : ℝ) / (d : ℝ)) * (if d ≤ X then (1 : ℝ) else 0)
                    * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ)
         else 0))
      = ∑ d ∈ Finset.Icc 1 X, ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          (if Work.FIPlan.GaussCoprime z1 z2 ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2 then
            ((Nat.totient d : ℝ) / (d : ℝ) : ℂ) * (β z1 * star (β z2)
              * (Work.FITop4.ratioSym z1 z2 d : ℂ) * (Work.FITop4.logFac6 z1 z2 : ℂ))
           else 0) := by
    simp only [pair_eq]
    exact triple_swap (Work.FITop.boxN Pa) (Work.FITop.boxN Pa) (Finset.Icc 1 X)
      (fun z1 z2 d => if Work.FIPlan.GaussCoprime z1 z2 ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2
        then ((Nat.totient d : ℝ) / (d : ℝ) : ℂ) * (β z1 * star (β z2)
              * (Work.FITop4.ratioSym z1 z2 d : ℂ) * (Work.FITop4.logFac6 z1 z2 : ℂ))
        else 0)
  have hD : (∑ d ∈ Finset.Icc 1 X,
        ((Nat.totient d : ℝ) / (d : ℝ) : ℂ) * (∑ z1 ∈ Work.FITop.boxN Pa,
          ∑ z2 ∈ Work.FITop.boxN Pa,
          (if Work.FIPlan.GaussCoprime z1 z2 ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2 then
            β z1 * star (β z2) * (Work.FITop4.ratioSym z1 z2 d : ℂ)
              * (Work.FITop4.logFac6 z1 z2 : ℂ) else 0)))
      = ∑ d ∈ Finset.Icc 1 X, ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          (if Work.FIPlan.GaussCoprime z1 z2 ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2 then
            ((Nat.totient d : ℝ) / (d : ℝ) : ℂ) * (β z1 * star (β z2)
              * (Work.FITop4.ratioSym z1 z2 d : ℂ) * (Work.FITop4.logFac6 z1 z2 : ℂ))
           else 0) := by
    apply Finset.sum_congr rfl; intro d _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro z1 _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro z2 _
    by_cases h : Work.FIPlan.GaussCoprime z1 z2 ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]; ring
  exact hS.trans hD.symm

end

end Work.FIArea6
