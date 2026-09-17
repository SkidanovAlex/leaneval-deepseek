import Submission.E8WCFC
import Submission.E8WCFD

/-!
# The Euler characteristic of the Verma modules: support and Freudenthal recursion

`Submission/E8WCFC.lean` defines `euler Λ = ∑_{N ∈ W} ε(N) chV(N·Λ)` (the Euler characteristic of
the Verma modules on the dot-orbit of `Λ`) and proves `A_ρ · euler Λ = A_{Λ+ρ}` and the height
bound `euler Λ μ ≠ 0 ⟹ htOf μ ≤ htOf Λ`.

This file adds the two remaining structural properties of `euler Λ` for a **dominant** `Λ`:

* `euler_support` — **the support bound**: `euler Λ μ ≠ 0 → Λ - μ ∈ ℕΦ⁺ ∪ {0}`.  This is the
  analogue of the "weights of `L(Λ)` are ≤ Λ" statement; note that it does *not* need the
  `W`-invariance of `euler Λ`.  The proof is the observation that a *single* non-zero summand
  `chV(N·Λ) μ = K(N(Λ+ρ) - ρ - μ)` already forces `N(Λ+ρ)-ρ-μ ∈ ℕΦ⁺`, and then
  `Λ - μ = (N(Λ+ρ)-ρ-μ) + (Λ+ρ - N(Λ+ρ))` is a sum of two cone elements (`Λ+ρ` is strictly
  dominant, so `N(Λ+ρ) ⪯ Λ+ρ`).

* `euler_freudenthal` — **the Freudenthal recursion**, valid at *every* weight `ν` (not only at the
  dominant ones): it is the sum of the recursions of the Verma characters `chV(N·Λ)`, whose
  Casimir coefficients agree (`Bint (N·Λ) = Bint Λ`).  The `k`-ranges have to be compared, which is
  where `htOf_dot_le` and the vanishing `chV ν' μ = 0` for `htOf (ν'-μ) < 0` are used.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

noncomputable section
open scoped BigOperators

namespace Submission.E8WCFE

open Commons.LinearAlgebra.Matrix.Cartan
open Submission.WCFSetup
open Submission.E8Character
open Submission.E8WCFC
open Submission.E8WCFD
open Submission.E8Casimir

/-! ## Vanishing of the Kostant function off the cone -/

/-- The Kostant partition function vanishes off the positive cone. -/
lemma KP_eq_zero_of_htOf_neg {γ : Fin 8 → ℤ} (h : htOf γ < 0) : KP γ = 0 := by
  by_contra h0
  have := htOf_nonneg (KP_posCon h0)
  linarith

/-- The Verma character vanishes off the support cone. -/
lemma chV_eq_zero_of_htOf_neg {ν μ : Fin 8 → ℤ} (h : htOf (ν - μ) < 0) : chV ν μ = 0 := by
  rw [chV, KP_eq_zero_of_htOf_neg h]
  norm_num

/-! ## The height of the dot action -/

/-- `htOf (N · Λ) ≤ htOf Λ` for a dominant `Λ`: `N · Λ` is a weight of the Verma module `M(Λ)`. -/
theorem htOf_dot_le {Λ : Fin 8 → ℤ} (hΛ : ∀ i, 0 ≤ Λ i)
    {N : Matrix (Fin 8) (Fin 8) ℤ} (hN : N ∈ WG) : htOf (dot N Λ) ≤ htOf Λ := by
  obtain ⟨L, rfl⟩ := mem_WG.mp hN
  have h3 : htOf (dot (wactMat L) Λ) = htOf (wact L (Λ + rhoV)) - 620 := by
    rw [htOf_dot, wactMat_ap]
  have h4 : htOf (wact L (Λ + rhoV)) ≤ htOf (Λ + rhoV) := by
    have h5 : posCon (Λ + rhoV - wact L (Λ + rhoV)) :=
      posCon_dom_sub_wact L (Λ + rhoV)
        (fun i => by have := hΛ i; simp only [Pi.add_apply, rhoV, Pi.one_apply]; omega)
    have h6 := htOf_nonneg h5
    rw [htOf_sub] at h6
    linarith
  have h7 : htOf (Λ + rhoV) = htOf Λ + 620 := by rw [htOf_add, htOf_rhoV]
  linarith

/-- `Bint` is invariant under the dot action of the whole Weyl group. -/
lemma Bint_dot_eq {Λ : Fin 8 → ℤ} {N : Matrix (Fin 8) (Fin 8) ℤ} (hN : N ∈ WG) :
    Bint (dot N Λ) = Bint Λ := by
  obtain ⟨L, rfl⟩ := mem_WG.mp hN
  exact Bint_dot' L Λ

/-! ## The support bound -/

/-- **The support of the Euler characteristic of the Verma modules.**  For a dominant `Λ`, a
non-zero value of `euler Λ` can only be attained at a weight `μ ⪯ Λ` in the cone order. -/
theorem euler_support {Λ : Fin 8 → ℤ} (hΛ : ∀ i, 0 ≤ Λ i) {μ : Fin 8 → ℤ}
    (h : euler Λ μ ≠ 0) : posCon (Λ - μ) := by
  rw [euler] at h
  obtain ⟨N, hN, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hch : chV (dot N Λ) μ ≠ 0 := fun h0 => hterm (by rw [h0, mul_zero])
  have hKP : KP (dot N Λ - μ) ≠ 0 := fun h0 => hch (by simp [chV, h0])
  have h1 := KP_posCon hKP
  -- Λ + ρ is strictly dominant, hence `N(Λ+ρ) ⪯ Λ+ρ`
  obtain ⟨L, rfl⟩ := mem_WG.mp hN
  have h2 : posCon (Λ + rhoV - wact L (Λ + rhoV)) :=
    posCon_dom_sub_wact L (Λ + rhoV)
      (fun i => by have := hΛ i; simp only [Pi.add_apply, rhoV, Pi.one_apply]; omega)
  have h2' : posCon (Λ - dot (wactMat L) Λ) := by
    have heq : Λ - dot (wactMat L) Λ = Λ + rhoV - wact L (Λ + rhoV) := by
      rw [dot, wactMat_ap]
      abel
    rw [heq]; exact h2
  have hsum : Λ - μ = (dot (wactMat L) Λ - μ) + (Λ - dot (wactMat L) Λ) := by abel
  rw [hsum]
  exact posCon_add h1 h2'

/-- **The support bound in the "height" form**: the support of `euler Λ` is contained in the cone
translate `Λ - ℕΦ⁺`. -/
theorem euler_support_ht {Λ : Fin 8 → ℤ} (hΛ : ∀ i, 0 ≤ Λ i) {μ : Fin 8 → ℤ}
    (h : euler Λ μ ≠ 0) : Λ - μ = 0 ∨ posCon (Λ - μ) := Or.inr (euler_support hΛ h)

/-! ## The Freudenthal recursion -/

/-- The `k`-range of `chV (N·Λ)` is contained in the `k`-range attached to `Λ`, the extra terms
vanishing. -/
lemma chV_dot_range {Λ ν : Fin 8 → ℤ} (hΛ : ∀ i, 0 ≤ Λ i) {N : Matrix (Fin 8) (Fin 8) ℤ}
    (hN : N ∈ WG) (j : Fin 120) :
    (∑ k ∈ Finset.Icc 1 (htOf (Λ - ν)).toNat,
        (brk (ν + k • pR j) j : ℚ) * chV (dot N Λ) (ν + k • pR j))
      = ∑ k ∈ Finset.Icc 1 (htOf (dot N Λ - ν)).toNat,
          (brk (ν + k • pR j) j : ℚ) * chV (dot N Λ) (ν + k • pR j) := by
  classical
  refine (Finset.sum_subset ?_ ?_).symm
  · -- the `dot N Λ`-range is contained in the `Λ`-range
    intro k hk
    rw [Finset.mem_Icc] at hk ⊢
    refine ⟨hk.1, ?_⟩
    have hdt := htOf_dot_le (Λ := Λ) hΛ hN
    have hsub : htOf (dot N Λ - ν) = htOf (dot N Λ) - htOf ν := htOf_sub _ _
    have hsub2 : htOf (Λ - ν) = htOf Λ - htOf ν := htOf_sub _ _
    have htoNat : (htOf (dot N Λ - ν)).toNat ≤ (htOf (Λ - ν)).toNat := by
      rw [hsub, hsub2]
      omega
    omega
  · intro k hk hknot
    rw [Finset.mem_Icc] at hk hknot
    have hlt : htOf (dot N Λ - (ν + k • pR j)) < 0 := by
      have hsub : htOf (dot N Λ - (ν + k • pR j))
          = htOf (dot N Λ - ν) - (k : ℤ) * htOf (pR j) := by
        rw [show dot N Λ - (ν + k • pR j) = (dot N Λ - ν) - k • pR j from by abel,
          htOf_sub, htOf_nsmul]
      rw [hsub]
      have h1 : (htOf (dot N Λ - ν)).toNat < k := by
        by_contra hc
        exact hknot ⟨hk.1, by omega⟩
      have h2 : htOf (dot N Λ - ν) < (k : ℤ) := by
        have := Int.self_le_toNat (htOf (dot N Λ - ν))
        omega
      have h3 : 1 ≤ htOf (pR j) := htOf_pR j
      have hk0 : (0:ℤ) ≤ (k:ℤ) := by positivity
      nlinarith [h3, hk0]
    rw [chV_eq_zero_of_htOf_neg hlt, mul_zero]

open scoped BigOperators in
/-- Reordering a triple sum with a `k`-range depending only on `ν`. -/
lemma sum3_comm (Λ ν : Fin 8 → ℤ) (F : Matrix (Fin 8) (Fin 8) ℤ → Fin 120 → ℕ → ℚ) :
    (∑ N ∈ WG, ∑ j : Fin 120, ∑ k ∈ Finset.Icc 1 (htOf (Λ - ν)).toNat, F N j k)
      = ∑ j : Fin 120, ∑ k ∈ Finset.Icc 1 (htOf (Λ - ν)).toNat, ∑ N ∈ WG, F N j k := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]

/-- **The Freudenthal recursion for `euler Λ`** (valid at every weight `ν`). -/
theorem euler_freudenthal (Λ : Fin 8 → ℤ) (hΛ : ∀ i, 0 ≤ Λ i) (ν : Fin 8 → ℤ) :
    (Bint Λ - Bint ν) * euler Λ ν
      = 2 * ∑ j : Fin 120, ∑ k ∈ Finset.Icc 1 (htOf (Λ - ν)).toNat,
          (brk (ν + k • pR j) j : ℚ) * euler Λ (ν + k • pR j) := by
  classical
  have h1 : (Bint Λ - Bint ν) * euler Λ ν
      = ∑ N ∈ WG, (N.det : ℚ) *
          ((Bint Λ - Bint ν) * chV (dot N Λ) ν) := by
    rw [euler, Finset.mul_sum]
    refine Finset.sum_congr rfl fun N _ => ?_
    ring
  have h2 : ∀ N ∈ WG, (N.det : ℚ) * ((Bint Λ - Bint ν) * chV (dot N Λ) ν)
      = (N.det : ℚ) * (2 * ∑ j : Fin 120, ∑ k ∈ Finset.Icc 1 (htOf (Λ - ν)).toNat,
          (brk (ν + k • pR j) j : ℚ) * chV (dot N Λ) (ν + k • pR j)) := by
    intro N hN
    have hB : Bint (dot N Λ) = Bint Λ := Bint_dot_eq hN
    have hf := chV_freudenthal (dot N Λ) ν
    rw [hB] at hf
    have hrange : (∑ j : Fin 120, ∑ k ∈ Finset.Icc 1 (htOf (dot N Λ - ν)).toNat,
            (brk (ν + k • pR j) j : ℚ) * chV (dot N Λ) (ν + k • pR j))
        = ∑ j : Fin 120, ∑ k ∈ Finset.Icc 1 (htOf (Λ - ν)).toNat,
            (brk (ν + k • pR j) j : ℚ) * chV (dot N Λ) (ν + k • pR j) :=
      Finset.sum_congr rfl fun (j : Fin 120) _ => (chV_dot_range (Λ := Λ) (ν := ν) hΛ hN j).symm
    rw [hrange] at hf
    rw [hf]
  rw [h1]
  have h2sum : (∑ N ∈ WG, (N.det : ℚ) * ((Bint Λ - Bint ν) * chV (dot N Λ) ν))
      = ∑ N ∈ WG, (N.det : ℚ) * (2 * ∑ j : Fin 120,
          ∑ k ∈ Finset.Icc 1 (htOf (Λ - ν)).toNat,
            (brk (ν + k • pR j) j : ℚ) * chV (dot N Λ) (ν + k • pR j)) :=
    Finset.sum_congr rfl h2
  rw [h2sum]
  -- Step 1: factor the constant `2` out of the outer sum
  have step1 : (∑ N ∈ WG, (N.det : ℚ) * (2 * ∑ j : Fin 120,
        ∑ k ∈ Finset.Icc 1 (htOf (Λ - ν)).toNat,
          (brk (ν + k • pR j) j : ℚ) * chV (dot N Λ) (ν + k • pR j)))
      = ∑ N ∈ WG, (2 : ℚ) * ((N.det : ℚ) * ∑ j : Fin 120,
          ∑ k ∈ Finset.Icc 1 (htOf (Λ - ν)).toNat,
            (brk (ν + k • pR j) j : ℚ) * chV (dot N Λ) (ν + k • pR j)) :=
    Finset.sum_congr rfl fun N _ => by ring
  rw [step1, ← Finset.mul_sum]
  congr 1
  -- Step 2: distribute the `det N` over the inner sum
  have step2 : (∑ N ∈ WG, (N.det : ℚ) * ∑ j : Fin 120,
        ∑ k ∈ Finset.Icc 1 (htOf (Λ - ν)).toNat,
          (brk (ν + k • pR j) j : ℚ) * chV (dot N Λ) (ν + k • pR j))
      = ∑ N ∈ WG, ∑ j : Fin 120, ∑ k ∈ Finset.Icc 1 (htOf (Λ - ν)).toNat,
          (N.det : ℚ) * ((brk (ν + k • pR j) j : ℚ) * chV (dot N Λ) (ν + k • pR j)) := by
    refine Finset.sum_congr rfl fun N _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun (j : Fin 120) _ => ?_
    rw [Finset.mul_sum]
  rw [step2, sum3_comm]
  -- Step 3: identify the inner sum with `euler Λ`
  refine Finset.sum_congr rfl fun (j : Fin 120) _ => ?_
  refine Finset.sum_congr rfl fun (k : ℕ) _ => ?_
  rw [euler, Finset.mul_sum]
  refine Finset.sum_congr rfl fun N _ => ?_
  ring

end Submission.E8WCFE
