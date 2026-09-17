import Submission.E8WCFM
import Submission.E8TensorChar
import Submission.E8WCFV

/-!
# (TRACE-D): `A_ρ · ch T = alt (λ+ρ) * mfun`

For the tensor square `T N = (V ⧸ N) ⊗ (V ⧸ N)` of the irreducible quotient one has
`ch T = mfun * mfun` (`Submission.E8TensorChar.finrank_TLwt_eq`) and `A_ρ · mfun = alt (λ+ρ)`
(`Submission.E8WCFV.WCF_V`).  Associativity of the convolution gives

  `WSum chT x = ∑_{M ∈ W} ε(M) · mfun (x - M(λ + ρ))`   `(TRACE-D)`

which computes `A_ρ · ch T` without any knowledge of the constituent structure of `T N`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

noncomputable section
open scoped BigOperators

namespace Submission.E8Klimyk

open Submission.WCFSetup
open Submission.E8Character
open Submission.E8WCFC
open Submission.E8Tensor Submission.E8TensorBound Submission.VermaWeight
open Submission.E8WeightSpaces
open Submission.E8Numerics
open Commons.LinearAlgebra.Matrix.Cartan

/-- `mfun` vanishes off the finite set `E8Iso.L` of lattice points of squared length `≤ 10`. -/
lemma mfun_eq_zero_of_not_mem {v : Fin 8 → ℤ}
    (h : v ∉ (E8Iso.L.toFinset : Finset (Fin 8 → ℤ))) : mfun v = 0 := by
  by_contra h0
  apply h
  rw [List.mem_toFinset]
  apply E8Iso.L_mem
  have hq := (Submission.E8Support.mfun_ne_zero_iff v).mp h0
  simp only [Submission.E8Numerics.qq] at hq
  rcases hq with h' | h' | h' | h' | h' | h' <;> omega

/-- **The convolution identity for `mfun`**: `∑_{ξ ∈ L} mfun ξ · [ξ = x] = mfun x`. -/
lemma sum_mfun_ite (x : Fin 8 → ℤ) :
    (∑ ξ ∈ (E8Iso.L.toFinset : Finset (Fin 8 → ℤ)),
        (mfun ξ : ℚ) * (if ξ = x then 1 else 0)) = (mfun x : ℚ) := by
  classical
  rw [Finset.sum_eq_single x]
  · simp
  · intro ξ _ hξ
    simp [hξ]
  · intro hx
    rw [mfun_eq_zero_of_not_mem hx]
    simp

/-- `∑_{ξ ∈ L} mfun ξ · (c · [y = x - ξ]) = c · mfun (x - y)`. -/
lemma sum_mfun_ite_sub (x y : Fin 8 → ℤ) (c : ℚ) :
    (∑ ξ ∈ (E8Iso.L.toFinset : Finset (Fin 8 → ℤ)),
        (mfun ξ : ℚ) * (c * (if y = x - ξ then 1 else 0))) = c * mfun (x - y) := by
  classical
  have h1 : (∑ ξ ∈ (E8Iso.L.toFinset : Finset (Fin 8 → ℤ)),
        (mfun ξ : ℚ) * (c * (if y = x - ξ then 1 else 0)))
      = c * ∑ ξ ∈ (E8Iso.L.toFinset : Finset (Fin 8 → ℤ)),
          (mfun ξ : ℚ) * (if ξ = x - y then 1 else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    by_cases h : y = x - ξ
    · rw [if_pos h, if_pos (show ξ = x - y from by rw [h]; abel)]; ring
    · rw [if_neg h,
        if_neg (show ¬(ξ = x - y) from by intro hh; exact h (by rw [hh]; abel))]
      ring
  rw [h1, sum_mfun_ite]

/-- **`A_ρ · mfun` as a sum of deltas** (a restatement of `WCF_V`). -/
lemma WSum_mfun_eq_sum_delta (x : Fin 8 → ℤ) :
    WSum (fun v => (mfun v : ℚ)) x
      = ∑ M ∈ WG, (M.det : ℚ) *
          (if ap M (Submission.E8Enum.lam + rhoV) = x then 1 else 0) := by
  rw [Submission.E8WCFV.WCF_V]
  rfl

/-- **(TRACE-D)**: `WSum chT = alt(λ+ρ) * mfun`. -/
theorem WSum_chT (N : Submodule U V) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) (x : Fin 8 → ℤ) :
    WSum (fun ν => (Module.finrank ℂ ↥(TLwt N ν) : ℚ)) x
      = ∑ M ∈ WG, (M.det : ℚ) *
          mfun (x - ap M (Submission.E8Enum.lam + rhoV)) := by
  classical
  have hterm : ∀ ν : Fin 8 → ℤ, (Module.finrank ℂ ↥(TLwt N ν) : ℚ)
      = ∑ ξ ∈ (E8Iso.L.toFinset : Finset (Fin 8 → ℤ)), (mfun ξ : ℚ) * (mfun (ν - ξ) : ℚ) := by
    intro ν
    have h := Submission.E8TensorChar.finrank_TLwt_eq N hvN hmax ν
    have h2 := congrArg (fun z : ℤ => (z : ℚ)) h
    push_cast at h2
    rw [h2]
  calc WSum (fun ν => (Module.finrank ℂ ↥(TLwt N ν) : ℚ)) x
      = ∑ M ∈ WG, (M.det : ℚ) *
          (∑ ξ ∈ (E8Iso.L.toFinset : Finset (Fin 8 → ℤ)),
            (mfun ξ : ℚ) * (mfun (x - ap M rhoV - ξ) : ℚ)) := by
        rw [WSum]
        refine Finset.sum_congr rfl fun M _ => ?_
        rw [hterm]
    _ = ∑ M ∈ WG, ∑ ξ ∈ (E8Iso.L.toFinset : Finset (Fin 8 → ℤ)),
          (M.det : ℚ) * ((mfun ξ : ℚ) * (mfun (x - ap M rhoV - ξ) : ℚ)) := by
        refine Finset.sum_congr rfl fun M _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ ξ ∈ (E8Iso.L.toFinset : Finset (Fin 8 → ℤ)), ∑ M ∈ WG,
          (M.det : ℚ) * ((mfun ξ : ℚ) * (mfun (x - ap M rhoV - ξ) : ℚ)) :=
        Finset.sum_comm
    _ = ∑ ξ ∈ (E8Iso.L.toFinset : Finset (Fin 8 → ℤ)),
          (mfun ξ : ℚ) * WSum (fun v => (mfun v : ℚ)) (x - ξ) := by
        refine Finset.sum_congr rfl fun ξ _ => ?_
        rw [WSum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun M _ => ?_
        rw [show x - ξ - ap M rhoV = x - ap M rhoV - ξ from by abel]
        ring
    _ = ∑ ξ ∈ (E8Iso.L.toFinset : Finset (Fin 8 → ℤ)), ∑ M ∈ WG,
          (mfun ξ : ℚ) * ((M.det : ℚ) *
            (if ap M (Submission.E8Enum.lam + rhoV) = x - ξ then 1 else 0)) := by
        refine Finset.sum_congr rfl fun ξ _ => ?_
        rw [WSum_mfun_eq_sum_delta, Finset.mul_sum]
    _ = ∑ M ∈ WG, (M.det : ℚ) *
          mfun (x - ap M (Submission.E8Enum.lam + rhoV)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun M _ => ?_
        exact sum_mfun_ite_sub x (ap M (Submission.E8Enum.lam + rhoV)) ((M.det : ℚ))


end E8Klimyk
