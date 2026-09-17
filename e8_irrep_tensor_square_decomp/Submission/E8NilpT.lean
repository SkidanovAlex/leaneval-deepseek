import Submission.E8TensorBound
import Submission.E8LocallyNilpotent
import Submission.E8WInvariance

/-!
# Local nilpotence of the raising/lowering operators on the tensor square

The tensor square `T N = (V ⧸ N) ⊗[ℂ] (V ⧸ N)` inherits local nilpotence of `Eᵢ` and `Fᵢ` from
its two factors.  The derivation action of `x` is the sum of the two one-sided actions

  `deriv x = (x·)_L + (x·)_R`   (on `a ⊗ b`: `(x·a) ⊗ b + a ⊗ (x·b)`),

the two summands *commute* (they are `TensorProduct.map` in both orders), and each of them is
locally nilpotent as soon as the factor action is.  The sum of two commuting locally nilpotent
endomorphisms is locally nilpotent, which gives the results.

The local-nilpotence inputs of the `𝔰𝔩₂`-string argument for the *constituents* of the tensor
square (`Submission.E8WInvSub`) are `deriv_e_locallyNilpotent` and `deriv_f_locallyNilpotent`.
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

noncomputable section
open scoped BigOperators TensorProduct

namespace Submission.E8NilpT

open Submission.E8Tensor Submission.E8TensorBound Submission.VermaWeight
open Submission.E8WeightSpaces
open Submission.E8Weights (e f SerreE SerreF SerreH)
open UniversalEnvelopingAlgebra

variable {N : Submodule U V}

/-! ## A general lemma: sums of commuting locally nilpotent endomorphisms -/

/-- Powers beyond the nilpotence index vanish. -/
lemma pow_eq_zero_of_le {M : Type*} [AddCommMonoid M] [Module ℂ M] (A : Module.End ℂ M) {x : M} {n k : ℕ}
    (h : (A^n) x = 0) (hnk : n ≤ k) : (A^k) x = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hnk
  rw [show n + j = j + n from Nat.add_comm n j, pow_add, Module.End.mul_apply, h, map_zero]

/-- **The sum of two commuting locally nilpotent endomorphisms is locally nilpotent.** -/
theorem locallyNilpotent_add {M : Type*} [AddCommGroup M] [Module ℂ M]
    (A B : Module.End ℂ M) (hc : Commute A B)
    (hA : ∀ x : M, ∃ n : ℕ, (A^n) x = 0) (hB : ∀ x : M, ∃ n : ℕ, (B^n) x = 0)
    (x : M) : ∃ n : ℕ, ((A + B)^n) x = 0 := by
  obtain ⟨N₁, hN₁⟩ := hA x
  obtain ⟨N₂, hN₂⟩ := hB x
  refine ⟨N₁ + N₂, ?_⟩
  rw [Commute.add_pow hc, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.mem_range] at hp
  have hzero : (A^p * B^(N₁ + N₂ - p)) x = 0 := by
    rcases lt_or_ge p N₁ with h | h
    · rw [Module.End.mul_apply,
        show (B^(N₁ + N₂ - p)) x = 0 from pow_eq_zero_of_le B hN₂ (by omega), map_zero]
    · rw [(hc.pow_pow p (N₁ + N₂ - p)).eq, Module.End.mul_apply,
        show (A^p) x = 0 from pow_eq_zero_of_le A hN₁ h, map_zero]
  have hcoef : ∀ (f : Module.End ℂ M) (c : ℕ),
      (f * (↑c : Module.End ℂ M)) x = c • (f x) := by
    intro f c
    rw [Module.End.mul_apply,
      show (↑c : Module.End ℂ M) = c • (1 : Module.End ℂ M) from
        (by rw [nsmul_eq_mul, mul_one]),
      LinearMap.smul_apply, Module.End.one_apply, map_nsmul]
  rw [hcoef (A^p * B^(N₁ + N₂ - p)) ((N₁ + N₂).choose p), hzero, smul_zero]

/-! ## The two one-sided actions on the tensor square -/

/-- The left action of `u : U(e₈)` on the tensor square, acting on the first factor. -/
noncomputable def rEnd (N : Submodule U V) (u : U) : Module.End ℂ (T N) :=
  LinearMap.rTensor (V ⧸ N) (endU N u)

/-- The right action of `u : U(e₈)` on the tensor square, acting on the second factor. -/
noncomputable def lEnd (N : Submodule U V) (u : U) : Module.End ℂ (T N) :=
  LinearMap.lTensor (V ⧸ N) (endU N u)

lemma rEnd_apply (u : U) (x : T N) : rEnd N u x = (LinearMap.rTensor (V ⧸ N) (endU N u)) x := rfl

lemma rEnd_tmul (u : U) (a b : V ⧸ N) :
    rEnd N u (a ⊗ₜ[ℂ] b) = (endU N u a) ⊗ₜ[ℂ] b :=
  LinearMap.rTensor_tmul (V ⧸ N) (endU N u) b a

lemma lEnd_tmul (u : U) (a b : V ⧸ N) :
    lEnd N u (a ⊗ₜ[ℂ] b) = a ⊗ₜ[ℂ] (endU N u b) :=
  LinearMap.lTensor_tmul (V ⧸ N) (endU N u) a b

lemma rEnd_pow (u : U) (k : ℕ) : (rEnd N u)^k = rEnd N (u^k) := by
  rw [rEnd, rEnd, Submission.E8WInvariance.endU_pow, LinearMap.rTensor_pow]

lemma lEnd_pow (u : U) (k : ℕ) : (lEnd N u)^k = lEnd N (u^k) := by
  rw [lEnd, lEnd, Submission.E8WInvariance.endU_pow, LinearMap.lTensor_pow]

lemma rEnd_pow_apply_tmul (u : U) (k : ℕ) (a b : V ⧸ N) :
    ((rEnd N u)^k) (a ⊗ₜ[ℂ] b) = ((endU N (u^k)) a) ⊗ₜ[ℂ] b := by
  rw [rEnd_pow, rEnd_tmul]

lemma lEnd_pow_apply_tmul (u : U) (k : ℕ) (a b : V ⧸ N) :
    ((lEnd N u)^k) (a ⊗ₜ[ℂ] b) = a ⊗ₜ[ℂ] ((endU N (u^k)) b) := by
  rw [lEnd_pow, lEnd_tmul]

/-- The two one-sided actions commute. -/
lemma commute_rEnd_lEnd (u : U) : Commute (rEnd N u) (lEnd N u) := by
  have h1 : rEnd N u * lEnd N u = TensorProduct.map (endU N u) (endU N u) :=
    LinearMap.rTensor_comp_lTensor (V ⧸ N) (endU N u) (endU N u)
  have h2 : lEnd N u * rEnd N u = TensorProduct.map (endU N u) (endU N u) :=
    LinearMap.lTensor_comp_rTensor (V ⧸ N) (endU N u) (endU N u)
  rw [Commute, SemiconjBy]
  exact h1.trans h2.symm

/-- Local nilpotence of the left action, from local nilpotence of the factor. -/
lemma locallyNilpotent_rEnd (u : U) (h : ∀ y : V ⧸ N, ∃ n : ℕ, (endU N (u^n)) y = 0)
    (x : T N) : ∃ n : ℕ, ((rEnd N u)^n) x = 0 := by
  classical
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨1, by simp⟩
  | tmul a b =>
      obtain ⟨n, hn⟩ := h a
      exact ⟨n, by rw [rEnd_pow_apply_tmul, hn, TensorProduct.zero_tmul]⟩
  | add x y hx hy =>
      obtain ⟨n₁, hn₁⟩ := hx
      obtain ⟨n₂, hn₂⟩ := hy
      refine ⟨n₁ + n₂, ?_⟩
      have h₁ : ((rEnd N u)^(n₁ + n₂)) x = 0 :=
        pow_eq_zero_of_le (rEnd N u) (n := n₁) hn₁ (by omega)
      have h₂ : ((rEnd N u)^(n₁ + n₂)) y = 0 :=
        pow_eq_zero_of_le (rEnd N u) (n := n₂) hn₂ (by omega)
      rw [map_add, h₁, h₂, add_zero]

/-- Local nilpotence of the right action, from local nilpotence of the factor. -/
lemma locallyNilpotent_lEnd (u : U) (h : ∀ y : V ⧸ N, ∃ n : ℕ, (endU N (u^n)) y = 0)
    (x : T N) : ∃ n : ℕ, ((lEnd N u)^n) x = 0 := by
  classical
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨1, by simp⟩
  | tmul a b =>
      obtain ⟨n, hn⟩ := h b
      exact ⟨n, by rw [lEnd_pow_apply_tmul, hn, TensorProduct.tmul_zero]⟩
  | add x y hx hy =>
      obtain ⟨n₁, hn₁⟩ := hx
      obtain ⟨n₂, hn₂⟩ := hy
      refine ⟨n₁ + n₂, ?_⟩
      have h₁ : ((lEnd N u)^(n₁ + n₂)) x = 0 :=
        pow_eq_zero_of_le (lEnd N u) (n := n₁) hn₁ (by omega)
      have h₂ : ((lEnd N u)^(n₁ + n₂)) y = 0 :=
        pow_eq_zero_of_le (lEnd N u) (n := n₂) hn₂ (by omega)
      rw [map_add, h₁, h₂, add_zero]

/-! ## The derivation action as a sum of the two one-sided actions -/

lemma deriv_eq_rEnd_add_lEnd (z : LieAlgebra.e₈ ℂ) :
    deriv (N := N) z
      = rEnd N (UniversalEnvelopingAlgebra.ι ℂ z) + lEnd N (UniversalEnvelopingAlgebra.ι ℂ z) := by
  apply LinearMap.ext
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
      rw [deriv_tmul, LinearMap.add_apply, rEnd_tmul, lEnd_tmul]
      simp only [endU_apply]
  | add p q hp hq => rw [map_add, hp, hq, map_add]

/-! ## Local nilpotence of `Eᵢ` and `Fᵢ` on the tensor square -/

/-- **`Eᵢ` is locally nilpotent on the tensor square.** -/
theorem deriv_e_locallyNilpotent (N : Submodule U V) (i : Fin 8) (x : T N) :
    ∃ n : ℕ, ((deriv (N := N) (SerreE i))^n) x = 0 := by
  have hA : ∀ y : V ⧸ N, ∃ n : ℕ, (endU N ((e i)^n)) y = 0 := fun y => by
    obtain ⟨n, hn⟩ := Submission.E8LocallyNilpotent.e_locallyNilpotent N i y
    exact ⟨n, by simpa [e] using hn⟩
  have h := locallyNilpotent_add (rEnd N (e i)) (lEnd N (e i)) (commute_rEnd_lEnd (e i))
    (locallyNilpotent_rEnd (e i) hA) (locallyNilpotent_lEnd (e i) hA) x
  rwa [show rEnd N (e i) + lEnd N (e i)
    = deriv (N := N) (SerreE i) from (deriv_eq_rEnd_add_lEnd (SerreE i)).symm] at h

/-- **`Fᵢ` is locally nilpotent on the tensor square.** -/
theorem deriv_f_locallyNilpotent (N : Submodule U V) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) (i : Fin 8) (x : T N) :
    ∃ n : ℕ, ((deriv (N := N) (SerreF i))^n) x = 0 := by
  have hA : ∀ y : V ⧸ N, ∃ n : ℕ, (endU N ((f i)^n)) y = 0 := fun y => by
    obtain ⟨n, hn⟩ := Submission.E8LocallyNilpotent.f_locallyNilpotent N hvN hmax i y
    exact ⟨n, by simpa [f] using hn⟩
  have h := locallyNilpotent_add (rEnd N (f i)) (lEnd N (f i)) (commute_rEnd_lEnd (f i))
    (locallyNilpotent_rEnd (f i) hA) (locallyNilpotent_lEnd (f i) hA) x
  rwa [show rEnd N (f i) + lEnd N (f i)
    = deriv (N := N) (SerreF i) from (deriv_eq_rEnd_add_lEnd (SerreF i)).symm] at h

end Submission.E8NilpT
