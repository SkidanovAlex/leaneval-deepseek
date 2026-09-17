import Submission.E8TensorBound
import Submission.E8Multiplicity
import Submission.Commons.Algebra.Lie.SerreConstruction.weight_tensor_finrank

/-!
# The character of the tensor square `T N = (V ⧸ N) ⊗[ℂ] (V ⧸ N)`

This file proves `ch T = ch V · ch V` for the tensor square of the irreducible quotient
`V ⧸ N = L(ω₁+ω₈)`, i.e.

  `dim (T N)_ν = ∑_ξ dim (V ⧸ N)_ξ · dim (V ⧸ N)_{ν-ξ}`   for every weight `ν`,

by instantiating the commons theorem
`Commons.Algebra.Lie.SerreConstruction.weight_tensor_finrank` (the weight multiplicities of a
tensor product of finite-dimensional `e₈`-modules) for `M = N = V ⧸ N`.

The two ingredients are the bridges

* `Mwt (M := V ⧸ N) μ = Lwt N μ` (both are `⨅ᵢ ker (Hᵢ - μᵢ)`; the `U(e₈)`-module structure on the
  quotient is transported to a Lie-module structure by `Submission.Enveloping.instLieModuleE8`), and
* `Mwt (M := T N) ν = TLwt N ν` (the tensor product carries the *derivation* action, matching
  `Submission.E8Tensor.deriv`).

The finite weight set used is the commons object `E8Iso.L` (all lattice points of squared length
`≤ 10`), which contains every weight of `V ⧸ N` because `mfun` vanishes off `qq ≤ 10`
(`Submission.E8Support.mfun_ne_zero_iff`).
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

noncomputable section
open scoped TensorProduct BigOperators

namespace Submission.E8TensorChar

open Submission.E8Tensor Submission.E8TensorBound Submission.VermaWeight
open Submission.E8WeightSpaces
open Submission.E8Freudenthal
open Commons.Algebra.Lie.SerreConstruction
open Commons.LinearAlgebra.Matrix.Cartan

variable {N : Submodule U V}

/-- The Lie action on `V ⧸ N` (from the `U(e₈)`-action) is the `U(e₈)`-action. -/
theorem toEnd_quot (N : Submodule U V) (i : Fin 8) :
    LieModule.toEnd ℂ (LieAlgebra.e₈ ℂ) (V ⧸ N) (SerreH i)
      = endU N (Submission.E8Weights.h i) := by
  ext x
  rfl

/-- The Lie action on the tensor square is the derivation action. -/
theorem toEnd_tensor (N : Submodule U V) (i : Fin 8) :
    LieModule.toEnd ℂ (LieAlgebra.e₈ ℂ) (T N) (SerreH i)
      = deriv (N := N) (Submission.E8Weights.SerreH i) := by
  ext x
  rfl

/-- **The weight spaces of the quotient `V ⧸ N` for the two module structures agree.** -/
theorem Mwt_quot (N : Submodule U V) (μ : Fin 8 → ℤ) :
    Mwt (M := V ⧸ N) μ = Submission.E8WeightSpaces.Lwt N μ := by
  simp only [Mwt, Submission.E8WeightSpaces.Lwt]
  refine iInf_congr fun i => ?_
  rw [toEnd_quot N i]

/-- **The weight spaces of the tensor square for the two module structures agree.** -/
theorem Mwt_tensor (N : Submodule U V) (ν : Fin 8 → ℤ) :
    Mwt (M := T N) ν = TLwt N ν := by
  simp only [Mwt]
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [Submodule.mem_iInf] at hx
    refine mem_TLwt_of_deriv_h_eq (N := N) ν x ?_
    intro j
    rw [← toEnd_tensor N j]
    exact Module.End.mem_eigenspace_iff.mp (hx j)
  · rw [TLwt_eq_span]
    refine Submodule.span_le.mpr ?_
    rintro x ⟨ν₁, ν₂, hν, a, ha, b, hb, rfl⟩
    refine (Submodule.mem_iInf fun j : Fin 8 =>
      (LieModule.toEnd ℂ (LieAlgebra.e₈ ℂ) (T N) (SerreH j)).eigenspace
        (((ν j : ℤ)) : ℂ)).mpr ?_
    intro j
    rw [Module.End.mem_eigenspace_iff, toEnd_tensor N j, deriv_h_tmul j ha hb]
    rw [show (ν₁ j + ν₂ j : ℤ) = ν j from congrFun hν j]

/-- **`ch T = ch V · ch V`** at every weight. -/
theorem finrank_TLwt_eq_sum (N : Submodule U V) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) (ν : Fin 8 → ℤ) :
    Module.finrank ℂ ↥(TLwt N ν)
      = ∑ ξ ∈ (E8Iso.L.toFinset : Finset (Fin 8 → ℤ)), dmul N ξ * dmul N (ν - ξ) := by
  classical
  have hchar : ∀ w : Fin 8 → ℤ, (Submission.E8Numerics.mfun w : ℚ) = mul N w :=
    Submission.E8Multiplicity.mfun_eq_mul N hvN hmax
  have hS : ∀ w : Fin 8 → ℤ, Lwt N w ≠ ⊥ → w ∈ (E8Iso.L.toFinset : Finset (Fin 8 → ℤ)) := by
    intro w hw
    rw [List.mem_toFinset]
    apply E8Iso.L_mem
    have hpos : 0 < dmul N w := by
      obtain ⟨x, hx, hx0⟩ := (Lwt N w).ne_bot_iff.mp hw
      haveI : Nontrivial ↥(Lwt N w) :=
        ⟨⟨⟨x, hx⟩, 0, fun h => hx0 (Subtype.ext_iff.mp h)⟩⟩
      exact Module.finrank_pos
    have hmul : mul N w ≠ 0 := by
      rw [mul]
      have : (0 : ℚ) < (dmul N w : ℚ) := by exact_mod_cast hpos
      exact ne_of_gt this
    have hmf : Submission.E8Numerics.mfun w ≠ 0 := by
      intro h0
      exact hmul (by rw [← hchar w, h0]; norm_num)
    have hq := (Submission.E8Support.mfun_ne_zero_iff w).mp hmf
    simp only [Submission.E8Numerics.qq] at hq
    rcases hq with h | h | h | h | h | h <;> rw [h] <;> norm_num
  haveI : Module.Finite ℂ (V ⧸ N) := finite_quot N hvN hmax
  rw [← Mwt_tensor N ν]
  rw [weight_tensor_finrank (M := V ⧸ N) (N := V ⧸ N) E8Iso.L.toFinset
      (fun ξ hξ => hS ξ ((Mwt_quot N ξ).symm ▸ hξ)) ν]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [Mwt_quot N ξ, Mwt_quot N (ν - ξ)]


/-- **`ch T = mfun * mfun`**: the weight multiplicity of the tensor square in terms of the
candidate character `mfun` of `V ⧸ N`. -/
theorem finrank_TLwt_eq (N : Submodule U V) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) (ν : Fin 8 → ℤ) :
    (Module.finrank ℂ ↥(TLwt N ν) : ℤ)
      = ∑ ξ ∈ (E8Iso.L.toFinset : Finset (Fin 8 → ℤ)),
          Submission.E8Numerics.mfun ξ * Submission.E8Numerics.mfun (ν - ξ) := by
  classical
  have hchar : ∀ w : Fin 8 → ℤ, (Submission.E8Numerics.mfun w : ℚ) = mul N w :=
    Submission.E8Multiplicity.mfun_eq_mul N hvN hmax
  rw [finrank_TLwt_eq_sum N hvN hmax ν]
  push_cast
  refine Finset.sum_congr rfl fun ξ _ => ?_
  have h1 : (dmul N ξ : ℚ) = (Submission.E8Numerics.mfun ξ : ℚ) := (hchar ξ).symm
  have h2 : (dmul N (ν - ξ) : ℚ) = (Submission.E8Numerics.mfun (ν - ξ) : ℚ) :=
    (hchar (ν - ξ)).symm
  exact_mod_cast (show (dmul N ξ : ℚ) * (dmul N (ν-ξ) : ℚ)
      = (Submission.E8Numerics.mfun ξ : ℚ) * (Submission.E8Numerics.mfun (ν-ξ) : ℚ) by
    rw [h1, h2])

end Submission.E8TensorChar
