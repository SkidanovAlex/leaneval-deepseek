import Submission.E8TensorChar
import Submission.E8WInvariance

/-!
# `W`-invariance of the weight multiplicities of the tensor square

The weight multiplicities of the tensor square `T N = (V ⧸ N) ⊗[ℂ] (V ⧸ N)` are the
**convolution** of the (known) weight multiplicities of `V ⧸ N`:

  `dim (T N)_ν = ∑_ξ d(ξ) · d(ν - ξ)`,   `d(ξ) = dim (V ⧸ N)_ξ`

(`Submission.E8TensorChar.finrank_TLwt_eq_sum`), and `d` is `W`-invariant
(`Submission.E8WInvariance.finrank_Lwt_sref`).  Since a simple reflection `sᵢ` permutes the
weight lattice and preserves the finite set `Commons.LinearAlgebra.Matrix.Cartan.E8Iso.L` of lattice points of squared length `≤ 10`
(the support of `d`), substituting `ξ ↦ sᵢξ` in the convolution gives

  **`dim (T N)_ν = dim (T N)_{sᵢν}`**

— the `W`-invariance of the weight multiplicities of the tensor square, i.e. exactly the
hypothesis (c) of `eq_of_freudenthal` needed to identify the *actual* constituents of `T N`
with the candidate characters `Mnu i`.

This route replaces the `𝔰𝔩₂`-string argument (the mirror `Submission.E8WInvarianceT` of
`Submission.E8WInvariance` for the tensor square, whose string machinery is proved there but
whose restricted-operator step is blocked by an instance diamond) by a two-line convolution
computation.
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

noncomputable section
open scoped BigOperators

namespace Submission.E8WinTensor

open Submission.E8Tensor Submission.E8TensorBound Submission.VermaWeight
open Submission.E8WeightSpaces Submission.E8Freudenthal
open Submission.WeylWeights
open Submission.E8WInvariance Submission.E8Orbit Submission.E8Character

variable {N : Submodule U V}

/-- The squared length is invariant under a simple reflection. -/
lemma qZ_sref (i : Fin 8) (v : Fin 8 → ℤ) :
    Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ (sref i v)
      = Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ v :=
  Submission.E8Numerics.qZ_foldl [i] v

/-- The simple reflection is additive. -/
lemma sref_sub (i : Fin 8) (a b : Fin 8 → ℤ) : sref i (a - b) = sref i a - sref i b := by
  funext j
  simp only [sref_apply, Pi.sub_apply]
  ring

/-- The finite set `Commons.LinearAlgebra.Matrix.Cartan.E8Iso.L` is exactly the set of lattice points of squared length `≤ 10`. -/
lemma mem_L_toFinset {v : Fin 8 → ℤ} :
    v ∈ (Commons.LinearAlgebra.Matrix.Cartan.E8Iso.L.toFinset : Finset (Fin 8 → ℤ)) ↔ Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ v ≤ 10 := by
  rw [List.mem_toFinset, Commons.LinearAlgebra.Matrix.Cartan.E8Iso.L, Finset.mem_toList]
  exact Set.Finite.mem_toFinset _

/-- `W`-invariance of the weight multiplicities of `V ⧸ N` (restated). -/
theorem dmul_sref (N : Submodule U V) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) (i : Fin 8) (μ : Fin 8 → ℤ) :
    dmul N (sref i μ) = dmul N μ :=
  (Submission.E8WInvariance.finrank_Lwt_sref N hvN hmax i μ).symm

/-- **`W`-invariance of the weight multiplicities of the tensor square.** -/
theorem finrank_TLwt_sref (N : Submodule U V) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) (i : Fin 8) (ν : Fin 8 → ℤ) :
    Module.finrank ℂ ↥(TLwt N ν) = Module.finrank ℂ ↥(TLwt N (sref i ν)) := by
  classical
  set S : Finset (Fin 8 → ℤ) := (Commons.LinearAlgebra.Matrix.Cartan.E8Iso.L.toFinset : Finset (Fin 8 → ℤ)) with hS
  have hmem : ∀ a ∈ S, sref i a ∈ S := by
    intro a ha
    rw [hS, mem_L_toFinset] at ha ⊢
    rw [qZ_sref]
    exact ha
  have hinj : ∀ a₁ ∈ S, ∀ a₂ ∈ S, sref i a₁ = sref i a₂ → a₁ = a₂ := by
    intro a₁ _ a₂ _ h
    have h2 := congrArg (sref i) h
    rwa [sref_involutive i a₁, sref_involutive i a₂] at h2
  have hsurj : ∀ b ∈ S, ∃ a, ∃ (_ : a ∈ S), sref i a = b := by
    intro b hb
    exact ⟨sref i b, hmem b hb, sref_involutive i b⟩
  rw [Submission.E8TensorChar.finrank_TLwt_eq_sum N hvN hmax ν,
    Submission.E8TensorChar.finrank_TLwt_eq_sum N hvN hmax (sref i ν)]
  rw [show (∑ ξ ∈ S, dmul N ξ * dmul N (sref i ν - ξ))
      = ∑ ξ ∈ S, dmul N (sref i ξ) * dmul N (sref i ν - sref i ξ) from
    (Finset.sum_bij (fun a (_ : a ∈ S) => sref i a) (fun a ha => hmem a ha)
      (fun a₁ ha₁ a₂ ha₂ h => hinj a₁ ha₁ a₂ ha₂ h) (fun b hb => hsurj b hb)
      (fun a _ => rfl)).symm]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [show sref i ν - sref i ξ = sref i (ν - ξ) from (sref_sub i ν ξ).symm]
  rw [dmul_sref N hvN hmax i ξ, dmul_sref N hvN hmax i (ν - ξ)]

/-- The same invariance for the iterated dominant-conjugate algorithm `dcl`. -/
lemma finrank_TLwt_dcl (N : Submodule U V) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) (n : ℕ) (ν : Fin 8 → ℤ) :
    Module.finrank ℂ ↥(TLwt N ν) = Module.finrank ℂ ↥(TLwt N (dcl n ν)) := by
  induction n generalizing ν with
  | zero => rfl
  | succ n ih =>
      rw [dcl]
      split
      · rename_i i _
        rw [finrank_TLwt_sref N hvN hmax i ν, ih (sref i ν)]
      · rfl

/-- **`W`-invariance of the weight multiplicities of the tensor square, in the form needed by
`eq_of_freudenthal`**: the multiplicity is invariant under the dominant conjugate. -/
theorem finrank_TLwt_dc (N : Submodule U V) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) (ν : Fin 8 → ℤ) :
    Module.finrank ℂ ↥(TLwt N ν) = Module.finrank ℂ ↥(TLwt N (Submission.E8Character.dc ν)) := by
  have h := finrank_TLwt_dcl N hvN hmax 130 ν
  rwa [show dcl 130 ν = dcX ν from rfl, dcX_eq_dc] at h

end Submission.E8WinTensor
