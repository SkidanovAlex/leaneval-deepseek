import Submission.E8TensorBound
import Submission.E8LocallyNilpotent
import Submission.E8WInvariance
import Submission.Commons.LinearAlgebra.End.iSup_inf_eigenspace_eq
import Submission.Commons.LinearAlgebra.End.sl2_eigenspace_finrank_symm

/-!
# `W`-invariance of the weight multiplicities of the tensor square

`Submission/E8WInvariance.lean` proves that the multiplicity function
`ν ↦ finrank ℂ (Lwt ν)` of the irreducible quotient `L(ω₁+ω₈) = V ⧸ N` is invariant under every
simple reflection.  The same argument works verbatim for the tensor square `T N = (V ⧸ N) ⊗ (V ⧸
N)`, with the derivation action `deriv` (`Submission.E8Tensor`) in place of the enveloping-algebra
action `endU`:

* `StrT i ν = ⨆ c : ℤ, TLwt (ν + c αᵢ)` is the `αᵢ`-string through `ν`, stable under
  `Hᵢ`, `Eᵢ`, `Fᵢ` (`deriv_h_maps_StrT`, `deriv_e_maps_StrT`, `deriv_f_maps_StrT`);
* the `Hᵢ`-eigenspaces inside the string are the single weight spaces
  (`StrT_inf_eigenspace_shift`, via `Commons.LinearAlgebra.End.iSup_inf_eigenspace_eq`);
* `Commons.LinearAlgebra.End.sl2_eigenspace_finrank_symm`, applied to the string, gives
  **`finrank (TLwt ν) = finrank (TLwt (sᵢν))`** (`finrank_TLwt_sref`).

The `Eᵢ`/`Fᵢ` actions shift the weight by `±αᵢ` (`deriv_e_apply_mem_TLwt`,
`deriv_f_apply_mem_TLwt`), and their local nilpotence on `T N` follows from the local nilpotence
of the corresponding endomorphisms of `V ⧸ N` (`Submission.E8LocallyNilpotent`).
-/

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

noncomputable section
open scoped BigOperators TensorProduct

namespace Submission.E8WInvarianceT

open Submission.E8Tensor Submission.E8TensorBound
open Submission.VermaWeight
open Submission.E8WeightSpaces
open Submission.E8Weights (e f h SerreE SerreF SerreH)
open Submission.WeylWeights (sref sref_apply)
open Submission.E8WInvariance (shift shift_zero shift_succ shift_pred shift_apply_eigen E8symm E8diag)

variable {N : Submodule U V}

/-- The tensor square analogue of the `αᵢ`-string: `⨆ c, TLwt (ν + c αᵢ)`. -/
def StrT (N : Submodule U V) (i : Fin 8) (ν : Fin 8 → ℤ) : Submodule ℂ (T N) :=
  ⨆ c : ℤ, TLwt N (shift i ν c)

lemma TLwt_le_StrT (N : Submodule U V) (i : Fin 8) (ν : Fin 8 → ℤ) (c : ℤ) :
    TLwt N (shift i ν c) ≤ StrT N i ν :=
  le_iSup (fun c : ℤ => TLwt N (shift i ν c)) c

/-- `Eᵢ` raises the weight by `αᵢ`. -/
lemma deriv_e_apply_mem_TLwt (i : Fin 8) {μ : Fin 8 → ℤ} {x : T N} (hx : x ∈ TLwt N μ) :
    deriv (N := N) (SerreE i) x ∈ TLwt N (fun j => μ j + CartanMatrix.E₈ j i) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨ν₁, ν₂, hsum, a, ha, b, hb, rfl⟩ := hy
      subst hsum
      rw [deriv_tmul]
      refine Submodule.add_mem _ ?_ ?_
      · have hh := tmul_mem_TLwt (endU_e_apply_mem_Lwt N i ha) hb
        rw [show (fun j => ν₁ j + CartanMatrix.E₈ j i) + ν₂
              = (fun j => (ν₁ + ν₂) j + CartanMatrix.E₈ j i) from by
            funext j; simp only [Pi.add_apply]; ring] at hh
        exact hh
      · have hh := tmul_mem_TLwt ha (endU_e_apply_mem_Lwt N i hb)
        rw [show ν₁ + (fun j => ν₂ j + CartanMatrix.E₈ j i)
              = (fun j => (ν₁ + ν₂) j + CartanMatrix.E₈ j i) from by
            funext j; simp only [Pi.add_apply]; ring] at hh
        exact hh
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add p q _ _ ihp ihq => rw [map_add]; exact Submodule.add_mem _ ihp ihq
  | smul c p _ ih => rw [map_smul]; exact Submodule.smul_mem _ _ ih

/-- `Fᵢ` lowers the weight by `αᵢ`. -/
lemma deriv_f_apply_mem_TLwt (i : Fin 8) {μ : Fin 8 → ℤ} {x : T N} (hx : x ∈ TLwt N μ) :
    deriv (N := N) (SerreF i) x ∈ TLwt N (fun j => μ j - CartanMatrix.E₈ j i) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨ν₁, ν₂, hsum, a, ha, b, hb, rfl⟩ := hy
      subst hsum
      rw [deriv_tmul]
      refine Submodule.add_mem _ ?_ ?_
      · have hh := tmul_mem_TLwt (endU_f_apply_mem_Lwt N i ha) hb
        rw [show (fun j => ν₁ j - CartanMatrix.E₈ j i) + ν₂
              = (fun j => (ν₁ + ν₂) j - CartanMatrix.E₈ j i) from by
            funext j; simp only [Pi.add_apply]; ring] at hh
        exact hh
      · have hh := tmul_mem_TLwt ha (endU_f_apply_mem_Lwt N i hb)
        rw [show ν₁ + (fun j => ν₂ j - CartanMatrix.E₈ j i)
              = (fun j => (ν₁ + ν₂) j - CartanMatrix.E₈ j i) from by
            funext j; simp only [Pi.add_apply]; ring] at hh
        exact hh
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add p q _ _ ihp ihq => rw [map_add]; exact Submodule.add_mem _ ihp ihq
  | smul c p _ ih => rw [map_smul]; exact Submodule.smul_mem _ _ ih

theorem deriv_h_maps_StrT (i : Fin 8) (ν : Fin 8 → ℤ) :
    Submodule.map (deriv (N := N) (SerreH i)) (StrT N i ν) ≤ StrT N i ν := by
  rw [StrT, Submodule.map_iSup]
  refine iSup_le fun c => ?_
  refine Submodule.map_le_iff_le_comap.mpr fun x hx => ?_
  have hx' : deriv (N := N) (SerreH i) x = ((((shift i ν c) i : ℤ)) : ℂ) • x :=
    deriv_h_eq_of_mem_TLwt i hx
  refine le_iSup (fun c : ℤ => TLwt N (shift i ν c)) c ?_
  rw [hx']
  exact Submodule.smul_mem _ _ hx

theorem deriv_e_maps_StrT (i : Fin 8) (ν : Fin 8 → ℤ) :
    Submodule.map (deriv (N := N) (SerreE i)) (StrT N i ν) ≤ StrT N i ν := by
  rw [StrT, Submodule.map_iSup]
  refine iSup_le fun c => ?_
  refine Submodule.map_le_iff_le_comap.mpr fun x hx => ?_
  have h := deriv_e_apply_mem_TLwt (N := N) i hx
  rw [← shift_succ] at h
  exact le_iSup (fun c : ℤ => TLwt N (shift i ν c)) (c + 1) h

theorem deriv_f_maps_StrT (i : Fin 8) (ν : Fin 8 → ℤ) :
    Submodule.map (deriv (N := N) (SerreF i)) (StrT N i ν) ≤ StrT N i ν := by
  rw [StrT, Submodule.map_iSup]
  refine iSup_le fun c => ?_
  refine Submodule.map_le_iff_le_comap.mpr fun x hx => ?_
  have h := deriv_f_apply_mem_TLwt (N := N) i hx
  rw [← shift_pred] at h
  exact le_iSup (fun c : ℤ => TLwt N (shift i ν c)) (c - 1) h

/-! ## The `Hᵢ`-eigenspaces inside the string -/

theorem StrT_inf_eigenspace_shift (i : Fin 8) (ν : Fin 8 → ℤ) (c : ℤ) :
    StrT N i ν ⊓ Module.End.eigenspace (deriv (N := N) (SerreH i))
      (((shift i ν c) i : ℤ) : ℂ) = TLwt N (shift i ν c) := by
  rw [StrT]
  rw [Commons.LinearAlgebra.End.iSup_inf_eigenspace_eq (f := deriv (N := N) (SerreH i))
    (lam := fun c : ℤ => (((shift i ν c) i : ℤ) : ℂ))
    (p := fun c : ℤ => TLwt N (shift i ν c)) ?_ ?_ c]
  · intro c c' h
    have h' : (shift i ν c) i = (shift i ν c') i := Int.cast_injective h
    rw [shift_apply_eigen, shift_apply_eigen] at h'
    omega
  · intro c x hx
    rw [Module.End.mem_eigenspace_iff]
    exact deriv_h_eq_of_mem_TLwt i hx

theorem StrT_inf_eigenspace (i : Fin 8) (ν : Fin 8 → ℤ) :
    StrT N i ν ⊓ Module.End.eigenspace (deriv (N := N) (SerreH i))
      (((ν i : ℤ)) : ℂ) = TLwt N ν := by
  have h := StrT_inf_eigenspace_shift (N := N) i ν 0
  simpa [shift_zero] using h

lemma sref_apply_self' (i : Fin 8) (ν : Fin 8 → ℤ) : sref i ν i = -(ν i) := by
  simp only [sref_apply, Submission.WeylWeights.E8, Int.cast_id]
  rw [E8diag]; ring

theorem StrT_inf_eigenspace_neg (i : Fin 8) (ν : Fin 8 → ℤ) :
    StrT N i ν ⊓ Module.End.eigenspace (deriv (N := N) (SerreH i))
      (-(((ν i : ℤ)) : ℂ)) = TLwt N (sref i ν) := by
  have h := StrT_inf_eigenspace_shift (N := N) i ν (-(ν i))
  rw [Submission.E8WInvariance.shift_neg, sref_apply_self'] at h
  simpa using h

/-! ## NOTE (SESSION 30): this file is SUPERSEDED — see `Submission/E8WinTensor.lean`

The statement this file was written to prove (`finrank ℂ ↥(TLwt N ν) = finrank ℂ ↥(TLwt N (sᵢν))`)
is now proved *without* any `𝔰𝔩₂` theory, by a convolution argument, in
`Submission/E8WinTensor.lean` (`finrank_TLwt_sref`, `finrank_TLwt_dc`).  The string machinery
below is correct and may still be useful (e.g. for other representation-theoretic inputs), but the
restricted-operator step is no longer on the critical path.

## What would have remained here (kept for the record)

The remaining steps of the mirror of `Submission.E8WInvariance` are

* `StrTH`, `StrTE`, `StrTF` — the restricted operators on `StrT`, and the `𝔰𝔩₂` commutation
  relations `StrT_sl2_1/2/3` (they follow from `deriv_lie` below);
* `deriv_e_localNilpotent` / `deriv_f_localNilpotent` on `T N` (from
  `Submission.E8LocallyNilpotent.e_locallyNilpotent` / `f_locallyNilpotent` via the Leibniz formula
  `(D)^n (a ⊗ b) = Σ_k C(n,k) u^k a ⊗ u^{n-k} b`, or, as done below, via the filtration
  `span {u^p a ⊗ u^q b : p + q = n}`);
* `StrTE_localNilpotent` / `StrTF_localNilpotent`;
* the equivalence `eigenspace StrTH μ ≃ StrT ⊓ eigenspace (deriv H_i) μ` and
  **`finrank_TLwt_sref : finrank (TLwt ν) = finrank (TLwt (sᵢν))`**.

⚠️ **The obstacle.**  These all typecheck up to the point where one forms
`Module.End ℂ ↥(StrT N i ν)` *products and differences*: typeclass search fails with

  `failed to synthesize HSub (Module.End ℂ ↥(StrT N i ν)) (Module.End ℂ ↥(StrT N i ν)) ?m`

even though the same code works verbatim in `Submission.E8WInvariance` for `↥(Str N i ν)` with
`Str N i ν : Submodule ℂ (V ⧸ N)`.  The difference is the tensor square: `T N` carries the extra
high-priority instances `instModT`/`instSMulT`/`instISTTensor` of `Submission.E8TensorBound`, and
the `Module ℂ` structure of `↥(StrT N i ν)` is apparently not recognised through them.  The fix is
presumably to pin the instances (e.g. by restating `StrT` with an explicit
`Module ℂ ↥(StrT N i ν)`/`Module.End ℂ ↥(StrT N i ν)` ascription, or by adding
`attribute [local instance] Submodule.module`), or to phrase the whole sl₂ argument on
`StrT N i ν` viewed as an abstract `ℂ`-module (via `Submodule.subtype` and `Submodule.comap`)
rather than on the subtype's `Module.End`.

The derivation rule `deriv_lie` (the only Lie-theoretic input, replacing the enveloping-algebra
commutators `commutator_H_E`/`commutator_H_F`/`commutator_E_F` used in `E8WInvariance`) is

  `deriv ⁅x,y⁆ = deriv x * deriv y - deriv y * deriv x`,

a direct consequence of the `LieRingModule` axiom for the tensor-product action.

-/

end Submission.E8WInvarianceT
