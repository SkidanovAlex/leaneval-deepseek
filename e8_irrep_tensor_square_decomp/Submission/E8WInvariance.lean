import Submission.E8WeightSpaces
import Submission.WeylWeights
import Submission.Commons.LinearAlgebra.End.iSup_inf_eigenspace_eq
import Submission.Commons.LinearAlgebra.End.sl2_eigenspace_finrank_symm

/-!
# `W`-invariance of the weight multiplicities of `L(ω₁+ω₈)`

The character of the irreducible quotient `L = V ⧸ N` is invariant under the Weyl group.  This
file proves the infinitesimal version of that statement: for every weight `ν` and every simple
reflection `sᵢ`, the multiplicities of `ν` and of `sᵢν` agree.

The argument is the classical one:

* `Str i ν = ⨆ c : ℤ, Lwt (ν + c αᵢ)` is the `αᵢ`-string through `ν`, stable under `eᵢ`, `fᵢ` and
  `Hᵢ` (`endU_e_mem_Str`, `endU_f_mem_Str`, `endU_h_mem_Str`);
* the `Hᵢ`-eigenspaces inside the string are single weight spaces:
  `Str ⊓ eigenspace (Hᵢ) (νᵢ + 2c) = Lwt (ν + c αᵢ)`, which is the general lemma
  `Commons.LinearAlgebra.End.iSup_inf_eigenspace_eq` applied to the independent family of the
  `Lwt`-spaces;
* `Commons.LinearAlgebra.End.sl2_eigenspace_finrank_symm` applied to the string (with the
  restricted operators) therefore gives
  `finrank (Lwt ν) = finrank (Lwt (sᵢν))`.

Consequently the multiplicity function `ν ↦ finrank (Lwt N ν)` is invariant under every element of
the Weyl group, in particular under the dominant conjugate `dcX`.
-/

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

noncomputable section
open scoped BigOperators

namespace Submission.E8WInvariance

open Submission.StarModule (wordElt Eword)
open Submission.StarQuotient (Hbar Ebar Lbar J V)
open Submission.VermaWeight
open Submission.E8WeightSpaces
open Submission.WeylWeights (sref sref_apply)

variable (N : Submodule U V)

/-! ## The `αᵢ`-string through a weight -/

lemma E8symm (i j : Fin 8) : CartanMatrix.E₈ i j = CartanMatrix.E₈ j i := by
  fin_cases i <;> fin_cases j <;> decide

lemma E8diag (i : Fin 8) : CartanMatrix.E₈ i i = 2 := by fin_cases i <;> decide

/-- The shift of the weight `ν` by `c` copies of the root `αᵢ`. -/
def shift (i : Fin 8) (ν : Fin 8 → ℤ) (c : ℤ) : Fin 8 → ℤ :=
  fun j => ν j + c * CartanMatrix.E₈ j i

lemma shift_zero (i : Fin 8) (ν : Fin 8 → ℤ) : shift i ν 0 = ν := by
  funext j; simp [shift]

lemma shift_neg (i : Fin 8) (ν : Fin 8 → ℤ) : shift i ν (-(ν i)) = sref i ν := by
  funext j
  simp only [shift, sref_apply, Submission.WeylWeights.E8, Int.cast_id]
  rw [← E8symm i j]
  ring

lemma shift_neg_apply (i : Fin 8) (ν : Fin 8 → ℤ) :
    (shift i ν (-(ν i))) i = -(ν i) := by
  simp only [shift]
  rw [E8diag]
  ring

lemma shift_succ (i : Fin 8) (ν : Fin 8 → ℤ) (c : ℤ) :
    shift i ν (c + 1) = fun j => shift i ν c j + CartanMatrix.E₈ j i := by
  funext j; simp only [shift]; ring

lemma shift_pred (i : Fin 8) (ν : Fin 8 → ℤ) (c : ℤ) :
    shift i ν (c - 1) = fun j => shift i ν c j - CartanMatrix.E₈ j i := by
  funext j; simp only [shift]; ring

lemma shift_apply_eigen (i : Fin 8) (ν : Fin 8 → ℤ) (c : ℤ) :
    (shift i ν c) i = ν i + 2 * c := by
  simp only [shift]
  rw [E8diag]
  ring

/-- The `αᵢ`-string through `ν`: the sum of the weight spaces `ν + cαᵢ`. -/
def Str (i : Fin 8) (ν : Fin 8 → ℤ) : Submodule ℂ (V ⧸ N) :=
  ⨆ c : ℤ, Lwt N (shift i ν c)

lemma Lwt_le_Str (i : Fin 8) (ν : Fin 8 → ℤ) (c : ℤ) : Lwt N (shift i ν c) ≤ Str N i ν :=
  le_iSup (fun c : ℤ => Lwt N (shift i ν c)) c

lemma Lwt_le_Str_zero (i : Fin 8) (ν : Fin 8 → ℤ) : Lwt N ν ≤ Str N i ν := by
  simpa [shift_zero] using Lwt_le_Str N i ν 0

/-! ## Stability of the string under `eᵢ`, `fᵢ`, `Hᵢ` -/

theorem endU_e_maps_Str (i : Fin 8) (ν : Fin 8 → ℤ) :
    Submodule.map (endU N (Submission.E8Weights.e i)) (Str N i ν) ≤ Str N i ν := by
  rw [Str, Submodule.map_iSup]
  refine iSup_le fun c => ?_
  refine Submodule.map_le_iff_le_comap.mpr fun x hx => ?_
  have h := endU_e_apply_mem_Lwt N i hx
  rw [← shift_succ] at h
  exact le_iSup (fun c : ℤ => Lwt N (shift i ν c)) (c + 1) h

theorem endU_f_maps_Str (i : Fin 8) (ν : Fin 8 → ℤ) :
    Submodule.map (endU N (Submission.E8Weights.f i)) (Str N i ν) ≤ Str N i ν := by
  rw [Str, Submodule.map_iSup]
  refine iSup_le fun c => ?_
  refine Submodule.map_le_iff_le_comap.mpr fun x hx => ?_
  have h := endU_f_apply_mem_Lwt N i hx
  rw [← shift_pred] at h
  exact le_iSup (fun c : ℤ => Lwt N (shift i ν c)) (c - 1) h

theorem endU_h_maps_Str (i : Fin 8) (ν : Fin 8 → ℤ) :
    Submodule.map (endU N (Submission.E8Weights.h i)) (Str N i ν) ≤ Str N i ν := by
  rw [Str, Submodule.map_iSup]
  refine iSup_le fun c => ?_
  refine Submodule.map_le_iff_le_comap.mpr fun x hx => ?_
  have hx' : endU N (Submission.E8Weights.h i) x = ((((shift i ν c) i : ℤ) : ℂ)) • x :=
    (mem_Lwt_iff.mp hx) i
  refine le_iSup (fun c : ℤ => Lwt N (shift i ν c)) c ?_
  rw [hx']
  exact Submodule.smul_mem _ _ hx

theorem endU_e_mem_Str (i : Fin 8) (ν : Fin 8 → ℤ) {x : V ⧸ N} (hx : x ∈ Str N i ν) :
    endU N (Submission.E8Weights.e i) x ∈ Str N i ν :=
  endU_e_maps_Str N i ν (Submodule.mem_map.mpr ⟨x, hx, rfl⟩)

theorem endU_f_mem_Str (i : Fin 8) (ν : Fin 8 → ℤ) {x : V ⧸ N} (hx : x ∈ Str N i ν) :
    endU N (Submission.E8Weights.f i) x ∈ Str N i ν :=
  endU_f_maps_Str N i ν (Submodule.mem_map.mpr ⟨x, hx, rfl⟩)

theorem endU_h_mem_Str (i : Fin 8) (ν : Fin 8 → ℤ) {x : V ⧸ N} (hx : x ∈ Str N i ν) :
    endU N (Submission.E8Weights.h i) x ∈ Str N i ν :=
  endU_h_maps_Str N i ν (Submodule.mem_map.mpr ⟨x, hx, rfl⟩)

/-! ## The `Hᵢ`-eigenspaces inside the string -/

theorem Str_inf_eigenspace_shift (i : Fin 8) (ν : Fin 8 → ℤ) (c : ℤ) :
    Str N i ν ⊓ Module.End.eigenspace (endU N (Submission.E8Weights.h i))
      (((shift i ν c) i : ℤ) : ℂ) = Lwt N (shift i ν c) := by
  rw [Str]
  rw [Commons.LinearAlgebra.End.iSup_inf_eigenspace_eq (f := endU N (Submission.E8Weights.h i))
    (lam := fun c : ℤ => (((shift i ν c) i : ℤ) : ℂ))
    (p := fun c : ℤ => Lwt N (shift i ν c)) ?_ ?_ c]
  · intro c c' h
    have h' : (shift i ν c) i = (shift i ν c') i := Int.cast_injective h
    rw [shift_apply_eigen, shift_apply_eigen] at h'
    omega
  · intro c x hx
    rw [Module.End.mem_eigenspace_iff]
    exact (mem_Lwt_iff.mp hx) i

theorem Str_inf_eigenspace (i : Fin 8) (ν : Fin 8 → ℤ) :
    Str N i ν ⊓ Module.End.eigenspace (endU N (Submission.E8Weights.h i))
      (((ν i : ℤ)) : ℂ) = Lwt N ν := by
  have h := Str_inf_eigenspace_shift N i ν 0
  simpa [shift_zero] using h

lemma sref_apply_self (i : Fin 8) (ν : Fin 8 → ℤ) : sref i ν i = -(ν i) := by
  simp only [sref_apply, Submission.WeylWeights.E8, Int.cast_id]
  rw [E8diag]
  ring

theorem Str_inf_eigenspace_neg (i : Fin 8) (ν : Fin 8 → ℤ) :
    Str N i ν ⊓ Module.End.eigenspace (endU N (Submission.E8Weights.h i))
      (-(((ν i : ℤ)) : ℂ)) = Lwt N (sref i ν) := by
  have h := Str_inf_eigenspace_shift N i ν (-(ν i))
  rw [shift_neg, sref_apply_self] at h
  simpa using h

/-! ## The restricted operators on the string and the `𝔰𝔩₂` relations -/

/-! ## The restricted operators on the string and the `𝔰𝔩₂` relations -/

/-- The restricted operator `x ↦ Hᵢx` on the string. -/
def StrH (N : Submodule U V) (i : Fin 8) (ν : Fin 8 → ℤ) : Module.End ℂ ↥(Str N i ν) :=
  LinearMap.restrict (endU N (Submission.E8Weights.h i)) (fun x hx => endU_h_mem_Str N i ν hx)

/-- The restricted operator `x ↦ Eᵢx` on the string. -/
def StrE (N : Submodule U V) (i : Fin 8) (ν : Fin 8 → ℤ) : Module.End ℂ ↥(Str N i ν) :=
  LinearMap.restrict (endU N (Submission.E8Weights.e i)) (fun x hx => endU_e_mem_Str N i ν hx)

/-- The restricted operator `x ↦ Fᵢx` on the string. -/
def StrF (N : Submodule U V) (i : Fin 8) (ν : Fin 8 → ℤ) : Module.End ℂ ↥(Str N i ν) :=
  LinearMap.restrict (endU N (Submission.E8Weights.f i)) (fun x hx => endU_f_mem_Str N i ν hx)

lemma endU_smul (N : Submodule U V) (c : ℂ) (u : U) : endU N (c • u) = c • endU N u := by
  ext x
  simp only [endU_apply, LinearMap.smul_apply]
  exact IsScalarTower.smul_assoc c u x

lemma endU_zsmul (N : Submodule U V) (n : ℤ) (u : U) :
    endU N (n • u) = (((n : ℤ)) : ℂ) • endU N u := by
  ext x
  simp only [endU_apply, LinearMap.smul_apply]
  rw [← Int.cast_smul_eq_zsmul ℂ n u, smul_assoc]

lemma endU_pow (N : Submodule U V) (u : U) (n : ℕ) : endU N (u^n) = (endU N u)^n := by
  induction n with
  | zero => ext x; simp
  | succ n ih => rw [pow_succ, endU_mul, ih, pow_succ]

lemma endU_h_e_rel (N : Submodule U V) (i : Fin 8) :
    endU N (Submission.E8Weights.h i) * endU N (Submission.E8Weights.e i)
      - endU N (Submission.E8Weights.e i) * endU N (Submission.E8Weights.h i)
      = (2 : ℂ) • endU N (Submission.E8Weights.e i) := by
  have h := Submission.E8Weights.commutator_H_E i i
  rw [E8diag] at h
  calc endU N (Submission.E8Weights.h i) * endU N (Submission.E8Weights.e i)
        - endU N (Submission.E8Weights.e i) * endU N (Submission.E8Weights.h i)
      = endU N (Submission.E8Weights.h i * Submission.E8Weights.e i
          - Submission.E8Weights.e i * Submission.E8Weights.h i) := by
        rw [endU_sub, endU_mul, endU_mul]
    _ = endU N ((2 : ℤ) • Submission.E8Weights.e i) := congrArg (endU N) h
    _ = (2 : ℂ) • endU N (Submission.E8Weights.e i) := by
        rw [endU_zsmul N (2 : ℤ) (Submission.E8Weights.e i)]
        norm_num

lemma endU_h_f_rel (N : Submodule U V) (i : Fin 8) :
    endU N (Submission.E8Weights.h i) * endU N (Submission.E8Weights.f i)
      - endU N (Submission.E8Weights.f i) * endU N (Submission.E8Weights.h i)
      = -((2 : ℂ) • endU N (Submission.E8Weights.f i)) := by
  have h := Submission.E8Weights.commutator_H_F i i
  rw [E8diag] at h
  calc endU N (Submission.E8Weights.h i) * endU N (Submission.E8Weights.f i)
        - endU N (Submission.E8Weights.f i) * endU N (Submission.E8Weights.h i)
      = endU N (Submission.E8Weights.h i * Submission.E8Weights.f i
          - Submission.E8Weights.f i * Submission.E8Weights.h i) := by
        rw [endU_sub, endU_mul, endU_mul]
    _ = endU N ((-(2 : ℤ)) • Submission.E8Weights.f i) := congrArg (endU N) h
    _ = (-(2 : ℂ)) • endU N (Submission.E8Weights.f i) := by
        rw [endU_zsmul N (-(2 : ℤ)) (Submission.E8Weights.f i)]
        norm_num
    _ = -((2 : ℂ) • endU N (Submission.E8Weights.f i)) :=
        neg_smul (2 : ℂ) (endU N (Submission.E8Weights.f i))

lemma endU_e_f_rel (N : Submodule U V) (i : Fin 8) :
    endU N (Submission.E8Weights.e i) * endU N (Submission.E8Weights.f i)
      - endU N (Submission.E8Weights.f i) * endU N (Submission.E8Weights.e i)
      = endU N (Submission.E8Weights.h i) := by
  have h := Submission.E8Weights.commutator_E_F i i
  rw [if_pos rfl] at h
  calc endU N (Submission.E8Weights.e i) * endU N (Submission.E8Weights.f i)
        - endU N (Submission.E8Weights.f i) * endU N (Submission.E8Weights.e i)
      = endU N (Submission.E8Weights.e i * Submission.E8Weights.f i
          - Submission.E8Weights.f i * Submission.E8Weights.e i) := by
        rw [endU_sub, endU_mul, endU_mul]
    _ = endU N (Submission.E8Weights.h i) := congrArg (endU N) h

lemma Str_sl2_1 (N : Submodule U V) (i : Fin 8) (ν : Fin 8 → ℤ) :
    StrH N i ν * StrE N i ν - StrE N i ν * StrH N i ν = (2 : ℂ) • StrE N i ν := by
  ext x
  have h := congrArg (fun (F : Module.End ℂ (V ⧸ N)) => F (x : V ⧸ N)) (endU_h_e_rel N i)
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.restrict_apply, Subtype.coe_mk, StrH, StrE] at h ⊢
  exact h

lemma Str_sl2_2 (N : Submodule U V) (i : Fin 8) (ν : Fin 8 → ℤ) :
    StrH N i ν * StrF N i ν - StrF N i ν * StrH N i ν = -((2 : ℂ) • StrF N i ν) := by
  ext x
  have h := congrArg (fun (F : Module.End ℂ (V ⧸ N)) => F (x : V ⧸ N)) (endU_h_f_rel N i)
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.restrict_apply, Subtype.coe_mk, StrH, StrF] at h ⊢
  exact h

lemma Str_sl2_3 (N : Submodule U V) (i : Fin 8) (ν : Fin 8 → ℤ) :
    StrE N i ν * StrF N i ν - StrF N i ν * StrE N i ν = StrH N i ν := by
  ext x
  have h := congrArg (fun (F : Module.End ℂ (V ⧸ N)) => F (x : V ⧸ N)) (endU_e_f_rel N i)
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.restrict_apply, Subtype.coe_mk, StrH, StrE, StrF] at h ⊢
  exact h

lemma StrE_pow_coe (N : Submodule U V) (i : Fin 8) (ν : Fin 8 → ℤ) (n : ℕ)
    (x : ↥(Str N i ν)) :
    (((StrE N i ν)^n) x : V ⧸ N) = ((endU N (Submission.E8Weights.e i))^n) (x : V ⧸ N) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      have h1 : ((StrE N i ν)^(n+1)) x = (StrE N i ν) (((StrE N i ν)^n) x) := by
        rw [pow_succ', Module.End.mul_apply]
      have h2 : ((endU N (Submission.E8Weights.e i))^(n+1)) (x : V ⧸ N)
          = endU N (Submission.E8Weights.e i)
            (((endU N (Submission.E8Weights.e i))^n) (x : V ⧸ N)) := by
        rw [pow_succ', Module.End.mul_apply]
      have h3 : (((StrE N i ν) (((StrE N i ν)^n) x) : V ⧸ N))
          = endU N (Submission.E8Weights.e i)
            ((((StrE N i ν)^n) x : ↥(Str N i ν)) : V ⧸ N) := rfl
      rw [h1, h2, h3, ih]

lemma StrF_pow_coe (N : Submodule U V) (i : Fin 8) (ν : Fin 8 → ℤ) (n : ℕ)
    (x : ↥(Str N i ν)) :
    (((StrF N i ν)^n) x : V ⧸ N) = ((endU N (Submission.E8Weights.f i))^n) (x : V ⧸ N) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      have h1 : ((StrF N i ν)^(n+1)) x = (StrF N i ν) (((StrF N i ν)^n) x) := by
        rw [pow_succ', Module.End.mul_apply]
      have h2 : ((endU N (Submission.E8Weights.f i))^(n+1)) (x : V ⧸ N)
          = endU N (Submission.E8Weights.f i)
            (((endU N (Submission.E8Weights.f i))^n) (x : V ⧸ N)) := by
        rw [pow_succ', Module.End.mul_apply]
      have h3 : (((StrF N i ν) (((StrF N i ν)^n) x) : V ⧸ N))
          = endU N (Submission.E8Weights.f i)
            ((((StrF N i ν)^n) x : ↥(Str N i ν)) : V ⧸ N) := rfl
      rw [h1, h2, h3, ih]

lemma StrE_localNilpotent (N : Submodule U V) (i : Fin 8) (ν : Fin 8 → ℤ)
    (x : ↥(Str N i ν)) : ∃ n : ℕ, ((StrE N i ν)^n) x = 0 := by
  obtain ⟨n, hn⟩ := Submission.E8LocallyNilpotent.e_locallyNilpotent N i (x : V ⧸ N)
  refine ⟨n, ?_⟩
  apply Subtype.ext
  rw [StrE_pow_coe, ← endU_pow, endU_apply]
  exact hn

lemma StrF_localNilpotent (N : Submodule U V) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) (i : Fin 8) (ν : Fin 8 → ℤ)
    (x : ↥(Str N i ν)) : ∃ n : ℕ, ((StrF N i ν)^n) x = 0 := by
  obtain ⟨n, hn⟩ := Submission.E8LocallyNilpotent.f_locallyNilpotent N hvN hmax i (x : V ⧸ N)
  refine ⟨n, ?_⟩
  apply Subtype.ext
  rw [StrF_pow_coe, ← endU_pow, endU_apply]
  exact hn

/-! ## The eigenspaces of the string and the weight spaces -/

noncomputable def eigenspaceEquiv (N : Submodule U V) (i : Fin 8) (ν : Fin 8 → ℤ) (μ : ℂ) :
    ↥(Module.End.eigenspace (StrH N i ν) μ) ≃ₗ[ℂ]
      ↥(Str N i ν ⊓ Module.End.eigenspace (endU N (Submission.E8Weights.h i)) μ) where
  toFun x := ⟨(x.1 : V ⧸ N), ⟨x.1.2, by
    refine Module.End.mem_eigenspace_iff.mpr ?_
    have h := congrArg (fun z : ↥(Str N i ν) => (z : V ⧸ N))
      (Module.End.mem_eigenspace_iff.mp x.2)
    simpa [StrH, LinearMap.restrict_apply, Submodule.coe_mk] using h⟩⟩
  invFun y := ⟨⟨(y.1 : V ⧸ N), y.2.1⟩, by
    refine Module.End.mem_eigenspace_iff.mpr ?_
    apply Subtype.ext
    exact (Module.End.mem_eigenspace_iff.mp y.2.2)⟩
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl
  map_add' x y := by ext; rfl
  map_smul' c x := by ext; rfl

lemma eigenspace_finrank_eq (N : Submodule U V) (i : Fin 8) (ν : Fin 8 → ℤ) (μ : ℂ) :
    Module.finrank ℂ ↥(Module.End.eigenspace (StrH N i ν) μ)
      = Module.finrank ℂ
        ↥(Str N i ν ⊓ Module.End.eigenspace (endU N (Submission.E8Weights.h i)) μ) :=
  LinearEquiv.finrank_eq (eigenspaceEquiv N i ν μ)

/-! ## `W`-invariance of the weight multiplicities -/

/-- **`W`-invariance (infinitesimal form):** the multiplicity of the weight `ν` equals that of
its reflection `sᵢν`. -/
theorem finrank_Lwt_sref (N : Submodule U V) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) (i : Fin 8) (ν : Fin 8 → ℤ) :
    Module.finrank ℂ ↥(Lwt N ν) = Module.finrank ℂ ↥(Lwt N (sref i ν)) := by
  have hsl2 := Commons.LinearAlgebra.End.sl2_eigenspace_finrank_symm (StrH N i ν) (StrE N i ν)
    (StrF N i ν) (Str_sl2_1 N i ν) (Str_sl2_2 N i ν) (Str_sl2_3 N i ν)
    (StrE_localNilpotent N i ν) (StrF_localNilpotent N hvN hmax i ν) (((ν i : ℤ)) : ℂ)
  rw [eigenspace_finrank_eq N i ν (((ν i : ℤ)) : ℂ), Str_inf_eigenspace N i ν,
    eigenspace_finrank_eq N i ν (-(((ν i : ℤ)) : ℂ)), Str_inf_eigenspace_neg N i ν] at hsl2
  exact hsl2

end Submission.E8WInvariance
