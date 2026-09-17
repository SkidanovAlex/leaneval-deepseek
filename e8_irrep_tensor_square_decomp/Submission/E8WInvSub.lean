import Submission.E8NilpT
import Submission.E8WInvarianceT
import Submission.E8WinTensor
import Submission.Commons.LinearAlgebra.End.iSup_inf_eigenspace_eq
import Submission.Commons.LinearAlgebra.End.sl2_eigenspace_finrank_symm

/-!
# `W`-invariance of the weight multiplicities of a submodule of the tensor square

`Submission.E8WInvariance` proves that the weight multiplicities of `L(ω₁+ω₈) = V ⧸ N` are
`W`-invariant, and `Submission.E8WinTensor` the same for the whole tensor square.  Here the same
`𝔰𝔩₂`-string argument is run for an **arbitrary `U(e₈)`-submodule `S ≤ T N`**, which is what makes
hypothesis (c) of `eq_of_freudenthal` available for the *actual* simple constituents of the
tensor square (`Submission/E8ConstChar.lean`).

For a `U`-submodule `S` the `αᵢ`-string through `ν` inside `S` is

  `StrS S i ν = ⨆ c : ℤ, (S ⊓ TLwt (ν + c αᵢ))`,

stable under `Hᵢ`, `Eᵢ`, `Fᵢ` (the `U`-submodule `S` is stable under the derivation action, and
`Eᵢ`/`Fᵢ` shift the weight by `±αᵢ`); its `Hᵢ`-eigenspaces are the single weight spaces
`S ⊓ TLwt (ν + c αᵢ)`, the restricted operators form an `𝔰𝔩₂`-triple, and they are locally
nilpotent because the ambient operators are (`Submission.E8NilpT`).  Hence
`Commons.LinearAlgebra.End.sl2_eigenspace_finrank_symm` gives

  **`finrank ℂ ↥(S ⊓ TLwt ν) = finrank ℂ ↥(S ⊓ TLwt (sᵢν))`**,

and, by the iterated dominant-conjugate algorithm `dc`,

  **`finrank ℂ ↥(S ⊓ TLwt ν) = finrank ℂ ↥(S ⊓ TLwt (dc ν))`**.
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

noncomputable section
open scoped BigOperators TensorProduct

namespace Submission.E8WInvSub

open Submission.E8Tensor Submission.E8TensorBound Submission.VermaWeight
open Submission.E8WeightSpaces
open Submission.E8Weights (e f h SerreE SerreF SerreH)
open Submission.WeylWeights (sref sref_apply)
open Submission.E8WInvariance (shift shift_zero shift_succ shift_pred shift_neg shift_apply_eigen
  E8symm E8diag)
open Submission.E8Orbit (dcl dcX dcX_eq_dc)
open UniversalEnvelopingAlgebra

variable {N : Submodule U V}

/-- The `ℂ`-linear endomorphisms of a `ℂ`-submodule of the tensor square form an additive
commutative group.  This is `LinearMap.addCommGroup`, declared explicitly because the instance
search is not usable on the tensor square (whose instances are heavily overridden). -/
instance instAddCommGroupEnd (P : Submodule ℂ (T N)) : AddCommGroup (Module.End ℂ ↥P) :=
  LinearMap.addCommGroup (R₁ := ℂ) (R₂ := ℂ) (M := ↥P) (N₂ := ↥P) (σ₁₂ := RingHom.id ℂ)

/-- The additive group structure on a `ℂ`-submodule of the tensor square, declared at high
priority: the instance search is unusable on the tensor square, and this makes the additive
structure on the subtype the canonical one (`AddCommGroup.toAddCommMonoid`), as expected by
`Module.End.eigenspace`. -/
@[reducible] instance (priority := 10000) instAddCommGroupSub (P : Submodule ℂ (T N)) :
    AddCommGroup ↥P := Submodule.addCommGroup P

/-- The additive monoid structure on a `ℂ`-submodule of the tensor square, taken through its
additive group structure. -/
@[reducible] instance (priority := 10000) instAddCommMonoidSub (P : Submodule ℂ (T N)) :
    AddCommMonoid ↥P := AddCommGroup.toAddCommMonoid

/-! ## The string of a submodule -/

/-- The `αᵢ`-string through `ν` inside the submodule `S`. -/
def StrS (S : Submodule U (T N)) (i : Fin 8) (ν : Fin 8 → ℤ) : Submodule ℂ (T N) :=
  ⨆ c : ℤ, (S.restrictScalars ℂ ⊓ TLwt N (shift i ν c))

lemma mem_StrS {S : Submodule U (T N)} {i : Fin 8} {ν : Fin 8 → ℤ} (c : ℤ) :
    S.restrictScalars ℂ ⊓ TLwt N (shift i ν c) ≤ StrS S i ν :=
  le_iSup (fun c : ℤ => S.restrictScalars ℂ ⊓ TLwt N (shift i ν c)) c

/-! ## Stability of the string under `Hᵢ`, `Eᵢ`, `Fᵢ` -/

theorem deriv_h_mem_StrS (S : Submodule U (T N)) (i : Fin 8) (ν : Fin 8 → ℤ) {c : ℤ}
    {x : T N} (hx : x ∈ S.restrictScalars ℂ ⊓ TLwt N (shift i ν c)) :
    deriv (N := N) (SerreH i) x ∈ S.restrictScalars ℂ ⊓ TLwt N (shift i ν c) := by
  obtain ⟨hxS, hxw⟩ := hx
  have h := deriv_h_eq_of_mem_TLwt (N := N) i hxw
  exact ⟨h ▸ Submodule.smul_mem _ _ hxS, h ▸ Submodule.smul_mem _ _ hxw⟩

theorem deriv_e_mem_StrS (S : Submodule U (T N)) (i : Fin 8) (ν : Fin 8 → ℤ) {c : ℤ}
    {x : T N} (hx : x ∈ S.restrictScalars ℂ ⊓ TLwt N (shift i ν c)) :
    deriv (N := N) (SerreE i) x
      ∈ S.restrictScalars ℂ ⊓ TLwt N (shift i ν (c + 1)) := by
  obtain ⟨hxS, hxw⟩ := hx
  have h : deriv (N := N) (SerreE i) x
      ∈ TLwt N (fun j => shift i ν c j + CartanMatrix.E₈ j i) :=
    Submission.E8WInvarianceT.deriv_e_apply_mem_TLwt i hxw
  rw [← shift_succ i ν c] at h
  refine ⟨?_, h⟩
  rw [show deriv (N := N) (SerreE i) x
    = (UniversalEnvelopingAlgebra.ι ℂ (SerreE i)) • x from
    (iota_smul_eq_deriv (N := N) (SerreE i) x).symm]
  exact S.smul_mem _ hxS

theorem deriv_f_mem_StrS (S : Submodule U (T N)) (i : Fin 8) (ν : Fin 8 → ℤ) {c : ℤ}
    {x : T N} (hx : x ∈ S.restrictScalars ℂ ⊓ TLwt N (shift i ν c)) :
    deriv (N := N) (SerreF i) x
      ∈ S.restrictScalars ℂ ⊓ TLwt N (shift i ν (c - 1)) := by
  obtain ⟨hxS, hxw⟩ := hx
  have h : deriv (N := N) (SerreF i) x
      ∈ TLwt N (fun j => shift i ν c j - CartanMatrix.E₈ j i) :=
    Submission.E8WInvarianceT.deriv_f_apply_mem_TLwt i hxw
  rw [← shift_pred i ν c] at h
  refine ⟨?_, h⟩
  rw [show deriv (N := N) (SerreF i) x
    = (UniversalEnvelopingAlgebra.ι ℂ (SerreF i)) • x from
    (iota_smul_eq_deriv (N := N) (SerreF i) x).symm]
  exact S.smul_mem _ hxS

theorem deriv_h_maps_StrS (S : Submodule U (T N)) (i : Fin 8) (ν : Fin 8 → ℤ) :
    Submodule.map (deriv (N := N) (SerreH i)) (StrS S i ν) ≤ StrS S i ν := by
  rw [StrS, Submodule.map_iSup]
  exact iSup_le fun c =>
    Submodule.map_le_iff_le_comap.mpr fun x hx => mem_StrS c (deriv_h_mem_StrS S i ν hx)

theorem deriv_e_maps_StrS (S : Submodule U (T N)) (i : Fin 8) (ν : Fin 8 → ℤ) :
    Submodule.map (deriv (N := N) (SerreE i)) (StrS S i ν) ≤ StrS S i ν := by
  rw [StrS, Submodule.map_iSup]
  exact iSup_le fun c =>
    Submodule.map_le_iff_le_comap.mpr fun x hx => mem_StrS (c + 1) (deriv_e_mem_StrS S i ν hx)

theorem deriv_f_maps_StrS (S : Submodule U (T N)) (i : Fin 8) (ν : Fin 8 → ℤ) :
    Submodule.map (deriv (N := N) (SerreF i)) (StrS S i ν) ≤ StrS S i ν := by
  rw [StrS, Submodule.map_iSup]
  exact iSup_le fun c =>
    Submodule.map_le_iff_le_comap.mpr fun x hx => mem_StrS (c - 1) (deriv_f_mem_StrS S i ν hx)

/-! ## The `Hᵢ`-eigenspaces inside the string -/

theorem StrS_inf_eigenspace_shift (S : Submodule U (T N)) (i : Fin 8) (ν : Fin 8 → ℤ) (c : ℤ) :
    StrS S i ν ⊓ Module.End.eigenspace (deriv (N := N) (SerreH i))
        ((((shift i ν c) i : ℤ)) : ℂ)
      = S.restrictScalars ℂ ⊓ TLwt N (shift i ν c) := by
  have hinj : Function.Injective (fun d : ℤ => (((shift i ν d) i : ℤ) : ℂ)) := by
    intro d d' hd
    have hd' : (shift i ν d) i = (shift i ν d') i := Int.cast_injective hd
    simp only [shift_apply_eigen, E8diag] at hd'
    omega
  have hp : ∀ d : ℤ, S.restrictScalars ℂ ⊓ TLwt N (shift i ν d) ≤
      Module.End.eigenspace (deriv (N := N) (SerreH i)) (((shift i ν d) i : ℤ) : ℂ) := by
    intro d x hx
    obtain ⟨_, hxw⟩ := hx
    rw [Module.End.mem_eigenspace_iff]
    exact deriv_h_eq_of_mem_TLwt (N := N) i hxw
  have h := Commons.LinearAlgebra.End.iSup_inf_eigenspace_eq
    (f := deriv (N := N) (SerreH i)) (lam := fun d : ℤ => (((shift i ν d) i : ℤ) : ℂ))
    hinj (fun d : ℤ => S.restrictScalars ℂ ⊓ TLwt N (shift i ν d)) hp c
  simpa [StrS] using h

theorem StrS_inf_eigenspace (S : Submodule U (T N)) (i : Fin 8) (ν : Fin 8 → ℤ) :
    StrS S i ν ⊓ Module.End.eigenspace (deriv (N := N) (SerreH i)) (((ν i : ℤ)) : ℂ)
      = S.restrictScalars ℂ ⊓ TLwt N ν := by
  have h := StrS_inf_eigenspace_shift S i ν 0
  rw [shift_zero] at h
  exact h

theorem StrS_inf_eigenspace_neg (S : Submodule U (T N)) (i : Fin 8) (ν : Fin 8 → ℤ) :
    StrS S i ν ⊓ Module.End.eigenspace (deriv (N := N) (SerreH i)) (-(((ν i : ℤ)) : ℂ))
      = S.restrictScalars ℂ ⊓ TLwt N (sref i ν) := by
  have h := StrS_inf_eigenspace_shift S i ν (-(ν i))
  rw [shift_neg i ν, Submission.WeylWeights.sref_apply_self] at h
  simpa using h

/-! ## The restricted operators on the string -/

/-- The restricted operator `x ↦ Hᵢx` on the string of `S`. -/
def StrSH (S : Submodule U (T N)) (i : Fin 8) (ν : Fin 8 → ℤ) :
    Module.End ℂ ↥(StrS S i ν) :=
  LinearMap.restrict (deriv (N := N) (SerreH i))
    (fun x hx => deriv_h_maps_StrS S i ν (Submodule.mem_map.mpr ⟨x, hx, rfl⟩))

/-- The restricted operator `x ↦ Eᵢx` on the string of `S`. -/
def StrSE (S : Submodule U (T N)) (i : Fin 8) (ν : Fin 8 → ℤ) :
    Module.End ℂ ↥(StrS S i ν) :=
  LinearMap.restrict (deriv (N := N) (SerreE i))
    (fun x hx => deriv_e_maps_StrS S i ν (Submodule.mem_map.mpr ⟨x, hx, rfl⟩))

/-- The restricted operator `x ↦ Fᵢx` on the string of `S`. -/
def StrSF (S : Submodule U (T N)) (i : Fin 8) (ν : Fin 8 → ℤ) :
    Module.End ℂ ↥(StrS S i ν) :=
  LinearMap.restrict (deriv (N := N) (SerreF i))
    (fun x hx => deriv_f_maps_StrS S i ν (Submodule.mem_map.mpr ⟨x, hx, rfl⟩))

/-! ## The ambient `𝔰𝔩₂`-relations on the tensor square -/

lemma deriv_eq_uEnd_iota (z : LieAlgebra.e₈ ℂ) :
    deriv (N := N) z = uEnd N (UniversalEnvelopingAlgebra.ι ℂ z) := by
  apply LinearMap.ext
  intro m
  show deriv (N := N) z m = uEnd N (UniversalEnvelopingAlgebra.ι ℂ z) m
  rw [show uEnd N (UniversalEnvelopingAlgebra.ι ℂ z) m
    = (UniversalEnvelopingAlgebra.ι ℂ z) • m from rfl, iota_smul_eq_deriv]

lemma two_zsmul_eq (y : Module.End ℂ (T N)) : ((2 : ℤ) • y) = (2 : ℂ) • y := by
  rw [← Int.cast_smul_eq_zsmul ℂ (2 : ℤ) y, show (((2 : ℤ) : ℂ)) = (2 : ℂ) by norm_num]

lemma uEnd_mul_sub (a b : U) :
    uEnd N a * uEnd N b - uEnd N b * uEnd N a = uEnd N (a * b - b * a) := by
  rw [map_sub, map_mul, map_mul]

theorem uEnd_sl2_1 (i : Fin 8) :
    uEnd N (UniversalEnvelopingAlgebra.ι ℂ (SerreH i))
        * uEnd N (UniversalEnvelopingAlgebra.ι ℂ (SerreE i))
      - uEnd N (UniversalEnvelopingAlgebra.ι ℂ (SerreE i))
        * uEnd N (UniversalEnvelopingAlgebra.ι ℂ (SerreH i))
      = (2 : ℂ) • uEnd N (UniversalEnvelopingAlgebra.ι ℂ (SerreE i)) := by
  have h2 : CartanMatrix.E₈ i i = 2 := by fin_cases i <;> decide
  have h := uEnd_mul_sub (N := N) (UniversalEnvelopingAlgebra.ι ℂ (SerreH i))
    (UniversalEnvelopingAlgebra.ι ℂ (SerreE i))
  rw [Submission.E8Weights.commutator_H_E i i, h2, map_zsmul] at h
  rw [← two_zsmul_eq (uEnd N (UniversalEnvelopingAlgebra.ι ℂ (SerreE i)))]
  exact h

theorem uEnd_sl2_2 (i : Fin 8) :
    uEnd N (UniversalEnvelopingAlgebra.ι ℂ (SerreH i))
        * uEnd N (UniversalEnvelopingAlgebra.ι ℂ (SerreF i))
      - uEnd N (UniversalEnvelopingAlgebra.ι ℂ (SerreF i))
        * uEnd N (UniversalEnvelopingAlgebra.ι ℂ (SerreH i))
      = -((2 : ℂ) • uEnd N (UniversalEnvelopingAlgebra.ι ℂ (SerreF i))) := by
  have h2 : CartanMatrix.E₈ i i = 2 := by fin_cases i <;> decide
  have h := uEnd_mul_sub (N := N) (UniversalEnvelopingAlgebra.ι ℂ (SerreH i))
    (UniversalEnvelopingAlgebra.ι ℂ (SerreF i))
  rw [Submission.E8Weights.commutator_H_F i i, h2, map_zsmul] at h
  rw [neg_zsmul] at h
  rw [← two_zsmul_eq (uEnd N (UniversalEnvelopingAlgebra.ι ℂ (SerreF i)))]
  exact h

theorem uEnd_sl2_3 (i : Fin 8) :
    uEnd N (UniversalEnvelopingAlgebra.ι ℂ (SerreE i))
        * uEnd N (UniversalEnvelopingAlgebra.ι ℂ (SerreF i))
      - uEnd N (UniversalEnvelopingAlgebra.ι ℂ (SerreF i))
        * uEnd N (UniversalEnvelopingAlgebra.ι ℂ (SerreE i))
      = uEnd N (UniversalEnvelopingAlgebra.ι ℂ (SerreH i)) := by
  have h := uEnd_mul_sub (N := N) (UniversalEnvelopingAlgebra.ι ℂ (SerreE i))
    (UniversalEnvelopingAlgebra.ι ℂ (SerreF i))
  rw [Submission.E8Weights.commutator_E_F i i, if_pos rfl] at h
  exact h

theorem deriv_h_e_rel (i : Fin 8) :
    deriv (N := N) (SerreH i) * deriv (N := N) (SerreE i)
      - deriv (N := N) (SerreE i) * deriv (N := N) (SerreH i)
      = (2 : ℂ) • deriv (N := N) (SerreE i) := by
  simp only [deriv_eq_uEnd_iota]
  exact uEnd_sl2_1 i

theorem deriv_h_f_rel (i : Fin 8) :
    deriv (N := N) (SerreH i) * deriv (N := N) (SerreF i)
      - deriv (N := N) (SerreF i) * deriv (N := N) (SerreH i)
      = -((2 : ℂ) • deriv (N := N) (SerreF i)) := by
  simp only [deriv_eq_uEnd_iota]
  exact uEnd_sl2_2 i

theorem deriv_e_f_rel (i : Fin 8) :
    deriv (N := N) (SerreE i) * deriv (N := N) (SerreF i)
      - deriv (N := N) (SerreF i) * deriv (N := N) (SerreE i)
      = deriv (N := N) (SerreH i) := by
  simp only [deriv_eq_uEnd_iota]
  exact uEnd_sl2_3 i

/-! ## The `𝔰𝔩₂`-relations on the string -/

theorem StrS_sl2_1 (S : Submodule U (T N)) (i : Fin 8) (ν : Fin 8 → ℤ) :
    StrSH S i ν * StrSE S i ν - StrSE S i ν * StrSH S i ν = (2 : ℂ) • StrSE S i ν := by
  ext x
  have h := congrArg (fun (F : Module.End ℂ (T N)) => F (x : T N)) (deriv_h_e_rel (N := N) i)
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.restrict_apply, Subtype.coe_mk, StrSH, StrSE] at h ⊢
  exact h

theorem StrS_sl2_2 (S : Submodule U (T N)) (i : Fin 8) (ν : Fin 8 → ℤ) :
    StrSH S i ν * StrSF S i ν - StrSF S i ν * StrSH S i ν = -((2 : ℂ) • StrSF S i ν) := by
  ext x
  have h := congrArg (fun (F : Module.End ℂ (T N)) => F (x : T N)) (deriv_h_f_rel (N := N) i)
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.restrict_apply, Subtype.coe_mk, StrSH, StrSF] at h ⊢
  exact h

theorem StrS_sl2_3 (S : Submodule U (T N)) (i : Fin 8) (ν : Fin 8 → ℤ) :
    StrSE S i ν * StrSF S i ν - StrSF S i ν * StrSE S i ν = StrSH S i ν := by
  ext x
  have h := congrArg (fun (F : Module.End ℂ (T N)) => F (x : T N)) (deriv_e_f_rel (N := N) i)
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.restrict_apply, Subtype.coe_mk, StrSH, StrSE, StrSF] at h ⊢
  exact h

/-! ## Local nilpotence of the restricted operators -/

lemma StrSE_pow_coe (S : Submodule U (T N)) (i : Fin 8) (ν : Fin 8 → ℤ) (n : ℕ)
    (x : ↥(StrS S i ν)) :
    (((StrSE S i ν)^n) x : T N) = ((deriv (N := N) (SerreE i))^n) (x : T N) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply]
      show deriv (N := N) (SerreE i) ((((StrSE S i ν)^n) x : ↥(StrS S i ν)) : T N)
        = deriv (N := N) (SerreE i) (((deriv (N := N) (SerreE i))^n) (x : T N))
      rw [ih]

lemma StrSE_localNilpotent (S : Submodule U (T N)) (i : Fin 8) (ν : Fin 8 → ℤ)
    (x : ↥(StrS S i ν)) : ∃ n : ℕ, ((StrSE S i ν)^n) x = 0 := by
  obtain ⟨n, hn⟩ := Submission.E8NilpT.deriv_e_locallyNilpotent N i (x : T N)
  exact ⟨n, Subtype.ext (by rw [StrSE_pow_coe]; exact hn)⟩

lemma StrSF_pow_coe (S : Submodule U (T N)) (i : Fin 8) (ν : Fin 8 → ℤ) (n : ℕ)
    (x : ↥(StrS S i ν)) :
    (((StrSF S i ν)^n) x : T N) = ((deriv (N := N) (SerreF i))^n) (x : T N) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply]
      show deriv (N := N) (SerreF i) ((((StrSF S i ν)^n) x : ↥(StrS S i ν)) : T N)
        = deriv (N := N) (SerreF i) (((deriv (N := N) (SerreF i))^n) (x : T N))
      rw [ih]

lemma StrSF_localNilpotent (S : Submodule U (T N)) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) (i : Fin 8) (ν : Fin 8 → ℤ)
    (x : ↥(StrS S i ν)) : ∃ n : ℕ, ((StrSF S i ν)^n) x = 0 := by
  obtain ⟨n, hn⟩ := Submission.E8NilpT.deriv_f_locallyNilpotent N hvN hmax i (x : T N)
  exact ⟨n, Subtype.ext (by rw [StrSF_pow_coe]; exact hn)⟩

/-! ## The eigenspaces of the string and the weight spaces -/

/-- **The `𝔰𝔩₂` symmetry in kernel form.** -/
theorem sl2_ker_symm {V : Type*} [AddCommGroup V] [Module ℂ V] (h e f : Module.End ℂ V)
    (hhe : h * e - e * h = (2 : ℂ) • e) (hhf : h * f - f * h = -((2 : ℂ) • f))
    (hef : e * f - f * e = h)
    (he : ∀ v : V, ∃ n : ℕ, (e^n) v = 0) (hf : ∀ v : V, ∃ n : ℕ, (f^n) v = 0) (μ : ℂ) :
    Module.finrank ℂ ↥(LinearMap.ker (h - μ • 1))
      = Module.finrank ℂ ↥(LinearMap.ker (h - (-μ) • 1)) := by
  have h1 := Commons.LinearAlgebra.End.sl2_eigenspace_finrank_symm h e f hhe hhf hef he hf μ
  rw [Module.End.eigenspace_def, Module.End.eigenspace_def] at h1
  exact h1

/-- The eigenspace of the restricted Cartan operator, as a linear equivalence with the
corresponding part of the string. -/
noncomputable def kerEquiv (S : Submodule U (T N)) (i : Fin 8) (ν : Fin 8 → ℤ) (μ : ℂ) :
    ↥(LinearMap.ker (StrSH S i ν - μ • 1)) ≃ₗ[ℂ]
      ↥(StrS S i ν ⊓ LinearMap.ker (deriv (N := N) (SerreH i) - μ • 1)) where
  toFun x := ⟨(x.1 : T N), ⟨x.1.2, by
    have hx := LinearMap.mem_ker.mp x.2
    refine LinearMap.mem_ker.mpr ?_
    simpa [StrSH, LinearMap.restrict_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, Submodule.coe_mk] using
        congrArg (fun z : ↥(StrS S i ν) => (z : T N)) hx⟩⟩
  invFun y := ⟨⟨(y.1 : T N), y.2.1⟩, by
    apply Subtype.ext
    have hy : (deriv (N := N) (SerreH i)) (y.1 : T N) - μ • (y.1 : T N) = 0 :=
      LinearMap.mem_ker.mp y.2.2
    show (deriv (N := N) (SerreH i)) (y.1 : T N) - μ • (y.1 : T N) = 0
    exact hy⟩
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl
  map_add' x y := by ext; rfl
  map_smul' c x := by ext; rfl

lemma ker_finrank_eq (S : Submodule U (T N)) (i : Fin 8) (ν : Fin 8 → ℤ) (μ : ℂ) :
    Module.finrank ℂ ↥(LinearMap.ker (StrSH S i ν - μ • 1))
      = Module.finrank ℂ ↥(StrS S i ν ⊓ LinearMap.ker (deriv (N := N) (SerreH i) - μ • 1)) :=
  LinearEquiv.finrank_eq (kerEquiv S i ν μ)

/-- **`W`-invariance (infinitesimal form) for a `U`-submodule of the tensor square.** -/
theorem finrank_inf_TLwt_sref (S : Submodule U (T N)) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) (i : Fin 8) (ν : Fin 8 → ℤ) :
    Module.finrank ℂ ↥(S.restrictScalars ℂ ⊓ TLwt N ν)
      = Module.finrank ℂ ↥(S.restrictScalars ℂ ⊓ TLwt N (sref i ν)) := by
  have hsl2 := sl2_ker_symm (StrSH S i ν) (StrSE S i ν) (StrSF S i ν) (StrS_sl2_1 S i ν)
    (StrS_sl2_2 S i ν) (StrS_sl2_3 S i ν) (StrSE_localNilpotent S i ν)
    (StrSF_localNilpotent S hvN hmax i ν) (((ν i : ℤ)) : ℂ)
  rw [ker_finrank_eq S i ν (((ν i : ℤ)) : ℂ),
    show StrS S i ν ⊓ LinearMap.ker (deriv (N := N) (SerreH i) - (((ν i : ℤ)) : ℂ) • 1)
      = S.restrictScalars ℂ ⊓ TLwt N ν from by
        rw [← Module.End.eigenspace_def]; exact StrS_inf_eigenspace S i ν,
    ker_finrank_eq S i ν (-(((ν i : ℤ)) : ℂ)),
    show StrS S i ν ⊓ LinearMap.ker (deriv (N := N) (SerreH i) - (-(((ν i : ℤ)) : ℂ)) • 1)
      = S.restrictScalars ℂ ⊓ TLwt N (sref i ν) from by
        rw [← Module.End.eigenspace_def]; exact StrS_inf_eigenspace_neg S i ν] at hsl2
  exact hsl2

/-- The same invariance for the iterated dominant-conjugate algorithm `dcl`. -/
lemma finrank_inf_TLwt_dcl (S : Submodule U (T N)) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) (n : ℕ) (ν : Fin 8 → ℤ) :
    Module.finrank ℂ ↥(S.restrictScalars ℂ ⊓ TLwt N ν)
      = Module.finrank ℂ ↥(S.restrictScalars ℂ ⊓ TLwt N (dcl n ν)) := by
  induction n generalizing ν with
  | zero => rfl
  | succ n ih =>
      rw [dcl]
      split
      · rename_i i _
        rw [finrank_inf_TLwt_sref S hvN hmax i ν, ih (sref i ν)]
      · rfl

/-- **`W`-invariance of the weight multiplicities of a `U`-submodule of the tensor square, in
the form needed by `eq_of_freudenthal`.** -/
theorem finrank_inf_TLwt_dc (S : Submodule U (T N)) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) (ν : Fin 8 → ℤ) :
    Module.finrank ℂ ↥(S.restrictScalars ℂ ⊓ TLwt N ν)
      = Module.finrank ℂ ↥(S.restrictScalars ℂ ⊓ TLwt N (Submission.E8Character.dc ν)) := by
  have h := finrank_inf_TLwt_dcl S hvN hmax 130 ν
  rwa [show dcl 130 ν = dcX ν from rfl, dcX_eq_dc] at h

end Submission.E8WInvSub
