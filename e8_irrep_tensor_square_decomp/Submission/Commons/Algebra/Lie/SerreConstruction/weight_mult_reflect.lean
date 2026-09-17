import Mathlib
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_zero_weightSpace_finrank
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_weightSpace_reflect_finrank
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_stab_rho_trivial
import Submission.Commons.LinearAlgebra.End.sl2_eigenspace_finrank_symm
import Submission.Commons.LinearAlgebra.End.iSup_inf_eigenspace_eq

/-!
# Reflection invariance of the weight multiplicities of an `e₈`-module

For a finite-dimensional module `M` over the Serre-constructed `e₈` (`L8`), the multiplicity of a
weight `μ` (the dimension of the joint eigenspace of the `SerreH j`) equals that of its reflection
`sᵢμ` at any simple root `i`, where

`(sᵢμ)ⱼ = μⱼ - μᵢ A_{ij}`.

This is the infinitesimal form of the classical statement that the character of a
finite-dimensional representation is invariant under the Weyl group.

The proof follows the standard `𝔰𝔩₂` argument (as in `Submission.E8WInvariance` for the specific
highest weight module `L(ω₁+ω₈)`), now for an *arbitrary* finite-dimensional module:

* `Str i ν = ⨆_{c : ℤ} Mwt (ν + c αᵢ)` is the `αᵢ`-string through `ν`; it is stable under `Eᵢ`,
  `Fᵢ` and `Hᵢ`;
* inside the string the `Hᵢ`-eigenspaces are exactly the joint weight spaces
  (`Str ⊓ eigenspace Hᵢ (νᵢ + 2c) = Mwt (ν + c αᵢ)`, from
  `Commons.LinearAlgebra.End.iSup_inf_eigenspace_eq` applied to the independent family of weight
  spaces);
* `Commons.LinearAlgebra.End.sl2_eigenspace_finrank_symm` applied to the restricted operators on
  the string gives `finrank (Mwt ν) = finrank (Mwt (sᵢν))`.

The local nilpotence of `Eᵢ` and `Fᵢ` on the finite-dimensional `M` — the only input not available
for free — is obtained from `Eᵢ = ½[Hᵢ, Eᵢ]` by the trace/eigenvalue argument: the powers `Eᵢⁿ`
are eigenvectors of `ad Hᵢ` with the pairwise distinct eigenvalues `2n`, while `ad Hᵢ` has only
finitely many eigenvalues, so some power vanishes.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

noncomputable section
open scoped BigOperators

namespace Commons.Algebra.Lie.SerreConstruction

open Commons.LinearAlgebra.End

/-! ### Nilpotency -/

lemma adEnd_deriv {V : Type*} [AddCommGroup V] [Module ℂ V]
    (H X Y : Module.End ℂ V) :
    adEnd H (X * Y) = adEnd H X * Y + X * adEnd H Y := by
  rw [adEnd_apply, adEnd_apply, adEnd_apply]; noncomm_ring

lemma exists_pow_eq_zero_of_adEnd_eq_smul {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V] (H E : Module.End ℂ V) (c : ℂ) (hc : c ≠ 0)
    (had : adEnd H E = c • E) : ∃ n : ℕ, E ^ n = 0 := by
  have hderiv : ∀ n : ℕ, adEnd H (E ^ n) = (c * (n : ℂ)) • (E ^ n) := by
    intro n
    induction n with
    | zero => simp [adEnd_apply]
    | succ n ih =>
        rw [pow_succ, adEnd_deriv, ih, had, smul_mul_assoc, mul_smul_comm, ← add_smul]
        congr 1
        push_cast; ring
  by_contra hcon
  push Not at hcon
  have hmem : ∀ n : ℕ, (adEnd H).HasEigenvalue (c * (n : ℂ)) := by
    intro n
    refine Module.End.hasEigenvalue_of_hasEigenvector ⟨?_, hcon n⟩
    rw [Module.End.mem_eigenspace_iff]
    exact hderiv n
  have hfin : Set.Finite {μ : ℂ | (adEnd H).HasEigenvalue μ} :=
    Module.End.finite_hasEigenvalue _
  have hinj : Function.Injective (fun n : ℕ => c * (n : ℂ)) := by
    intro a b hab
    simp only at hab
    have h : (a : ℂ) = (b : ℂ) := mul_left_cancel₀ hc hab
    exact_mod_cast h
  exact Set.infinite_range_of_injective hinj (hfin.subset (fun x hx => by
    obtain ⟨n, rfl⟩ := hx; exact hmem n))

section Main

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
    [LieRingModule L8 M] [LieModule ℂ L8 M]

/-- The joint weight space of a module `M` at the weight `μ`. -/
def Mwt (μ : Fin 8 → ℤ) : Submodule ℂ M :=
  ⨅ j : Fin 8, Module.End.eigenspace (LieModule.toEnd ℂ L8 M (SerreH j)) ((μ j : ℤ) : ℂ)

lemma mem_Mwt_iff {μ : Fin 8 → ℤ} {x : M} :
    x ∈ Mwt μ ↔ ∀ j : Fin 8,
      LieModule.toEnd ℂ L8 M (SerreH j) x = ((μ j : ℤ) : ℂ) • x := by
  simp only [Mwt, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

lemma toEnd_mul_sub (x y : L8) :
    LieModule.toEnd ℂ L8 M x * LieModule.toEnd ℂ L8 M y
      - LieModule.toEnd ℂ L8 M y * LieModule.toEnd ℂ L8 M x
      = LieModule.toEnd ℂ L8 M ⁅x, y⁆ := by
  ext m
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LieModule.toEnd_apply_apply]
  rw [leibniz_lie]
  abel

/-- `E_i` raises the weight by `α_i`. -/
lemma toEnd_e_mem_Mwt (i : Fin 8) {ν : Fin 8 → ℤ} {x : M} (hx : x ∈ Mwt ν) :
    LieModule.toEnd ℂ L8 M (SerreE i) x ∈ Mwt (fun j => ν j + E8 j i) := by
  rw [mem_Mwt_iff] at hx ⊢
  intro j
  have hxj : ⁅SerreH j, x⁆ = ((ν j : ℤ) : ℂ) • x := hx j
  show ⁅SerreH j, ⁅SerreE i, x⁆⁆ = ((ν j + E8 j i : ℤ) : ℂ) • ⁅SerreE i, x⁆
  rw [leibniz_lie, hxj, lie_smul, serreLie_H_E_c, smul_lie, ← add_smul]
  congr 1
  push_cast
  ring

/-- `F_i` lowers the weight by `α_i`. -/
lemma toEnd_f_mem_Mwt (i : Fin 8) {ν : Fin 8 → ℤ} {x : M} (hx : x ∈ Mwt ν) :
    LieModule.toEnd ℂ L8 M (SerreF i) x ∈ Mwt (fun j => ν j - E8 j i) := by
  rw [mem_Mwt_iff] at hx ⊢
  intro j
  have hxj : ⁅SerreH j, x⁆ = ((ν j : ℤ) : ℂ) • x := hx j
  show ⁅SerreH j, ⁅SerreF i, x⁆⁆ = ((ν j - E8 j i : ℤ) : ℂ) • ⁅SerreF i, x⁆
  rw [leibniz_lie, hxj, lie_smul, serreLie_H_F_c, smul_lie, ← add_smul]
  congr 1
  push_cast
  ring

/-- `H_k` preserves the weight. -/
lemma toEnd_h_mem_Mwt (k : Fin 8) {ν : Fin 8 → ℤ} {x : M} (hx : x ∈ Mwt ν) :
    LieModule.toEnd ℂ L8 M (SerreH k) x ∈ Mwt ν := by
  rw [mem_Mwt_iff] at hx ⊢
  intro j
  have hxj : ⁅SerreH j, x⁆ = ((ν j : ℤ) : ℂ) • x := hx j
  show ⁅SerreH j, ⁅SerreH k, x⁆⁆ = ((ν j : ℤ) : ℂ) • ⁅SerreH k, x⁆
  rw [leibniz_lie, serreLie_HH, zero_lie, zero_add, hxj, lie_smul]

/-- The shift of a weight by `c` copies of the root `α_i`. -/
def shift (i : Fin 8) (ν : Fin 8 → ℤ) (c : ℤ) : Fin 8 → ℤ := fun j => ν j + c * E8 j i

lemma shift_zero (i : Fin 8) (ν : Fin 8 → ℤ) : shift i ν 0 = ν := by
  funext j; simp [shift]

lemma shift_succ (i : Fin 8) (ν : Fin 8 → ℤ) (c : ℤ) :
    shift i ν (c + 1) = fun j => shift i ν c j + E8 j i := by
  funext j; simp only [shift]; ring

lemma shift_pred (i : Fin 8) (ν : Fin 8 → ℤ) (c : ℤ) :
    shift i ν (c - 1) = fun j => shift i ν c j - E8 j i := by
  funext j; simp only [shift]; ring

lemma shift_apply_eigen (i : Fin 8) (ν : Fin 8 → ℤ) (c : ℤ) :
    (shift i ν c) i = ν i + 2 * c := by
  simp only [shift]; rw [E8_diag]; ring

lemma shift_neg (i : Fin 8) (ν : Fin 8 → ℤ) :
    shift i ν (-(ν i)) = Commons.LinearAlgebra.Matrix.Cartan.sref i ν := by
  funext j
  simp only [shift, Commons.LinearAlgebra.Matrix.Cartan.sref,
    Commons.LinearAlgebra.Matrix.Cartan.E8m]
  rw [← E8_symm i j]
  ring

lemma sref_apply_self' (i : Fin 8) (ν : Fin 8 → ℤ) :
    Commons.LinearAlgebra.Matrix.Cartan.sref i ν i = -(ν i) := by
  simp only [Commons.LinearAlgebra.Matrix.Cartan.sref, Commons.LinearAlgebra.Matrix.Cartan.E8m]
  rw [show CartanMatrix.E₈ i i = 2 from by fin_cases i <;> decide]
  ring

/-- The `α_i`-string through the weight `ν`. -/
def Str (i : Fin 8) (ν : Fin 8 → ℤ) : Submodule ℂ M := ⨆ c : ℤ, Mwt (shift i ν c)

lemma toEnd_e_maps_Str (i : Fin 8) (ν : Fin 8 → ℤ) :
    Submodule.map (LieModule.toEnd ℂ L8 M (SerreE i)) (Str i ν) ≤ Str i ν := by
  rw [Str, Submodule.map_iSup]
  refine iSup_le fun c => ?_
  refine Submodule.map_le_iff_le_comap.mpr fun x hx => ?_
  have h := toEnd_e_mem_Mwt i hx
  rw [← shift_succ] at h
  exact le_iSup (fun c : ℤ => Mwt (shift i ν c)) (c + 1) h

lemma toEnd_f_maps_Str (i : Fin 8) (ν : Fin 8 → ℤ) :
    Submodule.map (LieModule.toEnd ℂ L8 M (SerreF i)) (Str i ν) ≤ Str i ν := by
  rw [Str, Submodule.map_iSup]
  refine iSup_le fun c => ?_
  refine Submodule.map_le_iff_le_comap.mpr fun x hx => ?_
  have h := toEnd_f_mem_Mwt i hx
  rw [← shift_pred] at h
  exact le_iSup (fun c : ℤ => Mwt (shift i ν c)) (c - 1) h

lemma toEnd_h_maps_Str (i : Fin 8) (ν : Fin 8 → ℤ) :
    Submodule.map (LieModule.toEnd ℂ L8 M (SerreH i)) (Str i ν) ≤ Str i ν := by
  rw [Str, Submodule.map_iSup]
  refine iSup_le fun c => ?_
  refine Submodule.map_le_iff_le_comap.mpr fun x hx => ?_
  exact le_iSup (fun c : ℤ => Mwt (shift i ν c)) c (toEnd_h_mem_Mwt i hx)

lemma toEnd_e_mem_Str (i : Fin 8) (ν : Fin 8 → ℤ) {x : M} (hx : x ∈ Str i ν) :
    LieModule.toEnd ℂ L8 M (SerreE i) x ∈ Str i ν :=
  toEnd_e_maps_Str i ν (show LieModule.toEnd ℂ L8 M (SerreE i) x
      ∈ Submodule.map (LieModule.toEnd ℂ L8 M (SerreE i)) (Str i ν)
    from Submodule.mem_map.mpr ⟨x, hx, rfl⟩)

lemma toEnd_f_mem_Str (i : Fin 8) (ν : Fin 8 → ℤ) {x : M} (hx : x ∈ Str i ν) :
    LieModule.toEnd ℂ L8 M (SerreF i) x ∈ Str i ν :=
  toEnd_f_maps_Str i ν (show LieModule.toEnd ℂ L8 M (SerreF i) x
      ∈ Submodule.map (LieModule.toEnd ℂ L8 M (SerreF i)) (Str i ν)
    from Submodule.mem_map.mpr ⟨x, hx, rfl⟩)

lemma toEnd_h_mem_Str (i : Fin 8) (ν : Fin 8 → ℤ) {x : M} (hx : x ∈ Str i ν) :
    LieModule.toEnd ℂ L8 M (SerreH i) x ∈ Str i ν :=
  toEnd_h_maps_Str i ν (show LieModule.toEnd ℂ L8 M (SerreH i) x
      ∈ Submodule.map (LieModule.toEnd ℂ L8 M (SerreH i)) (Str i ν)
    from Submodule.mem_map.mpr ⟨x, hx, rfl⟩)

/-- The restricted operator `H_i` on the string. -/
noncomputable def StrH (i : Fin 8) (ν : Fin 8 → ℤ) : Module.End ℂ ↥(Str (M := M) i ν) :=
  LinearMap.restrict (LieModule.toEnd ℂ L8 M (SerreH i))
    (fun _ hx => toEnd_h_mem_Str i ν hx)

/-- The restricted operator `E_i` on the string. -/
noncomputable def StrE (i : Fin 8) (ν : Fin 8 → ℤ) : Module.End ℂ ↥(Str (M := M) i ν) :=
  LinearMap.restrict (LieModule.toEnd ℂ L8 M (SerreE i))
    (fun _ hx => toEnd_e_mem_Str i ν hx)

/-- The restricted operator `F_i` on the string. -/
noncomputable def StrF (i : Fin 8) (ν : Fin 8 → ℤ) : Module.End ℂ ↥(Str (M := M) i ν) :=
  LinearMap.restrict (LieModule.toEnd ℂ L8 M (SerreF i))
    (fun _ hx => toEnd_f_mem_Str i ν hx)

lemma H_mul_E_sub (i : Fin 8) :
    LieModule.toEnd ℂ L8 M (SerreH i) * LieModule.toEnd ℂ L8 M (SerreE i)
      - LieModule.toEnd ℂ L8 M (SerreE i) * LieModule.toEnd ℂ L8 M (SerreH i)
      = (2 : ℂ) • LieModule.toEnd ℂ L8 M (SerreE i) := by
  rw [toEnd_mul_sub, serreLie_H_E_c, E8_diag]
  norm_num

lemma H_mul_F_sub (i : Fin 8) :
    LieModule.toEnd ℂ L8 M (SerreH i) * LieModule.toEnd ℂ L8 M (SerreF i)
      - LieModule.toEnd ℂ L8 M (SerreF i) * LieModule.toEnd ℂ L8 M (SerreH i)
      = -((2 : ℂ) • LieModule.toEnd ℂ L8 M (SerreF i)) := by
  rw [toEnd_mul_sub, serreLie_H_F_c, E8_diag]
  norm_num

lemma E_mul_F_sub (i : Fin 8) :
    LieModule.toEnd ℂ L8 M (SerreE i) * LieModule.toEnd ℂ L8 M (SerreF i)
      - LieModule.toEnd ℂ L8 M (SerreF i) * LieModule.toEnd ℂ L8 M (SerreE i)
      = LieModule.toEnd ℂ L8 M (SerreH i) := by
  rw [toEnd_mul_sub, serreLie_E_F, if_pos rfl]

lemma Str_sl2_1 (i : Fin 8) (ν : Fin 8 → ℤ) :
    StrH (M := M) i ν * StrE (M := M) i ν - StrE (M := M) i ν * StrH (M := M) i ν
      = (2 : ℂ) • StrE (M := M) i ν := by
  ext x
  have h := congrArg (fun (F : Module.End ℂ M) => F (x : M)) (H_mul_E_sub i)
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.restrict_apply, StrH, StrE] at h ⊢
  exact h

lemma Str_sl2_2 (i : Fin 8) (ν : Fin 8 → ℤ) :
    StrH (M := M) i ν * StrF (M := M) i ν - StrF (M := M) i ν * StrH (M := M) i ν
      = -((2 : ℂ) • StrF (M := M) i ν) := by
  ext x
  have h := congrArg (fun (F : Module.End ℂ M) => F (x : M)) (H_mul_F_sub i)
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.neg_apply,
    LinearMap.restrict_apply, StrH, StrF] at h ⊢
  exact h

lemma Str_sl2_3 (i : Fin 8) (ν : Fin 8 → ℤ) :
    StrE (M := M) i ν * StrF (M := M) i ν - StrF (M := M) i ν * StrE (M := M) i ν
      = StrH (M := M) i ν := by
  ext x
  have h := congrArg (fun (F : Module.End ℂ M) => F (x : M)) (E_mul_F_sub i)
  simp only [Module.End.mul_apply, LinearMap.sub_apply,
    LinearMap.restrict_apply, Subtype.coe_mk, StrH, StrE, StrF] at h ⊢
  exact h

lemma adEnd_H_e (i : Fin 8) :
    adEnd (LieModule.toEnd ℂ L8 M (SerreH i)) (LieModule.toEnd ℂ L8 M (SerreE i))
      = (2 : ℂ) • LieModule.toEnd ℂ L8 M (SerreE i) := by
  rw [adEnd_apply, H_mul_E_sub]

lemma adEnd_H_f (i : Fin 8) :
    adEnd (LieModule.toEnd ℂ L8 M (SerreH i)) (LieModule.toEnd ℂ L8 M (SerreF i))
      = (-2 : ℂ) • LieModule.toEnd ℂ L8 M (SerreF i) := by
  rw [adEnd_apply, H_mul_F_sub, neg_smul]

lemma localNilpotent_e (i : Fin 8) [Module.Finite ℂ M] (x : M) :
    ∃ n : ℕ, ((LieModule.toEnd ℂ L8 M (SerreE i)) ^ n) x = 0 := by
  obtain ⟨n, hn⟩ := exists_pow_eq_zero_of_adEnd_eq_smul (LieModule.toEnd ℂ L8 M (SerreH i))
    (LieModule.toEnd ℂ L8 M (SerreE i)) (2 : ℂ) (by norm_num) (adEnd_H_e i)
  exact ⟨n, by rw [hn]; simp⟩

lemma localNilpotent_f (i : Fin 8) [Module.Finite ℂ M] (x : M) :
    ∃ n : ℕ, ((LieModule.toEnd ℂ L8 M (SerreF i)) ^ n) x = 0 := by
  obtain ⟨n, hn⟩ := exists_pow_eq_zero_of_adEnd_eq_smul (LieModule.toEnd ℂ L8 M (SerreH i))
    (LieModule.toEnd ℂ L8 M (SerreF i)) (-2 : ℂ) (by norm_num) (adEnd_H_f i)
  exact ⟨n, by rw [hn]; simp⟩

lemma StrE_pow_coe (i : Fin 8) (ν : Fin 8 → ℤ) (n : ℕ) (x : ↥(Str (M := M) i ν)) :
    (((StrE (M := M) i ν) ^ n) x : M)
      = ((LieModule.toEnd ℂ L8 M (SerreE i)) ^ n) (x : M) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      have h1 : ((StrE (M := M) i ν) ^ (n + 1)) x
          = (StrE (M := M) i ν) (((StrE (M := M) i ν) ^ n) x) := by
        rw [pow_succ', Module.End.mul_apply]
      have h2 : ((LieModule.toEnd ℂ L8 M (SerreE i)) ^ (n + 1)) (x : M)
          = LieModule.toEnd ℂ L8 M (SerreE i)
            (((LieModule.toEnd ℂ L8 M (SerreE i)) ^ n) (x : M)) := by
        rw [pow_succ', Module.End.mul_apply]
      have h3 : (((StrE (M := M) i ν) (((StrE (M := M) i ν) ^ n) x) : M))
          = LieModule.toEnd ℂ L8 M (SerreE i)
            ((((StrE (M := M) i ν) ^ n) x : ↥(Str (M := M) i ν)) : M) := rfl
      rw [h1, h2, h3, ih]

lemma StrF_pow_coe (i : Fin 8) (ν : Fin 8 → ℤ) (n : ℕ) (x : ↥(Str (M := M) i ν)) :
    (((StrF (M := M) i ν) ^ n) x : M)
      = ((LieModule.toEnd ℂ L8 M (SerreF i)) ^ n) (x : M) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      have h1 : ((StrF (M := M) i ν) ^ (n + 1)) x
          = (StrF (M := M) i ν) (((StrF (M := M) i ν) ^ n) x) := by
        rw [pow_succ', Module.End.mul_apply]
      have h2 : ((LieModule.toEnd ℂ L8 M (SerreF i)) ^ (n + 1)) (x : M)
          = LieModule.toEnd ℂ L8 M (SerreF i)
            (((LieModule.toEnd ℂ L8 M (SerreF i)) ^ n) (x : M)) := by
        rw [pow_succ', Module.End.mul_apply]
      have h3 : (((StrF (M := M) i ν) (((StrF (M := M) i ν) ^ n) x) : M))
          = LieModule.toEnd ℂ L8 M (SerreF i)
            ((((StrF (M := M) i ν) ^ n) x : ↥(Str (M := M) i ν)) : M) := rfl
      rw [h1, h2, h3, ih]

lemma StrE_localNilpotent (i : Fin 8) (ν : Fin 8 → ℤ) [Module.Finite ℂ M]
    (x : ↥(Str (M := M) i ν)) : ∃ n : ℕ, ((StrE (M := M) i ν) ^ n) x = 0 := by
  obtain ⟨n, hn⟩ := localNilpotent_e (M := M) i (x : M)
  exact ⟨n, by apply Subtype.ext; rw [StrE_pow_coe]; exact hn⟩

lemma StrF_localNilpotent (i : Fin 8) (ν : Fin 8 → ℤ) [Module.Finite ℂ M]
    (x : ↥(Str (M := M) i ν)) : ∃ n : ℕ, ((StrF (M := M) i ν) ^ n) x = 0 := by
  obtain ⟨n, hn⟩ := localNilpotent_f (M := M) i (x : M)
  exact ⟨n, by apply Subtype.ext; rw [StrF_pow_coe]; exact hn⟩

lemma Str_inf_eigenspace_shift (i : Fin 8) (ν : Fin 8 → ℤ) (c : ℤ) :
    Str (M := M) i ν ⊓ Module.End.eigenspace (LieModule.toEnd ℂ L8 M (SerreH i))
      (((shift i ν c) i : ℤ) : ℂ) = Mwt (shift i ν c) := by
  show (⨆ c : ℤ, Mwt (shift i ν c)) ⊓ Module.End.eigenspace (LieModule.toEnd ℂ L8 M (SerreH i))
      (((shift i ν c) i : ℤ) : ℂ) = Mwt (shift i ν c)
  rw [Commons.LinearAlgebra.End.iSup_inf_eigenspace_eq (f := LieModule.toEnd ℂ L8 M (SerreH i))
    (lam := fun c : ℤ => (((shift i ν c) i : ℤ) : ℂ))
    (p := fun c : ℤ => Mwt (shift i ν c)) ?_ ?_ c]
  · intro c c' h
    have h' : (shift i ν c) i = (shift i ν c') i := Int.cast_injective h
    rw [shift_apply_eigen, shift_apply_eigen] at h'
    omega
  · intro c x hx
    rw [Module.End.mem_eigenspace_iff]
    exact (mem_Mwt_iff.mp hx) i

lemma Str_inf_eigenspace (i : Fin 8) (ν : Fin 8 → ℤ) :
    Str (M := M) i ν ⊓ Module.End.eigenspace (LieModule.toEnd ℂ L8 M (SerreH i))
      ((ν i : ℤ) : ℂ) = Mwt ν := by
  have h := Str_inf_eigenspace_shift (M := M) i ν 0
  simpa [shift_zero] using h

lemma Str_inf_eigenspace_neg (i : Fin 8) (ν : Fin 8 → ℤ) :
    Str (M := M) i ν ⊓ Module.End.eigenspace (LieModule.toEnd ℂ L8 M (SerreH i))
      (-(((ν i : ℤ)) : ℂ)) = Mwt (Commons.LinearAlgebra.Matrix.Cartan.sref i ν) := by
  have h := Str_inf_eigenspace_shift (M := M) i ν (-(ν i))
  rw [shift_neg, sref_apply_self'] at h
  simpa using h

noncomputable def eigenspaceEquiv (i : Fin 8) (ν : Fin 8 → ℤ) (μ : ℂ) :
    ↥(Module.End.eigenspace (StrH (M := M) i ν) μ) ≃ₗ[ℂ]
      ↥(Str (M := M) i ν ⊓ Module.End.eigenspace
        (LieModule.toEnd ℂ L8 M (SerreH i)) μ) where
  toFun x := ⟨(x.1 : M), ⟨x.1.2, by
    refine Module.End.mem_eigenspace_iff.mpr ?_
    have h := congrArg (fun z : ↥(Str (M := M) i ν) => (z : M))
      (Module.End.mem_eigenspace_iff.mp x.2)
    simpa [StrH, LinearMap.restrict_apply, Submodule.coe_mk] using h⟩⟩
  invFun y := ⟨⟨(y.1 : M), y.2.1⟩, by
    refine Module.End.mem_eigenspace_iff.mpr ?_
    apply Subtype.ext
    exact (Module.End.mem_eigenspace_iff.mp y.2.2)⟩
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl
  map_add' x y := by ext; rfl
  map_smul' c x := by ext; rfl

lemma eigenspace_finrank_eq (i : Fin 8) (ν : Fin 8 → ℤ) (μ : ℂ) :
    Module.finrank ℂ ↥(Module.End.eigenspace (StrH (M := M) i ν) μ)
      = Module.finrank ℂ ↥(Str (M := M) i ν ⊓ Module.End.eigenspace
        (LieModule.toEnd ℂ L8 M (SerreH i)) μ) :=
  LinearEquiv.finrank_eq (eigenspaceEquiv (M := M) i ν μ)

end Main

theorem weight_mult_reflect {M : Type*} [AddCommGroup M] [Module ℂ M]
    [LieRingModule Commons.Algebra.Lie.SerreConstruction.L8 M]
    [LieModule ℂ Commons.Algebra.Lie.SerreConstruction.L8 M] [Module.Finite ℂ M]
    (i : Fin 8) (μ : Fin 8 → ℤ) :
    Module.finrank ℂ ↥(⨅ j : Fin 8, Module.End.eigenspace
        (LieModule.toEnd ℂ Commons.Algebra.Lie.SerreConstruction.L8 M
          (Commons.Algebra.Lie.SerreConstruction.SerreH j)) ((μ j : ℤ) : ℂ))
      = Module.finrank ℂ ↥(⨅ j : Fin 8, Module.End.eigenspace
        (LieModule.toEnd ℂ Commons.Algebra.Lie.SerreConstruction.L8 M
          (Commons.Algebra.Lie.SerreConstruction.SerreH j))
        (((Commons.LinearAlgebra.Matrix.Cartan.sref i μ) j : ℤ) : ℂ)) := by
  show Module.finrank ℂ ↥(Mwt (M := M) μ)
    = Module.finrank ℂ ↥(Mwt (M := M) (Commons.LinearAlgebra.Matrix.Cartan.sref i μ))
  have hsl2 := Commons.LinearAlgebra.End.sl2_eigenspace_finrank_symm
    (StrH (M := M) i μ) (StrE (M := M) i μ) (StrF (M := M) i μ)
    (Str_sl2_1 (M := M) i μ) (Str_sl2_2 (M := M) i μ) (Str_sl2_3 (M := M) i μ)
    (StrE_localNilpotent (M := M) i μ) (StrF_localNilpotent (M := M) i μ)
    (((μ i : ℤ)) : ℂ)
  rw [eigenspace_finrank_eq (M := M) i μ (((μ i : ℤ)) : ℂ),
    Str_inf_eigenspace (M := M) i μ,
    eigenspace_finrank_eq (M := M) i μ (-(((μ i : ℤ)) : ℂ)),
    Str_inf_eigenspace_neg (M := M) i μ] at hsl2
  exact hsl2

end Commons.Algebra.Lie.SerreConstruction
