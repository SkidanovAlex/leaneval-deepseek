import Mathlib
import Submission.Work.CharPrelim.weightSpace_defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The weight spaces span, over a field containing a primitive root of unity

Over an *arbitrary* field `k` (not necessarily algebraically closed) which contains a primitive
`|Z|`-th root of unity and in which `|Z|` is invertible, the weight spaces `weightSpace τ χ` of a
representation `τ : Z →* Module.End k M` of a finite abelian group `Z` span `M`:

`Work.CharPrelim.weightSpace_span_of_primitiveRoot`.

This is the general-field form of `Work.CharPrelim.weightSpace_finDim` (which assumes `k`
algebraically closed).  The proof replaces the algebraically-closed spectral decomposition of a
single finite-order operator used there by an elementary one over `k`:

* `iSup_eigenspace_eq_top_of_primitiveRoot`: if `T ^ n = 1` and `k` contains a primitive `n`-th
  root of unity `ζ`, then the eigenspaces of `T` (for eigenvalues in `k`) span.  The proof factors
  `X ^ n - 1 = ∏_{i<n} (X - ζ^i)` into pairwise coprime linear factors and applies the primary
  decomposition `iSup_ker_aeval_eq_ker_aeval_prod`.
* The family `z ↦ τ z` is a commuting family of endomorphisms, so it is simultaneously
  triangularizable
  (`Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute`).
  Since each `τ z` is semisimple (its minimal polynomial divides the separable `X ^ n - 1`), the
  (maximal) generalised eigenspaces are ordinary eigenspaces.
* `iSup_iInf_eigenspace_le_iSup_weightSpace`: a simultaneous eigenvector for an arbitrary function
  `χ : Z → k` is a weight vector of a genuine character `Z →* kˣ`.
-/

noncomputable section

set_option linter.style.haveILetI false

open Classical

namespace Work.CharPrelim

open Polynomial

section PrimaryDecomposition

/-- **Primary decomposition.**  For a linear endomorphism `f` of an `R`-module `M` and a finite
family `g` of pairwise coprime polynomials, the supremum of the kernels of the `aeval f (g i)` is
the kernel of `aeval f (∏ g i)`. -/
theorem iSup_ker_aeval_eq_ker_aeval_prod' {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {ι : Type*} (f : M →ₗ[R] M) (s : Finset ι) (g : ι → Polynomial R)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (g i) (g j)) :
    (⨆ i ∈ s, LinearMap.ker (Polynomial.aeval f (g i))) =
      LinearMap.ker (Polynomial.aeval f (∏ i ∈ s, g i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty, map_one]
      rw [show (⨆ i ∈ (∅ : Finset ι), LinearMap.ker (Polynomial.aeval f (g i))) = ⊥ from by simp]
      exact (LinearMap.ker_eq_bot.mpr (fun a b h => by simpa using h)).symm
  | insert a t ha ih =>
      rw [Finset.iSup_insert, Finset.prod_insert ha]
      rw [ih (fun i hi j hj hij =>
        hcop i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)]
      rw [sup_ker_aeval_eq_ker_aeval_mul_of_coprime]
      apply IsCoprime.prod_right
      intro i hi
      exact hcop a (Finset.mem_insert_self a t) i (Finset.mem_insert_of_mem hi)
        (by rintro rfl; exact ha hi)

end PrimaryDecomposition

section SingleOperator

/-- **Spectral decomposition of a finite order operator over a field with a primitive root.**
If `T ^ n = 1` and `k` contains a primitive `n`-th root of unity `ζ`, then the eigenspaces of `T`
(for eigenvalues in `k`) span the whole space.  No dimension hypothesis is needed. -/
theorem iSup_eigenspace_eq_top_of_primitiveRoot {k V : Type*} [Field k] [AddCommGroup V]
    [Module k V] (T : Module.End k V) {n : ℕ} {ζ : k} (hn : 0 < n)
    (hζ : IsPrimitiveRoot ζ n) (hT : T ^ n = 1) :
    (⨆ μ : k, T.eigenspace μ) = ⊤ := by
  -- `X ^ n - 1 = ∏_{i<n} (X - ζ ^ i)`
  have hfac : (∏ i ∈ Finset.range n, (Polynomial.X - Polynomial.C (ζ ^ i) : Polynomial k))
      = (Polynomial.X : Polynomial k) ^ n - 1 := by
    have h := X_pow_sub_C_eq_prod (R := k) hζ (α := (1 : k)) (a := (1 : k)) hn (one_pow n)
    simpa using h.symm
  -- the factors are pairwise coprime
  have hcop : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n, i ≠ j →
      IsCoprime (Polynomial.X - Polynomial.C (ζ ^ i) : Polynomial k)
        (Polynomial.X - Polynomial.C (ζ ^ j)) := by
    intro i hi j hj hij
    apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
    rw [isUnit_iff_ne_zero, sub_ne_zero]
    intro h
    exact hij (hζ.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) h)
  -- primary decomposition gives a spanning family of eigenspaces
  have hdecomp : (⨆ i ∈ Finset.range n,
      LinearMap.ker (Polynomial.aeval T (Polynomial.X - Polynomial.C (ζ ^ i) : Polynomial k))) =
      ⊤ := by
    rw [iSup_ker_aeval_eq_ker_aeval_prod' T _ _ hcop, hfac]
    rw [show Polynomial.aeval T ((Polynomial.X : Polynomial k) ^ n - 1) = 0 by
      simp [Polynomial.aeval_X, hT]]
    exact LinearMap.ker_zero
  have hEq : ∀ i : ℕ, LinearMap.ker (Polynomial.aeval T
        (Polynomial.X - Polynomial.C (ζ ^ i) : Polynomial k)) = T.eigenspace (ζ ^ i) := by
    intro i
    rw [Module.End.eigenspace_def]
    congr 1
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
  have htop : (⨆ i ∈ Finset.range n, T.eigenspace (ζ ^ i)) = ⊤ := by
    rw [← hdecomp]
    simp_rw [hEq]
  refine le_antisymm le_top ?_
  rw [← htop]
  exact iSup_le (fun i => iSup_le (fun _ => le_iSup (fun μ : k => T.eigenspace μ) (ζ ^ i)))

end SingleOperator

section Bridge

/-- **From simultaneous eigenvectors to weight vectors.**  A simultaneous eigenvector of the family
`z ↦ τ z` for an arbitrary function `χ : Z → k` is a weight vector for a genuine character
`Z →* kˣ` (namely `z ↦ χ z`).  Hence the supremum of the simultaneous eigenspaces over all
functions `Z → k` is contained in the supremum of the weight spaces. -/
theorem iSup_iInf_eigenspace_le_iSup_weightSpace {k M Z : Type*} [Field k] [CommGroup Z]
    [AddCommGroup M] [Module k M] (τ : Z →* Module.End k M) :
    (⨆ χ : Z → k, ⨅ z, (τ z).eigenspace (χ z)) ≤
      ⨆ ψ : Z →* kˣ, weightSpace τ ψ := by
  refine iSup_le (fun χ => ?_)
  by_cases hbot : (⨅ z, (τ z).eigenspace (χ z)) = ⊥
  · rw [hbot]; exact bot_le
  · obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hbot
    have hvmem : ∀ z, v ∈ (τ z).eigenspace (χ z) := fun z => (Submodule.mem_iInf _).mp hv z
    -- `χ z` is nonzero because `τ z` is invertible and `v ≠ 0`
    have hne : ∀ z, χ z ≠ 0 := by
      intro z hz
      have hzv : τ z v = 0 := by
        have h := hvmem z
        rw [Module.End.mem_eigenspace_iff] at h
        rw [h, hz, zero_smul]
      have hinv : τ z⁻¹ * τ z = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
      have h2 := congrArg (fun f : Module.End k M => f v) hinv
      simp only [Module.End.mul_apply, Module.End.one_apply] at h2
      rw [hzv, map_zero] at h2
      exact hv0 h2.symm
    -- `χ` is multiplicative
    have hmul : ∀ a b : Z, χ (a * b) = χ a * χ b := by
      intro a b
      have ha := hvmem a
      have hb := hvmem b
      rw [Module.End.mem_eigenspace_iff] at ha hb
      have h1 : τ (a * b) v = (χ a * χ b) • v := by
        rw [map_mul, Module.End.mul_apply, hb, map_smul, ha, smul_smul, mul_comm]
      have h2 : τ (a * b) v = χ (a * b) • v := by
        have := hvmem (a * b)
        rwa [Module.End.mem_eigenspace_iff] at this
      have h3 : (χ (a * b) - χ a * χ b) • v = 0 := by rw [sub_smul, ← h2, h1, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hv0)
    have hone : χ 1 = 1 := by
      have h2 : v = χ 1 • v := by
        have := hvmem 1
        rw [Module.End.mem_eigenspace_iff, map_one, Module.End.one_apply] at this
        exact this
      have h3 : (χ 1 - 1) • v = 0 := by rw [sub_smul, one_smul, ← h2, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hv0)
    let ψ : Z →* kˣ :=
      { toFun := fun z => Units.mk0 (χ z) (hne z)
        map_one' := Units.ext (by rw [Units.val_mk0, hone, Units.val_one])
        map_mul' := fun a b => Units.ext (by
          rw [Units.val_mk0, Units.val_mul, Units.val_mk0, Units.val_mk0, hmul a b]) }
    refine le_iSup_of_le ψ ?_
    intro w hw
    rw [mem_weightSpace]
    intro z
    have hwz : w ∈ (τ z).eigenspace (χ z) := (Submodule.mem_iInf _).mp hw z
    rw [Module.End.mem_eigenspace_iff] at hwz
    rw [hwz]
    simp only [ψ, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mk0]

end Bridge

/-- **The weight spaces span the whole space**, over a field `k` which contains a primitive
`|Z|`-th root of unity and in which `|Z|` is invertible. -/
theorem weightSpace_span_of_primitiveRoot {k M Z : Type*} [Field k] [CommGroup Z] [Finite Z]
    [AddCommGroup M] [Module k M] [FiniteDimensional k M] (τ : Z →* Module.End k M)
    (hcard : IsUnit ((Nat.card Z : ℕ) : k))
    (hroot : ∃ ζ : k, IsPrimitiveRoot ζ (Nat.card Z)) :
    (⨆ χ : Z →* kˣ, weightSpace τ χ) = ⊤ := by
  classical
  obtain ⟨ζ, hζ⟩ := hroot
  have hn0 : Nat.card Z ≠ 0 := fun h => hcard.ne_zero (by rw [h]; simp)
  have hn : 0 < Nat.card Z := Nat.pos_of_ne_zero hn0
  letI := Fintype.ofFinite Z
  have hzpow : ∀ z : Z, z ^ Nat.card Z = 1 := fun z => by
    rw [Nat.card_eq_fintype_card]; exact pow_card_eq_one
  have hpow : ∀ z : Z, (τ z) ^ (Nat.card Z) = 1 := fun z => by
    rw [← map_pow, hzpow z, map_one]
  -- each `τ z` is semisimple
  have hss : ∀ z : Z, (τ z).IsSemisimple := by
    intro z
    have hp : Squarefree ((Polynomial.X : Polynomial k) ^ (Nat.card Z) - 1) :=
      (Polynomial.X_pow_sub_one_separable_iff.mpr hcard.ne_zero).squarefree
    have hae : Polynomial.aeval (τ z) ((Polynomial.X : Polynomial k) ^ (Nat.card Z) - 1) = 0 := by
      rw [map_sub, map_pow, Polynomial.aeval_X, map_one, hpow z, sub_self]
    exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero hp hae
  -- semisimplicity: generalised eigenspaces are ordinary eigenspaces
  have hmaxeq : ∀ z : Z, ∀ μ : k, (τ z).maxGenEigenspace μ = (τ z).eigenspace μ :=
    fun z μ => Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace
      (hss z).isFinitelySemisimple μ
  -- each `τ z` has spanning generalised eigenspaces
  have hspan : ∀ z : Z, (⨆ μ : k, (τ z).maxGenEigenspace μ) = ⊤ := by
    intro z
    rw [show (⨆ μ : k, (τ z).maxGenEigenspace μ) = ⨆ μ : k, (τ z).eigenspace μ from
      iSup_congr (hmaxeq z)]
    exact iSup_eigenspace_eq_top_of_primitiveRoot (τ z) hn hζ (hpow z)
  -- simultaneous decomposition
  have hsim : (⨆ χ : Z → k, ⨅ z, (τ z).maxGenEigenspace (χ z)) = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      (fun z : Z => τ z)
      (fun a b _ => by show τ a * τ b = τ b * τ a; rw [← map_mul, ← map_mul, mul_comm])
      hspan
  -- replace generalised eigenspaces by eigenspaces
  have hsim' : (⨆ χ : Z → k, ⨅ z, (τ z).eigenspace (χ z)) = ⊤ := by
    rw [show (⨆ χ : Z → k, ⨅ z, (τ z).eigenspace (χ z))
        = (⨆ χ : Z → k, ⨅ z, (τ z).maxGenEigenspace (χ z)) from
      iSup_congr (fun χ => iInf_congr (fun z => (hmaxeq z (χ z)).symm)), hsim]
  refine le_antisymm le_top ?_
  rw [← hsim']
  exact iSup_iInf_eigenspace_le_iSup_weightSpace τ

end Work.CharPrelim
