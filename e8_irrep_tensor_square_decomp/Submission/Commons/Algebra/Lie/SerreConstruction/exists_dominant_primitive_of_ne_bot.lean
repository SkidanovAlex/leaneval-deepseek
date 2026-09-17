import Mathlib
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_zero_weightSpace_finrank
import Submission.Commons.LinearAlgebra.End.exists_joint_eigenvector
import Submission.Commons.LinearAlgebra.Matrix.Cartan.exists_w_mul_E8

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open CartanMatrix

namespace Commons.Algebra.Lie.SerreConstruction

/-- The Serre generators `(Hᵢ, Eᵢ, Fᵢ)` form an `𝔰𝔩₂`-triple in the Serre-constructed `e₈`. -/
theorem isSl2Triple_serre (i : Fin 8) : IsSl2Triple (SerreH i) (SerreE i) (SerreF i) where
  h_ne_zero := e8_H_linearIndependent.ne_zero i
  lie_e_f := by rw [serreLie_E_F, if_pos rfl]
  lie_h_e_nsmul := by
    rw [serreLie_H_E, E8_diag i]
    rw [← Int.cast_smul_eq_zsmul ℂ (2 : ℤ) (SerreE i),
      ← Nat.cast_smul_eq_nsmul ℂ (2 : ℕ) (SerreE i)]
    norm_num
  lie_h_f_nsmul := by
    rw [serreLie_H_F, E8_diag i]
    rw [← Int.cast_smul_eq_zsmul ℂ (-(2 : ℤ)) (SerreF i),
      ← Nat.cast_smul_eq_nsmul ℂ (2 : ℕ) (SerreF i)]
    norm_num

/-- **Every non-zero finite-dimensional `e₈`-module contains a dominant primitive vector.**

For any finite-dimensional complex `e₈`-module `M` and any non-zero Lie submodule `N ≤ M` there are
`0 ≠ x ∈ N` and `ν : Fin 8 → ℤ` with `ν i ≥ 0` for all `i`, such that `x` is a joint eigenvector of
the Cartan generators `SerreH i` with the integer eigenvalues `ν i` and is killed by all the raising
operators `SerreE i`.

Proof.  Let `w = A⁻¹·1` be the height coefficients (`Commons.LinearAlgebra.Matrix.Cartan.exists_w_mul_E8`) and let
`T = ∑ j, w j • ad(SerreH j)`.  Since `T` is a sum of the commuting `ad(SerreH j)`, it commutes with
each of them, and the identity `∑ j, w j * A_{j i} = 1` gives
`T (⁅SerreE i, x⁆) = ⁅SerreE i, T x⁆ + ⁅SerreE i, x⁆`, i.e. `ad(SerreE i)` raises the `T`-eigenvalue
by `1`.  Take an eigenvalue `λ` of the restriction of `T` to `N` whose real part is maximal and let
`W := N ⊓ eigenspace T λ ≠ ⊥`.  The identity above forces `⁅SerreE i, x⁆ = 0` for every `x ∈ W`
(otherwise `λ + 1` would be an eigenvalue of `T|_N` with strictly larger real part).  Finally `W` is
stable under every `ad(SerreH j)` (they commute with `T`), so `Commons.LinearAlgebra.End.exists_joint_eigenvector` produces
`0 ≠ x ∈ W` which is a joint eigenvector of all the `SerreH j`; then `(Hᵢ, Eᵢ, Fᵢ)` is an
`𝔰𝔩₂`-triple (`isSl2Triple_serre`) for which `x` is primitive, so
`IsSl2Triple.HasPrimitiveVectorWith.exists_nat` makes its weight a natural number. -/
theorem exists_dominant_primitive_of_ne_bot {M : Type*} [AddCommGroup M] [Module ℂ M]
    [LieRingModule Commons.Algebra.Lie.SerreConstruction.L8 M]
    [LieModule ℂ Commons.Algebra.Lie.SerreConstruction.L8 M] [Module.Finite ℂ M]
    (N : LieSubmodule ℂ Commons.Algebra.Lie.SerreConstruction.L8 M) (hN : N ≠ ⊥) :
    ∃ (x : M) (ν : Fin 8 → ℤ), x ∈ N ∧ x ≠ 0 ∧
      (∀ i, ⁅Commons.Algebra.Lie.SerreConstruction.SerreH i, x⁆ = ((ν i : ℤ) : ℂ) • x) ∧
      (∀ i, ⁅Commons.Algebra.Lie.SerreConstruction.SerreE i, x⁆ = 0) ∧ (∀ i, 0 ≤ ν i) := by
  classical
  obtain ⟨w, hw⟩ := Commons.LinearAlgebra.Matrix.Cartan.exists_w_mul_E8
  set T : Module.End ℂ M := ∑ j : Fin 8, w j • LieModule.toEnd ℂ L8 M (SerreH j) with hT
  have hT_apply (x : M) : T x = ∑ j : Fin 8, w j • ⁅SerreH j, x⁆ := by
    rw [hT, LinearMap.sum_apply]
    exact Finset.sum_congr rfl (fun j _ => by rw [LinearMap.smul_apply, LieModule.toEnd_apply_apply])
  have hTN : ∀ x ∈ N, T x ∈ N := by
    intro x hx
    rw [hT_apply]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (N.lie_mem (x := SerreH j) hx))
  haveI : Nontrivial ↥N := Submodule.nontrivial_iff_ne_bot.mpr (by simpa using hN)
  set TN : Module.End ℂ ↥N := T.restrict hTN with hTNdef
  obtain ⟨lam, hlam⟩ := Module.End.exists_eigenvalue TN
  obtain ⟨lam0, hlam0, hlam0max⟩ :=
    Set.exists_max_image {mu : ℂ | TN.HasEigenvalue mu} Complex.re
      TN.finite_hasEigenvalue ⟨lam, hlam⟩
  set W : Submodule ℂ M := N.toSubmodule ⊓ Module.End.eigenspace T lam0 with hWdef
  have hWne : W ≠ ⊥ := by
    have hlam0' : Module.End.eigenspace TN lam0 ≠ ⊥ := Module.End.hasEigenvalue_iff.mp hlam0
    obtain ⟨y, hy, hyne⟩ :=
      (Submodule.ne_bot_iff (Module.End.eigenspace TN lam0)).mp hlam0'
    have hyy : TN y = lam0 • y := Module.End.mem_eigenspace_iff.mp hy
    have hye : T (y : M) = lam0 • (y : M) := by
      have h2 : ((TN y : ↥N) : M) = lam0 • (y : M) := by rw [hyy]; rfl
      rw [hTNdef] at h2
      exact h2
    rw [Submodule.ne_bot_iff]
    refine ⟨(y : M), ⟨y.2, ?_⟩, fun h => hyne (Subtype.ext h)⟩
    exact Module.End.mem_eigenspace_iff.mpr hye
  -- the key computation: `ad (SerreE i)` raises the `T`-eigenvalue by one
  have hterm (i : Fin 8) (x : M) (j : Fin 8) :
      w j • ⁅SerreH j, ⁅SerreE i, x⁆⁆
        = (w j * (E8 j i : ℂ)) • ⁅SerreE i, x⁆ + w j • ⁅SerreE i, ⁅SerreH j, x⁆⁆ := by
    have h1 : ⁅SerreH j, ⁅SerreE i, x⁆⁆
        = ((E8 j i : ℤ) : ℂ) • ⁅SerreE i, x⁆ + ⁅SerreE i, ⁅SerreH j, x⁆⁆ := by
      rw [leibniz_lie (SerreH j) (SerreE i) x, serreLie_H_E j i, smul_lie,
        ← Int.cast_smul_eq_zsmul ℂ (E8 j i) (⁅SerreE i, x⁆)]
    rw [h1, smul_add, smul_smul]
  have hTE (i : Fin 8) (x : M) : T (⁅SerreE i, x⁆) = ⁅SerreE i, T x⁆ + ⁅SerreE i, x⁆ := by
    have hTx : ⁅SerreE i, T x⁆ = ∑ j : Fin 8, w j • ⁅SerreE i, ⁅SerreH j, x⁆⁆ := by
      rw [hT_apply]
      show (LieModule.toEnd ℂ L8 M (SerreE i)) (∑ j : Fin 8, w j • ⁅SerreH j, x⁆)
        = ∑ j : Fin 8, w j • ⁅SerreE i, ⁅SerreH j, x⁆⁆
      rw [map_sum]
      exact Finset.sum_congr rfl (fun j _ => by rw [map_smul, LieModule.toEnd_apply_apply])
    rw [hT_apply, Finset.sum_congr rfl (fun j _ => hterm i x j), Finset.sum_add_distrib, hTx,
      ← Finset.sum_smul, hw i, one_smul]
    abel
  -- `T` commutes with every `ad (SerreH j)`
  have hTW (j : Fin 8) (x : M) : T (⁅SerreH j, x⁆) = ⁅SerreH j, T x⁆ := by
    have hTx : ⁅SerreH j, T x⁆ = ∑ k : Fin 8, w k • ⁅SerreH j, ⁅SerreH k, x⁆⁆ := by
      rw [hT_apply]
      show (LieModule.toEnd ℂ L8 M (SerreH j)) (∑ k : Fin 8, w k • ⁅SerreH k, x⁆)
        = ∑ k : Fin 8, w k • ⁅SerreH j, ⁅SerreH k, x⁆⁆
      rw [map_sum]
      exact Finset.sum_congr rfl (fun k _ => by rw [map_smul, LieModule.toEnd_apply_apply])
    rw [hT_apply, hTx]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have hinner : ⁅SerreH k, ⁅SerreH j, x⁆⁆ = ⁅SerreH j, ⁅SerreH k, x⁆⁆ := by
      rw [leibniz_lie (SerreH k) (SerreH j) x, serreLie_HH k j]
      simp
    rw [hinner]
  have hWmap : ∀ j : Fin 8, ∀ x ∈ W, ⁅SerreH j, x⁆ ∈ W := by
    intro j x hx
    obtain ⟨hxN, hxeig⟩ := hx
    have hxe : T x = lam0 • x := Module.End.mem_eigenspace_iff.mp hxeig
    refine ⟨N.lie_mem (x := SerreH j) hxN, ?_⟩
    refine Module.End.mem_eigenspace_iff.mpr ?_
    rw [hTW j x, hxe]
    show (LieModule.toEnd ℂ L8 M (SerreH j)) (lam0 • x)
      = lam0 • (LieModule.toEnd ℂ L8 M (SerreH j)) x
    rw [map_smul]
  have hcommT : ∀ i j : Fin 8,
      LieModule.toEnd ℂ L8 M (SerreH i) * LieModule.toEnd ℂ L8 M (SerreH j)
        = LieModule.toEnd ℂ L8 M (SerreH j) * LieModule.toEnd ℂ L8 M (SerreH i) := by
    intro i j
    ext x
    simp only [Module.End.mul_apply, LieModule.toEnd_apply_apply]
    rw [leibniz_lie (SerreH i) (SerreH j) x, serreLie_HH i j, zero_lie, zero_add,
      leibniz_lie (SerreH j) (SerreH i) x, serreLie_HH j i, zero_lie, zero_add]
  obtain ⟨x, nu, hxW, hxne, hxspec⟩ :=
    Commons.LinearAlgebra.End.exists_joint_eigenvector
      (fun j : Fin 8 => LieModule.toEnd ℂ L8 M (SerreH j)) hcommT W hWne hWmap
  have hEkill : ∀ i : Fin 8, ⁅SerreE i, x⁆ = 0 := by
    intro i
    by_contra hne
    obtain ⟨hxN, hxT⟩ := hxW
    have hxTe : T x = lam0 • x := Module.End.mem_eigenspace_iff.mp hxT
    have hEN : ⁅SerreE i, x⁆ ∈ N := N.lie_mem (x := SerreE i) hxN
    have hTE' : T (⁅SerreE i, x⁆) = (lam0 + 1) • ⁅SerreE i, x⁆ := by
      rw [hTE i x, hxTe]
      show (LieModule.toEnd ℂ L8 M (SerreE i)) (lam0 • x)
          + (LieModule.toEnd ℂ L8 M (SerreE i)) x
        = (lam0 + 1) • (LieModule.toEnd ℂ L8 M (SerreE i)) x
      rw [map_smul, add_smul, one_smul]
    have hmem : (lam0 + 1) ∈ {mu : ℂ | TN.HasEigenvalue mu} := by
      refine Module.End.hasEigenvalue_iff.mpr ?_
      rw [Submodule.ne_bot_iff]
      refine ⟨⟨⁅SerreE i, x⁆, hEN⟩, ?_, ?_⟩
      · refine Module.End.mem_eigenspace_iff.mpr (Subtype.ext ?_)
        rw [hTNdef]
        exact hTE'
      · simpa using hne
    have hle := hlam0max (lam0 + 1) hmem
    simp only [Complex.add_re, Complex.one_re] at hle
    linarith
  have hnat : ∀ i : Fin 8, ∃ n : ℕ, nu i = (n : ℂ) := by
    intro i
    exact (show IsSl2Triple.HasPrimitiveVectorWith (isSl2Triple_serre i) x (nu i) from
      { ne_zero := hxne, lie_h := hxspec i, lie_e := hEkill i }).exists_nat
  choose n hn using hnat
  refine ⟨x, fun i => (n i : ℤ), hxW.1, hxne, ?_, hEkill, ?_⟩
  · intro i
    have h1 : ⁅SerreH i, x⁆ = nu i • x := hxspec i
    rw [h1, hn i]
    simp
  · intro i
    exact Int.natCast_nonneg (n i)

end Commons.Algebra.Lie.SerreConstruction
