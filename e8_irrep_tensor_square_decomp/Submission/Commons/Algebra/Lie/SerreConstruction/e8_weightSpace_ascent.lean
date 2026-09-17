import Mathlib
import Submission.Commons.Algebra.Lie.Sl2.string_of_locallyNilpotent
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_root_weightSpace_finrank_eq_one

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

noncomputable section
open CartanMatrix

namespace Commons.Algebra.Lie.SerreConstruction

private lemma mem_wtSpace_iff {μ : Fin 8 → ℤ} {x : L8} :
    x ∈ wtSpace μ ↔ ∀ i, ⁅SerreH i, x⁆ = (μ i : ℂ) • x := by
  simp only [wtSpace, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LieAlgebra.ad_apply, sub_eq_zero]
  exact Iff.rfl

private def alphaZ (i : Fin 8) : Fin 8 → ℤ := fun j => CartanMatrix.E₈ i j

private lemma SerreE_mem_wtSpace (i : Fin 8) : SerreE i ∈ wtSpace (alphaZ i) := by
  rw [mem_wtSpace_iff]
  intro j
  rw [serreLie_H_E, show (alphaZ i) j = E8 j i from by simp only [alphaZ, E8_symm]]
  exact zsmul_int_eq (E8 j i) (SerreE i)

private lemma SerreF_mem_wtSpace (i : Fin 8) : SerreF i ∈ wtSpace (- alphaZ i) := by
  rw [mem_wtSpace_iff]
  intro j
  rw [serreLie_H_F,
    show (-(alphaZ i)) j = -(E8 j i) from by simp only [Pi.neg_apply, alphaZ, E8_symm]]
  exact zsmul_int_eq (-(E8 j i)) (SerreF i)

private lemma bracket_mem_wtSpace {μ ν : Fin 8 → ℤ} {x y : L8} (hx : x ∈ wtSpace μ)
    (hy : y ∈ wtSpace ν) : ⁅x, y⁆ ∈ wtSpace (μ + ν) := by
  rw [mem_wtSpace_iff] at hx hy ⊢
  intro i
  rw [leibniz_lie, hx i, hy i, smul_lie, lie_smul, Pi.add_apply, Int.cast_add, add_smul]

private lemma SerreH_ne_zero (i : Fin 8) : SerreH i ≠ 0 :=
  e8_H_linearIndependent.ne_zero i

private lemma isSl2Triple (i : Fin 8) : IsSl2Triple (SerreH i) (SerreE i) (SerreF i) where
  h_ne_zero := SerreH_ne_zero i
  lie_e_f := by rw [serreLie_E_F, if_pos rfl]
  lie_h_e_nsmul := by
    rw [serreLie_H_E, show E8 i i = 2 from E8_diag i, zsmul_int_eq]
    rw [← Nat.cast_smul_eq_nsmul (R := ℂ) 2 (SerreE i)]
    norm_num
  lie_h_f_nsmul := by
    rw [serreLie_H_F, show E8 i i = 2 from E8_diag i]
    rw [show -((2 : ℤ)) = (-(2 : ℤ)) from rfl, zsmul_int_eq]
    rw [← Nat.cast_smul_eq_nsmul (R := ℂ) 2 (SerreF i)]
    norm_num

/-- **The ascent lemma.**  If `ν` is a weight of the adjoint representation of the
Serre-constructed `e₈` with `ν i ≤ -1`, then `ν + αᵢ` is again a weight.  (`αᵢ` is represented by
the `i`-th row `j ↦ CartanMatrix.E₈ i j` of the Cartan matrix.)  This is the mirror image of
`e8_weightSpace_descent`, obtained by running the `𝔰𝔩₂`-string argument on the `fᵢ`-string instead
of the `eᵢ`-string. -/
theorem e8_weightSpace_ascent (ν : Fin 8 → ℤ) (i : Fin 8) (hν : ν i ≤ -1)
    (h : Commons.Algebra.Lie.SerreConstruction.wtSpace ν ≠ ⊥) :
    Commons.Algebra.Lie.SerreConstruction.wtSpace (ν + fun j => CartanMatrix.E₈ i j) ≠ ⊥ := by
  classical
  obtain ⟨x, hx, hxne⟩ := (Submodule.ne_bot_iff _).mp h
  obtain ⟨n0, hn0⟩ := hloc_F i x
  have hex : ∃ n, (((LieAlgebra.ad ℂ L8 (SerreF i))^n) x) = 0 := ⟨n0, hn0⟩
  obtain ⟨k, hkspec, hkmin⟩ : ∃ k, ((((LieAlgebra.ad ℂ L8 (SerreF i))^k) x)) = 0 ∧
      ∀ m < k, ((((LieAlgebra.ad ℂ L8 (SerreF i))^m) x)) ≠ 0 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · exact absurd (by simpa [h0] using hkspec) hxne
    · exact hpos
  set y : L8 := ((((LieAlgebra.ad ℂ L8 (SerreF i))^(k-1)) x)) with hy
  have hyne : y ≠ 0 := hkmin (k - 1) (by omega)
  have hstep : ((((LieAlgebra.ad ℂ L8 (SerreF i))^k) x))
      = (LieAlgebra.ad ℂ L8 (SerreF i)) ((((LieAlgebra.ad ℂ L8 (SerreF i))^(k-1)) x)) := by
    conv_lhs => rw [show k = (k - 1) + 1 from (Nat.succ_pred_eq_of_pos hkpos).symm]
    rw [pow_succ', Module.End.mul_apply]
  have hykill : ⁅SerreF i, y⁆ = 0 := by
    rw [← LieAlgebra.ad_apply (R := ℂ), hy, ← hstep]
    exact hkspec
  -- The F-string through `x`, tracking the weights in all eight coordinates.
  have hFkey : ∀ m : ℕ, ((((LieAlgebra.ad ℂ L8 (SerreF i))^m) x)) ∈
      wtSpace (fun j => ν j - (m : ℤ) * E8 i j) := by
    intro m
    induction m with
    | zero => simpa using hx
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, LieAlgebra.ad_apply]
      have hmem := bracket_mem_wtSpace (SerreF_mem_wtSpace i) ih
      convert hmem using 1
      congr 1
      funext j
      simp only [Pi.add_apply, Pi.neg_apply, alphaZ]
      push_cast
      ring
  have hyFmem : y ∈ wtSpace (fun j => ν j - (((k - 1 : ℕ) : ℤ)) * E8 i j) := by
    rw [hy]; exact hFkey (k - 1)
  -- The `i`-th coordinate of the weight of `y` is `ν i - 2 (k - 1) < 0`.
  have hyH : ⁅SerreH i, y⁆ = (((ν i) - (((k - 1 : ℕ) : ℤ)) * 2 : ℤ) : ℂ) • y := by
    have h' := mem_wtSpace_iff.mp hyFmem i
    rw [E8_diag] at h'
    exact h'
  -- The primitive weight of `y` for the triple `(-hᵢ, fᵢ, eᵢ)`.
  set μ : ℂ := ((-(ν i) + 2 * ((k - 1 : ℕ) : ℤ) : ℤ) : ℂ) with hμdef
  have hyweight : ⁅-SerreH i, y⁆ = μ • y := by
    rw [neg_lie, hyH, ← neg_smul, hμdef]
    congr 1
    push_cast
    ring
  have hteE : (LieModule.toEnd ℂ L8 L8 (SerreE i)) = (LieAlgebra.ad ℂ L8 (SerreE i)) := by
    ext z; rw [LieModule.toEnd_apply_apply, LieAlgebra.ad_apply]
  have hteF : (LieModule.toEnd ℂ L8 L8 (SerreF i)) = (LieAlgebra.ad ℂ L8 (SerreF i)) := by
    ext z; rw [LieModule.toEnd_apply_apply, LieAlgebra.ad_apply]
  -- The `𝔰𝔩₂`-string lemma applied to the triple `(-hᵢ, fᵢ, eᵢ)`: the `eᵢ`-string through `y` is
  -- finite of length `μ + 1 = -ν i + 2(k-1) + 1`.
  obtain ⟨N, hNpos, hNcast, hNzero, hNne⟩ :=
    Commons.Algebra.Lie.Sl2.string_of_locallyNilpotent (t := (isSl2Triple i).symm)
      (he := by rw [hteF]; exact hloc_F i)
      (hf := by rw [hteE]; exact hloc_E i)
      y hyne hykill μ hyweight
  rw [hteE] at hNzero hNne
  -- Since `ν i ≤ -1`, the index `k` is strictly below the length `N`.
  have hklt : k < N := by
    have h1 : (N : ℂ) = (((-(ν i) + 2 * ((k - 1 : ℕ) : ℤ) + 1 : ℤ)) : ℂ) := by
      rw [hNcast]; rw [hμdef]; push_cast; ring
    have h1' : ((N : ℤ) : ℂ) = (((-(ν i) + 2 * ((k - 1 : ℕ) : ℤ) + 1 : ℤ)) : ℂ) := by
      rw [show ((N : ℤ) : ℂ) = (N : ℂ) from by push_cast; ring, h1]
    have h2 : (N : ℤ) = -(ν i) + 2 * ((k - 1 : ℕ) : ℤ) + 1 := Int.cast_injective h1'
    have h3 : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
    omega
  -- The `E`-string through `y`, tracking the weights in all eight coordinates.
  have hEkey : ∀ m : ℕ, ((((LieAlgebra.ad ℂ L8 (SerreE i))^m) y)) ∈
      wtSpace (fun j => ν j - (((k - 1 : ℕ) : ℤ)) * E8 i j + (m : ℤ) * E8 i j) := by
    intro m
    induction m with
    | zero => simpa using hyFmem
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, LieAlgebra.ad_apply]
      have hmem := bracket_mem_wtSpace (SerreE_mem_wtSpace i) ih
      convert hmem using 1
      congr 1
      funext j
      simp only [Pi.add_apply, alphaZ]
      push_cast
      ring
  have hwt_eq : (fun j => ν j - (((k - 1 : ℕ) : ℤ)) * E8 i j + (k : ℤ) * E8 i j)
      = (ν + fun j => E8 i j) := by
    funext j
    have h3 : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [h3]
    ring
  refine (Submodule.ne_bot_iff _).mpr ⟨((((LieAlgebra.ad ℂ L8 (SerreE i))^k) y)), ?_, hNne k hklt⟩
  rw [← hwt_eq]
  exact hEkey k

end Commons.Algebra.Lie.SerreConstruction
