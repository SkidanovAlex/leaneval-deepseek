import Mathlib
import Submission.Commons.Algebra.Lie.Sl2.string_of_locallyNilpotent
import Submission.Commons.Algebra.Lie.ad_locallyNilpotent_of_generators
import Submission.Commons.Algebra.Lie.SerreConstruction.eq_top_of_lieSubalgebra_of_generators
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_root_weightSpace_finrank_eq_one

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

noncomputable section
open CartanMatrix

namespace Commons.Algebra.Lie.SerreConstruction

private def alphaZ (i : Fin 8) : Fin 8 → ℤ := fun j => CartanMatrix.E₈ i j

private lemma mem_wtSpace_iff {μ : Fin 8 → ℤ} {x : L8} :
    x ∈ wtSpace μ ↔ ∀ i, ⁅SerreH i, x⁆ = (μ i : ℂ) • x := by
  simp only [wtSpace, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LieAlgebra.ad_apply, sub_eq_zero]
  exact Iff.rfl

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

set_option backward.isDefEq.respectTransparency false in
/-- The Serre generators span the algebra as a Lie subalgebra. -/
private theorem lieSpan_generators_top :
    LieSubalgebra.lieSpan ℂ L8 (Set.range (fun g : CartanMatrix.Generators (Fin 8) =>
      LieSubmodule.Quotient.mk (N := lieJ) (FreeLieAlgebra.of ℂ g))) = ⊤ := by
  refine eq_top_of_lieSubalgebra_of_generators CartanMatrix.E₈ _ ?_
  intro g
  exact LieSubalgebra.subset_lieSpan (Set.mem_range_self g)

/-- `ad (e i)` kills each generator after at most three applications. -/
private lemma adE_pow_generator (i : Fin 8) (g : CartanMatrix.Generators (Fin 8)) :
    ∃ n : ℕ, (((LieAlgebra.ad ℂ L8 (SerreE i))^n)
      (LieSubmodule.Quotient.mk (N := lieJ) (FreeLieAlgebra.of ℂ g))) = 0 := by
  have hadH : ∀ j, (LieAlgebra.ad ℂ L8 (SerreE i)) (SerreH j) = (-(E8 j i)) • SerreE i := by
    intro j
    rw [LieAlgebra.ad_apply, ← lie_skew, serreLie_H_E, neg_smul, zsmul_int_eq]
  have hadE : ∀ j, ((LieAlgebra.ad ℂ L8 (SerreE i))^2) (SerreE j) = 0 := fun j =>
    serreLie_adE_sq i j
  have hadF : ∀ j, (LieAlgebra.ad ℂ L8 (SerreE i)) (SerreF j)
      = if i = j then SerreH i else 0 := by
    intro j
    rw [LieAlgebra.ad_apply, serreLie_E_F]
  cases g with
  | H j =>
    refine ⟨2, ?_⟩
    rw [show (LieSubmodule.Quotient.mk (N := lieJ) (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H j)))
        = SerreH j from rfl]
    change (LieAlgebra.ad ℂ L8 (SerreE i)) ((LieAlgebra.ad ℂ L8 (SerreE i)) (SerreH j)) = 0
    rw [hadH j, map_zsmul, LieAlgebra.ad_apply, lie_self, smul_zero]
  | E j =>
    refine ⟨2, ?_⟩
    rw [show (LieSubmodule.Quotient.mk (N := lieJ) (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E j)))
        = SerreE j from rfl]
    exact hadE j
  | F j =>
    refine ⟨3, ?_⟩
    rw [show (LieSubmodule.Quotient.mk (N := lieJ) (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F j)))
        = SerreF j from rfl]
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one, Module.End.mul_apply]
    change (LieAlgebra.ad ℂ L8 (SerreE i)) ((LieAlgebra.ad ℂ L8 (SerreE i))
      ((LieAlgebra.ad ℂ L8 (SerreE i)) (SerreF j))) = 0
    rw [hadF j]
    by_cases hij : i = j
    · rw [if_pos hij]
      change (LieAlgebra.ad ℂ L8 (SerreE i)) ((LieAlgebra.ad ℂ L8 (SerreE i)) (SerreH i)) = 0
      rw [hadH i, map_zsmul, LieAlgebra.ad_apply, lie_self, smul_zero]
    · rw [if_neg hij]
      simp

/-- `ad (e i)` is locally nilpotent on `e₈`. -/
private theorem ad_SerreE_locallyNilpotent (i : Fin 8) :
    ∀ x : L8, ∃ n : ℕ, (((LieAlgebra.ad ℂ L8 (SerreE i))^n) x) = 0 := by
  have hx : ⁅SerreE i, SerreE i⁆ = 0 := lie_self _
  have hS := lieSpan_generators_top
  have hloc : ∀ y ∈ (Set.range (fun g : CartanMatrix.Generators (Fin 8) =>
      LieSubmodule.Quotient.mk (N := lieJ) (FreeLieAlgebra.of ℂ g))),
      ∃ n, (((LieAlgebra.ad ℂ L8 (SerreE i))^n) y) = 0 := by
    rintro y ⟨g, rfl⟩
    exact adE_pow_generator i g
  exact Commons.Algebra.Lie.ad_locallyNilpotent_of_generators hx hS hloc



/-- `ad (f i)` kills each generator after at most three applications. -/
private lemma adF_pow_generator (i : Fin 8) (g : CartanMatrix.Generators (Fin 8)) :
    ∃ n : ℕ, (((LieAlgebra.ad ℂ L8 (SerreF i))^n)
      (LieSubmodule.Quotient.mk (N := lieJ) (FreeLieAlgebra.of ℂ g))) = 0 := by
  have hadH : ∀ j, (LieAlgebra.ad ℂ L8 (SerreF i)) (SerreH j) = (E8 j i) • SerreF i := by
    intro j
    rw [LieAlgebra.ad_apply, ← lie_skew, serreLie_H_F, neg_smul, neg_neg, zsmul_int_eq]
  have hadF : ∀ j, ((LieAlgebra.ad ℂ L8 (SerreF i))^2) (SerreF j) = 0 := fun j =>
    serreLie_adF_sq i j
  have hadE : ∀ j, (LieAlgebra.ad ℂ L8 (SerreF i)) (SerreE j)
      = if i = j then -SerreH i else 0 := by
    intro j
    rw [LieAlgebra.ad_apply, ← lie_skew, serreLie_E_F]
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (Ne.symm hij), if_neg hij, neg_zero]
  cases g with
  | H j =>
    refine ⟨2, ?_⟩
    rw [show (LieSubmodule.Quotient.mk (N := lieJ) (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H j)))
        = SerreH j from rfl]
    change (LieAlgebra.ad ℂ L8 (SerreF i)) ((LieAlgebra.ad ℂ L8 (SerreF i)) (SerreH j)) = 0
    rw [hadH j, map_zsmul, LieAlgebra.ad_apply, lie_self, smul_zero]
  | F j =>
    refine ⟨2, ?_⟩
    rw [show (LieSubmodule.Quotient.mk (N := lieJ) (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F j)))
        = SerreF j from rfl]
    exact hadF j
  | E j =>
    refine ⟨3, ?_⟩
    rw [show (LieSubmodule.Quotient.mk (N := lieJ) (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E j)))
        = SerreE j from rfl]
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one, Module.End.mul_apply]
    change (LieAlgebra.ad ℂ L8 (SerreF i)) ((LieAlgebra.ad ℂ L8 (SerreF i))
      ((LieAlgebra.ad ℂ L8 (SerreF i)) (SerreE j))) = 0
    rw [hadE j]
    by_cases hij : i = j
    · rw [if_pos hij]
      change (LieAlgebra.ad ℂ L8 (SerreF i)) ((LieAlgebra.ad ℂ L8 (SerreF i)) (-SerreH i)) = 0
      rw [map_neg, hadH i, map_neg, map_zsmul, LieAlgebra.ad_apply, lie_self, smul_zero,
        neg_zero]
    · rw [if_neg hij]
      simp

/-- `ad (f i)` is locally nilpotent on `e₈`. -/
private theorem ad_SerreF_locallyNilpotent (i : Fin 8) :
    ∀ x : L8, ∃ n : ℕ, (((LieAlgebra.ad ℂ L8 (SerreF i))^n) x) = 0 := by
  have hx : ⁅SerreF i, SerreF i⁆ = 0 := lie_self _
  have hS := lieSpan_generators_top
  have hloc : ∀ y ∈ (Set.range (fun g : CartanMatrix.Generators (Fin 8) =>
      LieSubmodule.Quotient.mk (N := lieJ) (FreeLieAlgebra.of ℂ g))),
      ∃ n, (((LieAlgebra.ad ℂ L8 (SerreF i))^n) y) = 0 := by
    rintro y ⟨g, rfl⟩
    exact adF_pow_generator i g
  exact Commons.Algebra.Lie.ad_locallyNilpotent_of_generators hx hS hloc

/-- The action of `ad (H j)` on the `E i`-string through a weight vector. -/
private lemma lie_H_adE_pow {μ : Fin 8 → ℤ} {x : L8} (hx : x ∈ wtSpace μ) (i j : Fin 8) (m : ℕ) :
    ⁅SerreH j, (((LieAlgebra.ad ℂ L8 (SerreE i))^m) x)⁆ =
      (((μ j + (m : ℤ) * E8 j i : ℤ) : ℂ)) • (((LieAlgebra.ad ℂ L8 (SerreE i))^m) x) := by
  induction m with
  | zero => simpa using (mem_wtSpace_iff.mp hx j)
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply]
    have hleib : ⁅SerreH j, (LieAlgebra.ad ℂ L8 (SerreE i))
          (((LieAlgebra.ad ℂ L8 (SerreE i))^m) x)⁆ =
        ⁅(LieAlgebra.ad ℂ L8 (SerreH j)) (SerreE i), (((LieAlgebra.ad ℂ L8 (SerreE i))^m) x)⁆
          + (LieAlgebra.ad ℂ L8 (SerreE i))
            (⁅SerreH j, (((LieAlgebra.ad ℂ L8 (SerreE i))^m) x)⁆) := by
      rw [← LieAlgebra.ad_apply (R := ℂ), ← LieAlgebra.ad_apply (R := ℂ), ← LieAlgebra.ad_apply (R := ℂ)]
      exact leibniz_lie (SerreH j) (SerreE i) (((LieAlgebra.ad ℂ L8 (SerreE i))^m) x)
    rw [hleib, ih]
    have hHE : (LieAlgebra.ad ℂ L8 (SerreH j)) (SerreE i) = (E8 j i) • SerreE i := by
      rw [LieAlgebra.ad_apply, serreLie_H_E]
    rw [hHE, smul_lie, map_smul]
    rw [show ⁅SerreE i, (((LieAlgebra.ad ℂ L8 (SerreE i))^m) x)⁆
        = (LieAlgebra.ad ℂ L8 (SerreE i)) (((LieAlgebra.ad ℂ L8 (SerreE i))^m) x) from rfl]
    rw [zsmul_int_eq (E8 j i) _]
    rw [← add_smul]
    congr 1
    push_cast
    ring



/-- The action of `ad (H j)` on the `F i`-string through a weight vector. -/
private lemma lie_H_adF_pow {μ : Fin 8 → ℤ} {x : L8} (hx : x ∈ wtSpace μ) (i j : Fin 8) (m : ℕ) :
    ⁅SerreH j, (((LieAlgebra.ad ℂ L8 (SerreF i))^m) x)⁆ =
      (((μ j - (m : ℤ) * E8 j i : ℤ) : ℂ)) • (((LieAlgebra.ad ℂ L8 (SerreF i))^m) x) := by
  induction m with
  | zero => simpa using (mem_wtSpace_iff.mp hx j)
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply]
    have hleib : ⁅SerreH j, (LieAlgebra.ad ℂ L8 (SerreF i))
          (((LieAlgebra.ad ℂ L8 (SerreF i))^m) x)⁆ =
        ⁅(LieAlgebra.ad ℂ L8 (SerreH j)) (SerreF i), (((LieAlgebra.ad ℂ L8 (SerreF i))^m) x)⁆
          + (LieAlgebra.ad ℂ L8 (SerreF i))
            (⁅SerreH j, (((LieAlgebra.ad ℂ L8 (SerreF i))^m) x)⁆) := by
      rw [← LieAlgebra.ad_apply (R := ℂ), ← LieAlgebra.ad_apply (R := ℂ), ← LieAlgebra.ad_apply (R := ℂ)]
      exact leibniz_lie (SerreH j) (SerreF i) (((LieAlgebra.ad ℂ L8 (SerreF i))^m) x)
    rw [hleib, ih]
    have hHF : (LieAlgebra.ad ℂ L8 (SerreH j)) (SerreF i) = (-(E8 j i)) • SerreF i := by
      rw [LieAlgebra.ad_apply, serreLie_H_F]
    rw [hHF, smul_lie, map_smul]
    rw [show ⁅SerreF i, (((LieAlgebra.ad ℂ L8 (SerreF i))^m) x)⁆
        = (LieAlgebra.ad ℂ L8 (SerreF i)) (((LieAlgebra.ad ℂ L8 (SerreF i))^m) x) from rfl]
    rw [zsmul_int_eq (-(E8 j i)) _]
    rw [← add_smul]
    congr 1
    push_cast
    ring

/-- **The descent lemma.**  If `ν` is a weight of the adjoint representation of the
Serre-constructed `e₈` with `ν i ≥ 1`, then `ν - αᵢ` is again a weight.  (`αᵢ` is represented by
the `i`-th row `j ↦ CartanMatrix.E₈ i j` of the Cartan matrix.) -/
theorem e8_weightSpace_descent (ν : Fin 8 → ℤ) (i : Fin 8) (hν : 1 ≤ ν i)
    (h : Commons.Algebra.Lie.SerreConstruction.wtSpace ν ≠ ⊥) :
    Commons.Algebra.Lie.SerreConstruction.wtSpace (ν - fun j => CartanMatrix.E₈ i j) ≠ ⊥ := by

  classical
  obtain ⟨x, hx, hxne⟩ := (Submodule.ne_bot_iff _).mp h
  obtain ⟨n0, hn0⟩ := ad_SerreE_locallyNilpotent i x
  have hex : ∃ n, ((((LieAlgebra.ad ℂ L8 (SerreE i))^n) x)) = 0 := ⟨n0, hn0⟩
  obtain ⟨k, hkspec, hkmin⟩ : ∃ k, ((((LieAlgebra.ad ℂ L8 (SerreE i))^k) x)) = 0 ∧
      ∀ m < k, ((((LieAlgebra.ad ℂ L8 (SerreE i))^m) x)) ≠ 0 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · exact absurd (by simpa [h0] using hkspec) hxne
    · exact hpos
  set y : L8 := ((((LieAlgebra.ad ℂ L8 (SerreE i))^(k-1)) x)) with hy
  have hyne : y ≠ 0 := hkmin (k - 1) (by omega)
  have hstep : ((((LieAlgebra.ad ℂ L8 (SerreE i))^k) x))
      = (LieAlgebra.ad ℂ L8 (SerreE i)) ((((LieAlgebra.ad ℂ L8 (SerreE i))^(k-1)) x)) := by
    conv_lhs => rw [show k = (k - 1) + 1 from (Nat.succ_pred_eq_of_pos hkpos).symm]
    rw [pow_succ', Module.End.mul_apply]
  have hykill : ⁅SerreE i, y⁆ = 0 := by
    rw [← LieAlgebra.ad_apply (R := ℂ), hy, ← hstep]
    exact hkspec
  have hyweight : ⁅SerreH i, y⁆ = ((ν i : ℂ) + 2 * ((k - 1 : ℕ) : ℂ)) • y := by
    have h := lie_H_adE_pow hx i i (k - 1)
    rw [hy, h]
    congr 1
    rw [show E8 i i = 2 from E8_diag i]
    push_cast
    ring
  have hteE : (LieModule.toEnd ℂ L8 L8 (SerreE i)) = (LieAlgebra.ad ℂ L8 (SerreE i)) := by
    ext z; rw [LieModule.toEnd_apply_apply, LieAlgebra.ad_apply]
  have hteF : (LieModule.toEnd ℂ L8 L8 (SerreF i)) = (LieAlgebra.ad ℂ L8 (SerreF i)) := by
    ext z; rw [LieModule.toEnd_apply_apply, LieAlgebra.ad_apply]
  obtain ⟨N, hNpos, hNcast, hNzero, hNne⟩ :=
    Commons.Algebra.Lie.Sl2.string_of_locallyNilpotent (t := isSl2Triple i)
      (he := by rw [hteE]; exact ad_SerreE_locallyNilpotent i)
      (hf := by rw [hteF]; exact ad_SerreF_locallyNilpotent i)
      y hyne hykill (((ν i : ℂ) + 2 * ((k - 1 : ℕ) : ℂ))) hyweight
  rw [hteF] at hNzero hNne
  have hklt : k < N := by
    have h1 : (N : ℂ) = (((ν i + 2 * ((k - 1 : ℕ) : ℤ) + 1 : ℤ)) : ℂ) := by
      rw [hNcast]; push_cast; ring
    have h1' : ((N : ℤ) : ℂ) = (((ν i + 2 * ((k - 1 : ℕ) : ℤ) + 1 : ℤ)) : ℂ) := by
      rw [show ((N : ℤ) : ℂ) = (N : ℂ) from by push_cast; ring, h1]
    have h2 : (N : ℤ) = ν i + 2 * ((k - 1 : ℕ) : ℤ) + 1 := Int.cast_injective h1'
    have h3 : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
    omega
  have hkey : ∀ m : ℕ, ((((LieAlgebra.ad ℂ L8 (SerreF i))^m) y)) ∈
      wtSpace (fun j => ν j + (((k - 1 : ℕ) : ℤ) - (m : ℤ)) * E8 i j) := by
    intro m
    induction m with
    | zero =>
      have hbase : y ∈ wtSpace (fun j => ν j + (((k - 1 : ℕ) : ℤ) - ((0 : ℕ) : ℤ)) * E8 i j) := by
        rw [hy, mem_wtSpace_iff]
        intro j
        have h := lie_H_adE_pow hx i j (k - 1)
        rw [h, E8_symm]
        congr 1
      simpa using hbase
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, LieAlgebra.ad_apply]
      have hmem := bracket_mem_wtSpace (SerreF_mem_wtSpace i) ih
      convert hmem using 1
      congr 1
      funext j
      simp only [Pi.add_apply, Pi.neg_apply, alphaZ]
      push_cast
      ring
  refine (Submodule.ne_bot_iff _).mpr ⟨_, ?_, hNne k hklt⟩
  convert hkey k using 2
  ext j
  have hk1 : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
  rw [Pi.sub_apply, hk1]
  ring

end Commons.Algebra.Lie.SerreConstruction
