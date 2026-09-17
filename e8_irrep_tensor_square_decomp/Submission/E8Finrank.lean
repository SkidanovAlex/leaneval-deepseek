import Submission.E8Multiplicity
import Submission.Commons.LinearAlgebra.Matrix.Cartan.e8_lattice_count
import Submission.Commons.LinearAlgebra.Matrix.Cartan.e8_lattice_mnorm_sum
import Submission.Commons.LinearAlgebra.Matrix.Cartan.e8_lattice_toNat_sum

/-!
# `dim L(ω₁+ω₈) = 779247`

The character of `L = V ⧸ N` is `mfun` (`Submission.E8Multiplicity.mfun_eq_mul`).  This file
converts the character into the *dimension*:

* for a weight `w₀` and another weight `w ≠ w₀`, the operator
  `killerW N w₀ w j = (w₀ j - w j)⁻¹ (H_j - w_j)` kills `Lwt N w` and fixes `Lwt N w₀` (for `j`
  with `w j ≠ w₀ j`); products of these prove the **independence** of the weight spaces
  (`disjoint_Lwt`);
* hence `finrank ℂ (V ⧸ N) = ∑_{w ∈ S} dmul N w` for any finite `S` containing the support
  (`finrank_eq_sum_dmul`);
* the support is contained in the lattice points of `qq ≤ 10` (`E8Support.mfun_ne_zero_iff`), so
  the sum can be evaluated with `e8_lattice_count` and `e8_lattice_mnorm_sum` — giving `779247`.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

noncomputable section
open scoped BigOperators

namespace Submission.E8Finrank

open Submission.E8WeightSpaces Submission.VermaWeight
open Submission.E8Casimir
open Submission.E8Freudenthal
open Submission.E8Character
open Submission.WeylReflect Submission.WeylWeights
open UniversalEnvelopingAlgebra
open Submission.E8Multiplicity Submission.E8Numerics

/-! ## The killer operators -/

/-- The operator `(w₀ j - w j)⁻¹ (H_j - w_j)`: it kills the weight space of `w` and (when
`w j ≠ w₀ j`) fixes the weight space of `w₀`. -/
noncomputable def killerW (N : Submodule U V) (w₀ w : Fin 8 → ℤ) (j : Fin 8) :
    Module.End ℂ (V ⧸ N) :=
  (((w₀ j - w j : ℤ)) : ℂ)⁻¹ •
    (endU N (Submission.E8Weights.h j) - (((w j : ℤ)) : ℂ) • (1 : Module.End ℂ (V ⧸ N)))

lemma killerW_apply (N : Submodule U V) (w₀ w : Fin 8 → ℤ) (j : Fin 8) {μ : Fin 8 → ℤ}
    {x : V ⧸ N} (hx : x ∈ Lwt N μ) :
    killerW N w₀ w j x
      = ((((w₀ j - w j : ℤ)) : ℂ)⁻¹ * ((((μ j : ℤ)) : ℂ) - (((w j : ℤ)) : ℂ))) • x := by
  rw [killerW, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, mem_Lwt_iff.mp hx j, ← sub_smul, smul_smul]

lemma killerW_mem (N : Submodule U V) (w₀ w : Fin 8 → ℤ) (j : Fin 8) {μ : Fin 8 → ℤ}
    {x : V ⧸ N} (hx : x ∈ Lwt N μ) : killerW N w₀ w j x ∈ Lwt N μ := by
  rw [killerW_apply N w₀ w j hx]
  exact Submodule.smul_mem _ _ hx

lemma killerW_kills (N : Submodule U V) (w₀ w : Fin 8 → ℤ) (j : Fin 8) {x : V ⧸ N}
    (hx : x ∈ Lwt N w) : killerW N w₀ w j x = 0 := by
  rw [killerW_apply N w₀ w j hx]
  have : ((((w j : ℤ)) : ℂ) - (((w j : ℤ)) : ℂ)) = 0 := sub_self _
  rw [this, mul_zero, zero_smul]

lemma killerW_fixes (N : Submodule U V) {w₀ w : Fin 8 → ℤ} {j : Fin 8} (hj : w j ≠ w₀ j)
    {x : V ⧸ N} (hx : x ∈ Lwt N w₀) : killerW N w₀ w j x = x := by
  rw [killerW_apply N w₀ w j hx]
  have hne' : ((((w₀ j : ℤ)) : ℂ)) - ((((w j : ℤ)) : ℂ)) ≠ 0 := by
    intro h
    have h2 : (((w₀ j : ℤ)) : ℂ) = (((w j : ℤ)) : ℂ) := sub_eq_zero.mp h
    exact hj (Int.cast_injective h2).symm
  have hcast : ((((w₀ j - w j : ℤ)) : ℂ)) = ((((w₀ j : ℤ)) : ℂ)) - ((((w j : ℤ)) : ℂ)) :=
    Int.cast_sub ..
  rw [hcast, inv_mul_cancel₀ hne', one_smul]

/-! ## Independence of the weight spaces -/

open UniversalEnvelopingAlgebra in
/-- **The killer product.**  For a finite set `s` of weights not containing `w₀` there is an
endomorphism `P` of `V ⧸ N` which preserves all weight spaces, fixes `Lwt N w₀` and kills
`Lwt N w` for every `w ∈ s`. -/
lemma exists_killer (N : Submodule U V) (s : Finset (Fin 8 → ℤ)) (w₀ : Fin 8 → ℤ)
    (hne : ∀ w ∈ s, w ≠ w₀) :
    ∃ P : Module.End ℂ (V ⧸ N),
      (∀ μ : Fin 8 → ℤ, ∀ y : V ⧸ N, y ∈ Lwt N μ → P y ∈ Lwt N μ) ∧
      (∀ y : V ⧸ N, y ∈ Lwt N w₀ → P y = y) ∧
      (∀ w ∈ s, ∀ y : V ⧸ N, y ∈ Lwt N w → P y = 0) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨1, fun μ y hy => by simpa using hy, fun y hy => rfl, ?_⟩
      intro w hw
      exact absurd hw (Finset.notMem_empty w)
  | insert a s' ha ih =>
      obtain ⟨P', hpres', hfix', hkill'⟩ := ih (fun w hw => hne w (Finset.mem_insert_of_mem hw))
      obtain ⟨j, hj⟩ : ∃ j : Fin 8, a j ≠ w₀ j :=
        Function.ne_iff.mp (hne a (Finset.mem_insert_self a s'))
      refine ⟨(killerW N w₀ a j).comp P', ?_, ?_, ?_⟩
      · intro μ y hy
        exact killerW_mem N w₀ a j (hpres' μ y hy)
      · intro y hy
        simp only [LinearMap.comp_apply]
        rw [hfix' y hy]
        exact killerW_fixes N hj hy
      · intro w hw y hy
        simp only [LinearMap.comp_apply]
        rcases Finset.mem_insert.mp hw with h | h
        · rw [h] at hy
          exact killerW_kills N w₀ a j (hpres' a y hy)
        · rw [hkill' w h y hy, map_zero]

open UniversalEnvelopingAlgebra in
/-- **The weight spaces of `L = V ⧸ N` are independent.** -/
theorem disjoint_Lwt (N : Submodule U V) (S : Finset (Fin 8 → ℤ)) (w₀ : Fin 8 → ℤ) :
    Disjoint (Lwt N w₀) ((S.erase w₀).sup fun w => Lwt N w) := by
  obtain ⟨P, hpres, hfix, hkill⟩ :=
    exists_killer N (S.erase w₀) w₀ (fun w hw => Finset.ne_of_mem_erase hw)
  rw [disjoint_iff]
  refine eq_bot_iff.mpr fun x hx => ?_
  obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
  rw [Submodule.mem_bot]
  have h1 : P x = x := hfix x hx1
  have h2 : P x = 0 := by
    have hle : (S.erase w₀).sup (fun w => Lwt N w) ≤ P.ker :=
      Finset.sup_le fun w hw => fun y hy => hkill w hw y hy
    exact hle hx2
  rw [← h1, h2]


/-! ## The dimension is the sum of the weight multiplicities -/

lemma finrank_sup_Lwt (N : Submodule U V) (S : Finset (Fin 8 → ℤ)) :
    Module.finrank ℂ ↥(S.sup fun w => Lwt N w) = ∑ w ∈ S, dmul N w := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      rw [Finset.sup_empty, Finset.sum_empty]
      exact Module.finrank_zero_of_subsingleton
  | insert a s' ha ih =>
      rw [Finset.sup_insert, Finset.sum_insert ha]
      have hd := disjoint_Lwt N s' a
      rw [Finset.erase_eq_self.mpr ha] at hd
      have h2 := Submodule.finrank_sup_add_finrank_inf_eq (Lwt N a)
        (s'.sup fun w => Lwt N w)
      rw [disjoint_iff.mp hd, finrank_bot, add_zero] at h2
      rw [h2, ih]

/-- **The dimension of `L = V ⧸ N` is the sum of the multiplicities** over any finite set of
weights containing the support. -/
theorem finrank_eq_sum_dmul (N : Submodule U V) (S : Finset (Fin 8 → ℤ))
    (hS : ∀ w : Fin 8 → ℤ, Lwt N w ≠ ⊥ → w ∈ S) :
    Module.finrank ℂ (V ⧸ N) = ∑ w ∈ S, dmul N w := by
  have htop : S.sup (fun w => Lwt N w) = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← iSup_Lwt_eq_top]
    refine iSup_le fun w => ?_
    by_cases h : w ∈ S
    · exact Finset.le_sup (f := fun w => Lwt N w) h
    · rw [show Lwt N w = ⊥ from by
        by_contra hne
        exact h (hS w hne)]
      exact bot_le
  rw [← finrank_sup_Lwt N S, htop, LinearEquiv.finrank_eq (Submodule.topEquiv (R := ℂ))]


/-! ## `dim L(ω₁+ω₈) = 779247` -/

lemma mnorm_nonneg (q : ℤ) : 0 ≤ Submission.E8Support.mnorm q := by
  rw [Submission.E8Support.mnorm]
  split_ifs <;> decide

lemma mnorm_toNat (q : ℤ) : (Submission.E8Support.mnorm q).toNat
    = (if q = 0 then 1407 else if q = 2 then 455 else if q = 4 then 133
        else if q = 6 then 34 else if q = 8 then 7 else if q = 10 then 1 else 0 : ℕ) := by
  rw [Submission.E8Support.mnorm]
  split_ifs <;> decide

/-- **The dimension of the irreducible quotient `L(ω₁+ω₈) = V ⧸ N`.** -/
theorem finrank_eq (N : Submodule U V) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) :
    Module.finrank ℂ (V ⧸ N) = 779247 := by
  obtain ⟨L, hLnd, hLall, hL0, hL2, hL4, hL6, hL8, hL10⟩ :=
    Commons.LinearAlgebra.Matrix.Cartan.e8_lattice_count
  have hchar : ∀ w : Fin 8 → ℤ, (Submission.E8Numerics.mfun w : ℚ) = mul N w :=
    mfun_eq_mul N hvN hmax
  have hS : ∀ w : Fin 8 → ℤ, Lwt N w ≠ ⊥ → w ∈ L.toFinset := by
    intro w hw
    rw [List.mem_toFinset]
    apply hLall
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
  have hterm : ∀ w : Fin 8 → ℤ, dmul N w = (Submission.E8Support.mnorm (qq w)).toNat := by
    intro w
    have h1 : (Submission.E8Numerics.mfun w : ℚ) = ((dmul N w : ℤ) : ℚ) := hchar w
    have h2 : Submission.E8Numerics.mfun w = (dmul N w : ℤ) := Int.cast_injective h1
    rw [Submission.E8Support.mfun_eq_mnorm] at h2
    have h3 : ((dmul N w : ℕ) : ℤ) = Submission.E8Support.mnorm (qq w) := h2.symm
    have : (Submission.E8Support.mnorm (qq w)).toNat = dmul N w := by
      rw [← h3, Int.toNat_natCast]
    exact this.symm
  rw [finrank_eq_sum_dmul N L.toFinset hS,
    Finset.sum_congr rfl (fun w _ => hterm w),
    Finset.sum_congr rfl (fun w _ => mnorm_toNat (qq w))]
  exact Commons.LinearAlgebra.Matrix.Cartan.e8_lattice_toNat_sum L hLnd hL0 hL2 hL4 hL6 hL8 hL10


end Submission.E8Finrank
