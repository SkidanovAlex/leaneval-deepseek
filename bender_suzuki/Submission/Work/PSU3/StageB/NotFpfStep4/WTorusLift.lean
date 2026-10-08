/-
# The torus coordinate of an element of `W(B̄, w̄)` in `PSU(3,2ⁿ)`

For `ζ ∈ W(B̄, w̄)`, `ζ ≠ 1`, there is `a ∈ (GF(q²))ˣ` (`q = 2ⁿ`) with

  `ζ = psu3Hom (suTgSU a)`,  `a^{q+1} = 1`,  `a³ ≠ 1`.

Mathematics.  `W(B̄, w̄) = C_D(w̄) ∩ C(K)` where `D = B̄ ∩ B̄^{w̄}`; and

* `D = twoPoint B̄ w̄ = T̄` (`Work.PSU3.Model.twoPoint_psu3B_psu3Weyl`), the image of the
  maximal torus `suTS n = Fˣ → SU(3,2ⁿ)`, `a ↦ diag(a, a^{q-1}, a^{-q})`;
* `K = J(D, w̄) = T̄` because `w̄` inverts the torus (`suSgM_conj_suTgSU`), and `T̄` is abelian,
  so `W ⊆ centD B̄ w̄ ⊆ T̄`.

Hence `ζ = ψ a` for some `a ∈ Fˣ` (`ψ a = psu3Hom (suTgSU a)`), and `ζ` commutes with `w̄`.
Writing `y = suTgSU a = ψ`-preimage of `ζ`, the commutator
`y · suSgM · y⁻¹ · suSgM⁻¹ = suTgSU (a^{q+1})` (`wtl_suTgSU_conj_suSgM`) lies in
`ker psu3Hom`, i.e. `suTgSU (a^{q+1})` is a scalar matrix.  Since
`suTgSU b ∈ ker ↔ b^{q+1} = 1 ∧ b³ = 1` (`wtl_suTgSU_mem_ker_iff`), while
`(a^{q+1})^{q-1} = a^{q²-1} = 1`, we get `(a^{q+1})² = 1` and then `a^{q+1} = 1`.

Finally, if `(a : F)³ = 1` then `a³ = 1` and `a^{q+1} = 1`, so `suTgSU a ∈ ker`, whence
`ζ = 1` — contradiction.  So `a³ ≠ 1`.
-/
import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.Model.psu3_isSplitRankOne
import Submission.Work.PSU3.StageA.centD_le_W_psu3Model
import Submission.Work.ThmF.Setup
import Submission.Work.Models.Port.PSU3.Weyl
import Submission.Work.Models.Port.PSU3.WeylQuotient
import Submission.Work.Models.Port.PSU3.PSU3Order

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.PSU3.StageB.NotFpfStep4

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-! ## Arithmetic in the field `F = GF(2^{2n})` -/

/-- `(q + 1)(q - 1) = q² - 1` for `q = 2ⁿ`. -/
lemma wtl_mul_pow_sub (n : ℕ) : (2 ^ n + 1) * (2 ^ n - 1) = 2 ^ (2 * n) - 1 := by
  have hs : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by rw [← pow_mul, Nat.mul_comm]
  have h := Nat.sq_sub_sq (2 ^ n) 1
  rw [hs, one_pow] at h
  exact h.symm

/-- `a^(q²-1) = 1` for `a ∈ (GF(q²))ˣ`, from `a^(q²) = a` (`pow_card_sq`). -/
lemma wtl_pow_card_sub_one_units (n : ℕ) (a : (Submission.PSU3.F n)ˣ) :
    a ^ (2 ^ (2 * n) - 1) = 1 := by
  have hcard : a ^ (2 ^ (2 * n)) = a := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Submission.PSU3.pow_card_sq]
  have hne : 2 ^ (2 * n) ≠ 0 := by positivity
  have hstep : a ^ (2 ^ (2 * n) - 1) * a = 1 * a := by
    rw [pow_sub_one_mul hne a, hcard, one_mul]
  exact mul_right_cancel hstep

/-! ## The commutator of a torus element with the Weyl element -/

/-- The commutator of `suTgSU a` with the Weyl element `suSgM` is `suTgSU (a^{q+1})`: the Weyl
element inverts the torus `a ↦ a^{-q}`, so the commutator is `a · a^q`. -/
lemma wtl_suTgSU_conj_suSgM (n : ℕ) (a : (Submission.PSU3.F n)ˣ) :
    Submission.PSU3.suTgSU n a * Submission.PSU3.suSgM n * (Submission.PSU3.suTgSU n a)⁻¹ *
      (Submission.PSU3.suSgM n)⁻¹ = Submission.PSU3.suTgSU n (a ^ (2 ^ n + 1)) := by
  have h1 : Submission.PSU3.suTgSU n a * Submission.PSU3.suSgM n * (Submission.PSU3.suTgSU n a)⁻¹ *
      (Submission.PSU3.suSgM n)⁻¹
      = Submission.PSU3.suTgSU n a *
        (Submission.PSU3.suSgM n * (Submission.PSU3.suTgSU n a)⁻¹ *
          (Submission.PSU3.suSgM n)⁻¹) := by
    group
  rw [h1, ← map_inv (f := Submission.PSU3.suTgSU n) a,
    Submission.PSU3.suSgM_conj_suTgSU n a⁻¹, ← map_mul, inv_pow, inv_inv, pow_succ']

/-! ## The kernel of `SU(3,2ⁿ) → PSU(3,2ⁿ)` on the torus -/

/-- `suTgSU b` lies in the kernel of `SU(3,2ⁿ) → PSU(3,2ⁿ)` exactly when it is the scalar matrix
`b·1`, i.e. when `b^{q+1} = b^3 = 1` (the scalar matrices of `SU(3,2ⁿ)`). -/
lemma wtl_suTgSU_mem_ker_iff (n : ℕ) (b : (Submission.PSU3.F n)ˣ) :
    Submission.PSU3.suTgSU n b ∈ (Submission.PSU3.psu3Hom n).ker ↔
      b ^ (2 ^ n + 1) = 1 ∧ b ^ 3 = 1 := by
  constructor
  · intro h
    have hcent : ((Submission.PSU3.suTgSU n b : ↥(Submission.PSU3.SU3 n)) :
        GL (Fin 3) (Submission.PSU3.F n)) ∈
        Subgroup.center (GL (Fin 3) (Submission.PSU3.F n)) := by
      have h' := h
      rw [Submission.PSU3.psu3Hom_ker_eq, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h'
      exact h'.2
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcent
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hcent
    have hSU3 : Submission.PSU3.IsSU3 (Matrix.GeneralLinearGroup.scalar (Fin 3) u) := by
      rw [hu]; exact (Submission.PSU3.suTgSU n b).2
    obtain ⟨h1, h2⟩ := (Submission.PSU3.isSU3_scalar_iff n u).mp hSU3
    have hbu : u = b := by
      apply Units.ext
      have hmat := congrArg (fun x : GL (Fin 3) (Submission.PSU3.F n) =>
        (x : Matrix (Fin 3) (Fin 3) (Submission.PSU3.F n))) hu
      have h00 := congrFun (congrFun hmat 0) 0
      rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply] at h00
      simp only [Fin.isValue, ↓reduceIte] at h00
      rw [Submission.PSU3.suTgSU_val, Submission.PSU3.suTg_coe, Submission.PSU3.suTmat] at h00
      simpa using h00
    subst hbu
    exact ⟨h1, h2⟩
  · intro h
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    rw [Submission.PSU3.psu3Hom_apply]
    apply Matrix.ProjGenLinGroup.mk_eq_one.mpr
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    refine ⟨b, ?_⟩
    symm
    have hb2 : b ^ 2 = b⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ]
      norm_num [h.2]
    have hbq : b ^ (2 ^ n) = b⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ, h.1]
    have hbqm1 : b ^ (2 ^ n - 1) = b := by
      have hsum : (2 ^ n - 1) + 2 = 2 ^ n + 1 := by
        have := Nat.one_le_two_pow (n := n); omega
      have hh : b ^ (2 ^ n - 1) * b ^ 2 = 1 := by rw [← pow_add, hsum, h.1]
      rw [hb2] at hh
      exact mul_inv_eq_one.mp hh
    have hbqm1F : (b : Submission.PSU3.F n) ^ (2 ^ n - 1) = (b : Submission.PSU3.F n) := by
      simpa using congrArg (fun x : (Submission.PSU3.F n)ˣ => (x : Submission.PSU3.F n)) hbqm1
    have hbqF1 : (b : Submission.PSU3.F n) ^ (2 ^ n) = (b : Submission.PSU3.F n)⁻¹ := by
      simpa using congrArg (fun x : (Submission.PSU3.F n)ˣ => (x : Submission.PSU3.F n)) hbq
    have hbqF : ((b : Submission.PSU3.F n) ^ (2 ^ n))⁻¹ = (b : Submission.PSU3.F n) := by
      rw [hbqF1, inv_inv]
    apply Units.ext
    rw [Submission.PSU3.suTgSU_val, Submission.PSU3.suTg_coe,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Submission.PSU3.suTmat]
    ext i j
    simp only [Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      fin_cases i <;>
        simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
          Matrix.tail_cons, hbqm1F, hbqF]
    · simp [hij]

/-! ## The main statement -/

theorem WTorusLift {n : ℕ} (hn : 2 ≤ n) {ζ : LeanEval.GroupTheory.Defs.PSU3Model n}
    (hζ : ζ ∈ Work.ThmF.W (Submission.PSU3.psu3B n) (Submission.PSU3.psu3Weyl n))
    (hζ1 : ζ ≠ 1) :
    ∃ a : (Submission.PSU3.F n)ˣ,
      ζ = Submission.PSU3.psu3Hom n (Submission.PSU3.suTgSU n a) ∧
      (a : Submission.PSU3.F n) ^ (2 ^ n + 1) = 1 ∧
      (a : Submission.PSU3.F n) ^ 3 ≠ 1 := by
  -- `W ⊆ centD B̄ w̄ = twoPoint B̄ w̄ ⊓ C(w̄) ⊓ C(K) ⊆ T̄`
  rw [Work.ThmF.W, Subgroup.mem_inf] at hζ
  obtain ⟨hζD, -⟩ := hζ
  rw [Submission.Blueprint.centD, Subgroup.mem_inf] at hζD
  obtain ⟨hζ2, hζc⟩ := hζD
  have hζT : ζ ∈ Submission.PSU3.psu3T n := by
    rw [← Work.PSU3.Model.twoPoint_psu3B_psu3Weyl n]
    exact hζ2
  have hcomm : Submission.PSU3.psu3Weyl n * ζ = ζ * Submission.PSU3.psu3Weyl n :=
    (Subgroup.mem_centralizer_iff.mp hζc) _ (Set.mem_singleton _)
  -- lift `ζ` to the torus `T = suTS n` of `SU(3,2ⁿ)`
  obtain ⟨y, hy, hyζ⟩ := Subgroup.mem_map.mp hζT
  obtain ⟨a, ha⟩ := Subgroup.mem_subgroupOf.mp hy
  have hya : y = Submission.PSU3.suTgSU n a := by
    apply Subtype.ext
    rw [Submission.PSU3.suTgSU_val]
    exact ha
  have hζeq : ζ = Submission.PSU3.psu3Hom n (Submission.PSU3.suTgSU n a) := by
    rw [← hyζ, hya]
  -- the commutator of the lift with the Weyl element dies in `PSU(3,2ⁿ)`
  have hker : y * Submission.PSU3.suSgM n * y⁻¹ * (Submission.PSU3.suSgM n)⁻¹ ∈
      (Submission.PSU3.psu3Hom n).ker := by
    rw [MonoidHom.mem_ker]
    have hc : Submission.PSU3.psu3Hom n
        (y * Submission.PSU3.suSgM n * y⁻¹ * (Submission.PSU3.suSgM n)⁻¹) =
        ζ * Submission.PSU3.psu3Weyl n * ζ⁻¹ * (Submission.PSU3.psu3Weyl n)⁻¹ := by
      rw [show Submission.PSU3.psu3Weyl n =
        Submission.PSU3.psu3Hom n (Submission.PSU3.suSgM n) from rfl]
      simp only [map_mul, map_inv, hyζ]
    have hconj : ζ * Submission.PSU3.psu3Weyl n * ζ⁻¹ = Submission.PSU3.psu3Weyl n := by
      have h2 : ζ * Submission.PSU3.psu3Weyl n = Submission.PSU3.psu3Weyl n * ζ := hcomm.symm
      calc ζ * Submission.PSU3.psu3Weyl n * ζ⁻¹
          = (Submission.PSU3.psu3Weyl n * ζ) * ζ⁻¹ := by rw [h2]
        _ = Submission.PSU3.psu3Weyl n * (ζ * ζ⁻¹) := by rw [mul_assoc]
        _ = Submission.PSU3.psu3Weyl n * 1 := by rw [mul_inv_cancel]
        _ = Submission.PSU3.psu3Weyl n := mul_one _
    rw [hc, hconj, mul_inv_cancel]
  -- so `suTgSU (a^{q+1})` is a scalar: `(a^{q+1})^{q+1} = (a^{q+1})^3 = 1`
  have hbker : Submission.PSU3.suTgSU n (a ^ (2 ^ n + 1)) ∈ (Submission.PSU3.psu3Hom n).ker := by
    rw [← wtl_suTgSU_conj_suSgM n a, ← hya]
    exact hker
  obtain ⟨hbq1, hb3⟩ := (wtl_suTgSU_mem_ker_iff n (a ^ (2 ^ n + 1))).mp hbker
  have hbodd : (a ^ (2 ^ n + 1)) ^ (2 ^ n - 1) = 1 := by
    rw [← pow_mul, wtl_mul_pow_sub n, wtl_pow_card_sub_one_units n a]
  -- `b = a^{q+1}` satisfies `b^{q+1} = b^{q-1} = b^3 = 1`, whence `b = 1`
  have hb2 : (a ^ (2 ^ n + 1)) ^ 2 = 1 := by
    have hsum : (2 ^ n - 1) + 2 = 2 ^ n + 1 := by
      have := Nat.one_le_two_pow (n := n); omega
    have hsplit : (a ^ (2 ^ n + 1)) ^ (2 ^ n + 1)
        = (a ^ (2 ^ n + 1)) ^ (2 ^ n - 1) * (a ^ (2 ^ n + 1)) ^ 2 := by
      rw [← pow_add, hsum]
    rw [hbq1, hbodd, one_mul] at hsplit
    exact hsplit.symm
  have hbone : a ^ (2 ^ n + 1) = 1 := by
    have h3 : (a ^ (2 ^ n + 1)) ^ 3 = a ^ (2 ^ n + 1) := by
      rw [pow_three, ← pow_two, hb2]
      simp
    rw [h3] at hb3
    exact hb3
  have hfield1 : (a : Submission.PSU3.F n) ^ (2 ^ n + 1) = 1 := by
    simpa using congrArg (fun x : (Submission.PSU3.F n)ˣ => (x : Submission.PSU3.F n)) hbone
  -- and `a³ ≠ 1`, else `suTgSU a` would be trivial in `PSU(3,2ⁿ)`
  have hfield3 : (a : Submission.PSU3.F n) ^ 3 ≠ 1 := by
    intro h3f
    have h3u : a ^ 3 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val]
      exact h3f
    have haker : Submission.PSU3.suTgSU n a ∈ (Submission.PSU3.psu3Hom n).ker :=
      (wtl_suTgSU_mem_ker_iff n a).mpr ⟨hbone, h3u⟩
    exact hζ1 (by rw [hζeq]; exact MonoidHom.mem_ker.mp haker)
  exact ⟨a, hζeq, hfield1, hfield3⟩

end Work.PSU3.StageB.NotFpfStep4
