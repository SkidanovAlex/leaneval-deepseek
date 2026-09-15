import Submission.Work.KvnStep
import Submission.Commons.Combinatorics.Transference.levelJoin_atom_close

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Boundary selection and scaling for the Green–Tao §7 tower

* `exists_boundary_family`: the pigeonhole/shift choice of Green–Tao (7.3), performed
  simultaneously for a finite family of generators: there are shifts `α j` and boundary sets
  `T j` with total `(ν+1)`-mass `O(K η ∑(ν+1))`.
* `davg_div_eq`, `davg_div_bound`, `levelJoin_succ_close`: the scaling bookkeeping relating the
  scaled generator `F/(2C)` (whose level sets generate `B_{K+1}`) to the raw generator `F`.
-/

open Finset
open scoped BigOperators

namespace GTTrans

open Commons.Combinatorics.Transference
open FinSigma

/-- **Simultaneous boundary selection** (Green–Tao (7.3) / `exists_shift_boundary_cover`).
For a finite family of generators there are shifts `α j ∈ [0, ε)` and boundary sets `T j` such
that `T j` contains every point within `η` (in units of `ε`) of the level grid of the `j`-th
generator, and the total `(ν+1)`-mass of the `T j` is at most `K·3η·∑(ν+1)`. -/
theorem exists_boundary_family {p : ℕ} [Fact p.Prime] {K : ℕ} (G' : Fin K → ZMod p → ℝ)
    (ν : ZMod p → ℝ) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) (hη1 : η ≤ 1)
    (hν : ∀ x, 0 ≤ ν x) :
    ∃ (α : Fin K → ℝ) (T : Fin K → Finset (ZMod p)),
      (∀ j, 0 ≤ α j ∧ α j < ε) ∧
      (∀ (j : Fin K) (y : ZMod p),
        (∃ n : ℤ, |(G' j y - α j) / ε - n| ≤ η) → y ∈ T j) ∧
      ∑ j, ∑ y ∈ T j, (ν y + 1) ≤ (K : ℝ) * (3 * η * ∑ x, (ν x + 1)) := by
  classical
  have hν1 : ∀ x, 0 ≤ ν x + 1 := fun x => by have := hν x; linarith
  have key : ∀ j : Fin K, ∃ α : ℝ, 0 ≤ α ∧ α < ε ∧ ∃ T : Finset (ZMod p),
      (∀ y : ZMod p, (∃ n : ℤ, |(G' j y - α) / ε - n| ≤ η) → y ∈ T) ∧
      ∑ y ∈ T, (ν y + 1) ≤ 3 * η * ∑ x, (ν x + 1) :=
    fun j => exists_shift_boundary_cover (G' j) ν hε hη hη1 hν1
  choose α hα0 hαε T hT hTmass using key
  refine ⟨α, T, fun j => ⟨hα0 j, hαε j⟩, fun j y hy => hT j y hy, ?_⟩
  calc ∑ j, ∑ y ∈ T j, (ν y + 1) ≤ ∑ _j : Fin K, (3 * η * ∑ x, (ν x + 1)) :=
        Finset.sum_le_sum (fun j _ => hTmass j)
    _ = (K : ℝ) * (3 * η * ∑ x, (ν x + 1)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The scaled dual function is the dual function of the scaled generator:
`𝒟(F/(2C)) = (2C)^{-(2^d-1)}·𝒟F`. -/
lemma davg_div_eq {p : ℕ} [Fact p.Prime] {d : ℕ} (C : ℝ) (F : ZMod p → ℝ) (x : ZMod p) :
    davg d (fun y => F y / (2 * C)) x = (((2 * C) ^ (2 ^ d - 1))⁻¹) * davg d F x := by
  have h : (fun y => F y / (2 * C)) = fun y => (2 * C)⁻¹ * F y := by
    funext y; rw [div_eq_inv_mul]
  have h2 := congrFun (davg_smul (d := d) ((2 * C)⁻¹) F) x
  rw [h, h2, inv_pow]

/-- **Sup-norm bound for the raw generator** obtained from the bound on the scaled one. -/
lemma davg_div_bound {p : ℕ} [Fact p.Prime] {d : ℕ} {C : ℝ} (hC : 0 < C) (F : ZMod p → ℝ)
    {Mscaled : ℝ} (hM : ∀ x, |davg d (fun y => F y / (2 * C)) x| ≤ Mscaled) (x : ZMod p) :
    |davg d F x| ≤ (2 * C) ^ (2 ^ d - 1) * Mscaled := by
  have h2C : (0 : ℝ) < 2 * C := by linarith
  have hc : (0 : ℝ) < (2 * C) ^ (2 ^ d - 1) := pow_pos h2C _
  have h := davg_div_eq (d := d) C F x
  have hmul : davg d F x = (2 * C) ^ (2 ^ d - 1) * davg d (fun y => F y / (2 * C)) x := by
    rw [h, mul_inv_cancel_left₀ (ne_of_gt hc)]
  rw [hmul, abs_mul, abs_of_pos hc]
  exact mul_le_mul_of_nonneg_left (hM x) hc.le

/-- **Level sets of the scaled generator control the raw generator.**  If `x` and `y` lie in the
same level set of `𝒟(F/(2C))` at resolution `ε` and shift `α`, then the raw dual function differs
by at most `(2C)^{2^d-1}·ε`. -/
lemma davg_div_close {p : ℕ} [Fact p.Prime] {d : ℕ} {C ε α : ℝ} (hC : 0 < C) (hε : 0 < ε)
    {F : ZMod p → ℝ} {x y : ZMod p}
    (hy : ⌊(davg d (fun z => F z / (2 * C)) y - α) / ε⌋
        = ⌊(davg d (fun z => F z / (2 * C)) x - α) / ε⌋) :
    |davg d F y - davg d F x| ≤ (2 * C) ^ (2 ^ d - 1) * ε := by
  have h2C : (0 : ℝ) < 2 * C := by linarith
  have hc : (0 : ℝ) < (2 * C) ^ (2 ^ d - 1) := pow_pos h2C _
  have hlt := abs_sub_lt_of_floor_div_eq hε hy
  have hsub : (davg d (fun z => F z / (2 * C)) y - α) - (davg d (fun z => F z / (2 * C)) x - α)
      = (((2 * C) ^ (2 ^ d - 1))⁻¹) * (davg d F y - davg d F x) := by
    rw [davg_div_eq (d := d) C F y, davg_div_eq (d := d) C F x]; ring
  rw [hsub, abs_mul, abs_of_pos (inv_pos.mpr hc)] at hlt
  have hgoal : |davg d F y - davg d F x| < (2 * C) ^ (2 ^ d - 1) * ε := by
    have h2 : (2 * C) ^ (2 ^ d - 1) * (((2 * C) ^ (2 ^ d - 1))⁻¹
        * |davg d F y - davg d F x|) < (2 * C) ^ (2 ^ d - 1) * ε :=
      (mul_lt_mul_iff_of_pos_left hc).mpr hlt
    rwa [mul_inv_cancel_left₀ (ne_of_gt hc)] at h2
  exact hgoal.le

/-- **The refined σ-algebra `B_{K+1}` is contained in the level sets of the new generator.**
If `y` lies in the atom `kpartExt d C ε K G α Fnew αnew x` of `B_{K+1}`, then the raw dual
function `𝒟Fnew` differs by at most `(2C)^{2^d-1}·ε` at `x` and `y`.  (This is the hypothesis
`hQcl` of `energy_step_core`.) -/
lemma kpartExt_davg_close {p : ℕ} [Fact p.Prime] {d : ℕ} {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε)
    (G : ℕ → ZMod p → ℝ) (α : ℕ → ℝ) (K : ℕ) (Fnew : ZMod p → ℝ) (αnew : ℝ) {x y : ZMod p}
    (hy : y ∈ kpartExt d C ε K G α Fnew αnew x) :
    |davg d Fnew y - davg d Fnew x| ≤ (2 * C) ^ (2 ^ d - 1) * ε := by
  have hlev : ⌊(davg d (fun z => Fnew z / (2 * C)) y - αnew) / ε⌋
      = ⌊(davg d (fun z => Fnew z / (2 * C)) x - αnew) / ε⌋ := by
    have h := (mem_kpart d C ε (K + 1) (Function.update G K Fnew)
      (Function.update α K αnew) x y).mp hy K (by omega)
    simpa using h
  exact davg_div_close hC hε hlev

end GTTrans