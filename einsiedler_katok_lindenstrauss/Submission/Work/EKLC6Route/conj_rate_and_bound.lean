import Mathlib
import Submission.Work.EKLC6Route.Defs
import Submission.Work.EKLC6Core.V_mul_inv_bound
import Submission.Work.EKLComp.inv_mem_V
import Submission.Work.EKLC6Route.entries_tendsto_of_tendsto
import Submission.Work.LinearAlgebra.Matrix.abs_entry_mul_le

/-!
# `Work.EKLC6Route.conj_rate_and_bound`

For a sequence `u k ∈ V 1` (matrices within max-entry distance `1` of the identity) and a
sequence `w k → 1` in `SL₃(ℝ)`, the conjugates `u k * w k * (u k)⁻¹` converge to `1` with an
explicit *rate*, and they are uniformly bounded:

* `(u k * w k * (u k)⁻¹) - 1 = (↑(u k)) * (↑(w k) - 1) * (↑(u k)⁻¹)`, a product of the
  bounded factor `↑(u k)`, the displacement `↑(w k) - 1` and the bounded factor `↑(u k⁻¹)`;
* entries of `↑(u k)` are `≤ 2` and entries of `↑(u k⁻¹)` are `≤ 11` (`u k⁻¹ ∈ V 10`, by the
  adjugate estimate `Work.EKLComp.inv_mem_V`), so the displacement is dominated by
  `22 * s k` where `s k = ∑_{a,b} |(↑(w k) - 1) a b| → 0`;
* hence `ε k = 22 * s k + 1 / (k+1)` is a valid (strict) rate, and `C = 22 * sup s + 1` a valid
  bound, the supremum existing because `s → 0`.

The two ingredients are the separately proved lemmas
`Work.EKLC6Route.entries_tendsto_of_tendsto` (entrywise convergence of `w k → 1`, using that
`SL₃(ℝ)` carries the subspace topology of the product topology on matrices) and
`Work.LinearAlgebra.Matrix.abs_entry_mul_le` (the entrywise product estimate).
-/

open Filter Topology

namespace Work.EKLC6Route

open Work.EKLContract

theorem conj_rate_and_bound {u w : ℕ → Work.EKLContract.SL3}
    (hu : ∀ k, u k ∈ Work.EKLContract.V 1)
    (hw : Filter.Tendsto w Filter.atTop (nhds (1 : Work.EKLContract.SL3))) :
    ∃ (ε : ℕ → ℝ) (C : ℝ),
      Filter.Tendsto ε Filter.atTop (nhds 0) ∧ (∀ k, 0 ≤ ε k) ∧ 0 < C ∧
      (∀ k : ℕ, ∀ i j : Fin 3,
        |(u k * w k * (u k)⁻¹) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < ε k) ∧
      (∀ k : ℕ, ∀ i j : Fin 3, |(u k * w k * (u k)⁻¹) i j| ≤ C) := by
  -- Step 1: `w k → 1` entrywise.
  have hentry : ∀ a b : Fin 3,
      Tendsto (fun k => ((w k : SL3) : Matrix (Fin 3) (Fin 3) ℝ) a b) atTop
        (nhds ((1 : Matrix (Fin 3) (Fin 3) ℝ) a b)) :=
    fun a b => entries_tendsto_of_tendsto hw a b
  -- Step 2: the displacement sequence `s k = ∑_{a,b} |(↑(w k) - 1) a b| → 0`.
  let s : ℕ → ℝ := fun k => ∑ a : Fin 3, ∑ b : Fin 3,
      |((w k : Matrix (Fin 3) (Fin 3) ℝ) - 1) a b|
  have hs_nonneg : ∀ k, 0 ≤ s k := by
    intro k
    apply Finset.sum_nonneg; intro a _
    apply Finset.sum_nonneg; intro b _
    exact abs_nonneg _
  have hs_tend : Tendsto s atTop (nhds 0) := by
    change Tendsto (fun k => ∑ a : Fin 3, ∑ b : Fin 3,
      |((w k : Matrix (Fin 3) (Fin 3) ℝ) - 1) a b|) atTop (nhds 0)
    have hinner : ∀ a : Fin 3, Tendsto (fun k => ∑ b : Fin 3,
        |((w k : Matrix (Fin 3) (Fin 3) ℝ) - 1) a b|) atTop (nhds 0) := by
      intro a
      have hb : ∀ b : Fin 3, Tendsto (fun k =>
          |((w k : Matrix (Fin 3) (Fin 3) ℝ) - 1) a b|) atTop (nhds 0) := by
        intro b
        simp only [Matrix.sub_apply]
        have h := (hentry a b).sub
          (tendsto_const_nhds (x := ((1 : Matrix (Fin 3) (Fin 3) ℝ) a b)) (f := atTop))
        simpa using h.abs
      have := tendsto_finsetSum (Finset.univ : Finset (Fin 3)) (fun b _ => hb b)
      simpa using this
    have := tendsto_finsetSum (Finset.univ : Finset (Fin 3)) (fun a _ => hinner a)
    simpa using this
  have hbdd : BddAbove (Set.range s) := hs_tend.bddAbove_range
  have hs_le_sup : ∀ k, s k ≤ sSup (Set.range s) :=
    fun k => le_csSup hbdd (Set.mem_range_self k)
  have hsup_nonneg : 0 ≤ sSup (Set.range s) := le_trans (hs_nonneg 0) (hs_le_sup 0)
  -- Step 3: the factorisation of the conjugated displacement.
  have hdec : ∀ k, ((u k * w k * (u k)⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) - 1
      = (u k : Matrix (Fin 3) (Fin 3) ℝ) * ((w k : Matrix (Fin 3) (Fin 3) ℝ) - 1)
          * (((u k)⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) := by
    intro k
    have hAB : (u k : Matrix (Fin 3) (Fin 3) ℝ)
        * (((u k)⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    conv_lhs => rw [← hAB]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  -- Step 4: the entrywise product estimate, with the two uniform bounds.
  have hb_est : ∀ k i j,
      |((u k : Matrix (Fin 3) (Fin 3) ℝ) * ((w k : Matrix (Fin 3) (Fin 3) ℝ) - 1)
          * (((u k)⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ)) i j| ≤ 22 * s k := by
    intro k i j
    have hA : ∀ a b, |(u k : Matrix (Fin 3) (Fin 3) ℝ) a b| ≤ 2 := by
      intro a b
      have h := Work.EKLC6Core.entry_abs_le_of_mem_V (hu k) a b
      linarith
    have hB : ∀ a b, |(((u k)⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) a b| ≤ 11 := by
      intro a b
      have hmem : (u k)⁻¹ ∈ V (10 * 1) :=
        Work.EKLComp.inv_mem_V (by norm_num) (by norm_num) (hu k)
      have h := Work.EKLC6Core.entry_abs_le_of_mem_V hmem a b
      linarith
    have h := Work.LinearAlgebra.Matrix.abs_entry_mul_le
      (M := ((w k : Matrix (Fin 3) (Fin 3) ℝ) - 1)) hA hB i j
    simpa [s] using h
  refine ⟨fun k => 22 * s k + 1 / ((k : ℝ) + 1), 22 * sSup (Set.range s) + 1,
    ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : Tendsto (fun k => 22 * s k) atTop (nhds 0) := by
      simpa using hs_tend.const_mul (22 : ℝ)
    have h2 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using h1.add h2
  · intro k
    have := hs_nonneg k
    positivity
  · linarith
  · intro k i j
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have h := hb_est k i j
    have heq : ((u k * w k * (u k)⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j
        = ((u k : Matrix (Fin 3) (Fin 3) ℝ) * ((w k : Matrix (Fin 3) (Fin 3) ℝ) - 1)
            * (((u k)⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ)) i j := by
      rw [← Matrix.sub_apply, hdec k]
    rw [heq]
    linarith
  · intro k i j
    have hsub := sub_eq_iff_eq_add.mp (hdec k)
    rw [hsub, Matrix.add_apply]
    have hone : |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
      rw [Matrix.one_apply]; split <;> simp
    have h1 := hb_est k i j
    have h3 := hs_le_sup k
    calc |((u k : Matrix (Fin 3) (Fin 3) ℝ) * ((w k : Matrix (Fin 3) (Fin 3) ℝ) - 1)
            * (((u k)⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ)) i j
            + (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
        ≤ |((u k : Matrix (Fin 3) (Fin 3) ℝ) * ((w k : Matrix (Fin 3) (Fin 3) ℝ) - 1)
            * (((u k)⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ)) i j|
          + |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := abs_add_le _ _
      _ ≤ 22 * sSup (Set.range s) + 1 := by linarith

end Work.EKLC6Route
