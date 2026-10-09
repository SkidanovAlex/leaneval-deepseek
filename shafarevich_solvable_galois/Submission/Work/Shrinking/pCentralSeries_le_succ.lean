import Mathlib
import Submission.Work.Shrinking.PCentral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Shrinking

/-- `H^p` is a normal subgroup whenever `H` is: conjugation fixes the set of `p`-th powers
of `H`, hence fixes the subgroup they generate. -/
private theorem powSubgroup_normal (p : ℕ) (P : Type*) [Group P] (H : Subgroup P) [hH : H.Normal] :
    (powSubgroup p H).Normal := by
  refine Subgroup.Normal.mk fun n hn g => ?_
  have key : ∀ x ∈ (fun x : P => x ^ p) '' (H : Set P), g * x * g⁻¹ ∈ powSubgroup p H := by
    rintro x ⟨w, hw, rfl⟩
    exact Subgroup.subset_closure ⟨g * w * g⁻¹, hH.conj_mem w hw g, by simp [conj_pow]⟩
  induction hn using Subgroup.closure_induction with
  | mem x hx => exact key x hx
  | one => simp
  | mul x y hx hy ihx ihy =>
      rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group]
      exact mul_mem ihx ihy
  | inv x hx ih =>
      rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
      exact inv_mem ih

/-- `pCentralStep p H = H^p [H, P]` is normal whenever `H` is. -/
private theorem pCentralStep_normal (p : ℕ) (P : Type*) [Group P] (H : Subgroup P) [H.Normal] :
    (pCentralStep p H).Normal := by
  have hpow : (powSubgroup p H).Normal := powSubgroup_normal p P H
  have hcomm : (⁅H, ⊤⁆ : Subgroup P).Normal := Subgroup.commutator_normal H ⊤
  exact Subgroup.sup_normal (powSubgroup p H) ⁅H, ⊤⁆

/-- `pCentralStep p H ≤ H` for a normal subgroup `H`. -/
private theorem pCentralStep_le_of_normal (p : ℕ) (P : Type*) [Group P] (H : Subgroup P)
    [H.Normal] : pCentralStep p H ≤ H :=
  sup_le (powSubgroup_le p H) (commutator_le_self_of_normal H)

/-- Simultaneous induction: every term of the descending `p`-central series is normal, and the
series is descending. -/
private theorem pCentralSeries_normal_and_le (p : ℕ) (P : Type*) [Group P] (n : ℕ) :
    (pCentralSeries p P n).Normal ∧ pCentralSeries p P (n + 1) ≤ pCentralSeries p P n := by
  induction n with
  | zero => exact ⟨by rw [pCentralSeries_zero]; infer_instance, le_top⟩
  | succ n ih =>
      obtain ⟨hN, _⟩ := ih
      have hnN : (pCentralSeries p P n).Normal := hN
      have hN' : (pCentralSeries p P (n + 1)).Normal :=
        pCentralStep_normal p P (pCentralSeries p P n)
      refine ⟨hN', ?_⟩
      have hn'N : (pCentralSeries p P (n + 1)).Normal := hN'
      exact pCentralStep_le_of_normal p P (pCentralSeries p P (n + 1))

/-- The descending `p`-central series is descending: `P_{n+1} ≤ P_n`, i.e.
`pCentralStep p H ≤ H` for `H = pCentralSeries p P n`.

Since `pCentralStep p H = powSubgroup p H ⊔ ⁅H, ⊤⁆`, it suffices to show `powSubgroup p H ≤ H`
(this is `Work.Shrinking.powSubgroup_le`) and `⁅H, ⊤⁆ ≤ H`, which follows from
`Work.Shrinking.commutator_le_self_of_normal` and the normality of `H`.  Normality of the terms
can either be imported from `Submission.Work.Shrinking.pCentralSeries_normal` once available or
proved simultaneously by induction (`∀ n, (pCentralSeries p P n).Normal ∧
pCentralSeries p P (n+1) ≤ pCentralSeries p P n`). -/
theorem pCentralSeries_le_succ (p : ℕ) (P : Type*) [Group P] (n : ℕ) :
    pCentralSeries p P (n + 1) ≤ pCentralSeries p P n :=
  (pCentralSeries_normal_and_le p P n).2

end Work.Shrinking
