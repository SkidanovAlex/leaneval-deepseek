import Mathlib
import Submission.Work.ThomBordism.TwoSet.Basic

/-!
# The Lebesgue subdivision of a two-set open cover

For a continuous `f : I^j → X` and an open cover `X = U ∪ V` there is a grid size `N ≥ 1` such
that each closed grid box of the `N`-subdivision of `I^j` is mapped entirely into `U` or entirely
into `V`.  This is the Lebesgue-number lemma applied to the pulled-back cover of the compact metric
space `I^j`.
-/

namespace Work.ThomBordism.TwoSet

open scoped Topology unitInterval

theorem Subdivision {X : Type*} [TopologicalSpace X] {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) {j : ℕ} (f : C(Work.ThomBordism.TwoSet.IC j, X)) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ m : Fin j → Fin N,
      (∀ x : IC j, (∀ i, ((m i : ℝ) ≤ (N : ℝ) * (x i : ℝ) ∧
        (N : ℝ) * (x i : ℝ) ≤ (m i : ℝ) + 1)) → f x ∈ U)
      ∨ (∀ x : IC j, (∀ i, ((m i : ℝ) ≤ (N : ℝ) * (x i : ℝ) ∧
        (N : ℝ) * (x i : ℝ) ≤ (m i : ℝ) + 1)) → f x ∈ V) := by
  classical
  have hcover : (Set.univ : Set (IC j)) ⊆
      ⋃ b : Bool, (cond b (f ⁻¹' V) (f ⁻¹' U) : Set (IC j)) := by
    intro x _
    rw [Set.mem_iUnion]
    rcases (show f x ∈ U ∨ f x ∈ V from by
      have := Set.eq_univ_iff_forall.mp hcov (f x); simpa [Set.mem_union] using this) with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  obtain ⟨δ, hδpos, hδ⟩ := lebesgue_number_lemma_of_metric
      (s := (Set.univ : Set (IC j))) (c := fun b : Bool => cond b (f ⁻¹' V) (f ⁻¹' U))
      isCompact_univ
      (by
        intro b
        cases b
        · show IsOpen (f ⁻¹' U); exact IsOpen.preimage f.continuous hU
        · show IsOpen (f ⁻¹' V); exact IsOpen.preimage f.continuous hV)
      hcover
  obtain ⟨N, hNδ⟩ := exists_nat_one_div_lt hδpos
  refine ⟨N+1, Nat.le_add_left 1 N, fun m => ?_⟩
  have hNp : (0:ℝ) < ((N+1 : ℕ) : ℝ) := by positivity
  have hNp1 : (1:ℝ) ≤ ((N+1 : ℕ) : ℝ) := by
    have : (1:ℕ) ≤ N+1 := Nat.le_add_left 1 N
    exact_mod_cast this
  let c : IC j := fun i => (⟨((m i : ℝ) + 1/2) / ((N+1 : ℕ) : ℝ), by
    constructor
    · positivity
    · rw [div_le_one hNp]
      have hm : (m i : ℕ) + 1 ≤ N + 1 := Nat.succ_le_of_lt (m i).isLt
      have : (m i : ℝ) + 1 ≤ ((N+1 : ℕ) : ℝ) := by exact_mod_cast hm
      linarith⟩)
  obtain ⟨b, hb⟩ := hδ c (Set.mem_univ c)
  have hmem : ∀ {x : IC j}, (∀ i, ((m i : ℝ) ≤ ((N+1 : ℕ) : ℝ) * (x i : ℝ) ∧
        ((N+1 : ℕ) : ℝ) * (x i : ℝ) ≤ (m i : ℝ) + 1)) → x ∈ Metric.ball c δ := by
    intro x hx
    rw [Metric.mem_ball]
    have hd : dist x c ≤ 1/(2*((N+1 : ℕ) : ℝ)) := by
      rw [dist_pi_le_iff (by positivity)]
      intro i
      have h1 := (hx i).1
      have h2 := (hx i).2
      have hc : (c i : ℝ) = ((m i : ℝ) + 1/2)/((N+1 : ℕ) : ℝ) := rfl
      rw [Subtype.dist_eq, Real.dist_eq, hc, abs_le]
      refine ⟨?_, ?_⟩ <;> · field_simp; linarith
    have hkey : 1/(2*((N+1 : ℕ) : ℝ)) ≤ 1/((N+1 : ℕ) : ℝ) := by
      exact one_div_le_one_div_of_le hNp (by linarith)
    have hkey2 : 1/(((N+1 : ℕ) : ℝ)) < δ := by
      have hEq : ((N:ℝ)+1) = ((N+1 : ℕ) : ℝ) := by push_cast; ring
      rw [← hEq]; exact hNδ
    linarith
  cases b with
  | false => left; intro x hx; exact hb (hmem hx)
  | true => right; intro x hx; exact hb (hmem hx)


end Work.ThomBordism.TwoSet
