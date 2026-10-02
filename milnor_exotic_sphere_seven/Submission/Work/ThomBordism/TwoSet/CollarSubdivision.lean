import Mathlib
import Submission.Work.ThomBordism.TwoSet.Basic
import Submission.Work.ThomBordism.TwoSet.Subdivision

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The collared Lebesgue subdivision

`Subdivision` produces a grid size `N` such that every closed grid box of the `N`-subdivision of
`I^j` is mapped by `f` into one of the two open sets `U`, `V` of a cover.  For the cell-by-cell
compression argument one needs the additional collar condition that the boxes "near `∂I^j`" are
mapped into `U`: then the modification of a box never touches the boundary `∂I^j` (which must stay
fixed), and every point whose containing boxes are labelled `V` is at distance `≥ 2/N` from
`∂I^j`.
-/

namespace Work.ThomBordism.TwoSet

open scoped Topology unitInterval

/-- The closed grid box of the `N`-subdivision indexed by `m`. -/
def boxSet {j N : ℕ} (m : Fin j → Fin N) : Set (IC j) :=
  {x | ∀ i, (m i : ℝ) ≤ (N : ℝ) * (x i : ℝ) ∧ (N : ℝ) * (x i : ℝ) ≤ (m i : ℝ) + 1}

/-- **The collared subdivision.**  For a continuous `f : I^j → X`, an open cover `X = U ∪ V` and
`f (∂I^j) ⊆ U`, there is `N ≥ 3` such that every closed grid box of the `N`-subdivision is mapped
into `U` or into `V`, and every box which is "close to the boundary" — i.e. some index `mᵢ` is
`0`, `1`, `N-2` or `N-1` — is mapped into `U`. -/
theorem SubdivisionCollared {X : Type*} [TopologicalSpace X] {U V : Set X} (hU : IsOpen U)
    (hV : IsOpen V) (hcov : U ∪ V = Set.univ) {j : ℕ} (f : C(IC j, X))
    (hbd : ∀ x, x ∈ Cube.boundary (Fin j) → f x ∈ U) :
    ∃ N : ℕ, 3 ≤ N ∧ ∀ m : Fin j → Fin N,
      ((∀ x : IC j, x ∈ boxSet m → f x ∈ U) ∨ (∀ x : IC j, x ∈ boxSet m → f x ∈ V)) ∧
      ((∃ i, (m i : ℕ) = 0 ∨ (m i : ℕ) = 1 ∨ (m i : ℕ) = N - 2 ∨ (m i : ℕ) = N - 1) →
        ∀ x : IC j, x ∈ boxSet m → f x ∈ U) := by
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
  have hbd' : Cube.boundary (Fin j) ⊆ f ⁻¹' U := fun x hx => hbd x hx
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ :=
    (isClosed_cubeBoundary j).isCompact.exists_cthickening_subset_open
      (IsOpen.preimage f.continuous hU) hbd'
  have hδmin : 0 < min δ (δ₂ / 3) := lt_min hδpos (by linarith)
  obtain ⟨N₀, hN₀⟩ := exists_nat_one_div_lt hδmin
  set n : ℕ := N₀ + 4 with hn
  have hn4 : 4 ≤ n := by omega
  have hlt : 1/((n:ℝ)) < min δ (δ₂ / 3) := by
    refine lt_trans ?_ hN₀
    apply one_div_lt_one_div_of_lt
    · positivity
    · rw [hn]; push_cast; linarith
  refine ⟨n, by omega, fun m => ?_⟩
  have hnp : (0:ℝ) < (n:ℝ) := by positivity
  have hmem : ∀ {x : IC j}, x ∈ boxSet m → dist x (fun i => (⟨((m i : ℝ) + 1/2) / (n:ℝ), by
      constructor
      · positivity
      · rw [div_le_one hnp]
        have hm' : (m i : ℕ) + 1 ≤ n := Nat.succ_le_of_lt (m i).isLt
        have : (m i : ℝ) + 1 ≤ (n:ℝ) := by exact_mod_cast hm'
        linarith⟩ : unitInterval)) ≤ 1/(n:ℝ) := by
    intro x hx
    rw [dist_pi_le_iff (by positivity)]
    intro i
    have h1 := (hx i).1
    have h2 := (hx i).2
    rw [Subtype.dist_eq, Real.dist_eq, abs_le]
    constructor <;> · field_simp; linarith
  have hmesh : 1/(n:ℝ) < δ := lt_of_lt_of_le hlt (min_le_left _ _)
  have hmesh₂ : 3/(n:ℝ) < δ₂ := by
    have h := lt_of_lt_of_le hlt (min_le_right _ _)
    rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 3)] at h
    have h32 : (1/(n:ℝ)) * 3 = 3/(n:ℝ) := by ring
    rw [h32] at h
    exact h
  have hlab : ((∀ x : IC j, x ∈ boxSet m → f x ∈ U) ∨
      (∀ x : IC j, x ∈ boxSet m → f x ∈ V)) := by
    obtain ⟨b, hb⟩ := hδ (fun i => (⟨((m i : ℝ) + 1/2) / (n:ℝ), by
      constructor
      · positivity
      · rw [div_le_one hnp]
        have hm' : (m i : ℕ) + 1 ≤ n := Nat.succ_le_of_lt (m i).isLt
        have : (m i : ℝ) + 1 ≤ (n:ℝ) := by exact_mod_cast hm'
        linarith⟩ : unitInterval)) (Set.mem_univ _)
    cases b with
    | false => left; intro x hx; exact hb (lt_of_le_of_lt (hmem hx) hmesh)
    | true => right; intro x hx; exact hb (lt_of_le_of_lt (hmem hx) hmesh)
  refine ⟨hlab, fun hnear y hy => ?_⟩
  obtain ⟨i, hi⟩ := hnear
  -- the `i`-th scaled coordinate of `y` is within `2` of an end
  have hyi : (n:ℝ) * (y i : ℝ) ≤ 2 ∨ (n:ℝ) - 2 ≤ (n:ℝ) * (y i : ℝ) := by
    rcases hi with h | h | h | h
    · left; have h2 := (hy i).2; rw [h] at h2; push_cast at h2; linarith
    · left; have h2 := (hy i).2; rw [h] at h2; push_cast at h2; linarith
    · right
      have h1 := (hy i).1; rw [h] at h1
      have hcast : (((n - 2 : ℕ)) : ℝ) = (n:ℝ) - 2 := by
        rw [Nat.cast_sub (by omega : 2 ≤ n)]; norm_num
      rw [hcast] at h1; linarith
    · right
      have h1 := (hy i).1; rw [h] at h1
      have hcast : (((n - 1 : ℕ)) : ℝ) = (n:ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
      rw [hcast] at h1; linarith
  have hyi' : (y i : ℝ) ≤ 2/(n:ℝ) ∨ 1 - (y i : ℝ) ≤ 2/(n:ℝ) := by
    rcases hyi with h | h
    · left; rw [le_div_iff₀ hnp]; nlinarith [h]
    · right; rw [le_div_iff₀ hnp]; nlinarith [h]
  have htwo : 2/(n:ℝ) < δ₂ := by
    have : 2/(n:ℝ) < 3/(n:ℝ) := by rw [div_lt_div_iff_of_pos_right hnp]; norm_num
    linarith
  rcases hyi' with hyi' | hyi'
  · refine hδ₂ (Metric.thickening_subset_cthickening δ₂ _ ?_)
    rw [Metric.mem_thickening_iff]
    refine ⟨Function.update y i 0, ⟨i, Or.inl (Function.update_self i (0:unitInterval) y)⟩, ?_⟩
    refine lt_of_le_of_lt ?_ htwo
    rw [dist_pi_le_iff (by positivity)]
    intro k
    rw [Subtype.dist_eq, Real.dist_eq, Function.update_apply]
    by_cases hk : k = i
    · rw [if_pos hk, show ((0:unitInterval):ℝ) = 0 from rfl, sub_zero,
        abs_of_nonneg (y k).2.1]
      simpa [hk] using hyi'
    · rw [if_neg hk, sub_self, abs_zero]
      positivity
  · refine hδ₂ (Metric.thickening_subset_cthickening δ₂ _ ?_)
    rw [Metric.mem_thickening_iff]
    refine ⟨Function.update y i 1, ⟨i, Or.inr (Function.update_self i (1:unitInterval) y)⟩, ?_⟩
    refine lt_of_le_of_lt ?_ htwo
    rw [dist_pi_le_iff (by positivity)]
    intro k
    rw [Subtype.dist_eq, Real.dist_eq, Function.update_apply]
    by_cases hk : k = i
    · rw [if_pos hk, show ((1:unitInterval):ℝ) = 1 from rfl,
        abs_of_nonpos (by have := (y k).2.2; linarith : (y k : ℝ) - 1 ≤ 0)]
      simpa [hk] using hyi'
    · rw [if_neg hk, sub_self, abs_zero]
      positivity

end Work.ThomBordism.TwoSet
