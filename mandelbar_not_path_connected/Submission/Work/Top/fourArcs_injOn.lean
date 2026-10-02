/-
# The four-arc concatenation is injective on `[0,1)`

Given four injective arcs `γ₁ γ₂ γ₃ γ₄ : C(unitInterval, ℂ)` which close up into a loop
(`γ₁ 1 = γ₂ 0`, `γ₂ 1 = γ₃ 0`, `γ₃ 1 = γ₄ 0`, `γ₄ 1 = γ₁ 0`) and such that distinct arcs
meet only in the single point at which they are glued (`range γ₁ ∩ range γ₂ = {γ₁ 1}`, etc.,
and `range γ₁`, `range γ₃` as well as `range γ₂`, `range γ₄` are disjoint), the concatenation
`fourArcs γ₁ γ₂ γ₃ γ₄` is injective on the half-open interval `[0,1)`.

The parameter `1` (which would repeat the starting point `γ₁ 0 = γ₄ 1`) is excluded, and that
is exactly what makes the statement true: with `t ∈ [0,1)` the four pieces are traversed on
the four sub-intervals `[0,1/4]`, `(1/4,1/2]`, `(1/2,3/4]`, `(3/4,1)`.
-/
import Mathlib
import Submission.Work.Top.FourArcsDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Set
open scoped Topology

noncomputable section

namespace Work.Top

/-! ## Elementary helper lemmas -/

/-- Two points of `unitInterval` giving the same value under the arc `γ` are equal. -/
theorem arcPt_inj_of_injective {γ : C(unitInterval, ℂ)} (hγ : Function.Injective γ)
    {c d : ℝ} (hc : c ∈ unitInterval) (hd : d ∈ unitInterval)
    (h : arcPt γ c = arcPt γ d) : c = d := by
  rw [arcPt_of_mem γ hc, arcPt_of_mem γ hd] at h
  exact congrArg Subtype.val (hγ h)

/-- In a set which is a singleton, every member equals the singleton element. -/
theorem eq_of_mem_inter_singleton {A B : Set ℂ} {w : ℂ} (h : A ∩ B = {w}) {z : ℂ}
    (hzA : z ∈ A) (hzB : z ∈ B) : z = w := by
  have hz : z ∈ A ∩ B := ⟨hzA, hzB⟩
  rw [h] at hz
  exact Set.mem_singleton_iff.mp hz

/-- Two disjoint sets share no point. -/
theorem false_of_disjoint_of_mem {A B : Set ℂ} (h : Disjoint A B) {z : ℂ} (hzA : z ∈ A)
    (hzB : z ∈ B) : False := by
  have hz : z ∈ A ∩ B := ⟨hzA, hzB⟩
  exact h.le_bot hz

/-- Each real number lies in one of the four parameter regions of the concatenation. -/
theorem fourArcs_region (x : ℝ) :
    x ≤ 1/4 ∨ (1/4 < x ∧ x ≤ 1/2) ∨ (1/2 < x ∧ x ≤ 3/4) ∨ 3/4 < x := by
  by_cases h : x ≤ 1/4
  · exact Or.inl h
  · rw [not_le] at h
    by_cases h2 : x ≤ 1/2
    · exact Or.inr (Or.inl ⟨h, h2⟩)
    · rw [not_le] at h2
      by_cases h3 : x ≤ 3/4
      · exact Or.inr (Or.inr (Or.inl ⟨h2, h3⟩))
      · exact Or.inr (Or.inr (Or.inr (not_le.mp h3)))

/-! ## The four affine reparametrisations land in `unitInterval` -/

theorem four_mul_mem_unitInterval {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1/4) :
    (4 * t) ∈ unitInterval := by
  rw [unitInterval, Set.mem_Icc]; constructor <;> linarith

theorem four_mul_sub_one_mem_unitInterval {t : ℝ} (h0 : 1/4 ≤ t) (h1 : t ≤ 1/2) :
    (4 * t - 1) ∈ unitInterval := by
  rw [unitInterval, Set.mem_Icc]; constructor <;> linarith

theorem four_mul_sub_two_mem_unitInterval {t : ℝ} (h0 : 1/2 ≤ t) (h1 : t ≤ 3/4) :
    (4 * t - 2) ∈ unitInterval := by
  rw [unitInterval, Set.mem_Icc]; constructor <;> linarith

theorem four_mul_sub_three_mem_unitInterval {t : ℝ} (h0 : 3/4 ≤ t) (h1 : t ≤ 1) :
    (4 * t - 3) ∈ unitInterval := by
  rw [unitInterval, Set.mem_Icc]; constructor <;> linarith

/-! ## Gluing two adjacent arcs -/

/-- If two injective arcs meet only in `γ 1 = δ 0`, then a common point of the two arcs can
only be obtained by taking `a = 1` in the first arc and `b = 0` in the second. -/
theorem arcPt_eq_endpoints_of_adjacent {γ δ : C(unitInterval, ℂ)} (hγ : Function.Injective γ)
    (hδ : Function.Injective δ) (hinter : Set.range γ ∩ Set.range δ = {γ 1})
    (hlink : γ 1 = δ 0) {a b : ℝ} (ha : a ∈ unitInterval) (hb : b ∈ unitInterval)
    (h : arcPt γ a = arcPt δ b) : a = 1 ∧ b = 0 := by
  have hmem : arcPt γ a ∈ Set.range γ ∩ Set.range δ :=
    ⟨arcPt_mem_range γ a, by rw [h]; exact arcPt_mem_range δ b⟩
  have hz : arcPt γ a = γ 1 := eq_of_mem_inter_singleton hinter hmem.1 hmem.2
  have ha1 : a = 1 := by
    rw [← arcPt_one γ] at hz
    exact arcPt_inj_of_injective hγ ha (by rw [unitInterval, Set.mem_Icc]; norm_num) hz
  have hb0 : b = 0 := by
    have hz2 : arcPt δ b = arcPt δ 0 := by rw [← h, hz, hlink, arcPt_zero δ]
    exact arcPt_inj_of_injective hδ hb (by rw [unitInterval, Set.mem_Icc]; norm_num) hz2
  exact ⟨ha1, hb0⟩

/-- The same as `arcPt_eq_endpoints_of_adjacent`, with the roles of the two intermediate
endpoints interchanged: if the arcs meet only in `γ 0 = δ 1`, then a common point forces
`a = 0` and `b = 1`. -/
theorem arcPt_eq_endpoints_of_adjacent_rev {γ δ : C(unitInterval, ℂ)}
    (hγ : Function.Injective γ) (hδ : Function.Injective δ)
    (hinter : Set.range γ ∩ Set.range δ = {γ 0}) (hlink : γ 0 = δ 1) {a b : ℝ}
    (ha : a ∈ unitInterval) (hb : b ∈ unitInterval) (h : arcPt γ a = arcPt δ b) :
    a = 0 ∧ b = 1 := by
  have hmem : arcPt γ a ∈ Set.range γ ∩ Set.range δ :=
    ⟨arcPt_mem_range γ a, by rw [h]; exact arcPt_mem_range δ b⟩
  have hz : arcPt γ a = γ 0 := eq_of_mem_inter_singleton hinter hmem.1 hmem.2
  have ha0 : a = 0 := by
    rw [← arcPt_zero γ] at hz
    exact arcPt_inj_of_injective hγ ha (by rw [unitInterval, Set.mem_Icc]; norm_num) hz
  have hb1 : b = 1 := by
    have hz2 : arcPt δ b = arcPt δ 1 := by rw [← h, hz, hlink, arcPt_one δ]
    exact arcPt_inj_of_injective hδ hb (by rw [unitInterval, Set.mem_Icc]; norm_num) hz2
  exact ⟨ha0, hb1⟩

/-- Disjointness of two arcs rules out a common value of the parametrisations. -/
theorem false_of_arcPt_eq_of_disjoint {γ δ : C(unitInterval, ℂ)}
    (hdis : Disjoint (Set.range γ) (Set.range δ)) {a b : ℝ}
    (h : arcPt γ a = arcPt δ b) : False :=
  false_of_disjoint_of_mem hdis (arcPt_mem_range γ a)
    (by rw [h]; exact arcPt_mem_range δ b)

/-! ## The main statement -/

theorem fourArcs_injOn (γ₁ γ₂ γ₃ γ₄ : C(unitInterval, ℂ))
    (h₁ : Function.Injective γ₁) (h₂ : Function.Injective γ₂)
    (h₃ : Function.Injective γ₃) (h₄ : Function.Injective γ₄)
    (h₁₂ : γ₁ 1 = γ₂ 0) (h₂₃ : γ₂ 1 = γ₃ 0) (h₃₄ : γ₃ 1 = γ₄ 0) (h₄₁ : γ₄ 1 = γ₁ 0)
    (hd₁₂ : Set.range γ₁ ∩ Set.range γ₂ = {γ₁ 1})
    (hd₂₃ : Set.range γ₂ ∩ Set.range γ₃ = {γ₂ 1})
    (hd₃₄ : Set.range γ₃ ∩ Set.range γ₄ = {γ₃ 1})
    (hd₄₁ : Set.range γ₄ ∩ Set.range γ₁ = {γ₄ 1})
    (hd₁₃ : Disjoint (Set.range γ₁) (Set.range γ₃))
    (hd₂₄ : Disjoint (Set.range γ₂) (Set.range γ₄)) :
    Set.InjOn (fourArcs γ₁ γ₂ γ₃ γ₄) (Set.Ico (0:ℝ) 1) := by
  intro t ht u hu htu
  rw [Set.mem_Ico] at ht hu
  obtain ⟨ht0, ht1⟩ := ht
  obtain ⟨hu0, hu1⟩ := hu
  -- The "reversed" intersection identities (shared point written as the left arc's initial
  -- point), obtained by symmetry and the gluing relations.
  have hd₁₄ : Set.range γ₁ ∩ Set.range γ₄ = {γ₁ 0} := by rw [Set.inter_comm, hd₄₁, h₄₁]
  have hd₂₁ : Set.range γ₂ ∩ Set.range γ₁ = {γ₂ 0} := by rw [Set.inter_comm, hd₁₂, h₁₂]
  have hd₃₂ : Set.range γ₃ ∩ Set.range γ₂ = {γ₃ 0} := by rw [Set.inter_comm, hd₂₃, h₂₃]
  have hd₄₃ : Set.range γ₄ ∩ Set.range γ₃ = {γ₄ 0} := by rw [Set.inter_comm, hd₃₄, h₃₄]
  rcases fourArcs_region t with hT | ⟨hTa, hTb⟩ | ⟨hTa, hTb⟩ | hT
  · -- `t ∈ [0,1/4]`: the first piece.
    rw [fourArcs_eq_arcPt₁ γ₁ γ₂ γ₃ γ₄ hT] at htu
    rcases fourArcs_region u with hU | ⟨hUa, hUb⟩ | ⟨hUa, hUb⟩ | hU
    · rw [fourArcs_eq_arcPt₁ γ₁ γ₂ γ₃ γ₄ hU] at htu
      have h4 := arcPt_inj_of_injective h₁
        (four_mul_mem_unitInterval ht0 hT) (four_mul_mem_unitInterval hu0 hU) htu
      linarith
    · rw [fourArcs_eq_arcPt₂ γ₁ γ₂ γ₃ γ₄ hUa hUb] at htu
      obtain ⟨ha, hb⟩ := arcPt_eq_endpoints_of_adjacent h₁ h₂ hd₁₂ h₁₂
        (four_mul_mem_unitInterval ht0 hT)
        (four_mul_sub_one_mem_unitInterval hUa.le hUb) htu
      linarith
    · rw [fourArcs_eq_arcPt₃ γ₁ γ₂ γ₃ γ₄ hUa hUb] at htu
      exact (false_of_arcPt_eq_of_disjoint hd₁₃ htu).elim
    · rw [fourArcs_eq_arcPt₄ γ₁ γ₂ γ₃ γ₄ hU] at htu
      obtain ⟨ha, hb⟩ := arcPt_eq_endpoints_of_adjacent_rev h₁ h₄ hd₁₄ h₄₁.symm
        (four_mul_mem_unitInterval ht0 hT)
        (four_mul_sub_three_mem_unitInterval hU.le hu1.le) htu
      linarith
  · -- `t ∈ (1/4,1/2]`: the second piece.
    rw [fourArcs_eq_arcPt₂ γ₁ γ₂ γ₃ γ₄ hTa hTb] at htu
    rcases fourArcs_region u with hU | ⟨hUa, hUb⟩ | ⟨hUa, hUb⟩ | hU
    · rw [fourArcs_eq_arcPt₁ γ₁ γ₂ γ₃ γ₄ hU] at htu
      obtain ⟨ha, hb⟩ := arcPt_eq_endpoints_of_adjacent_rev h₂ h₁ hd₂₁ h₁₂.symm
        (four_mul_sub_one_mem_unitInterval hTa.le hTb) (four_mul_mem_unitInterval hu0 hU) htu
      linarith
    · rw [fourArcs_eq_arcPt₂ γ₁ γ₂ γ₃ γ₄ hUa hUb] at htu
      have h4 := arcPt_inj_of_injective h₂
        (four_mul_sub_one_mem_unitInterval hTa.le hTb)
        (four_mul_sub_one_mem_unitInterval hUa.le hUb) htu
      linarith
    · rw [fourArcs_eq_arcPt₃ γ₁ γ₂ γ₃ γ₄ hUa hUb] at htu
      obtain ⟨ha, hb⟩ := arcPt_eq_endpoints_of_adjacent h₂ h₃ hd₂₃ h₂₃
        (four_mul_sub_one_mem_unitInterval hTa.le hTb)
        (four_mul_sub_two_mem_unitInterval hUa.le hUb) htu
      linarith
    · rw [fourArcs_eq_arcPt₄ γ₁ γ₂ γ₃ γ₄ hU] at htu
      exact (false_of_arcPt_eq_of_disjoint hd₂₄ htu).elim
  · -- `t ∈ (1/2,3/4]`: the third piece.
    rw [fourArcs_eq_arcPt₃ γ₁ γ₂ γ₃ γ₄ hTa hTb] at htu
    rcases fourArcs_region u with hU | ⟨hUa, hUb⟩ | ⟨hUa, hUb⟩ | hU
    · rw [fourArcs_eq_arcPt₁ γ₁ γ₂ γ₃ γ₄ hU] at htu
      exact (false_of_arcPt_eq_of_disjoint hd₁₃.symm htu).elim
    · rw [fourArcs_eq_arcPt₂ γ₁ γ₂ γ₃ γ₄ hUa hUb] at htu
      obtain ⟨ha, hb⟩ := arcPt_eq_endpoints_of_adjacent_rev h₃ h₂ hd₃₂ h₂₃.symm
        (four_mul_sub_two_mem_unitInterval hTa.le hTb)
        (four_mul_sub_one_mem_unitInterval hUa.le hUb) htu
      linarith
    · rw [fourArcs_eq_arcPt₃ γ₁ γ₂ γ₃ γ₄ hUa hUb] at htu
      have h4 := arcPt_inj_of_injective h₃
        (four_mul_sub_two_mem_unitInterval hTa.le hTb)
        (four_mul_sub_two_mem_unitInterval hUa.le hUb) htu
      linarith
    · rw [fourArcs_eq_arcPt₄ γ₁ γ₂ γ₃ γ₄ hU] at htu
      obtain ⟨ha, hb⟩ := arcPt_eq_endpoints_of_adjacent h₃ h₄ hd₃₄ h₃₄
        (four_mul_sub_two_mem_unitInterval hTa.le hTb)
        (four_mul_sub_three_mem_unitInterval hU.le hu1.le) htu
      linarith
  · -- `t ∈ (3/4,1)`: the fourth piece.
    rw [fourArcs_eq_arcPt₄ γ₁ γ₂ γ₃ γ₄ hT] at htu
    rcases fourArcs_region u with hU | ⟨hUa, hUb⟩ | ⟨hUa, hUb⟩ | hU
    · rw [fourArcs_eq_arcPt₁ γ₁ γ₂ γ₃ γ₄ hU] at htu
      obtain ⟨ha, hb⟩ := arcPt_eq_endpoints_of_adjacent h₄ h₁ hd₄₁ h₄₁
        (four_mul_sub_three_mem_unitInterval hT.le ht1.le)
        (four_mul_mem_unitInterval hu0 hU) htu
      linarith
    · rw [fourArcs_eq_arcPt₂ γ₁ γ₂ γ₃ γ₄ hUa hUb] at htu
      exact (false_of_arcPt_eq_of_disjoint hd₂₄.symm htu).elim
    · rw [fourArcs_eq_arcPt₃ γ₁ γ₂ γ₃ γ₄ hUa hUb] at htu
      obtain ⟨ha, hb⟩ := arcPt_eq_endpoints_of_adjacent_rev h₄ h₃ hd₄₃ h₃₄.symm
        (four_mul_sub_three_mem_unitInterval hT.le ht1.le)
        (four_mul_sub_two_mem_unitInterval hUa.le hUb) htu
      linarith
    · rw [fourArcs_eq_arcPt₄ γ₁ γ₂ γ₃ γ₄ hU] at htu
      have h4 := arcPt_inj_of_injective h₄
        (four_mul_sub_three_mem_unitInterval hT.le ht1.le)
        (four_mul_sub_three_mem_unitInterval hU.le hu1.le) htu
      linarith

end Work.Top
