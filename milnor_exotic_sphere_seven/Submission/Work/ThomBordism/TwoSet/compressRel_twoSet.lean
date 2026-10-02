import Mathlib
import Submission.Work.ThomBordism.TwoSet.Fold
import Submission.Work.ThomBordism.TwoSet.CollarSubdivision

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.ThomBordism.TwoSet

theorem compressRel_twoSet {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (j : ℕ)
    (hVc : ∀ d, d ≤ j → Work.ThomBordism.TwoSet.Compress ↥V {v : ↥V | (v : X) ∈ U} d)
    (hUc : ∀ d, d ≤ j → Work.ThomBordism.TwoSet.Compress ↥U {u : ↥U | (u : X) ∈ V} d) :
    Work.ThomBordism.TwoSet.Compress X U j := by
  classical
  intro f hf
  obtain ⟨N, hN3, hsub⟩ := SubdivisionCollared hU hV hcov f hf
  have hNpos : (0 : ℝ) < N := by
    have : (0 : ℕ) < N := by omega
    exact_mod_cast this
  let lab : (Fin j → Fin N) → Bool := fun m => decide (¬ ∀ x : IC j, x ∈ boxSet m → f x ∈ U)
  have hlabU : ∀ m, lab m = false → ∀ x ∈ boxSet m, f x ∈ U := by
    intro m hm
    have hm' : decide (¬ ∀ x : IC j, x ∈ boxSet m → f x ∈ U) = false := hm
    have h2 : ¬ ¬ (∀ x : IC j, x ∈ boxSet m → f x ∈ U) := of_decide_eq_false hm'
    exact fun x hx => (not_not.mp h2) x hx
  have hlabV : ∀ m, lab m = true → ∀ x ∈ boxSet m, f x ∈ V := by
    intro m hm x hx
    have hm' : decide (¬ ∀ x : IC j, x ∈ boxSet m → f x ∈ U) = true := hm
    have hneg : ¬ ∀ x : IC j, x ∈ boxSet m → f x ∈ U := of_decide_eq_true hm'
    rcases (hsub m).1 with h | h
    · exact absurd h hneg
    · exact h x hx
  have hfar : ∀ m, lab m = true → ∀ x ∈ boxSet m, ∀ i,
      2/(N:ℝ) ≤ (x i : ℝ) ∧ (x i : ℝ) ≤ 1 - 2/(N:ℝ) := by
    intro m hm x hx i
    have hm' : decide (¬ ∀ x : IC j, x ∈ boxSet m → f x ∈ U) = true := hm
    have hneg : ¬ ∀ x : IC j, x ∈ boxSet m → f x ∈ U := of_decide_eq_true hm'
    have hnot : ¬ (∃ i, (m i : ℕ) = 0 ∨ (m i : ℕ) = 1 ∨ (m i : ℕ) = N - 2 ∨
        (m i : ℕ) = N - 1) := by
      rintro ⟨i, hi⟩
      exact hneg fun y hy => (hsub m).2 ⟨i, hi⟩ y hy
    have hmge : 2 ≤ (m i : ℕ) := by
      by_contra hcon
      exact hnot ⟨i, by omega⟩
    have hmle : (m i : ℕ) ≤ N - 3 := by
      have h1 : (m i : ℕ) < N := (m i).isLt
      by_contra hcon
      exact hnot ⟨i, by omega⟩
    have hxi := hx i
    constructor
    · have h2 : (2 : ℝ) ≤ (N : ℝ) * (x i : ℝ) := by
        have h3 : (2 : ℝ) ≤ ((m i : ℕ) : ℝ) := by exact_mod_cast hmge
        linarith [hxi.1]
      exact (div_le_iff₀ hNpos).mpr (by linarith [h2])
    · have h2 : (N : ℝ) * (x i : ℝ) ≤ (N : ℝ) - 2 := by
        have h3 : ((m i : ℕ) + 1 : ℕ) ≤ N - 2 := by omega
        have h4 : (((m i : ℕ) + 1 : ℕ) : ℝ) ≤ ((N - 2 : ℕ) : ℝ) := by exact_mod_cast h3
        have h5 : ((N - 2 : ℕ) : ℝ) = (N : ℝ) - 2 := by
          rw [Nat.cast_sub (by omega : 2 ≤ N)]
          norm_num
        rw [h5] at h4
        push_cast at h4
        linarith [hxi.2]
      have h6 : (x i : ℝ) ≤ ((N : ℝ) - 2) / N := by
        rw [le_div_iff₀ hNpos]
        linarith [h2]
      have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
      have h7 : ((N : ℝ) - 2) / N = 1 - 2/(N : ℝ) := by
        field_simp
      linarith [h6, h7]
  exact processCells hN3 lab hVc hUc hfar f hlabU hlabV hf

end Work.ThomBordism.TwoSet
