import Mathlib
import Submission.Work.GlaubermanZJ.Thm41.commutator_lowerCentralSeries_le

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.Higman.MSA

open scoped commutatorElement

/-- **Class two from uniqueness of the abelian characteristic subgroups.**  If every abelian
characteristic subgroup of a nilpotent group `G` is either trivial or the centre, then
`[G,G] ≤ Z(G)`. -/
theorem commutator_le_center_of_unique_abelian_char {G : Type} [Group G]
    (hnil : Group.IsNilpotent G)
    (huniq : ∀ B : Subgroup G, B.Characteristic → (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      B = ⊥ ∨ B = Subgroup.center G) :
    ⁅(⊤ : Subgroup G), ⊤⁆ ≤ Subgroup.center G := by
  classical
  haveI : Group.IsNilpotent G := hnil
  -- The nilpotency class of `G` is at most two.
  have hclass : Group.nilpotencyClass G ≤ 2 := by
    by_contra hk
    rw [not_le] at hk
    obtain ⟨m, hm⟩ : ∃ m, Group.nilpotencyClass G = m + 2 :=
      ⟨Group.nilpotencyClass G - 2, by omega⟩
    -- `B` is the `m`-th term of the lower central series, with `m ≥ 1`.
    set B : Subgroup G := (⊤ : Subgroup G).lowerCentralSeries m with hB
    have hBchar : B.Characteristic := by rw [hB]; infer_instance
    have hBne : B ≠ ⊥ := by
      rw [hB]
      intro hbot
      have hle := (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le (n := m)).mp hbot
      omega
    -- `B` is abelian, because `⁅B, B⁆ ≤ γ_{2m+1} = ⊥` as `m ≥ 1`.
    have hBabel : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
      intro x hx y hy
      have hmem : ⁅x, y⁆ ∈ ⁅B, B⁆ := Subgroup.commutator_mem_commutator hx hy
      have hle : ⁅B, B⁆ ≤ (⊤ : Subgroup G).lowerCentralSeries (m + m + 1) := by
        rw [hB]
        exact Work.GlaubermanZJ.Thm41.commutator_lowerCentralSeries_le (⊤ : Subgroup G) m m
      have hbot : (⊤ : Subgroup G).lowerCentralSeries (m + m + 1) = ⊥ :=
        (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le (n := m + m + 1)).mpr
          (by omega)
      have hone : ⁅x, y⁆ = 1 := by
        have hmem' := hle hmem
        rw [hbot] at hmem'
        exact Subgroup.mem_bot.mp hmem'
      exact commutatorElement_eq_one_iff_mul_comm.mp hone
    have hBcenter : B = Subgroup.center G := by
      rcases huniq B hBchar hBabel with h | h
      · exact absurd h hBne
      · exact h
    -- Hence the next term of the lower central series is trivial ...
    have hnext : (⊤ : Subgroup G).lowerCentralSeries (m + 1) = ⊥ := by
      rw [Subgroup.lowerCentralSeries_succ, ← hB, hBcenter]
      exact Subgroup.commutator_center_left (⊤ : Subgroup G)
    -- ... contradicting minimality of the nilpotency class.
    have hnextne : (⊤ : Subgroup G).lowerCentralSeries (m + 1) ≠ ⊥ := by
      intro hbot
      have hle := (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le (n := m + 1)).mp hbot
      omega
    exact hnextne hnext
  -- `γ₂ = ⁅γ₁, ⊤⁆ = ⊥` because the class is at most two, so `γ₁` is central.
  have h2 : (⊤ : Subgroup G).lowerCentralSeries 2 = ⊥ :=
    (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le (n := 2)).mpr hclass
  have hstep : (⊤ : Subgroup G).lowerCentralSeries 2 =
      ⁅(⊤ : Subgroup G).lowerCentralSeries 1, (⊤ : Subgroup G)⁆ :=
    Subgroup.lowerCentralSeries_succ (⊤ : Subgroup G) 1
  rw [hstep] at h2
  have h1 : (⊤ : Subgroup G).lowerCentralSeries 1 ≤ Subgroup.center G :=
    (Subgroup.commutator_top_right_eq_bot_iff_le_center).mp h2
  rwa [Subgroup.top_lowerCentralSeries_one, _root_.commutator_def] at h1

end Work.Higman.MSA
