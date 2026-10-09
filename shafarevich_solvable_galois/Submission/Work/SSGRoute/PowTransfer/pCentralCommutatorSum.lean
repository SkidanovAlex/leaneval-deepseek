import Mathlib
import Submission.Work.Shrinking.PCentral
import Submission.Work.Shrinking.pCentralSeries_normal
import Submission.Work.Shrinking.pCentralSeries_antitone
import Submission.Work.Shrinking.pow_mem_pCentralSeries_succ
import Submission.Work.Shrinking.commutator_le_pCentralSeries_succ
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.SSGRoute.PowTransfer

open scoped commutatorElement

/-- The Three Subgroups Lemma (local copy, kept dependency-free). -/
theorem ssg_three_subgroups_le {G : Type*} [Group G] {H₁ H₂ H₃ K : Subgroup G} (hK : K.Normal)
    (h1 : ⁅⁅H₂, H₃⁆, H₁⁆ ≤ K) (h2 : ⁅⁅H₃, H₁⁆, H₂⁆ ≤ K) :
    ⁅⁅H₁, H₂⁆, H₃⁆ ≤ K := by
  let π : G →* G ⧸ K := QuotientGroup.mk' K
  have key : ∀ X : Subgroup G, X ≤ K → Subgroup.map π X = ⊥ := by
    intro X hX
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hX
  have h1' : ⁅⁅Subgroup.map π H₂, Subgroup.map π H₃⁆, Subgroup.map π H₁⁆ = ⊥ := by
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator]
    exact key _ h1
  have h2' : ⁅⁅Subgroup.map π H₃, Subgroup.map π H₁⁆, Subgroup.map π H₂⁆ = ⊥ := by
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator]
    exact key _ h2
  have hgoal : Subgroup.map π ⁅⁅H₁, H₂⁆, H₃⁆ = ⊥ := by
    rw [Subgroup.map_commutator, Subgroup.map_commutator]
    exact Subgroup.commutator_commutator_eq_bot_of_rotate h1' h2'
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hgoal
  exact hgoal

/-- `[P_m, P_n] ≤ P_{m+n+1}` for the descending `2`-central series (0-indexed:
`pCentralSeries 2 P k` is the paper's `P_{k+1}`). -/
theorem commutator_pCentralSeries_two_le (P : Type*) [Group P] (m n : ℕ) :
    ⁅Work.Shrinking.pCentralSeries 2 P m, Work.Shrinking.pCentralSeries 2 P n⁆
      ≤ Work.Shrinking.pCentralSeries 2 P (m + n + 1) := by
  have main : ∀ n m : ℕ,
      ⁅Work.Shrinking.pCentralSeries 2 P m, Work.Shrinking.pCentralSeries 2 P n⁆
        ≤ Work.Shrinking.pCentralSeries 2 P (m + n + 1) := by
    intro n
    induction n with
    | zero =>
        intro m
        rw [Work.Shrinking.pCentralSeries_zero]
        simpa using (Work.Shrinking.commutator_le_pCentralSeries_succ 2 P m).1
    | succ n ih =>
        intro m
        rw [show m + (n + 1) + 1 = m + n + 2 from by omega]
        haveI hg : (Work.Shrinking.pCentralSeries 2 P n).Normal :=
          Work.Shrinking.pCentralSeries_normal 2 P n
        haveI hpow : (Work.Shrinking.pCentralSeries 2 P (m + n + 1)).Normal :=
          Work.Shrinking.pCentralSeries_normal 2 P (m + n + 1)
        haveI hpow2 : (Work.Shrinking.pCentralSeries 2 P (m + n + 2)).Normal :=
          Work.Shrinking.pCentralSeries_normal 2 P (m + n + 2)
        haveI hcommnorm : (⁅Work.Shrinking.pCentralSeries 2 P n, ⊤⁆ : Subgroup P).Normal :=
          Subgroup.commutator_normal _ _
        -- The subgroup of `2`-powers.
        have hP : ⁅Work.Shrinking.pCentralSeries 2 P m,
              Work.Shrinking.powSubgroup 2 (Work.Shrinking.pCentralSeries 2 P n)⁆
            ≤ Work.Shrinking.pCentralSeries 2 P (m + n + 2) := by
          rw [Subgroup.commutator_le]
          intro g hg2 a ha
          show ⁅g, a⁆ ∈ Work.Shrinking.pCentralSeries 2 P (m + n + 2)
          rw [Work.Shrinking.powSubgroup] at ha
          induction ha using Subgroup.closure_induction with
          | mem x hx =>
              obtain ⟨y, hy, rfl⟩ := hx
              have hc : ⁅g, y⁆ ∈ Work.Shrinking.pCentralSeries 2 P (m + n + 1) :=
                ih m (Subgroup.commutator_mem_commutator hg2 hy)
              have hsq : ⁅g, y⁆ ^ 2 ∈ Work.Shrinking.pCentralSeries 2 P (m + n + 2) := by
                rw [show m + n + 2 = (m + n + 1) + 1 from by omega,
                  Work.Shrinking.pCentralSeries_succ, Work.Shrinking.pCentralStep]
                exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨⁅g, y⁆, hc, rfl⟩)
              have hcm : ⁅⁅g, y⁆⁻¹, y⁆ ∈ Work.Shrinking.pCentralSeries 2 P (m + n + 2) :=
                Work.Shrinking.pCentralSeries_antitone 2 P (by omega)
                  (ih (m + n + 1) (Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ hc) hy))
              simp only [pow_two]
              rw [commutatorElement_mul_right_eq_mul_conj]
              rw [show ⁅g, y⁆ * y * ⁅g, y⁆ * y⁻¹
                    = ⁅g, y⁆ ^ 2 * ⁅⁅g, y⁆⁻¹, y⁆ by
                simp only [commutatorElement_def, pow_two]; group]
              exact Subgroup.mul_mem _ hsq hcm
          | one => simp
          | mul x y hx hy ihx ihy =>
              rw [commutatorElement_mul_right_eq_mul_conj]
              have hconj : x * ⁅g, y⁆ * x⁻¹ ∈ Work.Shrinking.pCentralSeries 2 P (m + n + 2) :=
                (inferInstance :
                  (Work.Shrinking.pCentralSeries 2 P (m + n + 2)).Normal).conj_mem
                  ⁅g, y⁆ ihy x
              simpa only [mul_assoc] using
                (Work.Shrinking.pCentralSeries 2 P (m + n + 2)).mul_mem ihx hconj
          | inv x hx ihx =>
              rw [commutatorElement_inv_right]
              have hmem : ⁅x, g⁆ ∈ Work.Shrinking.pCentralSeries 2 P (m + n + 2) := by
                rw [← commutatorElement_inv g x]
                exact Subgroup.inv_mem _ ihx
              simpa using (inferInstance :
                (Work.Shrinking.pCentralSeries 2 P (m + n + 2)).Normal).conj_mem ⁅x, g⁆ hmem x⁻¹
        -- The commutator part, via the Three Subgroups Lemma.
        have hQ : ⁅Work.Shrinking.pCentralSeries 2 P m,
              ⁅Work.Shrinking.pCentralSeries 2 P n, ⊤⁆⁆
            ≤ Work.Shrinking.pCentralSeries 2 P (m + n + 2) := by
          rw [Subgroup.commutator_comm (Work.Shrinking.pCentralSeries 2 P m)
            ⁅Work.Shrinking.pCentralSeries 2 P n, ⊤⁆]
          refine ssg_three_subgroups_le
            (H₁ := Work.Shrinking.pCentralSeries 2 P n) (H₂ := ⊤)
            (H₃ := Work.Shrinking.pCentralSeries 2 P m)
            (Work.Shrinking.pCentralSeries_normal 2 P (m + n + 2)) ?_ ?_
          · have h1 : ⁅(⊤ : Subgroup P), Work.Shrinking.pCentralSeries 2 P m⁆
                ≤ Work.Shrinking.pCentralSeries 2 P (m + 1) := by
              rw [Subgroup.commutator_comm]
              exact (Work.Shrinking.commutator_le_pCentralSeries_succ 2 P m).1
            calc ⁅⁅(⊤ : Subgroup P), Work.Shrinking.pCentralSeries 2 P m⁆,
                    Work.Shrinking.pCentralSeries 2 P n⁆
                ≤ ⁅Work.Shrinking.pCentralSeries 2 P (m + 1),
                    Work.Shrinking.pCentralSeries 2 P n⁆ := Subgroup.commutator_mono h1 le_rfl
              _ ≤ Work.Shrinking.pCentralSeries 2 P ((m + 1) + n + 1) := ih (m + 1)
              _ = Work.Shrinking.pCentralSeries 2 P (m + n + 2) := by
                    rw [show (m + 1) + n + 1 = m + n + 2 from by omega]
          · calc ⁅⁅Work.Shrinking.pCentralSeries 2 P m, Work.Shrinking.pCentralSeries 2 P n⁆,
                    (⊤ : Subgroup P)⁆
                ≤ ⁅Work.Shrinking.pCentralSeries 2 P (m + n + 1), (⊤ : Subgroup P)⁆ :=
                  Subgroup.commutator_mono (ih m) le_rfl
              _ ≤ Work.Shrinking.pCentralSeries 2 P ((m + n + 1) + 1) :=
                  (Work.Shrinking.commutator_le_pCentralSeries_succ 2 P (m + n + 1)).1
              _ = Work.Shrinking.pCentralSeries 2 P (m + n + 2) := by
                    rw [show (m + n + 1) + 1 = m + n + 2 from by omega]
        -- Combine.
        rw [Work.Shrinking.pCentralSeries_succ, Work.Shrinking.pCentralStep,
          Subgroup.commutator_le]
        intro g hg2 x hx
        rw [Subgroup.mem_sup_of_normal_right] at hx
        obtain ⟨a, ha, b, hb, rfl⟩ := hx
        rw [commutatorElement_mul_right_eq_mul_conj]
        have h1 : ⁅g, a⁆ ∈ Work.Shrinking.pCentralSeries 2 P (m + n + 2) :=
          hP (Subgroup.commutator_mem_commutator hg2 ha)
        have h2 : ⁅g, b⁆ ∈ Work.Shrinking.pCentralSeries 2 P (m + n + 2) :=
          hQ (Subgroup.commutator_mem_commutator hg2 hb)
        haveI h2n : (Work.Shrinking.pCentralSeries 2 P (m + n + 2)).Normal :=
          Work.Shrinking.pCentralSeries_normal 2 P (m + n + 2)
        have hconj : a * ⁅g, b⁆ * a⁻¹ ∈ Work.Shrinking.pCentralSeries 2 P (m + n + 2) :=
          (inferInstance : (Work.Shrinking.pCentralSeries 2 P (m + n + 2)).Normal).conj_mem
            ⁅g, b⁆ h2 a
        simpa only [mul_assoc] using
          (Work.Shrinking.pCentralSeries 2 P (m + n + 2)).mul_mem h1 hconj
  exact main n m

end Work.SSGRoute.PowTransfer
