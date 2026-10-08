import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.center_eq_omega1_new
import Submission.Work.Higman.MSA.centralizer_eq_self
import Submission.Work.Higman.H8.Clean.Nsd
import Submission.Work.Higman.HS.c4_hs_aux
import Submission.Work.Higman.RedAux.setup
import Submission.Work.Higman.RedAux.crux_helpers
import Submission.Work.Higman.H8.fixed_coset_imp_fix_all

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option maxHeartbeats 1000000

open scoped commutatorElement

namespace Work.Higman.RedAux

variable {P : Type} [Group P] [Finite P]

/-- **`ξ ^ (|Ω₁(P)| - 1)` acts trivially on `P/A`** in the `C₄` configuration.

`P` is a Suzuki 2-group, `A ⊴ P` is `ξ`-invariant abelian and maximal among such (`hmax`) with
`Ω₁(P) ≤ A`, `⁅P,P⁆ = A`, every square of `P` in `A`, `A ^ (4) = ⊥`, `A ^ (2) = Ω₁(P)` and
`|A| = |Ω₁(P)|²`.  Then `η := ξ ^ (|Ω₁(P)| - 1)` fixes `P/A` pointwise, i.e. `η x · x⁻¹ ∈ A`. -/
theorem xi_pow_triv_quot_full (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hA : IsXiAbelNormal h A)
    (hmax : ∀ B : Subgroup P, IsXiAbelNormal h B → A ≤ B → B = A)
    (hNA : omega1 P ≤ A) (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A) (hA4 : powSub A 4 = ⊥)
    (htop : powSub A 2 = omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(omega1 P)) ^ 2) :
    ∀ x : P, (h.xi ^ (Nat.card ↥(omega1 P) - 1)) x * x⁻¹ ∈ A := by
  classical
  haveI hAn : A.Normal := hA.normal
  have hAab := hA.abelian
  have hAne : A ≠ powSub A 2 := ne_powSub_two_of_card h htop hcard
  -- `Z(P) = Ω₁(P) = A²`
  have hZ : Subgroup.center P = omega1 P := center_eq_omega1_new h
  have hA2cent : powSub A 2 ≤ Subgroup.center P := by rw [htop]; exact h.omega1_le_center
  have hAZ : ¬ A ≤ Subgroup.center P := by
    intro hle
    have h1 : A ≤ powSub A 2 := by rw [htop, ← hZ]; exact hle
    exact hAne (le_antisymm h1 (powSub_le (by norm_num)))
  have hcent : Subgroup.centralizer (A : Set P) = A :=
    MSA.centralizer_eq_self h hA hmax hNA hGs hsq hA4 htop hcard hAZ
  -- `⁅A, ⊤⁆ = A²`
  have hAP : ⁅A, (⊤ : Subgroup P)⁆ = powSub A 2 := by
    rcases H8.Clean.nsd_comm_eq_bot_or_omega1 h hA.map_eq hAab hGs htop with hb | hb
    · exact absurd hb (H8.Clean.nsd_comm_eq_bot_false h hAab hNA hGs hsq htop)
    · rw [hb, htop]
  -- (1) every `⁅x,a⁆` with `a ∈ A` lies in `A²`
  have hmem2 : ∀ x : P, ∀ a ∈ A, ⁅x, a⁆ ∈ powSub A 2 := by
    intro x a ha
    have h1 : ⁅x, a⁆ ∈ ⁅(⊤ : Subgroup P), A⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top x) ha
    have h2 : ⁅(⊤ : Subgroup P), A⁆ = powSub A 2 := by
      rw [Subgroup.commutator_comm]; exact hAP
    rwa [h2] at h1
  -- (2) `χ` is injective: an element commuting with `A` lies in `A`
  have hker : ∀ x : P, (∀ a ∈ A, ⁅x, a⁆ = 1) → x ∈ A := by
    intro x hx
    have h1 : x ∈ Subgroup.centralizer (A : Set P) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have h2 : ⁅x, a⁆ = 1 := hx a ha
      have h3 : x * a = a * x := by
        rw [commutatorElement_def] at h2
        calc x * a = x * a * x⁻¹ * a⁻¹ * (a * x) := by group
          _ = 1 * (a * x) := by rw [h2]
          _ = a * x := one_mul _
      exact h3.symm
    rwa [hcent] at h1
  -- (3) `η := ξ ^ k` fixes `Ω₁(P)` pointwise, and moves `A` only modulo `A²`
  set k : ℕ := Nat.card ↥(omega1 P) - 1 with hk
  have hηΩ : ∀ w ∈ omega1 P, (h.xi ^ k) w = w := by
    intro w hw; rw [hk]; exact HS.xi_pow_card_sub_one_fixes_omega1 h w hw
  have hηA : ∀ a ∈ A, (h.xi ^ k) a * a⁻¹ ∈ powSub A 2 := by
    intro a ha
    have h2 : ((h.xi ^ k) a) ^ 2 = a ^ 2 := by
      have h3 : ((h.xi ^ k) a) ^ 2 = (h.xi ^ k) (a ^ 2) := by
        rw [pow_two, pow_two, map_mul]
      rw [h3]
      exact hηΩ (a ^ 2) (by rw [← htop]; exact pow_mem_powSub (n := 2) ha)
    have hc : Commute ((h.xi ^ k) a) a⁻¹ :=
      hAab ((h.xi ^ k) a) (HS.mem_of_pow_map_eq hA.map_eq k ha) a⁻¹ (A.inv_mem ha)
    have hsq1 : ((h.xi ^ k) a * a⁻¹) ^ 2 = 1 := by
      rw [hc.mul_pow 2, h2]
      group
    have hΩ : (h.xi ^ k) a * a⁻¹ ∈ omega1 P := h.mem_omega1.mpr hsq1
    rwa [← htop] at hΩ
  -- (4) `χ (η x) = χ x`
  have hχ : ∀ x : P, ∀ a ∈ A, ⁅(h.xi ^ k) x, a⁆ = ⁅x, a⁆ := by
    intro x a ha
    -- `η⁻¹ a = a * z` with `z ∈ A²`
    obtain ⟨z, hz2, hz⟩ : ∃ z ∈ powSub A 2, ((h.xi ^ k).symm) a = a * z := by
      have hmemA : ((h.xi ^ k).symm) a ∈ A :=
        symm_mem_of_map_eq (h.xi ^ k : MulAut P) (map_pow_xi_eq h hA.map_eq k) ha
      have h1 := hηA (((h.xi ^ k).symm) a) hmemA
      rw [show (h.xi ^ k) (((h.xi ^ k).symm) a) = a from MulEquiv.apply_symm_apply _ _] at h1
      refine ⟨a⁻¹ * ((h.xi ^ k).symm) a, ?_, ?_⟩
      · have h2 : a⁻¹ * ((h.xi ^ k).symm) a = (a * (((h.xi ^ k).symm) a)⁻¹)⁻¹ := by
          rw [mul_inv_rev, inv_inv]
          exact hAab a⁻¹ (A.inv_mem ha) (((h.xi ^ k).symm) a) hmemA
        rw [h2]
        exact Subgroup.inv_mem _ h1
      · rw [← mul_assoc, mul_inv_cancel, one_mul]
    have hzcen : z ∈ Subgroup.center P := hA2cent hz2
    have h4 : ⁅x, ((h.xi ^ k).symm) a⁆ = ⁅x, a⁆ := by
      rw [hz, commutator_mul_central_right hzcen x a]
    have h5 : ⁅(h.xi ^ k) x, a⁆ = (h.xi ^ k) (⁅x, ((h.xi ^ k).symm) a⁆) := by
      simp only [commutatorElement_def, map_mul, map_inv, MulEquiv.apply_symm_apply]
    rw [h5, h4]
    have hmem : ⁅x, a⁆ ∈ omega1 P := by rw [← htop]; exact hmem2 x a ha
    exact hηΩ _ hmem

  -- conclude
  intro x
  refine hker _ (fun a ha => ?_)
  have hx2 : ⁅x, a⁆ ^ 2 = 1 := h.mem_omega1.mp (by rw [← htop]; exact hmem2 x a ha)
  have h3 : ⁅x⁻¹, a⁆ = ⁅x, a⁆⁻¹ := by
    have hc : ⁅x, a⁆ ∈ Subgroup.center P := hA2cent (hmem2 x a ha)
    have h1 : ⁅x⁻¹ * x, a⁆ = ⁅x, a⁆ * ⁅x⁻¹, a⁆ :=
      commutator_mul_of_central (hA2cent (hmem2 x a ha))
    rw [inv_mul_cancel] at h1
    have h2 : ⁅x, a⁆ * ⁅x⁻¹, a⁆ = 1 := by
      rw [← h1]
      simp [commutatorElement_def]
    have h2' : ⁅x⁻¹, a⁆ * ⁅x, a⁆ = 1 := by
      rw [Subgroup.mem_center_iff.mp hc ⁅x⁻¹, a⁆, h2]
    exact eq_inv_of_mul_eq_one_left h2'
  have h2 : ⁅(h.xi ^ k) x * x⁻¹, a⁆ = ⁅x⁻¹, a⁆ * ⁅(h.xi ^ k) x, a⁆ :=
    commutator_mul_of_central (hA2cent (hmem2 x⁻¹ a ha))
  rw [h2, hχ x a ha, h3, inv_mul_cancel]

end Work.Higman.RedAux
