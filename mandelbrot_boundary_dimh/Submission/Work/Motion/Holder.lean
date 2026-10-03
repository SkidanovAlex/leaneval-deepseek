import Mathlib
import Submission.Work.Interfaces.Basic
import Submission.Work.Motion.Basic
import Submission.Work.Motion.Coding

/-!
# Hölder continuity of the coding map in the parameter
-/

namespace Work.Motion

open MandelDim
open LeanEval.Dynamics.MandelbrotBoundary
open Set Metric Filter
open scoped Topology
open Classical

noncomputable section

namespace PertData

variable {c₀ : ℂ} {N : ℕ} {τ : Fin N → ℂ → ℂ} {n : Fin N → ℕ} {p : ℂ} {r K : ℝ}
variable (D : PertData c₀ N τ n p r K)
include D

lemma ball_half_subset : ball p (r / 2) ⊆ ball p D.r₁ :=
  ball_subset_ball (le_of_lt D.hr₁)

lemma closedBall_s_subset_ball : closedBall p D.s ⊆ ball p (r / 2) := by
  intro z hz
  rw [mem_closedBall] at hz
  rw [mem_ball]
  linarith [D.hsr]

lemma closedBall_s_subset_ball' : closedBall p D.s ⊆ ball p D.r₁ :=
  (closedBall_s_subset_ball D).trans (ball_half_subset D)

/-- The `k`-fold composite along a code is holomorphic on `ball p (r/2)`. -/
lemma pComp_diffOn (c : ℂ) (hc : c ∈ ball c₀ D.ρ) (ω : ℕ → Fin N) (k : ℕ) :
    DifferentiableOn ℂ (pComp (D.τc c) ω k) (ball p (r / 2)) := by
  induction k generalizing ω with
  | zero => exact differentiableOn_id
  | succ k ih =>
    rw [pComp_succ]
    refine DifferentiableOn.comp (t := ball p D.r₁) ?_ (ih (fun j => ω (j + 1))) ?_
    · exact D.diffOn_z (ω 0) hc
    · intro x hx
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; rw [pComp_zero]; exact ball_half_subset D hx
      · have hx' : x ∈ closedBall p (r / 2) := by
          rw [mem_closedBall]; rw [mem_ball] at hx; exact le_of_lt hx
        have h2 := pComp_mem D c hc (fun j => ω (j + 1)) (k - 1) x hx'
        have h3 : k - 1 + 1 = k := by omega
        rw [h3] at h2
        exact closedBall_s_subset_ball' D h2

/-- The `k`-fold composite along a code is injective on `ball p (r/2)`. -/
lemma pComp_injOn (c : ℂ) (hc : c ∈ ball c₀ D.ρ) (ω : ℕ → Fin N) (k : ℕ) :
    InjOn (pComp (D.τc c) ω k) (ball p (r / 2)) := by
  induction k generalizing ω with
  | zero => intro x _ y _ h; simpa using h
  | succ k ih =>
    intro u hu v hv huv
    rw [pComp_succ, Function.comp_apply, Function.comp_apply] at huv
    have hmem : ∀ x ∈ ball p (r / 2), pComp (D.τc c) (fun j => ω (j + 1)) k x ∈ ball p D.r₁ := by
      intro x hx
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; rw [pComp_zero]; exact ball_half_subset D hx
      · have hx' : x ∈ closedBall p (r / 2) := by
          rw [mem_closedBall]; rw [mem_ball] at hx; exact le_of_lt hx
        have h2 := pComp_mem D c hc (fun j => ω (j + 1)) (k - 1) x hx'
        have h3 : k - 1 + 1 = k := by omega
        rw [h3] at h2
        exact closedBall_s_subset_ball' D h2
    have h1 := D.dyn c hc (ω 0) _ (hmem u hu)
    have h2 := D.dyn c hc (ω 0) _ (hmem v hv)
    have h3 : pComp (D.τc c) (fun j => ω (j + 1)) k u
        = pComp (D.τc c) (fun j => ω (j + 1)) k v := by
      rw [← h1, huv, h2]
    exact ih (fun j => ω (j + 1)) hu hv h3

/-- The `k`-step expansion of the coding map. -/
lemma coding_eq_pComp (c : ℂ) (hc : c ∈ ball c₀ D.ρ) (ω : ℕ → Fin N) (k : ℕ) :
    coding D c ω = pComp (D.τc c) ω k (coding D c (fun j => ω (j + k))) := by
  induction k generalizing ω with
  | zero => rw [pComp_zero]; rfl
  | succ k ih =>
    have ih' := ih (fun j => ω (j + 1))
    have hcode : (fun j => ω (j + k + 1)) = (fun j => ω (j + (k + 1))) := by
      funext j; rfl
    rw [hcode] at ih'
    rw [coding_step D c hc ω, ih']
    rfl

/-- The shifted code lands in the level-1 piece of the `k`-th letter. -/
lemma coding_shift_mem (c : ℂ) (hc : c ∈ ball c₀ D.ρ) (ω : ℕ → Fin N) (k : ℕ) :
    ∃ x ∈ closedBall p (r / 2), coding D c (fun j => ω (j + k)) = D.τc c (ω k) x := by
  refine ⟨coding D c (fun j => ω (j + (k + 1))), closedBall_s_subset D (coding_mem D c hc _), ?_⟩
  have h := coding_eq_pComp D c hc (fun j => ω (j + k)) 1
  have hcode : (fun j => ω (j + 1 + k)) = (fun j => ω (j + (k + 1))) := by
    funext j; congr 1; omega
  rw [pComp_succ, pComp_zero] at h
  simp only [Function.comp_apply, id_eq, Nat.zero_add] at h
  rw [hcode] at h
  exact h

/-- **Injectivity of the coding map**, given separation of the level-1 pieces. -/
lemma coding_injective {ρ ρ_s g : ℝ} (hρ : ρ ≤ D.ρ) (hρ' : ρ ≤ ρ_s) (hg : 0 < g)
    (hsep : ∀ (i j : Fin N), i ≠ j → ∀ c ∈ ball c₀ ρ_s,
      ∀ x ∈ closedBall p (r / 2), ∀ y ∈ closedBall p (r / 2), g ≤ ‖D.τc c i x - D.τc c j y‖)
    {c : ℂ} (hc : c ∈ ball c₀ ρ) : Function.Injective (coding D c) := by
  have hcD : c ∈ ball c₀ D.ρ := ball_subset_ball hρ hc
  have hcs : c ∈ ball c₀ ρ_s := ball_subset_ball hρ' hc
  intro ω ω' heq
  by_contra hne
  have hex : ∃ j, ω j ≠ ω' j := by
    by_contra h
    exact hne (funext (by simpa [not_exists] using h))
  set k := Nat.find hex with hk
  have hkdiff : ω k ≠ ω' k := Nat.find_spec hex
  have hkagree : ∀ j < k, ω j = ω' j := by
    intro j hj
    by_contra h
    exact Nat.find_min hex hj h
  have hΦ : pComp (D.τc c) ω' k = pComp (D.τc c) ω k :=
    pComp_congr k (fun j hj => (hkagree j hj).symm)
  have h1 := coding_eq_pComp D c hcD ω k
  have h2 := coding_eq_pComp D c hcD ω' k
  have hUU : coding D c (fun j => ω (j + k)) = coding D c (fun j => ω' (j + k)) := by
    rw [h1, h2, hΦ] at heq
    exact (pComp_injOn D c hcD ω k)
      (closedBall_s_subset_ball D (coding_mem D c hcD _))
      (closedBall_s_subset_ball D (coding_mem D c hcD _)) heq
  obtain ⟨x, hx, hxeq⟩ := coding_shift_mem D c hcD ω k
  obtain ⟨y, hy, hyeq⟩ := coding_shift_mem D c hcD ω' k
  have h := hsep (ω k) (ω' k) hkdiff c hcs x hx y hy
  rw [← hxeq, ← hyeq, hUU] at h
  simp only [sub_self, norm_zero] at h
  linarith

end PertData

end

end Work.Motion
