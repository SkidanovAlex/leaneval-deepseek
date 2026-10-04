import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.Lead.Gal.gardJet_holds
import Submission.Work.Diff.STE.flat.level_linear

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead

theorem pdVec_sum2_mul_le {n N : ℕ} {z : Fin n → ℝ}
    {A : Fin n → Fin n → (Fin n → ℝ) → ℂ} {G : (Fin n → ℝ) → ℂ} {CA CD : ℝ}
    (hCA : 0 ≤ CA) (hCD : 0 ≤ CD)
    (hA : ∀ c d, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (A c d))
    (hG : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) G)
    (hAj : ∀ (c d : Fin n) (m : ℕ), m ≤ N → ∀ β : Fin m → Fin n,
        ‖Work.Diff.STE.pdVec m β (A c d) z‖ ≤ CA)
    (hDj : ∀ (c d : Fin n) (m : ℕ), m ≤ N → ∀ β : Fin m → Fin n,
        ‖Work.Diff.STE.pdVec m β (Work.Diff.STE.pd c (Work.Diff.STE.pd d G)) z‖ ≤ CD) :
    ∀ (m : ℕ), m ≤ N → ∀ β : Fin m → Fin n,
      ‖Work.Diff.STE.pdVec m β
          (fun y => ∑ c, ∑ d, A c d y * Work.Diff.STE.pd c (Work.Diff.STE.pd d G) y) z‖
        ≤ (n : ℝ) ^ 2 * ((2 : ℝ) ^ N * ((n : ℝ) + 1) ^ N * ((N : ℝ) + 1)) * (CA * CD) := by
  intro m hm β
  have hA' : ∀ c d, ContDiff ℝ (⊤ : ℕ∞) (A c d) := fun c d => hA c d
  have hBsm : ∀ c d, ContDiff ℝ (⊤ : ℕ∞)
      (fun y => Work.Diff.STE.pd c (Work.Diff.STE.pd d G) y) := fun c d =>
    Work.Diff.STE.flat.contDiff_pd_top (Work.Diff.STE.flat.contDiff_pd_top hG d) c
  -- linearity of `pdVec` over the two finite sums
  have hlin := Work.Diff.STE.flat.pdVec_sum2 (n := n) (m := m) β
      (fun c d => fun y => A c d y * Work.Diff.STE.pd c (Work.Diff.STE.pd d G) y)
      (fun c d => (hA' c d).mul (hBsm c d))
  rw [hlin]
  -- triangle inequality, twice
  have hstep1 : ‖∑ c : Fin n, ∑ d : Fin n,
        Work.Diff.STE.pdVec m β (fun y => A c d y * Work.Diff.STE.pd c (Work.Diff.STE.pd d G) y) z‖
      ≤ ∑ c : Fin n, ∑ d : Fin n,
        ‖Work.Diff.STE.pdVec m β (fun y => A c d y * Work.Diff.STE.pd c (Work.Diff.STE.pd d G) y) z‖ := by
    refine (norm_sum_le _ _).trans ?_
    exact Finset.sum_le_sum (fun c _ => norm_sum_le _ _)
  refine hstep1.trans ?_
  -- the Leibniz bound for each summand
  have hstep2 : ∑ c : Fin n, ∑ d : Fin n,
        ‖Work.Diff.STE.pdVec m β (fun y => A c d y * Work.Diff.STE.pd c (Work.Diff.STE.pd d G) y) z‖
      ≤ ∑ c : Fin n, ∑ d : Fin n,
        ((2 : ℝ) ^ N * ((n : ℝ) + 1) ^ N * ((N : ℝ) + 1)) * (CA * CD) := by
    refine Finset.sum_le_sum (fun c _ => Finset.sum_le_sum (fun d _ => ?_))
    exact Work.Diff.STE.Lead.Gal.pdVec_mul_le (n := n) (N := N) (z := z) (A := CA) (B := CD)
      hCA hCD (hA' c d) (hBsm c d) (fun j hj γ => hAj c d j hj γ)
      (fun j hj γ => hDj c d j hj γ) m hm β
  have hstep3 : ∑ c : Fin n, ∑ d : Fin n,
        ((2 : ℝ) ^ N * ((n : ℝ) + 1) ^ N * ((N : ℝ) + 1)) * (CA * CD)
      = (n : ℝ) ^ 2 * ((2 : ℝ) ^ N * ((n : ℝ) + 1) ^ N * ((N : ℝ) + 1)) * (CA * CD) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    ring
  exact hstep2.trans (le_of_eq hstep3)

end Work.Diff.STE.Lead
