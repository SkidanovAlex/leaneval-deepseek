import Mathlib
import Submission.Work.Resample.defs
import Submission.Work.Resample.tensorNorm

namespace Work.Resample

/-- The one-dimensional factor of the tensor `resAop` written as a flat sum against `rA`
is the `mulVec` of the bundled matrix `HvdH.resA`. -/
lemma rA_sum_eq_mulVec (s t α : ℕ) (x : Fin s → ℂ) :
    (fun j : Fin t => ∑ k : Fin s, rA s t α (j : ℕ) (k : ℕ) * x k) =
      (HvdH.resA s t α).mulVec x := by
  funext j
  rw [Matrix.mulVec]
  apply Finset.sum_congr rfl
  intro k _
  rw [rA, unb_apply]

theorem resAopNorm (p α : ℕ) (ss ts : List ℕ) (h : HvdH.ResParams p α ss ts)
    (hM : HvdH.ResMath1DProp) (u : Fin ss.prod → ℂ) :
    ‖Work.Resample.resAop ss ts α u‖ ≤ ‖u‖ := by
  have hlen : ts.length = ss.length := by
    have h1 : ss.length = HvdH.D := h.1
    have h2 : ts.length = HvdH.D := h.2.1
    omega
  have hm : ∀ i < ss.length, ∀ x : Fin (ss.getD i 0) → ℂ,
      ‖(fun j : Fin (ts.getD i 0) =>
          ∑ k : Fin (ss.getD i 0),
            (fun i => rA (ss.getD i 0) (ts.getD i 0) α) i (j : ℕ) (k : ℕ) * x k)‖ ≤
        (fun _ : ℕ => (1 : ℝ)) i * ‖x‖ := by
    intro i hi x
    have hiD : i < HvdH.D := lt_of_lt_of_eq hi h.1
    obtain ⟨hs, hst, hlt, hcop, hrat⟩ := h.2.2.2.2.2 i hiD
    have hb := (hM (ss.getD i 0) (ts.getD i 0) α p hs hst hcop h.2.2.2.1 h.2.2.2.2.1 hrat).2.1 x
    have heq : (fun j : Fin (ts.getD i 0) =>
          ∑ k : Fin (ss.getD i 0), rA (ss.getD i 0) (ts.getD i 0) α (j : ℕ) (k : ℕ) * x k) =
        (HvdH.resA (ss.getD i 0) (ts.getD i 0) α).mulVec x :=
      rA_sum_eq_mulVec _ _ _ x
    rw [heq]
    calc ‖(HvdH.resA (ss.getD i 0) (ts.getD i 0) α).mulVec x‖ ≤ 3 / 4 * ‖x‖ := hb
      _ ≤ 1 * ‖x‖ := by nlinarith [norm_nonneg x]
  have htn := tensorNorm ss ts hlen
      (fun i => rA (ss.getD i 0) (ts.getD i 0) α) (fun _ : ℕ => (1 : ℝ)) hm u
  rw [resAop, tensorLin_apply]
  simpa using htn

end Work.Resample
