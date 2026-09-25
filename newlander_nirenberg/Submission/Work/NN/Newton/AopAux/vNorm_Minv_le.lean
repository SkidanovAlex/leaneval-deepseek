import Mathlib
import Submission.Work.NN.Newton.pushforward_norms
import Submission.Work.NN.Newton.Minv_holderNorm_one_le

namespace Work.NN.Newton.AopAux

open scoped NNReal ENNReal ContDiff

theorem vNorm_Minv_le {n : ℕ} {α r δ b : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hr : 1 ≤ r) (hr4 : r ≤ 4) (hδ : 0 < δ) (hδ8 : δ ≤ 1 / 8)
    {v : Fin n → Work.NN.Core.Cn n → ℂ}
    (hv : ∀ l, ∀ m : ℕ, ContDiffOn ℝ m (v l) (Work.NN.Newton.Pd n (r * (1 - δ))))
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 16)
    (hb : ∀ l, Work.CR.Flat.holderNorm 2 α (v l) (Work.NN.Newton.Pd n (r * (1 - δ)))
      ≤ ENNReal.ofReal b) :
    ∀ w : Work.NN.Core.Cn n, ‖w‖ ≤ 1 →
      Work.NN.Newton.vNorm 1 α (fun z => Work.NN.Newton.Minv v z w)
        (Work.NN.Newton.Pd n (r * (1 - δ))) ≤ ENNReal.ofReal (1024 * (n : ℝ)) := by
  intro w hw
  have h1d : 0 < 1 - δ := by linarith
  have hRpos : 0 < r * (1 - δ) := mul_pos (by linarith) h1d
  have hR4 : r * (1 - δ) ≤ 4 := by nlinarith [hr4, hδ, hδ8]
  have hb1' : b ≤ 1 / 8 := by linarith
  have hmain := Work.NN.Newton.Minv_holderNorm_one_le (n := n) (α := α)
    hα0 hα1 hRpos hR4 hv hb0 hb1' hb
  have hbound : ∀ k : Fin n,
      Work.CR.Flat.holderNorm 1 α (fun z => (Work.NN.Newton.Minv v z w) k)
        (Work.NN.Newton.Pd n (r * (1 - δ))) ≤ ENNReal.ofReal 1024 :=
    fun k => (hmain w hw k).2
  calc Work.NN.Newton.vNorm 1 α (fun z => Work.NN.Newton.Minv v z w)
        (Work.NN.Newton.Pd n (r * (1 - δ)))
      = ∑ k : Fin n, Work.CR.Flat.holderNorm 1 α (fun z => (Work.NN.Newton.Minv v z w) k)
          (Work.NN.Newton.Pd n (r * (1 - δ))) := rfl
    _ ≤ ∑ _k : Fin n, ENNReal.ofReal 1024 := Finset.sum_le_sum (fun k _ => hbound k)
    _ = ENNReal.ofReal ((n:ℝ) * 1024) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast n, ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal (1024 * (n:ℝ)) := by rw [mul_comm]

end Work.NN.Newton.AopAux
