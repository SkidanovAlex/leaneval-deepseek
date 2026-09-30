import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mrlas

/-- If `F N` is uniformly close to `f` on `s` with error at most `b N`, and `b → 0` along `p`,
then `F` tends to `f` uniformly on `s` along `p`. -/
theorem tendstoUniformlyOn_of_dist_le {ι α : Type*} [PseudoMetricSpace α]
    {F : ι → α → ℂ} {f : α → ℂ} {p : Filter ι} {s : Set α} {b : ι → ℝ}
    (hb : Filter.Tendsto b p (nhds 0))
    (hpb : ∀ N, ∀ x ∈ s, dist (f x) (F N x) ≤ b N) :
    TendstoUniformlyOn F f p s := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hb.eventually (Metric.ball_mem_nhds (0 : ℝ) hε)] with N hN
  intro x hx
  calc dist (f x) (F N x) ≤ b N := hpb N x hx
    _ ≤ |b N| := le_abs_self (b N)
    _ = dist (b N) 0 := by rw [Real.dist_eq, sub_zero]
    _ < ε := hN

end Work.BMF.mrlas
