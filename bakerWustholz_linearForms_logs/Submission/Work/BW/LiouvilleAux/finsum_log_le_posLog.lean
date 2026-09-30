import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.LiouvilleAux

open NumberField

theorem finsum_log_le_posLog {K : Type*} [Field K] [NumberField K] {x : K} (hx : x ≠ 0) :
    ∑ᶠ v : NumberField.FinitePlace K, Real.log (v x) ≤
      ∑ᶠ v : NumberField.FinitePlace K, Real.posLog (v x) := by
  have h := NumberField.FinitePlace.hasFiniteMulSupport (K := K) hx
  have hf : Function.HasFiniteSupport (fun v : NumberField.FinitePlace K => Real.log (v x)) := by
    refine h.subset ?_
    intro v hv
    simp only [Function.mem_mulSupport, Function.mem_support] at hv ⊢
    intro h1
    exact hv (by rw [h1, Real.log_one])
  have hg : Function.HasFiniteSupport (fun v : NumberField.FinitePlace K => Real.posLog (v x)) := by
    refine h.subset ?_
    intro v hv
    simp only [Function.mem_mulSupport, Function.mem_support] at hv ⊢
    intro h1
    exact hv (by simp [Real.posLog, h1])
  exact finsum_le_finsum hf hg (fun v => by simp [Real.posLog])

end Work.BW.LiouvilleAux
