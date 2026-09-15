import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

namespace Commons.Analysis.Complex

/-- An infinite product `∏' n, (1 + f n x)` of functions holomorphic on an open set `s ⊆ ℂ`, whose terms are eventually dominated by a summable majorant, is holomorphic on `s`.  PROOF SKETCH: as in `continuousOn_tprod_one_add_nat`, get `HasProdLocallyUniformlyOn` from `hasProdLocallyUniformlyOn_nat_one_add`, then `TendstoLocallyUniformlyOn.differentiableOn` (Mathlib, `Mathlib/Analysis/Complex/LocallyUniformLimit.lean`) applied to the finite partial products `F s x = ∏ i ∈ s, (1 + f i x)`, which are `DifferentiableOn ℂ` by `Finset.differentiableOn_prod` (the `∀ᶠ` condition is immediate since every partial product is differentiable).  Compare the Mathlib usage `differentiableOn_tprod_one_sub_pow` in `Mathlib/NumberTheory/ModularForms/DedekindEta.lean`. -/
lemma differentiableOn_tprod_one_add_nat {s : Set ℂ} (hs : IsOpen s) {f : ℕ → ℂ → ℂ} {u : ℕ → ℝ}
    (hu : Summable u) (h : ∀ᶠ n in Filter.atTop, ∀ x ∈ s, ‖f n x‖ ≤ u n)
    (hd : ∀ n, DifferentiableOn ℂ (f n) s) :
    DifferentiableOn ℂ (fun x => ∏' n, (1 + f n x)) s := by
  have hcts : ∀ n, ContinuousOn (f n) s := fun n => (hd n).continuousOn
  have hprod : HasProdLocallyUniformlyOn (fun n x => 1 + f n x)
      (fun x => ∏' i, (1 + f i x)) s :=
    Summable.hasProdLocallyUniformlyOn_nat_one_add hs hu h hcts
  rw [hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at hprod
  refine hprod.differentiableOn (Filter.Eventually.of_forall fun t => ?_) hs
  exact DifferentiableOn.fun_finsetProd (fun i _ => (hd i).const_add 1)

end Commons.Analysis.Complex