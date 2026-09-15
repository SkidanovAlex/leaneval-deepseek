import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

namespace Commons.Analysis.Complex

/-- An infinite product `∏' n, (1 + f n x)` of continuous functions, whose terms are eventually dominated by a summable majorant, is continuous on the open set.  PROOF SKETCH: use `hasProdLocallyUniformlyOn_nat_one_add` (Mathlib, `Mathlib/Analysis/Normed/Module/MultipliableUniformlyOn.lean`, needs `[LocallyCompactSpace α]`) to get `HasProdLocallyUniformlyOn (fun n x => 1 + f n x) (fun x => ∏' n, (1 + f n x)) s`, then `TendstoLocallyUniformlyOn.continuousOn` (Mathlib, `Mathlib/Topology/UniformSpace/UniformApproximation.lean`) applied to the family of finite partial products `F : Finset ℕ → α → ℂ`, `F s x = ∏ i ∈ s, (1 + f i x)`; each `F s` is `ContinuousOn` by `Finset.continuousOn_prod`/`ContinuousOn.finsetProd`.  The `∃ᶠ` condition is discharged by `Filter.Eventually.of_forall` since EVERY partial product is continuous.  Compare the Mathlib usage `differentiableOn_tprod_one_sub_pow` in `Mathlib/NumberTheory/ModularForms/DedekindEta.lean`. -/
lemma continuousOn_tprod_one_add_nat {α : Type*} [TopologicalSpace α] [LocallyCompactSpace α]
    {s : Set α} (hs : IsOpen s) {f : ℕ → α → ℂ} {u : ℕ → ℝ} (hu : Summable u)
    (h : ∀ᶠ n in Filter.atTop, ∀ x ∈ s, ‖f n x‖ ≤ u n)
    (hcts : ∀ n, ContinuousOn (f n) s) :
    ContinuousOn (fun x => ∏' n, (1 + f n x)) s := by
  have hprod := Summable.hasProdLocallyUniformlyOn_nat_one_add (R := ℂ) hs hu h hcts
  refine hprod.continuousOn ?_
  -- Every finite partial product `x ↦ ∏ i ∈ t, (1 + f i x)` is continuous on `s`.
  exact (Filter.Eventually.of_forall fun t =>
    continuousOn_finsetProd t fun i _ => hcts i |>.const_add 1).frequently

end Commons.Analysis.Complex