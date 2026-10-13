import Mathlib
import Submission.Work.WilG4a.CD.fibDerivDefs
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG4a.Cells
import Submission.Work.WilG4a.subst_mem
import Submission.Work.WilG4a.CD.graphFamParamDefs
import Submission.Work.WilG4a.CD.pullProjGraphFam

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4a.CD

open Work.WilG0

/-- The graph of the pulled-back family `(u,x) ↦ f (Ψ u) x` is `Ω`-definable with sharp bounds. `Ψ : ℝ^k → ℝ^p` is an `Ω`-definable parametrisation (its graph is the set `paramGraph Ψ ⊆ ℝ^{k+p}`, in the layout "first `k` coordinates the parameter, last `p` the value"). The construction: form in `ℝ^{k+2+p}` (layout `(u,x,y,v)`) the intersection of (i) the pullback of `paramGraph Ψ` along the coordinate map selecting `(u, v)`, and (ii) the pullback of `graphFam f` along the coordinate map selecting `(v, x, y)`; then project away the `p` coordinates `v` (`projLastIter`). Both pullbacks are substitution atoms (`Work.WilG4a.subst_mem`); all format/degree costs are constants plus one copy of the two input degrees. -/
theorem graphFam_param_mem (S : WilkiesDesign.SOMin) (hcd : WilkiesDesign.SOMin.SharpCD S)
    (p k F0 F1 : ℕ) :
    ∃ (A : ℕ) (B : MvPolynomial (Fin 2) ℕ),
      ∀ (D₀ D₁ : ℕ) (f : (Fin p → ℝ) → ℝ → ℝ) (Ψ : (Fin k → ℝ) → (Fin p → ℝ)),
        Work.WilG4a.graphFam f ∈ S.Ω F0 D₀ (p + 1 + 1) →
        Work.WilG4a.CD.paramGraph Ψ ∈ S.Ω F1 D₁ (k + p) →
        Work.WilG4a.graphFam (fun (u : Fin k → ℝ) (x : ℝ) => f (Ψ u) x) ∈
          S.Ω A (MvPolynomial.eval ![D₀, D₁] B) (k + 1 + 1) := by
  -- The sharp bounds: the format is the `max` of the two substitution-atom formats, plus one
  -- step for the intersection and `p` steps for the iterated projection; the degree is the sum
  -- of the two input degrees plus the two `+2` charges of the substitution atoms.
  refine ⟨max (F1 + 2 * (((k + 1 + 1) + p) + (k + p)) + 1)
              (F0 + 2 * (((k + 1 + 1) + p) + (p + 1 + 1)) + 1) + 1 + p,
          MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.C 4, ?_⟩
  intro D₀ D₁ f Ψ hf hΨ
  -- The pullback of `paramGraph Ψ` along `(u,x,y,v) ↦ (u,v)`.
  have hA : {z : Fin ((k + 1 + 1) + p) → ℝ | z ∘ pullIdxA k p ∈ paramGraph Ψ} ∈
      S.Ω (F1 + 2 * (((k + 1 + 1) + p) + (k + p)) + 1) (D₁ + 2) ((k + 1 + 1) + p) :=
    subst_mem S (pullIdxA k p) hΨ
  -- The pullback of `graphFam f` along `(u,x,y,v) ↦ (v,x,y)`.
  have hB : {z : Fin ((k + 1 + 1) + p) → ℝ | z ∘ pullIdxB k p ∈ graphFam f} ∈
      S.Ω (F0 + 2 * (((k + 1 + 1) + p) + (p + 1 + 1)) + 1) (D₀ + 2) ((k + 1 + 1) + p) :=
    subst_mem S (pullIdxB k p) hf
  -- Common format.
  have h1 : {z : Fin ((k + 1 + 1) + p) → ℝ | z ∘ pullIdxA k p ∈ paramGraph Ψ} ∈
      S.Ω (max (F1 + 2 * (((k + 1 + 1) + p) + (k + p)) + 1)
              (F0 + 2 * (((k + 1 + 1) + p) + (p + 1 + 1)) + 1))
          (D₁ + 2) ((k + 1 + 1) + p) :=
    Work.WilG4a.mem_mono hA (le_max_left _ _) le_rfl
  have h2 : {z : Fin ((k + 1 + 1) + p) → ℝ | z ∘ pullIdxB k p ∈ graphFam f} ∈
      S.Ω (max (F1 + 2 * (((k + 1 + 1) + p) + (k + p)) + 1)
              (F0 + 2 * (((k + 1 + 1) + p) + (p + 1 + 1)) + 1))
          (D₀ + 2) ((k + 1 + 1) + p) :=
    Work.WilG4a.mem_mono hB (le_max_right _ _) le_rfl
  -- The intersection of the two pullbacks.
  have h3 : (⋂ i : Fin 2, (if i = 0 then
        {z : Fin ((k + 1 + 1) + p) → ℝ | z ∘ pullIdxA k p ∈ paramGraph Ψ}
      else {z : Fin ((k + 1 + 1) + p) → ℝ | z ∘ pullIdxB k p ∈ graphFam f})) ∈
      S.Ω (max (F1 + 2 * (((k + 1 + 1) + p) + (k + p)) + 1)
              (F0 + 2 * (((k + 1 + 1) + p) + (p + 1 + 1)) + 1) + 1)
          ((D₁ + 2) + (D₀ + 2)) ((k + 1 + 1) + p) := by
    have h := S.inter (fun i : Fin 2 => if i = 0 then D₁ + 2 else D₀ + 2)
      (fun i : Fin 2 => if i = 0 then
          ({z : Fin ((k + 1 + 1) + p) → ℝ | z ∘ pullIdxA k p ∈ paramGraph Ψ} : Set _)
        else {z : Fin ((k + 1 + 1) + p) → ℝ | z ∘ pullIdxB k p ∈ graphFam f})
      (by intro i
          fin_cases i
          · exact h1
          · exact h2)
    simpa [Fin.sum_univ_two] using h
  -- Project the `p` coordinates `v` away.
  have h4 : projLastIter (k + 1 + 1) p
      (⋂ i : Fin 2, (if i = 0 then
        {z : Fin ((k + 1 + 1) + p) → ℝ | z ∘ pullIdxA k p ∈ paramGraph Ψ}
      else {z : Fin ((k + 1 + 1) + p) → ℝ | z ∘ pullIdxB k p ∈ graphFam f})) ∈
      S.Ω (max (F1 + 2 * (((k + 1 + 1) + p) + (k + p)) + 1)
              (F0 + 2 * (((k + 1 + 1) + p) + (p + 1 + 1)) + 1) + 1 + p)
          ((D₁ + 2) + (D₀ + 2)) (k + 1 + 1) :=
    Work.WilG4a.projLastIter_mem h3
  rw [Work.WilG4a.iInter_fin_two] at h4
  -- The projected intersection is exactly the graph of the pulled-back family.
  rw [pullProjGraphFam k p f Ψ] at h4
  refine Work.WilG4a.mem_mono h4 le_rfl ?_
  simp
  omega

end Work.WilG4a.CD
