import Mathlib
import Submission.Work.WilE9.Ift.AppendCLM

namespace Work.WilCrux

open scoped Topology

/-- The splitting map `x ↦ (x ∘ Fin.castAdd n, x ∘ Fin.natAdd m)` as a continuous linear map
(the coordinate inverse of `Fin.append`). -/
private noncomputable def appendSplitCLM (m n : ℕ) :
    (Fin (m + n) → ℝ) →L[ℝ] ((Fin m → ℝ) × (Fin n → ℝ)) :=
  ContinuousLinearMap.prod
    (ContinuousLinearMap.pi fun i : Fin m =>
      (ContinuousLinearMap.proj (R := ℝ) (Fin.castAdd n i) : (Fin (m + n) → ℝ) →L[ℝ] ℝ))
    (ContinuousLinearMap.pi fun j : Fin n =>
      (ContinuousLinearMap.proj (R := ℝ) (Fin.natAdd m j) : (Fin (m + n) → ℝ) →L[ℝ] ℝ))

private theorem appendSplitCLM_apply (m n : ℕ) (x : Fin (m + n) → ℝ) :
    appendSplitCLM m n x = (x ∘ Fin.castAdd n, x ∘ Fin.natAdd m) := by
  apply Prod.ext
  · funext i; simp [appendSplitCLM]
  · funext j; simp [appendSplitCLM]

private theorem appendCLM_appendSplitCLM (m n : ℕ) (x : Fin (m + n) → ℝ) :
    Work.WilE9.Ift.appendCLM m n (appendSplitCLM m n x) = x := by
  rw [appendSplitCLM_apply, Work.WilE9.Ift.appendCLM_apply]
  funext s
  exact Fin.addCases (fun i => by simp [Fin.append_left])
    (fun j => by simp [Fin.append_right]) s

private theorem appendSplitCLM_append (m n : ℕ) (v : Fin m → ℝ) (u : Fin n → ℝ) :
    appendSplitCLM m n (Fin.append v u) = (v, u) := by
  rw [appendSplitCLM_apply]
  apply Prod.ext <;> funext i <;> simp [Fin.append_left, Fin.append_right]

/-- **Transfer of `ContDiffAt` across the `Fin.append` splitting of coordinates.**
`join : (Fin m → ℝ) × (Fin n → ℝ) → (Fin (m+n) → ℝ)`, `join p = Fin.append p.1 p.2`, is a linear
isomorphism (its inverse is `split x = (x ∘ Fin.castAdd n, x ∘ Fin.natAdd m)`), so `f` is `C^{n'}`
at `Fin.append v u` iff `f ∘ join` is `C^{n'}` at `(v,u)`.

Useful ingredients: `Work.WilE9.Ift.appendCLM m n` with `Work.WilE9.Ift.appendCLM_apply` is the
forward continuous linear map; `Fin.appendHomeomorph` is the homeomorphism; the general transfer
`ContinuousLinearEquiv.contDiffAt_comp_iff e : ContDiffAt 𝕜 n (f ∘ e) (e.symm x) ↔ ContDiffAt 𝕜 n f x`;
and `Fin.addCases`, `Fin.append_left`, `Fin.append_right` for the coordinate case splits. -/
theorem contDiffAt_finAppend_iff {m n : ℕ} {n' : WithTop ℕ∞} (f : (Fin (m + n) → ℝ) → ℝ)
    (v : Fin m → ℝ) (u : Fin n → ℝ) :
    ContDiffAt ℝ n' f (Fin.append v u) ↔
      ContDiffAt ℝ n' (fun p : (Fin m → ℝ) × (Fin n → ℝ) => f (Fin.append p.1 p.2)) (v, u) := by
  have hJ : (fun p : (Fin m → ℝ) × (Fin n → ℝ) => f (Fin.append p.1 p.2))
      = f ∘ ⇑(Work.WilE9.Ift.appendCLM m n) := by
    funext p
    rcases p with ⟨a, b⟩
    simp
  have hJS : ((f ∘ ⇑(Work.WilE9.Ift.appendCLM m n)) ∘ ⇑(appendSplitCLM m n)) = f := by
    funext x
    simp only [Function.comp_apply]
    rw [appendCLM_appendSplitCLM]
  constructor
  · intro hf
    rw [hJ]
    exact ContDiffAt.comp (v, u) (f := ⇑(Work.WilE9.Ift.appendCLM m n)) (g := f)
      (by simpa using hf)
      ((ContinuousLinearMap.contDiff (Work.WilE9.Ift.appendCLM m n)).contDiffAt)
  · intro hf
    rw [hJ] at hf
    have hcomp : ContDiffAt ℝ n'
        ((f ∘ ⇑(Work.WilE9.Ift.appendCLM m n)) ∘ ⇑(appendSplitCLM m n))
        (Fin.append v u) :=
      ContDiffAt.comp (Fin.append v u) (f := ⇑(appendSplitCLM m n))
        (g := f ∘ ⇑(Work.WilE9.Ift.appendCLM m n))
        (by rw [appendSplitCLM_append]; exact hf)
        ((ContinuousLinearMap.contDiff (appendSplitCLM m n)).contDiffAt)
    rwa [hJS] at hcomp

end Work.WilCrux
