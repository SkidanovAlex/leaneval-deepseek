import Mathlib

namespace Work.Pert.pert2v2

/-- **Continuity of the iterated orbit map `w ↦ f^[m] (φ w)`.**

If `U` is open, `φ` is continuous on `U`, `Df` is open and `f` is differentiable (hence continuous)
on `Df`, and the first `m + 1` points `f^[i] (φ w₀)` of the orbit of `φ w₀` lie in `Df`, then the
map `w ↦ f^[m] (φ w)` is continuous at `w₀`.

The hypotheses on the orbit are exactly what the chain rule for continuity needs: `f` must be
continuous at `f^[i] (φ w₀)` for `i < m`, which holds because those points lie in the open set
`Df` on which `f` is holomorphic. -/
theorem continuousAt_iterate_phi_of_continuousOn {f φ : ℂ → ℂ} {Df U : Set ℂ} {m : ℕ} (hU : IsOpen U) (hφ : ContinuousOn φ U) (hDf : IsOpen Df) (hf : DifferentiableOn ℂ f Df) {w₀ : ℂ} (hw₀ : w₀ ∈ U) (hwalk : ∀ j : ℕ, j ≤ m → f^[j] (φ w₀) ∈ Df) : ContinuousAt (fun w : ℂ => f^[m] (φ w)) w₀ := by
  -- `φ` is continuous at `w₀`, since `U` is open and contains `w₀`.
  have hφc : ContinuousAt φ w₀ := hφ.continuousAt (hU.mem_nhds hw₀)
  -- `f` is continuous at every point of the open set `Df`.
  have hfcont : ∀ x ∈ Df, ContinuousAt f x := fun x hx =>
    hf.continuousOn.continuousAt (hDf.mem_nhds hx)
  -- Induct on `j`: the `j`-fold orbit map is continuous at `w₀` for every `j ≤ m`.
  have key : ∀ j, j ≤ m → ContinuousAt (fun w => f^[j] (φ w)) w₀ := by
    intro j
    induction j with
    | zero => intro _; simpa using hφc
    | succ j ih =>
        intro hj
        -- the `j`-fold orbit map is continuous at `w₀` (induction hypothesis, `j ≤ m` from `j+1 ≤ m`)
        have hj' : j ≤ m := Nat.le_of_succ_le hj
        have hg : ContinuousAt (fun w => f^[j] (φ w)) w₀ := ih hj'
        -- its value at `w₀` lies in `Df`, so `f` is continuous there
        have hmem : f^[j] (φ w₀) ∈ Df := hwalk j hj'
        have hcomp : ContinuousAt (fun w => f (f^[j] (φ w))) w₀ :=
          ContinuousAt.comp' (g := f) (f := fun w => f^[j] (φ w)) (x := w₀) (hfcont _ hmem) hg
        simpa [Function.iterate_succ_apply'] using hcomp
  exact key m le_rfl

end Work.Pert.pert2v2
