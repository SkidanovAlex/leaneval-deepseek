import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped ContDiff

namespace Work.FTS.EllipticEst

/-- The iterated Leibniz rule for the angular operator `L = D_θ = sin(2θ) ∂_θ` (here
`LopIter i f = (L^i) f = (Work.Spaces.Lop^[i]) f`): for `f`, `g` smooth at `θ`,

`L^i (f * g) θ = ∑_{a ≤ i} C(i,a) · (L^a f θ) · (L^{i-a} g θ)`.

Proof route: this is the pointwise specialisation of the already available
`Work.Spaces.Lop_iter_mul_eqOn` (in `Submission/Work/Spaces/DthIter_mul.lean`), which gives the
identity as a `Set.EqOn` on any open set where `f` and `g` are `C^∞`; `ContDiffAt ℝ ⊤ f θ`
supplies such an open neighbourhood.  (Alternatively: induction using `Work.Spaces.Lop_mul` and
`Work.Spaces.leibniz_step`.) -/
theorem Lop_iter_mul {f g : ℝ → ℝ} {i : ℕ} {θ : ℝ} (hf : ContDiffAt ℝ ⊤ f θ)
    (hg : ContDiffAt ℝ ⊤ g θ) :
    Work.FTS.EllipticEst.LopIter i (f * g) θ = ∑ a ∈ Finset.range (i + 1),
      (i.choose a : ℝ) * (Work.FTS.EllipticEst.LopIter a f θ)
        * (Work.FTS.EllipticEst.LopIter (i - a) g θ) := by
  -- `ContDiffAt ℝ ⊤ f θ` = analytic at `θ`, hence `C^∞` on an open neighbourhood of `θ`
  -- (the neighbourhood being reasonably shrunk so that both `f` and `g` qualify).
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn (le_refl (⊤ : ℕ∞ω))
    (fun h => absurd h (ne_of_gt (WithTop.coe_lt_top (⊤ : ℕ∞))))
  obtain ⟨v, hv, hgv⟩ := hg.contDiffOn (le_refl (⊤ : ℕ∞ω))
    (fun h => absurd h (ne_of_gt (WithTop.coe_lt_top (⊤ : ℕ∞))))
  obtain ⟨W, hWU, hWopen, hθW⟩ := mem_nhds_iff.mp (Filter.inter_mem hu hv)
  -- the iterated Leibniz rule on the open set `W`
  have hmain := Work.Spaces.Lop_iter_mul_eqOn f g W hWopen
    (hfu.mono (fun x hx => (hWU hx).1)) (hgv.mono (fun x hx => (hWU hx).2)) i hθW
  simp only [Work.FTS.EllipticEst.LopIter]
  rw [hmain]
  apply Finset.sum_congr rfl
  intro a ha
  ring

end Work.FTS.EllipticEst
