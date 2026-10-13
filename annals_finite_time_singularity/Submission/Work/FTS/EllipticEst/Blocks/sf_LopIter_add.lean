import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.Spaces.DthIter_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Blocks

open Filter
open scoped Topology

/-- On an open set `U` on which both `f` and `g` are smooth, the iterates of
`L = sin(2θ) ∂_θ` are additive.  This is the local/functional form of additivity, from which
the pointwise statement `sf_LopIter_add` follows by taking `U` a neighbourhood of the point. -/
lemma Lop_iterate_addOn {U : Set ℝ} (hU : IsOpen U) {f g : ℝ → ℝ}
    (hf : ∀ x ∈ U, ContDiffAt ℝ ⊤ f x) (hg : ∀ x ∈ U, ContDiffAt ℝ ⊤ g x) :
    ∀ n : ℕ, Set.EqOn (Work.Spaces.Lop^[n] (fun x => f x + g x))
      (Work.Spaces.Lop^[n] f + Work.Spaces.Lop^[n] g) U := by
  intro n
  induction n with
  | zero => intro x _; rfl
  | succ n ih =>
      intro θ hθ
      have hm : U ∈ 𝓝 θ := hU.mem_nhds hθ
      -- the two summands stay smooth at `θ`, so `deriv_add` applies
      have hdf : DifferentiableAt ℝ (Work.Spaces.Lop^[n] f) θ :=
        (Work.Spaces.Lop_iter_contDiffAt f θ (hf θ hθ) n).differentiableAt (by simp)
      have hdg : DifferentiableAt ℝ (Work.Spaces.Lop^[n] g) θ :=
        (Work.Spaces.Lop_iter_contDiffAt g θ (hg θ hθ) n).differentiableAt (by simp)
      -- the induction hypothesis gives equality of the two functions on `U`, hence at `θ`
      have heq : (Work.Spaces.Lop^[n] (fun x => f x + g x)) =ᶠ[𝓝 θ]
          (Work.Spaces.Lop^[n] f + Work.Spaces.Lop^[n] g) := ih.eventuallyEq_of_mem hm
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply']
      simp only [Work.Spaces.Lop, Pi.add_apply]
      rw [heq.deriv_eq, deriv_add hdf hdg]
      ring

/-- Additivity of the iterates of `L = sin(2θ) ∂_θ` at a point of smoothness: for `f` and `g`
`C^∞` at `θ` and every `n`, `L^n (f + g) θ = L^n f θ + L^n g θ`.

Route: induction on `n`.  Base: `rfl`.  Step: `L^{n+1} h = L (L^n h)`, and
`L (f₀ + g₀) θ = L f₀ θ + L g₀ θ` follows from `deriv_add` (`Lop` is `sin(2θ) * ·'`); the
summands `L^n f`, `L^n g` stay `C^∞` at `θ` by `Work.Spaces.Lop_iter_contDiffAt`, so
`deriv_add` applies at each step.  Put the declaration in namespace
`Work.FTS.EllipticEst.Blocks`. -/
theorem sf_LopIter_add {f g : ℝ → ℝ} {n : ℕ} {θ : ℝ} (hf : ContDiffAt ℝ ⊤ f θ)
    (hg : ContDiffAt ℝ ⊤ g θ) :
    Work.FTS.EllipticEst.LopIter n (fun θ' => f θ' + g θ') θ
      = Work.FTS.EllipticEst.LopIter n f θ + Work.FTS.EllipticEst.LopIter n g θ := by
  -- `ContDiffAt` at `⊤` gives openness: there are open neighbourhoods `t₁`, `t₂` of `θ` on
  -- which `f`, resp. `g`, is smooth at every point.
  obtain ⟨u₁, hu₁, hf₁⟩ := hf.contDiffOn le_rfl
    (fun h => absurd h.symm (ne_of_lt (WithTop.coe_lt_top (a := (⊤ : ℕ∞)))))
  obtain ⟨u₂, hu₂, hg₂⟩ := hg.contDiffOn le_rfl
    (fun h => absurd h.symm (ne_of_lt (WithTop.coe_lt_top (a := (⊤ : ℕ∞)))))
  obtain ⟨t₁, ht₁_sub, ht₁_open, hθt₁⟩ := mem_nhds_iff.mp hu₁
  obtain ⟨t₂, ht₂_sub, ht₂_open, hθt₂⟩ := mem_nhds_iff.mp hu₂
  have hft : ∀ x ∈ t₁ ∩ t₂, ContDiffAt ℝ ⊤ f x := fun x hx =>
    (ht₁_open.contDiffOn_iff.mp (hf₁.mono ht₁_sub)) hx.1
  have hgt : ∀ x ∈ t₁ ∩ t₂, ContDiffAt ℝ ⊤ g x := fun x hx =>
    (ht₂_open.contDiffOn_iff.mp (hg₂.mono ht₂_sub)) hx.2
  have h := Lop_iterate_addOn (ht₁_open.inter ht₂_open) hft hgt n ⟨hθt₁, hθt₂⟩
  simpa [Work.FTS.EllipticEst.LopIter, Pi.add_apply] using h

end Work.FTS.EllipticEst.Blocks
