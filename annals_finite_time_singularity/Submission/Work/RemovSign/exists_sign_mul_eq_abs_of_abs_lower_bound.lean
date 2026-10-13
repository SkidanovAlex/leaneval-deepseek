import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.RemovSign

theorem exists_sign_mul_eq_abs_of_abs_lower_bound {T b θ μ : ℝ} (hTb : T < b)
    {Q : ℝ → ℝ} (hQ : ∀ x ∈ Set.Ioo T b, DifferentiableAt ℝ Q x)
    (hθ : θ ∈ Set.Ioo T b) (hμ : 0 < μ)
    (h : ∀ t ∈ Set.Ioo θ b, μ ≤ |Q t|) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ t ∈ Set.Ioo θ b, s * Q t = |Q t| := by
  -- `Q` is continuous on the open interval `(θ, b)` (indeed on `(T, b)`).
  have hcont : ContinuousOn Q (Set.Ioo θ b) := fun x hx =>
    (hQ x ⟨lt_trans hθ.1 hx.1, hx.2⟩).continuousAt.continuousWithinAt
  -- `Q` never vanishes on `(θ, b)`, since `|Q| ≥ μ > 0` there.
  have hne : ∀ t ∈ Set.Ioo θ b, Q t ≠ 0 := by
    intro t ht h0
    have ht' := h t ht
    rw [h0, abs_zero] at ht'
    linarith
  -- Pick a base point of `(θ, b)`.
  obtain ⟨θ', hθ'⟩ := Set.nonempty_Ioo.mpr hθ.2
  -- Intermediate value theorem on the closed interval spanned by two points of `(θ, b)`.
  have hwit : ∀ x ∈ Set.Ioo θ b, ∀ y ∈ Set.Ioo θ b,
      Set.uIcc (Q x) (Q y) ⊆ Q '' Set.uIcc x y := fun x hx y hy =>
    intermediate_value_uIcc
      (hcont.mono (Set.OrdConnected.uIcc_subset Set.ordConnected_Ioo hx hy))
  -- Consequently `0` is never between `Q x` and `Q y` for `x, y ∈ (θ, b)`.
  have hzero : ∀ x ∈ Set.Ioo θ b, ∀ y ∈ Set.Ioo θ b, 0 ∈ Set.uIcc (Q x) (Q y) → False := by
    intro x hx y hy h0
    obtain ⟨z, hz, hzQ⟩ := hwit x hx y hy h0
    have hzI : z ∈ Set.Ioo θ b :=
      Set.OrdConnected.uIcc_subset Set.ordConnected_Ioo hx hy hz
    have hz' := h z hzI
    rw [hzQ, abs_zero] at hz'
    linarith
  rcases lt_or_gt_of_ne (hne θ' hθ').symm with hpos | hneg
  · -- `Q θ' > 0`: then `Q > 0` on all of `(θ, b)`, so `s = 1` works.
    refine ⟨1, Or.inl rfl, ?_⟩
    intro t ht
    have h0 : 0 ≤ Q t := by
      by_contra hlt
      push Not at hlt
      exact hzero θ' hθ' t ht
        (by rw [Set.mem_uIcc]; exact Or.inr ⟨le_of_lt hlt, le_of_lt hpos⟩)
    rw [one_mul, abs_of_nonneg h0]
  · -- `Q θ' < 0`: then `Q < 0` on all of `(θ, b)`, so `s = -1` works.
    refine ⟨-1, Or.inr rfl, ?_⟩
    intro t ht
    have h0 : Q t ≤ 0 := by
      by_contra hlt
      push Not at hlt
      exact hzero θ' hθ' t ht
        (by rw [Set.mem_uIcc]; exact Or.inl ⟨le_of_lt hneg, le_of_lt hlt⟩)
    rw [neg_one_mul, abs_of_nonpos h0]

end Work.RemovSign
