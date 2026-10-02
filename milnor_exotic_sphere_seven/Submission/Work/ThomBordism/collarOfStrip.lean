import Mathlib
import Submission.Work.ThomBordism.RelDuality.Collar.Global
import Submission.Work.Surgery.Collar

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A collar of `M` from an open embedding of a strip `bnd M × [0,δ)`

`Submission/Work/ThomBordism/RelDuality/Collar/Global.lean` isolates the strip map

`stripMap L δ : (bnd M) × {t // 0 ≤ t ∧ t < δ} → M`,  `(y,t) ↦ fam L t y`,

of the composite family of local pushes `fam L t` of a list `L` of `PushDatum`s.  The main theorem
of this file `collarOfStrip` is the *last* step of the collar neighbourhood theorem: if for some
`δ > 0` the strip map is an open embedding, then `M` admits a collar
`∂M × [0,∞) ↪ M` in the sense of `Work.Surgery.Collar`.

The argument is a reparametrisation of the collar parameter.  The half-line `[0,∞)` is
homeomorphic to the half-open interval `[0,δ)` by the increasing homeomorphism
`t ↦ δ t/(t+1)` (with inverse `s ↦ s/(δ - s)`); this homeomorphism fixes `0`, so the composite

`∂M × [0,∞) → ∂M × [0,δ) → M`,  `(x,t) ↦ stripMap L δ (x, δ t/(t+1))`,

is an open embedding (a homeomorphism followed by an open embedding) which is the inclusion of
the boundary at `t = 0` (because `fam L 0 = id`).  Hence it is a collar of `M`.

No smoothness or compactness of `M` is used: the statement is purely topological.  Note also that
the strip map is only assumed to be an open embedding — the fact that such a `δ` exists for the
family of pushes is a separate statement (`exists_strip_isOpenEmbedding`).

## Main results

* `Work.ThomBordism.stripHomeomorph δ hδ : [0,∞) ≃ₜ [0,δ)` — the reparametrisation
  `t ↦ δ t/(t+1)`, with `stripHomeomorph_zero` recording that it fixes `0`;
* `Work.ThomBordism.collarOfStrip` — the target of this file.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped Topology Manifold
open Function Set

namespace Work.ThomBordism

noncomputable section

/-- **Reparametrising the half-line.**  The increasing homeomorphism `t ↦ δ t / (t + 1)` of the
half-line `[0,∞)` onto the half-open interval `[0,δ)`, with inverse `s ↦ s / (δ - s)`; it is the
identity at `0`. -/
def stripHomeomorph (δ : ℝ) (hδ : 0 < δ) :
    Work.Surgery.HalfLine ≃ₜ {t : ℝ // 0 ≤ t ∧ t < δ} where
  toFun t := ⟨δ * (t:ℝ) / ((t:ℝ) + 1), by
    have ht : (0:ℝ) ≤ (t:ℝ) := t.2
    have hpos : 0 < (t:ℝ) + 1 := by linarith
    refine ⟨?_, ?_⟩
    · exact div_nonneg (mul_nonneg (le_of_lt hδ) ht) (le_of_lt hpos)
    · rw [div_lt_iff₀ hpos]; nlinarith
  ⟩
  invFun s := ⟨(s:ℝ)/(δ - (s:ℝ)), by
    have hs : (s:ℝ) < δ := s.2.2
    have hs0 : 0 ≤ (s:ℝ) := s.2.1
    exact div_nonneg hs0 (by linarith)
  ⟩
  left_inv t := by
    apply Subtype.ext
    have ht : (0:ℝ) ≤ (t:ℝ) := t.2
    have h1 : (t:ℝ) + 1 ≠ 0 := by positivity
    have h2 : δ - δ * (t:ℝ) / ((t:ℝ) + 1) ≠ 0 := by
      have hpos : 0 < (t:ℝ) + 1 := by linarith
      have hlt : δ * (t:ℝ) / ((t:ℝ) + 1) < δ := by rw [div_lt_iff₀ hpos]; nlinarith
      linarith
    field_simp
    ring
  right_inv s := by
    apply Subtype.ext
    have hs : (s:ℝ) < δ := s.2.2
    have hs0 : 0 ≤ (s:ℝ) := s.2.1
    have h3 : δ - (s:ℝ) ≠ 0 := by linarith
    have h4 : (s:ℝ) / (δ - (s:ℝ)) + 1 ≠ 0 := by positivity
    field_simp
    rw [show (s:ℝ) + (δ - (s:ℝ)) = δ by ring]
    exact mul_div_cancel_left₀ (s:ℝ) hδ.ne'
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_const.mul continuous_subtype_val).div
      (continuous_subtype_val.add continuous_const) (by intro t; have := t.2; positivity)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.div (continuous_const.sub continuous_subtype_val)
      (by intro s; have := s.2.2; linarith)

/-- The reparametrisation of the half-line fixes `0`. -/
theorem stripHomeomorph_zero (δ : ℝ) (hδ : 0 < δ) :
    stripHomeomorph δ hδ ⟨0, le_refl 0⟩ = ⟨0, ⟨le_refl 0, hδ⟩⟩ := by
  apply Subtype.ext
  simp [stripHomeomorph]
  exact Or.inl (Or.inr rfl)

/-- **A uniform strip gives a collar.**  If for some `δ > 0` the strip map
`(y,t) ↦ fam L t y` is an open embedding of `bnd M × [0,δ)` into `M`, then `M` admits a collar
`∂M × [0,∞) ↪ M`: reparametrise the collar parameter by `t ↦ δ t/(t+1)`. -/
theorem collarOfStrip {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanHalfSpace 9) M]
    (L : List (Work.ThomBordism.RelDuality.PushDatum M)) {δ : ℝ} (hδ : 0 < δ)
    (h : Topology.IsOpenEmbedding (Work.ThomBordism.RelDuality.stripMap L δ)) :
    Nonempty (Work.Surgery.Collar 8 M) := by
  have hφ : stripHomeomorph δ hδ ⟨0, le_refl 0⟩ = ⟨0, ⟨le_refl 0, hδ⟩⟩ :=
    stripHomeomorph_zero δ hδ
  refine ⟨{ toFun := fun p : (𝓡∂ 9).boundary M × Work.Surgery.HalfLine =>
              Work.ThomBordism.RelDuality.stripMap L δ (p.1, stripHomeomorph δ hδ p.2)
            isOpenEmbedding := ?_
            toFun_zero := ?_ }⟩
  · -- a homeomorphism of the parameter followed by an open embedding is an open embedding
    have hinner : Topology.IsOpenEmbedding
        (fun p : (𝓡∂ 9).boundary M × Work.Surgery.HalfLine =>
          (p.1, stripHomeomorph δ hδ p.2)) :=
      (Homeomorph.prodCongr (Homeomorph.refl ((𝓡∂ 9).boundary M))
        (stripHomeomorph δ hδ)).isOpenEmbedding
    exact h.comp hinner
  · intro x
    -- at time `0` the family is the identity
    show Work.ThomBordism.RelDuality.stripMap L δ (x, stripHomeomorph δ hδ ⟨0, le_refl 0⟩) = x.1
    rw [hφ, Work.ThomBordism.RelDuality.stripMap_apply]
    exact Work.ThomBordism.RelDuality.fam_zero L x.1

end

end Work.ThomBordism
