import Mathlib
import Submission.Work.KT.Defs

namespace Work.KT.ExtGen

/-! ## Two elementary norm facts

On the product `V × W` (sup norm) the norms of the two coordinates are bounded by the norm of the
point.  When one factor is a subsingleton its coordinate is `0`, so its norm vanishes and the sup
norm of a point is that of the other coordinate. -/

lemma norm_snd_eq_one_of_subsingleton {V W : Type} [NormedAddCommGroup V] [NormedAddCommGroup W]
    (hV : Subsingleton V) (z : V × W) (hz : ‖z‖ = 1) : ‖z.2‖ = 1 := by
  have h1 : ‖z.1‖ = 0 := by rw [@Subsingleton.elim V hV z.1 0, norm_zero]
  rw [Prod.norm_def, h1, max_eq_right (norm_nonneg _)] at hz
  exact hz

lemma norm_fst_eq_one_of_subsingleton {V W : Type} [NormedAddCommGroup V] [NormedAddCommGroup W]
    (hW : Subsingleton W) (z : V × W) (hz : ‖z‖ = 1) : ‖z.1‖ = 1 := by
  have h1 : ‖z.2‖ = 0 := by rw [@Subsingleton.elim W hW z.2 0, norm_zero]
  rw [Prod.norm_def, h1, max_eq_left (norm_nonneg _)] at hz
  exact hz

/-- If one of the two factors is trivial (so that its sphere carries no information), then the
smash inclusion `smashIncl V W : Kpair (V × W) →ₐ[ℂ] prodAlg V W` (`Submission/Work/KT/Defs.lean`)
is a bijection, hence induces an injection on `K₀`.  (`Subsingleton V` holds exactly when
`bdry V = ∅`.) -/
theorem smashIncl_bijective_of_subsingleton (V W : Type) [NormedAddCommGroup V]
    [NormedAddCommGroup W] (h : Subsingleton V ∨ Subsingleton W) :
    Function.Bijective (smashIncl V W) := by
  -- `smashIncl` is (the cod-restriction of) the inclusion `Kpair (V × W) ⊆ prodAlg V W`,
  -- so its underlying continuous map is that of its argument.
  have hcoe : ∀ g : Kpair (V × W),
      (smashIncl V W g : C(Ball (V × W), ℂ)) = (g : C(Ball (V × W), ℂ)) := fun _ => rfl
  constructor
  · -- injectivity: the underlying map is the inclusion of a subalgebra
    intro g g' hgg
    apply Subtype.ext
    rw [← hcoe g, ← hcoe g', hgg]
  · -- surjectivity: every `F ∈ prodAlg V W` is constant on `bdry (V × W)`
    intro F
    refine ⟨⟨(F : C(Ball (V × W), ℂ)), ?_⟩, ?_⟩
    · intro z hz z' hz'
      rcases h with hV | hW
      · -- `Subsingleton V`: at boundary points the `V`-coordinate vanishes, so the sup norm
        -- sees only the `W`-coordinate, which is therefore `1`
        refine F.2.2 z z' (norm_snd_eq_one_of_subsingleton hV (z : V × W) hz)
          (norm_snd_eq_one_of_subsingleton hV (z' : V × W) hz') ?_
        exact @Subsingleton.elim V hV _ _
      · refine F.2.1 z z' (norm_fst_eq_one_of_subsingleton hW (z : V × W) hz)
          (norm_fst_eq_one_of_subsingleton hW (z' : V × W) hz') ?_
        exact @Subsingleton.elim W hW _ _
    · apply Subtype.ext
      rfl

end Work.KT.ExtGen
