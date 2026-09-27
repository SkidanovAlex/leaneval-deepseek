import Mathlib
import Submission.Work.KT.ExtGen.Triple

namespace Work.KT.ExtGen

/-- If `W` or `Z` is trivial (so that its sphere carries no information), then the comparison map
`tripleInclP V W Z : prodAlg V (W × Z) →ₐ[ℂ] tripleAlg V W Z` from
`Submission/Work/KT/ExtGen/Triple.lean` is a bijection, hence induces an injection on `K₀`.
(`Subsingleton W` holds exactly when `bdry W = ∅`.) -/
theorem tripleInclP_bijective_of_subsingleton (V W Z : Type) [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (h : Subsingleton W ∨ Subsingleton Z) : Function.Bijective (tripleInclP V W Z) := by
  constructor
  · -- injectivity: `tripleInclP` is the inclusion of a subalgebra
    intro F G hFG
    apply Subtype.ext
    simpa using congrArg (fun φ : tripleAlg V W Z => (φ : C(Ball (V × (W × Z)), ℂ))) hFG
  · -- surjectivity: every element of `tripleAlg` satisfies the two `prodAlg` conditions
    intro F
    obtain ⟨h1, h2, h3⟩ := (mem_tripleAlg_iff V W Z).mp F.2
    refine ⟨⟨(F : C(Ball (V × (W × Z)), ℂ)), ⟨?_, ?_⟩⟩, ?_⟩
    · -- constancy in the `V`-coordinate when `‖v‖ = 1`, at fixed `(w, z)`
      intro z z' hv hv' hwz
      exact h1 z z' hv hv' (congrArg Prod.fst hwz) (congrArg Prod.snd hwz)
    · -- constancy in the `(W × Z)`-coordinate when it lies on the boundary, at fixed `v`
      intro z z' hv hv' hval
      rcases h with hW | hZ
      · -- `W` trivial: the `‖(w,z)‖ = 1` condition is exactly `‖z‖ = 1`, and `w = w'`
        have hz : ‖(z : V × (W × Z)).2.2‖ = 1 := by
          rw [Prod.norm_def, show ‖(z : V × (W × Z)).2.1‖ = 0 from by
            rw [hW.elim ((z : V × (W × Z)).2.1) (0 : W)]; simp,
            max_eq_right (norm_nonneg _)] at hv
          exact hv
        have hz' : ‖(z' : V × (W × Z)).2.2‖ = 1 := by
          rw [Prod.norm_def, show ‖(z' : V × (W × Z)).2.1‖ = 0 from by
            rw [hW.elim ((z' : V × (W × Z)).2.1) (0 : W)]; simp,
            max_eq_right (norm_nonneg _)] at hv'
          exact hv'
        exact h3 z z' hz hz' (hW.elim _ _) hval
      · -- `Z` trivial: symmetric
        have hw : ‖(z : V × (W × Z)).2.1‖ = 1 := by
          rw [Prod.norm_def, show ‖(z : V × (W × Z)).2.2‖ = 0 from by
            rw [hZ.elim ((z : V × (W × Z)).2.2) (0 : Z)]; simp,
            max_eq_left (norm_nonneg _)] at hv
          exact hv
        have hw' : ‖(z' : V × (W × Z)).2.1‖ = 1 := by
          rw [Prod.norm_def, show ‖(z' : V × (W × Z)).2.2‖ = 0 from by
            rw [hZ.elim ((z' : V × (W × Z)).2.2) (0 : Z)]; simp,
            max_eq_left (norm_nonneg _)] at hv'
          exact hv'
        exact h2 z z' hw hw' (hZ.elim _ _) hval
    · -- the chosen preimage maps back to `F`
      rfl

end Work.KT.ExtGen
