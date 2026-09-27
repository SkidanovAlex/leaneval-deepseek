import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.ExtGen.Basic
import Submission.Work.KT.ExtGen.Triple

/-!
# `Work.KT.ExtGen.tripleInclQ_bijective_of_subsingleton`

If `V` is trivial, the map `ballAssoc : Ball (V × (W × Z)) → Ball ((V × W) × Z)` is a
homeomorphism and the pullback it induces on function algebras is compatible with the two
subalgebras `prodAlg (V × W) Z ⊆ C(Ball ((V × W) × Z), ℂ)` and
`tripleAlg V W Z ⊆ C(Ball (V × (W × Z)), ℂ)`: their membership conditions differ only by a
`V`-direction condition, which is vacuous when `V` is a subsingleton (no unit vector).
-/

namespace Work.KT

namespace ExtGen

noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false

section Helpers

variable (V W Z : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]

/-! ## Coordinates of `ballAssocInv` -/

lemma ballAssocInv_fst (z : Ball ((V × W) × Z)) :
    ((ballAssocInv V W Z z : Ball (V × (W × Z))) : V × (W × Z)).1
      = (z : (V × W) × Z).1.1 := rfl

lemma ballAssocInv_snd_fst (z : Ball ((V × W) × Z)) :
    ((ballAssocInv V W Z z : Ball (V × (W × Z))) : V × (W × Z)).2.1
      = (z : (V × W) × Z).1.2 := rfl

lemma ballAssocInv_snd_snd (z : Ball ((V × W) × Z)) :
    ((ballAssocInv V W Z z : Ball (V × (W × Z))) : V × (W × Z)).2.2
      = (z : (V × W) × Z).2 := rfl

lemma ballAssoc_surjective : Function.Surjective (ballAssoc V W Z) :=
  fun x => ⟨ballAssocInv V W Z x, ballAssoc_ballAssocInv V W Z x⟩

/-! ## Membership in `prodAlg` -/

lemma mem_prodAlg_iff {F : C(Ball (V × W), ℂ)} :
    F ∈ prodAlg V W ↔
      (∀ z z' : Ball (V × W), ‖(z : V × W).1‖ = 1 → ‖(z' : V × W).1‖ = 1 →
        (z : V × W).2 = (z' : V × W).2 → F z = F z') ∧
      (∀ z z' : Ball (V × W), ‖(z : V × W).2‖ = 1 → ‖(z' : V × W).2‖ = 1 →
        (z : V × W).1 = (z' : V × W).1 → F z = F z') :=
  Iff.rfl

/-! ## Injectivity of `tripleInclQ` (no hypothesis on `V`) -/

/-- `tripleInclQ` is injective: pulling back along the (always surjective) homeomorphism
`ballAssoc` loses no information. -/
lemma tripleInclQ_injective : Function.Injective (tripleInclQ V W Z) := by
  intro F G h
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  obtain ⟨y, rfl⟩ := ballAssoc_surjective V W Z x
  have h1 := congrArg (fun k : tripleAlg V W Z => (k : C(Ball (V × (W × Z)), ℂ)) y) h
  rw [tripleInclQ_apply V W Z F, tripleInclQ_apply V W Z G] at h1
  exact h1

/-! ## The `tripleAlg`-elements that come from `prodAlg (V × W) Z` -/

/-- If `V` is a subsingleton, every element of `tripleAlg V W Z`, transported back along the
homeomorphism `ballAssoc`, lies in `prodAlg (V × W) Z`: the `V`-coordinate condition of
`prodAlg (V × W) Z` reduces to the `W`-coordinate condition of `tripleAlg V W Z`. -/
lemma mem_prodAlg_pullAlg_ballAssocInv (hV : Subsingleton V)
    {G : C(Ball (V × (W × Z)), ℂ)} (hG : G ∈ tripleAlg V W Z) :
    pullAlg (ballAssocInv V W Z) G ∈ prodAlg (V × W) Z := by
  rw [mem_prodAlg_iff]
  rw [mem_tripleAlg_iff] at hG
  obtain ⟨hG1, hG2, hG3⟩ := hG
  constructor
  · intro x x' h1 h2 hz
    have hw : ‖(x : (V × W) × Z).1.2‖ = 1 := by
      have hx1 : ‖(x : (V × W) × Z).1.1‖ = 0 := by
        rw [hV.elim ((x : (V × W) × Z).1.1) 0, norm_zero]
      have h := h1
      rw [Prod.norm_def, hx1, max_eq_right (norm_nonneg _)] at h
      exact h
    have hw' : ‖(x' : (V × W) × Z).1.2‖ = 1 := by
      have hx1 : ‖(x' : (V × W) × Z).1.1‖ = 0 := by
        rw [hV.elim ((x' : (V × W) × Z).1.1) 0, norm_zero]
      have h := h2
      rw [Prod.norm_def, hx1, max_eq_right (norm_nonneg _)] at h
      exact h
    have hvv : (x : (V × W) × Z).1.1 = (x' : (V × W) × Z).1.1 := hV.elim _ _
    show (pullAlg (ballAssocInv V W Z) G) x = (pullAlg (ballAssocInv V W Z) G) x'
    rw [show (pullAlg (ballAssocInv V W Z) G) x = G (ballAssocInv V W Z x) from rfl,
        show (pullAlg (ballAssocInv V W Z) G) x' = G (ballAssocInv V W Z x') from rfl]
    exact hG2 _ _ hw hw' hz hvv
  · intro x x' h1 h2 hfst
    have hvv : (x : (V × W) × Z).1.1 = (x' : (V × W) × Z).1.1 := hV.elim _ _
    have hww : (x : (V × W) × Z).1.2 = (x' : (V × W) × Z).1.2 :=
      congrArg (fun p : V × W => (p : V × W).2) hfst
    show (pullAlg (ballAssocInv V W Z) G) x = (pullAlg (ballAssocInv V W Z) G) x'
    rw [show (pullAlg (ballAssocInv V W Z) G) x = G (ballAssocInv V W Z x) from rfl,
        show (pullAlg (ballAssocInv V W Z) G) x' = G (ballAssocInv V W Z x') from rfl]
    exact hG3 _ _ h1 h2 hww hvv

/-! ## Surjectivity of `tripleInclQ` -/

/-- The preimage under `tripleInclQ` of any element of `tripleAlg V W Z` is an element of
`prodAlg (V × W) Z`; this gives surjectivity. -/
lemma tripleInclQ_surjective (hV : Subsingleton V) : Function.Surjective (tripleInclQ V W Z) := by
  intro G
  refine ⟨⟨pullAlg (ballAssocInv V W Z) (G : C(Ball (V × (W × Z)), ℂ)),
    mem_prodAlg_pullAlg_ballAssocInv V W Z hV G.2⟩, ?_⟩
  apply Subtype.ext
  apply ContinuousMap.ext
  intro y
  rw [tripleInclQ_apply]
  change (pullAlg (ballAssocInv V W Z) (G : C(Ball (V × (W × Z)), ℂ))) (ballAssoc V W Z y)
    = (G : C(Ball (V × (W × Z)), ℂ)) y
  rw [show (pullAlg (ballAssocInv V W Z) (G : C(Ball (V × (W × Z)), ℂ))) (ballAssoc V W Z y)
      = (G : C(Ball (V × (W × Z)), ℂ)) (ballAssocInv V W Z (ballAssoc V W Z y)) from rfl,
    ballAssocInv_ballAssoc]

end Helpers

/-- If `V` is trivial (so that `ballAssoc : Ball (V × (W × Z)) → Ball ((V × W) × Z)` loses no
information in the `V`-coordinate), then the comparison map
`tripleInclQ V W Z : prodAlg (V × W) Z →ₐ[ℂ] tripleAlg V W Z` from
`Submission/Work/KT/ExtGen/Triple.lean` is a bijection, hence induces an injection on `K₀`.
(`Subsingleton V` holds exactly when `V` has no unit vector, i.e. `bdry V = ∅`.) -/
theorem tripleInclQ_bijective_of_subsingleton (V W Z : Type) [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (hV : Subsingleton V) : Function.Bijective (tripleInclQ V W Z) :=
  ⟨tripleInclQ_injective V W Z, tripleInclQ_surjective V W Z hV⟩

end

end ExtGen

end Work.KT
