import Mathlib

/-!
# The plane retracts onto a (topological) arc

Let `u : ℝ → ℝ × ℝ` be continuous and injective on the compact interval `Icc a b` (`a < b`).
Then the *arc* `A = u '' Icc a b` is a retract of the plane: there is a continuous
`r : ℝ × ℝ → ℝ × ℝ` with `r (u t) = u t` for `t ∈ Icc a b` and `r x ∈ A` for every `x`.

The point of the construction is that one should **not** try to retract onto `A` by a
"nearest point" (or similar) rule — the nearest-point map of a non-convex compact set is not
continuous.  Instead, note that it suffices to extend the *parameter* function

  `A ∋ u t ↦ t ∈ ℝ`

to the whole plane.  Since `u` is injective and continuous on the compact interval, it is a
closed embedding, so `A ⊢ u` is a closed subset of the normal space `ℝ × ℝ` that is homeomorphic
to `Icc a b`; the extension of the parameter to the plane is then exactly the Tietze extension
theorem (`ContinuousMap.exists_extension`).  Composing such an extension `G` with the
parametrisation and clamping its values to `Icc a b` produces the retraction

  `r x = u (projIcc a b (G x))`.
-/

namespace Work.RPB1a.Caratheodory.Brouwer

open Set

/-- **Extending the parameter of an arc.**  If `u` is continuous and injective on `Icc a b`, then
the parameter `t` of a point `u t` of the arc can be extended to a continuous real function on the
whole plane. -/
theorem exists_continuous_param_extension (u : ℝ → ℝ × ℝ) (hu : Continuous u) {a b : ℝ}
    (_hab : a < b) (hinj : Set.InjOn u (Set.Icc a b)) :
    ∃ G : (ℝ × ℝ) → ℝ, Continuous G ∧ ∀ t ∈ Set.Icc a b, G (u t) = t := by
  have hcpt : CompactSpace ↥(Set.Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
  have := hcpt
  -- `u` restricted to the compact interval is a closed embedding of `Icc a b` in the plane.
  let e : ↥(Set.Icc a b) → ℝ × ℝ := fun t => u t
  have he_cont : Continuous e := hu.comp continuous_subtype_val
  have he_inj : Function.Injective e := by
    intro s t hst
    exact Subtype.ext (hinj s.2 t.2 hst)
  have he : Topology.IsClosedEmbedding e := he_cont.isClosedEmbedding he_inj
  -- Tietze: extend the parametrisation `Subtype.val : Icc a b → ℝ` to the plane.
  obtain ⟨G, hG⟩ := ContinuousMap.exists_extension (Y := ℝ) he
    (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(Set.Icc a b), ℝ))
  refine ⟨G, G.continuous, fun t ht => ?_⟩
  simpa using DFunLike.congr_fun hG ⟨t, ht⟩

/-- **The plane retracts onto an arc.**  For a continuous `u : ℝ → ℝ × ℝ` injective on the compact
interval `Icc a b`, the arc `u '' Icc a b` is a retract of the plane. -/
theorem exists_continuous_retraction_of_arc (u : ℝ → ℝ × ℝ) (hu : Continuous u) {a b : ℝ}
    (hab : a < b) (hinj : Set.InjOn u (Set.Icc a b)) :
    ∃ r : (ℝ × ℝ) → (ℝ × ℝ), Continuous r ∧ (∀ t ∈ Set.Icc a b, r (u t) = u t) ∧
      ∀ x, r x ∈ u '' Set.Icc a b := by
  obtain ⟨G, hG_cont, hG⟩ := exists_continuous_param_extension u hu hab hinj
  refine ⟨fun x => u (Set.projIcc a b hab.le (G x)), ?_, ?_, ?_⟩
  · -- continuity of `hu ∘ projIcc ∘ G`
    exact hu.comp (continuous_subtype_val.comp (continuous_projIcc.comp hG_cont))
  · -- points of the arc are fixed
    intro t ht
    change u (Set.projIcc a b hab.le (G (u t))) = u t
    rw [hG t ht, Set.projIcc_of_mem hab.le ht]
  · -- the retraction lands in the arc
    intro x
    exact ⟨Set.projIcc a b hab.le (G x), (Set.projIcc a b hab.le (G x)).2, rfl⟩

end Work.RPB1a.Caratheodory.Brouwer
