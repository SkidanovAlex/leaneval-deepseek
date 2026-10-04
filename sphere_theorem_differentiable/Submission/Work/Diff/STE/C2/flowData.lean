import Mathlib
import Submission.Work.Diff.STE.C2.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.Diff.STE.C2.flowData`: the smooth flow of `-W` on `[0,τ]`, from the ODE contract

`Work.Diff.STE.C2.flowData` unpacks the frozen contract `Submission.Diff.SmoothFlowIcc` (ODE area)
at the time-dependent field `X := fun t y ↦ -W t y`: it produces a jointly smooth two-parameter flow
`Φ s t x` on `[0,τ]²` whose time derivative is `-W`, together with

* the reflexivity `Φ s s x = x` and the groupoid identity `Φ t u (Φ s t x) = Φ s u x`,
* the *global* smoothness in `x` of the one-parameter flows `x ↦ Φ 0 t x` and `x ↦ Φ t 0 x`,
* the fact that these two maps are inverse to each other.

Two ingredients are needed beyond the contract itself.

* `Work.Diff.STE.C2.jointField_neg`: joint smoothness of a tangent field is closed under fibrewise
  negation.  This is *not* the same as negating coordinates: the trivialisation
  `trivializationAt E (TangentSpace I) x` is only a fibrewise-linear *homeomorphism* on its base set,
  and the raw coercion `(X x : E)` relevant for the outside reader is chart-dependent.  The proof
  reads the field in the trivialisation at the base point of the point under consideration
  (`Bundle.contMDiffWithinAt_totalSpace`), where the coordinate of `-X` is literally the negative of
  the coordinate of `X` by linearity of the trivialisation
  (`Trivialization.apply_eq_prod_continuousLinearEquivAt`).

* the base-point slice: a map which is jointly smooth on `A ×ˢ univ` is smooth in `x` after fixing
  the base point `a ∈ A`, `A = [0,τ]²` being closed — no interiority of `a` is needed.  Indeed
  `x ↦ (a, x)` is smooth *everywhere* and maps into `A ×ˢ univ`, so `ContMDiffWithinAt.comp`
  applies with the source set `univ`.
-/

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology
open Bundle Set Filter

namespace Work.Diff.STE.C2

/-- **Joint smoothness of a tangent field is preserved by fibrewise negation.**  This is stated for
an arbitrary set `W` of base points (no chart condition is needed: one reads the field in the
trivialisation at the base point itself). -/
theorem jointField_neg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    {W : Set (ℝ × M)} (X : ℝ → (x : M) → TangentSpace I x)
    (hX : ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I) I.tangent (⊤ : ℕ∞)
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)) W) :
    ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I) I.tangent (⊤ : ℕ∞)
      (fun p : ℝ × M ↦ (⟨p.2, -X p.1 p.2⟩ : TangentBundle I M)) W := by
  intro p₀ hp₀
  have hX' := hX p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace] at hX'
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨by simpa using hX'.1, ?_⟩
  -- read both fields in the trivialisation at the base point `p₀.2`
  let e := trivializationAt E (TangentSpace I) p₀.2
  have hbase : p₀.2 ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) p₀.2
  have key : ∀ p : ℝ × M, p.2 ∈ e.baseSet →
      (e ⟨p.2, -X p.1 p.2⟩).2 = -((e ⟨p.2, X p.1 p.2⟩).2) := by
    intro p hp
    have h1 := Trivialization.apply_eq_prod_continuousLinearEquivAt ℝ e p.2 hp (-X p.1 p.2)
    have h2 := Trivialization.apply_eq_prod_continuousLinearEquivAt ℝ e p.2 hp (X p.1 p.2)
    rw [h1, h2]
    exact ContinuousLinearEquiv.map_neg _ _
  refine (hX'.2.neg).congr_of_eventuallyEq ?_ ?_
  · apply eventually_nhdsWithin_of_eventually_nhds
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hbase)]
      with p hp
    exact key p hp
  · exact key p₀ hbase

theorem flowData
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (hFlow : Submission.Diff.SmoothFlowIcc I M) {τ : ℝ} (hτ : 0 < τ)
    (W : ℝ → (x : M) → TangentSpace I x)
    (hW : ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I) I.tangent (⊤ : ℕ∞)
      (fun p : ℝ × M ↦ (⟨p.2, W p.1 p.2⟩ : TangentBundle I M)) (Set.Icc 0 τ ×ˢ Set.univ)) :
    ∃ Φ : ℝ → ℝ → M → M,
      ContMDiffOn (((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ ℝ)).prod I) I (⊤ : ℕ∞)
        (fun q : (ℝ × ℝ) × M ↦ Φ q.1.1 q.1.2 q.2) ((Set.Icc 0 τ ×ˢ Set.Icc 0 τ) ×ˢ Set.univ) ∧
      (∀ s ∈ Set.Icc 0 τ, ∀ x : M, Φ s s x = x) ∧
      (∀ s ∈ Set.Icc 0 τ, ∀ t ∈ Set.Icc 0 τ, ∀ u ∈ Set.Icc 0 τ, ∀ x : M, Φ t u (Φ s t x) = Φ s u x) ∧
      (∀ s ∈ Set.Icc 0 τ, ∀ t ∈ Set.Icc 0 τ, ∀ x : M,
        HasMFDerivWithinAt (modelWithCornersSelf ℝ ℝ) I (fun τ' ↦ Φ s τ' x) (Set.Icc 0 τ) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (-(W t (Φ s t x))))) ∧
      (∀ t ∈ Set.Icc 0 τ, ContMDiff I I (⊤ : ℕ∞) (fun x : M ↦ Φ 0 t x)) ∧
      (∀ t ∈ Set.Icc 0 τ, ContMDiff I I (⊤ : ℕ∞) (fun x : M ↦ Φ t 0 x)) ∧
      (∀ t ∈ Set.Icc 0 τ, ∀ x : M, Φ 0 t (Φ t 0 x) = x) ∧
      (∀ t ∈ Set.Icc 0 τ, ∀ x : M, Φ t 0 (Φ 0 t x) = x) := by
  -- the field `-W` is jointly smooth on the slab; apply the contract `SmoothFlowIcc` to it
  obtain ⟨Φ, hsm, hrefl, hcomp, hvel⟩ :=
    hFlow 0 τ (fun t y ↦ -W t y) hτ (jointField_neg W hW)
  have h0 : (0 : ℝ) ∈ Set.Icc 0 τ := ⟨le_rfl, hτ.le⟩
  refine ⟨Φ, hsm, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs x; exact hrefl s hs x
  · intro s hs t ht u hu x; exact hcomp s hs t ht u hu x
  · intro s hs t ht x
    simpa using hvel s hs t ht x
  · -- smoothness of `x ↦ Φ 0 t x` on all of `M`: slice the joint smoothness at `(0,t)`
    intro t ht x
    have hmem : (((0 : ℝ), t), x) ∈ ((Set.Icc 0 τ ×ˢ Set.Icc 0 τ) ×ˢ Set.univ) :=
      ⟨⟨h0, ht⟩, mem_univ x⟩
    have hg := hsm (((0 : ℝ), t), x) hmem
    have hf : ContMDiffWithinAt I (((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))).prod I) (⊤ : ℕ∞)
        (fun y : M ↦ (((0 : ℝ), t), y)) Set.univ x :=
      ContMDiffWithinAt.prodMk (contMDiffWithinAt_const (c := (((0 : ℝ), t) : ℝ × ℝ)))
        contMDiffWithinAt_id
    have hmt : MapsTo (fun y : M ↦ (((0 : ℝ), t), y)) Set.univ
        ((Set.Icc 0 τ ×ˢ Set.Icc 0 τ) ×ˢ Set.univ) :=
      fun y _ ↦ ⟨⟨h0, ht⟩, mem_univ y⟩
    exact ContMDiffWithinAt.comp (f := fun y : M ↦ (((0 : ℝ), t), y))
      (g := fun q : (ℝ × ℝ) × M ↦ Φ q.1.1 q.1.2 q.2) x hg hf hmt
  · -- smoothness of `x ↦ Φ t 0 x` on all of `M`: slice the joint smoothness at `(t,0)`
    intro t ht x
    have hmem : ((t, (0 : ℝ)), x) ∈ ((Set.Icc 0 τ ×ˢ Set.Icc 0 τ) ×ˢ Set.univ) :=
      ⟨⟨ht, h0⟩, mem_univ x⟩
    have hg := hsm ((t, (0 : ℝ)), x) hmem
    have hf : ContMDiffWithinAt I (((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))).prod I) (⊤ : ℕ∞)
        (fun y : M ↦ ((t, (0 : ℝ)), y)) Set.univ x :=
      ContMDiffWithinAt.prodMk (contMDiffWithinAt_const (c := ((t, (0 : ℝ)) : ℝ × ℝ)))
        contMDiffWithinAt_id
    have hmt : MapsTo (fun y : M ↦ ((t, (0 : ℝ)), y)) Set.univ
        ((Set.Icc 0 τ ×ˢ Set.Icc 0 τ) ×ˢ Set.univ) :=
      fun y _ ↦ ⟨⟨ht, h0⟩, mem_univ y⟩
    exact ContMDiffWithinAt.comp (f := fun y : M ↦ ((t, (0 : ℝ)), y))
      (g := fun q : (ℝ × ℝ) × M ↦ Φ q.1.1 q.1.2 q.2) x hg hf hmt
  · -- `Φ 0 t` is a left inverse of `Φ t 0`
    intro t ht x
    exact (hcomp t ht 0 h0 t ht x).trans (hrefl t ht x)
  · -- `Φ t 0` is a left inverse of `Φ 0 t`
    intro t ht x
    exact (hcomp 0 h0 t ht 0 h0 x).trans (hrefl 0 h0 x)

end Work.Diff.STE.C2
