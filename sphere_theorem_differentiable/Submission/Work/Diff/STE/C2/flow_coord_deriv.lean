import Mathlib
import Submission.Work.Diff.STE.C2.ChartKit
import Submission.Work.Diff.STE.C2.within_slice_clairaut
import Submission.Work.Diff.STE.C2.hasDerivWithinAt_comp_curve

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.Diff.STE.C2.flow_coord_deriv`

The derivative in `s` of the (chart-`Φ 0 t x`-)coordinate Jacobian of the flow `Φ 0 s` at `x`,
written intrinsically: it is the derivative of the coordinate function of the field `Y t` at
`Φ 0 t x`, evaluated on the flow differential `mfderiv (Φ 0 t) x u`.

This is the *coordinate* form of the first variation of the flow (the raw form
`Work.Diff.STE.C2.hasDerivWithinAt_flow_mfderiv` is false: the raw identification
`TangentSpace I z ≃ E` is not the tangent-bundle trivialisation).  Proof: write the left-hand side
as the slice `fderiv` of `Ψ : ℝ × E → E`, `Ψ (s, y) = (extChartAt I (Φ 0 t x)) (Φ 0 s ((extChartAt I x).symm y))`,
and apply the one-sided Clairaut theorem `within_slice_clairaut` (`s` is confined to
`Set.Ico 0 τ`); the `s`-partial is `derivWithin (fun s ↦ Ψ (s,y)) (Set.Icc 0 τ) t`, which is the
coordinate of `Y t` at `Φ 0 t (χ.symm y)` by the chain rule `hasDerivWithinAt_comp_curve` together
with `TangentBundle.continuousLinearMapAt_trivializationAt`; the `y`-derivative is then the
manifold chain rule.

The key bookkeeping point: `Work.Diff.STE.C2.coord` (an `abbrev` for `Submission.ChartCurv.coordFun`)
is *definitionally* the tangent-bundle trivialisation expression, so we work with the latter
(`coordT`) — `coordFun`'s API is unusable here because its signature carries a `[T2Space M]` and a
Riemannian-bundle hypothesis which are not available in this context.
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.C2

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless]

/-- The trivialization expression defining `coord`. -/
noncomputable abbrev coordT (p : M) (Z : Π x : M, TangentSpace I x) : M → E :=
  fun q ↦ (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ q (Z q)

/-- `coord` is the trivialization expression. -/
lemma coord_eq_coordT (p : M) (Z : Π x : M, TangentSpace I x) :
    Work.Diff.STE.C2.coord p Z = coordT p Z := rfl

/-- `mvfderiv` read in the chart at the base point. -/
lemma mvfderiv_eq_fderiv_comp_symm {F : M → E} (x : M)
    (hF : MDifferentiableAt I 𝓘(ℝ,E) F x) :
    mvfderiv I F x = fderiv ℝ (F ∘ (extChartAt I x).symm) ((extChartAt I x) x) := by
  rw [hF.mvfderiv, ModelWithCorners.Boundaryless.range_eq_univ, fderivWithin_univ]
  congr 1

/-- The trivialization of the tangent bundle at `p` is the derivative of the chart at `p`. -/
lemma coordT_eq_mvfderiv (p : M) (Z : Π x : M, TangentSpace I x) {z : M}
    (hz : z ∈ (chartAt H p).source) :
    coordT p Z z = mvfderiv I (extChartAt I p) z (Z z) := by
  have h := TangentBundle.continuousLinearMapAt_trivializationAt (I := I) (x₀ := p) (x := z)
    (𝕜 := ℝ) hz
  exact congrArg (fun (L : TangentSpace I z →L[ℝ] E) ↦ L (Z z)) h

theorem flow_coord_deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless]
    (Φ : ℝ → ℝ → M → M) (Y : ℝ → (x : M) → TangentSpace I x) {τ : ℝ}
    (hΦ : ContMDiffOn (((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ ℝ)).prod I) I (⊤ : ℕ∞)
      (fun q : (ℝ × ℝ) × M ↦ Φ q.1.1 q.1.2 q.2) ((Set.Icc 0 τ ×ˢ Set.Icc 0 τ) ×ˢ Set.univ))
    (hYsm : ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I) I.tangent (⊤ : ℕ∞)
      (fun p : ℝ × M ↦ (⟨p.2, Y p.1 p.2⟩ : TangentBundle I M)) (Set.Icc 0 τ ×ˢ Set.univ))
    (hvel : ∀ s ∈ Set.Icc 0 τ, ∀ t ∈ Set.Icc 0 τ, ∀ x : M,
      HasMFDerivWithinAt (modelWithCornersSelf ℝ ℝ) I (fun τ' ↦ Φ s τ' x) (Set.Icc 0 τ) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Y t (Φ s t x))))
    {t : ℝ} (ht : t ∈ Set.Ico 0 τ) {x : M} (u : TangentSpace I x) :
    HasDerivWithinAt
      (fun s : ℝ ↦ fderiv ℝ
        (fun y : E ↦ (extChartAt I (Φ 0 t x)) (Φ 0 s ((extChartAt I x).symm y)))
        ((extChartAt I x) x) u)
      (mvfderiv I (Work.Diff.STE.C2.coord (Φ 0 t x) (Y t)) (Φ 0 t x)
        (mfderiv I I (fun y : M ↦ Φ 0 t y) x u))
      (Set.Ico 0 τ) t := by
  classical
  have hτ : 0 < τ := lt_of_le_of_lt ht.1 ht.2
  have h0mem : (0:ℝ) ∈ Set.Icc 0 τ := ⟨le_rfl, hτ.le⟩
  have htmem : t ∈ Set.Icc 0 τ := ⟨ht.1, ht.2.le⟩
  set p : M := Φ 0 t x
  set y₀ : E := (extChartAt I x) x with hy₀
  -- ### smoothness of the flow slice at time `t`
  have hΦslice : MDifferentiableAt I I (fun y : M ↦ Φ 0 t y) x := by
    have hmid : ContMDiffWithinAt
        (((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ ℝ)).prod I) I (⊤ : ℕ∞)
        (fun q : (ℝ × ℝ) × M ↦ Φ q.1.1 q.1.2 q.2)
        ((Set.Icc 0 τ ×ˢ Set.Icc 0 τ) ×ˢ Set.univ) (((0:ℝ), t), x) :=
      hΦ (((0:ℝ), t), x) ⟨⟨h0mem, htmem⟩, trivial⟩
    have hcon : ContMDiffWithinAt I
        (((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ ℝ)).prod I) (⊤ : ℕ∞)
        (fun y : M ↦ (((0:ℝ), t), y)) Set.univ x :=
      (contMDiffWithinAt_const (c := (((0:ℝ), t) : ℝ × ℝ))).prodMk contMDiffWithinAt_id
    have hcomp := hmid.comp x hcon (fun y _ ↦ ⟨⟨h0mem, htmem⟩, trivial⟩)
    exact (hcomp.contMDiffAt Filter.univ_mem).mdifferentiableAt (by simp)
  -- ### smoothness of the field `Y t`
  have hYt : ContMDiff I I.tangent (⊤ : ℕ∞)
      (fun q : M ↦ (⟨q, Y t q⟩ : TangentBundle I M)) := by
    intro q
    have hpt : (t, q) ∈ Set.Icc 0 τ ×ˢ (Set.univ : Set M) := ⟨htmem, trivial⟩
    have hcon : ContMDiffWithinAt I ((modelWithCornersSelf ℝ ℝ).prod I) (⊤ : ℕ∞)
        (fun r : M ↦ (t, r)) Set.univ q :=
      (contMDiffWithinAt_const (c := t)).prodMk contMDiffWithinAt_id
    have hcomp := (hYsm (t, q) hpt).comp q hcon (fun r _ ↦ hpt)
    exact (hcomp.contMDiffAt Filter.univ_mem)
  -- ### differentiability of `coord p (Y t)` at `p`
  have hA : MDifferentiableAt I 𝓘(ℝ,E) (coordT p (Y t)) p := by
    have hsmooth :=
      Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiffOn_continuousLinearMapAt_section
        (I := I) (M := M) p (W := Y t) (u := Set.univ) (hYt.contMDiffOn)
    have hpt : p ∈ (Set.univ : Set M) ∩ (chartAt H p).source :=
      ⟨trivial, mem_chart_source H p⟩
    have hnb : (Set.univ : Set M) ∩ (chartAt H p).source ∈ 𝓝 p :=
      Filter.inter_mem Filter.univ_mem
        ((chartAt H p).open_source.mem_nhds (mem_chart_source H p))
    exact ((hsmooth p hpt).contMDiffAt hnb).mdifferentiableAt (by simp)
  -- ### smoothness of `Ψ` on the strip
  set Ψ : ℝ × E → E :=
    fun q ↦ (extChartAt I p) (Φ 0 q.1 ((extChartAt I x).symm q.2)) with hΨdef
  have hy₀target : y₀ ∈ (extChartAt I x).target := by
    rw [hy₀]
    exact (extChartAt I x).map_source (mem_extChartAt_source x)
  have hsxy : (extChartAt I x).symm y₀ = x := by
    rw [hy₀]; exact PartialEquiv.left_inv _ (mem_extChartAt_source x)
  have hUp : (extChartAt I x).target ∈ 𝓝 y₀ :=
    (isOpen_extChartAt_target (I := I) x).mem_nhds hy₀target
  have hκ : ContMDiffWithinAt (𝓘(ℝ,ℝ).prod 𝓘(ℝ,E))
      ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) (⊤ : ℕ∞)
      (fun q : ℝ × E ↦ (((0:ℝ), q.1), (extChartAt I x).symm q.2))
      ((Set.Icc 0 τ) ×ˢ (extChartAt I x).target) (t, y₀) := by
    refine ContMDiffWithinAt.prodMk ?_ ?_
    · exact (contMDiffWithinAt_const (c := (0:ℝ))).prodMk contMDiffWithinAt_fst
    · exact ((contMDiffOn_extChartAt_symm (I := I) x) y₀ hy₀target).comp (t, y₀)
        contMDiffWithinAt_snd (fun z hz ↦ hz.2)
  have hκpt : (fun q : ℝ × E ↦ (((0:ℝ), q.1), (extChartAt I x).symm q.2)) (t, y₀)
      = (((0:ℝ), t), x) := by
    show (((0:ℝ), t), (extChartAt I x).symm ((extChartAt I x) x)) = (((0:ℝ), t), x)
    rw [PartialEquiv.left_inv _ (mem_extChartAt_source x)]
  have hmid : ContMDiffWithinAt ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) I (⊤ : ℕ∞)
      (fun r : (ℝ × ℝ) × M ↦ Φ r.1.1 r.1.2 r.2)
      ((Set.Icc 0 τ ×ˢ Set.Icc 0 τ) ×ˢ Set.univ)
      ((fun q : ℝ × E ↦ (((0:ℝ), q.1), (extChartAt I x).symm q.2)) (t, y₀)) := by
    rw [hκpt]
    exact hΦ (((0:ℝ), t), x) ⟨⟨h0mem, htmem⟩, trivial⟩
  have hΨsm : ContMDiffWithinAt (𝓘(ℝ,ℝ).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) (⊤ : ℕ∞)
      (fun q : ℝ × E ↦ (extChartAt I p) (Φ 0 q.1 ((extChartAt I x).symm q.2)))
      ((Set.Icc 0 τ) ×ˢ (extChartAt I x).target) (t, y₀) := by
    have hmap : Set.MapsTo (fun q : ℝ × E ↦ (((0:ℝ), q.1), (extChartAt I x).symm q.2))
        ((Set.Icc 0 τ) ×ˢ (extChartAt I x).target)
        ((Set.Icc 0 τ ×ˢ Set.Icc 0 τ) ×ˢ (Set.univ : Set M)) := by
      intro z hz
      exact ⟨⟨h0mem, hz.1⟩, trivial⟩
    have hcomp := hmid.comp (t, y₀) hκ hmap
    have hout : ContMDiffAt I 𝓘(ℝ,E) (⊤ : ℕ∞) (extChartAt I p)
        ((fun r : (ℝ × ℝ) × M ↦ Φ r.1.1 r.1.2 r.2)
          ((fun q : ℝ × E ↦ (((0:ℝ), q.1), (extChartAt I x).symm q.2)) (t, y₀))) := by
      show ContMDiffAt I 𝓘(ℝ,E) (⊤ : ℕ∞) (extChartAt I p) (Φ 0 t ((extChartAt I x).symm y₀))
      rw [hsxy]
      exact contMDiffAt_extChartAt
    exact hout.comp_contMDiffWithinAt (t, y₀) hcomp
  have hΨcd : ContDiffWithinAt ℝ 2 Ψ
      ((Set.Icc 0 τ) ×ˢ (extChartAt I x).target) (t, y₀) := by
    have h1 : ContMDiffWithinAt (modelWithCornersSelf ℝ (ℝ × E)) (modelWithCornersSelf ℝ E)
        2 (fun q : ℝ × E ↦ (extChartAt I p) (Φ 0 q.1 ((extChartAt I x).symm q.2)))
        ((Set.Icc 0 τ) ×ˢ (extChartAt I x).target) (t, y₀) := by
      rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      exact hΨsm.of_le (by simp)
    have h2 := (contMDiffWithinAt_iff_contDiffWithinAt).mp h1
    exact h2.congr (fun q _ ↦ rfl) rfl
  -- ### Clairaut
  have hcl := within_slice_clairaut (a := 0) (b := τ) (U := (extChartAt I x).target) hτ hUp
    ⟨ht.1, ht.2.le⟩ hΨcd
  -- ### the value of the `s`-partial
  have hgcont : ContinuousAt (fun y : E ↦ Φ 0 t ((extChartAt I x).symm y)) y₀ := by
    have h1 : ContinuousAt (fun z : M ↦ Φ 0 t z) ((extChartAt I x).symm y₀) := by
      rw [hsxy]; exact hΦslice.continuousAt
    exact h1.comp (continuousAt_extChartAt_symm (I := I) x)
  have hgy : (fun y : E ↦ Φ 0 t ((extChartAt I x).symm y)) y₀ = p := by
    show Φ 0 t ((extChartAt I x).symm ((extChartAt I x) x)) = p
    rw [PartialEquiv.left_inv _ (mem_extChartAt_source x)]
  have hbase : ∀ᶠ y in 𝓝 y₀, Φ 0 t ((extChartAt I x).symm y) ∈ (chartAt H p).source := by
    have hnb : (chartAt H p).source ∈ 𝓝 ((fun y : E ↦ Φ 0 t ((extChartAt I x).symm y)) y₀) := by
      rw [hgy]
      exact (chartAt H p).open_source.mem_nhds (mem_chart_source H p)
    exact hgcont.preimage_mem_nhds hnb
  have hstep : ∀ y : E, Φ 0 t ((extChartAt I x).symm y) ∈ (chartAt H p).source →
      derivWithin (fun s : ℝ ↦ Ψ (s, y)) (Set.Icc 0 τ) t
        = coordT p (Y t) (Φ 0 t ((extChartAt I x).symm y)) := by
    intro y hy
    have hψmd : MDifferentiableAt I 𝓘(ℝ,E) (extChartAt I p)
        (Φ 0 t ((extChartAt I x).symm y)) := mdifferentiableAt_extChartAt hy
    have hcurve : HasMFDerivWithinAt (modelWithCornersSelf ℝ ℝ) I
        (fun s : ℝ ↦ Φ 0 s ((extChartAt I x).symm y)) (Set.Icc 0 τ) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Y t (Φ 0 t ((extChartAt I x).symm y)))) :=
      hvel 0 h0mem t htmem ((extChartAt I x).symm y)
    have hB := hasDerivWithinAt_comp_curve (ψ := extChartAt I p) (γ := fun s : ℝ ↦ Φ 0 s ((extChartAt I x).symm y))
      (J := Set.Icc 0 τ) (v := Y t (Φ 0 t ((extChartAt I x).symm y))) hcurve hψmd
    have huniq : UniqueDiffWithinAt ℝ (Set.Icc 0 τ) t :=
      (uniqueDiffOn_Icc hτ) t ⟨ht.1, ht.2.le⟩
    rw [hB.derivWithin huniq]
    exact (coordT_eq_mvfderiv p (Y t) hy).symm
  have hEq : (fun y : E ↦ derivWithin (fun s : ℝ ↦ Ψ (s, y)) (Set.Icc 0 τ) t)
      =ᶠ[𝓝 y₀] (fun y : E ↦ coordT p (Y t) (Φ 0 t ((extChartAt I x).symm y))) := by
    filter_upwards [hbase] with y hy
    exact hstep y hy
  have hval : fderiv ℝ (fun y : E ↦ derivWithin (fun s : ℝ ↦ Ψ (s, y)) (Set.Icc 0 τ) t) y₀
      = fderiv ℝ (fun y : E ↦ coordT p (Y t) (Φ 0 t ((extChartAt I x).symm y))) y₀ :=
    hEq.fderiv_eq
  rw [hval] at hcl
  -- ### the `y`-chain rule
  have hcompA : MDifferentiableAt I 𝓘(ℝ,E)
      ((coordT p (Y t)) ∘ (fun z : M ↦ Φ 0 t z)) x := hA.comp x hΦslice
  have hfinal : fderiv ℝ (fun y : E ↦ coordT p (Y t) (Φ 0 t ((extChartAt I x).symm y))) y₀ u
      = mvfderiv I (coordT p (Y t)) p (mfderiv I I (fun z : M ↦ Φ 0 t z) x u) := by
    have h1 := mvfderiv_eq_fderiv_comp_symm (F := (coordT p (Y t)) ∘ (fun z : M ↦ Φ 0 t z))
      x hcompA
    have h2 : fderiv ℝ (fun y : E ↦ coordT p (Y t) (Φ 0 t ((extChartAt I x).symm y))) y₀
        = mvfderiv I ((coordT p (Y t)) ∘ (fun z : M ↦ Φ 0 t z)) x := h1.symm
    have h3 : mvfderiv I ((coordT p (Y t)) ∘ (fun z : M ↦ Φ 0 t z)) x u
        = mvfderiv I (coordT p (Y t)) p (mfderiv I I (fun z : M ↦ Φ 0 t z) x u) :=
      mvfderiv_comp_apply x hA hΦslice u
    exact (congrArg (fun (L : E →L[ℝ] E) ↦ L u) h2).trans h3
  -- ### assemble
  have hmono : HasDerivWithinAt (fun s : ℝ ↦ fderiv ℝ (fun y : E ↦ Ψ (s, y)) y₀)
      (fderiv ℝ (fun y : E ↦ coordT p (Y t) (Φ 0 t ((extChartAt I x).symm y))) y₀)
      (Set.Ico 0 τ) t := hcl.mono (fun s hs ↦ ⟨hs.1, hs.2.le⟩)
  have hfin : HasDerivWithinAt (fun s : ℝ ↦ fderiv ℝ (fun y : E ↦ Ψ (s, y)) y₀ u)
      (mvfderiv I (coordT p (Y t)) p (mfderiv I I (fun z : M ↦ Φ 0 t z) x u))
      (Set.Ico 0 τ) t := by
    have h1 := (ContinuousLinearMap.apply (E := E) ℝ E u).hasFDerivAt.comp_hasDerivWithinAt t hmono
    have hv : (ContinuousLinearMap.apply (E := E) ℝ E u)
        (fderiv ℝ (fun y : E ↦ coordT p (Y t) (Φ 0 t ((extChartAt I x).symm y))) y₀)
        = mvfderiv I (coordT p (Y t)) p (mfderiv I I (fun z : M ↦ Φ 0 t z) x u) := hfinal
    exact hv ▸ h1
  have hfin' : HasDerivWithinAt (fun s : ℝ ↦ fderiv ℝ (fun y : E ↦ Ψ (s, y)) y₀ u)
      (mvfderiv I (Work.Diff.STE.C2.coord p (Y t)) p
        (mfderiv I I (fun z : M ↦ Φ 0 t z) x u))
      (Set.Ico 0 τ) t := by
    rw [coord_eq_coordT]
    exact hfin
  exact hfin'

end Work.Diff.STE.C2
