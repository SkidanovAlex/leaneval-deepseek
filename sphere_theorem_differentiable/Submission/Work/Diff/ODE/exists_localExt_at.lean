import Mathlib
import Submission.Work.Diff.EXT.twoSided_of_within
import Submission.Work.Diff.EXT.covK_onFrameFamily
import Submission.Work.Diff.ODE.ChartField

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Local extension of a jointly smooth field off the slab `[a,b] × M`

`Work.Diff.ODE.exists_localExt_at`: a field `X` which is jointly smooth on the *closed* slab
`[a,b] × M` restricts, near any of its points `(t₀,x₀)`, to a jointly smooth field on an open
neighbourhood, agreeing with `X` on the slab.

Route (as agreed with the ODE area):
* in the interior `a < t₀ < b` take the neighbourhood `Ioo a b ×ˢ univ` and `G := X`;
* at an endpoint the one-sided extension is the classic "Seeley in the time variable" step, done in
  the model space by `Work.Diff.EXT.local_ext_of_within` and read back through the tangent-bundle
  trivialisation using `Work.Diff.EXT.jointField_iff_coords`.  The two endpoints are the same
  argument with the time substitution `τ = t - a` resp. `τ = b - t`; the engine
  `exists_localExt_engine` below takes the substitution as a parameter.
-/

namespace Work.Diff.ODE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## Reading a jointly smooth field in the chart at a point -/

/-- **The chart field of a field which is jointly smooth on a chart box.**  If `X` is jointly smooth
on `J ×ˢ (chartAt H x₀).source`, then its coordinate expression `chartField X x₀` is smooth on
`J ×ˢ (extChartAt I x₀).target`. -/
theorem chartField_contDiffOn_of_jointFieldOn {x₀ : M} {J : Set ℝ}
    {X : ℝ → Work.Diff.EXT.TField (I := I) (M := M)}
    (hX : Work.Diff.EXT.JointField X (J ×ˢ (chartAt H x₀).source)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (chartField X x₀) (J ×ˢ (extChartAt I x₀).target) := by
  have hW : J ×ˢ (chartAt H x₀).source ⊆ univ ×ˢ (chartAt H x₀).source :=
    fun p hp => ⟨mem_univ _, hp.2⟩
  -- the fibre coordinate of the section, in the trivialisation at `x₀`
  have hψ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, E) (⊤ : ℕ∞)
      (fun p : ℝ × M => ((trivializationAt E (TangentSpace I) x₀)
        ⟨p.2, X p.1 p.2⟩).2) (J ×ˢ (chartAt H x₀).source) :=
    ((Work.Diff.EXT.jointField_iff_coords hW X).mp hX).2
  -- rewrite it as `continuousLinearMapAt`
  have hψ' : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, E) (⊤ : ℕ∞)
      (fun p : ℝ × M =>
        ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ p.2) (X p.1 p.2))
      (J ×ˢ (chartAt H x₀).source) := by
    refine hψ.congr ?_
    intro p hp
    have hb : p.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact hp.2
    exact Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hb (X p.1 p.2)
  -- the chart inverse as a smooth map on the chart box
  have hchart : ContMDiffOn 𝓘(ℝ, ℝ × E) ((𝓘(ℝ, ℝ)).prod I) (⊤ : ℕ∞)
      (fun q : ℝ × E => (q.1, (extChartAt I x₀).symm q.2))
      (J ×ˢ (extChartAt I x₀).target) := by
    have hfst : ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) (fun q : ℝ × E => q.1)
        (J ×ˢ (extChartAt I x₀).target) :=
      (contDiffOn_fst (𝕜 := ℝ) (E := ℝ) (F := E) (s := J ×ˢ (extChartAt I x₀).target)).contMDiffOn
    have hsnd : ContMDiffOn 𝓘(ℝ, ℝ × E) I (⊤ : ℕ∞)
        (fun q : ℝ × E => (extChartAt I x₀).symm q.2) (J ×ˢ (extChartAt I x₀).target) :=
      (contMDiffOn_extChartAt_symm (I := I) x₀).comp
        ((contDiffOn_snd (𝕜 := ℝ) (E := ℝ) (F := E)
          (s := J ×ˢ (extChartAt I x₀).target)).contMDiffOn)
        (fun _ hq => hq.2)
    exact hfst.prodMk hsnd
  -- compose
  have hcomp : ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ, E) (⊤ : ℕ∞)
      ((fun p : ℝ × M =>
          ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ p.2) (X p.1 p.2)) ∘
        (fun q : ℝ × E => (q.1, (extChartAt I x₀).symm q.2)))
      (J ×ˢ (extChartAt I x₀).target) :=
    hψ'.comp hchart (fun _ hq => by
      refine ⟨hq.1, ?_⟩
      rw [← extChartAt_source I x₀]
      exact (extChartAt I x₀).map_target hq.2)
  have h2 : ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ, E) (⊤ : ℕ∞) (chartField X x₀)
      (J ×ˢ (extChartAt I x₀).target) :=
    hcomp.congr (fun q _ => rfl)
  exact h2.contDiffOn

/-! ## The chart neighbourhood of a point of the chart source -/

/-- The preimage under the extended chart of an open set of the model space, cut down to the chart
source, is open. -/
theorem isOpen_extChartAt_inter {x₀ : M} {V : Set E} (hV : IsOpen V) :
    IsOpen {y : M | y ∈ (extChartAt I x₀).source ∧ extChartAt I x₀ y ∈ V} := by
  have h := OpenPartialHomeomorph.isOpen_extend_preimage (I := I)
    (chartAt H x₀ : OpenPartialHomeomorph M H) hV
  have hset : {y : M | y ∈ (extChartAt I x₀).source ∧ extChartAt I x₀ y ∈ V}
      = (chartAt H x₀).source ∩ (chartAt H x₀).extend I ⁻¹' V := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, extChartAt,
      OpenPartialHomeomorph.extend_source]
  rwa [hset]

/-! ## Lifting a smooth chart-coordinate function to a field -/

/-- **From chart coordinates back to a field.**  A function `K` of `(t, v)` which is smooth on
`J ×ˢ V` defines, through the tangent-bundle trivialisation at `x₀`, a jointly smooth field on the
set of points of `ℝ × M` whose chart image lies in `J ×ˢ V`. -/
theorem jointField_chartLift {x₀ : M} {J : Set ℝ} {V : Set E} {K : ℝ × E → E}
    (hK : ContDiffOn ℝ (⊤ : ℕ∞) K (J ×ˢ V)) :
    Work.Diff.EXT.JointField
      (fun t y =>
        (trivializationAt E (TangentSpace I) x₀).symmL ℝ y (K (t, extChartAt I x₀ y)))
      (J ×ˢ {y : M | y ∈ (extChartAt I x₀).source ∧ extChartAt I x₀ y ∈ V}) := by
  have hW : J ×ˢ {y : M | y ∈ (extChartAt I x₀).source ∧ extChartAt I x₀ y ∈ V}
      ⊆ univ ×ˢ (chartAt H x₀).source := by
    rintro p ⟨hp1, hp2⟩
    refine ⟨mem_univ _, ?_⟩
    have h1 : p.2 ∈ (extChartAt I x₀).source := hp2.1
    rwa [extChartAt_source I x₀] at h1
  rw [Work.Diff.EXT.jointField_iff_coords hW]
  refine ⟨contMDiffOn_snd, ?_⟩
  have hΨ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ × E) (⊤ : ℕ∞)
      (fun p : ℝ × M => (p.1, extChartAt I x₀ p.2))
      (J ×ˢ {y : M | y ∈ (extChartAt I x₀).source ∧ extChartAt I x₀ y ∈ V}) := by
    refine (contMDiffOn_prod_module_iff (F₁ := ℝ) (F₂ := E) _).mpr ⟨contMDiffOn_fst, ?_⟩
    exact (contMDiffOn_extChartAt (I := I) (x := x₀)).comp contMDiffOn_snd
      (fun p hp => by rw [← extChartAt_source I x₀]; exact hp.2.1)
  have hcoord : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, E) (⊤ : ℕ∞)
      (fun p : ℝ × M => K (p.1, extChartAt I x₀ p.2))
      (J ×ˢ {y : M | y ∈ (extChartAt I x₀).source ∧ extChartAt I x₀ y ∈ V}) :=
    hK.contMDiffOn.comp hΨ (fun p hp => ⟨hp.1, hp.2.2⟩)
  refine hcoord.congr ?_
  intro p hp
  have hb : p.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet, ← extChartAt_source I x₀]
    exact hp.2.1
  rw [Trivialization.symmL_apply (R := ℝ) (e := trivializationAt E (TangentSpace I) x₀) hb]
  exact congrArg Prod.snd
    (Trivialization.apply_mk_symm (trivializationAt E (TangentSpace I) x₀) hb
      (K (p.1, extChartAt I x₀ p.2)))

/-! ## The endpoint engine -/

/-- **The one-sided extension at a point of the slab, with the time substitution as a parameter.**
`X` is jointly smooth on the closed slab `[a,b] × M`.  If `φ` maps the half slab `[0, b-a)` into
`[a,b]`, `ψ` inverts `φ` and does not increase the distance to `t₀` (the two cases below are
`φ τ = a + τ`, `ψ t = t - a`, `t₀ = a` and `φ τ = b - τ`, `ψ t = b - t`, `t₀ = b`), then `X`
extends to a jointly smooth field on a neighbourhood of `(t₀, x₀)`, agreeing with `X` on the slab. -/
theorem exists_localExt_engine {X : ℝ → Work.Diff.EXT.TField (I := I) (M := M)} {a b : ℝ}
    (hab : a < b) (hX : Work.Diff.EXT.JointField X (Set.Icc a b ×ˢ Set.univ))
    {t₀ : ℝ} (_ht₀ : t₀ ∈ Set.Icc a b) (x₀ : M)
    (φ ψ : ℝ → ℝ) (hφsm : ContDiff ℝ (⊤ : ℕ∞) φ) (hψsm : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hφmem : ∀ τ ∈ Set.Ico 0 (b - a), φ τ ∈ Set.Icc a b)
    (hφψ : ∀ τ : ℝ, φ (ψ τ) = τ)
    (hψ0 : ∀ t ∈ Set.Icc a b, 0 ≤ ψ t)
    (hψle : ∀ t : ℝ, |ψ t| ≤ |t - t₀|) [I.Boundaryless] :
    ∃ V : Set (ℝ × M), IsOpen V ∧ (t₀, x₀) ∈ V ∧
      ∃ G : ℝ → Work.Diff.EXT.TField (I := I) (M := M), Work.Diff.EXT.JointField G V ∧
        ∀ q ∈ V, q.1 ∈ Set.Icc a b → G q.1 q.2 = X q.1 q.2 := by
  have hTpos : 0 < b - a := by linarith
  -- 1. the coordinate expression of `X` is smooth on the slab
  have hcoord : ContDiffOn ℝ (⊤ : ℕ∞) (chartField X x₀) (Set.Icc a b ×ˢ (extChartAt I x₀).target) :=
    chartField_contDiffOn_of_jointFieldOn (hX.mono (fun p hp => ⟨hp.1, mem_univ _⟩))
  -- 2. substitute the time variable
  have hsub : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × E => (φ p.1, p.2)) (Set.Ico 0 (b - a) ×ˢ (extChartAt I x₀).target) := by
    refine ContDiffOn.prodMk ?_
      (contDiffOn_snd (𝕜 := ℝ) (E := ℝ) (F := E)
        (s := Set.Ico 0 (b - a) ×ˢ (extChartAt I x₀).target))
    exact ContDiffOn.comp hφsm.contDiffOn
      (contDiffOn_fst (𝕜 := ℝ) (E := ℝ) (F := E)
        (s := Set.Ico 0 (b - a) ×ˢ (extChartAt I x₀).target))
      (fun _ _ => mem_univ _)
  have hH : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × E => chartField X x₀ (φ p.1, p.2))
      (Set.Ico 0 (b - a) ×ˢ (extChartAt I x₀).target) :=
    ContDiffOn.comp hcoord hsub (fun p hp => ⟨hφmem p.1 hp.1, hp.2⟩)
  -- 3. the Seeley extension in the model space
  obtain ⟨ε, hε, V, hVo, hy₀V, hVt, K, hK, hKagr⟩ :=
    Work.Diff.EXT.local_ext_of_within hTpos (isOpen_extChartAt_target x₀)
      (fun p : ℝ × E => chartField X x₀ (φ p.1, p.2)) hH (mem_extChartAt_target x₀)
  -- 4. read the extension back as a field
  have hKsh : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × E => K (ψ p.1, p.2))
      (Set.Ioo (t₀ - ε) (t₀ + ε) ×ˢ V) := by
    have hsub2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × E => (ψ p.1, p.2))
        (Set.Ioo (t₀ - ε) (t₀ + ε) ×ˢ V) := by
      refine ContDiffOn.prodMk ?_
        (contDiffOn_snd (𝕜 := ℝ) (E := ℝ) (F := E) (s := Set.Ioo (t₀ - ε) (t₀ + ε) ×ˢ V))
      exact ContDiffOn.comp hψsm.contDiffOn
        (contDiffOn_fst (𝕜 := ℝ) (E := ℝ) (F := E) (s := Set.Ioo (t₀ - ε) (t₀ + ε) ×ˢ V))
        (fun _ _ => mem_univ _)
    refine ContDiffOn.comp hK hsub2 (fun p hp => ⟨?_, hp.2⟩)
    have hlt : |p.1 - t₀| < ε := by
      rw [abs_lt]
      exact ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩
    exact abs_lt.mp (lt_of_le_of_lt (hψle p.1) hlt)
  refine ⟨Set.Ioo (t₀ - ε) (t₀ + ε) ×ˢ
      {y : M | y ∈ (extChartAt I x₀).source ∧ extChartAt I x₀ y ∈ V},
    isOpen_Ioo.prod (isOpen_extChartAt_inter (I := I) (x₀ := x₀) hVo), ?_,
    ⟨fun t y => (trivializationAt E (TangentSpace I) x₀).symmL ℝ y
      ((fun p : ℝ × E => K (ψ p.1, p.2)) (t, extChartAt I x₀ y)), jointField_chartLift hKsh, ?_⟩⟩
  · -- the base point
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    exact ⟨mem_extChartAt_source x₀, hy₀V⟩
  · -- agreement with `X` on the slab
    intro q hq hqab
    have hεq : |q.1 - t₀| < ε := by
      rw [abs_lt]
      exact ⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩
    have hτ : ψ q.1 ∈ Set.Ico 0 ε :=
      ⟨hψ0 q.1 hqab, lt_of_le_of_lt (le_abs_self _) (lt_of_le_of_lt (hψle q.1) hεq)⟩
    have hb : q.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet, ← extChartAt_source I x₀]
      exact hq.2.1
    have hcf : chartField X x₀ (q.1, extChartAt I x₀ q.2)
        = ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ q.2) (X q.1 q.2) := by
      simp only [chartField]
      rw [(extChartAt I x₀).left_inv hq.2.1]
    have hkey : K (ψ q.1, extChartAt I x₀ q.2) = chartField X x₀ (q.1, extChartAt I x₀ q.2) := by
      rw [hKagr (ψ q.1) hτ (extChartAt I x₀ q.2) hq.2.2]
      simp only [hφψ]
    show (trivializationAt E (TangentSpace I) x₀).symmL ℝ q.2
      (K (ψ q.1, extChartAt I x₀ q.2)) = X q.1 q.2
    rw [hkey, hcf]
    exact Trivialization.symmL_continuousLinearMapAt _ hb (X q.1 q.2)

theorem exists_localExt_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    {X : ℝ → Work.Diff.EXT.TField (I := I) (M := M)} {a b : ℝ} (hab : a < b)
    (hX : Work.Diff.EXT.JointField X (Set.Icc a b ×ˢ Set.univ))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Icc a b) (x₀ : M) :
    ∃ V : Set (ℝ × M), IsOpen V ∧ (t₀, x₀) ∈ V ∧
      ∃ G : ℝ → Work.Diff.EXT.TField (I := I) (M := M), Work.Diff.EXT.JointField G V ∧
        ∀ q ∈ V, q.1 ∈ Set.Icc a b → G q.1 q.2 = X q.1 q.2 := by
  classical
  by_cases ht : t₀ ∈ Set.Ioo a b
  · -- the base point is in the interior of the slab: no extension is needed
    refine ⟨Set.Ioo a b ×ˢ Set.univ, isOpen_Ioo.prod isOpen_univ, ⟨ht, mem_univ _⟩, X, ?_, ?_⟩
    · exact hX.mono (fun p hp => ⟨⟨le_of_lt hp.1.1, le_of_lt hp.1.2⟩, mem_univ _⟩)
    · intro q _ _
      rfl
  · -- the base point is an endpoint of the slab
    have ht0 : t₀ = a ∨ t₀ = b := by
      rcases lt_or_eq_of_le ht₀.1 with h | h
      · exact Or.inr (le_antisymm ht₀.2 (not_lt.mp fun hlt => ht ⟨h, hlt⟩))
      · exact Or.inl h.symm
    rcases ht0 with h | h
    · -- `t₀ = a`: extend to the left, using the substitution `τ = t - t₀`
      refine exists_localExt_engine (I := I) (M := M) (X := X) hab hX ht₀ x₀
        (fun τ => t₀ + τ) (fun t => t - t₀)
        (contDiff_const.add contDiff_id) (contDiff_id.sub contDiff_const)
        ?_ (fun τ => by ring) ?_ (fun t => le_refl _)
      · intro τ hτ
        rw [h]
        exact ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
      · intro t ht
        rw [h]
        linarith [ht.1]
    · -- `t₀ = b`: extend to the right, using the substitution `τ = t₀ - t`
      refine exists_localExt_engine (I := I) (M := M) (X := X) hab hX ht₀ x₀
        (fun τ => t₀ - τ) (fun t => t₀ - t)
        (contDiff_const.sub contDiff_id) (contDiff_const.sub contDiff_id)
        ?_ (fun τ => by ring) ?_ (fun t => le_of_eq (abs_sub_comm t₀ t))
      · intro τ hτ
        rw [h]
        exact ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
      · intro t ht
        rw [h]
        linarith [ht.2]

end Work.Diff.ODE
