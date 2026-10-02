import Mathlib
import Submission.Work.TangentClasses.DiscSplitting
import Submission.Work.Thom.ThomAPI

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# Independence of the presentation of a gluing datum

Two presentations of the *tangent bundle* of a manifold `M` -- two vector bundle cores `Z`, `Z'`
on `M` with fibre `E` whose transition functions are those of `Work.TangentClasses.tangentBundle I M`
along the index maps `c : ι → atlas H M` and `c' : ι' → atlas H M` -- are isomorphic as vector
bundles (`Work.Agree.presentation_independence`).

The isomorphism is the *identity* on the underlying fibres: the fibre of either core at a point `x`
is the same type `E`, and `Z` and `Z'` are both presentations of the same geometric bundle.  Its
continuity is exactly the content of the hypothesis `hcont`, which says that in every pair of
charts `(i, i')` the trivialised transition

`x ↦ Z'.coordChange (Z'.indexAt x) i' x ∘ Z.coordChange i (Z.indexAt x) x`

is continuous on the overlap `Z.baseSet i ∩ Z'.baseSet i'`, i.e. that the two presentations glue
consistently.  The continuity of the *inverse* (which is the *same* function of the total spaces)
uses the fact that the inverse of a continuous family of invertible continuous linear maps is
continuous (`Work.Agree.continuousOn_inv_of_comp_eq_one`), which holds for arbitrary normed spaces
over a nontrivially normed field, without any completeness hypothesis.

## Contents

* `Work.Agree.continuousOn_inv_of_comp_eq_one` -- continuity of the pointwise inverse;
* `Work.Agree.continuous_totalSpaceMap_clm'` -- a universe-polymorphic version of
  `Work.Thom.continuous_totalSpaceMap_clm` of `Submission/Work/Thom/coreMorphism.lean` (whose base
  spaces are pinned to `Type`), needed because the base manifold here is universe-polymorphic;
* `Work.Agree.presentation_independence` -- the main statement.
-/

namespace Work.Agree

open Filter
open scoped Topology

noncomputable section

/-- **Continuity of the pointwise inverse of a continuous family of invertible continuous linear
maps.**  If `A : α → E →L[𝕜] E` is continuous along `s` and `B : α → E →L[𝕜] E` is a pointwise
two-sided inverse of `A` on `s`, then `B` is continuous along `s`.

Nothing is assumed about `E` beyond being a normed space over `𝕜` (in particular `E` need not be
complete): the estimate used is `‖B x - B x₀‖ ≤ 2‖B x₀‖ ‖1 - (A x) ∘ B x₀‖`, which is proved by
elementary algebra. -/
theorem continuousOn_inv_of_comp_eq_one {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {α : Type*} [TopologicalSpace α] {s : Set α} {A B : α → E →L[𝕜] E}
    (hA : ContinuousOn A s)
    (hBA : ∀ x ∈ s, ∀ v : E, (B x) ((A x) v) = v)
    (hAB : ∀ x ∈ s, ∀ v : E, (A x) ((B x) v) = v) :
    ContinuousOn B s := by
  intro x₀ hx₀
  show Filter.Tendsto B (𝓝[s] x₀) (𝓝 (B x₀))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set D : α → E →L[𝕜] E := fun x => (1 : E →L[𝕜] E) - (A x).comp (B x₀) with hDdef
  have hD0 : D x₀ = 0 := by
    have hDx : D x₀ = (1 : E →L[𝕜] E) - (A x₀).comp (B x₀) := rfl
    rw [hDx]
    ext v
    simp only [ContinuousLinearMap.comp_apply, sub_apply, zero_apply]
    rw [hAB x₀ hx₀ v]
    simp
  have hDtend : Tendsto D (𝓝[s] x₀) (𝓝 0) := by
    have hcont : ContinuousWithinAt D s x₀ := by
      rw [hDdef]
      exact continuousWithinAt_const.sub
        ((hA.continuousWithinAt hx₀).clm_comp continuousWithinAt_const)
    have h2 : Tendsto D (𝓝[s] x₀) (𝓝 (D x₀)) := hcont
    rwa [hD0] at h2
  have hvd : Tendsto (fun x => ‖D x‖) (𝓝[s] x₀) (𝓝 0) := by
    simpa using hDtend.norm
  have hv : Tendsto (fun x => 2 * ‖B x₀‖ * ‖D x‖) (𝓝[s] x₀) (𝓝 0) := by
    simpa using hvd.const_mul (2 * ‖B x₀‖)
  have hev : ∀ᶠ x in 𝓝[s] x₀, ‖B x - B x₀‖ ≤ 2 * ‖B x₀‖ * ‖D x‖ := by
    have hmem : ∀ᶠ x in 𝓝[s] x₀, ‖D x‖ < 1/2 :=
      hvd.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1/2))
    have hs : ∀ᶠ x in 𝓝[s] x₀, x ∈ s := self_mem_nhdsWithin
    refine (hmem.and hs).mono ?_
    rintro x ⟨hx, hxs⟩
    have hDx : D x = (1 : E →L[𝕜] E) - (A x).comp (B x₀) := rfl
    have hkey : B x - B x₀ = (B x).comp (D x) := by
      rw [hDx]
      ext v
      simp only [ContinuousLinearMap.comp_apply, sub_apply]
      rw [map_sub, hBA x hxs]
      simp
    have hle1 : ‖B x‖ ≤ ‖B x₀‖ + ‖B x‖ * ‖D x‖ := by
      calc ‖B x‖ = ‖B x₀ + (B x - B x₀)‖ := by rw [add_sub_cancel]
        _ ≤ ‖B x₀‖ + ‖B x - B x₀‖ := norm_add_le _ _
        _ = ‖B x₀‖ + ‖(B x).comp (D x)‖ := by rw [hkey]
        _ ≤ ‖B x₀‖ + ‖B x‖ * ‖D x‖ := by
              rw [add_le_add_iff_left]; exact ContinuousLinearMap.opNorm_comp_le _ _
    have hle2 : ‖B x‖ ≤ 2 * ‖B x₀‖ := by
      nlinarith [hle1, hx, norm_nonneg (B x), norm_nonneg (B x₀), norm_nonneg (D x)]
    calc ‖B x - B x₀‖ = ‖(B x).comp (D x)‖ := by rw [hkey]
      _ ≤ ‖B x‖ * ‖D x‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 2 * ‖B x₀‖ * ‖D x‖ := by nlinarith [hle2, norm_nonneg (D x)]
  exact squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) hev hv

/-- **Universe-polymorphic form of `Work.Thom.continuous_totalSpaceMap_clm`.**  The latter is
stated for base spaces in `Type`, while the base manifold of `presentation_independence` is
universe-polymorphic.  The proof is the same as that of `Work.Thom.continuous_totalSpaceMap_clm`,
whose total-space topology is generated by the local trivialisations. -/
private theorem continuous_totalSpaceMap_clm' {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {B B' : Type*} [TopologicalSpace B] [TopologicalSpace B'] {F F' : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
    {ι ι' : Type*} (Z₁ : VectorBundleCore 𝕜 B' F ι) (Z₂ : VectorBundleCore 𝕜 B F' ι')
    (f : C(B', B)) (T : B' → F →L[𝕜] F')
    (hT : ∀ (i₁ : ι) (i₂ : ι'), ContinuousOn (fun b : B' =>
        (Z₂.coordChange (Z₂.indexAt (f b)) i₂ (f b)).comp
          ((T b).comp (Z₁.coordChange i₁ (Z₁.indexAt b) b)))
        (Z₁.baseSet i₁ ∩ f ⁻¹' Z₂.baseSet i₂)) :
    Continuous (fun p : Z₁.TotalSpace => (⟨f p.1, T p.1 p.2⟩ : Z₂.TotalSpace)) := by
  have hgOn : ∀ (i₁ : ι) (i₂ : ι'),
      ContinuousOn (fun p : Z₁.TotalSpace => (⟨f p.1, T p.1 p.2⟩ : Z₂.TotalSpace))
        ((Z₁.localTriv i₁).source ∩ Z₁.proj ⁻¹' (f ⁻¹' Z₂.baseSet i₂)) := by
    intro i₁ i₂
    -- the trivialised expression on the source chart
    have hcont : ContinuousOn (fun p : Z₁.TotalSpace =>
        (⟨f p.1, (Z₂.coordChange (Z₂.indexAt (f p.1)) i₂ (f p.1)) (T p.1 p.2)⟩ : B × F'))
        ((Z₁.localTriv i₁).source ∩ Z₁.proj ⁻¹' (f ⁻¹' Z₂.baseSet i₂)) := by
      have hrw : ∀ p ∈ (Z₁.localTriv i₁).source ∩ Z₁.proj ⁻¹' (f ⁻¹' Z₂.baseSet i₂),
          (⟨f p.1, (Z₂.coordChange (Z₂.indexAt (f p.1)) i₂ (f p.1)) (T p.1 p.2)⟩ : B × F')
            = (⟨f p.1, ((Z₂.coordChange (Z₂.indexAt (f p.1)) i₂ (f p.1)).comp
                ((T p.1).comp (Z₁.coordChange i₁ (Z₁.indexAt p.1) p.1)))
                ((Z₁.localTriv i₁) p).2⟩ : B × F') := by
        intro p hp
        congr 1
        have hinner : ((Z₁.localTriv i₁) p).2 = Z₁.coordChange (Z₁.indexAt p.1) i₁ p.1 p.2 := by
          rw [VectorBundleCore.localTriv_apply]
        have hcomp' : (Z₁.coordChange i₁ (Z₁.indexAt p.1) p.1)
            ((Z₁.coordChange (Z₁.indexAt p.1) i₁ p.1) p.2) = p.2 := by
          have hx : p.1 ∈ Z₁.baseSet (Z₁.indexAt p.1) ∩ Z₁.baseSet i₁ :=
            ⟨Z₁.mem_baseSet_at p.1, (VectorBundleCore.mem_localTriv_source Z₁ i₁ p).mp hp.1⟩
          have h := Z₁.coordChange_comp (Z₁.indexAt p.1) i₁ (Z₁.indexAt p.1) p.1
            ⟨hx, Z₁.mem_baseSet_at p.1⟩ p.2
          rwa [Z₁.coordChange_self (Z₁.indexAt p.1) p.1 (Z₁.mem_baseSet_at p.1) p.2] at h
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hinner]
        exact congrArg (fun w => (Z₂.coordChange (Z₂.indexAt (f p.1)) i₂ (f p.1)) (T p.1 w))
          hcomp'.symm
      refine ContinuousOn.congr ?_ hrw
      have h1 : ContinuousOn (fun p : Z₁.TotalSpace => f p.1)
          ((Z₁.localTriv i₁).source ∩ Z₁.proj ⁻¹' (f ⁻¹' Z₂.baseSet i₂)) :=
        f.continuous.comp_continuousOn
          ((FiberBundle.continuous_proj F Z₁.Fiber).continuousOn)
      have hclm : ContinuousOn (fun p : Z₁.TotalSpace =>
          (Z₂.coordChange (Z₂.indexAt (f p.1)) i₂ (f p.1)).comp
            ((T p.1).comp (Z₁.coordChange i₁ (Z₁.indexAt p.1) p.1)))
          ((Z₁.localTriv i₁).source ∩ Z₁.proj ⁻¹' (f ⁻¹' Z₂.baseSet i₂)) := by
        have hb : Set.MapsTo (fun p : Z₁.TotalSpace => p.1)
            ((Z₁.localTriv i₁).source ∩ Z₁.proj ⁻¹' (f ⁻¹' Z₂.baseSet i₂))
            (Z₁.baseSet i₁ ∩ f ⁻¹' Z₂.baseSet i₂) := fun p hp =>
          ⟨(VectorBundleCore.mem_localTriv_source Z₁ i₁ p).mp hp.1, hp.2⟩
        exact ContinuousOn.comp (hT i₁ i₂)
          (FiberBundle.continuous_proj F Z₁.Fiber).continuousOn hb
      have hsnd : ContinuousOn (fun p : Z₁.TotalSpace => ((Z₁.localTriv i₁) p).2)
          ((Z₁.localTriv i₁).source ∩ Z₁.proj ⁻¹' (f ⁻¹' Z₂.baseSet i₂)) :=
        (Continuous.comp_continuousOn continuous_snd (Z₁.localTriv i₁).continuousOn).mono
          (fun x hx => hx.1)
      exact ContinuousOn.prodMk h1 (hclm.clm_apply hsnd)
    -- assemble via the target trivialisation
    intro p hp
    have hmem : (⟨f p.1, (Z₂.coordChange (Z₂.indexAt (f p.1)) i₂ (f p.1)) (T p.1 p.2)⟩ : B × F')
        ∈ (Z₂.localTriv i₂).target := by
      rw [VectorBundleCore.mem_localTriv_target]; exact hp.2
    have hcomp : ContinuousWithinAt (fun p : Z₁.TotalSpace =>
        (⟨f p.1, (Z₂.coordChange (Z₂.indexAt (f p.1)) i₂ (f p.1)) (T p.1 p.2)⟩ : B × F'))
        ((Z₁.localTriv i₁).source ∩ Z₁.proj ⁻¹' (f ⁻¹' Z₂.baseSet i₂)) p :=
      hcont.continuousWithinAt hp
    let Ψ : B × F' → Z₂.TotalSpace := fun q => ⟨q.1, (Z₂.localTriv i₂).symm q.1 q.2⟩
    let Φ : Z₁.TotalSpace → B × F' := fun p =>
      (⟨f p.1, (Z₂.coordChange (Z₂.indexAt (f p.1)) i₂ (f p.1)) (T p.1 p.2)⟩ : B × F')
    have hsymm : ContinuousWithinAt Ψ ((Z₂.localTriv i₂).baseSet ×ˢ Set.univ) (Φ p) :=
      (Z₂.localTriv i₂).continuousOn_symm.continuousWithinAt (by
        simp only [Set.mem_prod, Set.mem_univ, and_true]; exact hp.2)
    have hfinal : ContinuousWithinAt (Ψ ∘ Φ)
        ((Z₁.localTriv i₁).source ∩ Z₁.proj ⁻¹' (f ⁻¹' Z₂.baseSet i₂)) p :=
      hsymm.comp hcomp (fun q hq =>
        (VectorBundleCore.mem_localTriv_target Z₂ i₂ (Φ q)).mpr
          (by simpa [Φ, VectorBundleCore.baseSet_at] using hq.2))
    have hpt : ∀ q ∈ (Z₁.localTriv i₁).source ∩ Z₁.proj ⁻¹' (f ⁻¹' Z₂.baseSet i₂),
        (⟨f q.1, T q.1 q.2⟩ : Z₂.TotalSpace) = Ψ (Φ q) := by
      intro q hq
      have hq2 : f q.1 ∈ Z₂.baseSet i₂ := hq.2
      show (⟨f q.1, T q.1 q.2⟩ : Z₂.TotalSpace)
        = (⟨f q.1, (Z₂.localTriv i₂).symm (f q.1)
        ((Z₂.coordChange (Z₂.indexAt (f q.1)) i₂ (f q.1)) (T q.1 q.2))⟩ : Z₂.TotalSpace)
      rw [VectorBundleCore.localTriv_symm_apply Z₂ i₂ hq2]
      congr 1
      have hcc := Z₂.coordChange_comp (Z₂.indexAt (f q.1)) i₂ (Z₂.indexAt (f q.1)) (f q.1)
        ⟨⟨Z₂.mem_baseSet_at (f q.1), hq2⟩, Z₂.mem_baseSet_at (f q.1)⟩ ((T q.1) q.2)
      rw [hcc, Z₂.coordChange_self (Z₂.indexAt (f q.1)) (f q.1)
        (Z₂.mem_baseSet_at (f q.1))]
    exact hfinal.congr hpt (hpt p hp)
  rw [continuous_iff_continuousAt]
  intro p
  refine (hgOn (Z₁.indexAt p.1) (Z₂.indexAt (f p.1))).continuousAt ?_
  refine (IsOpen.inter ?_ ?_).mem_nhds ⟨?_, ?_⟩
  · exact (Z₁.localTriv (Z₁.indexAt p.1)).open_source
  · exact (Z₂.isOpen_baseSet (Z₂.indexAt (f p.1))).preimage f.continuous
      |>.preimage (FiberBundle.continuous_proj F Z₁.Fiber)
  · exact (VectorBundleCore.mem_localTriv_source Z₁ (Z₁.indexAt p.1) p).mpr
      (Z₁.mem_baseSet_at p.1)
  · exact Z₂.mem_baseSet_at (f p.1)

/-- **Two presentations of the tangent bundle with the same underlying manifold are isomorphic.**
If the transition functions of two gluing data `Z`, `Z'` on `M` with fibre `E` are those of the
tangent bundle `TM` along index maps `c`, `c'` into the atlas of `M`, and if the chart expressions
of the identity of the fibres are continuous, then `Z ≅ Z'`.  The isomorphism is the identity on
the fibres. -/
theorem presentation_independence {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] {ι ι' : Type} (Z : VectorBundleCore ℝ M E ι)
    (Z' : VectorBundleCore ℝ M E ι') (c : ι → atlas H M) (c' : ι' → atlas H M)
    (hZ : ∀ i j x, Z.coordChange i j x =
      (Work.TangentClasses.tangentBundle I M).coordChange (c i) (c j) x)
    (hZ' : ∀ i j x, Z'.coordChange i j x =
      (Work.TangentClasses.tangentBundle I M).coordChange (c' i) (c' j) x)
    (hcont : ∀ (i : ι) (i' : ι'), ContinuousOn (fun x : M =>
      (Z'.coordChange (Z'.indexAt x) i' x).comp (Z.coordChange i (Z.indexAt x) x))
      (Z.baseSet i ∩ Z'.baseSet i')) :
    Nonempty (Work.Thom.BundleIso Z Z') := by
  have hone : ∀ f : E →L[ℝ] E, (1 : E →L[ℝ] E).comp f = f := fun f => by ext v; simp
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact fun _ => LinearMap.id
  · exact fun _ => LinearMap.id
  · intro b x; rfl
  · intro b x; rfl
  · refine continuous_totalSpaceMap_clm' Z Z' (ContinuousMap.id M) (fun _ => 1) ?_
    intro i i'
    rw [ContinuousMap.coe_id, Set.preimage_id]
    refine (hcont i i').congr ?_
    intro b hb
    show (Z'.coordChange (Z'.indexAt b) i' b).comp (Z.coordChange i (Z.indexAt b) b)
        = (Z'.coordChange (Z'.indexAt b) i' b).comp
            ((1 : E →L[ℝ] E).comp (Z.coordChange i (Z.indexAt b) b))
    rw [hone]
  · refine continuous_totalSpaceMap_clm' Z' Z (ContinuousMap.id M) (fun _ => 1) ?_
    intro i' i
    rw [ContinuousMap.coe_id, Set.preimage_id]
    have hA : ContinuousOn (fun b : M => (Z'.coordChange (Z'.indexAt b) i' b).comp
        (Z.coordChange i (Z.indexAt b) b)) (Z'.baseSet i' ∩ Z.baseSet i) := by
      rw [Set.inter_comm]; exact hcont i i'
    have hBA : ∀ x ∈ Z'.baseSet i' ∩ Z.baseSet i, ∀ v : E,
        ((Z.coordChange (Z.indexAt x) i x).comp (Z'.coordChange i' (Z'.indexAt x) x))
          (((Z'.coordChange (Z'.indexAt x) i' x).comp (Z.coordChange i (Z.indexAt x) x)) v) = v := by
      intro x hx v
      have hxZ : x ∈ Z.baseSet i := hx.2
      have hxZ' : x ∈ Z'.baseSet i' := hx.1
      have hxz : x ∈ Z.baseSet (Z.indexAt x) := Z.mem_baseSet_at x
      have hxz' : x ∈ Z'.baseSet (Z'.indexAt x) := Z'.mem_baseSet_at x
      show (Z.coordChange (Z.indexAt x) i x) ((Z'.coordChange i' (Z'.indexAt x) x)
        ((Z'.coordChange (Z'.indexAt x) i' x) ((Z.coordChange i (Z.indexAt x) x) v))) = v
      rw [Z'.coordChange_comp (Z'.indexAt x) i' (Z'.indexAt x) x ⟨⟨hxz', hxZ'⟩, hxz'⟩,
        Z'.coordChange_self (Z'.indexAt x) x hxz',
        Z.coordChange_comp i (Z.indexAt x) i x ⟨⟨hxZ, hxz⟩, hxZ⟩,
        Z.coordChange_self i x hxZ]
    have hAB : ∀ x ∈ Z'.baseSet i' ∩ Z.baseSet i, ∀ v : E,
        ((Z'.coordChange (Z'.indexAt x) i' x).comp (Z.coordChange i (Z.indexAt x) x))
          (((Z.coordChange (Z.indexAt x) i x).comp (Z'.coordChange i' (Z'.indexAt x) x)) v) = v := by
      intro x hx v
      have hxZ : x ∈ Z.baseSet i := hx.2
      have hxZ' : x ∈ Z'.baseSet i' := hx.1
      have hxz : x ∈ Z.baseSet (Z.indexAt x) := Z.mem_baseSet_at x
      have hxz' : x ∈ Z'.baseSet (Z'.indexAt x) := Z'.mem_baseSet_at x
      show (Z'.coordChange (Z'.indexAt x) i' x) ((Z.coordChange i (Z.indexAt x) x)
        ((Z.coordChange (Z.indexAt x) i x) ((Z'.coordChange i' (Z'.indexAt x) x) v))) = v
      rw [Z.coordChange_comp (Z.indexAt x) i (Z.indexAt x) x ⟨⟨hxz, hxZ⟩, hxz⟩,
        Z.coordChange_self (Z.indexAt x) x hxz,
        Z'.coordChange_comp i' (Z'.indexAt x) i' x ⟨⟨hxZ', hxz'⟩, hxZ'⟩,
        Z'.coordChange_self i' x hxZ']
    refine (continuousOn_inv_of_comp_eq_one hA hBA hAB).congr (fun b hb => ?_)
    show (Z.coordChange (Z.indexAt b) i b).comp (Z'.coordChange i' (Z'.indexAt b) b)
        = (Z.coordChange (Z.indexAt b) i b).comp
            ((1 : E →L[ℝ] E).comp (Z'.coordChange i' (Z'.indexAt b) b))
    rw [hone]

end

end Work.Agree
