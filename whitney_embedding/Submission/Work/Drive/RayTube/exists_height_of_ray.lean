import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Noncompact.CompressionTube.exists_collar_of_local_slabs
import Submission.Work.Noncompact.CompressionTube.smooth_left_inverse_tools
import Submission.Work.Noncompact.CompressionTube.isLocalDiffeomorph_of_immersion
import Submission.Work.Whitney.exists_sheet_model

/-!
# A smooth height function along a proper embedded ray

Given a smooth proper embedded ray `ρ : [0,∞) → M` in a smooth `n`-manifold `M` whose derivative
is injective along the ray, there is a smooth function `g : M → ℝ` with `g (ρ t) = t` for all
`t ≥ 0`.

The proof is the standard partition-of-unity argument.  Around each point `ρ s` of the ray one
constructs a *local height function*: a chart coordinate `u ∘ c` whose derivative along the ray at
`s` does not vanish has a smooth local inverse `L` defined near `u (c (ρ s))`, and `L ∘ u ∘ c` is a
smooth function on a neighbourhood of `ρ s` which agrees with the parameter `t` on the ray close to
`s`.  (The domain of this local function is cut down along the ray so that the identity
`L (u (c (ρ t))) = t` holds for *every* point `ρ t` of the ray in it; here the injectivity of the
ray is used, and properness makes the cut-down set open.)  Gluing the local functions by a smooth
partition of unity subordinate to the (closed) image of the ray gives the global height.
-/

namespace Work.Drive.RayTube

open scoped Manifold ContDiff
open Topology Set Function
open Work.Noncompact.CompressionTube

noncomputable section

/-! ## Two elementary tools -/

set_option backward.isDefEq.respectTransparency false in
/-- **Injectivity of the derivative of the chart expression at a single point.**  If `f : E → M` is
smooth, `c` is a chart of `M` around `f y` and the manifold derivative of `f` at `y` is injective,
then the Fréchet derivative at `y` of the coordinate expression `z ↦ c (f z)` is injective.  (This
is `Work.Noncompact.CompressionTube.injective_fderiv_chart_comp` with the pointwise hypothesis,
which is what the ray statement provides.) -/
theorem injective_fderiv_chart_comp_at {E E' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {M : Type*} [TopologicalSpace M] [ChartedSpace E' M]
    [IsManifold 𝓘(ℝ,E') ∞ M] {f : E → M} {y : E}
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E') ∞ f)
    {c : OpenPartialHomeomorph M E'} (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ,E') ∞ M)
    (h : Function.Injective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E') f y))
    (hy : f y ∈ c.source) :
    Function.Injective (fderiv ℝ (fun z => c (f z)) y) := by
  rw [(hasFDerivAt_chart_comp hf hc hy).fderiv, ContinuousLinearMap.coe_comp]
  exact Function.Injective.comp (isLocalDiffeomorphAt_chart_mfderiv_injective hc hy) h

/-! ## The local height function along the ray -/

/-- **A local height function along the ray.**  For every point `ρ s` of the ray (`s ≥ 0`) there is
an open neighbourhood `U` of `ρ s` and a smooth function `F` on `U` with `F (ρ t) = t` for every
point `ρ t` of the ray with `t ≥ 0` which lies in `U`.

The construction follows `Work.Noncompact.CompressionTube.exists_local_left_inverse`: pick a chart
`c` at `ρ s` and a coordinate `u` for which `t ↦ u (c (ρ t))` has nonzero derivative at `s`; the
inverse function theorem gives a smooth local inverse `L` of this scalar function, and
`F = L ∘ u ∘ c`.  The domain is cut down to `(ρ '' Jᶜ)ᶜ ∩ c.source ∩ (u ∘ c)⁻¹' O`, so that every
point of the ray in it corresponds to a parameter in `J`, where the scalar inverse relation holds;
here the injectivity of `ρ` on `[0,∞)` is used, and properness of the ray makes `ρ '' Jᶜ` closed. -/
theorem exists_local_left_inverse_ray {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    [T2Space M] [SecondCountableTopology M] {ρ : ℝ → M}
    (hρ : ContMDiff MCreal (MC n) smoothOrder ρ)
    (hprop : IsProperMap (fun t : Set.Ici (0:ℝ) => ρ t))
    (hinj : Set.InjOn ρ (Set.Ici (0:ℝ)))
    (himm : ∀ t : ℝ, 0 ≤ t → Function.Injective (mfderiv MCreal (MC n) ρ t))
    (s : Set.Ici (0:ℝ)) :
    ∃ (U : Set M) (F : M → ℝ), IsOpen U ∧ ρ s ∈ U ∧
      ContMDiffOn (MC n) MCreal smoothOrder F U ∧
      ∀ t : Set.Ici (0:ℝ), ρ t ∈ U → F (ρ t) = (t : ℝ) := by
  classical
  set c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) (ρ s) with hc_def
  have hc : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M :=
    IsManifold.chart_mem_maximalAtlas (ρ s)
  have hmem : ρ s ∈ c.source := mem_chart_source (EuclideanSpace ℝ (Fin n)) (ρ s)
  have hI : IsOpen (ρ ⁻¹' c.source) := c.open_source.preimage hρ.continuous
  have hsI : (s : ℝ) ∈ ρ ⁻¹' c.source := hmem
  -- the chart expression of the ray is smooth on a neighbourhood of `s`
  have hh_smooth : ContDiffOn ℝ smoothOrder (fun t => c (ρ t)) (ρ ⁻¹' c.source) :=
    contMDiffOn_iff_contDiffOn.mp
      ((contMDiffOn_of_mem_maximalAtlas hc).comp hρ.contMDiffOn (fun t ht => ht))
  have hh_inj : Function.Injective (fderiv ℝ (fun t => c (ρ t)) (s : ℝ)) :=
    injective_fderiv_chart_comp_at hρ hc (himm s s.2) hmem
  -- pick a chart coordinate in which the derivative is nonzero
  have hne : fderiv ℝ (fun t => c (ρ t)) (s : ℝ) 1 ≠ 0 := fun h0 =>
    one_ne_zero (hh_inj (by rw [h0, map_zero]))
  obtain ⟨j, hj⟩ : ∃ j : Fin n, (fderiv ℝ (fun t => c (ρ t)) (s : ℝ) 1) j ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hne (PiLp.ext hcon)
  let u : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := EuclideanSpace.proj (𝕜 := ℝ) j
  have hu_apply : ∀ y : EuclideanSpace ℝ (Fin n), u y = y j := fun y => by
    simp [u, PiLp.proj_apply]
  -- the corresponding scalar coordinate function
  have hG_smooth : ContDiffOn ℝ smoothOrder (fun t => u (c (ρ t))) (ρ ⁻¹' c.source) :=
    u.contDiff.comp_contDiffOn hh_smooth
  have hG_fderiv : fderiv ℝ (fun t => u (c (ρ t))) (s : ℝ) =
      u ∘L fderiv ℝ (fun t => c (ρ t)) (s : ℝ) := by
    have hhat : HasFDerivAt (fun t => c (ρ t)) (fderiv ℝ (fun t => c (ρ t)) (s : ℝ)) s :=
      (hh_smooth.contDiffAt (hI.mem_nhds hsI)).differentiableAt (by simp) |>.hasFDerivAt
    exact (u.hasFDerivAt.comp (s : ℝ) hhat).fderiv
  have hG_inj : Function.Injective (fderiv ℝ (fun t => u (c (ρ t))) (s : ℝ)) := by
    rw [hG_fderiv]
    have hU1 : (u ∘L fderiv ℝ (fun t => c (ρ t)) (s : ℝ)) 1 ≠ 0 := by
      simpa [hu_apply] using hj
    intro x y hxy
    have h2 : (u ∘L fderiv ℝ (fun t => c (ρ t)) (s : ℝ)) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have h1 : (x - y) • ((u ∘L fderiv ℝ (fun t => c (ρ t)) (s : ℝ)) 1) = 0 := by
      calc (x - y) • ((u ∘L fderiv ℝ (fun t => c (ρ t)) (s : ℝ)) 1)
          = (u ∘L fderiv ℝ (fun t => c (ρ t)) (s : ℝ)) ((x - y) • (1 : ℝ)) :=
            (ContinuousLinearMap.map_smul _ _ _).symm
        _ = (u ∘L fderiv ℝ (fun t => c (ρ t)) (s : ℝ)) (x - y) := by rw [smul_eq_mul, mul_one]
        _ = 0 := h2
    rcases smul_eq_zero.mp h1 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hU1
  -- the inverse function theorem: the coordinate function has a smooth local inverse
  obtain ⟨L, O, W, hOo, hOs, hWo, hsW, hWV, hLGa, hLsmooth, hLO, hLG, huniq⟩ :=
    Work.Whitney.exists_localInverse_smooth_on (fun t => u (c (ρ t))) (ρ ⁻¹' c.source) hI (s : ℝ) hsI
      hG_smooth hG_inj
  -- an open neighbourhood of `s` on which the inverse identity may be used
  have hGcont : ContinuousAt (fun t => u (c (ρ t))) (s : ℝ) :=
    (hG_smooth.contDiffAt (hI.mem_nhds hsI)).continuousAt
  obtain ⟨J₁, hJ₁sub, hJ₁open, hsJ₁⟩ :=
    mem_nhds_iff.mp (hGcont.preimage_mem_nhds (hOo.mem_nhds hOs))
  set J : Set ℝ := W ∩ J₁ with hJ_def
  have hJopen : IsOpen J := hWo.inter hJ₁open
  have hsJ : (s : ℝ) ∈ J := ⟨hsW, hsJ₁⟩
  -- the parameters of the ray outside `J` (a closed set of the half line)
  set K : Set (Set.Ici (0:ℝ)) := {w : Set.Ici (0:ℝ) | (w : ℝ) ∉ J} with hK_def
  have hKclosed : IsClosed K := hJopen.isClosed_compl.preimage continuous_subtype_val
  -- the local data
  set U : Set M := ((fun t : Set.Ici (0:ℝ) => ρ t) '' K)ᶜ ∩
      (c.source ∩ (fun x => u (c x)) ⁻¹' O) with hU_def
  refine ⟨U, fun x => L (u (c x)), ?_, ?_, ?_, ?_⟩
  · rw [hU_def]
    refine ((hprop.isClosedMap K hKclosed).isOpen_compl).inter ?_
    exact (u.continuous.comp_continuousOn c.continuousOn).isOpen_inter_preimage
      c.open_source hOo
  · -- `ρ s ∈ U`
    rw [hU_def]
    refine ⟨?_, hmem, hOs⟩
    simp only [mem_compl_iff, mem_image, not_exists, not_and]
    intro t ht hts
    exact ht ((hinj t.2 s.2 hts) ▸ hsJ)
  · -- smoothness of `L ∘ u ∘ c` on `U`
    have hcU : ContMDiffOn (MC n) (MC n) smoothOrder (c : M → EuclideanSpace ℝ (Fin n)) U :=
      (contMDiffOn_of_mem_maximalAtlas hc).mono (fun x hx => hx.2.1)
    have hucU : ContMDiffOn (MC n) MCreal smoothOrder (fun x => u (c x)) U :=
      u.contMDiff.comp_contMDiffOn hcU
    exact hLsmooth.contMDiffOn.comp hucU (fun x hx => hx.2.2)
  · -- the left inverse property
    intro t ht
    have htJ : (t : ℝ) ∈ J := by
      by_contra htJ
      exact ht.1 ⟨t, htJ, rfl⟩
    have hGtO : u (c (ρ t)) ∈ O := hJ₁sub htJ.2
    have hz : (t : ℝ) = L (u (c (ρ t))) := huniq (u (c (ρ t))) hGtO (t : ℝ) htJ.1 rfl
    show L (u (c (ρ t))) = (t : ℝ)
    exact hz.symm

/-! ## Gluing the local height functions -/

/-- **Gluing local height functions along the ray.**  Let `γ : [0,∞) → M` have closed range and let
`(U s, F s)` be local data: `U s` an open neighbourhood of `γ s` and `F s` a function smooth on
`U s` with `F s = (· : ℝ)` on `U s ∩ range γ`.  Then the data glue to a globally smooth left
inverse of `γ`.

This is `Work.Noncompact.CompressionTube.smooth_left_inverse_of_local` for a ray (a map on the half
line); only the closedness of the range of `γ` is used. -/
theorem smooth_left_inverse_of_local_ray {n : ℕ}
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M] [T2Space M] [SecondCountableTopology M]
    {γ : Set.Ici (0:ℝ) → M} (hprop : IsProperMap γ)
    (U : Set.Ici (0:ℝ) → Set M) (hUo : ∀ s, IsOpen (U s)) (hUm : ∀ s, γ s ∈ U s)
    (F : Set.Ici (0:ℝ) → M → ℝ)
    (hF : ∀ s, ContMDiffOn (MC n) MCreal smoothOrder (F s) (U s))
    (hUF : ∀ s t : Set.Ici (0:ℝ), γ t ∈ U s → F s (γ t) = (t : ℝ)) :
    ∃ g : M → ℝ, ContMDiff (MC n) MCreal smoothOrder g ∧
      ∀ s : Set.Ici (0:ℝ), g (γ s) = (s : ℝ) := by
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  haveI : SigmaCompactSpace M := sigmaCompactSpace_of_locallyCompact_secondCountable
  let C : Set M := range γ
  have hCcl : IsClosed C := hprop.isClosed_range
  let V : Option (Set.Ici (0:ℝ)) → Set M := fun i => match i with | none => Cᶜ | some s => U s
  have hVo : ∀ i, IsOpen (V i) := by
    intro i; cases i with
    | none => exact hCcl.isOpen_compl
    | some s => exact hUo s
  have hVcov : C ⊆ ⋃ i, V i := by
    rintro x ⟨t, rfl⟩
    exact mem_iUnion.mpr ⟨some t, hUm t⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (MC n) hCcl V hVo hVcov
  let G : Option (Set.Ici (0:ℝ)) → M → ℝ := fun i => match i with | none => 0 | some s => F s
  have hG : ∀ i, ContMDiffOn (MC n) MCreal smoothOrder (G i) (V i) := by
    intro i; cases i with
    | none => exact contMDiffOn_const
    | some s => exact hF s
  refine ⟨fun x => ∑ᶠ i, ρ i x • G i x, ?_, ?_⟩
  · exact hρ.contMDiff_finsum_smul hVo hG
  · intro t
    have htC : γ t ∈ C := ⟨t, rfl⟩
    have hterm : ∀ i, ρ i (γ t) • G i (γ t) = ρ i (γ t) • (t : ℝ) := by
      intro i
      by_cases h0 : ρ i (γ t) = 0
      · simp [h0]
      · have hmem : γ t ∈ tsupport (ρ i) := subset_closure (mem_support.mpr h0)
        have hsub : γ t ∈ V i := hρ i hmem
        cases i with
        | none => exact absurd htC hsub
        | some s => show ρ (some s) (γ t) • F s (γ t) = ρ (some s) (γ t) • (t : ℝ)
                    rw [hUF s t hsub]
    change (∑ᶠ i, ρ i (γ t) • G i (γ t)) = (t : ℝ)
    rw [finsum_congr hterm]
    have h₁ : (∑ᶠ i, ρ i (γ t) • (t : ℝ)) = ∑ i ∈ ρ.finsupport (γ t), ρ i (γ t) • (t : ℝ) :=
      (ρ.sum_finsupport_smul_eq_finsum (γ t) (fun _ _ => (t : ℝ))).symm
    rw [h₁, ← Finset.sum_smul, ρ.sum_finsupport (γ t) htC, one_smul]

/-! ## The height function of the ray -/

open scoped Manifold ContDiff in
open Work.Noncompact.CompressionTube in
theorem exists_height_of_ray {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    [T2Space M] [SecondCountableTopology M]
    {ρ : ℝ → M} (hρ : ContMDiff MCreal (MC n) smoothOrder ρ)
    (hinj : Set.InjOn ρ (Set.Ici (0:ℝ)))
    (hprop : IsProperMap (fun t : Set.Ici (0:ℝ) => ρ t))
    (himm : ∀ t : ℝ, 0 ≤ t → Function.Injective (mfderiv MCreal (MC n) ρ t)) :
    ∃ g : M → ℝ, ContMDiff (MC n) MCreal smoothOrder g ∧
      ∀ t : ℝ, 0 ≤ t → g (ρ t) = t := by
  have _ : 2 ≤ n := hn
  have key : ∀ s : Set.Ici (0:ℝ), ∃ (U : Set M) (F : M → ℝ), IsOpen U ∧ ρ s ∈ U ∧
      ContMDiffOn (MC n) MCreal smoothOrder F U ∧
      ∀ t : Set.Ici (0:ℝ), ρ t ∈ U → F (ρ t) = (t : ℝ) :=
    fun s => exists_local_left_inverse_ray hρ hprop hinj himm s
  choose U F hprops using key
  obtain ⟨g, hgsm, hg⟩ := smooth_left_inverse_of_local_ray hprop U (fun s => (hprops s).1)
    (fun s => (hprops s).2.1) F (fun s => (hprops s).2.2.1)
    (fun s t ht => (hprops s).2.2.2 t ht)
  exact ⟨g, hgsm, fun t ht => hg ⟨t, ht⟩⟩

end

end Work.Drive.RayTube
