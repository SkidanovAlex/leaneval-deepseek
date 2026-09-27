import Mathlib
import Submission.Work.Drive.meetBoxEngine
import Submission.Work.Drive.geometricCount
import Submission.Work.Drive.localConstancy_oneThree
import Submission.Work.Drive.finite_loopChainMeet_of_transverse
import Submission.Work.Drive.meetPt_ncard_eq_of_regular_embedded

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# Locality of the *geometric* (pairing) count of a loop against a `3`-chain in a `4`-manifold

`Submission/Work/Drive/HN4_SEAM_DEFECT.md` records the defect of the design's box count
`Work.Drive.coreSideCount Q c P`: both parameter domains are quotients presented by closed boxes, so a
meet sitting on the loop's seam (`t = 0 ≡ 1`) or on the chain's box seam is counted **twice**, and the
parity of the box count flips at the isolated angles where a meet crosses a seam — an event no generic
perturbation removes.  The corrected count is the *geometric* (parameterisation-free) one, the number of
distinct points of the manifold at which the loop meets the chain.

This file proves the **locality** of that count, in the form `hn4` needs:

* **`Work.Drive.meetPt_ncard_eq_of_localSolutions`** — the chart-free engine.  Given a continuous loop
  `L : ℝ → M` (periodic with period `1`) and a continuous family `u ↦ D u` of `3`-chains whose box
  covers the chain's image (`hbox`), with finitely many base meets and, at each base meet, a *local
  solution* `ψ` (the output of the implicit function theorem), the number of distinct loop values on
  the meet set is locally constant in `u`.  The proof is the standard transversality argument run on
  the *geometric* count: the local solutions are unique in their balls, every meet of a nearby chain is
  one of them (compactness of the box, Hausdorffness of `M`), and the values `L (ψ_ξ u).1` agree on the
  classes of base meets with equal loop value — the periodicity (`hper`) plus "the loop is injective
  modulo its period" (`hinj`) are what makes those classes stable.
* **`Work.Drive.chartedDiff_surjective_of_transverse`** — the bridge that *produces* the implicit
  function theorem's hypothesis from the intrinsic transversality
  `range (mfderiv L p.1) ⊔ range (mfderiv (D 0) p.2) = ⊤` (the change of coordinates is the same on
  both sides, `tangentCoordChange_self`, since the chart is centred at the common value).
* **`Work.Drive.meetPt_ncard_eq_of_regular_manifold`** — the two together: at a configuration whose
  meets are finite and transverse and whose loop is embedded modulo its period, the geometric count is
  locally constant.

The `(1,3)` system is square (`1 + 3 = 4` parameters against `4` equations), so the implicit function
theorem applies; the only new ingredient relative to the vector-space engine
`Work.Drive.meetPt_ncard_eq_of_regular_embedded` is the manifold charting in
`Work.Drive.exists_local_solution_of_chartDiff`, whose shape mirrors
`Work.Drive.loopChainMeet_isolated` (`Submission/Work/Drive/finite_loopChainMeet_of_transverse.lean`).
-/

namespace Work.Drive

open Filter
open scoped Topology ContDiff
open Manifold

set_option backward.isDefEq.respectTransparency false

noncomputable section

/-! ## 1. The implicit function theorem with a pointwise smoothness hypothesis

`Work.Drive.exists_local_solution_of_surjective` (`localConstancy_oneThree.lean`) asks for a *globally*
smooth family `(s,x) ↦ G s x`.  In the manifold application the family is the charted difference map,
which is only smooth near the meet (the chart is junk outside its source), so the pointwise form is what
is usable.  The proof is that of the global form verbatim — the smoothness is used in a single place
(the strict differentiability of `R (s,x) = (s, G s x)`), and `ContDiffAt.hasStrictFDerivAt` supplies it
there. -/

/-- **The local solution of a regular family, with smoothness only at the base point.** -/
theorem exists_local_solution_of_surjective_at {F E : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (G : ℝ → F → E) {ξ : F}
    (hG : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × F => G p.1 p.2) (0, ξ))
    (hdim : Module.finrank ℝ F = Module.finrank ℝ E) (hξ0 : G 0 ξ = 0)
    (hsurj : Function.Surjective (fderiv ℝ (G 0) ξ)) :
    ∃ (ε δ : ℝ) (ψ : ℝ → F), 0 < ε ∧ 0 < δ ∧ ψ 0 = ξ ∧
      Filter.Tendsto ψ (nhds (0 : ℝ)) (nhds ξ) ∧
      (∀ s, |s| < ε → ‖ψ s - ξ‖ < δ ∧ G s (ψ s) = 0) ∧
      (∀ s, |s| < ε → ∀ x, ‖x - ξ‖ < δ → G s x = 0 → x = ψ s) := by
  classical
  have hne : Ctop ≠ 0 := by decide
  set uG : ℝ × F → E := fun p => G p.1 p.2 with huG
  have hucd : ContDiffAt ℝ Ctop uG (0, ξ) := hG
  have huat : HasFDerivAt uG (fderiv ℝ uG (0, ξ)) (0, ξ) :=
    (hucd.differentiableAt hne).hasFDerivAt
  set dG : F →L[ℝ] E := fderiv ℝ (G 0) ξ with hdG
  have happ : ∀ w : F, fderiv ℝ uG (0, ξ) (0, w) = dG w := by
    intro w
    have h := congrArg (fun (T : F →L[ℝ] E) => T w) (fderiv_uncurry_snd huat).symm
    simpa [huG, hdG, ContinuousLinearMap.inr_apply] using h
  -- surjective + equal dimensions ⟹ bijective
  have hdGinj : Function.Injective dG :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := dG.toLinearMap) hdim).mpr hsurj
  -- the derivative `L` of `R (s,x) = (s, uG (s,x))`
  set L : ℝ × F →L[ℝ] ℝ × E :=
    (ContinuousLinearMap.fst ℝ ℝ F).prod (fderiv ℝ uG (0, ξ)) with hL
  have hLc : ∀ p : ℝ × F, L p = (p.1, fderiv ℝ uG (0, ξ) p) := fun p => rfl
  have hLsurj : Function.Surjective L := by
    rintro ⟨b, y⟩
    obtain ⟨v, hv⟩ := hsurj (y - b • (fderiv ℝ uG (0, ξ) ((1 : ℝ), (0 : F))))
    refine ⟨(b, v), ?_⟩
    rw [hLc]
    refine Prod.ext rfl ?_
    have hsplit : (b, v) = b • ((1 : ℝ), (0 : F)) + (0, v) := by ext <;> simp
    rw [hsplit, map_add, map_smul, happ, hv]
    abel
  have hdim2 : Module.finrank ℝ (ℝ × F) = Module.finrank ℝ (ℝ × E) := by
    rw [Module.finrank_prod, Module.finrank_prod, hdim]
  have hLinj : Function.Injective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (L : ℝ × F →ₗ[ℝ] ℝ × E)) hdim2).mpr hLsurj
  have hbij : Function.Bijective (L : ℝ × F →ₗ[ℝ] ℝ × E) := ⟨hLinj, hLsurj⟩
  let e := (LinearEquiv.ofBijective (L : ℝ × F →ₗ[ℝ] ℝ × E) hbij).toContinuousLinearEquiv
  have he : (e : ℝ × F →L[ℝ] ℝ × E) = L := by
    apply ContinuousLinearMap.ext; intro x; rfl
  -- the map `R` and its strict derivative
  set R : ℝ × F → ℝ × E := fun p => (p.1, uG p) with hRdef
  have hRfd : HasFDerivAt R L (0, ξ) := hasFDerivAt_fst.prodMk huat
  have hRcd : ContDiffAt ℝ Ctop R (0, ξ) := by
    rw [hRdef]
    exact contDiffAt_fst.prodMk hucd
  have hst : HasStrictFDerivAt R (e : ℝ × F →L[ℝ] ℝ × E) (0, ξ) := by
    rw [he, ← hRfd.fderiv]
    exact hRcd.hasStrictFDerivAt hne
  let Φ : OpenPartialHomeomorph (ℝ × F) (ℝ × E) := HasStrictFDerivAt.toOpenPartialHomeomorph R hst
  have hΦcoe : (Φ : ℝ × F → ℝ × E) = R := HasStrictFDerivAt.toOpenPartialHomeomorph_coe hst
  have hsrc : (0, ξ) ∈ Φ.source := HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source hst
  have hR0 : R (0, ξ) = ((0 : ℝ), (0 : E)) := by simp [hRdef, huG, hξ0]
  have htgt : R (0, ξ) ∈ Φ.target :=
    HasStrictFDerivAt.image_mem_toOpenPartialHomeomorph_target hst
  have htgt0 : (((0 : ℝ), (0 : E)) : ℝ × E) ∈ Φ.target := by rwa [← hR0]
  obtain ⟨r_src, hr_src, hr_src'⟩ := Metric.mem_nhds_iff.mp (Φ.open_source.mem_nhds hsrc)
  have htgt_nhds : ∀ᶠ s in nhds (0 : ℝ), ((s, (0 : E)) : ℝ × E) ∈ Φ.target :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
      (Φ.open_target.mem_nhds htgt0)
  obtain ⟨r_tgt, hr_tgt, hr_tgt'⟩ := Metric.mem_nhds_iff.mp htgt_nhds
  have hsymm0 : Φ.symm (((0 : ℝ), (0 : E)) : ℝ × E) = (0, ξ) := by
    have h := Φ.left_inv hsrc
    rw [hΦcoe, hR0] at h
    exact h
  set ψ : ℝ → F := fun s => (Φ.symm ((s, (0 : E)) : ℝ × E)).2 with hψ
  have hψ0 : ψ 0 = ξ := by simp [hψ, hsymm0]
  have hψcont : Filter.Tendsto ψ (nhds (0 : ℝ)) (nhds ξ) := by
    have hs : Filter.Tendsto (fun s : ℝ => Φ.symm ((s, (0 : E)) : ℝ × E)) (nhds (0 : ℝ))
        (nhds (Φ.symm (((0 : ℝ), (0 : E)) : ℝ × E))) :=
      (Φ.continuousAt_symm htgt0).tendsto.comp
        (continuous_id.prodMk continuous_const).continuousAt.tendsto
    rw [hsymm0] at hs
    exact (continuous_snd.continuousAt.tendsto).comp hs
  obtain ⟨r_ψ, hr_ψ, hr_ψ'⟩ := Metric.mem_nhds_iff.mp
    (hψcont.eventually (Metric.ball_mem_nhds ξ hr_src))
  refine ⟨min r_tgt (min r_src r_ψ), r_src, ψ, lt_min hr_tgt (lt_min hr_src hr_ψ), hr_src,
    hψ0, hψcont, ?_, ?_⟩
  · intro s hs
    have hs_tgt : |s| < r_tgt := lt_of_lt_of_le hs (min_le_left _ _)
    have hs_ψ : |s| < r_ψ := lt_of_lt_of_le hs (le_trans (min_le_right _ _) (min_le_right _ _))
    have hd_tgt : dist s (0 : ℝ) < r_tgt := by simpa [Real.dist_eq, sub_zero] using hs_tgt
    have hmem_tgt : ((s, (0 : E)) : ℝ × E) ∈ Φ.target := hr_tgt' hd_tgt
    have hRsol : R (Φ.symm ((s, (0 : E)) : ℝ × E)) = ((s, (0 : E)) : ℝ × E) := by
      rw [← hΦcoe]; exact Φ.right_inv hmem_tgt
    have h1 : (Φ.symm ((s, (0 : E)) : ℝ × E)).1 = s := by
      have := congrArg (fun z : ℝ × E => z.1) hRsol
      simpa [hRdef] using this
    have h2 : uG (Φ.symm ((s, (0 : E)) : ℝ × E)) = 0 := by
      have := congrArg (fun z : ℝ × E => z.2) hRsol
      simpa [hRdef] using this
    have hnorm : ‖ψ s - ξ‖ < r_src := by
      have hs_ψ' : dist s (0 : ℝ) < r_ψ := by simpa [Real.dist_eq, sub_zero] using hs_ψ
      have hm := hr_ψ' hs_ψ'
      simpa [Set.mem_ofPred_eq, dist_eq_norm] using hm
    refine ⟨hnorm, ?_⟩
    have hun : G s (ψ s) = uG (Φ.symm ((s, (0 : E)) : ℝ × E)) := by
      simp [huG, hψ, h1]
    rw [hun]; exact h2
  · intro s hs x hx hx0
    have hs_src : |s| < r_src :=
      lt_of_lt_of_le hs (le_trans (min_le_right _ _) (min_le_left _ _))
    have hs_src' : dist s (0 : ℝ) < r_src := by simpa [Real.dist_eq, sub_zero] using hs_src
    have hball : ((s, x) : ℝ × F) ∈ Metric.ball ((0, ξ) : ℝ × F) r_src := by
      rw [Metric.mem_ball, Prod.dist_eq]
      exact max_lt hs_src' (by rw [dist_eq_norm]; exact hx)
    have hinsrc : (s, x) ∈ Φ.source := hr_src' hball
    have hΦsx : Φ (s, x) = ((s, (0 : E)) : ℝ × E) := by
      rw [hΦcoe]
      have hRt : R (s, x) = (s, G s x) := by simp [hRdef, huG]
      rw [hRt, hx0]
    have hleft := Φ.left_inv hinsrc
    rw [hΦsx] at hleft
    have hfin : (Φ.symm ((s, (0 : E)) : ℝ × E)).2 = x := by
      have := congrArg (fun z : ℝ × F => z.2) hleft
      simpa using this
    exact hfin.symm



/-! ## 2. The charted-derivative bridge for a `ℝ`-parametrised loop

`Work.Drive.fderiv_chart_comp` (`ChartBridge.lean`) computes the derivative of a charted composite for
a chain parametrised by `ℝⁿ`.  The design's loop is parametrised by `ℝ` (the core loop `t ↦ Q (exp (iπt))`),
i.e. by the `1`-dimensional self-model-corners space `𝓘(ℝ,ℝ)`, so the three lemmas below are the same
statements with `𝓡 n` replaced by `𝓘(ℝ,ℝ)`.  They are the only place where the manifold charting enters
the locality engine. -/

/-- `Work.Drive.mfderiv_chart_comp` for a loop parametrised by `ℝ`. -/
theorem mfderiv_chart_comp_real {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]
    (f : ℝ → M) (hf : ContMDiff (𝓘(ℝ,ℝ)) (𝓡 4) Ctop f) (p : M) {s : ℝ}
    (hs : f s ∈ (chr p).source) :
    mfderiv (𝓘(ℝ,ℝ)) (𝓡 4) (fun u => chr p (f u)) s =
      (tangentCoordChange (𝓡 4) (f s) p (f s)).comp (mfderiv (𝓘(ℝ,ℝ)) (𝓡 4) f s) := by
  have hφ : MDifferentiableAt (𝓡 4) (𝓡 4) (chartAt (EuclideanSpace ℝ (Fin 4)) p) (f s) :=
    mdifferentiableAt_atlas (chart_mem_atlas _ _) hs
  have hfs : MDifferentiableAt (𝓘(ℝ,ℝ)) (𝓡 4) f s := (hf s).mdifferentiableAt (by simp)
  have hmain := mfderiv_comp s hφ hfs
  rw [mfderiv_chartAt_eq_tangentCoordChange hs] at hmain
  exact hmain

/-- The same, for the Fréchet derivative. -/
theorem fderiv_chart_comp_real {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]
    (f : ℝ → M) (hf : ContMDiff (𝓘(ℝ,ℝ)) (𝓡 4) Ctop f) (p : M) {s : ℝ}
    (hs : f s ∈ (chr p).source) :
    fderiv ℝ (fun u => chr p (f u)) s =
      (tangentCoordChange (𝓡 4) (f s) p (f s)).comp (mfderiv (𝓘(ℝ,ℝ)) (𝓡 4) f s) := by
  rw [← mfderiv_eq_fderiv]
  exact mfderiv_chart_comp_real f hf p hs

/-- `Work.Drive.fderiv_chart_comp_hasFDerivAt` for a loop parametrised by `ℝ`. -/
theorem fderiv_chart_comp_hasFDerivAt_real {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]
    (f : ℝ → M) (hf : ContMDiff (𝓘(ℝ,ℝ)) (𝓡 4) Ctop f) (p : M) {s : ℝ}
    (hs : f s ∈ (chr p).source) :
    HasFDerivAt (fun u => chr p (f u))
      ((tangentCoordChange (𝓡 4) (f s) p (f s)).comp (mfderiv (𝓘(ℝ,ℝ)) (𝓡 4) f s)) s := by
  have h1 : MDifferentiableAt (𝓡 4) (𝓡 4) (chr p : M → EuclideanSpace ℝ (Fin 4)) (f s) :=
    mdifferentiableAt_atlas (chart_mem_atlas _ _) hs
  have h2 : MDifferentiableAt (𝓘(ℝ,ℝ)) (𝓡 4) f s := (hf s).mdifferentiableAt (by simp)
  have hmd : MDifferentiableAt (𝓘(ℝ,ℝ)) (𝓡 4) (fun u => chr p (f u)) s := h1.comp s h2
  rw [← fderiv_chart_comp_real f hf p hs]
  exact hmd.differentiableAt.hasFDerivAt

/-- **The bridge**: intrinsic transversality of an `ℝ`-parametrised loop and a `3`-chain at a meet
makes the derivative of the *charted* difference map surjective.  The chart is centred at the common
value, so the change of coordinates `tangentCoordChange` is the *same* on the two sides and drops out. -/
theorem chartedDiff_surjective_of_transverse {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]
    (L : ℝ → M) (D : ℝ → EuclideanSpace ℝ (Fin 3) → M)
    (hL : ContMDiff (𝓘(ℝ,ℝ)) (𝓡 4) Ctop L)
    (hD : ContMDiff (𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 3))) (𝓡 4) Ctop
      (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => D q.1 q.2))
    {p : ℝ × EuclideanSpace ℝ (Fin 3)} (heq : L p.1 = D 0 p.2)
    (htrans : LinearMap.range (mfderiv (𝓘(ℝ,ℝ)) (𝓡 4) L p.1).toLinearMap ⊔
      LinearMap.range (mfderiv (𝓡 3) (𝓡 4) (D 0) p.2).toLinearMap = ⊤) :
    Function.Surjective (fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin 3) =>
      chr (L p.1) (L q.1) - chr (L p.1) (D 0 q.2)) p) := by
  classical
  have hD0 : ContMDiff (𝓡 3) (𝓡 4) Ctop (D 0) :=
    hD.comp ((ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin 3))).contMDiff (n := Ctop))
  let M₀ : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 4) := mfderiv (𝓘(ℝ,ℝ)) (𝓡 4) L p.1
  let M₁ : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    mfderiv (𝓡 3) (𝓡 4) (D 0) p.2
  let T : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    tangentCoordChange (𝓡 4) (L p.1) (L p.1) (L p.1)
  have hsL : L p.1 ∈ (chr (L p.1)).source :=
    mem_chart_source (EuclideanSpace ℝ (Fin 4)) (L p.1)
  have hsN : D 0 p.2 ∈ (chr (L p.1)).source := by
    rw [← heq]; exact mem_chart_source _ _
  have hTapp : ∀ v : EuclideanSpace ℝ (Fin 4), T v = v := fun v =>
    tangentCoordChange_self (I := 𝓡 4) (mem_extChartAt_source (I := 𝓡 4) (L p.1))
  have hA : HasFDerivAt (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => chr (L p.1) (L q.1))
      ((T.comp M₀).comp (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin 3)))) p := by
    have h1 := fderiv_chart_comp_hasFDerivAt_real L hL (L p.1) hsL
    have hc := h1.comp p hasFDerivAt_fst
    simpa [Function.comp_def, M₀, T] using hc
  have hB : HasFDerivAt (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => chr (L p.1) (D 0 q.2))
      ((T.comp M₁).comp (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin 3)))) p := by
    have h1 := fderiv_chart_comp_hasFDerivAt (D 0) hD0 (L p.1) hsN
    rw [← heq] at h1
    have hc := h1.comp p hasFDerivAt_snd
    simpa [Function.comp_def, M₁, T] using hc
  have hPderiv : fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin 3) =>
        chr (L p.1) (L q.1) - chr (L p.1) (D 0 q.2)) p
      = ((T.comp M₀).comp (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin 3))))
        - ((T.comp M₁).comp (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin 3)))) := by
    have h := (hA.sub hB).fderiv
    rw [show ((fun q : ℝ × EuclideanSpace ℝ (Fin 3) => chr (L p.1) (L q.1)) -
          (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => chr (L p.1) (D 0 q.2)))
        = (fun q : ℝ × EuclideanSpace ℝ (Fin 3) =>
            chr (L p.1) (L q.1) - chr (L p.1) (D 0 q.2)) from rfl] at h
    exact h
  intro w
  have htr : LinearMap.range M₀.toLinearMap ⊔ LinearMap.range M₁.toLinearMap = ⊤ := by
    simpa [M₀, M₁] using htrans
  have hw : w ∈ LinearMap.range M₀.toLinearMap ⊔ LinearMap.range M₁.toLinearMap := by
    rw [htr]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hw
  obtain ⟨σ, hσ⟩ := LinearMap.mem_range.mp ha
  obtain ⟨τ, hτ⟩ := LinearMap.mem_range.mp (Submodule.neg_mem _ hb)
  refine ⟨(σ, τ), ?_⟩
  have hval : fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin 3) =>
      chr (L p.1) (L q.1) - chr (L p.1) (D 0 q.2)) p (σ, τ) = T (M₀ σ) - T (M₁ τ) := by
    rw [hPderiv]
    simp only [sub_apply, ContinuousLinearMap.comp_apply]
    rfl
  rw [hval]
  rw [show T (M₀ σ) = M₀ σ from hTapp _, show T (M₁ τ) = M₁ τ from hTapp _]
  rw [show M₀ σ = a from hσ, show M₁ τ = -b from hτ]
  rw [sub_neg_eq_add, hab]

/-- **Joint smoothness of the charted difference map of a loop and a family of `3`-chains** (the
`(1,3)` analogue of `Work.Drive.contDiffAt_chartDiff_family_fin`, with the chart centred at the base
meet's value; the hypothesis is exactly that both base values lie in the chart's source). -/
theorem contDiffAt_chartDiff_fam_real {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]
    (L : ℝ → M) (D : ℝ → EuclideanSpace ℝ (Fin 3) → M)
    (hL : ContMDiff (𝓘(ℝ,ℝ)) (𝓡 4) Ctop L)
    (hD : ContMDiff (𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 3))) (𝓡 4) Ctop
      (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => D q.1 q.2))
    {c : M} {u₀ : ℝ} {y : EuclideanSpace ℝ (Fin 3)}
    (hLu : L u₀ ∈ (chr c).source) (hDy : D 0 y ∈ (chr c).source) :
    ContDiffAt ℝ Ctop (fun p : ℝ × (ℝ × EuclideanSpace ℝ (Fin 3)) =>
      chr c (L p.2.1) - chr c (D p.1 p.2.2)) (0, (u₀, y)) := by
  have hchartOn : ContMDiffOn (𝓡 4) (𝓡 4) Ctop (chr c) (chr c).source := by
    have h := contMDiffOn_extChartAt (I := 𝓡 4) (x := c) (n := Ctop)
    simpa [chr] using h
  -- the loop side
  have hloop : ContDiffAt ℝ Ctop (fun u : ℝ => chr c (L u)) u₀ :=
    ((hchartOn.contMDiffAt ((chr c).open_source.mem_nhds hLu)).comp u₀ (hL u₀)).contDiffAt
  have hloop2 : ContDiffAt ℝ Ctop (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => chr c (L q.1))
      (u₀, y) := hloop.fst' (y := y)
  have hcdA : ContDiffAt ℝ Ctop (fun p : ℝ × (ℝ × EuclideanSpace ℝ (Fin 3)) =>
      chr c (L p.2.1)) (0, (u₀, y)) :=
    ContDiffAt.comp (x := (0, (u₀, y))) (f := Prod.snd) hloop2 contDiffAt_snd
  -- the chain side
  have hfam : ContDiffAt ℝ Ctop
      (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => chr c (D q.1 q.2)) (0, y) :=
    ((hchartOn.contMDiffAt ((chr c).open_source.mem_nhds hDy)).comp (0, y)
      (hD.contMDiffAt)).contDiffAt
  have hcdB : ContDiffAt ℝ Ctop (fun p : ℝ × (ℝ × EuclideanSpace ℝ (Fin 3)) =>
      chr c (D p.1 p.2.2)) (0, (u₀, y)) :=
    hfam.comp₂ (x := (0, (u₀, y))) (contDiffAt_fst (𝕜 := ℝ) (p := (0, (u₀, y))))
      ((contDiffAt_snd (𝕜 := ℝ) (p := (0, (u₀, y)))).snd)
  exact hcdA.sub hcdB

/-! ## 3. The compactness cover, with the diagonal of `M × M` in place of the norm -/

/-- **Upper semicontinuity of the loop-vs-chain meet set in a Hausdorff target.**  For `s → 0` every
meet point of `D s` is close to a meet point of `D 0`.  The vector-space proof
(`Work.Drive.eventually_meetBox_cover_noInterior`) takes the limit of the difference map; here the
target is a Hausdorff space, and the limit argument uses that the diagonal is closed: the two
components of the pair `(L p.1, D s p.2)` have a common limit, so the limit pair lies on the diagonal. -/
theorem eventually_meetBox_cover_diag {M : Type*} [TopologicalSpace M] [T2Space M]
    {L : ℝ → M} {D : ℝ → EuclideanSpace ℝ (Fin 3) → M}
    (hc : Continuous (fun q : ℝ × (ℝ × EuclideanSpace ℝ (Fin 3)) => (L q.2.1, D q.1 q.2.2)))
    {δ : meetBox L (D 0) → ℝ} (hδ : ∀ ξ, 0 < δ ξ) :
    ∀ᶠ s in nhds (0 : ℝ), ∀ p ∈ meetBox L (D s),
      ∃ ξ : meetBox L (D 0), ‖p - ξ.1‖ < δ ξ := by
  have hLc : Continuous (fun q : ℝ × (ℝ × EuclideanSpace ℝ (Fin 3)) => L q.2.1) :=
    continuous_fst.comp hc
  have hDc : Continuous (fun q : ℝ × (ℝ × EuclideanSpace ℝ (Fin 3)) => D q.1 q.2.2) :=
    continuous_snd.comp hc
  have key : ∃ ε > 0, ∀ s, |s| < ε → ∀ p ∈ meetBox L (D s),
      ∃ ξ : meetBox L (D 0), ‖p - ξ.1‖ < δ ξ := by
    by_contra hcon
    push Not at hcon
    have hseq : ∀ k : ℕ, ∃ s : ℝ, ∃ p : ℝ × EuclideanSpace ℝ (Fin 3),
        |s| < 1 / ((k : ℝ) + 1) ∧ p ∈ meetBox L (D s) ∧
        ∀ ξ : meetBox L (D 0), δ ξ ≤ ‖p - ξ.1‖ := by
      intro k
      obtain ⟨s, hs, p, hp, hfar⟩ := hcon (1 / ((k : ℝ) + 1)) (by positivity)
      exact ⟨s, p, hs, hp, hfar⟩
    choose s p hs hp hfar using hseq
    have hst : Tendsto s atTop (nhds (0 : ℝ)) := by
      refine squeeze_zero_norm' (a := fun k : ℕ => 1 / ((k : ℝ) + 1)) ?_
        tendsto_one_div_add_atTop_nhds_zero_nat
      exact Eventually.of_forall fun k => le_of_lt (hs k)
    have hpm : ∀ k, p k ∈ Set.Icc (0 : ℝ) 1 ×ˢ Submission.Drive.unitBox 2 := fun k => by
      obtain ⟨ht, hv, -⟩ := mem_meetBox.mp (hp k)
      exact ⟨ht, hv⟩
    obtain ⟨a, ha, φ, hφ, hpt⟩ :=
      (isCompact_Icc.prod (isCompact_unitBox 2)).tendsto_subseq hpm
    have hpair : Tendsto (fun k : ℕ => (s (φ k), p (φ k))) atTop (nhds ((0 : ℝ), a)) :=
      (hst.comp hφ.tendsto_atTop).prodMk_nhds hpt
    have h1 : Tendsto (fun k : ℕ => L (p (φ k)).1) atTop (nhds (L a.1)) :=
      (hLc.continuousAt (x := ((0 : ℝ), a))).tendsto.comp hpair
    have h2 : Tendsto (fun k : ℕ => D (s (φ k)) (p (φ k)).2) atTop (nhds (D 0 a.2)) :=
      (hDc.continuousAt (x := ((0 : ℝ), a))).tendsto.comp hpair
    have h3 : (fun k : ℕ => D (s (φ k)) (p (φ k)).2) = fun k : ℕ => L (p (φ k)).1 := by
      funext k
      exact (mem_meetBox.mp (hp (φ k))).2.2.symm
    have hLa : L a.1 = D 0 a.2 := tendsto_nhds_unique h1 (h3 ▸ h2)
    have hamem : a ∈ meetBox L (D 0) := ⟨ha.1, ha.2, hLa⟩
    have hfar' : ∀ k, δ ⟨a, hamem⟩ ≤ ‖p (φ k) - a‖ := fun k => by
      simpa using hfar (φ k) ⟨a, hamem⟩
    have hev : ∀ᶠ k in atTop, ‖p (φ k) - a‖ < δ ⟨a, hamem⟩ :=
      hpt.eventually (Metric.ball_mem_nhds a (hδ ⟨a, hamem⟩))
    obtain ⟨k, hk⟩ := hev.exists
    exact absurd hk (not_lt.mpr (hfar' k))
  obtain ⟨ε, hε, hval⟩ := key
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with s hs
  refine hval s ?_
  have : dist s 0 < ε := by simpa [Metric.mem_ball] using hs
  rwa [Real.dist_eq, sub_zero] at this

/-! ## 4. The chart-free engine: local solutions give local constancy of the geometric count -/

/-- **The number of distinct loop values at which a loop meets a `3`-chain is locally constant**, from
local solutions at the base meets, the loop being a `1`-periodic curve, the chain's box covering its
image, and the loop being injective modulo its period (`hinj`).

This is the manifold form of `Work.Drive.meetPt_ncard_eq_of_regular_embedded`: the implicit function
theorem and the transversality are isolated in the hypothesis `hloc`, so that the charting appears only
in `Work.Drive.meetPt_ncard_eq_of_regular_manifold` below. -/
theorem meetPt_ncard_eq_of_localSolutions {M : Type*} [TopologicalSpace M] [T2Space M]
    (L : ℝ → M) (D : ℝ → EuclideanSpace ℝ (Fin 3) → M)
    (hLc : Continuous L)
    (hDc : Continuous (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => D q.1 q.2))
    (hper : ∀ s : ℝ, L (s + 1) = L s)
    (hbox : ∀ (u : ℝ) (x : EuclideanSpace ℝ (Fin 3)),
      ∃ x' ∈ Submission.Drive.unitBox 2, D u x' = D u x)
    (hfin : (meetBox L (D 0)).Finite)
    (hloc : ∀ ξ : ↥(meetBox L (D 0)),
      ∃ (ε δ : ℝ) (ψ : ℝ → ℝ × EuclideanSpace ℝ (Fin 3)),
        0 < ε ∧ 0 < δ ∧ ψ 0 = ξ.1 ∧ Tendsto ψ (nhds (0 : ℝ)) (nhds ξ.1) ∧
        (∀ s, |s| < ε → ‖ψ s - ξ.1‖ < δ ∧ L (ψ s).1 = D s (ψ s).2) ∧
        (∀ s, |s| < ε → ∀ x, ‖x - ξ.1‖ < δ → L x.1 = D s x.2 → x = ψ s))
    (hinj : ∀ p : ℝ × EuclideanSpace ℝ (Fin 3), p ∈ meetBox L (D 0) →
      ∀ q : ℝ × EuclideanSpace ℝ (Fin 3), q ∈ meetBox L (D 0) →
      L p.1 = L q.1 → D 0 p.2 = D 0 q.2 →
      (∃ k : ℤ, q.1 = p.1 + (k : ℝ)) ∧ q.2 = p.2) :
    ∀ᶠ u in nhds (0 : ℝ),
      (Set.range (fun p : meetBox L (D u) => L p.1.1)).ncard =
        (Set.range (fun p : meetBox L (D 0) => L p.1.1)).ncard := by
  classical
  haveI : Finite ↥(meetBox L (D 0)) := hfin.to_subtype
  -- ## 1. the periodicity of `L` in integer form
  have hperP : Function.Periodic L 1 := hper
  have hperInt : ∀ (k : ℤ) (t : ℝ), L (t + (k : ℝ)) = L t := by
    intro k t
    simpa using hperP.int_mul k t
  have hLfract : ∀ t : ℝ, L (Int.fract t) = L t := by
    intro t
    have h := hperInt ⌊t⌋ (Int.fract t)
    have h2 : Int.fract t + ((⌊t⌋ : ℤ) : ℝ) = t := Int.fract_add_floor t
    rw [h2] at h
    exact h.symm
  choose ε₀ δ₀ ψ₀ hε₀ hδ₀ hψ₀ hcont₀ hmain₀ huniq₀ using hloc
  -- ## 2. the eventual properties of the family of branches
  have hEv1 : ∀ᶠ s in nhds (0 : ℝ), ∀ ξ : ↥(meetBox L (D 0)), |s| < ε₀ ξ := by
    rw [Filter.eventually_all]
    intro ξ
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (hε₀ ξ)] with s hs
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hs
    exact hs
  have hEv2 : ∀ᶠ s in nhds (0 : ℝ), ∀ p : ↥(meetBox L (D 0)) ×
      ↥(meetBox L (D 0)), ‖ψ₀ p.1 s - p.1.1‖ < min (δ₀ p.1) (δ₀ p.2) := by
    rw [Filter.eventually_all]
    intro p
    have hpos : 0 < min (δ₀ p.1) (δ₀ p.2) := lt_min (hδ₀ p.1) (hδ₀ p.2)
    filter_upwards [(hcont₀ p.1).eventually (Metric.ball_mem_nhds p.1.1 hpos)] with s hs
    simpa [dist_eq_norm] using hs
  have hEv3 : ∀ᶠ s in nhds (0 : ℝ), ∀ p : ↥(meetBox L (D 0)) ×
      ↥(meetBox L (D 0)),
      L p.1.1.1 ≠ L p.2.1.1 → L (ψ₀ p.1 s).1 ≠ L (ψ₀ p.2 s).1 := by
    rw [Filter.eventually_all]
    intro p
    by_cases hp : L p.1.1.1 = L p.2.1.1
    · exact Eventually.of_forall fun s h => absurd hp h
    · have hfst : Tendsto (fun s : ℝ => (ψ₀ p.1 s).1) (nhds (0 : ℝ)) (nhds p.1.1.1) :=
        (continuous_fst.continuousAt.tendsto).comp (hcont₀ p.1)
      have hsnd : Tendsto (fun s : ℝ => (ψ₀ p.2 s).1) (nhds (0 : ℝ)) (nhds p.2.1.1) :=
        (continuous_fst.continuousAt.tendsto).comp (hcont₀ p.2)
      have h1 : Tendsto (fun s : ℝ => L (ψ₀ p.1 s).1) (nhds (0 : ℝ)) (nhds (L p.1.1.1)) :=
        (hLc.continuousAt (x := p.1.1.1)).tendsto.comp hfst
      have h2 : Tendsto (fun s : ℝ => L (ψ₀ p.2 s).1) (nhds (0 : ℝ)) (nhds (L p.2.1.1)) :=
        (hLc.continuousAt (x := p.2.1.1)).tendsto.comp hsnd
      have hpair : Tendsto (fun s : ℝ => (L (ψ₀ p.1 s).1, L (ψ₀ p.2 s).1)) (nhds (0 : ℝ))
          (nhds (L p.1.1.1, L p.2.1.1)) := h1.prodMk_nhds h2
      have hopen : {q : M × M | q.1 ≠ q.2} ∈ nhds (L p.1.1.1, L p.2.1.1) :=
        (isClosed_diagonal.isOpen_compl).mem_nhds (by simpa using hp)
      filter_upwards [hpair.eventually hopen] with s hs
      exact fun _ => hs
  -- ## 3. the compactness cover
  have hc : Continuous
      (fun q : ℝ × (ℝ × EuclideanSpace ℝ (Fin 3)) => (L q.2.1, D q.1 q.2.2)) :=
    (hLc.comp (continuous_fst.comp continuous_snd)).prodMk
      (hDc.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
  have hcover : ∀ᶠ s in nhds (0 : ℝ), ∀ p ∈ meetBox L (D s),
      ∃ ξ : ↥(meetBox L (D 0)), ‖p - ξ.1‖ < δ₀ ξ / 2 :=
    eventually_meetBox_cover_diag hc (fun ξ => by linarith [hδ₀ ξ])
  -- ## 4. the assembly
  filter_upwards [hEv1, hEv2, hEv3, hcover] with s hs1 hs2 hs3 hscover
  have hrange : Set.range (fun p : ↥(meetBox L (D s)) => L p.1.1) =
      Set.range (fun ξ : ↥(meetBox L (D 0)) => L (ψ₀ ξ s).1) := by
    ext v
    constructor
    · rintro ⟨p, rfl⟩
      obtain ⟨ξ, hξ⟩ := hscover p.1 p.2
      have hp : p.1 = ψ₀ ξ s := huniq₀ ξ s (hs1 ξ) p.1
        (lt_of_lt_of_le hξ (by linarith [hδ₀ ξ]))
        ((mem_meetBox.mp p.2).2.2)
      exact ⟨ξ, by show L (ψ₀ ξ s).1 = L p.1.1; rw [← hp]⟩
    · rintro ⟨ξ, rfl⟩
      obtain ⟨x', hx'mem, hx'⟩ := hbox s (ψ₀ ξ s).2
      have hmeet : L (ψ₀ ξ s).1 = D s (ψ₀ ξ s).2 := (hmain₀ ξ s (hs1 ξ)).2
      refine ⟨⟨(Int.fract (ψ₀ ξ s).1, x'), ?_⟩, hLfract (ψ₀ ξ s).1⟩
      rw [mem_meetBox]
      exact ⟨⟨Int.fract_nonneg _, le_of_lt (Int.fract_lt_one _)⟩, hx'mem,
        (hLfract (ψ₀ ξ s).1).trans (hmeet.trans hx'.symm)⟩
  have hfib : ∀ ξ η : ↥(meetBox L (D 0)),
      (L (ψ₀ ξ s).1 = L (ψ₀ η s).1 ↔ L ξ.1.1 = L η.1.1) := by
    intro ξ η
    constructor
    · intro h
      by_contra hne
      exact hs3 (ξ, η) hne h
    · intro h
      have hD0 : D 0 ξ.1.2 = D 0 η.1.2 := by
        rw [← (mem_meetBox.mp ξ.2).2.2, h, (mem_meetBox.mp η.2).2.2]
      obtain ⟨⟨k, hk⟩, hx2⟩ := hinj ξ.1 ξ.2 η.1 η.2 h hD0
      have hnorm : ψ₀ ξ s + ((k : ℝ), (0 : EuclideanSpace ℝ (Fin 3))) - η.1 = ψ₀ ξ s - ξ.1 := by
        ext <;> simp [hk, hx2] <;> ring
      have hsol : L (ψ₀ ξ s + ((k : ℝ), (0 : EuclideanSpace ℝ (Fin 3)))).1 =
          D s (ψ₀ ξ s + ((k : ℝ), (0 : EuclideanSpace ℝ (Fin 3)))).2 := by
        have e1 : (ψ₀ ξ s + ((k : ℝ), (0 : EuclideanSpace ℝ (Fin 3)))).1
            = (ψ₀ ξ s).1 + (k : ℝ) := rfl
        have e2 : (ψ₀ ξ s + ((k : ℝ), (0 : EuclideanSpace ℝ (Fin 3)))).2 = (ψ₀ ξ s).2 := by simp
        rw [e1, e2, hperInt k (ψ₀ ξ s).1]
        exact (hmain₀ ξ s (hs1 ξ)).2
      have hshift : ψ₀ ξ s + ((k : ℝ), (0 : EuclideanSpace ℝ (Fin 3))) = ψ₀ η s :=
        huniq₀ η s (hs1 η) _ (by rw [hnorm]; exact lt_of_lt_of_le (hs2 (ξ, η)) (min_le_right _ _))
          hsol
      have hval : L (ψ₀ η s).1 = L (ψ₀ ξ s).1 := by
        rw [← hshift]
        show L (ψ₀ ξ s + ((k : ℝ), (0 : EuclideanSpace ℝ (Fin 3)))).1 = L (ψ₀ ξ s).1
        rw [show (ψ₀ ξ s + ((k : ℝ), (0 : EuclideanSpace ℝ (Fin 3)))).1 =
          (ψ₀ ξ s).1 + (k : ℝ) from rfl, hperInt k (ψ₀ ξ s).1]
      exact hval.symm
  rw [hrange]
  exact ncard_range_eq_of_fiber (fun ξ η => hfib ξ η)

/-! ## 5. The assembly: the geometric count is locally constant at a regular configuration -/

/-- **The locality (`hn4`) of the geometric count, in the manifold setting.**  A smooth `1`-periodic
loop and a smooth family of `3`-chains in a charted `4`-manifold, whose meets at the base parameter are
transverse and finitely many and whose loop is injective modulo its period, have the same number of
distinct meet points for nearby parameters. -/
theorem meetPt_ncard_eq_of_regular_manifold {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]
    (L : ℝ → M) (D : ℝ → EuclideanSpace ℝ (Fin 3) → M)
    (hL : ContMDiff (𝓘(ℝ,ℝ)) (𝓡 4) Ctop L)
    (hLc : Continuous L)
    (hDc : Continuous (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => D q.1 q.2))
    (hD : ContMDiff (𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 3))) (𝓡 4) Ctop
      (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => D q.1 q.2))
    (hper : ∀ s : ℝ, L (s + 1) = L s)
    (hbox : ∀ (u : ℝ) (x : EuclideanSpace ℝ (Fin 3)),
      ∃ x' ∈ Submission.Drive.unitBox 2, D u x' = D u x)
    (hfin : (meetBox L (D 0)).Finite)
    (htrans : ∀ p : ℝ × EuclideanSpace ℝ (Fin 3), p ∈ meetBox L (D 0) →
      LinearMap.range (mfderiv (𝓘(ℝ,ℝ)) (𝓡 4) L p.1).toLinearMap ⊔
      LinearMap.range (mfderiv (𝓡 3) (𝓡 4) (D 0) p.2).toLinearMap = ⊤)
    (hinj : ∀ p : ℝ × EuclideanSpace ℝ (Fin 3), p ∈ meetBox L (D 0) →
      ∀ q : ℝ × EuclideanSpace ℝ (Fin 3), q ∈ meetBox L (D 0) →
      L p.1 = L q.1 → D 0 p.2 = D 0 q.2 →
      (∃ k : ℤ, q.1 = p.1 + (k : ℝ)) ∧ q.2 = p.2) :
    ∀ᶠ u in nhds (0 : ℝ),
      (Set.range (fun p : meetBox L (D u) => L p.1.1)).ncard =
        (Set.range (fun p : meetBox L (D 0) => L p.1.1)).ncard := by
  classical
  refine meetPt_ncard_eq_of_localSolutions L D hLc hDc hper hbox hfin ?_ hinj
  intro ξ
  have heq : L ξ.1.1 = D 0 ξ.1.2 := (mem_meetBox.mp ξ.2).2.2
  have hsrcL : L ξ.1.1 ∈ (chr (L ξ.1.1)).source := mem_chart_source _ _
  have hsN : D 0 ξ.1.2 ∈ (chr (L ξ.1.1)).source := by
    rw [← heq]; exact mem_chart_source _ _
  have hsurj := chartedDiff_surjective_of_transverse L D hL hD heq (htrans ξ.1 ξ.2)
  have hsmooth := contDiffAt_chartDiff_fam_real L D hL hD hsrcL hsN
  have hdim : Module.finrank ℝ (ℝ × EuclideanSpace ℝ (Fin 3)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) := by
    rw [finrank_prod_fin3, finrank_euclideanSpace_fin]
  obtain ⟨ε, δ, ψ, hε, hδ, hψ0, hψcont, hmain, huniq⟩ :=
    exists_local_solution_of_surjective_at
      (fun s x => chr (L ξ.1.1) (L x.1) - chr (L ξ.1.1) (D s x.2)) hsmooth hdim
      (by simp [heq]) hsurj
  -- the two values stay in the chart's source near `s = 0`
  have hcontA : Tendsto (fun s : ℝ => L (ψ s).1) (nhds (0 : ℝ)) (nhds (L ξ.1.1)) :=
    (hLc.continuousAt (x := ξ.1.1)).tendsto.comp ((continuous_fst.tendsto ξ.1).comp hψcont)
  have hcontB : Tendsto (fun s : ℝ => D s (ψ s).2) (nhds (0 : ℝ)) (nhds (D 0 ξ.1.2)) :=
    (hDc.continuousAt (x := ((0 : ℝ), ξ.1.2))).tendsto.comp
      (tendsto_id.prodMk_nhds ((continuous_snd.tendsto ξ.1).comp hψcont))
  have hevL : ∀ᶠ s in nhds (0 : ℝ), L (ψ s).1 ∈ (chr (L ξ.1.1)).source :=
    hcontA.eventually ((chr (L ξ.1.1)).open_source.mem_nhds hsrcL)
  have hevB : ∀ᶠ s in nhds (0 : ℝ), D s (ψ s).2 ∈ (chr (L ξ.1.1)).source :=
    hcontB.eventually ((chr (L ξ.1.1)).open_source.mem_nhds hsN)
  obtain ⟨ε', hε'pos, hε'⟩ := Metric.mem_nhds_iff.mp (hevL.and hevB)
  refine ⟨min ε ε', δ, ψ, lt_min hε hε'pos, hδ, hψ0, hψcont, ?_, ?_⟩
  · intro s hs
    have hsε : |s| < ε := lt_of_lt_of_le hs (min_le_left _ _)
    have hsε' : |s| < ε' := lt_of_lt_of_le hs (min_le_right _ _)
    obtain ⟨hsmemL, hsmemD⟩ := hε' (by simpa [Real.dist_eq, sub_zero] using hsε')
    refine ⟨(hmain s hsε).1, ?_⟩
    have hz : chr (L ξ.1.1) (L (ψ s).1) = chr (L ξ.1.1) (D s (ψ s).2) :=
      sub_eq_zero.mp (hmain s hsε).2
    exact (chr (L ξ.1.1)).injOn hsmemL hsmemD hz
  · intro s hs x hx hx0
    have hsε : |s| < ε := lt_of_lt_of_le hs (min_le_left _ _)
    exact huniq s hsε x hx (by rw [hx0]; exact sub_self _)

end

end Work.Drive
