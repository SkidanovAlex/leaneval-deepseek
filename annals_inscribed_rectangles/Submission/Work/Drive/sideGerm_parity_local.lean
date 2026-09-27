import Mathlib
import Submission.Work.Drive.meetBoxEngine
import Submission.Work.Drive.geometricLocality
import Submission.Work.Drive.eventually_ncard_meetBox_eq_fam
import Submission.Work.Drive.sideGermDefs
import Submission.Work.Drive.chainLocalityDesign
import Submission.Work.Drive.parityFamDefs

/-!
# The local constancy of the germ count's parity at a good configuration

`Work.Drive.sideGerm` is the germ of the parity of the loop-vs-sweep count `coreSideCount` over small
chart perturbations `Ξ` of a chart `Q` of the capped plane.  This file proves the *transfer* input of
the germ route: at a *good* configuration (a parameter at which the perturbed pair is a `GoodPair`) the
parity of the count is locally constant in the configuration parameters.

The mathematical content is the local constancy of the number of *parameter* meets of a loop against a
`3`-chain in a `4`-manifold, along a family in which both curves move.  The two ingredients are

* the implicit function theorem at each base meet, applied to the *charted* difference map
  (`Work.Drive.exists_local_solution_of_surjective_par_at`, a general-parameter variant of the
  workspace's IFT with only *local* smoothness, which is what a chart allows), and
* the chart-free compactness cover of the parameter box
  (`Work.Drive.eventually_meetBox_cover_par_diag`, the manifold version of
  `Work.Drive.eventually_meetBox_cover_par`).

Together they say that near a good configuration the meet set is exactly the image of the base meet set
under the local branches `ψ_ξ`, hence has the same cardinality — in particular the same parity.
-/

namespace Work.Drive

open Filter Manifold
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

noncomputable section

/-! ## The implicit function theorem with a general parameter space and local smoothness -/

/-- **The local solution of a regular family, with a general parameter space and smoothness only at
the base point.**  This is `Work.Drive.exists_local_solution_of_surjective_par` with the *global*
smoothness hypothesis `ContDiff ℝ Ctop (fun p => G p.1 p.2)` weakened to
`ContDiffAt ℝ Ctop (fun p => G p.1 p.2) (0, ξ)`, which is what a *charted* difference map provides: the
chart is junk outside its source, so the system is only smooth near the base meet.

The proof is that of `Work.Drive.exists_local_solution_of_surjective_at` with `ℝ` replaced by the
general finite-dimensional parameter space `P`: the smoothness is used in a single place (the strict
differentiability of `R (s,x) = (s, G s x)`), and `ContDiffAt.hasStrictFDerivAt` supplies it there. -/
theorem exists_local_solution_of_surjective_par_at {P F E : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (G : P → F → E) {ξ : F}
    (hG : ContDiffAt ℝ Ctop (fun p : P × F => G p.1 p.2) (0, ξ))
    (hdim : Module.finrank ℝ F = Module.finrank ℝ E) (hξ0 : G 0 ξ = 0)
    (hsurj : Function.Surjective (fderiv ℝ (G 0) ξ)) :
    ∃ (ε δ : ℝ) (ψ : P → F), 0 < ε ∧ 0 < δ ∧ ψ 0 = ξ ∧
      Filter.Tendsto ψ (nhds (0 : P)) (nhds ξ) ∧
      (∀ s, ‖s‖ < ε → ‖ψ s - ξ‖ < δ ∧ G s (ψ s) = 0) ∧
      (∀ s, ‖s‖ < ε → ∀ x, ‖x - ξ‖ < δ → G s x = 0 → x = ψ s) := by
  classical
  have hne : Ctop ≠ 0 := by decide
  set uG : P × F → E := fun p => G p.1 p.2 with huG
  have hucd : ContDiffAt ℝ Ctop uG (0, ξ) := hG
  have huat : HasFDerivAt uG (fderiv ℝ uG (0, ξ)) (0, ξ) :=
    (hucd.differentiableAt hne).hasFDerivAt
  set dG : F →L[ℝ] E := fderiv ℝ (G 0) ξ with hdG
  have happ : ∀ w : F, fderiv ℝ uG (0, ξ) (0, w) = dG w := by
    intro w
    have h := congrArg (fun (T : F →L[ℝ] E) => T w) (fderiv_uncurry_snd_par huat).symm
    simpa [huG, hdG, ContinuousLinearMap.inr_apply] using h
  -- surjective + equal dimensions ⟹ bijective
  have hdGinj : Function.Injective dG :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := dG.toLinearMap) hdim).mpr hsurj
  -- the derivative `L` of `R (s,x) = (s, uG (s,x))`
  set L : P × F →L[ℝ] P × E :=
    (ContinuousLinearMap.fst ℝ P F).prod (fderiv ℝ uG (0, ξ)) with hL
  have hLc : ∀ p : P × F, L p = (p.1, fderiv ℝ uG (0, ξ) p) := fun p => rfl
  have hLsurj : Function.Surjective L := by
    rintro ⟨b, y⟩
    obtain ⟨v, hv⟩ := hsurj (y - fderiv ℝ uG (0, ξ) (b, (0 : F)))
    refine ⟨(b, v), ?_⟩
    rw [hLc]
    refine Prod.ext rfl ?_
    have hsplit : (b, v) = (b, (0 : F)) + (0, v) := by ext <;> simp
    rw [hsplit, map_add, happ, hv]
    abel
  have hdim2 : Module.finrank ℝ (P × F) = Module.finrank ℝ (P × E) := by
    rw [Module.finrank_prod, Module.finrank_prod, hdim]
  have hLinj : Function.Injective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (L : P × F →ₗ[ℝ] P × E)) hdim2).mpr hLsurj
  have hbij : Function.Bijective (L : P × F →ₗ[ℝ] P × E) := ⟨hLinj, hLsurj⟩
  let e := (LinearEquiv.ofBijective (L : P × F →ₗ[ℝ] P × E) hbij).toContinuousLinearEquiv
  have he : (e : P × F →L[ℝ] P × E) = L := by
    apply ContinuousLinearMap.ext; intro x; rfl
  -- the map `R` and its strict derivative
  set R : P × F → P × E := fun p => (p.1, uG p) with hRdef
  have hRfd : HasFDerivAt R L (0, ξ) := hasFDerivAt_fst.prodMk huat
  have hRcd : ContDiffAt ℝ Ctop R (0, ξ) := by
    rw [hRdef]
    exact contDiffAt_fst.prodMk hucd
  have hst : HasStrictFDerivAt R (e : P × F →L[ℝ] P × E) (0, ξ) := by
    rw [he, ← hRfd.fderiv]
    exact hRcd.hasStrictFDerivAt hne
  let Φ : OpenPartialHomeomorph (P × F) (P × E) := HasStrictFDerivAt.toOpenPartialHomeomorph R hst
  have hΦcoe : (Φ : P × F → P × E) = R := HasStrictFDerivAt.toOpenPartialHomeomorph_coe hst
  have hsrc : (0, ξ) ∈ Φ.source := HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source hst
  have hR0 : R (0, ξ) = ((0 : P), (0 : E)) := by simp [hRdef, huG, hξ0]
  have htgt : R (0, ξ) ∈ Φ.target :=
    HasStrictFDerivAt.image_mem_toOpenPartialHomeomorph_target hst
  have htgt0 : (((0 : P), (0 : E)) : P × E) ∈ Φ.target := by rwa [← hR0]
  obtain ⟨r_src, hr_src, hr_src'⟩ := Metric.mem_nhds_iff.mp (Φ.open_source.mem_nhds hsrc)
  have htgt_nhds : ∀ᶠ s in nhds (0 : P), ((s, (0 : E)) : P × E) ∈ Φ.target :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
      (Φ.open_target.mem_nhds htgt0)
  obtain ⟨r_tgt, hr_tgt, hr_tgt'⟩ := Metric.mem_nhds_iff.mp htgt_nhds
  have hsymm0 : Φ.symm (((0 : P), (0 : E)) : P × E) = (0, ξ) := by
    have h := Φ.left_inv hsrc
    rw [hΦcoe, hR0] at h
    exact h
  set ψ : P → F := fun s => (Φ.symm ((s, (0 : E)) : P × E)).2 with hψ
  have hψ0 : ψ 0 = ξ := by simp [hψ, hsymm0]
  have hψcont : Filter.Tendsto ψ (nhds (0 : P)) (nhds ξ) := by
    have hs : Filter.Tendsto (fun s : P => Φ.symm ((s, (0 : E)) : P × E)) (nhds (0 : P))
        (nhds (Φ.symm (((0 : P), (0 : E)) : P × E))) :=
      (Φ.continuousAt_symm htgt0).tendsto.comp
        (continuous_id.prodMk continuous_const).continuousAt.tendsto
    rw [hsymm0] at hs
    exact (continuous_snd.continuousAt.tendsto).comp hs
  obtain ⟨r_ψ, hr_ψ, hr_ψ'⟩ := Metric.mem_nhds_iff.mp
    (hψcont.eventually (Metric.ball_mem_nhds ξ hr_src))
  refine ⟨min r_tgt (min r_src r_ψ), r_src, ψ, lt_min hr_tgt (lt_min hr_src hr_ψ), hr_src,
    hψ0, hψcont, ?_, ?_⟩
  · intro s hs
    have hs_tgt : ‖s‖ < r_tgt := lt_of_lt_of_le hs (min_le_left _ _)
    have hs_ψ : ‖s‖ < r_ψ := lt_of_lt_of_le hs (le_trans (min_le_right _ _) (min_le_right _ _))
    have hd_tgt : dist s (0 : P) < r_tgt := by simpa [dist_eq_norm, sub_zero] using hs_tgt
    have hmem_tgt : ((s, (0 : E)) : P × E) ∈ Φ.target := hr_tgt' hd_tgt
    have hRsol : R (Φ.symm ((s, (0 : E)) : P × E)) = ((s, (0 : E)) : P × E) := by
      rw [← hΦcoe]; exact Φ.right_inv hmem_tgt
    have h1 : (Φ.symm ((s, (0 : E)) : P × E)).1 = s := by
      have := congrArg (fun z : P × E => z.1) hRsol
      simpa [hRdef] using this
    have h2 : uG (Φ.symm ((s, (0 : E)) : P × E)) = 0 := by
      have := congrArg (fun z : P × E => z.2) hRsol
      simpa [hRdef] using this
    have hnorm : ‖ψ s - ξ‖ < r_src := by
      have hs_ψ' : dist s (0 : P) < r_ψ := by simpa [dist_eq_norm, sub_zero] using hs_ψ
      have hm := hr_ψ' hs_ψ'
      simpa [Set.mem_ofPred_eq, dist_eq_norm] using hm
    refine ⟨hnorm, ?_⟩
    have hun : G s (ψ s) = uG (Φ.symm ((s, (0 : E)) : P × E)) := by
      simp [huG, hψ, h1]
    rw [hun]; exact h2
  · intro s hs x hx hx0
    have hs_src : ‖s‖ < r_src :=
      lt_of_lt_of_le hs (le_trans (min_le_right _ _) (min_le_left _ _))
    have hs_src' : dist s (0 : P) < r_src := by simpa [dist_eq_norm, sub_zero] using hs_src
    have hball : ((s, x) : P × F) ∈ Metric.ball ((0, ξ) : P × F) r_src := by
      rw [Metric.mem_ball, Prod.dist_eq]
      exact max_lt hs_src' (by rw [dist_eq_norm]; exact hx)
    have hinsrc : (s, x) ∈ Φ.source := hr_src' hball
    have hΦsx : Φ (s, x) = ((s, (0 : E)) : P × E) := by
      rw [hΦcoe]
      have hRt : R (s, x) = (s, G s x) := by simp [hRdef, huG]
      rw [hRt, hx0]
    have hleft := Φ.left_inv hinsrc
    rw [hΦsx] at hleft
    have hfin : (Φ.symm ((s, (0 : E)) : P × E)).2 = x := by
      have := congrArg (fun z : P × F => z.2) hleft
      simpa using this
    exact hfin.symm

/-! ## The charted difference map and its smoothness -/

/-- The chart `chr p` is `C^∞` on its source. -/
lemma contMDiffOn_chr {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M] (p : M) :
    ContMDiffOn (𝓡 4) (𝓡 4) Ctop (chr p) (chr p).source := by
  have h := contMDiffOn_extChartAt (I := 𝓡 4) (x := p) (n := Ctop)
  simpa [chr] using h

/-- **A charted smooth map is smooth where its value lies in the chart's source.**  This is the shape in
which the chart enters the implicit function theorem: the system is only smooth near the meet. -/
lemma contDiffAt_chr_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]
    (f : E → M) (hf : ContMDiff (𝓘(ℝ, E)) (𝓡 4) Ctop f) (p : M) (q₀ : E)
    (hreg : f q₀ ∈ (chr p).source) :
    ContDiffAt ℝ Ctop (fun q => (chr p) (f q)) q₀ := by
  have h1 : ContMDiffAt (𝓡 4) (𝓡 4) Ctop (chr p) (f q₀) :=
    (contMDiffOn_chr p).contMDiffAt ((chr p).open_source.mem_nhds hreg)
  exact contMDiffAt_iff_contDiffAt.mp (h1.comp q₀ hf.contMDiffAt)

/-! ## The compactness cover of the box, for a general family parameter -/

/-- **Upper semicontinuity of the loop-vs-chain meet set in a Hausdorff target, with a general family
parameter.**  For `s → 0` every meet point of the family at `s` is close to a meet point of the family
at `0`.

This is `Work.Drive.eventually_meetBox_cover_diag` with `ℝ` replaced by a general normed parameter
space `P`: the proof is the same diagonal/compactness argument (the box is compact, the diagonal of the
Hausdorff target `M × M` is closed), and only the *upper* semicontinuity direction uses the
compactness, so it is dimension-independent. -/
theorem eventually_meetBox_cover_par_diag {P M : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [TopologicalSpace M] [T2Space M] {L : P → ℝ → M} {D : P → EuclideanSpace ℝ (Fin 3) → M}
    (hc : Continuous (fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) => (L q.1 q.2.1, D q.1 q.2.2)))
    {δ : meetBox (L 0) (D 0) → ℝ} (hδ : ∀ ξ, 0 < δ ξ) :
    ∀ᶠ s in nhds (0 : P), ∀ p ∈ meetBox (L s) (D s),
      ∃ ξ : meetBox (L 0) (D 0), ‖p - ξ.1‖ < δ ξ := by
  have hLc : Continuous (fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) => L q.1 q.2.1) :=
    continuous_fst.comp hc
  have hDc : Continuous (fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) => D q.1 q.2.2) :=
    continuous_snd.comp hc
  have key : ∃ ε > 0, ∀ s, ‖s‖ < ε → ∀ p ∈ meetBox (L s) (D s),
      ∃ ξ : meetBox (L 0) (D 0), ‖p - ξ.1‖ < δ ξ := by
    by_contra hcon
    push Not at hcon
    have hseq : ∀ k : ℕ, ∃ s : P, ∃ p : ℝ × EuclideanSpace ℝ (Fin 3),
        ‖s‖ < 1 / ((k : ℝ) + 1) ∧ p ∈ meetBox (L s) (D s) ∧
        ∀ ξ : meetBox (L 0) (D 0), δ ξ ≤ ‖p - ξ.1‖ := by
      intro k
      obtain ⟨s, hs, p, hp, hfar⟩ := hcon (1 / ((k : ℝ) + 1)) (by positivity)
      exact ⟨s, p, hs, hp, hfar⟩
    choose s p hs hp hfar using hseq
    have hst : Tendsto s atTop (nhds (0 : P)) :=
      squeeze_zero_norm' (Eventually.of_forall fun k => le_of_lt (hs k))
        tendsto_one_div_add_atTop_nhds_zero_nat
    have hpm : ∀ k, p k ∈ Set.Icc (0 : ℝ) 1 ×ˢ Submission.Drive.unitBox 2 := fun k => by
      obtain ⟨ht, hv, -⟩ := mem_meetBox.mp (hp k)
      exact ⟨ht, hv⟩
    obtain ⟨a, ha, φ, hφ, hpt⟩ :=
      (isCompact_Icc.prod (isCompact_unitBox 2)).tendsto_subseq hpm
    have hpair : Tendsto (fun k : ℕ => (s (φ k), p (φ k))) atTop (nhds ((0 : P), a)) :=
      (hst.comp hφ.tendsto_atTop).prodMk_nhds hpt
    have h1 : Tendsto (fun k : ℕ => L (s (φ k)) (p (φ k)).1) atTop (nhds (L 0 a.1)) :=
      (hLc.continuousAt (x := ((0 : P), a))).tendsto.comp hpair
    have h2 : Tendsto (fun k : ℕ => D (s (φ k)) (p (φ k)).2) atTop (nhds (D 0 a.2)) :=
      (hDc.continuousAt (x := ((0 : P), a))).tendsto.comp hpair
    have h3 : (fun k : ℕ => D (s (φ k)) (p (φ k)).2)
        = fun k : ℕ => L (s (φ k)) (p (φ k)).1 := by
      funext k
      exact (mem_meetBox.mp (hp (φ k))).2.2.symm
    have hLa : L 0 a.1 = D 0 a.2 := tendsto_nhds_unique h1 (h3 ▸ h2)
    have hamem : a ∈ meetBox (L 0) (D 0) := ⟨ha.1, ha.2, hLa⟩
    have hfar' : ∀ k, δ ⟨a, hamem⟩ ≤ ‖p (φ k) - a‖ := fun k => by
      simpa using hfar (φ k) ⟨a, hamem⟩
    have hev : ∀ᶠ k in atTop, ‖p (φ k) - a‖ < δ ⟨a, hamem⟩ :=
      hpt.eventually (Metric.ball_mem_nhds a (hδ ⟨a, hamem⟩))
    obtain ⟨k, hk⟩ := hev.exists
    exact absurd hk (not_lt.mpr (hfar' k))
  obtain ⟨ε, hε, hval⟩ := key
  filter_upwards [Metric.ball_mem_nhds (0 : P) hε] with s hs
  refine hval s ?_
  have : dist s 0 < ε := by simpa [Metric.mem_ball] using hs
  rwa [dist_eq_norm, sub_zero] at this

/-! ## The local constancy engine for the parameter meet count in a `4`-manifold -/

/-- **The local constancy of the number of parameter meets of a loop against a `3`-chain in a
`4`-manifold**, along a family in which *both* curves move with the parameter `u : P`.

This is the manifold form of `Work.Drive.eventually_ncard_meetBox_eq_par`, for a *chart* whose source
cannot cover the box: the implicit function theorem is therefore applied *in a chart centred at each
base meet* (`Work.Drive.exists_local_solution_of_surjective_par_at` fed by the charted difference map
and the transversality `Work.Drive.chartedDiff_surjective_of_transverse`), while the cover of the box by
the balls around the base meets is chart-free
(`Work.Drive.eventually_meetBox_cover_par_diag`).

The hypotheses are: joint `C^∞` of both curve families (as maps of the *manifold*), finiteness of the
base meet set, interiority of the base meets in the box, and intrinsic transversality at them. -/
theorem eventually_ncard_meetBox_eq_manifold {P M : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]
    (L : P → ℝ → M) (D : P → EuclideanSpace ℝ (Fin 3) → M)
    (hL : ContMDiff (𝓘(ℝ, P × ℝ)) (𝓡 4) Ctop (fun q : P × ℝ => L q.1 q.2))
    (hD : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 3))) (𝓡 4) Ctop
      (fun q : P × EuclideanSpace ℝ (Fin 3) => D q.1 q.2))
    (hfin : (meetBox (L 0) (D 0)).Finite)
    (hint : ∀ p ∈ meetBox (L 0) (D 0), p.1 ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ i : Fin 3, p.2 i ∈ Set.Ioo (0 : ℝ) 1)
    (htrans : ∀ p ∈ meetBox (L 0) (D 0),
      LinearMap.range (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) (L 0) p.1).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4) (D 0) p.2).toLinearMap = ⊤) :
    ∀ᶠ u in nhds (0 : P), (meetBox (L u) (D u)).ncard = (meetBox (L 0) (D 0)).ncard := by
  classical
  haveI : Fintype ↥(meetBox (L 0) (D 0)) := hfin.fintype
  -- ## 1. the two base curves are smooth
  have hL0 : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 4) Ctop (L 0) := by
    have h : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, P × ℝ)) Ctop (fun t : ℝ => ((0 : P), t)) :=
      contMDiff_iff_contDiff.mpr (by fun_prop)
    exact hL.comp h
  have hD0 : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (𝓡 4) Ctop (D 0) := by
    have h : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 3))) Ctop
        (fun x : EuclideanSpace ℝ (Fin 3) => ((0 : P), x)) :=
      contMDiff_iff_contDiff.mpr (by fun_prop)
    exact hD.comp h
  -- ## 2. the local solution at each base meet, in the chart at the meet's value
  have hloc : ∀ ξ : ↥(meetBox (L 0) (D 0)),
      ∃ (ε δ : ℝ) (ψ : P → ℝ × EuclideanSpace ℝ (Fin 3)), 0 < ε ∧ 0 < δ ∧ ψ 0 = ξ.1 ∧
        Tendsto ψ (nhds (0 : P)) (nhds ξ.1) ∧
        (∀ u, ‖u‖ < ε → ‖ψ u - ξ.1‖ < δ ∧
          L u (ψ u).1 ∈ (chr (L 0 ξ.1.1)).source ∧ D u (ψ u).2 ∈ (chr (L 0 ξ.1.1)).source ∧
          L u (ψ u).1 = D u (ψ u).2) ∧
        (∀ u, ‖u‖ < ε → ∀ x, ‖x - ξ.1‖ < δ → L u x.1 = D u x.2 → x = ψ u) := by
    intro ξ
    obtain ⟨hξ1, hξ2, hξeq⟩ := mem_meetBox.mp ξ.2
    -- the surjectivity of the charted derivative of the base system
    have hDconst : ContMDiff (𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 3))) (𝓡 4) Ctop
        (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => D 0 q.2) :=
      hD0.comp (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin 3))).contMDiff
    have hsurj := chartedDiff_surjective_of_transverse (M := M) (L 0) (fun _ : ℝ => D 0)
      hL0 hDconst hξeq (htrans ξ.1 ξ.2)
    -- the charted difference system is smooth at the base meet
    have hsmA : ContMDiff (𝓘(ℝ, P × (ℝ × EuclideanSpace ℝ (Fin 3)))) (𝓡 4) Ctop
        (fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) => L q.1 q.2.1) := by
      have hpair : ContMDiff (𝓘(ℝ, P × (ℝ × EuclideanSpace ℝ (Fin 3)))) (𝓘(ℝ, P × ℝ)) Ctop
          (fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) => (q.1, q.2.1)) :=
        contMDiff_iff_contDiff.mpr (by fun_prop)
      exact hL.comp hpair
    have hsmB : ContMDiff (𝓘(ℝ, P × (ℝ × EuclideanSpace ℝ (Fin 3)))) (𝓡 4) Ctop
        (fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) => D q.1 q.2.2) := by
      have hpair : ContMDiff (𝓘(ℝ, P × (ℝ × EuclideanSpace ℝ (Fin 3))))
          (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 3))) Ctop
          (fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) => (q.1, q.2.2)) :=
        contMDiff_iff_contDiff.mpr (by fun_prop)
      exact hD.comp hpair
    have hregA : L 0 ξ.1.1 ∈ (chr (L 0 ξ.1.1)).source := mem_chart_source _ _
    have hregB : D 0 ξ.1.2 ∈ (chr (L 0 ξ.1.1)).source := by
      rw [← hξeq]; exact mem_chart_source _ _
    have hChartSm : ContDiffAt ℝ Ctop
        (fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) =>
          chr (L 0 ξ.1.1) (L q.1 q.2.1) - chr (L 0 ξ.1.1) (D q.1 q.2.2)) (0, ξ.1) := by
      have hA := contDiffAt_chr_comp (f := fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) =>
          L q.1 q.2.1) hsmA (L 0 ξ.1.1) (0, ξ.1) hregA
      have hB := contDiffAt_chr_comp (f := fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) =>
          D q.1 q.2.2) hsmB (L 0 ξ.1.1) (0, ξ.1) hregB
      exact hA.sub hB
    have hξ0 : (fun p : ℝ × EuclideanSpace ℝ (Fin 3) =>
          chr (L 0 ξ.1.1) (L 0 p.1) - chr (L 0 ξ.1.1) (D 0 p.2)) ξ.1 = 0 := by
      simp only [hξeq, sub_self]
    obtain ⟨ε₁, δ, ψ, hε₁, hδ, hψ0, hψcont, hmain, huniq⟩ :=
      exists_local_solution_of_surjective_par_at (P := P)
        (fun u (p : ℝ × EuclideanSpace ℝ (Fin 3)) =>
          chr (L 0 ξ.1.1) (L u p.1) - chr (L 0 ξ.1.1) (D u p.2))
        hChartSm (by rw [finrank_prod_fin3, finrank_euclideanSpace_fin]) hξ0 hsurj
    -- the values at the branch stay in the chart's source
    have hfst1 : Continuous (fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) => q.1) := continuous_fst
    have hsnd1 : Continuous (fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) => q.2.1) :=
      continuous_fst.comp continuous_snd
    have hsnd2 : Continuous (fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) => q.2.2) :=
      continuous_snd.comp continuous_snd
    have hLAt : ContinuousAt (fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) => L q.1 q.2.1)
        ((0 : P), ξ.1) := (hL.continuous.comp (hfst1.prodMk hsnd1)).continuousAt
    have hDAt : ContinuousAt (fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) => D q.1 q.2.2)
        ((0 : P), ξ.1) := (hD.continuous.comp (hfst1.prodMk hsnd2)).continuousAt
    have hcontA : Tendsto (fun u : P => L u (ψ u).1) (nhds (0 : P)) (nhds (L 0 ξ.1.1)) :=
      hLAt.tendsto.comp (tendsto_id.prodMk_nhds hψcont)
    have hcontB : Tendsto (fun u : P => D u (ψ u).2) (nhds (0 : P)) (nhds (D 0 ξ.1.2)) :=
      hDAt.tendsto.comp (tendsto_id.prodMk_nhds hψcont)
    have hevSrcA : ∀ᶠ u in nhds (0 : P), L u (ψ u).1 ∈ (chr (L 0 ξ.1.1)).source :=
      hcontA.eventually ((chr (L 0 ξ.1.1)).open_source.mem_nhds hregA)
    have hevSrcB : ∀ᶠ u in nhds (0 : P), D u (ψ u).2 ∈ (chr (L 0 ξ.1.1)).source :=
      hcontB.eventually ((chr (L 0 ξ.1.1)).open_source.mem_nhds hregB)
    obtain ⟨ε₂, hε₂pos, hε₂⟩ := Metric.mem_nhds_iff.mp (hevSrcA.and hevSrcB)
    refine ⟨min ε₁ ε₂, δ, ψ, lt_min hε₁ hε₂pos, hδ, hψ0, hψcont, ?_, ?_⟩
    · intro u hu
      have hu₁ : ‖u‖ < ε₁ := lt_of_lt_of_le hu (min_le_left _ _)
      have hu₂ : ‖u‖ < ε₂ := lt_of_lt_of_le hu (min_le_right _ _)
      obtain ⟨hsa, hsb⟩ :=
        hε₂ (by rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hu₂)
      exact ⟨(hmain u hu₁).1, hsa, hsb,
        (chr (L 0 ξ.1.1)).injOn hsa hsb (sub_eq_zero.mp (hmain u hu₁).2)⟩
    · intro u hu x hx hx0
      exact huniq u (lt_of_lt_of_le hu (min_le_left _ _)) x hx
        (sub_eq_zero.mpr (congrArg (chr (L 0 ξ.1.1)) hx0))
  choose ε₀ δ₀ ψ₀ hε₀ hδ₀ hψ₀ hcont₀ hmain₀ huniq₀ using hloc
  obtain ⟨ρ, hρpos, hρ⟩ := exists_pos_le_dist_of_finite hfin
  -- ## 3. the comparison radii
  have hff : ∀ ξ : ↥(meetBox (L 0) (D 0)), ∃ r : ℝ, 0 < r ∧
      ∀ x : ℝ × EuclideanSpace ℝ (Fin 3), ‖x - ξ.1‖ < r →
        x.1 ∈ Set.Icc (0 : ℝ) 1 ∧ x.2 ∈ Submission.Drive.unitBox 2 :=
    fun ξ => exists_box_radius ξ.1 (hint ξ.1 ξ.2).1 (hint ξ.1 ξ.2).2
  choose rf hrfpos hrf using hff
  set δZ : ↥(meetBox (L 0) (D 0)) → ℝ := fun ξ => min (δ₀ ξ) (min (rf ξ) ρ) with hδZdef
  have hδZval : ∀ ξ, δZ ξ = min (δ₀ ξ) (min (rf ξ) ρ) := fun ξ => rfl
  have hδZpos : ∀ ξ, 0 < δZ ξ := by
    intro ξ; rw [hδZval]; exact lt_min (hδ₀ ξ) (lt_min (hrfpos ξ) hρpos)
  have hδZ_le_δ₀ : ∀ ξ, δZ ξ ≤ δ₀ ξ := fun ξ =>
    (le_of_eq (hδZval ξ)).trans (min_le_left _ _)
  have hδZ_le_rf : ∀ ξ, δZ ξ ≤ rf ξ := fun ξ =>
    (le_of_eq (hδZval ξ)).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδZ_le_ρ : ∀ ξ, δZ ξ ≤ ρ := fun ξ =>
    (le_of_eq (hδZval ξ)).trans ((min_le_right _ _).trans (min_le_right _ _))
  -- ## 4. the eventual properties of the branches
  have hevGood : ∀ᶠ u in nhds (0 : P), ∀ ξ : ↥(meetBox (L 0) (D 0)),
      ‖ψ₀ ξ u - ξ.1‖ < δZ ξ ∧ L u (ψ₀ ξ u).1 ∈ (chr (L 0 ξ.1.1)).source ∧
      D u (ψ₀ ξ u).2 ∈ (chr (L 0 ξ.1.1)).source ∧ L u (ψ₀ ξ u).1 = D u (ψ₀ ξ u).2 := by
    rw [Filter.eventually_all]
    intro ξ
    have h1 : ∀ᶠ u in nhds (0 : P), ‖u‖ < ε₀ ξ := by
      filter_upwards [Metric.ball_mem_nhds (0 : P) (hε₀ ξ)] with u hu
      rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at hu
    have h2 : ∀ᶠ u in nhds (0 : P), ‖ψ₀ ξ u - ξ.1‖ < δZ ξ := by
      have hc := (hcont₀ ξ).eventually (Metric.ball_mem_nhds ξ.1 (hδZpos ξ))
      filter_upwards [hc] with u hu
      simpa [dist_eq_norm] using hu
    filter_upwards [h1, h2] with u hu1 hu2
    obtain ⟨-, hsa, hsb, hmeet⟩ := hmain₀ ξ u hu1
    exact ⟨hu2, hsa, hsb, hmeet⟩
  have hevCover : ∀ᶠ u in nhds (0 : P), ∀ p ∈ meetBox (L u) (D u),
      ∃ ξ : ↥(meetBox (L 0) (D 0)), ‖p - ξ.1‖ < δZ ξ :=
    eventually_meetBox_cover_par_diag (by
      have hf1 : Continuous (fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) => q.1) := continuous_fst
      have hf2 : Continuous (fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) => q.2.1) :=
        continuous_fst.comp continuous_snd
      have hf3 : Continuous (fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) => q.2.2) :=
        continuous_snd.comp continuous_snd
      have hcL : Continuous (fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) => L q.1 q.2.1) :=
        hL.continuous.comp (hf1.prodMk hf2)
      have hcD : Continuous (fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) => D q.1 q.2.2) :=
        hD.continuous.comp (hf1.prodMk hf3)
      exact hcL.prodMk hcD) hδZpos
  have hevUniq : ∀ᶠ u in nhds (0 : P), ∀ ξ : ↥(meetBox (L 0) (D 0)),
      ∀ x : ℝ × EuclideanSpace ℝ (Fin 3), ‖x - ξ.1‖ < δZ ξ →
      L u x.1 = D u x.2 → x = ψ₀ ξ u := by
    rw [Filter.eventually_all]
    intro ξ
    have h1 : ∀ᶠ u in nhds (0 : P), ‖u‖ < ε₀ ξ := by
      filter_upwards [Metric.ball_mem_nhds (0 : P) (hε₀ ξ)] with u hu
      rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at hu
    filter_upwards [h1] with u hu1 x hx hx0
    exact huniq₀ ξ u hu1 x (lt_of_lt_of_le hx (hδZ_le_δ₀ ξ)) hx0
  -- ## 5. the assembly: the meet set is the branch set
  filter_upwards [hevGood, hevCover, hevUniq] with u hA hB hC
  set Ψ : ↥(meetBox (L 0) (D 0)) → ℝ × EuclideanSpace ℝ (Fin 3) := fun ξ => ψ₀ ξ u with hΨdef
  have hΨval : ∀ ξ : ↥(meetBox (L 0) (D 0)), Ψ ξ = ψ₀ ξ u := fun ξ => rfl
  have hΨmem : ∀ ξ : ↥(meetBox (L 0) (D 0)), Ψ ξ ∈ meetBox (L u) (D u) := by
    intro ξ
    have hfr := hrf ξ (Ψ ξ) (lt_of_lt_of_le (hA ξ).1 (hδZ_le_rf ξ))
    exact ⟨hfr.1, hfr.2, (hA ξ).2.2.2⟩
  have hΨinj : Function.Injective Ψ := by
    intro ξ η hξη
    by_contra hne
    have hd : ξ.1 ≠ η.1 := fun h => hne (Subtype.ext h)
    have h1 : ‖Ψ ξ - ξ.1‖ < δZ ξ := (hA ξ).1
    have h2 : ‖Ψ η - η.1‖ < δZ η := (hA η).1
    have h3 : 2 * ρ ≤ ‖ξ.1 - η.1‖ := hρ ξ.1 ξ.2 η.1 η.2 hd
    have h4 : ‖ξ.1 - η.1‖ ≤ ‖Ψ ξ - ξ.1‖ + ‖Ψ η - η.1‖ := by
      have hsub : ξ.1 - η.1 = (ξ.1 - Ψ ξ) + (Ψ ξ - η.1) := by abel
      calc ‖ξ.1 - η.1‖ = ‖(ξ.1 - Ψ ξ) + (Ψ ξ - η.1)‖ := by rw [hsub]
        _ ≤ ‖ξ.1 - Ψ ξ‖ + ‖Ψ ξ - η.1‖ := norm_add_le _ _
        _ = ‖Ψ ξ - ξ.1‖ + ‖Ψ η - η.1‖ := by rw [norm_sub_rev, hξη]
    have h5 : δZ ξ + δZ η ≤ 2 * ρ := by linarith [hδZ_le_ρ ξ, hδZ_le_ρ η]
    linarith
  have hΨsurj : ∀ x ∈ meetBox (L u) (D u), ∃ ξ : ↥(meetBox (L 0) (D 0)), Ψ ξ = x := by
    intro x hx
    obtain ⟨ξ, hdist⟩ := hB x hx
    refine ⟨ξ, ?_⟩
    rw [hΨval ξ]
    exact (hC ξ x (lt_of_lt_of_le hdist (le_refl _)) (mem_meetBox.mp hx).2.2).symm
  let Φ : ↥(meetBox (L 0) (D 0)) → ↥(meetBox (L u) (D u)) := fun ξ => ⟨Ψ ξ, hΨmem ξ⟩
  have hΦinj : Function.Injective Φ := by
    intro ξ η h
    exact hΨinj (congrArg Subtype.val h)
  have hΦsurj : Function.Surjective Φ := by
    intro x
    obtain ⟨ξ, hξ⟩ := hΨsurj x.1 x.2
    exact ⟨ξ, Subtype.ext hξ⟩
  have hcard : Nat.card ↥(meetBox (L u) (D u)) = Nat.card ↥(meetBox (L 0) (D 0)) :=
    Nat.card_congr (Equiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩).symm
  have hfinS : Finite ↥(meetBox (L u) (D u)) := Finite.of_surjective Φ hΦsurj
  have hfS : (meetBox (L u) (D u)).Finite := Set.finite_coe_iff.mp hfinS
  haveI : Fintype ↥(meetBox (L u) (D u)) := hfS.fintype
  have hA' : (meetBox (L u) (D u)).ncard = Nat.card ↥(meetBox (L u) (D u)) := by
    rw [Set.ncard_eq_toFinset_card _ hfS, hfS.card_toFinset, Fintype.card_eq_nat_card]
  have hB' : (meetBox (L 0) (D 0)).ncard = Nat.card ↥(meetBox (L 0) (D 0)) := by
    rw [Set.ncard_eq_toFinset_card _ hfin, hfin.card_toFinset, Fintype.card_eq_nat_card]
  exact hA'.trans (hcard.trans hB'.symm)

/-! ## The parity locality at a good configuration -/

/-- The parity of the germ count is locally constant at a good configuration. -/
theorem sideGerm_parity_local {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → Work.Drive.CappingSpace → Work.Drive.CappingSpace)
    (Q : ℂ → Work.Drive.CappingSpace) (c : ℝ)
    (hΞ : Work.Drive.ChartPert Q m Ξ) (hQ : Work.Drive.IsChartData Q)
    (w : UnitAddCircle)
    (A : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (hA : Work.Drive.GoodAt Ξ Q c w A) :
    ∃ η : ℝ, 0 < η ∧ ∀ u : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
      ‖u‖ < η →
        Odd (Work.Drive.CntAt Ξ Q c w (A + u)) = Odd (Work.Drive.CntAt Ξ Q c w A) := by
  classical
  -- the base data of the good configuration, at the base parameter `A + 0` of the family
  have hA0 : Work.Drive.GoodAt Ξ Q c w (A + 0) := by simpa using hA
  obtain ⟨-, -, hfin0, hint0, htrans0⟩ := hA0
  have hfin : (meetBox (parityLoopFam Ξ Q A 0) (parityChainFam Ξ Q c w A 0)).Finite := hfin0
  have hint : ∀ p ∈ meetBox (parityLoopFam Ξ Q A 0) (parityChainFam Ξ Q c w A 0),
      p.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ ∀ i : Fin 3, p.2 i ∈ Set.Ioo (0 : ℝ) 1 := hint0
  have htrans : ∀ p ∈ meetBox (parityLoopFam Ξ Q A 0) (parityChainFam Ξ Q c w A 0),
      LinearMap.range (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) (parityLoopFam Ξ Q A 0) p.1).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4) (parityChainFam Ξ Q c w A 0) p.2).toLinearMap = ⊤ :=
    htrans0
  -- the local constancy of the number of meets
  have hEv := eventually_ncard_meetBox_eq_manifold
    (P := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (parityLoopFam Ξ Q A) (parityChainFam Ξ Q c w A)
    (parityLoopFam_contMDiff Ξ Q hΞ hQ A) (parityChainFam_contMDiff Ξ Q c w hΞ hQ A)
    hfin hint htrans
  obtain ⟨η, hη, hsub⟩ := Metric.mem_nhds_iff.mp hEv
  refine ⟨η, hη, fun u hu => ?_⟩
  have hmem : u ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) η := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hu
  have hEq := hsub hmem
  rw [CntAt_eq_ncard_meetBox Ξ Q c w A u, hEq,
    ← CntAt_eq_ncard_meetBox Ξ Q c w A 0, add_zero]

end

end Work.Drive
