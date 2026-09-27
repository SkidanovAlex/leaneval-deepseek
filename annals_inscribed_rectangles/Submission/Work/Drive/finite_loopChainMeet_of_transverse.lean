import Mathlib
import Submission.Work.Drive.chartDiffRangeBridge
import Submission.Work.Drive.finite_of_isCompact_of_isolated
import Submission.Work.Drive.meetS_finite_of_regular
import Submission.Work.Drive.ChartBridge

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# Finiteness of the meets of a loop and a `3`-chain in a charted `4`-manifold

`Work.Drive.finite_loopChainMeet_of_transverse` is the finiteness statement the collapse transport of
Hugelmeyer's Lemma 2 consumes as a hypothesis: a smooth loop `L : ℝ¹ → M` (one parameter) and a
smooth `3`-chain `N : ℝ³ → M` in a charted `4`-manifold `M` meet in **finitely many** parameter pairs
inside the two boxes, provided they are transverse at every meet in the boxes.

The proof is the standard one:

* the meet set `S` is closed (the condition `L p.1 = N p.2` is the preimage of the diagonal of
  `M × M`, closed because `M` is Hausdorff) and contained in the compact product of boxes
  `unitBox 0 × unitBox 2`, hence compact;
* at a meet `p` we use the *chart at the common value* `m = L p.1 = N p.2`.  In that chart the local
  model of the intersection problem is the charted difference map
  `q ↦ chart m (L q.1) - chart m (N q.2)`, whose derivative at `p` is
  `(mfderiv L p.1) ∘ fst - (mfderiv N p.2) ∘ snd` — the change of coordinates `tangentCoordChange`
  is the *same* on the two sides (`tangentCoordChange_self`, since the base point coincides with the
  chart centre), so it drops out.  The transversality hypothesis therefore makes that derivative
  surjective; the dimensions are `1 + 3 = 4`, so it is invertible and the inverse function theorem
  (`ContDiffAt.toOpenPartialHomeomorph`), in the elementary form
  `Work.Drive.eventually_eq_of_fderiv_surjective`, exhibits an open ball around `p` in which `p` is
  the *unique* zero of the charted difference map;
* the intersection of that ball with the (open) chart region is the required open neighbourhood of
  `p` meeting `S` only in `p`, and `Work.Drive.finite_of_isCompact_of_isolated` finishes.
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Manifold Set Filter

set_option backward.isDefEq.respectTransparency false

noncomputable section

/-- **A zero with invertible derivative is isolated.**  If `f : X → Y` is `C^∞` at `a`, `f a = 0`, the
spaces are finite-dimensional of the *same* dimension and `fderiv ℝ f a` is surjective (hence, the
system being square, bijective), then `a` is the only zero of `f` in a ball around `a`.

This is the inverse function theorem (`ContDiffAt.toOpenPartialHomeomorph`) read as a statement about
zeros: the map is a local homeomorphism at `a` with value `0`. -/
theorem eventually_eq_of_fderiv_surjective {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (f : X → Y) (a : X) (hdim : Module.finrank ℝ X = Module.finrank ℝ Y)
    (hf : ContDiffAt ℝ Ctop f a) (hfa : f a = 0)
    (hsurj : Function.Surjective (fderiv ℝ f a)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : X, ‖x - a‖ < ε → f x = 0 → x = a := by
  classical
  have hne : Ctop ≠ 0 := by decide
  have hd : DifferentiableAt ℝ f a := hf.differentiableAt hne
  have hfd : HasFDerivAt f (fderiv ℝ f a) a := hd.hasFDerivAt
  have hinj : Function.Injective (fderiv ℝ f a) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (fderiv ℝ f a).toLinearMap) hdim).mpr hsurj
  let e : X ≃L[ℝ] Y :=
    (LinearEquiv.ofBijective (fderiv ℝ f a).toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv
  have he : (e : X →L[ℝ] Y) = fderiv ℝ f a := by ext v; rfl
  have hfd' : HasFDerivAt f (e : X →L[ℝ] Y) a := hfd.congr_fderiv he.symm
  let Φ : OpenPartialHomeomorph X Y := hf.toOpenPartialHomeomorph f hfd' hne
  have hΦcoe : (Φ : X → Y) = f := ContDiffAt.toOpenPartialHomeomorph_coe hf hfd' hne
  have hΦmem : a ∈ Φ.source := ContDiffAt.mem_toOpenPartialHomeomorph_source hf hfd' hne
  have hev : ∀ᶠ x in 𝓝 a, Φ.symm (Φ x) = x := Φ.eventually_left_inverse hΦmem
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨ε, hε, fun x hx hx0 => ?_⟩
  have hx1 : Φ.symm (Φ x) = x :=
    hball (by rw [Metric.mem_ball, dist_eq_norm]; exact hx)
  have hxa : Φ x = Φ a := by rw [hΦcoe, hx0, hfa]
  rw [hxa] at hx1
  exact hx1.symm.trans (Φ.left_inv hΦmem)

/-- **Isolation of a meet of a loop and a `3`-chain.**  Two smooth maps `L : ℝ¹ → M`, `N : ℝ³ → M`
into a charted `4`-manifold `M`, transverse at the meet `L p.1 = N p.2` (with both parameters in the
respective boxes), meet only at `p` in a neighbourhood of `p`. -/
theorem loopChainMeet_isolated {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (L : EuclideanSpace ℝ (Fin 1) → M) (N : EuclideanSpace ℝ (Fin 3) → M)
    (hL : ContMDiff (𝓡 1) (𝓡 4) Ctop L) (hN : ContMDiff (𝓡 3) (𝓡 4) Ctop N)
    (htrans : ∀ (u : EuclideanSpace ℝ (Fin 1)) (x : EuclideanSpace ℝ (Fin 3)),
      u ∈ Submission.Drive.unitBox 0 → x ∈ Submission.Drive.unitBox 2 → L u = N x →
      LinearMap.range (mfderiv (𝓡 1) (𝓡 4) L u).toLinearMap ⊔
      LinearMap.range (mfderiv (𝓡 3) (𝓡 4) N x).toLinearMap = ⊤)
    {p : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3)}
    (hu : p.1 ∈ Submission.Drive.unitBox 0) (hx : p.2 ∈ Submission.Drive.unitBox 2)
    (heq : L p.1 = N p.2) :
    ∃ U : Set (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3)), IsOpen U ∧ p ∈ U ∧
      U ∩ {q | q.1 ∈ Submission.Drive.unitBox 0 ∧ q.2 ∈ Submission.Drive.unitBox 2 ∧
        L q.1 = N q.2} ⊆ {p} := by
  classical
  -- the two intrinsic derivatives, rebranded as maps between the plain model spaces; and the change
  -- of coordinates at the common value `L p.1 = N p.2`, which is the identity on values
  let M₀ : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    mfderiv (𝓡 1) (𝓡 4) L p.1
  let M₁ : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    mfderiv (𝓡 3) (𝓡 4) N p.2
  let T : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    tangentCoordChange (𝓡 4) (L p.1) (L p.1) (L p.1)
  have hsL : L p.1 ∈ (chr (L p.1)).source :=
    mem_chart_source (EuclideanSpace ℝ (Fin 4)) (L p.1)
  have hsN : N p.2 ∈ (chr (L p.1)).source := by rw [heq]; exact mem_chart_source _ _
  have hTapp : ∀ v : EuclideanSpace ℝ (Fin 4), T v = v := fun v =>
    tangentCoordChange_self (I := 𝓡 4) (mem_extChartAt_source (I := 𝓡 4) (L p.1))
  -- ## smoothness of the charted difference map
  have hchartOn : ContMDiffOn (𝓡 4) (𝓡 4) Ctop (chr (L p.1)) (chr (L p.1)).source := by
    have h := contMDiffOn_extChartAt (I := 𝓡 4) (x := L p.1) (n := Ctop)
    simpa [chr] using h
  have hcdA : ContDiffAt ℝ Ctop
      (fun q : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3) => chr (L p.1) (L q.1)) p := by
    have h1 : ContDiffAt ℝ Ctop
        (fun u : EuclideanSpace ℝ (Fin 1) => chr (L p.1) (L u)) p.1 :=
      ((hchartOn.contMDiffAt
        ((chr (L p.1)).open_source.mem_nhds hsL)).comp p.1 (hL p.1)).contDiffAt
    exact h1.comp p (contDiff_fst.contDiffAt)
  have hcdB : ContDiffAt ℝ Ctop
      (fun q : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3) => chr (L p.1) (N q.2)) p := by
    have h1 : ContDiffAt ℝ Ctop
        (fun u : EuclideanSpace ℝ (Fin 3) => chr (L p.1) (N u)) p.2 :=
      ((hchartOn.contMDiffAt
        ((chr (L p.1)).open_source.mem_nhds hsN)).comp p.2 (hN p.2)).contDiffAt
    exact h1.comp p (contDiff_snd.contDiffAt)
  -- ## the derivative of the charted difference map
  have hA : HasFDerivAt (fun q : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3) =>
        chr (L p.1) (L q.1))
      ((T.comp M₀).comp (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 1))
        (EuclideanSpace ℝ (Fin 3)))) p := by
    have h1 := fderiv_chart_comp_hasFDerivAt L hL (L p.1) hsL
    have hc := h1.comp p hasFDerivAt_fst
    simpa [Function.comp_def, M₀, T] using hc
  have hB : HasFDerivAt (fun q : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3) =>
        chr (L p.1) (N q.2))
      ((T.comp M₁).comp (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 1))
        (EuclideanSpace ℝ (Fin 3)))) p := by
    have h1 := fderiv_chart_comp_hasFDerivAt N hN (L p.1) hsN
    rw [← heq] at h1
    have hc := h1.comp p hasFDerivAt_snd
    simpa [Function.comp_def, M₁, T] using hc
  have hPderiv : fderiv ℝ (fun q : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3) =>
        chr (L p.1) (L q.1) - chr (L p.1) (N q.2)) p
      = ((T.comp M₀).comp (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 1))
          (EuclideanSpace ℝ (Fin 3))))
        - ((T.comp M₁).comp (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 1))
          (EuclideanSpace ℝ (Fin 3)))) := by
    have h := (hA.sub hB).fderiv
    rw [show ((fun q : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3) =>
            chr (L p.1) (L q.1)) -
          (fun q : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3) =>
            chr (L p.1) (N q.2)))
        = (fun q : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3) =>
            chr (L p.1) (L q.1) - chr (L p.1) (N q.2)) from rfl] at h
    exact h
  -- ## the derivative is surjective
  have hsurj : Function.Surjective (fderiv ℝ (fun q : EuclideanSpace ℝ (Fin 1) ×
      EuclideanSpace ℝ (Fin 3) => chr (L p.1) (L q.1) - chr (L p.1) (N q.2)) p) := by
    intro w
    have htr : LinearMap.range M₀.toLinearMap ⊔ LinearMap.range M₁.toLinearMap = ⊤ := by
      simpa [M₀, M₁] using htrans p.1 p.2 hu hx heq
    have hw : w ∈ LinearMap.range M₀.toLinearMap ⊔ LinearMap.range M₁.toLinearMap := by
      rw [htr]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hw
    obtain ⟨σ, hσ⟩ := LinearMap.mem_range.mp ha
    obtain ⟨τ, hτ⟩ := LinearMap.mem_range.mp (Submodule.neg_mem _ hb)
    refine ⟨(σ, τ), ?_⟩
    have hval : fderiv ℝ (fun q : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3) =>
        chr (L p.1) (L q.1) - chr (L p.1) (N q.2)) p (σ, τ) = T (M₀ σ) - T (M₁ τ) := by
      rw [hPderiv]
      simp only [sub_apply, ContinuousLinearMap.comp_apply]
      rfl
    rw [hval]
    rw [show T (M₀ σ) = M₀ σ from hTapp _, show T (M₁ τ) = M₁ τ from hTapp _]
    rw [show M₀ σ = a from hσ, show M₁ τ = -b from hτ]
    rw [sub_neg_eq_add, hab]
  -- ## `p` is the unique zero of the charted difference map in a ball
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3))
      = Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) := by
    rw [Module.finrank_prod, finrank_euclideanSpace, finrank_euclideanSpace, finrank_euclideanSpace]
    norm_num
  have hcont : ContDiffAt ℝ Ctop (fun q : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3) =>
      chr (L p.1) (L q.1) - chr (L p.1) (N q.2)) p := hcdA.sub hcdB
  have hP0 : (fun q : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3) =>
      chr (L p.1) (L q.1) - chr (L p.1) (N q.2)) p = 0 := by
    show chr (L p.1) (L p.1) - chr (L p.1) (N p.2) = 0
    rw [show N p.2 = L p.1 from heq.symm, sub_self]
  obtain ⟨ε, hε, huniq⟩ := eventually_eq_of_fderiv_surjective
    (fun q : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3) =>
      chr (L p.1) (L q.1) - chr (L p.1) (N q.2)) p hdim hcont hP0 hsurj
  -- ## the neighbourhood: inside the ball the charted difference map has `p` as its only zero, and
  -- every meet of the two chains is such a zero
  refine ⟨Metric.ball p ε, Metric.isOpen_ball, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_self]; exact hε
  · intro q hq
    obtain ⟨hqb, hqs⟩ := hq
    have hnorm : ‖q - p‖ < ε := by
      rw [Metric.mem_ball, dist_eq_norm] at hqb; exact hqb
    have hz : chr (L p.1) (L q.1) - chr (L p.1) (N q.2) = 0 := by rw [hqs.2.2, sub_self]
    simpa using huniq q hnorm hz

/-- **Finiteness of the meets of a loop and a `3`-chain in a charted `4`-manifold.**  A smooth loop (one parameter) and a smooth `3`-chain in a `4`-manifold meet in finitely many parameter pairs, provided they are transverse at every meet in the two boxes: `4` parameters against `4` equations, so every meet in the box is isolated, and `unitBox 0 × unitBox 2` is compact.  (`Submission.Drive.unitBox m` is the closed unit box in `EuclideanSpace ℝ (Fin (m+1))`, so `unitBox 0` is the box in the loop parameter and `unitBox 2` the box in the chain parameter.)

This is the missing finiteness of the design's counts `Work.Drive.coreMeet Q c P` and `Work.Drive.diamMeet Q t W` (the collapse transport of Hugelmeyer's Lemma 2 consumes their finiteness as a hypothesis); it is *not* supplied by the boundary-finiteness `Work.Drive.bdyZeros_finite` of the box-parity chapter, which controls the boundary faces only.  The transversality hypothesis is required at the meets *inside the boxes*, which is the form the design's Sard lemmas produce. -/
theorem finite_loopChainMeet_of_transverse {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (L : EuclideanSpace ℝ (Fin 1) → M) (N : EuclideanSpace ℝ (Fin 3) → M)
    (hL : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) L)
    (hN : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) N)
    (htrans : ∀ (u : EuclideanSpace ℝ (Fin 1)) (x : EuclideanSpace ℝ (Fin 3)),
      u ∈ Submission.Drive.unitBox 0 → x ∈ Submission.Drive.unitBox 2 → L u = N x →
      LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) L u).toLinearMap ⊔
      LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) N x).toLinearMap = ⊤) :
    ({p : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3) |
        p.1 ∈ Submission.Drive.unitBox 0 ∧ p.2 ∈ Submission.Drive.unitBox 2 ∧
        L p.1 = N p.2}).Finite := by
  classical
  set S : Set (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3)) :=
    {p | p.1 ∈ Submission.Drive.unitBox 0 ∧ p.2 ∈ Submission.Drive.unitBox 2 ∧ L p.1 = N p.2}
    with hS
  have hclosed : IsClosed S := by
    rw [hS]
    have h1 : IsClosed {p : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3) |
        p.1 ∈ Submission.Drive.unitBox 0} :=
      (isClosed_unitBox 0).preimage continuous_fst
    have h2 : IsClosed {p : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3) |
        p.2 ∈ Submission.Drive.unitBox 2} :=
      (isClosed_unitBox 2).preimage continuous_snd
    have h3 : IsClosed {p : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3) |
        L p.1 = N p.2} :=
      isClosed_eq (hL.continuous.comp continuous_fst) (hN.continuous.comp continuous_snd)
    exact h1.inter (h2.inter h3)
  have hK : IsCompact (Submission.Drive.unitBox 0 ×ˢ Submission.Drive.unitBox 2) :=
    (isCompact_unitBox 0).prod (isCompact_unitBox 2)
  have hsub : S ⊆ Submission.Drive.unitBox 0 ×ˢ Submission.Drive.unitBox 2 :=
    fun p hp => ⟨hp.1, hp.2.1⟩
  have hcomp : IsCompact S := hK.of_isClosed_subset hclosed hsub
  refine finite_of_isCompact_of_isolated hcomp ?_
  intro p hp
  rw [hS] at hp
  exact loopChainMeet_isolated L N hL hN htrans hp.1 hp.2.1 hp.2.2

end

end Work.Drive
