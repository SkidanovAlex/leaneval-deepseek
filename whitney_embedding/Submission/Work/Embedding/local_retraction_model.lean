import Mathlib
import Submission.Work.Embedding.exists_unique_closest_point
import Submission.Work.Embedding.chartRepN_adjoint_min

/-!
# The local model of the nearest-point retraction

Let `e : M → ℝ^N` be a smooth embedding of a compact `n`-manifold and suppose that, close enough to
the image of `e`, the closest point of `y` in `Set.range e` is unique.  Then near every point `e p`
the nearest-point map is given by a `C^∞` function.

The file contains three auxiliary results and the main theorem `local_retraction_model`:

* `isInvAdj_aux` — linear algebra: if `A` is injective then `A† ∘L A` is invertible.
* `smooth_implicit_function_local` — the implicit function theorem for the normal equation
  `(fderiv ψ u)† (y - ψ u) = 0`, *assuming* that `ψ` is `C^∞` on an open neighbourhood `V` of `u₀`.
  (This neighbourhood hypothesis is essential: for the conclusion `ContDiffOn ℝ ∞ η O` one needs
  `ψ` to be `C^∞` at the points of a whole neighbourhood, not merely `ContDiffAt` at `u₀`.)
* `minimizers_eventually_mem` — closest points of points near `e p` lie in any prescribed
  neighbourhood of `p`.
-/

namespace Work.Embedding

open scoped Manifold ContDiff
open Topology Metric Filter

/-- If a continuous linear map `A` between inner product spaces is injective then `A† ∘L A` is
invertible. -/
theorem isInvAdj_aux {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [CompleteSpace E] {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) (hA : Function.Injective A) : (A.adjoint ∘L A).IsInvertible := by
  have hinjA : Function.Injective (A.adjoint ∘L A) := by
    intro x y hxy
    have h0 : (A.adjoint ∘L A) (x - y) = 0 := by simp [map_sub, hxy]
    have hinner : inner 𝕜 ((A.adjoint ∘L A) (x - y)) (x - y) =
        inner 𝕜 (A (x - y)) (A (x - y)) := by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]
    rw [h0, inner_zero_left] at hinner
    have hAz : A (x - y) = 0 := (inner_self_eq_zero).mp hinner.symm
    have : x - y = 0 := hA (by simpa using hAz)
    exact sub_eq_zero.mp this
  refine ⟨(LinearEquiv.ofInjectiveEndo (A.adjoint ∘L A).toLinearMap hinjA).toContinuousLinearEquiv, ?_⟩
  ext x
  simp [LinearEquiv.coe_ofInjectiveEndo]

/-- **Implicit function theorem for the normal equation.**  Let `ψ` be `C^∞` on an open set `V` and
let `fderiv ℝ ψ u₀` be injective.  Then the equation `(fderiv ℝ ψ u)† (y - ψ u) = 0` has a local
solution `u = η y` near `(ψ u₀, u₀)`, and `η` is `C^∞` on a neighbourhood of `ψ u₀`. -/
theorem smooth_implicit_function_local {n N : ℕ}
    (ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    {V : Set (EuclideanSpace ℝ (Fin n))} (hV : IsOpen V)
    {u₀ : EuclideanSpace ℝ (Fin n)} (hu₀ : u₀ ∈ V)
    (hψ : ContDiffOn ℝ ∞ ψ V)
    (hinj : Function.Injective (fderiv ℝ ψ u₀)) :
    ∃ (η : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin n))
      (O : Set (EuclideanSpace ℝ (Fin N))),
      IsOpen O ∧ ψ u₀ ∈ O ∧ η (ψ u₀) = u₀ ∧ ContDiffOn ℝ ∞ η O ∧
      (∀ᶠ z in nhds (ψ u₀, u₀),
        (fderiv ℝ ψ z.2).adjoint (z.1 - ψ z.2) = 0 ↔ η z.1 = z.2) := by
  let f : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun z => (fderiv ℝ ψ z.2).adjoint (z.1 - ψ z.2)
  have hAdjsmooth0 : ContDiffAt ℝ ∞ (fun u : EuclideanSpace ℝ (Fin n) =>
      (fderiv ℝ ψ u).adjoint) u₀ := by
    have hf' : ContDiffAt ℝ ∞ (fderiv ℝ ψ) u₀ :=
      (hψ.contDiffAt (hV.mem_nhds hu₀)).fderiv_right (m := ∞) (by simp)
    have hadj : ContDiff ℝ ∞
        (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin N) => A.adjoint) :=
      (ContinuousLinearMap.adjoint :
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin N)) ≃ₗᵢ[ℝ]
          (EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin n))).contDiff
    exact ContDiffAt.comp u₀ hadj.contDiffAt hf'
  have hcd : ContDiffAt ℝ ∞ f (ψ u₀, u₀) := by
    have h2 := ContDiffAt.comp (ψ u₀, u₀) hAdjsmooth0 contDiffAt_snd
    have h3 : ContDiffAt ℝ ∞ (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin n) =>
        z.1 - ψ z.2) (ψ u₀, u₀) :=
      contDiffAt_fst.sub (ContDiffAt.comp (ψ u₀, u₀)
        (hψ.contDiffAt (hV.mem_nhds hu₀)) contDiffAt_snd)
    exact h2.clm_apply h3
  have hif : (fderiv ℝ f (ψ u₀, u₀)
      ∘L ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin N)) (EuclideanSpace ℝ (Fin n))).IsInvertible := by
    have hFhas : HasFDerivAt f (fderiv ℝ f (ψ u₀, u₀)) (ψ u₀, u₀) :=
      (hcd.differentiableAt (by simp)).hasFDerivAt
    have hpair : HasFDerivAt (fun u : EuclideanSpace ℝ (Fin n) => (ψ u₀, u))
        (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin N)) (EuclideanSpace ℝ (Fin n))) u₀ :=
      hasFDerivAt_prodMk_right (ψ u₀) u₀
    have h1 : HasFDerivAt (fun u => f (ψ u₀, u))
        (fderiv ℝ f (ψ u₀, u₀)
          ∘L ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin N)) (EuclideanSpace ℝ (Fin n))) u₀ :=
      HasFDerivAt.comp u₀ hFhas hpair
    have hα : HasFDerivAt (fun u : EuclideanSpace ℝ (Fin n) => (fderiv ℝ ψ u).adjoint)
        (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => (fderiv ℝ ψ u).adjoint) u₀) u₀ :=
      (hAdjsmooth0.differentiableAt (by simp)).hasFDerivAt
    have hβ : HasFDerivAt (fun u : EuclideanSpace ℝ (Fin n) => ψ u₀ - ψ u)
        (-(fderiv ℝ ψ u₀)) u₀ :=
      ((hψ.contDiffAt (hV.mem_nhds hu₀)).differentiableAt (by simp)).hasFDerivAt |>.const_sub (ψ u₀)
    have hprod := hα.clm_apply hβ
    have h2 : HasFDerivAt (fun u => f (ψ u₀, u))
        (-((fderiv ℝ ψ u₀).adjoint ∘L (fderiv ℝ ψ u₀))) u₀ := by
      simpa [f, sub_self, ContinuousLinearMap.comp_neg] using hprod
    have heq : fderiv ℝ f (ψ u₀, u₀)
        ∘L ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin N)) (EuclideanSpace ℝ (Fin n))
        = -((fderiv ℝ ψ u₀).adjoint ∘L (fderiv ℝ ψ u₀)) := by
      rw [← h1.fderiv, h2.fderiv]
    have hinj2 : Function.Injective (fderiv ℝ f (ψ u₀, u₀)
        ∘L ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin N)) (EuclideanSpace ℝ (Fin n))) := by
      rw [heq]
      have hTinv : ((fderiv ℝ ψ u₀).adjoint ∘L (fderiv ℝ ψ u₀)).IsInvertible :=
        isInvAdj_aux (fderiv ℝ ψ u₀) hinj
      exact fun x y h => hTinv.injective (by simpa using h)
    exact ⟨(LinearEquiv.ofInjectiveEndo (fderiv ℝ f (ψ u₀, u₀)
        ∘L ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin N)) (EuclideanSpace ℝ (Fin n))).toLinearMap
        hinj2).toContinuousLinearEquiv, by ext x; simp [LinearEquiv.coe_ofInjectiveEndo]⟩
  let η : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin n) :=
    hcd.implicitFunction (by simp) hif
  have hηrfl : hcd.implicitFunction (by simp) hif = η := rfl
  have hf_smooth : ∀ z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin n),
      z.2 ∈ V → ContDiffAt ℝ ∞ f z := by
    intro z hz
    have hψz : ContDiffAt ℝ ∞ ψ z.2 := hψ.contDiffAt (hV.mem_nhds hz)
    have hAdjs : ContDiffAt ℝ ∞ (fun u : EuclideanSpace ℝ (Fin n) =>
        (fderiv ℝ ψ u).adjoint) z.2 := by
      have hf' : ContDiffAt ℝ ∞ (fderiv ℝ ψ) z.2 := hψz.fderiv_right (m := ∞) (by simp)
      have hadj : ContDiff ℝ ∞
          (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin N) => A.adjoint) :=
        (ContinuousLinearMap.adjoint :
          (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin N)) ≃ₗᵢ[ℝ]
            (EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin n))).contDiff
      exact ContDiffAt.comp z.2 hadj.contDiffAt hf'
    have h1 := ContDiffAt.comp z hAdjs contDiffAt_snd
    have h2 : ContDiffAt ℝ ∞ (fun w : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin n) =>
        w.1 - ψ w.2) z :=
      contDiffAt_fst.sub (ContDiffAt.comp z hψz contDiffAt_snd)
    exact h1.clm_apply h2
  have hopen_inv : IsOpen {T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) |
      T.IsInvertible} := by
    have h := ContinuousLinearEquiv.isOpen (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n))
      (F := EuclideanSpace ℝ (Fin n))
    convert h using 1
    ext T
    simp [ContinuousLinearMap.IsInvertible]
  have hcont_comp : ContinuousAt (fun z : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin n) =>
      fderiv ℝ f z ∘L ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin N)) (EuclideanSpace ℝ (Fin n)))
      (ψ u₀, u₀) :=
    (hcd.continuousAt_fderiv (by simp)).clm_comp continuousAt_const
  have hinv_ev : ∀ᶠ z in 𝓝 (ψ u₀, u₀),
      (fderiv ℝ f z ∘L ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin N))
        (EuclideanSpace ℝ (Fin n))).IsInvertible :=
    hcont_comp.preimage_mem_nhds (hopen_inv.mem_nhds hif)
  have hηat : ContDiffAt ℝ ∞ η (ψ u₀) := hcd.contDiffAt_implicitFunction (by simp) hif
  have hηcont : ContinuousAt η (ψ u₀) := hηat.continuousAt
  have hηbase : η (ψ u₀) = u₀ := hcd.implicitFunction_apply_self (by simp) hif
  have hη1_ev : ∀ᶠ y in 𝓝 (ψ u₀), ContDiffAt ℝ 1 η y :=
    (hηat.of_le (by norm_num)).eventually (by norm_num)
  have hzero_ev : ∀ᶠ y in 𝓝 (ψ u₀), f (y, η y) = 0 := by
    have h := hcd.eventually_apply_implicitFunction (by simp) hif
    have h0 : f (ψ u₀, u₀) = 0 := by simp [f, sub_self]
    rw [h0] at h
    rw [hηrfl] at h
    exact h
  have htarget_ev : ∀ᶠ y in 𝓝 (ψ u₀), η y ∈ V := by
    have h : V ∈ 𝓝 (η (ψ u₀)) := by rw [hηbase]; exact hV.mem_nhds hu₀
    exact hηcont.preimage_mem_nhds h
  have hcont_ev : ∀ᶠ y in 𝓝 (ψ u₀), ContinuousAt η y :=
    hη1_ev.mono fun y hy => hy.continuousAt
  have htend : Tendsto (fun y => (y, η y)) (𝓝 (ψ u₀)) (𝓝 (ψ u₀, u₀)) := by
    have h := (continuousAt_id.prodMk hηcont).tendsto
    rw [hηbase] at h
    exact h
  have hinv_ev' : ∀ᶠ y in 𝓝 (ψ u₀),
      (fderiv ℝ f (y, η y) ∘L ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin N))
        (EuclideanSpace ℝ (Fin n))).IsInvertible :=
    htend.eventually hinv_ev
  have hW : ∀ᶠ y in 𝓝 (ψ u₀), f (y, η y) = 0 ∧ ContinuousAt η y ∧ η y ∈ V ∧
      (fderiv ℝ f (y, η y) ∘L ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin N))
        (EuclideanSpace ℝ (Fin n))).IsInvertible :=
    hzero_ev.and (hcont_ev.and (htarget_ev.and hinv_ev'))
  obtain ⟨O₀, hO₀sub, hO₀open, hO₀mem⟩ := _root_.mem_nhds_iff.mp hW
  refine ⟨η, O₀, hO₀open, hO₀mem, hηbase, ?_, ?_⟩
  · refine (hO₀open.contDiffOn_iff).mpr ?_
    intro y hy
    have hyf : f (y, η y) = 0 := (hO₀sub hy).1
    have hycont : ContinuousAt η y := (hO₀sub hy).2.1
    have hyS : η y ∈ V := (hO₀sub hy).2.2.1
    have hyinv : (fderiv ℝ f (y, η y) ∘L ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin N))
        (EuclideanSpace ℝ (Fin n))).IsInvertible := (hO₀sub hy).2.2.2
    have hwsmooth : ContDiffAt ℝ ∞ f (y, η y) := hf_smooth (y, η y) hyS
    have hηw : ContDiffAt ℝ ∞ (hwsmooth.implicitFunction (by simp) hyinv) y :=
      hwsmooth.contDiffAt_implicitFunction (by simp) hyinv
    have hηw_ev := hwsmooth.eventually_apply_eq_iff_implicitFunction (by simp) hyinv
    have htend_y : Tendsto (fun z => (z, η z)) (𝓝 y) (𝓝 (y, η y)) :=
      (continuousAt_id.prodMk hycont).tendsto
    have hpull2 : ∀ᶠ z in 𝓝 y, f (z, η z) = f (y, η y) ↔
        (hwsmooth.implicitFunction (by simp) hyinv) z = η z := htend_y.eventually hηw_ev
    refine ContDiffAt.congr_of_eventuallyEq hηw ?_
    filter_upwards [hpull2, hO₀open.mem_nhds hy] with z hzP hzV
    rw [(hO₀sub hzV).1, hyf] at hzP
    exact (hzP.mp rfl).symm
  · have h := hcd.eventually_apply_eq_iff_implicitFunction (by simp) hif
    rw [hηrfl] at h
    have h0 : f (ψ u₀, u₀) = 0 := by simp [f, sub_self]
    rw [h0] at h
    filter_upwards [h] with z hz
    simpa [f, sub_self] using hz

/-- Closest points of points near `e p` lie in any prescribed open neighbourhood of `p`. -/
theorem minimizers_eventually_mem {n N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [CompactSpace M]
    (e : M → EuclideanSpace ℝ (Fin N)) (he : ContMDiff (𝓡 n) (𝓡 N) ∞ e)
    (hinj : Function.Injective e) (p : M) {V : Set M} (hV : IsOpen V) (hpV : p ∈ V) :
    ∃ δ > 0, ∀ y : EuclideanSpace ℝ (Fin N), dist y (e p) < δ →
      ∀ q : M, dist y (e q) = infDist y (Set.range e) → q ∈ V := by
  classical
  by_cases hne : (Vᶜ).Nonempty
  · have hclosed : IsClosed (e '' Vᶜ) := (hV.isClosed_compl.isCompact.image he.continuous).isClosed
    have hep : e p ∉ e '' Vᶜ := by
      rintro ⟨z, hz, hzp⟩
      exact hz (by rw [hinj hzp]; exact hpV)
    have hpos : 0 < infDist (e p) (e '' Vᶜ) :=
      (hclosed.notMem_iff_infDist_pos (hne.image e)).mp hep
    refine ⟨infDist (e p) (e '' Vᶜ) / 2, by linarith, fun y hy q hq => ?_⟩
    by_contra hqV
    have hle : infDist (e p) (e '' Vᶜ) ≤ dist (e p) (e q) :=
      Metric.infDist_le_dist_of_mem ⟨q, hqV, rfl⟩
    have htri : dist (e p) (e q) ≤ dist (e p) y + dist y (e q) := dist_triangle _ _ _
    rw [hq] at htri
    have hlow : infDist y (Set.range e) ≤ dist y (e p) :=
      Metric.infDist_le_dist_of_mem (Set.mem_range_self p)
    have h2 : dist (e p) y < infDist (e p) (e '' Vᶜ) / 2 := by rw [dist_comm]; exact hy
    have hlow' : infDist y (Set.range e) ≤ dist (e p) y := by rw [dist_comm]; exact hlow
    have h3 : 2 * (infDist (e p) (e '' Vᶜ) / 2) = infDist (e p) (e '' Vᶜ) := by ring
    linarith [htri, hlow', h2, h3]
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    refine ⟨1, one_pos, fun y hy q hq => ?_⟩
    by_contra hqv
    have hqv' : q ∈ Vᶜ := hqv
    rw [hne] at hqv'
    exact hqv'

theorem local_retraction_model {n N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [CompactSpace M]
    (e : M → EuclideanSpace ℝ (Fin N)) (he : ContMDiff (𝓡 n) (𝓡 N) ∞ e)
    (hinj : Function.Injective e)
    (himm : ∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 N) e x))
    {ε : ℝ} (hεpos : 0 < ε)
    (huniq : ∀ y : EuclideanSpace ℝ (Fin N), infDist y (Set.range e) < ε →
      ∃! x : M, dist y (e x) = infDist y (Set.range e))
    (p : M) :
    ∃ (O : Set (EuclideanSpace ℝ (Fin N)))
      (g : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)),
      IsOpen O ∧ e p ∈ O ∧ (∀ y ∈ O, infDist y (Set.range e) < ε) ∧
      ContDiffOn ℝ ∞ g O ∧
      (∀ y ∈ O, ∀ q : M, dist y (e q) = infDist y (Set.range e) → e q = g y) := by
  classical
  let c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) p
  let ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N) := chartRepN e p
  have hψc : ∀ x ∈ c.source, ψ (c x) = e x := fun x hx => chartRepN_chart e p x hx
  have hbase : ψ (c p) = e p := hψc p (mem_chart_source (EuclideanSpace ℝ (Fin n)) p)
  have hctarget : c p ∈ c.target := c.map_source (mem_chart_source (EuclideanSpace ℝ (Fin n)) p)
  obtain ⟨η, O₁, hO₁open, hO₁mem, hηbase, hηsm, hIFT⟩ :=
    smooth_implicit_function_local ψ c.open_target hctarget
      (contMDiffOn_chartRepN e he p).contDiffOn
      (injective_fderiv_chartRep_infty e he himm p hctarget)
  obtain ⟨r, hrpos, hrsub⟩ := Metric.mem_nhds_iff.mp hIFT
  have hVopen : IsOpen (c.source ∩ c ⁻¹' ball (c p) r) := c.isOpen_inter_preimage isOpen_ball
  have hpV : p ∈ c.source ∩ c ⁻¹' ball (c p) r :=
    ⟨mem_chart_source _ p, mem_ball_self hrpos⟩
  obtain ⟨δ, hδpos, hδ⟩ := minimizers_eventually_mem e he hinj p hVopen hpV
  have hηcont : ContinuousAt η (ψ (c p)) :=
    (hηsm.contDiffAt (hO₁open.mem_nhds hO₁mem)).continuousAt
  have hηbase_target : η (ψ (c p)) ∈ c.target := by rw [hηbase]; exact hctarget
  obtain ⟨W, hWsub, hWopen, hWmem⟩ :=
    _root_.mem_nhds_iff.mp (hηcont.preimage_mem_nhds (c.open_target.mem_nhds hηbase_target))
  have hminpos : 0 < min δ (min r ε) := lt_min hδpos (lt_min hrpos hεpos)
  refine ⟨O₁ ∩ W ∩ ball (ψ (c p)) (min δ (min r ε)), fun y => ψ (η y),
    (hO₁open.inter hWopen).inter isOpen_ball, ?_, ?_, ?_, ?_⟩
  · rw [← hbase]
    exact ⟨⟨hO₁mem, hWmem⟩, mem_ball_self hminpos⟩
  · intro y hy
    have hy_ball : dist y (ψ (c p)) < min δ (min r ε) := mem_ball.mp hy.2
    have h1 : infDist y (Set.range e) ≤ dist y (e p) :=
      Metric.infDist_le_dist_of_mem (Set.mem_range_self p)
    have h2 : dist y (e p) < min δ (min r ε) := by rw [← hbase]; exact hy_ball
    have h3 : min δ (min r ε) ≤ ε := le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  · have hηO : ContDiffOn ℝ ∞ η (O₁ ∩ W ∩ ball (ψ (c p)) (min δ (min r ε))) :=
      hηsm.mono (by intro y hy; exact hy.1.1)
    have hmapsto : Set.MapsTo η (O₁ ∩ W ∩ ball (ψ (c p)) (min δ (min r ε))) c.target :=
      fun y hy => hWsub hy.1.2
    exact ((contMDiffOn_chartRepN e he p).contDiffOn).comp hηO hmapsto
  · intro y hy q hq
    have hy_ball : dist y (ψ (c p)) < min δ (min r ε) := mem_ball.mp hy.2
    have hyδ : dist y (e p) < δ := by
      rw [← hbase]; exact lt_of_lt_of_le hy_ball (min_le_left _ _)
    have hyr : dist y (ψ (c p)) < r :=
      lt_of_lt_of_le hy_ball (le_trans (min_le_right _ _) (min_le_left _ _))
    have hqV := hδ y hyδ q hq
    have hqsrc : q ∈ c.source := hqV.1
    have hcq_dist : dist (c q) (c p) < r := mem_ball.mp hqV.2
    have hmin : ∀ z : M, dist y (e q) ≤ dist y (e z) := fun z => by
      rw [hq]; exact Metric.infDist_le_dist_of_mem (Set.mem_range_self z)
    have hadj : (fderiv ℝ ψ (c q)).adjoint (y - e q) = 0 :=
      chartRepN_adjoint_min e he hqsrc hmin
    have hz_mem : (y, c q) ∈ ball (ψ (c p), c p) r := by
      rw [Metric.mem_ball, Prod.dist_eq]
      exact max_lt hyr hcq_dist
    have hIFT_at : (fderiv ℝ ψ (c q)).adjoint (y - ψ (c q)) = 0 ↔ η y = c q := by
      simpa using hrsub hz_mem
    rw [hψc q hqsrc] at hIFT_at
    have hηeq : η y = c q := hIFT_at.mp hadj
    simp only [hηeq, hψc q hqsrc]

end Work.Embedding
