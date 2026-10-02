import Mathlib
import Submission.Work.PTGeometric.WeakRegion.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.PTGeometric.WeakRegion

/-- The filter of neighbourhoods of `x` within a set `s` (spelled as in the statement below; it is
the same filter as `nhdsWithin`). -/
abbrev nhwaysWithin {α : Type*} [TopologicalSpace α] (x : α) (s : Set α) : Filter α :=
  nhdsWithin x s

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

noncomputable section

variable {n : ℕ} [NeZero n]

/-- The continuous linear map `(u, s) ↦ consVec s u = u + s • e 0`. -/
def consCLM : (EuclideanSpace ℝ (Fin n) × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) ℝ +
    ContinuousLinearMap.smulRight (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
      (eZero (n := n))

lemma consCLM_apply (v : EuclideanSpace ℝ (Fin n) × ℝ) : consCLM v = consVec v.2 v.1 := by
  have h1 : (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) ℝ) v = v.1 := rfl
  have h2 : (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ) v = v.2 := rfl
  simp only [consCLM, add_apply, ContinuousLinearMap.smulRight_apply, h1, h2, consVec]

lemma consCLM_apply_pair (u : EuclideanSpace ℝ (Fin n)) (s : ℝ) :
    consCLM (u, s) = consVec s u := consCLM_apply (u, s)

lemma consCLM_zero_apply (u : EuclideanSpace ℝ (Fin n)) : consCLM (u, 0) = u := by
  rw [consCLM_apply]; simp [consVec]

lemma proj_zero_consCLM (v : EuclideanSpace ℝ (Fin n) × ℝ) :
    PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) 0 (consCLM v) = v.2 + v.1.ofLp 0 := by
  rw [consCLM_apply]
  rw [show PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) 0 (consVec v.2 v.1)
      = (consVec v.2 v.1).ofLp 0 from rfl, consVec_apply_zero]

/-- The analytic extension of `Ψ` across the boundary of the half-space, together with the value
of its derivative at `p`. -/
lemma exists_analytic_ext
    (Ψ : EuclideanSpace ℝ (Fin n) → ℝ) (p : EuclideanSpace ℝ (Fin n))
    (hp0 : p.ofLp 0 = 0)
    (hC : ContDiffWithinAt ℝ (⊤ : WithTop ℕ∞) Ψ
      (Set.range (modelWithCornersEuclideanHalfSpace n)) p)
    (h0 : Ψ p = 0) (c : ℝ) (hc : c < 0)
    (hd : fderivWithin ℝ Ψ (Set.range (modelWithCornersEuclideanHalfSpace n)) p
      = c • (PiLp.proj 2 (fun _ : Fin n => ℝ) 0)) :
    ∃ g : EuclideanSpace ℝ (Fin n) → ℝ,
      AnalyticAt ℝ g p ∧ g p = 0 ∧
      Set.EqOn Ψ g (Set.range (modelWithCornersEuclideanHalfSpace n)) ∧
      fderiv ℝ g p = c • (PiLp.proj 2 (fun _ : Fin n => ℝ) 0) := by
  have ha : AnalyticWithinAt ℝ Ψ (Set.range (modelWithCornersEuclideanHalfSpace n)) p :=
    (contDiffWithinAt_omega_iff_analyticWithinAt).mp hC
  obtain ⟨g, hgv, hgEq, hgan⟩ := ha.exists_analyticAt
  have hpH : p ∈ Set.range (modelWithCornersEuclideanHalfSpace n) := by
    rw [range_modelWithCornersEuclideanHalfSpace]
    simpa using le_of_eq hp0.symm
  refine ⟨g, hgan, ?_, ?_, ?_⟩
  · rw [← hgv, h0]
  · exact hgEq.mono (Set.subset_insert _ _)
  · have h1 : fderivWithin ℝ Ψ (Set.range (modelWithCornersEuclideanHalfSpace n)) p
        = fderivWithin ℝ g (Set.range (modelWithCornersEuclideanHalfSpace n)) p := by
      refine Filter.EventuallyEq.fderivWithin_eq ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with z hz
        exact hgEq (Set.mem_insert_of_mem _ hz)
      · rw [hgv]
    have h2 : fderivWithin ℝ g (Set.range (modelWithCornersEuclideanHalfSpace n)) p
        = fderiv ℝ g p :=
      fderivWithin_eq_fderiv
        ((modelWithCornersEuclideanHalfSpace n).uniqueDiffOn.uniqueDiffWithinAt hpH)
        hgan.differentiableAt
    rw [← h2, ← h1, hd]



/-- A continuous linear map `ℝ →L[ℝ] ℝ` which is a nonzero multiple of the identity is
invertible. -/
lemma isInvertible_smul_one (c : ℝ) (hc : c ≠ 0) :
    (c • (1 : ℝ →L[ℝ] ℝ)).IsInvertible := by
  refine ContinuousLinearMap.IsInvertible.of_inverse (g := c⁻¹ • (1 : ℝ →L[ℝ] ℝ)) ?_ ?_
  · ext x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    field_simp
  · ext x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    field_simp

/-- The coordinate functional `z ↦ z 0`. -/
def coord0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) 0

lemma coord0_apply (z : EuclideanSpace ℝ (Fin n)) : coord0 z = z.ofLp 0 :=
  PiLp.proj_apply 2 (fun _ : Fin n => ℝ) 0 z

lemma coord0_eZero : coord0 (eZero (n := n)) = 1 := by
  rw [coord0_apply, eZero_apply]

lemma eZero_norm : ‖(eZero (n := n))‖ = 1 := by
  rw [eZero, PiLp.norm_single]
  simp

/-- `tailVec` as a continuous linear map. -/
def tailVecCLM : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) -
    (coord0 (n := n)).smulRight (eZero (n := n))

lemma tailVecCLM_apply (z : EuclideanSpace ℝ (Fin n)) : tailVecCLM z = tailVec z := by
  simp only [tailVecCLM, sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, coord0_apply, tailVec]

lemma consVec_zero (u : EuclideanSpace ℝ (Fin n)) : consVec 0 u = u := by
  simp [consVec]

lemma tailVec_self_of_apply_zero {z : EuclideanSpace ℝ (Fin n)} (hz : z.ofLp 0 = 0) :
    tailVec z = z := by
  simp [tailVec, hz]

lemma tailVec_idem (z : EuclideanSpace ℝ (Fin n)) : tailVec (tailVec z) = tailVec z := by
  have h := tailVec_consVec (0 : ℝ) (tailVec_apply_zero z)
  rwa [consVec_zero] at h

/-- **Monotonicity in the normal direction.**  Under the hypotheses of the graph theorem, the
one-variable functions `s ↦ g (consVec s u)` are strictly decreasing on a fixed interval around
`0`, uniformly for `u` near `p`. -/
lemma eventually_strictAntiOn (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (p : EuclideanSpace ℝ (Fin n)) (c : ℝ) (hc : c < 0) (hg : AnalyticAt ℝ g p)
    (hgd : fderiv ℝ g p = c • (PiLp.proj 2 (fun _ : Fin n => ℝ) 0)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ u in 𝓝 p,
      StrictAntiOn (fun s : ℝ => g (consVec s u)) (Ioo (-ε) ε) := by
  have hgc : ContDiffAt ℝ (⊤ : WithTop ℕ∞) g p := hg.contDiffAt
  have hcf : ContinuousAt (fderiv ℝ g) p := hgc.continuousAt_fderiv (by simp)
  have hcv : ContinuousAt (fun z => fderiv ℝ g z (eZero (n := n))) p :=
    hcf.clm_apply continuousAt_const
  have hval : (fun z => fderiv ℝ g z (eZero (n := n))) p = c := by
    change (fderiv ℝ g p) (eZero (n := n)) = c
    have h : fderiv ℝ g p = c • (coord0 (n := n)) := by rw [hgd]; rfl
    rw [h, ContinuousLinearMap.smul_apply, smul_eq_mul, coord0_eZero, mul_one]
  have hval' : (fun z => fderiv ℝ g z (eZero (n := n))) p < c / 2 := by
    rw [hval]; linarith
  have hev1 : ∀ᶠ z in 𝓝 p, fderiv ℝ g z (eZero (n := n)) < c / 2 :=
    hcv.eventually_lt continuousAt_const hval'
  have hev2 : ∀ᶠ z in 𝓝 p, AnalyticAt ℝ g z := hg.eventually_analyticAt
  obtain ⟨ρ, hρpos, hρ⟩ := Metric.mem_nhds_iff.mp (hev1.and hev2)
  refine ⟨ρ / 4, by linarith, ?_⟩
  filter_upwards [Metric.ball_mem_nhds p (show (0 : ℝ) < ρ / 4 by linarith)] with u hu
  have hmem : ∀ s ∈ Ioo (-(ρ / 4)) (ρ / 4), consVec s u ∈ Metric.ball p ρ := by
    intro s hs
    have hu' : ‖u - p‖ < ρ / 4 := by simpa [Metric.mem_ball, dist_eq_norm] using hu
    have hs' : |s| < ρ / 4 := by
      rw [abs_lt]; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    rw [Metric.mem_ball, dist_eq_norm]
    have h1 : consVec s u - p = (u - p) + s • eZero := by rw [consVec]; abel
    calc ‖consVec s u - p‖ = ‖(u - p) + s • eZero‖ := by rw [h1]
      _ ≤ ‖u - p‖ + ‖s • eZero‖ := norm_add_le _ _
      _ = ‖u - p‖ + |s| * ‖(eZero (n := n))‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ = ‖u - p‖ + |s| := by rw [eZero_norm, mul_one]
      _ < ρ / 4 + ρ / 4 := by linarith
      _ = ρ / 2 := by ring
      _ < ρ := by linarith
  refine strictAntiOn_of_deriv_neg (convex_Ioo _ _) ?_ ?_
  · intro s hs
    have hpath : ContinuousAt (fun s' : ℝ => consVec s' u) s := by
      simp only [consVec]
      fun_prop
    have h1 : ContinuousAt g (consVec s u) := ((hρ (hmem s hs)).2).continuousAt
    exact (ContinuousAt.comp (f := fun s' : ℝ => consVec s' u) h1 hpath).continuousWithinAt
  · intro s hs
    rw [interior_Ioo] at hs
    have hz : consVec s u ∈ Metric.ball p ρ := hmem s hs
    have hgd' : HasFDerivAt g (fderiv ℝ g (consVec s u)) (consVec s u) :=
      ((hρ hz).2.differentiableAt).hasFDerivAt
    have hpath : HasDerivAt (fun s' : ℝ => consVec s' u) (eZero (n := n)) s := by
      simpa [consVec, one_smul] using
        ((hasDerivAt_id s).smul_const (eZero (n := n))).const_add u
    have hderiv : HasDerivAt (fun s' : ℝ => g (consVec s' u))
        (fderiv ℝ g (consVec s u) (eZero (n := n))) s := hgd'.comp_hasDerivAt s hpath
    rw [hderiv.deriv]
    have := (hρ hz).1
    linarith

/-- **The implicit root.**  If `g` is analytic at `p`, vanishes at `p` and its derivative at `p` is
a negative multiple of the coordinate functional `z ↦ z 0`, then near `p` the equation `g = 0`
determines the coordinate `z 0` as an analytic function `ψ` of the other coordinates. -/
lemma exists_implicit_root
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (p : EuclideanSpace ℝ (Fin n)) (c : ℝ) (hc : c < 0)
    (hg : AnalyticAt ℝ g p) (hgp : g p = 0)
    (hgd : fderiv ℝ g p = c • (PiLp.proj 2 (fun _ : Fin n => ℝ) 0)) :
    ∃ (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (ε δ : ℝ), 0 < ε ∧ 0 < δ ∧
      AnalyticAt ℝ ψ p ∧ ψ p = 0 ∧
      ∃ U ∈ 𝓝 p, ∀ u ∈ U, ψ u ∈ Ioo (-ε) δ ∧ g (consVec (ψ u) u) = 0 ∧
        ∀ s ∈ Ioo (-ε) δ, (g (consVec s u) = 0 ↔ ψ u = s) := by
  classical
  set F : EuclideanSpace ℝ (Fin n) × ℝ → ℝ := fun v => g (consCLM v) with hFdef
  have hFapp : ∀ v, F v = g (consCLM v) := fun v => by rw [hFdef]
  have hFana : AnalyticAt ℝ F (p, 0) := by
    have h1 : AnalyticAt ℝ g (consCLM (p, 0)) := by rw [consCLM_zero_apply]; exact hg
    have h2 := h1.comp ((ContinuousLinearMap.analyticAt consCLM (p, 0)))
    simpa [hFdef, Function.comp_def] using h2
  have hcdf : ContDiffAt ℝ (⊤ : WithTop ℕ∞) F (p, 0) := hFana.contDiffAt
  have hpn : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  have hFderiv : HasFDerivAt F (fderiv ℝ g p ∘SL consCLM) (p, 0) := by
    have hg' : HasFDerivAt g (fderiv ℝ g p) (consCLM (p, 0)) := by
      rw [consCLM_zero_apply]
      exact hg.differentiableAt.hasFDerivAt
    exact hg'.comp (p, 0) (ContinuousLinearMap.hasFDerivAt consCLM)
  have hproj : (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) 0)
      (consVec 1 (0 : EuclideanSpace ℝ (Fin n))) = 1 := by
    rw [PiLp.proj_apply, consVec_apply_zero]
    simp
  have hcval : (fderiv ℝ F (p, 0))
      ((ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) ℝ) 1) = c := by
    rw [hFderiv.fderiv, ContinuousLinearMap.comp_apply]
    have hinr : (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) ℝ) (1 : ℝ) = (0, 1) := by
      rw [ContinuousLinearMap.inr_apply]
    rw [hinr, consCLM_apply_pair, hgd, ContinuousLinearMap.smul_apply, hproj]
    simp
  have hT : (fderiv ℝ F (p, 0) ∘SL ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
      = c • (1 : ℝ →L[ℝ] ℝ) := by
    refine ContinuousLinearMap.ext fun x => ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply]
    have hx : (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) ℝ) x
        = x • (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) ℝ) 1 := by
      rw [ContinuousLinearMap.inr_apply, ContinuousLinearMap.inr_apply]
      simp
    rw [hx, map_smul, hcval]
    simp [smul_eq_mul, mul_comm]
  have hif : (fderiv ℝ F (p, 0) ∘SL
      ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) ℝ).IsInvertible := by
    rw [hT]
    exact isInvertible_smul_one c (ne_of_lt hc)
  set ψ : EuclideanSpace ℝ (Fin n) → ℝ := hcdf.implicitFunction hpn hif with hψdef
  have hψcd : ContDiffAt ℝ (⊤ : WithTop ℕ∞) ψ p := hcdf.contDiffAt_implicitFunction hpn hif
  have hself : ψ p = 0 := hcdf.implicitFunction_apply_self hpn hif
  have hcont : ContinuousAt ψ p := hψcd.continuousAt
  have hana : AnalyticAt ℝ ψ p := by
    have h1 : ContDiffWithinAt ℝ (⊤ : WithTop ℕ∞) ψ univ p := hψcd.contDiffWithinAt
    exact (analyticWithinAt_univ).mp ((contDiffWithinAt_omega_iff_analyticWithinAt).mp h1)
  have hev := hcdf.eventually_apply_eq_iff_implicitFunction hpn hif
  obtain ⟨W, hW, hW'⟩ := hev.exists_mem
  rw [nhds_prod_eq] at hW
  obtain ⟨U₀, hU₀, T, hT₀, hUT⟩ := Filter.mem_prod_iff.mp hW
  obtain ⟨r, hrpos, hball⟩ := Metric.mem_nhds_iff.mp hT₀
  have hIooT : Ioo (-r) r ⊆ T := fun y hy => hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩)
  have hFp : F (p, 0) = 0 := by
    rw [hFapp, consCLM_zero_apply]
    exact hgp
  refine ⟨ψ, r, r, hrpos, hrpos, hana, hself, ?_⟩
  have hmem : ψ ⁻¹' Ioo (-r) r ∈ 𝓝 p := by
    refine hcont.preimage_mem_nhds ?_
    rw [hself]
    exact Ioo_mem_nhds (by linarith) (by linarith)
  refine ⟨U₀ ∩ ψ ⁻¹' Ioo (-r) r, Filter.inter_mem hU₀ hmem, ?_⟩
  rintro u ⟨hu₀, huψ⟩
  have hmemW : (u, ψ u) ∈ W := hUT ⟨hu₀, hIooT huψ⟩
  have h1 : F (u, ψ u) = F (p, 0) := (hW' _ hmemW).mpr rfl
  have hzu : F (u, ψ u) = 0 := h1.trans hFp
  have hFu : g (consVec (ψ u) u) = 0 := by
    rw [← hzu, hFapp, consCLM_apply_pair]
  refine ⟨huψ, hFu, ?_⟩
  intro s hs
  have h2 : (u, s) ∈ W := hUT ⟨hu₀, hIooT hs⟩
  have h3 : F (u, s) = F (p, 0) ↔ ψ u = s := hW' _ h2
  have hFs : F (u, s) = g (consVec s u) := by rw [hFapp, consCLM_apply_pair]
  simpa only [hFs, hFp] using h3

/-- **The graph data.**  Combining the implicit function theorem with the monotonicity gives a
function `ψ` (the "height" of the level set of `g` above the tangential coordinates) with all the
properties needed by the half-space graph theorem. -/
lemma exists_graph_data (g : EuclideanSpace ℝ (Fin n) → ℝ) (p : EuclideanSpace ℝ (Fin n))
    (c : ℝ) (hc : c < 0) (hg : AnalyticAt ℝ g p) (hgp : g p = 0)
    (hgd : fderiv ℝ g p = c • (PiLp.proj 2 (fun _ : Fin n => ℝ) 0))
    (hsign : ∀ᶠ u in 𝓝 p, u.ofLp 0 = 0 → 0 ≤ g u) :
    ∃ (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (ε : ℝ), 0 < ε ∧ AnalyticAt ℝ ψ p ∧ ψ p = 0 ∧
      ∃ S ∈ 𝓝 p, ∀ u ∈ S, ψ u ∈ Ioo (-ε) ε ∧ g (consVec (ψ u) u) = 0 ∧
        StrictAntiOn (fun s : ℝ => g (consVec s u)) (Ioo (-ε) ε) ∧
        (u.ofLp 0 = 0 → 0 ≤ ψ u) ∧
        (∀ s ∈ Ioo (-ε) ε, (g (consVec s u) ≤ 0 ↔ ψ u ≤ s)) := by
  obtain ⟨ψ, ε₁, δ₁, hε₁, hδ₁, hψana, hψ0, U₁, hU₁, hU₁prop⟩ :=
    exists_implicit_root g p c hc hg hgp hgd
  obtain ⟨ε₂, hε₂, hAnti⟩ := eventually_strictAntiOn g p c hc hg hgd
  set ε : ℝ := min (min ε₁ δ₁) ε₂ with hεdef
  have hε : 0 < ε := lt_min (lt_min hε₁ hδ₁) hε₂
  have hεle₁ : ε ≤ ε₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hεleδ₁ : ε ≤ δ₁ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hεle₂ : ε ≤ ε₂ := min_le_right _ _
  have hsub : Ioo (-ε) ε ⊆ Ioo (-ε₁) δ₁ := by
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hsub₂ : Ioo (-ε) ε ⊆ Ioo (-ε₂) ε₂ := by
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hmemψ : ∀ᶠ u in 𝓝 p, ψ u ∈ Ioo (-ε) ε := by
    have hI : Ioo (-ε) ε ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) (by linarith)
    have h := hψana.continuousAt.preimage_mem_nhds (by rw [hψ0]; exact hI)
    exact h
  have hmemS : U₁ ∩ ψ ⁻¹' Ioo (-ε) ε ∩
      {u | StrictAntiOn (fun s : ℝ => g (consVec s u)) (Ioo (-ε) ε)} ∩
      {u | u.ofLp 0 = 0 → 0 ≤ g u} ∈ 𝓝 p := by
    refine Filter.inter_mem (Filter.inter_mem (Filter.inter_mem hU₁ hmemψ) ?_) hsign
    exact hAnti.mono (fun u hu => hu.mono hsub₂)
  refine ⟨ψ, ε, hε, hψana, hψ0, _, hmemS, ?_⟩
  rintro u ⟨⟨⟨hu₁, huψ⟩, hanti⟩, hsignu⟩
  have hroot : g (consVec (ψ u) u) = 0 := (hU₁prop u hu₁).2.1
  have h0mem : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, by linarith⟩
  have hzero : g (consVec 0 u) = g u := by
    rw [show consVec 0 u = u from by simp [consVec]]
  refine ⟨huψ, hroot, hanti, ?_, ?_⟩
  · intro hu0
    by_contra hcon
    push_neg at hcon
    have hstrict := hanti huψ h0mem hcon
    change g (consVec 0 u) < g (consVec (ψ u) u) at hstrict
    rw [hroot] at hstrict
    have hge := hsignu hu0
    rw [← hzero] at hge
    linarith
  · intro s hs
    constructor
    · intro hle
      by_contra hcon
      push_neg at hcon
      have hstrict := hanti hs huψ hcon
      change g (consVec (ψ u) u) < g (consVec s u) at hstrict
      rw [hroot] at hstrict
      linarith
    · intro hle
      have hmono := hanti.antitoneOn huψ hs hle
      change g (consVec s u) ≤ g (consVec (ψ u) u) at hmono
      rw [hroot] at hmono
      exact hmono


end


/-- **The half-space graph result (the crux of the weak region-charting statement).**

Let `Ψ : ℝⁿ → ℝ` be `C^∞` on the half-space `H = {z | 0 ≤ z 0}` near a *boundary* point `p` (i.e.
`p 0 = 0`), with `Ψ p = 0`, with nonvanishing *within* derivative at `p`
(`fderivWithin ℝ Ψ H p = c • (z ↦ z 0)` with `c < 0`), and nonnegative on the boundary hyperplane
near `p`.  Then the sublevel set `{Ψ ≤ 0} ∩ H` is, near `p`, the epigraph `{z 0 ≥ h (tail z)}` of a
`C^∞` function `h ≥ 0` of the tangential coordinates, with `h (tail p) = 0`.

`Work.PTGeometric.tailVec z = z - (z 0) • e 0` is the tail of `z`, so the conclusion says exactly
that `{Ψ ≤ 0}` is the region above the graph of `h`.

Suggested route (three steps; any correct route is fine):

1. **Monotonicity.** `ContDiffWithinAt ℝ ∞ Ψ H p` gives, by
   `ContDiffWithinAt.continuousWithinAt_fderivWithin` (Mathlib,
   `Analysis/Calculus/ContDiff/Comp.lean`; needs `(modelWithCornersEuclideanHalfSpace n).uniqueDiffOn`),
   the continuity of `z ↦ fderivWithin ℝ Ψ H z` on `H` at `p`; hence `fderivWithin ℝ Ψ H z (e 0) ≤ c/2 < 0`
   for `z ∈ H` near `p`.  A mean value argument along the lines `s ↦ Ψ (consVec s u)` (at interior
   points `fderivWithin ℝ Ψ H = fderiv ℝ Ψ`) then shows that `s ↦ Ψ (consVec s u)` is strictly
   decreasing on a small interval `[0, δ]` for every `u` near `tailVec p`.

2. **The root.** For such `u` the intermediate value argument (with `Ψ (consVec 0 u) ≥ 0` from
   `hsign` and `Ψ (consVec δ u) < 0`) produces a root in `[0, δ]`, unique by monotonicity.  Define
   `h u` by that root (e.g. by `Classical.choose` or `sInf`), and transfer the strict monotonicity
   to get `Ψ z ≤ 0 ↔ h (tailVec z) ≤ z 0` near `p` inside `H`, together with `0 ≤ h` and
   `h (tailVec p) = 0`.

3. **Smoothness.** Two possible routes:
   * *(extension + implicit function machinery)*: extend `Ψ` to a function `Ψ̃` that is `C^1` (or `C^K`
     for all `K`) on a full neighbourhood of `p`, e.g. by the normal Taylor polynomial at the
     boundary: `Ψ̃ (consVec s u) := Ψ (consVec s u)` for `s ≥ 0` and
     `Ψ̃ (consVec s u) := Σ_{k=0}^{K} (s^k / k!) • (∂₀^k Ψ) (consVec 0 u)` for `s ≤ 0` (the two
     branches have matching derivatives up to order `K` on the hyperplane).  Then apply Mathlib's
     implicit function machinery to `Λ s u := (Ψ̃ (consVec s u), u)` at `(0, tailVec p)` (its
     derivative is invertible: `∂₀Ψ̃ = c ≠ 0`; see
     `Mathlib/Analysis/Calculus/Implicit.lean`, `HasStrictFDerivAt.implicitFunction`, or
     `ContDiffAt.toOpenPartialHomeomorph`/`ContDiffAt.localInverse` in
     `Analysis/Calculus/InverseFunctionTheorem/`, plus `localInverse_apply_image`,
     `to_localInverse`, or the workspace's
     `Work.ThomBordism.Transversality.Sard.localInverse_smooth.contDiffOn_symm_of_contDiffOn`), which
     gives a `C^∞` function `σ` with `Ψ̃ (consVec (σ s u) u) = s`.  For `s = 0` and `u` near
     `tailVec p` one has `σ 0 u = h u` (both are roots of `Ψ (·, u)` in `[0, δ]`, where the root is
     unique by step 1), so `h` is `C^∞`.  If the extension is only `C^K`, get `h ∈ C^K` for every `K`
     and conclude with `contDiffAt_top`/`contDiffOn_top`-style reasoning.
   * *(bootstrap)*: show that `h` is differentiable near `tailVec p` with
     `∂_u h (u) = - (∂_u Ψ) (consVec (h u) u) / (∂₀ Ψ) (consVec (h u) u)` (mean value argument in `s`
     plus the continuity of `h` from step 2 and of the derivatives of `Ψ`), and then bootstrap
     `C^k ⟹ C^{k+1}` since the right-hand side is a `C^∞` function of `u` composed with
     `(h u, u)` (using that `0 ≤ h u`, so the argument stays in `H`).
-/
theorem exists_graph_halfSpace {n : ℕ} [NeZero n]
    (Ψ : EuclideanSpace ℝ (Fin n) → ℝ) (p : EuclideanSpace ℝ (Fin n))
    (hp0 : p.ofLp 0 = 0)
    (hC : ContDiffWithinAt ℝ (⊤ : WithTop ℕ∞) Ψ
      (Set.range (modelWithCornersEuclideanHalfSpace n)) p)
    (h0 : Ψ p = 0) (c : ℝ) (hc : c < 0)
    (hd : fderivWithin ℝ Ψ (Set.range (modelWithCornersEuclideanHalfSpace n)) p
      = c • (PiLp.proj 2 (fun _ : Fin n => ℝ) 0))
    (hsign : Filter.Eventually (fun z : EuclideanSpace ℝ (Fin n) =>
        z.ofLp 0 = 0 → 0 ≤ Ψ z)
        (nhdsWithin p (Set.range (modelWithCornersEuclideanHalfSpace n)))) :
    ∃ (h : EuclideanSpace ℝ (Fin n) → ℝ) (W : Set (EuclideanSpace ℝ (Fin n))),
      IsOpen W ∧ Work.PTGeometric.tailVec p ∈ W ∧
      ContDiffOn ℝ (⊤ : WithTop ℕ∞) h W ∧ (∀ u ∈ W, 0 ≤ h u) ∧
      h (Work.PTGeometric.tailVec p) = 0 ∧
      Filter.Eventually (fun z : EuclideanSpace ℝ (Fin n) =>
        (Ψ z ≤ 0 ↔ h (Work.PTGeometric.tailVec z) ≤ z.ofLp 0))
        (nhwaysWithin p (Set.range (modelWithCornersEuclideanHalfSpace n))) := by
  obtain ⟨g, hgan, hgp, hgEq, hgd⟩ := exists_analytic_ext Ψ p hp0 hC h0 c hc hd
  have hHmem : ∀ z : EuclideanSpace ℝ (Fin n),
      z ∈ Set.range (modelWithCornersEuclideanHalfSpace n) ↔ 0 ≤ z.ofLp 0 := by
    intro z
    rw [range_modelWithCornersEuclideanHalfSpace]
    simp only [Set.mem_ofPred_eq]
  have hsign_g : ∀ᶠ u in 𝓝 p, u.ofLp 0 = 0 → 0 ≤ g u := by
    filter_upwards [eventually_nhdsWithin_iff.mp hsign] with u hu hu0
    have huH : u ∈ Set.range (modelWithCornersEuclideanHalfSpace n) := by
      rw [hHmem, hu0]
    have h1 : 0 ≤ Ψ u := hu huH hu0
    rwa [hgEq huH] at h1
  obtain ⟨ψ, ε, hε, hψana, hψ0, S₀, hS₀, hS₀prop⟩ :=
    exists_graph_data g p c hc hgan hgp hgd hsign_g
  obtain ⟨O, hOsub, hOopen, hpO⟩ := mem_nhds_iff.mp
    (Filter.inter_mem hS₀ ((isOpen_analyticAt ℝ ψ).mem_nhds hψana))
  have hOana : ∀ u ∈ O, AnalyticAt ℝ ψ u := fun u hu => (hOsub hu).2
  have hOinS : ∀ u ∈ O, u ∈ S₀ := fun u hu => (hOsub hu).1
  refine ⟨fun z => ψ (tailVec z), tailVecCLM ⁻¹' O, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hOopen.preimage tailVecCLM.continuous
  · show tailVecCLM (tailVec p) ∈ O
    rw [tailVecCLM_apply, tailVec_idem, tailVec_self_of_apply_zero hp0]
    exact hpO
  · have hψO : ContDiffOn ℝ (⊤ : WithTop ℕ∞) ψ O :=
      fun u hu => ((hOana u hu).analyticWithinAt).contDiffWithinAt
    have hcomp := hψO.comp_continuousLinearMap tailVecCLM
    refine hcomp.congr fun z _ => ?_
    simp only [Function.comp_apply]
    exact congrArg ψ (tailVecCLM_apply z).symm
  · intro u hu
    have h1 : tailVec u ∈ O := by rw [← tailVecCLM_apply]; exact hu
    exact (hS₀prop _ (hOinS _ h1)).2.2.2.1 (tailVec_apply_zero u)
  · show ψ (tailVec (tailVec p)) = 0
    rw [tailVec_idem, tailVec_self_of_apply_zero hp0, hψ0]
  · refine eventually_nhdsWithin_iff.mpr ?_
    have hset : {z : EuclideanSpace ℝ (Fin n) | tailVec z ∈ O ∧ z.ofLp 0 < ε} ∈ 𝓝 p := by
      refine Filter.inter_mem ?_ ?_
      · refine (Work.PTGeometric.continuous_tailVec.continuousAt).preimage_mem_nhds ?_
        rw [tailVec_self_of_apply_zero hp0]
        exact hOopen.mem_nhds hpO
      · have hcont : ContinuousAt (fun z : EuclideanSpace ℝ (Fin n) => z.ofLp 0) p := by
          simpa only [PiLp.proj_apply] using
            (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) 0).continuousAt
        have hI : Iio ε ∈ 𝓝 (p.ofLp 0) := by
          rw [hp0]
          exact Iio_mem_nhds hε
        show (fun z : EuclideanSpace ℝ (Fin n) => z.ofLp 0) ⁻¹' Iio ε ∈ 𝓝 p
        exact hcont.preimage_mem_nhds hI
    filter_upwards [hset] with z hz hzH
    obtain ⟨hzO, hzε⟩ := hz
    have hz0 : 0 ≤ z.ofLp 0 := (hHmem z).mp hzH
    have hzs : z.ofLp 0 ∈ Ioo (-ε) ε := ⟨by linarith, hzε⟩
    have hkey := (hS₀prop (tailVec z) (hOinS _ hzO)).2.2.2.2 (z.ofLp 0) hzs
    have hzeq : Ψ z = g (consVec (z.ofLp 0) (tailVec z)) := by
      rw [hgEq hzH, consVec_tailVec]
    rw [hzeq, hkey]
    simp only [tailVec_idem]

end Work.PTGeometric.WeakRegion
