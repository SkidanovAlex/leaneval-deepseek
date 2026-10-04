import Mathlib
import Submission.Work.EvenBound.Imports

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Work.EvenBound.FarthestPoint

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.InjRadius
open Submission.HopfRinow
open Submission.CornerCut

/-- **A point at distance exactly `r` from `p`, when `d(p,q)` is finite.**

If `d(p,q) ≠ ⊤`, `0 < r < d(p,q)` and `z ↦ d(p,z)` is continuous, then the `r`-sphere around `p`
for the Riemannian distance is nonempty.  This is the replacement for
`Submission.HopfRinow.exists_riemannianEDist_eq_ofReal` (which needs `PathConnectedSpace M`)
used in the localised Hopf–Rinow recursion below: the path is produced by
`Manifold.exists_lt_of_riemannianEDist_lt` from the finiteness of `d(p,q)` alone, and the point of
the sphere is found by the intermediate value theorem
(`Commons.Geometry.Manifold.exists_riemannianEDist_eq_ofReal_and_add_le`). -/
theorem exists_riemannianEDist_eq_ofReal_of_ne_top
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    (p q : M) {r : ℝ} (hr : 0 < r)
    (hcontp : Continuous (fun z : M => Manifold.riemannianEDist I p z))
    (hfin : Manifold.riemannianEDist I p q ≠ ⊤)
    (hrq : ENNReal.ofReal r < Manifold.riemannianEDist I p q) :
    ∃ z : M, Manifold.riemannianEDist I p z = ENNReal.ofReal r := by
  obtain ⟨z, hz, -⟩ :=
    Commons.Geometry.Manifold.exists_riemannianEDist_eq_ofReal_and_add_le (I := I) p q hr hcontp
      (ENNReal.ofReal_toReal hfin).symm hrq 1 one_pos
  exact ⟨z, hz⟩

/-- **Localised Hopf–Rinow.**  If `d(p,q)` is finite (in particular if `p` and `q` are joined by
a finite-length path) then there is a *minimising* geodesic from `p` to `q`: a tangent vector `v`
with `GExp p v = q` and `d(p,q) = ‖v‖`.

This is `Submission.HopfRinow.exists_geodesic_riemannianEDist_eq` without the hypotheses
`[PathConnectedSpace M] [RegularSpace M]`: the finiteness of `d(p,q)` replaces the use of
`riemannianEDist_lt_top` (which needs `ConnectedSpace`), the spheres needed by the recursion are
provided by `exists_riemannianEDist_eq_ofReal_of_ne_top` instead of
`Submission.HopfRinow.exists_riemannianEDist_eq_ofReal` (which needs `PathConnectedSpace`), and
`RegularSpace M` is produced from `T2Space M` by local compactness of the model space. -/
theorem exists_geodesic_riemannianEDist_eq_of_lt_top
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (p q : M)
    (hfin : Manifold.riemannianEDist I p q < ⊤) :
    ∃ v : TangentSpace I p, GExp (cov := cov) hmet p v = q ∧
      Manifold.riemannianEDist I p q = ENNReal.ofReal ‖v‖ := by
  classical
  haveI hR : RegularSpace M := by
    haveI : LocallyCompactSpace H := I.locallyCompactSpace
    haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
    infer_instance
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  obtain ⟨ρ₁, hρ₁, hexp⟩ :=
    exists_eq_expMap_of_riemannianEDist_lt (I := I) (cov := cov) hmet htor p
  obtain ⟨ρ₂, hρ₂, hexp_eq⟩ := exists_pos_GExp_eq_expMap (cov := cov) hmet p
  set ρ : ℝ := min ρ₁ ρ₂ with hρdef
  have hρ : 0 < ρ := lt_min hρ₁ hρ₂
  by_cases hsmall : Manifold.riemannianEDist I p q < ENNReal.ofReal ρ
  · obtain ⟨v, hv, hd⟩ := hexp q
      (lt_of_lt_of_le hsmall (ENNReal.ofReal_le_ofReal (min_le_left _ _)))
    have hvρ₂ : ‖v‖ < ρ₂ := by
      have h1 : ENNReal.ofReal ‖v‖ < ENNReal.ofReal ρ₂ := by
        rw [← hd]
        exact lt_of_lt_of_le hsmall (ENNReal.ofReal_le_ofReal (min_le_right _ _))
      exact (ENNReal.ofReal_lt_ofReal_iff hρ₂).mp h1
    exact ⟨v, by rw [← hv, hexp_eq v hvρ₂], hd⟩
  · push Not at hsmall
    have hdtop : Manifold.riemannianEDist I p q < ⊤ := hfin
    set L : ℝ := (Manifold.riemannianEDist I p q).toReal with hLdef
    have hdL : Manifold.riemannianEDist I p q = ENNReal.ofReal L :=
      (ENNReal.ofReal_toReal hdtop.ne).symm
    have hLge : ρ ≤ L := by
      rw [hLdef, ← ENNReal.toReal_ofReal hρ.le]
      exact ENNReal.toReal_mono hdtop.ne hsmall
    have hLpos : 0 < L := lt_of_lt_of_le hρ hLge
    have hLnn : 0 ≤ L := hLpos.le
    have hεpos : 0 < ρ / 2 := by linarith
    have hεL : ρ / 2 < L := by linarith
    -- the point `y₁` minimising `d(·,q)` on the sphere of radius `ρ/2`
    obtain ⟨y₁, hy₁, hy₁tri, hy₁min⟩ :=
      Commons.Geometry.Manifold.riemannianEDist_min_on_sphere_enormSMul (I := I) p q hεpos
        (exists_riemannianEDist_eq_ofReal_of_ne_top (I := I) p q hεpos
          (continuous_riemannianEDist_left (I := I) p) hdtop.ne
          (by rw [hdL]; exact (ENNReal.ofReal_lt_ofReal_iff hLpos).mpr hεL))
        (continuous_riemannianEDist_left (I := I) p) (continuous_riemannianEDist_right (I := I) q)
        (by rw [hdL]; exact (ENNReal.ofReal_lt_ofReal_iff hLpos).mpr hεL)
    have hy₁q : Manifold.riemannianEDist I y₁ q = ENNReal.ofReal (L - ρ/2) := by
      have h : Manifold.riemannianEDist I y₁ q + ENNReal.ofReal (ρ/2) = ENNReal.ofReal L := by
        rw [hy₁tri, hdL]
      have h2 : ENNReal.ofReal (L - ρ/2) + ENNReal.ofReal (ρ/2) = ENNReal.ofReal L := by
        rw [← ENNReal.ofReal_add (by linarith) hεpos.le, show L - ρ/2 + ρ/2 = L from by ring]
      exact (ENNReal.add_left_inj ENNReal.ofReal_ne_top).mp (h.trans h2.symm)
    have hltρ₁ : ρ / 2 < ρ₁ := by
      have h : ρ ≤ ρ₁ := by rw [hρdef]; exact min_le_left _ _
      linarith
    obtain ⟨v₁, hv₁eq, hv₁d⟩ := hexp y₁ (by
      rw [hy₁]; exact (ENNReal.ofReal_lt_ofReal_iff hρ₁).mpr hltρ₁)
    have hv₁norm : ‖v₁‖ = ρ/2 := by
      have h : ENNReal.ofReal ‖v₁‖ = ENNReal.ofReal (ρ/2) := by rw [← hv₁d, hy₁]
      exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg _) hεpos.le).mp h
    have hv₁ne : v₁ ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hv₁norm; linarith
    set u : TangentSpace I p := unitOf v₁ hv₁ne with hudef
    have hunorm : ‖u‖ = 1 := unitOf_norm v₁ hv₁ne
    have hu_v₁ : (ρ/2) • u = v₁ := by
      rw [hudef, unitOf, smul_smul, hv₁norm, mul_inv_cancel₀ (ne_of_gt hεpos), one_smul]
    have hv₁ρ₂ : ‖v₁‖ < ρ₂ := by
      have hρle : ρ ≤ ρ₂ := by rw [hρdef]; exact min_le_right _ _
      have hlt : ‖v₁‖ < ρ := by rw [hv₁norm]; linarith
      linarith
    have hGExp_v₁ : GExp (cov := cov) hmet p v₁ = y₁ := by
      rw [hexp_eq v₁ hv₁ρ₂, hv₁eq]
    -- the ray
    set α : ℝ → M := fun t : ℝ => GExp (cov := cov) hmet p (t • u) with hαdef
    have hαε : α (ρ/2) = y₁ := by
      simp only [hαdef]
      rw [hu_v₁, hGExp_v₁]
    -- the underlying chosen geodesic of length `L`
    set Gp : ℝ → M := geodCurve (cov := cov) hmet L hLnn p u hunorm with hGpdef
    have hGpspec := geodCurve_spec (cov := cov) hmet L hLnn p u hunorm
    have hGpsm : ContMDiffOn 𝓘(ℝ) I ∞ Gp
        (Ioo (-(geodDelta (cov := cov) hmet)) (L + geodDelta (cov := cov) hmet)) := by
      rw [hGpdef]; exact hGpspec.2.2.1
    have hGpsp : ∀ r ∈ Ioo (-(geodDelta (cov := cov) hmet))
        (L + geodDelta (cov := cov) hmet), ‖curveVelocity (I := I) Gp r‖ = 1 := by
      intro r hr; rw [hGpdef]; exact hGpspec.2.2.2.2 r hr
    have hαGp : ∀ t ∈ Icc (0:ℝ) L, α t = Gp t := by
      intro t ht
      simp only [hαdef, hGpdef]
      exact GExp_eq_geodCurve (cov := cov) hmet (x := p) (u := u) hunorm (T := L) hLnn ht.1 ht.2
    have hαcont : ContinuousOn α (Icc (0:ℝ) L) :=
      (hGpsm.continuousOn.mono (fun r hr => ⟨by linarith [geodDelta_pos (cov := cov) hmet, hr.1],
        by linarith [geodDelta_pos (cov := cov) hmet, hr.2]⟩)).congr (fun t ht => hαGp t ht)
    -- the set of times up to which the ray is radial
    set S : Set ℝ := {t : ℝ | t ∈ Icc (0:ℝ) L ∧
      Manifold.riemannianEDist I p (α t) = ENNReal.ofReal t ∧
      Manifold.riemannianEDist I (α t) q = ENNReal.ofReal (L - t)} with hSdef
    have hSsub : S ⊆ Icc (0:ℝ) L := fun t ht => ht.1
    have hSclosed : IsClosed S := by
      rw [← closure_subset_iff_isClosed]
      intro t ht
      obtain ⟨un, huS, hut⟩ := mem_closure_iff_seq_limit.mp ht
      have huK : ∀ n, un n ∈ Icc (0:ℝ) L := fun n => (huS n).1
      have htK : t ∈ Icc (0:ℝ) L :=
        ⟨le_of_tendsto_of_tendsto tendsto_const_nhds hut (Eventually.of_forall (fun n => (huK n).1)),
         le_of_tendsto_of_tendsto hut tendsto_const_nhds (Eventually.of_forall (fun n => (huK n).2))⟩
      have hut' : Tendsto un atTop (𝓝[Icc (0:ℝ) L] t) :=
        tendsto_nhdsWithin_iff.mpr ⟨hut, Eventually.of_forall huK⟩
      have hαtend : Tendsto (fun n => α (un n)) atTop (𝓝 (α t)) :=
        Filter.Tendsto.comp (ContinuousWithinAt.tendsto (hαcont.continuousWithinAt htK)) hut'
      have h1 : Tendsto (fun n => Manifold.riemannianEDist I p (α (un n))) atTop
          (𝓝 (Manifold.riemannianEDist I p (α t))) :=
        Filter.Tendsto.comp ((continuous_riemannianEDist_left (I := I) p).tendsto (α t)) hαtend
      have h2 : Tendsto (fun n => Manifold.riemannianEDist I p (α (un n))) atTop
          (𝓝 (ENNReal.ofReal t)) := by
        rw [show (fun n => Manifold.riemannianEDist I p (α (un n)))
            = (fun n => ENNReal.ofReal (un n)) from funext (fun n => (huS n).2.1)]
        exact Filter.Tendsto.comp (g := ENNReal.ofReal) (f := un)
          (hg := ENNReal.continuous_ofReal.tendsto t) (hf := hut)
      have h3 : Tendsto (fun n => Manifold.riemannianEDist I (α (un n)) q) atTop
          (𝓝 (Manifold.riemannianEDist I (α t) q)) :=
        Filter.Tendsto.comp ((continuous_riemannianEDist_right (I := I) q).tendsto (α t)) hαtend
      have h4 : Tendsto (fun n => Manifold.riemannianEDist I (α (un n)) q) atTop
          (𝓝 (ENNReal.ofReal (L - t))) := by
        rw [show (fun n => Manifold.riemannianEDist I (α (un n)) q)
            = (fun n => ENNReal.ofReal (L - un n)) from funext (fun n => (huS n).2.2)]
        exact Filter.Tendsto.comp (g := ENNReal.ofReal) (f := fun n => L - un n)
          (hg := ENNReal.continuous_ofReal.tendsto (L - t)) (hf := tendsto_const_nhds.sub hut)
      exact ⟨htK, tendsto_nhds_unique h1 h2, tendsto_nhds_unique h3 h4⟩
    have h0S : (0:ℝ) ∈ S := by
      refine ⟨⟨le_refl 0, hLnn⟩, ?_, ?_⟩
      · simp only [hαdef]; rw [zero_smul, GExp_zero, Manifold.riemannianEDist_self, ENNReal.ofReal_zero]
      · simp only [hαdef]; rw [zero_smul, GExp_zero, sub_zero, hdL]
    have hεS : ρ/2 ∈ S := by
      refine ⟨⟨hεpos.le, hεL.le⟩, ?_, ?_⟩
      · rw [hαε]; exact hy₁
      · rw [hαε]; exact hy₁q
    have hbdd : BddAbove S := ⟨L, fun x hx => hx.1.2⟩
    have hsupS : sSup S ∈ S := hSclosed.csSup_mem ⟨0, h0S⟩ hbdd
    have hsup0 : 0 < sSup S := lt_of_lt_of_le hεpos (le_csSup hbdd hεS)
    -- the corner-cut step
    have hstep : ∀ t ∈ S, 0 < t → t < L → ∃ r : ℝ, 0 < r ∧ t + r ∈ S := by
      intro t ht ht0 htlt
      have htK : t ∈ Icc (0:ℝ) L := ht.1
      have htrad : Manifold.riemannianEDist I p (Gp t) = ENNReal.ofReal t := by
        rw [← hαGp t htK]; exact ht.2.1
      have htq : Manifold.riemannianEDist I (Gp t) q = ENNReal.ofReal (L - t) := by
        rw [← hαGp t htK]; exact ht.2.2
      -- the local theory at `Gp t`
      obtain ⟨ρz, hρz, hexpz⟩ :=
        exists_eq_expMap_of_riemannianEDist_lt (I := I) (cov := cov) hmet htor (Gp t)
      obtain ⟨ρz', hρz', hexpz_eq⟩ := exists_pos_GExp_eq_expMap (cov := cov) hmet (Gp t)
      set r : ℝ := min (min ρz ρz') (L - t) / 2 with hrdef
      have hrpos : 0 < r := by
        rw [hrdef]
        exact div_pos (lt_min (lt_min hρz hρz') (by linarith)) (by norm_num)
      have hrρz : r < ρz := by
        rw [hrdef]
        have h1 : min (min ρz ρz') (L - t) ≤ min ρz ρz' := min_le_left _ _
        have h2 : min ρz ρz' ≤ ρz := min_le_left _ _
        linarith
      have hrρz' : r < ρz' := by
        rw [hrdef]
        have h1 : min (min ρz ρz') (L - t) ≤ min ρz ρz' := min_le_left _ _
        have h2 : min ρz ρz' ≤ ρz' := min_le_right _ _
        linarith
      have hrLt : r < L - t := by
        rw [hrdef]
        have h1 : min (min ρz ρz') (L - t) ≤ L - t := min_le_right _ _
        linarith
      -- the sub-segment minimality
      have hsub_min : ∀ s ∈ Icc (0:ℝ) t, Manifold.riemannianEDist I p (α s) = ENNReal.ofReal s := by
        intro s hs
        have h1 : Manifold.riemannianEDist I p (α s) ≤ ENNReal.ofReal s := by
          have hγ : CMDiff[Icc (0:ℝ) s] 1 Gp :=
            (hGpsm.mono (fun q hq => ⟨by linarith [geodDelta_pos (cov := cov) hmet, hq.1],
              by linarith [geodDelta_pos (cov := cov) hmet, hq.2, hs.2, htK.2]⟩)).of_le
              (WithTop.coe_le_coe.mpr le_top)
          have hpath : Manifold.pathELength I Gp 0 s = ENNReal.ofReal s := by
            rw [pathELength_of_unit_speed (I := I) (γ := Gp) (a := 0) (b := s) (fun q hq => hGpsp q
              ⟨by linarith [geodDelta_pos (cov := cov) hmet, hq.1],
               by linarith [geodDelta_pos (cov := cov) hmet, hq.2, hs.2, htK.2]⟩), sub_zero]
          calc Manifold.riemannianEDist I p (α s) = Manifold.riemannianEDist I p (Gp s) := by
                rw [hαGp s ⟨hs.1, le_trans hs.2 htK.2⟩]
            _ ≤ Manifold.pathELength I Gp 0 s :=
                Manifold.riemannianEDist_le_pathELength hγ
                  (by rw [hGpdef]; exact hGpspec.1) rfl hs.1
            _ = ENNReal.ofReal s := hpath
        have h3 : Manifold.riemannianEDist I (α s) (α t) ≤ ENNReal.ofReal (t - s) := by
          have hγ : CMDiff[Icc s t] 1 Gp :=
            (hGpsm.mono (fun q hq => ⟨by linarith [geodDelta_pos (cov := cov) hmet, hq.1, hs.1],
              by linarith [geodDelta_pos (cov := cov) hmet, hq.2, htK.2]⟩)).of_le
              (WithTop.coe_le_coe.mpr le_top)
          have hpath : Manifold.pathELength I Gp s t = ENNReal.ofReal (t - s) :=
            pathELength_of_unit_speed (I := I) (γ := Gp) (a := s) (b := t) (fun q hq => hGpsp q
              ⟨by linarith [geodDelta_pos (cov := cov) hmet, hq.1, hs.1],
               by linarith [geodDelta_pos (cov := cov) hmet, hq.2, htK.2]⟩)
          calc Manifold.riemannianEDist I (α s) (α t) = Manifold.riemannianEDist I (Gp s) (Gp t) := by
                rw [hαGp s ⟨hs.1, le_trans hs.2 htK.2⟩, hαGp t htK]
            _ ≤ Manifold.pathELength I Gp s t :=
                Manifold.riemannianEDist_le_pathELength hγ rfl rfl hs.2
            _ = ENNReal.ofReal (t - s) := hpath
        have h5 : ENNReal.ofReal s + ENNReal.ofReal (t - s)
            ≤ Manifold.riemannianEDist I p (α s) + ENNReal.ofReal (t - s) := by
          calc ENNReal.ofReal s + ENNReal.ofReal (t - s) = ENNReal.ofReal (s + (t - s)) :=
                (ENNReal.ofReal_add hs.1 (sub_nonneg.mpr hs.2)).symm
            _ = ENNReal.ofReal t := by rw [show s + (t - s) = t from by ring]
            _ = Manifold.riemannianEDist I p (α t) := by rw [hαGp t htK]; exact htrad.symm
            _ ≤ Manifold.riemannianEDist I p (α s) + Manifold.riemannianEDist I (α s) (α t) :=
                Manifold.riemannianEDist_triangle (I := I)
            _ ≤ Manifold.riemannianEDist I p (α s) + ENNReal.ofReal (t - s) := add_le_add le_rfl h3
        exact le_antisymm h1 ((ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp h5)
      -- the minimiser on the sphere of radius `r` around `Gp t`
      obtain ⟨y', hy', hy'tri, hy'min⟩ :=
        Commons.Geometry.Manifold.riemannianEDist_min_on_sphere_enormSMul (I := I) (Gp t) q hrpos
          (exists_riemannianEDist_eq_ofReal_of_ne_top (I := I) (Gp t) q hrpos
            (continuous_riemannianEDist_left (I := I) (Gp t))
            (by rw [htq]; exact ENNReal.ofReal_ne_top)
            (by rw [htq]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hrLt))
          (continuous_riemannianEDist_left (I := I) (Gp t))
          (continuous_riemannianEDist_right (I := I) q)
          (by rw [htq]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hrLt)
      have hy'q : Manifold.riemannianEDist I y' q = ENNReal.ofReal (L - t - r) := by
        have h : Manifold.riemannianEDist I y' q + ENNReal.ofReal r = ENNReal.ofReal (L - t) := by
          rw [hy'tri, htq]
        have h2 : ENNReal.ofReal (L - t - r) + ENNReal.ofReal r = ENNReal.ofReal (L - t) := by
          rw [← ENNReal.ofReal_add (by linarith) (le_of_lt hrpos),
            show L - t - r + r = L - t from by ring]
        exact (ENNReal.add_left_inj ENNReal.ofReal_ne_top).mp (h.trans h2.symm)
      obtain ⟨w', hw'eq, hw'd⟩ := hexpz y' (by
        rw [hy']; exact (ENNReal.ofReal_lt_ofReal_iff hρz).mpr hrρz)
      have hw'norm : ‖w'‖ = r := by
        have h : ENNReal.ofReal ‖w'‖ = ENNReal.ofReal r := by rw [← hw'd, hy']
        exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg _) hrpos.le).mp h
      have hw'ne : w' ≠ 0 := by
        intro h0; rw [h0, norm_zero] at hw'norm; linarith
      set η : TangentSpace I (Gp t) := unitOf w' hw'ne with hηdef
      have hηnorm : ‖η‖ = 1 := unitOf_norm w' hw'ne
      have hrη : r • η = w' := by
        rw [hηdef, unitOf, smul_smul, hw'norm, mul_inv_cancel₀ (ne_of_gt hrpos), one_smul]
      have hy'GExp : y' = GExp (cov := cov) hmet (Gp t) (r • η) := by
        rw [hrη, hexpz_eq w' (by rw [hw'norm]; exact hrρz'), hw'eq]
      -- the unit velocity of the ray at `t`
      have htIoo : t ∈ Ioo (-(geodDelta (cov := cov) hmet)) (L + geodDelta (cov := cov) hmet) :=
        Set.mem_Ioo.mpr ⟨by linarith [geodDelta_pos (cov := cov) hmet, ht0.le],
          by linarith [htK.2, geodDelta_pos (cov := cov) hmet]⟩
      set ξ : TangentSpace I (Gp t) := curveVelocity (I := I) Gp t with hξdef
      have hξnorm : ‖ξ‖ = 1 := hGpsp t htIoo
      -- the corner cut
      have hξη : ξ = η := by
        by_contra hne
        obtain ⟨δc, hδc, hcut⟩ := corner_cut (cov := cov) hmet (Gp t) hξnorm hηnorm hne
        set τ : ℝ := min (min δc t) r / 2 with hτdef
        have hτpos : 0 < τ := by
          rw [hτdef]
          exact div_pos (lt_min (lt_min hδc ht0) hrpos) (by norm_num)
        have hτδ : τ < δc := by
          rw [hτdef]
          have h1 : min (min δc t) r ≤ min δc t := min_le_left _ _
          have h2 : min δc t ≤ δc := min_le_left _ _
          linarith
        have hτt : τ < t := by
          rw [hτdef]
          have h1 : min (min δc t) r ≤ min δc t := min_le_left _ _
          have h2 : min δc t ≤ t := min_le_right _ _
          linarith
        have hτr : τ < r := by
          rw [hτdef]
          have h1 : min (min δc t) r ≤ r := min_le_right _ _
          linarith
        set A : M := GExp (cov := cov) hmet (Gp t) ((-τ) • ξ) with hAdef
        set B : M := GExp (cov := cov) hmet (Gp t) (τ • η) with hBdef
        have hAcut : Manifold.riemannianEDist I A B < ENNReal.ofReal (2 * τ) := hcut τ hτpos hτδ
        have hAeq' : GExp (cov := cov) hmet (Gp t)
            ((-τ) • curveVelocity (I := I) Gp t) = Gp (t - τ) :=
          GExp_neg_smul_curveVelocity_geodCurve (cov := cov) hmet p hunorm (T := L) hLnn
            ht0.le htK.2 (le_of_lt hτpos) hτt.le
        have hAeq : A = α (t - τ) := by
          rw [hAdef, hξdef]
          exact hAeq'.trans (hαGp (t - τ) ⟨by linarith, by linarith [htK.2]⟩).symm
        have hAx : Manifold.riemannianEDist I p A ≤ ENNReal.ofReal (t - τ) := by
          rw [hAeq]; exact (hsub_min (t - τ) ⟨by linarith, by linarith⟩).le
        have hBy : Manifold.riemannianEDist I B (GExp (cov := cov) hmet (Gp t) (r • η))
            ≤ ENNReal.ofReal (r - τ) :=
          riemannianEDist_GExp_ray_le (cov := cov) hmet (Gp t) hηnorm hτpos.le hτr.le
        have hB2 : Manifold.riemannianEDist I B q
            ≤ Manifold.riemannianEDist I B (GExp (cov := cov) hmet (Gp t) (r • η))
              + Manifold.riemannianEDist I (GExp (cov := cov) hmet (Gp t) (r • η)) q :=
          Manifold.riemannianEDist_triangle (I := I)
        have h3 : Manifold.riemannianEDist I (GExp (cov := cov) hmet (Gp t) (r • η)) q
            = ENNReal.ofReal (L - t - r) := by
          rw [← hy'GExp]; exact hy'q
        have hByq : Manifold.riemannianEDist I B q
            ≤ ENNReal.ofReal (r - τ) + ENNReal.ofReal (L - t - r) :=
          hB2.trans (add_le_add hBy (le_of_eq h3))
        have htri1 : Manifold.riemannianEDist I p q
            ≤ (Manifold.riemannianEDist I p A + Manifold.riemannianEDist I A B)
              + Manifold.riemannianEDist I B q := by
          calc Manifold.riemannianEDist I p q
              ≤ Manifold.riemannianEDist I p A + Manifold.riemannianEDist I A q :=
                Manifold.riemannianEDist_triangle (I := I)
            _ ≤ Manifold.riemannianEDist I p A
                  + (Manifold.riemannianEDist I A B + Manifold.riemannianEDist I B q) :=
                add_le_add le_rfl (Manifold.riemannianEDist_triangle (I := I))
            _ = (Manifold.riemannianEDist I p A + Manifold.riemannianEDist I A B)
                  + Manifold.riemannianEDist I B q := by rw [add_assoc]
        have hlt2 : (Manifold.riemannianEDist I p A + Manifold.riemannianEDist I A B)
              + Manifold.riemannianEDist I B q
            < (ENNReal.ofReal (t - τ) + ENNReal.ofReal (2 * τ))
              + (ENNReal.ofReal (r - τ) + ENNReal.ofReal (L - t - r)) := by
          have hXY : Manifold.riemannianEDist I p A + Manifold.riemannianEDist I A B
              < ENNReal.ofReal (t - τ) + ENNReal.ofReal (2 * τ) :=
            ENNReal.add_lt_add_of_le_of_lt
              (ne_of_lt (lt_of_le_of_lt hAx ENNReal.ofReal_lt_top)) hAx hAcut
          have hZne : Manifold.riemannianEDist I B q ≠ ⊤ :=
            ne_of_lt (lt_of_le_of_lt hByq
              (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩))
          exact ENNReal.add_lt_add_of_lt_of_le hZne hXY hByq
        have hsum : (ENNReal.ofReal (t - τ) + ENNReal.ofReal (2 * τ))
              + (ENNReal.ofReal (r - τ) + ENNReal.ofReal (L - t - r)) = ENNReal.ofReal L := by
          rw [← ENNReal.ofReal_add (show 0 ≤ t - τ by linarith) (show 0 ≤ 2 * τ by linarith),
            ← ENNReal.ofReal_add (show 0 ≤ r - τ by linarith) (show 0 ≤ L - t - r by linarith),
            ← ENNReal.ofReal_add (show 0 ≤ t - τ + 2 * τ by linarith)
              (show 0 ≤ r - τ + (L - t - r) by linarith),
            show t - τ + 2 * τ + (r - τ + (L - t - r)) = L from by ring]
        exact absurd (lt_of_le_of_lt htri1 (hlt2.trans_eq hsum)) (not_lt.mpr (le_of_eq hdL.symm))
      -- conclude
      have hyt : Manifold.riemannianEDist I p y' = ENNReal.ofReal (t + r) := by
        have h1 : Manifold.riemannianEDist I p y' ≤ ENNReal.ofReal (t + r) := by
          calc Manifold.riemannianEDist I p y'
              ≤ Manifold.riemannianEDist I p (Gp t) + Manifold.riemannianEDist I (Gp t) y' :=
                Manifold.riemannianEDist_triangle (I := I)
            _ = ENNReal.ofReal t + ENNReal.ofReal r := by rw [htrad, hy']
            _ = ENNReal.ofReal (t + r) := (ENNReal.ofReal_add ht0.le hrpos.le).symm
        have h2 : ENNReal.ofReal (t + r) ≤ Manifold.riemannianEDist I p y' := by
          have h3 : ENNReal.ofReal (t + r) + ENNReal.ofReal (L - t - r) ≤ ENNReal.ofReal L := by
            rw [← ENNReal.ofReal_add (show 0 ≤ t + r by linarith)
              (show 0 ≤ L - t - r by linarith), show t + r + (L - t - r) = L from by ring]
          have h4 : ENNReal.ofReal L
              ≤ Manifold.riemannianEDist I p y' + Manifold.riemannianEDist I y' q := by
            rw [← hdL]
            exact Manifold.riemannianEDist_triangle (I := I) (x := p) (y := y') (z := q)
          rw [hy'q] at h4
          exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp (le_trans h3 h4)
        exact le_antisymm h1 h2
      have hytq : Manifold.riemannianEDist I y' q = ENNReal.ofReal (L - (t + r)) := by
        rw [hy'q, show L - t - r = L - (t + r) from by ring]
      have hα : α (t + r) = y' := by
        have h1 : α (t + r) = Gp (t + r) :=
          hαGp (t + r) ⟨by linarith, by linarith [hrLt]⟩
        have h2 : GExp (cov := cov) hmet (Gp t) (r • curveVelocity (I := I) Gp t) = Gp (t + r) :=
          GExp_geodCurve_add (cov := cov) hmet p hunorm (T := L) hLnn ht0.le htK.2 hrpos.le
            (by linarith [hrLt])
        rw [h1, ← h2, ← hξdef, hξη]
        exact hy'GExp.symm
      have hmem : t + r ∈ S := by
        change t + r ∈ Icc (0:ℝ) L
          ∧ Manifold.riemannianEDist I p (α (t + r)) = ENNReal.ofReal (t + r)
          ∧ Manifold.riemannianEDist I (α (t + r)) q = ENNReal.ofReal (L - (t + r))
        exact ⟨⟨by linarith, by linarith [hrLt]⟩, by rw [hα]; exact hyt, by rw [hα]; exact hytq⟩
      exact ⟨r, hrpos, hmem⟩
    -- assemble
    have hsupL : sSup S = L := by
      by_contra hne
      have hlt : sSup S < L := lt_of_le_of_ne hsupS.1.2 hne
      obtain ⟨r, hrpos, hrS⟩ := hstep (sSup S) hsupS hsup0 hlt
      have hle : sSup S + r ≤ sSup S := le_csSup hbdd hrS
      linarith
    have hLS : L ∈ S := hsupL ▸ hsupS
    have hαLq : α L = q := by
      have h0 : Manifold.riemannianEDist I (α L) q = 0 := by
        rw [hLS.2.2, show L - L = 0 from by ring, ENNReal.ofReal_zero]
      exact (Submission.EDist.riemannianEDist_eq_zero_iff (I := I)).mp h0
    refine ⟨L • u, ?_, ?_⟩
    · have h := hαLq
      simp only [hαdef] at h
      exact h
    · rw [hdL, show ‖L • u‖ = L from by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hLnn, hunorm, mul_one]]

/-- **Rays below the injectivity radius are minimising — the `PathConnectedSpace`-free form.**

This is `Submission.InjRadius.edist_GExp_eq_norm_of_injAtLeast` with the hypotheses
`[PathConnectedSpace M] [RegularSpace M]` and `hune : u ≠ 0` removed (`RegularSpace M` is derivable
from `T2Space`; the others were only used to invoke Hopf–Rinow
`Submission.HopfRinow2.exists_geodesic_riemannianEDist_eq`).

Intended proof: reduce to a *localised* Hopf–Rinow.  If `d(x, GExp x u) < ‖u‖`, then
`d(x, GExp x u) < ⊤` (its value is bounded by the ray bound `Submission.CutWitness.edist_GExp_le_norm`),
so it suffices to prove the following lemma (in the same file, by copying the proof of
`Submission.HopfRinow2.exists_geodesic_riemannianEDist_eq` and replacing the two uses of
`PathConnectedSpace`/`ConnectedSpace`, namely `riemannianEDist_lt_top` and
`Submission.HopfRinow.exists_riemannianEDist_eq_ofReal`, by the finite-distance hypothesis — the
latter by extracting a `C^1` path from `Manifold.exists_lt_of_riemannianEDist_lt` with `r = ⊤` and
the intermediate value theorem; the copied proof's calls to
`continuous_riemannianEDist_left/right` need `haveI : RegularSpace M := inferInstance`):

  `∃ v, GExp hmet p v = q ∧ d(p,q) = ofReal ‖v‖`   from `d(p,q) < ⊤`.

With that, the conclusion is the argument already in `Submission.Klingenberg.edist_GExp_eq_norm_of_injOn`:
if `d(x, GExp x u) < ofReal ‖u‖` then the minimising vector `v` has `‖v‖ = d(x,GExp x u) < ‖u‖ < r`,
and `GExp x v = GExp x u` with both norms `< r`, so injectivity gives `v = u`, whence
`‖v‖ = ‖u‖`, a contradiction.  The reverse inequality is the ray bound
`Submission.CutWitness.edist_GExp_le_norm`. -/
theorem edist_GExp_eq_norm_of_injAtLeast
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {x : M} {r : ℝ} (h : Submission.InjRadius.InjAtLeast hmet x r)
    {u : TangentSpace I x} (hu : ‖u‖ < r) :
    Manifold.riemannianEDist I x (Submission.GlobalExp.GExp (cov := cov) hmet x u)
      = ENNReal.ofReal ‖u‖ := by
  refine le_antisymm
    (Submission.CutWitness.edist_GExp_le_norm (cov := cov) (p := x) hmet u) ?_
  by_contra hcon
  rw [not_le] at hcon
  have hfin : Manifold.riemannianEDist I x (Submission.GlobalExp.GExp (cov := cov) hmet x u)
      < ⊤ := lt_of_lt_of_le hcon ENNReal.ofReal_lt_top.le
  obtain ⟨w, hwG, hwd⟩ :=
    exists_geodesic_riemannianEDist_eq_of_lt_top (cov := cov) hmet htor x
      (Submission.GlobalExp.GExp (cov := cov) hmet x u) hfin
  rw [hwd] at hcon
  have hwlt : ‖w‖ < ‖u‖ := by
    have h' := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top).mpr hcon
    simpa [ENNReal.toReal_ofReal (norm_nonneg w), ENNReal.toReal_ofReal (norm_nonneg u)] using h'
  have hwu : w = u := h w u (lt_trans hwlt hu) hu (by rw [hwG])
  rw [hwu] at hwlt
  exact lt_irrefl _ hwlt

end Work.EvenBound.FarthestPoint
