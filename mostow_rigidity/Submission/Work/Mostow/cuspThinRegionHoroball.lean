import Mathlib
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.cuspParDispDefs
import Submission.Work.Mostow.cuspThinRegionBasic
import Submission.Work.Mostow.cuspThinRegion_eq_parDisp
import Submission.Work.Mostow.parDisp_lipschitz_invariant
import Submission.Work.Mostow.geomFiniteMultThick
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.hptOf_level
import Submission.Work.Mostow.cuspHoroDefs
import Submission.Work.Mostow.cuspFrontierShortBound
import Submission.Work.Mostow.cuspFrontierBallUniform
import Submission.Work.Mostow.cuspFrontierClassesB
import Submission.Work.Mostow.flatEllipticGap

/-!
# Every Margulis region at a cusp contains a horoball

The target of this file is

`cuspThinRegion_horoball Γ ξ : ∀ ε > 0, ∃ t, horoball ξ t ⊆ cuspThinRegion Γ ξ ε`

for a lattice `Γ`, a parabolic fixed point `ξ ∈ parFixed Γ` and every `ε > 0`.

By `cuspThinRegion_eq_parDisp` the Margulis region at `ξ` is
`{u | lev ξ u * parDisp Γ ξ (yc ξ u) < cEps ε}`, so it suffices to bound `parDisp Γ ξ` on the flat
space.  The route (`CUSP_CRUX_NOTES.md`) is a contradiction:

* if `parDisp Γ ξ` is unbounded, take frontier points `u_k` of `cuspThinRegion Γ ξ ε` with
  `lev ξ u_k → 0`;
* at a frontier point the `(ε/2)`-short elements are elliptics of `Γ_ξ` with separated rotation
  parts, so the short set has at most `N` elements (`cuspFrontierShortBound`, fed by the elliptic
  gap `cuspEllipticGapV2`);
* by `MultThickProp` (proved as `Work.Mostow.geomFiniteMultThick`) the `u_k` are `Γ`-equivalent
  to points of a fixed compact set;
* only finitely many cusp classes meet that compact set (`cuspFrontierClassesB`, using the
  separation of the Margulis regions at distinct cusps), so after relabelling `sigma_k • u_k` lies
  in a fixed compact set with `sigma_k ∈ Γ_ξ` — but `Γ_ξ` preserves the level `lev ξ`, which tends
  to `0` along the `u_k`, and a compact subset of the chart has `lev ξ ≥ δ > 0` everywhere.

Hence `parDisp Γ ξ ≤ M` on `ξ^⊥`, and `horoball ξ (log (cEps ε / max M 1)) ⊆ cuspThinRegion Γ ξ ε`.
-/

set_option maxHeartbeats 4000000

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Metric
open scoped Topology

namespace Work.Mostow

noncomputable section

variable {n : ℕ}

lemma inner_yc_self {ξ u : E n} (hξ : ξ ∈ Sph n) : inner ℝ (yc ξ u) ξ = 0 := by
  have h1 : inner ℝ ξ ξ = 1 := by
    rw [real_inner_self_eq_norm_sq]
    have h : ‖ξ‖ = 1 := by simpa [Sph, mem_sphere, dist_eq_norm] using hξ
    rw [h, one_pow]
  simp only [yc, wc, real_inner_smul_left, inner_sub_left, h1, mul_one, sub_self, mul_zero]

lemma continuous_lev_ξ (ξ : E n) : Continuous (fun u : E n => lev ξ u) := by
  have h : (fun u : E n => lev ξ u) = fun u => Real.sqrt (1 + ‖u‖ ^ 2) - inner ℝ u ξ := by
    funext u; rw [lev, tpart]
  rw [h]
  exact (Real.continuous_sqrt.comp (continuous_const.add (continuous_norm.pow 2))).sub
    (continuous_id.inner continuous_const)

lemma continuous_yc_ξ {ξ : E n} (hξ : ξ ∈ Sph n) : Continuous (fun u : E n => yc ξ u) := by
  have h : (fun u : E n => yc ξ u) = fun u => (lev ξ u)⁻¹ • wc ξ u := by
    funext u; rw [yc]
  rw [h]
  have hlev : Continuous (fun u : E n => lev ξ u) := continuous_lev_ξ ξ
  refine Continuous.smul (hlev.inv₀ (fun u => ne_of_gt (lev_pos ξ hξ u))) ?_
  show Continuous (fun u : E n => u - inner ℝ u ξ • ξ)
  fun_prop

/-- On a compact subset of the chart, `lev ξ` is bounded below by a positive constant. -/
lemma lev_pos_lb_of_isCompact {ξ : E n} (hξ : ξ ∈ Sph n) {K : Set (E n)} (hK : IsCompact K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v ∈ K, δ ≤ lev ξ v := by
  by_cases hne : K.Nonempty
  · obtain ⟨v₀, hv₀⟩ := hne
    obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
    have hRnn : 0 ≤ R := le_trans (norm_nonneg v₀) (hR v₀ hv₀)
    have hξn : ‖ξ‖ = 1 := by simpa [Sph, mem_sphere, dist_eq_norm] using hξ
    have key : ∀ r : ℝ, 0 ≤ r → Real.sqrt (1 + r ^ 2) - r
        = (Real.sqrt (1 + r ^ 2) + r)⁻¹ := by
      intro r hr
      have h1 : Real.sqrt (1 + r ^ 2) ^ 2 = 1 + r ^ 2 := Real.sq_sqrt (by positivity)
      exact eq_inv_of_mul_eq_one_right (by nlinarith [Real.sqrt_nonneg (1 + r ^ 2)])
    have hdenpos : ∀ r : ℝ, 0 ≤ r → 0 < Real.sqrt (1 + r ^ 2) + r := by
      intro r hr
      have h1 : Real.sqrt (1 + r ^ 2) ^ 2 = 1 + r ^ 2 := Real.sq_sqrt (by positivity)
      nlinarith [Real.sqrt_nonneg (1 + r ^ 2)]
    refine ⟨Real.sqrt (1 + R ^ 2) - R, ?_, ?_⟩
    · rw [key R hRnn]
      exact inv_pos.mpr (hdenpos R hRnn)
    · intro v hv
      have hvR : ‖v‖ ≤ R := hR v hv
      have hin : inner ℝ v ξ ≤ ‖v‖ := by
        have h := abs_real_inner_le_norm v ξ
        rw [hξn, mul_one] at h
        linarith [le_abs_self (inner ℝ v ξ)]
      have hsq : Real.sqrt (1 + ‖v‖ ^ 2) ≤ Real.sqrt (1 + R ^ 2) := by
        apply Real.sqrt_le_sqrt
        nlinarith [hvR, norm_nonneg v]
      have hmono : Real.sqrt (1 + R ^ 2) - R ≤ Real.sqrt (1 + ‖v‖ ^ 2) - ‖v‖ := by
        rw [key R hRnn, key ‖v‖ (norm_nonneg v), inv_le_inv₀ (hdenpos R hRnn)
          (hdenpos ‖v‖ (norm_nonneg v))]
        linarith
      have hlev : lev ξ v = Real.sqrt (1 + ‖v‖ ^ 2) - inner ℝ v ξ := by
        rw [lev, tpart]
      rw [hlev]
      linarith
  · refine ⟨1, one_pos, ?_⟩
    intro v hv
    exact absurd ⟨v, hv⟩ hne

/-- The frontier of the Margulis region is the level set of `lev η · parDisp Γ η (yc η ·)`. -/
lemma frontier_parDisp_eq (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1))
    (hdisc : IsDiscrete (SetLike.coe Γ))
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ Work.Mostow.parFixed Γ →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = 0)
    {η : Submission.Mostow.E n} (hη : η ∈ Work.Mostow.parFixed Γ)
    {ε : ℝ} (hε : 0 < ε) {u : Submission.Mostow.E n}
    (hu : u ∈ frontier (Work.Mostow.cuspThinRegion Γ η ε)) :
    Work.Mostow.lev η u * Work.Mostow.parDisp Γ η (Work.Mostow.yc η u) = Work.Mostow.cEps ε := by
  have hηS : η ∈ Sph n := hη.1
  obtain ⟨-, hiff⟩ := cuspThinRegion_eq_parDisp n hA hI Γ hdisc hvan hη
  have hL := (parDisp_lipschitz_invariant n hA hI Γ hvan hη).1
  have hcontlev : Continuous (fun v : E n => lev η v) := continuous_lev_ξ η
  have hcontyc : Continuous (fun v : E n => yc η v) := continuous_yc_ξ hηS
  have hcontpar : Continuous (fun v : E n => parDisp Γ η (yc η v)) := by
    have hLo : ContinuousOn (parDisp Γ η) {y : E n | inner ℝ y η = 0} :=
      (parDisp_lipschitz_invariant n hA hI Γ hvan hη).1.continuousOn
    have := hLo.comp_continuous hcontyc (fun v => inner_yc_self hηS)
    simpa [Function.comp_def] using this
  have hcontf : Continuous (fun v : E n => lev η v * parDisp Γ η (yc η v)) :=
    hcontlev.mul hcontpar
  have hset : cuspThinRegion Γ η ε
      = {v : E n | lev η v * parDisp Γ η (yc η v) < cEps ε} := by
    ext v; exact hiff ε hε v
  have hopen : IsOpen (cuspThinRegion Γ η ε) := by
    rw [hset]; exact isOpen_lt hcontf continuous_const
  have hnotin : u ∉ cuspThinRegion Γ η ε := by
    intro hmem
    have : u ∈ interior (cuspThinRegion Γ η ε) := by rwa [hopen.interior_eq]
    exact hu.2 this
  have hge : cEps ε ≤ lev η u * parDisp Γ η (yc η u) := by
    by_contra hlt
    push_neg at hlt
    exact hnotin (hset ▸ Set.mem_ofPred_eq.mpr hlt)
  have hle : lev η u * parDisp Γ η (yc η u) ≤ cEps ε := by
    have hclosed : IsClosed {v : E n | lev η v * parDisp Γ η (yc η v) ≤ cEps ε} :=
      isClosed_le hcontf continuous_const
    have hsub : cuspThinRegion Γ η ε
        ⊆ {v : E n | lev η v * parDisp Γ η (yc η v) ≤ cEps ε} := by
      intro v hv
      rw [hset] at hv
      exact le_of_lt (Set.mem_ofPred_eq.mp hv)
    exact (hclosed.closure_subset_iff.mpr hsub) hu.1
  linarith

lemma cEps_pos' {ε : ℝ} (hε : 0 < ε) : 0 < cEps ε := by
  rw [cEps, Real.sqrt_pos]
  have h : 1 < Real.cosh ε := Real.one_lt_cosh.mpr (ne_of_gt hε)
  linarith

/-- **`parDisp` is bounded on the flat space.** -/
theorem parDisp_bounded (n : ℕ) (hn : 2 ≤ n) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)) (hΓ : Submission.Mostow.HypLattice Γ)
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ Work.Mostow.parFixed Γ →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = 0)
    {ξ : Submission.Mostow.E n} (hξ : ξ ∈ Work.Mostow.parFixed Γ)
    (hshort : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ N : ℕ, ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ u : Submission.Mostow.E n,
      Work.Mostow.lev ξ u * Work.Mostow.parDisp Γ ξ (Work.Mostow.yc ξ u) = Work.Mostow.cEps ε →
      {γ : Γ | Submission.Mostow.hdist u
        ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • u) < ε / 2}.ncard ≤ N)
    (hballU : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ r : ℝ, 0 < r ∧ ∀ η : Submission.Mostow.E n,
      η ∈ Work.Mostow.parFixed Γ → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ u : Submission.Mostow.E n,
      Work.Mostow.lev η u * Work.Mostow.parDisp Γ η (Work.Mostow.yc η u) = Work.Mostow.cEps ε →
      ∀ w : Submission.Mostow.E n, Submission.Mostow.hdist u w ≤ r * ε →
        w ∈ Work.Mostow.cuspThinRegion Γ η (2 * ε))
    (hsep0 : ∃ εsep : ℝ, 0 < εsep ∧ ∀ η ∈ Work.Mostow.parFixed Γ,
      ∀ η' ∈ Work.Mostow.parFixed Γ, η ≠ η' →
      Disjoint (Work.Mostow.cuspThinRegion Γ η εsep)
        (Work.Mostow.cuspThinRegion Γ η' εsep))
    (hccl : ∀ (εsep : ℝ), 0 < εsep →
      (∀ η ∈ Work.Mostow.parFixed Γ, ∀ η' ∈ Work.Mostow.parFixed Γ, η ≠ η' →
        Disjoint (Work.Mostow.cuspThinRegion Γ η εsep)
          (Work.Mostow.cuspThinRegion Γ η' εsep)) →
      ∀ (εB : ℝ), 0 < εB → ∀ (r : ℝ), 0 < r →
      (∀ η ∈ Work.Mostow.parFixed Γ, ∀ ε' : ℝ, 0 < ε' → ε' ≤ εB →
        ∀ u : Submission.Mostow.E n,
        Work.Mostow.lev η u * Work.Mostow.parDisp Γ η (Work.Mostow.yc η u) =
          Work.Mostow.cEps ε' →
        ∀ w : Submission.Mostow.E n, Submission.Mostow.hdist u w ≤ r * ε' →
          w ∈ Work.Mostow.cuspThinRegion Γ η (2 * ε')) →
      ∀ (ε : ℝ), 0 < ε → ε ≤ εB → 2 * ε ≤ εsep →
      (∀ η ∈ Work.Mostow.parFixed Γ, ∀ u : Submission.Mostow.E n,
        u ∈ frontier (Work.Mostow.cuspThinRegion Γ η ε) →
        Work.Mostow.lev η u * Work.Mostow.parDisp Γ η (Work.Mostow.yc η u) =
          Work.Mostow.cEps ε) →
      ∀ (K : Set (Submission.Mostow.E n)), IsCompact K →
      {η : Submission.Mostow.E n | η ∈ Work.Mostow.parFixed Γ ∧
        (frontier (Work.Mostow.cuspThinRegion Γ η ε) ∩ K).Nonempty}.Finite)
    (hcsmul : ∀ (γ : Γ) (ε : ℝ),
      (fun u : Submission.Mostow.E n =>
        (γ : LeanEval.Geometry.MostowRigidity.PO n 1) • u) ''
        Work.Mostow.cuspThinRegion Γ ξ ε
        = Work.Mostow.cuspThinRegion Γ
          (Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ) ε) :
    ∃ M : ℝ, ∀ y : Submission.Mostow.E n, inner ℝ y ξ = 0 →
      Work.Mostow.parDisp Γ ξ y ≤ M := by
  classical
  have hξS : ξ ∈ Sph n := hξ.1
  have hA' : POBasic n := POBasic.ofProp hA
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  have hdisc : IsDiscrete (SetLike.coe Γ) := hΓ.1
  obtain ⟨εS, hεSpos, N, hN⟩ := hshort
  obtain ⟨εB, hεBpos, r, hr, hball⟩ := hballU
  obtain ⟨εsep, hεseppos, hsep⟩ := hsep0
  let ε : ℝ := min (min εS εB) (min (1 / 4) (εsep / 4))
  have hεpos : 0 < ε := by
    have h1 : (0 : ℝ) < min εS εB := lt_min hεSpos hεBpos
    have h2 : (0 : ℝ) < min (1 / 4) (εsep / 4) := lt_min (by norm_num) (by linarith)
    exact lt_min h1 h2
  have hεleS : ε ≤ εS := le_trans (min_le_left _ _) (min_le_left _ _)

  have hεleB : ε ≤ εB := le_trans (min_le_left _ _) (min_le_right _ _)
  have hεle1 : ε ≤ 1 := by
    have h1 : ε ≤ (1 / 4 : ℝ) := le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have h2ε : 2 * ε ≤ εsep := by
    have h1 : ε ≤ εsep / 4 := le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  have hmt := geomFiniteMultThick n (by omega) hA hI Γ hΓ
  obtain ⟨K, hKc, hK⟩ := hmt (ε / 2) (by positivity) N
  by_contra hcon
  push_neg at hcon
  choose Y hYperp hYgt using hcon
  let Yk : ℕ → E n := fun k => Y ((k : ℝ) + 1)
  have hYkp : ∀ k : ℕ, inner ℝ (Yk k) ξ = 0 := fun k => hYperp ((k : ℝ) + 1)
  have hYkpos : ∀ k : ℕ, 0 < parDisp Γ ξ (Yk k) :=
    fun k => lt_trans (by positivity) (hYgt ((k : ℝ) + 1))
  let L : ℕ → ℝ := fun k => cEps ε / parDisp Γ ξ (Yk k)
  have hLpos : ∀ k : ℕ, 0 < L k := fun k => div_pos (cEps_pos' hεpos) (hYkpos k)
  let u : ℕ → E n := fun k => hptOf ξ (Yk k) (L k)
  have hulev : ∀ k : ℕ, lev ξ (u k) = L k :=
    fun k => (hptOf_level ξ hξS (L k) (hLpos k) (Yk k) (hYkp k)).1
  have huyc : ∀ k : ℕ, yc ξ (u k) = Yk k :=
    fun k => (hptOf_level ξ hξS (L k) (hLpos k) (Yk k) (hYkp k)).2
  have hfront : ∀ k : ℕ, lev ξ (u k) * parDisp Γ ξ (yc ξ (u k)) = cEps ε := by
    intro k
    rw [hulev k, huyc k]
    show cEps ε / parDisp Γ ξ (Yk k) * parDisp Γ ξ (Yk k) = cEps ε
    rw [div_mul_cancel₀ _ (ne_of_gt (hYkpos k))]
  have hfinshort : ∀ k : ℕ, {γ : Γ | hdist (u k) ((γ : PO n 1) • (u k)) < ε / 2}.Finite := by
    intro k
    refine (finite_nearStab (POBasic.ofProp hA) (HypIsoData.ofProp hI) hdisc
      (2 * hdist (0 : E n) (u k) + ε / 2)).subset ?_
    intro γ hγ
    have h1 : hdist (0 : E n) ((γ : PO n 1) • (0 : E n))
        ≤ hdist (0 : E n) ((γ : PO n 1) • (u k))
          + hdist ((γ : PO n 1) • (u k)) ((γ : PO n 1) • (0 : E n)) := hI'.triangle _ _ _
    have h2 : hdist ((γ : PO n 1) • (u k)) ((γ : PO n 1) • (0 : E n)) = hdist (u k) (0 : E n) :=
      hI'.isom_smul _ _ _
    have h3 : hdist (0 : E n) ((γ : PO n 1) • (u k))
        ≤ hdist (0 : E n) (u k) + hdist (u k) ((γ : PO n 1) • (u k)) := hI'.triangle _ _ _
    have h4 : hdist (u k) (0 : E n) = hdist (0 : E n) (u k) := hI'.symm _ _
    rw [h2, h4] at h1
    have hγ' : hdist (u k) ((γ : PO n 1) • (u k)) < ε / 2 := hγ
    show hdist (0 : E n) ((γ : PO n 1) • (0 : E n)) ≤ 2 * hdist (0 : E n) (u k) + ε / 2
    linarith
  choose γk hγkK using fun k => hK (u k) ⟨hfinshort k, hN ε hεpos (le_trans hεleS le_rfl) (u k) (hfront k)⟩
  have hufront : ∀ k : ℕ, u k ∈ frontier (cuspThinRegion Γ ξ ε) := by
    intro k
    obtain ⟨-, hiff⟩ := cuspThinRegion_eq_parDisp n hA hI Γ hdisc hvan hξ
    have hset : cuspThinRegion Γ ξ ε = {v : E n | lev ξ v * parDisp Γ ξ (yc ξ v) < cEps ε} := by
      ext v; exact hiff ε hεpos v
    refine ⟨?_, ?_⟩
    · have hnat : Filter.Tendsto (fun m : ℕ => 1 - 1 / ((m : ℝ) + 2)) Filter.atTop (𝓝 1) := by
        have ht : Filter.Tendsto (fun m : ℕ => ((m : ℝ) + 2)) Filter.atTop Filter.atTop := by
          rw [Filter.tendsto_atTop_atTop]
          intro b
          refine ⟨⌈b⌉₊, fun m hm => ?_⟩
          have h1 : (⌈b⌉₊ : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
          linarith [Nat.le_ceil b]
        have h0 : Filter.Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 2)) Filter.atTop (𝓝 0) :=
          Filter.Tendsto.div_atTop tendsto_const_nhds ht
        simpa using Filter.Tendsto.sub tendsto_const_nhds h0
      have hcont : ContinuousAt (fun D : ℝ => hptOf ξ (Yk k) D) (L k) := by
        have h1 : ContinuousAt
            (fun D : ℝ => (1 + D ^ 2 * ‖Yk k‖ ^ 2) / (2 * D) - D / 2) (L k) := by
          refine ContinuousAt.sub ?_ (continuousAt_id.div_const 2)
          refine ContinuousAt.div ?_ (continuousAt_const.mul continuousAt_id) ?_
          · exact continuousAt_const.add ((continuousAt_id.pow 2).mul continuousAt_const)
          · intro h
            have h2 : (2 : ℝ) * L k = 0 := h
            linarith [hLpos k]
        have h2 : ContinuousAt (fun D : ℝ => D • (Yk k)) (L k) :=
          continuousAt_id.smul continuousAt_const
        show ContinuousAt (fun D : ℝ =>
          ((1 + D ^ 2 * ‖Yk k‖ ^ 2) / (2 * D) - D / 2) • ξ + D • (Yk k)) (L k)
        exact (h1.smul continuousAt_const).add h2
      have hlim : Filter.Tendsto (fun m : ℕ => hptOf ξ (Yk k) (L k * (1 - 1 / ((m : ℝ) + 2))))
          Filter.atTop (𝓝 (u k)) := by
        have h3 : Filter.Tendsto (fun m : ℕ => L k * (1 - 1 / ((m : ℝ) + 2)))
            Filter.atTop (𝓝 (L k * 1)) := Filter.Tendsto.const_mul (L k) hnat
        rw [mul_one] at h3
        have h4 := hcont.tendsto.comp h3
        simpa [u, Function.comp_def, one_div] using h4
      refine mem_closure_of_tendsto hlim ?_
      filter_upwards with m
      rw [hset, Set.mem_ofPred_eq]
      have hDpos : 0 < L k * (1 - 1 / ((m : ℝ) + 2)) := by
        have hm : (0 : ℝ) < (m : ℝ) + 2 := by positivity
        have h1 : 1 / ((m : ℝ) + 2) < 1 := by rw [div_lt_one hm]; linarith
        exact mul_pos (hLpos k) (by linarith)
      have hlt : 1 - 1 / ((m : ℝ) + 2) < 1 := by
        have hm : (0 : ℝ) < (m : ℝ) + 2 := by positivity
        have h1 : 0 < 1 / ((m : ℝ) + 2) := by positivity
        linarith
      have h1 := (hptOf_level ξ hξS (L k * (1 - 1 / ((m : ℝ) + 2))) hDpos (Yk k) (hYkp k)).1
      have h2 := (hptOf_level ξ hξS (L k * (1 - 1 / ((m : ℝ) + 2))) hDpos (Yk k) (hYkp k)).2
      rw [h1, h2]
      have hcoef : L k * (1 - 1 / ((m : ℝ) + 2)) * parDisp Γ ξ (Yk k)
          = (1 - 1 / ((m : ℝ) + 2)) * cEps ε := by
        show cEps ε / parDisp Γ ξ (Yk k) * (1 - 1 / ((m : ℝ) + 2)) * parDisp Γ ξ (Yk k)
          = (1 - 1 / ((m : ℝ) + 2)) * cEps ε
        rw [mul_comm (cEps ε / parDisp Γ ξ (Yk k)) (1 - 1 / ((m : ℝ) + 2)), mul_assoc,
          div_mul_cancel₀ _ (ne_of_gt (hYkpos k))]
      rw [hcoef]
      have hc : 0 < cEps ε := cEps_pos' hεpos
      nlinarith [hlt, hc]
    · intro hmem
      have hopen : IsOpen (cuspThinRegion Γ ξ ε) := by
        rw [hset]
        exact isOpen_lt (continuous_lev_ξ ξ |>.mul (by
          have hLo : ContinuousOn (parDisp Γ ξ) {y : E n | inner ℝ y ξ = 0} :=
            (parDisp_lipschitz_invariant n hA hI Γ hvan hξ).1.continuousOn
          have := hLo.comp_continuous (continuous_yc_ξ hξS) (fun v => inner_yc_self hξS)
          simpa [Function.comp_def] using this)) continuous_const
      rw [hopen.interior_eq, hset] at hmem
      have hlt := Set.mem_ofPred_eq.mp hmem
      rw [hfront k] at hlt
      exact lt_irrefl _ hlt
  have hSfin := hccl εsep hεseppos hsep εB hεBpos r hr
    (fun η hη ε' hε' hε'leB u' h u'' hw => hball η hη ε' hε' hε'leB u' h u'' hw)
    ε hεpos hεleB h2ε
    (fun η hη u hu => frontier_parDisp_eq n hA hI Γ hdisc hvan hη hεpos hu)
    K hKc
  have hηkS : ∀ k : ℕ, bd (γk k : PO n 1) ξ ∈ {η : E n | η ∈ parFixed Γ ∧
      (frontier (cuspThinRegion Γ η ε) ∩ K).Nonempty} := by
    intro k
    refine ⟨parFixed_invariant hA hI Γ (γk k) hξ, ?_⟩
    refine ⟨(γk k : PO n 1) • (u k), ?_, hγkK k⟩
    have hsmul := hcsmul (γk k) ε
    have himg : (fun w : E n => (γk k : PO n 1) • w) '' frontier (cuspThinRegion Γ ξ ε)
        = frontier (cuspThinRegion Γ (bd (γk k : PO n 1) ξ) ε) := by
      rw [← hsmul]
      let e : E n ≃ₜ E n :=
        { toFun := fun w => (γk k : PO n 1) • w
          invFun := fun w => (γk k : PO n 1)⁻¹ • w
          left_inv := fun w => by
            show (γk k : PO n 1)⁻¹ • ((γk k : PO n 1) • w) = w
            rw [← hA'.mul_smul, inv_mul_cancel, hA'.one_smul]
          right_inv := fun w => by
            show (γk k : PO n 1) • ((γk k : PO n 1)⁻¹ • w) = w
            rw [← hA'.mul_smul, mul_inv_cancel, hA'.one_smul]
          continuous_toFun := hA.2.2.2.2.2.2.1.comp (continuous_const.prodMk continuous_id)
          continuous_invFun := hA.2.2.2.2.2.2.1.comp (continuous_const.prodMk continuous_id) }
      have hfr := Homeomorph.image_frontier e (s := cuspThinRegion Γ ξ ε)
      change (fun w : E n => (γk k : PO n 1) • w) '' frontier (cuspThinRegion Γ ξ ε)
        = frontier ((fun w : E n => (γk k : PO n 1) • w) '' cuspThinRegion Γ ξ ε) at hfr
      exact hfr
    rw [← himg]
    exact ⟨u k, hufront k, rfl⟩
  let S' : Set (E n) := {η ∈ {η : E n | η ∈ parFixed Γ ∧
      (frontier (cuspThinRegion Γ η ε) ∩ K).Nonempty} | ∃ γ : Γ, bd (γ : PO n 1) ξ = η}
  have hS'fin : S'.Finite := hSfin.subset (fun η hη => hη.1)
  have hch2 : ∀ η : E n, η ∈ S' → ∃ γ : Γ, bd (γ : PO n 1) ξ = η := fun η hη => hη.2
  let g : E n → Γ := fun η => if h : η ∈ S' then Classical.choose (hch2 η h) else 1
  have hgfix : ∀ η (hη : η ∈ S'), bd ((g η : Γ) : PO n 1) ξ = η := by
    intro η hη
    have h := Classical.choose_spec (hch2 η hη)
    simp only [g, dif_pos hη]
    exact h
  have hηkS' : ∀ k : ℕ, bd (γk k : PO n 1) ξ ∈ S' := by
    intro k
    exact ⟨hηkS k, ⟨γk k, rfl⟩⟩
  let σ : ℕ → Γ := fun k => (g (bd (γk k : PO n 1) ξ))⁻¹ * γk k
  have hσfix : ∀ k : ℕ, bd ((σ k : Γ) : PO n 1) ξ = ξ := by
    intro k
    have h1 := hgfix _ (hηkS' k)
    have hinv : bd (((g (bd (γk k : PO n 1) ξ))⁻¹ : Γ) : PO n 1)
        (bd ((g (bd (γk k : PO n 1) ξ) : Γ) : PO n 1) ξ) = ξ := by
      have h2 := hA'.bd_mul (((g (bd (γk k : PO n 1) ξ))⁻¹ : Γ) : PO n 1)
        ((g (bd (γk k : PO n 1) ξ) : Γ) : PO n 1) ξ hξS
      rw [← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, hA'.bd_one ξ hξS] at h2
      exact h2.symm
    show bd (((g (bd (γk k : PO n 1) ξ))⁻¹ * γk k : Γ) : PO n 1) ξ = ξ
    rw [Subgroup.coe_mul, hA'.bd_mul _ _ ξ hξS]
    rw [h1] at hinv
    exact hinv
  let K' : Set (E n) := ⋃ η ∈ S',
    (fun w : E n => (((g η)⁻¹ : Γ) : PO n 1) • w) '' K
  have hK'c : IsCompact K' := by
    refine Set.Finite.isCompact_biUnion hS'fin (fun η _ => ?_)
    exact hKc.image (hA.2.2.2.2.2.2.1.comp (continuous_const.prodMk continuous_id))
  have hσK : ∀ k : ℕ, ((σ k : Γ) : PO n 1) • (u k) ∈ K' := by
    intro k
    refine Set.mem_iUnion₂.mpr ⟨bd (γk k : PO n 1) ξ, hηkS' k, ?_⟩
    · refine ⟨(γk k : PO n 1) • (u k), hγkK k, ?_⟩
      show (((g (bd (γk k : PO n 1) ξ))⁻¹ : Γ) : PO n 1) • ((γk k : PO n 1) • (u k))
        = ((σ k : Γ) : PO n 1) • (u k)
      rw [← hA'.mul_smul]
      rfl
  have hσlev : ∀ k : ℕ, lev ξ (((σ k : Γ) : PO n 1) • (u k)) = L k := by
    intro k
    have hbc : bCocy ((σ k : Γ) : PO n 1) ξ = 0 := hvan (σ k) ξ hξ (hσfix k)
    have hb : busemann ξ (((σ k : Γ) : PO n 1) • (0 : E n)) = 0 := by
      simpa [bCocy, hσfix k] using hbc
    have hbus := (HypIsoData.ofProp hI).busemann_cocycle ((σ k : Γ) : PO n 1) ξ (u k) hξS
    rw [hσfix k, hb, add_zero] at hbus
    rw [lev_eq_exp hξS]
    rw [hbus]
    rw [← lev_eq_exp hξS]
    exact hulev k
  obtain ⟨δ, hδpos, hδ⟩ := lev_pos_lb_of_isCompact hξS hK'c
  have hbound : ∀ k : ℕ, δ ≤ L k := by
    intro k
    have h := hδ _ (hσK k)
    rwa [hσlev k] at h
  have hLdec : ∀ k : ℕ, L k ≤ cEps ε / ((k : ℝ) + 1) := by
    intro k
    have h1 : ((k : ℝ) + 1) < parDisp Γ ξ (Yk k) := hYgt ((k : ℝ) + 1)
    show cEps ε / parDisp Γ ξ (Yk k) ≤ cEps ε / ((k : ℝ) + 1)
    exact div_le_div_of_nonneg_left (le_of_lt (cEps_pos' hεpos)) (by positivity) (le_of_lt h1)
  obtain ⟨k, hk⟩ := exists_nat_gt (cEps ε / δ)
  have h2 : cEps ε / ((k : ℝ) + 1) < δ := by
    rw [div_lt_iff₀ (by positivity)]
    have hδk : cEps ε / δ < (k : ℝ) := hk
    have h3 : cEps ε < (k : ℝ) * δ := by
      rw [div_lt_iff₀ hδpos] at hδk
      linarith
    nlinarith [hδpos]
  linarith [hbound k, hLdec k]


/-- **The crux.** For a lattice `Γ`, a parabolic fixed point `ξ` and every level `ε > 0`, the
Margulis region at `ξ` contains a horoball at `ξ`. -/
theorem cuspThinRegion_horoball (n : ℕ) (hn : 2 ≤ n) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)) (hΓ : Submission.Mostow.HypLattice Γ)
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ Work.Mostow.parFixed Γ →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = 0)
    {ξ : Submission.Mostow.E n} (hξ : ξ ∈ Work.Mostow.parFixed Γ) :
    ∀ ε : ℝ, 0 < ε → ∃ t : ℝ, Submission.Mostow.horoball ξ t ⊆
      Work.Mostow.cuspThinRegion Γ ξ ε := by
  -- the elliptic gap of the cusp stabiliser, in the flat-linear form
  obtain ⟨θ, hθpos, hgap₀⟩ := Work.Mostow.feg_gap_core n hn hA hI Γ hΓ ξ hξ
  have hgap : ∀ (σ : Γ),
      Submission.Mostow.bd (σ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ → σ ≠ 1 →
      (∃ p : Submission.Mostow.E n, (σ : LeanEval.Geometry.MostowRigidity.PO n 1) • p = p) →
      ∃ y : Submission.Mostow.E n, inner ℝ y ξ = 0 ∧ ‖y‖ = 1 ∧
        θ ≤ ‖Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat
              (σ : LeanEval.Geometry.MostowRigidity.PO n 1)) y - y‖ := by
    intro σ hbd hne hell
    simpa only [Work.Mostow.fPart] using hgap₀ σ hbd hne hell
  -- a uniform bound on the number of short elements at a frontier point
  have hshort := Work.Mostow.cuspFrontierShortBound n hn hA hI Γ hΓ hvan ξ hξ hθpos hgap
  -- a uniform collar of the frontier inside the thin region at `2 * ε`
  have hballU := Work.Mostow.cuspFrontierBallUniform n hn hA hI Γ hvan
  -- the separation of the thin regions of distinct parabolic fixed points
  obtain ⟨εsep, hεseppos, hsep⟩ := Work.Mostow.cuspThinRegion_separation n hn hA hI Γ hΓ.1
  -- the action of `G` on the thin region at `ξ`
  have hcsmul : ∀ (γ : Γ) (ε : ℝ),
      (fun u : Submission.Mostow.E n => (γ : LeanEval.Geometry.MostowRigidity.PO n 1) • u) ''
        Work.Mostow.cuspThinRegion Γ ξ ε
        = Work.Mostow.cuspThinRegion Γ
          (Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ) ε :=
    fun γ ε => Work.Mostow.cuspThinRegion_smul n hA hI Γ γ hξ.1 ε
  -- `parDisp` is bounded on the flat space
  have hccl : ∀ (εsep' : ℝ), 0 < εsep' →
      (∀ η ∈ Work.Mostow.parFixed Γ, ∀ η' ∈ Work.Mostow.parFixed Γ, η ≠ η' →
        Disjoint (Work.Mostow.cuspThinRegion Γ η εsep')
          (Work.Mostow.cuspThinRegion Γ η' εsep')) →
      ∀ (εB : ℝ), 0 < εB → ∀ (r : ℝ), 0 < r →
      (∀ η ∈ Work.Mostow.parFixed Γ, ∀ ε' : ℝ, 0 < ε' → ε' ≤ εB →
        ∀ u : Submission.Mostow.E n,
        Work.Mostow.lev η u * Work.Mostow.parDisp Γ η (Work.Mostow.yc η u) =
          Work.Mostow.cEps ε' →
        ∀ w : Submission.Mostow.E n, Submission.Mostow.hdist u w ≤ r * ε' →
          w ∈ Work.Mostow.cuspThinRegion Γ η (2 * ε')) →
      ∀ (ε : ℝ), 0 < ε → ε ≤ εB → 2 * ε ≤ εsep' →
      (∀ η ∈ Work.Mostow.parFixed Γ, ∀ u : Submission.Mostow.E n,
        u ∈ frontier (Work.Mostow.cuspThinRegion Γ η ε) →
        Work.Mostow.lev η u * Work.Mostow.parDisp Γ η (Work.Mostow.yc η u) =
          Work.Mostow.cEps ε) →
      ∀ (K : Set (Submission.Mostow.E n)), IsCompact K →
      {η : Submission.Mostow.E n | η ∈ Work.Mostow.parFixed Γ ∧
        (frontier (Work.Mostow.cuspThinRegion Γ η ε) ∩ K).Nonempty}.Finite :=
    fun εsep' hεsep' hsep' εB hεB r hr hball' ε hε hεleB h2ε heq K hK =>
      Work.Mostow.cuspFrontierClassesB n hn hA hI Γ hvan hεsep' hsep' hεB hr hball' hε hεleB h2ε heq hK
  obtain ⟨M, hM⟩ := parDisp_bounded n hn hA hI Γ hΓ hvan hξ hshort hballU
    ⟨εsep, hεseppos, hsep⟩ hccl hcsmul
  intro ε hε
  obtain ⟨hpos, hiff⟩ := Work.Mostow.cuspThinRegion_eq_parDisp n hA hI Γ hΓ.1 hvan hξ
  refine ⟨Real.log (cEps ε / max M 1), ?_⟩
  intro u hu
  rw [hiff ε hε]
  have hMpos : 0 < max M 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hlev : lev ξ u < cEps ε / max M 1 := by
    have h1 : Real.exp (busemann ξ u) < Real.exp (Real.log (cEps ε / max M 1)) :=
      Real.exp_lt_exp.mpr hu
    rw [Real.exp_log (div_pos (cEps_pos' hε) hMpos), ← lev_eq_exp hξ.1 u] at h1
    exact h1
  have hparle : parDisp Γ ξ (yc ξ u) ≤ max M 1 :=
    le_trans (hM (yc ξ u) (inner_yc_self hξ.1)) (le_max_left _ _)
  calc lev ξ u * parDisp Γ ξ (yc ξ u)
      ≤ lev ξ u * max M 1 := mul_le_mul_of_nonneg_left hparle (le_of_lt (lev_pos ξ hξ.1 u))
    _ < (cEps ε / max M 1) * max M 1 := mul_lt_mul_of_pos_right hlev hMpos
    _ = cEps ε := div_mul_cancel₀ _ (ne_of_gt hMpos)

end

end Work.Mostow
