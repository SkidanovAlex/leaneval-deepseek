import Mathlib
import Submission.Work.StemsB.SphLoopModel

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The based contraction of the thickened outer disc to `∞` (the `H2` input of route B)

`CONTRACTS.md` §H2 asks for the **based contraction** of the outer thickening

`U = sphLoopThick n = {∞} ∪ {v | 1/2 < ‖v‖}`

of the model `SphModel n = OnePoint ℝⁿ` to the base point `∞`: a continuous `F : ↥U × I → ↥U` with
`F (u, 0) = u`, `F (u, 1) = ∞` and `F (∞, t) = ∞`.

The contraction is the **radial push**

`(↑v, t) ↦ ↑(((1 - t)⁻¹) • v)`,   `(∞, t) ↦ ∞`,   `(↑v, 1) ↦ ∞`

of `CONTRACTS.md` §H2: the vector is pushed radially outwards, growing without bound as `t → 1`, so
that at `t = 1` it has reached `∞`.  Since `(1 - t)⁻¹ ≥ 1` for `t ∈ [0, 1]`, the push never
re-enters the inner closed ball of radius `1/2`, i.e. it stays in `U`
(`mem_sphLoopThick_pushFun`).

## The continuity obligations

`Work.StemsB.pushFun` is the model-level formula.  It is continuous at the two kinds of points that
occur in `↥U × I`:

* `continuousAt_pushFun_infty` — at `(∞, t)`, for every `t`.  A basic neighbourhood of `∞` is the
  complement of a compact `K ⊆ ℝⁿ`, and for `v ∉ closedBall 0 R ⊇ K` the pushed vector
  `(1 - t)⁻¹ • v` has norm `≥ ‖v‖ > R`, hence also stays outside `K`; this bounds the whole
  `t`-direction at once, exactly as in `Work.StemsB.continuousAt_interpolateFun_infty`.
* `continuousAt_pushFun_some` — at `(↑v, t)` for `v ≠ 0`.  Here `(w, s) ↦ (↑w, s)` is an open chart
  of `OnePoint ℝⁿ × I` (`OnePoint.isOpenEmbedding_coe.prodMap`), so it suffices to handle the
  coordinate formula `(w, s) ↦ (1 - s)⁻¹ • w`: for `t ≠ 1` it is a manifestly continuous
  expression, and for `t = 1` (where the value is `∞`) the norm `(1 - s)⁻¹‖w‖` tends to infinity for
  `w` near the non-zero point `v` and `s → 1`.

Note that the push is **not** continuous at `(↑0, 1)`; this is why the construction is carried out on
`↥U`, which avoids the origin (`CONTRACTS.md` §H4).
-/

open scoped Topology unitInterval

namespace Work.StemsB

noncomputable section

/-- The **radial push** on the model `SphModel n = OnePoint ℝⁿ`, as a function of the space
variable and the homotopy parameter: `(∞, t) ↦ ∞`, `(↑v, t) ↦ ↑((1 - t)⁻¹ • v)` for `t ≠ 1`, and
`(↑v, 1) ↦ ∞`. -/
def pushFun (n : ℕ) (p : SphModel n × unitInterval) : SphModel n :=
  match p.1 with
  | none => OnePoint.infty
  | some v => if (p.2 : ℝ) = 1 then OnePoint.infty
      else OnePoint.some (((1 - (p.2 : ℝ))⁻¹) • v)

@[simp] theorem pushFun_infty (n : ℕ) (t : unitInterval) :
    pushFun n (OnePoint.infty, t) = OnePoint.infty := rfl

@[simp] theorem pushFun_some (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) (t : unitInterval) :
    pushFun n (OnePoint.some v, t) =
      (if (t : ℝ) = 1 then OnePoint.infty
       else OnePoint.some (((1 - (t : ℝ))⁻¹) • v)) := rfl

/-- **The push stays in the thickening**: for `x ∈ sphLoopThick n` the radial push of `x` at any
time `t` still lies in `sphLoopThick n`.  Indeed the factor `(1 - t)⁻¹` is `≥ 1` on `[0, 1]`, so the
norm of the pushed vector is `≥ ‖v‖ > 1/2` (and `∞` is fixed). -/
theorem mem_sphLoopThick_pushFun (n : ℕ) {x : SphModel n} (hx : x ∈ sphLoopThick n)
    (t : unitInterval) : pushFun n (x, t) ∈ sphLoopThick n := by
  rcases hx with h | ⟨v, hv, hlt⟩
  · rw [show x = OnePoint.infty from h, pushFun_infty]
    exact Or.inl rfl
  · rw [show x = OnePoint.some v from hv]
    by_cases h1 : (t : ℝ) = 1
    · rw [pushFun_some, if_pos h1]; exact Or.inl rfl
    · have ht : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 h1
      have hpos : (0 : ℝ) < 1 - (t : ℝ) := by linarith
      have hle : (1 : ℝ) ≤ (1 - (t : ℝ))⁻¹ := by
        rw [one_le_inv₀ hpos]; linarith [t.2.1]
      rw [pushFun_some, if_neg h1]
      refine Or.inr ⟨_, rfl, ?_⟩
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_trans zero_le_one hle)]
      have hge : ‖v‖ ≤ (1 - (t : ℝ))⁻¹ * ‖v‖ :=
        le_mul_of_one_le_left (norm_nonneg v) hle
      linarith

/-! ## Continuity of the push at the base point `∞` -/

/-- **Joint continuity of the push at `(∞, t)`**, for every `t`.  This is where the thickening
matters: a basic neighbourhood of `∞` is the complement of a compact set `K ⊆ ℝⁿ`, and for `v`
outside a ball containing `K` the pushed vector `(1 - t)⁻¹ • v` has norm `≥ ‖v‖`, hence also lies
outside that ball, for *every* `t ∈ [0, 1]`. -/
theorem continuousAt_pushFun_infty (n : ℕ) (t : unitInterval) :
    ContinuousAt (fun p : SphModel n × unitInterval => pushFun n p) (OnePoint.infty, t) := by
  rw [ContinuousAt, Filter.tendsto_def]
  intro s hs
  obtain ⟨K, ⟨hKcl, hKcp⟩, hKsub⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.mp hs
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall
    (0 : EuclideanSpace ℝ (Fin n))).mp hKcp.isBounded
  have hU : (OnePoint.some '' (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ ∪
      {OnePoint.infty}) ∈ 𝓝 (OnePoint.infty : SphModel n) :=
    OnePoint.hasBasis_nhds_infty.mem_iff.mpr
      ⟨Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R,
        ⟨Metric.isClosed_closedBall, isCompact_closedBall _ _⟩, subset_rfl⟩
  have hprod : ((OnePoint.some '' (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ ∪
      {OnePoint.infty}) ×ˢ (Set.univ : Set unitInterval)) ∈
      𝓝 ((OnePoint.infty, t) : SphModel n × unitInterval) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod hU Filter.univ_mem
  refine Filter.mem_of_superset hprod ?_
  rintro ⟨x, s'⟩ ⟨hx, -⟩
  rcases hx with hx | hx
  · obtain ⟨v, hv, rfl⟩ := hx
    have hvR : R < ‖v‖ := by
      have hv' : R < dist v (0 : EuclideanSpace ℝ (Fin n)) := by
        simpa only [Set.mem_compl_iff, Metric.mem_closedBall, not_le] using hv
      simpa [dist_eq_norm, sub_zero] using hv'
    show pushFun n (OnePoint.some v, s') ∈ s
    by_cases h1 : (s' : ℝ) = 1
    · rw [pushFun_some, if_pos h1]
      exact hKsub (Or.inr rfl)
    · have ht : (s' : ℝ) < 1 := lt_of_le_of_ne s'.2.2 h1
      have hpos : (0 : ℝ) < 1 - (s' : ℝ) := by linarith
      have hs1 : (1 : ℝ) ≤ (1 - (s' : ℝ))⁻¹ := by
        rw [one_le_inv₀ hpos]; linarith [s'.2.1]
      have hnot : (((1 - (s' : ℝ))⁻¹) • v) ∉ K := by
        intro hmem
        have hmem' := hR hmem
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hmem'
        have hle : ‖v‖ ≤ ‖((1 - (s' : ℝ))⁻¹) • v‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_trans zero_le_one hs1)]
          exact le_mul_of_one_le_left (norm_nonneg v) hs1
        linarith
      rw [pushFun_some, if_neg h1]
      exact hKsub (Or.inl ⟨_, hnot, rfl⟩)
  · obtain rfl : x = OnePoint.infty := by simpa using hx
    show pushFun n (OnePoint.infty, s') ∈ s
    rw [pushFun_infty]
    exact hKsub (Or.inr rfl)

/-! ## Continuity of the push at a finite point of the thickening

The two branches of the chart computation: at `t = 1` the value is `∞` and is the limit of the push
(since `(1 - s)⁻¹‖w‖ → ∞` for `w → w₀ ≠ 0`), and at `t ≠ 1` the push agrees near `(w, t)` with a
manifestly continuous expression. -/

/-- The chart computation at `t = 1`: `(w, s) ↦ pushFun (↑w, s)` tends to `∞` as `(w, s) → (w₀, 1)`
for `w₀ ≠ 0`. -/
theorem continuousAt_pushFun_chart_one (n : ℕ) (w : EuclideanSpace ℝ (Fin n)) (hw : w ≠ 0)
    (t : unitInterval) (h1 : (t : ℝ) = 1) :
    ContinuousAt (fun p : EuclideanSpace ℝ (Fin n) × unitInterval =>
        pushFun n (OnePoint.some p.1, p.2)) (w, t) := by
  have ht1 : t = (1 : unitInterval) := Subtype.ext (by simpa using h1)
  rw [ht1]
  have hval : pushFun n (OnePoint.some w, (1 : unitInterval)) = OnePoint.infty := by
    rw [pushFun_some]; simp
  have hgoal : Filter.Tendsto (fun p : EuclideanSpace ℝ (Fin n) × unitInterval =>
      pushFun n (OnePoint.some p.1, p.2)) (𝓝 (w, (1 : unitInterval))) (𝓝 OnePoint.infty) := by
    change Filter.map (fun p : EuclideanSpace ℝ (Fin n) × unitInterval =>
      pushFun n (OnePoint.some p.1, p.2)) (𝓝 (w, (1 : unitInterval))) ≤ 𝓝 OnePoint.infty
    rw [OnePoint.le_nhds_infty]
    intro K _ hKcp
    rw [Filter.mem_map]
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall
      (0 : EuclideanSpace ℝ (Fin n))).mp hKcp.isBounded
    have hw2 : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have hA : IsOpen {p : EuclideanSpace ℝ (Fin n) × unitInterval | ‖p.1 - w‖ < ‖w‖ / 2} :=
      isOpen_lt (continuous_norm.comp (continuous_fst.sub continuous_const)) continuous_const
    have hB : IsOpen {p : EuclideanSpace ℝ (Fin n) × unitInterval |
        (1 - (p.2 : ℝ)) * (2 * (R + 1)) < ‖w‖} :=
      isOpen_lt ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).mul
        continuous_const) continuous_const
    have hmemA : (w, (1 : unitInterval)) ∈
        {p : EuclideanSpace ℝ (Fin n) × unitInterval | ‖p.1 - w‖ < ‖w‖ / 2} := by
      show ‖w - w‖ < ‖w‖ / 2
      rw [sub_self, norm_zero]; linarith
    have hmemB : (w, (1 : unitInterval)) ∈
        {p : EuclideanSpace ℝ (Fin n) × unitInterval |
          (1 - (p.2 : ℝ)) * (2 * (R + 1)) < ‖w‖} := by
      show (1 - (((1 : unitInterval) : ℝ))) * (2 * (R + 1)) < ‖w‖
      norm_num
      exact hw
    refine Filter.mem_of_superset (Filter.inter_mem (hA.mem_nhds hmemA)
      (hB.mem_nhds hmemB)) ?_
    rintro ⟨u, s⟩ ⟨hp1, hp2⟩
    simp only [Set.mem_ofPred_eq] at hp1 hp2
    show pushFun n (OnePoint.some u, s) ∈ (OnePoint.some '' Kᶜ ∪ {OnePoint.infty})
    by_cases h2 : (s : ℝ) = 1
    · rw [pushFun_some, if_pos h2]; exact Or.inr rfl
    · have hslt : (s : ℝ) < 1 := lt_of_le_of_ne s.2.2 h2
      have hpos : (0 : ℝ) < 1 - (s : ℝ) := by linarith
      rw [pushFun_some, if_neg h2]
      refine Or.inl ⟨_, ?_, rfl⟩
      intro hmemK
      have hmem' := hR hmemK
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hmem'
      have hnorm : ‖w‖ / 2 < ‖u‖ := by
        have hn := norm_sub_norm_le w u
        rw [show w - u = -(u - w) from by abel, norm_neg] at hn
        linarith
      have h3 : (1 - (s : ℝ)) * (R + 1) < ‖u‖ := by nlinarith [hp2, hnorm]
      have h4 : R + 1 < ‖u‖ / (1 - (s : ℝ)) := by
        rw [lt_div_iff₀ hpos]; linarith
      have h5 : ‖u‖ / (1 - (s : ℝ)) = (1 - (s : ℝ))⁻¹ * ‖u‖ := by
        rw [div_eq_inv_mul]
      have h6 : R < ‖((1 - (s : ℝ))⁻¹) • u‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt (inv_pos.mpr hpos))]
        linarith
      linarith
  simpa only [ContinuousAt, hval] using hgoal

/-- The chart computation at `t ≠ 1`: near `(w, t)` the chart expression of the push,
`(w, s) ↦ pushFun (↑w, s)`, coincides with the manifestly continuous map
`(w, s) ↦ ↑((1 - s)⁻¹ • w)`. -/
theorem continuousAt_pushFun_chart_ne (n : ℕ) (w : EuclideanSpace ℝ (Fin n)) (t : unitInterval)
    (h1 : ¬(t : ℝ) = 1) :
    ContinuousAt (fun p : EuclideanSpace ℝ (Fin n) × unitInterval =>
        pushFun n (OnePoint.some p.1, p.2)) (w, t) := by
  have hne : (1 : ℝ) - (t : ℝ) ≠ 0 := fun hh => h1 (by linarith)
  have hG : ContinuousAt (fun p : EuclideanSpace ℝ (Fin n) × unitInterval =>
      OnePoint.some (((1 - (p.2 : ℝ))⁻¹) • p.1)) (w, t) := by
    have h2' : ContinuousAt (fun p : EuclideanSpace ℝ (Fin n) × unitInterval =>
        (p.2 : ℝ)) (w, t) :=
      (continuous_subtype_val.continuousAt).comp continuousAt_snd
    have h3' : ContinuousAt (fun p : EuclideanSpace ℝ (Fin n) × unitInterval =>
        (1 : ℝ) - (p.2 : ℝ)) (w, t) := continuousAt_const.sub h2'
    have h4' : ContinuousAt (fun p : EuclideanSpace ℝ (Fin n) × unitInterval =>
        ((1 : ℝ) - (p.2 : ℝ))⁻¹) (w, t) := h3'.inv₀ (by simpa using hne)
    have h5' : ContinuousAt (fun p : EuclideanSpace ℝ (Fin n) × unitInterval =>
        ((1 : ℝ) - (p.2 : ℝ))⁻¹ • p.1) (w, t) := h4'.smul continuousAt_fst
    exact (OnePoint.continuous_coe.continuousAt).comp h5'
  have hev : (fun p : EuclideanSpace ℝ (Fin n) × unitInterval =>
      OnePoint.some (((1 - (p.2 : ℝ))⁻¹) • p.1)) =ᶠ[𝓝 (w, t)]
      (fun p => pushFun n (OnePoint.some p.1, p.2)) := by
    have hmem : {p : EuclideanSpace ℝ (Fin n) × unitInterval | (p.2 : ℝ) ≠ 1} ∈ 𝓝 (w, t) := by
      have hcont : Continuous fun p : EuclideanSpace ℝ (Fin n) × unitInterval => (p.2 : ℝ) :=
        continuous_subtype_val.comp continuous_snd
      have hsing : IsOpen ({p : EuclideanSpace ℝ (Fin n) × unitInterval | (p.2 : ℝ) ≠ 1}) := by
        simpa [Set.preimage, Set.mem_compl_iff, Set.mem_singleton_iff] using
          (isOpen_compl_singleton (x := (1 : ℝ))).preimage hcont
      exact hsing.mem_nhds (by simpa using h1)
    filter_upwards [hmem] with p hp
    rw [pushFun_some, if_neg hp]
  exact hG.congr hev

/-- **Joint continuity of the push at `(↑w, t)`**, for `w ≠ 0` and every `t`.  The chart
`(w, s) ↦ (↑w, s)` is an open embedding of `ℝⁿ × I` into `OnePoint ℝⁿ × I`, so continuity at
`(↑w, t)` is equivalent to continuity of the chart expression at `(w, t)`, which is
`continuousAt_pushFun_chart_one` at `t = 1` and `continuousAt_pushFun_chart_ne` at `t ≠ 1`. -/
theorem continuousAt_pushFun_some (n : ℕ) (w : EuclideanSpace ℝ (Fin n)) (hw : w ≠ 0)
    (t : unitInterval) :
    ContinuousAt (fun p : SphModel n × unitInterval => pushFun n p) (OnePoint.some w, t) := by
  have hchart : Topology.IsOpenEmbedding
      (fun p : EuclideanSpace ℝ (Fin n) × unitInterval => (OnePoint.some p.1, p.2)) :=
    (OnePoint.isOpenEmbedding_coe (X := EuclideanSpace ℝ (Fin n))).prodMap
      Topology.IsOpenEmbedding.id
  have hcomp : ContinuousAt
      (fun p : EuclideanSpace ℝ (Fin n) × unitInterval => pushFun n (OnePoint.some p.1, p.2))
      (w, t) := by
    by_cases h1 : (t : ℝ) = 1
    · exact continuousAt_pushFun_chart_one n w hw t h1
    · exact continuousAt_pushFun_chart_ne n w t h1
  exact (hchart.continuousAt_iff
    (g := fun p : SphModel n × unitInterval => pushFun n p)).mp hcomp

/-! ## The based contraction of the thickening -/

theorem onePoint_radialPush (n : ℕ) :
    ∃ F : C(↥(sphLoopThick n) × unitInterval, ↥(sphLoopThick n)),
      (∀ u, F (u, 0) = u) ∧
      (∀ u, F (u, 1) = ⟨OnePoint.infty, Or.inl rfl⟩) ∧
      (∀ t, F (⟨OnePoint.infty, Or.inl rfl⟩, t) = ⟨OnePoint.infty, Or.inl rfl⟩) := by
  have hmem : ∀ q : ↥(sphLoopThick n) × unitInterval,
      pushFun n (q.1.1, q.2) ∈ sphLoopThick n :=
    fun q => mem_sphLoopThick_pushFun n q.1.2 q.2
  have hcont : Continuous fun q : ↥(sphLoopThick n) × unitInterval => pushFun n (q.1.1, q.2) := by
    rw [continuous_iff_continuousAt]
    intro q
    have hincl : ContinuousAt (fun q : ↥(sphLoopThick n) × unitInterval => (q.1.1, q.2)) q :=
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).continuousAt
    rcases q.1.2 with h | ⟨v, hv, hlt⟩
    · have h1 : ContinuousAt (fun p : SphModel n × unitInterval => pushFun n p) (q.1.1, q.2) := by
        rw [show q.1.1 = OnePoint.infty from h]
        exact continuousAt_pushFun_infty n q.2
      exact ContinuousAt.comp (f := fun q : ↥(sphLoopThick n) × unitInterval => (q.1.1, q.2))
        (g := fun p : SphModel n × unitInterval => pushFun n p) h1 hincl
    · have hv0 : v ≠ 0 := by
        intro h0
        rw [h0] at hlt
        norm_num at hlt
      have h1 : ContinuousAt (fun p : SphModel n × unitInterval => pushFun n p) (q.1.1, q.2) := by
        rw [show q.1.1 = OnePoint.some v from hv]
        exact continuousAt_pushFun_some n v hv0 q.2
      exact ContinuousAt.comp (f := fun q : ↥(sphLoopThick n) × unitInterval => (q.1.1, q.2))
        (g := fun p : SphModel n × unitInterval => pushFun n p) h1 hincl
  refine ⟨⟨fun q => ⟨pushFun n (q.1.1, q.2), hmem q⟩, hcont.subtype_mk hmem⟩, ?_, ?_, ?_⟩
  · intro u
    apply Subtype.ext
    rcases u.2 with h | ⟨v, hv, _⟩
    · show pushFun n (u.1, (0 : unitInterval)) = u.1
      rw [show u.1 = OnePoint.infty from h]
      exact pushFun_infty n 0
    · show pushFun n (u.1, (0 : unitInterval)) = u.1
      rw [show u.1 = OnePoint.some v from hv, pushFun_some]
      simp
  · intro u
    apply Subtype.ext
    rcases u.2 with h | ⟨v, hv, _⟩
    · show pushFun n (u.1, (1 : unitInterval)) = OnePoint.infty
      rw [show u.1 = OnePoint.infty from h]
      exact pushFun_infty n 1
    · show pushFun n (u.1, (1 : unitInterval)) = OnePoint.infty
      rw [show u.1 = OnePoint.some v from hv, pushFun_some]
      simp
  · intro t
    apply Subtype.ext
    show pushFun n ((⟨OnePoint.infty, Or.inl rfl⟩ : ↥(sphLoopThick n)).1, t) = OnePoint.infty
    exact pushFun_infty n t

end

end Work.StemsB
