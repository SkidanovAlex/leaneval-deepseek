import Mathlib
import Submission.Work.Smooth.SphereJordan.planeIndexGeom
import Submission.Work.Smooth.SphereJordan.windNumber_eq_zero_or_odd_uncond
import Submission.Work.Smooth.SphereJordan.exists_sqrt_curve_of_even_windNumber
import Submission.Work.Smooth.JordanSeparation.ComplHelpers
import Submission.Work.Topology.PlaneCurve.compl_jordan_atMostTwo
import Submission.Work.Topology.PlaneCurve.frontier_component_eq_range
import Submission.Work.Smooth.SphereJordan.jsepDefs

/-!
# A Jordan curve enclosing `0` meets its reflection, bounded-component form
# (cycle-free copy: the unused `jsepExists` import of the original is removed so that this module
#  does not (transitively) import `Submission.Work.Topology.PlaneCurve.windNumber_ne_zero_of_normalized`.)

The classical fact that a Jordan curve with `0` in its *bounded* complementary component must contain
a pair of antipodal points, proved here from the weaker hypothesis that the complementary component
of `0` is bounded (no winding number is used): the same case analysis as in
`Work.Smooth.SphereJordan.false_of_antipodalFree_of_windNumber_ne_zero`, with the winding-number
inputs replaced by the boundedness of the component of `0` and by the two purely topological facts
`ComplHelpers.isPreconnected_lt_norm_compl` and `ray_exit`.

The point of the weakening is that "the component of `0` is bounded" is available for the
*continuous square root* `η` of a curve of winding number `0` about `z` with `z` in a *bounded*
complementary component of the original curve, so that this form of the statement can be used to
prove `windNumber_ne_zero_of_bounded_component` (see that result below).
-/

namespace Work.Smooth.SphereJordan

open Set

noncomputable section

/-- **No antipodal-free Jordan curve has `0` in a bounded complementary component.** -/
theorem antipodal_free_false_of_bounded_component {η : ℝ → ℂ} (hη : Continuous η)
    (hper : Function.Periodic η (2 * Real.pi)) (hinj : Set.InjOn η (Set.Ico 0 (2 * Real.pi)))
    (h0 : ∀ t : ℝ, η t ≠ 0)
    (hbdd : Bornology.IsBounded (connectedComponentIn (Set.range η)ᶜ (0 : ℂ)))
    (hanti : ∀ s t : ℝ, η s ≠ -η t) : False := by
  classical
  have h0K : (0 : ℂ) ∉ Set.range η := fun h => h.elim fun t ht => h0 t ht
  obtain ⟨x₀, hx₀K, hx₀max⟩ :=
    (Work.Topology.PlaneCurve.isCompact_range_of_periodic hη hper).exists_isMaxOn
      ⟨η 0, ⟨0, rfl⟩⟩ continuous_norm.continuousOn
  obtain ⟨t₀, ht₀⟩ := hx₀K
  set R : ℝ := ‖η t₀‖ with hRdef
  have hR : ∀ t : ℝ, ‖η t‖ ≤ R := by
    intro t
    rw [hRdef, ht₀]
    exact hx₀max ⟨t, rfl⟩
  have hRpos : 0 ≤ R := by rw [hRdef]; exact norm_nonneg _
  have hRμ : ∀ t : ℝ, ‖-η t‖ ≤ R := by intro t; rw [norm_neg]; exact hR t
  -- the far exterior
  have hfar_pre : IsPreconnected {u : ℂ | R < ‖u‖} :=
    Work.Smooth.JordanSeparation.isPreconnected_lt_norm_compl R hRpos
  have hfar_K : {u : ℂ | R < ‖u‖} ⊆ (Set.range η)ᶜ := by
    intro u hu
    rw [Set.mem_setOf_eq] at hu
    rintro ⟨t, ht⟩
    have h1 := hR t
    rw [ht] at h1
    linarith
  have hfar_Kμ : {u : ℂ | R < ‖u‖} ⊆ (Set.range (fun t : ℝ => -η t))ᶜ := by
    intro u hu
    rw [Set.mem_setOf_eq] at hu
    rintro ⟨t, ht⟩
    have h2 : ‖u‖ ≤ R := by
      rw [← ht]
      simpa using hRμ t
    linarith [hu, h2]
  have hfar_ub : ¬ Bornology.IsBounded {u : ℂ | R < ‖u‖} := by
    intro hb
    obtain ⟨M, hM⟩ := hb.exists_norm_le
    set u : ℂ := (((max M (R + 1) + 1 : ℝ)) : ℂ) with hudef
    have hunorm : ‖u‖ = max M (R + 1) + 1 := by
      rw [hudef, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ max M (R + 1) + 1)]
    have humem : u ∈ {u : ℂ | R < ‖u‖} := by
      rw [Set.mem_setOf_eq, hunorm]
      have : R + 1 ≤ max M (R + 1) := le_max_right _ _
      linarith
    have h1 := hM u humem
    rw [hunorm] at h1
    have : M ≤ max M (R + 1) := le_max_left _ _
    linarith
  -- the far point
  set w : ℂ := ((R + 1 : ℝ) : ℂ) with hwdef
  have hwn : ‖w‖ = R + 1 := by
    rw [hwdef, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hwR : R < ‖w‖ := by rw [hwn]; linarith
  have hwfar : w ∈ {u : ℂ | R < ‖u‖} := by rw [Set.mem_setOf_eq, hwn]; linarith
  have hwK : w ∉ Set.range η := fun h => hfar_K hwfar h
  have hwnegK : (-w) ∉ Set.range (fun t : ℝ => -η t) := by
    rintro ⟨t, ht⟩
    exact hwK ⟨t, neg_inj.mp ht⟩
  have hnegwfar : (-w : ℂ) ∈ {u : ℂ | R < ‖u‖} := by
    rw [Set.mem_setOf_eq, norm_neg, hwn]
    linarith
  have hμc : Continuous fun t : ℝ => -η t := hη.neg
  have hμper : Function.Periodic (fun t : ℝ => -η t) (2 * Real.pi) := fun t => by
    simp only [hper t]
  have hμinj : Set.InjOn (fun t : ℝ => -η t) (Set.Ico 0 (2 * Real.pi)) :=
    fun a ha b hb hab => hinj ha hb (neg_inj.mp hab)
  have hμ0 : (0 : ℂ) ∉ Set.range (fun t : ℝ => -η t) := by
    rintro ⟨t, ht⟩
    exact h0 t (by simpa using ht)
  set U : Set ℂ := connectedComponentIn (Set.range η)ᶜ w with hUdef
  set V : Set ℂ := connectedComponentIn (Set.range η)ᶜ 0 with hVdef
  set U' : Set ℂ := connectedComponentIn (Set.range (fun t : ℝ => -η t))ᶜ (-w) with hU'def
  set V' : Set ℂ := connectedComponentIn (Set.range (fun t : ℝ => -η t))ᶜ 0 with hV'def
  have hKclosed : IsClosed (Set.range η) :=
    (Work.Topology.PlaneCurve.isCompact_range_of_periodic hη hper).isClosed
  have hμclosed : IsClosed (Set.range (fun t : ℝ => -η t)) :=
    (Work.Topology.PlaneCurve.isCompact_range_of_periodic hμc hμper).isClosed
  have hUo : IsOpen U := hKclosed.isOpen_compl.connectedComponentIn
  have hVo : IsOpen V := hKclosed.isOpen_compl.connectedComponentIn
  have hU'o : IsOpen U' := hμclosed.isOpen_compl.connectedComponentIn
  have hV'o : IsOpen V' := hμclosed.isOpen_compl.connectedComponentIn
  have hVpre : IsPreconnected V := isPreconnected_connectedComponentIn
  have hV'pre : IsPreconnected V' := isPreconnected_connectedComponentIn
  have hVmem : (0 : ℂ) ∈ V := mem_connectedComponentIn h0K
  have hV'mem : (0 : ℂ) ∈ V' := mem_connectedComponentIn hμ0
  -- the far exterior lies in `U` and in `U'`, so both are unbounded
  have hfar_U : {u : ℂ | R < ‖u‖} ⊆ U := by
    rw [hUdef]
    exact hfar_pre.subset_connectedComponentIn hwfar hfar_K
  have hUunbdd : ¬ Bornology.IsBounded U := fun hb => hfar_ub (hb.subset hfar_U)
  have hfar_U' : {u : ℂ | R < ‖u‖} ⊆ U' := by
    rw [hU'def]
    exact hfar_pre.subset_connectedComponentIn hnegwfar hfar_Kμ
  have hU'unbdd : ¬ Bornology.IsBounded U' := fun hb => hfar_ub (hb.subset hfar_U')
  have hUVne : U ≠ V := fun heq => hUunbdd (heq ▸ hbdd)
  have hUVdisj : Disjoint U V := by
    rw [Set.disjoint_left]
    intro p hpU hpV
    exact hUVne (by rw [hUdef, hVdef, connectedComponentIn_eq hpU, connectedComponentIn_eq hpV])
  -- `V` is contained in the ball of radius `R`
  have hVbdd : ∀ p ∈ V, ‖p‖ ≤ R := by
    intro p hp
    by_contra hcon
    have hgt : R < ‖p‖ := not_le.mp hcon
    have hpmem : p ∈ {u : ℂ | R < ‖u‖} := by rw [Set.mem_setOf_eq]; exact hgt
    have hcomp : connectedComponentIn (Set.range η)ᶜ p = connectedComponentIn (Set.range η)ᶜ 0 :=
      (connectedComponentIn_eq hp).symm
    have hsub : {u : ℂ | R < ‖u‖} ⊆ V := by
      rw [hVdef, ← hcomp]
      exact hfar_pre.subset_connectedComponentIn hpmem hfar_K
    exact hfar_ub (hbdd.subset hsub)
  have hVbd : Bornology.IsBounded V :=
    (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset (fun p hp => by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hVbdd p hp)
  -- `V'` is contained in `-V`, hence bounded with the same ball
  have hV'sub : V' ⊆ -V := by
    have hpre : IsPreconnected ((fun u : ℂ => -u) '' V') :=
      hV'pre.image _ continuous_neg.continuousOn
    have hsub : (fun u : ℂ => -u) '' V' ⊆ (Set.range η)ᶜ := by
      rintro v ⟨u, huV', rfl⟩
      have hu : u ∉ Set.range (fun t : ℝ => -η t) :=
        connectedComponentIn_subset _ _ huV'
      intro hv
      obtain ⟨t, ht⟩ := hv
      have h2 : -η t = u := by rw [ht]; ring
      exact hu ⟨t, h2⟩
    have hmem : (0 : ℂ) ∈ (fun u : ℂ => -u) '' V' := ⟨0, hV'mem, by simp⟩
    have hsubV : (fun u : ℂ => -u) '' V' ⊆ V := by
      rw [hVdef]
      exact hpre.subset_connectedComponentIn hmem hsub
    intro u hu
    have h1 : (-u : ℂ) ∈ V := hsubV ⟨u, hu, rfl⟩
    rw [Set.mem_neg]
    exact h1
  have hV'bdd : ∀ p ∈ V', ‖p‖ ≤ R := by
    intro p hp
    have h1 : (-p : ℂ) ∈ V := by
      have h2 : p ∈ -V := hV'sub hp
      rwa [Set.mem_neg] at h2
    have h3 := hVbdd (-p) h1
    rwa [norm_neg] at h3
  have hV'bd : Bornology.IsBounded V' :=
    (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset (fun p hp => by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hV'bdd p hp)
  have hU'V'ne : U' ≠ V' := fun heq => hU'unbdd (heq ▸ hV'bd)
  have hU'V'disj : Disjoint U' V' := by
    rw [Set.disjoint_left]
    intro p hpU hpV
    exact hU'V'ne (by rw [hU'def, hV'def, connectedComponentIn_eq hpU, connectedComponentIn_eq hpV])
  -- the two complements are not preconnected, so the frontiers are the traces
  have hdis : ¬ IsPreconnected (Set.range η)ᶜ := by
    intro hconn
    have hwV : w ∈ V := by
      rw [hVdef, hconn.connectedComponentIn h0K]
      exact hwK
    have h1 := hVbdd w hwV
    rw [hwn] at h1
    linarith
  have hdisμ : ¬ IsPreconnected (Set.range (fun t : ℝ => -η t))ᶜ := by
    intro hconn
    have hwV' : (-w : ℂ) ∈ V' := by
      rw [hV'def, hconn.connectedComponentIn hμ0]
      exact hwnegK
    have h1 := hV'bdd (-w) hwV'
    rw [norm_neg, hwn] at h1
    linarith
  have hfr : frontier V = Set.range η := by
    rw [hVdef]
    exact Work.Topology.PlaneCurve.frontier_component_eq_range hη hper hinj hdis 0 h0K
  have hfr' : frontier V' = Set.range (fun t : ℝ => -η t) := by
    rw [hV'def]
    exact Work.Topology.PlaneCurve.frontier_component_eq_range hμc hμper hμinj hdisμ 0 hμ0
  -- the two traces are disjoint
  have hdisjK : Disjoint (Set.range η) (Set.range (fun t : ℝ => -η t)) := by
    rw [Set.disjoint_left]
    rintro p ⟨s, hs⟩ ⟨t, ht⟩
    exact hanti s t (hs.trans ht.symm)
  have hnegKsub : Set.range (fun t : ℝ => -η t) ⊆ (Set.range η)ᶜ := fun p hp hpk =>
    (Set.disjoint_left.mp hdisjK) hpk hp
  have hKsub : Set.range η ⊆ (Set.range (fun t : ℝ => -η t))ᶜ := fun p hp hpk =>
    (Set.disjoint_left.mp hdisjK) hp hpk
  have hnegK : IsPreconnected (Set.range (fun t : ℝ => -η t)) := isPreconnected_range hμc
  have hKpre : IsPreconnected (Set.range η) := isPreconnected_range hη
  -- every point off the trace lies in `U` or in `V`
  have hucov : ∀ p : ℂ, p ∉ Set.range η → p ∈ U ∪ V := by
    intro p hp
    rcases Work.Topology.PlaneCurve.compl_jordan_atMostTwo hη hper hinj h0K hwK hp with h | h | h
    · exfalso
      have hwV : w ∈ V := by
        rw [hVdef, h]
        exact mem_connectedComponentIn hwK
      have h1 := hVbdd w hwV
      rw [hwn] at h1
      linarith
    · exact Or.inr (by rw [hVdef]; exact h ▸ mem_connectedComponentIn hp)
    · exact Or.inl (by rw [hUdef]; exact h ▸ mem_connectedComponentIn hp)
  have hucov' : ∀ p : ℂ, p ∉ Set.range (fun t : ℝ => -η t) → p ∈ U' ∪ V' := by
    intro p hp
    rcases Work.Topology.PlaneCurve.compl_jordan_atMostTwo hμc hμper hμinj hμ0 hwnegK hp with
      h | h | h
    · exfalso
      have hwV' : (-w : ℂ) ∈ V' := by
        rw [hV'def, h]
        exact mem_connectedComponentIn hwnegK
      have h1 := hV'bdd (-w) hwV'
      rw [norm_neg, hwn] at h1
      linarith
    · exact Or.inr (by rw [hV'def]; exact h ▸ mem_connectedComponentIn hp)
    · exact Or.inl (by rw [hU'def]; exact h ▸ mem_connectedComponentIn hp)
  -- the case analysis
  rcases hnegK.subset_or_subset hUo hVo hUVdisj (fun p hp => hucov p (hnegKsub hp)) with
    hKU | hKV
  · rcases hKpre.subset_or_subset hU'o hV'o hU'V'disj (fun p hp => hucov' p (hKsub hp)) with
      hKU' | hKV'
    · -- `K ⊆ U'` and `-K ⊆ U`: then `V = V'`, so the two traces coincide
      have hVsubV' : V ⊆ V' := by
        have hsub : V ⊆ U' ∪ V' := fun p hp =>
          hucov' p (fun hpk => (Set.disjoint_left.mp hUVdisj) (hKU hpk) hp)
        rcases hVpre.subset_or_subset hU'o hV'o hU'V'disj hsub with h | h
        · exact absurd (h hVmem) (fun h0U' => (Set.disjoint_left.mp hU'V'disj) h0U' hV'mem)
        · exact h
      have hV'subV : V' ⊆ V := by
        have hsub : V' ⊆ U ∪ V := fun p hp =>
          hucov p (fun hpk => (Set.disjoint_left.mp hU'V'disj) (hKU' hpk) hp)
        rcases hV'pre.subset_or_subset hUo hVo hUVdisj hsub with h | h
        · exact absurd (h hV'mem) (fun h0U => (Set.disjoint_left.mp hUVdisj) h0U hVmem)
        · exact h
      have heq : V = V' := Subset.antisymm hVsubV' hV'subV
      have hrange : Set.range η = Set.range (fun t : ℝ => -η t) := by
        rw [← hfr, ← hfr', heq]
      exact (Set.disjoint_left.mp hdisjK) ⟨0, rfl⟩ (by rw [← hrange]; exact ⟨0, rfl⟩)
    · -- `K ⊆ V'` and `-K ⊆ U`: the ray through the farthest point of `K` leaves `V'`
      have hpV' : η t₀ ∈ V' := hKV' ⟨t₀, rfl⟩
      have hpne : η t₀ ≠ 0 := h0 t₀
      obtain ⟨s, hsgt, hs⟩ := ray_exit hV'o hV'bd hfr' hpV' hpne
      obtain ⟨t, ht⟩ := hs
      have hnorm : ‖s • ((‖η t₀‖)⁻¹ • (η t₀))‖ = s := by
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (by linarith [hsgt, norm_nonneg (η t₀)])]
        congr 1
        rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (η t₀)),
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hpne), mul_one]
      have hle : ‖s • ((‖η t₀‖)⁻¹ • (η t₀))‖ ≤ R := by
        rw [← ht]
        exact hRμ t
      rw [hnorm, hRdef] at hle
      linarith
  · -- `-K ⊆ V`: the ray through the farthest point of `-K` leaves `V`
    have hpV : -(η t₀) ∈ V := hKV ⟨t₀, rfl⟩
    have hpne : -(η t₀) ≠ 0 := neg_ne_zero.mpr (h0 t₀)
    obtain ⟨s, hsgt, hs⟩ := ray_exit hVo hVbd hfr hpV hpne
    obtain ⟨t, ht⟩ := hs
    have hnorm : ‖s • ((‖-(η t₀)‖)⁻¹ • (-(η t₀)))‖ = s := by
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by linarith [hsgt, norm_nonneg (-(η t₀))])]
      congr 1
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (-(η t₀))),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hpne), mul_one]
    have hle : ‖s • ((‖-(η t₀)‖)⁻¹ • (-(η t₀)))‖ ≤ R := by
      rw [← ht]
      exact hR t
    rw [hnorm] at hle
    have hpR : ‖-(η t₀)‖ = R := by rw [norm_neg, hRdef]
    linarith

/-- **The crux, conditional on the "trap property".**  The trap property is the statement that for
an antipodal-free Jordan curve `η` avoiding `0`, the component of `0` in the complement of
`Set.range η ∪ Set.range (-η)` is unbounded.  Given it, the crux follows: if `windNumber γ hγ z = 0`
with `z` off the trace, then `γ - z` has a periodic continuous square root `η`; `η` is an
antipodal-free Jordan curve avoiding `0`, and the trap property produces an unbounded set `C` off the
trace of `η` and of `-η`; the map `q w = w * w + z` carries `C` into the complement of `range γ`
(since `q⁻¹ (range γ) = range η ∪ range (-η)`), `q '' C` is connected, unbounded and contains
`z = q 0`, so the component of `z` would be unbounded, contradicting the hypothesis. -/
theorem windNumber_ne_zero_of_bounded_component_of_trap
    (htrap : ∀ {η : ℝ → ℂ}, Continuous η → Function.Periodic η (2 * Real.pi) →
      Set.InjOn η (Set.Ico 0 (2 * Real.pi)) → (0 : ℂ) ∉ Set.range η →
      (∀ s t : ℝ, η s ≠ -η t) →
      ¬ Bornology.IsBounded
        (connectedComponentIn (Set.range η ∪ Set.range (fun t : ℝ => -η t))ᶜ (0 : ℂ)))
    {γ : ℝ → ℂ} (hγ : Continuous γ) (hper : Function.Periodic γ (2 * Real.pi))
    (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi))) {z : ℂ} (hz : z ∉ Set.range γ)
    (hbdd : Bornology.IsBounded (connectedComponentIn (Set.range γ)ᶜ z)) :
    windNumber γ hγ z ≠ 0 := by
  intro hzero
  have hz' : ∀ t : ℝ, γ t ≠ z := fun t ht => hz ⟨t, ht⟩
  obtain ⟨η, hsq, hne, hperη, -⟩ :=
    exists_sqrt_curve_of_even_windNumber hγ hper hz' (m := 0) (by rw [hzero]; ring)
  have h0η : (0 : ℂ) ∉ Set.range (fun t : ℝ => η t) := by
    rintro ⟨t, ht⟩
    exact hne t ht
  have hinjη : Set.InjOn (fun t : ℝ => η t) (Set.Ico 0 (2 * Real.pi)) := by
    intro s hs u hu hsu
    have hsu' : η s = η u := hsu
    have h1 : η s * η s = η u * η u := by rw [hsu']
    rw [hsq s, hsq u] at h1
    have h2 : γ s = γ u := by
      have h3 : γ s - z + z = γ u - z + z := congrArg (fun w : ℂ => w + z) h1
      simpa using h3
    exact hinj hs hu h2
  have hantiη : ∀ s t : ℝ, η s ≠ -η t := by
    intro s t hst
    have h1 : η s * η s = η t * η t := by rw [hst]; ring
    rw [hsq s, hsq t] at h1
    have hγst : γ s = γ t := by
      have h2 : γ s - z + z = γ t - z + z := congrArg (fun w : ℂ => w + z) h1
      simpa using h2
    obtain ⟨n, hn⟩ := exists_int_sub_eq_of_periodic_injOn hper hinj hγst
    have hs : s = t + (n : ℝ) * (2 * Real.pi) := by linarith [hn]
    have h2 : η s = η t := by
      rw [hs]
      exact (hperη.int_mul n) t
    rw [h2] at hst
    have h3 : η t = 0 := by linear_combination (1 / 2 : ℂ) * hst
    exact hne t h3
  have htrap' := htrap η.continuous hperη hinjη h0η hantiη
  set C : Set ℂ := connectedComponentIn
    (Set.range (fun t : ℝ => η t) ∪ Set.range (fun t : ℝ => -η t))ᶜ (0 : ℂ) with hCdef
  have h0U : (0 : ℂ) ∉ Set.range (fun t : ℝ => η t) ∪ Set.range (fun t : ℝ => -η t) := by
    rintro (h | h)
    · exact h0η h
    · obtain ⟨t, ht⟩ := h
      exact hne t (by simpa using ht)
  have h0C : (0 : ℂ) ∈ C := mem_connectedComponentIn h0U
  have hCunbdd : ¬ Bornology.IsBounded C := htrap'
  -- `q` maps `C` into the complement of the trace of `γ`
  have hq_sub : (fun u : ℂ => u * u + z) '' C ⊆ (Set.range γ)ᶜ := by
    rintro v ⟨u, huC, rfl⟩
    have hu_notin : u ∉ Set.range (fun t : ℝ => η t) ∪ Set.range (fun t : ℝ => -η t) :=
      connectedComponentIn_subset _ _ huC
    rintro ⟨s, hs⟩
    have h2 : u * u = η s * η s := by
      have h3 : η s * η s = γ s - z := hsq s
      have h4 : u * u = γ s - z := by
        rw [hs]; ring
      exact h4.trans h3.symm
    have hfac : (u - η s) * (u + η s) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp hfac with h' | h'
    · exact hu_notin (Or.inl ⟨s, (sub_eq_zero.mp h').symm⟩)
    · have h2' : η s = -u := by linear_combination h'
      refine hu_notin (Or.inr ?_)
      have h3 : -η s = u := by rw [h2']; ring
      exact ⟨s, h3⟩
  have hq_cont : Continuous fun u : ℂ => u * u + z := by fun_prop
  have hq_pre : IsPreconnected ((fun u : ℂ => u * u + z) '' C) :=
    (isPreconnected_connectedComponentIn).image _ hq_cont.continuousOn
  have hz_mem : z ∈ (fun u : ℂ => u * u + z) '' C := ⟨0, h0C, by ring⟩
  have hq_comp : (fun u : ℂ => u * u + z) '' C ⊆ connectedComponentIn (Set.range γ)ᶜ z :=
    hq_pre.subset_connectedComponentIn hz_mem hq_sub
  have hq_bdd : Bornology.IsBounded ((fun u : ℂ => u * u + z) '' C) := hbdd.subset hq_comp
  have hq_unbdd : ¬ Bornology.IsBounded ((fun u : ℂ => u * u + z) '' C) := by
    intro hb
    obtain ⟨M, hM⟩ := hb.exists_norm_le
    have hbig : ∃ u ∈ C, max M 0 + ‖z‖ + 2 < ‖u‖ := by
      by_contra hc
      push_neg at hc
      exact hCunbdd ((Metric.isBounded_closedBall (x := (0 : ℂ)) (r := max M 0 + ‖z‖ + 2)).subset
        (fun u hu => by rw [Metric.mem_closedBall, dist_zero_right]; exact hc u hu))
    obtain ⟨u, huC, hu⟩ := hbig
    have h1 : ‖u * u + z‖ ≤ M := hM _ ⟨u, huC, rfl⟩
    have h4 : ‖u * u + z‖ ≥ ‖u‖ ^ 2 - ‖z‖ := by
      have h5 := norm_sub_le (u * u + z) z
      rw [add_sub_cancel_right, norm_mul] at h5
      nlinarith [h5, norm_nonneg u, norm_nonneg z, sq_nonneg ‖u‖]
    have hu1 : 1 ≤ ‖u‖ := by
      have h7 := le_max_left M 0
      have h8 := le_max_right M 0
      have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
      linarith
    have hu_pos : 0 < ‖u‖ := by linarith
    have hprod : (max M 0 + ‖z‖ + 2) * ‖u‖ < ‖u‖ * ‖u‖ :=
      mul_lt_mul_of_pos_right hu hu_pos
    have h6 : M < ‖u‖ ^ 2 - ‖z‖ := by
      nlinarith [hprod, hu1, le_max_left M 0, norm_nonneg z]
    linarith
  exact hq_unbdd hq_bdd

end

end Work.Smooth.SphereJordan
