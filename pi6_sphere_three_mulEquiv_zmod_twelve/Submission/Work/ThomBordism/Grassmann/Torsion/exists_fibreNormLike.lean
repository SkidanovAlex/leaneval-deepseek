import Mathlib
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.Thom.Continuous
import Submission.Work.ThomBordism.Grassmann.IncidenceVector

set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

/-!
# A continuous, fibrewise-norm-like function on the tautological bundle

The function exhibited is the *Euclidean norm of the vector of the plane*,
`p ↦ ‖evalVec p‖` (`Work.ThomBordism.Grassmann.evalVec`): it is continuous (`continuous_evalVec`),
vanishes exactly on the zero section (`evalVec_eq_zero_iff`), is homogeneous in the fibre
(`evalVec_smul_snd`), and its sublevel set `{‖evalVec ·‖ ≤ 1}` is the fibrewise closed unit disc
bundle, which is compact.  The only serious point is the last one: the fibre coordinate
`(localTriv S p).2` of a *fixed* chart `S` is not comparable with `‖evalVec p‖` uniformly over all
of `baseSet S` (the chart-coordinate projection degenerates on the boundary), but it is comparable
on each *compact* piece of a finite cover of the Grassmannian (`exists_chartConditioning`), and a
partition of unity subordinate to the chart cover produces such a cover
(`exists_compact_pos_cover`).

## Main results

* `exists_fibreNormLike` — the target;
* `isCompact_localTrivDisc`, `exists_compact_pos_cover`, `exists_chartConditioning`,
  `isCompact_evalVec_le_one` — the steps.
-/

namespace Work.ThomBordism.Grassmann

open scoped Topology

noncomputable section

variable {k m : ℕ}

/-! ## Fibrewise linearity of the chart evaluation and of `evalVec` -/

theorem coordEval_smul (S : ChartIdx k m) (f : Stiefel k m) (c : ℝ) (v : Amb k) :
    coordEval S f (c • v) = c • coordEval S f v := by
  rw [coordEval, coordEval, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, mul_smul]

theorem evalChart_smul (S : ChartIdx k m) (x : ↥(baseSet S)) (c : ℝ) (w : Amb k) :
    evalChart S (x, c • w) = c • evalChart S (x, w) := by
  obtain ⟨f, hf⟩ : ∃ f : Stiefel k m, (x : OG k m) = Quotient.mk'' f :=
    ⟨Quotient.out _, (Quotient.out_eq _).symm⟩
  have hfc : f ∈ chartSet S := (mem_baseSet_iff S f).mp (hf ▸ x.2)
  rw [evalChart_spec S x f hfc hf (c • w), evalChart_spec S x f hfc hf w, coordEval_smul]

theorem evalChartO_smul (S : ChartIdx k m) (x : ↥(baseSet S)) (c : ℝ) (v : Amb k) :
    evalChartO S x (c • v) = c • evalChartO S x v := by
  rw [evalChartO, evalChartO, ContinuousLinearMap.map_smul, evalChart_smul]

theorem evalVec_smul_snd (k m : ℕ) (c : ℝ) (p : (tautologicalBundle k m).TotalSpace) :
    evalVec (k := k) (m := m) ⟨p.1, c • p.2⟩ = c • evalVec (k := k) (m := m) p := by
  have hpp : p.1 ∈ (tautologicalBundle k m).baseSet ((tautologicalBundle k m).indexAt p.1) :=
    (tautologicalBundle k m).mem_baseSet_at p.1
  have hqq : (⟨p.1, c • p.2⟩ : (tautologicalBundle k m).TotalSpace).1 ∈
      (tautologicalBundle k m).baseSet ((tautologicalBundle k m).indexAt p.1) := hpp
  rw [evalVec_apply_chart (k := k) (m := m) p ((tautologicalBundle k m).indexAt p.1) hpp,
    evalVec_apply_chart (k := k) (m := m) (⟨p.1, c • p.2⟩ : (tautologicalBundle k m).TotalSpace)
      ((tautologicalBundle k m).indexAt p.1) hqq]
  have hlin : ((tautologicalBundle k m).localTriv ((tautologicalBundle k m).indexAt p.1)
        (⟨p.1, c • p.2⟩ : (tautologicalBundle k m).TotalSpace)).2
      = c • ((tautologicalBundle k m).localTriv ((tautologicalBundle k m).indexAt p.1) p).2 := by
    rw [VectorBundleCore.localTriv_apply, VectorBundleCore.localTriv_apply]
    exact ContinuousLinearMap.map_smul _ c p.2
  rw [hlin, evalChartO_smul]



end

end Work.ThomBordism.Grassmann

namespace Work.ThomBordism.Grassmann.Torsion

open Work.ThomBordism.Grassmann

/-! ## Two supporting lemmas -/

theorem isCompact_localTrivDisc
    {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [ProperSpace F] {ι : Type*} (Z : VectorBundleCore ℝ B F ι) (S : ι) (C : Set B)
    (hC : IsCompact C) (hCU : C ⊆ Z.baseSet S) (r : ℝ) :
    IsCompact {p : Z.TotalSpace | p.1 ∈ C ∧ ‖(Z.localTriv S p).2‖ ≤ r} := by
  set e := Z.localTriv S
  have hK : IsCompact (C ×ˢ Metric.closedBall (0 : F) r) :=
    hC.prod (isCompact_closedBall (0 : F) r)
  have hKtgt : C ×ˢ Metric.closedBall (0 : F) r ⊆ e.target := by
    intro q hq
    rw [Bundle.Trivialization.mem_target]
    exact hCU hq.1
  have hcont : ContinuousOn (fun q : B × F => e.toOpenPartialHomeomorph.symm q)
      (C ×ˢ Metric.closedBall (0 : F) r) :=
    (e.toOpenPartialHomeomorph.continuousOn_invFun).mono hKtgt
  have himg : e.toOpenPartialHomeomorph.symm '' (C ×ˢ Metric.closedBall (0 : F) r)
      = {p : Z.TotalSpace | p.1 ∈ C ∧ ‖(e p).2‖ ≤ r} := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨hqC, hqr⟩ := hq
      rw [Metric.mem_closedBall, dist_zero_right] at hqr
      have hqt : q ∈ e.target := hKtgt ⟨hqC, by rw [Metric.mem_closedBall, dist_zero_right]; exact hqr⟩
      have hs : e.toOpenPartialHomeomorph.symm q ∈ e.source :=
        e.toOpenPartialHomeomorph.map_target hqt
      have heq : e (e.toOpenPartialHomeomorph.symm q) = q :=
        e.toOpenPartialHomeomorph.right_inv hqt
      have hfst : (e.toOpenPartialHomeomorph.symm q).1 = q.1 := by
        have h1 : (e.toOpenPartialHomeomorph.symm q).1
            = (e (e.toOpenPartialHomeomorph.symm q)).1 := (e.proj_toFun _ hs).symm
        rw [h1, heq]
      have hsnd : (e (e.toOpenPartialHomeomorph.symm q)).2 = q.2 := by rw [heq]
      exact ⟨by rw [hfst]; exact hqC, by rw [hsnd]; exact hqr⟩
    · rintro ⟨hpC, hpr⟩
      have hps : p ∈ e.source := by
        rw [VectorBundleCore.mem_localTriv_source]
        exact hCU hpC
      refine ⟨e p, ⟨?_, ?_⟩, ?_⟩
      · have h1 : (e p).1 = p.1 := e.proj_toFun p hps
        rw [h1]; exact hpC
      · rw [Metric.mem_closedBall, dist_zero_right]; exact hpr
      · exact e.toOpenPartialHomeomorph.left_inv hps
  rw [← himg]
  exact IsCompact.image_of_continuousOn hK hcont

/-- **A partition of unity on a compact space has a uniform positive threshold**, and the compact
sets where it exceeds the threshold cover the space. -/
theorem exists_compact_pos_cover
    {ι X : Type*} [TopologicalSpace X] [Fintype ι] [CompactSpace X]
    (ρ : PartitionOfUnity ι X Set.univ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : ι → Set X,
      (∀ i, IsCompact (C i)) ∧ (∀ i, C i ⊆ {x | ε ≤ (ρ i) x}) ∧ (∀ x, ∃ i, x ∈ C i) := by
  classical
  refine ⟨1 / ((Fintype.card ι : ℝ) + 1), by positivity,
    fun i => {x | 1 / ((Fintype.card ι : ℝ) + 1) ≤ (ρ i) x}, ?_, ?_, ?_⟩
  · intro i
    exact (isClosed_le continuous_const (ρ i).continuous).isCompact
  · intro i x hx
    exact hx
  · intro x
    by_contra h
    have hlt : ∀ i, (ρ i) x < 1 / ((Fintype.card ι : ℝ) + 1) := by
      intro i
      by_contra hc
      exact h ⟨i, not_lt.mp hc⟩
    have hsum : ∑ i : ι, (ρ i) x = 1 := by
      rw [← finsum_eq_sum_of_support_subset (fun i => (ρ i) x) (s := Finset.univ)
        (fun i _ => Finset.mem_univ i)]
      exact ρ.sum_eq_one (Set.mem_univ x)
    rcases isEmpty_or_nonempty ι with hι | hι
    · have hzero : ∑ i : ι, (ρ i) x = 0 := by
        refine Finset.sum_eq_zero (fun i _ => ?_)
        exact (hι.false i).elim
      linarith
    · have hne : (Finset.univ : Finset ι).Nonempty := Finset.univ_nonempty
      have hle : ∑ _i : ι, (1 / ((Fintype.card ι : ℝ) + 1) : ℝ) ≤ ∑ i : ι, (ρ i) x := by
        rw [hsum, Finset.sum_const, nsmul_eq_mul, one_div, ← div_eq_mul_inv]
        rw [div_le_one (by positivity)]
        exact le_add_of_nonneg_right (by positivity)
      obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le hne hle
      exact absurd hi (not_le.mpr (hlt i))


/-- **The chart coordinate is controlled by the Euclidean norm of the vector of the plane, on any
compact piece of a chart.**  For a compact `C S ⊆ baseSet S` there is a constant `R S ≥ 0` with
`1 ≤ R S * ‖evalChartO S x v‖` for all `x ∈ C S` and all *unit* `v`; equivalently, over `C S` the
chart coordinate projection is bounded by `R S` times the Euclidean norm of the vector of the plane.
This is where compactness of `C S` is used: the minimum of the continuous, strictly positive
function `(x, v) ↦ ‖evalChartO S x v‖` over the compact set `C S ×ˢ sphere 0 1` is positive. -/
theorem exists_chartConditioning (k m : ℕ) (C : ChartIdx k m → Set (OG k m))
    (hCcomp : ∀ S, IsCompact (C S)) (hCU : ∀ S, C S ⊆ baseSet S) :
    ∃ R : ChartIdx k m → ℝ, (∀ S, 0 ≤ R S) ∧
      ∀ S, ∀ x : OG k m, x ∈ C S → ∀ hx : x ∈ baseSet S,
        ∀ v : Amb k, ‖v‖ = 1 → 1 ≤ R S * ‖evalChartO S ⟨x, hx⟩ v‖ := by
  classical
  have hR : ∀ S : ChartIdx k m, ∃ R : ℝ, 0 ≤ R ∧
      ∀ x : OG k m, x ∈ C S → ∀ hx : x ∈ baseSet S,
        ∀ v : Amb k, ‖v‖ = 1 → 1 ≤ R * ‖evalChartO S ⟨x, hx⟩ v‖ := by
    intro S
    by_cases hK : (Set.univ ×ˢ Metric.sphere (0 : Amb k) 1 :
        Set (↥(C S) × Amb k)).Nonempty
    · have : CompactSpace ↥(C S) := isCompact_iff_compactSpace.mp (hCcomp S)
      have hcont : Continuous fun q : ↥(C S) × Amb k =>
          ‖evalChartO S (⟨q.1.1, hCU S q.1.2⟩ : ↥(baseSet S)) q.2‖ := by
        have h1 : Continuous fun q : ↥(C S) => (⟨q.1, hCU S q.2⟩ : ↥(baseSet S)) :=
          continuous_subtype_val.subtype_mk (fun q => hCU S q.2)
        have h2 : Continuous fun q : ↥(C S) × Amb k =>
            ((⟨q.1.1, hCU S q.1.2⟩ : ↥(baseSet S)), q.2) :=
          (h1.comp continuous_fst).prodMk continuous_snd
        exact ((continuous_evalChartO S).comp h2).norm
      have hKc : IsCompact (Set.univ ×ˢ Metric.sphere (0 : Amb k) 1 :
          Set (↥(C S) × Amb k)) :=
        isCompact_univ.prod (isCompact_sphere (0 : Amb k) 1)
      obtain ⟨q, hq, hmin⟩ := hKc.exists_isMinOn hK hcont.continuousOn
      have hq2 : q.2 ≠ 0 := by
        have h := Metric.mem_sphere.mp hq.2
        rw [dist_zero_right] at h
        exact norm_ne_zero_iff.mp (by rw [h]; exact one_ne_zero)
      have hpos : 0 < ‖evalChartO S (⟨q.1.1, hCU S q.1.2⟩ : ↥(baseSet S)) q.2‖ :=
        norm_pos_iff.mpr fun h0 =>
          hq2 ((evalChartO_eq_zero_iff S ⟨q.1.1, hCU S q.1.2⟩ q.2).mp h0)
      refine ⟨1 / ‖evalChartO S (⟨q.1.1, hCU S q.1.2⟩ : ↥(baseSet S)) q.2‖,
        div_nonneg zero_le_one (le_of_lt hpos), ?_⟩
      intro x hx hxbase v hv
      have hmem : ((⟨x, hx⟩ : ↥(C S)), v) ∈ (Set.univ ×ˢ Metric.sphere (0 : Amb k) 1 :
          Set (↥(C S) × Amb k)) :=
        ⟨Set.mem_univ _, by rw [Metric.mem_sphere, dist_zero_right]; exact hv⟩
      have hle : ‖evalChartO S (⟨q.1.1, hCU S q.1.2⟩ : ↥(baseSet S)) q.2‖
          ≤ ‖evalChartO S (⟨x, hCU S hx⟩ : ↥(baseSet S)) v‖ :=
        (isMinOn_iff.mp hmin) (⟨x, hx⟩, v) hmem
      have hsub : (⟨x, hCU S hx⟩ : ↥(baseSet S)) = ⟨x, hxbase⟩ := Subtype.ext rfl
      rw [hsub] at hle
      rw [one_div, inv_mul_eq_div, one_le_div hpos]
      exact hle
    · exact ⟨1, zero_le_one, fun x hx hxbase v hv =>
        absurd (show ((⟨x, hx⟩ : ↥(C S)), v) ∈ (Set.univ ×ˢ Metric.sphere (0 : Amb k) 1 :
            Set (↥(C S) × Amb k)) from
          ⟨Set.mem_univ _, by rw [Metric.mem_sphere, dist_zero_right]; exact hv⟩)
          fun hnn => hK ⟨((⟨x, hx⟩ : ↥(C S)), v), hnn⟩⟩
  choose R hRnn hRspec using hR
  exact ⟨R, hRnn, hRspec⟩


/-- **The fibrewise closed unit disc bundle `{p | ‖evalVec p‖ ≤ 1}` of the tautological bundle is
compact.**  It is closed (`evalVec` is continuous) and contained in the union of the compact chart
discs over a finite compact cover of the Grassmannian. -/
theorem isCompact_evalVec_le_one (k m : ℕ) :
    IsCompact {p : (tautologicalBundle k m).TotalSpace | ‖evalVec (k := k) (m := m) p‖ ≤ 1} := by
  classical
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate (s := Set.univ) isClosed_univ
    (fun S : ChartIdx k m => baseSet S) (fun S => isOpen_baseSet S)
    (fun x _ => Set.mem_iUnion.mpr (exists_mem_baseSet x))
  obtain ⟨ε, hε, C, hCcomp, hClb, hCcov⟩ := exists_compact_pos_cover ρ
  have hCU : ∀ S : ChartIdx k m, C S ⊆ baseSet S := by
    intro S x hx
    exact hρ S (subset_closure (Function.mem_support.mpr
      (ne_of_gt (lt_of_lt_of_le hε (hClb S hx)))))
  have hCU' : ∀ S : ChartIdx k m, C S ⊆ (tautologicalBundle k m).baseSet S :=
    fun S x hx => hCU S hx
  obtain ⟨R, hRnn, hRspec⟩ := exists_chartConditioning k m C hCcomp hCU
  have hclosed : IsClosed {p : (tautologicalBundle k m).TotalSpace |
      ‖evalVec (k := k) (m := m) p‖ ≤ 1} :=
    isClosed_le continuous_evalVec.norm continuous_const
  have hsub : {p : (tautologicalBundle k m).TotalSpace | ‖evalVec (k := k) (m := m) p‖ ≤ 1} ⊆
      ⋃ S : ChartIdx k m, {p : (tautologicalBundle k m).TotalSpace |
        p.1 ∈ C S ∧ ‖((tautologicalBundle k m).localTriv S p).2‖ ≤ R S} := by
    intro p hp
    obtain ⟨S, hS⟩ := hCcov p.1
    refine Set.mem_iUnion.mpr ⟨S, hS, ?_⟩
    have hxS : p.1 ∈ baseSet S := hCU S hS
    have hxS' : p.1 ∈ (tautologicalBundle k m).baseSet S := hxS
    rcases eq_or_ne ((tautologicalBundle k m).localTriv S p).2 0 with hv | hv
    · rw [hv, norm_zero]
      exact hRnn S
    · have hnorm : ‖(((tautologicalBundle k m).localTriv S p).2)‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      have hv1 : ‖(‖(((tautologicalBundle k m).localTriv S p).2)‖)⁻¹ •
          (((tautologicalBundle k m).localTriv S p).2)‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hnorm]
      have hb := hRspec S p.1 hS hxS _ hv1
      rw [evalChartO_smul, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] at hb
      have hpe : ‖evalChartO S ⟨p.1, hxS⟩ (((tautologicalBundle k m).localTriv S p).2)‖ ≤ 1 := by
        rw [← evalVec_apply_chart p S hxS']
        exact hp
      have h2 : ‖(((tautologicalBundle k m).localTriv S p).2)‖
          ≤ R S * ‖evalChartO S ⟨p.1, hxS⟩ (((tautologicalBundle k m).localTriv S p).2)‖ := by
        have h3 := mul_le_mul_of_nonneg_right hb (norm_nonneg _ :
          0 ≤ ‖(((tautologicalBundle k m).localTriv S p).2)‖)
        rw [one_mul] at h3
        have hcalc : R S * ((‖(((tautologicalBundle k m).localTriv S p).2)‖)⁻¹ *
            ‖evalChartO S ⟨p.1, hxS⟩ (((tautologicalBundle k m).localTriv S p).2)‖) *
            ‖(((tautologicalBundle k m).localTriv S p).2)‖
            = R S * ‖evalChartO S ⟨p.1, hxS⟩ (((tautologicalBundle k m).localTriv S p).2)‖ := by
          have h1 : (‖(((tautologicalBundle k m).localTriv S p).2)‖)⁻¹ *
              ‖(((tautologicalBundle k m).localTriv S p).2)‖ = 1 := inv_mul_cancel₀ hnorm
          calc R S * ((‖(((tautologicalBundle k m).localTriv S p).2)‖)⁻¹ *
                ‖evalChartO S ⟨p.1, hxS⟩ (((tautologicalBundle k m).localTriv S p).2)‖) *
                ‖(((tautologicalBundle k m).localTriv S p).2)‖
              = R S * ‖evalChartO S ⟨p.1, hxS⟩ (((tautologicalBundle k m).localTriv S p).2)‖ *
                ((‖(((tautologicalBundle k m).localTriv S p).2)‖)⁻¹ *
                ‖(((tautologicalBundle k m).localTriv S p).2)‖) := by ring
            _ = R S * ‖evalChartO S ⟨p.1, hxS⟩ (((tautologicalBundle k m).localTriv S p).2)‖ := by
                rw [h1, mul_one]
        rwa [hcalc] at h3
      refine le_trans h2 ?_
      calc R S * ‖evalChartO S ⟨p.1, hxS⟩ (((tautologicalBundle k m).localTriv S p).2)‖
          ≤ R S * 1 := mul_le_mul_of_nonneg_left hpe (hRnn S)
        _ = R S := mul_one _
  have hUnion : IsCompact (⋃ S : ChartIdx k m, {p : (tautologicalBundle k m).TotalSpace |
      p.1 ∈ C S ∧ ‖((tautologicalBundle k m).localTriv S p).2‖ ≤ R S}) :=
    isCompact_iUnion fun S =>
      isCompact_localTrivDisc (tautologicalBundle k m) S (C S) (hCcomp S) (hCU' S) (R S)
  exact hUnion.of_isClosed_subset hclosed hsub


/-- **A continuous, fibrewise-norm-like function on the total space of the tautological bundle**
`γ = Work.ThomBordism.Grassmann.tautologicalBundle k m`: a continuous function which is nonnegative,
homogeneous in the fibre, vanishes exactly on the zero section, and whose sublevel set `{f ≤ 1}` is
compact.

The witness is `p ↦ ‖evalVec p‖`, the Euclidean norm of the vector of the plane represented by `p`
(`Work.ThomBordism.Grassmann.evalVec`): continuity is `continuous_evalVec`, vanishing exactly on the
zero section is `evalVec_eq_zero_iff`, and fibrewise homogeneity is `evalVec_smul_snd`.

The compactness of `{‖evalVec ·‖ ≤ 1}` is the substance: it is `isCompact_evalVec_le_one`, which
compares the Euclidean norm of the vector of the plane with the fibre coordinate of `localTriv S`
for a *finite family of charts covering the compact Grassmannian by compact pieces*
(`exists_compact_pos_cover`, from a partition of unity subordinate to the chart cover).  Note that
the classical recipe `f p = ∑_S ρ_S p.1 * ‖(localTriv S p).2‖` does *not* avoid this comparison:
the coordinate projection of a chart degenerates on the boundary of `baseSet S`, so the comparison
with `‖(localTriv S p).2‖` holds only with a constant depending on `p.1`, uniformly on compact pieces
of the base — which is exactly what `exists_chartConditioning` supplies, while `evalVec` supplies the
continuous function itself. -/
theorem exists_fibreNormLike (k m : ℕ) :
    ∃ f : (Work.ThomBordism.Grassmann.tautologicalBundle k m).TotalSpace → ℝ,
      Continuous f ∧ (∀ p, 0 ≤ f p) ∧
      (∀ (c : ℝ) (p : (Work.ThomBordism.Grassmann.tautologicalBundle k m).TotalSpace),
        0 ≤ c → f ⟨p.1, c • p.2⟩ = c * f p) ∧
      (∀ p : (Work.ThomBordism.Grassmann.tautologicalBundle k m).TotalSpace,
        f p = 0 ↔ (show EuclideanSpace ℝ (Fin k) from p.2) = 0) ∧
      IsCompact {p : (Work.ThomBordism.Grassmann.tautologicalBundle k m).TotalSpace | f p ≤ 1} := by
  refine ⟨fun p => ‖evalVec (k := k) (m := m) p‖, continuous_evalVec.norm,
    fun p => norm_nonneg _, ?_, ?_, isCompact_evalVec_le_one k m⟩
  · intro c p hc
    show ‖evalVec (k := k) (m := m) ⟨p.1, c • p.2⟩‖ = c * ‖evalVec (k := k) (m := m) p‖
    rw [evalVec_smul_snd, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  · intro p
    show ‖evalVec (k := k) (m := m) p‖ = 0 ↔ (show EuclideanSpace ℝ (Fin k) from p.2) = 0
    rw [norm_eq_zero]
    exact evalVec_eq_zero_iff p


end Work.ThomBordism.Grassmann.Torsion
