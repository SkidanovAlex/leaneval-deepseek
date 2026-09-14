import Submission.NBody.MarchalClusterBound
import Submission.NBody.MarchalForce
import Submission.NBody.PairKernel
import Submission.Commons.Analysis.InnerProduct.exists_inner_pos_extreme

/-!
# The standard variation of a colliding cluster

Ferrario--Terracini's *standard variation* (`defi:standard_variation`): the displacement which is
constant equal to `δ` on `[0, T - ‖δ‖]` and returns linearly to `0` at time `T`.

For a colliding cluster `k` we need a *centred* variant: the perturbation of the configuration which
moves `i₀` by `(1 - mᵢ₀/m_k) v` and every other body of `k` by `-(mᵢ₀/m_k) v`.  The resulting
displacement field is centred (`∑_{j∈k} m_j · (disp) j = 0`), so that the centre of mass of the
cluster is not moved, and the difference between `i₀` and every other body of the cluster is exactly
`v`.

Finally we record the elementary *outward direction lemma* in the form needed here: for any
collision-free configuration of a cluster with at least two bodies there is a body `i₀` and a
nonzero direction `δ` such that `i₀` is moved strictly away from all the other bodies of the
cluster.
-/

open Set Real Metric Finset InnerProductSpace
open scoped BigOperators Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Submission.NBody

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

/-- The scalar coefficient of the **standard variation** of a displacement `δ` on `[0,T]`. -/
noncomputable def stdCoef (δ : E) (T t : ℝ) : ℝ := min 1 (max 0 ((T - t) / ‖δ‖))

/-- The **standard variation** of a displacement `δ` on the time interval `[0,T]`: the constant
displacement `δ` up to time `T - ‖δ‖`, followed by a linear return to `0` at time `T`. -/
noncomputable def stdVar (δ : E) (T t : ℝ) : E := stdCoef δ T t • δ

lemma stdCoef_nonneg (δ : E) (T t : ℝ) : 0 ≤ stdCoef δ T t := le_min zero_le_one (le_max_left _ _)

lemma stdCoef_le_one (δ : E) (T t : ℝ) : stdCoef δ T t ≤ 1 := min_le_left _ _

lemma stdCoef_of_le {δ : E} {T t : ℝ} (hδ : δ ≠ 0) (h : t ≤ T - ‖δ‖) : stdCoef δ T t = 1 := by
  have h0 : (0:ℝ) < ‖δ‖ := norm_pos_iff.mpr hδ
  have h1 : 1 ≤ (T - t) / ‖δ‖ := by
    rw [le_div_iff₀ h0]; linarith
  have h2 : (0:ℝ) ≤ (T - t) / ‖δ‖ := le_trans zero_le_one h1
  rw [stdCoef, max_eq_right h2, min_eq_left h1]

lemma stdCoef_of_ge {δ : E} {T t : ℝ} (hδ : δ ≠ 0) (h : T ≤ t) : stdCoef δ T t = 0 := by
  have h0 : (0:ℝ) < ‖δ‖ := norm_pos_iff.mpr hδ
  have h1 : (T - t) / ‖δ‖ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) h0.le
  simp only [stdCoef, max_eq_left h1, min_eq_right zero_le_one]

lemma stdCoef_of_mem {δ : E} {T t : ℝ} (hδ : δ ≠ 0) (h1 : T - ‖δ‖ ≤ t) (h2 : t ≤ T) :
    stdCoef δ T t = (T - t) / ‖δ‖ := by
  have h0 : (0:ℝ) < ‖δ‖ := norm_pos_iff.mpr hδ
  have h3 : 0 ≤ (T - t) / ‖δ‖ := div_nonneg (by linarith) h0.le
  have h4 : (T - t) / ‖δ‖ ≤ 1 := by
    rw [div_le_one h0]; linarith
  rw [stdCoef, max_eq_right h3, min_eq_right h4]

lemma stdVar_of_le {δ : E} {T t : ℝ} (hδ : δ ≠ 0) (h : t ≤ T - ‖δ‖) : stdVar δ T t = δ := by
  rw [stdVar, stdCoef_of_le hδ h, one_smul]

lemma stdVar_of_ge {δ : E} {T t : ℝ} (hδ : δ ≠ 0) (h : T ≤ t) : stdVar δ T t = 0 := by
  rw [stdVar, stdCoef_of_ge hδ h, zero_smul]

lemma stdVar_of_mem {δ : E} {T t : ℝ} (hδ : δ ≠ 0) (h1 : T - ‖δ‖ ≤ t) (h2 : t ≤ T) :
    stdVar δ T t = ((T - t) / ‖δ‖) • δ := by
  rw [stdVar, stdCoef_of_mem hδ h1 h2]

lemma norm_stdVar (δ : E) (T t : ℝ) : ‖stdVar δ T t‖ = stdCoef δ T t * ‖δ‖ := by
  rw [stdVar, norm_smul, Real.norm_eq_abs, abs_of_nonneg (stdCoef_nonneg _ _ _)]

lemma norm_stdVar_le (δ : E) (T t : ℝ) : ‖stdVar δ T t‖ ≤ ‖δ‖ := by
  rw [norm_stdVar]
  calc stdCoef δ T t * ‖δ‖ ≤ 1 * ‖δ‖ := by
        exact mul_le_mul_of_nonneg_right (stdCoef_le_one _ _ _) (norm_nonneg δ)
    _ = ‖δ‖ := one_mul _

lemma norm_stdVar_of_mem {δ : E} {T t : ℝ} (hδ : δ ≠ 0) (h1 : T - ‖δ‖ ≤ t) (h2 : t ≤ T) :
    ‖stdVar δ T t‖ = T - t := by
  rw [norm_stdVar, stdCoef_of_mem hδ h1 h2, div_mul_cancel₀ _ (norm_pos_iff.mpr hδ).ne']

lemma continuous_stdVar {δ : E} {T : ℝ} (hδ : δ ≠ 0) : Continuous (stdVar δ T) := by
  have h0 : (0:ℝ) < ‖δ‖ := norm_pos_iff.mpr hδ
  have hc : Continuous fun t : ℝ => min 1 (max 0 ((T - t) / ‖δ‖)) := by fun_prop
  exact hc.smul continuous_const

lemma hasDerivAt_stdVar_const {δ : E} {T t : ℝ} (hδ : δ ≠ 0) (h : t < T - ‖δ‖) :
    HasDerivAt (stdVar δ T) 0 t := by
  refine (hasDerivAt_const (c := δ) (x := t)).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Iio.mem_nhds h] with s hs
  exact stdVar_of_le hδ hs.le

lemma hasDerivAt_stdVar_lin {δ : E} {T t : ℝ} (hδ : δ ≠ 0) (h1 : T - ‖δ‖ < t) (h2 : t < T) :
    HasDerivAt (stdVar δ T) ((-(‖δ‖)⁻¹) • δ) t := by
  have hev : ∀ᶠ s in 𝓝 t, stdVar δ T s = ((T - s) / ‖δ‖) • δ := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨h1, h2⟩] with s hs
    exact stdVar_of_mem hδ hs.1.le hs.2.le
  refine (HasDerivAt.congr_of_eventuallyEq ?_ hev)
  have h4 : HasDerivAt (fun s : ℝ => T - s) (-1) t := by
    have h := (hasDerivAt_id (x := t)).const_sub T
    simpa using h
  have h5 : HasDerivAt (fun s : ℝ => (T - s) / ‖δ‖) (-(‖δ‖)⁻¹) t := by
    have h := h4.div_const ‖δ‖
    have h2 : (-1/‖δ‖ : ℝ) = -(‖δ‖⁻¹) := by rw [neg_div, one_div]
    rw [h2] at h
    exact h
  simpa using h5.smul_const δ

lemma hasDerivAt_stdVar_out {δ : E} {T t : ℝ} (hδ : δ ≠ 0) (h : T < t) :
    HasDerivAt (stdVar δ T) 0 t := by
  refine (hasDerivAt_const (c := (0:E)) (x := t)).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds h] with s hs
  exact stdVar_of_ge hδ hs.le

/-! ## The centred perturbation of a cluster -/

variable {m : Fin N → ℝ} {k : Finset (Fin N)} {i₀ : Fin N}

/-- The vector by which the **standard variation** displaces the bodies of the cluster: `i₀` is moved
by `(1 - mᵢ₀/m_k) v` and every other body of `k` by `-(mᵢ₀/m_k) v`.  With this choice the
displacement is *centred* (`∑_{j∈k} m_j · (disp) j = 0`), while the difference between `i₀` and any
other body of `k` is exactly `v`. -/
noncomputable def stdPertVec (m : Fin N → ℝ) (k : Finset (Fin N)) (i₀ : Fin N) (v : E) : EN E N :=
  ∑ j ∈ k, singleBodyVec j (((if j = i₀ then 1 else 0) - m i₀ / clusterMass m k) • v)

/-- The perturbation of the configuration given by the standard variation of the displacement `δ`. -/
noncomputable def stdPert (m : Fin N → ℝ) (k : Finset (Fin N)) (i₀ : Fin N) (δ : E) (T : ℝ) :
    ℝ → EN E N :=
  fun t => stdPertVec m k i₀ (stdVar δ T t)

lemma stdPertVec_apply_of_mem {j : Fin N} (hj : j ∈ k) (v : E) :
    stdPertVec m k i₀ v j = ((if j = i₀ then 1 else 0) - m i₀ / clusterMass m k) • v := by
  classical
  rw [stdPertVec, WithLp.ofLp_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single j]
  · rw [singleBodyVec_self]
  · intro b _ hb; exact singleBodyVec_of_ne (fun h => hb h.symm) _
  · intro h; exact absurd hj h

lemma stdPertVec_apply_of_notMem {j : Fin N} (hj : j ∉ k) (v : E) : stdPertVec m k i₀ v j = 0 := by
  classical
  rw [stdPertVec, WithLp.ofLp_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun b hb => ?_
  refine singleBodyVec_of_ne (fun h => hj ?_) _
  rwa [h]

lemma stdPertVec_sub_i₀ {j : Fin N} (hi₀ : i₀ ∈ k) (hj : j ∈ k) (hjne : j ≠ i₀) (v : E) :
    stdPertVec m k i₀ v i₀ - stdPertVec m k i₀ v j = v := by
  rw [stdPertVec_apply_of_mem hi₀, stdPertVec_apply_of_mem hj, if_pos rfl, if_neg hjne]
  simp only [sub_smul, one_smul, zero_smul]
  abel

lemma norm_coef_le_one {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {i₀ : Fin N} (hi₀ : i₀ ∈ k) :
    ∀ j ∈ k, ‖((if j = i₀ then 1 else 0) - m i₀ / clusterMass m k : ℝ)‖ ≤ 1 := by
  have hmk : 0 < clusterMass m k := clusterMass_pos hm ⟨i₀, hi₀⟩
  have hle : m i₀ ≤ clusterMass m k := by
    rw [clusterMass]
    exact Finset.single_le_sum (fun i _ => (hm i).le) hi₀
  have h0 : 0 ≤ m i₀ / clusterMass m k := div_nonneg (hm i₀).le hmk.le
  have h1 : m i₀ / clusterMass m k ≤ 1 := (div_le_one hmk).mpr hle
  intro j hj
  rw [Real.norm_eq_abs]
  by_cases h : j = i₀
  · rw [if_pos h, abs_le]; constructor <;> linarith
  · rw [if_neg h, abs_le]; constructor <;> linarith

lemma norm_stdPertVec_apply_le {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {i₀ : Fin N}
    (hi₀ : i₀ ∈ k) (v : E) (j : Fin N) : ‖stdPertVec m k i₀ v j‖ ≤ ‖v‖ := by
  classical
  by_cases hj : j ∈ k
  · rw [stdPertVec_apply_of_mem hj, norm_smul, Real.norm_eq_abs]
    calc |((if j = i₀ then 1 else 0) - m i₀ / clusterMass m k : ℝ)| * ‖v‖
        ≤ 1 * ‖v‖ :=
          mul_le_mul_of_nonneg_right (norm_coef_le_one (m := m) hm hi₀ j hj) (norm_nonneg v)
      _ = ‖v‖ := one_mul _
  · rw [stdPertVec_apply_of_notMem hj, norm_zero]; exact norm_nonneg v

lemma stdPertVec_centred {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {i₀ : Fin N} (hi₀ : i₀ ∈ k) (v : E) :
    ∑ j ∈ k, m j • (stdPertVec m k i₀ v j) = 0 := by
  classical
  have hmk : clusterMass m k ≠ 0 := (clusterMass_pos hm ⟨i₀, hi₀⟩).ne'
  have hsplit : ∑ j ∈ k, m j • (stdPertVec m k i₀ v j)
      = (∑ j ∈ k, m j * ((if j = i₀ then 1 else 0) - m i₀ / clusterMass m k : ℝ)) • v := by
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [stdPertVec_apply_of_mem hj, smul_smul]
  rw [hsplit]
  have hcoef : (∑ j ∈ k, m j * ((if j = i₀ then 1 else 0) - m i₀ / clusterMass m k : ℝ)) = 0 := by
    have h1 : ∀ j ∈ k, m j * ((if j = i₀ then (1:ℝ) else 0) - m i₀ / clusterMass m k)
        = (if j = i₀ then m j else 0) - m j * (m i₀ / clusterMass m k) := by
      intro j hj
      by_cases h : j = i₀
      · rw [if_pos h, if_pos h]; ring
      · rw [if_neg h, if_neg h, zero_sub]; ring
    rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, Finset.sum_ite_eq' k i₀ (fun j => m j),
      if_pos hi₀, ← Finset.sum_mul]
    rw [clusterMass] at hmk ⊢
    field_simp
    ring
  rw [hcoef, zero_smul]





/-- **Outward displacement.**  For a collision-free configuration `sbar` of a cluster `k` with at
least two bodies there is a body `i₀ ∈ k` and a nonzero direction `δ` such that the vectors
`sbar i₀ - sbar j` (`j ∈ k`, `j ≠ i₀`) all have strictly positive inner product with `δ`: displacing
`i₀` in the direction `δ` moves it strictly away from every other body of the cluster. -/
theorem exists_outward_displacement {sbar : EN E N} (hk2 : 2 ≤ k.card)
    (hs : ∀ i ∈ k, ∀ j ∈ k, i ≠ j → sbar i ≠ sbar j) :
    ∃ i₀ ∈ k, ∃ δ : E, δ ≠ 0 ∧ ∀ j ∈ k, j ≠ i₀ → 0 < inner ℝ (sbar i₀ - sbar j) δ := by
  classical
  haveI : Nonempty {j // j ∈ k} := by
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < k.card)
    exact ⟨⟨i, hi⟩⟩
  have hinj : Function.Injective (fun j : {j // j ∈ k} => sbar j.val) := by
    intro a b hab
    refine Subtype.ext ?_
    by_contra hne
    exact hs a.val a.property b.val b.property hne hab
  obtain ⟨i₀, δ, hδ, hpos⟩ := Commons.Analysis.InnerProduct.exists_inner_pos_extreme
    (p := fun j : {j // j ∈ k} => sbar j.val) hinj (by
      rw [Fintype.card_coe]; exact hk2)
  exact ⟨i₀.val, i₀.property, δ, hδ, fun j hj hjne =>
    hpos ⟨j, hj⟩ fun h => hjne (congrArg Subtype.val h)⟩

end Submission.NBody
