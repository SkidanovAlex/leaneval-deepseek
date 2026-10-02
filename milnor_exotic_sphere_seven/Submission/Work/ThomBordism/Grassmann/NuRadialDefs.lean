import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

/-!
# The radial homeomorphism of a fibrewise `ν`-disc

Let `X` be a topological space and `ν : X × ℝ^k → ℝ` a continuous function which is
* non-negative,
* positively homogeneous in the second variable: `ν (x, c • v) = c * ν (x, v)` for `c ≥ 0`,
* and vanishes exactly on the zero section: `ν (x, v) = 0 ↔ v = 0`.

Such a `ν` is a "fibrewise norm" on the trivial bundle `X × ℝ^k`.  This file builds the
two radial maps

* `nuRadial k ν (x, v) = ν (x, v) • (v / ‖v‖)`, the point of the ray through `v` at
  ν-radius `ν (x, v)` (equal to `0` when `v = 0`, since `ν (x, 0) = 0`), and
* `nuRadialInv k ν (x, w) = (ν (x, w / ‖w‖))⁻¹ • w`, the point of the ray through `w`
  with ν-value `‖w‖`,

together with the basic identities showing that they are mutually inverse and that
`‖nuRadial k ν z‖ = ν z`, `ν (x, nuRadialInv k ν (x, w)) = ‖w‖`.  Consequently `nuRadial`
restricts to a homeomorphism from the `ν`-unit disc onto the euclidean unit disc, once
continuity of both maps is known (see `NuRadialCont.lean`).
-/

namespace Work.ThomBordism.Grassmann

open scoped Topology

noncomputable section

/-- The radial map associated with a fibrewise norm `ν`: `(x, v)` is sent to the point of the
ray `ℝ_{≥ 0} · v` at ν-radius `ν (x, v)`, i.e. to `ν (x, v) • (v / ‖v‖)`.  At `v = 0` this is
`0`, because `‖0‖⁻¹ • 0 = 0`. -/
def nuRadial {X : Type*} (k : ℕ) (ν : X × EuclideanSpace ℝ (Fin k) → ℝ) :
    X × EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k) :=
  fun z => ν z • (‖z.2‖⁻¹ • z.2)

/-- The inverse radial map: `(x, w)` is sent to the point of the ray `ℝ_{≥ 0} · w` whose
ν-value is `‖w‖`, i.e. to `(ν (x, w / ‖w‖))⁻¹ • w`. -/
def nuRadialInv {X : Type*} (k : ℕ) (ν : X × EuclideanSpace ℝ (Fin k) → ℝ) :
    X × EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k) :=
  fun z => (ν (z.1, ‖z.2‖⁻¹ • z.2))⁻¹ • z.2

variable {X : Type*} (k : ℕ) (ν : X × EuclideanSpace ℝ (Fin k) → ℝ)

lemma nuRadial_apply_zero (x : X) : nuRadial k ν (x, 0) = 0 := by
  simp [nuRadial]

lemma nuRadialInv_apply_zero (x : X) : nuRadialInv k ν (x, 0) = 0 := by
  simp [nuRadialInv]

lemma nu_apply_zero
    (hhom : ∀ (c : ℝ) (x : X) (v : EuclideanSpace ℝ (Fin k)), 0 ≤ c → ν (x, c • v) = c * ν (x, v))
    (x : X) : ν (x, 0) = 0 := by
  have h := hhom 0 x 0 le_rfl
  simpa using h

/-- The ν-radius of `nuRadial k ν z` is `ν z`. -/
lemma norm_nuRadial (hnonneg : ∀ z, 0 ≤ ν z)
    (hhom : ∀ (c : ℝ) (x : X) (v : EuclideanSpace ℝ (Fin k)), 0 ≤ c → ν (x, c • v) = c * ν (x, v))
    (z : X × EuclideanSpace ℝ (Fin k)) : ‖nuRadial k ν z‖ = ν z := by
  rw [nuRadial, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hnonneg z)]
  by_cases hz : z.2 = 0
  · have h0 : ν z = 0 := by
      rw [show z = (z.1, 0) from Prod.ext rfl hz]
      exact nu_apply_zero k ν hhom z.1
    rw [h0]; simp
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz), mul_one]

/-- `nuRadial` is positively homogeneous in the second variable. -/
lemma nuRadial_smul
    (hhom : ∀ (c : ℝ) (x : X) (v : EuclideanSpace ℝ (Fin k)), 0 ≤ c → ν (x, c • v) = c * ν (x, v))
    (c : ℝ) (hc : 0 ≤ c) (x : X) (v : EuclideanSpace ℝ (Fin k)) :
    nuRadial k ν (x, c • v) = c • nuRadial k ν (x, v) := by
  rw [nuRadial, nuRadial, hhom c x v hc, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  simp only [smul_smul]
  congr 1
  field_simp

/-- The ν-value of `nuRadialInv k ν (x, w)` is `‖w‖`. -/
lemma nu_nuRadialInv
    (hhom : ∀ (c : ℝ) (x : X) (v : EuclideanSpace ℝ (Fin k)), 0 ≤ c → ν (x, c • v) = c * ν (x, v))
    (hnonneg : ∀ z, 0 ≤ ν z)
    (hzero : ∀ (x : X) (v : EuclideanSpace ℝ (Fin k)), ν (x, v) = 0 ↔ v = 0)
    (x : X) (w : EuclideanSpace ℝ (Fin k)) :
    ν (x, nuRadialInv k ν (x, w)) = ‖w‖ := by
  rw [nuRadialInv]
  by_cases hw : w = 0
  · subst hw
    have h0 : ν (x, 0) = 0 := nu_apply_zero k ν hhom x
    simp [h0]
  · set a : ℝ := ν (x, ‖w‖⁻¹ • w) with ha
    have ha0 : a ≠ 0 := by
      rw [ha]
      intro h
      rw [hzero] at h
      rw [smul_eq_zero] at h
      rcases h with h | h
      · exact inv_ne_zero (norm_ne_zero_iff.mpr hw) h
      · exact hw h
    have hsplit : ν (x, w) = ‖w‖ * a := by
      rw [ha]
      have h := hhom ‖w‖ x (‖w‖⁻¹ • w) (norm_nonneg _)
      rwa [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hw), one_smul] at h
    rw [hhom a⁻¹ x w (inv_nonneg.mpr (hnonneg _)), hsplit]
    field_simp

/-- `nuRadialInv` is a left inverse of `nuRadial`. -/
lemma nuRadialInv_nuRadial
    (hhom : ∀ (c : ℝ) (x : X) (v : EuclideanSpace ℝ (Fin k)), 0 ≤ c → ν (x, c • v) = c * ν (x, v))
    (hnonneg : ∀ z, 0 ≤ ν z)
    (hzero : ∀ (x : X) (v : EuclideanSpace ℝ (Fin k)), ν (x, v) = 0 ↔ v = 0)
    (x : X) (v : EuclideanSpace ℝ (Fin k)) :
    nuRadialInv k ν (x, nuRadial k ν (x, v)) = v := by
  rw [nuRadial]
  by_cases hv : v = 0
  · subst hv; simp [nuRadialInv]
  · set W : EuclideanSpace ℝ (Fin k) := ν (x, v) • (‖v‖⁻¹ • v) with hW
    have hWn : ‖W‖ = ν (x, v) := by rw [hW]; exact norm_nuRadial k ν hnonneg hhom (x, v)
    have hνv : ν (x, v) ≠ 0 := fun h => hv ((hzero x v).mp h)
    have hdir : ‖W‖⁻¹ • W = ‖v‖⁻¹ • v := by
      rw [hWn, hW, smul_smul, inv_mul_cancel₀ hνv, one_smul]
    have hν : ν (x, ‖W‖⁻¹ • W) = ‖v‖⁻¹ * ν (x, v) := by
      rw [hdir, hhom (‖v‖⁻¹) x v (inv_nonneg.mpr (norm_nonneg _))]
    rw [nuRadialInv, hν, hW]
    simp only [smul_smul]
    conv_rhs => rw [← one_smul ℝ v]
    rw [smul_left_inj hv]
    field_simp [norm_ne_zero_iff.mpr hv]

/-- `nuRadialInv` is a right inverse of `nuRadial`. -/
lemma nuRadial_nuRadialInv
    (hhom : ∀ (c : ℝ) (x : X) (v : EuclideanSpace ℝ (Fin k)), 0 ≤ c → ν (x, c • v) = c * ν (x, v))
    (hnonneg : ∀ z, 0 ≤ ν z)
    (hzero : ∀ (x : X) (v : EuclideanSpace ℝ (Fin k)), ν (x, v) = 0 ↔ v = 0)
    (x : X) (w : EuclideanSpace ℝ (Fin k)) :
    nuRadial k ν (x, nuRadialInv k ν (x, w)) = w := by
  rw [nuRadialInv]
  by_cases hw : w = 0
  · subst hw; simp [nuRadial]
  · set a : ℝ := ν (x, ‖w‖⁻¹ • w) with ha
    have ha0 : a ≠ 0 := by
      rw [ha]
      intro h
      rw [hzero] at h
      rw [smul_eq_zero] at h
      rcases h with h | h
      · exact inv_ne_zero (norm_ne_zero_iff.mpr hw) h
      · exact hw h
    have hapos : 0 ≤ a := by rw [ha]; exact hnonneg _
    have hsplit : ν (x, w) = ‖w‖ * a := by
      rw [ha]
      have h := hhom ‖w‖ x (‖w‖⁻¹ • w) (norm_nonneg _)
      rwa [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hw), one_smul] at h
    rw [nuRadial]
    have hνv : ν (x, a⁻¹ • w) = ‖w‖ := by
      rw [hhom a⁻¹ x w (inv_nonneg.mpr hapos), hsplit]
      field_simp
    have hdir : ‖a⁻¹ • w‖⁻¹ • (a⁻¹ • w) = ‖w‖⁻¹ • w := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hapos), smul_smul]
      rw [smul_left_inj hw]
      field_simp
    rw [hνv, hdir, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hw), one_smul]

section Top

variable [TopologicalSpace X]

/-- **A uniform positive lower bound for `ν` on the unit sphere, locally in the base point.**
For every `x₀` there is `δ > 0` and a neighbourhood `U` of `x₀` such that `δ ≤ ν (x, v)` for
every `x ∈ U` and every unit vector `v`.  This is the input that makes `nuRadialInv` continuous
at the zero section. -/
lemma exists_nhds_le_nu (hcont : Continuous ν)
    (hnonneg : ∀ z, 0 ≤ ν z)
    (hzero : ∀ (x : X) (v : EuclideanSpace ℝ (Fin k)), ν (x, v) = 0 ↔ v = 0)
    (x₀ : X) :
    ∃ δ > 0, ∃ U ∈ 𝓝 x₀, ∀ x ∈ U, ∀ v : EuclideanSpace ℝ (Fin k), ‖v‖ = 1 → δ ≤ ν (x, v) := by
  by_cases hne : (Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1).Nonempty
  · have hcont' : Continuous fun v : EuclideanSpace ℝ (Fin k) => ν (x₀, v) :=
      hcont.comp (continuous_const.prodMk continuous_id)
    obtain ⟨δ0, hδ0pos, hδ0⟩ :=
      (isCompact_sphere (0 : EuclideanSpace ℝ (Fin k)) 1).exists_forall_le'
        hcont'.continuousOn (a := 0) (fun b hb => by
          have hb0 : b ≠ 0 := by
            intro h; rw [h] at hb
            rw [Metric.mem_sphere, dist_self] at hb; norm_num at hb
          exact lt_of_le_of_ne (hnonneg _) (fun h => hb0 ((hzero x₀ b).mp h.symm)))
    refine ⟨δ0 / 2, by linarith, ?_⟩
    have hWopen : IsOpen {p : X × EuclideanSpace ℝ (Fin k) | δ0 / 2 < ν p} :=
      isOpen_lt continuous_const hcont
    have hsub : ({x₀} : Set X) ×ˢ (Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1)
        ⊆ {p | δ0 / 2 < ν p} := by
      rintro ⟨x, v⟩ ⟨hx, hv⟩
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact lt_of_lt_of_le (by linarith) (hδ0 v hv)
    obtain ⟨u, t, huopen, htopen, hsu, hst, hut⟩ :=
      generalized_tube_lemma isCompact_singleton
        (isCompact_sphere (0 : EuclideanSpace ℝ (Fin k)) 1) hWopen hsub
    refine ⟨u, huopen.mem_nhds (hsu rfl), fun x hx v hv => le_of_lt (hut ⟨hx, ?_⟩)⟩
    exact hst (by rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact hv)
  · refine ⟨1, one_pos, Set.univ, Filter.univ_mem, fun x _ v hv => ?_⟩
    exact absurd ⟨v, by rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact hv⟩ hne

/-- The radial map `nuRadial k ν` is continuous. -/
lemma continuous_nuRadial (hcont : Continuous ν)
    (hnonneg : ∀ z, 0 ≤ ν z)
    (hhom : ∀ (c : ℝ) (x : X) (v : EuclideanSpace ℝ (Fin k)), 0 ≤ c → ν (x, c • v) = c * ν (x, v)) :
    Continuous (nuRadial k ν) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z.2 = 0
  · have hz0 : nuRadial k ν z = 0 := by simp [nuRadial, hz]
    rw [ContinuousAt, hz0, tendsto_zero_iff_norm_tendsto_zero]
    have hν : Filter.Tendsto (fun z : X × EuclideanSpace ℝ (Fin k) => ν z) (𝓝 z) (𝓝 0) := by
      have h : ContinuousAt ν z := hcont.continuousAt (x := z)
      have h0 : ν z = 0 := by
        rw [show z = (z.1, 0) from Prod.ext rfl hz]
        exact nu_apply_zero k ν hhom z.1
      rw [ContinuousAt, h0] at h
      exact h
    refine Filter.Tendsto.congr' (Filter.Eventually.of_forall (fun z' => ?_)) hν
    exact (norm_nuRadial k ν hnonneg hhom z').symm
  · have hsc : ContinuousAt (fun z : X × EuclideanSpace ℝ (Fin k) => ‖z.2‖⁻¹) z :=
      ((continuous_snd.norm).continuousAt (x := z)).inv₀ (norm_ne_zero_iff.mpr hz)
    exact (hcont.continuousAt (x := z)).smul (hsc.smul (continuous_snd.continuousAt (x := z)))

end Top

end

end Work.ThomBordism.Grassmann
