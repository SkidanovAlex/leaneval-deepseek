import Mathlib
import Submission.Work.Whitney.exists_sheet_model
import Submission.Work.Whitney.localPushNTrans_sheet

/-! Own copies of the scaled sheet-model chain, insulated from the (currently broken) colleague
file `Work.Whitney.local_push_manifold`.  The originals are `lct_sheet_model_scaled.lean`,
`lct_scaled_setup.lean`, `lct_model_cont.lean`; every name here sits inside the namespace
`Work.Whitney.L42`, so nothing clashes with the originals. -/

set_option maxHeartbeats 4000000
open scoped Manifold ContDiff Topology
open Topology Metric Set

namespace Work.Whitney

/-- **Containment of a small clean ball** (copy of `Work.Whitney.exists_radius_containment`, whose
original is inside the currently broken file `local_push_manifold.lean`). -/
theorem exists_radius_containment42 {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] (f : M → EuclideanSpace ℝ (Fin (2 * n))) (hf : Continuous f)
    (q : EuclideanSpace ℝ (Fin (2 * n))) (p₁ p₂ : M)
    (hsep : ∀ y : M, f y = q → y = p₁ ∨ y = p₂)
    (U₁ U₂ : Set M) (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hp₁ : p₁ ∈ U₁) (hp₂ : p₂ ∈ U₂) :
    ∃ ε : ℝ, 0 < ε ∧ f ⁻¹' (Metric.ball q ε) ⊆ U₁ ∪ U₂ := by
  by_cases hne : ((U₁ ∪ U₂)ᶜ : Set M).Nonempty
  · have hK : IsCompact ((U₁ ∪ U₂)ᶜ : Set M) := (hU₁.union hU₂).isClosed_compl.isCompact
    have hne' : ∀ y ∈ ((U₁ ∪ U₂)ᶜ : Set M), f y ≠ q := by
      intro y hy h
      rcases hsep y h with rfl | rfl
      · exact hy (Or.inl hp₁)
      · exact hy (Or.inr hp₂)
    have hcont : Continuous fun y : M => dist (f y) q := by fun_prop
    obtain ⟨y₀, hy₀, hmin⟩ := hK.exists_isMinOn hne hcont.continuousOn
    refine ⟨dist (f y₀) q, dist_pos.mpr (hne' y₀ hy₀), fun y hy => ?_⟩
    rw [Set.mem_preimage, Metric.mem_ball] at hy
    by_contra hnot
    have hle : dist (f y₀) q ≤ dist (f y) q := hmin hnot
    linarith
  · exact ⟨1, one_pos, fun y hy => by
      by_contra h
      exact hne ⟨y, h⟩⟩

end Work.Whitney

namespace Work.Whitney.L42


/-!
# The local sheet model at a transverse double point, with a small chart

`Work.Whitney.exists_sheet_model` produces, at a transverse double point `f p₁ = f p₂` of a smooth
map `f : M → ℝ^{2n}` of a compact smooth `n`-manifold, two branches `σ₁ ∋ p₁`, `σ₂ ∋ p₂` and a
linear identification `Φ : ℝ^{2n} ≃L ℝⁿ × ℝⁿ` in which the two branches are graphs over the first
factor, with the quantitative bounds

`‖h₁ u - h₂ u - A u‖ ≤ K ‖u‖²`, `‖h₂ u‖ ≤ K ‖u‖²`, `‖h₁ u‖ ≤ K ‖u‖`, `α ‖u‖ ≤ ‖A u‖`.

This file adds the freedom of *scaling the whole chart*: replacing `Φ` by `μ • Φ` and pulling the
two parametrisations back by `u ↦ μ⁻¹ • u` turns `(h₁, h₂, A, α, K, R₀)` into
`(μ h₁(·/μ), μ h₂(·/μ), A, α, K/μ, μ R₀)`, so that the operator norm of the chart becomes
`μ ‖Φ‖`.  Choosing `μ > 0` small (and `≤ 1`) therefore makes the product `c ‖A‖` — with
`c = μ (‖Φ‖ + 1)` — smaller than any prescribed `b > 0`, while keeping all the bounds.  This is the
form of the sheet model needed by the local Whitney move.
-/

open scoped Manifold ContDiff Topology
open Topology Metric


/-- **The local sheet model at a transverse double point, with a small chart.**  Given the sheet
model of `Work.Whitney.exists_sheet_model` and a prescribed `b > 0`, the chart can be scaled so
that its operator norm `c` satisfies `c ‖A‖ < b`. -/
theorem lct_sheet_model_scaled {n : ℕ} (hn : 1 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (p₁ p₂ : M) (hp : p₁ ≠ p₂) (hfp : f p₁ = f p₂)
    (htr : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₁).range ⊔
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₂).range = ⊤)
    (b : ℝ) (hb : 0 < b) :
    ∃ (Φ : EuclideanSpace ℝ (Fin (2 * n)) ≃L[ℝ]
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
      (σ₁ σ₂ : EuclideanSpace ℝ (Fin n) → M)
      (h₁ h₂ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (α K R₀ c : ℝ),
      0 < α ∧ 0 < K ∧ 0 < R₀ ∧ 0 < c ∧ (∀ u, α * ‖u‖ ≤ ‖A u‖) ∧
      c * ‖A‖ < b ∧ (∀ z, ‖Φ z‖ ≤ c * ‖z‖) ∧
      σ₁ 0 = p₁ ∧ σ₂ 0 = p₂ ∧
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        ((⊤ : ℕ∞) : WithTop ℕ∞) σ₁ ∧
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        ((⊤ : ℕ∞) : WithTop ℕ∞) σ₂ ∧
      (∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ ≤ R₀ → Φ (f (σ₁ w) - f p₁) = (w, h₁ w)) ∧
      (∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ R₀ → Φ (f (σ₂ u) - f p₁) = (u, h₂ u)) ∧
      (∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ R₀ → ‖h₁ u - h₂ u - A u‖ ≤ K * ‖u‖ ^ 2) ∧
      (∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ R₀ → ‖h₂ u‖ ≤ K * ‖u‖ ^ 2) ∧
      (∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ R₀ → ‖h₁ u‖ ≤ K * ‖u‖) := by
  classical
  obtain ⟨Φ, σ₁, σ₂, h₁, h₂, A, α, K, R₀, hα, hK, hR₀, hAα, hσ₁0, hσ₂0,
    hσ₁sm, hσ₂sm, _, _, _, _, hgr₁, hgr₂, hΞ, hh₂, hh₁⟩ :=
    Work.Whitney.exists_sheet_model hn f hf p₁ p₂ hp hfp htr
  -- the underlying continuous linear map of `Φ`, and the quantity controlling the scale
  set Fc : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ]
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    (Φ : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ]
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) with hFc
  set nrm : ℝ := (‖Fc‖ + 1) * (‖A‖ + 1) with hnrm
  have hnrmpos : 0 < nrm := by rw [hnrm]; positivity
  -- the scale `μ`
  set μ : ℝ := min 1 (b / (2 * nrm)) with hμ
  have hμpos : 0 < μ := by
    rw [hμ]; exact lt_min one_pos (div_pos hb (by positivity))
  have hμle1 : μ ≤ 1 := by rw [hμ]; exact min_le_left _ _
  have hμne : μ ≠ 0 := hμpos.ne'
  have hμnrm : μ * nrm < b := by
    have hle : μ * nrm ≤ (b / (2 * nrm)) * nrm :=
      mul_le_mul_of_nonneg_right (by rw [hμ]; exact min_le_right _ _) hnrmpos.le
    have heq : (b / (2 * nrm)) * nrm = b / 2 := by field_simp
    rw [heq] at hle
    linarith
  have hμinv : ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ μ * R₀ → ‖μ⁻¹ • u‖ ≤ R₀ := by
    intro u hu
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hμpos)]
    have h := mul_le_mul_of_nonneg_left hu (inv_pos.mpr hμpos).le
    rwa [← mul_assoc, inv_mul_cancel₀ hμne, one_mul] at h
  -- the scaled linear identification `Φ' = μ • Φ`
  let eμ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (LinearEquiv.smulOfNeZero ℝ (EuclideanSpace ℝ (Fin n)) μ hμne).toContinuousLinearEquiv
  have heμ : ∀ x : EuclideanSpace ℝ (Fin n), eμ x = μ • x := by intro x; rfl
  let Φ' : EuclideanSpace ℝ (Fin (2 * n)) ≃L[ℝ]
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) := Φ.trans (eμ.prodCongr eμ)
  have hΦ' : ∀ z : EuclideanSpace ℝ (Fin (2 * n)), Φ' z = μ • Φ z := by
    intro z
    simp only [Φ', ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.prodCongr_apply, heμ]
    exact (Prod.smul_mk μ (Φ z).1 (Φ z).2).symm
  have hsc : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : EuclideanSpace ℝ (Fin n) => μ⁻¹ • w) := by
    rw [contMDiff_iff_contDiff]
    exact (contDiff_id (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n))).const_smul (μ⁻¹)
  refine ⟨Φ', (fun w => σ₁ (μ⁻¹ • w)), (fun u => σ₂ (μ⁻¹ • u)),
    (fun w => μ • h₁ (μ⁻¹ • w)), (fun u => μ • h₂ (μ⁻¹ • u)), A, α, K / μ, μ * R₀,
    μ * (‖Fc‖ + 1), ?_⟩
  refine ⟨hα, div_pos hK hμpos, mul_pos hμpos hR₀, mul_pos hμpos (by positivity), hAα,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the product `c ‖A‖` is below the prescribed `b`
    show (μ * (‖Fc‖ + 1)) * ‖A‖ < b
    have hle : (‖Fc‖ + 1) * ‖A‖ ≤ nrm := by
      rw [hnrm]
      exact mul_le_mul_of_nonneg_left (by linarith [norm_nonneg A]) (by positivity)
    calc (μ * (‖Fc‖ + 1)) * ‖A‖ = μ * ((‖Fc‖ + 1) * ‖A‖) := by ring
      _ ≤ μ * nrm := mul_le_mul_of_nonneg_left hle hμpos.le
      _ < b := hμnrm
  · -- the operator norm of the scaled chart
    intro z
    rw [hΦ']
    calc ‖μ • Φ z‖ = μ * ‖Φ z‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hμpos]
      _ ≤ μ * (‖Fc‖ * ‖z‖) := by
          apply mul_le_mul_of_nonneg_left _ hμpos.le
          have h := Fc.le_opNorm z
          rw [hFc] at h
          simpa only [ContinuousLinearEquiv.coe_coe] using h
      _ = (μ * ‖Fc‖) * ‖z‖ := by ring
      _ ≤ (μ * (‖Fc‖ + 1)) * ‖z‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg z)
          apply mul_le_mul_of_nonneg_left _ hμpos.le
          linarith [norm_nonneg Fc]
  · show (fun w => σ₁ (μ⁻¹ • w)) 0 = p₁
    simpa using hσ₁0
  · show (fun u => σ₂ (μ⁻¹ • u)) 0 = p₂
    simpa using hσ₂0
  · exact hσ₁sm.comp hsc
  · exact hσ₂sm.comp hsc
  · intro w hw
    have hw' := hμinv w hw
    show Φ' (f (σ₁ (μ⁻¹ • w)) - f p₁) = (w, μ • h₁ (μ⁻¹ • w))
    rw [hΦ', hgr₁ (μ⁻¹ • w) hw', Prod.smul_mk, smul_smul, mul_inv_cancel₀ hμne, one_smul]
  · intro u hu
    have hu' := hμinv u hu
    show Φ' (f (σ₂ (μ⁻¹ • u)) - f p₁) = (u, μ • h₂ (μ⁻¹ • u))
    rw [hΦ', hgr₂ (μ⁻¹ • u) hu', Prod.smul_mk, smul_smul, mul_inv_cancel₀ hμne, one_smul]
  · -- the two height functions still differ by `A` to second order
    intro u hu
    have hu' := hμinv u hu
    show ‖μ • h₁ (μ⁻¹ • u) - μ • h₂ (μ⁻¹ • u) - A u‖ ≤ (K / μ) * ‖u‖ ^ 2
    have hkey : μ • h₁ (μ⁻¹ • u) - μ • h₂ (μ⁻¹ • u) - A u
        = μ • (h₁ (μ⁻¹ • u) - h₂ (μ⁻¹ • u) - A (μ⁻¹ • u)) := by
      have hAu : A u = μ • A (μ⁻¹ • u) := by
        conv_lhs => rw [show u = μ • (μ⁻¹ • u) by
          rw [smul_smul, mul_inv_cancel₀ hμne, one_smul]]
        rw [A.map_smul]
      rw [hAu, ← smul_sub, ← smul_sub]
    rw [hkey, norm_smul, Real.norm_eq_abs, abs_of_pos hμpos]
    calc μ * ‖h₁ (μ⁻¹ • u) - h₂ (μ⁻¹ • u) - A (μ⁻¹ • u)‖
        ≤ μ * (K * ‖μ⁻¹ • u‖ ^ 2) := mul_le_mul_of_nonneg_left (hΞ (μ⁻¹ • u) hu') hμpos.le
      _ = (K / μ) * ‖u‖ ^ 2 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hμpos)]
          field_simp
  · -- the second height function still vanishes to second order
    intro u hu
    have hu' := hμinv u hu
    show ‖μ • h₂ (μ⁻¹ • u)‖ ≤ (K / μ) * ‖u‖ ^ 2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hμpos]
    calc μ * ‖h₂ (μ⁻¹ • u)‖ ≤ μ * (K * ‖μ⁻¹ • u‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hh₂ (μ⁻¹ • u) hu') hμpos.le
      _ = (K / μ) * ‖u‖ ^ 2 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hμpos)]
          field_simp
  · -- the first height function is still bounded by a linear term
    intro u hu
    have hu' := hμinv u hu
    show ‖μ • h₁ (μ⁻¹ • u)‖ ≤ (K / μ) * ‖u‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hμpos]
    have h2 : μ * (K * ‖μ⁻¹ • u‖) = K * ‖u‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hμpos)]
      field_simp
    have h3 : K * ‖u‖ ≤ (K / μ) * ‖u‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg u)
      rw [le_div_iff₀ hμpos]
      exact mul_le_of_le_one_right hK.le hμle1
    calc μ * ‖h₁ (μ⁻¹ • u)‖ ≤ μ * (K * ‖μ⁻¹ • u‖) :=
          mul_le_mul_of_nonneg_left (hh₁ (μ⁻¹ • u) hu') hμpos.le
      _ = K * ‖u‖ := h2
      _ ≤ (K / μ) * ‖u‖ := h3



/-!
# The scaled sheet model with the injectivity/openness conjuncts and an inverse bound

`Work.Whitney.lct_sheet_model_scaled` scales the chart of `Work.Whitney.exists_sheet_model` by `μ`
so that the product `‖Φ‖ ‖A‖` becomes small, but discards the `Set.InjOn` and `IsOpen` conjuncts
and says nothing about `Φ.symm`.  This module redoes the same scaling keeping those conjuncts (at
the scaled radius `μ R₀`) and adds the bound `‖Φ.symm z‖ ≤ S ‖z‖`.

The scaling is what makes the transverse cut form work: writing `c = ‖Φ‖` and `S` for the inverse
bound, the two quantities `c` and `S` can be moved to opposite extremes by choosing `μ`, which is
exactly what the geometric parameter choice needs.
-/

set_option maxHeartbeats 4000000

open scoped Manifold ContDiff
open Topology Metric


/-- **Injectivity transfers along the rescaling `w ↦ μ⁻¹ • w`.** -/
theorem injOn_comp_smul_inv {n : ℕ} {μ R : ℝ} (hμ : 0 < μ) {X : Type*}
    {σ : EuclideanSpace ℝ (Fin n) → X}
    (h : Set.InjOn σ (Metric.closedBall 0 R)) :
    Set.InjOn (fun w : EuclideanSpace ℝ (Fin n) => σ (μ⁻¹ • w))
      (Metric.closedBall 0 (μ * R)) := by
  intro w hw w' hw' hww
  have hmem : ∀ v : EuclideanSpace ℝ (Fin n), v ∈ Metric.closedBall 0 (μ * R) →
      μ⁻¹ • v ∈ Metric.closedBall 0 R := by
    intro v hv
    rw [Metric.mem_closedBall] at hv ⊢
    rw [dist_eq_norm, sub_zero] at hv ⊢
    rw [norm_smul]
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hμ)]
    calc μ⁻¹ * ‖v‖ ≤ μ⁻¹ * (μ * R) :=
          mul_le_mul_of_nonneg_left hv (le_of_lt (inv_pos.mpr hμ))
      _ = R := by field_simp
  have h1 : μ⁻¹ • w = μ⁻¹ • w' := h (hmem w hw) (hmem w' hw') hww
  have h2 := congrArg (fun z : EuclideanSpace ℝ (Fin n) => μ • z) h1
  rw [smul_smul, smul_smul, mul_inv_cancel₀ hμ.ne', one_smul, one_smul] at h2
  exact h2

/-- **The ball image transfers along the rescaling `w ↦ μ⁻¹ • w`.** -/
theorem image_ball_comp_smul_inv {n : ℕ} {μ R : ℝ} (hμ : 0 < μ) {X : Type*}
    {σ : EuclideanSpace ℝ (Fin n) → X} :
    (fun w : EuclideanSpace ℝ (Fin n) => σ (μ⁻¹ • w)) '' Metric.ball 0 (μ * R)
      = σ '' Metric.ball 0 R := by
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw' : ‖w‖ < μ * R := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hw
      exact hw
    refine ⟨μ⁻¹ • w, ?_, rfl⟩
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hμ)]
    calc μ⁻¹ * ‖w‖ < μ⁻¹ * (μ * R) := mul_lt_mul_of_pos_left hw' (inv_pos.mpr hμ)
      _ = R := by field_simp
  · rintro ⟨u, hu, rfl⟩
    have hu' : ‖u‖ < R := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hu
      exact hu
    refine ⟨μ • u, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, sub_zero]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hμ]
      exact mul_lt_mul_of_pos_left hu' hμ
    · show σ (μ⁻¹ • (μ • u)) = σ u
      rw [smul_smul, inv_mul_cancel₀ hμ.ne', one_smul]

/-- The linear rescaling `x ↦ μ • x` as a continuous linear equivalence, given a name so that
`set`-folding works when it appears inside larger statements. -/
noncomputable def smulCE (n : ℕ) (μ : ℝ) (hμ : μ ≠ 0) :
    EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (LinearEquiv.smulOfNeZero ℝ (EuclideanSpace ℝ (Fin n)) μ hμ).toContinuousLinearEquiv

theorem smulCE_apply {n : ℕ} {μ : ℝ} (hμ : μ ≠ 0) (x : EuclideanSpace ℝ (Fin n)) :
    smulCE n μ hμ x = μ • x := rfl

/-- **The inverse of a rescaled chart scales the norm by `μ⁻¹`.** -/
theorem norm_symm_trans_prod_smul {n : ℕ}
    (Φ : EuclideanSpace ℝ (Fin (2 * n)) ≃L[ℝ]
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    {μ : ℝ} (hμ : 0 < μ) :
    ∀ z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      ‖(Φ.trans ((smulCE n μ hμ.ne').prodCongr (smulCE n μ hμ.ne'))).symm z‖
        ≤ (μ⁻¹ * (‖(Φ.symm : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
            EuclideanSpace ℝ (Fin (2 * n)))‖ + 1)) * ‖z‖ := by
  intro z
  set e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) := smulCE n μ hμ.ne'
    with he
  have he_apply : ∀ x : EuclideanSpace ℝ (Fin n), e x = μ • x := fun x => smulCE_apply _ x
  have he_prod : ∀ ξ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      (e.prodCongr e) ξ = μ • ξ := by
    rintro ⟨a, b⟩
    show (e a, e b) = μ • (a, b)
    rw [he_apply, he_apply, Prod.smul_mk]
  have he_prod_symm : ∀ ξ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      (e.prodCongr e).symm ξ = μ⁻¹ • ξ := by
    intro ξ
    have h : (e.prodCongr e) (μ⁻¹ • ξ) = ξ := by
      rw [he_prod, smul_smul, mul_inv_cancel₀ hμ.ne', one_smul]
    calc (e.prodCongr e).symm ξ = (e.prodCongr e).symm ((e.prodCongr e) (μ⁻¹ • ξ)) := by rw [h]
      _ = μ⁻¹ • ξ := ContinuousLinearEquiv.symm_apply_apply _ _
  have h2 : ∀ ξ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      ‖(e.prodCongr e).symm ξ‖ = μ⁻¹ * ‖ξ‖ := by
    intro ξ
    rw [he_prod_symm ξ, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hμ)]
  have hsymm : (Φ.trans (e.prodCongr e)).symm z = Φ.symm ((e.prodCongr e).symm z) := by
    apply (Φ.trans (e.prodCongr e)).injective
    rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
  have hA : ‖(Φ.symm : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
        EuclideanSpace ℝ (Fin (2 * n)))‖
      ≤ ‖(Φ.symm : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
        EuclideanSpace ℝ (Fin (2 * n)))‖ + 1 := by linarith
  calc ‖(Φ.trans (e.prodCongr e)).symm z‖
      = ‖Φ.symm ((e.prodCongr e).symm z)‖ := by rw [hsymm]
    _ ≤ ‖(Φ.symm : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
          EuclideanSpace ℝ (Fin (2 * n)))‖ * ‖(e.prodCongr e).symm z‖ := by
        have := (Φ.symm : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
          EuclideanSpace ℝ (Fin (2 * n))).le_opNorm ((e.prodCongr e).symm z)
        simpa only [ContinuousLinearEquiv.coe_coe] using this
    _ = ‖(Φ.symm : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
          EuclideanSpace ℝ (Fin (2 * n)))‖ * (μ⁻¹ * ‖z‖) := by rw [h2 z]
    _ ≤ (μ⁻¹ * (‖(Φ.symm : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
          EuclideanSpace ℝ (Fin (2 * n)))‖ + 1)) * ‖z‖ := by
        calc ‖(Φ.symm : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
              EuclideanSpace ℝ (Fin (2 * n)))‖ * (μ⁻¹ * ‖z‖)
            = (‖(Φ.symm : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
              EuclideanSpace ℝ (Fin (2 * n)))‖ * μ⁻¹) * ‖z‖ := by ring
          _ ≤ ((‖(Φ.symm : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
              EuclideanSpace ℝ (Fin (2 * n)))‖ + 1) * μ⁻¹) * ‖z‖ := by
              apply mul_le_mul_of_nonneg_right _ (norm_nonneg z)
              exact mul_le_mul_of_nonneg_right hA (le_of_lt (inv_pos.mpr hμ))
          _ = (μ⁻¹ * (‖(Φ.symm : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
              EuclideanSpace ℝ (Fin (2 * n)))‖ + 1)) * ‖z‖ := by ring

/-- **The scaled local sheet model, with injectivity, openness and an inverse-norm bound.** -/
theorem sheet_model_scaled_full {n : ℕ} (hn : 1 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (p₁ p₂ : M) (hp : p₁ ≠ p₂) (hfp : f p₁ = f p₂)
    (htr : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₁).range ⊔
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₂).range = ⊤)
    (b : ℝ) (hb : 0 < b) :
    ∃ (Φ : EuclideanSpace ℝ (Fin (2 * n)) ≃L[ℝ]
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
      (σ₁ σ₂ : EuclideanSpace ℝ (Fin n) → M)
      (h₁ h₂ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (α K R₀ c S : ℝ),
      0 < α ∧ 0 < K ∧ 0 < R₀ ∧ 0 < c ∧ 0 < S ∧
      (∀ u, α * ‖u‖ ≤ ‖A u‖) ∧ c * ‖A‖ < b ∧
      (∀ z, ‖Φ z‖ ≤ c * ‖z‖) ∧ (∀ z, ‖Φ.symm z‖ ≤ S * ‖z‖) ∧
      σ₁ 0 = p₁ ∧ σ₂ 0 = p₂ ∧
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        ((⊤ : ℕ∞) : WithTop ℕ∞) σ₁ ∧
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        ((⊤ : ℕ∞) : WithTop ℕ∞) σ₂ ∧
      Set.InjOn σ₁ (Metric.closedBall 0 R₀) ∧ Set.InjOn σ₂ (Metric.closedBall 0 R₀) ∧
      IsOpen (σ₁ '' Metric.ball 0 R₀) ∧ IsOpen (σ₂ '' Metric.ball 0 R₀) ∧
      (∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ ≤ R₀ → Φ (f (σ₁ w) - f p₁) = (w, h₁ w)) ∧
      (∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ R₀ → Φ (f (σ₂ u) - f p₁) = (u, h₂ u)) ∧
      (∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ R₀ → ‖h₁ u - h₂ u - A u‖ ≤ K * ‖u‖ ^ 2) ∧
      (∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ R₀ → ‖h₂ u‖ ≤ K * ‖u‖ ^ 2) ∧
      (∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ R₀ → ‖h₁ u‖ ≤ K * ‖u‖) ∧
      c * (2 * (‖A‖ + 1)) ≤ b ∧ 1 ≤ S := by
  classical
  obtain ⟨Φ, σ₁, σ₂, h₁, h₂, A, α, K, R₀, hα, hK, hR₀, hAα, hσ₁0, hσ₂0,
    hσ₁sm, hσ₂sm, hinj₁, hinj₂, hopen₁, hopen₂, hgr₁, hgr₂, hΞ, hh₂, hh₁⟩ :=
    Work.Whitney.exists_sheet_model hn f hf p₁ p₂ hp hfp htr
  set Fc : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ]
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    (Φ : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ]
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) with hFc
  set Fcs : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
      EuclideanSpace ℝ (Fin (2 * n)) :=
    (Φ.symm : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
      EuclideanSpace ℝ (Fin (2 * n))) with hFcs
  set nrm : ℝ := (‖Fc‖ + 1) * (‖A‖ + 1) with hnrm
  have hnrmpos : 0 < nrm := by rw [hnrm]; positivity
  set μ : ℝ := min 1 (b / (2 * nrm)) with hμ
  have hμpos : 0 < μ := by
    rw [hμ]; exact lt_min one_pos (div_pos hb (by positivity))
  have hμle1 : μ ≤ 1 := by rw [hμ]; exact min_le_left _ _
  have hμne : μ ≠ 0 := hμpos.ne'
  have hμnrm : μ * nrm < b := by
    have hle : μ * nrm ≤ (b / (2 * nrm)) * nrm :=
      mul_le_mul_of_nonneg_right (by rw [hμ]; exact min_le_right _ _) hnrmpos.le
    have heq : (b / (2 * nrm)) * nrm = b / 2 := by field_simp
    rw [heq] at hle
    linarith
  have hμinv : ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ μ * R₀ → ‖μ⁻¹ • u‖ ≤ R₀ := by
    intro u hu
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hμpos)]
    have h := mul_le_mul_of_nonneg_left hu (inv_pos.mpr hμpos).le
    rwa [← mul_assoc, inv_mul_cancel₀ hμne, one_mul] at h
  let Φ' : EuclideanSpace ℝ (Fin (2 * n)) ≃L[ℝ]
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    Φ.trans ((smulCE n μ hμne).prodCongr (smulCE n μ hμne))
  have hΦ' : ∀ z : EuclideanSpace ℝ (Fin (2 * n)), Φ' z = μ • Φ z := by
    intro z
    simp only [Φ', ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.prodCongr_apply,
      smulCE_apply]
    exact (Prod.smul_mk μ (Φ z).1 (Φ z).2).symm
  have hsc : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : EuclideanSpace ℝ (Fin n) => μ⁻¹ • w) := by
    rw [contMDiff_iff_contDiff]
    exact (contDiff_id (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n))).const_smul (μ⁻¹)
  refine ⟨Φ', (fun w => σ₁ (μ⁻¹ • w)), (fun u => σ₂ (μ⁻¹ • u)),
    (fun w => μ • h₁ (μ⁻¹ • w)), (fun u => μ • h₂ (μ⁻¹ • u)), A, α, K / μ, μ * R₀,
    μ * (‖Fc‖ + 1), μ⁻¹ * (‖Fcs‖ + 1), ?_⟩
  refine ⟨hα, div_pos hK hμpos, mul_pos hμpos hR₀, mul_pos hμpos (by positivity),
    mul_pos (inv_pos.mpr hμpos) (by positivity), hAα, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the product `c ‖A‖` is below the prescribed `b`
    show (μ * (‖Fc‖ + 1)) * ‖A‖ < b
    have hle : (‖Fc‖ + 1) * ‖A‖ ≤ nrm := by
      rw [hnrm]
      exact mul_le_mul_of_nonneg_left (by linarith [norm_nonneg A]) (by positivity)
    calc (μ * (‖Fc‖ + 1)) * ‖A‖ = μ * ((‖Fc‖ + 1) * ‖A‖) := by ring
      _ ≤ μ * nrm := mul_le_mul_of_nonneg_left hle hμpos.le
      _ < b := hμnrm
  · -- the operator norm of the scaled chart
    intro z
    rw [hΦ']
    calc ‖μ • Φ z‖ = μ * ‖Φ z‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hμpos]
      _ ≤ μ * (‖Fc‖ * ‖z‖) := by
          apply mul_le_mul_of_nonneg_left _ hμpos.le
          have h := Fc.le_opNorm z
          rw [hFc] at h
          simpa only [ContinuousLinearEquiv.coe_coe] using h
      _ = (μ * ‖Fc‖) * ‖z‖ := by ring
      _ ≤ (μ * (‖Fc‖ + 1)) * ‖z‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg z)
          apply mul_le_mul_of_nonneg_left _ hμpos.le
          linarith [norm_nonneg Fc]
  · -- the inverse bound: this is the banked transfer lemma
    intro z
    have := norm_symm_trans_prod_smul Φ hμpos z
    simpa only [hFcs, Φ'] using this
  · show (fun w => σ₁ (μ⁻¹ • w)) 0 = p₁
    simpa using hσ₁0
  · show (fun u => σ₂ (μ⁻¹ • u)) 0 = p₂
    simpa using hσ₂0
  · exact hσ₁sm.comp hsc
  · exact hσ₂sm.comp hsc
  · exact injOn_comp_smul_inv hμpos hinj₁
  · exact injOn_comp_smul_inv hμpos hinj₂
  · rw [image_ball_comp_smul_inv (μ := μ) (R := R₀) hμpos (σ := σ₁)]; exact hopen₁
  · rw [image_ball_comp_smul_inv (μ := μ) (R := R₀) hμpos (σ := σ₂)]; exact hopen₂
  · intro w hw
    have hw' := hμinv w hw
    show Φ' (f (σ₁ (μ⁻¹ • w)) - f p₁) = (w, μ • h₁ (μ⁻¹ • w))
    rw [hΦ', hgr₁ (μ⁻¹ • w) hw', Prod.smul_mk, smul_smul, mul_inv_cancel₀ hμne, one_smul]
  · intro u hu
    have hu' := hμinv u hu
    show Φ' (f (σ₂ (μ⁻¹ • u)) - f p₁) = (u, μ • h₂ (μ⁻¹ • u))
    rw [hΦ', hgr₂ (μ⁻¹ • u) hu', Prod.smul_mk, smul_smul, mul_inv_cancel₀ hμne, one_smul]
  · -- the two height functions still differ by `A` to second order
    intro u hu
    have hu' := hμinv u hu
    show ‖μ • h₁ (μ⁻¹ • u) - μ • h₂ (μ⁻¹ • u) - A u‖ ≤ (K / μ) * ‖u‖ ^ 2
    have hkey : μ • h₁ (μ⁻¹ • u) - μ • h₂ (μ⁻¹ • u) - A u
        = μ • (h₁ (μ⁻¹ • u) - h₂ (μ⁻¹ • u) - A (μ⁻¹ • u)) := by
      have hAu : A u = μ • A (μ⁻¹ • u) := by
        conv_lhs => rw [show u = μ • (μ⁻¹ • u) by
          rw [smul_smul, mul_inv_cancel₀ hμne, one_smul]]
        rw [A.map_smul]
      rw [hAu, ← smul_sub, ← smul_sub]
    rw [hkey, norm_smul, Real.norm_eq_abs, abs_of_pos hμpos]
    calc μ * ‖h₁ (μ⁻¹ • u) - h₂ (μ⁻¹ • u) - A (μ⁻¹ • u)‖
        ≤ μ * (K * ‖μ⁻¹ • u‖ ^ 2) := mul_le_mul_of_nonneg_left (hΞ (μ⁻¹ • u) hu') hμpos.le
      _ = (K / μ) * ‖u‖ ^ 2 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hμpos)]
          field_simp
  · -- the second height function still vanishes to second order
    intro u hu
    have hu' := hμinv u hu
    show ‖μ • h₂ (μ⁻¹ • u)‖ ≤ (K / μ) * ‖u‖ ^ 2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hμpos]
    calc μ * ‖h₂ (μ⁻¹ • u)‖ ≤ μ * (K * ‖μ⁻¹ • u‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hh₂ (μ⁻¹ • u) hu') hμpos.le
      _ = (K / μ) * ‖u‖ ^ 2 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hμpos)]
          field_simp
  · -- the first height function is still bounded by a linear term
    intro u hu
    have hu' := hμinv u hu
    show ‖μ • h₁ (μ⁻¹ • u)‖ ≤ (K / μ) * ‖u‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hμpos]
    have h2 : μ * (K * ‖μ⁻¹ • u‖) = K * ‖u‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hμpos)]
      field_simp
    have h3 : K * ‖u‖ ≤ (K / μ) * ‖u‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg u)
      rw [le_div_iff₀ hμpos]
      exact mul_le_of_le_one_right hK.le hμle1
    calc μ * ‖h₁ (μ⁻¹ • u)‖ ≤ μ * (K * ‖μ⁻¹ • u‖) :=
          mul_le_mul_of_nonneg_left (hh₁ (μ⁻¹ • u) hu') hμpos.le
      _ = K * ‖u‖ := h2
      _ ≤ (K / μ) * ‖u‖ := h3
  · -- the regime bounds: `c = μ (‖Fc‖+1)` with `μ ≤ b / (2 nrm)` and `nrm = (‖Fc‖+1)(‖A‖+1)`
    have hreg : μ * nrm ≤ b / 2 := by
      have hle : μ ≤ b / (2 * nrm) := by rw [hμ]; exact min_le_right _ _
      have h2 := mul_le_mul_of_nonneg_right hle hnrmpos.le
      have h3 : (b / (2 * nrm)) * nrm = b / 2 := by field_simp
      rw [h3] at h2
      exact h2
    show (μ * (‖Fc‖ + 1)) * (2 * (‖A‖ + 1)) ≤ b
    have hexp : (μ * (‖Fc‖ + 1)) * (2 * (‖A‖ + 1)) = 2 * (μ * nrm) := by
      rw [hnrm]; ring
    rw [hexp]
    linarith
  · -- `S = μ⁻¹ (‖Fcs‖+1) ≥ 1`
    show 1 ≤ μ⁻¹ * (‖Fcs‖ + 1)
    have h1 : 1 ≤ μ⁻¹ := by
      rw [one_le_inv₀ hμpos]
      exact hμle1
    have h2 : (1 : ℝ) ≤ ‖Fcs‖ + 1 := by linarith [norm_nonneg Fcs]
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ μ⁻¹ * (‖Fcs‖ + 1) := mul_le_mul h1 h2 (by norm_num) (by positivity)

/-- **The scaled input package for the transverse cut form.**  This is the scaled version of
`Work.Whitney.lct_input_package`: it returns the *scaled* sheet model (small `c = ‖Φ‖`, large
`S` for the inverse — precisely the regime v7 needs), together with the saturation of `W`, the
frontier-clearance radius `γ₀` and the isolation radius `δloc`. -/
theorem lct_scaled_input_package {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (b : ℝ) (hb : 0 < b)
    (W : Set M) (hWopen : IsOpen W) (hWcpt : IsCompact (closure W))
    (p₁ p₂ : M) (hp₁p₂ : p₁ ≠ p₂) (hfp : f p₁ = f p₂)
    (hpre : ∀ y : M, f y = f p₂ → y = p₁ ∨ y = p₂)
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (hp₁ : p₁ ∈ W) (hp₂ : p₂ ∈ W)
    (htrans : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₁).range ⊔
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₂).range = ⊤) :
    ∃ (Φ : EuclideanSpace ℝ (Fin (2 * n)) ≃L[ℝ]
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
      (σ₁ σ₂ : EuclideanSpace ℝ (Fin n) → M)
      (h₁ h₂ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (α K R₀ c S γ₀ δloc : ℝ),
      0 < α ∧ 0 < K ∧ 0 < R₀ ∧ 0 < c ∧ 0 < S ∧ 0 < γ₀ ∧ 0 < δloc ∧
      (∀ u, α * ‖u‖ ≤ ‖A u‖) ∧ c * ‖A‖ < b ∧
      (∀ z, ‖Φ z‖ ≤ c * ‖z‖) ∧ (∀ z, ‖Φ.symm z‖ ≤ S * ‖z‖) ∧
      σ₁ 0 = p₁ ∧ σ₂ 0 = p₂ ∧
      (∀ y : M, y ∈ W ↔ f y ∈ f '' W) ∧
      (∀ y ∈ frontier W, γ₀ ≤ ‖f y - f p₂‖) ∧
      f ⁻¹' (Metric.ball (f p₂) δloc) ⊆ σ₁ '' Metric.ball 0 R₀ ∪ σ₂ '' Metric.ball 0 R₀ ∧
      Set.InjOn σ₁ (Metric.closedBall 0 R₀) ∧ Set.InjOn σ₂ (Metric.closedBall 0 R₀) ∧
      IsOpen (σ₁ '' Metric.ball 0 R₀) ∧ IsOpen (σ₂ '' Metric.ball 0 R₀) ∧
      (∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ ≤ R₀ → Φ (f (σ₁ w) - f p₁) = (w, h₁ w)) ∧
      (∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ R₀ → Φ (f (σ₂ u) - f p₁) = (u, h₂ u)) ∧
      (∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ R₀ → ‖h₁ u - h₂ u - A u‖ ≤ K * ‖u‖ ^ 2) ∧
      (∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ R₀ → ‖h₂ u‖ ≤ K * ‖u‖ ^ 2) ∧
      (∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ R₀ → ‖h₁ u‖ ≤ K * ‖u‖) ∧
      c * (2 * (‖A‖ + 1)) ≤ b ∧ 1 ≤ S := by
  obtain ⟨Φ, σ₁, σ₂, h₁, h₂, A, α, K, R₀, c, S, hα, hK, hR₀, hc, hS, hAα, hcA, hΦ, hΦs,
    hσ₁0, hσ₂0, hσ₁sm, hσ₂sm, hinj₁, hinj₂, hopen₁, hopen₂, hgr₁, hgr₂, hΞ, hh₂, hh₁,
    hcreg, hSreg⟩ :=
    sheet_model_scaled_full (by omega) f hf p₁ p₂ hp₁p₂ hfp htrans b hb
  have hsat : ∀ y : M, y ∈ W ↔ f y ∈ f '' W := by
    intro y
    constructor
    · intro hy; exact ⟨y, hy, rfl⟩
    · rintro ⟨y', hy', hyy'⟩
      by_contra hyW
      exact hsep y' y hy' hyW hyy'
  have hfrne : ∀ y ∈ frontier W, f y ≠ f p₂ := fun y hy hyq => by
    have hp₁int : p₁ ∈ interior W := by rw [hWopen.interior_eq]; exact hp₁
    have hp₂int : p₂ ∈ interior W := by rw [hWopen.interior_eq]; exact hp₂
    rcases hpre y hyq with h | h
    · exact hy.2 (h ▸ hp₁int)
    · exact hy.2 (h ▸ hp₂int)
  obtain ⟨γ₀, hγ₀pos, hγ₀⟩ : ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ y ∈ frontier W, γ₀ ≤ ‖f y - f p₂‖ := by
    have hfrclosed : IsClosed (frontier W) := isClosed_frontier
    have hfrcpt : IsCompact (frontier W) :=
      hWcpt.of_isClosed_subset hfrclosed frontier_subset_closure
    have hcont : Continuous fun y : M => ‖f y - f p₂‖ :=
      (hf.continuous.sub continuous_const).norm
    by_cases hne : (frontier W).Nonempty
    · obtain ⟨y₀, hy₀, hmin⟩ := hfrcpt.exists_isMinOn hne hcont.continuousOn
      exact ⟨‖f y₀ - f p₂‖,
        norm_pos_iff.mpr (sub_ne_zero.mpr (hfrne y₀ hy₀)), fun y hy => hmin hy⟩
    · exact ⟨1, one_pos, fun y hy => absurd ⟨y, hy⟩ hne⟩
  obtain ⟨δloc, hδpos, hiso⟩ :=
    exists_radius_containment42 f hf.continuous (f p₂) p₁ p₂
      (fun y hy => hpre y hy)
      (σ₁ '' Metric.ball 0 R₀) (σ₂ '' Metric.ball 0 R₀) hopen₁ hopen₂
      ⟨0, Metric.mem_ball.mpr (by simpa using hR₀), hσ₁0⟩
      ⟨0, Metric.mem_ball.mpr (by simpa using hR₀), hσ₂0⟩
  exact ⟨Φ, σ₁, σ₂, h₁, h₂, A, α, K, R₀, c, S, γ₀, δloc, hα, hK, hR₀, hc, hS, hγ₀pos, hδpos,
    hAα, hcA, hΦ, hΦs, hσ₁0, hσ₂0, hsat, hγ₀, hiso, hinj₁, hinj₂, hopen₁, hopen₂,
    hgr₁, hgr₂, hΞ, hh₂, hh₁, hcreg, hSreg⟩



set_option maxHeartbeats 4000000

open scoped Manifold ContDiff
open Set Metric


theorem lct_model_package_cont {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (b : ℝ) (hb : 0 < b)
    (W : Set M) (hWopen : IsOpen W) (hWcpt : IsCompact (closure W))
    (p₁ p₂ : M) (hp₁p₂ : p₁ ≠ p₂) (hfp : f p₁ = f p₂)
    (hpre : ∀ y : M, f y = f p₂ → y = p₁ ∨ y = p₂)
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (hp₁ : p₁ ∈ W) (hp₂ : p₂ ∈ W)
    (htrans : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₁).range ⊔
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₂).range = ⊤) :
    ∃ (Φ : EuclideanSpace ℝ (Fin (2 * n)) ≃L[ℝ]
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
      (σ₁ σ₂ : EuclideanSpace ℝ (Fin n) → M)
      (h₁ h₂ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (α K R₀ c S ε : ℝ),
      0 < α ∧ 0 < K ∧ 0 < R₀ ∧ 0 < c ∧ 0 < S ∧ 0 < ε ∧
      (∀ u, α * ‖u‖ ≤ ‖A u‖) ∧ c * ‖A‖ < b ∧
      (∀ z, ‖Φ z‖ ≤ c * ‖z‖) ∧ (∀ z, ‖Φ.symm z‖ ≤ S * ‖z‖) ∧
      σ₁ 0 = p₁ ∧ σ₂ 0 = p₂ ∧
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        ((⊤ : ℕ∞) : WithTop ℕ∞) σ₁ ∧
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        ((⊤ : ℕ∞) : WithTop ℕ∞) σ₂ ∧
      Continuous σ₁ ∧ Continuous σ₂ ∧
      Set.InjOn σ₁ (Metric.closedBall 0 R₀) ∧ Set.InjOn σ₂ (Metric.closedBall 0 R₀) ∧
      IsOpen (σ₁ '' Metric.ball 0 R₀) ∧ IsOpen (σ₂ '' Metric.ball 0 R₀) ∧
      Disjoint (σ₁ '' Metric.ball 0 R₀) (σ₂ '' Metric.ball 0 R₀) ∧
      (∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ ≤ R₀ → Φ (f (σ₁ w) - f p₁) = (w, h₁ w)) ∧
      (∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ R₀ → Φ (f (σ₂ u) - f p₁) = (u, h₂ u)) ∧
      (∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ R₀ → ‖h₁ u - h₂ u - A u‖ ≤ K * ‖u‖ ^ 2) ∧
      (∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ R₀ → ‖h₂ u‖ ≤ K * ‖u‖ ^ 2) ∧
      (∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ R₀ → ‖h₁ u‖ ≤ K * ‖u‖) ∧
      h₁ 0 = 0 ∧ h₂ 0 = 0 ∧
      f ⁻¹' Metric.ball (f p₁) ε ⊆ σ₁ '' Metric.ball 0 R₀ ∪ σ₂ '' Metric.ball 0 R₀ ∧
      (∀ y : M, ‖f y - f p₁‖ ≤ ε → y ∈ W) := by
  classical
  -- the scaled sheet model (small `c`, so that `c ‖A‖ < b`, and large `S`)
  obtain ⟨Φ, σ₁, σ₂, h₁, h₂, A, α, K, R₀, c, S, hα, hK, hR₀, hc, hS, hAα, hcA, hΦ, hΦs,
    hσ₁0, hσ₂0, hσ₁sm, hσ₂sm, hinj₁, hinj₂, hopen₁, hopen₂, hgr₁, hgr₂, hΞ, hh₂, hh₁,
    _hcreg, _hSreg⟩ :=
    sheet_model_scaled_full (by omega) f hf p₁ p₂ hp₁p₂ hfp htrans b hb
  have hfcont : Continuous f := hf.continuous
  -- shrink the radius so that the two sheet balls become disjoint
  set R : ℝ := min R₀ (α / (2 * (K + 1))) with hRdef
  have hK1 : 0 < K + 1 := by linarith
  have hRpos : 0 < R := by
    rw [hRdef]; exact lt_min hR₀ (div_pos hα (by linarith))
  have hRle : R ≤ R₀ := by rw [hRdef]; exact min_le_left _ _
  have hRsmall : K * R < α := by
    have h1 : R ≤ α / (2 * (K + 1)) := by rw [hRdef]; exact min_le_right _ _
    have h2 : R * (2 * (K + 1)) ≤ α := by
      rw [le_div_iff₀ (by linarith : (0:ℝ) < 2 * (K + 1))] at h1; linarith [h1]
    nlinarith [h2, hK, hα, hRpos]
  -- the two sheet balls
  set U₁ : Set M := σ₁ '' Metric.ball 0 R with hU₁def
  set U₂ : Set M := σ₂ '' Metric.ball 0 R with hU₂def
  have hinj₁' : Set.InjOn σ₁ (Metric.closedBall 0 R) := by
    refine hinj₁.mono (fun y hy => ?_)
    rw [Metric.mem_closedBall, dist_zero_right] at hy ⊢
    exact le_trans hy hRle
  have hinj₂' : Set.InjOn σ₂ (Metric.closedBall 0 R) := by
    refine hinj₂.mono (fun y hy => ?_)
    rw [Metric.mem_closedBall, dist_zero_right] at hy ⊢
    exact le_trans hy hRle
  have hU₁open : IsOpen U₁ :=
    isOpen_sheet_ball f hfcont Φ σ₁ h₁ p₁ R₀ hR₀ (fun u hu => hgr₁ u hu) hinj₁ hopen₁ R hRle
  have hU₂open : IsOpen U₂ :=
    isOpen_sheet_ball f hfcont Φ σ₂ h₂ p₁ R₀ hR₀ (fun u hu => hgr₂ u hu) hinj₂ hopen₂ R hRle
  have hp₁U : p₁ ∈ U₁ := ⟨0, by simpa using hRpos, hσ₁0⟩
  have hp₂U : p₂ ∈ U₂ := ⟨0, by simpa using hRpos, hσ₂0⟩
  -- disjointness of the two sheets, by the gap estimate `α ‖v‖ ≤ K ‖v‖²`
  have hdisj : Disjoint U₁ U₂ := by
    rw [Set.disjoint_left]
    rintro x ⟨v, hv, rfl⟩ ⟨u, hu, hux⟩
    have hvR : ‖v‖ < R := by simpa using (Metric.mem_ball.mp hv)
    have huR : ‖u‖ < R := by simpa using (Metric.mem_ball.mp hu)
    have h1 : Φ (f (σ₁ v) - f p₁) = (v, h₁ v) := hgr₁ v (le_of_lt (lt_of_lt_of_le hvR hRle))
    have h2 : Φ (f (σ₂ u) - f p₁) = (u, h₂ u) := hgr₂ u (le_of_lt (lt_of_lt_of_le huR hRle))
    have hfx : f (σ₁ v) = f (σ₂ u) := by rw [← hux]
    rw [hfx] at h1
    have hpair : (v, h₁ v) = (u, h₂ u) := h1.symm.trans h2
    have hvu : v = u := congrArg Prod.fst hpair
    have hΞ0 : h₁ v - h₂ v = 0 := by
      have hsnd : h₁ v = h₂ u := congrArg Prod.snd hpair
      rw [hvu] at hsnd ⊢
      rw [hsnd, sub_self]
    have hAv : A v = -(h₁ v - h₂ v - A v) := by rw [hΞ0]; abel
    have h1' : ‖A v‖ ≤ K * ‖v‖ ^ 2 := by
      rw [hAv, norm_neg]
      exact hΞ v (le_of_lt (lt_of_lt_of_le hvR hRle))
    have h2' : α * ‖v‖ ≤ K * ‖v‖ ^ 2 := le_trans (hAα v) h1'
    rw [sq] at h2'
    have hv0 : v = 0 := by
      by_contra hne
      have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hne
      have : α ≤ K * ‖v‖ := by
        have h3 : α * ‖v‖ ≤ (K * ‖v‖) * ‖v‖ := by nlinarith [h2', norm_nonneg v]
        exact le_of_mul_le_mul_right h3 hpos
      have hvR' : ‖v‖ ≤ R := le_of_lt hvR
      nlinarith [this, mul_le_mul_of_nonneg_left hvR' hK.le, hRsmall]
    have hux' : σ₁ 0 = σ₂ 0 := by
      have hu0 : u = 0 := by rw [← hvu, hv0]
      rw [hv0] at hux
      rw [hu0] at hux
      exact hux.symm
    exact hp₁p₂ (by rw [← hσ₁0, ← hσ₂0]; exact hux')
  -- the isolation radius
  obtain ⟨εiso, hεisopos, hiso⟩ :=
    exists_radius_containment42 (n := n) f hfcont (f p₁) p₁ p₂
      (fun y hy => hpre y (by rwa [hfp] at hy)) U₁ U₂ hU₁open hU₂open hp₁U hp₂U
  -- the heights at the origin
  have hh₁0 : h₁ 0 = 0 := by
    have h := hgr₁ 0 (by simpa using hR₀.le)
    have h0 : f (σ₁ 0) - f p₁ = 0 := by rw [hσ₁0, sub_self]
    rw [h0, map_zero] at h
    have := congrArg Prod.snd h
    simpa using this.symm
  have hh₂0 : h₂ 0 = 0 := by
    have h := hgr₂ 0 (by simpa using hR₀.le)
    have h0 : f (σ₂ 0) - f p₁ = 0 := by rw [hσ₂0, hfp, sub_self]
    rw [h0, map_zero] at h
    have := congrArg Prod.snd h
    simpa using this.symm
  -- a radius whose closed ball around `f p₁` already lies in `W`
  obtain ⟨εW, hεWpos, hWball⟩ : ∃ εW : ℝ, 0 < εW ∧ ∀ y : M, ‖f y - f p₁‖ ≤ εW → y ∈ W := by
    by_cases hC : (Wᶜ : Set M).Nonempty
    · have hCcpt : IsCompact (Wᶜ : Set M) := hWopen.isClosed_compl.isCompact
      have hcont : ContinuousOn (fun y : M => ‖f y - f p₁‖) (Wᶜ : Set M) :=
        (hfcont.sub continuous_const).norm.continuousOn
      obtain ⟨y₀, hy₀, hmin⟩ := hCcpt.exists_isMinOn hC hcont
      have hne : f y₀ ≠ f p₁ := by
        intro h
        rcases hpre y₀ (h.trans hfp) with h' | h'
        · exact hy₀ (by rw [h']; exact hp₁)
        · exact hy₀ (by rw [h']; exact hp₂)
      have hpos : 0 < ‖f y₀ - f p₁‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
      refine ⟨‖f y₀ - f p₁‖ / 2, by linarith, fun y hy => ?_⟩
      by_contra hyW
      have hle : ‖f y₀ - f p₁‖ ≤ ‖f y - f p₁‖ := hmin hyW
      linarith [hle, hpos]
    · exact ⟨1, one_pos, fun y _ => by by_contra h; exact hC ⟨y, h⟩⟩
  refine ⟨Φ, σ₁, σ₂, h₁, h₂, A, α, K, R, c, S, min εiso εW,
    hα, hK, hRpos, hc, hS, lt_min hεisopos hεWpos,
    hAα, hcA, hΦ, hΦs, hσ₁0, hσ₂0,
    hσ₁sm, hσ₂sm, hσ₁sm.continuous, hσ₂sm.continuous,
    hinj₁', hinj₂', hU₁open, hU₂open, hdisj,
    (fun v hv => hgr₁ v (le_trans hv hRle)),
    (fun u hu => hgr₂ u (le_trans hu hRle)),
    (fun u hu => hΞ u (le_trans hu hRle)),
    (fun u hu => hh₂ u (le_trans hu hRle)),
    (fun u hu => hh₁ u (le_trans hu hRle)),
    hh₁0, hh₂0, ?_, ?_⟩
  · exact fun y hy => hiso (Metric.ball_subset_ball (min_le_left _ _) hy)
  · exact fun y hy => hWball y (le_trans hy (min_le_right _ _))



end Work.Whitney.L42
