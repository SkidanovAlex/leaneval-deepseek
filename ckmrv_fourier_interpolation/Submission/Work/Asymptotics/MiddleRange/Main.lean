/-
# Local bounds for the CKMRV middle range

This file assembles the local estimates that give `Work.Asymptotics.Kaxis_local_middle`: on the
parameter space `K × [ε,1]` (`K ⊆ 𝒟` compact), the kernel `K(τ,it)` is bounded, uniformly near
each parameter point.

* `Work.Asymptotics.Pspace` : the parameter space `K × [ε,1]`, compact.
* `Work.Asymptotics.Cseg` : the contour `{it : ε ≤ t ≤ 1}` as a compact subset of `ℍ`.
* `Work.Asymptotics.exists_local_bound_clean` : the local bound at a parameter point where
  `j τ ≠ j (it)` — the divisor `Δ(τ)Δ(it)^e (j τ - j(it))` is bounded away from zero there.
* `Work.Asymptotics.exists_local_bound_coincidence` : the local bound at a coincidence
  `j τ = j (it)`, where the pole of `z ↦ K(τ,z)` is removable
  (`Work.Residues.KPlusClear_diag`, `Work.Asymptotics.KClear_S_vanishing`).
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.Theorem31
import Submission.Work.Kernels.ModerateGrowth
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.KClear_mg2
import Submission.Work.Kernels.ClassicalFacts.DeltaFun_basic
import Submission.Work.Kernels.ClearLink.KPlusClear_eq_smul
import Submission.Work.Kernels.ClearLink.KMinusClear_eq_smul
import Submission.Work.Residues.KPlusClear_diag
import Submission.Work.Residues.KMinusClear_diag
import Submission.Work.Asymptotics.KClear_S_vanishing
import Submission.Work.Asymptotics.orbit_imagAxis_of_mem_DomainD
import Submission.Work.Asymptotics.eq_one_or_neg_one_or_S_of_smul_imagAxis
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq
import Submission.Work.Asymptotics.MiddleRange.Basic
import Submission.Work.Asymptotics.MiddleRange.Classify

set_option maxHeartbeats 4000000

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped Topology MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Asymptotics

open Work.Kernels

/-! ## The parameter space `K × [ε,1]` -/

/-- The parameter space of the middle-range estimate. -/
def Pspace (K : Set ℍ) (ε : ℝ) : Set (ℍ × ℝ) := K ×ˢ Set.Icc ε 1

lemma isCompact_Pspace {K : Set ℍ} (hK : IsCompact K) (ε : ℝ) : IsCompact (Pspace K ε) :=
  hK.prod isCompact_Icc

lemma mem_Pspace {K : Set ℍ} {ε : ℝ} {q : ℍ × ℝ} :
    q ∈ Pspace K ε ↔ q.1 ∈ K ∧ ε ≤ q.2 ∧ q.2 ≤ 1 :=
  ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

/-! ## The contour `{it : ε ≤ t ≤ 1}` -/

lemma contourMap_im (ε : ℝ) (hε : 0 < ε) (t : {t : ℝ // t ∈ Set.Icc ε 1}) :
    0 < (((t.1 : ℝ) : ℂ) * Complex.I).im := by
  have ht := Set.mem_Icc.mp t.2
  have h0 : (0:ℝ) < t.1 := lt_of_lt_of_le hε ht.1
  simpa [Complex.mul_im] using h0

/-- The contour `{it : ε ≤ t ≤ 1}` as a subset of `ℍ`. -/
def Cseg (ε : ℝ) (hε : 0 < ε) : Set ℍ :=
  Set.range (fun t : {t : ℝ // t ∈ Set.Icc ε 1} =>
    (⟨((t.1 : ℝ) : ℂ) * Complex.I, contourMap_im ε hε t⟩ : ℍ))

/-- The parametrisation of the contour is continuous. -/
lemma continuous_contourMap {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun t : {t : ℝ // t ∈ Set.Icc ε 1} =>
      (⟨((t.1 : ℝ) : ℂ) * Complex.I, contourMap_im ε hε t⟩ : ℍ)) := by
  rw [continuous_induced_rng]
  exact (Complex.continuous_ofReal.comp continuous_subtype_val).mul continuous_const

theorem isCompact_Cseg {ε : ℝ} (hε : 0 < ε) : IsCompact (Cseg ε hε) := by
  have hcs : CompactSpace {t : ℝ // t ∈ Set.Icc ε 1} := isCompact_iff_compactSpace.mp isCompact_Icc
  have := isCompact_univ.image (continuous_contourMap hε)
  simpa [Cseg, Set.image_univ] using this

lemma imagAxis_mem_Cseg {ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht : ε ≤ t) (ht1 : t ≤ 1)
    (h : 0 < t) : imagAxis t h ∈ Cseg ε hε := by
  refine ⟨⟨t, Set.mem_Icc.mpr ⟨ht, ht1⟩⟩, UpperHalfPlane.ext rfl⟩

/-- The contour point is `i t`. -/
lemma imagAxis_coe (t : ℝ) (h : 0 < t) : ((imagAxis t h : ℍ) : ℂ) = (t : ℂ) * Complex.I := rfl

/-! ## Global bounds on the box `K × Cseg` -/

theorem exists_bound_KfunClear_Cseg (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set ℍ} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ τ ∈ K, ∀ z ∈ Cseg ε hε, ‖KfunClear ℓ d τ z‖ ≤ M := by
  obtain ⟨R₁, hR₁pos, hR₁⟩ := exists_scale_bound_of_isCompact hK
  obtain ⟨R₂, hR₂pos, hR₂⟩ := exists_scale_bound_of_isCompact (isCompact_Cseg hε)
  exact exists_bound_KfunClear_of_scale_bounds ℓ d hd hR₁pos hR₂pos hR₁ hR₂

theorem exists_lower_DeltaFun_Cseg {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ Cseg ε hε, δ ≤ ‖DeltaFun z‖ :=
  exists_lower_DeltaFun (isCompact_Cseg hε)

/-! ## Continuity of the `j`-difference -/

theorem continuous_jInvariantFun_mr : Continuous (fun τ : ℍ => jInvariantFun τ) := by
  have hE4 : Continuous (fun τ : ℍ => E4Fun τ) :=
    (ModularForm.holo' ModularForm.E₄).continuous
  have hΔ : Continuous (fun τ : ℍ => DeltaFun τ) :=
    (CuspForm.holo' CuspForm.discriminant).continuous
  have hne : ∀ τ : ℍ, DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero
  have h : (fun τ : ℍ => jInvariantFun τ) = fun τ => E4Fun τ ^ 3 / DeltaFun τ := rfl
  rw [h]
  exact (hE4.pow 3).div hΔ hne

/-- The `j`-difference `(τ,z) ↦ j τ - j z` is continuous on `ℍ × ℍ`. -/
theorem continuous_jInvariantFun_sub :
    Continuous (fun p : ℍ × ℍ => jInvariantFun p.1 - jInvariantFun p.2) :=
  (continuous_jInvariantFun_mr.comp continuous_fst).sub
    (continuous_jInvariantFun_mr.comp continuous_snd)

/-! ## The contour point attached to a parameter -/

/-- The contour point `i t` attached to a parameter `(τ,t) ∈ K × [ε,1]`. -/
def pz {K : Set ℍ} {ε : ℝ} (hε : 0 < ε) (q : ℍ × ℝ) (hq : q ∈ Pspace K ε) : ℍ :=
  imagAxis q.2 (lt_of_lt_of_le hε (mem_Pspace.mp hq).2.1)

lemma pz_coe {K : Set ℍ} {ε : ℝ} (hε : 0 < ε) (q : ℍ × ℝ) (hq : q ∈ Pspace K ε) :
    ((pz hε q hq : ℍ) : ℂ) = (q.2 : ℂ) * Complex.I := rfl

lemma pz_mem_Cseg {K : Set ℍ} {ε : ℝ} (hε : 0 < ε) (q : ℍ × ℝ) (hq : q ∈ Pspace K ε) :
    pz hε q hq ∈ Cseg ε hε := by
  obtain ⟨hK, h1, h2⟩ := mem_Pspace.mp hq
  exact imagAxis_mem_Cseg hε h1 h2 _

lemma ofComplex_coe (τ : ℍ) : UpperHalfPlane.ofComplex (τ : ℂ) = τ := by
  have h := UpperHalfPlane.ofComplex_apply_of_im_pos τ.im_pos
  exact UpperHalfPlane.ext (by simpa using congrArg Subtype.val h)

lemma ofComplex_coe' (τ : ℍ) : ((UpperHalfPlane.ofComplex (τ : ℂ) : ℍ) : ℂ) = (τ : ℂ) := by
  rw [ofComplex_coe]

lemma mdiff_jInvariantFun : MDiff jInvariantFun := by
  have hE4 : MDiff (fun τ : ℍ => E4Fun τ) := ModularForm.holo' ModularForm.E₄
  have hΔ : MDiff (fun τ : ℍ => DeltaFun τ) := CuspForm.holo' CuspForm.discriminant
  change MDiff (fun τ : ℍ => E4Fun τ ^ 3 / DeltaFun τ)
  exact (hE4.pow 3).div hΔ (fun z => ClassicalFacts.DeltaFun_ne_zero z)

/-- Continuity of `j` at a point of `ℍ`, in the Euclidean coordinate. -/
lemma continuousAt_jInvariantFun_ofComplex (τ : ℍ) :
    ContinuousAt (fun w : ℂ => jInvariantFun (UpperHalfPlane.ofComplex w)) (τ : ℂ) := by
  have hdiff := UpperHalfPlane.mdifferentiable_iff.mp mdiff_jInvariantFun
  have hcont : ContinuousOn (fun w : ℂ => jInvariantFun (UpperHalfPlane.ofComplex w))
      {z : ℂ | 0 < z.im} := hdiff.continuousOn
  exact hcont.continuousAt
    ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds τ.im_pos)

/-- Continuity of `j` at a point of `ℍ`, in the Euclidean coordinate of `ℍ`. -/
lemma exists_norm_lt_jInvariantFun (τ₀ : ℍ) {e : ℝ} (he : 0 < e) :
    ∃ r : ℝ, 0 < r ∧ ∀ τ : ℍ, ‖(τ : ℂ) - (τ₀ : ℂ)‖ < r →
      ‖jInvariantFun τ - jInvariantFun τ₀‖ < e := by
  obtain ⟨ρ, hρpos, hρ⟩ := Metric.continuousAt_iff.mp
    (continuousAt_jInvariantFun_ofComplex τ₀) e he
  refine ⟨ρ, hρpos, fun τ hτ => ?_⟩
  have h := hρ (by rw [dist_eq_norm]; exact hτ)
  rw [dist_eq_norm] at h
  rwa [ofComplex_coe, ofComplex_coe] at h

/-! ## The local bound away from the coincidences -/

/-- The norm of the growth prefactor. -/
lemma norm_growthPrefactor (d : ℕ) (τ z : ℍ) :
    ‖growthPrefactor d τ z‖
      = ‖DeltaFun τ‖ * ‖DeltaFun z‖ ^ (if d = 8 then 1 else 2)
        * ‖jInvariantFun τ - jInvariantFun z‖ := by
  simp only [growthPrefactor, norm_mul, norm_pow]

theorem exists_local_bound_clean (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set ℍ} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε)
    (p : ℍ × ℝ) (hp : p ∈ Pspace K ε)
    (hne : jInvariantFun p.1 ≠ jInvariantFun (pz hε p hp)) :
    ∃ C : ℝ, 0 < C ∧ ∃ r : ℝ, 0 < r ∧ ∀ (q : ℍ × ℝ) (hq : q ∈ Pspace K ε),
      ‖(q.1 : ℂ) - (p.1 : ℂ)‖ < r → ‖((pz hε q hq : ℍ) : ℂ) - ((pz hε p hp : ℍ) : ℂ)‖ < r →
      ‖Kfun ℓ d q.1 (pz hε q hq)‖ ≤ C := by
  obtain ⟨M, hMpos, hM⟩ := exists_bound_KfunClear_Cseg ℓ d hd hK hε
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := exists_lower_DeltaFun hK
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := exists_lower_DeltaFun_Cseg hε
  set Jp : ℝ := ‖jInvariantFun p.1 - jInvariantFun (pz hε p hp)‖ with hJp
  have hJppos : 0 < Jp := by
    rw [hJp]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have h3pos : (0:ℝ) < Jp / 3 := by linarith
  obtain ⟨ρ₁, hρ₁pos, hρ₁⟩ := exists_norm_lt_jInvariantFun p.1 h3pos
  obtain ⟨ρ₂, hρ₂pos, hρ₂⟩ := exists_norm_lt_jInvariantFun (pz hε p hp) h3pos
  have hden : (0:ℝ) < δ₁ * δ₂ ^ (if d = 8 then 1 else 2) * (Jp / 3) :=
    mul_pos (mul_pos hδ₁pos (pow_pos hδ₂pos _)) h3pos
  refine ⟨M / (δ₁ * δ₂ ^ (if d = 8 then 1 else 2) * (Jp / 3)), div_pos hMpos hden,
    min ρ₁ ρ₂, lt_min hρ₁pos hρ₂pos, fun q hq hq1 hq2 => ?_⟩
  have hτ1 : ‖jInvariantFun q.1 - jInvariantFun p.1‖ < Jp / 3 :=
    hρ₁ q.1 (lt_of_lt_of_le hq1 (min_le_left _ _))
  have hz1 : ‖jInvariantFun (pz hε q hq) - jInvariantFun (pz hε p hp)‖ < Jp / 3 :=
    hρ₂ (pz hε q hq) (lt_of_lt_of_le hq2 (min_le_right _ _))
  -- `‖j p₁ - j z_p‖ = Jp` and the two perturbations are `< Jp/3`
  have hB : jInvariantFun p.1 - jInvariantFun (pz hε p hp)
      = (jInvariantFun q.1 - jInvariantFun (pz hε q hq))
        - (jInvariantFun q.1 - jInvariantFun (p.1))
        + (jInvariantFun (pz hε q hq) - jInvariantFun (pz hε p hp)) := by ring
  have hnormB : ‖jInvariantFun p.1 - jInvariantFun (pz hε p hp)‖ = Jp := rfl
  have hJq : Jp / 3 ≤ ‖jInvariantFun q.1 - jInvariantFun (pz hε q hq)‖ := by
    have hA' : ‖jInvariantFun q.1 - jInvariantFun (p.1)‖ = ‖jInvariantFun q.1 - jInvariantFun p.1‖ :=
      rfl
    have htri := norm_add_le
      ((jInvariantFun q.1 - jInvariantFun (pz hε q hq))
        - (jInvariantFun q.1 - jInvariantFun (p.1)))
      (jInvariantFun (pz hε q hq) - jInvariantFun (pz hε p hp))
    have hrewrite : (jInvariantFun q.1 - jInvariantFun (pz hε q hq))
        - (jInvariantFun q.1 - jInvariantFun (p.1))
        + (jInvariantFun (pz hε q hq) - jInvariantFun (pz hε p hp))
        = jInvariantFun p.1 - jInvariantFun (pz hε p hp) := by ring
    rw [hrewrite, hnormB] at htri
    have hsub : ‖(jInvariantFun q.1 - jInvariantFun (pz hε q hq))
        - (jInvariantFun q.1 - jInvariantFun (p.1))‖
        ≤ ‖jInvariantFun q.1 - jInvariantFun (pz hε q hq)‖
          + ‖jInvariantFun q.1 - jInvariantFun (p.1)‖ := norm_sub_le _ _
    linarith
  have hJpos : 0 < ‖jInvariantFun q.1 - jInvariantFun (pz hε q hq)‖ := by linarith
  have hjne : jInvariantFun q.1 ≠ jInvariantFun (pz hε q hq) := by
    intro h; rw [h, sub_self, norm_zero] at hJpos; exact lt_irrefl 0 hJpos
  have hK1 := ClearLink.KPlusClear_eq_smul d hd q.1 (pz hε q hq) hjne
  have hK2 := ClearLink.KMinusClear_eq_smul ℓ d hd q.1 (pz hε q hq) hjne
  have hP : growthPrefactor d q.1 (pz hε q hq) ≠ 0 := by
    simp only [growthPrefactor]
    exact mul_ne_zero (mul_ne_zero (ClassicalFacts.DeltaFun_ne_zero _)
      (pow_ne_zero _ (ClassicalFacts.DeltaFun_ne_zero _))) (sub_ne_zero.mpr hjne)
  have hKfun : Kfun ℓ d q.1 (pz hε q hq)
      = KfunClear ℓ d q.1 (pz hε q hq) / growthPrefactor d q.1 (pz hε q hq) := by
    rw [Kfun, KfunClear, hK1, hK2]
    field_simp
  have hM' := hM q.1 (mem_Pspace.mp hq).1 (pz hε q hq) (pz_mem_Cseg hε q hq)
  have hΔ1 := hδ₁ q.1 (mem_Pspace.mp hq).1
  have hΔ2 := hδ₂ (pz hε q hq) (pz_mem_Cseg hε q hq)
  have hZnn : (0:ℝ) ≤ δ₁ * δ₂ ^ (if d = 8 then 1 else 2) * (Jp / 3) :=
    hden.le
  have hpre : δ₁ * δ₂ ^ (if d = 8 then 1 else 2) * (Jp / 3)
      ≤ ‖growthPrefactor d q.1 (pz hε q hq)‖ := by
    simp only [norm_growthPrefactor]
    have h2 : δ₂ ^ (if d = 8 then 1 else 2)
        ≤ ‖DeltaFun (pz hε q hq)‖ ^ (if d = 8 then 1 else 2) :=
      pow_le_pow_left₀ hδ₂pos.le hΔ2 _
    have h3 : (0:ℝ) ≤ δ₂ ^ (if d = 8 then 1 else 2) := pow_nonneg hδ₂pos.le _
    have h5 : δ₁ * δ₂ ^ (if d = 8 then 1 else 2)
        ≤ ‖DeltaFun q.1‖ * ‖DeltaFun (pz hε q hq)‖ ^ (if d = 8 then 1 else 2) :=
      mul_le_mul hΔ1 h2 h3 (norm_nonneg _)
    exact mul_le_mul h5 hJq h3pos.le (mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _))
  have hprepos : 0 < ‖growthPrefactor d q.1 (pz hε q hq)‖ := by
    simp only [norm_growthPrefactor]
    exact mul_pos (mul_pos (lt_of_lt_of_le hδ₁pos hΔ1)
      (pow_pos (lt_of_lt_of_le hδ₂pos hΔ2) _)) hJpos
  have hfinal : ‖KfunClear ℓ d q.1 (pz hε q hq)‖ / ‖growthPrefactor d q.1 (pz hε q hq)‖
      ≤ M / (δ₁ * δ₂ ^ (if d = 8 then 1 else 2) * (Jp / 3)) := by
    rw [div_le_div_iff₀ hprepos hden]
    calc ‖KfunClear ℓ d q.1 (pz hε q hq)‖
          * (δ₁ * δ₂ ^ (if d = 8 then 1 else 2) * (Jp / 3))
        ≤ M * (δ₁ * δ₂ ^ (if d = 8 then 1 else 2) * (Jp / 3)) :=
          mul_le_mul_of_nonneg_right hM' hZnn
      _ ≤ M * ‖growthPrefactor d q.1 (pz hε q hq)‖ :=
          mul_le_mul_of_nonneg_left hpre hMpos.le
  rw [hKfun, norm_div]
  exact hfinal

end Work.Asymptotics