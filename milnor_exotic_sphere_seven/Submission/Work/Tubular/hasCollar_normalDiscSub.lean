import Mathlib
import Submission.Work.Tubular.chartedSpace_normalDisc_add
import Submission.Work.Tubular.mem_boundary_normalDiscSub_add
import Submission.Work.Surgery.Collar

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The normal disc bundle has a collar

`Work.Tubular.NormalDiscSub E ε` is the closed `ε`-disc bundle of the normal bundle of the
embedding `E : V ↪ ℝ^{8+k}`; it is a manifold with boundary whose boundary is the normal *sphere*
bundle `S_ε(ν)` (`Work.Tubular.mem_boundary_normalDiscSub_add`).  This file proves that it admits a
collar (`Work.Surgery.HasCollar (7 + k)`).

The construction is the **radial collar**

`(x, w, t) ↦ (x, w / (1 + t))`,   `x ∈ V`, `‖w‖ = ε`, `t ∈ [0, ∞)`,

the fibrewise version of `Work.Surgery.ballCollar`: the normal vector stays in the disc, it is never
zero on the image, and the image is the (open) complement of the zero section, so the map is an open
embedding onto an open set.  Its inverse is the fibrewise normalisation
`(x, w) ↦ ((x, ε/‖w‖ · w), ε/‖w‖ - 1)`.

The whole construction is carried out on the *sphere bundle* `S_ε(ν) = {q | ‖q.vec‖ = ε}`, which
needs no manifold structure; only at the very end is it transported to the boundary of the disc
bundle along the identification `Work.Tubular.mem_boundary_normalDiscSub_add`.
-/

open scoped Manifold Topology ContDiff
open Function Set

open Work.ThomBordism.PontryaginThom (EmbeddingData)

namespace Work.Tubular

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ} [NeZero k]

/-! ## The sphere bundle and the punctured disc bundle

Both are subsets of the closed disc bundle `D_ε(ν)`, defined by a condition on the normal vector. -/

/-- The normal sphere bundle `S_ε(ν)`, inside the closed disc bundle. -/
def sphereBundle (E : EmbeddingData V (8 + k)) (ε : ℝ) : Set (NormalDiscSub E ε) :=
  {q | ‖(q : NormalTotal E).vec‖ = ε}

/-- The disc bundle with its zero section removed. -/
def puncturedNormalDisc (E : EmbeddingData V (8 + k)) (ε : ℝ) : Set (NormalDiscSub E ε) :=
  {q | (q : NormalTotal E).vec ≠ 0}

@[simp] theorem mem_sphereBundle {E : EmbeddingData V (8 + k)} {ε : ℝ}
    {q : NormalDiscSub E ε} : q ∈ sphereBundle E ε ↔ ‖(q : NormalTotal E).vec‖ = ε := Iff.rfl

@[simp] theorem mem_puncturedNormalDisc {E : EmbeddingData V (8 + k)} {ε : ℝ}
    {q : NormalDiscSub E ε} : q ∈ puncturedNormalDisc E ε ↔ (q : NormalTotal E).vec ≠ 0 :=
  Iff.rfl

theorem isOpen_puncturedNormalDisc (E : EmbeddingData V (8 + k)) (ε : ℝ) :
    IsOpen (puncturedNormalDisc E ε) := by
  have h : puncturedNormalDisc E ε
      = ((fun q : NormalDiscSub E ε => (q : NormalTotal E).vec) ⁻¹' {0})ᶜ := by
    ext q
    simp [puncturedNormalDisc]
  rw [h]
  exact (isClosed_singleton.isOpen_compl).preimage
    ((NormalTotal.continuous_vec E).comp continuous_subtype_val)

/-- The fibrewise norm of the normal bundle is the norm of the normal vector. -/
theorem normalNorm_eq_norm_vec (E : EmbeddingData V (8 + k)) (p : NormalTotal E) :
    normalNorm E p = ‖p.vec‖ := rfl

/-- A point of the closed disc bundle has normal vector of norm at most `ε`. -/
theorem norm_vec_le_eps (E : EmbeddingData V (8 + k)) {ε : ℝ} (q : NormalDiscSub E ε) :
    ‖(q : NormalTotal E).vec‖ ≤ ε := q.2

/-! ## Continuity of the tautological maps on the two bundles -/

theorem continuous_punctured_val (E : EmbeddingData V (8 + k)) (ε : ℝ) :
    Continuous fun q : ↥(puncturedNormalDisc E ε) => ((q.1 : NormalDiscSub E ε) : NormalTotal E) :=
  continuous_subtype_val.comp continuous_subtype_val

theorem continuous_punctured_proj (E : EmbeddingData V (8 + k)) (ε : ℝ) :
    Continuous fun q : ↥(puncturedNormalDisc E ε) =>
      ((q.1 : NormalDiscSub E ε) : NormalTotal E).proj :=
  (NormalTotal.continuous_proj E).comp (continuous_punctured_val E ε)

theorem continuous_punctured_vec (E : EmbeddingData V (8 + k)) (ε : ℝ) :
    Continuous fun q : ↥(puncturedNormalDisc E ε) =>
      ((q.1 : NormalDiscSub E ε) : NormalTotal E).vec :=
  (NormalTotal.continuous_vec E).comp (continuous_punctured_val E ε)

theorem continuous_punctured_norm (E : EmbeddingData V (8 + k)) (ε : ℝ) :
    Continuous fun q : ↥(puncturedNormalDisc E ε) =>
      ‖((q.1 : NormalDiscSub E ε) : NormalTotal E).vec‖ :=
  (continuous_punctured_vec E ε).norm

theorem continuous_sphere_val (E : EmbeddingData V (8 + k)) (ε : ℝ) :
    Continuous fun p : ↥(sphereBundle E ε) => ((p.1 : NormalDiscSub E ε) : NormalTotal E) :=
  continuous_subtype_val.comp continuous_subtype_val

theorem continuous_sphere_proj (E : EmbeddingData V (8 + k)) (ε : ℝ) :
    Continuous fun p : ↥(sphereBundle E ε) =>
      ((p.1 : NormalDiscSub E ε) : NormalTotal E).proj :=
  (NormalTotal.continuous_proj E).comp (continuous_sphere_val E ε)

theorem continuous_sphere_vec (E : EmbeddingData V (8 + k)) (ε : ℝ) :
    Continuous fun p : ↥(sphereBundle E ε) =>
      ((p.1 : NormalDiscSub E ε) : NormalTotal E).vec :=
  (NormalTotal.continuous_vec E).comp (continuous_sphere_val E ε)

theorem continuous_sphere_param (E : EmbeddingData V (8 + k)) (ε : ℝ) :
    Continuous fun p : ↥(sphereBundle E ε) × Work.Surgery.HalfLine => 1 / (1 + (p.2 : ℝ)) := by
  have h2 : Continuous fun p : ↥(sphereBundle E ε) × Work.Surgery.HalfLine => (p.2 : ℝ) :=
    (continuous_subtype_val : Continuous fun t : Work.Surgery.HalfLine => (t : ℝ)).comp
      continuous_snd
  have h3 : Continuous fun p : ↥(sphereBundle E ε) × Work.Surgery.HalfLine =>
      (1 + (p.2 : ℝ) : ℝ) := continuous_const.add h2
  have hne : ∀ p : ↥(sphereBundle E ε) × Work.Surgery.HalfLine, (1 + (p.2 : ℝ) : ℝ) ≠ 0 := by
    intro p
    have ht : (0 : ℝ) ≤ (p.2 : ℝ) := p.2.2
    linarith
  exact (h3.inv₀ hne).congr (fun p => by simp only [Pi.inv_apply, one_div])

/-! ## The radial collar maps -/

/-- The underlying point of the radial collar map `(x, w, t) ↦ (x, w/(1+t))`. -/
def radialToTotal (E : EmbeddingData V (8 + k)) (ε : ℝ)
    (p : ↥(sphereBundle E ε) × Work.Surgery.HalfLine) : NormalTotal E :=
  ⟨(((p.1.1 : NormalDiscSub E ε) : NormalTotal E).proj,
      (1 / (1 + (p.2 : ℝ))) • ((p.1.1 : NormalDiscSub E ε) : NormalTotal E).vec),
   Submodule.smul_mem _ _ ((p.1.1 : NormalDiscSub E ε) : NormalTotal E).2⟩

/-- The scalar `1/(1+t)` is nonnegative. -/
theorem one_div_one_add_nonneg (t : Work.Surgery.HalfLine) : 0 ≤ 1 / (1 + (t : ℝ)) := by
  rw [one_div]
  exact inv_nonneg.mpr (by have := t.2; linarith)

/-- The scalar `1/(1+t)` is positive. -/
theorem one_div_one_add_pos (t : Work.Surgery.HalfLine) : 0 < 1 / (1 + (t : ℝ)) := by
  rw [one_div]
  exact inv_pos.mpr (by have := t.2; linarith)

/-- The scalar `1/(1+t)` is at most `1`. -/
theorem one_div_one_add_le_one (t : Work.Surgery.HalfLine) : 1 / (1 + (t : ℝ)) ≤ 1 := by
  rw [div_le_one (by have := t.2; linarith : (0 : ℝ) < 1 + (t : ℝ))]
  have := t.2
  linarith

theorem normalNorm_radialToTotal_le (E : EmbeddingData V (8 + k)) (ε : ℝ)
    (p : ↥(sphereBundle E ε) × Work.Surgery.HalfLine) :
    normalNorm E (radialToTotal E ε p) ≤ ε := by
  have hb : ‖((p.1.1 : NormalDiscSub E ε) : NormalTotal E).vec‖ = ε := p.1.2
  have hε0 : 0 ≤ ε := hb ▸ norm_nonneg _
  calc normalNorm E (radialToTotal E ε p)
      = ‖(1 / (1 + (p.2 : ℝ))) • ((p.1.1 : NormalDiscSub E ε) : NormalTotal E).vec‖ := rfl
    _ = ‖(1 / (1 + (p.2 : ℝ)))‖ * ‖((p.1.1 : NormalDiscSub E ε) : NormalTotal E).vec‖ := by
        rw [norm_smul]
    _ = (1 / (1 + (p.2 : ℝ))) * ε := by
        rw [Real.norm_of_nonneg (one_div_one_add_nonneg p.2), hb]
    _ ≤ 1 * ε := mul_le_mul_of_nonneg_right (one_div_one_add_le_one p.2) hε0
    _ = ε := one_mul ε

theorem radialToTotal_vec_ne_zero (E : EmbeddingData V (8 + k)) {ε : ℝ} (hε : ε ≠ 0)
    (p : ↥(sphereBundle E ε) × Work.Surgery.HalfLine) : (radialToTotal E ε p).vec ≠ 0 := by
  have hb : ‖((p.1.1 : NormalDiscSub E ε) : NormalTotal E).vec‖ = ε := p.1.2
  have hc : 0 < 1 / (1 + (p.2 : ℝ)) := one_div_one_add_pos p.2
  have hval : (radialToTotal E ε p).vec
      = (1 / (1 + (p.2 : ℝ))) • ((p.1.1 : NormalDiscSub E ε) : NormalTotal E).vec := rfl
  have hw : ((p.1.1 : NormalDiscSub E ε) : NormalTotal E).vec ≠ 0 := by
    intro h0
    exact hε (by rw [← hb, h0, norm_zero])
  intro h0
  rw [hval] at h0
  rcases smul_eq_zero.1 h0 with hc0 | hw0
  · exact (ne_of_gt hc) hc0
  · exact hw hw0

theorem continuous_radialToTotal (E : EmbeddingData V (8 + k)) (ε : ℝ) :
    Continuous (radialToTotal E ε) := by
  have hpair : Continuous fun p : ↥(sphereBundle E ε) × Work.Surgery.HalfLine =>
      (((p.1.1 : NormalDiscSub E ε) : NormalTotal E).proj,
        (1 / (1 + (p.2 : ℝ))) • ((p.1.1 : NormalDiscSub E ε) : NormalTotal E).vec) :=
    Continuous.prodMk
      ((NormalTotal.continuous_proj E).comp ((continuous_sphere_val E ε).comp continuous_fst))
      ((continuous_sphere_param E ε).smul
        ((NormalTotal.continuous_vec E).comp ((continuous_sphere_val E ε).comp continuous_fst)))
  have hmem : ∀ p : ↥(sphereBundle E ε) × Work.Surgery.HalfLine,
      (1 / (1 + (p.2 : ℝ))) • ((p.1.1 : NormalDiscSub E ε) : NormalTotal E).vec
        ∈ normalSpace E (((p.1.1 : NormalDiscSub E ε) : NormalTotal E).proj) :=
    fun p => Submodule.smul_mem _ _ ((p.1.1 : NormalDiscSub E ε) : NormalTotal E).2
  exact Continuous.subtype_mk hpair hmem

/-- The forward map of the radial collar, as a point of the punctured disc bundle. -/
def radialCollarToFun (E : EmbeddingData V (8 + k)) {ε : ℝ} (hε : ε ≠ 0)
    (p : ↥(sphereBundle E ε) × Work.Surgery.HalfLine) : ↥(puncturedNormalDisc E ε) :=
  ⟨⟨radialToTotal E ε p, normalNorm_radialToTotal_le E ε p⟩,
   radialToTotal_vec_ne_zero E hε p⟩

theorem continuous_radialCollarToFun (E : EmbeddingData V (8 + k)) {ε : ℝ} (hε : ε ≠ 0) :
    Continuous (radialCollarToFun E hε) := by
  have hinner : Continuous fun p : ↥(sphereBundle E ε) × Work.Surgery.HalfLine =>
      (⟨radialToTotal E ε p, normalNorm_radialToTotal_le E ε p⟩ : NormalDiscSub E ε) :=
    Continuous.subtype_mk (continuous_radialToTotal E ε)
      (fun p => normalNorm_radialToTotal_le E ε p)
  exact Continuous.subtype_mk hinner (fun p => radialToTotal_vec_ne_zero E hε p)

/-! ### The inverse of the radial collar -/

/-- The underlying point of the inverse of the radial collar. -/
def radialInvToTotal (E : EmbeddingData V (8 + k)) (ε : ℝ)
    (q : ↥(puncturedNormalDisc E ε)) : NormalTotal E :=
  ⟨(((q.1 : NormalDiscSub E ε) : NormalTotal E).proj,
      (ε / ‖((q.1 : NormalDiscSub E ε) : NormalTotal E).vec‖) •
        ((q.1 : NormalDiscSub E ε) : NormalTotal E).vec),
   Submodule.smul_mem _ _ ((q.1 : NormalDiscSub E ε) : NormalTotal E).2⟩

theorem norm_vec_radialInvToTotal (E : EmbeddingData V (8 + k)) (ε : ℝ)
    (q : ↥(puncturedNormalDisc E ε)) : ‖(radialInvToTotal E ε q).vec‖ = ε := by
  have hpos : 0 < ‖((q.1 : NormalDiscSub E ε) : NormalTotal E).vec‖ := norm_pos_iff.mpr q.2
  have hε0 : 0 ≤ ε := le_trans (norm_nonneg _) (norm_vec_le_eps E q.1)
  have hc0 : 0 ≤ ε / ‖((q.1 : NormalDiscSub E ε) : NormalTotal E).vec‖ :=
    div_nonneg hε0 (le_of_lt hpos)
  calc ‖(radialInvToTotal E ε q).vec‖
      = ‖(ε / ‖((q.1 : NormalDiscSub E ε) : NormalTotal E).vec‖) •
          ((q.1 : NormalDiscSub E ε) : NormalTotal E).vec‖ := rfl
    _ = (ε / ‖((q.1 : NormalDiscSub E ε) : NormalTotal E).vec‖) *
          ‖((q.1 : NormalDiscSub E ε) : NormalTotal E).vec‖ := by
        rw [norm_smul, Real.norm_of_nonneg hc0]
    _ = ε := by rw [div_mul_cancel₀ _ (ne_of_gt hpos)]

theorem normalNorm_radialInvToTotal_le (E : EmbeddingData V (8 + k)) (ε : ℝ)
    (q : ↥(puncturedNormalDisc E ε)) : normalNorm E (radialInvToTotal E ε q) ≤ ε :=
  le_of_eq (norm_vec_radialInvToTotal E ε q)

theorem continuous_radialInvToTotal (E : EmbeddingData V (8 + k)) (ε : ℝ) :
    Continuous (radialInvToTotal E ε) := by
  have hpair : Continuous fun q : ↥(puncturedNormalDisc E ε) =>
      (((q.1 : NormalDiscSub E ε) : NormalTotal E).proj,
        (ε / ‖((q.1 : NormalDiscSub E ε) : NormalTotal E).vec‖) •
          ((q.1 : NormalDiscSub E ε) : NormalTotal E).vec) :=
    Continuous.prodMk
      ((NormalTotal.continuous_proj E).comp (continuous_punctured_val E ε))
      ((continuous_const.div (continuous_punctured_norm E ε)
        (fun q => ne_of_gt (norm_pos_iff.mpr q.2))).smul (continuous_punctured_vec E ε))
  have hmem : ∀ q : ↥(puncturedNormalDisc E ε),
      (ε / ‖((q.1 : NormalDiscSub E ε) : NormalTotal E).vec‖) •
          ((q.1 : NormalDiscSub E ε) : NormalTotal E).vec
        ∈ normalSpace E (((q.1 : NormalDiscSub E ε) : NormalTotal E).proj) :=
    fun q => Submodule.smul_mem _ _ ((q.1 : NormalDiscSub E ε) : NormalTotal E).2
  exact Continuous.subtype_mk hpair hmem

/-- The inverse of the radial collar: fibrewise normalisation. -/
def radialCollarInvFun (E : EmbeddingData V (8 + k)) (ε : ℝ)
    (q : ↥(puncturedNormalDisc E ε)) : ↥(sphereBundle E ε) × Work.Surgery.HalfLine :=
  (⟨⟨radialInvToTotal E ε q, normalNorm_radialInvToTotal_le E ε q⟩,
     norm_vec_radialInvToTotal E ε q⟩,
   ⟨ε / ‖((q.1 : NormalDiscSub E ε) : NormalTotal E).vec‖ - 1, by
     have hpos : 0 < ‖((q.1 : NormalDiscSub E ε) : NormalTotal E).vec‖ := norm_pos_iff.mpr q.2
     have hle : ‖((q.1 : NormalDiscSub E ε) : NormalTotal E).vec‖ ≤ ε := norm_vec_le_eps E q.1
     have h1 : 1 ≤ ε / ‖((q.1 : NormalDiscSub E ε) : NormalTotal E).vec‖ :=
       (one_le_div hpos).mpr hle
     linarith⟩)

theorem continuous_radialCollarInvFun (E : EmbeddingData V (8 + k)) (ε : ℝ) :
    Continuous (radialCollarInvFun E ε) := by
  have hsphere : Continuous fun q : ↥(puncturedNormalDisc E ε) =>
      (⟨⟨radialInvToTotal E ε q, normalNorm_radialInvToTotal_le E ε q⟩,
        norm_vec_radialInvToTotal E ε q⟩ : ↥(sphereBundle E ε)) :=
    Continuous.subtype_mk
      (Continuous.subtype_mk (continuous_radialInvToTotal E ε)
        (fun q => normalNorm_radialInvToTotal_le E ε q))
      (fun q => norm_vec_radialInvToTotal E ε q)
  have htime : Continuous fun q : ↥(puncturedNormalDisc E ε) =>
      (⟨ε / ‖((q.1 : NormalDiscSub E ε) : NormalTotal E).vec‖ - 1, by
        have hpos : 0 < ‖((q.1 : NormalDiscSub E ε) : NormalTotal E).vec‖ :=
          norm_pos_iff.mpr q.2
        have hle : ‖((q.1 : NormalDiscSub E ε) : NormalTotal E).vec‖ ≤ ε :=
          norm_vec_le_eps E q.1
        have h1 : 1 ≤ ε / ‖((q.1 : NormalDiscSub E ε) : NormalTotal E).vec‖ :=
          (one_le_div hpos).mpr hle
        linarith⟩ : Work.Surgery.HalfLine) :=
    Continuous.subtype_mk
      ((continuous_const.div (continuous_punctured_norm E ε)
        (fun q => ne_of_gt (norm_pos_iff.mpr q.2))).sub continuous_const)
      (fun q => by
        show (0 : ℝ) ≤ ε / ‖((q.1 : NormalDiscSub E ε) : NormalTotal E).vec‖ - 1
        have hpos : 0 < ‖((q.1 : NormalDiscSub E ε) : NormalTotal E).vec‖ :=
          norm_pos_iff.mpr q.2
        have hle : ‖((q.1 : NormalDiscSub E ε) : NormalTotal E).vec‖ ≤ ε :=
          norm_vec_le_eps E q.1
        have h1 : 1 ≤ ε / ‖((q.1 : NormalDiscSub E ε) : NormalTotal E).vec‖ :=
          (one_le_div hpos).mpr hle
        linarith)
  exact Continuous.prodMk hsphere htime

/-! ### The two inverse identities -/

theorem radialCollarInvFun_toFun (E : EmbeddingData V (8 + k)) {ε : ℝ} (hε : ε ≠ 0)
    (p : ↥(sphereBundle E ε) × Work.Surgery.HalfLine) :
    radialCollarInvFun E ε (radialCollarToFun E hε p) = p := by
  obtain ⟨pb, t⟩ := p
  have hb : ‖((pb.1 : NormalDiscSub E ε) : NormalTotal E).vec‖ = ε := pb.2
  have hc : 0 < 1 / (1 + (t : ℝ)) := one_div_one_add_pos t
  have hn : ‖(1 / (1 + (t : ℝ))) • ((pb.1 : NormalDiscSub E ε) : NormalTotal E).vec‖
      = 1 / (1 + (t : ℝ)) * ε := by
    rw [norm_smul, Real.norm_of_nonneg (one_div_one_add_nonneg t), hb]
  refine Prod.ext ?_ ?_
  · refine Subtype.ext ?_
    refine Subtype.ext ?_
    refine Subtype.ext ?_
    refine Prod.ext rfl ?_
    show (ε / ‖(1 / (1 + (t : ℝ))) • ((pb.1 : NormalDiscSub E ε) : NormalTotal E).vec‖) •
        ((1 / (1 + (t : ℝ))) • ((pb.1 : NormalDiscSub E ε) : NormalTotal E).vec)
      = ((pb.1 : NormalDiscSub E ε) : NormalTotal E).vec
    rw [hn]
    have h1 : ε / ((1 / (1 + (t : ℝ))) * ε) = (1 / (1 + (t : ℝ)))⁻¹ := by field_simp
    rw [h1, smul_smul, inv_mul_cancel₀ (ne_of_gt hc), one_smul]
  · refine Subtype.ext ?_
    show ε / ‖(1 / (1 + (t : ℝ))) • ((pb.1 : NormalDiscSub E ε) : NormalTotal E).vec‖ - 1
      = (t : ℝ)
    have h1 : ε / ((1 / (1 + (t : ℝ))) * ε) = 1 + (t : ℝ) := by field_simp
    rw [hn, h1]
    ring

theorem radialCollarToFun_invFun (E : EmbeddingData V (8 + k)) {ε : ℝ} (hε : ε ≠ 0)
    (q : ↥(puncturedNormalDisc E ε)) :
    radialCollarToFun E hε (radialCollarInvFun E ε q) = q := by
  obtain ⟨qb, hqb⟩ := q
  have hpos : 0 < ‖((qb : NormalDiscSub E ε) : NormalTotal E).vec‖ := norm_pos_iff.mpr hqb
  have h1 : 1 + (ε / ‖((qb : NormalDiscSub E ε) : NormalTotal E).vec‖ - 1)
      = ε / ‖((qb : NormalDiscSub E ε) : NormalTotal E).vec‖ := by ring
  refine Subtype.ext ?_
  refine Subtype.ext ?_
  refine Subtype.ext ?_
  refine Prod.ext rfl ?_
  show (1 / (1 + (ε / ‖((qb : NormalDiscSub E ε) : NormalTotal E).vec‖ - 1))) •
      ((ε / ‖((qb : NormalDiscSub E ε) : NormalTotal E).vec‖) •
        ((qb : NormalDiscSub E ε) : NormalTotal E).vec)
    = ((qb : NormalDiscSub E ε) : NormalTotal E).vec
  rw [h1, one_div, smul_smul]
  rw [inv_mul_cancel₀ (div_ne_zero hε (ne_of_gt hpos)), one_smul]

/-! ## The collar homeomorphism and the collar -/

/-- **The radial collar homeomorphism**: `(x, w, t) ↦ (x, w/(1+t))` identifies the sphere bundle
times `[0,∞)` with the disc bundle minus its zero section. -/
def radialCollarHomeo (E : EmbeddingData V (8 + k)) {ε : ℝ} (hε : ε ≠ 0) :
    ↥(sphereBundle E ε) × Work.Surgery.HalfLine ≃ₜ ↥(puncturedNormalDisc E ε) where
  toFun := radialCollarToFun E hε
  invFun := radialCollarInvFun E ε
  left_inv := radialCollarInvFun_toFun E hε
  right_inv := radialCollarToFun_invFun E hε
  continuous_toFun := continuous_radialCollarToFun E hε
  continuous_invFun := continuous_radialCollarInvFun E ε

end

/-! ## The collar of the disc bundle -/

theorem hasCollar_normalDiscSub {V : Work.ThomBordism.Man8} {k : ℕ} [NeZero k] {ε : ℝ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} (C : Work.Tubular.TubeChart E ε)
    (R : Work.Tubular.DiscManifold.HalfModelReindex k) :
    letI : ChartedSpace (EuclideanHalfSpace (7 + k + 1)) (Work.Tubular.NormalDiscSub E ε) :=
      Work.Tubular.chartedSpace_normalDisc_add C R
    Work.Surgery.HasCollar (7 + k) (Work.Tubular.NormalDiscSub E ε) := by
  letI : ChartedSpace (EuclideanHalfSpace (7 + k + 1)) (Work.Tubular.NormalDiscSub E ε) :=
    Work.Tubular.chartedSpace_normalDisc_add C R
  have hε : ε ≠ 0 := ne_of_gt C.eps_pos
  -- the boundary of the disc bundle is the sphere bundle
  have hbdry : ∀ q : Work.Tubular.NormalDiscSub E ε,
      q ∈ (𝓡∂ (7 + k + 1)).boundary (Work.Tubular.NormalDiscSub E ε) ↔
        q ∈ Work.Tubular.sphereBundle E ε := by
    intro q
    have h := Work.Tubular.mem_boundary_normalDiscSub_add C R q
    rw [Work.Tubular.normalNorm_eq_norm_vec] at h
    exact h
  -- the homeomorphism identifying the boundary with the sphere bundle
  let τ : (𝓡∂ (7 + k + 1)).boundary (Work.Tubular.NormalDiscSub E ε) →
      ↥(Work.Tubular.sphereBundle E ε) := fun p => ⟨p.1, (hbdry p.1).1 p.2⟩
  let τ' : ↥(Work.Tubular.sphereBundle E ε) →
      (𝓡∂ (7 + k + 1)).boundary (Work.Tubular.NormalDiscSub E ε) :=
    fun q => ⟨q.1, (hbdry q.1).2 q.2⟩
  have hτ : Function.LeftInverse τ' τ := fun p => Subtype.ext rfl
  have hτ' : Function.RightInverse τ' τ := fun q => Subtype.ext rfl
  have hcτ : Continuous τ :=
    Continuous.subtype_mk continuous_subtype_val (fun p => (hbdry p.1).1 p.2)
  have hcτ' : Continuous τ' :=
    Continuous.subtype_mk continuous_subtype_val (fun q => (hbdry q.1).2 q.2)
  let τh : (𝓡∂ (7 + k + 1)).boundary (Work.Tubular.NormalDiscSub E ε) ≃ₜ
      ↥(Work.Tubular.sphereBundle E ε) :=
    { toFun := τ, invFun := τ', left_inv := hτ, right_inv := hτ',
      continuous_toFun := hcτ, continuous_invFun := hcτ' }
  let τp : ((𝓡∂ (7 + k + 1)).boundary (Work.Tubular.NormalDiscSub E ε) ×
      Work.Surgery.HalfLine) ≃ₜ (↥(Work.Tubular.sphereBundle E ε) × Work.Surgery.HalfLine) :=
    τh.prodCongr (Homeomorph.refl Work.Surgery.HalfLine)
  refine ⟨{ toFun := fun p => (Work.Tubular.radialCollarHomeo E hε (τp p) :
              Work.Tubular.NormalDiscSub E ε)
            isOpenEmbedding := ?_
            toFun_zero := ?_ }⟩
  · exact (Work.Tubular.isOpen_puncturedNormalDisc E ε).isOpenEmbedding_subtypeVal.comp
      ((Work.Tubular.radialCollarHomeo E hε).isOpenEmbedding.comp τp.isOpenEmbedding)
  · intro x
    refine Subtype.ext ?_
    refine Subtype.ext ?_
    refine Prod.ext rfl ?_
    show (1 / (1 + ((⟨0, le_refl 0⟩ : Work.Surgery.HalfLine) : ℝ))) •
        ((x.1 : Work.Tubular.NormalDiscSub E ε) : Work.Tubular.NormalTotal E).vec
      = ((x.1 : Work.Tubular.NormalDiscSub E ε) : Work.Tubular.NormalTotal E).vec
    simp

end Work.Tubular
