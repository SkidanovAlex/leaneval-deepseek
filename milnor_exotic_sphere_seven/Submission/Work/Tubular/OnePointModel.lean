import Submission.Work.Tubular.Defs
import Submission.Work.Tubular.Compact
import Submission.Work.Tubular.Collapse
import Submission.Work.Tubular.TubeBasic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
# The Thom space of the normal bundle, metric-free: `Th(ν) ≃ₜ ν⁺`

The Grassmann chapter models the Thom space of the universal bundle as the **one-point
compactification** of its total space (`Work.ThomBordism.Grassmann.TautologicalThomSpace k m =
OnePoint (tautologicalBundle k m).TotalSpace`), because the tautological bundle carries no
`IsEuclidean` structure (`tautologicalBundleNotEuclidean.lean`).  For the ν-side of the
Pontryagin–Thom construction we must therefore identify the `D_ε/S_ε` quotient
(`Work.Tubular.NormalThomSpace E ε`, a *closed disc bundle modulo its sphere bundle*, which is what
the tubular map produces) with the one-point compactification `OnePoint (NormalTotal E)`.

The identification is the classical radial homeomorphism: a point of the interior of the disc bundle
of norm `t < ε` is sent to its blow-up `(ε/(ε - t)) • p`, and the whole sphere bundle is sent to
`∞`.  This file proves that this is a homeomorphism (`Work.Tubular.normalThomToOnePoint`), from which
the forms needed by the Pontryagin–Thom chapter follow:

* `Work.Tubular.normalThomSpace_homeo_onePoint` — the identification of the two models;
* `Work.Tubular.collapseToOnePoint` — **the Pontryagin–Thom collapse in the metric-free model**:
  a continuous map `S^N = OnePoint ℝ^N → OnePoint (NormalTotal E)`, `∞ ↦ ∞`, which on the open tube
  is the blow-up of the normal foot and which is `∞` off the open tube.  This is the map that the
  Gauss/classifying map of the Grassmann chapter is composed with to obtain `α_V`.

The hypothesis is a point of the sphere bundle `NormalSphSub E ε`.  This is *not* automatic: for
codimension `0` (an embedding `V ↪ ℝ^8`, so that `ν = 0` and every normal vector is `0`) the sphere
bundle is empty and `NormalThomSpace E ε` is `V` itself, not `ν⁺ = V⁺`.  For `E : EmbeddingData V
(8+k)` with `0 < k` it is `Work.Tubular.nonempty_normalSphSub`.
-/

open scoped Manifold ContDiff Topology unitInterval
open Function Topology Filter Set

open Work.ThomBordism.PontryaginThom (EmbeddingData)

namespace Work.Tubular

noncomputable section

variable {V : Work.ThomBordism.Man8} {N : ℕ}

/-! ## The radial rescaling of the normal bundle -/

/-- The blow-up coefficient `ε / (ε - ‖p‖)`: the fibrewise radial factor taking the open `ε`-disc
into the whole normal bundle. -/
def blowCoeff (E : EmbeddingData V N) (ε : ℝ) (p : NormalTotal E) : ℝ :=
  ε * (ε - normalNorm E p)⁻¹

/-- The shrink coefficient `ε / (ε + ‖p‖)`: its inverse, taking the whole normal bundle into the
closed `ε`-disc bundle. -/
def shrinkCoeff (E : EmbeddingData V N) (ε : ℝ) (p : NormalTotal E) : ℝ :=
  ε * (ε + normalNorm E p)⁻¹

/-- The radial **blow-up** `p ↦ (ε/(ε - ‖p‖)) • p` of the normal bundle along the fibres. -/
def normalBlowUp (E : EmbeddingData V N) (ε : ℝ) (p : NormalTotal E) : NormalTotal E :=
  ⟨(p.1.1, blowCoeff E ε p • p.1.2), Submodule.smul_mem _ _ p.2⟩

/-- The radial **shrink** `p ↦ (ε/(ε + ‖p‖)) • p`, the inverse of `normalBlowUp`. -/
def normalShrink (E : EmbeddingData V N) (ε : ℝ) (p : NormalTotal E) : NormalTotal E :=
  ⟨(p.1.1, shrinkCoeff E ε p • p.1.2), Submodule.smul_mem _ _ p.2⟩

@[simp] theorem normalBlowUp_proj (E : EmbeddingData V N) (ε : ℝ) (p : NormalTotal E) :
    (normalBlowUp E ε p).1.1 = p.1.1 := rfl

@[simp] theorem normalBlowUp_vec (E : EmbeddingData V N) (ε : ℝ) (p : NormalTotal E) :
    (normalBlowUp E ε p).1.2 = blowCoeff E ε p • p.1.2 := rfl

@[simp] theorem normalShrink_proj (E : EmbeddingData V N) (ε : ℝ) (p : NormalTotal E) :
    (normalShrink E ε p).1.1 = p.1.1 := rfl

@[simp] theorem normalShrink_vec (E : EmbeddingData V N) (ε : ℝ) (p : NormalTotal E) :
    (normalShrink E ε p).1.2 = shrinkCoeff E ε p • p.1.2 := rfl

theorem blowCoeff_pos {E : EmbeddingData V N} {ε : ℝ} (hε : 0 < ε) {p : NormalTotal E}
    (hp : normalNorm E p < ε) : 0 < blowCoeff E ε p :=
  mul_pos hε (inv_pos.mpr (by linarith))

theorem shrinkCoeff_pos {E : EmbeddingData V N} {ε : ℝ} (hε : 0 < ε) (p : NormalTotal E) :
    0 < shrinkCoeff E ε p :=
  mul_pos hε (inv_pos.mpr (by have := normalNorm_nonneg E p; linarith))

/-- The norm of the blow-up, in closed form. -/
theorem normalNorm_normalBlowUp {E : EmbeddingData V N} {ε : ℝ} (hε : 0 < ε) {p : NormalTotal E}
    (hp : normalNorm E p < ε) :
    normalNorm E (normalBlowUp E ε p) = ε * normalNorm E p / (ε - normalNorm E p) := by
  rw [normalNorm, normalBlowUp_vec, norm_smul, Real.norm_eq_abs,
    abs_of_pos (blowCoeff_pos hε hp), blowCoeff, normalNorm]
  ring

/-- The norm of the shrink, in closed form. -/
theorem normalNorm_normalShrink {E : EmbeddingData V N} {ε : ℝ} (hε : 0 < ε) (p : NormalTotal E) :
    normalNorm E (normalShrink E ε p) = ε * normalNorm E p / (ε + normalNorm E p) := by
  rw [normalNorm, normalShrink_vec, norm_smul, Real.norm_eq_abs,
    abs_of_pos (shrinkCoeff_pos hε p), shrinkCoeff, normalNorm]
  ring

/-- The shrink lands in the closed `ε`-disc bundle. -/
theorem normalNorm_normalShrink_le {E : EmbeddingData V N} {ε : ℝ} (hε : 0 < ε)
    (p : NormalTotal E) : normalNorm E (normalShrink E ε p) ≤ ε := by
  rw [normalNorm_normalShrink hε p]
  rw [div_le_iff₀ (by have := normalNorm_nonneg E p; linarith)]
  nlinarith [normalNorm_nonneg E p]

/-- The shrink lands in the **open** `ε`-disc bundle. -/
theorem normalNorm_normalShrink_lt {E : EmbeddingData V N} {ε : ℝ} (hε : 0 < ε)
    (p : NormalTotal E) : normalNorm E (normalShrink E ε p) < ε := by
  rw [normalNorm_normalShrink hε p]
  rw [div_lt_iff₀ (by have := normalNorm_nonneg E p; linarith)]
  nlinarith [normalNorm_nonneg E p]

/-- The two radial factors are mutually inverse along the shrink. -/
theorem blowCoeff_normalShrink_mul {E : EmbeddingData V N} {ε : ℝ} (hε : 0 < ε)
    (p : NormalTotal E) : blowCoeff E ε (normalShrink E ε p) * shrinkCoeff E ε p = 1 := by
  have he : ε ≠ 0 := ne_of_gt hε
  have h1 : ε + normalNorm E p ≠ 0 := by have := normalNorm_nonneg E p; positivity
  have h2 : ε ^ 2 / (ε + normalNorm E p) ≠ 0 := div_ne_zero (pow_ne_zero 2 he) h1
  have heq : ε - ε * normalNorm E p / (ε + normalNorm E p)
      = ε ^ 2 / (ε + normalNorm E p) := by
    field_simp
    ring
  rw [blowCoeff, normalNorm_normalShrink hε p, shrinkCoeff, heq,
    show (ε ^ 2 / (ε + normalNorm E p))⁻¹ = (ε + normalNorm E p) / ε ^ 2 from inv_div _ _]
  field_simp

/-- The two radial factors are mutually inverse along the blow-up. -/
theorem shrinkCoeff_normalBlowUp_mul {E : EmbeddingData V N} {ε : ℝ} (hε : 0 < ε)
    {p : NormalTotal E} (hp : normalNorm E p < ε) :
    shrinkCoeff E ε (normalBlowUp E ε p) * blowCoeff E ε p = 1 := by
  have he : ε ≠ 0 := ne_of_gt hε
  have h1 : ε - normalNorm E p ≠ 0 := by have := normalNorm_nonneg E p; linarith
  have h2 : ε ^ 2 / (ε - normalNorm E p) ≠ 0 := div_ne_zero (pow_ne_zero 2 he) h1
  have heq : ε + ε * normalNorm E p / (ε - normalNorm E p)
      = ε ^ 2 / (ε - normalNorm E p) := by
    field_simp
    ring
  rw [shrinkCoeff, normalNorm_normalBlowUp hε hp, blowCoeff, heq,
    show (ε ^ 2 / (ε - normalNorm E p))⁻¹ = (ε - normalNorm E p) / ε ^ 2 from inv_div _ _]
  field_simp

/-- The blow-up and the shrink are mutually inverse on the normal bundle. -/
theorem normalBlowUp_normalShrink {E : EmbeddingData V N} {ε : ℝ} (hε : 0 < ε)
    (p : NormalTotal E) : normalBlowUp E ε (normalShrink E ε p) = p := by
  apply NormalTotal.ext
  apply Prod.ext
  · rfl
  · rw [normalBlowUp_vec, normalShrink_vec, smul_smul, blowCoeff_normalShrink_mul hε p, one_smul]

/-- The shrink and the blow-up are mutually inverse on the open disc bundle. -/
theorem normalShrink_normalBlowUp {E : EmbeddingData V N} {ε : ℝ} (hε : 0 < ε)
    {p : NormalTotal E} (hp : normalNorm E p < ε) : normalShrink E ε (normalBlowUp E ε p) = p := by
  apply NormalTotal.ext
  apply Prod.ext
  · rfl
  · rw [normalShrink_vec, normalBlowUp_vec, smul_smul, shrinkCoeff_normalBlowUp_mul hε hp, one_smul]

/-- **The blow-up is continuous at every point of the open disc bundle.**  (It is *not*
continuous at the sphere bundle, where the coefficient blows up; the collapse there is handled by
the `∞` branch of `normalDiscToOnePoint`.) -/
theorem continuousAt_normalBlowUp {E : EmbeddingData V N} {ε : ℝ} {p₀ : NormalTotal E}
    (hp₀ : normalNorm E p₀ < ε) : ContinuousAt (normalBlowUp E ε) p₀ := by
  have hne : ε - normalNorm E p₀ ≠ 0 := by have := normalNorm_nonneg E p₀; linarith
  have hinv : ContinuousAt (fun p : NormalTotal E => ((ε - normalNorm E p)⁻¹ : ℝ)) p₀ :=
    (continuousAt_const.sub ((continuous_normalNorm E).continuousAt)).inv₀ hne
  have hbase : ContinuousAt (fun p : NormalTotal E =>
      ((p.1.1, (ε * (ε - normalNorm E p)⁻¹) • p.1.2) : V.pt × Euc N)) p₀ :=
    ContinuousAt.prodMk
      ((continuous_fst.comp continuous_subtype_val).continuousAt)
      ((ContinuousAt.const_mul hinv ε).smul
        ((continuous_snd.comp continuous_subtype_val).continuousAt))
  have hval : (Subtype.val ∘ fun p : NormalTotal E => normalBlowUp E ε p)
      = fun p => (p.1.1, (ε * (ε - normalNorm E p)⁻¹) • p.1.2) := by
    funext p
    rfl
  rw [← continuousWithinAt_univ,
    (Topology.IsEmbedding.subtypeVal
      (p := fun q : V.pt × Euc N => q.2 ∈ normalSpace E q.1)).isInducing.continuousWithinAt_iff,
    hval]
  simpa only [ContinuousWithinAt, ContinuousAt, nhdsWithin_univ] using hbase

/-! ## The map `D_ε(ν) → ν⁺` and its continuity -/

/-- The map `D_ε(ν) → ν⁺`: the sphere bundle is collapsed to `∞`, the interior is blown up. -/
def normalDiscToOnePoint (E : EmbeddingData V N) (ε : ℝ) (q : NormalDiscSub E ε) :
    OnePoint (NormalTotal E) :=
  if normalNorm E q.1 = ε then OnePoint.infty else OnePoint.some (normalBlowUp E ε q.1)

@[simp] theorem normalDiscToOnePoint_of_eq (E : EmbeddingData V N) (ε : ℝ)
    {q : NormalDiscSub E ε} (hq : normalNorm E q.1 = ε) :
    normalDiscToOnePoint E ε q = OnePoint.infty := if_pos hq

@[simp] theorem normalDiscToOnePoint_of_lt (E : EmbeddingData V N) (ε : ℝ)
    {q : NormalDiscSub E ε} (hq : normalNorm E q.1 < ε) :
    normalDiscToOnePoint E ε q = OnePoint.some (normalBlowUp E ε q.1) :=
  if_neg (ne_of_lt hq)

/-- The sphere bundle of the closed disc bundle is closed in it. -/
theorem isClosed_normalSphereInDisc (E : EmbeddingData V N) (ε : ℝ) :
    IsClosed (normalSphereInDisc E ε) :=
  isClosed_eq ((continuous_normalNorm E).comp continuous_subtype_val) continuous_const

/-- The open disc bundle is open in the closed one. -/
theorem isOpen_normalOpenDiscInDisc (E : EmbeddingData V N) (ε : ℝ) :
    IsOpen {q : NormalDiscSub E ε | normalNorm E q.1 < ε} :=
  isOpen_lt ((continuous_normalNorm E).comp continuous_subtype_val) continuous_const

/-- The algebraic core of the continuity at the sphere: beyond the threshold `Mε/(M+ε)` the blow-up
of a point of norm `< ε` has norm `> M`. -/
theorem lt_norm_normalBlowUp {ε M t : ℝ} (hε : 0 < ε) (hM : 0 ≤ M)
    (h1 : M * ε / (M + ε) < t) (h2 : t < ε) : M < ε * t / (ε - t) := by
  have h3 : 0 < ε - t := by linarith
  rw [lt_div_iff₀ h3]
  have h4 : M * ε < t * (M + ε) :=
    (div_lt_iff₀ (show (0 : ℝ) < M + ε by linarith)).mp h1
  nlinarith [h4]

/-- **The map `D_ε(ν) → ν⁺` is continuous.** -/
theorem continuous_normalDiscToOnePoint (E : EmbeddingData V N) {ε : ℝ} (hε : 0 < ε) :
    Continuous (normalDiscToOnePoint E ε) := by
  rw [continuous_iff_continuousAt]
  intro q₀
  by_cases hq : normalNorm E q₀.1 = ε
  · rw [ContinuousAt, normalDiscToOnePoint_of_eq E ε hq]
    refine (OnePoint.hasBasis_nhds_infty.tendsto_right_iff).mpr ?_
    intro K hK
    obtain ⟨hKc, hKcomp⟩ := hK
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp
      ((hKcomp.image (continuous_normalNorm E)).isBounded)
    set M : ℝ := max r 0 with hMdef
    have hM0 : 0 ≤ M := le_max_right _ _
    have hKM : ∀ x ∈ K, normalNorm E x ≤ M := by
      intro x hx
      have h1 : normalNorm E x ∈ Metric.closedBall (0 : ℝ) r := hr (Set.mem_image_of_mem _ hx)
      have h2 := Metric.mem_closedBall.mp h1
      rw [Real.dist_eq, sub_zero] at h2
      exact le_trans (le_abs_self _) (le_trans h2 (le_max_left _ _))
    have hMpos : (0 : ℝ) < M + ε := by linarith
    have hth : M * ε / (M + ε) < normalNorm E q₀.1 := by
      rw [hq, div_lt_iff₀ hMpos]
      nlinarith
    refine Filter.mem_of_superset
      ((isOpen_lt continuous_const
        ((continuous_normalNorm E).comp continuous_subtype_val)).mem_nhds hth) ?_
    intro q hqM
    show normalDiscToOnePoint E ε q ∈ OnePoint.some '' Kᶜ ∪ {OnePoint.infty}
    by_cases hqe : normalNorm E q.1 = ε
    · rw [normalDiscToOnePoint_of_eq E ε hqe]
      exact Or.inr rfl
    · have hqlt : normalNorm E q.1 < ε := lt_of_le_of_ne q.2 hqe
      rw [normalDiscToOnePoint_of_lt E ε hqlt]
      refine Or.inl ⟨normalBlowUp E ε q.1, fun hmem => ?_, rfl⟩
      have hle := hKM _ hmem
      rw [normalNorm_normalBlowUp hε hqlt] at hle
      exact absurd hle (not_le.mpr (lt_norm_normalBlowUp hε hM0 hqM hqlt))
  · have hlt : normalNorm E q₀.1 < ε := lt_of_le_of_ne q₀.2 hq
    have hcont : ContinuousAt
        (fun q : NormalDiscSub E ε => OnePoint.some (normalBlowUp E ε q.1)) q₀ :=
      (OnePoint.continuous_coe.continuousAt.comp
        ((continuousAt_normalBlowUp hlt).comp continuous_subtype_val.continuousAt))
    refine hcont.congr ?_
    filter_upwards [(isOpen_normalOpenDiscInDisc E ε).mem_nhds hlt] with q hq'
    exact (normalDiscToOnePoint_of_lt E ε hq').symm

theorem normalDiscToOnePoint_eq_of_thomRel {E : EmbeddingData V N} {ε : ℝ}
    {q q' : NormalDiscSub E ε} (h : normalThomSetoid E ε q q') :
    normalDiscToOnePoint E ε q = normalDiscToOnePoint E ε q' := by
  rcases h with h | ⟨h1, h2⟩
  · rw [h]
  · rw [normalDiscToOnePoint_of_eq E ε h1, normalDiscToOnePoint_of_eq E ε h2]

/-- The descent of `normalDiscToOnePoint` to the Thom space: the map `Th(ν) → ν⁺`. -/
def normalThomToOnePoint (E : EmbeddingData V N) (ε : ℝ) :
    NormalThomSpace E ε → OnePoint (NormalTotal E) :=
  fun q => Quotient.liftOn q (normalDiscToOnePoint E ε)
    (fun _ _ h => normalDiscToOnePoint_eq_of_thomRel h)

@[simp] theorem normalThomToOnePoint_mk (E : EmbeddingData V N) (ε : ℝ) (q : NormalDiscSub E ε) :
    normalThomToOnePoint E ε (normalThomMk E ε q) = normalDiscToOnePoint E ε q := rfl

theorem continuous_normalThomToOnePoint (E : EmbeddingData V N) {ε : ℝ} (hε : 0 < ε) :
    Continuous (normalThomToOnePoint E ε) := by
  exact ((isQuotientMap_quotient_mk' (s := normalThomSetoid E ε)).continuous_iff
    (g := normalThomToOnePoint E ε)).mpr (continuous_normalDiscToOnePoint E hε)

/-! ## The homeomorphism `Th(ν) ≃ₜ ν⁺` -/

/-- The shrink of a normal vector, as a point of the closed disc bundle. -/
def normalShrinkDisc {E : EmbeddingData V N} {ε : ℝ} (hε : 0 < ε) (p : NormalTotal E) :
    NormalDiscSub E ε :=
  ⟨normalShrink E ε p, normalNorm_normalShrink_le hε p⟩

@[simp] theorem normalShrinkDisc_coe {E : EmbeddingData V N} {ε : ℝ} (hε : 0 < ε)
    (p : NormalTotal E) : ((normalShrinkDisc hε p : NormalDiscSub E ε) : NormalTotal E)
      = normalShrink E ε p := rfl

theorem normalThomToOnePoint_surjective {E : EmbeddingData V N} {ε : ℝ} (hε : 0 < ε)
    (q : NormalSphSub E ε) : Function.Surjective (normalThomToOnePoint E ε) := by
  intro y
  cases y with
  | infty =>
    refine ⟨normalThomBasepoint E ε q, ?_⟩
    show normalThomToOnePoint E ε (normalThomMk E ε ⟨q.1, le_of_eq q.2⟩) = OnePoint.infty
    rw [normalThomToOnePoint_mk]
    exact normalDiscToOnePoint_of_eq E ε q.2
  | coe p =>
    refine ⟨normalThomMk E ε (normalShrinkDisc hε p), ?_⟩
    rw [normalThomToOnePoint_mk]
    rw [normalDiscToOnePoint_of_lt E ε (q := normalShrinkDisc hε p)
      (normalNorm_normalShrink_lt hε p)]
    rw [normalShrinkDisc_coe, normalBlowUp_normalShrink hε p]

theorem normalDiscToOnePoint_injective {E : EmbeddingData V N} {ε : ℝ} (hε : 0 < ε)
    {a b : NormalDiscSub E ε} (h : normalDiscToOnePoint E ε a = normalDiscToOnePoint E ε b) :
    normalThomSetoid E ε a b := by
  rcases eq_or_ne (normalNorm E a.1) ε with ha | ha
  · rcases eq_or_ne (normalNorm E b.1) ε with hb | hb
    · exact Or.inr ⟨ha, hb⟩
    · exfalso
      have h' : (OnePoint.infty : OnePoint (NormalTotal E))
          = OnePoint.some (normalBlowUp E ε b.1) := by
        rw [normalDiscToOnePoint_of_eq E ε (q := a) ha,
          normalDiscToOnePoint_of_lt E ε (q := b) (lt_of_le_of_ne b.2 hb)] at h
        exact h
      exact OnePoint.infty_ne_coe _ h'
  · rcases eq_or_ne (normalNorm E b.1) ε with hb | hb
    · exfalso
      have h' : (OnePoint.some (normalBlowUp E ε a.1) : OnePoint (NormalTotal E))
          = OnePoint.infty := by
        rw [normalDiscToOnePoint_of_lt E ε (q := a) (lt_of_le_of_ne a.2 ha),
          normalDiscToOnePoint_of_eq E ε (q := b) hb] at h
        exact h
      exact OnePoint.coe_ne_infty _ h'
    · refine Or.inl (Subtype.ext ?_)
      have h2 : normalBlowUp E ε a.1 = normalBlowUp E ε b.1 := by
        rw [normalDiscToOnePoint_of_lt E ε (q := a) (lt_of_le_of_ne a.2 ha),
          normalDiscToOnePoint_of_lt E ε (q := b) (lt_of_le_of_ne b.2 hb)] at h
        exact OnePoint.coe_eq_coe.mp h
      rw [← normalShrink_normalBlowUp hε (lt_of_le_of_ne a.2 ha),
        ← normalShrink_normalBlowUp hε (lt_of_le_of_ne b.2 hb), h2]

set_option backward.isDefEq.respectTransparency false in
theorem normalThomToOnePoint_injective {E : EmbeddingData V N} {ε : ℝ} (hε : 0 < ε) :
    Function.Injective (normalThomToOnePoint E ε) := by
  intro q q' h
  revert h
  refine Quotient.inductionOn₂ q q' ?_
  intro a b hab
  exact Quotient.sound (normalDiscToOnePoint_injective hε
    (show normalDiscToOnePoint E ε a = normalDiscToOnePoint E ε b from hab))

/-- **The radial homeomorphism `Th(ν) ≃ₜ ν⁺`**, as a bijective map. -/
def normalThomToOnePointEquiv {E : EmbeddingData V N} {ε : ℝ} (hε : 0 < ε)
    (q : NormalSphSub E ε) : NormalThomSpace E ε ≃ OnePoint (NormalTotal E) :=
  Equiv.ofBijective (normalThomToOnePoint E ε)
    ⟨normalThomToOnePoint_injective hε, normalThomToOnePoint_surjective hε q⟩

/-- **The radial homeomorphism `Th(ν) ≃ₜ ν⁺`**, the homeomorphism realised by
`normalThomToOnePoint`. -/
def normalThomToOnePointHomeo {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : EmbeddingData V (8 + k)) {ε : ℝ} (hε : 0 < ε) (q : NormalSphSub E ε) :
    NormalThomSpace E ε ≃ₜ OnePoint (NormalTotal E) :=
  haveI : CompactSpace (NormalDiscSub E ε) := compactSpace_normalDiscSub E ε
  haveI : CompactSpace (NormalThomSpace E ε) := Quotient.compactSpace
  haveI : LocallyCompactSpace (NormalTotal E) := (isClosed_normalGraph E).locallyCompactSpace
  haveI : T2Space (OnePoint (NormalTotal E)) := inferInstance
  Continuous.homeoOfEquivCompactToT2 (f := normalThomToOnePointEquiv hε q)
    (by
      show Continuous (normalThomToOnePoint E ε)
      exact continuous_normalThomToOnePoint E hε)

@[simp] theorem normalThomToOnePointHomeo_apply {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : EmbeddingData V (8 + k)) {ε : ℝ} (hε : 0 < ε) (q : NormalSphSub E ε)
    (x : NormalThomSpace E ε) :
    normalThomToOnePointHomeo E hε q x = normalThomToOnePoint E ε x := by
  show normalThomToOnePointEquiv hε q x = normalThomToOnePoint E ε x
  exact Equiv.ofBijective_apply _ _ x

/-- **The Thom space of the normal bundle is the one-point compactification of the normal bundle.**
This is the identification that lets the `D_ε/S_ε` model produced by the tubular map be compared
with the metric-free model `OnePoint (TotalSpace γ)` of the Grassmann chapter. -/
theorem normalThomSpace_homeo_onePoint {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : EmbeddingData V (8 + k)) {ε : ℝ} (hε : 0 < ε) (q : NormalSphSub E ε) :
    Nonempty (NormalThomSpace E ε ≃ₜ OnePoint (NormalTotal E)) :=
  ⟨normalThomToOnePointHomeo E hε q⟩

/-! ## The Pontryagin–Thom collapse in the metric-free model -/

/-- **The Pontryagin–Thom collapse of a tubular neighbourhood, in the metric-free model.**  A
continuous map `S^N = ℝ^N ∪ {∞} → ν⁺`, sending `∞` to `∞`, which off the open tube is the constant
`∞` and on the open tube is the radial blow-up of the normal foot.  This is the map composed with
the Gauss/classifying map of the Grassmann chapter to produce the Pontryagin–Thom class `α_V`. -/
theorem collapseToOnePoint {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε) (q : NormalSphSub E ε)
    (hU : IsCompact C.U) :
    Nonempty { g : C(OnePoint (Euc (8 + k)), OnePoint (NormalTotal E)) //
      (∀ y, y ∈ C.openTube → g (OnePoint.some y) = OnePoint.some (normalBlowUp E ε (C.inv y))) ∧
      (∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty) ∧
      g OnePoint.infty = OnePoint.infty } := by
  set Φ : NormalThomSpace E ε ≃ₜ OnePoint (NormalTotal E) :=
    normalThomToOnePointHomeo E C.eps_pos q with hΦdef
  have hΦeq : (Φ : NormalThomSpace E ε → OnePoint (NormalTotal E))
      = normalThomToOnePoint E ε := by
    funext x
    rw [hΦdef]
    exact normalThomToOnePointHomeo_apply E C.eps_pos q x
  refine ⟨⟨fun x => Φ (tubeCollapseOnePoint C q hU x),
    Φ.continuous.comp (tubeCollapseOnePoint C q hU).continuous⟩, ?_, ?_, ?_⟩
  · intro y hy
    have hyU : y ∈ C.U := C.openTube_subset_U hy
    show Φ (tubeCollapseOnePoint C q hU (OnePoint.some y))
      = OnePoint.some (normalBlowUp E ε (C.inv y))
    rw [tubeCollapseOnePoint_coe, tubeCollapse_of_mem C q hyU, hΦeq, normalThomToOnePoint_mk]
    rw [normalDiscToOnePoint_of_lt E ε (q := ⟨C.inv y, C.inv_mem y hyU⟩)
      (C.normalNorm_inv_lt hy)]
  · intro y hy
    show Φ (tubeCollapseOnePoint C q hU (OnePoint.some y)) = OnePoint.infty
    rw [tubeCollapseOnePoint_coe, tubeCollapse_eq_basepoint_of_notMem_openTube C q hy, hΦeq,
      normalThomBasepoint, normalThomToOnePoint_mk]
    exact normalDiscToOnePoint_of_eq E ε q.2
  · show Φ (tubeCollapseOnePoint C q hU OnePoint.infty) = OnePoint.infty
    rw [tubeCollapseOnePoint_infty, hΦeq, normalThomBasepoint, normalThomToOnePoint_mk]
    exact normalDiscToOnePoint_of_eq E ε q.2

end

end Work.Tubular
