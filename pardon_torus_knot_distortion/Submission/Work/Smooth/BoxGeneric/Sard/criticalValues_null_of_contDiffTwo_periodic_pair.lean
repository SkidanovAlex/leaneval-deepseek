import Mathlib
import Submission.Work.Smooth.BoxGeneric.Sard.criticalValues_null_of_contDiffTwo_periodic
import Submission.Work.Smooth.BoxGeneric.Sard.exists_isOpen_volume_image_restrictedCritical_null
import Submission.Work.Smooth.BoxGeneric.Sard.Reduce

/-!
# Two-dimensional Sard for periodic `C²` self-maps of the plane

The critical values of a `C²` map `G : ℝ × ℝ → ℝ × ℝ`, i.e. the Lebesgue measure of

`{v | ∃ p, G p = v ∧ ¬ (fderiv ℝ G p).IsInvertible}`,

is zero.  The periodicity hypotheses are not used (they only record the intended setting, exactly
as in the sibling `criticalValues_null_of_contDiffTwo_periodic`).

## Proof

Write `G = (G₁, G₂)` and `S = {p | ¬(fderiv ℝ G p).IsInvertible}` for the critical set.  Split

`S ⊆ S₀ ∪ T₁ ∪ T₂`,   `S₀ = {fderiv ℝ G p = 0}`,
`T₁ = {fderiv ℝ G₁ p ≠ 0 ∧ ∃ a, fderiv ℝ G₂ p = a • fderiv ℝ G₁ p}`,
`T₂ = {fderiv ℝ G₂ p ≠ 0 ∧ ∃ a, fderiv ℝ G₁ p = a • fderiv ℝ G₂ p}`.

* If `fderiv ℝ G p = 0` this is clear.  Otherwise the differential is a nonzero endomorphism of
  `ℝ × ℝ` that is not invertible; hence it is not surjective and by
  `Submodule.exists_le_ker_of_lt_top` there is a nonzero functional vanishing on its range.  This
  forces the two rows of the differential to be proportional, which is exactly `T₁ ∪ T₂`.
* `S₀` is closed.  A section of `G '' S₀` over the first coordinate is contained in the critical
  values `{u | ∃ p, G₂ p = u ∧ fderiv ℝ G₂ p = 0}` of the *scalar* `C²` function `G₂` (periodic
  because `G` is), which is null by the sibling `criticalValues_null_of_contDiffTwo_periodic`.
  Fubini (product measure `volume = volume.prod volume`) turns nullity of all sections into
  nullity of the image.
* For `T₁`: `T₁ = {fderiv ℝ G₁ p ≠ 0} ∩ {det of the two rows` `= 0}`, an `F_σ` set, so
  `G '' T₁` is `F_σ` (countable union of continuous images of compacta), in particular measurable.
  Its section over `u` is null because on the level curve `{G₁ = u}` the points of `T₁` are exactly
  the critical points of the restriction of `G₂` to that curve: Sard in dimension one, in the form
  of the sibling `exists_isOpen_volume_image_restrictedCritical_null`, applied at each point of the
  section, together with a Lindelöf cover, gives nullity of the section.  Fubini concludes.
  `T₂` is symmetric, using sections over the second coordinate.
-/

namespace Work.Smooth.BoxGeneric.Sard

noncomputable section

open MeasureTheory Set
open Filter
open scoped Topology

/-! ## Elementary linear algebra on `ℝ × ℝ` -/

/-- The value of a functional on `ℝ × ℝ` in terms of the standard basis. -/
private lemma clm_apply_eq_coord {T : (ℝ × ℝ) →L[ℝ] ℝ} (v : ℝ × ℝ) :
    T v = v.1 * T ((1 : ℝ), 0) + v.2 * T ((0 : ℝ), 1) := by
  have hv : v.1 • ((1 : ℝ), 0) + v.2 • ((0 : ℝ), 1) = v := by ext <;> simp
  calc T v = T (v.1 • ((1 : ℝ), 0) + v.2 • ((0 : ℝ), 1)) := by rw [hv]
    _ = v.1 * T ((1 : ℝ), 0) + v.2 * T ((0 : ℝ), 1) := by
        rw [map_add, map_smul, map_smul]; simp [smul_eq_mul]

/-- An endomorphism of `ℝ × ℝ` that is injective is invertible (the space is finite dimensional,
and every linear map on it is continuous). -/
private lemma isInvertible_of_injective {T : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)}
    (h : Function.Injective T) : T.IsInvertible := by
  let e : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) := LinearEquiv.ofInjectiveEndo T.toLinearMap h
  have he : ⇑e = T := LinearEquiv.coe_ofInjectiveEndo T.toLinearMap h
  refine ⟨e.toContinuousLinearEquiv, ContinuousLinearMap.ext ?_⟩
  intro x
  simpa [he] using congrFun he x

/-- An endomorphism of `ℝ × ℝ` that is surjective is invertible. -/
private lemma isInvertible_of_surjective {T : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)}
    (h : Function.Surjective T) : T.IsInvertible :=
  isInvertible_of_injective (LinearMap.injective_iff_surjective.mpr h)

/-- At a point where the differential `T` of a map is not invertible and whose **first row**
`fst ∘ T` does not vanish, the second row is a multiple of the first. -/
private lemma exists_smul_snd_of_not_isInvertible {T : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)}
    (hT : ¬ T.IsInvertible) (h1 : ContinuousLinearMap.fst ℝ ℝ ℝ ∘L T ≠ 0) :
    ∃ a : ℝ, ContinuousLinearMap.snd ℝ ℝ ℝ ∘L T = a • (ContinuousLinearMap.fst ℝ ℝ ℝ ∘L T) := by
  have hsurj : ¬ Function.Surjective T := fun hs => hT (isInvertible_of_surjective hs)
  have hrange : LinearMap.range T.toLinearMap < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hsurj
    intro y
    have : y ∈ LinearMap.range T.toLinearMap := by rw [htop]; trivial
    obtain ⟨x, hx⟩ := this
    exact ⟨x, hx⟩
  obtain ⟨L, hLne, hL⟩ :=
    Submodule.exists_le_ker_of_lt_top (LinearMap.range T.toLinearMap) hrange
  set α : ℝ := L ((1 : ℝ), 0) with hα
  set β : ℝ := L ((0 : ℝ), 1) with hβ
  have hLapply : ∀ v : ℝ × ℝ, L v = α * v.1 + β * v.2 := by
    rintro ⟨x, y⟩
    have hxy : ((x, y) : ℝ × ℝ) = x • ((1 : ℝ), 0) + y • ((0 : ℝ), 1) := by ext <;> simp
    calc L (x, y) = L (x • ((1 : ℝ), 0) + y • ((0 : ℝ), 1)) := by rw [hxy]
      _ = α * x + β * y := by rw [map_add, map_smul, map_smul, hα, hβ]; ring
  have hzero : ∀ v : ℝ × ℝ, L (T v) = 0 := fun v => hL (LinearMap.mem_range.mpr ⟨v, rfl⟩)
  have hcomb : ∀ v : ℝ × ℝ, α * ((ContinuousLinearMap.fst ℝ ℝ ℝ ∘L T) v)
      + β * ((ContinuousLinearMap.snd ℝ ℝ ℝ ∘L T) v) = 0 := by
    intro v
    have h := hzero v
    rw [hLapply (T v)] at h
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd'] using h
  by_cases hβ0 : β = 0
  · exfalso
    have hα0 : α ≠ 0 := by
      intro hαz
      apply hLne
      refine LinearMap.ext (fun v => ?_)
      rw [hLapply v, hαz, hβ0]
      simp
    have hfst0 : ContinuousLinearMap.fst ℝ ℝ ℝ ∘L T = 0 := by
      refine ContinuousLinearMap.ext (fun v => ?_)
      have h := hcomb v
      rw [hβ0] at h
      simp only [zero_mul, add_zero] at h
      simpa using (mul_eq_zero.mp h).resolve_left hα0
    exact h1 hfst0
  · refine ⟨-(α / β), ?_⟩
    refine ContinuousLinearMap.ext (fun v => ?_)
    have h := hcomb v
    have hβne : β ≠ 0 := hβ0
    have key : ((ContinuousLinearMap.snd ℝ ℝ ℝ ∘L T) v)
        = -(α * ((ContinuousLinearMap.fst ℝ ℝ ℝ ∘L T) v)) / β := by
      rw [eq_div_iff hβne]
      linarith
    rw [key, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring

/-- Symmetric form of `exists_smul_snd_of_not_isInvertible`: if the **second** row does not
vanish, then the first row is a multiple of the second. -/
private lemma exists_smul_fst_of_not_isInvertible {T : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)}
    (hT : ¬ T.IsInvertible) (h2 : ContinuousLinearMap.snd ℝ ℝ ℝ ∘L T ≠ 0) :
    ∃ a : ℝ, ContinuousLinearMap.fst ℝ ℝ ℝ ∘L T = a • (ContinuousLinearMap.snd ℝ ℝ ℝ ∘L T) := by
  set P : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) with hP
  have hcomp1 : ContinuousLinearMap.fst ℝ ℝ ℝ ∘L (P ∘L T)
      = ContinuousLinearMap.snd ℝ ℝ ℝ ∘L T := by
    refine ContinuousLinearMap.ext (fun v => ?_)
    simp [P, ContinuousLinearEquiv.prodComm]
  have hcomp2 : ContinuousLinearMap.snd ℝ ℝ ℝ ∘L (P ∘L T)
      = ContinuousLinearMap.fst ℝ ℝ ℝ ∘L T := by
    refine ContinuousLinearMap.ext (fun v => ?_)
    simp [P, ContinuousLinearEquiv.prodComm]
  have hPT : ¬ (P ∘L T).IsInvertible := by
    rw [ContinuousLinearMap.isInvertible_equiv_comp]
    exact hT
  have h1 : ContinuousLinearMap.fst ℝ ℝ ℝ ∘L (P ∘L T) ≠ 0 := by
    rw [hcomp1]; exact h2
  obtain ⟨a, ha⟩ := exists_smul_snd_of_not_isInvertible hPT h1
  refine ⟨a, ?_⟩
  rw [← hcomp2, ha, hcomp1]

/-- The `2 × 2` determinant of the two coordinate functionals of an endomorphism of `ℝ × ℝ`. -/
private def detF (f g : (ℝ × ℝ) →L[ℝ] ℝ) : ℝ :=
  f ((1 : ℝ), 0) * g ((0 : ℝ), 1) - f ((0 : ℝ), 1) * g ((1 : ℝ), 0)

private lemma detF_smul {f g : (ℝ × ℝ) →L[ℝ] ℝ} {a : ℝ} (h : g = a • f) : detF f g = 0 := by
  rw [h, detF]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- Two functionals on `ℝ × ℝ` with vanishing determinant, the first one nonzero, are
proportional. -/
private lemma exists_smul_of_detF_eq_zero {f g : (ℝ × ℝ) →L[ℝ] ℝ} (hf : f ≠ 0)
    (h : detF f g = 0) : ∃ a : ℝ, g = a • f := by
  have hrel : f ((1 : ℝ), 0) * g ((0 : ℝ), 1) = f ((0 : ℝ), 1) * g ((1 : ℝ), 0) := by
    have := h; rw [detF] at this; linarith
  rcases eq_or_ne (f ((1 : ℝ), 0)) 0 with hp | hp
  · have hq : f ((0 : ℝ), 1) ≠ 0 := by
      intro hq
      apply hf
      refine ContinuousLinearMap.ext (fun v => ?_)
      rw [clm_apply_eq_coord (T := f) v, hp, hq, ContinuousLinearMap.zero_apply]
      ring
    have hg10 : g ((1 : ℝ), 0) = 0 := by
      have hh := hrel
      rw [hp, zero_mul] at hh
      exact (mul_eq_zero.mp hh.symm).resolve_left hq
    refine ⟨g ((0 : ℝ), 1) / f ((0 : ℝ), 1), ContinuousLinearMap.ext (fun v => ?_)⟩
    have h1 : g ((1 : ℝ), 0) = (g ((0 : ℝ), 1) / f ((0 : ℝ), 1)) * f ((1 : ℝ), 0) := by
      rw [hg10, hp, mul_zero]
    have h2 : g ((0 : ℝ), 1) = (g ((0 : ℝ), 1) / f ((0 : ℝ), 1)) * f ((0 : ℝ), 1) := by
      field_simp
    rw [clm_apply_eq_coord (T := g) v, ContinuousLinearMap.smul_apply, smul_eq_mul,
      clm_apply_eq_coord (T := f) v, h1, h2]
    field_simp
  · refine ⟨g ((1 : ℝ), 0) / f ((1 : ℝ), 0), ContinuousLinearMap.ext (fun v => ?_)⟩
    have h2 : g ((0 : ℝ), 1) = (g ((1 : ℝ), 0) / f ((1 : ℝ), 0)) * f ((0 : ℝ), 1) := by
      field_simp
      linarith [hrel]
    have h1 : g ((1 : ℝ), 0) = (g ((1 : ℝ), 0) / f ((1 : ℝ), 0)) * f ((1 : ℝ), 0) := by
      field_simp
    rw [clm_apply_eq_coord (T := g) v, ContinuousLinearMap.smul_apply, smul_eq_mul,
      clm_apply_eq_coord (T := f) v, h1, h2]
    field_simp

/-! ## Two Fubini lemmas -/

/-- A measurable subset of `ℝ × ℝ` all of whose vertical sections are null is null. -/
private lemma volume_eq_zero_of_forall_section_eq_zero {E : Set (ℝ × ℝ)} (hE : MeasurableSet E)
    (h : ∀ u : ℝ, volume (Prod.mk u ⁻¹' E) = 0) : volume E = 0 := by
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod (volume : Measure ℝ) from rfl,
    MeasureTheory.Measure.prod_apply hE]
  simp [h]

/-- A measurable subset of `ℝ × ℝ` all of whose horizontal sections are null is null. -/
private lemma volume_eq_zero_of_forall_section_eq_zero' {E : Set (ℝ × ℝ)} (hE : MeasurableSet E)
    (h : ∀ u : ℝ, volume ((fun x : ℝ => (x, u)) ⁻¹' E) = 0) : volume E = 0 := by
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod (volume : Measure ℝ) from rfl,
    MeasureTheory.Measure.prod_apply_symm hE]
  simp [h]

/-- The image of a closed set under a continuous map is measurable. -/
private lemma measurableSet_image_of_isClosed {f : ℝ × ℝ → ℝ × ℝ} (hf : Continuous f)
    {s : Set (ℝ × ℝ)} (hs : IsClosed s) : MeasurableSet (f '' s) := by
  have hcover : s = ⋃ n : ℕ, s ∩ Metric.closedBall (0 : ℝ × ℝ) (n : ℝ) :=
    (Metric.iUnion_inter_closedBall_nat s (0 : ℝ × ℝ)).symm
  rw [hcover, Set.image_iUnion]
  refine MeasurableSet.iUnion (fun (n : ℕ) => ?_)
  rw [Set.inter_comm]
  exact ((isCompact_closedBall (0 : ℝ × ℝ) (n : ℝ)).inter_right hs).image hf |>.measurableSet

/-- The image of a countable union of closed sets under a continuous map is measurable. -/
private lemma measurableSet_image_iUnion_isClosed {f : ℝ × ℝ → ℝ × ℝ} (hf : Continuous f)
    {s : ℕ → Set (ℝ × ℝ)} (hs : ∀ n, IsClosed (s n)) :
    MeasurableSet (f '' (⋃ n, s n)) := by
  rw [Set.image_iUnion]
  refine MeasurableSet.iUnion (fun n => ?_)
  have heq : f '' s n = ⋃ m : ℕ, f '' (Metric.closedBall (0 : ℝ × ℝ) (m : ℝ) ∩ s n) := by
    rw [← Set.image_iUnion]
    congr 1
    rw [← Set.iUnion_inter]
    simp only [Metric.iUnion_closedBall_nat, Set.univ_inter]
  rw [heq]
  exact MeasurableSet.iUnion (fun (m : ℕ) =>
    ((isCompact_closedBall (0 : ℝ × ℝ) (m : ℝ)).inter_right (hs n)).image hf |>.measurableSet)

/-! ## Sections of the restricted critical set are null -/

/-- For `C¹` maps `F H : ℝ × ℝ → ℝ` and a level `u`, the set of values `F q` over the points `q`
of the level curve `{H = u}` at which the derivative of `H` does not vanish and the differentials
of `F` and `H` are proportional is Lebesgue-null.  These are exactly the critical values of the
restriction of `F` to the curve `{H = u}`. -/
private lemma volume_section_eq_zero_of_restrictedCritical {F H : ℝ × ℝ → ℝ}
    (hF : ContDiff ℝ 1 F) (hH : ContDiff ℝ 1 H) (u : ℝ) :
    volume {v : ℝ | ∃ q : ℝ × ℝ, F q = v ∧ H q = u ∧ fderiv ℝ H q ≠ 0 ∧
        ∃ a : ℝ, fderiv ℝ F q = a • fderiv ℝ H q} = 0 := by
  classical
  set A : Set (ℝ × ℝ) := {q : ℝ × ℝ | H q = u ∧ fderiv ℝ H q ≠ 0 ∧
    ∃ a : ℝ, fderiv ℝ F q = a • fderiv ℝ H q} with hA
  have hmemA : ∀ q, q ∈ A ↔ H q = u ∧ fderiv ℝ H q ≠ 0 ∧
      ∃ a : ℝ, fderiv ℝ F q = a • fderiv ℝ H q := fun q => by simp [hA]
  have hderiv : ∀ q : ℝ × ℝ, fderiv ℝ (fun p : ℝ × ℝ => H p - u) q = fderiv ℝ H q := by
    intro q
    have h1 : (fun p : ℝ × ℝ => H p - u) = H - (Function.const (ℝ × ℝ) u) := rfl
    rw [h1, fderiv_sub, fderiv_const]
    · simp
    · exact (hH.differentiable (by norm_num : (1 : WithTop ℕ∞) ≠ 0)).differentiableAt
    · exact differentiableAt_const u
  have hset : {v : ℝ | ∃ q : ℝ × ℝ, F q = v ∧ H q = u ∧ fderiv ℝ H q ≠ 0 ∧
      ∃ a : ℝ, fderiv ℝ F q = a • fderiv ℝ H q} = F '' A := by
    ext v; constructor
    · rintro ⟨q, h1, h2, h3, h4⟩; exact ⟨q, (hmemA q).mpr ⟨h2, h3, h4⟩, h1⟩
    · rintro ⟨q, hq, h1⟩; exact ⟨q, h1, (hmemA q).mp hq⟩
  rw [hset]
  have hpt : ∀ p ∈ A, ∃ U : Set (ℝ × ℝ), IsOpen U ∧ p ∈ U ∧
      volume (F '' ({q : ℝ × ℝ | (fun p : ℝ × ℝ => H p - u) q = 0 ∧
        ∃ a : ℝ, fderiv ℝ F q = a • fderiv ℝ (fun p : ℝ × ℝ => H p - u) q} ∩ U)) = 0 := by
    intro p hp
    have hcd : ContDiff ℝ 1 (fun p : ℝ × ℝ => H p - u) := hH.sub contDiff_const
    have hp0 : (fun p : ℝ × ℝ => H p - u) p = 0 := by
      simp [((hmemA p).mp hp).1]
    have hg : fderiv ℝ (fun p : ℝ × ℝ => H p - u) p ≠ 0 := by
      rw [hderiv p]; exact ((hmemA p).mp hp).2.1
    exact exists_isOpen_volume_image_restrictedCritical_null hF hcd hp0 hg
  let U : ℝ × ℝ → Set (ℝ × ℝ) := fun p => if h : p ∈ A then (hpt p h).choose else ∅
  have hU : ∀ p : ℝ × ℝ, ∀ hp : p ∈ A, IsOpen (U p) ∧ p ∈ U p ∧
      volume (F '' ({q : ℝ × ℝ | (fun p : ℝ × ℝ => H p - u) q = 0 ∧
        ∃ a : ℝ, fderiv ℝ F q = a • fderiv ℝ (fun p : ℝ × ℝ => H p - u) q} ∩ U p)) = 0 := by
    intro p hp
    simp only [U, dif_pos hp]
    exact (hpt p hp).choose_spec
  have hnhd : ∀ p ∈ A, U p ∈ nhds p := fun p hp => (hU p hp).1.mem_nhds (hU p hp).2.1
  obtain ⟨t, htc, htsub, hcover⟩ :=
    (HereditarilyLindelofSpace.isLindelof A).elim_nhds_subcover U hnhd
  have hsub : F '' A ⊆ ⋃ p ∈ t, F '' ({q : ℝ × ℝ | (fun p : ℝ × ℝ => H p - u) q = 0 ∧
      ∃ a : ℝ, fderiv ℝ F q = a • fderiv ℝ (fun p : ℝ × ℝ => H p - u) q} ∩ U p) := by
    rintro v ⟨q, hqA, rfl⟩
    have hq' : q ∈ ⋃ p ∈ t, U p := hcover hqA
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hq'
    obtain ⟨hxt, hxq⟩ := Set.mem_iUnion.mp hx
    refine Set.mem_biUnion hxt ⟨q, ⟨⟨?_, ?_⟩, hxq⟩, rfl⟩
    · show H q - u = 0
      rw [((hmemA q).mp hqA).1]
      simp
    · obtain ⟨a, ha⟩ := ((hmemA q).mp hqA).2.2
      exact ⟨a, by rw [hderiv q]; exact ha⟩
  refine le_antisymm (le_trans (MeasureTheory.measure_mono hsub) (le_of_eq ?_)) bot_le
  rw [MeasureTheory.measure_biUnion_null_iff htc]
  intro x hx
  exact (hU x (htsub x hx)).2.2

/-! ## The main theorem -/

theorem criticalValues_null_of_contDiffTwo_periodic_pair {G : ℝ × ℝ → ℝ × ℝ}
    (hG : ContDiff ℝ 2 G)
    (hper₁ : ∀ p : ℝ × ℝ, G (p.1 + 2 * Real.pi, p.2) = G p)
    (hper₂ : ∀ p : ℝ × ℝ, G (p.1, p.2 + 2 * Real.pi) = G p) :
    MeasureTheory.volume {v : ℝ × ℝ | ∃ p : ℝ × ℝ, G p = v ∧ ¬ (fderiv ℝ G p).IsInvertible} = 0 := by
  -- ### The two components of `G` and their derivatives
  set G₁ : ℝ × ℝ → ℝ := fun p => (G p).1 with hG₁
  set G₂ : ℝ × ℝ → ℝ := fun p => (G p).2 with hG₂
  have hG₁cd : ContDiff ℝ 2 G₁ := by
    rw [hG₁]; exact (ContinuousLinearMap.fst ℝ ℝ ℝ).contDiff.comp hG
  have hG₂cd : ContDiff ℝ 2 G₂ := by
    rw [hG₂]; exact (ContinuousLinearMap.snd ℝ ℝ ℝ).contDiff.comp hG
  have hG₁c1 : ContDiff ℝ 1 G₁ := hG₁cd.of_le (by norm_num)
  have hG₂c1 : ContDiff ℝ 1 G₂ := hG₂cd.of_le (by norm_num)
  have hGcont : Continuous G := hG.continuous
  have hGdiff : ∀ p : ℝ × ℝ, DifferentiableAt ℝ G p := fun p =>
    (hG.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).differentiableAt
  have hfd₁ : ∀ p : ℝ × ℝ, fderiv ℝ G₁ p = ContinuousLinearMap.fst ℝ ℝ ℝ ∘L fderiv ℝ G p := by
    intro p; rw [hG₁]
    exact (hGdiff p).hasFDerivAt.fst.fderiv
  have hfd₂ : ∀ p : ℝ × ℝ, fderiv ℝ G₂ p = ContinuousLinearMap.snd ℝ ℝ ℝ ∘L fderiv ℝ G p := by
    intro p; rw [hG₂]
    exact (hGdiff p).hasFDerivAt.snd.fderiv
  have hfd₁cont : Continuous (fderiv ℝ G₁) := hG₁c1.continuous_fderiv (by norm_num)
  have hfd₂cont : Continuous (fderiv ℝ G₂) := hG₂c1.continuous_fderiv (by norm_num)
  -- the two components of the differential
  have hdecomp : ∀ (p v : ℝ × ℝ),
      (fderiv ℝ G p) v = ((fderiv ℝ G₁ p) v, (fderiv ℝ G₂ p) v) := by
    intro p v
    have e1 : ((fderiv ℝ G p) v).1 = (fderiv ℝ G₁ p) v := by rw [hfd₁ p]; rfl
    have e2 : ((fderiv ℝ G p) v).2 = (fderiv ℝ G₂ p) v := by rw [hfd₂ p]; rfl
    rw [← e1, ← e2]
  have hzero_of_comp : ∀ p : ℝ × ℝ, fderiv ℝ G₁ p = 0 → fderiv ℝ G₂ p = 0 →
      fderiv ℝ G p = 0 := by
    intro p h1 h2
    refine ContinuousLinearMap.ext (fun v => ?_)
    have hv := hdecomp p v
    rw [hv, ContinuousLinearMap.zero_apply]
    have : ((fderiv ℝ G₁ p) v, (fderiv ℝ G₂ p) v) = ((0 : ℝ × ℝ)) := by
      rw [h1, h2]; rfl
    simpa using this
  -- ### Sard in dimension one for the scalar function `G₂`
  have hsard₂ : volume {u : ℝ | ∃ p : ℝ × ℝ, G₂ p = u ∧ fderiv ℝ G₂ p = 0} = 0 :=
    criticalValues_null_of_contDiffTwo_periodic hG₂cd
      (fun p => by
        simp only [hG₂]
        exact congrArg Prod.snd (hper₁ p))
      (fun p => by
        simp only [hG₂]
        exact congrArg Prod.snd (hper₂ p))
  -- ### Decomposition of the critical set
  set S : Set (ℝ × ℝ) := {p | ¬ (fderiv ℝ G p).IsInvertible} with hS
  set S0 : Set (ℝ × ℝ) := {p | fderiv ℝ G p = 0} with hS0
  set T₁ : Set (ℝ × ℝ) := {p | fderiv ℝ G₁ p ≠ 0 ∧
    ∃ a : ℝ, fderiv ℝ G₂ p = a • fderiv ℝ G₁ p} with hT₁
  set T₂ : Set (ℝ × ℝ) := {p | fderiv ℝ G₂ p ≠ 0 ∧
    ∃ a : ℝ, fderiv ℝ G₁ p = a • fderiv ℝ G₂ p} with hT₂
  have hldep₁ : ∀ p : ℝ × ℝ, ¬ (fderiv ℝ G p).IsInvertible → fderiv ℝ G₁ p ≠ 0 →
      ∃ a : ℝ, fderiv ℝ G₂ p = a • fderiv ℝ G₁ p := by
    intro p hp h1
    have h1' : ContinuousLinearMap.fst ℝ ℝ ℝ ∘L fderiv ℝ G p ≠ 0 := by
      rw [← hfd₁ p]; exact h1
    obtain ⟨a, ha⟩ := exists_smul_snd_of_not_isInvertible hp h1'
    exact ⟨a, by rw [hfd₂ p, hfd₁ p]; exact ha⟩
  have hldep₂ : ∀ p : ℝ × ℝ, ¬ (fderiv ℝ G p).IsInvertible → fderiv ℝ G₂ p ≠ 0 →
      ∃ a : ℝ, fderiv ℝ G₁ p = a • fderiv ℝ G₂ p := by
    intro p hp h2
    have h2' : ContinuousLinearMap.snd ℝ ℝ ℝ ∘L fderiv ℝ G p ≠ 0 := by
      rw [← hfd₂ p]; exact h2
    obtain ⟨a, ha⟩ := exists_smul_fst_of_not_isInvertible hp h2'
    exact ⟨a, by rw [hfd₁ p, hfd₂ p]; exact ha⟩
  have hcover : S ⊆ S0 ∪ T₁ ∪ T₂ := by
    intro p hp
    have hp' : ¬ (fderiv ℝ G p).IsInvertible := by simpa [hS] using hp
    by_cases h0 : fderiv ℝ G p = 0
    · exact Or.inl (Or.inl (by simp [hS0, h0]))
    · rcases eq_or_ne (fderiv ℝ G₁ p) 0 with h1 | h1
      · have h2 : fderiv ℝ G₂ p ≠ 0 := fun h2 => h0 (hzero_of_comp p h1 h2)
        refine Or.inr ?_
        rw [hT₂]
        exact ⟨h2, hldep₂ p hp' h2⟩
      · refine Or.inl (Or.inr ?_)
        rw [hT₁]
        exact ⟨h1, hldep₁ p hp' h1⟩
  -- ### Nullity of the flat part `G '' S₀`
  have hS0closed : IsClosed S0 := by
    rw [hS0]
    have h1 : ContDiff ℝ 1 G := hG.of_le (by norm_num)
    exact isClosed_eq (h1.continuous_fderiv (by norm_num)) continuous_const
  have hS0null : volume (G '' S0) = 0 := by
    have hmeas : MeasurableSet (G '' S0) :=
      measurableSet_image_of_isClosed hGcont hS0closed
    refine volume_eq_zero_of_forall_section_eq_zero hmeas (fun u => ?_)
    refine measure_mono_null ?_ hsard₂
    rintro v hv
    obtain ⟨p, hpS0, hpv⟩ := hv
    have hp0 : fderiv ℝ G p = 0 := by simpa [hS0] using hpS0
    refine ⟨p, ?_, ?_⟩
    · show (G p).2 = v
      rw [hpv]
    · rw [hfd₂ p, hp0]
      refine ContinuousLinearMap.ext (fun v => ?_)
      simp
  -- ### The determinant detecting proportionality of the two rows
  have hJcont : Continuous (fun p : ℝ × ℝ => detF (fderiv ℝ G₁ p) (fderiv ℝ G₂ p)) := by
    have c1 : Continuous fun p : ℝ × ℝ => (fderiv ℝ G₁ p) ((1 : ℝ), 0) :=
      (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), 0)).continuous.comp hfd₁cont
    have c2 : Continuous fun p : ℝ × ℝ => (fderiv ℝ G₂ p) ((0 : ℝ), 1) :=
      (ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), 1)).continuous.comp hfd₂cont
    have c3 : Continuous fun p : ℝ × ℝ => (fderiv ℝ G₁ p) ((0 : ℝ), 1) :=
      (ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), 1)).continuous.comp hfd₁cont
    have c4 : Continuous fun p : ℝ × ℝ => (fderiv ℝ G₂ p) ((1 : ℝ), 0) :=
      (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), 0)).continuous.comp hfd₂cont
    exact (c1.mul c2).sub (c3.mul c4)
  have hJcont' : Continuous (fun p : ℝ × ℝ => detF (fderiv ℝ G₂ p) (fderiv ℝ G₁ p)) := by
    have c1 : Continuous fun p : ℝ × ℝ => (fderiv ℝ G₂ p) ((1 : ℝ), 0) :=
      (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), 0)).continuous.comp hfd₂cont
    have c2 : Continuous fun p : ℝ × ℝ => (fderiv ℝ G₁ p) ((0 : ℝ), 1) :=
      (ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), 1)).continuous.comp hfd₁cont
    have c3 : Continuous fun p : ℝ × ℝ => (fderiv ℝ G₂ p) ((0 : ℝ), 1) :=
      (ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), 1)).continuous.comp hfd₂cont
    have c4 : Continuous fun p : ℝ × ℝ => (fderiv ℝ G₁ p) ((1 : ℝ), 0) :=
      (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), 0)).continuous.comp hfd₁cont
    exact (c1.mul c2).sub (c3.mul c4)
  -- ### Nullity of `G '' T₁`
  have hT₁null : volume (G '' T₁) = 0 := by
    have hT₁eq : T₁ = {p : ℝ × ℝ | fderiv ℝ G₁ p ≠ 0} ∩
        {p : ℝ × ℝ | detF (fderiv ℝ G₁ p) (fderiv ℝ G₂ p) = 0} := by
      rw [hT₁]
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
      exact ⟨fun ⟨h1, a, ha⟩ => ⟨h1, detF_smul ha⟩,
        fun ⟨h1, h2⟩ => ⟨h1, exists_smul_of_detF_eq_zero h1 h2⟩⟩
    have hcl : ∀ n : ℕ, IsClosed ({p : ℝ × ℝ | (1 : ℝ) / ((n : ℝ) + 1) ≤ ‖fderiv ℝ G₁ p‖} ∩
        {p : ℝ × ℝ | detF (fderiv ℝ G₁ p) (fderiv ℝ G₂ p) = 0}) := fun n =>
      (isClosed_le continuous_const hfd₁cont.norm).inter
        (isClosed_eq hJcont continuous_const)
    have hT₁cov : T₁ = ⋃ n : ℕ, ({p : ℝ × ℝ | (1 : ℝ) / ((n : ℝ) + 1) ≤ ‖fderiv ℝ G₁ p‖} ∩
        {p : ℝ × ℝ | detF (fderiv ℝ G₁ p) (fderiv ℝ G₂ p) = 0}) := by
      rw [hT₁eq]
      ext p
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨h1, h2⟩
        have hL : 0 < ‖fderiv ℝ G₁ p‖ := norm_pos_iff.mpr h1
        obtain ⟨n, hn⟩ := exists_nat_ge (1 / ‖fderiv ℝ G₁ p‖)
        refine ⟨n, ?_, h2⟩
        have hn' : 1 ≤ (n : ℝ) * ‖fderiv ℝ G₁ p‖ := by
          have h := hn; rw [div_le_iff₀ hL] at h; linarith
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
        nlinarith [hn', norm_nonneg (fderiv ℝ G₁ p)]
      · rintro ⟨n, hn, h2⟩
        refine ⟨?_, h2⟩
        intro h0
        rw [h0] at hn
        simp only [norm_zero] at hn
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    have hmeas : MeasurableSet (G '' T₁) := by
      rw [hT₁cov]
      exact measurableSet_image_iUnion_isClosed hGcont hcl
    refine volume_eq_zero_of_forall_section_eq_zero hmeas (fun u => ?_)
    refine measure_mono_null ?_
      (volume_section_eq_zero_of_restrictedCritical hG₂c1 hG₁c1 u)
    rintro v hv
    obtain ⟨p, hpT₁, hpv⟩ := hv
    have hp : fderiv ℝ G₁ p ≠ 0 ∧ ∃ a : ℝ, fderiv ℝ G₂ p = a • fderiv ℝ G₁ p := by
      simpa [hT₁] using hpT₁
    exact ⟨p, by show (G p).2 = v; rw [hpv], by show (G p).1 = u; rw [hpv], hp.1, hp.2⟩
  -- ### Nullity of `G '' T₂`
  have hT₂null : volume (G '' T₂) = 0 := by
    have hT₂eq : T₂ = {p : ℝ × ℝ | fderiv ℝ G₂ p ≠ 0} ∩
        {p : ℝ × ℝ | detF (fderiv ℝ G₂ p) (fderiv ℝ G₁ p) = 0} := by
      rw [hT₂]
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
      exact ⟨fun ⟨h1, a, ha⟩ => ⟨h1, detF_smul ha⟩,
        fun ⟨h1, h2⟩ => ⟨h1, exists_smul_of_detF_eq_zero h1 h2⟩⟩
    have hcl : ∀ n : ℕ, IsClosed ({p : ℝ × ℝ | (1 : ℝ) / ((n : ℝ) + 1) ≤ ‖fderiv ℝ G₂ p‖} ∩
        {p : ℝ × ℝ | detF (fderiv ℝ G₂ p) (fderiv ℝ G₁ p) = 0}) := fun n =>
      (isClosed_le continuous_const hfd₂cont.norm).inter
        (isClosed_eq hJcont' continuous_const)
    have hT₂cov : T₂ = ⋃ n : ℕ, ({p : ℝ × ℝ | (1 : ℝ) / ((n : ℝ) + 1) ≤ ‖fderiv ℝ G₂ p‖} ∩
        {p : ℝ × ℝ | detF (fderiv ℝ G₂ p) (fderiv ℝ G₁ p) = 0}) := by
      rw [hT₂eq]
      ext p
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨h1, h2⟩
        have hL : 0 < ‖fderiv ℝ G₂ p‖ := norm_pos_iff.mpr h1
        obtain ⟨n, hn⟩ := exists_nat_ge (1 / ‖fderiv ℝ G₂ p‖)
        refine ⟨n, ?_, h2⟩
        have hn' : 1 ≤ (n : ℝ) * ‖fderiv ℝ G₂ p‖ := by
          have h := hn; rw [div_le_iff₀ hL] at h; linarith
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
        nlinarith [hn', norm_nonneg (fderiv ℝ G₂ p)]
      · rintro ⟨n, hn, h2⟩
        refine ⟨?_, h2⟩
        intro h0
        rw [h0] at hn
        simp only [norm_zero] at hn
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    have hmeas : MeasurableSet (G '' T₂) := by
      rw [hT₂cov]
      exact measurableSet_image_iUnion_isClosed hGcont hcl
    refine volume_eq_zero_of_forall_section_eq_zero' hmeas (fun u => ?_)
    refine measure_mono_null ?_
      (volume_section_eq_zero_of_restrictedCritical hG₁c1 hG₂c1 u)
    rintro v hv
    obtain ⟨p, hpT₂, hpv⟩ := hv
    have hp : fderiv ℝ G₂ p ≠ 0 ∧ ∃ a : ℝ, fderiv ℝ G₁ p = a • fderiv ℝ G₂ p := by
      simpa [hT₂] using hpT₂
    exact ⟨p, by show (G p).1 = v; rw [hpv], by show (G p).2 = u; rw [hpv], hp.1, hp.2⟩
  -- ### Conclusion
  have htarget : {v : ℝ × ℝ | ∃ p : ℝ × ℝ, G p = v ∧ ¬ (fderiv ℝ G p).IsInvertible} = G '' S := by
    ext v; constructor
    · rintro ⟨p, hp, h⟩; exact ⟨p, by simpa [hS] using h, hp⟩
    · rintro ⟨p, hp, rfl⟩; exact ⟨p, rfl, by simpa [hS] using hp⟩
  rw [htarget]
  have hsub : G '' S ⊆ G '' S0 ∪ G '' T₁ ∪ G '' T₂ := by
    rintro v ⟨p, hp, rfl⟩
    rcases hcover hp with (h | h) | h
    · exact Or.inl (Or.inl ⟨p, h, rfl⟩)
    · exact Or.inl (Or.inr ⟨p, h, rfl⟩)
    · exact Or.inr ⟨p, h, rfl⟩
  refine le_antisymm ?_ bot_le
  calc volume (G '' S) ≤ volume (G '' S0 ∪ G '' T₁ ∪ G '' T₂) := measure_mono hsub
    _ ≤ volume (G '' S0) + volume (G '' T₁) + volume (G '' T₂) := by
        refine le_trans (MeasureTheory.measure_union_le _ _) ?_
        gcongr
        exact MeasureTheory.measure_union_le _ _
    _ = 0 := by simp [hS0null, hT₁null, hT₂null]

end

end Work.Smooth.BoxGeneric.Sard
