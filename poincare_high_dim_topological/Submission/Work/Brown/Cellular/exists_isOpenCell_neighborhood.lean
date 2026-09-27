import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.Brown.Cell.exists_homeomorph_image_compact_subset_open
import Submission.Work.Brown.Cell.isOpenCell_compl_point_sphere

/-!
# A closed set whose complement is an open cell has an open cell neighbourhood

Let `K ⊆ 𝕊ⁿ` be closed and suppose its complement is an open `n`-cell (homeomorphic to `ℝⁿ`).
Then for every open neighbourhood `U` of `K` there is an open set `W` with `K ⊆ W ⊆ U` which
is again homeomorphic to `ℝⁿ`.

The proof is a "pinch" construction.  Writing `h : 𝕊ⁿ ∖ K ≃ₜ ℝⁿ` and `φ := (h.symm ·)` for
the chart map `ℝⁿ → 𝕊ⁿ` (an open embedding onto `Kᶜ`), the radial squeeze
`σ : ℝⁿ → ℝⁿ`, `σ y = (ψ ‖y‖ / ‖y‖) • y` with `ψ` the piecewise linear map that is `0` on
`[0, S]` and the identity on `[S + 1, ∞)`, collapses the flat ball `φ '' closedBall 0 S` to the
single point `φ 0`.  Pasted with the identity off that ball it gives a continuous surjection
`ρ : 𝕊ⁿ → 𝕊ⁿ` whose only non-trivial fibre is `φ '' closedBall 0 S`; as `𝕊ⁿ` is compact and
Hausdorff, `ρ` induces a homeomorphism `𝕊ⁿ / (φ '' closedBall 0 S) ≅ 𝕊ⁿ`, and restricting `ρ`
to the complement of its non-trivial fibre exhibits `(φ '' closedBall 0 S)ᶜ ≅ 𝕊ⁿ ∖ {φ 0} ≅ ℝⁿ`.
Choosing `S` large enough that `𝕊ⁿ ∖ U ⊆ φ '' closedBall 0 S` finishes the argument.
-/

namespace Work.Brown.Cellular

open Metric Set

/-- `𝕊ⁿ`, the unit sphere of `ℝⁿ⁺¹`, as a type. -/
abbrev Sph (n : ℕ) : Type := ↥(Metric.sphere (0 : PL.E (n + 1)) 1)

/-! ## The scalar pinch `pinchPsi` -/

/-- The scalar pinch: `0` on `(-∞, S]`, the identity on `[S + 1, ∞)` and linear in between. -/
noncomputable def pinchPsi (S : ℝ) : ℝ → ℝ := fun t => max 0 (min ((t - S) * (S + 1)) t)

lemma pinchPsi_continuous (S : ℝ) : Continuous (pinchPsi S) := by
  unfold pinchPsi; fun_prop

lemma pinchPsi_nonneg (S t : ℝ) : 0 ≤ pinchPsi S t := le_max_left _ _

lemma pinchPsi_zero (S : ℝ) : pinchPsi S 0 = 0 := by
  unfold pinchPsi
  rw [max_eq_left_iff]
  exact min_le_right _ _

lemma pinchPsi_eq_zero_iff {S : ℝ} (hS : 0 ≤ S) (t : ℝ) : pinchPsi S t = 0 ↔ t ≤ S := by
  unfold pinchPsi
  rw [max_eq_left_iff, min_le_iff]
  constructor
  · rintro (h | h)
    · have h2 : (0:ℝ) < S + 1 := by linarith
      nlinarith
    · linarith
  · intro h
    exact Or.inl (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))

lemma pinchPsi_of_mem_Ioc {S : ℝ} (hS : 0 ≤ S) {t : ℝ} (h1 : S ≤ t) (h2 : t ≤ S + 1) :
    pinchPsi S t = (t - S) * (S + 1) := by
  unfold pinchPsi
  rw [min_eq_left (by nlinarith : (t - S) * (S + 1) ≤ t),
      max_eq_right (by nlinarith : (0:ℝ) ≤ (t - S) * (S + 1))]

lemma pinchPsi_of_ge {S : ℝ} (hS : 0 ≤ S) {t : ℝ} (ht : S + 1 ≤ t) : pinchPsi S t = t := by
  unfold pinchPsi
  rw [min_eq_right (by nlinarith : t ≤ (t - S) * (S + 1)),
      max_eq_right (by linarith : (0:ℝ) ≤ t)]

lemma pinchPsi_pos {S : ℝ} (hS : 0 ≤ S) {t : ℝ} (ht : S < t) : 0 < pinchPsi S t := by
  rcases lt_or_ge t (S + 1) with h | h
  · rw [pinchPsi_of_mem_Ioc hS (le_of_lt ht) (le_of_lt h)]
    nlinarith
  · rw [pinchPsi_of_ge hS h]; linarith

lemma pinchPsi_injOn {S : ℝ} (hS : 0 ≤ S) : Set.InjOn (pinchPsi S) (Ioi S) := by
  intro t ht t' ht' h
  rw [mem_Ioi] at ht ht'
  by_cases h1 : t ≤ S + 1
  · rw [pinchPsi_of_mem_Ioc hS (le_of_lt ht) h1] at h
    by_cases h2 : t' ≤ S + 1
    · rw [pinchPsi_of_mem_Ioc hS (le_of_lt ht') h2] at h; nlinarith
    · rw [pinchPsi_of_ge hS (le_of_lt (not_le.mp h2))] at h
      exfalso; nlinarith
  · rw [pinchPsi_of_ge hS (le_of_lt (not_le.mp h1))] at h
    by_cases h2 : t' ≤ S + 1
    · rw [pinchPsi_of_mem_Ioc hS (le_of_lt ht') h2] at h
      exfalso; nlinarith
    · rw [pinchPsi_of_ge hS (le_of_lt (not_le.mp h2))] at h; exact h

lemma pinchPsi_surjOn {S : ℝ} (hS : 0 ≤ S) :
    ∀ r : ℝ, 0 ≤ r → ∃ t : ℝ, 0 ≤ t ∧ pinchPsi S t = r := by
  intro r hr
  by_cases h : r ≤ S + 1
  · have hSp : (0:ℝ) < S + 1 := by linarith
    have hrdiv : 0 ≤ r / (S + 1) := div_nonneg hr (le_of_lt hSp)
    refine ⟨S + r / (S + 1), by linarith, ?_⟩
    have hle : S + r / (S + 1) ≤ S + 1 := by
      rw [add_le_add_iff_left, div_le_one hSp]; exact h
    rw [pinchPsi_of_mem_Ioc hS (by linarith) hle]
    field_simp
    ring
  · exact ⟨r, by linarith, pinchPsi_of_ge hS (le_of_lt (not_le.mp h))⟩

/-! ## The radial pinch `pinchMap` of `ℝⁿ` -/

/-- The radial pinch of `ℝⁿ`: it collapses the closed ball of radius `S` to the origin, is the
identity outside the closed ball of radius `S + 1`, and is a radial homeomorphism in between. -/
noncomputable def pinchMap {n : ℕ} (S : ℝ) (y : PL.E n) : PL.E n :=
  (pinchPsi S ‖y‖ / ‖y‖) • y

lemma continuous_pinchMap {n : ℕ} (S : ℝ) : Continuous (pinchMap (n := n) S) :=
  Work.Brown.Cell.continuous_radial (pinchPsi_continuous S) (pinchPsi_zero S)

lemma norm_pinchMap {n : ℕ} (S : ℝ) (y : PL.E n) : ‖pinchMap S y‖ = pinchPsi S ‖y‖ := by
  rw [pinchMap, Work.Brown.Cell.norm_radial (pinchPsi_zero S) y,
    abs_of_nonneg (pinchPsi_nonneg _ _)]

lemma pinchMap_eq_zero_iff {n : ℕ} {S : ℝ} (hS : 0 ≤ S) (y : PL.E n) :
    pinchMap S y = 0 ↔ ‖y‖ ≤ S := by
  constructor
  · intro h
    have := congrArg norm h
    rw [norm_pinchMap, norm_zero] at this
    exact (pinchPsi_eq_zero_iff hS _).mp this
  · intro h
    rw [pinchMap, (pinchPsi_eq_zero_iff hS _).mpr h]
    simp

lemma pinchMap_self {n : ℕ} {S : ℝ} (hS : 0 ≤ S) {y : PL.E n} (h : S + 1 ≤ ‖y‖) :
    pinchMap S y = y := by
  have hy : ‖y‖ ≠ 0 := by
    have h0 : (0:ℝ) < S + 1 := by linarith
    exact ne_of_gt (by linarith)
  rw [pinchMap, pinchPsi_of_ge hS h, div_self hy, one_smul]

lemma pinchMap_injOn {n : ℕ} {S : ℝ} (hS : 0 ≤ S) :
    Set.InjOn (pinchMap (n := n) S) {y | S < ‖y‖} := by
  intro y hy y' hy' h
  rw [mem_setOf] at hy hy'
  have hn : ‖y‖ = ‖y'‖ := by
    have h2 : ‖pinchMap S y‖ = ‖pinchMap S y'‖ := by rw [h]
    rw [norm_pinchMap, norm_pinchMap] at h2
    exact pinchPsi_injOn hS hy hy' h2
  have hnpos : (0:ℝ) < ‖y‖ := by linarith
  have hc : pinchPsi S ‖y‖ / ‖y‖ ≠ 0 :=
    div_ne_zero (ne_of_gt (pinchPsi_pos hS hy)) (ne_of_gt hnpos)
  have h' : (pinchPsi S ‖y‖ / ‖y‖) • y = (pinchPsi S ‖y‖ / ‖y‖) • y' := by
    have h3 := h
    rw [pinchMap, pinchMap, hn.symm] at h3
    exact h3
  have h2 := congrArg (fun w => (pinchPsi S ‖y‖ / ‖y‖)⁻¹ • w) h'
  simpa only [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ hc, one_smul] using h2

lemma pinchMap_surjective {n : ℕ} {S : ℝ} (hS : 0 ≤ S) :
    Function.Surjective (pinchMap (n := n) S) := by
  intro z
  rcases eq_or_ne z 0 with rfl | hz
  · exact ⟨0, by simp [pinchMap, pinchPsi_zero]⟩
  · have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    obtain ⟨t, ht0, ht⟩ := pinchPsi_surjOn hS ‖z‖ (le_of_lt hzpos)
    have htpos : 0 < t := by
      by_contra h; push_neg at h
      rw [le_antisymm h ht0, pinchPsi_zero] at ht
      linarith
    refine ⟨(t / ‖z‖) • z, ?_⟩
    have hnorm : ‖(t / ‖z‖) • z‖ = t := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
        div_mul_cancel₀ _ (ne_of_gt hzpos)]
    rw [pinchMap, hnorm, ht, smul_smul,
      show ‖z‖ / t * (t / ‖z‖) = 1 by field_simp, one_smul]

/-! ## The chart map `φ` and the pinch of `𝕊ⁿ` -/

/-- The chart map `φ : ℝⁿ → 𝕊ⁿ`, the inverse of `h` followed by the inclusion `Kᶜ ↪ 𝕊ⁿ`. -/
noncomputable def phiOf {n : ℕ} {K : Set (Sph n)} (h : ↥(Kᶜ : Set (Sph n)) ≃ₜ PL.E n) :
    PL.E n → Sph n := fun y => ((h.symm y : ↥(Kᶜ : Set (Sph n))) : Sph n)

lemma phiOf_mem {n : ℕ} {K : Set (Sph n)} (h : ↥(Kᶜ : Set (Sph n)) ≃ₜ PL.E n) (y : PL.E n) :
    phiOf h y ∈ (Kᶜ : Set (Sph n)) := (h.symm y).2

lemma phiOf_apply {n : ℕ} {K : Set (Sph n)} (h : ↥(Kᶜ : Set (Sph n)) ≃ₜ PL.E n) (y : PL.E n) :
    phiOf h y = ((h.symm y : ↥(Kᶜ : Set (Sph n))) : Sph n) := rfl

lemma continuous_phiOf {n : ℕ} {K : Set (Sph n)} (h : ↥(Kᶜ : Set (Sph n)) ≃ₜ PL.E n) :
    Continuous (phiOf h) := continuous_subtype_val.comp h.symm.continuous

lemma phiOf_injective {n : ℕ} {K : Set (Sph n)} (h : ↥(Kᶜ : Set (Sph n)) ≃ₜ PL.E n) :
    Function.Injective (phiOf h) := by
  intro y y' hyy
  exact h.symm.injective (Subtype.val_injective hyy)

lemma phiOf_h {n : ℕ} {K : Set (Sph n)} (h : ↥(Kᶜ : Set (Sph n)) ≃ₜ PL.E n)
    (u : ↥(Kᶜ : Set (Sph n))) : phiOf h (h u) = (u : Sph n) := by
  rw [phiOf_apply, h.symm_apply_apply]

/-- The pinch of `𝕊ⁿ`: the identity on `K`, and `φ ∘ pinchMap ∘ φ⁻¹` on `Kᶜ`. -/
noncomputable def pinchOf {n : ℕ} {K : Set (Sph n)} (h : ↥(Kᶜ : Set (Sph n)) ≃ₜ PL.E n)
    (S : ℝ) : Sph n → Sph n := by
  classical
  exact fun x => if hx : x ∈ K then x else phiOf h (pinchMap S (h ⟨x, hx⟩))

lemma pinchOf_of_mem {n : ℕ} {K : Set (Sph n)} (h : ↥(Kᶜ : Set (Sph n)) ≃ₜ PL.E n)
    (S : ℝ) {x : Sph n} (hx : x ∈ K) : pinchOf h S x = x := by
  rw [pinchOf]; exact dite_eq_left hx

lemma pinchOf_of_notMem {n : ℕ} {K : Set (Sph n)} (h : ↥(Kᶜ : Set (Sph n)) ≃ₜ PL.E n)
    (S : ℝ) {x : Sph n} (hx : x ∉ K) :
    pinchOf h S x = phiOf h (pinchMap S (h ⟨x, hx⟩)) := by
  rw [pinchOf]; exact dite_eq_right hx


/-! ## The pinch of `𝕊ⁿ` -/

/-- The image of a closed ball under the chart map is closed. -/
lemma isClosed_image_closedBall {n : ℕ} {K : Set (Sph n)}
    (h : ↥(Kᶜ : Set (Sph n)) ≃ₜ PL.E n) (S : ℝ) :
    IsClosed (phiOf h '' closedBall (0 : PL.E n) S) := by
  have hc : IsCompact (closedBall (0 : PL.E n) S) := isCompact_closedBall 0 S
  exact (hc.image (continuous_phiOf h)).isClosed

/-- On the complement of the image of `closedBall 0 (S+1)` the pinch is the identity. -/
lemma pinchOf_eq_self_of_notMem_image {n : ℕ} {K : Set (Sph n)}
    (h : ↥(Kᶜ : Set (Sph n)) ≃ₜ PL.E n) {S : ℝ} (hS : 0 ≤ S) {x : Sph n}
    (hx : x ∉ phiOf h '' closedBall (0 : PL.E n) (S + 1)) : pinchOf h S x = x := by
  by_cases hK : x ∈ K
  · exact pinchOf_of_mem h S hK
  · rw [pinchOf_of_notMem h S hK]
    have hw : h ⟨x, hK⟩ ∉ closedBall (0 : PL.E n) (S + 1) := by
      intro hmem
      exact hx ⟨h ⟨x, hK⟩, hmem, (phiOf_h h ⟨x, hK⟩)⟩
    rw [mem_closedBall, dist_zero_right, not_le] at hw
    rw [pinchMap_self hS (le_of_lt hw)]
    exact phiOf_h h ⟨x, hK⟩

lemma continuous_pinchOf {n : ℕ} {K : Set (Sph n)} (hK : IsClosed K)
    (h : ↥(Kᶜ : Set (Sph n)) ≃ₜ PL.E n) {S : ℝ} (hS : 0 ≤ S) :
    Continuous (pinchOf h S) := by
  classical
  have hcontKc : ContinuousOn (pinchOf h S) (Kᶜ : Set (Sph n)) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hfun : (Kᶜ : Set (Sph n)).domRestrict (pinchOf h S)
        = fun u : ↥(Kᶜ : Set (Sph n)) => phiOf h (pinchMap S (h u)) := by
      funext u
      rw [Set.domRestrict_apply, pinchOf_of_notMem h S u.2]
    rw [hfun]
    exact (continuous_phiOf h).comp ((continuous_pinchMap S).comp h.continuous)
  have hcontImg : ContinuousOn (pinchOf h S)
      ((phiOf h '' closedBall (0 : PL.E n) (S + 1))ᶜ) :=
    ContinuousOn.congr continuous_id.continuousOn
      (fun x hx => pinchOf_eq_self_of_notMem_image h hS hx)
  refine continuous_of_continuousOn_iUnion_of_isOpen (s := fun b : Bool => match b with
    | true => (Kᶜ : Set (Sph n))
    | false => (phiOf h '' closedBall (0 : PL.E n) (S + 1))ᶜ) ?_ ?_ ?_
  · intro b
    cases b with
    | true => exact hcontKc
    | false => exact hcontImg
  · intro b
    cases b with
    | true => exact hK.isOpen_compl
    | false => exact (isClosed_image_closedBall h (S + 1)).isOpen_compl
  · ext x
    rw [mem_iUnion]
    constructor
    · rintro ⟨_⟩; trivial
    · intro _
      by_cases hx : x ∈ K
      · refine ⟨false, ?_⟩
        show x ∈ (phiOf h '' closedBall (0 : PL.E n) (S + 1))ᶜ
        rw [mem_compl_iff]
        rintro ⟨y, -, hyx⟩
        exact absurd hx (hyx ▸ phiOf_mem h y)
      · exact ⟨true, hx⟩

lemma pinchOf_surjective {n : ℕ} {K : Set (Sph n)}
    (h : ↥(Kᶜ : Set (Sph n)) ≃ₜ PL.E n) {S : ℝ} (hS : 0 ≤ S) :
    Function.Surjective (pinchOf h S) := by
  intro z
  by_cases hK : z ∈ K
  · exact ⟨z, pinchOf_of_mem h S hK⟩
  · obtain ⟨y, hy⟩ := pinchMap_surjective (n := n) (S := S) hS (h ⟨z, hK⟩)
    refine ⟨phiOf h y, ?_⟩
    have hyK : phiOf h y ∉ K := phiOf_mem h y
    have hsub : (⟨phiOf h y, hyK⟩ : ↥(Kᶜ : Set (Sph n))) = h.symm y := Subtype.ext rfl
    have hhy : h ⟨phiOf h y, hyK⟩ = y := by rw [hsub, h.apply_symm_apply]
    rw [pinchOf_of_notMem h S hyK, hhy, hy]
    exact phiOf_h h ⟨z, hK⟩

lemma pinchOf_preimage_singleton {n : ℕ} {K : Set (Sph n)}
    (h : ↥(Kᶜ : Set (Sph n)) ≃ₜ PL.E n) {S : ℝ} (hS : 0 ≤ S) :
    pinchOf h S ⁻¹' {phiOf h 0} = phiOf h '' closedBall (0 : PL.E n) S := by
  ext x
  constructor
  · intro hx
    rw [mem_preimage, mem_singleton_iff] at hx
    by_cases hK : x ∈ K
    · rw [pinchOf_of_mem h S hK] at hx
      exact absurd hK (hx ▸ phiOf_mem h 0)
    · rw [pinchOf_of_notMem h S hK] at hx
      have h1 : pinchMap S (h ⟨x, hK⟩) = 0 := phiOf_injective h hx
      have h2 : ‖h ⟨x, hK⟩‖ ≤ S := (pinchMap_eq_zero_iff hS _).mp h1
      exact ⟨h ⟨x, hK⟩, by rw [mem_closedBall, dist_zero_right]; exact h2, phiOf_h h ⟨x, hK⟩⟩
  · rintro ⟨y, hy, rfl⟩
    rw [mem_preimage, mem_singleton_iff]
    rw [mem_closedBall, dist_zero_right] at hy
    have hyK : phiOf h y ∉ K := phiOf_mem h y
    have hsub : (⟨phiOf h y, hyK⟩ : ↥(Kᶜ : Set (Sph n))) = h.symm y := Subtype.ext rfl
    have hmap : pinchMap S y = 0 := (pinchMap_eq_zero_iff hS y).mpr hy
    rw [pinchOf_of_notMem h S hyK, hsub, h.apply_symm_apply, hmap]

lemma pinchOf_injOn {n : ℕ} {K : Set (Sph n)}
    (h : ↥(Kᶜ : Set (Sph n)) ≃ₜ PL.E n) {S : ℝ} (hS : 0 ≤ S) :
    Set.InjOn (pinchOf h S) ((phiOf h '' closedBall (0 : PL.E n) S)ᶜ) := by
  intro x hx x' hx' heq
  rw [mem_compl_iff] at hx hx'
  by_cases hK : x ∈ K
  · rw [pinchOf_of_mem h S hK] at heq
    by_cases hK' : x' ∈ K
    · rw [pinchOf_of_mem h S hK'] at heq; exact heq
    · rw [pinchOf_of_notMem h S hK'] at heq
      exact absurd hK (heq ▸ phiOf_mem h _)
  · rw [pinchOf_of_notMem h S hK] at heq
    by_cases hK' : x' ∈ K
    · rw [pinchOf_of_mem h S hK'] at heq
      exact absurd hK' (heq ▸ phiOf_mem h _)
    · rw [pinchOf_of_notMem h S hK'] at heq
      have h1 : pinchMap S (h ⟨x, hK⟩) = pinchMap S (h ⟨x', hK'⟩) := phiOf_injective h heq
      have hgt : S < ‖h ⟨x, hK⟩‖ := by
        by_contra hle
        rw [not_lt] at hle
        exact hx ⟨h ⟨x, hK⟩, by rw [mem_closedBall, dist_zero_right]; exact hle,
          phiOf_h h ⟨x, hK⟩⟩
      have hgt' : S < ‖h ⟨x', hK'⟩‖ := by
        by_contra hle
        rw [not_lt] at hle
        exact hx' ⟨h ⟨x', hK'⟩, by rw [mem_closedBall, dist_zero_right]; exact hle,
          phiOf_h h ⟨x', hK'⟩⟩
      have h2 : h ⟨x, hK⟩ = h ⟨x', hK'⟩ := pinchMap_injOn hS hgt hgt' h1
      exact Subtype.ext_iff.mp (h.injective h2)

/-! ## The complement of a flat closed ball -/

/-- **The complement of the image of a closed ball under the chart map is `ℝⁿ`.** -/
theorem nonempty_homeomorph_sdiff_image_closedBall {n : ℕ} {K : Set (Sph n)} (hK : IsClosed K)
    (h : ↥(Kᶜ : Set (Sph n)) ≃ₜ PL.E n) {S : ℝ} (hS : 0 < S) :
    Nonempty (↥((phiOf h '' closedBall (0 : PL.E n) S)ᶜ) ≃ₜ PL.E n) := by
  classical
  have hS0 : 0 ≤ S := le_of_lt hS
  haveI : CompactSpace (Sph n) := isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  set rho := pinchOf h S with hrho
  set F := phiOf h '' closedBall (0 : PL.E n) S with hF
  have hρcont : Continuous rho := continuous_pinchOf hK h hS0
  have hρsurj : Function.Surjective rho := pinchOf_surjective h hS0
  have hρclosedmap : IsClosedMap rho := fun s hs => (hs.isCompact.image hρcont).isClosed
  have hpre : rho ⁻¹' ({phiOf h 0} : Set (Sph n)) = F := pinchOf_preimage_singleton h hS0
  have hpre' : rho ⁻¹' (({phiOf h 0} : Set (Sph n))ᶜ) = Fᶜ := by
    rw [Set.preimage_compl, hpre]
  have hmem : ∀ x : ↥(rho ⁻¹' (({phiOf h 0} : Set (Sph n))ᶜ)), x.1 ∈ Fᶜ :=
    fun x => hpre' ▸ x.2
  have hFx : ∀ x : Sph n, x ∈ F → rho x = phiOf h 0 := by
    intro x hx
    rw [← hpre] at hx
    simpa using hx
  have hbij : Function.Bijective
      ((({phiOf h 0} : Set (Sph n))ᶜ).restrictPreimage rho) := by
    constructor
    · intro a b hab
      have hab' : rho a.1 = rho b.1 := congrArg Subtype.val hab
      have ha : a.1 ∈ Fᶜ := hmem a
      have hb : b.1 ∈ Fᶜ := hmem b
      have hFab : a.1 ∈ (phiOf h '' closedBall (0 : PL.E n) S)ᶜ := hpre' ▸ a.2
      have hFbb : b.1 ∈ (phiOf h '' closedBall (0 : PL.E n) S)ᶜ := hpre' ▸ b.2
      have : a.1 = b.1 := pinchOf_injOn h (S := S) hS0 hFab hFbb hab'
      exact Subtype.ext this
    · intro z
      obtain ⟨x, hx⟩ := hρsurj z.1
      have hxF : x ∉ F := by
        intro hF'
        exact z.2 (hx ▸ hFx x hF')
      refine ⟨⟨x, ?_⟩, ?_⟩
      · rw [hpre']
        exact hxF
      · exact Subtype.ext hx
  have hcont : Continuous ((({phiOf h 0} : Set (Sph n))ᶜ).restrictPreimage rho) :=
    (hρcont.comp continuous_subtype_val).subtype_mk _
  have hclosed : IsClosedMap ((({phiOf h 0} : Set (Sph n))ᶜ).restrictPreimage rho) :=
    IsClosedMap.restrictPreimage hρclosedmap _
  let e : ↥(rho ⁻¹' (({phiOf h 0} : Set (Sph n))ᶜ)) ≃ ↥(({phiOf h 0} : Set (Sph n))ᶜ) :=
    Equiv.ofBijective _ hbij
  have hecont : Continuous e := by
    rw [show (⇑e) = ((({phiOf h 0} : Set (Sph n))ᶜ).restrictPreimage rho) from
      funext fun x => Equiv.ofBijective_apply _ _ x]
    exact hcont
  have heclosed : IsClosedMap e := by
    rw [show (⇑e) = ((({phiOf h 0} : Set (Sph n))ᶜ).restrictPreimage rho) from
      funext fun x => Equiv.ofBijective_apply _ _ x]
    exact hclosed
  have hhomeo : ↥(rho ⁻¹' (({phiOf h 0} : Set (Sph n))ᶜ)) ≃ₜ ↥(({phiOf h 0} : Set (Sph n))ᶜ) :=
    e.toHomeomorphOfContinuousClosed hecont heclosed
  obtain ⟨hp⟩ := Work.Brown.Cell.nonempty_homeomorph_compl_point_sphere (phiOf h 0)
  exact ⟨((Homeomorph.setCongr hpre').symm.trans hhomeo).trans hp⟩

/-! ## The main theorem -/

theorem exists_isOpenCell_neighborhood {n : ℕ} {K : Set ↥(Metric.sphere (0 : PL.E (n + 1)) 1)}
    (hK : IsClosed K) (hc : Nonempty (↥(Kᶜ : Set ↥(Metric.sphere (0 : PL.E (n + 1)) 1)) ≃ₜ PL.E n))
    {U : Set ↥(Metric.sphere (0 : PL.E (n + 1)) 1)} (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ W : Set ↥(Metric.sphere (0 : PL.E (n + 1)) 1),
      IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧ Nonempty (↥W ≃ₜ PL.E n) := by
  classical
  obtain ⟨h⟩ := hc
  have hUc : IsCompact (Uᶜ : Set (Sph n)) := hU.isClosed_compl.isCompact
  haveI : CompactSpace ↥(Uᶜ : Set (Sph n)) := isCompact_iff_compactSpace.mp hUc
  have hUcK : ∀ x : ↥(Uᶜ : Set (Sph n)), x.1 ∈ (Kᶜ : Set (Sph n)) :=
    fun x hxK => x.2 (hKU hxK)
  let psi : ↥(Uᶜ : Set (Sph n)) → PL.E n := fun x => h ⟨x.1, hUcK x⟩
  have hpsicont : Continuous psi :=
    h.continuous.comp (Continuous.subtype_mk continuous_subtype_val hUcK)
  obtain ⟨R, hR⟩ := (isCompact_range hpsicont).isBounded.exists_norm_le
  set S : ℝ := max R 1 with hSdef
  have hSpos : 0 < S := lt_of_lt_of_le one_pos (le_max_right R 1)
  have hsub : (Uᶜ : Set (Sph n)) ⊆ phiOf h '' closedBall (0 : PL.E n) S := by
    intro y hy
    have hRy : ‖psi ⟨y, hy⟩‖ ≤ R := hR (psi ⟨y, hy⟩) ⟨⟨y, hy⟩, rfl⟩
    exact ⟨psi ⟨y, hy⟩,
      by rw [mem_closedBall, dist_zero_right]; exact le_trans hRy (le_max_left R 1),
      phiOf_h h (⟨y, hUcK ⟨y, hy⟩⟩ : ↥(Kᶜ : Set (Sph n)))⟩
  have hFclosed : IsClosed (phiOf h '' closedBall (0 : PL.E n) S) :=
    isClosed_image_closedBall h S
  refine ⟨(phiOf h '' closedBall (0 : PL.E n) S)ᶜ, hFclosed.isOpen_compl, ?_, ?_, ?_⟩
  · intro x hxK
    rw [mem_compl_iff]
    rintro ⟨y, -, hyx⟩
    exact absurd hxK (hyx ▸ phiOf_mem h y)
  · intro x hx
    rw [mem_compl_iff] at hx
    by_contra hxU
    exact hx (hsub hxU)
  · exact nonempty_homeomorph_sdiff_image_closedBall hK h hSpos

end Work.Brown.Cellular
