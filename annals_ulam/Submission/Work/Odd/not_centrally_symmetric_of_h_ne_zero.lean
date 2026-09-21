import Mathlib
import Submission.Commons.Geometry.Ulam.odd_floating_of_family

namespace Work.Odd

open MeasureTheory
open scoped RealInnerProductSpace

set_option autoImplicit false

/-- The point reflection `x ↦ 2 • p - x` about `p` preserves Lebesgue measure. -/
private lemma measurePreserving_reflect {d : ℕ} (p : EuclideanSpace ℝ (Fin d)) :
    MeasurePreserving (fun x : EuclideanSpace ℝ (Fin d) => (2 : ℝ) • p - x) volume volume := by
  have h1 : MeasurePreserving (fun x : EuclideanSpace ℝ (Fin d) => -x) volume volume :=
    Measure.measurePreserving_neg volume
  have h2 : MeasurePreserving (fun y : EuclideanSpace ℝ (Fin d) => (2 : ℝ) • p + y) volume volume :=
    measurePreserving_add_left volume ((2 : ℝ) • p)
  have h3 : MeasurePreserving
      ((fun y : EuclideanSpace ℝ (Fin d) => (2 : ℝ) • p + y) ∘
        (fun x : EuclideanSpace ℝ (Fin d) => -x)) volume volume := h2.comp h1
  exact h3

/-- For a set `K` invariant under the point reflection about `p`, the half space
`{x | ⟪x, ξ⟫ ≤ ⟪p, ξ⟫}` containing one of the two halves bounded by the hyperplane through
`p` with normal `ξ` has exactly half the volume of `K`, provided `ξ ≠ 0`. -/
private lemma halfspace_center_half_volume' {d : ℕ} [NeZero d]
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK_meas : MeasurableSet K)
    (hK_fin : volume K < ⊤)
    {p ξ : EuclideanSpace ℝ (Fin d)}
    (hp : ∀ x : EuclideanSpace ℝ (Fin d), (x ∈ K ↔ (2 : ℝ) • p - x ∈ K))
    (hξ : ξ ≠ 0) :
    volume.real (K ∩ {x | ⟪x, ξ⟫ ≤ ⟪p, ξ⟫}) = volume.real K / 2 := by
  classical
  set c0 : ℝ := ⟪p, ξ⟫ with hc0
  set A : Set (EuclideanSpace ℝ (Fin d)) := K ∩ {x | ⟪x, ξ⟫ ≤ c0} with hA
  set C : Set (EuclideanSpace ℝ (Fin d)) := K ∩ {x | c0 ≤ ⟪x, ξ⟫} with hC
  have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin d) => ⟪x, ξ⟫) :=
    continuous_id.inner continuous_const
  have hC_meas : MeasurableSet C :=
    hK_meas.inter (measurableSet_le measurable_const hcont.measurable)
  have hC_null : NullMeasurableSet C volume := hC_meas.nullMeasurableSet
  have hA_lt : volume A < ⊤ := lt_of_le_of_lt (measure_mono (Set.inter_subset_left)) hK_fin
  have hC_lt : volume C < ⊤ := lt_of_le_of_lt (measure_mono (Set.inter_subset_left)) hK_fin
  have hinner : ∀ x : EuclideanSpace ℝ (Fin d),
      ⟪(2 : ℝ) • p - x, ξ⟫ = 2 * ⟪p, ξ⟫ - ⟪x, ξ⟫ := by
    intro x
    rw [inner_sub_left, inner_smul_left]
    simp
  have hpre : (fun x : EuclideanSpace ℝ (Fin d) => (2 : ℝ) • p - x) ⁻¹' C = A := by
    ext x
    simp only [Set.mem_preimage, hA, hC, Set.mem_inter_iff, Set.mem_ofPred_eq]
    rw [hinner x]
    constructor
    · rintro ⟨hx, hle⟩
      exact ⟨(hp x).mpr hx, by rw [hc0] at hle ⊢; linarith⟩
    · rintro ⟨hx, hle⟩
      exact ⟨(hp x).mp hx, by rw [hc0] at hle ⊢; linarith⟩
  have hvol_eq : volume A = volume C := by
    have h := (measurePreserving_reflect p).measure_preimage hC_null
    rw [hpre] at h
    exact h
  have hUnion : A ∪ C = K := by
    ext x
    simp only [hA, hC, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    · intro hx
      rcases le_total (⟪x, ξ⟫) c0 with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
  have hInter_zero : volume (A ∩ C) = 0 := by
    refine measure_mono_null ?_ (Commons.Geometry.Ulam.volume_hyperplane_eq_zero hξ c0)
    intro x hx
    simp only [hA, hC, Set.mem_inter_iff, Set.mem_ofPred_eq] at hx
    exact le_antisymm hx.1.2 hx.2.2
  have hInter_real_zero : volume.real (A ∩ C) = 0 := by
    rw [Measure.real, hInter_zero]
    simp
  have hdecomp : volume.real (A ∪ C) + volume.real (A ∩ C) = volume.real A + volume.real C :=
    measureReal_union_add_inter₀ hC_null hA_lt.ne hC_lt.ne
  rw [hUnion, hInter_real_zero, add_zero] at hdecomp
  have hvolC : volume.real C = volume.real A := by
    show (volume C).toReal = (volume A).toReal
    rw [hvol_eq]
  rw [hvolC] at hdecomp
  linarith

lemma not_centrally_symmetric_of_h_ne_zero {d : ℕ} [NeZero d]
    {K : Set (EuclideanSpace ℝ (Fin d))} {h : ℝ → ℝ}
    (hK_meas : MeasurableSet K) (hK_conv : Convex ℝ K)
    (hK_int : (interior K).Nonempty) (hK_fin : MeasureTheory.volume K < ⊤)
    (hvol : ∀ s : ℝ, 0 < s →
      MeasureTheory.volume.real (K ∩ {x : EuclideanSpace ℝ (Fin d) |
          x ⟨d - 1, by exact Nat.sub_lt (Nat.pos_of_neZero d) (by decide : 0 < 1)⟩ ≤ s * x 0 + h s}) =
        MeasureTheory.volume.real K / 2)
    (hh_supp : Function.support h ⊆ Set.Icc (1 - 2 * (1 / 10 : ℝ)) (1 - (1 / 10 : ℝ)))
    (hhne : ∃ s : ℝ, 0 < s ∧ h s ≠ 0) :
    ¬ ∃ p : EuclideanSpace ℝ (Fin d),
      ∀ x : EuclideanSpace ℝ (Fin d), (x ∈ K ↔ (2 : ℝ) • p - x ∈ K) := by
  classical
  rintro ⟨p, hp⟩
  -- The two coordinate directions featuring in `hvol`.
  let i0 : Fin d := ⟨d - 1, by exact Nat.sub_lt (Nat.pos_of_neZero d) (by decide : 0 < 1)⟩
  let xi : ℝ → EuclideanSpace ℝ (Fin d) :=
    fun s => EuclideanSpace.single i0 (1 : ℝ) - s • EuclideanSpace.single (0 : Fin d) (1 : ℝ)
  -- `K` has positive volume.
  have hK_pos : 0 < volume.real K := by
    obtain ⟨q, hq⟩ := hK_int
    obtain ⟨r, hr, hball⟩ := (Metric.isOpen_iff.mp isOpen_interior) q hq
    have hsub : Metric.ball q r ⊆ K := fun x hx => interior_subset (hball hx)
    have hpos : 0 < volume (Metric.ball q r) :=
      Metric.isOpen_ball.measure_pos volume ⟨q, Metric.mem_ball_self hr⟩
    have hne : volume K ≠ 0 := ne_of_gt (lt_of_lt_of_le hpos (measure_mono hsub))
    exact ENNReal.toReal_pos hne hK_fin.ne
  -- Coordinate computation for `xi`.
  have hxi_inner : ∀ s : ℝ, ⟪p, xi s⟫ = p i0 - s * p 0 := by
    intro s
    simp only [xi]
    rw [inner_sub_right, inner_smul_right, EuclideanSpace.inner_single_right,
      EuclideanSpace.inner_single_right]
    simp
  have hpt_inner : ∀ (x : EuclideanSpace ℝ (Fin d)) (s : ℝ),
      ⟪x, xi s⟫ = x i0 - s * x 0 := by
    intro x s
    simp only [xi]
    rw [inner_sub_right, inner_smul_right, EuclideanSpace.inner_single_right,
      EuclideanSpace.inner_single_right]
    simp
  -- Restate `hvol` in terms of `xi`.
  have hvol_xi : ∀ s : ℝ, 0 < s →
      volume.real (K ∩ {x | ⟪x, xi s⟫ ≤ h s}) = volume.real K / 2 := by
    intro s hs
    have hset : K ∩ {x : EuclideanSpace ℝ (Fin d) | x i0 ≤ s * x 0 + h s} =
        K ∩ {x : EuclideanSpace ℝ (Fin d) | ⟪x, xi s⟫ ≤ h s} := by
      congr 1
      ext x
      simp only [Set.mem_ofPred_eq]
      rw [hpt_inner x s]
      constructor <;> intro hx <;> linarith
    rw [← hset]
    exact hvol s hs
  -- `xi s ≠ 0` for every `s > 0`: otherwise the hypothesis `hvol` is contradictory.
  have hxi_ne : ∀ s : ℝ, 0 < s → xi s ≠ 0 := by
    intro s hs hzero
    have hvol_s := hvol_xi s hs
    rw [hzero] at hvol_s
    have hinner0 : ∀ x : EuclideanSpace ℝ (Fin d), ⟪x, (0 : EuclideanSpace ℝ (Fin d))⟫ = 0 := by
      intro x
      simp
    have hset : {x : EuclideanSpace ℝ (Fin d) | ⟪x, (0 : EuclideanSpace ℝ (Fin d))⟫ ≤ h s} =
        (if 0 ≤ h s then Set.univ else ∅) := by
      ext x
      simp only [hinner0, Set.mem_ofPred_eq]
      by_cases hh : 0 ≤ h s
      · simp [hh]
      · simp [hh]
    rw [hset] at hvol_s
    by_cases hh : 0 ≤ h s
    · rw [if_pos hh] at hvol_s
      rw [Set.inter_univ] at hvol_s
      linarith
    · rw [if_neg hh] at hvol_s
      simp only [Set.inter_empty, measureReal_empty] at hvol_s
      linarith
  -- The level of `h` is the level of the centre.
  have hh_eq : ∀ s : ℝ, 0 < s → h s = ⟪p, xi s⟫ := by
    intro s hs
    have hξ := hxi_ne s hs
    have ha := hvol_xi s hs
    have hb := halfspace_center_half_volume' hK_meas hK_fin hp hξ
    exact Commons.Geometry.Convex.eq_of_volume_halfspace_eq_of_convex
      hK_meas hK_conv hK_int hK_fin hξ
      (by rw [ha]; linarith)
      (by rw [ha]; linarith)
      (by rw [hb]; linarith)
      (by rw [hb]; linarith)
      (by rw [ha, hb])
  -- Since `2, 3` are outside the support of `h`, they give `p = 0`.
  have h2out : (2 : ℝ) ∉ Set.Icc (1 - 2 * (1 / 10 : ℝ)) (1 - (1 / 10 : ℝ)) := by
    simp only [Set.mem_Icc]; norm_num
  have h3out : (3 : ℝ) ∉ Set.Icc (1 - 2 * (1 / 10 : ℝ)) (1 - (1 / 10 : ℝ)) := by
    simp only [Set.mem_Icc]; norm_num
  have hh2 : h 2 = 0 := by
    by_contra hc
    exact h2out (hh_supp (by simpa [Function.mem_support] using hc))
  have hh3 : h 3 = 0 := by
    by_contra hc
    exact h3out (hh_supp (by simpa [Function.mem_support] using hc))
  have hp2 : p i0 - 2 * p 0 = 0 := by
    rw [← hxi_inner 2, ← hh_eq 2 (by norm_num), hh2]
  have hp3 : p i0 - 3 * p 0 = 0 := by
    rw [← hxi_inner 3, ← hh_eq 3 (by norm_num), hh3]
  have hp_0 : p 0 = 0 := by linarith
  have hp_i0 : p i0 = 0 := by linarith
  obtain ⟨s0, hs0_pos, hs0_ne⟩ := hhne
  exact hs0_ne (by rw [hh_eq s0 hs0_pos, hxi_inner s0, hp_0, hp_i0]; ring)

end Work.Odd
