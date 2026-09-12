import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

namespace Commons.Geometry.Convex.Hadwiger

open Filter
open scoped Topology

namespace HausdorffSupport

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Support function value of a convex body in a direction. -/
noncomputable def support (K : ConvexBody V) (u : V) : ℝ :=
  sSup ((fun x : V => inner ℝ u x) '' (K : Set V))

/-- The set of absolute support-function differences over unit directions. -/
noncomputable def supportSet (K L : ConvexBody V) : Set ℝ :=
  {r : ℝ | ∃ u : V, ‖u‖ = 1 ∧ r = |support K u - support L u|}

lemma supportSet_comm (K L : ConvexBody V) : supportSet K L = supportSet L K := by
  ext r
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u, hu, ?_⟩
    rw [abs_sub_comm]
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u, hu, ?_⟩
    rw [abs_sub_comm]

lemma inner_image_nonempty (K : ConvexBody V) (u : V) :
    ((fun x : V => inner ℝ u x) '' (K : Set V)).Nonempty :=
  K.nonempty.image _

lemma inner_image_bddAbove (K : ConvexBody V) (u : V) :
    BddAbove ((fun x : V => inner ℝ u x) '' (K : Set V)) := by
  obtain ⟨R, hRpos, hR⟩ := K.isBounded.exists_pos_norm_le
  refine ⟨‖u‖ * R, ?_⟩
  rintro a ⟨x, hx, rfl⟩
  calc
    inner ℝ u x ≤ ‖u‖ * ‖x‖ := real_inner_le_norm u x
    _ ≤ ‖u‖ * R := mul_le_mul_of_nonneg_left (hR x hx) (norm_nonneg u)

lemma inner_le_support (K : ConvexBody V) {x : V} (hx : x ∈ (K : Set V)) (u : V) :
    inner ℝ u x ≤ support K u := by
  exact le_csSup (inner_image_bddAbove K u) ⟨x, hx, rfl⟩

lemma support_le_of_forall_le (K : ConvexBody V) (u : V) (a : ℝ)
    (ha : ∀ x : V, x ∈ (K : Set V) → inner ℝ u x ≤ a) : support K u ≤ a := by
  exact csSup_le (inner_image_nonempty K u) (by
    rintro b ⟨x, hx, rfl⟩
    exact ha x hx)

lemma inner_le_inner_add_norm_dist (u x y : V) :
    inner ℝ u x ≤ inner ℝ u y + ‖u‖ * dist x y := by
  calc
    inner ℝ u x = inner ℝ u (y + (x - y)) := by congr 1; abel
    _ = inner ℝ u y + inner ℝ u (x - y) := by rw [inner_add_right]
    _ ≤ inner ℝ u y + ‖u‖ * ‖x - y‖ := add_le_add_right (real_inner_le_norm u (x - y)) _
    _ = inner ℝ u y + ‖u‖ * dist x y := by rw [dist_eq_norm]

/-- One-sided bound of the support difference by the Hausdorff distance. -/
lemma support_le_support_add_dist (K L : ConvexBody V) {u : V} (hu : ‖u‖ = 1) :
    support K u ≤ support L u + dist K L := by
  apply support_le_of_forall_le K u (support L u + dist K L)
  intro x hx
  have hfin : Metric.hausdorffEDist (K : Set V) (L : Set V) ≠ ⊤ := ConvexBody.hausdorffEDist_ne_top
  have hinf0 : Metric.infDist x (L : Set V) ≤ Metric.hausdorffDist (K : Set V) (L : Set V) :=
    Metric.infDist_le_hausdorffDist_of_mem hx hfin
  have hinf : Metric.infDist x (L : Set V) ≤ dist K L := by
    simpa [ConvexBody.hausdorffDist_coe] using hinf0
  obtain ⟨y, hyL, hyd⟩ := L.isCompact.exists_infDist_eq_dist L.nonempty x
  have hdy : dist x y ≤ dist K L := by
    rw [← hyd]
    exact hinf
  calc
    inner ℝ u x ≤ inner ℝ u y + ‖u‖ * dist x y := inner_le_inner_add_norm_dist u x y
    _ = inner ℝ u y + dist x y := by
      rw [hu]
      ring
    _ ≤ support L u + dist x y := add_le_add_left (inner_le_support L hyL u) (dist x y)
    _ ≤ support L u + dist K L := add_le_add_right hdy (support L u)

/-- The support difference in a unit direction is bounded by the Hausdorff distance. -/
lemma support_dist_le_dist (K L : ConvexBody V) {u : V} (hu : ‖u‖ = 1) :
    |support K u - support L u| ≤ dist K L := by
  rw [abs_sub_le_iff]
  constructor
  · have h1 : support K u - support L u ≤ dist K L := by
      have h := support_le_support_add_dist K L hu
      linarith
    exact h1
  · have h2 : support L u - support K u ≤ dist K L := by
      have h := support_le_support_add_dist L K hu
      simpa [dist_comm, add_comm] using h
    exact h2

/-- For a unit vector the absolute support value is bounded by the norm bound of the body. -/
lemma support_abs_le_unit (K : ConvexBody V) {u : V} (hu : ‖u‖ = 1) (R : ℝ)
    (hR : ∀ x : V, x ∈ (K : Set V) → ‖x‖ ≤ R) : |support K u| ≤ R := by
  rw [abs_le]
  constructor
  · obtain ⟨x0, hx0⟩ := K.nonempty
    have hx0_le : inner ℝ u x0 ≤ support K u := inner_le_support K hx0 u
    have hb : |inner ℝ u x0| ≤ R := by
      calc
        |inner ℝ u x0| ≤ ‖u‖ * ‖x0‖ := by
          simpa using (norm_inner_le_norm (𝕜 := ℝ) u x0)
        _ = ‖x0‖ := by rw [hu]; simp
        _ ≤ R := hR x0 hx0
    exact le_trans (abs_le.mp hb).1 hx0_le
  · apply support_le_of_forall_le K u R
    intro x hx
    calc
      inner ℝ u x ≤ ‖u‖ * ‖x‖ := real_inner_le_norm u x
      _ = ‖x‖ := by rw [hu]; simp
      _ ≤ R := hR x hx

/-- The set of support differences over unit vectors is bounded above. -/
lemma supportSet_bddAbove (K L : ConvexBody V) : BddAbove (supportSet K L) := by
  obtain ⟨RK, hRKpos, hRK⟩ := K.isBounded.exists_pos_norm_le
  obtain ⟨RL, hRLpos, hRL⟩ := L.isBounded.exists_pos_norm_le
  refine ⟨RK + RL, ?_⟩
  rintro r ⟨u, hu, rfl⟩
  calc
    |support K u - support L u| ≤ |support K u| + |support L u| := by
      have h := abs_sub_le (support K u) (0 : ℝ) (support L u)
      simpa using h
    _ ≤ RK + RL := add_le_add (support_abs_le_unit K hu RK hRK) (support_abs_le_unit L hu RL hRL)

/-- The supremum of the support-difference set is nonnegative. -/
lemma supportSet_sSup_nonneg (K L : ConvexBody V) : 0 ≤ sSup (supportSet K L) := by
  cases (supportSet K L).eq_empty_or_nonempty with
  | inl h0 =>
      rw [h0, Real.sSup_empty]
  | inr hn =>
      obtain ⟨r, hr⟩ := hn
      rcases hr with ⟨u, hu, rfl⟩
      have hnonneg : 0 ≤ |support K u - support L u| := abs_nonneg _
      have hle : |support K u - support L u| ≤ sSup (supportSet K L) :=
        le_csSup (supportSet_bddAbove K L) ⟨u, hu, rfl⟩
      linarith

/-- closest point from a point outside a compact convex body -/
lemma exists_closest (L : ConvexBody V) (x : V) (hxL : x ∉ (L : Set V)) :
    ∃ p : V, p ∈ (L : Set V) ∧ x ≠ p ∧
      (‖x - p‖ = ⨅ w : (L : Set V), ‖x - w‖) := by
  obtain ⟨p, hpL, hpdist⟩ := L.isCompact.exists_infDist_eq_dist L.nonempty x
  have hp_ne : x ≠ p := by
    intro hxp
    apply hxL
    simpa [hxp] using hpL
  refine ⟨p, hpL, hp_ne, ?_⟩
  have hinf_eq : ‖x - p‖ = Metric.infDist x (L : Set V) :=
    (dist_eq_norm x p).symm.trans hpdist.symm
  rw [hinf_eq, Metric.infDist_eq_iInf]
  simp [dist_eq_norm]

lemma norm_smul_unit (x p : V) (hne : x ≠ p) :
    ‖(‖x - p‖⁻¹) • (x - p)‖ = 1 := by
  have hn0 : ‖x - p‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  rw [norm_smul, Real.norm_eq_abs]
  have habs : |‖x - p‖⁻¹| = ‖x - p‖⁻¹ := abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))
  rw [habs, inv_mul_cancel₀ hn0]

lemma inner_unit_xp (x p : V) (hne : x ≠ p) :
    inner ℝ ((‖x - p‖⁻¹) • (x - p)) (x - p) = ‖x - p‖ := by
  have hn0 : ‖x - p‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  calc
    inner ℝ ((‖x - p‖⁻¹) • (x - p)) (x - p)
        = (‖x - p‖⁻¹) * inner ℝ (x - p) (x - p) := by
            rw [inner_smul_left]
            simp
    _ = (‖x - p‖⁻¹) * ‖x - p‖ ^ 2 := by
            simp
    _ = ‖x - p‖ := by
            rw [sq, ← mul_assoc, inv_mul_cancel₀ hn0, one_mul]

/-- distance of a point of K to L is bounded by the sup of support differences -/
lemma infDist_le_sSup_support (K L : ConvexBody V) :
    ∀ x : V, x ∈ (K : Set V) →
      Metric.infDist x (L : Set V) ≤ sSup (supportSet K L) := by
  intro x hxK
  by_cases hxL : x ∈ (L : Set V)
  · have h0 : Metric.infDist x (L : Set V) = 0 := Metric.infDist_zero_of_mem hxL
    rw [h0]
    exact supportSet_sSup_nonneg K L
  · obtain ⟨p, hpL, hne, hmin⟩ := exists_closest L x hxL
    have hproj : ∀ w ∈ (L : Set V), inner ℝ (x - p) (w - p) ≤ 0 :=
      (norm_eq_iInf_iff_real_inner_le_zero (K := (L : Set V)) L.convex hpL).mp hmin
    let u : V := (‖x - p‖⁻¹) • (x - p)
    have hu_unit : ‖u‖ = 1 := by
      simpa [u] using norm_smul_unit x p hne
    have hL_sup_le : support L u ≤ inner ℝ u p := by
      apply support_le_of_forall_le L u (inner ℝ u p)
      intro w hw
      have hwp : inner ℝ (x - p) (w - p) ≤ 0 := hproj w hw
      have hn0 : 0 < ‖x - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
      have hu_wp : inner ℝ u (w - p) ≤ 0 := by
        calc
          inner ℝ u (w - p) = (‖x - p‖⁻¹) * inner ℝ (x - p) (w - p) := by
            rw [inner_smul_left]
            simp
          _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hn0.le) hwp
      have hdiff : inner ℝ u w - inner ℝ u p ≤ 0 := by
        simpa [inner_sub_right] using hu_wp
      linarith
    have hK_sup_ge : inner ℝ u x ≤ support K u := inner_le_support K hxK u
    have hu_xp : inner ℝ u (x - p) = ‖x - p‖ := by
      simpa [u] using inner_unit_xp x p hne
    have hL_le : support L u ≤ inner ℝ u x - ‖x - p‖ := by
      have hsub : inner ℝ u x - inner ℝ u p = ‖x - p‖ := by
        rw [← inner_sub_right u x p]
        exact hu_xp
      linarith
    have hgap : ‖x - p‖ ≤ support K u - support L u := by linarith
    have hinf_eq : Metric.infDist x (L : Set V) = ‖x - p‖ := by
      calc
        Metric.infDist x (L : Set V) = ⨅ y : (L : Set V), dist x ↑y := Metric.infDist_eq_iInf
        _ = ⨅ y : (L : Set V), ‖x - ↑y‖ := by simp [dist_eq_norm]
        _ = ‖x - p‖ := hmin.symm
    have hle_abs : ‖x - p‖ ≤ |support K u - support L u| := by
      have ha : 0 ≤ support K u - support L u := le_trans (norm_nonneg _) hgap
      rw [abs_of_nonneg ha]
      exact hgap
    have hinf_abs : Metric.infDist x (L : Set V) ≤ |support K u - support L u| := by
      rw [hinf_eq]
      exact hle_abs
    have hmem : |support K u - support L u| ∈ supportSet K L := ⟨u, hu_unit, rfl⟩
    exact le_trans hinf_abs (le_csSup (supportSet_bddAbove K L) hmem)

/-- Upper bound: the supremum of support differences is at most the Hausdorff distance. -/
lemma sSup_support_le_dist (K L : ConvexBody V) : sSup (supportSet K L) ≤ dist K L := by
  cases (supportSet K L).eq_empty_or_nonempty with
  | inl h0 =>
      rw [h0, Real.sSup_empty]
      exact dist_nonneg
  | inr hn =>
      refine csSup_le hn ?_
      rintro r ⟨u, hu, rfl⟩
      exact support_dist_le_dist K L hu

/-- Lower bound: the Hausdorff distance is at most the supremum of support differences. -/
lemma hausdorffDist_le_sSup_support (K L : ConvexBody V) : dist K L ≤ sSup (supportSet K L) := by
  have hnonneg : 0 ≤ sSup (supportSet K L) := supportSet_sSup_nonneg K L
  have H1 : ∀ x ∈ (K : Set V), Metric.infDist x (L : Set V) ≤ sSup (supportSet K L) := by
    intro x hx
    exact infDist_le_sSup_support K L x hx
  have H2 : ∀ y ∈ (L : Set V), Metric.infDist y (K : Set V) ≤ sSup (supportSet K L) := by
    intro y hy
    have h := infDist_le_sSup_support L K y hy
    simpa [supportSet_comm L K] using h
  have hhd : Metric.hausdorffDist (K : Set V) (L : Set V) ≤ sSup (supportSet K L) :=
    Metric.hausdorffDist_le_of_infDist hnonneg H1 H2
  simpa [ConvexBody.hausdorffDist_coe] using hhd

end HausdorffSupport

open HausdorffSupport

theorem hausdorffDist_eq_sSup_support
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    (K L : ConvexBody V) :
    dist K L =
      sSup {r : ℝ | ∃ u : V, ‖u‖ = 1 ∧
        r = |sSup ((fun x : V => inner ℝ u x) '' (K : Set V)) -
              sSup ((fun x : V => inner ℝ u x) '' (L : Set V))|} := by
  change dist K L = sSup (HausdorffSupport.supportSet K L)
  exact le_antisymm (HausdorffSupport.hausdorffDist_le_sSup_support K L)
    (HausdorffSupport.sSup_support_le_dist K L)

end Commons.Geometry.Convex.Hadwiger