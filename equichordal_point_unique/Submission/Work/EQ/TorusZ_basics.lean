import Mathlib
import Submission.Work.EQ.TorusZ
import Submission.Work.EQ.DefsCore
import Submission.Work.Covering.exists_tendsto_of_isCoveringMap_comp

/-!
# The torus `ℂ*/λ^ℤ`: discreteness, covering map, compactness

Basic facts about the quotient `TorusZ l = ℂˣ ⧸ Subgroup.zpowers (lamU l)` used in Rychlik's
proof of Theorems 8, 10 and 11:

* `TorusZ_isDiscrete`: the subgroup `λ^ℤ` is discrete in `ℂ*` (the input for the
  `IsQuotientCoveringMap` machinery of `Mathlib/Topology/Covering/Quotient.lean`);
* `TorusZ_isCoveringMap`: `ℂ* → ℂ*/λ^ℤ` is a covering map;
* `TorusZ_t2Space`, `TorusZ_compactSpace`: the torus is a compact Hausdorff space;
* `TorusZ_zpow_mem_annulus`: every `λ^ℤ`-orbit meets the annulus `{r₁ ≤ ‖z‖ ≤ r₂}` when
  `r₁ ≤ l r₂` (the "`r₂/r₁ > 1/λ`" condition);
* `exists_tendsto_of_tendsto_mk`: a continuous path into `ℂ*` whose image in the torus has a
  limit has a limit in `ℂ*` (the "coverings do not create limits" input).
-/

namespace Work.EQ

open Filter _root_.Topology

/-! ## Elementary norm estimates for the `λ^ℤ`-orbit -/

/-- The norm of `(lamU l)^n` is `l^n` (real `zpow`). -/
theorem norm_lamU_zpow {l : ℝ} (hl0 : 0 < l) (n : ℤ) :
    ‖(((lamU l) ^ n : ℂˣ) : ℂ)‖ = l ^ n := by
  rw [Units.val_zpow_eq_zpow_val, lamU_coe (ne_of_gt hl0), norm_zpow]
  congr 1
  simp [abs_of_pos hl0]

/-- For `0 < l < 1` and `j ≠ 0`, `|l^j - 1| ≥ 1 - l`. -/
theorem one_sub_le_abs_zpow_sub_one {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) {j : ℤ} (hj : j ≠ 0) :
    1 - l ≤ |l ^ j - 1| := by
  rcases lt_trichotomy j 0 with h | h | h
  · obtain ⟨k, hjk⟩ : ∃ k : ℕ, j = -((k + 1 : ℕ) : ℤ) := ⟨(-j).toNat - 1, by omega⟩
    subst hjk
    rw [zpow_neg, zpow_natCast]
    have hpow_pos : 0 < l ^ (k + 1) := pow_pos hl0 _
    have hpow_le : l ^ (k + 1) ≤ l :=
      pow_le_of_le_one (le_of_lt hl0) (le_of_lt hl1) (by omega)
    have hle1 : 1 ≤ (l ^ (k + 1))⁻¹ :=
      (one_le_inv₀ hpow_pos).mpr (le_of_lt (lt_of_le_of_lt hpow_le hl1))
    have habs : |(l ^ (k + 1))⁻¹ - 1| = (l ^ (k + 1))⁻¹ - 1 := abs_of_nonneg (by linarith)
    rw [habs]
    have h4 : 2 - l ≤ (l ^ (k + 1))⁻¹ := by
      rw [inv_eq_one_div, le_div_iff₀ hpow_pos]
      have h3 : l * (2 - l) ≤ 1 := by nlinarith [sq_nonneg (1 - l)]
      have h5 : (2 - l) * l ^ (k + 1) ≤ (2 - l) * l :=
        mul_le_mul_of_nonneg_left hpow_le (by linarith)
      linarith [mul_comm (2 - l) (l ^ (k + 1))]
    linarith
  · exact absurd h hj
  · obtain ⟨k, hjk⟩ : ∃ k : ℕ, j = ((k + 1 : ℕ) : ℤ) := ⟨j.toNat - 1, by omega⟩
    subst hjk
    rw [zpow_natCast]
    have hpow_le : l ^ (k + 1) ≤ l :=
      pow_le_of_le_one (le_of_lt hl0) (le_of_lt hl1) (by omega)
    have habs : |l ^ (k + 1) - 1| = 1 - l ^ (k + 1) := by
      rw [abs_of_neg (by linarith)]
      ring
    rw [habs]
    linarith

/-- **Separation of the `λ^ℤ`-orbit.** For `0 < l < 1` and `m ≠ n`,
`|l^m - l^n| ≥ l^n (1 - l)`. -/
theorem abs_zpow_sub_zpow_ge {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) {m n : ℤ} (hmn : m ≠ n) :
    l ^ n * (1 - l) ≤ |l ^ m - l ^ n| := by
  have hlne : l ≠ 0 := ne_of_gt hl0
  have hsplit : l ^ m = l ^ n * l ^ (m - n) := by
    rw [← zpow_add₀ hlne]
    congr 1
    ring
  have hjn : m - n ≠ 0 := sub_ne_zero.mpr hmn
  have hposn : 0 < l ^ n := zpow_pos hl0 n
  calc l ^ n * (1 - l) ≤ l ^ n * |l ^ (m - n) - 1| :=
        mul_le_mul_of_nonneg_left (one_sub_le_abs_zpow_sub_one hl0 hl1 hjn) (le_of_lt hposn)
    _ = |l ^ n * (l ^ (m - n) - 1)| := by rw [abs_mul, abs_of_pos hposn]
    _ = |l ^ m - l ^ n| := by rw [mul_sub, mul_one, hsplit]

/-- The norm of a difference of `l`-powers is the absolute value of the real difference. -/
theorem norm_ofReal_zpow_sub {l : ℝ} (m n : ℤ) :
    ‖(l : ℂ) ^ m - (l : ℂ) ^ n‖ = |l ^ m - l ^ n| := by
  have h1 : (l : ℂ) ^ m = ((l ^ m : ℝ) : ℂ) := (Complex.ofReal_zpow l m).symm
  have h2 : (l : ℂ) ^ n = ((l ^ n : ℝ) : ℂ) := (Complex.ofReal_zpow l n).symm
  rw [h1, h2, ← Complex.ofReal_sub]
  exact RCLike.norm_ofReal _

/-! ## Discreteness of the subgroup and the quotient topology -/

/-- **The subgroup `λ^ℤ` is discrete in `ℂ*`.** -/
theorem TorusZ_isDiscrete {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) :
    IsDiscrete ((Subgroup.zpowers (lamU l) : Subgroup ℂˣ) : Set ℂˣ) := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro y hy
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hcpos : 0 < ‖(((lamU l) ^ n : ℂˣ) : ℂ)‖ * (1 - l) / 3 := by
    have h1 : 0 < l ^ n := zpow_pos hl0 n
    exact div_pos (mul_pos (by rw [norm_lamU_zpow hl0 n]; exact h1) (by linarith)) (by norm_num)
  refine ⟨{z : ℂˣ | ‖(z : ℂ) - (((lamU l) ^ n : ℂˣ) : ℂ)‖
      < ‖(((lamU l) ^ n : ℂˣ) : ℂ)‖ * (1 - l) / 3}, ?_, ?_⟩
  · have hcont : Continuous fun z : ℂˣ => ‖(z : ℂ) - (((lamU l) ^ n : ℂˣ) : ℂ)‖ := by
      fun_prop
    exact isOpen_lt hcont continuous_const
  · ext z
    constructor
    · intro hz
      obtain ⟨hz1, hz2⟩ := hz
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz2
      simp only [Set.mem_singleton_iff]
      by_contra hmn
      have hmn' : m ≠ n := fun h => hmn (by rw [h])
      have hz1' : ‖(l : ℂ) ^ m - (l : ℂ) ^ n‖ < l ^ n * (1 - l) / 3 := by
        have h1 : ‖(((lamU l) ^ m : ℂˣ) : ℂ) - (((lamU l) ^ n : ℂˣ) : ℂ)‖
            < ‖(((lamU l) ^ n : ℂˣ) : ℂ)‖ * (1 - l) / 3 := hz1
        rw [norm_lamU_zpow hl0 n] at h1
        rwa [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val,
          lamU_coe (ne_of_gt hl0)] at h1
      rw [norm_ofReal_zpow_sub] at hz1'
      have h1 := abs_zpow_sub_zpow_ge hl0 hl1 hmn'
      have hpos : 0 < l ^ n * (1 - l) := mul_pos (zpow_pos hl0 n) (by linarith)
      linarith
    · intro hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨by simpa using hcpos, Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩⟩

theorem TorusZ_isClosed {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) :
    IsClosed ((Subgroup.zpowers (lamU l) : Subgroup ℂˣ) : Set ℂˣ) :=
  (Subgroup.zpowers (lamU l)).isClosed_of_isDiscrete (TorusZ_isDiscrete hl0 hl1)

theorem TorusZ_t2Space {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) : T2Space (TorusZ l) := by
  haveI : IsClosed ((Subgroup.zpowers (lamU l) : Subgroup ℂˣ) : Set ℂˣ) :=
    TorusZ_isClosed hl0 hl1
  infer_instance

/-- **`ℂ* → ℂ*/λ^ℤ` is a covering map.** -/
theorem TorusZ_isCoveringMap {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) :
    IsCoveringMap (QuotientGroup.mk : ℂˣ → TorusZ l) :=
  (Subgroup.isQuotientCoveringMap_of_comm (Subgroup.zpowers (lamU l))
    (TorusZ_isDiscrete hl0 hl1)).isCoveringMap

/-- The quotient map is invariant under the `λ^ℤ`-shifts. -/
theorem mk_zpow_mul {l : ℝ} (n : ℤ) (z : ℂˣ) :
    (QuotientGroup.mk ((lamU l) ^ n * z : ℂˣ) : TorusZ l) = QuotientGroup.mk (z : ℂˣ) := by
  rw [QuotientGroup.eq]
  have h : ((lamU l) ^ n * z)⁻¹ * z = (lamU l) ^ (-n) := by
    rw [mul_inv_rev, ← zpow_neg]
    rw [mul_comm (z⁻¹), mul_assoc, inv_mul_cancel, mul_one]
  rw [h]
  exact Subgroup.mem_zpowers_iff.mpr ⟨-n, rfl⟩

/-- **Coverings do not create limits**, in the form used here: if a continuous path in `ℂ*`
becomes convergent in the torus `ℂ*/λ^ℤ`, it is convergent in `ℂ*`. -/
theorem exists_tendsto_of_tendsto_mk {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) {u : ℝ → ℂˣ}
    (hu : ContinuousOn u (Set.Iio (1 : ℝ))) {t : TorusZ l}
    (h : Tendsto (fun s : ℝ => (QuotientGroup.mk (u s) : TorusZ l))
      (nhdsWithin 1 (Set.Iio (1 : ℝ))) (nhds t)) :
    ∃ z : ℂˣ, Tendsto u (nhdsWithin 1 (Set.Iio (1 : ℝ))) (nhds z) :=
  exists_tendsto_of_isCoveringMap_comp (TorusZ_isCoveringMap hl0 hl1) hu h

/-! ## Orbit normalisation and compactness -/

/-- **Real orbit normalisation**: for `0 < l < 1`, `x > 0` and `0 < r₁ ≤ l r₂` there is `n : ℤ`
with `r₁ ≤ l^n x ≤ r₂`. -/
theorem exists_zpow_mul_mem_Icc {l x r₁ r₂ : ℝ} (hl0 : 0 < l) (hl1 : l < 1) (hx : 0 < x)
    (hr₁ : 0 < r₁) (hr : r₁ ≤ l * r₂) :
    ∃ n : ℤ, r₁ ≤ l ^ n * x ∧ l ^ n * x ≤ r₂ := by
  have hzero : Tendsto (fun k : ℕ => l ^ k * x) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hl0.le hl1).mul_const x
  by_cases hxk : r₁ ≤ x
  · have hne : ∃ k : ℕ, ¬ (r₁ ≤ l ^ k * x) := by
      obtain ⟨k, hk⟩ := (hzero.eventually (Iio_mem_nhds hr₁)).exists
      exact ⟨k, not_le.mpr hk⟩
    have hspec : ¬ (r₁ ≤ l ^ Nat.find hne * x) := Nat.find_spec hne
    have hfind_ne : Nat.find hne ≠ 0 := by
      rintro h
      rw [h] at hspec
      simp only [pow_zero, one_mul] at hspec
      exact hspec hxk
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hfind_ne
    have hprev : r₁ ≤ l ^ j * x := by
      have hlt : j < Nat.find hne := by omega
      have hmin := Nat.find_min hne hlt
      push Not at hmin
      exact hmin
    rw [hj] at hspec
    refine ⟨(j : ℤ), by rw [zpow_natCast]; exact hprev, ?_⟩
    rw [zpow_natCast]
    have h2 : l * (l ^ j * x) < l * r₂ := by
      rw [show l * (l ^ j * x) = l ^ (j + 1) * x by rw [pow_succ]; ring]
      exact lt_of_lt_of_le (lt_of_not_ge hspec) hr
    have h4 := mul_lt_mul_of_pos_left h2 (inv_pos.mpr hl0)
    simp only [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hl0), one_mul] at h4
    exact le_of_lt h4
  · push Not at hxk
    have hne : ∃ k : ℕ, r₁ * l ^ k ≤ x := by
      have h2 : Tendsto (fun k : ℕ => r₁ * l ^ k) atTop (nhds 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hl0.le hl1).const_mul r₁
      obtain ⟨k, hk⟩ := (h2.eventually (Iio_mem_nhds hx)).exists
      exact ⟨k, le_of_lt hk⟩
    have hspec : r₁ * l ^ Nat.find hne ≤ x := Nat.find_spec hne
    have hfind_ne : Nat.find hne ≠ 0 := by
      rintro h
      rw [h] at hspec
      simp only [pow_zero, mul_one] at hspec
      exact lt_irrefl x (lt_of_lt_of_le hxk hspec)
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hfind_ne
    have hprev : x < r₁ * l ^ j := by
      have hlt : j < Nat.find hne := by omega
      have hmin := Nat.find_min hne hlt
      push Not at hmin
      exact hmin
    rw [hj] at hspec
    refine ⟨-(((j + 1 : ℕ)) : ℤ), ?_, ?_⟩
    · rw [zpow_neg, zpow_natCast, inv_mul_eq_div, le_div_iff₀ (pow_pos hl0 _)]
      exact hspec
    · rw [zpow_neg, zpow_natCast, inv_mul_eq_div, div_le_iff₀ (pow_pos hl0 _)]
      have hl2 : r₁ * l ^ j ≤ r₂ * l ^ (j + 1) := by
        have hpow : (0 : ℝ) < l ^ j := pow_pos hl0 _
        have hr' : r₁ ≤ r₂ * l := by linarith [hr, mul_comm r₂ l]
        calc r₁ * l ^ j ≤ (r₂ * l) * l ^ j := mul_le_mul_of_nonneg_right hr' (le_of_lt hpow)
          _ = r₂ * l ^ (j + 1) := by rw [pow_succ]; ring
      linarith [le_of_lt hprev, hl2]

/-- **Annulus normalisation for the `λ^ℤ`-action.** -/
theorem TorusZ_zpow_mem_annulus {l r₁ r₂ : ℝ} (hl0 : 0 < l) (hl1 : l < 1) (hr₁ : 0 < r₁)
    (hr : r₁ ≤ l * r₂) (z : ℂˣ) :
    ∃ n : ℤ, r₁ ≤ ‖(((lamU l) ^ n * z : ℂˣ) : ℂ)‖ ∧ ‖(((lamU l) ^ n * z : ℂˣ) : ℂ)‖ ≤ r₂ := by
  obtain ⟨n, h1, h2⟩ :=
    exists_zpow_mul_mem_Icc hl0 hl1 (norm_pos_iff.mpr (Units.ne_zero z)) hr₁ hr
  refine ⟨n, ?_, ?_⟩
  · rw [Units.val_mul, norm_mul, norm_lamU_zpow hl0 n]; exact h1
  · rw [Units.val_mul, norm_mul, norm_lamU_zpow hl0 n]; exact h2

/-- **The torus `ℂ*/λ^ℤ` is compact.** -/
theorem TorusZ_compactSpace {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) : CompactSpace (TorusZ l) := by
  have hcomp : IsCompact (annulus l 1 : Set ℂˣ) := by
    have hset : ((Units.val : ℂˣ → ℂ) '' (annulus l 1 : Set ℂˣ))
        = {w : ℂ | l ≤ ‖w‖ ∧ ‖w‖ ≤ 1} := by
      ext w
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨hz.1, hz.2⟩
      · intro hw
        have hwne : w ≠ 0 := by
          rintro rfl
          simp only [Set.mem_setOf_eq, norm_zero] at hw
          exact absurd hw.1 (not_le.mpr hl0)
        exact ⟨Units.mk0 w hwne, by rw [mem_annulus, Units.val_mk0]; exact ⟨hw.1, hw.2⟩,
          Units.val_mk0 _⟩
    have hclosed : IsClosed (((Units.val : ℂˣ → ℂ) '' (annulus l 1 : Set ℂˣ)) : Set ℂ) := by
      rw [hset]
      exact (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
    have hbdd : Bornology.IsBounded (((Units.val : ℂˣ → ℂ) '' (annulus l 1 : Set ℂˣ))
        : Set ℂ) := by
      rw [isBounded_iff_forall_norm_le]
      exact ⟨1, by rintro w ⟨z, hz, rfl⟩; exact hz.2⟩
    have hc : IsCompact (((Units.val : ℂˣ → ℂ) '' (annulus l 1 : Set ℂˣ)) : Set ℂ) :=
      Metric.isCompact_iff_isClosed_bounded.mpr ⟨hclosed, hbdd⟩
    exact (IsEmbedding.isCompact_iff
      (show IsEmbedding (Units.val : ℂˣ → ℂ) from Units.isEmbedding_val₀)).mpr hc
  have himg : (QuotientGroup.mk : ℂˣ → TorusZ l) '' (annulus l 1 : Set ℂˣ) = Set.univ := by
    refine Set.eq_univ_of_forall fun t => ?_
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective t
    obtain ⟨n, h1, h2⟩ :=
      TorusZ_zpow_mem_annulus hl0 hl1 hl0 (by rw [mul_one]) z
    exact ⟨((lamU l) ^ n * z : ℂˣ), ⟨h1, h2⟩, mk_zpow_mul n z⟩
  rw [← isCompact_univ_iff, ← himg]
  exact hcomp.image (QuotientGroup.continuous_mk)

end Work.EQ
