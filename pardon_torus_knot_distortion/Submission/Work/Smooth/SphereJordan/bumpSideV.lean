import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.Jordan.All
import Submission.Work.Smooth.SphereJordan.DiscCurve
import Submission.Work.Smooth.SphereJordan.planeArcSetup
import Submission.Work.Smooth.SphereJordan.thetaPlaneJordanCurve
import Submission.Work.Smooth.SphereJordan.interior_closure_V_eq
import Submission.Work.Smooth.SphereJordan.range_eq_of_subset_of_periodic

namespace Work.Smooth.SphereJordan

noncomputable section

open Set Filter

/-! ## 1. A toolbox for parameterised simple closed curves -/

/-- **Injectivity on any interval shorter than a period.** -/
theorem injOn_Icc_of_periodic {κ : ℝ → ℂ} (hper : Function.Periodic κ (2 * Real.pi))
    (hinj : Set.InjOn κ (Set.Ico 0 (2 * Real.pi))) {a b : ℝ} (hab : b - a < 2 * Real.pi) :
    Set.InjOn κ (Set.Icc a b) := by
  intro u hu v hv huv
  obtain ⟨k, hk⟩ := exists_int_sub_eq_of_periodic_injOn hper hinj huv
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have habs : |u - v| ≤ b - a := by
    rw [abs_sub_le_iff]
    exact ⟨by linarith [hu.2, hv.1], by linarith [hu.1, hv.2]⟩
  have hkabs : |((k : ℝ))| * (2 * Real.pi) = |u - v| := by
    rw [hk, abs_mul, abs_of_pos hπ]
  have hlt : |(k : ℝ)| < 1 := by nlinarith
  have hcast : ((|k| : ℤ) : ℝ) < 1 := by rw [Int.cast_abs]; exact hlt
  have hk1 : (|k| : ℤ) < 1 := by exact_mod_cast hcast
  have hk0 : k = 0 := Int.abs_lt_one_iff.mp hk1
  rw [hk0] at hk
  simp only [Int.cast_zero, zero_mul] at hk
  linarith

/-- **A point strictly inside a subinterval of length less than a period takes a different value
from both ends.** -/
theorem ne_of_Ioo_of_periodic {κ : ℝ → ℂ} (hper : Function.Periodic κ (2 * Real.pi))
    (hinj : Set.InjOn κ (Set.Ico 0 (2 * Real.pi))) {a b x : ℝ} (hxa : a < x) (hxb : x < b)
    (hab : b - a < 2 * Real.pi) : κ x ≠ κ a ∧ κ x ≠ κ b := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  constructor
  · intro h
    obtain ⟨k, hk⟩ := exists_int_sub_eq_of_periodic_injOn hper hinj h
    have hkpos : 0 < k := by
      rcases lt_trichotomy k 0 with h' | h' | h'
      · have h'' : (k : ℝ) < 0 := by exact_mod_cast h'
        nlinarith [hk, hπ, h'']
      · rw [h'] at hk; simp at hk; linarith
      · exact h'
    have hklt : k < 1 := by
      have : (k : ℝ) < 1 := by nlinarith [hk, hπ]
      exact_mod_cast this
    omega
  · intro h
    obtain ⟨k, hk⟩ := exists_int_sub_eq_of_periodic_injOn hper hinj h
    have hkneg : k < 0 := by
      rcases lt_trichotomy k 0 with h' | h' | h'
      · exact h'
      · rw [h'] at hk; simp at hk; linarith
      · have h'' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast h'
        nlinarith [hk, hπ, h'']
    have hkgt : -1 < k := by
      have : (-1 : ℝ) < (k : ℝ) := by nlinarith [hk, hπ]
      exact_mod_cast this
    omega

/-- **The arc `κ '' Icc a b` as a parametrised path on `[0,1]`.** -/
def arcPath {κ : ℝ → ℂ} (hcont : Continuous κ) (a b : ℝ) : C(Set.Icc (0 : ℝ) 1, ℂ) where
  toFun v := κ (a + (v : ℝ) * (b - a))
  continuous_toFun := hcont.comp
    (continuous_const.add (continuous_subtype_val.mul continuous_const))

theorem arcPath_apply {κ : ℝ → ℂ} (hcont : Continuous κ) (a b : ℝ)
    (v : Set.Icc (0 : ℝ) 1) : arcPath hcont a b v = κ (a + (v : ℝ) * (b - a)) := rfl

@[simp] theorem arcPath_zero {κ : ℝ → ℂ} (hcont : Continuous κ) (a b : ℝ) :
    arcPath hcont a b ⟨0, by norm_num⟩ = κ a := by
  simp [arcPath]

@[simp] theorem arcPath_one {κ : ℝ → ℂ} (hcont : Continuous κ) (a b : ℝ) :
    arcPath hcont a b ⟨1, by norm_num⟩ = κ b := by
  simp [arcPath]

theorem range_arcPath {κ : ℝ → ℂ} (hcont : Continuous κ) {a b : ℝ} (hab : a ≤ b) :
    Set.range (arcPath hcont a b) = κ '' Set.Icc a b := by
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨a + (v : ℝ) * (b - a), ⟨?_, ?_⟩, rfl⟩
    · have := v.2.1; nlinarith
    · have := v.2.2; nlinarith
  · rintro ⟨u, hu, rfl⟩
    rcases eq_or_lt_of_le hab with h | h
    · have hu' : u = a := le_antisymm (h.symm ▸ hu.2) hu.1
      refine ⟨⟨0, by norm_num⟩, ?_⟩
      rw [arcPath_zero, hu']
    · refine ⟨⟨(u - a) / (b - a), ⟨?_, ?_⟩⟩, ?_⟩
      · apply div_nonneg <;> linarith [hu.1]
      · rw [div_le_one (by linarith : (0 : ℝ) < b - a)]; linarith [hu.2]
      · rw [arcPath_apply]
        have hbd : b - a ≠ 0 := by linarith
        congr 1
        field_simp
        ring

theorem arcPath_injective {κ : ℝ → ℂ} (hcont : Continuous κ)
    (hper : Function.Periodic κ (2 * Real.pi))
    (hinj : Set.InjOn κ (Set.Ico 0 (2 * Real.pi))) {a b : ℝ} (hab : a < b)
    (hlt : b - a < 2 * Real.pi) : Function.Injective (arcPath hcont a b) := by
  intro u v huv
  have huv' : κ (a + (u : ℝ) * (b - a)) = κ (a + (v : ℝ) * (b - a)) := huv
  have hmemu : a + (u : ℝ) * (b - a) ∈ Set.Icc a b :=
    ⟨by have := u.2.1; nlinarith, by have := u.2.2; nlinarith⟩
  have hmemv : a + (v : ℝ) * (b - a) ∈ Set.Icc a b :=
    ⟨by have := v.2.1; nlinarith, by have := v.2.2; nlinarith⟩
  have heq := injOn_Icc_of_periodic hper hinj hlt hmemu hmemv huv'
  have hbd : b - a ≠ 0 := by linarith
  have h1 : (u : ℝ) * (b - a) = (v : ℝ) * (b - a) := by linarith
  exact Subtype.ext (mul_right_cancel₀ hbd h1)

/-- **A preconnected closed set which contains the two ends of a parametrised arc is the arc.** -/
theorem eq_range_of_subset_of_arc {φ : C(Set.Icc (0 : ℝ) 1, ℂ)} (hφ : Function.Injective φ)
    {A : Set ℂ} (hAclosed : IsClosed A) (hApre : IsPreconnected A)
    (hsub : A ⊆ Set.range φ)
    (h0 : φ ⟨0, by norm_num⟩ ∈ A) (h1 : φ ⟨1, by norm_num⟩ ∈ A) : A = Set.range φ := by
  have hCclosed : IsClosed (φ ⁻¹' A) := hAclosed.preimage φ.continuous
  have hCpre : IsPreconnected (φ ⁻¹' A) := by
    rw [isPreconnected_iff_subset_of_disjoint_closed]
    intro u v hu hv huv hdis
    have hcu : IsCompact (φ ⁻¹' A ∩ u) := (hCclosed.inter hu).isCompact
    have hcv : IsCompact (φ ⁻¹' A ∩ v) := (hCclosed.inter hv).isCompact
    set A₁ : Set ℂ := φ '' (φ ⁻¹' A ∩ u) with hA₁
    set A₂ : Set ℂ := φ '' (φ ⁻¹' A ∩ v) with hA₂
    have hc1 : IsClosed A₁ := (hcu.image φ.continuous).isClosed
    have hc2 : IsClosed A₂ := (hcv.image φ.continuous).isClosed
    have hcover : A ⊆ A₁ ∪ A₂ := by
      intro z hz
      obtain ⟨w, rfl⟩ := hsub hz
      have hwC : w ∈ φ ⁻¹' A := hz
      rcases huv hwC with h | h
      · exact Or.inl ⟨w, ⟨hwC, h⟩, rfl⟩
      · exact Or.inr ⟨w, ⟨hwC, h⟩, rfl⟩
    have hdisj : A ∩ (A₁ ∩ A₂) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨-, ⟨x, ⟨hxC, hxu⟩, hxz⟩, ⟨y, ⟨hyC, hyv⟩, hyz⟩⟩
      have hxy : x = y := hφ (hxz.trans hyz.symm)
      subst hxy
      exact (Set.eq_empty_iff_forall_notMem.mp hdis x) ⟨hxC, hxu, hyv⟩
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hApre A₁ A₂ hc1 hc2 hcover hdisj
      with h | h
    · left
      intro w hw
      by_contra hwu
      have hwv : w ∈ v := by
        rcases huv hw with h' | h'
        · exact absurd h' hwu
        · exact h'
      have hzA : φ w ∈ A := hw
      have hz2 : φ w ∈ A₂ := ⟨w, ⟨hw, hwv⟩, rfl⟩
      have hz1 : φ w ∈ A₁ := h hzA
      exact (Set.eq_empty_iff_forall_notMem.mp hdisj (φ w)) ⟨hzA, hz1, hz2⟩
    · right
      intro w hw
      by_contra hwv
      have hwu : w ∈ u := by
        rcases huv hw with h' | h'
        · exact h'
        · exact absurd h' hwv
      have hzA : φ w ∈ A := hw
      have hz1 : φ w ∈ A₁ := ⟨w, ⟨hw, hwu⟩, rfl⟩
      have hz2 : φ w ∈ A₂ := h hzA
      exact (Set.eq_empty_iff_forall_notMem.mp hdisj (φ w)) ⟨hzA, hz1, hz2⟩
  have hord : (φ ⁻¹' A).OrdConnected := hCpre.ordConnected
  have huniv : φ ⁻¹' A = Set.univ := by
    apply Set.eq_univ_of_forall
    intro w
    exact hord.out h0 h1 (by simp only [Set.mem_Icc]; exact ⟨w.2.1, w.2.2⟩)
  refine Set.Subset.antisymm hsub ?_
  rintro z ⟨w, -, rfl⟩
  show w ∈ φ ⁻¹' A
  rw [huniv]; trivial

/-- **Splitting a simple closed curve along an embedded arc.** -/
theorem arcSplit {κ : ℝ → ℂ} (hcont : Continuous κ)
    (hper : Function.Periodic κ (2 * Real.pi))
    (hinj : Set.InjOn κ (Set.Ico 0 (2 * Real.pi)))
    {δ : C(Set.Icc (0 : ℝ) 1, ℂ)} (hδinj : Function.Injective δ)
    (hδsub : Set.range δ ⊆ Set.range κ)
    {s t : ℝ} (hst : s < t) (hts : t - s < 2 * Real.pi)
    (hs : κ s = δ ⟨0, by norm_num⟩) (ht : κ t = δ ⟨1, by norm_num⟩) :
    (Set.range κ = κ '' Set.Icc s t ∪ κ '' Set.Icc t (s + 2 * Real.pi)) ∧
    (κ '' Set.Icc s t ∩ κ '' Set.Icc t (s + 2 * Real.pi) =
      {δ ⟨0, by norm_num⟩, δ ⟨1, by norm_num⟩}) ∧
    (Set.range δ = κ '' Set.Icc s t ∨ Set.range δ = κ '' Set.Icc t (s + 2 * Real.pi)) ∧
    Set.range δ ≠ Set.range κ := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  -- one full period
  have hperiod : Set.range κ = κ '' Set.Icc s (s + 2 * Real.pi) := by
    apply Set.Subset.antisymm
    · rintro x ⟨u, rfl⟩
      set n : ℤ := ⌊(u - s) / (2 * Real.pi)⌋ with hn
      have h1 : s ≤ u - (n : ℝ) * (2 * Real.pi) := by
        have h := Int.floor_le ((u - s) / (2 * Real.pi))
        have h2 := (le_div_iff₀ hπ).mp h
        nlinarith [h2]
      have h2 : u - (n : ℝ) * (2 * Real.pi) ≤ s + 2 * Real.pi := by
        have h := Int.lt_floor_add_one ((u - s) / (2 * Real.pi))
        have h3 := (div_lt_iff₀ hπ).mp h
        nlinarith [h3]
      refine ⟨u - (n : ℝ) * (2 * Real.pi), ⟨h1, h2⟩, ?_⟩
      have hper' := hper.int_mul n (u - (n : ℝ) * (2 * Real.pi))
      rw [show u - (n : ℝ) * (2 * Real.pi) + (n : ℝ) * (2 * Real.pi) = u by ring] at hper'
      exact hper'.symm
    · rintro x ⟨u, hu, rfl⟩
      exact ⟨u, rfl⟩
  have hIcc : Set.Icc s (s + 2 * Real.pi) = Set.Icc s t ∪ Set.Icc t (s + 2 * Real.pi) := by
    ext u
    constructor
    · intro hu
      by_cases h : u ≤ t
      · exact Or.inl ⟨hu.1, h⟩
      · exact Or.inr ⟨le_of_lt (lt_of_not_ge h), hu.2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, by linarith⟩
      · exact ⟨by linarith, h2⟩
  have hmain : Set.range κ = κ '' Set.Icc s t ∪ κ '' Set.Icc t (s + 2 * Real.pi) := by
    rw [hperiod, hIcc, Set.image_union]
  -- the two halves meet exactly in the two endpoints of the arc
  have hinter : κ '' Set.Icc s t ∩ κ '' Set.Icc t (s + 2 * Real.pi) =
      {δ ⟨0, by norm_num⟩, δ ⟨1, by norm_num⟩} := by
    apply Set.Subset.antisymm
    · rintro x ⟨⟨u, hu, hux⟩, ⟨v, hv, hvx⟩⟩
      have huv : κ u = κ v := hux.trans hvx.symm
      obtain ⟨k, hk⟩ := exists_int_sub_eq_of_periodic_injOn hper hinj huv
      have hku : u - v = (k : ℝ) * (2 * Real.pi) := hk
      have hk0 : k ≤ 0 := by
        have h1 : (k : ℝ) * (2 * Real.pi) ≤ 0 := by rw [← hku]; linarith [hu.2, hv.1]
        have h2 : (k : ℝ) ≤ 0 := by nlinarith [hπ]
        exact_mod_cast h2
      have hk1 : -1 ≤ k := by
        have h1 : -2 * Real.pi ≤ (k : ℝ) * (2 * Real.pi) := by
          rw [← hku]; linarith [hu.1, hv.2]
        have h2 : (-1 : ℝ) ≤ (k : ℝ) := by nlinarith [hπ]
        exact_mod_cast h2
      have hcases : k = 0 ∨ k = -1 := by omega
      rcases hcases with hk' | hk'
      · have huv' : u = v := by rw [hk'] at hku; norm_num at hku; linarith
        have hut : u = t := by linarith [hu.2, hv.1, huv']
        have hx : x = δ ⟨1, by norm_num⟩ := by rw [← hux, hut, ht]
        exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr hx))
      · have hu' : u = s := by
          have h2 : u - v = -2 * Real.pi := by rw [hku, hk']; ring
          linarith [hu.1, hv.2]
        have hx : x = δ ⟨0, by norm_num⟩ := by rw [← hux, hu', hs]
        exact Set.mem_insert_iff.mpr (Or.inl hx)
    · intro x hx
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx
      · rw [hx]
        exact ⟨⟨s, ⟨le_rfl, hst.le⟩, hs⟩,
          ⟨s + 2 * Real.pi, ⟨by linarith, le_rfl⟩, by rw [hper s]; exact hs⟩⟩
      · rw [hx]
        exact ⟨⟨t, ⟨hst.le, le_rfl⟩, ht⟩, ⟨t, ⟨le_rfl, by linarith⟩, ht⟩⟩
  -- the arc is one of the two halves
  have hAeq : Set.range δ \ {δ ⟨0, by norm_num⟩, δ ⟨1, by norm_num⟩} =
      δ '' Set.Ioo (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) ⟨1, by norm_num⟩ := by
    ext x
    constructor
    · rintro ⟨⟨w, rfl⟩, hxw⟩
      have hw0 : w ≠ (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) := by
        intro h; exact hxw (by rw [h]; exact Set.mem_insert_iff.mpr (Or.inl rfl))
      have hw1 : w ≠ (⟨1, by norm_num⟩ : Set.Icc (0 : ℝ) 1) := by
        intro h; exact hxw (by rw [h]; exact Set.mem_insert_iff.mpr (Or.inr rfl))
      have h0 : (0 : ℝ) < (w : ℝ) := lt_of_le_of_ne w.2.1 (fun h => hw0 (Subtype.ext h.symm))
      have h1 : (w : ℝ) < 1 := lt_of_le_of_ne w.2.2 (fun h => hw1 (Subtype.ext h))
      exact ⟨⟨(w : ℝ), ⟨le_of_lt h0, le_of_lt h1⟩⟩, ⟨h0, h1⟩, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      refine ⟨⟨w, rfl⟩, ?_⟩
      intro hcon
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hcon
      rcases hcon with hcon | hcon
      · have h1 : (0 : ℝ) < (w : ℝ) := by simpa using hw.1
        have : (w : ℝ) = 0 := congrArg Subtype.val (hδinj hcon)
        linarith
      · have h2 : (w : ℝ) < 1 := by simpa using hw.2
        have : (w : ℝ) = 1 := congrArg Subtype.val (hδinj hcon)
        linarith
  have hconn : IsPreconnected
      (δ '' Set.Ioo (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) ⟨1, by norm_num⟩) :=
    isPreconnected_Ioo.image (δ : Set.Icc (0 : ℝ) 1 → ℂ) δ.continuous.continuousOn
  have hT1c : IsClosed (κ '' Set.Icc s t) := (isCompact_Icc.image hcont).isClosed
  have hT2c : IsClosed (κ '' Set.Icc t (s + 2 * Real.pi)) := (isCompact_Icc.image hcont).isClosed
  have hsub' : δ '' Set.Ioo (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) ⟨1, by norm_num⟩ ⊆
      κ '' Set.Icc s t ∪ κ '' Set.Icc t (s + 2 * Real.pi) := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := hx
    rw [← hmain]
    exact hδsub ⟨w, rfl⟩
  have hdisj' : δ '' Set.Ioo (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) ⟨1, by norm_num⟩ ∩
      (κ '' Set.Icc s t ∩ κ '' Set.Icc t (s + 2 * Real.pi)) = ∅ := by
    rw [hinter, Set.eq_empty_iff_forall_notMem]
    rintro x ⟨⟨w, hw, rfl⟩, hx⟩
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · have h1 : (0 : ℝ) < (w : ℝ) := by simpa using hw.1
      have : (w : ℝ) = 0 := congrArg Subtype.val (hδinj hx)
      linarith
    · have h2 : (w : ℝ) < 1 := by simpa using hw.2
      have : (w : ℝ) = 1 := congrArg Subtype.val (hδinj hx)
      linarith
  have hthird : Set.range δ = κ '' Set.Icc s t ∨
      Set.range δ = κ '' Set.Icc t (s + 2 * Real.pi) := by
    have hδcomp : IsClosed (Set.range δ) := (isCompact_range δ.continuous).isClosed
    have hδpre : IsPreconnected (Set.range δ) := isPreconnected_range δ.continuous
    have hd0T1 : δ ⟨0, by norm_num⟩ ∈ κ '' Set.Icc s t := by
      have hmem : δ ⟨0, by norm_num⟩ ∈
          κ '' Set.Icc s t ∩ κ '' Set.Icc t (s + 2 * Real.pi) := by
        rw [hinter]; exact Set.mem_insert_iff.mpr (Or.inl rfl)
      exact hmem.1
    have hd1T1 : δ ⟨1, by norm_num⟩ ∈ κ '' Set.Icc s t := by
      have hmem : δ ⟨1, by norm_num⟩ ∈
          κ '' Set.Icc s t ∩ κ '' Set.Icc t (s + 2 * Real.pi) := by
        rw [hinter]; exact Set.mem_insert_iff.mpr (Or.inr rfl)
      exact hmem.1
    have hd0T2 : δ ⟨0, by norm_num⟩ ∈ κ '' Set.Icc t (s + 2 * Real.pi) := by
      have hmem : δ ⟨0, by norm_num⟩ ∈
          κ '' Set.Icc s t ∩ κ '' Set.Icc t (s + 2 * Real.pi) := by
        rw [hinter]; exact Set.mem_insert_iff.mpr (Or.inl rfl)
      exact hmem.2
    have hd1T2 : δ ⟨1, by norm_num⟩ ∈ κ '' Set.Icc t (s + 2 * Real.pi) := by
      have hmem : δ ⟨1, by norm_num⟩ ∈
          κ '' Set.Icc s t ∩ κ '' Set.Icc t (s + 2 * Real.pi) := by
        rw [hinter]; exact Set.mem_insert_iff.mpr (Or.inr rfl)
      exact hmem.2
    have arc_subset : ∀ {T : Set ℂ}, (δ '' Set.Ioo (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1)
        ⟨1, by norm_num⟩ ⊆ T) → δ ⟨0, by norm_num⟩ ∈ T → δ ⟨1, by norm_num⟩ ∈ T →
        Set.range δ ⊆ T := by
      intro T hsubT h0T h1T x hx
      by_cases hx' : x ∈ ({δ ⟨0, by norm_num⟩, δ ⟨1, by norm_num⟩} : Set ℂ)
      · rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
        rcases hx' with h | h
        · rw [h]; exact h0T
        · rw [h]; exact h1T
      · have hmem : x ∈ Set.range δ \ {δ ⟨0, by norm_num⟩, δ ⟨1, by norm_num⟩} := ⟨hx, hx'⟩
        rw [hAeq] at hmem
        exact hsubT hmem
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hconn _ _ hT1c hT2c hsub' hdisj'
      with h1 | h1
    · left
      have hA1 : Set.range δ ⊆ κ '' Set.Icc s t := arc_subset h1 hd0T1 hd1T1
      have h := eq_range_of_subset_of_arc (arcPath_injective hcont hper hinj hst hts) hδcomp hδpre
        (by rw [range_arcPath hcont hst.le]; exact hA1)
        (by rw [arcPath_zero]; exact ⟨⟨0, by norm_num⟩, hs.symm⟩)
        (by rw [arcPath_one]; exact ⟨⟨1, by norm_num⟩, ht.symm⟩)
      rwa [range_arcPath hcont hst.le] at h
    · right
      have hA2 : Set.range δ ⊆ κ '' Set.Icc t (s + 2 * Real.pi) := arc_subset h1 hd0T2 hd1T2
      have hrew : Set.range (arcPath hcont t (s + 2 * Real.pi)) = κ '' Set.Icc t (s + 2 * Real.pi) :=
        range_arcPath hcont (by linarith : t ≤ s + 2 * Real.pi)
      have h := eq_range_of_subset_of_arc
        (arcPath_injective hcont hper hinj (by linarith : t < s + 2 * Real.pi)
          (by linarith : s + 2 * Real.pi - t < 2 * Real.pi))
        hδcomp hδpre (by rw [hrew]; exact hA2)
        (by rw [arcPath_zero]; exact ⟨⟨1, by norm_num⟩, ht.symm⟩)
        (by rw [arcPath_one]; exact ⟨⟨0, by norm_num⟩, hs.symm.trans (hper s).symm⟩)
      rwa [hrew] at h
  have hfour : Set.range δ ≠ Set.range κ := by
    intro hcon
    rcases hthird with h3 | h3
    · have hκT1 : Set.range κ = κ '' Set.Icc s t := hcon.symm.trans h3
      have hw : t < (t + (s + 2 * Real.pi)) / 2 ∧
          (t + (s + 2 * Real.pi)) / 2 < s + 2 * Real.pi := ⟨by linarith, by linarith⟩
      have hne := ne_of_Ioo_of_periodic hper hinj hw.1 hw.2
        (by linarith : (s + 2 * Real.pi) - t < 2 * Real.pi)
      have hne' : κ ((t + (s + 2 * Real.pi)) / 2) ≠ κ s := by
        rw [← hper s]; exact hne.2
      have hmem : κ ((t + (s + 2 * Real.pi)) / 2) ∈
          κ '' Set.Icc s t ∩ κ '' Set.Icc t (s + 2 * Real.pi) :=
        ⟨by rw [← hκT1]; exact ⟨_, rfl⟩,
          ⟨_, ⟨hw.1.le, hw.2.le⟩, rfl⟩⟩
      rw [hinter, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with hmem | hmem
      · exact absurd (hmem.trans hs.symm) hne'
      · exact absurd (hmem.trans ht.symm) hne.1
    · have hκT2 : Set.range κ = κ '' Set.Icc t (s + 2 * Real.pi) := hcon.symm.trans h3
      have hmid : s < (s + t) / 2 ∧ (s + t) / 2 < t := ⟨by linarith, by linarith⟩
      have hne := ne_of_Ioo_of_periodic hper hinj hmid.1 hmid.2 hts
      have hmem : κ ((s + t) / 2) ∈
          κ '' Set.Icc s t ∩ κ '' Set.Icc t (s + 2 * Real.pi) :=
        ⟨⟨_, ⟨hmid.1.le, hmid.2.le⟩, rfl⟩,
          by rw [← hκT2]; exact ⟨_, rfl⟩⟩
      rw [hinter, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with hmem | hmem
      · exact absurd (hmem.trans hs.symm) hne.1
      · exact absurd (hmem.trans ht.symm) hne.2
  exact ⟨hmain, hinter, hthird, hfour⟩

/-- **The complementary arc, when the given arc is the first half.** -/
theorem arcSplit_compl_left {κ : ℝ → ℂ} {δ : C(Set.Icc (0 : ℝ) 1, ℂ)} {s t : ℝ}
    (h1 : Set.range κ = κ '' Set.Icc s t ∪ κ '' Set.Icc t (s + 2 * Real.pi))
    (h2 : κ '' Set.Icc s t ∩ κ '' Set.Icc t (s + 2 * Real.pi) =
      {δ ⟨0, by norm_num⟩, δ ⟨1, by norm_num⟩})
    (hA : Set.range δ = κ '' Set.Icc s t) :
    κ '' Set.Icc t (s + 2 * Real.pi) =
      Set.range κ \ (Set.range δ \ {δ ⟨0, by norm_num⟩, δ ⟨1, by norm_num⟩}) := by
  have hd0 : δ ⟨0, by norm_num⟩ ∈ κ '' Set.Icc t (s + 2 * Real.pi) := by
    have hmem : δ ⟨0, by norm_num⟩ ∈
        κ '' Set.Icc s t ∩ κ '' Set.Icc t (s + 2 * Real.pi) := by
      rw [h2]; exact Set.mem_insert_iff.mpr (Or.inl rfl)
    exact hmem.2
  have hd1 : δ ⟨1, by norm_num⟩ ∈ κ '' Set.Icc t (s + 2 * Real.pi) := by
    have hmem : δ ⟨1, by norm_num⟩ ∈
        κ '' Set.Icc s t ∩ κ '' Set.Icc t (s + 2 * Real.pi) := by
      rw [h2]; exact Set.mem_insert_iff.mpr (Or.inr rfl)
    exact hmem.2
  rw [h1, hA, ← h2]
  ext x
  constructor
  · intro hx
    refine ⟨Or.inr hx, ?_⟩
    rintro ⟨hx1, hx2⟩
    exact hx2 ⟨hx1, hx⟩
  · rintro ⟨hx | hx, hmem⟩
    · by_contra hx2
      exact hmem ⟨hx, fun h => hx2 h.2⟩
    · exact hx

/-- **The complementary arc, when the given arc is the second half.** -/
theorem arcSplit_compl_right {κ : ℝ → ℂ} {δ : C(Set.Icc (0 : ℝ) 1, ℂ)} {s t : ℝ}
    (h1 : Set.range κ = κ '' Set.Icc s t ∪ κ '' Set.Icc t (s + 2 * Real.pi))
    (h2 : κ '' Set.Icc s t ∩ κ '' Set.Icc t (s + 2 * Real.pi) =
      {δ ⟨0, by norm_num⟩, δ ⟨1, by norm_num⟩})
    (hA : Set.range δ = κ '' Set.Icc t (s + 2 * Real.pi)) :
    κ '' Set.Icc s t =
      Set.range κ \ (Set.range δ \ {δ ⟨0, by norm_num⟩, δ ⟨1, by norm_num⟩}) := by
  have hd0 : δ ⟨0, by norm_num⟩ ∈ κ '' Set.Icc s t := by
    have hmem : δ ⟨0, by norm_num⟩ ∈
        κ '' Set.Icc s t ∩ κ '' Set.Icc t (s + 2 * Real.pi) := by
      rw [h2]; exact Set.mem_insert_iff.mpr (Or.inl rfl)
    exact hmem.1
  have hd1 : δ ⟨1, by norm_num⟩ ∈ κ '' Set.Icc s t := by
    have hmem : δ ⟨1, by norm_num⟩ ∈
        κ '' Set.Icc s t ∩ κ '' Set.Icc t (s + 2 * Real.pi) := by
      rw [h2]; exact Set.mem_insert_iff.mpr (Or.inr rfl)
    exact hmem.1
  rw [h1, hA, ← h2]
  ext x
  constructor
  · intro hx
    refine ⟨Or.inl hx, ?_⟩
    rintro ⟨hx2, hx1⟩
    exact hx1 ⟨hx, hx2⟩
  · rintro ⟨hx | hx, hmem⟩
    · exact hx
    · by_contra hx1
      exact hmem ⟨hx, fun h => hx1 h.1⟩

/-- **The reversal of an arc** `v ↦ Q (1-v)`. -/
def revArc (Q : C(Set.Icc (0 : ℝ) 1, ℂ)) : C(Set.Icc (0 : ℝ) 1, ℂ) :=
  ⟨fun v => Q (unitInterval.symm v), Q.continuous.comp unitInterval.continuous_symm⟩

theorem revArc_apply (Q : C(Set.Icc (0 : ℝ) 1, ℂ)) (v : Set.Icc (0 : ℝ) 1) :
    revArc Q v = Q (unitInterval.symm v) := rfl

theorem revArc_zero (Q : C(Set.Icc (0 : ℝ) 1, ℂ)) :
    revArc Q (0 : unitInterval) = Q (1 : unitInterval) := by
  show Q (unitInterval.symm (0 : unitInterval)) = Q (1 : unitInterval)
  rw [unitInterval.symm_zero]

theorem revArc_one (Q : C(Set.Icc (0 : ℝ) 1, ℂ)) :
    revArc Q (1 : unitInterval) = Q (0 : unitInterval) := by
  show Q (unitInterval.symm (1 : unitInterval)) = Q (0 : unitInterval)
  rw [unitInterval.symm_one]

theorem revArc_injective {Q : C(Set.Icc (0 : ℝ) 1, ℂ)} (hQ : Function.Injective Q) :
    Function.Injective (revArc Q) := by
  intro u v huv
  rw [revArc_apply, revArc_apply] at huv
  have h1 : unitInterval.symm u = unitInterval.symm v := hQ huv
  have h2 := congrArg unitInterval.symm h1
  rwa [unitInterval.symm_symm, unitInterval.symm_symm] at h2

theorem range_revArc (Q : C(Set.Icc (0 : ℝ) 1, ℂ)) :
    Set.range (revArc Q) = Set.range Q := by
  have h : (revArc Q : Set.Icc (0 : ℝ) 1 → ℂ) = Q ∘ unitInterval.symm := rfl
  rw [h, Set.range_comp]
  have h2 : Set.range (unitInterval.symm : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1) = Set.univ :=
    Set.range_eq_univ.mpr (fun w => ⟨unitInterval.symm w, unitInterval.symm_symm w⟩)
  rw [h2, Set.image_univ]

/-- **A concatenation of two paths which meet only in the two ends of the loop is a simple closed
plane curve whose trace is the union of the two traces.** -/
theorem exists_curve_of_two_paths {a b : ℂ} {R : Path a b} {S : Path b a}
    (hR : Function.Injective (R : C(Set.Icc (0 : ℝ) 1, ℂ)))
    (hS : Function.Injective (S : C(Set.Icc (0 : ℝ) 1, ℂ)))
    (hdis : Set.range (R : C(Set.Icc (0 : ℝ) 1, ℂ)) ∩
      Set.range (S : C(Set.Icc (0 : ℝ) 1, ℂ)) ⊆ {a, b}) :
    ∃ Γ : Work.Smooth.Jordan.PlaneCurve, Γ.IsSimple ∧
      Γ.trace = Set.range (R : C(Set.Icc (0 : ℝ) 1, ℂ)) ∪
        Set.range (S : C(Set.Icc (0 : ℝ) 1, ℂ)) := by
  have hL : Set.InjOn ((R.trans S : Path a a) : C(Set.Icc (0 : ℝ) 1, ℂ))
      {t : Set.Icc (0 : ℝ) 1 | (t : ℝ) < 1} :=
    path_injOn_trans_loop R S hR hS hdis
  have hp : ((R.trans S : Path a a) : C(Set.Icc (0 : ℝ) 1, ℂ)) ⟨0, by norm_num⟩ =
      ((R.trans S : Path a a) : C(Set.Icc (0 : ℝ) 1, ℂ)) ⟨1, by norm_num⟩ :=
    (Path.source (R.trans S)).trans (Path.target (R.trans S)).symm
  refine ⟨loopCurve ((R.trans S : Path a a) : C(Set.Icc (0 : ℝ) 1, ℂ)) hp,
    loopCurve_isSimple _ _ hL, ?_⟩
  show Set.range (loopCurve ((R.trans S : Path a a) : C(Set.Icc (0 : ℝ) 1, ℂ)) hp).γ = _
  rw [range_loopCurve]
  exact path_range_trans R S

/-- **The frontier of the image of an injective disc map is traced by its boundary curve.** -/
theorem frontier_range_eq_discCurve_trace {f : C(Work.Smooth.SphereJordan.Disc, ℂ)}
    (hf : Function.Injective f) :
    frontier (Set.range f) = Set.range ((discCurve f).γ) := by
  have hfr : frontier (Set.range f) = Set.range f \ openImage f := by
    rw [frontier_eq_closure_inter_closure, (isCompact_range f.continuous).isClosed.closure_eq,
      closure_compl, interior_range_eq_openImage hf, Set.sdiff_eq]
  have hle : ∀ z : Work.Smooth.SphereJordan.Disc, ‖(z : ℂ)‖ ≤ 1 := by
    intro z
    have h := z.2
    rwa [Metric.mem_closedBall, dist_zero_right] at h
  apply Set.Subset.antisymm
  · rw [hfr]
    rintro x ⟨⟨z, rfl⟩, hz⟩
    have hz1 : ‖(z : ℂ)‖ = 1 := by
      by_contra hne
      exact hz ⟨z, lt_of_le_of_ne (hle z) hne, rfl⟩
    obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq z hz1
    exact ⟨θ, by show f (Work.Smooth.Jordan.circlePoint θ) = f z; rw [hθ]⟩
  · rintro x ⟨θ, rfl⟩
    rw [hfr]
    refine ⟨⟨_, rfl⟩, ?_⟩
    rintro ⟨w, hw, hwe⟩
    have hwz : w = Work.Smooth.Jordan.circlePoint θ := hf hwe
    rw [hwz] at hw
    have h2 : ‖((Work.Smooth.Jordan.circlePoint θ : Work.Smooth.SphereJordan.Disc) : ℂ)‖ < 1 := hw
    have h1 : ‖((Work.Smooth.Jordan.circlePoint θ : Work.Smooth.SphereJordan.Disc) : ℂ)‖ = 1 := by
      rw [Work.Smooth.Jordan.circlePoint_coe]
      exact Complex.norm_exp_ofReal_mul_I θ
    linarith

/-- The image of the boundary circle of the spanning embedding is the trace of the curve. -/
theorem circle_image_e_eq_trace {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    S.e '' {z : Work.Smooth.SphereJordan.Disc | ‖(z : ℂ)‖ = 1} = γ.trace := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨θ, rfl⟩ := Work.Smooth.Jordan.exists_circlePoint_eq z hz
    exact ⟨θ, (S.boundary θ).symm⟩
  · rintro _ ⟨θ, rfl⟩
    exact ⟨Work.Smooth.Jordan.circlePoint θ, by
      show ‖((Work.Smooth.Jordan.circlePoint θ : Work.Smooth.SphereJordan.Disc) : ℂ)‖ = 1
      rw [Work.Smooth.Jordan.circlePoint_coe]
      exact Complex.norm_exp_ofReal_mul_I θ, S.boundary θ⟩

/-- A point of the unit circle is in the closure of the half-disc near it. -/
theorem closure_mem_of_norm_eq_one {c : ℂ} (hc : ‖c‖ = 1) {η : ℝ} (hη : 0 < η) :
    c ∈ closure (Metric.ball (0 : ℂ) 1 ∩ Metric.ball c η) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  set s : ℝ := min (min (ε / 2) (η / 2)) (1 / 2) with hs
  have hs0 : 0 < s := lt_min (lt_min (by linarith) (by linarith)) (by norm_num)
  have hsε : s < ε := by
    have h := min_le_left (min (ε / 2) (η / 2)) (1 / 2)
    have h2 := min_le_left (ε / 2) (η / 2)
    linarith
  have hsη : s < η := by
    have h := min_le_left (min (ε / 2) (η / 2)) (1 / 2)
    have h2 := min_le_right (ε / 2) (η / 2)
    linarith
  have hs1 : 0 < 1 - s := by
    have h := min_le_right (min (ε / 2) (η / 2)) (1 / 2)
    linarith
  refine ⟨((1 - s : ℝ) : ℂ) * c, ⟨?_, ?_⟩, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hs1, hc, mul_one]
    linarith
  · rw [Metric.mem_ball, dist_eq_norm]
    have h1 : ((1 - s : ℝ) : ℂ) * c - c = ((- s : ℝ) : ℂ) * c := by push_cast; ring
    rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hs0, hc, mul_one]
    exact hsη
  · rw [dist_comm, dist_eq_norm]
    have h1 : ((1 - s : ℝ) : ℂ) * c - c = ((- s : ℝ) : ℂ) * c := by push_cast; ring
    rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hs0, hc, mul_one]
    exact hsε

/-- **The local separation at an interior point of the glued arc.**

If a ball around `z` meets the two traces `γ.trace` and `frontier (range f)` only inside the glued
arc `range δ` (`hTr`), then a (possibly smaller) ball around `z` meets the bounded side `S.V` only
inside the disc `range f`.

Near `z` the two traces coincide with the glued arc, so both `V` and the disc look locally like the
two sides of one arc.  The half-disc `A` of `V` bounded by the arc is obtained from the spanning
embedding `S.e` and a convex half-disc of the model disc, hence is preconnected; it meets the
interior of the disc (the latter contains points of the interior of the disc arbitrarily close to
`z`) and avoids the frontier of the disc, so it lies on the interior side; and all of `V` near `z`
is contained in `A`. -/
theorem sV_local_aux {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    {f : C(Work.Smooth.SphereJordan.Disc, ℂ)} (hf : Function.Injective f)
    {δ : C(Set.Icc (0 : ℝ) 1, ℂ)} (hδ : Function.Injective δ)
    (hδsub : Set.range δ ⊆ frontier (Set.range f))
    (hδeq : Set.range δ = Set.range f ∩ γ.trace)
    (hside : Set.range f ∩ S.U = ∅)
    {z : ℂ} (hz : z ∈ Set.range δ) (hz0 : z ≠ δ ⟨0, by norm_num⟩)
    (hz1 : z ≠ δ ⟨1, by norm_num⟩)
    (hTr : ∃ ρ : ℝ, 0 < ρ ∧
      Metric.ball z ρ ∩ (γ.trace ∪ frontier (Set.range f)) ⊆ Set.range δ) :
    ∃ ε : ℝ, 0 < ε ∧ S.V ∩ Metric.ball z ε ⊆ Set.range f := by
  classical
  have hzγ : z ∈ γ.trace := (hδeq ▸ hz).2
  have hzfr : z ∈ frontier (Set.range f) := hδsub hz
  have hδsubγ : Set.range δ ⊆ γ.trace := fun x hx => (hδeq ▸ hx).2
  obtain ⟨ρ, hρ, hball⟩ := hTr
  obtain ⟨w₀, hw₀1, hw₀⟩ : ∃ w : Work.Smooth.SphereJordan.Disc, ‖(w : ℂ)‖ = 1 ∧ S.e w = z := by
    have h := circle_image_e_eq_trace S
    rw [← h] at hzγ
    exact hzγ
  obtain ⟨y₀, hy₀1, hy₀⟩ : ∃ y : Work.Smooth.SphereJordan.Disc, ‖(y : ℂ)‖ = 1 ∧ f y = z := by
    rw [frontier_range_eq_discCurve_trace hf] at hzfr
    obtain ⟨θ, hθ⟩ := hzfr
    exact ⟨Work.Smooth.Jordan.circlePoint θ, by
      rw [Work.Smooth.Jordan.circlePoint_coe]
      exact Complex.norm_exp_ofReal_mul_I θ, hθ⟩
  -- a small half-disc of the model disc whose `S.e`-image fits in the ball of radius `ρ`
  obtain ⟨η, hη, hηsub⟩ : ∃ η : ℝ, 0 < η ∧ ∀ u : Work.Smooth.SphereJordan.Disc,
      dist u w₀ < η → dist (S.e u) z < ρ := by
    have hcont : Filter.Tendsto S.e (nhds w₀) (nhds (S.e w₀)) := S.e.continuous.continuousAt
    have hmem : Metric.ball (S.e w₀) ρ ∈ nhds (S.e w₀) := Metric.ball_mem_nhds _ hρ
    obtain ⟨η, hη, hηsub⟩ := Metric.eventually_nhds_iff.mp (hcont hmem)
    refine ⟨η, hη, fun u hu => ?_⟩
    have h1 := hηsub hu
    rw [Metric.mem_ball] at h1
    rwa [hw₀] at h1
  -- the convex half-discs of the plane
  set C₁ : Set ℂ := Metric.ball (0 : ℂ) 1 ∩
    Metric.ball ((w₀ : Work.Smooth.SphereJordan.Disc) : ℂ) η with hC₁def
  set C₂ : Set ℂ := Metric.ball (0 : ℂ) 1 ∩
    Metric.ball ((y₀ : Work.Smooth.SphereJordan.Disc) : ℂ) η with hC₂def
  have hC₁pre : IsPreconnected C₁ :=
    ((convex_ball (0 : ℂ) 1).inter (convex_ball _ _)).isPreconnected
  have hCmem₁ : ∀ x ∈ C₁, x ∈ Metric.closedBall (0 : ℂ) 1 := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_lt (by
      have h := hx.1
      rwa [Metric.mem_ball, dist_zero_right] at h)
  -- the half-disc of `S.V`
  set A : Set ℂ :=
    (fun x : C₁ => S.e (⟨(x : ℂ), hCmem₁ x x.2⟩ : Work.Smooth.SphereJordan.Disc)) ''
      (Set.univ : Set C₁) with hAdef
  have hC₁ne : C₁.Nonempty := by
    refine ⟨((1 - min (η / 2) (1 / 2) / 2 : ℝ) : ℂ) *
      ((w₀ : Work.Smooth.SphereJordan.Disc) : ℂ), ?_, ?_⟩
    · have hs1 : min (η / 2) (1 / 2) ≤ 1 / 2 := min_le_right _ _
      have hm0 : 0 < min (η / 2) (1 / 2) := lt_min (by linarith) (by norm_num)
      have hs2 : (0 : ℝ) < 1 - min (η / 2) (1 / 2) / 2 := by linarith
      rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs2, hw₀1, mul_one]
      linarith
    · have hs2 : min (η / 2) (1 / 2) / 2 < η := by
        have h2 : min (η / 2) (1 / 2) ≤ η / 2 := min_le_left _ _
        linarith
      rw [Metric.mem_ball, dist_eq_norm]
      have h1 : ((1 - min (η / 2) (1 / 2) / 2 : ℝ) : ℂ) *
          ((w₀ : Work.Smooth.SphereJordan.Disc) : ℂ) -
          ((w₀ : Work.Smooth.SphereJordan.Disc) : ℂ) =
          ((- (min (η / 2) (1 / 2) / 2) : ℝ) : ℂ) *
          ((w₀ : Work.Smooth.SphereJordan.Disc) : ℂ) := by push_cast; ring
      rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg]
      rw [abs_of_pos (by
        have : 0 < min (η / 2) (1 / 2) := lt_min (by linarith) (by norm_num)
        linarith)]
      rw [hw₀1, mul_one]
      exact hs2
  have hApre : IsPreconnected A := by
    haveI : ConnectedSpace C₁ := isConnected_iff_connectedSpace.mp ⟨hC₁ne, hC₁pre⟩
    rw [hAdef]
    refine isPreconnected_univ.image _ ?_
    exact (S.e.continuous.comp (Continuous.subtype_mk continuous_subtype_val _)).continuousOn
  have hAsubV : A ⊆ S.V := by
    rintro _ ⟨x, -, rfl⟩
    rw [← Work.Smooth.Jordan.plane_schoenflies_openDisc_eq S]
    exact ⟨(⟨(x : ℂ), hCmem₁ x x.2⟩ : Work.Smooth.SphereJordan.Disc),
      by simpa [Metric.mem_ball, dist_zero_right] using x.2.1, rfl⟩
  have hAsubball : A ⊆ Metric.ball z ρ := by
    rintro _ ⟨x, -, rfl⟩
    refine hηsub _ ?_
    rw [Subtype.dist_eq]
    exact x.2.2
  -- the compactness bound: the far part of the model disc is away from `z`
  have hKcl : IsClosed (S.e '' ((Set.univ : Set Work.Smooth.SphereJordan.Disc) \
      Metric.ball w₀ η)) :=
    ((isCompact_univ.diff Metric.isOpen_ball).image S.e.continuous).isClosed
  have hzK : z ∉ S.e '' ((Set.univ : Set Work.Smooth.SphereJordan.Disc) \
      Metric.ball w₀ η) := by
    rintro ⟨u, hu, huz⟩
    have h1 : S.e u = S.e w₀ := by rw [huz, hw₀]
    have h2 : u = w₀ := S.inj h1
    rw [h2] at hu
    exact hu.2 (Metric.mem_ball_self hη)
  obtain ⟨ρ₁, hρ₁, hball₁⟩ := Metric.isOpen_iff.mp hKcl.isOpen_compl z hzK
  -- the final radius
  set ε : ℝ := min ρ ρ₁ with hεdef
  have hεpos : 0 < ε := lt_min hρ hρ₁
  have hερ : ε ≤ ρ := min_le_left _ _
  have hερ₁ : ε ≤ ρ₁ := min_le_right _ _
  refine ⟨ε, hεpos, ?_⟩
  -- `S.V` near `z` is contained in the half-disc `A`
  have hVsubA : S.V ∩ Metric.ball z ε ⊆ A := by
    rintro y ⟨hyV, hyB⟩
    have hy1 : y ∈ S.e '' {w : Work.Smooth.SphereJordan.Disc | ‖(w : ℂ)‖ < 1} := by
      rw [Work.Smooth.Jordan.plane_schoenflies_openDisc_eq S]
      exact hyV
    obtain ⟨u, hu, huy⟩ := hy1
    have huB : u ∈ Metric.ball w₀ η := by
      by_contra hcon
      have him : S.e u ∈ S.e '' ((Set.univ : Set Work.Smooth.SphereJordan.Disc) \
          Metric.ball w₀ η) := ⟨u, ⟨trivial, hcon⟩, rfl⟩
      have h2 : S.e u ∉ Metric.ball z ρ₁ := fun hmem => hball₁ hmem him
      rw [Metric.mem_ball, not_lt] at h2
      rw [huy] at h2
      have h3 : dist y z < ρ₁ := lt_of_lt_of_le (Metric.mem_ball.mp hyB) hερ₁
      linarith
    have huC₁ : (u : ℂ) ∈ C₁ := by
      rw [hC₁def]
      exact ⟨by rw [Metric.mem_ball, dist_zero_right]; simpa using hu, by
        rw [Metric.mem_ball]; simpa [Subtype.dist_eq] using huB⟩
    refine ⟨(⟨(u : ℂ), huC₁⟩ : C₁), trivial, ?_⟩
    rw [← huy]
  -- `A` avoids the frontier of the disc
  have hAdisj : A ⊆ (frontier (Set.range f))ᶜ := by
    intro y hy
    rw [Set.mem_compl_iff]
    intro hyfr
    have hyδ : y ∈ Set.range δ := hball ⟨hAsubball hy, Or.inr hyfr⟩
    have : y ∈ γ.traceᶜ := by
      rw [← S.union_eq]; exact Or.inr (hAsubV hy)
    exact this (hδsubγ hyδ)
  -- `A` meets the interior of the disc
  have hAmeet : (A ∩ interior (Set.range f)).Nonempty := by
    have hy₀cl : (y₀ : Work.Smooth.SphereJordan.Disc) ∈ closure (Subtype.val ⁻¹' C₂) := by
      have h1 : ((y₀ : Work.Smooth.SphereJordan.Disc) : ℂ) ∈ closure C₂ :=
        closure_mem_of_norm_eq_one hy₀1 hη
      rw [Metric.mem_closure_iff] at h1 ⊢
      intro ε' hε'
      obtain ⟨x, hx1, hx2⟩ := h1 ε' hε'
      have hxmem : x ∈ Metric.closedBall (0 : ℂ) 1 := by
        have hx1' := hx1.1
        rw [Metric.mem_ball, dist_zero_right] at hx1'
        rw [Metric.mem_closedBall, dist_zero_right]
        exact le_of_lt hx1'
      exact ⟨⟨x, hxmem⟩, hx1, by simpa [Subtype.dist_eq] using hx2⟩
    have hzcl : z ∈ closure (f '' (Subtype.val ⁻¹' C₂)) := by
      rw [← hy₀]
      exact image_closure_subset_closure_image f.continuous (s := Subtype.val ⁻¹' C₂)
        ⟨y₀, hy₀cl, rfl⟩
    obtain ⟨w, hwmem, hwball⟩ := Metric.mem_closure_iff.mp hzcl ε hεpos
    have hwint : w ∈ interior (Set.range f) := by
      obtain ⟨y, hy, rfl⟩ := hwmem
      rw [interior_range_eq_openImage hf]
      refine ⟨y, ?_, rfl⟩
      have h := hy.1
      rwa [Metric.mem_ball, dist_zero_right] at h
    have hwγ : w ∉ γ.trace := by
      intro hc
      have hδw : w ∈ Set.range δ := by
        rw [hδeq]
        exact ⟨interior_subset hwint, hc⟩
      have hfr : w ∈ frontier (Set.range f) := hδsub hδw
      rw [frontier] at hfr
      exact hfr.2 hwint
    have hwV : w ∈ S.V := by
      have hmem : w ∈ S.U ∪ S.V := by rwa [S.union_eq]
      rcases hmem with h | h
      · exact absurd ⟨interior_subset hwint, h⟩ (Set.eq_empty_iff_forall_notMem.mp hside w)
      · exact h
    have hwA : w ∈ A := hVsubA ⟨hwV, by rw [Metric.mem_ball, dist_comm]; exact hwball⟩
    exact ⟨w, hwA, hwint⟩
  -- hence `A` lies in the interior of the disc
  have hAint : A ⊆ interior (Set.range f) := by
    have hcover : A ⊆ interior (Set.range f) ∪ (Set.range f)ᶜ := by
      intro x hx
      by_cases hxi : x ∈ interior (Set.range f)
      · exact Or.inl hxi
      · refine Or.inr (fun hxf => ?_)
        exact hAdisj hx (by
          rw [frontier, (isCompact_range f.continuous).isClosed.closure_eq]
          exact ⟨hxf, hxi⟩)
    rcases IsPreconnected.subset_or_subset isOpen_interior
      ((isCompact_range f.continuous).isClosed.isOpen_compl)
      (Set.disjoint_left.mpr (fun x h1 h2 => h2 (interior_subset h1))) hcover hApre with h | h
    · exact h
    · exfalso
      obtain ⟨w, hw1, hw2⟩ := hAmeet
      exact h hw1 (interior_subset hw2)
  exact fun y hy => interior_subset (hAint (hVsubA hy))

/-- **The frontier of the bounded side of a plane Schoenflies datum is the curve.** -/
theorem frontier_V_eq_trace {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) : frontier S.V = γ.trace := by
  have hVsub : S.V ⊆ γ.traceᶜ := by
    intro x hx
    rw [← S.union_eq]
    exact Or.inr hx
  have hcircle : S.e '' {z : Work.Smooth.SphereJordan.Disc | ‖(z : ℂ)‖ = 1} = γ.trace := by
    apply Set.Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      obtain ⟨θ, rfl⟩ := Work.Smooth.Jordan.exists_circlePoint_eq z hz
      exact ⟨θ, (S.boundary θ).symm⟩
    · rintro _ ⟨θ, rfl⟩
      exact ⟨Work.Smooth.Jordan.circlePoint θ, by
        show ‖((Work.Smooth.Jordan.circlePoint θ : Work.Smooth.SphereJordan.Disc) : ℂ)‖ = 1
        rw [Work.Smooth.Jordan.circlePoint_coe]
        exact Complex.norm_exp_ofReal_mul_I θ, S.boundary θ⟩
  have hle : ∀ z : Work.Smooth.SphereJordan.Disc, ‖(z : ℂ)‖ ≤ 1 := by
    intro z
    have h := z.2
    rwa [Metric.mem_closedBall, dist_zero_right] at h
  apply Set.Subset.antisymm
  · rw [S.isOpen_V.frontier_eq]
    rintro x ⟨hxcl, hxV⟩
    rw [← S.range_e] at hxcl
    obtain ⟨z, rfl⟩ := hxcl
    have hz : ‖(z : ℂ)‖ = 1 := by
      by_contra hne
      have hlt : ‖(z : ℂ)‖ < 1 := lt_of_le_of_ne (hle z) hne
      refine hxV ?_
      rw [← Work.Smooth.Jordan.plane_schoenflies_openDisc_eq S]
      exact ⟨z, hlt, rfl⟩
    rw [← hcircle]
    exact ⟨z, hz, rfl⟩
  · intro x hx
    rw [← hcircle] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    rw [S.isOpen_V.frontier_eq]
    refine ⟨?_, ?_⟩
    · rw [← S.range_e]
      exact ⟨z, rfl⟩
    · intro hmem
      rw [← Work.Smooth.Jordan.plane_schoenflies_openDisc_eq S] at hmem
      obtain ⟨w, hw, hwe⟩ := hmem
      have hwz : w = z := S.inj hwe
      rw [hwz] at hw
      have h2 : ‖(z : ℂ)‖ < 1 := hw
      rw [hz] at h2
      exact absurd h2 (by norm_num)

/-- **A bounded open set with frontier in the trace of a simple closed curve is its bounded side.**

The set is clopen in the complement of the trace, hence a union of components; the components of
the complement are the two sides, and the unbounded one is not bounded. -/
theorem eq_boundedSide_of_frontier_subset {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {A : Set ℂ}
    (hAopen : IsOpen A) (hAbdd : Bornology.IsBounded A) (hAne : A.Nonempty)
    (hAsub : A ⊆ γ.traceᶜ) (hAfro : frontier A ⊆ γ.trace) : A = S.V := by
  have hUsub : S.U ⊆ γ.traceᶜ := by
    intro x hx; rw [← S.union_eq]; exact Or.inl hx
  have hVsub : S.V ⊆ γ.traceᶜ := by
    intro x hx; rw [← S.union_eq]; exact Or.inr hx
  have hcl : ∀ x ∈ γ.traceᶜ, x ∈ closure A ↔ x ∈ A := by
    intro x hx
    refine ⟨fun hxc => ?_, fun hxA => subset_closure hxA⟩
    by_contra hxA
    have hxfr : x ∈ frontier A := by
      rw [hAopen.frontier_eq]; exact ⟨hxc, hxA⟩
    exact hx (hAfro hxfr)
  have hUdisj : S.U ∩ A = ∅ := by
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp S.preconn_U (closure A) Aᶜ
      (isClosed_closure : IsClosed (closure A)) hAopen.isClosed_compl (by
        intro y hy
        by_cases hyA : y ∈ A
        · exact Or.inl (subset_closure hyA)
        · exact Or.inr hyA) (by
          rw [Set.eq_empty_iff_forall_notMem]
          rintro y ⟨hyU, hyc, hyA⟩
          exact hyA ((hcl y (hUsub hyU)).mp hyc)) with h | h
    · -- `S.U ⊆ closure A`, hence `S.U ⊆ A`; but `S.U` is unbounded and `A` is not
      exfalso
      have hUA : S.U ⊆ A := fun y hy => (hcl y (hUsub hy)).mp (h hy)
      obtain ⟨r, hr⟩ := hAbdd.subset_closedBall (0 : ℂ)
      obtain ⟨y, hyU, hyr⟩ :=
        Work.Smooth.Jordan.plane_separation_unbounded S.toPlaneSeparation (r + 1)
      have : ‖y‖ ≤ r := by
        have hyr' := hr (hUA hyU)
        rwa [Metric.mem_closedBall, dist_zero_right] at hyr'
      linarith
    · rw [Set.eq_empty_iff_forall_notMem]
      rintro y ⟨hyU, hyA⟩
      exact h hyU hyA
  have hAV : A ⊆ S.V := by
    intro x hxA
    have hxT : x ∈ γ.traceᶜ := hAsub hxA
    rw [← S.union_eq] at hxT
    rcases hxT with hxU | hxV
    · exfalso
      have : x ∈ S.U ∩ A := ⟨hxU, hxA⟩
      rw [hUdisj] at this
      exact this
    · exact hxV
  have hVA : S.V ⊆ A := by
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp S.preconn_V (closure A) Aᶜ
      (isClosed_closure : IsClosed (closure A)) hAopen.isClosed_compl (by
        intro y hy
        by_cases hyA : y ∈ A
        · exact Or.inl (subset_closure hyA)
        · exact Or.inr hyA) (by
          rw [Set.eq_empty_iff_forall_notMem]
          rintro y ⟨hyV, hyc, hyA⟩
          exact hyA ((hcl y (hVsub hyV)).mp hyc)) with h | h
    · intro y hyV
      exact (hcl y (hVsub hyV)).mp (h hyV)
    · exfalso
      rcases hAne with ⟨x, hx⟩
      exact (h (hAV hx)) hx
  exact Set.Subset.antisymm hAV hVA

/-- **Two arcs meeting exactly in their two endpoints form a simple closed plane curve.** -/
theorem exists_simple_curve_of_two_arcs {P Q : C(Set.Icc (0 : ℝ) 1, ℂ)}
    (hP : Function.Injective P) (hQ : Function.Injective Q)
    (hdisj : Set.range P ∩ Set.range Q = {P ⟨0, by norm_num⟩, P ⟨1, by norm_num⟩})
    (hQe : ({Q (0 : unitInterval), Q (1 : unitInterval)} : Set ℂ) =
      {P (0 : unitInterval), P (1 : unitInterval)}) :
    ∃ Γ : Work.Smooth.Jordan.PlaneCurve, Γ.IsSimple ∧ Γ.trace = Set.range P ∪ Set.range Q := by
  have hP01 : P (0 : unitInterval) ≠ P (1 : unitInterval) := by
    intro h; exact absurd (hP h) (by simp)
  have hQ0 : Q (0 : unitInterval) ∈
      ({P (0 : unitInterval), P (1 : unitInterval)} : Set ℂ) := hQe ▸ Set.mem_insert _ _
  have hQ1 : Q (1 : unitInterval) ∈
      ({P (0 : unitInterval), P (1 : unitInterval)} : Set ℂ) :=
    hQe ▸ Set.mem_insert_of_mem _ rfl
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hQ0 hQ1
  rcases hQ0 with hA0 | hB0
  · -- `Q 0 = P 0`: traverse `Q` backwards
    have hB1 : Q (1 : unitInterval) = P (1 : unitInterval) := by
      rcases hQ1 with h | h
      · exfalso
        have : Q (1 : unitInterval) = Q (0 : unitInterval) := h.trans hA0.symm
        exact absurd (hQ this) (by simp)
      · exact h
    obtain ⟨Γ, hsimple, htrace⟩ :=
      exists_curve_of_two_paths (R := (⟨P, rfl, rfl⟩ : Path (P (0 : unitInterval))
        (P (1 : unitInterval)))) (S := (⟨revArc Q, by simpa using (revArc_zero Q).trans hB1,
        by simpa using (revArc_one Q).trans hA0⟩ : Path (P (1 : unitInterval))
        (P (0 : unitInterval)))) hP (revArc_injective hQ) (by
          intro x hx
          have hmem : x ∈ Set.range P ∩ Set.range Q :=
            ⟨hx.1, by rw [← range_revArc Q]; exact hx.2⟩
          exact hdisj ▸ hmem)
    exact ⟨Γ, hsimple, by simpa [range_revArc] using htrace⟩
  · -- `Q 0 = P 1`: traverse `Q` directly
    have hA1 : Q (1 : unitInterval) = P (0 : unitInterval) := by
      rcases hQ1 with h | h
      · exact h
      · exfalso
        have : Q (1 : unitInterval) = Q (0 : unitInterval) := h.trans hB0.symm
        exact absurd (hQ this) (by simp)
    obtain ⟨Γ, hsimple, htrace⟩ :=
      exists_curve_of_two_paths (R := (⟨P, rfl, rfl⟩ : Path (P (0 : unitInterval))
        (P (1 : unitInterval)))) (S := (⟨Q, hB0, hA1⟩ : Path (P (1 : unitInterval))
        (P (0 : unitInterval)))) hP hQ (by
          intro x hx
          have hmem : x ∈ Set.range P ∩ Set.range Q := ⟨hx.1, hx.2⟩
          exact hdisj ▸ hmem)
    exact ⟨Γ, hsimple, by simpa using htrace⟩

/-- **Two distinct points of a parametrised closed curve are joined by a pair of parameters**
`(s,t)` with `s < t` and `t - s < 2π`. -/
theorem exists_param_pair {κ : ℝ → ℂ} (hper : Function.Periodic κ (2 * Real.pi))
    {p q : ℂ} (hp : p ∈ Set.range κ) (hq : q ∈ Set.range κ) (hpq : p ≠ q) :
    ∃ s t : ℝ, s < t ∧ t - s < 2 * Real.pi ∧ κ s = p ∧ κ t = q := by
  obtain ⟨s₀, hs₀⟩ := hp
  obtain ⟨t₀, ht₀⟩ := hq
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  set n : ℤ := ⌊(t₀ - s₀) / (2 * Real.pi)⌋ with hn
  set t : ℝ := t₀ - (n : ℝ) * (2 * Real.pi) with ht
  have htq : κ t = q := by
    have h1 : κ t = κ t₀ := by
      have := (hper.int_mul n t).symm
      rwa [show t + (n : ℝ) * (2 * Real.pi) = t₀ by rw [ht]; ring] at this
    exact h1.trans ht₀
  have hle : s₀ ≤ t := by
    have h := Int.floor_le ((t₀ - s₀) / (2 * Real.pi))
    have h2 := (le_div_iff₀ hπ).mp h
    rw [ht]
    nlinarith [h2]
  have hlt : t < s₀ + 2 * Real.pi := by
    have h := Int.lt_floor_add_one ((t₀ - s₀) / (2 * Real.pi))
    have h2 := (div_lt_iff₀ hπ).mp h
    rw [ht]
    nlinarith [h2]
  refine ⟨s₀, t, ?_, ?_, hs₀, htq⟩
  · rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      refine hpq ?_
      rw [← hs₀, ← htq, h]
  · linarith

/-- **Removing a disc glued to the bounded side of a Jordan curve along an arc.** -/
theorem bumpSideV (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    {γ : Work.Smooth.Jordan.PlaneCurve} (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    {f : C(Work.Smooth.SphereJordan.Disc, ℂ)} (hf : Function.Injective f)
    {δ : C(Set.Icc (0 : ℝ) 1, ℂ)} (hδ : Function.Injective δ)
    (hδsub : Set.range δ ⊆ frontier (Set.range f))
    (hδeq : Set.range δ = Set.range f ∩ γ.trace)
    (hside : Set.range f ∩ S.U = ∅) :
    ∃ (Γ : Work.Smooth.Jordan.PlaneCurve) (S' : Work.Smooth.Jordan.PlaneSchoenflies Γ),
      (S'.V = S.V \ Set.range f) ∧ (γ.trace \ frontier (Set.range f) ⊆ Γ.trace) ∧
      (Γ.trace ⊆ γ.trace ∪ frontier (Set.range f)) := by
  classical
  have hγsimple : γ.IsSimple := S.simple
  have hpq : δ ⟨0, by norm_num⟩ ≠ δ ⟨1, by norm_num⟩ := by
    intro hcon
    exact absurd (hδ hcon) (by simp)
  have hfr : frontier (Set.range f) = Set.range ((discCurve f).γ) :=
    frontier_range_eq_discCurve_trace hf
  have hδsubγ : Set.range δ ⊆ γ.trace := fun x hx => (hδeq ▸ hx).2
  have hfrsub : frontier (Set.range f) ⊆ Set.range f :=
    (isCompact_range f.continuous).isClosed.frontier_subset
  have hγfr : γ.trace ∩ frontier (Set.range f) = Set.range δ := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro x ⟨hx1, hx2⟩
      rw [hδeq]
      exact ⟨hfrsub hx2, hx1⟩
    · intro x hx
      exact ⟨hδsubγ hx, hδsub hx⟩
  -- the two arc decompositions
  obtain ⟨a, b, hab, hablt, ha, hb⟩ := exists_param_pair (discCurve f).periodic
    (by rw [← hfr]; exact hδsub ⟨⟨0, by norm_num⟩, rfl⟩)
    (by rw [← hfr]; exact hδsub ⟨⟨1, by norm_num⟩, rfl⟩) hpq
  obtain ⟨s, t, hst, hts, hs, ht⟩ := exists_param_pair γ.periodic
    (hδsubγ ⟨⟨0, by norm_num⟩, rfl⟩) (hδsubγ ⟨⟨1, by norm_num⟩, rfl⟩) hpq
  obtain ⟨hfκ, hfint, hfarc, _⟩ := arcSplit (discCurve f).cont (discCurve f).periodic
    (discCurve_isSimple hf) hδ (by rw [← hfr]; exact hδsub) hab hablt ha hb
  obtain ⟨hgκ, hgint, hgarc, hgne⟩ := arcSplit γ.cont γ.periodic hγsimple hδ hδsubγ hst hts hs ht
  -- the two complementary arcs
  obtain ⟨P, Q, hPinj, hQinj, hPrange, hQrange, hPe, hQe⟩ :
      ∃ (P Q : C(Set.Icc (0 : ℝ) 1, ℂ)), Function.Injective P ∧ Function.Injective Q ∧
        Set.range P = γ.trace \ (Set.range δ \ {δ ⟨0, by norm_num⟩, δ ⟨1, by norm_num⟩}) ∧
        Set.range Q = frontier (Set.range f) \
          (Set.range δ \ {δ ⟨0, by norm_num⟩, δ ⟨1, by norm_num⟩}) ∧
        ({P ⟨0, by norm_num⟩, P ⟨1, by norm_num⟩} : Set ℂ) =
          {δ ⟨0, by norm_num⟩, δ ⟨1, by norm_num⟩} ∧
        ({Q ⟨0, by norm_num⟩, Q ⟨1, by norm_num⟩} : Set ℂ) =
          {δ ⟨0, by norm_num⟩, δ ⟨1, by norm_num⟩} := by
    rcases hfarc with hfT1 | hfT2
    · rcases hgarc with hgT1 | hgT2
      · refine ⟨arcPath γ.cont t (s + 2 * Real.pi), arcPath (discCurve f).cont b (a + 2 * Real.pi),
          arcPath_injective γ.cont γ.periodic hγsimple (by linarith) (by linarith),
          arcPath_injective (discCurve f).cont (discCurve f).periodic (discCurve_isSimple hf)
            (by linarith) (by linarith), ?_, ?_, ?_, ?_⟩
        · rw [range_arcPath γ.cont (by linarith : t ≤ s + 2 * Real.pi)]
          exact arcSplit_compl_left hgκ hgint hgT1
        · rw [range_arcPath (discCurve f).cont (by linarith : b ≤ a + 2 * Real.pi), hfr]
          exact arcSplit_compl_left hfκ hfint hfT1
        · have h0 : (arcPath γ.cont t (s + 2 * Real.pi)) ⟨0, by norm_num⟩ = δ ⟨1, by norm_num⟩ := by
            rw [arcPath_zero]; exact ht
          have h1 : (arcPath γ.cont t (s + 2 * Real.pi)) ⟨1, by norm_num⟩ = δ ⟨0, by norm_num⟩ := by
            rw [arcPath_one, γ.periodic s]; exact hs
          rw [h0, h1, Set.pair_comm]
        · have h0 : (arcPath (discCurve f).cont b (a + 2 * Real.pi)) ⟨0, by norm_num⟩ =
              δ ⟨1, by norm_num⟩ := by rw [arcPath_zero]; exact hb
          have h1 : (arcPath (discCurve f).cont b (a + 2 * Real.pi)) ⟨1, by norm_num⟩ =
              δ ⟨0, by norm_num⟩ := by
            rw [arcPath_one, (discCurve f).periodic a]; exact ha
          rw [h0, h1, Set.pair_comm]
      · refine ⟨arcPath γ.cont s t, arcPath (discCurve f).cont b (a + 2 * Real.pi),
          arcPath_injective γ.cont γ.periodic hγsimple hst hts,
          arcPath_injective (discCurve f).cont (discCurve f).periodic (discCurve_isSimple hf)
            (by linarith) (by linarith), ?_, ?_, ?_, ?_⟩
        · rw [range_arcPath γ.cont hst.le]
          exact arcSplit_compl_right hgκ hgint hgT2
        · rw [range_arcPath (discCurve f).cont (by linarith : b ≤ a + 2 * Real.pi), hfr]
          exact arcSplit_compl_left hfκ hfint hfT1
        · have h0 : (arcPath γ.cont s t) ⟨0, by norm_num⟩ = δ ⟨0, by norm_num⟩ := by
            rw [arcPath_zero]; exact hs
          have h1 : (arcPath γ.cont s t) ⟨1, by norm_num⟩ = δ ⟨1, by norm_num⟩ := by
            rw [arcPath_one]; exact ht
          rw [h0, h1]
        · have h0 : (arcPath (discCurve f).cont b (a + 2 * Real.pi)) ⟨0, by norm_num⟩ =
              δ ⟨1, by norm_num⟩ := by rw [arcPath_zero]; exact hb
          have h1 : (arcPath (discCurve f).cont b (a + 2 * Real.pi)) ⟨1, by norm_num⟩ =
              δ ⟨0, by norm_num⟩ := by
            rw [arcPath_one, (discCurve f).periodic a]; exact ha
          rw [h0, h1, Set.pair_comm]
    · rcases hgarc with hgT1 | hgT2
      · refine ⟨arcPath γ.cont t (s + 2 * Real.pi), arcPath (discCurve f).cont a b,
          arcPath_injective γ.cont γ.periodic hγsimple (by linarith) (by linarith),
          arcPath_injective (discCurve f).cont (discCurve f).periodic (discCurve_isSimple hf)
            hab hablt, ?_, ?_, ?_, ?_⟩
        · rw [range_arcPath γ.cont (by linarith : t ≤ s + 2 * Real.pi)]
          exact arcSplit_compl_left hgκ hgint hgT1
        · rw [range_arcPath (discCurve f).cont hab.le, hfr]
          exact arcSplit_compl_right hfκ hfint hfT2
        · have h0 : (arcPath γ.cont t (s + 2 * Real.pi)) ⟨0, by norm_num⟩ = δ ⟨1, by norm_num⟩ := by
            rw [arcPath_zero]; exact ht
          have h1 : (arcPath γ.cont t (s + 2 * Real.pi)) ⟨1, by norm_num⟩ = δ ⟨0, by norm_num⟩ := by
            rw [arcPath_one, γ.periodic s]; exact hs
          rw [h0, h1, Set.pair_comm]
        · have h0 : (arcPath (discCurve f).cont a b) ⟨0, by norm_num⟩ = δ ⟨0, by norm_num⟩ := by
            rw [arcPath_zero]; exact ha
          have h1 : (arcPath (discCurve f).cont a b) ⟨1, by norm_num⟩ = δ ⟨1, by norm_num⟩ := by
            rw [arcPath_one]; exact hb
          rw [h0, h1]
      · refine ⟨arcPath γ.cont s t, arcPath (discCurve f).cont a b,
          arcPath_injective γ.cont γ.periodic hγsimple hst hts,
          arcPath_injective (discCurve f).cont (discCurve f).periodic (discCurve_isSimple hf)
            hab hablt, ?_, ?_, ?_, ?_⟩
        · rw [range_arcPath γ.cont hst.le]
          exact arcSplit_compl_right hgκ hgint hgT2
        · rw [range_arcPath (discCurve f).cont hab.le, hfr]
          exact arcSplit_compl_right hfκ hfint hfT2
        · have h0 : (arcPath γ.cont s t) ⟨0, by norm_num⟩ = δ ⟨0, by norm_num⟩ := by
            rw [arcPath_zero]; exact hs
          have h1 : (arcPath γ.cont s t) ⟨1, by norm_num⟩ = δ ⟨1, by norm_num⟩ := by
            rw [arcPath_one]; exact ht
          rw [h0, h1]
        · have h0 : (arcPath (discCurve f).cont a b) ⟨0, by norm_num⟩ = δ ⟨0, by norm_num⟩ := by
            rw [arcPath_zero]; exact ha
          have h1 : (arcPath (discCurve f).cont a b) ⟨1, by norm_num⟩ = δ ⟨1, by norm_num⟩ := by
            rw [arcPath_one]; exact hb
          rw [h0, h1]
  have hPQeq : Set.range P ∩ Set.range Q =
      {δ ⟨0, by norm_num⟩, δ ⟨1, by norm_num⟩} := by
    rw [hPrange, hQrange]
    have hinter : ∀ {u v : Set ℂ}, (γ.trace \ u) ∩ (v \ u) = (γ.trace ∩ v) \ u := by
      intro u v
      ext x
      simp only [Set.mem_inter_iff, Set.mem_diff]
      tauto
    rw [hinter, hγfr]
    ext x
    constructor
    · rintro ⟨hx, hxA⟩
      by_contra hx'
      exact hxA ⟨hx, hx'⟩
    · intro hx
      refine ⟨?_, ?_⟩
      · rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with hx | hx
        · rw [hx]; exact ⟨⟨0, by norm_num⟩, rfl⟩
        · rw [hx]; exact ⟨⟨1, by norm_num⟩, rfl⟩
      · rintro ⟨-, hcon⟩
        exact hcon (by rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx; exact hx)
  have hdisj : Set.range P ∩ Set.range Q = {P ⟨0, by norm_num⟩, P ⟨1, by norm_num⟩} := by
    rw [hPQeq, hPe]
  have hQe' : ({Q ⟨0, by norm_num⟩, Q ⟨1, by norm_num⟩} : Set ℂ) =
      {P ⟨0, by norm_num⟩, P ⟨1, by norm_num⟩} := by
    rw [hQe, hPe]
  obtain ⟨Γ, hΓsimple, hΓtrace⟩ := exists_simple_curve_of_two_arcs hPinj hQinj hdisj hQe'
  have hΓtr : Γ.trace = (γ.trace \
      (Set.range δ \ {δ ⟨0, by norm_num⟩, δ ⟨1, by norm_num⟩})) ∪
      (frontier (Set.range f) \ (Set.range δ \ {δ ⟨0, by norm_num⟩, δ ⟨1, by norm_num⟩})) := by
    rw [hΓtrace, hPrange, hQrange]
  obtain ⟨S'⟩ := h Γ hΓsimple
  -- basic inclusions for the new curve
  have hA0sub : Set.range δ \ {δ ⟨0, by norm_num⟩, δ ⟨1, by norm_num⟩} ⊆ frontier (Set.range f) :=
    fun x hx => hδsub hx.1
  have hγδΓ : γ.trace \ Set.range δ ⊆ Γ.trace := by
    intro x hx
    rw [hΓtr]
    exact Or.inl ⟨hx.1, fun hcon => hx.2 hcon.1⟩
  -- the geometric input: the bounded side of the new curve is the old one minus the disc
  set W : Set ℂ := S.V \ Set.range f with hWdef
  have hWopen : IsOpen W := S.isOpen_V.sdiff (isCompact_range f.continuous).isClosed
  have hWbdd : Bornology.IsBounded W := S.bounded_V.subset (Set.sdiff_subset)
  have hWsub : W ⊆ Γ.traceᶜ := by
    intro x hx
    rw [Set.mem_compl_iff]
    intro hxΓ
    rcases (hΓtr ▸ hxΓ) with hx' | hx'
    · have : x ∈ γ.traceᶜ := by rw [← S.union_eq]; exact Or.inr hx.1
      exact this hx'.1
    · exact hx.2 (hfrsub hx'.1)
  -- the two traces decompose as the corresponding complementary arc plus the glued arc
  have hγdecomp : γ.trace = Set.range P ∪ Set.range δ := by
    refine Set.Subset.antisymm ?_ ?_
    · intro y hy
      by_cases hyA : y ∈ Set.range δ \ {δ ⟨0, by norm_num⟩, δ ⟨1, by norm_num⟩}
      · exact Or.inr hyA.1
      · exact Or.inl (by rw [hPrange]; exact ⟨hy, hyA⟩)
    · rintro y (hy | hy)
      · rw [hPrange] at hy; exact hy.1
      · exact hδsubγ hy
  have hfrdecomp : frontier (Set.range f) = Set.range Q ∪ Set.range δ := by
    refine Set.Subset.antisymm ?_ ?_
    · intro y hy
      by_cases hyA : y ∈ Set.range δ \ {δ ⟨0, by norm_num⟩, δ ⟨1, by norm_num⟩}
      · exact Or.inr hyA.1
      · exact Or.inl (by rw [hQrange]; exact ⟨hy, hyA⟩)
    · rintro y (hy | hy)
      · rw [hQrange] at hy; exact hy.1
      · exact hδsub hy
  -- the interior of the glued arc is disjoint from the closure of `W`
  have hAarcclW : (Set.range δ \ {δ ⟨0, by norm_num⟩, δ ⟨1, by norm_num⟩}) ∩
      closure W = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hzA, hzcl⟩
    obtain ⟨hzδ, hz01⟩ := hzA
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz01
    have hzP : z ∉ Set.range P := by
      intro hz
      rw [hPrange] at hz
      exact hz.2 ⟨hzδ, hz01⟩
    have hzQ : z ∉ Set.range Q := by
      intro hz
      rw [hQrange] at hz
      exact hz.2 ⟨hzδ, hz01⟩
    have hopen : IsOpen ((Set.range P ∪ Set.range Q)ᶜ) :=
      ((isCompact_range P.continuous).isClosed.union
        (isCompact_range Q.continuous).isClosed).isOpen_compl
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hopen z (fun h => h.elim hzP hzQ)
    have hTr : ∃ ρ : ℝ, 0 < ρ ∧
        Metric.ball z ρ ∩ (γ.trace ∪ frontier (Set.range f)) ⊆ Set.range δ := by
      refine ⟨ρ, hρ, fun y hy => ?_⟩
      have hy' : y ∈ (Set.range P ∪ Set.range δ) ∪ (Set.range Q ∪ Set.range δ) := by
        rw [← hγdecomp, ← hfrdecomp]
        exact hy.2
      rcases hy' with (hP | hd) | (hQ | hd)
      · exact absurd (Or.inl hP) (hρsub hy.1)
      · exact hd
      · exact absurd (Or.inr hQ) (hρsub hy.1)
      · exact hd
    obtain ⟨ε, hε, hεsub⟩ :=
      sV_local_aux S hf hδ hδsub hδeq hside hzδ (fun h => hz01 (Or.inl h))
        (fun h => hz01 (Or.inr h)) hTr
    have hempty : Metric.ball z ε ∩ W = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro y ⟨hyb, hyV, hyf⟩
      exact hyf (hεsub ⟨hyV, hyb⟩)
    obtain ⟨y, hyW, hyb⟩ := Metric.mem_closure_iff.mp hzcl ε hε
    have hyball : y ∈ Metric.ball z ε := by
      rw [Metric.mem_ball, dist_comm]
      exact hyb
    have : y ∈ Metric.ball z ε ∩ W := ⟨hyball, hyW⟩
    rw [hempty] at this
    exact this
  have hWfront : frontier W ⊆ Γ.trace := by
    intro x hx
    rw [hWopen.frontier_eq] at hx
    obtain ⟨hxcl, hxW⟩ := hx
    have hxcl' : x ∈ S.V ∪ γ.trace := by
      have h2 : closure S.V = S.V ∪ γ.trace := by
        rw [closure_eq_interior_union_frontier, S.isOpen_V.interior_eq, frontier_V_eq_trace S]
      exact h2 ▸ closure_mono (Set.sdiff_subset) hxcl
    have hnotint : x ∉ interior (Set.range f) := by
      have hsubW : W ⊆ (interior (Set.range f))ᶜ :=
        fun y hy => fun hc => hy.2 (interior_subset hc)
      exact closure_minimal hsubW isOpen_interior.isClosed_compl hxcl
    have hxA : x ∉ Set.range δ \ {δ ⟨0, by norm_num⟩, δ ⟨1, by norm_num⟩} :=
      fun hA => (Set.eq_empty_iff_forall_notMem.mp hAarcclW x) ⟨hA, hxcl⟩
    rcases hxcl' with hxV | hxγ
    · have hxf : x ∈ Set.range f := by
        by_contra hcon
        exact hxW ⟨hxV, hcon⟩
      have hxfr : x ∈ frontier (Set.range f) := by
        have h2 : Set.range f = interior (Set.range f) ∪ frontier (Set.range f) := by
          rw [← closure_eq_interior_union_frontier,
            (isCompact_range f.continuous).isClosed.closure_eq]
        rcases (h2 ▸ hxf : x ∈ _) with h | h
        · exact absurd h hnotint
        · exact h
      rw [hΓtr]
      exact Or.inr ⟨hxfr, hxA⟩
    · rw [hΓtr]
      exact Or.inl ⟨hxγ, hxA⟩
  have hUsubΓ : S.U ⊆ Γ.traceᶜ := by
    intro x hx
    rw [Set.mem_compl_iff]
    intro hxΓ
    rcases (hΓtr ▸ hxΓ) with hx' | hx'
    · have : x ∈ γ.traceᶜ := by rw [← S.union_eq]; exact Or.inl hx
      exact this hx'.1
    · exact (Set.eq_empty_iff_forall_notMem.mp hside x) ⟨hfrsub hx'.1, hx⟩
  have hSU : S.U ⊆ S'.U := by
    rcases Work.Smooth.Jordan.plane_separation_preconnected_subset S'.toPlaneSeparation
      S.preconn_U hUsubΓ with h' | h'
    · exact h'
    · exfalso
      obtain ⟨r, hr⟩ := S'.bounded_V.subset_closedBall (0 : ℂ)
      obtain ⟨y, hyU, hyr⟩ :=
        Work.Smooth.Jordan.plane_separation_unbounded S.toPlaneSeparation (r + 1)
      have hyr' : ‖y‖ ≤ r := by
        have := hr (h' hyU)
        rwa [Metric.mem_closedBall, dist_zero_right] at this
      linarith
  have hWne : W.Nonempty := by
    obtain ⟨z, hzγ, hzδ⟩ : ∃ z, z ∈ γ.trace ∧ z ∉ Set.range δ := by
      have hnot : ¬ γ.trace ⊆ Set.range δ := fun hsub => hgne (Set.Subset.antisymm hδsubγ hsub)
      exact Set.not_subset.mp hnot
    have hzD : z ∉ Set.range f := fun hmem => hzδ (hδeq ▸ ⟨hmem, hzγ⟩)
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp
      (isCompact_range f.continuous).isClosed.isOpen_compl z hzD
    have hzfr : z ∈ frontier S'.V := by
      rw [frontier_V_eq_trace S']
      exact hγδΓ ⟨hzγ, hzδ⟩
    have hzcl : z ∈ closure S'.V := by
      rw [S'.isOpen_V.frontier_eq] at hzfr
      exact hzfr.1
    obtain ⟨u, huV, huρ⟩ := Metric.mem_closure_iff.mp hzcl ρ hρ
    have huD : u ∉ Set.range f := by
      intro hmem
      exact (hball (by rw [Metric.mem_ball, dist_comm]; exact huρ)) hmem
    have huΓ : u ∉ Γ.trace := by
      have hmem : u ∈ S'.U ∪ S'.V := Or.inr huV
      rwa [S'.union_eq] at hmem
    have huγ : u ∉ γ.trace := by
      intro hmem
      refine huΓ ?_
      rw [hΓtr]
      exact Or.inl ⟨hmem, fun hcon => huD (hfrsub (hδsub hcon.1))⟩
    have huUV : u ∈ S.U ∪ S.V := by rw [S.union_eq]; exact huγ
    rcases huUV with huU | huV'
    · exact absurd huV (Set.disjoint_left.mp S'.disjoint_UV (hSU huU))
    · exact ⟨u, huV', huD⟩
  have hWV : W = S'.V := eq_boundedSide_of_frontier_subset S' hWopen hWbdd hWne hWsub hWfront
  refine ⟨Γ, S', ?_, ?_, ?_⟩
  · rw [← hWV, hWdef]
  · intro x hx
    have hx' : x ∉ Set.range δ := fun hcon => hx.2 (hδsub hcon)
    rw [hΓtr]
    exact Or.inl ⟨hx.1, fun hcon => hx' hcon.1⟩
  · intro x hx
    rw [hΓtr] at hx
    rcases hx with hx' | hx'
    · exact Or.inl hx'.1
    · exact Or.inr hx'.1

end

end Work.Smooth.SphereJordan
