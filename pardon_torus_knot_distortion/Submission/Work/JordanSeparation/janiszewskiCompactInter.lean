import Mathlib
import Submission.Work.JordanSeparation.janiszewskiZeroInftyOfWinding
import Submission.Work.JordanSeparation.loopInFrontierBallUnion
import Submission.Work.Smooth.SphereJordan.planeIndex
import Submission.Work.Smooth.SphereJordan.existsLogPath
import Submission.Work.Smooth.SphereJordan.winding_loop_of_bounded_component
import Submission.Work.Smooth.SphereJordan.log_compl_cut
import Submission.Work.Smooth.SphereJordan.Transport
import Submission.Work.Smooth.SphereJordan.mobiusAddInv
import Submission.Work.Smooth.JordanSeparation.phragmen_brouwer_of_square
import Submission.Work.Smooth.JordanSeparation.onePoint_locallyPathConnected

namespace Work.JordanSeparation

open Set
open scoped OnePoint

noncomputable section

/-- The one-point compactification of `ℂ`. -/
abbrev RiemannSphere : Type := OnePoint ℂ

/-! ## The difference of two logarithms on a preconnected set -/

theorem log_diff_const {F : Set ℂ} (hF : IsPreconnected F) {φ₁ φ₂ : ℂ → ℂ}
    (h₁ : ContinuousOn φ₁ F) (h₂ : ContinuousOn φ₂ F)
    (he₁ : ∀ z ∈ F, Complex.exp (φ₁ z) = z) (he₂ : ∀ z ∈ F, Complex.exp (φ₂ z) = z) :
    ∃ k : ℤ, ∀ z ∈ F, φ₁ z - φ₂ z = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
  classical
  set cP : ℂ := 2 * (Real.pi : ℂ) * Complex.I with hcP
  have hpi : (1 : ℝ) < 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hnormC : ‖cP‖ = 2 * Real.pi := by
    rw [hcP, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  by_cases hne : F.Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    exact ⟨0, fun z hz => absurd (hne ▸ hz) (Set.notMem_empty z)⟩
  obtain ⟨z₀, hz₀⟩ := hne
  have hint : ∀ z ∈ F, ∃ n : ℤ, φ₁ z - φ₂ z = (n : ℂ) * cP := by
    intro z hz
    have h : Complex.exp (φ₁ z - φ₂ z) = 1 := by
      have h2 : Complex.exp (φ₂ z) = z := he₂ z hz
      rw [Complex.exp_sub, he₁ z hz, h2]
      exact div_self fun hc => Complex.exp_ne_zero (φ₂ z) (by rw [h2, hc])
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
    exact ⟨n, by rw [hn, hcP]⟩
  rcases hint z₀ hz₀ with ⟨k, hk⟩
  refine ⟨k, fun z hz => ?_⟩
  by_contra hbad
  haveI : PreconnectedSpace ↥F := isPreconnected_iff_preconnectedSpace.mp hF
  have hcont : Continuous (fun z : ↥F => φ₁ z.1 - φ₂ z.1) := h₁.domRestrict.sub h₂.domRestrict
  set Δ : ↥F → ℂ := fun z => φ₁ z.1 - φ₂ z.1 with hΔ
  have hval : ∀ z : ↥F, Δ z = (k : ℂ) * cP ∨ (1 : ℝ) ≤ ‖Δ z - (k : ℂ) * cP‖ := by
    intro z
    obtain ⟨n, hn⟩ := hint z.1 z.2
    rcases eq_or_ne n k with hnk | hnk
    · left
      rw [hΔ]; show φ₁ z.1 - φ₂ z.1 = (k : ℂ) * cP
      rw [hn, hnk]
    · right
      have h1 : (1 : ℤ) ≤ |n - k| := Int.one_le_abs (sub_ne_zero.mpr hnk)
      have h3 : Δ z - (k : ℂ) * cP = ((n - k : ℤ) : ℂ) * cP := by
        rw [hΔ]; show φ₁ z.1 - φ₂ z.1 - (k:ℂ) * cP = _
        rw [hn]; push_cast; ring
      rw [h3, norm_mul, hnormC, Complex.norm_intCast]
      have h2 : (1 : ℝ) ≤ |((n - k : ℤ) : ℝ)| := by exact_mod_cast h1
      have h2' : (0 : ℝ) ≤ |((n - k : ℤ) : ℝ)| := abs_nonneg _
      nlinarith [h2, h2', hpi]
  set A : Set ↥F := {z | Δ z = (k : ℂ) * cP} with hA
  have hAeq1 : A = {z : ↥F | ‖Δ z - (k : ℂ) * cP‖ < 1} := by
    ext z
    constructor
    · intro hz
      rw [hA] at hz
      simp only [Set.mem_setOf_eq] at hz ⊢
      rw [hz, sub_self, norm_zero]; norm_num
    · intro hz
      simp only [Set.mem_setOf_eq] at hz ⊢
      rcases hval z with h | h
      · exact h
      · exact absurd hz (by linarith)
  have hAeq2 : A = {z : ↥F | ‖Δ z - (k : ℂ) * cP‖ ≤ 1 / 2} := by
    ext z
    constructor
    · intro hz
      rw [hA] at hz
      simp only [Set.mem_setOf_eq] at hz ⊢
      rw [hz, sub_self, norm_zero]; norm_num
    · intro hz
      simp only [Set.mem_setOf_eq] at hz ⊢
      rcases hval z with h | h
      · exact h
      · exact absurd hz (by linarith)
  have hAclopen : IsClopen A := by
    constructor
    · rw [hAeq2]
      exact isClosed_le ((hcont.sub continuous_const).norm) continuous_const
    · rw [hAeq1]
      exact isOpen_lt ((hcont.sub continuous_const).norm) continuous_const
  have hAz₀ : (⟨z₀, hz₀⟩ : ↥F) ∈ A := by
    rw [hA]; simp only [Set.mem_setOf_eq, hΔ]; exact hk
  rcases (isClopen_iff.mp hAclopen) with h | h
  · exact absurd (h ▸ hAz₀) (Set.notMem_empty _)
  · have : (⟨z, hz⟩ : ↥F) ∈ A := by rw [h]; exact Set.mem_univ _
    rw [hA] at this
    simp only [Set.mem_setOf_eq, hΔ] at this
    exact hbad this

/-! ## The planar winding crux -/

/-- A closed set `F ∋ 0` whose component of `0` is bounded has a closed loop in its complement
with non-zero index about `0`. -/
theorem windingLoopAvoidingClosedSet {F : Set ℂ} (hF : IsClosed F) (h0 : (0 : ℂ) ∈ F)
    (hbdd : Bornology.IsBounded (connectedComponentIn F (0 : ℂ))) :
    ∃ c : C(unitInterval, ℂ), (∀ t, c t ∉ F) ∧ (∀ t, c t ≠ 0) ∧ c 0 = c 1 ∧
      Work.Smooth.SphereJordan.loopIndex c ≠ 0 := by
  obtain ⟨U, ρ, hUcomp, h0U, _hUsubF, hρpos, hgap⟩ :=
    Work.Smooth.SphereJordan.exists_compact_gap hF h0 hbdd
  obtain ⟨c, hcU, hcnear, hcloop, hidx⟩ :=
    Work.Smooth.SphereJordan.existsShellLoop_of_frontierLoop
      (fun P r hr h0mem => loopInFrontierBallUnion hr h0mem) hUcomp h0U
      (by linarith : (0 : ℝ) < ρ / 2)
  have hcF : ∀ t, c t ∉ F := by
    intro t hzt
    obtain ⟨k, hkU, hdk⟩ := hcnear t
    by_cases hztU : c t ∈ U
    · exact hcU t hztU
    · have hρle : ρ ≤ dist k (c t) := hgap k hkU (c t) hzt hztU
      rw [dist_comm] at hρle
      linarith [hdk]
  have hc0 : ∀ t, c t ≠ 0 := fun t h => hcU t (h ▸ h0U)
  obtain ⟨Λ, hΛ, -, -⟩ := Work.Smooth.SphereJordan.argChangeLift c hc0
  have hincr : Λ 1 - Λ 0 = 2 * ↑Real.pi * Complex.I := by
    rw [Work.Smooth.SphereJordan.loopIndex_spec c hc0 hcloop Λ hΛ, hidx]
    ring
  have hincr' : Λ 1 = Λ 0 + 2 * ↑Real.pi * Complex.I := by linear_combination hincr
  obtain ⟨c', hc'F, hc'0, hc'loop, hc'idx⟩ :=
    Work.Smooth.SphereJordan.loop_index_one_of_exp_path Λ
      (fun t => by rw [hΛ t]; exact hcF t) hincr'
  exact ⟨c', hc'F, hc'0, hc'loop, by rw [hc'idx]; norm_num⟩

/-! ## A logarithm on the complement of a path from `0` to `∞` -/

theorem exists_log_on_compl_path {γ : C(unitInterval, OnePoint ℂ)}
    (h0 : γ 0 = ((0 : ℂ) : OnePoint ℂ)) (h1 : γ 1 = OnePoint.infty) :
    ∃ F : ℂ → ℂ, ContinuousOn F {z : ℂ | ((z : ℂ) : OnePoint ℂ) ∈ (Set.range γ)ᶜ} ∧
      ∀ z : ℂ, ((z : ℂ) : OnePoint ℂ) ∈ (Set.range γ)ᶜ → Complex.exp (F z) = z := by
  classical
  obtain ⟨f, hfc, hfe⟩ := Work.Smooth.SphereJordan.log_compl_cut h0 h1
  refine ⟨fun z => if h : ((z : ℂ) : OnePoint ℂ) ∈ (Set.range γ)ᶜ then f ⟨z, h⟩ else 0, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have hcont : Continuous (fun z : ↥{z : ℂ | ((z : ℂ) : OnePoint ℂ) ∈ (Set.range γ)ᶜ} =>
        f ⟨z.1, z.2⟩) := hfc.comp (Continuous.subtype_mk continuous_subtype_val _)
    refine hcont.congr (fun z => ?_)
    simp only [Set.domRestrict_apply]
    split_ifs with h
    · exact congrArg f (Subtype.ext rfl)
    · exact absurd z.2 h
  · intro z hz
    simp only [dif_pos hz]
    exact hfe ⟨z, hz⟩

/-! ## Janiszewski's theorem on the Riemann sphere for the points `0` and `∞` -/

theorem janiszewskiZeroInfty {A₁ A₂ : Set (OnePoint ℂ)}
    (h₁ : IsClosed A₁) (h₂ : IsClosed A₂)
    (hne : (A₁ ∩ A₂).Nonempty) (hcon : IsPreconnected (A₁ ∩ A₂))
    (h0 : ((0 : ℂ) : OnePoint ℂ) ∉ A₁ ∪ A₂) (hinf : (OnePoint.infty : OnePoint ℂ) ∉ A₁ ∪ A₂)
    (h₁' : (OnePoint.infty : OnePoint ℂ) ∈
      connectedComponentIn A₁ᶜ ((0 : ℂ) : OnePoint ℂ))
    (h₂' : (OnePoint.infty : OnePoint ℂ) ∈
      connectedComponentIn A₂ᶜ ((0 : ℂ) : OnePoint ℂ)) :
    (OnePoint.infty : OnePoint ℂ) ∈
      connectedComponentIn (A₁ ∪ A₂)ᶜ ((0 : ℂ) : OnePoint ℂ) :=
  janiszewskiZeroInftyOfWinding
    (fun {F} hF h0F hbdd => windingLoopAvoidingClosedSet hF h0F hbdd)
    h₁ h₂ hne hcon h0 hinf h₁' h₂'

/-! ## Transport to arbitrary points of the sphere -/

/-- Images of connected components under a homeomorphism. -/
theorem image_connectedComponentIn_homeomorph {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] (φ : α ≃ₜ β) (A : Set α) (a : α) :
    φ '' connectedComponentIn A a = connectedComponentIn (φ '' A) (φ a) := by
  by_cases ha : a ∈ A
  · apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact (isPreconnected_connectedComponentIn.image φ φ.continuous.continuousOn)
        |>.subset_connectedComponentIn ⟨a, mem_connectedComponentIn ha, rfl⟩
          (Set.image_mono (connectedComponentIn_subset A a)) ⟨z, hz, rfl⟩
    · intro y hy
      have hpre : IsPreconnected (φ.symm '' connectedComponentIn (φ '' A) (φ a)) :=
        isPreconnected_connectedComponentIn.image φ.symm φ.symm.continuous.continuousOn
      have hsub : φ.symm '' connectedComponentIn (φ '' A) (φ a) ⊆ A := by
        rintro _ ⟨z, hz, rfl⟩
        obtain ⟨w, hw, hwz⟩ := connectedComponentIn_subset (φ '' A) (φ a) hz
        rw [← hwz, Homeomorph.symm_apply_apply]
        exact hw
      have hmem : φ.symm (φ a) ∈ φ.symm '' connectedComponentIn (φ '' A) (φ a) :=
        ⟨φ a, mem_connectedComponentIn ⟨a, ha, rfl⟩, rfl⟩
      have h1 : φ.symm y ∈ connectedComponentIn A a := by
        simpa only [Homeomorph.symm_apply_apply] using
          (hpre.subset_connectedComponentIn hmem hsub ⟨y, hy, rfl⟩)
      exact ⟨φ.symm y, h1, φ.apply_symm_apply y⟩
  · have h1 : connectedComponentIn A a = ∅ := connectedComponentIn_eq_empty ha
    have h2 : connectedComponentIn (φ '' A) (φ a) = ∅ :=
      connectedComponentIn_eq_empty (fun h => ha (by
        obtain ⟨b, hb, hba⟩ := h
        rw [← φ.injective hba]; exact hb))
    rw [h1, h2, Set.image_empty]

/-- Two distinct points of the sphere can be sent to `0` and `∞` by a homeomorphism. -/
private lemma exists_homeomorph_zero_infty {a b : OnePoint ℂ} (hab : a ≠ b) :
    ∃ φ : OnePoint ℂ ≃ₜ OnePoint ℂ, φ a = ((0 : ℂ) : OnePoint ℂ) ∧
      φ b = OnePoint.infty := by
  by_cases hb : b = OnePoint.infty
  · have ha : a ≠ OnePoint.infty := fun h => hab (h.trans hb.symm)
    obtain ⟨a₀, rfl⟩ := OnePoint.ne_infty_iff_exists.mp ha
    refine ⟨Homeomorph.onePointCongr (Homeomorph.addRight (-a₀)), ?_, ?_⟩
    · rw [Homeomorph.onePointCongr_apply, OnePoint.map_some]
      simp
    · rw [hb, Homeomorph.onePointCongr_apply]
      exact OnePoint.map_infty _
  · obtain ⟨b₀, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hb
    by_cases ha : a = OnePoint.infty
    · refine ⟨(Homeomorph.onePointCongr (Homeomorph.addRight (-b₀))).trans
        Work.Smooth.SphereJordan.invHomeomorph, ?_, ?_⟩
      · rw [Homeomorph.trans_apply, ha, Homeomorph.onePointCongr_apply, OnePoint.map_infty]
        exact Work.Smooth.SphereJordan.invMap_infty
      · rw [Homeomorph.trans_apply, Homeomorph.onePointCongr_apply, OnePoint.map_some]
        simp only [Homeomorph.coe_addRight, add_neg_cancel, OnePoint.map_some]
        exact Work.Smooth.SphereJordan.invHomeomorph_coe_zero
    · obtain ⟨a₀, rfl⟩ := OnePoint.ne_infty_iff_exists.mp ha
      have hab₀ : a₀ ≠ b₀ := fun h => hab (by rw [h])
      obtain ⟨Φ, -, hΦ0, hΦz⟩ := Work.Smooth.SphereJordan.mobiusAddInv (-(a₀ - b₀)⁻¹)
      refine ⟨(Homeomorph.onePointCongr (Homeomorph.addRight (-b₀))).trans Φ, ?_, ?_⟩
      · rw [Homeomorph.trans_apply, Homeomorph.onePointCongr_apply, OnePoint.map_some]
        simp only [Homeomorph.coe_addRight]
        rw [hΦz (a₀ + (-b₀)) (by simpa only [sub_eq_add_neg] using sub_ne_zero.mpr hab₀)]
        congr 1
        rw [show a₀ + (-b₀) = a₀ - b₀ from by ring]
        exact neg_add_cancel _
      · rw [Homeomorph.trans_apply, Homeomorph.onePointCongr_apply, OnePoint.map_some]
        simp only [Homeomorph.coe_addRight, add_neg_cancel, OnePoint.map_some]
        exact hΦ0

/-- **Janiszewski's theorem on the Riemann sphere.** -/
theorem janiszewskiSphereGeneral {A₁ A₂ : Set (OnePoint ℂ)} (h₁ : IsClosed A₁) (h₂ : IsClosed A₂)
    (hne : (A₁ ∩ A₂).Nonempty) (hcon : IsPreconnected (A₁ ∩ A₂)) {a b : OnePoint ℂ}
    (ha : a ∉ A₁ ∪ A₂) (hb : b ∉ A₁ ∪ A₂)
    (h₁' : b ∈ connectedComponentIn A₁ᶜ a) (h₂' : b ∈ connectedComponentIn A₂ᶜ a) :
    b ∈ connectedComponentIn (A₁ ∪ A₂)ᶜ a := by
  by_cases hab : a = b
  · subst hab
    exact mem_connectedComponentIn ha
  · obtain ⟨φ, hφa, hφb⟩ := exists_homeomorph_zero_infty hab
    have hA₁ : IsClosed (φ '' A₁) := (φ.isClosed_image).mpr h₁
    have hA₂ : IsClosed (φ '' A₂) := (φ.isClosed_image).mpr h₂
    have hne' : ((φ '' A₁) ∩ (φ '' A₂)).Nonempty := by
      obtain ⟨z, hz⟩ := hne
      exact ⟨φ z, ⟨⟨z, hz.1, rfl⟩, ⟨z, hz.2, rfl⟩⟩⟩
    have hcon' : IsPreconnected ((φ '' A₁) ∩ (φ '' A₂)) := by
      rw [← Set.image_inter φ.injective]
      exact hcon.image _ φ.continuous.continuousOn
    have ha' : ((0 : ℂ) : OnePoint ℂ) ∉ (φ '' A₁) ∪ (φ '' A₂) := by
      rw [← hφa]
      rintro (h | h)
      · obtain ⟨z, hz, hz0⟩ := h
        exact ha (Or.inl (by rwa [← φ.injective hz0]))
      · obtain ⟨z, hz, hz0⟩ := h
        exact ha (Or.inr (by rwa [← φ.injective hz0]))
    have hb' : (OnePoint.infty : OnePoint ℂ) ∉ (φ '' A₁) ∪ (φ '' A₂) := by
      rw [← hφb]
      rintro (h | h)
      · obtain ⟨z, hz, hz0⟩ := h
        exact hb (Or.inl (by rwa [← φ.injective hz0]))
      · obtain ⟨z, hz, hz0⟩ := h
        exact hb (Or.inr (by rwa [← φ.injective hz0]))
    have h₁'' : (OnePoint.infty : OnePoint ℂ) ∈
        connectedComponentIn (φ '' A₁)ᶜ ((0 : ℂ) : OnePoint ℂ) := by
      have h := image_connectedComponentIn_homeomorph φ A₁ᶜ a
      rw [Set.image_compl_eq φ.bijective] at h
      have hb2 : φ b ∈ φ '' connectedComponentIn A₁ᶜ a := ⟨b, h₁', rfl⟩
      rw [h, hφa, hφb] at hb2
      exact hb2
    have h₂'' : (OnePoint.infty : OnePoint ℂ) ∈
        connectedComponentIn (φ '' A₂)ᶜ ((0 : ℂ) : OnePoint ℂ) := by
      have h := image_connectedComponentIn_homeomorph φ A₂ᶜ a
      rw [Set.image_compl_eq φ.bijective] at h
      have hb2 : φ b ∈ φ '' connectedComponentIn A₂ᶜ a := ⟨b, h₂', rfl⟩
      rw [h, hφa, hφb] at hb2
      exact hb2
    have hmain := janiszewskiZeroInfty hA₁ hA₂ hne' hcon' ha' hb' h₁'' h₂''
    have h := image_connectedComponentIn_homeomorph φ (A₁ ∪ A₂)ᶜ a
    rw [Set.image_compl_eq φ.bijective, Set.image_union, hφa] at h
    have hmem : φ b ∈ φ '' connectedComponentIn (A₁ ∪ A₂)ᶜ a := by
      rw [h, hφb]; exact hmain
    obtain ⟨z, hz, hzb⟩ := hmem
    rw [φ.injective hzb] at hz
    exact hz

/-! ## Components of the complement: plane versus sphere -/

/-! ## Elementary connectedness helpers -/

/-- If an open set `U` is covered by two disjoint open sets, and two points of `U` lie one in each
of them, they are in different connected components of `U`. -/
theorem notMem_connectedComponentIn_of_separating {α : Type*} [TopologicalSpace α]
    {U X X' : Set α} (hXo : IsOpen X) (hX'o : IsOpen X') (hcover : U ⊆ X ∪ X')
    (hdisj : Disjoint X X') {a b : α} (haU : a ∈ U) (haX : a ∈ X) (hbX' : b ∈ X') :
    b ∉ connectedComponentIn U a := by
  intro hb
  have hpre := isPreconnected_connectedComponentIn (F := U) (x := a)
  have hsub : connectedComponentIn U a ⊆ X ∪ X' := (connectedComponentIn_subset U a).trans hcover
  have hdisj' : connectedComponentIn U a ∩ (X ∩ X') = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro p ⟨-, hpX, hpX'⟩
    exact Set.disjoint_left.mp hdisj hpX hpX'
  rcases (isPreconnected_iff_subset_of_disjoint.mp hpre) X X' hXo hX'o hsub hdisj' with h | h
  · exact Set.disjoint_left.mp hdisj (h hb) hbX'
  · exact Set.disjoint_left.mp hdisj haX (h (mem_connectedComponentIn haU))

/-- The far region `{z : ℂ | r < ‖z‖}` of the plane is preconnected (for `0 ≤ r`). -/
theorem isPreconnected_lt_norm (r : ℝ) (hr : 0 ≤ r) :
    IsPreconnected {z : ℂ | r < ‖z‖} := by
  have hsph : IsPreconnected (Metric.sphere (0 : ℂ) 1) :=
    isPreconnected_sphere (E := ℂ) (by rw [Complex.rank_real_complex]; norm_num) 0 1
  have hprod : IsPreconnected (Set.Ioi r ×ˢ Metric.sphere (0 : ℂ) 1) :=
    isPreconnected_Ioi.prod hsph
  have himg : IsPreconnected
      ((fun p : ℝ × ℂ => p.1 • p.2) '' (Set.Ioi r ×ˢ Metric.sphere (0 : ℂ) 1)) :=
    hprod.image _ (by fun_prop)
  have heq : (fun p : ℝ × ℂ => p.1 • p.2) '' (Set.Ioi r ×ˢ Metric.sphere (0 : ℂ) 1)
      = {z : ℂ | r < ‖z‖} := by
    ext z
    constructor
    · rintro ⟨⟨a, u⟩, ⟨ha, hu⟩, rfl⟩
      have hu' : ‖u‖ = 1 := by
        rw [mem_sphere_iff_norm] at hu; simpa using hu
      show r < ‖a • u‖
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (lt_of_le_of_lt hr ha), hu', mul_one]
      exact ha
    · intro hz
      have hzpos : 0 < ‖z‖ := lt_of_le_of_lt hr hz
      refine ⟨(‖z‖, (‖z‖ : ℝ)⁻¹ • z), ⟨hz, ?_⟩, ?_⟩
      · rw [mem_sphere_iff_norm]
        show ‖(‖z‖ : ℝ)⁻¹ • z - 0‖ = 1
        rw [sub_zero, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (norm_nonneg z)), inv_mul_cancel₀ (ne_of_gt hzpos)]
      · show ‖z‖ • ((‖z‖ : ℝ)⁻¹ • z) = z
        rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hzpos), one_smul]
  rwa [heq] at himg

/-- The frontier of a connected component of the complement of a closed set lies in that set. -/
theorem frontier_connectedComponentIn_subset {A : Set ℂ} (hA : IsClosed A) (z : ℂ) :
    frontier (connectedComponentIn Aᶜ z) ⊆ A := by
  intro q hq
  by_contra hqA
  have hqAc : q ∈ Aᶜ := hqA
  set P : Set ℂ := connectedComponentIn Aᶜ z with hP
  have hPopen : IsOpen P := by rw [hP]; exact hA.isOpen_compl.connectedComponentIn
  have hqclP : q ∈ closure P := frontier_subset_closure hq
  have hqP : q ∉ P := by
    have h := hq
    rw [hPopen.frontier_eq] at h
    exact h.2
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hA.isOpen_compl q hqAc
  obtain ⟨q', hq'P, hq'ball⟩ := Metric.mem_closure_iff.mp hqclP (ε / 2) (by linarith)
  have hball : Metric.ball q ε ⊆ connectedComponentIn Aᶜ q' :=
    IsPreconnected.subset_connectedComponentIn (convex_ball q ε).isPreconnected
      (Metric.mem_ball.mpr (by rw [dist_comm]; linarith)) (fun w hw => hεsub hw)
  have hq'mem : q ∈ connectedComponentIn Aᶜ q' := hball (Metric.mem_ball_self hε)
  have hqeq : connectedComponentIn Aᶜ q' = P :=
    (connectedComponentIn_eq (by rw [← hP]; exact hq'P)).symm.trans hP.symm
  exact hqP (by rwa [hqeq] at hq'mem)

/-- **Comparison of the connected components of the complement of a compact plane set, in the plane
and in the Riemann sphere.**

If `A ⊆ ℂ` is compact and `z, w ∈ ℂ`, then `w` lies in the connected component of `z` in the
complement of `A` *in the Riemann sphere* if and only if it lies in the connected component of `z`
in the complement of `A` *in the plane*.  (The point `∞` glues only the unbounded component of the
plane complement to itself, so it never glues two distinct plane components.) -/
theorem connectedComponentIn_compl_coe {A : Set ℂ} (hA : IsCompact A) (z : ℂ) :
    {w : ℂ | (w : RiemannSphere) ∈ connectedComponentIn ((↑) '' A)ᶜ (z : RiemannSphere)}
      = connectedComponentIn (Aᶜ : Set ℂ) z := by
  have hAcl : IsClosed A := hA.isClosed
  have hAclo : IsOpen (Aᶜ : Set ℂ) := hAcl.isOpen_compl
  set P : Set ℂ := connectedComponentIn Aᶜ z with hP
  have hPopen : IsOpen P := by rw [hP]; exact hAclo.connectedComponentIn
  have hPpre : IsPreconnected P := by rw [hP]; exact isPreconnected_connectedComponentIn
  have hfront : frontier P ⊆ A := by rw [hP]; exact frontier_connectedComponentIn_subset hAcl z
  -- `Aᶜ \ P` is open in the plane
  have hQPopen : IsOpen (Aᶜ \ P) := by
    rw [isOpen_iff_mem_nhds]
    rintro q ⟨hqAc, hqP⟩
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hAclo q hqAc
    refine Filter.mem_of_superset (Metric.ball_mem_nhds q hε) (fun c hc => ⟨hεsub hc, ?_⟩)
    intro hcP
    have hball : Metric.ball q ε ⊆ P := by
      have h1 : Metric.ball q ε ⊆ connectedComponentIn Aᶜ c :=
        IsPreconnected.subset_connectedComponentIn (convex_ball q ε).isPreconnected
          hc (fun u hu => hεsub hu)
      have h2 : connectedComponentIn Aᶜ c = P :=
        (connectedComponentIn_eq (show c ∈ connectedComponentIn Aᶜ z by rw [← hP]; exact hcP)).symm.trans hP.symm
      rw [h2] at h1
      exact h1
    exact hqP (hball (Metric.mem_ball_self hε))
  -- boundedness datum
  obtain ⟨C, hC⟩ := hA.isBounded.exists_norm_le
  have hfar : ({w : ℂ | max C 0 < ‖w‖}) ⊆ Aᶜ := by
    intro w hw
    rw [mem_compl_iff]; intro hwA
    have h1 : ‖w‖ ≤ C := hC w hwA
    have h2 : C ≤ max C 0 := le_max_left _ _
    exact absurd (le_trans h1 h2) (not_le.mpr hw)
  refine Set.Subset.antisymm ?_ ?_
  · -- the hard direction: a sphere-connection is a plane-connection
    intro w hw
    by_contra hwP
    have hwU : (w : RiemannSphere) ∈ ((↑) '' A)ᶜ := connectedComponentIn_subset _ _ hw
    have hwAc : w ∈ Aᶜ := by
      rw [mem_compl_iff]; intro hwA; exact hwU ⟨w, hwA, rfl⟩
    have hzAc : z ∈ Aᶜ := by
      by_contra hzA
      rw [mem_compl_iff, not_not] at hzA
      have hD : connectedComponentIn ((↑) '' A)ᶜ (z : RiemannSphere) = ∅ :=
        connectedComponentIn_eq_empty (by intro h; exact h ⟨z, hzA, rfl⟩)
      rw [hD] at hw; exact hw
    have hzP : z ∈ P := by rw [hP]; exact mem_connectedComponentIn hzAc
    have haU : (z : RiemannSphere) ∈ ((↑) '' A)ᶜ := by
      rw [mem_compl_iff]; rintro ⟨a, ha, hza⟩
      exact hzAc (OnePoint.coe_injective hza ▸ ha)
    by_cases hPbdd : Bornology.IsBounded P
    · -- `P` bounded: separate with `↑''P` and `↑''(Aᶜ \ P) ∪ {∞}`
      have hAPclosed : IsClosed (A ∪ P) := by
        have hsub : closure P ⊆ A ∪ P := by
          rw [closure_eq_self_union_frontier, ← Set.union_comm P A]
          exact Set.union_subset_union (subset_refl P) hfront
        have heq : A ∪ P = A ∪ closure P :=
          Set.Subset.antisymm (Set.union_subset_union (subset_refl A) subset_closure)
            (Set.union_subset Set.subset_union_left hsub)
        rw [heq]; exact hAcl.union isClosed_closure
      have hAPbdd : Bornology.IsBounded (A ∪ P) := hA.isBounded.union hPbdd
      have hAPc : IsCompact (A ∪ P) :=
        Metric.isCompact_iff_isClosed_bounded.mpr ⟨hAPclosed, hAPbdd⟩
      have hpre : (OnePoint.some ⁻¹' ((↑) '' (Aᶜ \ P) ∪ {∞} : Set RiemannSphere) : Set ℂ) = Aᶜ \ P := by
        change {c : ℂ | (c : RiemannSphere) ∈ ((↑) '' (Aᶜ \ P) ∪ {∞} : Set RiemannSphere)} = Aᶜ \ P
        ext c
        rw [Set.mem_ofPred_eq, Set.mem_union, Set.mem_image, Set.mem_singleton_iff]
        constructor
        · rintro (⟨x, hx, hxc⟩ | hinf)
          · rwa [OnePoint.coe_injective hxc] at hx
          · exact absurd hinf (OnePoint.coe_ne_infty c)
        · intro hc; exact Or.inl ⟨c, hc, rfl⟩
      refine notMem_connectedComponentIn_of_separating (α := RiemannSphere)
        (U := ((↑) '' A)ᶜ) (X := (↑) '' P) (X' := (↑) '' (Aᶜ \ P) ∪ {∞})
        (OnePoint.isOpen_image_coe.mpr hPopen) ?_ ?_ ?_ haU ⟨z, hzP, rfl⟩ (Or.inl ⟨w, ⟨hwAc, hwP⟩, rfl⟩) hw
      · refine (OnePoint.isOpen_iff_of_mem' (by simp : (∞ : RiemannSphere) ∈ (↑) '' (Aᶜ \ P) ∪ {∞})).mpr ⟨?_, ?_⟩
        · have hdiff : (Aᶜ \ P)ᶜ = A ∪ P := by
            ext c
            rw [Set.mem_compl_iff, Set.mem_sdiff, Set.mem_union]
            constructor
            · intro h; by_cases hc : c ∈ A
              · exact Or.inl hc
              · exact Or.inr (by by_contra hp; exact h ⟨hc, hp⟩)
            · rintro (hc | hp) ⟨hc', hp'⟩
              · exact hc' hc
              · exact hp' hp
          rw [hpre, hdiff]
          exact hAPc
        · rw [hpre]; exact hQPopen
      · -- covering
        intro a ha
        rw [OnePoint.compl_image_coe] at ha
        rcases ha with ⟨c, hc, hca⟩ | hinf
        · rw [← hca]
          rcases em (c ∈ P) with hcP | hcP
          · exact Or.inl ⟨c, hcP, rfl⟩
          · exact Or.inr (Or.inl ⟨c, ⟨hc, hcP⟩, rfl⟩)
        · rw [Set.mem_singleton_iff] at hinf
          rw [hinf]
          exact Or.inr (Or.inr rfl)
      · -- disjointness
        rw [Set.disjoint_left]
        rintro a ⟨c, hcP, hac⟩ hain
        rcases hain with ⟨e, he, hea⟩ | hin
        · exact he.2 (OnePoint.coe_injective (hac.trans hea.symm) ▸ hcP)
        · rw [Set.mem_singleton_iff] at hin
          exact OnePoint.coe_ne_infty c (hac.trans hin)
    · -- `P` unbounded: separate with `↑''P ∪ {∞}` and `↑''(Aᶜ \ P)`
      have hPunb : ∃ w₀ ∈ P, max C 0 < ‖w₀‖ := by
        by_contra hcon
        simp only [not_exists, not_and, not_lt] at hcon
        exact hPbdd (isBounded_iff_forall_norm_le.mpr ⟨max C 0, hcon⟩)
      have hsubP : ({w : ℂ | max C 0 < ‖w‖}) ⊆ P := by
        obtain ⟨w₀, hw₀P, hw₀R⟩ := hPunb
        have h1 : {w : ℂ | max C 0 < ‖w‖} ⊆ connectedComponentIn Aᶜ w₀ :=
          IsPreconnected.subset_connectedComponentIn (isPreconnected_lt_norm (max C 0) (le_max_right _ _))
            hw₀R hfar
        have h2 : connectedComponentIn Aᶜ w₀ = P :=
          (connectedComponentIn_eq (show w₀ ∈ connectedComponentIn Aᶜ z by rw [← hP]; exact hw₀P)).symm.trans hP.symm
        rw [h2] at h1
        exact h1
      have hPc : IsCompact Pᶜ := by
        refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨hPopen.isClosed_compl, ?_⟩
        refine isBounded_iff_forall_norm_le.mpr ⟨max C 0, fun u hu => ?_⟩
        by_contra hlt
        exact hu (hsubP (not_le.mp hlt))
      have hpre : (OnePoint.some ⁻¹' ((↑) '' P ∪ {∞} : Set RiemannSphere) : Set ℂ) = P := by
        change {c : ℂ | (c : RiemannSphere) ∈ ((↑) '' P ∪ {∞} : Set RiemannSphere)} = P
        ext c
        rw [Set.mem_ofPred_eq, Set.mem_union, Set.mem_image, Set.mem_singleton_iff]
        constructor
        · rintro (⟨x, hx, hxc⟩ | hinf)
          · rwa [OnePoint.coe_injective hxc] at hx
          · exact absurd hinf (OnePoint.coe_ne_infty c)
        · intro hc; exact Or.inl ⟨c, hc, rfl⟩
      refine notMem_connectedComponentIn_of_separating (α := RiemannSphere)
        (U := ((↑) '' A)ᶜ) (X := (↑) '' P ∪ {∞}) (X' := (↑) '' (Aᶜ \ P))
        ?_ (OnePoint.isOpen_image_coe.mpr hQPopen) ?_ ?_ haU (Or.inl ⟨z, hzP, rfl⟩) ⟨w, ⟨hwAc, hwP⟩, rfl⟩ hw
      · refine (OnePoint.isOpen_iff_of_mem' (by simp : (∞ : RiemannSphere) ∈ (↑) '' P ∪ {∞})).mpr ⟨?_, ?_⟩
        · rw [hpre]; exact hPc
        · rw [hpre]; exact hPopen
      · -- covering
        intro a ha
        rw [OnePoint.compl_image_coe] at ha
        rcases ha with ⟨c, hc, hca⟩ | hinf
        · rw [← hca]
          rcases em (c ∈ P) with hcP | hcP
          · exact Or.inl (Or.inl ⟨c, hcP, rfl⟩)
          · exact Or.inr ⟨c, ⟨hc, hcP⟩, rfl⟩
        · rw [Set.mem_singleton_iff] at hinf
          rw [hinf]
          exact Or.inl (Or.inr rfl)
      · -- disjointness
        rw [Set.disjoint_left]
        rintro a hain ⟨e, he, hea⟩
        rcases hain with ⟨c, hcP, hac⟩ | hin
        · exact he.2 (OnePoint.coe_injective (hac.trans hea.symm) ▸ hcP)
        · rw [Set.mem_singleton_iff] at hin
          exact OnePoint.coe_ne_infty e (hea.trans hin)
  · -- the easy direction
    intro w hwP
    have hwP' : w ∈ connectedComponentIn Aᶜ z := by rw [← hP]; exact hwP
    have hzAc : z ∈ Aᶜ := connectedComponentIn_nonempty_iff.mp ⟨w, hwP'⟩
    have hzP : z ∈ P := by rw [hP]; exact mem_connectedComponentIn hzAc
    have hsub : ((↑) '' P : Set RiemannSphere) ⊆ ((↑) '' A)ᶜ := by
      rintro _ ⟨c, hc, rfl⟩
      rw [mem_compl_iff]
      rintro ⟨a, ha, hca⟩
      exact (connectedComponentIn_subset Aᶜ z (by rw [← hP]; exact hc)) (OnePoint.coe_injective hca ▸ ha)
    exact IsPreconnected.subset_connectedComponentIn
      (hPpre.image _ OnePoint.continuous_coe.continuousOn)
      ⟨z, hzP, rfl⟩ hsub ⟨w, hwP, rfl⟩


/-! ## The plane statement -/

private lemma image_union_coe (F₁ F₂ : Set ℂ) :
    OnePoint.some '' (F₁ ∪ F₂) = (OnePoint.some '' F₁) ∪ (OnePoint.some '' F₂) := by
  rw [Set.image_union]

private lemma image_inter_coe (F₁ F₂ : Set ℂ) :
    OnePoint.some '' (F₁ ∩ F₂) = (OnePoint.some '' F₁) ∩ (OnePoint.some '' F₂) := by
  ext z
  constructor
  · rintro ⟨w, ⟨hw₁, hw₂⟩, rfl⟩
    exact ⟨⟨w, hw₁, rfl⟩, ⟨w, hw₂, rfl⟩⟩
  · rintro ⟨⟨a, ha, haz⟩, ⟨b, hb, hbz⟩⟩
    have hab : a = b := OnePoint.coe_injective (haz.trans hbz.symm)
    exact ⟨a, ⟨ha, by rw [hab]; exact hb⟩, haz⟩

theorem janiszewskiCompactInter {F₁ F₂ : Set ℂ} (h₁ : IsCompact F₁) (h₂ : IsCompact F₂)
    (hne : (F₁ ∩ F₂).Nonempty) (hcon : IsPreconnected (F₁ ∩ F₂))
    {x y : ℂ} (hx : x ∉ F₁ ∪ F₂) (hy : y ∉ F₁ ∪ F₂)
    (h₁' : y ∈ connectedComponentIn F₁ᶜ x) (h₂' : y ∈ connectedComponentIn F₂ᶜ x) :
    y ∈ connectedComponentIn (F₁ ∪ F₂)ᶜ x := by
  by_cases hxy : x = y
  · subst hxy
    exact mem_connectedComponentIn hx
  · have hA₁c : IsClosed (OnePoint.some '' F₁) :=
      (OnePoint.isClosed_image_coe).mpr ⟨h₁.isClosed, h₁⟩
    have hA₂c : IsClosed (OnePoint.some '' F₂) :=
      (OnePoint.isClosed_image_coe).mpr ⟨h₂.isClosed, h₂⟩
    have hne' : ((OnePoint.some '' F₁) ∩ (OnePoint.some '' F₂)).Nonempty := by
      rw [← image_inter_coe]
      obtain ⟨z, hz⟩ := hne
      exact ⟨OnePoint.some z, ⟨z, hz, rfl⟩⟩
    have hcon' : IsPreconnected ((OnePoint.some '' F₁) ∩ (OnePoint.some '' F₂)) := by
      rw [← image_inter_coe]
      exact hcon.image _ OnePoint.continuous_coe.continuousOn
    have ha : (x : OnePoint ℂ) ∉ (OnePoint.some '' F₁) ∪ (OnePoint.some '' F₂) := by
      rintro (h | h)
      · obtain ⟨a, ha, hax⟩ := h
        exact hx (Or.inl (OnePoint.coe_injective hax ▸ ha))
      · obtain ⟨a, ha, hax⟩ := h
        exact hx (Or.inr (OnePoint.coe_injective hax ▸ ha))
    have hb : (y : OnePoint ℂ) ∉ (OnePoint.some '' F₁) ∪ (OnePoint.some '' F₂) := by
      rintro (h | h)
      · obtain ⟨a, ha, hay⟩ := h
        exact hy (Or.inl (OnePoint.coe_injective hay ▸ ha))
      · obtain ⟨a, ha, hay⟩ := h
        exact hy (Or.inr (OnePoint.coe_injective hay ▸ ha))
    have h₁'' : (y : OnePoint ℂ) ∈ connectedComponentIn (OnePoint.some '' F₁)ᶜ (x : OnePoint ℂ) := by
      have h := connectedComponentIn_compl_coe h₁ x
      have : y ∈ ({w : ℂ | (w : OnePoint ℂ) ∈
          connectedComponentIn (OnePoint.some '' F₁)ᶜ (x : OnePoint ℂ)} : Set ℂ) := by
        rw [h]; exact h₁'
      exact this
    have h₂'' : (y : OnePoint ℂ) ∈ connectedComponentIn (OnePoint.some '' F₂)ᶜ (x : OnePoint ℂ) := by
      have h := connectedComponentIn_compl_coe h₂ x
      have : y ∈ ({w : ℂ | (w : OnePoint ℂ) ∈
          connectedComponentIn (OnePoint.some '' F₂)ᶜ (x : OnePoint ℂ)} : Set ℂ) := by
        rw [h]; exact h₂'
      exact this
    have hmain : (y : OnePoint ℂ) ∈
        connectedComponentIn ((OnePoint.some '' F₁) ∪ (OnePoint.some '' F₂))ᶜ (x : OnePoint ℂ) :=
      janiszewskiSphereGeneral hA₁c hA₂c hne' hcon' ha hb h₁'' h₂''
    have h := connectedComponentIn_compl_coe (h₁.union h₂) x
    rw [image_union_coe] at h
    have : y ∈ ({w : ℂ | (w : OnePoint ℂ) ∈
        connectedComponentIn ((OnePoint.some '' F₁) ∪ (OnePoint.some '' F₂))ᶜ
          (x : OnePoint ℂ)} : Set ℂ) := hmain
    rw [h] at this
    exact this


end

end Work.JordanSeparation
