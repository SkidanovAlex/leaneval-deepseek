import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.half_spans_setup
import Submission.Work.Smooth.SphereJordan.mobiusAddInv
import Submission.Work.Smooth.SphereJordan.thetaTwoComponentsSpansH

namespace Work.Smooth.SphereJordan

open Set Metric

noncomputable section

/-! ## The exterior disc of the unit disc on the Riemann sphere -/

/-- The inversion, read as a map of the model disc onto the closed exterior of the unit disc. -/
def exteriorDisc : C(Disc, RiemannSphere) :=
  ⟨fun z : Disc => invHomeomorph ((z : ℂ) : RiemannSphere),
    invHomeomorph.continuous.comp (OnePoint.continuous_coe.comp continuous_subtype_val)⟩

@[simp] theorem exteriorDisc_apply (z : Disc) :
    exteriorDisc z = invHomeomorph ((z : ℂ) : RiemannSphere) := rfl

theorem not_inOpenDisc_infty : ¬ InOpenDisc (infty : RiemannSphere) := by
  rintro ⟨z, -, hz⟩
  exact (OnePoint.coe_ne_infty z) hz

theorem range_exteriorDisc : Set.range exteriorDisc = {x : RiemannSphere | ¬ InOpenDisc x} := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    show ¬ InOpenDisc (invHomeomorph ((z : ℂ) : RiemannSphere))
    rcases eq_or_ne ((z : ℂ)) 0 with hz | hz
    · rw [hz, invHomeomorph_coe_zero]
      exact not_inOpenDisc_infty
    · rw [invHomeomorph_coe_ne hz, inOpenDisc_coe_aux, not_lt]
      have hnorm : ‖(z : ℂ)‖ ≤ 1 := by
        have h := z.2
        rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
      have hpos : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr hz
      rw [norm_inv]
      exact (one_le_inv_iff₀).mpr ⟨hpos, hnorm⟩
  · intro hx
    rcases eq_or_ne x infty with hxinf | hxfin
    · refine ⟨0, ?_⟩
      show invHomeomorph ((((0 : Disc)) : ℂ) : RiemannSphere) = x
      rw [hxinf]
      rw [show ((((0 : Disc)) : ℂ) : RiemannSphere) = ((0 : ℂ) : RiemannSphere) from rfl,
        invHomeomorph_coe_zero]
    · obtain ⟨w, hw⟩ := OnePoint.ne_infty_iff_exists.mp hxfin
      have hw1 : 1 ≤ ‖w‖ := by
        have h : ¬ InOpenDisc ((w : ℂ) : RiemannSphere) := by rw [hw]; exact hx
        rwa [inOpenDisc_coe_aux, not_lt] at h
      have hw0 : w ≠ 0 := by
        intro h; rw [h] at hw1; norm_num at hw1
      refine ⟨⟨(w⁻¹ : ℂ), ?_⟩, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right, norm_inv]
        exact inv_le_one_of_one_le₀ hw1
      · show invHomeomorph (((w⁻¹ : ℂ) : RiemannSphere)) = x
        rw [invHomeomorph_coe_ne (inv_ne_zero hw0), inv_inv, hw]

theorem exteriorDisc_injective : Function.Injective exteriorDisc :=
  invHomeomorph.injective.comp (OnePoint.coe_injective.comp Subtype.val_injective)

/-! ## The radial arc from `t • w` to `w` -/

/-- `rayPar t s = t + s(1-t)` runs linearly from `t` (at `s = 0`) to `1` (at `s = 1`). -/
def rayPar (t s : ℝ) : ℝ := t + s * (1 - t)

theorem continuous_rayPar (t : ℝ) : Continuous (rayPar t) := by
  unfold rayPar; fun_prop

theorem rayPar_zero (t : ℝ) : rayPar t 0 = t := by unfold rayPar; ring
theorem rayPar_one (t : ℝ) : rayPar t 1 = 1 := by unfold rayPar; ring

theorem rayPar_mem_Icc {t s : ℝ} (ht : t ≤ 1) (hs : s ∈ Set.Icc (0:ℝ) 1) :
    rayPar t s ∈ Set.Icc t 1 := by
  refine ⟨?_, ?_⟩ <;> unfold rayPar <;> nlinarith [hs.1, hs.2, ht]

theorem rayPar_mem_Ioo {t s : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hs : s ∈ Set.Ioo (0:ℝ) 1) :
    rayPar t s ∈ Set.Ioo t 1 := by
  refine ⟨?_, ?_⟩ <;> unfold rayPar <;> nlinarith [hs.1, hs.2]

theorem rayPar_surj {t r : ℝ} (ht : t < 1) (hr : r ∈ Set.Icc t 1) :
    ∃ s ∈ Set.Icc (0:ℝ) 1, rayPar t s = r := by
  have h1t : (0:ℝ) < 1 - t := by linarith
  refine ⟨(r - t)/(1 - t), ⟨?_, ?_⟩, ?_⟩
  · exact div_nonneg (by linarith [hr.1]) h1t.le
  · rw [div_le_one h1t]; linarith [hr.2]
  · unfold rayPar; field_simp; ring

theorem rayPar_injOn {t : ℝ} (ht : t < 1) :
    Set.InjOn (rayPar t) (Set.Icc (0:ℝ) 1) := by
  intro a ha b hb hab
  have h1t : (0:ℝ) < 1 - t := by linarith
  unfold rayPar at hab
  have h : (a - b) * (1 - t) = 0 := by linarith
  have h2 : a - b = 0 := by
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact absurd h (ne_of_gt h1t)
  linarith

/-- The `rayPar`-parametrised rays avoid `z` exactly when the straight rays do (the two extra
parameters `t` and `1` give points of `W` respectively of norm one). -/
theorem forall_rayPar_ne_iff {t : ℝ} (ht1 : t < 1) {W : Set ℂ} {w z : ℂ} (hw : ‖w‖ = 1)
    (hm : t • w ∈ W) (hzW : z ∉ W) (hzn : ‖z‖ < 1) :
    (∀ s : Set.Icc (0:ℝ) 1, rayPar t (s:ℝ) • w ≠ z) ↔
      (∀ r : ℝ, t < r → r < 1 → r • w ≠ z) := by
  constructor
  · intro H r hr hr1
    obtain ⟨s, hs, hsr⟩ := rayPar_surj ht1 ⟨hr.le, hr1.le⟩
    rw [← hsr]; exact H ⟨s, hs⟩
  · intro H s
    have hmem := rayPar_mem_Icc ht1.le s.2
    rcases lt_or_eq_of_le hmem.1 with hlt | heq
    · by_cases h1 : rayPar t (s:ℝ) < 1
      · exact H _ hlt h1
      · have hr1 : rayPar t (s:ℝ) = 1 := le_antisymm hmem.2 (not_lt.mp h1)
        rw [hr1, one_smul]
        intro hcon
        have : ‖z‖ = 1 := by rw [← hcon]; exact hw
        linarith
    · have hm' : rayPar t (s:ℝ) • w ∈ W := by rw [← heq]; exact hm
      exact fun hcon => hzW (hcon ▸ hm')

/-- The canonical point `0` of the unit interval. -/
def zeroIcc : Set.Icc (0:ℝ) 1 := ⟨0, by norm_num⟩

/-- The canonical point `1` of the unit interval. -/
def oneIcc : Set.Icc (0:ℝ) 1 := ⟨1, by norm_num⟩

@[simp] theorem zeroIcc_coe : ((zeroIcc : Set.Icc (0:ℝ) 1) : ℝ) = 0 := rfl
@[simp] theorem oneIcc_coe : ((oneIcc : Set.Icc (0:ℝ) 1) : ℝ) = 1 := rfl

/-- The radial arc in the Riemann sphere from `t • w` to `w`, as a map on the unit interval. -/
def radArc (w : ℂ) (t : ℝ) : C(Set.Icc (0:ℝ) 1, RiemannSphere) :=
  ⟨fun s => ((rayPar t (s:ℝ) • w : ℂ) : RiemannSphere), by
    have h : Continuous fun s : Set.Icc (0:ℝ) 1 => rayPar t (s:ℝ) :=
      (continuous_rayPar t).comp continuous_subtype_val
    exact OnePoint.continuous_coe.comp (h.smul continuous_const)⟩

@[simp] theorem radArc_apply (w : ℂ) (t : ℝ) (s : Set.Icc (0:ℝ) 1) :
    radArc w t s = ((rayPar t (s:ℝ) • w : ℂ) : RiemannSphere) := rfl

theorem radArc_zero (w : ℂ) (t : ℝ) :
    radArc w t zeroIcc = ((t • w : ℂ) : RiemannSphere) := by
  show ((rayPar t ((zeroIcc : Set.Icc (0:ℝ) 1) : ℝ) • w : ℂ) : RiemannSphere) = _
  rw [zeroIcc_coe, rayPar_zero]

theorem radArc_one (w : ℂ) (t : ℝ) :
    radArc w t oneIcc = ((w : ℂ) : RiemannSphere) := by
  show ((rayPar t ((oneIcc : Set.Icc (0:ℝ) 1) : ℝ) • w : ℂ) : RiemannSphere) = _
  rw [oneIcc_coe, rayPar_one, one_smul]

theorem norm_smul_of_norm_eq_one {w : ℂ} (hw : ‖w‖ = 1) {r : ℝ} (hr : 0 ≤ r) :
    ‖r • w‖ = r := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, hw, mul_one]


/-- **The complement of a disc and two radial free crosscuts in the unit ball has exactly two
pieces.**  With the planar Jordan–Schoenflies input `h`, `W` a closed disc inside the open unit ball
and `tᵢ • wᵢ ∈ W` the inner endpoints of the two radial crosscuts `(tᵢ, 1) • wᵢ` (whose interiors
avoid `W`), the set `ball 0 1 \ (W ∪ slits)` is the disjoint union of two non-empty open preconnected
sets. -/
theorem radialTwoCutsComponents (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    (W : Set ℂ) (hWcl : IsClosed W) (hWsub : W ⊆ Metric.ball (0 : ℂ) 1)
    (hWdisc : ∃ e : C(Work.Smooth.SphereJordan.Disc, ℂ),
      Function.Injective e ∧ Set.range e = W)
    (h0 : (0 : ℂ) ∈ W)
    (w₁ w₂ : ℂ) (hw₁ : ‖w₁‖ = 1) (hw₂ : ‖w₂‖ = 1) (hne : w₁ ≠ w₂)
    (t₁ t₂ : ℝ) (ht₁ : 0 < t₁) (ht₁' : t₁ < 1) (ht₂ : 0 < t₂) (ht₂' : t₂ < 1)
    (hm₁ : t₁ • w₁ ∈ W) (hm₂ : t₂ • w₂ ∈ W)
    (hf₁ : ∀ r : ℝ, t₁ < r → r < 1 → r • w₁ ∉ W)
    (hf₂ : ∀ r : ℝ, t₂ < r → r < 1 → r • w₂ ∉ W) :
    ∃ P₁ P₂ : Set ℂ, P₁.Nonempty ∧ P₂.Nonempty ∧ IsOpen P₁ ∧ IsOpen P₂ ∧ Disjoint P₁ P₂ ∧
      P₁ ∪ P₂ = Metric.ball (0 : ℂ) 1 \
        (W ∪ (fun r : ℝ => r • w₁) '' Set.Ioo t₁ 1 ∪ (fun r : ℝ => r • w₂) '' Set.Ioo t₂ 1) ∧
      IsPreconnected P₁ ∧ IsPreconnected P₂ := by
  classical
  obtain ⟨e, he_inj, he_range⟩ := hWdisc
  have hw₁ne : w₁ ≠ 0 := by intro hh; rw [hh, norm_zero] at hw₁; norm_num at hw₁
  have hw₂ne : w₂ ≠ 0 := by intro hh; rw [hh, norm_zero] at hw₂; norm_num at hw₂
  set D₁ : Set RiemannSphere := ((↑) : ℂ → RiemannSphere) '' W with hD₁
  set D₂ : Set RiemannSphere := {x : RiemannSphere | ¬ InOpenDisc x} with hD₂
  have hdisj : Disjoint D₁ D₂ := by
    rw [Set.disjoint_left]
    rintro x ⟨y, hyW, rfl⟩ hx
    have hy : ‖y‖ < 1 := by
      have h := hWsub hyW
      rwa [Metric.mem_ball, dist_zero_right] at h
    exact hx ⟨y, hy, rfl⟩
  have hF : ∃ f : C(Disc, RiemannSphere), Function.Injective f ∧ Set.range f = D₁ :=
    ⟨⟨fun z => ((e z : ℂ) : RiemannSphere), OnePoint.continuous_coe.comp e.continuous⟩,
     OnePoint.coe_injective.comp he_inj, by
      rw [hD₁]
      ext x; constructor
      · rintro ⟨z, rfl⟩
        exact ⟨e z, by rw [← he_range]; exact ⟨z, rfl⟩, rfl⟩
      · rintro ⟨y, hyW, rfl⟩
        have hy : y ∈ Set.range e := by rwa [he_range]
        obtain ⟨z, rfl⟩ := hy
        exact ⟨z, rfl⟩⟩
  -- the two inner endpoints lie in `D₁`
  have hα₀ : radArc w₁ t₁ zeroIcc ∈ D₁ := by
    rw [hD₁, radArc_zero]
    exact ⟨t₁ • w₁, hm₁, rfl⟩
  have hβ₀ : radArc w₂ t₂ zeroIcc ∈ D₁ := by
    rw [hD₁, radArc_zero]
    exact ⟨t₂ • w₂, hm₂, rfl⟩
  -- the two outer endpoints lie in `D₂`
  have hα₁ : radArc w₁ t₁ oneIcc ∈ D₂ := by
    rw [hD₂, radArc_one, Set.mem_setOf_eq, inOpenDisc_coe_aux, hw₁]
    norm_num
  have hβ₁ : radArc w₂ t₂ oneIcc ∈ D₂ := by
    rw [hD₂, radArc_one, Set.mem_setOf_eq, inOpenDisc_coe_aux, hw₂]
    norm_num
  -- the interiors of the arcs avoid the two discs
  have hαint : ∀ s : Set.Icc (0:ℝ) 1, (s:ℝ) ∈ Set.Ioo 0 1 → radArc w₁ t₁ s ∉ D₁ ∪ D₂ := by
    intro s hs hmem
    rw [hD₁, hD₂] at hmem
    rcases hmem with hmem | hmem
    · simp only [Set.mem_image, radArc_apply] at hmem
      obtain ⟨y, hyW, hy⟩ := hmem
      have hy' : y = rayPar t₁ (s:ℝ) • w₁ := OnePoint.coe_injective hy
      have hr := rayPar_mem_Ioo ht₁ ht₁' hs
      exact hf₁ _ hr.1 hr.2 (hy' ▸ hyW)
    · simp only [Set.mem_setOf_eq, radArc_apply, inOpenDisc_coe_aux] at hmem
      have hr := rayPar_mem_Ioo ht₁ ht₁' hs
      rw [norm_smul_of_norm_eq_one hw₁ (le_of_lt (lt_trans ht₁ hr.1))] at hmem
      exact hmem hr.2
  have hβint : ∀ s : Set.Icc (0:ℝ) 1, (s:ℝ) ∈ Set.Ioo 0 1 → radArc w₂ t₂ s ∉ D₁ ∪ D₂ := by
    intro s hs hmem
    rw [hD₁, hD₂] at hmem
    rcases hmem with hmem | hmem
    · simp only [Set.mem_image, radArc_apply] at hmem
      obtain ⟨y, hyW, hy⟩ := hmem
      have hy' : y = rayPar t₂ (s:ℝ) • w₂ := OnePoint.coe_injective hy
      have hr := rayPar_mem_Ioo ht₂ ht₂' hs
      exact hf₂ _ hr.1 hr.2 (hy' ▸ hyW)
    · simp only [Set.mem_setOf_eq, radArc_apply, inOpenDisc_coe_aux] at hmem
      have hr := rayPar_mem_Ioo ht₂ ht₂' hs
      rw [norm_smul_of_norm_eq_one hw₂ (le_of_lt (lt_trans ht₂ hr.1))] at hmem
      exact hmem hr.2
  -- the arcs are injective
  have hαinj : Function.Injective (radArc w₁ t₁) := by
    intro s s' hss
    have h1 : ((rayPar t₁ (s:ℝ) • w₁ : ℂ)) = rayPar t₁ (s':ℝ) • w₁ := OnePoint.coe_injective hss
    rw [Complex.real_smul, Complex.real_smul] at h1
    have h2 : rayPar t₁ (s:ℝ) = rayPar t₁ (s':ℝ) := by
      have h3 := mul_right_cancel₀ hw₁ne h1
      exact_mod_cast h3
    exact Subtype.ext (rayPar_injOn ht₁' s.2 s'.2 h2)
  have hβinj : Function.Injective (radArc w₂ t₂) := by
    intro s s' hss
    have h1 : ((rayPar t₂ (s:ℝ) • w₂ : ℂ)) = rayPar t₂ (s':ℝ) • w₂ := OnePoint.coe_injective hss
    rw [Complex.real_smul, Complex.real_smul] at h1
    have h2 : rayPar t₂ (s:ℝ) = rayPar t₂ (s':ℝ) := by
      have h3 := mul_right_cancel₀ hw₂ne h1
      exact_mod_cast h3
    exact Subtype.ext (rayPar_injOn ht₂' s.2 s'.2 h2)
  -- the two arcs are disjoint, apart from their endpoints
  have hsep : ∀ s u : Set.Icc (0:ℝ) 1, (s:ℝ) ∈ Set.Ioo 0 1 → (u:ℝ) ∈ Set.Ioo 0 1 →
      radArc w₁ t₁ s ≠ radArc w₂ t₂ u := by
    intro s u hs hu hEq
    have h1 : ((rayPar t₁ (s:ℝ) • w₁ : ℂ)) = rayPar t₂ (u:ℝ) • w₂ := OnePoint.coe_injective hEq
    have hr₁ := rayPar_mem_Ioo ht₁ ht₁' hs
    have hr₂ := rayPar_mem_Ioo ht₂ ht₂' hu
    have h2 : rayPar t₁ (s:ℝ) = rayPar t₂ (u:ℝ) := by
      have h3 := congrArg norm h1
      rwa [norm_smul_of_norm_eq_one hw₁ (le_of_lt (lt_trans ht₁ hr₁.1)),
           norm_smul_of_norm_eq_one hw₂ (le_of_lt (lt_trans ht₂ hr₂.1))] at h3
    have h4 : w₁ = w₂ := by
      have h5 : rayPar t₁ (s:ℝ) • w₁ = rayPar t₁ (s:ℝ) • w₂ := by rw [h1, h2]
      rw [Complex.real_smul, Complex.real_smul] at h5
      exact mul_left_cancel₀ (by exact_mod_cast (ne_of_gt (lt_trans ht₁ hr₁.1))) h5
    exact hne h4
  have hαβ₀ : radArc w₁ t₁ zeroIcc ≠ radArc w₂ t₂ zeroIcc := by
    rw [radArc_zero, radArc_zero]
    intro hEq
    have h1 : ((t₁ • w₁ : ℂ)) = t₂ • w₂ := OnePoint.coe_injective hEq
    have h2 : t₁ = t₂ := by
      have h3 := congrArg norm h1
      rwa [norm_smul_of_norm_eq_one hw₁ (le_of_lt ht₁),
           norm_smul_of_norm_eq_one hw₂ (le_of_lt ht₂)] at h3
    exact hne (by
      rw [Complex.real_smul, Complex.real_smul, h2] at h1
      exact mul_left_cancel₀ (by exact_mod_cast (ne_of_gt ht₂)) h1)
  have hαβ₁ : radArc w₁ t₁ oneIcc ≠ radArc w₂ t₂ oneIcc := by
    rw [radArc_one, radArc_one]
    exact fun hEq => hne (OnePoint.coe_injective hEq)
  -- the two-component theorem on the Riemann sphere
  obtain ⟨Q₁, Q₂, hQ₁ne, hQ₂ne, hQ₁o, hQ₂o, hQd, hQu, hQ₁c, hQ₂c, hΦ, hΨ⟩ :=
    thetaTwoComponentsSpansH h hF
      ⟨exteriorDisc, exteriorDisc_injective, range_exteriorDisc⟩ hdisj
      (radArc w₁ t₁) (radArc w₂ t₂) hαinj hβinj hα₀ hα₁ hβ₀ hβ₁ hαint hβint hsep hαβ₀ hαβ₁
  have hQsub₁ : Q₁ ⊆ Set.range ((↑) : ℂ → RiemannSphere) := by
    intro x hx
    have hx' : x ∈ Set.univ \
        (D₁ ∪ D₂ ∪ Set.range (radArc w₁ t₁) ∪ Set.range (radArc w₂ t₂)) := by
      rw [← hQu]; exact Or.inl hx
    have hxnD₂ : x ∉ D₂ := fun hD => hx'.2 (Or.inl (Or.inl (Or.inr hD)))
    rw [hD₂] at hxnD₂
    simp only [Set.mem_setOf_eq, not_not] at hxnD₂
    obtain ⟨z, -, hz⟩ := hxnD₂
    exact ⟨z, hz⟩
  have hQsub₂ : Q₂ ⊆ Set.range ((↑) : ℂ → RiemannSphere) := by
    intro x hx
    have hx' : x ∈ Set.univ \
        (D₁ ∪ D₂ ∪ Set.range (radArc w₁ t₁) ∪ Set.range (radArc w₂ t₂)) := by
      rw [← hQu]; exact Or.inr hx
    have hxnD₂ : x ∉ D₂ := fun hD => hx'.2 (Or.inl (Or.inl (Or.inr hD)))
    rw [hD₂] at hxnD₂
    simp only [Set.mem_setOf_eq, not_not] at hxnD₂
    obtain ⟨z, -, hz⟩ := hxnD₂
    exact ⟨z, hz⟩
  -- identify the complement with the target set
  have hD₁mem : ∀ z : ℂ, ((z:ℂ):RiemannSphere) ∈ D₁ ↔ z ∈ W := by
    intro z
    rw [hD₁]
    exact ⟨fun hh => by
      obtain ⟨y, hyW, hy⟩ := hh
      rwa [← OnePoint.coe_injective hy], fun hh => ⟨z, hh, rfl⟩⟩
  have hD₂mem : ∀ z : ℂ, ((z:ℂ):RiemannSphere) ∈ D₂ ↔ ¬ (‖z‖ < 1) := by
    intro z
    rw [hD₂]
    simp only [Set.mem_setOf_eq, inOpenDisc_coe_aux]
  have hnotα : ∀ z : ℂ, ((z:ℂ):RiemannSphere) ∉ Set.range (radArc w₁ t₁) ↔
      ∀ s : Set.Icc (0:ℝ) 1, rayPar t₁ (s:ℝ) • w₁ ≠ z := by
    intro z
    constructor
    · intro hh s hcon
      refine hh ⟨s, ?_⟩
      show ((rayPar t₁ (s:ℝ) • w₁ : ℂ) : RiemannSphere) = ((z:ℂ):RiemannSphere)
      rw [hcon]
    · rintro hh ⟨s, hs⟩
      exact hh s (OnePoint.coe_injective hs)
  have hnotβ : ∀ z : ℂ, ((z:ℂ):RiemannSphere) ∉ Set.range (radArc w₂ t₂) ↔
      ∀ s : Set.Icc (0:ℝ) 1, rayPar t₂ (s:ℝ) • w₂ ≠ z := by
    intro z
    constructor
    · intro hh s hcon
      refine hh ⟨s, ?_⟩
      show ((rayPar t₂ (s:ℝ) • w₂ : ℂ) : RiemannSphere) = ((z:ℂ):RiemannSphere)
      rw [hcon]
    · rintro hh ⟨s, hs⟩
      exact hh s (OnePoint.coe_injective hs)
  have hA : ∀ z : ℂ, ((z:ℂ):RiemannSphere) ∈
        (Set.univ \ (D₁ ∪ D₂ ∪ Set.range (radArc w₁ t₁) ∪ Set.range (radArc w₂ t₂)))
      ↔ (z ∉ W) ∧ (‖z‖ < 1) ∧ (∀ s : Set.Icc (0:ℝ) 1, rayPar t₁ (s:ℝ) • w₁ ≠ z)
          ∧ (∀ u : Set.Icc (0:ℝ) 1, rayPar t₂ (u:ℝ) • w₂ ≠ z) := by
    intro z
    have hun : ((z:ℂ):RiemannSphere) ∉
        (D₁ ∪ D₂ ∪ Set.range (radArc w₁ t₁) ∪ Set.range (radArc w₂ t₂))
        ↔ ((¬((z:ℂ):RiemannSphere) ∈ D₁ ∧ ¬((z:ℂ):RiemannSphere) ∈ D₂)
            ∧ ¬((z:ℂ):RiemannSphere) ∈ Set.range (radArc w₁ t₁))
            ∧ ¬((z:ℂ):RiemannSphere) ∈ Set.range (radArc w₂ t₂) := by
      simp only [Set.mem_union, not_or]
    rw [Set.mem_sdiff]
    simp only [Set.mem_univ, true_and]
    rw [hun, hD₁mem z, hD₂mem z, hnotα z, hnotβ z]
    simp only [not_not]
    tauto
  have hB : ∀ z : ℂ, z ∈ Metric.ball (0:ℂ) 1 \ (W ∪ (fun r : ℝ => r • w₁) '' Set.Ioo t₁ 1
        ∪ (fun r : ℝ => r • w₂) '' Set.Ioo t₂ 1)
      ↔ (z ∉ W) ∧ (‖z‖ < 1) ∧ (∀ r : ℝ, t₁ < r → r < 1 → r • w₁ ≠ z)
          ∧ (∀ r : ℝ, t₂ < r → r < 1 → r • w₂ ≠ z) := by
    intro z
    have hball : z ∈ Metric.ball (0:ℂ) 1 ↔ ‖z‖ < 1 := by
      rw [Metric.mem_ball, dist_zero_right]
    have hun : z ∉ (W ∪ (fun r : ℝ => r • w₁) '' Set.Ioo t₁ 1
        ∪ (fun r : ℝ => r • w₂) '' Set.Ioo t₂ 1)
        ↔ ((z ∉ W ∧ z ∉ (fun r : ℝ => r • w₁) '' Set.Ioo t₁ 1)
            ∧ z ∉ (fun r : ℝ => r • w₂) '' Set.Ioo t₂ 1) := by
      simp only [Set.mem_union, not_or]
    have himg₁ : z ∉ (fun r : ℝ => r • w₁) '' Set.Ioo t₁ 1
        ↔ ∀ r : ℝ, t₁ < r → r < 1 → r • w₁ ≠ z := by
      rw [Set.mem_image]; simp only [not_exists, not_and]
      constructor
      · intro hh r hr hr1; exact hh r ⟨hr, hr1⟩
      · intro hh r hr; exact hh r hr.1 hr.2
    have himg₂ : z ∉ (fun r : ℝ => r • w₂) '' Set.Ioo t₂ 1
        ↔ ∀ r : ℝ, t₂ < r → r < 1 → r • w₂ ≠ z := by
      rw [Set.mem_image]; simp only [not_exists, not_and]
      constructor
      · intro hh r hr hr1; exact hh r ⟨hr, hr1⟩
      · intro hh r hr; exact hh r hr.1 hr.2
    rw [Set.mem_sdiff, hball, hun, himg₁, himg₂]
    tauto
  have hset : ((↑) ⁻¹' (Set.univ \
        (D₁ ∪ D₂ ∪ Set.range (radArc w₁ t₁) ∪ Set.range (radArc w₂ t₂))) : Set ℂ)
      = Metric.ball (0:ℂ) 1 \ (W ∪ (fun r : ℝ => r • w₁) '' Set.Ioo t₁ 1
          ∪ (fun r : ℝ => r • w₂) '' Set.Ioo t₂ 1) := by
    ext z
    rw [Set.mem_preimage, hA z, hB z]
    constructor
    · rintro ⟨hW', hzn, hα, hβ⟩
      exact ⟨hW', hzn, (forall_rayPar_ne_iff ht₁' hw₁ hm₁ hW' hzn).mp hα,
        (forall_rayPar_ne_iff ht₂' hw₂ hm₂ hW' hzn).mp hβ⟩
    · rintro ⟨hW', hzn, hα, hβ⟩
      exact ⟨hW', hzn, (forall_rayPar_ne_iff ht₁' hw₁ hm₁ hW' hzn).mpr hα,
        (forall_rayPar_ne_iff ht₂' hw₂ hm₂ hW' hzn).mpr hβ⟩
  refine ⟨(↑) ⁻¹' Q₁, (↑) ⁻¹' Q₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hQ₁ne
    obtain ⟨z, hz⟩ := hQsub₁ hx
    exact ⟨z, by show ((z:ℂ):RiemannSphere) ∈ Q₁; rw [hz]; exact hx⟩
  · obtain ⟨x, hx⟩ := hQ₂ne
    obtain ⟨z, hz⟩ := hQsub₂ hx
    exact ⟨z, by show ((z:ℂ):RiemannSphere) ∈ Q₂; rw [hz]; exact hx⟩
  · exact isOpen_pullback_coe hQ₁o
  · exact isOpen_pullback_coe hQ₂o
  · rw [Set.disjoint_iff_inter_eq_empty] at hQd ⊢
    rw [← Set.preimage_inter, hQd, Set.preimage_empty]
  · rw [← Set.preimage_union, hQu]
    exact hset
  · exact isPreconnected_preimage_coe hQ₁c hQ₁ne hQsub₁
  · exact isPreconnected_preimage_coe hQ₂c hQ₂ne hQsub₂

end

end Work.Smooth.SphereJordan
