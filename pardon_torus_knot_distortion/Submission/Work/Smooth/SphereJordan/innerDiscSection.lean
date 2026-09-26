import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.familyDataOfTwoDiscs
import Submission.Work.Smooth.SphereJordan.mobiusAddInv

/-!
# `innerDiscSection`

Let `γ : ℝ → ℂ` be a simple closed plane curve lying in the closed unit disc (`‖γ t‖ ≤ 1`), and let
`T : TwoDiscs (fun t => (γ t : RiemannSphere))` decompose the Riemann sphere `ℂ ∪ {∞}` into the two
complementary discs bounded by `γ`.  The *inner* disc `T.inner ∞` is the one not containing `∞`
(and we assume, as the statement does, that this disc misses `∞`).

Then `T.inner ∞` is (the Riemann-sphere image of) a continuous map `𝔻 → 𝔻` into the *closed unit
disc*: the geometric content is that the bounded side of `γ` is contained in the closed unit disc,
because the complement of the closed unit disc in the sphere is preconnected, contains `∞` (which
lies in the *outer* side of `γ`) and misses `γ`.

The complement of the closed unit ball is preconnected because inversion
(`invHomeomorph`, from `mobiusAddInv`) carries the open unit ball onto it.
-/

open Set

namespace Work.Smooth.SphereJordan

noncomputable section

theorem innerDiscSection (h : PlaneHypothesis) {γ : ℝ → ℂ} (hcont : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    (hball : ∀ t, ‖γ t‖ ≤ 1) (T : TwoDiscs (fun t => (γ t : RiemannSphere)))
    (hinf : ∀ z : Disc, T.inner infty z ≠ infty) :
    ∃ s : C(Disc, Disc), ∀ z : Disc, (((s z : Disc) : ℂ) : RiemannSphere) = T.inner infty z := by
  classical
  have hK : infty ∉ Set.range (fun t : ℝ => (γ t : RiemannSphere)) := by
    rintro ⟨t, ht⟩
    exact OnePoint.coe_ne_infty (γ t) ht
  -- ### Step 1: the `ℂ`-valued map underlying the inner disc
  have hex : ∀ z : Disc, ∃ w : ℂ, (w : RiemannSphere) = T.inner infty z := fun z =>
    OnePoint.ne_infty_iff_exists.mp (hinf z)
  let g : Disc → ℂ := fun z => (hex z).choose
  have hg : ∀ z : Disc, (g z : RiemannSphere) = T.inner infty z := fun z => (hex z).choose_spec
  have hgcont : Continuous g := by
    have hcomp : Continuous (fun z : Disc => ((g z : ℂ) : RiemannSphere)) := by
      have hfun : (fun z : Disc => ((g z : ℂ) : RiemannSphere)) = fun z => T.inner infty z :=
        funext fun z => hg z
      rw [hfun]
      exact (T.inner infty).continuous
    exact (Topology.IsInducing.continuous_iff OnePoint.isOpenEmbedding_coe.isInducing).mpr hcomp
  -- ### Step 2: the closed unit ball of the sphere
  set sB : Set RiemannSphere := ((↑) : ℂ → RiemannSphere) '' Metric.closedBall (0 : ℂ) 1 with hsB
  set oB : Set RiemannSphere := ((↑) : ℂ → RiemannSphere) '' Metric.ball (0 : ℂ) 1 with hoB
  have hmem_sB : ∀ w : ℂ, ‖w‖ ≤ 1 → (w : RiemannSphere) ∈ sB := by
    intro w hw
    rw [hsB]
    exact ⟨w, by rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero], rfl⟩
  have hKsub : Set.range (fun t : ℝ => (γ t : RiemannSphere)) ⊆ sB := by
    rintro x ⟨t, rfl⟩
    exact hmem_sB (γ t) (hball t)
  have hinfW : infty ∉ sB := by
    rw [hsB]
    rintro ⟨w, -, hw⟩
    exact OnePoint.coe_ne_infty w hw
  -- ### Step 3: the complement of the closed unit ball is preconnected
  have hpre_oB : IsPreconnected oB := by
    rw [hoB]
    exact Metric.isPreconnected_ball.image ((↑) : ℂ → RiemannSphere)
      OnePoint.continuous_coe.continuousOn
  have himg : invHomeomorph '' oB = sBᶜ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hoB] at hx
      obtain ⟨w, hw, rfl⟩ := hx
      have hwlt : ‖w‖ < 1 := by
        simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hw
      rw [Set.mem_compl_iff, hsB]
      rintro ⟨u, hu, huy⟩
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hu
      rcases eq_or_ne w 0 with rfl | hw0
      · rw [invHomeomorph_coe_zero] at huy
        exact OnePoint.coe_ne_infty u huy
      · rw [invHomeomorph_coe_ne hw0] at huy
        have huw : u = w⁻¹ := OnePoint.coe_eq_coe.mp huy
        have hwnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw0
        have h1 : 1 < ‖w‖⁻¹ := (one_lt_inv₀ hwnorm).mpr hwlt
        have h2 : ‖w‖⁻¹ ≤ 1 := by
          rw [← norm_inv, ← huw]
          exact hu
        exact absurd h2 (not_le.mpr h1)
    · intro hy
      rw [Set.mem_compl_iff, hsB] at hy
      rcases eq_or_ne y infty with rfl | hyinf
      · refine ⟨((0 : ℂ) : RiemannSphere), ?_, invHomeomorph_coe_zero⟩
        rw [hoB]
        exact ⟨0, by simp [Metric.mem_ball], rfl⟩
      · obtain ⟨u, hu⟩ := OnePoint.ne_infty_iff_exists.mp hyinf
        have hu1 : 1 < ‖u‖ := by
          by_contra hcon
          rw [not_lt] at hcon
          exact hy ⟨u, by simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hcon, hu⟩
        rcases eq_or_ne u 0 with rfl | hu0
        · simp only [norm_zero] at hu1
          exact absurd hu1 (by norm_num)
        · refine ⟨((u⁻¹ : ℂ) : RiemannSphere), ?_, ?_⟩
          · rw [hoB]
            exact ⟨u⁻¹, by
              rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_inv]
              exact inv_lt_one_of_one_lt₀ hu1, rfl⟩
          · rw [invHomeomorph_coe_ne (inv_ne_zero hu0)]
            simpa [inv_inv] using hu
  have hpre_inv : IsPreconnected (invHomeomorph '' oB) :=
    hpre_oB.image invHomeomorph invHomeomorph.continuous.continuousOn
  have hWpre : IsPreconnected (sBᶜ : Set RiemannSphere) := by
    rw [← himg]
    exact hpre_inv
  -- ### Step 4: the bounded side of `γ` lies in the closed unit ball
  have hVmem : infty ∈ T.outSide infty := TwoDiscs.mem_outSide_self T infty hK
  have hne : ((sBᶜ : Set RiemannSphere) ∩ T.outSide infty).Nonempty := ⟨infty, hinfW, hVmem⟩
  have hWsub : (sBᶜ : Set RiemannSphere) ⊆ T.outSide infty ∪ T.inSide infty := by
    intro x hx
    rcases TwoDiscs.inSide_or_range_or_outSide T infty x with h1 | h1 | h1
    · exact Or.inr h1
    · exact absurd (hKsub h1) hx
    · exact Or.inl h1
  have hWsubV : (sBᶜ : Set RiemannSphere) ⊆ T.outSide infty :=
    IsPreconnected.subset_left_of_subset_union (TwoDiscs.isOpen_outSide T infty)
      (TwoDiscs.isOpen_inSide T infty) (TwoDiscs.disjoint_inSide_outSide T infty).symm
      hWsub hne hWpre
  have hUsub : T.inSide infty ⊆ sB := by
    intro x hx
    by_contra hxnot
    exact (Set.disjoint_left.mp (TwoDiscs.disjoint_inSide_outSide T infty)) hx (hWsubV hxnot)
  -- ### Step 5: assemble
  have hnorm : ∀ z : Disc, ‖g z‖ ≤ 1 := by
    intro z
    have hz : T.inner infty z ∈
        T.inSide infty ∪ Set.range (fun t : ℝ => (γ t : RiemannSphere)) := by
      rw [← TwoDiscs.range_inner_eq T infty]
      exact ⟨z, rfl⟩
    rcases hz with hzU | hzK
    · have hmem : T.inner infty z ∈ sB := hUsub hzU
      rw [hsB] at hmem
      obtain ⟨w, hw, hwx⟩ := hmem
      have hgw : g z = w := OnePoint.coe_eq_coe.mp (by rw [hg z, ← hwx])
      rw [hgw]
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hw
      exact hw
    · obtain ⟨t, ht⟩ := hzK
      have hgt : g z = γ t := OnePoint.coe_eq_coe.mp (by rw [hg z, ← ht])
      rw [hgt]
      exact hball t
  have hmem : ∀ z : Disc, g z ∈ Metric.closedBall (0 : ℂ) 1 := fun z => by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact hnorm z
  refine ⟨⟨fun z => ⟨g z, hmem z⟩, ?_⟩, fun z => hg z⟩
  exact Continuous.subtype_mk hgcont hmem

end

end Work.Smooth.SphereJordan
