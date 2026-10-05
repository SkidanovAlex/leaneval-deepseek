import Mathlib
import Submission.Work.RPB1a.Defs
import Submission.Work.RPB1a.Geometry
import Submission.Work.RPB1a.isPreconnected_annulus_shell

namespace Work.RPB1a

open Complex Set Metric
open scoped ContDiff Real
open Work.RPB1a

/-- N4b: for a collar `Γ` of the boundary `range v` of `D`, exactly one of the two halves of the
collar lies in `D`.

Route (elementary topology, no outside library).  From `hDo` and `hDfr`, `closure D = D ∪ range v`,
so `ℂ = D ⊔ ((D ∪ range v)ᶜ)` with both parts open; a preconnected set missing `range v` lies in `D`
or in `(D ∪ range v)ᶜ`.  The two halves `annulus ρ ∩ ball 0 1` and `annulus ρ \ closedBall 0 1` are
preconnected (e.g. as images of the convex strips `{log ρ < Re ζ < 0}` and `{0 < Re ζ < -log ρ}`
under `ζ ↦ exp ζ`, or by an explicit path argument), and their `Γ`-images miss
`range v = Γ '' sphere 0 1` by injectivity (`hΓcirc`, `hΓi`).

* Both halves outside `D`: `Γ '' annulus ρ` is open (`hΓo`), contains `v 0`, and lies in
  `(D ∪ range v)ᶜ ∪ range v`, so a ball `B (v 0) ε ⊆ (D ∪ range v)ᶜ ∪ range v`; since
  `D ∩ range v = ∅` (`hDdisj`) that ball misses `D`, contradicting `v 0 ∈ frontier D ⊆ closure D`.
* Both halves inside `D`: then `Γ '' annulus ρ ⊆ D ∪ range v = closure D` is an open neighbourhood
  of `v 0`, so `v 0 ∈ interior (closure D)`, contradicting `hDext`, which says
  `v 0 ∈ closure ((D ∪ range v)ᶜ) = (interior (closure D))ᶜ`.

Hence at least one half is inside and not both, which is the stated disjunction (up to symmetry of
`Disjoint`). -/
theorem collar_side (v : ℝ → ℂ) (D : Set ℂ) (hDo : IsOpen D)
    (hDfr : frontier D = range v) (hDdisj : Disjoint D (range v))
    (hDext : range v ⊆ closure (D ∪ range v)ᶜ)
    (Γ : ℂ → ℂ) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hΓc : ContinuousOn Γ (annulus ρ)) (hΓi : InjOn Γ (annulus ρ))
    (hΓo : IsOpen (Γ '' annulus ρ))
    (hΓcirc : ∀ t : ℝ, Γ (Complex.exp (t * I)) = v t) :
    (Γ '' (annulus ρ ∩ ball 0 1) ⊆ D ∧ Disjoint (Γ '' (annulus ρ \ closedBall 0 1)) D) ∨
    (Γ '' (annulus ρ \ closedBall 0 1) ⊆ D ∧ Disjoint (Γ '' (annulus ρ ∩ ball 0 1)) D) := by
  have hρinv : 1 < ρ⁻¹ := (one_lt_inv₀ hρ0).2 hρ1
  have h1ann : (1 : ℂ) ∈ annulus ρ := by
    change ρ < ‖(1 : ℂ)‖ ∧ ‖(1 : ℂ)‖ < ρ⁻¹
    rw [norm_one]
    exact ⟨hρ1, hρinv⟩
  have hv0 : Γ 1 = v 0 := by simpa using hΓcirc 0
  have hcl : closure D = D ∪ range v := by rw [closure_eq_self_union_frontier, hDfr]
  have hv0cl : v 0 ∈ closure D := by rw [hcl]; exact Or.inr ⟨0, rfl⟩
  have h1exp : ∀ t : ℝ, ‖Complex.exp (t * I)‖ = 1 := by
    intro t
    rw [Complex.norm_exp]
    simp
  -- any point of the collar mapping into `range v` lies on the unit circle
  have hkey : ∀ w ∈ annulus ρ, Γ w ∈ range v → w ∈ sphere 0 1 := by
    intro w hw hwv
    obtain ⟨t, ht⟩ := hwv
    have hexpmem : Complex.exp (t * I) ∈ annulus ρ := by
      change ρ < ‖Complex.exp (t * I)‖ ∧ ‖Complex.exp (t * I)‖ < ρ⁻¹
      rw [h1exp t]
      exact ⟨hρ1, hρinv⟩
    have hww : w = Complex.exp (t * I) :=
      hΓi hw hexpmem (by rw [ht.symm]; exact (hΓcirc t).symm)
    rw [hww, mem_sphere, dist_eq_norm, sub_zero]
    exact h1exp t
  -- the unit circle maps into `range v`
  have hsphere_mem : ∀ w : ℂ, w ∈ sphere 0 1 → Γ w ∈ range v := by
    intro w hw
    have hw1 : ‖w‖ = 1 := by
      rw [mem_sphere, dist_eq_norm, sub_zero] at hw
      exact hw
    have heq : Complex.exp ((w.arg : ℂ) * I) = w := by
      have h := Complex.norm_mul_exp_arg_mul_I w
      rw [hw1] at h
      simpa using h
    exact ⟨w.arg, by rw [← hΓcirc w.arg, heq]⟩
  -- the collar is covered by its two halves together with the unit circle
  have htri : ∀ w ∈ annulus ρ,
      w ∈ (annulus ρ ∩ ball 0 1) ∪ (annulus ρ \ closedBall 0 1) ∪ sphere 0 1 := by
    intro w hw
    rcases lt_trichotomy ‖w‖ 1 with h | h | h
    · exact Or.inl (Or.inl ⟨hw, by rwa [Metric.mem_ball, dist_eq_norm, sub_zero]⟩)
    · exact Or.inr (by rw [mem_sphere, dist_eq_norm, sub_zero]; exact h)
    · exact Or.inl (Or.inr
        ⟨hw, by rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact not_le.mpr h⟩)
  -- the two halves, described as shells in the modulus
  have hInner_eq : annulus ρ ∩ ball 0 1 = {w : ℂ | ρ < ‖w‖ ∧ ‖w‖ < 1} := by
    ext w
    change (ρ < ‖w‖ ∧ ‖w‖ < ρ⁻¹) ∧ w ∈ ball 0 1 ↔ ρ < ‖w‖ ∧ ‖w‖ < 1
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, lt_trans h.2 hρinv⟩, h.2⟩⟩
  have hOuter_eq : annulus ρ \ closedBall 0 1 = {w : ℂ | 1 < ‖w‖ ∧ ‖w‖ < ρ⁻¹} := by
    ext w
    change (ρ < ‖w‖ ∧ ‖w‖ < ρ⁻¹) ∧ w ∉ closedBall 0 1 ↔ 1 < ‖w‖ ∧ ‖w‖ < ρ⁻¹
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, not_le]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨lt_trans hρ1 h.1, h.2⟩, h.1⟩⟩
  have hInner_pre : IsPreconnected (annulus ρ ∩ ball 0 1) := by
    rw [hInner_eq]; exact isPreconnected_annulus_shell hρ0 hρ1
  have hOuter_pre : IsPreconnected (annulus ρ \ closedBall 0 1) := by
    rw [hOuter_eq]; exact isPreconnected_annulus_shell one_pos hρinv
  have hInner_img_pre : IsPreconnected (Γ '' (annulus ρ ∩ ball 0 1)) :=
    hInner_pre.image Γ (hΓc.mono inter_subset_left)
  have hOuter_img_pre : IsPreconnected (Γ '' (annulus ρ \ closedBall 0 1)) :=
    hOuter_pre.image Γ (hΓc.mono sdiff_subset)
  -- the two half-images miss `range v`
  have hInner_miss : Γ '' (annulus ρ ∩ ball 0 1) ⊆ (range v)ᶜ := by
    rintro y ⟨w, ⟨hwann, hwball⟩, rfl⟩ hyv
    have hsp := hkey w hwann hyv
    rw [mem_sphere, dist_eq_norm, sub_zero] at hsp
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hwball
    linarith
  have hOuter_miss : Γ '' (annulus ρ \ closedBall 0 1) ⊆ (range v)ᶜ := by
    rintro y ⟨w, ⟨hwann, hwcb⟩, rfl⟩ hyv
    have hsp := hkey w hwann hyv
    rw [mem_sphere, dist_eq_norm, sub_zero] at hsp
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hwcb
    exact hwcb hsp.le
  -- `(range v)ᶜ` is the disjoint union of `D` and `(closure D)ᶜ`
  have hcompl : (range v)ᶜ = D ∪ (closure D)ᶜ := by
    rw [hcl]
    ext x
    simp only [Set.mem_compl_iff, Set.mem_union]
    constructor
    · intro hx
      by_cases hxD : x ∈ D
      · exact Or.inl hxD
      · exact Or.inr (fun h => h.elim hxD hx)
    · rintro (hxD | hx)
      · exact fun hy => (Set.disjoint_left.mp hDdisj) hxD hy
      · exact fun hy => hx (Or.inr hy)
  have hDisjD : Disjoint D (closure D)ᶜ := by
    rw [Set.disjoint_left]
    intro x hxD hxc
    exact hxc (subset_closure hxD)
  have hCopen : IsOpen (closure D)ᶜ := isClosed_closure.isOpen_compl
  -- each half-image is entirely inside `D` or entirely outside `closure D`
  have hInner_or : Γ '' (annulus ρ ∩ ball 0 1) ⊆ D ∨
      Γ '' (annulus ρ ∩ ball 0 1) ⊆ (closure D)ᶜ := by
    refine hInner_img_pre.subset_or_subset hDo hCopen hDisjD ?_
    rw [← hcompl]
    exact hInner_miss
  have hOuter_or : Γ '' (annulus ρ \ closedBall 0 1) ⊆ D ∨
      Γ '' (annulus ρ \ closedBall 0 1) ⊆ (closure D)ᶜ := by
    refine hOuter_img_pre.subset_or_subset hDo hCopen hDisjD ?_
    rw [← hcompl]
    exact hOuter_miss
  have hv0U : v 0 ∈ Γ '' annulus ρ := ⟨1, h1ann, hv0⟩
  have hv0notint : v 0 ∉ interior (closure D) := by
    intro hmem
    have h := hDext ⟨0, rfl⟩
    rw [← hcl, closure_compl, Set.mem_compl_iff] at h
    exact h hmem
  -- not both halves can lie in `D`: that would make `Γ '' annulus ρ` an open
  -- neighbourhood of `v 0` inside `closure D`, contradicting `hDext`
  have hnotboth_in : ¬ (Γ '' (annulus ρ ∩ ball 0 1) ⊆ D ∧
      Γ '' (annulus ρ \ closedBall 0 1) ⊆ D) := by
    rintro ⟨hIin, hOin⟩
    have hUsub : Γ '' annulus ρ ⊆ closure D := by
      rw [hcl]
      rintro y ⟨w, hwann, rfl⟩
      rcases htri w hwann with (h | h) | h
      · exact Or.inl (hIin ⟨w, h, rfl⟩)
      · exact Or.inl (hOin ⟨w, h, rfl⟩)
      · exact Or.inr (hsphere_mem w h)
    exact hv0notint (hΓo.subset_interior_iff.mpr hUsub hv0U)
  -- not both halves can lie outside `D`: that would make `Γ '' annulus ρ` an open
  -- neighbourhood of `v 0` inside `Dᶜ`, contradicting `v 0 ∈ frontier D ⊆ closure D`
  have hnotboth_out : ¬ (Γ '' (annulus ρ ∩ ball 0 1) ⊆ (closure D)ᶜ ∧
      Γ '' (annulus ρ \ closedBall 0 1) ⊆ (closure D)ᶜ) := by
    rintro ⟨hIout, hOout⟩
    have hUsub : Γ '' annulus ρ ⊆ (closure D)ᶜ ∪ range v := by
      rintro y ⟨w, hwann, rfl⟩
      rcases htri w hwann with (h | h) | h
      · exact Or.inl (hIout ⟨w, h, rfl⟩)
      · exact Or.inl (hOout ⟨w, h, rfl⟩)
      · exact Or.inr (hsphere_mem w h)
    obtain ⟨y, hyU, hyD⟩ := (_root_.mem_closure_iff.mp hv0cl) (Γ '' annulus ρ) hΓo hv0U
    rcases hUsub hyU with hyc | hyr
    · exact hyc (subset_closure hyD)
    · exact (Set.disjoint_left.mp hDdisj) hyD hyr
  -- exactly one half lies in `D`
  rcases hInner_or with hI | hI <;> rcases hOuter_or with hO | hO
  · exact absurd ⟨hI, hO⟩ hnotboth_in
  · refine Or.inl ⟨hI, ?_⟩
    rw [Set.disjoint_left]
    intro y hy hyD
    exact hO hy (subset_closure hyD)
  · refine Or.inr ⟨hO, ?_⟩
    rw [Set.disjoint_left]
    intro y hy hyD
    exact hI hy (subset_closure hyD)
  · exact absurd ⟨hI, hO⟩ hnotboth_out

end Work.RPB1a
