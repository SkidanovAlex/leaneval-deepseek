import Mathlib
import Submission.Work.Whitney.CutPush.arc_straightening
import Submission.Work.Whitney.CutPush.arc_localisation
import Submission.Work.Whitney.CutPush.arc_direction_generic
import Submission.Work.Whitney.CutPush.box_separation_arc
import Submission.Work.Whitney.CutPush.partition_of_unity_trail_arc
import Submission.Work.Whitney.CutPush.finite_localRetraction_sep
import Submission.Work.Whitney.CutPush.flow_of_compactSupport
import Submission.Work.ODE.GlobalFlow
import Submission.Work.ODE.SmoothFlow
import Submission.Work.ODE.CompactSupportBounds
import Submission.Work.Whitney.exists_flow_map_of_compactSupport

/-!
# Unknotting an arc in `ℝ^m`, `m ≥ 4`

Target: every smooth, injective, regular arc `c : ℝ → ℝ^m` (`m ≥ 4`) can be carried onto the
straight segment `t ↦ c 0 + t • (c 1 - c 0)` (`t ∈ [0,1]`) by a global `C^∞` diffeomorphism of
`ℝ^m` (`Work.Whitney.CutPush.arc_unknotting`).

The proof has three parts.

* **A chord-free direction** (`CutPush/arc_direction_generic`): a direction `v ≠ 0` such that no
  chord of the arc and no tangent of the arc is parallel to `v`.  Its existence is the
  Sard-flavoured genericity input of the argument, proved by the Hausdorff-dimension substitute for
  Sard (the bad directions form the image of two `C¹` maps from a `3`- and a `2`-dimensional domain,
  so its dimension is `≤ 3 < m`).

* **Isotopy extension for the arc family** (`arc_ambient` below): the localised straightening family
  `Φ lam t = localisedArc c v 1 lam t` (which runs from the arc to the straight segment in direction
  `v`, is injective and regular on `Icc 0 1` at every time, is stationary outside `[0,1]` in the time
  parameter and has bounded trail) is realised by a global diffeomorphism `A₁` with `A₁ (c t)`
  `= c 0 + t • v`.  The construction is the classical one:
  * separated local retractions of the family on finitely many boxes
    (`CutPush/finite_localRetraction_sep`),
  * a smooth partition of unity subordinate to those boxes on the trail
    (`CutPush/partition_of_unity_trail_arc`),
  * the patched velocity field `(lam, y) ↦ ∑ j, ψ j lam y • vel lam (par j lam y)`, which agrees with
    the family's own velocity on the trail (`patchedVelocityOn`), cut off in the space variable along
    the (bounded) trail and in the time variable,
  * the flow of the autonomous field `(lam, y) ↦ (1, V lam y)` on `ℝ × ℝ^m`
    (`CutPush/flow_of_compactSupport`); the first coordinate of an integral curve of this field is the
    flow time, which identifies the time-`1` map with the family and produces the inverse from the
    time-`(-1)` map.

* **Assembly**: applying the same ambience lemma a second time, to the family which rotates the
  direction of a *straight* segment from `v` to `u = c 1 - c 0`, gives a diffeomorphism `A₂` with
  `A₂ (c 0 + t • v) = c 0 + t • u`.  The composite `A₂ ∘ A₁` is the required diffeomorphism, and
  `A₁⁻¹ ∘ A₂⁻¹` its inverse.
-/

open scoped Manifold ContDiff
open Topology Set Function MeasureTheory

namespace Work.Whitney.CutPush

/-- The derivative of `G : ℝ × ℝ → F` in the first variable is the derivative of the section. -/
lemma fderiv_apply_inl {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : ℝ × ℝ → F) {s t : ℝ} (hG : DifferentiableAt ℝ G (s, t)) :
    fderiv ℝ G (s, t) (1, 0) = fderiv ℝ (fun u : ℝ => G (u, t)) s 1 := by
  have h1 : HasFDerivAt (fun u : ℝ => (u, t)) (ContinuousLinearMap.inl ℝ ℝ ℝ) s :=
    hasFDerivAt_prodMk_left s t
  have h2 : HasFDerivAt (fun u : ℝ => G (u, t))
      ((fderiv ℝ G (s, t)) ∘L ContinuousLinearMap.inl ℝ ℝ ℝ) s := by
    simpa only [Function.comp_def] using hG.hasFDerivAt.comp s h1
  rw [h2.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]

/-- The section `u ↦ G (u, t)` has derivative the first partial derivative of `G`. -/
lemma section_deriv_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : ℝ × ℝ → F) {s t : ℝ} (hG : DifferentiableAt ℝ G (s, t)) :
    HasDerivAt (fun u : ℝ => G (u, t)) (fderiv ℝ G (s, t) (1, 0)) s := by
  have h1 : HasFDerivAt (fun u : ℝ => (u, t)) (ContinuousLinearMap.inl ℝ ℝ ℝ) s :=
    hasFDerivAt_prodMk_left s t
  have h2 : HasFDerivAt (fun u : ℝ => G (u, t))
      ((fderiv ℝ G (s, t)) ∘L ContinuousLinearMap.inl ℝ ℝ ℝ) s := by
    simpa only [Function.comp_def] using hG.hasFDerivAt.comp s h1
  rw [fderiv_apply_inl G hG]
  exact (h2.differentiableAt.hasFDerivAt).hasDerivAt

/-- A product of a smooth scalar function with a function that is smooth on an open set containing
the (closed) support of the scalar factor is smooth. -/
lemma contDiff_smul_of_tsupport {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → ℝ} {g : E → F} {U : Set E} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g U) (hU : IsOpen U)
    (hsupp : tsupport f ⊆ U) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => f x • g x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hxU : x ∈ U
  · exact (hf.contDiffAt.smul (hg.contDiffAt (hU.mem_nhds hxU)))
  · have hmem : ∀ᶠ y in 𝓝 x, y ∉ tsupport f :=
      (isClosed_tsupport f).isOpen_compl.mem_nhds (fun h => hxU (hsupp h))
    refine (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq ?_
    filter_upwards [hmem] with y hy
    have : f y = 0 := by
      by_contra h
      exact hy (subset_tsupport _ h)
    simp [this]

/-- Patching velocities along the trail, with the trail parameter restricted to `[0,1]`. -/
theorem patchedVelocityOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type}
    [Fintype ι]
    (Φ : ℝ → ℝ → E) (vel : ℝ → ℝ → E) (par : ι → ℝ → E → ℝ) (ψ : ι → ℝ → E → ℝ)
    (hψsum : ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1,
      ∑ i, ψ i lam (Φ lam t) = 1)
    (hcorrect : ∀ i, ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1,
      ψ i lam (Φ lam t) ≠ 0 → par i lam (Φ lam t) = t) :
    ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1,
      (∑ i, ψ i lam (Φ lam t) • vel lam (par i lam (Φ lam t))) = vel lam t := by
  intro lam hlam t ht
  have hterm : ∀ i, ψ i lam (Φ lam t) • vel lam (par i lam (Φ lam t))
      = ψ i lam (Φ lam t) • vel lam t := by
    intro i
    by_cases h : ψ i lam (Φ lam t) = 0
    · rw [h, zero_smul, zero_smul]
    · rw [hcorrect i lam hlam t ht h]
  calc (∑ i, ψ i lam (Φ lam t) • vel lam (par i lam (Φ lam t)))
      = ∑ i, ψ i lam (Φ lam t) • vel lam t := Finset.sum_congr rfl fun i _ => hterm i
    _ = (∑ i, ψ i lam (Φ lam t)) • vel lam t := (Finset.sum_smul).symm
    _ = (1 : ℝ) • vel lam t := by rw [hψsum lam hlam t ht]
    _ = vel lam t := one_smul _ _

end Work.Whitney.CutPush
namespace Work.Whitney.CutPush

set_option maxHeartbeats 1000000 in
/-- **Isotopy extension for a family of arcs.** -/
theorem arc_ambient {m : ℕ} (Φ : ℝ → ℝ → EuclideanSpace ℝ (Fin m))
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => Φ p.1 p.2))
    (hinj : ∀ lam : ℝ, Set.InjOn (Φ lam) (Set.Icc (0 : ℝ) 1))
    (hreg : ∀ lam t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → fderiv ℝ (Φ lam) t 1 ≠ 0)
    (hstat0 : ∀ lam t : ℝ, lam ≤ 0 → Φ lam t = Φ 0 t)
    (hstat1 : ∀ lam t : ℝ, 1 ≤ lam → Φ lam t = Φ 1 t)
    (hbound : ∃ K : Set (EuclideanSpace ℝ (Fin m)), IsCompact K ∧
      ∀ lam, lam ∈ Set.Icc (0 : ℝ) 1 → ∀ t, Φ lam t ∈ K) :
    ∃ (A Ainv : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ainv ∧
      Function.LeftInverse Ainv A ∧ Function.RightInverse Ainv A ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, A (Φ 0 t) = Φ 1 t) := by
  classical
  obtain ⟨ι, hι, O, U, B, par, hO, hU, hB, hsm, hretr, hsep, hcover⟩ :=
    exists_finite_localRetraction_sep Φ hΦ hinj hreg
  haveI : Fintype ι := hι
  obtain ⟨ψ, hψsm, hψnn, hψtsupp, hψsum⟩ :=
    partition_of_unity_trail_arc (ι := ι) hO hB hΦ.continuous 0 1
      (fun s hs x hx => by
        obtain ⟨j, hj1, hj2, hj3⟩ := hcover s hs x hx
        exact ⟨j, hj1, hj3⟩)
  have hψsupp : ∀ j s z, ψ j s z ≠ 0 → s ∈ O j ∧ z ∈ B j := by
    intro j s z hz
    have hmem : (s, z) ∈ tsupport (fun p : ℝ × EuclideanSpace ℝ (Fin m) => ψ j p.1 p.2) :=
      subset_tsupport _ (by simpa using hz)
    exact hψtsupp j hmem
  let vel : ℝ → ℝ → EuclideanSpace ℝ (Fin m) :=
    fun lam t => fderiv ℝ (fun p : ℝ × ℝ => Φ p.1 p.2) (lam, t) (1, 0)
  have hvel_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => vel p.1 p.2) := by
    have hfd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => Φ q.1 q.2) p) := by
      have h := (contDiffOn_infty_iff_fderiv_of_isOpen (𝕜 := ℝ)
        (f := fun q : ℝ × ℝ => Φ q.1 q.2) (s := Set.univ) isOpen_univ).mp
        (hΦ.contDiffOn (s := Set.univ))
      exact contDiffOn_univ.mp h.2
    have h2 := hfd.clm_apply (contDiff_const : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun _ : ℝ × ℝ => ((1:ℝ), (0:ℝ))))
    exact h2
  have hvel_section : ∀ s t : ℝ, vel s t = fderiv ℝ (fun u : ℝ => Φ u t) s 1 :=
    fun s t => fderiv_apply_inl (fun p : ℝ × ℝ => Φ p.1 p.2)
      ((hΦ.differentiable (by simp)) (s, t))
  have hvel_zero_left : ∀ s : ℝ, s < 0 → ∀ y, vel s y = 0 := by
    intro s hs y
    rw [hvel_section s y]
    have hev : (fun u : ℝ => Φ u y) =ᶠ[𝓝 s] fun _ => Φ 0 y := by
      filter_upwards [isOpen_Iio.mem_nhds hs] with u hu
      exact hstat0 u y (le_of_lt hu)
    rw [hev.fderiv_eq]
    simp
  have hvel_zero_right : ∀ s : ℝ, 1 < s → ∀ y, vel s y = 0 := by
    intro s hs y
    rw [hvel_section s y]
    have hev : (fun u : ℝ => Φ u y) =ᶠ[𝓝 s] fun _ => Φ 1 y := by
      filter_upwards [isOpen_Ioi.mem_nhds hs] with u hu
      exact hstat1 u y (le_of_lt hu)
    rw [hev.fderiv_eq]
    simp
  obtain ⟨K, hK, hKbound⟩ := hbound
  obtain ⟨R₀, hR₀⟩ := Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace ℝ (Fin m)) |>.mp
    hK.isBounded
  set R : ℝ := max R₀ 0 with hRdef
  have hR0 : 0 ≤ R := le_max_right _ _
  have hKsub : K ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) R := fun y hy =>
    Metric.closedBall_subset_closedBall (le_max_left _ _) (hR₀ hy)
  let spaceBump : EuclideanSpace ℝ (Fin m) → ℝ :=
    fun y => Real.smoothTransition ((R + 1)^2 - ‖y‖^2)
  have hsb_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) spaceBump := by
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : EuclideanSpace ℝ (Fin m) => (R + 1)^2 - ‖y‖^2) :=
      contDiff_const.sub (contDiff_norm_sq ℝ)
    exact Real.smoothTransition.contDiff.comp h2
  have hsb_one : ∀ y ∈ K, spaceBump y = 1 := by
    intro y hy
    have hyR : ‖y‖ ≤ R := by
      have h := hKsub hy
      rwa [Metric.mem_closedBall, dist_zero_right] at h
    refine Real.smoothTransition.one_of_one_le ?_
    have h1 : ‖y‖^2 ≤ R^2 := by nlinarith [norm_nonneg y]
    nlinarith [hR0]
  have hsb_zero : ∀ y : EuclideanSpace ℝ (Fin m), R + 1 ≤ ‖y‖ → spaceBump y = 0 := by
    intro y hy
    refine Real.smoothTransition.zero_of_nonpos ?_
    have h1 : (R + 1)^2 ≤ ‖y‖^2 := by nlinarith [norm_nonneg y, hR0]
    linarith
  have hsb_supp : HasCompactSupport spaceBump := by
    refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m))
      (R + 1)) (isClosed_tsupport spaceBump) (closure_minimal ?_ Metric.isClosed_closedBall)
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra h
    exact hy (hsb_zero y (le_of_lt (not_le.mp h)))
  let V : ℝ → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) :=
    fun lam y => arcBump lam • (spaceBump y • ∑ j, ψ j lam y • vel lam (par j lam y))
  have hV_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin m) => V p.1 p.2) := by
    have hb1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × EuclideanSpace ℝ (Fin m) => arcBump p.1) :=
      arcBump_contDiff.comp contDiff_fst
    have hb2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × EuclideanSpace ℝ (Fin m) => spaceBump p.2) :=
      hsb_sm.comp contDiff_snd
    have hsum : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × EuclideanSpace ℝ (Fin m) =>
          ∑ j, ψ j p.1 p.2 • vel p.1 (par j p.1 p.2)) := by
      refine ContDiff.sum (fun j _ => ?_)
      refine contDiff_smul_of_tsupport
        (f := fun p : ℝ × EuclideanSpace ℝ (Fin m) => ψ j p.1 p.2)
        (U := O j ×ˢ B j) (hψsm j) ?_ ((hO j).prod (hB j)) (hψtsupp j)
      have hpair : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : ℝ × EuclideanSpace ℝ (Fin m) => (p.1, par j p.1 p.2)) (O j ×ˢ B j) :=
        ContDiffOn.prodMk (contDiff_fst.contDiffOn) (hsm j)
      exact hvel_sm.contDiffOn.comp hpair (fun p _ => Set.mem_univ _)
    exact hb1.smul (hb2.smul hsum)
  have harcBump_cs : HasCompactSupport arcBump := by
    refine IsCompact.of_isClosed_subset (isCompact_Icc : IsCompact (Set.Icc (-2:ℝ) 3))
      (isClosed_tsupport arcBump) (closure_minimal (fun t ht => ?_) isClosed_Icc)
    rw [Set.mem_Icc]
    exact ⟨by by_contra h; exact ht (arcBump_eq_zero_of_le (le_of_lt (not_le.mp h))),
      by by_contra h; exact ht (arcBump_eq_zero_of_ge (le_of_lt (not_le.mp h)))⟩
  have hV_supp : HasCompactSupport (fun p : ℝ × EuclideanSpace ℝ (Fin m) => V p.1 p.2) := by
    have hsupp : Function.support (fun p : ℝ × EuclideanSpace ℝ (Fin m) => V p.1 p.2) ⊆
        Function.support arcBump ×ˢ Function.support spaceBump := by
      intro p hp
      have h1 : arcBump p.1 ≠ 0 := by
        intro h; exact hp (by simp [V, h])
      have h2 : spaceBump p.2 ≠ 0 := by
        intro h; exact hp (by simp [V, h])
      exact ⟨h1, h2⟩
    refine IsCompact.of_isClosed_subset (harcBump_cs.isCompact.prod hsb_supp.isCompact)
      (isClosed_tsupport (fun p : ℝ × EuclideanSpace ℝ (Fin m) => V p.1 p.2))
      (closure_minimal (fun x hx => ⟨subset_tsupport _ (hsupp hx).1,
        subset_tsupport _ (hsupp hx).2⟩) ((isClosed_tsupport arcBump).prod
          (isClosed_tsupport spaceBump)))
  have hV_trail : ∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1, V lam (Φ lam t) = vel lam t := by
    intro lam hlam t ht
    have h1 : arcBump lam = 1 := arcBump_eq_one ⟨by linarith [hlam.1], by linarith [hlam.2]⟩
    have h2 : spaceBump (Φ lam t) = 1 := hsb_one _ (hKbound lam hlam t)
    have h3 : (∑ j, ψ j lam (Φ lam t) • vel lam (par j lam (Φ lam t))) = vel lam t := by
      refine patchedVelocityOn Φ vel par ψ (fun s hs x hx => hψsum s hs x hx) ?_ lam hlam t ht
      intro i s hs x hx hψ
      obtain ⟨hsO, hxB⟩ := hψsupp i s (Φ s x) hψ
      exact hretr i s x hsO (hsep i s x hsO hx hxB) hxB
    simp only [V]
    rw [h1, h2, h3, one_smul, one_smul]
  have hVd_cs : HasCompactSupport (fun p : ℝ × EuclideanSpace ℝ (Fin m) =>
      fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin m) => V q.1 q.2) p) :=
    hV_supp.fderiv (𝕜 := ℝ)
  obtain ⟨Lv, hLv⟩ := Work.ODE.exists_nnnorm_le_of_hasCompactSupport
    (hV_sm.continuous_fderiv (by norm_num)) hVd_cs
  have hV_lip : LipschitzWith Lv (fun p : ℝ × EuclideanSpace ℝ (Fin m) => V p.1 p.2) :=
    lipschitzWith_of_nnnorm_fderiv_le (hV_sm.differentiable (by norm_num)) hLv
  obtain ⟨Mv, _hMv0, hMv⟩ := Work.ODE.exists_norm_le_of_hasCompactSupport
    (f := fun p : ℝ × EuclideanSpace ℝ (Fin m) => V p.1 p.2) hV_sm.continuous hV_supp
  -- ## the field on the product space
  let X : ℝ × EuclideanSpace ℝ (Fin m) → ℝ × EuclideanSpace ℝ (Fin m) :=
    fun p => ((1:ℝ), V p.1 p.2)
  have hX_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) X := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun _ : ℝ × EuclideanSpace ℝ (Fin m) => (1 : ℝ)) := contDiff_const
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × EuclideanSpace ℝ (Fin m) => V p.1 p.2) := hV_sm
    exact h1.prodMk h2
  have hX_lip : LipschitzWith (max 0 Lv) X := by
    refine LipschitzWith.of_dist_le_mul (fun p q => ?_)
    have h1 : dist (X p).1 (X q).1 = 0 := by simp [X]
    have h2 : dist (X p).2 (X q).2 ≤ (Lv : ℝ) * dist p q := by
      simpa [X] using hV_lip.dist_le_mul p q
    have h2' : dist (X p).2 (X q).2 ≤ (Lv : ℝ) * max (dist p.1 q.1) (dist p.2 q.2) := by
      rw [show max (dist p.1 q.1) (dist p.2 q.2) = dist p q from Prod.dist_eq.symm]
      exact h2
    rw [Prod.dist_eq, Prod.dist_eq, h1, max_eq_right (by positivity)]
    exact le_trans h2' (mul_le_mul_of_nonneg_right
      (by exact_mod_cast le_max_right (0 : NNReal) Lv) (by positivity))
  have hX_bd : ∀ z, ‖X z‖ ≤ max 1 Mv := by
    intro z
    rw [Prod.norm_def]
    refine max_le ?_ ?_
    · simpa [X] using le_max_left (1 : ℝ) Mv
    · simpa [X] using le_trans (hMv z) (le_max_right (1 : ℝ) Mv)
  have hX_db : ∀ z, ‖fderiv ℝ X z‖ ≤ ((max 0 Lv : NNReal) : ℝ) :=
    fun z => norm_fderiv_le_of_lipschitz ℝ hX_lip
  obtain ⟨FL, δ, hδpos, hFL0, hFLsem, hFLint, hFLsmooth⟩ :=
    exists_flow_of_lipschitz X hX_sm hX_lip hX_bd hX_db
  have hY : LipschitzWith 0 (fun _ : ℝ => (1:ℝ)) := LipschitzWith.const 1
  have hFLfst : ∀ s p, (FL s p).1 = p.1 + s := by
    intro s p
    have hcurve1 : IsIntegralCurve (fun u : ℝ => (FL u p).1) (fun _ z => (1:ℝ)) := by
      intro u
      have h2 := ((hFLint p u).hasFDerivAt.fst).hasDerivAt
      simpa [X] using h2
    have hcurve2 : IsIntegralCurve (fun u : ℝ => p.1 + u) (fun _ z => (1:ℝ)) := by
      intro u
      simpa using (hasDerivAt_id u).const_add p.1
    have heq := Work.ODE.eq_of_isIntegralCurve (X := fun _ : ℝ => (1:ℝ)) (L := 0) hY
      hcurve1 hcurve2 (t := 0) (by simp [hFL0])
    have := congrFun heq s
    simpa using this
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδpos
  have hstep : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (FL ((1:ℝ) / ((n:ℝ) + 1))) :=
    hFLsmooth _ (by rw [abs_of_pos (by positivity)]; exact le_of_lt hn)
  have hstepneg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (FL (-((1:ℝ) / ((n:ℝ) + 1)))) :=
    hFLsmooth _ (by rw [abs_neg, abs_of_pos (by positivity)]; exact le_of_lt hn)
  have hiter : ∀ (k : ℕ) (r : ℝ) p, FL ((k:ℝ) * r) p = (FL r)^[k] p := by
    intro k
    induction k with
    | zero => intro r p; simp [hFL0]
    | succ k ih =>
      intro r p
      have h1 : ((k:ℝ) + 1) * r = r + (k:ℝ) * r := by ring
      rw [Nat.cast_succ, h1, hFLsem, ih, Function.iterate_succ_apply']
  have hFL1_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (FL 1) := by
    have hpow : (FL 1) = (FL ((1:ℝ)/((n:ℝ)+1)))^[n+1] := by
      funext p
      have h1 : ((n:ℝ) + 1) * ((1:ℝ)/((n:ℝ)+1)) = 1 := by field_simp
      have h2 : ((n:ℝ) + 1) = (((n+1 : ℕ)) : ℝ) := by push_cast; ring
      calc FL 1 p = FL ((((n+1 : ℕ)) : ℝ) * ((1:ℝ)/((n:ℝ)+1))) p := by rw [← h2, h1]
        _ = (FL ((1:ℝ)/((n:ℝ)+1)))^[n+1] p := hiter (n+1) _ p
    rw [hpow]
    exact Work.Whitney.contDiff_iterate (n+1) hstep
  have hFLneg1_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (FL (-1)) := by
    have hpow : (FL (-1)) = (FL (-((1:ℝ)/((n:ℝ)+1))))^[n+1] := by
      funext p
      have h1 : ((n:ℝ) + 1) * (-((1:ℝ)/((n:ℝ)+1))) = -1 := by field_simp
      have h2 : ((n:ℝ) + 1) = (((n+1 : ℕ)) : ℝ) := by push_cast; ring
      calc FL (-1) p = FL ((((n+1 : ℕ)) : ℝ) * (-((1:ℝ)/((n:ℝ)+1)))) p := by rw [← h2, h1]
        _ = (FL (-((1:ℝ)/((n:ℝ)+1))))^[n+1] p := hiter (n+1) _ p
    rw [hpow]
    exact Work.Whitney.contDiff_iterate (n+1) hstepneg
  let A : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) := fun y => (FL 1 ((0:ℝ), y)).2
  let Ainv : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) := fun y => (FL (-1) ((1:ℝ), y)).2
  have hA_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A := by
    show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => (FL 1 ((0:ℝ), y)).2)
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : EuclideanSpace ℝ (Fin m) => FL 1 ((0:ℝ), y)) :=
      hFL1_sm.comp (contDiff_const.prodMk contDiff_id)
    exact h1.snd
  have hAinv_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ainv := by
    show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => (FL (-1) ((1:ℝ), y)).2)
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : EuclideanSpace ℝ (Fin m) => FL (-1) ((1:ℝ), y)) :=
      hFLneg1_sm.comp (contDiff_const.prodMk contDiff_id)
    exact h1.snd
  have hleft : Function.LeftInverse Ainv A := by
    intro y
    show (FL (-1) ((1:ℝ), (FL 1 ((0:ℝ), y)).2)).2 = y
    have h1 : FL 1 ((0:ℝ), y) = (1, (FL 1 ((0:ℝ), y)).2) := by
      refine Prod.ext ?_ rfl
      rw [hFLfst]; norm_num
    rw [← h1]
    have h2 := hFLsem (-1) 1 ((0:ℝ), y)
    rw [show (-1:ℝ) + 1 = 0 by norm_num, hFL0] at h2
    exact (congrArg Prod.snd h2).symm
  have hright : Function.RightInverse Ainv A := by
    intro y
    show (FL 1 ((0:ℝ), (FL (-1) ((1:ℝ), y)).2)).2 = y
    have h1 : FL (-1) ((1:ℝ), y) = (0, (FL (-1) ((1:ℝ), y)).2) := by
      refine Prod.ext ?_ rfl
      rw [hFLfst]; norm_num
    rw [← h1]
    have h2 := hFLsem 1 (-1) ((1:ℝ), y)
    rw [show (1:ℝ) + -1 = 0 by norm_num, hFL0] at h2
    exact (congrArg Prod.snd h2).symm
  have hV_zero_neg : ∀ u : ℝ, u < 0 → ∀ y, V u y = 0 := by
    intro u hu y
    have hsum0 : (∑ j, ψ j u y • vel u (par j u y)) = 0 := by
      refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [hvel_zero_left u hu (par j u y), smul_zero]
    simp [V, hsum0]
  have hV_zero_pos : ∀ u : ℝ, 1 < u → ∀ y, V u y = 0 := by
    intro u hu y
    have hsum0 : (∑ j, ψ j u y • vel u (par j u y)) = 0 := by
      refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [hvel_zero_right u hu (par j u y), smul_zero]
    simp [V, hsum0]
  have hVeq : ∀ u : ℝ, ∀ t ∈ Set.Icc (0:ℝ) 1, V u (Φ u t) = vel u t := by
    intro u t ht
    by_cases hu : u ∈ Set.Icc (0:ℝ) 1
    · exact hV_trail u hu t ht
    · have hu' : u < 0 ∨ 1 < u := by
        by_contra h
        push_neg at h
        exact hu ⟨h.1, h.2⟩
      rcases hu' with hu' | hu'
      · rw [hV_zero_neg u hu' (Φ u t), hvel_zero_left u hu' t]
      · rw [hV_zero_pos u hu' (Φ u t), hvel_zero_right u hu' t]
  have hconj : ∀ t ∈ Set.Icc (0:ℝ) 1, A (Φ 0 t) = Φ 1 t := by
    intro t ht
    have hcurve : IsIntegralCurve (fun u : ℝ => (u, Φ u t)) (fun _ z => X z) := by
      intro u
      have hderiv : HasDerivAt (fun u : ℝ => Φ u t) (vel u t) u :=
        section_deriv_eq (fun p : ℝ × ℝ => Φ p.1 p.2) ((hΦ.differentiable (by simp)) (u, t))
      have hprod := (hasDerivAt_id u).prodMk hderiv
      simpa [X, hVeq u t ht] using hprod
    have hflowcurve : IsIntegralCurve (fun u : ℝ => FL u ((0:ℝ), Φ 0 t)) (fun _ z => X z) :=
      hFLint ((0:ℝ), Φ 0 t)
    have hagree : (fun u : ℝ => (u, Φ u t)) 0 = (fun u : ℝ => FL u ((0:ℝ), Φ 0 t)) 0 := by
      simp [hFL0]
    have heq := Work.ODE.eq_of_isIntegralCurve hX_lip hcurve hflowcurve hagree
    have hval := congrFun heq 1
    show (FL 1 ((0:ℝ), Φ 0 t)).2 = Φ 1 t
    rw [← hval]
  exact ⟨A, Ainv, hA_sm, hAinv_sm, hleft, hright, hconj⟩

end Work.Whitney.CutPush
namespace Work.Whitney.CutPush

set_option maxHeartbeats 1000000 in
/-- **Arc unknotting.** -/
theorem arc_unknotting {m : ℕ} (hm : 4 ≤ m) (c : ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c)
    (hinj : Set.InjOn c (Set.Icc (0 : ℝ) 1))
    (hreg : ∀ t ∈ Set.Icc (0 : ℝ) 1, fderiv ℝ c t 1 ≠ 0) :
    ∃ (A Ainv : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ainv ∧
      Function.LeftInverse Ainv A ∧ Function.RightInverse Ainv A ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, A (c t) = c 0 + t • (c 1 - c 0)) := by
  classical
  obtain ⟨v, hv0, hcf, htan⟩ := arc_direction_generic hm c hc hinj hreg
  set u : EuclideanSpace ℝ (Fin m) := c 1 - c 0 with hudef
  have hu0 : u ≠ 0 := by
    intro h
    have h01 : c 1 = c 0 := by rw [hudef, sub_eq_zero] at h; exact h
    exact absurd (hinj (by norm_num) (by norm_num) h01.symm) (by norm_num)
  -- `v` is not a multiple of `u`, since `u` is the chord from `0` to `1`
  have hnu : ∀ μ : ℝ, v ≠ μ • u := by
    intro μ hvu
    rcases eq_or_ne μ 0 with hμ | hμ
    · rw [hμ, zero_smul] at hvu
      exact hv0 hvu
    · have hcoef : μ ≠ 0 := hμ
      have hu : u = μ⁻¹ • v := by rw [hvu, smul_smul, inv_mul_cancel₀ hcoef, one_smul]
      refine hcf 1 (by norm_num) 0 (by norm_num) (by norm_num) μ⁻¹ ?_
      rw [← hudef]
      exact hu
  -- the straight arc in direction `v` has chord-free direction `u`
  have hcf' : ChordFree (fun t : ℝ => c 0 + t • v) u := by
    intro t ht t' ht' hne α hcon
    have h1 : (t - t') • v = α • u := by
      have h2 : (c 0 + t • v) - (c 0 + t' • v) = (t - t') • v := by module
      rw [← h2, hcon]
    have htne : t - t' ≠ 0 := sub_ne_zero.mpr hne
    have hα : α ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at h1
      exact htne ((smul_eq_zero.mp h1).resolve_right hv0)
    have hvt : v = ((t - t')⁻¹ * α) • u := by
      calc v = ((t - t')⁻¹ * (t - t')) • v := by rw [inv_mul_cancel₀ htne, one_smul]
        _ = ((t - t')⁻¹) • ((t - t') • v) := by rw [smul_smul]
        _ = ((t - t')⁻¹) • (α • u) := by rw [h1]
        _ = ((t - t')⁻¹ * α) • u := by rw [smul_smul]
    have hcoef : ((t - t')⁻¹ * α) ≠ 0 := mul_ne_zero (inv_ne_zero htne) hα
    have hu' : u = ((t - t')⁻¹ * α)⁻¹ • v := by
      rw [hvt, smul_smul, inv_mul_cancel₀ hcoef, one_smul]
    refine hcf 1 (by norm_num) 0 (by norm_num) (by norm_num) (((t - t')⁻¹ * α)⁻¹) ?_
    rw [← hudef]
    exact hu'
  -- the derivative of the straight arc is constantly `v`
  have hderiv_v : ∀ s : ℝ, fderiv ℝ (fun t : ℝ => c 0 + t • v) s 1 = v := by
    intro s
    have hd : HasDerivAt (fun t : ℝ => c 0 + t • v) v s := by
      simpa using ((hasDerivAt_id s).smul_const v).const_add (c 0)
    rw [hd.hasFDerivAt.fderiv]
    simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul]
  -- the localised straightening family of `c` in direction `v`
  obtain ⟨A₁, A₁inv, hA₁, hA₁inv, hl₁, hr₁, hconj₁⟩ :=
    arc_ambient (localisedArc c v 1) (localisedArc_contDiff hc v 1)
      (fun lam => localisedArc_injOn hv0 hcf 1 one_ne_zero lam)
      (fun lam t ht => localisedArc_fderiv_ne_zero (hc.differentiable (by simp)) hv0
        one_ne_zero hreg htan lam t ht)
      (fun lam t h => localisedArc_hstat0 c v 1 lam h t)
      (fun lam t h => localisedArc_hstat1 c v 1 lam h t)
      (localisedArc_bound hc.continuous v 1)
  have hA₁c : ∀ t ∈ Set.Icc (0:ℝ) 1, A₁ (c t) = c 0 + t • v := by
    intro t ht
    have h := hconj₁ t ht
    have h0 : localisedArc c v 1 0 t = c t := by
      rw [localisedArc_eq_on c v 1 0 ht]
      have hσ : (1:ℝ) - Real.smoothTransition (0:ℝ) = 1 := by
        rw [Real.smoothTransition.zero_of_nonpos le_rfl]; ring
      rw [hσ, straighteningFamily_one]
    rw [h0, localisedArc_one_eq_segment c v 1 t ht, one_mul] at h
    exact h
  -- the localised straightening family of the straight arc in direction `v`, to direction `u`
  have hdif : Differentiable ℝ (fun t : ℝ => c 0 + t • v) := by
    have : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => c 0 + t • v) := by fun_prop
    exact this.differentiable (by simp)
  have hcont' : Continuous (fun t : ℝ => c 0 + t • v) := hdif.continuous
  obtain ⟨A₂, A₂inv, hA₂, hA₂inv, hl₂, hr₂, hconj₂⟩ :=
    arc_ambient (localisedArc (fun t : ℝ => c 0 + t • v) u 1)
      (localisedArc_contDiff (by fun_prop) u 1)
      (fun lam => localisedArc_injOn hu0 hcf' 1 one_ne_zero lam)
      (fun lam t ht => localisedArc_fderiv_ne_zero hdif hu0 one_ne_zero
        (fun s hs h => hv0 (by rw [hderiv_v s] at h; exact h))
        (fun s hs μ h => hnu μ (by rw [hderiv_v s] at h; exact h)) lam t ht)
      (fun lam t h => localisedArc_hstat0 (fun t : ℝ => c 0 + t • v) u 1 lam h t)
      (fun lam t h => localisedArc_hstat1 (fun t : ℝ => c 0 + t • v) u 1 lam h t)
      (localisedArc_bound hcont' u 1)
  have hA₂c : ∀ t ∈ Set.Icc (0:ℝ) 1, A₂ (c 0 + t • v) = c 0 + t • u := by
    intro t ht
    have h := hconj₂ t ht
    have h0 : localisedArc (fun s : ℝ => c 0 + s • v) u 1 0 t = c 0 + t • v := by
      rw [localisedArc_eq_on (fun s : ℝ => c 0 + s • v) u 1 0 ht]
      have hσ : (1:ℝ) - Real.smoothTransition (0:ℝ) = 1 := by
        rw [Real.smoothTransition.zero_of_nonpos le_rfl]; ring
      rw [hσ, straighteningFamily_one]
    rw [h0, localisedArc_one_eq_segment (fun s : ℝ => c 0 + s • v) u 1 t ht, one_mul] at h
    simpa using h
  refine ⟨A₂ ∘ A₁, A₁inv ∘ A₂inv, hA₂.comp hA₁, hA₁inv.comp hA₂inv, ?_, ?_, ?_⟩
  · intro y
    show A₁inv (A₂inv (A₂ (A₁ y))) = y
    rw [hl₂ (A₁ y)]
    exact hl₁ y
  · intro y
    show A₂ (A₁ (A₁inv (A₂inv y))) = y
    rw [hr₁ (A₂inv y)]
    exact hr₂ y
  · intro t ht
    show A₂ (A₁ (c t)) = c 0 + t • (c 1 - c 0)
    rw [hA₁c t ht, hA₂c t ht, hudef]

end Work.Whitney.CutPush
