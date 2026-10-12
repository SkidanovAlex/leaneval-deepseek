import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseKinLoc.Kinetic

/-!
# `Work.BoseKinLoc.Kinetic.dSpace_fibre_eq` — the Dirichlet word of a slot fibre

The full-space Dirichlet word of the slot-`i` fibre of an `(n+1)`-body state `Φ`,

  `r ↦ dSpace (fun z => Φ (kcInsN n i (z, r)))`,

is integrable over the remaining `n` particles, and its integral is the kinetic energy of `Φ` in
the slot-`i` coordinate directions:

  `∫ x, ∑_k (∂_{i,k}Φ x)²  =  ∫ r, dSpace (fun z => Φ (kcInsN n i (z, r)))`.

This is the fibre form of FS `lem:LocKinEn` at one body: the insertion `kcInsN n i` splits
`X (n+1) ≃ ℝ³ × X n` into the `i`-th particle and the rest, and the chain rule
(`Submission.BoseGases.fiber_fderiv_kcDir`) identifies the derivative of the fibre along the
coordinate `kcStdBasis k` with the derivative of `Φ` along `kcDir (n+1) i k`.

The proof is Fubini: `kcInsN n i` is measure preserving (`Submission.BoseGases.kc_mp_insN`), and
the peeled integrand `(z,r) ↦ (∂_{i,k}Φ (kcInsN n i (z,r)))²` is integrable on the product (it is
continuous with compact support, because `Φ ∈ C_c^∞`).
-/

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators ENNReal

set_option autoImplicit false

/-- **The insertion `kcInsN n i` does not decrease the norm of its arguments.**  In the product
(sup) norm on `X (n+1) = Fin (n+1) → ℝ³`, both the inserted point `z` and every coordinate `r j` of
the remaining configuration are coordinates of `kcInsN n i (z,r)`, hence bounded by its norm.  This
is the elementary geometric input that turns membership of `kcInsN n i (z,r)` in a ball into
membership of `(z,r)` in a product of balls. -/
lemma insN_norm_le {n : ℕ} (i : Fin (n + 1)) (z : ℝ³) (r : Submission.BoseGases.X n) :
    ‖z‖ ≤ ‖Submission.BoseGases.kcInsN n i (z, r)‖ ∧
      ∀ j : Fin n, ‖r j‖ ≤ ‖Submission.BoseGases.kcInsN n i (z, r)‖ := by
  constructor
  · calc ‖z‖ = ‖(Submission.BoseGases.kcInsN n i (z, r)) i‖ := by
          rw [Submission.BoseGases.kc_insN_apply_same]
      _ ≤ _ := norm_le_pi_norm _ i
  · intro j
    calc ‖r j‖ = ‖(Submission.BoseGases.kcInsN n i (z, r)) (i.succAbove j)‖ := by
          rw [Submission.BoseGases.kc_insN_apply_succ]
      _ ≤ _ := norm_le_pi_norm _ _

/-- The square of a directional derivative of a smooth compactly supported function is
integrable (continuity of `fderiv` plus vanishing off the compact support). -/
lemma integrable_fderiv_apply_sq {N : ℕ} {f : Submission.BoseGases.X N → ℝ}
    (hf : ContDiff ℝ (⊤ : ENat) f) (hcs : HasCompactSupport f) (v : Submission.BoseGases.X N) :
    Integrable (fun x : Submission.BoseGases.X N => (fderiv ℝ f x v) ^ 2) := by
  have h1 : HasCompactSupport (fun x : Submission.BoseGases.X N => fderiv ℝ f x v) :=
    hcs.fderiv_apply ℝ v
  have h2 : HasCompactSupport (fun x : Submission.BoseGases.X N => (fderiv ℝ f x v) ^ 2) :=
    HasCompactSupport.of_support_subset_isCompact h1 (fun x hx => by
      simp only [Function.mem_support] at hx
      exact subset_tsupport _ (fun h0 => hx (by simp [h0])))
  exact Continuous.integrable_of_hasCompactSupport
    (((Submission.BoseGases.firstDir_contDiff hf v).continuous).pow 2) h2

theorem dSpace_fibre_eq {n : ℕ} {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (hcs : HasCompactSupport Φ) (i : Fin (n + 1)) :
    MeasureTheory.Integrable
        (fun r : Submission.BoseGases.X n => Work.BSKinetic.dSpace
          (fun z : EuclideanSpace ℝ (Fin 3) => Φ (Submission.BoseGases.kcInsN n i (z, r))))
      ∧ (∫ x : Submission.BoseGases.X (n + 1), ∑ k : Fin 3,
            (fderiv ℝ Φ x (Submission.BoseGases.kcDir (n + 1) i k)) ^ 2)
          = ∫ r : Submission.BoseGases.X n,
              Work.BSKinetic.dSpace
                (fun z : EuclideanSpace ℝ (Fin 3) => Φ (Submission.BoseGases.kcInsN n i (z, r))) := by
  -- integrability of each coordinate square on `X (n+1)`
  have hIntX : ∀ k : Fin 3, Integrable (fun x : Submission.BoseGases.X (n + 1) =>
      (fderiv ℝ Φ x (Submission.BoseGases.kcDir (n + 1) i k)) ^ 2) :=
    fun k => integrable_fderiv_apply_sq hΦ hcs (Submission.BoseGases.kcDir (n + 1) i k)
  -- integrability of each peeled coordinate square on the product `ℝ³ × X n`
  have hIntP : ∀ k : Fin 3, Integrable (fun p : ℝ³ × Submission.BoseGases.X n =>
      (fderiv ℝ Φ (Submission.BoseGases.kcInsN n i p)
        (Submission.BoseGases.kcDir (n + 1) i k)) ^ 2)
      ((volume : Measure ℝ³).prod (volume : Measure (Submission.BoseGases.X n))) := by
    intro k
    -- a bound `R` for the (compact) support of `fderiv ℝ Φ`
    obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_closedBall
      (0 : Submission.BoseGases.X (n + 1))).1 (hcs.fderiv ℝ).isBounded
    set R : ℝ := max R₀ 0 with hRdef
    have hR0 : 0 ≤ R := le_max_right _ _
    have hR : ∀ x ∈ tsupport (fderiv ℝ Φ), ‖x‖ ≤ R := by
      intro x hx
      have h1 : ‖x‖ ≤ R₀ := by
        have h2 := hR₀ hx
        rwa [Metric.mem_closedBall, dist_zero_right] at h2
      exact h1.trans (le_max_left _ _)
    have hcont : Continuous (fun p : ℝ³ × Submission.BoseGases.X n =>
        (fderiv ℝ Φ (Submission.BoseGases.kcInsN n i p)
          (Submission.BoseGases.kcDir (n + 1) i k)) ^ 2) :=
      (((hΦ.continuous_fderiv (by simp)).comp (Submission.BoseGases.kcInsN_cont i)).clm_apply
        continuous_const).pow 2
    refine Continuous.integrable_of_hasCompactSupport hcont ?_
    refine HasCompactSupport.of_support_subset_isCompact
      ((isCompact_closedBall (0 : ℝ³) R).prod
        (isCompact_closedBall (0 : Submission.BoseGases.X n) R)) ?_
    intro p hp
    simp only [Function.mem_support] at hp
    refine ⟨?_, ?_⟩
    · by_contra hcon
      rw [Metric.mem_closedBall, dist_zero_right, not_le] at hcon
      have h2 : Submission.BoseGases.kcInsN n i p ∉ tsupport (fderiv ℝ Φ) := by
        intro hmem
        have h3 := hR _ hmem
        have h4 : ‖p.1‖ ≤ ‖Submission.BoseGases.kcInsN n i p‖ := (insN_norm_le i p.1 p.2).1
        linarith
      exact hp (by rw [image_eq_zero_of_notMem_tsupport h2]; simp)
    · rw [Metric.mem_closedBall, dist_zero_right]
      rw [pi_norm_le_iff_of_nonneg hR0]
      intro j
      by_contra hcon
      rw [not_le] at hcon
      have h2 : Submission.BoseGases.kcInsN n i p ∉ tsupport (fderiv ℝ Φ) := by
        intro hmem
        have h3 := hR _ hmem
        have h4 : ‖p.2 j‖ ≤ ‖Submission.BoseGases.kcInsN n i p‖ := (insN_norm_le i p.1 p.2).2 j
        linarith
      exact hp (by rw [image_eq_zero_of_notMem_tsupport h2]; simp)
  -- `r`-integrability of the inner integrals, by Fubini
  have hIntR : ∀ k : Fin 3, Integrable (fun r : Submission.BoseGases.X n =>
      ∫ z : ℝ³, (fderiv ℝ Φ (Submission.BoseGases.kcInsN n i (z, r))
        (Submission.BoseGases.kcDir (n + 1) i k)) ^ 2) :=
    fun k => (hIntP k).integral_prod_right
  -- the peel identity for one coordinate direction
  have hpeel : ∀ k : Fin 3,
      (∫ x : Submission.BoseGases.X (n + 1),
          (fderiv ℝ Φ x (Submission.BoseGases.kcDir (n + 1) i k)) ^ 2)
        = ∫ r : Submission.BoseGases.X n, ∫ z : ℝ³,
            (fderiv ℝ Φ (Submission.BoseGases.kcInsN n i (z, r))
              (Submission.BoseGases.kcDir (n + 1) i k)) ^ 2 := by
    intro k
    rw [← (Submission.BoseGases.kc_mp_insN n i).integral_comp'
      (fun x : Submission.BoseGases.X (n + 1) =>
        (fderiv ℝ Φ x (Submission.BoseGases.kcDir (n + 1) i k)) ^ 2)]
    exact integral_prod_symm _ (hIntP k)
  -- identification of the inner integral with the one-body Dirichlet word of the fibre
  have hpoint : ∀ r : Submission.BoseGases.X n,
      (∑ k : Fin 3, ∫ z : ℝ³, (fderiv ℝ Φ (Submission.BoseGases.kcInsN n i (z, r))
          (Submission.BoseGases.kcDir (n + 1) i k)) ^ 2)
        = Work.BSKinetic.dSpace
            (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, r))) := by
    intro r
    unfold Work.BSKinetic.dSpace
    refine Finset.sum_congr rfl (fun k _ => ?_)
    apply integral_congr_ae
    filter_upwards with z
    rw [Submission.BoseGases.fiber_fderiv_kcDir i hΦ r z k]
  constructor
  · have hsum : Integrable (fun r : Submission.BoseGases.X n => ∑ k : Fin 3, ∫ z : ℝ³,
        (fderiv ℝ Φ (Submission.BoseGases.kcInsN n i (z, r))
          (Submission.BoseGases.kcDir (n + 1) i k)) ^ 2) :=
      integrable_finsetSum _ (fun k _ => hIntR k)
    exact hsum.congr (Filter.Eventually.of_forall (fun r => hpoint r))
  · calc (∫ x : Submission.BoseGases.X (n + 1), ∑ k : Fin 3,
            (fderiv ℝ Φ x (Submission.BoseGases.kcDir (n + 1) i k)) ^ 2)
        = ∑ k : Fin 3, ∫ x : Submission.BoseGases.X (n + 1),
            (fderiv ℝ Φ x (Submission.BoseGases.kcDir (n + 1) i k)) ^ 2 :=
          integral_finsetSum Finset.univ (fun k _ => hIntX k)
      _ = ∑ k : Fin 3, ∫ r : Submission.BoseGases.X n, ∫ z : ℝ³,
            (fderiv ℝ Φ (Submission.BoseGases.kcInsN n i (z, r))
              (Submission.BoseGases.kcDir (n + 1) i k)) ^ 2 :=
          Finset.sum_congr rfl (fun k _ => hpeel k)
      _ = ∫ r : Submission.BoseGases.X n, ∑ k : Fin 3, ∫ z : ℝ³,
            (fderiv ℝ Φ (Submission.BoseGases.kcInsN n i (z, r))
              (Submission.BoseGases.kcDir (n + 1) i k)) ^ 2 :=
          (integral_finsetSum Finset.univ (fun k _ => hIntR k)).symm
      _ = ∫ r : Submission.BoseGases.X n,
            Work.BSKinetic.dSpace
              (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN n i (z, r))) :=
          integral_congr_ae (Filter.Eventually.of_forall (fun r => hpoint r))

end Work.BoseKinLoc.Kinetic
