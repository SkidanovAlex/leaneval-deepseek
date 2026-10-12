import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Submission.Work.BoseBox.CNodeDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBox.chiBigUnifData` — uniform support/derivative data for the big-box window

This module collects the *uniform* (in `u`) geometric and analytic data of FS's
box window `χ_u(x) = χ(x/ℓ − u) = chiBig ℓ u x` on the localisation region
`coverU ℓ L`: there is a radius `R > 0` outside which every `χ_u` (`u ∈ coverU ℓ L`)
vanishes, and a nonnegative sequence `G` bounding the norms of the complexified
iterated Fréchet derivatives of `χ_u` up to order `3`, uniformly in
`u ∈ coverU ℓ L` and in the base point.

Both statements are read off from the *single* function `chiScale ℓ` (the
`ℓ`-scaling of the corpus bump `χ`):

* `χ_u = chiScale ℓ (· − ℓ•u)` is a translate of `chiScale ℓ`, so its support sits
  in `B(ℓ•u, supp chiScale)`; the localisation region `coverU ℓ L` is the cube
  `[−1/2, L/ℓ+1/2]³` in coordinates (`|u k| ≤ L/ℓ + 1/2`), whence the uniform
  radius;
* `iteratedFDeriv ℝ k (fun z => (χ_u z : ℂ)) z = iteratedFDeriv ℝ k
  (fun y => (chiScale ℓ y : ℂ)) (z − ℓ•u)` by `iteratedFDeriv_comp_sub`, so the
  bound for `chiScale ℓ` (proved by compact support + continuity in
  `Work.SmallBoxTBWord.chi_support_and_deriv_bound`) transfers verbatim.

The two halves are independent: the radius uses only the support and the
coordinate form of `coverU`, the derivative bound uses only the translation
invariance of the iterated derivative.
-/

namespace Work.BoseBox

open MeasureTheory

/-- **Uniform bound on the localisation parameters.**  Every `u` whose sliding box
`Λ(u) = ℓu + [−ℓ/2,ℓ/2]³` meets the corner box `[0,L]³` has all coordinates in
`[−1/2, L/ℓ+1/2]`, hence `‖u‖ ≤ 3(L/ℓ + 1/2)`. -/
private lemma coverU_norm_le {ℓ L : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) :
    ∀ u ∈ Work.BoseBox.coverU ℓ L, ‖u‖ ≤ 3 * (L / ℓ + 1 / 2) := by
  intro u hu
  obtain ⟨x, hx, hxu⟩ := hu
  set M : ℝ := L / ℓ + 1 / 2 with hMdef
  have hM : 0 ≤ M := by rw [hMdef]; positivity
  have hk : ∀ k : Fin 3, |u k| ≤ M := by
    intro k
    rw [hMdef]
    have hxk : 0 ≤ x k ∧ x k ≤ L := Set.mem_Icc.mp (hx k)
    have hku : -ℓ / 2 ≤ (x - ℓ • u) k ∧ (x - ℓ • u) k ≤ ℓ / 2 := Set.mem_Icc.mp (hxu k)
    have heq : (x - ℓ • u) k = x k - ℓ * u k := by simp
    rw [abs_le]
    constructor
    · have h1 : ℓ * (-(L / ℓ + 1 / 2)) ≤ ℓ * u k := by
        have hMeq : ℓ * (L / ℓ + 1 / 2) = L + ℓ / 2 := by field_simp
        linarith [hku.2, hxk.1, heq, hMeq]
      exact le_of_mul_le_mul_left h1 hℓ
    · have h1 : ℓ * u k ≤ ℓ * (L / ℓ + 1 / 2) := by
        have hMeq : ℓ * (L / ℓ + 1 / 2) = L + ℓ / 2 := by field_simp
        linarith [hku.1, hxk.2, heq, hMeq]
      exact le_of_mul_le_mul_left h1 hℓ
  have hsq : ‖u‖ ^ 2 ≤ (3 * M) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i : Fin 3, ‖u.ofLp i‖ ^ 2 ≤ ∑ i : Fin 3, M ^ 2 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          have hi : |u.ofLp i| ≤ M := by
            have h1 : u i = u.ofLp i := rfl
            rw [← h1]; exact hk i
          calc ‖u.ofLp i‖ ^ 2 = |u.ofLp i| ^ 2 := by rw [Real.norm_eq_abs]
            _ ≤ M ^ 2 := sq_le_sq.mpr (by simpa [abs_of_nonneg hM] using hi)
      _ = 3 * M ^ 2 := by simp [Finset.sum_const, Finset.card_univ]
      _ ≤ (3 * M) ^ 2 := by nlinarith [hM]
  have h3M : (0 : ℝ) ≤ 3 * M := by positivity
  nlinarith [hsq, h3M, norm_nonneg u]

/-- **Uniform support and derivative data for the big-box window family.**

There is `R > 0` such that `chiBig ℓ u ·` vanishes outside `B(0,R)` for every
`u ∈ coverU ℓ L`, and a nonnegative `G` bounding `‖iteratedFDeriv ℝ k
(chiBig ℓ u) z‖` for `k ≤ 3`, uniformly over `u ∈ coverU ℓ L` and `z`. -/
theorem chiBigUnifData {ℓ L : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) :
    ∃ (R : ℝ) (G : ℕ → ℝ), 0 < R ∧ (∀ k : ℕ, 0 ≤ G k) ∧
      (∀ u ∈ Work.BoseBox.coverU ℓ L, ∀ z : EuclideanSpace ℝ (Fin 3),
        Work.BoseBox.chiBig ℓ u z ≠ 0 → ‖z‖ ≤ R) ∧
      (∀ u ∈ Work.BoseBox.coverU ℓ L, ∀ k : ℕ, k ≤ 3 → ∀ z : EuclideanSpace ℝ (Fin 3),
        ‖iteratedFDeriv ℝ k (fun z : EuclideanSpace ℝ (Fin 3) => (Work.BoseBox.chiBig ℓ u z : ℂ)) z‖
          ≤ G k) := by
  -- `chiScale ℓ` is `C^∞` with compact support, so it carries uniform support and
  -- derivative bounds (compactness of the support, continuity of the derivatives).
  have hne : ℓ ≠ 0 := ne_of_gt hℓ
  have hcs : HasCompactSupport (Submission.BoseGases.chiScale ℓ) :=
    Submission.BoseGases.chi_hasCompactSupport.comp_smul (inv_ne_zero hne)
  have hcd : ContDiff ℝ (⊤ : ENat) (Submission.BoseGases.chiScale ℓ) := by
    have h : ContDiff ℝ (⊤ : ENat)
        (fun x : EuclideanSpace ℝ (Fin 3) => (ℓ⁻¹ : ℝ) • x) := by
      simpa using (contDiff_id (𝕜 := ℝ) (n := (⊤ : ENat))).const_smul (ℓ⁻¹)
    exact Submission.BoseGases.chi_contDiff.comp h
  obtain ⟨R0, hR0, hsupp, G, hG0, hGb⟩ :=
    Work.SmallBoxTBWord.chi_support_and_deriv_bound hcd hcs
  refine ⟨R0 + (3 * L + 3 * ℓ / 2), G, by linarith, hG0, ?_, ?_⟩
  · -- support: `chiBig ℓ u ·` is `chiScale ℓ (· − ℓ•u)`, and `‖ℓ•u‖ ≤ 3L + 3ℓ/2`.
    intro u hu z hz
    have hmem : z - ℓ • u ∈ tsupport (Submission.BoseGases.chiScale ℓ) := by
      by_contra h
      have hz0 : Submission.BoseGases.chiScale ℓ (z - ℓ • u) = 0 :=
        image_eq_zero_of_notMem_tsupport h
      exact hz (by simpa [Work.BoseBox.chiBig] using hz0)
    have hb : ‖z - ℓ • u‖ ≤ R0 := by
      have h' := hsupp hmem
      rwa [Metric.mem_closedBall, dist_zero_right] at h'
    have hu' : ‖u‖ ≤ 3 * (L / ℓ + 1 / 2) := coverU_norm_le hℓ hL u hu
    have h1 : ‖z‖ ≤ ‖z - ℓ • u‖ + ‖ℓ • u‖ := by
      have := norm_add_le (z - ℓ • u) (ℓ • u)
      simpa using this
    have h2 : ‖ℓ • u‖ = ℓ * ‖u‖ := by
      rw [norm_smul, Real.norm_of_nonneg hℓ.le]
    rw [h2] at h1
    have h3 : ℓ * ‖u‖ ≤ ℓ * (3 * (L / ℓ + 1 / 2)) :=
      mul_le_mul_of_nonneg_left hu' hℓ.le
    have h4 : ℓ * (3 * (L / ℓ + 1 / 2)) = 3 * L + 3 * ℓ / 2 := by field_simp
    linarith [h1, h3, hb, h4]
  · -- derivative bound: translation invariance of the iterated derivative.
    intro u hu k hk z
    have hcomp := iteratedFDeriv_comp_sub (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 3))
      (f := fun y : EuclideanSpace ℝ (Fin 3) => (Submission.BoseGases.chiScale ℓ y : ℂ))
      k (ℓ • u) z
    rw [show (fun z : EuclideanSpace ℝ (Fin 3) => (Work.BoseBox.chiBig ℓ u z : ℂ))
        = (fun z => (fun y : EuclideanSpace ℝ (Fin 3) =>
            (Submission.BoseGases.chiScale ℓ y : ℂ)) (z - ℓ • u)) from rfl]
    rw [hcomp]
    exact hGb k hk (z - ℓ • u)

end Work.BoseBox
