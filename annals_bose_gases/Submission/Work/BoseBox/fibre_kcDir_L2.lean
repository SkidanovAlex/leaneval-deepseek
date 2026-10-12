import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Submission.Work.BoseKinLoc.Kinetic.integral_fibre_sq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBox.fibre_kcDir_L2`

Fibre decomposition of the `L²`-norm of the **directional derivative** of a smooth
state supported in the box:

    ∫ r, ∫ z, (D_{kcDir (n+1) i k} Ψ) (kcInsN n i (z, r))²  =  ∫ x, (D_{kcDir (n+1) i k} Ψ) x ²,

i.e. the `L²` mass of the derivative in the direction `kcDir (n+1) i k` is the integral
over the base of the fibre-wise masses, where the fibre coordinate `(i, k)` is integrated
out by the measure-preserving insertion `kcInsN n i` (`piFinSuccAbove`).

The proof is a direct instantiation of the already available fibration identity
`Work.BoseKinLoc.Kinetic.integral_fibre_sq` for `Φ := fun x => fderiv ℝ Ψ x (kcDir (n+1) i k)`,
so all that is needed are the two analytic inputs for `Φ`:

* smoothness (`fun_prop`), and
* compact support: `tsupport (fderiv Ψ · v) ⊆ tsupport Ψ ⊆ box (n+1) L`, together with the
  fact that `box N L` is compact for **every** `L : ℝ` (no positivity hypothesis is available
  in the statement here; for `L ≤ 0` the box is empty or a single point).

The last two facts are proved as helpers below.
-/

open MeasureTheory Filter

namespace Work.BoseBox

/-- The box `box N L = {x | ∀ i k, x i k ∈ Icc 0 L}` is compact for *every* `L : ℝ`
(no positivity of `L` is needed: for `L ≤ 0` it is empty or a single point). -/
lemma box_isCompact_all (N : ℕ) (L : ℝ) : IsCompact (_root_.BoseGases.box N L) := by
  rcases le_or_gt L 0 with hL | hL
  · have hsub : _root_.BoseGases.box N L ⊆ ({(0 : Submission.BoseGases.X N)} : Set _) := by
      intro x hx
      simp only [Set.mem_singleton_iff]
      funext i
      ext k
      have h1 := hx i k
      simp only [Set.mem_Icc] at h1
      simp only [Pi.zero_apply, PiLp.zero_apply]
      exact le_antisymm (le_trans h1.2 hL) h1.1
    rcases Set.eq_empty_or_nonempty (_root_.BoseGases.box N L) with hemp | ⟨x, hx⟩
    · rw [hemp]; exact isCompact_empty
    · have h0 : (0 : Submission.BoseGases.X N) ∈ _root_.BoseGases.box N L := by
        rw [← hsub hx]; exact hx
      have huniq : _root_.BoseGases.box N L = {(0 : Submission.BoseGases.X N)} := by
        rw [Set.eq_singleton_iff_unique_mem]
        exact ⟨h0, fun y hy => hsub hy⟩
      rw [huniq]; exact isCompact_singleton
  · exact Submission.BoseGases.box_compact hL

/-- The support of a directional derivative is contained in the support of the function:
outside `tsupport f` the function vanishes near the point, hence so does its derivative. -/
lemma tsupport_fderiv_apply_subset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (v : E) :
    tsupport (fun x => fderiv ℝ f x v) ⊆ tsupport f := by
  refine closure_minimal ?_ (isClosed_tsupport _)
  intro x hx
  by_contra hx'
  rw [Function.mem_support] at hx
  exact hx (by
    have hev : f =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx'
    rw [hev.fderiv_eq]
    simp)

theorem fibre_kcDir_L2 {n : ℕ} {L : ℝ} {Ψ : Submission.BoseGases.X (n + 1) → ℝ}
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hsupp : tsupport Ψ ⊆ _root_.BoseGases.box (n + 1) L)
    (i : Fin (n + 1)) (k : Fin 3) :
    MeasureTheory.Integrable (fun r : Submission.BoseGases.X n =>
        ∫ z : EuclideanSpace ℝ (Fin 3),
          (fderiv ℝ Ψ (Submission.BoseGases.kcInsN n i (z, r))
            (Submission.BoseGases.kcDir (n + 1) i k)) ^ 2) ∧
      (∫ r : Submission.BoseGases.X n, ∫ z : EuclideanSpace ℝ (Fin 3),
          (fderiv ℝ Ψ (Submission.BoseGases.kcInsN n i (z, r))
            (Submission.BoseGases.kcDir (n + 1) i k)) ^ 2)
        = ∫ x : Submission.BoseGases.X (n + 1),
            (fderiv ℝ Ψ x (Submission.BoseGases.kcDir (n + 1) i k)) ^ 2 := by
  have hΦ : ContDiff ℝ (⊤ : ℕ∞) (fun x : Submission.BoseGases.X (n + 1) =>
      fderiv ℝ Ψ x (Submission.BoseGases.kcDir (n + 1) i k)) := by fun_prop
  have hcs : HasCompactSupport (fun x : Submission.BoseGases.X (n + 1) =>
      fderiv ℝ Ψ x (Submission.BoseGases.kcDir (n + 1) i k)) :=
    IsCompact.of_isClosed_subset (box_isCompact_all (n + 1) L) (isClosed_tsupport _)
      ((tsupport_fderiv_apply_subset (Submission.BoseGases.kcDir (n + 1) i k)).trans hsupp)
  exact Work.BoseKinLoc.Kinetic.integral_fibre_sq hΦ hcs i

end Work.BoseBox
