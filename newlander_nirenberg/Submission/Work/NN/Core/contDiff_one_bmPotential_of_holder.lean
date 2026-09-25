/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The Bochner–Martinelli potential of compactly supported `C^{0,α}` data is `C¹`

Let `0 < α < 1` and let `F = (F_j)` be a family of functions on `ℂⁿ` whose components are
compactly supported and have finite `C^{0,α}`-norm on `ℂⁿ` (finiteness of the `C^{0,α}`-norm
already forces continuity, since it controls both the supremum and the `α`-Hölder seminorm).
Then the Bochner–Martinelli potential

  `bmPotential F z = Σ_j ∫ ζ, \overline{(ζ_j - z_j)} / ‖ζ - z‖^{2n} · F_j ζ dζ`

is continuously differentiable on `ℂⁿ`.

This is the global (no support-in-a-polydisc hypothesis) form of the first step of the
`C^{1,α}` Schauder estimate for the flat `∂̄`-operator: the compactly supported `C^{0,α}` data
gain exactly one derivative.

The proof is local.  At a point `x` choose the polydisc `U = polydisc x rad` with
`rad j = ‖x‖ + M + 1`, where `M` bounds the support of the data; then `U` contains the support
of every `F_j`, so on `U`

* `F` is differentiable, by `Work.NN.Core.bmPotential_differentiableAt_holder` (the
  `C^{0,α}`-regularity of the potential, proved by mollification);
* `‖fderiv ℝ (bmPotential F) u - fderiv ℝ (bmPotential F) v‖ ≤ C ‖u - v‖^α`, by the
  `C^{1,α}` bound `Work.NN.Core.bmPot_holder_C0a` read off through
  `Work.NN.Core.holderNorm_one_bounds`.

Hence `fderiv ℝ (bmPotential F)` is `α`-Hölder, hence continuous, on the open set `U`, and
`ContDiffOn ℝ 1` follows from `contDiffOn_succ_iff_fderiv_of_isOpen`.  As the polydiscs of this
form cover `ℂⁿ`, the conclusion is global.
-/
import Mathlib
import Submission.Work.NN.Core.bmPotential_differentiableAt_holder
import Submission.Work.NN.Core.bmPot_holder_C0a
import Submission.Work.CR.Flat.Cauchy.bmPotential_iteratedFDeriv

noncomputable section

open scoped NNReal ENNReal Topology ContDiff
open MeasureTheory Set Filter

namespace Work.NN.Core

open Work.CR.Flat
open Work.CR.Flat.Cauchy

/-- A function which is `α`-Hölder (`0 < α`) on a set is continuous on that set. -/
private lemma continuousOn_of_holder_bound {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {α K : ℝ} (hα : 0 < α) (hK : 0 ≤ K)
    {g : X → Y} {s : Set X}
    (hg : ∀ x ∈ s, ∀ y ∈ s, ‖g x - g y‖ ≤ K * ‖x - y‖ ^ α) : ContinuousOn g s := by
  have hH : HolderOnWith (Real.toNNReal K) (Real.toNNReal α) g s := by
    intro x hx y hy
    rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm]
    refine le_trans (ENNReal.ofReal_le_ofReal (hg x hx y hy)) ?_
    rw [ENNReal.ofReal_mul hK, ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hα.le]
    rw [ENNReal.coe_nnreal_eq, Real.coe_toNNReal K hK, Real.coe_toNNReal α hα.le]
  exact hH.continuousOn (by rw [Real.toNNReal_pos]; exact hα)

/-- A function which is differentiable on an open set and whose derivative is continuous there is
`C¹` there; consequently, if on a neighbourhood of every point the function admits an open set on
which both properties hold, it is `C¹` on the whole space. -/
private lemma contDiff_one_of_locally {n : ℕ} {f : (Fin n → ℂ) → ℂ}
    (h : ∀ x, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ x ∈ U ∧
      DifferentiableOn ℝ f U ∧ ContinuousOn (fderiv ℝ f) U) : ContDiff ℝ 1 f := by
  rw [← contDiffOn_univ]
  refine contDiffOn_of_locally_contDiffOn fun x _ => ?_
  obtain ⟨U, hU, hxU, hd, hc⟩ := h x
  refine ⟨U, hU, hxU, ?_⟩
  rw [Set.univ_inter]
  change ContDiffOn ℝ ((0 : ℕ∞ω) + 1) f U
  rw [contDiffOn_succ_iff_fderiv_of_isOpen hU]
  exact ⟨hd, fun h => absurd h (by simp), by rwa [contDiffOn_zero]⟩

theorem contDiff_one_bmPotential_of_holder {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {F : Fin n → (Fin n → ℂ) → ℂ}
    (hF : ∀ j, HasCompactSupport (F j))
    (hFfin : ∀ j, Work.CR.Flat.holderNorm 0 α (F j) Set.univ < ⊤) :
    ContDiff ℝ 1 (Work.CR.Flat.Cauchy.bmPotential F) := by
  classical
  -- ### a norm bound on the compact support of the data
  have hRj : ∀ j, ∃ R : ℝ, 0 ≤ R ∧ ∀ z ∈ tsupport (F j), ‖z‖ ≤ R := by
    intro j
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Fin n → ℂ)).mp
      ((hF j).isCompact.isBounded)
    refine ⟨max r 0, le_max_right _ _, fun z hz => ?_⟩
    have h1 : z ∈ Metric.closedBall (0 : Fin n → ℂ) r := hr hz
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h1
    exact h1.trans (le_max_left _ _)
  choose R hR0 hR using hRj
  set M : ℝ := ∑ j, R j with hMdef
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun j _ => hR0 j
  have hM : ∀ j z, M < ‖z‖ → F j z = 0 := by
    intro j z hz
    by_contra h
    have h1 : z ∈ tsupport (F j) := subset_tsupport (F j) (Function.mem_support.mpr h)
    have h2 : ‖z‖ ≤ R j := hR j z h1
    have h3 : R j ≤ M := by
      rw [hMdef]
      exact Finset.single_le_sum (fun i _ => hR0 i) (Finset.mem_univ j)
    linarith
  have hFne : ∀ j, Work.CR.Flat.holderNorm 0 α (F j) Set.univ ≠ ⊤ := fun j => (hFfin j).ne
  -- ### the local argument at an arbitrary point
  refine contDiff_one_of_locally fun x => ?_
  set rad : Fin n → ℝ := fun _ => ‖x‖ + M + 1 with hrad
  set rr : Fin n → ℝ := fun j => 2 * rad j with hrr
  have hradpos : ∀ j, 0 < rad j := by
    intro j
    have h1 : rad j = ‖x‖ + M + 1 := by simp [hrad]
    rw [h1]; linarith [norm_nonneg x]
  have hrpos : ∀ j, 0 < rr j := by
    intro j
    have h1 : rr j = 2 * rad j := by simp [hrr]
    rw [h1]; linarith [hradpos j]
  have hhalf : ∀ j, rr j / 2 = rad j := by
    intro j
    have h1 : rr j = 2 * rad j := by simp [hrr]
    rw [h1]; ring
  have hpd : polydisc x (fun j => rr j / 2) = polydisc x rad := by
    congr 1
    funext j
    exact hhalf j
  -- the data vanish off the half-size polydisc
  have hgsub : ∀ j z, (∃ i, rad i ≤ ‖z i - x i‖) → F j z = 0 := by
    intro j z hz
    refine hM j z ?_
    obtain ⟨i, hi⟩ := hz
    have h1 : rad i = ‖x‖ + M + 1 := by simp [hrad]
    have h2 : ‖z i - x i‖ ≤ ‖z - x‖ := norm_le_pi_norm (z - x) i
    have h3 : ‖z - x‖ ≤ ‖z‖ + ‖x‖ := norm_sub_le z x
    linarith
  have hgsup : ∀ j z, (∃ i, rr i / 2 ≤ ‖z i - x i‖) → F j z = 0 := by
    intro j z hz
    refine hgsub j z ?_
    obtain ⟨i, hi⟩ := hz
    exact ⟨i, by rw [hhalf i] at hi; exact hi⟩
  -- ### differentiability of the potential on the polydisc
  have hdiff : ∀ z ∈ polydisc x rad, DifferentiableAt ℝ (bmPotential F) z := by
    have h1 := bmPotential_differentiableAt_holder (n := n) hn (c := x) (r := rr) (α := α)
      hα0 hα1 hrpos (g := F) hFfin hgsup
    rw [hpd] at h1
    exact h1
  -- ### the `C^{1,α}` bound on the polydisc
  obtain ⟨C, hCpos, hC⟩ := bmPot_holder_C0a (n := n) hn (c := x) (r := rr) (α := α) hα0 hα1 hrpos
  have hsumlt : (∑ j, Work.CR.Flat.holderNorm 0 α (F j) Set.univ) < ⊤ :=
    ENNReal.sum_lt_top.mpr fun j _ => hFfin j
  have hfun : (fun z => Work.CR.Flat.Cauchy.bmPot F z) = bmPotential F :=
    funext fun z => (bmPotential_eq_bmPot F z).symm
  have hbound : Work.CR.Flat.holderNorm 1 α (bmPotential F) (polydisc x rad)
      ≤ ENNReal.ofReal (C * (∑ j, Work.CR.Flat.holderNorm 0 α (F j) Set.univ).toReal) := by
    have hmain := hC F hgsup hFne
    rw [hpd, hfun] at hmain
    calc Work.CR.Flat.holderNorm 1 α (bmPotential F) (polydisc x rad)
        ≤ ENNReal.ofReal C * (∑ j, Work.CR.Flat.holderNorm 0 α (F j) Set.univ) := hmain
      _ = ENNReal.ofReal C *
            ENNReal.ofReal (∑ j, Work.CR.Flat.holderNorm 0 α (F j) Set.univ).toReal := by
            rw [ENNReal.ofReal_toReal hsumlt.ne]
      _ = ENNReal.ofReal (C * (∑ j, Work.CR.Flat.holderNorm 0 α (F j) Set.univ).toReal) :=
            (ENNReal.ofReal_mul hCpos.le).symm
  have hL5 := holderNorm_one_bounds (isOpen_polydisc x rad)
    (mul_nonneg hCpos.le ENNReal.toReal_nonneg) hbound
  have hHold : ∀ y ∈ polydisc x rad, ∀ y' ∈ polydisc x rad,
      ‖fderiv ℝ (bmPotential F) y - fderiv ℝ (bmPotential F) y'‖
        ≤ (C * (∑ j, Work.CR.Flat.holderNorm 0 α (F j) Set.univ).toReal) * ‖y - y'‖ ^ α :=
    hL5.2.2.2
  refine ⟨polydisc x rad, isOpen_polydisc x rad, ?_, ?_, ?_⟩
  · simp only [mem_polydisc]
    intro j
    rw [sub_self, norm_zero]
    exact hradpos j
  · intro z hz
    exact (hdiff z hz).differentiableWithinAt
  · exact continuousOn_of_holder_bound (α := α)
      (K := C * (∑ j, Work.CR.Flat.holderNorm 0 α (F j) Set.univ).toReal)
      (g := fderiv ℝ (bmPotential F)) (s := polydisc x rad)
      hα0 (mul_nonneg hCpos.le ENNReal.toReal_nonneg) hHold

end Work.NN.Core
