/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Finite `C^{0,α}`-bound for `∂(bmPotential G)` on a polydisc

For continuous, compactly supported data `G` whose `C^{0,α}`-norm on `ℂⁿ` is finite (i.e. `G` is
globally `α`-Hölder), the `(1,0)`-derivative `∂_i (bmPotential G)` of the Bochner–Martinelli
potential is again of class `C^{0,α}` on any polydisc `polydisc 0 τ`, with a bound depending on the
datum.

The estimate is a corollary of the Schauder estimate `dCoord_bmPot_holderNorm_le`
(`Submission.Work.NN.Core.beltrami_theta_est`), which bounds the `C^{0,α}`-norm of `∂_i (bmPot H)`
on a polydisc `polydisc 0 τ` by a constant times `Σ_j ‖H_j‖_{C^{0,α}}`, provided `H` vanishes off a
smaller polydisc `polydisc 0 σ ⊆ polydisc 0 τ`.  Since the data here are only assumed to have
compact support, we first choose a multi-radius `S` so large that the polydisc `polydisc 0 S`
contains both the support of `G` and the target polydisc `polydisc 0 τ` (a compactly supported
function vanishes outside a ball, `BTheta.exists_radius_of_hasCompactSupport`), apply the estimate
there and restrict to `polydisc 0 τ` by monotonicity of the `C^{k,α}`-norm in the set.
-/
import Mathlib
import Submission.Work.NN.Core.bmPotentialHolderContinuous
import Submission.Work.NN.Core.beltrami_theta_est

noncomputable section

open scoped NNReal ENNReal
open Set

namespace Work.NN.Core

/-- **Finiteness of the `C^{0,α}`-norm of `∂_i (bmPotential G)` on a polydisc.**

For `n ≥ 1`, `0 < α < 1`, positive multi-radii `τ`, and a datum `G` (a family of `n` functions on
`ℂⁿ`) which is continuous, compactly supported and of finite `C^{0,α}`-norm on all of `ℂⁿ`, there is
a constant `C > 0` with

  `‖∂_i (bmPotential G)‖_{C^{0,α}(polydisc 0 τ)} ≤ C`  for every `i`.

(The constant is allowed to depend on `G`: it is `2 C₀ Σ_j ‖G_j‖_{C^{0,α}} + 1`, where `C₀` is the
Schauder constant of a polydisc containing both the support of `G` and `polydisc 0 τ`.) -/
theorem dCoord_bmPotential_finite_holder {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {τ : Fin n → ℝ} (hτ : ∀ j, 0 < τ j) :
    ∀ (G : Fin n → (Fin n → ℂ) → ℂ), (∀ j, Continuous (G j)) →
      (∀ j, HasCompactSupport (G j)) →
      (∀ j, Work.CR.Flat.holderNorm 0 α (G j) Set.univ < ⊤) →
      ∃ C : ℝ, 0 < C ∧ ∀ i : Fin n,
        Work.CR.Flat.holderNorm 0 α (fun z => Work.CR.Flat.dCoord i
            (Work.CR.Flat.Cauchy.bmPotential G) z) (Work.CR.Flat.polydisc 0 τ)
          ≤ ENNReal.ofReal C := by
  intro G _ hGcs hGfin
  -- ## A multi-radius bounding the supports of the data
  choose R hR0 hR using fun j => BTheta.exists_radius_of_hasCompactSupport (hGcs j)
  have hRsum0 : (0 : ℝ) ≤ ∑ j, R j := Finset.sum_nonneg fun j _ => hR0 j
  have hτsum0 : (0 : ℝ) ≤ ∑ j, τ j := Finset.sum_nonneg fun j _ => (hτ j).le
  set S : ℝ := (∑ j, R j) + (∑ j, τ j) + 1 with hSdef
  have hSpos : 0 < S := by rw [hSdef]; linarith
  have hRS : ∀ j, R j ≤ S := by
    intro j
    have h1 : R j ≤ ∑ i, R i := Finset.single_le_sum (fun i _ => hR0 i) (Finset.mem_univ j)
    rw [hSdef]; linarith
  have hτS : ∀ j, τ j ≤ S := by
    intro j
    have h1 : τ j ≤ ∑ i, τ i := Finset.single_le_sum (fun i _ => (hτ i).le) (Finset.mem_univ j)
    rw [hSdef]; linarith
  -- ## The Schauder estimate on the large polydisc `polydisc 0 (fun _ => S)`
  obtain ⟨C₀, hC₀pos, hC₀⟩ := BTheta.dCoord_bmPot_holderNorm_le (n := n) hn
    (α := α) hα0 hα1 (σ := fun _ => S) (τ := fun _ => S)
    (fun j => hSpos) (fun j => hSpos) (fun j => le_rfl)
  -- `G` vanishes off that polydisc: outside it some coordinate is at least `S ≥ R j`
  have hsupp : ∀ j (z : Fin n → ℂ), z ∉ Work.CR.Flat.polydisc 0 (fun _ : Fin n => S) →
      G j z = 0 := by
    intro j z hz
    refine hR j z ?_
    have hz1 : ∃ k, S ≤ ‖z k‖ := by
      by_contra hcon
      push Not at hcon
      exact hz (by rw [Work.CR.Flat.mem_polydisc]; intro k; simpa using hcon k)
    obtain ⟨k, hk⟩ := hz1
    calc R j ≤ S := hRS j
      _ ≤ ‖z k‖ := hk
      _ ≤ ‖z‖ := norm_le_pi_norm z k
  have hmain := hC₀ G (fun j => hGfin j) hsupp
  -- ## The (finite) value of the sum of the `C^{0,α}`-norms of the data
  set Ssum : ℝ≥0∞ := ∑ j, Work.CR.Flat.holderNorm 0 α (G j) Set.univ with hSsumdef
  have hSsum_top : Ssum ≠ ⊤ := by
    rw [hSsumdef]
    exact ENNReal.sum_ne_top.mpr (fun j _ => ne_of_lt (hGfin j))
  set K : ℝ := Ssum.toReal with hKdef
  have hK0 : 0 ≤ K := ENNReal.toReal_nonneg
  have hofK : ENNReal.ofReal K = Ssum := ENNReal.ofReal_toReal hSsum_top
  refine ⟨2 * C₀ * K + 1, by positivity, fun i => ?_⟩
  -- ## Restriction from `polydisc 0 (fun _ => S)` to `polydisc 0 τ`
  have hsub : Work.CR.Flat.polydisc 0 τ ⊆ Work.CR.Flat.polydisc 0 (fun _ : Fin n => S) := by
    intro z hz
    rw [Work.CR.Flat.mem_polydisc] at hz ⊢
    intro j
    exact lt_of_lt_of_le (hz j) (hτS j)
  -- `bmPotential` and `bmPot` are the same function
  have hbmpot : (fun z => Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential G) z)
      = fun z => Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPot G) z := by
    have hfun : Work.CR.Flat.Cauchy.bmPotential G = Work.CR.Flat.Cauchy.bmPot G :=
      funext fun w => Work.CR.Flat.Cauchy.bmPotential_eq_bmPot G w
    rw [hfun]
  calc Work.CR.Flat.holderNorm 0 α (fun z => Work.CR.Flat.dCoord i
          (Work.CR.Flat.Cauchy.bmPotential G) z) (Work.CR.Flat.polydisc 0 τ)
      = Work.CR.Flat.holderNorm 0 α (fun z => Work.CR.Flat.dCoord i
          (Work.CR.Flat.Cauchy.bmPot G) z) (Work.CR.Flat.polydisc 0 τ) := by rw [hbmpot]
    _ ≤ Work.CR.Flat.holderNorm 0 α (fun z => Work.CR.Flat.dCoord i
          (Work.CR.Flat.Cauchy.bmPot G) z) (Work.CR.Flat.polydisc 0 (fun _ : Fin n => S)) :=
        Work.CR.Flat.holderNorm_mono_set (Work.CR.Flat.isOpen_polydisc 0 (fun _ : Fin n => S))
          (Work.CR.Flat.isOpen_polydisc 0 τ) hsub 0 α _
    _ ≤ ENNReal.ofReal C₀ * Ssum := hmain i
    _ = ENNReal.ofReal (C₀ * K) := by rw [← hofK, ← ENNReal.ofReal_mul hC₀pos.le]
    _ ≤ ENNReal.ofReal (2 * C₀ * K + 1) := by
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith [hC₀pos.le, hK0]

end Work.NN.Core
