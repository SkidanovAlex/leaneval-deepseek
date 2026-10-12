import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.q2wordAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory
open scoped BigOperators

noncomputable section

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## Helper layer

The mass row of the box/Fock dictionary compares the windowed mass
`M₂·∑ᵢⱼ∫(PᵢQⱼΨ)²χ(x_j)²` with the "fibre" pairing `∑ᵢⱼ∫(PᵢQⱼΨ)²fib(x_j)`, against
the supply `e₂·∑ᵢⱼ∫(PᵢQⱼΨ)²`.

The proof has three independent ingredients.

* `massRow_aP_sub` / `massRow_aP_aQ_self`: the projection algebra `PᵢQᵢ = 0`, which kills
  the diagonal pairs `i = j`.
* `massRow_pair_le_aux`: the *single-pair* integral inequality, obtained by integrating the
  pointwise bound `M₂ χ² − e₂ ≤ fib` against the non-negative weight `(PᵢQⱼΨ)²`.
* `massRow_sum_le`: the purely combinatorial passage from the pairwise inequality to the
  inequality between the sums.
-/

/-- `aP` is additive in its state argument, pointwise. -/
private lemma massRow_aP_sub {N : ℕ} {ℓ : ℝ} (i : Fin N) {f g : X N → ℝ} (x : X N)
    (hf : IntegrableOn (fun y : E3 => f (Function.update x i y)) (acube ℓ) volume)
    (hg : IntegrableOn (fun y : E3 => g (Function.update x i y)) (acube ℓ) volume) :
    aP ℓ i (fun z => f z - g z) x = aP ℓ i f x - aP ℓ i g x := by
  simp only [aP]
  rw [integral_sub hf hg]
  ring

/-- `Pᵢ Qᵢ = 0`: the projection onto the constant fibre of a function with vanishing
centred-box mean. -/
private lemma massRow_aP_aQ_self {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) : aP ℓ i (aQ ℓ i Φ) = 0 := by
  funext x
  have hf : IntegrableOn (fun y : E3 => Φ (Function.update x i y)) (acube ℓ) volume :=
    integrableOn_acube_of_continuous hℓ (hΦc.comp (by fun_prop))
  have hg : IntegrableOn (fun y : E3 => aP ℓ i Φ (Function.update x i y)) (acube ℓ) volume :=
    integrableOn_acube_of_continuous hℓ ((aP_continuous hℓ i hΦc).comp (by fun_prop))
  have h1 : aP ℓ i (fun z => Φ z - aP ℓ i Φ z) x
      = aP ℓ i Φ x - aP ℓ i (aP ℓ i Φ) x :=
    massRow_aP_sub (ℓ := ℓ) i x (f := Φ) (g := aP ℓ i Φ) hf hg
  have h2 : aP ℓ i (aQ ℓ i Φ) x = aP ℓ i Φ x - aP ℓ i (aP ℓ i Φ) x := h1
  rw [h2, aP_idem hℓ i hΦc x, sub_self]
  simp

/-- The single-pair integral inequality: integrating the pointwise bound
`M₂·χ(x_j)² − e₂ ≤ fib(x_j)` against a non-negative continuous weight `P`. -/
private lemma massRow_pair_le_aux {N : ℕ} {ℓ M₂ e₂ Cw : ℝ} (hℓ : 0 < ℓ)
    {P : X N → ℝ} (hPc : Continuous P) (hPnn : ∀ x, 0 ≤ P x) {j : Fin N} {fib : E3 → ℝ}
    (hfibm : AEStronglyMeasurable fib (volume.restrict (acube ℓ)))
    (hfibb : ∀ z : E3, z ∈ acube ℓ → |fib z| ≤ Cw)
    (hfib : ∀ z : E3, M₂ * (chiScale ℓ z) ^ 2 - e₂ ≤ fib z) :
    M₂ * (∫ x in abox N ℓ, P x * (chiScale ℓ (x j)) ^ 2)
      - (∫ x in abox N ℓ, P x * fib (x j))
    ≤ e₂ * (∫ x in abox N ℓ, P x) := by
  have hCw0 : 0 ≤ Cw :=
    le_trans (abs_nonneg _) (hfibb ((0 : X N) j) ((zero_mem_abox hℓ.le) j))
  have hχc : Continuous (fun x : X N => (chiScale ℓ (x j)) ^ 2) :=
    ((chiScale_continuous ℓ).comp (by fun_prop)).pow 2
  obtain ⟨BP, hBP⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn
    (s := abox N ℓ) (f := P) hPc.continuousOn
  have hBP0 : 0 ≤ BP := le_trans (norm_nonneg _) (hBP 0 (zero_mem_abox hℓ.le))
  have hIP : IntegrableOn P (abox N ℓ) volume := integrableOn_abox_of_continuous hℓ hPc
  have hIPMchi : IntegrableOn (fun x : X N => P x * (M₂ * (chiScale ℓ (x j)) ^ 2))
      (abox N ℓ) volume :=
    integrableOn_abox_of_continuous hℓ (hPc.mul (continuous_const.mul hχc))
  have hIPe : IntegrableOn (fun x : X N => P x * e₂) (abox N ℓ) volume :=
    Integrable.mul_const hIP e₂
  have hqmp : Measure.QuasiMeasurePreserving (fun x : X N => x j)
      (volume.restrict (abox N ℓ)) (volume.restrict (acube ℓ)) := by
    rw [restrict_abox_eq_pi N ℓ]
    exact Measure.quasiMeasurePreserving_eval
      (fun _ : Fin N => (volume : Measure E3).restrict (acube ℓ)) j
  have hfibmeas : AEStronglyMeasurable (fun x : X N => fib (x j))
      (volume.restrict (abox N ℓ)) :=
    hfibm.comp_quasiMeasurePreserving hqmp
  have hIPfib : IntegrableOn (fun x : X N => P x * fib (x j)) (abox N ℓ) volume := by
    refine IntegrableOn.of_bound (abox_lt_top N ℓ hℓ.le) ?_ (BP * Cw) ?_
    · exact (hPc.aestronglyMeasurable.restrict (s := abox N ℓ)).mul hfibmeas
    · rw [ae_restrict_iff' (abox_measurable N ℓ)]
      refine ae_of_all volume (fun x hx => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |P x| ≤ BP := by
        have := hBP x hx
        rwa [Real.norm_eq_abs] at this
      exact mul_le_mul h1 (hfibb (x j) (hx j)) (abs_nonneg _) hBP0
  have hstep1 : M₂ * (∫ x in abox N ℓ, P x * (chiScale ℓ (x j)) ^ 2)
      = ∫ x in abox N ℓ, P x * (M₂ * (chiScale ℓ (x j)) ^ 2) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))
  calc M₂ * (∫ x in abox N ℓ, P x * (chiScale ℓ (x j)) ^ 2)
        - (∫ x in abox N ℓ, P x * fib (x j))
      = (∫ x in abox N ℓ, P x * (M₂ * (chiScale ℓ (x j)) ^ 2))
        - (∫ x in abox N ℓ, P x * fib (x j)) := by rw [hstep1]
    _ = ∫ x in abox N ℓ,
          (P x * (M₂ * (chiScale ℓ (x j)) ^ 2) - P x * fib (x j)) := by
        rw [integral_sub hIPMchi hIPfib]
    _ ≤ ∫ x in abox N ℓ, P x * e₂ := by
        refine integral_mono (Integrable.sub hIPMchi hIPfib) hIPe (fun x => ?_)
        calc P x * (M₂ * (chiScale ℓ (x j)) ^ 2) - P x * fib (x j)
            = P x * (M₂ * (chiScale ℓ (x j)) ^ 2 - fib (x j)) := by ring
          _ ≤ P x * e₂ := mul_le_mul_of_nonneg_left (by linarith [hfib (x j)]) (hPnn x)
    _ = e₂ * (∫ x in abox N ℓ, P x) := by
        rw [integral_mul_const]
        ring

/-- The purely combinatorial passage: a pairwise bound between three families of reals
gives the same bound between the double sums. -/
private lemma massRow_sum_le {N : ℕ} {M₂ e₂ : ℝ} (U V W : Fin N → Fin N → ℝ)
    (hpair : ∀ j i : Fin N, M₂ * U j i - V j i ≤ e₂ * W j i) :
    M₂ * (∑ j : Fin N, ∑ i : Fin N, U j i) - (∑ j : Fin N, ∑ i : Fin N, V j i)
      ≤ e₂ * (∑ j : Fin N, ∑ i : Fin N, W j i) := by
  have h1 : M₂ * (∑ j : Fin N, ∑ i : Fin N, U j i)
      = ∑ j : Fin N, ∑ i : Fin N, M₂ * U j i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
  have h2 : M₂ * (∑ j : Fin N, ∑ i : Fin N, U j i) - (∑ j : Fin N, ∑ i : Fin N, V j i)
      = ∑ j : Fin N, ∑ i : Fin N, (M₂ * U j i - V j i) := by
    rw [h1, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_sub_distrib]
  calc M₂ * (∑ j : Fin N, ∑ i : Fin N, U j i) - (∑ j : Fin N, ∑ i : Fin N, V j i)
      = ∑ j : Fin N, ∑ i : Fin N, (M₂ * U j i - V j i) := h2
    _ ≤ ∑ j : Fin N, ∑ i : Fin N, e₂ * W j i :=
        Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun i _ => hpair j i))
    _ = e₂ * (∑ j : Fin N, ∑ i : Fin N, W j i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.mul_sum]

theorem massRowDiff_le {N : ℕ} {ℓ M₂ e₂ Cw : ℝ} (hℓ : 0 < ℓ) (hM₂ : 0 ≤ M₂) (he₂ : 0 ≤ e₂)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨc : Continuous Ψ)
    {fib : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hfibm : AEStronglyMeasurable fib (volume.restrict (Submission.BoseGases.acube ℓ)))
    (hfibb : ∀ z : EuclideanSpace ℝ (Fin 3), z ∈ Submission.BoseGases.acube ℓ → |fib z| ≤ Cw)
    (hfib : ∀ z : EuclideanSpace ℝ (Fin 3),
      M₂ * (Submission.BoseGases.chiScale ℓ z) ^ 2 - e₂ ≤ fib z) :
    (ℓ ^ 3)⁻¹ * M₂ * (∑ j : Fin N, ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j Ψ) x) ^ 2
          * (Submission.BoseGases.chiScale ℓ (x j)) ^ 2)
      - (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∑ j : Fin N, (if j ≠ i then
          (∫ x in Submission.BoseGases.abox N ℓ,
            (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Ψ) x) ^ 2 * fib (x i))
          else 0))
    ≤ (ℓ ^ 3)⁻¹ * e₂ * (∑ i : Fin N, ∑ j : Fin N,
        ∫ x in Submission.BoseGases.abox N ℓ,
          (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Ψ) x) ^ 2) := by
  have hℓinv : (0 : ℝ) ≤ (ℓ ^ 3)⁻¹ := by positivity
  -- Step 0: put the two outer sums in the common convention (weight index `j` outside,
  -- projection index `i` inside); the statements differ only by renaming bound variables.
  show (ℓ ^ 3)⁻¹ * M₂ * (∑ j : Fin N, ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j Ψ) x) ^ 2
          * (Submission.BoseGases.chiScale ℓ (x j)) ^ 2)
      - (ℓ ^ 3)⁻¹ * (∑ j : Fin N, ∑ i : Fin N, (if i ≠ j then
          (∫ x in Submission.BoseGases.abox N ℓ,
            (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j Ψ) x) ^ 2 * fib (x j))
          else 0))
    ≤ (ℓ ^ 3)⁻¹ * e₂ * (∑ j : Fin N, ∑ i : Fin N,
        ∫ x in Submission.BoseGases.abox N ℓ,
          (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j Ψ) x) ^ 2)
  set S1 : ℝ := ∑ j : Fin N, ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
      (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j Ψ) x) ^ 2
        * (Submission.BoseGases.chiScale ℓ (x j)) ^ 2 with hS1
  set S2 : ℝ := ∑ j : Fin N, ∑ i : Fin N, (if i ≠ j then
      (∫ x in Submission.BoseGases.abox N ℓ,
        (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j Ψ) x) ^ 2 * fib (x j))
      else 0) with hS2
  set S3 : ℝ := ∑ j : Fin N, ∑ i : Fin N,
      ∫ x in Submission.BoseGases.abox N ℓ,
        (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j Ψ) x) ^ 2 with hS3
  have hpair : ∀ j i : Fin N,
      M₂ * (∫ x in Submission.BoseGases.abox N ℓ,
          (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j Ψ) x) ^ 2
            * (Submission.BoseGases.chiScale ℓ (x j)) ^ 2)
        - (if i ≠ j then
            (∫ x in Submission.BoseGases.abox N ℓ,
              (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j Ψ) x) ^ 2 * fib (x j))
            else 0)
      ≤ e₂ * (∫ x in Submission.BoseGases.abox N ℓ,
          (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j Ψ) x) ^ 2) := by
    intro j i
    by_cases hij : i = j
    · subst hij
      have hz : Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ i Ψ) = 0 :=
        massRow_aP_aQ_self hℓ i hΨc
      have h1 : (∫ x in Submission.BoseGases.abox N ℓ,
          (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ i Ψ) x) ^ 2
            * (Submission.BoseGases.chiScale ℓ (x i)) ^ 2) = 0 := by simp [hz]
      have h2 : (∫ x in Submission.BoseGases.abox N ℓ,
          (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ i Ψ) x) ^ 2) = 0 := by
        simp [hz]
      rw [h1, h2, if_neg (not_not.mpr rfl)]
      simp
    · rw [if_pos hij]
      exact massRow_pair_le_aux hℓ
        ((aP_continuous hℓ i (aQ_continuous hℓ j hΨc)).pow 2)
        (fun x => sq_nonneg _) hfibm hfibb hfib
  have hS : M₂ * S1 - S2 ≤ e₂ * S3 := by
    rw [hS1, hS2, hS3]
    exact massRow_sum_le _ _ _ hpair
  have hfin : (ℓ ^ 3)⁻¹ * M₂ * S1 - (ℓ ^ 3)⁻¹ * S2 ≤ (ℓ ^ 3)⁻¹ * e₂ * S3 := by
    rw [show (ℓ ^ 3)⁻¹ * M₂ * S1 - (ℓ ^ 3)⁻¹ * S2 = (ℓ ^ 3)⁻¹ * (M₂ * S1 - S2) by ring,
      show (ℓ ^ 3)⁻¹ * e₂ * S3 = (ℓ ^ 3)⁻¹ * (e₂ * S3) by ring]
    exact mul_le_mul_of_nonneg_left hS hℓinv
  exact hfin

end

end Work.BoseBoxFock
