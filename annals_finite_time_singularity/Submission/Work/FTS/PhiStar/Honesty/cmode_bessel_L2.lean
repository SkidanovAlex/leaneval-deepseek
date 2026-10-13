/-
Copyright: work module for the Elgindi finite-time singularity project.

# `cmode_bessel_L2` — the angular mode coefficients of an `ℋ⁰` source

`Work.FTS.PhiStar.Series.cmode m F t` is the `e_m`-coefficient of the slice `F t ·` for the
self-adjoint weight `cos θ dθ` (`eFam m θ = cos θ · C^{(3/2)}_{2m+1}(sin θ)`).

The lemma has three conjuncts, and it is the *summability* (third) conjunct that matters for
the mode series `psiSeries`: the total `L²(z)`-energy of the `m`-th mode, weighted by the
squared norm `eNorm m = ∫_θ eFam m θ² cos θ`, is summable in `m`, with the *sum* bounded by the
`ℋ⁰`-energy of the source `F`.

* **Conjunct 1** (a.e. strong measurability) is `ModalSolution.aesm_cmode` (`SmoothOpen F`
  makes every slice integrable in the Fubini sense).
* **Conjunct 2** (`∫_0^∞ (cmode m F t)² dt < ∞`) is `ModalSolution.cmode_memLp`, whose only
  input beyond `SmoothOpen` is `∫∫_{Q0} F² < ∞`; that is
  `Work.FTS.PhiStar.integrableOn_sq_Q0_of_HkMem`, i.e. `HkMem α 0 F` (on the open quadrant both
  weights `w(z)²` and `sin(2θ)^{-η}` are `≥ 1`).
* **Conjunct 3** (summability) is Bessel's inequality integrated in `z`:
  * the slicewise Bessel bound `ModalSolution.cmode_bessel` gives
    `∑_{m≤N} eNorm m · (cmode m F z)² ≤ ∫_θ (F z θ)² cos θ` for every `z`;
  * integrating in `z` (`lintegral_mono`, the finite sum pulled out with the a.e. strong
    measurability of the summands) gives
    `∑_{m≤N} ∫⁻_z ofReal (eNorm m · cmode m F z²) ≤ ∫⁻_z ofReal (∫_θ (F z θ)² cos θ)`
    (`Honesty.besselZ_plain`);
  * the right-hand side is finite and dominated by `∫⁻_{Q0} ofReal (F²) < ∞`
    (`Honesty.C0_le_lintegral` together with `integrableOn_sq_Q0_of_HkMem`);
  * `ENNReal.toReal_sum` (each summand being finite since it is `≤ ` the full sum) turns the
    lintegral bound into a bound on the partial sums of the *real* series, and
    `summable_of_sum_range_le` concludes.  The identification of `∫_0^∞ (cmode m F t)² dt`
    with the `toReal` of the corresponding lintegral is
    `integral_eq_lintegral_of_nonneg_ae`, which needs no integrability.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.ClassC.bessel_cmode
import Submission.Work.EllipticEst.ModalSolution.cmode_memLp
import Submission.Work.FTS.PhiStar.Honesty.cmode_modeEnergy_integrable
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.EllExistHalf
import Submission.Work.FTS.PhiStar.Honesty.integrableOn_sq_cos_of_HkMem
import Submission.Work.FTS.PhiStar.Honesty.besselZ_plain
import Submission.Work.FTS.PhiStar.Honesty.C0_le_lintegral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

theorem cmode_bessel_L2 {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α 0 F) :
    (∀ m : ℕ, MeasureTheory.AEStronglyMeasurable
        (fun t : ℝ => Work.FTS.PhiStar.Series.cmode m F t)
        (MeasureTheory.volume.restrict (Set.Ioi 0))) ∧
    (∀ m : ℕ, MeasureTheory.IntegrableOn
        (fun t : ℝ => Work.FTS.PhiStar.Series.cmode m F t ^ 2) (Set.Ioi 0)) ∧
    Summable (fun m : ℕ =>
      (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
        * ∫ t in Set.Ioi 0, Work.FTS.PhiStar.Series.cmode m F t ^ 2) := by
  -- the `L²`-integrability of the source on the open quadrant, and the per-slice `cos`-honesty
  have hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.PhiStar.integrableOn_sq_Q0_of_HkMem hF hsm
  have hint : ∀ z ∈ Set.Ioi (0 : ℝ), MeasureTheory.IntegrableOn
      (fun θ : ℝ => F z θ ^ 2 * Real.cos θ) Work.Spaces.Iθ :=
    fun z hz => integrableOn_sq_cos_of_HkMem hF hz
  -- the two `lintegral` bounds of the Bessel argument
  have hDfin : (∫⁻ p in Work.FTS.EllipticEst.Q0, ENNReal.ofReal (F p.1 p.2 ^ 2)) < ⊤ :=
    hL2.lintegral_lt_top
  have hC0le : (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal
        (∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ))
      ≤ ∫⁻ p in Work.FTS.EllipticEst.Q0, ENNReal.ofReal (F p.1 p.2 ^ 2) :=
    C0_le_lintegral hsm hint
  have hC0fin : (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal
        (∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ)) < ⊤ :=
    lt_of_le_of_lt hC0le hDfin
  have hbess : ∀ N : ℕ,
      (∑ m ∈ Finset.range (N + 1), ∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal
          (Work.EllipticEst.ModalSolution.eNorm m *
            Work.FTS.PhiStar.Series.cmode m F z ^ 2))
        ≤ ∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal
            (∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ) :=
    fun N => besselZ_plain hsm hint N
  -- every single summand of the Bessel sum is finite
  have hAfine : ∀ m : ℕ,
      (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal
          (Work.EllipticEst.ModalSolution.eNorm m *
            Work.FTS.PhiStar.Series.cmode m F z ^ 2)) ≠ ⊤ := by
    intro m
    have hsingle : (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal
          (Work.EllipticEst.ModalSolution.eNorm m *
            Work.FTS.PhiStar.Series.cmode m F z ^ 2))
        ≤ ∑ i ∈ Finset.range (m + 1), ∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal
            (Work.EllipticEst.ModalSolution.eNorm i *
              Work.FTS.PhiStar.Series.cmode i F z ^ 2) :=
      Finset.single_le_sum
        (f := fun i : ℕ => ∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal
            (Work.EllipticEst.ModalSolution.eNorm i *
              Work.FTS.PhiStar.Series.cmode i F z ^ 2))
        (fun i _ => zero_le) (Finset.mem_range.mpr (Nat.lt_succ_self m))
    exact ne_top_of_le_ne_top (ne_of_lt hC0fin) (le_trans hsingle (hbess m))
  -- the per-mode energy is the `toReal` of the corresponding lintegral
  have hterm : ∀ m : ℕ,
      (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
        * (∫ t in Set.Ioi (0 : ℝ), Work.FTS.PhiStar.Series.cmode m F t ^ 2)
      = (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal
          (Work.EllipticEst.ModalSolution.eNorm m *
            Work.FTS.PhiStar.Series.cmode m F z ^ 2)).toReal := by
    intro m
    have hconv : (∫ t in Set.Ioi (0 : ℝ), Work.FTS.PhiStar.Series.cmode m F t ^ 2)
        = (∫⁻ t in Set.Ioi (0 : ℝ),
            ENNReal.ofReal (Work.FTS.PhiStar.Series.cmode m F t ^ 2)).toReal :=
      MeasureTheory.integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall (fun t => sq_nonneg _))
        ((Work.EllipticEst.ModalSolution.aesm_cmode hsm m).pow 2)
    have hunfold : (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal
          (Work.EllipticEst.ModalSolution.eNorm m *
            Work.FTS.PhiStar.Series.cmode m F z ^ 2))
        = ENNReal.ofReal (Work.EllipticEst.ModalSolution.eNorm m)
          * ∫⁻ t in Set.Ioi (0 : ℝ),
              ENNReal.ofReal (Work.FTS.PhiStar.Series.cmode m F t ^ 2) := by
      rw [MeasureTheory.lintegral_congr (g := fun z : ℝ =>
        ENNReal.ofReal (Work.EllipticEst.ModalSolution.eNorm m)
          * ENNReal.ofReal (Work.FTS.PhiStar.Series.cmode m F z ^ 2))
        (fun z => ENNReal.ofReal_mul
          (le_of_lt (Work.EllipticEst.ModalSolution.eNorm_pos m)))]
      exact MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    rw [hconv, hunfold, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (le_of_lt (Work.EllipticEst.ModalSolution.eNorm_pos m))]
    rfl
  refine ⟨fun m => Work.EllipticEst.ModalSolution.aesm_cmode hsm m,
    fun m => Work.EllipticEst.ModalSolution.cmode_memLp hsm hL2 m, ?_⟩
  -- the summability of the mode energies
  refine summable_of_sum_range_le
    (f := fun m : ℕ =>
      (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
        * ∫ t in Set.Ioi (0 : ℝ), Work.FTS.PhiStar.Series.cmode m F t ^ 2)
    (c := (∫⁻ p in Work.FTS.EllipticEst.Q0, ENNReal.ofReal (F p.1 p.2 ^ 2)).toReal) ?_ ?_
  · intro n
    rw [hterm n]
    exact ENNReal.toReal_nonneg
  · intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp only [Finset.range_zero, Finset.sum_empty]
      exact ENNReal.toReal_nonneg
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
      calc (∑ i ∈ Finset.range (k + 1), (∫ θ in Work.Spaces.Iθ,
            Work.FTS.PhiStar.Gegenbauer.eFam i θ ^ 2 * Real.cos θ)
              * ∫ t in Set.Ioi (0 : ℝ), Work.FTS.PhiStar.Series.cmode i F t ^ 2)
          = ∑ i ∈ Finset.range (k + 1), (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal
              (Work.EllipticEst.ModalSolution.eNorm i *
                Work.FTS.PhiStar.Series.cmode i F z ^ 2)).toReal :=
            Finset.sum_congr rfl (fun i _ => hterm i)
        _ = (∑ i ∈ Finset.range (k + 1), ∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal
              (Work.EllipticEst.ModalSolution.eNorm i *
                Work.FTS.PhiStar.Series.cmode i F z ^ 2)).toReal :=
            (ENNReal.toReal_sum (fun i _ => hAfine i)).symm
        _ ≤ (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal
              (∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ)).toReal :=
            ENNReal.toReal_mono (ne_of_lt hC0fin) (hbess k)
        _ ≤ (∫⁻ p in Work.FTS.EllipticEst.Q0,
              ENNReal.ofReal (F p.1 p.2 ^ 2)).toReal :=
            ENNReal.toReal_mono (ne_of_lt hDfin) hC0le

end Work.FTS.PhiStar.Honesty
