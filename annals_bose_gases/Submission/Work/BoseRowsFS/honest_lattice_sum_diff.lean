import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseRowsFS.Hon
import Submission.Work.BoseRowsFS.W1sub_g0_ae_bounds
import Submission.Work.BoseRowsFS.chat_g0_abs_le
import Submission.Work.BoseRowsFS.chat_sub
import Submission.Work.BoseRowsFS.honest_lattice_W1sq_le_uniform
import Submission.Work.BoseRowsFS.momentum_coulomb_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.honest_lattice_sum_diff`

The lattice half of `IntKernel.sum_diff` at the honest model, in the *mixed* form:

    ∃ C ≥ 0, ∀ ℓ ≥ 1, R ≤ ℓ, R ≤ ℓ·chiR0, ∀ S : Finset (Fin 3 → ℤ) (nonzero indices),
      ℓ⁻³ Σ_{m∈S} (Ŵ₁(k_m) − ĝ(k_m))²/‖k_m‖²  ≤  C·a v·(R/ℓ)⁴.

## Route

Put `D := W₁ − g₀` (with `W₁ = W1fun v h ℓ = wScaled ℓ (g₀)`, `g₀ = g0 v h`).  Then

* `0 ≤ D ≤ 2C₁(R/ℓ)²·g₀` a.e. (`Work.BoseRowsFS.W1sub_g0_ae_bounds`, from the sharp a.e.
  sandwich), so `|D| ≤ W₁` a.e.;
* `D` is even (`Work.BoseFixR.isEven_W1fun`, `Submission.BoseGases.g0_even`), integrable
  (`wScaled_g0_integrable`, `g0_integrable`), and `tsupport D ⊆ ball 0 R` (both kernels are
  supported on `supp v`);
* the pair (Coulomb) kernel of `D` is integrable: `|D| ≤ W₁` a.e. dominates it by the pair kernel
  of `W₁`, which is integrable (`Work.BoseRowsFS.honest_W1_pair_integrable`).

Hence `Work.BoseRowsFS.lattice_row_aux` (the uniform lattice-versus-continuum comparison, constant
`10⁸(1+R)⁵`) applies to `D`, and `Work.BoseRowsFS.momentum_coulomb_le` bounds the continuum
integral by `(2C₁(R/ℓ)²)²·∫g₀ω`.  Finally
`Submission.BoseGases.chosen_gomega_integral_bounds` gives `∫g₀ω ≤ 8π·a v`, and
`Work.BoseRowsFS.chat_sub` identifies `chat D = chat W₁ − chat g₀` pointwise, so the target's
summand is the `D`-summand.
-/

namespace Work.BoseRowsFS

open scoped Real BigOperators Topology
open MeasureTheory Metric

theorem honest_lattice_sum_diff {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    (R : ℝ) (hR : 0 < R)
    (hav : 0 < _root_.BoseGases.a v)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℝ, 1 ≤ ℓ → R ≤ ℓ →
      R ≤ ℓ * Submission.BoseGases.chiR0 →
      ∀ S : Finset (Fin 3 → ℤ), (∀ m ∈ S, m ≠ 0) →
        ℓ ^ (-(3 : ℝ)) *
            ∑ m ∈ S, (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (kvec ℓ m)
                - Work.BoseFixR.chat (Submission.BoseGases.g0 v h) (kvec ℓ m)) ^ 2
              / ‖kvec ℓ m‖ ^ 2
          ≤ C * _root_.BoseGases.a v * (R / ℓ) ^ 4 := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := Work.BoseB7AK.C3Q.conv3chi_dev_quad
  refine ⟨10 ^ 8 * (1 + R) ^ 5 * (4 * C₁ ^ 2) * (8 * Real.pi), by positivity, ?_⟩
  intro ℓ hℓ1 hRℓ hRchi S hS
  have hℓ0 : (0 : ℝ) < ℓ := lt_of_lt_of_le zero_lt_one hℓ1
  -- the difference kernel `D = W₁ − g₀`
  let D : EuclideanSpace ℝ (Fin 3) → ℝ :=
    fun x => Work.BoseFixR.W1fun v h ℓ x - Submission.BoseGases.g0 v h x
  -- integrability of the two kernels and of `D`
  have hW1I : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h ℓ) :=
    Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ0 hRchi
  have hgI : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR hv_supp h
  have hDI : MeasureTheory.Integrable D := hW1I.sub hgI
  -- the a.e. two-sided bound on `D`
  have hae := W1sub_g0_ae_bounds hR hℓ0 hC₁0 hC₁ hv_nonneg hvrad hv_supp h hRchi
  have hD0 : ∀ᵐ x, 0 ≤ D x := hae.mono (fun x hx => hx.1)
  have hDc : ∀ᵐ x, D x ≤ (2 * C₁ * (R / ℓ) ^ 2) * Submission.BoseGases.g0 v h x :=
    hae.mono (fun x hx => hx.2)
  -- evenness
  have hDe : ∀ x, D (-x) = D x := by
    intro x
    show Work.BoseFixR.W1fun v h ℓ (-x) - Submission.BoseGases.g0 v h (-x)
      = Work.BoseFixR.W1fun v h ℓ x - Submission.BoseGases.g0 v h x
    rw [Work.BoseFixR.isEven_W1fun h hvrad ℓ x, Submission.BoseGases.g0_even hvrad h x]
  -- support
  have hDs : tsupport D ⊆ Metric.ball 0 R := by
    have h1 : Function.support D ⊆ Function.support v := by
      intro x hx
      simp only [Function.mem_support] at hx ⊢
      intro hvx
      exact hx (by
        show Work.BoseFixR.W1fun v h ℓ x - Submission.BoseGases.g0 v h x = 0
        simp only [Work.BoseFixR.W1fun, Submission.BoseGases.wScaled, Submission.BoseGases.g0,
          hvx]
        ring)
    calc tsupport D = closure (Function.support D) := rfl
      _ ⊆ closure (Function.support v) := closure_mono h1
      _ = tsupport v := rfl
      _ ⊆ Metric.ball 0 R := hv_supp
  -- pair (Coulomb) integrability of `D`, by domination by the pair kernel of `W₁`
  have hcdW1 : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Work.BoseFixR.W1fun v h ℓ p.1 * Work.BoseFixR.W1fun v h ℓ p.2 / ‖p.1 - p.2‖) :=
    honest_W1_pair_integrable hR hℓ0 hv_nonneg hvrad hv_supp hRchi
  have hcd : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        D p.1 * D p.2 / ‖p.1 - p.2‖) := by
    have hDabs : ∀ᵐ x, |D x| ≤ Work.BoseFixR.W1fun v h ℓ x := by
      filter_upwards [hD0, Submission.BoseGases.g0_nonneg_ae hR hv_nonneg hvrad hv_supp h]
        with x h1 h2
      rw [abs_of_nonneg h1]
      show Work.BoseFixR.W1fun v h ℓ x - Submission.BoseGases.g0 v h x
        ≤ Work.BoseFixR.W1fun v h ℓ x
      linarith
    have hAEM : AEMeasurable
        (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          D z.1 * D z.2 / ‖z.1 - z.2‖) (MeasureTheory.volume.prod MeasureTheory.volume) :=
      ((hDI.aestronglyMeasurable.aemeasurable.comp_fst).mul
          (hDI.aestronglyMeasurable.aemeasurable.comp_snd)).div
        (((measurable_fst.sub measurable_snd).norm).aemeasurable)
    refine hcdW1.mono' hAEM.aestronglyMeasurable ?_
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hDabs,
      Measure.quasiMeasurePreserving_snd.ae hDabs] with p hp1 hp2
    have hden : (0 : ℝ) ≤ ‖p.1 - p.2‖ := norm_nonneg _
    have h1 : |D p.1| * |D p.2|
        ≤ Work.BoseFixR.W1fun v h ℓ p.1 * Work.BoseFixR.W1fun v h ℓ p.2 :=
      mul_le_mul hp1 hp2 (abs_nonneg _)
        (le_trans (abs_nonneg _) hp1)
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg hden]
    exact div_le_div_of_nonneg_right h1 hden
  -- the lattice-versus-continuum comparison at `D`
  have hlat := lattice_row_aux (W := D) hR hℓ1 hRℓ hDI hD0 hDe hDs hcd S hS
  -- the continuum bound at `D`
  have hmom := momentum_coulomb_le hR hℓ0 hv_nonneg hvrad hv_supp h hRchi
    (c := 2 * C₁ * (R / ℓ) ^ 2) (by positivity) hDI hD0 hDe hDc
  -- `∫ g₀ω ≤ 8π a v`
  have hgω : (∫ x, Submission.BoseGases.g0 v h x * Classical.choose h x)
      ≤ 8 * Real.pi * _root_.BoseGases.a v := by
    have hb := Submission.BoseGases.chosen_gomega_integral_bounds hR hv_nonneg hvrad hv_supp h
    simpa only [Submission.BoseGases.g0] using hb.2
  -- the chain
  have hCfac : (0 : ℝ) ≤ 10 ^ 8 * (1 + R) ^ 5 := by positivity
  have hchain : ℓ ^ (-(3 : ℝ)) * (∑ m ∈ S, (Work.BoseFixR.chat D (kvec ℓ m)) ^ 2
        / ‖kvec ℓ m‖ ^ 2)
      ≤ 10 ^ 8 * (1 + R) ^ 5
        * ((2 * C₁ * (R / ℓ) ^ 2) ^ 2 * (8 * Real.pi * _root_.BoseGases.a v)) := by
    calc ℓ ^ (-(3 : ℝ)) * (∑ m ∈ S, (Work.BoseFixR.chat D (kvec ℓ m)) ^ 2
            / ‖kvec ℓ m‖ ^ 2)
        ≤ (10 ^ 8 * (1 + R) ^ 5) * (((2 * Real.pi) ^ 3)⁻¹
            * (∫ p, Work.BoseFixR.chat D p ^ 2 / (2 * ‖p‖ ^ 2))) := hlat
      _ ≤ (10 ^ 8 * (1 + R) ^ 5)
            * ((2 * C₁ * (R / ℓ) ^ 2) ^ 2
              * (∫ x, Submission.BoseGases.g0 v h x * Classical.choose h x)) :=
          mul_le_mul_of_nonneg_left hmom hCfac
      _ ≤ 10 ^ 8 * (1 + R) ^ 5
            * ((2 * C₁ * (R / ℓ) ^ 2) ^ 2 * (8 * Real.pi * _root_.BoseGases.a v)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hgω (sq_nonneg _)) hCfac
  have hfin : 10 ^ 8 * (1 + R) ^ 5
        * ((2 * C₁ * (R / ℓ) ^ 2) ^ 2 * (8 * Real.pi * _root_.BoseGases.a v))
      = (10 ^ 8 * (1 + R) ^ 5 * (4 * C₁ ^ 2) * (8 * Real.pi)) * _root_.BoseGases.a v
        * (R / ℓ) ^ 4 := by ring
  have hmain : ℓ ^ (-(3 : ℝ)) * (∑ m ∈ S, (Work.BoseFixR.chat D (kvec ℓ m)) ^ 2
        / ‖kvec ℓ m‖ ^ 2)
      ≤ (10 ^ 8 * (1 + R) ^ 5 * (4 * C₁ ^ 2) * (8 * Real.pi)) * _root_.BoseGases.a v
        * (R / ℓ) ^ 4 := hfin ▸ hchain
  -- identify `chat D` with the difference of the two transforms
  have hsum_eq : (∑ m ∈ S, (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (kvec ℓ m)
          - Work.BoseFixR.chat (Submission.BoseGases.g0 v h) (kvec ℓ m)) ^ 2
        / ‖kvec ℓ m‖ ^ 2)
      = ∑ m ∈ S, (Work.BoseFixR.chat D (kvec ℓ m)) ^ 2 / ‖kvec ℓ m‖ ^ 2 := by
    refine Finset.sum_congr rfl (fun m _ => ?_)
    have hc := chat_sub hW1I hgI (kvec ℓ m)
    rw [← hc]
  rw [hsum_eq]
  exact hmain

end Work.BoseRowsFS
