import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixR.IntegrableChatW1sq
import Submission.Work.BoseRowsFS.W1_pair_integrable
import Submission.Work.BoseRowsL.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.Tails.lattice_energy_summable`

The two kinetic lattice rows of the honest gate are summable at every box side `ℓ ≥ 1` in the
dilute regime:

    Σ_{n ∈ ℤ³} (Ŵ₁(k_n)² + ĝ(k_n)²)/‖k_n‖²  < ∞ ,      k_n = kvec ℓ n = ℓ⁻¹ • vec n .

This is what makes the *full-lattice* form of the kinetic rows legitimate (the finite-set forms
`Work.BoseRowsFS.tailL` / `Work.BoseRowsFS.lattice_row_aux` only control finitely many modes, and
`summable_exp_div_norm_sq`-style Gaussian majorants apply to the *exponential*, not to `Ŵ₁/ĝ`).

## Route

Both kernels are handled by the same machine, `summable_chat_lattice_of_row`, whose only input is
the five hypotheses of the corpus's uniform lattice-versus-continuum comparison
`Work.BoseRowsFS.lattice_row_aux`:

* `W₁ = W1fun v h ℓ = wScaled ℓ (g₀)`: integrable (`wScaled_g0_integrable`), nonnegative a.e.
  (`wScaled_g0_nonneg_ae`), even (`isEven_W1fun`), supported in `ball 0 R`
  (`tsupport_W1fun_subset`), with integrable Coulomb pair kernel (`honest_W1_pair_integrable`);
* `g₀ = v(1−ω)`: integrable (`g0_integrable`), nonnegative a.e. (`g0_nonneg_ae`), even
  (`g0_even`), supported in `ball 0 R` (here), with integrable Coulomb pair kernel
  (`g0_pair_integrable` below — the `g₀⊗g₀` conjunct of `Work.BoseRowsFS.W1_g0_finite` run through
  the same Tonelli argument as its `W₁` sibling).

`lattice_row_aux` then gives, for *every* finite set `S` of nonzero labels,
`ℓ⁻³ Σ_{m∈S} Ŵ(k_m)²/‖k_m‖² ≤ 10⁸(1+R)⁵ (2π)⁻³∫Ŵ(p)²/(2‖p‖²)`; the summation criterion
`summable_of_sum_le` turns the uniform bound into `Summable` (the label `0` contributes
`chat(·)(0)²/‖0‖² = 0`).

A note on the constant: no decay of `Ŵ₁/ĝ` at infinity is used (and none is available for a general
`L¹` scattering numerator) — the bound is the *sampling* inequality of `lattice_row_aux`, i.e. the
nonnegativity of the kernel plus its Coulomb energy.
-/

namespace Work.BoseRowsL.Tails

open MeasureTheory
open scoped ENNReal Real

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The Coulomb pair kernel of `g₀ = v(1−ω)` is Bochner-integrable.**

Mirror of `Work.BoseRowsFS.honest_W1_pair_integrable` with `W₁` replaced by `g₀`.  The iterated
`∫⁻` of `g₀(x)g₀(y)/‖x−y‖` is finite — conjunct 2 of `Work.BoseRowsFS.W1_g0_finite`, which only
needs the `g₀`-side facts, so the auxiliary box side there may be taken `ℓ := R/chiR0` — and
Tonelli together with `MeasureTheory.lintegral_ofReal_ne_top_iff_integrable` upgrades it to
product-measure integrability. -/
theorem g0_pair_integrable {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {R : ℝ} (hR : 0 < R)
    (hv_nonneg : ∀ x : E3, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) :
    MeasureTheory.Integrable (fun p : E3 × E3 =>
      Submission.BoseGases.g0 v h p.1 * Submission.BoseGases.g0 v h p.2 / ‖p.1 - p.2‖) := by
  have hchi : (0 : ℝ) < Submission.BoseGases.chiR0 := Submission.BoseGases.chiR0_pos
  have hℓ0 : (0 : ℝ) < R / Submission.BoseGases.chiR0 := div_pos hR hchi
  have hRℓ : R ≤ (R / Submission.BoseGases.chiR0) * Submission.BoseGases.chiR0 := by
    rw [div_mul_cancel₀ R (ne_of_gt hchi)]
  -- finiteness of the iterated `∫⁻` of the pair kernel (the `g₀⊗g₀` conjunct)
  have hiter : (∫⁻ x : E3, ∫⁻ y : E3,
      ENNReal.ofReal (Submission.BoseGases.g0 v h x * Submission.BoseGases.g0 v h y / ‖x - y‖))
      ≠ ⊤ := (Work.BoseRowsFS.W1_g0_finite hR hℓ0 hv_nonneg hvrad hv_supp h hRℓ).2.1
  have hint : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR hv_supp h
  have hnn : ∀ᵐ x : E3, 0 ≤ Submission.BoseGases.g0 v h x :=
    Submission.BoseGases.g0_nonneg_ae hR hv_nonneg hvrad hv_supp h
  -- a.e. strong measurability of the pair integrand
  have hAEW : AEMeasurable (Submission.BoseGases.g0 v h)
      (MeasureTheory.volume : MeasureTheory.Measure E3) := hint.1.aemeasurable
  have hAEF : AEMeasurable (fun p : E3 × E3 =>
      Submission.BoseGases.g0 v h p.1 * Submission.BoseGases.g0 v h p.2 / ‖p.1 - p.2‖)
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    ((hAEW.comp_fst).mul (hAEW.comp_snd)).div
      ((measurable_fst.sub measurable_snd).norm.aemeasurable)
  have hF0 : 0 ≤ᵐ[(MeasureTheory.volume.prod MeasureTheory.volume :
        MeasureTheory.Measure (E3 × E3))]
      (fun p : E3 × E3 =>
        Submission.BoseGases.g0 v h p.1 * Submission.BoseGases.g0 v h p.2 / ‖p.1 - p.2‖) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hnn,
      Measure.quasiMeasurePreserving_snd.ae hnn] with p h1 h2
    exact div_nonneg (mul_nonneg h1 h2) (norm_nonneg _)
  -- Tonelli: the product-measure `∫⁻` equals the iterated one
  have hprod : (∫⁻ p : E3 × E3, ENNReal.ofReal (Submission.BoseGases.g0 v h p.1
        * Submission.BoseGases.g0 v h p.2 / ‖p.1 - p.2‖)
        ∂(MeasureTheory.volume.prod MeasureTheory.volume))
      = (∫⁻ x : E3, ∫⁻ y : E3, ENNReal.ofReal
          (Submission.BoseGases.g0 v h x * Submission.BoseGases.g0 v h y / ‖x - y‖)) :=
    MeasureTheory.lintegral_prod _ hAEF.ennreal_ofReal
  have hne : (∫⁻ p : E3 × E3, ENNReal.ofReal (Submission.BoseGases.g0 v h p.1
      * Submission.BoseGases.g0 v h p.2 / ‖p.1 - p.2‖)
      ∂(MeasureTheory.volume.prod MeasureTheory.volume)) ≠ ⊤ := by
    rw [hprod]
    exact hiter
  exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hAEF.aestronglyMeasurable hF0).mp hne

/-- `tsupport (g₀ v h) ⊆ ball 0 R` when `tsupport v ⊆ ball 0 R` (`g₀ = v·(1−ω)`). -/
theorem tsupport_g0_subset {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) :
    tsupport (Submission.BoseGases.g0 v h) ⊆ Metric.ball 0 R := by
  have h1 : Function.support (Submission.BoseGases.g0 v h) ⊆ Function.support v := by
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro hvx
    exact hx (by simp [Submission.BoseGases.g0, hvx])
  calc tsupport (Submission.BoseGases.g0 v h)
      = closure (Function.support (Submission.BoseGases.g0 v h)) := rfl
    _ ⊆ closure (Function.support v) := closure_mono h1
    _ = tsupport v := rfl
    _ ⊆ Metric.ball 0 R := hv_supp

/-- **The weighted lattice row of a `lattice_row_aux` kernel is summable.**

If `W` is `L¹`, nonnegative a.e., even, supported in `ball 0 R`, and has an integrable Coulomb pair
kernel, then for every box side `ℓ ≥ 1` with `R ≤ ℓ`

    Σ_{n ∈ ℤ³} Ŵ(k_n)²/‖k_n‖² < ∞ ,     k_n = kvec ℓ n .

The finite-set bound `Work.BoseRowsFS.lattice_row_aux` is uniform in the set, so the summation
criterion `summable_of_sum_le` applies; the label `0` is harmless since `kvec ℓ 0 = 0` and hence its
term is `Ŵ(0)²/0 = 0`. -/
theorem summable_chat_lattice_of_row {W : E3 → ℝ} {R ℓ : ℝ}
    (hR : 0 < R) (hℓ1 : 1 ≤ ℓ) (hRℓ : R ≤ ℓ)
    (hW : MeasureTheory.Integrable W) (hW0 : ∀ᵐ x : E3, 0 ≤ W x) (hWe : ∀ x : E3, W (-x) = W x)
    (hWs : tsupport W ⊆ Metric.ball 0 R)
    (hcd : MeasureTheory.Integrable (fun p : E3 × E3 => W p.1 * W p.2 / ‖p.1 - p.2‖)) :
    Summable (fun n : Fin 3 → ℤ =>
      (Work.BoseFixR.chat W (Work.BoseRowsFS.kvec ℓ n)) ^ 2 / ‖Work.BoseRowsFS.kvec ℓ n‖ ^ 2) := by
  have hℓ0 : (0 : ℝ) < ℓ := lt_of_lt_of_le zero_lt_one hℓ1
  have hℓ3 : (0 : ℝ) < ℓ ^ 3 := by positivity
  have hid : ℓ ^ 3 * ℓ ^ (-(3 : ℝ)) = 1 := by
    rw [← Real.rpow_natCast ℓ 3, ← Real.rpow_add hℓ0]
    norm_num
  have hzero : (Work.BoseFixR.chat W (Work.BoseRowsFS.kvec ℓ (0 : Fin 3 → ℤ))) ^ 2
      / ‖Work.BoseRowsFS.kvec ℓ (0 : Fin 3 → ℤ)‖ ^ 2 = 0 := by
    simp [Work.BoseRowsFS.kvec]
  refine summable_of_sum_le (f := fun n : Fin 3 → ℤ =>
    (Work.BoseFixR.chat W (Work.BoseRowsFS.kvec ℓ n)) ^ 2 / ‖Work.BoseRowsFS.kvec ℓ n‖ ^ 2)
    (c := ℓ ^ 3 * (10 ^ 8 * (1 + R) ^ 5 * (((2 * Real.pi) ^ 3)⁻¹
      * (∫ p : E3, (Work.BoseFixR.chat W p) ^ 2 / (2 * ‖p‖ ^ 2)))))
    (fun n => div_nonneg (sq_nonneg _) (by positivity)) ?_
  intro S
  -- the uniform sampling bound, over the nonzero labels of `S`
  have hrow := Work.BoseRowsFS.lattice_row_aux hR hℓ1 hRℓ hW hW0 hWe hWs hcd (S.erase 0)
    (fun m hm => (Finset.mem_erase.mp hm).1)
  have hsplit : (∑ m ∈ S, (Work.BoseFixR.chat W (Work.BoseRowsFS.kvec ℓ m)) ^ 2
        / ‖Work.BoseRowsFS.kvec ℓ m‖ ^ 2)
      = ∑ m ∈ S.erase 0, (Work.BoseFixR.chat W (Work.BoseRowsFS.kvec ℓ m)) ^ 2
        / ‖Work.BoseRowsFS.kvec ℓ m‖ ^ 2 := by
    by_cases h0 : (0 : Fin 3 → ℤ) ∈ S
    · have h := Finset.sum_erase_add S
          (fun m : Fin 3 → ℤ => (Work.BoseFixR.chat W (Work.BoseRowsFS.kvec ℓ m)) ^ 2
            / ‖Work.BoseRowsFS.kvec ℓ m‖ ^ 2) h0
      rw [hzero, add_zero] at h
      exact h.symm
    · rw [Finset.erase_eq_of_notMem h0]
  rw [hsplit]
  have hstep := mul_le_mul_of_nonneg_left hrow hℓ3.le
  rwa [← mul_assoc, hid, one_mul] at hstep

theorem lattice_energy_summable {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R : ℝ} (hR : 0 < R) (hav : 0 < _root_.BoseGases.a v)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) :
    ∀ ℓ : ℝ, 1 ≤ ℓ → R ≤ ℓ → R ≤ ℓ * Submission.BoseGases.chiR0 →
      Summable (fun n : Fin 3 → ℤ =>
        ((Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (Work.BoseRowsFS.kvec ℓ n)) ^ 2
          + (Work.BoseFixR.chat (Submission.BoseGases.g0 v h) (Work.BoseRowsFS.kvec ℓ n)) ^ 2)
        / ‖Work.BoseRowsFS.kvec ℓ n‖ ^ 2) := by
  intro ℓ hℓ1 hRℓ hRchi
  have hℓ0 : (0 : ℝ) < ℓ := lt_of_lt_of_le zero_lt_one hℓ1
  -- the two rows, both from the uniform lattice comparison
  have hW1 := summable_chat_lattice_of_row (W := Work.BoseFixR.W1fun v h ℓ) hR hℓ1 hRℓ
    (Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ0 hRchi)
    (Submission.BoseGases.wScaled_g0_nonneg_ae hR hv_nonneg hvrad hv_supp h)
    (Work.BoseFixR.isEven_W1fun h hvrad ℓ)
    (Work.BoseFixR.tsupport_W1fun_subset h hv_supp ℓ)
    (Work.BoseRowsFS.honest_W1_pair_integrable hR hℓ0 hv_nonneg hvrad hv_supp hRchi)
  have hg0 := summable_chat_lattice_of_row (W := Submission.BoseGases.g0 v h) hR hℓ1 hRℓ
    (Submission.BoseGases.g0_integrable hR hv_supp h)
    (Submission.BoseGases.g0_nonneg_ae hR hv_nonneg hvrad hv_supp h)
    (Submission.BoseGases.g0_even hvrad h)
    (tsupport_g0_subset h hv_supp)
    (g0_pair_integrable h hR hv_nonneg hvrad hv_supp)
  exact (hW1.add hg0).congr (fun n => by rw [add_div])

end Work.BoseRowsL.Tails
