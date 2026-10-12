import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseBoxFock.exists_honestModes
import Submission.Work.BoseRowsL.Tails.exists_finset_sum_le_of_summable
import Submission.Work.BoseRowsL.Tails.integrable_chat_g0_sq
import Submission.Work.BoseRowsL.Tails.lattice_energy_summable
import Submission.Work.BoseRowsL.Tails.tendsto_tail_setIntegral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
/-!
# `Work.BoseRowsL.Tails.tailFields` — the tail rows of the honest interface `HonestInterfaceL`

The lemma produces, for every admissible datum, a cube-size function `Ng' ≥ hthr.Ng` such that the
three *tail* fields of `Work.BoseRowsL.HonestInterfaceL` hold (the `cutR` row, the lattice UV-tail
row `tailL` and the continuum UV-tail row `tailC`), with the constant `Cw > 0` supplied by the
caller.

## Proof

Everything is driven by the *choice* of `Ng' μ` large: both tail rows are "small for large cube
size", and `uvRad ℓ N = πN/(2ℓ) → ∞`.

* **Lattice (`tailL`).**  The family `n ↦ (Ŵ₁(k_n)² + ĝ(k_n)²)/‖k_n‖²` is summable
  (`Work.BoseRowsL.Tails.lattice_energy_summable`, from the uniform lattice-versus-continuum
  comparison `Work.BoseRowsFS.lattice_row_aux` applied to `W₁` and to `g₀`), so
  `Work.BoseRowsL.Tails.exists_finset_sum_le_of_summable` supplies a finite set `s₀` outside which
  every finite sub-sum is `≤ ℓ³·Cw²a(R/ℓ)⁴`.  Any finite `S` whose points all lie beyond
  `uvRad (ellH v μ) N`, with `N` large enough that `uvRad` exceeds the largest norm in `s₀`, is
  disjoint from `s₀`, and the row follows.
* **Continuum (`tailC`).**  The integrand `(Ŵ₁² + ĝ²)/(4‖p‖²)` is integrable — the `Ŵ₁` half is
  `Work.BoseFixR.IntegrableChatW1sq` and the `ĝ` half is
  `Work.BoseRowsL.Tails.integrable_chat_g0_sq` — so its tail integrals vanish
  (`Work.BoseRowsL.Tails.tendsto_tail_setIntegral`); again `N` may be taken large.
* **`cutR`.**  `1/R ≤ 2·uvRad (ellH v μ) N` for `N ≥ ℓ/(πR)`.

The `Ng'` is assembled without a case distinction in its *value*: the per-`μ` statement is proved in
the relaxed form "… provided `0 < μ` and `μ a³ ≤ εg`", so that it holds for every real `μ`
(vacuously off the dilute régime), and `Ng' μ := max (hthr.Ng μ) (choose …)`.
-/


noncomputable section
open scoped Real BigOperators Topology
open MeasureTheory Metric Filter
open _root_.BoseGases Submission.BoseGases

namespace Work.BoseRowsL.Tails

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- `uvRad ℓ N` is monotone in the cube size `N` (for `ℓ > 0`). -/
private lemma uvRad_mono {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Monotone fun N : ℕ => Work.BoseBoxFock.uvRad ℓ N := by
  intro N N' hNN'
  show Work.BoseBoxFock.uvRad ℓ N ≤ Work.BoseBoxFock.uvRad ℓ N'
  have h1 : (N : ℝ) ≤ (N' : ℝ) := by exact_mod_cast hNN'
  have hcoef : 0 ≤ 2 * Real.pi / ℓ / 4 := by positivity
  have e1 : Work.BoseBoxFock.uvRad ℓ N = (2 * Real.pi / ℓ / 4) * (N : ℝ) := by
    rw [Work.BoseBoxFock.uvRad]; ring
  have e2 : Work.BoseBoxFock.uvRad ℓ N' = (2 * Real.pi / ℓ / 4) * (N' : ℝ) := by
    rw [Work.BoseBoxFock.uvRad]; ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left h1 hcoef

theorem tailFields {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (R : ℝ) (hR : 0 < R) (hav : 0 < _root_.BoseGases.a v)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (hthr : Work.BoseGateFS.GateThresholds v h fc fu R) (Cw : ℝ) (hCw : 0 < Cw) :
    ∃ Ng' : ℝ → ℕ, (∀ μ, hthr.Ng μ ≤ Ng' μ) ∧
      (∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg →
        1 / R ≤ 2 * Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) (Ng' μ)) ∧
      (∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg → ∀ N : ℕ, Ng' μ ≤ N →
        ∀ S : Finset (Fin 3 → ℤ),
          (∀ n ∈ S, Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N
              < ‖(Work.BoseBoxFock.ellH v μ)⁻¹ • Work.BoseB4.vec n‖) →
          (Work.BoseBoxFock.ellH v μ) ^ (-(3 : ℝ)) * ∑ n ∈ S,
              (Work.BoseFixR.chat (Submission.BoseGases.g0 v h)
                  ((Work.BoseBoxFock.ellH v μ)⁻¹ • Work.BoseB4.vec n) ^ 2
                + Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
                    ((Work.BoseBoxFock.ellH v μ)⁻¹ • Work.BoseB4.vec n) ^ 2)
              / ‖(Work.BoseBoxFock.ellH v μ)⁻¹ • Work.BoseB4.vec n‖ ^ 2
            ≤ Cw ^ 2 * _root_.BoseGases.a v * (R / Work.BoseBoxFock.ellH v μ) ^ 4) ∧
      (∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg → ∀ N : ℕ, Ng' μ ≤ N →
        ((2 * Real.pi) ^ 3)⁻¹ *
            ∫ p in {p : EuclideanSpace ℝ (Fin 3) |
                2 * Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N < ‖p‖},
              (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) p ^ 2
                + Work.BoseFixR.chat (Submission.BoseGases.g0 v h) p ^ 2) / (4 * ‖p‖ ^ 2)
          ≤ Cw ^ 2 * _root_.BoseGases.a v * (R / Work.BoseBoxFock.ellH v μ) ^ 4) := by
  classical
  -- an honest mode family with `N = hthr.Ng μ`
  choose HM hHMN using fun μ : ℝ => Work.BoseBoxFock.exists_honestModes v μ (hthr.Ng μ)
  have hNg : ∀ μ, hthr.Ng μ ≤ (HM μ).N := fun μ => (hHMN μ).ge
  -- the per-μ statement
  have key : ∀ (μ : ℝ) (hμ : 0 < μ) (hμ' : μ * a v ^ 3 ≤ hthr.εg),
      ∃ N₀ : ℕ, hthr.Ng μ ≤ N₀ ∧ (1 / R ≤ 2 * Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N₀) ∧
        (∀ N : ℕ, N₀ ≤ N → ∀ S : Finset (Fin 3 → ℤ),
          (∀ n ∈ S, Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N
              < ‖(Work.BoseBoxFock.ellH v μ)⁻¹ • Work.BoseB4.vec n‖) →
          (Work.BoseBoxFock.ellH v μ) ^ (-(3 : ℝ)) * ∑ n ∈ S,
              (Work.BoseFixR.chat (g0 v h)
                  ((Work.BoseBoxFock.ellH v μ)⁻¹ • Work.BoseB4.vec n) ^ 2
                + Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
                    ((Work.BoseBoxFock.ellH v μ)⁻¹ • Work.BoseB4.vec n) ^ 2)
              / ‖(Work.BoseBoxFock.ellH v μ)⁻¹ • Work.BoseB4.vec n‖ ^ 2
            ≤ Cw ^ 2 * a v * (R / Work.BoseBoxFock.ellH v μ) ^ 4) ∧
        (∀ N : ℕ, N₀ ≤ N →
          ((2 * Real.pi) ^ 3)⁻¹ *
              ∫ p in {p : E3 |
                  2 * Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N < ‖p‖},
                (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) p ^ 2
                  + Work.BoseFixR.chat (g0 v h) p ^ 2) / (4 * ‖p‖ ^ 2)
            ≤ Cw ^ 2 * a v * (R / Work.BoseBoxFock.ellH v μ) ^ 4) := by
    intro μ hμ hμ'
    obtain ⟨hℓ1, -, hRchi, -, -, -⟩ := hthr.dil HM hNg μ hμ hμ'
    have hℓ0 : 0 < Work.BoseBoxFock.ellH v μ := Work.BoseBoxFock.ellH_pos v μ
    have hchi1 : chiR0 ≤ 1 := Work.BoseFixR.Rb5Lin.chiR0_le_one
    have hRℓ : R ≤ Work.BoseBoxFock.ellH v μ := by
      calc R ≤ Work.BoseBoxFock.ellH v μ * chiR0 := hRchi
        _ ≤ Work.BoseBoxFock.ellH v μ * 1 := mul_le_mul_of_nonneg_left hchi1 hℓ0.le
        _ = Work.BoseBoxFock.ellH v μ := mul_one _
    have hb : 0 < Cw ^ 2 * a v * (R / Work.BoseBoxFock.ellH v μ) ^ 4 :=
      mul_pos (mul_pos (pow_pos hCw 2) hav)
        (pow_pos (div_pos hR hℓ0) 4)
    -- ### the lattice family and its summability
    set F : (Fin 3 → ℤ) → ℝ := fun n =>
      ((Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
            (Work.BoseRowsFS.kvec (Work.BoseBoxFock.ellH v μ) n)) ^ 2
        + (Work.BoseFixR.chat (g0 v h) (Work.BoseRowsFS.kvec (Work.BoseBoxFock.ellH v μ) n)) ^ 2)
        / ‖Work.BoseRowsFS.kvec (Work.BoseBoxFock.ellH v μ) n‖ ^ 2 with hFdef
    have hF0 : ∀ n, 0 ≤ F n := by
      intro n
      rw [hFdef]
      exact div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (by positivity)
    have hSumm : Summable F := by
      rw [hFdef]
      exact lattice_energy_summable hR hav hv_nonneg hvrad hv_supp
        (Work.BoseBoxFock.ellH v μ) hℓ1 hRℓ hRchi
    -- ### the escape
    have hε₁ : 0 < (Work.BoseBoxFock.ellH v μ) ^ 3 * (Cw ^ 2 * a v * (R / Work.BoseBoxFock.ellH v μ) ^ 4) :=
      mul_pos (pow_pos hℓ0 3) hb
    obtain ⟨s₀, hs₀⟩ := exists_finset_sum_le_of_summable hSumm hF0 hε₁
    -- ### the lattice threshold
    let Bnd : ℕ := s₀.sup fun n => ⌈‖Work.BoseRowsFS.kvec (Work.BoseBoxFock.ellH v μ) n‖⌉₊
    have hBnd_le : ∀ n ∈ s₀, ‖Work.BoseRowsFS.kvec (Work.BoseBoxFock.ellH v μ) n‖ ≤ (Bnd : ℝ) := by
      intro n hn
      have h1 : ‖Work.BoseRowsFS.kvec (Work.BoseBoxFock.ellH v μ) n‖
          ≤ ((⌈‖Work.BoseRowsFS.kvec (Work.BoseBoxFock.ellH v μ) n‖⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      have h2 : (⌈‖Work.BoseRowsFS.kvec (Work.BoseBoxFock.ellH v μ) n‖⌉₊ : ℕ) ≤ Bnd :=
        Finset.le_sup (s := s₀)
          (f := fun n => ⌈‖Work.BoseRowsFS.kvec (Work.BoseBoxFock.ellH v μ) n‖⌉₊) hn
      exact le_trans h1 (by exact_mod_cast h2)
    obtain ⟨N_lat, hN_lat⟩ : ∃ N_lat : ℕ, ∀ N : ℕ, N_lat ≤ N →
        (Bnd : ℝ) + 1 ≤ Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N := by
      obtain ⟨N₀, hN₀⟩ := exists_nat_ge (2 * (Work.BoseBoxFock.ellH v μ) * ((Bnd : ℝ) + 1) / Real.pi)
      refine ⟨N₀, fun N hN => ?_⟩
      have hN' : (N₀ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hπ : 0 < Real.pi := Real.pi_pos
      have h4 : 0 < 4 * Work.BoseBoxFock.ellH v μ := by linarith
      have h1 : (Bnd : ℝ) + 1 ≤ 2 * Real.pi * (N₀ : ℝ) / (4 * Work.BoseBoxFock.ellH v μ) := by
        rw [le_div_iff₀ h4]
        have h2 : 2 * (Work.BoseBoxFock.ellH v μ) * ((Bnd : ℝ) + 1) / Real.pi ≤ (N₀ : ℝ) := hN₀
        rw [div_le_iff₀ hπ] at h2
        nlinarith [h2]
      have h3 : 2 * Real.pi * (N₀ : ℝ) / (4 * Work.BoseBoxFock.ellH v μ)
          ≤ 2 * Real.pi * (N : ℝ) / (4 * Work.BoseBoxFock.ellH v μ) := by
        have e1 : 2 * Real.pi * (N₀ : ℝ) / (4 * Work.BoseBoxFock.ellH v μ)
            = (2 * Real.pi / (4 * Work.BoseBoxFock.ellH v μ)) * (N₀ : ℝ) := by ring
        have e2 : 2 * Real.pi * (N : ℝ) / (4 * Work.BoseBoxFock.ellH v μ)
            = (2 * Real.pi / (4 * Work.BoseBoxFock.ellH v μ)) * (N : ℝ) := by ring
        rw [e1, e2]
        exact mul_le_mul_of_nonneg_left hN' (by positivity)
      have huv : Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N
          = 2 * Real.pi * (N : ℝ) / (4 * Work.BoseBoxFock.ellH v μ) := by
        rw [Work.BoseBoxFock.uvRad]; ring
      rw [huv]
      linarith [h1, h3]
    -- ### the continuum integrand
    have hIntW : MeasureTheory.Integrable (fun q : E3 =>
        (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) q) ^ 2
          / (2 * ‖q‖ ^ 2)) :=
      Work.BoseFixR.IntegrableChatW1sq h hv_nonneg hvrad hR hℓ0 hv_supp hRchi
    have hIntG : MeasureTheory.Integrable (fun q : E3 =>
        (Work.BoseFixR.chat (g0 v h) q) ^ 2 / (2 * ‖q‖ ^ 2)) :=
      integrable_chat_g0_sq h hR hav hv_nonneg hvrad hv_supp
    have hfpt : ∀ p : E3,
        ((Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) p) ^ 2
            + (Work.BoseFixR.chat (g0 v h) p) ^ 2) / (4 * ‖p‖ ^ 2)
          = (1 / 2) * ((Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) p) ^ 2
              / (2 * ‖p‖ ^ 2))
            + (1 / 2) * ((Work.BoseFixR.chat (g0 v h) p) ^ 2 / (2 * ‖p‖ ^ 2)) := by
      intro p
      rcases eq_or_ne ‖p‖ 0 with h0 | h0
      · simp [h0]
      · have h0' : ‖p‖ ^ 2 ≠ 0 := pow_ne_zero 2 h0
        field_simp
        ring
    have hf : MeasureTheory.Integrable (fun p : E3 =>
        ((Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) p) ^ 2
            + (Work.BoseFixR.chat (g0 v h) p) ^ 2) / (4 * ‖p‖ ^ 2)) := by
      have h0 := (hIntW.const_mul (1 / 2)).add (hIntG.const_mul (1 / 2))
      refine h0.congr (Filter.Eventually.of_forall (fun p => ?_))
      exact (hfpt p).symm
    have hf0 : ∀ᵐ p : E3, 0 ≤ ((Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) p) ^ 2
            + (Work.BoseFixR.chat (g0 v h) p) ^ 2) / (4 * ‖p‖ ^ 2) :=
      Filter.Eventually.of_forall (fun p =>
        div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (by positivity))
    -- ### the tail limit
    obtain ⟨N_cont, hN_cont⟩ : ∃ N_cont : ℕ, ∀ N ≥ N_cont,
        ((2 * Real.pi) ^ 3)⁻¹ *
            ∫ p in {p : E3 | 2 * Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N < ‖p‖},
              ((Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) p) ^ 2
                + (Work.BoseFixR.chat (g0 v h) p) ^ 2) / (4 * ‖p‖ ^ 2)
          ≤ Cw ^ 2 * a v * (R / Work.BoseBoxFock.ellH v μ) ^ 4 := by
      have hc : Tendsto (fun N : ℕ => 2 * Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
          atTop atTop := by
        rw [tendsto_atTop_atTop]
        intro a
        obtain ⟨n₀, hn₀⟩ := exists_nat_ge (a * (Work.BoseBoxFock.ellH v μ) / Real.pi + 1)
        refine ⟨n₀, fun N hN => ?_⟩
        have hN' : (n₀ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
        have huv : 2 * Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N
            = Real.pi * (N : ℝ) / Work.BoseBoxFock.ellH v μ := by
          rw [Work.BoseBoxFock.uvRad]; ring
        rw [huv, le_div_iff₀ hℓ0]
        have hπ : 0 < Real.pi := Real.pi_pos
        have h2 : a * (Work.BoseBoxFock.ellH v μ) / Real.pi + 1 ≤ (n₀ : ℝ) := hn₀
        have h3 : a * (Work.BoseBoxFock.ellH v μ) ≤ (n₀ : ℝ) * Real.pi := by
          have h4 : a * (Work.BoseBoxFock.ellH v μ)
              ≤ (a * (Work.BoseBoxFock.ellH v μ) / Real.pi + 1) * Real.pi := by
            rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hπ), one_mul]
            linarith [hπ]
          exact le_trans h4 (mul_le_mul_of_nonneg_right h2 hπ.le)
        calc a * Work.BoseBoxFock.ellH v μ ≤ (n₀ : ℝ) * Real.pi := h3
          _ ≤ (N : ℝ) * Real.pi := mul_le_mul_of_nonneg_right hN' hπ.le
          _ = Real.pi * (N : ℝ) := by ring
      have htend := tendsto_tail_setIntegral
        (fun p : E3 => ((Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) p) ^ 2
            + (Work.BoseFixR.chat (g0 v h) p) ^ 2) / (4 * ‖p‖ ^ 2)) hf hf0 hc
      have hε : 0 < (2 * Real.pi) ^ 3 * (Cw ^ 2 * a v * (R / Work.BoseBoxFock.ellH v μ) ^ 4) :=
        mul_pos (by positivity) hb
      obtain ⟨N_cont, hNc⟩ := Metric.tendsto_atTop.mp htend
        ((2 * Real.pi) ^ 3 * (Cw ^ 2 * a v * (R / Work.BoseBoxFock.ellH v μ) ^ 4)) hε
      refine ⟨N_cont, fun N hN => ?_⟩
      have h1 : dist (∫ p in {p : E3 |
            2 * Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N < ‖p‖},
            ((Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) p) ^ 2
              + (Work.BoseFixR.chat (g0 v h) p) ^ 2) / (4 * ‖p‖ ^ 2)) 0
          < (2 * Real.pi) ^ 3 * (Cw ^ 2 * a v * (R / Work.BoseBoxFock.ellH v μ) ^ 4) := hNc N hN
      rw [Real.dist_eq, sub_zero] at h1
      have h2 : 0 ≤ ∫ p in {p : E3 |
            2 * Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N < ‖p‖},
            ((Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) p) ^ 2
              + (Work.BoseFixR.chat (g0 v h) p) ^ 2) / (4 * ‖p‖ ^ 2) :=
        setIntegral_nonneg (measurableSet_lt measurable_const continuous_norm.measurable)
          (fun p _ => div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (by positivity))
      rw [abs_of_nonneg h2] at h1
      have h3 : 0 < (2 * Real.pi) ^ 3 := by positivity
      calc ((2 * Real.pi) ^ 3)⁻¹ *
            ∫ p in {p : E3 | 2 * Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N < ‖p‖},
              ((Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) p) ^ 2
                + (Work.BoseFixR.chat (g0 v h) p) ^ 2) / (4 * ‖p‖ ^ 2)
          ≤ ((2 * Real.pi) ^ 3)⁻¹ *
              ((2 * Real.pi) ^ 3 * (Cw ^ 2 * a v * (R / Work.BoseBoxFock.ellH v μ) ^ 4)) :=
            mul_le_mul_of_nonneg_left h1.le (by positivity)
        _ = Cw ^ 2 * a v * (R / Work.BoseBoxFock.ellH v μ) ^ 4 := by
            field_simp
    -- ### the cut threshold
    obtain ⟨N_cut, hN_cut⟩ : ∃ N_cut : ℕ,
        1 / R ≤ 2 * Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N_cut := by
      obtain ⟨N₀, hN₀⟩ := exists_nat_ge ((Work.BoseBoxFock.ellH v μ) / (Real.pi * R))
      refine ⟨N₀, ?_⟩
      have huv : 2 * Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N₀
          = Real.pi * (N₀ : ℝ) / Work.BoseBoxFock.ellH v μ := by
        rw [Work.BoseBoxFock.uvRad]; ring
      rw [huv, le_div_iff₀ hℓ0]
      have h2 : Work.BoseBoxFock.ellH v μ / (Real.pi * R) ≤ (N₀ : ℝ) := hN₀
      have h2' : Work.BoseBoxFock.ellH v μ ≤ (N₀ : ℝ) * (Real.pi * R) := by
        rw [div_le_iff₀ (by positivity : 0 < Real.pi * R)] at h2; exact h2
      have h3 : Work.BoseBoxFock.ellH v μ / R ≤ Real.pi * (N₀ : ℝ) := by
        have h7 : Real.pi * (Work.BoseBoxFock.ellH v μ / (Real.pi * R)) ≤ Real.pi * (N₀ : ℝ) :=
          mul_le_mul_of_nonneg_left h2 Real.pi_pos.le
        have h8 : Real.pi * (Work.BoseBoxFock.ellH v μ / (Real.pi * R))
            = Work.BoseBoxFock.ellH v μ / R := by field_simp
        rwa [h8] at h7
      have h4 : (1 / R) * Work.BoseBoxFock.ellH v μ = Work.BoseBoxFock.ellH v μ / R := by ring
      linarith [h3, h4]
    refine ⟨max (hthr.Ng μ) (max N_lat (max N_cont N_cut)), le_max_left _ _, ?_, ?_, ?_⟩
    · -- `cutR`
      have h1 : N_cut ≤ max (hthr.Ng μ) (max N_lat (max N_cont N_cut)) :=
        le_trans (le_trans (le_max_right N_cont N_cut) (le_max_right N_lat (max N_cont N_cut)))
          (le_max_right (hthr.Ng μ) (max N_lat (max N_cont N_cut)))
      have h2 := uvRad_mono hℓ0 h1
      linarith [hN_cut, h2]
    · -- `tailL`
      intro N hN S hS
      have hNlat_le : N_lat ≤ N :=
        le_trans (le_trans (le_max_left N_lat (max N_cont N_cut))
          (le_max_right (hthr.Ng μ) (max N_lat (max N_cont N_cut)))) hN
      have huvN : (Bnd : ℝ) + 1 ≤ Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N :=
        hN_lat N hNlat_le
      have hdisj : Disjoint S s₀ := by
        rw [Finset.disjoint_iff_ne]
        intro a ha b hb hab
        have h1 : Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N
            < ‖Work.BoseRowsFS.kvec (Work.BoseBoxFock.ellH v μ) a‖ := by
          have h := hS a ha
          rw [← Work.BoseRowsFS.kvec_eq] at h
          exact h
        have h2 : ‖Work.BoseRowsFS.kvec (Work.BoseBoxFock.ellH v μ) a‖ ≤ (Bnd : ℝ) := by
          rw [hab]
          exact hBnd_le b hb
        linarith
      have hbnd := hs₀ S hdisj
      -- transfer to the target's spelling
      have hsum : ∑ n ∈ S,
            (Work.BoseFixR.chat (g0 v h)
                ((Work.BoseBoxFock.ellH v μ)⁻¹ • Work.BoseB4.vec n) ^ 2
              + Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
                  ((Work.BoseBoxFock.ellH v μ)⁻¹ • Work.BoseB4.vec n) ^ 2)
            / ‖(Work.BoseBoxFock.ellH v μ)⁻¹ • Work.BoseB4.vec n‖ ^ 2
          = ∑ n ∈ S, F n := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [hFdef]
        dsimp only
        rw [Work.BoseRowsFS.kvec_eq]
        ring
      rw [hsum]
      have h4 : (Work.BoseBoxFock.ellH v μ) ^ (-(3 : ℝ)) * ∑ n ∈ S, F n
          ≤ (Work.BoseBoxFock.ellH v μ) ^ (-(3 : ℝ))
              * ((Work.BoseBoxFock.ellH v μ) ^ 3 * (Cw ^ 2 * a v * (R / Work.BoseBoxFock.ellH v μ) ^ 4)) :=
        mul_le_mul_of_nonneg_left hbnd (by positivity)
      refine le_trans h4 (le_of_eq ?_)
      have hbase : (Work.BoseBoxFock.ellH v μ) ^ (-(3 : ℝ))
          = ((Work.BoseBoxFock.ellH v μ) ^ 3)⁻¹ := by
        rw [Real.rpow_neg hℓ0.le]
        norm_num
      rw [hbase]
      exact inv_mul_cancel_left₀ (ne_of_gt (pow_pos hℓ0 3))
        (Cw ^ 2 * a v * (R / Work.BoseBoxFock.ellH v μ) ^ 4)
    · -- `tailC`
      intro N hN
      have hNcont_le : N_cont ≤ N :=
        le_trans (le_trans (le_trans (le_max_left N_cont N_cut) (le_max_right N_lat (max N_cont N_cut)))
          (le_max_right (hthr.Ng μ) (max N_lat (max N_cont N_cut)))) hN
      exact hN_cont N hNcont_le
  -- ### the global key (no `if` in the value of `Ng'`)
  have gkey : ∀ μ : ℝ, ∃ N₀ : ℕ, hthr.Ng μ ≤ N₀ ∧
      (0 < μ → μ * a v ^ 3 ≤ hthr.εg →
        1 / R ≤ 2 * Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N₀) ∧
      (0 < μ → μ * a v ^ 3 ≤ hthr.εg → ∀ N : ℕ, N₀ ≤ N → ∀ S : Finset (Fin 3 → ℤ),
          (∀ n ∈ S, Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N
              < ‖(Work.BoseBoxFock.ellH v μ)⁻¹ • Work.BoseB4.vec n‖) →
          (Work.BoseBoxFock.ellH v μ) ^ (-(3 : ℝ)) * ∑ n ∈ S,
              (Work.BoseFixR.chat (g0 v h)
                  ((Work.BoseBoxFock.ellH v μ)⁻¹ • Work.BoseB4.vec n) ^ 2
                + Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
                    ((Work.BoseBoxFock.ellH v μ)⁻¹ • Work.BoseB4.vec n) ^ 2)
              / ‖(Work.BoseBoxFock.ellH v μ)⁻¹ • Work.BoseB4.vec n‖ ^ 2
            ≤ Cw ^ 2 * a v * (R / Work.BoseBoxFock.ellH v μ) ^ 4) ∧
      (0 < μ → μ * a v ^ 3 ≤ hthr.εg → ∀ N : ℕ, N₀ ≤ N →
          ((2 * Real.pi) ^ 3)⁻¹ *
              ∫ p in {p : E3 |
                  2 * Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N < ‖p‖},
                (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) p ^ 2
                  + Work.BoseFixR.chat (g0 v h) p ^ 2) / (4 * ‖p‖ ^ 2)
            ≤ Cw ^ 2 * a v * (R / Work.BoseBoxFock.ellH v μ) ^ 4) := by
    intro μ
    by_cases h : 0 < μ ∧ μ * a v ^ 3 ≤ hthr.εg
    · obtain ⟨N₀, h1, h2, h3, h4⟩ := key μ h.1 h.2
      exact ⟨N₀, h1, fun _ _ => h2, fun _ _ => h3, fun _ _ => h4⟩
    · refine ⟨hthr.Ng μ, le_rfl, ?_, ?_, ?_⟩
      · intro hμ hμ'; exact absurd ⟨hμ, hμ'⟩ h
      · intro hμ hμ'; exact absurd ⟨hμ, hμ'⟩ h
      · intro hμ hμ'; exact absurd ⟨hμ, hμ'⟩ h
  refine ⟨fun μ => max (hthr.Ng μ) (Classical.choose (gkey μ)), ?_, ?_, ?_, ?_⟩
  · intro μ
    exact le_max_left _ _
  · intro μ hμ hμ'
    have h2 := (Classical.choose_spec (gkey μ)).2.1 hμ hμ'
    have h3 : Classical.choose (gkey μ) ≤ max (hthr.Ng μ) (Classical.choose (gkey μ)) :=
      le_max_right _ _
    have h4 := uvRad_mono (Work.BoseBoxFock.ellH_pos v μ) h3
    linarith [h2, h4]
  · intro μ hμ hμ' N hN S hS
    exact (Classical.choose_spec (gkey μ)).2.2.1 hμ hμ' N (le_trans (le_max_right _ _) hN) S hS
  · intro μ hμ hμ' N hN
    exact (Classical.choose_spec (gkey μ)).2.2.2 hμ hμ' N (le_trans (le_max_right _ _) hN)

end Work.BoseRowsL.Tails
