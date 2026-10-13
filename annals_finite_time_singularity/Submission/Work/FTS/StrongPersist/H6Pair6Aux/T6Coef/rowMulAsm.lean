/-
# `T6Coef/rowMulAsm` — the assembly of the level-six `A · f` coefficient row

This module assembles the slot pairing `slotPairing ρ a b (A · f) f` from the per-summand
bounds of the Leibniz expansion

  `D_z^bD_θ^a (A·f) = Σ_{a₁≤a} Σ_{b₁≤b} C(a,a₁) C(b,b₁) (D_z^{b₁}D_θ^{a₁}A)(D_z^{b-b₁}D_θ^{a-a₁}f)`,

exactly as `T6Gen/RowAsm.lean` assembles the `D_z`-row.  The three ingredients are taken as
*hypotheses* here, so that this file is independent of the three delegated lemmas:

* `hExp`   — the integral Leibniz expansion (`mulExpansion`),
* `hSmall` — the per-summand bound for `a₁ + b₁ ≤ 2` (`mulTermSmall`),
* `hLarge` — the per-summand bound for `3 ≤ a₁ + b₁` (`mulTermLarge`).

The finite-sum bookkeeping (`2^a·2^b ≤ 64` for `a + b ≤ 6`) and the final arithmetic are copied
verbatim from `RowAsm`.
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.HardDefs
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.OpenTwins
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 3200000

set_option quotPrecheck false in
local notation "IPM" => ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
  (MeasureTheory.volume.restrict Work.Spaces.Iθ))

/-! ## The pointwise Leibniz majorant -/

/-- **The pointwise majorant of a single slot pairing.**  For `SmoothOpen` functions and a
nonnegative weight, the weighted product `ρ·(D_z^bD_θ^a(f·g))·(D_z^bD_θ^a g)` is dominated by
the Leibniz sum of the products of the absolute values of the individual slots. -/
theorem abs_mixed_mul_le_sum {f g ρ : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (a b : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hρ : 0 ≤ ρ z θ) :
    ρ z θ * |Work.Spaces.mixed b a (fun z θ => f z θ * g z θ) z θ
        * Work.Spaces.mixed b a g z θ|
      ≤ ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
          ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * (ρ z θ * |Work.Spaces.mixed b₁ a₁ f z θ|
                * |Work.Spaces.mixed (b - b₁) (a - a₁) g z θ|
                * |Work.Spaces.mixed b a g z θ|) := by
  have hX := Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed b a f g hf hg z θ hz hθ0 hθ1
  have habs : |Work.Spaces.mixed b a (fun z θ => f z θ * g z θ) z θ|
      ≤ ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
          ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * (|Work.Spaces.mixed b₁ a₁ f z θ|
                * |Work.Spaces.mixed (b - b₁) (a - a₁) g z θ|) := by
    rw [hX]
    calc |∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
            ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
              * (Work.Spaces.mixed b₁ a₁ f z θ
                  * Work.Spaces.mixed (b - b₁) (a - a₁) g z θ)|
        ≤ ∑ a₁ ∈ Finset.range (a + 1),
            |∑ b₁ ∈ Finset.range (b + 1),
              ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
                * (Work.Spaces.mixed b₁ a₁ f z θ
                    * Work.Spaces.mixed (b - b₁) (a - a₁) g z θ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
            |((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
              * (Work.Spaces.mixed b₁ a₁ f z θ
                  * Work.Spaces.mixed (b - b₁) (a - a₁) g z θ)| :=
          Finset.sum_le_sum fun a₁ _ => Finset.abs_sum_le_sum_abs _ _
      _ = ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
            ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
              * (|Work.Spaces.mixed b₁ a₁ f z θ|
                  * |Work.Spaces.mixed (b - b₁) (a - a₁) g z θ|) := by
          refine Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun b₁ _ => ?_
          rw [abs_mul, abs_mul, abs_mul]
          rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (a.choose a₁ : ℝ)),
              abs_of_nonneg (by positivity : (0 : ℝ) ≤ (b.choose b₁ : ℝ))]
          try ring_nf
  calc ρ z θ * |Work.Spaces.mixed b a (fun z θ => f z θ * g z θ) z θ
        * Work.Spaces.mixed b a g z θ|
      = ρ z θ * |Work.Spaces.mixed b a (fun z θ => f z θ * g z θ) z θ|
        * |Work.Spaces.mixed b a g z θ| := by rw [abs_mul]; ring
    _ ≤ ρ z θ * (∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
          ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * (|Work.Spaces.mixed b₁ a₁ f z θ|
                * |Work.Spaces.mixed (b - b₁) (a - a₁) g z θ|))
        * |Work.Spaces.mixed b a g z θ| := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left habs hρ) (abs_nonneg _)
    _ = ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
          ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * (ρ z θ * |Work.Spaces.mixed b₁ a₁ f z θ|
                * |Work.Spaces.mixed (b - b₁) (a - a₁) g z θ|
                * |Work.Spaces.mixed b a g z θ|) := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a₁ _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun b₁ _ => ?_
        ring

/-! ## The assembly -/

/-- **The level-six `A · f` coefficient row**, assembled from the Leibniz expansion and the two
per-summand bounds. -/
theorem rowMulAsm
    (hExp : ∀ {f g : ℝ → ℝ → ℝ} (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.EllipticEst.SmoothOpen g →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
        * Work.Spaces.mixed b a (fun z θ => f z θ * g z θ) p.1 p.2
        * Work.Spaces.mixed b a g p.1 p.2) IPM →
      (∀ a₁ ≤ a, ∀ b₁ ≤ b, MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
        * Work.Spaces.mixed b₁ a₁ f p.1 p.2
        * Work.Spaces.mixed (b - b₁) (a - a₁) g p.1 p.2
        * Work.Spaces.mixed b a g p.1 p.2) IPM) →
      Work.FTS.TransportS.slotPairing ρ a b (fun z θ => f z θ * g z θ) g
        = ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
            ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
              * (∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ f p.1 p.2
                  * Work.Spaces.mixed (b - b₁) (a - a₁) g p.1 p.2
                  * Work.Spaces.mixed b a g p.1 p.2 ∂IPM))
    (hSmall : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
      ∀ (A f : Fn) (K0 K4 K6 M : ℝ) (a b a₁ b₁ : ℕ) (ρ : ℝ → ℝ → ℝ),
        CoefData α A K0 K4 K6 → DatData α f M →
        a₁ + b₁ ≤ 2 → a₁ ≤ a → b₁ ≤ b → a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
        MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
            * Work.Spaces.mixed b₁ a₁ A p.1 p.2
            * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2) IPM ∧
        |∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
              * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
              * Work.Spaces.mixed b a f p.1 p.2 ∂IPM|
          ≤ C * α ^ (-(3 : ℝ))
              * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
                 + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)))
    (hLarge : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
      ∀ (A f : Fn) (K0 K4 K6 M : ℝ) (a b a₁ b₁ : ℕ) (ρ : ℝ → ℝ → ℝ),
        CoefData α A K0 K4 K6 → DatData α f M →
        3 ≤ a₁ + b₁ → a₁ ≤ a → b₁ ≤ b → a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
        MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
            * Work.Spaces.mixed b₁ a₁ A p.1 p.2
            * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2) IPM ∧
        |∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
              * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
              * Work.Spaces.mixed b a f p.1 p.2 ∂IPM|
          ≤ C * α ^ (-(3 : ℝ))
              * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
                 + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f))) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
      ∀ (A f : Fn) (K0 K4 K6 M : ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
        CoefData α A K0 K4 K6 → DatData α f M → a + b ≤ 6 →
        Work.FTS.TransportS.IsLeafW α a ρ →
        |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => A z θ * f z θ) f|
          ≤ C * α ^ (-(3 : ℝ))
              * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
                 + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := by
  obtain ⟨Ce, hCep, hsmall⟩ := hSmall
  obtain ⟨Cl, hClp, hlarge⟩ := hLarge
  have hC0 : (0 : ℝ) < max Ce Cl := lt_of_lt_of_le hCep (le_max_left _ _)
  refine ⟨64 * max Ce Cl + 1, by positivity, ?_⟩
  intro α hα A f K0 K4 K6 M a b ρ hcoef hdat hab hleaf
  have hAsm : Work.FTS.EllipticEst.SmoothOpen A := hcoef.sm
  have hA4 : Work.Spaces.HkMem α 4 A := hcoef.h4
  have hA6 : Work.Spaces.HkMem α 6 A := hcoef.h6
  have hAval : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ K0 := hcoef.val
  have hAn4 : Work.FTS.Nonlin.Xn α A ≤ K4 := hcoef.n4
  have hAn6 : Work.Spaces.HkNorm α 6 A ≤ K6 := hcoef.n6
  have hfSm : Work.FTS.EllipticEst.SmoothOpen f := hdat.sm
  have hf6 : Work.Spaces.HkMem α 6 f := hdat.h6
  have hf7 : Work.Spaces.HkMem α 7 f := hdat.h7
  have hfVanish : Work.Spaces.VanishTheta f := hdat.vanish
  have hfAxis : ∀ θ ∈ Work.Spaces.Iθ, f 0 θ = 0 ∧ Work.Spaces.pz f 0 θ = 0 := hdat.axis
  have hfBdd : Work.FTS.Nonlin.Xn α f ≤ M := hdat.bdd
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hK0 : 0 ≤ K0 := le_trans (abs_nonneg (A 1 1))
    (hAval 1 1 (by norm_num) (by norm_num) (by linarith [Real.pi_gt_three]))
  have hK4 : 0 ≤ K4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 A) hAn4
  have hK6 : 0 ≤ K6 := le_trans (Work.Spaces.HkNorm_nonneg α 6 A) hAn6
  have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hfBdd
  have hS0 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hN0 : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
  have hα3pos : 0 < α ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos hα0 _
  set RHS : ℝ := (1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
      + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) with hRHSdef
  have hRHS0 : 0 ≤ RHS := by
    rw [hRHSdef]
    refine add_nonneg (mul_nonneg (by linarith) (by linarith)) ?_
    exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  set C0 : ℝ := max Ce Cl with hC0def
  set Kv : ℝ := C0 * α ^ (-(3 : ℝ)) * RHS with hKvdef
  have hKv0 : 0 ≤ Kv := by
    rw [hKvdef]
    exact mul_nonneg (mul_nonneg (le_of_lt hC0) (le_of_lt hα3pos)) hRHS0
  -- the per-summand integrability and bounds
  have hterm : ∀ a₁ b₁ : ℕ, a₁ ≤ a → b₁ ≤ b → MeasureTheory.Integrable
      (fun p : ℝ × ℝ => ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
        * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
        * Work.Spaces.mixed b a f p.1 p.2) IPM ∧
      |∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
            * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2 ∂IPM| ≤ Kv := by
    intro a₁ b₁ ha₁ hb₁
    have hle : ∀ Cc : ℝ, Cc ≤ C0 →
        Cc * α ^ (-(3 : ℝ)) * RHS ≤ Kv := by
      intro Cc hCc
      rw [hKvdef, hC0def]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCc (le_of_lt hα3pos)) hRHS0
    by_cases hp : a₁ + b₁ ≤ 2
    · obtain ⟨hint, hbd⟩ :=
        hsmall α hα A f K0 K4 K6 M a b a₁ b₁ ρ hcoef hdat hp ha₁ hb₁ hab hleaf
      exact ⟨hint, le_trans hbd (hle Ce (le_max_left _ _))⟩
    · have hp3 : 3 ≤ a₁ + b₁ := by omega
      obtain ⟨hint, hbd⟩ :=
        hlarge α hα A f K0 K4 K6 M a b a₁ b₁ ρ hcoef hdat hp3 ha₁ hb₁ hab hleaf
      exact ⟨hint, le_trans hbd (hle Cl (le_max_right _ _))⟩
  have hint : ∀ a₁ : ℕ, a₁ ≤ a → ∀ b₁ : ℕ, b₁ ≤ b → MeasureTheory.Integrable
      (fun p : ℝ × ℝ => ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
        * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
        * Work.Spaces.mixed b a f p.1 p.2) IPM :=
    fun a₁ ha₁ b₁ hb₁ => (hterm a₁ b₁ ha₁ hb₁).1
  have hbd : ∀ a₁ : ℕ, a₁ ≤ a → ∀ b₁ : ℕ, b₁ ≤ b →
      |∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
            * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2 ∂IPM| ≤ Kv :=
    fun a₁ ha₁ b₁ hb₁ => (hterm a₁ b₁ ha₁ hb₁).2
  -- the majorant
  have hmaj : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
        ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
          * (ρ p.1 p.2 * |Work.Spaces.mixed b₁ a₁ A p.1 p.2|
              * |Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2|
              * |Work.Spaces.mixed b a f p.1 p.2|)) IPM := by
    refine MeasureTheory.integrable_finset_sum _ fun a₁ ha₁ => ?_
    refine MeasureTheory.integrable_finset_sum _ fun b₁ hb₁ => ?_
    have ha₁' : a₁ ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha₁)
    have hb₁' : b₁ ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb₁)
    refine (((hint a₁ ha₁' b₁ hb₁').abs).const_mul
      ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))).congr ?_
    filter_upwards [Work.FTS.TransportS.ae_of_forall_Qd (P := fun p : ℝ × ℝ =>
        ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * |ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
                * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
                * Work.Spaces.mixed b a f p.1 p.2|
          = ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
              * (ρ p.1 p.2 * |Work.Spaces.mixed b₁ a₁ A p.1 p.2|
                  * |Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2|
                  * |Work.Spaces.mixed b a f p.1 p.2|))
      (fun z θ hz hθ0 hθ1 => by
        simp only [abs_mul,
          abs_of_nonneg (Work.FTS.TransportS.T3SlotAux.IsLeafW.nonneg hleaf z
            ⟨le_of_lt hθ0, le_of_lt hθ1⟩)])] with p hp
    exact hp
  -- integrability of the left-hand integrand
  have hXY : MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
      * Work.Spaces.mixed b a (fun z θ => A z θ * f z θ) p.1 p.2
      * Work.Spaces.mixed b a f p.1 p.2) IPM := by
    refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
    · have hcont : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2
          * Work.Spaces.mixed b a (fun z θ => A z θ * f z θ) p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
        have hρcont : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
          rcases hleaf with h | h | ⟨-, h⟩
          · subst h
            simpa [Work.FTS.TransportS.leafEta, Work.FTS.TransportS.SlotT2.canonW] using
              Work.FTS.TransportS.SlotT2.continuousOn_canonW Work.Spaces.eta
          · subst h
            simpa [Work.FTS.TransportS.leafOne, Work.FTS.TransportS.SlotT2.canonW] using
              Work.FTS.TransportS.SlotT2.continuousOn_canonW 0
          · subst h
            simpa [Work.FTS.TransportS.leafGam, Work.FTS.TransportS.SlotT2.canonW] using
              Work.FTS.TransportS.SlotT2.continuousOn_canonW (Work.Spaces.gam α)
        have hXcont : ContinuousOn (fun p : ℝ × ℝ =>
            Work.Spaces.mixed b a (fun z θ => A z θ * f z θ) p.1 p.2)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
          have hpt : ∀ p ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2),
              Work.Spaces.mixed b a (fun z θ => A z θ * f z θ) p.1 p.2
                = ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
                    ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
                      * (Work.Spaces.mixed b₁ a₁ A p.1 p.2
                          * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2) :=
            fun p hp =>
              Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed b a A f hAsm hfSm
                p.1 p.2 hp.1 hp.2.1 hp.2.2
          refine ContinuousOn.congr ?_ hpt
          refine continuousOn_finset_sum _ fun a₁ _ => ?_
          refine continuousOn_finset_sum _ fun b₁ _ => ?_
          refine ContinuousOn.const_mul ?_ _
          exact ((Work.FTS.StrongPersist.N6Trans.Hon.continuousOn_mixed_Qd_open hAsm b₁ a₁).mul
            (Work.FTS.StrongPersist.N6Trans.Hon.continuousOn_mixed_Qd_open hfSm
              (b - b₁) (a - a₁)))
        exact (hρcont.mul hXcont).mul
          (Work.FTS.StrongPersist.N6Trans.Hon.continuousOn_mixed_Qd_open hfSm b a)
      exact Work.Spaces.aesm_of_continuousOn_Qd _ hcont
    · have hpt : ∀ᵐ p ∂IPM, ‖ρ p.1 p.2
            * Work.Spaces.mixed b a (fun z θ => A z θ * f z θ) p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2‖
          ≤ ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
              ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
                * (ρ p.1 p.2 * |Work.Spaces.mixed b₁ a₁ A p.1 p.2|
                    * |Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2|
                    * |Work.Spaces.mixed b a f p.1 p.2|) :=
        Work.FTS.TransportS.ae_of_forall_Qd fun z θ hz hθ0 hθ1 => by
          rw [Real.norm_eq_abs]
          have hρnn : 0 ≤ ρ z θ :=
            Work.FTS.TransportS.T3SlotAux.IsLeafW.nonneg hleaf z ⟨le_of_lt hθ0, le_of_lt hθ1⟩
          have hlhs : |ρ z θ * Work.Spaces.mixed b a (fun z θ => A z θ * f z θ) z θ
                * Work.Spaces.mixed b a f z θ|
              = ρ z θ * |Work.Spaces.mixed b a (fun z θ => A z θ * f z θ) z θ
                * Work.Spaces.mixed b a f z θ| := by
            rw [show ρ z θ * Work.Spaces.mixed b a (fun z θ => A z θ * f z θ) z θ
                  * Work.Spaces.mixed b a f z θ
                = ρ z θ * (Work.Spaces.mixed b a (fun z θ => A z θ * f z θ) z θ
                  * Work.Spaces.mixed b a f z θ) from by ring,
              abs_mul, abs_of_nonneg hρnn]
          rw [hlhs]
          exact abs_mixed_mul_le_sum hAsm hfSm a b hz hθ0 hθ1 hρnn
      filter_upwards [hpt] with p hp
      exact hp
  rw [hExp a b ρ hAsm hfSm hXY hint]
  have hbnd : ∀ a₁ b₁ : ℕ, a₁ ≤ a → b₁ ≤ b →
      |((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
        * (∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
            * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2 ∂IPM)|
        ≤ ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ)) * Kv := by
    intro a₁ b₁ ha₁ hb₁
    rw [abs_mul, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hbd a₁ ha₁ b₁ hb₁)
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hbinom : (∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
      ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))) = (2 : ℝ) ^ a * (2 : ℝ) ^ b := by
    rw [← Finset.sum_mul_sum]
    congr 1
    · rw [← Nat.cast_sum, Nat.sum_range_choose]; push_cast; ring
    · rw [← Nat.cast_sum, Nat.sum_range_choose]; push_cast; ring
  have hpow : (2 : ℝ) ^ a * (2 : ℝ) ^ b ≤ 64 := by
    rw [← pow_add]
    calc (2 : ℝ) ^ (a + b) ≤ (2 : ℝ) ^ 6 := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = 64 := by norm_num
  have hmain : |∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
        ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
          * (∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
              * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
              * Work.Spaces.mixed b a f p.1 p.2 ∂IPM)| ≤ 64 * Kv := by
    have h1 : |∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
          ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
            * (∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
                * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
                * Work.Spaces.mixed b a f p.1 p.2 ∂IPM)|
        ≤ ∑ a₁ ∈ Finset.range (a + 1), |∑ b₁ ∈ Finset.range (b + 1),
            ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
              * (∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
                  * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
                  * Work.Spaces.mixed b a f p.1 p.2 ∂IPM)| :=
          Finset.abs_sum_le_sum_abs _ _
    have h2 : (∑ a₁ ∈ Finset.range (a + 1), |∑ b₁ ∈ Finset.range (b + 1),
            ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))
              * (∫ p, ρ p.1 p.2 * Work.Spaces.mixed b₁ a₁ A p.1 p.2
                  * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
                  * Work.Spaces.mixed b a f p.1 p.2 ∂IPM)|)
        ≤ ∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
            ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ)) * Kv := by
      refine Finset.sum_le_sum fun a₁ ha₁ => ?_
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      exact Finset.sum_le_sum fun b₁ hb₁ => hbnd a₁ b₁
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha₁))
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb₁))
    have h3 : (∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
            ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ)) * Kv)
        = (∑ a₁ ∈ Finset.range (a + 1), ∑ b₁ ∈ Finset.range (b + 1),
            ((a.choose a₁ : ℝ) * (b.choose b₁ : ℝ))) * Kv := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun a₁ _ => ?_
      rw [Finset.sum_mul]
    refine (h1.trans h2).trans ?_
    rw [h3, hbinom]
    exact mul_le_mul_of_nonneg_right hpow hKv0
  refine le_trans hmain ?_
  have hα3R0 : 0 ≤ α ^ (-(3 : ℝ)) * RHS := mul_nonneg (le_of_lt hα3pos) hRHS0
  have hstep : (64 : ℝ) * Kv = (64 * C0) * (α ^ (-(3 : ℝ)) * RHS) := by
    rw [hKvdef]; ring
  rw [hstep, hC0def]
  have h2 : (64 * max Ce Cl) * (α ^ (-(3 : ℝ)) * RHS)
      ≤ (64 * max Ce Cl + 1) * (α ^ (-(3 : ℝ)) * RHS) :=
    mul_le_mul_of_nonneg_right (by linarith) hα3R0
  have h3 : (64 * max Ce Cl + 1) * (α ^ (-(3 : ℝ)) * RHS)
      = (64 * max Ce Cl + 1) * α ^ (-(3 : ℝ)) * RHS := by ring
  rw [h3] at h2
  exact h2

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef
