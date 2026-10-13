/-
# The four coercivity estimates of the clean operator `Lhat`

The four pairings of `H1IP` are bounded below by the corresponding weighted energies, up to the
explicit error terms of `Assembly.lean`:

* `est_A` — the `η`-weighted `D_z`-pairing, with the `D_z`-commutator defect `Ê₂f` handled by
  Cauchy–Schwarz (`Work.Coercivity.sq_integral_mul_le`) and its pointwise bound
  `|Ê₂f| ≤ (2|f| + 3|D_θf|)/4`;
* `est_B` — the `η`-weighted `L²`-pairing: the paper's identity `(LW)` in the interior class
  (`wip_L_self_Q`) plus the transport bound `wip_transport_le_Q` with `|η - 1| = 1/100`;
* `est_C` — the plain `L²`-pairing: `(LW)` plus Cauchy–Schwarz for the transport term;
* `est_D` — the `γ`-weighted `D_θ`-pairing: `D_θ` commutes with `Lhat` **exactly**
  (`Work.FTS.CoercivityFix.LhatCalc.Dth_Lhat`), so the same two inputs apply with
  `|γ - 1| = α/10`.

All the integrability certificates come from `IntPkg_Q`; the boundary limits of the two
one-dimensional integrations by parts come from `BdryTraces` (with the `η`-exponent limits
deduced from the `γ`-exponent ones via `sin(2θ)^{1-η} = sin(2θ)^{γ-η}·sin(2θ)^{1-γ}`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.CoercivityFix.Coer1.Defs
import Submission.Work.FTS.CoercivityFix.Coer1.HkSqOne
import Submission.Work.FTS.CoercivityFix.Coer1.zIBP
import Submission.Work.FTS.CoercivityFix.Coer1.thetaIBP
import Submission.Work.FTS.CoercivityFix.Coer1.IntFacts
import Submission.Work.FTS.CoercivityFix.LhatCalc.Dth_Lhat
import Submission.Work.FTS.CoercivityFix.LhatCalc.Dz_Lhat
import Submission.Work.Coercivity.wip_Aop_ge
import Submission.Work.Coercivity.sq_integral_mul_le
import Submission.Work.FTS.H2.STBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Tools -/

theorem ae_restrict_Iz_pos : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
  rw [MeasureTheory.ae_restrict_iff (p := fun z => 0 < z) measurableSet_Ioi,
    MeasureTheory.ae_iff]
  have hset : {z : ℝ | ¬ (z ∈ Work.Spaces.Iz → 0 < z)} = {0} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Work.Spaces.Iz, Set.mem_Ici, not_imp]
    constructor
    · rintro ⟨h1, h2⟩; exact le_antisymm (not_lt.mp h2) h1
    · intro h; rw [h]; exact ⟨le_refl 0, lt_irrefl 0⟩
  rw [hset, Real.volume_singleton]

/-- The `wip` of a difference splits, under the two integrability certificates. -/
theorem wip_sub_left {ρ A B C : Fn}
    (hA : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => A z θ * C z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hB : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => B z θ * C z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Work.Coercivity.wip ρ (fun z θ => A z θ - B z θ) C
      = Work.Coercivity.wip ρ A C - Work.Coercivity.wip ρ B C := by
  have hA' : MeasureTheory.Integrable (fun p : ℝ × ℝ => A p.1 p.2 * C p.1 p.2 * ρ p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [iz_prod_restrict]; exact hA
  have hB' : MeasureTheory.Integrable (fun p : ℝ × ℝ => B p.1 p.2 * C p.1 p.2 * ρ p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [iz_prod_restrict]; exact hB
  have hAB : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (A z θ - B z θ) * C z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    rw [MeasureTheory.IntegrableOn, ← iz_prod_restrict]
    refine (hA'.sub hB').congr (Filter.Eventually.of_forall (fun p => ?_))
    rcases p with ⟨z, θ⟩
    simp only [Pi.sub_apply, Function.uncurry_apply_pair]
    ring
  rw [Work.Coercivity.wip_eq_integral_prod ρ (fun z θ => A z θ - B z θ) C hAB,
    Work.Coercivity.wip_eq_integral_prod ρ A C hA,
    Work.Coercivity.wip_eq_integral_prod ρ B C hB]
  rw [show (∫ p, (A p.1 p.2 - B p.1 p.2) * C p.1 p.2 * ρ p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = ∫ p, (A p.1 p.2 * C p.1 p.2 * ρ p.1 p.2 - B p.1 p.2 * C p.1 p.2 * ρ p.1 p.2)
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) from
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => by
      rcases p with ⟨z, θ⟩; ring))]
  rw [MeasureTheory.integral_sub hA' hB']

/-- `En η u ≤ En (gam α) u`. -/
theorem En_eta_le_En_gam (α : ℝ) (hα : 0 < α) (u : Fn)
    (h1 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2 * Work.Spaces.w z ^ 2 * sig Work.Spaces.eta θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (h2 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ =>
        u z θ ^ 2 * Work.Spaces.w z ^ 2 * sig (Work.Spaces.gam α) θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    En Work.Spaces.eta u ≤ En (Work.Spaces.gam α) u := by
  have h1' : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => u p.1 p.2 ^ 2 * Work.Spaces.w p.1 ^ 2 * sig Work.Spaces.eta p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [iz_prod_restrict]; exact h1
  have h2' : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => u p.1 p.2 ^ 2 * Work.Spaces.w p.1 ^ 2 * sig (Work.Spaces.gam α) p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [iz_prod_restrict]; exact h2
  have e1 : En Work.Spaces.eta u = ∫ p : ℝ × ℝ,
      u p.1 p.2 ^ 2 * Work.Spaces.w p.1 ^ 2 * sig Work.Spaces.eta p.2
      ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (MeasureTheory.integral_prod (fun p : ℝ × ℝ =>
      u p.1 p.2 ^ 2 * Work.Spaces.w p.1 ^ 2 * sig Work.Spaces.eta p.2) h1').symm
  have e2 : En (Work.Spaces.gam α) u = ∫ p : ℝ × ℝ,
      u p.1 p.2 ^ 2 * Work.Spaces.w p.1 ^ 2 * sig (Work.Spaces.gam α) p.2
      ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (MeasureTheory.integral_prod (fun p : ℝ × ℝ =>
      u p.1 p.2 ^ 2 * Work.Spaces.w p.1 ^ 2 * sig (Work.Spaces.gam α) p.2) h2').symm
  rw [e1, e2]
  refine MeasureTheory.integral_mono_ae h1' h2' ?_
  filter_upwards [ae_prod_snd_mem measurableSet_Icc
    (MeasureTheory.ae_restrict_mem measurableSet_Icc)] with p hp
  exact mul_le_mul_of_nonneg_left (sig_eta_le_sig_gam_Iθ α hα hp)
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The `γ`-weight is at least `1` on the open angular interval. -/
theorem one_le_sig_gam (α : ℝ) (hα : 0 < α) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    1 ≤ sig (Work.Spaces.gam α) θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hgam : 0 < Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have h := Real.rpow_le_rpow_of_exponent_ge hs hs1 (show -(Work.Spaces.gam α) ≤ -(0 : ℝ) by
    linarith)
  rw [sig]
  simpa using h

/-- `EDthW u ≤ En (gam α) (D_θ u)`. -/
theorem EDthW_le_En_gam (α : ℝ) (hα : 0 < α) (u : Fn)
    (h1 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.Dth u z θ) ^ 2 * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (h2 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.Dth u z θ) ^ 2 * Work.Spaces.w z ^ 2
        * sig (Work.Spaces.gam α) θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Work.Coercivity.EDthW u ≤ En (Work.Spaces.gam α) (Work.Spaces.Dth u) := by
  have h1' : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.Dth u p.1 p.2 * Work.Spaces.Dth u p.1 p.2
        * Work.Spaces.w p.1 ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [iz_prod_restrict]
    refine (h1.const_mul 1).congr (Filter.Eventually.of_forall (fun p => ?_))
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, one_mul]
    ring
  have h2' : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.Dth u p.1 p.2 ^ 2 * Work.Spaces.w p.1 ^ 2
        * sig (Work.Spaces.gam α) p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [iz_prod_restrict]; exact h2
  have e1 : Work.Coercivity.EDthW u = ∫ p : ℝ × ℝ,
      Work.Spaces.Dth u p.1 p.2 * Work.Spaces.Dth u p.1 p.2 * Work.Spaces.w p.1 ^ 2
      ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (MeasureTheory.integral_prod (fun p : ℝ × ℝ =>
      Work.Spaces.Dth u p.1 p.2 * Work.Spaces.Dth u p.1 p.2 * Work.Spaces.w p.1 ^ 2) h1').symm
  have e2 : En (Work.Spaces.gam α) (Work.Spaces.Dth u) = ∫ p : ℝ × ℝ,
      Work.Spaces.Dth u p.1 p.2 ^ 2 * Work.Spaces.w p.1 ^ 2 * sig (Work.Spaces.gam α) p.2
      ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (MeasureTheory.integral_prod (fun p : ℝ × ℝ =>
      Work.Spaces.Dth u p.1 p.2 ^ 2 * Work.Spaces.w p.1 ^ 2 * sig (Work.Spaces.gam α) p.2)
      h2').symm
  rw [e1, e2]
  refine MeasureTheory.integral_mono_ae h1' h2' ?_
  filter_upwards [ae_prod_snd_mem measurableSet_Ioo ae_restrict_Iθ_mem_Ioo] with p hp
  have hgnn : (0:ℝ) ≤ sig (Work.Spaces.gam α) p.2 :=
    Real.rpow_nonneg (sin_nonneg_of_mem_Iθ ⟨le_of_lt hp.1, le_of_lt hp.2⟩) _
  calc Work.Spaces.Dth u p.1 p.2 * Work.Spaces.Dth u p.1 p.2 * Work.Spaces.w p.1 ^ 2
      = Work.Spaces.Dth u p.1 p.2 ^ 2 * Work.Spaces.w p.1 ^ 2 := by ring
    _ ≤ Work.Spaces.Dth u p.1 p.2 ^ 2 * Work.Spaces.w p.1 ^ 2 * sig (Work.Spaces.gam α) p.2 :=
        le_mul_of_one_le_right (mul_nonneg (sq_nonneg _) (sq_nonneg _))
          (one_le_sig_gam α hα hp)


/-! ## The angular boundary limits

`BdryTraces` gives the one-sided angular limits of `sin(2θ)^{1-γ}·(D_z^bD_θ^a f)²`; the
`η`-exponent version follows from `sin(2θ)^{1-η} = sin(2θ)^{γ-η}·sin(2θ)^{1-γ}` and
`sin(2θ)^{γ-η} → 0`. -/

theorem tendsto_sin_rpow_gam_sub_eta_right (α : ℝ) (hα : 0 < α) :
    Filter.Tendsto (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - Work.Spaces.eta))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
  Work.FTS.H2.tendsto_sin_rpow_zero_right _
    (by linarith [Work.Spaces.eta_lt_one, (by rw [Work.Spaces.gam]; linarith :
      (1 : ℝ) < Work.Spaces.gam α)])

theorem tendsto_sin_rpow_gam_sub_eta_left (α : ℝ) (hα : 0 < α) :
    Filter.Tendsto (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - Work.Spaces.eta))
      (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds 0) :=
  Work.FTS.H2.tendsto_sin_rpow_zero_left _
    (by linarith [Work.Spaces.eta_lt_one, (by rw [Work.Spaces.gam]; linarith :
      (1 : ℝ) < Work.Spaces.gam α)])

/-- The `η`-exponent angular limits follow from the `γ`-exponent ones. -/
theorem hvan_eta_of_gam (α : ℝ) (hα : 0 < α) {a b : ℕ} {f : Fn}
    (hγ : ∀ z, 0 < z → Filter.Tendsto
      (fun θ => (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α)
        * (Work.Spaces.mixed b a f z θ) ^ 2) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hγ2 : ∀ z, 0 < z → Filter.Tendsto
      (fun θ => (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α)
        * (Work.Spaces.mixed b a f z θ) ^ 2) (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds 0)) :
    (∀ z, 0 < z → Filter.Tendsto
        (fun θ => (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta)
          * (Work.Spaces.mixed b a f z θ) ^ 2) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
      ∧ ∀ z, 0 < z → Filter.Tendsto
        (fun θ => (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta)
          * (Work.Spaces.mixed b a f z θ) ^ 2) (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds 0) := by
  have hgη : Work.Spaces.gam α - Work.Spaces.eta = 1 - Work.Spaces.eta - (1 - Work.Spaces.gam α) := by
    ring
  constructor
  · intro z hz
    have hprod := (tendsto_sin_rpow_gam_sub_eta_right α hα).mul (hγ z hz)
    have hprod0 : Filter.Tendsto (fun θ => (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - Work.Spaces.eta)
        * ((Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a f z θ) ^ 2)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      simpa using hprod
    refine hprod0.congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds (by positivity : (0:ℝ) < π / 2))]
      with θ hθ hθπ
    have hθ0 : (0 : ℝ) < θ := hθ
    have hθπ' : θ < π / 2 := hθπ
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have hexp : Work.Spaces.gam α - Work.Spaces.eta + (1 - Work.Spaces.gam α)
        = 1 - Work.Spaces.eta := by ring
    rw [← mul_assoc, ← Real.rpow_add hs, hexp]
  · intro z hz
    have hprod := (tendsto_sin_rpow_gam_sub_eta_left α hα).mul (hγ2 z hz)
    have hprod0 : Filter.Tendsto (fun θ => (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - Work.Spaces.eta)
        * ((Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a f z θ) ^ 2)) (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds 0) := by
      simpa using hprod
    refine hprod0.congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Ioi_mem_nhds (by positivity : (0:ℝ) < π / 2))] with θ hθ hθ0
    have hθπ' : θ < π / 2 := hθ
    have hθ0' : (0 : ℝ) < θ := hθ0
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have hexp : Work.Spaces.gam α - Work.Spaces.eta + (1 - Work.Spaces.gam α)
        = 1 - Work.Spaces.eta := by ring
    rw [← mul_assoc, ← Real.rpow_add hs, hexp]

/-! ## The weighted energies as product-measure integrals -/

theorem En_eq_prod {β : ℝ} {u : Fn}
    (h : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2 * Work.Spaces.w z ^ 2 * sig β θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    En β u = ∫ p : ℝ × ℝ, u p.1 p.2 ^ 2 * Work.Spaces.w p.1 ^ 2 * sig β p.2
      ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  rw [En]
  refine (MeasureTheory.integral_prod
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (fun p : ℝ × ℝ => u p.1 p.2 ^ 2 * Work.Spaces.w p.1 ^ 2 * sig β p.2) ?_).symm
  rw [iz_prod_restrict]; exact h

theorem EnOne_eq_prod {u : Fn}
    (h : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2 * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    EnOne u = ∫ p : ℝ × ℝ, u p.1 p.2 ^ 2 * Work.Spaces.w p.1 ^ 2
      ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  rw [EnOne]
  refine (MeasureTheory.integral_prod
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (fun p : ℝ × ℝ => u p.1 p.2 ^ 2 * Work.Spaces.w p.1 ^ 2) ?_).symm
  rw [iz_prod_restrict]; exact h

theorem EDthW_eq_prod {u : Fn}
    (h : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth u z θ * Work.Spaces.Dth u z θ
        * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Work.Coercivity.EDthW u = ∫ p : ℝ × ℝ,
      Work.Spaces.Dth u p.1 p.2 * Work.Spaces.Dth u p.1 p.2 * Work.Spaces.w p.1 ^ 2
      ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  rw [Work.Coercivity.EDthW, Work.Coercivity.wip]
  refine (MeasureTheory.integral_prod
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (fun p : ℝ × ℝ => Work.Spaces.Dth u p.1 p.2 * Work.Spaces.Dth u p.1 p.2
      * Work.Spaces.w p.1 ^ 2) ?_).symm
  rw [iz_prod_restrict]; exact h

/-! ## Shape conversions for the `wip`-form integrands -/

theorem to_h1 {β : ℝ} {u : Fn}
    (h : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2 * Rho β z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2 * Work.Spaces.w z ^ 2 * sig β θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  refine h.congr (MeasureTheory.ae_restrict_of_forall_mem
    (measurableSet_Ici.prod measurableSet_Icc) (fun p hpp => ?_))
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry_apply_pair, Rho, sig]
  ring

theorem to_h2 {β : ℝ} {u : Fn}
    (h : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Coercivity.L u z θ * u z θ * Rho β z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Coercivity.L u z θ * u z θ
        * Work.Spaces.w z ^ 2 * sig β θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  refine h.congr (MeasureTheory.ae_restrict_of_forall_mem
    (measurableSet_Ici.prod measurableSet_Icc) (fun p hpp => ?_))
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry_apply_pair, Rho, sig]
  ring

theorem to_tr_hint {β : ℝ} {u : Fn}
    (h : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth u z θ * u z θ * Rho β z θ / (1 + z)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-β) * Work.Spaces.Dth u z θ * u z θ
        / (1 + z))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  refine h.congr (MeasureTheory.ae_restrict_of_forall_mem
    (measurableSet_Ici.prod measurableSet_Icc) (fun p hpp => ?_))
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry_apply_pair, Rho, sig]
  ring

theorem to_tr_hint2 {β : ℝ} {u : Fn}
    (h : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2 * Rho β z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  refine h.congr (MeasureTheory.ae_restrict_of_forall_mem
    (measurableSet_Ici.prod measurableSet_Icc) (fun p hpp => ?_))
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry_apply_pair, Rho, sig]
  ring

/-! ## The four estimates -/

theorem est_B (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {f : Fn}
    (hf : Work.FTS.Nonlin.RegQ α 2 f) :
    (47 / 100) * En Work.Spaces.eta f
      ≤ Work.Coercivity.wip (Rho Work.Spaces.eta) (Work.FTS.CoercivityFix.Lhat f) f := by
  have hp := IntPkg_Q α hα hf
  obtain ⟨hsq, hm, hb⟩ := hf
  have h0 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => f z θ ^ 2 * Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine (hp.sqDzEta 0 (by norm_num)).congr (MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ici.prod measurableSet_Icc) (fun p hpp => ?_))
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, Work.Spaces.DzIter_zero]
  have h1 := to_h1 (β := Work.Spaces.eta) h0
  have h2 := to_tr_hint2 (β := Work.Spaces.eta) h0
  have hL2 := to_h2 (β := Work.Spaces.eta) hp.intL_f_eta
  have hT2 := to_tr_hint (β := Work.Spaces.eta) hp.hint_f_eta
  have hvan := hvan_eta_of_gam α hα
    (fun z hz => ((hb 0 0 (by norm_num)).2 z hz).1)
    (fun z hz => ((hb 0 0 (by norm_num)).2 z hz).2)
  have hL := wip_L_self_Q f hp.zibp_f (sig Work.Spaces.eta) h1 hL2
  have hw : Work.Coercivity.wip (Rho Work.Spaces.eta) f f = En Work.Spaces.eta f :=
    wip_Rho_self Work.Spaces.eta f
  have hTr := wip_transport_le_Q Work.Spaces.eta f hsq hvan.1 hvan.2 hT2 h2
  have hTr' : Work.Coercivity.wip (Rho Work.Spaces.eta) (Work.Coercivity.Transport f) f
      ≤ (3 / 100) * En Work.Spaces.eta f := by
    rw [hw] at hTr
    have heta : (3 : ℝ) * |Work.Spaces.eta - 1| ≤ 3 / 100 := by
      rw [Work.Spaces.eta]
      rw [show |(99:ℝ) / 100 - 1| = 1 / 100 by norm_num]
      norm_num
    have hEn := En_nonneg Work.Spaces.eta f
    have h2 := mul_le_mul_of_nonneg_right heta hEn
    linarith [hTr, h2]
  have hT : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.Transport f z θ * f z θ * Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := intTransport_of hp.hint_f_eta
  have hsplit : Work.Coercivity.wip (Rho Work.Spaces.eta) (Work.FTS.CoercivityFix.Lhat f) f
      = Work.Coercivity.wip (Rho Work.Spaces.eta) (Work.Coercivity.L f) f
        - Work.Coercivity.wip (Rho Work.Spaces.eta) (Work.Coercivity.Transport f) f := by
    have h := wip_sub_left (ρ := Rho Work.Spaces.eta) (A := Work.Coercivity.L f)
      (B := Work.Coercivity.Transport f) (C := f) hp.intL_f_eta hT
    show Work.Coercivity.wip (Rho Work.Spaces.eta)
      (fun z θ => Work.Coercivity.L f z θ - Work.Coercivity.Transport f z θ) f = _
    exact h
  have hwc : ∀ A B : Fn, Work.Coercivity.wip (Rho Work.Spaces.eta) A B
      = Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * sig Work.Spaces.eta θ) A B := by
    intro A B
    simp only [Work.Coercivity.wip, Rho]
  rw [hsplit, hwc (Work.Coercivity.L f) f, hL, ← hwc f f, hw]
  linarith [hTr']

theorem est_D (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {f : Fn}
    (hf : Work.FTS.Nonlin.RegQ α 2 f) :
    (17 / 40) * En (Work.Spaces.gam α) (Work.Spaces.Dth f)
      ≤ Work.Coercivity.wip (Rho (Work.Spaces.gam α))
          (Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dth f) := by
  have hp := IntPkg_Q α hα hf
  obtain ⟨hsq, hm, hb⟩ := hf
  have h0 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.Dth f z θ) ^ 2 * Rho (Work.Spaces.gam α) z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine (hp.sqMixedGam 1 0 (by norm_num) (by norm_num)).congr
      (MeasureTheory.ae_restrict_of_forall_mem (measurableSet_Ici.prod measurableSet_Icc)
        (fun p hpp => ?_))
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, Work.Spaces.mixed, Work.Spaces.DzIter_zero,
      Work.Spaces.DthIter_zero, Work.Spaces.DthIter_succ]
  have h1 := to_h1 (β := Work.Spaces.gam α) h0
  have h2 := to_tr_hint2 (β := Work.Spaces.gam α) h0
  have hL2 := to_h2 (β := Work.Spaces.gam α) hp.intL_Dth_gam
  have hT2 := to_tr_hint (β := Work.Spaces.gam α) hp.hint_Dth_gam
  have hae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ
        = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f) z θ := by
    filter_upwards [ae_restrict_Iz_pos] with z hz
    filter_upwards [ae_restrict_Iθ_mem_Ioo] with θ hθ
    exact Work.FTS.CoercivityFix.LhatCalc.Dth_Lhat hsq hz hθ.1 hθ.2
  have hL := wip_L_self_Q (Work.Spaces.Dth f) hp.zibp_Dth (sig (Work.Spaces.gam α)) h1 hL2
  have hw : Work.Coercivity.wip (Rho (Work.Spaces.gam α))
      (Work.Spaces.Dth f) (Work.Spaces.Dth f) = En (Work.Spaces.gam α) (Work.Spaces.Dth f) :=
    wip_Rho_self (Work.Spaces.gam α) (Work.Spaces.Dth f)
  have hTr := wip_transport_le_Q (Work.Spaces.gam α) (Work.Spaces.Dth f)
    (Work.FTS.LocData.SmoothQuad.DthIter hsq 1)
    (fun z hz => ((hb 1 0 (by norm_num)).2 z hz).1)
    (fun z hz => ((hb 1 0 (by norm_num)).2 z hz).2) hT2 h2
  have hTr' : Work.Coercivity.wip (Rho (Work.Spaces.gam α))
      (Work.Coercivity.Transport (Work.Spaces.Dth f)) (Work.Spaces.Dth f)
      ≤ (3 / 40) * En (Work.Spaces.gam α) (Work.Spaces.Dth f) := by
    rw [hw] at hTr
    have hg : (3 : ℝ) * |Work.Spaces.gam α - 1| ≤ 3 / 40 := by
      rw [Work.Spaces.gam]
      rw [show |(1:ℝ) + α / 10 - 1| = α / 10 by
        rw [show (1:ℝ) + α / 10 - 1 = α / 10 by ring, abs_of_nonneg (by linarith)]]
      linarith
    have hEn := En_nonneg (Work.Spaces.gam α) (Work.Spaces.Dth f)
    have h2 := mul_le_mul_of_nonneg_right hg hEn
    linarith [hTr, h2]
  have hT : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.Transport (Work.Spaces.Dth f) z θ * Work.Spaces.Dth f z θ
        * Rho (Work.Spaces.gam α) z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    intTransport_of hp.hint_Dth_gam
  have hsplit : Work.Coercivity.wip (Rho (Work.Spaces.gam α))
      (Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dth f)
      = Work.Coercivity.wip (Rho (Work.Spaces.gam α)) (Work.Coercivity.L (Work.Spaces.Dth f))
          (Work.Spaces.Dth f)
        - Work.Coercivity.wip (Rho (Work.Spaces.gam α))
            (Work.Coercivity.Transport (Work.Spaces.Dth f)) (Work.Spaces.Dth f) := by
    have h := wip_sub_left (ρ := Rho (Work.Spaces.gam α))
      (A := Work.Coercivity.L (Work.Spaces.Dth f))
      (B := Work.Coercivity.Transport (Work.Spaces.Dth f)) (C := Work.Spaces.Dth f)
      hp.intL_Dth_gam hT
    rw [Work.Coercivity.wip_congr_ae hae]
    show Work.Coercivity.wip (Rho (Work.Spaces.gam α))
      (fun z θ => Work.Coercivity.L (Work.Spaces.Dth f) z θ
        - Work.Coercivity.Transport (Work.Spaces.Dth f) z θ) (Work.Spaces.Dth f) = _
    exact h
  have hwc : ∀ A B : Fn, Work.Coercivity.wip (Rho (Work.Spaces.gam α)) A B
      = Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * sig (Work.Spaces.gam α) θ) A B := by
    intro A B
    simp only [Work.Coercivity.wip, Rho]
  rw [hsplit, hwc (Work.Coercivity.L (Work.Spaces.Dth f)) (Work.Spaces.Dth f), hL,
    ← hwc (Work.Spaces.Dth f) (Work.Spaces.Dth f), hw]
  linarith [hTr']

/-! ## Toolbox for the two remaining estimates

The two estimates `est_A` and `est_C` rest on two more scalar inequalities:

* `est_C` needs the transport pairing in the *plain* radial weight to be dominated by
  `(3/8)E_1(u) + 6·|D_θu·w|²`, which is the pointwise Young inequality
  `3ab/(1+z) ≤ 6a² + (3/8)b²` integrated;
* `est_A` needs the `D_z`-commutator defect `Ê₂f` to be dominated by
  `|f|²_{η} + 4|D_θf|²_{γ} + (1/8)|D_zf|²_{η}`, which is the pointwise bound
  `|Ê₂u| ≤ (2|u| + 3|D_θu|)/4` combined with two more Young inequalities.
-/

/-- `IntegrableOn` transports across a pointwise identification of the integrands. -/
theorem integrableOn_congr_fun_Q {A B : Fn}
    (h : MeasureTheory.IntegrableOn (Function.uncurry A) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (heq : ∀ z θ, A z θ = B z θ) :
    MeasureTheory.IntegrableOn (Function.uncurry B) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  refine h.congr (MeasureTheory.ae_restrict_of_forall_mem
    (measurableSet_Ici.prod measurableSet_Icc) (fun p _ => ?_))
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry_apply_pair]
  exact heq z θ

/-- The weighted energy `En` with the integrand in the `Rho`-form. -/
theorem En_eq_prod_Rho {β : ℝ} {u : Fn}
    (h : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => u z θ ^ 2 * Rho β z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    En β u = ∫ p : ℝ × ℝ, u p.1 p.2 ^ 2 * Rho β p.1 p.2
      ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  rw [En_eq_prod (to_h1 h)]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => by
    rcases p with ⟨z, θ⟩
    simp only [Rho]
    ring))

/-! ### The two Young inequalities

`(1/2)|a||b| ≤ a² + b²/16` and `(3/4)|a||b| ≤ 3a² + (3/64)b²`, both with the sharp
discriminant-zero constants. -/

theorem amgm_half_abs (a b : ℝ) : (1 / 2) * |a| * |b| ≤ a ^ 2 + (1 / 16) * b ^ 2 := by
  have h : (0 : ℝ) ≤ (|a| - |b| / 4) ^ 2 := sq_nonneg _
  have e : (|a| - |b| / 4) ^ 2 = a ^ 2 - |a| * |b| / 2 + b ^ 2 / 16 := by
    rw [sub_sq, sq_abs, div_pow, sq_abs]
    ring
  rw [e] at h
  nlinarith [h]

theorem amgm_three_quarter_abs (a b : ℝ) :
    (3 / 4) * |a| * |b| ≤ 3 * a ^ 2 + (3 / 64) * b ^ 2 := by
  have h : (0 : ℝ) ≤ (|a| - |b| / 8) ^ 2 := sq_nonneg _
  have e : (|a| - |b| / 8) ^ 2 = a ^ 2 - |a| * |b| / 4 + b ^ 2 / 64 := by
    rw [sub_sq, sq_abs, div_pow, sq_abs]
    ring
  rw [e] at h
  nlinarith [h]

/-- Young for the transport term: `3ab/(1+z) ≤ 6a² + (3/8)b²` for `z ≥ 0`. -/
theorem transport_young (a b : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    3 * a / (1 + z) * b ≤ 6 * a ^ 2 + (3 / 8) * b ^ 2 := by
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  rcases le_total 0 (a * b) with hab | hab
  · have h1 : 3 * a / (1 + z) * b ≤ 3 * (a * b) := by
      rw [show 3 * a / (1 + z) * b = 3 * (a * b) / (1 + z) by ring]
      rw [div_le_iff₀ hz1]
      nlinarith
    have h2 : 3 * (a * b) ≤ 6 * a ^ 2 + (3 / 8) * b ^ 2 := by
      nlinarith [sq_nonneg (4 * a - b)]
    linarith
  · have h1 : 3 * a / (1 + z) * b ≤ 0 := by
      rw [show 3 * a / (1 + z) * b = 3 * (a * b) / (1 + z) by ring]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hz1)
    have h2 : (0 : ℝ) ≤ 6 * a ^ 2 + (3 / 8) * b ^ 2 := by positivity
    linarith

/-- The pointwise transport estimate with the plain radial weight. -/
theorem transport_pt_w2 {u : Fn} {z θ : ℝ} (hz : 0 ≤ z) :
    Work.Coercivity.Transport u z θ * u z θ * Work.Spaces.w z ^ 2
      ≤ 6 * ((Work.Spaces.Dth u z θ) ^ 2 * Work.Spaces.w z ^ 2)
        + (3 / 8) * ((u z θ) ^ 2 * Work.Spaces.w z ^ 2) := by
  have h2 := mul_le_mul_of_nonneg_right
    (transport_young (Work.Spaces.Dth u z θ) (u z θ) hz) (sq_nonneg (Work.Spaces.w z))
  simp only [Work.Coercivity.Transport]
  nlinarith [h2]

/-- The transport pairing in the plain radial weight. -/
theorem transport_w2_bound {u : Fn}
    (hT : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.Transport u z θ * u z θ * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hD : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Spaces.Dth u z θ * Work.Spaces.Dth u z θ * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hU : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (u z θ) ^ 2 * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2) (Work.Coercivity.Transport u) u
      ≤ (3 / 8) * EnOne u + 6 * Work.Coercivity.EDthW u := by
  have hpr : (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      = (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := iz_prod_restrict
  have hT' : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Work.Coercivity.Transport u p.1 p.2 * u p.1 p.2 * Work.Spaces.w p.1 ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [hpr]; exact hT
  have hD' : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Work.Spaces.Dth u p.1 p.2 * Work.Spaces.Dth u p.1 p.2 * Work.Spaces.w p.1 ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [hpr]; exact hD
  have hU' : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (u p.1 p.2) ^ 2 * Work.Spaces.w p.1 ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [hpr]; exact hU
  have hA : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      6 * ((Work.Spaces.Dth u p.1 p.2) ^ 2 * Work.Spaces.w p.1 ^ 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (hD'.const_mul 6).congr (Filter.Eventually.of_forall (fun p => by
      rcases p with ⟨z, θ⟩; ring))
  have hB : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (3 / 8) * ((u p.1 p.2) ^ 2 * Work.Spaces.w p.1 ^ 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (hU'.const_mul (3 / 8)).congr (Filter.Eventually.of_forall (fun p => by
      rcases p with ⟨z, θ⟩; ring))
  have hS : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      6 * ((Work.Spaces.Dth u p.1 p.2) ^ 2 * Work.Spaces.w p.1 ^ 2)
        + (3 / 8) * ((u p.1 p.2) ^ 2 * Work.Spaces.w p.1 ^ 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := hA.add hB
  have hpoint : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      Work.Coercivity.Transport u p.1 p.2 * u p.1 p.2 * Work.Spaces.w p.1 ^ 2
        ≤ 6 * ((Work.Spaces.Dth u p.1 p.2) ^ 2 * Work.Spaces.w p.1 ^ 2)
          + (3 / 8) * ((u p.1 p.2) ^ 2 * Work.Spaces.w p.1 ^ 2) := by
    filter_upwards [ae_prod_fst_mem (s := Set.Ici (0 : ℝ)) measurableSet_Ici
      (MeasureTheory.ae_restrict_mem measurableSet_Ici)] with p hp
    rcases p with ⟨z, θ⟩
    simp only [Set.mem_Ici] at hp
    exact transport_pt_w2 hp
  calc Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
        (Work.Coercivity.Transport u) u
      = ∫ p : ℝ × ℝ, Work.Coercivity.Transport u p.1 p.2 * u p.1 p.2
          * Work.Spaces.w p.1 ^ 2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
        Work.Coercivity.wip_eq_integral_prod (fun z _ => Work.Spaces.w z ^ 2)
          (Work.Coercivity.Transport u) u hT
    _ ≤ ∫ p : ℝ × ℝ, (6 * ((Work.Spaces.Dth u p.1 p.2) ^ 2 * Work.Spaces.w p.1 ^ 2)
          + (3 / 8) * ((u p.1 p.2) ^ 2 * Work.Spaces.w p.1 ^ 2))
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
        MeasureTheory.integral_mono_ae hT' hS hpoint
    _ = 6 * (∫ p : ℝ × ℝ, Work.Spaces.Dth u p.1 p.2 * Work.Spaces.Dth u p.1 p.2
            * Work.Spaces.w p.1 ^ 2
            ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
        + (3 / 8) * (∫ p : ℝ × ℝ, (u p.1 p.2) ^ 2 * Work.Spaces.w p.1 ^ 2
            ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
        have e1 : (∫ p : ℝ × ℝ,
              (Work.Spaces.Dth u p.1 p.2) ^ 2 * Work.Spaces.w p.1 ^ 2
              ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
                (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
            = ∫ p : ℝ × ℝ, Work.Spaces.Dth u p.1 p.2 * Work.Spaces.Dth u p.1 p.2
                * Work.Spaces.w p.1 ^ 2
                ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
                  (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => by
            rcases p with ⟨z, θ⟩; ring))
        rw [MeasureTheory.integral_add
            (f := fun p : ℝ × ℝ => 6 * ((Work.Spaces.Dth u p.1 p.2) ^ 2
              * Work.Spaces.w p.1 ^ 2))
            (g := fun p : ℝ × ℝ => (3 / 8) * ((u p.1 p.2) ^ 2 * Work.Spaces.w p.1 ^ 2))
            hA hB,
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, e1]
    _ = (3 / 8) * EnOne u + 6 * Work.Coercivity.EDthW u := by
        rw [EDthW_eq_prod hD, EnOne_eq_prod hU]
        ring

/-- **The `ê₂`-pairing defect bound.** -/
theorem E2hat_pt {α : ℝ} (u g : Fn) (hα : 0 < α) {z θ : ℝ} (hz : 0 ≤ z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    -(u z θ ^ 2 * Rho Work.Spaces.eta z θ
        + 4 * ((Work.Spaces.Dth u z θ) ^ 2 * Rho (Work.Spaces.gam α) z θ)
        + (7 / 64) * (g z θ ^ 2 * Rho Work.Spaces.eta z θ))
      ≤ Work.FTS.CoercivityFix.E2hat u z θ * g z θ * Rho Work.Spaces.eta z θ := by
  have habs : |Work.FTS.CoercivityFix.E2hat u z θ|
      ≤ (2 * |u z θ| + 3 * |Work.Spaces.Dth u z θ|) / 4 :=
    Work.FTS.CoercivityFix.E2hat_abs_le u (z := z) (θ := θ) hz
  have hρ : 0 ≤ Rho Work.Spaces.eta z θ := Rho_nonneg _ _ _ hθ
  have hρ' : Rho Work.Spaces.eta z θ ≤ Rho (Work.Spaces.gam α) z θ :=
    Rho_eta_le_Rho_gam α hα z θ hθ
  have hA := amgm_half_abs (u z θ) (g z θ)
  have hB := amgm_three_quarter_abs (Work.Spaces.Dth u z θ) (g z θ)
  have h3ρ : (3 : ℝ) * Rho Work.Spaces.eta z θ ≤ 4 * Rho (Work.Spaces.gam α) z θ := by
    nlinarith [hρ, hρ']
  have hAρ := mul_le_mul_of_nonneg_right hA hρ
  have hBρ := mul_le_mul_of_nonneg_right hB hρ
  have h3B := mul_le_mul_of_nonneg_left h3ρ (sq_nonneg (Work.Spaces.Dth u z θ))
  have h1 : |Work.FTS.CoercivityFix.E2hat u z θ| * |g z θ| * Rho Work.Spaces.eta z θ
      ≤ ((1 / 2) * |u z θ| + (3 / 4) * |Work.Spaces.Dth u z θ|) * |g z θ|
        * Rho Work.Spaces.eta z θ := by
    have h := mul_le_mul_of_nonneg_right habs (abs_nonneg (g z θ))
    have h2 := mul_le_mul_of_nonneg_right h hρ
    linarith [h2]
  have h2 : ((1 / 2) * |u z θ| + (3 / 4) * |Work.Spaces.Dth u z θ|) * |g z θ|
        * Rho Work.Spaces.eta z θ
      ≤ u z θ ^ 2 * Rho Work.Spaces.eta z θ
        + 4 * ((Work.Spaces.Dth u z θ) ^ 2 * Rho (Work.Spaces.gam α) z θ)
        + (7 / 64) * (g z θ ^ 2 * Rho Work.Spaces.eta z θ) := by
    nlinarith [hAρ, hBρ, h3B]
  have h3 : -|Work.FTS.CoercivityFix.E2hat u z θ * g z θ * Rho Work.Spaces.eta z θ|
      ≤ Work.FTS.CoercivityFix.E2hat u z θ * g z θ * Rho Work.Spaces.eta z θ :=
    neg_abs_le _
  have h4 : |Work.FTS.CoercivityFix.E2hat u z θ * g z θ * Rho Work.Spaces.eta z θ|
      = |Work.FTS.CoercivityFix.E2hat u z θ| * |g z θ| * Rho Work.Spaces.eta z θ := by
    rw [abs_mul, abs_mul, abs_of_nonneg hρ]
  linarith [h1, h2, h3, h4]

/-- **The `ê₂`-pairing defect is bounded below.** -/
theorem E2hat_wip_lower (α : ℝ) (hα : 0 < α) {u g : Fn}
    (hE : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.FTS.CoercivityFix.E2hat u z θ * g z θ * Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hU : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (u z θ) ^ 2 * Rho Work.Spaces.eta z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hDγ : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (Work.Spaces.Dth u z θ) ^ 2 * Rho (Work.Spaces.gam α) z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hG : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (g z θ) ^ 2 * Rho Work.Spaces.eta z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    -(En Work.Spaces.eta u + 4 * En (Work.Spaces.gam α) (Work.Spaces.Dth u)
        + (1 / 8) * En Work.Spaces.eta g)
      ≤ Work.Coercivity.wip (Rho Work.Spaces.eta) (Work.FTS.CoercivityFix.E2hat u) g := by
  have hpr : (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      = (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := iz_prod_restrict
  have hE' : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Work.FTS.CoercivityFix.E2hat u p.1 p.2 * g p.1 p.2 * Rho Work.Spaces.eta p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [hpr]; exact hE
  have hU' : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (u p.1 p.2) ^ 2 * Rho Work.Spaces.eta p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [hpr]; exact hU
  have hDγ' : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.Spaces.Dth u p.1 p.2) ^ 2 * Rho (Work.Spaces.gam α) p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [hpr]; exact hDγ
  have hG' : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (g p.1 p.2) ^ 2 * Rho Work.Spaces.eta p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [hpr]; exact hG
  have hF : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      u p.1 p.2 ^ 2 * Rho Work.Spaces.eta p.1 p.2
        + 4 * ((Work.Spaces.Dth u p.1 p.2) ^ 2 * Rho (Work.Spaces.gam α) p.1 p.2)
        + (7 / 64) * (g p.1 p.2 ^ 2 * Rho Work.Spaces.eta p.1 p.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (hU'.add (hDγ'.const_mul 4)).add (hG'.const_mul (7 / 64))
  have hpoint : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      -(u p.1 p.2 ^ 2 * Rho Work.Spaces.eta p.1 p.2
        + 4 * ((Work.Spaces.Dth u p.1 p.2) ^ 2 * Rho (Work.Spaces.gam α) p.1 p.2)
        + (7 / 64) * (g p.1 p.2 ^ 2 * Rho Work.Spaces.eta p.1 p.2))
        ≤ Work.FTS.CoercivityFix.E2hat u p.1 p.2 * g p.1 p.2 * Rho Work.Spaces.eta p.1 p.2 := by
    filter_upwards [ae_prod_fst_mem (s := Set.Ici (0 : ℝ)) measurableSet_Ici
      (MeasureTheory.ae_restrict_mem measurableSet_Ici),
      ae_prod_snd_mem measurableSet_Icc (MeasureTheory.ae_restrict_mem measurableSet_Icc)]
      with p hz hθ
    rcases p with ⟨z, θ⟩
    simp only [Set.mem_Ici] at hz
    exact E2hat_pt u g hα hz hθ
  have hFval : (∫ p : ℝ × ℝ, (u p.1 p.2 ^ 2 * Rho Work.Spaces.eta p.1 p.2
        + 4 * ((Work.Spaces.Dth u p.1 p.2) ^ 2 * Rho (Work.Spaces.gam α) p.1 p.2)
        + (7 / 64) * (g p.1 p.2 ^ 2 * Rho Work.Spaces.eta p.1 p.2))
      ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = En Work.Spaces.eta u + 4 * En (Work.Spaces.gam α) (Work.Spaces.Dth u)
        + (7 / 64) * En Work.Spaces.eta g := by
    have eF1 : (∫ p : ℝ × ℝ, u p.1 p.2 ^ 2 * Rho Work.Spaces.eta p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))) = En Work.Spaces.eta u :=
      (En_eq_prod_Rho hU).symm
    have eF2 : (∫ p : ℝ × ℝ, (Work.Spaces.Dth u p.1 p.2) ^ 2
          * Rho (Work.Spaces.gam α) p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
        = En (Work.Spaces.gam α) (Work.Spaces.Dth u) :=
      (En_eq_prod_Rho hDγ).symm
    have eF3 : (∫ p : ℝ × ℝ, g p.1 p.2 ^ 2 * Rho Work.Spaces.eta p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))) = En Work.Spaces.eta g :=
      (En_eq_prod_Rho hG).symm
    rw [MeasureTheory.integral_add
          (f := fun p : ℝ × ℝ => u p.1 p.2 ^ 2 * Rho Work.Spaces.eta p.1 p.2
            + 4 * ((Work.Spaces.Dth u p.1 p.2) ^ 2 * Rho (Work.Spaces.gam α) p.1 p.2))
          (g := fun p : ℝ × ℝ => (7 / 64) * (g p.1 p.2 ^ 2 * Rho Work.Spaces.eta p.1 p.2))
          (hU'.add (hDγ'.const_mul 4)) (hG'.const_mul (7 / 64)),
        MeasureTheory.integral_add
          (f := fun p : ℝ × ℝ => u p.1 p.2 ^ 2 * Rho Work.Spaces.eta p.1 p.2)
          (g := fun p : ℝ × ℝ => 4 * ((Work.Spaces.Dth u p.1 p.2) ^ 2
            * Rho (Work.Spaces.gam α) p.1 p.2))
          hU' (hDγ'.const_mul 4),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        eF1, eF2, eF3]
  have hmain : -(En Work.Spaces.eta u + 4 * En (Work.Spaces.gam α) (Work.Spaces.Dth u)
        + (7 / 64) * En Work.Spaces.eta g)
      ≤ Work.Coercivity.wip (Rho Work.Spaces.eta) (Work.FTS.CoercivityFix.E2hat u) g := by
    rw [Work.Coercivity.wip_eq_integral_prod (Rho Work.Spaces.eta)
      (Work.FTS.CoercivityFix.E2hat u) g hE]
    rw [← hFval]
    rw [← MeasureTheory.integral_neg]
    exact MeasureTheory.integral_mono_ae hF.neg hE' hpoint
  have h7 : (7 / 64) * En Work.Spaces.eta g ≤ (1 / 8) * En Work.Spaces.eta g := by
    have hg := En_nonneg Work.Spaces.eta g
    linarith
  linarith [hmain, h7]

/-! ## The two remaining estimates -/

theorem est_C (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {f : Fn}
    (hf : Work.FTS.Nonlin.RegQ α 2 f) :
    (1 / 8) * EnOne f - 6 * Work.Coercivity.EDthW f
      ≤ Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
          (Work.FTS.CoercivityFix.Lhat f) f := by
  have hp := IntPkg_Q α hα hf
  obtain ⟨hsq, hm, hb⟩ := hf
  have hU : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (f z θ) ^ 2 * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrableOn_congr_fun_Q (A := fun z θ =>
      (Work.Spaces.DzIter 0 f z θ) ^ 2 * Work.Spaces.w z ^ 2)
      (hp.sqDzOne 0 (by norm_num)) (fun z θ => by
        simp only [Work.Spaces.DzIter_zero])
  have hD : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Spaces.Dth f z θ * Work.Spaces.Dth f z θ * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrableOn_congr_fun_Q (A := fun z θ =>
      (Work.Spaces.mixed 0 1 f z θ) ^ 2 * Work.Spaces.w z ^ 2)
      (hp.sqMixedOne 1 0 (by norm_num) (by norm_num)) (fun z θ => by
        simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero,
          Work.Spaces.DthIter_succ]
        ring)
  have hT : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.Transport f z θ * f z θ * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrableOn_congr_fun_Q (A := fun z θ =>
      3 * (Work.Spaces.Dth f z θ * f z θ * Work.Spaces.w z ^ 2 / (1 + z)))
      (hp.hint_f_one.const_mul 3) (fun z θ => by
        simp only [Work.Coercivity.Transport]; ring)
  have hU1 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      f z θ ^ 2 * Work.Spaces.w z ^ 2 * (1 : ℝ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrableOn_congr_fun_Q hU (fun z θ => by ring)
  have hL1 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.L f z θ * f z θ * Work.Spaces.w z ^ 2 * (1 : ℝ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrableOn_congr_fun_Q (A := fun z θ =>
      Work.Coercivity.L f z θ * f z θ * Work.Spaces.w z ^ 2)
      hp.intL_f_one (fun z θ => by ring)
  have hL := wip_L_self_Q f hp.zibp_f (fun _ => 1) hU1 hL1
  simp only [mul_one] at hL
  have hw : Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2) f f = EnOne f :=
    wip_one_self f
  have hbd := transport_w2_bound hT hD hU
  have hsplit : Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
      (Work.FTS.CoercivityFix.Lhat f) f
      = Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2) (Work.Coercivity.L f) f
        - Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
            (Work.Coercivity.Transport f) f := by
    have h := wip_sub_left (ρ := fun z _ => Work.Spaces.w z ^ 2)
      (A := Work.Coercivity.L f) (B := Work.Coercivity.Transport f) (C := f)
      hp.intL_f_one hT
    show Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
      (fun z θ => Work.Coercivity.L f z θ - Work.Coercivity.Transport f z θ) f = _
    exact h
  rw [hsplit, hL, hw]
  linarith [hbd]

theorem est_A (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {f : Fn}
    (hf : Work.FTS.Nonlin.RegQ α 2 f) :
    (47 / 100) * En Work.Spaces.eta (Work.Spaces.Dz f)
      - (En Work.Spaces.eta f + 4 * En (Work.Spaces.gam α) (Work.Spaces.Dth f)
          + (1 / 8) * En Work.Spaces.eta (Work.Spaces.Dz f))
      ≤ Work.Coercivity.wip (Rho Work.Spaces.eta)
          (Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dz f) := by
  have hp := IntPkg_Q α hα hf
  obtain ⟨hsq, hm, hb⟩ := hf
  -- ## the `𝓛̂`-pairing of `D_z f`
  have hsqDz : Work.FTS.LocData.SmoothQuad (Work.Spaces.Dz f) :=
    Work.FTS.LocData.SmoothQuad.DzIter hsq 1
  have hvan := hvan_eta_of_gam α hα
    (fun z hz => ((hb 0 1 (by norm_num)).2 z hz).1)
    (fun z hz => ((hb 0 1 (by norm_num)).2 z hz).2)
  have h1 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (Work.Spaces.Dz f z θ) ^ 2 * Work.Spaces.w z ^ 2 * sig Work.Spaces.eta θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrableOn_congr_fun_Q (A := fun z θ =>
      (Work.Spaces.DzIter 1 f z θ) ^ 2 * Rho Work.Spaces.eta z θ)
      (hp.sqDzEta 1 (by norm_num)) (fun z θ => by
        simp only [Rho, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]; ring)
  have h2 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.L (Work.Spaces.Dz f) z θ * Work.Spaces.Dz f z θ
        * Work.Spaces.w z ^ 2 * sig Work.Spaces.eta θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrableOn_congr_fun_Q (A := fun z θ =>
      Work.Coercivity.L (Work.Spaces.Dz f) z θ * Work.Spaces.Dz f z θ
        * Rho Work.Spaces.eta z θ)
      hp.intL_Dz_eta (fun z θ => by simp only [Rho]; ring)
  have h3 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
        * Work.Spaces.Dth (Work.Spaces.Dz f) z θ * Work.Spaces.Dz f z θ / (1 + z)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrableOn_congr_fun_Q (A := fun z θ =>
      Work.Spaces.Dth (Work.Spaces.Dz f) z θ * Work.Spaces.Dz f z θ
        * Rho Work.Spaces.eta z θ / (1 + z))
      hp.hint_Dz_eta (fun z θ => by simp only [Rho, sig]; ring)
  have h4 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
        * (Work.Spaces.Dz f z θ) ^ 2)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrableOn_congr_fun_Q h1 (fun z θ => by simp only [sig]; ring)
  have h5 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.Transport (Work.Spaces.Dz f) z θ * Work.Spaces.Dz f z θ
        * Rho Work.Spaces.eta z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrableOn_congr_fun_Q (A := fun z θ =>
      3 * (Work.Spaces.Dth (Work.Spaces.Dz f) z θ * Work.Spaces.Dz f z θ
        * Rho Work.Spaces.eta z θ / (1 + z)))
      (hp.hint_Dz_eta.const_mul 3) (fun z θ => by
        simp only [Work.Coercivity.Transport]; ring)
  have hwc : ∀ A B : Fn, Work.Coercivity.wip (Rho Work.Spaces.eta) A B
      = Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * sig Work.Spaces.eta θ) A B :=
    fun A B => rfl
  have hwDz : Work.Coercivity.wip (Rho Work.Spaces.eta) (Work.Spaces.Dz f)
      (Work.Spaces.Dz f) = En Work.Spaces.eta (Work.Spaces.Dz f) :=
    wip_Rho_self Work.Spaces.eta (Work.Spaces.Dz f)
  have hL0 := wip_L_self_Q (Work.Spaces.Dz f) hp.zibp_Dz (sig Work.Spaces.eta) h1 h2
  have hTr := wip_transport_le_Q Work.Spaces.eta (Work.Spaces.Dz f) hsqDz
    hvan.1 hvan.2 h3 h4
  have hTr' : Work.Coercivity.wip (Rho Work.Spaces.eta)
      (Work.Coercivity.Transport (Work.Spaces.Dz f)) (Work.Spaces.Dz f)
      ≤ (3 / 100) * En Work.Spaces.eta (Work.Spaces.Dz f) := by
    rw [hwDz] at hTr
    have heta : (3 : ℝ) * |Work.Spaces.eta - 1| ≤ 3 / 100 := by
      rw [Work.Spaces.eta]
      rw [show |(99 : ℝ) / 100 - 1| = 1 / 100 by norm_num]
      norm_num
    have hEn := En_nonneg Work.Spaces.eta (Work.Spaces.Dz f)
    have h2' := mul_le_mul_of_nonneg_right heta hEn
    linarith [hTr, h2']
  have hL : (47 / 100) * En Work.Spaces.eta (Work.Spaces.Dz f)
      ≤ Work.Coercivity.wip (Rho Work.Spaces.eta)
          (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f)) (Work.Spaces.Dz f) := by
    have hsplit : Work.Coercivity.wip (Rho Work.Spaces.eta)
        (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f)) (Work.Spaces.Dz f)
        = Work.Coercivity.wip (Rho Work.Spaces.eta) (Work.Coercivity.L (Work.Spaces.Dz f))
            (Work.Spaces.Dz f)
          - Work.Coercivity.wip (Rho Work.Spaces.eta)
              (Work.Coercivity.Transport (Work.Spaces.Dz f)) (Work.Spaces.Dz f) := by
      have h := wip_sub_left (ρ := Rho Work.Spaces.eta)
        (A := Work.Coercivity.L (Work.Spaces.Dz f))
        (B := Work.Coercivity.Transport (Work.Spaces.Dz f)) (C := Work.Spaces.Dz f)
        hp.intL_Dz_eta h5
      show Work.Coercivity.wip (Rho Work.Spaces.eta)
        (fun z θ => Work.Coercivity.L (Work.Spaces.Dz f) z θ
          - Work.Coercivity.Transport (Work.Spaces.Dz f) z θ) (Work.Spaces.Dz f) = _
      exact h
    rw [hsplit, hwc (Work.Coercivity.L (Work.Spaces.Dz f)) (Work.Spaces.Dz f), hL0,
      ← hwc (Work.Spaces.Dz f) (Work.Spaces.Dz f), hwDz]
    linarith [hTr']
  -- ## the `D_z`-commutator defect
  have hae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ
        = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f) z θ
          + Work.FTS.CoercivityFix.E2hat f z θ := by
    filter_upwards [ae_restrict_Iz_pos] with z hz
    filter_upwards [ae_restrict_Iθ_mem_Ioo] with θ hθ
    exact Work.FTS.CoercivityFix.LhatCalc.Dz_Lhat hsq hz hθ.1 hθ.2
  have hsplitE : Work.Coercivity.wip (Rho Work.Spaces.eta)
      (Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dz f)
      = Work.Coercivity.wip (Rho Work.Spaces.eta)
          (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f)) (Work.Spaces.Dz f)
        + Work.Coercivity.wip (Rho Work.Spaces.eta)
            (Work.FTS.CoercivityFix.E2hat f) (Work.Spaces.Dz f) := by
    rw [Work.Coercivity.wip_congr_ae hae]
    exact Work.Coercivity.wip_add_left (ρ := Rho Work.Spaces.eta)
      (g := Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f))
      (h := Work.FTS.CoercivityFix.E2hat f) (k := Work.Spaces.Dz f)
      hp.intLhat_Dz_eta hp.intE2hat_Dz_eta
  have hU0 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (f z θ) ^ 2 * Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrableOn_congr_fun_Q (A := fun z θ =>
      (Work.Spaces.DzIter 0 f z θ) ^ 2 * Rho Work.Spaces.eta z θ)
      (hp.sqDzEta 0 (by norm_num)) (fun z θ => by
        simp only [Work.Spaces.DzIter_zero])
  have hDη : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (Work.Spaces.Dth f z θ) ^ 2 * Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrableOn_congr_fun_Q (A := fun z θ =>
      (Work.Spaces.mixed 0 1 f z θ) ^ 2 * Rho Work.Spaces.eta z θ)
      (hp.sqMixedEta 1 0 (by norm_num) (by norm_num)) (fun z θ => by
        simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero,
          Work.Spaces.DthIter_succ])
  have hDγ : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (Work.Spaces.Dth f z θ) ^ 2 * Rho (Work.Spaces.gam α) z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrableOn_congr_fun_Q (A := fun z θ =>
      (Work.Spaces.mixed 0 1 f z θ) ^ 2 * Rho (Work.Spaces.gam α) z θ)
      (hp.sqMixedGam 1 0 (by norm_num) (by norm_num)) (fun z θ => by
        simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero,
          Work.Spaces.DthIter_succ])
  have hG : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (Work.Spaces.Dz f z θ) ^ 2 * Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrableOn_congr_fun_Q (A := fun z θ =>
      (Work.Spaces.DzIter 1 f z θ) ^ 2 * Rho Work.Spaces.eta z θ)
      (hp.sqDzEta 1 (by norm_num)) (fun z θ => by
        simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero])
  have hE := E2hat_wip_lower α hα hp.intE2hat_Dz_eta hU0 hDγ hG
  rw [hsplitE]
  linarith [hL, hE]

end Work.FTS.CoercivityFix.Coer1