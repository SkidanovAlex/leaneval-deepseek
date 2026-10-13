/-
# `Work.FTS.LocDataExt.Traces` — the boundary traces `BdryTraces` of the localised datum

`Work.FTS.Nonlin.BdryTraces α k f` is the domain of the integration-by-parts boundary terms of
the paper's estimates: for every slot `(b,a)` with `a + b ≤ k`,

* `z · (D_z^b D_θ^a f z θ · w z)² → 0` as `z → 0⁺` and as `z → ∞`, for each `θ ∈ (0,π/2)`;
* `sin(2θ)^{1-γ}·(D_z^b D_θ^a f z θ)² → 0` as `θ → 0⁺` and as `θ → (π/2)⁻`, for each `z > 0`.

For the perturbation `locG α L β (hLoc α) = locR α L β (z)·Γ(θ)` of the localised-data
extension (`Defs.lean`, `SepFactor.lean`) all four limits are elementary:

* **at `z → 0⁺`**: `locR` vanishes on the strip `0 < z < 3/4` (for `L ≥ 1`, both the far part
  `-(α/c)·zfarR L = -(α/c)(1-χ(z/L))F_*` and the bump part `β·bumpZ` vanish there), hence so do
  all its `D`-iterates (`Work.FTS.LocData.ZFBase.mixed_eq_zero_of_eventually_zero`);
* **at `z → ∞`**: `locR` agrees beyond `max (2L) (7/4)` with `-(α/c)·FM.Fstar`, whose
  `D_z`-jets decay like `1/z`, while `|D_θ^a Γ| ≤ C·Γ ≤ C` (`DthIter_Gam_abs_le`); the factor
  `z·w(z)² ≤ 64/z` then gives the limit;
* **at `θ → 0⁺`, `(π/2)⁻`**: the angular factor obeys `|D_θ^a Γ| ≤ C·Γ ≤ C·sin(2θ)^{α/5}`
  (`Gam_le_sin_two_rpow`), and `1 - γ + 2·(α/5) = 3α/10 > 0`, so
  `sin(2θ)^{1-γ}·(D_z^b D_θ^a f z θ)² ≤ C(z)²·sin(2θ)^{3α/10} → 0`.

The module is stated for a *generic* order `k` with the two jet inputs as hypotheses
(`hΓ` at order `k`, `hF` at order `k`), so that both the order `4` instance (feeding
`galerkin_bound`, jets from the delivered `DthIter_Gam_abs_le`/`DzIter_FM_Fstar_abs_le`) and the
order `5` instance (design §2.4, §6) come out of the same proof.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.LocDataExt.SepFactor
import Submission.Work.FTS.LocData.Gam_le_sin_two_rpow
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.Vocab

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocDataExt

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Three one-dimensional limit helpers -/

/-- A function which vanishes eventually in the filter tends to `0`. -/
theorem tendsto_of_eventually_eq_zero {l : Filter ℝ} {g : ℝ → ℝ}
    (h : ∀ᶠ z in l, g z = 0) : Tendsto g l (𝓝 0) :=
  Filter.EventuallyEq.tendsto h

/-- On `z ≥ 1` the square of the radial weight is at most `16`
(`w z = (1+z)²/z² ≤ 4`). -/
theorem w_sq_le_sixteen {z : ℝ} (hz : 1 ≤ z) : (Work.Spaces.w z) ^ 2 ≤ 16 := by
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have h1 : 1 + z ≤ 2 * z := by linarith
  have h2 : (1 + z) ^ 2 ≤ (2 * z) ^ 2 := by nlinarith
  rw [Work.Spaces.w, div_pow]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (z ^ 2) ^ 2)]
  have h3 : ((1 + z) ^ 2) ^ 2 ≤ ((2 * z) ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
  nlinarith [h3]

/-- The left `z`-trace: if a slot vanishes eventually at `0⁺`, then `z·(·)² → 0` there. -/
theorem tendsto_z_trace_of_eventually_zero {f : Fn} {b a : ℕ} {θ : ℝ}
    (h : ∀ᶠ z in 𝓝[>] 0, Work.Spaces.mixed b a f z θ = 0) :
    Tendsto (fun z => z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2)
      (𝓝[>] 0) (𝓝 0) :=
  tendsto_of_eventually_eq_zero (h.mono (fun z hz => by rw [hz]; ring))

/-- The right `z`-trace: a slot decaying like `C/z` gives `z·(· w)² → 0` at `∞`. -/
theorem tendsto_z_trace_of_le_div {g : ℝ → ℝ} {C Z : ℝ} (hC : 0 ≤ C)
    (h : ∀ z : ℝ, Z ≤ z → |g z| ≤ C / z) :
    Tendsto (fun z => z * (g z * Work.Spaces.w z) ^ 2) Filter.atTop (𝓝 0) := by
  have hup : Tendsto (fun z : ℝ => 16 * C ^ 2 / z) Filter.atTop (𝓝 0) :=
    tendsto_id.const_div_atTop (16 * C ^ 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (f := fun z : ℝ => z * (g z * Work.Spaces.w z) ^ 2) (g := fun _ : ℝ => (0 : ℝ))
    (h := fun z : ℝ => 16 * C ^ 2 / z) tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop (max Z 1)] with z hz
    have hz1 : (1 : ℝ) ≤ z := le_trans (le_max_right _ _) hz
    exact mul_nonneg (le_of_lt (lt_of_lt_of_le zero_lt_one hz1)) (sq_nonneg _)
  · filter_upwards [eventually_ge_atTop (max Z 1)] with z hz
    have hz1 : (1 : ℝ) ≤ z := le_trans (le_max_right _ _) hz
    have hZ : Z ≤ z := le_trans (le_max_left _ _) hz
    have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz1
    have hw := w_sq_le_sixteen hz1
    have hg := h z hZ
    have hg2 : (g z) ^ 2 ≤ (C / z) ^ 2 := by
      have h4 := pow_le_pow_left₀ (abs_nonneg (g z)) hg 2
      rwa [sq_abs] at h4
    calc z * (g z * Work.Spaces.w z) ^ 2 = z * (g z) ^ 2 * (Work.Spaces.w z) ^ 2 := by ring
      _ ≤ z * (C / z) ^ 2 * 16 := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hg2 (le_of_lt hz0)) hw (sq_nonneg _) ?_
          positivity
      _ = 16 * C ^ 2 / z := by
          field_simp <;> ring

/-- The angular traces: a slot dominated by `C·Γ` satisfies both `θ`-boundary limits, because
`Γ ≤ sin(2θ)^{α/5}` and `1 - γ + 2·(α/5) = 3α/10 > 0`. -/
theorem tendsto_sin_gam_trace (α : ℝ) (hα : 0 < α) {C : ℝ} (hC : 0 ≤ C) {v : ℝ → ℝ}
    (h : ∀ θ ∈ Work.Spaces.Iθ, |v θ| ≤ C * Work.Spaces.Gam α θ) :
    Tendsto (fun θ => (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α) * (v θ) ^ 2)
        (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun θ => (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α) * (v θ) ^ 2)
        (𝓝[<] (π / 2)) (𝓝 0) := by
  have hp : (0 : ℝ) < 3 * α / 10 := by linarith
  have hbound : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α) * (v θ) ^ 2
        ≤ C ^ 2 * (Real.sin (2 * θ)) ^ (3 * α / 10) := by
    intro θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hs0 : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hs0' : 0 ≤ Real.sin (2 * θ) := le_of_lt hs0
    obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds α θ hα hθI
    have hGle : Work.Spaces.Gam α θ ≤ (Real.sin (2 * θ)) ^ (α / 5) :=
      Work.FTS.LocData.Gam_le_sin_two_rpow α hα hθI
    have hv : (v θ) ^ 2 ≤ C ^ 2 * (Work.Spaces.Gam α θ) ^ 2 := by
      have h1 := h θ hθI
      have h2 : (|v θ|) ^ 2 ≤ (C * Work.Spaces.Gam α θ) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
      rw [sq_abs, mul_pow] at h2
      exact h2
    have hsq : (Work.Spaces.Gam α θ) ^ 2 ≤ ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 :=
      pow_le_pow_left₀ hG0 hGle 2
    have hrw1 : ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 = (Real.sin (2 * θ)) ^ (2 * α / 5) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs0']
      congr 1
      ring
    have hrw2 : (Real.sin (2 * θ)) ^ (2 * α / 5) * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α)
        = (Real.sin (2 * θ)) ^ (3 * α / 10) := by
      rw [← Real.rpow_add hs0]
      congr 1
      rw [Work.Spaces.gam]
      ring
    calc (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α) * (v θ) ^ 2
        ≤ (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α)
            * (C ^ 2 * (Work.Spaces.Gam α θ) ^ 2) :=
          mul_le_mul_of_nonneg_left hv (Real.rpow_nonneg hs0' _)
      _ = C ^ 2 * ((Work.Spaces.Gam α θ) ^ 2
            * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α)) := by ring
      _ ≤ C ^ 2 * (((Real.sin (2 * θ)) ^ (2 * α / 5))
            * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α)) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg C)
          exact mul_le_mul_of_nonneg_right (le_trans hsq (le_of_eq hrw1))
            (Real.rpow_nonneg hs0' _)
      _ = C ^ 2 * (Real.sin (2 * θ)) ^ (3 * α / 10) := by rw [hrw2]
  have hhalf : (0 : ℝ) < π / 4 := by positivity
  have hlimr : Tendsto (fun θ : ℝ => C ^ 2 * (Real.sin (2 * θ)) ^ (3 * α / 10))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using (Work.FTS.H2.tendsto_sin_rpow_zero_right (3 * α / 10) hp).const_mul (C ^ 2)
  have hliml : Tendsto (fun θ : ℝ => C ^ 2 * (Real.sin (2 * θ)) ^ (3 * α / 10))
      (𝓝[<] (π / 2)) (𝓝 0) := by
    simpa using (Work.FTS.H2.tendsto_sin_rpow_zero_left (3 * α / 10) hp).const_mul (C ^ 2)
  constructor
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (f := fun θ : ℝ => (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α) * (v θ) ^ 2)
      (g := fun _ : ℝ => (0 : ℝ))
      (h := fun θ : ℝ => C ^ 2 * (Real.sin (2 * θ)) ^ (3 * α / 10))
      tendsto_const_nhds hlimr ?_ ?_
    · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hhalf] with θ hθ hθ'
      have hθI : θ ∈ Work.Spaces.Iθ :=
        ⟨le_of_lt hθ, by linarith [hθ'.2, Real.pi_pos]⟩
      exact mul_nonneg
        (Real.rpow_nonneg (Work.FTS.LocData.ZFBase.sin_two_nonneg_Iθ hθI) _) (sq_nonneg _)
    · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hhalf] with θ hθ hθ'
      exact hbound θ ⟨hθ, by linarith [hθ'.2, Real.pi_pos]⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (f := fun θ : ℝ => (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α) * (v θ) ^ 2)
      (g := fun _ : ℝ => (0 : ℝ))
      (h := fun θ : ℝ => C ^ 2 * (Real.sin (2 * θ)) ^ (3 * α / 10))
      tendsto_const_nhds hliml ?_ ?_
    · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsLT (show π / 4 < π / 2 by linarith)]
        with θ hθ hθ'
      have hθI : θ ∈ Work.Spaces.Iθ :=
        ⟨by linarith [hθ'.1, Real.pi_pos], le_of_lt hθ⟩
      exact mul_nonneg
        (Real.rpow_nonneg (Work.FTS.LocData.ZFBase.sin_two_nonneg_Iθ hθI) _) (sq_nonneg _)
    · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsLT (show π / 4 < π / 2 by linarith)]
        with θ hθ hθ'
      exact hbound θ ⟨by linarith [hθ'.1, Real.pi_pos], hθ⟩

/-! ## The boundary traces of the localised datum -/

/-- **The localised datum has vanishing boundary traces in `BdryTraces α k`**, for every order
`k ≤ 5` (the two jet inputs are the only order-dependent data: `hΓ` for the angular limits and
`hF` for the decay of the far factor at `∞`). -/
theorem bdryTraces_locG (α L β : ℝ) (hα : 0 < α) (hL : 1 ≤ L) {k : ℕ} {CΓ CF : ℝ}
    (hCΓ : 0 ≤ CΓ) (hCF : 0 ≤ CF)
    (hΓ : ∀ i ≤ k, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
        ≤ CΓ * Work.Spaces.Gam α θ)
    (hF : ∀ b ≤ k, ∀ z : ℝ, 1 ≤ z → ∀ θ : ℝ,
      |Work.Spaces.DzIter b (fun z _ => Work.FM.Fstar z) z θ| ≤ CF / z) :
    Work.FTS.Nonlin.BdryTraces α k
      (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  intro a b hab
  have hb : b ≤ k := by omega
  have ha : a ≤ k := by omega
  refine ⟨fun θ hθ => ⟨?_, ?_⟩, fun z hz => ?_⟩
  · -- ## the left `z`-trace: `locR` vanishes on `(0, 3/4)`
    apply tendsto_z_trace_of_eventually_zero
      (f := Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α))
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 3 / 4 by norm_num)] with z hz'
    have hev : ∀ᶠ z'' in 𝓝 z, ∀ θ' : ℝ,
        Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α) z'' θ' = 0 := by
      filter_upwards [locR_eventuallyEq_zero (α := α) (L := L) (β := β) (z := z) hLpos
        hz'.1 (by linarith [hz'.2, hL]) hz'.2] with z'' hz''
      intro θ'
      rw [locG_eq_locR_Gam]
      change locR α L β z'' * Work.Spaces.Gam α θ' = 0
      rw [hz'', zero_mul]
    exact Work.FTS.LocData.ZFBase.mixed_eq_zero_of_eventually_zero hev b a
  · -- ## the right `z`-trace: the two radial factors decay like `1/z`
    apply tendsto_z_trace_of_le_div (C := |α / Work.Spaces.c α| * CF * CΓ)
      (Z := max (2 * L) (7 / 4) + 1) (by positivity) ?_
    intro z hz
    have hz2 : 2 * L < z := by
      have h1 : 2 * L ≤ max (2 * L) (7 / 4) := le_max_left _ _
      linarith
    have hz7 : 7 / 4 < z := by
      have h1 : (7 / 4 : ℝ) ≤ max (2 * L) (7 / 4) := le_max_right _ _
      linarith
    have hz1 : (1 : ℝ) ≤ z := by linarith
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    rw [locG_eq_locR_Gam, congrFun (congrFun (mixed_sepGam α (locR α L β) b a) z) θ, abs_mul]
    have hrad : |Work.Spaces.DzIter b (fun z _ => locR α L β z) z θ|
        ≤ |α / Work.Spaces.c α| * (CF / z) := by
      have hev := locR_eventuallyEq_far (α := α) (L := L) (β := β) (z := z) hLpos hz2 hz7
      have hc := DzIter_z_congr_of_eventuallyEq hev b θ
      rw [hc, DzIter_const_mul, abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_left (hF b hb z hz1 θ) (abs_nonneg _)
    have hang : |Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ| ≤ CΓ := by
      have h1 := hΓ a ha θ hθI
      have hG1 : Work.Spaces.Gam α θ ≤ 1 := (Work.Spaces.Gam_bounds α θ hα hθI).2
      calc |Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
          ≤ CΓ * Work.Spaces.Gam α θ := h1
        _ ≤ CΓ * 1 := mul_le_mul_of_nonneg_left hG1 hCΓ
        _ = CΓ := by ring
    calc |Work.Spaces.DzIter b (fun z _ => locR α L β z) z θ|
            * |Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
        ≤ (|α / Work.Spaces.c α| * (CF / z)) * CΓ :=
          mul_le_mul hrad hang (abs_nonneg _) (by positivity)
      _ = (|α / Work.Spaces.c α| * CF * CΓ) / z := by ring
  · -- ## the angular traces: domination by `R·Γ`
    set R : ℝ := |Work.Spaces.DzIter b (fun z _ => locR α L β z) z 0| + 1 with hRdef
    have hR0 : 0 ≤ R := by rw [hRdef]; positivity
    have hdom : ∀ θ' ∈ Work.Spaces.Iθ,
        |Work.Spaces.mixed b a (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) z θ'|
          ≤ (R * CΓ) * Work.Spaces.Gam α θ' := by
      intro θ' hθ'
      rw [locG_eq_locR_Gam, congrFun (congrFun (mixed_sepGam α (locR α L β) b a) z) θ', abs_mul]
      have hR : |Work.Spaces.DzIter b (fun z _ => locR α L β z) z θ'| ≤ R := by
        rw [DzIter_z_only_apply (locR α L β) b z θ', hRdef]
        linarith [abs_nonneg (Work.Spaces.DzIter b (fun z _ => locR α L β z) z 0)]
      have hang := hΓ a ha θ' hθ'
      calc |Work.Spaces.DzIter b (fun z _ => locR α L β z) z θ'|
              * |Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ'|
          ≤ R * (CΓ * Work.Spaces.Gam α θ') := mul_le_mul hR hang (abs_nonneg _) hR0
        _ = (R * CΓ) * Work.Spaces.Gam α θ' := by ring
    exact tendsto_sin_gam_trace α hα (mul_nonneg hR0 hCΓ) hdom

end Work.FTS.LocDataExt
