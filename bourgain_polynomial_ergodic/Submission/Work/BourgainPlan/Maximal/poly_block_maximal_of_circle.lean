import Mathlib
import Submission.Work.BourgainPlan.Maximal.poly_block_defs
import Submission.Work.BourgainPlan.Maximal.poly_block_core_defs
import Submission.Work.BourgainPlan.Maximal.poly_block_cap
import Submission.Work.BourgainPlan.Maximal.poly_block_maximal
import Submission.Work.BourgainPlan.Maximal.poly_cutoff
import Submission.Work.BourgainPlan.Maximal.polyErrNorm_tsum_le
import Submission.Work.BourgainPlan.Maximal.polyBlockCore_eq_weighted
import Submission.Work.BourgainPlan.Maximal.polyBlockT_sep
import Submission.Work.BourgainPlan.Maximal.norm_polyBlockErr_le_actIdx
import Submission.Work.BourgainPlan.Maximal.polyActIdx_card_le_one

namespace Work.BourgainPlan.Maximal

open Finset Function MeasureTheory
open scoped BigOperators ENNReal Topology
open Commons.Analysis.ExponentialSums

/-! ## Auxiliary lemmas for the per-block `ℓ²` maximal estimate -/

/-- The sharp-window radius is the dyadic family radius at index `k*d - 1`. -/
lemma polyDil_inv_eq (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) {k : ℕ} (hk : 1 ≤ k) :
    (polyDil P k)⁻¹ = (2:ℝ)^(-(((k * P.natDegree - 1 : ℕ)) : ℝ) - 1) := by
  rw [poly_cutoff_polyDil_inv]
  have h1 : 1 ≤ k * P.natDegree := le_trans hk (Nat.le_mul_of_pos_right k (by omega))
  have hcast : (((k * P.natDegree - 1 : ℕ)) : ℝ) = (k * P.natDegree : ℝ) - 1 := by
    rw [Nat.cast_sub h1]; push_cast; ring
  rw [hcast]
  have h2 : -((k * P.natDegree : ℝ) - 1) - 1 = -((k * P.natDegree : ℕ) : ℝ) := by push_cast; ring
  rw [h2, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]

/-- The profile-replacement error multiplier agrees with the block error on `(0,1)`. -/
lemma polyErrMult_eq_blockErr {P : Polynomial ℤ} {m K : ℕ} {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    polyErrMult P m K θ = polyBlockErr P m K θ := by
  rw [polyErrMult, if_pos ⟨hθ0, hθ1⟩]

/-- The cut error multiplier agrees with the block error on `(0,1)` above the cutoff. -/
lemma polyErrMultCut_eq {P : Polynomial ℤ} {m K₀ K : ℕ} {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hK : K₀ ≤ K) : polyErrMultCut P m K₀ K θ = polyBlockErr P m K θ := by
  rw [polyErrMultCut, if_pos hK, polyErrMult_eq_blockErr hθ0 hθ1]

/-- Cauchy–Schwarz in `ℝ≥0∞` with the convenient constant `2 * card`. -/
lemma sq_sum_le_two_card_mul_sum_sq {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) :
    (∑ i ∈ s, f i) ^ 2 ≤ (2 * (s.card : ℝ≥0∞)) * ∑ i ∈ s, f i ^ 2 := by
  rw [sq, Finset.sum_mul_sum]
  calc ∑ i ∈ s, ∑ j ∈ s, f i * f j
      ≤ ∑ i ∈ s, ∑ j ∈ s, (f i ^ 2 + f j ^ 2) := by
        refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
        calc f i * f j = 1 * (f i * f j) := (one_mul _).symm
          _ ≤ 2 * (f i * f j) := mul_le_mul_of_nonneg_right (by norm_num : (1:ℝ≥0∞) ≤ 2) zero_le
          _ = 2 * f i * f j := by ring
          _ ≤ f i ^ 2 + f j ^ 2 := two_mul_le_sq_add_sq (f i) (f j)
    _ = (2 * (s.card : ℝ≥0∞)) * ∑ i ∈ s, f i ^ 2 := by
        rw [Finset.sum_congr rfl (fun i _ => Finset.sum_add_distrib), Finset.sum_add_distrib]
        have h2 : (∑ i ∈ s, ∑ j ∈ s, f i ^ 2) = (s.card : ℝ≥0∞) * ∑ i ∈ s, f i ^ 2 := by
          rw [Finset.sum_congr rfl (fun i _ => by rw [Finset.sum_const, nsmul_eq_mul]),
            ← Finset.mul_sum]
        have h3 : (∑ i ∈ s, ∑ j ∈ s, f j ^ 2) = (s.card : ℝ≥0∞) * ∑ j ∈ s, f j ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
        rw [h2, h3]; ring

/-- The numerical comparison behind the final constant. -/
lemma poly_block_const_key (x b d M : ℝ) (hx : 0 ≤ x) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hM : 1 ≤ M) : 12*x^2 + 3*b^2*M^2 + 6*d^2 ≤ (3*(2*x+b+d)+1)^2 * M^2 := by
  have hM1 : 0 ≤ M := by linarith
  have hM2 : 1 ≤ M^2 := by nlinarith
  have hM20 : 0 ≤ M^2 := by linarith
  have hS : (2*x)^2 + b^2 + d^2 ≤ (2*x+b+d)^2 := by nlinarith
  have h9 : 9*((2*x)^2 + b^2 + d^2) ≤ (3*(2*x+b+d)+1)^2 := by nlinarith
  have step1 : 9*((2*x)^2 + b^2 + d^2) * M^2 ≤ (3*(2*x+b+d)+1)^2 * M^2 :=
    mul_le_mul_of_nonneg_right h9 hM20
  have step2 : 12*x^2 + 3*b^2*M^2 + 6*d^2 ≤ 9*((2*x)^2 + b^2 + d^2) * M^2 := by
    nlinarith [sq_nonneg x, sq_nonneg b, sq_nonneg d, hM2]
  linarith [step1, step2]

/-- **The per-block `ℓ²` maximal estimate for the general-polynomial model.**  There is `C > 0` such that for every dyadic block `m`, every finitely supported `g` and every `k`, the block maximal function is bounded by `C · 2^{−mσ}(m+2)² · ‖g‖₂`, `σ = polySig P = 2^{−(d+1)}`.

COMPLETE PROOF PLAN (all ingredients are already proved in the imported modules; the template is `Commons.Analysis.ExponentialSums.pow_block_maximal_of_circle`, `Submission/Commons/Analysis/ExponentialSums/pure_power_kernel_maximal_l2.lean` lines ~2334–2615 — port it, replacing the pure-power ingredients by the `poly_*` ones).

Ingredients (all sorry-free):
* `poly_weight_cap_block`, `polyWeight_cap_Icc` (weight caps), `norm_polyModelQBlock_le_cap` (`‖polyModelQBlock P m (2^k) θ‖ ≤ B·2^{−mσ}`), `polyErrNorm_tsum_le` (`∀ q a l θ, ∑'_K polyErrNorm P q a l K θ ≤ ofReal CN`), `poly_cutoff` (`∃ K₁ ≥ 4, ∀ m k, K₁ + 4m ≤ k →` containment + smallness + separation), `weighted_core_maximal H`, `polyBlockCore_eq_weighted`, `polyBlockT_sep`, `polyActIdx_card_le_one`, `norm_polyBlockErr_le_actIdx`, `poly_blockErr_tsum_sq_le`, `polyErrMultCut`/`polyErrMultCut_hsum`/`polyErrMultCut_maximal_le`, `lintegral_polyTkBlock_sq_le`, `log_polyBlockT_le`, `polyTkBlockMax_eq_zero_of_lt`, `polyDil_inv_eq`, `enorm_eq_ofReal_norm'''`.

Structure.  Fix `m, g, s, hgs`; set `K₀ := K₁ + 4m`, `j₀ := K₀*d − 1`, `cap := Az·2^{−mσ}` (`Az` from `polyWeight_cap_Icc`), `δ := 1/(c²4^{m+1})`, `E := Az·(CN+1)·2^{−mσ}`, and
`Pg θ := ∑_{n∈s} g n · e(nθ)`, `Ef x θ := e(−xθ)`,
`CoreFam j x := ∫_0^1 (if j₀ ≤ j then ∑_{p∈polyBlockT P m} p.2·perNbhd p.1 (2^{−j−1}) θ else 0)·Pg θ·Ef x θ`,
`ErrFam K x := ∫_0^1 polyErrMultCut P m K₀ K θ·Pg θ·Ef x θ`,
`CrudeSum x := ∑_{K ∈ Ico (4m) K₀} ‖polyTkBlockMax P g s m K x‖ₑ`.

(1) Pointwise: `(⨆_k ‖polyTkBlockMax … k x‖ₑ) ≤ CrudeSum x + (⨆_j ‖CoreFam j x‖ₑ) + (⨆_K ‖ErrFam K x‖ₑ)`.  For `k < 4m` the operator vanishes (`polyTkBlockMax_eq_zero_of_lt`); for `4m ≤ k < K₀` it is dominated by `CrudeSum`; for `k ≥ K₀`, `polyTkBlockMax P g s m k x = CoreFam (k*d−1) x + ErrFam k x`, proved from `polyBlockErr`'s definition (`conj(polyModelQBlock) = polyBlockCore + polyBlockErr` for `4m+4 ≤ k`) together with `polyBlockCore_eq_weighted` (using the cutoff's smallness and `polyDil_inv_eq`: the sharp radius `(polyDil P k)⁻¹ = 2^{−(k*d−1)−1}` is the family radius) and `polyErrMultCut_eq` on `(0,1)`; use `intervalIntegral.integral_add`/`integral_congr`/`eq_of_eq_Ioo` and `enorm_add_le`.

(2) Crude bound: `∫⁻ (CrudeSum x)² ≤ ofReal((K₁ : ℝ)²·B²·(2^{−mσ})²)·I` where `I := ∫⁻‖g‖ₑ²`: Cauchy–Schwarz `sq_sum_le_card_mul_sum_sq` over the `K₁` scales of `Finset.Ico (4m) K₀`, then `lintegral_finsetSum` and `lintegral_polyTkBlock_sq_le` with the cap `B·2^{−mσ}` from `norm_polyModelQBlock_le_cap`.

(3) Core: `hCw (polyBlockT P m) cap δ hδpos hcap0 (weight bound from polyWeight_cap_Icc) (polyBlockT_sep P hc m) j₀ h2pos h3` applied to `g, s, hgs` gives exactly `∫⁻(⨆_j ‖CoreFam j x‖ₑ)² ≤ ofReal((Cw·cap·log(|polyBlockT P m|+2)²)²)·I`; then bound `log(|T|+2) ≤ (c.toNat+5)(m+2)` by `log_polyBlockT_le`.

(4) Error: `polyErrMultCut_maximal_le` (with `A := Az`, `Cf := CN`) gives `∫⁻(⨆_K‖ErrFam K x‖ₑ)² ≤ ofReal(2E²)·I`.

(5) Combine with `(a+b+c)² ≤ 3(a²+b²+c²)` in `ℝ≥0∞` and choose `C := 3(K₁·B + Cw·Az·(c.toNat+5) + Az·(CN+1)) + 1`, using `(m+2)^4 ≥ 1`. -/
theorem poly_block_maximal_of_circle (H : CircleNeighborhoodMaximal) (P : Polynomial ℤ)
    (hc : 0 < P.leadingCoeff) (hd : 2 ≤ P.natDegree) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∫⁻ x : ℤ, (⨆ k : ℕ, ‖polyTkBlockMax P g s m k x‖ₑ) ^ (2:ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (2:ℝ)^(-(m:ℝ) * polySig P) * ((m:ℝ) + 2) ^ 2) ^ 2 *
          ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
  obtain ⟨Cw, hCwpos, hCw⟩ := weighted_core_maximal H
  obtain ⟨Aw, hAwpos, hAw⟩ := polyWeight_cap_Icc P hc hd
  obtain ⟨B, hBpos, hBcap⟩ := norm_polyModelQBlock_le_cap P hc hd
  obtain ⟨CN, hCNpos, hCN⟩ := polyErrNorm_tsum_le P hd
  obtain ⟨K₁, hK₁4, hcut⟩ := poly_cutoff P hc hd
  set Cval : ℝ := 3 * (2 * (K₁ : ℝ) * B + Cw * Aw * ((P.leadingCoeff.toNat : ℝ) + 5) ^ 2
    + Aw * (CN + 1)) + 1 with hCval
  have hK₁pos : (0:ℝ) < (K₁ : ℝ) := by
    have : (0:ℕ) < K₁ := by omega
    exact_mod_cast this
  have hCvalpos : 0 < Cval := by
    rw [hCval]
    have h1 : (0:ℝ) < 2 * (K₁ : ℝ) * B := by
      have h0 : (0:ℝ) < (2:ℝ) * (K₁ : ℝ) := by linarith
      exact mul_pos h0 hBpos
    have h2 : (0:ℝ) < Cw * Aw * ((P.leadingCoeff.toNat : ℝ) + 5) ^ 2 := by
      have h0 : (0:ℝ) < (P.leadingCoeff.toNat : ℝ) + 5 := by positivity
      exact mul_pos (mul_pos hCwpos hAwpos) (pow_pos h0 2)
    have h3 : (0:ℝ) < Aw * (CN + 1) := mul_pos hAwpos (by linarith)
    linarith
  refine ⟨Cval, hCvalpos, ?_⟩
  intro m g s hgs
  set t : ℝ := (2:ℝ)^(-(m:ℝ) * polySig P) with ht
  set M : ℝ := ((m:ℝ) + 2) ^ 2 with hM
  set cap : ℝ := Aw * t with hcap
  set δ : ℝ := 1 / ((P.leadingCoeff : ℝ)^2 * (4:ℝ)^(m+1)) with hδ
  set E : ℝ := Aw * (CN + 1) * t with hE
  set K₀ : ℕ := K₁ + 4*m with hK₀
  set j₀ : ℕ := K₀ * P.natDegree - 1 with hj₀
  set I : ℝ≥0∞ := ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count with hI
  set Pg : ℝ → ℂ := fun θ => ∑ n ∈ s, g n * Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ))
    with hPg
  set Ef : ℤ → ℝ → ℂ := fun x θ => Complex.exp (-(2*Real.pi*Complex.I*((x:ℤ):ℂ)*(θ:ℂ)))
    with hEf
  set CrudeSum : ℤ → ℝ≥0∞ := fun x => ∑ K ∈ Finset.Ico (4*m) K₀,
    ‖polyTkBlockMax P g s m K x‖ₑ with hCrude
  set CoreFam : ℕ → ℤ → ℂ := fun j x => ∫ θ in (0:ℝ)..1,
    (if j₀ ≤ j then ∑ p ∈ polyBlockT P m, p.2 * perNbhd p.1 ((2:ℝ)^(-(j:ℝ)-1)) θ else 0)
      * Pg θ * Ef x θ with hCoreFam
  set ErrFam : ℕ → ℤ → ℂ := fun K x => ∫ θ in (0:ℝ)..1,
    polyErrMultCut P m K₀ K θ * Pg θ * Ef x θ with hErrFam
  set Kcr : ℝ := 2 * (K₁:ℝ) * B * t with hKcr
  set Kc : ℝ := Cw * Aw * ((P.leadingCoeff.toNat : ℝ) + 5) ^ 2 * t * M with hKc
  have htpos : 0 < t := by rw [ht]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hM1 : 1 ≤ M := by rw [hM]; nlinarith [show (0:ℝ) ≤ (m:ℝ) from Nat.cast_nonneg m]
  have hcap0 : 0 ≤ cap := by rw [hcap]; exact mul_nonneg hAwpos.le htpos.le
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  -- #### the crude bound
  have hcrude : ∫⁻ x : ℤ, (CrudeSum x)^(2:ℝ) ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (Kcr^2) * I := by
    have hcard : (Finset.Ico (4*m) K₀).card = K₁ := by
      rw [Nat.card_Ico, hK₀]; omega
    have hpt : ∀ x : ℤ, (CrudeSum x)^2
        ≤ (2 * (K₁ : ℝ≥0∞)) * ∑ K ∈ Finset.Ico (4*m) K₀,
            ‖polyTkBlockMax P g s m K x‖ₑ^2 := by
      intro x
      rw [hCrude]
      refine le_trans (sq_sum_le_two_card_mul_sum_sq _ _) ?_
      rw [hcard]
    have hsingle : ∀ K ∈ Finset.Ico (4*m) K₀,
        ∫⁻ x : ℤ, ‖polyTkBlockMax P g s m K x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count
          ≤ ENNReal.ofReal ((B * t)^2) * I := by
      intro K hK
      have h1 := lintegral_polyTkBlock_sq_le P g s hgs m K (B := B * t)
        (mul_nonneg hBpos.le htpos.le) (fun θ => hBcap m K θ)
      rw [hI]
      exact h1
    calc ∫⁻ x : ℤ, (CrudeSum x)^(2:ℝ) ∂MeasureTheory.Measure.count
        = ∫⁻ x : ℤ, (CrudeSum x)^2 ∂MeasureTheory.Measure.count :=
          lintegral_congr (fun x => ENNReal.rpow_two _)
      _ ≤ ∫⁻ x : ℤ, (2 * (K₁ : ℝ≥0∞)) * ∑ K ∈ Finset.Ico (4*m) K₀,
            ‖polyTkBlockMax P g s m K x‖ₑ^2 ∂MeasureTheory.Measure.count :=
          lintegral_mono hpt
      _ = (2 * (K₁ : ℝ≥0∞)) * ∫⁻ x : ℤ, ∑ K ∈ Finset.Ico (4*m) K₀,
            ‖polyTkBlockMax P g s m K x‖ₑ^2 ∂MeasureTheory.Measure.count :=
          lintegral_const_mul _ (measurable_of_countable _)
      _ = (2 * (K₁ : ℝ≥0∞)) * ∑ K ∈ Finset.Ico (4*m) K₀,
            ∫⁻ x : ℤ, (‖polyTkBlockMax P g s m K x‖ₑ^2)
              ∂MeasureTheory.Measure.count := by
          rw [lintegral_finsetSum _
            (fun K _ => Measurable.pow_const (measurable_of_countable _) 2)]
      _ = (2 * (K₁ : ℝ≥0∞)) * ∑ K ∈ Finset.Ico (4*m) K₀,
            ∫⁻ x : ℤ, ‖polyTkBlockMax P g s m K x‖ₑ^(2:ℝ)
              ∂MeasureTheory.Measure.count := by
          congr 1
          refine Finset.sum_congr rfl (fun K _ => ?_)
          exact lintegral_congr (fun x => (ENNReal.rpow_two _).symm)
      _ ≤ (2 * (K₁ : ℝ≥0∞)) * ∑ K ∈ Finset.Ico (4*m) K₀,
            ENNReal.ofReal ((B * t)^2) * I :=
          mul_le_mul_right (Finset.sum_le_sum (fun K hK => hsingle K hK)) _
      _ = (2 * (K₁ : ℝ≥0∞)) * ((K₁ : ℝ≥0∞) * (ENNReal.ofReal ((B * t)^2) * I)) := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]
      _ = ((2:ℝ≥0∞) * (K₁:ℝ≥0∞) * (K₁:ℝ≥0∞) * ENNReal.ofReal ((B * t)^2)) * I := by ring
      _ ≤ ENNReal.ofReal (Kcr^2) * I := by
          refine mul_le_mul_left ?_ I
          rw [hKcr]
          calc (2:ℝ≥0∞) * (K₁:ℝ≥0∞) * (K₁:ℝ≥0∞) * ENNReal.ofReal ((B * t)^2)
              = ENNReal.ofReal (2 * (K₁:ℝ) * (K₁:ℝ) * (B * t)^2) := by
                rw [show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by norm_num,
                    show (K₁:ℝ≥0∞) = ENNReal.ofReal (K₁:ℝ) by
                      exact (ENNReal.ofReal_natCast K₁).symm,
                    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
                    ← ENNReal.ofReal_mul (by positivity),
                    ← ENNReal.ofReal_mul (by positivity)]
            _ ≤ ENNReal.ofReal ((2 * (K₁:ℝ) * B * t)^2) :=
                ENNReal.ofReal_le_ofReal (by nlinarith [htpos.le, hBpos.le])
  -- #### the core bound
  have hcapT : ∀ p ∈ polyBlockT P m, ‖p.2‖ ≤ cap := by
    intro p hp
    rw [polyBlockT, Finset.mem_image] at hp
    obtain ⟨u, hu, hup⟩ := hp
    obtain ⟨hb, hs⟩ := Finset.mem_product.mp hu
    rw [Finset.mem_range] at hs
    obtain ⟨⟨q, a⟩, sc⟩ := u
    obtain ⟨hm1, hm2, _, hgcd⟩ := mem_blockPair.mp hb
    rw [← hup, Complex.norm_conj, hcap]
    refine hAw m q a (sc:ℤ) hm1 hm2 hgcd ?_
    rw [Finset.mem_Icc]
    refine ⟨by omega, ?_⟩
    have hcc : ((P.leadingCoeff.toNat : ℕ) : ℤ) = P.leadingCoeff :=
      Int.toNat_of_nonneg (show (0:ℤ) ≤ P.leadingCoeff from le_of_lt hc)
    have hlt : (sc : ℤ) < (P.leadingCoeff.toNat : ℤ) := by exact_mod_cast hs
    rw [hcc] at hlt
    exact le_of_lt hlt
  have h3 : (2:ℝ)^(-(j₀:ℝ)-1) ≤ δ/3 := by
    have h1 : (2:ℝ)^(-(j₀:ℝ)-1) = (polyDil P K₀)⁻¹ := by
      rw [hj₀]
      exact (polyDil_inv_eq P hd (k := K₀) (by simp only [hK₀]; omega)).symm
    rw [h1, hδ]
    exact (hcut m K₀ (le_of_eq hK₀.symm)).2.2
  have hcore_raw := hCw (polyBlockT P m) cap δ hδpos hcap0 hcapT (polyBlockT_sep P hc m) j₀
    (Real.rpow_pos_of_pos (by norm_num) _) h3 g s hgs
  have hlognn : 0 ≤ Real.log (((polyBlockT P m).card : ℝ) + 2) := by
    refine Real.log_nonneg ?_
    have : (0:ℝ) ≤ ((polyBlockT P m).card : ℝ) := Nat.cast_nonneg _
    linarith
  have hlog2 : Real.log (((polyBlockT P m).card : ℝ) + 2)^2
      ≤ (((P.leadingCoeff.toNat : ℝ) + 5) * ((m:ℝ) + 2))^2 := by
    have h := log_polyBlockT_le P (le_of_lt hc) m
    have h2 : (0:ℝ) ≤ ((P.leadingCoeff.toNat : ℝ) + 5) * ((m:ℝ) + 2) := by positivity
    nlinarith [h, hlognn, h2]
  have hcore : ∫⁻ x : ℤ, (⨆ j : ℕ, ‖CoreFam j x‖ₑ)^(2:ℝ) ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (Kc^2) * I := by
    refine le_trans hcore_raw ?_
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) I
    have hnonneg : 0 ≤ Cw * Aw * t := by positivity
    have hkey : Real.log (((polyBlockT P m).card : ℝ) + 2) ^ 2
        ≤ ((P.leadingCoeff.toNat : ℝ) + 5)^2 * M := by
      rw [hM]
      nlinarith [hlog2]
    have hmain : Cw * cap * Real.log (((polyBlockT P m).card : ℝ) + 2) ^ 2
        ≤ Cw * Aw * ((P.leadingCoeff.toNat : ℝ) + 5)^2 * t * M := by
      calc Cw * cap * Real.log (((polyBlockT P m).card : ℝ) + 2) ^ 2
          = (Cw * Aw * t) * Real.log (((polyBlockT P m).card : ℝ) + 2) ^ 2 := by
            rw [hcap]; ring
        _ ≤ (Cw * Aw * t) * (((P.leadingCoeff.toNat : ℝ) + 5)^2 * M) :=
            mul_le_mul_of_nonneg_left hkey hnonneg
        _ = Cw * Aw * ((P.leadingCoeff.toNat : ℝ) + 5)^2 * t * M := by ring
    rw [hKc]
    exact pow_le_pow_left₀ (by positivity) hmain 2
  -- #### the error bound
  have herr : ∫⁻ x : ℤ, (⨆ K : ℕ, ‖ErrFam K x‖ₑ)^(2:ℝ) ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (2 * E^2) * I := by
    refine le_trans (polyErrMultCut_maximal_le P hc hd hAwpos hCNpos hAw hCN hK₁4
      (fun m k hk => (hcut m k hk).1) m g s hgs) ?_
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) I
    rw [hE]
  -- #### structural decomposition of a single block operator
  have hPgm : Measurable Pg := by
    rw [hPg]
    refine Finset.measurable_sum _ (fun n _ => ?_)
    exact measurable_const.mul (by fun_prop)
  have hPgbd : ∀ θ : ℝ, ‖Pg θ‖ ≤ ∑ n ∈ s, ‖g n‖ := by
    intro θ
    rw [hPg]
    calc ‖∑ n ∈ s, g n * Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ))‖
        ≤ ∑ n ∈ s, ‖g n * Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ))‖ :=
          norm_sum_le _ _
      _ = ∑ n ∈ s, ‖g n‖ := by
          refine Finset.sum_congr rfl (fun n _ => ?_)
          rw [norm_mul]
          have hexp : ‖Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ))‖ = 1 := by
            rw [show 2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ)
                  = (((2*Real.pi*(n:ℝ)*θ : ℝ)) : ℂ) * Complex.I by push_cast; ring,
              Complex.norm_exp_ofReal_mul_I]
          rw [hexp, mul_one]
  have hsplit : ∀ (k : ℕ) (x : ℤ), K₀ ≤ k →
      polyTkBlockMax P g s m k x = CoreFam (k * P.natDegree - 1) x + ErrFam k x := by
    intro k x hk
    have hkc : K₁ + 4*m ≤ k := by rw [← hK₀]; exact hk
    have hk4 : 4*m + 4 ≤ k := by omega
    have hk1 : 1 ≤ k := by omega
    have hCbd : ((blockPair m).card : ℝ) * ((Finset.Icc (-1:ℤ) P.leadingCoeff).card : ℝ)
        * (Aw * t) ≤ B * t + ((blockPair m).card : ℝ)
          * ((Finset.Icc (-1:ℤ) P.leadingCoeff).card : ℝ) * (Aw * t) := by
      have h0 : (0:ℝ) ≤ B * t := mul_nonneg hBpos.le htpos.le
      linarith
    have hcorebd : ∀ θ, ‖polyBlockCore P m k θ‖
        ≤ ((blockPair m).card : ℝ) * ((Finset.Icc (-1:ℤ) P.leadingCoeff).card : ℝ)
          * (Aw * t) := fun θ => norm_polyBlockCore_le P m k (Aw * t)
        (mul_nonneg hAwpos.le htpos.le)
        (fun l hl i hi => hAw m i.1 i.2 l (mem_blockPair.mp hi).1 (mem_blockPair.mp hi).2.1
          (mem_blockPair.mp hi).2.2.2 hl) θ
    have hint_core : IntervalIntegrable (fun θ => polyBlockCore P m k θ * Pg θ * Ef x θ)
        volume 0 1 := by
      refine intervalIntegrable_mul_exp (f := fun θ => polyBlockCore P m k θ) (P := Pg)
        (Cf := ((blockPair m).card : ℝ) * ((Finset.Icc (-1:ℤ) P.leadingCoeff).card : ℝ)
          * (Aw * t)) (CP := ∑ n ∈ s, ‖g n‖) (measurable_polyBlockCore P m k) hPgm ?_ hPgbd x
      exact hcorebd
    have hint_err : IntervalIntegrable (fun θ => polyBlockErr P m k θ * Pg θ * Ef x θ)
        volume 0 1 := by
      refine intervalIntegrable_mul_exp (f := fun θ => polyBlockErr P m k θ) (P := Pg)
        (Cf := B * t + ((blockPair m).card : ℝ) * ((Finset.Icc (-1:ℤ) P.leadingCoeff).card : ℝ)
          * (Aw * t)) (CP := ∑ n ∈ s, ‖g n‖) (measurable_polyBlockErr P m k) hPgm ?_ hPgbd x
      intro θ
      rw [polyBlockErr, if_pos hk4]
      exact le_trans (norm_sub_le _ _)
        (add_le_add (by rw [Complex.norm_conj]; exact hBcap m k θ) (hcorebd θ))
    have hstep : polyTkBlockMax P g s m k x
        = ∫ θ in (0:ℝ)..1, ((polyBlockCore P m k θ * Pg θ * Ef x θ)
            + (polyBlockErr P m k θ * Pg θ * Ef x θ)) := by
      rw [polyTkBlockMax]
      refine intervalIntegral.integral_congr (fun θ _ => ?_)
      have h2 : starRingEnd ℂ (polyModelQBlock P m (2^k) θ)
          = polyBlockCore P m k θ + polyBlockErr P m k θ := by
        rw [polyBlockErr, if_pos hk4, add_sub_cancel]
      simp only [hPg, hEf]
      rw [h2]
      simp only [mul_assoc]
      ring
    rw [hstep, intervalIntegral.integral_add hint_core hint_err]
    congr 1
    · rw [hCoreFam]
      refine intervalIntegral_eq_of_eq_Ioo (fun θ hθ0 hθ1 => ?_)
      have h2k : j₀ ≤ k * P.natDegree - 1 := by
        rw [hj₀, hK₀]
        exact Nat.sub_le_sub_right (Nat.mul_le_mul_right _ hkc) 1
      rw [if_pos h2k,
        polyBlockCore_eq_weighted P hc hd ((hcut m k hkc).2.1) θ hθ0 hθ1,
        polyDil_inv_eq P hd hk1]
    · rw [hErrFam]
      refine intervalIntegral_eq_of_eq_Ioo (fun θ hθ0 hθ1 => ?_)
      rw [polyErrMultCut_eq hθ0 hθ1 hk]
  -- #### pointwise sup bound
  have hsup1 : ∀ x : ℤ, (⨆ k : ℕ, ‖polyTkBlockMax P g s m k x‖ₑ)
      ≤ CrudeSum x + (⨆ j : ℕ, ‖CoreFam j x‖ₑ) + (⨆ K : ℕ, ‖ErrFam K x‖ₑ) := by
    intro x
    refine iSup_le (fun k => ?_)
    rcases lt_or_ge k (4*m) with hk | hk
    · rw [polyTkBlockMax_eq_zero_of_lt P g s hk x]
      simp only [enorm_zero]
      exact zero_le
    rcases lt_or_ge k K₀ with hk2 | hk2
    · have hmem : k ∈ Finset.Ico (4*m) K₀ := Finset.mem_Ico.mpr ⟨hk, hk2⟩
      calc ‖polyTkBlockMax P g s m k x‖ₑ ≤ CrudeSum x := by
            show ‖polyTkBlockMax P g s m k x‖ₑ
              ≤ ∑ K ∈ Finset.Ico (4*m) K₀, ‖polyTkBlockMax P g s m K x‖ₑ
            exact Finset.single_le_sum (f := fun K => ‖polyTkBlockMax P g s m K x‖ₑ)
              (fun i _ => zero_le) hmem
        _ ≤ CrudeSum x + (⨆ j : ℕ, ‖CoreFam j x‖ₑ) + (⨆ K : ℕ, ‖ErrFam K x‖ₑ) :=
            le_trans (le_add_of_nonneg_right zero_le) (le_add_of_nonneg_right zero_le)
    · rw [hsplit k x hk2]
      calc ‖CoreFam (k * P.natDegree - 1) x + ErrFam k x‖ₑ
          ≤ ‖CoreFam (k * P.natDegree - 1) x‖ₑ + ‖ErrFam k x‖ₑ := enorm_add_le _ _
        _ ≤ (⨆ j : ℕ, ‖CoreFam j x‖ₑ) + (⨆ K : ℕ, ‖ErrFam K x‖ₑ) :=
            add_le_add (le_iSup (fun j : ℕ => ‖CoreFam j x‖ₑ) (k * P.natDegree - 1))
              (le_iSup (fun K : ℕ => ‖ErrFam K x‖ₑ) k)
        _ ≤ CrudeSum x + (⨆ j : ℕ, ‖CoreFam j x‖ₑ) + (⨆ K : ℕ, ‖ErrFam K x‖ₑ) :=
            add_le_add (le_add_of_nonneg_left (zero_le : 0 ≤ CrudeSum x)) le_rfl
  have hsup2 : ∀ x : ℤ, (⨆ k : ℕ, ‖polyTkBlockMax P g s m k x‖ₑ)^(2:ℝ)
      ≤ 3 * ((CrudeSum x)^(2:ℝ) + (⨆ j : ℕ, ‖CoreFam j x‖ₑ)^(2:ℝ)
          + (⨆ K : ℕ, ‖ErrFam K x‖ₑ)^(2:ℝ)) := by
    intro x
    have hkey : ∀ a b c : ℝ≥0∞, (a+b+c)^2 ≤ 3*(a^2+b^2+c^2) := by
      intro a b c
      have h1 : 2*(a*b) ≤ a^2+b^2 := by
        calc 2*(a*b) = 2*a*b := by ring
          _ ≤ a^2+b^2 := two_mul_le_sq_add_sq a b
      have h2 : 2*(a*c) ≤ a^2+c^2 := by
        calc 2*(a*c) = 2*a*c := by ring
          _ ≤ a^2+c^2 := two_mul_le_sq_add_sq a c
      have h3 : 2*(b*c) ≤ b^2+c^2 := by
        calc 2*(b*c) = 2*b*c := by ring
          _ ≤ b^2+c^2 := two_mul_le_sq_add_sq b c
      calc (a+b+c)^2 = (a^2+b^2+c^2) + (2*(a*b) + (2*(a*c) + 2*(b*c))) := by ring
        _ ≤ (a^2+b^2+c^2) + ((a^2+b^2) + ((a^2+c^2) + (b^2+c^2))) :=
            add_le_add le_rfl (add_le_add h1 (add_le_add h2 h3))
        _ = 3*(a^2+b^2+c^2) := by ring
    have h1 := hsup1 x
    rw [ENNReal.rpow_two, ENNReal.rpow_two, ENNReal.rpow_two, ENNReal.rpow_two]
    calc (⨆ k, ‖polyTkBlockMax P g s m k x‖ₑ)^2
        ≤ (CrudeSum x + (⨆ j : ℕ, ‖CoreFam j x‖ₑ) + (⨆ K : ℕ, ‖ErrFam K x‖ₑ))^2 :=
          pow_le_pow_left₀ zero_le h1 2
      _ ≤ 3 * ((CrudeSum x)^2 + (⨆ j : ℕ, ‖CoreFam j x‖ₑ)^2
            + (⨆ K : ℕ, ‖ErrFam K x‖ₑ)^2) := hkey _ _ _
  -- #### assembly
  have hfin : 3 * (ENNReal.ofReal (Kcr^2) + ENNReal.ofReal (Kc^2) + ENNReal.ofReal (2*E^2))
      ≤ ENNReal.ofReal (Cval * t * M) ^ 2 := by
    have hmain : 3 * (Kcr^2 + Kc^2 + 2*E^2) ≤ (Cval * t * M)^2 := by
      rw [hKcr, hKc, hE, hCval]
      rw [show 3 * ((2 * (K₁:ℝ) * B * t)^2 + (Cw * Aw * ((P.leadingCoeff.toNat:ℝ) + 5)^2 * t * M)^2
            + 2 * (Aw * (CN + 1) * t)^2)
          = (12*((K₁:ℝ)*B)^2 + 3*(Cw * Aw * ((P.leadingCoeff.toNat:ℝ) + 5)^2)^2 * M^2
            + 6*(Aw * (CN + 1))^2) * t^2 by ring]
      rw [show ((3 * (2 * (K₁:ℝ) * B + Cw * Aw * ((P.leadingCoeff.toNat:ℝ) + 5)^2
              + Aw * (CN + 1)) + 1) * t * M)^2
          = ((3*(2*((K₁:ℝ)*B) + Cw * Aw * ((P.leadingCoeff.toNat:ℝ) + 5)^2 + Aw * (CN + 1))
            + 1)^2 * M^2) * t^2 by ring]
      exact mul_le_mul_of_nonneg_right (poly_block_const_key ((K₁:ℝ)*B)
        (Cw * Aw * ((P.leadingCoeff.toNat:ℝ) + 5)^2) (Aw * (CN + 1)) M
        (mul_nonneg (Nat.cast_nonneg _) hBpos.le) (by positivity) (by positivity) hM1)
        (sq_nonneg t)
    calc 3 * (ENNReal.ofReal (Kcr^2) + ENNReal.ofReal (Kc^2) + ENNReal.ofReal (2*E^2))
        = ENNReal.ofReal (3 * (Kcr^2 + Kc^2 + 2*E^2)) := by
          rw [show (3:ℝ≥0∞) = ENNReal.ofReal (3:ℝ) by norm_num,
              ← ENNReal.ofReal_add (by positivity) (by positivity),
              ← ENNReal.ofReal_add (by positivity) (by positivity),
              ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)]
      _ ≤ ENNReal.ofReal ((Cval * t * M)^2) := ENNReal.ofReal_le_ofReal hmain
      _ = ENNReal.ofReal (Cval * t * M) ^ 2 := ENNReal.ofReal_pow (by positivity) 2
  calc ∫⁻ x : ℤ, (⨆ k : ℕ, ‖polyTkBlockMax P g s m k x‖ₑ)^(2:ℝ)
        ∂MeasureTheory.Measure.count
      ≤ ∫⁻ x : ℤ, 3 * ((CrudeSum x)^(2:ℝ) + (⨆ j : ℕ, ‖CoreFam j x‖ₑ)^(2:ℝ)
          + (⨆ K : ℕ, ‖ErrFam K x‖ₑ)^(2:ℝ)) ∂MeasureTheory.Measure.count :=
        lintegral_mono hsup2
    _ = 3 * (∫⁻ x : ℤ, (CrudeSum x)^(2:ℝ) ∂MeasureTheory.Measure.count
          + ∫⁻ x : ℤ, (⨆ j : ℕ, ‖CoreFam j x‖ₑ)^(2:ℝ) ∂MeasureTheory.Measure.count
          + ∫⁻ x : ℤ, (⨆ K : ℕ, ‖ErrFam K x‖ₑ)^(2:ℝ) ∂MeasureTheory.Measure.count) := by
        rw [lintegral_const_mul _ (measurable_of_countable _),
          lintegral_add_left (measurable_of_countable _),
          lintegral_add_left (measurable_of_countable _)]
    _ ≤ 3 * (ENNReal.ofReal (Kcr^2) * I + ENNReal.ofReal (Kc^2) * I
          + ENNReal.ofReal (2*E^2) * I) :=
        mul_le_mul_right (add_le_add (add_le_add hcrude hcore) herr) 3
    _ = 3 * (ENNReal.ofReal (Kcr^2) + ENNReal.ofReal (Kc^2) + ENNReal.ofReal (2*E^2)) * I := by
        ring
    _ ≤ ENNReal.ofReal (Cval * t * M) ^ 2 * I := mul_le_mul_left hfin I

end Work.BourgainPlan.Maximal
