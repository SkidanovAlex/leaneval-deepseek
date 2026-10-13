/-
Copyright: work module for the Elgindi finite-time singularity project.

# Right-endpoint (linear) decay of a weak slice

`Work.FTS.EllipticEst.AngAWeak.corrRightRate`: for `0 < q < 1` and `u` of class `C^∞` on
`(0, π/2)` with `u²·wq q` and `(Lzero1 u)²·wq q` integrable on `Iθ`, the slice vanishes at
least linearly at `π/2` and its derivative is bounded there.

The proof has three layers.

* `cRR_fluxTail`: on `(π/4, π/2)` the flux integrand `cRRflux u = cos·sin 2·Lzero1 u` is
  integrable and its tail from `θ` to `π/2` is `O((π/2-θ)^{(5+q)/2})` (a Young/Cauchy–Schwarz
  estimate for `g = Lzero1 u`, whose half-weighted version lies in `L²` by `hLu2`).
* `cRR_bflux_decomp`: hence `Bflux u θ = Binf + ∫_θ^{π/2} cRRflux u` for a constant `Binf`
  (the fundamental theorem of calculus for `Bflux`, whose derivative is `-cRRflux u`).
* `cRR_binf_zero`: `Binf = 0`.  Otherwise `Bflux` keeps the sign of `Binf` and modulus
  `≥ |Binf|/2` on a left neighbourhood of `π/2`, so `Binf·(Wn u)'` is `≳ δ^{-3}`, forcing
  `|Wn u| ≳ δ^{-2}` and `u²·wq q ≳ δ^{-(2+q)}`, contradicting `hu2` and
  `SRSAux.NotIntegrable`.
* `cRR_wnBound`: with `Binf = 0` we get `|(Wn u)'| ≲ δ^{-1/2}`, integrable at `π/2`, so
  `Wn u` stays bounded; `u = Wn u · sin 2θ` and the product rule give the two conclusions.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.AngAWeak.AngWeakDefs
import Submission.Work.FTS.EllipticEst.AngAWeak.SRSAux.BfluxDeriv
import Submission.Work.FTS.EllipticEst.AngAWeak.SRSAux.WnDeriv
import Submission.Work.FTS.EllipticEst.AngAWeak.SRSAux.TrigCompare
import Submission.Work.FTS.EllipticEst.AngAWeak.SRSAux.NotIntegrable
import Submission.Work.FTS.EllipticEst.AngAWeak.CorrPieces.EndDecayAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ### The flux integrand and elementary trigonometric extractions -/

/-- The flux integrand `s ↦ cos s · sin 2s · Lzero1 u s`, i.e. minus the derivative of
`Bflux u`. -/
def cRRflux (u : ℝ → ℝ) : ℝ → ℝ :=
  fun s => Real.cos s * Real.sin (2 * s) * Work.FTS.EllipticEst.Lzero1 u s

/-- The trigonometric comparisons on `(π/4, π/2)` used throughout, in the form needed here:
positivity, `sin 2θ ≥ (4/π)δ`, the flux denominator bound `cos θ sin²2θ ≤ 4δ³`, and the
lower bound `wq q θ ≥ (2δ)^{-q}` for the weight (`δ = π/2 - θ`). -/
lemma cRR_trig {q : ℝ} (hq0 : 0 < q) {θ : ℝ} (hθ : θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) ∧ 0 < Real.cos θ ∧
      (4 / Real.pi) * (Real.pi / 2 - θ) ≤ Real.sin (2 * θ) ∧
      Real.cos θ * (Real.sin (2 * θ)) ^ 2 ≤ 4 * (Real.pi / 2 - θ) ^ 3 ∧
      (2 * (Real.pi / 2 - θ)) ^ (-q) ≤ wq q θ := by
  obtain ⟨-, h2, -, -, h5, h6, h7, -, -, h10, -, -⟩ := SRSAux.TrigCompare (q := q) hq0 θ hθ
  exact ⟨h5, h6, h2, h10, h7⟩

/-- The reciprocal of the flux denominator, in the `rpow` normalisation used below:
`1/(cos θ sin²2θ) ≤ (π³/32)·δ^{-3}`. -/
lemma cRR_one_div_den {θ : ℝ} (hθ : θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2)) :
    1 / (Real.cos θ * (Real.sin (2 * θ)) ^ 2)
      ≤ (Real.pi ^ 3 / 32) * (Real.pi / 2 - θ) ^ (-3 : ℝ) := by
  have hδ : 0 < Real.pi / 2 - θ := by linarith [hθ.2, Real.pi_pos]
  have h := CorrPieces.one_div_fluxDen_le hθ
  have h3 : (Real.pi / 2 - θ) ^ (-3 : ℝ) = ((Real.pi / 2 - θ) ^ 3)⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hδ) (3 : ℝ), Real.rpow_ofNat]
  rw [h3, div_eq_mul_inv]
  calc 1 / (Real.cos θ * (Real.sin (2 * θ)) ^ 2)
      ≤ (Real.pi ^ 3 / 32) / (Real.pi / 2 - θ) ^ 3 := h
    _ = (Real.pi ^ 3 / 32) * ((Real.pi / 2 - θ) ^ 3)⁻¹ := by rw [div_eq_mul_inv]

/-- `δ^{(5+q)/2}·δ^{-3} = δ^{(q-1)/2}` for `δ > 0`. -/
lemma cRR_delta_rpow_div_cube {q δ : ℝ} (hδ : 0 < δ) :
    δ ^ ((5 + q) / 2) * δ ^ (-3 : ℝ) = δ ^ ((q - 1) / 2) := by
  rw [← Real.rpow_add hδ]
  congr 1
  ring

/-- `∫_a^b u^p = (b^{p+1} - a^{p+1})/(p+1)` for `0 < a ≤ b`, `p ≠ -1`. -/
lemma cRR_integral_rpow {a b p : ℝ} (ha : 0 < a) (hab : a ≤ b) (hp : p ≠ -1) :
    ∫ u in a..b, u ^ p = (b ^ (p + 1) - a ^ (p + 1)) / (p + 1) := by
  have h0 : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab, Set.mem_Icc]
    exact fun h => absurd h.1 (not_le_of_gt ha)
  rw [integral_rpow (Or.inr ⟨hp, h0⟩)]

/-! ### The `L²` datum and the flux tail bound -/

/-- `∫_{(c, π/2)} (π/2-s)^p = (π/2-c)^{p+1}/(p+1)` for `p > -1`. -/
lemma cRR_rpowTailIntegral {c p : ℝ} (hc : c < Real.pi / 2) (hp : -1 < p) :
    MeasureTheory.IntegrableOn (fun s => (Real.pi / 2 - s) ^ p) (Set.Ioo c (Real.pi / 2)) ∧
      (∫ s in Set.Ioo c (Real.pi / 2), (Real.pi / 2 - s) ^ p)
        = (Real.pi / 2 - c) ^ (p + 1) / (p + 1) := by
  have hle : c ≤ Real.pi / 2 := le_of_lt hc
  constructor
  · rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le hle]
    have h0 : IntervalIntegrable (fun x : ℝ => x ^ p) volume (0 : ℝ) (Real.pi / 2 - c) :=
      intervalIntegral.intervalIntegrable_rpow' hp
    have h1 : IntervalIntegrable (fun x : ℝ => x ^ p) volume (Real.pi / 2 - c) (0 : ℝ) := h0.symm
    have h2 := h1.comp_sub_left (Real.pi / 2)
    have h2' : IntervalIntegrable (fun x : ℝ => (Real.pi / 2 - x) ^ p) volume c (Real.pi / 2) := by
      convert h2 using 1 <;> ring
    exact h2'
  · rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [← intervalIntegral.integral_of_le hle]
    rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ p) (Real.pi / 2)]
    rw [show Real.pi / 2 - Real.pi / 2 = (0 : ℝ) by ring]
    rw [integral_rpow (Or.inl hp), Real.zero_rpow (by linarith : p + 1 ≠ 0)]
    ring

/-- **Cauchy–Schwarz/Young tail estimate for the flux integrand.**  With
`h = g · sin(2·)^{-q/2}` of class `L²` on `(π/4, π/2)` (so `g = h·sin(2·)^{q/2}`), the tail
integral `∫_θ^{π/2} cos s · sin 2s · g s` is `O((π/2-θ)^((5+q)/2))`: the factor
`cos s · sin(2s)^{1+q/2}` is `≤ 2^{1+q/2}·δ_s^{2+q/2}`, and Young's inequality with
`λ = δ_θ^{(5+q)/2}` balances `λ·∫h²` against `λ^{-1}δ_θ^{5+q}`. -/
lemma cRR_fluxTailBound {q : ℝ} (hq0 : 0 < q) {g : ℝ → ℝ}
    (hg : MeasureTheory.MemLp
      (fun s => g s * (Real.sin (2 * s)) ^ (-(q / 2))) 2
      (MeasureTheory.volume.restrict (Set.Ioo (Real.pi / 4) (Real.pi / 2)))) :
    MeasureTheory.IntegrableOn (fun s => Real.cos s * Real.sin (2 * s) * g s)
        (Set.Ioo (Real.pi / 4) (Real.pi / 2)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
        |∫ s in Set.Ioo θ (Real.pi / 2), Real.cos s * Real.sin (2 * s) * g s|
          ≤ C * (Real.pi / 2 - θ) ^ ((5 + q) / 2) := by
  have h4q : (-1 : ℝ) < 4 + q := by linarith
  have hπ : 0 < Real.pi := Real.pi_pos
  set A : Set ℝ := Set.Ioo (Real.pi / 4) (Real.pi / 2) with hA
  set h : ℝ → ℝ := fun s => g s * (Real.sin (2 * s)) ^ (-(q / 2)) with hh
  set F : ℝ → ℝ := fun s => Real.cos s * Real.sin (2 * s) * g s with hF
  -- the two pointwise facts on the whole of `(π/4, π/2)`
  have hFs : ∀ s ∈ A, F s = h s * (Real.cos s * (Real.sin (2 * s)) ^ (1 + q / 2)) := by
    intro s hs
    have hsin_pos : 0 < Real.sin (2 * s) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hs.1]) (by linarith [hs.2])
    have hsplit : (Real.sin (2 * s)) ^ (-(q / 2)) * (Real.sin (2 * s)) ^ (1 + q / 2)
        = Real.sin (2 * s) := by
      rw [← Real.rpow_add hsin_pos, show -(q / 2) + (1 + q / 2) = 1 by ring, Real.rpow_one]
    rw [hF, hh]
    calc Real.cos s * Real.sin (2 * s) * g s
        = (g s * ((Real.sin (2 * s)) ^ (-(q / 2))
            * (Real.sin (2 * s)) ^ (1 + q / 2))) * Real.cos s := by rw [hsplit]; ring
      _ = (g s * (Real.sin (2 * s)) ^ (-(q / 2)))
            * (Real.cos s * (Real.sin (2 * s)) ^ (1 + q / 2)) := by ring
  have hK : ∀ s ∈ A, 0 ≤ Real.cos s * (Real.sin (2 * s)) ^ (1 + q / 2) ∧
      Real.cos s * (Real.sin (2 * s)) ^ (1 + q / 2)
        ≤ 2 ^ (1 + q / 2) * (Real.pi / 2 - s) ^ (2 + q / 2) := by
    intro s hs
    have hsin_pos : 0 < Real.sin (2 * s) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hs.1]) (by linarith [hs.2])
    have hcos_pos : 0 < Real.cos s := Real.cos_pos_of_mem_Ioo ⟨by linarith [hs.1], hs.2⟩
    set d : ℝ := Real.pi / 2 - s with hd
    have hd0 : 0 < d := by rw [hd]; linarith [hs.2]
    have hsin_le : Real.sin (2 * s) ≤ 2 * d := by
      have heq : Real.sin (2 * s) = Real.sin (2 * d) := by
        rw [hd, show 2 * (Real.pi / 2 - s) = Real.pi - 2 * s by ring, Real.sin_pi_sub]
      rw [heq]
      exact Real.sin_le (le_of_lt (by linarith : (0 : ℝ) < 2 * d))
    have hcos_eq : Real.cos s = Real.sin d := by rw [hd, Real.sin_pi_div_two_sub]
    have hrpow_le : (Real.sin (2 * s)) ^ (1 + q / 2) ≤ (2 * d) ^ (1 + q / 2) :=
      Real.rpow_le_rpow (le_of_lt hsin_pos) hsin_le (by linarith)
    have hmul : (2 * d) ^ (1 + q / 2) = 2 ^ (1 + q / 2) * d ^ (1 + q / 2) :=
      Real.mul_rpow (by norm_num) (le_of_lt hd0)
    have hdeq : d * d ^ (1 + q / 2) = d ^ (2 + q / 2) := by
      have h7 : d * d ^ (1 + q / 2) = d ^ (1 + q / 2) * d ^ (1 : ℝ) := by
        rw [Real.rpow_one]; ring
      rw [h7, ← Real.rpow_add hd0]
      congr 1
      ring
    refine ⟨mul_nonneg (le_of_lt hcos_pos) (Real.rpow_nonneg (le_of_lt hsin_pos) _), ?_⟩
    calc Real.cos s * (Real.sin (2 * s)) ^ (1 + q / 2)
        = Real.sin d * (Real.sin (2 * s)) ^ (1 + q / 2) := by rw [hcos_eq]
      _ ≤ d * (2 * d) ^ (1 + q / 2) :=
          mul_le_mul (Real.sin_le (le_of_lt hd0)) hrpow_le
            (Real.rpow_nonneg (by linarith) _) (le_of_lt hd0)
      _ = d * (2 ^ (1 + q / 2) * d ^ (1 + q / 2)) := by rw [hmul]
      _ = 2 ^ (1 + q / 2) * (d * d ^ (1 + q / 2)) := by ring
      _ = 2 ^ (1 + q / 2) * d ^ (2 + q / 2) := by rw [hdeq]
  have hsqI : MeasureTheory.IntegrableOn (fun s => (h s) ^ 2) A := hg.integrable_sq
  set H : ℝ := ∫ s in A, (h s) ^ 2 with hH
  have hHnn : 0 ≤ H := by
    rw [hH]
    exact integral_nonneg_of_ae (Eventually.of_forall fun s => sq_nonneg _)
  -- the estimate at an arbitrary left endpoint
  have key : ∀ l : ℝ, Real.pi / 4 ≤ l → l < Real.pi / 2 →
      MeasureTheory.IntegrableOn F (Set.Ioo l (Real.pi / 2)) ∧
        |∫ s in Set.Ioo l (Real.pi / 2), F s|
          ≤ 2 ^ (1 + q / 2) * (H / 2 + 1 / (2 * (5 + q))) * (Real.pi / 2 - l) ^ ((5 + q) / 2) := by
    intro l hl1 hl2
    have ha0 : 0 < Real.pi / 2 - l := by linarith
    set lam : ℝ := (Real.pi / 2 - l) ^ ((5 + q) / 2) with hlam
    have hlam0 : 0 < lam := Real.rpow_pos_of_pos ha0 _
    have hSmeas : MeasurableSet (Set.Ioo l (Real.pi / 2)) := measurableSet_Ioo
    have hsub : Set.Ioo l (Real.pi / 2) ⊆ A := fun s hs => ⟨by linarith [hs.1, hl1], hs.2⟩
    have hsq : MeasureTheory.IntegrableOn (fun s => (h s) ^ 2) (Set.Ioo l (Real.pi / 2)) :=
      hsqI.mono_set hsub
    have hwt := cRR_rpowTailIntegral (c := l) (p := 4 + q) hl2 h4q
    -- the pointwise domination
    have hpt : ∀ s ∈ Set.Ioo l (Real.pi / 2),
        |F s| ≤ 2 ^ (1 + q / 2)
          * (lam / 2 * (h s) ^ 2 + (2 * lam)⁻¹ * (Real.pi / 2 - s) ^ (4 + q)) := by
      intro s hs
      have hsA : s ∈ A := hsub hs
      obtain ⟨hKnn, hKle⟩ := hK s hsA
      have hFs' := hFs s hsA
      set d : ℝ := Real.pi / 2 - s with hd
      have hd0 : 0 < d := by rw [hd]; linarith [hsA.2]
      have hd2 : (d ^ (2 + q / 2)) ^ 2 = d ^ (4 + q) := by
        rw [← Real.rpow_ofNat _ 2, ← Real.rpow_mul (le_of_lt hd0),
          show (2 + q / 2) * 2 = 4 + q by ring]
      have ham : d ^ (2 + q / 2) * |h s| ≤ lam / 2 * (h s) ^ 2 + (2 * lam)⁻¹ * d ^ (4 + q) := by
        have h3 : 0 ≤ (lam * |h s| - d ^ (2 + q / 2)) ^ 2 := sq_nonneg _
        have h4 : |h s| ^ 2 = (h s) ^ 2 := sq_abs _
        have h0 : 2 * (d ^ (2 + q / 2) * |h s|) * lam
            ≤ lam ^ 2 * (h s) ^ 2 + (d ^ (2 + q / 2)) ^ 2 := by
          nlinarith [h3, h4]
        calc d ^ (2 + q / 2) * |h s|
            = (2 * (d ^ (2 + q / 2) * |h s|) * lam) / (2 * lam) := by
              rw [show 2 * (d ^ (2 + q / 2) * |h s|) * lam
                    = (d ^ (2 + q / 2) * |h s|) * (2 * lam) by ring,
                mul_div_cancel_right₀ _ (by positivity : (2 : ℝ) * lam ≠ 0)]
          _ ≤ (lam ^ 2 * (h s) ^ 2 + d ^ (4 + q)) / (2 * lam) := by
              rw [← hd2]
              exact div_le_div_of_nonneg_right h0 (by positivity)
          _ = lam / 2 * (h s) ^ 2 + (2 * lam)⁻¹ * d ^ (4 + q) := by
              rw [add_div, div_eq_mul_inv, mul_inv]
              field_simp
      rw [hFs', abs_mul, abs_of_nonneg hKnn]
      calc |h s| * (Real.cos s * (Real.sin (2 * s)) ^ (1 + q / 2))
          ≤ |h s| * (2 ^ (1 + q / 2) * d ^ (2 + q / 2)) :=
            mul_le_mul_of_nonneg_left hKle (abs_nonneg _)
        _ = 2 ^ (1 + q / 2) * (d ^ (2 + q / 2) * |h s|) := by ring
        _ ≤ 2 ^ (1 + q / 2) * (lam / 2 * (h s) ^ 2 + (2 * lam)⁻¹ * d ^ (4 + q)) :=
            mul_le_mul_of_nonneg_left ham (by positivity)
        _ = 2 ^ (1 + q / 2)
              * (lam / 2 * (h s) ^ 2 + (2 * lam)⁻¹ * (Real.pi / 2 - s) ^ (4 + q)) := by rw [hd]
    have hmaj : MeasureTheory.IntegrableOn
        (fun s => 2 ^ (1 + q / 2)
          * (lam / 2 * (h s) ^ 2 + (2 * lam)⁻¹ * (Real.pi / 2 - s) ^ (4 + q)))
        (Set.Ioo l (Real.pi / 2)) := by
      have h1 : MeasureTheory.Integrable (fun s => lam / 2 * (h s) ^ 2
          + (2 * lam)⁻¹ * (Real.pi / 2 - s) ^ (4 + q))
          (MeasureTheory.volume.restrict (Set.Ioo l (Real.pi / 2))) := by
        have h1' : MeasureTheory.Integrable
            ((fun s => lam / 2 * (h s) ^ 2)
              + fun s => (2 * lam)⁻¹ * (Real.pi / 2 - s) ^ (4 + q))
            (MeasureTheory.volume.restrict (Set.Ioo l (Real.pi / 2))) :=
          (MeasureTheory.Integrable.const_mul hsq (lam / 2)).add
            (MeasureTheory.Integrable.const_mul hwt.1 ((2 * lam)⁻¹))
        exact h1'
      exact MeasureTheory.Integrable.const_mul h1 (2 ^ (1 + q / 2))
    have haesm : MeasureTheory.AEStronglyMeasurable F
        (MeasureTheory.volume.restrict (Set.Ioo l (Real.pi / 2))) := by
      have hHs : MeasureTheory.AEStronglyMeasurable h
          (MeasureTheory.volume.restrict (Set.Ioo l (Real.pi / 2))) :=
        (hg.aestronglyMeasurable).mono_measure (Measure.restrict_mono hsub le_rfl)
      have hKs : MeasureTheory.AEStronglyMeasurable
          (fun s => Real.cos s * (Real.sin (2 * s)) ^ (1 + q / 2))
          (MeasureTheory.volume.restrict (Set.Ioo l (Real.pi / 2))) := by
        have hcont : ContinuousOn (fun s => Real.cos s * (Real.sin (2 * s)) ^ (1 + q / 2))
            (Set.Ioo l (Real.pi / 2)) := by
          refine ContinuousOn.mul Real.continuous_cos.continuousOn ?_
          exact ContinuousOn.rpow_const
            ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn)
            (fun x hx => Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
              (by linarith [hx.1, hl1, hπ]) (by linarith [hx.2, hπ]))))
        exact (hcont.aemeasurable measurableSet_Ioo).aestronglyMeasurable
      refine (hHs.mul hKs).congr ?_
      filter_upwards [ae_restrict_mem hSmeas] with s hs
      exact (hFs s (hsub hs)).symm
    have hpt' : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioo l (Real.pi / 2))),
        |F s| ≤ 2 ^ (1 + q / 2)
          * (lam / 2 * (h s) ^ 2 + (2 * lam)⁻¹ * (Real.pi / 2 - s) ^ (4 + q)) := by
      rw [ae_restrict_iff' hSmeas]
      exact Eventually.of_forall fun s hs => hpt s hs
    have hFint : MeasureTheory.IntegrableOn F (Set.Ioo l (Real.pi / 2)) :=
      MeasureTheory.Integrable.mono' hmaj haesm hpt'
    refine ⟨hFint, ?_⟩
    have hInt2 : ∫ s in Set.Ioo l (Real.pi / 2), |F s|
        ≤ ∫ s in Set.Ioo l (Real.pi / 2), 2 ^ (1 + q / 2)
          * (lam / 2 * (h s) ^ 2 + (2 * lam)⁻¹ * (Real.pi / 2 - s) ^ (4 + q)) :=
      integral_mono_of_nonneg (Eventually.of_forall fun s => abs_nonneg _) hmaj hpt'
    have hvalA : ∫ s in Set.Ioo l (Real.pi / 2),
        2 ^ (1 + q / 2) * (lam / 2 * (h s) ^ 2 + (2 * lam)⁻¹ * (Real.pi / 2 - s) ^ (4 + q))
        = 2 ^ (1 + q / 2) * (lam / 2 * (∫ s in Set.Ioo l (Real.pi / 2), (h s) ^ 2)
            + (2 * lam)⁻¹ * (∫ s in Set.Ioo l (Real.pi / 2), (Real.pi / 2 - s) ^ (4 + q))) := by
      rw [MeasureTheory.integral_const_mul]
      congr 1
      have hadd := MeasureTheory.integral_add
        (MeasureTheory.Integrable.const_mul hsq (lam / 2))
        (MeasureTheory.Integrable.const_mul hwt.1 ((2 * lam)⁻¹))
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hadd
      exact hadd
    have hwt2 : (∫ s in Set.Ioo l (Real.pi / 2), (Real.pi / 2 - s) ^ (4 + q))
        = (Real.pi / 2 - l) ^ (5 + q) / (5 + q) := by
      have h := hwt.2
      rw [show (4 : ℝ) + q + 1 = 5 + q by ring] at h
      exact h
    have hfin : lam / 2 * (∫ s in Set.Ioo l (Real.pi / 2), (h s) ^ 2)
        + (2 * lam)⁻¹ * ((Real.pi / 2 - l) ^ (5 + q) / (5 + q))
        ≤ (H / 2 + 1 / (2 * (5 + q))) * lam := by
      have hpow5 : (Real.pi / 2 - l) ^ (5 + q) = lam ^ 2 := by
        rw [hlam, ← Real.rpow_ofNat _ 2, ← Real.rpow_mul (le_of_lt ha0),
          show (5 + q) / 2 * 2 = 5 + q by ring]
      have hInt_le : ∫ s in Set.Ioo l (Real.pi / 2), (h s) ^ 2 ≤ H := by
        rw [hH]
        exact setIntegral_mono_set hsqI (Eventually.of_forall fun s => sq_nonneg _)
          (Eventually.of_forall fun s hs => hsub hs)
      have heq : (2 * lam)⁻¹ * (lam ^ 2 / (5 + q)) = lam / (2 * (5 + q)) := by
        field_simp
      have h1 : lam / 2 * (∫ s in Set.Ioo l (Real.pi / 2), (h s) ^ 2) ≤ lam / 2 * H :=
        mul_le_mul_of_nonneg_left hInt_le (by positivity)
      have hEq : (H / 2 + 1 / (2 * (5 + q))) * lam = lam / 2 * H + lam / (2 * (5 + q)) := by
        ring
      rw [hpow5, heq]
      linarith [h1]
    calc |∫ s in Set.Ioo l (Real.pi / 2), F s|
        ≤ ∫ s in Set.Ioo l (Real.pi / 2), |F s| := abs_integral_le_integral_abs
      _ ≤ ∫ s in Set.Ioo l (Real.pi / 2), 2 ^ (1 + q / 2)
            * (lam / 2 * (h s) ^ 2 + (2 * lam)⁻¹ * (Real.pi / 2 - s) ^ (4 + q)) := hInt2
      _ = 2 ^ (1 + q / 2) * (lam / 2 * (∫ s in Set.Ioo l (Real.pi / 2), (h s) ^ 2)
            + (2 * lam)⁻¹ * (∫ s in Set.Ioo l (Real.pi / 2), (Real.pi / 2 - s) ^ (4 + q))) :=
          hvalA
      _ = 2 ^ (1 + q / 2) * (lam / 2 * (∫ s in Set.Ioo l (Real.pi / 2), (h s) ^ 2)
            + (2 * lam)⁻¹ * ((Real.pi / 2 - l) ^ (5 + q) / (5 + q))) := by
          rw [hwt2]
      _ ≤ 2 ^ (1 + q / 2) * ((H / 2 + 1 / (2 * (5 + q))) * lam) :=
          mul_le_mul_of_nonneg_left hfin (by positivity)
      _ = 2 ^ (1 + q / 2) * (H / 2 + 1 / (2 * (5 + q)))
            * (Real.pi / 2 - l) ^ ((5 + q) / 2) := by rw [hlam]; ring
  refine ⟨(key (Real.pi / 4) le_rfl (by linarith)).1,
    2 ^ (1 + q / 2) * (H / 2 + 1 / (2 * (5 + q))), ?_, ?_⟩
  · refine mul_nonneg (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)) ?_
    have h1 : 0 < 1 / (2 * (5 + q)) := by positivity
    linarith [hHnn]
  · intro θ hθ
    exact (key θ (le_of_lt hθ.1) hθ.2).2

/-- From the weighted square integrability of `Lzero1 u` on `Iθ`, its half-weighted version
`Lzero1 u · sin(2·)^{-q/2}` is square integrable on `(π/4, π/2)`. -/
lemma cRR_memLp {q : ℝ} (hq0 : 0 < q) {u : ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)))
    (hLu2 : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2 * wq q θ) Work.Spaces.Iθ) :
    MeasureTheory.MemLp
      (fun s => Work.FTS.EllipticEst.Lzero1 u s * (Real.sin (2 * s)) ^ (-(q / 2))) 2
      (MeasureTheory.volume.restrict (Set.Ioo (Real.pi / 4) (Real.pi / 2))) := by
  have hpi := Real.pi_pos
  have hsub : Set.Ioo (Real.pi / 4) (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
    fun x hx => ⟨by linarith [hx.1], le_of_lt hx.2⟩
  have hsubI : Set.Ioo (Real.pi / 4) (Real.pi / 2) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun x hx => ⟨by linarith [hx.1], hx.2⟩
  have hmem : MeasureTheory.IntegrableOn
      (fun s => (Work.FTS.EllipticEst.Lzero1 u s) ^ 2 * (Real.sin (2 * s)) ^ (-q))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := hLu2.mono_set hsub
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun s => Work.FTS.EllipticEst.Lzero1 u s)
      (MeasureTheory.volume.restrict (Set.Ioo (Real.pi / 4) (Real.pi / 2))) :=
    CorrPieces.aesm_Lzero1 hsubI measurableSet_Ioo hsm
  have hwcont : ContinuousOn (fun s : ℝ => (Real.sin (2 * s)) ^ (-(q / 2)))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
    have hbase : ContinuousOn (fun s : ℝ => Real.sin (2 * s))
        (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    exact hbase.rpow_const (fun x hx => Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
      (by linarith [hx.1]) (by linarith [hx.2, hpi]))))
  have hwaesm : MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => (Real.sin (2 * s)) ^ (-(q / 2)))
      (MeasureTheory.volume.restrict (Set.Ioo (Real.pi / 4) (Real.pi / 2))) :=
    hwcont.aestronglyMeasurable measurableSet_Ioo
  exact (MeasureTheory.memLp_two_iff_integrable_sq (hmeas.mul hwaesm)).2 (by
    refine hmem.congr_fun ?_ measurableSet_Ioo
    intro x hx
    have hs : 0 < Real.sin (2 * x) := Real.sin_pos_of_pos_of_lt_pi
      (by linarith [hx.1]) (by linarith [hx.2, hpi])
    have hrhs : (Work.FTS.EllipticEst.Lzero1 u x * (Real.sin (2 * x)) ^ (-(q / 2))) ^ 2
        = (Work.FTS.EllipticEst.Lzero1 u x) ^ 2 * (Real.sin (2 * x)) ^ (-q) := by
      rw [mul_pow]
      congr 1
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (le_of_lt hs)]
      congr 1
      push_cast
      ring
    simp only [Pi.mul_apply]
    rw [hrhs])

/-- **Flux tail bound.**  `cRRflux u` is integrable on `(π/4, π/2)` and its tail at `π/2` is
`O(δ^{(5+q)/2})`. -/
lemma cRR_fluxTail {q : ℝ} (hq0 : 0 < q) {u : ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)))
    (hLu2 : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2 * wq q θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (cRRflux u) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
        |∫ s in Set.Ioo θ (Real.pi / 2), cRRflux u s|
          ≤ C * (Real.pi / 2 - θ) ^ ((5 + q) / 2) :=
  cRR_fluxTailBound hq0 (cRR_memLp hq0 hsm hLu2)

/-! ### The flux decomposition -/

/-- **Flux decomposition.**  `Bflux u` differs from its limit `Binf` at `π/2` by the tail
integral of `cRRflux u`. -/
lemma cRR_bflux_decomp {q : ℝ} (hq0 : 0 < q) {u : ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)))
    (hF : MeasureTheory.IntegrableOn (cRRflux u) (Set.Ioo (Real.pi / 4) (Real.pi / 2))) :
    ∃ Binf : ℝ, ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      Bflux u θ = Binf + ∫ s in Set.Ioo θ (Real.pi / 2), cRRflux u s := by
  refine ⟨Bflux u (Real.pi / 4)
    - ∫ s in Set.Ioo (Real.pi / 4) (Real.pi / 2), cRRflux u s, ?_⟩
  intro θ hθ
  have hpi := Real.pi_pos
  have hle : Real.pi / 4 ≤ θ := le_of_lt hθ.1
  have hIcc : Set.Icc (Real.pi / 4) θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun x hx => ⟨by linarith [hx.1], lt_of_le_of_lt hx.2 hθ.2⟩
  have hu_cont : ContinuousOn u (Set.Icc (Real.pi / 4) θ) :=
    ((hsm 0).continuousOn).mono hIcc
  have hdu_cont : ContinuousOn (deriv u) (Set.Icc (Real.pi / 4) θ) :=
    ((hsm 2).continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).mono hIcc
  have hBflux_cont : ContinuousOn (Bflux u) (Set.Icc (Real.pi / 4) θ) := by
    unfold Bflux
    fun_prop
  have hderiv : ∀ x ∈ Set.Ioo (Real.pi / 4) θ, HasDerivAt (Bflux u) (-(cRRflux u x)) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [hx.1], lt_trans hx.2 hθ.2⟩
    simpa only [cRRflux] using SRSAux.BfluxDeriv (hsm 2) hx'
  have hIoo : MeasureTheory.IntegrableOn (cRRflux u) (Set.Ioo (Real.pi / 4) θ) :=
    hF.mono_set (fun x hx => ⟨hx.1, lt_trans hx.2 hθ.2⟩)
  have hcc : IntervalIntegrable (fun s => -(cRRflux u s)) volume (Real.pi / 4) θ := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hle]
    exact MeasureTheory.Integrable.neg hIoo
  have hftc := (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle
    hBflux_cont hderiv hcc).symm
  rw [intervalIntegral.integral_neg] at hftc
  -- split the full integral at `θ`
  have hdisj : Disjoint (Set.Ioc (Real.pi / 4) θ) (Set.Ioo θ (Real.pi / 2)) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    exact absurd hx2.1 (not_lt_of_ge hx1.2)
  have hsub1 : Set.Ioc (Real.pi / 4) θ ⊆ Set.Ioo (Real.pi / 4) (Real.pi / 2) :=
    fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hθ.2⟩
  have hsub2 : Set.Ioo θ (Real.pi / 2) ⊆ Set.Ioo (Real.pi / 4) (Real.pi / 2) :=
    fun x hx => ⟨lt_trans hθ.1 hx.1, hx.2⟩
  have hsplit : ∫ s in Set.Ioo (Real.pi / 4) (Real.pi / 2), cRRflux u s
      = (∫ s in Set.Ioc (Real.pi / 4) θ, cRRflux u s)
        + ∫ s in Set.Ioo θ (Real.pi / 2), cRRflux u s := by
    rw [← Set.Ioc_union_Ioo_eq_Ioo hle hθ.2]
    exact MeasureTheory.setIntegral_union hdisj measurableSet_Ioo
      (hF.mono_set hsub1) (hF.mono_set hsub2)
  have hIntEq : ∫ s in (Real.pi / 4)..θ, cRRflux u s
      = ∫ s in Set.Ioc (Real.pi / 4) θ, cRRflux u s :=
    intervalIntegral.integral_of_le hle
  have key : Bflux u θ - Bflux u (Real.pi / 4)
      = -(∫ s in Set.Ioc (Real.pi / 4) θ, cRRflux u s) := by
    rw [← hIntEq]
    linarith [hftc]
  have key2 : Bflux u θ
      = Bflux u (Real.pi / 4) - (∫ s in Set.Ioc (Real.pi / 4) θ, cRRflux u s) := by
    linarith [key]
  rw [key2, hsplit]
  ring

/-! ### Vanishing of the flux limit -/

/-- **The flux limit vanishes.**  If `|Bflux u θ - Binf| ≤ C δ^{(5+q)/2}` on `(π/4, π/2)` and
`u²·wq q` is integrable then `Binf = 0`. -/
lemma cRR_binf_zero {q : ℝ} (hq0 : 0 < q) {u : ℝ → ℝ} {Binf C : ℝ} (hC : 0 ≤ C)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)))
    (hu2 : MeasureTheory.IntegrableOn
      (fun θ => (u θ) ^ 2 * wq q θ) Work.Spaces.Iθ)
    (hdec : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      Bflux u θ = Binf + ∫ s in Set.Ioo θ (Real.pi / 2), cRRflux u s)
    (ht : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      |∫ s in Set.Ioo θ (Real.pi / 2), cRRflux u s|
        ≤ C * (Real.pi / 2 - θ) ^ ((5 + q) / 2)) :
    Binf = 0 := by
  by_contra hne
  have hpi := Real.pi_pos
  have hBpos : 0 < |Binf| := abs_pos.mpr hne
  have hBhalf : 0 < |Binf| / 2 := by linarith
  set r : ℝ := (5 + q) / 2 with hr
  have hrpos : 0 < r := by rw [hr]; linarith
  -- a first scale on which the tail is below `|Binf|/2`
  set δ₁ : ℝ := min (Real.pi / 8) (((|Binf| / 2) / (C + 1)) ^ (1 / r)) with hδ₁
  have hApos : 0 < (|Binf| / 2) / (C + 1) := by positivity
  have hδ₁pos : 0 < δ₁ := by
    rw [hδ₁]
    exact lt_min (by positivity) (Real.rpow_pos_of_pos hApos _)
  have hδ₁lt : δ₁ < Real.pi / 4 := by
    rw [hδ₁]
    have h := min_le_left (Real.pi / 8) (((|Binf| / 2) / (C + 1)) ^ (1 / r))
    linarith [Real.pi_pos]
  have hδ₁le : δ₁ ≤ ((|Binf| / 2) / (C + 1)) ^ (1 / r) := by
    rw [hδ₁]; exact min_le_right _ _
  have hpow : (((|Binf| / 2) / (C + 1)) ^ (1 / r)) ^ r = (|Binf| / 2) / (C + 1) := by
    rw [← Real.rpow_mul (le_of_lt hApos)]
    rw [show (1 / r) * r = 1 by field_simp]
    exact Real.rpow_one _
  have hδ₁ineq : C * δ₁ ^ r < |Binf| / 2 := by
    have h1 : δ₁ ^ r ≤ (|Binf| / 2) / (C + 1) := by
      calc δ₁ ^ r ≤ (((|Binf| / 2) / (C + 1)) ^ (1 / r)) ^ r :=
            Real.rpow_le_rpow (le_of_lt hδ₁pos) hδ₁le (le_of_lt hrpos)
        _ = (|Binf| / 2) / (C + 1) := hpow
    calc C * δ₁ ^ r ≤ C * ((|Binf| / 2) / (C + 1)) := mul_le_mul_of_nonneg_left h1 hC
      _ = (C / (C + 1)) * (|Binf| / 2) := by ring
      _ < |Binf| / 2 := by
          apply mul_lt_of_lt_one_left hBhalf
          rw [div_lt_one (by positivity)]
          linarith
  -- the reference point and the second scale
  set θs : ℝ := Real.pi / 2 - δ₁ / 2 with hθs
  have hθsδ : Real.pi / 2 - θs = δ₁ / 2 := by rw [hθs]; ring
  set S : ℝ := (δ₁ / 2) ^ (-2 : ℝ) with hS
  set X : ℝ := (|Binf| / 32) / ((|Binf| / 16) * S + |Wn u θs| + 1) with hX
  have hXpos : 0 < X := by rw [hX]; positivity
  set δ₂ : ℝ := min (δ₁ / 4) (Real.sqrt X) with hδ₂
  have hδ₂pos : 0 < δ₂ := by
    rw [hδ₂]
    exact lt_min (by linarith) (Real.sqrt_pos.mpr hXpos)
  have hδ₂le : δ₂ ≤ δ₁ / 4 := by rw [hδ₂]; exact min_le_left _ _
  have hδ₂leX : δ₂ ≤ Real.sqrt X := by rw [hδ₂]; exact min_le_right _ _
  have hδ₂lt : δ₂ < Real.pi / 8 := by linarith
  -- the contradiction at the level of integrability
  refine absurd ?_ (SRSAux.NotIntegrable (p := -(2 + q)) (t := δ₂)
    (by linarith) hδ₂pos)
  have hS₂sub : Set.Ioo (Real.pi / 2 - δ₂) (Real.pi / 2) ⊆ Work.Spaces.Iθ := fun θ hθ =>
    ⟨by linarith [hθ.1, hδ₂lt, hpi], le_of_lt hθ.2⟩
  have hle : ∀ θ ∈ Set.Ioo (Real.pi / 2 - δ₂) (Real.pi / 2),
      ((|Binf| / (8 * Real.pi)) ^ 2 * 2 ^ (-q)) * (Real.pi / 2 - θ) ^ (-(2 + q))
        ≤ (u θ) ^ 2 * wq q θ := by
    intro θ hθ
    set d : ℝ := Real.pi / 2 - θ with hd
    have hd0 : 0 < d := by rw [hd]; linarith [hθ.2, hpi]
    have hdle : d < δ₂ := by rw [hd]; linarith [hθ.1]
    have hθmem : θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2) := by
      refine ⟨?_, hθ.2⟩
      have h1 : Real.pi / 2 - δ₂ < θ := hθ.1
      have h2 : δ₂ ≤ Real.pi / 8 := le_of_lt hδ₂lt
      linarith
    obtain ⟨hsinpos, hcospos, hsinlow, hden_up, hwlow⟩ := cRR_trig hq0 hθmem
    -- the tail is small, so `Bflux` has the sign of `Binf` and modulus `≥ |Binf|/2`
    have hθθs : θs < θ := by
      rw [hθs]
      have h1 : θ > Real.pi / 2 - δ₂ := hθ.1
      have h2 : δ₂ ≤ δ₁ / 4 := hδ₂le
      linarith
    have htailθ : |∫ s in Set.Ioo θ (Real.pi / 2), cRRflux u s| < |Binf| / 2 := by
      have hδx0 : 0 < Real.pi / 2 - θ := by linarith [hθ.2, hpi]
      have hδx1 : Real.pi / 2 - θ ≤ δ₁ := by linarith [hdle, hδ₂le]
      calc |∫ s in Set.Ioo θ (Real.pi / 2), cRRflux u s| ≤ C * (Real.pi / 2 - θ) ^ r :=
            ht θ hθmem
        _ ≤ C * δ₁ ^ r :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (le_of_lt hδx0) hδx1 (le_of_lt hrpos)) hC
        _ < |Binf| / 2 := hδ₁ineq
    -- the pointwise bound on the product `Binf · (Wn u)'`
    have hpt : ∀ x ∈ Set.Ioo θs θ,
        (|Binf| ^ 2 / 8) * (Real.pi / 2 - x) ^ (-3 : ℝ)
          ≤ Binf * (Bflux u x / (Real.cos x * (Real.sin (2 * x)) ^ 2)) := by
      intro x hx
      have hxmem : x ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2) := by
        refine ⟨?_, lt_trans hx.2 hθ.2⟩
        rw [hθs] at hx
        linarith [hx.1, hδ₁lt, hpi]
      obtain ⟨hxsinpos, hxcospos, -, hxden_up, -⟩ := cRR_trig hq0 hxmem
      have hxd0 : 0 < Real.pi / 2 - x := by linarith [hxmem.2, hpi]
      have hxdle : Real.pi / 2 - x ≤ δ₁ := by
        have h1 : x > θs := hx.1
        rw [hθs] at h1
        have h2 : δ₂ ≤ δ₁ / 4 := hδ₂le
        have h3 : x < θ := hx.2
        linarith
      have htailx : |∫ s in Set.Ioo x (Real.pi / 2), cRRflux u s| < |Binf| / 2 := by
        calc |∫ s in Set.Ioo x (Real.pi / 2), cRRflux u s| ≤ C * (Real.pi / 2 - x) ^ r :=
              ht x hxmem
          _ ≤ C * δ₁ ^ r := mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (le_of_lt hxd0) hxdle (le_of_lt hrpos)) hC
          _ < |Binf| / 2 := hδ₁ineq
      have hdenpos : 0 < Real.cos x * (Real.sin (2 * x)) ^ 2 := by positivity
      have hBB : |Binf| ^ 2 / 2 ≤ Binf * Bflux u x := by
        have h1 : Binf * (∫ s in Set.Ioo x (Real.pi / 2), cRRflux u s)
            ≥ -(|Binf| * |∫ s in Set.Ioo x (Real.pi / 2), cRRflux u s|) := by
          have h2 := neg_le_abs (Binf * (∫ s in Set.Ioo x (Real.pi / 2), cRRflux u s))
          rw [abs_mul] at h2
          linarith [h2]
        have h3 : |Binf| * |∫ s in Set.Ioo x (Real.pi / 2), cRRflux u s|
            ≤ |Binf| * (|Binf| / 2) :=
          mul_le_mul_of_nonneg_left htailx.le (abs_nonneg _)
        have h4 : Binf * Binf = |Binf| ^ 2 := by rw [← sq, ← sq_abs Binf]
        rw [hdec x hxmem]
        nlinarith [h1, h3, h4, sq_nonneg Binf]
      have hstep1 : (|Binf| ^ 2 / 8) * (Real.pi / 2 - x) ^ (-3 : ℝ)
          ≤ (|Binf| ^ 2 / 2) / (Real.cos x * (Real.sin (2 * x)) ^ 2) := by
        have h1 : (|Binf| ^ 2 / 8) * (Real.pi / 2 - x) ^ (-3 : ℝ)
            = (|Binf| ^ 2 / 2) / (4 * (Real.pi / 2 - x) ^ 3) := by
          rw [Real.rpow_neg (le_of_lt hxd0) (3 : ℝ), Real.rpow_ofNat]
          field_simp
          ring
        rw [h1]
        exact div_le_div_of_nonneg_left (by positivity) hdenpos hxden_up
      calc (|Binf| ^ 2 / 8) * (Real.pi / 2 - x) ^ (-3 : ℝ)
          ≤ (|Binf| ^ 2 / 2) / (Real.cos x * (Real.sin (2 * x)) ^ 2) := hstep1
        _ ≤ (Binf * Bflux u x) / (Real.cos x * (Real.sin (2 * x)) ^ 2) :=
            div_le_div_of_nonneg_right hBB hdenpos.le
        _ = Binf * (Bflux u x / (Real.cos x * (Real.sin (2 * x)) ^ 2)) := by
            rw [← mul_div_assoc']
    -- the fundamental theorem of calculus for `Wn u`
    have hWn' : ∀ x ∈ Set.Ioo θs θ,
        HasDerivAt (Wn u) (Bflux u x / (Real.cos x * (Real.sin (2 * x)) ^ 2)) x := by
      intro x hx
      have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
        refine ⟨?_, lt_trans hx.2 hθ.2⟩
        rw [hθs] at hx
        linarith [hx.1, hδ₁lt, hpi]
      exact SRSAux.WnDeriv (hsm 1) hx'
    have hWn_cont : ContinuousOn (Wn u) (Set.Icc θs θ) := by
      have hu_cont : ContinuousOn u (Set.Icc θs θ) :=
        ((hsm 0).continuousOn).mono (fun x hx =>
          ⟨by rw [hθs] at hx; linarith [hx.1, hδ₁lt, hpi], lt_of_le_of_lt hx.2 hθ.2⟩)
      unfold Wn
      refine ContinuousOn.div hu_cont (by fun_prop) ?_
      intro x hx
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
        (by rw [hθs] at hx; linarith [hx.1, hδ₁lt, hpi])
        (by linarith [hx.2, hθ.2, hpi]))
    have hWn'cont : ContinuousOn
        (fun x => Bflux u x / (Real.cos x * (Real.sin (2 * x)) ^ 2)) (Set.Icc θs θ) := by
      have hu_cont : ContinuousOn u (Set.Icc θs θ) :=
        ((hsm 0).continuousOn).mono (fun x hx =>
          ⟨by rw [hθs] at hx; linarith [hx.1, hδ₁lt, hpi], lt_of_le_of_lt hx.2 hθ.2⟩)
      have hdu_cont : ContinuousOn (deriv u) (Set.Icc θs θ) :=
        ((hsm 2).continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).mono
          (fun x hx => ⟨by rw [hθs] at hx; linarith [hx.1, hδ₁lt, hpi],
            lt_of_le_of_lt hx.2 hθ.2⟩)
      have hBc : ContinuousOn (Bflux u) (Set.Icc θs θ) := by
        unfold Bflux
        fun_prop
      refine hBc.div (by fun_prop) (fun x hx => ?_)
      exact ne_of_gt (by
        have h1 : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo
          ⟨by rw [hθs] at hx; linarith [hx.1, hδ₁lt, hpi], lt_of_le_of_lt hx.2 hθ.2⟩
        have h2 : 0 < Real.sin (2 * x) := Real.sin_pos_of_pos_of_lt_pi
          (by rw [hθs] at hx; linarith [hx.1, hδ₁lt, hpi])
          (by linarith [hx.2, hθ.2, hpi])
        positivity)
    have hintW : IntervalIntegrable
        (fun x => Bflux u x / (Real.cos x * (Real.sin (2 * x)) ^ 2)) volume θs θ := by
      have h := hWn'cont
      rw [← Set.uIcc_of_le (le_of_lt hθθs)] at h
      exact h.intervalIntegrable
    have hftc : Wn u θ - Wn u θs
        = ∫ x in θs..θ, Bflux u x / (Real.cos x * (Real.sin (2 * x)) ^ 2) :=
      (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (le_of_lt hθθs) hWn_cont hWn'
        hintW).symm
    -- integrate the pointwise lower bound
    have hInt3 : ∫ x in θs..θ, (Real.pi / 2 - x) ^ (-3 : ℝ) = (1 / 2) * (d ^ (-2 : ℝ) - S) := by
      have h1 : ∫ x in θs..θ, (Real.pi / 2 - x) ^ (-3 : ℝ)
          = ∫ u in (Real.pi / 2 - θ)..(Real.pi / 2 - θs), u ^ (-3 : ℝ) := by
        have h := intervalIntegral.integral_comp_sub_left (fun u : ℝ => u ^ (-3 : ℝ))
          (Real.pi / 2) (a := θs) (b := θ)
        simpa only [Function.comp_def] using h
      rw [h1, ← hd, hθsδ]
      rw [cRR_integral_rpow (a := d) (b := δ₁ / 2) (p := (-3 : ℝ)) hd0
        (by linarith [hdle, hδ₂le]) (by norm_num)]
      rw [show ((-3 : ℝ) + 1) = -2 by norm_num, ← hS]
      ring
    have hintBW : IntervalIntegrable
        (fun x => Binf * (Bflux u x / (Real.cos x * (Real.sin (2 * x)) ^ 2))) volume θs θ := by
      have h := (ContinuousOn.const_mul hWn'cont Binf)
      rw [← Set.uIcc_of_le (le_of_lt hθθs)] at h
      exact h.intervalIntegrable
    have hconst_cont : ContinuousOn
        (fun x => (|Binf| ^ 2 / 8) * (Real.pi / 2 - x) ^ (-3 : ℝ)) (Set.Icc θs θ) := by
      refine ContinuousOn.const_mul ?_ _
      refine ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id) ?_
      intro x hx
      exact Or.inl (ne_of_gt (by linarith [hx.2, hθ.2, hpi]))
    have hintC : IntervalIntegrable
        (fun x => (|Binf| ^ 2 / 8) * (Real.pi / 2 - x) ^ (-3 : ℝ)) volume θs θ := by
      have h := hconst_cont
      rw [← Set.uIcc_of_le (le_of_lt hθθs)] at h
      exact h.intervalIntegrable
    have hIntmono : ∫ x in θs..θ, (|Binf| ^ 2 / 8) * (Real.pi / 2 - x) ^ (-3 : ℝ)
        ≤ ∫ x in θs..θ, Binf * (Bflux u x / (Real.cos x * (Real.sin (2 * x)) ^ 2)) :=
      intervalIntegral.integral_mono_on_of_le_Ioo (le_of_lt hθθs) hintC
        hintBW (fun x hx => hpt x ⟨hx.1, hx.2⟩)
    have hstep : Binf * (Wn u θ - Wn u θs) ≥ (|Binf| ^ 2 / 8) * (1 / 2) * (d ^ (-2 : ℝ) - S) := by
      have hval : ∫ x in θs..θ, (|Binf| ^ 2 / 8) * (Real.pi / 2 - x) ^ (-3 : ℝ)
          = (|Binf| ^ 2 / 8) * (1 / 2) * (d ^ (-2 : ℝ) - S) := by
        rw [intervalIntegral.integral_const_mul, hInt3]
        ring
      have heq : Binf * (Wn u θ - Wn u θs)
          = ∫ x in θs..θ, Binf * (Bflux u x / (Real.cos x * (Real.sin (2 * x)) ^ 2)) := by
        rw [intervalIntegral.integral_const_mul, hftc]
      rw [heq, ← hval]
      exact hIntmono
    -- consequences for `Wn` and `u`
    have hWndiff : (|Binf| / 16) * (d ^ (-2 : ℝ) - S) ≤ |Wn u θ - Wn u θs| := by
      have h2 : |Binf * (Wn u θ - Wn u θs)| / |Binf| = |Wn u θ - Wn u θs| := by
        rw [abs_mul, mul_div_cancel_left₀ _ (ne_of_gt hBpos)]
      have hX : (|Binf| / 16) * (d ^ (-2 : ℝ) - S)
          = ((|Binf| ^ 2 / 8) * (1 / 2) * (d ^ (-2 : ℝ) - S)) / |Binf| := by
        field_simp
        ring
      have hmono : ((|Binf| ^ 2 / 8) * (1 / 2) * (d ^ (-2 : ℝ) - S)) / |Binf|
          ≤ |Binf * (Wn u θ - Wn u θs)| / |Binf| :=
        le_trans (div_le_div_of_nonneg_right hstep (le_of_lt hBpos))
          (div_le_div_of_nonneg_right (le_abs_self _) (le_of_lt hBpos))
      rw [← hX, h2] at hmono
      exact hmono
    have hleX : (|Binf| / 16) * S + |Wn u θs| + 1 ≤ (|Binf| / 32) * d ^ (-2 : ℝ) := by
      have hden : 0 < (|Binf| / 16) * S + |Wn u θs| + 1 := by positivity
      have hd2 : d ^ 2 ≤ X := by
        have hdX : d ≤ Real.sqrt X := le_of_lt (lt_of_lt_of_le hdle hδ₂leX)
        have h1 : d * d ≤ Real.sqrt X * Real.sqrt X := mul_self_le_mul_self hd0.le hdX
        have h2 : Real.sqrt X * Real.sqrt X = X := by
          rw [← pow_two, Real.sq_sqrt (le_of_lt hXpos)]
        have h3 : d * d ≤ X := by linarith only [h1, h2]
        simpa only [pow_two] using h3
      have hXeq : X = (|Binf| / 32) / ((|Binf| / 16) * S + |Wn u θs| + 1) := hX
      have hd2' : d ^ 2 * ((|Binf| / 16) * S + |Wn u θs| + 1) ≤ |Binf| / 32 := by
        have h := hd2
        rw [hXeq, le_div_iff₀ hden] at h
        exact h
      calc (|Binf| / 16) * S + |Wn u θs| + 1
          ≤ (|Binf| / 32) / d ^ 2 := by
            rw [le_div_iff₀ (by positivity : (0 : ℝ) < d ^ 2)]
            linarith [hd2']
        _ = (|Binf| / 32) * d ^ (-2 : ℝ) := by
            rw [Real.rpow_neg (le_of_lt hd0) (2 : ℝ), Real.rpow_ofNat, div_eq_mul_inv]
    have hWnlarge : (|Binf| / 32) * d ^ (-2 : ℝ) ≤ |Wn u θ| := by
      have h5 : |Wn u θ| ≥ |Wn u θ - Wn u θs| - |Wn u θs| := by
        have h := abs_add_le (Wn u θ) (-(Wn u θs))
        rw [abs_neg] at h
        rw [show Wn u θ + -(Wn u θs) = Wn u θ - Wn u θs by ring] at h
        linarith only [h]
      linarith [hWndiff, h5, hleX]
    have hu_low : |Binf| / (8 * Real.pi) * d ^ (-1 : ℝ) ≤ |u θ| := by
      have hueq : |u θ| = |Wn u θ| * Real.sin (2 * θ) := by
        rw [show u θ = Wn u θ * Real.sin (2 * θ) from
          (div_mul_cancel₀ (u θ) (ne_of_gt hsinpos)).symm, abs_mul, abs_of_pos hsinpos]
      rw [hueq]
      have hs : (4 / Real.pi) * d ≤ Real.sin (2 * θ) := by rw [hd]; exact hsinlow
      have h1 : (|Binf| / 32) * d ^ (-2 : ℝ) * ((4 / Real.pi) * d)
          ≤ |Wn u θ| * Real.sin (2 * θ) :=
        mul_le_mul hWnlarge hs (by positivity) (by positivity)
      have h2 : (|Binf| / 32) * d ^ (-2 : ℝ) * ((4 / Real.pi) * d)
          = |Binf| / (8 * Real.pi) * d ^ (-1 : ℝ) := by
        rw [Real.rpow_neg (le_of_lt hd0) (2 : ℝ), Real.rpow_ofNat,
          Real.rpow_neg (le_of_lt hd0) (1 : ℝ), Real.rpow_one]
        field_simp
        ring
      linarith [h1, h2.le, h2.ge]
    -- assemble the pointwise bound
    have hsplit2 : d ^ (-(2 + q)) = d ^ (-2 : ℝ) * d ^ (-q) := by
      rw [← Real.rpow_add hd0]
      congr 1
      ring
    have hAB : (|Binf| / (8 * Real.pi)) ^ 2 * d ^ (-2 : ℝ) ≤ (u θ) ^ 2 := by
      have h1 : u θ ^ 2 = |u θ| ^ 2 := by rw [sq_abs]
      have h3 : (|Binf| / (8 * Real.pi) * d ^ (-1 : ℝ)) ^ 2 ≤ |u θ| ^ 2 := by
        have h := mul_self_le_mul_self
          (by positivity : (0 : ℝ) ≤ |Binf| / (8 * Real.pi) * d ^ (-1 : ℝ)) hu_low
        simpa only [pow_two] using h
      have h4 : (|Binf| / (8 * Real.pi) * d ^ (-1 : ℝ)) ^ 2
          = (|Binf| / (8 * Real.pi)) ^ 2 * d ^ (-2 : ℝ) := by
        have hd1 : d ^ (-1 : ℝ) = d⁻¹ := by
          rw [Real.rpow_neg (le_of_lt hd0) (1 : ℝ), Real.rpow_one]
        have hd2 : d ^ (-2 : ℝ) = (d ^ 2)⁻¹ := by
          rw [Real.rpow_neg (le_of_lt hd0) (2 : ℝ), Real.rpow_ofNat]
        rw [hd1, hd2, mul_pow, inv_pow]
      rw [← h4, h1]
      exact h3
    calc ((|Binf| / (8 * Real.pi)) ^ 2 * 2 ^ (-q)) * (Real.pi / 2 - θ) ^ (-(2 + q))
        = ((|Binf| / (8 * Real.pi)) ^ 2 * d ^ (-2 : ℝ)) * ((2 * d) ^ (-q)) := by
          rw [hsplit2, hd, Real.mul_rpow (by norm_num) (le_of_lt hd0)]
          ring
      _ ≤ (u θ) ^ 2 * wq q θ :=
          mul_le_mul hAB hwlow (by positivity) (sq_nonneg _)
  -- assemble the integrability contradiction
  have hminor : MeasureTheory.IntegrableOn
      (fun θ => ((|Binf| / (8 * Real.pi)) ^ 2 * 2 ^ (-q)) * (Real.pi / 2 - θ) ^ (-(2 + q)))
      (Set.Ioo (Real.pi / 2 - δ₂) (Real.pi / 2)) := by
    refine MeasureTheory.Integrable.mono' (hu2.mono_set hS₂sub) ?_ ?_
    · have hbase : ContinuousOn (fun s : ℝ => Real.pi / 2 - s)
          (Set.Ioo (Real.pi / 2 - δ₂) (Real.pi / 2)) :=
        continuousOn_const.sub continuousOn_id
      have hcont : ContinuousOn (fun s : ℝ => (Real.pi / 2 - s) ^ (-(2 + q)))
          (Set.Ioo (Real.pi / 2 - δ₂) (Real.pi / 2)) :=
        hbase.rpow_const (fun x hx => Or.inl (ne_of_gt (by linarith [hx.2, hpi])))
      exact (hcont.const_mul _).aestronglyMeasurable measurableSet_Ioo
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      have hx' : 0 ≤ ((|Binf| / (8 * Real.pi)) ^ 2 * 2 ^ (-q)) * (Real.pi / 2 - x) ^ (-(2 + q)) :=
        mul_nonneg (by positivity) (Real.rpow_nonneg (by linarith [hx.2, hpi]) _)
      rw [Real.norm_eq_abs, abs_of_nonneg hx']
      exact hle x hx
  have hone : MeasureTheory.IntegrableOn
      (fun θ => (Real.pi / 2 - θ) ^ (-(2 + q)))
      (Set.Ioo (Real.pi / 2 - δ₂) (Real.pi / 2)) := by
    have hc : 0 < (|Binf| / (8 * Real.pi)) ^ 2 * 2 ^ (-q) := by positivity
    have h := MeasureTheory.Integrable.const_mul hminor ((|Binf| / (8 * Real.pi)) ^ 2 * 2 ^ (-q))⁻¹
    refine h.congr ?_
    filter_upwards with x
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul]
  exact hone

/-! ### Boundedness of the amplitude -/

/-- **The amplitude is bounded.**  If `|Bflux u| ≤ C δ^{(5+q)/2}` on `(π/4, π/2)` then
`Wn u = u/sin 2θ` is bounded there: `|(Wn u)'| ≤ (Cπ³/32)δ^{-1/2}`, whose integral over
`(π/4, π/2)` is at most `2`. -/
lemma cRR_wnBound {q : ℝ} (hq0 : 0 < q) {u : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)))
    (hB : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      |Bflux u θ| ≤ C * (Real.pi / 2 - θ) ^ ((5 + q) / 2)) :
    ∃ K : ℝ, 0 < K ∧ ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2), |Wn u θ| ≤ K := by
  have hpi := Real.pi_pos
  have hCnn : (0 : ℝ) ≤ (Real.pi ^ 3 / 32) * C := by positivity
  refine ⟨|Wn u (Real.pi / 4)| + ((Real.pi ^ 3 / 32) * C) * 2 + 1, by positivity, ?_⟩
  intro θ hθ
  have hpt : ∀ x ∈ Set.Ioo (Real.pi / 4) θ,
      |Bflux u x / (Real.cos x * (Real.sin (2 * x)) ^ 2)|
        ≤ ((Real.pi ^ 3 / 32) * C) * (Real.pi / 2 - x) ^ (-(1 / 2) : ℝ) := by
    intro x hx
    have hxmem : x ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2) := ⟨hx.1, lt_trans hx.2 hθ.2⟩
    have hxsinpos : 0 < Real.sin (2 * x) := Real.sin_pos_of_pos_of_lt_pi
      (by linarith [hx.1]) (by linarith [hx.2, hθ.2, hpi])
    have hxcospos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hx.1], lt_trans hx.2 hθ.2⟩
    have hδ : 0 < Real.pi / 2 - x := by linarith [hxmem.2, hpi]
    have hδ1 : Real.pi / 2 - x ≤ 1 := by linarith [hxmem.1, Real.pi_le_four]
    have hdenpos : 0 < Real.cos x * (Real.sin (2 * x)) ^ 2 := by positivity
    have h1 : |Bflux u x / (Real.cos x * (Real.sin (2 * x)) ^ 2)|
        = |Bflux u x| * (1 / (Real.cos x * (Real.sin (2 * x)) ^ 2)) := by
      rw [abs_div, abs_of_pos hdenpos, div_eq_mul_one_div]
    rw [h1]
    calc |Bflux u x| * (1 / (Real.cos x * (Real.sin (2 * x)) ^ 2))
        ≤ (C * (Real.pi / 2 - x) ^ ((5 + q) / 2))
            * ((Real.pi ^ 3 / 32) * (Real.pi / 2 - x) ^ (-3 : ℝ)) :=
          mul_le_mul (hB x hxmem) (cRR_one_div_den hxmem) (by positivity) (by positivity)
      _ = ((Real.pi ^ 3 / 32) * C)
            * ((Real.pi / 2 - x) ^ ((5 + q) / 2) * (Real.pi / 2 - x) ^ (-3 : ℝ)) := by ring
      _ = ((Real.pi ^ 3 / 32) * C) * (Real.pi / 2 - x) ^ ((q - 1) / 2) := by
          rw [cRR_delta_rpow_div_cube (q := q) hδ]
      _ ≤ ((Real.pi ^ 3 / 32) * C) * (Real.pi / 2 - x) ^ (-(1 / 2) : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ hCnn
          have hsplit : (Real.pi / 2 - x) ^ ((q - 1) / 2)
              = (Real.pi / 2 - x) ^ (-(1 / 2) : ℝ) * (Real.pi / 2 - x) ^ (q / 2) := by
            rw [← Real.rpow_add hδ]
            congr 1
            ring
          rw [hsplit]
          have h6 : (Real.pi / 2 - x) ^ (q / 2) ≤ 1 :=
            Real.rpow_le_one (le_of_lt hδ) hδ1 (by linarith)
          have h7 : 0 ≤ (Real.pi / 2 - x) ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg (le_of_lt hδ) _
          calc (Real.pi / 2 - x) ^ (-(1 / 2) : ℝ) * (Real.pi / 2 - x) ^ (q / 2)
              ≤ (Real.pi / 2 - x) ^ (-(1 / 2) : ℝ) * 1 := mul_le_mul_of_nonneg_left h6 h7
            _ = (Real.pi / 2 - x) ^ (-(1 / 2) : ℝ) := by ring
  have hWn_cont : ContinuousOn (Wn u) (Set.Icc (Real.pi / 4) θ) := by
    have hu_cont : ContinuousOn u (Set.Icc (Real.pi / 4) θ) :=
      ((hsm 0).continuousOn).mono (fun x hx =>
        ⟨by linarith [hx.1], lt_of_le_of_lt hx.2 hθ.2⟩)
    unfold Wn
    refine ContinuousOn.div hu_cont (by fun_prop) ?_
    intro x hx
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1])
      (by linarith [hx.2, hθ.2, hpi]))
  have hWn'cont : ContinuousOn
      (fun x => Bflux u x / (Real.cos x * (Real.sin (2 * x)) ^ 2)) (Set.Icc (Real.pi / 4) θ) := by
    have hu_cont : ContinuousOn u (Set.Icc (Real.pi / 4) θ) :=
      ((hsm 0).continuousOn).mono (fun x hx =>
        ⟨by linarith [hx.1], lt_of_le_of_lt hx.2 hθ.2⟩)
    have hdu_cont : ContinuousOn (deriv u) (Set.Icc (Real.pi / 4) θ) :=
      ((hsm 2).continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).mono
        (fun x hx => ⟨by linarith [hx.1], lt_of_le_of_lt hx.2 hθ.2⟩)
    have hBc : ContinuousOn (Bflux u) (Set.Icc (Real.pi / 4) θ) := by
      unfold Bflux
      fun_prop
    refine hBc.div (by fun_prop) (fun x hx => ?_)
    exact ne_of_gt (by
      have h1 : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo
        ⟨by linarith [hx.1], lt_of_le_of_lt hx.2 hθ.2⟩
      have h2 : 0 < Real.sin (2 * x) := Real.sin_pos_of_pos_of_lt_pi
        (by linarith [hx.1]) (by linarith [hx.2, hθ.2, hpi])
      positivity)
  have hmajden : ContinuousOn
      (fun x => ((Real.pi ^ 3 / 32) * C) * (Real.pi / 2 - x) ^ (-(1 / 2) : ℝ))
      (Set.Icc (Real.pi / 4) θ) := by
    refine ContinuousOn.const_mul ?_ _
    refine ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id) ?_
    intro x hx
    exact Or.inl (ne_of_gt (by linarith [hx.2, hθ.2, hpi]))
  have hderiv : ∀ x ∈ Set.Ioo (Real.pi / 4) θ,
      HasDerivAt (Wn u) (Bflux u x / (Real.cos x * (Real.sin (2 * x)) ^ 2)) x := by
    intro x hx
    exact SRSAux.WnDeriv (hsm 1) ⟨by linarith [hx.1], lt_trans hx.2 hθ.2⟩
  have hintW : IntervalIntegrable
      (fun x => Bflux u x / (Real.cos x * (Real.sin (2 * x)) ^ 2)) volume (Real.pi / 4) θ := by
    have h := hWn'cont
    rw [← Set.uIcc_of_le (le_of_lt hθ.1)] at h
    exact h.intervalIntegrable
  have hftc : Wn u θ - Wn u (Real.pi / 4)
      = ∫ x in (Real.pi / 4)..θ, Bflux u x / (Real.cos x * (Real.sin (2 * x)) ^ 2) :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (le_of_lt hθ.1) hWn_cont hderiv
      hintW).symm
  have hintmaj : IntervalIntegrable
      (fun x => ((Real.pi ^ 3 / 32) * C) * (Real.pi / 2 - x) ^ (-(1 / 2) : ℝ))
      volume (Real.pi / 4) θ := by
    have h := hmajden
    rw [← Set.uIcc_of_le (le_of_lt hθ.1)] at h
    exact h.intervalIntegrable
  have hintabs : IntervalIntegrable
      (fun x => |Bflux u x / (Real.cos x * (Real.sin (2 * x)) ^ 2)|) volume (Real.pi / 4) θ := by
    have h := hWn'cont.abs
    rw [← Set.uIcc_of_le (le_of_lt hθ.1)] at h
    exact h.intervalIntegrable
  have hmono : ∫ x in (Real.pi / 4)..θ,
      |Bflux u x / (Real.cos x * (Real.sin (2 * x)) ^ 2)|
      ≤ ∫ x in (Real.pi / 4)..θ,
          ((Real.pi ^ 3 / 32) * C) * (Real.pi / 2 - x) ^ (-(1 / 2) : ℝ) :=
    intervalIntegral.integral_mono_on_of_le_Ioo (le_of_lt hθ.1) hintabs
      hintmaj hpt
  have hbnd : ∫ x in (Real.pi / 4)..θ, ((Real.pi ^ 3 / 32) * C) * (Real.pi / 2 - x) ^ (-(1 / 2) : ℝ)
      ≤ ((Real.pi ^ 3 / 32) * C) * 2 := by
    rw [intervalIntegral.integral_const_mul]
    apply mul_le_mul_of_nonneg_left _ hCnn
    have hsub : ∫ x in (Real.pi / 4)..θ, (Real.pi / 2 - x) ^ (-(1 / 2) : ℝ)
        = ∫ u in (Real.pi / 2 - θ)..(Real.pi / 2 - Real.pi / 4), u ^ (-(1 / 2) : ℝ) := by
      have h := intervalIntegral.integral_comp_sub_left (fun u : ℝ => u ^ (-(1 / 2) : ℝ))
        (Real.pi / 2) (a := Real.pi / 4) (b := θ)
      simpa only [Function.comp_def] using h
    rw [hsub, cRR_integral_rpow (a := Real.pi / 2 - θ) (b := Real.pi / 2 - Real.pi / 4)
      (p := (-(1 / 2) : ℝ)) (by linarith [hθ.2, hpi]) (by linarith [hθ.1]) (by norm_num)]
    have h1 : ((Real.pi / 2 - Real.pi / 4 : ℝ)) ^ ((-(1 / 2) : ℝ) + 1) ≤ 1 :=
      Real.rpow_le_one (by linarith [hpi]) (by linarith [Real.pi_le_four]) (by norm_num)
    have h2 : 0 ≤ (Real.pi / 2 - θ) ^ ((-(1 / 2) : ℝ) + 1) :=
      Real.rpow_nonneg (by linarith [hθ.2, hpi]) _
    rw [show (-(1 / 2) : ℝ) + 1 = 1 / 2 by norm_num] at h1 h2 ⊢
    linarith
  have hInt : ∫ x in (Real.pi / 4)..θ,
      |Bflux u x / (Real.cos x * (Real.sin (2 * x)) ^ 2)| ≤ ((Real.pi ^ 3 / 32) * C) * 2 :=
    le_trans hmono hbnd
  have h1 : Wn u θ = Wn u (Real.pi / 4)
      + ∫ x in (Real.pi / 4)..θ, Bflux u x / (Real.cos x * (Real.sin (2 * x)) ^ 2) := by
    linarith [hftc]
  rw [h1]
  calc |Wn u (Real.pi / 4) + ∫ x in (Real.pi / 4)..θ, Bflux u x / (Real.cos x * (Real.sin (2 * x)) ^ 2)|
      ≤ |Wn u (Real.pi / 4)|
        + |∫ x in (Real.pi / 4)..θ, Bflux u x / (Real.cos x * (Real.sin (2 * x)) ^ 2)| := by
        simpa only [Real.norm_eq_abs] using
          norm_add_le (Wn u (Real.pi / 4))
            (∫ x in (Real.pi / 4)..θ, Bflux u x / (Real.cos x * (Real.sin (2 * x)) ^ 2))
    _ ≤ |Wn u (Real.pi / 4)|
        + ∫ x in (Real.pi / 4)..θ,
            |Bflux u x / (Real.cos x * (Real.sin (2 * x)) ^ 2)| :=
        add_le_add le_rfl (intervalIntegral.abs_integral_le_integral_abs (le_of_lt hθ.1))
    _ ≤ |Wn u (Real.pi / 4)| + (Real.pi ^ 3 / 32) * C * 2 := add_le_add le_rfl hInt
    _ ≤ |Wn u (Real.pi / 4)| + (Real.pi ^ 3 / 32) * C * 2 + 1 := by linarith

/-! ### The target -/

theorem corrRightRate (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) {u : ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)))
    (hu2 : MeasureTheory.IntegrableOn
      (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.AngAWeak.wq q θ) Work.Spaces.Iθ)
    (hLu2 : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2
        * Work.FTS.EllipticEst.AngAWeak.wq q θ) Work.Spaces.Iθ) :
    ∃ K : ℝ, 0 < K ∧ ∀ θ ∈ Set.Ioo (Real.pi / 2 - Real.pi / 8) (Real.pi / 2),
      |u θ| ≤ K * (Real.pi / 2 - θ) ∧ |deriv u θ| ≤ K := by
  have hpi := Real.pi_pos
  obtain ⟨hF, C, hC0, htail⟩ := cRR_fluxTail hq0 hsm hLu2
  obtain ⟨Binf, hdec⟩ := cRR_bflux_decomp hq0 hsm hF
  have hBinf0 : Binf = 0 := cRR_binf_zero hq0 hC0 hsm hu2 hdec htail
  have hflux : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      |Bflux u θ| ≤ C * (Real.pi / 2 - θ) ^ ((5 + q) / 2) := by
    intro θ hθ
    rw [hdec θ hθ, hBinf0, zero_add]
    exact htail θ hθ
  obtain ⟨K₁, hK₁pos, hK₁⟩ := cRR_wnBound hq0 hC0 hsm hflux
  have hCnn : (0 : ℝ) ≤ (Real.pi ^ 3 / 32) * C := by positivity
  have hWn'bound : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      |Bflux u θ / (Real.cos θ * (Real.sin (2 * θ)) ^ 2)|
        ≤ ((Real.pi ^ 3 / 32) * C) * (Real.pi / 2 - θ) ^ (-(1 / 2) : ℝ) := by
    intro θ hθ
    have hδ : 0 < Real.pi / 2 - θ := by linarith [hθ.2, hpi]
    have hδ1 : Real.pi / 2 - θ ≤ 1 := by linarith [hθ.1, Real.pi_le_four]
    have hcospos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], hθ.2⟩
    have hsinpos : 0 < Real.sin (2 * θ) := Real.sin_pos_of_pos_of_lt_pi
      (by linarith [hθ.1]) (by linarith [hθ.2, hpi])
    have hdenpos : 0 < Real.cos θ * (Real.sin (2 * θ)) ^ 2 := by positivity
    rw [abs_div, abs_of_pos hdenpos, div_eq_mul_one_div]
    calc |Bflux u θ| * (1 / (Real.cos θ * (Real.sin (2 * θ)) ^ 2))
        ≤ (C * (Real.pi / 2 - θ) ^ ((5 + q) / 2))
            * ((Real.pi ^ 3 / 32) * (Real.pi / 2 - θ) ^ (-3 : ℝ)) :=
          mul_le_mul (hflux θ hθ) (cRR_one_div_den hθ) (by positivity) (by positivity)
      _ = ((Real.pi ^ 3 / 32) * C)
            * ((Real.pi / 2 - θ) ^ ((5 + q) / 2) * (Real.pi / 2 - θ) ^ (-3 : ℝ)) := by ring
      _ = ((Real.pi ^ 3 / 32) * C) * (Real.pi / 2 - θ) ^ ((q - 1) / 2) := by
          rw [cRR_delta_rpow_div_cube (q := q) hδ]
      _ ≤ ((Real.pi ^ 3 / 32) * C) * (Real.pi / 2 - θ) ^ (-(1 / 2) : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ hCnn
          have hsplit : (Real.pi / 2 - θ) ^ ((q - 1) / 2)
              = (Real.pi / 2 - θ) ^ (-(1 / 2) : ℝ) * (Real.pi / 2 - θ) ^ (q / 2) := by
            rw [← Real.rpow_add hδ]
            congr 1
            ring
          rw [hsplit]
          have h6 : (Real.pi / 2 - θ) ^ (q / 2) ≤ 1 :=
            Real.rpow_le_one (le_of_lt hδ) hδ1 (by linarith)
          have h7 : 0 ≤ (Real.pi / 2 - θ) ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg (le_of_lt hδ) _
          calc (Real.pi / 2 - θ) ^ (-(1 / 2) : ℝ) * (Real.pi / 2 - θ) ^ (q / 2)
              ≤ (Real.pi / 2 - θ) ^ (-(1 / 2) : ℝ) * 1 := mul_le_mul_of_nonneg_left h6 h7
            _ = (Real.pi / 2 - θ) ^ (-(1 / 2) : ℝ) := by ring
  have hderiv_eq : ∀ θ ∈ Set.Ioo (Real.pi / 2 - Real.pi / 8) (Real.pi / 2),
      deriv u θ = (Bflux u θ / (Real.cos θ * (Real.sin (2 * θ)) ^ 2)) * Real.sin (2 * θ)
        + Wn u θ * (2 * Real.cos (2 * θ)) := by
    intro θ hθ
    have hθ' : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [hθ.1, hpi], hθ.2⟩
    have hWn_deriv : HasDerivAt (Wn u)
        (Bflux u θ / (Real.cos θ * (Real.sin (2 * θ)) ^ 2)) θ :=
      SRSAux.WnDeriv (hsm 1) hθ'
    have hsin2 : HasDerivAt (fun s : ℝ => Real.sin (2 * s)) (2 * Real.cos (2 * θ)) θ := by
      have h1 : HasDerivAt (fun s : ℝ => 2 * s) 2 θ := by
        simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
      have h2 := (Real.hasDerivAt_sin (2 * θ)).comp θ h1
      simpa only [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using h2
    have hprod := hWn_deriv.mul hsin2
    have heq : u =ᶠ[𝓝 θ] (fun s => Wn u s * Real.sin (2 * s)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ'] with s hs
      simp only [Wn]
      exact (div_mul_cancel₀ (u s) (ne_of_gt (wq_sin_pos hs))).symm
    have hprod' : HasDerivAt u
        ((Bflux u θ / (Real.cos θ * (Real.sin (2 * θ)) ^ 2)) * Real.sin (2 * θ)
          + Wn u θ * (2 * Real.cos (2 * θ))) θ := hprod.congr_of_eventuallyEq heq
    have hdu : HasDerivAt u (deriv u θ) θ :=
      (((hsm 1).contDiffAt (isOpen_Ioo.mem_nhds hθ')).differentiableAt
        (by norm_num)).hasDerivAt
    exact (hprod'.unique hdu).symm
  refine ⟨max (2 * K₁) (((Real.pi ^ 3 / 32) * C) * 2 + 2 * K₁) + 1, by positivity, ?_⟩
  intro θ hθ
  have hθ' : θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2) := by
    refine ⟨?_, hθ.2⟩
    linarith [hθ.1, hpi]
  set d : ℝ := Real.pi / 2 - θ with hd
  have hd0 : 0 < d := by rw [hd]; linarith [hθ.2, hpi]
  have hdle : d ≤ Real.pi / 8 := by rw [hd]; linarith [hθ.1]
  have hsinpos : 0 < Real.sin (2 * θ) := (cRR_trig hq0 hθ').1
  have hsinup : Real.sin (2 * θ) ≤ 2 * d := by
    have h := (SRSAux.TrigCompare (q := q) hq0 θ hθ').1
    rw [hd]; exact h
  have hWn_le : |Wn u θ| ≤ K₁ := hK₁ θ hθ'
  have hder : |deriv u θ| ≤ ((Real.pi ^ 3 / 32) * C) * 2 + 2 * K₁ := by
    rw [hderiv_eq θ hθ]
    refine le_trans (abs_add_le _ _) ?_
    have h1 : |(Bflux u θ / (Real.cos θ * (Real.sin (2 * θ)) ^ 2)) * Real.sin (2 * θ)|
        ≤ ((Real.pi ^ 3 / 32) * C) * 2 := by
      rw [abs_mul]
      have h2 := hWn'bound θ hθ'
      have h3 : |Bflux u θ / (Real.cos θ * (Real.sin (2 * θ)) ^ 2)|
          ≤ ((Real.pi ^ 3 / 32) * C) * d ^ (-(1 / 2) : ℝ) := by
        have h := h2
        rw [← hd] at h
        exact h
      calc |Bflux u θ / (Real.cos θ * (Real.sin (2 * θ)) ^ 2)| * |Real.sin (2 * θ)|
          ≤ (((Real.pi ^ 3 / 32) * C) * d ^ (-(1 / 2) : ℝ)) * (2 * d) :=
            mul_le_mul h3 (by rw [abs_of_pos hsinpos]; exact hsinup) (abs_nonneg _) (by positivity)
        _ = ((Real.pi ^ 3 / 32) * C) * (2 * (d ^ (-(1 / 2) : ℝ) * d)) := by ring
        _ ≤ ((Real.pi ^ 3 / 32) * C) * 2 := by
            apply mul_le_mul_of_nonneg_left _ hCnn
            have hsplit : d ^ (-(1 / 2) : ℝ) * d = d ^ ((1 : ℝ) / 2) := by
              have h := Real.rpow_add hd0 (-(1 / 2) : ℝ) (1 : ℝ)
              rw [Real.rpow_one] at h
              rw [← h]
              congr 1
              norm_num
            rw [hsplit]
            have h4 : d ^ ((1 : ℝ) / 2) ≤ 1 :=
              Real.rpow_le_one (le_of_lt hd0) (by linarith [hdle, Real.pi_le_four]) (by norm_num)
            linarith
    have h5 : |Wn u θ * (2 * Real.cos (2 * θ))| ≤ K₁ * 2 := by
      rw [abs_mul]
      have h6 : |2 * Real.cos (2 * θ)| ≤ 2 := by
        rw [abs_mul, show |(2 : ℝ)| = 2 by norm_num]
        have h := Real.abs_cos_le_one (2 * θ)
        linarith
      exact mul_le_mul hWn_le h6 (abs_nonneg _) hK₁pos.le
    have hsum : |(Bflux u θ / (Real.cos θ * (Real.sin (2 * θ)) ^ 2)) * Real.sin (2 * θ)
          + Wn u θ * (2 * Real.cos (2 * θ))|
        ≤ |(Bflux u θ / (Real.cos θ * (Real.sin (2 * θ)) ^ 2)) * Real.sin (2 * θ)|
          + |Wn u θ * (2 * Real.cos (2 * θ))| := abs_add_le _ _
    have hAB : |(Bflux u θ / (Real.cos θ * (Real.sin (2 * θ)) ^ 2)) * Real.sin (2 * θ)|
          + |Wn u θ * (2 * Real.cos (2 * θ))|
        ≤ ((Real.pi ^ 3 / 32) * C) * 2 + 2 * K₁ := by
      have h := add_le_add h1 h5
      linarith only [h]
    linarith only [hsum, hAB]
  refine ⟨?_, ?_⟩
  · have hueq : |u θ| = |Wn u θ| * Real.sin (2 * θ) := by
      rw [show u θ = Wn u θ * Real.sin (2 * θ) from
        (div_mul_cancel₀ (u θ) (ne_of_gt hsinpos)).symm, abs_mul, abs_of_pos hsinpos]
    have hK : 2 * K₁ ≤ max (2 * K₁) (((Real.pi ^ 3 / 32) * C) * 2 + 2 * K₁) + 1 := by
      linarith [le_max_left (2 * K₁) (((Real.pi ^ 3 / 32) * C) * 2 + 2 * K₁)]
    rw [hueq]
    calc |Wn u θ| * Real.sin (2 * θ) ≤ K₁ * (2 * d) :=
          mul_le_mul hWn_le hsinup hsinpos.le hK₁pos.le
      _ ≤ (max (2 * K₁) (((Real.pi ^ 3 / 32) * C) * 2 + 2 * K₁) + 1) * d := by
          nlinarith [hd0, hK, hK₁pos]
  · have hK : ((Real.pi ^ 3 / 32) * C) * 2 + 2 * K₁
        ≤ max (2 * K₁) (((Real.pi ^ 3 / 32) * C) * 2 + 2 * K₁) + 1 := by
      linarith [le_max_right (2 * K₁) (((Real.pi ^ 3 / 32) * C) * 2 + 2 * K₁)]
    linarith [hder, hK]

end Work.FTS.EllipticEst.AngAWeak
