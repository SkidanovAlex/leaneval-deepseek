import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseFixB1.RungAssembly
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1.boxSlack_le_pcBlock` — **the requested statement is FALSE**

**STATUS.**  The theorem `boxSlack_le_pcBlock` at the bottom of this file is kept verbatim as
requested, but it is **not provable**: its conclusion needs the hypothesis `boxM2 ≥ 2·boxM1`
(see below), which the corpus *refutes*.  See
`Submission/Work/BoseFixB1/FINDING_boxSlack_le_pcBlock_FALSE.md` for the full write-up.

## Why the statement says `boxM2 ≥ 2 boxM1`

With `rungSlack V M1 S = ½(M₁/V²)(S²−S)` and `rungPCBlock V M2 M1 S Pc = ½(M₂/V²)Pc − rungSlack`,
the conclusion

    rungSlack ≤ rungPCBlock + C·a·(μ + S/V)·n₊

is *equivalent* (all hypotheses are fixed except the scalar ones) to

    (M₁/V²)(S² − S) ≤ ½(M₂/V²)·Pc + C·a(v)·(μ + S/V)·n₊ .                    (∗)

The corpus hypothesis `hcS2` is `S² − S ≤ Pc`, and for the (admissible, normalised, continuous)
product states `Φ = φ^{⊗N}` of the box projections one has exactly

    S = Nγ,     Pc = N(N−1)γ²,     n₊ = N(1−γ),      γ = (∫_A φ)²/V ∈ (0,1)

(so `hcS2` reads `Nγ(1−γ) ≥ 0` and *is* satisfied), and the credit is
`C·a·(μ + Nγ/V)·N(1−γ)`.  In the limit `γ → 1` the credit vanishes while (∗) becomes
`M₁ ≤ M₂/2`; the credit can be defeated for each fixed `C` by taking `1−γ` small and `N` large.
Hence (∗) for all admissible data is equivalent to the **missing hypothesis**

    boxM2 ≥ 2 · boxM1 ,        i.e.   M₂ − M₁ ≥ M₁ ,

and that hypothesis is *false* for the localised kernels: the `ω`-mass identity
(`Work.BoseFixB1B.boxM2_sub_boxM1_eq_omegaMass`) gives `M₂ − M₁ = ∫∫ ω₀(x−y)·w₁(x,y)` and
`0 ≤ ω₀ ≤ 1` a.e. (FS `eq:omegabounds`), so `M₂ − M₁ ≤ ∫∫ w₁ = M₁`, i.e. `M₂ ≤ 2 M₁` — with
*strict* inequality as soon as `w₁` does not vanish a.e. (`w₁(x,y) > 0` forces `g₀(x−y) > 0`,
hence `ω₀(x−y) < 1`).

## Machine-checked content of this file

* `boxSlack_shadow_arith` — the arithmetic core in the densities `κ₁ = M₁/V²`, `κ₂ = M₂/V²`:
  assuming `κ₁ ≤ κ₂` (the target's `hM2`) and `κ₂ < 2κ₁`, for **every** `C ≥ 0` there are
  product-state scalars satisfying `hcS2` and violating the conclusion;
* `boxSlack_shadow` — the same in the `rungSlack`/`rungPCBlock`/`rungRate` vocabulary;
* `boxM2_le_two_mul_boxM1` — the corpus inequality `boxM2 ≤ 2·boxM1` (with its two kernels
  `ae_g2_le_two_g0`, `wSmallPair_const_mul`, `ae_wSmallPair_g2_le_two_mul_wSmall1Pair`), the
  refutation of the missing hypothesis.
-/

namespace Work.BoseFixB1

open MeasureTheory
open scoped BigOperators

set_option maxHeartbeats 1000000

/-- The arithmetic core of the refutation of `boxSlack_le_pcBlock`, in the *densities*
`κ₁ = M₁/V²`, `κ₂ = M₂/V²`, `λ = 1/V` in which the localised masses enter the target's slack
(so no division by the variable `V` occurs and the statement is pure polynomial arithmetic).

`κ₁ ≤ κ₂` is the target's hypothesis `hM2`, and `κ₂ < 2κ₁` is what the corpus *proves* for the
actual localised kernels (`boxM2 − boxM1 = ∫∫ω w₁ ≤ ∫∫w₁ = boxM1`, since `0 ≤ ω ≤ 1` a.e.).
The conclusion is the product-state family of the box projections:
with `Φ = φ^{⊗N}`, `S = Nγ`, `Pc = N(N−1)γ²`, `n₊ = N(1−γ)` (`γ = (∫_A φ)²/V ∈ (0,1)`),
`hcS2` reads `S² − S ≤ Pc`, and the target's inequality fails for suitable `γ, N` — for
*every* `C`. -/
theorem boxSlack_shadow_arith (C : ℝ) (hC : 0 ≤ C) {κ1 κ2 a μ lam : ℝ}
    (hκ1 : 0 < κ1) (hκ2le : κ1 ≤ κ2) (hκ2lt : κ2 < 2 * κ1)
    (ha : 0 < a) (hμ : 0 < μ) (hlam : 0 < lam) :
    ∃ (γ : ℝ) (N : ℕ), 0 < γ ∧ γ < 1 ∧ 1 ≤ N ∧
      (N : ℝ) * γ * ((N : ℝ) * γ) - (N : ℝ) * γ ≤ (N : ℝ) * ((N : ℝ) - 1) * γ ^ 2 ∧
      ¬ ((1 / 2) * κ1 * (((N : ℝ) * γ) ^ 2 - (N : ℝ) * γ)
          ≤ ((1 / 2) * κ2 * ((N : ℝ) * ((N : ℝ) - 1) * γ ^ 2)
              - (1 / 2) * κ1 * (((N : ℝ) * γ) ^ 2 - (N : ℝ) * γ))
            + C * a * (μ + lam * ((N : ℝ) * γ)) * ((N : ℝ) * (1 - γ))) := by
  have hKpos : 0 < κ1 - κ2 / 2 := by linarith
  have hden : 0 < C * a * lam + 1 := by positivity
  set eps : ℝ := min (1 / 2) ((κ1 - κ2 / 2) / (8 * (C * a * lam + 1))) with heps
  have heps_pos : 0 < eps := lt_min (by norm_num) (div_pos hKpos (by positivity))
  have heps_half : eps ≤ 1 / 2 := min_le_left _ _
  have heps_K : C * a * lam * eps ≤ (κ1 - κ2 / 2) / 8 := by
    have h1 : eps ≤ (κ1 - κ2 / 2) / (8 * (C * a * lam + 1)) := min_le_right _ _
    have h2 : C * a * lam * eps
        ≤ C * a * lam * ((κ1 - κ2 / 2) / (8 * (C * a * lam + 1))) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : C * a * lam * ((κ1 - κ2 / 2) / (8 * (C * a * lam + 1)))
        ≤ (κ1 - κ2 / 2) / 8 := by
      have he : C * a * lam * ((κ1 - κ2 / 2) / (8 * (C * a * lam + 1)))
          = (C * a * lam / (C * a * lam + 1)) * ((κ1 - κ2 / 2) / 8) := by
        field_simp
      rw [he]
      exact mul_le_of_le_one_left (by positivity)
        (by rw [div_le_one hden]; linarith)
    linarith
  set G : ℝ := 1 - eps with hG
  have hGgt : 0 < G := by rw [hG]; linarith
  have hGlt : G < 1 := by rw [hG]; linarith
  have hGhalf : 1 / 2 ≤ G := by rw [hG]; linarith
  have hGnn : 0 ≤ G := hGgt.le
  have hGle : G ≤ 1 := hGlt.le
  have hone : (1 : ℝ) - G = eps := by rw [hG]; ring
  -- the quadratic coefficient in `N`
  have hcoef : (κ1 - κ2 / 2) / 8 ≤ G ^ 2 * (κ1 - κ2 / 2) - C * a * lam * G * eps := by
    have h1 : (1 / 4 : ℝ) ≤ G ^ 2 := by nlinarith [hGhalf]
    have h2 : C * a * lam * G * eps ≤ (κ1 - κ2 / 2) / 8 := by
      have h3 : G * eps ≤ 1 * eps := mul_le_mul_of_nonneg_right hGle heps_pos.le
      nlinarith [h3, heps_K]
    nlinarith [h1, h2, hKpos]
  set B : ℝ := κ1 + C * a * μ with hB
  have hBnn : 0 ≤ B := by rw [hB]; positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (8 * B / (κ1 - κ2 / 2)))
  have hNcast : (1 : ℝ) ≤ (N : ℝ) :=
    le_of_lt (lt_of_le_of_lt (le_max_left _ _) hN)
  have hNbig : B < (N : ℝ) * ((κ1 - κ2 / 2) / 8) := by
    have h8 : 8 * B / (κ1 - κ2 / 2) < (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
    have hmul := mul_lt_mul_of_pos_right h8 hKpos
    have hsimp : 8 * B / (κ1 - κ2 / 2) * (κ1 - κ2 / 2) = 8 * B := by
      rw [div_mul_cancel₀ _ (ne_of_gt hKpos)]
    rw [hsimp] at hmul
    linarith
  have hNne : N ≠ 0 := by
    intro h0
    have hz : ((N : ℝ)) = 0 := by rw [h0]; simp
    rw [hz] at hN
    have h1 : (1 : ℝ) ≤ max 1 (8 * B / (κ1 - κ2 / 2)) := le_max_left _ _
    linarith
  have hNcastN : (1 : ℕ) ≤ N := Nat.one_le_iff_ne_zero.mpr hNne
  refine ⟨G, N, hGgt, hGlt, hNcastN, ?_, ?_⟩
  · -- `hcS2` for the product-state scalars
    have hn0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have hkey : 0 ≤ (N : ℝ) * G * (1 - G) := by
      have h1 : 0 ≤ 1 - G := by linarith
      positivity
    nlinarith [hkey]
  · -- the violation
    intro hle
    have hnorm : (1 : ℝ) - G = eps := hone
    have hle' : κ1 * (((N : ℝ) * G) ^ 2 - (N : ℝ) * G)
        ≤ (1 / 2) * κ2 * ((N : ℝ) * ((N : ℝ) - 1) * G ^ 2)
          + C * a * (μ + lam * ((N : ℝ) * G)) * ((N : ℝ) * (1 - G)) := by linarith
    have hn : (0 : ℝ) < (N : ℝ) := by linarith
    have hn1 : (0 : ℝ) ≤ (N : ℝ) := hn.le
    have hsq : (0 : ℝ) ≤ (N : ℝ) ^ 2 := sq_nonneg _
    have hrewrite : κ1 * (((N : ℝ) * G) ^ 2 - (N : ℝ) * G)
          - ((1 / 2) * κ2 * ((N : ℝ) * ((N : ℝ) - 1) * G ^ 2)
            + C * a * (μ + lam * ((N : ℝ) * G)) * ((N : ℝ) * (1 - G)))
        = ((N : ℝ) ^ 2) * (G ^ 2 * (κ1 - κ2 / 2) - C * a * lam * G * eps)
          - (N : ℝ) * (G * κ1 - G ^ 2 * (κ2 / 2) + C * a * μ * eps) := by
      rw [hnorm]
      ring
    have hmul1 : ((N : ℝ) ^ 2) * ((κ1 - κ2 / 2) / 8)
        ≤ ((N : ℝ) ^ 2) * (G ^ 2 * (κ1 - κ2 / 2) - C * a * lam * G * eps) :=
      mul_le_mul_of_nonneg_left hcoef hsq
    have hNB : (N : ℝ) * B < ((N : ℝ) ^ 2) * ((κ1 - κ2 / 2) / 8) := by
      nlinarith [hNbig, hn]
    have hBbound : G * κ1 - G ^ 2 * (κ2 / 2) + C * a * μ * eps ≤ B := by
      rw [hB]
      have h1 : G * κ1 ≤ κ1 := by nlinarith [hGle, hGnn, hκ1]
      have h2 : 0 ≤ G ^ 2 * (κ2 / 2) := by nlinarith [hκ1, hκ2le, sq_nonneg G]
      have h3 : C * a * μ * eps ≤ C * a * μ := by
        have h1 : eps ≤ 1 := by linarith [heps_half]
        calc C * a * μ * eps ≤ C * a * μ * 1 :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = C * a * μ := by ring
      linarith
    have hmul2 : (N : ℝ) * (G * κ1 - G ^ 2 * (κ2 / 2) + C * a * μ * eps)
        ≤ (N : ℝ) * B := mul_le_mul_of_nonneg_left hBbound hn1
    have hfinal : 0 < ((N : ℝ) ^ 2) * (G ^ 2 * (κ1 - κ2 / 2) - C * a * lam * G * eps)
        - (N : ℝ) * (G * κ1 - G ^ 2 * (κ2 / 2) + C * a * μ * eps) := by
      linarith [hmul1, hmul2, hNB]
    rw [← hrewrite] at hfinal
    linarith

/-- The same refutation in the `rungSlack` / `rungPCBlock` / `rungRate` vocabulary of
`Submission/Work/BoseFixB1/RungPieces.lean`, at `V = boxMass`, `M₁ = boxM1`, `M₂ = boxM2`,
`a = a(v)`. -/
theorem boxSlack_shadow (C : ℝ) (hC : 0 ≤ C) {V M1 M2 a μ : ℝ}
    (hV : 0 < V) (hM1 : 0 < M1) (hM2le : M1 ≤ M2) (hM2lt : M2 < 2 * M1)
    (ha : 0 < a) (hμ : 0 < μ) :
    ∃ (γ : ℝ) (N : ℕ), 0 < γ ∧ γ < 1 ∧ 1 ≤ N ∧
      (N : ℝ) * γ * ((N : ℝ) * γ) - (N : ℝ) * γ ≤ (N : ℝ) * ((N : ℝ) - 1) * γ ^ 2 ∧
      ¬ (rungSlack V M1 ((N : ℝ) * γ)
          ≤ rungPCBlock V M2 M1 ((N : ℝ) * γ) ((N : ℝ) * ((N : ℝ) - 1) * γ ^ 2)
            + C * a * rungRate V μ ((N : ℝ) * γ) * ((N : ℝ) * (1 - γ))) := by
  obtain ⟨γ, N, h1, h2, h3, hcS2, hviol⟩ :=
    boxSlack_shadow_arith (C := C) hC (κ1 := M1 / V ^ 2) (κ2 := M2 / V ^ 2)
      (a := a) (μ := μ) (lam := 1 / V)
      (div_pos hM1 (pow_pos hV 2))
      (div_le_div_of_nonneg_right hM2le (pow_pos hV 2).le)
      (by rw [show (2 : ℝ) * (M1 / V ^ 2) = 2 * M1 / V ^ 2 by ring]
          exact div_lt_div_of_pos_right hM2lt (pow_pos hV 2))
      ha hμ (one_div_pos.mpr hV)
  refine ⟨γ, N, h1, h2, h3, hcS2, ?_⟩
  rw [rungPCBlock, rungSlack, rungRate]
  intro hle
  exact hviol (by
    simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, mul_one, one_mul]
      using hle)


/-! ## The actual localised masses satisfy `boxM2 < 2 boxM1` — the missing hypothesis

The requested statement is equivalent (in the `hcS2`-tight regime `Pc = S²−S`) to
`M₂ ≥ 2 M₁`; the corpus *proves* the opposite inequality: the `ω`-mass identity
`Work.BoseFixB1B.boxM2_sub_boxM1_eq_omegaMass` gives

    M₂ − M₁ = ∫∫_{B×B} ω₀(x−y)·w₁(x,y) ,      0 ≤ ω₀ ≤ 1  a.e. (FS `eq:omegabounds`),

so `M₂ − M₁ ≤ ∫∫ w₁ = M₁`, i.e. `M₂ ≤ 2M₁` — and *strictly* `<` as soon as `w₁` is not a.e.
zero, because `w₁ > 0` forces `g₀(x−y) > 0`, hence `ω₀(x−y) < 1`.  Here is the inequality
`M₂ ≤ 2 M₁` itself, followed by the strict form `M₂ < 2 M₁` for data with `M₁ > 0`. -/

/-- FS `eq:omegabounds` consequence at the numerator level: `g₂ ≤ 2 g₀` a.e. -/
lemma ae_g2_le_two_g0 {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ, _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v) :
    ∀ᵐ z : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.g2 v h z ≤ 2 * Submission.BoseGases.g0 v h z := by
  obtain ⟨hrad, hscat⟩ := Classical.choose_spec h
  have hb := Submission.BoseGases.scattering_bounds_ae (w := Classical.choose h)
    hR0 hv hvrad hv_supp hrad hscat
  have hg0 := Submission.BoseGases.g0_nonneg_ae (R := R0) hR0 hv hvrad hv_supp h
  filter_upwards [hg0, hb.2] with z h0 hw
  have heq : Submission.BoseGases.g2 v h z
      = Submission.BoseGases.g0 v h z * (1 + Classical.choose h z) := by
    rw [Submission.BoseGases.g2, Submission.BoseGases.g0]
  rw [heq]
  nlinarith [h0, hw]

/-- The localised kernel is additive in its numerator. -/
lemma wSmallPair_const_mul {M : ℕ} {ℓ d : ℝ} {u : EuclideanSpace ℝ (Fin 3)} (c : ℝ) (f : EuclideanSpace ℝ (Fin 3) → ℝ) (x y : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.wSmallPair M ℓ d u (fun z => c * f z) x y
      = c * Submission.BoseGases.wSmallPair M ℓ d u f x y := by
  simp only [Submission.BoseGases.wSmallPair, Submission.BoseGases.wSmallScaled]
  ring

/-- **`w₂ ≤ 2 w₁` pointwise a.e.** (the `ω₀ ≤ 1` half of FS `lm:w2>w1`). -/
lemma ae_wSmallPair_g2_le_two_mul_wSmall1Pair {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ, _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} {ℓ d : ℝ} (u : EuclideanSpace ℝ (Fin 3)) :
    ∀ᵐ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) ∂((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))),
      2 * Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2
        ≥ Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) p.1 p.2 := by
  have hle_ae := ae_g2_le_two_g0 (R0 := R0) hv_supp hR0 hv hvrad h
  have key : ∀ x y : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.g2 v h (x - y) ≤ 2 * Submission.BoseGases.g0 v h (x - y) →
      2 * Submission.BoseGases.wSmall1Pair h M ℓ d u x y
        ≥ Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) x y := by
    intro x y hxy
    have h1 := wSmallPair_mono_of_le (M := M) (ℓ := ℓ) (d := d) (u := u)
      (f := Submission.BoseGases.g2 v h)
      (g := fun z => 2 * Submission.BoseGases.g0 v h z) x y hxy
    have h2 : Submission.BoseGases.wSmallPair M ℓ d u
        (fun z => 2 * Submission.BoseGases.g0 v h z) x y
        = 2 * Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) x y :=
      wSmallPair_const_mul 2 (Submission.BoseGases.g0 v h) x y
    rw [h2] at h1
    simpa only [Submission.BoseGases.wSmall1Pair] using h1
  rw [MeasureTheory.ae_iff]
  obtain ⟨t, hNt, htmeas, ht0⟩ :=
    MeasureTheory.exists_measurable_superset_of_null (MeasureTheory.ae_iff.mp hle_ae)
  have hsub : {p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) |
        ¬ (2 * Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2
          ≥ Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) p.1 p.2)}
      ⊆ {p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) | p.1 - p.2 ∈ t} := by
    intro p hp
    by_contra hpt
    have hz : Submission.BoseGases.g2 v h (p.1 - p.2)
        ≤ 2 * Submission.BoseGases.g0 v h (p.1 - p.2) := by
      by_contra hc
      exact hpt (hNt hc)
    exact hp (key p.1 p.2 hz)
  have hS0 : ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))
      {p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) | p.1 - p.2 ∈ t} = 0 := by
    have hmeas : MeasurableSet {p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) | p.1 - p.2 ∈ t} :=
      htmeas.preimage (measurable_fst.sub measurable_snd)
    refine (MeasureTheory.Measure.measure_prod_null hmeas).2 ?_
    filter_upwards with x
    have hmp : MeasureTheory.MeasurePreserving (fun y : EuclideanSpace ℝ (Fin 3) => x - y)
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) := by
      have hh := (MeasureTheory.measurePreserving_add_left
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) x).comp
        (MeasureTheory.Measure.measurePreserving_neg
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))
      simpa [Function.comp_def, sub_eq_add_neg] using hh
    have hsec : Prod.mk x ⁻¹' {p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) | p.1 - p.2 ∈ t}
        = (fun y : EuclideanSpace ℝ (Fin 3) => x - y) ⁻¹' t := rfl
    rw [hsec, hmp.measure_preimage htmeas.nullMeasurableSet, ht0]
    simp
  exact MeasureTheory.measure_mono_null hsub hS0

/-- **The missing hypothesis is FALSE**: for every admissible localised kernel,
`boxM2 ≤ 2 · boxM1` (this is `M₂ − M₁ = ∫∫ω₀w₁ ≤ ∫∫w₁ = M₁`). -/
theorem boxM2_le_two_mul_boxM1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : Work.UBB.ScatSol v) {M : ℕ} (hM : 1 ≤ M)
    {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hR : R0 ≤ ℓ * d / 16)
    (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0) (u : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u)
        (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h))
      ≤ 2 * Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Submission.BoseGases.wSmall1Pair h M ℓ d u) := by
  have hvan1 : ∀ x y : EuclideanSpace ℝ (Fin 3),
      (x ∉ Submission.BoseGases.dlBox ℓ d u ∨ y ∉ Submission.BoseGases.dlBox ℓ d u) →
      Submission.BoseGases.wSmall1Pair h M ℓ d u x y = 0 :=
    fun x y hxy => Work.BoseFixB1S.wSmallPair_eq_zero_of_notMem_dlBox hM hℓ hd u hxy
  have hvan2 : ∀ x y : EuclideanSpace ℝ (Fin 3),
      (x ∉ Submission.BoseGases.dlBox ℓ d u ∨ y ∉ Submission.BoseGases.dlBox ℓ d u) →
      Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) x y = 0 :=
    fun x y hxy => Work.BoseFixB1S.wSmallPair_eq_zero_of_notMem_dlBox hM hℓ hd u hxy
  have hInt1 : MeasureTheory.IntegrableOn
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2)
      (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ) :=
    Work.BoseFixB1.integrableOn_wSmallPair_cube (f := Submission.BoseGases.g0 v h)
      (Submission.BoseGases.g0_integrable (R := R0) hR0 hv_supp h)
      (fun z hz => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h) hM hℓ hd hR hRχ u
  rw [Work.BoseFixB1S.boxM1_eq_acubePair u hvan1 hInt1,
    Work.BoseFixB1S.boxM2_eq_acubePair (volA := Work.SmallBoxSliding.boxMass ℓ d u) u hvan2]
  have hpt := ae_wSmallPair_g2_le_two_mul_wSmall1Pair (v := v) (R0 := R0) hv_supp hR0 hv
    hvrad h (M := M) (ℓ := ℓ) (d := d) u
  have hw1nn : ∀ᵐ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)
      ∂((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))),
      0 ≤ Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2 := by
    have hgnn : ∀ᵐ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)
        ∂((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))),
        0 ≤ Submission.BoseGases.g0 v h (p.1 - p.2) :=
      Work.BoseFixB1.ae_nonneg_g0_sub (v := v) h hv hvrad (R := R0) hR0 hv_supp
    filter_upwards [hgnn] with p hp
    simp only [Submission.BoseGases.wSmall1Pair, Submission.BoseGases.wSmallPair,
      Submission.BoseGases.wSmallScaled]
    exact mul_nonneg (mul_nonneg (Work.SmallBoxSliding.chiSmallB_nonneg M ℓ d u p.1)
      (div_nonneg (div_nonneg hp
          (Work.BoseFixB1.convScaleSmall_nonneg M (ℓ * d) (p.1 - p.2)))
        (Submission.BoseGases.convScale_nonneg ℓ (p.1 - p.2))))
      (Work.SmallBoxSliding.chiSmallB_nonneg M ℓ d u p.2)
  have hw2nn : ∀ᵐ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)
      ∂((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))),
      0 ≤ Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) p.1 p.2 := by
    have hqmp : Measure.QuasiMeasurePreserving
        (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => p.1 - p.2)
        ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) :=
      MeasureTheory.quasiMeasurePreserving_sub_of_right_invariant _ _
    have hgnn : ∀ᵐ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)
        ∂((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))),
        0 ≤ Submission.BoseGases.g2 v h (p.1 - p.2) :=
      hqmp.ae (Submission.BoseGases.g2_nonneg_ae (R := R0) hR0 hv hvrad hv_supp h)
    filter_upwards [hgnn] with p hp
    simp only [Submission.BoseGases.wSmallPair, Submission.BoseGases.wSmallScaled]
    exact mul_nonneg (mul_nonneg (Work.SmallBoxSliding.chiSmallB_nonneg M ℓ d u p.1)
      (div_nonneg (div_nonneg hp
          (Work.BoseFixB1.convScaleSmall_nonneg M (ℓ * d) (p.1 - p.2)))
        (Submission.BoseGases.convScale_nonneg ℓ (p.1 - p.2))))
      (Work.SmallBoxSliding.chiSmallB_nonneg M ℓ d u p.2)
  have hmono : (∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) p.1 p.2)
      ≤ ∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ,
          2 * Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2 := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
    · filter_upwards [hw2nn.filter_mono
        (MeasureTheory.ae_mono MeasureTheory.Measure.restrict_le_self)] with p hp
      exact hp
    · exact (hInt1.const_mul 2)
    · filter_upwards [hpt.filter_mono
        (MeasureTheory.ae_mono MeasureTheory.Measure.restrict_le_self)] with p hp
      exact hp
  have htwice : (∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ,
        2 * Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2)
      = 2 * ∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2 :=
    MeasureTheory.integral_const_mul 2 _
  have hfinal : (∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) p.1 p.2)
      ≤ 2 * ∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2 := by
    rw [← htwice]
    exact hmono
  exact hfinal


theorem boxSlack_le_pcBlock {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : Work.UBB.ScatSol v) {M : ℕ} (hM : 1 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hμ : 0 < μ)
        (u : EuclideanSpace ℝ (Fin 3)) (hμv : 1 ≤ μ * Work.SmallBoxSliding.boxMass ℓ d u)
        (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
        (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
        {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
        (hI : ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 = 1)
        (hM1nn : 0 ≤ Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmall1Pair h M ℓ d u))
        (hM2 : Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u)
            ≤ Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u)
                (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)))
        (hPcnn : 0 ≤ Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
            (Submission.BoseGases.dlBox ℓ d u) Φ)
        (hcS2 : Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ
                * Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ
                - Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ
              ≤ Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ),
        Work.BoseFixB1.rungSlack (Work.SmallBoxSliding.boxMass ℓ d u)
            (Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u))
            (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u) Φ)
        ≤ Work.BoseFixB1.rungPCBlock (Work.SmallBoxSliding.boxMass ℓ d u)
            (Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)))
            (Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u))
            (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u) Φ)
            (Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u) Φ)
          + C * (_root_.BoseGases.a v)
              * Work.BoseFixB1.rungRate (Work.SmallBoxSliding.boxMass ℓ d u) μ
                  (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                    (Submission.BoseGases.dlBox ℓ d u) Φ)
              * Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ := by sorry

end Work.BoseFixB1
