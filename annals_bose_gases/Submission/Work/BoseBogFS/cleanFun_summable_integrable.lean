import ChallengeDeps
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.measurable_cleanFun
import Submission.Work.BoseBogFS.tauAt_rows
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-!
# `Work.BoseBogFS.cleanFun_summable_integrable` — summability and integrability of the clean row

The clean part of the zero-point summand (FS `eq:LHYIntegral1`)

`cleanFun v h ρ μ k = 𝒵(τ(k)+c(k), c(k)) − c(k)²/(2‖k‖²)`,   `𝒵(𝒜,ℬ) = 𝒜 − √(𝒜²−ℬ²)`,

is summable over the full dual lattice and integrable over `ℝ³`.  The proof is a single explicit
pointwise majorant.  Writing `τ = tauAt v μ`, `c = cAt v h ρ μ = ρ·Ŵ₁`,

* `0 ≤ τ ≤ ‖k‖²` and `‖k‖² − τ(k) ≤ θ‖k‖` with `θ = 2/(dsℓ)` (the three rows of
  `Work.BoseBogFS.tauAt_rows`),
* `|c(k)| ≤ C/(1+‖k‖)` (`Work.BoseFixR.LatGreen.W1funDecay` gives the `1/‖k‖` decay of `Ŵ₁`, and
  `CloseCondFS` bounds `|ρ|`),

and `Work.BoseBogFS.bogZeroPoint_majorant` turns those into

`|cleanFun (k)| ≤ A·((‖k‖²)⁻¹(1+‖k‖)⁻⁴) + B·(1+‖k‖)⁻⁴`

for some constants `A, B ≥ 0` depending on `θ, C` (and *not* on `k`).  The two terms of the
majorant are integrable over `ℝ³` — `Work.BoseRowsFS.integrable_inv2_inv4_r3` and
`Mathlib.integrable_one_add_norm` at `r = 4` — and, evaluated at the lattice points
`k_n = ℓ⁻¹ • vec n`, are dominated by `((1 + ‖vec n‖²)²)⁻¹`, which is summable by
`Work.BoseK15.sum_inv_one_add_norm_le`.

The elementary lattice bookkeeping (the two pointwise comparisons at the lattice points and the
two summability statements) is isolated in the `csi_*` lemmas below.
-/

/-! ## 1. The lattice bookkeeping -/

/-- The zero label is the zero vector. -/
lemma csi_vec_zero : (Work.BoseB4.vec (0 : Fin 3 → ℤ) : E3) = 0 := by
  ext i
  simp [Work.BoseB4.vec]

/-- A non-zero label has norm at least `2π` (`vec n = 2π • n` with `‖n‖ ≥ 1`). -/
lemma csi_two_pi_le_norm_vec (n : Fin 3 → ℤ) (hn : n ≠ 0) :
    2 * Real.pi ≤ ‖(Work.BoseB4.vec n : E3)‖ := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hn
  have h1 : (1 : ℝ) ≤ |((n i : ℤ) : ℝ)| := by
    have : (1 : ℤ) ≤ |n i| := Int.one_le_abs hi
    exact_mod_cast this
  have hcoord : (Work.BoseB4.vec n).ofLp i = 2 * Real.pi * (n i : ℝ) := rfl
  have h2 : ‖(Work.BoseB4.vec n).ofLp i‖ ≤ ‖(Work.BoseB4.vec n : E3)‖ := PiLp.norm_apply_le _ _
  rw [hcoord] at h2
  have h3 : ‖(2 * Real.pi * (n i : ℝ) : ℝ)‖ = 2 * Real.pi * |((n i : ℤ) : ℝ)| := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
  rw [h3] at h2
  nlinarith [Real.pi_pos]

/-- At a non-zero label, `(‖ℓ⁻¹ • vec n‖²)⁻¹ ≤ (ℓ/2π)²`. -/
lemma csi_inv2_le (L : ℝ) (hL : 1 ≤ L) (n : Fin 3 → ℤ) (hn : n ≠ 0) :
    ((‖(L⁻¹ : ℝ) • (Work.BoseB4.vec n : E3)‖) ^ 2)⁻¹ ≤ (L / (2 * Real.pi)) ^ 2 := by
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  have hx : 2 * Real.pi ≤ ‖(Work.BoseB4.vec n : E3)‖ := csi_two_pi_le_norm_vec n hn
  have hnorm : ‖(L⁻¹ : ℝ) • (Work.BoseB4.vec n : E3)‖ = ‖(Work.BoseB4.vec n : E3)‖ / L := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hL0.le), inv_mul_eq_div]
  rw [hnorm]
  have hge : 2 * Real.pi / L ≤ ‖(Work.BoseB4.vec n : E3)‖ / L := by
    rw [div_le_div_iff_of_pos_right hL0]; linarith
  have hpos : 0 < 2 * Real.pi / L := by positivity
  have hpos2 : 0 < ‖(Work.BoseB4.vec n : E3)‖ / L :=
    div_pos (lt_of_lt_of_le (by positivity : (0:ℝ) < 2 * Real.pi) hx) hL0
  calc ((‖(Work.BoseB4.vec n : E3)‖ / L) ^ 2)⁻¹ ≤ ((2 * Real.pi / L) ^ 2)⁻¹ := by
        rw [inv_le_inv₀ (pow_pos hpos2 2) (pow_pos hpos 2)]
        exact pow_le_pow_left₀ (by positivity) hge 2
    _ = (L / (2 * Real.pi)) ^ 2 := by rw [div_pow, inv_div, div_pow]

/-- `(1 + ‖ℓ⁻¹ • vec n‖)⁻⁴ ≤ ℓ⁴ (1 + ‖vec n‖²)⁻²` (`ℓ ≥ 1`). -/
lemma csi_inv4_le (L : ℝ) (hL : 1 ≤ L) (n : Fin 3 → ℤ) :
    ((1 + ‖(L⁻¹ : ℝ) • (Work.BoseB4.vec n : E3)‖) ^ 4)⁻¹
      ≤ L ^ 4 * ((1 + ‖(Work.BoseB4.vec n : E3)‖ ^ 2) ^ 2)⁻¹ := by
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  set x : ℝ := ‖(Work.BoseB4.vec n : E3)‖ with hx
  have hnorm : ‖(L⁻¹ : ℝ) • (Work.BoseB4.vec n : E3)‖ = x / L := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hL0.le), inv_mul_eq_div, ← hx]
  rw [hnorm]
  have h1 : (1 + x / L) = (L + x) / L := by field_simp
  rw [h1]
  have hLx : 0 < (L + x) / L := by
    apply div_pos _ hL0
    have : 0 ≤ x := by rw [hx]; exact norm_nonneg _
    linarith
  have h1x : 0 < (1 + x) / L := by
    apply div_pos _ hL0
    have : 0 ≤ x := by rw [hx]; exact norm_nonneg _
    linarith
  have h2 : ((1 + x) / L) ≤ (L + x) / L := by
    rw [div_le_div_iff_of_pos_right hL0]; linarith
  have h4a : (((L + x) / L) ^ 4)⁻¹ ≤ (((1 + x) / L) ^ 4)⁻¹ := by
    rw [inv_le_inv₀ (pow_pos hLx 4) (pow_pos h1x 4)]
    exact pow_le_pow_left₀ (by positivity) h2 4
  have h4b : (((1 + x) / L) ^ 4)⁻¹ = L ^ 4 * ((1 + x) ^ 4)⁻¹ := by
    rw [div_pow, inv_div, div_eq_mul_inv]
  have h6 : ((1 + x) ^ 4)⁻¹ ≤ ((1 + x ^ 2) ^ 2)⁻¹ := by
    have hx0 : 0 ≤ x := by rw [hx]; exact norm_nonneg _
    have hp1 : (0:ℝ) < (1+x)^4 := by positivity
    have hp2 : (0:ℝ) < (1 + x^2)^2 := by positivity
    rw [inv_le_inv₀ hp1 hp2]
    have h7 : 1 + x ^ 2 ≤ (1 + x) ^ 2 := by nlinarith
    calc (1 + x ^ 2) ^ 2 ≤ ((1 + x) ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) h7 2
      _ = (1 + x) ^ 4 := by ring
  calc (((L + x) / L) ^ 4)⁻¹ ≤ (((1 + x) / L) ^ 4)⁻¹ := h4a
    _ = L ^ 4 * ((1 + x) ^ 4)⁻¹ := h4b
    _ ≤ L ^ 4 * ((1 + x ^ 2) ^ 2)⁻¹ := by
        apply mul_le_mul_of_nonneg_left h6 (by positivity)

/-- The comparison family of the lattice sums: `((1 + ‖vec n‖²)²)⁻¹` is summable
(`Work.BoseK15.sum_inv_one_add_norm_le` at `s = 2`, `3 < 2·2`). -/
lemma csi_summable_lattice_base : Summable (fun n : Fin 3 → ℤ =>
    (((1 : ℝ) + ‖(Work.BoseB4.vec n : E3)‖ ^ 2) ^ 2)⁻¹) := by
  obtain ⟨C₀, _hC₀0, hC₀⟩ := Work.BoseK15.sum_inv_one_add_norm_le 2 (by norm_num)
  exact summable_of_sum_le (fun n => by positivity) hC₀

/-- The `1/‖k‖²` part of the majorant is summable on the lattice. -/
lemma csi_summable_first (A L : ℝ) (hA : 0 ≤ A) (hL : 1 ≤ L) :
    Summable (fun n : Fin 3 → ℤ =>
      A * (((‖(L⁻¹ : ℝ) • (Work.BoseB4.vec n : E3)‖) ^ 2)⁻¹
             * ((1 + ‖(L⁻¹ : ℝ) • (Work.BoseB4.vec n : E3)‖) ^ 4)⁻¹)) := by
  have hf := csi_summable_lattice_base
  refine Summable.of_norm_bounded (hf.mul_left (A * (L / (2 * Real.pi)) ^ 2 * L ^ 4)) (fun n => ?_)
  have hP : 0 ≤ ((‖(L⁻¹ : ℝ) • (Work.BoseB4.vec n : E3)‖) ^ 2)⁻¹
      * ((1 + ‖(L⁻¹ : ℝ) • (Work.BoseB4.vec n : E3)‖) ^ 4)⁻¹ := by positivity
  have hval : (0:ℝ) ≤ A * (((‖(L⁻¹ : ℝ) • (Work.BoseB4.vec n : E3)‖) ^ 2)⁻¹
      * ((1 + ‖(L⁻¹ : ℝ) • (Work.BoseB4.vec n : E3)‖) ^ 4)⁻¹) := mul_nonneg hA hP
  rw [Real.norm_eq_abs, abs_of_nonneg hval]
  by_cases hn : n = 0
  · subst hn
    have hthis : ((‖(L⁻¹ : ℝ) • (Work.BoseB4.vec (0 : Fin 3 → ℤ) : E3)‖) ^ 2)⁻¹ = 0 := by
      rw [csi_vec_zero, smul_zero, norm_zero]
      norm_num
    rw [hthis, zero_mul, mul_zero]
    positivity
  · have h1 := csi_inv2_le L hL n hn
    have h2 := csi_inv4_le L hL n
    have h2nn : 0 ≤ ((1 + ‖(L⁻¹ : ℝ) • (Work.BoseB4.vec n : E3)‖) ^ 4)⁻¹ := by positivity
    have hprod := mul_le_mul h1 h2 h2nn (by positivity : (0:ℝ) ≤ (L / (2 * Real.pi)) ^ 2)
    calc A * (((‖(L⁻¹ : ℝ) • (Work.BoseB4.vec n : E3)‖) ^ 2)⁻¹
          * ((1 + ‖(L⁻¹ : ℝ) • (Work.BoseB4.vec n : E3)‖) ^ 4)⁻¹)
        ≤ A * ((L / (2 * Real.pi)) ^ 2
            * (L ^ 4 * ((1 + ‖(Work.BoseB4.vec n : E3)‖ ^ 2) ^ 2)⁻¹)) :=
          mul_le_mul_of_nonneg_left hprod hA
      _ = A * (L / (2 * Real.pi)) ^ 2 * L ^ 4
            * ((1 + ‖(Work.BoseB4.vec n : E3)‖ ^ 2) ^ 2)⁻¹ := by ring

/-- The `(1+‖k‖)⁻⁴` part of the majorant is summable on the lattice. -/
lemma csi_summable_second (B L : ℝ) (hB : 0 ≤ B) (hL : 1 ≤ L) :
    Summable (fun n : Fin 3 → ℤ =>
      B * ((1 + ‖(L⁻¹ : ℝ) • (Work.BoseB4.vec n : E3)‖) ^ 4)⁻¹) := by
  have hf := csi_summable_lattice_base
  refine Summable.of_norm_bounded (hf.mul_left (B * L ^ 4)) (fun n => ?_)
  have h1 : (0:ℝ) ≤ ((1 + ‖(L⁻¹ : ℝ) • (Work.BoseB4.vec n : E3)‖) ^ 4)⁻¹ := by positivity
  have h2 : (0:ℝ) ≤ B * ((1 + ‖(L⁻¹ : ℝ) • (Work.BoseB4.vec n : E3)‖) ^ 4)⁻¹ :=
    mul_nonneg hB h1
  rw [Real.norm_eq_abs, abs_of_nonneg h2]
  calc B * ((1 + ‖(L⁻¹ : ℝ) • (Work.BoseB4.vec n : E3)‖) ^ 4)⁻¹
      ≤ B * (L ^ 4 * ((1 + ‖(Work.BoseB4.vec n : E3)‖ ^ 2) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left (csi_inv4_le L hL n) hB
    _ = B * L ^ 4 * ((1 + ‖(Work.BoseB4.vec n : E3)‖ ^ 2) ^ 2)⁻¹ := by ring

/-! ## 2. Integrability of the majorant -/

/-- `(1+‖k‖)⁻⁴` is integrable on `ℝ³` (`r = 4 > 3 = finrank`). -/
lemma csi_integrable_inv4 : Integrable (fun k : E3 => ((1 + ‖k‖) ^ 4)⁻¹) := by
  have h : Integrable (fun k : E3 => (1 + ‖k‖) ^ (-(4:ℝ))) :=
    integrable_one_add_norm (E := E3) (r := 4)
      (by rw [finrank_euclideanSpace_fin]; norm_num)
  refine h.congr (Eventually.of_forall (fun k => ?_))
  dsimp only
  rw [Real.rpow_neg (by positivity : (0:ℝ) ≤ 1 + ‖k‖)]
  congr 1
  exact Real.rpow_natCast _ 4

/-- The explicit majorant is integrable on `ℝ³`. -/
lemma csi_integrable_majorant (A B : ℝ) :
    Integrable (fun k : E3 =>
      A * ((‖k‖ ^ 2)⁻¹ * ((1 + ‖k‖) ^ 4)⁻¹) + B * ((1 + ‖k‖) ^ 4)⁻¹) := by
  have h1 : Integrable (fun k : E3 => (‖k‖ ^ 2)⁻¹ * ((1 + ‖k‖) ^ 4)⁻¹) :=
    Work.BoseRowsFS.integrable_inv2_inv4_r3
  exact (h1.const_mul A).add (csi_integrable_inv4.const_mul B)

/-! ## 3. The bound on the pairing coefficient `c = ρ·Ŵ₁` -/

/-- Under the close condition, `|cAt v h ρ μ k| ≤ C/(1+‖k‖)`: the decay is
`Work.BoseFixR.LatGreen.W1funDecay`'s `|Ŵ₁(q)| ≤ Cw/(1+‖q‖)` and the prefactor is the bound
`|ρ| ≤ μ + closeThresholdFS v μ` carried by `CloseCondFS`. -/
lemma csi_cAt_abs_le {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R μ ρ : ℝ}
    (hR : 0 < R) (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v) (hv : ∀ x, 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hℓ : 0 < ell v μ)
    (hRℓ : R ≤ ell v μ * Submission.BoseGases.chiR0)
    (hρ : Work.BoseBoxFock.CloseCondFS v μ ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : E3, |cAt v h ρ μ k| ≤ C / (1 + ‖k‖) := by
  obtain ⟨Cw, hCw0, hCw⟩ :=
    Work.BoseFixR.LatGreen.W1funDecay (v := v) h hv hvrad hR hℓ hv_supp hRℓ
  have hKl : 0 < (paramsAt μ (_root_.BoseGases.a v)).Kl := by
    have : (paramsAt μ (_root_.BoseGases.a v)).Kl
        = fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-(3 / 2)) := by
      simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    rw [this]
    exact fsXp_pos (mul_pos hμ (pow_pos hav 3))
  have hthr0 : 0 ≤ Work.BoseBoxFock.closeThresholdFS v μ := by
    rw [Work.BoseBoxFock.closeThresholdFS, div_nonneg_iff]
    left
    exact ⟨mul_nonneg hμ.le (Real.rpow_nonneg hKl.le _), by positivity⟩
  have hρb : |ρ| ≤ μ + Work.BoseBoxFock.closeThresholdFS v μ := by
    rw [Work.BoseBoxFock.CloseCondFS] at hρ
    calc |ρ| = |(ρ - μ) + μ| := by ring_nf
      _ ≤ |ρ - μ| + |μ| := abs_add_le _ _
      _ ≤ Work.BoseBoxFock.closeThresholdFS v μ + μ := by rw [abs_of_pos hμ]; linarith
      _ = μ + Work.BoseBoxFock.closeThresholdFS v μ := by ring
  refine ⟨(μ + Work.BoseBoxFock.closeThresholdFS v μ) * Cw, by positivity, fun k => ?_⟩
  have hck : cAt v h ρ μ k = ρ * chat (Work.BoseFixR.W1fun v h (ell v μ)) k := rfl
  rw [hck, abs_mul]
  calc |ρ| * |chat (Work.BoseFixR.W1fun v h (ell v μ)) k|
      ≤ (μ + Work.BoseBoxFock.closeThresholdFS v μ) * (Cw / (1 + ‖k‖)) :=
        mul_le_mul hρb (hCw k) (abs_nonneg _) (add_nonneg hμ.le hthr0)
    _ = (μ + Work.BoseBoxFock.closeThresholdFS v μ) * Cw / (1 + ‖k‖) := by ring

/-! ## 4. The pointwise majorant of the clean summand

`𝒵(τ+c, c) − c²/(2‖k‖²)` is bounded by an explicit integrable summable majorant, using only
`0 ≤ τ ≤ ‖k‖²`, the linear kinetic deficit `‖k‖² − τ(k) ≤ θ‖k‖` and the decay
`|c(k)| ≤ C/(1+‖k‖)`.

The two elementary facts used are

* `|𝒵(A,B)| ≤ 2|A|` for **all** real `A, B` (the junk branch `A² < B²` of `Real.sqrt` is
  harmless, since `√(A²−B²) ∈ [0,|A|]` always), and
* `𝒵(A,B) = B²/(A + √(A²−B²))` when `B² ≤ A²` and the denominator is positive.

Beyond `K = max 1 (max (2θ) (2√C+1))` one has `τ ≥ ‖k‖²/2 ≥ 2C ≥ 2|c|`, so `τ+c > 0`,
`τ² + 2τc ≥ 0` and the second identity applies with `S := τ + c + √(τ²+2τc) ≥ ‖k‖²/4`;
whence `|𝒵 − c²/(2‖k‖²)| ≤ 4c²/‖k‖² + c²/(2‖k‖²) ≤ 5C²/((1+‖k‖)²‖k‖²) ≤ 32C²(1+‖k‖)⁻⁴`.
Below `K` the crude bound `|𝒵| ≤ 2|τ+c|` gives `2(K²+C) + (C²/2)(‖k‖²)⁻¹`, and both terms are
dominated by the majorant on `{‖k‖ ≤ K}` since `(1+‖k‖)⁻⁴ ≥ (1+K)⁻⁴` there. -/

/-- `|𝒵(A,B)| ≤ 2|A|` for all real `A, B` (no sign hypotheses on `B`). -/
lemma csi_abs_bogZeroPoint_le (A B : ℝ) : |Work.BoseB6.bogZeroPoint A B| ≤ 2 * |A| := by
  have hR : Real.sqrt (A ^ 2 - B ^ 2) ≤ |A| := by
    calc Real.sqrt (A ^ 2 - B ^ 2) ≤ Real.sqrt (A ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_nonneg B])
      _ = |A| := Real.sqrt_sq_eq_abs A
  have hR0 : 0 ≤ Real.sqrt (A ^ 2 - B ^ 2) := Real.sqrt_nonneg _
  rw [Work.BoseB6.bogZeroPoint]
  calc |A - Real.sqrt (A ^ 2 - B ^ 2)| ≤ |A| + |Real.sqrt (A ^ 2 - B ^ 2)| := abs_sub _ _
    _ = |A| + Real.sqrt (A ^ 2 - B ^ 2) := by rw [abs_of_nonneg hR0]
    _ ≤ |A| + |A| := by linarith
    _ = 2 * |A| := by ring

/-- `𝒵(A,B) = B²/(A + √(A²−B²))` when `B² ≤ A²` and the denominator is positive. -/
lemma csi_bog_zero_eq_div (A B : ℝ) (hAB : B ^ 2 ≤ A ^ 2)
    (hden : 0 < A + Real.sqrt (A ^ 2 - B ^ 2)) :
    Work.BoseB6.bogZeroPoint A B = B ^ 2 / (A + Real.sqrt (A ^ 2 - B ^ 2)) := by
  have h0 : 0 ≤ A ^ 2 - B ^ 2 := by linarith
  have hR2 : Real.sqrt (A ^ 2 - B ^ 2) ^ 2 = A ^ 2 - B ^ 2 := Real.sq_sqrt h0
  rw [Work.BoseB6.bogZeroPoint, eq_div_iff (ne_of_gt hden)]
  nlinarith [hR2]

/-- **The pointwise majorant.** -/
lemma csi_bogZeroPoint_majorant {τ c : E3 → ℝ} {θ C : ℝ} (hθ : 0 ≤ θ) (hC : 0 ≤ C)
    (hτ0 : ∀ k : E3, 0 ≤ τ k) (hτ1 : ∀ k : E3, τ k ≤ ‖k‖ ^ 2)
    (hτ2 : ∀ k : E3, ‖k‖ ^ 2 - τ k ≤ θ * ‖k‖)
    (hc : ∀ k : E3, |c k| ≤ C / (1 + ‖k‖)) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ k : E3,
      |Work.BoseB6.bogZeroPoint (τ k + c k) (c k) - (c k) ^ 2 / (2 * ‖k‖ ^ 2)|
        ≤ A * ((‖k‖ ^ 2)⁻¹ * ((1 + ‖k‖) ^ 4)⁻¹) + B * ((1 + ‖k‖) ^ 4)⁻¹ := by
  set K : ℝ := max 1 (max (2 * θ) (2 * Real.sqrt C + 1)) with hKdef
  have hK1 : 1 ≤ K := by rw [hKdef]; exact le_max_left _ _
  have hKθ : 2 * θ ≤ K := by
    rw [hKdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hKs : 2 * Real.sqrt C + 1 ≤ K := by
    rw [hKdef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK1
  refine ⟨(C ^ 2 / 2 + 1) * (1 + K) ^ 4, (2 * (K ^ 2 + C) + 1) * (1 + K) ^ 4 + 32 * C ^ 2,
    by positivity, by positivity, fun k => ?_⟩
  have hYnn : (0:ℝ) ≤ ((1 + ‖k‖) ^ 4)⁻¹ := by positivity
  have hXnn : (0:ℝ) ≤ (‖k‖ ^ 2)⁻¹ := by positivity
  have hcC : |c k| ≤ C := by
    have h1 : C / (1 + ‖k‖) ≤ C := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 1 + ‖k‖)]; nlinarith [norm_nonneg k, hC]
    linarith [hc k]
  have hK4 : ((1 + K) ^ 4) ≠ 0 := by positivity
  by_cases hk : ‖k‖ ≤ K
  · -- ═══ interior `‖k‖ ≤ K` ═══
    have h1K : (1 + ‖k‖) ^ 4 ≤ (1 + K) ^ 4 :=
      pow_le_pow_left₀ (by linarith [norm_nonneg k]) (by linarith [hk]) 4
    have hw : ((1 + K) ^ 4)⁻¹ ≤ ((1 + ‖k‖) ^ 4)⁻¹ := by
      rw [inv_le_inv₀ (by positivity) (by positivity)]; exact h1K
    have hτk : τ k ≤ K ^ 2 := by
      have h := hτ1 k; nlinarith [norm_nonneg k, hk, h]
    have hcC2 : (c k) ^ 2 ≤ C ^ 2 := by
      calc (c k) ^ 2 = |c k| ^ 2 := (sq_abs _).symm
        _ ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hcC 2
    have hbound : |Work.BoseB6.bogZeroPoint (τ k + c k) (c k) - (c k) ^ 2 / (2 * ‖k‖ ^ 2)|
        ≤ 2 * (K ^ 2 + C) + (C ^ 2 / 2) * ((‖k‖ ^ 2)⁻¹) := by
      have h2 : |τ k + c k| ≤ τ k + |c k| := by
        have h := abs_add_le (τ k) (c k)
        rwa [abs_of_nonneg (hτ0 k)] at h
      have h3 : (c k) ^ 2 / (2 * ‖k‖ ^ 2) ≤ (C ^ 2 / 2) * ((‖k‖ ^ 2)⁻¹) := by
        calc (c k) ^ 2 / (2 * ‖k‖ ^ 2) = (c k) ^ 2 * (2 * ‖k‖ ^ 2)⁻¹ := by rw [div_eq_mul_inv]
          _ ≤ C ^ 2 * (2 * ‖k‖ ^ 2)⁻¹ :=
              mul_le_mul_of_nonneg_right hcC2 (by positivity)
          _ = (C ^ 2 / 2) * ((‖k‖ ^ 2)⁻¹) := by rw [mul_inv]; ring
      have h4 : |(c k) ^ 2 / (2 * ‖k‖ ^ 2)| = (c k) ^ 2 / (2 * ‖k‖ ^ 2) :=
        abs_of_nonneg (by positivity)
      calc |Work.BoseB6.bogZeroPoint (τ k + c k) (c k) - (c k) ^ 2 / (2 * ‖k‖ ^ 2)|
          ≤ |Work.BoseB6.bogZeroPoint (τ k + c k) (c k)| + |(c k) ^ 2 / (2 * ‖k‖ ^ 2)| :=
            abs_sub _ _
        _ ≤ 2 * (τ k + |c k|) + (c k) ^ 2 / (2 * ‖k‖ ^ 2) := by
            rw [h4]; linarith [csi_abs_bogZeroPoint_le (τ k + c k) (c k)]
        _ ≤ 2 * (K ^ 2 + C) + (C ^ 2 / 2) * ((‖k‖ ^ 2)⁻¹) := by linarith
    have hAY : (C ^ 2 / 2) ≤ ((C ^ 2 / 2 + 1) * (1 + K) ^ 4) * ((1 + ‖k‖) ^ 4)⁻¹ := by
      have h1 : (C ^ 2 / 2 + 1) ≤ ((C ^ 2 / 2 + 1) * (1 + K) ^ 4) * ((1 + ‖k‖) ^ 4)⁻¹ := by
        calc (C ^ 2 / 2 + 1) = ((C ^ 2 / 2 + 1) * (1 + K) ^ 4) * ((1 + K) ^ 4)⁻¹ := by
              rw [mul_assoc, mul_inv_cancel₀ hK4, mul_one]
          _ ≤ ((C ^ 2 / 2 + 1) * (1 + K) ^ 4) * ((1 + ‖k‖) ^ 4)⁻¹ :=
              mul_le_mul_of_nonneg_left hw (by positivity)
      linarith [sq_nonneg C]
    have hBY : 2 * (K ^ 2 + C)
        ≤ ((2 * (K ^ 2 + C) + 1) * (1 + K) ^ 4 + 32 * C ^ 2) * ((1 + ‖k‖) ^ 4)⁻¹ := by
      have h1 : 2 * (K ^ 2 + C) + 1
          ≤ ((2 * (K ^ 2 + C) + 1) * (1 + K) ^ 4) * ((1 + ‖k‖) ^ 4)⁻¹ := by
        calc 2 * (K ^ 2 + C) + 1
            = ((2 * (K ^ 2 + C) + 1) * (1 + K) ^ 4) * ((1 + K) ^ 4)⁻¹ := by
              rw [mul_assoc, mul_inv_cancel₀ hK4, mul_one]
          _ ≤ ((2 * (K ^ 2 + C) + 1) * (1 + K) ^ 4) * ((1 + ‖k‖) ^ 4)⁻¹ :=
              mul_le_mul_of_nonneg_left hw (by positivity)
      have h2 : ((2 * (K ^ 2 + C) + 1) * (1 + K) ^ 4) * ((1 + ‖k‖) ^ 4)⁻¹
          ≤ ((2 * (K ^ 2 + C) + 1) * (1 + K) ^ 4 + 32 * C ^ 2) * ((1 + ‖k‖) ^ 4)⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ hYnn
        have h3 : 0 ≤ (2 * (K ^ 2 + C) + 1) * (1 + K) ^ 4 := by positivity
        linarith [sq_nonneg C]
      linarith
    have hAp : (C ^ 2 / 2) * (‖k‖ ^ 2)⁻¹
        ≤ ((C ^ 2 / 2 + 1) * (1 + K) ^ 4) * ((‖k‖ ^ 2)⁻¹ * ((1 + ‖k‖) ^ 4)⁻¹) := by
      calc (C ^ 2 / 2) * (‖k‖ ^ 2)⁻¹
          ≤ (((C ^ 2 / 2 + 1) * (1 + K) ^ 4) * ((1 + ‖k‖) ^ 4)⁻¹) * (‖k‖ ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right hAY hXnn
        _ = ((C ^ 2 / 2 + 1) * (1 + K) ^ 4) * ((‖k‖ ^ 2)⁻¹ * ((1 + ‖k‖) ^ 4)⁻¹) := by ring
    have hcomb := add_le_add hAp hBY
    calc |Work.BoseB6.bogZeroPoint (τ k + c k) (c k) - (c k) ^ 2 / (2 * ‖k‖ ^ 2)|
        ≤ 2 * (K ^ 2 + C) + (C ^ 2 / 2) * ((‖k‖ ^ 2)⁻¹) := hbound
      _ = (C ^ 2 / 2) * (‖k‖ ^ 2)⁻¹ + 2 * (K ^ 2 + C) := by ring
      _ ≤ ((C ^ 2 / 2 + 1) * (1 + K) ^ 4) * ((‖k‖ ^ 2)⁻¹ * ((1 + ‖k‖) ^ 4)⁻¹)
            + ((2 * (K ^ 2 + C) + 1) * (1 + K) ^ 4 + 32 * C ^ 2)
              * ((1 + ‖k‖) ^ 4)⁻¹ := hcomb
  · -- ═══ exterior `K < ‖k‖` ═══
    have hkK : K ≤ ‖k‖ := le_of_lt (not_le.mp hk)
    have hk0 : 0 < ‖k‖ := lt_of_lt_of_le hK0 hkK
    have hk2 : 0 < ‖k‖ ^ 2 := pow_pos hk0 2
    have hτlow : ‖k‖ ^ 2 / 2 ≤ τ k := by
      have h := hτ2 k
      have h2 : θ * ‖k‖ ≤ ‖k‖ ^ 2 / 2 := by nlinarith [hKθ, hkK, hk0]
      linarith
    have hτC : 2 * C ≤ τ k := by
      have hKs' : 2 * C ≤ K ^ 2 / 2 := by
        nlinarith [hC, Real.sqrt_nonneg C, Real.sq_sqrt hC, hKs]
      nlinarith [hτlow, hKs', hkK, hk2]
    have hca : |c k| ≤ τ k / 2 := by linarith
    have hcl : -|c k| ≤ c k := neg_abs_le _
    have hsq : (c k) ^ 2 ≤ (τ k + c k) ^ 2 := by
      nlinarith [hτ0 k, hca, hcl, le_abs_self (c k)]
    have hSpos : 0 < τ k + c k + Real.sqrt (τ k ^ 2 + 2 * τ k * c k) := by
      have h1 : 0 ≤ Real.sqrt (τ k ^ 2 + 2 * τ k * c k) := Real.sqrt_nonneg _
      have h2 : τ k / 2 ≤ τ k + c k := by linarith
      linarith [hτlow]
    have harg : (τ k + c k) ^ 2 - (c k) ^ 2 = τ k ^ 2 + 2 * τ k * c k := by ring
    have hid : Work.BoseB6.bogZeroPoint (τ k + c k) (c k)
        = (c k) ^ 2 / (τ k + c k + Real.sqrt (τ k ^ 2 + 2 * τ k * c k)) := by
      have hden : 0 < (τ k + c k) + Real.sqrt ((τ k + c k) ^ 2 - (c k) ^ 2) := by
        rw [harg]; exact hSpos
      have h := csi_bog_zero_eq_div (τ k + c k) (c k) hsq hden
      rwa [harg] at h
    have hSlow : ‖k‖ ^ 2 / 4 ≤ τ k + c k + Real.sqrt (τ k ^ 2 + 2 * τ k * c k) := by
      have h1 : τ k / 2 ≤ τ k + c k := by linarith
      have h2 : 0 ≤ Real.sqrt (τ k ^ 2 + 2 * τ k * c k) := Real.sqrt_nonneg _
      linarith [hτlow]
    rw [hid]
    have hb1 : (c k) ^ 2 / (τ k + c k + Real.sqrt (τ k ^ 2 + 2 * τ k * c k))
        ≤ 4 * (c k) ^ 2 / ‖k‖ ^ 2 := by
      rw [div_le_div_iff₀ hSpos hk2]
      nlinarith [hSlow, sq_nonneg (c k), sq_nonneg ‖k‖, hk0]
    have hb2 : (c k) ^ 2 / (2 * ‖k‖ ^ 2) ≤ (c k) ^ 2 / ‖k‖ ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) hk2]
      nlinarith [sq_nonneg (c k), sq_nonneg ‖k‖]
    have hc2 : (c k) ^ 2 ≤ C ^ 2 * ((1 + ‖k‖) ^ 2)⁻¹ := by
      have h1 : |c k| ≤ C * (1 + ‖k‖)⁻¹ := by
        have h2 := hc k
        rwa [div_eq_mul_inv] at h2
      calc (c k) ^ 2 = |c k| ^ 2 := (sq_abs _).symm
        _ ≤ (C * (1 + ‖k‖)⁻¹) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ = C ^ 2 * ((1 + ‖k‖) ^ 2)⁻¹ := by rw [mul_pow, inv_pow]
    have hc3 : (c k) ^ 2 * (1 + ‖k‖) ^ 2 ≤ C ^ 2 := by
      rw [← div_eq_mul_inv] at hc2
      rwa [le_div_iff₀ (by positivity : (0:ℝ) < (1 + ‖k‖) ^ 2)] at hc2
    have h1 : (1 + ‖k‖) ^ 2 ≤ 4 * ‖k‖ ^ 2 := by nlinarith [hkK, hK1, norm_nonneg k]
    have h2 : 5 * (c k) ^ 2 / ‖k‖ ^ 2 ≤ 5 * C ^ 2 / ((1 + ‖k‖) ^ 2 * ‖k‖ ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hc3, sq_nonneg ‖k‖]
    have key : 5 * C ^ 2 * (1 + ‖k‖) ^ 4 ≤ 32 * C ^ 2 * ((1 + ‖k‖) ^ 2 * ‖k‖ ^ 2) := by
      have h4 : 5 * (1 + ‖k‖) ^ 2 ≤ 32 * ‖k‖ ^ 2 := by nlinarith [h1, norm_nonneg k]
      calc 5 * C ^ 2 * (1 + ‖k‖) ^ 4
          = C ^ 2 * (1 + ‖k‖) ^ 2 * (5 * (1 + ‖k‖) ^ 2) := by ring
        _ ≤ C ^ 2 * (1 + ‖k‖) ^ 2 * (32 * ‖k‖ ^ 2) :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = 32 * C ^ 2 * ((1 + ‖k‖) ^ 2 * ‖k‖ ^ 2) := by ring
    have h3 : 5 * C ^ 2 / ((1 + ‖k‖) ^ 2 * ‖k‖ ^ 2) ≤ 32 * C ^ 2 * ((1 + ‖k‖) ^ 4)⁻¹ := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < (1 + ‖k‖) ^ 2 * ‖k‖ ^ 2)]
      rw [← div_eq_mul_inv, div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0:ℝ) < (1 + ‖k‖) ^ 4)]
      exact key
    have hext : |(c k) ^ 2 / (τ k + c k + Real.sqrt (τ k ^ 2 + 2 * τ k * c k))
        - (c k) ^ 2 / (2 * ‖k‖ ^ 2)| ≤ 32 * C ^ 2 * ((1 + ‖k‖) ^ 4)⁻¹ := by
      calc |(c k) ^ 2 / (τ k + c k + Real.sqrt (τ k ^ 2 + 2 * τ k * c k))
            - (c k) ^ 2 / (2 * ‖k‖ ^ 2)|
          ≤ |(c k) ^ 2 / (τ k + c k + Real.sqrt (τ k ^ 2 + 2 * τ k * c k))|
              + |(c k) ^ 2 / (2 * ‖k‖ ^ 2)| := abs_sub _ _
        _ = (c k) ^ 2 / (τ k + c k + Real.sqrt (τ k ^ 2 + 2 * τ k * c k))
              + (c k) ^ 2 / (2 * ‖k‖ ^ 2) := by
            rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
        _ ≤ 4 * (c k) ^ 2 / ‖k‖ ^ 2 + (c k) ^ 2 / ‖k‖ ^ 2 := add_le_add hb1 hb2
        _ = 5 * (c k) ^ 2 / ‖k‖ ^ 2 := by ring
        _ ≤ 32 * C ^ 2 * ((1 + ‖k‖) ^ 4)⁻¹ := le_trans h2 h3
    have hBterm : 32 * C ^ 2 * ((1 + ‖k‖) ^ 4)⁻¹
        ≤ ((2 * (K ^ 2 + C) + 1) * (1 + K) ^ 4 + 32 * C ^ 2) * ((1 + ‖k‖) ^ 4)⁻¹ := by
      apply mul_le_mul_of_nonneg_right _ hYnn
      have h6 : 0 ≤ (2 * (K ^ 2 + C) + 1) * (1 + K) ^ 4 := by positivity
      linarith [sq_nonneg C]
    have hAterm : 0 ≤ ((C ^ 2 / 2 + 1) * (1 + K) ^ 4) * ((‖k‖ ^ 2)⁻¹ * ((1 + ‖k‖) ^ 4)⁻¹) :=
      mul_nonneg (by positivity) (mul_nonneg hXnn hYnn)
    calc |(c k) ^ 2 / (τ k + c k + Real.sqrt (τ k ^ 2 + 2 * τ k * c k))
          - (c k) ^ 2 / (2 * ‖k‖ ^ 2)|
        ≤ 32 * C ^ 2 * ((1 + ‖k‖) ^ 4)⁻¹ := hext
      _ ≤ ((C ^ 2 / 2 + 1) * (1 + K) ^ 4) * ((‖k‖ ^ 2)⁻¹ * ((1 + ‖k‖) ^ 4)⁻¹)
            + ((2 * (K ^ 2 + C) + 1) * (1 + K) ^ 4 + 32 * C ^ 2)
              * ((1 + ‖k‖) ^ 4)⁻¹ := by
          linarith [hBterm, hAterm]

/-! ## 5. The row -/

theorem cleanFun_summable_integrable {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R : ℝ} (hR : 0 < R) (hv : ∀ x, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ ρ : ℝ,
      Work.BoseBoxFock.CloseCondFS v μ ρ →
        Summable (fun n : Fin 3 → ℤ => Work.BoseBogFS.cleanFun v h ρ μ (Work.BoseBogFS.kAt v μ n))
        ∧ MeasureTheory.Integrable (fun k : EuclideanSpace ℝ (Fin 3) =>
            Work.BoseBogFS.cleanFun v h ρ μ k) := by
  -- the two thresholds: the dilute regime (`R ≤ ℓ·chiR0`, `R/ℓ ≤ 1/4`, `C(R/ℓ)² ≤ 1/2`)
  -- and the large-box condition `1 ≤ ℓ`, together with `ε₀ ≤ 1`
  obtain ⟨ε₁, hε₁0, hε₁⟩ :=
    existsAdmRegime (v := v) (R := R) (C := 0) (r₁ := 1 / 4) hR hav le_rfl (by norm_num)
  obtain ⟨ε₂, hε₂0, hε₂⟩ := exists_adm_ell_ge (v := v) hav (M := 1) one_pos
  refine ⟨min (min ε₁ ε₂) 1, lt_min (lt_min hε₁0 hε₂0) one_pos, ?_⟩
  intro μ hAdm ρ hρ
  have hAdm₁ : Work.BoseBoxFix.Adm v ε₁ μ :=
    adm_mono (le_trans (min_le_left _ _) (min_le_left _ _)) hAdm
  have hAdm₂ : Work.BoseBoxFix.Adm v ε₂ μ :=
    adm_mono (le_trans (min_le_left _ _) (min_le_right _ _)) hAdm
  have hμ : 0 < μ := hAdm.1
  have ht1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 := le_trans hAdm.2.1 (min_le_right _ _)
  obtain ⟨hRℓ, _hr₁, _hcond⟩ := hε₁ μ hAdm₁
  have hℓ1 : 1 ≤ ell v μ := hε₂ μ hAdm₂
  have hℓ : 0 < ell v μ := lt_of_lt_of_le one_pos hℓ1
  -- the three rows of the kinetic symbol
  obtain ⟨hτ0, hτ1, hτ2⟩ := tauAt_rows (v := v) hμ hav hℓ ht1
  -- the decay of the pairing coefficient
  obtain ⟨C, hC0, hC⟩ := csi_cAt_abs_le hR hμ hav hv hvrad hv_supp hℓ hRℓ hρ
  -- the slope of the kinetic deficit
  set θ : ℝ := 2 / ((paramsAt μ (_root_.BoseGases.a v)).d
    * (paramsAt μ (_root_.BoseGases.a v)).s * ell v μ) with hθdef
  have hdpos : 0 < (paramsAt μ (_root_.BoseGases.a v)).d := by
    have : (paramsAt μ (_root_.BoseGases.a v)).d
        = fsXp (μ * (_root_.BoseGases.a v) ^ 3) 6 := by
      simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    rw [this]
    exact fsXp_pos (mul_pos hμ (pow_pos hav 3))
  have hspos : 0 < (paramsAt μ (_root_.BoseGases.a v)).s := by
    have : (paramsAt μ (_root_.BoseGases.a v)).s
        = fsXp (μ * (_root_.BoseGases.a v) ^ 3) 1 := by
      simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    rw [this]
    exact fsXp_pos (mul_pos hμ (pow_pos hav 3))
  have hθ0 : 0 ≤ θ := by
    rw [hθdef]; positivity
  have hτ2' : ∀ k : E3, ‖k‖ ^ 2 - tauAt v μ k ≤ θ * ‖k‖ := by
    intro k
    rw [hθdef, div_mul_eq_mul_div]
    exact hτ2 k
  -- the explicit majorant
  obtain ⟨A, B, hA0, hB0, hbound⟩ :=
    csi_bogZeroPoint_majorant (τ := tauAt v μ) (c := cAt v h ρ μ) (θ := θ) (C := C) hθ0 hC0
      hτ0 hτ1 hτ2' hC
  set g : E3 → ℝ := fun k => A * ((‖k‖ ^ 2)⁻¹ * ((1 + ‖k‖) ^ 4)⁻¹)
    + B * ((1 + ‖k‖) ^ 4)⁻¹ with hg
  have hgint : Integrable g := csi_integrable_majorant A B
  have hgsumm : Summable (fun n : Fin 3 → ℤ => g (kAt v μ n)) := by
    have hsum := (csi_summable_first A (ell v μ) hA0 hℓ1).add
      (csi_summable_second B (ell v μ) hB0 hℓ1)
    simpa only [hg, kAt] using hsum
  constructor
  · refine Summable.of_norm_bounded hgsumm (fun n => ?_)
    rw [Real.norm_eq_abs]
    exact hbound (kAt v μ n)
  · refine Integrable.mono' hgint
      ((measurable_cleanFun (v := v) (h := h) (μ := μ) (ρ := ρ)
        (Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ hRℓ)).aestronglyMeasurable)
      (Eventually.of_forall (fun k => hbound k))

end Work.BoseBogFS
