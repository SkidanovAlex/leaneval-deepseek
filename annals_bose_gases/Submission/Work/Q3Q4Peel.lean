import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FSGroupQ2
import Submission.Work.PotQ0Lower
import Submission.Work.Q1Peel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Q3/Q4-CS transcription — first atoms (design note Session-136)

The FS `eq:Q3+Q4CS` leftover `−Σ(P_iQ_jw₁ωP_jP_i+h.c.)` cancels eq:Q1n0's
w₁ω-line exactly.  Convention check (corpus): the corpus `w₁`-kernel is
`wPairC(g₀)` (`g₀ := v(1−ω₀)`, `w₁rel_chosen`: `wPairC(g0) = wPairC(v)(1−ω₀)`),
so the leftover kernel `w₁·ω₀` equals, pointwise,

    wPairC(g₀)(x,y)·ω₀(x−y) = wPairC(g₀·ω₀)(x,y)

(`wScaled` is linear in the numerator; `omC w₀ x y = w₀(x−y)`) — the exact
kernel of `q1_pair_part_sandwich_w0`'s w₁ω-pair-sum.  This module records
that identity and the pointwise square-expansion atom of `q4B`:

    q4B = Q_jQ_iΦ + ω₀·(P_jP_i + P_jQ_i + Q_jP_i)Φ
    (q4B)² = (QQ)² + 2·QQ·ω·S + ω²·S² ,   S := PP+PQ+QP

(the raw first-sector C–S atom; `wPair(v) ≥ 0`, `abs_mul_le_half_sq_sq`-type
C–S to follow in the next sector).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false
set_option maxHeartbeats 600000

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **Leftover-kernel identity (convention check)**: pointwise
`w₁(x,y)·ω₀(x−y) = wPairC(g₀·ω₀)(x,y)` with `w₁ := wPairC(g₀)` — the FS
`eq:Q3+Q4CS` leftover kernel is exactly the w₁ω-kernel of
`Q1Peel.q1_pair_part_sandwich_w0`. -/
lemma w1_mul_omega_eq_w1w {ℓ : ℝ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (x y : ℝ³) :
    wPairC ℓ (g0 v h) x y * (omC (Classical.choose h) x y)
      = wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) x y := by
  unfold wPairC wPair wScaled omC
  ring

/-- **`q4B` expansion, pointwise**: `q4B = QQ + ω·S` where
`QQ := Q_jQ_iΦ` and `S := (P_jP_i + P_jQ_i + Q_jP_i)Φ` (the `q4B`-sum in
`PotWords.q4B`). -/
lemma q4B_expand {N : ℕ} {ℓ : ℝ}
    {om : ℝ³ → ℝ³ → ℝ} {Φ : X N → ℝ} (p : Fin N × Fin N) (x : X N) :
    q4B ℓ om Φ p x
      = aQ ℓ p.2 (aQ ℓ p.1 Φ) x
        + om (x p.1) (x p.2) *
            (aP ℓ p.2 (aP ℓ p.1 Φ) x + aP ℓ p.2 (aQ ℓ p.1 Φ) x + aQ ℓ p.2 (aP ℓ p.1 Φ) x) := by
  rfl

/-- **Square-expansion atom** (pointwise): `(q4B)² = QQ² + 2·QQ·ω·S + (ω·S)²`
with `QQ := Q_jQ_iΦ`, `ω := om(x p.1)(x p.2)`, `S := PP+PQ+QP` — the raw
identity the ω-cross C–S (`2|⟨QQ,ωS⟩| ≤ c⟨QQ²⟩ + c⁻¹⟨ω²S²⟩`) starts from. -/
lemma q4B_sq_expand {N : ℕ} {ℓ : ℝ}
    {om : ℝ³ → ℝ³ → ℝ} {Φ : X N → ℝ} (p : Fin N × Fin N) (x : X N) :
    (q4B ℓ om Φ p x) ^ 2
      = (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2
        + 2 * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
            (om (x p.1) (x p.2) *
              (aP ℓ p.2 (aP ℓ p.1 Φ) x + aP ℓ p.2 (aQ ℓ p.1 Φ) x + aQ ℓ p.2 (aP ℓ p.1 Φ) x))
        + (om (x p.1) (x p.2) *
            (aP ℓ p.2 (aP ℓ p.1 Φ) x + aP ℓ p.2 (aQ ℓ p.1 Φ) x + aQ ℓ p.2 (aP ℓ p.1 Φ) x)) ^ 2 := by
  have hx := q4B_expand (ℓ := ℓ) (om := om) (Φ := Φ) p x
  rw [hx]
  ring

/-- **Per-pair ω-cross C–S (weighted)**: for a weight `w ≥ 0` a.e. over the
box and `f,g` such that the three weighted products are integrable,

`2·|∫ f·g·w| ≤ ∫ f²·w + ∫ g²·w`

(pointwise `2|fg|w ≤ (f²+g²)w`, `|∫h| ≤ ∫|h|`; the raw atom the
`eq:Q3+Q4CS` ω-cross bound is built from, with `f := QQ`, `g := ω·S`,
`w := wPair(v)(x p.1)(x p.2)`). -/
lemma pair_cross_cs {N : ℕ} {ℓ : ℝ}
    {f g w : X N → ℝ}
    (hw : ∀ᵐ x ∂(volume.restrict (abox N ℓ)), 0 ≤ w x)
    (hfg : IntegrableOn (fun x => f x * g x * w x) (abox N ℓ) volume)
    (hf : IntegrableOn (fun x => (f x) ^ 2 * w x) (abox N ℓ) volume)
    (hg : IntegrableOn (fun x => (g x) ^ 2 * w x) (abox N ℓ) volume) :
    2 * |∫ x in abox N ℓ, f x * g x * w x|
      ≤ (∫ x in abox N ℓ, (f x) ^ 2 * w x) + (∫ x in abox N ℓ, (g x) ^ 2 * w x) := by
  have hfg_abs : IntegrableOn (fun x => |f x * g x * w x|) (abox N ℓ) volume := hfg.abs
  have h1 : |∫ x in abox N ℓ, f x * g x * w x|
      ≤ ∫ x in abox N ℓ, |f x * g x * w x| :=
    abs_integral_le_integral_abs (μ := (volume : Measure (X N)).restrict (abox N ℓ))
      (f := fun x => f x * g x * w x)
  have hw_abs : ∀ᵐ x ∂(volume.restrict (abox N ℓ)), |w x| = w x := by
    filter_upwards [hw] with x hx
    exact abs_of_nonneg hx
  have hfun_ae : (fun x => |f x * g x * w x|)
      =ᵐ[volume.restrict (abox N ℓ)] fun x => |f x| * |g x| * w x := by
    filter_upwards [hw_abs] with x hx
    calc
      |f x * g x * w x| = |f x * g x| * |w x| := by rw [abs_mul]
      _ = |f x * g x| * w x := by rw [hx]
      _ = (|f x| * |g x|) * w x := by rw [abs_mul]
  have hcong : (∫ x in abox N ℓ, |f x * g x * w x|)
      = ∫ x in abox N ℓ, |f x| * |g x| * w x := by
    apply integral_congr_ae
    exact hfun_ae
  have h2abs : IntegrableOn (fun x => |f x| * |g x| * w x) (abox N ℓ) volume := by
    change Integrable (fun x => |f x| * |g x| * w x) (volume.restrict (abox N ℓ))
    exact Integrable.congr hfg_abs hfun_ae
  have h2pt : ∀ᵐ x ∂(volume.restrict (abox N ℓ)),
      2 * (|f x| * |g x| * w x) ≤ ((f x) ^ 2 + (g x) ^ 2) * w x := by
    filter_upwards [hw] with x hx
    have hsq : 2 * (|f x| * |g x|) ≤ (f x) ^ 2 + (g x) ^ 2 := by
      have hsg := abs_mul_le_half_sq_sq (f x) (g x)
      nlinarith
    calc
      2 * (|f x| * |g x| * w x) = (2 * (|f x| * |g x|)) * w x := by ring
      _ ≤ ((f x) ^ 2 + (g x) ^ 2) * w x := mul_le_mul_of_nonneg_right hsq hx
  have h2int : IntegrableOn (fun x => 2 * (|f x| * |g x| * w x)) (abox N ℓ) volume := by
    change Integrable (fun x : X N => 2 * (|f x| * |g x| * w x)) (volume.restrict (abox N ℓ))
    have hc := h2abs.const_mul (2 : ℝ)
    simpa [mul_comm, mul_left_comm, mul_assoc] using hc
  have hsum_int : IntegrableOn (fun x => ((f x) ^ 2 + (g x) ^ 2) * w x) (abox N ℓ) volume := by
    have hsum : (fun x => ((f x) ^ 2 + (g x) ^ 2) * w x)
        = fun x => (f x) ^ 2 * w x + (g x) ^ 2 * w x := by
      funext x
      ring
    rw [hsum]
    exact hf.add hg
  have hmono : (∫ x in abox N ℓ, 2 * (|f x| * |g x| * w x))
      ≤ ∫ x in abox N ℓ, ((f x) ^ 2 + (g x) ^ 2) * w x :=
    integral_mono_ae h2int hsum_int h2pt
  calc
    2 * |∫ x in abox N ℓ, f x * g x * w x|
        ≤ 2 * (∫ x in abox N ℓ, |f x * g x * w x|) := by
            exact mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ = 2 * (∫ x in abox N ℓ, |f x| * |g x| * w x) := by rw [hcong]
    _ = ∫ x in abox N ℓ, 2 * (|f x| * |g x| * w x) := by
            rw [integral_const_mul]
    _ ≤ ∫ x in abox N ℓ, ((f x) ^ 2 + (g x) ^ 2) * w x := hmono
    _ = (∫ x in abox N ℓ, (f x) ^ 2 * w x) + (∫ x in abox N ℓ, (g x) ^ 2 * w x) := by
            have hsum : (fun x => ((f x) ^ 2 + (g x) ^ 2) * w x)
                = fun x => (f x) ^ 2 * w x + (g x) ^ 2 * w x := by
              funext x
              ring
            rw [hsum]
            rw [integral_add hf hg]


/-! ## Per-pair ω-cross C–S instantiation (eq:Q3+Q4CS sector)

For an ordered pair `(i, j)`, `i ≠ j`:
`QQ := Q_jQ_iΦ`, `omx := ω₀(x i − x j)`, `SS := (P_jP_i + P_jQ_i + Q_jP_i)Φ`,
`wt := wPair(v)(x i)(x j) ≥ 0`.  The three integrability facts feed
`pair_cross_cs` (f := QQ, g := omx·SS, w := wt), giving the per-pair
ω-cross bound. -/

/-- Integrability of the `QQ·(ω·S)·wPair(v)`-cross over the box (domination
by `|QQ·S|·|wPair(v)|`, `|ω₀| ≤ 1` a.e.). -/
lemma q4_cross_fg_int {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (hv_memL1 : MemLp v 1)
    {i j : Fin N} (hij : i ≠ j) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    IntegrableOn (fun x : X N =>
      (aQ ℓ j (aQ ℓ i Φ) x) *
        ((Classical.choose h (x i - x j)) *
          ((aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x))) *
        (wPair ℓ v (x i) (x j)))
      (abox N ℓ) volume := by
  classical
  let μ : Measure (X N) := volume.restrict (abox N ℓ)
  let QQ : X N → ℝ := fun x => aQ ℓ j (aQ ℓ i Φ) x
  let SS : X N → ℝ := fun x => (aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x)
  let omx : X N → ℝ := fun x => Classical.choose h (x i - x j)
  let wt : X N → ℝ := fun x => wPair ℓ v (x i) (x j)
  have hQQc : Continuous QQ := by
    dsimp [QQ]
    exact aQ_continuous hℓ j (aQ_continuous hℓ i hΦc)
  have hSc : Continuous SS := by
    dsimp [SS]
    have h1 : Continuous (fun x : X N =>
        aP ℓ j (aP ℓ i Φ) x + (aP ℓ j (aQ ℓ i Φ) x + aQ ℓ j (aP ℓ i Φ) x)) :=
      (aP_continuous hℓ j (aP_continuous hℓ i hΦc)).add
        ((aP_continuous hℓ j (aQ_continuous hℓ i hΦc)).add
          (aQ_continuous hℓ j (aP_continuous hℓ i hΦc)))
    simpa [add_assoc] using h1
  have hAbsSc : Continuous (fun x : X N => |QQ x * SS x|) := by
    exact (hQQc.mul hSc).abs
  have hvzero : ∀ z : ℝ³, R ≤ ‖z‖ → v z = 0 := fun z hz => v_zero_of_norm_ge hv_supp hz
  have hdom : IntegrableOn (fun x : X N => |QQ x * SS x| * wt x) (abox N ℓ) volume := by
    have h1 := integrableOn_slot_wPair hℓ (v_integrable hv_memL1) hvzero hRℓ hij
      (S := fun x : X N => |QQ x * SS x|) hAbsSc
    simpa [wt] using h1
  have homx : AEStronglyMeasurable omx μ := by
    dsimp [omx, μ]
    simpa using (w0_diff_aem (N := N) (ℓ := ℓ) hℓ hij (w0 := Classical.choose h) (w0_spec h).2.lhs_integrable)
  have hw : AEStronglyMeasurable wt μ := by
    have hwI : Integrable wt μ := by
      have hs : IntegrableOn (fun x : X N => wPair ℓ v (x i) (x j)) (abox N ℓ) volume := by
        simpa using (integrableOn_slot_wPair hℓ (v_integrable hv_memL1) hvzero hRℓ hij
          (S := fun _ : X N => (1 : ℝ)) (by fun_prop : Continuous (fun _ : X N => (1 : ℝ))))
      simpa [wt, μ, IntegrableOn] using hs
    exact hwI.aestronglyMeasurable
  have hprod_aem : AEStronglyMeasurable (fun x : X N =>
      QQ x * (omx x * SS x) * wt x) μ := by
    exact ((hQQc.aestronglyMeasurable.mul (homx.mul hSc.aestronglyMeasurable))).mul hw
  have homxb : ∀ᵐ x ∂μ, |omx x| ≤ 1 := by
    dsimp [omx, μ]
    simpa using (w0_abs_le_one_box_ae (N := N) hℓ hR hv_nonneg hvrad hv_supp h hij)
  have hbnd : ∀ᵐ x ∂μ, ‖QQ x * (omx x * SS x) * wt x‖ ≤ |QQ x * SS x| * wt x := by
    filter_upwards [homxb] with x hx
    have hwt0 : 0 ≤ wt x := by
      dsimp [wt]
      exact wPairC_nonneg hv_nonneg ℓ (x i) (x j)
    have homle : |omx x| ≤ 1 := hx
    calc
      ‖QQ x * (omx x * SS x) * wt x‖
          = |QQ x| * (|omx x| * |SS x|) * |wt x| := by
              rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
      _ ≤ |QQ x| * (1 * |SS x|) * |wt x| := by
              have hm : |omx x| * |SS x| ≤ 1 * |SS x| :=
                mul_le_mul_of_nonneg_right homle (abs_nonneg (SS x))
              have h1 : |QQ x| * (|omx x| * |SS x|) ≤ |QQ x| * (1 * |SS x|) :=
                mul_le_mul_of_nonneg_left hm (abs_nonneg (QQ x))
              have h2 : (|QQ x| * (|omx x| * |SS x|)) * |wt x|
                  ≤ (|QQ x| * (1 * |SS x|)) * |wt x| :=
                mul_le_mul_of_nonneg_right h1 (abs_nonneg (wt x))
              simpa [mul_assoc] using h2
      _ = |QQ x * SS x| * wt x := by
              rw [abs_mul]
              rw [abs_of_nonneg hwt0]
              ring
  have hgoal : Integrable (fun x : X N => QQ x * (omx x * SS x) * wt x) μ :=
    Integrable.mono' hdom hprod_aem hbnd
  change Integrable (fun x : X N =>
      (aQ ℓ j (aQ ℓ i Φ) x) *
        ((Classical.choose h (x i - x j)) *
          ((aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x))) *
        (wPair ℓ v (x i) (x j))) μ
  simpa [QQ, SS, omx, wt, μ, IntegrableOn] using hgoal

/-- Integrability of `(ω·S)²·wPair(v)` over the box (domination by
`S²·wPair(v)`, `|ω₀| ≤ 1` a.e.). -/
lemma q4_cross_g_int {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (hv_memL1 : MemLp v 1)
    {i j : Fin N} (hij : i ≠ j) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    IntegrableOn (fun x : X N =>
      ((Classical.choose h (x i - x j)) *
          ((aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x))) ^ 2 *
        (wPair ℓ v (x i) (x j)))
      (abox N ℓ) volume := by
  classical
  let μ : Measure (X N) := volume.restrict (abox N ℓ)
  let SS : X N → ℝ := fun x => (aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x)
  let omx : X N → ℝ := fun x => Classical.choose h (x i - x j)
  let wt : X N → ℝ := fun x => wPair ℓ v (x i) (x j)
  have hSc : Continuous SS := by
    dsimp [SS]
    have h1 : Continuous (fun x : X N =>
        aP ℓ j (aP ℓ i Φ) x + (aP ℓ j (aQ ℓ i Φ) x + aQ ℓ j (aP ℓ i Φ) x)) :=
      (aP_continuous hℓ j (aP_continuous hℓ i hΦc)).add
        ((aP_continuous hℓ j (aQ_continuous hℓ i hΦc)).add
          (aQ_continuous hℓ j (aP_continuous hℓ i hΦc)))
    simpa [add_assoc] using h1
  have hS2c : Continuous (fun x : X N => (SS x) ^ 2) := hSc.pow 2
  have hvzero : ∀ z : ℝ³, R ≤ ‖z‖ → v z = 0 := fun z hz => v_zero_of_norm_ge hv_supp hz
  have hdom : IntegrableOn (fun x : X N => (SS x) ^ 2 * wt x) (abox N ℓ) volume := by
    have h1 := integrableOn_slot_wPair hℓ (v_integrable hv_memL1) hvzero hRℓ hij
      (S := fun x : X N => (SS x) ^ 2) hS2c
    simpa [wt] using h1
  have homx : AEStronglyMeasurable omx μ := by
    dsimp [omx, μ]
    simpa using (w0_diff_aem (N := N) (ℓ := ℓ) hℓ hij (w0 := Classical.choose h) (w0_spec h).2.lhs_integrable)
  have hw : AEStronglyMeasurable wt μ := by
    have hwI : Integrable wt μ := by
      have hs : IntegrableOn (fun x : X N => wPair ℓ v (x i) (x j)) (abox N ℓ) volume := by
        simpa using (integrableOn_slot_wPair hℓ (v_integrable hv_memL1) hvzero hRℓ hij
          (S := fun _ : X N => (1 : ℝ)) (by fun_prop : Continuous (fun _ : X N => (1 : ℝ))))
      simpa [wt, μ, IntegrableOn] using hs
    exact hwI.aestronglyMeasurable
  have hprod_aem : AEStronglyMeasurable (fun x : X N => (omx x * SS x) ^ 2 * wt x) μ := by
    have hm : AEStronglyMeasurable (fun x : X N => omx x * SS x) μ := homx.mul hSc.aestronglyMeasurable
    exact (hm.pow 2).mul hw
  have homxb : ∀ᵐ x ∂μ, |omx x| ≤ 1 := by
    dsimp [omx, μ]
    simpa using (w0_abs_le_one_box_ae (N := N) hℓ hR hv_nonneg hvrad hv_supp h hij)
  have hbnd : ∀ᵐ x ∂μ, ‖(omx x * SS x) ^ 2 * wt x‖ ≤ (SS x) ^ 2 * wt x := by
    filter_upwards [homxb] with x hx
    have hw0 : 0 ≤ wt x := by
      dsimp [wt]
      exact wPairC_nonneg hv_nonneg ℓ (x i) (x j)
    have homle : |omx x| ^ 2 ≤ 1 := by nlinarith [hx, abs_nonneg (omx x)]
    have hsqle : (omx x * SS x) ^ 2 ≤ (SS x) ^ 2 := by
      rw [mul_pow]
      have hom2 : (omx x) ^ 2 ≤ 1 := by
        simpa using homle
      have hm := mul_le_mul_of_nonneg_right hom2 (sq_nonneg (SS x))
      simpa using hm
    calc
      ‖(omx x * SS x) ^ 2 * wt x‖ = (omx x * SS x) ^ 2 * wt x := by
        rw [Real.norm_eq_abs]
        rw [abs_of_nonneg (mul_nonneg (sq_nonneg (omx x * SS x)) hw0)]
      _ ≤ (SS x) ^ 2 * wt x := mul_le_mul_of_nonneg_right hsqle hw0
  have hgoal : Integrable (fun x : X N => (omx x * SS x) ^ 2 * wt x) μ :=
    Integrable.mono' hdom hprod_aem hbnd
  change Integrable (fun x : X N =>
      ((Classical.choose h (x i - x j)) *
          ((aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x))) ^ 2 *
        (wPair ℓ v (x i) (x j))) μ
  simpa [SS, omx, wt, μ, IntegrableOn] using hgoal

/-- Integrability of `QQ²·wPair(v)` over the box (direct
`integrableOn_slot_wPair`). -/
lemma q4_cross_f_int {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (_hv_nonneg : 0 ≤ v) (_hvrad : IsRadial v) {R : ℝ} (_hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (_h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (hv_memL1 : MemLp v 1)
    {i j : Fin N} (hij : i ≠ j) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    IntegrableOn (fun x : X N => (aQ ℓ j (aQ ℓ i Φ) x) ^ 2 * wPair ℓ v (x i) (x j))
      (abox N ℓ) volume := by
  have hQQc : Continuous (fun x : X N => (aQ ℓ j (aQ ℓ i Φ) x) ^ 2) :=
    (aQ_continuous hℓ j (aQ_continuous hℓ i hΦc)).pow 2
  have hvzero : ∀ z : ℝ³, R ≤ ‖z‖ → v z = 0 := fun z hz => v_zero_of_norm_ge hv_supp hz
  exact integrableOn_slot_wPair hℓ (v_integrable hv_memL1) hvzero hRℓ hij
    (S := fun x : X N => (aQ ℓ j (aQ ℓ i Φ) x) ^ 2) hQQc

/-- **Per-pair ω-cross C–S (eq:Q3+Q4CS sector, instantiated)**: for the pair
`(i,j)`, `i ≠ j`, with `QQ := Q_jQ_iΦ`, `ω := ω₀(x i − x j)`,
`S := (P_jP_i+P_jQ_i+Q_jP_i)Φ` and the nonneg `wPair(v)`-kernel,

`2·|∫ QQ·(ω·S)·wPair(v)| ≤ ∫ QQ²·wPair(v) + ∫ (ω·S)²·wPair(v)`

(from `pair_cross_cs`; the three integrability facts and `w ≥ 0` supplied). -/
lemma q4_cross_cs_pair {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (hv_memL1 : MemLp v 1)
    {i j : Fin N} (hij : i ≠ j) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    2 * |∫ x in abox N ℓ,
        (aQ ℓ j (aQ ℓ i Φ) x) *
          ((Classical.choose h (x i - x j)) *
            ((aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x))) *
          (wPair ℓ v (x i) (x j))|
      ≤ (∫ x in abox N ℓ, (aQ ℓ j (aQ ℓ i Φ) x) ^ 2 * wPair ℓ v (x i) (x j))
        + (∫ x in abox N ℓ,
            ((Classical.choose h (x i - x j)) *
              ((aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x))) ^ 2 *
            (wPair ℓ v (x i) (x j))) := by
  classical
  let w : X N → ℝ := fun x => wPair ℓ v (x i) (x j)
  have hw0 : ∀ᵐ x ∂(volume.restrict (abox N ℓ)), 0 ≤ w x := by
    refine ae_of_all _ (fun x => ?_)
    dsimp [w]
    exact wPairC_nonneg hv_nonneg ℓ (x i) (x j)
  have hfg := q4_cross_fg_int hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1 hij hΦc
  have hf := q4_cross_f_int hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1 hij hΦc
  have hg := q4_cross_g_int hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1 hij hΦc
  have hcs := pair_cross_cs (N := N) (ℓ := ℓ)
    (f := fun x : X N => aQ ℓ j (aQ ℓ i Φ) x)
    (g := fun x : X N => Classical.choose h (x i - x j) *
        ((aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x)))
    (w := w) hw0 hfg hf hg
  simpa [w, mul_assoc, mul_left_comm, mul_comm] using hcs


/-- **`pairSet`-summed ω-cross C–S** (the regrouping spine): summing
`q4_cross_cs_pair` over the ordered `pairSet`,

`2·Σ_{p∈pairSet} |∫ QQ_p·(ω_p·S_p)·wPair(v)| 
 ≤ Σ_{p∈pairSet} ∫ QQ_p²·wPair(v) + Σ_{p∈pairSet} ∫ (ω_p·S_p)²·wPair(v)`

(`QQ_p := Q_{p.2}Q_{p.1}Φ`, `ω_p := ω₀(x p.1 − x p.2)`,
`S_p := (P_{p.2}P_{p.1}+P_{p.2}Q_{p.1}+Q_{p.2}P_{p.1})Φ`). -/
lemma q4_cross_cs_pairs {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (hv_memL1 : MemLp v 1)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    2 * (∑ p ∈ pairSet N, |∫ x in abox N ℓ,
        (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
          (Classical.choose h (x p.1 - x p.2) *
            ((aP ℓ p.2 (aP ℓ p.1 Φ) x) + (aP ℓ p.2 (aQ ℓ p.1 Φ) x) + (aQ ℓ p.2 (aP ℓ p.1 Φ) x))) *
          (wPair ℓ v (x p.1) (x p.2))|)
      ≤ (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * wPair ℓ v (x p.1) (x p.2))
        + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (Classical.choose h (x p.1 - x p.2) *
              ((aP ℓ p.2 (aP ℓ p.1 Φ) x) + (aP ℓ p.2 (aQ ℓ p.1 Φ) x) + (aQ ℓ p.2 (aP ℓ p.1 Φ) x))) ^ 2 *
            (wPair ℓ v (x p.1) (x p.2))) := by
  classical
  have hper : ∀ p : Fin N × Fin N, p ∈ pairSet N →
      2 * |∫ x in abox N ℓ,
          (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
            (Classical.choose h (x p.1 - x p.2) *
              ((aP ℓ p.2 (aP ℓ p.1 Φ) x) + (aP ℓ p.2 (aQ ℓ p.1 Φ) x) + (aQ ℓ p.2 (aP ℓ p.1 Φ) x))) *
            (wPair ℓ v (x p.1) (x p.2))|
        ≤ (∫ x in abox N ℓ,
            (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * wPair ℓ v (x p.1) (x p.2))
          + (∫ x in abox N ℓ,
              (Classical.choose h (x p.1 - x p.2) *
                ((aP ℓ p.2 (aP ℓ p.1 Φ) x) + (aP ℓ p.2 (aQ ℓ p.1 Φ) x) + (aQ ℓ p.2 (aP ℓ p.1 Φ) x))) ^ 2 *
              (wPair ℓ v (x p.1) (x p.2))) := by
    intro p hp
    have hpij : p.1 ≠ p.2 := by
      simpa [pairSet] using (Finset.mem_filter.mp hp).2
    exact q4_cross_cs_pair hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1
      (i := p.1) (j := p.2) hpij hΦc
  have hsum : (∑ p ∈ pairSet N,
      2 * |∫ x in abox N ℓ,
          (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
            (Classical.choose h (x p.1 - x p.2) *
              ((aP ℓ p.2 (aP ℓ p.1 Φ) x) + (aP ℓ p.2 (aQ ℓ p.1 Φ) x) + (aQ ℓ p.2 (aP ℓ p.1 Φ) x))) *
            (wPair ℓ v (x p.1) (x p.2))|)
      ≤ ∑ p ∈ pairSet N,
          ((∫ x in abox N ℓ,
              (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * wPair ℓ v (x p.1) (x p.2))
            + (∫ x in abox N ℓ,
              (Classical.choose h (x p.1 - x p.2) *
                ((aP ℓ p.2 (aP ℓ p.1 Φ) x) + (aP ℓ p.2 (aQ ℓ p.1 Φ) x) + (aQ ℓ p.2 (aP ℓ p.1 Φ) x))) ^ 2 *
              (wPair ℓ v (x p.1) (x p.2)))) := by
    exact Finset.sum_le_sum (fun p hp => hper p hp)
  calc
    2 * (∑ p ∈ pairSet N, |∫ x in abox N ℓ,
        (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
          (Classical.choose h (x p.1 - x p.2) *
            ((aP ℓ p.2 (aP ℓ p.1 Φ) x) + (aP ℓ p.2 (aQ ℓ p.1 Φ) x) + (aQ ℓ p.2 (aP ℓ p.1 Φ) x))) *
          (wPair ℓ v (x p.1) (x p.2))|)
        = ∑ p ∈ pairSet N,
            2 * |∫ x in abox N ℓ,
              (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
                (Classical.choose h (x p.1 - x p.2) *
                  ((aP ℓ p.2 (aP ℓ p.1 Φ) x) + (aP ℓ p.2 (aQ ℓ p.1 Φ) x) + (aQ ℓ p.2 (aP ℓ p.1 Φ) x))) *
                (wPair ℓ v (x p.1) (x p.2))| := by
            rw [Finset.mul_sum]
    _ ≤ ∑ p ∈ pairSet N,
          ((∫ x in abox N ℓ,
              (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * wPair ℓ v (x p.1) (x p.2))
            + (∫ x in abox N ℓ,
              (Classical.choose h (x p.1 - x p.2) *
                ((aP ℓ p.2 (aP ℓ p.1 Φ) x) + (aP ℓ p.2 (aQ ℓ p.1 Φ) x) + (aQ ℓ p.2 (aP ℓ p.1 Φ) x))) ^ 2 *
              (wPair ℓ v (x p.1) (x p.2)))) := hsum
    _ = (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * wPair ℓ v (x p.1) (x p.2))
        + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (Classical.choose h (x p.1 - x p.2) *
              ((aP ℓ p.2 (aP ℓ p.1 Φ) x) + (aP ℓ p.2 (aQ ℓ p.1 Φ) x) + (aQ ℓ p.2 (aP ℓ p.1 Φ) x))) ^ 2 *
            (wPair ℓ v (x p.1) (x p.2))) := by
            rw [Finset.sum_add_distrib]


/-- **ω-funnel (per pair)**: since `|ω₀| ≤ 1` a.e. over the box and
`wPair(v) ≥ 0`, the ω-cross square collapses to the `ω`-free square,

`∫ (ω_p·S_p)²·wPair(v) ≤ ∫ S_p²·wPair(v)`. -/
lemma q4_cross_omega_funnel {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (hv_memL1 : MemLp v 1)
    {i j : Fin N} (hij : i ≠ j) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∫ x in abox N ℓ,
        ((Classical.choose h (x i - x j)) *
          ((aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x))) ^ 2 *
        (wPair ℓ v (x i) (x j)))
      ≤ (∫ x in abox N ℓ,
          ((aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x)) ^ 2 *
          (wPair ℓ v (x i) (x j))) := by
  classical
  let wt : X N → ℝ := fun x => wPair ℓ v (x i) (x j)
  let SS : X N → ℝ := fun x => (aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x)
  have hwt0 : ∀ᵐ x ∂(volume.restrict (abox N ℓ)), 0 ≤ wt x := by
    refine ae_of_all _ (fun x => ?_)
    dsimp [wt]
    exact wPairC_nonneg hv_nonneg ℓ (x i) (x j)
  have hg := q4_cross_g_int hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1 hij hΦc
  have hSc : Continuous SS := by
    dsimp [SS]
    have h1 : Continuous (fun x : X N =>
        aP ℓ j (aP ℓ i Φ) x + (aP ℓ j (aQ ℓ i Φ) x + aQ ℓ j (aP ℓ i Φ) x)) :=
      (aP_continuous hℓ j (aP_continuous hℓ i hΦc)).add
        ((aP_continuous hℓ j (aQ_continuous hℓ i hΦc)).add
          (aQ_continuous hℓ j (aP_continuous hℓ i hΦc)))
    simpa [add_assoc] using h1
  have hvzero : ∀ z : ℝ³, R ≤ ‖z‖ → v z = 0 := fun z hz => v_zero_of_norm_ge hv_supp hz
  have hs2 : IntegrableOn (fun x : X N => (SS x) ^ 2 * wt x) (abox N ℓ) volume := by
    have h1 := integrableOn_slot_wPair hℓ (v_integrable hv_memL1) hvzero hRℓ hij
      (S := fun x : X N => (SS x) ^ 2) (hSc.pow 2)
    simpa [wt] using h1
  have homxb : ∀ᵐ x ∂(volume.restrict (abox N ℓ)),
      (Classical.choose h (x i - x j)) ^ 2 ≤ 1 := by
    have hw : ∀ᵐ x ∂(volume.restrict (abox N ℓ)), |Classical.choose h (x i - x j)| ≤ 1 := by
      simpa using (w0_abs_le_one_box_ae (N := N) hℓ hR hv_nonneg hvrad hv_supp h hij)
    filter_upwards [hw] with x hx
    have habs : |Classical.choose h (x i - x j)| ^ 2 ≤ 1 := by
      nlinarith [hx, abs_nonneg (Classical.choose h (x i - x j))]
    simpa using habs
  have hmono : ∀ᵐ x ∂(volume.restrict (abox N ℓ)),
      ((Classical.choose h (x i - x j)) * SS x) ^ 2 * wt x ≤ (SS x) ^ 2 * wt x := by
    filter_upwards [homxb, hwt0] with x hx hw0
    have hsqle : ((Classical.choose h (x i - x j)) * SS x) ^ 2 ≤ (SS x) ^ 2 := by
      rw [mul_pow]
      have hw2 : 0 ≤ (SS x) ^ 2 := sq_nonneg _
      have hm := mul_le_mul_of_nonneg_right hx hw2
      simpa using hm
    exact mul_le_mul_of_nonneg_right hsqle hw0
  exact integral_mono_ae hg hs2 hmono

/-- **ω-funnel, `pairSet`-summed**: `Σ∫(ω_p·S_p)²·wPair(v) ≤
Σ∫S_p²·wPair(v)` — collapsing the ω-cross square of `q4_cross_cs_pairs`'s
RHS into the `ω`-free `S_p²`-mass form. -/
lemma q4_cross_omega_funnel_pairs {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (hv_memL1 : MemLp v 1)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        ((Classical.choose h (x p.1 - x p.2)) *
          ((aP ℓ p.2 (aP ℓ p.1 Φ) x) + (aP ℓ p.2 (aQ ℓ p.1 Φ) x) + (aQ ℓ p.2 (aP ℓ p.1 Φ) x))) ^ 2 *
        (wPair ℓ v (x p.1) (x p.2)))
      ≤ (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          ((aP ℓ p.2 (aP ℓ p.1 Φ) x) + (aP ℓ p.2 (aQ ℓ p.1 Φ) x) + (aQ ℓ p.2 (aP ℓ p.1 Φ) x)) ^ 2 *
          (wPair ℓ v (x p.1) (x p.2))) := by
  apply Finset.sum_le_sum
  intro p hp
  have hpij : p.1 ≠ p.2 := by
    simpa [pairSet] using (Finset.mem_filter.mp hp).2
  exact q4_cross_omega_funnel hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1
    (i := p.1) (j := p.2) hpij hΦc


/-- **(a′) v-side mass split (per pair)**: `S_p² = (PP+PQ+QP)²` decomposes
into the three P-family masses against the nonneg `wPair(v)`-kernel,

`∫ S_p²·wPair(v) ≤ 3·(∫(PP)²·|wPair(v)| + ∫(PQ)²·|wPair(v)| + ∫(QP)²·|wPair(v)|)`

(`sq3_mass_pair_le` with `h := v`, generic numerator; `|wPair(v)| = wPair(v)`
since `wPair(v) ≥ 0` pointwise). -/
lemma q4_S2_mass_v_split {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (_hv_nonneg : 0 ≤ v) (_hvrad : IsRadial v) {R : ℝ} (_hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (_h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (hv_memL1 : MemLp v 1)
    {i j : Fin N} (hij : i ≠ j) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∫ x in abox N ℓ,
        ((aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x)) ^ 2 *
        (wPair ℓ v (x i) (x j)))
      ≤ 3 * ((∫ x in abox N ℓ,
            (aP ℓ j (aP ℓ i Φ) x) ^ 2 * |wPair ℓ v (x i) (x j)|)
          + (∫ x in abox N ℓ,
            (aP ℓ j (aQ ℓ i Φ) x) ^ 2 * |wPair ℓ v (x i) (x j)|)
          + (∫ x in abox N ℓ,
            (aQ ℓ j (aP ℓ i Φ) x) ^ 2 * |wPair ℓ v (x i) (x j)|)) := by
  classical
  have hvzero : ∀ z : ℝ³, R ≤ ‖z‖ → v z = 0 := fun z hz => v_zero_of_norm_ge hv_supp hz
  have hsplit := sq3_mass_pair_le hℓ (v_integrable hv_memL1) hvzero hRℓ
    (a := fun x : X N => aP ℓ j (aP ℓ i Φ) x)
    (b := fun x : X N => aP ℓ j (aQ ℓ i Φ) x)
    (c := fun x : X N => aQ ℓ j (aP ℓ i Φ) x)
    (aP_continuous hℓ j (aP_continuous hℓ i hΦc))
    (aP_continuous hℓ j (aQ_continuous hℓ i hΦc))
    (aQ_continuous hℓ j (aP_continuous hℓ i hΦc)) hij
  -- hsplit : ∫(a+b+c)²·|wPair(v)| ≤ 3(∫a²|w|+∫b²|w|+∫c²|w|)
  have hcong : (∫ x in abox N ℓ,
        ((aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x)) ^ 2 *
        (wPair ℓ v (x i) (x j)))
      = (∫ x in abox N ℓ,
        ((aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x)) ^ 2 *
        |wPair ℓ v (x i) (x j)|) := by
    apply integral_congr_ae
    refine ae_of_all _ (fun x => ?_)
    change ((aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x)) ^ 2 *
              wPair ℓ v (x i) (x j)
        = ((aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x)) ^ 2 *
              |wPair ℓ v (x i) (x j)|
    have hw0 : 0 ≤ wPair ℓ v (x i) (x j) := wPairC_nonneg _hv_nonneg ℓ (x i) (x j)
    rw [abs_of_nonneg hw0]
  rw [hcong]
  exact hsplit

/-- **(a′) v-side mass split, `pairSet`-summed**: the ω-free `S_p²`-mass of
the funnel RHS decomposes into the three P-family masses summed over pairs. -/
lemma q4_S2_mass_v_split_pairs {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (hv_memL1 : MemLp v 1)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        ((aP ℓ p.2 (aP ℓ p.1 Φ) x) + (aP ℓ p.2 (aQ ℓ p.1 Φ) x) + (aQ ℓ p.2 (aP ℓ p.1 Φ) x)) ^ 2 *
        (wPair ℓ v (x p.1) (x p.2)))
      ≤ 3 * ((∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)|)
          + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)|)
          + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)|)) := by
  classical
  let A : (Fin N × Fin N) → ℝ := fun p =>
      ∫ x in abox N ℓ, (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)|
  let B : (Fin N × Fin N) → ℝ := fun p =>
      ∫ x in abox N ℓ, (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)|
  let C : (Fin N × Fin N) → ℝ := fun p =>
      ∫ x in abox N ℓ, (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)|
  have hper : ∀ p : Fin N × Fin N, p ∈ pairSet N →
      (∫ x in abox N ℓ,
        ((aP ℓ p.2 (aP ℓ p.1 Φ) x) + (aP ℓ p.2 (aQ ℓ p.1 Φ) x) + (aQ ℓ p.2 (aP ℓ p.1 Φ) x)) ^ 2 *
        (wPair ℓ v (x p.1) (x p.2)))
      ≤ 3 * (A p + B p + C p) := by
    intro p hp
    have hpij : p.1 ≠ p.2 := by
      simpa [pairSet] using (Finset.mem_filter.mp hp).2
    have hsp := q4_S2_mass_v_split hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1
      (i := p.1) (j := p.2) hpij hΦc
    simpa [A, B, C] using hsp
  have hsum1 : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        ((aP ℓ p.2 (aP ℓ p.1 Φ) x) + (aP ℓ p.2 (aQ ℓ p.1 Φ) x) + (aQ ℓ p.2 (aP ℓ p.1 Φ) x)) ^ 2 *
        (wPair ℓ v (x p.1) (x p.2)))
      ≤ ∑ p ∈ pairSet N, 3 * (A p + B p + C p) :=
    Finset.sum_le_sum (fun p hp => hper p hp)
  have hfin : (∑ p ∈ pairSet N, 3 * (A p + B p + C p))
      = 3 * ((∑ p ∈ pairSet N, A p) + (∑ p ∈ pairSet N, B p) + (∑ p ∈ pairSet N, C p)) := by
    rw [← Finset.mul_sum]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  calc
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        ((aP ℓ p.2 (aP ℓ p.1 Φ) x) + (aP ℓ p.2 (aQ ℓ p.1 Φ) x) + (aQ ℓ p.2 (aP ℓ p.1 Φ) x)) ^ 2 *
        (wPair ℓ v (x p.1) (x p.2)))
        ≤ ∑ p ∈ pairSet N, 3 * (A p + B p + C p) := hsum1
    _ = 3 * ((∑ p ∈ pairSet N, A p) + (∑ p ∈ pairSet N, B p) + (∑ p ∈ pairSet N, C p)) := hfin
    _ = 3 * ((∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)|)
          + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)|)
          + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)|)) := by
            simp [A, B, C]


/-- **Generic kernel-abs fibre bound**: `|∫_y |wPair(h)(x,y)|dy| ≤
chiSup²·2·∫|h|` for an integrable `h` with support in `ball 0 R` (dilute) —
the `hfib`-hypothesis of the `masssum_PP/PQ_abs_le`-type mass atoms,
generic in the numerator. -/
lemma kernel_abs_fibre_acube_abs_le {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R)
    (hRℓ : R ≤ ℓ * chiR0) {h : ℝ³ → ℝ} (hi : MeasureTheory.Integrable h)
    (hsupp : ∀ z : ℝ³, R ≤ ‖z‖ → h z = 0) (x : ℝ³) :
    |(∫ y in acube ℓ, |wPair ℓ h x y|)| ≤ chiSup ^ 2 * 2 * (∫ z : ℝ³, |h z|) := by
  have h1 : (∫ y in acube ℓ, |wPair ℓ h x y|)
      = ∫ y in acube ℓ, wPair ℓ (fun z : ℝ³ => |h z|) x y := by
    apply integral_congr_ae
    refine ae_of_all _ (fun y => ?_)
    exact wPair_abs_eq ℓ h x y
  have hAbsI : MeasureTheory.Integrable (fun z : ℝ³ => |h z|) := hi.abs
  have hAbs_supp : ∀ z : ℝ³, R ≤ ‖z‖ → (fun z : ℝ³ => |h z|) z = 0 := by
    intro z hz
    change |h z| = 0
    rw [hsupp z hz, abs_zero]
  calc
    |(∫ y in acube ℓ, |wPair ℓ h x y|)| = |∫ y in acube ℓ, wPair ℓ (fun z : ℝ³ => |h z|) x y| := by
        rw [h1]
    _ ≤ chiSup ^ 2 * 2 * (∫ z : ℝ³, |(fun z : ℝ³ => |h z|) z|) :=
        fibre_acube_abs_le hℓ hR hRℓ (hi := hAbsI) (hsupp := hAbs_supp) x
    _ = chiSup ^ 2 * 2 * (∫ z : ℝ³, |h z|) := by
        congr 1
        apply integral_congr_ae
        refine ae_of_all _ (fun z => ?_)
        exact abs_abs (h z)

/-- **v-kernel abs fibre bound** (the `masssum_*_abs_le`-fibre hypothesis for
`h := v`): `|∫|wPair(v)|-fibre| ≤ chiSup²·2·∫|v|` — with `v ≥ 0`, `∫|v| = ∫v`. -/
lemma v_abs_fibre_acube_abs_le {v : ℝ³ → ℝ} {R ℓ : ℝ} (hℓ : 0 < ℓ)
    (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hv_memL1 : MemLp v 1) (hRℓ : R ≤ ℓ * chiR0) (x : ℝ³) :
    |(∫ y in acube ℓ, |wPair ℓ v x y|)| ≤ chiSup ^ 2 * 2 * (∫ z : ℝ³, |v z|) := by
  have hvzero : ∀ z : ℝ³, R ≤ ‖z‖ → v z = 0 := fun z hz => v_zero_of_norm_ge hv_supp hz
  exact kernel_abs_fibre_acube_abs_le hℓ (le_of_lt hR) hRℓ (v_integrable hv_memL1) hvzero x


/-! ## P-family `v`-mass counts (the masssum instantiations for `h := v`) -/

/-- **(PP)-family count (`h := v`)**: `Σ∫(P_{p.1}P_{p.2}Φ)²·|wPair(v)| ≤
C_v·(ℓ³)⁻¹·Σ∫(P_{p.1}P_{p.2}Φ)²`, `C_v := chiSup²·2·∫|v|` (`masssum_PP_abs_le`
with `hfib := v_abs_fibre_acube_abs_le`). -/
lemma q4_PP_mass_v_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hv_memL1 : MemLp v 1) (hRℓ : R ≤ ℓ * chiR0)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)|)
      ≤ (chiSup ^ 2 * 2 * (∫ z : ℝ³, |v z|)) * (ℓ ^ 3)⁻¹ *
          (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2) := by
  classical
  have hvzero : ∀ z : ℝ³, R ≤ ‖z‖ → v z = 0 := fun z hz => v_zero_of_norm_ge hv_supp hz
  have hfib : ∀ x : ℝ³, |(∫ y in acube ℓ, |wPair ℓ v x y|)| ≤ chiSup ^ 2 * 2 * (∫ z : ℝ³, |v z|) :=
    v_abs_fibre_acube_abs_le hℓ hR hv_supp hv_memL1 hRℓ
  exact masssum_PP_abs_le hℓ hR.le hRℓ (v_integrable hv_memL1) hvzero (radial_neg hvrad)
    (C := chiSup ^ 2 * 2 * (∫ z : ℝ³, |v z|)) hfib hΦc

/-- **(PQ)-family count (`h := v`)** (the `P_{p.1}Q_{p.2}`-family): `Σ∫(P_{p.1}
Q_{p.2}Φ)²·|wPair(v)| ≤ C_v·(ℓ³)⁻¹·Σ∫(P_{p.1}Q_{p.2}Φ)²`. -/
lemma q4_PQ_mass_v_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hv_memL1 : MemLp v 1) (hRℓ : R ≤ ℓ * chiR0)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)|)
      ≤ (chiSup ^ 2 * 2 * (∫ z : ℝ³, |v z|)) * (ℓ ^ 3)⁻¹ *
          (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2) := by
  classical
  have hvzero : ∀ z : ℝ³, R ≤ ‖z‖ → v z = 0 := fun z hz => v_zero_of_norm_ge hv_supp hz
  have hfib : ∀ x : ℝ³, |(∫ y in acube ℓ, |wPair ℓ v x y|)| ≤ chiSup ^ 2 * 2 * (∫ z : ℝ³, |v z|) :=
    v_abs_fibre_acube_abs_le hℓ hR hv_supp hv_memL1 hRℓ
  exact masssum_PQ_abs_le hℓ hR.le hRℓ (v_integrable hv_memL1) hvzero (radial_neg hvrad)
    (C := chiSup ^ 2 * 2 * (∫ z : ℝ³, |v z|)) hfib hΦc

/-- **(PP)-family slot swap**: the `(P_{p.2}P_{p.1}Φ)`-family equals the
`(P_{p.1}P_{p.2}Φ)`-family pointwise (`aP_comm`). -/
lemma q4_PP_family_p2first {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)|)
      = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)| := by
  apply Finset.sum_congr rfl
  intro p hp
  have hpij : p.1 ≠ p.2 := by
    simpa [pairSet] using (Finset.mem_filter.mp hp).2
  apply integral_congr_ae
  refine ae_of_all _ (fun x => ?_)
  have hcomm : aP ℓ p.2 (aP ℓ p.1 Φ) x = aP ℓ p.1 (aP ℓ p.2 Φ) x :=
    (aP_comm hℓ p.1 p.2 hΦc x).symm
  change (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)| =
      (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)|
  rw [hcomm]

/-- **(QP)-family slot swap**: the `(Q_{p.2}P_{p.1}Φ)`-family equals the
`(P_{p.1}Q_{p.2}Φ)`-family pointwise (`aP_aQ_comm`). -/
lemma q4_QP_family_p1PQ {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)|)
      = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)| := by
  apply Finset.sum_congr rfl
  intro p hp
  have hpij : p.1 ≠ p.2 := by
    simpa [pairSet] using (Finset.mem_filter.mp hp).2
  apply integral_congr_ae
  refine ae_of_all _ (fun x => ?_)
  have hcomm : aQ ℓ p.2 (aP ℓ p.1 Φ) x = aP ℓ p.1 (aQ ℓ p.2 Φ) x :=
    (aP_aQ_comm hℓ (i := p.1) (j := p.2) hpij hΦc x).symm
  change (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)| =
      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)|
  rw [hcomm]


/-! ## (a′) v-side mass counts (closing `Σ_p∫S_p²·wPair(v)`) -/

/-- **(PP)-family count in `cS2`-form (`h := v`, slot-swapped family)**: the
`(P_{p.2}P_{p.1}Φ)`-family mass appearing in `q4B`'s `S_p` is bounded by
`C_v·(ℓ³)⁻¹·cS2` (`q4_PP_family_p2first` slot swap + `q4_PP_mass_v_le`). -/
lemma q4_PPsw_mass_v_cS2 {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hv_memL1 : MemLp v 1) (hRℓ : R ≤ ℓ * chiR0)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)|)
      ≤ (chiSup ^ 2 * 2 * (∫ z : ℝ³, |v z|)) * (ℓ ^ 3)⁻¹ * cS2 ℓ Φ := by
  classical
  have hswap := q4_PP_family_p2first (ℓ := ℓ) (hℓ := hℓ) (v := v) (Φ := Φ) hΦc
  have hPP := q4_PP_mass_v_le hℓ hvrad hR hv_supp hv_memL1 hRℓ hΦc
  have hC : (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2)
      = cS2 ℓ Φ := by
    rfl
  calc
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)|)
        = (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)|) := hswap
    _ ≤ (chiSup ^ 2 * 2 * (∫ z : ℝ³, |v z|)) * (ℓ ^ 3)⁻¹ *
          (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2) := hPP
    _ = (chiSup ^ 2 * 2 * (∫ z : ℝ³, |v z|)) * (ℓ ^ 3)⁻¹ * cS2 ℓ Φ := by
          rw [hC]

/-- **(PQ)-family count (`h := v`, slot-swapped family)**: the
`(P_{p.2}Q_{p.1}Φ)`-family mass appearing in `q4B`'s `S_p` is bounded by
`C_v·(ℓ³)⁻¹·N̂·n₊` (`masssum_Qsw_abs_le` + `pairSum_Q_swap_le`). -/
lemma q4_PQsw_mass_v_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hv_memL1 : MemLp v 1) (hRℓ : R ≤ ℓ * chiR0)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)|)
      ≤ (chiSup ^ 2 * 2 * (∫ z : ℝ³, |v z|)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
  classical
  have hvzero : ∀ z : ℝ³, R ≤ ‖z‖ → v z = 0 := fun z hz => v_zero_of_norm_ge hv_supp hz
  have hfib : ∀ x : ℝ³, |(∫ y in acube ℓ, |wPair ℓ v x y|)| ≤ chiSup ^ 2 * 2 * (∫ z : ℝ³, |v z|) :=
    v_abs_fibre_acube_abs_le hℓ hR hv_supp hv_memL1 hRℓ
  have hmm : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)|)
      ≤ (chiSup ^ 2 * 2 * (∫ z : ℝ³, |v z|)) * (ℓ ^ 3)⁻¹ *
          (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2) :=
    masssum_Qsw_abs_le hℓ hR.le hRℓ (v_integrable hv_memL1) hvzero (radial_neg hvrad)
      (C := chiSup ^ 2 * 2 * (∫ z : ℝ³, |v z|)) hfib hΦc
  have hCv : 0 ≤ chiSup ^ 2 * 2 * (∫ z : ℝ³, |v z|) := by
    exact mul_nonneg (mul_nonneg (sq_nonneg chiSup) (by norm_num))
      (integral_nonneg (fun z : ℝ³ => abs_nonneg (v z)))
  have hLinv : 0 ≤ (ℓ ^ 3)⁻¹ := by positivity
  have hcount := pairSum_Q_swap_le hℓ hΦc
  calc
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)|)
        ≤ (chiSup ^ 2 * 2 * (∫ z : ℝ³, |v z|)) * (ℓ ^ 3)⁻¹ *
            (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2) := hmm
    _ ≤ (chiSup ^ 2 * 2 * (∫ z : ℝ³, |v z|)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ) := by
          exact mul_le_mul_of_nonneg_left hcount (mul_nonneg hCv hLinv)
    _ = (chiSup ^ 2 * 2 * (∫ z : ℝ³, |v z|)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
          ring

/-- **(QP)-family count (`h := v`)**: the `(Q_{p.2}P_{p.1}Φ)`-family mass in
`q4B`'s `S_p` is bounded by `C_v·(ℓ³)⁻¹·N̂·n₊` (`q4_QP_family_p1PQ` slot swap
to the `(P_{p.1}Q_{p.2}Φ)`-family + `q4_PQ_mass_v_le` + `pairSum_B_le`). -/
lemma q4_QP_mass_v_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hv_memL1 : MemLp v 1) (hRℓ : R ≤ ℓ * chiR0)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)|)
      ≤ (chiSup ^ 2 * 2 * (∫ z : ℝ³, |v z|)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
  classical
  have hswap := q4_QP_family_p1PQ (ℓ := ℓ) (hℓ := hℓ) (v := v) (Φ := Φ) hΦc
  have hPQ := q4_PQ_mass_v_le hℓ hvrad hR hv_supp hv_memL1 hRℓ hΦc
  have hCv : 0 ≤ chiSup ^ 2 * 2 * (∫ z : ℝ³, |v z|) := by
    exact mul_nonneg (mul_nonneg (sq_nonneg chiSup) (by norm_num))
      (integral_nonneg (fun z : ℝ³ => abs_nonneg (v z)))
  have hLinv : 0 ≤ (ℓ ^ 3)⁻¹ := by positivity
  have hcount := pairSum_B_le hℓ hΦc
  calc
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)|)
        = (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)|) := hswap
    _ ≤ (chiSup ^ 2 * 2 * (∫ z : ℝ³, |v z|)) * (ℓ ^ 3)⁻¹ *
          (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2) := hPQ
    _ ≤ (chiSup ^ 2 * 2 * (∫ z : ℝ³, |v z|)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ) := by
          exact mul_le_mul_of_nonneg_left hcount (mul_nonneg hCv hLinv)
    _ = (chiSup ^ 2 * 2 * (∫ z : ℝ³, |v z|)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
          ring


/-- **(a′) headline — v-side `S_p²`-mass control**: `Σ_p∫S_p²·wPair(v)` is
bounded by `3·C_v·(ℓ³)⁻¹·(cS2 + 2·N̂·n₊)`, `C_v := chiSup²·2·∫|v|` — the
`pairSet`-sum of `q4_S2_mass_v_split_pairs` + the three P-family
`v`-mass counts (`q4_PPsw_mass_v_cS2`, `q4_PQsw_mass_v_le`,
`q4_QP_mass_v_le`).  This is the ω-funnel RHS control of
`q4_cross_omega_funnel_pairs` (`(a′)` of the eq:Q3+Q4CS transcription). -/
lemma q4_S2_mass_v_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (hv_memL1 : MemLp v 1)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        ((aP ℓ p.2 (aP ℓ p.1 Φ) x) + (aP ℓ p.2 (aQ ℓ p.1 Φ) x) + (aQ ℓ p.2 (aP ℓ p.1 Φ) x)) ^ 2 *
        (wPair ℓ v (x p.1) (x p.2)))
      ≤ 3 * (chiSup ^ 2 * 2 * (∫ z : ℝ³, |v z|)) * (ℓ ^ 3)⁻¹ *
          (cS2 ℓ Φ + (N : ℝ) * cnPlus ℓ Φ + (N : ℝ) * cnPlus ℓ Φ) := by
  classical
  let A : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)|
  let B : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)|
  let C : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPair ℓ v (x p.1) (x p.2)|
  let Cv : ℝ := chiSup ^ 2 * 2 * (∫ z : ℝ³, |v z|)
  let P : ℝ := Cv * (ℓ ^ 3)⁻¹ * cS2 ℓ Φ
  let Q : ℝ := Cv * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
  have hsplit : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        ((aP ℓ p.2 (aP ℓ p.1 Φ) x) + (aP ℓ p.2 (aQ ℓ p.1 Φ) x) + (aQ ℓ p.2 (aP ℓ p.1 Φ) x)) ^ 2 *
        (wPair ℓ v (x p.1) (x p.2)))
      ≤ 3 * (A + B + C) := by
    have hsp := q4_S2_mass_v_split_pairs hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1 hΦc
    simpa [A, B, C] using hsp
  have hA : A ≤ P := by
    have h1 := q4_PPsw_mass_v_cS2 hℓ hvrad hR hv_supp hv_memL1 hRℓ hΦc
    simpa [A, P, Cv] using h1
  have hB : B ≤ Q := by
    have h1 := q4_PQsw_mass_v_le hℓ hvrad hR hv_supp hv_memL1 hRℓ hΦc
    simpa [B, Q, Cv, mul_assoc] using h1
  have hCq : C ≤ Q := by
    have h1 := q4_QP_mass_v_le hℓ hvrad hR hv_supp hv_memL1 hRℓ hΦc
    simpa [C, Q, Cv, mul_assoc] using h1
  have hsum : 3 * (A + B + C) ≤ 3 * (P + Q + Q) := by
    have hAB : A + (B + C) ≤ P + (Q + Q) := add_le_add hA (add_le_add hB hCq)
    have hABC : (A + B) + C ≤ (P + Q) + Q := by simpa [add_assoc] using hAB
    exact mul_le_mul_of_nonneg_left hABC (by norm_num)
  calc
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        ((aP ℓ p.2 (aP ℓ p.1 Φ) x) + (aP ℓ p.2 (aQ ℓ p.1 Φ) x) + (aQ ℓ p.2 (aP ℓ p.1 Φ) x)) ^ 2 *
        (wPair ℓ v (x p.1) (x p.2)))
        ≤ 3 * (A + B + C) := hsplit
    _ ≤ 3 * (P + Q + Q) := hsum
    _ = 3 * (chiSup ^ 2 * 2 * (∫ z : ℝ³, |v z|)) * (ℓ ^ 3)⁻¹ *
          (cS2 ℓ Φ + (N : ℝ) * cnPlus ℓ Φ + (N : ℝ) * cnPlus ℓ Φ) := by
          dsimp [P, Q, Cv]
          ring

/-- **Exact q4word square-split identity**: with the chosen kernels
(`w := wPairC(v)`, `om := omC w₀`), `q4B = QQ + ω·S` pointwise gives the
exact word identity

`q4word = ½·Σ_p∫QQ_p²·wPair(v) + Σ_p∫QQ_p·(ω_p·S_p)·wPair(v) + ½·Σ_p∫(ω_p·S_p)²·wPair(v)`

(`QQ_p := Q_{p.2}Q_{p.1}Φ`, `ω_p := w₀(x p.1 − x p.2)`, `S_p :=
(P_{p.2}P_{p.1}+P_{p.2}Q_{p.1}+Q_{p.2}P_{p.1})Φ`) — the ω-cross extraction
atom of the eq:Q3+Q4CS transcription: the signed `QQ·(ωS)`-cross of the
square appears explicitly (any (c′) assembly starts from this identity, with
the `(ω_p·S_p)²`-part mass-funnelled by `q4_cross_omega_funnel_pairs` and the
`S_p²`-mass counted by `q4_S2_mass_v_le`). -/
lemma q4word_sq_split {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (hv_memL1 : MemLp v 1)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ
    = (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * (wPair ℓ v (x p.1) (x p.2)))
      + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
          ((Classical.choose h (x p.1 - x p.2)) *
            ((aP ℓ p.2 (aP ℓ p.1 Φ) x) + (aP ℓ p.2 (aQ ℓ p.1 Φ) x) + (aQ ℓ p.2 (aP ℓ p.1 Φ) x))) *
          (wPair ℓ v (x p.1) (x p.2)))
      + (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          ((Classical.choose h (x p.1 - x p.2)) *
            ((aP ℓ p.2 (aP ℓ p.1 Φ) x) + (aP ℓ p.2 (aQ ℓ p.1 Φ) x) + (aQ ℓ p.2 (aP ℓ p.1 Φ) x))) ^ 2 *
          (wPair ℓ v (x p.1) (x p.2))) := by
  classical
  let A : (Fin N × Fin N) → ℝ := fun p =>
      ∫ x in abox N ℓ, (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * (wPair ℓ v (x p.1) (x p.2))
  let B : (Fin N × Fin N) → ℝ := fun p =>
      ∫ x in abox N ℓ, (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
          ((Classical.choose h (x p.1 - x p.2)) *
            ((aP ℓ p.2 (aP ℓ p.1 Φ) x) + (aP ℓ p.2 (aQ ℓ p.1 Φ) x) + (aQ ℓ p.2 (aP ℓ p.1 Φ) x))) *
          (wPair ℓ v (x p.1) (x p.2))
  let C : (Fin N × Fin N) → ℝ := fun p =>
      ∫ x in abox N ℓ, ((Classical.choose h (x p.1 - x p.2)) *
          ((aP ℓ p.2 (aP ℓ p.1 Φ) x) + (aP ℓ p.2 (aQ ℓ p.1 Φ) x) + (aQ ℓ p.2 (aP ℓ p.1 Φ) x))) ^ 2 *
          (wPair ℓ v (x p.1) (x p.2))
  have hper : ∀ p : Fin N × Fin N, p ∈ pairSet N →
      (∫ x in abox N ℓ, (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 *
          (wPair ℓ v (x p.1) (x p.2)))
      = (A p + 2 * B p) + C p := by
    intro p hp
    have hpij : p.1 ≠ p.2 := by
      simpa [pairSet] using (Finset.mem_filter.mp hp).2
    let QQ : X N → ℝ := fun x => aQ ℓ p.2 (aQ ℓ p.1 Φ) x
    let SS : X N → ℝ := fun x => (aP ℓ p.2 (aP ℓ p.1 Φ) x) + (aP ℓ p.2 (aQ ℓ p.1 Φ) x) + (aQ ℓ p.2 (aP ℓ p.1 Φ) x)
    let omx : X N → ℝ := fun x => Classical.choose h (x p.1 - x p.2)
    let wt : X N → ℝ := fun x => wPair ℓ v (x p.1) (x p.2)
    let M : X N → ℝ := fun x => QQ x * (omx x * SS x) * wt x
    have h1 : IntegrableOn (fun x : X N => (QQ x) ^ 2 * wt x) (abox N ℓ) volume := by
      have hi := q4_cross_f_int hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1
        (i := p.1) (j := p.2) hpij hΦc
      simpa [QQ, wt] using hi
    have hM : IntegrableOn M (abox N ℓ) volume := by
      have hi := q4_cross_fg_int hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1
        (i := p.1) (j := p.2) hpij hΦc
      simpa [QQ, SS, omx, wt, M] using hi
    have h2 : IntegrableOn (fun x : X N => 2 * M x) (abox N ℓ) volume := by
      change Integrable (fun x : X N => 2 * M x) (volume.restrict (abox N ℓ))
      exact hM.const_mul 2
    have h3 : IntegrableOn (fun x : X N => ((omx x * SS x) ^ 2) * wt x) (abox N ℓ) volume := by
      have hi := q4_cross_g_int hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1
        (i := p.1) (j := p.2) hpij hΦc
      simpa [SS, omx, wt] using hi
    have hBC : IntegrableOn (fun x : X N => 2 * M x + ((omx x * SS x) ^ 2) * wt x)
        (abox N ℓ) volume := by
      have h2I : Integrable (fun x : X N => 2 * M x) (volume.restrict (abox N ℓ)) := by
        simpa [IntegrableOn] using h2
      have h3I : Integrable (fun x : X N => ((omx x * SS x) ^ 2) * wt x)
          (volume.restrict (abox N ℓ)) := by
        simpa [IntegrableOn] using h3
      exact h2I.add h3I
    have hfun_pt : ∀ x : X N,
        (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wt x
          = (QQ x) ^ 2 * wt x + (2 * M x + ((omx x * SS x) ^ 2) * wt x) := by
      intro x
      have hsq := q4B_sq_expand (ℓ := ℓ) (om := omC (Classical.choose h)) (Φ := Φ) p x
      rw [hsq]
      dsimp [QQ, SS, omx, wt, M, omC]
      ring
    have hfun_ae : (fun x : X N => (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wt x)
        =ᵐ[volume.restrict (abox N ℓ)] fun x : X N =>
            (QQ x) ^ 2 * wt x + (2 * M x + ((omx x * SS x) ^ 2) * wt x) := by
      refine ae_of_all _ (fun x => ?_)
      exact hfun_pt x
    have hsplit1 : (∫ x in abox N ℓ, (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wt x)
        = (∫ x in abox N ℓ, (QQ x) ^ 2 * wt x)
          + (∫ x in abox N ℓ, 2 * M x + ((omx x * SS x) ^ 2) * wt x) := by
      calc
        (∫ x in abox N ℓ, (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wt x)
            = (∫ x in abox N ℓ,
                (QQ x) ^ 2 * wt x + (2 * M x + ((omx x * SS x) ^ 2) * wt x)) := by
                apply integral_congr_ae
                exact hfun_ae
        _ = (∫ x in abox N ℓ, (QQ x) ^ 2 * wt x)
            + (∫ x in abox N ℓ, 2 * M x + ((omx x * SS x) ^ 2) * wt x) := by
            rw [integral_add (by simpa [IntegrableOn] using h1) (by simpa [IntegrableOn] using hBC)]
    have hMid2 : (∫ x in abox N ℓ, 2 * M x + ((omx x * SS x) ^ 2) * wt x)
        = (∫ x in abox N ℓ, 2 * M x) + (∫ x in abox N ℓ, ((omx x * SS x) ^ 2) * wt x) := by
      rw [integral_add (by simpa [IntegrableOn] using h2) (by simpa [IntegrableOn] using h3)]
    have hMid : (∫ x in abox N ℓ, 2 * M x)
        = 2 * (∫ x in abox N ℓ, M x) := by
      rw [integral_const_mul]
    calc
      (∫ x in abox N ℓ, (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wt x)
          = (∫ x in abox N ℓ, (QQ x) ^ 2 * wt x)
            + (∫ x in abox N ℓ, 2 * M x + ((omx x * SS x) ^ 2) * wt x) := hsplit1
      _ = ((∫ x in abox N ℓ, (QQ x) ^ 2 * wt x)
            + (∫ x in abox N ℓ, 2 * M x))
          + (∫ x in abox N ℓ, ((omx x * SS x) ^ 2) * wt x) := by
          rw [hMid2]
          ring
      _ = ((∫ x in abox N ℓ, (QQ x) ^ 2 * wt x)
            + 2 * (∫ x in abox N ℓ, M x))
          + (∫ x in abox N ℓ, ((omx x * SS x) ^ 2) * wt x) := by
          rw [hMid]
      _ = (A p + 2 * B p) + C p := by
          simp [A, B, C, QQ, SS, omx, wt, M]
  -- sum over pairs
  have hsumcongr : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * (wPair ℓ v (x p.1) (x p.2)))
      = ∑ p ∈ pairSet N, ((A p + 2 * B p) + C p) := by
    apply Finset.sum_congr rfl
    intro p hp
    exact hper p hp
  have hlin : (∑ p ∈ pairSet N, ((A p + 2 * B p) + C p))
      = ((∑ p ∈ pairSet N, A p) + 2 * (∑ p ∈ pairSet N, B p)) + (∑ p ∈ pairSet N, C p) := by
    calc
      (∑ p ∈ pairSet N, ((A p + 2 * B p) + C p))
          = (∑ p ∈ pairSet N, (A p + 2 * B p)) + (∑ p ∈ pairSet N, C p) := by
            rw [Finset.sum_add_distrib]
      _ = ((∑ p ∈ pairSet N, A p) + (∑ p ∈ pairSet N, 2 * B p)) + (∑ p ∈ pairSet N, C p) := by
            congr 1
            rw [Finset.sum_add_distrib]
      _ = ((∑ p ∈ pairSet N, A p) + 2 * (∑ p ∈ pairSet N, B p)) + (∑ p ∈ pairSet N, C p) := by
            congr 1
            rw [← Finset.mul_sum]
  -- reassemble with the ½
  calc
    q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ
        = (1 / 2 : ℝ) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * (wPair ℓ v (x p.1) (x p.2))) := by
            rfl
    _ = (1 / 2 : ℝ) * (∑ p ∈ pairSet N, ((A p + 2 * B p) + C p)) := by
            rw [hsumcongr]
    _ = (1 / 2 : ℝ) * (((∑ p ∈ pairSet N, A p) + 2 * (∑ p ∈ pairSet N, B p)) + (∑ p ∈ pairSet N, C p)) := by
            rw [hlin]
    _ = ((1 / 2 : ℝ) * (∑ p ∈ pairSet N, A p) + (∑ p ∈ pairSet N, B p))
        + (1 / 2 : ℝ) * (∑ p ∈ pairSet N, C p) := by
            ring
    _ = (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * (wPair ℓ v (x p.1) (x p.2)))
        + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
              ((Classical.choose h (x p.1 - x p.2)) *
                ((aP ℓ p.2 (aP ℓ p.1 Φ) x) + (aP ℓ p.2 (aQ ℓ p.1 Φ) x) + (aQ ℓ p.2 (aP ℓ p.1 Φ) x))) *
              (wPair ℓ v (x p.1) (x p.2)))
        + (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            ((Classical.choose h (x p.1 - x p.2)) *
              ((aP ℓ p.2 (aP ℓ p.1 Φ) x) + (aP ℓ p.2 (aQ ℓ p.1 Φ) x) + (aQ ℓ p.2 (aP ℓ p.1 Φ) x))) ^ 2 *
            (wPair ℓ v (x p.1) (x p.2))) := by
          simp [A, B, C]

/-- **Signed ω-cross extraction (q4 lower bound)**: from the exact
`q4word_sq_split`, dropping the nonnegative `(ω_p·S_p)²`-part (`wPair(v) ≥ 0`),
q4word dominates the QQ²-mass plus the SIGNED ω-cross:

`½·Σ_p∫QQ_p²·wPair(v) + Σ_p∫QQ_p·(ω_p·S_p)·wPair(v) ≤ q4word`.

This is the per-word lower-bound form in which the q1-w₁ω-cancellation
partner (`q1_pair_part_sandwich_w0`) enters the joint q1+q3+q4 assembly. -/
lemma q4word_ge_signed {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (hv_memL1 : MemLp v 1)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * (wPair ℓ v (x p.1) (x p.2)))
      + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
          ((Classical.choose h (x p.1 - x p.2)) *
            ((aP ℓ p.2 (aP ℓ p.1 Φ) x) + (aP ℓ p.2 (aQ ℓ p.1 Φ) x) + (aQ ℓ p.2 (aP ℓ p.1 Φ) x))) *
          (wPair ℓ v (x p.1) (x p.2)))
    ≤ q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
  classical
  have hsplit := q4word_sq_split hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1 hΦc
  have hωpos : 0 ≤ (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        ((Classical.choose h (x p.1 - x p.2)) *
          ((aP ℓ p.2 (aP ℓ p.1 Φ) x) + (aP ℓ p.2 (aQ ℓ p.1 Φ) x) + (aQ ℓ p.2 (aP ℓ p.1 Φ) x))) ^ 2 *
        (wPair ℓ v (x p.1) (x p.2))) := by
    have hsum : 0 ≤ ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        ((Classical.choose h (x p.1 - x p.2)) *
          ((aP ℓ p.2 (aP ℓ p.1 Φ) x) + (aP ℓ p.2 (aQ ℓ p.1 Φ) x) + (aQ ℓ p.2 (aP ℓ p.1 Φ) x))) ^ 2 *
        (wPair ℓ v (x p.1) (x p.2)) := by
      apply Finset.sum_nonneg
      intro p hp
      apply integral_nonneg
      intro x
      exact mul_nonneg (sq_nonneg (Classical.choose h (x p.1 - x p.2) *
          ((aP ℓ p.2 (aP ℓ p.1 Φ) x) + (aP ℓ p.2 (aQ ℓ p.1 Φ) x) + (aQ ℓ p.2 (aP ℓ p.1 Φ) x))))
        (wPairC_nonneg hv_nonneg ℓ (x p.1) (x p.2))
    nlinarith
  rw [hsplit]
  nlinarith


/-! ## (A)/(B) atoms of the eq:Q3+Q4CS transcription (Session-145)

* (A) `q4_pair_sq_split` / `q4_pair_ge_signed` — the per-pair square split of
  the q4 integrand (`∫(q4B)²w = ∫QQ²w + 2∫QQ·(ωS)w + ∫(ωS)²w`) and the
  per-pair signed bound `½∫QQ²w + ∫QQ·(ωS)w ≤ ½∫(q4B)²w` (dropping the
  nonnegative `(ωS)²`-part; the per-pair version of `q4word_sq_split` /
  `q4word_ge_signed`, exposed for the joint q1+q3+q4 assembly).
* (B) the QQ²-kernel split: pointwise `wPair(v) = wPair(g₀) + wPair(v·ω₀)`
  (`v_eq_g0_add_vw0`, `wPair_v_split_g0_vw0`, `vw0_integrable` the
  `v·ω₀`-L¹/support facts) giving the per-pair and `pairSet`-summed QQ²-mass
  identities `Σ∫QQ²·wPair(v) = Σ∫QQ²·wPair(g₀) + Σ∫QQ²·wPair(v·ω₀)`
  (`qq2_wv_eq_w1_add_vw0_pair` / `_pairs`) and the domination
  `Σ∫QQ²·|w₁| ≤ Σ∫QQ²·wPair(v)` (`qq2_w1_le_w_pair` / `_pairs`) — the exact
  accounting by which q3's QQ²-`|w₁|`-masses relate to the q4-side
  `QQ²·wPair(v)`-sum of `q4word_sq_split`.
-/
/-- Pointwise `v = g₀ + v·ω₀` (`ω₀ := Classical.choose h`). -/
lemma v_eq_g0_add_vw0 {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (x : ℝ³) :
    v x = g0 v h x + v x * Classical.choose h x := by
  unfold g0
  ring

/-- **Kernel split (pointwise)**: `wPair(v) = wPair(g₀) + wPair(v·ω₀)` —
the numerator split `v = g₀ + v·ω₀` through `wPair`-linearity. -/
lemma wPair_v_split_g0_vw0 {ℓ : ℝ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (x y : ℝ³) :
    wPair ℓ v x y = wPair ℓ (g0 v h) x y
      + wPair ℓ (fun z : ℝ³ => v z * Classical.choose h z) x y := by
  have hfun : v = g0 v h + (fun z : ℝ³ => v z * Classical.choose h z) := by
    funext z
    exact v_eq_g0_add_vw0 h z
  have hcong : wPair ℓ v x y = wPair ℓ (g0 v h + (fun z : ℝ³ => v z * Classical.choose h z)) x y := by
    exact congrArg (fun u : ℝ³ → ℝ => wPair ℓ u x y) hfun
  rw [hcong, wPair_add]

/-- `v·ω₀` is integrable (it equals `v − g₀` pointwise). -/
lemma vw0_integrable {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (_hv_nonneg : 0 ≤ v) (_hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hv_memL1 : MemLp v 1) :
    MeasureTheory.Integrable (fun z : ℝ³ => v z * Classical.choose h z) := by
  have hg0i : MeasureTheory.Integrable (g0 v h) := g0_integrable hR hv_supp h
  have hvi : MeasureTheory.Integrable v := v_integrable hv_memL1
  have hsub : MeasureTheory.Integrable (fun z : ℝ³ => v z - g0 v h z) := hvi.sub hg0i
  have heq : (fun z : ℝ³ => v z - g0 v h z) =ᵐ[volume] fun z : ℝ³ => v z * Classical.choose h z := by
    refine ae_of_all _ (fun z => ?_)
    unfold g0
    ring
  exact hsub.congr heq

/-- Per-pair square split, see below. -/
lemma q4_pair_sq_split {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (hv_memL1 : MemLp v 1)
    {i j : Fin N} (hij : i ≠ j) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∫ x in abox N ℓ, (q4B ℓ (omC (Classical.choose h)) Φ (i, j) x) ^ 2 *
        wPair ℓ v (x i) (x j))
      = (∫ x in abox N ℓ, (aQ ℓ j (aQ ℓ i Φ) x) ^ 2 * wPair ℓ v (x i) (x j))
        + 2 * (∫ x in abox N ℓ,
            (aQ ℓ j (aQ ℓ i Φ) x) *
              ((Classical.choose h (x i - x j)) *
                ((aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x))) *
              (wPair ℓ v (x i) (x j)))
        + (∫ x in abox N ℓ,
            ((Classical.choose h (x i - x j)) *
              ((aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x))) ^ 2 *
            (wPair ℓ v (x i) (x j))) := by
  classical
  let A : ℝ := ∫ x in abox N ℓ, (aQ ℓ j (aQ ℓ i Φ) x) ^ 2 * (wPair ℓ v (x i) (x j))
  let B : ℝ := ∫ x in abox N ℓ,
      (aQ ℓ j (aQ ℓ i Φ) x) *
        ((Classical.choose h (x i - x j)) *
          ((aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x))) *
        (wPair ℓ v (x i) (x j))
  let C : ℝ := ∫ x in abox N ℓ,
      ((Classical.choose h (x i - x j)) *
        ((aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x))) ^ 2 *
        (wPair ℓ v (x i) (x j))
  have hper : (∫ x in abox N ℓ, (q4B ℓ (omC (Classical.choose h)) Φ (i, j) x) ^ 2 *
      wPair ℓ v (x i) (x j))
      = (A + 2 * B) + C := by
    let QQ : X N → ℝ := fun x => aQ ℓ j (aQ ℓ i Φ) x
    let SS : X N → ℝ := fun x => (aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x)
    let omx : X N → ℝ := fun x => Classical.choose h (x i - x j)
    let wt : X N → ℝ := fun x => wPair ℓ v (x i) (x j)
    let M : X N → ℝ := fun x => QQ x * (omx x * SS x) * wt x
    let BB : X N → ℝ := fun x => q4B ℓ (omC (Classical.choose h)) Φ (i, j) x
    have h1 : IntegrableOn (fun x : X N => (QQ x) ^ 2 * wt x) (abox N ℓ) volume := by
      have hi := q4_cross_f_int hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1
        (i := i) (j := j) hij hΦc
      simpa [QQ, wt] using hi
    have hM : IntegrableOn M (abox N ℓ) volume := by
      have hi := q4_cross_fg_int hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1
        (i := i) (j := j) hij hΦc
      simpa [QQ, SS, omx, wt, M] using hi
    have h3 : IntegrableOn (fun x : X N => ((omx x * SS x) ^ 2) * wt x) (abox N ℓ) volume := by
      have hi := q4_cross_g_int hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1
        (i := i) (j := j) hij hΦc
      simpa [SS, omx, wt] using hi
    have hB : IntegrableOn (fun x : X N => (BB x) ^ 2 * wt x) (abox N ℓ) volume := by
      have hi := q4B_sq_w_integrable hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1 hij hΦc
      simpa [BB, wt] using hi
    have hM2 : IntegrableOn (fun x : X N => 2 * M x) (abox N ℓ) volume := by
      change Integrable (fun x : X N => 2 * M x) (volume.restrict (abox N ℓ))
      exact hM.const_mul 2
    have h23 : IntegrableOn (fun x : X N => 2 * M x + ((omx x * SS x) ^ 2) * wt x)
        (abox N ℓ) volume := by
      have h2I : Integrable (fun x : X N => 2 * M x) (volume.restrict (abox N ℓ)) := by
        simpa [IntegrableOn] using hM2
      have h3I : Integrable (fun x : X N => ((omx x * SS x) ^ 2) * wt x)
          (volume.restrict (abox N ℓ)) := by
        simpa [IntegrableOn] using h3
      exact h2I.add h3I
    have hfun_pt : ∀ x : X N,
        (BB x) ^ 2 * wt x = (QQ x) ^ 2 * wt x + (2 * M x + ((omx x * SS x) ^ 2) * wt x) := by
      intro x
      have hsq := q4B_sq_expand (ℓ := ℓ) (om := omC (Classical.choose h)) (Φ := Φ) (i, j) x
      rw [hsq]
      dsimp [QQ, SS, omx, wt, M, BB, omC]
      ring
    have hfun_ae : (fun x : X N => (BB x) ^ 2 * wt x)
        =ᵐ[volume.restrict (abox N ℓ)] fun x : X N =>
            (QQ x) ^ 2 * wt x + (2 * M x + ((omx x * SS x) ^ 2) * wt x) := by
      refine ae_of_all _ (fun x => ?_)
      exact hfun_pt x
    have hsplit1 : (∫ x in abox N ℓ, (BB x) ^ 2 * wt x)
        = (∫ x in abox N ℓ, (QQ x) ^ 2 * wt x)
          + (∫ x in abox N ℓ, 2 * M x + ((omx x * SS x) ^ 2) * wt x) := by
      calc
        (∫ x in abox N ℓ, (BB x) ^ 2 * wt x)
            = (∫ x in abox N ℓ,
                (QQ x) ^ 2 * wt x + (2 * M x + ((omx x * SS x) ^ 2) * wt x)) := by
                apply integral_congr_ae
                exact hfun_ae
        _ = (∫ x in abox N ℓ, (QQ x) ^ 2 * wt x)
            + (∫ x in abox N ℓ, 2 * M x + ((omx x * SS x) ^ 2) * wt x) := by
            rw [integral_add (by simpa [IntegrableOn] using h1) (by simpa [IntegrableOn] using h23)]
    have hMid2 : (∫ x in abox N ℓ, 2 * M x + ((omx x * SS x) ^ 2) * wt x)
        = (∫ x in abox N ℓ, 2 * M x) + (∫ x in abox N ℓ, ((omx x * SS x) ^ 2) * wt x) := by
      rw [integral_add (by simpa [IntegrableOn] using hM2) (by simpa [IntegrableOn] using h3)]
    have hMid : (∫ x in abox N ℓ, 2 * M x)
        = 2 * (∫ x in abox N ℓ, M x) := by
      rw [integral_const_mul]
    calc
      (∫ x in abox N ℓ, (q4B ℓ (omC (Classical.choose h)) Φ (i, j) x) ^ 2 * wPair ℓ v (x i) (x j))
          = (∫ x in abox N ℓ, (BB x) ^ 2 * wt x) := by simp [BB, wt]
      _ = ((∫ x in abox N ℓ, (QQ x) ^ 2 * wt x) + 2 * (∫ x in abox N ℓ, M x))
            + (∫ x in abox N ℓ, ((omx x * SS x) ^ 2) * wt x) := by
            rw [hsplit1]
            rw [hMid2, hMid]
            ring
      _ = (A + 2 * B) + C := by
            simp [A, B, C, QQ, SS, omx, wt, M]
  simpa [A, B, C] using hper

/-- **Per-pair QQ²-`|w₁|`-mass vs `QQ²·wPair(v)`-mass**: since
`|w₁| = |wPair(g₀)| ≤ wPair(v)` pointwise a.e. on the box and `QQ² ≥ 0`,

`∫ QQ²·|wPair(g₀)| ≤ ∫ QQ²·wPair(v)`  (per pair `(i,j)`). -/
lemma qq2_w1_le_w_pair {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (hv_memL1 : MemLp v 1)
    {i j : Fin N} (hij : i ≠ j) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∫ x in abox N ℓ, (aQ ℓ j (aQ ℓ i Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)|)
      ≤ (∫ x in abox N ℓ, (aQ ℓ j (aQ ℓ i Φ) x) ^ 2 * wPair ℓ v (x i) (x j)) := by
  classical
  let QQ : X N → ℝ := fun x => aQ ℓ j (aQ ℓ i Φ) x
  have hL : IntegrableOn (fun x : X N => (QQ x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)|)
      (abox N ℓ) volume := by
    have hg0i : MeasureTheory.Integrable (g0 v h) := g0_integrable hR hv_supp h
    have hg0s : ∀ z : ℝ³, R ≤ ‖z‖ → g0 v h z = 0 := fun z hz => g0_zero_of_norm_ge hv_supp hz h
    have hi := sq_slot_wPair_abs_integrable hℓ hg0i hg0s hRℓ hij (S := QQ) (aQ_continuous hℓ j (aQ_continuous hℓ i hΦc))
    simpa [QQ] using hi
  have hRv : IntegrableOn (fun x : X N => (QQ x) ^ 2 * wPair ℓ v (x i) (x j))
      (abox N ℓ) volume := by
    have hi := q4_cross_f_int hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1
      (i := i) (j := j) hij hΦc
    simpa [QQ] using hi
  have hmono : ∀ᵐ x ∂(volume.restrict (abox N ℓ)),
      (QQ x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)| ≤ (QQ x) ^ 2 * wPair ℓ v (x i) (x j) := by
    have hle := w1_abs_le_w_ae (N := N) hℓ hR hv_nonneg hvrad hv_supp h hij
    filter_upwards [hle] with x hx
    exact mul_le_mul_of_nonneg_left hx (sq_nonneg (QQ x))
  exact integral_mono_ae hL hRv hmono

/-- **QQ²-`|w₁|`-mass vs `QQ²·wPair(v)`-mass, `pairSet`-summed**: the q3-side
`QQ²·w₁`-masses are dominated by the q4-side `QQ²·wPair(v)`-sum. -/
lemma qq2_w1_le_wv_pairs {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (hv_memL1 : MemLp v 1)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
      ≤ (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * wPair ℓ v (x p.1) (x p.2)) := by
  classical
  apply Finset.sum_le_sum
  intro p hp
  have hpij : p.1 ≠ p.2 := by
    simpa [pairSet] using (Finset.mem_filter.mp hp).2
  exact qq2_w1_le_w_pair hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1
    (i := p.1) (j := p.2) hpij hΦc

/-- **QQ²-kernel split, `pairSet`-summed (atom (B))**: from the pointwise
numerator split `v = g₀ + v·ω₀` (`wPair`-linearity),

`Σ∫QQ_p²·wPair(v) = Σ∫QQ_p²·wPair(g₀) + Σ∫QQ_p²·wPair(v·ω₀)`

— the exact `QQ²`-mass account that q4's square-split (`q4word_sq_split`)
feeds into the joint q1+q3+q4 assembly. -/
lemma qq2_wv_eq_w1_add_vw0_pairs {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (hv_memL1 : MemLp v 1)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * wPair ℓ v (x p.1) (x p.2))
      = (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2))
        + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 *
            wPair ℓ (fun z : ℝ³ => v z * Classical.choose h z) (x p.1) (x p.2)) := by
  classical
  let hvw0 : ℝ³ → ℝ := fun z : ℝ³ => v z * Classical.choose h z
  have hvw0i : MeasureTheory.Integrable hvw0 := by
    simpa [hvw0] using (vw0_integrable hR hv_nonneg hvrad hv_supp h hv_memL1)
  have hvw0s : ∀ z : ℝ³, R ≤ ‖z‖ → hvw0 z = 0 := by
    intro z hz
    have hv0 : v z = 0 := v_zero_of_norm_ge hv_supp hz
    dsimp [hvw0]
    simp [hv0]
  have hg0i : MeasureTheory.Integrable (g0 v h) := g0_integrable hR hv_supp h
  have hg0s : ∀ z : ℝ³, R ≤ ‖z‖ → g0 v h z = 0 := fun z hz => g0_zero_of_norm_ge hv_supp hz h
  have hper : ∀ p : Fin N × Fin N, p ∈ pairSet N →
      (∫ x in abox N ℓ, (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * wPair ℓ v (x p.1) (x p.2))
        = (∫ x in abox N ℓ, (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2))
          + (∫ x in abox N ℓ, (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 *
              wPair ℓ hvw0 (x p.1) (x p.2)) := by
    intro p hp
    have hpij : p.1 ≠ p.2 := by
      simpa [pairSet] using (Finset.mem_filter.mp hp).2
    let QQ : X N → ℝ := fun x => (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2
    have hQQc : Continuous QQ := (aQ_continuous hℓ p.2 (aQ_continuous hℓ p.1 hΦc)).pow 2
    have hI1 : IntegrableOn (fun x : X N => QQ x * wPair ℓ (g0 v h) (x p.1) (x p.2))
        (abox N ℓ) volume := by
      exact integrableOn_slot_wPair hℓ hg0i hg0s hRℓ hpij hQQc
    have hI2 : IntegrableOn (fun x : X N => QQ x * wPair ℓ hvw0 (x p.1) (x p.2))
        (abox N ℓ) volume := by
      exact integrableOn_slot_wPair hℓ hvw0i hvw0s hRℓ hpij hQQc
    have hpt : ∀ x : X N,
        QQ x * wPair ℓ v (x p.1) (x p.2)
          = QQ x * wPair ℓ (g0 v h) (x p.1) (x p.2)
            + QQ x * wPair ℓ hvw0 (x p.1) (x p.2) := by
      intro x
      have hsplit := wPair_v_split_g0_vw0 (ℓ := ℓ) (v := v) h (x p.1) (x p.2)
      have hvw0eq : hvw0 = fun z : ℝ³ => v z * Classical.choose h z := by rfl
      rw [← hvw0eq] at hsplit
      rw [hsplit]
      ring
    have hae : (fun x : X N => QQ x * wPair ℓ v (x p.1) (x p.2))
        =ᵐ[volume.restrict (abox N ℓ)] fun x : X N =>
            QQ x * wPair ℓ (g0 v h) (x p.1) (x p.2)
              + QQ x * wPair ℓ hvw0 (x p.1) (x p.2) := by
      refine ae_of_all _ (fun x => ?_)
      exact hpt x
    have hI : IntegrableOn (fun x : X N => QQ x * wPair ℓ v (x p.1) (x p.2))
        (abox N ℓ) volume := by
      have hi := q4_cross_f_int hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1
        (i := p.1) (j := p.2) hpij hΦc
      simpa [QQ] using hi
    calc
      (∫ x in abox N ℓ, (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * wPair ℓ v (x p.1) (x p.2))
          = (∫ x in abox N ℓ, QQ x * wPair ℓ v (x p.1) (x p.2)) := by rfl
      _ = (∫ x in abox N ℓ,
            QQ x * wPair ℓ (g0 v h) (x p.1) (x p.2)
              + QQ x * wPair ℓ hvw0 (x p.1) (x p.2)) := by
            apply integral_congr_ae
            exact hae
      _ = (∫ x in abox N ℓ, QQ x * wPair ℓ (g0 v h) (x p.1) (x p.2))
          + (∫ x in abox N ℓ, QQ x * wPair ℓ hvw0 (x p.1) (x p.2)) := by
          rw [integral_add (by simpa [IntegrableOn] using hI1) (by simpa [IntegrableOn] using hI2)]
      _ = (∫ x in abox N ℓ, (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2))
          + (∫ x in abox N ℓ, (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * wPair ℓ hvw0 (x p.1) (x p.2)) := by
            rfl
  calc
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * wPair ℓ v (x p.1) (x p.2))
        = ∑ p ∈ pairSet N,
            ((∫ x in abox N ℓ, (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2))
              + (∫ x in abox N ℓ, (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * wPair ℓ hvw0 (x p.1) (x p.2))) := by
            refine Finset.sum_congr rfl (fun p hp => ?_)
            exact hper p hp
    _ = (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2))
        + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * wPair ℓ hvw0 (x p.1) (x p.2)) := by
            rw [Finset.sum_add_distrib]
    _ = (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2))
        + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 *
              wPair ℓ (fun z : ℝ³ => v z * Classical.choose h z) (x p.1) (x p.2)) := by
            simp [hvw0]

/-- **QQ²-kernel split, per pair (atom (B))**: pointwise
`wPair(v) = wPair(g₀) + wPair(v·ω₀)` gives per pair `(i,j)`, `i ≠ j`,

`∫ QQ²·wPair(v) = ∫ QQ²·wPair(g₀) + ∫ QQ²·wPair(v·ω₀)`. -/
lemma qq2_wv_eq_w1_add_vw0_pair {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (hv_memL1 : MemLp v 1)
    {i j : Fin N} (hij : i ≠ j) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∫ x in abox N ℓ, (aQ ℓ j (aQ ℓ i Φ) x) ^ 2 * wPair ℓ v (x i) (x j))
      = (∫ x in abox N ℓ, (aQ ℓ j (aQ ℓ i Φ) x) ^ 2 * wPair ℓ (g0 v h) (x i) (x j))
        + (∫ x in abox N ℓ, (aQ ℓ j (aQ ℓ i Φ) x) ^ 2 *
            wPair ℓ (fun z : ℝ³ => v z * Classical.choose h z) (x i) (x j)) := by
  classical
  let hvw0 : ℝ³ → ℝ := fun z : ℝ³ => v z * Classical.choose h z
  have hvw0i : MeasureTheory.Integrable hvw0 := by
    simpa [hvw0] using (vw0_integrable hR hv_nonneg hvrad hv_supp h hv_memL1)
  have hvw0s : ∀ z : ℝ³, R ≤ ‖z‖ → hvw0 z = 0 := by
    intro z hz
    have hv0 : v z = 0 := v_zero_of_norm_ge hv_supp hz
    dsimp [hvw0]
    simp [hv0]
  have hg0i : MeasureTheory.Integrable (g0 v h) := g0_integrable hR hv_supp h
  have hg0s : ∀ z : ℝ³, R ≤ ‖z‖ → g0 v h z = 0 := fun z hz => g0_zero_of_norm_ge hv_supp hz h
  let QQ : X N → ℝ := fun x => (aQ ℓ j (aQ ℓ i Φ) x) ^ 2
  have hQQc : Continuous QQ := (aQ_continuous hℓ j (aQ_continuous hℓ i hΦc)).pow 2
  have hI1 : IntegrableOn (fun x : X N => QQ x * wPair ℓ (g0 v h) (x i) (x j))
      (abox N ℓ) volume := by
    exact integrableOn_slot_wPair hℓ hg0i hg0s hRℓ hij hQQc
  have hI2 : IntegrableOn (fun x : X N => QQ x * wPair ℓ hvw0 (x i) (x j))
      (abox N ℓ) volume := by
    exact integrableOn_slot_wPair hℓ hvw0i hvw0s hRℓ hij hQQc
  have hpt : ∀ x : X N,
      QQ x * wPair ℓ v (x i) (x j)
        = QQ x * wPair ℓ (g0 v h) (x i) (x j)
          + QQ x * wPair ℓ hvw0 (x i) (x j) := by
    intro x
    have hsplit := wPair_v_split_g0_vw0 (ℓ := ℓ) (v := v) h (x i) (x j)
    have hvw0eq : hvw0 = fun z : ℝ³ => v z * Classical.choose h z := by rfl
    rw [← hvw0eq] at hsplit
    rw [hsplit]
    ring
  have hae : (fun x : X N => QQ x * wPair ℓ v (x i) (x j))
      =ᵐ[volume.restrict (abox N ℓ)] fun x : X N =>
          QQ x * wPair ℓ (g0 v h) (x i) (x j)
            + QQ x * wPair ℓ hvw0 (x i) (x j) := by
    refine ae_of_all _ (fun x => ?_)
    exact hpt x
  have hI : IntegrableOn (fun x : X N => QQ x * wPair ℓ v (x i) (x j))
      (abox N ℓ) volume := by
    have hi := q4_cross_f_int hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1
      (i := i) (j := j) hij hΦc
    simpa [QQ] using hi
  calc
    (∫ x in abox N ℓ, (aQ ℓ j (aQ ℓ i Φ) x) ^ 2 * wPair ℓ v (x i) (x j))
        = (∫ x in abox N ℓ, QQ x * wPair ℓ v (x i) (x j)) := by rfl
    _ = (∫ x in abox N ℓ,
          QQ x * wPair ℓ (g0 v h) (x i) (x j)
            + QQ x * wPair ℓ hvw0 (x i) (x j)) := by
          apply integral_congr_ae
          exact hae
    _ = (∫ x in abox N ℓ, QQ x * wPair ℓ (g0 v h) (x i) (x j))
        + (∫ x in abox N ℓ, QQ x * wPair ℓ hvw0 (x i) (x j)) := by
        rw [integral_add (by simpa [IntegrableOn] using hI1) (by simpa [IntegrableOn] using hI2)]
    _ = (∫ x in abox N ℓ, (aQ ℓ j (aQ ℓ i Φ) x) ^ 2 * wPair ℓ (g0 v h) (x i) (x j))
        + (∫ x in abox N ℓ, (aQ ℓ j (aQ ℓ i Φ) x) ^ 2 * wPair ℓ hvw0 (x i) (x j)) := by
        rfl
    _ = (∫ x in abox N ℓ, (aQ ℓ j (aQ ℓ i Φ) x) ^ 2 * wPair ℓ (g0 v h) (x i) (x j))
        + (∫ x in abox N ℓ, (aQ ℓ j (aQ ℓ i Φ) x) ^ 2 *
            wPair ℓ (fun z : ℝ³ => v z * Classical.choose h z) (x i) (x j)) := by
            simp [hvw0]

/-- **Per-pair signed ω-cross bound (atom (A))**: from `q4_pair_sq_split`
dropping the nonnegative `(ω·S)²`-part (`wPair(v) ≥ 0`),

`½·∫ QQ²·wPair(v) + ∫ QQ·(ω·S)·wPair(v) ≤ ½·∫(q4B)²·wPair(v)`

— the per-pair form in which q4's square dominates the QQ²-mass plus the
signed ω-cross. -/
lemma q4_pair_ge_signed {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (hv_memL1 : MemLp v 1)
    {i j : Fin N} (hij : i ≠ j) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (1 / 2) * (∫ x in abox N ℓ, (aQ ℓ j (aQ ℓ i Φ) x) ^ 2 * wPair ℓ v (x i) (x j))
      + (∫ x in abox N ℓ,
          (aQ ℓ j (aQ ℓ i Φ) x) *
            ((Classical.choose h (x i - x j)) *
              ((aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x))) *
            (wPair ℓ v (x i) (x j)))
    ≤ (1 / 2) * (∫ x in abox N ℓ, (q4B ℓ (omC (Classical.choose h)) Φ (i, j) x) ^ 2 *
        wPair ℓ v (x i) (x j)) := by
  classical
  have hsq := q4_pair_sq_split hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1 hij hΦc
  rw [hsq]
  have hWnn : 0 ≤ ∫ x in abox N ℓ,
      ((Classical.choose h (x i - x j)) *
        ((aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x))) ^ 2 *
        (wPair ℓ v (x i) (x j)) := by
    apply integral_nonneg
    intro x
    exact mul_nonneg (sq_nonneg (Classical.choose h (x i - x j) *
        ((aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x))))
      (wPairC_nonneg hv_nonneg ℓ (x i) (x j))
  nlinarith

/-- **w₁ω-line ↔ w₁ω-pair-sum** (the PPQω-cancellation identity): the
`w₁ω`-line of `q1word_eq_q1n0_split` (the `f₁ω`-sandwich with the realised
`n₀ = Σ_j P_j`, kernel `g₀ω₀`) equals the `w₁ω`-pair-sum over `pairSet`
(`q1_pair_part_sandwich_w0`'s RHS presented in the `aQ_i((Σ_{j≠i}P_j)Φ)`-form
via `q1_n0_collapse`).  This is the exact corpus partner that the q3+q4
`eq:Q3+Q4CS` leftover (kernel `w₁ω`) cancels in the joint q1+q3+q4
assembly. -/
lemma q1w0_pair_sum_eq_sandwich_n0 {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.1 (aP ℓ p.2 Φ) x) *
          wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))
    = 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
        (aP ℓ i Φ x) *
          (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i)) *
          (aQ ℓ i (fun y : X N => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0))) x) := by
  classical
  have hsand := q1_pair_part_sandwich_w0 (N := N) hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
  have hper : ∀ i : Fin N,
      (∫ x in abox N ℓ,
        (aP ℓ i Φ x) *
          (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i)) *
          (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j (aQ ℓ i Φ) x else 0))
      = (∫ x in abox N ℓ,
          (aP ℓ i Φ x) *
            (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i)) *
            (aQ ℓ i (fun y : X N => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0))) x) := by
    intro i
    apply integral_congr_ae
    refine ae_of_all _ (fun x => ?_)
    dsimp
    have hc := q1_n0_collapse (N := N) hℓ i hΦc x
    simpa using congrArg (fun t : ℝ =>
        aP ℓ i Φ x * w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i) * t) hc
  calc
    2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.1 (aP ℓ p.2 Φ) x) *
          wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))
        = 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
        (aP ℓ i Φ x) *
          (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i)) *
          (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j (aQ ℓ i Φ) x else 0)) := hsand
    _ = 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
        (aP ℓ i Φ x) *
          (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i)) *
          (aQ ℓ i (fun y : X N => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0))) x) := by
            apply congrArg (fun t : ℝ => 2 * (ℓ ^ 3)⁻¹ * t)
            exact Finset.sum_congr rfl (fun i hi => hper i)


/-! ## The q3-word expansion exposing the PPQω-leftover (Session-145b)

* `q3_pair_expand` — per pair `(i,j)`: inside q3's pair integrand write
  `QQ = q4B − ω·(PP+PQ+QP)` (`q4B_expand`) and use
  `w₁·ω₀ = wPair(g₀ω₀)` (`w1_mul_omega_eq_w1w`), giving the EXACT integral
  identity

  `2∫(P_iQ_jΦ)(Q_jQ_iΦ)·w₁ = 2∫(P_iQ_jΦ)·(q4B(i,j))·w₁
     − 2∫(P_iQ_jΦ)(P_jP_iΦ)·w₁ω  − 2∫(P_iQ_jΦ)(P_jQ_iΦ)·w₁ω
     − 2∫(P_iQ_jΦ)(Q_jP_iΦ)·w₁ω`

  (`w₁ := wPair(g₀)`, `w₁ω := wPair(g₀ω₀)`) — q3's pair term rewritten so
  that the `PPQω`-leftover (kernel `w₁ω`, the `eq:Q3+Q4CS` cancellation
  partner of q1's w₁ω-line) is isolated with its exact sign and coefficient.

* `q3word_expand` — the `pairSet`-summed version:

  `q3word(ℓ, w₁)Φ = [q4B-cross-sum] − [PPQω-pair-sum] − [PQω-sum] − [QPω-sum]`

  where the q4B-cross-sum `2·Σ_p∫(P_{p.1}Q_{p.2}Φ)·(q4B_p)·w₁` is absorbed
  into q4's square by completing the square against
  `½Σ∫(q4B)²·w₁ ≤ q4word` (w₁ ≤ w(v)) — the FS "absorb Q3 in Q4" step —
  leaving the PPQω-leftover plus mass terms.

Proof idioms (recorded): sum bodies with top-level `−` must be parenthesised
`∑ p ∈ s, (A − B − C − D)` (else `p` escapes the binder); splitting such a
sum is `simp [Finset.sum_sub_distrib]`; integrability of `A·(ω·SS)·w₁` by
domination `|ω| ≤ 1` a.e. + `|w₁| ≤ wPair(v)` a.e. (`w1_abs_le_w_ae`);
`dsimp [omC]` must precede `ring` after `rw [q4B_expand ...]`; name
`Integrable`s before `.add`/`.sub`/`.congr`.
-/
/-- **Per-pair q3-word expansion exposing the PPQω-leftover (eq:Q3+Q4CS
atom)**: writing `QQ = q4B − ω·(PP+PQ+QP)` (`q4B_expand`) inside q3's pair
integrand and using `w₁·ω₀ = wPair(g₀ω₀)` (`w1_mul_omega_eq_w1w`),

`2∫(P_iQ_jΦ)(Q_jQ_iΦ)·w₁
 = 2∫(P_iQ_jΦ)·(q4B(i,j))·w₁
   − 2∫(P_iQ_jΦ)(P_jP_iΦ)·w₁ω   [the PPQω leftover, kernel g₀ω₀]
   − 2∫(P_iQ_jΦ)(P_jQ_iΦ)·w₁ω   [PQω 2-Q cross]
   − 2∫(P_iQ_jΦ)(Q_jP_iΦ)·w₁ω   [QPω 2-Q cross]`

per pair `(i,j)`, `i ≠ j`, `w₁ := wPair(g₀)`, `w₁ω := wPair(g₀ω₀)`. -/
lemma q3_pair_expand {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (hv_memL1 : MemLp v 1)
    {i j : Fin N} (hij : i ≠ j) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    2 * (∫ x in abox N ℓ,
        (aP ℓ i (aQ ℓ j Φ) x) * (aQ ℓ j (aQ ℓ i Φ) x) * wPair ℓ (g0 v h) (x i) (x j))
    = 2 * (∫ x in abox N ℓ,
        (aP ℓ i (aQ ℓ j Φ) x) * (q4B ℓ (omC (Classical.choose h)) Φ (i, j) x) *
          wPair ℓ (g0 v h) (x i) (x j))
      - 2 * (∫ x in abox N ℓ,
        (aP ℓ i (aQ ℓ j Φ) x) * (aP ℓ j (aP ℓ i Φ) x) *
          wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x i) (x j))
      - 2 * (∫ x in abox N ℓ,
        (aP ℓ i (aQ ℓ j Φ) x) * (aP ℓ j (aQ ℓ i Φ) x) *
          wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x i) (x j))
      - 2 * (∫ x in abox N ℓ,
        (aP ℓ i (aQ ℓ j Φ) x) * (aQ ℓ j (aP ℓ i Φ) x) *
          wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x i) (x j)) := by
  classical
  let A : X N → ℝ := fun x => aP ℓ i (aQ ℓ j Φ) x
  let QQ : X N → ℝ := fun x => aQ ℓ j (aQ ℓ i Φ) x
  let S1 : X N → ℝ := fun x => aP ℓ j (aP ℓ i Φ) x
  let S2 : X N → ℝ := fun x => aP ℓ j (aQ ℓ i Φ) x
  let S3 : X N → ℝ := fun x => aQ ℓ j (aP ℓ i Φ) x
  let SS : X N → ℝ := fun x => S1 x + S2 x + S3 x
  let BB : X N → ℝ := fun x => q4B ℓ (omC (Classical.choose h)) Φ (i, j) x
  let omx : X N → ℝ := fun x => Classical.choose h (x i - x j)
  let w1 : X N → ℝ := fun x => wPair ℓ (g0 v h) (x i) (x j)
  let w1w : X N → ℝ := fun x => wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x i) (x j)
  let L : ℝ := ∫ x in abox N ℓ, A x * QQ x * w1 x
  let B : ℝ := ∫ x in abox N ℓ, A x * BB x * w1 x
  let Iω : ℝ := ∫ x in abox N ℓ, A x * (omx x * SS x) * w1 x
  let T1 : ℝ := ∫ x in abox N ℓ, A x * S1 x * w1w x
  let T2 : ℝ := ∫ x in abox N ℓ, A x * S2 x * w1w x
  let T3 : ℝ := ∫ x in abox N ℓ, A x * S3 x * w1w x
  have hg0i : MeasureTheory.Integrable (g0 v h) := g0_integrable hR hv_supp h
  have hg0s : ∀ z : ℝ³, R ≤ ‖z‖ → g0 v h z = 0 := fun z hz => g0_zero_of_norm_ge hv_supp hz h
  have hgw0i : MeasureTheory.Integrable (fun w : ℝ³ => g0 v h w * Classical.choose h w) :=
    g0w0_integrable hR hv_nonneg hvrad hv_supp h
  have hgw0s : ∀ z : ℝ³, R ≤ ‖z‖ → (fun w : ℝ³ => g0 v h w * Classical.choose h w) z = 0 := by
    intro z hz
    have hgz : g0 v h z = 0 := g0_zero_of_norm_ge hv_supp hz h
    simp [hgz]
  have hvzero : ∀ z : ℝ³, R ≤ ‖z‖ → v z = 0 := fun z hz => v_zero_of_norm_ge hv_supp hz
  have hAc : Continuous A := by
    dsimp [A]
    exact aP_continuous hℓ i (aQ_continuous hℓ j hΦc)
  have hQQc : Continuous QQ := by
    dsimp [QQ]
    exact aQ_continuous hℓ j (aQ_continuous hℓ i hΦc)
  have hS1c : Continuous S1 := by
    dsimp [S1]
    exact aP_continuous hℓ j (aP_continuous hℓ i hΦc)
  have hS2c : Continuous S2 := by
    dsimp [S2]
    exact aP_continuous hℓ j (aQ_continuous hℓ i hΦc)
  have hS3c : Continuous S3 := by
    dsimp [S3]
    exact aQ_continuous hℓ j (aP_continuous hℓ i hΦc)
  have hSSc : Continuous SS := (hS1c.add hS2c).add hS3c
  have hIQQ : IntegrableOn (fun x => A x * QQ x * w1 x) (abox N ℓ) volume := by
    have h := integrableOn_slot_wPair hℓ hg0i hg0s hRℓ hij (S := fun x => A x * QQ x) (hAc.mul hQQc)
    simpa [A, QQ, w1] using h
  have hI1 : IntegrableOn (fun x => A x * S1 x * w1w x) (abox N ℓ) volume := by
    have h := integrableOn_slot_wPair hℓ hgw0i hgw0s hRℓ hij (S := fun x => A x * S1 x) (hAc.mul hS1c)
    simpa [A, S1, w1w] using h
  have hI2 : IntegrableOn (fun x => A x * S2 x * w1w x) (abox N ℓ) volume := by
    have h := integrableOn_slot_wPair hℓ hgw0i hgw0s hRℓ hij (S := fun x => A x * S2 x) (hAc.mul hS2c)
    simpa [A, S2, w1w] using h
  have hI3 : IntegrableOn (fun x => A x * S3 x * w1w x) (abox N ℓ) volume := by
    have h := integrableOn_slot_wPair hℓ hgw0i hgw0s hRℓ hij (S := fun x => A x * S3 x) (hAc.mul hS3c)
    simpa [A, S3, w1w] using h
  have hI12 : IntegrableOn (fun x => A x * S1 x * w1w x + A x * S2 x * w1w x) (abox N ℓ) volume := by
    change Integrable (fun x => A x * S1 x * w1w x + A x * S2 x * w1w x)
        (volume.restrict (abox N ℓ))
    have h1I : Integrable (fun x => A x * S1 x * w1w x) (volume.restrict (abox N ℓ)) := by
      simpa [IntegrableOn] using hI1
    have h2I : Integrable (fun x => A x * S2 x * w1w x) (volume.restrict (abox N ℓ)) := by
      simpa [IntegrableOn] using hI2
    exact h1I.add h2I
  -- |ω| ≤ 1 a.e. and |w₁| ≤ wPair(v) a.e. (w1_abs_le_w_ae); domination for the ω-piece
  have homxb : ∀ᵐ x ∂(volume.restrict (abox N ℓ)), |omx x| ≤ 1 := by
    dsimp [omx]
    simpa using (w0_abs_le_one_box_ae (N := N) hℓ hR hv_nonneg hvrad hv_supp h hij)
  have hw1le : ∀ᵐ x ∂(volume.restrict (abox N ℓ)),
      |w1 x| ≤ wPair ℓ v (x i) (x j) := by
    have hle := w1_abs_le_w_ae (N := N) hℓ hR hv_nonneg hvrad hv_supp h hij
    filter_upwards [hle] with x hx
    simpa [w1] using hx
  have hIomxS : IntegrableOn (fun x => A x * (omx x * SS x) * w1 x) (abox N ℓ) volume := by
    let μ : Measure (X N) := volume.restrict (abox N ℓ)
    have hASv : IntegrableOn (fun x => |A x * SS x| * wPair ℓ v (x i) (x j))
        (abox N ℓ) volume := by
      have h := integrableOn_slot_wPair hℓ (v_integrable hv_memL1) hvzero hRℓ hij
        (S := fun x => |A x * SS x|) ((hAc.mul hSSc).abs)
      simpa [A, SS] using h
    have hbnd : ∀ᵐ x ∂μ, ‖A x * (omx x * SS x) * w1 x‖ ≤ |A x * SS x| * wPair ℓ v (x i) (x j) := by
      filter_upwards [homxb, hw1le] with x hx1 hx2
      calc
        ‖A x * (omx x * SS x) * w1 x‖ = |A x * (omx x * SS x)| * |w1 x| := by
            rw [Real.norm_eq_abs, abs_mul]
        _ = (|A x| * (|omx x| * |SS x|)) * |w1 x| := by
            rw [abs_mul, abs_mul]
        _ ≤ (|A x| * (1 * |SS x|)) * wPair ℓ v (x i) (x j) := by
            have hm : |omx x| * |SS x| ≤ 1 * |SS x| :=
              mul_le_mul_of_nonneg_right hx1 (abs_nonneg (SS x))
            have h1 : |A x| * (|omx x| * |SS x|) ≤ |A x| * (1 * |SS x|) :=
              mul_le_mul_of_nonneg_left hm (abs_nonneg (A x))
            have hw0 : 0 ≤ wPair ℓ v (x i) (x j) := wPairC_nonneg hv_nonneg ℓ (x i) (x j)
            have h2 : (|A x| * (|omx x| * |SS x|)) * |w1 x|
                ≤ (|A x| * (1 * |SS x|)) * wPair ℓ v (x i) (x j) := by
              exact mul_le_mul h1 hx2 (abs_nonneg _)
                (mul_nonneg (abs_nonneg _) (mul_nonneg (by norm_num) (abs_nonneg _)))
            simpa [mul_assoc] using h2
        _ = |A x * SS x| * wPair ℓ v (x i) (x j) := by
            rw [abs_mul]
            ring
    have haem : AEStronglyMeasurable (fun x => A x * (omx x * SS x) * w1 x) μ := by
      have hom : AEStronglyMeasurable omx μ := by
        dsimp [omx, μ]
        simpa using (w0_diff_aem (N := N) (ℓ := ℓ) hℓ hij (w0 := Classical.choose h) (w0_spec h).2.lhs_integrable)
      have hw1aem : AEStronglyMeasurable w1 μ := by
        have hwI : Integrable w1 μ := by
          have hs : IntegrableOn (fun x : X N => wPair ℓ (g0 v h) (x i) (x j)) (abox N ℓ) volume := by
            simpa using (integrableOn_slot_wPair hℓ hg0i hg0s hRℓ hij
              (S := fun _ : X N => (1 : ℝ)) (by fun_prop : Continuous (fun _ : X N => (1 : ℝ))))
          simpa [w1, μ, IntegrableOn] using hs
        exact hwI.aestronglyMeasurable
      exact ((hAc.aestronglyMeasurable.mul (hom.mul hSSc.aestronglyMeasurable))).mul hw1aem
    exact Integrable.mono' hASv haem hbnd
  -- pointwise identity BB = QQ + ω·SS (q4B_expand)
  have hBBpt : ∀ x : X N, BB x = QQ x + omx x * SS x := by
    intro x
    dsimp [QQ, S1, S2, S3, SS, BB, omx]
    rw [q4B_expand (ℓ := ℓ) (om := omC (Classical.choose h)) (Φ := Φ) (i, j) x]
    dsimp [omC]
  have hIBB : IntegrableOn (fun x => A x * BB x * w1 x) (abox N ℓ) volume := by
    have hsum : IntegrableOn (fun x => A x * QQ x * w1 x + A x * (omx x * SS x) * w1 x)
        (abox N ℓ) volume := by
      change Integrable (fun x => A x * QQ x * w1 x + A x * (omx x * SS x) * w1 x)
          (volume.restrict (abox N ℓ))
      have hqI : Integrable (fun x => A x * QQ x * w1 x) (volume.restrict (abox N ℓ)) := by
        simpa [IntegrableOn] using hIQQ
      have hoI : Integrable (fun x => A x * (omx x * SS x) * w1 x) (volume.restrict (abox N ℓ)) := by
        simpa [IntegrableOn] using hIomxS
      exact hqI.add hoI
    have hcong : (fun x => A x * BB x * w1 x) =ᵐ[volume.restrict (abox N ℓ)]
        fun x => A x * QQ x * w1 x + A x * (omx x * SS x) * w1 x := by
      refine ae_of_all _ (fun x => ?_)
      change A x * BB x * w1 x = A x * QQ x * w1 x + A x * (omx x * SS x) * w1 x
      rw [hBBpt x]
      ring
    exact hsum.congr hcong.symm
  -- step 1: L = B − Iω
  have hstep1 : L = B - Iω := by
    dsimp [L, B, Iω]
    have hpt : (fun x => A x * QQ x * w1 x) =ᵐ[volume.restrict (abox N ℓ)]
        fun x => A x * BB x * w1 x - A x * (omx x * SS x) * w1 x := by
      refine ae_of_all _ (fun x => ?_)
      change A x * QQ x * w1 x = A x * BB x * w1 x - A x * (omx x * SS x) * w1 x
      rw [hBBpt x]
      ring
    calc
      (∫ x in abox N ℓ, A x * QQ x * w1 x)
          = (∫ x in abox N ℓ, A x * BB x * w1 x - A x * (omx x * SS x) * w1 x) := by
              apply integral_congr_ae
              exact hpt
      _ = (∫ x in abox N ℓ, A x * BB x * w1 x)
          - (∫ x in abox N ℓ, A x * (omx x * SS x) * w1 x) := by
          have hBI : Integrable (fun x => A x * BB x * w1 x) (volume.restrict (abox N ℓ)) := by
            simpa [IntegrableOn] using hIBB
          have hωI : Integrable (fun x => A x * (omx x * SS x) * w1 x)
              (volume.restrict (abox N ℓ)) := by
            simpa [IntegrableOn] using hIomxS
          rw [integral_sub hBI hωI]
  -- step 2: Iω = T1 + T2 + T3 (kernel identity ω·w1 = w1w, then split the sum)
  have hker : ∀ x : X N, omx x * w1 x = w1w x := by
    intro x
    have hw := w1_mul_omega_eq_w1w (ℓ := ℓ) (v := v) h (x i) (x j)
    simpa [omx, w1, w1w, omC, wPairC, mul_comm, mul_left_comm, mul_assoc] using hw
  have hstep2 : Iω = T1 + T2 + T3 := by
    dsimp [Iω, T1, T2, T3]
    have hpt1 : (fun x => A x * (omx x * SS x) * w1 x) =ᵐ[volume.restrict (abox N ℓ)]
        fun x => (A x * S1 x * w1w x + A x * S2 x * w1w x) + A x * S3 x * w1w x := by
      refine ae_of_all _ (fun x => ?_)
      have hkerx := hker x
      dsimp [SS]
      rw [show A x * (omx x * (S1 x + S2 x + S3 x)) * w1 x
              = A x * (S1 x + S2 x + S3 x) * (omx x * w1 x) by ring]
      rw [hkerx]
      ring
    calc
      (∫ x in abox N ℓ, A x * (omx x * SS x) * w1 x)
          = (∫ x in abox N ℓ,
              (A x * S1 x * w1w x + A x * S2 x * w1w x) + A x * S3 x * w1w x) := by
              apply integral_congr_ae
              exact hpt1
      _ = (∫ x in abox N ℓ, A x * S1 x * w1w x + A x * S2 x * w1w x)
          + (∫ x in abox N ℓ, A x * S3 x * w1w x) := by
          have h12I : Integrable (fun x => A x * S1 x * w1w x + A x * S2 x * w1w x)
              (volume.restrict (abox N ℓ)) := by
            simpa [IntegrableOn] using hI12
          have h3I : Integrable (fun x => A x * S3 x * w1w x) (volume.restrict (abox N ℓ)) := by
            simpa [IntegrableOn] using hI3
          rw [integral_add h12I h3I]
      _ = ((∫ x in abox N ℓ, A x * S1 x * w1w x) + (∫ x in abox N ℓ, A x * S2 x * w1w x))
          + (∫ x in abox N ℓ, A x * S3 x * w1w x) := by
          have h1I : Integrable (fun x => A x * S1 x * w1w x) (volume.restrict (abox N ℓ)) := by
            simpa [IntegrableOn] using hI1
          have h2I : Integrable (fun x => A x * S2 x * w1w x) (volume.restrict (abox N ℓ)) := by
            simpa [IntegrableOn] using hI2
          rw [integral_add h1I h2I]
      _ = T1 + T2 + T3 := by
          dsimp [T1, T2, T3]
  -- assemble
  have hmain : L = B - T1 - T2 - T3 := by
    rw [hstep1, hstep2]
    ring
  have htwo : 2 * L = 2 * B - 2 * T1 - 2 * T2 - 2 * T3 := by
    rw [hmain]
    ring
  simpa [L, B, T1, T2, T3] using htwo

/-- **Summed q3-word expansion (eq:Q3+Q4CS transcription spine)**: summing
`q3_pair_expand` over `pairSet`,

`q3word(ℓ, w₁)Φ = [q4B-cross-sum] − [PPQω-pair-sum] − [PQω-sum] − [QPω-sum]`

where `w₁ := wPairC(g₀)`, the q4B-cross-sum is
`2·Σ_p∫(P_{p.1}Q_{p.2}Φ)·(q4B_p)·w₁`, the PPQω-pair-sum is the
`w₁ω := wPairC(g₀ω₀)`-kernel sum `2·Σ_p∫(P_{p.1}Q_{p.2}Φ)(P_{p.1}P_{p.2}Φ)w₁ω`
(= `q1_pair_part_sandwich_w0`'s LHS, the exact cancellation partner of q1's
w₁ω-line), and PQω/QPω are the two 2-Q `ω`-crosses that FS absorb by a second
Cauchy–Schwarz. -/
lemma q3word_expand {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (hv_memL1 : MemLp v 1)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ
    = 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (q4B ℓ (omC (Classical.choose h)) Φ p x) *
          wPair ℓ (g0 v h) (x p.1) (x p.2))
      - 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aP ℓ p.1 Φ) x) *
          wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))
      - 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aQ ℓ p.1 Φ) x) *
          wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))
      - 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aP ℓ p.1 Φ) x) *
          wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2)) := by
  classical
  have hper : ∀ p : Fin N × Fin N, p ∈ pairSet N →
      2 * (∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
            wPair ℓ (g0 v h) (x p.1) (x p.2))
      = 2 * (∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (q4B ℓ (omC (Classical.choose h)) Φ p x) *
            wPair ℓ (g0 v h) (x p.1) (x p.2))
        - 2 * (∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aP ℓ p.1 Φ) x) *
            wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))
        - 2 * (∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aQ ℓ p.1 Φ) x) *
            wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))
        - 2 * (∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aP ℓ p.1 Φ) x) *
            wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2)) := by
    intro p hp
    have hpij : p.1 ≠ p.2 := by
      simpa [pairSet] using (Finset.mem_filter.mp hp).2
    exact q3_pair_expand hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1
      (i := p.1) (j := p.2) hpij hΦc
  have hsum : (∑ p ∈ pairSet N, 2 * (∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
          wPair ℓ (g0 v h) (x p.1) (x p.2)))
    = (∑ p ∈ pairSet N,
        (2 * (∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (q4B ℓ (omC (Classical.choose h)) Φ p x) *
            wPair ℓ (g0 v h) (x p.1) (x p.2))
        - 2 * (∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aP ℓ p.1 Φ) x) *
            wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))
        - 2 * (∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aQ ℓ p.1 Φ) x) *
            wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))
        - 2 * (∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aP ℓ p.1 Φ) x) *
            wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2)))) := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    exact hper p hp
  calc
    q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ
        = 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
              wPair ℓ (g0 v h) (x p.1) (x p.2)) := by
            unfold q3word
            simp [wPairC]
    _ = ∑ p ∈ pairSet N, 2 * (∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
            wPair ℓ (g0 v h) (x p.1) (x p.2)) := by
          rw [Finset.mul_sum]
    _ = (∑ p ∈ pairSet N,
        (2 * (∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (q4B ℓ (omC (Classical.choose h)) Φ p x) *
            wPair ℓ (g0 v h) (x p.1) (x p.2))
        - 2 * (∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aP ℓ p.1 Φ) x) *
            wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))
        - 2 * (∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aQ ℓ p.1 Φ) x) *
            wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))
        - 2 * (∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aP ℓ p.1 Φ) x) *
            wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2)))) := hsum
    _ = (∑ p ∈ pairSet N, 2 * (∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (q4B ℓ (omC (Classical.choose h)) Φ p x) *
            wPair ℓ (g0 v h) (x p.1) (x p.2)))
        - (∑ p ∈ pairSet N, 2 * (∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aP ℓ p.1 Φ) x) *
            wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2)))
        - (∑ p ∈ pairSet N, 2 * (∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aQ ℓ p.1 Φ) x) *
            wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2)))
        - (∑ p ∈ pairSet N, 2 * (∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aP ℓ p.1 Φ) x) *
            wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))) := by
          simp [Finset.sum_sub_distrib]
    _ = 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (q4B ℓ (omC (Classical.choose h)) Φ p x) *
          wPair ℓ (g0 v h) (x p.1) (x p.2))
      - 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aP ℓ p.1 Φ) x) *
          wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))
      - 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aQ ℓ p.1 Φ) x) *
          wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))
      - 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aP ℓ p.1 Φ) x) *
          wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2)) := by
          simp [Finset.mul_sum]
/-- **q3's PPQω-sum = q1's w₁ω-pair-sum** (per-pair `aP_comm`, pure algebra):
the `PPQω`-leftover of `q3word_expand` (second factor `P_{p.2}P_{p.1}Φ`)
equals the `w₁ω`-pair-sum of `q1_pair_part_sandwich_w0` (second factor
`P_{p.1}P_{p.2}Φ`, slots commute) — the exact cancellation pairing of the
joint q1+q3+q4 assembly. -/
lemma q3_PPQw_eq_q1_pair_sum_w0 {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aP ℓ p.1 Φ) x) *
          wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))
    = (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.1 (aP ℓ p.2 Φ) x) *
          wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2)) := by
  classical
  refine Finset.sum_congr rfl (fun p hp => ?_)
  apply integral_congr_ae
  refine ae_of_all _ (fun x => ?_)
  dsimp
  rw [aP_comm hℓ p.1 p.2 hΦc x]

/-! ## q4-absorption atoms (Session-145c): `w₁ ≥ 0` a.e. and `(q4B)²·w₁`
integrability — the two generic ingredients of the per-pair completing-square
absorption `½∫(q4B)²·w₁ + 2∫A·q4B·w₁ ≥ −2∫A²·w₁` (the FS "absorb Q3 in
Q4" step) that finishes the `eq:Q3+Q4CS` lower-bound form
`q3word + q4word ≥ −[PPQω-pair-sum] − masses` from `q3word_expand`.
-/
lemma w1_nonneg_ae_pair {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ} {R : ℝ}
    (hR : 0 < R) (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    {i j : Fin N} (hij : i ≠ j) :
    ∀ᵐ x ∂(volume.restrict (abox N ℓ)), 0 ≤ wPair ℓ (g0 v h) (x i) (x j) := by
  classical
  have hg0 : ∀ᵐ z : ℝ³, 0 ≤ g0 v h z := g0_nonneg_ae hR hv_nonneg hvrad hv_supp h
  have hp := ae_pair_pullback (N := N) hℓ hij hg0
  filter_upwards [hp] with x hx
  change 0 ≤ chiScale ℓ (x i) * (g0 v h (x i - x j) / convScale ℓ (x i - x j)) * chiScale ℓ (x j)
  exact mul_nonneg
    (mul_nonneg (chiScale_nonneg ℓ (x i)) (div_nonneg hx (convScale_nonneg ℓ (x i - x j))))
    (chiScale_nonneg ℓ (x j))

/-- `(q4B)²·w₁`-integrability per pair (domination onto `(q4B)²·wPair(v)` via
`|w₁| ≤ wPair(v)` a.e.). -/
lemma q4B_sq_w1_integrable {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (hv_memL1 : MemLp v 1)
    {i j : Fin N} (hij : i ≠ j) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    IntegrableOn (fun x : X N =>
      (q4B ℓ (omC (Classical.choose h)) Φ (i, j) x) ^ 2 * wPair ℓ (g0 v h) (x i) (x j))
      (abox N ℓ) volume := by
  classical
  let μ : Measure (X N) := volume.restrict (abox N ℓ)
  let BB : X N → ℝ := fun x => q4B ℓ (omC (Classical.choose h)) Φ (i, j) x
  let w1 : X N → ℝ := fun x => wPair ℓ (g0 v h) (x i) (x j)
  let wt : X N → ℝ := fun x => wPair ℓ v (x i) (x j)
  have hBv : IntegrableOn (fun x => (BB x) ^ 2 * wt x) (abox N ℓ) volume := by
    have hi := q4B_sq_w_integrable hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1 hij hΦc
    simpa [BB, wt] using hi
  have hw1le : ∀ᵐ x ∂μ, |w1 x| ≤ wt x := by
    have hle := w1_abs_le_w_ae (N := N) hℓ hR hv_nonneg hvrad hv_supp h hij
    filter_upwards [hle] with x hx
    simpa [w1, wt] using hx
  have hbnd : ∀ᵐ x ∂μ, ‖(BB x) ^ 2 * w1 x‖ ≤ (BB x) ^ 2 * wt x := by
    filter_upwards [hw1le] with x hx
    have hnn : 0 ≤ (BB x) ^ 2 := sq_nonneg (BB x)
    calc
      ‖(BB x) ^ 2 * w1 x‖ = (BB x) ^ 2 * |w1 x| := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
      _ ≤ (BB x) ^ 2 * wt x := mul_le_mul_of_nonneg_left hx hnn
  have haem : AEStronglyMeasurable (fun x => (BB x) ^ 2 * w1 x) μ := by
    have hw1aem : AEStronglyMeasurable w1 μ := by
      have hwI : Integrable w1 μ := by
        have hs : IntegrableOn (fun x : X N => wPair ℓ (g0 v h) (x i) (x j)) (abox N ℓ) volume := by
          have hg0i : MeasureTheory.Integrable (g0 v h) := g0_integrable hR hv_supp h
          have hg0s : ∀ z : ℝ³, R ≤ ‖z‖ → g0 v h z = 0 := fun z hz => g0_zero_of_norm_ge hv_supp hz h
          simpa using (integrableOn_slot_wPair hℓ hg0i hg0s hRℓ hij
            (S := fun _ : X N => (1 : ℝ)) (by fun_prop : Continuous (fun _ : X N => (1 : ℝ))))
        simpa [w1, μ, IntegrableOn] using hs
      exact hwI.aestronglyMeasurable
    have hBaem : AEStronglyMeasurable (fun x => (BB x) ^ 2) μ := by
      -- BB = QQ + ω·SS with QQ, SS continuous and ω a.e.-strongly measurable
      let QQ : X N → ℝ := fun x => aQ ℓ j (aQ ℓ i Φ) x
      let SS : X N → ℝ := fun x => (aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x)
      let omx : X N → ℝ := fun x => Classical.choose h (x i - x j)
      have hom : AEStronglyMeasurable omx μ := by
        dsimp [omx, μ]
        simpa using (w0_diff_aem (N := N) (ℓ := ℓ) hℓ hij (w0 := Classical.choose h) (w0_spec h).2.lhs_integrable)
      have hQQc : Continuous QQ := by
        dsimp [QQ]
        exact aQ_continuous hℓ j (aQ_continuous hℓ i hΦc)
      have hSc : Continuous SS := by
        dsimp [SS]
        have h1 : Continuous (fun x : X N =>
            aP ℓ j (aP ℓ i Φ) x + (aP ℓ j (aQ ℓ i Φ) x + aQ ℓ j (aP ℓ i Φ) x)) :=
          (aP_continuous hℓ j (aP_continuous hℓ i hΦc)).add
            ((aP_continuous hℓ j (aQ_continuous hℓ i hΦc)).add
              (aQ_continuous hℓ j (aP_continuous hℓ i hΦc)))
        simpa [add_assoc] using h1
      have hBQQ : BB = fun x => QQ x + omx x * SS x := by
        funext x
        dsimp [BB, QQ, SS, omx]
        rfl
      have hBsm : AEStronglyMeasurable BB μ := by
        rw [hBQQ]
        exact (hQQc.aestronglyMeasurable.add (hom.mul hSc.aestronglyMeasurable))
      have hB2sm : AEStronglyMeasurable (fun x => BB x * BB x) μ := hBsm.mul hBsm
      simpa [pow_two] using hB2sm
    exact hBaem.mul hw1aem
  exact Integrable.mono' hBv haem hbnd


/-! ## q4-absorption lemmas (Session-146): the FS "absorb Q3 in Q4" step

* `q4_pair_absorbs_cross` — per pair, completing the square
  `½X² + 2AX = ½(X+2A)² − 2A²` (`A := P_iQ_jΦ`, `X := q4B(i,j)`,
  `w₁ := wPair(g₀) ≥ 0` a.e. via `w1_nonneg_ae_pair`):

  `½∫X²·w₁ + 2∫A·X·w₁ ≥ −2∫A²·w₁`   (per pair).

* `q4B_sq_w1_le_w_pair` — kernel comparison per pair
  `∫(q4B)²·w₁ ≤ ∫(q4B)²·wPair(v)`.

* `q4_absorbs_cross_pairs` — summed: `½Σ∫(q4B)²·w₁ ≤ q4word` (kernel
  comparison against q4word's `wPair(v)`-square) plus the per-pair absorption
  summed gives

  `q4word + 2·Σ_p∫(P_{p.1}Q_{p.2}Φ)·(q4B_p)·w₁ ≥ −2·Σ_p∫(P_{p.1}Q_{p.2}Φ)²·w₁`

  — combined with `q3word_expand` this produces the FS `eq:Q3+Q4CS` final
  form (next lemma `q3_q4_leftover`): `q3word + q4word ≥ −[PPQω-pair-sum] −
  [PQω-sum] − [QPω-sum] − [A²·w₁-mass]`.
-/
/-- **q4-square absorbs the q4B-cross (per pair, the FS "absorb Q3 in Q4"
step)**: with `A := P_iQ_jΦ`, `X := q4B(i,j)`, `w₁ := wPair(g₀) ≥ 0` a.e.,
completing the square `½X² + 2AX = ½(X+2A)² − 2A²` gives

`½∫X²·w₁ + 2∫A·X·w₁ ≥ −2∫A²·w₁`   (per pair `(i,j)`, `i ≠ j`). -/
lemma q4_pair_absorbs_cross {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (hv_memL1 : MemLp v 1)
    {i j : Fin N} (hij : i ≠ j) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (1 / 2) * (∫ x in abox N ℓ,
        (q4B ℓ (omC (Classical.choose h)) Φ (i, j) x) ^ 2 *
          wPair ℓ (g0 v h) (x i) (x j))
      + 2 * (∫ x in abox N ℓ,
          (aP ℓ i (aQ ℓ j Φ) x) * (q4B ℓ (omC (Classical.choose h)) Φ (i, j) x) *
            wPair ℓ (g0 v h) (x i) (x j))
    ≥ - 2 * (∫ x in abox N ℓ,
        (aP ℓ i (aQ ℓ j Φ) x) ^ 2 * wPair ℓ (g0 v h) (x i) (x j)) := by
  classical
  let A : X N → ℝ := fun x => aP ℓ i (aQ ℓ j Φ) x
  let BB : X N → ℝ := fun x => q4B ℓ (omC (Classical.choose h)) Φ (i, j) x
  let w1 : X N → ℝ := fun x => wPair ℓ (g0 v h) (x i) (x j)
  let S1 : ℝ := ∫ x in abox N ℓ, (BB x) ^ 2 * w1 x
  let S2 : ℝ := ∫ x in abox N ℓ, A x * BB x * w1 x
  let S3 : ℝ := ∫ x in abox N ℓ, (A x) ^ 2 * w1 x
  have hg0i : MeasureTheory.Integrable (g0 v h) := g0_integrable hR hv_supp h
  have hg0s : ∀ z : ℝ³, R ≤ ‖z‖ → g0 v h z = 0 := fun z hz => g0_zero_of_norm_ge hv_supp hz h
  have hAc : Continuous A := by
    dsimp [A]
    exact aP_continuous hℓ i (aQ_continuous hℓ j hΦc)
  have hA2w1 : IntegrableOn (fun x => (A x) ^ 2 * w1 x) (abox N ℓ) volume := by
    have h := integrableOn_slot_wPair hℓ hg0i hg0s hRℓ hij (S := fun x => (A x) ^ 2) (hAc.pow 2)
    simpa [A, w1] using h
  have hB2w1 : IntegrableOn (fun x => (BB x) ^ 2 * w1 x) (abox N ℓ) volume :=
    q4B_sq_w1_integrable hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1 hij hΦc
  -- integrability of A·BB·w1 by domination |A·BB| ≤ |A|·(|QQ|+|SS|) a.e. + |w1| ≤ wPair(v) a.e.
  have hABw1 : IntegrableOn (fun x => A x * BB x * w1 x) (abox N ℓ) volume := by
    let μ : Measure (X N) := volume.restrict (abox N ℓ)
    let QQ : X N → ℝ := fun x => aQ ℓ j (aQ ℓ i Φ) x
    let SS : X N → ℝ := fun x => (aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x)
    let omx : X N → ℝ := fun x => Classical.choose h (x i - x j)
    have hQQc : Continuous QQ := by
      dsimp [QQ]
      exact aQ_continuous hℓ j (aQ_continuous hℓ i hΦc)
    have hSc : Continuous SS := by
      dsimp [SS]
      have h1 : Continuous (fun x : X N =>
          aP ℓ j (aP ℓ i Φ) x + (aP ℓ j (aQ ℓ i Φ) x + aQ ℓ j (aP ℓ i Φ) x)) :=
        (aP_continuous hℓ j (aP_continuous hℓ i hΦc)).add
          ((aP_continuous hℓ j (aQ_continuous hℓ i hΦc)).add
            (aQ_continuous hℓ j (aP_continuous hℓ i hΦc)))
      simpa [add_assoc] using h1
    have hdom : IntegrableOn (fun x => |A x| * (|QQ x| + |SS x|) * wPair ℓ v (x i) (x j))
        (abox N ℓ) volume := by
      have hC : Continuous (fun x => |A x| * (|QQ x| + |SS x|)) :=
        (hAc.abs.mul (hQQc.abs.add hSc.abs))
      have hvzero : ∀ z : ℝ³, R ≤ ‖z‖ → v z = 0 := fun z hz => v_zero_of_norm_ge hv_supp hz
      simpa using (integrableOn_slot_wPair hℓ (v_integrable hv_memL1) hvzero hRℓ hij hC)
    have homxb : ∀ᵐ x ∂μ, |omx x| ≤ 1 := by
      dsimp [omx, μ]
      simpa using (w0_abs_le_one_box_ae (N := N) hℓ hR hv_nonneg hvrad hv_supp h hij)
    have hw1le : ∀ᵐ x ∂μ, |w1 x| ≤ wPair ℓ v (x i) (x j) := by
      have hle := w1_abs_le_w_ae (N := N) hℓ hR hv_nonneg hvrad hv_supp h hij
      filter_upwards [hle] with x hx
      simpa [w1] using hx
    have hBB : ∀ x : X N, BB x = QQ x + omx x * SS x := by
      intro x
      dsimp [QQ, SS, BB, omx]
      rfl
    have hbnd : ∀ᵐ x ∂μ, ‖A x * BB x * w1 x‖ ≤ |A x| * (|QQ x| + |SS x|) * wPair ℓ v (x i) (x j) := by
      filter_upwards [homxb, hw1le] with x hx1 hx2
      have hBBx : |BB x| ≤ |QQ x| + |SS x| := by
        rw [hBB x]
        calc
          |QQ x + omx x * SS x| ≤ |QQ x| + |omx x * SS x| := abs_add_le _ _
          _ = |QQ x| + |omx x| * |SS x| := by rw [abs_mul]
          _ ≤ |QQ x| + 1 * |SS x| := by
                have hm : |omx x| * |SS x| ≤ 1 * |SS x| :=
                  mul_le_mul_of_nonneg_right hx1 (abs_nonneg (SS x))
                linarith
          _ = |QQ x| + |SS x| := by ring
      calc
        ‖A x * BB x * w1 x‖ = |A x * BB x| * |w1 x| := by
            rw [Real.norm_eq_abs, abs_mul]
        _ = (|A x| * |BB x|) * |w1 x| := by rw [abs_mul]
        _ ≤ (|A x| * (|QQ x| + |SS x|)) * |w1 x| := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hBBx (abs_nonneg (A x))) (abs_nonneg (w1 x))
        _ ≤ (|A x| * (|QQ x| + |SS x|)) * wPair ℓ v (x i) (x j) := by
            exact mul_le_mul_of_nonneg_left hx2
              (mul_nonneg (abs_nonneg (A x)) (add_nonneg (abs_nonneg (QQ x)) (abs_nonneg (SS x))))
    have haem : AEStronglyMeasurable (fun x => A x * BB x * w1 x) μ := by
      have hom : AEStronglyMeasurable omx μ := by
        dsimp [omx, μ]
        simpa using (w0_diff_aem (N := N) (ℓ := ℓ) hℓ hij (w0 := Classical.choose h) (w0_spec h).2.lhs_integrable)
      have hBBfun : BB = (fun x : X N => QQ x + omx x * SS x) := by
        funext x
        exact hBB x
      have hBsm : AEStronglyMeasurable BB μ := by
        rw [hBBfun]
        exact (hQQc.aestronglyMeasurable.add (hom.mul hSc.aestronglyMeasurable))
      have hw1aem : AEStronglyMeasurable w1 μ := by
        have hwI : Integrable w1 μ := by
          have hs : IntegrableOn (fun x : X N => wPair ℓ (g0 v h) (x i) (x j)) (abox N ℓ) volume := by
            simpa using (integrableOn_slot_wPair hℓ hg0i hg0s hRℓ hij
              (S := fun _ : X N => (1 : ℝ)) (by fun_prop : Continuous (fun _ : X N => (1 : ℝ))))
          simpa [w1, μ, IntegrableOn] using hs
        exact hwI.aestronglyMeasurable
      exact (hAc.aestronglyMeasurable.mul hBsm).mul hw1aem
    exact Integrable.mono' hdom haem hbnd
  -- the three scalar-to-integral identities (no integrability needed)
  have h1eq : (1 / 2) * S1 = ∫ x in abox N ℓ, (1 / 2) * ((BB x) ^ 2 * w1 x) := by
    dsimp [S1]
    rw [← integral_const_mul]
  have h2eq : 2 * S2 = ∫ x in abox N ℓ, 2 * (A x * BB x * w1 x) := by
    dsimp [S2]
    rw [← integral_const_mul]
  have h3eq : 2 * S3 = ∫ x in abox N ℓ, 2 * ((A x) ^ 2 * w1 x) := by
    dsimp [S3]
    rw [← integral_const_mul]
  -- integrability of the three summands (shapes as produced by const_mul)
  have hc1 : IntegrableOn (fun x => (1 / 2) * ((BB x) ^ 2 * w1 x)) (abox N ℓ) volume := by
    change Integrable (fun x => (1 / 2) * ((BB x) ^ 2 * w1 x)) (volume.restrict (abox N ℓ))
    exact hB2w1.const_mul (1 / 2)
  have hc2 : IntegrableOn (fun x => 2 * (A x * BB x * w1 x)) (abox N ℓ) volume := by
    change Integrable (fun x => 2 * (A x * BB x * w1 x)) (volume.restrict (abox N ℓ))
    exact hABw1.const_mul 2
  have hc3 : IntegrableOn (fun x => 2 * ((A x) ^ 2 * w1 x)) (abox N ℓ) volume := by
    change Integrable (fun x => 2 * ((A x) ^ 2 * w1 x)) (volume.restrict (abox N ℓ))
    exact hA2w1.const_mul 2
  have hc12 : IntegrableOn
      (fun x => (1 / 2) * ((BB x) ^ 2 * w1 x) + 2 * (A x * BB x * w1 x)) (abox N ℓ) volume := by
    change Integrable (fun x => (1 / 2) * ((BB x) ^ 2 * w1 x) + 2 * (A x * BB x * w1 x))
        (volume.restrict (abox N ℓ))
    have h1I : Integrable (fun x => (1 / 2) * ((BB x) ^ 2 * w1 x)) (volume.restrict (abox N ℓ)) := by
      simpa [IntegrableOn] using hc1
    have h2I : Integrable (fun x => 2 * (A x * BB x * w1 x)) (volume.restrict (abox N ℓ)) := by
      simpa [IntegrableOn] using hc2
    exact h1I.add h2I
  -- the integral of the pointwise sum equals the completing-square integral
  have hsq_eq : (∫ x in abox N ℓ,
        ((1 / 2) * ((BB x) ^ 2 * w1 x) + 2 * (A x * BB x * w1 x)) + 2 * ((A x) ^ 2 * w1 x))
      = ∫ x in abox N ℓ, (1 / 2) * ((BB x + 2 * A x) ^ 2) * w1 x := by
    apply integral_congr_ae
    refine ae_of_all _ (fun x => ?_)
    ring
  have hnonneg : 0 ≤ ∫ x in abox N ℓ, (1 / 2) * ((BB x + 2 * A x) ^ 2) * w1 x := by
    have hw1nn : ∀ᵐ x ∂(volume.restrict (abox N ℓ)), 0 ≤ w1 x := by
      simpa [w1] using (w1_nonneg_ae_pair (N := N) hℓ hR hv_nonneg hvrad hv_supp h hij)
    refine integral_nonneg_of_ae ?_
    filter_upwards [hw1nn] with x hx
    exact mul_nonneg (mul_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) (sq_nonneg (BB x + 2 * A x))) hx
  -- assemble
  have hmain : 0 ≤ (1 / 2) * S1 + 2 * S2 + 2 * S3 := by
    calc
      0 ≤ ∫ x in abox N ℓ, (1 / 2) * ((BB x + 2 * A x) ^ 2) * w1 x := hnonneg
      _ = (∫ x in abox N ℓ,
            ((1 / 2) * ((BB x) ^ 2 * w1 x) + 2 * (A x * BB x * w1 x)) + 2 * ((A x) ^ 2 * w1 x)) := hsq_eq.symm
      _ = (∫ x in abox N ℓ, (1 / 2) * ((BB x) ^ 2 * w1 x) + 2 * (A x * BB x * w1 x))
          + (∫ x in abox N ℓ, 2 * ((A x) ^ 2 * w1 x)) := by
          have h12I : Integrable (fun x =>
              (1 / 2) * ((BB x) ^ 2 * w1 x) + 2 * (A x * BB x * w1 x))
              (volume.restrict (abox N ℓ)) := by
            simpa [IntegrableOn] using hc12
          have h3I : Integrable (fun x => 2 * ((A x) ^ 2 * w1 x)) (volume.restrict (abox N ℓ)) := by
            simpa [IntegrableOn] using hc3
          rw [integral_add h12I h3I]
      _ = (∫ x in abox N ℓ, (1 / 2) * ((BB x) ^ 2 * w1 x))
          + (∫ x in abox N ℓ, 2 * (A x * BB x * w1 x))
          + (∫ x in abox N ℓ, 2 * ((A x) ^ 2 * w1 x)) := by
          have h1I : Integrable (fun x => (1 / 2) * ((BB x) ^ 2 * w1 x))
              (volume.restrict (abox N ℓ)) := by
            simpa [IntegrableOn] using hc1
          have h2I : Integrable (fun x => 2 * (A x * BB x * w1 x)) (volume.restrict (abox N ℓ)) := by
            simpa [IntegrableOn] using hc2
          rw [integral_add h1I h2I]
      _ = (1 / 2) * S1 + 2 * S2 + 2 * S3 := by
          rw [h1eq, h2eq, h3eq]
  -- final: statement-goal ⟺ 0 ≤ (1/2)S1 + 2S2 + 2S3
  change (1 / 2) * S1 + 2 * S2 ≥ - 2 * S3
  nlinarith [hmain]

/-- **q4-square absorbs the q4B-cross at ¾ strength (per pair)**: completing
the square with coefficient `(3/8)` (`(3/8)X² + 2AX = (3/8)(X + 8A/3)² −
(8/3)A²`), `w₁ ≥ 0` a.e.,

`(3/8)∫X²·w₁ + 2∫A·X·w₁ ≥ −(8/3)∫A²·w₁`   (per pair `(i,j)`, `i ≠ j`).

This is `q4_pair_absorbs_cross` rebalanced to leave ¼ of `q4word` free for
q2's T4-bound in the all-Φ `pot_sharp_w1line` assembly. -/
lemma q4_pair_absorbs_cross_frac {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (hv_memL1 : MemLp v 1)
    {i j : Fin N} (hij : i ≠ j) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (3 / 8) * (∫ x in abox N ℓ,
        (q4B ℓ (omC (Classical.choose h)) Φ (i, j) x) ^ 2 *
          wPair ℓ (g0 v h) (x i) (x j))
      + 2 * (∫ x in abox N ℓ,
          (aP ℓ i (aQ ℓ j Φ) x) * (q4B ℓ (omC (Classical.choose h)) Φ (i, j) x) *
            wPair ℓ (g0 v h) (x i) (x j))
    ≥ - (8 / 3) * (∫ x in abox N ℓ,
        (aP ℓ i (aQ ℓ j Φ) x) ^ 2 * wPair ℓ (g0 v h) (x i) (x j)) := by
  classical
  let A : X N → ℝ := fun x => aP ℓ i (aQ ℓ j Φ) x
  let BB : X N → ℝ := fun x => q4B ℓ (omC (Classical.choose h)) Φ (i, j) x
  let w1 : X N → ℝ := fun x => wPair ℓ (g0 v h) (x i) (x j)
  let S1 : ℝ := ∫ x in abox N ℓ, (BB x) ^ 2 * w1 x
  let S2 : ℝ := ∫ x in abox N ℓ, A x * BB x * w1 x
  let S3 : ℝ := ∫ x in abox N ℓ, (A x) ^ 2 * w1 x
  have hg0i : MeasureTheory.Integrable (g0 v h) := g0_integrable hR hv_supp h
  have hg0s : ∀ z : ℝ³, R ≤ ‖z‖ → g0 v h z = 0 := fun z hz => g0_zero_of_norm_ge hv_supp hz h
  have hAc : Continuous A := by
    dsimp [A]
    exact aP_continuous hℓ i (aQ_continuous hℓ j hΦc)
  have hA2w1 : IntegrableOn (fun x => (A x) ^ 2 * w1 x) (abox N ℓ) volume := by
    have h := integrableOn_slot_wPair hℓ hg0i hg0s hRℓ hij (S := fun x => (A x) ^ 2) (hAc.pow 2)
    simpa [A, w1] using h
  have hB2w1 : IntegrableOn (fun x => (BB x) ^ 2 * w1 x) (abox N ℓ) volume :=
    q4B_sq_w1_integrable hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1 hij hΦc
  -- integrability of A·BB·w1 by domination |A·BB| ≤ |A|·(|QQ|+|SS|) a.e. + |w1| ≤ wPair(v) a.e.
  have hABw1 : IntegrableOn (fun x => A x * BB x * w1 x) (abox N ℓ) volume := by
    let μ : Measure (X N) := volume.restrict (abox N ℓ)
    let QQ : X N → ℝ := fun x => aQ ℓ j (aQ ℓ i Φ) x
    let SS : X N → ℝ := fun x => (aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x)
    let omx : X N → ℝ := fun x => Classical.choose h (x i - x j)
    have hQQc : Continuous QQ := by
      dsimp [QQ]
      exact aQ_continuous hℓ j (aQ_continuous hℓ i hΦc)
    have hSc : Continuous SS := by
      dsimp [SS]
      have h1 : Continuous (fun x : X N =>
          aP ℓ j (aP ℓ i Φ) x + (aP ℓ j (aQ ℓ i Φ) x + aQ ℓ j (aP ℓ i Φ) x)) :=
        (aP_continuous hℓ j (aP_continuous hℓ i hΦc)).add
          ((aP_continuous hℓ j (aQ_continuous hℓ i hΦc)).add
            (aQ_continuous hℓ j (aP_continuous hℓ i hΦc)))
      simpa [add_assoc] using h1
    have hdom : IntegrableOn (fun x => |A x| * (|QQ x| + |SS x|) * wPair ℓ v (x i) (x j))
        (abox N ℓ) volume := by
      have hC : Continuous (fun x => |A x| * (|QQ x| + |SS x|)) :=
        (hAc.abs.mul (hQQc.abs.add hSc.abs))
      have hvzero : ∀ z : ℝ³, R ≤ ‖z‖ → v z = 0 := fun z hz => v_zero_of_norm_ge hv_supp hz
      simpa using (integrableOn_slot_wPair hℓ (v_integrable hv_memL1) hvzero hRℓ hij hC)
    have homxb : ∀ᵐ x ∂μ, |omx x| ≤ 1 := by
      dsimp [omx, μ]
      simpa using (w0_abs_le_one_box_ae (N := N) hℓ hR hv_nonneg hvrad hv_supp h hij)
    have hw1le : ∀ᵐ x ∂μ, |w1 x| ≤ wPair ℓ v (x i) (x j) := by
      have hle := w1_abs_le_w_ae (N := N) hℓ hR hv_nonneg hvrad hv_supp h hij
      filter_upwards [hle] with x hx
      simpa [w1] using hx
    have hBB : ∀ x : X N, BB x = QQ x + omx x * SS x := by
      intro x
      dsimp [QQ, SS, BB, omx]
      rfl
    have hbnd : ∀ᵐ x ∂μ, ‖A x * BB x * w1 x‖ ≤ |A x| * (|QQ x| + |SS x|) * wPair ℓ v (x i) (x j) := by
      filter_upwards [homxb, hw1le] with x hx1 hx2
      have hBBx : |BB x| ≤ |QQ x| + |SS x| := by
        rw [hBB x]
        calc
          |QQ x + omx x * SS x| ≤ |QQ x| + |omx x * SS x| := abs_add_le _ _
          _ = |QQ x| + |omx x| * |SS x| := by rw [abs_mul]
          _ ≤ |QQ x| + 1 * |SS x| := by
                have hm : |omx x| * |SS x| ≤ 1 * |SS x| :=
                  mul_le_mul_of_nonneg_right hx1 (abs_nonneg (SS x))
                linarith
          _ = |QQ x| + |SS x| := by ring
      calc
        ‖A x * BB x * w1 x‖ = |A x * BB x| * |w1 x| := by
            rw [Real.norm_eq_abs, abs_mul]
        _ = (|A x| * |BB x|) * |w1 x| := by rw [abs_mul]
        _ ≤ (|A x| * (|QQ x| + |SS x|)) * |w1 x| := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hBBx (abs_nonneg (A x))) (abs_nonneg (w1 x))
        _ ≤ (|A x| * (|QQ x| + |SS x|)) * wPair ℓ v (x i) (x j) := by
            exact mul_le_mul_of_nonneg_left hx2
              (mul_nonneg (abs_nonneg (A x)) (add_nonneg (abs_nonneg (QQ x)) (abs_nonneg (SS x))))
    have haem : AEStronglyMeasurable (fun x => A x * BB x * w1 x) μ := by
      have hom : AEStronglyMeasurable omx μ := by
        dsimp [omx, μ]
        simpa using (w0_diff_aem (N := N) (ℓ := ℓ) hℓ hij (w0 := Classical.choose h) (w0_spec h).2.lhs_integrable)
      have hBBfun : BB = (fun x : X N => QQ x + omx x * SS x) := by
        funext x
        exact hBB x
      have hBsm : AEStronglyMeasurable BB μ := by
        rw [hBBfun]
        exact (hQQc.aestronglyMeasurable.add (hom.mul hSc.aestronglyMeasurable))
      have hw1aem : AEStronglyMeasurable w1 μ := by
        have hwI : Integrable w1 μ := by
          have hs : IntegrableOn (fun x : X N => wPair ℓ (g0 v h) (x i) (x j)) (abox N ℓ) volume := by
            simpa using (integrableOn_slot_wPair hℓ hg0i hg0s hRℓ hij
              (S := fun _ : X N => (1 : ℝ)) (by fun_prop : Continuous (fun _ : X N => (1 : ℝ))))
          simpa [w1, μ, IntegrableOn] using hs
        exact hwI.aestronglyMeasurable
      exact (hAc.aestronglyMeasurable.mul hBsm).mul hw1aem
    exact Integrable.mono' hdom haem hbnd
  -- the three scalar-to-integral identities (no integrability needed)
  have h1eq : (3 / 8) * S1 = ∫ x in abox N ℓ, (3 / 8) * ((BB x) ^ 2 * w1 x) := by
    dsimp [S1]
    rw [← integral_const_mul]
  have h2eq : 2 * S2 = ∫ x in abox N ℓ, 2 * (A x * BB x * w1 x) := by
    dsimp [S2]
    rw [← integral_const_mul]
  have h3eq : (8 / 3) * S3 = ∫ x in abox N ℓ, (8 / 3) * ((A x) ^ 2 * w1 x) := by
    dsimp [S3]
    rw [← integral_const_mul]
  -- integrability of the three summands (shapes as produced by const_mul)
  have hc1 : IntegrableOn (fun x => (3 / 8) * ((BB x) ^ 2 * w1 x)) (abox N ℓ) volume := by
    change Integrable (fun x => (3 / 8) * ((BB x) ^ 2 * w1 x)) (volume.restrict (abox N ℓ))
    exact hB2w1.const_mul (3 / 8)
  have hc2 : IntegrableOn (fun x => 2 * (A x * BB x * w1 x)) (abox N ℓ) volume := by
    change Integrable (fun x => 2 * (A x * BB x * w1 x)) (volume.restrict (abox N ℓ))
    exact hABw1.const_mul 2
  have hc3 : IntegrableOn (fun x => (8 / 3) * ((A x) ^ 2 * w1 x)) (abox N ℓ) volume := by
    change Integrable (fun x => (8 / 3) * ((A x) ^ 2 * w1 x)) (volume.restrict (abox N ℓ))
    exact hA2w1.const_mul (8 / 3)
  have hc12 : IntegrableOn
      (fun x => (3 / 8) * ((BB x) ^ 2 * w1 x) + 2 * (A x * BB x * w1 x)) (abox N ℓ) volume := by
    change Integrable (fun x => (3 / 8) * ((BB x) ^ 2 * w1 x) + 2 * (A x * BB x * w1 x))
        (volume.restrict (abox N ℓ))
    have h1I : Integrable (fun x => (3 / 8) * ((BB x) ^ 2 * w1 x)) (volume.restrict (abox N ℓ)) := by
      simpa [IntegrableOn] using hc1
    have h2I : Integrable (fun x => 2 * (A x * BB x * w1 x)) (volume.restrict (abox N ℓ)) := by
      simpa [IntegrableOn] using hc2
    exact h1I.add h2I
  -- the integral of the pointwise sum equals the completing-square integral
  have hsq_eq : (∫ x in abox N ℓ,
        ((3 / 8) * ((BB x) ^ 2 * w1 x) + 2 * (A x * BB x * w1 x)) + (8 / 3) * ((A x) ^ 2 * w1 x))
      = ∫ x in abox N ℓ, (3 / 8) * ((BB x + (8 / 3) * A x) ^ 2) * w1 x := by
    apply integral_congr_ae
    refine ae_of_all _ (fun x => ?_)
    ring
  have hnonneg : 0 ≤ ∫ x in abox N ℓ, (3 / 8) * ((BB x + (8 / 3) * A x) ^ 2) * w1 x := by
    have hw1nn : ∀ᵐ x ∂(volume.restrict (abox N ℓ)), 0 ≤ w1 x := by
      simpa [w1] using (w1_nonneg_ae_pair (N := N) hℓ hR hv_nonneg hvrad hv_supp h hij)
    refine integral_nonneg_of_ae ?_
    filter_upwards [hw1nn] with x hx
    exact mul_nonneg (mul_nonneg (by norm_num : 0 ≤ (3 / 8 : ℝ)) (sq_nonneg (BB x + (8 / 3) * A x))) hx
  -- assemble
  have hmain : 0 ≤ (3 / 8) * S1 + 2 * S2 + (8 / 3) * S3 := by
    calc
      0 ≤ ∫ x in abox N ℓ, (3 / 8) * ((BB x + (8 / 3) * A x) ^ 2) * w1 x := hnonneg
      _ = (∫ x in abox N ℓ,
            ((3 / 8) * ((BB x) ^ 2 * w1 x) + 2 * (A x * BB x * w1 x)) + (8 / 3) * ((A x) ^ 2 * w1 x)) := hsq_eq.symm
      _ = (∫ x in abox N ℓ, (3 / 8) * ((BB x) ^ 2 * w1 x) + 2 * (A x * BB x * w1 x))
          + (∫ x in abox N ℓ, (8 / 3) * ((A x) ^ 2 * w1 x)) := by
          have h12I : Integrable (fun x =>
              (3 / 8) * ((BB x) ^ 2 * w1 x) + 2 * (A x * BB x * w1 x))
              (volume.restrict (abox N ℓ)) := by
            simpa [IntegrableOn] using hc12
          have h3I : Integrable (fun x => (8 / 3) * ((A x) ^ 2 * w1 x)) (volume.restrict (abox N ℓ)) := by
            simpa [IntegrableOn] using hc3
          rw [integral_add h12I h3I]
      _ = (∫ x in abox N ℓ, (3 / 8) * ((BB x) ^ 2 * w1 x))
          + (∫ x in abox N ℓ, 2 * (A x * BB x * w1 x))
          + (∫ x in abox N ℓ, (8 / 3) * ((A x) ^ 2 * w1 x)) := by
          have h1I : Integrable (fun x => (3 / 8) * ((BB x) ^ 2 * w1 x))
              (volume.restrict (abox N ℓ)) := by
            simpa [IntegrableOn] using hc1
          have h2I : Integrable (fun x => 2 * (A x * BB x * w1 x)) (volume.restrict (abox N ℓ)) := by
            simpa [IntegrableOn] using hc2
          rw [integral_add h1I h2I]
      _ = (3 / 8) * S1 + 2 * S2 + (8 / 3) * S3 := by
          rw [h1eq, h2eq, h3eq]
  -- final: statement-goal ⟺ 0 ≤ (1/2)S1 + 2S2 + 2S3
  change (3 / 8) * S1 + 2 * S2 ≥ - (8 / 3) * S3
  nlinarith [hmain]
/-- **Kernel comparison, per pair**: `∫(q4B)²·w₁ ≤ ∫(q4B)²·wPair(v)`
(`w₁ := wPair(g₀) ≤ wPair(v)` a.e. since `g₀ ≤ v`, and `(q4B)² ≥ 0`). -/
lemma q4B_sq_w1_le_w_pair {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (hv_memL1 : MemLp v 1)
    {i j : Fin N} (hij : i ≠ j) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∫ x in abox N ℓ,
        (q4B ℓ (omC (Classical.choose h)) Φ (i, j) x) ^ 2 * wPair ℓ (g0 v h) (x i) (x j))
      ≤ (∫ x in abox N ℓ,
        (q4B ℓ (omC (Classical.choose h)) Φ (i, j) x) ^ 2 * wPair ℓ v (x i) (x j)) := by
  classical
  let BB : X N → ℝ := fun x => q4B ℓ (omC (Classical.choose h)) Φ (i, j) x
  let w1 : X N → ℝ := fun x => wPair ℓ (g0 v h) (x i) (x j)
  have hL : IntegrableOn (fun x => (BB x) ^ 2 * w1 x) (abox N ℓ) volume := by
    have hi := q4B_sq_w1_integrable hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1 hij hΦc
    simpa [BB, w1] using hi
  have hRv : IntegrableOn (fun x => (BB x) ^ 2 * wPair ℓ v (x i) (x j)) (abox N ℓ) volume := by
    have hi := q4B_sq_w_integrable hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1 hij hΦc
    simpa [BB] using hi
  have hmono : ∀ᵐ x ∂(volume.restrict (abox N ℓ)),
      (BB x) ^ 2 * w1 x ≤ (BB x) ^ 2 * wPair ℓ v (x i) (x j) := by
    have hw1nn := w1_nonneg_ae_pair (N := N) hℓ hR hv_nonneg hvrad hv_supp h hij
    have hle := w1_abs_le_w_ae (N := N) hℓ hR hv_nonneg hvrad hv_supp h hij
    filter_upwards [hw1nn, hle] with x hxnn hxle
    have hw1le : w1 x ≤ wPair ℓ v (x i) (x j) := by
      have habs : |w1 x| ≤ wPair ℓ v (x i) (x j) := by simpa [w1] using hxle
      rw [abs_of_nonneg hxnn] at habs
      exact habs
    exact mul_le_mul_of_nonneg_left hw1le (sq_nonneg (BB x))
  exact integral_mono_ae hL hRv hmono

/-- **q4 absorbs the q4B-cross, `pairSet`-summed** (FS "absorb Q3 in Q4"):
from `½Σ∫(q4B)²·w₁ ≤ q4word` (kernel comparison) and the per-pair
completing-square absorption summed over pairs,

`q4word(ℓ, wPairC(v), omC w₀)Φ + 2·Σ_p∫(P_{p.1}Q_{p.2}Φ)·(q4B_p)·w₁
 ≥ − 2·Σ_p∫(P_{p.1}Q_{p.2}Φ)²·w₁`   (`w₁ := wPair(g₀)`). -/
lemma q4_absorbs_cross_pairs {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (hv_memL1 : MemLp v 1)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ
      + 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (q4B ℓ (omC (Classical.choose h)) Φ p x) *
            wPair ℓ (g0 v h) (x p.1) (x p.2))
    ≥ - 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2)) := by
  classical
  let w1 : X N × (Fin N × Fin N) → ℝ := fun _ => (0 : ℝ)  -- unused placeholder to appease nothing
  have hper : ∀ p : Fin N × Fin N, p ∈ pairSet N →
      (1 / 2) * (∫ x in abox N ℓ,
          (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2))
        + 2 * (∫ x in abox N ℓ,
            (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (q4B ℓ (omC (Classical.choose h)) Φ p x) *
              wPair ℓ (g0 v h) (x p.1) (x p.2))
      ≥ - 2 * (∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2)) := by
    intro p hp
    have hpij : p.1 ≠ p.2 := by
      simpa [pairSet] using (Finset.mem_filter.mp hp).2
    exact q4_pair_absorbs_cross hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1
      (i := p.1) (j := p.2) hpij hΦc
  have hq4 : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wPair ℓ v (x p.1) (x p.2))
      = 2 * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
    unfold q4word
    simp [wPairC]
  have hcmp : (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2))
      ≤ q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
    have hsumle : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2))
        ≤ (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wPair ℓ v (x p.1) (x p.2)) := by
      refine Finset.sum_le_sum (fun p hp => ?_)
      have hpij : p.1 ≠ p.2 := by
        simpa [pairSet] using (Finset.mem_filter.mp hp).2
      exact q4B_sq_w1_le_w_pair hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1
        (i := p.1) (j := p.2) hpij hΦc
    have hle2 : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2))
        ≤ 2 * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
      rw [← hq4]
      exact hsumle
    have hhalf : 0 ≤ (1 / 2 : ℝ) := by norm_num
    calc
      (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2))
          ≤ (1 / 2) * (2 * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ) := by
              exact mul_le_mul_of_nonneg_left hle2 hhalf
      _ = q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by ring
  -- sum the per-pair absorption
  have hsumabs : (∑ p ∈ pairSet N,
        ((1 / 2) * (∫ x in abox N ℓ,
            (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2))
          + 2 * (∫ x in abox N ℓ,
              (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (q4B ℓ (omC (Classical.choose h)) Φ p x) *
                wPair ℓ (g0 v h) (x p.1) (x p.2))))
      ≥ (∑ p ∈ pairSet N,
          - 2 * (∫ x in abox N ℓ,
              (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2))) := by
    exact Finset.sum_le_sum (fun p hp => hper p hp)
  have hsplit : (∑ p ∈ pairSet N,
        ((1 / 2) * (∫ x in abox N ℓ,
            (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2))
          + 2 * (∫ x in abox N ℓ,
              (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (q4B ℓ (omC (Classical.choose h)) Φ p x) *
                wPair ℓ (g0 v h) (x p.1) (x p.2))))
      = (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2))
        + 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (q4B ℓ (omC (Classical.choose h)) Φ p x) *
              wPair ℓ (g0 v h) (x p.1) (x p.2)) := by
    simp [Finset.sum_add_distrib, Finset.mul_sum]
  have hneg : (∑ p ∈ pairSet N,
          - 2 * (∫ x in abox N ℓ,
              (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2)))
      = - 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2)) := by
    simp [Finset.mul_sum]
  have hsumabs' : (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2))
        + 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (q4B ℓ (omC (Classical.choose h)) Φ p x) *
              wPair ℓ (g0 v h) (x p.1) (x p.2))
      ≥ - 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2)) := by
    rw [← hsplit]
    rw [← hneg]
    exact hsumabs
  nlinarith [hcmp, hsumabs']

/-! ## eq:Q3+Q4CS final form + the joint q1+q3+q4 assembly (Session-146)

* `q3_q4_leftover` — the FS `eq:Q3+Q4CS` final form, per state:
  from `q3word_expand` (exact) and `q4_absorbs_cross_pairs`,

  `q3word + q4word ≥ −[PPQω-pair-sum] − [PQω-sum] − [QPω-sum]
                      − 2·Σ_p∫(P_{p.1}Q_{p.2}Φ)²·w₁`

  (PPQω/PQω/QPω with the `w₁ω := wPairC(g₀ω₀)` kernel; the A²-mass with
  `w₁`).  The PPQω-pair-sum is the q1-w₁ω cancellation partner; the
  PQω/QPω/A²-masses are the `n₊`-type terms FS absorb by the second
  Cauchy–Schwarz (`|ω₀| ≤ 1`) and `eq:BQwQleq`.

* `q1_q3_q4_assembly` — the JOINT assembly (FS `lm:appinteractionestimate`
  Steps 2–3): `q1word = w₁-line + w₁ω-line − 2μ·OB₁` (exact,
  `q1word_eq_q1n0_split`), the w₁ω-line equals the PPQω-pair-sum
  (`q1w0_pair_sum_eq_sandwich_n0` + `q3_PPQw_eq_q1_pair_sum_w0`), so with
  `q3_q4_leftover` the PPQω-terms CANCEL EXACTLY:

  `q1word + q3word + q4word ≥ w₁-line − 2μ·OB₁ − [PQω] − [QPω] − [A²-mass]`

  where the w₁-line `2(ℓ³)⁻¹Σ_i∫(P_iΦ)·f₁(x_i)·Q_i((Σ_{j≠i}P_j)Φ)` is the
  `(n₀/V − μ)`-weighted w₁-cross (the Step-4 CS input producing A₀'s
  `−¼(μ−u−1/V)²·8πaV`), `OB₁ := Σ_i∫(Q_iΦ)(P_iΦ)·f₁(x_i)`.
-/
/-- **eq:Q3+Q4CS final form (per state)**: from `q3word_expand` (exact) and
`q4_absorbs_cross_pairs` (q4's square absorbs the q4B-cross),

`q3word(ℓ, w₁)Φ + q4word(ℓ, wPairC(v), omC w₀)Φ
 ≥ − [PPQω-pair-sum] − [PQω-sum] − [QPω-sum] − 2·Σ_p∫(P_{p.1}Q_{p.2}Φ)²·w₁`

where all sums have kernel `w₁ω := wPairC(g₀ω₀)` except the last (`w₁`):
the PPQω-pair-sum is the q1-w₁ω cancellation partner
(`q1_pair_part_sandwich_w0` / `q1w0_pair_sum_eq_sandwich_n0`), and the
PQω/QPω/A²-masses are the `n₊`-type terms FS absorb by the second
Cauchy–Schwarz (`|ω₀| ≤ 1`) and `eq:BQwQleq`. -/
lemma q3_q4_leftover {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (hv_memL1 : MemLp v 1)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ
      + q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ
    ≥ - 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aP ℓ p.1 Φ) x) *
            wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))
      - 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aQ ℓ p.1 Φ) x) *
            wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))
      - 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aP ℓ p.1 Φ) x) *
            wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))
      - 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2)) := by
  classical
  let X1 : ℝ := 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (q4B ℓ (omC (Classical.choose h)) Φ p x) *
        wPair ℓ (g0 v h) (x p.1) (x p.2))
  let X2 : ℝ := 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aP ℓ p.1 Φ) x) *
        wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))
  let X3 : ℝ := 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aQ ℓ p.1 Φ) x) *
        wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))
  let X4 : ℝ := 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aP ℓ p.1 Φ) x) *
        wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))
  let A2 : ℝ := 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2))
  have hq3 := q3word_expand hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1 hΦc
  have habs := q4_absorbs_cross_pairs hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1 hΦc
  have hq3' : q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ = X1 - X2 - X3 - X4 := by
    simpa [X1, X2, X3, X4] using hq3
  have habs' : q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ + X1 ≥ - A2 := by
    simpa [X1, A2] using habs
  have hgoal : q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ
        + q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ
      ≥ - X2 - X3 - X4 - A2 := by
    rw [hq3']
    nlinarith [habs']
  simpa [X1, X2, X3, X4, A2] using hgoal


/-- **Joint q1+q3+q4 assembly (the w₁ω-cancellation)**: from
`q1word_eq_q1n0_split` (q1word = w₁-line + w₁ω-line − 2μ·OB₁, exact),
`q1w0_pair_sum_eq_sandwich_n0` + `q3_PPQw_eq_q1_pair_sum_w0` (the w₁ω-line
equals q3's PPQω-pair-sum), and `q3_q4_leftover` (q3+q4 ≥ −PPQω − PQω − QPω
− A²-mass), the PPQω-terms cancel exactly, leaving q1's `(n₀/V − μ)`-w₁-line
(the Step-4 CS input producing A₀'s `−¼(μ−u−1/V)²·8πaV`) minus the mass
terms:

`q1word + q3word + q4word ≥ w₁-line − 2μ·OB₁ − [PQω-sum] − [QPω-sum] − [A²-mass]`

where the w₁-line is `2(ℓ³)⁻¹Σ_i∫(P_iΦ)·f₁(x_i)·Q_i((Σ_{j≠i}P_j)Φ)`,
`f₁ := w1Fibre(wPairC(g₀))`, `OB₁ := Σ_i∫(Q_iΦ)(P_iΦ)·f₁(x_i)`. -/
lemma q1_q3_q4_assembly {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (hv_memL1 : MemLp v 1)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    q1word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ
      + q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ
      + q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ
    ≥ 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
        (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)) *
          (aQ ℓ i (fun y : X N => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0))) x)
      - 2 * μ * (∑ i : Fin N, ∫ x in abox N ℓ,
          (aQ ℓ i Φ x) * (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)))
      - 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aQ ℓ p.1 Φ) x) *
            wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))
      - 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aP ℓ p.1 Φ) x) *
            wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))
      - 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2)) := by
  classical
  let L1 : ℝ := 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
      (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)) *
        (aQ ℓ i (fun y : X N => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0))) x)
  let L2 : ℝ := 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
      (aP ℓ i Φ x) *
        (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i)) *
        (aQ ℓ i (fun y : X N => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0))) x)
  let OB : ℝ := ∑ i : Fin N, ∫ x in abox N ℓ,
      (aQ ℓ i Φ x) * (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i))
  let P : ℝ := 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.1 (aP ℓ p.2 Φ) x) *
        wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))
  let PPQ : ℝ := 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aP ℓ p.1 Φ) x) *
        wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))
  let PQw : ℝ := 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aQ ℓ p.1 Φ) x) *
        wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))
  let QPw : ℝ := 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aP ℓ p.1 Φ) x) *
        wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))
  let A2 : ℝ := 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2))
  have hq1 := q1word_eq_q1n0_split (N := N) (μ := μ) hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
  have hq1' : q1word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ
      = L1 + L2 - 2 * μ * OB := by
    simpa [L1, L2, OB] using hq1
  have hq34 := q3_q4_leftover hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1 hΦc
  have hq34' : q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ
      + q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ
    ≥ - PPQ - PQw - QPw - A2 := by
    simpa [PPQ, PQw, QPw, A2] using hq34
  have hL2P := q1w0_pair_sum_eq_sandwich_n0 hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
  have hL2P' : L2 = P := by
    simpa [L2, P, wPairC] using hL2P.symm
  have hPPQ := q3_PPQw_eq_q1_pair_sum_w0 (N := N) hℓ (v := v) h hΦc
  have hPPQ' : PPQ = P := by
    simpa [PPQ, P, wPairC] using hPPQ
  have hgoal : q1word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ
        + q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ
        + q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ
      ≥ L1 - 2 * μ * OB - PQw - QPw - A2 := by
    rw [hq1']
    nlinarith [hq34', hL2P', hPPQ']
  simpa [L1, OB, PQw, QPw, A2] using hgoal

/-! ## Mass-tail of the q3/q4 leftovers (Session-147)

* `w1w_abs_le_w1_pair_ae` — `|w₁ω| = |wPair(g₀·ω₀)| ≤ |w₁| = wPair(g₀)` a.e.
  along a pair difference (`|ω₀| ≤ 1` a.e., `g₀ ≥ 0` a.e.,
  `wPair_abs_le_pair`).
* `w1w_cross_pair_abs_le` — per-pair AM–GM: for continuous `f,g`,
  `|2·∫ f·(g·w₁ω)| ≤ ∫ f²·|w₁| + ∫ g²·|w₁|`.
* `q3_PQw_sum_abs_le` — `|PQω| ≤ 2·C₁·(ℓ³)⁻¹·N̂·n₊` (`C₁ := fsqC1(a v)`),
  `PQω := 2·Σ_p∫(P_{p.1}Q_{p.2}Φ)·(P_{p.2}Q_{p.1}Φ)·w₁ω`.
* `q3_QPw_sum_abs_le` — same for `QPω` (second factor `Q_{p.2}P_{p.1}Φ`).
* `q3_A2_sum_le` — `0 ≤ A2 ≤ 2·C₁·(ℓ³)⁻¹·N̂·n₊`,
  `A2 := 2·Σ_p∫(P_{p.1}Q_{p.2}Φ)²·w₁`.

Together these bound the `[PQω] − [QPω] − [A²]`-tail of
`q1_q3_q4_assembly` / `q3_q4_leftover` by
`6·C₁·(ℓ³)⁻¹·N̂·cnPlus` (next lemma `q1_q3_q4_mass`), so the joint
assembly closes at the all-Φ level as `q1+q3+q4 ≥ w₁-line − 2μ·OB₁ −
6·C₁·(ℓ³)⁻¹·N̂·n₊` — the input of the (windowed, c-number-layer) Step-4 CS.
-/
/-- `|w₁ω| = |wPair(g₀·ω₀)| ≤ |w₁| = wPair(g₀)` a.e. along a pair difference
(`|ω₀| ≤ 1` a.e., `g₀ ≥ 0` a.e., `wPair_abs_le_pair`). -/
lemma w1w_abs_le_w1_pair_ae {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ} {R : ℝ}
    (hR : 0 < R) (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    {i j : Fin N} (hij : i ≠ j) :
    ∀ᵐ x ∂(volume.restrict (abox N ℓ)),
      |wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x i) (x j)|
        ≤ wPair ℓ (g0 v h) (x i) (x j) := by
  classical
  have hspec := w0_spec h
  have hb := scattering_bounds_ae hR hv_nonneg hvrad hv_supp hspec.1 hspec.2
  have hg0nn : ∀ᵐ z : ℝ³, 0 ≤ g0 v h z := g0_nonneg_ae hR hv_nonneg hvrad hv_supp h
  have hw0le : ∀ᵐ z : ℝ³, |Classical.choose h z| ≤ 1 := by
    filter_upwards [hb.1, hb.2] with z hz0 hz1
    rw [abs_of_nonneg hz0]
    exact hz1
  have hmain : ∀ᵐ z : ℝ³, |g0 v h z * Classical.choose h z| ≤ g0 v h z := by
    filter_upwards [hg0nn, hw0le] with z hg0 hw0
    calc
      |g0 v h z * Classical.choose h z| = |g0 v h z| * |Classical.choose h z| := abs_mul _ _
      _ = g0 v h z * |Classical.choose h z| := by rw [abs_of_nonneg hg0]
      _ ≤ g0 v h z * 1 := mul_le_mul_of_nonneg_left hw0 hg0
      _ = g0 v h z := by ring
  have hpb := ae_pair_pullback (N := N) hℓ hij hmain
  filter_upwards [hpb] with x hx
  exact wPair_abs_le_pair (a := fun w : ℝ³ => g0 v h w * Classical.choose h w)
    (b := g0 v h) (x i) (x j) hx


/-- **Per-pair w₁ω-cross AM–GM (mass-tail atom)**: for continuous `f,g` and
`w₁ω := wPair(g₀ω₀)`-kernel, `|w₁ω| ≤ |w₁|` a.e. (`w1w_abs_le_w1_pair_ae`)
and `2|fg| ≤ f²+g²` give

`|2·∫ f·(g·w₁ω)| ≤ ∫ f²·|w₁| + ∫ g²·|w₁|`   (`w₁ := wPair(g₀)`, per pair). -/
lemma w1w_cross_pair_abs_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (_hv_memL1 : MemLp v 1)
    {i j : Fin N} (hij : i ≠ j) {f g : X N → ℝ}
    (hfc : Continuous f) (hgc : Continuous g) :
    |2 * (∫ x in abox N ℓ,
        f x * (g x * wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x i) (x j)))|
    ≤ (∫ x in abox N ℓ, (f x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)|)
      + (∫ x in abox N ℓ, (g x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)|) := by
  classical
  let hgw0 : ℝ³ → ℝ := fun w : ℝ³ => g0 v h w * Classical.choose h w
  have hgw0i : MeasureTheory.Integrable hgw0 := by
    simpa [hgw0] using (g0w0_integrable hR hv_nonneg hvrad hv_supp h)
  have hgw0s : ∀ z : ℝ³, R ≤ ‖z‖ → hgw0 z = 0 := by
    intro z hz
    have hgz : g0 v h z = 0 := g0_zero_of_norm_ge hv_supp hz h
    simp [hgw0, hgz]
  have hg0i : MeasureTheory.Integrable (g0 v h) := g0_integrable hR hv_supp h
  have hg0s : ∀ z : ℝ³, R ≤ ‖z‖ → g0 v h z = 0 := fun z hz => g0_zero_of_norm_ge hv_supp hz h
  have hcs := abs_integral_mul_mul_wPair_le_half hℓ hgw0i hgw0s hRℓ hij hfc hgc
  -- hcs : |∫ f·(g·wPair(hgw0))| ≤ ½∫f²|wPair(hgw0)| + ½∫g²|wPair(hgw0)|
  have hleW : ∀ᵐ x ∂(volume.restrict (abox N ℓ)),
      |wPair ℓ hgw0 (x i) (x j)| ≤ |wPair ℓ (g0 v h) (x i) (x j)| := by
    have hb := w1w_abs_le_w1_pair_ae (N := N) hℓ hR hv_nonneg hvrad hv_supp h hij
    have hnn := w1_nonneg_ae_pair (N := N) hℓ hR hv_nonneg hvrad hv_supp h hij
    filter_upwards [hb, hnn] with x hx hnnx
    rw [abs_of_nonneg hnnx]
    simpa [hgw0] using hx
  have hL1 : (∫ x in abox N ℓ, (f x) ^ 2 * |wPair ℓ hgw0 (x i) (x j)|)
      ≤ (∫ x in abox N ℓ, (f x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)|) := by
    have hLi : IntegrableOn (fun x => (f x) ^ 2 * |wPair ℓ hgw0 (x i) (x j)|)
        (abox N ℓ) volume := by
      simpa [hgw0] using (sq_slot_wPair_abs_integrable hℓ hgw0i hgw0s hRℓ hij hfc)
    have hRi : IntegrableOn (fun x => (f x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)|)
        (abox N ℓ) volume := by
      simpa using (sq_slot_wPair_abs_integrable hℓ hg0i hg0s hRℓ hij hfc)
    have hmono : ∀ᵐ x ∂(volume.restrict (abox N ℓ)),
        (f x) ^ 2 * |wPair ℓ hgw0 (x i) (x j)| ≤ (f x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)| := by
      filter_upwards [hleW] with x hx
      exact mul_le_mul_of_nonneg_left hx (sq_nonneg (f x))
    exact integral_mono_ae hLi hRi hmono
  have hL2 : (∫ x in abox N ℓ, (g x) ^ 2 * |wPair ℓ hgw0 (x i) (x j)|)
      ≤ (∫ x in abox N ℓ, (g x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)|) := by
    have hLi : IntegrableOn (fun x => (g x) ^ 2 * |wPair ℓ hgw0 (x i) (x j)|)
        (abox N ℓ) volume := by
      simpa [hgw0] using (sq_slot_wPair_abs_integrable hℓ hgw0i hgw0s hRℓ hij hgc)
    have hRi : IntegrableOn (fun x => (g x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)|)
        (abox N ℓ) volume := by
      simpa using (sq_slot_wPair_abs_integrable hℓ hg0i hg0s hRℓ hij hgc)
    have hmono : ∀ᵐ x ∂(volume.restrict (abox N ℓ)),
        (g x) ^ 2 * |wPair ℓ hgw0 (x i) (x j)| ≤ (g x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)| := by
      filter_upwards [hleW] with x hx
      exact mul_le_mul_of_nonneg_left hx (sq_nonneg (g x))
    exact integral_mono_ae hLi hRi hmono
  have htwo : |2 * (∫ x in abox N ℓ, f x * (g x * wPair ℓ hgw0 (x i) (x j)))|
      ≤ (∫ x in abox N ℓ, (f x) ^ 2 * |wPair ℓ hgw0 (x i) (x j)|)
        + (∫ x in abox N ℓ, (g x) ^ 2 * |wPair ℓ hgw0 (x i) (x j)|) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [hcs]
  calc
    |2 * (∫ x in abox N ℓ,
        f x * (g x * wPair ℓ hgw0 (x i) (x j)))|
        ≤ (∫ x in abox N ℓ, (f x) ^ 2 * |wPair ℓ hgw0 (x i) (x j)|)
          + (∫ x in abox N ℓ, (g x) ^ 2 * |wPair ℓ hgw0 (x i) (x j)|) := htwo
    _ ≤ (∫ x in abox N ℓ, (f x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)|)
        + (∫ x in abox N ℓ, (g x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)|) := by
        nlinarith [hL1, hL2]


/-- **PQω-sum absolute bound (mass-tail)**: with
`PQω := 2·Σ_p∫(P_{p.1}Q_{p.2}Φ)·(P_{p.2}Q_{p.1}Φ)·w₁ω` (`w₁ω := wPair(g₀ω₀)`),

`|PQω| ≤ 2·C₁·(ℓ³)⁻¹·N̂·n₊`,  `C₁ := fsqC1(a v)`. -/
lemma q3_PQw_sum_abs_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (hv_memL1 : MemLp v 1)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    |2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aQ ℓ p.1 Φ) x) *
          wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))|
    ≤ 2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
  classical
  let A : (Fin N × Fin N) → X N → ℝ := fun p x => aP ℓ p.1 (aQ ℓ p.2 Φ) x
  let B : (Fin N × Fin N) → X N → ℝ := fun p x => aP ℓ p.2 (aQ ℓ p.1 Φ) x
  let K : (Fin N × Fin N) → X N → ℝ := fun p x =>
      wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2)
  let w1 : (Fin N × Fin N) → X N → ℝ := fun p x =>
      |wPair ℓ (g0 v h) (x p.1) (x p.2)|
  have hper : ∀ p : Fin N × Fin N, p ∈ pairSet N →
      |2 * (∫ x in abox N ℓ, (A p x * B p x) * K p x)|
      ≤ (∫ x in abox N ℓ, (A p x) ^ 2 * w1 p x)
        + (∫ x in abox N ℓ, (B p x) ^ 2 * w1 p x) := by
    intro p hp
    have hpij : p.1 ≠ p.2 := by
      simpa [pairSet] using (Finset.mem_filter.mp hp).2
    have hc1 : Continuous (A p) := by
      dsimp [A]
      exact aP_continuous hℓ p.1 (aQ_continuous hℓ p.2 hΦc)
    have hc2 : Continuous (B p) := by
      dsimp [B]
      exact aP_continuous hℓ p.2 (aQ_continuous hℓ p.1 hΦc)
    have h1 := w1w_cross_pair_abs_le hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1
      (i := p.1) (j := p.2) hpij hc1 hc2
    have hcong : (∫ x in abox N ℓ, (A p x * B p x) * K p x)
        = (∫ x in abox N ℓ, A p x * (B p x * K p x)) := by
      apply integral_congr_ae
      refine ae_of_all _ (fun x => ?_)
      ring
    rw [← hcong] at h1
    simpa [K, w1] using h1
  have hsumle : (∑ p ∈ pairSet N, |2 * (∫ x in abox N ℓ, (A p x * B p x) * K p x)|)
      ≤ (∑ p ∈ pairSet N,
          ((∫ x in abox N ℓ, (A p x) ^ 2 * w1 p x)
            + (∫ x in abox N ℓ, (B p x) ^ 2 * w1 p x))) := by
    exact Finset.sum_le_sum (fun p hp => hper p hp)
  have hmain : |∑ p ∈ pairSet N, 2 * (∫ x in abox N ℓ, (A p x * B p x) * K p x)|
      ≤ (∑ p ∈ pairSet N, |2 * (∫ x in abox N ℓ, (A p x * B p x) * K p x)|) := by
    simpa using (Finset.abs_sum_le_sum_abs (s := pairSet N)
      (f := fun p : Fin N × Fin N => 2 * (∫ x in abox N ℓ, (A p x * B p x) * K p x)))
  have hA : (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (A p x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
      ≤ (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
    have hmm := pq_w1_mass_le_cnPlus hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
    simpa [A, wPairC] using hmm
  have hB : (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (B p x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
      ≤ (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
    have hmm := pq_w1_mass_swap_le_cnPlus hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
    simpa [B, wPairC] using hmm
  have hA1 : (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (A p x) ^ 2 * w1 p x)
      ≤ (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
    simpa [w1] using hA
  have hB1 : (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (B p x) ^ 2 * w1 p x)
      ≤ (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
    simpa [w1] using hB
  have hAB : (∑ p ∈ pairSet N,
          ((∫ x in abox N ℓ, (A p x) ^ 2 * w1 p x)
            + (∫ x in abox N ℓ, (B p x) ^ 2 * w1 p x)))
      ≤ 2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
    rw [Finset.sum_add_distrib]
    nlinarith [hA1, hB1]
  calc
    |2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aQ ℓ p.1 Φ) x) *
          wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))|
        = |2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (A p x * B p x) * K p x)| := by
            simp [A, B, K]
    _ = |∑ p ∈ pairSet N, 2 * (∫ x in abox N ℓ, (A p x * B p x) * K p x)| := by
            rw [Finset.mul_sum]
    _ ≤ (∑ p ∈ pairSet N, |2 * (∫ x in abox N ℓ, (A p x * B p x) * K p x)|) := hmain
    _ ≤ (∑ p ∈ pairSet N,
          ((∫ x in abox N ℓ, (A p x) ^ 2 * w1 p x)
            + (∫ x in abox N ℓ, (B p x) ^ 2 * w1 p x))) := hsumle
    _ ≤ 2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := hAB

lemma q3_QPw_sum_abs_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (hv_memL1 : MemLp v 1)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    |2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aP ℓ p.1 Φ) x) *
          wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))|
    ≤ 2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
  classical
  let A : (Fin N × Fin N) → X N → ℝ := fun p x => aP ℓ p.1 (aQ ℓ p.2 Φ) x
  let B : (Fin N × Fin N) → X N → ℝ := fun p x => aQ ℓ p.2 (aP ℓ p.1 Φ) x
  let K : (Fin N × Fin N) → X N → ℝ := fun p x =>
      wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2)
  let w1 : (Fin N × Fin N) → X N → ℝ := fun p x =>
      |wPair ℓ (g0 v h) (x p.1) (x p.2)|
  have hper : ∀ p : Fin N × Fin N, p ∈ pairSet N →
      |2 * (∫ x in abox N ℓ, (A p x * B p x) * K p x)|
      ≤ (∫ x in abox N ℓ, (A p x) ^ 2 * w1 p x)
        + (∫ x in abox N ℓ, (B p x) ^ 2 * w1 p x) := by
    intro p hp
    have hpij : p.1 ≠ p.2 := by
      simpa [pairSet] using (Finset.mem_filter.mp hp).2
    have hc1 : Continuous (A p) := by
      dsimp [A]
      exact aP_continuous hℓ p.1 (aQ_continuous hℓ p.2 hΦc)
    have hc2 : Continuous (B p) := by
      dsimp [B]
      exact aQ_continuous hℓ p.2 (aP_continuous hℓ p.1 hΦc)
    have h1 := w1w_cross_pair_abs_le hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1
      (i := p.1) (j := p.2) hpij hc1 hc2
    have hcong : (∫ x in abox N ℓ, (A p x * B p x) * K p x)
        = (∫ x in abox N ℓ, A p x * (B p x * K p x)) := by
      apply integral_congr_ae
      refine ae_of_all _ (fun x => ?_)
      ring
    rw [← hcong] at h1
    simpa [K, w1] using h1
  have hsumle : (∑ p ∈ pairSet N, |2 * (∫ x in abox N ℓ, (A p x * B p x) * K p x)|)
      ≤ (∑ p ∈ pairSet N,
          ((∫ x in abox N ℓ, (A p x) ^ 2 * w1 p x)
            + (∫ x in abox N ℓ, (B p x) ^ 2 * w1 p x))) := by
    exact Finset.sum_le_sum (fun p hp => hper p hp)
  have hmain : |∑ p ∈ pairSet N, 2 * (∫ x in abox N ℓ, (A p x * B p x) * K p x)|
      ≤ (∑ p ∈ pairSet N, |2 * (∫ x in abox N ℓ, (A p x * B p x) * K p x)|) := by
    simpa using (Finset.abs_sum_le_sum_abs (s := pairSet N)
      (f := fun p : Fin N × Fin N => 2 * (∫ x in abox N ℓ, (A p x * B p x) * K p x)))
  have hA : (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (A p x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
      ≤ (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
    have hmm := pq_w1_mass_le_cnPlus hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
    simpa [A, wPairC] using hmm
  have hB : (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (B p x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
      ≤ (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
    have hmm := q_p_w1_mass_le_cnPlus hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
    simpa [B, wPairC] using hmm
  have hA1 : (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (A p x) ^ 2 * w1 p x)
      ≤ (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
    simpa [w1] using hA
  have hB1 : (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (B p x) ^ 2 * w1 p x)
      ≤ (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
    simpa [w1] using hB
  have hAB : (∑ p ∈ pairSet N,
          ((∫ x in abox N ℓ, (A p x) ^ 2 * w1 p x)
            + (∫ x in abox N ℓ, (B p x) ^ 2 * w1 p x)))
      ≤ 2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
    rw [Finset.sum_add_distrib]
    nlinarith [hA1, hB1]
  calc
    |2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aP ℓ p.1 Φ) x) *
          wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))|
        = |2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (A p x * B p x) * K p x)| := by
            simp [A, B, K]
    _ = |∑ p ∈ pairSet N, 2 * (∫ x in abox N ℓ, (A p x * B p x) * K p x)| := by
            rw [Finset.mul_sum]
    _ ≤ (∑ p ∈ pairSet N, |2 * (∫ x in abox N ℓ, (A p x * B p x) * K p x)|) := hmain
    _ ≤ (∑ p ∈ pairSet N,
          ((∫ x in abox N ℓ, (A p x) ^ 2 * w1 p x)
            + (∫ x in abox N ℓ, (B p x) ^ 2 * w1 p x))) := hsumle
    _ ≤ 2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := hAB

/-- **A²-mass bound (mass-tail)**: the `A²`-sum
`A2 := 2·Σ_p∫(P_{p.1}Q_{p.2}Φ)²·w₁` (`w₁ := wPair(g₀) ≥ 0` a.e.) satisfies

`0 ≤ A2 ≤ 2·C₁·(ℓ³)⁻¹·N̂·n₊`,  `C₁ := fsqC1(a v)`. -/
lemma q3_A2_sum_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (_hv_memL1 : MemLp v 1)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    0 ≤ 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2))
      ∧ 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2))
        ≤ 2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
  classical
  let A : (Fin N × Fin N) → X N → ℝ := fun p x => aP ℓ p.1 (aQ ℓ p.2 Φ) x
  have hA : (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (A p x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
      ≤ (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
    have hmm := pq_w1_mass_le_cnPlus hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
    simpa [A, wPairC] using hmm
  have hnn_per : ∀ p : Fin N × Fin N, p ∈ pairSet N →
      (∫ x in abox N ℓ, (A p x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2))
        = (∫ x in abox N ℓ, (A p x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)|) := by
    intro p hp
    have hpij : p.1 ≠ p.2 := by
      simpa [pairSet] using (Finset.mem_filter.mp hp).2
    have hnn := w1_nonneg_ae_pair (N := N) hℓ hR hv_nonneg hvrad hv_supp h hpij
    apply integral_congr_ae
    filter_upwards [hnn] with x hx
    congr 1
    rw [abs_of_nonneg hx]
  have hEq : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2))
      = (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (A p x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)|) := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    simpa [A] using (hnn_per p hp)
  have hnonneg : 0 ≤ (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2)) := by
    rw [hEq]
    apply Finset.sum_nonneg
    intro p hp
    apply integral_nonneg
    intro x
    exact mul_nonneg (sq_nonneg (A p x)) (abs_nonneg _)
  have hUpper : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2))
      ≤ (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
    rw [hEq]
    simpa [A] using hA
  constructor
  · nlinarith
  · nlinarith

/-- **q4 absorbs the q4B-cross at ¾ strength, summed** (rebalanced for the
all-Φ assembly): leaving ¼ of `q4word` free for q2's T4-bound,
`¾q4word + Cross ≥ −(8/3)·A2sum` (`Cross := 2Σ∫A·q4B·w₁`,
`A2sum := Σ_p∫(P_{p.1}Q_{p.2}Φ)²·w₁`). -/
lemma q4_absorbs_cross_frac_pairs {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (hv_memL1 : MemLp v 1)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (3 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ
      + 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (q4B ℓ (omC (Classical.choose h)) Φ p x) *
            wPair ℓ (g0 v h) (x p.1) (x p.2))
    ≥ - (8 / 3) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2)) := by
  classical
  let A2sum : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2)
  let X2w1 : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2)
  let X2wv : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wPair ℓ v (x p.1) (x p.2)
  let Cross : ℝ := 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (q4B ℓ (omC (Classical.choose h)) Φ p x) *
        wPair ℓ (g0 v h) (x p.1) (x p.2))
  -- per-pair frac absorption summed: (3/8)X²w₁ + 2AXw₁ ≥ −(8/3)A²w₁
  have hper : ∀ p : Fin N × Fin N, p ∈ pairSet N →
      (3 / 8) * (∫ x in abox N ℓ,
          (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2))
        + 2 * (∫ x in abox N ℓ,
            (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (q4B ℓ (omC (Classical.choose h)) Φ p x) *
              wPair ℓ (g0 v h) (x p.1) (x p.2))
      ≥ - (8 / 3) * (∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2)) := by
    intro p hp
    have hpij : p.1 ≠ p.2 := by
      simpa [pairSet] using (Finset.mem_filter.mp hp).2
    exact q4_pair_absorbs_cross_frac hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1
      (i := p.1) (j := p.2) hpij hΦc
  have hsumabs : (∑ p ∈ pairSet N,
        ((3 / 8) * (∫ x in abox N ℓ,
            (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2))
          + 2 * (∫ x in abox N ℓ,
              (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (q4B ℓ (omC (Classical.choose h)) Φ p x) *
                wPair ℓ (g0 v h) (x p.1) (x p.2))))
      ≥ (∑ p ∈ pairSet N,
          - (8 / 3) * (∫ x in abox N ℓ,
              (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2))) := by
    exact Finset.sum_le_sum (fun p hp => hper p hp)
  have hsplit : (∑ p ∈ pairSet N,
        ((3 / 8) * (∫ x in abox N ℓ,
            (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2))
          + 2 * (∫ x in abox N ℓ,
              (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (q4B ℓ (omC (Classical.choose h)) Φ p x) *
                wPair ℓ (g0 v h) (x p.1) (x p.2))))
      = (3 / 8) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2))
        + 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (q4B ℓ (omC (Classical.choose h)) Φ p x) *
              wPair ℓ (g0 v h) (x p.1) (x p.2)) := by
    simp [Finset.sum_add_distrib, Finset.mul_sum]
  have hneg : (∑ p ∈ pairSet N,
          - (8 / 3) * (∫ x in abox N ℓ,
              (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2)))
      = - (8 / 3) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2)) := by
    simp [Finset.mul_sum]
  have hsq : (3 / 8) * X2w1 + Cross ≥ - (8 / 3) * A2sum := by
    rw [← hsplit, ← hneg]
    simpa [X2w1, Cross, A2sum] using hsumabs
  -- kernel comparison: q4word ≥ ½X2wv ≥ ½X2w1, so ¾q4word ≥ (3/8)X2w1
  have hcmp : (3 / 8) * X2w1 ≤ (3 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
    have hq4 : X2wv = 2 * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
      dsimp [X2wv]
      unfold q4word
      simp [wPairC]
    have h12 : (1 / 2) * X2w1 ≤ (1 / 2) * X2wv := by
      -- X2w1 ≤ X2wv summed kernel comparison
      have hpercmp : ∀ p : Fin N × Fin N, p ∈ pairSet N →
          (∫ x in abox N ℓ,
            (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2))
          ≤ (∫ x in abox N ℓ,
            (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wPair ℓ v (x p.1) (x p.2)) := by
        intro p hp
        have hpij : p.1 ≠ p.2 := by
          simpa [pairSet] using (Finset.mem_filter.mp hp).2
        exact q4B_sq_w1_le_w_pair hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1
          (i := p.1) (j := p.2) hpij hΦc
      have hsumle : X2w1 ≤ X2wv := by
        dsimp [X2w1, X2wv]
        exact Finset.sum_le_sum (fun p hp => hpercmp p hp)
      have hhalf : 0 ≤ (1 / 2 : ℝ) := by norm_num
      nlinarith
    have hmain : (3 / 8) * X2w1 ≤ (3 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
      have hq4' : (1 / 2) * X2wv = q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
        rw [hq4]
        ring
      have h3 : (3 / 8) * X2w1 = (3 / 4) * ((1 / 2) * X2w1) := by ring
      rw [h3]
      have hc := mul_le_mul_of_nonneg_left h12 (by norm_num : 0 ≤ (3 / 4 : ℝ))
      nlinarith
    exact hmain
  have hfinal : (3 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ + Cross
      ≥ - (8 / 3) * A2sum := by
    nlinarith [hsq, hcmp]
  simpa [Cross, A2sum] using hfinal

/-! ## All-Φ closure of the joint assembly (Session-147b)

`q1_q3_q4_mass` — from `q1_q3_q4_assembly` (the PPQω-cancellation) and the
mass-tail bounds (`q3_PQw_sum_abs_le`, `q3_QPw_sum_abs_le`, `q3_A2_sum_le`):

`q1word + q3word + q4word ≥ w₁-line − 2μ·OB₁ − 6·C₁·(ℓ³)⁻¹·N̂·n₊`
(`C₁ := fsqC1(a v)`), with the w₁-line and `OB₁` exact — the all-Φ input of
the (windowed, c-number-layer) Step-4 CS into A₀'s quadratic.
-/
/-- **Joint q1+q3+q4 assembly, all-Φ mass form**: from
`q1_q3_q4_assembly` (the PPQω-cancellation) and the mass-tail bounds
(`q3_PQw_sum_abs_le`, `q3_QPw_sum_abs_le`, `q3_A2_sum_le`),

`q1word + q3word + q4word ≥ w₁-line − 2μ·OB₁ − 6·C₁·(ℓ³)⁻¹·N̂·n₊`

(`C₁ := fsqC1(a v)`), with the w₁-line `2(ℓ³)⁻¹Σ_i∫(P_iΦ)f₁(x_i)Q_i((Σ_{j≠i}P_j)Φ)`
and `OB₁ := Σ_i∫(Q_iΦ)(P_iΦ)f₁(x_i)` — the all-Φ input of the (windowed)
Step-4 CS into A₀'s quadratic. -/
lemma q1_q3_q4_mass {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (hv_memL1 : MemLp v 1)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    q1word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ
      + q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ
      + q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ
    ≥ 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
        (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)) *
          (aQ ℓ i (fun y : X N => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0))) x)
      - 2 * μ * (∑ i : Fin N, ∫ x in abox N ℓ,
          (aQ ℓ i Φ x) * (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)))
      - 6 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
  classical
  let L1 : ℝ := 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
      (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)) *
        (aQ ℓ i (fun y : X N => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0))) x)
  let OB : ℝ := ∑ i : Fin N, ∫ x in abox N ℓ,
      (aQ ℓ i Φ x) * (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i))
  let PQw : ℝ := 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aQ ℓ p.1 Φ) x) *
        wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))
  let QPw : ℝ := 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aP ℓ p.1 Φ) x) *
        wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))
  let A2 : ℝ := 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2))
  have hA := q1_q3_q4_assembly (μ := μ) hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1 hΦc
  have hA' : q1word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ
        + q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ
        + q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ
      ≥ L1 - 2 * μ * OB - PQw - QPw - A2 := by
    simpa [L1, OB, PQw, QPw, A2] using hA
  have hPQ := q3_PQw_sum_abs_le hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1 hΦc
  have hQP := q3_QPw_sum_abs_le hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1 hΦc
  have hA2 := q3_A2_sum_le hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1 hΦc
  have hPQlo : - PQw ≥ - (2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ) := by
    have hpq : |PQw| ≤ 2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
      dsimp [PQw]
      exact hPQ
    have hb := (abs_le.mp hpq).2
    nlinarith
  have hQPlo : - QPw ≥ - (2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ) := by
    have hqp : |QPw| ≤ 2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
      dsimp [QPw]
      exact hQP
    have hb := (abs_le.mp hqp).2
    nlinarith
  have hA2lo : - A2 ≥ - (2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ) := by
    have hup : A2 ≤ 2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
      dsimp [A2]
      exact hA2.2
    have hlo : 0 ≤ A2 := by
      dsimp [A2]
      exact hA2.1
    nlinarith
  have hgoal : q1word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ
        + q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ
        + q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ
      ≥ L1 - 2 * μ * OB - 6 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
    nlinarith [hA', hPQlo, hQPlo, hA2lo]
  simpa [L1, OB] using hgoal

/-! ## Item (a): the all-Φ w₁-line-exact potential bound (Session-148)

`pot_sharp_w1line` — from `pot_q0_lower`, the EXACT q1/q3 decompositions
(`q1word = w₁-line + PPQω − 2μ·OB` via `q1word_eq_q1n0_split` +
`q1w0_pair_sum_eq_sandwich_n0`; `q3word = Cross − PPQω − PQω − QPω` via
`q3word_expand` + `q3_PPQw_eq_q1_pair_sum_w0`), `q2_sharp_lower` (its T4
bound pays ¼ of `q4word`), the ¾-rebalanced absorption
`q4_absorbs_cross_frac_pairs` (`¾q4word + Cross ≥ −(8/3)·A2s`; the remaining
¾ of `q4word` absorbs the q4B-cross), and the mass-tail bounds:

`qLHSword ≥ q0RenVal + w₁-line − 2μ·OB₁
             − 2·C₂·(ℓ³)⁻¹·N̂·n₊ − C₁·(ℓ³)⁻¹·(4·cS2 + 29/3·N̂·n₊) − μ·C₁·n₊`

(the PPQω-terms cancel exactly and every `q4word`-dependence drops), with the
w₁-line `2(ℓ³)⁻¹Σ_i∫(P_iΦ)f₁(x_i)Q_i((Σ_{j≠i}P_j)Φ)` and
`OB₁ := Σ_i∫(Q_iΦ)(P_iΦ)f₁(x_i)` EXACT — the all-Φ potential-part input of
the (windowed, c-number-layer) Step-4 CS.
-/
/-- **All-Φ per-state potential bound with the w₁-line exact**
(`pot_sharp_w1line`): from `pot_q0_lower`, the exact q1/q3 decompositions
(`q1word = w₁-line + PPQω − 2μ·OB`, `q3word = Cross − PPQω − PQω − QPω`),
`q2_sharp_lower` (T4 paying ¼ of q4word) and the ¾-rebalanced absorption
`q4_absorbs_cross_frac_pairs` (the remaining ¾ of q4word absorbs the
q4B-cross), the PPQω-terms cancel and all q4word-dependence drops, leaving
the w₁-line and `OB` EXACT plus sharp `n₊`/`cS2`-masses — the all-Φ input of
the (windowed) Step-4 CS. -/
lemma pot_sharp_w1line {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ) (hμ : 0 ≤ μ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ ≥
      q0RenVal (N := N) (v := v) ℓ μ Φ
      + 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
          (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)) *
            (aQ ℓ i (fun y : X N => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0))) x)
      - 2 * μ * (∑ i : Fin N, ∫ x in abox N ℓ,
          (aQ ℓ i Φ x) * (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)))
      - 2 * (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (4 * cS2 ℓ Φ + 3 * ((N : ℝ) * cnPlus ℓ Φ))
      - (8 / 3) * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - 2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - 2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - μ * (fsqC1 (a v)) * cnPlus ℓ Φ := by
  classical
  let L1 : ℝ := 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
      (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)) *
        (aQ ℓ i (fun y : X N => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0))) x)
  let OB : ℝ := ∑ i : Fin N, ∫ x in abox N ℓ,
      (aQ ℓ i Φ x) * (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i))
  let P : ℝ := 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.1 (aP ℓ p.2 Φ) x) *
        wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))
  let Cross : ℝ := 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (q4B ℓ (omC (Classical.choose h)) Φ p x) *
        wPair ℓ (g0 v h) (x p.1) (x p.2))
  let PQw : ℝ := 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aQ ℓ p.1 Φ) x) *
        wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))
  let QPw : ℝ := 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aP ℓ p.1 Φ) x) *
        wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))
  let A2s : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * wPair ℓ (g0 v h) (x p.1) (x p.2)
  let q4 : ℝ := q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ
  -- exact q1 decomposition: q1word = L1 + P − 2μOB
  have hq1 := q1word_eq_q1n0_split (N := N) (μ := μ) hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
  have hL2P := q1w0_pair_sum_eq_sandwich_n0 hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
  have hq1' : q1word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ
      = L1 + P - 2 * μ * OB := by
    -- q1word = L1 + L2 − 2μOB (hq1); L2 = P (hL2P)
    have hq1'' : q1word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ
        = L1 + 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
            (aP ℓ i Φ x) *
              (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i)) *
              (aQ ℓ i (fun y : X N => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0))) x)
          - 2 * μ * OB := by
      simpa [L1, OB] using hq1
    have hL2 : 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
          (aP ℓ i Φ x) *
            (w1Fibre ℓ (wPairC ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w)) (x i)) *
            (aQ ℓ i (fun y : X N => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0))) x)
        = P := by
      simpa [P, wPairC] using hL2P.symm
    rw [hL2] at hq1''
    exact hq1''
  -- exact q3 decomposition: q3word = Cross − P − PQw − QPw
  have hq3e := q3word_expand hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1 hΦc
  have hPPQ := q3_PPQw_eq_q1_pair_sum_w0 (N := N) hℓ (v := v) h hΦc
  have hq3' : q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ = Cross - P - PQw - QPw := by
    have hPPQ' : 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aP ℓ p.1 Φ) x) *
            wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))
        = P := by
      simpa [P, wPairC] using hPPQ
    have hq3e' : q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ
        = Cross
          - 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
              (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aP ℓ p.1 Φ) x) *
                wPair ℓ (fun w : ℝ³ => g0 v h w * Classical.choose h w) (x p.1) (x p.2))
          - PQw - QPw := by
      simpa [Cross, PQw, QPw] using hq3e
    rw [hPPQ'] at hq3e'
    simpa using hq3e'
  -- q0 + q1 + q2 + q3 + q4 ≤ qLHS
  have hpot := pot_q0_lower (μ := μ) hℓ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc
  -- q2 ≥ q2mass − ¼ q4
  have hq2 := q2_sharp_lower hℓ hμ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc
  -- ¾ q4 + Cross ≥ −(8/3)A2s
  have hfrac := q4_absorbs_cross_frac_pairs hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1 hΦc
  have hfrac' : (3 / 4) * q4 + Cross ≥ - (8 / 3) * A2s := by
    simpa [q4, Cross, A2s] using hfrac
  -- mass bounds
  have hPQ := q3_PQw_sum_abs_le hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1 hΦc
  have hQP := q3_QPw_sum_abs_le hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1 hΦc
  have hA2 := q3_A2_sum_le hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1 hΦc
  let m : ℝ := (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
  have hPQlo : - PQw ≥ - 2 * m := by
    have habs : |PQw| ≤ 2 * m := by
      have hb := hPQ
      dsimp [PQw, m]
      nlinarith
    have hb := (abs_le.mp habs).2
    nlinarith
  have hQPlo : - QPw ≥ - 2 * m := by
    have habs : |QPw| ≤ 2 * m := by
      have hb := hQP
      dsimp [QPw, m]
      nlinarith
    have hb := (abs_le.mp habs).2
    nlinarith
  have hA2lo : - (8 / 3) * A2s ≥ - (8 / 3) * m := by
    have hup : A2s ≤ m := by
      have hb := hA2.2
      dsimp [A2s, m]
      nlinarith
    have hlo : 0 ≤ A2s := by
      have hb := hA2.1
      dsimp [A2s]
      nlinarith
    nlinarith
  -- assemble (qLHS ≥ q0 + L1 − 2μOB + Cross − PQw − QPw + q2 + q4)
  have hq13 : q1word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ
        + q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ
      = L1 + Cross - 2 * μ * OB - PQw - QPw := by
    rw [hq1', hq3']
    ring
  have hpot2 : q0RenVal (N := N) (v := v) ℓ μ Φ + L1 - 2 * μ * OB
        + Cross - PQw - QPw
        + q2word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ
        + q4
      ≤ qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ := by
    have hpot' : q0RenVal (N := N) (v := v) ℓ μ Φ
          + q1word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ
          + q2word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ
          + q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ
          + q4
        ≤ qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ := by
      simpa [q4] using hpot
    nlinarith [hpot', hq13]
  have hgoal : q0RenVal (N := N) (v := v) ℓ μ Φ + L1 - 2 * μ * OB
      - 2 * (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (4 * cS2 ℓ Φ + 3 * ((N : ℝ) * cnPlus ℓ Φ))
      - (8 / 3) * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - 2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - 2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - μ * (fsqC1 (a v)) * cnPlus ℓ Φ
    ≤ qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ := by
    -- q2 ≥ q2mass − ¼q4, ¾q4+Cross ≥ −(8/3)A2s, |PQw|,|QPw| ≤ 2m, A2s ≤ m
    nlinarith [hpot2, hq2, hfrac', hPQlo, hQPlo, hA2lo]
  simpa [L1, OB] using hgoal

/-! ## Session-149: the exact n₀-scalar collapse (per-sector Step-4 enabler)

`q1_n0_scalar_pt` — pointwise `Σ_{j≠i}P_j(Q_iΦ)(x) = N·(Q_iΦ)(x) −
Σ_k Q_k(Q_iΦ)(x)`, from `n₀ + n₊ = N̂·id` (`P_j + Q_j = id` per slot) and
`P_iQ_i = 0`.  This is the per-sector replacement of FS's operator-`n₀`
arithmetic: the realised condensate count inside the w₁-line sandwich becomes
the FIXED particle number `N̂` EXACTLY, leaving only the `n₊`-correction —
so FS's `eq:Q1n0`-line-1 `(n₀/V−μ)ΣQf₁P` reduces per sector to the
scalar-weighted cross `2(u−μ)·OB₁` (u := N̂/ℓ³) minus an `n₊`-suppressed
correction, with NO Fock √-algebra needed.  (Next lemma in progress:
`q1_w1line_scalar_split` — the integral-level split; the pointwise identity
and per-i integral mechanics are verified, only the final sum assembly
remains.)
-/
/-- **Pointwise n₀-scalar collapse**: `Σ_{j≠i}P_j(Q_iΦ)(x) = N·(Q_iΦ)(x) −
Σ_k Q_k(Q_iΦ)(x)` — from `n₀ + n₊ = N̂·id` (`P_j+Q_j = id` per slot) and
`P_iQ_i = 0` (`aP_aQ_zero`).  This is the per-sector replacement of FS's
operator-`n₀` arithmetic: the realised condensate count becomes the fixed
particle number `N̂` EXACTLY, leaving only the `n₊`-operator correction. -/
lemma q1_n0_scalar_pt {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) (x : X N) :
    (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j (aQ ℓ i Φ) x else 0)
    = (N : ℝ) * (aQ ℓ i Φ x) - (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x) := by
  classical
  have hsum : (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j (aQ ℓ i Φ) x else 0)
      = ∑ j : Fin N, aP ℓ j (aQ ℓ i Φ) x := by
    let A : Fin N → ℝ := fun j => aP ℓ j (aQ ℓ i Φ) x
    have hA : (∑ j : Fin N, if _hj : j ≠ i then A j else 0)
        = ∑ j ∈ (Finset.univ.erase i), A j := by
      have hf : (∑ j ∈ (Finset.univ.filter (fun j : Fin N => j ≠ i)), A j)
          = (∑ j : Fin N, if _hj : j ≠ i then A j else 0) := by
        simpa using (Finset.sum_filter (s := (Finset.univ : Finset (Fin N)))
          (p := fun j : Fin N => j ≠ i) (f := A))
      have hfe : (Finset.univ.filter (fun j : Fin N => j ≠ i)) = Finset.univ.erase i := by
        ext j
        by_cases hji : j = i <;> simp [hji]
      rw [← hf, hfe]
    have hB : (∑ j ∈ (Finset.univ.erase i), A j) = (∑ j : Fin N, A j) - A i := by
      have hmem : i ∈ (Finset.univ : Finset (Fin N)) := by simp
      have hE := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin N))) (a := i) hmem (f := A)
      have hz : A i = 0 := by
        dsimp [A]
        exact aP_aQ_zero hℓ i hΦc x
      nlinarith
    calc
      (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j (aQ ℓ i Φ) x else 0)
          = ∑ j ∈ (Finset.univ.erase i), A j := by
              simpa [A] using hA
      _ = (∑ j : Fin N, A j) - A i := hB
      _ = (∑ j : Fin N, A j) - 0 := by
              have hz : A i = 0 := by
                dsimp [A]
                exact aP_aQ_zero hℓ i hΦc x
              rw [hz]
      _ = ∑ j : Fin N, A j := by ring
      _ = ∑ j : Fin N, aP ℓ j (aQ ℓ i Φ) x := by rfl
  have hsplit : (∑ j : Fin N, aP ℓ j (aQ ℓ i Φ) x)
      = (N : ℝ) * (aQ ℓ i Φ x) - (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x) := by
    -- per j: aP_jψ + aQ_jψ = ψ (aQ def), sum over j
    have hper : ∀ j : Fin N, aP ℓ j (aQ ℓ i Φ) x = (aQ ℓ i Φ x) - aQ ℓ j (aQ ℓ i Φ) x := by
      intro j
      have hq : aQ ℓ j (aQ ℓ i Φ) x = (aQ ℓ i Φ x) - aP ℓ j (aQ ℓ i Φ) x := by rfl
      nlinarith
    calc
      (∑ j : Fin N, aP ℓ j (aQ ℓ i Φ) x)
          = ∑ j : Fin N, ((aQ ℓ i Φ x) - aQ ℓ j (aQ ℓ i Φ) x) := by
              exact Finset.sum_congr rfl (fun j hj => hper j)
      _ = (∑ j : Fin N, (aQ ℓ i Φ x)) - (∑ j : Fin N, aQ ℓ j (aQ ℓ i Φ) x) := by
              rw [Finset.sum_sub_distrib]
      _ = (N : ℝ) * (aQ ℓ i Φ x) - (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x) := by
              simp
  rw [hsum]
  exact hsplit
/-- **w₁-line scalar split (exact, per-sector n₀-replacement)**: from the
pointwise `Q_i((Σ_{j≠i}P_j)Φ) = N·Q_iΦ − Σ_k Q_k(Q_iΦ)` (`q1_n0_collapse` +
`q1_n0_scalar_pt`), the realised-`n₀` w₁-line becomes the SCALAR-weighted
cross `2(N̂/ℓ³)·OB₁` minus the `n₊`-correction:

`w₁-line − 2μ·OB₁ = 2(N̂/ℓ³ − μ)·OB₁ − 2·(ℓ³)⁻¹·Corr`

(`OB₁ := Σ_i∫(Q_iΦ)(P_iΦ)f₁(x_i)`,
`Corr := Σ_i∫(P_iΦ)f₁(x_i)·(Σ_k Q_k(Q_iΦ))x`, `f₁ := w1Fibre(wPairC(g₀))`)
— exact for every state; FS's `n₀ ↦ N̂` replacement with the fixed particle
number is per-sector algebra, the `n₊`-correction being the only remainder. -/
lemma q1_w1line_scalar_split {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
        (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)) *
          (aQ ℓ i (fun y : X N => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0))) x)
      - 2 * μ * (∑ i : Fin N, ∫ x in abox N ℓ,
          (aQ ℓ i Φ x) * (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)))
    = 2 * (((N : ℝ) / ℓ ^ 3) - μ) * (∑ i : Fin N, ∫ x in abox N ℓ,
          (aQ ℓ i Φ x) * (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)))
      - 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
          (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)) *
            (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x)) := by
  classical
  let f1 : ℝ³ → ℝ := fun z => w1Fibre ℓ (wPairC ℓ (g0 v h)) z
  let C0 : ℝ := chiSup ^ 2 * 2 * (8 * π * a v)
  have hf1b : ∀ z : ℝ³, z ∈ acube ℓ → |f1 z| ≤ C0 := by
    intro z hz
    dsimp [f1, C0]
    have hb := w1c_fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ z
    simpa [w1Fibre, wPairC] using hb
  have hf1m : AEStronglyMeasurable f1 (volume.restrict (acube ℓ)) := by
    dsimp [f1]
    have hfac := fibre_acube_aem (ℓ := ℓ) (h := g0 v h) (g0_integrable hR hv_supp h)
    simpa [w1Fibre, wPairC] using hfac
  -- per-i inner-integral identity
  have hper : ∀ i : Fin N,
      (∫ x in abox N ℓ,
          (aP ℓ i Φ x) * f1 (x i) *
            (aQ ℓ i (fun y : X N => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0))) x)
      = (N : ℝ) * (∫ x in abox N ℓ, (aP ℓ i Φ x) * f1 (x i) * (aQ ℓ i Φ x))
        - (∫ x in abox N ℓ,
            (aP ℓ i Φ x) * f1 (x i) * (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x)) := by
    intro i
    have hAc : Continuous (fun x : X N => aP ℓ i Φ x) := aP_continuous hℓ i hΦc
    have hQc : Continuous (fun x : X N => aQ ℓ i Φ x) := aQ_continuous hℓ i hΦc
    have hGc : Continuous (fun x : X N => ∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x) := by
      refine continuous_finsetSum (Finset.univ) ?_
      intro k hk
      exact aQ_continuous hℓ k (aQ_continuous hℓ i hΦc)
    have hI_AQ : IntegrableOn (fun x => (aP ℓ i Φ x) * f1 (x i) * (aQ ℓ i Φ x))
        (abox N ℓ) volume := by
      have hS : Continuous (fun x => (aP ℓ i Φ x) * (aQ ℓ i Φ x)) := hAc.mul hQc
      have hb := integrableOn_slot_fibre hℓ i hf1m (fun z hz => hf1b z hz) hS
      convert hb using 1
      ext x
      ring
    have hI_AG : IntegrableOn (fun x => (aP ℓ i Φ x) * f1 (x i) *
          (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x)) (abox N ℓ) volume := by
      have hS : Continuous (fun x => (aP ℓ i Φ x) * (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x)) := hAc.mul hGc
      have hb := integrableOn_slot_fibre hℓ i hf1m (fun z hz => hf1b z hz) hS
      convert hb using 1
      ext x
      ring
    have hI1 : Integrable (fun x => (aP ℓ i Φ x) * f1 (x i) * ((N : ℝ) * (aQ ℓ i Φ x)))
        (volume.restrict (abox N ℓ)) := by
      have hb := hI_AQ.const_mul (N : ℝ)
      convert hb using 1
      ext x
      ring
    have hI2 : Integrable (fun x => (aP ℓ i Φ x) * f1 (x i) *
          (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x)) (volume.restrict (abox N ℓ)) := by
      simpa [IntegrableOn] using hI_AG
    have hpt : ∀ x : X N,
        (aP ℓ i Φ x) * f1 (x i) *
            (aQ ℓ i (fun y : X N => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0))) x
        = (aP ℓ i Φ x) * f1 (x i) * ((N : ℝ) * (aQ ℓ i Φ x)
            - (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x)) := by
      intro x
      have hc := q1_n0_collapse (N := N) hℓ i hΦc x
      have hs := q1_n0_scalar_pt (N := N) hℓ i hΦc x
      rw [← hc, hs]
    have hd : (fun x : X N =>
          (aP ℓ i Φ x) * f1 (x i) *
            (aQ ℓ i (fun y : X N => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0))) x)
        =ᵐ[volume.restrict (abox N ℓ)] fun x : X N =>
            (aP ℓ i Φ x) * f1 (x i) * ((N : ℝ) * (aQ ℓ i Φ x)
              - (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x)) := by
      refine ae_of_all _ (fun x => ?_)
      exact hpt x
    have hsplit : (∫ x in abox N ℓ, (aP ℓ i Φ x) * f1 (x i) *
          ((N : ℝ) * (aQ ℓ i Φ x) - (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x)))
        = (∫ x in abox N ℓ, (aP ℓ i Φ x) * f1 (x i) * ((N : ℝ) * (aQ ℓ i Φ x)))
          - (∫ x in abox N ℓ, (aP ℓ i Φ x) * f1 (x i) *
              (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x)) := by
      have hd2 : (fun x : X N =>
            (aP ℓ i Φ x) * f1 (x i) * ((N : ℝ) * (aQ ℓ i Φ x)
              - (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x)))
          =ᵐ[volume.restrict (abox N ℓ)] fun x : X N =>
              (aP ℓ i Φ x) * f1 (x i) * ((N : ℝ) * (aQ ℓ i Φ x))
                - (aP ℓ i Φ x) * f1 (x i) * (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x) := by
        refine ae_of_all _ (fun x => ?_)
        ring
      calc
        (∫ x in abox N ℓ, (aP ℓ i Φ x) * f1 (x i) *
            ((N : ℝ) * (aQ ℓ i Φ x) - (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x)))
            = (∫ x in abox N ℓ,
                (aP ℓ i Φ x) * f1 (x i) * ((N : ℝ) * (aQ ℓ i Φ x))
                  - (aP ℓ i Φ x) * f1 (x i) * (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x)) := by
                apply integral_congr_ae
                exact hd2
        _ = (∫ x in abox N ℓ, (aP ℓ i Φ x) * f1 (x i) * ((N : ℝ) * (aQ ℓ i Φ x)))
            - (∫ x in abox N ℓ, (aP ℓ i Φ x) * f1 (x i) *
                (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x)) := by
                rw [integral_sub hI1 hI2]
    have hNpull : (∫ x in abox N ℓ, (aP ℓ i Φ x) * f1 (x i) * ((N : ℝ) * (aQ ℓ i Φ x)))
        = (N : ℝ) * (∫ x in abox N ℓ, (aP ℓ i Φ x) * f1 (x i) * (aQ ℓ i Φ x)) := by
      have hcong : (fun x : X N => (aP ℓ i Φ x) * f1 (x i) * ((N : ℝ) * (aQ ℓ i Φ x)))
          =ᵐ[volume.restrict (abox N ℓ)] fun x : X N =>
              (N : ℝ) * ((aP ℓ i Φ x) * f1 (x i) * (aQ ℓ i Φ x)) := by
        refine ae_of_all _ (fun x => ?_)
        ring
      calc
        (∫ x in abox N ℓ, (aP ℓ i Φ x) * f1 (x i) * ((N : ℝ) * (aQ ℓ i Φ x)))
            = (∫ x in abox N ℓ, (N : ℝ) * ((aP ℓ i Φ x) * f1 (x i) * (aQ ℓ i Φ x))) := by
                apply integral_congr_ae
                exact hcong
        _ = (N : ℝ) * (∫ x in abox N ℓ, (aP ℓ i Φ x) * f1 (x i) * (aQ ℓ i Φ x)) := by
                rw [integral_const_mul]
    calc
      (∫ x in abox N ℓ,
          (aP ℓ i Φ x) * f1 (x i) *
            (aQ ℓ i (fun y : X N => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0))) x)
          = (∫ x in abox N ℓ, (aP ℓ i Φ x) * f1 (x i) *
              ((N : ℝ) * (aQ ℓ i Φ x) - (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x))) := by
              apply integral_congr_ae
              exact hd
      _ = (∫ x in abox N ℓ, (aP ℓ i Φ x) * f1 (x i) * ((N : ℝ) * (aQ ℓ i Φ x)))
          - (∫ x in abox N ℓ, (aP ℓ i Φ x) * f1 (x i) *
              (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x)) := hsplit
      _ = (N : ℝ) * (∫ x in abox N ℓ, (aP ℓ i Φ x) * f1 (x i) * (aQ ℓ i Φ x))
          - (∫ x in abox N ℓ, (aP ℓ i Φ x) * f1 (x i) *
              (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x)) := by
              rw [hNpull]
  -- assemble the i-sum
  have hsum : (∑ i : Fin N, ∫ x in abox N ℓ,
        (aP ℓ i Φ x) * f1 (x i) *
          (aQ ℓ i (fun y : X N => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0))) x)
      = (N : ℝ) * (∑ i : Fin N, ∫ x in abox N ℓ,
            (aP ℓ i Φ x) * f1 (x i) * (aQ ℓ i Φ x))
        - (∑ i : Fin N, ∫ x in abox N ℓ,
            (aP ℓ i Φ x) * f1 (x i) * (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x)) := by
    calc
      (∑ i : Fin N, ∫ x in abox N ℓ,
            (aP ℓ i Φ x) * f1 (x i) *
              (aQ ℓ i (fun y : X N => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0))) x)
          = ∑ i : Fin N,
              ((N : ℝ) * (∫ x in abox N ℓ, (aP ℓ i Φ x) * f1 (x i) * (aQ ℓ i Φ x))
                - (∫ x in abox N ℓ, (aP ℓ i Φ x) * f1 (x i) *
                    (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x))) := by
              exact Finset.sum_congr rfl (fun i hi => hper i)
      _ = (N : ℝ) * (∑ i : Fin N, ∫ x in abox N ℓ,
              (aP ℓ i Φ x) * f1 (x i) * (aQ ℓ i Φ x))
          - (∑ i : Fin N, ∫ x in abox N ℓ,
              (aP ℓ i Φ x) * f1 (x i) * (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x)) := by
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hw1line : 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
        (aP ℓ i Φ x) * f1 (x i) *
          (aQ ℓ i (fun y : X N => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0))) x)
      = 2 * ((N : ℝ) / ℓ ^ 3) * (∑ i : Fin N, ∫ x in abox N ℓ,
            (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f1 (x i))
        - 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
            (aP ℓ i Φ x) * f1 (x i) * (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x)) := by
    have hOrder : (∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i Φ x) * f1 (x i) * (aQ ℓ i Φ x))
        = (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f1 (x i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply integral_congr_ae
      refine ae_of_all _ (fun x => ?_)
      ring
    rw [hsum]
    rw [hOrder]
    rw [div_eq_mul_inv]
    ring
  -- convert the target's w1Fibre-sums to the f1-form used by hw1line
  have hLw : (∑ i : Fin N, ∫ x in abox N ℓ,
        (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)) *
          (aQ ℓ i (fun y : X N => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0))) x)
      = (∑ i : Fin N, ∫ x in abox N ℓ,
          (aP ℓ i Φ x) * f1 (x i) *
            (aQ ℓ i (fun y : X N => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0))) x) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply integral_congr_ae
    refine ae_of_all _ (fun x => ?_)
    dsimp [f1]
  have hOBw : (∑ i : Fin N, ∫ x in abox N ℓ,
        (aQ ℓ i Φ x) * (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)))
      = (∑ i : Fin N, ∫ x in abox N ℓ,
          (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f1 (x i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply integral_congr_ae
    refine ae_of_all _ (fun x => ?_)
    dsimp [f1]
  have hCw : (∑ i : Fin N, ∫ x in abox N ℓ,
        (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)) *
          (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x))
      = (∑ i : Fin N, ∫ x in abox N ℓ,
          (aP ℓ i Φ x) * f1 (x i) * (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x)) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply integral_congr_ae
    refine ae_of_all _ (fun x => ?_)
    dsimp [f1]
  -- hw1line states: 2(ℓ³)⁻¹·Σf1 − 2μ·OBf = 2(u−μ)·OBf − 2(ℓ³)⁻¹·Corrf
  calc
    2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
          (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)) *
            (aQ ℓ i (fun y : X N => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0))) x)
        - 2 * μ * (∑ i : Fin N, ∫ x in abox N ℓ,
            (aQ ℓ i Φ x) * (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)))
        = 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
              (aP ℓ i Φ x) * f1 (x i) *
                (aQ ℓ i (fun y : X N => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0))) x)
          - 2 * μ * (∑ i : Fin N, ∫ x in abox N ℓ,
              (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f1 (x i)) := by
            rw [hLw, hOBw]
    _ = 2 * (((N : ℝ) / ℓ ^ 3) - μ) * (∑ i : Fin N, ∫ x in abox N ℓ,
            (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f1 (x i))
        - 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
            (aP ℓ i Φ x) * f1 (x i) * (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x)) := by
            rw [hw1line]
            ring
    _ = 2 * (((N : ℝ) / ℓ ^ 3) - μ) * (∑ i : Fin N, ∫ x in abox N ℓ,
            (aQ ℓ i Φ x) * (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)))
        - 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
            (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)) *
              (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x)) := by
            rw [← hOBw, ← hCw]


/-! ## Session-151: `w₁`-fibre nonnegativity + the per-slot AM–GM CS

* `w1Fibre_nonneg` — `0 ≤ w1Fibre(wPairC(g₀)) z` pointwise (from `g₀ ≥ 0`
  a.e., `χ ≥ 0`, `χ⋆χ ≥ 0`; the acube-restricted `integral_nonneg_of_ae`).
* `q1_cross_w1_cs` — per-slot AM–GM CS on the scalar-weighted cross (all-Φ,
  any real `t`): `2t·OB₁ ≥ −t²·8πa·S − qOneMass` (`S := cS1`) — pointwise
  `(t·P_iΦ+Q_iΦ)²f₁ ≥ 0` summed + `onebody_mass_condensate`
  (`Σ_i∫(P_iΦ)²f₁ = 8πa·S`) + `qOneMass` (rfl).  Instantiate `t := u−μ`
  (via `q1_w1line_scalar_split`) for the windowed Step-4 CS.
-/
/-- **`w₁`-fibre nonnegativity**: `0 ≤ w1Fibre(wPairC(g₀)) z` pointwise in
`z` (chosen branch) — from `g₀ ≥ 0` a.e., `χ ≥ 0`, `χ⋆χ ≥ 0` and
`w₁(x,y) ≥ 0` for a.e. `y`. -/
lemma w1Fibre_nonneg {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (z : ℝ³) :
    0 ≤ w1Fibre ℓ (wPairC ℓ (g0 v h)) z := by
  classical
  change 0 ≤ ∫ y in acube ℓ, wPair ℓ (g0 v h) z y
  have hnn_y : ∀ᵐ y ∂(volume : Measure ℝ³), 0 ≤ g0 v h (z - y) := by
    simpa using (ae_comp_sub_left (g0_nonneg_ae hR hv_nonneg hvrad hv_supp h) z)
  have hrestrict : ∀ᵐ y ∂(volume.restrict (acube ℓ)), 0 ≤ wPair ℓ (g0 v h) z y := by
    rw [ae_restrict_iff' (acube_measurable ℓ)]
    filter_upwards [hnn_y] with y hy
    intro _
    have hcsx : 0 ≤ chiScale ℓ z := chiScale_nonneg ℓ z
    have hcsy : 0 ≤ chiScale ℓ y := chiScale_nonneg ℓ y
    have hdiv : 0 ≤ g0 v h (z - y) / convScale ℓ (z - y) :=
      div_nonneg hy (convScale_nonneg ℓ (z - y))
    dsimp [wPair, wScaled]
    exact mul_nonneg (mul_nonneg hcsx hdiv) hcsy
  exact integral_nonneg_of_ae hrestrict
/-- **Per-slot AM–GM CS on the scalar-weighted w₁-cross (all-Φ)**: for any
real `t`, from the pointwise `(t·P_iΦ + Q_iΦ)²·f₁(x_i) ≥ 0` (`f₁ ≥ 0`),
summing over `i` and using `Σ_i∫(P_iΦ)²f₁ = 8πa·S` (`onebody_mass_condensate`):

`2·t·OB₁ ≥ −t²·8πa·S − qOneMass`

(`S := cS1`, `qOneMass := Σ_i∫(Q_iΦ)²f₁`).  Instantiate `t := N̂/ℓ³ − μ`
with `q1_w1line_scalar_split` for the Step-4 CS. -/
lemma q1_cross_w1_cs {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {t : ℝ}
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    2 * t * (∑ i : Fin N, ∫ x in abox N ℓ,
        (aQ ℓ i Φ x) * (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)))
    ≥ - t ^ 2 * ((8 * π * a v) * cS1 ℓ Φ)
      - qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ) := by
  classical
  let f1 : ℝ³ → ℝ := fun z => w1Fibre ℓ (wPairC ℓ (g0 v h)) z
  let C0 : ℝ := chiSup ^ 2 * 2 * (8 * π * a v)
  have hf1b : ∀ z : ℝ³, z ∈ acube ℓ → |f1 z| ≤ C0 := by
    intro z hz
    dsimp [f1, C0]
    have hb := w1c_fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ z
    simpa [w1Fibre, wPairC] using hb
  have hf1m : AEStronglyMeasurable f1 (volume.restrict (acube ℓ)) := by
    dsimp [f1]
    have hfac := fibre_acube_aem (ℓ := ℓ) (h := g0 v h) (g0_integrable hR hv_supp h)
    simpa [w1Fibre, wPairC] using hfac
  have hf1nn : ∀ z : ℝ³, 0 ≤ f1 z := by
    intro z
    dsimp [f1]
    exact w1Fibre_nonneg hR hv_nonneg hvrad hv_supp h z
  -- per-i pointwise: (t·P + Q)²·f1(x i) ≥ 0
  have hper : ∀ i : Fin N,
      0 ≤ ∫ x in abox N ℓ,
          (t * (aP ℓ i Φ x) + (aQ ℓ i Φ x)) ^ 2 * f1 (x i) := by
    intro i
    have hSc : Continuous (fun x : X N => (t * (aP ℓ i Φ x) + (aQ ℓ i Φ x)) ^ 2) := by
      have h1 : Continuous (fun x : X N => t * (aP ℓ i Φ x) + (aQ ℓ i Φ x)) :=
        ((continuous_const.mul (aP_continuous hℓ i hΦc))).add (aQ_continuous hℓ i hΦc)
      exact h1.pow 2
    have hInt : IntegrableOn (fun x => (t * (aP ℓ i Φ x) + (aQ ℓ i Φ x)) ^ 2 * f1 (x i))
        (abox N ℓ) volume := by
      have hb := integrableOn_slot_fibre hℓ i hf1m (fun z hz => hf1b z hz) hSc
      simpa [mul_assoc] using hb
    refine integral_nonneg_of_ae ?_
    have hnn_i : ∀ᵐ x ∂(volume.restrict (abox N ℓ)), 0 ≤ f1 (x i) := by
      rw [ae_restrict_iff' (abox_measurable N ℓ)]
      exact ae_of_all _ (fun x hx => hf1nn (x i))
    filter_upwards [hnn_i] with x hx
    exact mul_nonneg (sq_nonneg (t * (aP ℓ i Φ x) + (aQ ℓ i Φ x))) hx
  -- expand the square: (tP+Q)²f1 = t²P²f1 + 2tPQf1 + Q²f1
  have hsq (i : Fin N) :
      (∫ x in abox N ℓ, (t * (aP ℓ i Φ x) + (aQ ℓ i Φ x)) ^ 2 * f1 (x i))
      = t ^ 2 * (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2 * f1 (x i))
        + 2 * t * (∫ x in abox N ℓ, (aP ℓ i Φ x) * (aQ ℓ i Φ x) * f1 (x i))
        + (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * f1 (x i)) := by
    have hPc : Continuous (fun x : X N => aP ℓ i Φ x) := aP_continuous hℓ i hΦc
    have hQc : Continuous (fun x : X N => aQ ℓ i Φ x) := aQ_continuous hℓ i hΦc
    have hI_P2 : IntegrableOn (fun x => (aP ℓ i Φ x) ^ 2 * f1 (x i)) (abox N ℓ) volume := by
      exact integrableOn_slot_fibre hℓ i hf1m (fun z hz => hf1b z hz) (hPc.pow 2)
    have hI_PQ : IntegrableOn (fun x => (aP ℓ i Φ x) * (aQ ℓ i Φ x) * f1 (x i))
        (abox N ℓ) volume := by
      exact integrableOn_slot_fibre hℓ i hf1m (fun z hz => hf1b z hz) (hPc.mul hQc)
    have hI_Q2 : IntegrableOn (fun x => (aQ ℓ i Φ x) ^ 2 * f1 (x i)) (abox N ℓ) volume := by
      exact integrableOn_slot_fibre hℓ i hf1m (fun z hz => hf1b z hz) (hQc.pow 2)
    have hpt : (fun x : X N => (t * (aP ℓ i Φ x) + (aQ ℓ i Φ x)) ^ 2 * f1 (x i))
        =ᵐ[volume.restrict (abox N ℓ)] fun x : X N =>
            t ^ 2 * ((aP ℓ i Φ x) ^ 2 * f1 (x i))
              + 2 * t * ((aP ℓ i Φ x) * (aQ ℓ i Φ x) * f1 (x i))
              + (aQ ℓ i Φ x) ^ 2 * f1 (x i) := by
      refine ae_of_all _ (fun x => ?_)
      ring
    have hmain : (∫ x in abox N ℓ, (t * (aP ℓ i Φ x) + (aQ ℓ i Φ x)) ^ 2 * f1 (x i))
        = (∫ x in abox N ℓ,
            t ^ 2 * ((aP ℓ i Φ x) ^ 2 * f1 (x i))
              + 2 * t * ((aP ℓ i Φ x) * (aQ ℓ i Φ x) * f1 (x i))
              + (aQ ℓ i Φ x) ^ 2 * f1 (x i)) := by
      apply integral_congr_ae
      exact hpt
    have hP2r : Integrable (fun x => (aP ℓ i Φ x) ^ 2 * f1 (x i))
        (volume.restrict (abox N ℓ)) := by simpa [IntegrableOn] using hI_P2
    have hPQr : Integrable (fun x => (aP ℓ i Φ x) * (aQ ℓ i Φ x) * f1 (x i))
        (volume.restrict (abox N ℓ)) := by simpa [IntegrableOn] using hI_PQ
    have hI1 : Integrable (fun x => t ^ 2 * ((aP ℓ i Φ x) ^ 2 * f1 (x i)))
        (volume.restrict (abox N ℓ)) := hP2r.const_mul (t ^ 2)
    have hI2 : Integrable (fun x => 2 * t * ((aP ℓ i Φ x) * (aQ ℓ i Φ x) * f1 (x i)))
        (volume.restrict (abox N ℓ)) := by
      have hb := hPQr.const_mul (2 * t)
      simpa [mul_assoc] using hb
    have hI12 : Integrable (fun x =>
          t ^ 2 * ((aP ℓ i Φ x) ^ 2 * f1 (x i))
            + 2 * t * ((aP ℓ i Φ x) * (aQ ℓ i Φ x) * f1 (x i)))
        (volume.restrict (abox N ℓ)) := hI1.add hI2
    have hI123 : Integrable (fun x =>
          (t ^ 2 * ((aP ℓ i Φ x) ^ 2 * f1 (x i))
            + 2 * t * ((aP ℓ i Φ x) * (aQ ℓ i Φ x) * f1 (x i)))
            + (aQ ℓ i Φ x) ^ 2 * f1 (x i))
        (volume.restrict (abox N ℓ)) := hI12.add hI_Q2
    calc
      (∫ x in abox N ℓ, (t * (aP ℓ i Φ x) + (aQ ℓ i Φ x)) ^ 2 * f1 (x i))
          = (∫ x in abox N ℓ,
              (t ^ 2 * ((aP ℓ i Φ x) ^ 2 * f1 (x i))
                + 2 * t * ((aP ℓ i Φ x) * (aQ ℓ i Φ x) * f1 (x i)))
                + (aQ ℓ i Φ x) ^ 2 * f1 (x i)) := by
              apply integral_congr_ae
              refine ae_of_all _ (fun x => ?_)
              ring
      _ = (∫ x in abox N ℓ,
              t ^ 2 * ((aP ℓ i Φ x) ^ 2 * f1 (x i))
                + 2 * t * ((aP ℓ i Φ x) * (aQ ℓ i Φ x) * f1 (x i)))
          + (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * f1 (x i)) := by
              have hI_Q2' : Integrable (fun x => (aQ ℓ i Φ x) ^ 2 * f1 (x i))
                  (volume.restrict (abox N ℓ)) := by simpa [IntegrableOn] using hI_Q2
              rw [integral_add hI12 hI_Q2']
      _ = (∫ x in abox N ℓ, t ^ 2 * ((aP ℓ i Φ x) ^ 2 * f1 (x i)))
          + (∫ x in abox N ℓ, 2 * t * ((aP ℓ i Φ x) * (aQ ℓ i Φ x) * f1 (x i)))
          + (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * f1 (x i)) := by
              rw [integral_add hI1 hI2]
      _ = t ^ 2 * (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2 * f1 (x i))
          + 2 * t * (∫ x in abox N ℓ, (aP ℓ i Φ x) * (aQ ℓ i Φ x) * f1 (x i))
          + (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * f1 (x i)) := by
              rw [integral_const_mul, integral_const_mul]
  -- assemble over i
  have hsum0 : 0 ≤ (∑ i : Fin N, ∫ x in abox N ℓ,
        (t * (aP ℓ i Φ x) + (aQ ℓ i Φ x)) ^ 2 * f1 (x i)) := by
    exact Finset.sum_nonneg (fun i hi => hper i)
  have hsumsq : (∑ i : Fin N, ∫ x in abox N ℓ,
        (t * (aP ℓ i Φ x) + (aQ ℓ i Φ x)) ^ 2 * f1 (x i))
      = t ^ 2 * (∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2 * f1 (x i))
        + 2 * t * (∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i Φ x) * (aQ ℓ i Φ x) * f1 (x i))
        + (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * f1 (x i)) := by
    calc
      (∑ i : Fin N, ∫ x in abox N ℓ, (t * (aP ℓ i Φ x) + (aQ ℓ i Φ x)) ^ 2 * f1 (x i))
          = ∑ i : Fin N,
              (t ^ 2 * (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2 * f1 (x i))
                + 2 * t * (∫ x in abox N ℓ, (aP ℓ i Φ x) * (aQ ℓ i Φ x) * f1 (x i))
                + (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * f1 (x i))) := by
              exact Finset.sum_congr rfl (fun i hi => hsq i)
      _ = (∑ i : Fin N,
              (t ^ 2 * (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2 * f1 (x i))
                + 2 * t * (∫ x in abox N ℓ, (aP ℓ i Φ x) * (aQ ℓ i Φ x) * f1 (x i))))
          + (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * f1 (x i)) := by
              rw [Finset.sum_add_distrib]
      _ = (t ^ 2 * (∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2 * f1 (x i))
            + 2 * t * (∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i Φ x) * (aQ ℓ i Φ x) * f1 (x i)))
          + (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * f1 (x i)) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = t ^ 2 * (∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2 * f1 (x i))
          + 2 * t * (∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i Φ x) * (aQ ℓ i Φ x) * f1 (x i))
          + (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * f1 (x i)) := by
              ring
  have hsumP : (∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2 * f1 (x i))
      = (8 * π * a v) * cS1 ℓ Φ := by
    have hmm := onebody_mass_condensate hℓ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc
    -- hmm : Σ∫(P)²·w1Fibre(wPairC(g0)) = 8πa·cS1
    simpa [f1] using hmm
  have hsumQ : (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * f1 (x i))
      = qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ) := by
    simp [qOneMass, f1]
  have hOrder : (∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i Φ x) * (aQ ℓ i Φ x) * f1 (x i))
      = (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f1 (x i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply integral_congr_ae
    refine ae_of_all _ (fun x => ?_)
    ring
  have hmain : 0 ≤ t ^ 2 * ((8 * π * a v) * cS1 ℓ Φ)
        + 2 * t * (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f1 (x i))
        + qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ) := by
    have hsumsq' : (∑ i : Fin N, ∫ x in abox N ℓ,
          (t * (aP ℓ i Φ x) + (aQ ℓ i Φ x)) ^ 2 * f1 (x i))
        = t ^ 2 * ((8 * π * a v) * cS1 ℓ Φ)
          + 2 * t * (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f1 (x i))
          + qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ) := by
      rw [hsumsq, hsumP, hsumQ, hOrder]
    rw [← hsumsq']
    exact hsum0
  -- final: 2t·OB ≥ −t²8πa·S − qOneMass
  have hOB : (∑ i : Fin N, ∫ x in abox N ℓ,
        (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f1 (x i))
      = (∑ i : Fin N, ∫ x in abox N ℓ,
        (aQ ℓ i Φ x) * (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i))) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply integral_congr_ae
    refine ae_of_all _ (fun x => ?_)
    dsimp [f1]
  nlinarith [hmain]

/-! ## Session-152: the CS applied into scoped form — `pot_sharp_w1line_cs`

`pot_sharp_w1line_cs` (all-Φ, machine-checked): combining `pot_sharp_w1line`
(w₁-line exact), `q1_w1line_scalar_split` (the exact scalar split), and
`q1_cross_w1_cs` at `t := u−μ`:

`qLHSword ≥ q0RenVal − (u−μ)²·8πa·S − qOneMass − 2·(ℓ³)⁻¹·Corr − masses`

(`u := N̂/ℓ³`, `S := cS1`).  This is the WINDOWED STEP-4 in scoped form:
q0RenVal (to be square-completed against the `(u−μ)²`-quadratic via
`A0Core.a0_form_square_identity`), the `qOneMass`/`Corr`/mass terms (to be
absorbed by the kinetic gap under the a-priori window (w1)-(w3)).  The final
windowed assembly then adds `kinWord` and the window hypotheses.
-/
/-- **Windowed Step-4: CS applied into scoped form (all-Φ)** — combining
`pot_sharp_w1line` (w₁-line exact), `q1_w1line_scalar_split` (the exact
scalar split `w₁-line − 2μOB₁ = 2(u−μ)OB₁ − 2(ℓ³)⁻¹Corr`), and
`q1_cross_w1_cs` (per-slot AM–GM at `t := u−μ`):

`qLHSword ≥ q0RenVal − (u−μ)²·8πa·S − qOneMass − 2·(ℓ³)⁻¹·Corr − masses`

(`u := N̂/ℓ³`, `S := cS1`, `masses` = the `pot_sharp_w1line` tail).  This is
the scoped input to the final windowed step: square-complete `q0RenVal`
against the `(u−μ)²`-quadratic (`A0Core.a0_form_square_identity`) and absorb
`qOneMass`, `Corr` and the masses by the kinetic gap under the a-priori
window. -/
lemma pot_sharp_w1line_cs {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ) (hμ : 0 ≤ μ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ ≥
      q0RenVal (N := N) (v := v) ℓ μ Φ
      - (((N : ℝ) / ℓ ^ 3) - μ) ^ 2 * ((8 * π * a v) * cS1 ℓ Φ)
      - qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ)
      - 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
          (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)) *
            (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x))
      - 2 * (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (4 * cS2 ℓ Φ + 3 * ((N : ℝ) * cnPlus ℓ Φ))
      - (8 / 3) * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - 2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - 2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - μ * (fsqC1 (a v)) * cnPlus ℓ Φ := by
  classical
  let L1 : ℝ := 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
      (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)) *
        (aQ ℓ i (fun y : X N => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0))) x)
  let OB : ℝ := ∑ i : Fin N, ∫ x in abox N ℓ,
      (aQ ℓ i Φ x) * (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i))
  let Corr : ℝ := ∑ i : Fin N, ∫ x in abox N ℓ,
      (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)) * (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x)
  let qOneM : ℝ := qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ)
  have hp := pot_sharp_w1line hℓ hμ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc
  have hp' : qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ ≥
      q0RenVal (N := N) (v := v) ℓ μ Φ + L1 - 2 * μ * OB
        - 2 * (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
        - (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (4 * cS2 ℓ Φ + 3 * ((N : ℝ) * cnPlus ℓ Φ))
        - (8 / 3) * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
        - 2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
        - 2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
        - μ * (fsqC1 (a v)) * cnPlus ℓ Φ := by
    simpa [L1, OB] using hp
  have hsplit := q1_w1line_scalar_split (N := N) (μ := μ) hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
  have hsplit' : L1 - 2 * μ * OB
      = 2 * (((N : ℝ) / ℓ ^ 3) - μ) * OB - 2 * (ℓ ^ 3)⁻¹ * Corr := by
    simpa [L1, OB, Corr] using hsplit
  have hcs := q1_cross_w1_cs hℓ (t := ((N : ℝ) / ℓ ^ 3) - μ)
    hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc
  have hcs' : 2 * (((N : ℝ) / ℓ ^ 3) - μ) * OB
      ≥ - (((N : ℝ) / ℓ ^ 3) - μ) ^ 2 * ((8 * π * a v) * cS1 ℓ Φ)
        - qOneM := by
    simpa [OB, qOneM] using hcs
  have hgoal : q0RenVal (N := N) (v := v) ℓ μ Φ + L1 - 2 * μ * OB
      - 2 * (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (4 * cS2 ℓ Φ + 3 * ((N : ℝ) * cnPlus ℓ Φ))
      - (8 / 3) * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - 2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - 2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - μ * (fsqC1 (a v)) * cnPlus ℓ Φ
    ≥ q0RenVal (N := N) (v := v) ℓ μ Φ
      - (((N : ℝ) / ℓ ^ 3) - μ) ^ 2 * ((8 * π * a v) * cS1 ℓ Φ)
      - qOneM - 2 * (ℓ ^ 3)⁻¹ * Corr
      - 2 * (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (4 * cS2 ℓ Φ + 3 * ((N : ℝ) * cnPlus ℓ Φ))
      - (8 / 3) * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - 2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - 2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - μ * (fsqC1 (a v)) * cnPlus ℓ Φ := by
    nlinarith [hsplit', hcs']

  have hfin : q0RenVal (N := N) (v := v) ℓ μ Φ
        - (((N : ℝ) / ℓ ^ 3) - μ) ^ 2 * ((8 * π * a v) * cS1 ℓ Φ)
        - qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ)
        - 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
            (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)) *
              (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x))
        - 2 * (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
        - (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (4 * cS2 ℓ Φ + 3 * ((N : ℝ) * cnPlus ℓ Φ))
        - (8 / 3) * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
        - 2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
        - 2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
        - μ * (fsqC1 (a v)) * cnPlus ℓ Φ
      ≤ qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ := by
    dsimp [L1, OB, Corr, qOneM] at hp' hgoal
    simpa [Corr, qOneM] using (le_trans hgoal hp')
  simpa using hfin
/-- **FS-shape cross CS (the (b)-brick, all-Φ)**: the free-ε AM–GM at
`ε := V/(4S)` (`V := ℓ³`, `S := cS1 > 0`) shrinks the P-quadratic to FS's
exact `−¼t²·8πaV` form while the Q-part stays LINEAR with coefficient
`4S/V`: `2t·OB₁ ≥ −¼·t²·8πa·V − (4S/V)·qOneMass`.

Proof: per-slot `0 ≤ ∫ (V·t·P + 4S·Q)²·f₁`; expanding and summing gives
`0 ≤ V²t²·8πaS + 8VSt·OB₁ + 16S²·qOneMass = 4SV·[¼t²·8πaV + 2t·OB₁ + (4S/V)qOneMass]`;
divide by `4SV > 0` (`nonneg_of_mul_nonneg_left`).  No √-algebra needed. -/
lemma q1_cross_w1_cs_fs {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {t : ℝ}
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : X N → ℝ} (hΦc : Continuous Φ)
    (hS : 0 < cS1 ℓ Φ) :
    2 * t * (∑ i : Fin N, ∫ x in abox N ℓ,
        (aQ ℓ i Φ x) * (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)))
    ≥ - (1 / 4) * t ^ 2 * ((8 * π * (a v)) * ℓ ^ 3)
      - (4 * (cS1 ℓ Φ) / ℓ ^ 3) * qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ) := by
  classical
  let f1 : ℝ³ → ℝ := fun z => w1Fibre ℓ (wPairC ℓ (g0 v h)) z
  let C0 : ℝ := chiSup ^ 2 * 2 * (8 * π * a v)
  let V : ℝ := ℓ ^ 3
  let S : ℝ := cS1 ℓ Φ
  have hV : 0 < V := by dsimp [V]; positivity
  have hS' : 0 < S := by simpa [S] using hS
  have hV1 : V ≠ 0 := ne_of_gt hV
  have hS1 : S ≠ 0 := ne_of_gt hS'
  have hf1b : ∀ z : ℝ³, z ∈ acube ℓ → |f1 z| ≤ C0 := by
    intro z hz
    dsimp [f1, C0]
    have hb := w1c_fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ z
    simpa [w1Fibre, wPairC] using hb
  have hf1m : AEStronglyMeasurable f1 (volume.restrict (acube ℓ)) := by
    dsimp [f1]
    have hfac := fibre_acube_aem (ℓ := ℓ) (h := g0 v h) (g0_integrable hR hv_supp h)
    simpa [w1Fibre, wPairC] using hfac
  have hf1nn : ∀ z : ℝ³, 0 ≤ f1 z := by
    intro z
    dsimp [f1]
    exact w1Fibre_nonneg hR hv_nonneg hvrad hv_supp h z
  -- per-i pointwise: (V·t·P + 4S·Q)²·f1(x i) ≥ 0
  have hper : ∀ i : Fin N,
      0 ≤ ∫ x in abox N ℓ,
          (V * t * (aP ℓ i Φ x) + (4 * S) * (aQ ℓ i Φ x)) ^ 2 * f1 (x i) := by
    intro i
    have hSc : Continuous (fun x : X N => (V * t * (aP ℓ i Φ x) + (4 * S) * (aQ ℓ i Φ x)) ^ 2) := by
      have h1 : Continuous (fun x : X N => V * t * (aP ℓ i Φ x) + (4 * S) * (aQ ℓ i Φ x)) :=
        (((continuous_const.mul continuous_const).mul (aP_continuous hℓ i hΦc))).add
          (continuous_const.mul (aQ_continuous hℓ i hΦc))
      exact h1.pow 2
    have hInt : IntegrableOn (fun x => (V * t * (aP ℓ i Φ x) + (4 * S) * (aQ ℓ i Φ x)) ^ 2 * f1 (x i))
        (abox N ℓ) volume := by
      have hb := integrableOn_slot_fibre hℓ i hf1m (fun z hz => hf1b z hz) hSc
      simpa [mul_assoc] using hb
    refine integral_nonneg_of_ae ?_
    have hnn_i : ∀ᵐ x ∂(volume.restrict (abox N ℓ)), 0 ≤ f1 (x i) := by
      rw [ae_restrict_iff' (abox_measurable N ℓ)]
      exact ae_of_all _ (fun x hx => hf1nn (x i))
    filter_upwards [hnn_i] with x hx
    exact mul_nonneg (sq_nonneg (V * t * (aP ℓ i Φ x) + (4 * S) * (aQ ℓ i Φ x))) hx
  -- expand the square: (VtP+4SQ)²f1 = V²t²·P²f1 + 8VSt·PQf1 + 16S²·Q²f1
  have hsq (i : Fin N) :
      (∫ x in abox N ℓ, (V * t * (aP ℓ i Φ x) + (4 * S) * (aQ ℓ i Φ x)) ^ 2 * f1 (x i))
      = (V ^ 2 * t ^ 2) * (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2 * f1 (x i))
        + (8 * V * S * t) * (∫ x in abox N ℓ, (aP ℓ i Φ x) * (aQ ℓ i Φ x) * f1 (x i))
        + (16 * S ^ 2) * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * f1 (x i)) := by
    have hPc : Continuous (fun x : X N => aP ℓ i Φ x) := aP_continuous hℓ i hΦc
    have hQc : Continuous (fun x : X N => aQ ℓ i Φ x) := aQ_continuous hℓ i hΦc
    have hI_P2 : IntegrableOn (fun x => (aP ℓ i Φ x) ^ 2 * f1 (x i)) (abox N ℓ) volume := by
      exact integrableOn_slot_fibre hℓ i hf1m (fun z hz => hf1b z hz) (hPc.pow 2)
    have hI_PQ : IntegrableOn (fun x => (aP ℓ i Φ x) * (aQ ℓ i Φ x) * f1 (x i))
        (abox N ℓ) volume := by
      exact integrableOn_slot_fibre hℓ i hf1m (fun z hz => hf1b z hz) (hPc.mul hQc)
    have hI_Q2 : IntegrableOn (fun x => (aQ ℓ i Φ x) ^ 2 * f1 (x i)) (abox N ℓ) volume := by
      exact integrableOn_slot_fibre hℓ i hf1m (fun z hz => hf1b z hz) (hQc.pow 2)
    have hpt : (fun x : X N => (V * t * (aP ℓ i Φ x) + (4 * S) * (aQ ℓ i Φ x)) ^ 2 * f1 (x i))
        =ᵐ[volume.restrict (abox N ℓ)] fun x : X N =>
            (V ^ 2 * t ^ 2) * ((aP ℓ i Φ x) ^ 2 * f1 (x i))
              + (8 * V * S * t) * ((aP ℓ i Φ x) * (aQ ℓ i Φ x) * f1 (x i))
              + (16 * S ^ 2) * ((aQ ℓ i Φ x) ^ 2 * f1 (x i)) := by
      refine ae_of_all _ (fun x => ?_)
      ring
    have hmain0 : (∫ x in abox N ℓ, (V * t * (aP ℓ i Φ x) + (4 * S) * (aQ ℓ i Φ x)) ^ 2 * f1 (x i))
        = (∫ x in abox N ℓ,
            (V ^ 2 * t ^ 2) * ((aP ℓ i Φ x) ^ 2 * f1 (x i))
              + (8 * V * S * t) * ((aP ℓ i Φ x) * (aQ ℓ i Φ x) * f1 (x i))
              + (16 * S ^ 2) * ((aQ ℓ i Φ x) ^ 2 * f1 (x i))) := by
      apply integral_congr_ae
      exact hpt
    have hP2r : Integrable (fun x => (aP ℓ i Φ x) ^ 2 * f1 (x i))
        (volume.restrict (abox N ℓ)) := by simpa [IntegrableOn] using hI_P2
    have hPQr : Integrable (fun x => (aP ℓ i Φ x) * (aQ ℓ i Φ x) * f1 (x i))
        (volume.restrict (abox N ℓ)) := by simpa [IntegrableOn] using hI_PQ
    have hQ2r : Integrable (fun x => (aQ ℓ i Φ x) ^ 2 * f1 (x i))
        (volume.restrict (abox N ℓ)) := by simpa [IntegrableOn] using hI_Q2
    have hI1 : Integrable (fun x => (V ^ 2 * t ^ 2) * ((aP ℓ i Φ x) ^ 2 * f1 (x i)))
        (volume.restrict (abox N ℓ)) := hP2r.const_mul (V ^ 2 * t ^ 2)
    have hI2 : Integrable (fun x => (8 * V * S * t) * ((aP ℓ i Φ x) * (aQ ℓ i Φ x) * f1 (x i)))
        (volume.restrict (abox N ℓ)) := by
      have hb := hPQr.const_mul (8 * V * S * t)
      simpa [mul_assoc] using hb
    have hI3 : Integrable (fun x => (16 * S ^ 2) * ((aQ ℓ i Φ x) ^ 2 * f1 (x i)))
        (volume.restrict (abox N ℓ)) := hQ2r.const_mul (16 * S ^ 2)
    have hI12 : Integrable (fun x =>
          (V ^ 2 * t ^ 2) * ((aP ℓ i Φ x) ^ 2 * f1 (x i))
            + (8 * V * S * t) * ((aP ℓ i Φ x) * (aQ ℓ i Φ x) * f1 (x i)))
        (volume.restrict (abox N ℓ)) := hI1.add hI2
    calc
      (∫ x in abox N ℓ, (V * t * (aP ℓ i Φ x) + (4 * S) * (aQ ℓ i Φ x)) ^ 2 * f1 (x i))
          = (∫ x in abox N ℓ,
              ((V ^ 2 * t ^ 2) * ((aP ℓ i Φ x) ^ 2 * f1 (x i))
                + (8 * V * S * t) * ((aP ℓ i Φ x) * (aQ ℓ i Φ x) * f1 (x i)))
                + (16 * S ^ 2) * ((aQ ℓ i Φ x) ^ 2 * f1 (x i))) := by
              apply integral_congr_ae
              refine ae_of_all _ (fun x => ?_)
              ring
      _ = (∫ x in abox N ℓ,
              (V ^ 2 * t ^ 2) * ((aP ℓ i Φ x) ^ 2 * f1 (x i))
                + (8 * V * S * t) * ((aP ℓ i Φ x) * (aQ ℓ i Φ x) * f1 (x i)))
          + (∫ x in abox N ℓ, (16 * S ^ 2) * ((aQ ℓ i Φ x) ^ 2 * f1 (x i))) := by
              rw [integral_add hI12 hI3]
      _ = (∫ x in abox N ℓ, (V ^ 2 * t ^ 2) * ((aP ℓ i Φ x) ^ 2 * f1 (x i)))
          + (∫ x in abox N ℓ, (8 * V * S * t) * ((aP ℓ i Φ x) * (aQ ℓ i Φ x) * f1 (x i)))
          + (∫ x in abox N ℓ, (16 * S ^ 2) * ((aQ ℓ i Φ x) ^ 2 * f1 (x i))) := by
              rw [integral_add hI1 hI2]
      _ = (V ^ 2 * t ^ 2) * (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2 * f1 (x i))
          + (8 * V * S * t) * (∫ x in abox N ℓ, (aP ℓ i Φ x) * (aQ ℓ i Φ x) * f1 (x i))
          + (16 * S ^ 2) * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * f1 (x i)) := by
              rw [integral_const_mul, integral_const_mul, integral_const_mul]
  -- assemble over i
  have hsum0 : 0 ≤ (∑ i : Fin N, ∫ x in abox N ℓ,
        (V * t * (aP ℓ i Φ x) + (4 * S) * (aQ ℓ i Φ x)) ^ 2 * f1 (x i)) := by
    exact Finset.sum_nonneg (fun i hi => hper i)
  have hsumsq : (∑ i : Fin N, ∫ x in abox N ℓ,
        (V * t * (aP ℓ i Φ x) + (4 * S) * (aQ ℓ i Φ x)) ^ 2 * f1 (x i))
      = (V ^ 2 * t ^ 2) * (∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2 * f1 (x i))
        + (8 * V * S * t) * (∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i Φ x) * (aQ ℓ i Φ x) * f1 (x i))
        + (16 * S ^ 2) * (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * f1 (x i)) := by
    calc
      (∑ i : Fin N, ∫ x in abox N ℓ, (V * t * (aP ℓ i Φ x) + (4 * S) * (aQ ℓ i Φ x)) ^ 2 * f1 (x i))
          = ∑ i : Fin N,
              (((V ^ 2 * t ^ 2) * (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2 * f1 (x i))
                + (8 * V * S * t) * (∫ x in abox N ℓ, (aP ℓ i Φ x) * (aQ ℓ i Φ x) * f1 (x i)))
                + (16 * S ^ 2) * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * f1 (x i))) := by
              exact Finset.sum_congr rfl (fun i hi => hsq i)
      _ = (∑ i : Fin N,
              ((V ^ 2 * t ^ 2) * (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2 * f1 (x i))
                + (8 * V * S * t) * (∫ x in abox N ℓ, (aP ℓ i Φ x) * (aQ ℓ i Φ x) * f1 (x i))))
          + (∑ i : Fin N, (16 * S ^ 2) * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * f1 (x i))) := by
              rw [Finset.sum_add_distrib]
      _ = ((V ^ 2 * t ^ 2) * (∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2 * f1 (x i))
            + (8 * V * S * t) * (∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i Φ x) * (aQ ℓ i Φ x) * f1 (x i)))
          + (16 * S ^ 2) * (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * f1 (x i)) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = (V ^ 2 * t ^ 2) * (∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2 * f1 (x i))
          + (8 * V * S * t) * (∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i Φ x) * (aQ ℓ i Φ x) * f1 (x i))
          + (16 * S ^ 2) * (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * f1 (x i)) := by
              ring
  have hsumP : (∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2 * f1 (x i))
      = (8 * π * a v) * S := by
    have hmm := onebody_mass_condensate hℓ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc
    simpa [f1, S] using hmm
  have hsumQ : (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * f1 (x i))
      = qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ) := by
    simp [qOneMass, f1]
  have hOrder : (∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i Φ x) * (aQ ℓ i Φ x) * f1 (x i))
      = (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f1 (x i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply integral_congr_ae
    refine ae_of_all _ (fun x => ?_)
    ring
  have hmain : 0 ≤ (V ^ 2 * t ^ 2) * ((8 * π * a v) * S)
        + (8 * V * S * t) * (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f1 (x i))
        + (16 * S ^ 2) * qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ) := by
    have hsumsq' : (∑ i : Fin N, ∫ x in abox N ℓ,
          (V * t * (aP ℓ i Φ x) + (4 * S) * (aQ ℓ i Φ x)) ^ 2 * f1 (x i))
        = (V ^ 2 * t ^ 2) * ((8 * π * a v) * S)
          + (8 * V * S * t) * (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f1 (x i))
          + (16 * S ^ 2) * qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ) := by
      rw [hsumsq, hsumP, hsumQ, hOrder]
    rw [← hsumsq']
    exact hsum0
  -- division by 4·S·V > 0
  have hpos : 0 < (4 * S) * V := by positivity
  have hdiv : 0 ≤ (1 / 4) * t ^ 2 * ((8 * π * (a v)) * V)
        + 2 * t * (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f1 (x i))
        + ((4 * S) / V) * qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ) := by
    apply nonneg_of_mul_nonneg_left _ hpos
    have heq : ((1 / 4) * t ^ 2 * ((8 * π * (a v)) * V)
          + 2 * t * (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f1 (x i))
          + ((4 * S) / V) * qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ)) * ((4 * S) * V)
        = (V ^ 2 * t ^ 2) * ((8 * π * a v) * S)
          + (8 * V * S * t) * (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f1 (x i))
          + (16 * S ^ 2) * qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ) := by
      field_simp [hV1, hS1]
      ring
    rw [heq]
    exact hmain
  -- final: convert f1 sum to w1Fibre sum, unfold V S, rearrange
  have hOB : (∑ i : Fin N, ∫ x in abox N ℓ,
        (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f1 (x i))
      = (∑ i : Fin N, ∫ x in abox N ℓ,
        (aQ ℓ i Φ x) * (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i))) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply integral_congr_ae
    refine ae_of_all _ (fun x => ?_)
    dsimp [f1]
  rw [hOB] at hdiv
  have hfin : 0 ≤ (1 / 4) * t ^ 2 * ((8 * π * (a v)) * ℓ ^ 3)
        + 2 * t * (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) * (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)))
        + ((4 * (cS1 ℓ Φ)) / ℓ ^ 3) * qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ) := by
    simpa [V, S] using hdiv
  nlinarith
/-- **FS-shape (b)-bound: CS applied into scoped form (all-Φ)** — combining
`pot_sharp_w1line` (w₁-line exact), `q1_w1line_scalar_split` (the exact
scalar split `w₁-line − 2μOB₁ = 2(u−μ)OB₁ − 2(ℓ³)⁻¹Corr`), and
`q1_cross_w1_cs_fs` (the FS-shape per-slot AM–GM at `t := u−μ`,
`ε := V/(4S)`, `V := ℓ³`, `S := cS1` — machine-checked Session-155):

`qLHSword ≥ q0RenVal − ¼·(u−μ)²·8πa·V − (4S/V)·qOneMass − 2·(ℓ³)⁻¹·Corr − masses`

(`u := N̂/ℓ³`, `masses` = the `pot_sharp_w1line` tail).  This is the scoped
input to the final windowed step: square-complete `q0RenVal` against the
`¼(u−μ)²`-quadratic (the `u`-CONVEX FS form — the Session-153 concavity
obstruction is resolved, see `Step4SqrtFactorisation`) and absorb the
`(4S/V)·qOneMass`, `Corr` and the masses by the kinetic gap under the a-priori
window. -/
lemma pot_sharp_w1line_cs_fs {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ) (hμ : 0 ≤ μ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : X N → ℝ} (hΦc : Continuous Φ)
    (hSc1 : 0 < cS1 ℓ Φ) :
    qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ ≥
      q0RenVal (N := N) (v := v) ℓ μ Φ
      - (1 / 4) * ((((N : ℝ) / ℓ ^ 3) - μ) ^ 2) * ((8 * π * (a v)) * ℓ ^ 3)
      - ((4 * (cS1 ℓ Φ)) / ℓ ^ 3) * qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ)
      - 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
          (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)) *
            (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x))
      - 2 * (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (4 * cS2 ℓ Φ + 3 * ((N : ℝ) * cnPlus ℓ Φ))
      - (8 / 3) * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - 2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - 2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - μ * (fsqC1 (a v)) * cnPlus ℓ Φ := by
  classical
  let L1 : ℝ := 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
      (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)) *
        (aQ ℓ i (fun y : X N => (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0))) x)
  let OB : ℝ := ∑ i : Fin N, ∫ x in abox N ℓ,
      (aQ ℓ i Φ x) * (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i))
  let Corr : ℝ := ∑ i : Fin N, ∫ x in abox N ℓ,
      (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)) * (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x)
  let qOneM : ℝ := qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ)
  have hp := pot_sharp_w1line hℓ hμ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc
  have hp' : qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ ≥
      q0RenVal (N := N) (v := v) ℓ μ Φ + L1 - 2 * μ * OB
        - 2 * (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
        - (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (4 * cS2 ℓ Φ + 3 * ((N : ℝ) * cnPlus ℓ Φ))
        - (8 / 3) * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
        - 2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
        - 2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
        - μ * (fsqC1 (a v)) * cnPlus ℓ Φ := by
    simpa [L1, OB] using hp
  have hsplit := q1_w1line_scalar_split (N := N) (μ := μ) hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
  have hsplit' : L1 - 2 * μ * OB
      = 2 * (((N : ℝ) / ℓ ^ 3) - μ) * OB - 2 * (ℓ ^ 3)⁻¹ * Corr := by
    simpa [L1, OB, Corr] using hsplit
  have hcs := q1_cross_w1_cs_fs hℓ (t := ((N : ℝ) / ℓ ^ 3) - μ)
    hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc hSc1
  have hcs' : 2 * (((N : ℝ) / ℓ ^ 3) - μ) * OB
      ≥ - (1 / 4) * ((((N : ℝ) / ℓ ^ 3) - μ) ^ 2) * ((8 * π * (a v)) * ℓ ^ 3)
        - ((4 * (cS1 ℓ Φ)) / ℓ ^ 3) * qOneM := by
    simpa [OB, qOneM] using hcs
  have hgoal : q0RenVal (N := N) (v := v) ℓ μ Φ + L1 - 2 * μ * OB
      - 2 * (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (4 * cS2 ℓ Φ + 3 * ((N : ℝ) * cnPlus ℓ Φ))
      - (8 / 3) * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - 2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - 2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - μ * (fsqC1 (a v)) * cnPlus ℓ Φ
    ≥ q0RenVal (N := N) (v := v) ℓ μ Φ
      - (1 / 4) * ((((N : ℝ) / ℓ ^ 3) - μ) ^ 2) * ((8 * π * (a v)) * ℓ ^ 3)
      - ((4 * (cS1 ℓ Φ)) / ℓ ^ 3) * qOneM - 2 * (ℓ ^ 3)⁻¹ * Corr
      - 2 * (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (4 * cS2 ℓ Φ + 3 * ((N : ℝ) * cnPlus ℓ Φ))
      - (8 / 3) * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - 2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - 2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
      - μ * (fsqC1 (a v)) * cnPlus ℓ Φ := by
    nlinarith [hsplit', hcs']

  have hfin : q0RenVal (N := N) (v := v) ℓ μ Φ
        - (1 / 4) * ((((N : ℝ) / ℓ ^ 3) - μ) ^ 2) * ((8 * π * (a v)) * ℓ ^ 3)
        - ((4 * (cS1 ℓ Φ)) / ℓ ^ 3) * qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ)
        - 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
            (aP ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)) *
              (∑ k : Fin N, aQ ℓ k (aQ ℓ i Φ) x))
        - 2 * (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
        - (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (4 * cS2 ℓ Φ + 3 * ((N : ℝ) * cnPlus ℓ Φ))
        - (8 / 3) * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
        - 2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
        - 2 * (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ)
        - μ * (fsqC1 (a v)) * cnPlus ℓ Φ
      ≤ qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ := by
    dsimp [L1, OB, Corr, qOneM] at hp' hgoal
    simpa [Corr, qOneM] using (le_trans hgoal hp')
  simpa using hfin

end BoseGases


end Submission