import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.CentredSector
import Submission.KernelFibreBound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Layer 5 — the one-body (chemical-potential) cross-term bound

FS `lm:potapp` `eq:app1bdod` bounds the off-diagonal (P–Q) part of the
one-body chemical-potential term of the box Hamiltonian (`Q₁`- and `Q₂`-type
cross terms, final_v2.tex ~1155–1175):

    ± μ·Σ_i (P_i ∫_y w₁(xᵢ,y)dy Q_i + h.c.)  ≤  C·a·μ·(n₀ + n₊)-scale

Corpus-native (expectation form over `abox N ℓ`, chosen branch with
`w₁ := wPairU(g₀)`, `w₀` the scattering solution, `g₀ := v(1−w₀)`,
`∫g₀ = 8πa v`): for every continuous `Φ`,

    |2μ·Σ_i ∫_x (P_iΦ)(x)·(∫_y w₁(xᵢ,y)dy)·(Q_iΦ)(x) dx|
        ≤ μ·(2·chiSup²·8πa v)·(cS1 ℓ Φ + cnPlus ℓ Φ)            (onebody_cross_abs_le)

obtained from the elementary `2|∫A·f·B| ≤ ∫A²|f| + ∫B²|f|`
(pointwise `(A∓B)² ≥ 0`) with `A := P_iΦ`, `B := Q_iΦ`, `f` the kernel
fibre, whose pointwise bound `|fibre(xᵢ)| ≤ 2·chiSup²·8πa v` is
`KernelFibreBound.w1c_fibre_abs_le`; `cS1`, `cnPlus` are the
`CentredSector` condensed/excited counts.  (No nonnegativity of the kernel
is needed for this elementary bound; the sharper `w₁ ≥ 0`-version used by
FS is a later refinement via `QuadCS`.)

## Route notes (for the child)

* Real lemma: `abs_two_mul_le`: `2·|a·b| ≤ a² + b²` (nlinarith).
* `abs_integral_mul_le_half`: `|∫_x A x · (f (x i)) · B x| ≤
  ½·∫A²·|f∘coordᵢ| + ½·∫B²·|f∘coordᵢ|` by `|ABf| ≤ ½|f|(A²+B²)`
  pointwise and `integral`-triangle/linearity (integrability hypotheses
  given as `IntegrableOn`).
* Pointwise fibre bound `|∫_y wPair ℓ (g0 v h) (x i) y dy| ≤
  chiSup²·2·(8π·a v)` from `KernelFibreBound.w1c_fibre_abs_le`
  (all `x ∈ abox` covered since the bound is for all `x`); the fibre here is
  the *cube* integral — transferred from the full-space integral via
  `KernelFibreBound.fibre_acube_abs_le` (which is valid for all `x`).
* Summation over `Fin N` and the definitions of `cS1`/`cnPlus`
  (`CentredSector`) finish.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Submission

open _root_.BoseGases
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- `2·|a·b| ≤ a² + b²`. -/
lemma abs_two_mul_le_sq_sq (a b : ℝ) : 2 * |a * b| ≤ a ^ 2 + b ^ 2 := by
  rw [abs_mul]
  have hsq : 0 ≤ (|a| - |b|) ^ 2 := sq_nonneg _
  nlinarith [hsq, sq_abs a, sq_abs b]

/-- Rearranging the association inside an absolute value. -/
lemma abs_reorder_mul (a c b : ℝ) : |a * c * b| = |a * (c * b)| := by
  rw [show a * c * b = a * (c * b) by ring]

/-- Pointwise: `|a·(c·b)| ≤ ½·|c|·(a² + b²)`. -/
lemma abs_cross_mul_le_half_aux (a c b : ℝ) :
    |a * (c * b)| ≤ (1 / 2) * (|c| * a ^ 2 + |c| * b ^ 2) := by
  have h2 : 2 * |a * b| ≤ a ^ 2 + b ^ 2 := abs_two_mul_le_sq_sq a b
  have hc0 : 0 ≤ |c| := abs_nonneg c
  have hmul : |c| * (2 * |a * b|) ≤ |c| * (a ^ 2 + b ^ 2) := by
    exact mul_le_mul_of_nonneg_left h2 hc0
  have hEq : |a * (c * b)| = |c| * |a * b| := by
    rw [abs_mul, abs_mul, abs_mul]
    ring
  nlinarith [hmul, hEq]

/-- Pointwise: `|a·c·b| ≤ ½·|c|·(a² + b²)`. -/
lemma abs_cross_mul_le_half (a c b : ℝ) :
    |a * c * b| ≤ (1 / 2) * (|c| * a ^ 2 + |c| * b ^ 2) := by
  rw [abs_reorder_mul a c b]
  exact abs_cross_mul_le_half_aux a c b

/-- Pointwise: `|c| ≤ C` ⟹ `|a·(c·b)| ≤ (C/2)·(a²+b²)`. -/
lemma abs_cross_mul_le_of_bound_aux (a b : ℝ) {C c : ℝ} (hc : |c| ≤ C) :
    |a * (c * b)| ≤ (C / 2) * (a ^ 2 + b ^ 2) := by
  have h1 := abs_cross_mul_le_half_aux a c b
  have h2 : |c| * a ^ 2 ≤ C * a ^ 2 :=
    mul_le_mul_of_nonneg_right hc (sq_nonneg a)
  have h3 : |c| * b ^ 2 ≤ C * b ^ 2 :=
    mul_le_mul_of_nonneg_right hc (sq_nonneg b)
  calc
    |a * (c * b)| ≤ (1 / 2) * (|c| * a ^ 2 + |c| * b ^ 2) := h1
    _ ≤ (1 / 2) * (C * a ^ 2 + C * b ^ 2) := by
      exact mul_le_mul_of_nonneg_left (add_le_add h2 h3) (by norm_num)
    _ = (C / 2) * (a ^ 2 + b ^ 2) := by ring

/-- Pointwise: `|c| ≤ C` ⟹ `|a·c·b| ≤ (C/2)·(a²+b²)`. -/
lemma abs_cross_mul_le_of_bound (a b : ℝ) {C c : ℝ} (hc : |c| ≤ C) :
    |a * c * b| ≤ (C / 2) * (a ^ 2 + b ^ 2) := by
  rw [abs_reorder_mul a c b]
  exact abs_cross_mul_le_of_bound_aux a b hc

/-- `|∫ A·(f∘coordᵢ)·B| ≤ ½·∫A²·|f∘coordᵢ| + ½·∫B²·|f∘coordᵢ|` over the box. -/
lemma abs_integral_mul_fibre_le_half {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N)
    {f : kcE3 → ℝ} {A B : X N → ℝ}
    (hAi : IntegrableOn (fun x : X N => (A x) ^ 2 * |f (x i)|) (abox N ℓ) volume)
    (hBi : IntegrableOn (fun x : X N => (B x) ^ 2 * |f (x i)|) (abox N ℓ) volume)
    (hAB : IntegrableOn (fun x : X N => A x * (f (x i) * B x)) (abox N ℓ) volume) :
    |∫ x in abox N ℓ, A x * (f (x i) * B x)|
      ≤ (1 / 2) * (∫ x in abox N ℓ, (A x) ^ 2 * |f (x i)|) +
        (1 / 2) * (∫ x in abox N ℓ, (B x) ^ 2 * |f (x i)|) := by
  let μ : Measure (X N) := (volume : Measure (X N)).restrict (abox N ℓ)
  let F1 : X N → ℝ := fun x => (A x) ^ 2 * |f (x i)|
  let F2 : X N → ℝ := fun x => (B x) ^ 2 * |f (x i)|
  let G : X N → ℝ := fun x => (1 / 2) * F1 x + (1 / 2) * F2 x
  have hF1 : Integrable F1 μ := by
    simpa [F1, μ, IntegrableOn] using hAi
  have hF2 : Integrable F2 μ := by
    simpa [F2, μ, IntegrableOn] using hBi
  have hg1 : Integrable (fun x : X N => (1 / 2) * F1 x) μ := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hF1.const_mul (1 / 2)
  have hg2 : Integrable (fun x : X N => (1 / 2) * F2 x) μ := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hF2.const_mul (1 / 2)
  have hG : Integrable G μ := by
    dsimp [G]
    exact hg1.add hg2
  have hpt (x : X N) : |A x * (f (x i) * B x)| ≤ G x := by
    have hc := abs_cross_mul_le_half_aux (a := A x) (c := f (x i)) (b := B x)
    dsimp [G, F1, F2]
    nlinarith
  calc
    |∫ x in abox N ℓ, A x * (f (x i) * B x)|
        ≤ ∫ x in abox N ℓ, |A x * (f (x i) * B x)| := by
            simpa using (abs_integral_le_integral_abs
              (f := fun x : X N => A x * (f (x i) * B x)) (μ := μ))
    _ ≤ ∫ x in abox N ℓ, G x := by
            refine integral_mono_of_nonneg (μ := μ)
              (f := fun x : X N => |A x * (f (x i) * B x)|) (g := G) ?_ ?_ ?_
            · filter_upwards with x
              exact abs_nonneg _
            · simpa [μ, G] using hG
            · filter_upwards with x
              exact hpt x
    _ = (1 / 2) * (∫ x in abox N ℓ, F1 x) + (1 / 2) * (∫ x in abox N ℓ, F2 x) := by
            calc
              (∫ x in abox N ℓ, G x)
                  = (∫ x in abox N ℓ, (1 / 2) * F1 x) + (∫ x in abox N ℓ, (1 / 2) * F2 x) := by
                      simpa [G] using (integral_add (μ := μ) (f := fun x : X N => (1 / 2) * F1 x)
                        (g := fun x : X N => (1 / 2) * F2 x) hg1 hg2)
              _ = (1 / 2) * (∫ x in abox N ℓ, F1 x) + (1 / 2) * (∫ x in abox N ℓ, F2 x) := by
                      rw [integral_const_mul]
                      rw [integral_const_mul]

/-- A pointwise-bounded fibre gives a two-square bound on the cross term:
if `∀ x ∈ acube ℓ, |f x| ≤ C` then
`|∫ A·(f∘coordᵢ)·B| ≤ (C/2)·∫A² + (C/2)·∫B²`. -/
lemma abs_integral_mul_fibre_le_of_bound {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N)
    {f : kcE3 → ℝ} {C : ℝ} (hC : ∀ x : kcE3, x ∈ acube ℓ → |f x| ≤ C)
    {A B : X N → ℝ}
    (hAi : IntegrableOn (fun x : X N => (A x) ^ 2) (abox N ℓ) volume)
    (hBi : IntegrableOn (fun x : X N => (B x) ^ 2) (abox N ℓ) volume)
    (hAB : IntegrableOn (fun x : X N => A x * (f (x i) * B x)) (abox N ℓ) volume) :
    |∫ x in abox N ℓ, A x * (f (x i) * B x)|
      ≤ (C / 2) * (∫ x in abox N ℓ, (A x) ^ 2) +
        (C / 2) * (∫ x in abox N ℓ, (B x) ^ 2) := by
  let μ : Measure (X N) := (volume : Measure (X N)).restrict (abox N ℓ)
  let HA : X N → ℝ := fun x => (A x) ^ 2
  let HB : X N → ℝ := fun x => (B x) ^ 2
  let R : X N → ℝ := fun x => (C / 2) * (HA x + HB x)
  have hHA : Integrable HA μ := by
    simpa [HA, μ, IntegrableOn] using hAi
  have hHB : Integrable HB μ := by
    simpa [HB, μ, IntegrableOn] using hBi
  have hHAB : Integrable (fun x : X N => HA x + HB x) μ := hHA.add hHB
  have hR : Integrable R μ := by
    dsimp [R]
    exact hHAB.const_mul (C / 2)
  have hpt : ∀ x : X N, x ∈ abox N ℓ →
      |A x * (f (x i) * B x)| ≤ R x := by
    intro x hx
    have hb : |f (x i)| ≤ C := hC (x i) (hx i)
    have hcross := abs_cross_mul_le_of_bound_aux (a := A x) (b := B x) (c := f (x i)) hb
    dsimp [R, HA, HB]
    simpa using hcross
  calc
    |∫ x in abox N ℓ, A x * (f (x i) * B x)|
        ≤ ∫ x in abox N ℓ, |A x * (f (x i) * B x)| := by
            simpa using (abs_integral_le_integral_abs
              (f := fun x : X N => A x * (f (x i) * B x)) (μ := μ))
    _ ≤ ∫ x in abox N ℓ, R x := by
            refine integral_mono_of_nonneg (μ := μ)
              (f := fun x : X N => |A x * (f (x i) * B x)|) (g := R) ?_ ?_ ?_
            · filter_upwards with x
              exact abs_nonneg _
            · simpa [μ, R] using hR
            · change ∀ᵐ x : X N ∂μ, |A x * (f (x i) * B x)| ≤ R x
              rw [ae_restrict_iff' (abox_measurable N ℓ)]
              exact ae_of_all volume (by intro x hx; exact hpt x hx)
    _ = (C / 2) * (∫ x in abox N ℓ, HA x) + (C / 2) * (∫ x in abox N ℓ, HB x) := by
            calc
              (∫ x in abox N ℓ, R x)
                  = (C / 2) * (∫ x in abox N ℓ, HA x + HB x) := by
                      dsimp [R]
                      rw [integral_const_mul]
              _ = (C / 2) * ((∫ x in abox N ℓ, HA x) + (∫ x in abox N ℓ, HB x)) := by
                      rw [integral_add hHA hHB]
              _ = (C / 2) * (∫ x in abox N ℓ, HA x) + (C / 2) * (∫ x in abox N ℓ, HB x) := by ring
    _ = (C / 2) * (∫ x in abox N ℓ, (A x) ^ 2) +
        (C / 2) * (∫ x in abox N ℓ, (B x) ^ 2) := by
            simp [HA, HB]

/-- Chosen-branch fibre bound in the box form used here: for every `x : X N`,
`|∫_y wPair ℓ (g0 v h) (x i) y dy| ≤ chiSup²·2·(8π·a v)`. -/
lemma w1c_fibre_acube_abs_le_box {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) {N : ℕ} (i : Fin N) (x : X N) :
    |∫ y in acube ℓ, wPair ℓ (g0 v h) (x i) y| ≤ chiSup ^ 2 * 2 * (8 * π * a v) := by
  have hbnd := fibre_acube_abs_le (h := g0 v h) hℓ (le_of_lt hR) hRℓ
    (g0_integrable hR hv_supp h) (fun z hz => g0_zero_of_norm_ge hv_supp hz h) (x i)
  have hnn : ∀ᵐ z : ℝ³, 0 ≤ g0 v h z := g0_nonneg_ae hR hv_nonneg hvrad hv_supp h
  have hEq : (∫ z : ℝ³, |g0 v h z|) = ∫ z : ℝ³, g0 v h z := by
    apply integral_congr_ae
    filter_upwards [hnn] with z hz
    exact abs_of_nonneg hz
  rw [hEq, g0_integral hR hv_supp h] at hbnd
  exact hbnd

/-- **One-body cross-term bound** (potapp `eq:app1bdod` corpus form): with
`w₁ := wPair(g₀)` and fibre `f(z) := ∫_y w₁(z,y)dy`,

`|2μ·Σ_i ∫_x (P_iΦ)·f(xᵢ)·(Q_iΦ)| ≤ μ·(2·chiSup²·8πa v)·(cS1 + cnPlus)`. -/
lemma onebody_cross_abs_le {N : ℕ} {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) (μ : ℝ) (hμ : 0 ≤ μ) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) :
    |2 * μ * (∑ i : Fin N, ∫ x in abox N ℓ,
        (aP ℓ i Φ x) * (∫ y in acube ℓ, wPair ℓ (g0 v h) (x i) y) * (aQ ℓ i Φ x))|
      ≤ μ * (chiSup ^ 2 * 2 * (8 * π * a v)) * (cS1 ℓ Φ + cnPlus ℓ Φ) := by
  let C : ℝ := chiSup ^ 2 * 2 * (8 * π * a v)
  -- the chosen fibre is bounded by `C` at every coordinate (all `x`, since
  -- `fibre_acube_abs_le` is total)
  have hfib : ∀ (i : Fin N) (x : X N),
      |∫ y in acube ℓ, wPair ℓ (g0 v h) (x i) y| ≤ C := by
    intro i x
    simpa [C] using (w1c_fibre_acube_abs_le_box hR hv_nonneg hvrad hv_supp h hℓ hRℓ i x)
  -- per-particle bound: `|∫ (PᵢΦ)·fibre·(QᵢΦ)| ≤ (C/2)‖PᵢΦ‖² + (C/2)‖QᵢΦ‖²`
  have hmain (i : Fin N) :
      |∫ x in abox N ℓ,
          (aP ℓ i Φ x) * (∫ y in acube ℓ, wPair ℓ (g0 v h) (x i) y) * (aQ ℓ i Φ x)|
        ≤ (C / 2) * (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) +
          (C / 2) * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2) := by
    let P : X N → ℝ := fun x => aP ℓ i Φ x
    let Q : X N → ℝ := fun x => aQ ℓ i Φ x
    let F : X N → ℝ := fun x => ∫ y in acube ℓ, wPair ℓ (g0 v h) (x i) y
    let R : X N → ℝ := fun x => (C / 2) * ((P x) ^ 2 + (Q x) ^ 2)
    let μ : Measure (X N) := (volume : Measure (X N)).restrict (abox N ℓ)
    have hP : Integrable (fun x : X N => (P x) ^ 2) μ := by
      simpa [P, μ, IntegrableOn] using (integrableOn_sq_aP hℓ i hΦc)
    have hQ : Integrable (fun x : X N => (Q x) ^ 2) μ := by
      simpa [Q, μ, IntegrableOn] using (integrableOn_sq_aQ hℓ i hΦc)
    have hR : Integrable R μ := by
      dsimp [R]
      exact (hP.add hQ).const_mul (C / 2)
    -- pointwise `|P·F·Q| ≤ (C/2)(P² + Q²)` on the whole box (fibre bound is total)
    have hpt (x : X N) : |P x * F x * Q x| ≤ R x := by
      have hb : |F x| ≤ C := hfib i x
      have hc := abs_cross_mul_le_of_bound (a := P x) (b := Q x) (c := F x) hb
      dsimp [R]
      simpa using hc
    calc
      |∫ x in abox N ℓ, P x * F x * Q x|
          ≤ ∫ x in abox N ℓ, |P x * F x * Q x| := by
              simpa using (abs_integral_le_integral_abs
                (f := fun x : X N => P x * F x * Q x) (μ := μ))
      _ ≤ ∫ x in abox N ℓ, R x := by
              refine integral_mono_of_nonneg (μ := μ)
                (f := fun x : X N => |P x * F x * Q x|) (g := R) ?_ ?_ ?_
              · filter_upwards with x
                exact abs_nonneg _
              · simpa [μ, R] using hR
              · filter_upwards with x
                exact hpt x
      _ = (C / 2) * (∫ x in abox N ℓ, (P x) ^ 2) + (C / 2) * (∫ x in abox N ℓ, (Q x) ^ 2) := by
              calc
                (∫ x in abox N ℓ, R x)
                    = (C / 2) * (∫ x in abox N ℓ, (P x) ^ 2 + (Q x) ^ 2) := by
                        dsimp [R]
                        rw [integral_const_mul]
                _ = (C / 2) * ((∫ x in abox N ℓ, (P x) ^ 2) + (∫ x in abox N ℓ, (Q x) ^ 2)) := by
                        rw [integral_add hP hQ]
                _ = (C / 2) * (∫ x in abox N ℓ, (P x) ^ 2) + (C / 2) * (∫ x in abox N ℓ, (Q x) ^ 2) := by ring
  -- assemble: triangle inequality in the sum, then identify `cS1`/`cnPlus`
  let S : ℝ := ∑ i : Fin N, ∫ x in abox N ℓ,
      (aP ℓ i Φ x) * (∫ y in acube ℓ, wPair ℓ (g0 v h) (x i) y) * (aQ ℓ i Φ x)
  have hsum : |S| ≤ (C / 2) * cS1 ℓ Φ + (C / 2) * cnPlus ℓ Φ := by
    calc
      |S| ≤ ∑ i : Fin N, |∫ x in abox N ℓ,
            (aP ℓ i Φ x) * (∫ y in acube ℓ, wPair ℓ (g0 v h) (x i) y) * (aQ ℓ i Φ x)| := by
            dsimp [S]
            simpa using (Finset.abs_sum_le_sum_abs (f := fun i : Fin N =>
              ∫ x in abox N ℓ, (aP ℓ i Φ x) * (∫ y in acube ℓ, wPair ℓ (g0 v h) (x i) y) * (aQ ℓ i Φ x))
              (s := Finset.univ))
      _ ≤ ∑ i : Fin N, ((C / 2) * (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) +
            (C / 2) * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2)) := by
            exact Finset.sum_le_sum (fun i hi => hmain i)
      _ = (C / 2) * (∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) +
          (C / 2) * (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2) := by
            rw [Finset.sum_add_distrib]
            rw [← Finset.mul_sum]
            rw [← Finset.mul_sum]
      _ = (C / 2) * cS1 ℓ Φ + (C / 2) * cnPlus ℓ Φ := by
            rfl
  -- multiply by the nonnegative `2μ`
  have h2 : |2 * μ * S| ≤ 2 * μ * ((C / 2) * cS1 ℓ Φ + (C / 2) * cnPlus ℓ Φ) := by
    calc
      |2 * μ * S| = 2 * μ * |S| := by
        rw [abs_mul]
        rw [abs_of_nonneg (mul_nonneg (by norm_num) hμ)]
      _ ≤ 2 * μ * ((C / 2) * cS1 ℓ Φ + (C / 2) * cnPlus ℓ Φ) := by
        exact mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num) hμ)
  calc
    |2 * μ * S| ≤ 2 * μ * ((C / 2) * cS1 ℓ Φ + (C / 2) * cnPlus ℓ Φ) := h2
    _ = μ * C * (cS1 ℓ Φ + cnPlus ℓ Φ) := by ring
    _ = μ * (chiSup ^ 2 * 2 * (8 * π * a v)) * (cS1 ℓ Φ + cnPlus ℓ Φ) := by rfl

end BoseGases

end Submission
