import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Commons.Analysis.Real.cos_pi_mul_lower_bound_on_quarter
import Submission.Work.ChiSmallBand
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Executable dℓ-localised kernels for the sliding-sum layer (FS §SmallBoxes)

FS eq:HBU localises the big-box kernels to the small box `B(u)`:

    w_B(x,y) = χ_B(x)·W(x−y)·χ_B(y),   w_{1,B}(x,y) = χ_B(x)·W₁(x−y)·χ_B(y),

`χ_B(x) = χ_M(x/ℓ)·χ_M(x/(ℓd) − u)` (the cosine-M two-factor cutoff =
`Submission.Work.ChiSmall.chiSmallB`), and the renormalised kernels carry the
`(χ_M⋆χ_M)(·/(dℓ))` denominator:

    W(x) = h(x)/(χ_M⋆χ_M)(x/(ℓd))

(mirroring the corpus `wScaled = h/(χ⋆χ)(·/c)` at the big-box scale, but with
the cosine-M bump `chiSmall` in the convolution).

This module lays down those kernel OBJECTS as executable corpus definitions
(the atom of the `H_{B(u)}` family of eq:HBU / eq:BSsliding2): the small-box
cutoff `chiSmallB`, its self-convolution `conv3Small M` and scaled version
`convScaleSmall M c`, and the two-body/one-body localised kernels
`wSmallPair M ℓ d u h` (`h := v`) and `wSmall1Pair M ℓ d u h` (`h := g0 v h`).

STATUS: axiom-free, sorry-free, rc=0 (as of Session-194).  CLOSED in this
module: `chiSmallB`-kernel objects, `chiSmallB_partition_xy_u` (two-point
u-partition), `chiSmall_conv_fibre` (big-box convolution fibre),
`chiSmallB_w_pair_uint` (u-integrated pair kernel),
`conv3Small_pos_near_zero` (self-convolution positive on `|z_j| ≤ 1/16`,
Steps A–C, L21 fleet trig atom landed → no TEMP axiom), and the
**renormalisation cancellation corollary** (`conv3Small_ne_zero_of_norm_le`,
`norm_inv_smul_le`, `lt_norm_of_not_norm_inv_smul_le`,
`convScaleSmall_mul_wSmallScaled`, `chiSmallB_w_pair_uint_cancel`,
`chiSmallB_w1_pair_uint_cancel`): under `R ≤ (ℓd)/16`
`∫_u wSmallPair M ℓ d u h x y du = χ_M(x/ℓ)χ_M(y/ℓ)·h(x−y)` (and the
`h := g0 v h` corpus form); plus `conv3Small_zero`
(`(χ⋆χ)(0) = ∫χ_M² = 1`, Session-195).  Session-195 (see
`Submission/Work/DLSlidingIntegral.lean` + SmallBoxDesignNote.md Session-195
addendum): the eq:appw1sliding transcription decision is TAKEN — the EXACT
weighted triple identity `∫_x∫_y∫_u wSmallPair M ℓ d u h x y du dx dy =
ℓ³∫h(w)(χ⋆χ)(w/ℓ)dw` is machine-checked (`chiSmall_pair_double`,
`dlPair_triple_uInner`, `dlW1Pair_triple_uInner`).  Next: the operator-level
`H_{B(u)}` / `smallbox_dl_energy_bound` body (roadmap Step 2) and the
executable eq:appsliding statement.
-/

noncomputable section

open MeasureTheory Metric
open scoped Real BigOperators ENNReal Topology ContDiff

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false
set_option linter.unusedVariables false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- the self-convolution of the cosine-M bump: `(χ_M ⋆ χ_M)(x)`. -/
noncomputable def conv3Small (M : ℕ) (x : ℝ³) : ℝ :=
  ∫ y : ℝ³, chiSmall M y * chiSmall M (x - y)

/-- the scaled convolution `(χ_M ⋆ χ_M)(x/c)` used as the dℓ renormalisation
denominator. -/
noncomputable def convScaleSmall (M : ℕ) (c : ℝ) (x : ℝ³) : ℝ :=
  conv3Small M ((c)⁻¹ • x)

/-- the renormalised kernel `W(x) := h(x)/(χ_M⋆χ_M)(x/(dℓ))` (total:
division by zero is `0`). -/
noncomputable def wSmallScaled (M : ℕ) (c : ℝ) (h : ℝ³ → ℝ) (x : ℝ³) : ℝ :=
  h x / convScaleSmall M c x

/-- the localised two-body kernel
`w_B(x,y) = χ_{B(u)}(x)·W(x−y)·χ_{B(u)}(y)` (numerator `h`). -/
noncomputable def wSmallPair (M : ℕ) (ℓ d : ℝ) (u : ℝ³) (h : ℝ³ → ℝ) (x y : ℝ³) : ℝ :=
  chiSmallB M ℓ d u x *
    (wSmallScaled M (ℓ * d) h (x - y) / convScale ℓ (x - y)) * chiSmallB M ℓ d u y

/-- the localised one-body kernel with the chosen `g₀` numerator
(`∬w_{1,B} ≈ 8πa·|B|` at the assembly). -/
noncomputable def wSmall1Pair {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (M : ℕ) (ℓ d : ℝ)
    (u : ℝ³) (x y : ℝ³) : ℝ :=
  wSmallPair M ℓ d u (g0 v h) x y


/-- evenness of the cosine-M self-convolution: `(χ_M⋆χ_M)(−x) = (χ_M⋆χ_M)(x)`
(from evenness of `chiSmall` and the reflection `y ↦ −y`, `integral_comp_neg`).
This is what makes the localised kernels `wSmallPair`/`wSmall1Pair`
symmetric. -/
lemma conv3Small_symm {M : ℕ} (hM : 1 ≤ M) (x : ℝ³) : conv3Small M (-x) = conv3Small M x := by
  dsimp [conv3Small]
  have h1 : (∫ y : ℝ³, chiSmall M y * chiSmall M (-x - y)) =
      (∫ y : ℝ³, chiSmall M y * chiSmall M (x + y)) := by
    apply integral_congr_ae
    exact ae_of_all _ (by
      intro y
      change chiSmall M y * chiSmall M (-x - y) = chiSmall M y * chiSmall M (x + y)
      have harg : -x - y = -(x + y) := by abel
      rw [harg, chiSmall_even hM (x + y)])
  have h2 : (∫ y : ℝ³, chiSmall M y * chiSmall M (x + y)) =
      (∫ y : ℝ³, chiSmall M y * chiSmall M (x - y)) := by
    calc
      (∫ y : ℝ³, chiSmall M y * chiSmall M (x + y))
          = (∫ y : ℝ³, chiSmall M (-y) * chiSmall M (x - (-y))) := by
              apply integral_congr_ae
              exact ae_of_all _ (by
                intro y
                change chiSmall M y * chiSmall M (x + y) = chiSmall M (-y) * chiSmall M (x - (-y))
                have hg1 : chiSmall M y = chiSmall M (-y) := (chiSmall_even hM y).symm
                have hg2 : chiSmall M (x + y) = chiSmall M (x - (-y)) := by
                  congr 1
                  abel
                rw [hg1, hg2])
      _ = (∫ y : ℝ³, chiSmall M y * chiSmall M (x - y)) := by
          exact (integral_comp_neg (g := fun y : ℝ³ => chiSmall M y * chiSmall M (x - y)))
  calc
    (∫ y : ℝ³, chiSmall M y * chiSmall M (-x - y))
        = (∫ y : ℝ³, chiSmall M y * chiSmall M (x + y)) := h1
    _ = (∫ y : ℝ³, chiSmall M y * chiSmall M (x - y)) := h2

/-- the localised two-body kernel is symmetric (even numerator `h`): a
corpus potsplit prerequisite. -/
lemma wSmallPair_symm {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (u : ℝ³) {h : ℝ³ → ℝ}
    (hh : ∀ z : ℝ³, h (-z) = h z) (x y : ℝ³) :
    wSmallPair M ℓ d u h x y = wSmallPair M ℓ d u h y x := by
  have hnum : h (y - x) = h (x - y) := by
    have harg : y - x = -(x - y) := by abel
    rw [harg]
    exact hh (x - y)
  have hden : convScaleSmall M (ℓ * d) (x - y) = convScaleSmall M (ℓ * d) (y - x) := by
    dsimp [convScaleSmall]
    have harg : (ℓ * d)⁻¹ • (x - y) = -((ℓ * d)⁻¹ • (y - x)) := by
      rw [← smul_neg]
      congr 1
      abel
    rw [harg]
    exact conv3Small_symm hM ((ℓ * d)⁻¹ • (y - x))
  have hw : wSmallScaled M (ℓ * d) h (x - y) = wSmallScaled M (ℓ * d) h (y - x) := by
    dsimp [wSmallScaled]
    calc
      h (x - y) / convScaleSmall M (ℓ * d) (x - y)
          = h (y - x) / convScaleSmall M (ℓ * d) (x - y) := by rw [hnum]
      _ = h (y - x) / convScaleSmall M (ℓ * d) (y - x) := by rw [hden]
  have hden2 : convScale ℓ (y - x) = convScale ℓ (x - y) := by
    dsimp [convScale]
    have harg : (ℓ⁻¹) • (y - x) = -((ℓ⁻¹) • (x - y)) := by
      rw [← smul_neg]
      congr 1
      abel
    rw [harg, conv3chi_even]
  dsimp [wSmallPair]
  rw [hw, hden2]
  ring


/-- the two-point `u`-partition (the sliding/chemical-potential identity
ingredient): `∫_u χ_{B(u)}(x)·χ_{B(u)}(y) du = χ_M(x/ℓ)·χ_M(y/ℓ)·(χ_M⋆χ_M)((x−y)/(ℓd))`. -/
lemma chiSmallB_partition_xy_u {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (x y : ℝ³) :
    (∫ u : ℝ³, chiSmallB M ℓ d u x * chiSmallB M ℓ d u y)
      = chiScale ℓ x * chiScale ℓ y * conv3Small M ((ℓ * d)⁻¹ • (x - y)) := by
  let a : ℝ³ := (ℓ * d)⁻¹ • x
  let b : ℝ³ := (ℓ * d)⁻¹ • y
  have hinner : (∫ u : ℝ³, chiSmall M (a - u) * chiSmall M (b - u))
      = conv3Small M ((ℓ * d)⁻¹ • (x - y)) := by
    -- substitute w := u − a (translation, measure-preserving): u = w + a
    let φ : ℝ³ → ℝ³ := fun u => -a + u
    let g : ℝ³ → ℝ := fun w => chiSmall M (-w) * chiSmall M ((b - a) - w)
    have hφmp : MeasurePreserving φ volume volume := by
      dsimp [φ]
      exact measurePreserving_add_left (volume : Measure ℝ³) (-a)
    have hpt : ∀ u : ℝ³, g (φ u) = chiSmall M (a - u) * chiSmall M (b - u) := by
      intro u
      dsimp [φ, g]
      have h1 : -(-a + u) = a - u := by abel
      have h2 : (b - a) - (-a + u) = b - u := by abel
      rw [h1, h2]
    have hg : AEStronglyMeasurable g (Measure.map φ volume) := by
      have hc : Continuous g := by
        have hc' := chiSmall_continuous hM
        dsimp [g]
        fun_prop
      exact hc.aestronglyMeasurable
    have hm := MeasureTheory.integral_map (μ := volume) hφmp.aemeasurable (f := g) hg
    have hgpt : g = fun w : ℝ³ => chiSmall M w * chiSmall M ((b - a) - w) := by
      funext w
      dsimp [g]
      congr 1
      exact chiSmall_even hM w
    have hbminus : conv3Small M (b - a) = conv3Small M (a - b) := by
      have harg : a - b = -(b - a) := by abel
      rw [harg]
      exact (conv3Small_symm hM (b - a)).symm
    have hab : a - b = (ℓ * d)⁻¹ • (x - y) := by
      dsimp [a, b]
      rw [smul_sub]
    calc
      (∫ u : ℝ³, chiSmall M (a - u) * chiSmall M (b - u))
          = (∫ u : ℝ³, g (φ u)) := by
              apply integral_congr_ae
              exact ae_of_all _ (by intro u; exact (hpt u).symm)
      _ = ∫ w : ℝ³, g w := by
          rw [hφmp.map_eq] at hm
          exact hm.symm
      _ = (∫ w : ℝ³, chiSmall M w * chiSmall M ((b - a) - w)) := by rw [hgpt]
      _ = conv3Small M (b - a) := rfl
      _ = conv3Small M (a - b) := hbminus
      _ = conv3Small M ((ℓ * d)⁻¹ • (x - y)) := by rw [hab]
  -- factor out the ℓ-scale factors (constant in u)
  have hfact : (∫ u : ℝ³, chiScale ℓ x * chiScale ℓ y * chiSmall M (a - u) * chiSmall M (b - u))
      = chiScale ℓ x * chiScale ℓ y * (∫ u : ℝ³, chiSmall M (a - u) * chiSmall M (b - u)) := by
    have hpt : (fun u : ℝ³ => chiScale ℓ x * chiScale ℓ y * chiSmall M (a - u) * chiSmall M (b - u))
        = fun u : ℝ³ => (chiScale ℓ x * chiScale ℓ y) * (chiSmall M (a - u) * chiSmall M (b - u)) := by
      funext u
      ring
    rw [hpt]
    simpa using (MeasureTheory.integral_const_mul (μ := (volume : Measure ℝ³))
      (r := chiScale ℓ x * chiScale ℓ y)
      (f := fun u : ℝ³ => chiSmall M (a - u) * chiSmall M (b - u)))
  calc
    (∫ u : ℝ³, chiSmallB M ℓ d u x * chiSmallB M ℓ d u y)
        = (∫ u : ℝ³, chiScale ℓ x * chiScale ℓ y * chiSmall M (a - u) * chiSmall M (b - u)) := by
            apply integral_congr_ae
            exact ae_of_all _ (by
              intro u
              dsimp [chiSmallB, a, b]
              ring)
    _ = chiScale ℓ x * chiScale ℓ y * (∫ u : ℝ³, chiSmall M (a - u) * chiSmall M (b - u)) := hfact
    _ = chiScale ℓ x * chiScale ℓ y * conv3Small M ((ℓ * d)⁻¹ • (x - y)) := by rw [hinner]


/-- **big-box convolution fibre**: `∫_x χ_M(x/ℓ)·χ_M((x−z)/ℓ) dx =
ℓ³·(χ_M⋆χ_M)(z/ℓ)` — the companion to `chiSmallB_partition_u`; what the
`∬w_{1,B(u)}`-type normalisations reduce to (ℓ-scale dilation +
evenness of `chiSmall`). -/
lemma chiSmall_conv_fibre {M : ℕ} (hM : 1 ≤ M) {ℓ : ℝ} (hℓ : 0 < ℓ) (z : ℝ³) :
    (∫ x : ℝ³, chiSmall M (ℓ⁻¹ • x) * chiSmall M (ℓ⁻¹ • (x - z)))
      = ℓ ^ 3 * conv3Small M (ℓ⁻¹ • z) := by
  have hsc := integral_comp_smul_right (g := fun x : ℝ³ =>
    chiSmall M (ℓ⁻¹ • x) * chiSmall M (ℓ⁻¹ • (x - z))) hℓ
  have h1 (s : ℝ³) : ℓ⁻¹ • (ℓ • s) = s := by
    rw [smul_smul]
    change (ℓ⁻¹ * ℓ) • s = s
    rw [inv_mul_cancel₀ (ne_of_gt hℓ), one_smul]
  have hpt : ∀ s : ℝ³, chiSmall M (ℓ⁻¹ • (ℓ • s)) * chiSmall M (ℓ⁻¹ • (ℓ • s - z))
      = chiSmall M s * chiSmall M (s - ℓ⁻¹ • z) := by
    intro s
    have h2 : ℓ⁻¹ • (ℓ • s - z) = s - ℓ⁻¹ • z := by
      rw [smul_sub]
      rw [h1 s]
    rw [h1 s, h2]
  calc
    (∫ x : ℝ³, chiSmall M (ℓ⁻¹ • x) * chiSmall M (ℓ⁻¹ • (x - z)))
        = ℓ ^ 3 * (∫ s : ℝ³, chiSmall M (ℓ⁻¹ • (ℓ • s)) * chiSmall M (ℓ⁻¹ • (ℓ • s - z))) := hsc
    _ = ℓ ^ 3 * (∫ s : ℝ³, chiSmall M s * chiSmall M (s - ℓ⁻¹ • z)) := by
        congr 1
        apply integral_congr_ae
        exact ae_of_all _ (by
          intro s
          change chiSmall M (ℓ⁻¹ • (ℓ • s)) * chiSmall M (ℓ⁻¹ • (ℓ • s - z))
              = chiSmall M s * chiSmall M (s - ℓ⁻¹ • z)
          exact hpt s)
    _ = ℓ ^ 3 * (∫ s : ℝ³, chiSmall M s * chiSmall M (ℓ⁻¹ • z - s)) := by
        congr 1
        apply integral_congr_ae
        exact ae_of_all _ (by
          intro s
          change chiSmall M s * chiSmall M (s - ℓ⁻¹ • z) = chiSmall M s * chiSmall M (ℓ⁻¹ • z - s)
          have harg : s - ℓ⁻¹ • z = -(ℓ⁻¹ • z - s) := by abel
          rw [harg, chiSmall_even hM (ℓ⁻¹ • z - s)])
    _ = ℓ ^ 3 * conv3Small M (ℓ⁻¹ • z) := rfl


/-- the `u`-integrated localised pair kernel (assembly step toward the
`∬w_{1,B(u)}` normalisation): the `u`-integral of
`wSmallPair M ℓ d u h x y` factors the (`u`-independent) renormalised kernel
through the two-point partition:

    ∫_u wSmallPair M ℓ d u h x y du
        = χ(x/ℓ)·χ(y/ℓ)·(χ_M⋆χ_M)((x−y)/(ℓd)) · wSmallScaled M (ℓd) h (x−y) / (χ⋆χ)((x−y)/ℓ) . -/
lemma chiSmallB_w_pair_uint {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u x y : ℝ³) (h : ℝ³ → ℝ) :
    (∫ v : ℝ³, wSmallPair M ℓ d v h x y)
      = chiScale ℓ x * chiScale ℓ y
          * conv3Small M ((ℓ * d)⁻¹ • (x - y)) * wSmallScaled M (ℓ * d) h (x - y)
          * (convScale ℓ (x - y))⁻¹ := by
  let c : ℝ := wSmallScaled M (ℓ * d) h (x - y) / convScale ℓ (x - y)
  have hfac :
      (∫ v : ℝ³, (chiSmallB M ℓ d v x * chiSmallB M ℓ d v y) * c)
        = (∫ v : ℝ³, chiSmallB M ℓ d v x * chiSmallB M ℓ d v y) * c := by
    let A : ℝ³ → ℝ := fun v => chiSmallB M ℓ d v x * chiSmallB M ℓ d v y
    calc
      (∫ v : ℝ³, A v * c) = (∫ v : ℝ³, c * A v) := by
          apply integral_congr_ae
          exact ae_of_all _ (by intro v; dsimp [A]; ring)
      _ = c * (∫ v : ℝ³, A v) := by
          exact MeasureTheory.integral_const_mul (μ := (volume : Measure ℝ³)) (r := c) (f := A)
      _ = (∫ v : ℝ³, A v) * c := by ring
  calc
    (∫ v : ℝ³, wSmallPair M ℓ d v h x y)
        = (∫ v : ℝ³, (chiSmallB M ℓ d v x * chiSmallB M ℓ d v y) * c) := by
            apply integral_congr_ae
            exact ae_of_all _ (by
              intro v
              dsimp [wSmallPair, c]
              ring)
    _ = (∫ v : ℝ³, chiSmallB M ℓ d v x * chiSmallB M ℓ d v y) * c := hfac
    _ = (chiScale ℓ x * chiScale ℓ y * conv3Small M ((ℓ * d)⁻¹ • (x - y))) * c := by
          rw [chiSmallB_partition_xy_u hM hℓ hd x y]
    _ = chiScale ℓ x * chiScale ℓ y
          * conv3Small M ((ℓ * d)⁻¹ • (x - y)) * wSmallScaled M (ℓ * d) h (x - y)
          * (convScale ℓ (x - y))⁻¹ := by
          dsimp [c]
          ring


lemma zeta1d_ge_sqrt2_div_two (t : ℝ) (ht : |t| ≤ 1 / 4) :
    Real.sqrt 2 / 2 ≤ zeta1d t := by
  rw [zeta1d_of_abs_le (le_trans ht (by norm_num : (1 : ℝ) / 4 ≤ 1 / 2))]
  exact Commons.Analysis.Real.cos_pi_mul_lower_bound_on_quarter t ht


/-- **Step B1**: on the cube `|z_j| ≤ 1/4`, the unnormalised M-th power base
is bounded below by `((√2/2)³)^M` (each `ζ ≥ √2/2` by Step A, product, power). -/
lemma chiSmallBase_cube_lower {M : ℕ} (hM : 1 ≤ M) (z : ℝ³)
    (hz : ∀ j : Fin 3, |z.ofLp j| ≤ 1 / 4) :
    ((Real.sqrt 2 / 2) ^ 3) ^ M ≤ chiSmallBase M z := by
  let r : ℝ := Real.sqrt 2 / 2
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr3 : 0 ≤ r ^ 3 := pow_nonneg hr0 3
  have hzeta (j : Fin 3) : r ≤ zeta1d (z.ofLp j) := by
    dsimp [r]
    exact zeta1d_ge_sqrt2_div_two (z.ofLp j) (hz j)
  have h01 : r * r ≤ zeta1d (z.ofLp 0) * zeta1d (z.ofLp 1) := by
    exact mul_le_mul (hzeta 0) (hzeta 1) hr0 (zeta1d_nonneg (z.ofLp 0))
  have hprod : r ^ 3 ≤ zeta1d (z.ofLp 0) * zeta1d (z.ofLp 1) * zeta1d (z.ofLp 2) := by
    calc
      r ^ 3 = (r * r) * r := by ring
      _ ≤ (zeta1d (z.ofLp 0) * zeta1d (z.ofLp 1)) * zeta1d (z.ofLp 2) := by
          exact mul_le_mul h01 (hzeta 2) hr0
            (mul_nonneg (zeta1d_nonneg (z.ofLp 0)) (zeta1d_nonneg (z.ofLp 1)))
      _ = zeta1d (z.ofLp 0) * zeta1d (z.ofLp 1) * zeta1d (z.ofLp 2) := by ring
  have hpow : (r ^ 3) ^ M ≤ (zeta1d (z.ofLp 0) * zeta1d (z.ofLp 1) * zeta1d (z.ofLp 2)) ^ M := by
    exact pow_le_pow_left₀ hr3 hprod M
  change (r ^ 3) ^ M ≤ (zeta1d (z.ofLp 0) * zeta1d (z.ofLp 1) * zeta1d (z.ofLp 2)) ^ M
  exact hpow


/-- the unnormalised M-th power base is pointwise `≤ 1` (each `ζ ∈ [0,1]`). -/
lemma chiSmallBase_le_one (M : ℕ) (z : ℝ³) : chiSmallBase M z ≤ 1 := by
  dsimp [chiSmallBase]
  have hn (j : Fin 3) : 0 ≤ zeta1d (z.ofLp j) := zeta1d_nonneg (z.ofLp j)
  have hl (j : Fin 3) : zeta1d (z.ofLp j) ≤ 1 := zeta1d_le_one (z.ofLp j)
  have hp01 : (zeta1d (z.ofLp 0) * zeta1d (z.ofLp 1)) * zeta1d (z.ofLp 2) ≤ 1 := by
    calc
      (zeta1d (z.ofLp 0) * zeta1d (z.ofLp 1)) * zeta1d (z.ofLp 2)
          ≤ 1 * zeta1d (z.ofLp 2) := by
              exact mul_le_mul_of_nonneg_right (by
                calc zeta1d (z.ofLp 0) * zeta1d (z.ofLp 1) ≤ 1 * zeta1d (z.ofLp 1) :=
                        mul_le_mul_of_nonneg_right (hl 0) (hn 1)
                     _ = zeta1d (z.ofLp 1) := by simp
                     _ ≤ 1 := hl 1) (hn 2)
      _ = zeta1d (z.ofLp 2) := by simp
      _ ≤ 1 := hl 2
  have hpow : (zeta1d (z.ofLp 0) * zeta1d (z.ofLp 1) * zeta1d (z.ofLp 2)) ^ M ≤ 1 := by
    have hnon : 0 ≤ zeta1d (z.ofLp 0) * zeta1d (z.ofLp 1) * zeta1d (z.ofLp 2) :=
      mul_nonneg (mul_nonneg (hn 0) (hn 1)) (hn 2)
    have hle1 : zeta1d (z.ofLp 0) * zeta1d (z.ofLp 1) * zeta1d (z.ofLp 2) ≤ 1 := by
      -- align assoc with hp01: change (…)*… ≤ 1
      change (zeta1d (z.ofLp 0) * zeta1d (z.ofLp 1)) * zeta1d (z.ofLp 2) ≤ 1
      exact hp01
    calc
      (zeta1d (z.ofLp 0) * zeta1d (z.ofLp 1) * zeta1d (z.ofLp 2)) ^ M ≤ 1 ^ M :=
          pow_le_pow_left₀ hnon hle1 M
      _ = 1 := by simp
  exact hpow


/-- the base vanishes outside the unit cube `{|z_j| ≤ 1/2}` (support
containment, contrapositive). -/
lemma chiSmallBase_eq_zero_of_not_mem_cube {M : ℕ} (hM : 1 ≤ M) (z : ℝ³)
    (hz : z ∉ {x : ℝ³ | ∀ j : Fin 3, |x.ofLp j| ≤ 1 / 2}) : chiSmallBase M z = 0 := by
  have hne : ∃ j : Fin 3, ¬ |z.ofLp j| ≤ 1 / 2 := by
    simpa using hz
  rcases hne with ⟨j, hj⟩
  have hz1 : 1 / 2 < |z.ofLp j| := not_le.mp hj
  have h0 : zeta1d (z.ofLp j) = 0 := zeta1d_of_one_half_lt hz1
  have hbase0 : zeta1d (z.ofLp 0) * zeta1d (z.ofLp 1) * zeta1d (z.ofLp 2) = 0 := by
    fin_cases j
    · have h0j : zeta1d (z.ofLp (0 : Fin 3)) = 0 := by simpa using h0
      rw [h0j]
      simp
    · have h0j : zeta1d (z.ofLp (1 : Fin 3)) = 0 := by simpa using h0
      rw [h0j]
      simp
    · have h0j : zeta1d (z.ofLp (2 : Fin 3)) = 0 := by simpa using h0
      rw [h0j]
      simp
  dsimp [chiSmallBase]
  rw [hbase0]
  exact zero_pow (ne_of_gt (lt_of_lt_of_le zero_lt_one hM))
/-- the square of the base is pointwise `≤ 1` (base ∈ [0,1]). -/
lemma chiSmallBase_sq_le_one (M : ℕ) (z : ℝ³) : (chiSmallBase M z) ^ 2 ≤ 1 := by
  have hb0 : 0 ≤ chiSmallBase M z := chiSmallBase_nonneg M z
  have hb1 : chiSmallBase M z ≤ 1 := chiSmallBase_le_one M z
  calc
    (chiSmallBase M z) ^ 2 = chiSmallBase M z * chiSmallBase M z := by ring
    _ ≤ chiSmallBase M z * 1 := mul_le_mul_of_nonneg_left hb1 hb0
    _ = chiSmallBase M z := by ring
    _ ≤ 1 := hb1

/-- **Step B2**: the normalisation integral satisfies `chiSmallNormSq M ≤ 1`
(the base is ≤ 1 and supported in the unit cube of volume 1). -/
lemma chiSmallNormSq_le_one {M : ℕ} (hM : 1 ≤ M) : chiSmallNormSq M ≤ 1 := by
  dsimp [chiSmallNormSq]
  let C : Set ℝ³ := {z : ℝ³ | ∀ j : Fin 3, |z.ofLp j| ≤ 1 / 2}
  have hCmeas : MeasurableSet C := by
    dsimp [C]
    exact eucl_cube_measurable (c := (1 / 2 : ℝ))
  have hCvol : (volume : Measure ℝ³) C = ENNReal.ofReal 1 := by
    have hvol := eucl_cube_volume (c := (1 / 2 : ℝ)) (by norm_num : 0 ≤ (1 / 2 : ℝ))
    have hx : (2 * (1 / 2 : ℝ)) ^ 3 = 1 := by norm_num
    dsimp [C]
    simpa [hx] using hvol
  have hCfin : (volume : Measure ℝ³) C ≠ (∞ : ℝ≥0∞) :=
    ne_of_lt (lt_of_le_of_lt (le_of_eq hCvol) ENNReal.ofReal_lt_top)
  -- pointwise: base² = 1_C · base²  (vanishes off C)
  have hindpt : (fun z : ℝ³ => (chiSmallBase M z) ^ 2)
      = C.indicator (fun z : ℝ³ => (chiSmallBase M z) ^ 2) := by
    funext z
    by_cases hz : z ∈ C
    · simp [hz]
    · have hz' : chiSmallBase M z = 0 := by
        exact chiSmallBase_eq_zero_of_not_mem_cube hM z (by simpa [C] using hz)
      simp [hz, hz']
  -- integrability of the square
  have hcont2 : Continuous (fun z : ℝ³ => (chiSmallBase M z) ^ 2) := by
    have hc := chiSmallBase_continuous M
    fun_prop
  have hcsq : HasCompactSupport (fun z : ℝ³ => (chiSmallBase M z) ^ 2) := by
    have hmon : Function.support (fun z : ℝ³ => (chiSmallBase M z) ^ 2)
        ⊆ Function.support (chiSmallBase M) := by
      intro z hz
      change chiSmallBase M z ≠ 0
      intro hb
      exact hz (by simp [hb])
    exact HasCompactSupport.mono (chiSmallBase_hasCompactSupport hM) hmon
  have hf_int : Integrable (fun z : ℝ³ => (chiSmallBase M z) ^ 2) (volume : Measure ℝ³) :=
    hcont2.integrable_of_hasCompactSupport hcsq
  -- restricted integral comparison
  have hm : (∫ z in C, (chiSmallBase M z) ^ 2)
      ≤ (∫ z in C, (fun _ : ℝ³ => (1 : ℝ)) z) := by
    refine MeasureTheory.setIntegral_mono_on ?_ ?_ hCmeas ?_
    · exact hf_int.integrableOn
    · exact MeasureTheory.integrableOn_const (μ := volume) (s := C) hCfin
    · intro z hz
      exact chiSmallBase_sq_le_one M z
  have hCconst : (∫ z in C, (fun _ : ℝ³ => (1 : ℝ)) z) = (volume : Measure ℝ³).real C := by
    have hc := MeasureTheory.setIntegral_const (μ := volume) (s := C) (c := (1 : ℝ))
    simpa [smul_eq_mul] using hc
  have hreal : (volume : Measure ℝ³).real C = 1 := by
    rw [MeasureTheory.measureReal_def]
    rw [hCvol, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1)]
  calc
    (∫ z : ℝ³, (chiSmallBase M z) ^ 2)
        = ∫ z : ℝ³, (C.indicator (fun z : ℝ³ => (chiSmallBase M z) ^ 2)) z := by
            rw [← hindpt]
    _ = ∫ z in C, (chiSmallBase M z) ^ 2 := by
        rw [MeasureTheory.integral_indicator hCmeas]
    _ ≤ ∫ z in C, (fun _ : ℝ³ => (1 : ℝ)) z := hm
    _ = (volume : Measure ℝ³).real C := hCconst
    _ = 1 := hreal


/-- **Step B2 (done)**: on `|z_j| ≤ 1/4`, the normalised bump satisfies
`((√2/2)³)^M ≤ χ_M(z)` (base lower bound + `χ_M = base/√S ≥ base` from
`√S ≤ 1`). -/
lemma chiSmall_cube_lower {M : ℕ} (hM : 1 ≤ M) (z : ℝ³)
    (hz : ∀ j : Fin 3, |z.ofLp j| ≤ 1 / 4) :
    ((Real.sqrt 2 / 2) ^ 3) ^ M ≤ chiSmall M z := by
  have hbase := chiSmallBase_cube_lower hM z hz
  have hS1 : chiSmallNormSq M ≤ 1 := chiSmallNormSq_le_one hM
  have hSpos : 0 < chiSmallNormSq M := chiSmallNormSq_pos hM
  have hb0 : 0 ≤ chiSmallBase M z := chiSmallBase_nonneg M z
  have hchi : chiSmallBase M z ≤ chiSmall M z := by
    dsimp [chiSmall]
    rw [div_eq_mul_inv]
    have hsq0 : 0 < Real.sqrt (chiSmallNormSq M) := Real.sqrt_pos.mpr hSpos
    have hsq : Real.sqrt (chiSmallNormSq M) ≤ 1 :=
      (Real.sqrt_le_one (x := chiSmallNormSq M)).2 hS1
    have hmul : chiSmallBase M z * Real.sqrt (chiSmallNormSq M) ≤ chiSmallBase M z := by
      calc
        chiSmallBase M z * Real.sqrt (chiSmallNormSq M)
            ≤ chiSmallBase M z * 1 := mul_le_mul_of_nonneg_left hsq hb0
        _ = chiSmallBase M z := by ring
    have hm2 := mul_le_mul_of_nonneg_right hmul
      (inv_nonneg.mpr (le_of_lt hsq0))
    have hcancel : (chiSmallBase M z * Real.sqrt (chiSmallNormSq M)) *
        (Real.sqrt (chiSmallNormSq M))⁻¹ = chiSmallBase M z := by
      field_simp [ne_of_gt hsq0]
    rwa [hcancel] at hm2
  exact le_trans hbase hchi


/-- **Step C / conv3Small-support lemma**: the cosine-M self-convolution is
positive near zero — for `|z_j| ≤ 1/16` all `j`, `0 < (χ_M⋆χ_M)(z)`.
Proof (cleaner than the subcube route): `conv3Small M z = ∫_y f y` with
`f y := χ_M(y)·χ_M(z−y)` continuous, compactly supported (support ⊆ the unit
cube), nonnegative, and `f 0 = χ_M(0)·χ_M(z) > 0` (`χ_M(0) = 1/√S > 0`;
`χ_M(z) ≥ ((√2/2)³)^M > 0` by `chiSmall_cube_lower`) — so
`Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero` applies. -/
lemma conv3Small_pos_near_zero {M : ℕ} (hM : 1 ≤ M) (z : ℝ³)
    (hz : ∀ j : Fin 3, |z.ofLp j| ≤ 1 / 16) :
    0 < conv3Small M z := by
  dsimp [conv3Small]
  let f : ℝ³ → ℝ := fun y => chiSmall M y * chiSmall M (z - y)
  have hS : 0 < chiSmallNormSq M := chiSmallNormSq_pos hM
  have hchi0 : 0 < chiSmall M 0 := by
    have hb0 : chiSmallBase M 0 = 1 := chiSmallBase_zero M
    have hs0 : 0 < Real.sqrt (chiSmallNormSq M) := Real.sqrt_pos.mpr hS
    dsimp [chiSmall]
    rw [hb0]
    positivity
  have hzpos : 0 < chiSmall M z := by
    have hz4 : ∀ j : Fin 3, |z.ofLp j| ≤ 1 / 4 := by
      intro j
      exact le_trans (hz j) (by norm_num : (1 / 16 : ℝ) ≤ 1 / 4)
    have hlow := chiSmall_cube_lower hM z hz4
    have hr : 0 < Real.sqrt 2 / 2 := by positivity
    have hpow : 0 < ((Real.sqrt 2 / 2) ^ 3) ^ M := pow_pos (pow_pos hr 3) M
    exact lt_of_lt_of_le hpow hlow
  have hcont : Continuous f := by
    have hc := chiSmall_continuous hM
    dsimp [f]
    fun_prop
  have hcs : HasCompactSupport f := by
    change IsCompact (tsupport f)
    change IsCompact (closure (Function.support f))
    refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℝ³) (Real.sqrt 3 * (1 / 2)))
      isClosed_closure ?_
    calc
      closure (Function.support f)
          ⊆ closure (closedBall (0 : ℝ³) (Real.sqrt 3 * (1 / 2))) := by
            apply closure_mono
            intro y hy
            have hy' : chiSmall M y ≠ 0 := by
              intro hyc
              apply hy
              dsimp [f]
              rw [hyc]
              simp
            have hcube : ∀ j : Fin 3, |y.ofLp j| ≤ 1 / 2 :=
              fun j => chiSmall_support_mem_abs_le hM hy' j
            have hball : ‖y‖ ≤ Real.sqrt 3 * (1 / 2) := by
              have hmem : y ∈ {w : ℝ³ | ∀ j : Fin 3, |w.ofLp j| ≤ 1 / 2} := by
                change ∀ j : Fin 3, |y.ofLp j| ≤ 1 / 2
                exact hcube
              have hb := (coord_box_subset_eucl_ball (A := (1 / 2 : ℝ)) (by norm_num)) hmem
              simpa using hb
            simpa [Metric.mem_closedBall, dist_eq_norm, sub_eq_add_neg] using hball
      _ = closedBall (0 : ℝ³) (Real.sqrt 3 * (1 / 2)) := closure_closedBall
  have hnn : 0 ≤ f := by
    intro y
    dsimp [f]
    exact mul_nonneg (chiSmall_nonneg M y) (chiSmall_nonneg M (z - y))
  have hne : f 0 ≠ 0 := by
    dsimp [f]
    rw [sub_zero]
    exact mul_ne_zero (ne_of_gt hchi0) (ne_of_gt hzpos)
  exact Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (f := f) (x := 0) hcont hcs hnn hne

/-- coordinate-`∞`-bound → convolution-positivity: if `‖z‖ ≤ 1/16` then
`(χ_M⋆χ_M)(z) ≠ 0`. -/
lemma conv3Small_ne_zero_of_norm_le {M : ℕ} (hM : 1 ≤ M) (z : ℝ³) (hz : ‖z‖ ≤ 1 / 16) :
    conv3Small M z ≠ 0 := by
  have hzj : ∀ j : Fin 3, |z.ofLp j| ≤ 1 / 16 := by
    intro j
    exact le_trans (coord_abs_le_norm z j) hz
  exact ne_of_gt (conv3Small_pos_near_zero hM z hzj)

/-- scaling: `‖c⁻¹ • z‖ ≤ 1/16` from `‖z‖ ≤ c/16` (`c > 0`). -/
lemma norm_inv_smul_le {c : ℝ} (hc : 0 < c) (z : ℝ³) (hz : ‖z‖ ≤ c / 16) :
    ‖c⁻¹ • z‖ ≤ 1 / 16 := by
  have hnorm : ‖c⁻¹ • z‖ = c⁻¹ * ‖z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
  calc
    ‖c⁻¹ • z‖ = c⁻¹ * ‖z‖ := hnorm
    _ ≤ c⁻¹ * (c / 16) := by
        exact mul_le_mul_of_nonneg_left hz (le_of_lt (inv_pos.mpr hc))
    _ = 1 / 16 := by
        field_simp [ne_of_gt hc]

/-- converse: if `‖c⁻¹•z‖ > 1/16` then `c/16 < ‖z‖` (`c > 0`). -/
lemma lt_norm_of_not_norm_inv_smul_le {c : ℝ} (hc : 0 < c) (z : ℝ³)
    (h : ¬ ‖c⁻¹ • z‖ ≤ 1 / 16) : c / 16 < ‖z‖ := by
  have hgt : (1 / 16 : ℝ) < ‖c⁻¹ • z‖ := lt_of_not_ge h
  have hnorm : ‖c⁻¹ • z‖ = c⁻¹ * ‖z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
  rw [hnorm] at hgt
  have hmul := mul_lt_mul_of_pos_left hgt hc
  have hleft : c * (1 / 16 : ℝ) = c / 16 := by ring
  have hright : c * (c⁻¹ * ‖z‖) = ‖z‖ := by
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hc), one_mul]
  rwa [hleft, hright] at hmul

/-- **renormalisation-denominator cancellation**: when the numerator `h` is
supported inside `ball 0 R` with `R ≤ c/16`, the denominator
`(χ_M⋆χ_M)(c⁻¹•z)` is nonzero wherever `h z ≠ 0`, so pointwise
`convScaleSmall·wSmallScaled = h`. -/
lemma convScaleSmall_mul_wSmallScaled {M : ℕ} (hM : 1 ≤ M) {c : ℝ} (hc : 0 < c)
    {R : ℝ} {h : ℝ³ → ℝ} (hsupp : ∀ z : ℝ³, R ≤ ‖z‖ → h z = 0) (hR : R ≤ c / 16)
    (z : ℝ³) :
    convScaleSmall M c z * wSmallScaled M c h z = h z := by
  by_cases hconv : convScaleSmall M c z = 0
  · have hz0 : h z = 0 := by
      have hnz : conv3Small M (c⁻¹ • z) = 0 := by
        simpa [convScaleSmall] using hconv
      have hnle : ¬ ‖c⁻¹ • z‖ ≤ 1 / 16 := by
        intro hle
        exact (conv3Small_ne_zero_of_norm_le hM (c⁻¹ • z) hle) hnz
      have hgt : c / 16 < ‖z‖ := lt_norm_of_not_norm_inv_smul_le hc z hnle
      exact hsupp z (le_of_lt (lt_of_le_of_lt hR hgt))
    simp [hconv, hz0]
  · have hw : wSmallScaled M c h z = h z / convScaleSmall M c z := rfl
    calc
      convScaleSmall M c z * wSmallScaled M c h z
          = convScaleSmall M c z * (h z / convScaleSmall M c z) := by rw [hw]
      _ = h z := by
          rw [mul_comm]
          exact div_mul_cancel₀ (a := h z) hconv

/-- **u-integrated localised pair kernel with the renormalisation cancelled**
(exact): under the support regime `R ≤ (ℓd)/16` the
`(χ_M⋆χ_M)((x−y)/(ℓd))`-denominator never vanishes where the numerator `h`
is supported, so

    ∫_v wSmallPair M ℓ d v h x y = χ_M(x/ℓ)·χ_M(y/ℓ)·h(x−y).  -/
lemma chiSmallB_w_pair_uint_cancel {M : ℕ} (hM : 1 ≤ M) {ℓ d R : ℝ} {h : ℝ³ → ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d)
    (hsupp : ∀ z : ℝ³, R ≤ ‖z‖ → h z = 0) (hR : R ≤ (ℓ * d) / 16)
    (x y : ℝ³) :
    (∫ v : ℝ³, wSmallPair M ℓ d v h x y)
      = chiScale ℓ x * chiScale ℓ y * (h (x - y) / convScale ℓ (x - y)) := by
  have hc := convScaleSmall_mul_wSmallScaled (h := h) hM (mul_pos hℓ hd) hsupp hR (x - y)
  have hconv : conv3Small M ((ℓ * d)⁻¹ • (x - y)) = convScaleSmall M (ℓ * d) (x - y) := by rfl
  calc
    (∫ v : ℝ³, wSmallPair M ℓ d v h x y)
        = chiScale ℓ x * chiScale ℓ y
            * conv3Small M ((ℓ * d)⁻¹ • (x - y)) * wSmallScaled M (ℓ * d) h (x - y)
            * (convScale ℓ (x - y))⁻¹ :=
            chiSmallB_w_pair_uint hM hℓ hd 0 x y h
    _ = chiScale ℓ x * chiScale ℓ y * (h (x - y) / convScale ℓ (x - y)) := by
        rw [hconv, div_eq_mul_inv]
        rw [show (chiScale ℓ x * chiScale ℓ y * convScaleSmall M (ℓ * d) (x - y))
              * wSmallScaled M (ℓ * d) h (x - y) * (convScale ℓ (x - y))⁻¹
            = chiScale ℓ x * chiScale ℓ y
                * ((convScaleSmall M (ℓ * d) (x - y) * wSmallScaled M (ℓ * d) h (x - y))
                    * (convScale ℓ (x - y))⁻¹) by ring]
        rw [hc]


/-- value of the self-convolution at `0`: `(χ_M⋆χ_M)(0) = ∫χ_M² = 1` (the
`L²`-normalisation `chiSmall_L2` + evenness of `chiSmall`).  This is what
makes the eq:appw1sliding weighted form `ℓ³∫h(w)(χ⋆χ)(w/ℓ)dw` have the
correct `w = 0`-limit (weight exactly `1`, quadratic deviation elsewhere —
see `DLSlidingIntegral`). -/
lemma conv3Small_zero {M : ℕ} (hM : 1 ≤ M) : conv3Small M 0 = 1 := by
  dsimp [conv3Small]
  calc
    (∫ y : ℝ³, chiSmall M y * chiSmall M (0 - y))
        = (∫ y : ℝ³, chiSmall M y * chiSmall M (-y)) := by
            apply integral_congr_ae
            exact ae_of_all _ (by intro y; congr 1; abel)
    _ = (∫ y : ℝ³, (chiSmall M y) ^ 2) := by
            apply integral_congr_ae
            exact ae_of_all _ (by
              intro y
              change chiSmall M y * chiSmall M (-y) = (chiSmall M y) ^ 2
              rw [chiSmall_even hM y, pow_two])
    _ = 1 := chiSmall_L2 hM

/-- **corpus `w_{1,B(u)}` kernel, u-integrated with the renormalisation
cancelled**: for the chosen numerator `g₀ = v(1−ω₀)` supported inside
`ball 0 R0` with `R0 ≤ (ℓd)/16`,

    ∫_u wSmall1Pair h M ℓ d u x y du = χ_M(x/ℓ)·χ_M(y/ℓ)·g₀(x−y).  -/
lemma chiSmallB_w1_pair_uint_cancel {v : ℝ³ → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R0)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ (ℓ * d) / 16) (x y : ℝ³) :
    (∫ u : ℝ³, wSmall1Pair h M ℓ d u x y)
      = chiScale ℓ x * chiScale ℓ y * (g0 v h (x - y) / convScale ℓ (x - y)) := by
  unfold wSmall1Pair
  exact chiSmallB_w_pair_uint_cancel (h := g0 v h) hM hℓ hd
    (fun z hz => g0_zero_of_norm_ge (v := v) (R := R0) hv_supp hz h) hR x y

end BoseGases

end Submission
