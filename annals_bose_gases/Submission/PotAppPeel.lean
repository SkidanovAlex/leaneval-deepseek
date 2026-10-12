import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Submission.PotChosen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# potapp helper 1 — single-slot peel bound with a fibre-bounded kernel

Master lemma for the `potapp_q4` (FS `lm:potapp`) transcription in
`Submission.PotAppFull`: to control the excited-pair sums
`Σ_{p∈pairSet}∫ (PΦ)²·k(x_{p.1},x_{p.2})` for kernels `k := wPair(ℓ,g₀)`
(and its absolute value), we only need ONE abstract measure-theoretic fact:

    peel_sq_kernel_le:  for `i ≠ j`, `Ψ` continuous, and a kernel `k` with
    the second-argument fibre bound `∀x, |∫_y k x y| ≤ C`,

        ∫_x (aP ℓ i Ψ x)² · k (x j) (x i)  ≤  C · (ℓ³)⁻¹ · ∫_x (aP ℓ i Ψ x)²

    (`abox N ℓ` integrals).  Proof: the factor `(aPℓiΨ)` is constant in the
    `i`-slot (`aP_const_in_coord`), so peel the `i`-coordinate
    (`abox_integral_peel`): the inner `y`-integral is `∫_y k((kcInsN…)j,y)`,
    which is `≤ C` by the fibre bound pointwise (and the relabelled `j`-slot
    is `r j'` via `kc_insN_apply_succ`); then
    `∫_r (aPℓiΨ)(0-inserted r)² dr = (ℓ³)⁻¹∫_x(aPℓiΨ)²`
    (`aP_fiber_const_one`).  `|w1|-fibre`: `w1 = wPair(ℓ,g₀)` is symmetric
    (`wPairC_g0_sym`), `|w1(x,y)| = wPair(ℓ,|g₀|)(x,y)` pointwise, and the
    domination bound `∫_y |w1(x,y)|dy ≤ chiSup²·2·∫|g₀| = chiSup²·2·8π·a v`
    (`w1abs_fibre_acube_abs_le`) is proved below directly from
    `|wScaled| ≤ 2|h|`, `|χℓ| ≤ chiSup` (use `fibre_acube_abs_le` with
    `h := |g0 v h|` and the identity `∫|g₀| = ∫g₀ = 8π·a v` from
    `g0_nonneg_ae` + `g0_integral`, or repeat its domination argument).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Submission

open _root_.BoseGases
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Single-slot peel bound: a squared `Pᵢ`-projection against a kernel
`k (x j) (x i)` with second-argument fibre bound `C`. -/
lemma peel_sq_kernel_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N} (hij : i ≠ j)
    {k : ℝ³ → ℝ³ → ℝ} {C : ℝ}
    (hkC : ∀ x : ℝ³, |∫ y in acube ℓ, k x y| ≤ C)
    {Ψ : XN N → ℝ} (hΨc : Continuous Ψ)
    (hki : IntegrableOn (fun x : XN N => (aP ℓ i Ψ x) ^ 2 * k (x j) (x i))
      (abox N ℓ) volume) :
    (∫ x in abox N ℓ, (aP ℓ i Ψ x) ^ 2 * k (x j) (x i))
      ≤ C * (ℓ ^ 3)⁻¹ * (∫ x in abox N ℓ, (aP ℓ i Ψ x) ^ 2) := by
  cases N with
  | zero =>
      exfalso
      exact Nat.not_lt_zero i.1 i.isLt
  | succ n =>
      cases n with
      | zero =>
          exfalso
          have hi0 : i.1 = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt)
          have hj0 : j.1 = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt)
          exact hij (Fin.ext (hi0.trans hj0.symm))
      | succ p =>
          rcases Fin.exists_succAbove_eq (x := j) (y := i) hij.symm with ⟨j', hj'⟩
          let A : X (p + 2) → ℝ := fun x => (aP ℓ i Ψ x) ^ 2
          let A0 : X (p + 1) → ℝ := fun r => (aP ℓ i Ψ (kcInsN (p + 1) i (0, r))) ^ 2
          let F : X (p + 2) → ℝ := fun x => A x * k (x j) (x i)
          have hF_int : IntegrableOn F (abox (p + 2) ℓ) volume := by
            simpa [F, A] using hki
          have hzi : ∀ (r : X (p + 1)) (y : kcE3),
              (kcInsN (p + 1) i (y, r)) i = y := fun r y => kc_insN_apply_same (p + 1) i y r
          have hzj : ∀ (r : X (p + 1)) (y : kcE3),
              (kcInsN (p + 1) i (y, r)) j = r j' := by
            intro r y
            rw [← hj']
            exact kc_insN_apply_succ (p + 1) i y r j'
          have hA0const : ∀ (r : X (p + 1)) (y : kcE3),
              A (kcInsN (p + 1) i (y, r)) = A0 r := by
            intro r y
            dsimp [A, A0]
            exact congrArg (fun u : ℝ => u ^ 2) (aP_fiber_const_one hℓ i hΨc y r)
          have hpoint : ∀ r : X (p + 1),
              (fun y : kcE3 => F (kcInsN (p + 1) i (y, r))) =
                fun y : kcE3 => A0 r * k (r j') y := by
            intro r
            funext y
            dsimp [F]
            rw [hzi r y, hzj r y, hA0const r y]
          have hfib : ∀ r : X (p + 1),
              (∫ y in acube ℓ, F (kcInsN (p + 1) i (y, r))) =
                A0 r * (∫ y in acube ℓ, k (r j') y) := by
            intro r
            calc
              (∫ y in acube ℓ, F (kcInsN (p + 1) i (y, r)))
                  = ∫ y in acube ℓ, A0 r * k (r j') y := by
                      apply integral_congr_ae
                      filter_upwards with y
                      exact congrFun (hpoint r) y
              _ = A0 r * (∫ y in acube ℓ, k (r j') y) := by
                      rw [MeasureTheory.integral_const_mul]
          have hpeel := abox_integral_peel (n := p + 1) (i := i) (F := F) hF_int
          have hmain : (∫ x in abox (p + 2) ℓ, A x * k (x j) (x i))
              = ∫ r in abox (p + 1) ℓ, A0 r * (∫ y in acube ℓ, k (r j') y) := by
            calc
              (∫ x in abox (p + 2) ℓ, A x * k (x j) (x i))
                  = ∫ r in abox (p + 1) ℓ, (∫ y in acube ℓ,
                      F (kcInsN (p + 1) i (y, r))) := by
                      change (∫ x in abox (p + 2) ℓ, F x)
                          = ∫ r in abox (p + 1) ℓ, (∫ y in acube ℓ,
                              F (kcInsN (p + 1) i (y, r)))
                      rw [hpeel]
              _ = ∫ r in abox (p + 1) ℓ, A0 r * (∫ y in acube ℓ, k (r j') y) := by
                      apply integral_congr_ae
                      filter_upwards with r
                      exact hfib r
          have hfib_le : ∀ r : X (p + 1),
              A0 r * (∫ y in acube ℓ, k (r j') y) ≤ A0 r * C := by
            intro r
            have hle1 : (∫ y in acube ℓ, k (r j') y) ≤ C := (abs_le.mp (hkC (r j'))).2
            have hA0n : 0 ≤ A0 r := by
              dsimp [A0]
              exact sq_nonneg _
            exact mul_le_mul_of_nonneg_left hle1 hA0n
          have hbnd : (∫ x in abox (p + 2) ℓ, A x * k (x j) (x i))
              ≤ ∫ r in abox (p + 1) ℓ, A0 r * C := by
            rw [hmain]
            refine integral_mono_ae ?_ ?_ ?_
            · have hf0 : Integrable (fun r : X (p + 1) =>
                  ∫ y in acube ℓ, F (kcInsN (p + 1) i (y, r)))
                  (volume.restrict (abox (p + 1) ℓ)) :=
                abox_peel_inner_integrable (n := p + 1) (i := i) (F := F) hF_int
              refine hf0.congr ?_
              filter_upwards with r
              exact hfib r
            · have hA0c : Continuous A0 := by
                have hc1 : Continuous (fun r : X (p + 1) => kcInsN (p + 1) i (0, r)) :=
                  (kcInsN_cont (n := p + 1) i).comp
                    (by fun_prop : Continuous fun r : X (p + 1) => ((0 : kcE3), r))
                exact (aP_sq_continuous hℓ i hΨc).comp hc1
              exact integrableOn_abox_of_continuous hℓ (hA0c.mul continuous_const)
            · filter_upwards with r
              exact hfib_le r
          have hA_int : IntegrableOn A (abox (p + 2) ℓ) volume := by
            simpa [A] using integrableOn_sq_aP hℓ i hΨc
          have hpeelA := abox_integral_peel (n := p + 1) (i := i) (F := A) hA_int
          have hfibA : ∀ r : X (p + 1),
              (∫ y in acube ℓ, A (kcInsN (p + 1) i (y, r))) = (ℓ ^ 3) * A0 r := by
            intro r
            calc
              (∫ y in acube ℓ, A (kcInsN (p + 1) i (y, r)))
                  = ∫ y in acube ℓ, A0 r := by
                      apply integral_congr_ae
                      filter_upwards with y
                      exact hA0const r y
              _ = (ℓ ^ 3) * A0 r := by
                      rw [integral_const_acube ℓ hℓ]
                      ring
          have hAvol : (∫ x in abox (p + 2) ℓ, A x) = (ℓ ^ 3) * ∫ r in abox (p + 1) ℓ, A0 r := by
            calc
              (∫ x in abox (p + 2) ℓ, A x)
                  = ∫ r in abox (p + 1) ℓ, (∫ y in acube ℓ,
                      A (kcInsN (p + 1) i (y, r))) := hpeelA
              _ = ∫ r in abox (p + 1) ℓ, (ℓ ^ 3) * A0 r := by
                      apply integral_congr_ae
                      filter_upwards with r
                      exact hfibA r
              _ = (ℓ ^ 3) * ∫ r in abox (p + 1) ℓ, A0 r := by
                      rw [MeasureTheory.integral_const_mul]
          calc
            (∫ x in abox (p + 2) ℓ, (aP ℓ i Ψ x) ^ 2 * k (x j) (x i))
                = ∫ x in abox (p + 2) ℓ, A x * k (x j) (x i) := by
                    rfl
            _ ≤ ∫ r in abox (p + 1) ℓ, A0 r * C := hbnd
            _ = C * ∫ r in abox (p + 1) ℓ, A0 r := by
                    rw [MeasureTheory.integral_mul_const]
                    ring
            _ = C * (ℓ ^ 3)⁻¹ * (∫ x in abox (p + 2) ℓ, (aP ℓ i Ψ x) ^ 2) := by
                    have hℓ3nz : ℓ ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hℓ)
                    rw [show (∫ x in abox (p + 2) ℓ, (aP ℓ i Ψ x) ^ 2)
                          = (ℓ ^ 3) * (∫ r in abox (p + 1) ℓ, A0 r) by simpa [A] using hAvol]
                    field_simp [hℓ3nz]

/-- The absolute value of the pair kernel equals the pair kernel of the
absolute-value numerator, pointwise: `|wPair(ℓ,g)(x,y)| = wPair(ℓ,|g|)(x,y)`
(holds because `χ_ℓ ≥ 0` and `(χ⋆χ)_ℓ ≥ 0`). -/
lemma wPair_abs_eq (ℓ : ℝ) (g : ℝ³ → ℝ) (x y : ℝ³) :
    |wPair ℓ g x y| = wPair ℓ (fun z : ℝ³ => |g z|) x y := by
  have hcsx : 0 ≤ chiScale ℓ x := chiScale_nonneg ℓ x
  have hcsy : 0 ≤ chiScale ℓ y := chiScale_nonneg ℓ y
  have hconv : 0 ≤ convScale ℓ (x - y) := convScale_nonneg ℓ (x - y)
  dsimp [wPair, wScaled]
  calc
    |chiScale ℓ x * (g (x - y) / convScale ℓ (x - y)) * chiScale ℓ y|
        = |chiScale ℓ x * (g (x - y) / convScale ℓ (x - y))| * |chiScale ℓ y| := by
            rw [abs_mul]
    _ = chiScale ℓ x * |g (x - y) / convScale ℓ (x - y)| * chiScale ℓ y := by
            rw [abs_mul, abs_of_nonneg hcsx, abs_of_nonneg hcsy]
    _ = chiScale ℓ x * (|g (x - y)| / convScale ℓ (x - y)) * chiScale ℓ y := by
            rw [abs_div, abs_of_nonneg hconv]
    _ = chiScale ℓ x * (|g (x - y)| / convScale ℓ (x - y)) * chiScale ℓ y := by
            rfl

/-- Chosen-branch fibre bound for `|w₁|`: `∫_y |wPair(ℓ,g₀)(x,y)| dy ≤
chiSup²·2·(8π·a v)` pointwise in `x`. -/
lemma w1abs_fibre_acube_abs_le {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) (x : ℝ³) :
    |(∫ y in acube ℓ, |wPair ℓ (g0 v h) x y|)| ≤ chiSup ^ 2 * 2 * (8 * π * a v) := by
  let hAbs : ℝ³ → ℝ := fun z => |g0 v h z|
  have hAbsI : MeasureTheory.Integrable hAbs := by
    have hi := g0_integrable hR hv_supp h
    simpa [hAbs, Real.norm_eq_abs] using hi.abs
  have hAbs_supp : ∀ z : ℝ³, R ≤ ‖z‖ → hAbs z = 0 := by
    intro z hz
    dsimp [hAbs]
    rw [g0_zero_of_norm_ge hv_supp hz h, abs_zero]
  have hnn : ∀ᵐ z : ℝ³, 0 ≤ g0 v h z := g0_nonneg_ae hR hv_nonneg hvrad hv_supp h
  have hAbs_eq : (∫ z : ℝ³, |hAbs z|) = 8 * π * a v := by
    have hEq1 : (∫ z : ℝ³, |hAbs z|) = ∫ z : ℝ³, |g0 v h z| := by
      apply integral_congr_ae
      filter_upwards with z
      dsimp [hAbs]
      exact abs_abs (g0 v h z)
    have hEq2 : (∫ z : ℝ³, |g0 v h z|) = ∫ z : ℝ³, g0 v h z := by
      apply integral_congr_ae
      filter_upwards [hnn] with z hz
      exact abs_of_nonneg hz
    rw [hEq1, hEq2, g0_integral hR hv_supp h]
  have hint : (∫ y in acube ℓ, |wPair ℓ (g0 v h) x y|)
      = ∫ y in acube ℓ, wPair ℓ hAbs x y := by
    apply integral_congr_ae
    filter_upwards with y
    exact wPair_abs_eq ℓ (g0 v h) x y
  calc
    |(∫ y in acube ℓ, |wPair ℓ (g0 v h) x y|)|
        = |∫ y in acube ℓ, wPair ℓ hAbs x y| := by
            rw [hint]
    _ ≤ chiSup ^ 2 * 2 * (∫ z : ℝ³, |hAbs z|) := by
            exact fibre_acube_abs_le (h := hAbs) hℓ (le_of_lt hR) hRℓ hAbsI hAbs_supp x
    _ = chiSup ^ 2 * 2 * (8 * π * a v) := by
            rw [hAbs_eq]

end BoseGases

end Submission
