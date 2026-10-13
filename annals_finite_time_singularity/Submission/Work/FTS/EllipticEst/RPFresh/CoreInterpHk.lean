import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.EllipticEst.interpol_defs
import Submission.Work.FTS.EllipticEst.HkNorm_add_le
import Submission.Work.FTS.EllipticEst.hardy_shift_two_same_weight
import Submission.Work.FTS.EllipticEst.zHardy_sq_le
import Submission.Work.FTS.EllipticEst.zAMGM_Hk_le
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.FTS.EllipticEst.RPFresh.RadialIBP
import Submission.Work.FTS.EllipticEst.RPFresh.AngIBP
-- the pieces of the final assembly (all proved elsewhere in the workspace)
import Submission.Work.FTS.EllipticEst.RPFresh.LHSDecomp
import Submission.Work.FTS.EllipticEst.RPFresh.MixedFamilyAlpha1
import Submission.Work.FTS.EllipticEst.RPFresh.I0FamilyBound
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.EllipticEst.HkMem_add_smoothOpen
import Submission.Work.FTS.EllipticEst.HkIntegrand_add_le_open
import Submission.Work.FTS.EllipticEst.Alpha4.Assembly
import Submission.Work.FTS.EllipticEst.Alpha4.integrable_slice_pthDz_sigma
import Submission.Work.FTS.EllipticEst.RPFresh.slice_z_integrable
import Submission.Work.FTS.EllipticEst.RPFresh.slice_mixed_integrable
import Submission.Work.FTS.EllipticEst.RPFresh.HkMem_of_agreeOnQ
import Submission.Work.FTS.EllipticEst.RPFresh.HkNorm_le_of_HkSq_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.RPFresh

set_option autoImplicit false

/-!
# `CoreInterpHk` — the two-dimensional weighted interpolation for `α D_z ∂_θ`

Target (unchanged, as requested):

```
theorem CoreInterpHk (k : ℕ) (hk : 2 ≤ k) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (V : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → Work.Spaces.SmoothNbhd V →
      Work.Spaces.VanishTheta V →
      Work.Spaces.HkMem α k V →
      Work.Spaces.HkMem α k (Work.Spaces.Dz V) →
      Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ) →
      Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 V) →
      Work.Spaces.HkNorm α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ)
        ≤ C * (α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ)
            + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 V)
            + α * Work.Spaces.HkNorm α k (Work.Spaces.Dz V)) := by
```

## Route of the proof (complete analysis; see `NOTES_CoreInterpHk.md`)

All the mathematics is in the weighted `η`-currency (`σ θ = sin(2θ)^{-η}`, `η = 99/100`).

### 1. The base case (`interp_base_case`)

The same estimate as the workspace's long-standing
`Work.FTS.EllipticEst.interpol_mixed_weighted`: for `h` smooth on a neighbourhood of the
closed quadrant, `VanishTheta h`, the four functionals finite and the two radial boundary
products vanishing,

  `α² mixInt h ≤ C (α⁴ ddInt h + ttInt h + α² dInt h)`.

Proof.  Put `ψ = D_zh` (so that `D_z∂_θh = ∂_θψ`), `X = mixInt h`, `DD = ddInt h`,
`TT = ttInt h`, `D = dInt h`, and `σ' = -2η cos(2θ) sin(2θ)^{-1-η}`,
`σ'' = 4η(1+η)cos²(2θ)sin(2θ)^{-2-η} + 4ηsin(2θ)^{-η}`.

* **IBP in `θ`.**  `∂_θ(σψ∂_θψ) = σ(∂_θψ)² + σψ∂_θ²ψ + σ'ψ∂_θψ`, and the boundary terms
  `[σψ∂_θψ]_{θ=0}^{π/2}` vanish (`ψ(z,0) = ψ(z,π/2) = 0`, `σψ∂_θψ = O(sin(2θ)^{1-η})`);
  the `σ'`-term is turned around once more, with the same vanishing boundary.  Result:
  `X = -∫∫w²σ(D_zh)(D_z∂_θ²h) + 2η(1+η)∫∫w²cos²(2θ)sin(2θ)^{-2-η}(D_zh)²
        + 2η∫∫w²σ(D_zh)²`.
* **Sharp Hardy in `θ`** (`hardy_shift_two_same_weight`, applied to the `θ`-slice of `D_zh`,
  which vanishes at `θ = 0, π/2`):
  `∫σ(D_zh)²sin(2θ)^{-2} ≤ (1+η)^{-2}∫σ(∂_θD_zh)² + C∫σ(D_zh)²`, so the `cos²`-term is
  `≤ (2η/(1+η))X + C₁D`; the `η`-term is `2ηD`.
* **IBP in `z`** (`∂_t` in `t = log z`, where `ρ = w²z² = (1+z)^4/z²` and
  `∂_z(w²z²) = w²z·2(z-1)/(1+z)`, `|2(z-1)/(1+z)| ≤ 3`;
  `z·(w²)' = -4w²/(1+z)` is `Work.FTS.EllipticEst.AngSecond.z_mul_deriv_w2`):
  `-∫∫w²σ(D_zh)(D_z∂_θ²h) = ∫∫w²σ(D_z²h)(∂_θ²h) + ∫∫w²σ((z-3)/(1+z))(D_zh)(∂_θ²h)
     + (boundary terms)`, and the boundary terms are exactly the two `Tendsto` hypotheses.
* **Assembly.**  Cauchy–Schwarz gives
  `X ≤ (2η/(1+η))X + √(DD·TT) + 3√(D·TT) + (2η + C₁)D`, hence, since
  `1 - 2η/(1+η) = (1-η)/(1+η) = 1/199`,
  `X ≤ 199[√(DD·TT) + 3√(D·TT) + C·D]`; AM–GM (`2α²√(DD·TT) ≤ α⁴DD + TT`,
  `2α²√(D·TT) ≤ α²D + α²TT ≤ α²D + TT`) yields the stated form.

### 2. The slot bookkeeping in `HkSq`

With `Y(a,b) = ∫∫w²σ(D_z^a∂_θ^bV)²`:

* the first (`D_z`-)family of `HkIntegrand α k (αD_z∂_θV)` consists of the
  `α²(D_z^{i+1}∂_θV)²w²σ = α²X(D_z^iV)`, `i ≤ k`, so the base case applied to `h = D_z^iV`
  (`i = 0,…,k`) gives `α²Σ_{a≤k+1}Y(a,1) ≤ CΣ_{i≤k}(α⁴Y(i+2,0) + Y(i,2) + α²Y(i+1,0))`,
  every slot of which is a summand of the three right-hand `H^k`-norms:
  `Y(a,0)`, `a ≤ k+1`, of `HkMem (Dz V)`; `Y(a,2)`, `a ≤ k`, of `HkMem (pthIter 2 V)`;
  `Y(a,0)`, `a ≤ k+2`, of `HkMem (z²∂_z²V)` together with `HkMem (Dz V)`, via
  `D_z^a(z²∂_z²V) = D_z^{a+2}V - D_z^{a+1}V`;
* the mixed family consists of `(D_z^{j+1}D_θ^i∂_θV)²w²sin(2θ)^{-γ}`, `1 ≤ i`, `i+j ≤ k`.
  Expanding `D_θ^i∂_θ = Σ_{L=2}^{i+1}c_{i,L}∂_θ^L` with `|c_{i,L}| ≤ C_i sin(2θ)^{L-1}`
  (`Work.FTS.EllipticEst.DthIter_eq_sum_dthCoef` + `dthCoef_bound`) and using
  `sin(2θ)^{2L-2-γ} ≤ sin(2θ)^{-η}` for `L ≥ 2` bounds each summand by
  `C_kΣ_{L≤i+1}Y(j+1,L)`; the terms `L ≥ 3` are dominated by the mixed summands
  `(D_z^{j+1}D_θ^{L-2}∂_θ²V)²W²` of `HkSq α k (∂_θ²V)`, and the terms `L = 2` by the
  summands `Y(j+1,2)` of the first family of `HkSq α k (∂_θ²V)`;
* additivity of the norm (`HkNorm_add_le`) and homogeneity (`HkNorm_const_mul`) assemble the
  two families, and taking square roots gives the target.
-/

section Elementary

theorem sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem sig_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
  Real.rpow_nonneg (sin_two_nonneg hθ) _

/-- `w z ^ 2 * z ^ 2 = (1 + z)^4 / z^2`: the radial weight of the `t = log z` picture. -/
theorem w_sq_mul_zsq (z : ℝ) :
    (Work.Spaces.w z) ^ 2 * z ^ 2 = (1 + z) ^ 4 / z ^ 2 := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [Work.Spaces.w]
  · rw [Work.Spaces.w, div_pow]; field_simp

/-- The logarithmic derivative bound of the `z`-integration by parts:
`|∂_z (w²z²)/(w²z)| = |2(z-1)/(1+z)| ≤ 3` for `z > 0`. -/
theorem abs_two_mul_sub_one_div (z : ℝ) (hz : 0 < z) :
    |2 * (z - 1) / (1 + z)| ≤ 3 := by
  rw [abs_div, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 + z)]
  have h1 : |(2 : ℝ)| = 2 := by norm_num
  rw [h1, div_le_iff₀ (by linarith : (0 : ℝ) < 1 + z)]
  have h2 : |z - 1| ≤ z + 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  linarith

end Elementary

/-! ## Content lemmas: the `σ`-slots sit inside the right-hand `H^k`-norms

For `Y(a,b) = ∫∫w²σ(D_z^a∂_θ^bV)²` we need, for the bookkeeping:

* `Y(a,2)` as a summand of the first family of `HkSq α k (pthIter 2 V)` (`a ≤ k`);
* `Y(a,0)` as a summand of the first family of `HkSq α k (Dz V)` (`a ≤ k+1`).

Both are the existing `Work.Spaces.L2Sq_DzIter_le_HkSq` with the weight folded into the
function (and, in the second case, the operator shift `D_z^{a-1}(D_zV) = D_z^aV`).
-/

theorem DzIter_succ_apply_fts (n : ℕ) : ∀ (f : ℝ → ℝ → ℝ),
    Work.Spaces.DzIter n (Work.Spaces.Dz f) = Work.Spaces.DzIter (n + 1) f := by
  intro f
  induction n with
  | zero => rfl
  | succ m ih =>
      rw [Work.Spaces.DzIter_succ (n := m) (f := Work.Spaces.Dz f), ih,
        Work.Spaces.DzIter_succ (n := m + 1) (f := f)]

/-- **The pointwise identity `z² ∂_z²V = D_z²V - D_zV`** on the box `U`.

(`D_z²V = D_z(D_zV) = z ∂_z(z ∂_zV) = z ∂_zV + z²∂_z²V = D_zV + z²∂_z²V`.)  This is the
identity which turns the `z²pzIter 2 V`-slots into the `D_z`-slots of `V`. -/
theorem zsq_pzIter_two_eq {V : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd V)
    {p : ℝ × ℝ} (hp : p ∈ Work.Spaces.U) :
    p.1 ^ 2 * Work.Spaces.pzIter 2 V p.1 p.2
      = Work.Spaces.Dz (Work.Spaces.Dz V) p.1 p.2 - Work.Spaces.Dz V p.1 p.2 := by
  have h1 : ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.pz V)) Work.Spaces.U :=
    Work.Spaces.contDiffOn_uncurry_pz Work.Spaces.isOpen_U hsm
  have hd2 : DifferentiableAt ℝ (fun z' => deriv (fun z'' => V z'' p.2) z') p.1 := by
    have h := Work.Spaces.differentiableAt_curry_left
      ((h1.differentiableOn (n := ⊤) (by simp)).differentiableAt
        (Work.Spaces.isOpen_U.mem_nhds hp))
    simpa only [Work.Spaces.pz, Function.uncurry] using h
  have hprod : deriv (fun z' => z' * deriv (fun z'' => V z'' p.2) z') p.1
      = deriv (fun z'' => V z'' p.2) p.1
        + p.1 * deriv (fun z' => deriv (fun z'' => V z'' p.2) z') p.1 := by
    have h := deriv_mul (c := id) (d := fun z' => deriv (fun z'' => V z'' p.2) z')
      (x := p.1) differentiableAt_id hd2
    rw [show (id * fun z' => deriv (fun z'' => V z'' p.2) z')
        = (fun z' => z' * deriv (fun z'' => V z'' p.2) z') from rfl] at h
    simpa using h
  simp only [Work.Spaces.Dz, Work.Spaces.pz, Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero]
  rw [hprod]
  ring

/-- The uncurried `D_z`-iterates of a function smooth on the box are smooth on the box. -/
theorem contDiffOn_uncurry_DzIter {V : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd V) (n : ℕ) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.DzIter n V)) Work.Spaces.U := by
  induction n with
  | zero =>
      simpa only [Work.Spaces.SmoothNbhd, Work.Spaces.U, Work.Spaces.DzIter_zero] using hsm
  | succ m ih =>
      have hpz := Work.Spaces.contDiffOn_uncurry_pz Work.Spaces.isOpen_U ih
      have hfun : Function.uncurry (Work.Spaces.DzIter (m + 1) V)
          = (fun p : ℝ × ℝ => p.1) * Function.uncurry (Work.Spaces.pz (Work.Spaces.DzIter m V)) := by
        funext p
        simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz, Function.uncurry,
          Pi.mul_apply]
      rw [hfun]
      exact contDiffOn_fst.mul hpz

/-- `D_z` of a function smooth on the box is differentiable at every point of the open
quadrant, slicewise. -/
theorem DzIter_differentiableAt_slice {V : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd V)
    (n : ℕ) {p : ℝ × ℝ} (hp : p ∈ Work.Spaces.quadU) :
    DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n V z' p.2) p.1 := by
  have hmem : p ∈ Work.Spaces.U := by
    have h1 : -1 < p.1 := hp.1
    have h2 : p.2 ∈ Set.Ioo (-1) (Real.pi / 2 + 1) :=
      ⟨by linarith [hp.2.1], by linarith [hp.2.2, Real.pi_pos]⟩
    exact ⟨h1, h2⟩
  have h := (contDiffOn_uncurry_DzIter hsm n).differentiableOn (by simp)
  exact Work.Spaces.differentiableAt_curry_left
    (h.differentiableAt (Work.Spaces.isOpen_U.mem_nhds hmem))

/-- `D_z` respects pointwise equality on the open quadrant (in the uncurried form). -/
theorem Dz_uncurry_eqOn_quadU {f g : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) Work.Spaces.quadU) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dz f)) (Function.uncurry (Work.Spaces.Dz g))
      Work.Spaces.quadU := by
  rintro ⟨z, θ⟩ hp
  have hs : Set.EqOn (fun z' => f z' θ) (fun z' => g z' θ) (Set.Ioi (-1)) := by
    intro z' hz'
    have hmem : ((z', θ) : ℝ × ℝ) ∈ Work.Spaces.quadU := ⟨hz', hp.2⟩
    simpa only [Function.uncurry] using h hmem
  simp only [Work.Spaces.Dz, Work.Spaces.pz, Function.uncurry]
  rw [hs.deriv isOpen_Ioi hp.1]

/-- **The iterated Euler identity** on the open quadrant (uncurried form):
`D_z^m(z²∂_z²V) = D_z^{m+2}V - D_z^{m+1}V`. -/
theorem DzIter_zsq_pzIter_two_uncurry_eqOn {V : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothNbhd V) (m : ℕ) :
    Set.EqOn
      (Function.uncurry (Work.Spaces.DzIter m (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ)))
      (Function.uncurry (fun z θ =>
        Work.Spaces.DzIter (m + 2) V z θ - Work.Spaces.DzIter (m + 1) V z θ))
      Work.Spaces.quadU := by
  induction m with
  | zero =>
      rintro ⟨z, θ⟩ hp
      exact zsq_pzIter_two_eq hsm ⟨hp.1, ⟨by linarith [hp.2.1], by linarith [hp.2.2, Real.pi_pos]⟩⟩
  | succ m ih =>
      have h1 : Set.EqOn
          (Function.uncurry
            (Work.Spaces.DzIter (m + 1) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ)))
          (Function.uncurry (Work.Spaces.Dz (fun z θ =>
            Work.Spaces.DzIter (m + 2) V z θ - Work.Spaces.DzIter (m + 1) V z θ)))
          Work.Spaces.quadU := by
        have hc := Dz_uncurry_eqOn_quadU ih
        simpa only [Work.Spaces.DzIter_succ] using hc
      have h2 : Set.EqOn
          (Function.uncurry (Work.Spaces.Dz (fun z θ =>
            Work.Spaces.DzIter (m + 2) V z θ - Work.Spaces.DzIter (m + 1) V z θ)))
          (Function.uncurry (fun z θ =>
            Work.Spaces.DzIter (m + 3) V z θ - Work.Spaces.DzIter (m + 2) V z θ))
          Work.Spaces.quadU := by
        rintro ⟨z, θ⟩ hp
        have hd1 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter (m + 2) V z' θ) z :=
          DzIter_differentiableAt_slice hsm (m + 2) hp
        have hd2 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter (m + 1) V z' θ) z :=
          DzIter_differentiableAt_slice hsm (m + 1) hp
        simp only [Work.Spaces.Dz, Work.Spaces.pz, Function.uncurry]
        rw [show (fun z' => Work.Spaces.DzIter (m + 2) V z' θ
              - Work.Spaces.DzIter (m + 1) V z' θ)
            = (fun z' => Work.Spaces.DzIter (m + 2) V z' θ)
              - (fun z' => Work.Spaces.DzIter (m + 1) V z' θ) from rfl,
          deriv_sub hd1 hd2]
        simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
        ring
      exact h1.trans h2

/-- **The pointwise content of the `z²pzIter 2 V`-slot**: on the closed quadrant,
`(D_z^{k+2}V)²` is bounded by the corresponding `z²∂_z²V`-slot and the `D_zV`-slot,

  `(D_z^{k+2}V)² ≤ 2 (D_z^k(z²∂_z²V))² + 2 (D_z^{k+1}V)²`,

by the iterated Euler identity `D_z^k(z²∂_z²V) = D_z^{k+2}V - D_z^{k+1}V` (and `x² ≤
2(x-y)² + 2y²`).  Both sides are multiplied by the same weight `w/√sin(2θ)^η`. -/
theorem Y_zsqpz2_pointwise {V : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd V) (k : ℕ)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        * Work.Spaces.DzIter (k + 2) V z θ) ^ 2
      ≤ 2 * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
          * Work.Spaces.DzIter k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ) z θ) ^ 2
        + 2 * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
          * Work.Spaces.DzIter (k + 1) V z θ) ^ 2 := by
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ z from hz) with hz0 | hzpos
  · subst hz0
    simp [Work.Spaces.w]
  rcases eq_or_lt_of_le hθ.1 with hθ0 | hθpos
  · subst hθ0
    have h0 : (0:ℝ) ^ (Work.Spaces.eta / 2) = 0 :=
      Real.zero_rpow (by norm_num [Work.Spaces.eta])
    rw [show (2:ℝ) * 0 = 0 by ring, Real.sin_zero, h0, div_zero]
    norm_num
  rcases lt_or_eq_of_le hθ.2 with hθlt | hθtop
  · have hmem : (z, θ) ∈ Work.Spaces.quadU :=
      ⟨lt_of_lt_of_le (by norm_num : (-1:ℝ) < 0) (le_of_lt hzpos), hθpos, hθlt⟩
    have hid := DzIter_zsq_pzIter_two_uncurry_eqOn hsm k hmem
    simp only [Function.uncurry] at hid
    rw [hid]
    have hkey : (Work.Spaces.DzIter (k + 2) V z θ) ^ 2
        ≤ 2 * (Work.Spaces.DzIter (k + 2) V z θ - Work.Spaces.DzIter (k + 1) V z θ) ^ 2
          + 2 * (Work.Spaces.DzIter (k + 1) V z θ) ^ 2 := by
      nlinarith [sq_nonneg (Work.Spaces.DzIter (k + 2) V z θ
        - 2 * Work.Spaces.DzIter (k + 1) V z θ)]
    calc (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
          * Work.Spaces.DzIter (k + 2) V z θ) ^ 2
        = (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
          * (Work.Spaces.DzIter (k + 2) V z θ) ^ 2 := by ring
      _ ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
          * (2 * (Work.Spaces.DzIter (k + 2) V z θ - Work.Spaces.DzIter (k + 1) V z θ) ^ 2
            + 2 * (Work.Spaces.DzIter (k + 1) V z θ) ^ 2) :=
          mul_le_mul_of_nonneg_left hkey (sq_nonneg _)
      _ = 2 * ((Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
            * (Work.Spaces.DzIter (k + 2) V z θ - Work.Spaces.DzIter (k + 1) V z θ)) ^ 2
          + 2 * ((Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
            * Work.Spaces.DzIter (k + 1) V z θ) ^ 2 := by ring
  · subst hθtop
    have h0 : (0:ℝ) ^ (Work.Spaces.eta / 2) = 0 :=
      Real.zero_rpow (by norm_num [Work.Spaces.eta])
    rw [show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi, h0, div_zero]
    norm_num

/-- **The integrated content of the `z²pzIter 2 V`-slot**:

  `L2Sq (w·D_z^{k+2}V/√sin(2θ)^η) ≤ 2 HkSq α k (z²∂_z²V) + 2 HkSq α k (D_zV)`,

from the pointwise slot domination `Y_zsqpz2_pointwise` together with the fact that the two
smaller slots are summands of the corresponding `HkIntegrand`s. -/
theorem Y_le_HkSq_zsqpz2 (α : ℝ) (k : ℕ) {V : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothNbhd V)
    (hmemQ : Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ))
    (hmemD : Work.Spaces.HkMem α k (Work.Spaces.Dz V)) :
    Work.Spaces.L2Sq (fun z θ => Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        * Work.Spaces.DzIter (k + 2) V z θ)
      ≤ 2 * Work.Spaces.HkSq α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ)
        + 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V) := by
  set Q : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ with hQdef
  -- the two smaller slots are summands of the corresponding `HkIntegrand`s
  have hslotQ : ∀ z θ, (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
      * Work.Spaces.DzIter k Q z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k Q z θ := by
    intro z θ
    have h := Work.Spaces.sq_le_HkIntegrand_z α k Q z θ k (le_refl k)
    have hcomm : Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        * Work.Spaces.DzIter k Q z θ
        = Work.Spaces.DzIter k Q z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) :=
      mul_comm _ _
    rw [hcomm]
    exact h
  have hshift : Work.Spaces.DzIter (k + 1) V = Work.Spaces.DzIter k (Work.Spaces.Dz V) :=
    (DzIter_succ_apply_fts k V).symm
  have hslotD : ∀ z θ, (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
      * Work.Spaces.DzIter (k + 1) V z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α k (Work.Spaces.Dz V) z θ := by
    intro z θ
    have h := Work.Spaces.sq_le_HkIntegrand_z α k (Work.Spaces.Dz V) z θ k (le_refl k)
    rw [hshift]
    have hcomm : Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        * Work.Spaces.DzIter k (Work.Spaces.Dz V) z θ
        = Work.Spaces.DzIter k (Work.Spaces.Dz V) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) :=
      mul_comm _ _
    rw [hcomm]
    exact h
  -- the pointwise bound on the top slot
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        * Work.Spaces.DzIter (k + 2) V z θ) ^ 2
      ≤ 2 * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
          * Work.Spaces.DzIter k Q z θ) ^ 2
        + 2 * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
          * Work.Spaces.DzIter (k + 1) V z θ) ^ 2 := by
    intro z hz θ hθ
    exact Y_zsqpz2_pointwise hsm k hz hθ
  -- the inner (`θ`-) comparison
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
          * Work.Spaces.DzIter (k + 2) V z θ) ^ 2)
      ≤ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k Q z θ)
        + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.Dz V) z θ) := by
    intro z hz
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun θ => (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
          * Work.Spaces.DzIter (k + 2) V z θ) ^ 2)
      (g := fun θ => 2 * Work.Spaces.HkIntegrand α k Q z θ
        + 2 * Work.Spaces.HkIntegrand α k (Work.Spaces.Dz V) z θ)
      (Eventually.of_forall fun θ => sq_nonneg _)
      (((hmemQ.1 z hz).const_mul 2).add ((hmemD.1 z hz).const_mul 2))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ =>
        le_trans (hpt z hz θ hθ) (add_le_add
          (mul_le_mul_of_nonneg_left (hslotQ z θ) (by norm_num))
          (mul_le_mul_of_nonneg_left (hslotD z θ) (by norm_num))))
    refine hmono.trans_eq ?_
    rw [MeasureTheory.integral_add ((hmemQ.1 z hz).const_mul 2) ((hmemD.1 z hz).const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  -- the outer comparison
  rw [Work.Spaces.L2Sq, Work.Spaces.HkSq, Work.Spaces.HkSq]
  refine le_trans (MeasureTheory.integral_mono_of_nonneg
    (μ := volume.restrict Work.Spaces.Iz)
    (f := fun z => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z
        / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        * Work.Spaces.DzIter (k + 2) V z θ) ^ 2)
    (g := fun z => 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k Q z θ)
      + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.Dz V) z θ))
    (Eventually.of_forall fun z => integral_nonneg fun θ => sq_nonneg _)
    ((hmemQ.2.const_mul 2).add (hmemD.2.const_mul 2))
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hinner z hz)) ?_
  rw [MeasureTheory.integral_add (hmemQ.2.const_mul 2) (hmemD.2.const_mul 2),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

/-- **The first angular boundary product vanishes at `0⁺`.**  For `g` of class `C²` on a
neighbourhood of `0` with `g 0 = 0`,

  `sin(2θ)^{-η} · g θ · g' θ → 0` as `θ → 0⁺`.

Indeed `sin(2θ)^{-η} g g' = (sin 2θ)^{1-η} · (g/sin 2θ) · g'` with
`(sin 2θ)^{1-η} → 0` (`1-η > 0`), `g θ/sin(2θ) → g' 0/2` and `g' → g' 0`. -/
theorem sigma_slope_tendsto_zero {g : ℝ → ℝ} (hg : ContDiffOn ℝ 2 g (Set.Ioi (-1)))
    (h0 : g 0 = 0) :
    Filter.Tendsto (fun θ : ℝ =>
        (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * g θ * deriv g θ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hg1 : HasDerivAt g (deriv g 0) 0 :=
    ((hg.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds (by norm_num : (0:ℝ) ∈ Set.Ioi (-1)))).hasDerivAt
  -- eventual facts
  have hlt : ∀ᶠ θ : ℝ in nhdsWithin (0:ℝ) (Set.Ioi 0), θ < Real.pi / 2 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by positivity : (0:ℝ) < Real.pi / 2))
  have hsinpos : ∀ᶠ θ : ℝ in nhdsWithin (0:ℝ) (Set.Ioi 0), 0 < Real.sin (2 * θ) := by
    filter_upwards [self_mem_nhdsWithin, hlt] with θ hθ hθlt
    have hθ0 : (0:ℝ) < θ := hθ
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hsne : ∀ᶠ θ : ℝ in nhdsWithin (0:ℝ) (Set.Ioi 0), Real.sin (2 * θ) ≠ 0 :=
    hsinpos.mono fun _ h => ne_of_gt h
  -- `θ⁻¹ g θ → g' 0`
  have hslope0 : Filter.Tendsto (fun θ : ℝ => θ⁻¹ * (g θ - g 0))
      (nhdsWithin 0 {(0:ℝ)}ᶜ) (nhds (deriv g 0)) := by
    simpa using hg1.tendsto_slope_zero
  have hslope : Filter.Tendsto (fun θ : ℝ => θ⁻¹ * g θ) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (deriv g 0)) := by
    have h := hslope0.mono_left (nhdsWithin_mono 0 fun x hx => ne_of_gt hx)
    refine h.congr' ?_
    filter_upwards with θ
    rw [h0]; ring
  -- `sin(2θ)/(2θ) → 1`
  have hsin0 : Filter.Tendsto (fun y : ℝ => y⁻¹ * (Real.sin y - Real.sin 0))
      (nhdsWithin 0 {(0:ℝ)}ᶜ) (nhds 1) := by
    simpa using (Real.hasDerivAt_sin 0).tendsto_slope_zero
  have h2th : Filter.Tendsto (fun θ : ℝ => (2:ℝ) * θ) (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin 0 {(0:ℝ)}ᶜ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h : Filter.Tendsto (fun θ : ℝ => (2:ℝ) * θ) (nhds (0:ℝ)) (nhds (2 * 0)) :=
        tendsto_const_nhds.mul tendsto_id
      simpa using h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with θ hθ
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hc
      rcases mul_eq_zero.mp hc with h | h
      · exact absurd h (by norm_num)
      · exact absurd h (ne_of_gt (show (0:ℝ) < θ from hθ))
  have hsin2 : Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ) / (2 * θ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have h := hsin0.comp h2th
    refine h.congr' ?_
    filter_upwards with θ
    simp only [Function.comp_apply, sub_zero, Real.sin_zero, inv_mul_eq_div]
  -- `θ/sin(2θ) → 1/2`
  have hrecip : Filter.Tendsto (fun θ : ℝ => θ / Real.sin (2 * θ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1/2 : ℝ)) := by
    have h2 : Filter.Tendsto (fun θ : ℝ => (Real.sin (2 * θ) / (2 * θ))⁻¹)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds ((1:ℝ)⁻¹)) := hsin2.inv₀ (by norm_num)
    have h3 : Filter.Tendsto (fun θ : ℝ => (1/2 : ℝ) * (Real.sin (2 * θ) / (2 * θ))⁻¹)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (1/2 : ℝ)) := by
      have h := h2.const_mul (1/2 : ℝ)
      simpa using h
    refine h3.congr' ?_
    filter_upwards [hsne, self_mem_nhdsWithin] with θ hs hθ
    have hθ0 : θ ≠ 0 := ne_of_gt (show (0:ℝ) < θ from hθ)
    field_simp
  -- `g θ/sin(2θ) → g' 0/2`
  have hquot : Filter.Tendsto (fun θ : ℝ => g θ / Real.sin (2 * θ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (deriv g 0 / 2)) := by
    have h := hslope.mul hrecip
    have h' : Filter.Tendsto (fun θ : ℝ => g θ / Real.sin (2 * θ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (deriv g 0 * (1/2))) := by
      refine h.congr' ?_
      filter_upwards [hsne, self_mem_nhdsWithin] with θ hs hθ
      have hθ0 : θ ≠ 0 := ne_of_gt (show (0:ℝ) < θ from hθ)
      field_simp
    simpa [div_eq_mul_inv] using h'
  -- `(sin 2θ)^{1-η} → 0`
  have hsige : Filter.Tendsto (fun θ : ℝ => (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hsinT : Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (nhdsWithin 0 (Set.Ioi 0))
        (nhdsWithin 0 (Set.Ioi 0)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, hsinpos⟩
      have hcont : Continuous (fun θ : ℝ => Real.sin (2 * θ)) :=
        Real.continuous_sin.comp (continuous_const.mul continuous_id)
      have h : Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (nhds (0:ℝ))
          (nhds (Real.sin (2 * 0))) := hcont.continuousAt
      simpa using h.mono_left nhdsWithin_le_nhds
    have hlog : Filter.Tendsto (fun θ : ℝ => Real.log (Real.sin (2 * θ)))
        (nhdsWithin 0 (Set.Ioi 0)) atBot := Real.tendsto_log_nhdsGT_zero.comp hsinT
    have hmul : Filter.Tendsto (fun θ : ℝ =>
        (1 - Work.Spaces.eta) * Real.log (Real.sin (2 * θ)))
        (nhdsWithin 0 (Set.Ioi 0)) atBot :=
      hlog.const_mul_atBot (by rw [Work.Spaces.eta]; norm_num)
    have hexp : Filter.Tendsto (fun θ : ℝ =>
        Real.exp ((1 - Work.Spaces.eta) * Real.log (Real.sin (2 * θ))))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := Real.tendsto_exp_atBot.comp hmul
    refine hexp.congr' ?_
    filter_upwards [hsinpos] with θ hθ
    rw [Real.rpow_def_of_pos hθ, mul_comm]
  -- `deriv g → g' 0`
  have hd : Filter.Tendsto (deriv g) (nhdsWithin 0 (Set.Ioi 0)) (nhds (deriv g 0)) := by
    have hsm : ContDiffOn ℝ 1 (deriv g) (Set.Ioi (-1)) :=
      hg.deriv_of_isOpen isOpen_Ioi (m := 1) (by norm_num)
    exact (hsm.continuousOn.continuousAt (isOpen_Ioi.mem_nhds (by norm_num))).tendsto.mono_left
      nhdsWithin_le_nhds
  -- combine
  have hprod : Filter.Tendsto (fun θ : ℝ =>
      (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta) * (g θ / Real.sin (2 * θ)) * deriv g θ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h := (hsige.mul hquot).mul hd
    simpa using h
  refine hprod.congr' ?_
  filter_upwards [hsne, hsinpos, self_mem_nhdsWithin] with θ hs hθ hθmem
  have hθ0 : θ ≠ 0 := ne_of_gt (show (0:ℝ) < θ from hθmem)
  have hrpow : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      = (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta) / Real.sin (2 * θ) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hθ]
    congr 1
    ring
  rw [hrpow]
  field_simp

/-- **The `δ → 0` limit of the sub-interval integrals.**  For any function `f` that is
interval-integrable on every interval (in particular on `Iθ`),

  `∫_δ^{π/2 - δ} f → ∫_{Iθ} f`  as `δ → 0⁺`.

Proof: `∫_δ^{π/2-δ}f = ∫_0^{π/2-δ}f - ∫_0^δ f` (adjacent intervals) and both primitives are
continuous (`intervalIntegral.continuous_primitive`). -/
theorem intervalIntegral_tendsto_Icc {f : ℝ → ℝ}
    (hf : ∀ a b : ℝ, IntervalIntegrable f volume a b) :
    Filter.Tendsto (fun δ : ℝ => ∫ θ in δ..(Real.pi / 2 - δ), f θ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ θ in Work.Spaces.Iθ, f θ)) := by
  have hcont : Continuous (fun t : ℝ => ∫ θ in (0:ℝ)..t, f θ) :=
    intervalIntegral.continuous_primitive hf 0
  have hI : (∫ θ in Work.Spaces.Iθ, f θ) = ∫ θ in (0:ℝ)..(Real.pi / 2), f θ := by
    rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ Real.pi / 2)]
  rw [hI]
  have htop : Filter.Tendsto (fun δ : ℝ => Real.pi / 2 - δ) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Real.pi / 2)) := by
    have h : Filter.Tendsto (fun δ : ℝ => Real.pi / 2 - δ) (nhds (0:ℝ))
        (nhds (Real.pi / 2 - 0)) := tendsto_const_nhds.sub tendsto_id
    simpa using h.mono_left nhdsWithin_le_nhds
  have hzer : Filter.Tendsto (fun δ : ℝ => δ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hlim : Filter.Tendsto (fun δ : ℝ =>
      (∫ θ in (0:ℝ)..(Real.pi / 2 - δ), f θ) - ∫ θ in (0:ℝ)..δ, f θ)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((∫ θ in (0:ℝ)..(Real.pi / 2), f θ) - ∫ θ in (0:ℝ)..(0:ℝ), f θ)) :=
    (hcont.continuousAt.tendsto.comp htop).sub (hcont.continuousAt.tendsto.comp hzer)
  refine Tendsto.congr' ?_ (by simpa using hlim)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have h1 : (∫ θ in (0:ℝ)..δ, f θ) + (∫ θ in δ..(Real.pi / 2 - δ), f θ)
      = ∫ θ in (0:ℝ)..(Real.pi / 2 - δ), f θ :=
    intervalIntegral.integral_add_adjacent_intervals (hf 0 δ) (hf δ (Real.pi / 2 - δ))
  linarith

/-- **The angular integration by parts, combined.**  For `g` of class `C²` on `(0,π/2)` and
`0 < δ < π/4`, the two sorry-free sub-interval identities `RPFresh.AngIBP.ang_ibp_sub` and
`RPFresh.AngIBP.ang_T_id_sub` give

  `∫_δ^{π/2-δ} σ (g')² = [σ g g']_δ^{π/2-δ} + 2η ([σ cot(2θ) g²/2]_δ^{π/2-δ}
      + ∫_δ^{π/2-δ} σ (η cot²(2θ) + sin(2θ)^{-2}) g²) - ∫_δ^{π/2-δ} σ g g''`,

where `σ = sg = sin(2θ)^{-η}`. -/
theorem ang_ibp_combined {g : ℝ → ℝ} (hg : ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)))
    {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ < Real.pi / 4) :
    (∫ θ in δ..(Real.pi / 2 - δ), sg θ * (deriv g θ) ^ 2)
      = (sg (Real.pi / 2 - δ) * g (Real.pi / 2 - δ) * deriv g (Real.pi / 2 - δ)
          - sg δ * g δ * deriv g δ)
        + 2 * Work.Spaces.eta
            * ((sg (Real.pi / 2 - δ) * Real.cot (2 * (Real.pi / 2 - δ))
                  * (g (Real.pi / 2 - δ)) ^ 2 - sg δ * Real.cot (2 * δ) * (g δ) ^ 2) / 2
              + ∫ θ in δ..(Real.pi / 2 - δ), sg θ
                  * (Work.Spaces.eta * (Real.cot (2 * θ)) ^ 2
                    + (Real.sin (2 * θ)) ^ (-(2 : ℝ))) * (g θ) ^ 2)
        - ∫ θ in δ..(Real.pi / 2 - δ), sg θ * g θ * deriv (deriv g) θ := by
  rw [Work.FTS.EllipticEst.RPFresh.ang_ibp_sub (g := g) hg hδ hδ4,
    Work.FTS.EllipticEst.RPFresh.ang_T_id_sub (g := g) hg hδ hδ4]

/-- **The radial integration by parts with boundary terms.**  For `0 < a ≤ b` and `φ, ψ` of
class `C¹` on `(0,∞)`,

  `∫_a^b w² φ (z ψ') = [z w² φ ψ]_a^b - ∫_a^b (w²·((z-3)/(1+z))·φ + z w² · φ') ψ`. -/
theorem radial_ibp_bt {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {φ ψ : ℝ → ℝ}
    (hφ : ContDiffOn ℝ 1 φ (Set.Ioi 0)) (hψ : ContDiffOn ℝ 1 ψ (Set.Ioi 0)) :
    (∫ z in a..b, (Work.Spaces.w z) ^ 2 * φ z * (z * deriv ψ z))
      = (b * (Work.Spaces.w b) ^ 2 * φ b * ψ b
          - a * (Work.Spaces.w a) ^ 2 * φ a * ψ a)
        - ∫ z in a..b, ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)) * φ z
            + (z * (Work.Spaces.w z) ^ 2) * deriv φ z) * ψ z := by
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun x hx => by
    simp only [Set.mem_Ioi]; linarith [hx.1, ha]
  have hphid : ∀ z, 0 < z → HasDerivAt φ (deriv φ z) z := fun z hz =>
    ((hφ.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hz)).hasDerivAt
  have hpsid : ∀ z, 0 < z → HasDerivAt ψ (deriv ψ z) z := fun z hz =>
    ((hψ.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hz)).hasDerivAt
  have hwu : ∀ z, 0 < z → HasDerivAt (fun y : ℝ => y * (Work.Spaces.w y) ^ 2)
      ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z))) z := by
    intro z hz
    have hz0 : z ≠ 0 := ne_of_gt hz
    have hdiff : DifferentiableAt ℝ (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) z := by
      have hw : DifferentiableAt ℝ (fun y : ℝ => Work.Spaces.w y) z := by
        have h1 : DifferentiableAt ℝ (fun y : ℝ => (1 + y) ^ 2 / y ^ 2) z := by
          apply DifferentiableAt.div <;> try fun_prop
          exact pow_ne_zero 2 hz0
        simpa only [Work.Spaces.w] using h1
      exact differentiableAt_id.mul (hw.pow 2)
    have hdv : deriv (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) z
        = (Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)) := by
      rw [Work.FTS.EllipticEst.weight_algebra_fts.2.2.2.1 z hz0, Work.Spaces.w]
      field_simp
    rw [← hdv]; exact hdiff.hasDerivAt
  have hwcont : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Icc a b) := by
    have h1 : ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi 0) := by
      apply ContinuousOn.div <;> try fun_prop
      intro z hz; exact pow_ne_zero 2 (ne_of_gt hz)
    simpa only [Work.Spaces.w] using h1.mono hsub
  have hdφcont : ContinuousOn (deriv φ) (Set.Icc a b) :=
    (hφ.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).mono hsub
  have hdψcont : ContinuousOn (deriv ψ) (Set.Icc a b) :=
    (hψ.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).mono hsub
  have hφcont : ContinuousOn φ (Set.Icc a b) := hφ.continuousOn.mono hsub
  have hu'cont : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)) * φ z
      + (z * (Work.Spaces.w z) ^ 2) * deriv φ z) (Set.Icc a b) := by
    have hdiv : ContinuousOn (fun z : ℝ => (z - 3) / (1 + z)) (Set.Icc a b) := by
      apply ContinuousOn.div <;> try fun_prop
      intro z hz
      exact ne_of_gt (by linarith [hz.1, ha] : (0 : ℝ) < 1 + z)
    exact (((hwcont.pow 2).mul hdiv).mul hφcont).add
      ((continuousOn_id.mul (hwcont.pow 2)).mul hdφcont)
  have hu'int : IntervalIntegrable (fun z : ℝ => (Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)) * φ z
      + (z * (Work.Spaces.w z) ^ 2) * deriv φ z) volume a b :=
    hu'cont.intervalIntegrable_of_Icc hab
  have hψ'int : IntervalIntegrable (deriv ψ) volume a b :=
    hdψcont.intervalIntegrable_of_Icc hab
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := fun y : ℝ => y * (Work.Spaces.w y) ^ 2 * φ y) (v := ψ)
      (u' := fun z : ℝ => (Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)) * φ z
        + (z * (Work.Spaces.w z) ^ 2) * deriv φ z)
      (v' := deriv ψ)
      (fun x hx => by
        have hxab : a ≤ x ∧ x ≤ b := by
          rw [Set.uIcc_of_le hab] at hx; exact hx
        exact (hwu x (by linarith [hxab.1, ha])).mul (hphid x (by linarith [hxab.1, ha])))
      (fun x hx => by
        have hxab : a ≤ x ∧ x ≤ b := by
          rw [Set.uIcc_of_le hab] at hx; exact hx
        exact hpsid x (by linarith [hxab.1, ha]))
      hu'int hψ'int
  rw [show (∫ z in a..b, (Work.Spaces.w z) ^ 2 * φ z * (z * deriv ψ z))
      = ∫ z in a..b, (z * (Work.Spaces.w z) ^ 2 * φ z) * deriv ψ z by
    apply intervalIntegral.integral_congr
    intro z _; ring]
  rw [hIBP]

/-- `Y(a,2)` is a summand of the first family of `HkSq α k (pthIter 2 V)`. -/
theorem Y_le_HkSq_pthIter2 (α : ℝ) (k : ℕ) {V : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 V)) {a : ℕ} (ha : a ≤ k) :
    Work.Spaces.L2Sq (fun z θ => Work.Spaces.w z
        / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        * Work.Spaces.DzIter a (Work.Spaces.pthIter 2 V) z θ)
      ≤ Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V) := by
  have h := Work.Spaces.L2Sq_DzIter_le_HkSq α k (Work.Spaces.pthIter 2 V) hmem a ha
  have hfun : (fun z θ => Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        * Work.Spaces.DzIter a (Work.Spaces.pthIter 2 V) z θ)
      = (fun z θ => Work.Spaces.DzIter a (Work.Spaces.pthIter 2 V) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) := by
    funext z θ; ring
  rw [hfun]; exact h

/-- `Y(a,0)` is a summand of the first family of `HkSq α k (Dz V)`. -/
theorem Y_le_HkSq_Dz (α : ℝ) (k : ℕ) {V : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α k (Work.Spaces.Dz V)) {a : ℕ} (ha : 1 ≤ a) (hak : a ≤ k + 1) :
    Work.Spaces.L2Sq (fun z θ => Work.Spaces.w z
        / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        * Work.Spaces.DzIter a V z θ)
      ≤ Work.Spaces.HkSq α k (Work.Spaces.Dz V) := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  have hb : b ≤ k := by omega
  have h := Work.Spaces.L2Sq_DzIter_le_HkSq α k (Work.Spaces.Dz V) hmem b hb
  have hshift : Work.Spaces.DzIter b (Work.Spaces.Dz V) = Work.Spaces.DzIter (b + 1) V :=
    DzIter_succ_apply_fts b V
  have hfun : (fun z θ => Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        * Work.Spaces.DzIter (b + 1) V z θ)
      = (fun z θ => Work.Spaces.DzIter b (Work.Spaces.Dz V) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) := by
    funext z θ
    rw [hshift]; ring
  rw [hfun]; exact h

/-! ## The `θ`-slice honesty of the two families, and the unconditional decomposition

`RPFresh.LHSDecomp` proves the pointwise decomposition of the `ℋ^k`-integrand of `α·D_z∂_θV`
into the two families `lhsZ` (radial) and `lhsM` (mixed), together with the integral estimate

`HkSq α k (α·D_z∂_θV) ≤ C (α² ∑_r ∫_z mixIntS(D_z^rV) + α² ∑_{i,j} ∫_z mixedIntS α i j V)`

**provided** the majorant

`T z = α² ∑_r mixIntS(D_z^rV) z + α² ∑_{i,j} [1 ≤ i ∧ i+j ≤ k] mixedIntS α i j V z`

is integrable in `z`.  That hypothesis is not a consequence of the target's hypotheses — the
Bochner integral of a non-integrable function is `0`, so `HkSq` can hide a finite contribution —
but for the data of the target the two families do have honest `θ`-slices for **every** `z ∈ Iz`:

* the radial family: `θ ↦ D_z∂_θ(D_z^rV) z θ` is the `θ`-slice of a function which is `C^∞` on
  an open neighbourhood of the closed quadrant, hence bounded on the compact `Iθ`, while
  `thEta θ = sin(2θ)^{-η}` is integrable on `Iθ` (`RPFresh.slice_z_integrable`);
* the mixed family: `mixed j i f` with `i ≥ 1` carries one factor `sin(2θ)` for each `D_θ`
  (since `D_θ = sin(2θ)∂_θ`), which compensates the singularity of `thGam α θ = sin(2θ)^{-γ}`
  at `θ = 0, π/2` (`RPFresh.slice_mixed_integrable`).

Hence `θ ↦ HkIntegrand α k (α·D_z∂_θV) z θ` integrates to exactly `T z`, and `HkSq` of the
left-hand side is the honest integral of `T`; the estimate follows in the integrable case from
`LHSDecomp`, and in the non-integrable case both sides are `0 ≤ ·`. -/

theorem thetaIntegral_eq_majorant {V : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd V)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) :
    ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
          (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ)
        = α ^ 2 * (∑ r ∈ Finset.range (k + 1),
              Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
          + α ^ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              if 1 ≤ i ∧ i + j ≤ k then
                Work.EllipticEst.Core.mixedIntS α i j V z
              else 0) := by
  have hso : Work.FTS.EllipticEst.SmoothOpen V := by
    have h' : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (Function.uncurry V)
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)) := hsm
    show ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry V)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))
    refine (h'.of_le le_top).mono (Set.prod_mono ?_ ?_)
    · exact Set.Ioi_subset_Ioi (by norm_num)
    · exact Set.Ioo_subset_Ioo (by norm_num) (by linarith [Real.pi_pos])
  intro z hz
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k
          (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ
        = α ^ 2 * ((∑ r ∈ Finset.range (k + 1), lhsZ V r z θ)
            + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                lhsM α k V i j z θ)) :=
    fun θ hθ => HkIntegrand_alpha_Dz_pth hso hα z hz θ hθ
  have hZint : ∀ r : ℕ,
      MeasureTheory.IntegrableOn (fun θ : ℝ => lhsZ V r z θ) Work.Spaces.Iθ := by
    intro r
    have h := (slice_z_integrable hsm r z hz).const_mul ((Work.Spaces.w z) ^ 2)
    show MeasureTheory.Integrable (fun θ : ℝ => lhsZ V r z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)
    rw [show (fun θ : ℝ => lhsZ V r z θ) = fun θ : ℝ => (Work.Spaces.w z) ^ 2
        * ((Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) from rfl]
    exact h
  have hMint : ∀ i j : ℕ,
      MeasureTheory.IntegrableOn (fun θ : ℝ => lhsM α k V i j z θ) Work.Spaces.Iθ := by
    intro i j
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · have h := (slice_mixed_integrable (Work.Spaces.SmoothNbhd.pth hsm) α hα hα1
        (j + 1) i hc.1 z hz).const_mul ((Work.Spaces.w z) ^ 2)
      show MeasureTheory.Integrable (fun θ : ℝ => lhsM α k V i j z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      rw [show (fun θ : ℝ => lhsM α k V i j z θ) = fun θ : ℝ => (Work.Spaces.w z) ^ 2
          * ((Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
            * Work.FTS.EllipticEst.thGam α θ) from by
        funext θ; simp only [lhsM, if_pos hc]]
      exact h
    · have h0 : lhsM α k V i j z = fun _ : ℝ => (0 : ℝ) := by
        funext θ; simp only [lhsM, if_neg hc]
      rw [h0]
      exact MeasureTheory.integrableOn_zero
  have hFint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => ∑ r ∈ Finset.range (k + 1), lhsZ V r z θ) Work.Spaces.Iθ :=
    integrable_finsetSum _ (fun r _ => hZint r)
  have hHint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        lhsM α k V i j z θ) Work.Spaces.Iθ :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hMint i j))
  have hZsum : (∫ θ in Work.Spaces.Iθ,
        (∑ r ∈ Finset.range (k + 1), lhsZ V r z θ))
      = ∑ r ∈ Finset.range (k + 1),
          ∫ θ in Work.Spaces.Iθ, lhsZ V r z θ :=
    integral_finsetSum _ (fun r _ => hZint r)
  have hMsum : (∫ θ in Work.Spaces.Iθ,
        (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1), lhsM α k V i j z θ))
      = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          ∫ θ in Work.Spaces.Iθ, lhsM α k V i j z θ := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hMint i j))]
    exact Finset.sum_congr rfl (fun i _ => integral_finsetSum _ (fun j _ => hMint i j))
  have hZval : ∀ r : ℕ, (∫ θ in Work.Spaces.Iθ, lhsZ V r z θ)
      = Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z := by
    intro r
    simp only [lhsZ, Work.EllipticEst.Core.mixIntS]
    rw [MeasureTheory.integral_const_mul]
  have hMval : ∀ i j : ℕ, (∫ θ in Work.Spaces.Iθ, lhsM α k V i j z θ)
      = if 1 ≤ i ∧ i + j ≤ k then
          Work.EllipticEst.Core.mixedIntS α i j V z else 0 := by
    intro i j
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · simp only [lhsM, Work.EllipticEst.Core.mixedIntS, if_pos hc]
      rw [MeasureTheory.integral_const_mul]
    · simp only [lhsM, if_neg hc, MeasureTheory.integral_zero]
  calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
        (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ)
      = ∫ θ in Work.Spaces.Iθ, α ^ 2 * ((∑ r ∈ Finset.range (k + 1), lhsZ V r z θ)
          + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              lhsM α k V i j z θ)) :=
        setIntegral_congr_fun measurableSet_Icc (fun θ hθ => hpt θ hθ)
    _ = α ^ 2 * (∫ θ in Work.Spaces.Iθ, ((∑ r ∈ Finset.range (k + 1), lhsZ V r z θ)
          + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              lhsM α k V i j z θ))) :=
        MeasureTheory.integral_const_mul _ _
    _ = α ^ 2 * ((∑ r ∈ Finset.range (k + 1),
            ∫ θ in Work.Spaces.Iθ, lhsZ V r z θ)
          + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            ∫ θ in Work.Spaces.Iθ, lhsM α k V i j z θ)) := by
        rw [MeasureTheory.integral_add hFint hHint, hZsum, hMsum]
    _ = α ^ 2 * (∑ r ∈ Finset.range (k + 1),
            Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
          + α ^ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              if 1 ≤ i ∧ i + j ≤ k then
                Work.EllipticEst.Core.mixedIntS α i j V z else 0) := by
        rw [Finset.sum_congr rfl (fun r _ => hZval r),
          Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hMval i j))]
        ring

/-- **The decomposition without the integrability hypothesis.**  For `V` smooth on a
neighbourhood of the closed quadrant the estimate of `RPFresh.LHSDecomp` holds
unconditionally, because the two families have honest `θ`-slices for every `z ∈ Iz`. -/
theorem LHSDecompUncond (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (V : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → Work.Spaces.SmoothNbhd V →
      Work.Spaces.HkSq α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ)
        ≤ C * (α ^ 2 * (∑ r ∈ Finset.range (k + 1),
                  ∫ z in Work.Spaces.Iz,
                    Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
            + α ^ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k then
                  ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixedIntS α i j V z
                else 0)) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := LHSDecomp k
  refine ⟨1 + C₀, by linarith, ?_⟩
  intro α V hα hα1 hsm
  have hso : Work.FTS.EllipticEst.SmoothOpen V := by
    have h' : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (Function.uncurry V)
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)) := hsm
    show ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry V)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))
    refine (h'.of_le le_top).mono (Set.prod_mono ?_ ?_)
    · exact Set.Ioi_subset_Ioi (by norm_num)
    · exact Set.Ioo_subset_Ioo (by norm_num) (by linarith [Real.pi_pos])
  have hkey := thetaIntegral_eq_majorant hsm α hα hα1 k
  have hSq : Work.Spaces.HkSq α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ)
      = ∫ z in Work.Spaces.Iz,
          (α ^ 2 * (∑ r ∈ Finset.range (k + 1),
              Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
            + α ^ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k then
                  Work.EllipticEst.Core.mixedIntS α i j V z else 0)) := by
    rw [Work.Spaces.HkSq]
    exact setIntegral_congr_fun measurableSet_Iz (fun z hz => hkey z hz)
  have hRnonneg : 0 ≤ α ^ 2 * (∑ r ∈ Finset.range (k + 1),
        ∫ z in Work.Spaces.Iz,
          Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
      + α ^ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixedIntS α i j V z else 0) := by
    refine add_nonneg (mul_nonneg (sq_nonneg α) (Finset.sum_nonneg (fun r _ => ?_)))
      (mul_nonneg (sq_nonneg α) (Finset.sum_nonneg (fun i _ =>
        Finset.sum_nonneg (fun j _ => ?_))))
    · exact MeasureTheory.integral_nonneg (fun z => mixIntS_nonneg (Work.Spaces.DzIter r V) z)
    · by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · rw [if_pos hc]
        exact MeasureTheory.integral_nonneg (fun z => mixedIntS_nonneg α i j V z)
      · rw [if_neg hc]
  by_cases hint : MeasureTheory.IntegrableOn (fun z : ℝ =>
      α ^ 2 * (∑ r ∈ Finset.range (k + 1),
          Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
      + α ^ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            Work.EllipticEst.Core.mixedIntS α i j V z else 0)) Work.Spaces.Iz
  · have h := hC₀ α V hα hso hint
    refine le_trans h ?_
    exact mul_le_mul_of_nonneg_right (by linarith) hRnonneg
  · rw [hSq, MeasureTheory.integral_undef hint]
    exact mul_nonneg (by linarith) hRnonneg

/-- The open-quadrant smoothness of the Euler block `z²∂_z²V`. -/
private theorem smoothOpen_zsq_pzIter_two {V : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd V) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ) := by
  have hsmU : ContDiffOn ℝ ⊤ (Function.uncurry V) Work.Spaces.U := hsm
  have hpz : ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.pz V)) Work.Spaces.U :=
    Work.Spaces.contDiffOn_uncurry_pz Work.Spaces.isOpen_U hsmU
  have hpz2 : ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.pzIter 2 V)) Work.Spaces.U := by
    have h := Work.Spaces.contDiffOn_uncurry_pz Work.Spaces.isOpen_U hpz
    simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using h
  have hQsm : ContDiffOn ℝ ⊤
      (Function.uncurry (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ)) Work.Spaces.U := by
    rw [show Function.uncurry (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ)
        = (fun p : ℝ × ℝ => p.1 ^ 2) * Function.uncurry (Work.Spaces.pzIter 2 V) from rfl]
    exact (contDiffOn_fst.pow 2).mul hpz2
  refine (hQsm.of_le le_top).mono (Set.prod_mono ?_ ?_)
  · exact Set.Ioi_subset_Ioi (by norm_num)
  · exact Set.Ioo_subset_Ioo (by norm_num) (by linarith [Real.pi_pos])

/-- The open-quadrant smoothness of `D_zV`. -/
private theorem smoothOpen_Dz {V : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd V) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz V) := by
  have hsmU : ContDiffOn ℝ ⊤ (Function.uncurry V) Work.Spaces.U := hsm
  have hpz : ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.pz V)) Work.Spaces.U :=
    Work.Spaces.contDiffOn_uncurry_pz Work.Spaces.isOpen_U hsmU
  have hDsm : ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.Dz V)) Work.Spaces.U := by
    rw [show Function.uncurry (Work.Spaces.Dz V)
        = (fun p : ℝ × ℝ => p.1) * Function.uncurry (Work.Spaces.pz V) from rfl]
    exact contDiffOn_fst.mul hpz
  refine (hDsm.of_le le_top).mono (Set.prod_mono ?_ ?_)
  · exact Set.Ioi_subset_Ioi (by norm_num)
  · exact Set.Ioo_subset_Ioo (by norm_num) (by linarith [Real.pi_pos])

/-- **`ℋ^k`-membership of `D_z²V` from the Euler split** `D_z²V = z²∂_z²V + D_zV`. -/
theorem HkMem_DzIter_two {V : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd V) (α : ℝ) (hα : 0 < α)
    (k : ℕ)
    (hQ : Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ))
    (hD : Work.Spaces.HkMem α k (Work.Spaces.Dz V)) :
    Work.Spaces.HkMem α k (Work.Spaces.DzIter 2 V) := by
  have hadd := Work.FTS.EllipticEst.HkMem_add_smoothOpen α k hα
    (smoothOpen_zsq_pzIter_two hsm) (smoothOpen_Dz hsm) hQ hD
  refine Work.FTS.EllipticEst.RPFresh.HkMem_of_agreeOnQ ?_ hadd
  intro z θ hz hθ hlt
  have hmem : (z, θ) ∈ Work.Spaces.U :=
    Work.Spaces.mem_U_of_dom hz.le ⟨hθ.le, hlt.le⟩
  have he := zsq_pzIter_two_eq hsm hmem
  show (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ) z θ + Work.Spaces.Dz V z θ
    = Work.Spaces.Dz (Work.Spaces.Dz V) z θ
  linarith [he]

/-- **The Euler split for `HkSq`**: `HkSq α k (D_z²V) ≤ 2 HkSq α k (z²∂_z²V) + 2 HkSq α k (D_zV)`. -/
theorem HkSq_DzIter_two_le {V : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd V) (α : ℝ) (hα : 0 < α)
    (k : ℕ)
    (hQ : Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ))
    (hD : Work.Spaces.HkMem α k (Work.Spaces.Dz V)) :
    Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
      ≤ 2 * Work.Spaces.HkSq α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ)
        + 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V) := by
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k
          (fun z θ => (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ) z θ
            + Work.Spaces.Dz V z θ) z θ
        ≤ 2 * Work.Spaces.HkIntegrand α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ) z θ
          + 2 * Work.Spaces.HkIntegrand α k (Work.Spaces.Dz V) z θ :=
    fun z hz θ hθ => HkIntegrand_add_le_open α k (smoothOpen_zsq_pzIter_two hsm)
      (smoothOpen_Dz hsm) hz hθ
  have hsq := Work.FTS.EllipticEst.HkSq_add_le_of_pointwise α k hQ hD hpt
  have hcongr : Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
      = Work.Spaces.HkSq α k (fun z θ => (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ) z θ
          + Work.Spaces.Dz V z θ) := by
    refine Work.FTS.EllipticEst.HkSq_congr_open α k (fun z θ hz hθ hlt => ?_)
    have hmem : (z, θ) ∈ Work.Spaces.U :=
      Work.Spaces.mem_U_of_dom hz.le ⟨hθ.le, hlt.le⟩
    have he := zsq_pzIter_two_eq hsm hmem
    show Work.Spaces.Dz (Work.Spaces.Dz V) z θ
      = (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ) z θ + Work.Spaces.Dz V z θ
    linarith [he]
  rw [hcongr]
  exact hsq

/-! ## The target -/

theorem CoreInterpHk (k : ℕ) (hk : 2 ≤ k) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (V : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → Work.Spaces.SmoothNbhd V →
      Work.Spaces.VanishTheta V →
      Work.Spaces.HkMem α k V →
      Work.Spaces.HkMem α k (Work.Spaces.Dz V) →
      Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ) →
      Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 V) →
      Work.Spaces.HkNorm α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ)
        ≤ C * (α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ)
            + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 V)
            + α * Work.Spaces.HkNorm α k (Work.Spaces.Dz V)) := by
  obtain ⟨C₁, hC₁, hD₁⟩ := LHSDecompUncond k
  obtain ⟨C₂, hC₂, hI₀⟩ := I0FamilyBound k
  obtain ⟨C₃, hC₃, hMix⟩ := MixedFamilyAlpha1 k
  have hKpos : 0 < C₁ * (C₂ + 4 * C₃ + 1) := mul_pos hC₁ (by linarith)
  refine ⟨Real.sqrt (C₁ * (C₂ + 4 * C₃ + 1)), Real.sqrt_pos.mpr hKpos, ?_⟩
  intro α V hα hα1 hsm hvan hV hD hQ hP2
  have hso : Work.FTS.EllipticEst.SmoothOpen V := by
    have h' : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (Function.uncurry V)
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)) := hsm
    show ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry V)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))
    refine (h'.of_le le_top).mono (Set.prod_mono ?_ ?_)
    · exact Set.Ioi_subset_Ioi (by norm_num)
    · exact Set.Ioo_subset_Ioo (by norm_num) (by linarith [Real.pi_pos])
  have hDD : Work.Spaces.HkMem α k (Work.Spaces.DzIter 2 V) :=
    HkMem_DzIter_two hsm α hα k hQ hD
  have hsqDD : Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
      ≤ 2 * Work.Spaces.HkSq α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ)
        + 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V) :=
    HkSq_DzIter_two_le hsm α hα k hQ hD
  set P : ℝ := Work.Spaces.HkSq α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ) with hPdef
  set Qa : ℝ := Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V) with hQdef
  set Ra : ℝ := Work.Spaces.HkSq α k (Work.Spaces.Dz V) with hRdef
  set M : ℝ := α ^ 4 * P + Qa + α ^ 2 * Ra with hMdef
  set Xb : ℝ := α ^ 2 * (∑ r ∈ Finset.range (k + 1),
      ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z) with hXdef
  set Yb : ℝ := α ^ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      if 1 ≤ i ∧ i + j ≤ k then
        ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixedIntS α i j V z else 0) with hYdef
  have hP0 : 0 ≤ P := by rw [hPdef]; exact Work.Spaces.HkSq_nonneg α k _
  have hQ0 : 0 ≤ Qa := by rw [hQdef]; exact Work.Spaces.HkSq_nonneg α k _
  have hR0 : 0 ≤ Ra := by rw [hRdef]; exact Work.Spaces.HkSq_nonneg α k _
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    have h1 : 0 ≤ α ^ 4 * P := mul_nonneg (by positivity) hP0
    have h2 : 0 ≤ α ^ 2 * Ra := mul_nonneg (by positivity) hR0
    linarith
  have hα2le : α ^ 2 ≤ 1 := pow_le_one₀ hα.le hα1
  have hα4le : α ^ 4 ≤ α ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hα2le (sq_nonneg α)
    nlinarith [h]
  have hα4nn : (0 : ℝ) ≤ α ^ 4 := by positivity
  have h1 : Xb ≤ C₂ * M := by
    have h := hI₀ α V hα hα1 hsm hvan hV hD hQ hP2
    rw [← hXdef, ← hPdef, ← hQdef, ← hRdef, ← hMdef] at h
    exact h
  have h2 : Yb ≤ 4 * C₃ * M := by
    have h := hMix α V hα hα1 hso hvan.1 hvan.2 hDD hP2 hD
    rw [← hYdef, ← hQdef, ← hRdef] at h
    have hsq : Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V) ≤ 2 * P + 2 * Ra := by
      rw [hPdef, hRdef]; exact hsqDD
    have hstep : α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
        ≤ α ^ 4 * (2 * P + 2 * Ra) :=
      mul_le_mul_of_nonneg_left hsq hα4nn
    have hstep2 : α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V) + Qa + α ^ 2 * Ra
        ≤ 4 * (α ^ 4 * P + Qa + α ^ 2 * Ra) := by
      have h4R : α ^ 4 * Ra ≤ α ^ 2 * Ra := mul_le_mul_of_nonneg_right hα4le hR0
      have hw1 : 0 ≤ α ^ 4 * P := mul_nonneg hα4nn hP0
      have hw2 : 0 ≤ α ^ 4 * Ra := mul_nonneg hα4nn hR0
      have hw3 : 0 ≤ α ^ 2 * Ra := mul_nonneg (sq_nonneg α) hR0
      nlinarith [hstep, h4R, hw1, hw2, hw3, hP0, hQ0, hR0]
    refine le_trans h ?_
    calc C₃ * (α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V) + Qa + α ^ 2 * Ra)
        ≤ C₃ * (4 * (α ^ 4 * P + Qa + α ^ 2 * Ra)) :=
          mul_le_mul_of_nonneg_left hstep2 hC₃.le
      _ = 4 * C₃ * M := by rw [hMdef]; ring
  have hXY : Xb + Yb ≤ (C₂ + 4 * C₃ + 1) * M := by
    have hsum : Xb + Yb ≤ C₂ * M + 4 * C₃ * M := by linarith [h1, h2]
    have hle : C₂ * M + 4 * C₃ * M ≤ (C₂ + 4 * C₃ + 1) * M := by nlinarith [hM0]
    linarith [hsum, hle]
  have hmainM : Work.Spaces.HkSq α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ)
      ≤ (C₁ * (C₂ + 4 * C₃ + 1)) * M := by
    have h := hD₁ α V hα hα1 hsm
    rw [← hXdef, ← hYdef] at h
    have h2' : C₁ * (Xb + Yb) ≤ C₁ * ((C₂ + 4 * C₃ + 1) * M) :=
      mul_le_mul_of_nonneg_left hXY hC₁.le
    have h3' : C₁ * ((C₂ + 4 * C₃ + 1) * M) = (C₁ * (C₂ + 4 * C₃ + 1)) * M := by ring
    linarith [h, h2', h3']
  have hmain : Work.Spaces.HkSq α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ)
      ≤ (C₁ * (C₂ + 4 * C₃ + 1)) * (α ^ 4 * Work.Spaces.HkSq α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ)
          + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)
          + α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V)) := by
    rw [hMdef] at hmainM
    exact hmainM
  exact HkNorm_le_of_HkSq_le hKpos hα.le hmain

end Work.FTS.EllipticEst.RPFresh
