import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Submission.Work.FTS.Vocab
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.L12Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Filter Set

namespace Work.FTS.StrongEps.EpsE4Thr.TracesAux

/-! ## The mixed derivatives of a separated (angular × radial) product

For a factor `G` of `θ` alone and a factor `h` of `z` alone the mixed operator splits exactly
(`mixed_ang_mul_rad`): `D_z^b D_θ^a (G(θ)·h(z)) = (D_θ^a G)(θ)·(D_z^b h)(z)`.

The two ingredients are the facts that the operators preserve the class:

* `DthIter_mul_zfac` — `D_θ^i` commutes with multiplication by a `z`-only factor (no smoothness
  is needed: the only ingredient is the unconditional scalar linearity of `deriv`, provided here
  by `deriv_mul_const_uncond` / `deriv_const_mul_uncond`);
* `DzIter_angfac` — `D_z^b` commutes with multiplication by a `θ`-only factor. -/

/-- `deriv` is scalar homogeneous **unconditionally** on the right (Mathlib's `deriv_mul_const`
needs differentiability): if `f` is not differentiable at `x`, then neither is `f · c` for
`c ≠ 0`, so both sides are `0`. -/
private theorem deriv_mul_const_uncond (c x : ℝ) (f : ℝ → ℝ) :
    deriv (fun y => f y * c) x = deriv f x * c := by
  rcases eq_or_ne c 0 with h | h
  · subst h; simp
  · rcases em (DifferentiableAt ℝ f x) with hf | hf
    · exact deriv_mul_const hf c
    · have h2 : ¬ DifferentiableAt ℝ (fun y => f y * c) x := by
        intro hh
        apply hf
        have he : f = fun y => (f y * c) * c⁻¹ := by
          funext y; rw [mul_assoc, mul_inv_cancel₀ h, mul_one]
        rw [he]
        exact hh.mul_const c⁻¹
      rw [deriv_zero_of_not_differentiableAt hf,
        deriv_zero_of_not_differentiableAt h2, zero_mul]

/-- `deriv` is scalar homogeneous **unconditionally** on the left. -/
private theorem deriv_const_mul_uncond (c x : ℝ) (f : ℝ → ℝ) :
    deriv (fun y => c * f y) x = c * deriv f x := by
  rcases eq_or_ne c 0 with h | h
  · subst h; simp
  · rcases em (DifferentiableAt ℝ f x) with hf | hf
    · exact deriv_const_mul c hf
    · have h2 : ¬ DifferentiableAt ℝ (fun y => c * f y) x := by
        intro hh
        apply hf
        have he : f = fun y => c⁻¹ * (c * f y) := by
          funext y; rw [← mul_assoc, inv_mul_cancel₀ h, one_mul]
        rw [he]
        exact hh.const_mul c⁻¹
      rw [deriv_zero_of_not_differentiableAt hf,
        deriv_zero_of_not_differentiableAt h2, mul_zero]

/-- `D_θ^i` commutes with multiplication by a factor depending only on `z`. -/
private theorem DthIter_mul_zfac (i : ℕ) (G : ℝ → ℝ) (h : ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => G θ * h z)
      = fun z θ => (Work.Spaces.DthIter i (fun _ θ' => G θ') 0 θ) * h z := by
  induction i with
  | zero => rfl
  | succ i ih =>
      funext z θ
      show Work.Spaces.Dth (Work.Spaces.DthIter i (fun z θ => G θ * h z)) z θ
        = (Work.Spaces.DthIter (i + 1) (fun _ θ' => G θ') 0 θ) * h z
      rw [ih]
      show Real.sin (2 * θ)
          * deriv (fun θ' => (Work.Spaces.DthIter i (fun _ θ' => G θ') 0 θ') * h z) θ
        = (Real.sin (2 * θ)
          * deriv (fun θ' => Work.Spaces.DthIter i (fun _ θ' => G θ') 0 θ') θ) * h z
      rw [deriv_mul_const_uncond]
      ring

/-- `D_z^b` commutes with multiplication by a factor depending only on `θ`. -/
private theorem DzIter_angfac (b : ℕ) (c : ℝ → ℝ) (h : ℝ → ℝ) :
    Work.Spaces.DzIter b (fun z θ => c θ * h z)
      = fun z θ => c θ * Work.Elliptic.DzdIter b h z := by
  induction b with
  | zero => rfl
  | succ b ih =>
      funext z θ
      show Work.Spaces.Dz (Work.Spaces.DzIter b (fun z θ => c θ * h z)) z θ
        = c θ * Work.Elliptic.DzdIter (b + 1) h z
      rw [ih]
      show z * deriv (fun z' => c θ * Work.Elliptic.DzdIter b h z') z
        = c θ * (z * deriv (Work.Elliptic.DzdIter b h) z)
      rw [deriv_const_mul_uncond]
      ring

/-- **Exact separation of the mixed derivatives of an angular × radial product**:
`D_z^b D_θ^a (G(θ)·h(z)) = (D_θ^a G)(θ)·(D_z^b h)(z)`, for every `z` and `θ` (no smoothness
whatsoever is needed — the operators are the totalised `deriv`-based ones). -/
theorem mixed_ang_mul_rad (a b : ℕ) (G h : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed b a (fun z θ => G θ * h z) z θ
      = (Work.Spaces.DthIter a (fun _ θ' => G θ') 0 θ) * Work.Elliptic.DzdIter b h z := by
  rw [Work.Spaces.mixed, DthIter_mul_zfac a G h,
    DzIter_angfac b (fun θ => Work.Spaces.DthIter a (fun _ θ' => G θ') 0 θ) h]

/-! ## The explicit vanishing of the angular weight times `Γ²`

The angular trace weighs `D_θ^aΓ` by `sin(2θ)^{1-γ}` with `γ = gam α = 1 + α/10 > 1`, so the
weight *diverges* at both endpoints.  What saves the day is that `Γ` itself vanishes there:
`Γ(θ)² ≲ θ^{2α/3}` near `0` and `≲ (π/2-θ)^{4α/3}` near `π/2`, while Jordan's inequality gives
`sin(2θ)^{-α/10} ≲ θ^{-α/10}` (resp. `≲ (π/2-θ)^{-α/10}`), so the products behave like
`θ^{17α/30}` (resp. `(π/2-θ)^{37α/30}`) with **positive** exponents.

Everything is squeezed through the explicit majorant `sin_rpow_le_majorant` of
`Submission/Work/Spaces/sin_rpow_le_majorant.lean`. -/

/-- `Γ(θ)² ≤ θ^{2α/3}` for `0 < θ < π/4`: this is `sin θ ≤ θ` and `cos²θ ≤ 1` raised to the
power `α/3` and squared. -/
private theorem Gam_sq_le_rpow_right {α : ℝ} (hα : 0 < α) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < Real.pi / 4) :
    Work.Spaces.Gam α θ ^ 2 ≤ θ ^ (2 * α / 3) := by
  have hθpi : θ < Real.pi := by linarith [Real.pi_pos, hθ1]
  have hsin0 : 0 ≤ Real.sin θ := (Real.sin_pos_of_pos_of_lt_pi hθ0 hθpi).le
  have hsinle : Real.sin θ ≤ θ := Real.sin_le hθ0.le
  have hcosle : Real.cos θ ^ 2 ≤ 1 := Real.cos_sq_le_one θ
  have hbase : Real.sin θ * Real.cos θ ^ 2 ≤ θ := by
    have := mul_le_mul hsinle hcosle (sq_nonneg (Real.cos θ)) hθ0.le
    simpa using this
  have hle1 : Work.Spaces.Gam α θ ≤ θ ^ (α / 3) := by
    rw [Work.Spaces.Gam]
    exact Real.rpow_le_rpow (by positivity) hbase (by positivity)
  have hsq : (θ ^ (α / 3)) ^ 2 = θ ^ (2 * α / 3) := by
    rw [← Real.rpow_two (θ ^ (α / 3)), ← Real.rpow_mul hθ0.le (α / 3) (2 : ℝ)]
    congr 1
    ring
  calc Work.Spaces.Gam α θ ^ 2 ≤ (θ ^ (α / 3)) ^ 2 :=
        pow_le_pow_left₀ (Real.rpow_nonneg (mul_nonneg hsin0 (sq_nonneg _)) _) hle1 2
    _ = θ ^ (2 * α / 3) := hsq

/-- `Γ(θ)² ≤ (π/2-θ)^{4α/3}` for `π/4 < θ < π/2`: here `sin θ ≤ 1`, so `Γ ≤ (cos²θ)^{α/3}`,
and `cos θ = sin (π/2-θ) ≤ π/2-θ`. -/
private theorem Gam_sq_le_rpow_left {α : ℝ} (hα : 0 < α) {θ : ℝ} (hθ0 : Real.pi / 4 < θ)
    (hθ1 : θ < Real.pi / 2) :
    Work.Spaces.Gam α θ ^ 2 ≤ (Real.pi / 2 - θ) ^ (4 * α / 3) := by
  have hd0 : 0 < Real.pi / 2 - θ := by linarith
  have hsin0 : 0 ≤ Real.sin θ :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ0, Real.pi_pos])
      (by linarith [Real.pi_pos])).le
  have hcos0 : 0 ≤ Real.cos θ :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩).le
  have hbb : Real.sin θ * Real.cos θ ^ 2 ≤ Real.cos θ ^ 2 := by
    have := mul_le_mul_of_nonneg_right (Real.sin_le_one θ) (sq_nonneg (Real.cos θ))
    simpa using this
  have hle1 : Work.Spaces.Gam α θ ≤ Real.cos θ ^ (2 * α / 3) := by
    have h1 : Work.Spaces.Gam α θ ≤ (Real.cos θ ^ 2) ^ (α / 3) := by
      rw [Work.Spaces.Gam]
      exact Real.rpow_le_rpow (mul_nonneg hsin0 (sq_nonneg _)) hbb (by positivity)
    have h2 : (Real.cos θ ^ 2) ^ (α / 3) = Real.cos θ ^ (2 * α / 3) := by
      rw [← Real.rpow_two (Real.cos θ), ← Real.rpow_mul hcos0 (2 : ℝ) (α / 3)]
      congr 1
      ring
    rw [h2] at h1
    exact h1
  have hle2 : Real.cos θ ^ (2 * α / 3) ≤ (Real.pi / 2 - θ) ^ (2 * α / 3) := by
    rw [← Real.sin_pi_div_two_sub θ]
    exact Real.rpow_le_rpow
      (Real.sin_pos_of_pos_of_lt_pi hd0 (by linarith [Real.pi_pos])).le
      (Real.sin_le hd0.le) (by positivity)
  have hsq : ((Real.pi / 2 - θ) ^ (2 * α / 3)) ^ 2 = (Real.pi / 2 - θ) ^ (4 * α / 3) := by
    rw [← Real.rpow_two ((Real.pi / 2 - θ) ^ (2 * α / 3)),
      ← Real.rpow_mul hd0.le (2 * α / 3) (2 : ℝ)]
    congr 1
    ring
  calc Work.Spaces.Gam α θ ^ 2 ≤ ((Real.pi / 2 - θ) ^ (2 * α / 3)) ^ 2 :=
        pow_le_pow_left₀ (Real.rpow_nonneg (mul_nonneg hsin0 (sq_nonneg _)) _)
          (le_trans hle1 hle2) 2
    _ = (Real.pi / 2 - θ) ^ (4 * α / 3) := hsq

/-- `sin(2θ)^{1-γ}·Γ(θ)² → 0` as `θ → 0⁺`. -/
private theorem tendsto_sin_rpow_gam_sq_right {α : ℝ} (hα : 0 < α) :
    Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
      * Work.Spaces.Gam α θ ^ 2) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hexp : (1 : ℝ) - Work.Spaces.gam α = -(α / 10) := by rw [Work.Spaces.gam]; ring
  have hp : 0 < α / 10 := by positivity
  have hq : 0 < 17 * α / 30 := by linarith
  have hpow : Filter.Tendsto (fun θ : ℝ => θ ^ (17 * α / 30))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h : Filter.Tendsto (fun θ : ℝ => θ ^ (17 * α / 30)) (nhds (0 : ℝ))
        (nhds (0 ^ (17 * α / 30))) :=
      (Real.continuousAt_rpow_const 0 (17 * α / 30) (Or.inr hq.le)).tendsto
    rw [Real.zero_rpow (ne_of_gt hq)] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hdom := hpow.const_mul (2 * (Real.pi / 4) ^ (α / 10))
  rw [mul_zero] at hdom
  refine squeeze_zero' ?_ ?_ hdom
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < Real.pi / 4 by positivity)] with θ hθ
    rw [hexp]
    exact mul_nonneg (Real.rpow_nonneg (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])).le _) (sq_nonneg _)
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < Real.pi / 4 by positivity)] with θ hθ
    rw [hexp]
    have hGam2 := Gam_sq_le_rpow_right hα hθ.1 hθ.2
    have hmaj := Work.Spaces.sin_rpow_le_majorant (α / 10) θ hp
      ⟨hθ.1.le, by linarith [hθ.2, Real.pi_pos]⟩
    have hle2 : (Real.pi / 2 - θ) ^ (-(α / 10)) ≤ θ ^ (-(α / 10)) :=
      Real.rpow_le_rpow_of_nonpos hθ.1 (by linarith [hθ.2]) (by linarith)
    have h2 : (Real.pi / 4) ^ (α / 10) * (θ ^ (-(α / 10)) + (Real.pi / 2 - θ) ^ (-(α / 10)))
        ≤ (Real.pi / 4) ^ (α / 10) * (2 * θ ^ (-(α / 10))) :=
      mul_le_mul_of_nonneg_left (by linarith [hle2])
        (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ Real.pi / 4) (α / 10))
    have hmaj' : Real.sin (2 * θ) ^ (-(α / 10))
        ≤ 2 * (Real.pi / 4) ^ (α / 10) * θ ^ (-(α / 10)) := by
      refine le_trans hmaj (le_trans h2 ?_)
      exact le_of_eq (by ring)
    have hb : 0 ≤ 2 * (Real.pi / 4) ^ (α / 10) * θ ^ (-(α / 10)) :=
      mul_nonneg (mul_nonneg (by norm_num)
        (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ Real.pi / 4) _))
        (Real.rpow_nonneg hθ.1.le _)
    have hprod := mul_le_mul hmaj' hGam2 (sq_nonneg _) hb
    have hrw : (2 * (Real.pi / 4) ^ (α / 10) * θ ^ (-(α / 10))) * θ ^ (2 * α / 3)
        = 2 * (Real.pi / 4) ^ (α / 10) * θ ^ (17 * α / 30) := by
      rw [mul_assoc, mul_assoc, ← Real.rpow_add hθ.1]
      rw [show -(α / 10) + 2 * α / 3 = 17 * α / 30 by ring]
      ring
    exact le_trans hprod hrw.le

/-- `sin(2θ)^{1-γ}·Γ(θ)² → 0` as `θ → (π/2)⁻`. -/
private theorem tendsto_sin_rpow_gam_sq_left {α : ℝ} (hα : 0 < α) :
    Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
      * Work.Spaces.Gam α θ ^ 2) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hexp : (1 : ℝ) - Work.Spaces.gam α = -(α / 10) := by rw [Work.Spaces.gam]; ring
  have hp : 0 < α / 10 := by positivity
  have hq2 : 0 < 37 * α / 30 := by linarith
  have hδ : Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h3 : Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (nhds (Real.pi / 2)) (nhds 0) := by
        simpa using (tendsto_const_nhds.sub Filter.tendsto_id :
          Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (nhds (Real.pi / 2))
            (nhds (Real.pi / 2 - Real.pi / 2)))
      exact h3.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with θ hθ
      show (0 : ℝ) < Real.pi / 2 - θ
      have := Set.mem_Iio.mp hθ
      linarith
  have hpowδ : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (37 * α / 30))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have h := (Real.continuousAt_rpow_const 0 (37 * α / 30) (Or.inr hq2.le)).tendsto.comp
      (hδ.mono_right nhdsWithin_le_nhds)
    simpa [Function.comp_def, Real.zero_rpow (ne_of_gt hq2)] using h
  have hdom := hpowδ.const_mul (2 * (Real.pi / 4) ^ (α / 10))
  rw [mul_zero] at hdom
  refine squeeze_zero' ?_ ?_ hdom
  · filter_upwards [Ioo_mem_nhdsLT (show Real.pi / 4 < Real.pi / 2 by linarith [Real.pi_pos])]
      with θ hθ
    rw [hexp]
    exact mul_nonneg (Real.rpow_nonneg (Real.sin_pos_of_pos_of_lt_pi
      (by linarith [hθ.1, Real.pi_pos]) (by linarith [hθ.2, Real.pi_pos])).le _) (sq_nonneg _)
  · filter_upwards [Ioo_mem_nhdsLT (show Real.pi / 4 < Real.pi / 2 by linarith [Real.pi_pos])]
      with θ hθ
    rw [hexp]
    have hG := Gam_sq_le_rpow_left hα hθ.1 hθ.2
    have hmaj := Work.Spaces.sin_rpow_le_majorant (α / 10) θ hp
      ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
    have hle3 : θ ^ (-(α / 10)) ≤ (Real.pi / 2 - θ) ^ (-(α / 10)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith [hθ.2]) (by linarith [hθ.1]) (by linarith)
    have h2 : (Real.pi / 4) ^ (α / 10) * (θ ^ (-(α / 10)) + (Real.pi / 2 - θ) ^ (-(α / 10)))
        ≤ (Real.pi / 4) ^ (α / 10) * (2 * (Real.pi / 2 - θ) ^ (-(α / 10))) :=
      mul_le_mul_of_nonneg_left (by linarith [hle3])
        (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ Real.pi / 4) (α / 10))
    have hmaj' : Real.sin (2 * θ) ^ (-(α / 10))
        ≤ 2 * (Real.pi / 4) ^ (α / 10) * (Real.pi / 2 - θ) ^ (-(α / 10)) := by
      refine le_trans hmaj (le_trans h2 ?_)
      exact le_of_eq (by ring)
    have hb : 0 ≤ 2 * (Real.pi / 4) ^ (α / 10) * (Real.pi / 2 - θ) ^ (-(α / 10)) :=
      mul_nonneg (mul_nonneg (by norm_num)
        (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ Real.pi / 4) _))
        (Real.rpow_nonneg (by linarith [hθ.2]) _)
    have hprod := mul_le_mul hmaj' hG (sq_nonneg _) hb
    have hrw : (2 * (Real.pi / 4) ^ (α / 10) * (Real.pi / 2 - θ) ^ (-(α / 10)))
          * (Real.pi / 2 - θ) ^ (4 * α / 3)
        = 2 * (Real.pi / 4) ^ (α / 10) * (Real.pi / 2 - θ) ^ (37 * α / 30) := by
      rw [mul_assoc, mul_assoc, ← Real.rpow_add (by linarith [hθ.2])]
      rw [show -(α / 10) + 4 * α / 3 = 37 * α / 30 by ring]
      ring
    exact le_trans hprod hrw.le

/-- **The angular trace of a `D_θ`-iterate of `Γ`.**  Squeezing the hypothesis
`|D_θ^aΓ| ≤ Cg·Γ` between `0` and `Cg²·sin(2θ)^{1-γ}Γ²` reduces the two one-sided limits to the
explicit vanishing proved above. -/
private theorem trace_aux_base {α : ℝ} (hα : 0 < α) {a : ℕ} {Cg : ℝ} (hCg : 0 < Cg)
    (hgam : ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
        ≤ Cg * Work.Spaces.Gam α θ) :
    (Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) ∧
    (Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) := by
  have hCg2 : 0 ≤ Cg ^ 2 := sq_nonneg Cg
  refine ⟨?_, ?_⟩
  · have h := (tendsto_sin_rpow_gam_sq_right hα).const_mul (Cg ^ 2)
    rw [mul_zero] at h
    refine squeeze_zero' ?_ ?_ h
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < Real.pi / 4 by positivity)] with θ hθ
      exact mul_nonneg (Real.rpow_nonneg (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])).le _) (sq_nonneg _)
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < Real.pi / 4 by positivity)] with θ hθ
      have hs : 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
        Real.rpow_nonneg (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos])).le _
      have h1 : (Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
          ≤ (Cg * Work.Spaces.Gam α θ) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _)
          (hgam θ hθ.1 (by linarith [hθ.2, Real.pi_pos])) 2
      calc Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
          ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Cg * Work.Spaces.Gam α θ) ^ 2 := mul_le_mul_of_nonneg_left h1 hs
        _ = Cg ^ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * Work.Spaces.Gam α θ ^ 2) := by ring
  · have h := (tendsto_sin_rpow_gam_sq_left hα).const_mul (Cg ^ 2)
    rw [mul_zero] at h
    refine squeeze_zero' ?_ ?_ h
    · filter_upwards [Ioo_mem_nhdsLT (show Real.pi / 4 < Real.pi / 2 by linarith [Real.pi_pos])]
        with θ hθ
      exact mul_nonneg (Real.rpow_nonneg (Real.sin_pos_of_pos_of_lt_pi
        (by linarith [hθ.1, Real.pi_pos]) (by linarith [hθ.2, Real.pi_pos])).le _) (sq_nonneg _)
    · filter_upwards [Ioo_mem_nhdsLT (show Real.pi / 4 < Real.pi / 2 by linarith [Real.pi_pos])]
        with θ hθ
      have hs : 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
        Real.rpow_nonneg (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos])
          (by linarith [hθ.2, Real.pi_pos])).le _
      have h1 : (Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
          ≤ (Cg * Work.Spaces.Gam α θ) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _)
          (hgam θ (by linarith [hθ.1, Real.pi_pos]) hθ.2) 2
      calc Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
          ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Cg * Work.Spaces.Gam α θ) ^ 2 := mul_le_mul_of_nonneg_left h1 hs
        _ = Cg ^ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * Work.Spaces.Gam α θ ^ 2) := by ring

/-- **The boundary traces of a separated (angular × radial) product `Γ(θ)·r(z)`** for
`α > 0`.

The mixed derivatives of the product are *globally* separable:
`D_z^bD_θ^a(Γ(θ)·r(z)) = (D_θ^a Γ)(θ)·(D_z^b r)(z)` (`mixed_mul_rad_ang`, i.e. the `z`-iterates
commute with the `θ`-only factor and the `θ`-iterates with the `z`-only factor), so

* the radial traces reduce to `z·(D_z^b r·w)² → 0` (`hr0`, `hr1`) times the fixed constant
  `(D_θ^aΓ)(θ)²`, and
* the angular traces reduce to `sin(2θ)^{1-γ}·(D_θ^aΓ)² → 0` at `θ = 0, π/2⁻`, squeezed
  through `hgam` and the explicit vanishing `sin(2θ)^{1-γ}Γ(θ)² → 0`, where
  `1-γ+2α/3 = 17α/30 > 0` at `θ=0` and `1-γ+4α/3 = 37α/30 > 0` at `θ=π/2`; this is exactly
  where `hα : 0 < α` is needed (at `α = 0` the angular trace is a nonzero constant).

The hypothesis `ContDiffOn ℝ (k+1) r (Ioi 0)` only records that `D_z^b r` is honest for
`b ≤ k` (the `D_z`-iterates stay in the same smoothness class). -/
theorem BdryTraces_Gam_mul_rad {α : ℝ} (hα : 0 < α) {k : ℕ} {r : ℝ → ℝ} {Cg : ℝ}
    (hCg : 0 < Cg)
    (hgam : ∀ a : ℕ, a ≤ k → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ| ≤ Cg * Work.Spaces.Gam α θ)
    (hrsm : ContDiffOn ℝ (k + 1) r (Set.Ioi 0))
    (hr0 : ∀ b : ℕ, b ≤ k → Filter.Tendsto
      (fun z : ℝ => z * (Work.Elliptic.DzdIter b r z * Work.Spaces.w z) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hr1 : ∀ b : ℕ, b ≤ k → Filter.Tendsto
      (fun z : ℝ => z * (Work.Elliptic.DzdIter b r z * Work.Spaces.w z) ^ 2) Filter.atTop (nhds 0)) :
    Work.FTS.Nonlin.BdryTraces α k (fun z θ => Work.Spaces.Gam α θ * r z) := by
  intro a b hab
  have ha : a ≤ k := by omega
  have hb : b ≤ k := by omega
  -- the exact separation of the mixed derivatives of the product
  have hsep : ∀ z θ : ℝ, Work.Spaces.mixed b a (fun z θ => Work.Spaces.Gam α θ * r z) z θ
      = (Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ)
        * Work.Elliptic.DzdIter b r z :=
    fun z θ => mixed_ang_mul_rad a b (fun θ => Work.Spaces.Gam α θ) r z θ
  obtain ⟨hbase0, hbaseπ⟩ := trace_aux_base hα hCg (hgam a ha)
  refine ⟨fun θ hθ => ⟨?_, ?_⟩, fun z hz => ⟨?_, ?_⟩⟩
  · -- radial trace at `z → 0⁺`: the constant `(D_θ^aΓ)(θ)²` times the trace of `D_z^b r`
    have h := (hr0 b hb).const_mul
      ((Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2)
    rw [mul_zero] at h
    refine h.congr' (Filter.Eventually.of_forall fun z => ?_)
    beta_reduce
    rw [hsep z θ]
    ring
  · -- radial trace at `z → ∞`
    have h := (hr1 b hb).const_mul
      ((Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2)
    rw [mul_zero] at h
    refine h.congr' (Filter.Eventually.of_forall fun z => ?_)
    beta_reduce
    rw [hsep z θ]
    ring
  · -- angular trace at `θ → 0⁺`: the constant `(D_z^b r)(z)²` times the angular trace of `Γ`
    have h := hbase0.const_mul ((Work.Elliptic.DzdIter b r z) ^ 2)
    rw [mul_zero] at h
    refine h.congr' (Filter.Eventually.of_forall fun θ => ?_)
    beta_reduce
    rw [hsep z θ]
    ring
  · -- angular trace at `θ → (π/2)⁻`
    have h := hbaseπ.const_mul ((Work.Elliptic.DzdIter b r z) ^ 2)
    rw [mul_zero] at h
    refine h.congr' (Filter.Eventually.of_forall fun θ => ?_)
    beta_reduce
    rw [hsep z θ]
    ring

end Work.FTS.StrongEps.EpsE4Thr.TracesAux
