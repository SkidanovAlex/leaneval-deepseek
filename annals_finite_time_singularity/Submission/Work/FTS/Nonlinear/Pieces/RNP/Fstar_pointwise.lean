/-
# `Fstar_pointwise`: the pointwise bounds for the profile `F_*`

T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021), 1--70.

The profile of the self-similar ansatz is (tex 1334)

  `F_*(z,θ) = α · (Γ(θ)/c) · 2z/(1+z)²`,   `Γ(θ) = (sin θ cos²θ)^{α/3}`,

i.e. a product of the angular factor `Γ` and the radial factor `2z/(1+z)²`.  This file
collects the *pointwise* (not `sup`) consequences of that factorization, in the exact
shape needed by the nonlinear estimates of §8:

* `|F_*| ≤ C α z/(1+z)²`;
* `|∂_z^c F_*| ≤ C α/(1+z)^{c+1}` for `c ≤ 4`;
* `|∂_z^c D_θ^a F_*| · sin(2θ)^{-α/5}/(α + sin 2θ) ≤ C α/(1+z)^{c+1}` for `1 ≤ a`, `a+c ≤ 4`;
* `|D_θ^a F_*| · sin(2θ)^{-α/5}/(α + sin 2θ) ≤ C α z/(1+z)²` for `1 ≤ a ≤ 4`.

Since `F_* = a_α · (Γ ⊗ h)` with `a_α = 2α/c` (`|a_α| ≤ 20α` because `c ≥ 1/10`) and
`h(z) = z/(1+z)²`, every derivative is again a product: the angular operator
`D_θ = sin(2θ)∂_θ` acts on `Γ` (through its univariate model `Spaces.dthU`) and `∂_z` acts
on `h`.  Two estimates close everything:

* **radial, sharp:** `|h^{(c)}(z)| ≤ c! (c+1)/(1+z)^{c+1}` for `z > 0`.  The available
  weighted bound `Spaces.pzIter_hKer_bound` only gives `/(1+z)^c`; one power is gained by
  using the closed form `h^{(c)}(z) = (-1)^c c! (z-c) (1+z)^{-(c+2)}`
  (`Spaces.iter_deriv_hKerClosed`) together with `|z - c| ≤ (c+1)(1+z)`;
* **angular, weighted:** for `1 ≤ a ≤ 4` and `0 < α ≤ 1`,

    `|D_θ^a Γ(θ)| · sin(2θ)^{-α/5}/(α + sin 2θ) ≤ K`   on `(0,π/2)`,

  with `K` universal.  For `a ≥ 2` this is `DthAux.dthGamWeightLe`; the missing case
  `a = 1` is `D_θΓ = α q Γ` with `|q| ≤ 4/3` (`Spaces.dthU_iter_Gam`, `DthAux.abs_qfun_le`)
  together with `α Γ w ≤ 1` (`Spaces.Gam_mul_weight_le`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.IntervalCases
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.Spaces.c_bounds
import Submission.Work.FTS.Nonlinear.FstarPkg.Fstar_W
import Submission.Work.FTS.Nonlinear.FstarPkg.DthFstar_W

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The sharp radial bound for the iterated derivatives of `h(z) = z/(1+z)²` -/

/-- The sharp radial bound: `(1+z)^{c+1} |h^{(c)}(z)| ≤ c! (c+1)` for `z > 0`, where
`h(z) = z/(1+z)²` is the radial profile of `F_*`.  (The weighted version
`Spaces.pzIter_hKer_bound` has only `(1+z)^c` on the left.) -/
lemma hKer_deriv_pow_mul_le (c : ℕ) {z : ℝ} (hz : 0 < z) :
    (1 + z) ^ (c + 1) * |deriv^[c] Work.Spaces.hKer z|
      ≤ (c.factorial : ℝ) * ((c : ℝ) + 1) := by
  have hz1 : -1 < z := by linarith
  have hz' : (1 : ℝ) + z ≠ 0 := by positivity
  have hcnn : (0 : ℝ) ≤ (c.factorial : ℝ) := by positivity
  have hinvnn : 0 ≤ ((1 + z)⁻¹) ^ (c + 2) := by positivity
  have hclosed : deriv^[c] Work.Spaces.hKer z = Work.Spaces.hKerClosed c z := by
    have h1 : Work.Spaces.hKer = fun z : ℝ => z / (1 + z) ^ 2 := by
      funext y; rw [Work.Spaces.hKer_apply]
    rw [h1]
    exact Work.Spaces.iter_deriv_hKerClosed c z hz1
  have hsign : |(-1 : ℝ) ^ c| = 1 := by simp [abs_pow]
  have hfact : |(c.factorial : ℝ)| = (c.factorial : ℝ) := abs_of_nonneg hcnn
  have hpowc : |((1 + z)⁻¹) ^ (c + 2)| = ((1 + z)⁻¹) ^ (c + 2) := abs_of_nonneg hinvnn
  have habs : |Work.Spaces.hKerClosed c z|
      = (c.factorial : ℝ) * (|z - (c : ℝ)| * ((1 + z)⁻¹) ^ (c + 2)) := by
    rw [Work.Spaces.hKerClosed, abs_mul, abs_mul, abs_mul, hsign, hfact, hpowc]
    ring
  have hpow : (1 + z) ^ (c + 1) * ((1 + z)⁻¹) ^ (c + 2) = (1 + z)⁻¹ := by
    have h2 : ((1 + z)⁻¹) ^ (c + 2) = ((1 + z)⁻¹) ^ (c + 1) * (1 + z)⁻¹ := by
      rw [show c + 2 = (c + 1) + 1 from by omega, pow_succ]
    rw [h2, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hz', one_pow, one_mul]
  have hkey : |z - (c : ℝ)| * ((1 + z)⁻¹) ≤ (c : ℝ) + 1 := by
    have h1 : |z - (c : ℝ)| ≤ ((c : ℝ) + 1) * (1 + z) := by
      have h2 : |z - (c : ℝ)| ≤ z + (c : ℝ) := by
        rw [abs_sub_le_iff]
        constructor <;> linarith [Nat.cast_nonneg (α := ℝ) c, hz.le]
      have h3 : z + (c : ℝ) ≤ ((c : ℝ) + 1) * (1 + z) := by
        nlinarith [Nat.cast_nonneg (α := ℝ) c, hz.le,
          mul_nonneg hz.le (Nat.cast_nonneg (α := ℝ) c)]
      linarith
    calc |z - (c : ℝ)| * ((1 + z)⁻¹) ≤ (((c : ℝ) + 1) * (1 + z)) * ((1 + z)⁻¹) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (c : ℝ) + 1 := by rw [mul_assoc, mul_inv_cancel₀ hz', mul_one]
  have hfin : (1 + z) ^ (c + 1)
        * ((c.factorial : ℝ) * (|z - (c : ℝ)| * ((1 + z)⁻¹) ^ (c + 2)))
      = (c.factorial : ℝ) * (|z - (c : ℝ)| * (1 + z)⁻¹) := by
    rw [show (1 + z) ^ (c + 1)
          * ((c.factorial : ℝ) * (|z - (c : ℝ)| * ((1 + z)⁻¹) ^ (c + 2)))
        = (c.factorial : ℝ)
          * (|z - (c : ℝ)| * ((1 + z) ^ (c + 1) * ((1 + z)⁻¹) ^ (c + 2))) by ring,
      hpow]
  rw [hclosed, habs, hfin]
  exact mul_le_mul_of_nonneg_left hkey hcnn

/-- The `c ≤ 4` instance of `hKer_deriv_pow_mul_le`: `(c!)(c+1) ≤ 120`. -/
lemma factorial_mul_succ_le_120 {c : ℕ} (hc : c ≤ 4) :
    (c.factorial : ℝ) * ((c : ℝ) + 1) ≤ 120 := by
  interval_cases c <;> norm_num

/-! ## The weighted angular bound for the `D_θ`-iterates of `Γ` -/

/-- For `1 ≤ a ≤ 4` the weighted angular factor `|D_θ^a Γ(θ)| · sin(2θ)^{-α/5}/(α+sin 2θ)`
is bounded by a universal constant, uniformly in `0 < α ≤ 1` and `θ ∈ (0,π/2)`.

For `a ≥ 2` this is `DthAux.dthGamWeightLe`; for `a = 1` we use `D_θΓ = α q Γ` with
`|q| ≤ 4/3` and `α Γ · sin(2θ)^{-α/5}/(α + sin 2θ) ≤ 1`. -/
lemma dthU_Gam_weight_le {K : ℝ}
    (hK : ∀ m : ℕ, 2 ≤ m → m ≤ 5 → ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ|
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) ≤ K * α)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ a : ℕ, 1 ≤ a → a ≤ 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.dthU^[a] (fun t => Work.Spaces.Gam α t) θ|
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) ≤ max K (4 / 3) := by
  intro a ha1 ha4 θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hw0 : 0 ≤ (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) :=
    Work.Spaces.gamma_weight_nonneg α θ hα hθI
  have hK0 : 0 ≤ K := by
    have h := hK 2 (by norm_num) (by norm_num) α hα hα1 θ hθI
    have h0 : 0 ≤ |Work.Spaces.dthU^[2] (fun t => Work.Spaces.Gam α t) θ|
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) :=
      mul_nonneg (abs_nonneg _) hw0
    nlinarith [h, h0, hα]
  by_cases ha : a = 1
  · subst ha
    have hGam := Work.Spaces.Gam_bounds α θ hα hθI
    have hval : Work.Spaces.dthU^[1] (fun t => Work.Spaces.Gam α t) θ
        = α * Work.Spaces.qfun θ * Work.Spaces.Gam α θ := by
      simpa using Work.Spaces.dthU_iter_Gam 0 α hα hθ
    have hq : |Work.Spaces.qfun θ| ≤ 4 / 3 :=
      Work.FTS.Nonlinear.FstarPkg.DthAux.abs_qfun_le θ
    have hgw : α * Work.Spaces.Gam α θ
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) ≤ 1 := by
      rw [← mul_div_assoc]
      exact Work.Spaces.Gam_mul_weight_le α θ hα hθI
    rw [hval, abs_mul, abs_mul, abs_of_pos hα, abs_of_nonneg hGam.1]
    calc α * |Work.Spaces.qfun θ| * Work.Spaces.Gam α θ
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        = |Work.Spaces.qfun θ| * (α * Work.Spaces.Gam α θ
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) := by ring
      _ ≤ (4 / 3) * 1 :=
          mul_le_mul hq hgw (mul_nonneg (mul_nonneg (le_of_lt hα) hGam.1) hw0)
            (by norm_num)
      _ ≤ max K (4 / 3) := by rw [mul_one]; exact le_max_right K (4 / 3)
  · have ha2 : 2 ≤ a := by omega
    have h := hK a ha2 (by omega) α hα hα1 θ hθI
    calc |Work.Spaces.dthU^[a] (fun t => Work.Spaces.Gam α t) θ|
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        ≤ K * α := h
      _ ≤ K * 1 := mul_le_mul_of_nonneg_left hα1 hK0
      _ ≤ max K (4 / 3) := by rw [mul_one]; exact le_max_left K (4 / 3)

/-! ## The target -/

theorem Fstar_pointwise :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      (∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        |Work.Construction.Fstar α z θ| ≤ C * α * z / (1 + z) ^ 2) ∧
      (∀ c : ℕ, c ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        |Work.Spaces.pzIter c (Work.Construction.Fstar α) z θ| ≤ C * α / (1 + z) ^ (c + 1)) ∧
      (∀ a c : ℕ, 1 ≤ a → a + c ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        |Work.Spaces.pzIter c (Work.Spaces.DthIter a (Work.Construction.Fstar α)) z θ|
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
          ≤ C * α / (1 + z) ^ (c + 1)) ∧
      (∀ a : ℕ, 1 ≤ a → a ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        |Work.Spaces.DthIter a (Work.Construction.Fstar α) z θ|
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
          ≤ C * α * z / (1 + z) ^ 2) := by
  obtain ⟨K, hKpos, hKraw⟩ := Work.FTS.Nonlinear.FstarPkg.DthAux.dthGamWeightLe
  have hK : ∀ m : ℕ, 2 ≤ m → m ≤ 5 → ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ|
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) ≤ K * α := by
    intro m hm hm5 α hα hα1 θ hθ
    simpa only [Work.FTS.Nonlinear.FstarPkg.DthAux.Wt] using hKraw m hm hm5 α hα hα1 θ hθ
  refine ⟨2400 * (max K (4 / 3) + 1), by positivity, ?_⟩
  intro α hα hα1
  have hKa0 : 0 ≤ max K (4 / 3) := le_trans (by norm_num) (le_max_right K (4 / 3))
  have hcoef : |2 * α / Work.Spaces.c α| ≤ 20 * α :=
    Work.FTS.Nonlinear.FstarPkg.Fstar_coef_le α hα hα1
  have hcoefGam : ∀ θ ∈ Work.Spaces.Iθ,
      |(2 * α / Work.Spaces.c α) * Work.Spaces.Gam α θ| ≤ 20 * α := by
    intro θ hθ
    have hG := Work.Spaces.Gam_bounds α θ hα hθ
    rw [abs_mul, abs_of_nonneg hG.1]
    calc |2 * α / Work.Spaces.c α| * Work.Spaces.Gam α θ ≤ (20 * α) * 1 :=
          mul_le_mul hcoef hG.2 hG.1 (by linarith)
      _ = 20 * α := by ring
  have hcoefGam' : ∀ θ ∈ Work.Spaces.Iθ,
      |2 * α / Work.Spaces.c α| * |Work.Spaces.Gam α θ| ≤ 20 * α := by
    intro θ hθ
    rw [← abs_mul]
    exact hcoefGam θ hθ
  have hang : ∀ a : ℕ, 1 ≤ a → a ≤ 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.dthU^[a] (fun t => Work.Spaces.Gam α t) θ|
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) ≤ max K (4 / 3) :=
    dthU_Gam_weight_le hK hα hα1
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (1) the plain pointwise bound
    intro z hz θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
    have hzk : 0 ≤ z / (1 + z) ^ 2 := by positivity
    have hkey : |Work.Construction.Fstar α z θ| ≤ 20 * α * (z / (1 + z) ^ 2) := by
      rw [Work.FTS.Nonlinear.FstarPkg.Fstar_eq_factored α, abs_mul, abs_mul,
        Work.Spaces.hKer_apply]
      rw [abs_of_nonneg hzk]
      exact mul_le_mul_of_nonneg_right (hcoefGam' θ hθI) hzk
    refine hkey.trans ?_
    have hC : (20 : ℝ) ≤ 2400 * (max K (4 / 3) + 1) := by linarith [hKa0]
    calc 20 * α * (z / (1 + z) ^ 2) = 20 * (α * (z / (1 + z) ^ 2)) := by ring
      _ ≤ (2400 * (max K (4 / 3) + 1)) * (α * (z / (1 + z) ^ 2)) :=
          mul_le_mul_of_nonneg_right hC (mul_nonneg hα.le hzk)
      _ = 2400 * (max K (4 / 3) + 1) * α * z / (1 + z) ^ 2 := by ring
  · -- (2) the radial derivatives `∂_z^c F_*`, `c ≤ 4`
    intro c hc4 z hz θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
    have hz1 : 0 < (1 + z) ^ (c + 1) := pow_pos (by linarith) _
    rw [le_div_iff₀ hz1]
    rw [Work.FTS.Nonlinear.FstarPkg.pzIter_Fstar_eq α c z θ]
    have hker := hKer_deriv_pow_mul_le c hz
    have hcoefG := hcoefGam θ hθI
    have hfac := factorial_mul_succ_le_120 hc4
    have hident : |((2 * α / Work.Spaces.c α) * Work.Spaces.Gam α θ)
          * deriv^[c] Work.Spaces.hKer z| * (1 + z) ^ (c + 1)
        = |(2 * α / Work.Spaces.c α) * Work.Spaces.Gam α θ|
          * ((1 + z) ^ (c + 1) * |deriv^[c] Work.Spaces.hKer z|) := by
      rw [abs_mul]
      ring
    rw [hident]
    refine (mul_le_mul hcoefG hker (by positivity) (by positivity)).trans ?_
    have h1 : 20 * α * ((c.factorial : ℝ) * ((c : ℝ) + 1)) ≤ 20 * α * 120 :=
      mul_le_mul_of_nonneg_left hfac (by positivity)
    have h2 : 20 * α * 120 ≤ 2400 * (max K (4 / 3) + 1) * α := by
      have hM : (1 : ℝ) ≤ max K (4 / 3) + 1 := by linarith [hKa0]
      calc 20 * α * 120 = 2400 * (1 * α) := by ring
        _ ≤ 2400 * ((max K (4 / 3) + 1) * α) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hM hα.le) (by norm_num)
        _ = 2400 * (max K (4 / 3) + 1) * α := by ring
    linarith [h1, h2]
  · -- (3) the mixed derivatives `∂_z^c D_θ^a F_*`, `a ≥ 1`, `a + c ≤ 4`
    intro a c ha1 hac z hz θ hθ
    have hc4 : c ≤ 4 := by omega
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
    have hz1 : 0 < (1 + z) ^ (c + 1) := pow_pos (by linarith) _
    rw [le_div_iff₀ hz1]
    rw [Work.FTS.Nonlinear.FstarPkg.pzIter_DthIter_Fstar_eq α a c z θ]
    have hW0 : 0 ≤ (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) :=
      Work.Spaces.gamma_weight_nonneg α θ hα hθI
    have hker := hKer_deriv_pow_mul_le c hz
    have hanga := hang a ha1 (by omega) θ hθ
    have hcoefG := hcoefGam θ hθI
    have hfac := factorial_mul_succ_le_120 hc4
    have hident : |((2 * α / Work.Spaces.c α)
            * Work.Spaces.dthU^[a] (fun t => Work.Spaces.Gam α t) θ)
          * deriv^[c] Work.Spaces.hKer z|
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
          * (1 + z) ^ (c + 1)
        = (|2 * α / Work.Spaces.c α|
            * (|Work.Spaces.dthU^[a] (fun t => Work.Spaces.Gam α t) θ|
              * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))))
          * ((1 + z) ^ (c + 1) * |deriv^[c] Work.Spaces.hKer z|) := by
      rw [abs_mul, abs_mul]
      ring
    rw [hident]
    refine (mul_le_mul (mul_le_mul hcoef hanga (mul_nonneg (abs_nonneg _) hW0) (by positivity))
      hker (by positivity) (by positivity)).trans ?_
    have h1 : 20 * α * max K (4 / 3) * ((c.factorial : ℝ) * ((c : ℝ) + 1))
        ≤ 20 * α * max K (4 / 3) * 120 :=
      mul_le_mul_of_nonneg_left hfac (by positivity)
    have h2 : 20 * α * max K (4 / 3) * 120 ≤ 2400 * (max K (4 / 3) + 1) * α := by
      have hM : (max K (4 / 3) : ℝ) ≤ max K (4 / 3) + 1 := by linarith
      calc 20 * α * max K (4 / 3) * 120 = 2400 * (max K (4 / 3) * α) := by ring
        _ ≤ 2400 * ((max K (4 / 3) + 1) * α) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hM hα.le) (by norm_num)
        _ = 2400 * (max K (4 / 3) + 1) * α := by ring
    linarith [h1, h2]
  · -- (4) the angular derivatives `D_θ^a F_*`, `a ≥ 1`
    intro a ha1 ha4 z hz θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
    have hW0 : 0 ≤ (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) :=
      Work.Spaces.gamma_weight_nonneg α θ hα hθI
    have hzk : 0 ≤ z / (1 + z) ^ 2 := by positivity
    have hanga := hang a ha1 ha4 θ hθ
    have hker : |Work.Spaces.hKer z| = z / (1 + z) ^ 2 := by
      rw [Work.Spaces.hKer_apply]
      exact abs_of_nonneg hzk
    rw [Work.FTS.Nonlinear.FstarPkg.DthIter_Fstar_eq α a]
    have hident : |((2 * α / Work.Spaces.c α)
            * Work.Spaces.dthU^[a] (fun t => Work.Spaces.Gam α t) θ) * Work.Spaces.hKer z|
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        = (|2 * α / Work.Spaces.c α|
            * (|Work.Spaces.dthU^[a] (fun t => Work.Spaces.Gam α t) θ|
              * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))))
          * (z / (1 + z) ^ 2) := by
      rw [abs_mul, abs_mul, hker]
      ring
    rw [hident]
    refine (mul_le_mul (mul_le_mul hcoef hanga (mul_nonneg (abs_nonneg _) hW0) (by positivity))
      le_rfl hzk (by positivity)).trans ?_
    have hKb : 20 * max K (4 / 3) ≤ 2400 * (max K (4 / 3) + 1) := by linarith [hKa0]
    calc 20 * α * max K (4 / 3) * (z / (1 + z) ^ 2)
        = (20 * max K (4 / 3)) * (α * (z / (1 + z) ^ 2)) := by ring
      _ ≤ (2400 * (max K (4 / 3) + 1)) * (α * (z / (1 + z) ^ 2)) :=
          mul_le_mul_of_nonneg_right hKb (mul_nonneg hα.le hzk)
      _ = 2400 * (max K (4 / 3) + 1) * α * z / (1 + z) ^ 2 := by ring

end Work.FTS.Nonlinear.Pieces.RNP
