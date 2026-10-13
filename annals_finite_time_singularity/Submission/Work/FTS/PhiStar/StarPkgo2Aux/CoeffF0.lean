/-
# `FTS/PhiStar/StarPkgo2Aux/CoeffF0.lean` — the six coefficient functions are in `F0 6`

`Work.FTS.PhiStar.F0 n K f` (see `CoreAux/Defs.lean`) says that on the open quadrant
`Q0 = (0,∞) × (0,π/2)` all the mixed weighted derivatives

    (z+1)^k · ∂_z^k D_θ^i f ,     k + i ≤ n ,

are bounded by `K`.  This file produces **one** constant `A ≥ 1` which works simultaneously
for the four angular coefficients of the `StarPkgo2` assembly

    sin²θ ,   cos²θ - 2 sin²θ ,   cos 2θ ,   sin 2θ

and for the two radial coefficients

    z/(1+z) ,   (1+z)⁻¹ .

**The angular half** is `Work.FTS.PhiStar.CoreAux.F0_theta_coefs 6`: those four functions
depend on `θ` only, all their radial derivatives vanish, and the finitely many angular
iterates `dthU^[i] f` (`i ≤ 6`) are continuous on the compact interval `Iθ`.

**The radial half** is done here.  A function `f z θ = c z` of `z` alone has
`D_θ^i f = 0` for `i ≥ 1` (`DthIter_eq_zero_of_theta_indep`), and by
`Work.Spaces.pzIter_eq_iteratedDeriv` the remaining slots are

    (z+1)^k · ∂_z^k c z ,     k ≤ 6 .

For the two coefficients these are computed exactly:

* `(1+z)⁻¹`: the `k`-th derivative is `(-1)^k k! (1+z)^{-(k+1)}`
  (`iteratedDeriv_inv_one_add`), so the weighted slot is `± k! /(1+z)`, of modulus at most
  `k!` ≤ `720` (`weighted_iteratedDeriv_inv`);
* `z/(1+z) = 1 - (1+z)⁻¹` for `z ≠ -1`: for `k ≥ 1` the constant `1` drops out
  (`iteratedDeriv_const_sub` on the open set `Ioi (-1)`, `weighted_iteratedDeriv_div`), and
  for `k = 0` the slot is `z/(1+z) ∈ [0,1]`.

The two `k = 0` boundary cases are what the constant `720` is chosen for; the same `720`
bounds both radial coefficients, and it is added to the angular constant.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.PhiStar.CoreAux.Defs
import Submission.Work.FTS.PhiStar.CoreAux.F0_theta_coefs
import Submission.Work.Spaces.pz_aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.StarPkgo2Aux

set_option autoImplicit false

/-! ## `θ`-independent data

For `f z θ = c z` the angular operator `D_θ = sin(2θ)∂_θ` kills everything from order one on,
and the radial part is the ordinary iterated derivative of `c`. -/

/-- The `D_θ`-iterate of the zero function is again zero. -/
theorem Dth_zero_fun : Work.Spaces.Dth (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  funext z θ
  simp [Work.Spaces.Dth, Work.Spaces.pth]

/-- **`D_θ^{i+1}` of a `θ`-independent function vanishes identically.**

The `θ`-slice of such a function is constant, so its derivative is `0`; from the second
order on the function is already zero, so all further `D_θ`-iterates vanish too. -/
theorem DthIter_succ_eq_zero_of_theta_indep {f : ℝ → ℝ → ℝ}
    (hf : ∀ z θ θ', f z θ = f z θ') (i : ℕ) :
    Work.Spaces.DthIter (i + 1) f = fun _ _ => 0 := by
  induction i with
  | zero =>
    funext z θ
    simp only [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero]
    rw [Work.Spaces.Dth, Work.Spaces.pth]
    rw [show (fun θ' => f z θ') = fun _ => f z 0 from funext (fun θ' => hf z θ' 0),
      deriv_const, mul_zero]
  | succ i ih =>
    rw [Work.Spaces.DthIter_succ, ih, Dth_zero_fun]

/-- **`D_θ^i` of a `θ`-independent function vanishes** for `i ≥ 1`. -/
theorem DthIter_eq_zero_of_theta_indep {f : ℝ → ℝ → ℝ}
    (hf : ∀ z θ θ', f z θ = f z θ') {i : ℕ} (hi : 1 ≤ i) :
    Work.Spaces.DthIter i f = fun _ _ => 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  exact DthIter_succ_eq_zero_of_theta_indep hf j

/-- Every `z`-iterate of the zero function vanishes. -/
theorem pzIter_zero_fun (k : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter k (fun _ _ : ℝ => (0 : ℝ)) z θ = 0 := by
  rw [Work.Spaces.pzIter_eq_iteratedDeriv k (fun _ _ : ℝ => (0 : ℝ)) z θ]
  exact Work.Spaces.iteratedDeriv_zero_fun k z

/-- **A `z`-only coefficient belongs to the flat class as soon as its weighted iterated
derivatives are bounded.**

If `|(z+1)^k ∂_z^k c z| ≤ A` for all `k ≤ n` and `z > 0`, then
`F0 n A (fun z _ => c z)`: the slots with an angular derivative vanish, and the purely radial
slots are the weighted iterated derivatives of `c`. -/
theorem F0_of_iteratedDeriv_bound {n : ℕ} {A : ℝ} {c : ℝ → ℝ}
    (hc : ∀ k ≤ n, ∀ z : ℝ, 0 < z → |(z+1)^k * iteratedDeriv k c z| ≤ A) :
    Work.FTS.PhiStar.F0 n A (fun z _ => c z) := by
  intro k i hki z θ hz hθ hθ'
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · subst hi0
    rw [Work.Spaces.DthIter_zero, Work.Spaces.pzIter_eq_iteratedDeriv k (fun z _ => c z) z θ]
    exact hc k hki z hz
  · rw [DthIter_eq_zero_of_theta_indep (f := fun z _ => c z) (fun z θ θ' => rfl) hipos,
        pzIter_zero_fun, mul_zero, abs_zero]
    exact le_trans (abs_nonneg _) (hc 0 (Nat.zero_le n) z hz)

/-! ## The two radial coefficients -/

/-- **The `k`-th derivative of `(1+z)⁻¹`.**

On `(-1,∞)`, `∂_z^k (1+z)⁻¹ = (-1)^k k! (1+z)^{-(k+1)}`.  The proof is an induction on `k`:
the induction hypothesis identifies the `k`-th derivative near `z` with the explicit
expression (`Filter.EventuallyEq.iteratedDeriv`), whose derivative is computed by the chain
rule (`HasDerivAt.inv`, `HasDerivAt.fun_pow`). -/
theorem iteratedDeriv_inv_one_add (k : ℕ) :
    ∀ z : ℝ, -1 < z →
      iteratedDeriv k (fun z : ℝ => (1 + z)⁻¹) z
        = (-1 : ℝ) ^ k * (k.factorial : ℝ) * ((1 + z)⁻¹) ^ (k + 1) := by
  induction k with
  | zero => intro z _; simp
  | succ k ih =>
    intro z hz
    have hne : (1 : ℝ) + z ≠ 0 := by linarith
    rw [iteratedDeriv_succ]
    have hcongr : iteratedDeriv k (fun y : ℝ => (1 + y)⁻¹) =ᶠ[𝓝 z]
        (fun y : ℝ => (-1 : ℝ) ^ k * (k.factorial : ℝ) * ((1 + y)⁻¹) ^ (k + 1)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
      exact ih y hy
    rw [hcongr.deriv_eq]
    have h1 : HasDerivAt (fun y : ℝ => (1 + y)⁻¹) (-(((1 : ℝ) + z)⁻¹) ^ 2) z := by
      have h2 : HasDerivAt (fun y : ℝ => (1 : ℝ) + y) 1 z := by
        simpa using (hasDerivAt_id z).const_add (1 : ℝ)
      have h3 : HasDerivAt (fun y : ℝ => ((1 : ℝ) + y)⁻¹) (-(((1 + z) ^ 2)⁻¹) * 1) z :=
        (hasDerivAt_inv hne).comp z h2
      simpa [mul_one, inv_pow] using h3
    have h4 : HasDerivAt (fun y : ℝ => ((1 + y)⁻¹) ^ (k + 1))
        (((k : ℝ) + 1) * ((1 + z)⁻¹) ^ k * (-(((1 + z)⁻¹) ^ 2))) z := by
      have := h1.fun_pow (k + 1)
      simpa using this
    have h5 := h4.const_mul ((-1 : ℝ) ^ k * (k.factorial : ℝ))
    rw [h5.deriv]
    have hpow : ((k : ℝ) + 1) * ((1 + z)⁻¹) ^ k * (-(((1 + z)⁻¹) ^ 2))
        = -(((k : ℝ) + 1) * ((1 + z)⁻¹) ^ (k + 2)) := by
      have hA : ((k : ℝ) + 1) * ((1 + z)⁻¹) ^ k * (-(((1 + z)⁻¹) ^ 2))
          = -(((k : ℝ) + 1) * (((1 + z)⁻¹) ^ k * ((1 + z)⁻¹) ^ 2)) := by ring
      rw [hA, ← pow_add]
    rw [hpow]
    have hfac : (((k + 1).factorial : ℕ) : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hneg : (-1 : ℝ) ^ (k + 1) = (-1 : ℝ) ^ k * (-1) := by rw [pow_succ]
    rw [hneg, hfac]
    ring

/-- **The weighted inverse power.**  For `z > -1` and every `k`,
`(z+1)^k (1+z)^{-(k+1)} = (1+z)⁻¹`. -/
theorem weighted_inv (k : ℕ) (z : ℝ) (hz : -1 < z) :
    (z + 1) ^ k * (((1 + z)⁻¹) ^ (k + 1)) = (1 + z)⁻¹ := by
  have h1 : z + 1 = 1 + z := by ring
  rw [h1]
  have hne : (1 : ℝ) + z ≠ 0 := by linarith
  have hk : ((1 : ℝ) + z) ^ k ≠ 0 := pow_ne_zero k hne
  rw [inv_pow, pow_succ, mul_inv, ← mul_assoc, mul_inv_cancel₀ hk, one_mul]

/-- **The weighted derivative slots of `(1+z)⁻¹`.**  They are all equal to `± k! /(1+z)`. -/
theorem weighted_iteratedDeriv_inv (k : ℕ) (z : ℝ) (hz : -1 < z) :
    (z + 1) ^ k * iteratedDeriv k (fun z : ℝ => (1 + z)⁻¹) z
      = (-1 : ℝ) ^ k * (k.factorial : ℝ) * (1 + z)⁻¹ := by
  rw [iteratedDeriv_inv_one_add k z hz]
  have hstep : (z + 1) ^ k * ((-1 : ℝ) ^ k * (k.factorial : ℝ) * (((1 + z)⁻¹) ^ (k + 1)))
      = (-1 : ℝ) ^ k * (k.factorial : ℝ) * ((z + 1) ^ k * (((1 + z)⁻¹) ^ (k + 1))) := by
    ring
  rw [hstep, weighted_inv k z hz]

/-- **The weighted derivative slots of `z/(1+z)`**, for `k ≥ 1`.

On `(-1,∞)` one has `z/(1+z) = 1 - (1+z)⁻¹`; the constant `1` has no derivatives of order
`≥ 1`, so the slots are minus those of `(1+z)⁻¹`. -/
theorem weighted_iteratedDeriv_div (k : ℕ) (hk : 1 ≤ k) (z : ℝ) (hz : -1 < z) :
    (z + 1) ^ k * iteratedDeriv k (fun z : ℝ => z / (1 + z)) z
      = (-1 : ℝ) ^ (k + 1) * (k.factorial : ℝ) * (1 + z)⁻¹ := by
  have heq : Set.EqOn (fun z : ℝ => z / (1 + z)) (fun z : ℝ => 1 - (1 + z)⁻¹)
      (Set.Ioi (-1)) := by
    intro y hy
    have hy' : (-1 : ℝ) < y := hy
    have hne : (1 : ℝ) + y ≠ 0 := by linarith
    field_simp
    ring
  rw [heq.iteratedDeriv_of_isOpen isOpen_Ioi k hz]
  rw [iteratedDeriv_const_sub (n := k) (by omega : 0 < k) (1 : ℝ)]
  simp only [iteratedDeriv_neg]
  rw [iteratedDeriv_inv_one_add k z hz]
  have hstep : (z + 1) ^ k * (-((-1 : ℝ) ^ k * (k.factorial : ℝ) * (((1 + z)⁻¹) ^ (k + 1))))
      = -((-1 : ℝ) ^ k * (k.factorial : ℝ) * ((z + 1) ^ k * (((1 + z)⁻¹) ^ (k + 1)))) := by
    ring
  rw [hstep, weighted_inv k z hz, pow_succ]
  ring

/-! ## The two radial coefficients are in `F0 6`, with the common constant `720` -/

/-- `(1+z)⁻¹ ∈ F0 6` with the universal constant `720` (`= 6!`). -/
theorem F0_inv_one_add : Work.FTS.PhiStar.F0 6 720 (fun z _ => (1 + z)⁻¹) := by
  apply F0_of_iteratedDeriv_bound
  intro k hk z hz
  have hz' : -1 < z := by linarith
  rw [weighted_iteratedDeriv_inv k z hz']
  have hHpos : 0 < (1 + z)⁻¹ := by positivity
  have hHle : (1 + z)⁻¹ ≤ 1 := by
    have h1z : (1 : ℝ) ≤ 1 + z := by linarith
    exact inv_le_one_of_one_le₀ h1z
  have habs : |(-1 : ℝ) ^ k * (k.factorial : ℝ) * (1 + z)⁻¹|
      = (k.factorial : ℝ) * (1 + z)⁻¹ := by
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k.factorial : ℝ)), abs_of_nonneg hHpos.le]
  rw [habs]
  have hfac : (k.factorial : ℝ) ≤ 720 := by interval_cases k <;> norm_num
  calc (k.factorial : ℝ) * (1 + z)⁻¹ ≤ 720 * 1 :=
        mul_le_mul hfac hHle hHpos.le (by norm_num)
    _ = 720 := by norm_num

/-- `z/(1+z) ∈ F0 6` with the universal constant `720` (`= 6!`); the slot `k = 0` is
`z/(1+z) ∈ [0,1]` for `z > 0`. -/
theorem F0_div_one_add : Work.FTS.PhiStar.F0 6 720 (fun z _ => z / (1 + z)) := by
  apply F0_of_iteratedDeriv_bound
  intro k hk z hz
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    simp only [pow_zero, one_mul, iteratedDeriv_zero]
    have h1z : 0 < 1 + z := by linarith
    have hle : z / (1 + z) ≤ 1 := by
      rw [div_le_one h1z]; linarith
    have hge : 0 ≤ z / (1 + z) := div_nonneg hz.le h1z.le
    rw [abs_of_nonneg hge]
    linarith
  · rw [weighted_iteratedDeriv_div k hkpos z (by linarith)]
    have hHpos : 0 < (1 + z)⁻¹ := by positivity
    have hHle : (1 + z)⁻¹ ≤ 1 := by
      have h1z : (1 : ℝ) ≤ 1 + z := by linarith
      exact inv_le_one_of_one_le₀ h1z
    have habs : |(-1 : ℝ) ^ (k + 1) * (k.factorial : ℝ) * (1 + z)⁻¹|
        = (k.factorial : ℝ) * (1 + z)⁻¹ := by
      rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k.factorial : ℝ)), abs_of_nonneg hHpos.le]
    rw [habs]
    have hfac : (k.factorial : ℝ) ≤ 720 := by interval_cases k <;> norm_num
    calc (k.factorial : ℝ) * (1 + z)⁻¹ ≤ 720 * 1 :=
          mul_le_mul hfac hHle hHpos.le (by norm_num)
      _ = 720 := by norm_num

/-! ## The assembly -/

/-- **All six coefficient functions of the `StarPkgo2` assembly lie in `F0 6` for a single
constant `A ≥ 1`.**  The four angular coefficients come from
`CoreAux.F0_theta_coefs 6` (constant `C > 0`), the two radial ones from `F0_div_one_add` and
`F0_inv_one_add` (constant `720`), and `A = C + 720 + 1` dominates both. -/
theorem CoeffF0 : ∃ A : ℝ, 1 ≤ A ∧
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.sin θ ^ 2) ∧
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) ∧
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.cos (2 * θ)) ∧
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.sin (2 * θ)) ∧
    Work.FTS.PhiStar.F0 6 A (fun z _ => z / (1 + z)) ∧
    Work.FTS.PhiStar.F0 6 A (fun z _ => (1 + z)⁻¹) := by
  obtain ⟨C, hCpos, h1, h2, h3, h4⟩ := Work.FTS.PhiStar.CoreAux.F0_theta_coefs 6
  refine ⟨C + 720 + 1, by linarith, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) h1
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) h2
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) h3
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) h4
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) F0_div_one_add
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) F0_inv_one_add

end Work.FTS.PhiStar.StarPkgo2Aux
