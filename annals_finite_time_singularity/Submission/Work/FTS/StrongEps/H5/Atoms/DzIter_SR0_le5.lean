import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS.StrongEps.ClassCRHS.DzBoundR0
import Submission.Work.FTS.NonlinRows.AkRhoJetBasic
import Submission.Work.Elliptic.L12Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.H5.Atoms

open Work.FTS.StrongEps.ClassCRHS

/-! ## The level-`5` jet of the radial profile `SR0 z = 2z²/(1+z)³`

`AkRhoJetBasic.akJet4` computes the fourth `D_z`-iterate of `z ↦ 2z²/(1+z)³`; here we
differentiate it once more to obtain the fifth, and bound the result.  The constant is read
off from the coefficients of the numerator of the fifth iterate:

`D_z^5 SR0 = 2z²·(-z⁵ + 88z⁴ - 718z³ + 1208z² - 473z + 32)/(1+z)⁸`,
and `|z^k| ≤ (1+z)^5` for `z ≥ 0`, `k ≤ 5`, whence the numerator is dominated by
`2·2520·(1+z)^5 = 5040·(1+z)^5`, i.e. `|D_z^5 SR0| ≤ 5040·z²/(1+z)³`. -/

/-- The fifth `z∂_z`-iterate of the profile `z ↦ 2z²/(1+z)³`:
`D_z^5 (2z²/(1+z)³) = 2z²(-z⁵+88z⁴-718z³+1208z²-473z+32)/(1+z)^8`.

Obtained by differentiating the order-`4` formula `AkRhoJetBasic.akJet4`:
the derivative of `z²(2z⁴-82z³+342z²-262z+32)/(1+z)^7` is
`2z(-z⁵+88z⁴-718z³+1208z²-473z+32)/(1+z)^8`. -/
lemma SR0_akJet5 {z : ℝ} (hz : z ≠ -1) (θ : ℝ) :
    Work.Spaces.DzIter 5 (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z θ
      = 2 * z ^ 2 * (-z ^ 5 + 88 * z ^ 4 - 718 * z ^ 3 + 1208 * z ^ 2 - 473 * z + 32)
          / (1 + z) ^ 8 := by
  have hh : (1 : ℝ) + z ≠ 0 := by intro h; exact hz (by linarith)
  rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
  have hev : (fun z' : ℝ => Work.Spaces.DzIter 4 (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z' θ)
      =ᶠ[nhds z] fun z' : ℝ =>
          z' ^ 2 * (2 * z' ^ 4 - 82 * z' ^ 3 + 342 * z' ^ 2 - 262 * z' + 32) / (1 + z') ^ 7 := by
    filter_upwards [isOpen_ne.mem_nhds hz] with z' hz'
    exact Work.FTS.NonlinRows.AkRhoJetBasic.akJet4 hz' θ
  rw [hev.deriv_eq]
  have hd : HasDerivAt
      (fun z' : ℝ => z' ^ 2 * (2 * z' ^ 4 - 82 * z' ^ 3 + 342 * z' ^ 2 - 262 * z' + 32)
        / (1 + z') ^ 7)
      (2 * z * (-z ^ 5 + 88 * z ^ 4 - 718 * z ^ 3 + 1208 * z ^ 2 - 473 * z + 32)
        / (1 + z) ^ 8) z := by
    have hA : HasDerivAt (fun y : ℝ => 2 * y ^ 4) (2 * (4 * z ^ (4 - 1))) z :=
      (hasDerivAt_pow 4 z).const_mul 2
    have hB : HasDerivAt (fun y : ℝ => 82 * y ^ 3) (82 * (3 * z ^ (3 - 1))) z :=
      (hasDerivAt_pow 3 z).const_mul 82
    have hC : HasDerivAt (fun y : ℝ => 342 * y ^ 2) (342 * (2 * z ^ (2 - 1))) z :=
      (hasDerivAt_pow 2 z).const_mul 342
    have hD : HasDerivAt (fun y : ℝ => 262 * y) (262 * 1) z := by
      simpa using (hasDerivAt_id z).const_mul (262 : ℝ)
    have hq : HasDerivAt (fun y : ℝ => 2 * y ^ 4 - 82 * y ^ 3 + 342 * y ^ 2 - 262 * y + 32)
        (8 * z ^ 3 - 246 * z ^ 2 + 684 * z - 262) z := by
      have hc := (((hA.sub hB).add hC).sub hD).add_const 32
      convert hc using 1
      ring
    have hp : HasDerivAt (fun y : ℝ => y ^ 2) (2 * z) z := by
      simpa using hasDerivAt_pow 2 z
    have h1 : HasDerivAt
        (fun z' : ℝ => z' ^ 2 * (2 * z' ^ 4 - 82 * z' ^ 3 + 342 * z' ^ 2 - 262 * z' + 32))
        (12 * z ^ 5 - 410 * z ^ 4 + 1368 * z ^ 3 - 786 * z ^ 2 + 64 * z) z := by
      have h' := hp.mul hq
      convert h' using 1
      ring
    have h2 : HasDerivAt (fun z' : ℝ => (1 + z') ^ 7) (7 * (1 + z) ^ 6) z := by
      simpa using Work.FTS.NonlinRows.AkRhoJetBasic.hasDerivAt_one_add_pow 7 z
    have h3 : (1 + z) ^ 7 ≠ 0 := pow_ne_zero 7 hh
    have hdd := h1.div h2 h3
    convert hdd using 1
    · field_simp
      ring
  rw [hd.deriv]
  ring

/-- The numerator of the fifth iterate is dominated by `2520·(1+z)^5` for `z ≥ 0`
(the coefficient `ℓ¹`-norm of `-z⁵+88z⁴-718z³+1208z²-473z+32` is `2520`). -/
lemma SR0_num_le (z : ℝ) (hz : 0 ≤ z) :
    |(-z ^ 5 + 88 * z ^ 4 - 718 * z ^ 3 + 1208 * z ^ 2 - 473 * z + 32)|
      ≤ 2520 * (1 + z) ^ 5 := by
  have hzp : (1 : ℝ) ≤ 1 + z := by linarith
  have hzle : z ≤ 1 + z := by linarith
  have h5 : z ^ 5 ≤ (1 + z) ^ 5 := pow_le_pow_left₀ hz hzle 5
  have h4 : (1 + z) ^ 4 ≤ (1 + z) ^ 5 := pow_le_pow_right₀ hzp (by norm_num)
  have h3 : (1 + z) ^ 3 ≤ (1 + z) ^ 5 := pow_le_pow_right₀ hzp (by norm_num)
  have h2 : (1 + z) ^ 2 ≤ (1 + z) ^ 5 := pow_le_pow_right₀ hzp (by norm_num)
  have hone : (1 : ℝ) ≤ (1 + z) ^ 5 := one_le_pow₀ hzp
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg z, pow_nonneg hz 3, pow_nonneg hz 4, pow_nonneg hz 5]

/-- The quotient form of the level-`5` bound: a numerator dominated by `2520·(1+z)^5`
gives `|2z²·Q/(1+z)^8| ≤ 5040·z²/(1+z)³`. -/
lemma SR0_quot_le {z Q : ℝ} (hz : 0 ≤ z) (hQ : |Q| ≤ 2520 * (1 + z) ^ 5) :
    |2 * z ^ 2 * Q / (1 + z) ^ 8| ≤ 5040 * z ^ 2 / (1 + z) ^ 3 := by
  have hden8 : (0 : ℝ) < (1 + z) ^ 8 := by positivity
  have hden3 : (0 : ℝ) < (1 + z) ^ 3 := by positivity
  have hnum : |2 * z ^ 2 * Q| ≤ 5040 * z ^ 2 * (1 + z) ^ 5 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg (sq_nonneg z)]
    nlinarith [hQ, sq_nonneg z, pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + z) 5]
  rw [abs_div, abs_of_pos hden8]
  rw [div_le_div_iff₀ hden8 hden3]
  calc |2 * z ^ 2 * Q| * (1 + z) ^ 3
      ≤ (5040 * z ^ 2 * (1 + z) ^ 5) * (1 + z) ^ 3 :=
        mul_le_mul_of_nonneg_right hnum (by positivity)
    _ = 5040 * z ^ 2 * (1 + z) ^ 8 := by ring

/-- The `i = 5` case of the radial bound: `|D_z^5 SR0 z| ≤ 5040·z²/(1+z)³` for `z ≥ 0`. -/
lemma SR0_DzdIter_five_bound (z : ℝ) (hz : 0 ≤ z) :
    |Work.Elliptic.DzdIter 5 SR0 z| ≤ 5040 * z ^ 2 / (1 + z) ^ 3 := by
  have hz1 : z ≠ -1 := by linarith
  rw [← Work.Elliptic.DzIter_rad SR0 5 z 0]
  change |Work.Spaces.DzIter 5 (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z 0|
      ≤ 5040 * z ^ 2 / (1 + z) ^ 3
  rw [SR0_akJet5 hz1 0]
  exact SR0_quot_le hz (SR0_num_le z hz)

/-- The level-`5` radial iterates of `SR0 z = 2z²/(1+z)³` are bounded by `C·z²/(1+z)³`:
`D_z^i SR0 = z²·P_i(z)/(1+z)^(3+i)` with `deg P_i = i`, so `|D_z^i SR0 z| ≤ (Σ|c|)·z²/(1+z)³`.
(The level-`4` version with `C = 720` is `ClassCRHS.DzBoundR0`; this adds the `i = 5` case,
where `D_z^5 SR0 = z²(-z^5 + 88z^4 - 718z^3 + 1208z^2 - 473z + 32)·2/(1+z)^8`.) -/
theorem DzIter_SR0_le5 : ∃ C : ℝ, 0 < C ∧ ∀ i : ℕ, i ≤ 5 → ∀ z : ℝ, 0 ≤ z →
    |Work.Elliptic.DzdIter i Work.FTS.StrongEps.ClassCRHS.SR0 z| ≤ C * z ^ 2 / (1 + z) ^ 3 := by
  obtain ⟨C₀, hC₀, hb₀⟩ := Work.FTS.StrongEps.ClassCRHS.DzBoundR0
  refine ⟨max C₀ 5040, lt_max_of_lt_left hC₀, fun i hi z hz => ?_⟩
  have h1 : (0 : ℝ) < 1 + z := by linarith
  have hden : (0 : ℝ) ≤ (1 + z) ^ 3 := by positivity
  have hz2 : (0 : ℝ) ≤ z ^ 2 := sq_nonneg z
  by_cases h4 : i ≤ 4
  · exact le_trans (hb₀ i h4 z hz)
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left C₀ 5040) hz2) hden)
  · have hi5 : i = 5 := by omega
    rw [hi5]
    exact le_trans (SR0_DzdIter_five_bound z hz)
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right C₀ 5040) hz2) hden)

end Work.FTS.StrongEps.H5.Atoms
