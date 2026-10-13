/-
Copyright: work module for the Elgindi finite-time singularity project.

# The "pure slot" of the nonlinear rows: `D_z^i (f · ∂_θ g)`

The rows of §8 of Elgindi's paper contain products `f · ∂_θ g` in which the *whole* weight of
the coefficient `f` sits in the **radial** (`D_z`) slots of the nonlinearity, i.e. the term is
`D_z^i (f · ∂_θ g)` with `i ≤ 4` priced by the `η`-weight `w(z)/sin(2θ)^{η/2}`.  The estimate
proved here is the pointwise one:

  `(D_z^i (f ∂_θ g)(z,θ) · w(z)/sin(2θ)^{η/2})² ≤ C · K² · HkIntegrand α 6 g (z,θ)`

on the open quadrant, for `i ≤ 4`, whenever

  `|D_z^b D_θ^a f(z,θ)| ≤ K · sin(2θ)`  for all `a + b ≤ 4`

(the natural `𝒲^{4,∞}`-type hypothesis on the coefficient, stated directly on the mixed
derivatives).  The mechanism is one line of mathematics:

* Leibniz (`Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz`):
  `D_z^i (f·∂_θ g) = ∑_{b} C(i,b) · D_z^b f · D_z^{i-b}(∂_θ g)`;
* each `D_z^b f` costs a factor `sin(2θ)`, which is exactly what converts the "unweighted"
  angular derivative `D_z^{i-b}(∂_θ g)` into the weighted mixed slot
  `mixed (i-b) 1 g = D_z^{i-b} (sin(2θ) ∂_θ g)` (`Work.FTS.H2.sin_mul_dzIter_pth`);
* the surviving slots are single summands of `HkIntegrand α 6 g`
  (`Work.Spaces.sq_le_HkIntegrand_mixed`), and the `η`-weight is dominated by the
  `γ`-weight of the mixed slots since `η ≤ γ`.

Everything is pointwise: no integrability hypothesis on `g` is needed, only `C^∞` on the open
quadrant.
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows

set_option maxHeartbeats 1000000

/-! ## The weight comparison -/

/-- On the open quadrant the `η`-weight `w z / sin(2θ)^{η/2}` of the pure radial slots is
dominated by the `γ`-weight `Wt α z θ = w z · sin(2θ)^{-γ/2}` of the mixed slots: indeed
`0 < sin(2θ) ≤ 1` and `η ≤ γ` (for `α > 0`). -/
theorem w_div_sin_eta_le_Wt {α z θ : ℝ} (hα : 0 < α)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
      ≤ Work.Spaces.Wt α z θ := by
  have hSpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hSle1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hyz : -(Work.Spaces.gam α / 2) ≤ -(Work.Spaces.eta / 2) := by
    rw [Work.Spaces.gam, Work.Spaces.eta]
    linarith
  have hrpow : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))
      ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) :=
    Real.rpow_le_rpow_of_exponent_ge hSpos hSle1 hyz
  have hwnn : 0 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w]
    exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, div_eq_mul_inv,
    ← Real.rpow_neg (le_of_lt hSpos) (Work.Spaces.eta / 2)]
  exact mul_le_mul_of_nonneg_left hrpow hwnn

/-! ## The pointwise estimate -/

/-- The pure-slot estimate with the explicit constant `10^4`. -/
theorem pure_slot_mul_pth_le_main :
    ∀ (α : ℝ), 0 < α → ∀ (f g : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.EllipticEst.SmoothOpen g →
      ∀ (K : ℝ), 0 < K →
      (∀ (z : ℝ), 0 < z → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ b a : ℕ, a + b ≤ 4 →
        |Work.Spaces.mixed b a f z θ| ≤ K * Real.sin (2 * θ)) →
      ∀ (i : ℕ), i ≤ 4 → ∀ (z : ℝ) (θ : ℝ), 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
        (Work.Spaces.DzIter i (fun z θ => f z θ * Work.Spaces.pth g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ (10 : ℝ) ^ 4 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ := by
  intro α hα f g hf hg K hK hKb i hi z θ hz hθ
  have hSpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  set X : ℝ := Work.Spaces.DzIter i (fun z θ => f z θ * Work.Spaces.pth g z θ) z θ
    with hXdef
  set wz : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hwzdef
  set H : ℝ := Work.Spaces.HkIntegrand α 6 g z θ with hHdef
  have hHnn : 0 ≤ H := by rw [hHdef]; exact Work.Spaces.HkIntegrand_nonneg α 6 g z θ
  have hwznn : 0 ≤ wz := by
    rw [hwzdef]
    exact div_nonneg
      (by rw [Work.Spaces.w]; exact div_nonneg (sq_nonneg _) (sq_nonneg _))
      (Real.rpow_nonneg hSpos.le _)
  have hwzle : wz ≤ Work.Spaces.Wt α z θ := by
    rw [hwzdef]
    exact w_div_sin_eta_le_Wt hα hθ
  -- Leibniz for `D_z^i` on the open quadrant
  have hX : X = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) *
      (Work.Spaces.DzIter b f z θ * Work.Spaces.DzIter (i - b) (Work.Spaces.pth g) z θ) := by
    rw [hXdef]
    exact Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz i f (Work.Spaces.pth g) hf
      (Work.FTS.EllipticEst.SmoothOpen.pth hg) z θ hz hθ.1 hθ.2
  -- the per-term bound: one factor `sin(2θ)` coming from `f` converts `∂_θ g` into the slot
  -- `mixed (i-b) 1 g = D_z^{i-b}(sin(2θ) ∂_θ g)`
  have hterm : ∀ b ∈ Finset.range (i + 1),
      |Work.Spaces.DzIter b f z θ * Work.Spaces.DzIter (i - b) (Work.Spaces.pth g) z θ|
        ≤ K * |Work.Spaces.mixed (i - b) 1 g z θ| := by
    intro b hb
    have hbi : b ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hfb : |Work.Spaces.DzIter b f z θ| ≤ K * Real.sin (2 * θ) := by
      have h0 := hKb z hz θ hθ b 0 (by omega)
      simpa only [Work.Spaces.mixed_zero_right] using h0
    have h1 : Real.sin (2 * θ) * |Work.Spaces.DzIter (i - b) (Work.Spaces.pth g) z θ|
        = |Work.Spaces.mixed (i - b) 1 g z θ| := by
      have h2 : |Real.sin (2 * θ) * Work.Spaces.DzIter (i - b) (Work.Spaces.pth g) z θ|
          = |Work.Spaces.mixed (i - b) 1 g z θ| := by
        rw [Work.FTS.H2.sin_mul_dzIter_pth g (i - b) z θ]
      rwa [abs_mul, abs_of_pos hSpos] at h2
    have hY : |Work.Spaces.DzIter (i - b) (Work.Spaces.pth g) z θ|
        = |Work.Spaces.mixed (i - b) 1 g z θ| / Real.sin (2 * θ) :=
      (eq_div_iff (ne_of_gt hSpos)).mpr (by rw [mul_comm]; exact h1)
    rw [abs_mul, hY]
    calc |Work.Spaces.DzIter b f z θ| * (|Work.Spaces.mixed (i - b) 1 g z θ| / Real.sin (2 * θ))
        ≤ (K * Real.sin (2 * θ))
            * (|Work.Spaces.mixed (i - b) 1 g z θ| / Real.sin (2 * θ)) :=
          mul_le_mul_of_nonneg_right hfb (div_nonneg (abs_nonneg _) hSpos.le)
      _ = K * |Work.Spaces.mixed (i - b) 1 g z θ| := by
          field_simp
  have hsumX : |X| ≤ ∑ b ∈ Finset.range (i + 1),
      (i.choose b : ℝ) * (K * |Work.Spaces.mixed (i - b) 1 g z θ|) := by
    rw [hX]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
    intro b hb
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (i.choose b : ℝ))]
    exact mul_le_mul_of_nonneg_left (hterm b hb) (by positivity)
  have hsumX' : |X| ≤ K * ∑ b ∈ Finset.range (i + 1),
      ((i.choose b : ℝ) * |Work.Spaces.mixed (i - b) 1 g z θ|) := by
    refine hsumX.trans ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun b _ => le_of_eq (by ring))
  have hSumnn : 0 ≤ ∑ b ∈ Finset.range (i + 1),
      ((i.choose b : ℝ) * |Work.Spaces.mixed (i - b) 1 g z θ|) :=
    Finset.sum_nonneg fun b _ => mul_nonneg (by positivity) (abs_nonneg _)
  -- multiply by the weight `wz ≤ Wt` and collect the `HkIntegrand` slots
  have hA : |X * wz| ≤ K * ∑ b ∈ Finset.range (i + 1),
      ((i.choose b : ℝ) * |Work.Spaces.mixed (i - b) 1 g z θ| * Work.Spaces.Wt α z θ) := by
    rw [abs_mul, abs_of_nonneg hwznn]
    calc |X| * wz
        ≤ (K * ∑ b ∈ Finset.range (i + 1),
            ((i.choose b : ℝ) * |Work.Spaces.mixed (i - b) 1 g z θ|)) * wz :=
          mul_le_mul_of_nonneg_right hsumX' hwznn
      _ ≤ (K * ∑ b ∈ Finset.range (i + 1),
            ((i.choose b : ℝ) * |Work.Spaces.mixed (i - b) 1 g z θ|))
            * Work.Spaces.Wt α z θ :=
          mul_le_mul_of_nonneg_left hwzle (mul_nonneg hK.le hSumnn)
      _ = K * ∑ b ∈ Finset.range (i + 1),
            ((i.choose b : ℝ) * |Work.Spaces.mixed (i - b) 1 g z θ| * Work.Spaces.Wt α z θ) := by
          rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
  -- each single slot is a summand of `HkIntegrand α 6 g`
  have hper : ∀ b ∈ Finset.range (i + 1),
      ((i.choose b : ℝ) * |Work.Spaces.mixed (i - b) 1 g z θ| * Work.Spaces.Wt α z θ) ^ 2
        ≤ 256 * H := by
    intro b hb
    have hbi : b ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hch : ((i.choose b : ℝ)) ^ 2 ≤ 256 := by
      have h1 : i.choose b ≤ 2 ^ i := by
        have h := Finset.single_le_sum (f := fun k => i.choose k) (fun k _ => Nat.zero_le _)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hbi))
        rwa [Nat.sum_range_choose] at h
      have h2 : i.choose b ≤ 16 := by
        calc i.choose b ≤ 2 ^ i := h1
          _ ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) hi
          _ = 16 := by norm_num
      have h3 : (i.choose b : ℝ) ≤ 16 := by exact_mod_cast h2
      have h4 : (0 : ℝ) ≤ (i.choose b : ℝ) := by positivity
      nlinarith [h3, h4]
    have hslot : (|Work.Spaces.mixed (i - b) 1 g z θ| * Work.Spaces.Wt α z θ) ^ 2 ≤ H := by
      have h := Work.Spaces.sq_le_HkIntegrand_mixed α 6 g z θ 1 (i - b) le_rfl (by omega)
      rw [← hHdef] at h
      rw [show (|Work.Spaces.mixed (i - b) 1 g z θ| * Work.Spaces.Wt α z θ) ^ 2
          = (Work.Spaces.mixed (i - b) 1 g z θ * Work.Spaces.Wt α z θ) ^ 2 from by
            rw [mul_pow, sq_abs, mul_pow]]
      exact h
    calc ((i.choose b : ℝ) * |Work.Spaces.mixed (i - b) 1 g z θ| * Work.Spaces.Wt α z θ) ^ 2
        = ((i.choose b : ℝ)) ^ 2
            * (|Work.Spaces.mixed (i - b) 1 g z θ| * Work.Spaces.Wt α z θ) ^ 2 := by ring
      _ ≤ 256 * (|Work.Spaces.mixed (i - b) 1 g z θ| * Work.Spaces.Wt α z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right hch (sq_nonneg _)
      _ ≤ 256 * H := mul_le_mul_of_nonneg_left hslot (by norm_num)
  have hcard : (((Finset.range (i + 1)).card : ℕ) : ℝ) = (i : ℝ) + 1 := by
    rw [Finset.card_range]
    push_cast
    ring
  have hsum2 : ∑ b ∈ Finset.range (i + 1),
        ((i.choose b : ℝ) * |Work.Spaces.mixed (i - b) 1 g z θ| * Work.Spaces.Wt α z θ) ^ 2
      ≤ ((i : ℝ) + 1) * (256 * H) := by
    calc ∑ b ∈ Finset.range (i + 1),
          ((i.choose b : ℝ) * |Work.Spaces.mixed (i - b) 1 g z θ| * Work.Spaces.Wt α z θ) ^ 2
        ≤ ∑ b ∈ Finset.range (i + 1), 256 * H := Finset.sum_le_sum hper
      _ = ((Finset.range (i + 1)).card : ℝ) * (256 * H) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((i : ℝ) + 1) * (256 * H) := by rw [hcard]
  have hSum2 : (∑ b ∈ Finset.range (i + 1),
        ((i.choose b : ℝ) * |Work.Spaces.mixed (i - b) 1 g z θ| * Work.Spaces.Wt α z θ)) ^ 2
      ≤ ((i : ℝ) + 1) * (((i : ℝ) + 1) * (256 * H)) := by
    refine (sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
      (f := fun b : ℕ => (i.choose b : ℝ) * |Work.Spaces.mixed (i - b) 1 g z θ|
        * Work.Spaces.Wt α z θ)).trans ?_
    rw [hcard]
    exact mul_le_mul_of_nonneg_left hsum2 (by positivity)
  -- assemble
  have hsq : (X * wz) ^ 2 ≤ (K * ∑ b ∈ Finset.range (i + 1),
      ((i.choose b : ℝ) * |Work.Spaces.mixed (i - b) 1 g z θ| * Work.Spaces.Wt α z θ)) ^ 2 := by
    rw [← sq_abs (X * wz)]
    exact pow_le_pow_left₀ (abs_nonneg _) hA 2
  have h1nn : (0 : ℝ) ≤ (i : ℝ) + 1 := by positivity
  have hi5 : (i : ℝ) + 1 ≤ 5 := by
    exact_mod_cast (by omega : i + 1 ≤ 5)
  have hsqii : ((i : ℝ) + 1) * ((i : ℝ) + 1) ≤ 25 := by nlinarith [h1nn, hi5]
  calc (X * wz) ^ 2
      ≤ (K * ∑ b ∈ Finset.range (i + 1),
          ((i.choose b : ℝ) * |Work.Spaces.mixed (i - b) 1 g z θ| * Work.Spaces.Wt α z θ)) ^ 2 :=
        hsq
    _ = K ^ 2 * (∑ b ∈ Finset.range (i + 1),
          ((i.choose b : ℝ) * |Work.Spaces.mixed (i - b) 1 g z θ| * Work.Spaces.Wt α z θ)) ^ 2 := by
        ring
    _ ≤ K ^ 2 * (((i : ℝ) + 1) * (((i : ℝ) + 1) * (256 * H))) :=
        mul_le_mul_of_nonneg_left hSum2 (sq_nonneg K)
    _ ≤ (10 : ℝ) ^ 4 * K ^ 2 * H := by
        have h3 : K ^ 2 * (((i : ℝ) + 1) * (((i : ℝ) + 1) * (256 * H)))
            = 256 * (((i : ℝ) + 1) * ((i : ℝ) + 1)) * (K ^ 2 * H) := by ring
        rw [h3]
        have h4 : ((i : ℝ) + 1) * ((i : ℝ) + 1) * (K ^ 2 * H) ≤ 25 * (K ^ 2 * H) :=
          mul_le_mul_of_nonneg_right hsqii (mul_nonneg (sq_nonneg K) hHnn)
        have h5 := mul_le_mul_of_nonneg_left h4 (by norm_num : (0 : ℝ) ≤ 256)
        nlinarith [h5, hHnn, sq_nonneg K]

/-- **The pure slot of the nonlinear rows.**  For a coefficient `f` whose mixed derivatives of
order `≤ 4` are `O(sin 2θ)`, the pure radial slots `D_z^i (f ∂_θ g)`, `i ≤ 4`, weighted by
`w/sin(2θ)^{η/2}`, are controlled pointwise by the `ℋ⁶`-integrand of `g`. -/
theorem pure_slot_mul_pth_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → ∀ (f g : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.EllipticEst.SmoothOpen g →
      ∀ (K : ℝ), 0 < K →
      (∀ (z : ℝ), 0 < z → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ b a : ℕ, a + b ≤ 4 →
        |Work.Spaces.mixed b a f z θ| ≤ K * Real.sin (2 * θ)) →
      ∀ (i : ℕ), i ≤ 4 → ∀ (z : ℝ) (θ : ℝ), 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
        (Work.Spaces.DzIter i (fun z θ => f z θ * Work.Spaces.pth g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ C * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ :=
  ⟨(10 : ℝ) ^ 4, by norm_num, pure_slot_mul_pth_le_main⟩

end Work.FTS.NonlinRows
