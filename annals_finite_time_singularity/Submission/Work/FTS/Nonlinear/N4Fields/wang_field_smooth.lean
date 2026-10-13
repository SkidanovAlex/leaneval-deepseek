/-
# The `wang` field of `N4Norm`, with the missing regularity hypotheses

This file proves `Work.FTS.Nonlinear.N4Fields.wang_field_smooth` (design §3.3 / the `wang` field
of the `N4Norm` structure of `Submission/Work/FTS/Nonlinear/Interface.lean`):

for `0 < α ≤ α₂ ≤ 1`, an angular profile `a : ℝ → ℝ` which is `C^∞` at every point, bounded by
`B` on `Iθ = [0,π/2]`, with all its `D_θ`-iterates of order `1..4` bounded by `B·sin(2θ)` there,
and a `SmoothQuad` function `h ∈ 𝒲^{4,∞}`, the product `(z,θ) ↦ a θ · h z θ` is again in
`𝒲^{4,∞}` with `|a h|_{𝒲^{4,∞}} ≤ C B |h|_{𝒲^{4,∞}}`, `C` universal.

The proof is in three steps.

* **Auxiliary calculus.**  Because `a` depends on `θ` only, `∂_z^k (a h) = a · ∂_z^k h`
  (`pzIter_angular_mul`) and `D_θ^m (a(θ)) = Lop^[m] a` (`DthIter_const_snd`); the `θ`-only
  function `θ ↦ φ θ` has `pzIter c = 0` for `c ≥ 1` (`pzIter_const_snd`).
* **The two pointwise bounds.**
  * radial (`wang_radial_bound`): immediate from the factorisation and `WlInf_z_bound`;
  * mixed (`wang_mixed_bound`): the Leibniz expansion `sqm_pz_DthIter_mul_le_4` of the product
    with the `z`-independent factor `fun z θ => a θ` collapses (only `c = 0` survives), giving
    `|∂_z^k D_θ^j (a h)| ≤ 257 Σ_{m≤j} |Lop^[m] a| · |∂_z^k D_θ^{j-m} h|`; each summand is
    bounded by `B |h|_𝒲` using `factor_bound` and the elementary weight bounds
    `(α+s)s^{α/5}·s^{-α/5}/(α+s) ≤ 1` and `s·s^{-α/5}/(α+s) ≤ 1` (`s = sin 2θ`) — the latter,
    the delicate case `m = j`, from the concavity of `u ↦ u^{α/5}`.
* **Passage to the closed quadrant and assembly**: exactly the argument of
  `Work.FTS.Nonlinear.N4Fields.wmul_field` — the mixed summands carry the factor
  `sin(2θ)^{-α/5}/(α+sin 2θ)`, which *vanishes* at `θ = 0, π/2` for `α > 0`, and the radial ones
  are bounded there by `WlInf_z_bound`; the counting lemma `wlInf_of_pointwise_bounds` then gives
  membership and the norm bound `30 · 1285 · B · |h|_𝒲`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MeanInequalities
import Submission.Work.FTS.Nonlinear.Interface
import Submission.Work.FTS.Nonlinear.N4Fields.wlInf_of_pointwise_bounds
import Submission.Work.FTS.H2.prodW_interior_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.Nonlinear.N4Fields

set_option maxHeartbeats 1600000

/-! ## The angular profile as a function of `(z,θ)` -/

/-- `a` depends on `θ` only, so `∂_z` commutes with multiplication by `a θ`. -/
theorem pzIter_angular_mul (i : ℕ) (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pzIter i (fun z θ => a θ * f z θ)
      = fun z θ => a θ * Work.Spaces.pzIter i f z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Work.Spaces.pzIter_succ, ih, Work.Spaces.pzIter_succ]
    funext z θ
    show deriv (fun z' => a θ * Work.Spaces.pzIter i f z' θ) z
      = a θ * deriv (fun z' => Work.Spaces.pzIter i f z' θ) z
    rw [deriv_const_mul_field]

/-- A function of `θ` alone has no `z`-derivatives: `∂_z^c (θ ↦ φ θ)` is `φ` for `c = 0` and
`0` otherwise. -/
theorem pzIter_const_snd (c : ℕ) (φ : ℝ → ℝ) :
    Work.Spaces.pzIter c (fun _ θ : ℝ => φ θ) = fun _ θ => if c = 0 then φ θ else 0 := by
  induction c with
  | zero => funext z θ; simp
  | succ c ih =>
    funext z θ
    rw [Work.Spaces.pzIter_succ, ih, Work.Spaces.pz]
    simp

/-- `D_θ^m` applied to a function of `θ` alone is the `m`-th iterate of `Lop`. -/
theorem DthIter_const_snd (m : ℕ) (a : ℝ → ℝ) :
    Work.Spaces.DthIter m (fun _ θ : ℝ => a θ) = fun _ θ => Work.Spaces.Lop^[m] a θ := by
  funext z θ
  rw [Work.Spaces.DthIter_eq_iterate_Lop]

/-- Pointwise form of `DthIter_const_snd`. -/
theorem DthIter_const_snd_apply (m : ℕ) (a : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DthIter m (fun _ θ' : ℝ => a θ') z θ = Work.Spaces.Lop^[m] a θ := by
  rw [DthIter_const_snd m a]

/-- Combination of the two previous auxiliaries. -/
theorem pzIter_DthIter_const_snd (c m : ℕ) (a : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pzIter c (Work.Spaces.DthIter m (fun _ θ' : ℝ => a θ')) z θ
      = if c = 0 then Work.Spaces.Lop^[m] a θ else 0 := by
  rw [DthIter_const_snd m a, pzIter_const_snd c (Work.Spaces.Lop^[m] a)]

/-! ## Two elementary weighted bounds for the angular factor -/

/-- The concavity of `u ↦ u^q`, `q ∈ [0,1]`: `u^q ≤ 1 + q u` (weighted AM–GM at `(u,1)`). -/
theorem rpow_le_one_add_mul {q u : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hu : 0 ≤ u) :
    u ^ q ≤ 1 + q * u := by
  have h2 : q + (1 - q) = 1 := by ring
  have h := Real.geom_mean_le_arith_mean2_weighted hq0 (by linarith : 0 ≤ 1 - q) hu
    (by norm_num : (0:ℝ) ≤ 1) h2
  rw [Real.one_rpow, mul_one] at h
  linarith

/-- The delicate weight bound of the case `m = j`: for `0 ≤ α ≤ 5` and `s ≥ 0`,
`s · s^{-α/5}/(α+s) ≤ 1`.  (Substituting `u = 1/s`, this is `u^{α/5} ≤ 1 + (α/5)u`, i.e. the
concavity bound above.) -/
theorem sin_mul_rpow_neg_div_le_one {α s : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 5) (hs : 0 ≤ s) :
    s * (s ^ (-(α / 5)) / (α + s)) ≤ 1 := by
  rcases eq_or_lt_of_le hs with h | h
  · subst h; simp
  · have hq0 : (0:ℝ) ≤ α/5 := by linarith
    have hq1 : α/5 ≤ 1 := by linarith
    have hs' : (0:ℝ) < s := h
    have hmain : s * s ^ (-(α/5)) ≤ α + s := by
      have h2 : s * s ^ (-(α/5)) = s * (s⁻¹) ^ (α/5) := by
        rw [Real.inv_rpow (le_of_lt hs') (α/5), Real.rpow_neg (le_of_lt hs') (α/5)]
      rw [h2]
      have h3 : s * (s⁻¹) ^ (α/5) ≤ s * (1 + (α/5) * s⁻¹) :=
        mul_le_mul_of_nonneg_left (rpow_le_one_add_mul hq0 hq1 (inv_nonneg.mpr (le_of_lt hs')))
          (le_of_lt hs')
      have h4 : s * (1 + (α/5) * s⁻¹) = s + α/5 := by field_simp
      linarith [h3, h4.le]
    rw [← mul_div_assoc, div_le_one (by linarith : (0:ℝ) < α + s)]
    exact hmain

/-- The main weight cancellation: `((α+s)s^{α/5}) · s^{-α/5}/(α+s) = s^{α/5}s^{-α/5} ≤ 1`. -/
theorem weight_mul_div_le_one {α s : ℝ} (hα : 0 < α) (hs : 0 ≤ s) :
    ((α + s) * s ^ (α / 5)) * (s ^ (-(α / 5)) / (α + s)) ≤ 1 := by
  have h : ((α + s) * s ^ (α / 5)) * (s ^ (-(α / 5)) / (α + s))
      = s ^ (α / 5) * s ^ (-(α / 5)) := by
    have hne : α + s ≠ 0 := by positivity
    field_simp
  rw [h]
  exact Work.Spaces.rpow_mul_rpow_neg_le_one hs (by linarith)

/-! ## The mixed-derivative pointwise bound -/

/-- The angular mixed-derivative pointwise bound: for an angular profile `a` bounded by `B` on
`Iθ = [0,π/2]`, with all its `D_θ`-iterates (orders `1..4`) bounded by `B·sin(2θ)`, and a
`SmoothQuad` function `h` in `𝒲^{4,∞}`, the mixed derivatives of the product `a·h` are bounded
by `1285 · B · |h|_𝒲` on the open quadrant.

* the Leibniz expansion `sqm_pz_DthIter_mul_le_4` of the product with the `z`-independent factor
  `fun z θ => a θ` collapses (only `c = 0` survives) to
  `|∂_z^k D_θ^j (a h)| ≤ 257 Σ_{m≤j} |Lop^[m] a| · |∂_z^k D_θ^{j-m} h|`;
* each summand is bounded by `B · |h|_𝒲` using `Work.Spaces.factor_bound`:
  `m = 0` uses `haB` and the cancellation `((α+s)s^{α/5})·s^{-α/5}/(α+s) ≤ 1`;
  `m ≥ 1, j - m ≥ 1` uses `haIt` (`|Lop^[m] a| ≤ B s`) and the same cancellation (`s ≤ 1`);
  `m = j ≥ 1` uses `haIt` together with `s·s^{-α/5}/(α+s) ≤ 1` (concavity). -/
theorem wang_mixed_bound {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (a : ℝ → ℝ) (B : ℝ)
    (h : ℝ → ℝ → ℝ) (hB : 0 ≤ B)
    (haSm : ∀ θ : ℝ, ContDiffAt ℝ ⊤ a θ)
    (haB : ∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ B)
    (haIt : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ B * Real.sin (2 * θ))
    (hh : Work.FTS.LocData.SmoothQuad h) (hmem : Work.Spaces.WlInfMem α 4 h) :
    ∀ j k : ℕ, 1 ≤ j → k + j ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j (fun z θ => a θ * h z θ)) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
      ≤ 1285 * (B * Work.Spaces.WlInf α 4 h) := by
  intro j k hj hkj z hz θ hθ
  have hz0 : (0:ℝ) ≤ z := hz
  have hk4 : k ≤ 4 := by omega
  have hj4 : j ≤ 4 := by omega
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hsle1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hspos : 0 < α + Real.sin (2 * θ) := by linarith
  have hWnn : 0 ≤ Work.Spaces.WlInf α 4 h := Work.FTS.H2.sqm_WlInf_nonneg α 4 h hmem
  have hp : 0 ≤ (z + 1) ^ k := pow_nonneg (by linarith) k
  have hZnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) :=
    div_nonneg (Real.rpow_nonneg hs0 _) hspos.le
  have hψnn : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hs0 _)
  have hBWnn : 0 ≤ B * Work.Spaces.WlInf α 4 h := mul_nonneg hB hWnn
  -- the angular profile is `SmoothQuad` on the open quadrant
  have hfq : Work.FTS.LocData.SmoothQuad (fun _ θ : ℝ => a θ) := by
    have haCD : ContDiff ℝ ⊤ a := contDiff_iff_contDiffAt.mpr haSm
    have haC : ContDiff ℝ Work.Stability.smoothOrder a := haCD.of_le le_top
    exact haC.contDiffOn.comp contDiffOn_snd (fun p _ => Set.mem_univ p.2)
  -- the Leibniz expansion of the product
  have hleib := Work.FTS.H2.sqm_pz_DthIter_mul_le_4 k j hk4 hj4
      (fun _ θ : ℝ => a θ) h hfq hh z hz θ hθ
  -- the double sum collapses onto the `c = 0` column
  have hcollapse : (∑ c ∈ Finset.range (k+1), ∑ m ∈ Finset.range (j+1),
        |Work.Spaces.pzIter c (Work.Spaces.DthIter m (fun _ θ : ℝ => a θ)) z θ|
          * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - m) h) z θ|)
      = ∑ m ∈ Finset.range (j+1),
          |Work.Spaces.Lop^[m] a θ| * |Work.Spaces.pzIter k (Work.Spaces.DthIter (j - m) h) z θ| := by
    refine (Finset.sum_eq_single 0 ?_ ?_).trans ?_
    · intro c hc hc0
      refine Finset.sum_eq_zero fun m _ => ?_
      rw [pzIter_DthIter_const_snd c m a z θ, ite_eq_right hc0]
      simp
    · intro h0
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos k)) h0
    · refine Finset.sum_congr rfl fun m _ => ?_
      rw [pzIter_DthIter_const_snd 0 m a z θ, ite_eq_left rfl, Nat.sub_zero]
  -- termwise bound of the collapsed sum
  have hterm : ∀ m ∈ Finset.range (j + 1),
      (z + 1) ^ k * (|Work.Spaces.Lop^[m] a θ|
          * |Work.Spaces.pzIter k (Work.Spaces.DthIter (j - m) h) z θ|)
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        ≤ B * Work.Spaces.WlInf α 4 h := by
    intro m hm
    have hmj : m ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
    have hfb := Work.Spaces.factor_bound α hα h hmem k (j - m) hk4 (fun h1 => by omega) z θ hz hθI
    have hAZ : (z + 1) ^ k * (|Work.Spaces.Lop^[m] a θ|
          * |Work.Spaces.pzIter k (Work.Spaces.DthIter (j - m) h) z θ|)
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        = |Work.Spaces.Lop^[m] a θ|
          * |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter (j - m) h) z θ|
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := by
      rw [abs_mul, abs_of_nonneg hp]; ring
    rw [hAZ]
    have hstep : |Work.Spaces.Lop^[m] a θ|
          * |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter (j - m) h) z θ|
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        ≤ |Work.Spaces.Lop^[m] a θ|
          * (Work.Spaces.WlInf α 4 h * (if j - m = 0 then (1:ℝ)
              else (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfb (abs_nonneg _)) hZnn
    refine le_trans hstep ?_
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · -- `m = 0`: the profile factor is bounded by `haB`
      subst hm0
      simp only [Function.iterate_zero_apply, Nat.sub_zero]
      rw [ite_eq_right (by omega : ¬ (j = 0))]
      calc |a θ| * (Work.Spaces.WlInf α 4 h * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
              * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
          ≤ B * (Work.Spaces.WlInf α 4 h * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
              * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (haB θ hθI) (mul_nonneg hWnn hψnn)) hZnn
        _ = (B * Work.Spaces.WlInf α 4 h)
              * (((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) := by ring
        _ ≤ (B * Work.Spaces.WlInf α 4 h) * 1 :=
            mul_le_mul_of_nonneg_left (weight_mul_div_le_one hα hs0) hBWnn
        _ = B * Work.Spaces.WlInf α 4 h := by ring
    · -- `m ≥ 1`: the profile factor is bounded by `haIt`
      have hm4 : m ≤ 4 := by omega
      have hLa : |Work.Spaces.Lop^[m] a θ| ≤ B * Real.sin (2 * θ) := by
        have h1 := haIt m hmpos (by omega) θ hθI
        rwa [DthIter_const_snd_apply m a 0 θ] at h1
      by_cases hjm : j - m = 0
      · -- the `h`-factor is radial: use `s·s^{-α/5}/(α+s) ≤ 1`
        rw [ite_eq_left hjm]
        calc |Work.Spaces.Lop^[m] a θ| * (Work.Spaces.WlInf α 4 h * 1)
                * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
            ≤ (B * Real.sin (2 * θ)) * (Work.Spaces.WlInf α 4 h * 1)
                * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hLa (mul_nonneg hWnn (by norm_num))) hZnn
          _ = (B * Work.Spaces.WlInf α 4 h)
                * (Real.sin (2 * θ)
                  * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) := by ring
          _ ≤ (B * Work.Spaces.WlInf α 4 h) * 1 :=
              mul_le_mul_of_nonneg_left (sin_mul_rpow_neg_div_le_one hα.le (by linarith) hs0) hBWnn
          _ = B * Work.Spaces.WlInf α 4 h := by ring
      · -- both factors angular: `s^{α/5}·s^{-α/5} ≤ 1` and `s ≤ 1`
        rw [ite_eq_right hjm]
        calc |Work.Spaces.Lop^[m] a θ|
                * (Work.Spaces.WlInf α 4 h * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
                * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
            ≤ (B * Real.sin (2 * θ))
                * (Work.Spaces.WlInf α 4 h * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
                * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hLa (mul_nonneg hWnn hψnn)) hZnn
          _ = (B * Work.Spaces.WlInf α 4 h) * (Real.sin (2 * θ)
                * (((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                  * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))))) := by ring
          _ ≤ (B * Work.Spaces.WlInf α 4 h) * (Real.sin (2 * θ) * 1) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left (weight_mul_div_le_one hα hs0) hs0) hBWnn
          _ ≤ (B * Work.Spaces.WlInf α 4 h) * 1 :=
              mul_le_mul_of_nonneg_left (by linarith [hs0, hsle1]) hBWnn
          _ = B * Work.Spaces.WlInf α 4 h := by ring
  -- assemble: `257` summands, each at most `B |h|_𝒲`
  have hmain : (z + 1) ^ k
        * |Work.Spaces.pzIter k (Work.Spaces.DthIter j (fun z θ => a θ * h z θ)) z θ|
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      ≤ 1285 * (B * Work.Spaces.WlInf α 4 h) := by
    have h5 : ((j + 1 : ℕ) : ℝ) ≤ 5 := by exact_mod_cast (show j + 1 ≤ 5 by omega)
    calc (z + 1) ^ k * |Work.Spaces.pzIter k (Work.Spaces.DthIter j (fun z θ => a θ * h z θ)) z θ|
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        ≤ (z + 1) ^ k * (257 * (∑ c ∈ Finset.range (k+1), ∑ m ∈ Finset.range (j+1),
              |Work.Spaces.pzIter c (Work.Spaces.DthIter m (fun _ θ : ℝ => a θ)) z θ|
                * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - m) h) z θ|))
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hleib hp) hZnn
      _ = 257 * ((z + 1) ^ k * (∑ m ∈ Finset.range (j+1),
              |Work.Spaces.Lop^[m] a θ| * |Work.Spaces.pzIter k (Work.Spaces.DthIter (j - m) h) z θ|)
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) := by
          rw [hcollapse]; ring
      _ = 257 * (∑ m ∈ Finset.range (j+1), (z + 1) ^ k
              * (|Work.Spaces.Lop^[m] a θ| * |Work.Spaces.pzIter k (Work.Spaces.DthIter (j - m) h) z θ|)
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) := by
          congr 1
          rw [Finset.mul_sum, Finset.sum_mul]
      _ ≤ 257 * (∑ _m ∈ Finset.range (j+1), B * Work.Spaces.WlInf α 4 h) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by norm_num)
      _ = 257 * (((j + 1 : ℕ) : ℝ) * (B * Work.Spaces.WlInf α 4 h)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ 1285 * (B * Work.Spaces.WlInf α 4 h) := by
          nlinarith [h5, hBWnn]
  have hLHS : |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j (fun z θ => a θ * h z θ)) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
      = (z + 1) ^ k * |Work.Spaces.pzIter k (Work.Spaces.DthIter j (fun z θ => a θ * h z θ)) z θ|
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := by
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg hp,
      abs_of_nonneg (Real.rpow_nonneg hs0 _), abs_of_pos hspos]
    ring
  rw [hLHS]
  exact hmain

/-! ## The radial pointwise bound -/

/-- The radial (`D_θ`-free) summands of the product `a·h`: `a` factors out of `∂_z^k`, and both
factors are bounded by `B` resp. `|h|_𝒲`.  (On the *closed* quadrant, unlike the mixed summands:
no boundary hypothesis on `h` is needed.) -/
theorem wang_radial_bound {α : ℝ} (hα : 0 < α) (a : ℝ → ℝ) (B : ℝ) (h : ℝ → ℝ → ℝ)
    (hB : 0 ≤ B) (haB : ∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ B)
    (hmem : Work.Spaces.WlInfMem α 4 h) :
    ∀ k : ℕ, k ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k (fun z θ => a θ * h z θ) z θ|
        ≤ B * Work.Spaces.WlInf α 4 h := by
  intro k hk z hz θ hθ
  have hz0 : (0:ℝ) ≤ z := hz
  have hp : 0 ≤ (z + 1) ^ k := pow_nonneg (by linarith) k
  rw [pzIter_angular_mul k a h]
  calc |(z + 1) ^ k * (a θ * Work.Spaces.pzIter k h z θ)|
      = (z + 1) ^ k * (|a θ| * |Work.Spaces.pzIter k h z θ|) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hp]
    _ = |a θ| * ((z + 1) ^ k * |Work.Spaces.pzIter k h z θ|) := by ring
    _ ≤ B * Work.Spaces.WlInf α 4 h := by
        refine mul_le_mul (haB θ hθ) ?_ (mul_nonneg hp (abs_nonneg _)) hB
        rw [← abs_of_nonneg hp, ← abs_mul]
        exact Work.Spaces.WlInf_z_bound α 4 h hmem k hk z θ hz hθ

/-! ## The field lemma -/

/-- **The `wang` field of `N4Norm`, with the regularity hypotheses that the current version is
missing.**  The current field constrains only the *junk* derivatives of the angular profile `a`
and nothing on `h` besides `WlInfMem`, and it is **false**: with `a` and `h` the two
nowhere-differentiable rational/irrational profiles of
`Submission/Work/FTS/Nonlinear/N4Fields/wang_field_refuted.lean` both hypotheses on `a` hold
(all its `D_θ`-iterates vanish), `WlInfMem α 4 h` holds with `|h|_𝒲 = M`, while the product
`a·h = θ ↦ M(θ - π/4)·1_{|θ-π/4| ≤ M/2}` satisfies `|a·h|_𝒲 ≥ M/2` (the `(j,k) = (1,0)` mixed
term at `θ = π/4`), contradicting `M/2 ≤ C B |h|_𝒲 = C M²` for `M < 1/(2C)`.

The repair adds `∀ θ, ContDiffAt ℝ ⊤ a θ` (as in `angmul_field_smooth`, the backing result
`HkIntegrand_angular_mul_le`) and `SmoothQuad h` — then the two Leibniz expansions
(`DthIter_angular_mul_expand` in `θ`, `pzIter_mul_local_sm`/`pz_mul_le_4` in `z`) apply, the
angular weight is shared between the two factors of every summand (`Work.Spaces.psi_mw_le`,
`Work.Spaces.factor_bound`, `Work.Spaces.WlInf_z_bound`), and the passage from the interior
pointwise bound to `supAbs` on the closed quadrant is exactly the argument of
`Work.FTS.Nonlinear.N4Fields.wmul_field`. -/
theorem wang_field_smooth {α₂ : ℝ} (hα₂ : 0 < α₂) (hα₂1 : α₂ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ (a : ℝ → ℝ) (B : ℝ) (h : Work.FTS.Galerkin.Fn),
      0 ≤ B → (∀ θ : ℝ, ContDiffAt ℝ ⊤ a θ) →
      (∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ B) →
      (∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ B * Real.sin (2 * θ)) →
      Work.FTS.LocData.SmoothQuad h → Work.Spaces.WlInfMem α 4 h →
      Work.Spaces.WlInfMem α 4 (fun z θ => a θ * h z θ) ∧
      Work.Spaces.WlInf α 4 (fun z θ => a θ * h z θ)
        ≤ C * B * Work.Spaces.WlInf α 4 h := by
  refine ⟨30 * 1285 + 1, by norm_num, ?_⟩
  intro α hα a B h hB haSm haB haIt hh hmem
  have hα1 : α ≤ 1 := le_trans hα.2 hα₂1
  have hWnn : 0 ≤ Work.Spaces.WlInf α 4 h := Work.FTS.H2.sqm_WlInf_nonneg α 4 h hmem
  have hBWnn : 0 ≤ B * Work.Spaces.WlInf α 4 h := mul_nonneg hB hWnn
  have hB' : 0 ≤ 1285 * (B * Work.Spaces.WlInf α 4 h) := mul_nonneg (by norm_num) hBWnn
  have hrad := wang_radial_bound hα.1 a B h hB haB hmem
  have hmix := wang_mixed_bound hα.1 hα1 a B h hB haSm haB haIt hh hmem
  -- the radial summands on the closed quadrant
  have hr : ∀ k : ℕ, k ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k (fun z θ => a θ * h z θ) z θ|
        ≤ 1285 * (B * Work.Spaces.WlInf α 4 h) := by
    intro k hk z hz θ hθ
    have h1 := hrad k hk z hz θ hθ
    have h2 : B * Work.Spaces.WlInf α 4 h ≤ 1285 * (B * Work.Spaces.WlInf α 4 h) := by
      nlinarith [hBWnn]
    linarith
  -- the mixed summands on the closed quadrant (the angular weight vanishes at `θ = 0, π/2`)
  have ht : ∀ j k : ℕ, 1 ≤ j → k + j ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j (fun z θ => a θ * h z θ)) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
        ≤ 1285 * (B * Work.Spaces.WlInf α 4 h) := by
    intro j k hj hkj z hz θ hθ
    have hαpos : 0 < α := hα.1
    have hne : (-(α / 5) : ℝ) ≠ 0 := by
      have h5 : (0:ℝ) < α / 5 := by linarith
      linarith
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · subst h0
      rw [show Real.sin (2 * (0:ℝ)) = 0 by
            rw [show (2:ℝ) * 0 = 0 by ring, Real.sin_zero], Real.zero_rpow hne]
      simp
      exact hBWnn
    · rcases lt_or_eq_of_le hθ.2 with hpi | hpi
      · exact hmix j k hj hkj z hz θ ⟨h0, hpi⟩
      · subst hpi
        rw [show Real.sin (2 * (π / 2)) = 0 by
              rw [show (2:ℝ) * (π / 2) = π by ring, Real.sin_pi], Real.zero_rpow hne]
        simp
        exact hBWnn
  have hcount := wlInf_of_pointwise_bounds (α := α)
    (B := 1285 * (B * Work.Spaces.WlInf α 4 h)) hB' hr ht
  refine ⟨hcount.1, ?_⟩
  calc Work.Spaces.WlInf α 4 (fun z θ => a θ * h z θ)
      ≤ 30 * (1285 * (B * Work.Spaces.WlInf α 4 h)) := hcount.2
    _ ≤ (30 * 1285 + 1) * B * Work.Spaces.WlInf α 4 h := by nlinarith [hBWnn]

end Work.FTS.Nonlinear.N4Fields
