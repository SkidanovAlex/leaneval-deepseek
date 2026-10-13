/-
# `Work.FTS.PhiStar.wlInf_of_zeroOff` — the flat `𝒲^{4,∞}`-bound from the flat data

The lead's star package (`VocabO2.StarPkgo2`) consumes `𝒲^{4,∞}`-honesty of several functions
that are only known to be *flat* on the open quadrant (`VocabO2.FlatW 4 f K`) and to vanish
off the open quadrant (`zeroOff`).  This module proves the transfer

`FlatW 4 f K` + `zeroOff` + `SmoothOpen f` + `0 < α ≤ 1`  ⟹  `WlInfMem α 4 f ∧ WlInf α 4 f ≤ C·K`

with a *universal* constant `C` (independent of `α`), which is what the consumers need.

The mathematical content has three parts.

* **Radial slots** (`(z+1)^k ∂_z^k f`, `k ≤ 4`): the flat bound holds on the open quadrant;
  on the boundary `θ ∈ {0, π/2}` the whole `z`-slice of `f` vanishes and on `z = 0` the slice
  `z' ↦ f z' θ` vanishes on `(-∞,0]`, so every `∂_z`-iterate at `0` is `0` (the Lean `deriv`
  is totalised, and a function that vanishes on a left neighbourhood has derivative `0` at the
  junction).

* **Angular slots** (`(z+1)^k D_θ^j f · sin(2θ)^{-α/5}/(α + sin 2θ)`, `1 ≤ j`, `k + j ≤ 4`):
  here we use that `D_θ = sin(2θ)∂_θ` is a derivation, whence
  `D_θ^j f = ∑_{a<j} C(j-1,a) (D_θ^a sin 2·) (D_θ^{j-1-a} ∂_θ f)`;
  each `D_θ^a(sin 2·)` carries a factor `sin(2θ)` (`|D_θ^a sin 2·| ≤ Asin a · sin 2θ`), while
  `(z+1)^k D_θ^{j-1-a}(∂_θ f)` is exactly one of the quantities bounded by `K` in `FlatW`.
  The angular weight is consumed by `sin_rpow_slack`:
  `sin(2θ)^{1-α/5}/(α + sin 2θ) ≤ 2` uniformly for `α ∈ (0,1]`, `sin(2θ) ∈ [0,1]`.

* **Assembly**: `WlInf` is a sum of `5` radial and at most `10` angular suprema, each bounded
  by a universal multiple of `K`; the `Finset.sum_le_sum` bookkeeping is the last step.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.NonlinRows.sqm_pz_DthIter_mul_le_4_open
import Submission.Work.FTS.PhiStar.Psi0Est.Defs
import Submission.Work.FTS.PhiStar.sin_rpow_slack
import Submission.Work.FTS.PhiStar.pzIter_DthIter_leibniz
import Submission.Work.FTS.PhiStar.radial_slot_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The radial slots

`radial_slot_le` (the closed-domain form of the first family of `FlatW`-slots) is imported from
`FTS/PhiStar/radial_slot_le.lean`; the lemmas below are the tools its sibling
`angular_slot_le` needs. -/

/-! ## `deriv` of a function vanishing on `(-∞,0]`

The whole point of the `zeroOff` hypothesis at `z = 0`: the `z`-slice `z' ↦ f z' θ` vanishes on
`(-∞,0]`, and for such a function the (totalised) `deriv` at `0` is `0`: if it is differentiable
then the two-sided difference-quotient limit is forced to `0` by the left half-line, and if it is
not differentiable Lean's `deriv` is `0` by definition. -/

theorem deriv_eq_zero_of_eqOn_Iic_zero {g : ℝ → ℝ} (h : ∀ x ≤ 0, g x = 0) :
    deriv g 0 = 0 := by
  by_cases hd : DifferentiableAt ℝ g 0
  · have h1 : Tendsto (slope g 0) (𝓝[≠] (0 : ℝ)) (𝓝 (deriv g 0)) :=
      hasDerivAt_iff_tendsto_slope.mp hd.hasDerivAt
    have h2 : Tendsto (slope g 0) (𝓝[Set.Iio (0 : ℝ)] (0 : ℝ)) (𝓝 (deriv g 0)) :=
      h1.mono_left (nhdsWithin_mono 0 fun x hx =>
        Set.mem_compl_singleton_iff.mpr (ne_of_lt hx))
    have h3 : (fun y => slope g 0 y) =ᶠ[𝓝[Set.Iio (0 : ℝ)] (0 : ℝ)] (fun _ => (0 : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      rw [slope_def_field, h y (le_of_lt hy), h 0 le_rfl]
      ring
    have h4 : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[Set.Iio (0 : ℝ)] (0 : ℝ))
        (𝓝 (deriv g 0)) :=
      h2.congr' h3
    haveI : (𝓝[Set.Iio (0 : ℝ)] (0 : ℝ)).NeBot := nhdsWithin_Iio_neBot le_rfl
    exact tendsto_nhds_unique h4 tendsto_const_nhds
  · exact deriv_zero_of_not_differentiableAt hd

/-- Every iterated derivative, at a point of `(-∞,0]`, of a function vanishing on `(-∞,0]`,
vanishes.  (The intended use is `x = 0`.) -/
theorem iteratedDeriv_eq_zero_of_eqOn_Iic {g : ℝ → ℝ} (h : ∀ x ≤ 0, g x = 0) :
    ∀ (k : ℕ) (x : ℝ), x ≤ 0 → iteratedDeriv k g x = 0 := by
  intro k
  induction k with
  | zero => intro x hx; exact h x hx
  | succ k ih =>
      intro x hx
      rw [iteratedDeriv_succ]
      rcases lt_or_eq_of_le hx with hxlt | hxeq
      · have hmem : Set.Iio (0 : ℝ) ∈ 𝓝 x := isOpen_Iio.mem_nhds hxlt
        have hev : (iteratedDeriv k g) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
          filter_upwards [hmem] with y hy
          exact ih y (le_of_lt hy)
        rw [hev.deriv_eq, deriv_const']
      · subst hxeq
        exact deriv_eq_zero_of_eqOn_Iic_zero ih

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ] at hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩

/-- A `θ`-slice which vanishes identically has all its `D_θ`-iterates vanishing. -/
theorem DthIter_eq_zero_of_slice_zero {u : ℝ → ℝ → ℝ} {z : ℝ} (h : ∀ θ, u z θ = 0) (j : ℕ) :
    ∀ θ, Work.Spaces.DthIter j u z θ = 0 := by
  induction j with
  | zero => intro θ; exact h θ
  | succ j ih =>
      intro θ
      have hslice : (fun θ' => Work.Spaces.DthIter j u z θ') = fun _ => (0 : ℝ) := funext ih
      rw [Work.Spaces.DthIter_succ]
      simp only [Work.Spaces.Dth, Work.Spaces.pth]
      rw [hslice, deriv_const']
      simp

/-- The `∂_z`-iterates of `D_θ^a(sin 2·)` are bounded by `Asin a · sin(2θ)`; for `c ≥ 1` they
vanish (the function is independent of `z`). -/
theorem abs_pzIter_DthIter_Sfun_le {c a : ℕ} (ha : a ≤ 4) (z : ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.pzIter c (Work.Spaces.DthIter a Work.FTS.H2.Sfun) z θ|
      ≤ Work.FTS.H2.Asin a * Real.sin (2 * θ) := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc
    simpa using Work.FTS.H2.abs_DthIter_Sfun_le a ha z hθ
  · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    have hzero : Work.Spaces.pzIter (c' + 1) (Work.Spaces.DthIter a Work.FTS.H2.Sfun) z θ = 0 := by
      rw [show Work.FTS.H2.Sfun = (fun _ θ' => Real.sin (2 * θ')) from rfl,
        Psi0Est.DthIter_theta_only]
      exact congrFun (congrFun (Psi0Est.pzIter_theta_only_succ
        (Work.Spaces.dthU^[a] (fun θ' => Real.sin (2 * θ'))) c') z) θ
    rw [hzero, abs_zero]
    exact mul_nonneg (le_of_lt (Work.FTS.H2.Asin_pos a)) hs

/-- The numerical constant of the `C(j-1,a)·Asin a` sum, for `j ≤ 4`. -/
theorem sum_choose_Asin_le (j : ℕ) (hj : j ≤ 4) :
    (∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ) * Work.FTS.H2.Asin a) ≤ 1536 := by
  interval_cases j <;>
    norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Work.FTS.H2.Asin]

/-! ## The angular slots -/

/-- **The angular slot bound.**  For a flat datum, each of the angular slots of `WlInf α 4`
(`1 ≤ j`, `k + j ≤ 4`) is bounded by `10⁶ · K` on the closed domain. -/
theorem angular_slot_le {α K : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hzero : ∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 → f z θ = 0)
    (hF : Work.FTS.VocabO2.FlatW 4 f K) (hK : 0 ≤ K)
    {j k : ℕ} (hj : 1 ≤ j) (hjk : k + j ≤ 4) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| ≤ 1000000 * K := by
  intro z hz θ hθ
  have hKbig : (0 : ℝ) ≤ 1000000 * K := by positivity
  have hz0 : (0 : ℝ) ≤ z := hz
  rcases lt_or_eq_of_le hz0 with hzpos | hz0eq
  · by_cases hθI : θ ∈ Set.Ioo 0 (Real.pi / 2)
    · -- interior: the `D_θ`-Leibniz expansion plus the flat bound
      have hsin_pos : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hθI.1]) (by linarith [hθI.2, Real.pi_pos])
      have hsin_nn : 0 ≤ Real.sin (2 * θ) := le_of_lt hsin_pos
      have hden_pos : 0 < α + Real.sin (2 * θ) := by linarith
      have hleib := pzIter_DthIter_leibniz (k := k) hf hj hzpos hθI
      -- (1) the bound on the `D_z^k D_θ^j f`-part
      have hmain : |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ|
          ≤ 1536 * K * Real.sin (2 * θ) := by
        have hsum : |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ|
            ≤ (∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ) * Work.FTS.H2.Asin a)
              * K * Real.sin (2 * θ) := by
          rw [hleib, Finset.mul_sum]
          calc |∑ a ∈ Finset.range j, (z + 1) ^ k * (((j - 1).choose a : ℝ) *
                (Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
                  Work.Spaces.pzIter k (Work.Spaces.DthIter (j - 1 - a) (Work.Spaces.pth f))
                    z θ))|
              = |∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ) *
                  ((z + 1) ^ k * (Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
                    Work.Spaces.pzIter k (Work.Spaces.DthIter (j - 1 - a) (Work.Spaces.pth f))
                      z θ))| := by
                congr 1
                refine Finset.sum_congr rfl fun a _ => ?_
                ring
            _ ≤ ∑ a ∈ Finset.range j, |((j - 1).choose a : ℝ) *
                  ((z + 1) ^ k * (Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
                    Work.Spaces.pzIter k (Work.Spaces.DthIter (j - 1 - a) (Work.Spaces.pth f))
                      z θ))| := Finset.abs_sum_le_sum_abs _ _
            _ = ∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ) *
                  |(z + 1) ^ k * (Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
                    Work.Spaces.pzIter k (Work.Spaces.DthIter (j - 1 - a) (Work.Spaces.pth f))
                      z θ)| := by
                refine Finset.sum_congr rfl fun a _ => ?_
                rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
            _ ≤ ∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ) *
                  (Work.FTS.H2.Asin a * K * Real.sin (2 * θ)) := by
                refine Finset.sum_le_sum fun a ha => ?_
                refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
                have haj : a ≤ j - 1 := by rw [Finset.mem_range] at ha; omega
                have hA : |Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ|
                    ≤ Work.FTS.H2.Asin a * Real.sin (2 * θ) :=
                  abs_pzIter_DthIter_Sfun_le (c := 0) (a := a) (by omega) z hθ
                have hB : |(z + 1) ^ k * Work.Spaces.pzIter k
                      (Work.Spaces.DthIter (j - 1 - a) (Work.Spaces.pth f)) z θ| ≤ K :=
                  (hF z θ hzpos hθI.1 hθI.2).2 k (j - 1 - a) (by omega)
                calc |(z + 1) ^ k * (Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
                      Work.Spaces.pzIter k (Work.Spaces.DthIter (j - 1 - a)
                        (Work.Spaces.pth f)) z θ)|
                    = |Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ| *
                        |(z + 1) ^ k * Work.Spaces.pzIter k
                          (Work.Spaces.DthIter (j - 1 - a) (Work.Spaces.pth f)) z θ| := by
                      rw [show (z + 1) ^ k * (Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
                            Work.Spaces.pzIter k (Work.Spaces.DthIter (j - 1 - a)
                              (Work.Spaces.pth f)) z θ)
                          = Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
                            ((z + 1) ^ k * Work.Spaces.pzIter k
                              (Work.Spaces.DthIter (j - 1 - a) (Work.Spaces.pth f)) z θ)
                          from by ring, abs_mul]
                  _ ≤ (Work.FTS.H2.Asin a * Real.sin (2 * θ)) * K :=
                      mul_le_mul hA hB (abs_nonneg _)
                        (mul_nonneg (le_of_lt (Work.FTS.H2.Asin_pos a)) hsin_nn)
                  _ = Work.FTS.H2.Asin a * K * Real.sin (2 * θ) := by ring
            _ = (∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ) * Work.FTS.H2.Asin a)
                  * (K * Real.sin (2 * θ)) := by
                rw [Finset.sum_mul]
                refine Finset.sum_congr rfl fun a _ => ?_
                ring
            _ = (∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ) * Work.FTS.H2.Asin a)
                  * K * Real.sin (2 * θ) := by ring
        have hj4 : j ≤ 4 := by omega
        calc |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ|
            ≤ (∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ) * Work.FTS.H2.Asin a)
                * K * Real.sin (2 * θ) := hsum
          _ ≤ 1536 * K * Real.sin (2 * θ) := by
              refine mul_le_mul_of_nonneg_right ?_ hsin_nn
              exact mul_le_mul_of_nonneg_right (sum_choose_Asin_le j hj4) hK
      -- (2) multiply by the angular weight
      have hrpow : Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(α / 5))
          = (Real.sin (2 * θ)) ^ (1 - α / 5) := by
        have h : (1 : ℝ) - α / 5 = 1 + -(α / 5) := by ring
        rw [h, Real.rpow_add hsin_pos, Real.rpow_one]
      calc |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
          = |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ|
              * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := by
            rw [abs_div, abs_mul, abs_of_nonneg (Real.rpow_nonneg hsin_nn _),
              abs_of_nonneg (le_of_lt hden_pos)]
            ring
        _ ≤ (1536 * K * Real.sin (2 * θ))
              * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := by
            refine mul_le_mul_of_nonneg_right hmain ?_
            exact div_nonneg (Real.rpow_nonneg hsin_nn _) (le_of_lt hden_pos)
        _ = 1536 * K * ((Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (-(α / 5))
              / (α + Real.sin (2 * θ))) := by ring
        _ = 1536 * K * ((Real.sin (2 * θ)) ^ (1 - α / 5)
              / (α + Real.sin (2 * θ))) := by rw [hrpow]
        _ ≤ 1536 * K * 2 := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact sin_rpow_slack hα0 hα1 hsin_nn (Real.sin_le_one _)
        _ ≤ 1000000 * K := by nlinarith
    · -- `θ = 0` or `θ = π / 2`: the angular weight vanishes
      rw [Work.Spaces.Iθ] at hθ
      have hcases : θ = 0 ∨ θ = Real.pi / 2 := by
        rcases eq_or_lt_of_le hθ.1 with h | h
        · exact Or.inl h.symm
        · exact Or.inr (le_antisymm hθ.2 (not_lt.mp fun hlt => hθI ⟨h, hlt⟩))
      have hsin0 : Real.sin (2 * θ) = 0 := by
        rcases hcases with h | h
        · rw [h]; norm_num
        · rw [h, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      have hrpow : (Real.sin (2 * θ)) ^ (-(α / 5)) = 0 := by
        rw [hsin0]
        exact Real.zero_rpow (by linarith : -(α / 5) ≠ 0)
      rw [hrpow, mul_zero, zero_div, abs_zero]
      exact hKbig
  · -- `z = 0`: the whole slice `z' ↦ D_θ^j f z' θ` vanishes on `(-∞,0]`
    have hz0'' : z = 0 := hz0eq.symm
    subst hz0''
    have hsd : Work.Spaces.pzIter k (Work.Spaces.DthIter j f) 0 θ = 0 := by
      rw [Work.Spaces.pzIter_eq_iteratedDeriv]
      refine iteratedDeriv_eq_zero_of_eqOn_Iic (g := fun z' => Work.Spaces.DthIter j f z' θ)
        ?_ k 0 le_rfl
      intro z' hz'
      exact DthIter_eq_zero_of_slice_zero (u := f) (fun θ' => hzero z' θ' (by
        intro hmem
        have h1 : (0 : ℝ) < z' := (Work.FTS.EllipticEst.mem_Q0.mp hmem).1
        linarith)) j θ
    rw [hsd]
    simp only [mul_zero, zero_mul, zero_div, abs_zero]
    exact hKbig

/-! ## The target -/

theorem wlInf_of_zeroOff : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : Work.FTS.Galerkin.Fn) (K : ℝ),
    0 < α → α ≤ 1 →
    (∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 → f z θ = 0) →
    Work.FTS.EllipticEst.SmoothOpen f →
    Work.FTS.VocabO2.FlatW 4 f K →
    Work.Spaces.WlInfMem α 4 f ∧ Work.Spaces.WlInf α 4 f ≤ C * K := by
  refine ⟨300000000, by norm_num, ?_⟩
  intro α f K hα0 hα1 hzero hf hF
  have hK : 0 ≤ K := by
    have h := (hF 1 1 (by norm_num) (by norm_num)
      (by linarith [Real.pi_gt_three])).1 0 (by norm_num)
    exact le_trans (abs_nonneg _) h
  have hmem : Work.Spaces.WlInfMem α 4 f :=
    ⟨fun k hk => Work.Spaces.supFinite_of_pointwise
        (radial_slot_le hK hf hzero hF hk),
      fun j _ k _ hj1 hjk => Work.Spaces.supFinite_of_pointwise
        (angular_slot_le hα0 hα1 hf hzero hF hK hj1 hjk)⟩
  refine ⟨hmem, ?_⟩
  rw [Work.Spaces.WlInf]
  have h1 : (∑ k ∈ Finset.range 5,
      Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k f z θ)) ≤ 5 * K := by
    calc _ ≤ ∑ _k ∈ Finset.range 5, K := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk4 : k ≤ 4 := by rw [Finset.mem_range] at hk; omega
          exact Work.Spaces.supAbs_le (fun z hz θ hθ =>
            radial_slot_le hK hf hzero hF hk4 z hz θ hθ)
      _ = 5 * K := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
  have h2 : (∑ j ∈ Finset.range 5, ∑ k ∈ Finset.range 5,
      if 1 ≤ j ∧ k + j ≤ 4 then
        Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
          * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      else 0) ≤ 25 * (1000000 * K) := by
    calc _ ≤ ∑ _j ∈ Finset.range 5, ∑ _k ∈ Finset.range 5, (1000000 * K) := by
          refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ?_
          split_ifs with hcond
          · exact Work.Spaces.supAbs_le (fun z hz θ hθ =>
              angular_slot_le hα0 hα1 hf hzero hF hK hcond.1 hcond.2 z hz θ hθ)
          · exact mul_nonneg (by norm_num) hK
      _ = 25 * (1000000 * K) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_const,
            Finset.card_range, nsmul_eq_mul]
          ring
  linarith

end Work.FTS.PhiStar
