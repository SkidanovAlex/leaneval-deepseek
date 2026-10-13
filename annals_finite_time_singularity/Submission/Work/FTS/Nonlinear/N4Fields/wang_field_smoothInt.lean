import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Nonlinear.Interface
import Submission.Work.FTS.Nonlinear.N4Fields.wlInf_of_pointwise_bounds
import Submission.Work.FTS.H2.prodW_interior_bound
import Submission.Work.FTS.Nonlinear.N4Fields.wang_field_smooth
import Submission.Work.Spaces.ProductRuleInW

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.Nonlinear.N4Fields

set_option maxHeartbeats 1600000

/-! ## `SmoothInt` is stronger than `SmoothQuad`

`SmoothInt f` is `C^⊤` (analytic order) on the open strip `(-1,∞) × (0,π/2)` plus a
`z`-smoothness conjunct; `SmoothQuad f` is `C^∞` (genuine smooth order
`Work.Stability.smoothOrder = ∞ ≤ ⊤`) on the same strip, so the projection is immediate. -/

theorem smoothQuad_of_smoothInt {f : ℝ → ℝ → ℝ} (h : Work.Spaces.SmoothInt f) :
    Work.FTS.LocData.SmoothQuad f := h.1.of_le le_top

/-! ## The mixed-derivative pointwise bound, with `SmoothQuad` in place of pointwise smoothness

This is `Work.FTS.Nonlinear.N4Fields.wang_mixed_bound` with its hypothesis
`∀ θ, ContDiffAt ℝ ⊤ a θ` replaced by `SmoothQuad (fun _ θ => a θ)`: that hypothesis is used
only to produce `SmoothQuad (fun _ θ => a θ)` (see `hfq` below), which is exactly the data the
`θ`-Leibniz expansion `sqm_pz_DthIter_mul_le_4` consumes. -/

/-- The angular mixed-derivative pointwise bound: for an angular profile `a` which is `C^∞` on
the open quadrant, bounded by `B` on `Iθ = [0,π/2]`, with all its `D_θ`-iterates (orders `1..4`)
bounded by `B·sin(2θ)`, and a `SmoothQuad` function `h` in `𝒲^{4,∞}`, the mixed derivatives of
the product `a·h` are bounded by `1285 · B · |h|_𝒲` on the open quadrant. -/
theorem wang_mixed_bound_quad {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (a : ℝ → ℝ) (B : ℝ)
    (h : ℝ → ℝ → ℝ) (hB : 0 ≤ B)
    (hfq : Work.FTS.LocData.SmoothQuad (fun _ θ : ℝ => a θ))
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

/-! ## The field lemma -/

/-- **The `wang` field of the repaired `N4Norm`, in the exact form of the interface.**

The interface (revision of 07:49) requires `a` and `h` to be *honestly* regular —
`Work.Spaces.SmoothInt (fun _ θ => a θ)` and `Work.Spaces.SmoothInt h` — which is exactly what
the Leibniz expansions need (`DthIter_angular_mul_expand` in `θ`, the `z`-Leibniz rule in `z`),
and what rules out the rational/irrational counterexample of `N4Fields/wang_field_refuted.lean`.

Cheap route (as the reviews of the sibling files record): `SmoothInt f → SmoothQuad f` by the
`.1` projection (both are `ContDiffOn` on the same open strip, and `⊤ ≥ smoothOrder`), so the
already-proved `Work.FTS.Nonlinear.N4Fields.wang_field_smooth` applies verbatim once one
observes that its only use of `(∀ θ, ContDiffAt ℝ ⊤ a θ)` is to produce
`SmoothQuad (fun _ θ => a θ)`.  Alternatively redo the interior pointwise bound of
`Work.FTS.H2.prodW_interior_bound` (`Work.Spaces.psi_mw_le`, `Work.Spaces.factor_bound`,
`Work.Spaces.WlInf_z_bound`) and pass to `supAbs` on the closed quadrant exactly as
`N4Fields/wmul_field.lean` does (the mixed weight vanishes at `θ = 0, π/2`, where no
information about the product is needed). -/
theorem wang_field_smoothInt {α₂ : ℝ} (hα₂ : 0 < α₂) (hα₂1 : α₂ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ (a : ℝ → ℝ) (B : ℝ) (h : Work.FTS.Galerkin.Fn),
      0 ≤ B →
      Work.Spaces.SmoothInt (fun _ (θ : ℝ) => a θ) → Work.Spaces.SmoothInt h →
      (∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ B) →
      (∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ B * Real.sin (2 * θ)) →
      Work.Spaces.WlInfMem α 4 h →
      Work.Spaces.WlInfMem α 4 (fun z θ => a θ * h z θ) ∧
      Work.Spaces.WlInf α 4 (fun z θ => a θ * h z θ)
        ≤ C * B * Work.Spaces.WlInf α 4 h := by
  refine ⟨30 * 1285 + 1, by norm_num, ?_⟩
  intro α hα a B h hB haInt hInt haB haIt hmem
  have hα1 : α ≤ 1 := le_trans hα.2 hα₂1
  have hfq : Work.FTS.LocData.SmoothQuad (fun _ θ : ℝ => a θ) := smoothQuad_of_smoothInt haInt
  have hh : Work.FTS.LocData.SmoothQuad h := smoothQuad_of_smoothInt hInt
  have hWnn : 0 ≤ Work.Spaces.WlInf α 4 h := Work.FTS.H2.sqm_WlInf_nonneg α 4 h hmem
  have hBWnn : 0 ≤ B * Work.Spaces.WlInf α 4 h := mul_nonneg hB hWnn
  have hB' : 0 ≤ 1285 * (B * Work.Spaces.WlInf α 4 h) := mul_nonneg (by norm_num) hBWnn
  have hrad := wang_radial_bound hα.1 a B h hB haB hmem
  have hmix := wang_mixed_bound_quad hα.1 hα1 a B h hB hfq haB haIt hh hmem
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
