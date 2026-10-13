import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_RegExport.RXR5.Basic
import Submission.Work.FTS_RegExport.RXR5L.SG_C1Jet
import Submission.Work.FTS_RegExport.RXR5.Pieces.mixed_slice_tau_modulus

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXR5L.L12fAux.SG_tau_mod_weighted` — the *`z`-weighted* `τ`-modulus of `SG`

The sibling `Work.FTS_RegExport.RXR5L.SG_tau_mod` proves the unweighted `α`-Hölder modulus in the
fake time `τ` of the sanitised family `SG α g = gS α (tauExt g)` on the horizon `[0,S]`:

`|SG α g z θ τ - SG α g z θ τ'| ≤ Lt · |τ - τ'|^α`.

Here we prove the genuinely stronger, *weighted* statement

`|SG α g z θ τ - SG α g z θ τ'| ≤ Nt · z · |τ - τ'|^α`   (`0 ≤ z`),

i.e. the modulus is priced by a factor `z` vanishing at the axis `z = 0`.  This is exactly the
weight needed when the modulus is consumed inside a `z`-integral at the origin (the slots of
`L12`/`FK` carry the radial weight `w(z) = (1+z)²/z²`, so an unweighted modulus loses an integrable
factor).

The proof is the same three-step reduction as in `SG_tau_mod`:

* the weighted interior trade-off `RXR5.Pieces.mixed_slice_tau_modulus` at slot `(b,a) = (0,0)`
  turns the `ℋ⁴`-Lipschitz clause of `LimApprox` into
  `|g z θ τ - g z θ τ'| ≤ L · (z^{3/2}/(1+z)²) · |τ - τ'|` on the open quadrant;
* **the new ingredient** is `sliceW_le_z`: the interior weight is dominated by `z` itself, so the
  bound becomes `≤ L · z · |τ - τ'|` — this is what upgrades the *weight* from `z^{3/2}/(1+z)²`
  (`≤ 1`, the `SG_tau_mod` version) to `z`;
* on the horizon `[0,S]` the distance is dominated by `(S+1)·|τ - τ'|^α` (`tauDist_le_rpow`), which
  upgrades the Lipschitz bound to the weighted `α`-Hölder bound with constant `L·(S+1)`;
* on the two angular edges `θ = 0`, `θ = π/2` both values vanish identically by the
  `RegPkgMin.vanish` clause of `DynOK'`, and on the closed half-plane `z = 0` (the only place with
  `¬ 0 < z` and `0 ≤ z`) the sanitised family vanishes by `SG_apply_of_nonpos`, so both sides are
  `0` there — this is precisely why the weighted claim is *not* false for `z = 0`.
-/

namespace Work.FTS_RegExport.RXR5L.L12fAux

open scoped Real Topology
open Set Filter

/-- The radial weight `z^{3/2}/(1+z)²` of the weighted interior trade-off is dominated by `z`
itself: `z^{3/2}/(1+z)² ≤ z` for `z > 0`.  (For `0 < z ≤ 1` it is `z^{3/2} ≤ z`; for `z ≥ 1` it is
`z^{3/2} ≤ z² ≤ z(1+z)²`.) -/
lemma sliceW_le_z {z : ℝ} (hz : 0 < z) : z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2 ≤ z := by
  have h2 : 0 < (1 + z) ^ 2 := by positivity
  rw [div_le_iff₀ h2]
  have hsq : (1 : ℝ) ≤ (1 + z) ^ 2 := by nlinarith [sq_nonneg z, hz.le]
  rcases le_or_gt z 1 with hz1 | hz1
  · have hb : z ^ ((3 : ℝ) / 2) ≤ z := by
      have h := Real.rpow_le_rpow_of_exponent_ge hz hz1 (by norm_num : (1 : ℝ) ≤ (3 : ℝ) / 2)
      simpa using h
    nlinarith [hb, hsq, hz.le]
  · have hb : z ^ ((3 : ℝ) / 2) ≤ z ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hz1.le (by norm_num : (3 : ℝ) / 2 ≤ (2 : ℝ))
    rw [Real.rpow_two] at hb
    nlinarith [hb, hsq, hz.le]

/-- On `[0,S]` the distance of two points is dominated by `(S+1)·(distance)^α` for `0 < α ≤ 1`:
for small distances `t ≤ t^α`, for large ones `t^α ≥ 1` while `t ≤ S`. -/
lemma tauDist_le_rpow {α S t : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hS : 0 < S) (ht0 : 0 ≤ t)
    (htS : t ≤ S) : t ≤ (S + 1) * t ^ α := by
  rcases lt_or_ge t 1 with h1 | h1
  · have hle : t ≤ t ^ α := by
      rcases eq_or_lt_of_le ht0 with h0 | h0
      · rw [← h0]; simp [Real.zero_rpow (ne_of_gt hα)]
      · have h2 := Real.rpow_le_rpow_of_exponent_ge h0 h1.le hα1
        rwa [Real.rpow_one] at h2
    have hr : 0 ≤ t ^ α := Real.rpow_nonneg ht0 _
    nlinarith [hle, hr, hS]
  · have hle : (1 : ℝ) ≤ t ^ α := Real.one_le_rpow h1 (le_of_lt hα)
    nlinarith [hle, htS, hS]

theorem SG_tau_mod_weighted {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S) :
    ∃ Nt : ℝ, 0 ≤ Nt ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
      ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 ≤ z →
        |Work.FTS_RegExport.RXR5.SG α g z θ τ - Work.FTS_RegExport.RXR5.SG α g z θ τ'|
          ≤ Nt * z * |τ - τ'| ^ α := by
  have hDyn : Work.FTS.Final.DynOK (Work.FTS.Regularity.pExp α) C₀ g := hOK.1
  have hLim : Work.FTS.FinalV2.LimApprox (Work.FTS.Regularity.pExp α) C₀ Φs E g := hOK.2
  obtain ⟨L, hL0, hL⟩ :=
    Work.FTS_RegExport.RXR5.Pieces.mixed_slice_tau_modulus hLim
      (Work.FTS.Regularity.pExp_pos hα) (Work.FTS.Regularity.pExp_le_one hα13) S hS
  refine ⟨L * (S + 1), mul_nonneg hL0 (by linarith), ?_⟩
  intro τ hτ τ' hτ' θ hθ z hz
  have hτ0 : 0 ≤ τ := hτ.1
  have hτ'0 : 0 ≤ τ' := hτ'.1
  have hnn : 0 ≤ L * (S + 1) * z * |τ - τ'| ^ α :=
    mul_nonneg (mul_nonneg (mul_nonneg hL0 (by linarith)) hz)
      (Real.rpow_nonneg (abs_nonneg _) _)
  rcases lt_or_ge 0 z with hzpos | hznp
  · have hSGτ : Work.FTS_RegExport.RXR5.SG α g z θ τ = g z θ τ := by
      rw [Work.FTS_RegExport.RXR5.SG_apply_of_pos hzpos hθ.1 hθ.2,
        Work.FTS.FinalV2.tauExt_of_nonneg g hτ0]
    have hSGτ' : Work.FTS_RegExport.RXR5.SG α g z θ τ' = g z θ τ' := by
      rw [Work.FTS_RegExport.RXR5.SG_apply_of_pos hzpos hθ.1 hθ.2,
        Work.FTS.FinalV2.tauExt_of_nonneg g hτ'0]
    rw [hSGτ, hSGτ']
    rcases eq_or_lt_of_le hθ.1 with hθ0 | hθpos
    · obtain ⟨hv, -⟩ := hDyn.1.vanish τ hτ0 z hz
      obtain ⟨hv', -⟩ := hDyn.1.vanish τ' hτ'0 z hz
      rw [← hθ0, hv, hv', sub_self, abs_zero]
      exact hnn
    · rcases eq_or_lt_of_le hθ.2 with hθ2 | hθlt
      · obtain ⟨-, hv⟩ := hDyn.1.vanish τ hτ0 z hz
        obtain ⟨-, hv'⟩ := hDyn.1.vanish τ' hτ'0 z hz
        rw [hθ2, hv, hv', sub_self, abs_zero]
        exact hnn
      · -- open quadrant: the weighted Lipschitz bound, then `weight ≤ z`, then `τ`-length
        have hb := hL τ hτ τ' hτ' 0 0 (by norm_num) z θ hzpos hθpos hθlt
        have htz : |τ - τ'| ≤ S :=
          abs_sub_le_iff.mpr ⟨by linarith [hτ.1, hτ.2, hτ'.1, hτ'.2],
            by linarith [hτ.1, hτ.2, hτ'.1, hτ'.2]⟩
        have hself : |τ - τ'| ≤ (S + 1) * |τ - τ'| ^ α :=
          tauDist_le_rpow (t := |τ - τ'|) (S := S) hα (by linarith) hS (abs_nonneg _) htz
        calc |g z θ τ - g z θ τ'|
            = |Work.Spaces.mixed 0 0 (Work.FTS.Galerkin.slice g τ) z θ
                - Work.Spaces.mixed 0 0 (Work.FTS.Galerkin.slice g τ') z θ| := rfl
          _ ≤ L * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * |τ - τ'| := hb
          _ ≤ L * z * |τ - τ'| := by
              refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
              exact mul_le_mul_of_nonneg_left (sliceW_le_z hzpos) hL0
          _ ≤ L * z * ((S + 1) * |τ - τ'| ^ α) :=
              mul_le_mul_of_nonneg_left hself (mul_nonneg hL0 hzpos.le)
          _ = L * (S + 1) * z * |τ - τ'| ^ α := by ring
  · -- `z = 0` (the only point with `0 ≤ z` and `¬ 0 < z`): both values vanish
    have hz0 : z = 0 := le_antisymm hznp hz
    rw [hz0,
      Work.FTS_RegExport.RXR5.SG_apply_of_nonpos (α := α) (θ := θ) (τ := τ) (z := 0) le_rfl,
      Work.FTS_RegExport.RXR5.SG_apply_of_nonpos (α := α) (θ := θ) (τ := τ') (z := 0) le_rfl,
      sub_self, abs_zero]
    simp

end Work.FTS_RegExport.RXR5L.L12fAux
