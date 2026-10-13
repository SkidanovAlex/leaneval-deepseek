import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.StrongPersist.Degen.HkSqZeroOnQuad

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `PertResidPt`: the pointwise bounds of the perturbation residual `ℛ, 𝒰/ sin 2θ, 𝒱`

This file proves the pointwise (`L^∞`) form of the three inequalities carried by the
open-quadrant elliptic package `Work.FTS.VocabO.EllPkgGo α Ce f Ef`.  The package gives,
for each of the three residual coefficients

* `ℛ := Rop α (PhiTil α f Ef)`,
* `𝒰 := Uop α (PhiTil α f Ef) / s2`,
* `𝒱 := Vop (PhiTil α f Ef)`,

both the honesty of the datum at level `ℋ⁴` (`HQo α 4 · = SmoothOpen · ∧ HkMem α 4 ·`) and
the norm bound `Xn α · ≤ Ce · Xn α f`.  The missing link is the pointwise bound

  `|·(z,θ)| ≤ C / √(γ-1) · Xn α ·`  (`z > 0`, `0 < θ < π/2`),

which is Elgindi's Corollary `SecondDerivativesBounded` in the open class: it is exactly the
`b = 0` instance of `Work.FTS.TransportS.sup_dz_le_hk` applied to the residual coefficient
itself, since `D_z^0 = id`.  Composing the two inequalities gives

  `|·(z,θ)| ≤ C₀ · (1/√(γ-1)) · (Ce · Xn α f) ≤ (4 C₀ + 1) · α^{-1/2} · Ce · Xn α f`,

because `γ - 1 = α/10 ≥ α/16`, i.e. `1/√(γ-1) ≤ 4 α^{-1/2}` (`inv_sqrt_gam_le` below).

The sign of `Ce` has to be handled: the package only asserts `Xn α · ≤ Ce · Xn α f`, with no
positivity of `Ce`.  For `Ce < 0` that inequality forces `Xn α · = 0`, and since the residual
is `SmoothOpen` with `HkMem α 4`, `HkSqZeroOnQuad` upgrades `HkSq α 4 · = 0` to the honest
pointwise vanishing on the open quadrant, so the bound holds with both sides `0`
(it also forces `Xn α f = 0`).

Everything rests on the axioms `propext`, `Classical.choice`, `Quot.sound` only.

(Scratch: this directory still contains the elaboration harness `_probe_PRP.lean` /
`_probe_PRP2.lean` used while developing the proof; nothing imports them.)
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.NZaux

/-- For the Elgindi exponent `γ = 1 + α/10` one has `1/√(γ-1) ≤ 4 α^{-1/2}`
(quantitatively: `γ - 1 = α/10 ≥ α/16`, so `√(γ-1) ≥ √α/4`). -/
private lemma inv_sqrt_gam_le {α : ℝ} (hα : 0 < α) :
    1 / Real.sqrt (Work.Spaces.gam α - 1) ≤ 4 * α ^ (-(1 / 2 : ℝ)) := by
  have h4 : Real.sqrt (16 : ℝ) = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h16 : Real.sqrt (α / 16) = Real.sqrt α / 4 := by
    rw [Real.sqrt_div hα.le, h4]
  have hmono : Real.sqrt α / 4 ≤ Real.sqrt (Work.Spaces.gam α - 1) := by
    rw [← h16]
    exact Real.sqrt_le_sqrt (by rw [Work.Spaces.gam_sub_one]; linarith)
  have hpos : (0 : ℝ) < Real.sqrt α / 4 := by
    have := Real.sqrt_pos_of_pos hα
    linarith
  have h1 : 1 / Real.sqrt (Work.Spaces.gam α - 1) ≤ 1 / (Real.sqrt α / 4) :=
    one_div_le_one_div_of_le hpos hmono
  have h2 : 1 / (Real.sqrt α / 4) = 4 * α ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_neg hα.le, ← Real.sqrt_eq_rpow α, one_div_div, div_eq_mul_inv]
  calc 1 / Real.sqrt (Work.Spaces.gam α - 1)
      ≤ 1 / (Real.sqrt α / 4) := h1
    _ = 4 * α ^ (-(1 / 2 : ℝ)) := h2

/-- **The pointwise bounds for the residual coefficients of the elliptic package.**
The universal constant is `4 C₀ + 1`, where `C₀` is the universal constant of
`Work.FTS.TransportS.sup_dz_le_hk`. -/
theorem PertResidPt : ∃ C : ℝ, 0 < C ∧ ∀ {α Ce : ℝ} {f Ef : Work.FTS.Galerkin.Fn},
    0 < α → α ≤ 1 → Work.FTS.VocabO.EllPkgGo α Ce f Ef →
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Construction.Rop α (Work.Construction.PhiTil α f Ef) z θ|
        ≤ C * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f) ∧
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Construction.Uop α (Work.Construction.PhiTil α f Ef) z θ / Work.Construction.s2 θ|
        ≤ C * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f) ∧
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Construction.Vop (Work.Construction.PhiTil α f Ef) z θ|
        ≤ C * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f) := by
  obtain ⟨C0, hC0pos, hsup⟩ := Work.FTS.TransportS.sup_dz_le_hk
  refine ⟨4 * C0 + 1, by linarith, ?_⟩
  intro α Ce f Ef hα hα1 hpkg
  -- the generic step: `SmoothOpen` + `HkMem α 4` + `Xn α w ≤ Ce · Xn α f` give the
  -- pointwise bound for `w` with the universal constant `4 C₀ + 1`
  have key : ∀ (w : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen w → Work.Spaces.HkMem α 4 w →
      Work.FTS.Nonlin.Xn α w ≤ Ce * Work.FTS.Nonlin.Xn α f →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        |w z θ| ≤ (4 * C0 + 1) * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f := by
    intro w hsm hmem hle z θ hz hθ hθπ
    by_cases hCe : 0 ≤ Ce
    · -- the generic case `Ce ≥ 0`: chain the sup-bound with the package's norm bound
      have h1 : |w z θ| ≤ C0 / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α w := by
        have h := hsup α w hα hα1 hsm hmem 0 (by norm_num) z θ hz hθ hθπ
        simpa using h
      have hcoef : 0 ≤ C0 / Real.sqrt (Work.Spaces.gam α - 1) :=
        div_nonneg hC0pos.le (Real.sqrt_nonneg _)
      have hr : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
      have h3 : C0 / Real.sqrt (Work.Spaces.gam α - 1)
          ≤ (4 * C0 + 1) * α ^ (-(1 / 2 : ℝ)) := by
        have h := inv_sqrt_gam_le (α := α) hα
        have h1' : C0 * (1 / Real.sqrt (Work.Spaces.gam α - 1))
            ≤ C0 * (4 * α ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left h hC0pos.le
        have h2' : C0 * (4 * α ^ (-(1 / 2 : ℝ)))
            ≤ (4 * C0 + 1) * α ^ (-(1 / 2 : ℝ)) := by
          rw [show C0 * (4 * α ^ (-(1 / 2 : ℝ))) = (4 * C0) * α ^ (-(1 / 2 : ℝ)) by ring]
          exact mul_le_mul_of_nonneg_right (by linarith) hr
        have he : C0 / Real.sqrt (Work.Spaces.gam α - 1)
            = C0 * (1 / Real.sqrt (Work.Spaces.gam α - 1)) := by ring
        rw [he]
        linarith
      have h4 : 0 ≤ Ce * Work.FTS.Nonlin.Xn α f :=
        mul_nonneg hCe (Work.Spaces.HkNorm_nonneg α 4 f)
      calc |w z θ| ≤ C0 / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α w := h1
        _ ≤ C0 / Real.sqrt (Work.Spaces.gam α - 1) * (Ce * Work.FTS.Nonlin.Xn α f) :=
            mul_le_mul_of_nonneg_left hle hcoef
        _ ≤ ((4 * C0 + 1) * α ^ (-(1 / 2 : ℝ))) * (Ce * Work.FTS.Nonlin.Xn α f) :=
            mul_le_mul_of_nonneg_right h3 h4
        _ = (4 * C0 + 1) * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f := by ring
    · -- the degenerate case `Ce < 0`: the package's bound forces `Xn α w = 0`, hence `w = 0`
      have hCe' : Ce < 0 := not_le.mp hCe
      have hnonneg_f : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
      have hXw0 : Work.FTS.Nonlin.Xn α w = 0 := by
        have h1 : Work.FTS.Nonlin.Xn α w ≤ 0 :=
          le_trans hle (mul_nonpos_of_nonpos_of_nonneg hCe'.le hnonneg_f)
        have h2 : 0 ≤ Work.FTS.Nonlin.Xn α w := Work.Spaces.HkNorm_nonneg α 4 w
        linarith
      have hSq0 : Work.Spaces.HkSq α 4 w = 0 := by
        have hthis : Real.sqrt (Work.Spaces.HkSq α 4 w) = 0 := hXw0
        exact le_antisymm (Real.sqrt_eq_zero'.mp hthis) (Work.Spaces.HkSq_nonneg α 4 w)
      have hw0 : w z θ = 0 :=
        Work.FTS.StrongPersist.Degen.HkSqZeroOnQuad hsm hmem hSq0 z θ hz hθ hθπ
      have hXf0 : Work.FTS.Nonlin.Xn α f = 0 := by
        have h2 : 0 ≤ Ce * Work.FTS.Nonlin.Xn α f := by
          have h3 : 0 ≤ Work.FTS.Nonlin.Xn α w := Work.Spaces.HkNorm_nonneg α 4 w
          linarith [hXw0]
        by_contra hne
        have hpos : 0 < Work.FTS.Nonlin.Xn α f :=
          lt_of_le_of_ne hnonneg_f (Ne.symm hne)
        nlinarith [h2, hpos, hCe']
      rw [hw0, abs_zero, hXf0, mul_zero]
  exact ⟨key (Work.Construction.Rop α (Work.Construction.PhiTil α f Ef))
          hpkg.R.1.1 hpkg.R.1.2 hpkg.R.2,
        key (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α f Ef) z θ
            / Work.Construction.s2 θ) hpkg.U.1.1 hpkg.U.1.2 hpkg.U.2,
        key (Work.Construction.Vop (Work.Construction.PhiTil α f Ef))
          hpkg.V.1.1 hpkg.V.1.2 hpkg.V.2⟩

end Work.FTS.StrongPersist.H6Rows.NZaux
