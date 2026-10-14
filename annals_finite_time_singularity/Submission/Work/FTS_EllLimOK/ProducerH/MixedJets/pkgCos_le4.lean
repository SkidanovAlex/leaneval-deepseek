import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS_EllLimOK.ProducerH.slotBd_phiTil
import Submission.Work.FTS_EllLimOK.RulingELF
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.H2.Data =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.H2

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The uniform second angular-derivative bound** on the box, with the rate variable
`min θ (π/2 - θ)` and a fixed exponent `β`. -/
def ModWith (α : ℝ) (E : Fn →ₗ[ℝ] Fn) (a₀ b₀ K β : ℝ) : Prop :=
  ∀ g : Fn, Work.FTS.ClassC.ClassC α g →
    ∀ z ∈ Set.Icc a₀ b₀, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |deriv (deriv (fun θ' => (E g) z θ')) θ|
        ≤ K * Work.FTS.StrongGlobal.Xn6 α g * (min θ (π / 2 - θ)) ^ β

/-- **The pointwise derivative bounds of `E g`** on the open strip `(a₀,b₀) × (0,π/2)`. -/
def PartBounds (α : ℝ) (E : Fn →ₗ[ℝ] Fn) (a₀ b₀ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ g : Fn, Work.FTS.ClassC.ClassC α g →
    ∀ z ∈ Set.Icc a₀ b₀, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.pz (E g) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
      |Work.Spaces.pth (E g) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
      |Work.Spaces.pz (Work.Spaces.pz (E g)) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
      |Work.Spaces.pth (Work.Spaces.pz (E g)) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
      |Work.Spaces.pz (Work.Spaces.pth (E g)) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
      |Work.Spaces.pth (Work.Spaces.pth (E g)) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
      |Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pz (E g))) z θ|
        ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
      |Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pz (E g))) z θ|
        ≤ C * Work.FTS.StrongGlobal.Xn6 α g

/-- **The endpoint bounds and rates** of the radial derivatives of `E g`.  The first eight
conjuncts are the pointwise bounds (`PartBounds`); the last six are the endpoint rates, with the
exponent `β` of the second angular derivative. -/
def RatesWith (α : ℝ) (E : Fn →ₗ[ℝ] Fn) (a₀ b₀ β : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ g : Fn, Work.FTS.ClassC.ClassC α g →
    ∀ z ∈ Set.Icc a₀ b₀, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.pz (E g) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
      |Work.Spaces.pth (E g) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
      |Work.Spaces.pz (Work.Spaces.pz (E g)) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
      |Work.Spaces.pth (Work.Spaces.pz (E g)) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
      |Work.Spaces.pz (Work.Spaces.pth (E g)) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
      |Work.Spaces.pth (Work.Spaces.pth (E g)) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
      |Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pz (E g))) z θ|
        ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
      |Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pz (E g))) z θ|
        ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
      |Work.Spaces.pz (E g) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g * θ ∧
      |Work.Spaces.pz (Work.Spaces.pz (E g)) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g * θ ∧
      |Work.Spaces.pz (E g) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g * (π / 2 - θ) ∧
      |Work.Spaces.pz (Work.Spaces.pz (E g)) z θ|
        ≤ C * Work.FTS.StrongGlobal.Xn6 α g * (π / 2 - θ) ∧
      |Work.Spaces.pth (Work.Spaces.pth (E g)) z θ|
        ≤ C * Work.FTS.StrongGlobal.Xn6 α g * θ ^ β ∧
      |Work.Spaces.pth (Work.Spaces.pth (E g)) z θ|
        ≤ C * Work.FTS.StrongGlobal.Xn6 α g * (π / 2 - θ) ^ β

/-- **The angular endpoint limits** of `∂_θ(E g)` and of `∂_z∂_θ(E g)`: existence, linear rates,
continuity in `z`, and the identification of the `z`-derivative. -/
def Limits (α : ℝ) (E : Fn →ₗ[ℝ] Fn) (a b : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ g : Fn, Work.FTS.ClassC.ClassC α g →
    ∃ L0 N0 L1 N1 : ℝ → ℝ,
      (∀ z ∈ Set.Icc a b, Filter.Tendsto (fun θ => Work.Spaces.pth (E g) z θ)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (L0 z))) ∧
      (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        |Work.Spaces.pth (E g) z θ - L0 z| ≤ C * Work.FTS.StrongGlobal.Xn6 α g * θ) ∧
      (∀ z ∈ Set.Icc a b, Filter.Tendsto (fun θ => Work.Spaces.pz (Work.Spaces.pth (E g)) z θ)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (N0 z))) ∧
      (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        |Work.Spaces.pz (Work.Spaces.pth (E g)) z θ - N0 z|
          ≤ C * Work.FTS.StrongGlobal.Xn6 α g * θ) ∧
      (∀ z ∈ Set.Icc a b, Filter.Tendsto (fun θ => Work.Spaces.pth (E g) z θ)
        (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds (L1 z))) ∧
      (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        |Work.Spaces.pth (E g) z θ - L1 z|
          ≤ C * Work.FTS.StrongGlobal.Xn6 α g * (π / 2 - θ)) ∧
      (∀ z ∈ Set.Icc a b, Filter.Tendsto (fun θ => Work.Spaces.pz (Work.Spaces.pth (E g)) z θ)
        (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds (N1 z))) ∧
      (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        |Work.Spaces.pz (Work.Spaces.pth (E g)) z θ - N1 z|
          ≤ C * Work.FTS.StrongGlobal.Xn6 α g * (π / 2 - θ)) ∧
      ContinuousOn L0 (Set.Icc a b) ∧ ContinuousOn N0 (Set.Icc a b) ∧
      ContinuousOn L1 (Set.Icc a b) ∧ ContinuousOn N1 (Set.Icc a b) ∧
      (∀ z ∈ Set.Icc a b, HasDerivWithinAt L0 (N0 z) (Set.Icc a b) z) ∧
      (∀ z ∈ Set.Icc a b, HasDerivWithinAt L1 (N1 z) (Set.Icc a b) z)

/-- **The two-point θ-Hölder modulus** of the second angular derivative on the open strip. -/
def HolMod (α : ℝ) (E : Fn →ₗ[ℝ] Fn) (a₀ b₀ : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∃ β : ℝ, 0 < β ∧ ∀ g : Fn, Work.FTS.ClassC.ClassC α g →
    ∀ z ∈ Set.Icc a₀ b₀, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      ∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2),
        |deriv (deriv (fun θ'' => (E g) z θ'')) θ
            - deriv (deriv (fun θ'' => (E g) z θ'')) θ'|
          ≤ K * Work.FTS.StrongGlobal.Xn6 α g * |θ - θ'| ^ β

/-- **The complete endpoint data** for the box `[a₀,b₀] × [0,π/2]`: the angular rate bound,
the pointwise/endpoint bounds of the radial derivatives, the angular limits and the two-point
Hölder modulus. -/
def BoxData (α Ce : ℝ) (E : Fn →ₗ[ℝ] Fn) (a₀ b₀ : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∃ β : ℝ, 0 < β ∧ ModWith α E a₀ b₀ K β ∧ RatesWith α E a₀ b₀ β ∧
    Limits α E a₀ b₀ ∧ HolMod α E a₀ b₀

/-! ## Projections -/


theorem BoxData.bounds {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn} {a₀ b₀ : ℝ}
    (h : BoxData α Ce E a₀ b₀) : PartBounds α E a₀ b₀ := by
  obtain ⟨K, hK, β, hβ, -, h2, -⟩ := h
  obtain ⟨C, hC, hCb⟩ := h2
  exact ⟨C, hC, fun g hg => by
    intro z hz θ hθ
    obtain ⟨h1, h2', h3, h4, h5, h6, h7, h8, -⟩ := hCb g hg z hz θ hθ
    exact ⟨h1, h2', h3, h4, h5, h6, h7, h8⟩⟩




end Work.FTS_EllLimOK.ProducerH.H2
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.MixedJets.pkgCos_le4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FTS_EllLimOK.ProducerH.MixedJets.pkgCos_le4` — the pinning field at a fixed level `α ≤ 1/4`

The pinning field `PkgCos α E := ∀ g ∈ ClassC α, HkMem α 0 (PhiTil α g (E g) / cos θ)` of the
repaired package `HasPkgH` (`RulingELF`), derived from the level-`8` existence class
`∀ g ∈ ClassC α, EllClassOk 8 α g (E g)`, **at a prescribed level** `α ∈ (0, 1/4]`.

The sibling `ProducerH.pkgCos_of_ellClassOk` states the same derivation in *existential* form
(`∃ α₁ > 0, ∀ α ≤ α₁, …`), which does not expose the threshold `α₁ = 1/4` — an existential is not
usable at a prescribed level.  The present file therefore carries out the same derivation at the
fixed level `α`; the mathematical content and the route are those of the sibling:

Fix `g ∈ ClassC α` and put `Ψ := E g`, so that `EllClassOk 8 α g Ψ` gives

* `IsBslSol α g Ψ` (the law, the Dirichlet data and the decay),
* `SmoothOpen Ψ` (honest `C^∞` on the open quadrant),
* `EllWeakPos α 8 (orthSource g) (shiftSing α g Ψ)`.

* **The shifted unknown is in `ℋ⁰`** after division by `cos θ`: the weak class descends to level
  `0` (`EllWeakPos_descend`), and the *proved* first-order Step 1 of `prop:L2` (`Prop.l0_first`,
  which consumes exactly the hypothesis `α ≤ 1/4`) gives `HkMem α 0 (shiftSing α g Ψ / cos θ)`.
* **The singular part of the shift is in `ℋ⁰`**: writing `Gsing = Gstar + Gbar` with
  `Gstar α g = -(1/(4α))·L₁₂ g`, the exact identity
  `shiftSing α g Ψ = PhiTil α g Ψ + Gbar α g · sin 2θ` holds, so on the open quadrant
  `PhiTil / cos θ = shiftSing / cos θ - 2·Gbar·sin θ`.
* The `Gbar`-term is handled by a weighted Hardy bound for `Gbar α g`
  (`Cert.GbarLayer.layer_Gbar_rDzIter_bound`): `∫_0^∞ w² Ḡ² < ∞`, which is exactly the
  hypothesis of the membership `HkMem α 0 (2·Ḡ·sin θ)` proved here by domination with the
  majorant `8 w² Ḡ² sin(2θ)^{-η}` (`sin(2θ)^{-η}` is integrable on `Iθ` because `η = 99/100 < 1`).
* `HkMem α 0` is then closed under subtraction (`GalBasis.hkMem_sub_open`, whose two `SmoothOpen`
  hypotheses hold: `shiftSing/cos` is smooth by `gsing_certs_classC` + `smoothOpen_div_cos`, and
  `2·Ḡ·sin θ` is smooth by `sep_mul`), and the integrands of `PhiTil/cos` and of
  `shiftSing/cos - 2·Ḡ·sin θ` agree pointwise (at `θ = π/2`, where `1/cos` is junk and the two
  functions differ, the angular factor `w z / sin(2θ)^{η/2}` vanishes).

The helper lemmas are `private` in the sibling module and are therefore reproduced here.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.MixedJets

set_option autoImplicit false

/-! ## The algebraic identities -/

/-- **The exact identity `PhiTil α g Ψ = shiftSing α g Ψ - Gbar α g · sin 2θ`.**  It is the
definitional bookkeeping `Gsing = Gstar + Gbar`, `Gstar = -(1/(4α))·L₁₂`,
`Theta = (1/(4α))·sin 2θ·L₁₂`, and it holds for *all* `z, θ` (no division). -/
private theorem phiTil_eq_shiftSing_sub (α : ℝ) (g Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Construction.PhiTil α g Ψ z θ
      = Work.FTS.EllExist.shiftSing α g Ψ z θ
        - Work.Elliptic.Gbar α g z * Real.sin (2 * θ) := by
  have hL : Work.Construction.L12 g z = Work.Elliptic.L12 g z := by
    rw [Work.Construction.L12, Work.Elliptic.L12_eq_FM]
    rfl
  rw [Work.FTS.EllExist.shiftSing_apply, Work.Construction.PhiTil, Work.Construction.Theta,
      Work.Elliptic.Gsing, Work.Elliptic.Gstar, Work.Construction.s2, hL]
  ring

/-! ## The `ℋ⁰`-integrand at level `0` -/

/-- At level `0` the `ℋ⁰`-integrand has exactly one summand. -/
private theorem hkIntegrand_zero_unfold (α : ℝ) (X : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 X z θ
      = (X z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp only [Work.Spaces.HkIntegrand]
  norm_num

/-- Two functions whose *weighted* values agree at `(z,θ)` have the same `ℋ⁰`-integrand there. -/
private theorem hkIntegrand_zero_congr {α : ℝ} {X Y : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : X z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
       = Y z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) :
    Work.Spaces.HkIntegrand α 0 X z θ = Work.Spaces.HkIntegrand α 0 Y z θ := by
  rw [hkIntegrand_zero_unfold α X z θ, hkIntegrand_zero_unfold α Y z θ, h]

/-- **`HkMem` only depends on the `ℋ^k`-integrand.** -/
private theorem hkMem_congr_integrand {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ, Work.Spaces.HkIntegrand α k f z θ = Work.Spaces.HkIntegrand α k g z θ)
    (hf : Work.Spaces.HkMem α k f) : Work.Spaces.HkMem α k g := by
  constructor
  · intro z hz
    exact (hf.1 z hz).congr (Filter.Eventually.of_forall fun θ => h z θ)
  · refine hf.2.congr (Filter.Eventually.of_forall fun z => ?_)
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => h z θ)

/-! ## The angular weight -/

private theorem sq_div_rpow (w s : ℝ) (hs : 0 ≤ s) :
    (w / s ^ (Work.Spaces.eta / 2)) ^ 2 = w ^ 2 * s ^ (-(Work.Spaces.eta)) := by
  have hb : (s ^ (Work.Spaces.eta / 2)) ^ 2 = s ^ Work.Spaces.eta := by
    rw [← Real.rpow_natCast, show ((2 : ℕ) : ℝ) = 2 by norm_num]
    rw [← Real.rpow_mul hs (Work.Spaces.eta / 2) (2 : ℝ)]
    norm_num
  rw [div_pow, hb, Real.rpow_neg hs]
  ring

/-- The pointwise domination of the `ℋ⁰`-integrand of `2·R(z)·sin θ` by
`8·w(z)²·R(z)²·sin(2θ)^{-η}`: the angular factor is `4 sin²θ ≤ 4`. -/
private theorem bound_two_mul_sin {wz Rz s θ : ℝ} (hs : 0 ≤ s) :
    (2 * Rz * Real.sin θ * (wz / s ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ 8 * wz ^ 2 * Rz ^ 2 * s ^ (-(Work.Spaces.eta)) := by
  have h1 : (wz / s ^ (Work.Spaces.eta / 2)) ^ 2 = wz ^ 2 * s ^ (-(Work.Spaces.eta)) :=
    sq_div_rpow wz s hs
  have h2 : (2 * Rz * Real.sin θ * (wz / s ^ (Work.Spaces.eta / 2))) ^ 2
      = 4 * Rz ^ 2 * Real.sin θ ^ 2 * (wz / s ^ (Work.Spaces.eta / 2)) ^ 2 := by ring
  rw [h2, h1]
  have h3 : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
  have h4 : 0 ≤ s ^ (-(Work.Spaces.eta)) := Real.rpow_nonneg hs _
  have hR : (0 : ℝ) ≤ Rz ^ 2 := sq_nonneg Rz
  have hW : (0 : ℝ) ≤ wz ^ 2 := sq_nonneg wz
  have h5 : 4 * Rz ^ 2 * Real.sin θ ^ 2 * (wz ^ 2 * s ^ (-(Work.Spaces.eta)))
      ≤ 4 * Rz ^ 2 * 1 * (wz ^ 2 * s ^ (-(Work.Spaces.eta))) := by
    have h6 : (0 : ℝ) ≤ 4 * Rz ^ 2 := by linarith
    have h7 : (0 : ℝ) ≤ wz ^ 2 * s ^ (-(Work.Spaces.eta)) := mul_nonneg hW h4
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 h6) h7
  have h9 : 4 * Rz ^ 2 * 1 * (wz ^ 2 * s ^ (-(Work.Spaces.eta)))
      ≤ 8 * wz ^ 2 * Rz ^ 2 * s ^ (-(Work.Spaces.eta)) := by
    have h10 : (0 : ℝ) ≤ Rz ^ 2 * wz ^ 2 * s ^ (-(Work.Spaces.eta)) :=
      mul_nonneg (mul_nonneg hR hW) h4
    nlinarith [h10]
  linarith [h5, h9]

/-! ## The membership `HkMem α 0 (2·R·sin θ)` -/

/-- **`2·R(z)·sin θ ∈ ℋ⁰`** for a radial `R` that is `C^∞` on `(0,∞)` and has
`∫_0^∞ w² R² < ∞`.  This is the Hardy-type input supplied by the `GbarLayer` certificate for
`R = Gbar α g`: the angular weight `sin(2θ)^{-η}` is integrable on `Iθ` (`η < 1`), so the
majorant `8 w² R² sin(2θ)^{-η}` has integrable slices and integrable slice-integral. -/
private theorem hkMem_two_mul_sin {α : ℝ} {R : ℝ → ℝ}
    (hRsm : ∀ m : ℕ, ContDiffOn ℝ m R (Set.Ioi 0))
    (hint : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (R z) ^ 2) Work.Spaces.Iz) :
    Work.Spaces.HkMem α 0 (fun z θ => 2 * R z * Real.sin θ) := by
  have heta1 : -1 < -(Work.Spaces.eta) := by rw [Work.Spaces.eta]; norm_num
  have heta0 : -(Work.Spaces.eta) ≤ 0 := by rw [Work.Spaces.eta]; norm_num
  have hsinInt : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) heta1 heta0).1
  have hSm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => 2 * R z * Real.sin θ) := by
    have hsep := Work.FTS.EllipticEst.SmoothOpen.sep_mul (g := R)
      (χ := fun θ : ℝ => 2 * Real.sin θ) hRsm (by fun_prop)
    have hfun : (fun z θ : ℝ => R z * (2 * Real.sin θ))
        = fun z θ : ℝ => 2 * R z * Real.sin θ := by
      funext z θ; ring
    rwa [hfun] at hsep
  refine Work.FTS.LocData.HkMem_of_majorant α 0
    (f := fun z θ => 2 * R z * Real.sin θ)
    (M := fun z θ => 8 * (Work.Spaces.w z) ^ 2 * (R z) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
    (hSm.continuousOn_HkIntegrand α 0) ?_ ?_ ?_
  · intro z _
    have h := hsinInt.const_mul (8 * (Work.Spaces.w z) ^ 2 * (R z) ^ 2)
    refine MeasureTheory.IntegrableOn.congr_fun h (fun θ _ => by ring) measurableSet_Icc
  · have hMfun : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        8 * (Work.Spaces.w z) ^ 2 * (R z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        = fun z : ℝ =>
            (8 * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
              * ((Work.Spaces.w z) ^ 2 * (R z) ^ 2) := by
      funext z
      rw [show (fun θ : ℝ => 8 * (Work.Spaces.w z) ^ 2 * (R z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          = fun θ : ℝ => (8 * (Work.Spaces.w z) ^ 2 * (R z) ^ 2)
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) from by funext θ; ring]
      rw [MeasureTheory.integral_const_mul]
      ring
    rw [hMfun]
    exact hint.const_mul _
  · intro z _ θ hθ
    have hs : 0 ≤ Real.sin (2 * θ) := by
      refine Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], ?_⟩
      have := hθ.2; linarith [Real.pi_pos]
    rw [hkIntegrand_zero_unfold]
    exact bound_two_mul_sin hs

/-! ## Smoothness of the shifted unknown divided by `cos θ` -/

/-- `shiftSing α g Ψ / cos θ` is `C^∞` on the open quadrant: `shiftSing α g Ψ = Ψ + Gsing·sin 2θ`
with `Gsing α g` of class `C^∞` on `(0,∞)` (`gsing_certs_classC`), and `cos θ ≠ 0` on `Q0`. -/
private theorem smoothOpen_shiftSing_div_cos {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {g : Work.FTS.Galerkin.Fn} (hg : Work.FTS.ClassC.ClassC α g) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.FTS.EllExist.shiftSing α g Ψ z θ / Real.cos θ) := by
  have hGsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gsing α g) (Set.Ioi 0) :=
    (Work.FTS.ClassC.gsing_certs_classC hα hα1 hg).2.1
  have hsep : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Elliptic.Gsing α g z * Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.SmoothOpen.sep_mul (g := Work.Elliptic.Gsing α g)
      (χ := fun θ : ℝ => Real.sin (2 * θ)) hGsm (by fun_prop)
  have hsum : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Ψ z θ + Work.Elliptic.Gsing α g z * Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.smoothOpen_add hΨ hsep
  have h2 : (fun z θ : ℝ => Work.FTS.EllExist.shiftSing α g Ψ z θ / Real.cos θ)
      = fun z θ : ℝ => (Ψ z θ + Work.Elliptic.Gsing α g z * Real.sin (2 * θ)) / Real.cos θ := by
    funext z θ
    rw [Work.FTS.EllExist.shiftSing_apply]
  rw [h2]
  exact Work.FTS_EllLimOK.Pinning.smoothOpen_div_cos hsum

/-! ## The producer at the prescribed level -/

theorem pkgCos_le4 (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn)
    (hE : ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g →
      Work.FTS.EllExist.EllClassOk 8 α g (E g)) :
    Work.FTS_EllLimOK.PkgCos α E := by
  intro g hg
  have hα1 : α ≤ 1 := by linarith
  -- the level-`8` existence class of `E g`
  have hΨsm : Work.FTS.EllipticEst.SmoothOpen (E g) := (hE g hg).2.1
  have hw8 : Work.FTS.EllipticEst.TT.EllWeakPos α 8 (Work.Elliptic.orthSource g)
      (Work.FTS.EllExist.shiftSing α g (E g)) := (hE g hg).2.2
  -- `g ∈ ℋ⁰`
  have hg0 : Work.Spaces.HkMem α 0 g :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (k := 0) (l := 10) (by norm_num)
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall g).mp hg.reg) hg.mem10
  -- the weighted `L²`-integrability of `Ḡ(α,g)` (the Hardy bound of the `GbarLayer` certificate)
  have hGbarInt : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (Work.Elliptic.Gbar α g z) ^ 2) Work.Spaces.Iz := by
    have h1 := (Work.FTS.EllipticEst.Cert.GbarLayer.layer_Gbar_rDzIter_bound α hα hα1 0 g
      hg.reg hg0 0 le_rfl).1
    simpa only [Work.FTS.EllipticEst.rDzIter_zero] using h1
  have hGbarSm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gbar α g) (Set.Ioi 0) :=
    (Work.FTS.ClassC.gsing_certs_classC hα hα1 hg).2.2.1
  have hGsin : Work.Spaces.HkMem α 0
      (fun z θ => 2 * Work.Elliptic.Gbar α g z * Real.sin θ) :=
    hkMem_two_mul_sin hGbarSm hGbarInt
  -- the weak class at level `0`
  have hw0 : Work.FTS.EllipticEst.TT.EllWeakPos α 0 (Work.Elliptic.orthSource g)
      (Work.FTS.EllExist.shiftSing α g (E g)) :=
    Work.FTS.EllSol.PkgK5.EllWeakPos_descend (l := 0) (K := 8) (by norm_num) hw8
  -- Step 1 of `prop:L2`: the shifted unknown divided by `cos θ` is in `ℋ⁰`
  obtain ⟨C, _, hl0⟩ := Work.FTS.EllipticEst.Prop.l0_first
  have hShift : Work.Spaces.HkMem α 0
      (fun z θ => Work.FTS.EllExist.shiftSing α g (E g) z θ / Real.cos θ) :=
    (hl0 α (Work.Elliptic.orthSource g) (Work.FTS.EllExist.shiftSing α g (E g))
      hα hα4 hw0).2.1
  -- smoothness of the two summands
  have hShiftSm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.FTS.EllExist.shiftSing α g (E g) z θ / Real.cos θ) :=
    smoothOpen_shiftSing_div_cos hα hα1 hg hΨsm
  have hGsinSm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => 2 * Work.Elliptic.Gbar α g z * Real.sin θ) := by
    have hsep := Work.FTS.EllipticEst.SmoothOpen.sep_mul (g := Work.Elliptic.Gbar α g)
      (χ := fun θ : ℝ => 2 * Real.sin θ) hGbarSm (by fun_prop)
    have hfun : (fun z θ : ℝ => Work.Elliptic.Gbar α g z * (2 * Real.sin θ))
        = fun z θ : ℝ => 2 * Work.Elliptic.Gbar α g z * Real.sin θ := by
      funext z θ; ring
    rwa [hfun] at hsep
  -- `PhiTil/cos` agrees with the difference of the two summands
  have hU : Work.Spaces.HkMem α 0
      (fun z θ => Work.FTS.EllExist.shiftSing α g (E g) z θ / Real.cos θ
        - 2 * Work.Elliptic.Gbar α g z * Real.sin θ) :=
    Work.FTS.GalBasis.hkMem_sub_open α 0 hShiftSm hGsinSm hShift hGsin
  refine hkMem_congr_integrand (α := α) (k := 0) ?_ hU
  intro z θ
  refine hkIntegrand_zero_congr ?_
  by_cases hcos : Real.cos θ = 0
  · -- `cos θ = 0`: the angular weight vanishes on both sides
    have hs : Real.sin (2 * θ) = 0 := by rw [Real.sin_two_mul, hcos]; ring
    have hc : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
      rw [hs, Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)]
    simp only [hc, div_zero, mul_zero]
  · -- `cos θ ≠ 0`: `PhiTil/cos = shiftSing/cos - 2·Ḡ·sin θ`
    have h1 : Work.Construction.PhiTil α g (E g) z θ / Real.cos θ
        = Work.FTS.EllExist.shiftSing α g (E g) z θ / Real.cos θ
          - 2 * Work.Elliptic.Gbar α g z * Real.sin θ := by
      rw [phiTil_eq_shiftSing_sub α g (E g) z θ, Work.FTS.EllExist.shiftSing_apply]
      field_simp [hcos]
      rw [Real.sin_two_mul]
      ring
    rw [h1]

end Work.FTS_EllLimOK.ProducerH.MixedJets
end
end
