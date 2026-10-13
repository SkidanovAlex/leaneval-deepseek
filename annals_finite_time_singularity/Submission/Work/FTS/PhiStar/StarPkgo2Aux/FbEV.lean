/-
# `FTS/PhiStar/StarPkgo2Aux/FbEV.lean` — the `Fb 4`-bounds for `EVz Y` and `EV Y` in the
`K`-form

`Work.FTS.PhiStar.EVz Y = 2(cos²θ − 2 sin²θ)·Y + sin(2θ)·∂_θY` and `EV Y = (z/(z+1))·EVz Y`
are two of the eleven fields of `StarPkgo2`.  The `CoreAux` chapter proves them in the
"shifted" form

`Fb 6 (A(K+1)) Y → Fb 4 (C A⁴ (K+1)) (EVz Y)` (`CoreAux.Fb_EV_bound`),

because that is the shape in which the flat product calculus closes (`F0_mul` costs
`2^n K K'`, and the `∂_θ`-half of `EVz Y` produces a term `D_θ(∂_θY)` whose flat constant is
read off from the hypothesis `Fb 6 (A(K+1)) Y`).

Here we prove the *unshifted* form needed by the `StarPkgo2` assembly,

`Fb 6 (A·K) Y → Fb 4 (C A⁴ K (α+1)) (EVz Y) ∧ Fb 4 (C A⁴ K (α+1)) (EV Y)`.

The passage from the shifted to the unshifted constant is *not* a monotonicity step: for
`0 < K` the constant `C A⁴ (K+1)` is strictly larger than `C A⁴ K`, so one cannot simply drop
the `+1`.  The device is a **scaling argument**: the flat classes are homogeneous, so

* `Fb 6 (A·K) Y` gives `Fb 6 (c·(A·K)) (c·Y)` for every `c > 0` (`Fb_const_mul`), and
* `Fb 4 D (c·EVz Y)` gives back `Fb 4 (D/c) (EVz Y)` (`Fb_div_const`), because every
  `pzIter`/`DthIter` is `ℝ`-linear on constants (`pzIter_const_mul`, `DthIter_const_mul`).

Choosing `c = (K+1)/K` makes `c·(A·K) = A·(K+1)`, so `Fb_EV_bound` applies and yields the
constant `C A⁴ (K+1)`, which after the division by `c` is exactly `C A⁴ K` (`Fb_EV_lin`).  In
the degenerate case `K = 0` the target constant is *zero*: then the scaling argument is
available for every `c > 0`, so the constant can be made arbitrarily small, and a bound whose
constant is `≤ ε` for every `ε > 0` is a bound with constant `0` (`Fb_zero_of_forall_pos`).

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.CoreAux.Defs
import Submission.Work.FTS.PhiStar.CoreAux.FieldsDefs
import Submission.Work.FTS.PhiStar.CoreAux.F0_mul
import Submission.Work.FTS.PhiStar.CoreAux.F0_add
import Submission.Work.FTS.PhiStar.CoreAux.F0_zpz
import Submission.Work.FTS.PhiStar.CoreAux.Fb_zpz
import Submission.Work.FTS.PhiStar.CoreAux.Fb_basic
import Submission.Work.FTS.PhiStar.CoreAux.Fb_add
import Submission.Work.FTS.PhiStar.CoreAux.F0_congr
import Submission.Work.FTS.PhiStar.CoreAux.EVDefs
import Submission.Work.FTS.PhiStar.CoreAux.Fb_EV_bound

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
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## The constant supplied by `CoreAux.Fb_EV_bound` -/

/-- The constant of `CoreAux.Fb_EV_bound`, made explicit. -/
private noncomputable def FbEVc : ℝ := Classical.choose CoreAux.Fb_EV_bound

private theorem FbEVc_pos : 0 < FbEVc := (Classical.choose_spec CoreAux.Fb_EV_bound).1

/-- The shifted bound of `CoreAux.Fb_EV_bound` with the constant `FbEVc` made explicit. -/
private theorem FbEVc_spec (K A : ℝ) (Y : ℝ → ℝ → ℝ) (hK : 0 ≤ K) (hA : 1 ≤ A)
    (hYs : EllipticEst.SmoothOpen Y) (hphi : F0 6 A CoreAux.EVphi)
    (hsin : F0 6 A CoreAux.EVsin) (hrho : F0 6 A CoreAux.EVrho)
    (hY : Fb 6 (A * (K + 1)) Y) :
    Fb 4 (FbEVc * A ^ 4 * (K + 1)) (EVz Y) ∧ Fb 4 (FbEVc * A ^ 4 * (K + 1)) (EV Y) :=
  (Classical.choose_spec CoreAux.Fb_EV_bound).2 K A Y hK hA hYs hphi hsin hrho hY

/-! ## The flat classes are homogeneous -/

/-- **Scalar multiples in `Fb`.**  If `f` has flat constant `K`, then `c·f` has flat
constant `|c|·K`. -/
private theorem Fb_const_mul {n : ℕ} {K : ℝ} {f : ℝ → ℝ → ℝ} (c : ℝ) (h : Fb n K f) :
    Fb n (|c| * K) (fun z θ => c * f z θ) := by
  refine ⟨CoreAux.F0_const_mul c h.f0, ?_⟩
  rw [CoreAux.pth_const_mul c f]
  exact CoreAux.F0_const_mul c h.fd

/-- **Division by a non-zero constant in `F0`.**  If the scalar multiple `c·f` has flat
constant `D`, then `f` has flat constant `D/|c|`: every `pzIter`/`DthIter` is linear over the
constants. -/
private theorem F0_div_const {n : ℕ} {D : ℝ} {f : ℝ → ℝ → ℝ} {c : ℝ} (hc : c ≠ 0)
    (h : F0 n D (fun z θ => c * f z θ)) : F0 n (D / |c|) f := by
  have hcpos : 0 < |c| := abs_pos.mpr hc
  intro k i hki z θ hz hθ hθ'
  have h1 := h k i hki z θ hz hθ hθ'
  simp only [CoreAux.DthIter_const_mul, CoreAux.pzIter_const_mul] at h1
  have hkey : |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter i f) z θ| * |c| ≤ D := by
    rw [← abs_mul]
    rw [show ((z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter i f) z θ) * c
        = (z + 1) ^ k * (c * Work.Spaces.pzIter k (Work.Spaces.DthIter i f) z θ) from by ring]
    exact h1
  rw [le_div_iff₀ hcpos]
  exact hkey

/-- **Division by a non-zero constant in `Fb`.** -/
private theorem Fb_div_const {n : ℕ} {D : ℝ} {f : ℝ → ℝ → ℝ} {c : ℝ} (hc : c ≠ 0)
    (h : Fb n D (fun z θ => c * f z θ)) : Fb n (D / |c|) f := by
  have hp : F0 n D (Work.Spaces.pth (fun z θ => c * f z θ)) := h.fd
  rw [CoreAux.pth_const_mul c f] at hp
  exact ⟨F0_div_const hc h.f0, F0_div_const hc hp⟩

/-- **Congruence of the pair `Fb` on the open quadrant.** -/
private theorem Fb_congr {n : ℕ} {K : ℝ} {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) (hg : Fb n K g) :
    Fb n K f :=
  ⟨CoreAux.F0_congr h hg.f0, CoreAux.F0_congr (CoreAux.pth_congr_Q0 h) hg.fd⟩

/-- **A bound whose constant can be made arbitrarily small is a bound with constant `0`.** -/
private theorem Fb_zero_of_forall_pos {n : ℕ} {D : ℝ} {f : ℝ → ℝ → ℝ} (hD : 0 < D)
    (h : ∀ c : ℝ, 0 < c → Fb n (D / c) f) : Fb n 0 f := by
  have hkey : ∀ X : ℝ, (∀ c : ℝ, 0 < c → X ≤ D / c) → X ≤ 0 := by
    intro X hX
    by_contra hcon
    rw [not_le] at hcon
    have hXpos : 0 < X := hcon
    have hXne : X ≠ 0 := ne_of_gt hXpos
    have hden : (0 : ℝ) < D / X + 1 := by positivity
    have h2 : D / (D / X + 1) < X := by
      rw [div_lt_iff₀ hden]
      have hexp : X * (D / X + 1) = D + X := by field_simp
      rw [hexp]
      linarith
    have h1 : X ≤ D / (D / X + 1) := hX (D / X + 1) hden
    linarith
  exact ⟨fun k i hki z θ hz hθ hθ' => hkey _ fun c hc => (h c hc).f0 k i hki z θ hz hθ hθ',
    fun k i hki z θ hz hθ hθ' => hkey _ fun c hc => (h c hc).fd k i hki z θ hz hθ hθ'⟩

/-! ## The scaling device -/

/-- **The `EV`-bounds with the flat constant of the hypothesis scaled.**  For every `c > 0`
with `c(A K) ≤ A(K+1)` one gets the shifted bound of an earlier chapter applied to the
*unscaled* datum `Y` at constant `FbEVc·A⁴(K+1)/c`: scale `Y` up by `c`, apply the shifted
bound, and divide the constant back down. -/
private theorem Fb_EV_scaled {A K : ℝ} {Y : ℝ → ℝ → ℝ} (hA : 1 ≤ A) (hK : 0 ≤ K)
    (hYs : EllipticEst.SmoothOpen Y) (hphi : F0 6 A CoreAux.EVphi)
    (hsin : F0 6 A CoreAux.EVsin) (hrho : F0 6 A CoreAux.EVrho) (hY : Fb 6 (A * K) Y)
    {c : ℝ} (hc : 0 < c) (hcK : c * (A * K) ≤ A * (K + 1)) :
    Fb 4 (FbEVc * A ^ 4 * (K + 1) / c) (EVz Y) ∧
      Fb 4 (FbEVc * A ^ 4 * (K + 1) / c) (EV Y) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  -- the scaled datum
  have hYc : Fb 6 (A * (K + 1)) (fun z θ => c * Y z θ) := by
    have h := Fb_const_mul c hY
    rw [abs_of_pos hc] at h
    exact h.mono le_rfl hcK
  have hsYc : EllipticEst.SmoothOpen (fun z θ => c * Y z θ) := CoreAux.SmoothOpen.const_mul hYs c
  have haux := FbEVc_spec K A (fun z θ => c * Y z θ) hK hA hsYc hphi hsin hrho hYc
  -- the two pointwise identities `field (c·Y) = c·(field Y)`
  have hzc : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      EVz (fun z θ => c * Y z θ) z θ = c * EVz Y z θ := by
    intro z θ _ _ _
    have hp : Work.Spaces.pth (fun z θ => c * Y z θ) z θ = c * Work.Spaces.pth Y z θ :=
      congrFun (congrFun (CoreAux.pth_const_mul c Y) z) θ
    simp only [EVz, Tblk]
    rw [hp]
    ring
  have hevc : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      EV (fun z θ => c * Y z θ) z θ = c * EV Y z θ := by
    intro z θ hz hθ hθ'
    simp only [EV]
    rw [hzc z θ hz hθ hθ']
    ring
  have h1 : Fb 4 (FbEVc * A ^ 4 * (K + 1)) (fun z θ => c * EVz Y z θ) :=
    Fb_congr (fun z θ hz hθ hθ' => (hzc z θ hz hθ hθ').symm) haux.1
  have h2 : Fb 4 (FbEVc * A ^ 4 * (K + 1)) (fun z θ => c * EV Y z θ) :=
    Fb_congr (fun z θ hz hθ hθ' => (hevc z θ hz hθ hθ').symm) haux.2
  exact ⟨by simpa [abs_of_pos hc] using Fb_div_const hcne h1,
    by simpa [abs_of_pos hc] using Fb_div_const hcne h2⟩

/-! ## The unshifted constant -/

/-- **The `EV`-bounds in the `K`-form.** -/
private theorem Fb_EV_lin {A K : ℝ} {Y : ℝ → ℝ → ℝ} (hA : 1 ≤ A) (hK : 0 ≤ K)
    (hYs : EllipticEst.SmoothOpen Y) (hphi : F0 6 A CoreAux.EVphi)
    (hsin : F0 6 A CoreAux.EVsin) (hrho : F0 6 A CoreAux.EVrho) (hY : Fb 6 (A * K) Y) :
    Fb 4 (FbEVc * A ^ 4 * K) (EVz Y) ∧ Fb 4 (FbEVc * A ^ 4 * K) (EV Y) := by
  rcases eq_or_lt_of_le hK with hK0 | hKpos
  · -- `K = 0`: the target constant is `0`, and the scaling device drives it there
    subst hK0
    have hD : (0 : ℝ) < FbEVc * A ^ 4 := by
      exact mul_pos FbEVc_pos (pow_pos (lt_of_lt_of_le zero_lt_one hA) 4)
    have key : ∀ c : ℝ, 0 < c → Fb 4 (FbEVc * A ^ 4 / c) (EVz Y) ∧
        Fb 4 (FbEVc * A ^ 4 / c) (EV Y) := by
      intro c hc
      have hcs := Fb_EV_scaled hA hK hYs hphi hsin hrho hY hc
        (by nlinarith [le_trans zero_le_one hA])
      simpa using hcs
    refine ⟨?_, ?_⟩
    · simpa using Fb_zero_of_forall_pos hD (fun c hc => (key c hc).1)
    · simpa using Fb_zero_of_forall_pos hD (fun c hc => (key c hc).2)
  · -- `K > 0`: scale by `c = (K+1)/K`, which turns the scaled constant into `C A⁴ K`
    have hKne : K ≠ 0 := ne_of_gt hKpos
    have hK1pos : (0 : ℝ) < K + 1 := by linarith
    have hK1ne : K + 1 ≠ 0 := ne_of_gt hK1pos
    have hcpos : (0 : ℝ) < (K + 1) / K := div_pos hK1pos hKpos
    have hcKeq : (K + 1) / K * (A * K) = A * (K + 1) := by
      field_simp
    have h := Fb_EV_scaled hA hK hYs hphi hsin hrho hY hcpos (le_of_eq hcKeq)
    have hconst : FbEVc * A ^ 4 * (K + 1) / ((K + 1) / K) = FbEVc * A ^ 4 * K := by
      field_simp
    rwa [hconst] at h

/-! ## The target -/

theorem FbEV : ∃ C : ℝ, 0 < C ∧ ∀ (α K A : ℝ) (Y : ℝ → ℝ → ℝ),
    0 ≤ α → 0 ≤ K → 1 ≤ A →
    Work.FTS.EllipticEst.SmoothOpen Y →
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.sin θ ^ 2) →
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) →
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.cos (2 * θ)) →
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.sin (2 * θ)) →
    Work.FTS.PhiStar.F0 6 A (fun z _ => z / (1 + z)) →
    Work.FTS.PhiStar.F0 6 A (fun z _ => (1 + z)⁻¹) →
    Work.FTS.PhiStar.Fb 6 (A * K) Y →
    Work.FTS.PhiStar.Fb 4 (C * A ^ 4 * K * (α + 1)) (Work.FTS.PhiStar.EVz Y) ∧
    Work.FTS.PhiStar.Fb 4 (C * A ^ 4 * K * (α + 1)) (Work.FTS.PhiStar.EV Y) := by
  refine ⟨FbEVc + 1, by linarith [FbEVc_pos], ?_⟩
  intro α K A Y hα hK hA hYs hsinSq hphi hcos2 hsin2 hrho hrhoInv hY
  have hlin := Fb_EV_lin hA hK hYs hphi hsin2 hrho hY
  have hA4 : (0 : ℝ) ≤ A ^ 4 := pow_nonneg (le_trans zero_le_one hA) 4
  have hX : (0 : ℝ) ≤ FbEVc * A ^ 4 * K :=
    mul_nonneg (mul_nonneg FbEVc_pos.le hA4) hK
  have hle1 : FbEVc * A ^ 4 * K ≤ FbEVc * A ^ 4 * K * (α + 1) := by
    simpa using mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ α + 1) hX
  have hle2 : FbEVc * A ^ 4 * K * (α + 1) ≤ (FbEVc + 1) * A ^ 4 * K * (α + 1) := by
    have hα1 : (0 : ℝ) ≤ α + 1 := by linarith
    have hK4 : (0 : ℝ) ≤ A ^ 4 * K := mul_nonneg hA4 hK
    have h1 : FbEVc * (A ^ 4 * K) ≤ (FbEVc + 1) * (A ^ 4 * K) :=
      mul_le_mul_of_nonneg_right (by linarith) hK4
    calc FbEVc * A ^ 4 * K * (α + 1) = FbEVc * (A ^ 4 * K) * (α + 1) := by ring
      _ ≤ (FbEVc + 1) * (A ^ 4 * K) * (α + 1) := mul_le_mul_of_nonneg_right h1 hα1
      _ = (FbEVc + 1) * A ^ 4 * K * (α + 1) := by ring
  have hle : FbEVc * A ^ 4 * K ≤ (FbEVc + 1) * A ^ 4 * K * (α + 1) := hle1.trans hle2
  exact ⟨Fb.mono le_rfl hle hlin.1, Fb.mono le_rfl hle hlin.2⟩

end Work.FTS.PhiStar.StarPkgo2Aux
