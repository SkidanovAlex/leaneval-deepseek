import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.BogFSKernel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

/-!
# `Work.BoseBogFS.tauSc_le_fsTau` — the scaled honest symbol is below FS's `τ̃`

The proof is deliberately *hypothesis-light*: no sign of the parameters `s, d, ℓ` is needed.
The two ingredients are

* the pointwise profile bound `τ̃(r) ≤ (max 0 (r−1))²` (`Work.BoseBoxFock.tauProf_le_max_sq`),
  which for **every** real `c` (positive, zero or negative) gives
  `c²·τ̃(x/c) ≤ (max 0 (x−c))²` for `x ≥ 0` (`sq_mul_tauProf_le_all`: for `c > 0` multiply the
  bound by `c²`; for `c ≤ 0` the left side vanishes, because `τ̃` is nonnegative and the
  profile is *zero* below `1`), and
* the scaling identity `P⁻¹(max 0 (√P·r − c))² = (max 0 (r − c₁))²` for `√P·c₁ = c`
  (`invP_max_sq`), which converts the physical thresholds `(2sℓ)⁻¹, (2dsℓ)⁻¹` into FS's
  scaled thresholds `c₁, c₂`.

Both weights `1−ε_T` and `ε_T` are nonnegative by the hypotheses, so the two terms may be
estimated separately.  The only parameter identity needed is `√P·bogC₁ = (2sℓ)⁻¹`
(and likewise for `bogC₂`), i.e. `√P·(2sℓ√P)⁻¹ = (2sℓ)⁻¹` (`sqrt_mul_inv_cancel`).
-/

/-- `√P·(c·√P)⁻¹ = c⁻¹`: the factor `√P` cancels, for `P > 0` and **any** real `c`
(no hypothesis on `c`; if `c = 0` both sides are `0`). -/
private lemma sqrt_mul_inv_cancel {P c : ℝ} (hP : 0 < P) :
    Real.sqrt P * (c * Real.sqrt P)⁻¹ = c⁻¹ := by
  have hS : Real.sqrt P ≠ 0 := (Real.sqrt_pos.mpr hP).ne'
  calc Real.sqrt P * (c * Real.sqrt P)⁻¹
      = Real.sqrt P * (c⁻¹ * (Real.sqrt P)⁻¹) := by rw [mul_inv]
    _ = (Real.sqrt P * c⁻¹) * (Real.sqrt P)⁻¹ := (mul_assoc _ _ _).symm
    _ = (c⁻¹ * Real.sqrt P) * (Real.sqrt P)⁻¹ := by rw [mul_comm (Real.sqrt P) c⁻¹]
    _ = c⁻¹ * (Real.sqrt P * (Real.sqrt P)⁻¹) := mul_assoc _ _ _
    _ = c⁻¹ := by rw [mul_inv_cancel₀ hS, mul_one]

/-- `max 0 (a·y) = a·(max 0 y)` for `a ≥ 0`. -/
private lemma max_zero_mul {a y : ℝ} (ha : 0 ≤ a) : max 0 (a * y) = a * max 0 y := by
  rw [mul_max_of_nonneg _ _ ha, mul_zero]

/-- **The one-variable core, valid for every real `c`.**  For `x ≥ 0`,
`c²·τ̃(x/c) ≤ (max 0 (x−c))²`.

For `c > 0` this is exactly `Work.BoseBoxFock.tauProf_le_max_sq` multiplied by `c² ≥ 0`.
For `c ≤ 0` the argument `x/c` is `≤ 0 ≤ 1`, so the profile vanishes there
(`Work.BoseBoxFock.tauProf_eq_zero_of_le_one`) and the left side is `0`. -/
private lemma sq_mul_tauProf_le_all {c x : ℝ} (hx : 0 ≤ x) :
    c ^ 2 * Work.BoseBoxFock.tauProf (x / c) ≤ (max 0 (x - c)) ^ 2 := by
  rcases lt_or_ge 0 c with hc | hc
  · have h := Work.BoseBoxFock.tauProf_le_max_sq (x / c)
    have hcm : c * max 0 (x / c - 1) = max 0 (x - c) := by
      rw [mul_max_of_nonneg _ _ hc.le, mul_zero, mul_sub, mul_one,
        mul_div_cancel₀ x (ne_of_gt hc)]
    calc c ^ 2 * Work.BoseBoxFock.tauProf (x / c)
        ≤ c ^ 2 * (max 0 (x / c - 1)) ^ 2 := mul_le_mul_of_nonneg_left h (sq_nonneg c)
      _ = (max 0 (x - c)) ^ 2 := by rw [← hcm]; ring
  · have h0 : Work.BoseBoxFock.tauProf (x / c) = 0 :=
      Work.BoseBoxFock.tauProf_eq_zero_of_le_one
        (le_trans (div_nonpos_of_nonneg_of_nonpos hx hc) (by norm_num))
    rw [h0, mul_zero]
    exact sq_nonneg _

/-- **The `P`-scaling of a threshold.**  If `√P·c₁ = c` then
`P⁻¹·(max 0 (√P·r − c))² = (max 0 (r − c₁))²`: the factor `√P` moves from the threshold to
the variable, and `P⁻¹` cancels the `P` created by squaring. -/
private lemma invP_max_sq {P c c1 r : ℝ} (hP : 0 < P)
    (hc : Real.sqrt P * c1 = c) :
    P⁻¹ * (max 0 (Real.sqrt P * r - c)) ^ 2 = (max 0 (r - c1)) ^ 2 := by
  have hS : 0 < Real.sqrt P := Real.sqrt_pos.mpr hP
  have h1 : Real.sqrt P * r - c = Real.sqrt P * (r - c1) := by rw [← hc, mul_sub]
  rw [h1, max_zero_mul hS.le, mul_pow, Real.sq_sqrt hP.le]
  rw [inv_mul_cancel_left₀ (ne_of_gt hP)]

/-- **The scaled symbol comparison at the abstract data.**  With `P > 0`, `0 ≤ ε_T ≤ 1` and
thresholds related by `√P·c₁ = (2sℓ)⁻¹`, `√P·c₂ = (2dsℓ)⁻¹`,
`P⁻¹·τ_s(√P • t) ≤ fsTau ε_T c₁ c₂ ‖t‖` where `τ_s = tauSm ε_T s d ℓ` is the physical symbol. -/
private lemma key {P eT s d ℓ : ℝ} (hP : 0 < P) (heT0 : 0 ≤ eT) (heT1 : eT ≤ 1)
    (c1 c2 : ℝ) (hc1 : Real.sqrt P * c1 = (2 * s * ℓ)⁻¹)
    (hc2 : Real.sqrt P * c2 = (2 * d * s * ℓ)⁻¹) (t : EuclideanSpace ℝ (Fin 3)) :
    P⁻¹ * Work.BoseBoxFock.tauSm eT s d ℓ (Real.sqrt P • t)
      ≤ Work.BoseB6.fsTau eT c1 c2 ‖t‖ := by
  have hx : ‖Real.sqrt P • t‖ = Real.sqrt P * ‖t‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg P)]
  have htn : 0 ≤ ‖t‖ := norm_nonneg t
  -- the two termwise estimates (the weights `1 − eT` and `eT` are attached afterwards)
  have hA : P⁻¹ * (((2 * s * ℓ)⁻¹) ^ 2
        * Work.BoseBoxFock.tauProf (Real.sqrt P * ‖t‖ / (2 * s * ℓ)⁻¹))
      ≤ (max 0 (‖t‖ - c1)) ^ 2 := by
    have h1 := sq_mul_tauProf_le_all (c := (2 * s * ℓ)⁻¹) (x := Real.sqrt P * ‖t‖)
      (mul_nonneg (Real.sqrt_nonneg P) htn)
    have e1 := invP_max_sq (c := (2 * s * ℓ)⁻¹) (c1 := c1) (r := ‖t‖) hP hc1
    calc P⁻¹ * (((2 * s * ℓ)⁻¹) ^ 2
            * Work.BoseBoxFock.tauProf (Real.sqrt P * ‖t‖ / (2 * s * ℓ)⁻¹))
        ≤ P⁻¹ * (max 0 (Real.sqrt P * ‖t‖ - (2 * s * ℓ)⁻¹)) ^ 2 :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hP.le)
      _ = (max 0 (‖t‖ - c1)) ^ 2 := e1
  have hB : P⁻¹ * (((2 * d * s * ℓ)⁻¹) ^ 2
        * Work.BoseBoxFock.tauProf (Real.sqrt P * ‖t‖ / (2 * d * s * ℓ)⁻¹))
      ≤ (max 0 (‖t‖ - c2)) ^ 2 := by
    have h1 := sq_mul_tauProf_le_all (c := (2 * d * s * ℓ)⁻¹) (x := Real.sqrt P * ‖t‖)
      (mul_nonneg (Real.sqrt_nonneg P) htn)
    have e1 := invP_max_sq (c := (2 * d * s * ℓ)⁻¹) (c1 := c2) (r := ‖t‖) hP hc2
    calc P⁻¹ * (((2 * d * s * ℓ)⁻¹) ^ 2
            * Work.BoseBoxFock.tauProf (Real.sqrt P * ‖t‖ / (2 * d * s * ℓ)⁻¹))
        ≤ P⁻¹ * (max 0 (Real.sqrt P * ‖t‖ - (2 * d * s * ℓ)⁻¹)) ^ 2 :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hP.le)
      _ = (max 0 (‖t‖ - c2)) ^ 2 := e1
  -- unfold both symbols; `max (·) 0` is turned into `max 0 (·)` to match `hA`, `hB`
  rw [Work.BoseBoxFock.tauSm, Work.BoseB6.fsTau, hx, abs_of_nonneg htn,
    max_comm (‖t‖ - c1) 0, max_comm (‖t‖ - c2) 0]
  have hε : (0 : ℝ) ≤ 1 - eT := by linarith
  rw [mul_add]
  have p1 : P⁻¹ * ((1 - eT) * ((2 * s * ℓ)⁻¹) ^ 2
        * Work.BoseBoxFock.tauProf (Real.sqrt P * ‖t‖ / (2 * s * ℓ)⁻¹))
      = (1 - eT) * (P⁻¹ * (((2 * s * ℓ)⁻¹) ^ 2
        * Work.BoseBoxFock.tauProf (Real.sqrt P * ‖t‖ / (2 * s * ℓ)⁻¹))) := by ring
  have p2 : P⁻¹ * (eT * ((2 * d * s * ℓ)⁻¹) ^ 2
        * Work.BoseBoxFock.tauProf (Real.sqrt P * ‖t‖ / (2 * d * s * ℓ)⁻¹))
      = eT * (P⁻¹ * (((2 * d * s * ℓ)⁻¹) ^ 2
        * Work.BoseBoxFock.tauProf (Real.sqrt P * ‖t‖ / (2 * d * s * ℓ)⁻¹))) := by ring
  rw [p1, p2]
  exact add_le_add (mul_le_mul_of_nonneg_left hA hε) (mul_le_mul_of_nonneg_left hB heT0)

/-- **The honest scaled kinetic symbol is dominated by FS's `τ̃`.**  With
`c₁ = bogC1 v ρ μ = (2 s ℓ √(ρa))⁻¹` and `c₂ = bogC2 v ρ μ = (2 d s ℓ √(ρa))⁻¹`,
unfolding `tauSc`, `tauAt`, `tauSm` gives
`tauSc v ρ μ t = (1−ε_T)c₁²tauProf(‖t‖/c₁) + ε_T c₂²tauProf(‖t‖/c₂)`, and since the chosen
profile satisfies `tauProf u ≤ (max 0 (u−1))²` (`Work.BoseBoxFock.tauProf_le_max_sq`),
`tauSc v ρ μ t ≤ fsTau ε_T c₁ c₂ ‖t‖` **provided `0 ≤ ε_T ≤ 1`** (both weights must be
nonnegative; this is `ParamsOK`'s diluteness clause and is supplied here explicitly).
Consequently the `τ`-increment of the Bogoliubov bracket is negative and can be discarded in
the comparison with `fsI1`. -/
theorem tauSc_le_fsTau {v : EuclideanSpace ℝ (Fin 3) → ℝ} {ρ μ : ℝ} (hρ : 0 < ρ)
    (hP : 0 < ρ * _root_.BoseGases.a v)
    (heT0 : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
    (heT1 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT ≤ 1)
    (t : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseBogFS.tauSc v ρ μ t
      ≤ Work.BoseB6.fsTau ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
          (Work.BoseBogFS.bogC1 v ρ μ) (Work.BoseBogFS.bogC2 v ρ μ) ‖t‖ := by
  have hc1 : Real.sqrt (ρ * _root_.BoseGases.a v) * bogC1 v ρ μ
      = (2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
          * Work.BoseFixR.ell v μ)⁻¹ := by
    rw [bogC1]
    exact sqrt_mul_inv_cancel hP
  have hc2 : Real.sqrt (ρ * _root_.BoseGases.a v) * bogC2 v ρ μ
      = (2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
          * Work.BoseFixR.ell v μ)⁻¹ := by
    rw [bogC2]
    exact sqrt_mul_inv_cancel hP
  rw [tauSc, tauAt]
  exact key hP heT0 heT1 _ _ hc1 hc2 t

end Work.BoseBogFS
