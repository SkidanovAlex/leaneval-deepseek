/-
# `Submission.Work.FIArea5.S16Hecke.heckeFE_defs`

Definitions and definitional lemmas for the theta transformation of the Hecke `L`-function of
`ℚ(i)`: the constants `B = 16d²`, `c = 1/√B`, the cut integrals `thetaCut`, `thetaCutStar`,
`thetaCutLow`, the objects `heckeA`, `heckeE`, `thetaCθ`, `heckeXi`, `heckeLambda`, the theta law
`thetaHol_law` for `thetaHol`, the constant identity `thetaCθ_mul_star`, and the star-relations.
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.ThetaDefs

set_option maxHeartbeats 1000000

namespace Work.FIArea5.S16Hecke

open MeasureTheory Set Filter
open scoped BigOperators ComplexConjugate Topology
open Work.FIPlan

noncomputable section

/-! ## Basic constants and the theta summand -/

/-- `B = 16d²`: the scaling constant of the theta law `u ↦ 1/(Bu)`. -/
def thetaB (d : ℕ) : ℝ := 16 * (d : ℝ) ^ 2

/-- `c = 1/(4d) = 1/√B`: the fixed point of the involution `u ↦ 1/(B u)` on `(0,∞)`. -/
def thetaC (d : ℕ) : ℝ := 1 / (4 * (d : ℝ))

/-- The summand of `thetaHol`: `z ↦ χ(z)z^m exp(-πu|z|²)` on primary `z`, `0` elsewhere. -/
def thetaSummand (chi : GaussianInt → ℂ) (m : ℕ) (u : ℝ) (z : GaussianInt) : ℂ := by
  classical
  exact if IsPrimary z then chi z * (z.toComplex) ^ m * Complex.exp (-Real.pi * u * (gnorm z : ℝ))
    else 0

lemma thetaHol_eq_tsum (chi : GaussianInt → ℂ) (m : ℕ) (u : ℝ) :
    thetaHol chi m u = ∑' z : GaussianInt, thetaSummand chi m u z := by
  classical
  simp only [thetaHol, thetaSummand]

/-- `star` of a real integer power of a real number, as a complex number. -/
lemma star_ofReal_zpow (v : ℝ) (n : ℤ) : star ((v : ℂ) ^ n) = (v : ℂ) ^ n := by
  rw [← Complex.ofReal_zpow]
  exact Complex.conj_ofReal _

lemma thetaB_pos {d : ℕ} (hd : 1 ≤ d) : 0 < thetaB d := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  rw [thetaB]
  positivity

lemma thetaC_pos {d : ℕ} (hd : 1 ≤ d) : 0 < thetaC d := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  rw [thetaC]
  positivity

/-- `c = 1/√B` is the fixed point of `u ↦ 1/(Bu)`. -/
lemma thetaC_inv {d : ℕ} (hd : 1 ≤ d) : 1 / (thetaB d * thetaC d) = thetaC d := by
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  rw [thetaB, thetaC]
  field_simp
  norm_num

/-- The exponent appearing in the theta law: `-(m+1)`. -/
lemma neg_succ_eq (m : ℕ) : (-(m : ℤ) - 1 : ℤ) = -((m : ℤ) + 1) := by ring

/-! ## The cut integrals and the completed `L`-function -/

/-- The `(c,∞)`-truncation of `thetaHol`, `c = 1/(4d)`. -/
def thetaCut (d : ℕ) (chi : GaussianInt → ℂ) (m : ℕ) : ℝ → ℂ :=
  fun u => if thetaC d < u then thetaHol chi m u else 0

/-- The `(c,∞)`-truncation of `conj thetaHol`. -/
def thetaCutStar (d : ℕ) (chi : GaussianInt → ℂ) (m : ℕ) : ℝ → ℂ :=
  fun v => if thetaC d < v then star (thetaHol chi m v) else 0

/-- The `(0,c)`-truncation of `thetaHol`. -/
def thetaCutLow (d : ℕ) (chi : GaussianInt → ℂ) (m : ℕ) : ℝ → ℂ :=
  fun u => if u < thetaC d then thetaHol chi m u else 0

/-- `A(t) = ∫_c^∞ θ(u)u^{t-1}du`, as a Mellin transform of the cutoff `thetaCut`. -/
def heckeA (d : ℕ) (chi : GaussianInt → ℂ) (m : ℕ) (t : ℂ) : ℂ :=
  mellin (thetaCut d chi m) t

/-- `E(t) = ∫_c^∞ conj θ(v) v^{m-t}dv`. -/
def heckeE (d : ℕ) (chi : GaussianInt → ℂ) (m : ℕ) (t : ℂ) : ℂ :=
  mellin (thetaCutStar d chi m) (m + 1 - t)

/-- The value of the theta law: `c_θ = A conj U/U`. -/
def thetaCθ (U A : ℂ) : ℂ := A * star U / U

/-- `Ξ(t) = A(t) + c_θ B^{m+1-t} E(t)`. -/
def heckeXi (d : ℕ) (chi : GaussianInt → ℂ) (m : ℕ) (U A : ℂ) (t : ℂ) : ℂ :=
  heckeA d chi m t + thetaCθ U A * ((thetaB d : ℂ) ^ ((m : ℂ) + 1 - t)) * heckeE d chi m t

/-- `Λ(s) = (4d)^s π^{m/2} Ξ(s+m/2)`: the completed Hecke `L`-function. -/
def heckeLambda (d : ℕ) (chi : GaussianInt → ℂ) (m : ℕ) (U A : ℂ) (s : ℂ) : ℂ :=
  (((4 * d : ℕ)) : ℂ) ^ s * ((Real.pi : ℂ) ^ ((m : ℂ) / 2)) *
    heckeXi d chi m U A (s + (m : ℂ) / 2)

/-! ## The theta law for `thetaHol` -/

/-- **The theta law for `thetaHol`**: dividing the law for `thetaOdd` by the unit sum `U`. -/
theorem thetaHol_law (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (m : ℕ)
    (U : ℂ) (hU : U ≠ 0) (A : ℂ)
    (htheta : ∀ u : ℝ, 0 < u → thetaOdd chi m u = A * ((u : ℂ) ^ (-(m : ℤ) - 1)) *
        star (thetaOdd chi m (1 / (16 * (d : ℝ) ^ 2 * u))))
    (hunit : ∀ u : ℝ, thetaOdd chi m u = U * thetaHol chi m u) :
    ∀ u : ℝ, 0 < u → thetaHol chi m u = (A * star U / U) * ((u : ℂ) ^ (-(m : ℤ) - 1)) *
        star (thetaHol chi m (1 / (16 * (d : ℝ) ^ 2 * u))) := by
  intro u hu
  have h1 := htheta u hu
  rw [hunit u, hunit (1 / (16 * (d : ℝ) ^ 2 * u))] at h1
  -- `h1 : U * θ u = A u^n (star (U * θ v))`
  have h2 : U * thetaHol chi m u
      = A * ((u : ℂ) ^ (-(m : ℤ) - 1)) *
          (star U * star (thetaHol chi m (1 / (16 * (d : ℝ) ^ 2 * u)))) := by
    rw [h1, star_mul]
    ring
  calc thetaHol chi m u
      = U⁻¹ * (U * thetaHol chi m u) := by rw [inv_mul_cancel_left₀ hU]
    _ = U⁻¹ * (A * ((u : ℂ) ^ (-(m : ℤ) - 1)) *
          (star U * star (thetaHol chi m (1 / (16 * (d : ℝ) ^ 2 * u))))) := by rw [h2]
    _ = (A * star U / U) * ((u : ℂ) ^ (-(m : ℤ) - 1)) *
          star (thetaHol chi m (1 / (16 * (d : ℝ) ^ 2 * u))) := by ring

/-- Twice the theta law: `c_θ · conj c_θ · B^{m+1} = 1` whenever `thetaHol` is not identically
zero, where `c_θ = A conj U/U` and `B = 16d²`. -/
theorem thetaCθ_mul_star (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (m : ℕ)
    (U : ℂ) (hU : U ≠ 0) (A : ℂ)
    (hlaw : ∀ u : ℝ, 0 < u → thetaHol chi m u = (A * star U / U) * ((u : ℂ) ^ (-(m : ℤ) - 1)) *
        star (thetaHol chi m (1 / (16 * (d : ℝ) ^ 2 * u))))
    (hne : ∃ u : ℝ, 0 < u ∧ thetaHol chi m u ≠ 0) :
    (A * star U / U) * star (A * star U / U) *
        (((16 * (d : ℝ) ^ 2 : ℝ) : ℂ) ^ (m + 1)) = 1 := by
  obtain ⟨u, hu, hu0⟩ := hne
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  set B : ℝ := 16 * (d : ℝ) ^ 2 with hBdef
  have hB : 0 < B := by rw [hBdef]; positivity
  have hB0 : B ≠ 0 := ne_of_gt hB
  have hu0' : u ≠ 0 := ne_of_gt hu
  set v : ℝ := 1 / (B * u) with hvdef
  have hv : 0 < v := by rw [hvdef]; positivity
  have hvu : 1 / (B * v) = u := by rw [hvdef]; field_simp
  have huv : u * v = 1 / B := by rw [hvdef]; field_simp
  -- the two laws
  have h1 := hlaw u hu
  have h2 := hlaw v hv
  rw [hvu] at h2
  have h3 : star (thetaHol chi m v)
      = star (A * star U / U) * ((v : ℂ) ^ (-(m : ℤ) - 1)) * thetaHol chi m u := by
    rw [h2, star_mul, star_mul, star_star, star_ofReal_zpow]
    ring
  -- combine the two laws
  have h4 : thetaHol chi m u
      = (A * star U / U) * star (A * star U / U) *
          (((u : ℂ) ^ (-(m : ℤ) - 1)) * ((v : ℂ) ^ (-(m : ℤ) - 1))) * thetaHol chi m u := by
    calc thetaHol chi m u
        = (A * star U / U) * ((u : ℂ) ^ (-(m : ℤ) - 1)) * star (thetaHol chi m v) := h1
      _ = (A * star U / U) * ((u : ℂ) ^ (-(m : ℤ) - 1)) *
            (star (A * star U / U) * ((v : ℂ) ^ (-(m : ℤ) - 1)) * thetaHol chi m u) := by rw [h3]
      _ = (A * star U / U) * star (A * star U / U) *
            (((u : ℂ) ^ (-(m : ℤ) - 1)) * ((v : ℂ) ^ (-(m : ℤ) - 1))) * thetaHol chi m u := by ring
  have hreal : u ^ (-(m : ℤ) - 1) * v ^ (-(m : ℤ) - 1) = B ^ (m + 1) := by
    rw [← mul_zpow, huv, one_div, inv_zpow, ← zpow_neg]
    rw [show (-(-(m : ℤ) - 1)) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have hpow : ((u : ℂ) ^ (-(m : ℤ) - 1)) * ((v : ℂ) ^ (-(m : ℤ) - 1))
      = (((B) ^ (m + 1) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_zpow, ← Complex.ofReal_zpow, ← Complex.ofReal_mul, hreal]
  have h5 : ((A * star U / U) * star (A * star U / U) * (((B) ^ (m + 1) : ℝ) : ℂ)) *
      thetaHol chi m u = 1 * thetaHol chi m u := by
    rw [← hpow, ← h4]; ring
  have h6 := mul_right_cancel₀ hu0 h5
  rw [Complex.ofReal_pow] at h6
  exact h6

/-! ## Star of a Mellin transform, and the reflection relations of the cut integrals -/

/-- `conj (u^z) = u^(conj z)` for `u ≥ 0` real. -/
lemma starRingEnd_cpow_ofReal {u : ℝ} (hu : 0 ≤ u) (z : ℂ) :
    (starRingEnd ℂ) ((u : ℂ) ^ z) = (u : ℂ) ^ ((starRingEnd ℂ) z) := by
  have harg : ((u : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hu]; exact Real.pi_ne_zero.symm
  rw [Complex.cpow_conj ((u : ℂ)) z harg, Complex.conj_ofReal]

/-- `star` of a Mellin transform: `conj (mellin f t) = mellin (conj ∘ f) (conj t)`. -/
lemma star_mellin (f : ℝ → ℂ) (t : ℂ) :
    star (mellin f t) = mellin (fun u => star (f u)) (star t) := by
  rw [mellin, mellin]
  conv_lhs => rw [Complex.star_def]
  set I := ∫ (x : ℝ), (x:ℂ) ^ (t - 1) • f x ∂(MeasureTheory.volume.restrict (Set.Ioi 0)) with hI
  have key : (starRingEnd ℂ) I = Complex.conjCLE I := rfl
  rw [key, ← Complex.conjCLE.integral_comp_comm]
  rw [show (∫ (x : ℝ) in Set.Ioi 0, (x:ℂ) ^ (star t - 1) • star (f x))
      = ∫ (x : ℝ), (x:ℂ) ^ (star t - 1) • star (f x)
          ∂(MeasureTheory.volume.restrict (Set.Ioi 0)) from rfl]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
  simp only [Complex.conjCLE_apply]
  rw [smul_eq_mul, map_mul, starRingEnd_cpow_ofReal (le_of_lt hu), map_sub, map_one]
  rw [Complex.star_def, smul_eq_mul]

lemma star_thetaCut (d : ℕ) (chi : GaussianInt → ℂ) (m : ℕ) :
    (fun u => star (thetaCut d chi m u)) = thetaCutStar d chi m := by
  funext u
  simp only [thetaCut, thetaCutStar]
  split <;> simp

lemma star_thetaCutStar (d : ℕ) (chi : GaussianInt → ℂ) (m : ℕ) :
    (fun u => star (thetaCutStar d chi m u)) = thetaCut d chi m := by
  funext u
  simp only [thetaCut, thetaCutStar]
  split <;> simp

/-- `conj A(m+1-conj t) = E(t)`. -/
theorem star_heckeA (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (m : ℕ) (t : ℂ) :
    star (heckeA d chi m ((m : ℂ) + 1 - star t)) = heckeE d chi m t := by
  rw [heckeA, heckeE, star_mellin]
  have h1 : star ((m : ℂ) + 1 - star t) = (m : ℂ) + 1 - t := by
    rw [star_sub, star_add, star_one, star_natCast, star_star]
  rw [h1, star_thetaCut]

/-- `conj E(m+1-conj t) = A(t)`. -/
theorem star_heckeE (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (m : ℕ) (t : ℂ) :
    star (heckeE d chi m ((m : ℂ) + 1 - star t)) = heckeA d chi m t := by
  rw [heckeE, heckeA]
  have h1 : (m : ℂ) + 1 - ((m : ℂ) + 1 - star t) = star t := by ring
  rw [h1, star_mellin, star_star, star_thetaCutStar]

/-! ## Splitting the Mellin integral at `c` -/

/-- The Mellin integral splits into the two cuts `(0,c)` and `(c,∞)` (the two integrands differ
only at the single point `u = c`). -/
theorem mellin_thetaHol_eq_split (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (m : ℕ) (t : ℂ)
    (hconvlow : MellinConvergent (thetaCutLow d chi m) t)
    (hconv : MellinConvergent (thetaCut d chi m) t) :
    mellin (thetaHol chi m) t = mellin (thetaCutLow d chi m) t + mellin (thetaCut d chi m) t := by
  rw [mellin, mellin, mellin]
  have hpt : ∀ u : ℝ, u ≠ thetaC d → (u : ℂ) ^ (t - 1) • thetaHol chi m u
      = (u : ℂ) ^ (t - 1) • thetaCutLow d chi m u + (u : ℂ) ^ (t - 1) • thetaCut d chi m u := by
    intro u hu
    rcases lt_trichotomy u (thetaC d) with h | h | h
    · simp only [thetaCutLow, thetaCut]
      rw [if_pos h, if_neg (not_lt.mpr h.le), smul_zero, add_zero]
    · exact absurd h hu
    · simp only [thetaCutLow, thetaCut]
      rw [if_neg (not_lt.mpr h.le), if_pos h, smul_zero, zero_add]
  have hae : ∀ᵐ u : ℝ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), u ∈ Set.Ioi 0 →
      (u : ℂ) ^ (t - 1) • thetaHol chi m u
        = (u : ℂ) ^ (t - 1) • thetaCutLow d chi m u + (u : ℂ) ^ (t - 1) • thetaCut d chi m u := by
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_singleton (thetaC d))
    intro u hu
    by_contra huc
    exact hu (fun _ => hpt u huc)
  rw [MeasureTheory.setIntegral_congr_ae measurableSet_Ioi hae]
  rw [MeasureTheory.integral_add hconvlow hconv]

end

end Work.FIArea5.S16Hecke
