import Mathlib.Analysis.PSeries
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.Work.BoseB4.thetaExp_lattice
import Submission.Work.BoseB7AK.Q2Gram.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7AK.Q2Gram.chiSq_fourier_sum` — Poisson summation for `χ²`

This file proves the lattice Fourier sum

`∑_{m ∈ ℤ³} ∫_{ℝ³} χ(x)² cos(2π m·x) dx = χ(0)²`  (`chiSq_fourier_sum`),

i.e. Poisson summation for the compactly supported smooth function `χ²` on the unit lattice.
The (periodic) function `P` on `𝕋³` obtained by periodizing `χ²` (`Defs.P`) has Fourier
coefficients `∫ χ²(x) e^{-2πi m·x} dx` (`mFourierCoeff_P`); they are absolutely summable
(Schwartz decay, `summable_coeff`), so the Fourier series converges to `P` at the origin, where
`P(0) = ∑_n χ(n)² = χ(0)²`.
-/

noncomputable section

open MeasureTheory Complex Filter Topology
open scoped BigOperators FourierTransform RealInnerProductSpace ContDiff

namespace Work.BoseB7AK.Q2Gram

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Inner-product identities -/

lemma inner_lat (m : Fin 3 → ℤ) (x : E3) : inner ℝ (lat m) x = ∑ i, (m i : ℝ) * x i := by
  rw [lat, PiLp.inner_apply]
  simp [kv, mul_comm]

/-- `Work.BoseB4.vec m = 2π • lat m`. -/
lemma vec_eq_smul (m : Fin 3 → ℤ) : Work.BoseB4.vec m = (2 * Real.pi) • lat m := by
  rw [lat, Work.BoseB4.vec]
  ext i
  simp [kv, mul_comm]

lemma inner_vec (m : Fin 3 → ℤ) (x : E3) :
    inner ℝ (Work.BoseB4.vec m) x = 2 * Real.pi * ∑ i, (m i : ℝ) * x i := by
  rw [vec_eq_smul, real_inner_smul_left, inner_lat]

/-! ## 2. The torus monomial `mFourier (-m)` at a point of the cube -/

/-- `mFourier (-m)` evaluated at the lift of a point of `ℝ³` is the exponential
`exp(-i ⟪vec m, x⟫)`. -/
lemma mFourier_neg_apply (m : Fin 3 → ℤ) (x : Fin 3 → ℝ) :
    UnitAddTorus.mFourier (-m) (fun i => (x i : UnitAddCircle))
      = Complex.exp (-(Complex.I * inner ℝ (Work.BoseB4.vec m) (WithLp.toLp 2 x))) := by
  have hfm : UnitAddTorus.mFourier (-m) (fun i => (x i : UnitAddCircle))
      = ∏ i : Fin 3, fourier ((-m) i) ((x i : UnitAddCircle)) := rfl
  rw [hfm, Finset.prod_congr rfl (fun i _ => by rw [fourier_coe_apply])]
  rw [← Complex.exp_sum]
  rw [show inner ℝ (Work.BoseB4.vec m) (WithLp.toLp 2 x)
      = 2 * Real.pi * ∑ i, (m i : ℝ) * x i from by
    rw [inner_vec]]
  congr 1
  set P : ℂ := 2 * ((Real.pi : ℝ) : ℂ) * Complex.I with hP
  have h1 : (∑ i : Fin 3, 2 * ((Real.pi : ℝ) : ℂ) * Complex.I * (((-m) i : ℤ) : ℂ)
        * ((x i : ℝ) : ℂ) / ((1 : ℝ) : ℂ))
      = ∑ i : Fin 3, -(P * (((m i : ℝ) : ℂ) * ((x i : ℝ) : ℂ))) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Pi.neg_apply]
    push_cast
    rw [hP]
    ring
  have h2 : (∑ i : Fin 3, -(P * (((m i : ℝ) : ℂ) * ((x i : ℝ) : ℂ))))
      = -(P * (∑ i : Fin 3, (((m i : ℝ) : ℂ) * ((x i : ℝ) : ℂ)))) := by
    rw [Finset.sum_neg_distrib, Finset.mul_sum]
  have h3 : (∑ i : Fin 3, (((m i : ℝ) : ℂ) * ((x i : ℝ) : ℂ)))
      = (((∑ i : Fin 3, (m i : ℝ) * x i) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    simp [Complex.ofReal_mul]
  calc (∑ i : Fin 3, 2 * ((Real.pi : ℝ) : ℂ) * Complex.I * (((-m) i : ℤ) : ℂ)
        * ((x i : ℝ) : ℂ) / ((1 : ℝ) : ℂ))
      = ∑ i : Fin 3, -(P * (((m i : ℝ) : ℂ) * ((x i : ℝ) : ℂ))) := h1
    _ = -(P * (∑ i : Fin 3, (((m i : ℝ) : ℂ) * ((x i : ℝ) : ℂ)))) := h2
    _ = -(P * (((∑ i : Fin 3, (m i : ℝ) * x i) : ℝ) : ℂ)) := by rw [h3]
    _ = -(Complex.I * (((2 * Real.pi) * ∑ i : Fin 3, (m i : ℝ) * x i : ℝ) : ℂ)) := by
        rw [hP]; push_cast; ring

/-! ## 3. `χ²` as a Schwartz function -/

lemma gE_contDiff : ContDiff ℝ ∞ gE :=
  Complex.ofRealCLM.contDiff.comp (Submission.BoseGases.chi_contDiff.pow 2)

lemma gE_hasCompactSupport : HasCompactSupport gE := by
  refine HasCompactSupport.mono Submission.BoseGases.chi_hasCompactSupport ?_
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro h
  exact hx (by simp [gE, h])

/-- `χ²` as a Schwartz function. -/
def G : SchwartzMap E3 ℂ := gE_hasCompactSupport.toSchwartzMap gE_contDiff

@[simp] lemma G_apply (x : E3) : (G : E3 → ℂ) x = gE x := rfl

/-- The Fourier transform of `G = χ²` at a lattice momentum. -/
lemma fourier_G_apply (m : Fin 3 → ℤ) :
    (SchwartzMap.fourierTransformCLM ℂ G) (lat m)
      = ∫ x : E3, Complex.exp (-(Complex.I * inner ℝ (Work.BoseB4.vec m) x)) * gE x := by
  rw [SchwartzMap.fourierTransformCLM_apply, SchwartzMap.fourier_coe, Real.fourier_eq']
  simp only [G_apply, smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with y
  congr 1
  congr 1
  rw [inner_vec, ← real_inner_comm y (lat m), inner_lat]
  push_cast
  ring

/-! ## 4. The Fourier coefficient of the periodization -/

lemma mFourierCoeff_P (m : Fin 3 → ℤ) :
    UnitAddTorus.mFourierCoeff P m =
      ∫ x : E3,
        ((Submission.BoseGases.chi x : ℂ)) ^ 2 *
          Complex.exp (-(Complex.I * (inner ℝ (Work.BoseB4.vec m) x))) := by
  have hset : {x : Fin 3 → ℝ | ∀ i : Fin 3, x i ∈ Set.Ioc (-(1 / 2)) (-(1 / 2) + 1)}
      = {x : Fin 3 → ℝ | ∀ i : Fin 3, x i ∈ Set.Ioc (-(1 / 2)) (1 / 2)} := by
    congr 1
    norm_num
  rw [UnitAddTorus.mFourierCoeff_eq_integral P m (fun _ : Fin 3 => -(1 / 2)), hset]
  have hpi : {x : Fin 3 → ℝ | ∀ i : Fin 3, x i ∈ Set.Ioc (-(1 / 2)) (1 / 2)}
      = Set.univ.pi (fun _ : Fin 3 => Set.Ioc (-(1 / 2)) (1 / 2)) := by
    ext x
    simp [Set.mem_pi]
  rw [hpi]
  have hcube : Set.EqOn
      (fun x : Fin 3 → ℝ => UnitAddTorus.mFourier (-m) (fun i => (x i : UnitAddCircle))
          • P (fun i => (x i : UnitAddCircle)))
      (fun x : Fin 3 → ℝ => Complex.exp (-(Complex.I * inner ℝ (Work.BoseB4.vec m)
          (WithLp.toLp 2 x))) * gE (WithLp.toLp 2 x))
      (Set.univ.pi (fun _ : Fin 3 => Set.Ioc (-(1 / 2)) (1 / 2))) := by
    intro x hx
    dsimp only
    have hx' : ∀ i : Fin 3, x i ∈ Set.Ioc (-(1 / 2)) (1 / 2) := by
      simpa [Set.mem_pi] using hx
    rw [mFourier_neg_apply m x, P_apply x, F_eq_of_mem_cube x hx', smul_eq_mul]
    rfl
  rw [setIntegral_congr_fun
    (s := Set.univ.pi (fun _ : Fin 3 => Set.Ioc (-(1 / 2)) (1 / 2)))
    (MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Ioc) hcube]
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
  · rw [(MeasurePreserving.integral_comp (PiLp.volume_preserving_ofLp (Fin 3))
        (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.measurableEmbedding
        (fun y : Fin 3 → ℝ => Complex.exp (-(Complex.I * inner ℝ (Work.BoseB4.vec m)
            (WithLp.toLp 2 y))) * gE (WithLp.toLp 2 y))).symm]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [WithLp.toLp_ofLp, gE_apply, Complex.ofReal_pow]
    exact mul_comm _ _
  · intro x hx
    have hchi : Submission.BoseGases.chi (WithLp.toLp 2 x) = 0 := by
      by_contra hne
      have hx' : x ∈ Set.univ.pi (fun _ : Fin 3 => Set.Ioc (-(1 / 2)) (1 / 2)) := by
        intro i _
        by_contra hi
        rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hi
        have hle : (1 / 2 : ℝ) ≤ |x i| := by
          rcases hi with h | h
          · rw [abs_of_nonpos (by linarith)]; linarith
          · rw [abs_of_pos (by linarith)]; linarith
        have h0 : g1 x = 0 := g1_zero_of_abs_coord x i hle
        simp only [g1, gE, Complex.ofReal_eq_zero, sq_eq_zero_iff] at h0
        exact hne h0
      exact hx hx'
    rw [show gE (WithLp.toLp 2 x) = 0 by simp [gE, hchi]]
    simp

/-! ## 5. Summability of the Fourier coefficients -/

/-- The lattice `ℤ³` reorganised as `(ℤ × ℤ) × ℤ`. -/
def latEquiv : (Fin 3 → ℤ) ≃ (ℤ × ℤ) × ℤ where
  toFun m := ((m 0, m 1), m 2)
  invFun p := ![p.1.1, p.1.2, p.2]
  left_inv m := by funext i; fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨⟨a, b⟩, c⟩; rfl

lemma abs_coord_le_norm_lat (m : Fin 3 → ℤ) (i : Fin 3) : |(m i : ℝ)| ≤ ‖lat m‖ := by
  have h := abs_apply_le_norm (lat m) i
  rw [WithLp.ofLp_toLp] at h
  simpa [lat, kv] using h

/-- The factorisation of the `4`-th power decay into three one-dimensional factors. -/
lemma one_add_norm_lat_rpow_le (m : Fin 3 → ℤ) :
    (1 + ‖lat m‖) ^ (-(4 : ℝ)) ≤ ∏ i : Fin 3, (1 + |(m i : ℝ)|) ^ (-(4 / 3) : ℝ) := by
  have hbase : (0 : ℝ) < 1 + ‖lat m‖ := by positivity
  have hsplit : (1 + ‖lat m‖) ^ (-(4 : ℝ))
      = ∏ i : Fin 3, (1 + ‖lat m‖) ^ (-(4 / 3) : ℝ) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.rpow_natCast,
      ← Real.rpow_mul hbase.le]
    norm_num
  rw [hsplit]
  refine Finset.prod_le_prod₀ (fun i _ => Real.rpow_nonneg (by positivity) _) (fun i _ => ?_)
  refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by norm_num)
  have h := abs_coord_le_norm_lat m i
  linarith

/-- The one-dimensional factor is summable. -/
lemma summable_one_add_abs_rpow :
    Summable (fun z : ℤ => (1 + |(z : ℝ)|) ^ (-(4 / 3) : ℝ)) := by
  have hbase : Summable (fun z : ℤ => |(z : ℝ)| ^ (-(4 / 3) : ℝ)) :=
    Real.summable_abs_int_rpow (by norm_num)
  have hdelta : Summable (fun z : ℤ => if z = 0 then (1 : ℝ) else 0) :=
    summable_of_ne_finset_zero (s := {0}) (by intro z hz; simp at hz; simp [hz])
  refine Summable.of_nonneg_of_le (fun z => Real.rpow_nonneg (by positivity) _) ?_
    (hbase.add hdelta)
  intro z
  rcases eq_or_ne z 0 with hz | hz
  · subst hz; norm_num
  · have hzpos : (0 : ℝ) < |(z : ℝ)| := by
      rw [abs_pos]; exact_mod_cast hz
    have hle : |(z : ℝ)| ≤ 1 + |(z : ℝ)| := by linarith [abs_nonneg (z : ℝ)]
    have h := Real.rpow_le_rpow_of_nonpos hzpos hle (by norm_num : (-(4 / 3) : ℝ) ≤ 0)
    simpa [if_neg hz] using h

/-- The product majorant over `ℤ³` is summable. -/
lemma summable_lattice_prod :
    Summable (fun m : Fin 3 → ℤ => ∏ i : Fin 3, (1 + |(m i : ℝ)|) ^ (-(4 / 3) : ℝ)) := by
  have h1d := summable_one_add_abs_rpow
  have h1dnn : 0 ≤ (fun z : ℤ => (1 + |(z : ℝ)|) ^ (-(4 / 3) : ℝ)) :=
    fun z => Real.rpow_nonneg (by positivity) _
  have h2 : Summable (fun p : ℤ × ℤ =>
      (1 + |(p.1 : ℝ)|) ^ (-(4 / 3) : ℝ) * (1 + |(p.2 : ℝ)|) ^ (-(4 / 3) : ℝ)) :=
    h1d.mul_of_nonneg h1d h1dnn h1dnn
  have h3 : Summable (fun p : (ℤ × ℤ) × ℤ =>
      ((1 + |(p.1.1 : ℝ)|) ^ (-(4 / 3) : ℝ) * (1 + |(p.1.2 : ℝ)|) ^ (-(4 / 3) : ℝ))
        * (1 + |(p.2 : ℝ)|) ^ (-(4 / 3) : ℝ)) :=
    h2.mul_of_nonneg h1d (fun p => mul_nonneg (h1dnn _) (h1dnn _)) h1dnn
  have h4 := (Equiv.summable_iff latEquiv).mpr h3
  rwa [show (fun m : Fin 3 → ℤ => ∏ i : Fin 3, (1 + |(m i : ℝ)|) ^ (-(4 / 3) : ℝ))
      = fun m => ((1 + |(m 0 : ℝ)|) ^ (-(4 / 3) : ℝ) * (1 + |(m 1 : ℝ)|) ^ (-(4 / 3) : ℝ))
        * (1 + |(m 2 : ℝ)|) ^ (-(4 / 3) : ℝ) from by
    funext m; rw [Fin.prod_univ_three]]

lemma summable_lattice_majorant (K : ℝ) (hK : 0 ≤ K) :
    Summable (fun m : Fin 3 → ℤ => K * (1 + ‖lat m‖) ^ (-(4 : ℝ))) := by
  refine Summable.of_nonneg_of_le (fun m => mul_nonneg hK (Real.rpow_nonneg (by positivity) _))
    (fun m => ?_) (summable_lattice_prod.mul_left K)
  exact mul_le_mul_of_nonneg_left (one_add_norm_lat_rpow_le m) hK

/-- Schwartz decay of the Fourier transform along the lattice `ℤ³`. -/
lemma summable_fourier_lattice (F : SchwartzMap E3 ℂ) :
    Summable (fun m : Fin 3 → ℤ => (SchwartzMap.fourierTransformCLM ℂ F) (lat m)) := by
  obtain ⟨C0, hC0pos, hC0⟩ := (SchwartzMap.fourierTransformCLM ℂ F).decay 0 0
  obtain ⟨C4, hC4pos, hC4⟩ := (SchwartzMap.fourierTransformCLM ℂ F).decay 4 0
  have hC0' : ∀ x : E3, ‖(SchwartzMap.fourierTransformCLM ℂ F) x‖ ≤ C0 := fun x => by
    have h := hC0 x
    rwa [norm_iteratedFDeriv_zero, pow_zero, one_mul] at h
  have hC4' : ∀ x : E3, ‖x‖ ^ 4 * ‖(SchwartzMap.fourierTransformCLM ℂ F) x‖ ≤ C4 := fun x => by
    have h := hC4 x
    rwa [norm_iteratedFDeriv_zero] at h
  set C : ℝ := max (16 * C0) (16 * C4) with hCdef
  have hCnn : 0 ≤ C := le_max_of_le_left (by positivity)
  have hbound : ∀ x : E3,
      ‖(SchwartzMap.fourierTransformCLM ℂ F) x‖ ≤ C / (1 + ‖x‖) ^ 4 := by
    intro x
    rcases lt_or_ge ‖x‖ 1 with hx | hx
    · have h1 : (1 + ‖x‖) ^ 4 ≤ 16 := by
        have h2 : 1 + ‖x‖ ≤ 2 := by linarith
        calc (1 + ‖x‖) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ (by positivity) h2 4
          _ = 16 := by norm_num
      have hpos : (0 : ℝ) < (1 + ‖x‖) ^ 4 := by positivity
      have h16 : (1 : ℝ) / 16 ≤ 1 / (1 + ‖x‖) ^ 4 := by
        rw [div_le_div_iff₀ (by norm_num) hpos]
        linarith
      calc ‖(SchwartzMap.fourierTransformCLM ℂ F) x‖ ≤ C0 := hC0' x
        _ = 16 * C0 * (1 / 16) := by ring
        _ ≤ 16 * C0 * (1 / (1 + ‖x‖) ^ 4) := mul_le_mul_of_nonneg_left h16 (by positivity)
        _ ≤ C * (1 / (1 + ‖x‖) ^ 4) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        _ = C / (1 + ‖x‖) ^ 4 := by ring
    · have hxpos : (0 : ℝ) < ‖x‖ := by linarith
      have h4 := hC4' x
      have hb : ‖(SchwartzMap.fourierTransformCLM ℂ F) x‖ ≤ C4 / ‖x‖ ^ 4 := by
        rw [le_div_iff₀ (by positivity)]
        linarith [h4]
      have hpos : (0 : ℝ) < (1 + ‖x‖) ^ 4 := by positivity
      have h2 : 1 + ‖x‖ ≤ 2 * ‖x‖ := by linarith
      have h16 : 1 / ‖x‖ ^ 4 ≤ 16 / (1 + ‖x‖) ^ 4 := by
        rw [div_le_div_iff₀ (by positivity) hpos]
        have h3 : (1 + ‖x‖) ^ 4 ≤ (2 * ‖x‖) ^ 4 := pow_le_pow_left₀ (by positivity) h2 4
        have h4' : (2 * ‖x‖) ^ 4 = 16 * ‖x‖ ^ 4 := by ring
        linarith
      calc ‖(SchwartzMap.fourierTransformCLM ℂ F) x‖ ≤ C4 / ‖x‖ ^ 4 := hb
        _ = C4 * (1 / ‖x‖ ^ 4) := by ring
        _ ≤ C4 * (16 / (1 + ‖x‖) ^ 4) := mul_le_mul_of_nonneg_left h16 (by positivity)
        _ = 16 * C4 / (1 + ‖x‖) ^ 4 := by ring
        _ ≤ C * (1 / (1 + ‖x‖) ^ 4) := by
            rw [show 16 * C4 / (1 + ‖x‖) ^ 4 = 16 * C4 * (1 / (1 + ‖x‖) ^ 4) by ring]
            exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
        _ = C / (1 + ‖x‖) ^ 4 := by ring
  have hmaj : Summable (fun m : Fin 3 → ℤ => C / (1 + ‖lat m‖) ^ 4) := by
    refine (summable_lattice_majorant C hCnn).congr (fun m => ?_)
    have hpow : (1 + ‖lat m‖) ^ (-(4 : ℝ)) = ((1 + ‖lat m‖) ^ 4)⁻¹ := by
      rw [show (-(4 : ℝ)) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by positivity),
        Real.rpow_natCast]
    rw [hpow, div_eq_mul_inv]
  exact hmaj.of_norm_bounded (fun m => hbound (lat m))

/-- The Fourier coefficient of `P` is the Fourier transform of `χ²` at the lattice point. -/
lemma coeff_eq_fourier (m : Fin 3 → ℤ) :
    UnitAddTorus.mFourierCoeff P m = (SchwartzMap.fourierTransformCLM ℂ G) (lat m) := by
  rw [mFourierCoeff_P, fourier_G_apply]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [gE_apply, Complex.ofReal_pow, mul_comm]

lemma summable_coeff : Summable (fun m : Fin 3 → ℤ => UnitAddTorus.mFourierCoeff P m) :=
  (summable_fourier_lattice G).congr (fun m => by rw [coeff_eq_fourier])

/-- Taking real parts commutes with the Bochner integral for complex-valued functions. -/
lemma integral_re_complex {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : Integrable f μ) : (∫ x, f x ∂μ).re = ∫ x, (f x).re ∂μ := by
  calc (∫ x, f x ∂μ).re = RCLike.re (∫ x, f x ∂μ) := rfl
    _ = ∫ x, RCLike.re (f x) ∂μ := (integral_re hf).symm
    _ = ∫ x, (f x).re ∂μ := rfl

/-- The value of the periodization at the origin is `χ(0)²`: only the `n = 0` translate survives. -/
lemma P_zero : P 0 = (((Submission.BoseGases.chi 0) ^ 2 : ℝ) : ℂ) := by
  have h : P 0 = F 0 := by
    show P (fun _ : Fin 3 => (0 : UnitAddCircle)) = F 0
    exact P_apply (0 : Fin 3 → ℝ)
  rw [h, F_zero]
  simp only [g1, gE_apply, WithLp.toLp_zero]

theorem chiSq_fourier_sum :
    HasSum (fun m : Fin 3 → ℤ =>
        ∫ x : EuclideanSpace ℝ (Fin 3),
          (Submission.BoseGases.chi x) ^ 2 * Real.cos (inner ℝ (Work.BoseB4.vec m) x))
      ((Submission.BoseGases.chi 0) ^ 2) := by
  have hcomplex : HasSum (fun m : Fin 3 → ℤ =>
      ∫ x : E3, ((Submission.BoseGases.chi x : ℂ)) ^ 2 *
        Complex.exp (-(Complex.I * inner ℝ (Work.BoseB4.vec m) x)))
      (((Submission.BoseGases.chi 0) ^ 2 : ℝ) : ℂ) := by
    have h := UnitAddTorus.hasSum_mFourier_series_apply_of_summable
      (f := (⟨P, P_continuous⟩ : C(UnitAddTorus (Fin 3), ℂ)))
      (by simpa using summable_coeff) (0 : UnitAddTorus (Fin 3))
    have hm : ∀ m : Fin 3 → ℤ, UnitAddTorus.mFourier m (0 : UnitAddTorus (Fin 3)) = 1 := by
      intro m
      simp [UnitAddTorus.mFourier]
    simp only [hm, smul_eq_mul, mul_one, ContinuousMap.coe_mk] at h
    rw [P_zero] at h
    simpa only [mFourierCoeff_P] using h
  have hre := Complex.hasSum_re hcomplex
  have hsum_eq : (fun m : Fin 3 → ℤ =>
        (∫ x : E3, ((Submission.BoseGases.chi x : ℂ)) ^ 2 *
          Complex.exp (-(Complex.I * inner ℝ (Work.BoseB4.vec m) x))).re)
      = fun m => ∫ x : E3,
          (Submission.BoseGases.chi x) ^ 2 * Real.cos (inner ℝ (Work.BoseB4.vec m) x) := by
    funext m
    have hint : Integrable (fun x : E3 => ((Submission.BoseGases.chi x : ℂ)) ^ 2 *
        Complex.exp (-(Complex.I * inner ℝ (Work.BoseB4.vec m) x))) := by
      refine Continuous.integrable_of_hasCompactSupport ?_ ?_
      · exact ((Complex.continuous_ofReal.comp
          Submission.BoseGases.chi_continuous).pow 2).mul
          (Complex.continuous_exp.comp
            (Continuous.neg (continuous_const.mul
              (Complex.continuous_ofReal.comp (continuous_const.inner continuous_id)))))
      · refine HasCompactSupport.mono Submission.BoseGases.chi_hasCompactSupport ?_
        intro x hx
        simp only [Function.mem_support] at hx ⊢
        intro h
        exact hx (by simp [h])
    rw [integral_re_complex hint]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    rw [Complex.mul_re]
    have h1 : (((Submission.BoseGases.chi x : ℂ)) ^ 2).re = (Submission.BoseGases.chi x)^2 := by
      rw [← Complex.ofReal_pow, Complex.ofReal_re]
    have h2 : (((Submission.BoseGases.chi x : ℂ)) ^ 2).im = 0 := by
      rw [← Complex.ofReal_pow, Complex.ofReal_im]
    have h3 : (Complex.exp (-(Complex.I * (inner ℝ (Work.BoseB4.vec m) x)))).re
        = Real.cos (inner ℝ (Work.BoseB4.vec m) x) := by
      rw [Complex.exp_re]
      have hr : (-(Complex.I * (inner ℝ (Work.BoseB4.vec m) x))).re = 0 := by simp
      have hi : (-(Complex.I * (inner ℝ (Work.BoseB4.vec m) x))).im
          = -(inner ℝ (Work.BoseB4.vec m) x) := by simp
      rw [hr, hi, Real.exp_zero, one_mul, Real.cos_neg]
    rw [h1, h2, h3]
    ring
  rw [hsum_eq, Complex.ofReal_re] at hre
  exact hre

end Work.BoseB7AK.Q2Gram
