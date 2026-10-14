import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-! ## Copies of elementary facts (the originals live in the work-in-progress
`Submission/Work/Spaces/WProductRule.lean`) -/

/-- `sin (2θ) ≥ 0` on `Iθ`. -/
theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `SmoothNbhd` implies `SmoothInt`. -/
theorem SmoothInt.of_smoothNbhd {g : ℝ → ℝ → ℝ} (h : SmoothNbhd g) : SmoothInt g := by
  refine ⟨h.mono ?_, ?_⟩
  · rintro ⟨z, θ⟩ ⟨hz, hθ⟩
    exact ⟨hz, by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  · intro θ hθ
    have hθ' : θ ∈ Set.Ioo (-1) (π / 2 + 1) :=
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have hmap : Set.MapsTo (fun z : ℝ => (z, θ)) (Set.Ioi (-1))
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1)) := fun z hz => ⟨hz, hθ'⟩
    exact h.comp (contDiffOn_id.prodMk contDiffOn_const) hmap

/-- The `z`-slices of the `D_θ`-iterates of a `SmoothInt` function are `C^∞` on `(-1,∞)`. -/
theorem DthIter_contDiffOn_slice' {f : ℝ → ℝ → ℝ} (hf : SmoothInt f) (a : ℕ) :
    ∀ θ ∈ Iθ, ContDiffOn ℝ ⊤ (fun z => DthIter a f z θ) (Set.Ioi (-1)) := by
  intro θ hθ
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; simpa using hf.2 θ hθ
  · obtain ⟨a', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp ha)
    by_cases hθi : θ ∈ Set.Ioo 0 (π / 2)
    · refine isOpen_Ioi.contDiffOn_iff.mpr (fun z' hz' => ?_)
      exact contDiffAt_slice_left (DthIter_contDiffAt f (a' + 1) (hf.contDiffAt_uncurry hz' hθi))
    · have hsin := sin_two_mul_eq_zero_of_mem_Iθ_of_not_mem_Ioo hθ hθi
      have hzero : (fun z => DthIter (a' + 1) f z θ) = fun _ => (0 : ℝ) :=
        funext fun z => DthIter_eq_zero_of_sin_eq_zero f a' hsin z
      rw [hzero]; exact contDiffOn_const

/-- The weighted angular factor is bounded by `2α² sin(2θ)^{2α/5-γ} + 2`. -/
theorem angular_weight_pointwise' {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ} (hθ : θ ∈ Iθ) :
    (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α)
      ≤ 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) + 2 := by
  have hp0_2 : 2 * α / 5 - gam α ≤ 0 := by rw [gam]; nlinarith
  have hs0 := sin_two_nonneg_Iθ hθ
  have hs1 := Real.sin_le_one (2 * θ)
  have hpow_nn : 0 ≤ (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) := Real.rpow_nonneg hs0 _
  have hsplit : (α + Real.sin (2 * θ)) ^ 2 ≤ 2 * α ^ 2 + 2 * (Real.sin (2 * θ)) ^ 2 := by
    nlinarith [sq_nonneg (α - Real.sin (2 * θ))]
  have hs2le : (Real.sin (2 * θ)) ^ 2 ≤ 1 := by nlinarith [hs0, hs1]
  have hprod : (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) ≤ 1 := by
    have h2 : (Real.sin (2 * θ)) ^ 2 = (Real.sin (2 * θ)) ^ ((2 : ℝ)) :=
      (Real.rpow_natCast (Real.sin (2 * θ)) 2).symm
    rw [h2, ← Real.rpow_add' hs0 (by rw [gam]; intro h; linarith)]
    exact Real.rpow_le_one hs0 hs1 (by rw [gam]; linarith)
  calc (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α)
      ≤ (2 * α ^ 2 + 2 * (Real.sin (2 * θ)) ^ 2)
          * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) :=
        mul_le_mul_of_nonneg_right hsplit hpow_nn
    _ = 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α)
          + 2 * ((Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α)) := by ring
    _ ≤ 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) + 2 * 1 := by linarith
    _ = 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) + 2 := by ring

/-- Integrability of the weighted angular factor `(α+sin 2θ)² sin(2θ)^{2α/5-γ}`. -/
theorem integrableOn_angular_weight' {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    IntegrableOn (fun θ : ℝ => (α + Real.sin (2 * θ)) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α)) Iθ := by
  have hp1_2 : (-1 : ℝ) < 2 * α / 5 - gam α := by rw [gam]; linarith
  have hp0_2 : 2 * α / 5 - gam α ≤ 0 := by rw [gam]; nlinarith
  have hInt2 : IntegrableOn (fun θ : ℝ => 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α)
      + 2) Iθ :=
    ((sin_two_rpow (2 * α / 5 - gam α) hp1_2 hp0_2).1.const_mul (2 * α ^ 2)).add
      (integrableOn_const (s := Iθ) (C := (2 : ℝ))
        (by rw [Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  have hsinm : Measurable (fun θ : ℝ => Real.sin (2 * θ)) :=
    Real.measurable_sin.comp (measurable_const.mul measurable_id)
  have hmeas : Measurable (fun θ : ℝ => (α + Real.sin (2 * θ)) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α)) :=
    ((measurable_const.add hsinm).pow_const 2).mul (hsinm.pow_const _)
  refine hInt2.mono' hmeas.aestronglyMeasurable ?_
  · refine ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    have hnn : 0 ≤ (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _)
    rw [Real.norm_of_nonneg hnn]
    exact angular_weight_pointwise' hα hα1 hθ

/-- A quantitative bound for the weighted angular integral, uniformly in `α ∈ (0,1]`. -/
theorem angular_weight_integral_bound' {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∫ θ in Iθ, (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) ≤ 700 := by
  have hp1_2 : (-1 : ℝ) < 2 * α / 5 - gam α := by rw [gam]; linarith
  have hp0_2 : 2 * α / 5 - gam α ≤ 0 := by rw [gam]; nlinarith
  have hne : (2 * α / 5 - gam α) + 1 = 3 * α / 10 := by rw [gam]; ring
  have hvolIθ : (volume.real Iθ) = Real.pi / 2 := by
    rw [MeasureTheory.measureReal_def, Iθ, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  have hpt : ∀ θ ∈ Iθ,
      (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α)
        ≤ 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) + 2 :=
    fun θ hθ => angular_weight_pointwise' hα hα1 hθ
  have hInt2 : IntegrableOn (fun θ : ℝ => 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α)
      + 2) Iθ :=
    ((sin_two_rpow (2 * α / 5 - gam α) hp1_2 hp0_2).1.const_mul (2 * α ^ 2)).add
      (integrableOn_const (s := Iθ) (C := (2 : ℝ))
        (by rw [Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  calc ∫ θ in Iθ, (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α)
      ≤ ∫ θ in Iθ, (2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) + 2) :=
        MeasureTheory.setIntegral_mono_of_nonneg
          (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _))
          hpt hInt2
    _ = 2 * α ^ 2 * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α)) + 2 * (Real.pi / 2) := by
        rw [MeasureTheory.integral_add ((sin_two_rpow (2 * α / 5 - gam α) hp1_2 hp0_2).1.const_mul _)
          (integrableOn_const (by rw [Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)),
          MeasureTheory.integral_const_mul, MeasureTheory.setIntegral_const]
        simp only [smul_eq_mul, hvolIθ]
        ring
    _ ≤ 700 := by
        have hb := (sin_two_rpow (2 * α / 5 - gam α) hp1_2 hp0_2).2
        rw [hne] at hb
        have h3 : (0 : ℝ) < 3 * α / 10 := by linarith
        have hkey : 2 * α ^ 2 * (100 / (3 * α / 10)) = 2000 * α / 3 := by
          field_simp; ring
        have hαnn : (0 : ℝ) ≤ α := le_of_lt hα
        nlinarith [hb, hαnn, hα1, Real.pi_le_four, hkey,
          mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg α)) (sub_nonneg.mpr hb)]

end Work.Spaces

namespace Work.Elliptic

open Work.Spaces

set_option autoImplicit false

/-! ## The substitution `f = z² k` -/

/-- `divZ2 f z θ = f z θ / z ^ 2`, the function `k` with `f = z ^ 2 k` for `z ≠ 0`. -/
def divZ2 (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => f z θ / z ^ 2

/-- `z² · divZ2 f = f` away from `z = 0`. -/
theorem divZ2_mul {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : z ≠ 0) :
    z ^ 2 * divZ2 f z θ = f z θ := by
  rw [divZ2]
  field_simp

/-- `f = z² · divZ2 f` away from `z = 0`. -/
theorem divZ2_eq_mul {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : z ≠ 0) :
    f z θ = z ^ 2 * divZ2 f z θ := (divZ2_mul hz).symm

/-- `(z+1)³/z² · f = (z+1)³ · divZ2 f`, as functions (the identity also holds at `z = 0`). -/
theorem g_divZ2_eq (f : ℝ → ℝ → ℝ) :
    (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ)
      = fun z θ => (z + 1) ^ 3 * divZ2 f z θ := by
  funext z θ
  rw [divZ2]
  by_cases hz : z = 0
  · subst hz; simp
  · field_simp

/-- Locality of `pzIter` in the `z`-variable (eventual equality of the `z`-slices). -/
theorem pzIter_congr_nhds {u v : ℝ → ℝ → ℝ} {z θ : ℝ} (l : ℕ)
    (h : (fun z' => u z' θ) =ᶠ[𝓝 z] fun z' => v z' θ) :
    pzIter l u z θ = pzIter l v z θ := by
  rw [pzIter_eq_iteratedDeriv l u z θ, pzIter_eq_iteratedDeriv l v z θ]
  exact h.iteratedDeriv_eq l

/-- Locality of `pzIter` in the `z`-variable (eventual pointwise equality). -/
theorem pzIter_congr_of_eventually {u v : ℝ → ℝ → ℝ} {z θ : ℝ} (l : ℕ)
    (h : ∀ᶠ z' in 𝓝 z, ∀ θ' : ℝ, u z' θ' = v z' θ') :
    pzIter l u z θ = pzIter l v z θ :=
  pzIter_congr_nhds l (h.mono fun z' hz' => hz' θ)




/-! ## `D_θ` and functions of `z` alone -/

/-- `D_θ` commutes with multiplication by a function of `z` alone. -/
theorem Dth_const_mul (c : ℝ → ℝ) (u : ℝ → ℝ → ℝ) :
    Dth (fun z θ => c z * u z θ) = fun z θ => c z * Dth u z θ := by
  funext z θ
  show Real.sin (2 * θ) * deriv (fun θ' => c z * u z θ') θ
      = c z * (Real.sin (2 * θ) * deriv (fun θ' => u z θ') θ)
  rw [deriv_const_mul' (c z) θ (fun θ' => u z θ')]
  ring

/-- `D_θ^i` commutes with multiplication by a function of `z` alone. -/
theorem DthIter_const_mul (c : ℝ → ℝ) (u : ℝ → ℝ → ℝ) (i : ℕ) :
    DthIter i (fun z θ => c z * u z θ) = fun z θ => c z * DthIter i u z θ := by
  induction i with
  | zero => rfl
  | succ n ih => rw [DthIter_succ, ih, Dth_const_mul]; rfl

/-- The constant-factor iterations of `Lop`. -/
theorem Lop_iter_const_mul (c : ℝ) (v : ℝ → ℝ) (i : ℕ) :
    Lop^[i] (fun θ => c * v θ) = fun θ => c * Lop^[i] v θ := by
  induction i with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      funext θ
      rw [Function.iterate_succ_apply']
      show Real.sin (2 * θ) * deriv (fun θ' => c * Lop^[n] v θ') θ
          = c * (Real.sin (2 * θ) * deriv (Lop^[n] v) θ)
      rw [deriv_const_mul' c θ (Lop^[n] v)]
      ring

/-- `D_θ^i f = z² D_θ^i (divZ2 f)` away from `z = 0`. -/
theorem DthIter_divZ2_eq {f : ℝ → ℝ → ℝ} (i : ℕ) {z θ : ℝ} (hz : z ≠ 0) :
    DthIter i f z θ = z ^ 2 * DthIter i (divZ2 f) z θ := by
  rw [DthIter_eq_iterate_Lop i f z, DthIter_eq_iterate_Lop i (divZ2 f) z]
  have hfun : (fun θ' => f z θ') = fun θ' => z ^ 2 * divZ2 f z θ' := by
    funext θ'; exact divZ2_eq_mul hz
  rw [hfun, Lop_iter_const_mul (z ^ 2) (fun θ' => divZ2 f z θ') i]

/-! ## The local Leibniz rule for `∂_z` -/


/-! ## Absolute-value bookkeeping for the triangular estimate -/

theorem abs_three_le (a b c : ℝ) : |a - b - c| ≤ |a| + |b| + |c| := by
  have h1 : a - b - c = a + -b + -c := by ring
  rw [h1]
  calc |a + -b + -c| ≤ |a + -b| + |-c| := abs_add_le _ _
    _ ≤ (|a| + |-b|) + |-c| := by
        gcongr; exact abs_add_le _ _
    _ = |a| + |b| + |c| := by rw [abs_neg, abs_neg]

theorem abs_four_le (a b c d : ℝ) : |a - b - c - d| ≤ |a| + |b| + |c| + |d| := by
  have h1 : a - b - c - d = a + -b + -c + -d := by ring
  rw [h1]
  calc |a + -b + -c + -d| ≤ |a + -b + -c| + |-d| := abs_add_le _ _
    _ ≤ (|a + -b| + |-c|) + |-d| := by
        gcongr; exact abs_add_le _ _
    _ ≤ ((|a| + |-b|) + |-c|) + |-d| := by
        gcongr; exact abs_add_le _ _
    _ = |a| + |b| + |c| + |d| := by rw [abs_neg, abs_neg, abs_neg]

/-! ## Explicit derivatives of the two polynomials `z²` and `(1+z)³` -/

theorem pzIter_one_sq (z θ : ℝ) : pzIter 1 (fun z θ => z ^ 2) z θ = 2 * z := by
  show deriv (fun z' : ℝ => z' ^ 2) z = 2 * z
  rw [show (fun z' : ℝ => z' ^ 2) = (fun z' : ℝ => z') ^ 2 from rfl,
    deriv_pow differentiableAt_id, deriv_id'']
  ring

theorem pzIter_two_sq (z θ : ℝ) : pzIter 2 (fun z θ => z ^ 2) z θ = 2 := by
  have h1 : pzIter 1 (fun z θ => z ^ 2) = fun z θ => 2 * z := by
    funext z θ; exact pzIter_one_sq z θ
  rw [pzIter_succ, h1]
  show deriv (fun z' : ℝ => 2 * z') z = 2
  rw [deriv_const_mul 2 differentiableAt_id, deriv_id'']
  norm_num

theorem pzIter_three_sq (z θ : ℝ) : pzIter 3 (fun z θ => z ^ 2) z θ = 0 := by
  have h1 : pzIter 2 (fun z θ => z ^ 2) = fun _ _ => (2 : ℝ) := by
    funext z θ; exact pzIter_two_sq z θ
  rw [pzIter_succ, h1]
  show deriv (fun _ : ℝ => (2 : ℝ)) z = 0
  exact deriv_const z 2

theorem pzIter_four_sq (z θ : ℝ) : pzIter 4 (fun z θ => z ^ 2) z θ = 0 := by
  have h1 : pzIter 3 (fun z θ => z ^ 2) = fun _ _ => (0 : ℝ) := by
    funext z θ; exact pzIter_three_sq z θ
  rw [pzIter_succ, h1]
  show deriv (fun _ : ℝ => (0 : ℝ)) z = 0
  exact deriv_const z 0

theorem pzIter_one_cube (z θ : ℝ) :
    pzIter 1 (fun z θ => (z + 1) ^ 3) z θ = 3 * (z + 1) ^ 2 := by
  show deriv (fun z' : ℝ => (z' + 1) ^ 3) z = 3 * (z + 1) ^ 2
  rw [show (fun z' : ℝ => (z' + 1) ^ 3) = (fun z' : ℝ => z' + 1) ^ 3 from rfl,
    deriv_pow (differentiableAt_id.add_const 1)]
  rw [show deriv (fun z' : ℝ => z' + 1) z = 1 from by rw [deriv_add_const, deriv_id'']]
  ring

theorem pzIter_two_cube (z θ : ℝ) :
    pzIter 2 (fun z θ => (z + 1) ^ 3) z θ = 6 * (z + 1) := by
  have h1 : pzIter 1 (fun z θ => (z + 1) ^ 3) = fun z θ => 3 * (z + 1) ^ 2 := by
    funext z θ; exact pzIter_one_cube z θ
  rw [pzIter_succ, h1]
  show deriv (fun z' : ℝ => 3 * (z' + 1) ^ 2) z = 6 * (z + 1)
  rw [deriv_const_mul 3 ((differentiableAt_id.add_const 1).pow 2)]
  rw [show (fun z' : ℝ => (z' + 1) ^ 2) = (fun z' : ℝ => z' + 1) ^ 2 from rfl,
    deriv_pow (differentiableAt_id.add_const 1)]
  rw [show deriv (fun z' : ℝ => z' + 1) z = 1 from by rw [deriv_add_const, deriv_id'']]
  ring

theorem pzIter_three_cube (z θ : ℝ) :
    pzIter 3 (fun z θ => (z + 1) ^ 3) z θ = 6 := by
  have h1 : pzIter 2 (fun z θ => (z + 1) ^ 3) = fun z θ => 6 * (z + 1) := by
    funext z θ; exact pzIter_two_cube z θ
  rw [pzIter_succ, h1]
  show deriv (fun z' : ℝ => 6 * (z' + 1)) z = 6
  rw [deriv_const_mul 6 (differentiableAt_id.add_const 1)]
  rw [show deriv (fun z' : ℝ => z' + 1) z = 1 from by rw [deriv_add_const, deriv_id'']]
  ring

theorem pzIter_four_cube (z θ : ℝ) :
    pzIter 4 (fun z θ => (z + 1) ^ 3) z θ = 0 := by
  have h1 : pzIter 3 (fun z θ => (z + 1) ^ 3) = fun _ _ => (6 : ℝ) := by
    funext z θ; exact pzIter_three_cube z θ
  rw [pzIter_succ, h1]
  show deriv (fun _ : ℝ => (6 : ℝ)) z = 0
  exact deriv_const z 6

/-! ## The Leibniz expansions of `∂_z^m (z² κ)` and `∂_z^m ((1+z)³ κ)` -/



/-! ## The triangular estimate -/


end Work.Elliptic
