/-
Copyright: work module for the Elgindi finite-time singularity project.

# Auxiliary lemmas for the transfer `𝒲^{4,∞} → ℋ⁴` (Proposition `WtoH`)

Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021),
Proposition `WtoH` (tex line 1237) states that a universal constant `C` exists with
`|f|_{ℋ⁴} ≤ C |(z+1)³/z² · f|_{𝒲^{4,∞}}` for every smooth `f`.

The mathematical content is the substitution `f = z² k` (so that
`(z+1)³/z² f = (z+1)³ k`): the `𝒲^{4,∞}`-norm of `(z+1)³ k` controls `(z+1)^{j+3}∂_z^j k`,
which in turn dominates `(1+z) z^j w ∂_z^j f` with the crucial decay factor `1/(1+z)`.

This file collects the analytic bookkeeping:

* `divZ2 f = f / z²` and its two relations `f = z² (divZ2 f)` (for `z ≠ 0`) and
  `(z+1)³/z² f = (z+1)³ (divZ2 f)` (everywhere);
* smoothness of the `z`-slices of `divZ2 f` and of its `D_θ`-iterates on `z > 0`;
* `D_θ^i` commutes with multiplication by a function of `z` alone, whence
  `D_θ^i f z θ = z² D_θ^i (divZ2 f) z θ` for `z ≠ 0`;
* the local Leibniz rule `pzIter k (u·v) = ∑_c binom k c · (∂_z^c u · ∂_z^{k-c} v)`
  for `C^∞` slices, together with the explicit expansions of `∂_z^m (z² k)` and
  `∂_z^m ((1+z)³ k)` for `m ≤ 4`;
* `tri_bound`, the triangular estimate of the paper: bounds on
  `(1+z)^j ∂_z^j ((1+z)³ k)` give bounds on `(1+z)^{j+3} ∂_z^j k`.

It also contains copies (with primed names, since the file
`Submission/Work/Spaces/WProductRule.lean` carrying them is under construction) of
`SmoothNbhd → SmoothInt`, of the smoothness of the `z`-slices of `D_θ`-iterates, and
of the angular weighted integral bounds.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.pz_aux
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.Spaces.DthIter_contDiffAt
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.Spaces.DzIter_le_of_pzIter
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.HkAux
import Submission.Work.Spaces.Gamma_WlInf

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

/-- The `z`-slices of `divZ2 f` are smooth at every `z > 0`, for `SmoothNbhd f`. -/
theorem contDiffAt_divZ2_zslice {f : ℝ → ℝ → ℝ} (hsm : SmoothNbhd f) :
    ∀ θ ∈ Iθ, ∀ z : ℝ, 0 < z → ContDiffAt ℝ ⊤ (fun z' => divZ2 f z' θ) z := by
  intro θ hθ z hz
  have hf := SmoothInt.of_smoothNbhd hsm
  have hslice : ContDiffAt ℝ ⊤ (fun z' => f z' θ) z :=
    (hf.2 θ hθ).contDiffAt (isOpen_Ioi.mem_nhds (by simp only [Set.mem_Ioi]; linarith))
  have hinv : ContDiffAt ℝ ⊤ (fun z' : ℝ => (z' ^ 2)⁻¹) z :=
    (contDiffAt_id.pow 2).inv (by simpa using pow_ne_zero 2 (ne_of_gt hz))
  have hmul := hslice.mul hinv
  simpa [divZ2, div_eq_mul_inv] using hmul

/-- Joint smoothness of `divZ2 f` over the open quadrant. -/
theorem contDiffAt_uncurry_divZ2 {f : ℝ → ℝ → ℝ} (hsm : SmoothNbhd f) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ContDiffAt ℝ ⊤ (Function.uncurry (divZ2 f)) (z, θ) := by
  have hfU : ContDiffAt ℝ ⊤ (Function.uncurry f) (z, θ) :=
    ((smoothNbhd_iff f).mp hsm).contDiffAt
      (isOpen_U.mem_nhds (mem_U (by linarith) (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])))
  have hden : ContDiffAt ℝ ⊤ (fun p : ℝ × ℝ => p.1 ^ 2) (z, θ) := contDiffAt_fst.pow 2
  have hne : (fun p : ℝ × ℝ => p.1 ^ 2) (z, θ) ≠ 0 := pow_ne_zero 2 (ne_of_gt hz)
  have hdiv := hfU.div hden hne
  have heq : Function.uncurry (divZ2 f) = fun p : ℝ × ℝ => Function.uncurry f p / p.1 ^ 2 := by
    funext p; rfl
  rw [heq]
  exact hdiv

/-- The `z`-slices of the `D_θ`-iterates of `divZ2 f` are smooth at every `z > 0`. -/
theorem contDiffAt_DthIter_divZ2_zslice {f : ℝ → ℝ → ℝ} (hsm : SmoothNbhd f) (i : ℕ) :
    ∀ θ ∈ Iθ, ∀ z : ℝ, 0 < z → ContDiffAt ℝ ⊤ (fun z' => DthIter i (divZ2 f) z' θ) z := by
  intro θ hθ z hz
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi; exact contDiffAt_divZ2_zslice hsm θ hθ z hz
  · obtain ⟨i', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hi)
    by_cases hθi : θ ∈ Set.Ioo 0 (π / 2)
    · exact contDiffAt_slice_left (DthIter_contDiffAt (divZ2 f) (i' + 1)
        (contDiffAt_uncurry_divZ2 hsm hz hθi))
    · have hsin := sin_two_mul_eq_zero_of_mem_Iθ_of_not_mem_Ioo hθ hθi
      have hzero : (fun z' => DthIter (i' + 1) (divZ2 f) z' θ) = fun _ => (0 : ℝ) :=
        funext fun z' => DthIter_eq_zero_of_sin_eq_zero (divZ2 f) i' hsin z'
      rw [hzero]; exact contDiffAt_const

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

/-- Leibniz rule for `∂_z^k` of a product, at a point where both `z`-slices are `C^∞`. -/
theorem pzIter_mul_local (k : ℕ) {u v : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hu : ContDiffAt ℝ ⊤ (fun z' => u z' θ) z) (hv : ContDiffAt ℝ ⊤ (fun z' => v z' θ) z) :
    pzIter k (fun z θ => u z θ * v z θ) z θ
      = ∑ c ∈ Finset.range (k + 1),
          (k.choose c : ℝ) * (pzIter c u z θ * pzIter (k - c) v z θ) := by
  rw [pzIter_eq_iteratedDeriv k (fun z θ => u z θ * v z θ) z θ]
  have hfun : (fun z' => (fun z θ => u z θ * v z θ) z' θ)
      = (fun z' => u z' θ) * (fun z' => v z' θ) := rfl
  rw [hfun, iteratedDeriv_mul (hu.of_le le_top) (hv.of_le le_top)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← pzIter_eq_iteratedDeriv c u z θ, ← pzIter_eq_iteratedDeriv (k - c) v z θ]
  ring

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

/-- `∂_z^m (z² κ) = z² ∂_z^m κ + 2m z ∂_z^{m-1} κ + m(m-1) ∂_z^{m-2} κ` for `m ≤ 4`. -/
theorem pzIter_sq_mul (m : ℕ) (hm : m ≤ 4) {κ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hκ : ContDiffAt ℝ ⊤ (fun z' => κ z' θ) z) :
    pzIter m (fun z θ => z ^ 2 * κ z θ) z θ
      = z ^ 2 * pzIter m κ z θ + (2 * (m : ℝ)) * z * pzIter (m - 1) κ z θ
        + ((m : ℝ) * ((m : ℝ) - 1)) * pzIter (m - 2) κ z θ := by
  have hu : ContDiffAt ℝ ⊤ (fun z' : ℝ => z' ^ 2) z := contDiffAt_id.pow 2
  have h := pzIter_mul_local (u := fun z _ => z ^ 2) (v := κ) m hu hκ
  rcases m with _ | _ | _ | _ | _ | m
  · rw [h, Finset.sum_range_one]
    simp
  · rw [h, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [pzIter_zero, pzIter_one_sq, pzIter_two_sq]
    norm_num [Nat.choose]
  · rw [h, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [pzIter_zero, pzIter_one_sq, pzIter_two_sq, pzIter_three_sq]
    norm_num [Nat.choose]
    ring
  · rw [h, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [pzIter_zero, pzIter_one_sq, pzIter_two_sq, pzIter_three_sq, pzIter_four_sq]
    norm_num [Nat.choose]
    ring
  · rw [h, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [pzIter_zero, pzIter_one_sq, pzIter_two_sq, pzIter_three_sq, pzIter_four_sq]
    norm_num [Nat.choose]
    ring
  · omega

/-- `∂_z^m ((1+z)³ κ) = (1+z)³∂_z^mκ + 3m(1+z)²∂_z^{m-1}κ + 3m(m-1)(1+z)∂_z^{m-2}κ
+ m(m-1)(m-2)∂_z^{m-3}κ` for `m ≤ 4`. -/
theorem pzIter_three_mul (m : ℕ) (hm : m ≤ 4) {κ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hκ : ContDiffAt ℝ ⊤ (fun z' => κ z' θ) z) :
    pzIter m (fun z θ => (z + 1) ^ 3 * κ z θ) z θ
      = (z + 1) ^ 3 * pzIter m κ z θ
        + (3 * (m : ℝ)) * (z + 1) ^ 2 * pzIter (m - 1) κ z θ
        + (3 * (m : ℝ) * ((m : ℝ) - 1)) * (z + 1) * pzIter (m - 2) κ z θ
        + ((m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2)) * pzIter (m - 3) κ z θ := by
  have hu : ContDiffAt ℝ ⊤ (fun z' : ℝ => (z' + 1) ^ 3) z :=
    (contDiffAt_id.add contDiffAt_const).pow 3
  have h := pzIter_mul_local (u := fun z _ => (z + 1) ^ 3) (v := κ) m hu hκ
  rcases m with _ | _ | _ | _ | _ | m
  · rw [h, Finset.sum_range_one]
    simp
  · rw [h, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [pzIter_zero, pzIter_one_cube, pzIter_two_cube]
    norm_num [Nat.choose]
  · rw [h, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [pzIter_zero, pzIter_one_cube, pzIter_two_cube, pzIter_three_cube]
    norm_num [Nat.choose]
    ring
  · rw [h, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [pzIter_zero, pzIter_one_cube, pzIter_two_cube, pzIter_three_cube, pzIter_four_cube]
    norm_num [Nat.choose]
    ring
  · rw [h, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [pzIter_zero, pzIter_one_cube, pzIter_two_cube, pzIter_three_cube, pzIter_four_cube]
    norm_num [Nat.choose]
    ring
  · omega

/-! ## The triangular estimate -/

/-- **The triangular estimate.** If `G = (z+1)³ κ` and `|(z+1)^j ∂_z^j G| ≤ Λ` for `j ≤ J`
(`J ≤ 4`) at a point with `z > 0`, then `|(z+1)^{j+3} ∂_z^j κ| ≤ 6000 Λ` for `j ≤ J`. -/
theorem tri_bound {G κ : ℝ → ℝ → ℝ} (hG : G = fun z θ => (z + 1) ^ 3 * κ z θ)
    {z θ Λ : ℝ} {J : ℕ} (hJ : J ≤ 4) (hz : 0 < z)
    (hκ : ContDiffAt ℝ ⊤ (fun z' => κ z' θ) z)
    (hbound : ∀ j ≤ J, |(z + 1) ^ j * pzIter j G z θ| ≤ Λ) :
    ∀ j ≤ J, |(z + 1) ^ (j + 3) * pzIter j κ z θ| ≤ 6000 * Λ := by
  have hΛ : 0 ≤ Λ := le_trans (abs_nonneg _) (hbound 0 (Nat.zero_le J))
  set B : ℕ → ℝ := fun k => (z + 1) ^ (k + 3) * pzIter k κ z θ with hB
  set Gv : ℕ → ℝ := fun k => (z + 1) ^ k * pzIter k G z θ with hGv
  have hid0 : Gv 0 = B 0 := by
    have h := pzIter_three_mul (κ := κ) 0 (by norm_num) hκ
    simp only [hGv, hG, hB, h]
    ring
  have hid1 : Gv 1 = B 1 + 3 * B 0 := by
    have h := pzIter_three_mul (κ := κ) 1 (by norm_num) hκ
    simp only [hGv, hG, hB, h]
    ring
  have hid2 : Gv 2 = B 2 + 6 * B 1 + 6 * B 0 := by
    have h := pzIter_three_mul (κ := κ) 2 (by norm_num) hκ
    simp only [hGv, hG, hB, h]
    ring
  have hid3 : Gv 3 = B 3 + 9 * B 2 + 18 * B 1 + 6 * B 0 := by
    have h := pzIter_three_mul (κ := κ) 3 (by norm_num) hκ
    simp only [hGv, hG, hB, h]
    ring
  have hid4 : Gv 4 = B 4 + 12 * B 3 + 36 * B 2 + 24 * B 1 := by
    have h := pzIter_three_mul (κ := κ) 4 (by norm_num) hκ
    simp only [hGv, hG, hB, h]
    ring
  have hGk : ∀ k ≤ J, |Gv k| ≤ Λ := by
    intro k hk
    rw [hGv]
    simpa using hbound k hk
  have b0 : |B 0| ≤ Λ := by rw [← hid0]; exact hGk 0 (Nat.zero_le J)
  have b1 (hJ1 : 1 ≤ J) : |B 1| ≤ 4 * Λ := by
    have h1 : B 1 = Gv 1 - 3 * B 0 := by linarith [hid1]
    have hA : |3 * B 0| = 3 * |B 0| := by rw [abs_mul, abs_of_nonneg (by norm_num)]
    calc |B 1| = |Gv 1 - 3 * B 0| := by rw [h1]
      _ ≤ |Gv 1| + |3 * B 0| := abs_sub _ _
      _ = |Gv 1| + 3 * |B 0| := by rw [hA]
      _ ≤ Λ + 3 * Λ := add_le_add (hGk 1 hJ1) (by linarith [b0])
      _ = 4 * Λ := by ring
  have b2 (hJ2 : 2 ≤ J) : |B 2| ≤ 31 * Λ := by
    have h2 : B 2 = Gv 2 - 6 * B 1 - 6 * B 0 := by linarith [hid2]
    have hA : |6 * B 1| = 6 * |B 1| := by rw [abs_mul, abs_of_nonneg (by norm_num)]
    have hB' : |6 * B 0| = 6 * |B 0| := by rw [abs_mul, abs_of_nonneg (by norm_num)]
    calc |B 2| = |Gv 2 - 6 * B 1 - 6 * B 0| := by rw [h2]
      _ ≤ |Gv 2| + 6 * |B 1| + 6 * |B 0| := by
          refine le_trans (abs_three_le _ _ _) ?_
          rw [hA, hB']
      _ ≤ Λ + 6 * (4 * Λ) + 6 * Λ := by
          refine add_le_add (add_le_add (hGk 2 hJ2) ?_) ?_
          · linarith [b1 (by omega)]
          · linarith [b0]
      _ = 31 * Λ := by ring
  have b3 (hJ3 : 3 ≤ J) : |B 3| ≤ 358 * Λ := by
    have h3 : B 3 = Gv 3 - 9 * B 2 - 18 * B 1 - 6 * B 0 := by linarith [hid3]
    have hA : |9 * B 2| = 9 * |B 2| := by rw [abs_mul, abs_of_nonneg (by norm_num)]
    have hB' : |18 * B 1| = 18 * |B 1| := by rw [abs_mul, abs_of_nonneg (by norm_num)]
    have hC : |6 * B 0| = 6 * |B 0| := by rw [abs_mul, abs_of_nonneg (by norm_num)]
    calc |B 3| = |Gv 3 - 9 * B 2 - 18 * B 1 - 6 * B 0| := by rw [h3]
      _ ≤ |Gv 3| + 9 * |B 2| + 18 * |B 1| + 6 * |B 0| := by
          refine le_trans (abs_four_le _ _ _ _) ?_
          rw [hA, hB', hC]
      _ ≤ Λ + 9 * (31 * Λ) + 18 * (4 * Λ) + 6 * Λ := by
          refine add_le_add (add_le_add (add_le_add (hGk 3 hJ3) ?_) ?_) ?_
          · linarith [b2 (by omega)]
          · linarith [b1 (by omega)]
          · linarith [b0]
      _ = 358 * Λ := by ring
  have b4 (hJ4 : 4 ≤ J) : |B 4| ≤ 5509 * Λ := by
    have h4 : B 4 = Gv 4 - 12 * B 3 - 36 * B 2 - 24 * B 1 := by linarith [hid4]
    have hA : |12 * B 3| = 12 * |B 3| := by rw [abs_mul, abs_of_nonneg (by norm_num)]
    have hB' : |36 * B 2| = 36 * |B 2| := by rw [abs_mul, abs_of_nonneg (by norm_num)]
    have hC : |24 * B 1| = 24 * |B 1| := by rw [abs_mul, abs_of_nonneg (by norm_num)]
    calc |B 4| = |Gv 4 - 12 * B 3 - 36 * B 2 - 24 * B 1| := by rw [h4]
      _ ≤ |Gv 4| + 12 * |B 3| + 36 * |B 2| + 24 * |B 1| := by
          refine le_trans (abs_four_le _ _ _ _) ?_
          rw [hA, hB', hC]
      _ ≤ Λ + 12 * (358 * Λ) + 36 * (31 * Λ) + 24 * (4 * Λ) := by
          refine add_le_add (add_le_add (add_le_add (hGk 4 hJ4) ?_) ?_) ?_
          · linarith [b3 (by omega)]
          · linarith [b2 (by omega)]
          · linarith [b1 (by omega)]
      _ = 5509 * Λ := by ring
  intro j hj
  rcases j with _ | _ | _ | _ | _ | j
  · show |B 0| ≤ 6000 * Λ
    exact le_trans b0 (by nlinarith [hΛ])
  · show |B 1| ≤ 6000 * Λ
    exact le_trans (b1 hj) (by nlinarith [hΛ])
  · show |B 2| ≤ 6000 * Λ
    exact le_trans (b2 hj) (by nlinarith [hΛ])
  · show |B 3| ≤ 6000 * Λ
    exact le_trans (b3 hj) (by nlinarith [hΛ])
  · show |B 4| ≤ 6000 * Λ
    exact le_trans (b4 hj) (by nlinarith [hΛ])
  · omega

end Work.Elliptic
