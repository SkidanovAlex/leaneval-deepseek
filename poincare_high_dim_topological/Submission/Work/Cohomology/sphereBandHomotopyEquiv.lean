import Mathlib
import Submission.Work.Morse.TwoBallsBasic

/-!
# The equatorial band of `Sᵐ` is homotopy equivalent to `Sᵐ⁻¹`

Consider the unit sphere `Sᵐ ⊆ ℝ^{m+1}` and the open equatorial band

`Bᵐ = {x ∈ Sᵐ | -1/2 < x_{m+1} < 1/2}`.

Writing `x = (x', t)` with `t = x_{m+1} ∈ (-1/2, 1/2)` and `‖x'‖² = 1 - t² ∈ (3/4, 1]`,
the band is homeomorphic to `Sᵐ⁻¹ × (-1/2, 1/2)`; its "equator" `t = 0` is a strong
deformation retract of it.  Consequently `Bᵐ` is homotopy equivalent to `Sᵐ⁻¹`.

This file builds that homotopy equivalence explicitly, from the maps

* `fMap m : Bᵐ → Sᵐ⁻¹`, `x ↦ x'/‖x'‖` (normalising the first `m` coordinates), and
* `gMap m : Sᵐ⁻¹ → Bᵐ`, `y ↦ (y, 0)`,

with the homotopy `Hamb` from the identity of `Bᵐ` to `gMap m ∘ fMap m` given by
`x ↦ (√(1 - ((1-s) x_{m+1})²) · x'/‖x'‖, (1-s) x_{m+1})`,
i.e. moving `x` along the great circle through `x` and the equator at `s = 1`.

## Main result

* `Work.Cohomology.sphereBandHomotopyEquiv`:
  `Nonempty (ContinuousMap.HomotopyEquiv Bᵐ Sᵐ⁻¹)`.
-/

open unitInterval

noncomputable section

namespace Work.Cohomology

/-- The open equatorial band `{x ∈ Sᵐ ⊆ ℝ^{m+1} | -1/2 < x_{m+1} < 1/2}`. -/
abbrev Band (m : ℕ) : Type :=
  {x : EuclideanSpace ℝ (Fin (m+1)) // ‖x‖ = 1 ∧ x (Fin.last m) > -(1/2) ∧ x (Fin.last m) < 1/2}

/-- The unit sphere `Sᵐ⁻¹ ⊆ ℝᵐ`, written as a subtype. -/
abbrev Sph (m : ℕ) : Type := {y : EuclideanSpace ℝ (Fin m) // ‖y‖ = 1}

variable {m : ℕ}

/-! ## Coordinate lemmas -/

lemma continuous_strip (m : ℕ) : Continuous (Work.Morse.strip (n := m)) := by
  unfold Work.Morse.strip; fun_prop

lemma strip_snocLp (y : EuclideanSpace ℝ (Fin m)) (t : ℝ) :
    Work.Morse.strip (Work.Morse.snocLp y t) = y := by
  apply PiLp.ext; intro i; simp [Work.Morse.strip, Work.Morse.snocLp]

/-- Pythagoras for the coordinate splitting `x = (strip x, x_{m+1})` of `ℝ^{m+1}`. -/
lemma norm_sq_strip_add (x : EuclideanSpace ℝ (Fin (m+1))) :
    ‖Work.Morse.strip x‖ ^ 2 + (x (Fin.last m)) ^ 2 = ‖x‖ ^ 2 := by
  have h := Work.Morse.snocLp_norm_sq (Work.Morse.strip x) (x (Fin.last m))
  rw [Work.Morse.snocLp_strip] at h
  linarith [h]

lemma abs_last_lt_half (x : Band m) : |x.val (Fin.last m)| < 1/2 := by
  rw [abs_lt]; exact ⟨x.2.2.1, x.2.2.2⟩

/-- On the band the first `m` coordinates are nonzero: `‖strip x‖² = 1 - x_{m+1}² > 3/4`. -/
lemma strip_norm_pos (x : Band m) : 0 < ‖Work.Morse.strip x.val‖ := by
  have h := norm_sq_strip_add (x := x.val)
  rw [x.2.1] at h
  have ht := abs_last_lt_half x
  have ht2 : (x.val (Fin.last m)) ^ 2 < 1/4 := by
    rw [abs_lt] at ht; nlinarith [ht.1, ht.2]
  have hpos : (3:ℝ)/4 < ‖Work.Morse.strip x.val‖ ^ 2 := by nlinarith
  nlinarith [norm_nonneg (Work.Morse.strip x.val)]

/-- The normalisation of the first `m` coordinates. -/
def proj (x : EuclideanSpace ℝ (Fin (m+1))) : EuclideanSpace ℝ (Fin m) :=
  (‖Work.Morse.strip x‖)⁻¹ • Work.Morse.strip x

lemma norm_proj (x : EuclideanSpace ℝ (Fin (m+1))) (h : Work.Morse.strip x ≠ 0) :
    ‖proj x‖ = 1 := by
  rw [proj, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _)]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)

lemma continuous_proj_band (m : ℕ) : Continuous (fun x : Band m => proj x.val) := by
  have hc : Continuous (fun x : Band m => Work.Morse.strip x.val) :=
    (continuous_strip m).comp continuous_subtype_val
  exact (hc.norm.inv₀ (fun x => ne_of_gt (strip_norm_pos x))).smul hc

lemma proj_ne (x : Band m) : Work.Morse.strip x.val ≠ 0 :=
  norm_ne_zero_iff.mp (ne_of_gt (strip_norm_pos x))

lemma proj_norm (x : Band m) : ‖proj x.val‖ = 1 := norm_proj x.val (proj_ne x)

/-! ## The two maps -/

/-- The projection `Bᵐ → Sᵐ⁻¹`, normalising the first `m` coordinates. -/
def fMap (m : ℕ) : C(Band m, Sph m) where
  toFun x := ⟨proj x.val, proj_norm x⟩
  continuous_toFun := by
    apply Continuous.subtype_mk (continuous_proj_band m)

lemma norm_snocLp_zero (y : EuclideanSpace ℝ (Fin m)) (h : ‖y‖ = 1) :
    ‖Work.Morse.snocLp y 0‖ = 1 := by
  have h2 : ‖Work.Morse.snocLp y 0‖ ^ 2 = 1 := by
    rw [Work.Morse.snocLp_norm_sq, h]; ring
  rcases sq_eq_one_iff.mp h2 with h' | h'
  · exact h'
  · exact absurd h' (by linarith [norm_nonneg (Work.Morse.snocLp y 0)])

lemma snocLp_mem_band (y : EuclideanSpace ℝ (Fin m)) (h : ‖y‖ = 1) :
    ‖Work.Morse.snocLp y 0‖ = 1 ∧ (Work.Morse.snocLp y 0) (Fin.last m) > -(1/2) ∧
      (Work.Morse.snocLp y 0) (Fin.last m) < 1/2 := by
  refine ⟨norm_snocLp_zero y h, ?_, ?_⟩ <;> · rw [Work.Morse.snocLp_ofLp_last]; norm_num

/-- The equatorial inclusion `Sᵐ⁻¹ → Bᵐ`, `y ↦ (y, 0)`. -/
def gMap (m : ℕ) : C(Sph m, Band m) where
  toFun y := ⟨Work.Morse.snocLp y.val 0, snocLp_mem_band y.val y.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk (Work.Morse.continuous_snocLp.comp
      (continuous_subtype_val.prodMk continuous_const))

lemma fMap_gMap (m : ℕ) (y : Sph m) : fMap m (gMap m y) = y := by
  apply Subtype.ext
  show proj (Work.Morse.snocLp y.val 0) = y.val
  rw [proj, strip_snocLp]
  simp [y.2]

/-! ## The homotopy `Bᵐ × I → Bᵐ` -/

lemma one_sub_mem_Icc (p : I) : 0 ≤ 1 - (p : ℝ) ∧ 1 - (p : ℝ) ≤ 1 := by
  have h := p.2
  constructor <;> linarith [h.1, h.2]

lemma abs_mul_le_half (p : I) {t : ℝ} (ht : |t| < 1/2) : |(1 - (p:ℝ)) * t| < 1/2 := by
  have hp := one_sub_mem_Icc p
  rw [abs_mul, abs_of_nonneg hp.1]
  calc (1 - (p:ℝ)) * |t| ≤ |t| := mul_le_of_le_one_left (abs_nonneg t) hp.2
    _ < 1/2 := ht

lemma sq_lt_quarter_of_abs_lt {u : ℝ} (h : |u| < 1/2) : u ^ 2 < 1/4 := by
  have h1 : 0 ≤ |u| := abs_nonneg u
  rw [← sq_abs u]
  nlinarith [h, h1, mul_nonneg (sub_nonneg.mpr h.le) h1]

/-- The underlying map of the deformation retraction of the band onto its equator:
`x ↦ (√(1 - ((1-s) x_{m+1})²) · x'/‖x'‖, (1-s) x_{m+1})`. -/
def Hamb (p : I × Band m) : EuclideanSpace ℝ (Fin (m+1)) :=
  Work.Morse.snocLp
    (Real.sqrt (1 - ((1 - (p.1 : ℝ)) * p.2.val (Fin.last m)) ^ 2) • proj p.2.val)
    ((1 - (p.1 : ℝ)) * p.2.val (Fin.last m))

lemma Hamb_mem (p : I × Band m) :
    ‖Hamb p‖ = 1 ∧ Hamb p (Fin.last m) > -(1/2) ∧ Hamb p (Fin.last m) < 1/2 := by
  have hu := abs_mul_le_half p.1 (abs_last_lt_half p.2)
  have h1u : 0 ≤ 1 - ((1 - (p.1 : ℝ)) * p.2.val (Fin.last m)) ^ 2 := by
    have h2 : ((1 - (p.1 : ℝ)) * p.2.val (Fin.last m)) ^ 2 < 1/4 :=
      sq_lt_quarter_of_abs_lt hu
    linarith
  have hfirst : ‖Real.sqrt (1 - ((1 - (p.1 : ℝ)) * p.2.val (Fin.last m)) ^ 2)
      • proj p.2.val‖ ^ 2 = 1 - ((1 - (p.1 : ℝ)) * p.2.val (Fin.last m)) ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, proj_norm p.2, mul_one, sq_abs, Real.sq_sqrt h1u]
  have hlast : Hamb p (Fin.last m) = (1 - (p.1 : ℝ)) * p.2.val (Fin.last m) :=
    Work.Morse.snocLp_ofLp_last _ _
  refine ⟨?_, ?_, ?_⟩
  · have h2 : ‖Hamb p‖ ^ 2 = 1 := by
      rw [Hamb, Work.Morse.snocLp_norm_sq, hfirst]; ring
    rcases sq_eq_one_iff.mp h2 with h | h
    · exact h
    · exact absurd h (by linarith [norm_nonneg (Hamb p)])
  · rw [hlast]; exact (abs_lt.mp hu).1
  · rw [hlast]; exact (abs_lt.mp hu).2

lemma continuous_Hamb (m : ℕ) : Continuous (Hamb (m := m)) := by
  have ht : Continuous (fun p : I × Band m => p.2.val (Fin.last m)) := by fun_prop
  have hfac : Continuous (fun p : I × Band m => (1 - (p.1 : ℝ))) := by fun_prop
  have hu : Continuous (fun p : I × Band m => (1 - (p.1 : ℝ)) * p.2.val (Fin.last m)) :=
    hfac.mul ht
  have hR : Continuous (fun p : I × Band m =>
      Real.sqrt (1 - ((1 - (p.1 : ℝ)) * p.2.val (Fin.last m)) ^ 2)) :=
    Real.continuous_sqrt.comp (continuous_const.sub (hu.pow 2))
  have hpj : Continuous (fun p : I × Band m => proj p.2.val) :=
    (continuous_proj_band m).comp continuous_snd
  exact Work.Morse.continuous_snocLp.comp ((hR.smul hpj).prodMk hu)

lemma Hamb_zero (x : Band m) : Hamb (0, x) = x.val := by
  have hstrip : 0 < ‖Work.Morse.strip x.val‖ := strip_norm_pos x
  have hsq : ‖Work.Morse.strip x.val‖ ^ 2 = 1 - (x.val (Fin.last m)) ^ 2 := by
    have h := norm_sq_strip_add (x := x.val)
    rw [x.2.1] at h
    linarith [h]
  have hsqrt : Real.sqrt (1 - (x.val (Fin.last m)) ^ 2) = ‖Work.Morse.strip x.val‖ := by
    rw [← hsq, Real.sqrt_sq (le_of_lt hstrip)]
  have h0 : ((0 : I) : ℝ) = 0 := rfl
  change Work.Morse.snocLp
    (Real.sqrt (1 - ((1 - ((0 : I) : ℝ)) * x.val (Fin.last m)) ^ 2) • proj x.val)
    ((1 - ((0 : I) : ℝ)) * x.val (Fin.last m)) = x.val
  rw [h0, sub_zero, one_mul, hsqrt, proj, smul_smul, mul_inv_cancel₀ (ne_of_gt hstrip),
    one_smul, Work.Morse.snocLp_strip]

lemma Hamb_one (x : Band m) : Hamb (1, x) = (gMap m (fMap m x)).val := by
  have h1 : ((1 : I) : ℝ) = 1 := rfl
  change Work.Morse.snocLp
    (Real.sqrt (1 - ((1 - ((1 : I) : ℝ)) * x.val (Fin.last m)) ^ 2) • proj x.val)
    ((1 - ((1 : I) : ℝ)) * x.val (Fin.last m)) = (gMap m (fMap m x)).val
  rw [h1, sub_self, zero_mul, pow_two, mul_zero, sub_zero, Real.sqrt_one, one_smul]
  rfl

/-- The deformation retraction of the band onto its equator, as a homotopy from the
identity to `gMap m ∘ fMap m`. -/
def HambHomotopy (m : ℕ) : ContinuousMap.Homotopy (ContinuousMap.id (Band m))
    ((gMap m).comp (fMap m)) where
  toFun p := ⟨Hamb p, Hamb_mem p⟩
  continuous_toFun := Continuous.subtype_mk (continuous_Hamb m) (fun p => Hamb_mem p)
  map_zero_left x := by
    apply Subtype.ext
    exact Hamb_zero x
  map_one_left x := by
    apply Subtype.ext
    exact Hamb_one x

/-! ## The homotopy equivalence -/

set_option linter.unusedVariables false in
theorem sphereBandHomotopyEquiv (m : ℕ) (hm : 1 ≤ m) :
    Nonempty (ContinuousMap.HomotopyEquiv
      {x : EuclideanSpace ℝ (Fin (m+1)) // ‖x‖ = 1 ∧ x (Fin.last m) > -(1/2) ∧ x (Fin.last m) < 1/2}
      {y : EuclideanSpace ℝ (Fin m) // ‖y‖ = 1}) := by
  have hfg : (fMap m).comp (gMap m) = ContinuousMap.id (Sph m) := by
    apply ContinuousMap.ext
    intro y
    simpa using fMap_gMap m y
  have hcomp : ContinuousMap.Homotopy ((fMap m).comp (gMap m)) (ContinuousMap.id (Sph m)) :=
    (ContinuousMap.Homotopy.refl ((fMap m).comp (gMap m))).cast rfl hfg
  exact Nonempty.intro (ContinuousMap.HomotopyEquiv.mk (fMap m) (gMap m)
    ⟨(HambHomotopy m).symm⟩ ⟨hcomp⟩)

end Work.Cohomology
