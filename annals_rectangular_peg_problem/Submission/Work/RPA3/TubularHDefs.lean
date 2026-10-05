import Mathlib
import Submission.Work.RPA3.A3Defs
import Submission.Work.RPA3.TubularDefs
import Submission.Work.RPA3.Symp
import Submission.Work.RPA3.theta_std
import Submission.Work.RPA3.theta_per
import Submission.Work.RPA3.theta_per_int
import Submission.Work.RPA3.ell_per_int
import Submission.Work.RPA3.InjectiveDefs
import Submission.Work.RPA3.contDiff_thetaP
import Submission.Work.RPA3.exists_local_chart

/-!
# RPA3, D2: the tubular Hamiltonian `H₀` (definitions and well-definedness)

This file fixes the object that the D2 construction (`exists_tubular_H`) produces.

`HasWitness L T τ y` says that `y` is the image of some strip point `w = ((x,t),ξ)` with
`‖ξ‖ < T.ε` under the tubular map `θ`.  For `τ ∈ [-1,2]` this witness is *unique*: the tubular
map is injective on the strip modulo the periodicity of the angle (`T.inj`), and a shift of the
angle by an integer multiple of `2π` changes the point by `Tk`, so no two distinct witnesses can
give the same `y` (see `witness_unique`).

`cutXi ε` is the flat cut-off in the transverse variable: it is `1` for `s ≤ ε/4` and `0` for
`s ≥ ε/2`.  It is what makes the construction smooth: `H0` vanishes identically as soon as the
`ξ`-coordinate of the witness reaches `ε/2`, and since `ε/2 < ε` that is strictly inside the
injectivity radius, so the boundary of the tube is not seen by the cut-off function.

`H0 L F T τ y = cutXi T.ε ‖ξ‖ · F.h τ (x,t)` at the witness `(x,t,ξ)` of `y`, and `0` if there is
none.  It is `Tk`-invariant in `y` (because `F.h` is `2π`-periodic in the angle,
`FluxPrimitive.per`), and along the family it reproduces `F.h` (`H0_ell`).
-/

open scoped ContDiff Topology
open Real Classical

set_option autoImplicit false
noncomputable section

namespace Work.RPA3

/-! ## The transverse cut-off -/

/-- The flat cut-off `χ_ξ` on the transverse variable `ξ : ℝ × ℝ`: `1` near `ξ = 0` and `0` for
`‖ξ‖ ≥ ε/2`.

It is written as a function of the *square* of the Euclidean norm, `ξ₁² + ξ₂²`, rather than of
`‖ξ‖` itself: for the product (max) norm on `ℝ × ℝ`, `ξ ↦ ‖ξ‖` is not smooth away from the
diagonal, while `ξ ↦ ξ₁² + ξ₂²` is a polynomial (hence smooth), as is any smooth function of it. -/
noncomputable def cutXi (ε : ℝ) (ξ : ℝ × ℝ) : ℝ :=
  Real.smoothTransition (((ε / 2) ^ 2 - (ξ.1 ^ 2 + ξ.2 ^ 2)) / ((ε / 2) ^ 2 - (ε / 4) ^ 2))

theorem cutXi_contDiff (ε : ℝ) (n : ℕ) : ContDiff ℝ n (cutXi ε) := by
  unfold cutXi
  apply Real.smoothTransition.contDiff.comp
  fun_prop

theorem cutXi_zero {ε : ℝ} (hε : ε ≠ 0) : cutXi ε 0 = 1 := by
  unfold cutXi
  have h0 : ((0 : ℝ × ℝ).1 ^ 2 + (0 : ℝ × ℝ).2 ^ 2) = 0 := by norm_num
  have h : ((ε / 2) ^ 2 - ((0 : ℝ × ℝ).1 ^ 2 + (0 : ℝ × ℝ).2 ^ 2)) /
      ((ε / 2) ^ 2 - (ε / 4) ^ 2) = 4 / 3 := by
    rw [h0]; field_simp; ring
  rw [h]; exact Real.smoothTransition.one_of_one_le (by norm_num)

theorem cutXi_eq_zero {ε : ℝ} (hε : 0 < ε) {ξ : ℝ × ℝ} (h : ε / 2 ≤ ‖ξ‖) : cutXi ε ξ = 0 := by
  unfold cutXi
  apply Real.smoothTransition.zero_of_nonpos
  have hden : (0 : ℝ) < (ε / 2) ^ 2 - (ε / 4) ^ 2 := by
    have h : (ε / 2) ^ 2 - (ε / 4) ^ 2 = (3 / 4) * (ε / 2) ^ 2 := by ring
    rw [h]; positivity
  refine div_nonpos_of_nonpos_of_nonneg ?_ (le_of_lt hden)
  have hsq : (ε / 2) ^ 2 ≤ ξ.1 ^ 2 + ξ.2 ^ 2 := by
    have hmax : ‖ξ‖ = max |ξ.1| |ξ.2| := by simp [Prod.norm_def]
    have h3 : (ε / 2) ^ 2 ≤ ‖ξ‖ ^ 2 := by nlinarith [h, hε]
    have h4 : ‖ξ‖ ^ 2 ≤ ξ.1 ^ 2 + ξ.2 ^ 2 := by
      rw [hmax]
      rcases le_total |ξ.1| |ξ.2| with hh | hh
      · rw [max_eq_right hh, sq_abs]; nlinarith [sq_nonneg ξ.1]
      · rw [max_eq_left hh, sq_abs]; nlinarith [sq_nonneg ξ.2]
    linarith
  linarith

/-! ## The witness predicate -/

/-- `w : PS` is a *witness* of `y` at time `τ` if `‖w.2‖ < T.ε` and `θ(τ, w.1.1, w.1.2, w.2) = y`. -/
def HasWitness (L : LagFamilyAll) (T : TubularData L) (τ : ℝ) (y : PS) : Prop :=
  ∃ w : PS, ‖w.2‖ < T.ε ∧ theta L τ w.1.1 w.1.2 w.2 = y

/-- The (chosen) witness of `y` at time `τ`. -/
noncomputable def wit (L : LagFamilyAll) (T : TubularData L) (τ : ℝ) (y : PS)
    (h : HasWitness L T τ y) : PS := Classical.choose h

theorem wit_spec (L : LagFamilyAll) (T : TubularData L) (τ : ℝ) (y : PS)
    (h : HasWitness L T τ y) :
    ‖(wit L T τ y h).2‖ < T.ε ∧ theta L τ (wit L T τ y h).1.1 (wit L T τ y h).1.2
      (wit L T τ y h).2 = y :=
  Classical.choose_spec h

theorem wit_norm (L : LagFamilyAll) (T : TubularData L) (τ : ℝ) (y : PS)
    (h : HasWitness L T τ y) : ‖(wit L T τ y h).2‖ < T.ε :=
  (wit_spec L T τ y h).1

theorem theta_wit (L : LagFamilyAll) (T : TubularData L) (τ : ℝ) (y : PS)
    (h : HasWitness L T τ y) :
    theta L τ (wit L T τ y h).1.1 (wit L T τ y h).1.2 (wit L T τ y h).2 = y :=
  (wit_spec L T τ y h).2

/-! ## The tubular Hamiltonian -/

/-- The tubular Hamiltonian at time `τ`: the cut-off transverse variable times the flux primitive
at the witness of `y`, and `0` if `y` has no witness. -/
noncomputable def H0 (L : LagFamilyAll) (F : FluxPrimitive L) (T : TubularData L) :
    ℝ → PS → ℝ :=
  fun τ y => if h : HasWitness L T τ y then
    cutXi T.ε (wit L T τ y h).2 * F.h τ (wit L T τ y h).1 else 0

theorem H0_of (L : LagFamilyAll) (F : FluxPrimitive L) (T : TubularData L) (τ : ℝ) (y : PS)
    (h : HasWitness L T τ y) :
    H0 L F T τ y = cutXi T.ε (wit L T τ y h).2 * F.h τ (wit L T τ y h).1 := by
  rw [H0, dif_pos h]

theorem H0_of_not (L : LagFamilyAll) (F : FluxPrimitive L) (T : TubularData L) (τ : ℝ) (y : PS)
    (h : ¬ HasWitness L T τ y) : H0 L F T τ y = 0 := by
  rw [H0, dif_neg h]

/-- `H0` vanishes as soon as the witness has transverse coordinate `‖ξ‖ ≥ ε/2`. -/
theorem H0_eq_zero_of_witness_far (L : LagFamilyAll) (F : FluxPrimitive L) (T : TubularData L)
    (τ : ℝ) (y : PS) (h : HasWitness L T τ y) (hξ : T.ε / 2 ≤ ‖(wit L T τ y h).2‖) :
    H0 L F T τ y = 0 := by
  rw [H0_of L F T τ y h, cutXi_eq_zero T.εpos hξ, zero_mul]

/-! ## The angle shift -/

/-- `θ` is `Tk`-equivariant under a shift of the angle by `2πk`. -/
theorem theta_Tk_apply (L : LagFamilyAll) (τ : ℝ) (k : ℤ) (w : PS) :
    theta L τ (Tk k w).1.1 (Tk k w).1.2 (Tk k w).2 =
      Tk k (theta L τ w.1.1 w.1.2 w.2) := by
  simpa only [Tk] using theta_per_int L τ w.1.1 w.1.2 w.2 k

theorem HasWitness_Tk (L : LagFamilyAll) (T : TubularData L) (τ : ℝ) (k : ℤ) (y : PS) :
    HasWitness L T τ (Tk k y) → HasWitness L T τ y := by
  rintro ⟨w, hε, hθ⟩
  exact ⟨Tk (-k) w, by simpa using hε, by rw [theta_Tk_apply, hθ, Tk_neg_apply]⟩

theorem HasWitness_Tk' (L : LagFamilyAll) (T : TubularData L) (τ : ℝ) (k : ℤ) (y : PS) :
    HasWitness L T τ y → HasWitness L T τ (Tk k y) := by
  rintro ⟨w, hε, hθ⟩
  exact ⟨Tk k w, by simpa using hε, by rw [theta_Tk_apply, hθ]⟩

/-! ## Reduction of the angle to a fundamental period -/

/-- Every real is `t' + 2πk` with `t' ∈ [0, 2π)`. -/
theorem exists_shift_two_pi_Ico (t : ℝ) :
    ∃ t' ∈ Set.Ico (0 : ℝ) (2 * π), ∃ k : ℤ, t = t' + 2 * π * (k : ℝ) := by
  set m : ℤ := ⌊t / (2 * π)⌋ with hm
  refine ⟨t - (m : ℝ) * (2 * π), ?_, m, by ring⟩
  have h2pi : (0 : ℝ) < 2 * π := by positivity
  have hfloor : (m : ℝ) ≤ t / (2 * π) := Int.floor_le _
  have hlt : t / (2 * π) < (m : ℝ) + 1 := Int.lt_floor_add_one _
  constructor
  · have := mul_le_mul_of_nonneg_right hfloor (le_of_lt h2pi)
    rw [div_mul_cancel₀ _ (ne_of_gt h2pi)] at this
    linarith
  · have := mul_lt_mul_of_pos_right hlt h2pi
    rw [div_mul_cancel₀ _ (ne_of_gt h2pi)] at this
    linarith

/-- **Uniqueness of the witness.**  For `τ ∈ [-1,2]` and `‖ξ‖ < ε` the tubular map is injective
on the strip, so a point `y` has at most one witness. -/
theorem witness_unique (L : LagFamilyAll) (T : TubularData L) {τ : ℝ}
    (hτ : τ ∈ Set.Icc (-1 : ℝ) 2) {y w w' : PS}
    (hw : ‖w.2‖ < T.ε ∧ theta L τ w.1.1 w.1.2 w.2 = y)
    (hw' : ‖w'.2‖ < T.ε ∧ theta L τ w'.1.1 w'.1.2 w'.2 = y) : w = w' := by
  obtain ⟨t₀, ht₀, a, ha⟩ := exists_shift_two_pi_Ico w.1.2
  obtain ⟨t₀', ht₀', a', ha'⟩ := exists_shift_two_pi_Ico w'.1.2
  have h2pi : (0 : ℝ) < 2 * π := by positivity
  have hz : theta L τ w.1.1 t₀ w.2 = Tk (-a) y := by
    have h := theta_per_int L τ w.1.1 t₀ w.2 a
    rw [← ha] at h
    have hh : Tk a (theta L τ w.1.1 t₀ w.2) = y := by rw [← h]; exact hw.2
    have hc := congrArg (Tk (-a)) hh
    rwa [Tk_neg_apply] at hc
  have hz' : theta L τ w'.1.1 t₀' w'.2 = Tk (-a') y := by
    have h := theta_per_int L τ w'.1.1 t₀' w'.2 a'
    rw [← ha'] at h
    have hh : Tk a' (theta L τ w'.1.1 t₀' w'.2) = y := by rw [← h]; exact hw'.2
    have hc := congrArg (Tk (-a')) hh
    rwa [Tk_neg_apply] at hc
  have hkey : theta L τ w.1.1 t₀ w.2 = Tk (a' - a) (theta L τ w'.1.1 t₀' w'.2) := by
    rw [hz, hz']
    have : Tk (a' - a) (Tk (-a') y) = Tk (-a) y := by
      rw [← Tk_add]; congr 1; ring
    rw [this]
  obtain ⟨hx, hξ, m, hm⟩ := T.inj τ hτ w.1.1 t₀ w'.1.1 t₀' w.2 w'.2
    (Set.Ico_subset_Icc_self ht₀) (Set.Ico_subset_Icc_self ht₀') hw.1 hw'.1 (a' - a) hkey
  have ht_eq : t₀' = t₀ := by
    have hm_lt : (m : ℝ) < 1 := by
      have h1 : 2 * π * (m : ℝ) < 2 * π * 1 := by nlinarith [h2pi, hm, ht₀.1, ht₀'.2]
      exact lt_of_mul_lt_mul_left h1 (le_of_lt h2pi)
    have hm_gt : (-1 : ℝ) < (m : ℝ) := by
      have h1 : 2 * π * (-1) < 2 * π * (m : ℝ) := by nlinarith [h2pi, hm, ht₀.2, ht₀'.1]
      exact lt_of_mul_lt_mul_left h1 (le_of_lt h2pi)
    have h5 : m = 0 := by
      have h1' : (m : ℤ) < 1 := by exact_mod_cast hm_lt
      have h2' : (-1 : ℤ) < m := by exact_mod_cast hm_gt
      omega
    rw [h5] at hm; simpa using hm
  have haa : a = a' := by
    have hsubst : theta L τ w'.1.1 t₀' w'.2 = theta L τ w.1.1 t₀ w.2 := by
      rw [hx, ht_eq, ← hξ]
    have hTk : Tk (-a) y = Tk (-a') y := by rw [← hz, ← hz', hsubst]
    have h := congrArg (Tk a) hTk
    rw [← Tk_add, ← Tk_add] at h
    rw [show a + -a = 0 by ring, show a + -a' = a - a' by ring, Tk_zero] at h
    have h3 := (Tk_eq_self_iff (a - a') y).mp h.symm
    omega
  rw [Prod.ext_iff]
  refine ⟨?_, hξ⟩
  rw [Prod.ext_iff]
  exact ⟨hx, by rw [ha, ha', ht_eq, haa]⟩

/-! ## Periodicity of the flux primitive in the angle -/

/-- `F.h τ (x, ·)` is periodic of period `2π k` for every integer `k`. -/
theorem hf_per_int (L : LagFamilyAll) (F : FluxPrimitive L) (τ x : ℝ) (k : ℤ) (t : ℝ) :
    F.h τ (x, t + 2 * π * (k : ℝ)) = F.h τ (x, t) := by
  have hper : Function.Periodic (fun s : ℝ => F.h τ (x, s)) (2 * π) := fun s => F.per τ x s
  have := hper.int_mul k t
  simpa [mul_comm] using this

/-! ## The two defining properties of `H0` -/

/-- Along the family, `H0` reproduces the flux primitive. -/
theorem H0_ell (L : LagFamilyAll) (F : FluxPrimitive L) (T : TubularData L) {τ : ℝ}
    (hτ : τ ∈ Set.Icc (-1 : ℝ) 2) (x t : ℝ) :
    H0 L F T τ (L.ℓ τ (x, t)) = F.h τ (x, t) := by
  have hwit : HasWitness L T τ (L.ℓ τ (x, t)) :=
    ⟨((x, t), (0, 0)), by simpa using T.εpos, by simp [theta_zero]⟩
  have heq : wit L T τ (L.ℓ τ (x, t)) hwit = ((x, t), (0, 0)) :=
    witness_unique L T hτ (wit_spec L T τ _ hwit)
      ⟨by simpa using T.εpos, by simp [theta_zero]⟩
  rw [H0_of L F T τ _ hwit, heq]
  change cutXi T.ε (0 : ℝ × ℝ) * F.h τ (x, t) = F.h τ (x, t)
  rw [cutXi_zero (ne_of_gt T.εpos), one_mul]

/-- The chosen witness of `Tk k y` is `Tk k` of the chosen witness of `y`. -/
theorem wit_Tk (L : LagFamilyAll) (T : TubularData L) {τ : ℝ}
    (hτ : τ ∈ Set.Icc (-1 : ℝ) 2) (k : ℤ) (y : PS) (h : HasWitness L T τ y) :
    wit L T τ (Tk k y) (HasWitness_Tk' L T τ k y h) = Tk k (wit L T τ y h) := by
  refine witness_unique L T hτ (wit_spec L T τ _ _) ?_
  refine ⟨by simpa using wit_norm L T τ y h, ?_⟩
  rw [theta_Tk_apply, theta_wit]

/-- `H0` is invariant under the shift `Tk k` of the angle. -/
theorem H0_Tk (L : LagFamilyAll) (F : FluxPrimitive L) (T : TubularData L) {τ : ℝ}
    (hτ : τ ∈ Set.Icc (-1 : ℝ) 2) (k : ℤ) (y : PS) :
    H0 L F T τ (Tk k y) = H0 L F T τ y := by
  by_cases h : HasWitness L T τ y
  · have h' : HasWitness L T τ (Tk k y) := HasWitness_Tk' L T τ k y h
    rw [H0_of L F T τ _ h', H0_of L F T τ _ h, wit_Tk L T hτ k y h]
    show cutXi T.ε (wit L T τ y h).2 *
        F.h τ ((wit L T τ y h).1.1, (wit L T τ y h).1.2 + 2 * π * (k : ℝ))
      = cutXi T.ε (wit L T τ y h).2 * F.h τ (wit L T τ y h).1
    rw [hf_per_int L F τ (wit L T τ y h).1.1 k (wit L T τ y h).1.2]
  · have h' : ¬ HasWitness L T τ (Tk k y) := fun hh => h (HasWitness_Tk L T τ k y hh)
    rw [H0_of_not L F T τ _ h', H0_of_not L F T τ _ h]

/-! ## The standard (outer) region -/

/-- A point of the form `θ(τ,x,t,ξ) = ((x,t),(-ξ₁,-ξ₂))` in the standard region `|x| ≥ X₀` has
`((x,t),ξ)` as its witness. -/
theorem HasWitness_std (L : LagFamilyAll) (T : TubularData L) (τ x t : ℝ) (ξ : ℝ × ℝ)
    (hx : L.X0 ≤ |x|) (hξ : ‖ξ‖ < T.ε) :
    HasWitness L T τ ((x, t), (-ξ.1, -ξ.2)) :=
  ⟨((x, t), ξ), hξ, by rw [theta_std L τ x t ξ hx]⟩

end Work.RPA3
