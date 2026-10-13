/-
# Extracting the individual terms of the `H^k`-norm as honest integrals

`HkMem α n g` says that the `H^k`-integrand of `g` has honest iterated integrals, i.e.
that `z ↦ ∫_θ HkIntegrand α n g z θ` is integrable on `Iz` and that every angular slice
`θ ↦ HkIntegrand α n g z θ` is integrable on `Iθ`.  The integrand is a sum of squares of
weighted derivatives, so each individual summand inherits those two integrability
properties; this file records the extracted consequences for the two families of
summands, in the *unweighted* form in which the rest of the development consumes them:

* `(D_z^m g)² · sin(2θ)^{-η}` on every angular slice and, multiplied by `w²`, over `Iz`;
* `(D_z^j D_θ^i g)² · sin(2θ)^{-γ}` for `1 ≤ i`, `i + j ≤ n`, again in both senses.

The only thing that separates a summand of `HkIntegrand` from the corresponding
unweighted expression is the *square* of the weight `w(z)²` (resp. the rearrangement
`w·sin(2θ)^{-γ/2} = w/ sin(2θ)^{γ/2}`), which is a positive constant in `z` as soon as
`z > 0`; the algebraic identity behind this is `(x^{-e/2})² = x^{-e}` for `x ≥ 0`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.CTDefs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Coercivity.Eztheta1_eq_HkSq_one

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## The elementary `rpow` identity and the pointwise extraction -/

/-- `(x^{-e/2})² = x^{-e}` for `x ≥ 0`.  Both sides vanish at `x = 0` when `e ≠ 0`, and
are `1` when `e = 0`; the statement is uniform in `e`. -/
private lemma rpow_neg_half_sq {s e : ℝ} (hs : 0 ≤ s) : (s ^ (-(e / 2))) ^ 2 = s ^ (-e) := by
  rw [← Real.rpow_natCast (s ^ (-(e / 2))) 2, ← Real.rpow_mul hs (-(e / 2)) ((2 : ℕ) : ℝ)]
  congr 1
  push_cast
  ring

/-- Extraction identity in the divided form used by the pure `D_z` summands of
`HkIntegrand`, where the weight enters as `w / sin(2θ)^{e/2}`. -/
private lemma div_weight_sq {A W s e : ℝ} (hs : 0 ≤ s) :
    (A * (W / s ^ (e / 2))) ^ 2 = A ^ 2 * W ^ 2 * s ^ (-e) := by
  have h : (s ^ (-(e / 2))) ^ 2 = s ^ (-e) := rpow_neg_half_sq hs
  calc (A * (W / s ^ (e / 2))) ^ 2 = A ^ 2 * W ^ 2 * (s ^ (-(e / 2))) ^ 2 := by
        rw [div_eq_mul_inv, ← Real.rpow_neg hs (e / 2)]
        ring
    _ = A ^ 2 * W ^ 2 * s ^ (-e) := by rw [h]

/-- Extraction identity in the multiplied form used by the mixed summands of
`HkIntegrand`, where the weight enters as `Wt = w · sin(2θ)^{-γ/2}`. -/
private lemma mul_weight_sq {A W s e : ℝ} (hs : 0 ≤ s) :
    (A * (W * s ^ (-(e / 2)))) ^ 2 = A ^ 2 * W ^ 2 * s ^ (-e) := by
  have h : (s ^ (-(e / 2))) ^ 2 = s ^ (-e) := rpow_neg_half_sq hs
  calc (A * (W * s ^ (-(e / 2)))) ^ 2 = A ^ 2 * W ^ 2 * (s ^ (-(e / 2))) ^ 2 := by ring
    _ = A ^ 2 * W ^ 2 * s ^ (-e) := by rw [h]

/-- `sin (2θ) ≥ 0` on `Iθ`. -/
private lemma sin_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

/-- Pointwise identification of the `m`-th pure `D_z` summand of `HkIntegrand` with the
unweighted expression `(D_z^m g)² sin(2θ)^{-η}`. -/
private lemma dz_slice_pointwise {z θ : ℝ} (hθ : θ ∈ Spaces.Iθ) (A : ℝ) :
    (A * (Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2))) ^ 2
      = A ^ 2 * (Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta) :=
  div_weight_sq (A := A) (W := Spaces.w z) (s := Real.sin (2 * θ)) (e := Spaces.eta)
    (sin_nonneg_Iθ hθ)

/-- Pointwise identification of the mixed summand `(D_z^j D_θ^i g · Wt)²` of
`HkIntegrand` with the unweighted expression `(D_z^j D_θ^i g)² w² sin(2θ)^{-γ}`. -/
private lemma mixed_slice_pointwise {α z θ : ℝ} (hθ : θ ∈ Spaces.Iθ) (A : ℝ) :
    (A * Spaces.Wt α z θ) ^ 2
      = A ^ 2 * (Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_nonneg_Iθ hθ
  simp only [Spaces.Wt, Spaces.wTheta]
  exact mul_weight_sq (A := A) (W := Spaces.w z) (s := Real.sin (2 * θ))
    (e := Spaces.gam α) hs

/-! ## The four conclusions -/

theorem HkMem_terms (α : ℝ) (n : ℕ) (hn : 1 ≤ n) (g : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd g)
    (hmem : Work.Spaces.HkMem α n g) :
    (∀ m ≤ n, ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.DzIter m g z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) Work.Spaces.Iθ)
    ∧ (∀ m ≤ n, MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter m g z θ) ^ 2
        * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) Work.Spaces.Iz)
    ∧ (∀ i : ℕ, 1 ≤ i → ∀ j : ℕ, i + j ≤ n → ∀ z : ℝ, 0 < z →
        MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.mixed j i g z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ)
    ∧ (∀ i : ℕ, 1 ≤ i → ∀ j : ℕ, i + j ≤ n →
        MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed j i g z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iz) := by
  have hdz : ∀ m ≤ n, Spaces.L2Mem (fun z θ => Spaces.DzIter m g z θ
      * (Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2))) :=
    fun m hm => L2Mem_DzIter_Hwt α n g hsm hmem m hm
  have hmx : ∀ i, 1 ≤ i → ∀ j, i + j ≤ n → Spaces.L2Mem (fun z θ => Spaces.mixed j i g z θ
      * Spaces.Wt α z θ) :=
    fun i hi j hij => L2Mem_mixed_Wt_gen α n g hsm hmem i j hi hij
  have hmeasθ : MeasurableSet Spaces.Iθ := measurableSet_Icc
  have hmeasz : MeasurableSet Spaces.Iz := measurableSet_Ici
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (a) angular slices of the pure `D_z` terms
    intro m hm z hz
    have hzIz : z ∈ Spaces.Iz := le_of_lt hz
    have hwz : Spaces.w z ≠ 0 := by
      simp only [Spaces.w]
      exact div_ne_zero (pow_ne_zero 2 (by linarith [hz])) (pow_ne_zero 2 (ne_of_gt hz))
    have hbase : IntegrableOn (fun θ => ((Spaces.w z) ^ 2)⁻¹
        * (Spaces.DzIter m g z θ * (Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2))) ^ 2)
        Spaces.Iθ := ((hdz m hm).1 z hzIz).const_mul _
    refine hbase.congr_fun ?_ hmeasθ
    intro θ hθ
    show ((Spaces.w z) ^ 2)⁻¹
        * (Spaces.DzIter m g z θ * (Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2))) ^ 2
      = (Spaces.DzIter m g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)
    have h := dz_slice_pointwise (z := z) (θ := θ) hθ (Spaces.DzIter m g z θ)
    rw [h]
    have hw2 : ((Spaces.w z) ^ 2) ≠ 0 := pow_ne_zero 2 hwz
    field_simp
  · -- (b) the `z`-integral of the pure `D_z` terms
    intro m hm
    refine (hdz m hm).2.congr_fun ?_ hmeasz
    intro z hz
    refine MeasureTheory.setIntegral_congr_fun hmeasθ (fun θ hθ => ?_)
    exact dz_slice_pointwise (z := z) (θ := θ) hθ (Spaces.DzIter m g z θ)
  · -- (c) angular slices of the mixed terms
    intro i hi j hij z hz
    have hzIz : z ∈ Spaces.Iz := le_of_lt hz
    have hwz : Spaces.w z ≠ 0 := by
      simp only [Spaces.w]
      exact div_ne_zero (pow_ne_zero 2 (by linarith [hz])) (pow_ne_zero 2 (ne_of_gt hz))
    have hbase : IntegrableOn (fun θ => ((Spaces.w z) ^ 2)⁻¹
        * (Spaces.mixed j i g z θ * Spaces.Wt α z θ) ^ 2) Spaces.Iθ :=
      ((hmx i hi j hij).1 z hzIz).const_mul _
    refine hbase.congr_fun ?_ hmeasθ
    intro θ hθ
    show ((Spaces.w z) ^ 2)⁻¹ * (Spaces.mixed j i g z θ * Spaces.Wt α z θ) ^ 2
      = (Spaces.mixed j i g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
    have h := mixed_slice_pointwise (α := α) (z := z) (θ := θ) hθ (Spaces.mixed j i g z θ)
    rw [h]
    have hw2 : ((Spaces.w z) ^ 2) ≠ 0 := pow_ne_zero 2 hwz
    field_simp
  · -- (d) the `z`-integral of the mixed terms
    intro i hi j hij
    refine (hmx i hi j hij).2.congr_fun ?_ hmeasz
    intro z hz
    refine MeasureTheory.setIntegral_congr_fun hmeasθ (fun θ hθ => ?_)
    exact mixed_slice_pointwise (α := α) (z := z) (θ := θ) hθ (Spaces.mixed j i g z θ)

end Work.Coercivity
