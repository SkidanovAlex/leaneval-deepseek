/-
# The character expansion of *FI* §16 (16.11)/(17.10)

Detecting the congruence `z₁ ≡ ω z₂ (mod Q)` by the characters of the Gaussian unit group
`G = (ℤ[i]/Q)^*` yields the expansion (16.11):

  `Σ_ω w(ω) Σ_{x,y : π y = ω π x} c x c̄ y  =  (1/|G|) Σ_χ J(χ) |S_χ|²`,

with `J(χ) = Σ_{p ∈ G} w(p)χ(p)` and `S_χ = Σ_z c(z)χ(π z)`.  This file instantiates the abstract
orthogonality `Work.FIArea7.char_expansion_pair` at the §17 situation:

* `G = (ℤ[i]/Q)^*` in the coordinate model `GaussUnit Q`;
* the class map `unitClassD Q : ℤ[i] → G` (the identity off the units);
* the weight `ratWeight Q e`, i.e. `(ω|e)` on the rational classes `(ω, 0)` and `0` elsewhere
  (`Work.FIArea7.sum_omegaDetect_eq_ratWeight` identifies this with the `ω`-sum of (17.9)).

The result is the *exact* form of (16.11)/(17.10) for the coefficient family of §17.
-/
import Mathlib
import Submission.Work.FIArea7.Section16Detection
import Submission.Work.FIArea7.char_expansion_pair

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The Gaussian unit group `(ℤ[i]/Q)^*` in the coordinate model of `GaussUnits`. -/
abbrev GaussUnit (Q : ℕ) := {p : ZMod Q × ZMod Q // IsUnit (gaussNorm p)}

/-- The class of `z` in `G = (ℤ[i]/Q)^*`, with the identity as a default for the non-units. -/
noncomputable def unitClassD (Q : ℕ) (z : GaussianInt) : GaussUnit Q :=
  if h : Nat.Coprime (Work.FIPlan.gnorm z) Q then gaussUnitOf Q z h else 1

/-- On the units, `unitClassD` is the class map. -/
lemma unitClassD_eq (Q : ℕ) (z : GaussianInt) (h : Nat.Coprime (Work.FIPlan.gnorm z) Q) :
    unitClassD Q z = gaussUnitOf Q z h := dif_pos h

/-- The indicator of the units modulo `Q`, as a complex number. -/
def unitInd (Q : ℕ) (z : GaussianInt) : ℂ := if Nat.Coprime (Work.FIPlan.gnorm z) Q then 1 else 0

lemma star_unitInd (Q : ℕ) (z : GaussianInt) : star (unitInd Q z) = unitInd Q z := by
  rw [unitInd]; by_cases h : Nat.Coprime (Work.FIPlan.gnorm z) Q <;> simp [h]

/-- The coefficient `z ↦ c̄(z)·[z unit mod Q]` fed to `char_expansion_pair`. -/
def unitCoeff (Q : ℕ) (c : GaussianInt → ℂ) (z : GaussianInt) : ℂ := star (c z) * unitInd Q z

lemma star_unitCoeff (Q : ℕ) (c : GaussianInt → ℂ) (z : GaussianInt) :
    star (unitCoeff Q c z) = c z * unitInd Q z := by
  simp only [unitCoeff, star_mul, star_star, star_unitInd]
  ring

/-- **(16.11) over the Gaussian unit group.**  The `ω`-detection sum over `G` of `β x·c̄onj(β y)`
with `β z = c̄(z)[(gnorm z, Q) = 1]` equals `(1/|G|)Σ_χ J(χ)|S_χ|²`. -/
theorem section16_gauss_expansion (Rz : ℤ) (Q e : ℕ) [NeZero Q] (c : GaussianInt → ℂ) :
    (∑ p : GaussUnit Q, ratWeight Q e p *
        ∑ x : {z : GaussianInt // z ∈ Work.FIPlan.gBox Rz},
        ∑ y : {z : GaussianInt // z ∈ Work.FIPlan.gBox Rz},
          (if unitClassD Q y.1 = p * unitClassD Q x.1 then
            unitCoeff Q c x.1 * star (unitCoeff Q c y.1) else 0))
      = (1 / (Fintype.card (GaussUnit Q) : ℂ)) *
        ∑ χ : AddChar (Additive (GaussUnit Q)) ℂ,
          (∑ p : GaussUnit Q, ratWeight Q e p * χ (Additive.ofMul p)) *
            ((∑ z : {z : GaussianInt // z ∈ Work.FIPlan.gBox Rz},
                unitCoeff Q c z.1 * χ (Additive.ofMul (unitClassD Q z.1))) *
             star (∑ z : {z : GaussianInt // z ∈ Work.FIPlan.gBox Rz},
                unitCoeff Q c z.1 * χ (Additive.ofMul (unitClassD Q z.1)))) := by
  have h := char_expansion_pair (G := GaussUnit Q)
    (X := {z : GaussianInt // z ∈ Work.FIPlan.gBox Rz})
    (fun z => unitClassD Q z.1) (ratWeight Q e) (fun z => unitCoeff Q c z.1) (fun _ => 1)
  simpa using h


/-- Conversion of a sum over the subtype `{z // z ∈ s}` into a sum over the finset `s`. -/
lemma sum_subtype_gBox (Rz : ℤ) (f : GaussianInt → ℂ) :
    (∑ z : {z : GaussianInt // z ∈ Work.FIPlan.gBox Rz}, f z.1)
      = ∑ z ∈ Work.FIPlan.gBox Rz, f z := by
  rw [← Finset.attach_eq_univ]
  exact Finset.sum_attach _ f

/-- **The pointwise detection identity, with the unit indicators.**  Outside the units both sides
vanish (the indicators); on the units it is `Work.FIArea7.sum_omegaDetect_eq_ratWeight`. -/
lemma unitInd_mul_detect (Q e : ℕ) [NeZero Q] (z1 z2 : GaussianInt) :
    unitInd Q z1 * unitInd Q z2 *
        (∑ p : GaussUnit Q, ratWeight Q e p *
          (if unitClassD Q z1 = p * unitClassD Q z2 then 1 else 0))
      = unitInd Q z1 * unitInd Q z2 *
        (∑ ω : ZMod Q, (if ((z1.re : ZMod Q) = ω * (z2.re : ZMod Q)) ∧
            ((z1.im : ZMod Q) = ω * (z2.im : ZMod Q))
          then (jacobiSym (ω.val : ℤ) e : ℂ) else 0)) := by
  by_cases h1 : Nat.Coprime (Work.FIPlan.gnorm z1) Q
  · by_cases h2 : Nat.Coprime (Work.FIPlan.gnorm z2) Q
    · have hdet := sum_omegaDetect_eq_ratWeight Q e z1 z2 h1 h2
      have hiff : ∀ p : GaussUnit Q, ratWeight Q e p *
          (if unitClassD Q z1 = p * unitClassD Q z2 then 1 else 0)
          = (if unitClassD Q z1 = p * unitClassD Q z2 then ratWeight Q e p else 0) := by
        intro p
        by_cases h : unitClassD Q z1 = p * unitClassD Q z2 <;> simp [h]
      rw [unitInd, unitInd, if_pos h1, if_pos h2]
      simp only [one_mul]
      rw [Finset.sum_congr rfl (fun p _ => hiff p),
        unitClassD_eq Q z1 h1, unitClassD_eq Q z2 h2, hdet]
    · have hz2 : unitInd Q z2 = 0 := by rw [unitInd]; simp [h2]
      rw [hz2]; simp [zero_mul]
  · have hz1 : unitInd Q z1 = 0 := by rw [unitInd]; simp [h1]
    rw [hz1]; simp [zero_mul]

/-- The pointwise detection with a prefactor (the shape in which the box sum consumes it). -/
lemma detect_factor (Q e : ℕ) [NeZero Q] (z1 z2 : GaussianInt) (K : ℂ) :
    K * (unitInd Q z2 * unitInd Q z1) *
        (∑ p : GaussUnit Q, ratWeight Q e p *
          (if unitClassD Q z1 = p * unitClassD Q z2 then 1 else 0))
      = K * (unitInd Q z2 * unitInd Q z1) *
        (∑ ω : ZMod Q, (if ((z1.re : ZMod Q) = ω * (z2.re : ZMod Q)) ∧
            ((z1.im : ZMod Q) = ω * (z2.im : ZMod Q))
          then (jacobiSym (ω.val : ℤ) e : ℂ) else 0)) := by
  have h := unitInd_mul_detect Q e z1 z2
  calc K * (unitInd Q z2 * unitInd Q z1) *
        (∑ p : GaussUnit Q, ratWeight Q e p *
          (if unitClassD Q z1 = p * unitClassD Q z2 then 1 else 0))
      = K * (unitInd Q z1 * unitInd Q z2 *
          (∑ p : GaussUnit Q, ratWeight Q e p *
            (if unitClassD Q z1 = p * unitClassD Q z2 then 1 else 0))) := by ring
    _ = K * (unitInd Q z1 * unitInd Q z2 *
          (∑ ω : ZMod Q, (if ((z1.re : ZMod Q) = ω * (z2.re : ZMod Q)) ∧
              ((z1.im : ZMod Q) = ω * (z2.im : ZMod Q))
            then (jacobiSym (ω.val : ℤ) e : ℂ) else 0))) := by rw [h]
    _ = K * (unitInd Q z2 * unitInd Q z1) *
        (∑ ω : ZMod Q, (if ((z1.re : ZMod Q) = ω * (z2.re : ZMod Q)) ∧
            ((z1.im : ZMod Q) = ω * (z2.im : ZMod Q))
          then (jacobiSym (ω.val : ℤ) e : ℂ) else 0)) := by ring

/-- **(16.11)/(17.10) in the box form.**  The `ω`-detection sum of (17.9) over the box, with the
coefficient family `c` of §17, equals the `(1/|G|)Σ_χ J(χ)|S_χ|²` of (17.10). -/
theorem section16_omegaDetect_expansion (Rz : ℤ) (Q e : ℕ) [NeZero Q] (c : GaussianInt → ℂ) :
    (∑ z1 ∈ Work.FIPlan.gBox Rz, ∑ z2 ∈ Work.FIPlan.gBox Rz,
        unitInd Q z1 * unitInd Q z2 * (c z1 * star (c z2)) *
          (∑ ω : ZMod Q, (if ((z1.re : ZMod Q) = ω * (z2.re : ZMod Q)) ∧
              ((z1.im : ZMod Q) = ω * (z2.im : ZMod Q))
            then (jacobiSym (ω.val : ℤ) e : ℂ) else 0)))
      = (1 / (Fintype.card (GaussUnit Q) : ℂ)) *
        ∑ χ : AddChar (Additive (GaussUnit Q)) ℂ,
          (∑ p : GaussUnit Q, ratWeight Q e p * χ (Additive.ofMul p)) *
            ((∑ z ∈ Work.FIPlan.gBox Rz,
                unitCoeff Q c z * χ (Additive.ofMul (unitClassD Q z))) *
             star (∑ z ∈ Work.FIPlan.gBox Rz,
                unitCoeff Q c z * χ (Additive.ofMul (unitClassD Q z)))) := by
  -- the right-hand side of `section16_gauss_expansion`, with the subtype sums pushed to the box
  have hR : (1 / (Fintype.card (GaussUnit Q) : ℂ)) *
        ∑ χ : AddChar (Additive (GaussUnit Q)) ℂ,
          (∑ p : GaussUnit Q, ratWeight Q e p * χ (Additive.ofMul p)) *
            ((∑ z : {z : GaussianInt // z ∈ Work.FIPlan.gBox Rz},
                unitCoeff Q c z.1 * χ (Additive.ofMul (unitClassD Q z.1))) *
             star (∑ z : {z : GaussianInt // z ∈ Work.FIPlan.gBox Rz},
                unitCoeff Q c z.1 * χ (Additive.ofMul (unitClassD Q z.1))))
      = (1 / (Fintype.card (GaussUnit Q) : ℂ)) *
        ∑ χ : AddChar (Additive (GaussUnit Q)) ℂ,
          (∑ p : GaussUnit Q, ratWeight Q e p * χ (Additive.ofMul p)) *
            ((∑ z ∈ Work.FIPlan.gBox Rz,
                unitCoeff Q c z * χ (Additive.ofMul (unitClassD Q z))) *
             star (∑ z ∈ Work.FIPlan.gBox Rz,
                unitCoeff Q c z * χ (Additive.ofMul (unitClassD Q z)))) := by
    congr 1
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    rw [sum_subtype_gBox Rz (fun z => unitCoeff Q c z * χ (Additive.ofMul (unitClassD Q z)))]
  -- the left-hand side of the group expansion, in the required shape
  have hL : (∑ p : GaussUnit Q, ratWeight Q e p *
        ∑ x : {z : GaussianInt // z ∈ Work.FIPlan.gBox Rz},
        ∑ y : {z : GaussianInt // z ∈ Work.FIPlan.gBox Rz},
          (if unitClassD Q y.1 = p * unitClassD Q x.1 then
            unitCoeff Q c x.1 * star (unitCoeff Q c y.1) else 0))
      = ∑ x ∈ Work.FIPlan.gBox Rz, ∑ y ∈ Work.FIPlan.gBox Rz,
          (star (c x) * c y) * (unitInd Q x * unitInd Q y) *
            (∑ p : GaussUnit Q, ratWeight Q e p *
              (if unitClassD Q y = p * unitClassD Q x then 1 else 0)) := by
    conv_lhs =>
      enter [2, p]
      rw [sum_subtype_gBox Rz (fun z =>
        ∑ y : {z : GaussianInt // z ∈ Work.FIPlan.gBox Rz},
          (if unitClassD Q y.1 = p * unitClassD Q z then
            unitCoeff Q c z * star (unitCoeff Q c y.1) else 0))]
      enter [2, 2, x]
      rw [sum_subtype_gBox Rz (fun z =>
        (if unitClassD Q z = p * unitClassD Q x then
          unitCoeff Q c x * star (unitCoeff Q c z) else 0))]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [unitCoeff, star_unitCoeff]
    by_cases h : unitClassD Q y = p * unitClassD Q x
    · simp only [if_pos h]; ring
    · simp only [if_neg h]; ring
  -- and now the pointwise detection turns it into the box form
  have hL2 : (∑ z1 ∈ Work.FIPlan.gBox Rz, ∑ z2 ∈ Work.FIPlan.gBox Rz,
        unitInd Q z1 * unitInd Q z2 * (c z1 * star (c z2)) *
          (∑ ω : ZMod Q, (if ((z1.re : ZMod Q) = ω * (z2.re : ZMod Q)) ∧
              ((z1.im : ZMod Q) = ω * (z2.im : ZMod Q))
            then (jacobiSym (ω.val : ℤ) e : ℂ) else 0)))
      = (∑ x ∈ Work.FIPlan.gBox Rz, ∑ y ∈ Work.FIPlan.gBox Rz,
          (star (c x) * c y) * (unitInd Q x * unitInd Q y) *
            (∑ p : GaussUnit Q, ratWeight Q e p *
              (if unitClassD Q y = p * unitClassD Q x then 1 else 0))) := by
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    rw [detect_factor Q e y x (star (c x) * c y)]
    ring
  exact (hL2.trans hL.symm).trans ((section16_gauss_expansion Rz Q e c).trans hR)

end

end Work.FIArea7
