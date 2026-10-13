/-
# `Submission/Work/FTS_MuLipC/RowN/L12Ae.lean` — `L₁₂` linearity at the level of *fields*

The difference row of `N` is proved by polarizing the bilinear map `g ↦ Sn α Φs E g`: the
polarization identity is an identity of *fields*, and to turn it into an identity of the
`L₁₂`-zero-modes one needs the additivity of `L₁₂` **on the fields** `Sn α Φs E x`.

`L₁₂` is an integral, so its additivity is unconditional *except* for the integrability of the
objects integrated: the theorem `Work.FTS.LocData.L12_add_mul` needs the θ-slice integrability
of both data on `Ioi z` and the integrability of the two densities.  For the modulation fields
those facts are produced by the honesty lemma `Work.FTS_MuLipC.RowN.NHonest` of the sibling
file `NHonest.lean`, in the *a.e.-in-`s`* form (that is all the outer integral sees).  This file
records the corresponding a.e.-linearity statements:

* `L12dens_sub_ae` — the angular density of a difference is the difference of the densities,
  a.e.;
* `integrableOn_L12dens_sub` — hence the density of the difference is integrable as soon as the
  two densities are and the slices are a.e. integrable;
* `L12_ae_sub` — `L₁₂ a z = L₁₂ (a - b) z + L₁₂ b z`;
* `L12_const_mul` — homogeneity (unconditional);
* `L12_congrQd` — `L₁₂` sees a field only through its values on the open quadrant.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_MuLipC.RowN.Defs
import Submission.Work.FTS.LocData.L12_add_mul
import Submission.Work.FTS.GalFields.RHS.L12f_congr_of_agreeOnQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_MuLipC.RowN

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The angular density of a difference is the difference of the angular densities, a.e. in `s`:
at every `s` where both θ-slices are integrable the two integrands differ pointwise, so
`MeasureTheory.integral_sub` applies. -/
theorem L12dens_sub_ae {a b : Fn} {z : ℝ}
    (h1 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * a s θ / s) Work.Spaces.Iθ)
    (h2 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * b s θ / s) Work.Spaces.Iθ) :
    (fun s => Work.Construction.L12dens (fun z θ => a z θ - b z θ) s)
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioi z)]
        (fun s => Work.Construction.L12dens a s - Work.Construction.L12dens b s) := by
  filter_upwards [h1, h2] with s hs1 hs2
  have hpt : (fun θ => Work.Spaces.K θ * (a s θ - b s θ) / s)
      = fun θ => Work.Spaces.K θ * a s θ / s - Work.Spaces.K θ * b s θ / s := by
    funext θ
    ring
  simp only [Work.Construction.L12dens, Work.FM.L12dens, Work.Spaces.Iθ]
  rw [hpt]
  exact MeasureTheory.integral_sub hs1 hs2

/-- The `L₁₂`-density of a difference is integrable as soon as the two densities are integrable
and the two θ-slices are a.e. integrable. -/
theorem integrableOn_L12dens_sub {a b : Fn} {z : ℝ}
    (h1 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * a s θ / s) Work.Spaces.Iθ)
    (h2 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * b s θ / s) Work.Spaces.Iθ)
    (h3 : MeasureTheory.IntegrableOn (Work.Construction.L12dens a) (Set.Ioi z))
    (h4 : MeasureTheory.IntegrableOn (Work.Construction.L12dens b) (Set.Ioi z)) :
    MeasureTheory.IntegrableOn
      (fun s => Work.Construction.L12dens (fun z θ => a z θ - b z θ) s) (Set.Ioi z) :=
  (h3.sub h4).congr (L12dens_sub_ae h1 h2).symm

/-- **`L₁₂` is additive on a difference of fields**, in the a.e. form: if the θ-slices of `a`
and `b` are a.e. integrable on `Ioi z` and the densities of `a - b` and `b` are integrable,
then `L₁₂ a z = L₁₂ (a - b) z + L₁₂ b z`.  This is
`Work.FTS.LocData.L12_add_mul` with its (pointwise) slice hypothesis weakened to an a.e. one:
the outer integral only sees a.e. values. -/
theorem L12_ae_sub {a b : Fn} {z : ℝ}
    (h1 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * a s θ / s) Work.Spaces.Iθ)
    (h2 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * b s θ / s) Work.Spaces.Iθ)
    (h3 : MeasureTheory.IntegrableOn
      (fun s => Work.Construction.L12dens (fun z θ => a z θ - b z θ) s) (Set.Ioi z))
    (h4 : MeasureTheory.IntegrableOn (Work.Construction.L12dens b) (Set.Ioi z)) :
    Work.Construction.L12 a z
      = Work.Construction.L12 (fun z θ => a z θ - b z θ) z + Work.Construction.L12 b z := by
  have hkey : (fun s => Work.Construction.L12dens a s)
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioi z)]
        (fun s => Work.Construction.L12dens (fun z θ => a z θ - b z θ) s
          + Work.Construction.L12dens b s) := by
    filter_upwards [L12dens_sub_ae h1 h2] with s hs
    rw [hs]
    ring
  have hkey' : ∀ᵐ s ∂(MeasureTheory.volume : Measure ℝ), s ∈ Set.Ioi z →
      Work.FM.L12dens Work.Spaces.K a s
        = Work.FM.L12dens Work.Spaces.K (fun z θ => a z θ - b z θ) s
          + Work.FM.L12dens Work.Spaces.K b s :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mp hkey
  simp only [Work.Construction.L12, Work.FM.L12]
  rw [MeasureTheory.setIntegral_congr_ae measurableSet_Ioi hkey']
  exact MeasureTheory.integral_add h3 h4

/-- **Homogeneity of `L₁₂` in a constant**, with no hypothesis at all (both sides are the
integral of pointwise equal integrands, and `MeasureTheory.integral_const_mul` is
unconditional). -/
theorem L12_const_mul (c : ℝ) (a : Fn) (z : ℝ) :
    Work.Construction.L12 (fun z θ => c * a z θ) z = c * Work.Construction.L12 a z := by
  simp only [Work.Construction.L12, Work.FM.L12]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    (fun s _ => Work.FTS.LocData.L12dens_const_mul Work.Spaces.K c a s)]
  exact MeasureTheory.integral_const_mul c _

/-- **`L₁₂` only sees the values on the open quadrant** (`Work.FTS.GalFields.RHS.L12f_congr_of_agreeOnQ`,
transported to `Work.Construction.L12`). -/
theorem L12_congrQd {a b : Fn} {z : ℝ} (hz : 0 ≤ z)
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → a z θ = b z θ) :
    Work.Construction.L12 a z = Work.Construction.L12 b z :=
  Work.FTS.GalFields.RHS.L12f_congr_of_agreeOnQ hz h

/-! ## Congruence and combinations of the slices -/

/-- The angular density only sees the pointwise values of the field. -/
theorem L12dens_congr {X Y : Fn} (h : ∀ z θ : ℝ, X z θ = Y z θ) :
    Work.Construction.L12dens X = Work.Construction.L12dens Y := by
  funext s
  simp only [Work.Construction.L12dens, Work.FM.L12dens, Work.Spaces.Iθ]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by rw [h s θ])

/-- A.e. slice integrability of a difference. -/
theorem slices_sub {a b : Fn} {z : ℝ}
    (h1 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * a s θ / s) Work.Spaces.Iθ)
    (h2 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * b s θ / s) Work.Spaces.Iθ) :
    ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * (fun z θ => a z θ - b z θ) s θ / s) Work.Spaces.Iθ := by
  filter_upwards [h1, h2] with s hs1 hs2
  have hpt : (fun θ => Work.Spaces.K θ * (a s θ - b s θ) / s)
      = fun θ => Work.Spaces.K θ * a s θ / s - Work.Spaces.K θ * b s θ / s := by
    funext θ
    ring
  rw [hpt]
  exact hs1.sub hs2

/-- A.e. slice integrability of a sum. -/
theorem slices_add {a b : Fn} {z : ℝ}
    (h1 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * a s θ / s) Work.Spaces.Iθ)
    (h2 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * b s θ / s) Work.Spaces.Iθ) :
    ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * (fun z θ => a z θ + b z θ) s θ / s) Work.Spaces.Iθ := by
  filter_upwards [h1, h2] with s hs1 hs2
  have hpt : (fun θ => Work.Spaces.K θ * (a s θ + b s θ) / s)
      = fun θ => Work.Spaces.K θ * a s θ / s + Work.Spaces.K θ * b s θ / s := by
    funext θ
    ring
  rw [hpt]
  exact hs1.add hs2

/-! ## The linearity statements used by the difference row -/

/-- **`L₁₂` is additive on a difference**, with the density hypotheses carried by the two
fields themselves (the density of the difference is then integrable by
`integrableOn_L12dens_sub`). -/
theorem L12_ae_sub_of_dens {a b : Fn} {z : ℝ}
    (h1 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * a s θ / s) Work.Spaces.Iθ)
    (h2 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * b s θ / s) Work.Spaces.Iθ)
    (h3 : MeasureTheory.IntegrableOn (Work.Construction.L12dens a) (Set.Ioi z))
    (h4 : MeasureTheory.IntegrableOn (Work.Construction.L12dens b) (Set.Ioi z)) :
    Work.Construction.L12 a z
      = Work.Construction.L12 (fun z θ => a z θ - b z θ) z + Work.Construction.L12 b z :=
  L12_ae_sub h1 h2 (integrableOn_L12dens_sub h1 h2 h3 h4) h4

/-- The subtraction form of the a.e. additivity. -/
theorem L12_sub_eq {a b : Fn} {z : ℝ}
    (h1 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * a s θ / s) Work.Spaces.Iθ)
    (h2 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * b s θ / s) Work.Spaces.Iθ)
    (h3 : MeasureTheory.IntegrableOn (Work.Construction.L12dens a) (Set.Ioi z))
    (h4 : MeasureTheory.IntegrableOn (Work.Construction.L12dens b) (Set.Ioi z)) :
    Work.Construction.L12 a z - Work.Construction.L12 b z
      = Work.Construction.L12 (fun z θ => a z θ - b z θ) z := by
  have h := L12_ae_sub_of_dens h1 h2 h3 h4
  rw [h]
  ring


/-- The angular density of the negative is the negative of the density (unconditional). -/
theorem L12dens_neg (b : Fn) :
    Work.Construction.L12dens (fun z θ => -b z θ)
      = fun s => - Work.Construction.L12dens b s := by
  have h1 : (fun z θ => -b z θ) = fun z θ => (-1 : ℝ) * b z θ := by
    funext z θ
    ring
  funext s
  rw [show Work.Construction.L12dens (fun z θ => -b z θ) s
      = Work.FM.L12dens Work.Spaces.K (fun z θ => -b z θ) s from rfl, h1,
    Work.FTS.LocData.L12dens_const_mul Work.Spaces.K (-1) b s, neg_one_mul]
  rfl

/-- A.e. slice integrability of the negative. -/
theorem slices_neg {b : Fn} {z : ℝ}
    (h : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * b s θ / s) Work.Spaces.Iθ) :
    ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * (fun z θ => -b z θ) s θ / s) Work.Spaces.Iθ := by
  filter_upwards [h] with s hs
  have hpt : (fun θ => Work.Spaces.K θ * (-b s θ) / s)
      = fun θ => - (Work.Spaces.K θ * b s θ / s) := by
    funext θ
    ring
  rw [hpt]
  exact hs.neg

/-- The density of the negative field is integrable. -/
theorem integrableOn_L12dens_neg {b : Fn} {z : ℝ}
    (h : MeasureTheory.IntegrableOn (Work.Construction.L12dens b) (Set.Ioi z)) :
    MeasureTheory.IntegrableOn (Work.Construction.L12dens (fun z θ => -b z θ))
      (Set.Ioi z) :=
  (L12dens_neg b).symm ▸ h.neg

/-- The addition form of the a.e. additivity. -/
theorem L12_add_eq {a b : Fn} {z : ℝ} (hz : 0 ≤ z)
    (h1 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * a s θ / s) Work.Spaces.Iθ)
    (h2 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * b s θ / s) Work.Spaces.Iθ)
    (h3 : MeasureTheory.IntegrableOn (Work.Construction.L12dens a) (Set.Ioi z))
    (h4 : MeasureTheory.IntegrableOn (Work.Construction.L12dens b) (Set.Ioi z)) :
    Work.Construction.L12 (fun z θ => a z θ + b z θ) z
      = Work.Construction.L12 a z + Work.Construction.L12 b z := by
  have hsl_neg := slices_neg (z := z) h2
  have hden_neg : MeasureTheory.IntegrableOn
      (Work.Construction.L12dens (fun z θ => -b z θ)) (Set.Ioi z) :=
    integrableOn_L12dens_neg h4
  have hmain := L12_ae_sub h1 hsl_neg (integrableOn_L12dens_sub h1 hsl_neg h3 hden_neg) hden_neg
  have hneg : Work.Construction.L12 (fun z θ => -b z θ) z
      = - Work.Construction.L12 b z := by
    have h1' : (fun z θ => -b z θ) = fun z θ => (-1 : ℝ) * b z θ := by
      funext z θ
      ring
    rw [h1', L12_const_mul]
    ring
  have hbridge : Work.Construction.L12 (fun z θ => a z θ + b z θ) z
      = Work.Construction.L12 (fun z θ => a z θ - (-b z θ)) z :=
    L12_congrQd hz (fun z θ _ _ _ => by ring)
  rw [hbridge, hmain, hneg]
  ring

/-- **`L₁₂` on an alternating four-term sum of fields**: all that the polarization of the
difference row needs. -/
theorem L12_alt4 {A1 A2 A3 A4 : Fn} {z : ℝ} (hz : 0 ≤ z)
    (hs1 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * A1 s θ / s) Work.Spaces.Iθ)
    (hs2 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * A2 s θ / s) Work.Spaces.Iθ)
    (hs3 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * A3 s θ / s) Work.Spaces.Iθ)
    (hs4 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * A4 s θ / s) Work.Spaces.Iθ)
    (hd1 : MeasureTheory.IntegrableOn (Work.Construction.L12dens A1) (Set.Ioi z))
    (hd2 : MeasureTheory.IntegrableOn (Work.Construction.L12dens A2) (Set.Ioi z))
    (hd3 : MeasureTheory.IntegrableOn (Work.Construction.L12dens A3) (Set.Ioi z))
    (hd4 : MeasureTheory.IntegrableOn (Work.Construction.L12dens A4) (Set.Ioi z)) :
    Work.Construction.L12 (fun z θ => A1 z θ - A2 z θ + A3 z θ - A4 z θ) z
      = Work.Construction.L12 A1 z - Work.Construction.L12 A2 z
        + Work.Construction.L12 A3 z - Work.Construction.L12 A4 z := by
  have hsub12 : Work.Construction.L12 A1 z - Work.Construction.L12 A2 z
      = Work.Construction.L12 (fun z θ => A1 z θ - A2 z θ) z := L12_sub_eq hs1 hs2 hd1 hd2
  have hsub34 : Work.Construction.L12 A3 z - Work.Construction.L12 A4 z
      = Work.Construction.L12 (fun z θ => A3 z θ - A4 z θ) z := L12_sub_eq hs3 hs4 hd3 hd4
  have hden12 : MeasureTheory.IntegrableOn
      (Work.Construction.L12dens (fun z θ => A1 z θ - A2 z θ)) (Set.Ioi z) :=
    integrableOn_L12dens_sub hs1 hs2 hd1 hd2
  have hden34 : MeasureTheory.IntegrableOn
      (Work.Construction.L12dens (fun z θ => A3 z θ - A4 z θ)) (Set.Ioi z) :=
    integrableOn_L12dens_sub hs3 hs4 hd3 hd4
  have hsl12 := slices_sub hs1 hs2
  have hsl34 := slices_sub hs3 hs4
  have hadd := L12_add_eq hz hsl12 hsl34 hden12 hden34
  have hbridge : Work.Construction.L12 (fun z θ => A1 z θ - A2 z θ + A3 z θ - A4 z θ) z
      = Work.Construction.L12
          (fun z θ => (fun z θ => A1 z θ - A2 z θ) z θ
            + (fun z θ => A3 z θ - A4 z θ) z θ) z :=
    L12_congrQd hz (fun z θ _ _ _ => by ring)
  rw [hbridge, hadd, ← hsub12, ← hsub34]
  ring

end Work.FTS_MuLipC.RowN
