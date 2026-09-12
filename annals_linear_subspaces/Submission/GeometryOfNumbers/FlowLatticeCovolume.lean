import Mathlib
import ChallengeDeps
import Submission.GeometryOfNumbers.FlowLattice
import Submission.GeometryOfNumbers.DiagonalFlow
import Submission.Commons.Lattice.Minkowski.covolume_eq_of_eq

/-!
# Covolume of the two-scale flow lattice (Milestone C, part 2)

For the two-scale diagonal map `f = scaleMap (twoScale a b ℓ)` on `ℝᵈ`, the flow lattice
`Λ = f(ℤᵈ)` (also `flowLattice a b ℓ` = the ℤ-span of the flowed standard basis) is a full-rank
lattice in `ℝᵈ`.  We compute its covolume:

* `covol_flowSpan`: for the span presentation `Λ₀ = span ℤ (range (flowed basis))`,
  `ZLattice.covolume Λ₀ = |a^ℓ · b^(d−ℓ)|` (the absolute value of the determinant of the flow);
* `covol_flowSpan_exp`: for the exponential flow `a = exp(-t/ℓ)`, `b = exp(t/(d−ℓ))` (which has
  determinant `a^ℓ b^(d−ℓ) = 1`), the covolume is `1` — the "unimodular" flow lattice of
  Section 3 of the paper.

The computation reduces to the measure of the fundamental domain of an orthonormal basis of
`ℝᵈ` (`volume.real (ZSpan.fundamentalDomain (B d).toBasis) = 1`) and the determinant of the
flow in the standard basis (`LinearMap.det (scaleMap s) = ∏ s`, i.e. the diagonal determinant).
-/

noncomputable section

open LinearSubspaces
open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open MeasureTheory MeasureTheory.Measure Set Module
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Submission.FlowLattice

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- The standard orthonormal basis of `ℝᵈ`, as an `ℝ`-basis. -/
abbrev stdBasis (d : ℕ) : Basis (Fin d) ℝ (RD d) := (B d).toBasis

/-- The half-open fundamental domain of the standard lattice `ℤᵈ` (the unit cube in the
orthonormal basis of `ℝᵈ`) has volume `1`. -/
lemma measureReal_fundamentalDomain_std (d : ℕ) :
    volume.real (ZSpan.fundamentalDomain (stdBasis d)) = 1 := by
  have hcongr := ZSpan.fundamentalDomain_ae_parallelepiped (stdBasis d) (volume : Measure (RD d))
  have hreal : volume.real (ZSpan.fundamentalDomain (stdBasis d)) =
      volume.real (parallelepiped (stdBasis d)) := by
    exact measureReal_congr hcongr
  rw [hreal]
  have hp : volume (parallelepiped (stdBasis d)) = 1 := by
    simpa [stdBasis] using (B d).volume_parallelepiped
  rw [show volume.real (parallelepiped (stdBasis d)) =
      (volume (parallelepiped (stdBasis d))).toReal by rfl]
  rw [hp]
  simp

/-- The standard lattice `ℤᵈ = span ℤ (range (B d))` in `ℝᵈ` has covolume `1`. -/
lemma covol_intPoints (d : ℕ) : ZLattice.covolume (intPoints (d := d)) = 1 := by
  have hF : IsAddFundamentalDomain (intPoints (d := d))
      (ZSpan.fundamentalDomain (stdBasis d)) volume := by
    dsimp [intPoints]
    exact ZSpan.isAddFundamentalDomain (stdBasis d) volume
  have hcov : ZLattice.covolume (intPoints (d := d)) =
      volume.real (ZSpan.fundamentalDomain (stdBasis d)) := by
    exact ZLattice.covolume_eq_measure_fundamentalDomain (intPoints (d := d)) volume hF
  rw [hcov]
  exact measureReal_fundamentalDomain_std d

/-- The determinant of the coordinatewise diagonal linear map `scaleMap s` is the product of
the diagonal entries. -/
lemma det_scaleMap (s : Fin d → ℝ) :
    LinearMap.det (scaleMap s : RD d →ₗ[ℝ] RD d) = ∏ i, s i := by
  let b : Basis (Fin d) ℝ (RD d) := stdBasis d
  rw [← LinearMap.det_toMatrix b (scaleMap s)]
  have hmat : LinearMap.toMatrix b b (scaleMap s) = Matrix.diagonal s := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.diagonal_apply]
    have hsbj : scaleMap s (b j) = s j • (b j : RD d) := by
      change scaleMap s ((B d) j) = s j • ((B d) j : RD d)
      exact scaleMap_basis s j
    rw [hsbj]
    rw [map_smul]
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  rw [hmat]
  rw [Matrix.det_diagonal]

/-- The number of standard-basis indices `i` with `ℓ ≤ i.val` is `d − ℓ` (for `ℓ ≤ d`). -/
lemma card_filter_val_ge {d ℓ : ℕ} (hℓd : ℓ ≤ d) :
    ((Finset.univ : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card = d - ℓ := by
  classical
  have hb : ((Finset.univ : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card =
      (Finset.range (d - ℓ)).card := by
    refine Finset.card_bij (s := (Finset.univ : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val))
      (t := Finset.range (d - ℓ)) (fun i hi => i.val - ℓ) ?hi ?inj ?surj
    · intro i hi
      simp
      have h : ℓ ≤ i.val := by simpa using hi
      have hi2 : i.val < d := i.isLt
      omega
    · intro a ha b hb h
      apply Fin.ext
      have ha' : ℓ ≤ a.val := by simpa using ha
      have hb' : ℓ ≤ b.val := by simpa using hb
      omega
    · intro m hm
      simp at hm
      refine ⟨⟨ℓ + m, ?_⟩, ?_, ?_⟩
      · omega
      · simp
      · simp
  simpa using hb

/-- The number of standard-basis indices `i` with `i.val < ℓ` is `ℓ` (for `ℓ ≤ d`). -/
lemma card_filter_val_lt {d ℓ : ℕ} (hℓd : ℓ ≤ d) :
    ((Finset.univ : Finset (Fin d)).filter (fun i : Fin d => i.val < ℓ)).card = ℓ := by
  classical
  have hb : ((Finset.univ : Finset (Fin d)).filter (fun i : Fin d => i.val < ℓ)).card =
      (Finset.range ℓ).card := by
    refine Finset.card_bij (s := (Finset.univ : Finset (Fin d)).filter (fun i : Fin d => i.val < ℓ))
      (t := Finset.range ℓ) (fun i hi => i.val) ?hi ?inj ?surj
    · intro i hi
      simp
      have h : i.val < ℓ := by simpa using hi
      omega
    · intro a ha b hb h
      apply Fin.ext
      omega
    · intro m hm
      simp at hm
      refine ⟨⟨m, ?_⟩, ?_, ?_⟩
      · omega
      · simpa using hm
      · rfl
  simpa using hb

/-- The product of the two-scale coefficients over all `d` indices: `a` on the `ℓ` contracting
directions and `b` on the `d−ℓ` expanding ones. -/
lemma prod_twoScale_univ {d ℓ : ℕ} (hℓd : ℓ ≤ d) (a b : ℝ) :
    (∏ i : Fin d, twoScale a b ℓ i) = a ^ ℓ * b ^ (d - ℓ) := by
  classical
  have hprod := twoScale_prod (d := d) (a := a) (b := b) (ℓ := ℓ) (I := Finset.univ) (k := d)
    (j := d - ℓ) (by simp) (card_filter_val_ge (d := d) (ℓ := ℓ) hℓd)
  have hcard : d - (d - ℓ) = ℓ := by omega
  rw [hcard] at hprod
  simpa using hprod

/-- The flowed standard basis as an `ℝ`-basis (the image of the standard ON basis under the
invertible two-scale flow). -/
@[reducible] noncomputable def flowBasis (a b : ℝ) (ℓ : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Basis (Fin d) ℝ (RD d) :=
  (B d).toBasis.map (scaleMapEquiv (d := d) a b ℓ ha hb)

/-- The flow lattice, presented as the ℤ-span of the flowed basis (equal to `flowLattice a b ℓ`,
see `flowLattice_eq_span_map`). -/
@[reducible] noncomputable def flowSpan (a b : ℝ) (ℓ : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Submodule ℤ (RD d) :=
  Submodule.span ℤ (Set.range ⇑(flowBasis (d := d) a b ℓ ha hb))

/-- Determinant of the two-scale diagonal flow: `a^ℓ · b^(d−ℓ)`. -/
lemma det_scaleMap_twoScale (a b : ℝ) (ℓ : ℕ) (hℓd : ℓ ≤ d) :
    LinearMap.det (scaleMap (twoScale a b ℓ) : RD d →ₗ[ℝ] RD d) = a ^ ℓ * b ^ (d - ℓ) := by
  rw [det_scaleMap]
  exact prod_twoScale_univ hℓd a b

/-- Covolume of the flow lattice (span presentation): `|a^ℓ · b^(d−ℓ)|`. -/
lemma covol_flowSpan (a b : ℝ) (ℓ : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hℓd : ℓ ≤ d) :
    ZLattice.covolume (flowSpan (d := d) a b ℓ ha hb) = |a ^ ℓ * b ^ (d - ℓ)| := by
  classical
  let b₁ : Basis (Fin d) ℝ (RD d) := flowBasis (d := d) a b ℓ ha hb
  let b₀ : Basis (Fin d) ℝ (RD d) := stdBasis d
  have hL : flowSpan (d := d) a b ℓ ha hb = Submodule.span ℤ (Set.range ⇑b₁) := by
    simp [flowSpan, b₁]
  have hF : IsAddFundamentalDomain (flowSpan (d := d) a b ℓ ha hb)
      (ZSpan.fundamentalDomain b₁) volume := by
    rw [hL]
    exact ZSpan.isAddFundamentalDomain b₁ volume
  have hcov : ZLattice.covolume (flowSpan (d := d) a b ℓ ha hb) =
      volume.real (ZSpan.fundamentalDomain b₁) := by
    exact ZLattice.covolume_eq_measure_fundamentalDomain (flowSpan (d := d) a b ℓ ha hb) volume hF
  rw [hcov]
  have hvol : volume.real (ZSpan.fundamentalDomain b₁) =
      |b₀.det ⇑b₁| * volume.real (ZSpan.fundamentalDomain b₀) := by
    simpa using (ZSpan.measureReal_fundamentalDomain (b := b₁) (μ := volume) (b₀ := b₀))
  rw [hvol]
  have hvol0 : volume.real (ZSpan.fundamentalDomain b₀) = 1 := by
    simpa [b₀] using measureReal_fundamentalDomain_std d
  rw [hvol0]
  have hdetv : b₀.det ⇑b₁ = LinearMap.det (scaleMap (twoScale a b ℓ) : RD d →ₗ[ℝ] RD d) := by
    have hb₁ : ⇑b₁ = (scaleMap (twoScale a b ℓ) : RD d →ₗ[ℝ] RD d) ∘ ⇑b₀ := by
      funext i
      change (scaleMapEquiv (d := d) a b ℓ ha hb) ((B d).toBasis i) =
        (scaleMap (twoScale a b ℓ)) ((B d).toBasis i)
      rfl
    rw [hb₁]
    rw [Module.Basis.det_comp]
    rw [Basis.det_self]
    simp
  rw [hdetv]
  rw [det_scaleMap_twoScale a b ℓ hℓd]
  ring_nf

/-- `exp(-t/ℓ)` to the power `ℓ` is `exp(-t)`. -/
lemma exp_pow_neg_div (ℓ : ℕ) (hℓ0 : 0 < ℓ) (t : ℝ) :
    (Real.exp (-t / (ℓ : ℝ))) ^ ℓ = Real.exp (-t) := by
  rw [← Real.exp_nat_mul]
  congr 1
  field_simp [hℓ0.ne']

/-- `exp(t/(d−ℓ))` to the power `d−ℓ` is `exp(t)` (for `ℓ < d`). -/
lemma exp_pow_div_sub {d ℓ : ℕ} (hℓd : ℓ < d) (t : ℝ) :
    (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ^ (d - ℓ) = Real.exp t := by
  have hd0 : (d : ℝ) - (ℓ : ℝ) ≠ 0 := by
    rw [← Nat.cast_sub (le_of_lt hℓd)]
    exact_mod_cast (Nat.sub_ne_zero_of_lt hℓd)
  rw [← Real.exp_nat_mul]
  congr 1
  have hmain : ((d - ℓ : ℕ) : ℝ) * (t / ((d : ℝ) - (ℓ : ℝ))) = t := by
    rw [Nat.cast_sub (le_of_lt hℓd)]
    field_simp [hd0]
  exact hmain

/-- **Covolume of the exponential flow lattice is `1`**: for the two-scale flow
`a = exp(-t/ℓ)`, `b = exp(t/(d−ℓ))` (determinant `a^ℓ b^(d−ℓ) = 1`), the flow lattice
`a_t(ℤᵈ)` has covolume `1` — the "unimodular" lattice of Section 3 of the paper. -/
lemma covol_flowSpan_exp {d ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (t : ℝ) :
    ZLattice.covolume (flowSpan (d := d) (Real.exp (-t / (ℓ : ℝ)))
      (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ
        (ne_of_gt (Real.exp_pos _)) (ne_of_gt (Real.exp_pos _))) = 1 := by
  have ha0 : Real.exp (-t / (ℓ : ℝ)) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hb0 : Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) ≠ 0 := ne_of_gt (Real.exp_pos _)
  rw [covol_flowSpan (d := d) (a := Real.exp (-t / (ℓ : ℝ)))
    (b := Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ ha0 hb0 (le_of_lt hℓd)]
  have h1 : (Real.exp (-t / (ℓ : ℝ))) ^ ℓ *
      (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ^ (d - ℓ) = 1 := by
    rw [exp_pow_neg_div ℓ hℓ0 t, exp_pow_div_sub hℓd t]
    rw [← Real.exp_add]
    ring_nf
    simp
  rw [h1]
  simp


/-- The span presentation `flowSpan` is the same submodule as the flow lattice `flowLattice`
(for an invertible flow). -/
lemma flowLattice_eq_flowSpan (a b : ℝ) (ℓ : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    flowLattice (d := d) a b ℓ = flowSpan (d := d) a b ℓ ha hb := by
  rw [flowLattice_eq_span_map]

/-- Covolume of the flow lattice `flowLattice a b ℓ` (the map-image presentation): `|a^ℓ·b^(d−ℓ)|`. -/
lemma covol_flowLattice (a b : ℝ) (ℓ : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hℓd : ℓ ≤ d) :
    ZLattice.covolume (flowLattice (d := d) a b ℓ) = |a ^ ℓ * b ^ (d - ℓ)| := by
  haveI : Fact (a ≠ 0) := ⟨ha⟩
  haveI : Fact (b ≠ 0) := ⟨hb⟩
  rw [← covol_flowSpan (d := d) a b ℓ ha hb hℓd]
  exact Commons.Lattice.Minkowski.covolume_eq_of_eq (flowLattice (d := d) a b ℓ)
    (flowSpan (d := d) a b ℓ ha hb) (flowLattice_eq_flowSpan a b ℓ ha hb)

/-- Covolume of the exponential flow lattice is `1` (def presentation of the flow lattice):
`a = exp(-t/ℓ)`, `b = exp(t/(d−ℓ))`. -/
lemma covol_flowLattice_exp {d ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (t : ℝ) :
    ZLattice.covolume (flowLattice (d := d) (Real.exp (-t / (ℓ : ℝ)))
      (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ) = 1 := by
  have ha0 : Real.exp (-t / (ℓ : ℝ)) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hb0 : Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) ≠ 0 := ne_of_gt (Real.exp_pos _)
  haveI : Fact (Real.exp (-t / (ℓ : ℝ)) ≠ 0) := ⟨ha0⟩
  haveI : Fact (Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) ≠ 0) := ⟨hb0⟩
  rw [← covol_flowSpan_exp (d := d) hℓ0 hℓd t]
  exact Commons.Lattice.Minkowski.covolume_eq_of_eq
    (flowLattice (d := d) (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ)
    (flowSpan (d := d) (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ
      ha0 hb0) (flowLattice_eq_flowSpan (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ ha0 hb0)
end Submission.FlowLattice
