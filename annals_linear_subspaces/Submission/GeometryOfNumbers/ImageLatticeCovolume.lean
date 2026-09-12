import Mathlib
import ChallengeDeps
import Submission.GeometryOfNumbers.FlowLatticeCovolume

/-!
# Covolume of general linear-image lattices (the full flow `a_t ∘ s_x`)

For `ℝᵈ = EuclideanSpace ℝ (Fin d)` with standard orthonormal basis `(B d)`, and any
`ℝ`-linear automorphism `g` of `ℝᵈ`, the image lattice

`Λ_g = g(ℤᵈ) = span ℤ (range (fun i => g ((B d) i)))`

has covolume `|LinearMap.det g|` (`covol_imageSpan`).  This generalises the two-scale flow
computation of `FlowLatticeCovolume` (`covol_flowSpan`), which is the special case
`g = scaleMap (twoScale a b ℓ)`: there the determinant is `a^ℓ·b^(d−ℓ)`.

The paper's Section-3 lattice is `a_t ∘ s_x` applied to `ℤᵈ`, where `a_t` is the exponential
two-scale flow and `s_x ∈ SL_d(ℝ)` is the representative of `x = P s_x`.  Since the
determinant is multiplicative (`LinearMap.det_comp`), for a **unimodular** `s_x`
(`LinearMap.det s_x = 1`) and the exponential flow (determinant `1`) the lattice
`a_t s_x ℤᵈ` has covolume `1` — it is *unimodular*, exactly the "∆ is unimodular, so
`Σ log λᵢ = 0`" hypothesis of Proposition 4 of the paper.
-/

noncomputable section

open LinearSubspaces
open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.FlowLattice
open MeasureTheory MeasureTheory.Measure Set Module
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Submission.ImageLattice

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- The image of the standard orthonormal basis of `ℝᵈ` under the linear automorphism `g`,
as an `ℝ`-basis of `ℝᵈ`. -/
abbrev imageBasis (g : RD d ≃ₗ[ℝ] RD d) : Basis (Fin d) ℝ (RD d) :=
  (B d).toBasis.map g

/-- The image lattice `g(ℤᵈ)`, presented as the ℤ-span of the image basis. -/
@[reducible] noncomputable def imageSpan (g : RD d ≃ₗ[ℝ] RD d) : Submodule ℤ (RD d) :=
  Submodule.span ℤ (Set.range ⇑(imageBasis (d := d) g))

/-- **Covolume of a linear-image lattice**: `ZLattice.covolume (g(ℤᵈ)) = |LinearMap.det g|`
for any linear automorphism `g` of `ℝᵈ`. -/
lemma covol_imageSpan (g : RD d ≃ₗ[ℝ] RD d) :
    ZLattice.covolume (imageSpan (d := d) g) =
      |LinearMap.det (g : RD d →ₗ[ℝ] RD d)| := by
  classical
  let b₁ : Basis (Fin d) ℝ (RD d) := imageBasis (d := d) g
  let b₀ : Basis (Fin d) ℝ (RD d) := stdBasis d
  have hL : imageSpan (d := d) g = Submodule.span ℤ (Set.range ⇑b₁) := by
    simp [imageSpan, b₁]
  have hF : IsAddFundamentalDomain (imageSpan (d := d) g) (ZSpan.fundamentalDomain b₁) volume := by
    rw [hL]
    exact ZSpan.isAddFundamentalDomain b₁ volume
  have hcov : ZLattice.covolume (imageSpan (d := d) g) =
      volume.real (ZSpan.fundamentalDomain b₁) := by
    exact ZLattice.covolume_eq_measure_fundamentalDomain (imageSpan (d := d) g) volume hF
  rw [hcov]
  have hvol : volume.real (ZSpan.fundamentalDomain b₁) =
      |b₀.det ⇑b₁| * volume.real (ZSpan.fundamentalDomain b₀) := by
    simpa using (ZSpan.measureReal_fundamentalDomain (b := b₁) (μ := volume) (b₀ := b₀))
  rw [hvol]
  have hvol0 : volume.real (ZSpan.fundamentalDomain b₀) = 1 := by
    simpa [b₀] using measureReal_fundamentalDomain_std d
  rw [hvol0]
  have hb₁ : ⇑b₁ = (g : RD d →ₗ[ℝ] RD d) ∘ ⇑b₀ := by
    funext i
    rfl
  rw [hb₁]
  rw [Module.Basis.det_comp]
  rw [Module.Basis.det_self]
  simp

/-- Determinant of a `trans` composition of linear automorphisms, as a plain `LinearMap.det`
statement on the coercions: `(e₁.trans e₂)` applies `e₁` then `e₂`, so as linear maps it is
`e₂ ∘ₗ e₁`. -/
lemma det_linearMap_trans (g₁ g₂ : RD d ≃ₗ[ℝ] RD d) :
    LinearMap.det ((g₁.trans g₂ : RD d ≃ₗ[ℝ] RD d) : RD d →ₗ[ℝ] RD d) =
      LinearMap.det (g₂ : RD d →ₗ[ℝ] RD d) * LinearMap.det (g₁ : RD d →ₗ[ℝ] RD d) := by
  have h : ((g₁.trans g₂ : RD d ≃ₗ[ℝ] RD d) : RD d →ₗ[ℝ] RD d) =
      (g₂ : RD d →ₗ[ℝ] RD d) ∘ₗ (g₁ : RD d →ₗ[ℝ] RD d) := by
    ext x
    rfl
  rw [h]
  exact LinearMap.det_comp (g₂ : RD d →ₗ[ℝ] RD d) (g₁ : RD d →ₗ[ℝ] RD d)

/-- The covolume of the image lattice of a `trans` composition is the product of the absolute
values of the two determinants. -/
lemma covol_imageSpan_trans (g₁ g₂ : RD d ≃ₗ[ℝ] RD d) :
    ZLattice.covolume (imageSpan (d := d) (g₁.trans g₂)) =
      |LinearMap.det (g₂ : RD d →ₗ[ℝ] RD d)| *
        |LinearMap.det (g₁ : RD d →ₗ[ℝ] RD d)| := by
  rw [covol_imageSpan (g₁.trans g₂)]
  rw [det_linearMap_trans g₁ g₂]
  exact abs_mul _ _

/-- The full Section-3 flow lattice `(a_t ∘ s_x)(ℤᵈ)` for the two-scale flow `a,b` and an
arbitrary linear automorphism `sx` of `ℝᵈ` (representative of the point `x`). -/
abbrev flowSpan_sx (a b : ℝ) (ℓ : ℕ) (ha : a ≠ 0) (hb : b ≠ 0)
    (sx : RD d ≃ₗ[ℝ] RD d) : Submodule ℤ (RD d) :=
  imageSpan (d := d) (sx.trans (scaleMapEquiv (d := d) a b ℓ ha hb))

/-- **Covolume of the full flow lattice**: `ZLattice.covolume ((a_t ∘ s_x)(ℤᵈ)) =
|a^ℓ · b^(d−ℓ) · det s_x|`. -/
lemma covol_flowSpan_sx (a b : ℝ) (ℓ : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hℓd : ℓ ≤ d)
    (sx : RD d ≃ₗ[ℝ] RD d) :
    ZLattice.covolume (flowSpan_sx (d := d) a b ℓ ha hb sx) =
      |a ^ ℓ * b ^ (d - ℓ)| * |LinearMap.det (sx : RD d →ₗ[ℝ] RD d)| := by
  unfold flowSpan_sx
  rw [covol_imageSpan_trans sx (scaleMapEquiv (d := d) a b ℓ ha hb)]
  have hdet : LinearMap.det (scaleMapEquiv (d := d) a b ℓ ha hb : RD d →ₗ[ℝ] RD d) =
      a ^ ℓ * b ^ (d - ℓ) := by
    change LinearMap.det (scaleMap (twoScale a b ℓ) : RD d →ₗ[ℝ] RD d) = a ^ ℓ * b ^ (d - ℓ)
    exact det_scaleMap_twoScale a b ℓ hℓd
  rw [hdet]

/-- **The exponential full flow lattice is unimodular when `s_x` is**: for the exponential
two-scale flow `a = exp(-t/ℓ)`, `b = exp(t/(d−ℓ))` and a **unimodular** `s_x`
(`LinearMap.det s_x = 1`), the Section-3 lattice `a_t s_x ℤᵈ` has covolume `1`. -/
lemma covol_flowSpan_sx_exp {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (t : ℝ)
    (sx : RD d ≃ₗ[ℝ] RD d) (hsxdet : LinearMap.det (sx : RD d →ₗ[ℝ] RD d) = 1) :
    ZLattice.covolume (flowSpan_sx (d := d) (Real.exp (-t / (ℓ : ℝ)))
      (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ
        (ne_of_gt (Real.exp_pos _)) (ne_of_gt (Real.exp_pos _)) sx) = 1 := by
  have ha0 : Real.exp (-t / (ℓ : ℝ)) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hb0 : Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) ≠ 0 := ne_of_gt (Real.exp_pos _)
  rw [covol_flowSpan_sx (d := d) (a := Real.exp (-t / (ℓ : ℝ)))
    (b := Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ ha0 hb0 (le_of_lt hℓd) sx]
  have h1 : (Real.exp (-t / (ℓ : ℝ))) ^ ℓ *
      (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ^ (d - ℓ) = 1 := by
    rw [exp_pow_neg_div ℓ hℓ0 t, exp_pow_div_sub hℓd t]
    rw [← Real.exp_add]
    ring_nf
    simp
  rw [h1, hsxdet]
  simp
/-- The image lattice is the image of the integer lattice: `g(ℤᵈ) = map (g) ℤᵈ`. -/
lemma imageSpan_eq_map (g : RD d ≃ₗ[ℝ] RD d) :
    imageSpan (d := d) g = Submodule.map ((g : RD d →ₗ[ℝ] RD d).restrictScalars ℤ)
      (intPoints (d := d)) := by
  classical
  unfold imageSpan imageBasis
  have hint : intPoints (d := d) = Submodule.span ℤ (Set.range (fun i : Fin d => ((B d) i : RD d))) := by
    dsimp [intPoints]
  rw [hint]
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨(B d) i, ⟨i, rfl⟩, ?_⟩
    simp
  · rintro ⟨y, ⟨i, hy⟩, rfl⟩
    subst y
    refine ⟨i, rfl⟩

/-- Each image basis vector lies in the image lattice. -/
lemma imageBasis_mem_imageSpan (g : RD d ≃ₗ[ℝ] RD d) (i : Fin d) :
    (imageBasis (d := d) g i : RD d) ∈ imageSpan (d := d) g := by
  dsimp [imageSpan]
  exact Submodule.subset_span ⟨i, rfl⟩

/-- The preimage of an image-lattice vector under the automorphism is an integer point:
`y ∈ g(ℤᵈ)` gives `g⁻¹ y ∈ ℤᵈ`. -/
lemma preimage_mem_intPoints_of_mem_imageSpan (g : RD d ≃ₗ[ℝ] RD d)
    {y : RD d} (hy : y ∈ imageSpan (d := d) g) :
    (g.symm : RD d →ₗ[ℝ] RD d) y ∈ intPoints (d := d) := by
  classical
  rw [imageSpan_eq_map (d := d) g] at hy
  rcases (Submodule.mem_map).mp hy with ⟨n, hn, hny⟩
  have hpre : (g.symm : RD d →ₗ[ℝ] RD d) y = n := by
    rw [← hny]
    simp [g.symm_apply_apply n]
  rwa [hpre]

/-- The sheared basis is `ℤ`-independent (the automorphism `g` maps the independent
standard basis to an independent family). -/
lemma linearIndependent_imageBasis (g : RD d ≃ₗ[ℝ] RD d) :
    LinearIndependent ℤ (fun i : Fin d => ((imageBasis (d := d) g i) : RD d)) := by
  dsimp [imageBasis]
  have hstd : LinearIndependent ℤ (fun i : Fin d => ((B d) i : RD d)) :=
    Submission.FlowLattice.linearIndependent_std_basis (d := d)
  have hker : LinearMap.ker ((g : RD d →ₗ[ℝ] RD d).restrictScalars ℤ) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    simpa using g.injective
  exact LinearIndependent.map' hstd ((g : RD d →ₗ[ℝ] RD d).restrictScalars ℤ) hker

/-- The full Section-3 lattice `(a_t ∘ s_x)(ℤᵈ)`: the sheared-flowed standard basis
vectors are elements. -/
lemma flowSpan_sx_mem_std (a b : ℝ) (ℓ : ℕ) (ha : a ≠ 0) (hb : b ≠ 0)
    (sx : RD d ≃ₗ[ℝ] RD d) (i : Fin d) :
    (scaleMap (twoScale a b ℓ)) (sx ((B d) i)) ∈
      Submission.ImageLattice.flowSpan_sx (d := d) a b ℓ ha hb sx := by
  classical
  let T : RD d ≃ₗ[ℝ] RD d := sx.trans (Submission.FlowLattice.scaleMapEquiv (d := d) a b ℓ ha hb)
  have hgen : (scaleMap (twoScale a b ℓ)) (sx ((B d) i)) = (imageBasis (d := d) T i : RD d) := by
    dsimp [imageBasis, T]
    rfl
  rw [hgen]
  dsimp [Submission.ImageLattice.flowSpan_sx, imageSpan]
  exact Submodule.subset_span ⟨i, rfl⟩

end Submission.ImageLattice
