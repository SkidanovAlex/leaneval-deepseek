import Mathlib
import Submission.Work.ThomBordism.ambientLocalDefs
import Submission.Work.PTGeometric.HOFDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 4000000

open CategoryTheory CategoryTheory.Limits

namespace Work.ThomBordism

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-!
# A positive fibrewise radial rescaling induces the identity on the relative homology of
`(ν, ν∖0)`

The rescaling `radialRescale E φ` (with `φ > 0`) is homotopic to the identity, through the
fibrewise radial homotopy whose coefficient at time `t` is the convex combination
`(1 - t)·φ ‖p‖ + t`.  The coefficient is positive for every `t ∈ [0,1]`, so the homotopy preserves
`ν ∖ 0`, and homotopy invariance of the induced map on relative homology
(`Work.PTGeometric.HOF.relChainsMapOf_homologyMap_eq_of_homotopic`) gives the result.
-/

/-- The interpolation coefficient `(1 - t)·φ(‖p‖) + t` of the fibrewise radial homotopy. -/
def radialCoeff (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (φ : ℝ → ℝ)
    (p : unitInterval × Work.Tubular.NormalTotal E) : ℝ :=
  ((1 : ℝ) - (p.1 : ℝ)) * φ (Work.Tubular.normalNorm E p.2) + (p.1 : ℝ)

theorem continuous_radialCoeff (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (φ : ℝ → ℝ) (hφc : Continuous φ) : Continuous (radialCoeff E φ) := by
  have h1 : Continuous fun p : unitInterval × Work.Tubular.NormalTotal E => (p.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have h2 : Continuous fun p : unitInterval × Work.Tubular.NormalTotal E =>
      φ (Work.Tubular.normalNorm E p.2) :=
    hφc.comp ((Work.Tubular.continuous_normalNorm E).comp continuous_snd)
  exact ((continuous_const.sub h1).mul h2).add h1

/-- **The fibrewise radial homotopy**: it interpolates linearly, along each fibre, between the
coefficient `φ ‖p‖` (at `t = 0`) and the coefficient `1` (at `t = 1`). -/
def radialRescaleHomotopyFun (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (φ : ℝ → ℝ) :
    unitInterval × Work.Tubular.NormalTotal E → Work.Tubular.NormalTotal E :=
  fun p => ⟨(p.2.1.1, radialCoeff E φ p • p.2.1.2),
    Submodule.smul_mem (Work.Tubular.normalSpace E p.2.1.1) _ p.2.2⟩

@[simp] theorem radialRescaleHomotopyFun_apply
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (φ : ℝ → ℝ)
    (t : unitInterval) (p : Work.Tubular.NormalTotal E) :
    radialRescaleHomotopyFun E φ (t, p)
      = ⟨(p.1.1, radialCoeff E φ (t, p) • p.1.2),
          Submodule.smul_mem (Work.Tubular.normalSpace E p.1.1) _ p.2⟩ := rfl

theorem continuous_radialRescaleHomotopyFun
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (φ : ℝ → ℝ) (hφc : Continuous φ) : Continuous (radialRescaleHomotopyFun E φ) := by
  unfold radialRescaleHomotopyFun
  refine Continuous.subtype_mk (((Work.Tubular.NormalTotal.continuous_proj E).comp
    continuous_snd).prodMk ((continuous_radialCoeff E φ hφc).smul
      ((Work.Tubular.NormalTotal.continuous_vec E).comp continuous_snd))) ?_

/-- The radial homotopy, as a continuous map. -/
def radialRescaleHomotopy (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (φ : ℝ → ℝ) (hφc : Continuous φ) :
    C(unitInterval × Work.Tubular.NormalTotal E, Work.Tubular.NormalTotal E) :=
  ⟨radialRescaleHomotopyFun E φ, continuous_radialRescaleHomotopyFun E φ hφc⟩

@[simp] theorem radialRescaleHomotopy_apply
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (φ : ℝ → ℝ) (hφc : Continuous φ) (t : unitInterval) (p : Work.Tubular.NormalTotal E) :
    radialRescaleHomotopy E φ hφc (t, p) = radialRescaleHomotopyFun E φ (t, p) := rfl

/-- At time `0` the radial homotopy is the rescaling `radialRescale E φ`. -/
theorem radialRescaleHomotopyFun_zero
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (φ : ℝ → ℝ) (p : Work.Tubular.NormalTotal E) :
    radialRescaleHomotopyFun E φ ((0 : unitInterval), p) = radialRescale E φ p := by
  obtain ⟨⟨x, w⟩, hw⟩ := p
  have h0 : ((0 : unitInterval) : ℝ) = 0 := rfl
  apply Subtype.ext
  simp only [radialRescaleHomotopyFun_apply, radialRescale, radialCoeff, Prod.mk.injEq,
    true_and, h0, sub_zero, one_mul, add_zero]

/-- At time `1` the radial homotopy is the identity. -/
theorem radialRescaleHomotopyFun_one
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (φ : ℝ → ℝ) (p : Work.Tubular.NormalTotal E) :
    radialRescaleHomotopyFun E φ ((1 : unitInterval), p) = p := by
  obtain ⟨⟨x, w⟩, hw⟩ := p
  have h1 : ((1 : unitInterval) : ℝ) = 1 := rfl
  apply Subtype.ext
  simp only [radialRescaleHomotopyFun_apply, radialCoeff, Prod.mk.injEq, true_and, h1, sub_self,
    zero_mul, zero_add, one_smul]

/-- The interpolation coefficient is positive at every time, provided `φ > 0` on `[0,∞)`. -/
theorem radialCoeff_pos (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (φ : ℝ → ℝ) (hφpos : ∀ r, 0 ≤ r → 0 < φ r) (p : Work.Tubular.NormalTotal E)
    (hp : 0 < Work.Tubular.normalNorm E p) (t : unitInterval) :
    0 < radialCoeff E φ (t, p) := by
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := unitInterval.nonneg t
  have ht1 : (t : ℝ) ≤ 1 := unitInterval.le_one t
  have hφ : 0 < φ (Work.Tubular.normalNorm E p) := hφpos _ (le_of_lt hp)
  rcases lt_or_eq_of_le ht1 with h | h
  · have h1 : 0 < 1 - (t : ℝ) := by linarith
    have h2 : 0 < (1 - (t : ℝ)) * φ (Work.Tubular.normalNorm E p) := mul_pos h1 hφ
    rw [radialCoeff]
    linarith
  · have hc : radialCoeff E φ (t, p) = 1 := by
      rw [radialCoeff, h]
      ring
    rw [hc]
    norm_num

/-- The norm of the radial homotopy. -/
theorem normalNorm_radialRescaleHomotopyFun
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (φ : ℝ → ℝ) (t : unitInterval) (p : Work.Tubular.NormalTotal E) :
    Work.Tubular.normalNorm E (radialRescaleHomotopyFun E φ (t, p))
      = |radialCoeff E φ (t, p)| * Work.Tubular.normalNorm E p := by
  rw [Work.Tubular.normalNorm, Work.Tubular.normalNorm, radialRescaleHomotopyFun_apply]
  rw [norm_smul, Real.norm_eq_abs]

/-- The radial homotopy preserves the punctured total space `ν ∖ 0`. -/
theorem radialRescaleHomotopyFun_mem_normalNonzero
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (φ : ℝ → ℝ)
    (hφpos : ∀ r, 0 ≤ r → 0 < φ r) {t : unitInterval} {p : Work.Tubular.NormalTotal E}
    (hp : p ∈ Work.Tubular.normalNonzero E) :
    radialRescaleHomotopyFun E φ (t, p) ∈ Work.Tubular.normalNonzero E := by
  rw [Work.Tubular.mem_normalNonzero] at hp ⊢
  have hp' : 0 < Work.Tubular.normalNorm E p :=
    lt_of_le_of_ne (Work.Tubular.normalNorm_nonneg E p) (Ne.symm hp)
  have hc : 0 < radialCoeff E φ (t, p) := radialCoeff_pos E φ hφpos p hp' t
  rw [normalNorm_radialRescaleHomotopyFun]
  exact mul_ne_zero (abs_ne_zero.mpr (ne_of_gt hc)) hp

/-- **The positive fibrewise radial rescaling is homotopic to the identity**, through rescalings
which preserve `ν ∖ 0` at every time. -/
def radialRescaleHomotopyTop (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (φ : ℝ → ℝ) (hφc : Continuous φ) (hcont : Continuous (radialRescale E φ)) :
    TopCat.Homotopy (TopCat.ofHom ⟨radialRescale E φ, hcont⟩)
      (𝟙 (TopCat.of (Work.Tubular.NormalTotal E))) where
  toContinuousMap := radialRescaleHomotopy E φ hφc
  map_zero_left := fun p => by
    show radialRescaleHomotopy E φ hφc (0, p)
      = (TopCat.Hom.hom (TopCat.ofHom ⟨radialRescale E φ, hcont⟩)) p
    rw [radialRescaleHomotopy_apply, radialRescaleHomotopyFun_zero]
    rfl
  map_one_left := fun p => by
    show radialRescaleHomotopy E φ hφc (1, p)
      = (TopCat.Hom.hom (𝟙 (TopCat.of (Work.Tubular.NormalTotal E)))) p
    rw [radialRescaleHomotopy_apply, radialRescaleHomotopyFun_one]
    rfl

theorem radialRescale_homologyMap_id {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (φ : ℝ → ℝ) (hφc : Continuous φ) (hφpos : ∀ r, 0 ≤ r → 0 < φ r)
    (hcont : Continuous (Work.ThomBordism.radialRescale E φ)) (n : ℕ)
    (z : (Work.Cohomology.relChains (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E)).homology n) :
    (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMapOf
        (TopCat.of (Work.Tubular.NormalTotal E)) (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) (Work.Tubular.normalNonzero E)
        (TopCat.ofHom ⟨Work.ThomBordism.radialRescale E φ, hcont⟩)
        (TopCat.ofHom ⟨fun p => ⟨Work.ThomBordism.radialRescale E φ p.1,
            Work.ThomBordism.radialRescale_mem_normalNonzero E φ hφpos p.2⟩,
          Continuous.subtype_mk (hcont.comp continuous_subtype_val) _⟩)
        (by apply TopCat.ext; intro a; rfl)) n).hom z = z := by
  have hmain : HomologicalComplex.homologyMap (Work.Cohomology.relChainsMapOf
        (TopCat.of (Work.Tubular.NormalTotal E)) (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) (Work.Tubular.normalNonzero E)
        (TopCat.ofHom ⟨Work.ThomBordism.radialRescale E φ, hcont⟩)
        (TopCat.ofHom ⟨fun p => ⟨Work.ThomBordism.radialRescale E φ p.1,
            Work.ThomBordism.radialRescale_mem_normalNonzero E φ hφpos p.2⟩,
          Continuous.subtype_mk (hcont.comp continuous_subtype_val) _⟩)
        (by apply TopCat.ext; intro a; rfl)) n
      = HomologicalComplex.homologyMap (Work.Cohomology.relChainsMapOf
        (TopCat.of (Work.Tubular.NormalTotal E)) (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) (Work.Tubular.normalNonzero E)
        (𝟙 (TopCat.of (Work.Tubular.NormalTotal E)))
        (𝟙 (TopCat.of (Work.Tubular.normalNonzero E)))
        (by rw [Category.id_comp, Category.comp_id])) n := by
    refine Work.PTGeometric.HOF.relChainsMapOf_homologyMap_eq_of_homotopic
      (X := TopCat.of (Work.Tubular.NormalTotal E))
      (Y := TopCat.of (Work.Tubular.NormalTotal E))
      (A := Work.Tubular.normalNonzero E) (B := Work.Tubular.normalNonzero E)
      (f₀ := TopCat.ofHom ⟨Work.ThomBordism.radialRescale E φ, hcont⟩)
      (f₁ := 𝟙 (TopCat.of (Work.Tubular.NormalTotal E)))
      (g₀ := TopCat.ofHom ⟨fun p => ⟨Work.ThomBordism.radialRescale E φ p.1,
          Work.ThomBordism.radialRescale_mem_normalNonzero E φ hφpos p.2⟩,
        Continuous.subtype_mk (hcont.comp continuous_subtype_val) _⟩)
      (g₁ := 𝟙 (TopCat.of (Work.Tubular.normalNonzero E))) ?_ ?_
      (radialRescaleHomotopyTop E φ hφc hcont)
      (fun t x hx => radialRescaleHomotopyFun_mem_normalNonzero E φ hφpos hx) n
  have hid : HomologicalComplex.homologyMap (Work.Cohomology.relChainsMapOf
        (TopCat.of (Work.Tubular.NormalTotal E)) (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) (Work.Tubular.normalNonzero E)
        (𝟙 (TopCat.of (Work.Tubular.NormalTotal E)))
        (𝟙 (TopCat.of (Work.Tubular.normalNonzero E)))
        (by rw [Category.id_comp, Category.comp_id])) n
      = 𝟙 ((Work.Cohomology.relChains (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E)).homology n) := by
    have hchain : Work.Cohomology.relChainsMapOf
        (TopCat.of (Work.Tubular.NormalTotal E)) (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) (Work.Tubular.normalNonzero E)
        (𝟙 (TopCat.of (Work.Tubular.NormalTotal E)))
        (𝟙 (TopCat.of (Work.Tubular.normalNonzero E)))
        (by rw [Category.id_comp, Category.comp_id])
        = 𝟙 (Work.Cohomology.relChains (TopCat.of (Work.Tubular.NormalTotal E))
            (Work.Tubular.normalNonzero E)) := by
      unfold Work.Cohomology.relChainsMapOf Work.Cohomology.relChains
      simp only [Work.Cohomology.chainMap, CategoryTheory.Functor.map_id]
      exact Limits.cokernel.map_id _ _ _
    rw [hchain, HomologicalComplex.homologyMap_id]
  rw [hmain, hid]
  simp

end

end Work.ThomBordism
