import Mathlib
import Submission.Work.HP.MMDefs

/-!
# `coneSliceVol_GamLoc` : the volume of the local cone slice

For the "local" lattice `Γ^{loc}_{x,y}(Q) = Λ^{(Q)}_{ν(x)} ∩ Λ^{(Q)}_{ν(y)}` the region
`span_ℝ(Γ^{loc}) ∩ B_N(1) ∩ 𝒞_{ν(x)}^{(α)} ∩ 𝒞_{ν(y)}^{(α)}` has full dimension: the
congruence lattices `Λ^{(Q)}` are of finite index in `ℤ^N` (they contain `Q·ℤ^N`), hence their
real span is everything.  Consequently the volume computed by `coneSliceVol` is an ordinary
`N`-dimensional Lebesgue volume, and rescaling the two cone normals
`ν(x) ↦ (2α/‖ν(x)‖)·ν(x)` turns the cone conditions `|⟪ν(x),t⟫| ≤ ‖ν(x)‖‖t‖/(2α)` into the
unit form `|⟪w,t⟫| ≤ ‖t‖` appearing in `JcVol`.

The proof splits into three independent ingredients (each proved below):

* `spanE_GamLoc_eq_top` : `span_ℝ(Γ^{loc}_{x,y}(Q)) = ⊤` for `Q ≥ 1`;
* `subVol_top` : `subVol ⊤ S = volume S` for a measurable `S`;
* `abs_inner_cone_scale` : the pointwise rescaling identity for the cone condition.

The main theorem `coneSliceVol_GamLoc` is their assembly.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Finset
open scoped RealInnerProductSpace

namespace Work.HP

/-! ## The `ℤ`-scaling of `toEr` -/

/-- `toEr` intertwines integer scalars with real scalars. -/
lemma toEr_zsmul {ι : Type*} (z : ℤ) (a : ι → ℤ) : toEr (z • a) = (z : ℝ) • toEr a := by
  have h1 : toR (z • a) = (z : ℝ) • toR a := by
    funext j; simp [toR, Pi.smul_apply]
  show toE (toR (z • a)) = (z : ℝ) • toE (toR a)
  rw [h1]; simp only [toE, WithLp.toLp_smul]

/-! ## The local lattice has full real span -/

/-- The real span of the local lattice `Γ^{loc}_{x,y}(Q) = Λ^{(Q)}_{ν(x)} ∩ Λ^{(Q)}_{ν(y)}` is all
of `EuclideanSpace ℝ (Mon d n)`, for any `Q ≥ 1`. -/
theorem spanE_GamLoc_eq_top (d n : ℕ) [DecidableEq (Mon d n)]
    (x y : Fin (n + 1) → ℤ) (Q : ℕ) (hQ : 1 ≤ Q) :
    spanE (GamLoc d n x y Q) = ⊤ := by
  let T : (Mon d n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Mon d n) :=
    (WithLp.linearEquiv 2 ℝ (Mon d n → ℝ)).symm
  have hb : Submodule.span ℝ (Set.range (fun i : Mon d n => Pi.single i (1:ℝ))) = ⊤ := by
    have h := Module.Basis.span_eq (Pi.basisFun ℝ (Mon d n))
    have h2 : Set.range ⇑(Pi.basisFun ℝ (Mon d n))
        = Set.range (fun i : Mon d n => Pi.single i (1:ℝ)) := by
      congr 1; funext i; rw [Pi.basisFun_apply]
    rwa [h2] at h
  have hS1 : Set.range (fun i : Mon d n => toEr (Pi.single i (1:ℤ)))
      = Set.range (fun i : Mon d n => toE (Pi.single i (1:ℝ))) := by
    congr 1; funext i
    show toE (toR (Pi.single i (1:ℤ))) = toE (Pi.single i (1:ℝ))
    congr 1; funext j; simp [toR, Pi.single_apply]
  have hT : ∀ s : Mon d n → ℝ, T s = toE s := by
    intro s; rw [WithLp.linearEquiv_symm_apply]; rfl
  have hS2 : Set.range (fun i : Mon d n => toE (Pi.single i (1:ℝ)))
      = T '' Set.range (fun i : Mon d n => Pi.single i (1:ℝ)) := by
    rw [show (fun i : Mon d n => toE (Pi.single i (1:ℝ)))
        = T ∘ (fun i : Mon d n => Pi.single i (1:ℝ)) from by
      funext i; exact (hT _).symm]
    rw [Set.range_comp]
  have hS_span :
      Submodule.span ℝ (Set.range (fun i : Mon d n => toEr (Pi.single i (1:ℤ)))) = ⊤ := by
    rw [hS1, hS2]
    show Submodule.span ℝ (⇑(T : (Mon d n → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Mon d n))
      '' Set.range (fun i : Mon d n => Pi.single i (1:ℝ))) = ⊤
    rw [Submodule.span_image (T : (Mon d n → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Mon d n)),
      hb, Submodule.map_top, LinearEquiv.range]
  -- the standard basis vector scaled by `Q` is in both congruence lattices
  have key : ∀ i : Mon d n, (Q : ℤ) • (Pi.single i (1:ℤ)) ∈ GamLoc d n x y Q := by
    intro i
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [latMod, Submodule.mem_comap, Submodule.mem_span_singleton]
      refine ⟨Fintype.linearCombination ℤ (veronese d n x) (Pi.single i (1:ℤ)), ?_⟩
      rw [map_smul, smul_eq_mul, smul_eq_mul]; ring
    · rw [latMod, Submodule.mem_comap, Submodule.mem_span_singleton]
      refine ⟨Fintype.linearCombination ℤ (veronese d n y) (Pi.single i (1:ℤ)), ?_⟩
      rw [map_smul, smul_eq_mul, smul_eq_mul]; ring
  have hmemT : ∀ i : Mon d n, toEr (Pi.single i (1:ℤ)) ∈ spanE (GamLoc d n x y Q) := by
    intro i
    have h1 : toEr ((Q : ℤ) • (Pi.single i (1:ℤ))) ∈ spanE (GamLoc d n x y Q) :=
      Submodule.subset_span ⟨_, key i, rfl⟩
    rw [toEr_zsmul] at h1
    have hQne : (((Q : ℤ)) : ℝ) ≠ 0 := by
      have hle : (1:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hQ
      have hcast : (((Q:ℤ)) : ℝ) = (Q:ℝ) := by simp
      rw [hcast]; positivity
    have h2 := Submodule.smul_mem (spanE (GamLoc d n x y Q)) ((((Q:ℤ)):ℝ))⁻¹ h1
    rwa [inv_smul_smul₀ hQne] at h2
  have hle : ⊤ ≤ spanE (GamLoc d n x y Q) := by
    rw [← hS_span]
    exact Submodule.span_le.mpr (Set.range_subset_iff.mpr hmemT)
  exact le_antisymm le_top hle

/-! ## `subVol` of the whole space -/

/-- For a measurable `S`, the `subVol` of `S` inside the full subspace `⊤` is the ordinary Lebesgue
volume of `S`. -/
theorem subVol_top {ι : Type*} [Fintype ι] (S : Set (EuclideanSpace ℝ ι))
    (hS : MeasurableSet S) :
    subVol (⊤ : Submodule ℝ (EuclideanSpace ℝ ι)) S = (volume S).toReal := by
  rw [subVol]
  -- `↥⊤` is isometric to `EuclideanSpace ℝ ι` via `Submodule.topEquiv`
  let e : ↥(⊤ : Submodule ℝ (EuclideanSpace ℝ ι)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι :=
    LinearEquiv.isometryOfInner (Submodule.topEquiv) (by
      intro x y
      simp only [Submodule.topEquiv_apply]
      rw [Submodule.coe_inner])
  have he : ∀ t : ↥(⊤ : Submodule ℝ (EuclideanSpace ℝ ι)), e t = (t : EuclideanSpace ℝ ι) := by
    intro t
    dsimp only [e]
    rw [LinearEquiv.coe_isometryOfInner]
    exact Submodule.topEquiv_apply t
  have hpre : (e ⁻¹' S)
      = {t : ↥(⊤ : Submodule ℝ (EuclideanSpace ℝ ι)) | (t : EuclideanSpace ℝ ι) ∈ S} := by
    ext t
    change e t ∈ S ↔ (t : EuclideanSpace ℝ ι) ∈ S
    rw [he t]
  rw [show (volume {t : ↥(⊤ : Submodule ℝ (EuclideanSpace ℝ ι)) |
        (t : EuclideanSpace ℝ ι) ∈ S}) = volume (e ⁻¹' S) from by rw [hpre]]
  rw [MeasureTheory.MeasurePreserving.measure_preimage e.measurePreserving hS.nullMeasurableSet]

/-! ## The cone condition under rescaling of the normal -/

/-- Rescaling the normal `u` to `(2α/‖u‖)·u` converts the cone condition
`|⟪u,t⟫| ≤ ‖u‖‖t‖/(2α)` into the normalised form `|⟪w,t⟫| ≤ ‖t‖`.  The degenerate case `u = 0`
is consistent because both sides become trivial. -/
theorem abs_inner_cone_scale {ι : Type*} [Fintype ι] (u : ι → ℝ) (α : ℝ) (hα : 0 < α)
    (t : EuclideanSpace ℝ ι) :
    |inner ℝ (toE (fun m => (2 * α / ‖toE u‖) * u m)) t| ≤ ‖t‖
      ↔ |inner ℝ (toE u) t| ≤ ‖toE u‖ * ‖t‖ / (2 * α) := by
  rw [show (fun m => 2 * α / ‖toE u‖ * u m) = (2 * α / ‖toE u‖) • u from rfl,
      show (toE ((2 * α / ‖toE u‖) • u)) = (2 * α / ‖toE u‖) • toE u from rfl,
      real_inner_smul_left, abs_mul, abs_of_nonneg (by positivity)]
  by_cases hr : ‖toE u‖ = 0
  · rw [hr, norm_eq_zero.mp hr]
    simp
  · have hrpos : 0 < ‖toE u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hr)
    rw [div_mul_eq_mul_div, div_le_iff₀ hrpos, le_div_iff₀ (by positivity : (0:ℝ) < 2 * α)]
    ring_nf

/-! ## The main theorem -/

theorem coneSliceVol_GamLoc (d n : ℕ) [DecidableEq (Mon d n)] (hd : 2 ≤ d)
    (x y : Fin (n + 1) → ℤ) (Q : ℕ) (hQ : 1 ≤ Q) (α : ℝ) (hα : 0 < α) :
    coneSliceVol (GamLoc d n x y Q) (toR (veronese d n x)) (toR (veronese d n y)) α
      = JcVol (toE (fun m => (2 * α / ‖toE (toR (veronese d n x))‖) * toR (veronese d n x) m))
          (toE (fun m => (2 * α / ‖toE (toR (veronese d n y))‖) * toR (veronese d n y) m)) := by
  rw [coneSliceVol, JcVol, spanE_GamLoc_eq_top d n x y Q hQ]
  set v : Mon d n → ℝ := toR (veronese d n x) with hv
  set w : Mon d n → ℝ := toR (veronese d n y) with hw
  have hA : MeasurableSet {t : EuclideanSpace ℝ (Mon d n) |
      |inner ℝ (toE v) t| ≤ ‖toE v‖ * ‖t‖ / (2 * α)} :=
    (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  have hB : MeasurableSet {t : EuclideanSpace ℝ (Mon d n) |
      |inner ℝ (toE w) t| ≤ ‖toE w‖ * ‖t‖ / (2 * α)} :=
    (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  have hC : MeasurableSet {t : EuclideanSpace ℝ (Mon d n) | ‖t‖ ≤ 1} :=
    (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  have hSmeas : MeasurableSet {t : EuclideanSpace ℝ (Mon d n) |
      |inner ℝ (toE v) t| ≤ ‖toE v‖ * ‖t‖ / (2 * α) ∧
      |inner ℝ (toE w) t| ≤ ‖toE w‖ * ‖t‖ / (2 * α) ∧ ‖t‖ ≤ 1} :=
    hA.inter (hB.inter hC)
  rw [subVol_top _ hSmeas]
  have hset : {t : EuclideanSpace ℝ (Mon d n) |
        |inner ℝ (toE v) t| ≤ ‖toE v‖ * ‖t‖ / (2 * α) ∧
        |inner ℝ (toE w) t| ≤ ‖toE w‖ * ‖t‖ / (2 * α) ∧ ‖t‖ ≤ 1}
      = {t : EuclideanSpace ℝ (Mon d n) |
        |inner ℝ (toE (fun m => (2 * α / ‖toE v‖) * v m)) t| ≤ ‖t‖ ∧
        |inner ℝ (toE (fun m => (2 * α / ‖toE w‖) * w m)) t| ≤ ‖t‖ ∧ ‖t‖ ≤ 1} := by
    ext t
    simp only [Set.mem_ofPred_eq]
    rw [abs_inner_cone_scale v α hα t, abs_inner_cone_scale w α hα t]
  rw [hset]

end Work.HP
