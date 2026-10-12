import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.LatFourierDefs
import Submission.Work.BoseBoxFock.setIntegral_comp_add_right
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.latTiling_integral` — the lattice tiling of `ℝ³` by `ℓℤ³`-translates of the
half-open cell `[0,ℓ)³`

The half-open cube `latCell ℓ = [0,ℓ)³` (`LatFourier.latCell`) is a fundamental domain of the
translation action of the integer lattice `ℤ³ ∋ m ↦ ℓ • latVec m` on `ℝ³`: its translates
`latTile ℓ m = latCell ℓ + ℓ • latVec m` are pairwise disjoint and cover `ℝ³`.  Consequently the
Lebesgue integral of any integrable function is the sum of its integrals over the tiles,

    ∫ u, f u = ∑' m : Fin 3 → ℤ, ∫ z in latCell ℓ, f (z + ℓ • latVec m) ,

which is the target `Work.BoseBoxFock.latTiling_integral`.

The proof is the standard three-step decomposition:

* `latTile_coord`/`latTile_disjoint` — the tiles are pairwise disjoint, from the uniqueness of the
  integer in the one-dimensional half-open partition `[m, m+1)` of `ℝ` rescaled by `ℓ` (a
  difference of two members of an interval of length `ℓ` is an integer multiple of `ℓ` of modulus
  `< ℓ`);
* `latTile_cover` — the tiles cover `ℝ³`, from the existence half of the same partition via
  `Int.sub_floor_div_mul_nonneg`/`Int.sub_floor_div_mul_lt`;
* `integral_iUnion` decomposes the integral over the union, and the translation invariance of
  Lebesgue measure (`setIntegral_comp_add_right`, the Bochner analogue of
  `lattice_lintegral_tiling`'s `lintegral_shift_set`) rewrites each summand back into an integral
  over the single cell `latCell ℓ`.
-/

namespace Work.BoseBoxFock

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## The tiles `latCell ℓ + ℓ • latVec m` -/

/-- The translate of the half-open cell `latCell ℓ = [0,ℓ)³` by the lattice vector
`ℓ • latVec m`.  These tiles are the images whose disjointness and union are the content of the
tiling. -/
def latTile (ℓ : ℝ) (m : Fin 3 → ℤ) : Set E3 :=
  (fun z : E3 => z + ℓ • latVec m) '' LatFourier.latCell ℓ

/-- Membership in a tile, as an element of the cell. -/
lemma latTile_mem (ℓ : ℝ) (m : Fin 3 → ℤ) (x : E3) :
    x ∈ latTile ℓ m ↔ x - ℓ • latVec m ∈ LatFourier.latCell ℓ := by
  constructor
  · rintro ⟨y, hy, rfl⟩; simpa using hy
  · intro hx; exact ⟨x - ℓ • latVec m, hx, by simp⟩

/-- Membership in a tile, in coordinates. -/
lemma latTile_coord (ℓ : ℝ) (m : Fin 3 → ℤ) (x : E3) :
    x ∈ latTile ℓ m ↔ ∀ i, x i - ℓ * (m i : ℝ) ∈ Set.Ico (0:ℝ) ℓ := by
  rw [latTile_mem, LatFourier.mem_latCell]
  constructor
  · intro h i; simpa [latVec] using h i
  · intro h i; simpa [latVec] using h i

/-- The tiles are pairwise disjoint: two members of the same coordinate interval of length `ℓ`
differ, in each coordinate, by an integer multiple of `ℓ` of modulus `< ℓ`, hence by `0`. -/
lemma latTile_disjoint (ℓ : ℝ) (hℓ : 0 < ℓ) :
    Pairwise (fun m m' => Disjoint (latTile ℓ m) (latTile ℓ m')) := by
  intro m m' hne
  rw [Set.disjoint_iff]
  rintro x ⟨hx, hx'⟩
  apply hne
  funext i
  have h1 := (latTile_coord ℓ m x).mp hx i
  have h2 := (latTile_coord ℓ m' x).mp hx' i
  have h3 : |((m' i : ℝ) - (m i : ℝ))| < 1 := by
    have h4 : |ℓ * ((m' i : ℝ) - (m i : ℝ))| < ℓ := by
      have heq : ℓ * ((m' i : ℝ) - (m i : ℝ))
          = (x i - ℓ * (m i : ℝ)) - (x i - ℓ * (m' i : ℝ)) := by ring
      rw [heq, abs_lt]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    rw [abs_mul, abs_of_pos hℓ] at h4
    nlinarith [h4]
  have hlt : (m' i - m i : ℤ) < 1 := by
    have : ((m' i - m i : ℤ) : ℝ) < 1 := by push_cast; exact (abs_lt.mp h3).2
    exact_mod_cast this
  have hgt : (-1 : ℤ) < m' i - m i := by
    have : (-1 : ℝ) < ((m' i - m i : ℤ) : ℝ) := by push_cast; exact (abs_lt.mp h3).1
    exact_mod_cast this
  omega

/-- The tiles cover `ℝ³`: the integer part `⌊x i / ℓ⌋` places `x` in the tile of that lattice
vector. -/
lemma latTile_cover (ℓ : ℝ) (hℓ : 0 < ℓ) : (⋃ m : Fin 3 → ℤ, latTile ℓ m) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  refine ⟨fun i => ⌊x i / ℓ⌋, ?_⟩
  rw [latTile_coord]
  intro i
  exact ⟨by simpa [mul_comm] using Int.sub_floor_div_mul_nonneg (x i) hℓ,
         by simpa [mul_comm] using Int.sub_floor_div_mul_lt (x i) hℓ⟩

/-- The tiles are measurable. -/
lemma latTile_measurable (ℓ : ℝ) (m : Fin 3 → ℤ) : MeasurableSet (latTile ℓ m) := by
  have h : latTile ℓ m = (fun x : E3 => x - ℓ • latVec m) ⁻¹' LatFourier.latCell ℓ := by
    ext x; rw [Set.mem_preimage, latTile_mem]
  rw [h]
  exact (LatFourier.measurableSet_latCell ℓ).preimage (by fun_prop)

/-! ## The tiling identity for the Bochner integral -/

theorem latTiling_integral {ℓ : ℝ} (hℓ : 0 < ℓ) (f : EuclideanSpace ℝ (Fin 3) → ℂ)
    (hf : MeasureTheory.Integrable f MeasureTheory.volume) :
    ∫ u, f u = ∑' m : Fin 3 → ℤ,
      ∫ z in Work.BoseBoxFock.LatFourier.latCell ℓ,
        f (z + ℓ • Work.BoseBoxFock.latVec m) := by
  have hfi : IntegrableOn f (⋃ m, latTile ℓ m) volume := by
    rw [latTile_cover ℓ hℓ, integrableOn_univ]; exact hf
  calc ∫ u, f u = ∫ u in Set.univ, f u := setIntegral_univ.symm
    _ = ∫ u in ⋃ m, latTile ℓ m, f u := by rw [latTile_cover ℓ hℓ]
    _ = ∑' m, ∫ u in latTile ℓ m, f u :=
        integral_iUnion (fun m => latTile_measurable ℓ m) (latTile_disjoint ℓ hℓ) hfi
    _ = ∑' m, ∫ z in LatFourier.latCell ℓ, f (z + ℓ • latVec m) := by
        refine tsum_congr fun m => ?_
        exact (setIntegral_comp_add_right f (LatFourier.latCell ℓ) (ℓ • latVec m)).symm

end Work.BoseBoxFock
