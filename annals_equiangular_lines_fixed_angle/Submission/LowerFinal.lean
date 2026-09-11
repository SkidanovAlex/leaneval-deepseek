import Submission.LowerHas
import Submission.KOrder
import Submission.Perron

open EquiangularLinesFixedAngle
open Filter
open scoped BigOperators
open scoped RealInnerProductSpace

namespace Submission

set_option maxHeartbeats 1200000

/-! Final glue of the lower bound: `N α d` is at least the floor value from the
disjoint-union construction, eventually in `d`. -/

open Classical in
/-- For a `k0`-vertex witness `H`, `N α d` is at least the floor value for all `d ≥ 1`. -/
lemma N_ge_floor_witness {α : ℝ} {d k0 : ℕ} (H : SimpleGraph (Fin k0))
    (hα0 : 0 < α) (hα1 : α < 1) (hk0 : 2 ≤ k0) (hd : 1 ≤ d)
    (hρ : spectralRadius ℝ (H.adjMatrix ℝ) = ENNReal.ofReal (lam α)) :
    ⌊((k0 * (d - 1) : ℝ) / (k0 - 1 : ℝ))⌋₊ ≤ N α d := by
  classical
  have hl := hasLines_union_dim (d := d) (k0 := k0) H hα0 hα1 hk0 hd hρ
  have hle : ((d - 1) / (k0 - 1)) * k0 + ((d - 1) % (k0 - 1)) ≤ N α d :=
    le_N_of_hasLines hα0 hα1 hl
  have hn : ⌊((k0 * (d - 1) : ℝ) / (k0 - 1 : ℝ))⌋₊ = ((d - 1) / (k0 - 1)) * k0 + ((d - 1) % (k0 - 1)) :=
    floor_count_real_sub hk0 hd
  rwa [hn]

/-- When the spectral radius order is finite, the lower bound holds eventually. -/
lemma eventually_lower_bound (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hkl : spectralRadiusOrder (lam α) < (⊤ : ℕ∞)) :
    ∀ᶠ d : ℕ in atTop,
      ⌊((((spectralRadiusOrder (lam α)).toNat * (d - 1) : ℝ))
          / (((spectralRadiusOrder (lam α)).toNat - 1 : ℝ)))⌋₊ ≤ N α d := by
  classical
  rw [eventually_atTop]
  refine ⟨1, ?_⟩
  intro d hd
  have hk0 : 2 ≤ (spectralRadiusOrder (lam α)).toNat :=
    spectralRadiusOrder_toNat_ge_two (lam_pos hα0 hα1) hkl
  have hw := spectralRadiusOrder_lt_top_witness (lam := lam α) hkl
  rcases hw with ⟨H, hρ⟩
  exact N_ge_floor_witness (k0 := (spectralRadiusOrder (lam α)).toNat) H hα0 hα1 hk0 hd hρ

end Submission
