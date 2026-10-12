import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.ChiR0Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.volume_infDist_lat_eq_zero`

The lattice `ℓℤ³ ⊂ ℝ³` is *closed and discrete* (for `ℓ ≠ 0`), so the set of points at
distance zero from it is the lattice itself, which is countable and hence of Lebesgue
measure zero.

The two ingredients are
* `isClosed_range_mul_intCast`: the scaled integers `{ℓ m : m ∈ ℤ} ⊆ ℝ` are closed (they are
  the preimage of the closed set `ℤ ⊆ ℝ` under `x ↦ x / ℓ`);
* `isClosed_range_lat`: the lattice `ℓℤ³` is closed, being the preimage of the closed set
  `∏ᵢ ℓℤ ⊆ (Fin 3 → ℝ)` under the continuous map `WithLp.ofLp`.
-/

namespace Work.BoseFixR

open MeasureTheory Metric Set

/-- The scaled integers `{ℓ * m : m ∈ ℤ}` form a closed subset of `ℝ` when `ℓ ≠ 0`. -/
lemma isClosed_range_mul_intCast {ℓ : ℝ} (hℓ : ℓ ≠ 0) :
    IsClosed (Set.range (fun m : ℤ => ℓ * (m : ℝ))) := by
  have h : Set.range (fun m : ℤ => ℓ * (m : ℝ))
      = (fun x : ℝ => x / ℓ) ⁻¹' Set.range ((↑) : ℤ → ℝ) := by
    ext x
    constructor
    · rintro ⟨m, hm⟩
      exact ⟨m, by rw [← hm]; field_simp⟩
    · rintro ⟨m, hm⟩
      refine ⟨m, ?_⟩
      show ℓ * (m : ℝ) = x
      rw [show (m : ℝ) = x / ℓ from hm]
      exact mul_div_cancel₀ x hℓ
  rw [h]
  exact Real.isClosed_range_intCast.preimage (continuous_id.div_const ℓ)

/-- The lattice `ℓℤ³` is a closed subset of `ℝ³` when `ℓ ≠ 0`. -/
lemma isClosed_range_lat {ℓ : ℝ} (hℓ : ℓ ≠ 0) :
    IsClosed (Set.range (fun n : Fin 3 → ℤ => lat ℓ n)) := by
  have h1 : IsClosed (Set.range (fun m : ℤ => ℓ * (m : ℝ))) := isClosed_range_mul_intCast hℓ
  have h : Set.range (fun n : Fin 3 → ℤ => lat ℓ n)
      = WithLp.ofLp ⁻¹'
        (Set.pi Set.univ (fun _ : Fin 3 => Set.range (fun m : ℤ => ℓ * (m : ℝ)))) := by
    ext v
    rw [Set.mem_preimage, Set.mem_pi]
    constructor
    · rintro ⟨n, rfl⟩ i _
      exact ⟨n i, rfl⟩
    · intro hv
      choose n hn using fun i => hv i (Set.mem_univ i)
      refine ⟨n, ?_⟩
      ext i
      exact hn i
  rw [h]
  exact (isClosed_set_pi (fun _ _ => h1)).preimage
    (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ))

theorem volume_infDist_lat_eq_zero {ℓ : ℝ} (hℓ : 0 < ℓ) :
    MeasureTheory.volume {z : EuclideanSpace ℝ (Fin 3) |
        Metric.infDist z (Set.range (fun n : Fin 3 → ℤ => Work.BoseFixR.lat ℓ n)) = 0} = 0 := by
  have hne : (Set.range (fun n : Fin 3 → ℤ => lat ℓ n)).Nonempty := ⟨lat ℓ 0, ⟨0, rfl⟩⟩
  have hsub : {z : EuclideanSpace ℝ (Fin 3) |
      Metric.infDist z (Set.range (fun n : Fin 3 → ℤ => Work.BoseFixR.lat ℓ n)) = 0}
      ⊆ Set.range (fun n : Fin 3 → ℤ => lat ℓ n) :=
    fun z hz => ((isClosed_range_lat hℓ.ne').mem_iff_infDist_zero hne).mpr hz
  exact measure_mono_null hsub
    ((Set.countable_range (fun n : Fin 3 → ℤ => lat ℓ n)).measure_zero volume)

end Work.BoseFixR
