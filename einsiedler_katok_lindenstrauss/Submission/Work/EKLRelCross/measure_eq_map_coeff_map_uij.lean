import Mathlib
import Submission.Work.EKLRelCross.PeriodFunsDefs

/-!
# A measure carried by a root subgroup is the push-forward of its coordinate

For `i ≠ j` let `u : ℝ → SL₃(ℝ)`, `u t = u_ij(t) = 1 + t E_ij`, and let
`c : SL₃(ℝ) → ℝ`, `c g = g i j`, be the `(i,j)`-coordinate functional, so that
`c ∘ u = id` (`uij_coeff`).

If a measure `ν` on `SL₃(ℝ)` is carried by the image of `u` — that is,
`ν (range u)ᶜ = 0` — then pushing `ν` forward along `c` and then back along `u`
returns `ν`:

`ν = (ν.map c).map u`.

Indeed `u ∘ c` agrees with the identity on `range u`, hence `ν`-almost everywhere,
so `(ν.map c).map u = ν.map (u ∘ c) = ν.map id = ν` by `Measure.map_congr`.
-/

namespace Work.EKLRelCross

open MeasureTheory

theorem measure_eq_map_coeff_map_uij {i j : Fin 3} (hij : i ≠ j)
    (ν : MeasureTheory.Measure Work.EKLContract.SL3)
    (hν : ν (Set.range (fun t : ℝ => Work.EKLContract.uij hij t))ᶜ = 0) :
    ν = (ν.map (fun g : Work.EKLContract.SL3 => (g : Matrix (Fin 3) (Fin 3) ℝ) i j)).map
          (fun t : ℝ => Work.EKLContract.uij hij t) := by
  classical
  set u : ℝ → Work.EKLContract.SL3 := fun t => Work.EKLContract.uij hij t with hu_def
  set c : Work.EKLContract.SL3 → ℝ := fun g => (g : Matrix (Fin 3) (Fin 3) ℝ) i j with hc_def
  -- `c` is a left inverse of `u`
  have hcu : ∀ t : ℝ, c (u t) = t := fun t => uij_coeff hij t
  -- on the image of `u`, the map `u ∘ c` is the identity
  have huc : ∀ x ∈ Set.range u, u (c x) = x := by
    rintro x ⟨t, rfl⟩
    rw [hcu t]
  -- `ν` is carried by `range u`
  have hmem : ∀ᵐ x ∂ν, x ∈ Set.range u := by
    rw [MeasureTheory.ae_iff]
    exact hν
  have hmeas_u : Measurable u := by
    rw [hu_def]; exact (Work.EKLC7.continuous_uij hij).measurable
  have hmeas_c : Measurable c := by
    rw [hc_def]; exact continuous_coeff.measurable
  have hmain : (ν.map c).map u = ν := by
    rw [Measure.map_map hmeas_u hmeas_c]
    have hcongr : (u ∘ c) =ᵐ[ν] id := by
      filter_upwards [hmem] with x hx
      exact huc x hx
    rw [Measure.map_congr hcongr, Measure.map_id]
  simp only [hu_def, hc_def] at hmain ⊢
  exact hmain.symm

end Work.EKLRelCross
