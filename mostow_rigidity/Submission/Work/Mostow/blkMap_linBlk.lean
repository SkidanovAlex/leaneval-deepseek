import Mathlib
import Submission.Work.Mostow.ellipticDefs

/-!
# `blkMap k m 1 R = linBlk k m R`

The block isometry `Submission.Mostow.blkMap k m h R` is defined through the explicit Fermi
coordinates about the standard stratum `E k ↪ E (k+m)`:

`blkMap k m h R u = fermi k m (h • (fermiInv k m u).1) (R (fermiInv k m u).2)`.

Here we verify that for `h = 1` it is the plain linear block map `linBlk k m R` (keep the first
`k` coordinates, apply `R` to the last `m`).  The only non-formal input is `POActionProp k`, which
supplies `(1 : PO k 1) • v = v`.

The proof is a componentwise computation in the chart: on the tangential part the explicit factor
`cosh ‖w‖` of `fermi` cancels the inverse factor in `fermiInv`, and on the normal part the factor
`sinhc ‖w‖ · (arsinh ‖w‖)/‖w‖ = 1` cancels the explicit scalar of `fermiInv`, leaving `R` applied
to the normal coordinates.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-! ### Elementary facts about `sinhc` and the Fermi chart -/

/-- `sinhc s · s = sinh s`, with the removable singularity at `0` filled by `1`. -/
lemma sinhc_mul_self_aux (s : ℝ) : sinhc s * s = Real.sinh s := by
  rw [sinhc]
  by_cases h : s = 0
  · simp [h]
  · simp only [h, ↓reduceIte]
    field_simp

/-- Tangential part of a Fermi coordinate point. -/
lemma fermi_tanC (k m : ℕ) (v : E k) (w : E m) :
    tanC k m (fermi k m v w) = Real.cosh ‖w‖ • v := by
  ext i
  simp [tanC, fermi]

/-- Normal part of a Fermi coordinate point. -/
lemma fermi_nrmC (k m : ℕ) (v : E k) (w : E m) :
    nrmC k m (fermi k m v w) = sinhc ‖w‖ • w := by
  ext i
  simp [nrmC, fermi]

/-- Tangential part of `linBlk`. -/
lemma linBlk_tanC (k m : ℕ) (R : E m ≃ₗᵢ[ℝ] E m) (u : E (k + m)) :
    tanC k m (linBlk k m R u) = tanC k m u := by
  ext i
  simp [tanC, linBlk, Fin.append_left]

/-- Normal part of `linBlk`: it is `R` applied to the normal part of `u`. -/
lemma linBlk_nrmC (k m : ℕ) (R : E m ≃ₗᵢ[ℝ] E m) (u : E (k + m)) :
    nrmC k m (linBlk k m R u) = R (nrmC k m u) := by
  ext i
  simp [nrmC, linBlk, Fin.append_right]

/-- The normal part of `fermiInv u` has norm `arsinh ‖nrmC u‖`. -/
lemma norm_fermiInv_snd (k m : ℕ) (u : E (k + m)) :
    ‖(fermiInv k m u).2‖ = Real.arsinh ‖nrmC k m u‖ := by
  have hw : (fermiInv k m u).2
      = (if nrmC k m u = 0 then 0
         else (Real.arsinh ‖nrmC k m u‖ / ‖nrmC k m u‖) • nrmC k m u) := rfl
  rw [hw]
  by_cases hnu : nrmC k m u = 0
  · rw [ite_eq_left hnu, hnu, norm_zero, Real.arsinh_zero]
  · have hr : 0 < ‖nrmC k m u‖ := norm_pos_iff.mpr hnu
    rw [ite_eq_right hnu, norm_smul, Real.norm_eq_abs,
        abs_of_pos (div_pos (Real.arsinh_pos_iff.mpr hr) hr),
        div_mul_cancel₀ _ hr.ne']

/-- The explicit factor `sinhc ‖w‖` of `fermi` undone: applying `sinhc (arsinh ‖nrmC u‖)` to the
normal part of `fermiInv u` returns `R` of the normal part of `u`. -/
lemma smul_fermiInv_snd (k m : ℕ) (R : E m ≃ₗᵢ[ℝ] E m) (u : E (k + m)) :
    sinhc (Real.arsinh ‖nrmC k m u‖) • R ((fermiInv k m u).2) = R (nrmC k m u) := by
  have hw : (fermiInv k m u).2
      = (if nrmC k m u = 0 then 0
         else (Real.arsinh ‖nrmC k m u‖ / ‖nrmC k m u‖) • nrmC k m u) := rfl
  rw [hw]
  by_cases hz : nrmC k m u = 0
  · rw [ite_eq_left hz, hz]
    simp
  · rw [ite_eq_right hz, map_smul, smul_smul]
    have hs : sinhc (Real.arsinh ‖nrmC k m u‖)
        * (Real.arsinh ‖nrmC k m u‖ / ‖nrmC k m u‖) = 1 := by
      rw [← mul_div_assoc, sinhc_mul_self_aux, Real.sinh_arsinh,
          div_self (norm_ne_zero_iff.mpr hz)]
    rw [hs, one_smul]

/-- A point of `E (k+m)` is determined by its tangential and normal parts. -/
lemma eq_of_tanC_nrmC' {k m : ℕ} {u u' : E (k + m)}
    (h1 : tanC k m u = tanC k m u') (h2 : nrmC k m u = nrmC k m u') : u = u' := by
  apply WithLp.ofLp_injective
  funext j
  exact Fin.addCases (motive := fun j => WithLp.ofLp u j = WithLp.ofLp u' j)
    (fun i => congrFun (congrArg WithLp.ofLp h1) i)
    (fun i => congrFun (congrArg WithLp.ofLp h2) i) j

/-- For the identity foot map, the block isometry is the linear block map. -/
theorem blkMap_linBlk (k m : ℕ) (hAk : Submission.Mostow.POActionProp k)
    (R : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) (u : Submission.Mostow.E (k + m)) :
    Submission.Mostow.blkMap k m 1 R u = Work.Mostow.linBlk k m R u := by
  have hblk : Submission.Mostow.blkMap k m 1 R u
      = fermi k m (fermiInv k m u).1 (R (fermiInv k m u).2) := by
    rw [Submission.Mostow.blkMap, hAk.2.2.2.1]
  rw [hblk]
  refine eq_of_tanC_nrmC' ?_ ?_
  · rw [fermi_tanC, linBlk_tanC]
    have hnorm : ‖R (fermiInv k m u).2‖ = Real.arsinh ‖nrmC k m u‖ := by
      rw [R.norm_map, norm_fermiInv_snd]
    have ha : (fermiInv k m u).1
        = (Real.cosh (Real.arsinh ‖nrmC k m u‖))⁻¹ • tanC k m u := rfl
    rw [hnorm, ha, smul_smul, mul_inv_cancel₀ (Real.cosh_pos _).ne', one_smul]
  · rw [fermi_nrmC, linBlk_nrmC]
    have hnorm : ‖R (fermiInv k m u).2‖ = Real.arsinh ‖nrmC k m u‖ := by
      rw [R.norm_map, norm_fermiInv_snd]
    rw [hnorm, smul_fermiInv_snd]

end

end Work.Mostow
