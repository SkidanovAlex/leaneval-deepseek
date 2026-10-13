/-
  Locality of the padded stratum `padStratS p q d S hj`.

  If `S : Stratum p q` is `Good`, then in the neighbourhood of any point `z` of the padded
  set, a point `z'` with the same base coordinates `p` and satisfying all defining equations
  of the padded stratum already lies in the padded set.  The point is that

  * the defining equations of the padded stratum say precisely that the `d` inserted coordinates
    vanish and that the pulled-back defining functions of `S` vanish at the restriction
    `z' ∘ midInj`, and
  * `Good` gives the corresponding locality statement for `S` around the restriction
    `z ∘ midInj`, which is transported back along the (continuous) restriction map.
-/
import Mathlib
import Submission.Work.WilE7.PadDefs

namespace Work.WilE7.PadAux

open WilkiesConjecture WilkiesDesign WilkiesDesign.E
open Work.WilE7

/-- The restriction map `z ↦ z ∘ midInj` is continuous, whence any property holding eventually
near the restriction of `z` holds eventually near `z` after restricting. -/
theorem padLocal_tendsto_restrict (p q d : ℕ) (z : Fin (p + (d + q)) → ℝ)
    (P : (Fin (p + q) → ℝ) → Prop)
    (h : Filter.Eventually P (nhds (fun i => z (midInj p d q i)))) :
    Filter.Eventually (fun z' : Fin (p + (d + q)) → ℝ =>
      P (fun i => z' (midInj p d q i))) (nhds z) := by
  have hcont : Continuous (fun z' : Fin (p + (d + q)) → ℝ =>
      fun i : Fin (p + q) => z' (midInj p d q i)) :=
    continuous_pi (fun i => continuous_apply _)
  exact hcont.continuousAt.eventually h

/-- A point whose restriction lies in the base set `S.X.set` and whose inserted block vanishes
lies in the padded set. -/
theorem padLocal_mem_of_restrict (p q d : ℕ) (S : WilkiesDesign.E.Stratum p q)
    (hj : S.j = q) (z' : Fin (p + (d + q)) → ℝ)
    (hbase : (fun i => z' (midInj p d q i)) ∈ S.X.set)
    (hpin : ∀ a : Fin d, z' (midIdx p d q a) = 0) :
    z' ∈ (padStratS p q d S hj).X.set := by
  rw [padStratS_X, padStrat_set]
  refine ⟨?_, hpin⟩
  rwa [tidy_set]

/-- Vanishing of all defining functions of the padded stratum splits into vanishing of the
inserted coordinates and vanishing of the pulled-back defining functions of `S`. -/
theorem padLocal_h_vanishing (p q d : ℕ) (S : WilkiesDesign.E.Stratum p q)
    (hj : S.j = q) (z' : Fin (p + (d + q)) → ℝ)
    (h : ∀ a, eaEval (padStratS p q d S hj).X.c ((padStratS p q d S hj).h a) z' = 0) :
    (∀ a : Fin d, z' (midIdx p d q a) = 0) ∧
      (∀ b : Fin q, eaEval S.X.c (S.h (Fin.cast hj.symm b))
        (fun i => z' (midInj p d q i)) = 0) := by
  constructor
  · intro a
    have h1 := h (Fin.castAdd q a)
    rwa [eaEval_padStratS_h_castAdd] at h1
  · intro b
    have h1 := h (Fin.natAdd d b)
    rwa [eaEval_padStratS_h_natAdd] at h1

theorem padStratS_good_local (p q d : ℕ) (S : WilkiesDesign.E.Stratum p q)
    (hGood : S.Good) (hj : S.j = q) (z : Fin (p + (d + q)) → ℝ)
    (hz : z ∈ (Work.WilE7.padStratS p q d S hj).X.set) :
    Filter.Eventually (fun z' : Fin (p + (d + q)) → ℝ =>
      WilkiesDesign.E.projFirst p (d + q) z' = WilkiesDesign.E.projFirst p (d + q) z →
      (∀ a, WilkiesDesign.E.eaEval (Work.WilE7.padStratS p q d S hj).X.c
        ((Work.WilE7.padStratS p q d S hj).h a) z' = 0) →
        z' ∈ (Work.WilE7.padStratS p q d S hj).X.set) (nhds z) := by
  -- The restriction of `z` is a point of the base set.
  have hzmem : (fun i => z (midInj p d q i)) ∈ S.X.set := by
    have h1 := hz
    rw [padStratS_X, padStrat_set] at h1
    have h2 : (fun i => z (midInj p d q i)) ∈ (tidy S.X).set ∧
        ∀ a : Fin d, z (midIdx p d q a) = 0 := by simpa using h1
    exact tidy_set (X := S.X) ▸ h2.1
  -- Locality of `S` at that restriction point.
  have hEv : ∀ᶠ w' in nhds (fun i => z (midInj p d q i)),
      (projFirst p q w' = projFirst p q (fun i => z (midInj p d q i)) →
        (∀ a, eaEval S.X.c (S.h a) w' = 0) → w' ∈ S.X.set) :=
    (hGood _ hzmem).2.2
  -- Transport it back along the restriction map.
  filter_upwards [padLocal_tendsto_restrict p q d z _ hEv] with z' hz'
  intro hproj hzero
  obtain ⟨hpin, hbase⟩ := padLocal_h_vanishing p q d S hj z' hzero
  refine padLocal_mem_of_restrict p q d S hj z' ?_ hpin
  refine hz' ?_ ?_
  · rw [projFirst_midInj, projFirst_midInj]
    exact hproj
  · intro a
    have h1 := hbase (Fin.cast hj a)
    rwa [Fin.cast_cast] at h1

end Work.WilE7.PadAux
