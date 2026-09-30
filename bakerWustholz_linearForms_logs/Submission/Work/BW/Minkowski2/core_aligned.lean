import Mathlib
import Submission.Work.BW.Minkowski2.defs
import Submission.Work.BW.Minkowski2.section_maps
import Submission.Work.BW.Minkowski2.centroidMap_volume
import Submission.Work.BW.Minkowski2.centroidMap_lattice_free
import Submission.Work.BW.Minkowski2.volume_le_volume_fundamentalDomain
import Submission.Work.BW.Minkowski2.gauge_mem_interior
import Submission.Work.BW.minkowski_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.Minkowski2

open MeasureTheory
open scoped Pointwise

theorem core_aligned {d : ℕ} (Λ : Submodule ℤ (Fin d → ℝ)) (F : Set (Fin d → ℝ)) [Countable Λ]
    (hF : MeasureTheory.IsAddFundamentalDomain Λ.toAddSubgroup F MeasureTheory.volume)
    (hFfin : MeasureTheory.volume F ≠ ⊤)
    (K : Set (Fin d → ℝ)) (hKc : Convex ℝ K) (hsym : ∀ x ∈ K, -x ∈ K) (hKcl : IsClosed K)
    (hKbd : Bornology.IsBounded K) (hKi : (interior K).Nonempty)
    (lam : Fin (d+1) → ℝ) (hlam0 : lam 0 = 0) (hpos : ∀ i : Fin d, 0 < lam i.succ)
    (hmono : ∀ i j : Fin d, i ≤ j → lam i.succ ≤ lam j.succ)
    (hflag : ∀ (i : Fin d) (z : Fin d → ℝ), z ∈ (Λ : Set (Fin d → ℝ)) →
      gauge K z < lam i.succ → ∀ m : Fin d, i ≤ m → z m = 0) :
    (∏ i : Fin d, lam i.succ) * MeasureTheory.volume.real K
      ≤ (2:ℝ)^d * MeasureTheory.volume.real F := by
  classical
  -- Section maps: choices `c i x` of a point of `K` with the same coordinates `≥ i` as `x`,
  -- measurably, mapping `interior K` into itself.
  obtain ⟨c, hcmeas, _hcK, hcint, hcfix, hcdep⟩ := section_maps K hKc hsym hKcl hKbd hKi
  have h0 : (0 : Fin d → ℝ) ∈ interior K := zero_mem_interior_of_symm hKc hsym hKi
  -- Restate the flag hypothesis in terms of `interior (λ • K)`.
  have hflagI : ∀ (i : Fin d) (z : Fin d → ℝ), z ∈ (Λ : Set (Fin d → ℝ)) →
      z ∈ interior (Work.BW.smulSet (lam i.succ) K) → ∀ m : Fin d, i ≤ m → z m = 0 := by
    intro i z hz hzi m hm
    exact hflag i z hz ((mem_interior_smulSet_iff_gauge_lt hKc h0 (hpos i) z).mp hzi) m hm
  -- The centroid map and the fact that its image of `interior K` has no two points differing by a
  -- nonzero lattice vector.
  have havoid : ∀ z ∈ (Λ : Set (Fin d → ℝ)), z ≠ 0 →
      ∀ x ∈ (fun x : Fin d → ℝ => ∑ i : Fin d, ((lam i.succ - lam i.castSucc) / 2) • c i x)
            '' (interior K),
        x + z ∉ (fun x : Fin d → ℝ => ∑ i : Fin d, ((lam i.succ - lam i.castSucc) / 2) • c i x)
            '' (interior K) := by
    rintro z hz hz0 x ⟨p, hp, rfl⟩ ⟨q, hq, hqx⟩
    have hqx' : (∑ i : Fin d, ((lam i.succ - lam i.castSucc) / 2) • c i q)
        = (∑ i : Fin d, ((lam i.succ - lam i.castSucc) / 2) • c i p) + z := hqx
    have hne : p ≠ q := by
      rintro rfl
      have hcancel :
          (∑ i : Fin d, ((lam i.succ - lam i.castSucc) / 2) • c i p) + z
            = (∑ i : Fin d, ((lam i.succ - lam i.castSucc) / 2) • c i p) + 0 := by
        rw [add_zero]
        exact hqx'.symm
      exact hz0 (add_left_cancel hcancel)
    exact (centroidMap_lattice_free Λ K hKc hsym lam hlam0 hpos hmono hflagI c hcint hcfix
      hcdep hq hp (Ne.symm hne)) z hz (by rw [hqx']; abel)
  -- Volume of the image.
  have himg := centroidMap_volume lam hlam0 hpos c hcmeas hcfix hcdep
    (isOpen_interior (s := K)).measurableSet
  have hle : MeasureTheory.volume ((fun x : Fin d → ℝ =>
        ∑ i : Fin d, ((lam i.succ - lam i.castSucc) / 2) • c i x) '' (interior K))
      ≤ MeasureTheory.volume F :=
    volume_le_volume_fundamentalDomain Λ F hF himg.2 havoid
  have hle' : MeasureTheory.volume.real ((fun x : Fin d → ℝ =>
        ∑ i : Fin d, ((lam i.succ - lam i.castSucc) / 2) • c i x) '' (interior K))
      ≤ MeasureTheory.volume.real F :=
    ENNReal.toReal_mono hFfin hle
  -- `K` and its interior have the same volume (the frontier of a convex set is null).
  have hinter : MeasureTheory.volume (interior K) = MeasureTheory.volume K := by
    have hfr : MeasureTheory.volume (frontier K) = 0 :=
      Convex.addHaar_frontier MeasureTheory.volume hKc
    have hdiff : K \ interior K ⊆ frontier K := by
      intro x hx
      rw [frontier_eq_closure_inter_closure]
      exact ⟨by rw [hKcl.closure_eq]; exact hx.1, by rw [closure_compl]; exact hx.2⟩
    have hunion : interior K ∪ (K \ interior K) = K := by
      ext x
      constructor
      · rintro (h | h)
        · exact interior_subset h
        · exact h.1
      · intro hx
        by_cases h : x ∈ interior K
        · exact Or.inl h
        · exact Or.inr ⟨hx, h⟩
    refine le_antisymm (MeasureTheory.measure_mono interior_subset) ?_
    calc MeasureTheory.volume K
        = MeasureTheory.volume (interior K ∪ (K \ interior K)) := by rw [hunion]
      _ ≤ MeasureTheory.volume (interior K) + MeasureTheory.volume (K \ interior K) :=
            MeasureTheory.measure_union_le _ _
      _ ≤ MeasureTheory.volume (interior K) + MeasureTheory.volume (frontier K) :=
            add_le_add le_rfl (MeasureTheory.measure_mono hdiff)
      _ = MeasureTheory.volume (interior K) := by rw [hfr, add_zero]
  have hreal : MeasureTheory.volume.real (interior K) = MeasureTheory.volume.real K := by
    rw [Measure.real_def, Measure.real_def, hinter]
  -- Combine.
  have h1 : (∏ i : Fin d, lam i.succ / 2) * MeasureTheory.volume.real K
      ≤ MeasureTheory.volume.real F := by
    rw [← hreal, ← himg.1]
    exact hle'
  have h2 : (∏ i : Fin d, lam i.succ / 2) = (∏ i : Fin d, lam i.succ) / (2:ℝ)^d := by
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [h2] at h1
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^d)] at h1
  rw [mul_comm (MeasureTheory.volume.real F) ((2:ℝ)^d)] at h1
  exact h1

end Work.BW.Minkowski2
