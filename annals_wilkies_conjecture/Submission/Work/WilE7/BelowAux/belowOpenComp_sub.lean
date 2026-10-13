import Mathlib
import Submission.Work.WilE7.BelowAux.belowOpenDefs
import Submission.Work.WilE7.BelowAux.belowComp_sub
import Submission.Work.WilE7.BelowAux.connSub_graph
import Submission.Work.WilE7.BelowAux.BelowDefs

namespace Work.WilE7.BelowAux

open WilkiesDesign WilkiesDesign.E

/-!
  `belowOpenComp_sub`: the connected component of the *open* below presentation `belowSopen`
  through the interior vertical coordinate `belowT0` is contained in the open below cell.

  The closed version of this statement (`belowComp_sub`) is about the component of `belowS`
  through the *bottom* point `belowPt u₀ v₀ (-1)`.  The open statement needs two extra facts:

  * the vertical segment `t ↦ belowPt u₀ v₀ t` for `t ∈ [-1, t₀]` lies in `belowS` (the strict
    upper bound `t₀ < v₂` and the cube bound `|t₀| ≤ 1`, which follows from `S.X.set ⊆ cubeC`),
    so `belowT0` lies in the *same* component of `belowS` as the bottom point;

  * membership in `belowSopen` gives the strict lower bound `-1 < belowT belowPt`.

  With those, `belowComp_sub`'s sheet identity (`belowComp_sub_sheet_eq`) applies verbatim to
  the open component.
-/

/-! ## §1. The vertical segment of `belowS` -/

/-- For fixed data `(u, v)` the parametrised point `t ↦ belowPt u v t` is continuous: it is
`Fin.append` of a constant block and the (continuous) diagonal of `Fin 1 → ℝ`. -/
theorem continuous_belowPt_aux {p m : ℕ} (u : Fin (p + (m + 1)) → ℝ)
    (v : Fin (m + 1) → ℝ) : Continuous (fun t : ℝ => belowPt u v t) := by
  show Continuous fun t : ℝ =>
    Fin.append (Fin.append u (Fin.append (projFirst p (m + 1) u) v)) (fun _ : Fin 1 => t)
  exact (Fin.continuous_append (belowK p m) 1).comp
    (continuous_const.prodMk (continuous_pi fun _ => continuous_id))

/-- If the data `(u, v)` give points of `belowS` for the vertical coordinate `-1` and for `t`
(with `-1 ≤ t ≤ 1` and `t` below the level of the sheet), then `belowPt u v t` lies in the
connected component of `belowS` through the bottom point `belowPt u v (-1)`.

Indeed the whole vertical segment `{belowPt u v s | s ∈ [-1, t]}` is the continuous image of the
preconnected interval `[-1, t]`, is contained in `belowS`, and contains the bottom point. -/
theorem belowPt_segment_mem_component {p m : ℕ} (Z : SemiPf (p + (m + 1)))
    (S : Stratum p (m + 1))
    (u : Fin (p + (m + 1)) → ℝ) (hu : u ∈ Z.set) (v : Fin (m + 1) → ℝ)
    (hv : Fin.append (projFirst p (m + 1) u) v ∈ S.X.set)
    (t : ℝ) (ht1 : -1 ≤ t) (ht2 : |t| ≤ 1) (ht3 : t < v (Fin.last m)) :
    belowPt u v t ∈ connectedComponentIn (belowS Z S).set (belowPt u v (-1)) := by
  have hpc : IsPreconnected (belowPt u v '' Set.Icc (-1) t) :=
    isPreconnected_Icc.image _ (continuous_belowPt_aux u v).continuousOn
  have hsub : belowPt u v '' Set.Icc (-1) t ⊆ (belowS Z S).set := by
    rintro w ⟨r, hr, rfl⟩
    obtain ⟨hr1, hr2⟩ := hr
    exact belowPt_mem Z S u hu v r hv
      (abs_le.mpr ⟨hr1, le_trans hr2 (abs_le.mp ht2).2⟩) (lt_of_le_of_lt hr2 ht3)
  have hmem : belowPt u v (-1) ∈ belowPt u v '' Set.Icc (-1) t := ⟨-1, ⟨le_rfl, ht1⟩, rfl⟩
  have hfin := hpc.subset_connectedComponentIn hmem hsub
  exact hfin ⟨t, ⟨ht1, le_rfl⟩, rfl⟩

/-! ## §2. The statement -/

theorem belowOpenComp_sub
    {p m : ℕ} (S : WilkiesDesign.E.Stratum p (m + 1))
    (Z : WilkiesDesign.E.SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ) (hu₀ : u₀ ∈ Z.set)
    (C : Set (Fin p → ℝ))
    (hC : C = Set.image (WilkiesDesign.E.projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (k : ℕ) (hk : 0 < k) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ j, ContinuousOn (s j) C)
    (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set)
    (hcov : ∀ z ∈ S.X.set, WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
      ∃ j : Fin k, s j (WilkiesDesign.E.projFirst p (m + 1) z) =
        WilkiesDesign.E.projSnd p (m + 1) z)
    (hlt : ∀ x ∈ C, -1 < (s ⟨0, hk⟩ x) (Fin.last m)) :
    Work.WilE7.BelowAux.belowExtract ''
        (connectedComponentIn (Work.WilE7.BelowAux.belowSopen Z S).set
          (Work.WilE7.BelowAux.belowPt u₀
            (s ⟨0, hk⟩ (WilkiesDesign.E.projFirst p (m + 1) u₀))
            (Work.WilE7.BelowAux.belowT0 s ⟨0, hk⟩ u₀)))
      ⊆ {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
          y (Fin.last p) < (s ⟨0, hk⟩ (Fin.init y)) (Fin.last m)} := by
  let v₀ : Fin (m + 1) → ℝ := s ⟨0, hk⟩ (projFirst p (m + 1) u₀)
  let t₀ : ℝ := belowT0 s ⟨0, hk⟩ u₀
  have hu0C : projFirst p (m + 1) u₀ ∈ C := by
    rw [hC]; exact ⟨u₀, mem_connectedComponentIn hu₀, rfl⟩
  have hhv : Fin.append (projFirst p (m + 1) u₀) v₀ ∈ S.X.set := hsub ⟨0, hk⟩ _ hu0C
  -- the level of the sheet is `≤ 1`, since `S.X.set` is contained in the cube
  have hlev : v₀ (Fin.last m) ≤ 1 := by
    have h := hhv.1 (Fin.natAdd p (Fin.last m))
    rw [Fin.append_right] at h
    exact (abs_le.mp h).2
  have hltv : -1 < v₀ (Fin.last m) := hlt _ hu0C
  have hP : belowPt u₀ v₀ (-1) ∈ (belowS Z S).set :=
    belowPt_mem Z S u₀ hu₀ v₀ (-1) hhv (by norm_num) hltv
  -- the interior point `belowT0` lies in the same (closed) component as the bottom point
  have hqmem : belowPt u₀ v₀ t₀ ∈ connectedComponentIn (belowS Z S).set (belowPt u₀ v₀ (-1)) :=
    belowPt_segment_mem_component Z S u₀ hu₀ v₀ hhv t₀ (le_of_lt (belowT0_gt hltv))
      (belowT0_abs hltv hlev) (belowT0_lt hltv)
  have hZ1c := belowComp_sub_belowZ1_image S Z u₀ v₀ (-1) hP
  intro y hy
  obtain ⟨w, hw, rfl⟩ := hy
  have hwK : w ∈ connectedComponentIn (belowS Z S).set (belowPt u₀ v₀ (-1)) := by
    have h := connectedComponentIn_mono (belowPt u₀ v₀ t₀) (belowSopen_subset Z S) hw
    rwa [← connectedComponentIn_eq hqmem] at h
  have hwB := (belowSopen_mem_iff Z S w).mp (connectedComponentIn_subset _ _ hw)
  have hwS := (belowS_mem_iff Z S w).mp hwB.1
  have hsheet := belowComp_sub_sheet_eq S Z u₀ hu₀ C hC k hk s hcont hinj hsub hcov hlt w hwK
  refine ⟨?_, ?_, ?_⟩
  · rw [belowComp_sub_Fin_init, hC]
    exact ⟨belowZ1 w, hZ1c ⟨w, hwK, rfl⟩, rfl⟩
  · rw [belowExtract_apply_last]; exact hwB.2
  · rw [belowExtract_apply_last, belowComp_sub_Fin_init, hwS.2.2.1, ← hsheet]
    exact hwS.2.2.2.2

end Work.WilE7.BelowAux
