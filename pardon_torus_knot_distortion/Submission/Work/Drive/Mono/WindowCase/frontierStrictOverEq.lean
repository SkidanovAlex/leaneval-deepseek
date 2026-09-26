import Mathlib
import Submission.Work.Drive.Mono.CylRegionDefs
import Submission.Work.Drive.Mono.WindowCase.frontier_hypograph_eq

namespace Work.Drive.Mono.WindowCase

open Set

noncomputable section

/-!
# The frontier of the cylindrical region does not see the base

`frontier {p : ℝ³ | cproj p ∈ Z ∧ α (cproj p) < clast p ∧ clast p < β (cproj p)}` is unchanged if
the open base `Z` and the strict inequalities are replaced by the closed base `K = closure Z` and
the non-strict inequalities, provided `interior K ⊆ Z` and `closure (interior K) = K`.

The two cylindrical regions are `cReg Z α β` (open base, strict) and `cCyl K α β` (closed base,
non-strict), and we prove `frontier (cReg Z α β) = frontier (cCyl K α β)` through

* `closure (cReg Z α β) = cCyl K α β` (`cCyl_isClosed` + `cCyl_subset_closure_cReg`), and
* `interior (cReg Z α β) = interior (cCyl K α β)` (`interior_cCyl_subset_cInt` +
  `cInt_subset_interior_cReg`).
-/

/-! ## Metric normal forms for `cmk` -/

/-- Distances in `ℝ³` between two points of the form `cmk x y`. -/
theorem dist_cmk_sq (x x' : EuclideanSpace ℝ (Fin 2)) (y y' : ℝ) :
    dist (Work.Drive.Mono.cmk x y) (Work.Drive.Mono.cmk x' y') ^ 2 =
      dist x x' ^ 2 + (y - y') ^ 2 := by
  rw [dist_eq_norm, dist_eq_norm, Work.Drive.Mono.cmk_sub, Work.Drive.Mono.norm_sq_cmk]

/-- The projection is `1`-Lipschitz. -/
theorem dist_cproj_le (q p : EuclideanSpace ℝ (Fin 3)) :
    dist (Work.Drive.Mono.cproj q) (Work.Drive.Mono.cproj p) ≤ dist q p := by
  rw [dist_eq_norm, dist_eq_norm, ← Work.Drive.Mono.cproj_sub]
  exact Work.Drive.Mono.norm_cproj_le (q - p)

/-- The third coordinate is `1`-Lipschitz. -/
theorem abs_clast_sub_le (q p : EuclideanSpace ℝ (Fin 3)) :
    |Work.Drive.Mono.clast q - Work.Drive.Mono.clast p| ≤ dist q p := by
  rw [dist_eq_norm, ← Work.Drive.Mono.clast_sub]
  exact Work.Drive.Mono.abs_clast_le (q - p)

/-- Distance from the point of `ℝ³` over `Y` at the height of `p` to `p`. -/
theorem dist_cmk_p (Y : EuclideanSpace ℝ (Fin 2)) (p : EuclideanSpace ℝ (Fin 3)) :
    dist (Work.Drive.Mono.cmk Y (Work.Drive.Mono.clast p)) p =
      dist Y (Work.Drive.Mono.cproj p) := by
  rw [← Work.Drive.Mono.cmk_cproj_clast p]
  simp only [Work.Drive.Mono.clast_cmk, Work.Drive.Mono.cproj_cmk, dist_cmk_same_last]

/-- Distance from a point over `cproj p` at height `y` to `p`. -/
theorem dist_cmk_cproj (y : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    dist (Work.Drive.Mono.cmk (Work.Drive.Mono.cproj p) y) p =
      |y - Work.Drive.Mono.clast p| := by
  rw [← Work.Drive.Mono.cmk_cproj_clast p]
  simp only [Work.Drive.Mono.clast_cmk, Work.Drive.Mono.cproj_cmk, dist_cmk_same_proj]

/-! ## The closed cylindrical region is closed -/

/-- The closed cylindrical region `cCyl K α β` is closed when `K` is closed and `α, β` are
continuous on `K`. -/
theorem cCyl_isClosed {K : Set (EuclideanSpace ℝ (Fin 2))} {α β : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hK : IsClosed K) (hα : ContinuousOn α K) (hβ : ContinuousOn β K) :
    IsClosed (cCyl K α β) := by
  have hS1 : IsClosed (((K ×ˢ (univ : Set ℝ)) ∩
      (fun q : EuclideanSpace ℝ (Fin 2) × ℝ => α q.1 - q.2) ⁻¹' Set.Iic (0 : ℝ))) := by
    refine ContinuousOn.preimage_isClosed_of_isClosed ?_ (hK.prod isClosed_univ) isClosed_Iic
    exact (hα.comp continuous_fst.continuousOn (fun q hq => hq.1)).sub
      continuous_snd.continuousOn
  have hS2 : IsClosed (((K ×ˢ (univ : Set ℝ)) ∩
      (fun q : EuclideanSpace ℝ (Fin 2) × ℝ => q.2 - β q.1) ⁻¹' Set.Iic (0 : ℝ))) := by
    refine ContinuousOn.preimage_isClosed_of_isClosed ?_ (hK.prod isClosed_univ) isClosed_Iic
    exact continuous_snd.continuousOn.sub
      (hβ.comp continuous_fst.continuousOn (fun q hq => hq.1))
  have hT : IsClosed ((((K ×ˢ (univ : Set ℝ)) ∩
      (fun q : EuclideanSpace ℝ (Fin 2) × ℝ => α q.1 - q.2) ⁻¹' Set.Iic (0 : ℝ))) ∩
      (((K ×ˢ (univ : Set ℝ)) ∩
      (fun q : EuclideanSpace ℝ (Fin 2) × ℝ => q.2 - β q.1) ⁻¹' Set.Iic (0 : ℝ)))) :=
    hS1.inter hS2
  have hmap : Continuous (fun p : EuclideanSpace ℝ (Fin 3) =>
      (Work.Drive.Mono.cproj p, Work.Drive.Mono.clast p)) :=
    Work.Drive.Mono.continuous_cproj.prodMk Work.Drive.Mono.continuous_clast
  have heq : cCyl K α β = (fun p : EuclideanSpace ℝ (Fin 3) =>
      (Work.Drive.Mono.cproj p, Work.Drive.Mono.clast p)) ⁻¹'
      ((((K ×ˢ (univ : Set ℝ)) ∩
      (fun q : EuclideanSpace ℝ (Fin 2) × ℝ => α q.1 - q.2) ⁻¹' Set.Iic (0 : ℝ))) ∩
      (((K ×ˢ (univ : Set ℝ)) ∩
      (fun q : EuclideanSpace ℝ (Fin 2) × ℝ => q.2 - β q.1) ⁻¹' Set.Iic (0 : ℝ)))) := by
    ext p
    simp only [cCyl, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod,
      Set.mem_univ, and_true, Set.mem_Iic, sub_nonpos]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h1, h3⟩
    · rintro ⟨⟨h1, h2⟩, _, h3⟩; exact ⟨h1, h2, h3⟩
  rw [heq]
  exact hT.preimage hmap

/-! ## The closed region is the closure of the open one -/

/-- The open region over `Z` sits in the closed region over any super-set. -/
theorem cReg_subset_cCyl {Z K : Set (EuclideanSpace ℝ (Fin 2))}
    {α β : EuclideanSpace ℝ (Fin 2) → ℝ} (hZK : Z ⊆ K) :
    cReg Z α β ⊆ cCyl K α β := by
  intro p hp
  simp only [cReg, Set.mem_ofPred_eq] at hp
  simp only [cCyl, Set.mem_ofPred_eq]
  exact ⟨hZK hp.1, le_of_lt hp.2.1, le_of_lt hp.2.2⟩

/-- **The closed region is contained in the closure of the open region.**  For `p` in `cCyl K α β`
one approximates `cproj p` by points `Y` of `interior K ⊆ Z` and the height `clast p` by a height
in the window `(α Y, β Y)`, which is non-empty because `α < β` on `interior K`. -/
theorem cCyl_subset_closure_cReg {Z K : Set (EuclideanSpace ℝ (Fin 2))}
    {α β : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hKcl : closure (interior K) = K) (hIntZ : interior K ⊆ Z)
    (hα : ContinuousOn α K) (hβ : ContinuousOn β K)
    (hlt : ∀ X ∈ interior K, α X < β X) :
    cCyl K α β ⊆ closure (cReg Z α β) := by
  intro p hp
  simp only [cCyl, Set.mem_ofPred_eq] at hp
  obtain ⟨hpK, hpα, hpβ⟩ := hp
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hε4 : 0 < ε / 4 := by linarith
  have hXc : Work.Drive.Mono.cproj p ∈ closure (interior K) := by rw [hKcl]; exact hpK
  obtain ⟨δα, hδαpos, hαδ⟩ :=
    Metric.continuousWithinAt_iff.mp (hα (Work.Drive.Mono.cproj p) hpK) (ε / 4) hε4
  obtain ⟨δβ, hδβpos, hβδ⟩ :=
    Metric.continuousWithinAt_iff.mp (hβ (Work.Drive.Mono.cproj p) hpK) (ε / 4) hε4
  obtain ⟨Y, hYint, hYX⟩ :=
    Metric.mem_closure_iff.mp hXc (min (ε / 4) (min δα δβ))
      (lt_min hε4 (lt_min hδαpos hδβpos))
  have hYXε : dist (Work.Drive.Mono.cproj p) Y < ε / 4 :=
    lt_of_lt_of_le hYX (min_le_left _ _)
  have hYX' : dist Y (Work.Drive.Mono.cproj p) < min (ε / 4) (min δα δβ) := by
    rw [dist_comm]; exact hYX
  have hYX1 : dist Y (Work.Drive.Mono.cproj p) < δα :=
    lt_of_lt_of_le hYX' (le_trans (min_le_right _ _) (min_le_left _ _))
  have hYX2 : dist Y (Work.Drive.Mono.cproj p) < δβ :=
    lt_of_lt_of_le hYX' (le_trans (min_le_right _ _) (min_le_right _ _))
  have hαY : α Y < Work.Drive.Mono.clast p + ε / 4 := by
    have h := hαδ (interior_subset hYint) hYX1
    rw [Real.dist_eq] at h
    have := (abs_lt.mp h).2
    linarith
  have hβY : Work.Drive.Mono.clast p - ε / 4 < β Y := by
    have h := hβδ (interior_subset hYint) hYX2
    rw [Real.dist_eq] at h
    have := (abs_lt.mp h).1
    linarith
  have hαβY : α Y < β Y := hlt Y hYint
  have hmlt : max (α Y) (Work.Drive.Mono.clast p - ε / 4) <
      min (β Y) (Work.Drive.Mono.clast p + ε / 4) :=
    max_lt_iff.mpr ⟨lt_min_iff.mpr ⟨hαβY, hαY⟩, lt_min_iff.mpr ⟨hβY, by linarith⟩⟩
  set w := (max (α Y) (Work.Drive.Mono.clast p - ε / 4) +
    min (β Y) (Work.Drive.Mono.clast p + ε / 4)) / 2 with hwdef
  have hwα : α Y < w := by
    rw [hwdef]
    linarith [le_max_left (α Y) (Work.Drive.Mono.clast p - ε / 4), hmlt]
  have hwβ : w < β Y := by
    rw [hwdef]
    linarith [min_le_left (β Y) (Work.Drive.Mono.clast p + ε / 4), hmlt]
  have hwz : |w - Work.Drive.Mono.clast p| < ε / 4 := by
    rw [abs_lt]
    refine ⟨?_, ?_⟩
    · rw [hwdef]
      linarith [le_max_right (α Y) (Work.Drive.Mono.clast p - ε / 4), hmlt]
    · rw [hwdef]
      linarith [min_le_right (β Y) (Work.Drive.Mono.clast p + ε / 4), hmlt]
  refine ⟨Work.Drive.Mono.cmk Y w, ?_, ?_⟩
  · simp only [cReg, Set.mem_ofPred_eq, Work.Drive.Mono.cproj_cmk, Work.Drive.Mono.clast_cmk]
    exact ⟨hIntZ hYint, hwα, hwβ⟩
  · rw [← Work.Drive.Mono.cmk_cproj_clast p]
    have h1 : dist (Work.Drive.Mono.cproj p) Y ^ 2 < (ε / 4) ^ 2 :=
      sq_lt_sq.mpr (show |dist (Work.Drive.Mono.cproj p) Y| < |ε / 4| by
        rw [abs_of_nonneg (dist_nonneg :
            (0 : ℝ) ≤ dist (Work.Drive.Mono.cproj p) Y), abs_of_nonneg (le_of_lt hε4)]
        exact hYXε)
    have h2 : (Work.Drive.Mono.clast p - w) ^ 2 < (ε / 4) ^ 2 :=
      sq_lt_sq.mpr (show |Work.Drive.Mono.clast p - w| < |ε / 4| by
        rw [abs_of_nonneg (le_of_lt hε4)]
        rwa [abs_sub_comm] at hwz)
    have hd2 : dist (Work.Drive.Mono.cmk (Work.Drive.Mono.cproj p) (Work.Drive.Mono.clast p))
        (Work.Drive.Mono.cmk Y w) ^ 2 < ε ^ 2 := by
      rw [dist_cmk_sq]
      nlinarith [h1, h2, hε]
    have hfin := sq_lt_sq.mp hd2
    rw [abs_of_nonneg (dist_nonneg :
        (0 : ℝ) ≤ dist (Work.Drive.Mono.cmk (Work.Drive.Mono.cproj p) (Work.Drive.Mono.clast p))
          (Work.Drive.Mono.cmk Y w)), abs_of_nonneg (le_of_lt hε)] at hfin
    exact hfin

/-! ## Interiors -/

/-- The interior of the closed region lies over the interior of the base, between the two strict
graphs. -/
theorem interior_cCyl_subset_cInt {K : Set (EuclideanSpace ℝ (Fin 2))}
    {α β : EuclideanSpace ℝ (Fin 2) → ℝ} :
    interior (cCyl K α β) ⊆ cInt K α β := by
  intro p hp
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hp
  obtain ⟨δ, hδpos, hball⟩ := hp
  have hpCyl : p ∈ cCyl K α β := hball (Metric.mem_ball_self hδpos)
  simp only [cCyl, Set.mem_ofPred_eq] at hpCyl
  obtain ⟨hpK, hpα, hpβ⟩ := hpCyl
  simp only [cInt, Set.mem_ofPred_eq]
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
    refine ⟨δ, hδpos, fun Y hY => ?_⟩
    have hq : Work.Drive.Mono.cmk Y (Work.Drive.Mono.clast p) ∈ Metric.ball p δ := by
      rw [Metric.mem_ball, dist_cmk_p]
      exact Metric.mem_ball.mp hY
    have hq' := hball hq
    simp only [cCyl, Set.mem_ofPred_eq, Work.Drive.Mono.cproj_cmk] at hq'
    exact hq'.1
  · by_contra h
    rw [not_lt] at h
    have heq : α (Work.Drive.Mono.cproj p) = Work.Drive.Mono.clast p := le_antisymm hpα h
    have hq : Work.Drive.Mono.cmk (Work.Drive.Mono.cproj p) (Work.Drive.Mono.clast p - δ / 2) ∈
        Metric.ball p δ := by
      rw [Metric.mem_ball, dist_cmk_cproj, abs_lt]
      constructor <;> linarith
    have hq' := hball hq
    simp only [cCyl, Set.mem_ofPred_eq, Work.Drive.Mono.cproj_cmk, Work.Drive.Mono.clast_cmk]
      at hq'
    linarith [hq'.2.1, heq]
  · by_contra h
    rw [not_lt] at h
    have heq : β (Work.Drive.Mono.cproj p) = Work.Drive.Mono.clast p := le_antisymm h hpβ
    have hq : Work.Drive.Mono.cmk (Work.Drive.Mono.cproj p) (Work.Drive.Mono.clast p + δ / 2) ∈
        Metric.ball p δ := by
      rw [Metric.mem_ball, dist_cmk_cproj, abs_lt]
      constructor <;> linarith
    have hq' := hball hq
    simp only [cCyl, Set.mem_ofPred_eq, Work.Drive.Mono.cproj_cmk, Work.Drive.Mono.clast_cmk]
      at hq'
    linarith [hq'.2.2, heq]

/-- A point of the strict region over `interior K` is an interior point of the strict region over
`Z`, when `interior K ⊆ Z`. -/
theorem cInt_subset_interior_cReg {Z K : Set (EuclideanSpace ℝ (Fin 2))}
    {α β : EuclideanSpace ℝ (Fin 2) → ℝ} (hIntZ : interior K ⊆ Z)
    (hα : ContinuousOn α K) (hβ : ContinuousOn β K) :
    cInt K α β ⊆ interior (cReg Z α β) := by
  intro p hp
  simp only [cInt, Set.mem_ofPred_eq] at hp
  obtain ⟨hpKi, hpα, hpβ⟩ := hp
  have hpK : Work.Drive.Mono.cproj p ∈ K := interior_subset hpKi
  set eα := (Work.Drive.Mono.clast p - α (Work.Drive.Mono.cproj p)) / 2 with heα
  have heαpos : 0 < eα := by rw [heα]; linarith
  set eβ := (β (Work.Drive.Mono.cproj p) - Work.Drive.Mono.clast p) / 2 with heβ
  have heβpos : 0 < eβ := by rw [heβ]; linarith
  obtain ⟨δ1, hδ1pos, hδ1⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hpKi)
  obtain ⟨δα, hδαpos, hαδ⟩ :=
    Metric.continuousWithinAt_iff.mp (hα (Work.Drive.Mono.cproj p) hpK) eα heαpos
  obtain ⟨δβ, hδβpos, hβδ⟩ :=
    Metric.continuousWithinAt_iff.mp (hβ (Work.Drive.Mono.cproj p) hpK) eβ heβpos
  set η := min δ1 (min δα (min δβ (min eα eβ))) with hη
  have hηpos : 0 < η :=
    lt_min hδ1pos (lt_min hδαpos (lt_min hδβpos (lt_min heαpos heβpos)))
  have hsub : Metric.ball p η ⊆ cReg Z α β := by
    intro q hq
    rw [Metric.mem_ball] at hq
    rw [hη] at hq
    simp only [lt_min_iff] at hq
    obtain ⟨hd1, hdα, hdβ, hdeα, hdeβ⟩ := hq
    have hqKi : Work.Drive.Mono.cproj q ∈ interior K :=
      hδ1 (Metric.mem_ball.mpr (lt_of_le_of_lt (dist_cproj_le q p) hd1))
    have hdqα : dist (Work.Drive.Mono.cproj q) (Work.Drive.Mono.cproj p) < δα :=
      lt_of_le_of_lt (dist_cproj_le q p) hdα
    have hαq := hαδ (interior_subset hqKi) hdqα
    rw [Real.dist_eq] at hαq
    have hαq' : α (Work.Drive.Mono.cproj q) < α (Work.Drive.Mono.cproj p) + eα := by
      have := (abs_lt.mp hαq).2; linarith
    have hlastα : |Work.Drive.Mono.clast q - Work.Drive.Mono.clast p| < eα :=
      lt_of_le_of_lt (abs_clast_sub_le q p) hdeα
    have hlastα' : Work.Drive.Mono.clast p - eα < Work.Drive.Mono.clast q := by
      have := (abs_lt.mp hlastα).1; linarith
    have hsumα : α (Work.Drive.Mono.cproj p) + eα = Work.Drive.Mono.clast p - eα := by
      rw [heα]; ring
    have hlt1 : α (Work.Drive.Mono.cproj q) < Work.Drive.Mono.clast q := by
      linarith [hαq', hlastα', hsumα]
    have hdqβ : dist (Work.Drive.Mono.cproj q) (Work.Drive.Mono.cproj p) < δβ :=
      lt_of_le_of_lt (dist_cproj_le q p) hdβ
    have hβq := hβδ (interior_subset hqKi) hdqβ
    rw [Real.dist_eq] at hβq
    have hβq' : β (Work.Drive.Mono.cproj p) - eβ < β (Work.Drive.Mono.cproj q) := by
      have := (abs_lt.mp hβq).1; linarith
    have hlastβ : |Work.Drive.Mono.clast q - Work.Drive.Mono.clast p| < eβ :=
      lt_of_le_of_lt (abs_clast_sub_le q p) hdeβ
    have hlastβ' : Work.Drive.Mono.clast q < Work.Drive.Mono.clast p + eβ := by
      have := (abs_lt.mp hlastβ).2; linarith
    have hsumβ : β (Work.Drive.Mono.cproj p) - eβ = Work.Drive.Mono.clast p + eβ := by
      rw [heβ]; ring
    have hlt2 : Work.Drive.Mono.clast q < β (Work.Drive.Mono.cproj q) := by
      linarith [hβq', hlastβ', hsumβ]
    simp only [cReg, Set.mem_ofPred_eq]
    exact ⟨hIntZ hqKi, hlt1, hlt2⟩
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  exact ⟨η, hηpos, hsub⟩

/-! ## The main result -/

/-- **The frontier of the solid over `closure Z` is the frontier of the solid over `Z`.**  If
`Z ⊆ K := closure Z` contains the interior of `K` (so `Z` is dense in `K` and `interior K` is dense
in `K`), and `α ≤ β` are continuous on `K` with `α < β` on the interior, then replacing the open base
`Z` and the strict inequalities by the closed base `K` and the non-strict inequalities does not change
the frontier. -/
theorem frontierStrictOverEq
    {Z K : Set (EuclideanSpace ℝ (Fin 2))} (hZ : closure Z = K) (hIntZ : interior K ⊆ Z)
    (hKcl : closure (interior K) = K)
    {α β : EuclideanSpace ℝ (Fin 2) → ℝ} (hα : ContinuousOn α K) (hβ : ContinuousOn β K)
    (hαβ : ∀ X ∈ K, α X ≤ β X) (hlt : ∀ X ∈ interior K, α X < β X) :
    frontier {p : EuclideanSpace ℝ (Fin 3) |
        Work.Drive.Mono.cproj p ∈ Z ∧ α (Work.Drive.Mono.cproj p) < Work.Drive.Mono.clast p ∧
        Work.Drive.Mono.clast p < β (Work.Drive.Mono.cproj p)} =
      frontier {p : EuclideanSpace ℝ (Fin 3) |
        Work.Drive.Mono.cproj p ∈ K ∧ α (Work.Drive.Mono.cproj p) ≤ Work.Drive.Mono.clast p ∧
        Work.Drive.Mono.clast p ≤ β (Work.Drive.Mono.cproj p)} := by
  show frontier (cReg Z α β) = frontier (cCyl K α β)
  have hZK : Z ⊆ K := by rw [← hZ]; exact subset_closure
  have hKclosed : IsClosed K := by rw [← hZ]; exact isClosed_closure
  have hBclosed : IsClosed (cCyl K α β) := cCyl_isClosed hKclosed hα hβ
  have hcl : closure (cReg Z α β) = cCyl K α β :=
    le_antisymm (closure_minimal (cReg_subset_cCyl hZK) hBclosed)
      (cCyl_subset_closure_cReg hKcl hIntZ hα hβ hlt)
  have hint : interior (cReg Z α β) = interior (cCyl K α β) :=
    le_antisymm (interior_mono (cReg_subset_cCyl hZK))
      ((interior_cCyl_subset_cInt).trans (cInt_subset_interior_cReg hIntZ hα hβ))
  rw [frontier, hcl, hint, frontier, hBclosed.closure_eq]

end

end Work.Drive.Mono.WindowCase
