import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Submission.Lib.Unif2.Commons.Topology.Plane.convex_retract

namespace Commons.Topology.Plane

/-- A set `S ⊆ ℂ` is a retract of `ℂ` (with the strong pointwise-fixing property). -/
def IsRetract (S : Set ℂ) : Prop := ∃ r : C(ℂ, ↥S), ∀ x : ↥S, r (x : ℂ) = x

/-- A finite `accumulate` of closed sets is closed. -/
lemma isClosed_accumulate {A : ℕ → Set ℂ} (hA : ∀ k, IsClosed (A k)) :
    ∀ n, IsClosed (Set.accumulate A n) := by
  intro n
  induction n with
  | zero => simpa using hA 0
  | succ m ih => rw [Set.accumulate_succ]; exact ih.union (hA (m + 1))

/-- Continuity of `z ↦ Φ (z, s z)` when `Φ` is continuous and collapses the fibre
`{x} × [0,1]` to the point `x` and `s` is `[0,1]`-valued. -/
lemma continuousAt_comp_of_fiber {Φ : ℂ × ℝ → ℂ} (hΦ : Continuous Φ) {x : ℂ} {s : ℂ → ℝ}
    (hs : ∀ z, s z ∈ Set.Icc (0 : ℝ) 1) (hx : ∀ t ∈ Set.Icc (0 : ℝ) 1, Φ (x, t) = x) :
    ContinuousAt (fun z => Φ (z, s z)) x := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  have huncurry : (Function.uncurry fun z t => Φ (z, t)) = Φ := by
    funext p; rfl
  have hf : ContinuousOn (Function.uncurry fun z t => Φ (z, t))
      (Set.univ ×ˢ Set.Icc (0 : ℝ) 1) := by
    rw [huncurry]
    exact hΦ.continuousOn.mono (Set.subset_univ _)
  obtain ⟨v, hv, hvu⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).mem_uniformity_of_prod
    (f := fun z t => Φ (z, t)) hf (Set.mem_univ x) (Metric.dist_mem_uniformity hε)
  rw [nhdsWithin_univ] at hv
  obtain ⟨δ, hδ, hδv⟩ := Metric.mem_nhds_iff.mp hv
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have hyv : y ∈ v := hδv (by simpa [Metric.mem_ball] using hy)
  have hu := hvu y hyv (s y) (hs y)
  have hu' : dist (Φ (y, s y)) x < ε := by
    simpa [hx (s y) (hs y)] using hu
  simpa [hx (s x) (hs x)] using hu'

/-- If `X ⊆ ℂ` is closed and a retract of `ℂ`, and `Y` is closed, convex and nonempty with
`X ∩ Y` nonempty and convex, then `X ∪ Y` is a retract of `ℂ`. -/
theorem union_retract {X Y : Set ℂ} (hX : IsClosed X) (hYc : IsClosed Y) (hYne : Y.Nonempty)
    (hYcv : Convex ℝ Y) (hCne : (X ∩ Y).Nonempty) (hCcv : Convex ℝ (X ∩ Y))
    {R : C(ℂ, ↥X)} (hR : ∀ x : ↥X, R (x : ℂ) = x) : IsRetract (X ∪ Y) := by
  classical
  by_cases hXY : X ⊆ Y
  · rw [Set.union_eq_right.mpr hXY]
    exact convex_retract hYcv hYc hYne
  by_cases hYX : Y ⊆ X
  · rw [Set.union_eq_left.mpr hYX]
    exact ⟨R, hR⟩
  let C : Set ℂ := X ∩ Y
  have hCc : IsClosed C := hX.inter hYc
  have hCcv' : Convex ℝ C := hCcv
  have hCne' : C.Nonempty := hCne
  obtain ⟨pY, hpY⟩ := convex_retract hYcv hYc hYne
  obtain ⟨pC, hpC⟩ := convex_retract hCcv' hCc hCne'
  have hXmC : X \ C = X \ Y := by
    ext z; simp only [C, Set.mem_sdiff, Set.mem_inter_iff]; tauto
  have hYmC : Y \ C = Y \ X := by
    ext z; simp only [C, Set.mem_sdiff, Set.mem_inter_iff]; tauto
  have hXmCne : (X \ C).Nonempty := by
    rw [hXmC]; obtain ⟨a, ha1, ha2⟩ := Set.not_subset.mp hXY; exact ⟨a, ha1, ha2⟩
  have hYmCne : (Y \ C).Nonempty := by
    rw [hYmC]; obtain ⟨a, ha1, ha2⟩ := Set.not_subset.mp hYX; exact ⟨a, ha1, ha2⟩
  let dX : ℂ → ℝ := fun z => Metric.infDist z (X \ C)
  let dY : ℂ → ℝ := fun z => Metric.infDist z (Y \ C)
  have hdXc : Continuous dX := by rw [show dX = fun z => Metric.infDist z (X \ C) from rfl]; exact Metric.continuous_infDist_pt _
  have hdYc : Continuous dY := by rw [show dY = fun z => Metric.infDist z (Y \ C) from rfl]; exact Metric.continuous_infDist_pt _
  have hdXnn : ∀ z, 0 ≤ dX z := fun _ => Metric.infDist_nonneg
  have hdYnn : ∀ z, 0 ≤ dY z := fun _ => Metric.infDist_nonneg
  have hden : ∀ z ∈ Cᶜ, 0 < dX z + dY z := by
    intro z hz
    rcases lt_trichotomy (dX z + dY z) 0 with h | h | h
    · exfalso; linarith [hdXnn z, hdYnn z]
    · exfalso
      have hdX0 : dX z = 0 := le_antisymm (by linarith [hdXnn z, hdYnn z]) (hdXnn z)
      have hdY0 : dY z = 0 := le_antisymm (by linarith [hdXnn z, hdYnn z]) (hdYnn z)
      have hzXcl : z ∈ closure (X \ C) := (Metric.mem_closure_iff_infDist_zero hXmCne).mpr hdX0
      have hzYcl : z ∈ closure (Y \ C) := (Metric.mem_closure_iff_infDist_zero hYmCne).mpr hdY0
      have hzX : z ∈ X := ((closure_mono Set.sdiff_subset).trans (le_of_eq hX.closure_eq)) hzXcl
      have hzY : z ∈ Y := ((closure_mono Set.sdiff_subset).trans (le_of_eq hYc.closure_eq)) hzYcl
      exact hz ⟨hzX, hzY⟩
    · exact h
  let s : ℂ → ℝ := fun z => if z ∈ C then 0 else dX z / (dX z + dY z)
  have hs_mem : ∀ z, s z ∈ Set.Icc (0 : ℝ) 1 := by
    intro z
    by_cases hz : z ∈ C
    · simp [s, hz]
    · simp only [s, hz, if_false]
      refine ⟨div_nonneg (hdXnn z) (le_of_lt (hden z hz)), ?_⟩
      rw [div_le_one (hden z hz)]
      linarith [hdYnn z]
  have hs0 : ∀ z ∈ X \ C, s z = 0 := by
    intro z hz
    have hzC : z ∉ C := hz.2
    have hdX0 : dX z = 0 := Metric.infDist_zero_of_mem hz
    simp only [s, hzC, if_false]
    rw [hdX0]; simp
  have hs1 : ∀ z ∈ Y \ C, s z = 1 := by
    intro z hz
    have hzC : z ∉ C := hz.2
    simp only [s, hzC, if_false]
    have hdY0 : dY z = 0 := Metric.infDist_zero_of_mem hz
    have hdXpos : 0 < dX z :=
      (Metric.infDist_pos_iff_notMem_closure hXmCne).mp (by
        intro hzcl
        have hzX : z ∈ X := ((closure_mono Set.sdiff_subset).trans (le_of_eq hX.closure_eq)) hzcl
        exact hzC ⟨hzX, hz.1⟩)
    rw [hdY0, add_zero, div_self (ne_of_gt hdXpos)]
  have hs_contAt : ∀ z ∉ C, ContinuousAt s z := by
    intro z hz
    have hden' : dX z + dY z ≠ 0 := ne_of_gt (hden z hz)
    have hcont : ContinuousAt (fun w => dX w / (dX w + dY w)) z :=
      hdXc.continuousAt.div (hdXc.add hdYc).continuousAt hden'
    refine hcont.congr ?_
    filter_upwards [hCc.isOpen_compl.mem_nhds hz] with w hw
    have hw' : w ∉ C := by simpa using hw
    simp [s, hw']
  let Φ : ℂ × ℝ → ℂ := fun q =>
    if q.2 ≤ 1/2 then (R ((1 - 2 * q.2) • q.1 + (2 * q.2) • (pC q.1 : ℂ)) : ℂ)
    else (2 - 2 * q.2) • (pC q.1 : ℂ) + (2 * q.2 - 1) • (pY q.1 : ℂ)
  have hpc_fix : ∀ z ∈ C, (pC z : ℂ) = z := by
    intro z hz
    simpa using congrArg (fun y : ↥C => (y : ℂ)) (hpC ⟨z, hz⟩)
  have hpy_fix : ∀ z ∈ Y, (pY z : ℂ) = z := by
    intro z hz
    simpa using congrArg (fun y : ↥Y => (y : ℂ)) (hpY ⟨z, hz⟩)
  have hR_fix : ∀ z ∈ X, (R z : ℂ) = z := by
    intro z hz
    simpa using congrArg (fun y : ↥X => (y : ℂ)) (hR ⟨z, hz⟩)
  have hΦ_cont : Continuous Φ := by
    rw [show Φ = fun q : ℂ × ℝ =>
        if q.2 ≤ 1/2 then (R ((1 - 2 * q.2) • q.1 + (2 * q.2) • (pC q.1 : ℂ)) : ℂ)
        else (2 - 2 * q.2) • (pC q.1 : ℂ) + (2 * q.2 - 1) • (pY q.1 : ℂ) from rfl]
    apply Continuous.if_le
    · exact continuous_subtype_val.comp (R.continuous.comp (by fun_prop))
    · fun_prop
    · fun_prop
    · fun_prop
    · intro q hq
      have harg : (1 - 2 * q.2) • q.1 + (2 * q.2) • (pC q.1 : ℂ) = (pC q.1 : ℂ) := by
        rw [hq, show (2 : ℝ) * (1/2) = 1 by norm_num, show (1 : ℝ) - 1 = 0 by norm_num,
          zero_smul, one_smul, zero_add]
      rw [harg, hR_fix _ (pC q.1).2.1, hq]
      norm_num
  have hΦ0 : ∀ z, Φ (z, 0) = (R z : ℂ) := by
    intro z
    show (if (0 : ℝ) ≤ 1/2 then (R ((1 - 2 * (0:ℝ)) • z + (2 * (0:ℝ)) • (pC z : ℂ)) : ℂ)
      else (2 - 2 * (0:ℝ)) • (pC z : ℂ) + (2 * (0:ℝ) - 1) • (pY z : ℂ)) = (R z : ℂ)
    rw [if_pos (by norm_num)]
    congr 1
    simp
  have hΦ1 : ∀ z, Φ (z, 1) = (pY z : ℂ) := by
    intro z
    show (if (1 : ℝ) ≤ 1/2 then (R ((1 - 2 * (1:ℝ)) • z + (2 * (1:ℝ)) • (pC z : ℂ)) : ℂ)
      else (2 - 2 * (1:ℝ)) • (pC z : ℂ) + (2 * (1:ℝ) - 1) • (pY z : ℂ)) = (pY z : ℂ)
    rw [if_neg (by norm_num)]
    norm_num
  have hΦC : ∀ z ∈ C, ∀ t ∈ Set.Icc (0 : ℝ) 1, Φ (z, t) = z := by
    intro z hz t ht
    have hpc := hpc_fix z hz
    have hpy := hpy_fix z hz.2
    have hRz := hR_fix z hz.1
    by_cases hle : t ≤ 1/2
    · show (if t ≤ 1/2 then (R ((1 - 2 * t) • z + (2 * t) • (pC z : ℂ)) : ℂ) else _) = z
      rw [if_pos hle, hpc]
      have : (1 - 2 * t) • z + (2 * t) • z = z := by
        rw [← add_smul, show (1 : ℝ) - 2 * t + 2 * t = 1 by ring, one_smul]
      rw [this, hRz]
    · show (if t ≤ 1/2 then _ else (2 - 2 * t) • (pC z : ℂ) + (2 * t - 1) • (pY z : ℂ)) = z
      rw [if_neg hle, hpc, hpy]
      have : (2 - 2 * t) • z + (2 * t - 1) • z = z := by
        rw [← add_smul, show (2 : ℝ) - 2 * t + (2 * t - 1) = 1 by ring, one_smul]
      rw [this]
  let r : ℂ → ℂ := fun z => Φ (z, s z)
  have hr_mem : ∀ z, r z ∈ X ∪ Y := by
    intro z
    by_cases hz : z ∈ C
    · have hs : s z = 0 := by simp [s, hz]
      rw [show r z = Φ (z, 0) from by simp [r, hs], hΦ0 z]
      exact Or.inl (R z).2
    · by_cases hle : s z ≤ 1/2
      · have hΦz : Φ (z, s z) =
            (R ((1 - 2 * s z) • z + (2 * s z) • (pC z : ℂ)) : ℂ) := by
          show (if s z ≤ 1/2 then _ else _) = _
          rw [if_pos hle]
        change Φ (z, s z) ∈ X ∪ Y
        rw [hΦz]
        exact Or.inl (R _).2
      · have hΦz : Φ (z, s z) =
            (2 - 2 * s z) • (pC z : ℂ) + (2 * s z - 1) • (pY z : ℂ) := by
          show (if s z ≤ 1/2 then _ else _) = _
          rw [if_neg hle]
        change Φ (z, s z) ∈ X ∪ Y
        rw [hΦz]
        refine Or.inr (hYcv (pC z).2.2 (pY z).2 ?_ ?_ ?_)
        · have := (hs_mem z).2; linarith
        · have := (hs_mem z).1; linarith
        · ring
  have hrX : ∀ z ∈ X, r z = z := by
    intro z hzX
    by_cases hz : z ∈ C
    · have hs : s z = 0 := by simp [s, hz]
      rw [show r z = Φ (z, 0) from by simp [r, hs], hΦ0 z]
      exact hR_fix z hzX
    · have hs : s z = 0 := hs0 z ⟨hzX, hz⟩
      rw [show r z = Φ (z, 0) from by simp [r, hs], hΦ0 z]
      exact hR_fix z hzX
  have hrY : ∀ z ∈ Y, r z = z := by
    intro z hzY
    by_cases hz : z ∈ C
    · have hs : s z = 0 := by simp [s, hz]
      rw [show r z = Φ (z, 0) from by simp [r, hs], hΦ0 z]
      exact hR_fix z hz.1
    · have hs : s z = 1 := hs1 z ⟨hzY, hz⟩
      rw [show r z = Φ (z, 1) from by simp [r, hs], hΦ1 z]
      exact hpy_fix z hzY
  have hr_cont : Continuous r := by
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : z ∈ C
    · exact continuousAt_comp_of_fiber hΦ_cont hs_mem (hΦC z hz)
    · have hpair : ContinuousAt (fun w : ℂ => (w, s w)) z :=
        ContinuousAt.prodMk continuousAt_id (hs_contAt z hz)
      have hcomp := hΦ_cont.continuousAt.comp hpair
      exact hcomp
  refine ⟨⟨fun z => ⟨r z, hr_mem z⟩, ?_⟩, ?_⟩
  · exact hr_cont.subtype_mk hr_mem
  · intro x
    refine Subtype.ext ?_
    rcases x.2 with h | h
    · exact hrX x h
    · exact hrY x h

/-- Every finite `accumulate` of a chain of closed convex sets whose successive overlaps
`accumulate A k ∩ A (k+1)` are convex is a retract of `ℂ`. -/
theorem convex_tree_retract {A : ℕ → Set ℂ} (N : ℕ)
    (hconv : ∀ k, Convex ℝ (A k)) (hcl : ∀ k, IsClosed (A k))
    (hAkne : ∀ k, (A k).Nonempty)
    (hint : ∀ k, k + 1 < N → Convex ℝ (Set.accumulate A k ∩ A (k + 1)))
    (hne : ∀ k, k + 1 < N → (Set.accumulate A k ∩ A (k + 1)).Nonempty) :
    ∀ n, n < N → ∃ r : C(ℂ, ↥(Set.accumulate A n)),
      ∀ x : ↥(Set.accumulate A n), r (x : ℂ) = x := by
  have key : ∀ n, n < N → IsRetract (Set.accumulate A n) := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [Set.accumulate_zero_nat]
      exact convex_retract (hconv 0) (hcl 0) (hAkne 0)
    | succ m ih =>
      intro hm
      have hm' : m < N := by omega
      obtain ⟨R, hR⟩ := ih hm'
      have h := union_retract (isClosed_accumulate hcl m) (hcl (m + 1)) (hAkne (m + 1))
        (hconv (m + 1)) (hne m hm) (hint m hm) (R := R) hR
      rw [Set.accumulate_succ]
      exact h
  intro n hn
  exact key n hn

end Commons.Topology.Plane