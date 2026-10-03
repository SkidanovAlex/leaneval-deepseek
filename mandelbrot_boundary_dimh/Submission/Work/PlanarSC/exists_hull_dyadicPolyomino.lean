import Mathlib
import Submission.Work.PlanarSC.HullDefs
import Submission.Lib.Unif2.Commons.Topology.Jordan.frontier_connectedComponentIn_subset
import Submission.Lib.Unif2.Commons.Topology.Jordan.compl_compact_unique_unbounded
import Submission.Lib.Unif2.Commons.Topology.Plane.maxCell_interior_disjoint
import Submission.Lib.Unif2.Commons.Topology.Plane.exists_homotopyEquiv_subgraph_oneDimCW_of_dyadic_subcomplex
import Submission.Lib.Unif2.Commons.Topology.Connected.isPreconnected_compl_closedBall

/-!
# The "hull" of a compact set is a holed-free polyomino

For a compact `K` contained in an open `U` with no bounded complementary component, we produce a
finite union of dyadic squares containing `K`, contained in `U`, preconnected, and with
preconnected complement.  The construction is: cover `K` by the cells of a dyadic exhaustion, then
fill in the holes (`compHull`).

The file is self-contained: it proves the small chapter of plane topology it needs.
-/

open Set Metric
open scoped Topology
open Commons.Topology.Plane (dSq dInt dyadicCell)

namespace Work.PlanarSC

/-! ## Geometry of one dyadic cell -/

theorem hull_convex_dSq (n : ℕ) (p : ℤ × ℤ) : Convex ℝ (dSq n p) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨h1, h2, h3, h4⟩ := hx
  obtain ⟨g1, g2, g3, g4⟩ := hy
  have hre : (a • x + b • y).re = a * x.re + b * y.re := by
    simp [Complex.add_re, Complex.smul_re, smul_eq_mul]
  have him : (a • x + b • y).im = a * x.im + b * y.im := by
    simp [Complex.add_im, Complex.smul_im, smul_eq_mul]
  have key : ∀ (A X Y : ℝ), A ≤ X → A ≤ Y → a * A + b * A = A →
      A ≤ a * X + b * Y := by
    intro A X Y hX hY hsum
    have h1 : a * A ≤ a * X := mul_le_mul_of_nonneg_left hX ha
    have h2 : b * A ≤ b * Y := mul_le_mul_of_nonneg_left hY hb
    linarith
  have key' : ∀ (A X Y : ℝ), X ≤ A → Y ≤ A → a * A + b * A = A →
      a * X + b * Y ≤ A := by
    intro A X Y hX hY hsum
    have h1 : a * X ≤ a * A := mul_le_mul_of_nonneg_left hX ha
    have h2 : b * Y ≤ b * A := mul_le_mul_of_nonneg_left hY hb
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hre]
    exact key _ _ _ h1 g1 (by rw [← add_mul, hab, one_mul])
  · rw [hre]
    exact key' _ _ _ h2 g2 (by rw [← add_mul, hab, one_mul])
  · rw [him]
    exact key _ _ _ h3 g3 (by rw [← add_mul, hab, one_mul])
  · rw [him]
    exact key' _ _ _ h4 g4 (by rw [← add_mul, hab, one_mul])

theorem hull_isOpen_dInt (n : ℕ) (p : ℤ × ℤ) : IsOpen (dInt n p) := by
  have h : dInt n p =
      ({z : ℂ | (p.1 : ℝ) / 2 ^ n < z.re} ∩ {z : ℂ | z.re < ((p.1 : ℝ) + 1) / 2 ^ n}) ∩
      ({z : ℂ | (p.2 : ℝ) / 2 ^ n < z.im} ∩ {z : ℂ | z.im < ((p.2 : ℝ) + 1) / 2 ^ n}) := by
    ext z
    simp only [dInt, Set.mem_ofPred_eq, mem_inter_iff]
    tauto
  rw [h]
  refine IsOpen.inter (IsOpen.inter ?_ ?_) (IsOpen.inter ?_ ?_)
  · exact isOpen_lt continuous_const Complex.continuous_re
  · exact isOpen_lt Complex.continuous_re continuous_const
  · exact isOpen_lt continuous_const Complex.continuous_im
  · exact isOpen_lt Complex.continuous_im continuous_const

theorem hull_dInt_nonempty (n : ℕ) (p : ℤ × ℤ) : (dInt n p).Nonempty := by
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  refine ⟨⟨((p.1 : ℝ) + 1 / 2) / 2 ^ n, ((p.2 : ℝ) + 1 / 2) / 2 ^ n⟩, ?_, ?_, ?_, ?_⟩
  · show (p.1 : ℝ) / 2 ^ n < ((p.1 : ℝ) + 1 / 2) / 2 ^ n
    rw [div_lt_div_iff_of_pos_right h2n]; linarith
  · show ((p.1 : ℝ) + 1 / 2) / 2 ^ n < ((p.1 : ℝ) + 1) / 2 ^ n
    rw [div_lt_div_iff_of_pos_right h2n]; linarith
  · show (p.2 : ℝ) / 2 ^ n < ((p.2 : ℝ) + 1 / 2) / 2 ^ n
    rw [div_lt_div_iff_of_pos_right h2n]; linarith
  · show ((p.2 : ℝ) + 1 / 2) / 2 ^ n < ((p.2 : ℝ) + 1) / 2 ^ n
    rw [div_lt_div_iff_of_pos_right h2n]; linarith

theorem hull_dInt_subset_interior_dSq (n : ℕ) (p : ℤ × ℤ) : dInt n p ⊆ interior (dSq n p) :=
  interior_maximal (fun z hz => by
    obtain ⟨h1, h2, h3, h4⟩ := hz
    exact ⟨h1.le, h2.le, h3.le, h4.le⟩) (hull_isOpen_dInt n p)

theorem hull_interior_dSq_nonempty (n : ℕ) (p : ℤ × ℤ) : (interior (dSq n p)).Nonempty :=
  (hull_dInt_nonempty n p).mono (hull_dInt_subset_interior_dSq n p)

theorem hull_closure_interior_dSq (n : ℕ) (p : ℤ × ℤ) : closure (interior (dSq n p)) = dSq n p := by
  rw [Convex.closure_interior_eq_closure_of_nonempty_interior (hull_convex_dSq n p)
      (hull_interior_dSq_nonempty n p),
    IsClosed.closure_eq (Commons.Topology.Plane.isClosed_dSq n p)]

theorem hull_dSq_subset_closure_interior (n : ℕ) (p : ℤ × ℤ) :
    dSq n p ⊆ closure (interior (dSq n p)) := by
  rw [hull_closure_interior_dSq n p]

theorem hull_isPreconnected_interior_dSq (n : ℕ) (p : ℤ × ℤ) :
    IsPreconnected (interior (dSq n p)) :=
  (hull_convex_dSq n p).interior.isPreconnected

/-! ## The hull of a polyomino -/

theorem hull_isClosed_dyadicPolyomino (n : ℕ) (S : Finset (ℤ × ℤ)) :
    IsClosed (dyadicPolyomino n S) := by
  rw [dyadicPolyomino]
  exact isClosed_biUnion_finset (fun p _ => Commons.Topology.Plane.isClosed_dSq n p)

theorem hull_isClosed_compHull {A : Set ℂ} (hA : IsClosed A) : IsClosed (compHull A) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  rw [compl_compHull] at hx
  simp only [Set.mem_ofPred_eq] at hx
  have hxU : x ∈ Aᶜ := by
    by_contra h
    rw [connectedComponentIn_eq_empty h] at hx
    exact hx Bornology.isBounded_empty
  have hsub : connectedComponentIn Aᶜ x ⊆ (compHull A)ᶜ := by
    intro y hy
    rw [compl_compHull]
    change ¬ Bornology.IsBounded (connectedComponentIn Aᶜ y)
    rw [← connectedComponentIn_eq hy]
    exact hx
  exact Filter.mem_of_superset
    ((hA.isOpen_compl.connectedComponentIn (x := x)).mem_nhds (mem_connectedComponentIn hxU))
    hsub

theorem hull_interior_dSq_inter_polyomino {n : ℕ} {S : Finset (ℤ × ℤ)} {p : ℤ × ℤ}
    (hp : p ∉ S) : interior (dSq n p) ∩ dyadicPolyomino n S = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro z ⟨hzi, hzA⟩
  obtain ⟨q, hq, hzq⟩ := mem_dyadicPolyomino.mp hzA
  have hqp : p = q := Commons.Topology.Plane.eq_of_mem_interior_of_mem_cell hzi hzq
  rw [← hqp] at hq
  exact hp hq

theorem hull_dSq_subset_compHull_of_mem_interior {n : ℕ} {S : Finset (ℤ × ℤ)} {p : ℤ × ℤ}
    {y : ℂ} (hy : y ∈ compHull (dyadicPolyomino n S)) (hyi : y ∈ interior (dSq n p)) :
    dSq n p ⊆ compHull (dyadicPolyomino n S) := by
  by_cases hp : p ∈ S
  · intro w hw
    exact subset_compHull (mem_dyadicPolyomino.mpr ⟨p, hp, hw⟩)
  · have hempty := hull_interior_dSq_inter_polyomino (n := n) (S := S) (p := p) hp
    have hsub : interior (dSq n p) ⊆ (dyadicPolyomino n S)ᶜ := by
      intro z hz
      simp only [mem_compl_iff]
      intro hzA
      exact Set.eq_empty_iff_forall_notMem.mp hempty z ⟨hz, hzA⟩
    have hint : interior (dSq n p) ⊆ compHull (dyadicPolyomino n S) := by
      intro w hw
      have hwcomp : w ∈ connectedComponentIn (dyadicPolyomino n S)ᶜ y :=
        IsPreconnected.subset_connectedComponentIn (hull_isPreconnected_interior_dSq n p) hyi hsub hw
      rw [mem_compHull, ← connectedComponentIn_eq hwcomp]
      exact mem_compHull.mp hy
    intro w hw
    have h1 : w ∈ closure (interior (dSq n p)) := hull_dSq_subset_closure_interior n p hw
    have h2 : w ∈ closure (compHull (dyadicPolyomino n S)) := closure_mono hint h1
    rwa [IsClosed.closure_eq (hull_isClosed_compHull (hull_isClosed_dyadicPolyomino n S))] at h2

/-! ## Preconnectedness of the hull and of its complement -/

theorem hull_not_isBounded_exterior (c : ℂ) (r : ℝ) :
    ¬ Bornology.IsBounded {z : ℂ | r < ‖z - c‖} := by
  intro hb
  obtain ⟨ρ, hρ⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hb
  set t : ℝ := |r| + |ρ + ‖c‖| + 1 with ht
  have htpos : 0 < t := by rw [ht]; positivity
  have htmem : c + ((t : ℝ) : ℂ) ∈ {z : ℂ | r < ‖z - c‖} := by
    have h1 : ‖(c + ((t : ℝ) : ℂ)) - c‖ = t := by
      rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
    change r < ‖(c + ((t : ℝ) : ℂ)) - c‖
    rw [h1]
    rw [ht]
    linarith [le_abs_self r, abs_nonneg (ρ + ‖c‖)]
  have h2 : ‖c + ((t : ℝ) : ℂ)‖ ≤ ρ := by
    have := hρ htmem
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  have h4 : ‖((t : ℝ) : ℂ)‖ = t := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
  have h5 : ‖((t : ℝ) : ℂ)‖ ≤ ‖c + ((t : ℝ) : ℂ)‖ + ‖c‖ := by
    have h6 : ‖((t : ℝ) : ℂ)‖ = ‖(c + ((t : ℝ) : ℂ)) - c‖ := by rw [add_sub_cancel_left]
    rw [h6]
    exact norm_sub_le _ _
  have h6 : ρ + ‖c‖ < t := by
    rw [ht]
    linarith [le_abs_self (ρ + ‖c‖), abs_nonneg r]
  rw [h4] at h5
  linarith

theorem hull_isPreconnected_compl_compHull {A : Set ℂ} (hA : IsCompact A) :
    IsPreconnected (compHull A)ᶜ := by
  by_cases hne : ((compHull A)ᶜ).Nonempty
  · obtain ⟨x, hx⟩ := hne
    have hx' : ¬ Bornology.IsBounded (connectedComponentIn Aᶜ x) := by
      simpa [compl_compHull] using hx
    have hxU : x ∈ Aᶜ := by
      by_contra h
      rw [connectedComponentIn_eq_empty h] at hx'
      exact hx' Bornology.isBounded_empty
    have heq : (compHull A)ᶜ = connectedComponentIn Aᶜ x := by
      apply Subset.antisymm
      · intro z hz
        have hz' : ¬ Bornology.IsBounded (connectedComponentIn Aᶜ z) := by
          simpa [compl_compHull] using hz
        have hzU : z ∈ Aᶜ := by
          by_contra h
          rw [connectedComponentIn_eq_empty h] at hz'
          exact hz' Bornology.isBounded_empty
        have h1 : connectedComponentIn Aᶜ z = connectedComponentIn Aᶜ x :=
          Commons.Topology.Jordan.compl_compact_unique_unbounded hA hzU hxU hz' hx'
        rw [← h1]
        exact mem_connectedComponentIn hzU
      · intro z hz
        rw [compl_compHull]
        change ¬ Bornology.IsBounded (connectedComponentIn Aᶜ z)
        rw [← connectedComponentIn_eq hz]
        exact hx'
    rw [heq]
    exact isPreconnected_connectedComponentIn
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact isPreconnected_empty

theorem hull_not_isBounded_univ_complex : ¬ Bornology.IsBounded (univ : Set ℂ) := by
  intro hb
  obtain ⟨ρ, hρ⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hb
  have hmem : ((ρ + 1 : ℝ) : ℂ) ∈ Metric.closedBall (0 : ℂ) ρ := hρ (mem_univ _)
  rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] at hmem
  have hρ0 : 0 ≤ ρ := le_trans (abs_nonneg _) hmem
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ ρ + 1)] at hmem
  linarith

theorem hull_isPreconnected_union_bounded_component {A : Set ℂ} (hAc : IsClosed A)
    (hAp : IsPreconnected A) {z : ℂ} (hzU : z ∈ Aᶜ)
    (hzb : Bornology.IsBounded (connectedComponentIn Aᶜ z)) :
    IsPreconnected (A ∪ connectedComponentIn Aᶜ z) := by
  have hCop : IsOpen (connectedComponentIn Aᶜ z) := hAc.isOpen_compl.connectedComponentIn
  have hCc : IsPreconnected (connectedComponentIn Aᶜ z) := isPreconnected_connectedComponentIn
  have hCcl : closure (connectedComponentIn Aᶜ z) ⊆ connectedComponentIn Aᶜ z ∪ A := by
    intro v hv
    by_cases hvint : v ∈ interior (connectedComponentIn Aᶜ z)
    · exact Or.inl (by rwa [hCop.interior_eq] at hvint)
    · exact Or.inr
        (Commons.Topology.Jordan.frontier_connectedComponentIn_subset hAc z v hv hvint)
  have hfn : (frontier (connectedComponentIn Aᶜ z)).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hcl : closure (connectedComponentIn Aᶜ z) = connectedComponentIn Aᶜ z := by
      rw [closure_eq_self_union_frontier, h, union_empty]
    have hclopen : IsClopen (connectedComponentIn Aᶜ z) := ⟨hcl ▸ isClosed_closure, hCop⟩
    have huniv : connectedComponentIn Aᶜ z = univ :=
      hclopen.eq_univ ⟨z, mem_connectedComponentIn hzU⟩
    exact hull_not_isBounded_univ_complex (huniv ▸ hzb)
  obtain ⟨v, hv⟩ := hfn
  have hvcl : v ∈ closure (connectedComponentIn Aᶜ z) := hv.1
  have hvA : v ∈ A := by
    rcases hCcl hvcl with h1 | h1
    · exfalso
      have : v ∈ interior (connectedComponentIn Aᶜ z) := by rwa [hCop.interior_eq]
      exact hv.2 this
    · exact h1
  have h2 : IsPreconnected (A ∪ closure (connectedComponentIn Aᶜ z)) :=
    IsPreconnected.union v hvA hvcl hAp hCc.closure
  have heq : A ∪ closure (connectedComponentIn Aᶜ z) = A ∪ connectedComponentIn Aᶜ z := by
    apply Subset.antisymm
    · intro w hw
      rcases hw with hw | hw
      · exact Or.inl hw
      · rcases hCcl hw with h | h
        · exact Or.inr h
        · exact Or.inl h
    · intro w hw
      rcases hw with hw | hw
      · exact Or.inl hw
      · exact Or.inr (subset_closure hw)
  rwa [heq] at h2

theorem hull_isPreconnected_compHull {A : Set ℂ} (hA : IsCompact A)
    (hAp : IsPreconnected A) (hAne : A.Nonempty) : IsPreconnected (compHull A) := by
  have hAc : IsClosed A := hA.isClosed
  obtain ⟨a, haA⟩ := hAne
  have hkey_gen : ∀ z : ℂ, z ∈ compHull A → IsPreconnected (A ∪ connectedComponentIn Aᶜ z) := by
    intro z hz
    by_cases hzA : z ∈ A
    · rw [connectedComponentIn_eq_empty (by simpa using hzA), union_empty]
      exact hAp
    · exact hull_isPreconnected_union_bounded_component hAc hAp (by simpa using hzA)
        (mem_compHull.mp hz)
  have hkey : ∀ z : {z : ℂ // z ∈ compHull A},
      IsPreconnected (A ∪ connectedComponentIn Aᶜ (z : ℂ)) := fun z => hkey_gen (z : ℂ) z.2
  have hnonempty :
      (⋂ z : {z : ℂ // z ∈ compHull A}, (A ∪ connectedComponentIn Aᶜ (z : ℂ))).Nonempty :=
    ⟨a, mem_iInter.mpr fun z => Or.inl haA⟩
  have hUn : (⋃ z : {z : ℂ // z ∈ compHull A}, (A ∪ connectedComponentIn Aᶜ (z : ℂ)))
      = compHull A := by
    apply Subset.antisymm
    · intro w hw
      rcases mem_iUnion.mp hw with ⟨z, hw⟩
      rcases hw with h | h
      · exact subset_compHull h
      · rw [mem_compHull, ← connectedComponentIn_eq h]
        exact mem_compHull.mp z.2
    · intro w hw
      by_cases hwA : w ∈ A
      · exact mem_iUnion.mpr ⟨⟨w, hw⟩, Or.inl hwA⟩
      · exact mem_iUnion.mpr ⟨⟨w, hw⟩, Or.inr (mem_connectedComponentIn (by simpa using hwA))⟩
  have := isPreconnected_iUnion hnonempty hkey
  rwa [hUn] at this

/-! ## The hull of a bounded polyomino is a polyomino -/

theorem hull_exists_finset_compHull_eq {n : ℕ} {S : Finset (ℤ × ℤ)} {R : ℝ}
    (hR : R < (n : ℝ) + 1) (hball : dyadicPolyomino n S ⊆ Metric.closedBall 0 R) :
    ∃ S' : Finset (ℤ × ℤ), compHull (dyadicPolyomino n S) = dyadicPolyomino n S' := by
  classical
  have hbdd : compHull (dyadicPolyomino n S) ⊆ Metric.closedBall 0 R := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hlt
    have hlt : R < ‖z‖ := not_le.mp hlt
    have hEsub : {w : ℂ | R < ‖w‖} ⊆ (dyadicPolyomino n S)ᶜ := by
      intro w hw hwA
      change R < ‖w‖ at hw
      have h1 : ‖w‖ ≤ R := by
        have := hball hwA
        rwa [Metric.mem_closedBall, dist_zero_right] at this
      linarith
    have hzE : z ∈ {w : ℂ | R < ‖w‖} := hlt
    have hEpre : IsPreconnected {w : ℂ | R < ‖w‖} := by
      simpa using Commons.Topology.Connected.isPreconnected_compl_closedBall (0 : ℂ) R
    have hcomp : connectedComponentIn (dyadicPolyomino n S)ᶜ z ⊇ {w : ℂ | R < ‖w‖} :=
      IsPreconnected.subset_connectedComponentIn hEpre hzE hEsub
    have hunb : ¬ Bornology.IsBounded (connectedComponentIn (dyadicPolyomino n S)ᶜ z) := by
      intro hb
      exact hull_not_isBounded_exterior (0 : ℂ) R (by simpa using hb.subset hcomp)
    exact hunb (mem_compHull.mp hz)
  have hsat : ∀ z ∈ compHull (dyadicPolyomino n S),
      ∃ p : ℤ × ℤ, z ∈ dSq n p ∧ dSq n p ⊆ compHull (dyadicPolyomino n S) := by
    intro z hz
    by_cases hzA : z ∈ dyadicPolyomino n S
    · obtain ⟨p, hp, hzp⟩ := mem_dyadicPolyomino.mp hzA
      exact ⟨p, hzp, fun w hw => subset_compHull (mem_dyadicPolyomino.mpr ⟨p, hp, hw⟩)⟩
    · have hzU : z ∈ (dyadicPolyomino n S)ᶜ := hzA
      have hzb : Bornology.IsBounded (connectedComponentIn (dyadicPolyomino n S)ᶜ z) :=
        mem_compHull.mp hz
      have hopen : IsOpen (connectedComponentIn (dyadicPolyomino n S)ᶜ z) :=
        (hull_isClosed_dyadicPolyomino n S).isOpen_compl.connectedComponentIn
      obtain ⟨ε, hεpos, hε⟩ := Metric.isOpen_iff.mp hopen z (mem_connectedComponentIn hzU)
      obtain ⟨p, hzp⟩ := Commons.Topology.Plane.dyadicCell_grid_cover n z
      refine ⟨p, hzp, ?_⟩
      by_cases hzi : z ∈ interior (dSq n p)
      · exact hull_dSq_subset_compHull_of_mem_interior hz hzi
      · have hcl : z ∈ closure (interior (dSq n p)) := hull_dSq_subset_closure_interior n p hzp
        obtain ⟨u, hu, hzu⟩ := Metric.mem_closure_iff.mp hcl ε hεpos
        have hucomp : u ∈ compHull (dyadicPolyomino n S) := by
          have hucomp' : u ∈ connectedComponentIn (dyadicPolyomino n S)ᶜ z :=
            hε (by rw [Metric.mem_ball, dist_comm]; exact hzu)
          rw [mem_compHull, ← connectedComponentIn_eq hucomp']
          exact hzb
        exact hull_dSq_subset_compHull_of_mem_interior hucomp hu
  refine ⟨(Finset.Icc (-(Commons.Topology.Plane.dyadicBound n))
      (Commons.Topology.Plane.dyadicBound n) ×ˢ
      Finset.Icc (-(Commons.Topology.Plane.dyadicBound n))
        (Commons.Topology.Plane.dyadicBound n)).filter
      (fun p => dSq n p ⊆ compHull (dyadicPolyomino n S)), ?_⟩
  ext z
  constructor
  · intro hz
    obtain ⟨p, hzp, hcell⟩ := hsat z hz
    have hpbox : p ∈ Finset.Icc (-(Commons.Topology.Plane.dyadicBound n))
        (Commons.Topology.Plane.dyadicBound n) ×ˢ
        Finset.Icc (-(Commons.Topology.Plane.dyadicBound n))
          (Commons.Topology.Plane.dyadicBound n) := by
      refine Commons.Topology.Plane.mem_dyadicAmbientBox_of_subset_ball (fun w hw => ?_)
      have h1 : ‖w‖ ≤ R := by
        have := hbdd (hcell hw)
        rwa [Metric.mem_closedBall, dist_zero_right] at this
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    exact mem_dyadicPolyomino.mpr ⟨p, Finset.mem_filter.mpr ⟨hpbox, hcell⟩, hzp⟩
  · intro hz
    obtain ⟨p, hp, hzp⟩ := mem_dyadicPolyomino.mp hz
    exact (Finset.mem_filter.mp hp).2 hzp

/-! ## Covering a compact preconnected set by a preconnected polyomino -/

theorem hull_exists_polyomino_superset {U : Set ℂ} (hUo : IsOpen U) {K : Set ℂ}
    (hK : IsCompact K) (hKne : K.Nonempty) (hKp : IsPreconnected K) (hKU : K ⊆ U) :
    ∃ (n : ℕ) (S : Finset (ℤ × ℤ)), K ⊆ dyadicPolyomino n S ∧
      dyadicPolyomino n S ⊆ U ∧ IsPreconnected (dyadicPolyomino n S) ∧
      ∃ R : ℝ, R < (n : ℝ) + 1 ∧ dyadicPolyomino n S ⊆ Metric.closedBall 0 R := by
  classical
  obtain ⟨RK, hRK⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hK.isBounded
  obtain ⟨m, hm⟩ : ∃ m : ℕ, max RK 0 + 3 < (m : ℝ) + 1 := by
    obtain ⟨m, hm⟩ := exists_nat_gt (max RK 0 + 2)
    exact ⟨m, by linarith⟩
  obtain ⟨n₀, hn₀⟩ := Work.Spine.Plane.exists_polyK_superset_of_compact U hUo hK hKU
  let n : ℕ := max n₀ m
  have hn₀' : n₀ ≤ n := le_max_left _ _
  have hm' : (m : ℝ) ≤ (n : ℝ) := by
    have : m ≤ n := le_max_right _ _
    exact_mod_cast this
  have hbig : max RK 0 + 3 < (n : ℝ) + 1 := by linarith
  have hKsub : K ⊆ Work.Spine.Plane.polyK U hUo n :=
    hn₀.trans (Work.Spine.Plane.polyK_mono_le U hUo hn₀')
  let S : Finset (ℤ × ℤ) :=
    (Work.Spine.Plane.cells U hUo n).filter (fun p => (dSq n p ∩ K).Nonempty)
  have hKS : K ⊆ dyadicPolyomino n S := by
    intro z hz
    have hzP : z ∈ dyadicPolyomino n (Work.Spine.Plane.cells U hUo n) := hKsub hz
    obtain ⟨p, hp, hzp⟩ := mem_dyadicPolyomino.mp hzP
    exact mem_dyadicPolyomino.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, ⟨z, hzp, hz⟩⟩, hzp⟩
  have hSU : dyadicPolyomino n S ⊆ U := by
    intro z hz
    obtain ⟨p, hp, hzp⟩ := mem_dyadicPolyomino.mp hz
    have hpcell : p ∈ Work.Spine.Plane.cells U hUo n := (Finset.mem_filter.mp hp).1
    have hzP : z ∈ Work.Spine.Plane.polyK U hUo n := by
      show z ∈ ⋃ q ∈ Work.Spine.Plane.cells U hUo n, dSq n q
      exact mem_iUnion₂.mpr ⟨p, hpcell, hzp⟩
    exact Work.Spine.Plane.polyK_subset U hUo n hzP
  have hSpre : IsPreconnected (dyadicPolyomino n S) := by
    obtain ⟨x, hx⟩ := hKne
    have hXeq : dyadicPolyomino n S = connectedComponentIn (dyadicPolyomino n S) x := by
      apply Subset.antisymm
      · intro y hy
        obtain ⟨p, hp, hyp⟩ := mem_dyadicPolyomino.mp hy
        obtain ⟨k, hkp, hkK⟩ := (Finset.mem_filter.mp hp).2
        have hcellpre : IsPreconnected (dSq n p) := (hull_convex_dSq n p).isPreconnected
        have hcellsub : dSq n p ⊆ dyadicPolyomino n S :=
          fun w hw => mem_dyadicPolyomino.mpr ⟨p, hp, hw⟩
        have hkcomp : k ∈ connectedComponentIn (dyadicPolyomino n S) x :=
          IsPreconnected.subset_connectedComponentIn hKp hx hKS hkK
        have hyk : y ∈ connectedComponentIn (dyadicPolyomino n S) k :=
          IsPreconnected.subset_connectedComponentIn hcellpre hkp hcellsub hyp
        rwa [← connectedComponentIn_eq hkcomp] at hyk
      · intro y hy
        exact connectedComponentIn_subset _ _ hy
    rw [hXeq]
    exact isPreconnected_connectedComponentIn
  have hSbdd : dyadicPolyomino n S ⊆ Metric.closedBall 0 (max RK 0 + Real.sqrt 2 / 2 ^ n) := by
    intro z hz
    obtain ⟨p, hp, hzp⟩ := mem_dyadicPolyomino.mp hz
    obtain ⟨k, hkp, hkK⟩ := (Finset.mem_filter.mp hp).2
    rw [Metric.mem_closedBall, dist_zero_right]
    have hk0 : ‖k‖ ≤ RK := by
      have := hRK hkK
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    have hk : ‖k‖ ≤ max RK 0 := le_trans hk0 (le_max_left _ _)
    have hd : dist z k ≤ Real.sqrt 2 / 2 ^ n :=
      Commons.Topology.Plane.dyadicCell_dist_le hzp hkp
    calc ‖z‖ = ‖(z - k) + k‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - k‖ + ‖k‖ := norm_add_le _ _
      _ = dist z k + ‖k‖ := by rw [Complex.dist_eq]
      _ ≤ Real.sqrt 2 / 2 ^ n + max RK 0 := add_le_add hd hk
      _ = max RK 0 + Real.sqrt 2 / 2 ^ n := by ring
  refine ⟨n, S, hKS, hSU, hSpre, max RK 0 + Real.sqrt 2 / 2 ^ n, ?_, hSbdd⟩
  have hsqrt2 : Real.sqrt 2 < 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have h2n : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hdiv : Real.sqrt 2 / 2 ^ n ≤ Real.sqrt 2 := div_le_self (Real.sqrt_nonneg 2) h2n
  linarith

theorem hull_compHull_subset_of_no_bounded_complement {A U : Set ℂ}
    (hnb : ∀ z : ℂ, z ∉ U → ¬ Bornology.IsBounded (connectedComponentIn Uᶜ z))
    (hAU : A ⊆ U) : compHull A ⊆ U := by
  intro z hz
  by_contra hzU
  have hsub : connectedComponentIn Uᶜ z ⊆ Aᶜ := by
    intro w hw hwA
    exact connectedComponentIn_subset Uᶜ z hw (hAU hwA)
  have hcomp : connectedComponentIn Uᶜ z ⊆ connectedComponentIn Aᶜ z :=
    IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
      (mem_connectedComponentIn (show z ∈ Uᶜ from hzU)) hsub
  exact hnb z hzU ((mem_compHull.mp hz).subset hcomp)

/-! ## The target -/

theorem exists_hull_dyadicPolyomino {U : Set ℂ} (hUo : IsOpen U)
    (hnb : ∀ z : ℂ, z ∉ U → ¬ Bornology.IsBounded (connectedComponentIn Uᶜ z))
    {K : Set ℂ} (hK : IsCompact K) (hKc : IsConnected K) (hKU : K ⊆ U) :
    ∃ (n : ℕ) (S : Finset (ℤ × ℤ)), S.Nonempty ∧ K ⊆ Work.PlanarSC.dyadicPolyomino n S ∧
      Work.PlanarSC.dyadicPolyomino n S ⊆ U ∧
      IsPreconnected (Work.PlanarSC.dyadicPolyomino n S) ∧
      IsPreconnected (Work.PlanarSC.dyadicPolyomino n S)ᶜ := by
  obtain ⟨n, S, hKS, hSU, hSpre, R, hR, hSbdd⟩ :=
    hull_exists_polyomino_superset hUo hK hKc.nonempty hKc.isPreconnected hKU
  obtain ⟨S', hS'⟩ := hull_exists_finset_compHull_eq hR hSbdd
  have hne : (dyadicPolyomino n S).Nonempty := hKc.nonempty.mono hKS
  have hPc : IsCompact (dyadicPolyomino n S) :=
    Metric.isCompact_iff_isClosed_bounded.mpr
      ⟨hull_isClosed_dyadicPolyomino n S, (Metric.isBounded_closedBall).subset hSbdd⟩
  have hU : compHull (dyadicPolyomino n S) ⊆ U :=
    hull_compHull_subset_of_no_bounded_complement hnb hSU
  refine ⟨n, S', ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hne
    have hx' : x ∈ dyadicPolyomino n S' := hS' ▸ subset_compHull hx
    obtain ⟨p, hp, _⟩ := mem_dyadicPolyomino.mp hx'
    exact ⟨p, hp⟩
  · rw [← hS']; exact hKS.trans subset_compHull
  · rw [← hS']; exact hU
  · rw [← hS']; exact hull_isPreconnected_compHull hPc hSpre hne
  · rw [← hS']; exact hull_isPreconnected_compl_compHull hPc

end Work.PlanarSC
