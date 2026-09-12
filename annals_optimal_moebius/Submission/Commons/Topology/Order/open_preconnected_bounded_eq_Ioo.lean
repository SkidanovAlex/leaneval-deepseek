import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Submission.Commons.Topology.Order.open_preconnected_eq_Ioo_ereal

noncomputable section
open scoped Topology

namespace Commons.Topology.Order

/-- A nonempty open preconnected bounded subset of the real line is an open
interval with REAL endpoints: if `s` is open, preconnected, nonempty and
bounded (all its elements have modulus ≤ R), then there exist real
`a < b` with `s = Set.Ioo a b`.  This is the finite-endpoint sharpening of
`Commons.Topology.Order.open_preconnected_eq_Ioo_ereal` (boundedness rules
out the infinite EReal endpoints). -/
theorem open_preconnected_bounded_eq_Ioo {s : Set ℝ}
    (hs : IsOpen s) (hsne : s.Nonempty) (hpre : IsPreconnected s)
    (hbd : ∃ R : ℝ, ∀ x ∈ s, |x| ≤ R) :
    ∃ a b : ℝ, a < b ∧ s = Set.Ioo a b := by
  classical
  -- Boundedness provides both a lower and an upper bound for `s`.
  rcases hbd with ⟨R, hR⟩
  have hbddBelow : BddBelow s := by
    refine ⟨-R, ?_⟩
    intro x hx
    exact (abs_le.mp (hR x hx)).1
  have hbddAbove : BddAbove s := by
    refine ⟨R, ?_⟩
    intro x hx
    exact (abs_le.mp (hR x hx)).2
  let a : ℝ := sInf s
  let b : ℝ := sSup s
  -- Preconnected sets in a linear order are order-connected.
  have hord : s.OrdConnected := isPreconnected_iff_ordConnected.mp hpre
  -- Every point of `s` is strictly above the infimum (openness supplies points
  -- of `s` arbitrarily close below any point of `s`).
  have hlt_mem : ∀ x ∈ s, a < x := by
    intro x hx
    have hxmem : s ∈ 𝓝 x := hs.mem_nhds hx
    rcases exists_Ioc_subset_of_mem_nhds (s := s) hxmem ⟨x - 1, by linarith⟩ with
      ⟨l, hl, hlsub⟩
    let v : ℝ := (l + x) / 2
    have hlv : l < v := by dsimp [v]; linarith
    have hvx : v < x := by dsimp [v]; linarith
    have hvs : v ∈ s := hlsub ⟨hlv, le_of_lt hvx⟩
    have hle : a ≤ v := by
      dsimp [a]
      exact csInf_le hbddBelow hvs
    exact lt_of_le_of_lt hle hvx
  -- Every point of `s` is strictly below the supremum.
  have hmem_lt : ∀ x ∈ s, x < b := by
    intro x hx
    have hxmem : s ∈ 𝓝 x := hs.mem_nhds hx
    rcases exists_Ico_subset_of_mem_nhds (s := s) hxmem ⟨x + 1, by linarith⟩ with
      ⟨u, hxu, husub⟩
    let w : ℝ := (x + u) / 2
    have hxw : x < w := by dsimp [w]; linarith
    have hwu : w < u := by dsimp [w]; linarith
    have hws : w ∈ s := husub ⟨le_of_lt hxw, hwu⟩
    have hle : w ≤ b := by
      dsimp [b]
      exact le_csSup hbddAbove hws
    exact lt_of_lt_of_le hxw hle
  -- Conversely, anything strictly between the infimum and the supremum lies in
  -- `s`: strict inequality against the infimum/supremum supplies elements of
  -- `s` below and above it, and order-connectedness closes the interval.
  have h_mem : ∀ x, a < x → x < b → x ∈ s := by
    intro x hax hxb
    have hgt : ∃ z ∈ s, x < z := by
      by_contra h
      have hb : b ≤ x := by
        dsimp [b]
        apply csSup_le hsne
        intro z hz
        exact le_of_not_gt (fun hxz => h ⟨z, hz, hxz⟩)
      exact (not_lt_of_ge hb) hxb
    have hlt : ∃ y ∈ s, y < x := by
      by_contra h
      have ha : x ≤ a := by
        dsimp [a]
        apply le_csInf hsne
        intro y hy
        exact le_of_not_gt (fun hyx => h ⟨y, hy, hyx⟩)
      exact (not_lt_of_ge ha) hax
    rcases hlt with ⟨y, hys, hyx⟩
    rcases hgt with ⟨z, hzs, hxz⟩
    exact hord.out hys hzs ⟨le_of_lt hyx, le_of_lt hxz⟩
  refine ⟨a, b, ?_, ?_⟩
  · -- `a < b`: both follow from a single point of `s` (which exists by `hsne`).
    rcases hsne with ⟨x0, hx0⟩
    exact lt_trans (hlt_mem x0 hx0) (hmem_lt x0 hx0)
  · -- `s = Ioo a b`
    ext x
    constructor
    · intro hx
      exact ⟨hlt_mem x hx, hmem_lt x hx⟩
    · intro hx
      rcases hx with ⟨hax, hxb⟩
      exact h_mem x hax hxb

end Commons.Topology.Order

end