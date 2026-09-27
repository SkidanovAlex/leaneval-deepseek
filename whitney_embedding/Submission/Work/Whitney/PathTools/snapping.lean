import Mathlib
import Submission.Work.Whitney.PathTools.GridGeom
import Submission.Work.Whitney.PathTools.GridGeom2
import Submission.Work.Whitney.PathTools.exists_chain_of_path

/-!
# Snapping a continuous path to a grid chain avoiding a compact set

Given a path `γ` in the plane staying at distance `> m` from a set `K`, and a grid mesh `h` small
compared with `m`, one can build a `1`-chain `l` whose boundary is `δ_{p} + δ_{q}` (for the grid
vertices `p`, `q` nearest to the endpoints of `γ`) and whose support avoids all edges of cells
meeting `K`.  Combined with `GridSplit.exists_chain_avoiding_union` this gives Janiszewski's
theorem for two disjoint compacta.
-/

open Set Metric Work.Whitney.PathTools.Grid

namespace Work.Whitney.PathTools.Grid

noncomputable section

/-- Telescoping sum of consecutive differences in `ZMod 2`. -/
lemma sum_range_telescope (a : ℕ → (ℤ × ℤ → ZMod 2)) (N : ℕ) :
    (∑ i ∈ Finset.range N, (a i + a (i + 1))) = a 0 + a N := by
  induction N with
  | zero =>
      rw [Finset.sum_range_zero]
      funext v
      simp only [Pi.zero_apply, Pi.add_apply]
      exact (CharTwo.add_self_eq_zero (a 0 v)).symm
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      funext v
      simp only [Pi.add_apply]
      rw [show a 0 v + a N v + (a N v + a (N + 1) v) = a 0 v + a (N + 1) v + (a N v + a N v)
            from by abel, CharTwo.add_self_eq_zero, add_zero]

/-- **A staircase whose base vertex is close to a point far from `K` avoids the cells of `K`.** -/
lemma stair_avoids {h : ℝ} (hh : 0 < h) {K : Set Pt} {u v : ℤ × ℤ} {P : Pt} {m : ℝ}
    (huv : |u.1 - v.1| ≤ 1) (huv' : |u.2 - v.2| ≤ 1)
    (huP : dist (gptH h u) P ≤ 2 * h) (hPK : m ≤ Metric.infDist P K) (hm : 6 * h < m) :
    ∀ e ∈ (stair u v).support, e ∉ edgeSet (cellSet h K) := by
  intro e he hmem
  obtain ⟨c, hc, hec⟩ := hmem
  obtain ⟨z, hzg, hzK⟩ := hc
  obtain ⟨h1, h2, h3, h4⟩ := stair_edges_close huv huv' e he
  have hzu : dist z (gptH h u) ≤ 4 * h := by
    have hA : dist z (gptH h (eTail e)) ≤ 2 * h :=
      gsq_dist_le h hh.le hzg (cellEdges_endpoints h hh.le hec).1
    have hB : dist (gptH h (eTail e)) (gptH h u) ≤ 2 * h := gptH_dist_le h hh h1 h2
    calc dist z (gptH h u) ≤ dist z (gptH h (eTail e)) + dist (gptH h (eTail e)) (gptH h u) :=
          dist_triangle _ _ _
      _ ≤ 4 * h := by linarith
  have hPK' : m ≤ dist P z := le_trans hPK (Metric.infDist_le_dist_of_mem hzK)
  have hPz : dist P z ≤ dist P (gptH h u) + dist (gptH h u) z := dist_triangle _ _ _
  have h1' : dist P (gptH h u) ≤ 2 * h := by rwa [dist_comm] at huP
  have h2' : dist (gptH h u) z ≤ 4 * h := by rwa [dist_comm] at hzu
  linarith

/-- **Snapping.**  A path staying at distance `> m` from `K` snaps to a grid chain (mesh `h`, with
`16 h < m`) whose boundary is the pair of grid vertices nearest to the endpoint, and whose support
avoids all edges of cells meeting `K`. -/
theorem exists_chain_of_path {h : ℝ} (hh : 0 < h) {K : Set Pt} {m : ℝ} (hm : 0 < m)
    {x y : Pt} (γ : Path x y) (hav : ∀ t, m ≤ Metric.infDist (γ t) K) (hsmall : 16 * h < m) :
    ∃ (l : Chain1) (p q : ℤ × ℤ),
      (∀ v, bdry1 ((l : Chain1) : Edge → ZMod 2) v
        = (if v = p then 1 else 0) + (if v = q then 1 else 0)) ∧
      (∀ e ∈ l.support, e ∉ edgeSet (cellSet h K)) := by
  have huc : UniformContinuousOn γ (Set.univ : Set unitInterval) :=
    isCompact_univ.uniformContinuousOn_of_continuous γ.continuous.continuousOn
  obtain ⟨d, hdpos, hd⟩ := (Metric.uniformContinuousOn_iff.mp huc) (h / 8) (by positivity)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hdpos
  have hNlt : 1 / (((n + 1 : ℕ)) : ℝ) < d := by
    rw [Nat.cast_add, Nat.cast_one]
    exact hn
  set s : ℕ → unitInterval := fun i =>
    ⟨min 1 ((i : ℝ) / ((n + 1 : ℕ) : ℝ)),
      ⟨le_min zero_le_one (by positivity), min_le_left 1 _⟩⟩ with hsdef
  have hs_le : ∀ i ≤ n + 1, ((s i : unitInterval) : ℝ) = (i : ℝ) / ((n + 1 : ℕ) : ℝ) := by
    intro i hi
    show min 1 ((i : ℝ) / ((n + 1 : ℕ) : ℝ)) = _
    exact min_eq_right (by
      rw [div_le_one (by positivity)]
      exact_mod_cast hi)
  have hs_dist : ∀ i < n + 1, dist (s i) (s (i + 1)) < d := by
    intro i hi
    have h1 : ((s i : unitInterval) : ℝ) = (i : ℝ) / ((n + 1 : ℕ) : ℝ) := hs_le i (le_of_lt hi)
    have h2 : ((s (i + 1) : unitInterval) : ℝ) = ((i + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) :=
      hs_le (i + 1) (by omega)
    have hval : dist (s i) (s (i + 1)) = 1 / ((n + 1 : ℕ) : ℝ) := by
      rw [Subtype.dist_eq, h1, h2, Real.dist_eq]
      rw [show (i : ℝ) / ((n + 1 : ℕ) : ℝ) - ((i + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)
            = -(1 / ((n + 1 : ℕ) : ℝ)) from by push_cast; field_simp; ring]
      rw [abs_neg, abs_of_nonneg (by positivity)]
    rw [hval]
    exact hNlt
  have hstep : ∀ i < n + 1, dist (γ (s i)) (γ (s (i + 1))) < h / 8 := by
    intro i hi
    exact hd (s i) trivial (s (i + 1)) trivial (hs_dist i hi)
  have hcoord : ∀ i < n + 1,
      |(gNear h (γ (s i))).1 - (gNear h (γ (s (i + 1)))).1| ≤ 1 ∧
        |(gNear h (γ (s i))).2 - (gNear h (γ (s (i + 1)))).2| ≤ 1 := by
    intro i hi
    have h := gNF_step h hh (le_of_lt (hstep i hi))
    constructor
    · have h0 := h 0
      simpa [gNF] using h0
    · have h1 := h 1
      simpa [gNF] using h1
  refine ⟨∑ i ∈ Finset.range (n + 1), stair (gNear h (γ (s i))) (gNear h (γ (s (i + 1)))),
    gNear h (γ (s 0)), gNear h (γ (s (n + 1))), ?_, ?_⟩
  · have hcoe : ((∑ i ∈ Finset.range (n + 1),
        stair (gNear h (γ (s i))) (gNear h (γ (s (i + 1)))) : Chain1) : Edge → ZMod 2)
        = ∑ i ∈ Finset.range (n + 1),
          ((stair (gNear h (γ (s i))) (gNear h (γ (s (i + 1)))) : Chain1) : Edge → ZMod 2) :=
      Finsupp.coe_finset_sum _ _
    have hterm : ∀ i ∈ Finset.range (n + 1),
        bdry1 ((stair (gNear h (γ (s i))) (gNear h (γ (s (i + 1)))) : Chain1) : Edge → ZMod 2)
          = dirac (gNear h (γ (s i))) + dirac (gNear h (γ (s (i + 1)))) := by
      intro i hi
      exact bdry1_stair (hcoord i (Finset.mem_range.mp hi)).1 (hcoord i (Finset.mem_range.mp hi)).2
    have hbdry : bdry1 ((∑ i ∈ Finset.range (n + 1),
        stair (gNear h (γ (s i))) (gNear h (γ (s (i + 1)))) : Chain1) : Edge → ZMod 2)
        = dirac (gNear h (γ (s 0))) + dirac (gNear h (γ (s (n + 1)))) := by
      rw [hcoe, bdry1_finset_sum, Finset.sum_congr rfl hterm]
      exact sum_range_telescope (fun i => dirac (gNear h (γ (s i)))) (n + 1)
    intro v
    rw [hbdry]
    simp [dirac, Pi.add_apply]
  · intro e he
    have hsupp : e ∈ (Finset.range (n + 1)).biUnion (fun i =>
        (stair (gNear h (γ (s i))) (gNear h (γ (s (i + 1)))) : Chain1).support) :=
      Finsupp.support_finset_sum he
    obtain ⟨i, hi, hei⟩ := Finset.mem_biUnion.mp hsupp
    have hi' : i < n + 1 := Finset.mem_range.mp hi
    exact stair_avoids hh (hcoord i hi').1 (hcoord i hi').2
      (gNF_dist h hh (γ (s i))) (hav (s i)) (by linarith [hsmall]) e hei

end

end Work.Whitney.PathTools.Grid
