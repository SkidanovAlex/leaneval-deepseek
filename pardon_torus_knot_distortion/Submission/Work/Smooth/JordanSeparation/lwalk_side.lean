import Mathlib
import Submission.Work.Smooth.JordanSeparation.lwalk_local
import Submission.Work.Smooth.JordanSeparation.lwalk_peel_base

/-!
# The side determination at the lex-max vertex

For a simple closed lattice walk `W` with lex-max vertex `p`, the cell SW of `p` lies in the
bounded side `S.V` of the Jordan separation.  This is the input of the corner move of the peel
(`_LWALK_PEEL_NOTES2.md`).
-/

namespace Work.Smooth.JordanSeparation

open Set Metric

noncomputable section

namespace LWalk

variable {W : LWalk} {S : Work.Smooth.Jordan.PlaneSeparation W.toPlaneCurve}

/-- A connected unbounded set avoiding the trace lies in the unbounded side. -/
theorem subset_U_of_not_isBounded {A : Set ℂ} (hAc : IsPreconnected A)
    (hA : A ⊆ (Set.range W.curve)ᶜ) (hAunb : ¬ Bornology.IsBounded A) : A ⊆ S.U := by
  rcases subset_U_or_subset_V (W := W) S hAc hA with h | h
  · exact h
  · exact absurd (hAunb (S.bounded_V.subset h)) id

/-- The half-plane `{z | a < z.re}` is convex. -/
theorem convex_re_gt (a : ℝ) : Convex ℝ {z : ℂ | a < z.re} := by
  intro x hx y hy s t hs ht hst
  have hx' : a < x.re := hx
  have hy' : a < y.re := hy
  have hre : (s • x + t • y).re = s * x.re + t * y.re := by
    simp [Complex.add_re, Complex.real_smul, Complex.mul_re]
  show a < (s • x + t • y).re
  rw [hre]
  rcases eq_or_lt_of_le hs with hs0 | hs0
  · rw [← hs0, zero_mul, zero_add]
    have ht1 : t = 1 := by linarith
    rw [ht1, one_mul]
    exact hy'
  · rcases eq_or_lt_of_le ht with ht0 | ht0
    · rw [← ht0, zero_mul, add_zero]
      have hs1 : s = 1 := by linarith
      rw [hs1, one_mul]
      exact hx'
    · have h1 : s * a < s * x.re := mul_lt_mul_of_pos_left hx' hs0
      have h2 : t * a < t * y.re := mul_lt_mul_of_pos_left hy' ht0
      have hst' : s * a + t * a = a := by rw [← add_mul, hst, one_mul]
      nlinarith [h1, h2, hst']

/-- **The half-plane strictly east of the lex-max vertex lies in the unbounded side.** -/
theorem halfplane_subset_U {k : ℕ} (hk : k ≤ W.n)
    (hmax : ∀ j, j ≤ W.n → ((W.v j).1 : ℝ) * W.c ≤ ((W.v k).1 : ℝ) * W.c) :
    {z : ℂ | ((W.v k).1 : ℝ) * W.c < z.re} ⊆ S.U := by
  set a : ℝ := ((W.v k).1 : ℝ) * W.c with ha
  have htra : Set.range W.curve ⊆ {z : ℂ | z.re ≤ a} := by
    intro z hz
    rw [mem_range_curve_iff] at hz
    rcases hz with hz0 | ⟨j, hj, hzj⟩
    · have hz' : z = W.c • gpt (W.v 0) := by rw [hz0, LWalk.pt, Complex.real_smul]
      rw [hz']
      show (W.c • gpt (W.v 0)).re ≤ a
      rw [re_smul_gpt, ha]
      exact hmax 0 (Nat.zero_le _)
    · have hseg : z ∈ segment ℝ (W.c • gpt (W.v j)) (W.c • gpt (W.v (j + 1))) := by
        have h1 : W.pt j = W.c • gpt (W.v j) := by rw [LWalk.pt, Complex.real_smul]
        have h2 : W.pt (j + 1) = W.c • gpt (W.v (j + 1)) := by rw [LWalk.pt, Complex.real_smul]
        rw [show W.edge j = segPath (W.pt j) (W.pt (j + 1)) from rfl, segPath_range] at hzj
        rwa [h1, h2] at hzj
      rw [segment_eq_image] at hseg
      obtain ⟨t, ht, hzt⟩ := hseg
      have hval := congrArg Complex.re hzt.symm
      simp only [] at hval
      rw [re_interp_smul_gpt] at hval
      show z.re ≤ a
      rw [hval, ha]
      have h1 : ((W.v j).1 : ℝ) * W.c ≤ ((W.v k).1 : ℝ) * W.c := hmax j (le_of_lt hj)
      have h2 : ((W.v (j + 1)).1 : ℝ) * W.c ≤ ((W.v k).1 : ℝ) * W.c :=
        hmax (j + 1) (Nat.succ_le_of_lt hj)
      nlinarith [ht.1, ht.2]
  have hsub : {z : ℂ | a < z.re} ⊆ (Set.range W.curve)ᶜ := by
    intro z hz hztr
    have h1 : z.re ≤ a := htra hztr
    have h2 : a < z.re := hz
    linarith
  rcases subset_U_or_subset_V (W := W) S (convex_re_gt a).isPreconnected hsub with h | h
  · exact h
  · exfalso
    have hunb : ¬ Bornology.IsBounded {z : ℂ | a < z.re} := by
      intro hb
      obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hb
      set t : ℝ := |a| + |r| + 2 with ht
      have htmem : ((t : ℝ) : ℂ) ∈ {z : ℂ | a < z.re} := by
        simp only [Set.mem_ofPred_eq, Complex.ofReal_re]
        have h1 : a ≤ |a| := le_abs_self a
        have h2 : (0:ℝ) ≤ |r| := abs_nonneg r
        rw [ht]; linarith
      have hnorm : ‖((t : ℝ) : ℂ)‖ = t := by
        rw [Complex.norm_def, Complex.normSq_ofReal, ← pow_two, Real.sqrt_sq (by rw [ht]; positivity)]
      have hle := hr htmem
      rw [Metric.mem_closedBall, dist_zero_right, hnorm, ht] at hle
      have h3 : r ≤ |r| := le_abs_self r
      have h4 : (0:ℝ) ≤ |a| := abs_nonneg a
      have h5 : (0:ℝ) ≤ |r| := abs_nonneg r
      linarith
    exact hunb (S.bounded_V.subset h)

/-- A lattice neighbour of `p` that is lexicographically `≤ p` is one of `p - (1,0)`,
`p - (0,1)`. -/
theorem eq_sub_of_gridStep_le_left {u p : ℤ × ℤ} (h : GridStep u p)
    (hlex : (u.1 < p.1) ∨ (u.1 = p.1 ∧ u.2 ≤ p.2)) :
    u = p - (1, 0) ∨ u = p - (0, 1) := by
  obtain ⟨s, hs, hdir⟩ := gridStep_vert_or_horiz h
  rcases hdir with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hu : u = p - (0, s) := by
      apply Prod.ext
      · simp only [Prod.fst_sub, Prod.fst_zero, Prod.snd_zero, sub_zero]
        omega
      · simp only [Prod.snd_sub, Prod.fst_zero, Prod.snd_zero]
        omega
    rcases hs with rfl | rfl
    · right; exact hu
    · exfalso
      have h2' : u.2 = p.2 + 1 := by
        rw [hu]
        simp only [Prod.snd_sub, Prod.snd_zero]
        ring
      omega
  · have hu : u = p - (s, 0) := by
      apply Prod.ext
      · simp only [Prod.fst_sub, Prod.fst_zero, Prod.snd_zero]
        omega
      · simp only [Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, sub_zero]
        omega
    rcases hs with rfl | rfl
    · left; exact hu
    · exfalso
      have h1' : u.1 = p.1 + 1 := by
        rw [hu]
        simp only [Prod.fst_sub, Prod.fst_zero, Prod.snd_zero]
        ring
      omega

/-- At the lex-max vertex `p = W.v k`, the two edges of the walk meeting `p` are the top and the
right side of the corner cell; in particular one of them realizes the vertical canonical edge
`edgeV W.c (p.1, p.2 - 1)`. -/
theorem exists_edgeV_corner {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ W.n) {p : ℤ × ℤ}
    (hp : W.v k = p)
    (hlex : ∀ j, j ≤ W.n → ((W.v j).1 < p.1) ∨ ((W.v j).1 = p.1 ∧ (W.v j).2 ≤ p.2))
    (hW : W.IsSimple) (hn : 2 < W.n) :
    ∃ j, j < W.n ∧ Set.range (W.edge j) = edgeV W.c (p.1, p.2 - 1) := by
  have hkp : k - 1 < W.n := by omega
  have hke : k < W.n := by omega
  have hd1 : W.v (k - 1) = p - (1, 0) ∨ W.v (k - 1) = p - (0, 1) := by
    have hstep : GridStep (W.v (k - 1)) p := by
      have h := W.step (k - 1) hkp
      rwa [show k - 1 + 1 = k from by omega, hp] at h
    exact eq_sub_of_gridStep_le_left hstep (hlex (k - 1) (by omega))
  have hd2 : W.v (k + 1) = p - (1, 0) ∨ W.v (k + 1) = p - (0, 1) := by
    have hstep : GridStep (W.v (k + 1)) p := by
      have h := gridStep_symm (W.step k hke)
      rwa [hp] at h
    exact eq_sub_of_gridStep_le_left hstep (hlex (k + 1) hk2)
  have hne : W.v (k - 1) ≠ W.v (k + 1) := by
    refine hW (k - 1) (k + 1) (by omega) hk2 ?_
    intro hc
    have h1 : k - 1 = 0 := congrArg Prod.fst hc
    have h2 : k + 1 = W.n := congrArg Prod.snd hc
    omega
  have hv : W.v (k + 1) = p - (0, 1) ∨ W.v (k - 1) = p - (0, 1) := by
    rcases hd2 with h2 | h2
    · rcases hd1 with h1 | h1
      · exact absurd (h1.trans h2.symm) hne
      · exact Or.inr h1
    · exact Or.inl h2
  have hpe : (p.1, p.2 - 1) + (0, 1) = p := by ext <;> simp <;> omega
  rcases hv with h2 | h1
  · -- the `k`-th edge is the right side of the corner cell
    refine ⟨k, hke, ?_⟩
    have hpt1 : W.pt k = W.c • gpt p := by rw [LWalk.pt, hp, Complex.real_smul]
    have hpt2 : W.pt (k + 1) = W.c • gpt (p.1, p.2 - 1) := by
      rw [LWalk.pt, h2, Complex.real_smul]
      congr 2
      ext <;> simp <;> omega
    rw [show W.edge k = segPath (W.pt k) (W.pt (k + 1)) from rfl, segPath_range, hpt1, hpt2,
      edgeV, hpe]
    rw [segment_symm]
  · -- the `(k-1)`-th edge is the right side of the corner cell
    refine ⟨k - 1, hkp, ?_⟩
    have hk1' : k - 1 + 1 = k := by omega
    have hpt1 : W.pt (k - 1) = W.c • gpt (p.1, p.2 - 1) := by
      rw [LWalk.pt, h1, Complex.real_smul]
      congr 2
      ext <;> simp <;> omega
    have hpt2 : W.pt (k - 1 + 1) = W.c • gpt p := by
      rw [LWalk.pt, hk1', hp, Complex.real_smul]
    rw [show W.edge (k - 1) = segPath (W.pt (k - 1)) (W.pt (k - 1 + 1)) from rfl,
      segPath_range, hpt1, hpt2, edgeV, hpe]

/-- The midpoint of an edge lies on that edge. -/
theorem midPoint_mem_edge (W : LWalk) (j : ℕ) : W.midPoint j ∈ Set.range (W.edge j) := by
  refine ⟨⟨1 / 2, by norm_num⟩, ?_⟩
  simp only [LWalk.edge, segPath, Path.segment_apply, AffineMap.lineMap_apply_module, LWalk.midPoint]
  have h : ((1 : ℝ) - 1 / 2) = 1 / 2 := by norm_num
  rw [h]
  show (1 / 2 : ℝ) • W.pt j + (1 / 2 : ℝ) • W.pt (j + 1) = (W.pt j + W.pt (j + 1)) / 2
  rw [Complex.real_smul, Complex.real_smul, add_div]
  have h2 : (((1:ℝ)/2 : ℝ) : ℂ) = (2 : ℂ)⁻¹ := by norm_num
  congr 1
  · rw [h2]; ring_nf
  · rw [h2]; ring_nf

/-- **Half-ball at the midpoint of a canonical vertical edge.**  The points of the ball of radius
`c/4` around the midpoint of `edgeV c q`, off the edge itself, lie in one of the two adjacent
cells. -/
theorem ball_midV_subset_cells {c : ℝ} (hc : 0 < c) {q : ℤ × ℤ} :
    Metric.ball (midV c q) (c / 4) \ edgeV c q
      ⊆ unitCell c (q.1 - 1, q.2) ∪ unitCell c q := by
  intro z hz
  rw [Set.mem_sdiff] at hz
  obtain ⟨hzball, hzedge⟩ := hz
  rw [Metric.mem_ball] at hzball
  have hre : -(c / 4) < z.re - (q.1 : ℝ) * c ∧ z.re - (q.1 : ℝ) * c < c / 4 := by
    rw [← abs_lt, ← midV_re]
    exact lt_of_le_of_lt (abs_re_sub_le_dist _ _) hzball
  have him : -(c / 4) < z.im - ((q.2 : ℝ) + 1 / 2) * c ∧
      z.im - ((q.2 : ℝ) + 1 / 2) * c < c / 4 := by
    rw [← abs_lt, ← midV_im]
    exact lt_of_le_of_lt (abs_im_sub_le_dist _ _) hzball
  rcases lt_trichotomy z.re ((q.1 : ℝ) * c) with hlt | heq | hgt
  · left
    rw [mem_cell]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h1 : (((q.1 - 1 : ℤ)) : ℝ) * c = (q.1 : ℝ) * c - c := by push_cast; ring
      rw [h1]; nlinarith [hre.1, hc]
    · have h1 : ((((q.1 - 1 : ℤ)) : ℝ) + 1) * c = (q.1 : ℝ) * c := by push_cast; ring
      rw [h1]; exact hlt
    · nlinarith [him.1, hc]
    · nlinarith [him.2, hc]
  · exfalso
    apply hzedge
    rw [edgeV, segment_eq_image]
    refine ⟨z.im / c - (q.2 : ℝ), ⟨?_, ?_⟩, ?_⟩
    · have h1 : (q.2 : ℝ) ≤ z.im / c := by
        rw [le_div_iff₀ (by linarith : (0:ℝ) < c)]
        nlinarith [him.1, hc]
      linarith
    · have h1 : z.im / c ≤ (q.2 : ℝ) + 1 := by
        rw [div_le_iff₀ (by linarith : (0:ℝ) < c)]
        nlinarith [him.2, hc]
      linarith
    · set t : ℝ := z.im / c - (q.2 : ℝ) with ht
      rw [show (fun θ : ℝ => (1 - θ) • (c • gpt q) + θ • (c • gpt (q + (0, 1)))) t
          = (1 - t) • (c • gpt q) + t • (c • gpt (q + (0, 1))) from rfl]
      apply Complex.ext
      · rw [re_interp_smul_gpt, heq]
        have h2 : (((q + (0, 1)).1 : ℤ) : ℝ) = (q.1 : ℝ) := by simp
        rw [h2]
        ring
      · rw [im_interp_smul_gpt, ht]
        have h2 : (((q + (0, 1)).2 : ℤ) : ℝ) = (q.2 : ℝ) + 1 := by simp
        rw [h2]
        field_simp
        ring
  · right
    rw [mem_cell]
    refine ⟨hgt, ?_, ?_, ?_⟩
    · have h1 : ((q.1 : ℝ) + 1) * c = (q.1 : ℝ) * c + c := by ring
      rw [h1]; nlinarith [hre.2, hc]
    · nlinarith [him.1, hc]
    · nlinarith [him.2, hc]

/-- **The corner cell at the lex-max vertex is on the bounded side.**  If `W` is a simple closed
lattice walk, `2 < W.n`, and `p = W.v k` is lexicographically maximal among the vertices, with
`1 ≤ k` and `k + 1 ≤ W.n`, then the cell SW of `p` — the cell that the corner move of the peel
cuts off — lies in the bounded side `S.V`. -/
theorem unitCell_corner_subset_V {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ W.n)
    (hmax : ∀ j, j ≤ W.n → ((W.v j).1 : ℝ) * W.c ≤ ((W.v k).1 : ℝ) * W.c)
    (hlex : ∀ j, j ≤ W.n → ((W.v j).1 < (W.v k).1) ∨
      ((W.v j).1 = (W.v k).1 ∧ (W.v j).2 ≤ (W.v k).2))
    (hW : W.IsSimple) (hn : 4 ≤ W.n) :
    unitCell W.c (W.v k - (1, 1)) ⊆ S.V := by
  classical
  set p : ℤ × ℤ := W.v k with hp
  set q : ℤ × ℤ := (p.1, p.2 - 1) with hq
  have hcorner : p - (1, 1) = (q.1 - 1, q.2) := by
    rw [hq]; ext <;> simp
  by_contra hnot
  -- the corner cell is in the unbounded side
  have hCU : unitCell W.c (q.1 - 1, q.2) ⊆ S.U := by
    rw [← hcorner]
    rcases cell_subset_U_or_V W S (p - (1, 1)) with h | h
    · exact h
    · exact absurd h hnot
  -- the cell east of the right side of the corner cell is in the unbounded side
  have hEU : unitCell W.c q ⊆ S.U := by
    refine subset_trans ?_ (halfplane_subset_U (W := W) (S := S) (k := k) (le_of_lt (by omega)) hmax)
    intro z hz
    rw [mem_cell] at hz
    rw [hq] at hz
    exact hz.1
  -- the right side of the corner cell is a walk edge
  obtain ⟨j, hj, hje⟩ := exists_edgeV_corner (W := W) hk1 hk2 hp hlex hW (by omega)
  -- local structure at its midpoint
  have hball := exists_ball_inter_edge W hj
  -- the midpoint is on the trace, hence in the closure of the bounded side
  have hwmem : W.midPoint j ∈ Set.range (W.edge j) := midPoint_mem_edge W j
  have hwcurve : W.midPoint j ∈ Set.range W.curve :=
    edge_range_subset_curve W hj hwmem
  have hwcl : W.midPoint j ∈ closure S.V := by
    have h1 : W.midPoint j ∈ frontier S.V := by
      rw [frontier_V_eq_range hW hn S]
      exact hwcurve
    exact frontier_subset_closure h1
  obtain ⟨v, hvV, hvdist⟩ :=
    Metric.mem_closure_iff.mp hwcl (W.c / 4) (by linarith [W.cpos])
  -- `v` is not on the trace
  have hvnot : v ∉ Set.range W.curve := by
    have h : v ∈ (W.toPlaneCurve.trace)ᶜ := by
      rw [← S.union_eq]
      exact Or.inr hvV
    exact h
  have hvnotedge : v ∉ edgeV W.c q := by
    rw [← hje]
    exact fun hc => hvnot (edge_range_subset_curve W hj hc)
  -- so `v` lies in one of the two cells
  have hmid : W.midPoint j = midV W.c q := midPoint_eq_midV_of_range hj hje
  have hvcells : v ∈ unitCell W.c (q.1 - 1, q.2) ∪ unitCell W.c q := by
    refine ball_midV_subset_cells W.cpos (q := q) ?_
    rw [Set.mem_sdiff, Metric.mem_ball, dist_comm, ← hmid]
    exact ⟨hvdist, hvnotedge⟩
  rcases hvcells with h | h
  · exact Set.disjoint_left.mp S.disjoint_UV (hCU h) hvV
  · exact Set.disjoint_left.mp S.disjoint_UV (hEU h) hvV

end LWalk

end

end Work.Smooth.JordanSeparation
