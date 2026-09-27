import Mathlib
import Submission.Work.Drive.BoxParityAux
import Submission.Work.Drive.exists_local_normalForm
import Submission.Work.Drive.graph_region_props
import Submission.Work.Drive.crossing_of_deriv_ne_zero
import Submission.Work.Drive.exists_face_index
import Submission.Work.Drive.flowField_apply_ne_zero_of_chart
import Submission.Work.Drive.abs_sub_ge_of_abs_deriv_ge
import Submission.Work.Drive.chart_exit

/-!
# The in-box arc of a flow line through a boundary zero is bounded on the left

`in_box_arc_left` shows that the set of times `t < 0` for which the whole interval `(t,0)` is mapped
into the interior of the unit box is bounded below.  Together with `in_box_arc_right` this says that
the in-box arc of the zero set through a boundary zero is a compact arc, so that the "other
endpoint" `pairPt` of `BoxParityAux` is a boundary zero: the pairing of boundary zeros is an
involution and their number is even.

The proof is a compactness argument.  Suppose the contrary: the flow line `γ` of `flowField F`
through `b` lies in the interior of the box for *all* `t < 0`.  Then `γ` is trapped in the compact
zero set `zeroSet F` for all negative times, so a limit point `p` of `γ(-n)` exists.  Near `p` the
zero set is a graph over some coordinate `i` (the implicit function theorem / normal form), and on
that chart the `i`-th coordinate of `γ` is strictly monotone with derivative bounded away from zero
(it equals the `i`-th component of `flowField F`, which is nonzero on the chart by
`flowField_apply_ne_zero_of_chart`).  Hence every visit of `γ` to the chart ends, in backward time,
at one of the two "end points" of the chart after a bounded time — so we produce an unbounded
sequence of distinct times at which `γ` takes one of *two* fixed values.  Two of those times force
`γ` to be periodic, and then `γ 0 = b` is also attained at a negative time, where `γ` lies in the
*interior* of the box: contradiction with `b ∈ unitBoxBdry`.
-/

namespace Work.Drive

open scoped ContDiff Topology
open Set Filter

noncomputable section

theorem in_box_arc_left {m : ℕ} {F : Work.Drive.Amb m → Work.Drive.Tgt m}
    (hF : ContDiff ℝ Work.Drive.Ctop F)
    (hreg : ∀ x ∈ Submission.Drive.unitBox m, F x = 0 → Function.Surjective (fderiv ℝ F x))
    {b : Work.Drive.Amb m} (hb : b ∈ Work.Drive.bdyZeros F)
    (hface : ∃ i : Fin (m + 1), (b i = 0 ∨ b i = 1) ∧ (∀ j, j ≠ i → b j ∈ Set.Ioo (0 : ℝ) 1) ∧
      Work.Drive.flowField F b i ≠ 0)
    {ε : ℝ} (hε : ε < 0)
    (hin : ∀ t ∈ Set.Ioo ε 0,
      Work.Drive.flowCurve F hF b t ∈ interior (Submission.Drive.unitBox m)) :
    ∃ M : ℝ, ∀ t : ℝ,
      (∀ s ∈ Set.Ioo t 0,
        Work.Drive.flowCurve F hF b s ∈ interior (Submission.Drive.unitBox m)) → M ≤ t := by
  classical
  set γ : ℝ → Amb m := flowCurve F hF b with hγdef
  by_contra hcon
  push_neg at hcon
  -- `hcon : ∀ M, ∃ t, (∀ s ∈ Ioo t 0, γ s ∈ interior box) ∧ t < M`
  have hγderiv : ∀ t : ℝ, HasDerivAt γ (flowField F (γ t)) t := by
    intro t
    rw [hγdef]
    exact flowCurve_hasDerivAt F hF b t
  have hγcont : Continuous γ :=
    continuous_iff_continuousAt.mpr fun t => (hγderiv t).continuousAt
  have hFγ : ∀ t : ℝ, F (γ t) = 0 := by
    intro t
    rw [hγdef, F_flowCurve hF b t, (mem_bdyZeros.mp hb).2]
  -- the hypothesis says that the whole of `(-∞,0)` is mapped into the interior of the box
  have hmem : ∀ t : ℝ, t < 0 → γ t ∈ interior (Submission.Drive.unitBox m) := by
    intro t ht
    obtain ⟨t', ht'⟩ := hcon t
    exact ht'.1 t ⟨ht'.2, ht⟩
  have hbox_le : ∀ t : ℝ, t ≤ 0 → γ t ∈ Submission.Drive.unitBox m := by
    intro t ht
    rcases lt_or_eq_of_le ht with h | h
    · exact interior_subset (hmem t h)
    · subst h
      rw [hγdef, flowCurve_zero F hF b]
      exact (mem_bdyZeros.mp hb).1.1
  -- compactness: a limit point `p` of `γ (-n)`
  have hseq_mem : ∀ n : ℕ, γ (-(n : ℝ)) ∈ Submission.Drive.unitBox m := fun n =>
    hbox_le _ (by simp)
  obtain ⟨p, hpbox, φ, hφmono, hφtend⟩ :=
    (isCompact_unitBox m).tendsto_subseq hseq_mem
  have hFp : F p = 0 := by
    have h1 : Tendsto (fun k : ℕ => F (γ (-(φ k : ℝ)))) atTop (𝓝 (F p)) :=
      (hF.continuous.tendsto p).comp hφtend
    have h2 : (fun k : ℕ => F (γ (-(φ k : ℝ)))) = fun _ => (0 : Tgt m) := by
      funext k
      exact hFγ _
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  -- the local normal form of the zero set at `p`
  obtain ⟨i, hsurji⟩ := exists_face_index (F := F) (p := p) (hreg p hpbox hFp)
  obtain ⟨δ₀, ρ₀, η, hδ₀, hρ₀, hηcd, hηi, hηpi, hnormal, hchar⟩ :=
    exists_local_normalForm hF hFp i hsurji
  have hηc : Continuous η := hηcd.continuous
  have htube_p : ‖p - (p i) • EuclideanSpace.single i 1 - η (p i)‖ = 0 := by
    rw [hηpi]
    simp
  -- eventually `γ (-φ k)` lies in the inner chart region around `p`
  have hopen : {x : Amb m | |x i - p i| < δ₀ / 2 ∧
      ‖x - (x i) • EuclideanSpace.single i 1 - η (x i)‖ < ρ₀ / 2} ∈ 𝓝 p := by
    have hc1 : Continuous fun x : Amb m => |x i - p i| := by fun_prop
    have hc2 : Continuous fun x : Amb m =>
        ‖x - (x i) • EuclideanSpace.single i 1 - η (x i)‖ := by fun_prop
    apply IsOpen.mem_nhds
    · exact (isOpen_lt hc1 continuous_const).inter (isOpen_lt hc2 continuous_const)
    · refine ⟨?_, ?_⟩
      · simp only [sub_self, abs_zero]; linarith
      · rw [htube_p]; linarith
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (hφtend.eventually hopen)
  set qm : Amb m := (p i - δ₀ / 2) • EuclideanSpace.single i 1 + η (p i - δ₀ / 2) with hqm
  set qp : Amb m := (p i + δ₀ / 2) • EuclideanSpace.single i 1 + η (p i + δ₀ / 2) with hqp
  -- each visit to the chart, in backward time, ends at one of the two end points of the chart
  have hexit : ∀ k : ℕ, K ≤ k → ∃ a : ℝ, a < -(φ k : ℝ) ∧ (γ a = qm ∨ γ a = qp) := by
    intro k hk
    obtain ⟨h1, h2⟩ := hK k hk
    have ht0 : -(φ k : ℝ) ≤ (0 : ℝ) := by
      have : (0 : ℝ) ≤ (φ k : ℝ) := Nat.cast_nonneg (φ k)
      linarith
    obtain ⟨a, ha, hd⟩ :=
      chart_exit_of_normalForm (m := m) (F := F) hF hδ₀ hρ₀ hηc hnormal hchar hreg (γ := γ) hγderiv
        (T := 0) hbox_le (fun t _ => hFγ t) ht0 h2 h1
    exact ⟨a, ha, by simpa only [hqm, hqp] using hd⟩
  let a : ℕ → ℝ := fun k => if hk : K ≤ k then Classical.choose (hexit k hk) else 0
  have ha : ∀ k : ℕ, K ≤ k → a k < -(φ k : ℝ) ∧ (γ (a k) = qm ∨ γ (a k) = qp) := by
    intro k hk
    have := Classical.choose_spec (hexit k hk)
    simpa only [a, dif_pos hk] using this
  -- the values `a k` are unbounded below, so infinitely many of them
  set A : Set ℝ := a '' {k : ℕ | K ≤ k} with hA
  have ha_mem : ∀ k : ℕ, K ≤ k → a k ∈ A := fun k hk => ⟨k, hk, rfl⟩
  have hAk : ∀ k : ℕ, K ≤ k → a k < -(k : ℝ) := by
    intro k hk
    have h1 := (ha k hk).1
    have h2 : (k : ℝ) ≤ (φ k : ℝ) := by
      exact_mod_cast hφmono.id_le k
    linarith
  have hAinf : A.Infinite := by
    rw [← Set.not_finite]
    intro hfin
    obtain ⟨μ, hμ⟩ := hfin.bddBelow
    obtain ⟨n, hn⟩ := exists_nat_gt (-μ)
    have hKle : K ≤ K + n := Nat.le_add_right K n
    have h4 : a (K + n) < -((K + n : ℕ) : ℝ) := hAk _ hKle
    have h5 : μ ≤ a (K + n) := hμ (ha_mem _ hKle)
    have h6 : ((K : ℝ) + (n : ℝ)) = ((K + n : ℕ) : ℝ) := (Nat.cast_add K n).symm
    have h7 : ((K : ℝ) + (n : ℝ)) ≥ (n : ℝ) := by
      have : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
      linarith
    linarith
  -- `γ` takes one of two values on all of `A`, so it is not injective there
  have hnotinj : ¬ Set.InjOn γ A := by
    intro hinj
    have hsub : γ '' A ⊆ ({qm, qp} : Set (Amb m)) := by
      rintro y ⟨x, hx, rfl⟩
      rw [hA] at hx
      obtain ⟨k, hk, hkx⟩ := hx
      rw [← hkx]
      rcases (ha k hk).2 with h | h
      · exact Or.inl h
      · exact Or.inr h
    have hfin : (γ '' A).Finite :=
      Set.Finite.subset ((Set.finite_singleton qp).insert qm) hsub
    exact hAinf (Set.Finite.of_finite_image hfin hinj)
  rw [Set.InjOn] at hnotinj
  push_neg at hnotinj
  obtain ⟨x, hxA, y, hyA, hγxy, hxy⟩ := hnotinj
  -- two distinct times with the same value: `γ` is periodic
  have hper : Function.Periodic γ (x - y) := by
    have h' : flowCurve F hF b x = flowCurve F hF b y := by
      rw [← hγdef]
      exact hγxy
    have h2 := flowCurve_periodic_of_eq hF h'
    change Function.Periodic (flowCurve F hF b) (x - y)
    exact h2
  have hne' : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hkey : ∃ s : ℝ, s < 0 ∧ γ s = γ 0 := by
    rcases lt_or_gt_of_ne hne' with hlt | hgt
    · exact ⟨x - y, hlt, by simpa using (hper 0)⟩
    · exact ⟨-(x - y), by linarith, by simpa using (hper (-(x - y))).symm⟩
  obtain ⟨s, hs, hγs⟩ := hkey
  -- but `γ 0 = b` lies on the boundary of the box
  have hbint : b ∈ interior (Submission.Drive.unitBox m) := by
    have h : γ 0 ∈ interior (Submission.Drive.unitBox m) := by
      rw [← hγs]
      exact hmem s hs
    rwa [hγdef, flowCurve_zero F hF b] at h
  rw [interior_unitBox m] at hbint
  obtain ⟨j, hj⟩ : ∃ j : Fin (m + 1), b j = 0 ∨ b j = 1 := (mem_bdyZeros.mp hb).1.2
  have hj' := hbint j
  rcases hj with h | h <;> rw [h] at hj' <;> linarith [hj'.1, hj'.2]

end

end Work.Drive
