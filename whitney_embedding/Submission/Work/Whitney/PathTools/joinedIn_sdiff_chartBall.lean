import Mathlib

/-!
# Walking around a chart ball

A chart ball inside a path connected set `W` can be removed without destroying path
connectedness.
-/

namespace Work.Whitney.PathTools

open Set Metric Topology
open scoped Topology

/-- **Escaping an open set along a path.**  Let `O` be open and `B` a set with `closure B ⊆ O`.
If `x ∉ O` and `y ∈ O` are joined by a path lying in `W`, then some point of `O \ B` is joined to
`x` by a path lying in `W \ B`.

The proof looks at the first time `s` at which the extended path enters `O`: `γ s` lies in the
closure of `O` but not in `O` itself, hence not in `closure B`, so a whole neighbourhood of `s` is
mapped into the complement of `B`.  A point of `O` just after `s` then gives the desired point, and
the path restricted to `[0, t]` misses `B`. -/
theorem exists_mem_sdiff_joinedIn_compl {X : Type*} [TopologicalSpace X] {O B W : Set X}
    (hO : IsOpen O) (hclO : closure B ⊆ O)
    {x y : X} (hxO : x ∉ O) (hyO : y ∈ O) (hxy : JoinedIn W x y) :
    ∃ z ∈ O \ B, JoinedIn (W \ B) x z := by
  rcases hxy with ⟨γ, hγW⟩
  -- the times at which the extended path lies in `O`
  set S : Set ℝ := {t | γ.extend t ∈ O} with hS
  have hS1 : (1 : ℝ) ∈ S := by
    rw [hS, Set.mem_ofPred_eq, Path.extend_one]; exact hyO
  have hSne : S.Nonempty := ⟨1, hS1⟩
  have hbdd : BddBelow S := by
    refine ⟨0, ?_⟩
    intro t ht
    by_contra h
    rw [not_le] at h
    rw [hS, Set.mem_ofPred_eq] at ht
    rw [Path.extend_of_le_zero γ h.le] at ht
    exact hxO ht
  set s : ℝ := sInf S with hs
  have hs_nonneg : 0 ≤ s := by
    refine le_csInf hSne ?_
    intro t ht
    by_contra h
    rw [not_le] at h
    rw [hS, Set.mem_ofPred_eq] at ht
    rw [Path.extend_of_le_zero γ h.le] at ht
    exact hxO ht
  have hs_le_one : s ≤ 1 := by
    rw [hs]; exact csInf_le hbdd hS1
  -- the first entry point is not in `O`
  have hs_not_mem : γ.extend s ∉ O := by
    rintro hsO
    rcases eq_or_lt_of_le hs_nonneg with h0 | hpos
    · rw [← h0, Path.extend_zero] at hsO
      exact hxO hsO
    · have hev : ∀ᶠ t in 𝓝 s, γ.extend t ∈ O :=
        (γ.continuous_extend.tendsto s).eventually (hO.mem_nhds hsO)
      obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hev
      have hmem : s - ε / 2 ∈ S := by
        rw [hS, Set.mem_ofPred_eq]
        exact hεsub (by
          rw [Metric.mem_ball, Real.dist_eq, abs_lt]
          constructor <;> linarith)
      have := csInf_le hbdd hmem
      rw [← hs] at this
      linarith
  -- the first entry point lies in the closure of `O`
  have hs_closure : γ.extend s ∈ closure O := by
    rw [_root_.mem_closure_iff]
    intro U hU hxU
    have hpre : γ.extend ⁻¹' U ∈ 𝓝 s :=
      (γ.continuous_extend.tendsto s).eventually (hU.mem_nhds hxU)
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hpre
    have hsδ : sInf S < s + ε := by rw [← hs]; linarith
    obtain ⟨a, haS, ha⟩ := exists_lt_of_csInf_lt hSne hsδ
    have haO : γ.extend a ∈ O := by rwa [hS, Set.mem_ofPred_eq] at haS
    have hsa : s ≤ a := by
      have h := csInf_le hbdd haS
      rwa [← hs] at h
    refine ⟨γ.extend a, hεsub ?_, haO⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hs_not_closureB : γ.extend s ∉ closure B := fun h => hs_not_mem (hclO h)
  -- a neighbourhood of `γ.extend s` disjoint from `B`
  have hpre2 : γ.extend ⁻¹' (closure B)ᶜ ∈ 𝓝 s :=
    (γ.continuous_extend.tendsto s).eventually
      (isClosed_closure.isOpen_compl.mem_nhds hs_not_closureB)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hpre2
  -- a time of `S` inside the window
  have hsδ' : sInf S < s + δ := by rw [← hs]; linarith
  obtain ⟨a, haS, ha⟩ := exists_lt_of_csInf_lt hSne hsδ'
  have haO : γ.extend a ∈ O := by rwa [hS, Set.mem_ofPred_eq] at haS
  have hsa : s ≤ a := by
    have h := csInf_le hbdd haS
    rwa [← hs] at h
  have hsa' : s < a := by
    rcases lt_or_eq_of_le hsa with h | h
    · exact h
    · exact absurd (h ▸ haO) hs_not_mem
  have hslt1 : s < 1 := lt_of_le_of_ne hs_le_one fun h => hs_not_mem (by
    rw [h, Path.extend_one]; exact hyO)
  set t : ℝ := min a 1 with ht
  have ht_gt : s < t := lt_min hsa' hslt1
  have ht_lt : t < s + δ := lt_of_le_of_lt (min_le_left _ _) ha
  have ht_le : (0 : ℝ) ≤ t := le_of_lt (lt_of_le_of_lt hs_nonneg ht_gt)
  have ht_le_one : t ≤ 1 := by rw [ht]; exact min_le_right _ _
  have htS : γ.extend t ∈ O := by
    rcases le_total a 1 with h | h
    · rw [ht, min_eq_left h]; exact haO
    · rw [ht, min_eq_right h, Path.extend_one]; exact hyO
  -- the truncated path stays in the complement of `B`
  have htrunc : ∀ r : unitInterval, γ.extend ((r : ℝ) * t) ∈ W \ B := by
    intro r
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := r.2.1
    have hr1 : (r : ℝ) ≤ 1 := r.2.2
    have hrt0 : 0 ≤ (r : ℝ) * t := mul_nonneg hr0 ht_le
    have hrt1 : (r : ℝ) * t ≤ 1 := by nlinarith
    have hrtW : γ.extend ((r : ℝ) * t) ∈ W := by
      rw [Path.extend_apply γ (show (r : ℝ) * t ∈ Set.Icc (0 : ℝ) 1 from ⟨hrt0, hrt1⟩)]
      exact hγW ⟨(r : ℝ) * t, hrt0, hrt1⟩
    have hrtB : γ.extend ((r : ℝ) * t) ∉ B := by
      rcases lt_or_ge ((r : ℝ) * t) s with h | h
      · intro hmem
        have hmemS : (r : ℝ) * t ∈ S := by
          rw [hS, Set.mem_ofPred_eq]
          exact hclO (subset_closure hmem)
        have := csInf_le hbdd hmemS
        rw [← hs] at this
        linarith
      · intro hmem
        have hmem' : γ.extend ((r : ℝ) * t) ∈ (closure B)ᶜ := hδsub (by
          rw [Metric.mem_ball, Real.dist_eq, abs_lt]
          constructor
          · linarith
          · have : (r : ℝ) * t ≤ t := by nlinarith
            linarith)
        exact hmem' (subset_closure hmem)
    exact ⟨hrtW, by simpa using hrtB⟩
  refine ⟨γ.extend t, ⟨htS, ?_⟩, ?_⟩
  · have hmem : γ.extend t ∈ (closure B)ᶜ := hδsub (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith)
    exact fun h => hmem (subset_closure h)
  · refine JoinedIn.ofLine (f := fun r : ℝ => γ.extend (r * t)) ?_ ?_ ?_ ?_
    · fun_prop
    · show γ.extend (0 * t) = x
      rw [zero_mul, Path.extend_zero]
    · show γ.extend (1 * t) = γ.extend t
      rw [one_mul]
    · intro z hz
      obtain ⟨u, hu, huz⟩ := hz
      rw [← huz]
      exact htrunc ⟨u, hu⟩


/-- **A slightly larger ball around a closed ball inside an open set.** -/
theorem exists_ball_subset_of_closedBall_subset {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E] (z : E) {r : ℝ} (hr : 0 < r) {U : Set E}
    (hU : IsOpen U) (hKU : Metric.closedBall z r ⊆ U) :
    ∃ ρ : ℝ, r < ρ ∧ Metric.ball z ρ ⊆ U := by
  obtain ⟨δ, hδ, hsub⟩ :=
    IsCompact.exists_cthickening_subset_open (isCompact_closedBall z r) hU hKU
  refine ⟨r + δ, by linarith, fun y hy => hsub ?_⟩
  rw [Metric.mem_ball] at hy
  rw [Metric.cthickening_eq_biUnion_closedBall (Metric.closedBall z r) (le_of_lt hδ),
    isClosed_closedBall.closure_eq]
  rcases lt_or_ge (dist y z) r with h | h
  · refine Set.mem_iUnion₂.mpr ⟨y, Metric.mem_closedBall.mpr h.le, ?_⟩
    exact Metric.mem_closedBall_self (le_of_lt hδ)
  · have hyz : 0 < dist y z := lt_of_lt_of_le hr h
    set w : E := z + ((r / dist y z) • (y - z)) with hw
    have hnorm : ‖y - z‖ = dist y z := (dist_eq_norm y z).symm
    have hwK : w ∈ Metric.closedBall z r := by
      rw [Metric.mem_closedBall]
      have h1 : w - z = (r / dist y z) • (y - z) := by rw [hw]; abel
      rw [dist_eq_norm, h1, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity), hnorm, div_mul_cancel₀ _ (ne_of_gt hyz)]
    have hdist : dist y w < δ := by
      have hc : (1 : ℝ) - r / dist y z = (dist y z - r) / dist y z := by
        field_simp
      have h1 : y - w = ((dist y z - r) / dist y z) • (y - z) := by
        rw [hw, sub_add_eq_sub_sub, ← hc]
        rw [sub_smul, one_smul]
      rw [dist_eq_norm, h1, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity), hnorm, div_mul_cancel₀ _ (ne_of_gt hyz)]
      linarith
    exact Set.mem_iUnion₂.mpr ⟨w, hwK, Metric.mem_closedBall.mpr hdist.le⟩

/-- **The annulus `r ≤ ‖x - z‖ < ρ` is path connected** in dimension `≥ 2`. -/
theorem annulus_isPathConnected {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hrank : 1 < Module.rank ℝ E) (z : E) {r ρ : ℝ} (hr : 0 < r) (hrρ : r < ρ) :
    IsPathConnected (Metric.ball z ρ \ Metric.ball z r) := by
  have hsphere : IsPathConnected (Metric.sphere (0 : E) 1) :=
    isPathConnected_sphere hrank (0 : E) zero_le_one
  have hIco : IsPathConnected (Set.Ico r ρ) :=
    (convex_Ico r ρ).isPathConnected ⟨r, le_rfl, hrρ⟩
  have hprod : IsPathConnected (Metric.sphere (0 : E) 1 ×ˢ Set.Ico r ρ) := hsphere.prod hIco
  have hcont : ContinuousOn (fun p : E × ℝ => z + p.2 • p.1)
      (Metric.sphere (0 : E) 1 ×ˢ Set.Ico r ρ) := by fun_prop
  have himg : (fun p : E × ℝ => z + p.2 • p.1) '' (Metric.sphere (0 : E) 1 ×ˢ Set.Ico r ρ)
      = Metric.ball z ρ \ Metric.ball z r := by
    ext x
    constructor
    · rintro ⟨⟨θ, s⟩, ⟨hθ, hs⟩, rfl⟩
      rw [Metric.mem_sphere] at hθ
      obtain ⟨hsr, hsρ⟩ := hs
      show z + s • θ ∈ Metric.ball z ρ \ Metric.ball z r
      have hsn : ‖s‖ = s := Real.norm_of_nonneg (le_trans hr.le hsr)
      have hθn : ‖θ‖ = 1 := by simpa [dist_eq_norm] using hθ
      have hdist : dist (z + s • θ) z = s := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hsn, hθn, mul_one]
      rw [Set.mem_sdiff]
      refine ⟨Metric.mem_ball.mpr ?_, ?_⟩
      · rw [hdist]; exact hsρ
      · intro hmem
        rw [Metric.mem_ball, hdist] at hmem
        exact absurd hmem (not_lt.mpr hsr)
    · intro hx
      obtain ⟨hxρ, hxr⟩ := hx
      rw [Metric.mem_ball] at hxρ
      rw [Metric.mem_ball, not_lt] at hxr
      rw [dist_eq_norm] at hxρ hxr
      have hpos : 0 < ‖x - z‖ := lt_of_lt_of_le hr hxr
      refine ⟨(‖x - z‖⁻¹ • (x - z), ‖x - z‖), ⟨?_, hxr, hxρ⟩, ?_⟩
      · rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul,
          Real.norm_of_nonneg (by positivity), inv_mul_cancel₀ (ne_of_gt hpos)]
      · show z + ‖x - z‖ • (‖x - z‖⁻¹ • (x - z)) = x
        rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hpos), one_smul]
        abel
  rw [← himg]
  exact hprod.image' hcont

/-- **Removing a chart ball from a path connected set.**  Abstract form. -/
theorem joinedIn_sdiff_of_isOpen_of_closure_subset {X : Type*} [TopologicalSpace X]
    {W B : Set X} (hW : IsPathConnected W) {O : Set X} (hO : IsOpen O)
    (hclO : closure B ⊆ O) (hOpc : IsPathConnected (O \ B)) (hOsub : O \ B ⊆ W \ B)
    {u v : X} (hu : u ∈ W \ B) (hv : v ∈ W \ B) : JoinedIn (W \ B) u v := by
  obtain ⟨d, hd⟩ := hOpc.nonempty
  have key : ∀ x ∈ W \ B, JoinedIn (W \ B) x d := by
    intro x hx
    rcases hx with ⟨hxW, hxB⟩
    by_cases hxO : x ∈ O
    · exact (hOpc.joinedIn x ⟨hxO, hxB⟩ d hd).mono hOsub
    · obtain ⟨z', hz', hxz'⟩ := exists_mem_sdiff_joinedIn_compl hO hclO hxO hd.1
        (hW.joinedIn x hxW d (hOsub hd).1)
      exact hxz'.trans ((hOpc.joinedIn z' hz' d hd).mono hOsub)
  exact (key u hu).trans (key v hv).symm

/-- **Walking around a chart ball.**  If `W` is path connected, `c` is a chart whose source lies
in `W`, and `c.symm '' ball z r` is a chart ball whose closure lies in the chart target, then
`W` with that chart ball removed is still path connected. -/
theorem joinedIn_sdiff_chartBall {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    {W : Set M} (hW : IsPathConnected W)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))} {z : EuclideanSpace ℝ (Fin 2)}
    {r : ℝ} (hr : 0 < r) (hcl : Metric.closedBall z r ⊆ c.target)
    (hsrc : c.source ⊆ W)
    {u v : M} (hu : u ∈ W \ c.symm '' Metric.ball z r)
    (hv : v ∈ W \ c.symm '' Metric.ball z r) :
    JoinedIn (W \ c.symm '' Metric.ball z r) u v := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 2)) := by
    rw [← Module.finrank_eq_rank ℝ (EuclideanSpace ℝ (Fin 2)), finrank_euclideanSpace]
    simp
  -- a slightly larger chart ball, still inside the chart target
  obtain ⟨ρ, hrρ, hρsub⟩ := exists_ball_subset_of_closedBall_subset z hr c.open_target hcl
  have hOopen : IsOpen (c.symm '' Metric.ball z ρ) :=
    c.isOpen_image_symm_of_subset_target Metric.isOpen_ball hρsub
  -- the closure of the removed ball lies in the larger ball
  have hclO : closure (c.symm '' Metric.ball z r) ⊆ c.symm '' Metric.ball z ρ := by
    have hclosed : IsClosed (c.symm '' Metric.closedBall z r) :=
      (IsCompact.image_of_continuousOn (isCompact_closedBall z r)
        (c.continuousOn_symm.mono hcl)).isClosed
    refine (closure_minimal ?_ hclosed).trans ?_
    · rintro x ⟨y, hy, rfl⟩
      exact ⟨y, Metric.ball_subset_closedBall hy, rfl⟩
    · rintro x ⟨y, hy, rfl⟩
      exact ⟨y, Metric.closedBall_subset_ball hrρ hy, rfl⟩
  -- the complement of the removed ball inside the larger ball is path connected
  have hEq : c.symm '' Metric.ball z ρ \ c.symm '' Metric.ball z r
      = c.symm '' (Metric.ball z ρ \ Metric.ball z r) := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, hxy⟩, hxB⟩
      subst hxy
      exact ⟨y, ⟨hy, fun hyr => hxB ⟨y, hyr, rfl⟩⟩, rfl⟩
    · rintro ⟨y, ⟨hyρ, hyr⟩, hxy⟩
      subst hxy
      refine ⟨⟨y, hyρ, rfl⟩, fun hmem => ?_⟩
      obtain ⟨w, hw, hwy⟩ := hmem
      have hyT : y ∈ c.target := hρsub hyρ
      have hwT : w ∈ c.target := hcl (Metric.ball_subset_closedBall hw)
      have hEq' : w = y := (c.symm).injOn (by rwa [OpenPartialHomeomorph.symm_source])
        (by rwa [OpenPartialHomeomorph.symm_source]) hwy
      rw [hEq'] at hw
      exact hyr hw
  have hOpc : IsPathConnected (c.symm '' Metric.ball z ρ \ c.symm '' Metric.ball z r) := by
    rw [hEq]
    exact (annulus_isPathConnected hrank z hr hrρ).image'
      (c.continuousOn_symm.mono (fun x hx => hρsub hx.1))
  -- and it sits inside `W`
  have hOsub : c.symm '' Metric.ball z ρ \ c.symm '' Metric.ball z r
      ⊆ W \ c.symm '' Metric.ball z r := by
    rintro x ⟨hxO, hxB⟩
    obtain ⟨y, hy, hxy⟩ := hxO
    subst hxy
    exact ⟨hsrc (c.map_target (hρsub hy)), hxB⟩
  exact joinedIn_sdiff_of_isOpen_of_closure_subset hW hOopen hclO hOpc hOsub hu hv

end Work.Whitney.PathTools
