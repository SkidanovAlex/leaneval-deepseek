import Mathlib
import Submission.Work.Smooth.SphereJordan.outFrontierPath
import Submission.Work.Smooth.SphereJordan.jsepExterior

/-!
# The frontier of the component-union is inside the frontier of the whole union

`Work.Smooth.SphereJordan.frontierComponentUnionSubset`: for a finite set `P` of centres, a common
radius `r > 0`, a point `z` of the open union, `B` the component of `z` in that open union, and
`Q` the set of balls of `P` contained in `B`, the frontier of the closed union over `Q` is contained
in the frontier of the closed union over `P`.

This is one of the two inputs of the assembly of `frontierCurveOfOpenBallUnionAux`; it is proved
here sorry-free.  The mathematical content is that no frontier point of the small union can be an
*interior* point of the big union: a ball of `P` meeting `B` lies in `B` hence in `Q`, so a frontier
point `x` of the small union that were interior to the big union would have all balls through it
pairwise tangent (at most two, mutually antipodal centres), and then the perpendicular direction at
`x` is off the union — contradicting interiority.
-/

namespace Work.Smooth.SphereJordan

open Set

noncomputable section

theorem paradist {a b : ℂ} : ‖a + b‖ ^ 2 = 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 - ‖a - b‖ ^ 2 := by
  rw [norm_add_sq_real, norm_sub_sq_real]; ring

theorem inner_I_mul_self (a : ℂ) : inner ℝ a (Complex.I * a) = 0 := by
  rw [Complex.inner]
  have h : Complex.I * a * starRingEnd ℂ a = Complex.I * ((Complex.normSq a : ℝ) : ℂ) := by
    rw [show Complex.I * a * starRingEnd ℂ a = Complex.I * (a * starRingEnd ℂ a) by ring,
      Complex.mul_conj]
  rw [h]; simp

theorem norm_I_mul (a : ℂ) : ‖Complex.I * a‖ = ‖a‖ := by
  rw [norm_mul, Complex.norm_I, one_mul]

theorem norm_add_smul_I_sq (a : ℂ) (ρ : ℝ) :
    ‖a + (ρ : ℂ) * (Complex.I * a)‖ ^ 2 = (1 + ρ ^ 2) * ‖a‖ ^ 2 := by
  have hsmul : (ρ : ℂ) * (Complex.I * a) = ρ • (Complex.I * a) := rfl
  rw [hsmul, norm_add_sq_real, real_inner_smul_right, inner_I_mul_self]
  have h2 : ‖ρ • (Complex.I * a)‖ ^ 2 = ρ ^ 2 * ‖a‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_I_mul]
  rw [h2]; ring

theorem ball_inter_ball_of_dist_lt {r : ℝ} {w w' : ℂ} (h : dist w w' < 2 * r) :
    (Metric.ball w r ∩ Metric.ball w' r).Nonempty := by
  have hnorm : ‖w - w'‖ < 2 * r := by rw [← dist_eq_norm]; exact h
  refine ⟨(w + w') / 2, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm]
    have h1 : (w + w') / 2 - w = (w' - w) / 2 := by ring
    rw [h1, norm_div, norm_sub_rev]
    have h2 : ‖((2 : ℂ))‖ = 2 := by norm_num
    rw [h2]; linarith
  · rw [Metric.mem_ball, dist_eq_norm]
    have h1 : (w + w') / 2 - w' = (w - w') / 2 := by ring
    rw [h1, norm_div]
    have h2 : ‖((2 : ℂ))‖ = 2 := by norm_num
    rw [h2]; linarith

theorem eq_two_mul_sub_of_dists {x w w' : ℂ} {r : ℝ} (h1 : dist x w = r) (h2 : dist x w' = r)
    (h3 : dist w w' = 2 * r) : w' = 2 * x - w := by
  have hn1 : ‖w - x‖ = r := by rw [← dist_eq_norm, dist_comm]; exact h1
  have hn2 : ‖w' - x‖ = r := by rw [← dist_eq_norm, dist_comm]; exact h2
  have hn3 : ‖(w - x) - (w' - x)‖ = 2 * r := by
    rw [show (w - x) - (w' - x) = w - w' by ring, ← dist_eq_norm]; exact h3
  have hpar := paradist (a := w - x) (b := w' - x)
  rw [hn1, hn2, hn3] at hpar
  have hzero : ‖(w - x) + (w' - x)‖ = 0 := by
    have h : ‖(w - x) + (w' - x)‖ ^ 2 = 0 := by nlinarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
  have hsum : (w - x) + (w' - x) = 0 := norm_eq_zero.mp hzero
  have hA : w - x = -(w' - x) := by rw [add_eq_zero_iff_eq_neg] at hsum; exact hsum
  have hB : w' - x = -(w - x) := by rw [hA]; ring
  have hC : w' = x + -(w - x) := by rw [← hB]; ring
  rw [hC]; ring

/-- **The frontier of the component-union is inside the frontier of the whole union.** -/
theorem frontierComponentUnionSubset_of_mem (P : Finset ℂ) (B : Set ℂ) {r : ℝ} (hr : 0 < r)
    {z : ℂ} (hz : z ∈ ⋃ w ∈ P, Metric.ball w r)
    (hB : B = connectedComponentIn (⋃ w ∈ P, Metric.ball w r) z) (Q : Finset ℂ)
    (hQsub : ∀ w ∈ Q, w ∈ P) (hQ : ∀ w ∈ Q, Metric.ball w r ⊆ B)
    (hQmax : ∀ w ∈ P, Metric.ball w r ⊆ B → w ∈ Q) :
    frontier (⋃ w ∈ Q, Metric.closedBall w r) ⊆ frontier (⋃ w ∈ P, Metric.closedBall w r) := by
  classical
  have hzB : z ∈ B := by rw [hB]; exact mem_connectedComponentIn hz
  have hBpre : IsPreconnected B := hB ▸ isPreconnected_connectedComponentIn
  have hballB : ∀ w ∈ P, Metric.ball w r ⊆ B ∨ Disjoint (Metric.ball w r) B := by
    intro w hwP
    by_cases hne : (Metric.ball w r ∩ B).Nonempty
    · left
      obtain ⟨y, hy1, hy2⟩ := hne
      have hpre : IsPreconnected (Metric.ball w r ∪ B) :=
        IsPreconnected.union y hy1 hy2 Metric.isPreconnected_ball hBpre
      have hsub : Metric.ball w r ∪ B ⊆ ⋃ w ∈ P, Metric.ball w r := by
        rintro t (ht | ht)
        · exact Set.mem_iUnion₂.mpr ⟨w, hwP, ht⟩
        · exact connectedComponentIn_subset _ z (hB ▸ ht)
      intro t ht
      exact hB ▸ hpre.subset_connectedComponentIn (Or.inr hzB) hsub (Or.inl ht)
    · right
      exact Set.disjoint_left.mpr fun t ht1 ht2 => hne ⟨t, ht1, ht2⟩
  have hQmem : ∀ w ∈ P, ((Metric.ball w r ∩ B).Nonempty ↔ w ∈ Q) := by
    intro w hwP
    constructor
    · intro hne
      rcases hballB w hwP with h | h
      · exact hQmax w hwP h
      · exact absurd hne (by rw [Set.disjoint_iff_inter_eq_empty.mp h]; exact Set.not_nonempty_empty)
    · intro hwQ
      exact ⟨w, Metric.mem_ball_self hr, hQ w hwQ (Metric.mem_ball_self hr)⟩
  have hQclosed : IsClosed (⋃ w ∈ Q, Metric.closedBall w r) :=
    isClosed_biUnion_finset fun w _ => Metric.isClosed_closedBall
  intro x hx
  have hxQ : x ∈ ⋃ w ∈ Q, Metric.closedBall w r := hQclosed.closure_eq ▸ hx.1
  have hxQni : x ∉ interior (⋃ w ∈ Q, Metric.closedBall w r) := hx.2
  obtain ⟨w0, hw0Q, hxw0⟩ := Set.mem_iUnion₂.mp hxQ
  have hw0P : w0 ∈ P := hQsub w0 hw0Q
  have hw0sub : Metric.ball w0 r ⊆ B := hQ w0 hw0Q
  have hxclB : x ∈ closure B := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hxr : ‖x - w0‖ ≤ r := by
      have h := Metric.mem_closedBall.mp hxw0
      rwa [dist_eq_norm] at h
    set δ : ℝ := min (1/2) (ε / (2 * (r + 1))) with hδdef
    have hδpos : 0 < δ := lt_min (by norm_num) (by positivity)
    have hδle2 : δ ≤ ε / (2 * (r + 1)) := min_le_right _ _
    refine ⟨w0 + (1 - δ) * (x - w0), ?_, ?_⟩
    · apply hw0sub
      rw [Metric.mem_ball, dist_eq_norm]
      have h1 : w0 + (1 - δ) * (x - w0) - w0 = (1 - δ) * (x - w0) := by ring
      rw [h1, norm_mul]
      have h3 : (1 - δ : ℂ) = ((1 - δ : ℝ) : ℂ) := by push_cast; ring
      rw [h3, Complex.norm_real, Real.norm_eq_abs]
      have hδle : δ ≤ 1 / 2 := min_le_left _ _
      rw [abs_of_pos (by linarith)]
      nlinarith
    · rw [dist_eq_norm]
      have h1 : x - (w0 + (1 - δ) * (x - w0)) = δ * (x - w0) := by ring
      rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδpos]
      have hr1 : (0 : ℝ) < 2 * (r + 1) := by linarith
      have h4 : δ * (2 * (r + 1)) ≤ ε := by
        rw [le_div_iff₀ hr1] at hδle2; linarith
      nlinarith
  refine ⟨?_, ?_⟩
  · exact closure_mono (fun y hy => by
      obtain ⟨w, hw, hyw⟩ := Set.mem_iUnion₂.mp hy
      exact Set.mem_iUnion₂.mpr ⟨w, hQsub w hw, hyw⟩) hx.1
  · intro hxint
    have hA : ∀ w ∈ P, x ∉ Metric.ball w r := by
      intro w hwP hxw
      have hpos : 0 < r - dist x w := by rw [Metric.mem_ball] at hxw; linarith
      obtain ⟨y, hyB, hyx⟩ := (Metric.mem_closure_iff.mp hxclB) (r - dist x w) hpos
      have hyw : y ∈ Metric.ball w r := by
        rw [Metric.mem_ball]
        have ht : dist y w ≤ dist x y + dist x w := by
          simpa only [dist_comm y x] using dist_triangle y x w
        linarith
      have hwQ : w ∈ Q := (hQmem w hwP).mp ⟨y, hyw, hyB⟩
      exact hxQni (interior_mono (fun t ht => Set.mem_iUnion₂.mpr ⟨w, hwQ, ht⟩)
        ((Metric.ball_subset_interior_closedBall (x := w) (ε := r)) hxw))
    have hge : ∀ w ∈ P, r ≤ dist x w := by
      intro w hwP
      by_contra hlt
      rw [not_le] at hlt
      exact hA w hwP (Metric.mem_ball.mpr hlt)
    have hxw0r : dist x w0 = r :=
      le_antisymm (Metric.mem_closedBall.mp hxw0) (hge w0 hw0P)
    -- INPUT (B): the perpendicular direction of a point of the interior is off the union
    have key : ∀ w ∈ P, dist x w = r → (Metric.ball w r ⊆ B ↔ Metric.ball w0 r ⊆ B) := by
      intro w hwP hwd
      refine ⟨fun _ => hw0sub, fun hw0' => ?_⟩
      by_contra hsub
      have hdisjB : Disjoint (Metric.ball w r) B := by
        rcases hballB w hwP with h | h
        · exact absurd h hsub
        · exact h
      have hdisj : Disjoint (Metric.ball w r) (Metric.ball w0 r) := by
        rw [Set.disjoint_left]
        intro y hy1 hy2
        exact Set.disjoint_left.mp hdisjB hy1 (hw0' hy2)
      have hdist_w_w0 : dist w w0 = 2 * r := by
        have h2r : 2 * r ≤ dist w w0 := by
          by_contra hlt
          rw [not_le] at hlt
          obtain ⟨y, hy1, hy2⟩ := ball_inter_ball_of_dist_lt hlt
          exact Set.disjoint_left.mp hdisj hy1 hy2
        have hle2 : dist w w0 ≤ 2 * r := by
          calc dist w w0 ≤ dist w x + dist x w0 := dist_triangle w x w0
            _ = r + r := by rw [dist_comm w x, hwd, hxw0r]
            _ = 2 * r := by ring
        exact le_antisymm hle2 h2r
      have hmid : w = 2 * x - w0 :=
        eq_two_mul_sub_of_dists hxw0r hwd (by rw [dist_comm]; exact hdist_w_w0)
      have hthrough : ∀ w' ∈ P, dist x w' = r → w' = w ∨ w' = w0 := by
        intro w' hw'P hw'd
        by_cases hQ' : w' ∈ Q
        · have hdisj' : Disjoint (Metric.ball w' r) (Metric.ball w r) := by
            rw [Set.disjoint_left]
            intro y hy1 hy2
            exact Set.disjoint_left.mp hdisjB hy2 (hQ w' hQ' hy1)
          have h2r : 2 * r ≤ dist w' w := by
            by_contra hlt
            rw [not_le] at hlt
            obtain ⟨y, hy1, hy2⟩ := ball_inter_ball_of_dist_lt (by rw [dist_comm]; exact hlt)
            exact Set.disjoint_left.mp hdisj' hy2 hy1
          have hle2 : dist w' w ≤ 2 * r := by
            calc dist w' w ≤ dist w' x + dist x w := dist_triangle w' x w
              _ = r + r := by rw [dist_comm w' x, hw'd, hwd]
              _ = 2 * r := by ring
          have h2eq : dist w' w = 2 * r := le_antisymm hle2 h2r
          have hmid' : w' = 2 * x - w :=
            eq_two_mul_sub_of_dists hwd hw'd (by rw [dist_comm]; exact h2eq)
          exact Or.inr (by rw [hmid', hmid]; try ring)
        · have hdisjB' : Disjoint (Metric.ball w' r) B := by
            rcases hballB w' hw'P with h | h
            · exact absurd (hQmax w' hw'P h) hQ'
            · exact h
          have hdisj' : Disjoint (Metric.ball w' r) (Metric.ball w0 r) := by
            rw [Set.disjoint_left]
            intro y hy1 hy2
            exact Set.disjoint_left.mp hdisjB' hy1 (hw0sub hy2)
          have h2r : 2 * r ≤ dist w' w0 := by
            by_contra hlt
            rw [not_le] at hlt
            obtain ⟨y, hy1, hy2⟩ := ball_inter_ball_of_dist_lt hlt
            exact Set.disjoint_left.mp hdisj' hy1 hy2
          have hle2 : dist w' w0 ≤ 2 * r := by
            calc dist w' w0 ≤ dist w' x + dist x w0 := dist_triangle w' x w0
              _ = r + r := by rw [dist_comm w' x, hw'd, hxw0r]
              _ = 2 * r := by ring
          have h2eq : dist w' w0 = 2 * r := le_antisymm hle2 h2r
          have hmid' : w' = 2 * x - w0 :=
            eq_two_mul_sub_of_dists hxw0r hw'd (by rw [dist_comm]; exact h2eq)
          exact Or.inl (by rw [hmid', hmid]; try ring)
      obtain ⟨δ, hδpos, hδsub⟩ := Metric.isOpen_iff.mp isOpen_interior x hxint
      have hPne : P.Nonempty := ⟨w0, hw0P⟩
      set gapv : ℝ := P.inf' hPne (fun w' => if r < dist x w' then dist x w' - r else 1)
        with hgapvdef
      have hgapvpos : 0 < gapv := by
        obtain ⟨wq, hwq, hminq⟩ := P.exists_min_image
          (fun w' => if r < dist x w' then dist x w' - r else 1) hPne
        have hle : gapv ≤ (if r < dist x wq then dist x wq - r else 1) := by
          rw [hgapvdef]
          exact Finset.inf'_le _ hwq
        have hge : (if r < dist x wq then dist x wq - r else 1) ≤ gapv := by
          rw [hgapvdef]
          exact Finset.le_inf' hPne _ (fun b hb => hminq b hb)
        have hpos : 0 < (if r < dist x wq then dist x wq - r else 1) := by
          by_cases h : r < dist x wq
          · rw [if_pos h]; linarith
          · rw [if_neg h]; norm_num
        linarith
      have hgapvle : ∀ w' ∈ P, r < dist x w' → gapv ≤ dist x w' - r := by
        intro w' hw'P hlt
        have h1 : gapv ≤ (if r < dist x w' then dist x w' - r else 1) := by
          rw [hgapvdef]
          exact Finset.inf'_le _ hw'P
        rwa [if_pos hlt] at h1
      set ρ : ℝ := min (1 / 2) (min (gapv / 2) (δ / 2)) with hρdef
      have hρpos : 0 < ρ := lt_min (by norm_num) (lt_min (by linarith) (by linarith))
      have hρv : ρ < gapv := by
        have h1 : ρ ≤ gapv / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
        linarith
      have hρδ : ρ < δ := by
        have h1 : ρ ≤ δ / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
        linarith
      set a : ℂ := x - w0 with hadef
      have hanorm : ‖a‖ = r := by rw [hadef, ← dist_eq_norm]; exact hxw0r
      set pt : ℂ := x + ((ρ / r : ℝ) : ℂ) * (Complex.I * a) with hptdef
      have hptdist : dist x pt = ρ := by
        rw [hptdef, dist_eq_norm]
        have h1 : x - (x + ((ρ / r : ℝ) : ℂ) * (Complex.I * a)) = -(((ρ / r : ℝ) : ℂ) * (Complex.I * a)) := by ring
        have hr0 : r ≠ 0 := ne_of_gt hr
        rw [h1, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg (le_of_lt hρpos) (le_of_lt hr)), norm_I_mul, hanorm,
          div_mul_cancel₀ _ hr0]
      have hptw0 : r < dist pt w0 := by
        have h2 : ‖pt - w0‖ ^ 2 = r ^ 2 + ρ ^ 2 := by
          have h1 : pt - w0 = a + ((ρ / r : ℝ) : ℂ) * (Complex.I * a) := by rw [hptdef, hadef]; ring
          have hr0 : r ≠ 0 := ne_of_gt hr
          rw [h1, norm_add_smul_I_sq, hanorm, div_pow, add_mul, one_mul,
            div_mul_cancel₀ (ρ ^ 2) (pow_ne_zero 2 hr0)]
        have h3 : r ^ 2 < ‖pt - w0‖ ^ 2 := by rw [h2]; nlinarith [hρpos]
        rw [dist_eq_norm]
        have h4 : |r| < |‖pt - w0‖| := by rw [← sq_lt_sq]; simpa using h3
        rwa [abs_of_pos hr, abs_of_nonneg (norm_nonneg _)] at h4
      have hptw : r < dist pt w := by
        have h2 : ‖pt - w‖ ^ 2 = r ^ 2 + ρ ^ 2 := by
          have h1 : pt - w = -((x - w0) + ((-(ρ / r) : ℝ) : ℂ) * (Complex.I * (x - w0))) := by
            rw [hptdef, hmid, hadef]; push_cast; ring
          have hr0 : r ≠ 0 := ne_of_gt hr
          rw [h1, norm_neg, norm_add_smul_I_sq, hanorm, neg_sq, div_pow, add_mul, one_mul,
            div_mul_cancel₀ (ρ ^ 2) (pow_ne_zero 2 hr0)]
        have h3 : r ^ 2 < ‖pt - w‖ ^ 2 := by rw [h2]; nlinarith [hρpos]
        rw [dist_eq_norm]
        have h4 : |r| < |‖pt - w‖| := by rw [← sq_lt_sq]; simpa using h3
        rwa [abs_of_pos hr, abs_of_nonneg (norm_nonneg _)] at h4
      have houtside : pt ∉ ⋃ w' ∈ P, Metric.closedBall w' r := by
        rw [Set.mem_iUnion]
        rintro ⟨w', hw'⟩
        rw [Set.mem_iUnion] at hw'
        obtain ⟨hw'P, hmem⟩ := hw'
        have hle : dist x w' ≤ r + ρ := by
          calc dist x w' ≤ dist x pt + dist pt w' := dist_triangle x pt w'
            _ = ρ + dist pt w' := by rw [hptdist]
            _ ≤ ρ + r := by linarith [Metric.mem_closedBall.mp hmem]
            _ = r + ρ := by ring
        rcases lt_trichotomy (dist x w') r with hlt | heq | hgt
        · exact hA w' hw'P (Metric.mem_ball.mpr hlt)
        · rcases hthrough w' hw'P heq with h | h
          · rw [h] at hmem
            linarith [Metric.mem_closedBall.mp hmem, hptw]
          · rw [h] at hmem
            linarith [Metric.mem_closedBall.mp hmem, hptw0]
        · have hg := hgapvle w' hw'P hgt
          have h9 : dist pt w' ≥ dist x w' - ρ := by
            have ht := dist_triangle pt x w'
            rw [dist_comm pt x, hptdist] at ht
            linarith
          linarith [Metric.mem_closedBall.mp hmem, hg, hρv]
      have hinside : pt ∈ ⋃ w' ∈ P, Metric.closedBall w' r :=
        interior_subset (hδsub (Metric.mem_ball.mpr (by rw [dist_comm, hptdist]; exact hρδ)))
      exact houtside hinside
    -- a ball of `P \ Q` passes through `x`
    obtain ⟨w, hwP, hwnQ, hxw⟩ : ∃ w ∈ P, w ∉ Q ∧ x ∈ Metric.closedBall w r := by
      by_contra hcon
      push_neg at hcon
      have hxS : x ∉ ⋃ w ∈ P.filter (fun w => w ∉ Q), Metric.closedBall w r := by
        intro h
        obtain ⟨u, hu, hxu⟩ := Set.mem_iUnion₂.mp h
        exact hcon u (Finset.mem_filter.mp hu).1 (Finset.mem_filter.mp hu).2 hxu
      have hclosedS : IsClosed (⋃ w ∈ P.filter (fun w => w ∉ Q), Metric.closedBall w r) :=
        isClosed_biUnion_finset fun u _ => Metric.isClosed_closedBall
      have hgap : ∃ ε > 0, Metric.ball x ε ⊆
          (⋃ w ∈ P.filter (fun w => w ∉ Q), Metric.closedBall w r)ᶜ := by
        by_contra h2
        push_neg at h2
        refine hxS ?_
        rw [← hclosedS.closure_eq, Metric.mem_closure_iff]
        intro ε hε
        obtain ⟨y, hy, hys⟩ := Set.not_subset.mp (h2 ε hε)
        have hy' : dist x y < ε := by
          rw [dist_comm]; exact Metric.mem_ball.mp hy
        have hys' : y ∈ ⋃ w ∈ P.filter (fun w => w ∉ Q), Metric.closedBall w r := by
          rwa [Set.mem_compl_iff, not_not] at hys
        exact ⟨y, hys', hy'⟩
      obtain ⟨ε, hεpos, hεsub⟩ := hgap
      obtain ⟨δ, hδpos, hδsub⟩ := Metric.isOpen_iff.mp isOpen_interior x hxint
      set η : ℝ := min ε δ with hηdef
      have hηpos : 0 < η := lt_min hεpos hδpos
      have hsubQ : Metric.ball x η ⊆ ⋃ u ∈ Q, Metric.closedBall u r := by
        intro y hy
        have hyε : y ∈ Metric.ball x ε := by
          rw [Metric.mem_ball] at hy ⊢; linarith [min_le_left ε δ]
        have hyδ : y ∈ Metric.ball x δ := by
          rw [Metric.mem_ball] at hy ⊢; linarith [min_le_right ε δ]
        obtain ⟨u, huP, hyu⟩ := Set.mem_iUnion₂.mp (interior_subset (hδsub hyδ))
        by_cases huQ : u ∈ Q
        · exact Set.mem_iUnion₂.mpr ⟨u, huQ, hyu⟩
        · have hyS : y ∈ ⋃ w ∈ P.filter (fun w => w ∉ Q), Metric.closedBall w r :=
            Set.mem_iUnion₂.mpr ⟨u, Finset.mem_filter.mpr ⟨huP, huQ⟩, hyu⟩
          exact absurd (hεsub hyε) (by rwa [Set.mem_compl_iff, not_not])
      exact hxQni (interior_maximal hsubQ Metric.isOpen_ball (Metric.mem_ball_self hηpos))
    have hwr : dist x w = r := by
      have h1 : dist x w ≤ r := Metric.mem_closedBall.mp hxw
      have h2 : r ≤ dist x w := hge w hwP
      linarith
    have hnotsub : ¬ (Metric.ball w r ⊆ B) := fun h => hwnQ (hQmax w hwP h)
    exact hnotsub ((key w hwP hwr).mpr hw0sub)

end


/-- **The frontier of the component-union is inside the frontier of the whole union.** -/
theorem frontierComponentUnionSubset (P : Finset ℂ) (B : Set ℂ) {r : ℝ} (hr : 0 < r)
    {z : ℂ} (hB : B = connectedComponentIn (⋃ w ∈ P, Metric.ball w r) z) (Q : Finset ℂ)
    (hQsub : ∀ w ∈ Q, w ∈ P) (hQ : ∀ w ∈ Q, Metric.ball w r ⊆ B)
    (hQmax : ∀ w ∈ P, Metric.ball w r ⊆ B → w ∈ Q) :
    frontier (⋃ w ∈ Q, Metric.closedBall w r) ⊆
      frontier (⋃ w ∈ P, Metric.closedBall w r) := by
  by_cases hz : z ∈ ⋃ w ∈ P, Metric.ball w r
  · exact frontierComponentUnionSubset_of_mem P B hr hz hB Q hQsub hQ hQmax
  · have hBempty : B = ∅ := by
      rw [hB, connectedComponentIn_eq_empty]
      simpa using hz
    have hQempty : Q = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hwQ
      have h1 : Metric.ball w r ⊆ (∅ : Set ℂ) := by rw [← hBempty]; exact hQ w hwQ
      exact absurd (h1 (Metric.mem_ball_self hr)) (Set.notMem_empty w)
    rw [hQempty]
    simp

end Work.Smooth.SphereJordan
