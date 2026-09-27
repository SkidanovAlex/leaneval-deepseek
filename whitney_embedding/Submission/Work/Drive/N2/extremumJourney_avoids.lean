import Mathlib
import Submission.Work.Drive.N2.modelBall
import Submission.Work.Drive.N2.modelFlowDefs
import Submission.Work.Drive.N2.norm_le_of_mem_closure_modelBall

/-!
# The extremum transport is legal: the journey avoids the model ball and the forbidden set

`Work.Drive.N2.extremumJourney_avoids` is the legality lemma consumed by the extremum case of the
critical-window drawing (`Work.Drive.N2.extremumWindow_drawing`).  The data are a flow `Φ` on a
topological space `M`, a continuous level function `f`, a chart `φ` whose chart coordinates solve the
*outward* model ODE `u' = chartMult r (‖u‖²) · u` along the flow wherever the trajectory stays in the
region `C ⊇ closure (modelBall φ r)`, and a closed forbidden set `K` carrying no point of the closed
band `[c - η, c + η]` of values.  A point `x` off the ball, off `K`, with a value in the *open*
window `(c - η, c + η)` has its whole journey up to the level time `σ (c + σ η - f x)` off the ball
and off `K`, with values in the closed band.

The proof is the classical first-entry argument, run with `sInf` of the set

    B = {t ∈ [0, T] : Φ (t, x) ∈ modelBall φ r ∨ Φ (t, x) ∈ K}

of *bad* times (`T := σ (c + σ η - f x)`), assuming `B` nonempty:

* below `m := sInf B` the conditional level law applies, so `f (Φ (t,x)) = f x + σ t` there and, at
  `m` itself by continuity, `f (Φ (m,x)) = f x + σ m ∈ [c - η, c + η]`; hence `Φ (m,x) ∉ K` (else
  `hKval`) and `Φ (m,x) ∉ modelBall φ r` (else openness would produce a smaller bad time);
* consequently the bad times arbitrarily close *above* `m` are all *ball* points (the `K`-points
  near `m` are excluded by closedness of `K`), so `Φ (m,x) ∈ closure (modelBall φ r)`, whence
  `Φ (m,x) ∈ φ.source` and `‖φ (Φ (m,x))‖ = r`;
* the chart ODE, restarted at the sphere point `Φ (m,x)`, makes `s ↦ ‖φ (Φ (s, Φ (m,x)))‖²`
  monotone on `[0, ε₁]` (`hCseg` supplies the segment in `C`), hence `≥ r²` there — while a ball
  point at a time `s₀ - m ∈ (0, ε₁)` forces it to be `< r²`.  Contradiction.

The two hypotheses `hr` and `hmono` of the statement are not needed for this argument (only the
*nonnegativity* of the multiplier `chartMult r` enters, and the level law is supplied by `hlevel`).
-/

namespace Work.Drive.N2

open Set Filter Topology

variable {M : Type*} [TopologicalSpace M]

/-- The model ball of a chart is open (for a bare topological space `M`, i.e. without any manifold
structure). -/
lemma modelBall_isOpen (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (r : ℝ) :
    IsOpen (modelBall φ r) := by
  have h : modelBall φ r =
      φ.source ∩ φ ⁻¹' Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r := by
    ext y
    simp only [modelBall, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
      Metric.mem_ball, dist_eq_norm, sub_zero]
  rw [h]
  exact φ.isOpen_inter_preimage Metric.isOpen_ball

/-- Derivative of the squared norm of a curve whose chart velocity is a scalar multiple of the
curve itself: `v' = c • v` gives `d/ds ‖v s‖² = 2 c ‖v s‖²`. -/
lemma hasDerivAt_normSq_hom {v : ℝ → EuclideanSpace ℝ (Fin 2)} {c : ℝ} {t : ℝ}
    (h0 : HasDerivAt (fun s : ℝ => v s 0) (c * v t 0) t)
    (h1 : HasDerivAt (fun s : ℝ => v s 1) (c * v t 1) t) :
    HasDerivAt (fun s : ℝ => ‖v s‖ ^ 2) (2 * c * ‖v t‖ ^ 2) t := by
  have hfun : (fun s : ℝ => ‖v s‖ ^ 2) = fun s : ℝ => v s 0 ^ 2 + v s 1 ^ 2 := by
    funext s
    exact (norm_uVec (v s)).symm
  rw [hfun]
  have hsum : HasDerivAt (fun s : ℝ => v s 0 ^ 2 + v s 1 ^ 2)
      ((2 : ℝ) * v t 0 ^ (2 - 1) * (c * v t 0) + 2 * v t 1 ^ (2 - 1) * (c * v t 1)) t :=
    (h0.pow 2).add (h1.pow 2)
  have hval : (2 : ℝ) * v t 0 ^ (2 - 1) * (c * v t 0) + 2 * v t 1 ^ (2 - 1) * (c * v t 1)
      = 2 * c * ‖v t‖ ^ 2 := by
    rw [← norm_uVec (v t)]
    ring
  exact hsum.congr_deriv hval

/-- Along a curve solving the chart ODE `u' = chartMult r (‖u‖²) · u`, the squared chart norm is
monotone. -/
lemma monotoneOn_normSq_of_chartODE {v : ℝ → EuclideanSpace ℝ (Fin 2)} {r ε : ℝ}
    (h : ∀ s ∈ Set.Icc (0:ℝ) ε,
      HasDerivAt (fun u : ℝ => v u 0) (chartMult r (‖v s‖ ^ 2) * v s 0) s ∧
      HasDerivAt (fun u : ℝ => v u 1) (chartMult r (‖v s‖ ^ 2) * v s 1) s) :
    MonotoneOn (fun s : ℝ => ‖v s‖ ^ 2) (Set.Icc (0:ℝ) ε) := by
  have hd : ∀ s ∈ Set.Icc (0:ℝ) ε,
      HasDerivAt (fun u : ℝ => ‖v u‖ ^ 2) (2 * chartMult r (‖v s‖ ^ 2) * ‖v s‖ ^ 2) s :=
    fun s hs => hasDerivAt_normSq_hom (h s hs).1 (h s hs).2
  have hdiff : DifferentiableOn ℝ (fun s : ℝ => ‖v s‖ ^ 2) (Set.Icc (0:ℝ) ε) :=
    fun s hs => (hd s hs).differentiableAt.differentiableWithinAt
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f := fun s : ℝ => ‖v s‖ ^ 2)
    (f' := fun s : ℝ => 2 * chartMult r (‖v s‖ ^ 2) * ‖v s‖ ^ 2)
    (convex_Icc 0 ε) hdiff.continuousOn ?_ ?_
  · intro s hs
    rw [interior_Icc] at hs
    exact (hd s ⟨le_of_lt hs.1, le_of_lt hs.2⟩).hasDerivWithinAt
  · intro s hs
    rw [interior_Icc] at hs
    have h1 : (0:ℝ) ≤ chartMult r (‖v s‖ ^ 2) := chartMult_nonneg r _
    have h2 : (0:ℝ) ≤ ‖v s‖ ^ 2 := sq_nonneg _
    nlinarith

end Work.Drive.N2

namespace Work.Drive.N2

open Set Filter Topology

theorem extremumJourney_avoids {M : Type*} [TopologicalSpace M]
    (f : M → ℝ) {Φ : ℝ × M → M} (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    {c η r σ : ℝ} (hr : 0 < r) (hσ : σ = 1 ∨ σ = -1) {K : Set M}
    (hfcont : Continuous f) (hKclosed : IsClosed K)
    (hΦ0 : ∀ y : M, Φ (0, y) = y)
    (hΦcont : Continuous Φ)
    (hΦcomp : ∀ (a b : ℝ) (y : M), Φ (a, Φ (b, y)) = Φ (a + b, y))
    (hlevel : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t),
        Φ (u, y) ∉ Work.Drive.N2.modelBall φ r ∧ Φ (u, y) ∉ K) →
      f (Φ (t, y)) = f y + σ * t)
    (hmono : ∀ y : M, MonotoneOn (fun t : ℝ => σ * f (Φ (t, y))) (Set.Ici 0))
    (hKval : ∀ y ∈ K, η < |f y - c|)
    {C : Set M} (hCcl : closure (Work.Drive.N2.modelBall φ r) ⊆ C)
    (hsrc : closure (Work.Drive.N2.modelBall φ r) ⊆ φ.source)
    (hCseg : ∀ y ∈ closure (Work.Drive.N2.modelBall φ r), ∃ ε : ℝ, 0 < ε ∧
      ∀ t ∈ Set.Icc (0:ℝ) ε, Φ (t, y) ∈ C)
    (hODE : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), Φ (u, y) ∈ C) →
      HasDerivAt (fun s : ℝ => φ (Φ (s, y)) 0)
        (Work.Drive.N2.chartMult r (‖φ (Φ (t, y))‖ ^ 2) * φ (Φ (t, y)) 0) t ∧
      HasDerivAt (fun s : ℝ => φ (Φ (s, y)) 1)
        (Work.Drive.N2.chartMult r (‖φ (Φ (t, y))‖ ^ 2) * φ (Φ (t, y)) 1) t)
    {x : M} (hxK : x ∉ K) (hxD : x ∉ Work.Drive.N2.modelBall φ r)
    (hxband : f x ∈ Set.Ioo (c - η) (c + η)) :
    ∀ t ∈ Set.Icc (0:ℝ) (σ * (c + σ * η - f x)),
      Φ (t, x) ∉ Work.Drive.N2.modelBall φ r ∧ Φ (t, x) ∉ K ∧
        f (Φ (t, x)) ∈ Set.Icc (c - η) (c + η) := by
  have hΦx : Continuous fun t : ℝ => Φ (t, x) :=
    hΦcont.comp (continuous_id.prodMk continuous_const)
  have hWcont : Continuous fun t : ℝ => f (Φ (t, x)) := hfcont.comp hΦx
  set T : ℝ := σ * (c + σ * η - f x) with hTdef
  have hTpos : 0 < T := by
    rcases hσ with hσ | hσ
    · subst hσ; rw [hTdef]; linarith [hxband.2]
    · subst hσ; rw [hTdef]; linarith [hxband.1]
  have hband : ∀ t ∈ Set.Icc (0:ℝ) T, f x + σ * t ∈ Set.Icc (c - η) (c + η) := by
    intro t ht
    rcases hσ with hσ | hσ
    · subst hσ; rw [hTdef] at ht
      exact ⟨by linarith [ht.1, hxband.1], by linarith [ht.2]⟩
    · subst hσ; rw [hTdef] at ht
      exact ⟨by linarith [ht.2], by linarith [ht.1, hxband.2]⟩
  have hBempty : ∀ t ∈ Set.Icc (0:ℝ) T,
      Φ (t, x) ∉ Work.Drive.N2.modelBall φ r ∧ Φ (t, x) ∉ K := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨t₀, ht₀, hbad₀⟩ := hcon
    -- `hbad₀ : Φ (t₀,x) ∉ modelBall φ r → Φ (t₀,x) ∈ K`
    have hbad₀' : Φ (t₀, x) ∈ Work.Drive.N2.modelBall φ r ∨ Φ (t₀, x) ∈ K := by
      by_cases h : Φ (t₀, x) ∈ Work.Drive.N2.modelBall φ r
      · exact Or.inl h
      · exact Or.inr (hbad₀ h)
    set B : Set ℝ :=
      {t : ℝ | 0 ≤ t ∧ t ≤ T ∧
        (Φ (t, x) ∈ Work.Drive.N2.modelBall φ r ∨ Φ (t, x) ∈ K)} with hB
    have ht₀B : t₀ ∈ B := by rw [hB]; exact ⟨ht₀.1, ht₀.2, hbad₀'⟩
    have hBne : B.Nonempty := ⟨t₀, ht₀B⟩
    have hBbdd : BddBelow B := ⟨0, fun t ht => (by rw [hB] at ht; exact ht.1)⟩
    set m : ℝ := sInf B with hmdef
    have hm0 : 0 ≤ m := by
      rw [hmdef]; exact le_csInf hBne (fun b hb => (by rw [hB] at hb; exact hb.1))
    have hmT : m ≤ T := by
      have h : sInf B ≤ t₀ := csInf_le hBbdd ht₀B
      rw [hmdef]
      linarith [ht₀.2, h]
    have hle_m : ∀ t ∈ B, m ≤ t := fun t ht => by rw [hmdef]; exact csInf_le hBbdd ht
    -- below `m` the journey is good
    have hgood_lt : ∀ t : ℝ, 0 ≤ t → t < m →
        Φ (t, x) ∉ Work.Drive.N2.modelBall φ r ∧ Φ (t, x) ∉ K := by
      intro t ht0 htm
      have hnotB : t ∉ B := fun hmem => absurd (hle_m t hmem) (not_le.mpr htm)
      have hnn : ¬(Φ (t, x) ∈ Work.Drive.N2.modelBall φ r ∨ Φ (t, x) ∈ K) := fun hbad =>
        hnotB (by rw [hB]; exact ⟨ht0, by linarith [htm, hmT], hbad⟩)
      exact ⟨fun hb => hnn (Or.inl hb), fun hk => hnn (Or.inr hk)⟩
    -- `Φ (m,x)` does not lie in the ball
    have hmBall : Φ (m, x) ∉ Work.Drive.N2.modelBall φ r := by
      intro hmem
      rcases eq_or_lt_of_le hm0 with h0 | hpos
      · rw [← h0, hΦ0] at hmem
        exact hxD hmem
      · have hevA : ∀ᶠ v in nhdsWithin m (Set.Iio m),
            Φ (v, x) ∈ Work.Drive.N2.modelBall φ r :=
          Filter.Eventually.filter_mono nhdsWithin_le_nhds
            (hΦx.continuousAt ((modelBall_isOpen φ r).mem_nhds hmem))
        have hev0 : ∀ᶠ v in nhdsWithin m (Set.Iio m), 0 < v :=
          Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_gt_nhds hpos)
        have hev : ∀ᶠ v in nhdsWithin m (Set.Iio m),
            0 < v ∧ Φ (v, x) ∈ Work.Drive.N2.modelBall φ r ∧ v < m := by
          filter_upwards [hev0, hevA, self_mem_nhdsWithin] with v hv0 hvB hvm
          exact ⟨hv0, hvB, hvm⟩
        obtain ⟨v, hv0, hvB, hvm⟩ := hev.exists
        have hvB' : v ∈ B := by
          rw [hB]; exact ⟨le_of_lt hv0, by linarith [hvm, hmT], Or.inl hvB⟩
        linarith [hle_m v hvB', hvm]
    -- the level law below `m` and its limit at `m`
    have hlev : ∀ t : ℝ, 0 ≤ t → t < m → f (Φ (t, x)) = f x + σ * t := by
      intro t ht0 htm
      refine hlevel x t (fun u hu => ?_)
      rw [min_eq_left ht0, max_eq_right ht0] at hu
      exact hgood_lt u hu.1 (lt_of_le_of_lt hu.2 htm)
    have hmK : Φ (m, x) ∉ K := by
      intro hmem
      have hpos : 0 < m := by
        rcases eq_or_lt_of_le hm0 with h0 | h
        · exact absurd (by rw [← h0, hΦ0] at hmem; exact hmem) hxK
        · exact h
      have hEq : f (Φ (m, x)) = f x + σ * m := by
        have hev : (fun t : ℝ => f (Φ (t, x))) =ᶠ[nhdsWithin m (Set.Iio m)]
            (fun t : ℝ => f x + σ * t) := by
          filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds
              (eventually_gt_nhds hpos), self_mem_nhdsWithin] with t ht0 htm
          exact hlev t (le_of_lt ht0) htm
        have h1 : Tendsto (fun t : ℝ => f (Φ (t, x))) (nhdsWithin m (Set.Iio m))
            (nhds (f (Φ (m, x)))) :=
          hWcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
        have h2 : Tendsto (fun t : ℝ => f (Φ (t, x))) (nhdsWithin m (Set.Iio m))
            (nhds (f x + σ * m)) :=
          Tendsto.congr' hev.symm
            (((continuous_const.add (continuous_const.mul continuous_id)).tendsto m).mono_left
              nhdsWithin_le_nhds)
        exact tendsto_nhds_unique (l := nhdsWithin m (Set.Iio m)) h1 h2
      have hbnd := hband m ⟨hm0, hmT⟩
      have hKv := hKval (Φ (m, x)) hmem
      rw [hEq, lt_abs] at hKv
      obtain ⟨hlo, hhi⟩ := hbnd
      rcases hKv with h | h <;> linarith
    have hmNotB : m ∉ B := by
      intro hmem
      rw [hB] at hmem
      rcases hmem.2.2 with h | h
      · exact hmBall h
      · exact hmK h
    -- bad times above `m` exist
    have hBabove : ∃ r' ∈ B, m < r' := by
      obtain ⟨r', hr'B⟩ := hBne
      refine ⟨r', hr'B, lt_of_le_of_ne (hle_m r' hr'B) (fun hEq => hmNotB ?_)⟩
      rw [hEq]
      exact hr'B
    -- no `K`-point near `m` from above
    obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧
        ∀ t : ℝ, t ∈ Set.Ioo m (m + δ) → Φ (t, x) ∉ K := by
      have hevK : ∀ᶠ t in nhds m, Φ (t, x) ∉ K :=
        hΦx.continuousAt (hKclosed.isOpen_compl.mem_nhds hmK)
      obtain ⟨δ, hδ0, hδ'⟩ := Metric.eventually_nhds_iff.mp hevK
      refine ⟨δ, hδ0, fun t ht => hδ' ?_⟩
      rw [Real.dist_eq, abs_lt]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    -- ball points above `m`, arbitrarily close
    have hBallAbove : ∀ η' : ℝ, 0 < η' → η' ≤ δ →
        ∃ t ∈ Set.Ioo m (m + η'), Φ (t, x) ∈ Work.Drive.N2.modelBall φ r := by
      intro η' hη'0 hη'δ
      obtain ⟨t, htB, htlt⟩ :=
        (csInf_lt_iff hBbdd hBne).mp (by rw [← hmdef]; linarith : sInf B < m + η')
      have htm : m < t := by
        refine lt_of_le_of_ne (hle_m t htB) (fun hEq => hmNotB ?_)
        rw [hEq]
        exact htB
      have htδ : t < m + δ := lt_of_lt_of_le htlt (by linarith)
      have hnotK : Φ (t, x) ∉ K := hδ t ⟨htm, htδ⟩
      rw [hB] at htB
      exact ⟨t, ⟨htm, htlt⟩, htB.2.2.resolve_right hnotK⟩
    -- hence `Φ (m,x)` lies in the closure of the model ball
    have hcl : Φ (m, x) ∈ closure (Work.Drive.N2.modelBall φ r) := by
      rw [mem_closure_iff_nhds]
      intro U hU
      have hevU : ∀ᶠ t in nhds m, Φ (t, x) ∈ U := hΦx.continuousAt hU
      obtain ⟨δ', hδ'0, hδ'⟩ := Metric.eventually_nhds_iff.mp hevU
      obtain ⟨t, ht, htBall⟩ :=
        hBallAbove (min δ' δ / 2) (by have := lt_min hδ'0 hδ0; linarith)
          (by linarith [min_le_right δ' δ])
      have hdist : dist t m < δ' := by
        rw [Real.dist_eq, abs_lt]
        exact ⟨by linarith [ht.1], by linarith [ht.2, min_le_left δ' δ]⟩
      exact ⟨Φ (t, x), hδ' hdist, htBall⟩
    -- the chart norm at `m` is exactly `r`
    have hmemC : Φ (m, x) ∈ C := hCcl hcl
    have hmemφ : Φ (m, x) ∈ φ.source := hsrc hcl
    have hnormle : ‖φ (Φ (m, x))‖ ≤ r :=
      norm_le_of_mem_closure_modelBall φ r hsrc (Φ (m, x)) hcl
    have hnorm : ‖φ (Φ (m, x))‖ = r := by
      refine le_antisymm hnormle ?_
      by_contra hlt
      rw [not_le] at hlt
      exact hmBall (by simp only [modelBall, Set.mem_ofPred_eq]; exact ⟨hmemφ, hlt⟩)
    -- the restarted chart ODE at the sphere point
    obtain ⟨ε₁, hε₁0, hε₁⟩ := hCseg (Φ (m, x)) hcl
    have hode : ∀ s ∈ Set.Icc (0:ℝ) ε₁,
        HasDerivAt (fun u : ℝ => φ (Φ (u, Φ (m, x))) 0)
          (chartMult r (‖φ (Φ (s, Φ (m, x)))‖ ^ 2) * φ (Φ (s, Φ (m, x))) 0) s ∧
        HasDerivAt (fun u : ℝ => φ (Φ (u, Φ (m, x))) 1)
          (chartMult r (‖φ (Φ (s, Φ (m, x)))‖ ^ 2) * φ (Φ (s, Φ (m, x))) 1) s := by
      intro s hs
      refine hODE (Φ (m, x)) s (fun u hu => ?_)
      rw [min_eq_left hs.1, max_eq_right hs.1] at hu
      exact hε₁ u ⟨hu.1, le_trans hu.2 hs.2⟩
    have hmono_norm : MonotoneOn (fun s : ℝ => ‖φ (Φ (s, Φ (m, x)))‖ ^ 2)
        (Set.Icc (0:ℝ) ε₁) := monotoneOn_normSq_of_chartODE hode
    -- a ball point at a small positive time contradicts monotonicity
    obtain ⟨s₀, hs₀, hs₀Ball⟩ :=
      hBallAbove (min ε₁ δ / 2) (by have := lt_min hε₁0 hδ0; linarith)
        (by linarith [min_le_right ε₁ δ])
    have hsm0 : 0 < s₀ - m := by linarith [hs₀.1]
    have hsmε : s₀ - m < ε₁ := by linarith [hs₀.2, min_le_left ε₁ δ]
    have hrew : Φ (s₀ - m, Φ (m, x)) = Φ (s₀, x) := by
      rw [hΦcomp (s₀ - m) m x, show s₀ - m + m = s₀ by ring]
    have hge : ‖φ (Φ (0, Φ (m, x)))‖ ^ 2 ≤ ‖φ (Φ (s₀ - m, Φ (m, x)))‖ ^ 2 :=
      hmono_norm ⟨le_rfl, hε₁0.le⟩ ⟨hsm0.le, hsmε.le⟩ hsm0.le
    rw [hΦ0, hrew, hnorm] at hge
    have hlt : ‖φ (Φ (s₀, x))‖ ^ 2 < r ^ 2 := by
      have h1 : ‖φ (Φ (s₀, x))‖ < r := hs₀Ball.2
      nlinarith [norm_nonneg (φ (Φ (s₀, x)))]
    linarith
  intro t ht
  obtain ⟨h1, h2⟩ := hBempty t ht
  refine ⟨h1, h2, ?_⟩
  have hlev := hlevel x t (fun u hu => by
    rw [min_eq_left ht.1, max_eq_right ht.1] at hu
    exact hBempty u ⟨hu.1, le_trans hu.2 ht.2⟩)
  rw [hlev]
  exact hband t ht

end Work.Drive.N2
