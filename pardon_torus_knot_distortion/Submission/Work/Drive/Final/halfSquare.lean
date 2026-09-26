import Mathlib
import Submission.Work.Drive.Final.exists_faceMonotoneData

/-!
# The half-square is path connected

`Work.Drive.Final.halfSquare`: if `V : ℝ × ℝ → ℝ` is smooth at the origin, vanishes there, and has
Fréchet derivative `c • fst` with `c ≠ 0` (so that `V` is a submersion at `0`), then for all
sufficiently small `δ` the set `{V > 0}` meets the open square `(-δ,δ) × (-δ,δ)` in a path connected
set.

The proof is elementary.  Choose `δ` so small that on the square

* `V p - c * p.1` is small compared with `‖p‖` (differentiability at the origin), and
* `fderiv ℝ V` stays close to `fderiv ℝ V 0 = c • fst`, so that the sign of the partial derivative
  `∂₁V = fderiv ℝ V p (1,0)` is the sign of `c` (continuity of the derivative, `C¹` at the origin).

Then for each fixed `y` the function `x ↦ V (x,y)` is monotone (increasing if `c > 0`, decreasing
otherwise) on the square, so the horizontal slice `{V > 0}` is an interval.  Pick a "spine" point
`e = ±δ/2` on the side the derivative points to; `V (e,y) > 0` for all `|y| < δ` by the smallness
estimate.  Every point of the region is then joined to `(e,0)` by an L-shaped path: horizontally at
constant height to `(e, y)` (monotonicity gives positivity on the whole horizontal segment), then
vertically to `(e,0)`.
-/

namespace Work.Drive.Final

open Set Filter
open scoped Topology

/-- The norm on `ℝ × ℝ` is the sup norm. -/
private lemma halfSquare_norm_pair (a b : ℝ) : ‖((a,b) : ℝ×ℝ)‖ = max |a| |b| := by
  rw [Prod.norm_def]; simp [Real.norm_eq_abs]

/-- Linear interpolation between `a` and `b` stays between them. -/
private lemma halfSquare_interp_mem_Icc {a b t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (1-t)*a + t*b ∈ Set.Icc (min a b) (max a b) := by
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, max_eq_right hab]
    constructor <;> nlinarith
  · rw [min_eq_right hba, max_eq_left hba]
    constructor <;> nlinarith

/-- A monotone (or antitone) function on an interval takes at an interior point a value at least the
minimum of its two endpoint values. -/
private lemma halfSquare_min_le_of_monoOn_or_antiOn {f : ℝ → ℝ} {a b x : ℝ} (hab : a ≤ b)
    (hx : x ∈ Set.Icc a b) (h : MonotoneOn f (Set.Icc a b) ∨ AntitoneOn f (Set.Icc a b)) :
    min (f a) (f b) ≤ f x := by
  rcases h with h | h
  · exact le_trans (min_le_left _ _) (h (left_mem_Icc.mpr hab) hx hx.1)
  · exact le_trans (min_le_right _ _) (h hx (right_mem_Icc.mpr hab) hx.2)

/-- **The geometric core.**  Given the two analytic inputs — a quantitative bound comparing `V` with
its linearisation `c * p.1` on the square, and monotonicity of the partial slices — the region
`{V > 0}` inside the square is path connected.  The parameter `e` is the coordinate of the "spine"
(the side of the square on which `V` is large), and `hce` records that `V` grows in the `e`
direction. -/
private theorem isPathConnected_of_spine
    (V : ℝ × ℝ → ℝ) (c δ e : ℝ) (hc : c ≠ 0) (hδ : 0 < δ)
    (he : |e| < δ) (hce : |c| * δ / 2 ≤ c * e)
    (hVbound : ∀ p : ℝ × ℝ, ‖p‖ < δ → ‖V p - c * p.1‖ ≤ (|c|/4) * ‖p‖)
    (hmono : ∀ y : ℝ, |y| < δ →
      MonotoneOn (fun x : ℝ => V (x, y)) (Ioo (-δ) δ) ∨
        AntitoneOn (fun x : ℝ => V (x, y)) (Ioo (-δ) δ)) :
    IsPathConnected ((Ioo (-δ) δ ×ˢ Ioo (-δ) δ) ∩ {x : ℝ × ℝ | 0 < V x}) := by
  set S := (Ioo (-δ) δ ×ˢ Ioo (-δ) δ) ∩ {x : ℝ × ℝ | 0 < V x} with hS
  have he1 : -δ < e := (abs_lt.mp he).1
  have he2 : e < δ := (abs_lt.mp he).2
  have hcabs : 0 < |c| := abs_pos.mpr hc
  -- `V` is positive on the spine
  have hspine : ∀ y : ℝ, |y| < δ → 0 < V (e, y) := by
    intro y hy
    have hnorm : ‖((e,y) : ℝ×ℝ)‖ < δ := by rw [halfSquare_norm_pair]; exact max_lt he hy
    have hb : |V (e,y) - c * e| ≤ (|c|/4) * ‖((e,y) : ℝ×ℝ)‖ := by
      have hb0 := hVbound (e,y) hnorm
      simpa [Real.norm_eq_abs] using hb0
    have hlt : c * e - V (e,y) < (|c|/4) * δ := by
      have h1 : c * e - V (e,y) ≤ |V (e,y) - c * e| := by
        rw [show c * e - V (e,y) = -(V (e,y) - c * e) by ring]
        exact neg_le_abs _
      have h2 : (|c|/4) * ‖((e,y) : ℝ×ℝ)‖ < (|c|/4) * δ :=
        mul_lt_mul_of_pos_left hnorm (by linarith)
      linarith
    nlinarith
  have hbS : ((e, 0) : ℝ × ℝ) ∈ S := by
    rw [hS]
    exact ⟨⟨⟨he1, he2⟩, ⟨by linarith, hδ⟩⟩, hspine 0 (by rwa [abs_zero])⟩
  have hjoin : ∀ p ∈ S, JoinedIn S p (e, 0) := by
    intro p hp
    rw [hS] at hp ⊢
    obtain ⟨⟨hpx1, hpx2⟩, hpV⟩ := hp
    have hpabs : |p.2| < δ := abs_lt.mpr hpx2
    -- the horizontal leg
    have hhoriz : JoinedIn S p (e, p.2) := by
      refine JoinedIn.ofLine (f := fun t : ℝ => ((1-t)*p.1 + t*e, p.2)) ?_ ?_ ?_ ?_
      · exact (by fun_prop : Continuous fun t : ℝ => ((1-t)*p.1 + t*e, p.2)).continuousOn
      · simp
      · simp
      · rintro _ ⟨t, ht, rfl⟩
        rw [hS]
        have hmem := halfSquare_interp_mem_Icc (a := p.1) (b := e) ht
        have hxI : (1-t)*p.1 + t*e ∈ Ioo (-δ) δ :=
          ⟨lt_of_lt_of_le (lt_min hpx1.1 he1) hmem.1,
           lt_of_le_of_lt hmem.2 (max_lt hpx1.2 he2)⟩
        have hsub : Icc (min p.1 e) (max p.1 e) ⊆ Ioo (-δ) δ := by
          intro x hx
          exact ⟨lt_of_lt_of_le (lt_min hpx1.1 he1) hx.1,
                 lt_of_le_of_lt hx.2 (max_lt hpx1.2 he2)⟩
        have hmono' : MonotoneOn (fun x : ℝ => V (x, p.2)) (Icc (min p.1 e) (max p.1 e)) ∨
            AntitoneOn (fun x : ℝ => V (x, p.2)) (Icc (min p.1 e) (max p.1 e)) := by
          rcases hmono p.2 hpabs with h | h
          · exact Or.inl (h.mono hsub)
          · exact Or.inr (h.mono hsub)
        have hminpos : 0 < min (V (min p.1 e, p.2)) (V (max p.1 e, p.2)) := by
          rcases le_total p.1 e with hle | hle
          · rw [min_eq_left hle, max_eq_right hle]
            exact lt_min (by simpa using hpV) (hspine p.2 hpabs)
          · rw [min_eq_right hle, max_eq_left hle]
            exact lt_min (hspine p.2 hpabs) (by simpa using hpV)
        have hfin := halfSquare_min_le_of_monoOn_or_antiOn (f := fun x : ℝ => V (x, p.2))
          (min_le_max) hmem hmono'
        exact ⟨⟨hxI, hpx2⟩, lt_of_lt_of_le hminpos hfin⟩
    -- the vertical leg
    have hvert : JoinedIn S (e, p.2) (e, 0) := by
      refine JoinedIn.ofLine (f := fun t : ℝ => (e, (1-t)*p.2 + t*0)) ?_ ?_ ?_ ?_
      · exact (by fun_prop : Continuous fun t : ℝ => (e, (1-t)*p.2 + t*0)).continuousOn
      · simp
      · simp
      · rintro _ ⟨t, ht, rfl⟩
        rw [hS]
        have hmem := halfSquare_interp_mem_Icc (a := p.2) (b := 0) ht
        have hyI : (1-t)*p.2 + t*0 ∈ Ioo (-δ) δ :=
          ⟨lt_of_lt_of_le (lt_min hpx2.1 (by linarith)) hmem.1,
           lt_of_le_of_lt hmem.2 (max_lt hpx2.2 hδ)⟩
        have hyabs : |(1-t)*p.2 + t*0| < δ := abs_lt.mpr hyI
        exact ⟨⟨⟨he1, he2⟩, hyI⟩, hspine _ hyabs⟩
    exact hhoriz.trans hvert
  rw [isPathConnected_iff]
  exact ⟨⟨(e,0), hbS⟩, fun p hp q hq => (hjoin p hp).trans (hjoin q hq).symm⟩

theorem halfSquare (V : ℝ × ℝ → ℝ) (c : ℝ) (hc : c ≠ 0) (hV0 : V 0 = 0)
    (hVsm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V 0)
    (hdV : fderiv ℝ V 0 = c • ContinuousLinearMap.fst ℝ ℝ ℝ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      IsPathConnected ((Set.Ioo (-δ) δ ×ˢ Set.Ioo (-δ) δ) ∩ {x : ℝ × ℝ | 0 < V x}) := by
  -- `V` is `C¹` on a neighbourhood of the origin
  have h1 : ContDiffAt ℝ (1:ℕ) V 0 := (contDiffAt_infty.mp hVsm) 1
  obtain ⟨u, hu, hucd⟩ : ∃ u ∈ 𝓝 (0:ℝ×ℝ), ContDiffOn ℝ (1:ℕ) V u := by
    have hh := (contDiffWithinAt_iff_contDiffOn_nhds (𝕜:=ℝ) (f:=V) (x:=(0:ℝ×ℝ))
      (s:=Set.univ) (n:=(1:ℕ)) (by simp)).mp h1
    simpa using hh
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp hu
  have hball_cd : ContDiffOn ℝ (1:ℕ) V (Metric.ball (0:ℝ×ℝ) ρ) := hucd.mono hρsub
  have hball_diff : DifferentiableOn ℝ V (Metric.ball (0:ℝ×ℝ) ρ) := hball_cd.differentiableOn_one
  have hball_cont : ContinuousOn (fderiv ℝ V) (Metric.ball (0:ℝ×ℝ) ρ) :=
    hball_cd.continuousOn_fderiv_of_isOpen Metric.isOpen_ball (le_refl _)
  have hmem0 : (0:ℝ×ℝ) ∈ Metric.ball (0:ℝ×ℝ) ρ := Metric.mem_ball_self hρpos
  have hcont : ContinuousAt (fderiv ℝ V) 0 :=
    hball_cont.continuousAt (Metric.isOpen_ball.mem_nhds hmem0)
  have hd0 : DifferentiableAt ℝ V 0 :=
    hball_diff.differentiableAt (Metric.isOpen_ball.mem_nhds hmem0)
  -- the linearisation error is `o (‖·‖)` at the origin
  have hlittle : (fun p : ℝ×ℝ => V p - c * p.1) =o[𝓝 (0:ℝ×ℝ)] (fun p : ℝ×ℝ => p) := by
    have := hd0.hasFDerivAt.isLittleO
    simpa [hdV, hV0] using this
  obtain ⟨η₁, hη₁pos, hη₁⟩ :
      ∃ η > 0, ∀ p : ℝ×ℝ, ‖p‖ < η → ‖V p - c * p.1‖ ≤ (|c|/4) * ‖p‖ := by
    have hcpos : (0:ℝ) < |c|/4 := by have := abs_pos.mpr hc; linarith
    have h := Asymptotics.isLittleO_iff.mp hlittle hcpos
    obtain ⟨η, hη, hη'⟩ := Metric.eventually_nhds_iff.mp h
    exact ⟨η, hη, fun p hp => hη' (by simpa using hp)⟩
  -- the sign of `∂₁V` near the origin is the sign of `c`
  obtain ⟨η₂, hη₂pos, hη₂⟩ :
      ∃ η > 0, ∀ p : ℝ×ℝ, ‖p‖ < η → 0 < c * (fderiv ℝ V p (1,0)) := by
    obtain ⟨η, hηpos, hη⟩ := Metric.continuousAt_iff.mp hcont (|c|/2) (by positivity)
    refine ⟨η, hηpos, fun p hp => ?_⟩
    have hclose : dist (fderiv ℝ V p) (fderiv ℝ V 0) < |c|/2 := hη (by simpa using hp)
    have hD1 : (fderiv ℝ V 0) (1,0) = c := by rw [hdV]; simp
    have h1' : ‖(fderiv ℝ V p) (1,0) - (fderiv ℝ V 0) (1,0)‖ ≤ ‖fderiv ℝ V p - fderiv ℝ V 0‖ := by
      have := ContinuousLinearMap.le_opNorm (fderiv ℝ V p - fderiv ℝ V 0) ((1:ℝ),(0:ℝ))
      simpa [sub_apply] using this
    have hnorm : ‖(fderiv ℝ V p) (1,0) - c‖ < |c|/2 := by
      calc ‖(fderiv ℝ V p) (1,0) - c‖
          = ‖(fderiv ℝ V p) (1,0) - (fderiv ℝ V 0) (1,0)‖ := by rw [hD1]
        _ ≤ ‖fderiv ℝ V p - fderiv ℝ V 0‖ := h1'
        _ = dist (fderiv ℝ V p) (fderiv ℝ V 0) := (dist_eq_norm _ _).symm
        _ < |c|/2 := hclose
    have h4 : |(fderiv ℝ V p) (1,0) - c| < |c|/2 := by rwa [Real.norm_eq_abs] at hnorm
    have h3 : |c * ((fderiv ℝ V p) (1,0)) - c^2| < c^2/2 := by
      rw [show c * ((fderiv ℝ V p) (1,0)) - c^2 = c * ((fderiv ℝ V p) (1,0) - c) by ring,
        abs_mul]
      calc |c| * |(fderiv ℝ V p) (1,0) - c| < |c| * (|c|/2) :=
            mul_lt_mul_of_pos_left h4 (abs_pos.mpr hc)
        _ = c^2/2 := by
              have hh : |c| * (|c| / 2) = (|c| * |c|) / 2 := by ring
              rw [hh, abs_mul_abs_self]; ring
    have hlt := (abs_lt.mp h3).1
    show 0 < c * ((fderiv ℝ V p) (1,0))
    nlinarith [sq_pos_of_ne_zero hc]
  refine ⟨min η₁ (min η₂ ρ) / 2, ?_, fun δ hδ hδle => ?_⟩
  · have : 0 < min η₁ (min η₂ ρ) := lt_min hη₁pos (lt_min hη₂pos hρpos)
    linarith
  · -- all the small parameters are dominated by the chosen radius
    have hm1 : min η₁ (min η₂ ρ) ≤ η₁ := min_le_left _ _
    have hm2 : min η₁ (min η₂ ρ) ≤ η₂ := le_trans (min_le_right _ _) (min_le_left _ _)
    have hm3 : min η₁ (min η₂ ρ) ≤ ρ := le_trans (min_le_right _ _) (min_le_right _ _)
    have hδη₁ : δ ≤ η₁ := by linarith
    have hδη₂ : δ ≤ η₂ := by linarith
    have hδρ : δ ≤ ρ := by linarith
    have hdiff_near : ∀ p : ℝ×ℝ, ‖p‖ < δ → DifferentiableAt ℝ V p := by
      intro p hp
      have hmem : p ∈ Metric.ball (0:ℝ×ℝ) ρ := by
        rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact lt_of_lt_of_le hp hδρ
      exact hball_diff.differentiableAt (Metric.isOpen_ball.mem_nhds hmem)
    have hslice : ∀ (y x : ℝ), |y| < δ → |x| < δ →
        deriv (fun t : ℝ => V (t, y)) x = fderiv ℝ V (x, y) (1, 0) := by
      intro y x hy hx
      have hxy : DifferentiableAt ℝ V (x,y) := by
        refine hdiff_near (x,y) ?_
        rw [halfSquare_norm_pair]; exact max_lt hx hy
      have hcurve : HasDerivAt (fun t : ℝ => (t, y)) ((1:ℝ),(0:ℝ)) x := by
        simpa using (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
      exact (hxy.hasFDerivAt.comp_hasDerivAt x hcurve).deriv
    have hmono : ∀ y : ℝ, |y| < δ →
        MonotoneOn (fun x : ℝ => V (x, y)) (Ioo (-δ) δ) ∨
          AntitoneOn (fun x : ℝ => V (x, y)) (Ioo (-δ) δ) := by
      intro y hy
      have hcont_slice : ContinuousOn (fun x : ℝ => V (x,y)) (Ioo (-δ) δ) := by
        intro x hx
        have hxy : DifferentiableAt ℝ V (x,y) := by
          refine hdiff_near (x,y) ?_
          rw [halfSquare_norm_pair]; exact max_lt (abs_lt.mpr hx) hy
        have hct : ContinuousAt (fun t : ℝ => (t, y)) x := by fun_prop
        exact (hxy.continuousAt.comp (f := fun t : ℝ => (t,y)) (x := x) hct).continuousWithinAt
      rcases lt_or_gt_of_ne hc with hcneg | hcpos
      · right
        refine (strictAntiOn_of_deriv_neg (convex_Ioo (-δ) δ) hcont_slice ?_).antitoneOn
        intro x hx
        rw [interior_Ioo] at hx
        rw [hslice y x hy (abs_lt.mpr hx)]
        have hnorm : ‖((x,y) : ℝ×ℝ)‖ < η₂ := by
          rw [halfSquare_norm_pair]
          exact lt_of_lt_of_le (max_lt (abs_lt.mpr hx) hy) hδη₂
        have hs : 0 < c * (fderiv ℝ V (x, y) (1, 0)) := hη₂ (x,y) hnorm
        nlinarith
      · left
        refine (strictMonoOn_of_deriv_pos (convex_Ioo (-δ) δ) hcont_slice ?_).monotoneOn
        intro x hx
        rw [interior_Ioo] at hx
        rw [hslice y x hy (abs_lt.mpr hx)]
        have hnorm : ‖((x,y) : ℝ×ℝ)‖ < η₂ := by
          rw [halfSquare_norm_pair]
          exact lt_of_lt_of_le (max_lt (abs_lt.mpr hx) hy) hδη₂
        have hs : 0 < c * (fderiv ℝ V (x, y) (1, 0)) := hη₂ (x,y) hnorm
        nlinarith
    have hVbound : ∀ p : ℝ×ℝ, ‖p‖ < δ → ‖V p - c * p.1‖ ≤ (|c|/4) * ‖p‖ :=
      fun p hp => hη₁ p (lt_of_lt_of_le hp hδη₁)
    rcases lt_or_gt_of_ne hc with hcneg | hcpos
    · -- `c < 0`: the spine is on the negative side
      refine isPathConnected_of_spine V c δ (-(δ/2)) hc hδ ?_ ?_ hVbound hmono
      · rw [abs_neg, abs_of_pos (by linarith : (0:ℝ) < δ/2)]; linarith
      · rw [abs_of_neg hcneg]; nlinarith
    · -- `c > 0`: the spine is on the positive side
      refine isPathConnected_of_spine V c δ (δ/2) hc hδ ?_ ?_ hVbound hmono
      · rw [abs_of_pos (by linarith : (0:ℝ) < δ/2)]; linarith
      · rw [abs_of_pos hcpos]; nlinarith

end Work.Drive.Final
