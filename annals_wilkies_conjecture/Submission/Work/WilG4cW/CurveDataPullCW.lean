/-
  WilG4cW / `CurveDataPullCW` — the `CurveData` of the shrunk pullback of one `F1AffineW` chart.

  This is `Work.WilkG4c.CurveDataPullC` (`Submission/Work/WilG4c/CurveDataPullC.lean`) with the
  single chart hypothesis `Work.WilkG4c.H1Chart` replaced by the *corrected* chart hypothesis
  `Work.WilkG4c.H1ChartW` (`Submission/Work/WilG4cW/StepH1OutW.lean`), i.e. the output of area
  G4a's corrected Corollary 5.5 `Work.WilG4a.F1AffineW` for one chart.  The chart condition
  `0 < β₀ l` of `H1Chart` is relaxed to `ChartInW α₀ β₀`
  (`∀ l, 0 ≤ β₀ l ∧ 0 ≤ α₀ l ∧ α₀ l + β₀ l ≤ 1 ∧ ∀ t ∈ I, α₀ l + β₀ l * t ∈ I`).

  The proof is `CurveDataPullC`'s proof, with one change at the very top: after `set α`/`set β`
  we case split on `β₀ l = 0`.
  * `β₀ l = 0` (degenerate chart): the shrunk chart is `α = α₀ l` (constant), `β = 0`, so the
    pullback at `(i,l)` is `pullX F (fun _ => α₀ l) (fun _ => 0) i l`; the image clause of
    `ChartInW` at `t = 1/2` gives `α₀ l ∈ I`, and the proved `Work.WilG4c.CurveDataDegenerate`
    (namespace spelling: `Work.WilG4c`, without the `k`) supplies the two `CurveData` clauses
    with the EMPTY bad set.  Transfer along the function
    equality `pullX F α β i l = pullX F (fun _ => α₀ l) (fun _ => 0) i l`.
  * `β₀ l ≠ 0`: then `0 < β₀ l` from the `0 ≤ β₀ l` component and the rest of
    `CurveDataPullC`'s proof applies verbatim.
-/
import Mathlib
import Submission.Work.WilG4cW.StepH1OutW
import Submission.Work.WilG4c.CurveDataPullC
import Submission.Work.WilG4c.CurveDataDegenerate

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace Work.WilG4cW

open WilkiesDesign WilkiesDesign.CG

private noncomputable def pullCurve {k p n : ℕ}
    (γs : (i : Fin k) → (Fin p → ℝ) → (L : List (Fin (n + 1))) → ℝ → (Fin n → ℝ))
    (α₀ β₀ : (Fin p → ℝ) → ℝ) (cc : ℝ) (i : Fin k) (l : Fin p → ℝ) :
    (j : ℕ) → List (Fin n) → ℝ → Fin n → ℝ :=
  fun j M s ι => Work.WilG4c.clamp01
    (γs i l (Work.WilkG4c.LdirOf j M) ((α₀ l + β₀ l * cc) + (β₀ l / 4) * s) ι)

/-! ## The choice data at a good point -/

/-- The sliced choice lemma, fired at a point whose fibre contains a smooth point: the chosen
curve value lies in the cube, the member is smooth at the curve point, and the curve value is a
`2`-approximate maximiser of `|∂^L|` over the fibre. -/
private lemma cdp_choice_at {n r : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ}
    {γs : (L : List (Fin (n + 1))) → ℝ → (Fin n → ℝ)} {B : Finset ℝ}
    (hc : Work.WilkG4c.ChoiceOut f r γs) (hbdd : Work.WilkG4c.FibreBdd f r B)
    (L : List (Fin (n + 1))) (hL : L.length ≤ r) {x : ℝ} (hxI : x ∈ Work.WilkG4c.I)
    (hxB : x ∉ (B : Set ℝ)) {y : Fin n → ℝ} (hy : y ∈ WilkiesDesign.openCube n)
    (hs : ContDiffAt ℝ L.length f (Work.WilkG4c.pt x y)) :
    γs L x ∈ WilkiesDesign.openCube n ∧
    ContDiffAt ℝ L.length f (Work.WilkG4c.pt x (γs L x)) ∧
    (∀ y' : Fin n → ℝ, y' ∈ WilkiesDesign.openCube n →
      ContDiffAt ℝ L.length f (Work.WilkG4c.pt x y') →
      |iteratedFDeriv ℝ L.length f (Work.WilkG4c.pt x y')
          (fun j => Pi.single (L.get j) 1)| ≤
        2 * |iteratedFDeriv ℝ L.length f (Work.WilkG4c.pt x (γs L x))
          (fun j => Pi.single (L.get j) 1)|) := by
  have hbdd' := hbdd L hL x hxI hxB
  have hne : ({y' : Fin n → ℝ | y' ∈ WilkiesDesign.openCube n ∧
      ContDiffAt ℝ L.length f (Work.WilkG4c.pt x y')}).Nonempty := ⟨y, hy, hs⟩
  obtain ⟨y₀, hy₀, hmax⟩ := Work.WilkG4c.hmax_nearmax_of_bdd hne
    (fun y' => iteratedFDeriv ℝ L.length f (Work.WilkG4c.pt x y')
      (fun j => Pi.single (L.get j) 1))
    (by simpa using hbdd')
  exact hc L hL x ⟨y₀, hy₀.1, hy₀.2, fun y' hy' hcd => hmax y' ⟨hy', hcd⟩⟩

theorem CurveDataPullCW {k p n r : ℕ} (hr : 1 ≤ r)
    (F : Work.WilkG4c.Family k p (n + 1))
    (γs : (i : Fin k) → (Fin p → ℝ) → (L : List (Fin (n + 1))) → ℝ → (Fin n → ℝ))
    (hcspec : ∀ (i : Fin k) (l : Fin p → ℝ), Work.WilkG4c.ChoiceOut (F i l) r (γs i l))
    (Bbad : (i : Fin k) → (Fin p → ℝ) → Finset ℝ)
    (hb : ∀ (i : Fin k) (l : Fin p → ℝ), Work.WilkG4c.FibreBdd (F i l) r (Bbad i l))
    (cc : ℝ) (hcc0 : 0 ≤ cc) (hcc3 : cc ≤ 3 / 4)
    (α₀ β₀ : (Fin p → ℝ) → ℝ)
    (hH1 : Work.WilkG4c.H1ChartW F
      (fun (i : Fin k) (m : Work.WilkG4c.MIdx n r) (l : Fin p → ℝ) (x : ℝ) =>
        γs i l (Work.WilkG4c.LcOf m) x) α₀ β₀)
    (hY : Work.WilkG4c.YBound F r) :
    Work.WilkG4c.CurveData k p n r
      (Work.WilkG4c.pullX F (Work.WilkG4c.shrunkCoeff α₀ β₀ cc).1
        (Work.WilkG4c.shrunkCoeff α₀ β₀ cc).2) := by
  intro i l
  set α : (Fin p → ℝ) → ℝ := (Work.WilkG4c.shrunkCoeff α₀ β₀ cc).1 with hα
  set β : (Fin p → ℝ) → ℝ := (Work.WilkG4c.shrunkCoeff α₀ β₀ cc).2 with hβ
  have hαap : ∀ m : Fin p → ℝ, α m = α₀ m + β₀ m * cc := fun m => rfl
  have hβap : ∀ m : Fin p → ℝ, β m = β₀ m / 4 := fun m => rfl
  by_cases hβ0 : β₀ l = 0
  · -- degenerate chart `β₀ l = 0`: the shrunk chart is the constant chart `α₀ l`
    have hαl0 : α l = α₀ l := by rw [hαap, hβ0, zero_mul, add_zero]
    have hβl0 : β l = 0 := by rw [hβap, hβ0, zero_div]
    have hα0I : α₀ l ∈ Work.WilkG4c.I := by
      have h := (hH1.1 l).2.2.2 (1 / 2) (by
        rw [Work.WilkG4c.I]; exact ⟨by norm_num, by norm_num⟩)
      rwa [hβ0, zero_mul, add_zero] at h
    obtain ⟨γ, hγ1, hγ2⟩ := Work.WilG4c.CurveDataDegenerate hr F hY i l (α₀ l) hα0I
    have hfun : Work.WilkG4c.pullX F α β i l
        = Work.WilkG4c.pullX F (fun _ => α₀ l) (fun _ => (0 : ℝ)) i l := by
      funext t
      simp only [Work.WilkG4c.pullX_apply]
      have hconv : α l + β l * t 0 = α₀ l + (fun _ => (0 : ℝ)) l * t 0 := by
        rw [hαl0, hβl0]
      rw [hconv]
    refine ⟨∅, γ, ?_, ?_⟩
    · intro m v x y hm hxI _ hy hcd
      rw [hfun] at hcd ⊢
      exact hγ1 m v x y hm hxI hy hcd
    · intro m v x y hm hxI _ hy hcd
      rw [hfun] at hcd ⊢
      exact hγ2 m v x y hm hxI hy hcd
  · -- non-degenerate chart: verbatim `CurveDataPullC`
    have hβ0l : 0 < β₀ l := lt_of_le_of_ne (hH1.1 l).1 (Ne.symm hβ0)
    have hα0l : 0 ≤ α₀ l := (hH1.1 l).2.1
    have hαβ0 : α₀ l + β₀ l ≤ 1 := (hH1.1 l).2.2.1
    have hβpos : 0 < β l := by rw [hβap]; linarith
    have hβne : β l ≠ 0 := ne_of_gt hβpos
    have hα0 : 0 ≤ α l := by
      rw [hαap]; nlinarith [hβ0l, hα0l, hcc0]
    have hαβ : α l + β l ≤ 1 := by
      rw [hαap, hβap]; nlinarith [hβ0l, hα0l, hαβ0, hcc3]
    -- the bad set in the pullback's coordinates
    set B : Finset ℝ := (Bbad i l).image (fun t => (t - α l) / β l) with hB
    have hBB : ∀ x ∈ Work.WilkG4c.I, x ∉ (B : Set ℝ) → α l + β l * x ∉ (Bbad i l : Set ℝ) := by
      intro x _ hxB hcon
      exact hxB (by
        rw [hB]
        exact Finset.mem_image.mpr ⟨α l + β l * x, hcon, by rw [div_eq_iff hβne]; ring⟩)
    have hψI : ∀ x ∈ Work.WilkG4c.I, α l + β l * x ∈ Work.WilkG4c.I := by
      intro x hx
      have hx1 : 0 < x := hx.1
      have hx2 : x < 1 := hx.2
      constructor
      · have h2 : 0 < β l * x := mul_pos hβpos hx1
        linarith [hα0]
      · have hccx : cc + x / 4 < 1 := by linarith
        have h1 : β₀ l * (cc + x / 4) < β₀ l := by
          have := mul_lt_mul_of_pos_left hccx hβ0l
          simpa using this
        have h2 : α l + β l * x = α₀ l + β₀ l * (cc + x / 4) := by
          rw [hαap, hβap]; ring
        rw [h2]; linarith
    -- the unclamped and the clamped choice curves
    set γu : (j : ℕ) → List (Fin n) → ℝ → Fin n → ℝ :=
      fun j M s => γs i l (Work.WilkG4c.LdirOf j M) (α l + β l * s) with hγu
    set γc : (j : ℕ) → List (Fin n) → ℝ → Fin n → ℝ := pullCurve γs α₀ β₀ cc i l with hγc
    have hγc_clamp : ∀ (j : ℕ) (M : List (Fin n)) (s : ℝ) (ι : Fin n),
        γc j M s ι = Work.WilG4c.clamp01 (γu j M s ι) := by
      intro j M s ι
      have harg : (α₀ l + β₀ l * cc) + (β₀ l / 4) * s = α l + β l * s := by
        rw [hαap, hβap]
      simp only [hγc, hγu, pullCurve, harg]
    have hγc_eq_of_mem : ∀ (j : ℕ) (M : List (Fin n)) (x : ℝ),
        γu j M x ∈ WilkiesDesign.openCube n → γc j M x = γu j M x := by
      intro j M x hx
      funext ι
      rw [hγc_clamp j M x ι, Work.WilG4c.clamp01_of_mem (hx ι)]
    -- the pullback is smooth at `(x,y)` exactly when `F` is at the chart point
    have hFsmooth : ∀ (j : ℕ) (M : List (Fin n)) (x : ℝ) (y : Fin n → ℝ), j + M.length ≤ r →
        x ∈ Work.WilkG4c.I → x ∉ (B : Set ℝ) → y ∈ WilkiesDesign.openCube n →
        ContDiffAt ℝ (j + M.length) (Work.WilkG4c.pullX F α β i l) (Work.WilkG4c.pt x y) →
        ContDiffAt ℝ (j + M.length) (F i l) (Work.WilkG4c.pt (α l + β l * x) y) := by
      intro j M x y _ _ _ _ hG
      exact (Work.WilkG4c.contDiffAt_affine_pullback_iff (m := j + M.length) (F i l) (α l) (β l)
        hβne (Work.WilkG4c.pt x y)).mp hG
    -- the clamped and the unclamped curve agree at a good point
    have hclampAt : ∀ (j : ℕ) (M : List (Fin n)) (x : ℝ) (y : Fin n → ℝ), j + M.length ≤ r →
        x ∈ Work.WilkG4c.I → x ∉ (B : Set ℝ) → y ∈ WilkiesDesign.openCube n →
        ContDiffAt ℝ (j + M.length) (Work.WilkG4c.pullX F α β i l) (Work.WilkG4c.pt x y) →
        γc j M x = γu j M x := by
      intro j M x y hjr hxI hxB hy hG
      obtain ⟨hcube, -, -⟩ := cdp_choice_at (hcspec i l) (hb i l) (Work.WilkG4c.LdirOf j M)
        (by rw [Work.WilkG4c.LdirOf_length]; exact hjr) (hψI x hxI) (hBB x hxI hxB) hy
        (by simpa [Work.WilkG4c.LdirOf_length] using hFsmooth j M x y hjr hxI hxB hy hG)
      exact hγc_eq_of_mem j M x hcube
    -- (1)+(2): the near-maximality and the smoothness at the curve point
    have hmaxsm : (∀ (j : ℕ) (M : List (Fin n)) (x : ℝ) (y : Fin n → ℝ), j + M.length ≤ r →
          x ∈ Work.WilkG4c.I → x ∉ (B : Set ℝ) → y ∈ WilkiesDesign.openCube n →
          ContDiffAt ℝ (j + M.length) (Work.WilkG4c.pullX F α β i l) (Work.WilkG4c.pt x y) →
          |Work.WilkG4c.iterDir (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ)
              (Work.WilkG4c.pullX F α β i l) (Work.WilkG4c.pt x y)| ≤
            2 * |Work.WilkG4c.iterDir (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ)
              (Work.WilkG4c.pullX F α β i l) (Work.WilkG4c.curveFun (γc j M) x)|) ∧
        (∀ (j : ℕ) (M : List (Fin n)) (x : ℝ) (y : Fin n → ℝ), j + M.length ≤ r →
          x ∈ Work.WilkG4c.I → x ∉ (B : Set ℝ) → y ∈ WilkiesDesign.openCube n →
          ContDiffAt ℝ (j + M.length) (Work.WilkG4c.pullX F α β i l) (Work.WilkG4c.pt x y) →
          ContDiffAt ℝ (j + M.length) (Work.WilkG4c.pullX F α β i l)
            (Work.WilkG4c.curveFun (γc j M) x)) := by
      have hmain := Work.WilkG4c.hmax_hcurvesm_pullbackC hr (F i l) (α l) (β l) hβpos hα0 hαβ
        (Bbad i l) B hBB (γs i l) γu rfl (hcspec i l) (hb i l)
      constructor
      · intro j M x y hjr hxI hxB hy hG
        have hcfun : Work.WilkG4c.curveFun (γc j M) x = Work.WilkG4c.curveFun (γu j M) x := by
          simp only [Work.WilkG4c.curveFun, hclampAt j M x y hjr hxI hxB hy hG]
        rw [hcfun]
        exact hmain.1 j M x y hjr hxI hxB hy hG
      · intro j M x y hjr hxI hxB hy hG
        have hcfun : Work.WilkG4c.curveFun (γc j M) x = Work.WilkG4c.curveFun (γu j M) x := by
          simp only [Work.WilkG4c.curveFun, hclampAt j M x y hjr hxI hxB hy hG]
        rw [hcfun]
        exact hmain.2 j M x y hjr hxI hxB hy hG
    -- (3): the curve bound
    have hcurve : ∀ (j : ℕ) (M : List (Fin n)) (x : ℝ) (y : Fin n → ℝ), j + M.length ≤ r →
        x ∈ Work.WilkG4c.I → x ∉ (B : Set ℝ) → y ∈ WilkiesDesign.openCube n →
        ContDiffAt ℝ (j + M.length) (Work.WilkG4c.pullX F α β i l) (Work.WilkG4c.pt x y) →
        |Work.WilkG4c.iterDir (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ)
            (Work.WilkG4c.pullX F α β i l) (Work.WilkG4c.curveFun (γc j M) x)| ≤
          Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ j := by
      intro j M x y hjr hxI hxB hy hG
      -- basic data at the chart point
      have hx'I : α l + β l * x ∈ Work.WilkG4c.I := hψI x hxI
      have hx'B : α l + β l * x ∉ (Bbad i l : Set ℝ) := hBB x hxI hxB
      have hFs : ContDiffAt ℝ (j + M.length) (F i l) (Work.WilkG4c.pt (α l + β l * x) y) :=
        hFsmooth j M x y hjr hxI hxB hy hG
      -- the choice data at the chart point
      obtain ⟨hcube, hcj, hcmax⟩ := cdp_choice_at (hcspec i l) (hb i l) (Work.WilkG4c.LdirOf j M)
        (by rw [Work.WilkG4c.LdirOf_length]; exact hjr) hx'I hx'B hy
        (by simpa only [Work.WilkG4c.LdirOf_length, Nat.cast_add] using hFs)
      have hclampx : γc j M x = γu j M x := hγc_eq_of_mem j M x hcube
      have hγcube : γc j M x ∈ WilkiesDesign.openCube n := by rw [hclampx]; exact hcube
      -- the joint smoothness at the curve point
      have hcj' : ContDiffAt ℝ (j + M.length) (F i l)
          (Work.WilkG4c.pt (α l + β l * x) (γc j M x)) := by
        have h := hcj
        rw [Work.WilkG4c.LdirOf_length] at h
        rwa [hclampx]
      -- the (T1) tuple member: the clamped curve is `C^{r+1}` with unit jets
      have hT1 : ∀ (ι : Fin n),
          ContDiffAt ℝ (r + 1) (fun s : ℝ => γc j M s ι) x ∧
          (∀ q ≤ r + 1, ‖iteratedFDeriv ℝ q (fun s : ℝ => γc j M s ι) x‖ ≤ 1) := by
        intro ι
        have hmem := hH1.2 ⟨i, Work.WilkG4c.curveIdx j M r hjr, Sum.inl ι⟩ l
        have hfun : (fun t : Fin 1 → ℝ => Work.WilkG4c.tupleFunc F
              (fun (i : Fin k) (m : Work.WilkG4c.MIdx n r) (l : Fin p → ℝ) (x : ℝ) =>
                γs i l (Work.WilkG4c.LcOf m) x)
              ⟨i, Work.WilkG4c.curveIdx j M r hjr, Sum.inl ι⟩ l
              (fun _ => α₀ l + β₀ l * t 0))
            = (fun t : Fin 1 → ℝ => Work.WilG4c.clamp01
                (γs i l (Work.WilkG4c.LdirOf j M) (α₀ l + β₀ l * t 0) ι)) := by
          funext t
          simp only [Work.WilkG4c.tupleFunc_inl]
          rw [Work.WilkG4c.LcOf_curveIdx_eq j M r hjr (by omega)]
        rw [hfun] at hmem
        have hshift : (fun s : ℝ => Work.WilG4c.clamp01
              (γs i l (Work.WilkG4c.LdirOf j M) (α₀ l + β₀ l * (cc + s / 4)) ι))
            = (fun s : ℝ => γc j M s ι) := by
          funext s
          have harg : α₀ l + β₀ l * (cc + s / 4) = (α₀ l + β₀ l * cc) + (β₀ l / 4) * s := by
            ring
          rw [harg, hγc, pullCurve]
        have hres := Work.WilG4c.CdpT1Curve (r := r) hr
          (fun x' : ℝ => Work.WilG4c.clamp01 (γs i l (Work.WilkG4c.LdirOf j M) x' ι))
          (α₀ l) (β₀ l) cc x hβ0l hcc0 hcc3 hxI hmem.1 hmem.2
        rwa [hshift] at hres
      -- the smoothness of the pullback at the curve point
      have hGp : ContDiffAt ℝ (j + M.length) (Work.WilkG4c.pullX F α β i l)
          (Work.WilkG4c.curveFun (γc j M) x) :=
        (Work.WilkG4c.contDiffAt_affine_pullback_iff (m := j + M.length) (F i l) (α l) (β l)
          hβne (Work.WilkG4c.pt x (γc j M x))).mpr (by
            simpa only [Work.WilkG4c.pt_zero, Work.WilkG4c.tail_pt, Nat.cast_add] using hcj')
      -- the curve is `C^k` with the `hgd` and smoothness data
      have hγcsm : ∀ ι : Fin n, ContDiffAt ℝ (j + M.length) (fun s : ℝ => γc j M s ι) x :=
        fun ι => (hT1 ι).1.of_le (by exact_mod_cast (by omega : j + M.length ≤ r + 1))
      have hsmoothg : ∀ ι : Fin n,
          ContDiffAt ℝ (j + M.length) (fun s : ℝ => deriv (fun u => γc j M u ι) s) x :=
        fun ι => (hT1 ι).1.derivWithin
          (by exact_mod_cast (by omega : j + M.length + 1 ≤ r + 1))
      have hgd : ∀ ι : Fin n, ∀ m ≤ j + M.length,
          ‖iteratedFDeriv ℝ m (fun s : ℝ => deriv (fun u => γc j M u ι) s) x‖ ≤ 1 :=
        fun ι m hm => Work.WilkG4c.hgd_of_jet (fun s : ℝ => γc j M s ι) x (hT1 ι).2 m (by omega)
      -- the curve bound
      refine (Work.WilkG4c.curve_bound (Work.WilkG4c.pullX F α β i l) (γc j M) x (j + M.length)
        (by omega) hGp hγcsm ?_ hgd hsmoothg) j M (by omega)
      -- `hbase`
      intro M' hM'
      have hM'r : M'.length ≤ r := by omega
      set J : (Fin 1 → ℝ) → ℝ := fun t => Work.WilkG4c.surrogateSlice p n (F i)
        (Work.WilkG4c.gclOf (fun (i : Fin k) (m : Work.WilkG4c.MIdx n r) (l : Fin p → ℝ) (x : ℝ) =>
            γs i l (Work.WilkG4c.LcOf m) x) i (Work.WilkG4c.curveIdx j M r hjr))
        (Work.WilkG4c.cvList M') l (α₀ l + β₀ l * t 0) with hJ
      -- the curve point in `gclOf` form
      have hgcu : ∀ v : ℝ, Work.WilkG4c.gclOf (fun (i : Fin k) (m : Work.WilkG4c.MIdx n r)
            (l : Fin p → ℝ) (x : ℝ) => γs i l (Work.WilkG4c.LcOf m) x) i
            (Work.WilkG4c.curveIdx j M r hjr) l (α l + β l * v) = γc j M v := by
        intro v
        funext ι
        simp only [Work.WilkG4c.gclOf]
        rw [Work.WilkG4c.LcOf_curveIdx_eq j M r hjr (by omega), hγc, pullCurve, hαap, hβap]
      -- the slice smoothness at the curve point
      have hslicesm : ∀ u : ℝ, ContDiffAt ℝ (j + M.length) (F i l)
          (Work.WilkG4c.pt (α l + β l * u) (γc j M u)) →
          ContDiffAt ℝ M'.length (Work.WilkG4c.slice (F i l) (α l + β l * u)) (γc j M u) :=
        fun u hu => (Work.WilG4c.CdpSliceContDiffAt hu).of_le (by exact_mod_cast hM')
      -- the permutation of the direction lists
      have hperm : M'.Perm (Work.WilkG4c.cvList M') := by
        rw [Work.WilkG4c.cvList]
        exact Work.WilkG4c.canonList_cntVec_perm M' r hM'r
      -- the germ identity
      have hgermR : (fun s : ℝ => Work.WilkG4c.iterDir (M'.map Fin.succ)
            (Work.WilkG4c.pullX F α β i l) (Work.WilkG4c.curveFun (γc j M) s))
          =ᶠ[nhds x] (fun s : ℝ => 4 * J (fun _ : Fin 1 => cc + s / 4) - 2) := by
        have hev : ∀ᶠ u in nhds x, ContDiffAt ℝ (j + M.length) (F i l)
            (Work.WilkG4c.pt (α l + β l * u) (γc j M u)) :=
          Work.WilG4c.CdpEventuallyCurveSmooth (k := j + M.length) hcj'
            (by fun_prop) rfl (by
              rw [continuousAt_pi]
              intro ι
              exact ((hT1 ι).1).continuousAt) rfl
        filter_upwards [hev] with u hu
        have harg : α₀ l + β₀ l * (cc + u / 4) = α l + β l * u := by rw [hαap, hβap]; ring
        have hsmu : ContDiffAt ℝ M'.length (F i l)
            (Work.WilkG4c.pt (α l + β l * u) (γc j M u)) :=
          hu.of_le (by exact_mod_cast hM')
        have hsmu' : ContDiffAt ℝ (Work.WilkG4c.cvList M').length
            (Work.WilkG4c.slice (F i l) (α l + β l * u)) (γc j M u) := by
          rw [Work.WilkG4c.cvList_length]
          exact (Work.WilG4c.CdpSliceContDiffAt hu).of_le (by exact_mod_cast hM')
        -- the pullback identity: no `x`-direction occurs in `M'.map Fin.succ`
        have h1 : Work.WilkG4c.iterDir (M'.map Fin.succ) (Work.WilkG4c.pullX F α β i l)
              (Work.WilkG4c.curveFun (γc j M) u)
            = Work.WilkG4c.iterDir (M'.map Fin.succ) (F i l)
              (Work.WilkG4c.pt (α l + β l * u) (γc j M u)) := by
          have h := Work.WilG4c.iterDir_pullX (F i l) (α l) (β l) u (γc j M u) (M'.map Fin.succ)
            (by simpa only [List.length_map] using hsmu)
          have hx0 : Work.WilkG4c.xcount (M'.map Fin.succ) = 0 := by
            rw [Work.WilkG4c.xcount]
            simp
          rw [hx0, pow_zero, one_mul] at h
          exact h
        -- the slice transport and the permutation of the directions
        have hslice : Work.WilkG4c.iterDir (M'.map Fin.succ) (F i l)
              (Work.WilkG4c.pt (α l + β l * u) (γc j M u))
            = Work.WilkG4c.iterDir (Work.WilkG4c.cvList M')
              (Work.WilkG4c.slice (F i l) (α l + β l * u)) (γc j M u) := by
          rw [Work.WilG4c.iterDir_slice_transport (F i l) M' (α l + β l * u) (γc j M u) hsmu]
          exact Work.WilG4c.iterDir_perm (Work.WilkG4c.slice (F i l) (α l + β l * u)) hperm
            (γc j M u) (hsmu'.of_le (by rw [Work.WilkG4c.cvList_length]))
        have hiter : Work.WilkG4c.iterDir (Work.WilkG4c.cvList M')
              (Work.WilkG4c.slice (F i l) (α l + β l * u)) (γc j M u)
            = iteratedFDeriv ℝ (Work.WilkG4c.cvList M').length
              (Work.WilkG4c.slice (F i l) (α l + β l * u)) (γc j M u)
              (fun jj => Pi.single ((Work.WilkG4c.cvList M').get jj) 1) :=
          Work.WilG4c.iterDir_eq_iteratedFDeriv (Work.WilkG4c.cvList M')
            (Work.WilkG4c.slice (F i l) (α l + β l * u)) (γc j M u) hsmu'
        -- the surrogate is honest at `u`
        have hJu : J (fun _ : Fin 1 => cc + u / 4) = Work.WilkG4c.surrogateSlice p n (F i)
            (Work.WilkG4c.gclOf (fun (i : Fin k) (m : Work.WilkG4c.MIdx n r) (l : Fin p → ℝ)
              (x : ℝ) => γs i l (Work.WilkG4c.LcOf m) x) i (Work.WilkG4c.curveIdx j M r hjr))
            (Work.WilkG4c.cvList M') l (α₀ l + β₀ l * (cc + u / 4)) := by
          rw [hJ]
        have hbr : ContDiffAt ℝ (Work.WilkG4c.cvList M').length
            (Work.WilkG4c.slice (F i l) (α₀ l + β₀ l * (cc + u / 4)))
            (Work.WilkG4c.gclOf (fun (i : Fin k) (m : Work.WilkG4c.MIdx n r) (l : Fin p → ℝ)
              (x : ℝ) => γs i l (Work.WilkG4c.LcOf m) x) i (Work.WilkG4c.curveIdx j M r hjr) l
              (α₀ l + β₀ l * (cc + u / 4))) := by
          rw [harg, hgcu u, Work.WilkG4c.cvList_length]
          exact (Work.WilG4c.CdpSliceContDiffAt hu).of_le (by exact_mod_cast hM')
        rw [h1, hslice, hiter, hJu, Work.WilkG4c.surrogateSlice_of_mem hbr]
        rw [harg, hgcu u]
        ring
      -- the `Fin 1 → ℝ` form of the germ
      have huM : (fun u : Fin 1 → ℝ => Work.WilkG4c.iterDir (M'.map Fin.succ)
            (Work.WilkG4c.pullX F α β i l) (Work.WilkG4c.curveFun (γc j M) (u 0)))
          =ᶠ[nhds (fun _ : Fin 1 => x)]
          (fun u : Fin 1 → ℝ => 4 * J (fun _ : Fin 1 => cc + u 0 / 4) - 2) := by
        have htend : Filter.Tendsto (fun u : Fin 1 → ℝ => u 0) (nhds (fun _ : Fin 1 => x))
            (nhds x) := (continuous_apply (0 : Fin 1)).continuousAt.tendsto
        exact htend.eventually hgermR
      -- the surrogate's jet bounds
      have hJjet : ∀ m ≤ r + 1, ‖iteratedFDeriv ℝ m J (fun _ : Fin 1 => cc + x / 4)‖ ≤ 1 := by
        intro m hm
        have hmem := (hH1.2 ⟨i, Work.WilkG4c.curveIdx j M r hjr,
          Sum.inr (Work.WilkG4c.cntCIdx M' r hM'r)⟩ l).2 m hm
        have hcx : cc + x / 4 ∈ Set.Ioo (0 : ℝ) 1 := by
          constructor <;> linarith [hxI.1, hxI.2]
        have hpt : (fun _ : Fin 1 => cc + x / 4) ∈ WilkiesDesign.openCube 1 := by
          intro jj
          simpa using hcx
        exact hmem (fun _ : Fin 1 => cc + x / 4) hpt
      -- the surrogate's value bound
      have hJval : |4 * J (fun _ : Fin 1 => cc + x / 4) - 2| ≤ 1 := by
        have hψx : α₀ l + β₀ l * (cc + x / 4) = α l + β l * x := by rw [hαap, hβap]; ring
        have hbnd : |iteratedFDeriv ℝ (Work.WilkG4c.cvList M').length
            (Work.WilkG4c.slice (F i l) (α₀ l + β₀ l * (cc + x / 4)))
            (Work.WilkG4c.gclOf (fun (i : Fin k) (m : Work.WilkG4c.MIdx n r) (l : Fin p → ℝ)
              (x : ℝ) => γs i l (Work.WilkG4c.LcOf m) x) i (Work.WilkG4c.curveIdx j M r hjr) l
              (α₀ l + β₀ l * (cc + x / 4)))
            (fun jj => Pi.single ((Work.WilkG4c.cvList M').get jj) 1)| ≤ 1 := by
          rw [hψx, hgcu x]
          exact Work.WilG4c.CdpEvalAbsLe _ _ (Work.WilkG4c.cvList M') (by
            rw [Work.WilkG4c.cvList_length]
            exact hY i l (α l + β l * x) hx'I M'.length hM'r (γc j M x) hγcube)
        have hJx : J (fun _ : Fin 1 => cc + x / 4) = Work.WilkG4c.surrogateSlice p n (F i)
            (Work.WilkG4c.gclOf (fun (i : Fin k) (m : Work.WilkG4c.MIdx n r) (l : Fin p → ℝ)
              (x : ℝ) => γs i l (Work.WilkG4c.LcOf m) x) i (Work.WilkG4c.curveIdx j M r hjr))
            (Work.WilkG4c.cvList M') l (α₀ l + β₀ l * (cc + x / 4)) := by
          rw [hJ]
        rw [hJx]
        exact Work.WilG4c.CdpSurrogateAbs hbnd
      -- assemble
      have htn := Work.WilG4c.tnorm_curve_of_surrogate_germ hr
        (Work.WilkG4c.iterDir (M'.map Fin.succ) (Work.WilkG4c.pullX F α β i l)) (γc j M) J x cc
        hcc0 hcc3 hJjet hJval huM
      exact (WilkiesDesign.CG.tnorm_mono (by omega : j + M.length ≤ r)
        (fun s : ℝ => Work.WilkG4c.iterDir (M'.map Fin.succ)
          (Work.WilkG4c.pullX F α β i l) (Work.WilkG4c.curveFun (γc j M) s)) x).trans htn
    refine ⟨B, Work.WilkG4c.canonGamma γc, ?_⟩
    exact Work.WilkG4c.subdiv_hyp_multi_badBC hr (Work.WilkG4c.pullX F α β i l) γc B
      hmaxsm.1 hmaxsm.2 hcurve

end Work.WilG4cW
