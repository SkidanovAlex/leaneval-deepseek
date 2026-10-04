import Mathlib
import Submission.Work.Diff.EXT.MixedSum
import Submission.Work.Diff.T.clairaut_fderiv_apply

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `j`-th jet is bounded by the "space-outer, time-inner" mixed partials

Support file for `Work.Diff.EXT.norm_iteratedFDeriv_le_seamPartials`.

The main theorem `Work.Diff.EXT.norm_iteratedFDeriv_le_seamPartials` is the final statement of this
file.  Everything above it is the (finite-order) calculus needed to compare the mixed partials
`∂_y^{j-k} ∂_t^k F` with the mixed *time*-derivatives of the directional derivatives of `F`,
following the same route as `Submission/Work/Diff/EXT/Aux/norm_iteratedFDeriv_le_mixed_timeDeriv`
(whose directory name is a reserved file name and therefore cannot be imported).

For `F : ℝ × E → Z` smooth at `p` one has, with `sliceD F k p := ∂_t^k F (p.1, p.2)`:

* `mixSum` (`seamSum` below) is the sum of the norms of `∂_y^{m-j} ∂_t^j F` at `p`;
* `seamSum m (fun q => fderiv ℝ F q (1,0)) p ≤ seamSum (m+1) F p` (`seamSum_tDeriv_le`);
* `seamSum m (fun q => fderiv ℝ F q (0,ζ)) p ≤ ‖ζ‖ * seamSum (m+1) F p` (`seamSum_sDeriv_le`);
* hence, by peeling the last argument of the `(k+1)`-st jet and applying the induction hypothesis
  to the two pieces, `‖iteratedFDeriv ℝ k F p‖ ≤ 2 ^ k * seamSum k F p`.
-/


open scoped Topology ContDiff
open Filter ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

namespace Work.Diff.EXT

/-! ## The iterated time derivatives -/

/-- The time derivative of `u : ℝ × E → Z` as a function on `ℝ × E`. -/
noncomputable def tDerFun (u : ℝ × E → Z) : ℝ × E → Z :=
  fun p => deriv (fun s : ℝ => u (s, p.2)) p.1

/-- The `i`-th time derivative of `u`, as a function on `ℝ × E`. -/
noncomputable def sliceD (u : ℝ × E → Z) (i : ℕ) : ℝ × E → Z :=
  fun p => iteratedDeriv i (fun s : ℝ => u (s, p.2)) p.1

theorem sliceD_zero (u : ℝ × E → Z) : sliceD u 0 = u := by
  funext p
  simp [sliceD]

theorem sliceD_succ (u : ℝ × E → Z) (i : ℕ) : sliceD u (i + 1) = tDerFun (sliceD u i) := by
  funext p
  simp only [sliceD, tDerFun, iteratedDeriv_succ]

/-- `tDerFun w` agrees with the evaluation of the total derivative of `w` on `(1,0)`. -/
theorem tDerFun_eq_fderiv {w : ℝ × E → Z} {q : ℝ × E} (hw : DifferentiableAt ℝ w q) :
    tDerFun w q = (fderiv ℝ w q) (1, 0) := by
  have hφ : HasFDerivAt (fun s : ℝ => (s, q.2)) (ContinuousLinearMap.inl ℝ ℝ E) q.1 :=
    hasFDerivAt_prodMk_left (𝕜 := ℝ) q.1 q.2
  have h : HasDerivAt (fun s : ℝ => w (s, q.2)) ((fderiv ℝ w q) (1, 0)) q.1 :=
    (hw.hasFDerivAt.comp q.1 hφ).hasDerivAt
  exact h.deriv

/-- The time derivative of a `C^{N+1}` function is `C^N`. -/
theorem contDiffAt_tDerFun {w : ℝ × E → Z} {q : ℝ × E} {N : ℕ}
    (hw : ContDiffAt ℝ ((N + 1 : ℕ) : WithTop ℕ∞) w q) :
    ContDiffAt ℝ (N : WithTop ℕ∞) (tDerFun w) q := by
  have hfd : ContDiffAt ℝ (N : WithTop ℕ∞) (fun q' : ℝ × E => fderiv ℝ w q') q :=
    hw.fderiv_right (hmn := by simp)
  have h1 : ContDiffAt ℝ (N : WithTop ℕ∞)
      (fun q' : ℝ × E => (fderiv ℝ w q') (1, 0)) q :=
    hfd.clm_apply contDiffAt_const
  refine h1.congr_of_eventuallyEq ?_
  have hD : ∀ᶠ q' : ℝ × E in 𝓝 q, DifferentiableAt ℝ w q' :=
    ((hw.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ((N + 1 : ℕ) : WithTop ℕ∞))).eventually
      (by simp)).mono (fun q' hq' => hq'.differentiableAt (by simp))
  filter_upwards [hD] with q' hq'
  exact tDerFun_eq_fderiv hq'

/-- The Fréchet derivative of the partial map `y ↦ u (q.1, y)` is the total Fréchet derivative of
`u` at `q`, restricted to the second factor. -/
theorem fderiv_partial_eq (u : ℝ × E → Z) {q : ℝ × E} (hu : DifferentiableAt ℝ u q) :
    fderiv ℝ (fun y : E => u (q.1, y)) q.2
      = (fderiv ℝ u q).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
  have hφ : HasFDerivAt (fun y : E => (q.1, y)) (ContinuousLinearMap.inr ℝ ℝ E) q.2 :=
    hasFDerivAt_prodMk_right (𝕜 := ℝ) q.1 q.2
  exact (hu.hasFDerivAt.comp q.2 hφ).fderiv


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] 
variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-! ## Auxiliary calculus for the mixed-derivative decomposition

Everything below is stated with *finite* orders of smoothness at a single point: this is what
`ContDiffAt ℝ (⊤ : ℕ∞) f p` provides (it gives `C^N` at `p` for every finite `N`), and it is enough
at every step of the argument. -/

/-- The sum of the norms of the mixed derivatives `∂_y^{m-j} ∂_t^j F` at `p`. -/
noncomputable def seamSum (m : ℕ) (F : ℝ × E → Z) (p : ℝ × E) : ℝ :=
  ∑ j ∈ Finset.range (m + 1),
    ‖iteratedFDeriv ℝ (m - j)
      (fun y : E => sliceD F j (p.1, y)) p.2‖

/-- A finite order of smoothness is not `∞` (the smoothness exponent). -/
lemma cast_ne_infty {N : ℕ} : ((N : ℕ) : WithTop ℕ∞) ≠ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  intro h
  exact ENat.natCast_ne_top N (WithTop.coe_inj.mp h)

/-- `iteratedFDeriv` depends only on the germ of the function. -/
lemma iteratedFDeriv_congr_of_eventuallyEq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f g : V → W} {x : V} (h : f =ᶠ[𝓝 x] g) (n : ℕ) :
    iteratedFDeriv ℝ n f x = iteratedFDeriv ℝ n g x := by
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.mem_nhds_iff.mp h
  have h1 : iteratedFDerivWithin ℝ n f (Metric.ball x r) x = iteratedFDeriv ℝ n f x :=
    iteratedFDerivWithin_of_isOpen n Metric.isOpen_ball (Metric.mem_ball_self hr_pos)
  have h2 : iteratedFDerivWithin ℝ n g (Metric.ball x r) x = iteratedFDeriv ℝ n g x :=
    iteratedFDerivWithin_of_isOpen n Metric.isOpen_ball (Metric.mem_ball_self hr_pos)
  rw [← h1, ← h2,
    iteratedFDerivWithin_congr (fun y hy => hr_sub hy) (Metric.mem_ball_self hr_pos) n]

/-- The slice at `p.1` of an eventual equality on `ℝ × E`. -/
lemma eventuallyEq_slice {G H : ℝ × E → Z} {p : ℝ × E} (h : G =ᶠ[𝓝 p] H) :
    (fun y : E => G (p.1, y)) =ᶠ[𝓝 p.2] (fun y : E => H (p.1, y)) := by
  have htend : Tendsto (fun y : E => (p.1, y)) (𝓝 p.2) (𝓝 p) := by
    rw [nhds_prod_eq]
    exact tendsto_const_nhds.prodMk tendsto_id
  exact htend.eventually h

section Helpers

variable {p : ℝ × E} {F : ℝ × E → Z}

/-- The function `z ↦ fderiv ℝ F z c` is as smooth at `q` as `F` is (one order less). -/
lemma contDiffAt_fderiv_apply {q c : ℝ × E} {N : ℕ}
    (hF : ContDiffAt ℝ ((N + 1 : ℕ) : WithTop ℕ∞) F q) :
    ContDiffAt ℝ (N : WithTop ℕ∞) (fun z : ℝ × E => fderiv ℝ F z c) q :=
  (hF.fderiv_right (hmn := le_rfl)).clm_apply contDiffAt_const

/-- `Dfun F i` is as smooth at `q` as `F` is, one order lower for each time derivative. -/
lemma contDiffAt_Dfun_le {q : ℝ × E} {N : ℕ}
    (hF : ContDiffAt ℝ (N : WithTop ℕ∞) F q) (i : ℕ) (hi : i ≤ N) :
    ContDiffAt ℝ ((N - i : ℕ) : WithTop ℕ∞) (sliceD F i) q := by
  induction i with
  | zero => simpa [sliceD_zero] using hF
  | succ i ih =>
    have h1 : ContDiffAt ℝ (((N - (i + 1)) + 1 : ℕ) : WithTop ℕ∞)
        (sliceD F i) q := by
      have h := ih (by omega)
      rwa [show N - i = (N - (i + 1)) + 1 from by omega] at h
    have h2 := contDiffAt_tDerFun (N := N - (i + 1)) h1
    rwa [← sliceD_succ] at h2

/-- Smoothness of the spatial slice of an iterated time derivative. -/
lemma contDiffAt_Dfun_slice {M : ℕ}
    (hF : ContDiffAt ℝ ((M : ℕ) : WithTop ℕ∞) F p) (j : ℕ) (N : ℕ) (hN : j + N ≤ M) :
    ContDiffAt ℝ (N : WithTop ℕ∞)
      (fun y : E => sliceD F j (p.1, y)) p.2 := by
  have h1 : ContDiffAt ℝ (N : WithTop ℕ∞) (sliceD F j) p :=
    (contDiffAt_Dfun_le hF j (by omega)).of_le (by exact_mod_cast (show N ≤ M - j by omega))
  exact h1.comp p.2 (contDiffAt_const.prodMk contDiffAt_id)

/-- The `j`-th time derivative of the time derivative of `F` is the `(j+1)`-st time derivative
of `F`. -/
lemma sliceD_tDeriv_eq {t : ℝ} {y : E} (j : ℕ)
    (hF : ContDiffAt ℝ (1 : WithTop ℕ∞) F (t, y)) :
    sliceD (fun q : ℝ × E => fderiv ℝ F q (1, 0)) j (t, y)
      = sliceD F (j + 1) (t, y) := by
  have hev : (fun s : ℝ => (fderiv ℝ F (s, y)) (1, 0))
      =ᶠ[𝓝 t] (fun s : ℝ => deriv (fun s' : ℝ => F (s', y)) s) := by
    have hdiff : ∀ᶠ s : ℝ in 𝓝 t, DifferentiableAt ℝ F (s, y) := by
      have h1 : ∀ᶠ q : ℝ × E in 𝓝 (t, y), DifferentiableAt ℝ F q :=
        (hF.eventually cast_ne_infty).mono (fun q hq => hq.differentiableAt (by simp))
      have htend : Tendsto (fun s : ℝ => (s, y)) (𝓝 t) (𝓝 (t, y)) := by
        rw [nhds_prod_eq]
        exact tendsto_id.prodMk tendsto_const_nhds
      exact htend.eventually h1
    filter_upwards [hdiff] with s hs
    have h := tDerFun_eq_fderiv (w := F) hs
    simpa only [tDerFun] using h.symm
  calc sliceD (fun q : ℝ × E => fderiv ℝ F q (1, 0)) j (t, y)
      = iteratedDeriv j (fun s : ℝ => deriv (fun s' : ℝ => F (s', y)) s) t := by
        show iteratedDeriv j (fun s : ℝ => (fderiv ℝ F (s, y)) (1, 0)) t = _
        exact Filter.EventuallyEq.iteratedDeriv_eq j hev
    _ = iteratedDeriv (j + 1) (fun s : ℝ => F (s, y)) t := by rw [iteratedDeriv_succ']
    _ = sliceD F (j + 1) (t, y) := rfl

/-- The `j`-fold Clairaut identity `∂_t^j ∂_ζ F = ∂_ζ ∂_t^j F`. -/
lemma Dfun_sDeriv_eq {t : ℝ} {y : E} (j : ℕ) (ζ : E)
    (hF : ContDiffAt ℝ ((j + 2 : ℕ) : WithTop ℕ∞) F (t, y)) :
    sliceD (fun q : ℝ × E => fderiv ℝ F q (0, ζ)) j (t, y)
      = (fderiv ℝ (fun y' : E => sliceD F j (t, y')) y) ζ := by
  induction j generalizing t y with
  | zero =>
    have hd : DifferentiableAt ℝ F (t, y) := hF.differentiableAt (by simp)
    simp only [sliceD_zero]
    rw [fderiv_partial_eq F hd]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  | succ j ih =>
    have hFj : ContDiffAt ℝ ((j + 2 : ℕ) : WithTop ℕ∞) F (t, y) :=
      hF.of_le (by exact_mod_cast (show j + 2 ≤ j + 1 + 2 by omega))
    have hmem : ∀ᶠ s : ℝ in 𝓝 t, ContDiffAt ℝ ((j + 2 : ℕ) : WithTop ℕ∞) F (s, y) := by
      have h1 : ∀ᶠ q : ℝ × E in 𝓝 (t, y), ContDiffAt ℝ ((j + 3 : ℕ) : WithTop ℕ∞) F q :=
        hF.eventually cast_ne_infty
      have h2 : ∀ᶠ q : ℝ × E in 𝓝 (t, y), ContDiffAt ℝ ((j + 2 : ℕ) : WithTop ℕ∞) F q :=
        h1.mono (fun q hq => hq.of_le (by exact_mod_cast (show j + 2 ≤ j + 3 by omega)))
      have htend : Tendsto (fun s : ℝ => (s, y)) (𝓝 t) (𝓝 (t, y)) := by
        rw [nhds_prod_eq]
        exact tendsto_id.prodMk tendsto_const_nhds
      exact htend.eventually h2
    have hfun : (fun s : ℝ =>
          sliceD (fun q : ℝ × E => fderiv ℝ F q (0, ζ)) j (s, y))
        =ᶠ[𝓝 t] (fun s : ℝ =>
          (fderiv ℝ (fun y' : E => sliceD F j (s, y')) y) ζ) := by
      filter_upwards [hmem] with s hs
      exact ih hs
    have hderiv : sliceD (fun q : ℝ × E => fderiv ℝ F q (0, ζ))
          (j + 1) (t, y)
        = deriv (fun s : ℝ =>
            (fderiv ℝ (fun y' : E => sliceD F j (s, y')) y) ζ) t := by
      rw [show sliceD (fun q : ℝ × E => fderiv ℝ F q (0, ζ)) (j + 1) (t, y)
          = deriv (fun s : ℝ =>
              sliceD (fun q : ℝ × E => fderiv ℝ F q (0, ζ)) j (s, y)) t
            from by rw [sliceD_succ]; rfl]
      exact Filter.EventuallyEq.deriv_eq hfun
    have hΦ : ContDiffAt ℝ (2 : WithTop ℕ∞) (sliceD F j) (t, y) := by
      have h := contDiffAt_Dfun_le hFj j (by omega)
      rwa [show j + 2 - j = 2 from by omega] at h
    have hcl := Work.Diff.T.clairaut_fderiv_apply (V := E) (G := Z) hΦ ζ
    have hfun2 : (fun u : E => deriv (fun t : ℝ => sliceD F j (t, u)) t)
        = fun y' : E => sliceD F (j + 1) (t, y') := by
      funext y'
      rw [sliceD_succ]
      rfl
    rw [hderiv, hcl.deriv, hfun2]

/-- Peeling one spatial derivative, evaluated at a fixed tuple. -/
lemma norm_eval_iteratedFDeriv_fderiv_apply_le {G : E → Z} {x : E} {l : ℕ} {ζ : E}
    (hG : ContDiffAt ℝ ((l + 1 : ℕ) : WithTop ℕ∞) G x) (w : Fin l → E) :
    ‖(iteratedFDeriv ℝ l (fun y : E => fderiv ℝ G y ζ) x) w‖
      ≤ ‖ζ‖ * ‖iteratedFDeriv ℝ (l + 1) G x‖ * ∏ i : Fin l, ‖w i‖ := by
  have key : (iteratedFDeriv ℝ l (fun y : E => fderiv ℝ G y ζ) x) w
      = (iteratedFDeriv ℝ (l + 1) G x) (Fin.snoc (α := fun _ : Fin (l + 1) => E) w ζ) := by
    have hf : ContDiffAt ℝ ((l : ℕ) : WithTop ℕ∞) (fderiv ℝ G) x :=
      hG.fderiv_right (hmn := le_rfl)
    exact (iteratedFDeriv_succ_snoc_apply (V := E) (W := Z) (G := G) (q := x)
      (k := l) hf le_rfl w ζ).symm
  rw [key]
  refine le_trans (ContinuousMultilinearMap.le_opNorm _ _) ?_
  have hprod : ∏ i : Fin (l + 1),
      ‖(Fin.snoc (α := fun _ : Fin (l + 1) => E) w ζ) i‖ = (∏ i : Fin l, ‖w i‖) * ‖ζ‖ := by
    rw [Fin.prod_univ_castSucc]
    simp [Fin.snoc_castSucc, Fin.snoc_last]
  rw [hprod]
  have heq : ‖iteratedFDeriv ℝ (l + 1) G x‖ * ((∏ i : Fin l, ‖w i‖) * ‖ζ‖)
      = ‖ζ‖ * ‖iteratedFDeriv ℝ (l + 1) G x‖ * ∏ i : Fin l, ‖w i‖ := by ring
  rw [heq]

/-- Peeling one spatial derivative: the `l`-th iterated derivative of `y ↦ fderiv ℝ G y ζ` is
bounded by `‖ζ‖` times the `(l+1)`-st iterated derivative of `G`. -/
lemma norm_iteratedFDeriv_fderiv_apply_le {G : E → Z} {x : E} {l : ℕ} {ζ : E}
    (hG : ContDiffAt ℝ ((l + 1 : ℕ) : WithTop ℕ∞) G x) :
    ‖iteratedFDeriv ℝ l (fun y : E => fderiv ℝ G y ζ) x‖
      ≤ ‖ζ‖ * ‖iteratedFDeriv ℝ (l + 1) G x‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound
    (M := ‖ζ‖ * ‖iteratedFDeriv ℝ (l + 1) G x‖)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (fun w => ?_)
  exact norm_eval_iteratedFDeriv_fderiv_apply_le hG (w : Fin l → E)

end Helpers

section Sums

variable {p : ℝ × E} {F : ℝ × E → Z}

/-- The mixed sum of the time derivative is bounded by the next mixed sum. -/
lemma seamSum_tDeriv_le (k : ℕ)
    (hF : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) F p) :
    seamSum k (fun q : ℝ × E => fderiv ℝ F q (1, 0)) p ≤ seamSum (k + 1) F p := by
  have hmem : ∀ᶠ y : E in 𝓝 p.2, ContDiffAt ℝ (1 : WithTop ℕ∞) F (p.1, y) := by
    have h1 : ∀ᶠ q : ℝ × E in 𝓝 p, ContDiffAt ℝ (1 : WithTop ℕ∞) F q :=
      (hF.eventually cast_ne_infty).mono
        (fun q hq => hq.of_le (by exact_mod_cast (show 1 ≤ k + 1 by omega)))
    have htend : Tendsto (fun y : E => (p.1, y)) (𝓝 p.2) (𝓝 p) := by
      rw [nhds_prod_eq]
      exact tendsto_const_nhds.prodMk tendsto_id
    exact htend.eventually h1
  have hterm : ∀ j ∈ Finset.range (k + 1),
      ‖iteratedFDeriv ℝ (k - j) (fun y : E =>
          sliceD (fun q : ℝ × E => fderiv ℝ F q (1, 0)) j (p.1, y)) p.2‖
      = ‖iteratedFDeriv ℝ ((k + 1) - (j + 1)) (fun y : E =>
          sliceD F (j + 1) (p.1, y)) p.2‖ := by
    intro j _
    have hgerm : (fun y : E =>
          sliceD (fun q : ℝ × E => fderiv ℝ F q (1, 0)) j (p.1, y))
        =ᶠ[𝓝 p.2] (fun y : E => sliceD F (j + 1) (p.1, y)) := by
      filter_upwards [hmem] with y hy
      exact sliceD_tDeriv_eq j hy
    rw [iteratedFDeriv_congr_of_eventuallyEq hgerm (k - j)]
    rw [show (k + 1) - (j + 1) = k - j from by omega]
  have hreindex := Finset.sum_range_succ'
    (f := fun i : ℕ => ‖iteratedFDeriv ℝ ((k + 1) - i) (fun y : E =>
      sliceD F i (p.1, y)) p.2‖) (k + 1)
  rw [seamSum, seamSum]
  calc (∑ j ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ (k - j) (fun y : E =>
          sliceD (fun q : ℝ × E => fderiv ℝ F q (1, 0)) j (p.1, y)) p.2‖)
      = (∑ j ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ ((k + 1) - (j + 1)) (fun y : E =>
            sliceD F (j + 1) (p.1, y)) p.2‖) := Finset.sum_congr rfl hterm
    _ ≤ (∑ j ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ ((k + 1) - (j + 1)) (fun y : E =>
            sliceD F (j + 1) (p.1, y)) p.2‖)
          + ‖iteratedFDeriv ℝ ((k + 1) - 0) (fun y : E =>
            sliceD F 0 (p.1, y)) p.2‖ :=
        le_add_of_nonneg_right (norm_nonneg _)
    _ = (∑ i ∈ Finset.range ((k + 1) + 1), ‖iteratedFDeriv ℝ ((k + 1) - i) (fun y : E =>
            sliceD F i (p.1, y)) p.2‖) := hreindex.symm

/-- The mixed sum of a spatial derivative is bounded by `‖ζ‖` times the next mixed sum. -/
lemma seamSum_sDeriv_le (k : ℕ)
    (hF : ContDiffAt ℝ ((k + 2 : ℕ) : WithTop ℕ∞) F p) (ζ : E) :
    seamSum k (fun q : ℝ × E => fderiv ℝ F q (0, ζ)) p ≤ ‖ζ‖ * seamSum (k + 1) F p := by
  have hmem : ∀ᶠ y : E in 𝓝 p.2, ∀ j ≤ k,
      ContDiffAt ℝ ((j + 2 : ℕ) : WithTop ℕ∞) F (p.1, y) := by
    have h1 : ∀ᶠ q : ℝ × E in 𝓝 p, ContDiffAt ℝ ((k + 2 : ℕ) : WithTop ℕ∞) F q :=
      hF.eventually cast_ne_infty
    have htend : Tendsto (fun y : E => (p.1, y)) (𝓝 p.2) (𝓝 p) := by
      rw [nhds_prod_eq]
      exact tendsto_const_nhds.prodMk tendsto_id
    filter_upwards [htend.eventually h1] with y hy j hj
    exact hy.of_le (by exact_mod_cast (show j + 2 ≤ k + 2 by omega))
  have hle : ∀ j ∈ Finset.range (k + 1),
      ‖iteratedFDeriv ℝ (k - j) (fun y : E =>
          sliceD (fun q : ℝ × E => fderiv ℝ F q (0, ζ)) j (p.1, y)) p.2‖
      ≤ ‖ζ‖ * ‖iteratedFDeriv ℝ ((k + 1) - j) (fun y : E =>
          sliceD F j (p.1, y)) p.2‖ := by
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hgerm : (fun y : E =>
          sliceD (fun q : ℝ × E => fderiv ℝ F q (0, ζ)) j (p.1, y))
        =ᶠ[𝓝 p.2] (fun y : E =>
          fderiv ℝ (fun y' : E => sliceD F j (p.1, y')) y ζ) := by
      filter_upwards [hmem] with y hy
      exact Dfun_sDeriv_eq j ζ (hy j hjk)
    rw [iteratedFDeriv_congr_of_eventuallyEq hgerm (k - j)]
    have hb := norm_iteratedFDeriv_fderiv_apply_le
      (G := fun y' : E => sliceD F j (p.1, y')) (x := p.2) (l := k - j)
      (ζ := ζ)
      (contDiffAt_Dfun_slice (hF := hF.of_le (by exact_mod_cast (show k + 1 ≤ k + 2 by omega)))
        j (k - j + 1) (by omega))
    refine le_trans hb ?_
    rw [show (k - j) + 1 = (k + 1) - j from by omega]
  rw [seamSum, seamSum]
  calc (∑ j ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ (k - j) (fun y : E =>
          sliceD (fun q : ℝ × E => fderiv ℝ F q (0, ζ)) j (p.1, y)) p.2‖)
      ≤ ∑ j ∈ Finset.range (k + 1), ‖ζ‖ * ‖iteratedFDeriv ℝ ((k + 1) - j) (fun y : E =>
            sliceD F j (p.1, y)) p.2‖ := Finset.sum_le_sum hle
    _ = ‖ζ‖ * ∑ j ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ ((k + 1) - j) (fun y : E =>
            sliceD F j (p.1, y)) p.2‖ := by rw [Finset.mul_sum]
    _ ≤ ‖ζ‖ * ∑ i ∈ Finset.range ((k + 1) + 1), ‖iteratedFDeriv ℝ ((k + 1) - i) (fun y : E =>
            sliceD F i (p.1, y)) p.2‖ := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg ζ)
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => norm_nonneg _)
        intro x hx
        simp only [Finset.mem_range] at hx ⊢
        omega

end Sums

/-- The main induction: the `m`-th iterated Fréchet derivative is bounded by `2^m` times the
mixed sum. -/
theorem norm_iteratedFDeriv_le_seamSum : ∀ (k : ℕ) (F : ℝ × E → Z) (p : ℝ × E),
    ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) F p →
    ‖iteratedFDeriv ℝ k F p‖ ≤ (2 : ℝ) ^ k * seamSum k F p := by
  intro k
  induction k with
  | zero =>
    intro F p _
    rw [pow_zero, one_mul]
    have h0 : seamSum 0 F p = ‖F p‖ := by
      rw [seamSum, Finset.sum_range_one]
      simp [sliceD_zero, norm_iteratedFDeriv_zero]
    rw [h0, norm_iteratedFDeriv_zero]
  | succ k ih =>
    intro F p hF
    have hFk : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) F p :=
      hF.of_le (by exact_mod_cast (show k + 1 ≤ k + 2 by omega))
    have hfder : ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞) (fderiv ℝ F) p :=
      hF.fderiv_right (hmn := by exact_mod_cast (show k + 1 ≤ k + 2 by omega))
    refine ContinuousMultilinearMap.opNorm_le_bound
      (f := iteratedFDeriv ℝ (k + 1) F p)
      (M := (2 : ℝ) ^ (k + 1) * seamSum (k + 1) F p)
      (mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => norm_nonneg _))) (fun v => ?_)
    obtain ⟨a, ζ, haζ⟩ : ∃ (a : ℝ) (ζ : E), (a, ζ) = v (Fin.last k) := ⟨_, _, rfl⟩
    have hsplit : iteratedFDeriv ℝ (k + 1) F p v
        = a • (iteratedFDeriv ℝ k (fun z : ℝ × E => fderiv ℝ F z (1, 0)) p (Fin.init v))
          + iteratedFDeriv ℝ k (fun z : ℝ × E => fderiv ℝ F z (0, ζ)) p (Fin.init v) := by
      conv_lhs => rw [← Fin.snoc_init_self v]
      rw [iteratedFDeriv_succ_apply_right, Fin.init_snoc, Fin.snoc_last]
      rw [show v (Fin.last k) = a • ((1 : ℝ), (0 : E)) + ((0 : ℝ), ζ) from by
        rw [show v (Fin.last k) = (a, ζ) from haζ.symm]
        ext <;> simp]
      rw [map_add, map_smul]
      rw [← clmApplyConst_of (i := k) hfder le_rfl
            (u := ((1 : ℝ), (0 : E))) (m := Fin.init v),
        ← clmApplyConst_of (i := k) hfder le_rfl
            (u := ((0 : ℝ), ζ)) (m := Fin.init v)]
    rw [hsplit]
    have hTF : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞)
        (fun z : ℝ × E => fderiv ℝ F z (1, 0)) p := contDiffAt_fderiv_apply (N := k + 1) hF
    have hSF : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞)
        (fun z : ℝ × E => fderiv ℝ F z (0, ζ)) p := contDiffAt_fderiv_apply (N := k + 1) hF
    have hS : (0 : ℝ) ≤ seamSum (k + 1) F p := Finset.sum_nonneg (fun i _ => norm_nonneg _)
    have hT : (0 : ℝ) ≤ (2 : ℝ) ^ k := by positivity
    have hP : (0 : ℝ) ≤ ∏ i : Fin k, ‖(Fin.init v) i‖ :=
      Finset.prod_nonneg (fun i _ => norm_nonneg _)
    have hN : (0 : ℝ) ≤ ‖(a, ζ)‖ := norm_nonneg _
    have hA : ‖a‖ ≤ ‖(a, ζ)‖ := by rw [Prod.norm_def]; exact le_max_left _ _
    have hB : ‖ζ‖ ≤ ‖(a, ζ)‖ := by rw [Prod.norm_def]; exact le_max_right _ _
    have hX : ‖iteratedFDeriv ℝ k (fun z : ℝ × E => fderiv ℝ F z (1, 0)) p (Fin.init v)‖
        ≤ ((2 : ℝ) ^ k * seamSum (k + 1) F p) * ∏ i : Fin k, ‖(Fin.init v) i‖ := by
      refine le_trans (ContinuousMultilinearMap.le_opNorm _ _) ?_
      refine mul_le_mul_of_nonneg_right ?_ hP
      exact le_trans (ih _ _ hTF)
        (mul_le_mul_of_nonneg_left (seamSum_tDeriv_le k hFk) hT)
    have hY : ‖iteratedFDeriv ℝ k (fun z : ℝ × E => fderiv ℝ F z (0, ζ)) p (Fin.init v)‖
        ≤ ((2 : ℝ) ^ k * (‖(a, ζ)‖ * seamSum (k + 1) F p))
            * ∏ i : Fin k, ‖(Fin.init v) i‖ := by
      refine le_trans (ContinuousMultilinearMap.le_opNorm _ _) ?_
      refine mul_le_mul_of_nonneg_right ?_ hP
      refine le_trans (ih _ _ hSF) ?_
      exact mul_le_mul_of_nonneg_left
        (le_trans (seamSum_sDeriv_le k hF ζ) (mul_le_mul_of_nonneg_right hB hS)) hT
    have hprod : (∏ i : Fin k, ‖(Fin.init v) i‖) * ‖(a, ζ)‖ = ∏ i : Fin (k + 1), ‖v i‖ := by
      rw [Fin.prod_univ_castSucc, ← haζ]
      rfl
    calc ‖a • (iteratedFDeriv ℝ k (fun z : ℝ × E => fderiv ℝ F z (1, 0)) p (Fin.init v))
          + iteratedFDeriv ℝ k (fun z : ℝ × E => fderiv ℝ F z (0, ζ)) p (Fin.init v)‖
        ≤ ‖a • (iteratedFDeriv ℝ k (fun z : ℝ × E => fderiv ℝ F z (1, 0)) p (Fin.init v))‖
          + ‖iteratedFDeriv ℝ k (fun z : ℝ × E => fderiv ℝ F z (0, ζ)) p (Fin.init v)‖ :=
          norm_add_le _ _
      _ = ‖a‖ * ‖iteratedFDeriv ℝ k (fun z : ℝ × E => fderiv ℝ F z (1, 0)) p (Fin.init v)‖
          + ‖iteratedFDeriv ℝ k (fun z : ℝ × E => fderiv ℝ F z (0, ζ)) p (Fin.init v)‖ := by
          rw [norm_smul]
      _ ≤ ‖(a, ζ)‖ * (((2 : ℝ) ^ k * seamSum (k + 1) F p) * (∏ i : Fin k, ‖(Fin.init v) i‖))
          + ((2 : ℝ) ^ k * (‖(a, ζ)‖ * seamSum (k + 1) F p))
              * (∏ i : Fin k, ‖(Fin.init v) i‖) := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul hA hX (norm_nonneg _) hN
          · exact hY
      _ = (2 : ℝ) ^ (k + 1) * seamSum (k + 1) F p * ∏ i : Fin (k + 1), ‖v i‖ := by
          rw [← hprod, pow_succ]
          ring

/-! ## The main theorem -/

/-- **The `j`-th jet is bounded by the "space-outer, time-inner" mixed partials.**
For `F : ℝ × E → Z` smooth at `p`, the operator norm of the `j`-th iterated Fréchet derivative is
bounded by a constant (depending only on `j`) times the sum of the norms of the mixed partials
`∂_y^{j-k} ∂_t^k F` at `p`, where the `j-k` space derivatives are outermost and the `k` time
derivatives innermost (i.e. the mixed partials appearing here are the `m = j-k` fold space-jets of
the function `y ↦ ∂_t^k F (p.1,y)`, at `p.2`).

This is the bridge between the hypothesis "all these mixed partials tend to `0` at a seam" and the
conclusion "the full jet tends to `0` at the seam".

Route (all ingredients are Mathlib, `Submission/Commons/Analysis/Calculus/FDeriv/secondDirectional_commute_two`
(already proved, C² Clairaut), `Submission/Work/Diff/EXT/MixedSum` and `Submission/Work/Diff/EXT/ufslice`
(both proved)):
* `dOp u F := fun q => fderiv ℝ F q u`, `tower [u₁,…,u_j] F := dOp u₁ (… (dOp u_j F))` (head
  outermost).  For `F` smooth at `p`: `iteratedFDeriv ℝ j F p v = tower (List.ofFn v) F p`
  (induction on `j`, `iteratedFDeriv_succ_apply_left`).
* `dOp u (dOp v F) = dOp v (dOp u F)` on any open set on which `F` is `C^∞`: this is
  `Commons.Analysis.Calculus.FDeriv.secondDirectional_commute_two` applied to `F` and to the
  intermediate functions; hence `tower` is invariant under permuting the list.
* the jet at `p` on the tuple `((0,η_0),…,(0,η_{m-1}),(1,0),…,(1,0))` equals
  `(iteratedFDeriv ℝ m (fun y' => iteratedDeriv k (fun t => F (t,y')) p.1) p.2) η`
  (use `MixedSum.iteratedFDeriv_slice_eq` and `ufslice.tder_eq_jet`).
* multilinear expansion: `v i = ((v i).1, 0) + (0, (v i).2)` gives
  `B v = ∑_{S : Finset (Fin j)} B (fun i => if i ∈ S then ((v i).1, 0) else (0, (v i).2))` for any
  `j`-multilinear `B`; combining with the previous items gives the bound with `C = 2 ^ j`. -/
theorem norm_iteratedFDeriv_le_seamPartials
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (F : ℝ × E → Z) (p : ℝ × E), ContDiffAt ℝ (⊤ : ℕ∞) F p →
        ‖iteratedFDeriv ℝ j F p‖ ≤ C * ∑ k ∈ Finset.range (j + 1),
          ‖iteratedFDeriv ℝ (j - k) (fun y' : E => iteratedDeriv k (fun t : ℝ => F (t, y')) p.1) p.2‖ := by
  refine ⟨(2 : ℝ) ^ j, by positivity, ?_⟩
  intro F p hF
  have hF' : ContDiffAt ℝ ((j + 1 : ℕ) : WithTop ℕ∞) F p :=
    hF.of_le (WithTop.coe_le_coe.mpr le_top)
  have hmain := norm_iteratedFDeriv_le_seamSum j F p hF'
  simpa [seamSum, sliceD] using hmain

end Work.Diff.EXT
