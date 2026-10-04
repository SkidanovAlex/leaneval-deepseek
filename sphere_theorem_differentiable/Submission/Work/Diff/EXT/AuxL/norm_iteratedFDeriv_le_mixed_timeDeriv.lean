import Mathlib
import Submission.Work.Diff.EXT.jets_core
import Submission.Work.Diff.EXT.MixedSum
import Submission.Work.Diff.T.clairaut_fderiv_apply

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.AuxL

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-! ## Auxiliary calculus for the mixed-derivative decomposition

Everything below is stated with *finite* orders of smoothness at a single point: this is what
`ContDiffAt ℝ (⊤ : ℕ∞) f p` provides (it gives `C^N` at `p` for every finite `N`), and it is enough
at every step of the argument. -/

/-- The sum of the norms of the mixed derivatives `∂_y^{m-j} ∂_t^j F` at `p`. -/
noncomputable def mixSum (m : ℕ) (F : ℝ × E → Z) (p : ℝ × E) : ℝ :=
  ∑ j ∈ Finset.range (m + 1),
    ‖iteratedFDeriv ℝ (m - j)
      (fun y : E => Work.Diff.EXT.JetsCore.Dfun F j (p.1, y)) p.2‖

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
    ContDiffAt ℝ ((N - i : ℕ) : WithTop ℕ∞) (Work.Diff.EXT.JetsCore.Dfun F i) q := by
  induction i with
  | zero => simpa [Work.Diff.EXT.JetsCore.Dfun_zero] using hF
  | succ i ih =>
    have h1 : ContDiffAt ℝ (((N - (i + 1)) + 1 : ℕ) : WithTop ℕ∞)
        (Work.Diff.EXT.JetsCore.Dfun F i) q := by
      have h := ih (by omega)
      rwa [show N - i = (N - (i + 1)) + 1 from by omega] at h
    have h2 := Work.Diff.EXT.JetsCore.contDiffAt_tDerFun (N := N - (i + 1)) h1
    rwa [← Work.Diff.EXT.JetsCore.Dfun_succ] at h2

/-- Smoothness of the spatial slice of an iterated time derivative. -/
lemma contDiffAt_Dfun_slice {M : ℕ}
    (hF : ContDiffAt ℝ ((M : ℕ) : WithTop ℕ∞) F p) (j : ℕ) (N : ℕ) (hN : j + N ≤ M) :
    ContDiffAt ℝ (N : WithTop ℕ∞)
      (fun y : E => Work.Diff.EXT.JetsCore.Dfun F j (p.1, y)) p.2 := by
  have h1 : ContDiffAt ℝ (N : WithTop ℕ∞) (Work.Diff.EXT.JetsCore.Dfun F j) p :=
    (contDiffAt_Dfun_le hF j (by omega)).of_le (by exact_mod_cast (show N ≤ M - j by omega))
  exact h1.comp p.2 (contDiffAt_const.prodMk contDiffAt_id)

/-- The `j`-th time derivative of the time derivative of `F` is the `(j+1)`-st time derivative
of `F`. -/
lemma Dfun_tDeriv_eq {t : ℝ} {y : E} (j : ℕ)
    (hF : ContDiffAt ℝ (1 : WithTop ℕ∞) F (t, y)) :
    Work.Diff.EXT.JetsCore.Dfun (fun q : ℝ × E => fderiv ℝ F q (1, 0)) j (t, y)
      = Work.Diff.EXT.JetsCore.Dfun F (j + 1) (t, y) := by
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
    have h := Work.Diff.EXT.JetsCore.tDerFun_eq_fderiv (w := F) hs
    simpa only [Work.Diff.EXT.JetsCore.tDerFun] using h.symm
  calc Work.Diff.EXT.JetsCore.Dfun (fun q : ℝ × E => fderiv ℝ F q (1, 0)) j (t, y)
      = iteratedDeriv j (fun s : ℝ => deriv (fun s' : ℝ => F (s', y)) s) t := by
        show iteratedDeriv j (fun s : ℝ => (fderiv ℝ F (s, y)) (1, 0)) t = _
        exact Filter.EventuallyEq.iteratedDeriv_eq j hev
    _ = iteratedDeriv (j + 1) (fun s : ℝ => F (s, y)) t := by rw [iteratedDeriv_succ']
    _ = Work.Diff.EXT.JetsCore.Dfun F (j + 1) (t, y) := rfl

/-- The `j`-fold Clairaut identity `∂_t^j ∂_ζ F = ∂_ζ ∂_t^j F`. -/
lemma Dfun_sDeriv_eq {t : ℝ} {y : E} (j : ℕ) (ζ : E)
    (hF : ContDiffAt ℝ ((j + 2 : ℕ) : WithTop ℕ∞) F (t, y)) :
    Work.Diff.EXT.JetsCore.Dfun (fun q : ℝ × E => fderiv ℝ F q (0, ζ)) j (t, y)
      = (fderiv ℝ (fun y' : E => Work.Diff.EXT.JetsCore.Dfun F j (t, y')) y) ζ := by
  induction j generalizing t y with
  | zero =>
    have hd : DifferentiableAt ℝ F (t, y) := hF.differentiableAt (by simp)
    simp only [Work.Diff.EXT.JetsCore.Dfun_zero]
    rw [Work.Diff.EXT.JetsCore.fderiv_partial_eq F hd]
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
          Work.Diff.EXT.JetsCore.Dfun (fun q : ℝ × E => fderiv ℝ F q (0, ζ)) j (s, y))
        =ᶠ[𝓝 t] (fun s : ℝ =>
          (fderiv ℝ (fun y' : E => Work.Diff.EXT.JetsCore.Dfun F j (s, y')) y) ζ) := by
      filter_upwards [hmem] with s hs
      exact ih hs
    have hderiv : Work.Diff.EXT.JetsCore.Dfun (fun q : ℝ × E => fderiv ℝ F q (0, ζ))
          (j + 1) (t, y)
        = deriv (fun s : ℝ =>
            (fderiv ℝ (fun y' : E => Work.Diff.EXT.JetsCore.Dfun F j (s, y')) y) ζ) t := by
      rw [show Work.Diff.EXT.JetsCore.Dfun (fun q : ℝ × E => fderiv ℝ F q (0, ζ)) (j + 1) (t, y)
          = deriv (fun s : ℝ =>
              Work.Diff.EXT.JetsCore.Dfun (fun q : ℝ × E => fderiv ℝ F q (0, ζ)) j (s, y)) t
            from by rw [Work.Diff.EXT.JetsCore.Dfun_succ]; rfl]
      exact Filter.EventuallyEq.deriv_eq hfun
    have hΦ : ContDiffAt ℝ (2 : WithTop ℕ∞) (Work.Diff.EXT.JetsCore.Dfun F j) (t, y) := by
      have h := contDiffAt_Dfun_le hFj j (by omega)
      rwa [show j + 2 - j = 2 from by omega] at h
    have hcl := Work.Diff.T.clairaut_fderiv_apply (V := E) (G := Z) hΦ ζ
    have hfun2 : (fun u : E => deriv (fun t : ℝ => Work.Diff.EXT.JetsCore.Dfun F j (t, u)) t)
        = fun y' : E => Work.Diff.EXT.JetsCore.Dfun F (j + 1) (t, y') := by
      funext y'
      rw [Work.Diff.EXT.JetsCore.Dfun_succ]
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
    exact (Work.Diff.EXT.iteratedFDeriv_succ_snoc_apply (V := E) (W := Z) (G := G) (q := x)
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
lemma mixSum_tDeriv_le (k : ℕ)
    (hF : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) F p) :
    mixSum k (fun q : ℝ × E => fderiv ℝ F q (1, 0)) p ≤ mixSum (k + 1) F p := by
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
          Work.Diff.EXT.JetsCore.Dfun (fun q : ℝ × E => fderiv ℝ F q (1, 0)) j (p.1, y)) p.2‖
      = ‖iteratedFDeriv ℝ ((k + 1) - (j + 1)) (fun y : E =>
          Work.Diff.EXT.JetsCore.Dfun F (j + 1) (p.1, y)) p.2‖ := by
    intro j _
    have hgerm : (fun y : E =>
          Work.Diff.EXT.JetsCore.Dfun (fun q : ℝ × E => fderiv ℝ F q (1, 0)) j (p.1, y))
        =ᶠ[𝓝 p.2] (fun y : E => Work.Diff.EXT.JetsCore.Dfun F (j + 1) (p.1, y)) := by
      filter_upwards [hmem] with y hy
      exact Dfun_tDeriv_eq j hy
    rw [iteratedFDeriv_congr_of_eventuallyEq hgerm (k - j)]
    rw [show (k + 1) - (j + 1) = k - j from by omega]
  have hreindex := Finset.sum_range_succ'
    (f := fun i : ℕ => ‖iteratedFDeriv ℝ ((k + 1) - i) (fun y : E =>
      Work.Diff.EXT.JetsCore.Dfun F i (p.1, y)) p.2‖) (k + 1)
  rw [mixSum, mixSum]
  calc (∑ j ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ (k - j) (fun y : E =>
          Work.Diff.EXT.JetsCore.Dfun (fun q : ℝ × E => fderiv ℝ F q (1, 0)) j (p.1, y)) p.2‖)
      = (∑ j ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ ((k + 1) - (j + 1)) (fun y : E =>
            Work.Diff.EXT.JetsCore.Dfun F (j + 1) (p.1, y)) p.2‖) := Finset.sum_congr rfl hterm
    _ ≤ (∑ j ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ ((k + 1) - (j + 1)) (fun y : E =>
            Work.Diff.EXT.JetsCore.Dfun F (j + 1) (p.1, y)) p.2‖)
          + ‖iteratedFDeriv ℝ ((k + 1) - 0) (fun y : E =>
            Work.Diff.EXT.JetsCore.Dfun F 0 (p.1, y)) p.2‖ :=
        le_add_of_nonneg_right (norm_nonneg _)
    _ = (∑ i ∈ Finset.range ((k + 1) + 1), ‖iteratedFDeriv ℝ ((k + 1) - i) (fun y : E =>
            Work.Diff.EXT.JetsCore.Dfun F i (p.1, y)) p.2‖) := hreindex.symm

/-- The mixed sum of a spatial derivative is bounded by `‖ζ‖` times the next mixed sum. -/
lemma mixSum_sDeriv_le (k : ℕ)
    (hF : ContDiffAt ℝ ((k + 2 : ℕ) : WithTop ℕ∞) F p) (ζ : E) :
    mixSum k (fun q : ℝ × E => fderiv ℝ F q (0, ζ)) p ≤ ‖ζ‖ * mixSum (k + 1) F p := by
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
          Work.Diff.EXT.JetsCore.Dfun (fun q : ℝ × E => fderiv ℝ F q (0, ζ)) j (p.1, y)) p.2‖
      ≤ ‖ζ‖ * ‖iteratedFDeriv ℝ ((k + 1) - j) (fun y : E =>
          Work.Diff.EXT.JetsCore.Dfun F j (p.1, y)) p.2‖ := by
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hgerm : (fun y : E =>
          Work.Diff.EXT.JetsCore.Dfun (fun q : ℝ × E => fderiv ℝ F q (0, ζ)) j (p.1, y))
        =ᶠ[𝓝 p.2] (fun y : E =>
          fderiv ℝ (fun y' : E => Work.Diff.EXT.JetsCore.Dfun F j (p.1, y')) y ζ) := by
      filter_upwards [hmem] with y hy
      exact Dfun_sDeriv_eq j ζ (hy j hjk)
    rw [iteratedFDeriv_congr_of_eventuallyEq hgerm (k - j)]
    have hb := norm_iteratedFDeriv_fderiv_apply_le
      (G := fun y' : E => Work.Diff.EXT.JetsCore.Dfun F j (p.1, y')) (x := p.2) (l := k - j)
      (ζ := ζ)
      (contDiffAt_Dfun_slice (hF := hF.of_le (by exact_mod_cast (show k + 1 ≤ k + 2 by omega)))
        j (k - j + 1) (by omega))
    refine le_trans hb ?_
    rw [show (k - j) + 1 = (k + 1) - j from by omega]
  rw [mixSum, mixSum]
  calc (∑ j ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ (k - j) (fun y : E =>
          Work.Diff.EXT.JetsCore.Dfun (fun q : ℝ × E => fderiv ℝ F q (0, ζ)) j (p.1, y)) p.2‖)
      ≤ ∑ j ∈ Finset.range (k + 1), ‖ζ‖ * ‖iteratedFDeriv ℝ ((k + 1) - j) (fun y : E =>
            Work.Diff.EXT.JetsCore.Dfun F j (p.1, y)) p.2‖ := Finset.sum_le_sum hle
    _ = ‖ζ‖ * ∑ j ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ ((k + 1) - j) (fun y : E =>
            Work.Diff.EXT.JetsCore.Dfun F j (p.1, y)) p.2‖ := by rw [Finset.mul_sum]
    _ ≤ ‖ζ‖ * ∑ i ∈ Finset.range ((k + 1) + 1), ‖iteratedFDeriv ℝ ((k + 1) - i) (fun y : E =>
            Work.Diff.EXT.JetsCore.Dfun F i (p.1, y)) p.2‖ := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg ζ)
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => norm_nonneg _)
        intro x hx
        simp only [Finset.mem_range] at hx ⊢
        omega

end Sums

/-- The main induction: the `m`-th iterated Fréchet derivative is bounded by `2^m` times the
mixed sum. -/
theorem norm_iteratedFDeriv_le_mixSum : ∀ (k : ℕ) (F : ℝ × E → Z) (p : ℝ × E),
    ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) F p →
    ‖iteratedFDeriv ℝ k F p‖ ≤ (2 : ℝ) ^ k * mixSum k F p := by
  intro k
  induction k with
  | zero =>
    intro F p _
    rw [pow_zero, one_mul]
    have h0 : mixSum 0 F p = ‖F p‖ := by
      rw [mixSum, Finset.sum_range_one]
      simp [Work.Diff.EXT.JetsCore.Dfun_zero, norm_iteratedFDeriv_zero]
    rw [h0, norm_iteratedFDeriv_zero]
  | succ k ih =>
    intro F p hF
    have hFk : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) F p :=
      hF.of_le (by exact_mod_cast (show k + 1 ≤ k + 2 by omega))
    have hfder : ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞) (fderiv ℝ F) p :=
      hF.fderiv_right (hmn := by exact_mod_cast (show k + 1 ≤ k + 2 by omega))
    refine ContinuousMultilinearMap.opNorm_le_bound
      (f := iteratedFDeriv ℝ (k + 1) F p)
      (M := (2 : ℝ) ^ (k + 1) * mixSum (k + 1) F p)
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
      rw [← Work.Diff.EXT.clmApplyConst_of (i := k) hfder le_rfl
            (u := ((1 : ℝ), (0 : E))) (m := Fin.init v),
        ← Work.Diff.EXT.clmApplyConst_of (i := k) hfder le_rfl
            (u := ((0 : ℝ), ζ)) (m := Fin.init v)]
    rw [hsplit]
    have hTF : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞)
        (fun z : ℝ × E => fderiv ℝ F z (1, 0)) p := contDiffAt_fderiv_apply (N := k + 1) hF
    have hSF : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞)
        (fun z : ℝ × E => fderiv ℝ F z (0, ζ)) p := contDiffAt_fderiv_apply (N := k + 1) hF
    have hS : (0 : ℝ) ≤ mixSum (k + 1) F p := Finset.sum_nonneg (fun i _ => norm_nonneg _)
    have hT : (0 : ℝ) ≤ (2 : ℝ) ^ k := by positivity
    have hP : (0 : ℝ) ≤ ∏ i : Fin k, ‖(Fin.init v) i‖ :=
      Finset.prod_nonneg (fun i _ => norm_nonneg _)
    have hN : (0 : ℝ) ≤ ‖(a, ζ)‖ := norm_nonneg _
    have hA : ‖a‖ ≤ ‖(a, ζ)‖ := by rw [Prod.norm_def]; exact le_max_left _ _
    have hB : ‖ζ‖ ≤ ‖(a, ζ)‖ := by rw [Prod.norm_def]; exact le_max_right _ _
    have hX : ‖iteratedFDeriv ℝ k (fun z : ℝ × E => fderiv ℝ F z (1, 0)) p (Fin.init v)‖
        ≤ ((2 : ℝ) ^ k * mixSum (k + 1) F p) * ∏ i : Fin k, ‖(Fin.init v) i‖ := by
      refine le_trans (ContinuousMultilinearMap.le_opNorm _ _) ?_
      refine mul_le_mul_of_nonneg_right ?_ hP
      exact le_trans (ih _ _ hTF)
        (mul_le_mul_of_nonneg_left (mixSum_tDeriv_le k hFk) hT)
    have hY : ‖iteratedFDeriv ℝ k (fun z : ℝ × E => fderiv ℝ F z (0, ζ)) p (Fin.init v)‖
        ≤ ((2 : ℝ) ^ k * (‖(a, ζ)‖ * mixSum (k + 1) F p))
            * ∏ i : Fin k, ‖(Fin.init v) i‖ := by
      refine le_trans (ContinuousMultilinearMap.le_opNorm _ _) ?_
      refine mul_le_mul_of_nonneg_right ?_ hP
      refine le_trans (ih _ _ hSF) ?_
      exact mul_le_mul_of_nonneg_left
        (le_trans (mixSum_sDeriv_le k hF ζ) (mul_le_mul_of_nonneg_right hB hS)) hT
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
      _ ≤ ‖(a, ζ)‖ * (((2 : ℝ) ^ k * mixSum (k + 1) F p) * (∏ i : Fin k, ‖(Fin.init v) i‖))
          + ((2 : ℝ) ^ k * (‖(a, ζ)‖ * mixSum (k + 1) F p))
              * (∏ i : Fin k, ‖(Fin.init v) i‖) := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul hA hX (norm_nonneg _) hN
          · exact hY
      _ = (2 : ℝ) ^ (k + 1) * mixSum (k + 1) F p * ∏ i : Fin (k + 1), ‖v i‖ := by
          rw [← hprod, pow_succ]
          ring

/-- Mixed-derivative decomposition: for a `C^∞` function `f : ℝ × E → Z` at `p` and every `m`, there is a constant `C` depending only on `m` and on the finite-dimensional space `E`, such that the norm of the `m`-th ambient iterated Fréchet derivative of `f` at `p` is at most `C` times the sum, over `j ≤ m`, of the norms of the `(m-j)`-th *spatial* iterated Fréchet derivatives at `p.2` of the `j`-th *time* derivative `Dfun f j (p.1, ·)` (where `Dfun f j` is the `j`-fold `deriv` in the first variable, `Work.Diff.EXT.JetsCore.Dfun`).

Route: decompose every argument `vᵢ = aᵢ(1,0) + (0,bᵢ)` (product/max norm on `ℝ × E`), expand multi-linearly, and identify the terms with `|S| = j` as the mixed derivative `∂ₜ^j ∂_y^{m-j}`; Clairaut's theorem (available from `ContDiffAt ℝ (⊤ : ℕ∞) f p`) identifies these with the `(m-j)`-spatial derivative of `Dfun f j`. -/
theorem norm_iteratedFDeriv_le_mixed_timeDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] (f : ℝ × E → Z) (p : ℝ × E),
        ContDiffAt ℝ (⊤ : ℕ∞) f p →
        ‖iteratedFDeriv ℝ m f p‖ ≤ C * ∑ j ∈ Finset.range (m + 1),
          ‖iteratedFDeriv ℝ (m - j) (fun y : E => Work.Diff.EXT.JetsCore.Dfun f j (p.1, y)) p.2‖ := by
  refine ⟨(2 : ℝ) ^ m, by positivity, ?_⟩
  intro Z _ _ f p hf
  have hF : ContDiffAt ℝ ((m + 1 : ℕ) : WithTop ℕ∞) f p :=
    hf.of_le (WithTop.coe_le_coe.mpr le_top)
  have hmain := norm_iteratedFDeriv_le_mixSum m f p hF
  simpa [mixSum] using hmain

end Work.Diff.EXT.AuxL
