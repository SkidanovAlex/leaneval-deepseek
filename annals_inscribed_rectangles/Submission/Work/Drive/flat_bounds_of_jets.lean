import Mathlib

/-!
# Flat bounds for the jets of a function flat along a hyperplane

Let `S : X × ℝ → E` be smooth and flat to order `K` along the hyperplane `t = 0`
(all `t`-derivatives of order `< K` vanish at `(x,0)` for every `x`).  Then near any
`(x₀, 0)` the `j`-th jet of `S` is bounded by `C * t ^ (K - j)`.

The proof has two ingredients.
* `jets_flat_vanish_local`: flatness to order `N` forces the whole `r`-th jet (`r < N`)
  to vanish at every point of the hyperplane.
* a Taylor/mean-value estimate: differentiating the slice `s ↦ 𝔡^j S (x,s)` gains one
  power of `t`, and the lower order jets vanish on the hyperplane.
-/

namespace Work.Drive

open Set Filter Topology
open scoped ContDiff

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For a smooth function, the `(n+2)`-th iterated derivative evaluated on a tuple `M` equals the
second derivative of the `n`-th iterated derivative, evaluated on the first two entries `M 0`, `M 1`
and then on the remaining entries. -/
private lemma iteratedFDeriv_succ_succ_apply {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (n : ℕ) (z : E) (M : Fin (n + 2) → E) :
    iteratedFDeriv ℝ (n + 2) f z M =
      (fderiv ℝ (fderiv ℝ (iteratedFDeriv ℝ n f)) z (M 0) (M 1))
        (fun i => M i.succ.succ) := by
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (iteratedFDeriv ℝ n f) :=
    hf.iteratedFDeriv_right' (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (i := n)
  have hg1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (iteratedFDeriv ℝ (n + 1) f) :=
    hf.iteratedFDeriv_right' (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (i := n + 1)
  have hg_diff : ∀ y, DifferentiableAt ℝ (iteratedFDeriv ℝ n f) y :=
    fun y => (hg.differentiable (by simp)) y
  have hg1_diff : DifferentiableAt ℝ (iteratedFDeriv ℝ (n + 1) f) z :=
    (hg1.differentiable (by simp)) z
  have hdg : DifferentiableAt ℝ (fderiv ℝ (iteratedFDeriv ℝ n f)) z := by
    have h2 : ContDiff ℝ 1 (fderiv ℝ (iteratedFDeriv ℝ n f)) :=
      hg.fderiv_right (m := 1) (by decide)
    exact h2.contDiffAt.differentiableAt (by simp)
  have hdP : DifferentiableAt ℝ
      (fun y => (fderiv ℝ (iteratedFDeriv ℝ n f) y) (Fin.tail M 0)) z :=
    hdg.clm_apply (differentiableAt_const _)
  rw [DifferentiableAt.iteratedFDeriv_succ_apply_left' (m := M) hg1_diff]
  have hfun : (fun y => (iteratedFDeriv ℝ (n + 1) f y) (Fin.tail M))
      = fun y => fderiv ℝ
          (fun y' => (iteratedFDeriv ℝ n f y') (Fin.tail (Fin.tail M))) y ((Fin.tail M) 0) := by
    funext y
    exact DifferentiableAt.iteratedFDeriv_succ_apply_left' (m := Fin.tail M) (hg_diff y)
  rw [hfun]
  have hC : (fderiv ℝ (fun y => (fderiv ℝ
        (fun y' => (iteratedFDeriv ℝ n f y') (Fin.tail (Fin.tail M))) y) (Fin.tail M 0)) z) (M 0)
      = (((fderiv ℝ (fderiv ℝ (iteratedFDeriv ℝ n f)) z) (M 0)) (Fin.tail M 0))
          (Fin.tail (Fin.tail M)) := by
    have hfun2 : (fun y => (fderiv ℝ
          (fun y' => (iteratedFDeriv ℝ n f y') (Fin.tail (Fin.tail M))) y) (Fin.tail M 0))
        = (fun y => (fderiv ℝ (iteratedFDeriv ℝ n f) y) (Fin.tail M 0)
            (Fin.tail (Fin.tail M))) := by
      funext y
      rw [fderiv_continuousMultilinear_apply_const (hg_diff y) (Fin.tail (Fin.tail M))]
      rw [ContinuousLinearMap.flipMultilinear_apply_apply]
    rw [hfun2]
    rw [fderiv_continuousMultilinear_apply_const_apply hdP (Fin.tail (Fin.tail M)) (M 0)]
    rw [fderiv_clm_apply hdg (differentiableAt_const _)]
    simp [ContinuousLinearMap.flip_apply, fderiv_const_apply]
  rw [hC]
  rfl

theorem iteratedFDeriv_swap_first_two_local {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {S : X × ℝ → E}
    (hS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S)
    (n : ℕ) (z : X × ℝ) (u v : X × ℝ) (w : Fin n → X × ℝ) :
    iteratedFDeriv ℝ (n + 2) S z (Fin.cons u (Fin.cons v w)) =
      iteratedFDeriv ℝ (n + 2) S z (Fin.cons v (Fin.cons u w)) := by
  rw [iteratedFDeriv_succ_succ_apply hS n z (Fin.cons u (Fin.cons v w)),
      iteratedFDeriv_succ_succ_apply hS n z (Fin.cons v (Fin.cons u w))]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.cons_one]
  have hsym : IsSymmSndFDerivAt ℝ (iteratedFDeriv ℝ n S) z := by
    have hc : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S z := hS.contDiffAt
    have h2 : ContDiffAt ℝ 2 (iteratedFDeriv ℝ n S) z :=
      hc.iteratedFDeriv_right (i := n) (WithTop.coe_le_coe.mpr le_top)
    exact ContDiffAt.isSymmSndFDerivAt h2 (by simp)
  rw [IsSymmSndFDerivAt.eq hsym u v]


/-- The `j`-th jet of a smooth function on `X × ℝ` is smooth. -/
lemma contDiff_jet (S : X × ℝ → E) (hS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S) (j : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : X × ℝ => iteratedFDeriv ℝ j S z) := by
  exact hS.iteratedFDeriv_right (m := ∞) (show ∞ + (↑j : ℕ∞ω) ≤ ∞ from le_of_eq rfl)

/-- The Fréchet derivative of the slice `s ↦ 𝔡^j S (x, s)`. -/
lemma hasFDerivAt_slice (S : X × ℝ → E) (hS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S)
    (j : ℕ) (x : X) (s : ℝ) :
    HasFDerivAt (fun s' : ℝ => iteratedFDeriv ℝ j S (x, s'))
      ((fderiv ℝ (fun z : X × ℝ => iteratedFDeriv ℝ j S z) (x, s)).comp
        (ContinuousLinearMap.inr ℝ X ℝ)) s := by
  have h2 : HasFDerivAt (fun z : X × ℝ => iteratedFDeriv ℝ j S z)
      (fderiv ℝ (fun z : X × ℝ => iteratedFDeriv ℝ j S z) (x, s)) (x, s) :=
    ((contDiff_jet S hS j).differentiable (by simp)).differentiableAt.hasFDerivAt
  exact h2.comp s (hasFDerivAt_prodMk_right x s)

/-- The norm of the canonical inclusion `ℝ → X × ℝ`. -/
lemma norm_inr_le_one : ‖(ContinuousLinearMap.inr ℝ X ℝ)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun y => ?_)
  rw [ContinuousLinearMap.inr_apply, Prod.norm_def]
  simp

/-- The derivative of the slice is controlled by the next jet. -/
lemma norm_deriv_slice_le (S : X × ℝ → E) (j : ℕ) (x : X) (s : ℝ) :
    ‖(fderiv ℝ (fun z : X × ℝ => iteratedFDeriv ℝ j S z) (x, s)).comp
        (ContinuousLinearMap.inr ℝ X ℝ)‖ ≤ ‖iteratedFDeriv ℝ (j + 1) S (x, s)‖ := by
  calc ‖(fderiv ℝ (fun z : X × ℝ => iteratedFDeriv ℝ j S z) (x, s)).comp
        (ContinuousLinearMap.inr ℝ X ℝ)‖
      ≤ ‖fderiv ℝ (fun z : X × ℝ => iteratedFDeriv ℝ j S z) (x, s)‖ *
          ‖ContinuousLinearMap.inr ℝ X ℝ‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℝ (fun z : X × ℝ => iteratedFDeriv ℝ j S z) (x, s)‖ * 1 := by
        gcongr
        exact norm_inr_le_one
    _ = ‖iteratedFDeriv ℝ (j + 1) S (x, s)‖ := by
        rw [norm_fderiv_iteratedFDeriv, mul_one]

/-- Local boundedness of the `j`-th jet near `(x₀, 0)`. -/
lemma exists_local_jet_bound (S : X × ℝ → E) (hS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S)
    (j : ℕ) (x₀ : X) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ x : X, ‖x - x₀‖ < δ → ∀ t : ℝ, |t| < δ →
      ‖iteratedFDeriv ℝ j S (x, t)‖ ≤ C := by
  have hl : ((j : ℕ∞) : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  have hcont : Continuous (fun z : X × ℝ => ‖iteratedFDeriv ℝ j S z‖) :=
    (hS.continuous_iteratedFDeriv (m := j) hl).norm
  obtain ⟨δ, hδ, hb⟩ := (Metric.continuous_iff.1 hcont) (x₀, 0) 1 (by norm_num)
  refine ⟨‖iteratedFDeriv ℝ j S (x₀, 0)‖ + 1, δ, hδ, ?_⟩
  intro x hx t ht
  have hz : dist ((x, t) : X × ℝ) (x₀, 0) < δ := by
    rw [dist_eq_norm, Prod.norm_def]
    simp only [Prod.fst_sub, Prod.snd_sub, sub_zero]
    exact max_lt hx ht
  have h := hb (x, t) hz
  rw [Real.dist_eq] at h
  have h2 := (abs_lt.1 h).2
  linarith [norm_nonneg (iteratedFDeriv ℝ j S (x, t))]

/-- The `(n+1)`-th jet, with the first argument split off. -/
lemma iteratedFDeriv_cons_eq (S : X × ℝ → E) (hS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S)
    (n : ℕ) (z : X × ℝ) (a : X × ℝ) (w : Fin n → X × ℝ) :
    iteratedFDeriv ℝ (n + 1) S z (Fin.cons a w)
      = fderiv ℝ (fun z' : X × ℝ => iteratedFDeriv ℝ n S z' w) z a := by
  rw [iteratedFDeriv_succ_apply_left, Fin.tail_cons]
  have hd : DifferentiableAt ℝ (fun z' : X × ℝ => iteratedFDeriv ℝ n S z') z :=
    ((contDiff_jet S hS n).differentiable (by simp)).differentiableAt
  exact (fderiv_continuousMultilinear_apply_const_apply hd w a).symm

/-- Splitting the first argument of the `(n+1)`-th jet off additively. -/
lemma jet_cons_add (S : X × ℝ → E) (hS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S)
    (n : ℕ) (z : X × ℝ) (a b : X × ℝ) (w : Fin n → X × ℝ) :
    iteratedFDeriv ℝ (n + 1) S z (Fin.cons (a + b) w)
      = iteratedFDeriv ℝ (n + 1) S z (Fin.cons a w)
        + iteratedFDeriv ℝ (n + 1) S z (Fin.cons b w) := by
  rw [iteratedFDeriv_cons_eq S hS n z (a + b) w, iteratedFDeriv_cons_eq S hS n z a w,
    iteratedFDeriv_cons_eq S hS n z b w]
  exact map_add _ _ _

/-- Splitting the first argument of the `(n+1)`-th jet off under scalar multiplication. -/
lemma jet_cons_smul (S : X × ℝ → E) (hS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S)
    (n : ℕ) (z : X × ℝ) (c : ℝ) (a : X × ℝ) (w : Fin n → X × ℝ) :
    iteratedFDeriv ℝ (n + 1) S z (Fin.cons (c • a) w)
      = c • iteratedFDeriv ℝ (n + 1) S z (Fin.cons a w) := by
  rw [iteratedFDeriv_cons_eq S hS n z (c • a) w, iteratedFDeriv_cons_eq S hS n z a w]
  exact map_smul _ _ _

/-- Moving a `t`-direction argument from the first to the last slot of a jet: the `(n+1)`-th jet
with `e` in front is the `n`-th jet of the `t`-derivative function. -/
lemma iteratedFDeriv_cons_e_eq (S : X × ℝ → E) (hS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S)
    (n : ℕ) (w : Fin n → X × ℝ) (z : X × ℝ) :
    iteratedFDeriv ℝ (n + 1) S z (Fin.cons ((0 : X), (1 : ℝ)) w)
      = iteratedFDeriv ℝ n (fun z' : X × ℝ => fderiv ℝ S z' ((0 : X), (1 : ℝ))) z w := by
  have hSe : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z' : X × ℝ => fderiv ℝ S z' ((0 : X), (1 : ℝ))) :=
    (hS.fderiv_right (m := ∞)
      (show ∞ + ((1 : ℕ∞) : ℕ∞ω) ≤ ∞ from le_of_eq rfl)).clm_apply contDiff_const
  induction n generalizing z with
  | zero =>
    rw [iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply]
    simp
  | succ n ih =>
    rw [← Fin.cons_self_tail w]
    rw [iteratedFDeriv_swap_first_two_local (S := S) hS n z ((0 : X), (1 : ℝ)) (w 0) (Fin.tail w)]
    rw [iteratedFDeriv_cons_eq S hS (n + 1) z (w 0)
      (Fin.cons ((0 : X), (1 : ℝ)) (Fin.tail w))]
    rw [show (fun z' : X × ℝ => iteratedFDeriv ℝ (n + 1) S z' (Fin.cons ((0 : X), (1 : ℝ)) (Fin.tail w)))
        = (fun z' : X × ℝ =>
            iteratedFDeriv ℝ n (fun z'' : X × ℝ => fderiv ℝ S z'' ((0 : X), (1 : ℝ))) z' (Fin.tail w))
        from funext (fun z' => ih (Fin.tail w) z')]
    rw [← iteratedFDeriv_cons_eq (fun z' : X × ℝ => fderiv ℝ S z' ((0 : X), (1 : ℝ))) hSe n z (w 0)
      (Fin.tail w)]

/-- **Flatness forces the jets to vanish on the hyperplane.** -/
lemma jets_flat_vanish_aux : ∀ (N : ℕ) {S : X × ℝ → E},
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S →
    (∀ i < N, ∀ x : X,
      iteratedFDeriv ℝ i S (x, 0) (fun _ : Fin i => ((0 : X), (1 : ℝ))) = 0) →
    ∀ r < N, ∀ x : X, iteratedFDeriv ℝ r S (x, 0) = 0 := by
  intro N
  induction N with
  | zero =>
    intro S hS hflat r hr
    exact absurd hr (Nat.not_lt_zero r)
  | succ N ih =>
    intro S hS hflat r hr x
    have hSe : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z' : X × ℝ => fderiv ℝ S z' ((0 : X), (1 : ℝ))) :=
      (hS.fderiv_right (m := ∞)
        (show ∞ + ((1 : ℕ∞) : ℕ∞ω) ≤ ∞ from le_of_eq rfl)).clm_apply contDiff_const
    have hSe_flat : ∀ i < N, ∀ x : X,
        iteratedFDeriv ℝ i (fun z' : X × ℝ => fderiv ℝ S z' ((0 : X), (1 : ℝ))) (x, 0)
          (fun _ : Fin i => ((0 : X), (1 : ℝ))) = 0 := by
      intro i hi x
      rw [← iteratedFDeriv_cons_e_eq S hS i (fun _ : Fin i => ((0 : X), (1 : ℝ))) (x, 0)]
      rw [show (Fin.cons ((0 : X), (1 : ℝ)) (fun _ : Fin i => ((0 : X), (1 : ℝ))))
          = (fun _ : Fin (i + 1) => ((0 : X), (1 : ℝ))) from by
        funext j
        refine Fin.cases ?_ ?_ j <;> simp]
      exact hflat (i + 1) (by omega) x
    have hIHS : ∀ s < N, ∀ x : X,
        iteratedFDeriv ℝ s (fun z' : X × ℝ => fderiv ℝ S z' ((0 : X), (1 : ℝ))) (x, 0) = 0 :=
      fun s hs x => ih hSe hSe_flat s hs x
    have key : ∀ s ≤ N, ∀ x : X, iteratedFDeriv ℝ s S (x, 0) = 0 := by
      intro s
      induction s using Nat.strong_induction_on with
      | _ s ihs =>
        intro hsN x
        rcases s with _ | k
        · ext m
          rw [iteratedFDeriv_zero_apply, zero_apply]
          simpa [iteratedFDeriv_zero_apply] using hflat 0 (Nat.succ_pos N) x
        · ext m
          have hm : m = Fin.cons (m 0) (Fin.tail m) := (Fin.cons_self_tail m).symm
          have hdec : (m 0 : X × ℝ) = (((m 0).1, (0 : ℝ)) : X × ℝ) + (m 0).2 • ((0 : X), (1 : ℝ)) := by
            ext <;> simp
          have hsplit : iteratedFDeriv ℝ (k + 1) S (x, 0) m
              = iteratedFDeriv ℝ (k + 1) S (x, 0) (Fin.cons (((m 0).1, (0 : ℝ)) : X × ℝ) (Fin.tail m))
                + (m 0).2 • iteratedFDeriv ℝ (k + 1) S (x, 0)
                    (Fin.cons ((0 : X), (1 : ℝ)) (Fin.tail m)) := by
            conv_lhs => rw [hm, hdec]
            rw [jet_cons_add S hS k (x, 0), jet_cons_smul S hS k (x, 0)]
          rw [hsplit]
          have h2 : iteratedFDeriv ℝ (k + 1) S (x, 0) (Fin.cons ((0 : X), (1 : ℝ)) (Fin.tail m))
              = iteratedFDeriv ℝ k (fun z' : X × ℝ => fderiv ℝ S z' ((0 : X), (1 : ℝ))) (x, 0)
                  (Fin.tail m) :=
            iteratedFDeriv_cons_e_eq S hS k (Fin.tail m) (x, 0)
          rw [h2]
          have h3 : iteratedFDeriv ℝ k (fun z' : X × ℝ => fderiv ℝ S z' ((0 : X), (1 : ℝ))) (x, 0)
              = 0 := hIHS k (by omega) x
          rw [h3, zero_apply, smul_zero, add_zero]
          -- tangential part
          rw [iteratedFDeriv_cons_eq S hS k (x, 0) (((m 0).1, (0 : ℝ)) : X × ℝ) (Fin.tail m)]
          set G : X × ℝ → E := fun z' => iteratedFDeriv ℝ k S z' (Fin.tail m) with hG
          have hGdiff : DifferentiableAt ℝ G (x, 0) := by
            rw [hG]
            exact DifferentiableAt.continuousMultilinear_apply_const
              ((contDiff_jet S hS k).differentiable (by simp)).differentiableAt (Fin.tail m)
          have hGzero : (fun y' : X => G (y', 0)) = fun _ : X => (0 : E) := by
            funext y'
            have hk : iteratedFDeriv ℝ k S (y', 0) = 0 := ihs k (by omega) (by omega) y'
            show iteratedFDeriv ℝ k S (y', 0) (Fin.tail m) = 0
            rw [hk]
            simp
          have hchain : HasFDerivAt (fun y' : X => G (y', 0))
              ((fderiv ℝ G (x, 0)).comp (ContinuousLinearMap.inl ℝ X ℝ)) x :=
            HasFDerivAt.comp (x := x) (g := G) (f := fun e : X => (e, (0 : ℝ)))
              hGdiff.hasFDerivAt (hasFDerivAt_prodMk_left (𝕜 := ℝ) x (0 : ℝ))
          have hf : fderiv ℝ (fun y' : X => G (y', 0)) x
              = (fderiv ℝ G (x, 0)).comp (ContinuousLinearMap.inl ℝ X ℝ) := hchain.fderiv
          have hzero : fderiv ℝ (fun y' : X => G (y', 0)) x ((m 0).1) = 0 := by
            rw [hGzero]
            simp
          rw [hf] at hzero
          simpa using hzero
    exact key r (by omega) x

/-- **Flatness forces the jets to vanish on the hyperplane.**
Placeholder wrapper; see `jets_flat_vanish_aux`. -/
lemma jets_flat_vanish_local {S : X × ℝ → E} {N r : ℕ}
    (hS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S)
    (hflat : ∀ i < N, ∀ x : X,
      iteratedFDeriv ℝ i S (x, 0) (fun _ : Fin i => ((0 : X), (1 : ℝ))) = 0)
    (hr : r < N) (x : X) :
    iteratedFDeriv ℝ r S (x, 0) = 0 :=
  jets_flat_vanish_aux N hS hflat r hr x

theorem flat_bounds_of_jets {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {S : X × ℝ → E} {K : ℕ}
    (hS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S)
    (hflat : ∀ i < K, ∀ x : X,
      iteratedFDeriv ℝ i S (x, 0) (fun _ : Fin i => ((0 : X), (1 : ℝ))) = 0) :
    ∀ x₀ : X, ∃ C δ : ℝ, 0 < δ ∧ ∀ x : X, ‖x - x₀‖ < δ → ∀ t : ℝ, 0 < t → t < δ →
      ∀ j : ℕ, j ≤ K → ‖iteratedFDeriv ℝ j S (x, t)‖ ≤ C * t ^ (K - j) := by
  intro x₀
  have hFL : ∀ r < K, ∀ y : X, iteratedFDeriv ℝ r S (y, 0) = 0 :=
    fun r hr y => jets_flat_vanish_local hS hflat hr y
  obtain ⟨C, δ, hδ, hloc⟩ := exists_local_jet_bound S hS K x₀
  have hC0 : 0 ≤ C := by
    have h1 : ‖iteratedFDeriv ℝ K S (x₀, 0)‖ ≤ C := hloc x₀ (by simp [hδ]) 0 (by simp [hδ])
    exact le_trans (norm_nonneg _) h1
  refine ⟨C, δ, hδ, ?_⟩
  intro x hx t ht0 htd
  have step : ∀ (k : ℕ) (hk : k < K),
      (∀ s : ℝ, 0 < s → s < δ → ‖iteratedFDeriv ℝ (k + 1) S (x, s)‖ ≤ C * s ^ (K - (k + 1))) →
      (∀ s : ℝ, 0 < s → s < δ → ‖iteratedFDeriv ℝ k S (x, s)‖ ≤ C * s ^ (K - k)) := by
    intro k hk ih s hs0 hsd
    have hderiv : ∀ r ∈ Icc (0 : ℝ) s,
        HasDerivWithinAt (fun r' : ℝ => iteratedFDeriv ℝ k S (x, r'))
          (((fderiv ℝ (fun z : X × ℝ => iteratedFDeriv ℝ k S z) (x, r)).comp
            (ContinuousLinearMap.inr ℝ X ℝ)) 1) (Icc 0 s) r := by
      intro r _
      exact ((hasFDerivAt_slice S hS k x r).hasDerivAt).hasDerivWithinAt
    have hbound : ∀ r ∈ Ico (0 : ℝ) s,
        ‖(((fderiv ℝ (fun z : X × ℝ => iteratedFDeriv ℝ k S z) (x, r)).comp
            (ContinuousLinearMap.inr ℝ X ℝ)) 1)‖ ≤ C * s ^ (K - (k + 1)) := by
      intro r hr
      have hr0 : 0 ≤ r := hr.1
      have hrs : r < s := hr.2
      have h1 : ‖((fderiv ℝ (fun z : X × ℝ => iteratedFDeriv ℝ k S z) (x, r)).comp
            (ContinuousLinearMap.inr ℝ X ℝ)) 1‖ ≤ ‖iteratedFDeriv ℝ (k + 1) S (x, r)‖ := by
        refine le_trans ?_ (norm_deriv_slice_le S k x r)
        simpa using ContinuousLinearMap.le_opNorm
          ((fderiv ℝ (fun z : X × ℝ => iteratedFDeriv ℝ k S z) (x, r)).comp
            (ContinuousLinearMap.inr ℝ X ℝ)) (1 : ℝ)
      rcases eq_or_lt_of_le hr0 with h0 | hpos
      · have h2 : ‖iteratedFDeriv ℝ (k + 1) S (x, r)‖ ≤ C * s ^ (K - (k + 1)) := by
          rw [show r = 0 from h0.symm]
          by_cases hk1 : k + 1 = K
          · have h4 : ‖iteratedFDeriv ℝ K S (x, 0)‖ ≤ C := hloc x hx 0 (by simpa using hδ)
            rw [hk1]
            simpa using h4
          · have h4 : iteratedFDeriv ℝ (k + 1) S (x, 0) = 0 := hFL (k + 1) (by omega) x
            rw [h4, norm_zero]
            exact mul_nonneg hC0 (pow_nonneg hs0.le _)
        exact le_trans h1 h2
      · have h3 := ih r hpos (lt_trans hrs hsd)
        refine le_trans h1 (le_trans h3 ?_)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hpos.le hrs.le _) hC0
    have hf0 : (fun r' : ℝ => iteratedFDeriv ℝ k S (x, r')) 0 = 0 := hFL k hk x
    have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound s
      (right_mem_Icc.mpr hs0.le)
    have hmvt' : ‖iteratedFDeriv ℝ k S (x, s)‖ ≤ (C * s ^ (K - (k + 1))) * (s - 0) := by
      have h := hmvt
      simp only [hf0, sub_zero] at h
      simpa using h
    have hpow : (C * s ^ (K - (k + 1))) * (s - 0) = C * s ^ (K - k) := by
      rw [sub_zero, mul_assoc]
      congr 1
      rw [← pow_succ]
      congr 1
      omega
    linarith [hmvt', hpow.le, hpow.ge]
  have base : ∀ s : ℝ, 0 < s → s < δ → ‖iteratedFDeriv ℝ K S (x, s)‖ ≤ C * s ^ (K - K) := by
    intro s hs0 hsd
    have h1 : ‖iteratedFDeriv ℝ K S (x, s)‖ ≤ C :=
      hloc x hx s (by rw [abs_of_pos hs0]; exact hsd)
    simpa using h1
  have key : ∀ j ≤ K, ∀ s : ℝ, 0 < s → s < δ →
      ‖iteratedFDeriv ℝ j S (x, s)‖ ≤ C * s ^ (K - j) := by
    intro j hjK
    exact Nat.decreasingInduction (n := K)
      (motive := fun j _ => ∀ s : ℝ, 0 < s → s < δ →
        ‖iteratedFDeriv ℝ j S (x, s)‖ ≤ C * s ^ (K - j)) step base hjK
  intro j hj
  exact key j hj t ht0 htd

end Work.Drive
