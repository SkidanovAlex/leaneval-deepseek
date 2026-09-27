import Mathlib

/-!
# Bounds on the jets of a function flat along a hyperplane

Let `S : X × ℝ → E` be smooth and flat to order `K` along the hyperplane `t = 0`, i.e. all the
derivatives in `t` of the slices `t ↦ S (x, t)` of order `< K` vanish at `0` for every `x`.  Then
near any point `(x₀, 0)` the `j`-th Fréchet derivative of `S` is bounded by `C * t ^ (K - j)`.

The proof has three ingredients.

* Mixed partials: peeling one entry off a jet of a smooth function is a derivative operation
  (`fderiv_jet_apply`), so the jet of a directional derivative is the jet of the function with the
  direction prepended (`iteratedFDeriv_dir_apply`); the first two entries can be exchanged by
  symmetry of the second derivative.  This makes the `x`-directional derivative of a function which
  is flat to order `d` again flat to order `d`.
* Consequently the `n`-th jet at a point of the hyperplane vanishes on every tuple whose entries
  are either tangent `(w, 0)` or transversal `(0, s)`, provided the number of transversal entries is
  `< d` (`iteratedFDeriv_eq_zero_of_flat`).
* Multilinearity upgrades this to the vanishing of the whole jet at the hyperplane
  (`iteratedFDeriv_at_zero_eq_zero`), and a mean value estimate on the slices gives the bounds
  (`flat_descent`).
-/

namespace Work.Drive

open Set Filter Topology
open scoped ContDiff

/-- Number of entries of a tuple in `X × ℝ` whose second coordinate is nonzero. -/
private noncomputable def jetCount (X : Type*) : (n : ℕ) → (Fin n → X × ℝ) → ℕ
  | 0, _ => 0
  | n + 1, τ => jetCount X n (Fin.tail τ) + if (τ 0).2 = 0 then 0 else 1

private lemma jetCount_zero (X : Type*) (τ : Fin 0 → X × ℝ) : jetCount X 0 τ = 0 := rfl

private lemma jetCount_succ (X : Type*) {n : ℕ} (τ : Fin (n + 1) → X × ℝ) :
    jetCount X (n + 1) τ =
      jetCount X n (Fin.tail τ) + (if (τ 0).2 = 0 then 0 else 1) := rfl

private lemma jetCount_le (X : Type*) {n : ℕ} (τ : Fin n → X × ℝ) : jetCount X n τ ≤ n := by
  induction n with
  | zero => simp [jetCount]
  | succ n ih =>
    rw [jetCount_succ]
    have h := ih (Fin.tail τ)
    split <;> omega

section

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative in the second coordinate of a function on `X × ℝ` is the derivative of its
slice. -/
private lemma fderiv_snd_eq_deriv {G : X × ℝ → E} (hG : ContDiff ℝ ∞ G) (x : X) (t : ℝ) :
    fderiv ℝ G (x, t) ((0 : X), (1 : ℝ)) = deriv (fun s : ℝ => G (x, s)) t := by
  have h1 : HasFDerivAt (fun s : ℝ => (x, s)) (ContinuousLinearMap.inr ℝ X ℝ) t :=
    hasFDerivAt_prodMk_right x t
  have h2 : HasFDerivAt G (fderiv ℝ G (x, t)) (x, t) :=
    ((hG.differentiable (by simp)) (x, t)).hasFDerivAt
  have h3 := h2.comp t h1
  have h4 : HasDerivAt (fun s : ℝ => G (x, s)) ((fderiv ℝ G (x, t)) ((0 : X), (1 : ℝ))) t := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      Function.comp_def] using h3.hasDerivAt
  exact h4.deriv.symm

/-- The `c`-th derivative of the transversal derivative of a function is the `(c+1)`-st derivative
of its slices. -/
private lemma iteratedDeriv_fderiv_snd {G : X × ℝ → E} (hG : ContDiff ℝ ∞ G) (x : X) (c : ℕ) :
    iteratedDeriv c (fun t : ℝ => fderiv ℝ G (x, t) ((0 : X), (1 : ℝ))) 0
      = iteratedDeriv (c + 1) (fun s : ℝ => G (x, s)) 0 := by
  have hfun : (fun t : ℝ => fderiv ℝ G (x, t) ((0 : X), (1 : ℝ)))
      = deriv (fun s : ℝ => G (x, s)) := by
    funext t
    exact fderiv_snd_eq_deriv hG x t
  rw [hfun, ← iteratedDeriv_succ']

/-- The transversal derivative of a function flat to order `d` is flat to order `d - 1`. -/
private lemma iteratedDeriv_fderiv_snd_eq_zero {G : X × ℝ → E} (hG : ContDiff ℝ ∞ G) {d : ℕ}
    (hflat : ∀ c < d, ∀ x : X, iteratedDeriv c (fun t : ℝ => G (x, t)) 0 = 0) :
    ∀ c < d - 1, ∀ x : X,
      iteratedDeriv c (fun t : ℝ => fderiv ℝ G (x, t) ((0 : X), (1 : ℝ))) 0 = 0 := by
  intro c hc x
  rw [iteratedDeriv_fderiv_snd hG x c]
  exact hflat (c + 1) (by omega) x

/-- Peeling the first entry off a jet of a smooth function: the derivative of the slice of a jet is
the jet with one more (prepended) entry. -/
private lemma fderiv_jet_apply {G : X × ℝ → E} (hG : ContDiff ℝ ∞ G) (m : ℕ)
    (τ : Fin m → X × ℝ) (y : X × ℝ) (v : X × ℝ) :
    fderiv ℝ (fun z : X × ℝ => iteratedFDeriv ℝ m G z τ) y v =
      iteratedFDeriv ℝ (m + 1) G y (Fin.cons v τ) := by
  have hd : DifferentiableAt ℝ (fun z : X × ℝ => iteratedFDeriv ℝ m G z) y :=
    ((hG.iteratedFDeriv_right' (m := ∞) (i := m)).differentiable (by simp)) y
  rw [fderiv_continuousMultilinear_apply_const
    (c := fun z : X × ℝ => iteratedFDeriv ℝ m G z) hd τ]
  rw [ContinuousLinearMap.flipMultilinear_apply_apply]
  rw [iteratedFDeriv_succ_apply_left (m := Fin.cons v τ)]
  simp only [Fin.cons_zero, Fin.tail_cons]

/-- The directional derivative of a smooth function along a fixed vector is smooth. -/
private lemma contDiff_dir {G : X × ℝ → E} (hG : ContDiff ℝ ∞ G) (v : X × ℝ) :
    ContDiff ℝ ∞ (fun z : X × ℝ => fderiv ℝ G z v) :=
  (hG.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- The `(n+2)`-nd iterated derivative of a smooth function, evaluated on a tuple, is the second
derivative of the `n`-th iterated derivative evaluated on the first two entries and then the
remaining ones.  (Auxiliary computation for `swap_first_two_jet`.) -/
private lemma iteratedFDeriv_succ_succ_apply {G : X × ℝ → E} (hG : ContDiff ℝ ∞ G)
    (n : ℕ) (z : X × ℝ) (M : Fin (n + 2) → X × ℝ) :
    iteratedFDeriv ℝ (n + 2) G z M =
      (fderiv ℝ (fderiv ℝ (iteratedFDeriv ℝ n G)) z (M 0) (M 1))
        (fun i => M i.succ.succ) := by
  have hg : ContDiff ℝ ∞ (iteratedFDeriv ℝ n G) :=
    hG.iteratedFDeriv_right' (m := ∞) (i := n)
  have hg1 : ContDiff ℝ ∞ (iteratedFDeriv ℝ (n + 1) G) :=
    hG.iteratedFDeriv_right' (m := ∞) (i := n + 1)
  have hg_diff : ∀ y, DifferentiableAt ℝ (iteratedFDeriv ℝ n G) y :=
    fun y => (hg.differentiable (by simp)) y
  have hg1_diff : DifferentiableAt ℝ (iteratedFDeriv ℝ (n + 1) G) z :=
    (hg1.differentiable (by simp)) z
  have hdg : DifferentiableAt ℝ (fderiv ℝ (iteratedFDeriv ℝ n G)) z := by
    have h2 : ContDiff ℝ 1 (fderiv ℝ (iteratedFDeriv ℝ n G)) :=
      hg.fderiv_right (m := 1) (by decide)
    exact h2.contDiffAt.differentiableAt (by simp)
  have hdP : DifferentiableAt ℝ
      (fun y => (fderiv ℝ (iteratedFDeriv ℝ n G) y) (Fin.tail M 0)) z :=
    hdg.clm_apply (differentiableAt_const _)
  rw [DifferentiableAt.iteratedFDeriv_succ_apply_left' (m := M) hg1_diff]
  have hfun : (fun y => (iteratedFDeriv ℝ (n + 1) G y) (Fin.tail M))
      = fun y => fderiv ℝ
          (fun y' => (iteratedFDeriv ℝ n G y') (Fin.tail (Fin.tail M))) y ((Fin.tail M) 0) := by
    funext y
    exact DifferentiableAt.iteratedFDeriv_succ_apply_left' (m := Fin.tail M) (hg_diff y)
  rw [hfun]
  have hC : (fderiv ℝ (fun y => (fderiv ℝ
        (fun y' => (iteratedFDeriv ℝ n G y') (Fin.tail (Fin.tail M))) y) (Fin.tail M 0)) z) (M 0)
      = (((fderiv ℝ (fderiv ℝ (iteratedFDeriv ℝ n G)) z) (M 0)) (Fin.tail M 0))
          (Fin.tail (Fin.tail M)) := by
    have hfun2 : (fun y => (fderiv ℝ
          (fun y' => (iteratedFDeriv ℝ n G y') (Fin.tail (Fin.tail M))) y) (Fin.tail M 0))
        = (fun y => (fderiv ℝ (iteratedFDeriv ℝ n G) y) (Fin.tail M 0)
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

/-- For a smooth function the first two entries of a jet can be exchanged (symmetry of the second
derivative). -/
private lemma swap_first_two_jet {G : X × ℝ → E} (hG : ContDiff ℝ ∞ G)
    (n : ℕ) (z : X × ℝ) (u v : X × ℝ) (w : Fin n → X × ℝ) :
    iteratedFDeriv ℝ (n + 2) G z (Fin.cons u (Fin.cons v w)) =
      iteratedFDeriv ℝ (n + 2) G z (Fin.cons v (Fin.cons u w)) := by
  rw [iteratedFDeriv_succ_succ_apply hG n z (Fin.cons u (Fin.cons v w)),
      iteratedFDeriv_succ_succ_apply hG n z (Fin.cons v (Fin.cons u w))]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.cons_one]
  have hsym : IsSymmSndFDerivAt ℝ (iteratedFDeriv ℝ n G) z := by
    have hc : ContDiffAt ℝ ∞ G z := hG.contDiffAt
    have h2 : ContDiffAt ℝ 2 (iteratedFDeriv ℝ n G) z :=
      hc.iteratedFDeriv_right (i := n) (WithTop.coe_le_coe.mpr le_top)
    exact ContDiffAt.isSymmSndFDerivAt h2 (by simp)
  rw [IsSymmSndFDerivAt.eq hsym u v]

/-- The jet of the directional derivative of a smooth function along a direction `v` is the jet of
the function with `v` prepended. -/
private lemma iteratedFDeriv_dir_apply {G : X × ℝ → E} (hG : ContDiff ℝ ∞ G) :
    ∀ (m : ℕ) (σ : Fin m → X × ℝ) (v : X × ℝ) (y : X × ℝ),
      iteratedFDeriv ℝ m (fun z : X × ℝ => fderiv ℝ G z v) y σ =
        iteratedFDeriv ℝ (m + 1) G y (Fin.cons v σ) := by
  intro m
  induction m with
  | zero =>
    intro σ v y
    rw [iteratedFDeriv_zero_apply]
    show fderiv ℝ G y v = iteratedFDeriv ℝ 1 G y (Fin.cons v σ)
    rw [iteratedFDeriv_one_apply]
    simp
  | succ m ih =>
    intro σ v y
    rw [← Fin.cons_self_tail σ]
    rw [← fderiv_jet_apply (G := fun z : X × ℝ => fderiv ℝ G z v) (contDiff_dir hG v)
      m (Fin.tail σ) y (σ 0)]
    have hfun : (fun z : X × ℝ => iteratedFDeriv ℝ m (fun z : X × ℝ => fderiv ℝ G z v) z (Fin.tail σ))
        = fun z : X × ℝ => iteratedFDeriv ℝ (m + 1) G z (Fin.cons v (Fin.tail σ)) := by
      funext z
      exact ih (Fin.tail σ) v z
    rw [hfun]
    rw [fderiv_jet_apply hG (m + 1) (Fin.cons v (Fin.tail σ)) y (σ 0)]
    exact swap_first_two_jet hG m y (σ 0) v (Fin.tail σ)

/-- If a function vanishes on the hyperplane `t = 0`, then its derivative at a point of the
hyperplane in a tangent direction vanishes. -/
private lemma fderiv_inl_eq_zero (Φ : X × ℝ → E) (y : X) (w : X)
    (hd : DifferentiableAt ℝ Φ (y, 0)) (hΦ : ∀ y' : X, Φ (y', 0) = 0) :
    fderiv ℝ Φ (y, 0) ((w, 0)) = 0 := by
  have h1 : HasFDerivAt (fun y' : X => ((y', 0) : X × ℝ)) (ContinuousLinearMap.inl ℝ X ℝ) y :=
    hasFDerivAt_prodMk_left y 0
  have h2 : HasFDerivAt Φ (fderiv ℝ Φ (y, 0)) (y, 0) := hd.hasFDerivAt
  have h3 : fderiv ℝ (fun y' : X => Φ (y', 0)) y =
      (fderiv ℝ Φ (y, 0)).comp (ContinuousLinearMap.inl ℝ X ℝ) := (h2.comp y h1).fderiv
  have h4 : (fun y' : X => Φ (y', 0)) = fun _ : X => (0 : E) := funext hΦ
  have h5 : fderiv ℝ (fun _ : X => (0 : E)) y = 0 := by simp
  rw [h4, h5] at h3
  have h6 : ((fderiv ℝ Φ (y, 0)).comp (ContinuousLinearMap.inl ℝ X ℝ)) w = 0 := by
    have h7 := congrArg (fun L : X →L[ℝ] E => L w) h3.symm
    simpa using h7
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply] using h6

/-- Multilinearity of a jet in its first slot: the scalar of the transversal unit vector can be
pulled out. -/
private lemma jet_smul_cons {G : X × ℝ → E} (m : ℕ) (y : X) (s : ℝ) (σ : Fin m → X × ℝ) :
    iteratedFDeriv ℝ (m + 1) G (y, 0) (Fin.cons ((0 : X), s) σ)
      = s • iteratedFDeriv ℝ (m + 1) G (y, 0) (Fin.cons ((0 : X), (1 : ℝ)) σ) := by
  have h := ContinuousMultilinearMap.map_update_smul
    (f := iteratedFDeriv ℝ (m + 1) G (y, 0))
    (m := Fin.cons ((0 : X), (1 : ℝ)) σ) (i := 0) (c := s) (x := ((0 : X), (1 : ℝ)))
  rw [Fin.update_cons_zero, Fin.update_cons_zero] at h
  rw [show s • (((0 : X), (1 : ℝ)) : X × ℝ) = ((0 : X), s) from by simp] at h
  exact h

/-- **Main vanishing statement.**  A smooth function which is flat to order `d` along the
hyperplane `t = 0` has vanishing jet at any point of the hyperplane on every tuple whose entries
are either tangent or transversal, provided the number of transversal entries is `< d`. -/
private theorem iteratedFDeriv_eq_zero_of_flat (n : ℕ) :
    ∀ {d : ℕ} {G : X × ℝ → E}, ContDiff ℝ ∞ G →
      (∀ c < d, ∀ x : X, iteratedDeriv c (fun t : ℝ => G (x, t)) 0 = 0) →
      ∀ (τ : Fin n → X × ℝ), (∀ i, (τ i).1 = 0 ∨ (τ i).2 = 0) →
        jetCount X n τ < d → ∀ y : X, iteratedFDeriv ℝ n G (y, 0) τ = 0 := by
  induction n with
  | zero =>
    intro d G hG hflat τ hgood hb y
    rw [iteratedFDeriv_zero_apply]
    have hd : 0 < d := by
      have h0 : jetCount X 0 τ = 0 := jetCount_zero X τ
      omega
    have h := hflat 0 hd y
    simpa using h
  | succ n ih =>
    intro d G hG hflat τ hgood hb y
    rw [← Fin.cons_self_tail τ]
    have hcount := jetCount_succ X τ
    by_cases hv2 : (τ 0).2 = 0
    · rw [if_pos hv2] at hcount
      have hb' : jetCount X n (Fin.tail τ) < d := by omega
      rw [← fderiv_jet_apply hG n (Fin.tail τ) (y, 0) (τ 0)]
      have hv : τ 0 = (((τ 0).1, (0 : ℝ)) : X × ℝ) := by
        rw [← hv2, Prod.mk.eta]
      rw [hv]
      have hd : DifferentiableAt ℝ (fun z : X × ℝ => iteratedFDeriv ℝ n G z (Fin.tail τ)) (y, 0) :=
        (((hG.iteratedFDeriv_right' (m := ∞) (i := n)).differentiable (by simp)) (y, 0)).continuousMultilinear_apply_const
          (Fin.tail τ)
      refine fderiv_inl_eq_zero (fun z : X × ℝ => iteratedFDeriv ℝ n G z (Fin.tail τ)) y (τ 0).1 hd ?_
      intro y'
      exact ih hG hflat (Fin.tail τ) (fun i => hgood i.succ) hb' y'
    · rw [if_neg hv2] at hcount
      have hb' : jetCount X n (Fin.tail τ) < d - 1 := by omega
      have hs : (τ 0).1 = 0 := (hgood 0).resolve_right hv2
      have hv : τ 0 = (((0 : X), (τ 0).2) : X × ℝ) := by
        rw [← hs, Prod.mk.eta]
      rw [hv, jet_smul_cons]
      rw [← iteratedFDeriv_dir_apply hG n (Fin.tail τ) ((0 : X), (1 : ℝ)) (y, 0)]
      rw [ih (G := fun z : X × ℝ => fderiv ℝ G z ((0 : X), (1 : ℝ))) (contDiff_dir hG _)
        (iteratedDeriv_fderiv_snd_eq_zero hG hflat)
        (Fin.tail τ) (fun i => hgood i.succ) hb' y]
      simp

/-- **The jet at a point of the hyperplane vanishes.**  If a smooth function is flat to order `d`
along `t = 0` then its `n`-th jet vanishes at every point of the hyperplane, for `n < d`. -/
private theorem iteratedFDeriv_at_zero_eq_zero {G : X × ℝ → E} (hG : ContDiff ℝ ∞ G) {d : ℕ}
    (hflat : ∀ c < d, ∀ x : X, iteratedDeriv c (fun t : ℝ => G (x, t)) 0 = 0) {n : ℕ}
    (hn : n < d) (x : X) :
    iteratedFDeriv ℝ n G (x, 0) = 0 := by
  ext τ
  have hdecomp : τ = (fun i : Fin n => (((τ i).1, (0 : ℝ)) : X × ℝ))
      + (fun i : Fin n => (((0 : X), (τ i).2) : X × ℝ)) := by
    funext i
    simp
  rw [hdecomp, ContinuousMultilinearMap.map_add_univ]
  refine Finset.sum_eq_zero (fun s _ => ?_)
  refine iteratedFDeriv_eq_zero_of_flat n hG hflat _ (fun i => ?_) ?_ x
  · by_cases h : i ∈ s <;> simp [h]
  · have h1 : jetCount X n
        (s.piecewise (fun i : Fin n => (((τ i).1, (0 : ℝ)) : X × ℝ))
          (fun i : Fin n => (((0 : X), (τ i).2) : X × ℝ))) ≤ n := jetCount_le X _
    omega

/-- The canonical inclusion `ℝ → X × ℝ` has operator norm at most one. -/
private lemma norm_inr_le_one : ‖(ContinuousLinearMap.inr ℝ X ℝ : ℝ →L[ℝ] X × ℝ)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun y => ?_)
  rw [ContinuousLinearMap.inr_apply, Prod.norm_def]
  simp

/-- The derivative of the slice of a jet is controlled by the next jet. -/
private lemma norm_fderiv_jet_le {S : X × ℝ → E} (k : ℕ) (x : X) (r : ℝ) :
    ‖(fderiv ℝ (fun z : X × ℝ => iteratedFDeriv ℝ k S z) (x, r)).comp
        (ContinuousLinearMap.inr ℝ X ℝ)‖ ≤ ‖iteratedFDeriv ℝ (k + 1) S (x, r)‖ := by
  calc ‖(fderiv ℝ (fun z : X × ℝ => iteratedFDeriv ℝ k S z) (x, r)).comp
        (ContinuousLinearMap.inr ℝ X ℝ)‖
      ≤ ‖fderiv ℝ (fun z : X × ℝ => iteratedFDeriv ℝ k S z) (x, r)‖ *
          ‖(ContinuousLinearMap.inr ℝ X ℝ : ℝ →L[ℝ] X × ℝ)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℝ (fun z : X × ℝ => iteratedFDeriv ℝ k S z) (x, r)‖ * 1 :=
        mul_le_mul_of_nonneg_left norm_inr_le_one
          (norm_nonneg (fderiv ℝ (fun z : X × ℝ => iteratedFDeriv ℝ k S z) (x, r)))
    _ = ‖fderiv ℝ (fun z : X × ℝ => iteratedFDeriv ℝ k S z) (x, r)‖ := mul_one _
    _ = ‖iteratedFDeriv ℝ (k + 1) S (x, r)‖ := norm_fderiv_iteratedFDeriv

/-- **Descending mean value estimate.**  A local bound for the `K`-th jet together with the
vanishing of the lower jets at the hyperplane implies the polynomial bounds. -/
private lemma flat_descent {S : X × ℝ → E} {K : ℕ} {x₀ : X} {C δ : ℝ}
    (hS : ContDiff ℝ ∞ S) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hloc : ∀ x : X, ‖x - x₀‖ < δ → ∀ t : ℝ, |t| < δ → ‖iteratedFDeriv ℝ K S (x, t)‖ ≤ C)
    (hzero : ∀ j < K, ∀ x : X, iteratedFDeriv ℝ j S (x, 0) = 0) :
    ∀ x : X, ‖x - x₀‖ < δ → ∀ t : ℝ, 0 < t → t < δ →
      ∀ j : ℕ, j ≤ K → ‖iteratedFDeriv ℝ j S (x, t)‖ ≤ C * t ^ (K - j) := by
  intro x hx t ht0 htd j hj
  have key : ∀ k ≤ K, ∀ s : ℝ, 0 < s → s < δ →
      ‖iteratedFDeriv ℝ k S (x, s)‖ ≤ C * s ^ (K - k) := by
    intro k₀ hk₀
    refine Nat.decreasingInduction (n := K)
      (motive := fun k _ => ∀ s : ℝ, 0 < s → s < δ →
        ‖iteratedFDeriv ℝ k S (x, s)‖ ≤ C * s ^ (K - k)) ?_ ?_ hk₀
    · intro k hk ih s hs0 hsd
      have hderiv : ∀ r ∈ Icc (0 : ℝ) s,
          HasDerivWithinAt (fun r' : ℝ => iteratedFDeriv ℝ k S (x, r'))
            (((fderiv ℝ (fun z : X × ℝ => iteratedFDeriv ℝ k S z) (x, r)).comp
              (ContinuousLinearMap.inr ℝ X ℝ)) 1) (Icc 0 s) r := by
        intro r _
        have h1 : HasFDerivAt (fun r' : ℝ => ((x, r') : X × ℝ)) (ContinuousLinearMap.inr ℝ X ℝ) r :=
          hasFDerivAt_prodMk_right x r
        have h2 : HasFDerivAt (fun z : X × ℝ => iteratedFDeriv ℝ k S z)
            (fderiv ℝ (fun z : X × ℝ => iteratedFDeriv ℝ k S z) (x, r)) (x, r) :=
          (((hS.iteratedFDeriv_right' (m := ∞) (i := k)).differentiable
            (by simp)) (x, r)).hasFDerivAt
        exact ((h2.comp r h1).hasDerivAt).hasDerivWithinAt
      have hbound : ∀ r ∈ Ico (0 : ℝ) s,
          ‖(((fderiv ℝ (fun z : X × ℝ => iteratedFDeriv ℝ k S z) (x, r)).comp
              (ContinuousLinearMap.inr ℝ X ℝ)) 1)‖ ≤ C * s ^ (K - (k + 1)) := by
        intro r hr
        have hr0 : 0 ≤ r := hr.1
        have hrs : r < s := hr.2
        have hle : ‖(((fderiv ℝ (fun z : X × ℝ => iteratedFDeriv ℝ k S z) (x, r)).comp
              (ContinuousLinearMap.inr ℝ X ℝ)) 1)‖ ≤ ‖iteratedFDeriv ℝ (k + 1) S (x, r)‖ := by
          refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
          rw [norm_one, mul_one]
          exact norm_fderiv_jet_le k x r
        rcases eq_or_lt_of_le hr0 with h0 | hpos
        · subst h0
          by_cases hk1 : k + 1 = K
          · rw [← hk1]
            rw [Nat.sub_self, pow_zero, mul_one]
            have h1 : ‖iteratedFDeriv ℝ (k + 1) S (x, 0)‖ ≤ C := by
              rw [hk1]
              exact hloc x hx 0 (by simpa using hδ)
            exact le_trans hle h1
          · have hz : ‖iteratedFDeriv ℝ (k + 1) S (x, 0)‖ = 0 := by
              rw [hzero (k + 1) (lt_of_le_of_ne (Nat.succ_le_of_lt hk) hk1) x, norm_zero]
            rw [hz] at hle
            exact le_trans hle (mul_nonneg hC (pow_nonneg hs0.le _))
        · refine le_trans hle (le_trans (ih r hpos (lt_trans hrs hsd)) ?_)
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hr0 hrs.le (K - (k + 1))) hC
      have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound s
        (right_mem_Icc.mpr hs0.le)
      have hz : iteratedFDeriv ℝ k S (x, 0) = 0 := hzero k hk x
      rw [hz, sub_zero] at hmvt
      have hpow : (C * s ^ (K - (k + 1))) * (s - 0) = C * s ^ (K - k) := by
        rw [sub_zero, mul_assoc, ← pow_succ]
        congr 2
        omega
      linarith [hmvt, hpow.le, hpow.ge]
    · intro s hs0 hsd
      simpa using hloc x hx s (by rw [abs_of_pos hs0]; exact hsd)
  exact key j hj t ht0 htd

end

theorem flat_jets_bound {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {S : X × ℝ → E} {K : ℕ}
    (hS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S)
    (hflat : ∀ i < K, ∀ x : X, iteratedDeriv i (fun t : ℝ => S (x, t)) 0 = 0) :
    ∀ x₀ : X, ∃ C δ : ℝ, 0 < δ ∧ ∀ x : X, ‖x - x₀‖ < δ → ∀ t : ℝ, 0 < t → t < δ →
      ∀ j : ℕ, j ≤ K → ‖iteratedFDeriv ℝ j S (x, t)‖ ≤ C * t ^ (K - j) := by
  intro x₀
  have hjet : ContDiff ℝ ∞ (fun z : X × ℝ => iteratedFDeriv ℝ K S z) :=
    hS.iteratedFDeriv_right' (m := ∞) (i := K)
  have hcont : Continuous (fun z : X × ℝ => ‖iteratedFDeriv ℝ K S z‖) := hjet.continuous.norm
  obtain ⟨δ₁, hδ₁, hb⟩ := Metric.continuous_iff.1 hcont (x₀, 0) 1 (by norm_num)
  set C : ℝ := ‖iteratedFDeriv ℝ K S (x₀, 0)‖ + 1 with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  refine ⟨C, min δ₁ 1, lt_min hδ₁ one_pos, ?_⟩
  intro x hx t ht0 htd j hj
  have hloc : ∀ x' : X, ‖x' - x₀‖ < min δ₁ 1 → ∀ t' : ℝ, |t'| < min δ₁ 1 →
      ‖iteratedFDeriv ℝ K S (x', t')‖ ≤ C := by
    intro x' hx' t' ht'
    have hz : dist ((x', t') : X × ℝ) (x₀, 0) < δ₁ := by
      rw [dist_eq_norm, Prod.norm_def]
      simp only [Prod.fst_sub, Prod.snd_sub, sub_zero]
      exact max_lt (lt_of_lt_of_le hx' (min_le_left _ _))
        (lt_of_lt_of_le ht' (min_le_left _ _))
    have h := hb (x', t') hz
    rw [Real.dist_eq] at h
    have h2 := (abs_lt.1 h).2
    have h3 : ‖iteratedFDeriv ℝ K S (x', t')‖ <
        ‖iteratedFDeriv ℝ K S (x₀, 0)‖ + 1 := by linarith
    rw [hCdef]
    linarith
  exact flat_descent hS (lt_min hδ₁ one_pos) hCnn hloc
    (fun i hi y => iteratedFDeriv_at_zero_eq_zero hS hflat hi y) x hx t ht0 htd j hj

end Work.Drive
