import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The jet at the hyperplane is determined by the time Taylor coefficients

This file proves `Work.Diff.EXT.jets_eq_of_t_derivs_eq`: if two smooth functions
`f g : ℝ × E' → F` have, at every point `(T, x)` with `x` in a common open set `U`,
the same Taylor coefficients in the *time* variable `s ↦ f (s, x)`, then `f` and `g`
have the same full iterated Fréchet derivative at `(T, x)` to all orders.

The route is: it suffices to show that a smooth `H` all of whose time Taylor
coefficients vanish at `(T, ·)` on `U` has vanishing jet at `(T, x)`; this is proved by
induction on the order `k`, peeling the last argument of the `(k+1)`-st jet (which turns
it into a `k`-th jet of the directional derivative `z ↦ fderiv H z u`), decomposing
`u = u.1 • (1,0) + (0, u.2)`, and applying the induction hypothesis to the time derivative
`z ↦ (fderiv H z) (1,0)` (whose flatness is a shift) and to the spatial derivative
`z ↦ (fderiv H z) (0,v)` (whose flatness is Clairaut's theorem, i.e. symmetry of the
second Fréchet derivative).
-/

namespace Work.Diff.EXT

open scoped Topology

/-- The derivative of the time slice: for a function on `ℝ × E'`, the Fréchet derivative of
`s ↦ H (s, x)` is the Fréchet derivative of `H` at `(s, x)`, composed with the inclusion of
the first factor. -/
lemma jets_eq_slice_fst_fderiv {E' F : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F] [NormedSpace ℝ F] (H : ℝ × E' → F) {s : ℝ} {x : E'}
    (h : DifferentiableAt ℝ H (s, x)) :
    fderiv ℝ (fun r : ℝ => H (r, x)) s =
      (fderiv ℝ H (s, x)).comp (ContinuousLinearMap.inl ℝ ℝ E') := by
  have h1 : HasFDerivAt (fun r : ℝ => H (r, x))
      ((fderiv ℝ H (s, x)).comp (ContinuousLinearMap.inl ℝ ℝ E')) s :=
    (h.hasFDerivAt).comp s (hasFDerivAt_prodMk_left s x)
  exact h1.fderiv

/-- The derivative of the space slice: for a function on `ℝ × E'`, the Fréchet derivative of
`y ↦ H (s, y)` is the Fréchet derivative of `H` at `(s, y)`, composed with the inclusion of
the second factor. -/
lemma jets_eq_slice_snd_fderiv {E' F : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F] [NormedSpace ℝ F] (H : ℝ × E' → F) {s : ℝ} {x : E'}
    (h : DifferentiableAt ℝ H (s, x)) :
    fderiv ℝ (fun y : E' => H (s, y)) x =
      (fderiv ℝ H (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ E') := by
  have h1 : HasFDerivAt (fun y : E' => H (s, y))
      ((fderiv ℝ H (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ E')) x :=
    (h.hasFDerivAt).comp x (hasFDerivAt_prodMk_right s x)
  exact h1.fderiv

/-- The time directional derivative is the derivative of the time slice. -/
lemma jets_eq_fderiv_fst_apply {E' F : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F] [NormedSpace ℝ F] (H : ℝ × E' → F) {s : ℝ} {x : E'}
    (h : DifferentiableAt ℝ H (s, x)) :
    fderiv ℝ H (s, x) (1, 0) = deriv (fun r : ℝ => H (r, x)) s := by
  rw [← fderiv_apply_one_eq_deriv, jets_eq_slice_fst_fderiv H h]
  simp [ContinuousLinearMap.comp_apply]

/-- **Clairaut for one time and one space derivative**, in the form needed below: the time
derivative of the space directional derivative of `H` equals the space derivative of the time
directional derivative. -/
lemma jets_eq_clairaut_step {E' F : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F] [NormedSpace ℝ F] (H : ℝ × E' → F)
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (x : E') (v : E') :
    deriv (fun s : ℝ => fderiv ℝ H (s, x) (0, v))
      = fun s : ℝ => (fderiv ℝ (fun z : ℝ × E' => fderiv ℝ H z (1, 0)) (s, x)) (0, v) := by
  funext s
  have hFD : DifferentiableAt ℝ (fderiv ℝ H) (s, x) :=
    ((hH.fderiv_right (m := 1) (by simp)).differentiable (by simp)).differentiableAt
  have hslice : DifferentiableAt ℝ (fun z : ℝ × E' => fderiv ℝ H z (0, v)) (s, x) :=
    hFD.clm_apply (differentiableAt_const _)
  have hA : HasFDerivAt (fun z : ℝ × E' => fderiv ℝ H z (0, v))
      (((ContinuousLinearMap.apply ℝ F) (0, v)).comp (fderiv ℝ (fderiv ℝ H) (s, x))) (s, x) := by
    have hg0 : HasFDerivAt (⇑((ContinuousLinearMap.apply ℝ F) (0, v)) ∘ (fderiv ℝ H))
        (((ContinuousLinearMap.apply ℝ F) (0, v)) ∘SL fderiv ℝ (fderiv ℝ H) (s, x)) (s, x) :=
      HasFDerivAt.comp (s, x) (ContinuousLinearMap.hasFDerivAt _) hFD.hasFDerivAt
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using hg0
  have hB : HasFDerivAt (fun z : ℝ × E' => fderiv ℝ H z (1, 0))
      (((ContinuousLinearMap.apply ℝ F) (1, 0)).comp (fderiv ℝ (fderiv ℝ H) (s, x))) (s, x) := by
    have hg0 : HasFDerivAt (⇑((ContinuousLinearMap.apply ℝ F) (1, 0)) ∘ (fderiv ℝ H))
        (((ContinuousLinearMap.apply ℝ F) (1, 0)) ∘SL fderiv ℝ (fderiv ℝ H) (s, x)) (s, x) :=
      HasFDerivAt.comp (s, x) (ContinuousLinearMap.hasFDerivAt _) hFD.hasFDerivAt
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using hg0
  rw [← fderiv_apply_one_eq_deriv]
  rw [jets_eq_slice_fst_fderiv _ hslice]
  rw [hA.fderiv, hB.fderiv]
  have hsymm := (hH.contDiffAt (x := (s, x))).isSymmSndFDerivAt (by simp)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.apply_apply]
  exact hsymm.eq (1, 0) (0, v)

/-- **Mixed partials, iterated**: the `i`-th time derivative of the space directional derivative
of `H` equals the space directional derivative of the `i`-th *time Taylor coefficient*
`y ↦ ∂ₜ^i H (T, y)`. -/
lemma jets_eq_mixed_partial {E' F : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F] [NormedSpace ℝ F] (T : ℝ) (i : ℕ) :
    ∀ (H : ℝ × E' → F), ContDiff ℝ (⊤ : ℕ∞) H → ∀ (x : E') (v : E'),
      iteratedDeriv i (fun s : ℝ => fderiv ℝ H (s, x) (0, v)) T
        = fderiv ℝ (fun y : E' => iteratedDeriv i (fun s : ℝ => H (s, y)) T) x v := by
  induction i with
  | zero =>
    intro H hH x v
    simp only [iteratedDeriv_zero]
    have hdiff : DifferentiableAt ℝ H (T, x) := (hH.differentiable (by simp)).differentiableAt
    rw [jets_eq_slice_snd_fderiv H hdiff]
    simp [ContinuousLinearMap.comp_apply]
  | succ i ih =>
    intro H hH x v
    rw [iteratedDeriv_succ', jets_eq_clairaut_step H hH x v]
    rw [ih (fun z : ℝ × E' => fderiv ℝ H z (1, 0))
      ((hH.fderiv_right (by simp)).clm_apply contDiff_const) x v]
    have hfun : (fun y : E' => iteratedDeriv i (fun s : ℝ => fderiv ℝ H (s, y) (1, 0)) T)
        = fun y : E' => iteratedDeriv (i + 1) (fun s : ℝ => H (s, y)) T := by
      funext y
      rw [iteratedDeriv_succ']
      congr 1
      funext s
      exact (jets_eq_fderiv_fst_apply H ((hH.differentiable (by simp)).differentiableAt))
    rw [hfun]

/-- The time derivative of a function whose time Taylor coefficients vanish has vanishing
time Taylor coefficients. -/
lemma jets_eq_flat_fderiv_fst {E' F : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F] [NormedSpace ℝ F] {T : ℝ} {U : Set E'} (H : ℝ × E' → F)
    (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    (hflat : ∀ x ∈ U, ∀ i : ℕ, iteratedDeriv i (fun s : ℝ => H (s, x)) T = 0) :
    ∀ x ∈ U, ∀ i : ℕ, iteratedDeriv i (fun s : ℝ => fderiv ℝ H (s, x) (1, 0)) T = 0 := by
  intro x hx i
  have hfun : (fun s : ℝ => fderiv ℝ H (s, x) (1, 0)) = deriv (fun s : ℝ => H (s, x)) := by
    funext s
    exact jets_eq_fderiv_fst_apply H ((hH.differentiable (by simp)).differentiableAt)
  rw [hfun, ← iteratedDeriv_succ']
  exact hflat x hx (i + 1)

/-- The space directional derivative of a function whose time Taylor coefficients vanish has
vanishing time Taylor coefficients, by Clairaut's theorem and the fact that the functions
`y ↦ ∂ₜ^i H (T, y)` vanish on the neighbourhood `U`. -/
lemma jets_eq_flat_fderiv_snd {E' F : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F] [NormedSpace ℝ F] {T : ℝ} {U : Set E'} (hU : IsOpen U)
    (H : ℝ × E' → F) (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    (hflat : ∀ x ∈ U, ∀ i : ℕ, iteratedDeriv i (fun s : ℝ => H (s, x)) T = 0) (v : E') :
    ∀ x ∈ U, ∀ i : ℕ, iteratedDeriv i (fun s : ℝ => fderiv ℝ H (s, x) (0, v)) T = 0 := by
  intro x hx i
  rw [jets_eq_mixed_partial T i H hH x v]
  have hzero : (fun y : E' => iteratedDeriv i (fun s : ℝ => H (s, y)) T) =ᶠ[𝓝 x] (fun _ => 0) :=
    Filter.eventually_of_mem (hU.mem_nhds hx) (fun y hy => hflat y hy i)
  rw [hzero.fderiv_eq]
  simp

/-- **Engine.** A smooth function all of whose time Taylor coefficients vanish at `(T, ·)` on
the open set `U` has vanishing full jet at `(T, x)` for every `x ∈ U`. -/
lemma jets_eq_flat_imp_jets_zero {E' F : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F] [NormedSpace ℝ F] {T : ℝ} {U : Set E'} (hU : IsOpen U)
    (H : ℝ × E' → F) (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    (hflat : ∀ x ∈ U, ∀ i : ℕ, iteratedDeriv i (fun s : ℝ => H (s, x)) T = 0) :
    ∀ x ∈ U, ∀ k : ℕ, iteratedFDeriv ℝ k H (T, x) = 0 := by
  suffices aux : ∀ k : ℕ, ∀ (H : ℝ × E' → F), ContDiff ℝ (⊤ : ℕ∞) H →
      (∀ x ∈ U, ∀ i : ℕ, iteratedDeriv i (fun s : ℝ => H (s, x)) T = 0) →
      ∀ x ∈ U, ∀ m : Fin k → ℝ × E', iteratedFDeriv ℝ k H (T, x) m = 0 by
    intro x hx k
    ext m
    exact aux k H hH hflat x hx m
  intro k
  induction k with
  | zero =>
    intro H hH hflat x hx m
    have h0 := hflat x hx 0
    rw [iteratedDeriv_zero] at h0
    simpa using h0
  | succ k ih =>
    intro H hH hflat x hx m
    rw [iteratedFDeriv_succ_apply_right]
    set w := m (Fin.last k) with hwdef
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ H) := hH.fderiv_right (by simp)
    have hA : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ × E' => fderiv ℝ H y (1, 0)) :=
      hc.clm_apply contDiff_const
    have hB : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ × E' => fderiv ℝ H y (0, w.2)) :=
      hc.clm_apply contDiff_const
    have key1 : ((iteratedFDeriv ℝ k (fderiv ℝ H) (T, x)) (Fin.init m)) (1, 0)
        = iteratedFDeriv ℝ k (fun y : ℝ × E' => fderiv ℝ H y (1, 0)) (T, x) (Fin.init m) :=
      (iteratedFDeriv_clm_apply_const_apply hc (i := k) (by simp)
        (m := Fin.init m) (u := (1, 0))).symm
    have key2 : ((iteratedFDeriv ℝ k (fderiv ℝ H) (T, x)) (Fin.init m)) (0, w.2)
        = iteratedFDeriv ℝ k (fun y : ℝ × E' => fderiv ℝ H y (0, w.2)) (T, x) (Fin.init m) :=
      (iteratedFDeriv_clm_apply_const_apply hc (i := k) (by simp)
        (m := Fin.init m) (u := (0, w.2))).symm
    rw [show w = w.1 • ((1, 0) : ℝ × E') + (0, w.2) from by ext <;> simp]
    rw [map_add, map_smul]
    rw [key1, key2]
    rw [ih _ hA (jets_eq_flat_fderiv_fst H hH hflat) x hx (Fin.init m),
        ih _ hB (jets_eq_flat_fderiv_snd hU H hH hflat _) x hx (Fin.init m)]
    simp

/-- **The full jet at the hyperplane is determined by the time Taylor coefficients (uniform
version).**  Let `f g : ℝ × E' → F` be `C^∞`, let `U` be an open subset of `E'`, and suppose that
for every `x ∈ U` and every `i : ℕ` the time Taylor coefficients agree:
`∂ₜ^i f (T,x) = ∂ₜ^i g (T,x)`.  Then the full iterated Fréchet derivatives of `f` and `g` at
`(T,x)` agree to all orders, for every `x ∈ U`.

(The hypothesis must be uniform in `i` on a *common* open set: with a separate neighbourhood for
each order the statement is false, by a Borel-type counterexample.)

Proof sketch (induction on `k`): prove that for every pair `(F,G)` of `C^∞` functions with
`∀ x ∈ U, ∀ i, ∂ₜ^iF(T,x) = ∂ₜ^iG(T,x)` one has `∀ x ∈ U, iteratedFDeriv ℝ k F (T,x) =
iteratedFDeriv ℝ k G (T,x)`.
- `k = 0`: this is the hypothesis for `i = 0` (`iteratedFDeriv ℝ 0 F (T,x)` is `F (T,x)`, see
  `iteratedFDeriv_zero_eq_comp`).
- step: for `x ∈ U`, by `iteratedFDeriv_succ_eq_comp_right` (and
  `continuousMultilinearCurryRightEquiv'`, a linear isometry equivalence) it suffices that the
  `k`-jets of `fderiv ℝ F` and `fderiv ℝ G` agree at `(T,x)`.  The function `fderiv ℝ F` is
  determined by the two functions `z ↦ (fderiv ℝ F z) (1,0) = ∂ₜF z` and
  `z ↦ (fderiv ℝ F z) (0,v) = ∂ₓF z v` (`v : E'`); its `k`-jet at `(T,x)` is determined by the
  `k`-jets of those (use `iteratedFDeriv_clm_apply_const_apply`, which computes the jet of
  `z ↦ c z u` as the jet of `c` applied to `u`, plus extensionality of continuous multilinear maps).
  The induction hypothesis applies to the pair `(∂ₜF, ∂ₜG)`, whose hypothesis is the one for
  `(F,G)` shifted by one (`iteratedDeriv (i+1) = iteratedDeriv i ∘ deriv`), and to the pair
  `(∂ₓF, ∂ₓG)`, for which one needs `∂ₜ^i (∂ₓF)(T,y) = ∂ₓ (∂ₜ^iF)(T,y)`: Clairaut for the time
  derivative and one spatial derivative, available from skew-symmetry of the second Fréchet
  derivative (`ContDiffAt.isSymmSndFDerivAt`, `IsSymmSndFDerivAt.iteratedFDeriv_cons`), iterated in
  `i`; together with the fact that `x ↦ ∂ₜ^iF(T,x)` and `x ↦ ∂ₜ^iG(T,x)` agree on the *whole* open
  `U`, hence (as `U` is open and contains `y`) have the same `x`-derivatives at `y`. -/
theorem jets_eq_of_t_derivs_eq
    {E' F : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {T : ℝ} {U : Set E'} (hU : IsOpen U)
    {f g : ℝ × E' → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (h : ∀ x ∈ U, ∀ i : ℕ, iteratedDeriv i (fun s => f (s, x)) T = iteratedDeriv i (fun s => g (s, x)) T) :
    ∀ x ∈ U, ∀ k : ℕ, iteratedFDeriv ℝ k f (T, x) = iteratedFDeriv ℝ k g (T, x) := by
  intro x hx k
  have hsub : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × E' => f z - g z) := hf.sub hg
  have hflat : ∀ y ∈ U, ∀ i : ℕ,
      iteratedDeriv i (fun s : ℝ => (f (s, y) - g (s, y))) T = 0 := by
    intro y hy i
    have h1 : ContDiffAt ℝ (↑i) (fun s : ℝ => f (s, y)) T :=
      ((hf.comp (contDiff_prodMk_left y)).contDiffAt).of_le (by simp)
    have h2 : ContDiffAt ℝ (↑i) (fun s : ℝ => g (s, y)) T :=
      ((hg.comp (contDiff_prodMk_left y)).contDiffAt).of_le (by simp)
    have hfun : (fun s : ℝ => (f (s, y) - g (s, y)))
        = (fun s : ℝ => f (s, y)) - (fun s : ℝ => g (s, y)) := rfl
    rw [hfun, iteratedDeriv_sub h1 h2, h y hy i, sub_self]
  have hzero := jets_eq_flat_imp_jets_zero hU (fun z : ℝ × E' => f z - g z) hsub hflat x hx k
  have hsub_jet : iteratedFDeriv ℝ k f (T, x) - iteratedFDeriv ℝ k g (T, x) = 0 := by
    rw [← iteratedFDeriv_sub_apply ((hf.contDiffAt).of_le (by simp))
      ((hg.contDiffAt).of_le (by simp))]
    exact hzero
  exact sub_eq_zero.mp hsub_jet

end Work.Diff.EXT
