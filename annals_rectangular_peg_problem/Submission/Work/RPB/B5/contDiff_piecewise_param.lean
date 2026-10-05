import Mathlib
import Submission.Work.RPB.B5.mixedPartialFiberSwap

/-!
# Piecewise gluing of `C^k` functions on a product `P × ℝ`

If `f g : P → ℝ → E` are `C^k` as functions of `(p,t) ∈ P × ℝ` and their `t`-jets up to order
`k` agree at `t = x₀` (for every parameter `p`), then the piecewise function
`(p,t) ↦ if t ≤ x₀ then f p t else g p t` is again `C^k`.

This is the parametric version of `Work.RPB.B5.contDiff_piecewise` (the case `P = PUnit`).
Slicewise smoothness is *not* enough: the cross (mixed) partials must also match, which is what
the `iteratedDeriv`-hypothesis encodes once one uses that `t`-differentiation of a jointly
smooth family commutes with differentiation in the parameter.

## Layout of the argument

Write `D = g - f` on `P × ℝ`, so that the glued function is `f + D·H` with `H = 1_{t > x₀}` the
sharp Heaviside function.  By hypothesis `D` is jointly `C^k` and flat of order `k` along the
hyperplane `{t = x₀}`, i.e. all its `t`-derivatives up to order `k` vanish there.  The heart of
the file is

* `paramFiberIteratedDeriv` : the `j`-th `t`-derivative of a jointly smooth family is its `j`-th
  iterated Fréchet derivative applied to `j` copies of the direction `(0,1)`;
* `mixedPartialFiberSwap` : second-order Clairaut (`∂_t ∂_p = ∂_p ∂_t`) for a family over
  `P × ℝ`;
* `iteratedDerivFDerivFiber` : the resulting commutation of `∂_t^j` with `fderiv` in the
  parameter direction;
* `contDiff_heaviside_zero` : if `h` is jointly `C^k` and flat of order `k` on the hyperplane,
  then `h · 1_{t > x₀}` is jointly `C^k` — proved by induction on `k`, differentiating once and
  observing that `fderiv h` is again jointly `C^{k-1}` and flat of order `k - 1` (this is where
  the mixed-partial commutation is used).

The main theorem then follows by writing the glued function as `f + (g - f)·1_{t > x₀}`.

A remark on universes: `contDiff_heaviside_zero` is stated with the parameter space and the
value space in the *same* universe, because its successor step applies the induction hypothesis
to the value space `(P × ℝ) →L E`, whose universe is `max u v`.  The main theorem, whose
parameters live in arbitrary universes, is reduced to that situation by enlarging the parameter
space from `P` to `P × E` (so that both live in universe `max u v`) and reading off the answer
with `Prod.snd`.
-/

open scoped ContDiff Topology

open Filter

namespace Work.RPB.B5

set_option autoImplicit false

noncomputable section

/-! ## Elementary derivatives along the two factors -/

/-- The derivative of a function on `P × ℝ` along a vertical line is the Fréchet derivative
applied to the direction `(0,1)`. -/
lemma aux_deriv_fiber {P G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (Ψ : P × ℝ → G) (p : P) (t : ℝ)
    (hΨ : DifferentiableAt ℝ Ψ (p, t)) :
    deriv (fun s => Ψ (p, s)) t = fderiv ℝ Ψ (p, t) ((0 : P), (1 : ℝ)) := by
  have h1 : HasFDerivAt (fun s : ℝ => (p, s)) (ContinuousLinearMap.inr ℝ P ℝ) t :=
    hasFDerivAt_prodMk_right p t
  have h2 : HasFDerivAt Ψ (fderiv ℝ Ψ (p, t)) (p, t) := hΨ.hasFDerivAt
  have h3 : HasDerivAt (fun s : ℝ => Ψ (p, s))
      (fderiv ℝ Ψ (p, t) ((0 : P), (1 : ℝ))) t := by
    have h4 := (h2.comp t h1).hasDerivAt
    simpa [Function.comp_def] using h4
  exact h3.deriv

/-- `fderiv` of a function on `P × ℝ` in the direction `(v,0)` is the derivative of its
`P`-fiber. -/
lemma aux_fderiv_inl {P G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (Ψ : P × ℝ → G) (p : P) (t : ℝ) (v : P)
    (hΨ : DifferentiableAt ℝ Ψ (p, t)) :
    fderiv ℝ Ψ (p, t) (v, (0 : ℝ)) = fderiv ℝ (fun q => Ψ (q, t)) p v := by
  have h1 : HasFDerivAt (fun q : P => (q, t)) (ContinuousLinearMap.inl ℝ P ℝ) p :=
    hasFDerivAt_prodMk_left p t
  have h2 : HasFDerivAt Ψ (fderiv ℝ Ψ (p, t)) (p, t) := hΨ.hasFDerivAt
  have h3 : fderiv ℝ (fun q : P => Ψ (q, t)) p
      = (fderiv ℝ Ψ (p, t)).comp (ContinuousLinearMap.inl ℝ P ℝ) := (h2.comp p h1).fderiv
  rw [h3]
  simp [ContinuousLinearMap.inl]

/-- `fderiv` of a function on `P × ℝ` in the direction `(0,s)`. -/
lemma aux_fderiv_inr {P G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (Ψ : P × ℝ → G) (p : P) (t : ℝ) (s : ℝ)
    (hΨ : DifferentiableAt ℝ Ψ (p, t)) :
    fderiv ℝ Ψ (p, t) ((0 : P), s) = s • deriv (fun u => Ψ (p, u)) t := by
  rw [show (((0 : P), s) : P × ℝ) = s • ((0 : P), (1 : ℝ)) by ext <;> simp]
  rw [map_smul, aux_deriv_fiber Ψ p t hΨ]

/-- Evaluation at a fixed vector commutes with the iterated derivative. -/
lemma aux_iteratedDeriv_clm_apply {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : F →L[ℝ] G) (i : ℕ) (Φ : ℝ → F) (x : ℝ)
    (hΦ : ContDiffAt ℝ (i : ℕ∞ω) Φ x) :
    iteratedDeriv i (fun t => L (Φ t)) x = L (iteratedDeriv i Φ x) := by
  change (iteratedFDeriv ℝ i (L ∘ Φ) x) (fun _ => (1 : ℝ))
      = L ((iteratedFDeriv ℝ i Φ x) (fun _ => (1 : ℝ)))
  rw [ContinuousLinearMap.iteratedFDeriv_comp_left L hΦ (i := i) le_rfl]
  simp [ContinuousLinearMap.compContinuousMultilinearMap_coe]

/-! ## The analytic inputs -/

-- The two analytic inputs `paramFiberIteratedDeriv` and `mixedPartialFiberSwap` are proved in
-- the sibling modules imported above.

/-- The `n`-th `t`-derivative of a jointly `C^{n+k}` function is jointly `C^k`. -/
lemma contDiff_iteratedDeriv_fiber :
    ∀ (n : ℕ) {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ) (Φ : P × ℝ → E),
      ContDiff ℝ ((n : ℕ∞ω) + (k : ℕ∞ω)) Φ →
      ContDiff ℝ (k : ℕ∞ω) (fun z : P × ℝ => iteratedDeriv n (fun s => Φ (z.1, s)) z.2) := by
  intro n
  induction n with
  | zero =>
    intro P E _ _ _ _ k Φ hΦ
    simpa using hΦ
  | succ m ih =>
    intro P E _ _ _ _ k Φ hΦ
    have h1 : ContDiff ℝ ((m : ℕ∞ω) + ((k + 1 : ℕ) : ℕ∞ω)) Φ :=
      hΦ.of_le (le_of_eq (by push_cast; ring))
    have hΨ : ContDiff ℝ (((k + 1 : ℕ)) : ℕ∞ω)
        (fun z : P × ℝ => iteratedDeriv m (fun s => Φ (z.1, s)) z.2) := ih (k + 1) Φ h1
    have hcast : ((k + 1 : ℕ) : ℕ∞ω) = (k : ℕ∞ω) + 1 := by push_cast; ring
    have hΨ' : ContDiff ℝ ((k : ℕ∞ω) + 1)
        (fun z : P × ℝ => iteratedDeriv m (fun s => Φ (z.1, s)) z.2) := by
      simpa only [hcast] using hΨ
    have hderiv : ContDiff ℝ (k : ℕ∞ω)
        (fderiv ℝ (fun z : P × ℝ => iteratedDeriv m (fun s => Φ (z.1, s)) z.2)) :=
      (contDiff_succ_iff_fderiv.mp hΨ').2.2
    have hid : (fun z : P × ℝ => iteratedDeriv (m + 1) (fun s => Φ (z.1, s)) z.2)
        = fun z : P × ℝ => fderiv ℝ
            (fun w : P × ℝ => iteratedDeriv m (fun s => Φ (w.1, s)) w.2) z ((0 : P), (1 : ℝ)) := by
      funext z
      rw [iteratedDeriv_succ]
      exact aux_deriv_fiber (fun w : P × ℝ => iteratedDeriv m (fun s => Φ (w.1, s)) w.2)
        z.1 z.2 ((hΨ.differentiable (by simp)).differentiableAt)
    rw [hid]
    exact hderiv.clm_apply contDiff_const

/-- The `j`-th `t`-derivative of the parameter derivative of a family is the parameter derivative
of the `j`-th `t`-derivative. -/
theorem iteratedDerivFDerivFiber {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j : ℕ) : ∀ (Φ : P × ℝ → E) (v : P), ContDiff ℝ ((j + 1 : ℕ) : ℕ∞ω) Φ →
      ∀ (p : P) (t : ℝ),
      iteratedDeriv j (fun s => fderiv ℝ Φ (p, s) (v, (0 : ℝ))) t
        = fderiv ℝ (fun q => iteratedDeriv j (fun s => Φ (q, s)) t) p v := by
  induction j with
  | zero =>
    intro Φ v hΦ p t
    simp only [iteratedDeriv_zero]
    exact aux_fderiv_inl Φ p t v (hΦ.differentiable (by simp)).differentiableAt
  | succ n ih =>
    intro Φ v hΦ p t
    rw [iteratedDeriv_succ]
    have hfun : iteratedDeriv n (fun s => fderiv ℝ Φ (p, s) (v, (0 : ℝ)))
        = fun t' => fderiv ℝ (fun q => iteratedDeriv n (fun s => Φ (q, s)) t') p v := by
      funext t'
      exact ih Φ v (hΦ.of_le (by exact_mod_cast Nat.le_succ (n + 1))) p t'
    rw [hfun]
    have hD : ContDiffAt ℝ (2 : ℕ∞ω)
        (fun z : P × ℝ => iteratedDeriv n (fun s => Φ (z.1, s)) z.2) (p, t) := by
      have hΦnk : ContDiff ℝ ((n : ℕ∞ω) + 2) Φ := by
        have hcast2 : (((n + 1 + 1 : ℕ)) : ℕ∞ω) = (n : ℕ∞ω) + 2 := by push_cast; ring
        rw [hcast2] at hΦ
        exact hΦ
      exact (contDiff_iteratedDeriv_fiber n 2 Φ hΦnk).contDiffAt
    have hswap := mixedPartialFiberSwap
      (fun z : P × ℝ => iteratedDeriv n (fun s => Φ (z.1, s)) z.2) p t v hD
    rw [hswap]
    have hfun2 : (fun q => deriv (fun s => iteratedDeriv n (fun s' => Φ (q, s')) s) t)
        = (fun q => iteratedDeriv (n + 1) (fun s => Φ (q, s)) t) := by
      funext q
      rw [iteratedDeriv_succ]
    have hfinal : fderiv ℝ (fun q => deriv
          (fun s => iteratedDeriv n (fun s' => Φ (q, s')) s) t) p v
        = fderiv ℝ (fun q => iteratedDeriv (n + 1) (fun s => Φ (q, s)) t) p v := by
      rw [hfun2]
    exact hfinal

/-! ## Truncating a flat function by the Heaviside function -/

/-- At a point of the hyperplane where `h` vanishes together with all first derivatives, the
Heaviside-truncated function is differentiable with derivative `0`. -/
lemma hasFDerivAt_ite_heaviside {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (h : P × ℝ → E) (x₀ : ℝ) (p : P)
    (hd : DifferentiableAt ℝ h (p, x₀)) (hzero : h (p, x₀) = 0)
    (hf0 : fderiv ℝ h (p, x₀) = 0) :
    HasFDerivAt (fun z : P × ℝ => if z.2 ≤ x₀ then (0 : E) else h z)
      (0 : P × ℝ →L[ℝ] E) (p, x₀) := by
  rw [hasFDerivAt_iff_tendsto]
  have hc : Tendsto (fun y : P × ℝ =>
        ‖y - (p, x₀)‖⁻¹ * ‖h y - h (p, x₀) - (0 : P × ℝ →L[ℝ] E) (y - (p, x₀))‖)
      (𝓝 (p, x₀)) (𝓝 0) := by
    have h1 : HasFDerivAt h (fderiv ℝ h (p, x₀)) (p, x₀) := hd.hasFDerivAt
    rw [hf0] at h1
    rwa [hasFDerivAt_iff_tendsto] at h1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc (fun y => ?_) (fun y => ?_)
  · exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)
  · have hmain : ‖(if y.2 ≤ x₀ then (0 : E) else h y)‖ ≤ ‖h y‖ := by
      by_cases hy : y.2 ≤ x₀
      · rw [ite_eq_left hy, norm_zero]
        exact norm_nonneg _
      · rw [ite_eq_right hy]
    have hle : ‖(if y.2 ≤ x₀ then (0 : E) else h y)
        - (if (p, x₀).2 ≤ x₀ then (0 : E) else h (p, x₀))
        - (0 : P × ℝ →L[ℝ] E) (y - (p, x₀))‖
        ≤ ‖h y - h (p, x₀) - (0 : P × ℝ →L[ℝ] E) (y - (p, x₀))‖ := by
      have hb : (if (p, x₀).2 ≤ x₀ then (0 : E) else h (p, x₀)) = 0 := by
        rw [ite_eq_left (le_refl x₀)]
      rw [hb, hzero]
      simp only [zero_apply, sub_zero]
      exact hmain
    exact mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr (norm_nonneg _))

/-- The Heaviside truncation of a function vanishing at the hyperplane, together with its
first derivative there, has the expected Fréchet derivative. -/
lemma fderiv_ite_heaviside {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (h : P × ℝ → E) (x₀ : ℝ)
    (hdiff : ∀ y, DifferentiableAt ℝ h y) (hzero : ∀ p, h (p, x₀) = 0)
    (hfderiv0 : ∀ p, fderiv ℝ h (p, x₀) = 0) :
    fderiv ℝ (fun z : P × ℝ => if z.2 ≤ x₀ then (0 : E) else h z)
      = fun z : P × ℝ => if z.2 ≤ x₀ then 0 else fderiv ℝ h z := by
  funext z
  obtain ⟨a, b⟩ := z
  rcases lt_trichotomy b x₀ with hlt | heq | hgt
  · have hev : (fun w : P × ℝ => if w.2 ≤ x₀ then (0 : E) else h w)
        =ᶠ[𝓝 (a, b)] (fun _ => (0 : E)) := by
      filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds hlt] with w hw
      simp [le_of_lt hw]
    rw [hev.fderiv_eq]
    rw [show fderiv ℝ (fun _ : P × ℝ => (0 : E)) (a, b) = 0 from
      (hasFDerivAt_const (0 : E) (a, b)).fderiv]
    rw [ite_eq_left (le_of_lt hlt)]
  · subst b
    rw [(hasFDerivAt_ite_heaviside h x₀ a (hdiff (a, x₀)) (hzero a) (hfderiv0 a)).fderiv]
    simp
  · have hev : (fun w : P × ℝ => if w.2 ≤ x₀ then (0 : E) else h w)
        =ᶠ[𝓝 (a, b)] h := by
      filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hgt] with w hw
      simp [not_le.mpr hw]
    rw [hev.fderiv_eq, ite_eq_right (not_le.mpr hgt)]

/-- The Heaviside truncation of a function vanishing at the hyperplane, together with its
first derivative there, is differentiable. -/
lemma differentiable_ite_heaviside {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (h : P × ℝ → E) (x₀ : ℝ)
    (hdiff : ∀ y, DifferentiableAt ℝ h y) (hzero : ∀ p, h (p, x₀) = 0)
    (hfderiv0 : ∀ p, fderiv ℝ h (p, x₀) = 0) :
    Differentiable ℝ (fun z : P × ℝ => if z.2 ≤ x₀ then (0 : E) else h z) := by
  intro z
  obtain ⟨a, b⟩ := z
  rcases lt_trichotomy b x₀ with hlt | heq | hgt
  · have hev : (fun w : P × ℝ => if w.2 ≤ x₀ then (0 : E) else h w)
        =ᶠ[𝓝 (a, b)] (fun _ => (0 : E)) := by
      filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds hlt] with w hw
      simp [le_of_lt hw]
    exact hev.differentiableAt_iff.mpr (differentiableAt_const _)
  · subst b
    exact (hasFDerivAt_ite_heaviside h x₀ a (hdiff (a, x₀)) (hzero a) (hfderiv0 a)).differentiableAt
  · have hev : (fun w : P × ℝ => if w.2 ≤ x₀ then (0 : E) else h w)
        =ᶠ[𝓝 (a, b)] h := by
      filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hgt] with w hw
      simp [not_le.mpr hw]
    exact hev.differentiableAt_iff.mpr (hdiff (a, b))

/-! ## Flatness of the derivative of a flat function -/

/-- If `h` is jointly `C^{n+1}` and flat of order `n+1` along the hyperplane `{t = x₀}`, then
`fderiv h` is flat of order `n`. -/
lemma flat_fderiv {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) (h : P → ℝ → E) (x₀ : ℝ)
    (hh : ContDiff ℝ (n + 1) (fun z : P × ℝ => h z.1 z.2))
    (hflat : ∀ p (j : ℕ), j ≤ n + 1 → iteratedDeriv j (fun t => h p t) x₀ = 0) :
    ∀ p (j : ℕ), j ≤ n →
      iteratedDeriv j (fun t => fderiv ℝ (fun z : P × ℝ => h z.1 z.2) (p, t)) x₀ = 0 := by
  intro p j hj
  have hcast : ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 := by simp
  have hh' : ContDiff ℝ ((n : ℕ∞ω) + 1) (fun z : P × ℝ => h z.1 z.2) := by
    simpa only [hcast] using hh
  obtain ⟨_, _, hderiv⟩ := contDiff_succ_iff_fderiv.mp hh'
  have hderivj : ContDiff ℝ (j : ℕ∞ω) (fderiv ℝ (fun z : P × ℝ => h z.1 z.2)) :=
    hderiv.of_le (by exact_mod_cast hj)
  refine ContinuousLinearMap.ext (fun w => ?_)
  obtain ⟨v, s⟩ := w
  simp only [zero_apply]
  rw [show (v, s) = (v, (0 : ℝ)) + s • ((0 : P), (1 : ℝ)) by ext <;> simp]
  rw [map_add, map_smul]
  have hcontj :
      ContDiffAt ℝ (j : ℕ∞ω) (fun t => fderiv ℝ (fun z : P × ℝ => h z.1 z.2) (p, t)) x₀ :=
    (hderivj.contDiffAt (x := (p, x₀))).comp x₀ (contDiffAt_const.prodMk contDiffAt_id)
  have h1 : (iteratedDeriv j (fun t => fderiv ℝ (fun z : P × ℝ => h z.1 z.2) (p, t)) x₀)
      (v, (0 : ℝ)) = 0 := by
    have hev : (iteratedDeriv j (fun t => fderiv ℝ (fun z : P × ℝ => h z.1 z.2) (p, t)) x₀)
        (v, (0 : ℝ))
        = iteratedDeriv j (fun t => fderiv ℝ (fun z : P × ℝ => h z.1 z.2) (p, t) (v, (0 : ℝ))) x₀ := by
      simpa using (aux_iteratedDeriv_clm_apply (ContinuousLinearMap.apply ℝ E (v, (0 : ℝ))) j
        (fun t => fderiv ℝ (fun z : P × ℝ => h z.1 z.2) (p, t)) x₀ hcontj).symm
    rw [hev]
    rw [iteratedDerivFDerivFiber j (fun z : P × ℝ => h z.1 z.2) v
      (hh.of_le (by exact_mod_cast Nat.succ_le_succ hj)) p x₀]
    have hzero : (fun q => iteratedDeriv j (fun s => h q s) x₀) = fun _ => (0 : E) := by
      funext q
      exact hflat q j (le_trans hj (Nat.le_succ n))
    rw [hzero]
    rw [show fderiv ℝ (fun _ : P => (0 : E)) p = 0 from (hasFDerivAt_const (0 : E) p).fderiv]
    simp
  have h2 : (iteratedDeriv j (fun t => fderiv ℝ (fun z : P × ℝ => h z.1 z.2) (p, t)) x₀)
      ((0 : P), (1 : ℝ)) = 0 := by
    have hev : (iteratedDeriv j (fun t => fderiv ℝ (fun z : P × ℝ => h z.1 z.2) (p, t)) x₀)
        ((0 : P), (1 : ℝ))
        = iteratedDeriv j
          (fun t => fderiv ℝ (fun z : P × ℝ => h z.1 z.2) (p, t) ((0 : P), (1 : ℝ))) x₀ := by
      simpa using (aux_iteratedDeriv_clm_apply (ContinuousLinearMap.apply ℝ E ((0 : P), (1 : ℝ))) j
        (fun t => fderiv ℝ (fun z : P × ℝ => h z.1 z.2) (p, t)) x₀ hcontj).symm
    rw [hev]
    have hfun : (fun t => fderiv ℝ (fun z : P × ℝ => h z.1 z.2) (p, t) ((0 : P), (1 : ℝ)))
        = fun t => deriv (fun u => h p u) t := by
      funext t
      simpa using aux_fderiv_inr (fun z : P × ℝ => h z.1 z.2) p t 1
        ((hh.differentiable (by simp)).differentiableAt)
    rw [hfun, ← iteratedDeriv_succ']
    exact hflat p (j + 1) (by omega)
  rw [h1, h2]
  simp

/-! ## The Heaviside truncation of a flat `C^k` function -/

universe u

/-- **Flat truncation.**  If `h` is jointly `C^k` and all its `t`-derivatives of order `≤ k`
vanish at `t = x₀` (for every parameter), then `h · 1_{t > x₀}` is jointly `C^k`.

(The two types live in the same universe so that the induction may be applied in the successor
step to the space of continuous linear maps `(P × ℝ) →L[ℝ] E`, which has the same universe
level.) -/
theorem contDiff_heaviside_zero :
    ∀ (k : ℕ) {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup E] [NormedSpace ℝ E] (h : P → ℝ → E) (x₀ : ℝ),
      ContDiff ℝ k (fun z : P × ℝ => h z.1 z.2) →
      (∀ p (j : ℕ), j ≤ k → iteratedDeriv j (fun t => h p t) x₀ = 0) →
      ContDiff ℝ k (fun z : P × ℝ => if z.2 ≤ x₀ then 0 else h z.1 z.2) := by
  intro k
  induction k with
  | zero =>
    intro P E _ _ _ _ h x₀ hh hflat
    have hcont : Continuous (fun z : P × ℝ => h z.1 z.2) := hh.continuous
    refine contDiff_zero.mpr
      (Continuous.if_le continuous_const hcont continuous_snd continuous_const ?_)
    intro z hz
    have hz0 : h z.1 x₀ = 0 := by
      have := hflat z.1 0 (Nat.zero_le 0)
      simpa using this
    rw [hz]
    exact hz0.symm
  | succ n ih =>
    intro P E _ _ _ _ h x₀ hh hflat
    have hcast : ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 := by simp
    have hh' : ContDiff ℝ ((n : ℕ∞ω) + 1) (fun z : P × ℝ => h z.1 z.2) := by
      simpa only [hcast] using hh
    obtain ⟨hdiff, -, hderiv⟩ := contDiff_succ_iff_fderiv.mp hh'
    have hflat1 : ∀ p, h p x₀ = 0 := by
      intro p
      have := hflat p 0 (Nat.zero_le (n + 1))
      simpa using this
    have hfderiv0 : ∀ p,
        fderiv ℝ (fun z : P × ℝ => h z.1 z.2) (p, x₀) = (0 : P × ℝ →L[ℝ] E) := by
      intro p
      refine ContinuousLinearMap.ext (fun w => ?_)
      obtain ⟨v, s⟩ := w
      simp only [zero_apply]
      rw [show (v, s) = (v, (0 : ℝ)) + s • ((0 : P), (1 : ℝ)) by ext <;> simp]
      rw [map_add, map_smul]
      have hb : fderiv ℝ (fun z : P × ℝ => h z.1 z.2) (p, x₀) (v, (0 : ℝ)) = 0 := by
        rw [aux_fderiv_inl _ p x₀ v (hdiff (p, x₀))]
        have hz : (fun q => (fun z : P × ℝ => h z.1 z.2) (q, x₀)) = fun _ => (0 : E) := by
          funext q; exact hflat1 q
        rw [hz]
        rw [show fderiv ℝ (fun _ : P => (0 : E)) p = 0 from (hasFDerivAt_const (0 : E) p).fderiv]
        simp
      have hb2 : fderiv ℝ (fun z : P × ℝ => h z.1 z.2) (p, x₀) ((0 : P), (1 : ℝ)) = 0 := by
        rw [aux_fderiv_inr _ p x₀ 1 (hdiff (p, x₀))]
        have h1 : deriv (fun u => (fun z : P × ℝ => h z.1 z.2) (p, u)) x₀ = 0 := by
          have := hflat p 1 (by omega)
          simpa [iteratedDeriv_one] using this
        rw [show (fun u => (fun z : P × ℝ => h z.1 z.2) (p, u)) = fun u => h p u from rfl, h1]
        simp
      rw [hb, hb2]
      simp
    have hflat' : ∀ p (j : ℕ), j ≤ n →
        iteratedDeriv j (fun t => fderiv ℝ (fun z : P × ℝ => h z.1 z.2) (p, t)) x₀ = 0 :=
      flat_fderiv n h x₀ hh hflat
    have hIH := ih (fun p t => fderiv ℝ (fun z : P × ℝ => h z.1 z.2) (p, t)) x₀ hderiv hflat'
    have hgoal : ContDiff ℝ ((n : ℕ∞ω) + 1)
        (fun z : P × ℝ => if z.2 ≤ x₀ then 0 else h z.1 z.2) := by
      refine contDiff_succ_iff_fderiv.mpr ⟨?_, (fun hcon => by simp at hcon), ?_⟩
      · exact differentiable_ite_heaviside _ x₀ (fun y => hdiff y) hflat1 hfderiv0
      · rw [fderiv_ite_heaviside _ x₀ (fun y => hdiff y) hflat1 hfderiv0]
        exact hIH
    exact hcast ▸ hgoal

/-! ## The main theorem -/

theorem contDiff_piecewise_param {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (f g : P → ℝ → E) (x₀ : ℝ)
    (hf : ContDiff ℝ k (fun z : P × ℝ => f z.1 z.2))
    (hg : ContDiff ℝ k (fun z : P × ℝ => g z.1 z.2))
    (hjet : ∀ p (j : ℕ), j ≤ k → iteratedDeriv j (f p) x₀ = iteratedDeriv j (g p) x₀) :
    ContDiff ℝ k (fun z : P × ℝ => if z.2 ≤ x₀ then f z.1 z.2 else g z.1 z.2) := by
  -- Enlarge the parameter space to `P × E` so that parameter and value space share a universe.
  let F : P × E → ℝ → P × E := fun q t => (q.1, f q.1 t)
  let G : P × E → ℝ → P × E := fun q t => (q.1, g q.1 t)
  have hF : ContDiff ℝ k (fun z : (P × E) × ℝ => F z.1 z.2) := by
    have h1 : ContDiff ℝ k (fun z : (P × E) × ℝ => (z.1).1) :=
      ((ContinuousLinearMap.fst ℝ P E).comp (ContinuousLinearMap.fst ℝ (P × E) ℝ)).contDiff
    have h2 : ContDiff ℝ k (fun z : (P × E) × ℝ => f (z.1).1 z.2) :=
      hf.comp (((ContinuousLinearMap.fst ℝ P E).comp
        (ContinuousLinearMap.fst ℝ (P × E) ℝ)).prod
          (ContinuousLinearMap.snd ℝ (P × E) ℝ)).contDiff
    exact h1.prodMk h2
  have hG : ContDiff ℝ k (fun z : (P × E) × ℝ => G z.1 z.2) := by
    have h1 : ContDiff ℝ k (fun z : (P × E) × ℝ => (z.1).1) :=
      ((ContinuousLinearMap.fst ℝ P E).comp (ContinuousLinearMap.fst ℝ (P × E) ℝ)).contDiff
    have h2 : ContDiff ℝ k (fun z : (P × E) × ℝ => g (z.1).1 z.2) :=
      hg.comp (((ContinuousLinearMap.fst ℝ P E).comp
        (ContinuousLinearMap.fst ℝ (P × E) ℝ)).prod
          (ContinuousLinearMap.snd ℝ (P × E) ℝ)).contDiff
    exact h1.prodMk h2
  have hjet' : ∀ q (j : ℕ), j ≤ k →
      iteratedDeriv j (fun t => G q t - F q t) x₀ = 0 := by
    intro q j hj
    have hq1 : ContDiffAt ℝ (j : ℕ∞ω) (fun t => f q.1 t) x₀ :=
      (hf.contDiffAt (x := (q.1, x₀))).of_le (by exact_mod_cast hj) |>.comp x₀
        (contDiffAt_const.prodMk contDiffAt_id)
    have hq2 : ContDiffAt ℝ (j : ℕ∞ω) (fun t => g q.1 t) x₀ :=
      (hg.contDiffAt (x := (q.1, x₀))).of_le (by exact_mod_cast hj) |>.comp x₀
        (contDiffAt_const.prodMk contDiffAt_id)
    have hsub : (fun t => G q t - F q t) = fun t => ((0 : P), g q.1 t - f q.1 t) := by
      funext t
      simp only [G, F, Prod.mk_sub_mk, sub_self]
    rw [hsub]
    have hev : iteratedDeriv j (fun t => ((0 : P), g q.1 t - f q.1 t)) x₀
        = ((0 : P), iteratedDeriv j (fun t => g q.1 t - f q.1 t) x₀) := by
      simpa using aux_iteratedDeriv_clm_apply (ContinuousLinearMap.inr ℝ P E) j
        (fun t => g q.1 t - f q.1 t) x₀ (hq2.sub hq1)
    have hzero : iteratedDeriv j (fun t => g q.1 t - f q.1 t) x₀ = 0 := by
      rw [show (fun t => g q.1 t - f q.1 t) = (fun t => g q.1 t) - (fun t => f q.1 t) from rfl,
        iteratedDeriv_sub hq2 hq1, hjet q.1 j hj, sub_self]
    rw [hev, hzero]
    simp
  have hH := contDiff_heaviside_zero k (fun q t => G q t - F q t) x₀ (hG.sub hF) hjet'
  have hglue : ContDiff ℝ k (fun z : (P × E) × ℝ => if z.2 ≤ x₀ then F z.1 z.2 else G z.1 z.2) := by
    have hrewrite : (fun z : (P × E) × ℝ => if z.2 ≤ x₀ then F z.1 z.2 else G z.1 z.2)
        = fun z : (P × E) × ℝ =>
            F z.1 z.2 + (if z.2 ≤ x₀ then 0 else (G z.1 z.2 - F z.1 z.2)) := by
      funext z
      by_cases hz : z.2 ≤ x₀ <;> simp [hz]
    rw [hrewrite]
    exact hF.add hH
  have hcomp1 : ContDiff ℝ k (fun z : P × ℝ => (((z.1, (0 : E)) : P × E), z.2)) :=
    (((ContinuousLinearMap.inl ℝ P E).comp (ContinuousLinearMap.fst ℝ P ℝ)).prod
      (ContinuousLinearMap.snd ℝ P ℝ)).contDiff
  have hcomp2 : ContDiff ℝ k
      ((fun z : (P × E) × ℝ => if z.2 ≤ x₀ then F z.1 z.2 else G z.1 z.2) ∘
        (fun z : P × ℝ => (((z.1, (0 : E)) : P × E), z.2))) := hglue.comp hcomp1
  have hcomp3 : ContDiff ℝ k
      (Prod.snd ∘ ((fun z : (P × E) × ℝ => if z.2 ≤ x₀ then F z.1 z.2 else G z.1 z.2) ∘
        (fun z : P × ℝ => (((z.1, (0 : E)) : P × E), z.2)))) :=
    (ContinuousLinearMap.snd ℝ P E).contDiff.comp hcomp2
  convert hcomp3 using 1
  funext z
  by_cases hz : z.2 ≤ x₀ <;> simp [hz, F, G]

end

end Work.RPB.B5
