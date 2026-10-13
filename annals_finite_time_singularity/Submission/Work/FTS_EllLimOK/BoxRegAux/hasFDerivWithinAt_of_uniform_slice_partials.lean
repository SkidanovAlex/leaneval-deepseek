import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_EllLimOK.BoxRegAux.Defs
import Submission.Work.FTS_EllLimOK.BoxRegAux.abs_sub_mul_le_of_derivWithin_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS_EllLimOK.BoxRegAux

/-! ## Small interval and product-metric helpers -/

/-- A `uIcc` (unordered interval) with endpoints in `[a,b]` stays inside `[a,b]`. -/
theorem uIcc_subset_Icc {a b x y : ℝ} (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    Set.uIcc x y ⊆ Set.Icc a b := by
  intro t ht
  rw [Set.mem_uIcc] at ht
  rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨le_trans hx.1 h1, le_trans h2 hy.2⟩
  · exact ⟨le_trans hy.1 h1, le_trans h2 hx.2⟩

/-- A point of the unordered interval `[x,y]` is at distance at most `|y - x|` from the
endpoint `x`. -/
theorem abs_sub_left_le_abs_sub_of_mem_uIcc {x y t : ℝ} (ht : t ∈ Set.uIcc x y) :
    |t - x| ≤ |y - x| := by
  rcases le_total x y with h | h
  · rw [Set.uIcc_of_le h, Set.mem_Icc] at ht
    rw [abs_of_nonneg (by linarith [ht.1] : (0:ℝ) ≤ t - x),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ y - x)]
    linarith [ht.2]
  · rw [Set.uIcc_of_ge h, Set.mem_Icc] at ht
    rw [abs_of_nonpos (by linarith [ht.2] : t - x ≤ 0),
      abs_of_nonpos (by linarith : y - x ≤ 0)]
    linarith [ht.1]

/-- The product metric on `ℝ × ℝ` is the max of the coordinate distances, written with
absolute values. -/
theorem dist_prod_eq_max' (p q : ℝ × ℝ) : dist p q = max |p.1 - q.1| |p.2 - q.2| := by
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]

/-- To bound `dist p q` it suffices to bound both coordinate differences by the same
constant. -/
theorem dist_prod_le_of (p q : ℝ × ℝ) {r : ℝ} (h1 : |p.1 - q.1| ≤ r) (h2 : |p.2 - q.2| ≤ r) :
    dist p q ≤ r := by
  rw [dist_prod_eq_max']
  exact max_le h1 h2

/-- **The staircase/FTC engine for the closed-box regularity of a pointwise limit.**
On the box `s = [a,b] × [c,d]` (a product of two intervals), let `H n` be a sequence of functions
whose two one-variable slices have within-derivatives `P n` (in the first variable, on `[a,b]`)
and `Q n` (in the second variable, on `[c,d]`) at every point of the box, with `H n`, `P n`, `Q n`
continuous on the box.  If `H n → H₀` pointwise on the box and `P n → P₀`, `Q n → Q₀` uniformly
on the box, with `P₀`, `Q₀` continuous on the box, then `Function.uncurry H₀` is differentiable
within the box at every point of the box, with derivative the linear map with slopes `P₀`, `Q₀`.

Intended proof: for each `n`, integrate the two slice derivatives along the staircase
`(z,θ) → (z',θ) → (z',θ')` (`Work.FTS_EllipticEst`-style `intervalIntegral` FTC:
`intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le`), pass to the limit in the integrals
using the uniform convergence of `P n`, `Q n` on the box, and bound the remainder against
`ellCop (P₀ z θ) (Q₀ z θ)` by the *joint* continuity of `P₀`, `Q₀` on the box (the sup of
`|P₀ - P₀(z,θ)|` over the segment tends to `0`).  Please write the file in the namespace
`Work.FTS_EllLimOK` (as `BoxRegAux/Defs.lean` does) with `import Mathlib` and
`import Submission.Work.FTS_EllLimOK.BoxRegAux.Defs`, and do NOT open `Filter` globally in a way
that shadows names. -/
theorem hasFDerivWithinAt_of_uniform_slice_partials
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {H : ℕ → ℝ → ℝ → ℝ} {H₀ : ℝ → ℝ → ℝ}
    {P : ℕ → ℝ → ℝ → ℝ} {P₀ : ℝ → ℝ → ℝ}
    {Q : ℕ → ℝ → ℝ → ℝ} {Q₀ : ℝ → ℝ → ℝ}
    (hcontH : ∀ n, ContinuousOn (Function.uncurry (H n)) (Set.Icc a b ×ˢ Set.Icc c d))
    (hsz : ∀ n, ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      HasDerivWithinAt (fun z' => H n z' θ) (P n z θ) (Set.Icc a b) z)
    (hth : ∀ n, ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      HasDerivWithinAt (fun θ' => H n z θ') (Q n z θ) (Set.Icc c d) θ)
    (hcontP : ∀ n, ContinuousOn (Function.uncurry (P n)) (Set.Icc a b ×ˢ Set.Icc c d))
    (hcontQ : ∀ n, ContinuousOn (Function.uncurry (Q n)) (Set.Icc a b ×ˢ Set.Icc c d))
    (hH : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      Filter.Tendsto (fun n => H n z θ) Filter.atTop (nhds (H₀ z θ)))
    (hP : TendstoUniformlyOn (fun n p => P n p.1 p.2) (fun p => P₀ p.1 p.2) Filter.atTop
      (Set.Icc a b ×ˢ Set.Icc c d))
    (hQ : TendstoUniformlyOn (fun n p => Q n p.1 p.2) (fun p => Q₀ p.1 p.2) Filter.atTop
      (Set.Icc a b ×ˢ Set.Icc c d))
    (hcontP₀ : ContinuousOn (Function.uncurry P₀) (Set.Icc a b ×ˢ Set.Icc c d))
    (hcontQ₀ : ContinuousOn (Function.uncurry Q₀) (Set.Icc a b ×ˢ Set.Icc c d)) :
    ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      HasFDerivWithinAt (Function.uncurry H₀) (Work.FTS_EllLimOK.ellCop (P₀ z θ) (Q₀ z θ))
        (Set.Icc a b ×ˢ Set.Icc c d) (z, θ) := by
  -- The proof is the staircase argument: control `H n y - H n y₀ - L (y - y₀)` by the two
  -- one-dimensional mean-value bounds on the slices, then pass to `n → ∞` using the pointwise
  -- convergence of `H n` at `y` and at `y₀`.
  -- (`hab`, `hcd` and the three continuity hypotheses `hcontH`, `hcontP`, `hcontQ` are part of the
  -- requested interface but are not needed by this argument: the slice bounds only use `hsz`,
  -- `hth` and the two uniform-convergence hypotheses.)
  intro z hz θ hθ
  rw [hasFDerivWithinAt_iff_isLittleO]
  rw [Asymptotics.isLittleO_iff]
  intro k hk
  -- Uniform continuity of the two limits on the compact box.
  have hPuc : UniformContinuousOn (fun p : ℝ × ℝ => P₀ p.1 p.2) (Set.Icc a b ×ˢ Set.Icc c d) :=
    (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hcontP₀
  have hQuc : UniformContinuousOn (fun p : ℝ × ℝ => Q₀ p.1 p.2) (Set.Icc a b ×ˢ Set.Icc c d) :=
    (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hcontQ₀
  obtain ⟨δP, hδPpos, hδP⟩ := Metric.uniformContinuousOn_iff.1 hPuc (k/4) (by linarith)
  obtain ⟨δQ, hδQpos, hδQ⟩ := Metric.uniformContinuousOn_iff.1 hQuc (k/4) (by linarith)
  have hy0 : (z, θ) ∈ Set.Icc a b ×ˢ Set.Icc c d := ⟨hz, hθ⟩
  have hcloseP : ∀ p ∈ Set.Icc a b ×ˢ Set.Icc c d, dist p (z,θ) < min δP δQ →
      |P₀ p.1 p.2 - P₀ z θ| < k/4 := by
    intro p hp hpd
    have h := hδP p hp (z,θ) hy0 (lt_of_lt_of_le hpd (min_le_left _ _))
    rwa [Real.dist_eq] at h
  have hcloseQ : ∀ p ∈ Set.Icc a b ×ˢ Set.Icc c d, dist p (z,θ) < min δP δQ →
      |Q₀ p.1 p.2 - Q₀ z θ| < k/4 := by
    intro p hp hpd
    have h := hδQ p hp (z,θ) hy0 (lt_of_lt_of_le hpd (min_le_right _ _))
    rwa [Real.dist_eq] at h
  -- Uniform convergence of the two partials.
  have hPunif : ∀ᶠ n in Filter.atTop, ∀ p ∈ Set.Icc a b ×ˢ Set.Icc c d,
      dist (P₀ p.1 p.2) (P n p.1 p.2) < k/4 :=
    Metric.tendstoUniformlyOn_iff.1 hP (k/4) (by linarith)
  have hQunif : ∀ᶠ n in Filter.atTop, ∀ p ∈ Set.Icc a b ×ˢ Set.Icc c d,
      dist (Q₀ p.1 p.2) (Q n p.1 p.2) < k/4 :=
    Metric.tendstoUniformlyOn_iff.1 hQ (k/4) (by linarith)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
  refine ⟨min δP δQ, lt_min hδPpos hδQpos, fun y hy hys => ?_⟩
  obtain ⟨z', θ'⟩ := y
  have hzs : z' ∈ Set.Icc a b := hys.1
  have hθs : θ' ∈ Set.Icc c d := hys.2
  have hz'm : |z' - z| ≤ dist (z',θ') (z,θ) := by
    rw [dist_prod_eq_max']; exact le_max_left _ _
  have hθ'm : |θ' - θ| ≤ dist (z',θ') (z,θ) := by
    rw [dist_prod_eq_max']; exact le_max_right _ _
  have hzero : |θ - θ| ≤ dist (z',θ') (z,θ) := by simp [dist_nonneg]
  -- The staircase bound for each `n` in the (eventual) good range.
  have hbd : ∀ᶠ n in Filter.atTop,
      ‖H n z' θ' - H n z θ - ((z' - z) * P₀ z θ + (θ' - θ) * Q₀ z θ)‖
        ≤ k * dist (z',θ') (z,θ) := by
    filter_upwards [hPunif, hQunif] with n hPn hQn
    -- first variable, angle fixed at `θ`
    have hs1 : |H n z' θ - H n z θ - (z' - z) * P₀ z θ| ≤ (k/2) * |z' - z| := by
      refine abs_sub_mul_le_of_derivWithin_bound (α := a) (β := b) (c := P₀ z θ) (C := k/2)
        (u := fun t => H n t θ) (u' := fun t => P n t θ) (x := z) (y := z')
        (fun t ht => hsz n t ht θ hθ) hz hzs (fun t ht => ?_)
      have htI : t ∈ Set.Icc a b := uIcc_subset_Icc hz hzs ht
      have htd : dist (t, θ) (z, θ) < min δP δQ :=
        lt_of_le_of_lt
          (dist_prod_le_of _ _ (le_trans (abs_sub_left_le_abs_sub_of_mem_uIcc ht) hz'm) hzero) hy
      have h1 : |P₀ t θ - P₀ z θ| < k/4 := hcloseP (t,θ) ⟨htI, hθ⟩ htd
      have h2 : |P n t θ - P₀ t θ| < k/4 := by
        have hh := hPn (t,θ) ⟨htI, hθ⟩
        simpa only [Real.dist_eq, abs_sub_comm] using hh
      have h3 : |P n t θ - P₀ z θ| ≤ |P n t θ - P₀ t θ| + |P₀ t θ - P₀ z θ| := by
        rw [show P n t θ - P₀ z θ = (P n t θ - P₀ t θ) + (P₀ t θ - P₀ z θ) from by ring]
        exact abs_add_le _ _
      linarith
    -- second variable, first coordinate fixed at `z'`
    have hs2 : |H n z' θ' - H n z' θ - (θ' - θ) * Q₀ z θ| ≤ (k/2) * |θ' - θ| := by
      refine abs_sub_mul_le_of_derivWithin_bound (α := c) (β := d) (c := Q₀ z θ) (C := k/2)
        (u := fun t => H n z' t) (u' := fun t => Q n z' t) (x := θ) (y := θ')
        (fun t ht => hth n z' hzs t ht) hθ hθs (fun t ht => ?_)
      have htI : t ∈ Set.Icc c d := uIcc_subset_Icc hθ hθs ht
      have htd : dist (z', t) (z, θ) < min δP δQ :=
        lt_of_le_of_lt
          (dist_prod_le_of _ _ hz'm (le_trans (abs_sub_left_le_abs_sub_of_mem_uIcc ht) hθ'm)) hy
      have h1 : |Q₀ z' t - Q₀ z θ| < k/4 := hcloseQ (z',t) ⟨hzs, htI⟩ htd
      have h2 : |Q n z' t - Q₀ z' t| < k/4 := by
        have hh := hQn (z',t) ⟨hzs, htI⟩
        simpa only [Real.dist_eq, abs_sub_comm] using hh
      have h3 : |Q n z' t - Q₀ z θ| ≤ |Q n z' t - Q₀ z' t| + |Q₀ z' t - Q₀ z θ| := by
        rw [show Q n z' t - Q₀ z θ = (Q n z' t - Q₀ z' t) + (Q₀ z' t - Q₀ z θ) from by ring]
        exact abs_add_le _ _
      linarith
    have hsplit : H n z' θ' - H n z θ - ((z' - z) * P₀ z θ + (θ' - θ) * Q₀ z θ)
        = (H n z' θ' - H n z' θ - (θ' - θ) * Q₀ z θ)
          + (H n z' θ - H n z θ - (z' - z) * P₀ z θ) := by ring
    rw [hsplit, Real.norm_eq_abs]
    refine le_trans (abs_add_le _ _) (le_trans (add_le_add hs2 hs1) ?_)
    nlinarith [hz'm, hθ'm, hk, abs_nonneg (z' - z), abs_nonneg (θ' - θ)]
  -- Pass to the limit in `n`, using pointwise convergence of `H n` at `y` and at `(z,θ)`.
  have hlim : Filter.Tendsto (fun n => H n z' θ' - H n z θ
      - ((z' - z) * P₀ z θ + (θ' - θ) * Q₀ z θ))
      Filter.atTop (nhds (H₀ z' θ' - H₀ z θ - ((z' - z) * P₀ z θ + (θ' - θ) * Q₀ z θ))) :=
    ((hH z' hzs θ' hθs).sub (hH z hz θ hθ)).sub tendsto_const_nhds
  have hfin := le_of_tendsto hlim.norm hbd
  simpa only [Function.uncurry, Function.uncurry_apply_pair, Real.norm_eq_abs, dist_eq_norm,
    ellCop_apply, Prod.fst_sub, Prod.snd_sub] using hfin

end Work.FTS_EllLimOK.BoxRegAux
