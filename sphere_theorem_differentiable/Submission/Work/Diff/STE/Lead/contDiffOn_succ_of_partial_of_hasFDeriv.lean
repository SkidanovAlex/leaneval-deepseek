import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedVariables false

namespace Work.Diff.STE.Lead

open Set Filter
open scoped Topology

/-- The candidate joint derivative of a function `g : ℝ × E → F` whose first partial derivative is
`A` and whose second partial derivative is `B`: it sends `v` to `v.1 • A p + B p v.2`. -/
noncomputable def partialFDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : ℝ × E → F) (B : ℝ × E → E →L[ℝ] F) (p : ℝ × E) : ℝ × E →L[ℝ] F :=
  (ContinuousLinearMap.fst ℝ ℝ E).smulRight (A p) +
    (B p).comp (ContinuousLinearMap.snd ℝ ℝ E)

lemma partialFDeriv_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : ℝ × E → F) (B : ℝ × E → E →L[ℝ] F) (p v : ℝ × E) :
    partialFDeriv A B p v = v.1 • A p + B p v.2 := by
  simp [partialFDeriv]

/-- Mean value estimate along a straight segment: if `φ` is differentiable along the segment from
`y` to `u` with derivative `φ'`, and `φ'` stays within `c` of the fixed linear map `L` on the
segment, then the first order Taylor remainder is bounded by `c ‖u - y‖`. -/
lemma norm_segment_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : E → F} {φ' : E → E →L[ℝ] F} {y u : E} {L : E →L[ℝ] F} {c : ℝ}
    (hd : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasFDerivAt φ (φ' (y + τ • (u - y))) (y + τ • (u - y)))
    (hb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖φ' (y + τ • (u - y)) - L‖ ≤ c) :
    ‖φ u - φ y - L (u - y)‖ ≤ c * ‖u - y‖ := by
  set ψ : ℝ → F := fun τ => φ (y + τ • (u - y)) - φ y - τ • (L (u - y)) with hψ
  have hderiv : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt ψ ((φ' (y + τ • (u - y)) - L) (u - y)) (Set.Icc (0 : ℝ) 1) τ := by
    intro τ hτ
    have hpath : HasDerivAt (fun τ : ℝ => y + τ • (u - y)) (u - y) τ := by
      have h1 : HasDerivAt (fun τ : ℝ => τ • (u - y)) ((1 : ℝ) • (u - y)) τ :=
        (hasDerivAt_id τ).smul_const (u - y)
      simpa using h1.const_add y
    have h2 : HasDerivAt (fun τ : ℝ => φ (y + τ • (u - y)))
        ((φ' (y + τ • (u - y))) (u - y)) τ := by
      have hh := (hd τ hτ).comp_hasDerivAt τ hpath
      simpa [Function.comp_def] using hh
    have h3 : HasDerivAt (fun τ : ℝ => τ • (L (u - y))) ((1 : ℝ) • (L (u - y))) τ :=
      (hasDerivAt_id τ).smul_const (L (u - y))
    have h4 : HasDerivAt (fun τ : ℝ => φ (y + τ • (u - y)) - φ y - τ • (L (u - y)))
        ((φ' (y + τ • (u - y))) (u - y) - (1 : ℝ) • (L (u - y))) τ := by
      have h := (h2.sub_const (φ y)).sub h3
      convert h using 1
    have h4' : HasDerivAt (fun τ : ℝ => φ (y + τ • (u - y)) - φ y - τ • (L (u - y)))
        ((φ' (y + τ • (u - y)) - L) (u - y)) τ := by
      convert h4 using 1
      simp [sub_apply, one_smul]
    rw [hψ]
    exact h4'.hasDerivWithinAt (s := Set.Icc (0 : ℝ) 1)
  have hbound : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖(φ' (y + τ • (u - y)) - L) (u - y)‖ ≤ c * ‖u - y‖ := by
    intro τ hτ
    calc ‖(φ' (y + τ • (u - y)) - L) (u - y)‖
        ≤ ‖φ' (y + τ • (u - y)) - L‖ * ‖u - y‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ c * ‖u - y‖ := mul_le_mul_of_nonneg_right (hb τ hτ) (norm_nonneg _)
  have hMVT := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
      (convex_Icc 0 1) (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
  have h1 : ψ 1 = φ u - φ y - L (u - y) := by rw [hψ]; simp
  have h0 : ψ 0 = 0 := by rw [hψ]; simp
  rw [h1, h0, sub_zero] at hMVT
  simpa using hMVT

/-
GUIDANCE (from the requester).  This is a general real-analysis lemma (no workspace vocabulary
beyond Mathlib).  In the intended application `s = Set.Ico (0 : ℝ) τ` (so `s` is a half-open
interval: the derivative in the first variable is *one-sided at the endpoint*), `t = Ω` is open,
`g (σ,y) = V σ y a b`, `A (σ,y) = ∂_w G_{ab} (σ,y)` and `B (σ,y) = ∂_c ∂_w W_{ab} (σ,y)`.

ROUTE.  Show first that the continuous linear map
`L (σ,y) : ℝ × E →L[ℝ] F := (A (σ,y)) ∘L fst + (B (σ,y)) ∘L snd`
satisfies `HasFDerivWithinAt g (L (σ,y)) (s ×ˢ t) (σ,y)` for every `(σ,y) ∈ s ×ˢ t`:
  `g (σ',y') - g (σ,y) = [g (σ',y') - g (σ,y')] + [g (σ,y') - g (σ,y)]`,
the first bracket is controlled by the `s`-derivative at `(σ,y')` (the definition of
`HasDerivWithinAt` gives the little-o along `s`; then replace `A (σ,y')` by `A (σ,y)` using the
continuity of `A`), the second by the `y`-derivative at `(σ,y)` (the `o (‖y'-y‖)` of
`HasFDerivAt`).
Then `fderivWithin ℝ g (s ×ˢ t) (σ,y) = L (σ,y)` by uniqueness of the within-derivative (`hs`),
so `ContDiffOn ℝ m (fderivWithin ℝ g (s ×ˢ t)) (s ×ˢ t)` follows from `hA`, `hB` and the (linear,
hence smooth) construction of `L` from `A` and `B`, and `contDiffOn_succ_iff_fderivWithin hs`
gives the conclusion (the extra `n = ω → AnalyticOn` clause is vacuous for `n = ↑m`,
`m : ℕ`).
-/
theorem contDiffOn_succ_of_partial_of_hasFDeriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set ℝ} {t : Set E} {g : ℝ × E → F} {A : ℝ × E → F} {B : ℝ × E → E →L[ℝ] F} {m : ℕ}
    (hs : UniqueDiffOn ℝ (s ×ˢ t)) (ht : IsOpen t)
    (hg : ContDiffOn ℝ m g (s ×ˢ t)) (hA : ContDiffOn ℝ m A (s ×ˢ t))
    (hB : ContDiffOn ℝ m B (s ×ˢ t))
    (hgd : ∀ σ ∈ s, ∀ y ∈ t, HasDerivWithinAt (fun σ' => g (σ', y)) (A (σ, y)) s σ)
    (hgy : ∀ σ ∈ s, ∀ y ∈ t, HasFDerivAt (fun y' => g (σ, y')) (B (σ, y)) y) :
    ContDiffOn ℝ (m + 1) g (s ×ˢ t) := by
  -- the candidate derivative `partialFDeriv A B` is `C^m` on the slab
  have hpf : ContDiffOn ℝ m (fun p : ℝ × E => partialFDeriv A B p) (s ×ˢ t) := by
    intro p hp
    have h1 := hA.contDiffWithinAt hp
    have h2 := hB.contDiffWithinAt hp
    simp only [partialFDeriv]
    fun_prop
  -- at every point of the slab, `partialFDeriv A B` is the within-derivative of `g`
  have hfderiv : ∀ p ∈ s ×ˢ t, HasFDerivWithinAt g (partialFDeriv A B p) (s ×ˢ t) p := by
    rintro ⟨σ, y⟩ hp
    have hσ : σ ∈ s := (Set.mem_prod.mp hp).1
    have hy : y ∈ t := (Set.mem_prod.mp hp).2
    rw [hasFDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
    intro c hc
    have hc2 : 0 < c / 2 := by linarith
    have hc2' : 0 ≤ c / 2 := le_of_lt hc2
    -- the part coming from the second variable
    have hb : ∀ᶠ q in 𝓝[s ×ˢ t] (σ, y),
        ‖g (q.1, y) - g (σ, y) - (q.1 - σ) • A (σ, y)‖ ≤ c / 2 * ‖q - (σ, y)‖ := by
      have hl := Asymptotics.isLittleO_iff.mp (hasDerivWithinAt_iff_isLittleO.mp (hgd σ hσ y hy))
      have hstep : ∀ᶠ σ' in 𝓝[s] σ,
          ‖g (σ', y) - g (σ, y) - (σ' - σ) • A (σ, y)‖ ≤ c / 2 * ‖σ' - σ‖ := hl hc2
      have htend : Tendsto Prod.fst (𝓝[s ×ˢ t] (σ, y)) (𝓝[s] σ) := by
        rw [nhdsWithin_prod_eq]
        exact Filter.tendsto_fst
      filter_upwards [htend.eventually hstep] with q hq
      calc ‖g (q.1, y) - g (σ, y) - (q.1 - σ) • A (σ, y)‖ ≤ c / 2 * ‖q.1 - σ‖ := hq
        _ ≤ c / 2 * ‖q - (σ, y)‖ :=
            mul_le_mul_of_nonneg_left (norm_fst_le (q - (σ, y) : ℝ × E)) hc2'
    -- the part coming from the first variable
    have ha : ∀ᶠ q in 𝓝[s ×ˢ t] (σ, y),
        ‖g q - g (q.1, y) - B (σ, y) (q.2 - y)‖ ≤ c / 2 * ‖q - (σ, y)‖ := by
      obtain ⟨δB, hδBpos, hδB⟩ :=
        Metric.continuousWithinAt_iff.mp ((hB.continuousOn).continuousWithinAt hp) (c / 2) hc2
      obtain ⟨δt, hδtpos, hδt⟩ := Metric.mem_nhds_iff.mp (ht.mem_nhds hy)
      set δ : ℝ := min δB δt with hδdef
      have hδpos : 0 < δ := lt_min hδBpos hδtpos
      rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
      refine ⟨δ, hδpos, fun q hq hqmem => ?_⟩
      obtain ⟨hqs, -⟩ := Set.mem_prod.mp hqmem
      have hqδ : ‖q - (σ, y)‖ < δ := by rw [← dist_eq_norm]; exact hq
      have hseg : ∀ τ ∈ Set.Icc (0 : ℝ) 1, y + τ • (q.2 - y) ∈ t := by
        intro τ hτ
        apply hδt
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg hτ.1]
        calc τ * ‖q.2 - y‖ ≤ 1 * ‖q.2 - y‖ := mul_le_mul_of_nonneg_right hτ.2 (norm_nonneg _)
          _ = ‖q.2 - y‖ := one_mul _
          _ ≤ ‖q - (σ, y)‖ := norm_snd_le (q - (σ, y) : ℝ × E)
          _ < δt := lt_of_lt_of_le (lt_of_lt_of_le hqδ (min_le_right _ _)) le_rfl
      have hbd : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖B (q.1, y + τ • (q.2 - y)) - B (σ, y)‖ ≤ c / 2 := by
        intro τ hτ
        have hdist : dist (q.1, y + τ • (q.2 - y)) (σ, y) < δB := by
          rw [Prod.dist_eq]
          refine max_lt ?_ ?_
          · rw [dist_eq_norm]
            exact lt_of_le_of_lt (norm_fst_le (q - (σ, y) : ℝ × E))
              (lt_of_lt_of_le hqδ (min_le_left _ _))
          · rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
              abs_of_nonneg hτ.1]
            calc τ * ‖q.2 - y‖ ≤ 1 * ‖q.2 - y‖ := mul_le_mul_of_nonneg_right hτ.2 (norm_nonneg _)
              _ = ‖q.2 - y‖ := one_mul _
              _ ≤ ‖q - (σ, y)‖ := norm_snd_le (q - (σ, y) : ℝ × E)
              _ < δB := lt_of_lt_of_le (lt_of_lt_of_le hqδ (min_le_left _ _)) le_rfl
        exact le_of_lt (by
          rw [← dist_eq_norm]
          exact hδB (x := (q.1, y + τ • (q.2 - y))) ⟨hqs, hseg τ hτ⟩ hdist)
      have hd : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
          HasFDerivAt (fun u' : E => g (q.1, u')) (B (q.1, y + τ • (q.2 - y)))
            (y + τ • (q.2 - y)) :=
        fun τ hτ => hgy q.1 hqs _ (hseg τ hτ)
      have hmain := norm_segment_sub_le (φ := fun u' : E => g (q.1, u'))
        (φ' := fun u' : E => B (q.1, u')) (L := B (σ, y)) (y := y) (u := q.2)
        (c := c / 2) hd hbd
      calc ‖g q - g (q.1, y) - B (σ, y) (q.2 - y)‖
          = ‖g (q.1, q.2) - g (q.1, y) - B (σ, y) (q.2 - y)‖ := rfl
        _ ≤ c / 2 * ‖q.2 - y‖ := hmain
        _ ≤ c / 2 * ‖q - (σ, y)‖ :=
            mul_le_mul_of_nonneg_left (norm_snd_le (q - (σ, y) : ℝ × E)) hc2'
    filter_upwards [ha, hb] with q ha' hb'
    rw [partialFDeriv_apply]
    calc ‖g q - g (σ, y) - ((q.1 - σ) • A (σ, y) + B (σ, y) (q.2 - y))‖
        = ‖(g q - g (q.1, y) - B (σ, y) (q.2 - y)) +
            (g (q.1, y) - g (σ, y) - (q.1 - σ) • A (σ, y))‖ := by
          congr 1
          abel
      _ ≤ ‖g q - g (q.1, y) - B (σ, y) (q.2 - y)‖ +
            ‖g (q.1, y) - g (σ, y) - (q.1 - σ) • A (σ, y)‖ := norm_add_le _ _
      _ ≤ c / 2 * ‖q - (σ, y)‖ + c / 2 * ‖q - (σ, y)‖ := add_le_add ha' hb'
      _ = c * ‖q - (σ, y)‖ := by ring
  have hcon : ∀ p ∈ s ×ˢ t, fderivWithin ℝ g (s ×ˢ t) p = partialFDeriv A B p :=
    fun p hp => (hfderiv p hp).fderivWithin (hs p hp)
  have hfdc : ContDiffOn ℝ m (fderivWithin ℝ g (s ×ˢ t)) (s ×ˢ t) :=
    hpf.congr hcon
  rw [contDiffOn_succ_iff_fderivWithin hs]
  exact ⟨fun p hp => (hfderiv p hp).differentiableWithinAt, fun h => absurd h (by simp), hfdc⟩

end Work.Diff.STE.Lead
