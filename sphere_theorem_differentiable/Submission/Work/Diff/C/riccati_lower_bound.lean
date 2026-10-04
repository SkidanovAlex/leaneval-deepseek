import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Topology

/-!
# The Riccati lower bound for the differentiable sphere theorem

A "Riccati comparison" lemma: if `H` is differentiable on `(0,T)` with derivative `h`, if
`g > 0` there and the Riccati-type inequality `H² ≤ h · g` holds, and if moreover `g` vanishes
at least quadratically at the origin (`g t ≤ C t²` for `t ∈ (0,δ)`), then `H ≥ 0` on `(0,T)`.

The proof analyses the negativity set of `H`.  If `H t₀ < 0`, let `A` be the set of `s > 0` with
`H < 0` on `(s,t₀)` and put `a = sInf A`.  On `(a,t₀)` one has `H < 0`, hence `h ≥ H²/g > 0`, so
`H` is strictly increasing there.

* If `a > 0` then `H a = 0` by continuity, and strict increase together with `H < 0` on `(a,t₀)`
  is impossible (`riccati_endpoint_blowup`).
* If `a = 0` then `H < 0` on all of `(0,t₀)`; writing `φ = -1/H > 0` we get `φ' ≥ 1/(Ct²)`, whence
  `t ↦ φ t + 1/(Ct)` is monotone on `(0,δ)` while `φ ≥ 0` — evaluating at a small `s` and letting
  `s → 0⁺` gives a contradiction (`riccati_no_neg_prefix`).

This is the a-priori sign estimate used (in the Brendle–Schoen / Hamilton maximum principle
arguments) to compare solutions of the Riccati equation with the model solution on the sphere.
-/

namespace Work.Diff.C

/-- **Endpoint blow-up.**  A function that is strictly increasing on `(a,b)`, continuous at `a`
with `f a = 0`, and strictly negative on `(a,b)`, cannot exist: monotonicity would force
`0 ≤ f x` for `x` just to the right of `a`. -/
private theorem riccati_endpoint_blowup_aux {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hmono : StrictMonoOn f (Set.Ioo a b))
    (hfa : f a = 0) (hcont : ContinuousAt f a)
    (hneg : ∀ x ∈ Set.Ioo a b, f x < 0) : False := by
  obtain ⟨t, hat, htb⟩ : ∃ t : ℝ, a < t ∧ t < b := ⟨(a + b) / 2, by linarith, by linarith⟩
  have hft : f t < 0 := hneg t ⟨hat, htb⟩
  have hlim : Filter.Tendsto f (𝓝[>] a) (𝓝 0) := by
    have h := hcont.tendsto
    rw [hfa] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ x in (𝓝[>] a), f t < f x := (tendsto_order.1 hlim).1 (f t) hft
  have hI : Set.Ioo a t ∈ 𝓝[>] a := by
    rw [← Set.Ioi_inter_Iio]
    exact Filter.inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds hat))
  obtain ⟨x, hxt, hfx⟩ := Filter.nonempty_of_mem (Filter.inter_mem hI hev)
  have hfx' : f t < f x := hfx
  have h1 : x ∈ Set.Ioo a b := ⟨hxt.1, lt_trans hxt.2 htb⟩
  have h2 : t ∈ Set.Ioo a b := ⟨hat, htb⟩
  linarith [hmono h1 h2 hxt.2, hfx']

/-- **No negative prefix at the origin.**  If `H < 0` on all of `(0,T)`, with derivative `h`
satisfying the Riccati inequality `H² ≤ h·g`, where `0 < g ≤ C t²` on `(0,T)` with `C > 0`, then
we obtain a contradiction from the blow-up of `φ = -1/H` as `t → 0⁺`. -/
private theorem riccati_no_neg_prefix_aux {H h g : ℝ → ℝ} {C T : ℝ} (hT : 0 < T) (hC : 0 < C)
    (hd : ∀ t ∈ Set.Ioo 0 T, HasDerivAt H (h t) t)
    (hgpos : ∀ t ∈ Set.Ioo 0 T, 0 < g t)
    (hineq : ∀ t ∈ Set.Ioo 0 T, (H t) ^ 2 ≤ h t * g t)
    (hg : ∀ t ∈ Set.Ioo 0 T, g t ≤ C * t ^ 2)
    (hneg : ∀ t ∈ Set.Ioo 0 T, H t < 0) : False := by
  have hHne : ∀ t ∈ Set.Ioo 0 T, H t ≠ 0 := fun t ht => ne_of_lt (hneg t ht)
  -- derivative of `φ = -1/H`
  have hphi : ∀ t ∈ Set.Ioo 0 T, HasDerivAt (fun s => -(H s)⁻¹) (h t / (H t) ^ 2) t := by
    intro t ht
    have h2 := ((hd t ht).inv (hHne t ht)).neg
    convert h2 using 1 <;> ring
  -- `φ' = h/H² ≥ 1/(C t²)`
  have hbound : ∀ t ∈ Set.Ioo 0 T, C / (C * t) ^ 2 ≤ h t / (H t) ^ 2 := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have hgt : 0 < g t := hgpos t ht
    have hCt2 : 0 < C * t ^ 2 := mul_pos hC (pow_pos ht0 2)
    have hH2 : 0 < (H t) ^ 2 := sq_pos_of_ne_zero (ne_of_lt (hneg t ht))
    have hge : (H t) ^ 2 / (C * t ^ 2) ≤ h t := by
      have h1 : (H t) ^ 2 / g t ≤ h t := (div_le_iff₀ hgt).mpr (by linarith [hineq t ht])
      have h2 : (H t) ^ 2 / (C * t ^ 2) ≤ (H t) ^ 2 / g t := by
        rw [div_le_div_iff₀ hCt2 hgt]
        exact mul_le_mul_of_nonneg_left (hg t ht) (le_of_lt hH2)
      linarith
    have hconv : C / (C * t) ^ 2 = 1 / (C * t ^ 2) := by
      field_simp
    rw [hconv, le_div_iff₀ hH2]
    have : (1 / (C * t ^ 2)) * (H t) ^ 2 = (H t) ^ 2 / (C * t ^ 2) := by ring
    rw [this]
    exact hge
  -- `G t = -1/H t + 1/(C t)` is monotone on `(0,T)`
  let G : ℝ → ℝ := fun s => -(H s)⁻¹ + (C * s)⁻¹
  have hGder : ∀ t ∈ Set.Ioo 0 T, HasDerivAt G (h t / (H t) ^ 2 - C / (C * t) ^ 2) t := by
    intro t ht
    have hlin : HasDerivAt (fun s : ℝ => C * s) C t := by
      simpa using (hasDerivAt_id t).const_mul C
    have hinv : HasDerivAt (fun s : ℝ => (C * s)⁻¹) (-C / (C * t) ^ 2) t :=
      hlin.inv (ne_of_gt (mul_pos hC ht.1))
    have hsum := (hphi t ht).add hinv
    convert hsum using 1 <;> ring
  have hGmono : MonotoneOn G (Set.Ioo 0 T) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioo 0 T) ?_ ?_ ?_
    · intro x hx
      exact (hGder x hx).continuousAt.continuousWithinAt
    · rw [interior_Ioo]
      intro x hx
      exact (hGder x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Ioo]
      intro x hx
      rw [(hGder x hx).deriv]
      linarith [hbound x hx]
  set t : ℝ := T / 2 with htdef
  have htT : t ∈ Set.Ioo 0 T := ⟨by rw [htdef]; linarith, by rw [htdef]; linarith⟩
  -- for `s` near `0⁺`:  `1/(Cs) ≤ G t`
  have hle : ∀ᶠ s in (𝓝[>] (0:ℝ)), (C * s)⁻¹ ≤ G t := by
    have hIio : Set.Iio t ∈ 𝓝[>] (0:ℝ) :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by rw [htdef]; linarith))
    filter_upwards [self_mem_nhdsWithin, hIio] with s hs0 hst
    have hs0' : 0 < s := hs0
    have hst' : s < t := hst
    have hstT : s < T := by rw [htdef] at hst'; linarith
    have hsT : s ∈ Set.Ioo 0 T := ⟨hs0', hstT⟩
    have hm := hGmono hsT htT (le_of_lt hst')
    have hnonneg : 0 ≤ -(H s)⁻¹ := by
      rw [neg_nonneg]
      exact le_of_lt (inv_neg''.mpr (hneg s hsT))
    have hGs : (C * s)⁻¹ ≤ G s := by
      change (C * s)⁻¹ ≤ -(H s)⁻¹ + (C * s)⁻¹
      linarith
    exact le_trans hGs hm
  -- but `1/(Cs) → +∞`
  have htop : ∀ᶠ s in (𝓝[>] (0:ℝ)), G t + 1 ≤ (C * s)⁻¹ := by
    have hCs : Filter.Tendsto (fun s : ℝ => C * s) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have hc : Continuous fun s : ℝ => C * s := continuous_const.mul continuous_id
        have h2 := hc.continuousAt (x := 0) |>.tendsto
        simp only [mul_zero] at h2
        exact h2.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        exact mul_pos hC hs
    have hmain : Filter.Tendsto (fun s : ℝ => (C * s)⁻¹) (𝓝[>] (0:ℝ)) Filter.atTop := by
      simpa [Function.comp_def] using tendsto_inv_nhdsGT_zero.comp hCs
    exact Filter.tendsto_atTop.mp hmain (G t + 1)
  obtain ⟨s, hs1, hs2⟩ := Filter.Eventually.exists (hle.and htop)
  linarith

/-- **Riccati lower bound.**  See the module docstring. -/
theorem riccati_lower_bound {H h g : ℝ → ℝ} {T C δ : ℝ} (hT : 0 < T)
    (hd : ∀ t ∈ Set.Ioo 0 T, HasDerivAt H (h t) t)
    (hgpos : ∀ t ∈ Set.Ioo 0 T, 0 < g t)
    (hineq : ∀ t ∈ Set.Ioo 0 T, (H t) ^ 2 ≤ h t * g t)
    (hC : 0 < C) (hδ : 0 < δ)
    (hg : ∀ t ∈ Set.Ioo 0 δ, g t ≤ C * t ^ 2) :
    ∀ t ∈ Set.Ioo 0 T, 0 ≤ H t := by
  intro t0 ht0
  by_contra hcon
  have ht0neg : H t0 < 0 := not_le.mp hcon
  set A : Set ℝ := {s | 0 < s ∧ s < t0 ∧ ∀ r ∈ Set.Ioo s t0, H r < 0} with hA
  have hbdd : BddBelow A := ⟨0, by rintro b hb; rw [hA] at hb; exact le_of_lt hb.1⟩
  have hAne : A.Nonempty := by
    have hcont : ContinuousAt H t0 := (hd t0 ht0).continuousAt
    have hnhds : {r : ℝ | H r < 0} ∈ 𝓝 t0 :=
      hcont.preimage_mem_nhds (IsOpen.mem_nhds isOpen_Iio ht0neg)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
    refine ⟨t0 - min (ε / 2) (t0 / 2), ?_⟩
    rw [hA]
    have ht0pos : 0 < t0 := ht0.1
    have hminpos : 0 < min (ε / 2) (t0 / 2) := lt_min (by linarith) (by linarith)
    have hminle_t : min (ε / 2) (t0 / 2) ≤ t0 / 2 := min_le_right _ _
    have hminle_e : min (ε / 2) (t0 / 2) ≤ ε / 2 := min_le_left _ _
    refine ⟨by linarith, by linarith, ?_⟩
    intro r hr
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (by linarith [hr.2])]
    linarith [hr.1]
  set a : ℝ := sInf A with ha
  have ha0 : 0 ≤ a := by
    rw [ha]
    refine le_csInf hAne ?_
    rintro b hb
    rw [hA] at hb
    exact le_of_lt hb.1
  have hat : a < t0 := by
    obtain ⟨s, hsA⟩ := hAne
    have hs : s < t0 := by
      have h := hsA; rw [hA] at h; exact h.2.1
    have hle : sInf A ≤ s := csInf_le hbdd hsA
    rw [ha]
    linarith
  have hneg_ai : ∀ r ∈ Set.Ioo a t0, H r < 0 := by
    intro r hr
    rw [ha] at hr
    obtain ⟨s, hsA, hsr⟩ := exists_lt_of_csInf_lt hAne hr.1
    have hs : s ∈ A := hsA
    rw [hA] at hs
    exact hs.2.2 r ⟨hsr, hr.2⟩
  rcases eq_or_lt_of_le ha0 with h0a | hapos
  · -- the negativity region reaches `0`
    have hT' : 0 < min t0 δ := lt_min ht0.1 hδ
    have hneg' : ∀ t ∈ Set.Ioo 0 (min t0 δ), H t < 0 := by
      intro t ht
      exact hneg_ai t ⟨by rw [← h0a]; exact ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
    refine riccati_no_neg_prefix_aux (H := H) (h := h) (g := g) hT' hC ?_ ?_ ?_ ?_ hneg'
    · intro t ht
      exact hd t ⟨ht.1, lt_of_lt_of_le ht.2 (le_trans (min_le_left _ _) (le_of_lt ht0.2))⟩
    · intro t ht
      exact hgpos t ⟨ht.1, lt_of_lt_of_le ht.2 (le_trans (min_le_left _ _) (le_of_lt ht0.2))⟩
    · intro t ht
      exact hineq t ⟨ht.1, lt_of_lt_of_le ht.2 (le_trans (min_le_left _ _) (le_of_lt ht0.2))⟩
    · intro t ht
      exact hg t ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_right _ _)⟩
  · -- the negativity region starts at `a > 0`, where `H a = 0`
    have ha_mem : a ∈ Set.Ioo 0 T := ⟨hapos, lt_trans hat ht0.2⟩
    have hcont : ContinuousAt H a := (hd a ha_mem).continuousAt
    have hha_le : H a ≤ 0 := by
      have hlim0 : Filter.Tendsto H (𝓝[>] a) (𝓝 (H a)) :=
        hcont.tendsto.mono_left nhdsWithin_le_nhds
      refine le_of_tendsto hlim0 ?_
      have hI : Set.Ioo a t0 ∈ 𝓝[>] a := by
        rw [← Set.Ioi_inter_Iio]
        exact Filter.inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds hat))
      filter_upwards [hI] with r hr
      exact le_of_lt (hneg_ai r hr)
    have hha_ge : 0 ≤ H a := by
      by_contra hcon2
      have haneg : H a < 0 := not_le.mp hcon2
      have hnhds : {r : ℝ | H r < 0} ∈ 𝓝 a :=
        hcont.preimage_mem_nhds (IsOpen.mem_nhds isOpen_Iio haneg)
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
      set η : ℝ := min (ε / 2) (a / 2) with hηdef
      have hηpos : 0 < η := by rw [hηdef]; exact lt_min (by linarith) (by linarith)
      have hηa : η ≤ a / 2 := by rw [hηdef]; exact min_le_right _ _
      have hηε : η ≤ ε / 2 := by rw [hηdef]; exact min_le_left _ _
      have hsA : a - η ∈ A := by
        rw [hA]
        refine ⟨by linarith, by linarith, ?_⟩
        intro r hr
        rcases le_or_gt r a with hra | hra
        · apply hball
          rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (by linarith)]
          linarith [hr.1]
        · exact hneg_ai r ⟨hra, hr.2⟩
      have hcontra : sInf A ≤ a - η := csInf_le hbdd hsA
      rw [ha] at hcontra
      linarith
    have hHa : H a = 0 := le_antisymm hha_le hha_ge
    have hderpos : ∀ x ∈ Set.Ioo a t0, 0 < deriv H x := by
      intro x hx
      have hxT : x ∈ Set.Ioo 0 T := ⟨lt_trans hapos hx.1, lt_trans hx.2 ht0.2⟩
      rw [(hd x hxT).deriv]
      have hHx : H x < 0 := hneg_ai x hx
      have hH2 : 0 < (H x) ^ 2 := sq_pos_of_ne_zero (ne_of_lt hHx)
      have hmul : 0 < h x * g x := lt_of_lt_of_le hH2 (hineq x hxT)
      have hmul' : 0 < g x * h x := by simpa [mul_comm] using hmul
      exact pos_of_mul_pos_right hmul' (le_of_lt (hgpos x hxT))
    have hmonoH : StrictMonoOn H (Set.Ioo a t0) := by
      refine strictMonoOn_of_deriv_pos (convex_Ioo a t0) ?_ ?_
      · intro x hx
        exact ((hd x ⟨lt_trans hapos hx.1, lt_trans hx.2 ht0.2⟩).continuousAt).continuousWithinAt
      · rw [interior_Ioo]
        exact hderpos
    exact riccati_endpoint_blowup_aux hat hmonoH hHa hcont hneg_ai

end Work.Diff.C
