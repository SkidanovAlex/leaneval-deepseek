import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Noncompact.CompressionTube.immersedArcWithGerm
import Submission.Work.Noncompact.CompressionTube.germGlue

/-!
# Gluing two opposite rays into a proper immersed line (one-sided hypotheses)

This is `Work.Noncompact.CompressionTube.exists_line_of_twoRays` with the hypotheses weakened from
*global* injectivity of the two rays to injectivity on `[0,∞)` only, and with the range conclusion
tightened to `r '' Ici 0 ∪ r' '' Ici 0`.  The rays `r`, `r'` are still given as maps on `ℝ`, but
only their behaviour on `[0,∞)` is used: the glued curve

`γ t = r' (1 - t)` for `t ≤ 1`,  `γ t = r (t - 1)` for `t ≥ 1`

reads `r` at `t - 1 ≥ 0` and `r'` at `1 - t ≥ 0`.  Near `t = 1` it *is* the straight chart line
`t ↦ c.symm (c b + (t - 1) • w)`, so it is `C^∞` and an immersion there
(`contMDiffAt_glue_same_germ`); this is the form in which the two-lane construction of the
corridor chain delivers the two rays.
-/

namespace Work.Noncompact.CompressionTube

open Set Topology Function
open scoped ContDiff _root_.Topology

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (MC n) smoothOrder M] [T2Space M] [SecondCountableTopology M]

/-- **Two escaping rays with opposite germs at their common base point give a proper immersed
line.**  Only the behaviour of `r`, `r'` on `[0,∞)` is used. -/
theorem line_of_two_oneSided_rays {b : M} {r r' : ℝ → M}
    (hr : ContMDiffOn MCreal (MC n) smoothOrder r (Set.Ici (0:ℝ)))
    (hr' : ContMDiffOn MCreal (MC n) smoothOrder r' (Set.Ici (0:ℝ)))
    (hrb : r 0 = b) (hr'b : r' 0 = b)
    (hrinj : Set.InjOn r (Set.Ici (0:ℝ))) (hr'inj : Set.InjOn r' (Set.Ici (0:ℝ)))
    (hmeet : ∀ x : M, x ∈ r '' Set.Ici (0:ℝ) → x ∈ r' '' Set.Ici (0:ℝ) → x = b)
    (hrp : IsProperMap (fun t : Set.Ici (0:ℝ) => r t))
    (hr'p : IsProperMap (fun t : Set.Ici (0:ℝ) => r' t))
    (himm : ∀ t : ℝ, 0 ≤ t → Function.Injective (mfderiv MCreal (MC n) r t))
    (himm' : ∀ t : ℝ, 0 ≤ t → Function.Injective (mfderiv MCreal (MC n) r' t))
    (hger : ∃ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
        (w : EuclideanSpace ℝ (Fin n)) (e : ℝ), 0 < e ∧ w ≠ 0 ∧
      c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M ∧ b ∈ c.source ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ e → r t = c.symm (c b + t • w)) ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ e → r' t = c.symm (c b + t • (-w)))) :
    ∃ γ : ℝ → M, ContMDiff MCreal (MC n) smoothOrder γ ∧ Function.Injective γ ∧
      IsProperMap γ ∧ (∀ t : ℝ, Function.Injective (mfderiv MCreal (MC n) γ t)) ∧
      γ 1 = b ∧ Set.range γ ⊆ r '' Set.Ici (0:ℝ) ∪ r' '' Set.Ici (0:ℝ) := by
  classical
  obtain ⟨c, w, e, he, hw, hc, hbc, hrg, hr'g⟩ := hger
  set γ : ℝ → M := fun t => if t ≤ 1 then r' (1 - t) else r (t - 1) with hγdef
  have hγeq : ∀ t : ℝ, γ t = (if t ≤ 1 then r' (1 - t) else r (t - 1)) := fun t => rfl
  have hγ1 : γ 1 = b := by rw [hγeq]; simp only [le_refl, if_true, sub_self]; exact hr'b
  -- the two sides agree with the straight chart line near the junction
  have hleft : ∀ u : ℝ, 1 - e ≤ u → u ≤ 1 → r' (1 - u) = c.symm (c b + (u - 1) • w) := by
    intro u h1 h2
    have h0 : (0:ℝ) ≤ 1 - u := by linarith
    have h3 : 1 - u ≤ e := by linarith
    rw [hr'g (1 - u) h0 h3]
    have : (1 - u) • (-w) = (u - 1) • w := by
      rw [smul_neg, ← neg_smul]
      congr 1
      ring
    rw [this]
  have hright : ∀ u : ℝ, 1 ≤ u → u ≤ 1 + e → r (u - 1) = c.symm (c b + (u - 1) • w) := by
    intro u h1 h2
    exact hrg (u - 1) (by linarith) (by linarith)
  -- smoothness
  have hsm : ContMDiff MCreal (MC n) smoothOrder γ := by
    intro t
    by_cases ht : t < 1
    · have heq : γ =ᶠ[𝓝 t] (fun s : ℝ => r' (1 - s)) := by
        filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
        rw [hγeq]; exact if_pos (le_of_lt hs)
      refine ((hr'.contMDiffAt (Ici_mem_nhds (by linarith : (0:ℝ) < 1 - t))).comp t
        (contMDiff_const.sub contMDiff_id).contMDiffAt).congr_of_eventuallyEq heq
    · by_cases ht1 : t = 1
      · subst ht1
        have hglue := contMDiffAt_glue_same_germ (n := n) (c := c) hc hbc (w := w)
          (A := fun s : ℝ => r' (1 - s)) (B := fun s : ℝ => r (s - 1)) (τ := 1) (δ := e) he
          (fun u h1 h2 => hleft u h1 h2) (fun u h1 h2 => hright u h1 h2)
        refine hglue.congr_of_eventuallyEq ?_
        filter_upwards with s
        rw [hγeq]
      · have ht' : 1 < t := lt_of_le_of_ne (not_lt.mp ht) (Ne.symm ht1)
        have heq : γ =ᶠ[𝓝 t] (fun s : ℝ => r (s - 1)) := by
          filter_upwards [isOpen_Ioi.mem_nhds ht'] with s hs
          rw [hγeq]; exact if_neg (not_le.mpr hs)
        refine ((hr.contMDiffAt (Ici_mem_nhds (by linarith : (0:ℝ) < t - 1))).comp t
          (contMDiff_id.sub contMDiff_const).contMDiffAt).congr_of_eventuallyEq heq
  -- injectivity
  have hinj : Function.Injective γ := by
    intro s t hst
    by_cases hs1 : s ≤ 1
    · have hm1 : (1 - s) ∈ Set.Ici (0:ℝ) := by simp only [Set.mem_Ici]; linarith
      by_cases ht1 : t ≤ 1
      · have hm2 : (1 - t) ∈ Set.Ici (0:ℝ) := by simp only [Set.mem_Ici]; linarith
        rw [hγeq, if_pos hs1, hγeq, if_pos ht1] at hst
        have := hr'inj hm1 hm2 hst
        linarith
      · exfalso
        rw [hγeq, if_pos hs1, hγeq, if_neg ht1] at hst
        have hm3 : (t - 1) ∈ Set.Ici (0:ℝ) := by simp only [Set.mem_Ici]; linarith
        have hb : r' (1 - s) = b :=
          hmeet (r' (1 - s)) ⟨t - 1, hm3, hst.symm⟩ ⟨1 - s, hm1, rfl⟩
        have h0 : (0:ℝ) ∈ Set.Ici (0:ℝ) := by simp
        have h1 : 1 - s = 0 := hr'inj hm1 h0 (by rw [hb, hr'b])
        have h2 : r (t - 1) = b := by rw [← hst, hb]
        have h3 : t - 1 = 0 := hrinj hm3 h0 (by rw [h2, hrb])
        linarith
    · have hs1' : 1 < s := lt_of_not_ge hs1
      have hm1 : (s - 1) ∈ Set.Ici (0:ℝ) := by simp only [Set.mem_Ici]; linarith
      by_cases ht1 : t ≤ 1
      · exfalso
        rw [hγeq, if_neg hs1, hγeq, if_pos ht1] at hst
        have hm2 : (1 - t) ∈ Set.Ici (0:ℝ) := by simp only [Set.mem_Ici]; linarith
        have hb : r (s - 1) = b :=
          hmeet (r (s - 1)) ⟨s - 1, hm1, rfl⟩ ⟨1 - t, hm2, hst.symm⟩
        have h0 : (0:ℝ) ∈ Set.Ici (0:ℝ) := by simp
        have h3 : s - 1 = 0 := hrinj hm1 h0 (by rw [hb, hrb])
        have h1 : r' (1 - t) = b := by rw [← hst, hb]
        have h2 : 1 - t = 0 := hr'inj hm2 h0 (by rw [h1, hr'b])
        linarith
      · have hm2 : (t - 1) ∈ Set.Ici (0:ℝ) := by simp only [Set.mem_Ici]; linarith
        rw [hγeq, if_neg hs1, hγeq, if_neg ht1] at hst
        have := hrinj hm1 hm2 hst
        linarith
  -- the straight chart line through `b` in direction `w` is a smooth immersion near `0`
  obtain ⟨ρ, hρ0, hρ⟩ := Metric.isOpen_iff.mp c.open_target (c b) (c.map_source hbc)
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hlineMem : ∀ u : ℝ, |u| < ρ / (2 * ‖w‖) → c b + u • w ∈ c.target := by
    intro u hu
    have h1 : |u| * (2 * ‖w‖) < ρ := by
      have h2 : ρ / (2 * ‖w‖) * (2 * ‖w‖) = ρ := div_mul_cancel₀ ρ (by positivity)
      nlinarith [hu, h2, hwpos]
    apply hρ
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    nlinarith [h1, hwpos]
  have hlt : (0:ℝ) < ρ / (2 * ‖w‖) := by positivity
  have h0T : (0:ℝ) ∈ Set.Ioo (-(ρ / (2 * ‖w‖))) (ρ / (2 * ‖w‖)) := ⟨by linarith [hlt], hlt⟩
  have hlineImm : Function.Injective
      (mfderiv MCreal (MC n) (fun u : ℝ => c.symm (c b + u • w)) 0) :=
    (isImmersion_chartLine c hc hbc hw (T := Set.Ioo (-(ρ / (2 * ‖w‖))) (ρ / (2 * ‖w‖)))
      isOpen_Ioo (fun u hu => hlineMem u (by rw [abs_lt]; exact hu))).2 0 h0T
  have hlineSm : ContMDiffOn MCreal (MC n) smoothOrder (fun u : ℝ => c.symm (c b + u • w))
      (Set.Ioo (-(ρ / (2 * ‖w‖))) (ρ / (2 * ‖w‖))) :=
    (isImmersion_chartLine c hc hbc hw (T := Set.Ioo (-(ρ / (2 * ‖w‖))) (ρ / (2 * ‖w‖)))
      isOpen_Ioo (fun u hu => hlineMem u (by rw [abs_lt]; exact hu))).1
  -- reparametrisation lemma for the derivative
  have hReparam : ∀ (f : ℝ → M) (a : ℝ → ℝ) (x : ℝ),
      MDifferentiableAt MCreal (MC n) f (a x) → MDifferentiableAt MCreal MCreal a x →
      Function.Injective (mfderiv MCreal MCreal a x) →
      Function.Injective (mfderiv MCreal (MC n) f (a x)) →
      Function.Injective (mfderiv MCreal (MC n) (fun s : ℝ => f (a s)) x) := by
    intro f a x hfd had hac hf
    have hL : mfderiv MCreal (MC n) (fun s : ℝ => f (a s)) x
        = (mfderiv MCreal (MC n) f (a x)).comp (mfderiv MCreal MCreal a x) := by
      rw [show (fun s : ℝ => f (a s)) = f ∘ a from rfl, mfderiv_comp x hfd had]
    rw [hL, ContinuousLinearMap.coe_comp]
    exact Function.Injective.comp hf hac
  -- immersion
  have himmγ : ∀ t : ℝ, Function.Injective (mfderiv MCreal (MC n) γ t) := by
    intro t
    by_cases ht : t < 1
    · have heq : γ =ᶠ[𝓝 t] (fun s : ℝ => r' (1 - s)) := by
        filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
        rw [hγeq]; exact if_pos (le_of_lt hs)
      rw [heq.mfderiv_eq]
      exact hReparam r' (fun s : ℝ => 1 - s) t
        ((hr'.contMDiffAt (n := ∞) (Ici_mem_nhds (by linarith : (0:ℝ) < 1 - t))).mdifferentiableAt (by simp))
        (((contMDiff_const.sub contMDiff_id).contMDiffAt (n := ∞)).mdifferentiableAt (by simp))
        (injective_mfderiv_const_sub 1 t)
        (himm' (1 - t) (by linarith))
    · by_cases ht1 : t = 1
      · subst ht1
        have heq : γ =ᶠ[𝓝 (1:ℝ)] (fun s : ℝ => c.symm (c b + (s - 1) • w)) := by
          have hδ : (0:ℝ) < min e 1 := lt_min he one_pos
          filter_upwards [isOpen_Ioo.mem_nhds (show (1:ℝ) ∈ Set.Ioo (1 - min e 1) (1 + min e 1)
            from ⟨by linarith, by linarith⟩)] with s hs
          rw [hγeq]
          by_cases hs1 : s ≤ 1
          · rw [if_pos hs1]
            exact hleft s (by have := min_le_left e 1; linarith [hs.1, this]) hs1
          · rw [if_neg hs1]
            exact hright s (le_of_lt (lt_of_not_ge hs1))
              (by have := min_le_left e 1; linarith [hs.2, this])
        rw [heq.mfderiv_eq]
        exact hReparam (fun u : ℝ => c.symm (c b + u • w)) (fun s : ℝ => s - 1) 1
          (by rw [show (1:ℝ) - 1 = 0 from by norm_num]
              exact (hlineSm.contMDiffAt (isOpen_Ioo.mem_nhds h0T)).mdifferentiableAt (by simp))
          (((contMDiff_id.sub contMDiff_const).contMDiffAt (n := ∞)).mdifferentiableAt (by simp))
          (injective_mfderiv_sub 1 1)
          (by rw [show (1:ℝ) - 1 = 0 from by norm_num]; exact hlineImm)
      · have ht' : 1 < t := lt_of_le_of_ne (not_lt.mp ht) (Ne.symm ht1)
        have heq : γ =ᶠ[𝓝 t] (fun s : ℝ => r (s - 1)) := by
          filter_upwards [isOpen_Ioi.mem_nhds ht'] with s hs
          rw [hγeq]; exact if_neg (not_le.mpr hs)
        rw [heq.mfderiv_eq]
        exact hReparam r (fun s : ℝ => s - 1) t
          ((hr.contMDiffAt (n := ∞) (Ici_mem_nhds (by linarith : (0:ℝ) < t - 1))).mdifferentiableAt (by simp))
          (((contMDiff_id.sub contMDiff_const).contMDiffAt (n := ∞)).mdifferentiableAt (by simp))
          (injective_mfderiv_sub 1 t)
          (himm (t - 1) (by linarith))
  -- properness
  have hprop : IsProperMap γ := by
    rw [isProperMap_iff_isCompact_preimage]
    refine ⟨hsm.continuous, ?_⟩
    intro K hK
    have hA : IsCompact ((fun t : Set.Ici (0:ℝ) => r t) ⁻¹' K) := hrp.isCompact_preimage hK
    have hB : IsCompact ((fun t : Set.Ici (0:ℝ) => r' t) ⁻¹' K) := hr'p.isCompact_preimage hK
    have hsub : γ ⁻¹' K ⊆
        (fun u : ℝ => 1 + u) '' (Subtype.val '' ((fun t : Set.Ici (0:ℝ) => r t) ⁻¹' K)) ∪
        (fun u : ℝ => 1 - u) '' (Subtype.val '' ((fun t : Set.Ici (0:ℝ) => r' t) ⁻¹' K)) := by
      intro t ht
      simp only [mem_preimage] at ht
      rw [hγeq] at ht
      by_cases ht1 : t ≤ 1
      · rw [if_pos ht1] at ht
        exact Or.inr ⟨1 - t, ⟨⟨1 - t, by simp only [Set.mem_Ici]; linarith⟩, by simpa using ht, rfl⟩, by ring⟩
      · rw [if_neg ht1] at ht
        exact Or.inl ⟨t - 1, ⟨⟨t - 1, by simp only [Set.mem_Ici]; linarith⟩, by simpa using ht, rfl⟩, by ring⟩
    refine IsCompact.of_isClosed_subset ?_ (hK.isClosed.preimage hsm.continuous) hsub
    exact ((hA.image continuous_subtype_val).image (continuous_const.add continuous_id)).union
      ((hB.image continuous_subtype_val).image (continuous_const.sub continuous_id))
  refine ⟨γ, hsm, hinj, hprop, himmγ, hγ1, ?_⟩
  intro y hy
  rw [Set.mem_range] at hy
  obtain ⟨t, rfl⟩ := hy
  rw [hγeq]
  by_cases ht1 : t ≤ 1
  · rw [if_pos ht1]
    exact Or.inr ⟨1 - t, by simp only [Set.mem_Ici]; linarith, rfl⟩
  · rw [if_neg ht1]
    exact Or.inl ⟨t - 1, by simp only [Set.mem_Ici]; linarith, rfl⟩

end

end Work.Noncompact.CompressionTube
