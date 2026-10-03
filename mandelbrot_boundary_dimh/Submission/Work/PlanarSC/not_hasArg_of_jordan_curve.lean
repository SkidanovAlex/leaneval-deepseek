import Mathlib
import Submission.Work.PlanarSC.Tools
import Submission.Work.PlanarSC.Defs
import Submission.Work.PlanarSC.exists_injective_sqrtCurve
import Submission.Work.PlanarSC.sqrt_preimage_preconnected_mem_zero
import Submission.Work.PlanarSC.sqrt_preimage_preconnected_of_circle
import Submission.Work.PlanarSC.not_two_preconnected_pieces_of_two_jordan
import Submission.Lib.Unif2.Commons.Topology.Connected.isPreconnected_compl_closedBall
import Submission.Lib.Unif2.Commons.Topology.Jordan.plane_separation

/-!
# The winding number of a Jordan curve about a point of its bounded region is non-zero

`Work.PlanarSC.not_hasArg_of_jordan_curve`: if `γ : C(Circle, ℂ)` is injective (a Jordan curve) and
`a ∉ range γ` lies in a *bounded* connected component of the complement of the curve, then the
`1`-periodic closed curve `t ↦ circleParam γ t - a` admits no continuous `1`-periodic argument
function: the winding number of a Jordan curve about a point of its bounded region is `±1 ≠ 0`.

## Proof

Assume `HasArg`.  Then `γ - a` has an injective continuous square root `k` (a Jordan curve with
`k ^ 2 = γ - a`, `Work.PlanarSC.exists_injective_sqrtCurve`), and `range k`, `range (-k)` are two
**disjoint** Jordan curves.  The squaring map `p w = w ^ 2 + a` maps the complement
`X = (range k ∪ range (-k))ᶜ` two-to-one onto the complement `A ⊔ B` of `range γ`; let
`P_A = p⁻¹ A`, `P_B = p⁻¹ B`, so `X = P_A ⊔ P_B`.

Both `P_A` and `P_B` are preconnected: writing `Ω_A = {w | w + a ∈ A}` (open, preconnected,
`0 ∈ Ω_A`) and `Ω_B = {w | w + a ∈ B}` (open, preconnected, `0 ∉ Ω_B`, containing a round circle
about `0` — here the *boundedness* of the component of `a` is used), the preimages
`{w | w ^ 2 ∈ Ω_A} = P_A` and `{w | w ^ 2 ∈ Ω_B} = P_B` are preconnected
(`Work.PlanarSC.sqrt_preimage_preconnected_mem_zero`,
`Work.PlanarSC.sqrt_preimage_preconnected_of_circle`).

But the complement of the union of two disjoint Jordan curves is never the union of two preconnected
pieces (`Work.PlanarSC.not_two_preconnected_pieces_of_two_jordan`).  Contradiction.
-/

namespace Work.PlanarSC

open Set Metric

noncomputable section

/-- **The winding number of a Jordan curve about a point of its bounded region is non-zero.** -/
theorem not_hasArg_of_jordan_curve {γ : C(Circle, ℂ)} (hγ : Function.Injective γ)
    {a : ℂ} (ha : a ∉ Set.range γ)
    (hbdd : Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) a)) :
    ¬ Commons.Topology.Winding.HasArg (fun t : ℝ => circleParam γ t - a) 0 := by
  intro hH
  -- a continuous injective square root of `γ - a`
  obtain ⟨k, hkinj, hksq⟩ := exists_injective_sqrtCurve hγ ha hH
  -- #### `k` and `-k` are disjoint Jordan curves
  have hkneg : Function.Injective (-k : C(Circle, ℂ)) := by
    intro u v huv
    exact hkinj (neg_injective (by simpa using huv))
  have hdisjk : Disjoint (Set.range k) (Set.range (-k : C(Circle, ℂ))) := by
    rw [Set.disjoint_left]
    intro w hwk hwnk
    obtain ⟨u, hu⟩ := hwk
    obtain ⟨v, hv⟩ := hwnk
    have hneg : k u = -(k v) := by
      have h1 : (-k : C(Circle, ℂ)) v = -(k v) := ContinuousMap.neg_apply k v
      have h2 : (-k : C(Circle, ℂ)) v = k u := by rw [hv]; exact hu.symm
      rw [h2] at h1
      exact h1
    have hγeq : γ u = γ v := by
      apply sub_left_inj.mp
      rw [← hksq u, ← hksq v]
      rw [hneg]; ring
    have huv : u = v := hγ hγeq
    have h0 : k u = 0 := by
      have h3 : (2 : ℂ) * k u = 0 := by
        have h4 := hneg
        rw [← huv] at h4
        linear_combination h4
      exact (mul_eq_zero.mp h3).resolve_left (by norm_num)
    have hγa : γ u = a := by
      have h4 : γ u - a = 0 := by rw [← hksq u, h0]; ring
      exact sub_eq_zero.mp h4
    exact ha ⟨u, hγa⟩
  -- #### the two complementary regions of the Jordan curve `γ`
  obtain ⟨A, B, hAo, hBo, hAc, hBc, hABdisj, hAb, hBunb, hABeq⟩ :=
    Commons.Topology.Jordan.plane_separation γ hγ
  have hAsub : A ⊆ (Set.range γ)ᶜ := by rw [← hABeq]; exact subset_union_left
  have hBsub : B ⊆ (Set.range γ)ᶜ := by rw [← hABeq]; exact subset_union_right
  -- `a` lies in the bounded region `A`
  have haA : a ∈ A := by
    have haAB : a ∈ A ∪ B := by rw [hABeq]; exact ha
    rcases haAB with h | h
    · exact h
    · exfalso
      have hCB : connectedComponentIn ((Set.range γ)ᶜ) a = B := by
        refine Set.Subset.antisymm ?_ (hBc.isPreconnected.subset_connectedComponentIn h hBsub)
        rcases (isPreconnected_connectedComponentIn (F := (Set.range γ)ᶜ) (x := a)).subset_or_subset
            hAo hBo hABdisj (by rw [hABeq]; exact connectedComponentIn_subset _ _) with hc | hc
        · exact absurd h ((Set.disjoint_left.mp hABdisj) (hc (mem_connectedComponentIn ha)))
        · exact hc
      rw [hCB] at hbdd
      exact hBunb hbdd
  have haB : a ∉ B := fun h => (Set.disjoint_left.mp hABdisj) haA h
  -- #### a large radius outside `γ`, hence inside the unbounded region `B`
  obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp
    (isCompact_range γ.continuous).isBounded
  obtain ⟨R₁, hR₁⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hAb
  set R : ℝ := max R₀ R₁ + 1 with hRdef
  have hR₀nonneg : 0 ≤ R₀ := by
    have h := hR₀ (Set.mem_range_self (Circle.exp 0))
    rw [Metric.mem_closedBall, dist_zero_right] at h
    exact le_trans (norm_nonneg (γ (Circle.exp 0))) h
  have hRpos : 0 < R := by rw [hRdef]; linarith [le_max_left R₀ R₁]
  have hR₀le : R₀ ≤ R := by rw [hRdef]; linarith [le_max_left R₀ R₁]
  have hR₁le : R₁ ≤ R := by rw [hRdef]; linarith [le_max_right R₀ R₁]
  have hExt_sub_compl : {z : ℂ | R < ‖z‖} ⊆ (Set.range γ)ᶜ := by
    intro z hz hzK
    simp only [Set.mem_setOf_eq] at hz
    have h1 : ‖z - 0‖ ≤ R₀ := by
      have := hR₀ hzK
      simpa [Metric.mem_closedBall, dist_eq_norm] using this
    rw [sub_zero] at h1
    linarith
  have hExt_sub_B : {z : ℂ | R < ‖z‖} ⊆ B := by
    have hpre : IsPreconnected {z : ℂ | R < ‖z‖} := by
      simpa using Commons.Topology.Connected.isPreconnected_compl_closedBall (0 : ℂ) R
    rcases IsPreconnected.subset_or_subset hAo hBo hABdisj
        (by rw [hABeq]; exact hExt_sub_compl) hpre with h | h
    · exfalso
      exact Commons.Topology.Jordan.not_isBounded_gt_norm R (hAb.subset h)
    · exact h
  -- #### the two preimage domains `Ω_A`, `Ω_B` and their preconnectedness
  have hΩAc : IsPreconnected {z : ℂ | z + a ∈ A} := by
    have heq : {z : ℂ | z + a ∈ A} = (fun z : ℂ => z - a) '' A := by
      ext w
      constructor
      · intro hw; exact ⟨w + a, hw, by ring⟩
      · rintro ⟨z, hz, rfl⟩; simpa using hz
    rw [heq]
    exact hAc.isPreconnected.image _ (continuous_id.sub continuous_const).continuousOn
  have hΩBc : IsPreconnected {z : ℂ | z + a ∈ B} := by
    have heq : {z : ℂ | z + a ∈ B} = (fun z : ℂ => z - a) '' B := by
      ext w
      constructor
      · intro hw; exact ⟨w + a, hw, by ring⟩
      · rintro ⟨z, hz, rfl⟩; simpa using hz
    rw [heq]
    exact hBc.isPreconnected.image _ (continuous_id.sub continuous_const).continuousOn
  have hPApre : IsPreconnected {w : ℂ | w ^ 2 + a ∈ A} :=
    sqrt_preimage_preconnected_mem_zero (Ω := {z : ℂ | z + a ∈ A})
      (hAo.preimage (continuous_id.add continuous_const)) hΩAc (by simpa using haA)
  have hPBpre : IsPreconnected {w : ℂ | w ^ 2 + a ∈ B} := by
    have h0B : (0 : ℂ) ∉ {z : ℂ | z + a ∈ B} := by
      simp only [Set.mem_setOf_eq, zero_add]; exact haB
    have hcircB : ∃ ρ : ℝ, 0 < ρ ∧ ∀ w : ℂ, ‖w‖ = ρ → w ∈ {z : ℂ | z + a ∈ B} := by
      refine ⟨R + ‖a‖ + 1, by linarith [hRpos, norm_nonneg a], fun w hw => ?_⟩
      simp only [Set.mem_setOf_eq]
      apply hExt_sub_B
      simp only [Set.mem_setOf_eq]
      have h1 : ‖w‖ - ‖a‖ ≤ ‖w + a‖ := by
        have := norm_sub_le (w + a) a
        simpa using this
      rw [hw] at h1
      linarith [norm_nonneg a]
    exact sqrt_preimage_preconnected_of_circle (Ω := {z : ℂ | z + a ∈ B})
      (hBo.preimage (continuous_id.add continuous_const)) hΩBc h0B hcircB
  have hPAne : ({w : ℂ | w ^ 2 + a ∈ A}).Nonempty := ⟨0, by simpa using haA⟩
  have hPBne : ({w : ℂ | w ^ 2 + a ∈ B}).Nonempty := by
    refine ⟨(((Real.sqrt (R + ‖a‖ + 1) : ℝ) : ℂ)), ?_⟩
    simp only [Set.mem_setOf_eq]
    apply hExt_sub_B
    simp only [Set.mem_setOf_eq]
    have hsq : (((Real.sqrt (R + ‖a‖ + 1) : ℝ) : ℂ)) ^ 2 = (((R + ‖a‖ + 1 : ℝ)) : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by linarith [le_of_lt hRpos, norm_nonneg a])]
    rw [hsq]
    have h2 : ‖(((R + ‖a‖ + 1 : ℝ)) : ℂ)‖ = R + ‖a‖ + 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith [le_of_lt hRpos, norm_nonneg a])]
    have h1 : ‖(((R + ‖a‖ + 1 : ℝ)) : ℂ)‖
        ≤ ‖(((R + ‖a‖ + 1 : ℝ)) : ℂ) + a‖ + ‖a‖ := by
      have := norm_sub_le ((((R + ‖a‖ + 1 : ℝ)) : ℂ) + a) a
      simpa using this
    linarith
  have hPAdisj : Disjoint {w : ℂ | w ^ 2 + a ∈ A} {w : ℂ | w ^ 2 + a ∈ B} := by
    rw [Set.disjoint_left]
    intro w h1 h2
    exact (Set.disjoint_left.mp hABdisj) h1 h2
  -- #### `X = P_A ∪ P_B`
  have hXcov : {w : ℂ | w ^ 2 + a ∈ A} ∪ {w : ℂ | w ^ 2 + a ∈ B}
      = (Set.range k ∪ Set.range (-k : C(Circle, ℂ)))ᶜ := by
    ext w
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_range, not_or,
      not_exists]
    constructor
    · rintro (h | h)
      · refine ⟨fun u hu => ?_, fun u hu => ?_⟩
        · have hw2 : w ^ 2 = γ u - a := by
            calc w ^ 2 = (k u) ^ 2 := by rw [hu]
              _ = γ u - a := hksq u
          exact hAsub h ⟨u, by rw [hw2]; ring⟩
        · have hw2 : w ^ 2 = γ u - a := by
            have h3 : w = -(k u) := ContinuousMap.neg_apply k u ▸ hu.symm
            calc w ^ 2 = (-(k u)) ^ 2 := by rw [h3]
              _ = (k u) ^ 2 := by ring
              _ = γ u - a := hksq u
          exact hAsub h ⟨u, by rw [hw2]; ring⟩
      · refine ⟨fun u hu => ?_, fun u hu => ?_⟩
        · have hw2 : w ^ 2 = γ u - a := by
            calc w ^ 2 = (k u) ^ 2 := by rw [hu]
              _ = γ u - a := hksq u
          exact hBsub h ⟨u, by rw [hw2]; ring⟩
        · have hw2 : w ^ 2 = γ u - a := by
            have h3 : w = -(k u) := ContinuousMap.neg_apply k u ▸ hu.symm
            calc w ^ 2 = (-(k u)) ^ 2 := by rw [h3]
              _ = (k u) ^ 2 := by ring
              _ = γ u - a := hksq u
          exact hBsub h ⟨u, by rw [hw2]; ring⟩
    · rintro ⟨h1, h2⟩
      have hw : ∀ u : Circle, w ^ 2 ≠ γ u - a := by
        intro u hwu
        have hsq : w ^ 2 = (k u) ^ 2 := by rw [hwu, hksq u]
        have hsplit : w = k u ∨ w = -(k u) := by
          have h3 : (w - k u) * (w + k u) = 0 := by linear_combination hsq
          rcases mul_eq_zero.mp h3 with h4 | h4
          · exact Or.inl (sub_eq_zero.mp h4)
          · exact Or.inr (by linear_combination h4)
        rcases hsplit with h | h
        · exact h1 u h.symm
        · exact h2 u (by rw [ContinuousMap.neg_apply]; exact h.symm)
      have hwA : w ^ 2 + a ∈ A ∪ B := by
        rw [hABeq, Set.mem_compl_iff, Set.mem_range]
        rintro ⟨u, hu⟩
        exact hw u (by rw [hu]; ring)
      rcases hwA with h | h
      · exact Or.inl h
      · exact Or.inr h
  -- #### contradiction
  exact not_two_preconnected_pieces_of_two_jordan k (-k) hkinj hkneg hdisjk
    ⟨{w : ℂ | w ^ 2 + a ∈ A}, {w : ℂ | w ^ 2 + a ∈ B},
      hPApre, hPBpre, hPAne, hPBne, hPAdisj, hXcov⟩

end

end Work.PlanarSC
