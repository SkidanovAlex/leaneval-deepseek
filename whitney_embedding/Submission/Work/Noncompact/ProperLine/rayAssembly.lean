import Mathlib
import Submission.Work.Noncompact.ProperLine.TameTipDefs

/-!
# Assembling a smooth proper ray from a sequence of pieces

This file contains the "endgame" of the ray construction: given a sequence of smooth arcs
`γ i : ℝ → M` (the *pieces*) which

* live in `C`, start at `b` and match at the junctions (`γ (i+1) 0 = γ i 1`),
* meet only at the junctions (`γ i '' [0,1] ∩ γ j '' [0,1] ⊆ {γ i 1}` for `i < j`),
* eventually avoid every compact exhaustion level (`γ i '' [0,1] ∩ K n = ∅` for `i ≥ I n`),

we assemble the ray
`r t = b` for `t ≤ 0` and `r t = γ (⌊t⌋₊) (ψ (t - ⌊t⌋₊))` for `t ≥ 0`,
where `ψ = Real.smoothTransition` is flat at `0` and `1`.  The flatness makes `r` smooth at the
junctions, the separation makes it injective on `[0,∞)`, and the depth condition makes it proper.
-/

namespace Work.Noncompact.ProperLine

open Set Topology Filter
open scoped Manifold

section Transition

/-- `Real.smoothTransition` is strictly increasing on `[0,1]`, hence injective there. -/
theorem smoothTransition_strict {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) (hy : y ≤ 1) :
    Real.smoothTransition x < Real.smoothTransition y := by
  have hy0 : 0 < y := lt_of_le_of_lt hx hxy
  rcases eq_or_lt_of_le hx with h0 | hx0
  · rw [← h0, Real.smoothTransition.zero]
    exact div_pos (expNegInvGlue.pos_of_pos hy0)
      (add_pos_of_pos_of_nonneg (expNegInvGlue.pos_of_pos hy0) (expNegInvGlue.nonneg _))
  · rcases eq_or_lt_of_le hy with h1 | hy1
    · rw [h1, Real.smoothTransition.one]
      exact Real.smoothTransition.lt_one_of_lt_one (lt_of_lt_of_le hxy hy)
    · -- the main algebraic estimate
      have hx1 : x < 1 := lt_trans hxy hy1
      have h1x : 0 < 1 - x := by linarith
      have h1y : 0 < 1 - y := by linarith
      have hEx : expNegInvGlue x = Real.exp (-x⁻¹) := by
        simp [expNegInvGlue, not_le.mpr hx0]
      have hEy : expNegInvGlue y = Real.exp (-y⁻¹) := by
        simp [expNegInvGlue, not_le.mpr hy0]
      have hE1x : expNegInvGlue (1 - x) = Real.exp (-(1 - x)⁻¹) := by
        simp [expNegInvGlue, not_le.mpr h1x]
      have hE1y : expNegInvGlue (1 - y) = Real.exp (-(1 - y)⁻¹) := by
        simp [expNegInvGlue, not_le.mpr h1y]
      have hd : 0 < x⁻¹ + (1 - y)⁻¹ - (y⁻¹ + (1 - x)⁻¹) := by
        have h2 : x⁻¹ + (1 - y)⁻¹ - (y⁻¹ + (1 - x)⁻¹)
            = (y - x) * ((x*y)⁻¹ + ((1-x)*(1-y))⁻¹) := by
          field_simp
          ring
        have hp : 0 < (x*y)⁻¹ + ((1-x)*(1-y))⁻¹ := by positivity
        nlinarith [h2, hp, sub_pos.mpr hxy]
      have hkey : expNegInvGlue x * expNegInvGlue (1 - y) <
          expNegInvGlue y * expNegInvGlue (1 - x) := by
        rw [hEx, hE1y, hEy, hE1x, ← Real.exp_add, ← Real.exp_add, Real.exp_lt_exp]
        linarith
      have hdx : 0 < expNegInvGlue x + expNegInvGlue (1 - x) :=
        add_pos_of_pos_of_nonneg (expNegInvGlue.pos_of_pos hx0) (expNegInvGlue.nonneg _)
      have hdy : 0 < expNegInvGlue y + expNegInvGlue (1 - y) :=
        add_pos_of_pos_of_nonneg (expNegInvGlue.pos_of_pos hy0) (expNegInvGlue.nonneg _)
      rw [Real.smoothTransition, Real.smoothTransition, div_lt_div_iff₀ hdx hdy]
      nlinarith [hkey]

theorem smoothTransition_injOn : Set.InjOn Real.smoothTransition (Set.Icc (0:ℝ) 1) := by
  intro x hx y hy h
  rcases lt_trichotomy x y with hlt | heq | hgt
  · exact absurd h (ne_of_lt (smoothTransition_strict hx.1 hlt hy.2))
  · exact heq
  · exact absurd h.symm (ne_of_lt (smoothTransition_strict hy.1 hgt hx.2))

end Transition

section Glue

/-- **Gluing two smooth arcs at a point, with an agreement hypothesis.**

If `F` is constant equal to `p` on `(-∞,0]` and `G` is constant equal to `p` on `[0,∞)`, then the
glued map `u ↦ if u ≤ 0 then G u else F u` is smooth at `0`.  (The values away from `0` are
irrelevant.)  The proof works in a chart at `p`: there the sum `e (F u) + e (G u) - e p` is a
smooth function agreeing with the glued map on both sides of `0`. -/
theorem contMDiffAt_glue {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {F G : ℝ → M} {p : M}
    (hF : ContMDiff 𝓘(ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((⊤:ℕ∞):WithTop ℕ∞) F)
    (hG : ContMDiff 𝓘(ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((⊤:ℕ∞):WithTop ℕ∞) G)
    (hFp : ∀ u ≤ 0, F u = p) (hGp : ∀ u ≥ 0, G u = p) :
    ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((⊤:ℕ∞):WithTop ℕ∞)
      (fun u => if u ≤ 0 then G u else F u) 0 := by
  set H : ℝ → M := fun u => if u ≤ 0 then G u else F u with hH
  set I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) with hI
  set e : PartialEquiv M (EuclideanSpace ℝ (Fin n)) := extChartAt I p with he
  set a : ℝ → EuclideanSpace ℝ (Fin n) := fun u => e (F u) + e (G u) - e p with ha
  have hF0 : F 0 = p := hFp 0 le_rfl
  have hG0 : G 0 = p := hGp 0 le_rfl
  have hH0 : H 0 = p := by rw [hH]; simp only; rw [if_pos le_rfl, hG0]
  have hsrc : e.source ∈ 𝓝 p := by rw [he, hI]; exact extChartAt_source_mem_nhds p
  have hFev : ∀ᶠ u in 𝓝 (0:ℝ), F u ∈ e.source := by
    have h2 : e.source ∈ 𝓝 (F 0) := by rw [hF0]; exact hsrc
    exact Tendsto.eventually hF.continuous.continuousAt h2
  have hGev : ∀ᶠ u in 𝓝 (0:ℝ), G u ∈ e.source := by
    have h2 : e.source ∈ 𝓝 (G 0) := by rw [hG0]; exact hsrc
    exact Tendsto.eventually hG.continuous.continuousAt h2
  have ha_sm : ContDiffAt ℝ ((⊤:ℕ∞):WithTop ℕ∞) a 0 := by
    have h1 : ContMDiffAt 𝓘(ℝ) I ((⊤:ℕ∞):WithTop ℕ∞) (fun u => e (F u)) 0 := by
      refine ContMDiffAt.comp 0 ?_ hF.contMDiffAt
      rw [hF0, he, hI]
      exact contMDiffAt_extChartAt (I := I) (x := p)
    have h2 : ContMDiffAt 𝓘(ℝ) I ((⊤:ℕ∞):WithTop ℕ∞) (fun u => e (G u)) 0 := by
      refine ContMDiffAt.comp 0 ?_ hG.contMDiffAt
      rw [hG0, he, hI]
      exact contMDiffAt_extChartAt (I := I) (x := p)
    have h3 : ContDiffAt ℝ ((⊤:ℕ∞):WithTop ℕ∞)
        (fun u => e (F u) + e (G u) - e p) 0 :=
      (h1.contDiffAt.add h2.contDiffAt).sub contDiffAt_const
    rw [ha]; exact h3
  have hpoint : ∀ u, e (H u) = a u := by
    intro u
    by_cases h : u ≤ 0
    · rw [hH]; simp only
      rw [if_pos h]
      rw [ha]; simp only
      rw [hFp u h]; abel
    · rw [hH]; simp only
      rw [if_neg h]
      rw [ha]; simp only
      rw [hGp u (not_le.mp h).le]; abel
  have hcont_symm : ContinuousAt (fun y => e.symm y) (a 0) := by
    have ha0 : a 0 = e p := by rw [ha]; simp only; rw [hF0, hG0]; abel
    rw [ha0, he, hI]
    exact continuousAt_extChartAt_symm p
  have hev : H =ᶠ[𝓝 (0:ℝ)] (fun u => e.symm (a u)) := by
    filter_upwards [hFev, hGev] with u hFu hGu
    by_cases h : u ≤ 0
    · rw [hH]; simp only
      rw [if_pos h]
      change G u = e.symm (e (F u) + e (G u) - e p)
      rw [hFp u h, add_sub_cancel_left]
      exact (PartialEquiv.left_inv e hGu).symm
    · rw [hH]; simp only
      rw [if_neg h]
      change F u = e.symm (e (F u) + e (G u) - e p)
      rw [hGp u (not_le.mp h).le, add_sub_cancel_right]
      exact (PartialEquiv.left_inv e hFu).symm
  have hcont : ContinuousAt H 0 :=
    (hcont_symm.comp ha_sm.continuousAt).congr hev.symm
  rw [contMDiffAt_iff_target]
  refine ⟨hcont, ?_⟩
  rw [hH0]
  have hmain : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((⊤:ℕ∞):WithTop ℕ∞) a 0 :=
    ha_sm.contMDiffAt
  exact hmain.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => hpoint u)

end Glue



end Work.Noncompact.ProperLine
