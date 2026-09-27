import Mathlib
import Submission.Work.Drive.TParity.Basic

/-!
# The derivative of the charted difference map of three chains

For three smooth chains `D 0, D 1, D 2 : ℝ³ → M` in a smooth `4`-manifold, the derivative of the
charted difference map `chartDiff3 p D` at a point `x` of the chart region is
`pUpCLM ∘ tan3 p D x`, where `tan3 p D x` is the chart-independent (up to change of coordinates)
difference of the three manifold derivatives.

Consequences, all needed by the mod-2 parity argument:

* `chartDiff3_surj`: the transversality hypothesis (`TripleTransverse` of the three derivatives)
  makes the charted difference map a submersion at every triple intersection point;
* `tan3_eq_zero_iff` (and hence `chartDiff3_kernel_indep`): its kernel is chart-independent;
* `chartDiff3_eq_zero_of_commonDir`: a common direction of the three derivatives is a kernel vector.
-/

namespace Work.Drive.TParity

open scoped Manifold ContDiff Topology
open Manifold Set

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

/-! ## Elementary facts about the stacking map -/

lemma pUpCLM_eq_zero_iff (z : Tgt 4 × Tgt 4) : pUpCLM z = 0 ↔ z = 0 := by
  obtain ⟨a, b⟩ := z
  rw [pUpCLM_apply, pUp_eq_zero_iff]
  simp

lemma pUpCLM_surjective : Function.Surjective pUpCLM := by
  intro w
  exact ⟨(fst8 w, snd8 w), by rw [pUpCLM_apply, pUp_fst8_snd8]⟩

lemma pUpCLM_comp_apply (T : Amb 8 →L[ℝ] (Tgt 4 × Tgt 4)) (v : Amb 8) :
    pUpCLM.comp T v = pUp (T v).1 (T v).2 := by
  simpa [ContinuousLinearMap.comp_apply] using pUpCLM_apply (T v).1 (T v).2

/-- The inverse change of coordinates: from the chart at `p` back to the chart at the point. -/
def tcInv (p : M) (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (k : Fin 3) (x : Amb 8) :
    Tgt 4 →L[ℝ] Tgt 4 :=
  tangentCoordChange (𝓡 4) p (D k (bPartC k x)) (D k (bPartC k x))

/-- The change of coordinates at the point is a left inverse of the change of coordinates from the
chart at `p`, on the chart region. -/
theorem tc_leftInverse (p : M) (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (k : Fin 3)
    {x : Amb 8} (hx : x ∈ region3 p D) :
    Function.LeftInverse (tcInv p D k x) (tc p D k x) := by
  intro v
  exact tangentCoordChange_comp_inv
    ⟨mem_extChartAt_source _, by rw [extChartAt_source]; exact hx k⟩ v

/-- The change of coordinates at the point followed by its inverse is the identity. -/
lemma tc_comp_tcInv (p : M) (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (k : Fin 3)
    {x : Amb 8} (hx : x ∈ region3 p D) (u : Tgt 4) : tc p D k x (tcInv p D k x u) = u :=
  tangentCoordChange_comp_inv
    ⟨by rw [extChartAt_source]; exact hx k, mem_extChartAt_source _⟩ u

/-- The change of coordinates at the point itself is injective (on the chart region). -/
theorem tc_injective (p : M) (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (k : Fin 3)
    {x : Amb 8} (hx : x ∈ region3 p D) : Function.Injective (tc p D k x) :=
  (tc_leftInverse p D k hx).injective

/-- The change of coordinates at the point itself is surjective. -/
theorem tc_surjective (p : M) (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (k : Fin 3)
    {x : Amb 8} (hx : x ∈ region3 p D) : Function.Surjective (tc p D k x) := by
  have h : Function.LeftInverse (tc p D k x) (tcInv p D k x) := by
    intro v
    exact tangentCoordChange_comp_inv
      ⟨by rw [extChartAt_source]; exact hx k, mem_extChartAt_source _⟩ v
  exact h.surjective

/-- At a triple intersection point the three images coincide. -/
lemma meet3_eq (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) {x : Amb 8} (hm : meet3 D x)
    (k k' : Fin 3) : D k (bPartC k x) = D k' (bPartC k' x) := by
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with h | h | h <;> subst h <;>
    rcases (show k' = 0 ∨ k' = 1 ∨ k' = 2 by omega) with h' | h' | h' <;> subst h' <;>
    first
      | rfl
      | exact hm.1
      | exact hm.2
      | exact hm.1.symm
      | exact hm.2.symm
      | exact hm.1.symm.trans hm.2
      | exact hm.2.symm.trans hm.1

/-- The change of coordinates of the three chains at a triple intersection point coincide. -/
theorem tc_eq_of_meet {p : M} {D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M} {x : Amb 8}
    (hm : meet3 D x) {k k' : Fin 3} : tc p D k x = tc p D k' x := by
  rw [tc, tc, meet3_eq D hm k k']

/-- The point `mk3 v` of the nine-box has the blocks `v k`. -/
@[simp] lemma mk3_apply_bPartC (v : Fin 3 → EuclideanSpace ℝ (Fin 3)) (k : Fin 3) :
    bPartC k (mk3 v) = v k := bPartC_mk3 k v

lemma mk3_ne_zero_iff (v : Fin 3 → EuclideanSpace ℝ (Fin 3)) :
    mk3 v ≠ 0 ↔ ∃ k j, v k j ≠ 0 := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    refine h ?_
    ext i
    obtain ⟨k, j, hk⟩ : ∃ (k j : Fin 3), Work.Drive.bIdx k j = i :=
      ⟨⟨i.val / 3, by omega⟩, ⟨i.val % 3, by omega⟩, by
        ext
        rw [Work.Drive.bIdx_val]
        have h := Nat.mod_add_div i.val 3
        omega⟩
    rw [← hk, mk3_bIdx, hc k j]
    rfl
  · rintro ⟨k, j, hj⟩ h
    exact hj (by rw [← mk3_apply_bPartC v k, h]; rfl)

/-! ## The derivative of the charted difference map -/

/-- **The derivative of `chartDiff3`** is the charted difference `tan3` of the three derivatives. -/
theorem hasFDerivAt_chartDiff3 (p : M) (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hD : ∀ k, ContMDiff (𝓡 3) (𝓡 4) Ctop (D k))
    {x : Amb 8} (hx : x ∈ region3 p D) :
    HasFDerivAt (chartDiff3 p D) (pUpCLM.comp (tan3 p D x)) x := by
  have hchain : ∀ k : Fin 3,
      HasFDerivAt (fun y : Amb 8 => (Work.Drive.chr p) (D k (bPartC k y)))
        (show Amb 8 →L[ℝ] Tgt 4 from ((tc p D k x).comp (md3 D k x)).comp (bPartC k)) x := by
    intro k
    have h0 := Work.Drive.fderiv_chart_comp_hasFDerivAt (D k) (hD k) p (hx k)
    exact h0.comp x ((bPartC k).hasFDerivAt (x := x))
  have hmain := hasFDerivAt_pUp ((hchain 0).sub (hchain 1)) ((hchain 0).sub (hchain 2))
  have hfun : (fun y : Amb 8 =>
        pUp ((Work.Drive.chr p) (D 0 (bPartC 0 y)) - (Work.Drive.chr p) (D 1 (bPartC 1 y)))
          ((Work.Drive.chr p) (D 0 (bPartC 0 y)) - (Work.Drive.chr p) (D 2 (bPartC 2 y)))) =
      chartDiff3 p D := rfl
  exact hfun ▸ hmain

/-! ## The kernel of the charted difference map -/

/-- The two components of `tan3`. -/
lemma tan3_fst (p : M) (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (x v : Amb 8) :
    (tan3 p D x v).1 = tc p D 0 x (md3 D 0 x (bPartC 0 v)) -
      tc p D 1 x (md3 D 1 x (bPartC 1 v)) := by
  simp [tan3]

lemma tan3_snd (p : M) (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (x v : Amb 8) :
    (tan3 p D x v).2 = tc p D 0 x (md3 D 0 x (bPartC 0 v)) -
      tc p D 2 x (md3 D 2 x (bPartC 2 v)) := by
  simp [tan3]

/-- The inverse change of coordinates of the three chains coincide at a triple intersection. -/
lemma tcInv_eq_of_meet {p : M} {D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M} {x : Amb 8}
    (hm : meet3 D x) {k k' : Fin 3} : tcInv p D k x = tcInv p D k' x := by
  rw [tcInv, tcInv, meet3_eq D hm k k']

/-- **The kernel of `tan3` is chart-free**: `tan3 p D x` vanishes on `v` exactly when the three
derivatives of the chains take the same value on the three blocks of `v`. -/
theorem tan3_eq_zero_iff (p : M) (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    {x : Amb 8} (hx : x ∈ region3 p D) (hm : meet3 D x) (v : Amb 8) :
    tan3 p D x v = 0 ↔
      Work.Drive.TripleCommonDir (md3 D 0 x) (md3 D 1 x) (md3 D 2 x) (fun k => bPartC k v) := by
  have htc01 : tc p D 0 x = tc p D 1 x := tc_eq_of_meet hm
  have htc02 : tc p D 0 x = tc p D 2 x := tc_eq_of_meet hm
  have htc01inv : tcInv p D 0 x = tcInv p D 1 x := tcInv_eq_of_meet hm
  have htc02inv : tcInv p D 0 x = tcInv p D 2 x := tcInv_eq_of_meet hm
  constructor
  · intro h
    have h1 : tc p D 0 x (md3 D 0 x (bPartC 0 v)) - tc p D 1 x (md3 D 1 x (bPartC 1 v)) = 0 := by
      rw [← tan3_fst p D x v, h]; rfl
    have h2 : tc p D 0 x (md3 D 0 x (bPartC 0 v)) - tc p D 2 x (md3 D 2 x (bPartC 2 v)) = 0 := by
      rw [← tan3_snd p D x v, h]; rfl
    have e1 : tc p D 0 x (md3 D 0 x (bPartC 0 v)) = tc p D 1 x (md3 D 1 x (bPartC 1 v)) :=
      sub_eq_zero.mp h1
    have e2 : tc p D 0 x (md3 D 0 x (bPartC 0 v)) = tc p D 2 x (md3 D 2 x (bPartC 2 v)) :=
      sub_eq_zero.mp h2
    refine ⟨?_, ?_⟩
    · have e1' : tc p D 0 x (md3 D 0 x (bPartC 0 v)) =
          tc p D 0 x (md3 D 1 x (bPartC 1 v)) := htc01.symm ▸ e1
      exact tc_injective p D 0 hx e1'
    · have e2' : tc p D 0 x (md3 D 0 x (bPartC 0 v)) =
          tc p D 0 x (md3 D 2 x (bPartC 2 v)) := htc02.symm ▸ e2
      exact tc_injective p D 0 hx e2'
  · rintro ⟨e1, e2⟩
    have hf : (tan3 p D x v).1 = 0 := by
      rw [tan3_fst, htc01, e1, sub_self]
    have hs : (tan3 p D x v).2 = 0 := by
      rw [tan3_snd, htc02, e2, sub_self]
    exact Prod.ext hf hs

/-- **The transversality hypothesis makes the charted difference map a submersion.** -/
theorem chartDiff3_surj (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hD : ∀ k, ContMDiff (𝓡 3) (𝓡 4) Ctop (D k))
    {p : M} {x : Amb 8} (hx : x ∈ region3 p D) (hm : meet3 D x)
    (htr : Work.Drive.TripleTransverse (md3 D 0 x) (md3 D 1 x) (md3 D 2 x)) :
    Function.Surjective (fderiv ℝ (chartDiff3 p D) x) := by
  rw [(hasFDerivAt_chartDiff3 p D hD hx).fderiv]
  intro w
  obtain ⟨z, hz⟩ := pUpCLM_surjective w
  obtain ⟨z1, z2⟩ := z
  have htc01 : tc p D 0 x = tc p D 1 x := tc_eq_of_meet hm
  have htc02 : tc p D 0 x = tc p D 2 x := tc_eq_of_meet hm
  have htc01inv : tcInv p D 0 x = tcInv p D 1 x := tcInv_eq_of_meet hm
  have htc02inv : tcInv p D 0 x = tcInv p D 2 x := tcInv_eq_of_meet hm
  obtain ⟨v, hv1, hv2⟩ := htr (tcInv p D 0 x z1) (tcInv p D 0 x z2)
  refine ⟨mk3 v, ?_⟩
  have hcomp : tan3 p D x (mk3 v) = (z1, z2) := by
    refine Prod.ext ?_ ?_
    · rw [tan3_fst, bPartC_mk3, bPartC_mk3, htc01, ← map_sub, hv1, htc01inv]
      exact tc_comp_tcInv p D 1 hx z1
    · rw [tan3_snd, bPartC_mk3, bPartC_mk3, htc02, ← map_sub, hv2, htc02inv]
      exact tc_comp_tcInv p D 2 hx z2
  rw [ContinuousLinearMap.comp_apply, hcomp, hz]

/-- **A common direction of the three derivatives is a kernel vector of the charted difference
map.** -/
theorem chartDiff3_eq_zero_of_commonDir (p : M) (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hD : ∀ k, ContMDiff (𝓡 3) (𝓡 4) Ctop (D k))
    {x : Amb 8} (hx : x ∈ region3 p D) (hm : meet3 D x)
    {v : Fin 3 → EuclideanSpace ℝ (Fin 3)}
    (hv : Work.Drive.TripleCommonDir (md3 D 0 x) (md3 D 1 x) (md3 D 2 x) v) :
    fderiv ℝ (chartDiff3 p D) x (mk3 v) = 0 := by
  have htc01 : tc p D 0 x = tc p D 1 x := tc_eq_of_meet hm
  have htc02 : tc p D 0 x = tc p D 2 x := tc_eq_of_meet hm
  obtain ⟨e1, e2⟩ := hv
  have h1 : (tan3 p D x (mk3 v)).1 = 0 := by
    rw [tan3_fst, bPartC_mk3, bPartC_mk3, htc01, e1, sub_self]
  have h2 : (tan3 p D x (mk3 v)).2 = 0 := by
    rw [tan3_snd, bPartC_mk3, bPartC_mk3, htc02, e2, sub_self]
  have hz : tan3 p D x (mk3 v) = 0 := Prod.ext h1 h2
  rw [(hasFDerivAt_chartDiff3 p D hD hx).fderiv, ContinuousLinearMap.comp_apply, hz, map_zero]

/-- **The kernel of the charted difference map does not depend on the chart.** -/
theorem chartDiff3_kernel_indep (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hD : ∀ k, ContMDiff (𝓡 3) (𝓡 4) Ctop (D k))
    {p p' : M} {x : Amb 8} (hm : meet3 D x) (hx : x ∈ region3 p D) (hx' : x ∈ region3 p' D)
    (v : Amb 8) :
    (fderiv ℝ (chartDiff3 p D) x v = 0 ↔ fderiv ℝ (chartDiff3 p' D) x v = 0) := by
  rw [(hasFDerivAt_chartDiff3 p D hD hx).fderiv,
    (hasFDerivAt_chartDiff3 p' D hD hx').fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, pUpCLM_eq_zero_iff, pUpCLM_eq_zero_iff,
    tan3_eq_zero_iff p D hx hm v, tan3_eq_zero_iff p' D hx' hm v]

end

end Work.Drive.TParity
