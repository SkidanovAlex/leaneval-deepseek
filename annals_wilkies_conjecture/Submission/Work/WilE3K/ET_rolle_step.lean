/-
  annals_wilkies_conjecture, AREA E3K (`Submission.Work.WilE3K`): the **Rolle step** of the
  arctan-elimination (K2 of the design `sources/wilkiesE3E9/wilkiesE3E9_gaps.md`).

  `E : ETData N (rt+1) n re` is a lifted system; `E.psiMap` is the system map with the eliminated
  (last) arctan equation `E.gLast` deleted, and `s` is a finite set of nondegenerate zeros of `E`.

  Given a level `y` of the remaining system which is good (`E.ETGood y`: a regular value, on which
  the crossings are nondegenerate and the critical values of the Rolle determinant are null) and
  such that every small value `y'` of the full map is hit by `s.card` points (the hypothesis
  `hift`, applied at the value `E.psiLift y` — this is where `hydist` is used: `E.psiLift y` *is*
  the value `(y, 0)` in the coordinates of `E.map`), there is a level `δ` of the Rolle determinant
  such that the new system `E.newData y δ` — the remaining arctan equations, the old exp-affine
  equations shifted by `y`, and the Rolle equation `rolleDetP - δ · prodPoly` — has at least
  `s.card` nondegenerate zeros, with the degree bound of the recursion.

  The proof follows `Work.WilE2.kho_proper`:

  * `E.map z = E.psiLift y ↔ E.psiMap z = y ∧ E.gLast z = 0`: the hypothesis `hift` produces
    `s.card` crossings of the level set `{psiMap = y}` with the eliminated equation
    (`ETRolle/IndexBook.lean`);
  * on that level set the remaining system `V = psiMap - y` is a submersion with compact level sets
    (`hgood.1`, `hproper`), and the Rolle determinant is the derivative of `gLast` along its
    cross-product field (`rolleDetFun_crossField`), so the Khovanskii–Rolle counting
    `Work.WilE2.rolle_count_elimination` dominates the `s.card` crossings by points where the Rolle
    determinant takes a small generic value `δ`: the smallness and the genericity come from
    `exists_delta_lt_abs_avoid_null` applied to the null slice `E.ETSliceNull y` of `hgood.2.2`,
    the nondegeneracy of the crossings from `E.ETRegValue y` via `E.rolleDetFun z = (E.jac z).det`;
  * the vanishing of the new equations and the nondegeneracy of the new Jacobian at those points is
    `ETRolle/LevelSet.lean` and `ETRolle/Nondegen.lean`;
  * the degree bound is `newData_degree`.
-/
import Mathlib
import Submission.Work.WilE3K.ET
import Submission.Work.WilE3K.Elim
import Submission.Work.WilE3K.ContAux
import Submission.Work.WilE3K.ETRolle.IndexBook
import Submission.Work.WilE3K.ETRolle.LevelSet
import Submission.Work.WilE3K.ETRolle.Nondegen
import Submission.Work.WilE2.KhoCount
import Submission.Work.WilE2.kho_proper
import Submission.Work.WilE2.rolle_count_level_curve
import Submission.Work.WilE2.exists_delta_lt_abs_avoid_null
import Submission.Work.WilE3K.contDiff_map_and_det
import Submission.Work.WilE3K.evalPoly_rolleDetP
import Submission.Work.WilE3K.rolleDetFun_crossField
import Submission.Work.WilE3K.newData_degree

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
namespace Work.WilE3K
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

theorem ET_rolle_step {N rt n re : ℕ} (E : Work.WilE3K.ETData N (rt + 1) n re)
    (s : Finset (Fin (N + 1) → ℝ))
    (hs : ∀ z ∈ s, E.Nondegen z) (hproper : IsProperMap E.psiMap)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hift : ∀ y' : Fin (N + 1) → ℝ, dist y' 0 < ρ →
      ∃ t : Finset (Fin (N + 1) → ℝ), t.card = s.card ∧ ∀ z ∈ t, E.map z = y')
    (y : Fin N → ℝ) (hgood : E.ETGood y) (hydist : dist (E.psiLift y) 0 < ρ) :
    ∃ (δ : ℝ) (t : Finset (Fin (N + 1) → ℝ)),
      (∀ z ∈ t, (E.newData y δ).Nondegen z) ∧ s.card ≤ t.card ∧
      (∑ i, WilkiesDesign.E.atomDeg ((E.newData y δ).G i)) + rt ≤
        (N + 8) * ((∑ i, WilkiesDesign.E.atomDeg (E.G i)) + (rt + 1) + 8) := by
  classical
  -- The level `(y, 0)` of the full map is the value `psiLift y`, at distance `< ρ` from `0`.
  obtain ⟨t₀, ht₀card, ht₀mem⟩ := hift (E.psiLift y) hydist
  have ht₀ : ∀ z ∈ t₀, E.psiMap z = y ∧ E.gLast z = 0 :=
    fun z hz => (E.map_eq_psiLift_iff y z).mp (ht₀mem z hz)
  -- The remaining system, as a map to `ℝ^N`.
  set V : (Fin (N + 1) → ℝ) → (Fin N → ℝ) := fun w => E.psiMap w - y with hVdef
  have hVzero : ∀ z, V z = 0 ↔ E.psiMap z = y := fun z => sub_eq_zero
  -- Smoothness of the system map and of its components.
  have hmap2 : ContDiff ℝ 2 E.map := (Work.WilE3K.contDiff_map_and_det E).1
  have hpsi2 : ContDiff ℝ 2 (fun w => E.psiMap w) := by
    refine contDiff_pi.mpr fun i => ?_
    have hcomp : ContDiff ℝ 2 (fun w => E.map w (Fin.succAbove E.lastRow i)) :=
      (contDiff_pi.mp hmap2) _
    simpa only [ETData.psiMap_apply] using hcomp
  have hV2 : ContDiff ℝ 2 V := by
    rw [hVdef]
    exact hpsi2.sub contDiff_const
  have hV1 : ContDiff ℝ 1 V := hV2.of_le (by norm_num)
  have hgLast2 : ContDiff ℝ 2 E.gLast := by
    rw [show E.gLast = fun w => E.map w E.lastRow from funext fun w => (E.map_lastRow w).symm]
    exact (contDiff_pi.mp hmap2) _
  have hgLast1 : ContDiff ℝ 1 E.gLast := hgLast2.of_le (by norm_num)
  set c : ℝ := (-1 : ℝ) ^ n with hc
  have hg : ContDiff ℝ 1 (fun w => c * E.gLast w) := by
    have h1 : ContDiff ℝ 1 (fun _ : Fin (N + 1) → ℝ => c) := contDiff_const
    simpa only [Pi.mul_apply] using h1.mul hgLast1
  -- The Rolle determinant is the derivative of the eliminated equation along the cross-product
  -- field of the remaining system.
  have hcross : ∀ z, V z = 0 →
      E.rolleDetFun z = c * fderiv ℝ E.gLast z (Work.WilE2.crossField V z) := by
    intro z hz
    have hzy : E.psiMap z = y := (hVzero z).mp hz
    have h1 := (Work.WilE3K.rolleDetFun_crossField E).2.2 y z hzy
    rw [hVdef]
    exact h1
  have hgmul : ∀ z, fderiv ℝ (fun w => c * E.gLast w) z = c • fderiv ℝ E.gLast z := by
    intro z
    have hgd' : HasFDerivAt E.gLast (fderiv ℝ E.gLast z) z :=
      ((hgLast1.differentiable (by norm_num)) z).hasFDerivAt
    exact (hgd'.const_mul c).fderiv
  have hpsi : ∀ z, V z = 0 → (fun w => c * E.gLast w) z = 0 →
      E.rolleDetFun z = fderiv ℝ (fun w => c * E.gLast w) z (Work.WilE2.crossField V z) := by
    intro z hz _
    rw [hcross z hz, hgmul z]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hψne : ∀ z, V z = 0 → (fun w => c * E.gLast w) z = 0 → E.rolleDetFun z ≠ 0 := by
    intro z hz hgz
    have hzy : E.psiMap z = y := (hVzero z).mp hz
    have hg0 : E.gLast z = 0 := by
      have h1 : c * E.gLast z = 0 := hgz
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 (by rw [hc]; exact pow_ne_zero n (by norm_num))
      · exact h2
    rw [E.rolleDetFun_eq_jac_det z]
    exact hgood.2.1 z hzy hg0
  have hnd : ∀ z, V z = 0 → (fun w => c * E.gLast w) z = 0 →
      fderiv ℝ (fun w => c * E.gLast w) z (Work.WilE2.crossField V z) ≠ 0 := by
    intro z hz hgz
    rw [← hpsi z hz hgz]
    exact hψne z hz hgz
  -- Compactness of the level set and linear independence of the gradients.
  have hC : IsCompact {z : Fin (N + 1) → ℝ | V z = 0} := by
    have heq : {z : Fin (N + 1) → ℝ | V z = 0} = E.psiMap ⁻¹' {y} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
      exact hVzero z
    rw [heq]
    exact hproper.isCompact_preimage isCompact_singleton
  have hgrad : ∀ z, V z = 0 →
      LinearIndependent ℝ (fun a : Fin N => fderiv ℝ (fun w => V w a) z) := by
    intro z hz
    have hsub := hgood.1 z ((hVzero z).mp hz)
    have hfun : (fun a : Fin N => fderiv ℝ (fun w => V w a) z)
        = fun a : Fin N => fderiv ℝ (fun w => E.psiMap w a) z := by
      funext a
      rw [hVdef]
      exact fderiv_sub_const (y a)
    rw [hfun]
    exact hsub
  -- The level `δ` of the Rolle determinant: small and generic.
  obtain ⟨δ, hδpos, hδK, hδlt⟩ :=
    Work.WilE2.exists_delta_lt_abs_avoid_null V (fun w => c * E.gLast w) E.rolleDetFun hV1 hg
      (Work.WilE3K.rolleDetFun_crossField E).2.1 hC hψne
      {t : ℝ | Fin.snoc y t ∈ E.rolleMap '' {z | (fderiv ℝ E.rolleMap z).det = 0}}
      (by simpa only [ETData.ETSliceNull] using hgood.2.2)
  -- The Khovanskii–Rolle counting step.
  have hs₀ : ∀ z ∈ t₀, V z = 0 ∧ (fun w => c * E.gLast w) z = 0 := by
    intro z hz
    obtain ⟨h1, h2⟩ := ht₀ z hz
    exact ⟨(hVzero z).mpr h1, by simp only [h2, mul_zero]⟩
  obtain ⟨t, ht, htcard⟩ :=
    Work.WilE2.rolle_count_elimination V (fun w => c * E.gLast w) E.rolleDetFun hV2 hg
      (Work.WilE3K.rolleDetFun_crossField E).2.1 hC hgrad hpsi hnd δ hδpos hδlt t₀ hs₀
  refine ⟨δ, t, ?_, ?_, ?_⟩
  · -- every point of `t` is a nondegenerate zero of the new system
    intro z hz
    obtain ⟨hzV, hzψ⟩ := ht z hz
    have hzy : E.psiMap z = y := (hVzero z).mp hzV
    refine E.newData_nondegen_of_rolleMap y δ z hzy hzψ ?_
    intro hdet
    refine hδK ?_
    refine ⟨z, hdet, ?_⟩
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.snoc_last]
      rw [show E.rolleMap z (Fin.last N) = E.rolleDetFun z from E.rolleMap_fun_last z, hzψ]
    · rw [Fin.snoc_castSucc]
      rw [E.rolleMap_fun_lt z (Fin.castSucc j) (by simpa using j.isLt)]
      exact congrFun hzy j
  · rw [← ht₀card]
    exact htcard
  · exact Work.WilE3K.newData_degree E y δ

end Work.WilE3K
