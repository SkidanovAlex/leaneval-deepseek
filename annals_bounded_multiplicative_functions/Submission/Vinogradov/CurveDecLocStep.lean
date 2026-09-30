/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.AsymFineProof
import Submission.Vinogradov.AsymRefine

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# GLYZ §3.4: the reparametrisation of the level-`M` sub-blocks of a coarse block

The projected curve `Dproj = projCurveDeriv k l b` has torsion only where `|t − ξ'| ≥ 1/4`
(`Projection.torsion_projCurveDeriv`).  GLYZ therefore apply Corollary 3.7 to the *restriction*
of the curve to the coarse block `I`; in our formalisation this is the reparametrisation

  `D_I := intervalCurve l a c Dproj`,  `a = q/2^m`, `c = 1/2^m`,

so that the level-`M` sub-pieces of `I` become the whole (canonical) partition of `[0,1]` for
`D_I`.  The key structural identities are

* `pieceCenter_subIdx`: the centre of the level-`M` sub-block `subIdx m M q j` is
  `a + c · pieceCenter (2^{M−m}) j`;
* `curvePlate_intervalCurve` (`CurveLayer`): `curvePlate l D_I δ σ = curvePlate l Dproj (cδ) (a+cσ)`;
* `CurveTorsion_intervalCurve_of` (`CurveLayer`): the torsion of `Dproj` on `[a, a+c]` (which is
  all we have) transfers to `D_I` on `[0,1]`.

This module contains the index arithmetic and the **class transport** of
`AsymFine.exists_isFourierRep_restrict_translate` to the reparametrised family.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Submission.Vinogradov

/-! ## 1. The level-`M` sub-blocks of a level-`m` block -/

/-- **The level-`M` sub-block `j` of the level-`m` block `q`**, as an index at level `M`. -/
def subIdx (m M : ℕ) (hmM : m ≤ M) (q : Fin (2 ^ m)) (j : Fin (2 ^ (M - m))) : Fin (2 ^ M) :=
  ⟨(q : ℕ) * 2 ^ (M - m) + (j : ℕ), by
    have h1 : (q : ℕ) * 2 ^ (M - m) ≤ (2 ^ m - 1) * 2 ^ (M - m) :=
      Nat.mul_le_mul_right _ (Nat.le_sub_one_of_lt q.isLt)
    have h2 : (2 ^ m - 1) * 2 ^ (M - m) = 2 ^ M - 2 ^ (M - m) := by
      rw [Nat.sub_mul, one_mul, ← pow_add, Nat.add_sub_cancel' hmM]
    have h3 : (j : ℕ) < 2 ^ (M - m) := j.isLt
    have h4 : 2 ^ (M - m) ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le M m)
    have h5 : (q : ℕ) * 2 ^ (M - m) ≤ 2 ^ M - 2 ^ (M - m) := by
      rw [← h2]; exact h1
    omega⟩

/-- **The centre of a sub-block**, in the reparametrised coordinate: `a + c · σ_j`. -/
lemma pieceCenter_subIdx {m M : ℕ} (hmM : m ≤ M) (q : Fin (2 ^ m))
    (j : Fin (2 ^ (M - m))) :
    pieceCenter (2 ^ M) (subIdx m M hmM q j)
      = ((q : ℕ) : ℝ) / (2 : ℝ) ^ m
        + (1 / (2 : ℝ) ^ m) * pieceCenter (2 ^ (M - m)) j := by
  have hpow : (2 : ℝ) ^ M = (2 : ℝ) ^ m * (2 : ℝ) ^ (M - m) := by
    rw [← pow_add, Nat.add_sub_cancel' hmM]
  have hcast : ((subIdx m M hmM q j : ℕ) : ℝ)
      = ((q : ℕ) : ℝ) * (2 : ℝ) ^ (M - m) + ((j : ℕ) : ℝ) := by
    simp only [subIdx, Fin.val_mk]
    push_cast
    ring
  rw [pieceCenter, pieceCenter, hcast]
  push_cast
  rw [hpow]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have hpos2 : (0 : ℝ) < (2 : ℝ) ^ (M - m) := by positivity
  field_simp
  ring


/-! ## 2. The class transport to the reparametrised curve -/

/-- **The class transport for the reparametrised sub-blocks.**  The level-`M` sub-block sums of a
coarse block `q`, restricted to a translate `H + z` and reparametrised to the block, lie in the
class of the plates of the reparametrised projected curve `intervalCurve l a c Dproj` — with the
plate enlargement `lam · 8` of `exists_isFourierRep_restrict_translate`. -/
theorem exists_isFourierRep_subBlk_intervalCurve {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l)
    (hlk : l ≤ k) {ξ' : ℝ} (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1) :
    ∃ lam : ℝ, 1 ≤ lam ∧ ∀ {N m M : ℕ} (h2m : 2 ≤ m) (hmM : m ≤ M) (hMN : M ≤ N)
      (q : Fin (2 ^ m))
      (hsep : ∀ j : Fin (2 ^ (M - m)),
        1 / 4 ≤ |pieceCenter (2 ^ M) (subIdx m M hmM q j) - ξ'|)
      (z : E k) (f : Fin (2 ^ N) → E k → ℂ),
      (∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i)) →
      ∀ j : Fin (2 ^ (M - m)),
        IsFourierRep l
          (curvePlate l
            (intervalCurve l (((q : ℕ) : ℝ) / (2 : ℝ) ^ m) (1 / (2 : ℝ) ^ m)
              (projCurveDeriv k l (torsionVec k l hlk ξ')))
            (lam * (8 * plateHalf M) * (2 : ℝ) ^ m) (pieceCenter (2 ^ (M - m)) j))
          (fun y => ∑ i ∈ blkFin N M (subIdx m M hmM q j),
              f i (projEmbedLin k l (torsionVec k l hlk ξ') y + z)) := by
  obtain ⟨lam, hlam, hlam'⟩ := exists_isFourierRep_restrict_translate hk hl hlk hξ'
  refine ⟨lam, hlam, ?_⟩
  intro N m M h2m hmM hMN q hsep z f hf j
  have hM2 : 2 ≤ M := le_trans h2m hmM
  have hblk := hlam' hM2 hMN (subIdx m M hmM q j) z f hf (hsep j)
  have hδ : (1 / (2 : ℝ) ^ m) * (lam * (8 * plateHalf M) * (2 : ℝ) ^ m)
      = lam * (8 * plateHalf M) := by
    field_simp
  have hset : curvePlate l (projCurveDeriv k l (torsionVec k l hlk ξ'))
        (lam * (8 * plateHalf M)) (pieceCenter (2 ^ M) (subIdx m M hmM q j))
      = curvePlate l
          (intervalCurve l (((q : ℕ) : ℝ) / (2 : ℝ) ^ m) (1 / (2 : ℝ) ^ m)
            (projCurveDeriv k l (torsionVec k l hlk ξ')))
          (lam * (8 * plateHalf M) * (2 : ℝ) ^ m) (pieceCenter (2 ^ (M - m)) j) := by
    rw [pieceCenter_subIdx hmM q j]
    rw [curvePlate_intervalCurve, hδ]
  rw [← hset]
  exact hblk


/-! ## 3. The three curve hypotheses for the reparametrised projected curve -/

/-- **The torsion of the reparametrised projected curve on the whole interval `[0,1]`**, obtained
from the *localised* torsion of `Dproj` on the coarse block `[a, a+c]`
(`Projection.torsion_projCurveDeriv` + `CurveLayer.CurveTorsion_intervalCurve_of`). -/
theorem CurveTorsion_intervalCurve_proj {k l : ℕ} (hl : 1 ≤ l) (hlk : l ≤ k) {ξ' : ℝ}
    (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1) {m : ℕ} (hm : 1 ≤ m) (q : Fin (2 ^ m))
    (hsep : ∀ t ∈ Set.Icc (((q : ℕ) : ℝ) / (2 : ℝ) ^ m)
      (((q : ℕ) : ℝ) / (2 : ℝ) ^ m + 1 / (2 : ℝ) ^ m), 1 / 4 ≤ |t - ξ'|) :
    ∃ cT : ℝ, 0 < cT ∧
      CurveTorsion l
        (intervalCurve l (((q : ℕ) : ℝ) / (2 : ℝ) ^ m) (1 / (2 : ℝ) ^ m)
          (projCurveDeriv k l (torsionVec k l hlk ξ'))) cT := by
  obtain ⟨c, hc, htor⟩ := torsion_projCurveDeriv k l hl hlk ξ' hξ'
  set a : ℝ := ((q : ℕ) : ℝ) / (2 : ℝ) ^ m with ha
  set cc : ℝ := 1 / (2 : ℝ) ^ m with hcc
  have hm0 : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have hc0 : 0 ≤ cc := by rw [hcc]; positivity
  have hc1 : cc ≤ 1 := by
    rw [hcc, div_le_one hm0]
    have : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
    linarith
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hac : a + cc ≤ 1 := by
    rw [ha, hcc, ← add_div, div_le_one hm0]
    have hq : (q : ℕ) + 1 ≤ 2 ^ m := q.isLt
    have hcast : ((q : ℕ) : ℝ) + 1 ≤ ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast hq
    rw [show ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ m from by push_cast; ring] at hcast
    linarith
  refine ⟨c * cc ^ (l * (l + 1)), mul_pos hc (pow_pos (by positivity) _), ?_⟩
  intro σ hσ
  have hloc : ∀ t ∈ Set.Icc a (a + cc),
      c ≤ (Matrix.gram ℝ (fun j : Fin l =>
        projCurveDeriv k l (torsionVec k l hlk ξ') (j.val + 1) t)).det := by
    intro t ht
    refine htor t ?_ (hsep t ht)
    exact ⟨by linarith [ht.1, ha0], by linarith [ht.2, hac]⟩
  exact CurveTorsion_intervalCurve_of hloc hc0 ha0 hac hσ

/-- **The three curve hypotheses of the tower for the reparametrised projected curve.** -/
theorem curveHypotheses_intervalCurve {k l : ℕ} (hl : 1 ≤ l) (hlk : l ≤ k) {ξ' : ℝ}
    (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1) {m : ℕ} (hm : 1 ≤ m) (q : Fin (2 ^ m))
    (hsep : ∀ t ∈ Set.Icc (((q : ℕ) : ℝ) / (2 : ℝ) ^ m)
      (((q : ℕ) : ℝ) / (2 : ℝ) ^ m + 1 / (2 : ℝ) ^ m), 1 / 4 ≤ |t - ξ'|) :
    ∃ (A cT R : ℝ), 1 ≤ A ∧ 0 < cT ∧ 0 ≤ R ∧
      CurveBounded l
        (intervalCurve l (((q : ℕ) : ℝ) / (2 : ℝ) ^ m) (1 / (2 : ℝ) ^ m)
          (projCurveDeriv k l (torsionVec k l hlk ξ'))) A ∧
      CurveTorsion l
        (intervalCurve l (((q : ℕ) : ℝ) / (2 : ℝ) ^ m) (1 / (2 : ℝ) ^ m)
          (projCurveDeriv k l (torsionVec k l hlk ξ'))) cT ∧
      CurveTaylor l
        (intervalCurve l (((q : ℕ) : ℝ) / (2 : ℝ) ^ m) (1 / (2 : ℝ) ^ m)
          (projCurveDeriv k l (torsionVec k l hlk ξ'))) R := by
  obtain ⟨R₀, hR₀pos, htay⟩ := CurveTaylor_projCurveDeriv k l hl hlk
    (orthonormal_torsionVec k l hlk ξ')
  obtain ⟨cT, hcT, htor⟩ := CurveTorsion_intervalCurve_proj hl hlk hξ' hm q hsep
  refine ⟨Real.sqrt k * (k.factorial : ℝ), cT, R₀,
    one_le_mul_of_one_le_of_one_le (Real.one_le_sqrt.mpr (by exact_mod_cast le_trans hl hlk))
      (by exact_mod_cast Nat.factorial_pos k), hcT, hR₀pos.le, ?_, htor, ?_⟩
  · refine CurveBounded_intervalCurve (CurveBounded_projCurveDeriv k l hlk
      (orthonormal_torsionVec k l hlk ξ')) (by positivity) ?_ (by positivity) ?_
    · rw [div_le_one (by positivity : (0:ℝ) < (2:ℝ)^m)]
      have : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
      linarith
    · rw [← add_div, div_le_one (by positivity : (0:ℝ) < (2:ℝ)^m)]
      have hq : (q : ℕ) + 1 ≤ 2 ^ m := q.isLt
      have hcast : ((q : ℕ) : ℝ) + 1 ≤ ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast hq
      rw [show ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ m from by push_cast; ring] at hcast
      linarith
  · exact CurveTaylor_intervalCurve htay hR₀pos.le (by positivity)
      (by rw [div_le_one (by positivity : (0:ℝ) < (2:ℝ)^m)]
          have : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num); linarith)
      (by positivity)
      (by rw [← add_div, div_le_one (by positivity : (0:ℝ) < (2:ℝ)^m)]
          have hq : (q : ℕ) + 1 ≤ 2 ^ m := q.isLt
          have hcast : ((q : ℕ) : ℝ) + 1 ≤ ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast hq
          rw [show ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ m from by push_cast; ring] at hcast
          linarith)

end Submission.Vinogradov
