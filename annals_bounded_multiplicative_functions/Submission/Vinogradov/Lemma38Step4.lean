/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.Lemma38Step3
import Submission.Vinogradov.CurveDecLocStep
import Submission.Vinogradov.LocalisedDecouplingR

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# GLYZ Lemma 3.8, step 4: Corollary 3.7 on each translate

Lane 4 of the §3.4 chain.  The block `q` at level `m` is refined into the `mt = 2^(M-m)` level-`M`
sub-blocks; the localised decoupling `CurveDecLocR` (proved for the reparametrised projected curve
in `CurveDecProj.curveDecLocR_intervalCurve_proj`) is applied to the sub-block sums
`G_J = ∑_{i ∈ blkFin N M J} f i` composed with the `H`-isometry, giving

  `AV (u) ≤ |B| · C_loc^{p_l} · (∑_J TN_J (u)^{2/p_l})^{p_l/2}`

with `AV (u) = ∫⁻_{w ∈ B_H(0,r)} (‖f_I (u + Ψ w)‖₊)^{p_l}` and
`TN_J (u) = tentNorm l A 0 r (fun y => G_J (u + Ψ y))`.

This file contains the first, purely combinatorial ingredient of the lane: the **bijection** between
the index set `Fin (2^(M-m))` of the sub-blocks of the block `q` and the `Finset`
`subBlkLvl m M q`, together with the corresponding reindexing of sums.  The rest of the lane (the
class transport of `CurveDecLocStep.exists_isFourierRep_subBlk_intervalCurve` to the enlargement
`lam/(2*mt)`, and the identification of the `ballAvg` with `|B|⁻¹ AV`) is stated in the session-58
lanes of `ROADMAP.lean`.
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

/-! ## 1. The sub-block index `subIdx` -/

lemma subIdx_val (m M : ℕ) (hmM : m ≤ M) (q : Fin (2 ^ m)) (j : Fin (2 ^ (M - m))) :
    ((subIdx m M hmM q j : ℕ)) = (q : ℕ) * 2 ^ (M - m) + (j : ℕ) := rfl

/-- The sub-block index lies in the block: `subIdx` divides back to `q`. -/
lemma subIdx_div (m M : ℕ) (hmM : m ≤ M) (q : Fin (2 ^ m)) (j : Fin (2 ^ (M - m))) :
    ((subIdx m M hmM q j : ℕ)) / 2 ^ (M - m) = (q : ℕ) := by
  have hpos : 0 < 2 ^ (M - m) := by positivity
  have hcomm : (q : ℕ) * 2 ^ (M - m) = 2 ^ (M - m) * (q : ℕ) := Nat.mul_comm _ _
  rw [subIdx_val, hcomm, Nat.mul_add_div hpos, Nat.div_eq_of_lt j.isLt, Nat.add_zero]

/-- `subIdx` is injective: the sub-blocks of a block are distinct. -/
lemma subIdx_injective (m M : ℕ) (hmM : m ≤ M) (q : Fin (2 ^ m)) :
    Function.Injective (subIdx m M hmM q) := by
  intro j₁ j₂ h
  have h1 : ((subIdx m M hmM q j₁ : ℕ)) = ((subIdx m M hmM q j₂ : ℕ)) := by rw [h]
  rw [subIdx_val, subIdx_val] at h1
  exact Fin.ext (Nat.add_left_cancel h1)

/-- The sub-block index maps onto the block. -/
lemma subIdx_surjOn (m M : ℕ) (hmM : m ≤ M) (q : Fin (2 ^ m)) :
    ∀ q'' ∈ subBlkLvl m M q,
      ∃ j : Fin (2 ^ (M - m)), subIdx m M hmM q j = q'' := by
  intro q'' hq''
  have hpos : 0 < 2 ^ (M - m) := by positivity
  have hdiv : (q'' : ℕ) / 2 ^ (M - m) = (q : ℕ) := mem_subBlkLvl.mp hq''
  refine ⟨⟨(q'' : ℕ) % 2 ^ (M - m), Nat.mod_lt _ hpos⟩, ?_⟩
  refine Fin.ext ?_
  rw [subIdx_val]
  show (q : ℕ) * 2 ^ (M - m) + (q'' : ℕ) % 2 ^ (M - m) = (q'' : ℕ)
  have h := Nat.div_add_mod (q'' : ℕ) (2 ^ (M - m))
  rw [hdiv, Nat.mul_comm] at h
  exact h

/-- The image of the full index set under `subIdx` is the block. -/
lemma image_subIdx_univ (m M : ℕ) (hmM : m ≤ M) (q : Fin (2 ^ m)) :
    Finset.image (subIdx m M hmM q) Finset.univ = subBlkLvl m M q := by
  ext q''
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    exact mem_subBlkLvl.mpr (subIdx_div m M hmM q j)
  · exact subIdx_surjOn m M hmM q q''

/-- **The reindexing of a sum over the sub-blocks of a block.** -/
lemma sum_subIdx_eq_sum_subBlkLvl {m M : ℕ} (hmM : m ≤ M) (q : Fin (2 ^ m))
    {α : Type*} [AddCommMonoid α] (g : Fin (2 ^ M) → α) :
    (∑ j : Fin (2 ^ (M - m)), g (subIdx m M hmM q j))
      = ∑ q'' ∈ subBlkLvl m M q, g q'' := by
  have hinj : Set.InjOn (subIdx m M hmM q)
      (↑(Finset.univ : Finset (Fin (2 ^ (M - m))))) :=
    fun a _ b _ h => subIdx_injective m M hmM q h
  have h := Finset.sum_image (s := (Finset.univ : Finset (Fin (2 ^ (M - m))))) (f := g)
    (g := subIdx m M hmM q) hinj
  rw [image_subIdx_univ m M hmM q] at h
  exact h.symm

/-! ## 2. A congruence lemma for the class -/

/-- The class `𝒞(U)` is closed under pointwise equality of functions. -/
lemma IsFourierRep.congr {k : ℕ} {U : Set (E k)} {f g : E k → ℂ} (hf : IsFourierRep k U f)
    (h : ∀ x, f x = g x) : IsFourierRep k U g := by
  obtain ⟨ι, m, Γ, ν, φ, hν, hφ, hΓ, hmφ, hU, hf'⟩ := hf
  exact IsFourierRep.mk' hν hφ hΓ hmφ hU fun x => by rw [← h x, hf' x]

/-! ## 3. The localised decoupling on the `H`-ball average -/

/-- **GLYZ Lemma 3.8, step 4 (Corollary 3.7 on each translate).**  The `H`-ball average of
`|f_I|^{p_l}` — the object produced by the convolution swap of step 3 — is bounded by the `ℓ²`-sum
of the tent norms of the level-`M` sub-block sums:

  `∫⁻_{w ∈ B_H(0,r)} (‖f_I (u + Ψ w)‖₊)^{p_l}
     ≤ |B_H(0,r)| · C_loc^{p_l} · (∑_{J ∈ subBlkLvl m M q} TN_J (u)^{2/p_l})^{p_l/2}`,

with `TN_J (u) = tentNorm l A 0 r (fun y => G_J (u + Ψ y))` and
`G_J = ∑_{i ∈ blkFin N M J} f i`.

The inputs are the localised decoupling `CurveDecLocR` for the reparametrised projected curve
(`CurveDecProj.curveDecLocR_intervalCurve_proj`) and the class hypothesis for the sub-block sums at
the translate `H + u`, at the enlargement `lam/(2·mt)` (`mt = 2^(M-m)`) — obtained by the caller
from `CurveDecLocStep.exists_isFourierRep_subBlk_intervalCurve` plus monotonicity in the plate
(which is why `lam` must dominate `lamB · 8 · plateHalf M · 2^m`).  The two sum identifications are
`sum_subIdx_eq_sum_subBlkLvl` (section 1) and `AsymRefine.sum_subBlkLvl` (the partition of the
block into its sub-blocks); the passage between `ballAvg` and the raw ball integral is
`ballAvg_apply` plus `ENNReal.mul_inv_cancel` for the ball volume. -/
theorem asymAV_le_curveDecLocR {k l N m M m' : ℕ} (hl : 1 ≤ l) (hlk : l ≤ k)
    (hmM : m ≤ M) (hMN : M ≤ N)
    {ξ' : ℝ} (q : Fin (2 ^ m))
    {f : Fin (2 ^ N) → E k → ℂ} (u : E k)
    {lam A r : ℝ} (hA : 0 ≤ A) (hrR : hBallR k l m' ≤ r)
    {C : ℝ≥0∞}
    (hdec : CurveDecLocR l
      (intervalCurve l (((q : ℕ) : ℝ) / (2 : ℝ) ^ m) (1 / (2 : ℝ) ^ m)
        (projCurveDeriv k l (torsionVec k l hlk ξ')))
      (2 ^ (M - m)) lam A (hBallR k l m') C)
    (hclass : ∀ j : Fin (2 ^ (M - m)),
      IsFourierRep l
        (curvePlate l
          (intervalCurve l (((q : ℕ) : ℝ) / (2 : ℝ) ^ m) (1 / (2 : ℝ) ^ m)
            (projCurveDeriv k l (torsionVec k l hlk ξ')))
          (lam / (2 * ((2 ^ (M - m) : ℕ) : ℝ))) (pieceCenter (2 ^ (M - m)) j))
        (fun y : E l => ∑ i ∈ blkFin N M (subIdx m M hmM q j),
          f i (u + projEmbedLin k l (torsionVec k l hlk ξ') y))) :
    (∫⁻ w in Metric.ball (0 : E l) r,
        (‖∑ i ∈ blkFin N m q,
          f i (u + projEmbedLin k l (torsionVec k l hlk ξ') w)‖₊ : ℝ≥0∞) ^ (plExp l))
      ≤ ENNReal.ofReal ((volume (Metric.ball (0 : E l) r)).toReal) * C ^ (plExp l)
        * (∑ J ∈ subBlkLvl m M q,
            (tentNorm l A 0 r (fun y : E l => ∑ i ∈ blkFin N M J,
              f i (u + projEmbedLin k l (torsionVec k l hlk ξ') y))) ^ (2 / plExp l))
          ^ (plExp l / 2) := by
  set Ψ : E l →ₗ[ℝ] E k := projEmbedLin k l (torsionVec k l hlk ξ') with hΨ
  set gg : Fin (2 ^ (M - m)) → E l → ℂ :=
    fun j y => ∑ i ∈ blkFin N M (subIdx m M hmM q j), f i (u + Ψ y) with hgg
  have hclass' : ∀ j : Fin (2 ^ (M - m)), IsFourierRep l
      (curvePlate l
        (intervalCurve l (((q : ℕ) : ℝ) / (2 : ℝ) ^ m) (1 / (2 : ℝ) ^ m)
          (projCurveDeriv k l (torsionVec k l hlk ξ')))
        (lam / (2 * (((2 ^ (M - m) : ℕ) : ℝ)))) (pieceCenter (2 ^ (M - m)) j)) (gg j) :=
    fun j => IsFourierRep.congr (hclass j) fun y => by simp only [hgg]
  have hdec' := hdec gg hclass' 0 r hrR
  have hsum : (fun y : E l => ∑ j : Fin (2 ^ (M - m)), gg j y)
      = fun y : E l => ∑ i ∈ blkFin N m q, f i (u + Ψ y) := by
    funext y
    simp only [hgg]
    rw [sum_subIdx_eq_sum_subBlkLvl hmM q
      (fun J : Fin (2 ^ M) => ∑ i ∈ blkFin N M J, f i (u + Ψ y))]
    exact (sum_subBlkLvl hmM hMN q (fun i : Fin (2 ^ N) => f i (u + Ψ y))).symm
  rw [hsum] at hdec'
  rw [ballAvg_apply] at hdec'
  have hRsum : (∑ j : Fin (2 ^ (M - m)),
        (∫⁻ x, (‖gg j x‖₊ : ℝ≥0∞) ^ (plExp l) * ballTent l A 0 r x) ^ (2 / plExp l))
      = ∑ J ∈ subBlkLvl m M q,
          (tentNorm l A 0 r (fun y : E l => ∑ i ∈ blkFin N M J,
            f i (u + Ψ y))) ^ (2 / plExp l) := by
    refine (sum_subIdx_eq_sum_subBlkLvl hmM q
      (fun J : Fin (2 ^ M) => (tentNorm l A 0 r
        (fun y : E l => ∑ i ∈ blkFin N M J, f i (u + Ψ y))) ^ (2 / plExp l))).trans ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hgg, tentNorm]
  rw [hRsum] at hdec'
  have hrpos : 0 < r := lt_of_lt_of_le (hBallR_pos k l m') hrR
  have hBpos : ENNReal.ofReal ((volume (Metric.ball (0 : E l) r)).toReal) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]
    exact ENNReal.toReal_pos (Metric.measure_ball_pos (μ := volume) 0 hrpos).ne'
      (measure_ball_lt_top (μ := volume)).ne
  have hBtop : ENNReal.ofReal ((volume (Metric.ball (0 : E l) r)).toReal) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hmain := mul_le_mul_of_nonneg_left hdec' (by positivity : (0 : ℝ≥0∞) ≤ ENNReal.ofReal ((volume (Metric.ball (0 : E l) r)).toReal))
  rw [← mul_assoc, ENNReal.mul_inv_cancel hBpos hBtop, one_mul] at hmain
  exact hmain.trans (le_of_eq (mul_assoc _ _ _).symm)

end Submission.Vinogradov
