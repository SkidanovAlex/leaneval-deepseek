/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.Lemma38Step4
import Submission.Vinogradov.CurveDecProj

/-!
# GLYZ Lemma 3.8, step 4 (caller layer): discharging the two side conditions

Lane 4's main inequality `Lemma38Step4.asymAV_le_curveDecLocR` takes two side conditions as input:
the localised decoupling `CurveDecLocR` for the reparametrised projected curve, and the class
hypothesis for the sub-block sums at the translate `H + u`.  This module discharges both:

**Discharge 1 (the enlargement `lam`).**  `lamProj l k cL` is the *fixed* constant
`max 1 ((2^(l+2) · 2^(k−l+1) / cL)^(1/l))`, chosen so that the numerical hypothesis `hρlR` of
`CurveDecProj.curveDecLocR_intervalCurve_proj` holds automatically (section 1).  The two arithmetic
inputs it needs are `hBallR_eq` (the ball radius of Lemma A.2 is `2^((m'+1)(k−l+1))`) and
`hBallR_ge_pow` (the radius threshold `R₀ = hBallR k l m'` dominates `mt^l`).

**Discharge 2 (the class).**  `exists_class_subBlk` extracts the witness `λ₀` of
`CurveDecLocStep.exists_isFourierRep_subBlk_intervalCurve` and returns the class statement at the
enlargement `lam/(2·mt)` whenever `λ₀ · 8 · plateHalf M · 2^m ≤ lam` — using `IsFourierRep.congr`
for the order flip `Ψ y + u ↦ u + Ψ y` and `IsFourierRep.mono` for the enlargement.
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

/-! ## 1. The ball radius and the fixed enlargement -/

/-- The ball radius of GLYZ Lemma A.2, in closed form: `hBallR k l m' = 2^((m'+1)(k−l+1))`. -/
lemma hBallR_eq (k l m' : ℕ) :
    hBallR k l m' = ((2 : ℝ) ^ (m' + 1)) ^ (k - l + 1) := by
  rw [hBallR, plateHalf, one_div, inv_inv]

lemma hBallR_eq_exp (k l m' : ℕ) :
    hBallR k l m' = (2 : ℝ) ^ ((m' + 1) * (k - l + 1)) := by
  rw [hBallR_eq, pow_mul]

/-- **The radius threshold is dominated by `hBallR`**: `(2^(M−m))^l ≤ hBallR k l m'` as soon as
`M` is the refined level `refLvl l k m'`. -/
lemma hBallR_ge_pow {k l m M m' : ℕ} (hM : M = refLvl l k m') :
    (((2 ^ (M - m) : ℕ)) : ℝ) ^ l ≤ hBallR k l m' := by
  have hcast : (((2 ^ (M - m) : ℕ)) : ℝ) = (2 : ℝ) ^ (M - m) := by push_cast; ring
  have hMl : M * l ≤ (k - l + 1) * m' := by
    rw [hM, refLvl]; exact Nat.div_mul_le_self _ _
  have hexp : (M - m) * l ≤ (m' + 1) * (k - l + 1) := by
    calc (M - m) * l ≤ M * l := Nat.mul_le_mul_right _ (Nat.sub_le M m)
      _ ≤ (k - l + 1) * m' := hMl
      _ ≤ (k - l + 1) * (m' + 1) := Nat.mul_le_mul_left _ (Nat.le_succ _)
      _ = (m' + 1) * (k - l + 1) := Nat.mul_comm _ _
  rw [hcast, hBallR_eq_exp, ← pow_mul]
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexp

/-- **The fixed plate enlargement for the projected curve**: chosen so that the numerical
hypothesis `hρlR` of `curveDecLocR_intervalCurve_proj` becomes automatic. -/
noncomputable def lamProj (l k : ℕ) (cL : ℝ) : ℝ :=
  max 1 (((2 : ℝ) ^ (l + 2) * (2 : ℝ) ^ (k - l + 1) / cL) ^ ((1 : ℝ) / l))

lemma one_le_lamProj (l k : ℕ) (cL : ℝ) : 1 ≤ lamProj l k cL := le_max_left _ _

lemma lamProj_nonneg (l k : ℕ) (cL : ℝ) : 0 ≤ lamProj l k cL :=
  le_trans zero_le_one (one_le_lamProj l k cL)

/-- The defining lower bound for `lamProj`. -/
lemma lamProj_pow_ge {l k : ℕ} (hl : 1 ≤ l) {cL : ℝ} (hcL : 0 < cL) :
    (2 : ℝ) ^ (l + 2) * (2 : ℝ) ^ (k - l + 1) / cL ≤ (lamProj l k cL) ^ l := by
  have hl0 : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl
  set X : ℝ := (2 : ℝ) ^ (l + 2) * (2 : ℝ) ^ (k - l + 1) / cL with hX
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hls : (1 : ℝ) / l * (l : ℝ) = 1 := by field_simp
  have h1 : X = (X ^ ((1 : ℝ) / l)) ^ l := by
    rw [← Real.rpow_natCast (X ^ ((1 : ℝ) / l)) l, ← Real.rpow_mul hX0, hls, Real.rpow_one]
  rw [h1]
  exact pow_le_pow_left₀ (Real.rpow_nonneg hX0 _) (le_max_right _ _) l

/-- The base identity: `(1/2^m)^l / (2^(M-m))^l = (1/2^M)^l`. -/
lemma inv_pow_div_eq {m M l : ℕ} (hmM : m ≤ M) :
    (1 / (2 : ℝ) ^ m) ^ l / ((2 : ℝ) ^ (M - m)) ^ l = (1 / (2 : ℝ) ^ M) ^ l := by
  have h1 : (1 / (2 : ℝ) ^ m) / ((2 : ℝ) ^ (M - m)) = 1 / (2 : ℝ) ^ M := by
    rw [div_div, ← pow_add, Nat.add_sub_cancel' hmM]
  rw [← div_pow, h1]

/-- **Discharge 1's numerical hypothesis `hρlR`.**  For the fixed enlargement `lamProj l k cL`,
the condition `2^(l+2) ≤ (cL c^l)(hBallR/mt^l) lam^l` holds for every level `m` and every refined
level `M = refLvl l k m'`. -/
lemma hρlR_lamProj {k l m M m' : ℕ} (hl : 1 ≤ l) (hlk : l ≤ k) {cL : ℝ} (hcL : 0 < cL)
    (hmM : m ≤ M) (hM : M = refLvl l k m') :
    (2 : ℝ) ^ (l + 2)
      ≤ (cL * (1 / (2 : ℝ) ^ m) ^ l)
          * (hBallR k l m' / ((2 : ℝ) ^ (M - m)) ^ l) * (lamProj l k cL) ^ l := by
  set P : ℝ := lamProj l k cL with hP
  have hPl : (2 : ℝ) ^ (l + 2) * (2 : ℝ) ^ (k - l + 1) / cL ≤ P ^ l := by
    rw [hP]; exact lamProj_pow_ge hl hcL
  have hMl : M * l ≤ (k - l + 1) * m' := by
    rw [hM, refLvl]; exact Nat.div_mul_le_self _ _
  have hbase := inv_pow_div_eq (l := l) hmM
  -- the reduced inequality
  have hmain : (2 : ℝ) ^ (l + 2) ≤ hBallR k l m' * (2 : ℝ) ^ (k + 3) / (2 : ℝ) ^ (M * l) := by
    have hexp : (l + 2) + M * l ≤ (m' + 1) * (k - l + 1) + (k + 3) := by
      have h2 : (k - l + 1) * m' ≤ (k - l + 1) * (m' + 1) := Nat.mul_le_mul_left _ (Nat.le_succ _)
      have h3 : (k - l + 1) * (m' + 1) = (m' + 1) * (k - l + 1) := Nat.mul_comm _ _
      omega
    rw [hBallR_eq_exp]
    have hnum : (2 : ℝ) ^ ((m' + 1) * (k - l + 1)) * (2 : ℝ) ^ (k + 3)
        = (2 : ℝ) ^ ((m' + 1) * (k - l + 1) + (k + 3)) := (pow_add _ _ _).symm
    rw [hnum, le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (M * l))]
    have hlhs : (2 : ℝ) ^ (l + 2) * (2 : ℝ) ^ (M * l)
        = (2 : ℝ) ^ ((l + 2) + M * l) := (pow_add _ _ _).symm
    rw [hlhs]
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexp
  -- assemble
  have hkey : (cL * (1 / (2 : ℝ) ^ m) ^ l) * (hBallR k l m' / ((2 : ℝ) ^ (M - m)) ^ l)
      = cL * hBallR k l m' * (1 / (2 : ℝ) ^ M) ^ l := by
    calc (cL * (1 / (2 : ℝ) ^ m) ^ l) * (hBallR k l m' / ((2 : ℝ) ^ (M - m)) ^ l)
        = cL * ((1 / (2 : ℝ) ^ m) ^ l / ((2 : ℝ) ^ (M - m)) ^ l) * hBallR k l m' := by ring
      _ = cL * (1 / (2 : ℝ) ^ M) ^ l * hBallR k l m' := by rw [hbase]
      _ = cL * hBallR k l m' * (1 / (2 : ℝ) ^ M) ^ l := by ring
  have hId : cL * hBallR k l m' * (1 / (2 : ℝ) ^ M) ^ l
      * ((2 : ℝ) ^ (l + 2) * (2 : ℝ) ^ (k - l + 1) / cL)
      = hBallR k l m' * (2 : ℝ) ^ (k + 3) / (2 : ℝ) ^ (M * l) := by
    have h2p : (2 : ℝ) ^ (l + 2) * (2 : ℝ) ^ (k - l + 1) = (2 : ℝ) ^ (k + 3) := by
      rw [← pow_add]; congr 1; omega
    have h3p : (1 / (2 : ℝ) ^ M) ^ l = 1 / (2 : ℝ) ^ (M * l) := by
      rw [one_div, inv_pow, ← pow_mul, one_div]
    rw [h2p, h3p]
    field_simp
  rw [hkey]
  refine le_trans hmain ?_
  rw [← hId]
  exact mul_le_mul_of_nonneg_left hPl
    (mul_nonneg (mul_nonneg hcL.le (hBallR_pos k l m').le) (pow_nonneg (by positivity) l))

/-! ## 2. Discharge 1: the localised decoupling at the fixed enlargement -/

theorem exists_curveDecLocR_proj {k l m M m' : ℕ} (hl : 1 ≤ l) (hlk : l ≤ k) {ξ' : ℝ}
    (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1)
    {cL R : ℝ} (hcL : 0 < cL) (hR : 0 < R)
    (hplate : ∀ t ∈ Set.Icc (0 : ℝ) 1, 1 / 4 ≤ |t - ξ'| →
      PlateLowerAt l (projCurveDeriv k l (torsionVec k l hlk ξ')) cL t)
    (htay : CurveTaylorTop l (projCurveDeriv k l (torsionVec k l hlk ξ')) R)
    {a₀ εm A : ℝ} (ha1 : 1 ≤ a₀) (hεm : 0 < εm) (hA : 0 ≤ A)
    (hm : 1 ≤ m) (hmM : m ≤ M) (q : Fin (2 ^ m))
    (hsepI : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      1 / 4 ≤ |((q : ℕ) : ℝ) / (2 : ℝ) ^ m + (1 / (2 : ℝ) ^ m) * t - ξ'|)
    (hM : M = refLvl l k m')
    (h4 : 4 ≤ 2 ^ (M - m)) (hlam2 : 2 * lamProj l k cL ≤ (2 : ℝ) ^ (M - m))
    (hmMod : ∀ M' : ℕ, 1 ≤ M' → DecLinScale l M' (towerEnlP l cL R (2 * lamProj l k cL))
      (ENNReal.ofReal (a₀ * (M' : ℝ) ^ εm))) :
    ∃ C : ℝ≥0∞, CurveDecLocR l
      (intervalCurve l (((q : ℕ) : ℝ) / (2 : ℝ) ^ m) (1 / (2 : ℝ) ^ m)
        (projCurveDeriv k l (torsionVec k l hlk ξ')))
      (2 ^ (M - m)) (lamProj l k cL) A (hBallR k l m') C := by
  have hge : (((2 ^ (M - m) : ℕ) : ℝ)) ^ l ≤ hBallR k l m' := hBallR_ge_pow (l := l) hM
  have hρ := hρlR_lamProj (m := m) (M := M) (m' := m') hl hlk hcL hmM hM
  have hcast : (((2 ^ (M - m) : ℕ)) : ℝ) = (2 : ℝ) ^ (M - m) := by push_cast; ring
  have hρ' : (2 : ℝ) ^ (l + 2) ≤ cL * (1 / (2 : ℝ) ^ m) ^ l
      * (hBallR k l m' / (((2 ^ (M - m) : ℕ)) : ℝ) ^ l) * (lamProj l k cL) ^ l := by
    rw [hcast]; exact hρ
  exact curveDecLocR_intervalCurve_proj hl hlk hξ' hcL hR hplate htay ha1 hεm
    (one_le_lamProj l k cL) hm hmM h4 q hsepI hlam2 hge hρ' hA hmMod

/-! ## 3. Discharge 2: the class of the sub-block sums at the translate -/

theorem exists_class_subBlk {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k) {ξ' : ℝ}
    (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1) :
    ∃ lamB : ℝ, 1 ≤ lamB ∧ ∀ {N m M : ℕ} (h2m : 2 ≤ m) (hmM : m ≤ M) (hMN : M ≤ N)
      (q : Fin (2 ^ m))
      (hsep : ∀ j : Fin (2 ^ (M - m)),
        1 / 4 ≤ |pieceCenter (2 ^ M) (subIdx m M hmM q j) - ξ'|)
      {lam : ℝ} (hlam8 : 8 * lamB ≤ lam)
      (u : E k) (f : Fin (2 ^ N) → E k → ℂ),
      (∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i)) →
      ∀ j : Fin (2 ^ (M - m)),
        IsFourierRep l
          (curvePlate l
            (intervalCurve l (((q : ℕ) : ℝ) / (2 : ℝ) ^ m) (1 / (2 : ℝ) ^ m)
              (projCurveDeriv k l (torsionVec k l hlk ξ')))
            (lam / (2 * ((2 ^ (M - m) : ℕ) : ℝ))) (pieceCenter (2 ^ (M - m)) j))
          (fun y => ∑ i ∈ blkFin N M (subIdx m M hmM q j),
            f i (u + projEmbedLin k l (torsionVec k l hlk ξ') y)) := by
  obtain ⟨lamB, hlamB1, hlamB⟩ := exists_isFourierRep_subBlk_intervalCurve hk hl hlk hξ'
  refine ⟨lamB, hlamB1, ?_⟩
  intro N m M h2m hmM hMN q hsep lam hlam8 u f hf j
  have h0 := hlamB h2m hmM hMN q hsep u f hf j
  have hflip : IsFourierRep l
      (curvePlate l
        (intervalCurve l (((q : ℕ) : ℝ) / (2 : ℝ) ^ m) (1 / (2 : ℝ) ^ m)
          (projCurveDeriv k l (torsionVec k l hlk ξ')))
        (lamB * (8 * plateHalf M) * (2 : ℝ) ^ m) (pieceCenter (2 ^ (M - m)) j))
      (fun y => ∑ i ∈ blkFin N M (subIdx m M hmM q j),
        f i (u + projEmbedLin k l (torsionVec k l hlk ξ') y)) :=
    IsFourierRep.congr h0 fun y => Finset.sum_congr rfl fun i _ => by rw [add_comm]
  refine IsFourierRep.mono ?_ hflip
  refine curvePlate_mono ?_ ?_
  · have hp : (0 : ℝ) ≤ 8 * plateHalf M := by
      rw [plateHalf]; positivity
    exact mul_nonneg (mul_nonneg (le_trans zero_le_one hlamB1) hp) (by positivity)
  · have hmtp : (0 : ℝ) < ((2 ^ (M - m) : ℕ) : ℝ) := by positivity
    have hph' : 8 * plateHalf M * (2 : ℝ) ^ m = 4 / ((2 ^ (M - m) : ℕ) : ℝ) := by
      have hcast : ((2 ^ (M - m) : ℕ) : ℝ) = (2 : ℝ) ^ (M - m) := by push_cast; ring
      have h2 : (2 : ℝ) ^ (M + 1) = (2 : ℝ) ^ (M - m) * (2 : ℝ) ^ m * 2 := by
        rw [← pow_add, ← pow_succ]
        congr 1
        omega
      rw [plateHalf, hcast, h2]
      field_simp
      ring
    have h4 : 4 * lamB ≤ lam / 2 := by linarith [hlam8]
    calc lamB * (8 * plateHalf M) * (2 : ℝ) ^ m
        = lamB * (8 * plateHalf M * (2 : ℝ) ^ m) := mul_assoc _ _ _
      _ = lamB * (4 / ((2 ^ (M - m) : ℕ) : ℝ)) := by rw [hph']
      _ = (4 * lamB) / ((2 ^ (M - m) : ℕ) : ℝ) := by ring
      _ ≤ (lam / 2) / ((2 ^ (M - m) : ℕ) : ℝ) := div_le_div_of_nonneg_right h4 hmtp.le
      _ = lam / (2 * ((2 ^ (M - m) : ℕ) : ℝ)) := by ring

/-- `hρlR` is monotone in the enlargement: it holds for every `lam ≥ lamProj l k cL`. -/
lemma hρlR_mono {k l m M m' : ℕ} (hl : 1 ≤ l) (hlk : l ≤ k) {cL lam : ℝ} (hcL : 0 < cL)
    (hmM : m ≤ M) (hM : M = refLvl l k m') (hlam : lamProj l k cL ≤ lam) :
    (2 : ℝ) ^ (l + 2)
      ≤ (cL * (1 / (2 : ℝ) ^ m) ^ l)
          * (hBallR k l m' / ((2 : ℝ) ^ (M - m)) ^ l) * lam ^ l := by
  have h0 := hρlR_lamProj (m := m) (M := M) (m' := m') hl hlk hcL hmM hM
  refine h0.trans ?_
  have hp : (lamProj l k cL) ^ l ≤ lam ^ l :=
    pow_le_pow_left₀ (lamProj_nonneg l k cL) hlam l
  have hfac : (0 : ℝ) ≤ (cL * (1 / (2 : ℝ) ^ m) ^ l)
      * (hBallR k l m' / ((2 : ℝ) ^ (M - m)) ^ l) :=
    mul_nonneg (mul_nonneg hcL.le (pow_nonneg (by positivity) l))
      (div_nonneg (hBallR_pos k l m').le (pow_nonneg (by positivity) l))
  exact mul_le_mul_of_nonneg_left hp hfac

/-! ## 4. The assembly: lane 4 with both side conditions discharged -/

/-- **Lane 4, assembled.**  There is a constant `Λ₀` (the maximum of the fixed plate enlargement
`lamProj l k cL` and `8 λ₀`, where `λ₀` is the witness of the class transport) such that for every
`lam ≥ Λ₀` with `2 lam ≤ 2^(M−m)` the localised decoupling of the `H`-ball average holds:

  `∫⁻_{w ∈ B_H(0,r)} (‖f_I (u + Ψ w)‖₊)^{p_l}
     ≤ |B_H(0,r)| · C^{p_l} · (∑_{J ∈ subBlkLvl m M q} TN_J (u)^{2/p_l})^{p_l/2}`.

`hdec` comes from `exists_curveDecLocR_proj` and `hclass` from `exists_class_subBlk`, and the
model hypothesis is the degree-`l` induction hypothesis at the enlargement `towerEnlP l cL R
(2 lam)`. -/
theorem exists_asymAV_le_proj {k l N m M m' : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k)
    (h2m : 2 ≤ m) (hmM : m ≤ M) (hMN : M ≤ N)
    {ξ' : ℝ} (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1) (q : Fin (2 ^ m))
    (hsepI : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      1 / 4 ≤ |((q : ℕ) : ℝ) / (2 : ℝ) ^ m + (1 / (2 : ℝ) ^ m) * t - ξ'|)
    (hsep : ∀ j : Fin (2 ^ (M - m)),
      1 / 4 ≤ |pieceCenter (2 ^ M) (subIdx m M hmM q j) - ξ'|)
    {cL R : ℝ} (hcL : 0 < cL) (hR : 0 < R)
    (hplate : ∀ t ∈ Set.Icc (0 : ℝ) 1, 1 / 4 ≤ |t - ξ'| →
      PlateLowerAt l (projCurveDeriv k l (torsionVec k l hlk ξ')) cL t)
    (htay : CurveTaylorTop l (projCurveDeriv k l (torsionVec k l hlk ξ')) R)
    {a₀ εm A : ℝ} (ha1 : 1 ≤ a₀) (hεm : 0 < εm) (hA : 0 ≤ A)
    (hm : 1 ≤ m) (hM : M = refLvl l k m') (h4 : 4 ≤ 2 ^ (M - m))
    {f : Fin (2 ^ N) → E k → ℂ}
    (hf : ∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i))
    (u : E k) {r : ℝ} (hrR : hBallR k l m' ≤ r) :
    ∃ Λ₀ : ℝ, 1 ≤ Λ₀ ∧ ∀ {lam : ℝ}, Λ₀ ≤ lam → 2 * lam ≤ (2 : ℝ) ^ (M - m) →
      (∀ M' : ℕ, 1 ≤ M' → DecLinScale l M' (towerEnlP l cL R (2 * lam))
        (ENNReal.ofReal (a₀ * (M' : ℝ) ^ εm))) →
      ∃ C : ℝ≥0∞,
        (∫⁻ w in Metric.ball (0 : E l) r,
            (‖∑ i ∈ blkFin N m q,
              f i (u + projEmbedLin k l (torsionVec k l hlk ξ') w)‖₊ : ℝ≥0∞) ^ (plExp l))
          ≤ ENNReal.ofReal ((volume (Metric.ball (0 : E l) r)).toReal) * C ^ (plExp l)
            * (∑ J ∈ subBlkLvl m M q,
                (tentNorm l A 0 r (fun y : E l => ∑ i ∈ blkFin N M J,
                  f i (u + projEmbedLin k l (torsionVec k l hlk ξ') y))) ^ (2 / plExp l))
              ^ (plExp l / 2) := by
  obtain ⟨lamB, hlamB1, hclassB⟩ := exists_class_subBlk hk hl hlk hξ'
  refine ⟨max (lamProj l k cL) (8 * lamB), ?_, ?_⟩
  · exact le_trans (one_le_lamProj l k cL) (le_max_left _ _)
  · intro lam hlam hlam2 hmMod
    have hcast : (((2 ^ (M - m) : ℕ)) : ℝ) = (2 : ℝ) ^ (M - m) := by push_cast; ring
    have hρ : (2 : ℝ) ^ (l + 2) ≤ cL * (1 / (2 : ℝ) ^ m) ^ l
        * (hBallR k l m' / (((2 ^ (M - m) : ℕ)) : ℝ) ^ l) * lam ^ l := by
      rw [hcast]
      exact hρlR_mono hl hlk hcL hmM hM (le_trans (le_max_left _ _) hlam)
    have hge : (((2 ^ (M - m) : ℕ)) : ℝ) ^ l ≤ hBallR k l m' := hBallR_ge_pow (l := l) hM
    obtain ⟨C, hdec⟩ := curveDecLocR_intervalCurve_proj hl hlk hξ' hcL hR hplate htay
      ha1 hεm (le_trans (one_le_lamProj l k cL) (le_trans (le_max_left _ _) hlam))
      hm hmM h4 q hsepI hlam2 hge hρ hA hmMod
    have hclass := hclassB h2m hmM hMN q hsep (le_trans (le_max_right _ _) hlam) u f hf
    exact ⟨C, asymAV_le_curveDecLocR hl hlk hmM hMN q (u := u) hA hrR hdec hclass⟩

/-! ## 5. The arithmetic obligation `2 Λ₀ ≤ 2^(M−m)` -/

/-- **The arithmetic obligation of the lane-4 interface.**  For every real `Λ₀` there is a
threshold `K` such that `2 Λ₀ ≤ 2^n` for all `n ≥ K`.  Applied with `n = M − m` and
`Λ₀ = max (lamProj l k cL) (8 λ₀)` this is the side condition `2 Λ₀ ≤ 2^(M−m)` handed off by
`exists_asymAV_le_proj`.

The point of stating it separately is that `Λ₀` is a *fixed* constant of the induction (it depends
only on `k`, `l`, `cL` and `ξ'`, not on the level), so the threshold `K` is fixed too, and the
condition is met as soon as the level gap `M − m` is large enough. -/
lemma exists_two_mul_le_two_pow (Λ₀ : ℝ) :
    ∃ K : ℕ, ∀ {n : ℕ}, K ≤ n → 2 * Λ₀ ≤ (2 : ℝ) ^ n := by
  have htend : Filter.Tendsto (fun n : ℕ => (2 : ℝ) ^ n) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
  have hev := htend.eventually_ge_atTop (max 1 (2 * Λ₀))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨K, hK⟩ := hev
  exact ⟨K, fun {n} hn => le_trans (le_max_right _ _) (hK n hn)⟩

/-- **The lane-4 interface with the arithmetic obligation discharged.**  The assembly
`exists_asymAV_le_proj` returns a threshold `Λ₀`; this version returns in addition the integer `K`
witnessing that `2 Λ₀ ≤ 2^n` for every `n ≥ K` — so for `M − m ≥ K` the side condition
`2 Λ₀ ≤ 2^(M−m)` holds and the caller may take `lam := Λ₀`. -/
theorem exists_asymAV_le_proj_K {k l N m M m' : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k)
    (h2m : 2 ≤ m) (hmM : m ≤ M) (hMN : M ≤ N)
    {ξ' : ℝ} (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1) (q : Fin (2 ^ m))
    (hsepI : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      1 / 4 ≤ |((q : ℕ) : ℝ) / (2 : ℝ) ^ m + (1 / (2 : ℝ) ^ m) * t - ξ'|)
    (hsep : ∀ j : Fin (2 ^ (M - m)),
      1 / 4 ≤ |pieceCenter (2 ^ M) (subIdx m M hmM q j) - ξ'|)
    {cL R : ℝ} (hcL : 0 < cL) (hR : 0 < R)
    (hplate : ∀ t ∈ Set.Icc (0 : ℝ) 1, 1 / 4 ≤ |t - ξ'| →
      PlateLowerAt l (projCurveDeriv k l (torsionVec k l hlk ξ')) cL t)
    (htay : CurveTaylorTop l (projCurveDeriv k l (torsionVec k l hlk ξ')) R)
    {a₀ εm A : ℝ} (ha1 : 1 ≤ a₀) (hεm : 0 < εm) (hA : 0 ≤ A)
    (hm : 1 ≤ m) (hM : M = refLvl l k m') (h4 : 4 ≤ 2 ^ (M - m))
    {f : Fin (2 ^ N) → E k → ℂ}
    (hf : ∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i))
    (u : E k) {r : ℝ} (hrR : hBallR k l m' ≤ r) :
    ∃ Λ₀ : ℝ, 1 ≤ Λ₀ ∧ ∃ K : ℕ, (∀ {n : ℕ}, K ≤ n → 2 * Λ₀ ≤ (2 : ℝ) ^ n) ∧
      (K ≤ M - m → ∀ {lam : ℝ}, Λ₀ ≤ lam → 2 * lam ≤ (2 : ℝ) ^ (M - m) →
        (∀ M' : ℕ, 1 ≤ M' → DecLinScale l M' (towerEnlP l cL R (2 * lam))
          (ENNReal.ofReal (a₀ * (M' : ℝ) ^ εm))) →
        ∃ C : ℝ≥0∞,
          (∫⁻ w in Metric.ball (0 : E l) r,
              (‖∑ i ∈ blkFin N m q,
                f i (u + projEmbedLin k l (torsionVec k l hlk ξ') w)‖₊ : ℝ≥0∞) ^ (plExp l))
            ≤ ENNReal.ofReal ((volume (Metric.ball (0 : E l) r)).toReal) * C ^ (plExp l)
              * (∑ J ∈ subBlkLvl m M q,
                  (tentNorm l A 0 r (fun y : E l => ∑ i ∈ blkFin N M J,
                    f i (u + projEmbedLin k l (torsionVec k l hlk ξ') y))) ^ (2 / plExp l))
                ^ (plExp l / 2)) := by
  obtain ⟨Λ₀, hΛ₀1, hΛ₀⟩ := exists_asymAV_le_proj hk hl hlk h2m hmM hMN hξ' q hsepI hsep
    hcL hR hplate htay ha1 hεm hA hm hM h4 hf u hrR
  obtain ⟨K, hK⟩ := exists_two_mul_le_two_pow Λ₀
  exact ⟨Λ₀, hΛ₀1, K, hK, fun _ => hΛ₀⟩

end Submission.Vinogradov
