/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.AsymExpCrude
import Submission.Vinogradov.DescentStep

/-!
# The localised-decoupling bridge `DecLinScale ⟷ AsymDec` (GLYZ §4)

The `l = 0` slot of `AsymDec` is the entry point of the remaining critical path of §4:
`A_0(b) = η(1−b)` (GLYZ (4.3)), the finiteness bounds (4.6)/(4.7), and the recursion at `l = 1` all
need to pass between the *global* linear decoupling constant `DecLinScale` and the *localised*
bilinear one `AsymDec · 0`.

**Step 1 (this file).**  Because `plExp 0 = 0`, the first slot of `AsymDec k hk 0 N m₁ m₂ C`
contributes only `convPow k 0 … = ∫⁻ Φ_q = uncConst k hk` (a constant, by `lintegral_platePhi`) and
an `ℓ²`-factor `(…)^0 = 1`.  `asymDec_zero_unpack` isolates what is left: the **localised** linear
`L^{p_k}` inequality inside the block `q'`,

  `uncConst · ∫⁻ (|∑_{i ∈ blk q'} f i|^{p_k} ∗ Φ_{q'})  ≤  C^{p_k} · (ℓ²_{q'})^{p_k}`.

That is the shape on which both directions of the bridge act:

* **(⋆) fine ⟹ coarse** (`m₂' ≤ m₂`): the direction needed for the recursion at `l = 1`;
* **`DecLinScale ⟹ AsymDec 0`**: the direction needed for (4.3)/(4.6)/(4.7) — and, under exit (B)
  of ROADMAP session 67, for `l = 1` as well.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 16000000

namespace Submission.Vinogradov

set_option maxHeartbeats 32000000 in
/-- **The `l = 0` slot of the bridge, first step.**  Unpacking `AsymDec k hk 0 N m₁ m₂ C`: the
first slot's `convPow` is the total mass `∫⁻ Φ_q = uncConst k hk` of the local bump (a constant,
independent of the data) and its `ℓ²`-factor is `(…)^(plExp 0) = 1`, leaving the localised linear
`L^{p_k}` inequality inside the block `q'`. -/
theorem asymDec_zero_unpack {k : ℕ} (hk : 1 ≤ k) {N m₁ m₂ : ℕ} {C : ℝ≥0∞}
    (h : AsymDec k hk 0 N m₁ m₂ C) {q : Fin (2 ^ m₁)} {q' : Fin (2 ^ m₂)}
    (hsep : sepLevel m₁ m₂ q q') (f : Fin (2 ^ N) → E k → ℂ)
    (hf : ∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i)) :
    uncConst k hk * (∫⁻ x, convPow k (pkExp k) (fun x => ∑ i ∈ blkFin N m₂ q', f i x)
          (platePhi k hk (plateHalf m₂) (pieceCenter (2 ^ m₂) q')) x)
      ≤ C ^ (pkExp k)
        * (l2Of (blkFin N m₂ q') fun i => lpNorm k (pE k) (f i)) ^ (pkExp k) := by
  have hδm : plateHalf m₁ ≠ 0 := by rw [plateHalf]; positivity
  have hkey := h q q' hsep f hf
  have hFm : Measurable (fun x : E k => ∑ i ∈ blkFin N m₂ q', f i x) :=
    Finset.measurable_sum _ (fun i _ => (hf i).continuous.measurable)
  have hΦm : Measurable (platePhi k hk (plateHalf m₂) (pieceCenter (2 ^ m₂) q')) :=
    (continuous_platePhi k hk _ _).measurable
  have hgm : AEMeasurable (fun x : E k => convPow k (pkExp k)
      (fun x => ∑ i ∈ blkFin N m₂ q', f i x)
      (platePhi k hk (plateHalf m₂) (pieceCenter (2 ^ m₂) q')) x) volume :=
    (measurable_convPow k _ hFm hΦm).aemeasurable
  have hconst : ∀ x : E k, convPow k 0 (fun x => ∑ i ∈ blkFin N m₁ q, f i x)
      (platePhi k hk (plateHalf m₁) (pieceCenter (2 ^ m₁) q)) x = uncConst k hk := by
    intro x
    rw [convPow_exp_zero]
    exact lintegral_platePhi hk (plateHalf m₁) (pieceCenter (2 ^ m₁) q) hδm
  have hL : (∫⁻ x, convPow k (plExp 0) (fun x => ∑ i ∈ blkFin N m₁ q, f i x)
        (platePhi k hk (plateHalf m₁) (pieceCenter (2 ^ m₁) q)) x
      * convPow k (pkExp k - plExp 0) (fun x => ∑ i ∈ blkFin N m₂ q', f i x)
        (platePhi k hk (plateHalf m₂) (pieceCenter (2 ^ m₂) q')) x)
      = uncConst k hk * (∫⁻ x, convPow k (pkExp k) (fun x => ∑ i ∈ blkFin N m₂ q', f i x)
          (platePhi k hk (plateHalf m₂) (pieceCenter (2 ^ m₂) q')) x) := by
    rw [show plExp 0 = 0 from plExp_zero, show pkExp k - 0 = pkExp k from sub_zero _]
    rw [show (fun x : E k => convPow k 0 (fun x => ∑ i ∈ blkFin N m₁ q, f i x)
          (platePhi k hk (plateHalf m₁) (pieceCenter (2 ^ m₁) q)) x
        * convPow k (pkExp k) (fun x => ∑ i ∈ blkFin N m₂ q', f i x)
          (platePhi k hk (plateHalf m₂) (pieceCenter (2 ^ m₂) q')) x)
        = fun x : E k => uncConst k hk * convPow k (pkExp k)
          (fun x => ∑ i ∈ blkFin N m₂ q', f i x)
          (platePhi k hk (plateHalf m₂) (pieceCenter (2 ^ m₂) q')) x from
      funext fun x => by rw [hconst x]]
    rw [lintegral_const_mul'' (f := fun x : E k => convPow k (pkExp k)
      (fun x => ∑ i ∈ blkFin N m₂ q', f i x)
      (platePhi k hk (plateHalf m₂) (pieceCenter (2 ^ m₂) q')) x) (uncConst k hk) hgm]
  have hR : C ^ (pkExp k) * (l2Of (blkFin N m₁ q) fun i => lpNorm k (pE k) (f i)) ^ (plExp 0)
        * (l2Of (blkFin N m₂ q') fun i => lpNorm k (pE k) (f i)) ^ (pkExp k - plExp 0)
      = C ^ (pkExp k) * (l2Of (blkFin N m₂ q') fun i => lpNorm k (pE k) (f i)) ^ (pkExp k) := by
    rw [show plExp 0 = 0 from plExp_zero, show pkExp k - 0 = pkExp k from sub_zero _,
      ENNReal.rpow_zero, mul_one]
  rw [← hL, ← hR]
  exact hkey


/-! ## The `lam`-monotonicity of `DecLinScale`

`plateScale k M lam j = plate k (lam/(2M)) (pieceCenter M j)` **grows** with `lam`, so the class of
admissible tuples grows with `lam` and the statement `DecLinScale k M lam C` gets **stronger** as
`lam` grows.  Equivalently it is *anti-monotone* in `lam`:

  `DecLinScale k M lam' C → DecLinScale k M lam C`  for `0 ≤ lam ≤ lam'`.

This is what lets the block rescaling of brick 1 use the plate scale `plateHalf (N − m₂) = 1/(2M)`,
which is `plateScale k M lam j` at `lam = 1`, from a hypothesis stated at `lam = 2`. -/
lemma DecLinScale_lam_le {k M : ℕ} (hM : 0 < M) {lam lam' : ℝ} (h0 : 0 ≤ lam) (hlam : lam ≤ lam')
    {C : ℝ≥0∞} (hD : DecLinScale k M lam' C) : DecLinScale k M lam C := by
  intro f hf
  have hM2 : (0 : ℝ) < 2 * (M : ℝ) := by
    have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    linarith
  refine hD f (fun j => (hf j).mono ?_)
  exact plate_mono (div_nonneg h0 hM2.le) (div_le_div_of_nonneg_right hlam hM2.le)


/-! ## The bookkeeping of the block rescaling

For the block `q' : Fin (2^m₂)` and the sub-index `j : Fin (2^{N−m₂})`, the affine map
`affMap k ρ t₀` with `ρ := 2^{−m₂}`, `t₀ := q'/2^{m₂}` carries the *coarse* plate
`plateScale k (2^{N−m₂}) 1 j = plate k (1/(2·2^{N−m₂})) (pieceCenter (2^{N−m₂}) j)` onto the *fine*
plate `piecePlate k (2^N) (blkIdxFin N m₂ q' j)`.  `Plate.affMap_image_plate` reduces that to the
scalar identities proved here (`rescale_plate_half` for the scale, `rescale_pieceCenter` for the
centre). -/

/-- **The rescaled plate scale**: `2^{−m₂} · (1/(2·2^{N−m₂})) = plateHalf N`. -/
lemma rescale_plate_half {N m₂ : ℕ} (hm : m₂ ≤ N) :
    (2 : ℝ) ^ (-(m₂ : ℤ)) * (1 / (2 * ((2 ^ (N - m₂) : ℕ) : ℝ))) = plateHalf N := by
  have hsplit : (2 : ℝ) ^ m₂ * (2 : ℝ) ^ (N - m₂) = (2 : ℝ) ^ N := by
    rw [← pow_add, Nat.add_sub_cancel' hm]
  have h1 : ((2 : ℝ) ^ m₂) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h2 : (2 * (2 : ℝ) ^ (N - m₂)) ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))
  have hM : ((2 ^ (N - m₂) : ℕ) : ℝ) = (2 : ℝ) ^ (N - m₂) := by
    rw [Nat.cast_pow]; norm_num
  rw [hM, plateHalf, zpow_neg, zpow_natCast, pow_succ, ← hsplit]
  field_simp

/-- **The rescaled piece centre**: `2^{−m₂} · pieceCenter (2^{N−m₂}) j + q'/2^{m₂}` is the centre of
the fine piece `blkIdxFin N m₂ q' j` (`SymBilinear.blkIdxFin_val` supplies the index). -/
lemma rescale_pieceCenter {N m₂ : ℕ} (hm : m₂ ≤ N) (q' : Fin (2 ^ m₂))
    (j : Fin (2 ^ (N - m₂))) :
    (2 : ℝ) ^ (-(m₂ : ℤ)) * pieceCenter (2 ^ (N - m₂)) j + ((q' : ℕ) : ℝ) / 2 ^ m₂
      = pieceCenter (2 ^ N) (blkIdxFin N m₂ (q' : ℕ) j) := by
  have hidx := blkIdxFin_val hm q'.isLt j
  have hM : ((2 ^ (N - m₂) : ℕ) : ℝ) = (2 : ℝ) ^ (N - m₂) := by
    rw [Nat.cast_pow]; norm_num
  have hN : ((2 ^ N : ℕ) : ℝ) = (2 : ℝ) ^ N := by rw [Nat.cast_pow]; norm_num
  have hsplit : (2 : ℝ) ^ m₂ * (2 : ℝ) ^ (N - m₂) = (2 : ℝ) ^ N := by
    rw [← pow_add, Nat.add_sub_cancel' hm]
  rw [pieceCenter, pieceCenter, hidx, hM, hN, zpow_neg, zpow_natCast, ← hsplit]
  push_cast
  field_simp
  ring


/-! ## The block rescaling of the family (structural half of brick 1) -/

set_option maxHeartbeats 32000000 in
/-- **The block rescaling, per-piece form.**  For the block `q' : Fin (2^m₂)` and the affine map
`affMap k ρ t₀` (`ρ := 2^{−m₂}`, `t₀ := q'/2^{m₂}`), each fine piece of the block is a unimodular
phase times a member of the class over the *rescaled* plate
`plateScale k (2^{N−m₂}) 1 j`.  This is the precise form of the `|det|`-cancellation: every
`L^p`-norm on the left picks up the same factor. -/
theorem exists_block_rescale {k N m₂ : ℕ} (hk : 1 ≤ k) (hm : m₂ ≤ N) (q' : Fin (2 ^ m₂))
    (f : Fin (2 ^ N) → E k → ℂ)
    (hf : ∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i)) :
    ∃ g : Fin (2 ^ (N - m₂)) → E k → ℂ,
      (∀ j, IsFourierRep k (plateScale k (2 ^ (N - m₂)) 1 j) (g j)) ∧
      (∀ j x, f (blkIdxFin N m₂ (q' : ℕ) j) x
        = chat k x (gammaVec k (((q' : ℕ) : ℝ) / 2 ^ m₂))
          * g j (affVecLin k ((2 : ℝ) ^ (-(m₂ : ℤ))) (((q' : ℕ) : ℝ) / 2 ^ m₂) x)) := by
  classical
  have hρ0 : ((2 : ℝ) ^ (-(m₂ : ℤ))) ≠ 0 := zpow_ne_zero _ (by norm_num)
  have htrans : ∀ x y : E k,
      ⟪affVecLin k ((2 : ℝ) ^ (-(m₂ : ℤ))) (((q' : ℕ) : ℝ) / 2 ^ m₂) x, y⟫
        = ⟪x, affVecDualLin k ((2 : ℝ) ^ (-(m₂ : ℤ))) (((q' : ℕ) : ℝ) / 2 ^ m₂) y⟫ :=
    fun x y => inner_affVecLin k ((2 : ℝ) ^ (-(m₂ : ℤ))) (((q' : ℕ) : ℝ) / 2 ^ m₂) x y
  have hinj : Function.Injective (affVecDualLin k ((2 : ℝ) ^ (-(m₂ : ℤ))) (((q' : ℕ) : ℝ) / 2 ^ m₂)) :=
    (affVecDual_bijective k hρ0 _).injective
  have himg : ∀ j : Fin (2 ^ (N - m₂)),
      (fun ξ : E k => gammaVec k (((q' : ℕ) : ℝ) / 2 ^ m₂)
          + affVecDualLin k ((2 : ℝ) ^ (-(m₂ : ℤ))) (((q' : ℕ) : ℝ) / 2 ^ m₂) ξ)
        '' plateScale k (2 ^ (N - m₂)) 1 j
        = piecePlate k (2 ^ N) (blkIdxFin N m₂ (q' : ℕ) j) := by
    have h1 : (fun ξ : E k => gammaVec k (((q' : ℕ) : ℝ) / 2 ^ m₂)
          + affVecDualLin k ((2 : ℝ) ^ (-(m₂ : ℤ))) (((q' : ℕ) : ℝ) / 2 ^ m₂) ξ)
        = affMap k ((2 : ℝ) ^ (-(m₂ : ℤ))) (((q' : ℕ) : ℝ) / 2 ^ m₂) := rfl
    intro j
    rw [h1, plateScale, affMap_image_plate, rescale_plate_half hm, rescale_pieceCenter hm q',
      ← piecePlate_eq k N (blkIdxFin N m₂ (q' : ℕ) j)]
  choose g hg using fun j : Fin (2 ^ (N - m₂)) =>
    exists_isFourierRep_preimage k (affVecDualLin k ((2 : ℝ) ^ (-(m₂ : ℤ)))
        (((q' : ℕ) : ℝ) / 2 ^ m₂))
      (affVecLin k ((2 : ℝ) ^ (-(m₂ : ℤ))) (((q' : ℕ) : ℝ) / 2 ^ m₂)) htrans hinj
      (gammaVec k (((q' : ℕ) : ℝ) / 2 ^ m₂))
      (U := plateScale k (2 ^ (N - m₂)) 1 j)
      (f := f (blkIdxFin N m₂ (q' : ℕ) j))
      (by rw [himg j]; exact hf (blkIdxFin N m₂ (q' : ℕ) j))
  exact ⟨g, fun j => (hg j).1, fun j x => congrFun (hg j).2 x⟩

/-- **The block rescaling in summed form.** -/
lemma block_sum_rescale {k N m₂ : ℕ} (hm : m₂ ≤ N) (q' : Fin (2 ^ m₂))
    {f : Fin (2 ^ N) → E k → ℂ} {g : Fin (2 ^ (N - m₂)) → E k → ℂ}
    (hgid : ∀ j x, f (blkIdxFin N m₂ (q' : ℕ) j) x
        = chat k x (gammaVec k (((q' : ℕ) : ℝ) / 2 ^ m₂))
          * g j (affVecLin k ((2 : ℝ) ^ (-(m₂ : ℤ))) (((q' : ℕ) : ℝ) / 2 ^ m₂) x))
    (x : E k) :
    (∑ i ∈ blkFin N m₂ (q' : ℕ), f i x)
      = chat k x (gammaVec k (((q' : ℕ) : ℝ) / 2 ^ m₂))
        * (∑ j, g j (affVecLin k ((2 : ℝ) ^ (-(m₂ : ℤ))) (((q' : ℕ) : ℝ) / 2 ^ m₂) x)) := by
  rw [sum_blkFin_fin hm q'.isLt (fun i => f i x)]
  rw [Finset.sum_congr rfl (fun j _ => hgid j x), Finset.mul_sum]

/-- The `ℓ²`-functional is homogeneous. -/
lemma l2Of_mul_const {ι : Type*} (s : Finset ι) (c : ℝ≥0∞) (a : ι → ℝ≥0∞) :
    l2Of s (fun i => c * a i) = c * l2Of s a := by
  have h1 : (∑ i ∈ s, (c * a i) ^ (2 : ℝ)) = c ^ (2 : ℝ) * ∑ i ∈ s, a i ^ (2 : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ =>
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)
  rw [l2Of, l2Of, sqSum, sqSum, h1,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  congr 1
  rw [← ENNReal.rpow_mul]
  norm_num

/-- The `ℓ²`-functional respects pointwise equal families. -/
lemma l2Norm_congr {ι : Type*} [Fintype ι] {a b : ι → ℝ≥0∞} (h : ∀ i, a i = b i) :
    l2Norm a = l2Norm b := by
  rw [l2Norm, l2Norm]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [h i]

/-! ## The localised linear decoupling of a block -/

set_option maxHeartbeats 32000000 in
/-- **The localised linear decoupling of a block.**  From `DecLinScale` at the rescaled level
`2^{N−m₂}` — i.e. the linear decoupling inside the block `q'` — one gets the `L^{p_k}` bound for the
block sum against the `ℓ²`-norm of the fine pieces.  The `|det|`-factors of the two sides cancel
exactly (the per-piece identity of `exists_block_rescale`), which is why no determinant value and no
`δ`-loss occurs. -/
theorem lpNorm_block_le {k N m₂ : ℕ} (hk : 1 ≤ k) (hm : m₂ ≤ N) (q' : Fin (2 ^ m₂))
    {C₁ : ℝ≥0∞} (hD : DecLinScale k (2 ^ (N - m₂)) 1 C₁)
    {f : Fin (2 ^ N) → E k → ℂ}
    (hf : ∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i)) :
    lpNorm k (pE k) (fun x => ∑ i ∈ blkFin N m₂ (q' : ℕ), f i x)
      ≤ C₁ * l2Of (blkFin N m₂ (q' : ℕ)) (fun i => lpNorm k (pE k) (f i)) := by
  classical
  obtain ⟨g, hgc, hgi⟩ := exists_block_rescale hk hm q' f hf
  have hρ0 : ((2 : ℝ) ^ (-(m₂ : ℤ))) ≠ 0 := zpow_ne_zero _ (by norm_num)
  have hdet : LinearMap.det (affVecLin k ((2 : ℝ) ^ (-(m₂ : ℤ)))
      (((q' : ℕ) : ℝ) / 2 ^ m₂)) ≠ 0 :=
    det_affVecLin_ne_zero k hρ0 (((q' : ℕ) : ℝ) / 2 ^ m₂)
  set DET : ℝ≥0∞ := (ENNReal.ofReal |(LinearMap.det (affVecLin k ((2 : ℝ) ^ (-(m₂ : ℤ)))
      (((q' : ℕ) : ℝ) / 2 ^ m₂)))⁻¹|) ^ (1 / (pE k)).toReal with hDET
  have hper : ∀ j : Fin (2 ^ (N - m₂)),
      lpNorm k (pE k) (f (blkIdxFin N m₂ (q' : ℕ) j)) = DET * lpNorm k (pE k) (g j) := by
    intro j
    have hae : AEStronglyMeasurable (g j) (volume : Measure (E k)) :=
      (hgc j).continuous.aestronglyMeasurable
    have h := lpNorm_phase_comp_linearMap k (pE_ne_top k) hdet
      (gammaVec k (((q' : ℕ) : ℝ) / 2 ^ m₂)) (g := g j) hae
    have hL : lpNorm k (pE k) (f (blkIdxFin N m₂ (q' : ℕ) j))
        = lpNorm k (pE k) (fun x => chat k x (gammaVec k (((q' : ℕ) : ℝ) / 2 ^ m₂))
            * g j (affVecLin k ((2 : ℝ) ^ (-(m₂ : ℤ))) (((q' : ℕ) : ℝ) / 2 ^ m₂) x)) := by
      congr 1
      exact funext (hgi j)
    rw [hL, h, hDET]
  have hsum : lpNorm k (pE k) (fun x => ∑ i ∈ blkFin N m₂ (q' : ℕ), f i x)
      = DET * lpNorm k (pE k) (fun x => ∑ j, g j x) := by
    have hSm : AEStronglyMeasurable (fun x : E k => ∑ j, g j x) (volume : Measure (E k)) :=
      (continuous_finsetSum _ (fun j _ => (hgc j).continuous)).aestronglyMeasurable
    have h := lpNorm_phase_comp_linearMap k (pE_ne_top k) hdet
      (gammaVec k (((q' : ℕ) : ℝ) / 2 ^ m₂)) (g := fun x : E k => ∑ j, g j x) hSm
    have hL : lpNorm k (pE k) (fun x => ∑ i ∈ blkFin N m₂ (q' : ℕ), f i x)
        = lpNorm k (pE k) (fun x => chat k x (gammaVec k (((q' : ℕ) : ℝ) / 2 ^ m₂))
            * (∑ j, g j (affVecLin k ((2 : ℝ) ^ (-(m₂ : ℤ)))
                (((q' : ℕ) : ℝ) / 2 ^ m₂) x))) := by
      congr 1
      exact funext (block_sum_rescale hm q' hgi)
    rw [hL, h, hDET]
  have hdec := hD g hgc
  calc lpNorm k (pE k) (fun x => ∑ i ∈ blkFin N m₂ (q' : ℕ), f i x)
      = DET * lpNorm k (pE k) (fun x => ∑ j, g j x) := hsum
    _ ≤ DET * (C₁ * l2Norm (fun j => lpNorm k (pE k) (g j))) := by
        exact mul_le_mul' le_rfl hdec
    _ = C₁ * l2Norm (fun j => DET * lpNorm k (pE k) (g j)) := by
        rw [l2Norm_mul_const]; ring
    _ = C₁ * l2Of (blkFin N m₂ (q' : ℕ)) (fun i => lpNorm k (pE k) (f i)) := by
        congr 1
        rw [l2Of_blkFin_fin hm q'.isLt]
        refine l2Norm_congr fun j => ?_
        rw [hper j]

/-! ## The `l = 0` slot of the bridge: linear decoupling ⟹ `AsymDec 0` -/

/-- **The Fubini form of the `l = 0` left-hand side.**  With `plExp 0 = 0` the first slot of
`AsymDec k hk 0` contributes only the constant `∫⁻ Φ_q = uncConst k hk`, so the left-hand side is
`uncConst · ∫⁻ (|F|^{p_k} ∗ Φ_{q'})`. -/
lemma asymDec_zero_LHS_eq {k N m₁ m₂ : ℕ} (hk : 1 ≤ k) (q : Fin (2 ^ m₁)) (q' : Fin (2 ^ m₂))
    {f : Fin (2 ^ N) → E k → ℂ}
    (hFm : Measurable (fun x : E k => ∑ i ∈ blkFin N m₂ q', f i x)) :
    (∫⁻ x, convPow k (plExp 0) (fun x => ∑ i ∈ blkFin N m₁ q, f i x)
          (platePhi k hk (plateHalf m₁) (pieceCenter (2 ^ m₁) q)) x
        * convPow k (pkExp k - plExp 0) (fun x => ∑ i ∈ blkFin N m₂ q', f i x)
          (platePhi k hk (plateHalf m₂) (pieceCenter (2 ^ m₂) q')) x)
      = uncConst k hk * (∫⁻ x, convPow k (pkExp k) (fun x => ∑ i ∈ blkFin N m₂ q', f i x)
          (platePhi k hk (plateHalf m₂) (pieceCenter (2 ^ m₂) q')) x) := by
  have hδ₁ : plateHalf m₁ ≠ 0 := by rw [plateHalf]; positivity
  have hconst : ∀ x : E k, convPow k 0 (fun x => ∑ i ∈ blkFin N m₁ q, f i x)
      (platePhi k hk (plateHalf m₁) (pieceCenter (2 ^ m₁) q)) x = uncConst k hk := by
    intro x
    rw [convPow_exp_zero]
    exact lintegral_platePhi hk (plateHalf m₁) (pieceCenter (2 ^ m₁) q) hδ₁
  have hΦm : Measurable (platePhi k hk (plateHalf m₂) (pieceCenter (2 ^ m₂) q')) :=
    (continuous_platePhi k hk _ _).measurable
  have hgm : AEMeasurable (fun x : E k => convPow k (pkExp k)
      (fun x => ∑ i ∈ blkFin N m₂ q', f i x)
      (platePhi k hk (plateHalf m₂) (pieceCenter (2 ^ m₂) q')) x) volume :=
    (measurable_convPow k _ hFm hΦm).aemeasurable
  rw [show plExp 0 = 0 from plExp_zero, show pkExp k - (0 : ℝ) = pkExp k from sub_zero _]
  rw [show (fun x : E k => convPow k 0 (fun x => ∑ i ∈ blkFin N m₁ q, f i x)
        (platePhi k hk (plateHalf m₁) (pieceCenter (2 ^ m₁) q)) x
      * convPow k (pkExp k) (fun x => ∑ i ∈ blkFin N m₂ q', f i x)
        (platePhi k hk (plateHalf m₂) (pieceCenter (2 ^ m₂) q')) x)
      = fun x : E k => uncConst k hk * convPow k (pkExp k) (fun x => ∑ i ∈ blkFin N m₂ q', f i x)
        (platePhi k hk (plateHalf m₂) (pieceCenter (2 ^ m₂) q')) x from
    funext fun x => by rw [hconst x]]
  rw [lintegral_const_mul'' (uncConst k hk) hgm]

/-- **Linear decoupling implies the `l = 0` slot of the asymmetric bilinear inequality.**
This is the *favourable* direction of the localised-decoupling bridge: no level-gap loss occurs
(the `|det|`-factors cancel by `lpNorm_block_le`), so the `l = 0` exponent `A_0(b) = η(1−b)`
survives. -/
theorem asymDec_zero_of_decLinScale {k N m₁ m₂ : ℕ} (hk : 1 ≤ k) (hm : m₂ ≤ N)
    {C₁ : ℝ≥0∞} (hD : DecLinScale k (2 ^ (N - m₂)) 1 C₁) :
    AsymDec k hk 0 N m₁ m₂ ((uncConst k hk) ^ (2 / (pkExp k : ℝ)) * C₁) := by
  have hp : (0 : ℝ) < (pkExp k : ℝ) := by rw [pkExp]; positivity
  have hp0 : (pkExp k : ℝ) ≠ 0 := ne_of_gt hp
  intro q q' hsep f hf
  have hδ₂ : plateHalf m₂ ≠ 0 := by rw [plateHalf]; positivity
  have hFm : Measurable (fun x : E k => ∑ i ∈ blkFin N m₂ q', f i x) :=
    Finset.measurable_sum _ (fun i _ => (hf i).continuous.measurable)
  have hΦm : Measurable (platePhi k hk (plateHalf m₂) (pieceCenter (2 ^ m₂) q')) :=
    (continuous_platePhi k hk _ _).measurable
  have hK : ∫⁻ y, platePhi k hk (plateHalf m₂) (pieceCenter (2 ^ m₂) q') y = uncConst k hk :=
    lintegral_platePhi hk (plateHalf m₂) (pieceCenter (2 ^ m₂) q') hδ₂
  have hI : ∫⁻ x, convPow k (pkExp k) (fun x => ∑ i ∈ blkFin N m₂ q', f i x)
      (platePhi k hk (plateHalf m₂) (pieceCenter (2 ^ m₂) q')) x
      = uncConst k hk * (lpNorm k (pE k) (fun x => ∑ i ∈ blkFin N m₂ q', f i x)) ^ (pkExp k) := by
    rw [lintegral_convPow_eq k (pkExp k) hFm hΦm, hK, lintegral_nnnorm_rpow_pk k hk]
  have hblock := lpNorm_block_le hk hm q' hD hf
  have hC : ((uncConst k hk) ^ (2 / (pkExp k : ℝ)) * C₁) ^ (pkExp k)
      = (uncConst k hk) ^ (2 : ℝ) * C₁ ^ (pkExp k) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, ← ENNReal.rpow_mul,
      div_mul_cancel₀ (2 : ℝ) hp0]
  have hCL : (C₁ * l2Of (blkFin N m₂ q') (fun i => lpNorm k (pE k) (f i))) ^ (pkExp k)
      = C₁ ^ (pkExp k)
        * (l2Of (blkFin N m₂ q') (fun i => lpNorm k (pE k) (f i))) ^ (pkExp k) :=
    ENNReal.mul_rpow_of_nonneg _ _ hp.le
  have hu : (uncConst k hk) ^ (2 : ℝ) = uncConst k hk * uncConst k hk := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast, pow_two]
  rw [asymDec_zero_LHS_eq hk q q' hFm,
    show plExp 0 = 0 from plExp_zero, show pkExp k - (0 : ℝ) = pkExp k from sub_zero _,
    ENNReal.rpow_zero, mul_one]
  calc uncConst k hk * (∫⁻ x, convPow k (pkExp k) (fun x => ∑ i ∈ blkFin N m₂ q', f i x)
        (platePhi k hk (plateHalf m₂) (pieceCenter (2 ^ m₂) q')) x)
      = uncConst k hk * (uncConst k hk
          * (lpNorm k (pE k) (fun x => ∑ i ∈ blkFin N m₂ q', f i x)) ^ (pkExp k)) := by rw [hI]
    _ ≤ uncConst k hk * (uncConst k hk
          * (C₁ * l2Of (blkFin N m₂ q') (fun i => lpNorm k (pE k) (f i))) ^ (pkExp k)) := by
        refine mul_le_mul' le_rfl (mul_le_mul' le_rfl ?_)
        exact ENNReal.rpow_le_rpow hblock hp.le
    _ = ((uncConst k hk) ^ (2 / (pkExp k : ℝ)) * C₁) ^ (pkExp k)
          * (l2Of (blkFin N m₂ q') (fun i => lpNorm k (pE k) (f i))) ^ (pkExp k) := by
        rw [hC, hCL, hu]
        ring

end Submission.Vinogradov
