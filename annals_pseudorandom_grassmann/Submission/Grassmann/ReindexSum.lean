import Submission.Grassmann.Reindex
import Submission.Grassmann.SwRole
import Submission.Commons.LinearAlgebra.Matrix.card_rank_poset_fiber_le_pow

/-!
# The removal of the extra `D_X`-derivatives (P4 of the endgame)

The paper derives `Σ_X q^{-4d·rank X}‖D_Xf‖₂⁴ ≤ 2‖f‖₂⁴` from the identity
`‖D_Xf‖₂² = Σ_{Y ≥ X}|f̂(Y)|²`, which is **false** for the restricted derivative
`D_Xf = (L_Xf)_{(Im X, ker X)}` (the coefficients of the compression's fibres add).  The honest
proof uses

* the fibre count `l2sq (D_X h) ≤ 2^{2·rank X·d}·l2sq (L_X h)` (`l2sq_DopRole_le`, from the
  commons `card_rank_poset_upset_fiber_le_pow`), and
* the poset count `#{X : X ≤ Y, rank X = k} ≤ 2^{3kd}` (the paper's Claim,
  `card_plLE_rank_le_pow`, from the commons `card_rank_poset_fiber_le_pow`).

It yields `Σ_{X : rank X = k}(l2sq (D_X h))² ≤ 2^{7dk}(l2sq h)²` (`sum_rank_sq_DopRole_le`), a loss
of `2^{7dk}` per rank stratum.  The fibre bound (P3) supplies `2^{-λdk}` per stratum for every
`λ ≤ 61` (strengthened P3, `fiber_weight_le_sharp`), so `λ = 12` leaves `Σ_k 2^{-5dk} ≤ 2` and the
induction closes.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

variable {m n : ℕ}

/-! ## `l2sq (L_X h) ≤ l2sq h` -/

/-- A `plLE`-multiplier never increases the `L²`-norm. -/
lemma l2sq_lapMulN_plLE_le {m n : ℕ} {h : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ}
    (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    l2sq (lapMulN (plLE X) h) ≤ l2sq h := by
  rw [l2sq_lapMulN_eq]
  calc (∑ Y : Matrix (Fin n) (Fin m) 𝔽₂,
        if plLE X Y then ‖fcoeff h Y‖ ^ 2 else 0) ≤
      ∑ Y : Matrix (Fin n) (Fin m) 𝔽₂, ‖fcoeff h Y‖ ^ 2 :=
      Finset.sum_le_sum (fun Y _ => by
        by_cases hY : plLE X Y
        · rw [if_pos hY]
        · rw [if_neg hY]; positivity)
    _ = l2sq h := sum_normSq_fcoeff h

/-! ## The restricted `X`-derivative is dominated by its multiplier form -/

/-- **The fibre count for the restricted `X`-derivative**:
`l2sq (D_X h) ≤ 2^{2·rank X·d}·l2sq (L_X h)` for `DegLe d h`.  This is
`l2sq_restr_lapMulN_le` with its fibre-count hypothesis discharged by the commons lemma
`card_rank_poset_upset_fiber_le_pow`. -/
theorem l2sq_DopRole_le {d : ℕ} {h : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ} (hh : DegLe d h)
    (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    l2sq (DopRole X h) ≤ (2 : ℝ) ^ (2 * X.rank * d) * l2sq (lapMulN (plLE X) h) := by
  rw [DopRole]
  refine l2sq_restr_lapMulN_le hh X fun Z₀ hpl hrank => ?_
  have hX : X.rank ≤ d := le_trans (plLE_rank_le hpl) hrank
  have hiff : ∀ Z : Matrix (Fin n) (Fin m) 𝔽₂,
      (plLE X Z ∧ Z.rank ≤ d ∧
        Qp (LinearMap.range X.mulVecLin) * Z * Ip (LinearMap.ker X.mulVecLin)
          = Qp (LinearMap.range X.mulVecLin) * Z₀ * Ip (LinearMap.ker X.mulVecLin))
        ↔ (Z.rank = X.rank + (Z - X).rank ∧ Z.rank ≤ d ∧
          ∀ w : Fin m → 𝔽₂, w ∈ LinearMap.ker X.mulVecLin →
            (Z - Z₀).mulVec w ∈ LinearMap.range X.mulVecLin) := by
    intro Z
    have hsub : Qp (LinearMap.range X.mulVecLin) * (Z - Z₀) * Ip (LinearMap.ker X.mulVecLin)
        = Qp (LinearMap.range X.mulVecLin) * Z * Ip (LinearMap.ker X.mulVecLin)
          - Qp (LinearMap.range X.mulVecLin) * Z₀ * Ip (LinearMap.ker X.mulVecLin) := by
      rw [Matrix.mul_sub, Matrix.sub_mul]
    have h3iff : (Qp (LinearMap.range X.mulVecLin) * Z * Ip (LinearMap.ker X.mulVecLin)
        = Qp (LinearMap.range X.mulVecLin) * Z₀ * Ip (LinearMap.ker X.mulVecLin))
        ↔ (Qp (LinearMap.range X.mulVecLin) * (Z - Z₀) * Ip (LinearMap.ker X.mulVecLin) = 0) := by
      rw [hsub, sub_eq_zero]
    rw [plLE, h3iff, Qp_mul_Ip_eq_zero_iff]
  calc Nat.card {Z : Matrix (Fin n) (Fin m) 𝔽₂ //
        plLE X Z ∧ Z.rank ≤ d ∧
          Qp (LinearMap.range X.mulVecLin) * Z * Ip (LinearMap.ker X.mulVecLin)
            = Qp (LinearMap.range X.mulVecLin) * Z₀ * Ip (LinearMap.ker X.mulVecLin)}
      = Nat.card {Z : Matrix (Fin n) (Fin m) 𝔽₂ //
          Z.rank = X.rank + (Z - X).rank ∧ Z.rank ≤ d ∧
          ∀ w : Fin m → 𝔽₂, w ∈ LinearMap.ker X.mulVecLin →
            (Z - Z₀).mulVec w ∈ LinearMap.range X.mulVecLin} :=
        Nat.card_congr (Equiv.subtypeEquivRight hiff)
    _ ≤ 2 ^ (2 * X.rank * d) :=
        Commons.LinearAlgebra.Matrix.card_rank_poset_upset_fiber_le_pow n m d X Z₀ hX hpl

/-! ## The paper's poset count -/

/-- **The number of `X ≤ Y` of rank `k` is at most `2 ^ (3 k d)`** (the paper's Claim): `X ≤ Y`
forces `Im X ≤ Im Y` and `ker X ≥ ker Y` (`2^{kd}` choices each), and given both there are at most
`2^{k²} ≤ 2^{kd}` maps. -/
lemma card_plLE_rank_le_pow {d k : ℕ} {m n : ℕ} (Y : Matrix (Fin n) (Fin m) 𝔽₂)
    (hY : Y.rank ≤ d) :
    Nat.card {X : Matrix (Fin n) (Fin m) 𝔽₂ // plLE X Y ∧ X.rank = k} ≤ 2 ^ (3 * k * d) :=
  (Nat.card_le_card_of_injective
    (fun X : {X : Matrix (Fin n) (Fin m) 𝔽₂ // plLE X Y ∧ X.rank = k} =>
      (⟨X.1, X.2.1, X.2.2⟩ :
        {X : Matrix (Fin n) (Fin m) 𝔽₂ // Y.rank = X.rank + (Y - X).rank ∧ X.rank = k}))
    (fun _ _ hab => Subtype.ext (congrArg Subtype.val hab))).trans
    (Commons.LinearAlgebra.Matrix.card_rank_poset_fiber_le_pow n m d k Y hY)

/-! ## The sum of the `L²`-norms at a fixed rank -/

/-- The sum of the multiplier norms at a fixed rank is bounded by the poset count:
`Σ_{rank X = k} l2sq (L_X h) ≤ 2^{3dk}·l2sq h`. -/
lemma sum_rank_l2sq_lapMulN_le {d : ℕ} {h : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ} (hh : DegLe d h)
    (k : ℕ) :
    (∑ X : {X : Matrix (Fin n) (Fin m) 𝔽₂ // X.rank = k}, l2sq (lapMulN (plLE X.1) h))
      ≤ (2 : ℝ) ^ (3 * d * k) * l2sq h := by
  classical
  have hexp : ∀ X : {X : Matrix (Fin n) (Fin m) 𝔽₂ // X.rank = k},
      l2sq (lapMulN (plLE X.1) h)
        = ∑ Y : Matrix (Fin n) (Fin m) 𝔽₂,
            if plLE X.1 Y then ‖fcoeff h Y‖ ^ 2 else 0 := fun X => l2sq_lapMulN_eq (plLE X.1) h
  simp only [hexp]
  rw [Finset.sum_comm, ← sum_normSq_fcoeff h, Finset.mul_sum]
  refine Finset.sum_le_sum (fun Y _ => ?_)
  by_cases hY : Y.rank ≤ d
  · have hcard : (Finset.univ.filter (fun X : {X : Matrix (Fin n) (Fin m) 𝔽₂ // X.rank = k} =>
        plLE X.1 Y)).card ≤ 2 ^ (3 * k * d) := by
      rw [← Fintype.card_subtype
        (fun X : {X : Matrix (Fin n) (Fin m) 𝔽₂ // X.rank = k} => plLE X.1 Y)]
      rw [← Nat.card_eq_fintype_card]
      refine (Nat.card_le_card_of_injective
        (fun X : {X : {X : Matrix (Fin n) (Fin m) 𝔽₂ // X.rank = k} // plLE X.1 Y} =>
          (⟨X.1.1, X.2, X.1.2⟩ :
            {X : Matrix (Fin n) (Fin m) 𝔽₂ // plLE X Y ∧ X.rank = k}))
        (fun a b hab => Subtype.ext (Subtype.ext (congrArg (fun z => z.1) hab)))).trans
        (card_plLE_rank_le_pow Y hY)
    have h1 : ((Finset.univ.filter (fun X : {X : Matrix (Fin n) (Fin m) 𝔽₂ // X.rank = k} =>
        plLE X.1 Y)).card : ℝ) ≤ (2 : ℝ) ^ (3 * k * d) := by exact_mod_cast hcard
    calc (∑ X : {X : Matrix (Fin n) (Fin m) 𝔽₂ // X.rank = k},
            if plLE X.1 Y then ‖fcoeff h Y‖ ^ 2 else 0)
        = ((Finset.univ.filter (fun X : {X : Matrix (Fin n) (Fin m) 𝔽₂ // X.rank = k} =>
            plLE X.1 Y)).card : ℝ) * ‖fcoeff h Y‖ ^ 2 := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 : ℝ) ^ (3 * k * d) * ‖fcoeff h Y‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (2 : ℝ) ^ (3 * d * k) * ‖fcoeff h Y‖ ^ 2 := by
          rw [show 3 * k * d = 3 * d * k by ring]
  · have hz : fcoeff h Y = 0 := by
      rw [fcoeff_eq, hh Y (by omega), mul_zero]
    simp only [hz, norm_zero]
    simp

/-! ## The removal of the extra `D_X`-derivatives -/

/-- **The removal of the extra `D_X`-derivatives at a fixed rank** (`cor:getting rid of D_X
4-norms`, honest form): for `DegLe d h` and every `k`,
`Σ_{X : rank X = k} (l2sq (D_X h))² ≤ 2^{7dk} (l2sq h)²`. -/
theorem sum_rank_sq_DopRole_le {d : ℕ} {h : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ} (hh : DegLe d h)
    (k : ℕ) :
    (∑ X : {X : Matrix (Fin n) (Fin m) 𝔽₂ // X.rank = k}, (l2sq (DopRole X.1 h)) ^ 2)
      ≤ (2 : ℝ) ^ (7 * d * k) * (l2sq h) ^ 2 := by
  classical
  have hB0 : (0 : ℝ) ≤ l2sq h := l2sq_nonneg h
  have ha : ∀ X : {X : Matrix (Fin n) (Fin m) 𝔽₂ // X.rank = k},
      l2sq (DopRole X.1 h) ≤ (2 : ℝ) ^ (2 * d * k) * l2sq (lapMulN (plLE X.1) h) := by
    intro X
    have h := l2sq_DopRole_le hh X.1
    rw [X.2] at h
    have hc : (2 : ℝ) ^ (2 * k * d) = (2 : ℝ) ^ (2 * d * k) := by
      rw [show 2 * k * d = 2 * d * k by ring]
    rwa [hc] at h
  have ha0 : ∀ X : {X : Matrix (Fin n) (Fin m) 𝔽₂ // X.rank = k},
      (0 : ℝ) ≤ l2sq (DopRole X.1 h) := fun X => l2sq_nonneg _
  have hb : ∀ X : {X : Matrix (Fin n) (Fin m) 𝔽₂ // X.rank = k},
      l2sq (lapMulN (plLE X.1) h) ≤ l2sq h := fun X => l2sq_lapMulN_plLE_le X.1
  have hsum_a : (∑ X : {X : Matrix (Fin n) (Fin m) 𝔽₂ // X.rank = k}, l2sq (DopRole X.1 h))
      ≤ (2 : ℝ) ^ (2 * d * k) *
        ∑ X : {X : Matrix (Fin n) (Fin m) 𝔽₂ // X.rank = k}, l2sq (lapMulN (plLE X.1) h) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun X _ => ha X)
  calc (∑ X : {X : Matrix (Fin n) (Fin m) 𝔽₂ // X.rank = k}, (l2sq (DopRole X.1 h)) ^ 2)
      ≤ ∑ X : {X : Matrix (Fin n) (Fin m) 𝔽₂ // X.rank = k},
          l2sq (DopRole X.1 h) * ((2 : ℝ) ^ (2 * d * k) * l2sq (lapMulN (plLE X.1) h)) := by
        refine Finset.sum_le_sum fun X _ => ?_
        rw [sq]
        exact mul_le_mul_of_nonneg_left (ha X) (ha0 X)
    _ = (2 : ℝ) ^ (2 * d * k) *
          ∑ X : {X : Matrix (Fin n) (Fin m) 𝔽₂ // X.rank = k},
            l2sq (DopRole X.1 h) * l2sq (lapMulN (plLE X.1) h) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun X _ => by ring)
    _ ≤ (2 : ℝ) ^ (2 * d * k) *
          (l2sq h * ∑ X : {X : Matrix (Fin n) (Fin m) 𝔽₂ // X.rank = k},
            l2sq (DopRole X.1 h)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum (fun X _ => by
          calc l2sq (DopRole X.1 h) * l2sq (lapMulN (plLE X.1) h)
              ≤ l2sq (DopRole X.1 h) * l2sq h := mul_le_mul_of_nonneg_left (hb X) (ha0 X)
            _ = l2sq h * l2sq (DopRole X.1 h) := by ring)
    _ ≤ (2 : ℝ) ^ (2 * d * k) *
          (l2sq h * ((2 : ℝ) ^ (2 * d * k) *
            ∑ X : {X : Matrix (Fin n) (Fin m) 𝔽₂ // X.rank = k},
              l2sq (lapMulN (plLE X.1) h))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hsum_a hB0
    _ ≤ (2 : ℝ) ^ (2 * d * k) *
          (l2sq h * ((2 : ℝ) ^ (2 * d * k) * ((2 : ℝ) ^ (3 * d * k) * l2sq h))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine mul_le_mul_of_nonneg_left ?_ hB0
        exact mul_le_mul_of_nonneg_left (sum_rank_l2sq_lapMulN_le hh k) (by positivity)
    _ = (2 : ℝ) ^ (7 * d * k) * (l2sq h) ^ 2 := by ring

open scoped Classical in
/-- The `T'`-summed version of `sum_rank_sq_DopRole_le`. -/
theorem sum_rank_G_le (V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W : Submodule 𝔽₂ (Fin m → 𝔽₂))
    {d : ℕ} {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ} (hf : DegLe d f) (k : ℕ) :
    (∑ Z : {Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀))
          (Fin (Module.finrank 𝔽₂ W)) 𝔽₂ // Z.rank = k},
      ∑ T' : Matrix (Fin m) (Fin n) 𝔽₂,
        (l2sq (DopRole Z.1 (Dop0S V₀ W T' f))) ^ 2)
      ≤ (2 : ℝ) ^ (7 * d * k) * ((2 : ℝ) ^ (m * n) * D4 V₀ W (Lsub V₀ W f)) := by
  have hdeg : ∀ T' : Matrix (Fin m) (Fin n) 𝔽₂, DegLe d (Dop0S V₀ W T' f) := fun T' Y hY =>
    degLe_Dop0S hf V₀ W T' Y (by omega)
  rw [Finset.sum_comm]
  calc (∑ T' : Matrix (Fin m) (Fin n) 𝔽₂,
        ∑ Z : {Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀))
              (Fin (Module.finrank 𝔽₂ W)) 𝔽₂ // Z.rank = k},
          (l2sq (DopRole Z.1 (Dop0S V₀ W T' f))) ^ 2)
      ≤ ∑ T' : Matrix (Fin m) (Fin n) 𝔽₂,
          (2 : ℝ) ^ (7 * d * k) * (l2sq (Dop0S V₀ W T' f)) ^ 2 :=
        Finset.sum_le_sum (fun T' _ => sum_rank_sq_DopRole_le (hdeg T') k)
    _ = (2 : ℝ) ^ (7 * d * k) *
          ∑ T' : Matrix (Fin m) (Fin n) 𝔽₂, (l2sq (Dop0S V₀ W T' f)) ^ 2 := by
        rw [Finset.mul_sum]
    _ = (2 : ℝ) ^ (7 * d * k) * ((2 : ℝ) ^ (m * n) * D4 V₀ W (Lsub V₀ W f)) := by
        rw [D4_Lsub_eq_sum_l2sq]
        field_simp

/-- The switching summand reindexed by `Φ₃`, with the `T'`-sum kept. -/
noncomputable def G {m n : ℕ} (V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) : ℝ :=
  ∑ T' : Matrix (Fin m) (Fin n) 𝔽₂,
    (l2sq (DopRole Z (Dop0S V₀ W T' f))) ^ 2

/-- **The weighted `Z`-sum of the reindexed summands**: summing over the rank strata with the
weight `2^{−λdk}` costs at most `2·2^{mn}·D4 V₀ W (Lsub V₀ W f)` as soon as `8 ≤ λ`. -/
theorem sum_k_weight_G_le (V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W : Submodule 𝔽₂ (Fin m → 𝔽₂)) {d lam : ℕ} (hlam : 8 ≤ lam)
    {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ} (hf : DegLe d f) :
    (∑ k ∈ Finset.range (d + 1),
      ((2 : ℝ) ^ (lam * d * k))⁻¹ *
        ∑ Z : {Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀))
              (Fin (Module.finrank 𝔽₂ W)) 𝔽₂ // Z.rank = k}, G V₀ W Z.1 f)
      ≤ 2 * ((2 : ℝ) ^ (m * n) * D4 V₀ W (Lsub V₀ W f)) := by
  set D0 : ℝ := (2 : ℝ) ^ (m * n) * D4 V₀ W (Lsub V₀ W f) with hD0
  have hD00 : 0 ≤ D0 := by
    rw [hD0]; exact mul_nonneg (by positivity) (D4_nonneg _ _ _)
  have h1 : ∀ k ∈ Finset.range (d + 1),
      ((2 : ℝ) ^ (lam * d * k))⁻¹ *
          ∑ Z : {Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀))
                (Fin (Module.finrank 𝔽₂ W)) 𝔽₂ // Z.rank = k}, G V₀ W Z.1 f
        ≤ (2 : ℝ) ^ (7 * d * k) * ((2 : ℝ) ^ (lam * d * k))⁻¹ * D0 := by
    intro k _
    have h := sum_rank_G_le V₀ W hf k
    rw [hD0]
    calc ((2 : ℝ) ^ (lam * d * k))⁻¹ *
          ∑ Z : {Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀))
                (Fin (Module.finrank 𝔽₂ W)) 𝔽₂ // Z.rank = k}, G V₀ W Z.1 f
        ≤ ((2 : ℝ) ^ (lam * d * k))⁻¹ *
            ((2 : ℝ) ^ (7 * d * k) * ((2 : ℝ) ^ (m * n) * D4 V₀ W (Lsub V₀ W f))) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = (2 : ℝ) ^ (7 * d * k) * ((2 : ℝ) ^ (lam * d * k))⁻¹ *
            ((2 : ℝ) ^ (m * n) * D4 V₀ W (Lsub V₀ W f)) := by ring
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.sum_mul]
  have hpow : ∀ k : ℕ, (2 : ℝ) ^ (7 * d * k) * ((2 : ℝ) ^ (lam * d * k))⁻¹
      = ((2 : ℝ) ^ ((lam - 7) * d))⁻¹ ^ k := by
    intro k
    have hexp : lam * d * k = 7 * d * k + (lam - 7) * d * k := by
      have h1 : lam - 7 + 7 = lam := Nat.sub_add_cancel (by omega : 7 ≤ lam)
      have h2 : lam * d * k = ((lam - 7) + 7) * d * k := by rw [h1]
      rw [h2, Nat.add_mul, Nat.add_mul]
      ring
    have hA : (2 : ℝ) ^ (7 * d * k) * ((2 : ℝ) ^ (lam * d * k))⁻¹
        = ((2 : ℝ) ^ ((lam - 7) * d * k))⁻¹ := by
      rw [hexp, pow_add, mul_inv, ← mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)), one_mul]
    have hB : ((2 : ℝ) ^ ((lam - 7) * d * k))⁻¹
        = ((2 : ℝ) ^ ((lam - 7) * d))⁻¹ ^ k := by
      rw [inv_pow, ← pow_mul]
    rw [hA, hB]
  have hgeom : (∑ k ∈ Finset.range (d + 1),
      ((2 : ℝ) ^ ((lam - 7) * d))⁻¹ ^ k) ≤ 2 := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd; simp
    · have hkey : 1 ≤ (lam - 7) * d := by
        have h7 : 1 ≤ lam - 7 := by omega
        exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      have h2 : (2 : ℝ) ≤ 2 ^ ((lam - 7) * d) := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ ((lam - 7) * d) := pow_le_pow_right₀ (by norm_num) hkey
      have hr : ((2 : ℝ) ^ ((lam - 7) * d))⁻¹ ≤ 1 / 2 := by
        rw [inv_le_comm₀ (by positivity) (by norm_num : (0 : ℝ) < 1 / 2)]
        simpa using h2
      exact geom_sum_le_two (by positivity) hr (d + 1)
  refine mul_le_mul_of_nonneg_right ?_ hD00
  rw [Finset.sum_congr rfl (fun k _ => hpow k)]
  exact hgeom

end
end Submission.Grassmann
