import Mathlib
import Submission.Work.Mostow.rotCanonAux
import Submission.Work.Mostow.rcRotN_eq_linBlk
import Submission.Work.Mostow.rcBoost_smul_eq
import Submission.Work.Mostow.elliptic_normal_form
import Submission.Work.Mostow.normConjIsom

/-!
# `Work.Mostow.rotCanonEqRotN`

`rotCanon g` is the rotation norm of the normal form of the elliptic isometry `g`
(`Work.Mostow.rotCanon`, defined through `Work.Mostow.elliptic_normal_form`).  The statement
proved here says that it only depends on the conjugacy class of `g` and computes the rotation norm
`rotN R` of any block normal form `h⁻¹ * g * h = e ▸ blk j m 1 R` of `g`.

The mathematical content is that the rotation norm of an elliptic isometry is a conjugacy
invariant.  The proof is organised as follows.

* `rcLin g hg` is the linear isometry of the chart by which an element `g` fixing the base point
  `0` acts (`fix_zero_is_euclidean`).
* `rcRotN_eq_opNorm_blk` computes `rotN R` as `‖opOf (rcLin B) - 1‖` for a block element
  `B = e ▸ blk j m 1 R`; this uses `rcRotN_eq_linBlk` (the block map `linBlk` keeps the tangential
  coordinates and applies `R` to the normal ones).
* `rcLin_conj_boost` is the key computation: if `A` fixes `0` and the point `q`, and
  `M = rcBoost q` is the boost `0 ↦ q`, then `rcLin (M⁻¹ * A * M) = rcLin A`.  Writing
  `M • v = rcQf q v + tpart v • q`, the identity `M • (M⁻¹AM • u) = A • (M • u)` gives
  `rcQf q (rcLin (M⁻¹AM) u) = rcLin A (rcQf q u)`; since `rcLin A` is an isometry fixing `q` it
  commutes with `rcQf q`, and `rcQf q` is injective.
* `rcLin_conj_norm`: two conjugate elements fixing `0` have conjugate linear parts, hence
  `‖opOf (rcLin ·) - 1‖` is a conjugacy invariant.
* `rcRotN_conj_blk`: two conjugate block elements have equal `rotN`.
* The theorem follows by applying this to `B = e ▸ blk j m 1 R` and to the block normal form of
  `g` produced by `elliptic_normal_form`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-! ## Casts along dimension equalities -/

private lemma rcCastNorm {a b : ℕ} (e : a = b) (u : E a) : ‖(e ▸ u : E b)‖ = ‖u‖ := by
  cases e; rfl

private lemma rcCastSub {a b : ℕ} (e : a = b) (u v : E a) :
    (e ▸ (u - v) : E b) = e ▸ u - e ▸ v := by cases e; rfl

private lemma rcRotN_nonneg {m : ℕ} (R : E m ≃ₗᵢ[ℝ] E m) : 0 ≤ rotN R := by
  rw [rotN]; exact norm_nonneg _

/-! ## The block element fixes the base point -/

private lemma rcLinBlk_zero (k m : ℕ) (R : E m ≃ₗᵢ[ℝ] E m) :
    linBlk k m R (0 : E (k + m)) = 0 := by
  refine eq_of_tanC_nrmC' ?_ ?_
  · rw [linBlk_tanC]
  · rw [linBlk_nrmC]
    have h0 : nrmC k m (0 : E (k + m)) = 0 := by ext i; simp [nrmC]
    rw [h0, map_zero]

/-- The block element `e ▸ blk j m 1 R` fixes the base point. -/
lemma rcBlk_fixes_zero {j m N : ℕ} (e : j + m = N) (R : E m ≃ₗᵢ[ℝ] E m) :
    (e ▸ blk j m 1 R : PO N 1) • (0 : E N) = 0 := by
  cases e
  rw [blk_smul_linBlk j m (rcPOActionProp j) (rcPOActionProp (j + m)) (rcHypIsometryProp (j + m))
    R 0]
  exact rcLinBlk_zero j m R

/-! ## The linear part of a block element -/

lemma rcLin_blk_apply {j m N : ℕ} (e : j + m = N) (R : E m ≃ₗᵢ[ℝ] E m)
    (hB : (e ▸ blk j m 1 R : PO N 1) • (0 : E N) = 0) (u : E N) :
    rcLin (e ▸ blk j m 1 R) hB u = e ▸ linBlk j m R (e.symm ▸ u) := by
  rw [← rcLin_apply _ hB u]
  have h := cast_smul_po e (blk j m 1 R) (e.symm ▸ u)
  rw [cast_symm_cast e u] at h
  rw [h, blk_smul_linBlk j m (rcPOActionProp j) (rcPOActionProp (j + m))
    (rcHypIsometryProp (j + m)) R (e.symm ▸ u)]

/-- **The rotation norm of a block element.**  For `B = e ▸ blk j m 1 R` one has
`rotN R = ‖opOf (rcLin B) - 1‖`. -/
lemma rcRotN_eq_opNorm_blk {j m N : ℕ} (e : j + m = N) (R : E m ≃ₗᵢ[ℝ] E m)
    (hB : (e ▸ blk j m 1 R : PO N 1) • (0 : E N) = 0) :
    ‖opOf (rcLin (e ▸ blk j m 1 R) hB) - 1‖ = rotN R := by
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ (rcRotN_nonneg R) (fun u => ?_)
    have h1 : (opOf (rcLin (e ▸ blk j m 1 R) hB) - 1) u
        = rcLin (e ▸ blk j m 1 R) hB u - u := by simp [opOf]
    rw [h1, rcLin_blk_apply e R hB u]
    have h2 : (e ▸ linBlk j m R (e.symm ▸ u) - u : E N)
        = e ▸ (linBlk j m R (e.symm ▸ u) - (e.symm ▸ u)) := by
      rw [rcCastSub, cast_symm_cast]
    rw [h2, rcCastNorm]
    have key := ((rcRotN_eq_linBlk j m R (rcRotN_nonneg R)).mp le_rfl) (e.symm ▸ u)
    rwa [rcCastNorm e.symm u] at key
  · refine (rcRotN_eq_linBlk j m R (norm_nonneg _)).mpr (fun v => ?_)
    have hle : ‖(opOf (rcLin (e ▸ blk j m 1 R) hB) - 1) (e ▸ v)‖
        ≤ ‖opOf (rcLin (e ▸ blk j m 1 R) hB) - 1‖ * ‖(e ▸ v : E N)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have h1 : (opOf (rcLin (e ▸ blk j m 1 R) hB) - 1) (e ▸ v)
        = rcLin (e ▸ blk j m 1 R) hB (e ▸ v) - (e ▸ v) := by simp [opOf]
    rw [h1, rcLin_blk_apply e R hB (e ▸ v)] at hle
    have h2 : (e ▸ linBlk j m R (e.symm ▸ (e ▸ v)) - (e ▸ v) : E N)
        = e ▸ (linBlk j m R v - v) := by
      rw [cast_symm_cast, rcCastSub]
    rw [h2, rcCastNorm, rcCastNorm] at hle
    exact hle

/-! ## The transvection `rcQf` and the boost formula -/

/-- The linear part of the boost `rcBoost q` on the chart. -/
def rcQf {n : ℕ} (q w : E n) : E n := w + ((1 + tpart q)⁻¹ * inner ℝ q w) • q

lemma rcBoost_smul_eq' {n : ℕ} (q w : E n) : rcBoost q • w = rcQf q w + tpart w • q := by
  rw [rcBoost]
  exact rcBoost_smul_eq q w

lemma rcQf_sub {n : ℕ} (q w w' : E n) : rcQf q (w - w') = rcQf q w - rcQf q w' := by
  simp only [rcQf, inner_sub_right, mul_sub, sub_smul, sub_add_eq_add_sub]
  abel

lemma rcQf_injective {n : ℕ} (q : E n) : Function.Injective (rcQf q) := by
  intro w w' h
  have hz : rcQf q (w - w') = 0 := by rw [rcQf_sub, h, sub_self]
  have hkey : w - w' + ((1 + tpart q)⁻¹ * inner ℝ q (w - w')) • q = 0 := by
    have hz' : rcQf q (w - w') = 0 := hz
    rwa [rcQf] at hz'
  have hi : inner ℝ q (w - w') + ((1 + tpart q)⁻¹ * inner ℝ q (w - w')) * inner ℝ q q = 0 := by
    have hc := congrArg (fun y => inner ℝ q y) hkey
    simp only [inner_add_right, inner_smul_right, inner_zero_right] at hc
    exact hc
  have hqpos : 0 < 1 + (1 + tpart q)⁻¹ * ‖q‖ ^ 2 := by
    have ht0' : (0:ℝ) < 1 + tpart q := by
      have h : 0 ≤ tpart q := Real.sqrt_nonneg _
      linarith
    have h2 := inv_pos.mpr ht0'
    nlinarith [sq_nonneg ‖q‖]
  have ha : inner ℝ q (w - w') = 0 := by
    rw [real_inner_self_eq_norm_sq] at hi
    have : inner ℝ q (w - w') * (1 + (1 + tpart q)⁻¹ * ‖q‖ ^ 2) = 0 := by linarith [hi]
    exact (mul_eq_zero.mp this).resolve_right hqpos.ne'
  have hz0 : w - w' = 0 := by
    rw [ha, mul_zero, zero_smul, add_zero] at hkey
    exact hkey
  exact sub_eq_zero.mp hz0

/-! ## The key computation: conjugation by a boost does not change the linear part -/

/-- **Conjugation by a boost.**  If an element `A` fixes the base point `0` and the point `q`,
then conjugating it by the boost `rcBoost q` does not change its linear part. -/
lemma rcLin_conj_boost {N : ℕ} (A : PO N 1) (hA : A • (0 : E N) = 0) (q : E N)
    (hq : A • q = q) (hB : ((rcBoost q)⁻¹ * A * rcBoost q) • (0 : E N) = 0) :
    rcLin ((rcBoost q)⁻¹ * A * rcBoost q) hB = rcLin A hA := by
  have hAB := POBasic.ofProp (rcPOActionProp N)
  have hA'q : rcLin A hA q = q := by rw [← rcLin_apply A hA q]; exact hq
  have hstep : ∀ u : E N,
      ((rcBoost q)⁻¹ * A * rcBoost q) • u = (rcBoost q)⁻¹ • (A • (rcBoost q • u)) := by
    intro u
    rw [hAB.mul_smul ((rcBoost q)⁻¹ * A) (rcBoost q) u,
      hAB.mul_smul (rcBoost q)⁻¹ A (rcBoost q • u)]
  have hXtp : ∀ u : E N,
      tpart (rcLin ((rcBoost q)⁻¹ * A * rcBoost q) hB u) = tpart u := by
    intro u
    rw [tpart, tpart, (rcLin ((rcBoost q)⁻¹ * A * rcBoost q) hB).norm_map]
  refine LinearIsometryEquiv.ext (fun u => ?_)
  have h2 : rcBoost q • (rcLin ((rcBoost q)⁻¹ * A * rcBoost q) hB u)
      = rcLin A hA (rcBoost q • u) := by
    rw [← rcLin_apply ((rcBoost q)⁻¹ * A * rcBoost q) hB u, hstep u]
    rw [← hAB.mul_smul (rcBoost q) (rcBoost q)⁻¹ (A • (rcBoost q • u)), mul_inv_cancel,
      hAB.one_smul, ← rcLin_apply A hA (rcBoost q • u)]
  have h2' : rcQf q (rcLin ((rcBoost q)⁻¹ * A * rcBoost q) hB u) + tpart u • q
      = rcLin A hA (rcQf q u) + tpart u • q := by
    have h2c := h2
    rw [rcBoost_smul_eq' q (rcLin ((rcBoost q)⁻¹ * A * rcBoost q) hB u),
      rcBoost_smul_eq' q u, hXtp u] at h2c
    rw [h2c, map_add, map_smul, hA'q]
  have h1 : rcQf q (rcLin ((rcBoost q)⁻¹ * A * rcBoost q) hB u) = rcLin A hA (rcQf q u) :=
    add_right_cancel h2'
  have h5 : rcLin A hA (rcQf q u) = rcQf q (rcLin A hA u) := by
    have hinner : inner ℝ q (rcLin A hA u) = inner ℝ q u := by
      conv_lhs => rw [← hA'q]
      rw [LinearIsometryEquiv.inner_map_map]
    simp only [rcQf, map_add, map_smul, hA'q, hinner]
  exact rcQf_injective q (h1.trans h5)

/-! ## Conjugation invariance of `‖opOf (rcLin ·) - 1‖` -/

lemma rcLin_conj_of {N : ℕ} (g k : PO N 1) (hg : g • (0 : E N) = 0)
    (hk : k • (0 : E N) = 0) (hki : k⁻¹ • (0 : E N) = 0)
    (hconjk : (k⁻¹ * g * k) • (0 : E N) = 0) :
    rcLin (k⁻¹ * g * k) hconjk = (rcLin k hk)⁻¹ * rcLin g hg * rcLin k hk := by
  have hAB := POBasic.ofProp (rcPOActionProp N)
  have hkg : (k⁻¹ * g) • (0 : E N) = 0 := by rw [hAB.mul_smul, hg, hki]
  rw [rcLin_mul (k⁻¹ * g) k hkg hk hconjk, rcLin_mul k⁻¹ g hki hg hkg, rcLin_inv k hk hki]

/-- Conjugating a linear isometry of the chart by `Q` conjugates `‖opOf · - 1‖` accordingly. -/
private lemma rcOpNorm_conj {N : ℕ} (Q A₁ A₂ : E N ≃ₗᵢ[ℝ] E N)
    (h : ∀ u, A₂ u = Q.symm (A₁ (Q u))) :
    ‖opOf A₂ - 1‖ = ‖opOf A₁ - 1‖ := by
  have key1 : ∀ u : E N, (opOf A₂ - 1) u = Q.symm ((opOf A₁ - 1) (Q u)) := by
    intro u
    have e1 : (opOf A₂ - 1) u = A₂ u - u := by simp [opOf]
    have e2 : (opOf A₁ - 1) (Q u) = A₁ (Q u) - Q u := by simp [opOf]
    have e3 : Q.symm ((opOf A₁ - 1) (Q u)) = Q.symm (A₁ (Q u)) - u := by
      rw [e2, map_sub, LinearIsometryEquiv.symm_apply_apply]
    rw [e1, h u, e3]
  have key2 : ∀ v : E N, (opOf A₁ - 1) v = Q ((opOf A₂ - 1) (Q.symm v)) := by
    intro v
    have e1 : (opOf A₁ - 1) v = A₁ v - v := by simp [opOf]
    have e2 : (opOf A₂ - 1) (Q.symm v) = A₂ (Q.symm v) - Q.symm v := by simp [opOf]
    have h2 := h (Q.symm v)
    rw [LinearIsometryEquiv.apply_symm_apply] at h2
    have e3 : Q ((opOf A₂ - 1) (Q.symm v)) = A₁ v - v := by
      rw [e2, h2, map_sub, LinearIsometryEquiv.apply_symm_apply,
        LinearIsometryEquiv.apply_symm_apply]
    rw [e1, e3]
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun u => ?_)
    calc ‖(opOf A₂ - 1) u‖ = ‖(opOf A₁ - 1) (Q u)‖ := by
          rw [key1 u, LinearIsometryEquiv.norm_map]
      _ ≤ ‖opOf A₁ - 1‖ * ‖Q u‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖opOf A₁ - 1‖ * ‖u‖ := by rw [LinearIsometryEquiv.norm_map]
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun v => ?_)
    calc ‖(opOf A₁ - 1) v‖ = ‖(opOf A₂ - 1) (Q.symm v)‖ := by
          rw [key2 v, LinearIsometryEquiv.norm_map]
      _ ≤ ‖opOf A₂ - 1‖ * ‖Q.symm v‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖opOf A₂ - 1‖ * ‖v‖ := by rw [LinearIsometryEquiv.norm_map]

/-- **`‖opOf (rcLin ·) - 1‖` is a conjugacy invariant on elements fixing the base point.** -/
lemma rcLin_conj_norm {N : ℕ} (B₁ B₂ k : PO N 1) (h1 : B₁ • (0 : E N) = 0)
    (h2 : B₂ • (0 : E N) = 0) (hconj : B₂ = k⁻¹ * B₁ * k) :
    ‖opOf (rcLin B₂ h2) - 1‖ = ‖opOf (rcLin B₁ h1) - 1‖ := by
  have hAB := POBasic.ofProp (rcPOActionProp N)
  have hMq : rcBoost (k • (0 : E N)) • (0 : E N) = k • (0 : E N) := rcBoost_smul_zero _
  have hK0 : ((rcBoost (k • (0 : E N)))⁻¹ * k) • (0 : E N) = 0 := by
    calc ((rcBoost (k • (0:E N)))⁻¹ * k) • (0 : E N)
        = (rcBoost (k • (0:E N)))⁻¹ • (k • (0 : E N)) :=
          hAB.mul_smul (rcBoost (k • (0:E N)))⁻¹ k (0 : E N)
      _ = (rcBoost (k • (0:E N)))⁻¹ • ((rcBoost (k • (0:E N))) • (0 : E N)) := by rw [hMq]
      _ = ((rcBoost (k • (0:E N)))⁻¹ * rcBoost (k • (0:E N))) • (0 : E N) :=
          (hAB.mul_smul (rcBoost (k • (0:E N)))⁻¹ (rcBoost (k • (0:E N))) (0 : E N)).symm
      _ = 0 := by rw [inv_mul_cancel, hAB.one_smul]
  have h0 : k⁻¹ • (B₁ • (k • (0 : E N))) = 0 := by
    have hh := h2
    rw [hconj, hAB.mul_smul (k⁻¹ * B₁) k, hAB.mul_smul k⁻¹ B₁] at hh
    exact hh
  have hB₁q : B₁ • (k • (0 : E N)) = k • (0 : E N) := by
    have hh : k • (0 : E N) = B₁ • (k • (0 : E N)) := by
      calc k • (0 : E N) = k • (k⁻¹ • (B₁ • (k • (0 : E N)))) := by rw [h0]
        _ = (k * k⁻¹) • (B₁ • (k • (0 : E N))) :=
              (hAB.mul_smul k k⁻¹ (B₁ • (k • (0:E N)))).symm
        _ = B₁ • (k • (0 : E N)) := by rw [mul_inv_cancel, hAB.one_smul]
    exact hh.symm
  have hB30 : ((rcBoost (k • (0:E N)))⁻¹ * B₁ * rcBoost (k • (0:E N))) • (0 : E N) = 0 := by
    calc ((rcBoost (k • (0:E N)))⁻¹ * B₁ * rcBoost (k • (0:E N))) • (0 : E N)
        = ((rcBoost (k • (0:E N)))⁻¹ * B₁) • (rcBoost (k • (0:E N)) • (0 : E N)) :=
          hAB.mul_smul ((rcBoost (k • (0:E N)))⁻¹ * B₁) (rcBoost (k • (0:E N))) (0 : E N)
      _ = ((rcBoost (k • (0:E N)))⁻¹ * B₁) • (k • (0 : E N)) := by rw [hMq]
      _ = (rcBoost (k • (0:E N)))⁻¹ • (B₁ • (k • (0 : E N))) :=
          hAB.mul_smul (rcBoost (k • (0:E N)))⁻¹ B₁ (k • (0 : E N))
      _ = (rcBoost (k • (0:E N)))⁻¹ • ((rcBoost (k • (0:E N))) • (0 : E N)) := by
            rw [hMq, hB₁q]
      _ = 0 := by
            rw [← hAB.mul_smul (rcBoost (k • (0:E N)))⁻¹ (rcBoost (k • (0:E N))) (0 : E N),
              inv_mul_cancel, hAB.one_smul]
  have hW2 : rcLin ((rcBoost (k • (0 : E N)))⁻¹ * B₁ * rcBoost (k • (0 : E N))) hB30
      = rcLin B₁ h1 :=
    rcLin_conj_boost B₁ h1 (k • (0 : E N)) hB₁q hB30
  have hKinv0 : ((rcBoost (k • (0:E N)))⁻¹ * k)⁻¹ • (0 : E N) = 0 := by
    calc ((rcBoost (k • (0:E N)))⁻¹ * k)⁻¹ • (0 : E N)
        = ((rcBoost (k • (0:E N)))⁻¹ * k)⁻¹
            • (((rcBoost (k • (0:E N)))⁻¹ * k) • (0 : E N)) := by rw [hK0]
      _ = 0 := by
            rw [← hAB.mul_smul ((rcBoost (k • (0:E N)))⁻¹ * k)⁻¹ ((rcBoost (k • (0:E N)))⁻¹ * k)
                (0 : E N), inv_mul_cancel, hAB.one_smul]
  have hB2eq : B₂ = ((rcBoost (k • (0:E N)))⁻¹ * k)⁻¹
      * ((rcBoost (k • (0:E N)))⁻¹ * B₁ * rcBoost (k • (0:E N)))
      * ((rcBoost (k • (0:E N)))⁻¹ * k) := by
    rw [hconj]; group
  have hconjK : (((rcBoost (k • (0:E N)))⁻¹ * k)⁻¹
      * ((rcBoost (k • (0:E N)))⁻¹ * B₁ * rcBoost (k • (0:E N)))
      * ((rcBoost (k • (0:E N)))⁻¹ * k)) • (0 : E N) = 0 := by
    rw [← hB2eq]; exact h2
  have hAi : ∀ u : E N, rcLin B₂ h2 u
      = (rcLin ((rcBoost (k • (0:E N)))⁻¹ * k) hK0).symm
        ((rcLin B₁ h1) ((rcLin ((rcBoost (k • (0:E N)))⁻¹ * k) hK0) u)) := by
    intro u
    rw [rcLin_congr hB2eq h2 hconjK,
      rcLin_conj_of ((rcBoost (k • (0:E N)))⁻¹ * B₁ * rcBoost (k • (0:E N)))
        ((rcBoost (k • (0:E N)))⁻¹ * k) hB30 hK0 hKinv0 hconjK, hW2]
    simp only [LinearIsometryEquiv.coe_mul, Function.comp_apply, LinearIsometryEquiv.inv_def]
  exact rcOpNorm_conj _ _ _ hAi

/-! ## Conjugate block elements have the same rotation norm -/

/-- **`rotN` is independent of the block normal form.**  Two conjugate block elements of `PO N 1`
have the same rotation norm. -/
theorem rcRotN_conj_blk {N : ℕ} {j₁ m₁ j₂ m₂ : ℕ} (e₁ : j₁ + m₁ = N) (e₂ : j₂ + m₂ = N)
    (R₁ : E m₁ ≃ₗᵢ[ℝ] E m₁) (R₂ : E m₂ ≃ₗᵢ[ℝ] E m₂) (k : PO N 1)
    (hk : (e₂ ▸ blk j₂ m₂ 1 R₂ : PO N 1) = k⁻¹ * (e₁ ▸ blk j₁ m₁ 1 R₁ : PO N 1) * k) :
    rotN R₁ = rotN R₂ := by
  have h1 := rcBlk_fixes_zero e₁ R₁
  have h2 := rcBlk_fixes_zero e₂ R₂
  have hc := rcLin_conj_norm (e₁ ▸ blk j₁ m₁ 1 R₁) (e₂ ▸ blk j₂ m₂ 1 R₂) k h1 h2 hk
  rw [rcRotN_eq_opNorm_blk e₁ R₁ h1, rcRotN_eq_opNorm_blk e₂ R₂ h2] at hc
  exact hc.symm

/-! ## The theorem -/

/-- Two block normal forms of the same element of `PO N 1` have the same rotation norm. -/
theorem rcRotN_eq_of_conj_blk {N : ℕ} (g : PO N 1) {j₁ m₁ j₂ m₂ : ℕ}
    {e₁ : j₁ + m₁ = N} {e₂ : j₂ + m₂ = N} {R₁ : E m₁ ≃ₗᵢ[ℝ] E m₁} {R₂ : E m₂ ≃ₗᵢ[ℝ] E m₂}
    {k₁ k₂ : PO N 1}
    (h₁ : k₁⁻¹ * g * k₁ = (e₁ ▸ blk j₁ m₁ 1 R₁ : PO N 1))
    (h₂ : k₂⁻¹ * g * k₂ = (e₂ ▸ blk j₂ m₂ 1 R₂ : PO N 1)) :
    rotN R₁ = rotN R₂ := by
  refine rcRotN_conj_blk e₁ e₂ R₁ R₂ (k₁⁻¹ * k₂) ?_
  rw [← h₂, ← h₁]
  group

theorem rotCanonEqRotN (N : ℕ) (hAall : ∀ k, Submission.Mostow.POActionProp k)
    (hIall : ∀ k, Submission.Mostow.HypIsometryProp k) (g : PO N 1)
    (j m : ℕ) (e : j + m = N) (R : E m ≃ₗᵢ[ℝ] E m) (hR : ∀ w, R w = w → w = 0)
    (h : PO N 1)
    (hconj : h⁻¹ * g * h = (e ▸ Submission.Mostow.blk j m 1 R : PO N 1)) :
    Work.Mostow.rotCanon hAall hIall g = Submission.Mostow.rotN R := by
  have hAB := POBasic.ofProp (rcPOActionProp N)
  have hB0 : (e ▸ blk j m 1 R : PO N 1) • (0 : E N) = 0 := rcBlk_fixes_zero e R
  have hgell : ∃ p : E N, g • p = p := by
    refine ⟨h • (0 : E N), ?_⟩
    have hg : g = h * (e ▸ blk j m 1 R : PO N 1) * h⁻¹ := by rw [← hconj]; group
    calc g • (h • (0 : E N))
        = (h * (e ▸ blk j m 1 R : PO N 1) * h⁻¹) • (h • (0 : E N)) := by rw [hg]
      _ = (h * (e ▸ blk j m 1 R : PO N 1)) • (h⁻¹ • (h • (0 : E N))) :=
            hAB.mul_smul (h * (e ▸ blk j m 1 R : PO N 1)) h⁻¹ (h • (0 : E N))
      _ = (h * (e ▸ blk j m 1 R : PO N 1)) • ((h⁻¹ * h) • (0 : E N)) := by
            rw [← hAB.mul_smul h⁻¹ h (0 : E N)]
      _ = (h * (e ▸ blk j m 1 R : PO N 1)) • (0 : E N) := by
            rw [inv_mul_cancel, hAB.one_smul]
      _ = h • ((e ▸ blk j m 1 R : PO N 1) • (0 : E N)) :=
            hAB.mul_smul h (e ▸ blk j m 1 R : PO N 1) (0 : E N)
      _ = h • (0 : E N) := by rw [hB0]
  rw [rotCanon, dif_pos hgell]
  have hspec := (elliptic_normal_form N (hAall N) (hIall N) hAall hIall g hgell).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
  exact rcRotN_eq_of_conj_blk g hspec.2 hconj

end

end Work.Mostow
