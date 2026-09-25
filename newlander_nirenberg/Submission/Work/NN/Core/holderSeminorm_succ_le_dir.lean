/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The Hölder seminorm of order `k+1` is controlled by the directional derivatives

For an open set `Ω ⊆ ℂⁿ` and `f : ℂⁿ → ℂ` of class `C^{k+1}` on `Ω`, the `(k+1)`-th Hölder
seminorm of `f` is bounded by the sum of the `k`-th Hölder seminorms of the `2n` real
directional derivatives `z ↦ Df(z)(δ)` along the standard *real* directions
`δ ∈ {e_j, i e_j : j < n}`.

The mechanism is elementary.  Writing `T := D^{k+1}_Ω f x - D^{k+1}_Ω f y`, a `(k+1)`-multilinear
map on `ℂⁿ`, one has `‖T‖ ≤ Σ_p ‖T(·,…,·,δ_p)‖`: indeed, for a tuple `w` whose last argument is
`a = Σ_p c_p(a) δ_p` with `|c_p(a)| ≤ ‖a‖`, multilinearity in the last variable gives
`T w = Σ_p c_p(a) · T(·,…,·,δ_p) w`, whence the bound.  Each slice `T(·,…,·,δ_p)` is, by
`iteratedFDerivWithin_succ_eq_comp_right`, the difference of the `k`-th iterated derivatives of
the directional derivative `z ↦ Df(z)(δ_p)`, and the estimate follows by dividing by
`‖x - y‖ ^ α` and taking suprema.
-/
import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc

namespace Work.NN.Core

open scoped NNReal ENNReal
open Set

noncomputable section

/-! ### The standard real basis of `ℂⁿ` -/

/-- The `2n` vectors of the standard *real* basis of `ℂⁿ = (Fin n → ℂ)`: the `j`-th standard
basis vector, multiplied by `1` or by `I`. -/
private def nnb (n : ℕ) (j : Fin n) (b : Bool) : Fin n → ℂ :=
  if b then Pi.single j Complex.I else Pi.single j (1 : ℂ)

/-- The real coordinate of a complex number in the basis `(1, I)`. -/
private def nnc (z : ℂ) (b : Bool) : ℝ := if b then z.im else z.re

@[simp] private lemma nnc_true (z : ℂ) : nnc z true = z.im := by rw [nnc]; simp
@[simp] private lemma nnc_false (z : ℂ) : nnc z false = z.re := by rw [nnc]; simp

private lemma abs_nnc_le (z : ℂ) (b : Bool) : |nnc z b| ≤ ‖z‖ := by
  rw [nnc]; split
  · exact Complex.abs_im_le_norm z
  · exact Complex.abs_re_le_norm z

private lemma nnc_smul_nnb (n : ℕ) (z : Fin n → ℂ) (j : Fin n) :
    nnc (z j) true • nnb n j true + nnc (z j) false • nnb n j false = Pi.single j (z j) := by
  rw [nnc_true, nnc_false]
  ext j'
  by_cases h : j' = j
  · rw [h]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same]
    rw [show nnb n j true j = Complex.I from by rw [nnb]; simp,
      show nnb n j false j = (1:ℂ) from by rw [nnb]; simp]
    simp only [Complex.real_smul, mul_one]
    conv_rhs => rw [← Complex.re_add_im (z j)]
    ring
  · simp [h, nnb]

/-- Decomposition of a vector of `ℂⁿ` in the standard real basis. -/
private lemma sum_nnc_nnb (n : ℕ) (z : Fin n → ℂ) :
    ∑ p : Fin n × Bool, nnc (z p.1) p.2 • nnb n p.1 p.2 = z := by
  calc ∑ p : Fin n × Bool, nnc (z p.1) p.2 • nnb n p.1 p.2
      = ∑ j : Fin n, ∑ b : Bool, nnc (z j) b • nnb n j b := Fintype.sum_prod_type _
    _ = ∑ j : Fin n, (nnc (z j) true • nnb n j true + nnc (z j) false • nnb n j false) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Fintype.sum_bool]
    _ = ∑ j : Fin n, Pi.single j (z j) := Finset.sum_congr rfl fun j _ => nnc_smul_nnb n z j
    _ = z := Finset.univ_sum_single z

private lemma nnb_norm_le (n : ℕ) (j : Fin n) (b : Bool) : ‖nnb n j b‖ ≤ 1 := by
  rw [nnb]; split <;> rw [Pi.norm_single] <;> simp

/-! ### Fixing the last argument of a multilinear map -/

/-- The `k`-multilinear map `T(·,…,·,δ)` obtained by fixing the last argument of the
`(k+1)`-multilinear map `T` to be `δ`. -/
private def sliceOp {k n : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => (Fin n → ℂ)) ℂ)
    (δ : Fin n → ℂ) : ContinuousMultilinearMap ℝ (fun _ : Fin k => (Fin n → ℂ)) ℂ :=
  (ContinuousLinearMap.apply ℝ ℂ δ).compContinuousMultilinearMap
    ((continuousMultilinearCurryRightEquiv' ℝ k (Fin n → ℂ) ℂ) T)

private lemma sliceOp_apply {k n : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => (Fin n → ℂ)) ℂ)
    (δ : Fin n → ℂ) (v : Fin k → (Fin n → ℂ)) :
    sliceOp T δ v = T (Fin.snoc v δ) := by
  rw [sliceOp, ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousLinearMap.apply_apply, continuousMultilinearCurryRightEquiv_apply']

/-- The operator norm of a continuous multilinear map on `ℂⁿ` is bounded by the sum of the
operator norms of its `2n` slices obtained by fixing the last argument to be a vector of the
standard *real* basis. -/
private lemma opNorm_le_sum_sliceOp {k n : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => (Fin n → ℂ)) ℂ) :
    ‖T‖ ≤ ∑ p : Fin n × Bool, ‖sliceOp T (nnb n p.1 p.2)‖ := by
  set C : ℝ := ∑ p : Fin n × Bool, ‖sliceOp T (nnb n p.1 p.2)‖ with hCdef
  have hC : 0 ≤ C := Finset.sum_nonneg fun p _ => norm_nonneg _
  rw [ContinuousMultilinearMap.opNorm_le_iff hC]
  intro w
  set U : ContinuousMultilinearMap ℝ (fun _ : Fin k => (Fin n → ℂ))
      ((Fin n → ℂ) →L[ℝ] ℂ) :=
    (continuousMultilinearCurryRightEquiv' ℝ k (Fin n → ℂ) ℂ) T with hUdef
  set v : Fin k → (Fin n → ℂ) := Fin.init w with hvdef
  set a : Fin n → ℂ := w (Fin.last k) with hadef
  have hw : T w = U v a := by
    rw [hUdef, hvdef, hadef, continuousMultilinearCurryRightEquiv_apply']
    exact congrArg T (Fin.snoc_init_self w).symm
  have hexp : U v a = ∑ p : Fin n × Bool, nnc (a p.1) p.2 • (U v (nnb n p.1 p.2)) := by
    conv_lhs => rw [← sum_nnc_nnb n a]
    rw [map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_smul]
  have hterm : ∀ p : Fin n × Bool,
      ‖nnc (a p.1) p.2 • (U v (nnb n p.1 p.2))‖
        ≤ ‖a‖ * (‖sliceOp T (nnb n p.1 p.2)‖ * ∏ i, ‖v i‖) := by
    intro p
    have hδ : U v (nnb n p.1 p.2) = sliceOp T (nnb n p.1 p.2) v := by
      rw [hUdef, continuousMultilinearCurryRightEquiv_apply', sliceOp_apply]
    rw [norm_smul, Real.norm_eq_abs, hδ]
    refine (mul_le_mul_of_nonneg_right
      ((abs_nnc_le (a p.1) p.2).trans (norm_le_pi_norm a p.1)) (norm_nonneg _)).trans ?_
    exact mul_le_mul_of_nonneg_left (ContinuousMultilinearMap.le_opNorm _ _) (norm_nonneg a)
  rw [hw, hexp]
  have hv : (∏ i : Fin k, ‖w i.castSucc‖) = ∏ i : Fin k, ‖v i‖ :=
    Finset.prod_congr rfl fun i _ => by rw [hvdef]; rfl
  calc ‖∑ p : Fin n × Bool, nnc (a p.1) p.2 • (U v (nnb n p.1 p.2))‖
      ≤ ∑ p : Fin n × Bool, ‖nnc (a p.1) p.2 • (U v (nnb n p.1 p.2))‖ := norm_sum_le _ _
    _ ≤ ∑ p : Fin n × Bool, ‖a‖ * (‖sliceOp T (nnb n p.1 p.2)‖ * ∏ i, ‖v i‖) :=
        Finset.sum_le_sum fun p _ => hterm p
    _ = C * ∏ i, ‖w i‖ := by
        rw [hCdef, Fin.prod_univ_castSucc, hv, hadef, Finset.sum_mul]
        exact Finset.sum_congr rfl fun p _ => by ring

/-! ### The main estimate -/

theorem holderSeminorm_succ_le_dir {n k : ℕ} {α : ℝ} {Ω : Set (Fin n → ℂ)} {f : (Fin n → ℂ) → ℂ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ (((k+1 : ℕ)) : WithTop ENat) f Ω) :
    Work.CR.Flat.holderSeminorm (k+1) α f Ω
      ≤ ∑ p : Fin n × Bool, Work.CR.Flat.holderSeminorm k α
          (fun z => fderiv ℝ f z
            (if p.2 then Pi.single p.1 Complex.I else Pi.single p.1 (1 : ℂ))) Ω := by
  have hΩu : UniqueDiffOn ℝ Ω := hΩ.uniqueDiffOn
  have hm : (((k : ℕ)) : WithTop ENat) + 1 ≤ (((k+1 : ℕ)) : WithTop ENat) := by
    rw [← Nat.cast_one, ← Nat.cast_add]
  have hΦ : ContDiffOn ℝ (((k : ℕ)) : WithTop ENat) (fun z => fderivWithin ℝ f Ω z) Ω :=
    hf.fderivWithin hΩu hm
  -- The `k`-th derivative of a directional derivative is the corresponding slice of `D^{k+1}f`.
  have hslice : ∀ z ∈ Ω, ∀ δ : Fin n → ℂ,
      iteratedFDerivWithin ℝ k (fun w => fderivWithin ℝ f Ω w δ) Ω z
        = sliceOp (iteratedFDerivWithin ℝ (k+1) f Ω z) δ := by
    intro z hz δ
    have hleft : (fun w => fderivWithin ℝ f Ω w δ)
        = (ContinuousLinearMap.apply ℝ ℂ δ) ∘ (fun w => fderivWithin ℝ f Ω w) := by
      funext w
      rw [Function.comp_apply, ContinuousLinearMap.apply_apply]
    have hcomp := (ContinuousLinearMap.apply ℝ ℂ δ).iteratedFDerivWithin_comp_left
      (hΦ z hz) hΩu hz (le_rfl : (((k:ℕ)) : WithTop ENat) ≤ (((k:ℕ)) : WithTop ENat))
    have hcurry : iteratedFDerivWithin ℝ k (fun w => fderivWithin ℝ f Ω w) Ω z
        = (continuousMultilinearCurryRightEquiv' ℝ k (Fin n → ℂ) ℂ)
            (iteratedFDerivWithin ℝ (k+1) f Ω z) := by
      have h := iteratedFDerivWithin_succ_eq_comp_right (𝕜 := ℝ) (f := f) (s := Ω) (x := z)
        (n := k) hΩu hz
      rw [h, Function.comp_apply]
      simp
    rw [hleft, hcomp, hcurry]
    rfl
  -- The pointwise Hölder estimate.
  have hkey : ∀ x ∈ Ω, ∀ y ∈ Ω, x ≠ y →
      ENNReal.ofReal (‖iteratedFDerivWithin ℝ (k+1) f Ω x
          - iteratedFDerivWithin ℝ (k+1) f Ω y‖ / ‖x - y‖ ^ α)
        ≤ ∑ p : Fin n × Bool, Work.CR.Flat.holderSeminorm k α
            (fun z => fderiv ℝ f z (nnb n p.1 p.2)) Ω := by
    intro x hx y hy hxy
    have hcX : ∀ δ : Fin n → ℂ,
        iteratedFDerivWithin ℝ k (fun z => fderivWithin ℝ f Ω z δ) Ω x
          = iteratedFDerivWithin ℝ k (fun z => fderiv ℝ f z δ) Ω x :=
      fun δ => iteratedFDerivWithin_congr
        (fun z hz => by rw [fderivWithin_of_isOpen hΩ hz]) hx k
    have hcY : ∀ δ : Fin n → ℂ,
        iteratedFDerivWithin ℝ k (fun z => fderivWithin ℝ f Ω z δ) Ω y
          = iteratedFDerivWithin ℝ k (fun z => fderiv ℝ f z δ) Ω y :=
      fun δ => iteratedFDerivWithin_congr
        (fun z hz => by rw [fderivWithin_of_isOpen hΩ hz]) hy k
    have hsub : ∀ δ : Fin n → ℂ,
        sliceOp (iteratedFDerivWithin ℝ (k+1) f Ω x - iteratedFDerivWithin ℝ (k+1) f Ω y) δ
          = sliceOp (iteratedFDerivWithin ℝ (k+1) f Ω x) δ
            - sliceOp (iteratedFDerivWithin ℝ (k+1) f Ω y) δ := by
      intro δ
      ext v
      simp only [sliceOp_apply, sub_apply]
    have hT : ∀ δ : Fin n → ℂ,
        sliceOp (iteratedFDerivWithin ℝ (k+1) f Ω x - iteratedFDerivWithin ℝ (k+1) f Ω y) δ
          = iteratedFDerivWithin ℝ k (fun z => fderiv ℝ f z δ) Ω x
            - iteratedFDerivWithin ℝ k (fun z => fderiv ℝ f z δ) Ω y := by
      intro δ
      rw [hsub δ, ← hslice x hx δ, ← hslice y hy δ, hcX δ, hcY δ]
    have hstep : ‖iteratedFDerivWithin ℝ (k+1) f Ω x
          - iteratedFDerivWithin ℝ (k+1) f Ω y‖
        ≤ ∑ p : Fin n × Bool,
            ‖iteratedFDerivWithin ℝ k (fun z => fderiv ℝ f z (nnb n p.1 p.2)) Ω x
              - iteratedFDerivWithin ℝ k (fun z => fderiv ℝ f z (nnb n p.1 p.2)) Ω y‖ :=
      (opNorm_le_sum_sliceOp _).trans
        (Finset.sum_le_sum fun p _ => by rw [hT (nnb n p.1 p.2)])
    have hcp : 0 < ‖x - y‖ ^ α :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
    calc ENNReal.ofReal (‖iteratedFDerivWithin ℝ (k+1) f Ω x
            - iteratedFDerivWithin ℝ (k+1) f Ω y‖ / ‖x - y‖ ^ α)
        ≤ ENNReal.ofReal ((∑ p : Fin n × Bool,
            ‖iteratedFDerivWithin ℝ k (fun z => fderiv ℝ f z (nnb n p.1 p.2)) Ω x
              - iteratedFDerivWithin ℝ k (fun z => fderiv ℝ f z (nnb n p.1 p.2)) Ω y‖)
            / ‖x - y‖ ^ α) :=
          ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hstep (le_of_lt hcp))
      _ = ∑ p : Fin n × Bool, ENNReal.ofReal
            (‖iteratedFDerivWithin ℝ k (fun z => fderiv ℝ f z (nnb n p.1 p.2)) Ω x
              - iteratedFDerivWithin ℝ k (fun z => fderiv ℝ f z (nnb n p.1 p.2)) Ω y‖
              / ‖x - y‖ ^ α) := by
          rw [Finset.sum_div, ENNReal.ofReal_sum_of_nonneg
            (fun p _ => div_nonneg (norm_nonneg _) (le_of_lt hcp))]
      _ ≤ ∑ p : Fin n × Bool, Work.CR.Flat.holderSeminorm k α
            (fun z => fderiv ℝ f z (nnb n p.1 p.2)) Ω :=
          Finset.sum_le_sum fun p _ =>
            Work.CR.Flat.le_holderSeminorm k α _ Ω hx hy hxy
  rw [show Work.CR.Flat.holderSeminorm (k+1) α f Ω
      = ⨆ x ∈ Ω, ⨆ y ∈ Ω, ⨆ (_ : x ≠ y),
          ENNReal.ofReal (‖iteratedFDerivWithin ℝ (k+1) f Ω x
            - iteratedFDerivWithin ℝ (k+1) f Ω y‖ / ‖x - y‖ ^ α) from rfl]
  exact iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => hkey x hx y hy hxy

end

end Work.NN.Core
