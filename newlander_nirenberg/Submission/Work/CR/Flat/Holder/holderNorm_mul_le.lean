import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Holder.Bilinear
import Submission.Work.CR.Flat.Holder.hSN_bilinear_le

namespace Work.CR.Flat.Holder

open scoped NNReal ENNReal
open Set

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ### Transfer of the norms along a linear isometry -/

section Transfer

variable {A A' : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup A'] [NormedSpace ℝ A']

lemma contDiffOn_comp_lie (e : A ≃ₗᵢ[ℝ] A') {f : X → A} {Ω : Set X} {n : ℕ}
    (hf : ContDiffOn ℝ n f Ω) : ContDiffOn ℝ n (fun x => e (f x)) Ω := by
  show ContDiffOn ℝ n (⇑e ∘ f) Ω
  exact (e : A →L[ℝ] A').contDiff.comp_contDiffOn hf

lemma iDN_comp_lie (e : A ≃ₗᵢ[ℝ] A') (f : X → A) (i : ℕ) (Ω : Set X)
    (hΩ : UniqueDiffOn ℝ Ω) : iDN i (fun x => e (f x)) Ω = iDN i f Ω := by
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun x hx => ?_
    show ENNReal.ofReal ‖iteratedFDerivWithin ℝ i (⇑e ∘ f) Ω x‖ ≤ iDN i f Ω
    rw [LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_left e f hΩ hx i]
    exact le_iSup₂_of_le x hx le_rfl
  · refine iSup₂_le fun x hx => ?_
    refine le_iSup₂_of_le x hx ?_
    show ENNReal.ofReal ‖iteratedFDerivWithin ℝ i f Ω x‖ ≤
      ENNReal.ofReal ‖iteratedFDerivWithin ℝ i (⇑e ∘ f) Ω x‖
    rw [LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_left e f hΩ hx i]

lemma hSN_comp_lie (e : A ≃ₗᵢ[ℝ] A') (f : X → A) (i : ℕ) (α : ℝ) (Ω : Set X)
    (hΩ : UniqueDiffOn ℝ Ω) : hSN i α (fun x => e (f x)) Ω = hSN i α f Ω := by
  have key : ∀ x ∈ Ω, ∀ y ∈ Ω,
      ‖iteratedFDerivWithin ℝ i (fun x => e (f x)) Ω x
          - iteratedFDerivWithin ℝ i (fun x => e (f x)) Ω y‖
        = ‖iteratedFDerivWithin ℝ i f Ω x - iteratedFDerivWithin ℝ i f Ω y‖ := by
    intro x hx y hy
    have h1 : ∀ z ∈ Ω, iteratedFDerivWithin ℝ i (fun x => e (f x)) Ω z
        = (e : A →L[ℝ] A').compContinuousMultilinearMap (iteratedFDerivWithin ℝ i f Ω z) := by
      intro z hz
      show iteratedFDerivWithin ℝ i (⇑e ∘ f) Ω z
        = (e : A →L[ℝ] A').compContinuousMultilinearMap (iteratedFDerivWithin ℝ i f Ω z)
      exact ContinuousLinearEquiv.iteratedFDerivWithin_comp_left (e : A ≃L[ℝ] A') f hΩ hz i
    rw [h1 x hx, h1 y hy]
    rw [show (e : A →L[ℝ] A').compContinuousMultilinearMap (iteratedFDerivWithin ℝ i f Ω x)
          - (e : A →L[ℝ] A').compContinuousMultilinearMap (iteratedFDerivWithin ℝ i f Ω y)
        = (e : A →L[ℝ] A').compContinuousMultilinearMap
            (iteratedFDerivWithin ℝ i f Ω x - iteratedFDerivWithin ℝ i f Ω y) from by
      ext m
      simp [ContinuousLinearMap.compContinuousMultilinearMap_coe, ← map_sub]]
    rw [show (e : A →L[ℝ] A') = e.toLinearIsometry.toContinuousLinearMap from rfl]
    exact LinearIsometry.norm_compContinuousMultilinearMap e.toLinearIsometry _
  unfold hSN
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    rw [key x hx y hy]
    exact le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy le_rfl))
  · refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    refine le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy ?_))
    rw [key x hx y hy]

end Transfer

/-! ### The product bounds -/

/-- The sup-norm part of the Leibniz bound for a product of `ℂ`-valued functions. -/
lemma iDN_mul_le {i : ℕ} {f g : X → ℂ} {Ω : Set X}
    (hf : ContDiffOn ℝ i f Ω) (hg : ContDiffOn ℝ i g Ω) (hΩ : UniqueDiffOn ℝ Ω) :
    iDN i (fun x => f x * g x) Ω
      ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) * (iDN j f Ω * iDN (i - j) g Ω) := by
  calc iDN i (fun x => f x * g x) Ω
      ≤ ENNReal.ofReal ‖ContinuousLinearMap.mul ℝ ℂ‖ *
          ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) * (iDN j f Ω * iDN (i - j) g Ω) :=
        iDN_bilinear_le (ContinuousLinearMap.mul ℝ ℂ) i hf hg hΩ
    _ ≤ 1 * ∑ j ∈ Finset.range (i + 1),
          (i.choose j : ℝ≥0∞) * (iDN j f Ω * iDN (i - j) g Ω) := by
        gcongr
        exact ENNReal.ofReal_le_one.mpr (ContinuousLinearMap.opNorm_mul_le ℝ ℂ)
    _ = _ := one_mul _

/-- The elementary ENNReal inequality behind the sharp grouping of the Leibniz terms. -/
private lemma mul_add_le_mul_add (a b c d : ℝ≥0∞) :
    a * c + (b * c + a * d) ≤ (a + b) * (c + d) := by
  calc a * c + (b * c + a * d) = (a * c + b * c) + a * d := by ac_rfl
    _ ≤ (a * c + b * c) + (a * d + b * d) := by
        gcongr
        exact le_add_right le_rfl
    _ = (a + b) * (c + d) := by rw [mul_add, add_mul, add_mul]

/-- The space of `C^{k,α}` functions on `Ω` is a Banach algebra: the `C^{k,α}` norm
of `Submission/Work/CR/Flat/Holder.lean` of a pointwise product is bounded by a
constant depending only on `k` times the product of the norms, for functions whose
norm is finite.

The classical content is the Leibniz rule for iterated derivatives of a product
together with `[u*v]_α ≤ ‖u‖_∞ [v]_α + [u]_α ‖v‖_∞`.  The constant
`(k+1) * 2^(k+1)` is a valid (generous) one, coming from the binomial expansion
`Σ_{i≤k} 2^i ≤ 2^(k+1) - 1 ≤ (k+1) * 2^(k+1)`; only the fact that it depends
on `k` alone matters for applications. -/
theorem holderNorm_mul_le {k : ℕ} {α : ℝ} {f g : X → ℂ} {Ω : Set X}
    (hf : ContDiffOn ℝ (k : ℕ∞) f Ω) (hg : ContDiffOn ℝ (k : ℕ∞) g Ω)
    (hΩ : UniqueDiffOn ℝ Ω)
    (hf' : holderNorm k α f Ω ≠ ⊤) (hg' : holderNorm k α g Ω ≠ ⊤) :
    holderNorm k α (fun x => f x * g x) Ω
      ≤ ((k : ℝ≥0∞) + 1) * 2 ^ (k + 1) * holderNorm k α f Ω * holderNorm k α g Ω := by
  have hfk : ∀ i, i ≤ k → ContDiffOn ℝ i f Ω := fun i hi => hf.of_le (by exact_mod_cast hi)
  have hgk : ∀ i, i ≤ k → ContDiffOn ℝ i g Ω := fun i hi => hg.of_le (by exact_mod_cast hi)
  -- Lift `ℂ` to the universe of `X`, so that `X` and the target space live in a common universe.
  let e : ℂ ≃ₗᵢ[ℝ] ULift ℂ := (LinearIsometryEquiv.ulift ℝ ℂ).symm
  let F : X → ULift ℂ := fun x => e (f x)
  let G : X → ULift ℂ := fun x => e (g x)
  have hSF : ∀ j, hSN j α F Ω = hSN j α f Ω := fun j => hSN_comp_lie e f j α Ω hΩ
  have hSG : ∀ j, hSN j α G Ω = hSN j α g Ω := fun j => hSN_comp_lie e g j α Ω hΩ
  have hIF : ∀ j, iDN j F Ω = iDN j f Ω := fun j => iDN_comp_lie e f j Ω hΩ
  have hIG : ∀ j, iDN j G Ω = iDN j g Ω := fun j => iDN_comp_lie e g j Ω hΩ
  have hFG : (fun x => F x * G x) = fun x => e (f x * g x) := by
    funext x
    exact rfl
  -- the Leibniz/Hölder bound for the top-order seminorm of the product
  have hS : ∀ i, i ≤ k → hSN i α (fun x => f x * g x) Ω ≤
      ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
        (hSN j α f Ω * iDN (i - j) g Ω + iDN j f Ω * hSN (i - j) α g Ω) := by
    intro i hi
    have hb := hSN_bilinear_le (E := ULift ℂ) (F := ULift ℂ) (G := ULift ℂ)
      (B := ContinuousLinearMap.mul ℝ (ULift ℂ)) i α (f := F) (g := G) (Ω := Ω)
      (contDiffOn_comp_lie e (hfk i hi)) (contDiffOn_comp_lie e (hgk i hi)) hΩ
    have hbL : hSN i α (fun x => (ContinuousLinearMap.mul ℝ (ULift ℂ) (F x)) (G x)) Ω
        = hSN i α (fun x => f x * g x) Ω := by
      rw [show (fun x => (ContinuousLinearMap.mul ℝ (ULift ℂ) (F x)) (G x))
            = (fun x => F x * G x) from rfl, hFG]
      exact hSN_comp_lie e (fun x => f x * g x) i α Ω hΩ
    rw [hbL] at hb
    have hbR : (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
          (hSN j α F Ω * iDN (i - j) G Ω + iDN j F Ω * hSN (i - j) α G Ω))
        = ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
          (hSN j α f Ω * iDN (i - j) g Ω + iDN j f Ω * hSN (i - j) α g Ω) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hSF j, hIG (i - j), hIF j, hSG (i - j)]
    refine hb.trans ?_
    rw [hbR]
    calc ENNReal.ofReal ‖ContinuousLinearMap.mul ℝ (ULift ℂ)‖ *
          ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
            (hSN j α f Ω * iDN (i - j) g Ω + iDN j f Ω * hSN (i - j) α g Ω)
        ≤ 1 * ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
            (hSN j α f Ω * iDN (i - j) g Ω + iDN j f Ω * hSN (i - j) α g Ω) := by
          gcongr
          exact ENNReal.ofReal_le_one.mpr (ContinuousLinearMap.opNorm_mul_le ℝ (ULift ℂ))
      _ = _ := one_mul _
  -- finiteness of the individual pieces
  have hNf : ∀ j, j ≤ k → iDN j f Ω + hSN j α f Ω ≤ holderNorm k α f Ω := by
    intro j hj
    show iDN j f Ω + hSN j α f Ω ≤ ∑ l ∈ Finset.range (k + 1), (iDN l f Ω + hSN l α f Ω)
    exact Finset.single_le_sum (f := fun l => iDN l f Ω + hSN l α f Ω)
      (fun _ _ => bot_le) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  have hNg : ∀ j, j ≤ k → iDN j g Ω + hSN j α g Ω ≤ holderNorm k α g Ω := by
    intro j hj
    show iDN j g Ω + hSN j α g Ω ≤ ∑ l ∈ Finset.range (k + 1), (iDN l g Ω + hSN l α g Ω)
    exact Finset.single_le_sum (f := fun l => iDN l g Ω + hSN l α g Ω)
      (fun _ _ => bot_le) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  -- the order-`i` bound
  have key : ∀ i, i ≤ k →
      iDN i (fun x => f x * g x) Ω + hSN i α (fun x => f x * g x) Ω
        ≤ (2 : ℝ≥0∞) ^ i * holderNorm k α f Ω * holderNorm k α g Ω := by
    intro i hi
    have hI := iDN_mul_le (f := f) (g := g) (Ω := Ω) (hfk i hi) (hgk i hi) hΩ
    have hH := hS i hi
    have hstep : ∑ j ∈ Finset.range (i + 1),
          ((i.choose j : ℝ≥0∞) * (iDN j f Ω * iDN (i - j) g Ω)
            + (i.choose j : ℝ≥0∞) *
              (hSN j α f Ω * iDN (i - j) g Ω + iDN j f Ω * hSN (i - j) α g Ω))
        ≤ ∑ j ∈ Finset.range (i + 1),
            (i.choose j : ℝ≥0∞) * (holderNorm k α f Ω * holderNorm k α g Ω) := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hj' : j ≤ k := le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hi
      have hji : i - j ≤ k := le_trans (Nat.sub_le i j) hi
      rw [← mul_add]
      gcongr
      calc iDN j f Ω * iDN (i - j) g Ω
            + (hSN j α f Ω * iDN (i - j) g Ω + iDN j f Ω * hSN (i - j) α g Ω)
          ≤ (iDN j f Ω + hSN j α f Ω) * (iDN (i - j) g Ω + hSN (i - j) α g Ω) :=
            mul_add_le_mul_add _ _ _ _
        _ ≤ holderNorm k α f Ω * holderNorm k α g Ω := by
            gcongr
            · exact hNf j hj'
            · exact hNg (i - j) hji
    have htail : ∑ j ∈ Finset.range (i + 1),
          (i.choose j : ℝ≥0∞) * (holderNorm k α f Ω * holderNorm k α g Ω)
        ≤ (2 : ℝ≥0∞) ^ i * holderNorm k α f Ω * holderNorm k α g Ω := by
      have h1 : (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞)) = (2 : ℝ≥0∞) ^ i := by
        exact_mod_cast Nat.sum_range_choose i
      rw [← Finset.sum_mul, h1, mul_assoc]
    refine (add_le_add hI hH).trans ?_
    rw [← Finset.sum_add_distrib]
    exact hstep.trans htail
  have hsum2 : (∑ i ∈ Finset.range (k + 1), (2 : ℝ≥0∞) ^ i) ≤
      ((k : ℝ≥0∞) + 1) * 2 ^ (k + 1) := by
    calc (∑ i ∈ Finset.range (k + 1), (2 : ℝ≥0∞) ^ i)
        ≤ ∑ i ∈ Finset.range (k + 1), 2 ^ (k + 1) :=
          Finset.sum_le_sum fun i hi =>
            pow_le_pow_right₀ (by norm_num) (by have := Finset.mem_range.mp hi; omega)
      _ = (k + 1) • (2 ^ (k + 1) : ℝ≥0∞) := by rw [Finset.sum_const, Finset.card_range]
      _ = ((k : ℝ≥0∞) + 1) * 2 ^ (k + 1) := by
          rw [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  calc holderNorm k α (fun x => f x * g x) Ω
      ≤ ∑ i ∈ Finset.range (k + 1),
          (2 : ℝ≥0∞) ^ i * holderNorm k α f Ω * holderNorm k α g Ω := by
        rw [show holderNorm k α (fun x => f x * g x) Ω
            = ∑ i ∈ Finset.range (k + 1),
                (iDN i (fun x => f x * g x) Ω + hSN i α (fun x => f x * g x) Ω) from rfl]
        exact Finset.sum_le_sum fun i hi =>
          key i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    _ = (∑ i ∈ Finset.range (k + 1), (2 : ℝ≥0∞) ^ i) * holderNorm k α f Ω
          * holderNorm k α g Ω := by rw [← Finset.sum_mul, ← Finset.sum_mul]
    _ ≤ ((k : ℝ≥0∞) + 1) * 2 ^ (k + 1) * holderNorm k α f Ω * holderNorm k α g Ω := by
        gcongr

end Work.CR.Flat.Holder
