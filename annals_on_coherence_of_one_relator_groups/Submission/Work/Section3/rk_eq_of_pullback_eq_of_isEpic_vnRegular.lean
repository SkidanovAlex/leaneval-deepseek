import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.Epic
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.Epic.tmul_one_eq_tmul_one_of_isEpic
import Submission.Work.Section3.rank_eq_of_element_rank_eq
import Submission.Work.Section3.RkFinModel.Defs
import Submission.Work.Section3.exists_fp_model_of_tmul_eq_zero
import Submission.Work.Section3.rank_diff_of_fp_model_elementwise

set_option autoImplicit false

universe u

namespace Work.Section3

open Matrix Work.ORHughesFree

/-- For `s` in a von Neumann regular ring there is an idempotent `g` with `g * s = s` and
`g = s * c` for some `c`, and every Sylvester rank function takes the same value on `s` as on `g`.
(These are exactly the elementwise hypotheses of
`Work.Section3.rank_diff_of_fp_model_elementwise`.) -/
private theorem exists_idempotent_of_oneByOne {U : Type*} [Ring U] [VonNeumannRegularRing U]
    (s : U) :
    ∃ g : U, g * g = g ∧ g * s = s ∧ (∃ c : U, g = s * c) ∧
      ∀ (ρ : SylvesterRank U), ρ.rk 1 1 (oneByOne s) = ρ.rk 1 1 (oneByOne g) := by
  obtain ⟨g, hg, h1, h2⟩ := exists_idem_row (oneByOne s) (U := U)
  have h1' : g * s = s := by simpa [oneByOne] using h1 0
  have hc' : ∃ c' : U, g = s * c' := by
    obtain ⟨c, hc⟩ := h2
    refine ⟨c 0, ?_⟩
    simpa [oneByOne] using hc
  exact ⟨g, hg, h1', hc', fun ρ => rk_row_eq_rk_oneByOne ρ (oneByOne s) g hg h1 h2⟩

/-- `a ⊗ 0 = 0` in the `R`-balanced tensor square. -/
private theorem tmul_right_zero {R S : Type u} [Ring R] [Ring S] (f : R →+* S) (a : S) :
    Epic.BalancedTensor.tmul f a (0 : S) = 0 := by
  show Epic.BalancedTensor.mk f (a ⊗ₜ[ℤ] (0 : S)) = 0
  rw [TensorProduct.tmul_zero, map_zero]

/-- If `z * s = 0` and `f` is epic then `z ⊗[R] s = 0` in the `R`-balanced tensor square
(Silver's relation). -/
private theorem balanced_tmul_eq_zero_of_mul_eq_zero {R S : Type u} [Ring R] [Ring S]
    (f : R →+* S) (hf : IsEpic f) {z s : S} (hzs : z * s = 0) :
    Epic.BalancedTensor.tmul f z s = 0 := by
  have hsil : Epic.BalancedTensor.tmul f z 1 = Epic.BalancedTensor.tmul f 1 z :=
    Epic.tmul_one_eq_tmul_one_of_isEpic f hf z
  have h1 : Epic.BalancedTensor.tmul f z s
      = Epic.BalancedTensor.smulRight f s (Epic.BalancedTensor.tmul f 1 z) := by
    rw [← hsil, Epic.BalancedTensor.smulRight_tmul, one_mul]
  rw [h1, Epic.BalancedTensor.smulRight_tmul, hzs, tmul_right_zero]

theorem rk_eq_of_pullback_eq_of_isEpic_vnRegular {R S : Type u} [Ring R] [Ring S]
    [Work.ORHughesFree.VonNeumannRegularRing S] (f : R →+* S) (hf : Work.ORHughesFree.IsEpic f)
    (rk₁ rk₂ : Work.ORHughesFree.SylvesterRank S)
    (h : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) R),
      rk₁.rk n m (A.map f) = rk₂.rk n m (A.map f)) :
    ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) S), rk₁.rk n m A = rk₂.rk n m A := by
  -- it suffices to compare the two rank functions on `1 × 1` matrices
  refine rank_eq_of_element_rank_eq rk₁ rk₂ ?_
  intro s
  -- an idempotent `g` with `g * s = s`, `g = s * c`, and `ρ s = ρ g` for every rank function `ρ`
  obtain ⟨g, hg, hgs, ⟨c, hgc⟩, _hrank⟩ := exists_idempotent_of_oneByOne s
  -- `(1 - g) * s = 0`, hence `(1 - g) ⊗[R] s = 0` in `S ⊗[R] S`
  have hzs : (1 - g) * s = 0 := by rw [sub_mul, one_mul, hgs, sub_self]
  have hz : Epic.BalancedTensor.tmul f (1 - g) s = 0 :=
    balanced_tmul_eq_zero_of_mul_eq_zero f hf hzs
  -- a finitely presented model `L` with `φ r = s` and `(1 - g) ⊗[R] r = 0`
  obtain ⟨L, hL1, hL2, hL3, φ, hφ, r, hr, hzr⟩ :=
    Work.Section3.exists_fp_model_of_tmul_eq_zero (R := R) (S := S) f hz
  -- the rank of `s` is a difference of two values of the rank function on `R`-matrices
  obtain ⟨m₁, m₂, n, A₁, A₂, hA⟩ :=
    Work.Section3.rank_diff_of_fp_model_elementwise (f := f) hg hgs ⟨c, hgc⟩ φ hφ r hr hzr
  -- the two rank functions agree on those `R`-matrices
  rw [hA rk₁, hA rk₂, h m₁ n A₁, h m₂ n A₂]

end Work.Section3
