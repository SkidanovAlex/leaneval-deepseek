import ChallengeDeps
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Submission.Commons.Topology.Algebra.Valued.nonarchimedeanAddGroup
import Submission.Commons.Topology.Algebra.Valued.nonarchimedeanRing
import Submission.Commons.Topology.Algebra.Valued.exp_balls_is_basis
import Submission.Commons.FieldTheory.Polynomial.finite_monic_le
import Submission.Commons.FieldTheory.Polynomial.finite_monic_lt
import Submission.ZagierHoffmanProof.CompletionInstances
import Submission.ZagierHoffmanProof.Valuation

set_option autoImplicit false

open Filter Polynomial RatFunc
open scoped WithZero Topology BigOperators
open WithZero

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- `exp` turns sums into products over finite index sets. -/
lemma exp_sum (ι : Type*) (s : Finset ι) (f : ι → ℤ) :
    (s.prod fun i => exp (f i)) = exp (s.sum f) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s his ih
    rw [Finset.prod_insert his, Finset.sum_insert his, ih, exp_add]

/-- valuation of the image of a nonzero monic polynomial: `Valued.v p = exp (natDegree p)`. -/
lemma v_image_monic (p : F[X]) (hp : p.Monic) :
    Valued.v ((p : RatFunc F) : RatFunc.CompletionAtInfty F) = exp (p.natDegree : ℤ) := by
  exact inftyValued_v_polynomial F p hp.ne_zero

/-- valuation of a finite product of elements of the completion. -/
lemma v_prod (ι : Type*) (s : Finset ι)
    (g : ι → RatFunc.CompletionAtInfty F) :
    Valued.v (s.prod g) = s.prod (fun i => Valued.v (g i)) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s his ih
    rw [Finset.prod_insert his, Finset.prod_insert his]
    rw [map_mul (Valued.v)]
    rw [ih]

/-- inverse of a valuation equals valuation of the inverse (field case, no side conditions). -/
lemma v_inv (x : RatFunc.CompletionAtInfty F) :
    Valued.v (x⁻¹) = (Valued.v x)⁻¹ := by
  simpa [RatFunc.valuedCompletionAtInfty.def]

/-- The value of one summand of a depth-`r` multiple zeta sum of index `𝔰`. -/
lemma zeta_term_val {r : ℕ} (𝔰 : Fin r → ℕ+) (a : monicStrictAntiNatDegree F r) :
    Valued.v ((∏ i : Fin r, ((a.val i : RatFunc F) : RatFunc.CompletionAtInfty F) ^ (𝔰 i : ℕ))⁻¹)
      = exp (-(∑ i : Fin r, (𝔰 i : ℤ) * ((a.val i).natDegree : ℤ))) := by
  classical
  let x : Fin r → RatFunc.CompletionAtInfty F := fun i =>
    ((a.val i : RatFunc F) : RatFunc.CompletionAtInfty F)
  -- valuation is multiplicative and commutes with inverses:
  calc
    Valued.v ((∏ i : Fin r, x i ^ (𝔰 i : ℕ))⁻¹)
        = (Valued.v (∏ i : Fin r, x i ^ (𝔰 i : ℕ)))⁻¹ := v_inv F _
    _ = ((Finset.univ.prod fun i : Fin r => Valued.v (x i ^ (𝔰 i : ℕ))))⁻¹ := by
          rw [v_prod F (Fin r) Finset.univ]
    _ = ((Finset.univ.prod fun i : Fin r => (Valued.v (x i)) ^ (𝔰 i : ℕ)))⁻¹ := by
          congr 1
          refine Finset.prod_congr rfl ?_
          intro i hi
          exact map_pow (Valued.v) (x i) (𝔰 i : ℕ)
    _ = ((Finset.univ.prod fun i : Fin r => exp (((a.val i).natDegree : ℤ) * (𝔰 i : ℤ))))⁻¹ := by
          congr 1
          refine Finset.prod_congr rfl ?_
          intro i hi
          have hvi : Valued.v (x i) = exp ((a.val i).natDegree : ℤ) := by
            exact v_image_monic F (a.val i) (a.2.2 i)
          rw [hvi]
          rw [← exp_nsmul (n := (𝔰 i : ℕ)) (a := ((a.val i).natDegree : ℤ))]
          congr 1
          ring
    _ = exp (-(∑ i : Fin r, (𝔰 i : ℤ) * ((a.val i).natDegree : ℤ))) := by
          have hprod := exp_sum (Fin r) Finset.univ
            (fun i : Fin r => ((a.val i).natDegree : ℤ) * (𝔰 i : ℤ))
          rw [hprod]
          rw [← exp_neg]
          congr 1
          apply congrArg Neg.neg
          apply Finset.sum_congr rfl
          intro i hi
          ring

/-- Terms of a multiple-zeta sum have valuation `exp (- (weighted degree sum))`; for large
leading degree this is `< exp n`. -/
lemma zeta_term_val_lt {r : ℕ} (hr : 0 < r) (𝔰 : Fin r → ℕ+) {n : ℤ}
    (a : monicStrictAntiNatDegree F r) (hdeg : (-n : ℤ) < ((a.val ⟨0, hr⟩).natDegree : ℤ)) :
    Valued.v ((∏ i : Fin r, ((a.val i : RatFunc F) : RatFunc.CompletionAtInfty F) ^ (𝔰 i : ℕ))⁻¹)
      < exp n := by
  rw [zeta_term_val F 𝔰 a]
  rw [WithZero.exp_lt_exp]
  have hs0 : (1 : ℤ) ≤ (𝔰 ⟨0, hr⟩ : ℤ) := by
    exact_mod_cast (PNat.pos (𝔰 ⟨0, hr⟩))
  have hdeg0 : (0 : ℤ) ≤ ((a.val ⟨0, hr⟩).natDegree : ℤ) := by exact_mod_cast (Nat.zero_le _)
  have hd0 : ((a.val ⟨0, hr⟩).natDegree : ℤ) ≤
      (𝔰 ⟨0, hr⟩ : ℤ) * ((a.val ⟨0, hr⟩).natDegree : ℤ) := by
    nlinarith [mul_le_mul_of_nonneg_right hs0 hdeg0]
  have hnonneg : ∀ j : Fin r, (0 : ℤ) ≤ (𝔰 j : ℤ) * ((a.val j).natDegree : ℤ) := by
    intro j
    have hsj : (0 : ℤ) ≤ (𝔰 j : ℤ) := by exact_mod_cast (Nat.zero_le ((𝔰 j : ℕ)))
    have hdj : (0 : ℤ) ≤ ((a.val j).natDegree : ℤ) := by exact_mod_cast (Nat.zero_le _)
    nlinarith [mul_nonneg hsj hdj]
  have htotal : ((a.val ⟨0, hr⟩).natDegree : ℤ) ≤
      ∑ i : Fin r, (𝔰 i : ℤ) * ((a.val i).natDegree : ℤ) := by
    calc
      ((a.val ⟨0, hr⟩).natDegree : ℤ) ≤
          (𝔰 ⟨0, hr⟩ : ℤ) * ((a.val ⟨0, hr⟩).natDegree : ℤ) := hd0
      _ ≤ ∑ i : Fin r, (𝔰 i : ℤ) * ((a.val i).natDegree : ℤ) := by
        exact Finset.single_le_sum (fun i hi => hnonneg i) (Finset.mem_univ (x := (⟨0, hr⟩ : Fin r)))
  have hlt : (-n : ℤ) < ∑ i : Fin r, (𝔰 i : ℤ) * ((a.val i).natDegree : ℤ) :=
    lt_of_lt_of_le hdeg htotal
  omega

/-- Tuples whose leading polynomial has degree `< N` form a finite set. -/
lemma finite_deg_lt {r : ℕ} (hr : 0 < r) (N : ℕ) :
    Set.Finite {a : monicStrictAntiNatDegree F r | (a.val ⟨0, hr⟩).natDegree < N} := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  haveI hcod : Finite {p : F[X] // p.Monic ∧ p.natDegree ≤ N} := by
    simpa using (Commons.FieldTheory.Polynomial.finite_monic_le F N)
  let S : Set (monicStrictAntiNatDegree F r) :=
    {a | (a.val ⟨0, hr⟩).natDegree < N}
  have hbound : ∀ (a : monicStrictAntiNatDegree F r), a ∈ S →
      ∀ i : Fin r, (a.val i).natDegree < N := by
    intro a ha i
    have hdeg0 : (a.val ⟨0, hr⟩).natDegree < N := by simpa [S] using ha
    by_cases hi0 : (i : ℕ) = 0
    · have hi : i = ⟨0, hr⟩ := Fin.ext (by simpa using hi0)
      rw [hi]
      exact hdeg0
    · have h0i : (⟨0, hr⟩ : Fin r) < i :=
        (Fin.mk_lt_mk).2 (Nat.pos_of_ne_zero hi0)
      exact lt_trans (by simpa using a.2.1 h0i) hdeg0
  let f : S → Fin r → {p : F[X] // p.Monic ∧ p.natDegree ≤ N} := fun a i =>
    ⟨a.val.1 i, a.val.2.2 i, le_of_lt (hbound a.1 a.2 i)⟩
  have hinj : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    funext i
    simpa using congrArg Subtype.val (congrFun h i)
  have hfinS : Finite S := Finite.of_injective f hinj
  exact hfinS


/-- The summands of a multiple-zeta sum tend to zero along the cofinite filter on the index
set of monic tuples. -/
lemma zeta_tendsto_cofinite {r : ℕ} (hr : 0 < r) (𝔰 : Fin r → ℕ+) :
    Tendsto (fun a : monicStrictAntiNatDegree F r =>
      (∏ i : Fin r, ((a.val i : RatFunc F) : RatFunc.CompletionAtInfty F) ^ (𝔰 i : ℕ))⁻¹)
      Filter.cofinite (𝓝 0) := by
  rw [Filter.tendsto_def]
  intro U hU
  have hb := (Commons.Topology.Algebra.Valued.exp_balls_is_basis
    (K := RatFunc.CompletionAtInfty F) U hU)
  rcases hb with ⟨n, hball⟩
  let N : ℕ := Int.toNat (-n + 1)
  have hN : (-n : ℤ) < (N : ℤ) := by
    dsimp [N]
    by_cases h : (0 : ℤ) ≤ -n + 1
    · rw [Int.toNat_of_nonneg h]
      omega
    · rw [Int.toNat_eq_zero.mpr (by omega)]
      omega
  have hC : {a : monicStrictAntiNatDegree F r | N ≤ (a.val ⟨0, hr⟩).natDegree} ∈
      Filter.cofinite := by
    rw [Filter.mem_cofinite]
    have hc : ({a : monicStrictAntiNatDegree F r | N ≤ (a.val ⟨0, hr⟩).natDegree})ᶜ =
        {a | (a.val ⟨0, hr⟩).natDegree < N} := by
      ext a
      simp
    rw [hc]
    exact finite_deg_lt F hr N
  refine Filter.mem_of_superset hC ?_
  intro a ha
  apply hball
  have hdeg : (-n : ℤ) < ((a.val ⟨0, hr⟩).natDegree : ℤ) := by
    exact lt_of_lt_of_le hN (by exact_mod_cast ha)
  exact zeta_term_val_lt F (r := r) hr 𝔰 (n := n) a hdeg

/-- The family in the definition of `ζ_A` (depth `r ≥ 1`) is summable. -/
lemma summable_zeta_term {r : ℕ} (hr : 0 < r) (𝔰 : Fin r → ℕ+) :
    Summable (fun a : monicStrictAntiNatDegree F r =>
      (∏ i : Fin r, ((a.val i : RatFunc F) : RatFunc.CompletionAtInfty F) ^ (𝔰 i : ℕ))⁻¹) := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero]
  exact zeta_tendsto_cofinite F (r := r) hr 𝔰

end ZagierHoffmanPositiveChar
