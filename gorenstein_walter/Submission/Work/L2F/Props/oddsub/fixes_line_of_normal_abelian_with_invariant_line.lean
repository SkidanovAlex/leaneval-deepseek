import Mathlib
import Submission.Work.L2F.Props.oddsub.CommonEigenvectorAux
import Submission.Work.L2F.Props.oddsub.isCommonEigenvector_mulVec
import Submission.Work.L2F.Props.oddsub.spans_of_two_common_eigenvectors
import Submission.Work.L2F.Props.oddsub.false_of_stabilized_eigenline
import Submission.Work.L2F.Props.oddsub.isScalar_sq_of_swapping_eigenlines

/-!
# `fixes_line_of_normal_abelian_with_invariant_line`

If `Q ◁ L ≤ SL(2,F)`, `Q ≠ 1`, every element of `L` has odd order, and `Q` has a common
eigenvector `v`, then `L` has a common eigenvector (namely `v`).

Argument.  Pick `x ∈ Q`, `x ≠ 1`.  Its matrix is non-scalar (`not_scalar_coe_of_odd_orderOf`),
so (with `x v = c₀ v`) its `c₀`-eigenspace is exactly the line `F v`, and its eigenvalues are
`c₀` and `t - c₀` where `t = tr x` is the trace.  Every common eigenvector `z` of `Q` is an
eigenvector of `x`, and the characteristic equation
(`sq_sub_trace_mul_add_one_of_eigenvector`) forces its eigenvalue to be `c₀` or `t - c₀`; hence
`z ∈ F v` or `z ∈ F u`, where `u` is any common eigenvector outside `F v`.

For `l ∈ L` the vector `l *ᵥ v` is again a common eigenvector of `Q`
(`isCommonEigenvector_mulVec`).  If it is a multiple of `v` we are done for this `l`.  Otherwise
`l *ᵥ v = c • u` with `c ≠ 0`, and `l *ᵥ u` is a common eigenvector as well:
* if `l *ᵥ u = d • u`, then `u` is a common eigenvector of `l` and dividing by `l` shows that
  `v` is a multiple of `u`, contradicting `u ∉ F v` (`false_of_stabilized_eigenline`);
* if `l *ᵥ u = d • v`, then `l²` acts as the scalar `c * d` on both `v` and `u`, so `l²` is a
  scalar matrix (`isScalar_sq_of_swapping_eigenlines`), contradicting
  `not_scalar_coe_of_odd_orderOf` applied to `l²` (`l² ≠ 1` since `l = 1` would force
  `v = c • u`).
-/

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Props.oddsub

theorem fixes_line_of_normal_abelian_with_invariant_line (F : Type*) [Field F]
    (L Q : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))
    (hQL : Q ≤ L)
    (hQnorm : (Q.subgroupOf L).Normal)
    (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    (hQne : Q ≠ ⊥)
    (hQcop : ∀ x ∈ Q, ¬ ringChar F ∣ orderOf x)
    (hoddL : ∀ l ∈ L, Odd (orderOf l))
    (hv : ∃ v : Fin 2 → F, v ≠ 0 ∧ ∀ x ∈ Q,
        ∃ c : F, Matrix.mulVec ((x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) v = c • v) :
    ∃ v : Fin 2 → F, v ≠ 0 ∧ ∀ l ∈ L,
      ∃ c : F, Matrix.mulVec ((l : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) v = c • v := by
  classical
  obtain ⟨v, hv0, hvev⟩ := hv
  have hvEig : IsCommonEigenvector Q v := ⟨hv0, hvev⟩
  obtain ⟨x, hxQ, hx1⟩ : ∃ x ∈ Q, x ≠ 1 := by
    by_contra h
    push_neg at h
    exact hQne ((Subgroup.eq_bot_iff_forall Q).mpr h)
  have hxodd : Odd (orderOf x) := hoddL x (hQL hxQ)
  by_cases hcase : ∀ z : Fin 2 → F, IsCommonEigenvector Q z → ∃ c : F, z = c • v
  · -- every common eigenvector is a multiple of `v`
    refine ⟨v, hv0, fun l hl => ?_⟩
    exact hcase _ (isCommonEigenvector_mulVec F L Q hQL hQnorm l hl v hvEig)
  · push_neg at hcase
    obtain ⟨u, huEig, huNot⟩ := hcase
    have hu0 : u ≠ 0 := huEig.1
    have huv : u ∉ Submodule.span F ({v} : Set (Fin 2 → F)) := by
      intro hmem
      obtain ⟨c, hc⟩ : ∃ c : F, c • v = u := Submodule.mem_span_singleton.mp hmem
      exact huNot c hc.symm
    have hvnu : v ∉ Submodule.span F ({u} : Set (Fin 2 → F)) :=
      notMem_span_of_notMem_span hv0 hu0 huv
    have hspan := spans_of_two_common_eigenvectors F Q x hxQ hx1 hxodd v u hvEig huEig huv
    refine ⟨v, hv0, fun l hl => ?_⟩
    have hzEig : IsCommonEigenvector Q
        (Matrix.mulVec ((l : Matrix.SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) v) :=
      isCommonEigenvector_mulVec F L Q hQL hQnorm l hl v hvEig
    rcases hspan _ hzEig with ⟨c, hcv⟩ | ⟨c, hcvu⟩
    · exact ⟨c, hcv⟩
    · have hc0 : c ≠ 0 := by
        intro hc
        rw [hc, zero_smul] at hcvu
        exact hzEig.1 hcvu
      have hluEig : IsCommonEigenvector Q
          (Matrix.mulVec ((l : Matrix.SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F) u) :=
        isCommonEigenvector_mulVec F L Q hQL hQnorm l hl u huEig
      have hBA : ((l⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
          * ((l : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
        rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.SpecialLinearGroup.coe_one]
      rcases hspan _ hluEig with ⟨d, hdv⟩ | ⟨d, hdu⟩
      · -- `l` swaps the two eigenlines: then `l * l` is a scalar matrix
        obtain ⟨e, he⟩ := isScalar_sq_of_swapping_eigenlines
          (A := ((l : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
          hv0 huv hcvu hdv
        have hll_scal : ((l * l : Matrix.SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F) = e • (1 : Matrix (Fin 2) (Fin 2) F) := by
          rw [Matrix.SpecialLinearGroup.coe_mul]
          exact he
        have hll_ne : l * l ≠ 1 := by
          intro hll
          have h2 : orderOf l ∣ 2 := by
            rw [orderOf_dvd_iff_pow_eq_one, pow_two]
            exact hll
          have hone : orderOf l = 1 := by
            rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
            · exact h
            · exfalso
              obtain ⟨k, hk⟩ := hoddL l hl
              omega
          have hl1 : l = 1 := orderOf_eq_one_iff.mp hone
          rw [hl1] at hcvu
          simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec] at hcvu
          exact hvnu (Submodule.mem_span_singleton.mpr ⟨c, hcvu.symm⟩)
        have hoddll : Odd (orderOf (l * l)) := by
          have hpow : l * l = l ^ 2 := (pow_two l).symm
          rw [hpow]
          exact Odd.of_dvd_nat (hoddL l hl) (orderOf_pow_dvd 2)
        exact absurd hll_scal (not_scalar_coe_of_odd_orderOf (l * l) hll_ne hoddll e)
      · -- `l` stabilizes the line `F u`: impossible
        exact False.elim (false_of_stabilized_eigenline hBA hv0 hu0 huv hcvu hdu)

end Work.L2F.Props.oddsub
