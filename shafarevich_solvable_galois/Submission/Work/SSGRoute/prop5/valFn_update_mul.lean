import Mathlib
import Submission.Work.SSGRoute.prop5.Basic
import Submission.Work.SSGRoute.prop5.commWord_update_mul_mem
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.prop5

open scoped commutatorElement
open Work.CohomologicalShrinking

/-! ## Additivity of the value map `valFn` in a single slot

Schmidt–Wingberg's value map `valFn p G i j d` sends a `j`-tuple of elements of the free
`G`-operator group `F(d)` to the class of `(⁅x₀, ⋯, x_{j-1}⁆)^{p^{i-j}}` in the graded piece
`E(d,(i,j)) = F(d)_{(i,j)}/F(d)_{(i,j)+1}`.  The graded pieces of the refined `p`-central
filtration are elementary abelian `p`-groups, and the whole point of the refinement is that
this map is a homomorphism in each variable separately — that is the content of
Schmidt–Wingberg's Lemma 4, and it is what makes `Prop5Data` a chain complex.

The two ingredients are:

* `commWord_update_mul_mem` (already in the workspace): the commutator word is multiplicative
  in one slot modulo `γ_j`;
* the `p`-power estimates encoded in `pow_mem_pSeries`: a `p^e`-th power of a word of weight
  `j` lies in `P_{j+e}`.
-/

/-- Abstract quotient criterion: if `c * (a*b)⁻¹ ∈ K ≤ H` and `a, b, c ∈ H`, then the classes
of `c` and of `a*b` in `H ⧸ K` coincide. -/
lemma mk'_subgroupOf_mul_eq {P : Type*} [Group P] {H K : Subgroup P} [K.Normal]
    {a b c : P} (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H) (hmem : c * (a * b)⁻¹ ∈ K) :
    (QuotientGroup.mk' (K.subgroupOf H)) ⟨c, hc⟩ =
      (QuotientGroup.mk' (K.subgroupOf H)) ⟨a, ha⟩ *
        (QuotientGroup.mk' (K.subgroupOf H)) ⟨b, hb⟩ := by
  have hd : (⟨c, hc⟩ : H) / ((⟨a, ha⟩ : H) * ⟨b, hb⟩) ∈ K.subgroupOf H := by
    rw [Subgroup.mem_subgroupOf, div_eq_mul_inv]
    simpa using hmem
  rw [← map_mul]
  change (QuotientGroup.mk (⟨c, hc⟩ : H) : H ⧸ K.subgroupOf H)
      = QuotientGroup.mk ((⟨a, ha⟩ : H) * ⟨b, hb⟩)
  rw [QuotientGroup.eq_iff_div_mem]
  exact hd

/-- The value map `valFn`, unfolded: the class of `(commWord j x)^{p^{i-j}}` in the graded
piece, with the explicit membership witness. -/
lemma valFn_apply (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] (i j d : ℕ)
    (hj : 1 ≤ j) (hji : j ≤ i)
    (x : Fin j → Work.Shrinking.freeOperatorGroup G d) :
    valFn p G i j d hj hji x =
      Additive.ofMul ((QuotientGroup.mk'
        ((refinedTerm p (Work.Shrinking.freeOperatorGroup G d)
            (tauSucc i j).1 (tauSucc i j).2).subgroupOf
          (refinedTerm p (Work.Shrinking.freeOperatorGroup G d) i j)))
        ⟨(commWord j x) ^ (p ^ (i - j)),
          commWord_pow_mem_refinedTerm p G i j d hj hji x⟩) := rfl

/-- **The group-theoretic core of the additivity of `valFn`.**  For an arbitrary group `P`, the
`p^{i-j}`-th powers of the commutator words with one slot replaced by `a*b` and by `a`, `b`
agree modulo the successor term `P_{(i,j)+1}` of the refined `p`-central filtration.

Both `a, b` and the three commutator words live in the lower central series `γ_{j-1}`, whose
image modulo `γ_j` is central; hence `commWord j (update x k (a*b))^{p^{i-j}}` and
`commWord j (update x k a)^{p^{i-j}} * commWord j (update x k b)^{p^{i-j}}` have the same image
modulo `γ_j`, while both lie in `P_i` by the `p`-power estimates.  The two cases `j < i` and
`j = i` differ only in the shape of `τ + 1`. -/
theorem commWord_update_pow_sub_mem (p : ℕ) {P : Type*} [Group P] (i j : ℕ)
    (hj : 1 ≤ j) (hji : j ≤ i) (x : Fin j → P) (k : Fin j) (a b : P) :
    commWord j (Function.update x k (a * b)) ^ p ^ (i - j) *
        (commWord j (Function.update x k a) ^ p ^ (i - j) *
         commWord j (Function.update x k b) ^ p ^ (i - j))⁻¹
      ∈ refinedTerm p P (tauSucc i j).1 (tauSucc i j).2 := by
  rcases lt_or_eq_of_le hji with hlt | heq
  · -- `j < i`: the successor is `(i, j+1)`.
    have hidx : j + (i - j) - 1 = i - 1 := by omega
    have hRps : commWord j (Function.update x k (a * b)) ^ p ^ (i - j) *
        (commWord j (Function.update x k a) ^ p ^ (i - j) *
         commWord j (Function.update x k b) ^ p ^ (i - j))⁻¹ ∈ pSeries p P i := by
      have h1 := pow_mem_pSeries p j (i - j) hj (commWord j (Function.update x k (a * b)))
        (commWord_mem_lowerCentralSeries j (Function.update x k (a * b)))
      have h2 := pow_mem_pSeries p j (i - j) hj (commWord j (Function.update x k a))
        (commWord_mem_lowerCentralSeries j (Function.update x k a))
      have h3 := pow_mem_pSeries p j (i - j) hj (commWord j (Function.update x k b))
        (commWord_mem_lowerCentralSeries j (Function.update x k b))
      rw [hidx] at h1 h2 h3
      exact mul_mem h1 (inv_mem (mul_mem h2 h3))
    have hRg : commWord j (Function.update x k (a * b)) ^ p ^ (i - j) *
        (commWord j (Function.update x k a) ^ p ^ (i - j) *
         commWord j (Function.update x k b) ^ p ^ (i - j))⁻¹
        ∈ centralSeries P (j + 1) := by
      show _ ∈ (⊤ : Subgroup P).lowerCentralSeries j
      have hη : commWord j (Function.update x k (a * b)) *
          (commWord j (Function.update x k a) * commWord j (Function.update x k b))⁻¹
          ∈ (⊤ : Subgroup P).lowerCentralSeries j := commWord_update_mul_mem j hj x k a b
      have hwu : commWord j (Function.update x k a) ∈
          (⊤ : Subgroup P).lowerCentralSeries (j - 1) :=
        commWord_mem_lowerCentralSeries j _
      have hwv : commWord j (Function.update x k b) ∈
          (⊤ : Subgroup P).lowerCentralSeries (j - 1) :=
        commWord_mem_lowerCentralSeries j _
      have hmemN : ⁅commWord j (Function.update x k a), commWord j (Function.update x k b)⁆
          ∈ (⊤ : Subgroup P).lowerCentralSeries j := by
        have hsucc : (⊤ : Subgroup P).lowerCentralSeries j
            = ⁅(⊤ : Subgroup P).lowerCentralSeries (j - 1), (⊤ : Subgroup P)⁆ := by
          conv_lhs => rw [show j = (j - 1) + 1 from by omega]
          rw [Subgroup.lowerCentralSeries_succ]
        rw [hsucc]
        exact Subgroup.commutator_mem_commutator hwu (Subgroup.mem_top _)
      have hcomm1 : ⁅(QuotientGroup.mk' ((⊤ : Subgroup P).lowerCentralSeries j))
              (commWord j (Function.update x k a)),
            (QuotientGroup.mk' ((⊤ : Subgroup P).lowerCentralSeries j))
              (commWord j (Function.update x k b))⁆ = 1 := by
        rw [← map_commutatorElement (QuotientGroup.mk' ((⊤ : Subgroup P).lowerCentralSeries j)),
          QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hmemN
      have hcomm : Commute
          ((QuotientGroup.mk' ((⊤ : Subgroup P).lowerCentralSeries j))
            (commWord j (Function.update x k a)))
          ((QuotientGroup.mk' ((⊤ : Subgroup P).lowerCentralSeries j))
            (commWord j (Function.update x k b))) :=
        commutatorElement_eq_one_iff_commute.mp hcomm1
      have hπwuv : (QuotientGroup.mk' ((⊤ : Subgroup P).lowerCentralSeries j))
            (commWord j (Function.update x k (a * b)))
          = (QuotientGroup.mk' ((⊤ : Subgroup P).lowerCentralSeries j))
              (commWord j (Function.update x k a)) *
            (QuotientGroup.mk' ((⊤ : Subgroup P).lowerCentralSeries j))
              (commWord j (Function.update x k b)) := by
        have heq : commWord j (Function.update x k (a * b)) =
            (commWord j (Function.update x k (a * b)) *
                (commWord j (Function.update x k a) *
                 commWord j (Function.update x k b))⁻¹) *
              (commWord j (Function.update x k a) * commWord j (Function.update x k b)) := by
          group
        have hη1 : (QuotientGroup.mk' ((⊤ : Subgroup P).lowerCentralSeries j))
            (commWord j (Function.update x k (a * b)) *
              (commWord j (Function.update x k a) *
               commWord j (Function.update x k b))⁻¹) = 1 := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact hη
        rw [heq, map_mul, hη1, one_mul, map_mul]
      have hπR : (QuotientGroup.mk' ((⊤ : Subgroup P).lowerCentralSeries j))
          (commWord j (Function.update x k (a * b)) ^ p ^ (i - j) *
            (commWord j (Function.update x k a) ^ p ^ (i - j) *
             commWord j (Function.update x k b) ^ p ^ (i - j))⁻¹) = 1 := by
        rw [map_mul, map_inv, map_mul, map_pow, map_pow, map_pow, hπwuv, hcomm.mul_pow]
        group
      rw [← QuotientGroup.eq_one_iff]
      simpa using hπR
    have hgoal : refinedTerm p P (tauSucc i j).1 (tauSucc i j).2
        = (pSeries p P i ⊓ centralSeries P (j + 1)) ⊔ pSeries p P (i + 1) := by
      rw [tauSucc_of_lt hlt, refinedTerm]
    rw [hgoal]
    exact Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hRps, hRg⟩)
  · -- `j = i`: the successor is `(i+1, 1)`, and the exponent is `p^0 = 1`.
    subst heq
    have hη : commWord j (Function.update x k (a * b)) *
        (commWord j (Function.update x k a) * commWord j (Function.update x k b))⁻¹
        ∈ (⊤ : Subgroup P).lowerCentralSeries j := commWord_update_mul_mem j hj x k a b
    have hmem : commWord j (Function.update x k (a * b)) ^ p ^ (j - j) *
        (commWord j (Function.update x k a) ^ p ^ (j - j) *
         commWord j (Function.update x k b) ^ p ^ (j - j))⁻¹ ∈ pSeries p P (j + 1) := by
      simp only [tsub_self, pow_zero, pow_one]
      exact (Work.ProP.lowerCentralSeries_le_pCentralSeries p P j) hη
    have hgoal : refinedTerm p P (tauSucc j j).1 (tauSucc j j).2 = pSeries p P (j + 1) := by
      rw [tauSucc_of_le (le_refl j), refinedTerm_one]
    rw [hgoal]
    exact hmem

theorem valFn_update_mul (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] (i j d : ℕ)
    (hj : 1 ≤ j) (hji : j ≤ i)
    (x : Fin j → Work.Shrinking.freeOperatorGroup G d) (k : Fin j)
    (a b : Work.Shrinking.freeOperatorGroup G d) :
    valFn p G i j d hj hji (Function.update x k (a * b))
      = valFn p G i j d hj hji (Function.update x k a)
        + valFn p G i j d hj hji (Function.update x k b) := by
  rw [valFn_apply, valFn_apply, valFn_apply]
  apply Additive.ofMul.injective
  exact mk'_subgroupOf_mul_eq
    (commWord_pow_mem_refinedTerm p G i j d hj hji (Function.update x k a))
    (commWord_pow_mem_refinedTerm p G i j d hj hji (Function.update x k b))
    (commWord_pow_mem_refinedTerm p G i j d hj hji (Function.update x k (a * b)))
    (commWord_update_pow_sub_mem p i j hj hji x k a b)

end Work.SSGRoute.prop5
