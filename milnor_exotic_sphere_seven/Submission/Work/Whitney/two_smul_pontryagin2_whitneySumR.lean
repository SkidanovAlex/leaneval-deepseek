import Mathlib
import Submission.Work.Whitney.Basic
import Submission.Work.Whitney.Cup
import Submission.Work.Whitney.ChernProduct
import Submission.Work.Whitney.chernProductSum_eq_fin
import Submission.Work.Whitney.conjComplexification
import Submission.Work.Whitney.pontryagin1_line
import Submission.Work.Whitney.pontryagin1_whitneySum_line
import Submission.Work.Whitney.complexificationCore_whitneySumR
import Submission.Work.Thom.manifoldP1

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The additivity of `p₂` for real bundles, modulo `2`-torsion

The Whitney sum formula for the Pontryagin classes is

  `p₂(E ⊕ F) = p₂(E) + p₁(E) ⌣ p₁(F) + p₂(F)`

only modulo `2`-torsion: the integral identity carries the correction terms
`c₁(E_ℂ) ⌣ c₃(F_ℂ) + c₃(E_ℂ) ⌣ c₁(F_ℂ)`, which vanish after multiplication by `2` because all
odd Chern classes of a complexified real bundle are `2`-torsion
(`Work.Whitney.chernClass_complexification_add_self`, ADDENDUM W3 of the WHITNEY README).

This module proves the sharp statement

  `2 • p₂(E ⊕ F) = 2 • (p₂(E) + p₁(E) ⌣ p₁(F) + p₂(F))`.

With the normalisations of this workspace (`Work.Thom.pontryagin1 Z = -c₂(Z ⊗_ℝ ℂ)` and
`Work.Thom.pontryaginClass i Z = (-1)^i c_{2i}(Z ⊗_ℝ ℂ)`, so that `p₂` *is* `c₄` of the
complexification), the whole content is the degree-`4` expansion of the right-hand side
`Work.Whitney.chernProductSum` of the Whitney formula for the pair of complexified bundles, the
`2`-torsion of the two `(1,3)`/`(3,1)` cross terms and the two unit laws `c₀ ⌣ x = x`, `x ⌣ c₀ = x`.

The degree-`4` Whitney formula `c₄(E ⊕ F) = Σ_{i+j=4} c_i(E) ⌣ c_j(F)` is the hypothesis `hW4`
(the ranks `(i, 4-i)` are available for all complex bundles in the workspace; only the
*intermediate* degrees of the general formula are the known gap, and degree `4` is the hypothesis
the caller supplies).

## Main results

* `Work.Whitney.chernProductSum_four_eq` — the five-term expansion of the right-hand side in
  degree `4`;
* `Work.Whitney.two_smul_chernProductSum_four_complexification` — that expansion after
  multiplication by `2` for a pair of complexified real bundles;
* `Work.Whitney.two_smul_pontryagin2_whitneySumR` — the target.
-/

namespace Work.Whitney

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B]

/-! ## The degree cast along an equality of equal degrees

`Work.Thom.cohTransport` is defined by `eqToIso`, so it depends on its proof argument only through
the *type* of that argument; in particular, transporting along a proof of `n = n` (with the two
sides definitionally equal, e.g. equal numerals) is the identity. -/

theorem cohTransport_eq_self {n : ℕ} (h : n = n) (x : Coh ℤ n B) :
    cohTransport h x = x := by
  rw [Subsingleton.elim h rfl, cohTransport_rfl]

/-! ## The right unit law of the graded product, with the degree bookkeeping

The mirror image of `Work.LerayHirsch.cohTransport_cupChern_one_left`: `x ⌣ 1 = x`, up to the
degree cast `2*(b+0) = 2*b`. -/

theorem cohTransport_cupChern_one_right (b : ℕ) (y : Coh ℤ (2 * b) B) :
    cohTransport (by omega : 2 * (b + 0) = 2 * b)
        (cupChern b 0 y
          (cohTransport (by rfl : 2 * 0 = 0) (Work.Cohomology.oneH ℤ (ssB B)))) = y := by
  rw [cupChern_one_right]
  exact (Work.LerayHirsch.cohTransport_congr_proof _ (rfl : 2 * b = 2 * b)).trans
    (cohTransport_rfl y)

/-! ## The graded product is odd in its first argument -/

theorem cupChern_neg_left (a b : ℕ) (x : Coh ℤ (2 * a) B) (y : Coh ℤ (2 * b) B) :
    cupChern a b (-x) y = - cupChern a b x y := by
  have h := cupChern_add_left a b x (-x) y
  rw [add_neg_cancel, cupChern_zero_left] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

/-! ## The degree-`4` expansion of the right-hand side of the Whitney formula -/

/-- **The degree-`4` expansion of `Work.Whitney.chernProductSum`**: the sum
`Σ_{i+j=4} c_i(Z₁) ⌣ c_j(Z₂)` written out, one term for each of the five pairs `(0,4)`, `(1,3)`,
`(2,2)`, `(3,1)`, `(4,0)`. -/
theorem chernProductSum_four_eq {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] {m₁ m₂ : ℕ}
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂) :
    chernProductSum Z₁ Z₂ 4
      = cupChern 0 4 (chernClass m₁ 0 Z₁) (chernClass m₂ 4 Z₂)
      + cupChern 1 3 (chernClass m₁ 1 Z₁) (chernClass m₂ 3 Z₂)
      + cupChern 2 2 (chernClass m₁ 2 Z₁) (chernClass m₂ 2 Z₂)
      + cupChern 3 1 (chernClass m₁ 3 Z₁) (chernClass m₂ 1 Z₂)
      + cupChern 4 0 (chernClass m₁ 4 Z₁) (chernClass m₂ 0 Z₂) := by
  simp only [chernProductSum, chernSummand_def, cupChern_def, Finset.sum_range_succ,
    Finset.sum_range_zero, cohTransport_rfl, Nat.sub_zero,
    dif_pos (by norm_num : (0 : ℕ) ≤ 4), dif_pos (by norm_num : (1 : ℕ) ≤ 4),
    dif_pos (by norm_num : (2 : ℕ) ≤ 4), dif_pos (by norm_num : (3 : ℕ) ≤ 4),
    dif_pos (by norm_num : (4 : ℕ) ≤ 4), zero_add]

/-! ## The degree-`4` Whitney formula modulo `2`-torsion, for complexified real bundles -/

/-- **The right-hand side of the degree-`4` Whitney formula for a pair of complexified real
bundles, modulo `2`-torsion**: the `(0,4)` and `(4,0)` terms collapse to `c₄` of the factors (the
unit laws and `c₀ = 1`), the `(1,3)` and `(3,1)` cross terms die after multiplication by `2`
(odd Chern classes of a complexification are `2`-torsion and the product is bilinear), and the
`(2,2)` term survives unchanged. -/
theorem two_smul_chernProductSum_four_complexification {k l : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁]
    [Fintype ι₂] (E : VectorBundleCore ℝ B (EuclideanSpace ℝ (Fin k)) ι₁)
    (F : VectorBundleCore ℝ B (EuclideanSpace ℝ (Fin l)) ι₂) :
    (2 : ℤ) • chernProductSum (complexificationCore E) (complexificationCore F) 4
      = (2 : ℤ) • (chernClass k 4 (complexificationCore E)
          + cupChern 2 2 (chernClass k 2 (complexificationCore E))
              (chernClass l 2 (complexificationCore F))
          + chernClass l 4 (complexificationCore F)) := by
  rw [chernProductSum_four_eq]
  -- The `(0,4)` term: `c₀ ⌣ c₄ = c₄`.
  have h0 : cupChern 0 4 (chernClass k 0 (complexificationCore E))
        (chernClass l 4 (complexificationCore F)) = chernClass l 4 (complexificationCore F) := by
    have hmid : cupChern 0 4 (chernClass k 0 (complexificationCore E))
          (chernClass l 4 (complexificationCore F))
        = cupChern 0 4 (Work.Cohomology.oneH ℤ (ssB B))
          (chernClass l 4 (complexificationCore F)) :=
      congrArg (fun x => cupChern 0 4 x (chernClass l 4 (complexificationCore F)))
        (chernClass_zero_eq_oneH (complexificationCore E))
    have hleft := Work.LerayHirsch.cohTransport_cupChern_one_left (B := B) 4
      (chernClass l 4 (complexificationCore F))
    exact ((cohTransport_eq_self (by omega : 2 * (0 + 4) = 2 * (0 + 4)) _).symm).trans
      ((congrArg (cohTransport (by omega : 2 * (0 + 4) = 2 * 4)) hmid).trans hleft)
  -- The `(4,0)` term: `c₄ ⌣ c₀ = c₄`.
  have h4 : cupChern 4 0 (chernClass k 4 (complexificationCore E))
        (chernClass l 0 (complexificationCore F)) = chernClass k 4 (complexificationCore E) := by
    have hz : chernClass l 0 (complexificationCore F)
        = cohTransport (by rfl : 2 * 0 = 0) (Work.Cohomology.oneH ℤ (ssB B)) :=
      (chernClass_zero_eq_oneH (complexificationCore F)).trans (cohTransport_rfl _).symm
    have hmid : cupChern 4 0 (chernClass k 4 (complexificationCore E))
          (chernClass l 0 (complexificationCore F))
        = cupChern 4 0 (chernClass k 4 (complexificationCore E))
          (cohTransport (by rfl : 2 * 0 = 0) (Work.Cohomology.oneH ℤ (ssB B))) :=
      congrArg (fun x => cupChern 4 0 (chernClass k 4 (complexificationCore E)) x) hz
    have hright := cohTransport_cupChern_one_right (B := B) 4
      (chernClass k 4 (complexificationCore E))
    exact ((cohTransport_eq_self (by omega : 2 * (4 + 0) = 2 * (4 + 0)) _).symm).trans
      ((congrArg (cohTransport (by omega : 2 * (4 + 0) = 2 * 4)) hmid).trans hright)
  -- The `(1,3)` cross term is `2`-torsion.
  have h1 : (2 : ℤ) • cupChern 1 3 (chernClass k 1 (complexificationCore E))
        (chernClass l 3 (complexificationCore F)) = 0 := by
    have hx : chernClass k 1 (complexificationCore E)
        + chernClass k 1 (complexificationCore E) = 0 :=
      chernClass_complexification_add_self (B := B) (k := k) (j := 1) (by decide) E
    rw [show (2 : ℤ) • cupChern 1 3 (chernClass k 1 (complexificationCore E))
          (chernClass l 3 (complexificationCore F))
        = cupChern 1 3 (chernClass k 1 (complexificationCore E)
              + chernClass k 1 (complexificationCore E))
            (chernClass l 3 (complexificationCore F)) from by
      rw [cupChern_add_left]
      exact two_zsmul _]
    rw [hx, cupChern_zero_left]
  -- The `(3,1)` cross term is `2`-torsion.
  have h3 : (2 : ℤ) • cupChern 3 1 (chernClass k 3 (complexificationCore E))
        (chernClass l 1 (complexificationCore F)) = 0 := by
    have hx : chernClass k 3 (complexificationCore E)
        + chernClass k 3 (complexificationCore E) = 0 :=
      chernClass_complexification_add_self (B := B) (k := k) (j := 3) (by decide) E
    rw [show (2 : ℤ) • cupChern 3 1 (chernClass k 3 (complexificationCore E))
          (chernClass l 1 (complexificationCore F))
        = cupChern 3 1 (chernClass k 3 (complexificationCore E)
              + chernClass k 3 (complexificationCore E))
            (chernClass l 1 (complexificationCore F)) from by
      rw [cupChern_add_left]
      exact two_zsmul _]
    rw [hx, cupChern_zero_left]
  -- Distribute the scalar and compare the two groupings additively.
  conv_lhs => rw [zsmul_add, zsmul_add, zsmul_add, zsmul_add]
  rw [h0, h1, h3, h4]
  conv_rhs => rw [zsmul_add, zsmul_add]
  simp only [two_zsmul]
  abel

/-! ## `p₂` is `c₄` of the complexification -/

/-- **The second Pontryagin class is the fourth Chern class of the complexification**:
`Work.Thom.pontryaginClass 2 Z = (-1)^2 c₄(Z ⊗_ℝ ℂ) = c₄(Z ⊗_ℝ ℂ)`, with the degree cast
`2*(2*2) = 4*2` collapsed. -/
theorem pontryaginClass_two_eq {k : ℕ} {ι : Type} [Fintype ι]
    (Z : VectorBundleCore ℝ B (EuclideanSpace ℝ (Fin k)) ι) :
    pontryaginClass 2 Z = chernClass k 4 (complexificationCore Z) := by
  unfold pontryaginClass
  rw [show ((-1 : ℤ) ^ 2) = 1 by norm_num, one_smul]
  exact cohTransport_eq_self _ _

/-! ## The target -/

theorem two_smul_pontryagin2_whitneySumR
    (hW4 : ∀ {B' : Type} [TopologicalSpace B'] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
      {m n : ℕ} (Z₁ : VectorBundleCore ℂ B' (EuclideanSpace ℂ (Fin m)) ι₁)
      (Z₂ : VectorBundleCore ℂ B' (EuclideanSpace ℂ (Fin n)) ι₂),
      Work.Thom.chernClass (m + n) 4 (Work.Whitney.whitneySum Z₁ Z₂)
        = Work.Whitney.chernProductSum Z₁ Z₂ 4)
    {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    {k l : ℕ} (E : VectorBundleCore ℝ B (EuclideanSpace ℝ (Fin k)) ι₁)
    (F : VectorBundleCore ℝ B (EuclideanSpace ℝ (Fin l)) ι₂) :
    (2 : ℤ) • Work.Thom.pontryaginClass 2 (Work.Whitney.whitneySumR E F)
      = (2 : ℤ) • (Work.Thom.pontryaginClass 2 E
          + Work.Whitney.cupChern 2 2 (Work.Thom.pontryagin1 E) (Work.Thom.pontryagin1 F)
          + Work.Thom.pontryaginClass 2 F) := by
  -- `p₂(E ⊕ F) = c₄((E ⊕ F) ⊗_ℝ ℂ) = c₄(E_ℂ ⊕ F_ℂ)`, then the degree-`4` Whitney formula.
  rw [pontryaginClass_two_eq (whitneySumR E F), complexificationCore_whitneySumR E F,
    hW4 (complexificationCore E) (complexificationCore F)]
  -- the right-hand side of the Whitney formula, modulo `2`-torsion.
  rw [two_smul_chernProductSum_four_complexification E F]
  -- the surviving middle terms agree: `c₂(E_ℂ) = -p₁(E)`.
  have hB : cupChern 2 2 (chernClass k 2 (complexificationCore E))
        (chernClass l 2 (complexificationCore F))
      = cupChern 2 2 (pontryagin1 E) (pontryagin1 F) := by
    rw [pontryagin1_def E, pontryagin1_def F, cupChern_neg_left, cupChern_neg_right, neg_neg]
  -- and the outer terms agree: `p₂ = c₄` of the complexification.
  have hmain : chernClass k 4 (complexificationCore E)
        + cupChern 2 2 (chernClass k 2 (complexificationCore E))
            (chernClass l 2 (complexificationCore F))
        + chernClass l 4 (complexificationCore F)
      = pontryaginClass 2 E + cupChern 2 2 (pontryagin1 E) (pontryagin1 F)
        + pontryaginClass 2 F := by
    rw [hB, ← pontryaginClass_two_eq E, ← pontryaginClass_two_eq F]
  rw [hmain]

end

end Work.Whitney
