import Submission.Work.ThomBordism.PontryaginThom.Normal

/-!
# The Hurewicz image of the Pontryagin–Thom class, and rational Hurewicz

Item 2 of the chapter, and the place where `Work.Drive.RationalHurewiczStable` (area STEMS) is used.

Let `α_V ∈ π_{8+k}(T)` be the Pontryagin–Thom class of a closed oriented smooth `8`-manifold `V`
(`PTRep`), and let `h ∈ H_{8+k}(T;ℤ)` be its Hurewicz image (`hurewiczClassOf`).  The pairing of `h`
with `p₁²U` and `p₂U` is the **normal** Pontryagin numbers (`PTRep.hurewicz_p1sq`, `.hurewicz_p2`),
which by the Whitney formula are the *tangent* numbers `p₁²(V)`, `p₁²(V) - p₂(V)`
(`Normal.lean`).  Hence, if `p₁²(V) = 0` and `p₂(V) = 0`, the two pairings vanish; since `p₁²U` and
`p₂U` span `H^{8+k}(T;ℚ)` (`ThomTarget.detects_torsion`), `h` is **torsion**:

* `PTRep.hurewiczClass_torsion`.

Rational Hurewicz in the stable range (`Work.Drive.RationalHurewiczStable`, applied to the
`(k-1)`-connected space `T` in the degree `8+k ≤ 2k-2`) then upgrades this to a torsion *homotopy*
class:

* `exists_pow_eq_one_of_hurewiczClass_torsion`,
* `PTRep.exists_pow_eq_one_of_numbers_zero`.

The transversality chapter (`Transversality`) turns the resulting null-homotopy of a positive
multiple of `α_V` into a null-bordism of a positive multiple of `V`; the assembly is in
`Assembly.lean`.

The family forms (item 3) are proved the same way, the sums of the tangent numbers standing in for
the numbers themselves: `PTFamilyRep.pair1_eq_zero`, `PTFamilyRep.pair2_eq_zero`,
`PTFamilyRep.hurewiczClass_torsion`, `PTFamilyRep.exists_pow_eq_one_of_numbers_zero`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Work.ThomBordism.PontryaginThom

noncomputable section

open Work.Cohomology

variable {V : Man8} {k : ℕ} {D : ThomTarget k}

/-! ## The pairings of the Hurewicz image -/

/-- **The Hurewicz image of the Pontryagin–Thom class pairs trivially with `p₁²U` when the tangent
`p₁²`-number vanishes.** -/
theorem PTRep.pair1_eq_zero (r : PTRep V k D) (h1 : V.p1Sq = 0) :
    D.pair1 (hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀ r.α) = 0 := by
  show kronH ℤ (ssetOf D.T) (k + 8) D.p1sqU _ = 0
  rw [PTRep.α_eq r, r.hurewicz_p1sq, r.normal.normalP1Sq_eq, h1]

/-- **The Hurewicz image of the Pontryagin–Thom class pairs trivially with `p₂U` when the tangent
`p₁²`- and `p₂`-numbers vanish.** -/
theorem PTRep.pair2_eq_zero (r : PTRep V k D) (h1 : V.p1Sq = 0) (h2 : V.p2Num = 0) :
    D.pair2 (hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀ r.α) = 0 := by
  show kronH ℤ (ssetOf D.T) (k + 8) D.p2U _ = 0
  rw [PTRep.α_eq r, r.hurewicz_p2, r.normal.normalP2_eq, h1, h2]
  ring

/-- **The Hurewicz image of the Pontryagin–Thom class is torsion when the Pontryagin numbers
vanish.**

The pairings with `p₁²U` and `p₂U` are the normal numbers, which are the tangent numbers
(`p₁²` and `p₁² - p₂`), so both vanish; as `p₁²U`, `p₂U` span `H^{8+k}(T;ℚ)` (dual basis), the
torsion-free part of `h` is zero. -/
theorem PTRep.hurewiczClass_torsion (r : PTRep V k D) (h1 : V.p1Sq = 0) (h2 : V.p2Num = 0) :
    ∃ N : ℕ, 0 < N ∧
      (N : ℤ) • hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀ r.α = 0 :=
  D.detects_torsion _ (r.pair1_eq_zero h1) (r.pair2_eq_zero h1 h2)

/-- **Item 2, in quotable form**: the Hurewicz pairing of the Pontryagin–Thom class of `V` with
`p₁²U` is the *tangent* `p₁²`-number of `V`. -/
theorem PTRep.pair1_eq (r : PTRep V k D) :
    D.pair1 (hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀ r.α) = V.p1Sq := by
  show kronH ℤ (ssetOf D.T) (k + 8) D.p1sqU _ = V.p1Sq
  rw [PTRep.α_eq r, r.hurewicz_p1sq, r.normal.normalP1Sq_eq]

/-- **Item 2, in quotable form**: the Hurewicz pairing of the Pontryagin–Thom class of `V` with
`p₂U` is `p₁²(V) - p₂(V)`, the second *normal* Pontryagin number expressed in the tangent ones. -/
theorem PTRep.pair2_eq (r : PTRep V k D) :
    D.pair2 (hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀ r.α) = V.p1Sq - V.p2Num := by
  show kronH ℤ (ssetOf D.T) (k + 8) D.p2U _ = V.p1Sq - V.p2Num
  rw [PTRep.α_eq r, r.hurewicz_p2, r.normal.normalP2_eq]

/-! ## Rational Hurewicz in the stable range -/

/-- **Rational Hurewicz in the stable range, for the Thom space.**

`T` is `(k-1)`-connected (`D.connected`) and the degree `8+k` is in the stable range `≤ 2k-2`
(hypothesis `hdeg`), so a homotopy class whose Hurewicz image is torsion is itself torsion.

This is `Work.Drive.RationalHurewiczStable` applied with `i = k + 7`; the degree `(k+7)+1` is
*definitionally* `k+8`, so no transport is needed. -/
theorem exists_pow_eq_one_of_hurewiczClass_torsion (D : ThomTarget k) (hk : 2 ≤ k)
    (hrat : Work.Drive.RationalHurewiczStable) (hdeg : k + 8 ≤ 2 * k - 2)
    (α : HomotopyGroup (Fin (k + 8)) D.T D.t₀)
    (h : ∃ N : ℕ, 0 < N ∧
      (N : ℤ) • hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀ α = 0) :
    ∃ N : ℕ, 0 < N ∧ α ^ N = 1 := by
  obtain ⟨N, hN, htor⟩ := h
  revert htor
  refine Quotient.inductionOn α ?_
  intro p htor
  have hp : (N : ℤ) • Work.Stems.hurewiczChain (k + 8) (one_le_add_eight k) D.t₀ p = 0 := by
    simpa only [hurewiczClassOf_mk] using htor
  exact hrat k hk D.T D.t₀ D.connected (k + 7) (by omega) p ⟨N, hN, hp⟩

/-- **The Pontryagin–Thom class of a manifold with vanishing Pontryagin numbers is torsion.** -/
theorem PTRep.exists_pow_eq_one_of_numbers_zero (r : PTRep V k D) (hk : 2 ≤ k)
    (hrat : Work.Drive.RationalHurewiczStable) (hdeg : k + 8 ≤ 2 * k - 2)
    (h1 : V.p1Sq = 0) (h2 : V.p2Num = 0) :
    ∃ N : ℕ, 0 < N ∧ r.α ^ N = 1 :=
  exists_pow_eq_one_of_hurewiczClass_torsion D hk hrat hdeg r.α
    (r.hurewiczClass_torsion h1 h2)

/-- The Hurewicz pairing of a family's Pontryagin–Thom class with `p₁²U` is the sum of the tangent
`p₁²`-numbers of the pieces (additivity, item 3). -/
theorem PTFamilyRep.pair1_eq {ι : Type} [Fintype ι] {F : ι → Man8}
    (r : PTFamilyRep ι F k D) :
    D.pair1 (hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀ r.α) = ∑ i, (F i).p1Sq := by
  show kronH ℤ (ssetOf D.T) (k + 8) D.p1sqU _ = ∑ i, (F i).p1Sq
  rw [PTFamilyRep.α_eq r, r.hurewicz_p1sq]

/-- The Hurewicz pairing of a family's Pontryagin–Thom class with `p₂U` is the sum of
`p₁² - p₂` over the pieces (additivity, item 3). -/
theorem PTFamilyRep.pair2_eq {ι : Type} [Fintype ι] {F : ι → Man8}
    (r : PTFamilyRep ι F k D) :
    D.pair2 (hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀ r.α)
      = ∑ i, ((F i).p1Sq - (F i).p2Num) := by
  show kronH ℤ (ssetOf D.T) (k + 8) D.p2U _ = ∑ i, ((F i).p1Sq - (F i).p2Num)
  rw [PTFamilyRep.α_eq r, r.hurewicz_p2]

/-! ## Families -/

variable {ι : Type} [Fintype ι] {F : ι → Man8}

/-- **The Hurewicz image of the family's Pontryagin–Thom class pairs trivially with `p₁²U` when the
total `p₁²`-number vanishes.**  (Additivity of the pairing over the family.) -/
theorem PTFamilyRep.pair1_eq_zero (r : PTFamilyRep ι F k D) (h1 : ∑ i, (F i).p1Sq = 0) :
    D.pair1 (hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀ r.α) = 0 := by
  show kronH ℤ (ssetOf D.T) (k + 8) D.p1sqU _ = 0
  rw [PTFamilyRep.α_eq r, r.hurewicz_p1sq, h1]

/-- **The Hurewicz image of the family's Pontryagin–Thom class pairs trivially with `p₂U` when the
total `p₁²`- and `p₂`-numbers vanish.** -/
theorem PTFamilyRep.pair2_eq_zero (r : PTFamilyRep ι F k D)
    (h1 : ∑ i, (F i).p1Sq = 0) (h2 : ∑ i, (F i).p2Num = 0) :
    D.pair2 (hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀ r.α) = 0 := by
  show kronH ℤ (ssetOf D.T) (k + 8) D.p2U _ = 0
  rw [PTFamilyRep.α_eq r, r.hurewicz_p2, Finset.sum_sub_distrib, h1, h2]
  ring

/-- **The Hurewicz image of a family's Pontryagin–Thom class is torsion when the total Pontryagin
numbers vanish.** -/
theorem PTFamilyRep.hurewiczClass_torsion (r : PTFamilyRep ι F k D)
    (h1 : ∑ i, (F i).p1Sq = 0) (h2 : ∑ i, (F i).p2Num = 0) :
    ∃ N : ℕ, 0 < N ∧
      (N : ℤ) • hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀ r.α = 0 :=
  D.detects_torsion _ (r.pair1_eq_zero h1) (r.pair2_eq_zero h1 h2)

/-- **The Pontryagin–Thom class of a family with vanishing total Pontryagin numbers is torsion.** -/
theorem PTFamilyRep.exists_pow_eq_one_of_numbers_zero (r : PTFamilyRep ι F k D) (hk : 2 ≤ k)
    (hrat : Work.Drive.RationalHurewiczStable) (hdeg : k + 8 ≤ 2 * k - 2)
    (h1 : ∑ i, (F i).p1Sq = 0) (h2 : ∑ i, (F i).p2Num = 0) :
    ∃ N : ℕ, 0 < N ∧ r.α ^ N = 1 :=
  exists_pow_eq_one_of_hurewiczClass_torsion D hk hrat hdeg r.α
    (r.hurewiczClass_torsion h1 h2)

/-! ## The same with the weaker contract `Work.Drive.RationalHurewiczStable3`

The project lead's message of 2026-09-24 replaces the drive's hypothesis by the *one-short* variant
`Work.Drive.RationalHurewiczStable3` (range `i + 1 ≤ 2k - 3`), which avoids the genuinely stable
boundary degree; the degree of the Pontryagin–Thom class is `k + 8`, so `k ≥ 11` is what is needed
(`k + 8 ≤ 2k - 3`).  The statements below are the ones to use; the `RationalHurewiczStable` versions
above remain for backward compatibility (and `Work.Drive.rationalHurewiczStable3_of_stable` converts
between the two hypotheses). -/

/-- **The Hurewicz image of the Pontryagin–Thom class is torsion, from
`Work.Drive.RationalHurewiczStable3` and `k ≥ 11`.** -/
theorem exists_pow_eq_one_of_hurewiczClass_torsion_three (D : ThomTarget k) (hk : 11 ≤ k)
    (hrat : Work.Drive.RationalHurewiczStable3)
    (α : HomotopyGroup (Fin (k + 8)) D.T D.t₀)
    (h : ∃ N : ℕ, 0 < N ∧
      (N : ℤ) • hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀ α = 0) :
    ∃ N : ℕ, 0 < N ∧ α ^ N = 1 := by
  obtain ⟨N, hN, htor⟩ := h
  revert htor
  refine Quotient.inductionOn α ?_
  intro p htor
  have hp : (N : ℤ) • Work.Stems.hurewiczChain (k + 8) (one_le_add_eight k) D.t₀ p = 0 := by
    simpa only [hurewiczClassOf_mk] using htor
  exact hrat k (by omega) D.T D.t₀ D.connected (k + 7) (by omega) p ⟨N, hN, hp⟩

/-- **The Pontryagin–Thom class of a manifold with vanishing Pontryagin numbers is torsion**, from
`RationalHurewiczStable3` and `k ≥ 11`. -/
theorem PTRep.exists_pow_eq_one_of_numbers_zero_three (r : PTRep V k D) (hk : 11 ≤ k)
    (hrat : Work.Drive.RationalHurewiczStable3)
    (h1 : V.p1Sq = 0) (h2 : V.p2Num = 0) :
    ∃ N : ℕ, 0 < N ∧ r.α ^ N = 1 :=
  exists_pow_eq_one_of_hurewiczClass_torsion_three D hk hrat r.α
    (r.hurewiczClass_torsion h1 h2)

/-- The family form of the same. -/
theorem PTFamilyRep.exists_pow_eq_one_of_numbers_zero_three (r : PTFamilyRep ι F k D) (hk : 11 ≤ k)
    (hrat : Work.Drive.RationalHurewiczStable3)
    (h1 : ∑ i, (F i).p1Sq = 0) (h2 : ∑ i, (F i).p2Num = 0) :
    ∃ N : ℕ, 0 < N ∧ r.α ^ N = 1 :=
  exists_pow_eq_one_of_hurewiczClass_torsion_three D hk hrat r.α
    (r.hurewiczClass_torsion h1 h2)

end

end Work.ThomBordism.PontryaginThom
