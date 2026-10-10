import Mathlib
import Submission.Work.MotC5N3.ASZResVecDefs
import Submission.Work.MotV5.Contrib.AsResDefsA
import Submission.Work.MotC5N3.ASZhk_notMem
import Submission.Work.MotV5.Contrib.asZResRecoverySelfA
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotC5N3.ASZResVecAdjoin`

The residual chart coordinates `X i = Z (i+1) / Z 0` of the linear projection `phiAS`, restricted to
the class-`3g` twisted Klein curve `C_{3g}`, generate the twist field `twistFieldAS D (3 * g)` over
`K`; and the normalising coordinate `Z 0 = aszZ D (3 * g) 0` does not vanish on `C_{3g}`.

The mathematical content is the recovery package of `Work.MotAS.ASResidualGen` (proved there over
the base field `RatFunc 𝕜`), ported here to an arbitrary `𝕜`-algebra field `K`:

* `aszZ_three_mul_zero_ne_zero` — the direct nonvanishing computation for `Z 0`;
* `asResidualGenA_from` — the recovery identities (`Work.MotV5.Contrib.asZResRecoverySelfA`)
  give `twistFieldAS D g ≤ K(X₀, X₁, X₂)`, whence equality;
* `adjoin_subtype_eq_top_iff` — the formally trivial, but API-relevant, transfer of the ambient
  equality `adjoin K (range X) = twistFieldAS` to the subtype statement
  `adjoin K (range (aszResVec D g)) = ⊤` required by the statement of `ASZResVecAdjoin`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.MotC5N3

open Work.MotAS (phiAS)
open Work.MotV5.Contrib

variable {𝕜 : Type} [Field 𝕜] {K : Type} [Field K] [Algebra 𝕜 K] [CharP K 5]

/-- **Subtype transfer of a generating statement.**  For an intermediate field `F` of `L/k` and a
set `S ⊆ F`, the `k`-adjoin of `S` inside `↥F` is everything exactly when the `k`-adjoin of the
image of `S` in `L` is `F`.  (Elementary: `map`/`comap` along the inclusion, plus
`IntermediateField.adjoin_map`.) -/
theorem adjoin_subtype_eq_top_iff {k₀ : Type*} [Field k₀] {L₀ : Type*} [Field L₀] [Algebra k₀ L₀]
    (F : IntermediateField k₀ L₀) (S : Set ↥F) :
    IntermediateField.adjoin k₀ S = ⊤ ↔ IntermediateField.adjoin k₀ ((↑) '' S) = F := by
  have hmap : (IntermediateField.adjoin k₀ S).map (IntermediateField.val F)
      = IntermediateField.adjoin k₀ ((↑) '' S) := by
    rw [IntermediateField.adjoin_map]
    rfl
  have htop : (⊤ : IntermediateField k₀ ↥F).map (IntermediateField.val F) = F := by
    ext x
    rw [IntermediateField.mem_map]
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, trivial, rfl⟩
  constructor
  · intro h
    rw [← hmap, h, htop]
  · intro h
    refine IntermediateField.map_injective (IntermediateField.val F) ?_
    rw [hmap, h, htop]

/-! ## §1 The two descriptions of the residual coordinates

`Work.MotC5N3.aszZ` (the residual coordinates of `ASZResVecDefs.lean`) and
`Work.MotV5.Contrib.asZOmA` (the residual coordinates of the generic port) are the *same*
definition, written twice; `rfl` transfers between them. -/

/-- The two definitions of the residual coordinates agree definitionally. -/
theorem aszZ_eq_asZOmA (D : Work.MotV.KleinData 𝕜) (g : K) (k : Fin 5) :
    aszZ D g k = asZOmA D g k := rfl

/-- The range of `aszResVec D g` (in the twist field), viewed in `OmA K D`, is the range of the
residual chart coordinates `Z (i+1) / Z 0`. -/
theorem coe_image_range_aszResVec (D : Work.MotV.KleinData 𝕜) (g : K) :
    ((↑) : ↥(twistFieldAS D (3 * g)) → OmA K D) '' Set.range (aszResVec D g)
      = Set.range (fun i : Fin 3 =>
          aszZ D (3 * g) (⟨i.1 + 1, by omega⟩ : Fin 5) / aszZ D (3 * g) 0) := by
  ext x
  constructor
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨aszResVec D g i, ⟨i, rfl⟩, rfl⟩

/-! ## §2 Membership of the residual quadrics in an intermediate field -/

/-- `kleinPAS1` evaluated at elements of an intermediate field lies in it (generic port of
`Work.MotAS.kleinPAS1_mem`). -/
theorem kleinPAS1_mem_A (D : Work.MotV.KleinData 𝕜) (g : K)
    (F : IntermediateField K (OmA K D)) (ha : asZaA D g ∈ F) (hb : asZbA D g ∈ F)
    (hc : asZcA D g ∈ F) (hw : ∀ j : Fin 5, asZwA D g j ∈ F) :
    Work.MotAS.kleinPAS1 (asZaA D g) (asZbA D g) (asZcA D g) (asZwA D g) ∈ F := by
  let a' : ↥F := ⟨asZaA D g, ha⟩
  let b' : ↥F := ⟨asZbA D g, hb⟩
  let c' : ↥F := ⟨asZcA D g, hc⟩
  let y' : Fin 5 → ↥F := fun j => ⟨asZwA D g j, hw j⟩
  have h : ((Work.MotAS.kleinPAS1 a' b' c' y' : ↥F) : OmA K D)
      = Work.MotAS.kleinPAS1 (asZaA D g) (asZbA D g) (asZcA D g) (asZwA D g) := by
    simp only [Work.MotAS.kleinPAS1]
    push_cast
    rfl
  rw [← h]
  exact (Work.MotAS.kleinPAS1 a' b' c' y').2

/-- `kleinPAS3` evaluated at elements of an intermediate field lies in it (generic port of
`Work.MotAS.kleinPAS3_mem`). -/
theorem kleinPAS3_mem_A (D : Work.MotV.KleinData 𝕜) (g : K)
    (F : IntermediateField K (OmA K D)) (ha : asZaA D g ∈ F) (hb : asZbA D g ∈ F)
    (hc : asZcA D g ∈ F) (hw : ∀ j : Fin 5, asZwA D g j ∈ F) :
    Work.MotAS.kleinPAS3 (asZaA D g) (asZbA D g) (asZcA D g) (asZwA D g) ∈ F := by
  let a' : ↥F := ⟨asZaA D g, ha⟩
  let b' : ↥F := ⟨asZbA D g, hb⟩
  let c' : ↥F := ⟨asZcA D g, hc⟩
  let y' : Fin 5 → ↥F := fun j => ⟨asZwA D g j, hw j⟩
  have h : ((Work.MotAS.kleinPAS3 a' b' c' y' : ↥F) : OmA K D)
      = Work.MotAS.kleinPAS3 (asZaA D g) (asZbA D g) (asZcA D g) (asZwA D g) := by
    simp only [Work.MotAS.kleinPAS3]
    push_cast
    rfl
  rw [← h]
  exact (Work.MotAS.kleinPAS3 a' b' c' y').2

/-! ## §3 The residual chart generates the twist field

Generic port of `Work.MotAS.asResidualGen_from`. -/

theorem asResidualGenA_from (D : Work.MotV.KleinData 𝕜) (g : K) (hz0 : asZOmA D g 0 ≠ 0)
    (hrec : (asZvA D g 1 = asZOmA D g 0 * asZwA1 D g ∧
        asZvA D g 2 = asZOmA D g 0 * asZwA2 D g ∧
        asZvA D g 3 = asZOmA D g 0 * asZwA3 D g ∧
        asZvA D g 4 = asZOmA D g 0 * asZwA4 D g) ∧
      (asZOmA D g 0)⁻¹ =
        -(asZAA D g / asZmuA D g) *
          (Work.MotAS.kleinPAS1 (asZaA D g) (asZbA D g) (asZcA D g) (asZwA D g) +
            (asZlamA D g / asZmuA D g) *
              Work.MotAS.kleinPAS3 (asZaA D g) (asZbA D g) (asZcA D g) (asZwA D g))) :
    IntermediateField.adjoin K
        (Set.range (fun i : Fin 3 => asZOmA D g (⟨i.1 + 1, by omega⟩ : Fin 5) / asZOmA D g 0))
      = twistFieldAS D g := by
  haveI : CharP 𝕜 5 := charP_of_algebra_charP (𝕜 := 𝕜) (K := K)
  obtain ⟨⟨h1, h2, h3, h4⟩, ht⟩ := hrec
  have hy0 : asTwY D g 0 ≠ 0 := by
    intro h0
    apply hz0
    rw [asZOmA_zero_eq]
    have hv1 : asZvA D g 1 = 0 := by simp only [asZvA, h0, div_zero]
    have hv3 : asZvA D g 3 = 0 := by simp only [asZvA, h0, div_zero]
    rw [hv1, hv3, mul_zero, mul_zero, add_zero]
  apply le_antisymm
  · -- the residual coordinates lie in the twist field
    have hZmem : ∀ k : Fin 5, asZOmA D g k ∈ twistFieldAS D g := fun k => asZOmA_mem D g k
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro x ⟨i, rfl⟩
    exact div_mem (hZmem _) (hZmem 0)
  · -- the twist field is generated by the residual coordinates
    let L : IntermediateField K (OmA K D) :=
      IntermediateField.adjoin K
        (Set.range (fun i : Fin 3 => asZOmA D g (⟨i.1 + 1, by omega⟩ : Fin 5) / asZOmA D g 0))
    have hL : L = IntermediateField.adjoin K
        (Set.range (fun i : Fin 3 =>
          asZOmA D g (⟨i.1 + 1, by omega⟩ : Fin 5) / asZOmA D g 0)) := rfl
    rw [← hL]
    have hX : ∀ i : Fin 3,
        asZOmA D g (⟨i.1 + 1, by omega⟩ : Fin 5) / asZOmA D g 0 ∈ L :=
      fun i => IntermediateField.subset_adjoin K _ (Set.mem_range_self i)
    have hA : asZAA D g ∈ L :=
      IntermediateField.algebraMap_mem _ (phiAS (aK K D) (bK K D) 0 1)
    have hB : asZBA D g ∈ L :=
      IntermediateField.algebraMap_mem _ (phiAS (aK K D) (bK K D) 0 3)
    have hC : asZCA D g ∈ L :=
      IntermediateField.algebraMap_mem _ (phiAS (aK K D) (bK K D) 1 4)
    have hDD : asZDA D g ∈ L :=
      IntermediateField.algebraMap_mem _ (phiAS (aK K D) (bK K D) 2 3)
    have hE : asZEA D g ∈ L :=
      IntermediateField.algebraMap_mem _ (phiAS (aK K D) (bK K D) 3 4)
    have hmu : asZmuA D g ∈ L :=
      IntermediateField.algebraMap_mem _ (2 * (aK K D ^ 2 - aK K D * bK K D - bK K D ^ 2))
    have ha : asZaA D g ∈ L := IntermediateField.algebraMap_mem _ (aK K D)
    have hb : asZbA D g ∈ L := IntermediateField.algebraMap_mem _ (bK K D)
    have hc : asZcA D g ∈ L := IntermediateField.algebraMap_mem _ g
    have hlam : asZlamA D g ∈ L := by
      rw [asZlamA]
      exact add_mem (div_mem (mul_mem hmu hB) hA) (add_mem (pow_mem ha 2) (pow_mem hb 2))
    have hw3 : asZwA3 D g ∈ L := div_mem (hX 1) hDD
    have hw4 : asZwA4 D g ∈ L := div_mem (hX 2) hE
    have hw1 : asZwA1 D g ∈ L := div_mem (sub_mem (one_mem L) (mul_mem hB hw3)) hA
    have hw2 : asZwA2 D g ∈ L := div_mem (sub_mem (hX 0) (mul_mem hC hw4)) hA
    have hw : ∀ j : Fin 5, asZwA D g j ∈ L := by
      intro j
      fin_cases j
      · exact zero_mem L
      · exact hw1
      · exact hw2
      · exact hw3
      · exact hw4
    have hinv : (asZOmA D g 0)⁻¹ ∈ L := by
      rw [ht]
      exact mul_mem (neg_mem (div_mem hA hmu))
        (add_mem (kleinPAS1_mem_A D g L ha hb hc hw)
          (mul_mem (div_mem hlam hmu) (kleinPAS3_mem_A D g L ha hb hc hw)))
    have hz0L : asZOmA D g 0 ∈ L := by
      have h := inv_mem hinv
      rwa [inv_inv] at h
    have hv0 : asZvA D g 0 = 1 := by
      show asTwY D g 0 / asTwY D g 0 = 1
      exact div_self hy0
    have hvL : ∀ j : Fin 5, asZvA D g j ∈ L := by
      intro j
      fin_cases j
      · show asZvA D g 0 ∈ L
        rw [hv0]
        exact one_mem L
      · show asZvA D g 1 ∈ L
        rw [h1]
        exact mul_mem hz0L hw1
      · show asZvA D g 2 ∈ L
        rw [h2]
        exact mul_mem hz0L hw2
      · show asZvA D g 3 ∈ L
        rw [h3]
        exact mul_mem hz0L hw3
      · show asZvA D g 4 ∈ L
        rw [h4]
        exact mul_mem hz0L hw4
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro x ⟨j, rfl⟩
    exact hvL j

/-! ## §4 Nonvanishing of `Z 0` on the class-`3g` twisted Klein curve

Direct computation: `Z 0` is a nonzero scalar multiple of the linear form
`(3a+b)·y₁ + (3a+4b)·y₃`, whose vanishing would express `-(w+i)((3a+b)(w+i)² + (3a+4b))` as a
nontrivial `K̄`-linear relation among the linearly independent Klein coordinates `κ_i`; multiplying
the relations by `(w+i)` and summing contradicts `3a+b ≠ 0`. -/

theorem aszZ_three_mul_zero_ne_zero (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (g : K) : aszZ D (3 * g) 0 ≠ 0 := by
  haveI : CharP 𝕜 5 := charP_of_algebra_charP (𝕜 := 𝕜) (K := K)
  have hG : D.Good := hD.1
  have hy0 : asTwY D (3 * g) 0 ≠ 0 := asTwY_zero_ne_zero D (3 * g) hG
  have hkey : algebraMap K (OmA K D) (3 * aK K D + bK K D) * asTwY D (3 * g) 1
      + algebraMap K (OmA K D) (3 * aK K D + 4 * bK K D) * asTwY D (3 * g) 3 ≠ 0 := by
    intro hprod
    have hk := asZ0_key_A D (3 * g)
    rw [hprod] at hk
    have hsum : ∑ i : Fin 5, asZcIA D (3 * g) i • Work.MotV.kleinCoord D (KbA K) i = 0 := by
      simpa only [Algebra.smul_def] using hk.symm
    have hind : LinearIndependent (KbA K) (Work.MotV.kleinCoord D (KbA K)) :=
      kleinCoord_linearIndependent_KbA D hG
    rw [Fintype.linearIndependent_iff] at hind
    have hc : ∀ i : Fin 5, asZcIA D (3 * g) i = 0 := fun i => hind (asZcIA D (3 * g)) hsum i
    have hrel : ∀ i : Fin 5, (asRoot (3 * g) + (i : ℕ)) * asZcIA D (3 * g) i = 0 := by
      intro i
      rw [hc i, mul_zero]
    have hsum0 : ∑ i : Fin 5, (asRoot (3 * g) + (i : ℕ)) * asZcIA D (3 * g) i = 0 :=
      Finset.sum_eq_zero (fun i _ => hrel i)
    have hexp : (∑ i : Fin 5, (asRoot (3 * g) + (i : ℕ)) * asZcIA D (3 * g) i)
        = -(algebraMap K (KbA K) (3 * aK K D + bK K D)
              * (∑ i : Fin 5, (asRoot (3 * g) + (i : ℕ)) ^ 4)
            + algebraMap K (KbA K) (3 * aK K D + 4 * bK K D)
              * (∑ i : Fin 5, (asRoot (3 * g) + (i : ℕ)) ^ 2)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [asZcIA]
      first | refl_ring1 | ring
    have hfin : algebraMap K (KbA K) (3 * aK K D + bK K D) * (4 : KbA K) = 0 := by
      have h := hsum0
      rw [hexp, sum_five_pow_four (five_eq_zero_KbA K) (asRoot (3 * g)),
        sum_five_sq_A (five_eq_zero_KbA K) (asRoot (3 * g))] at h
      simpa using h
    have h4ne : (4 : KbA K) ≠ 0 := by
      rw [show (4 : KbA K) = -(1 : KbA K) by linear_combination five_eq_zero_KbA K]
      exact neg_ne_zero.mpr one_ne_zero
    have hα0 : algebraMap K (KbA K) (3 * aK K D + bK K D) = 0 := by
      rcases mul_eq_zero.mp hfin with h | h
      · exact h
      · exact absurd h h4ne
    have h3ab : 3 * aK K D + bK K D ≠ 0 :=
      three_mul_add_ne_zero_A (aK K D) (bK K D) (aK_sq_sub_ne D hD)
    exact h3ab ((algebraMap K (KbA K)).injective (by rw [hα0, map_zero]))
  intro h0
  have hznum : aszZ D (3 * g) 0 * asTwY D (3 * g) 0
      = algebraMap K (OmA K D) (3 * aK K D + bK K D) * asTwY D (3 * g) 1
        + algebraMap K (OmA K D) (3 * aK K D + 4 * bK K D) * asTwY D (3 * g) 3 := by
    rw [aszZ_eq_asZOmA, asZOmA_zero_eq, asZAA, asZBA, Work.MotAS.phiAS_01, Work.MotAS.phiAS_03]
    simp only [asZvA]
    field_simp [hy0]
  exact hkey (by rw [← hznum, h0, zero_mul])

/-- **The residual coordinates generate the twist field.**  For `K` a field of characteristic `5`,
`D : KleinData 𝕜` with `ASGood D` and `g : K`: the normalising denominator `aszZ D (3*g) 0` does not
vanish on the class-`3g` twisted Klein curve, and the three residual chart coordinates
`aszResVec D g i = aszZ D (3*g) (i+1) / aszZ D (3*g) 0` generate the twist field
`twistFieldAS D (3 * g)` over `K`.  Equivalently: the linear projection `phiAS` restricted to
`C_{3g}` is dominant onto the AS residual curve.

This is the `RatFunc 𝕜 ↦ K`, `fAS 𝕜 ↦ g` fork of `Work.MotAS.ASResidualGen`
(`Submission/Work/MotAS/ASResidualGen.lean`, **proved and sorry-free**), whose route is the
recovery package `asZOm_zero_ne_zero` + `asZResRecoverySelf` + `asResidualGen_from`.  The generic
port of that package (`asZOmA`, `asZwA`, ... in
`Submission/Work/MotV5/Contrib/AsResDefsA.lean`, with the proof route written out in
`Submission/Work/MotV5/Contrib/AsZ0ANeZero_GUIDE.md` and
`Submission/Work/MotV5/Contrib/AsZResRecoveryA_GUIDE.md`) is the suggested route. -/
theorem ASZResVecAdjoin (K : Type) [Field K] [CharP K 5] {𝕜 : Type} [Field 𝕜] [Algebra 𝕜 K]
    (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) (g : K)
    (hg : ¬ ∃ u : K, u ^ 5 - u = g) :
    Work.MotC5N3.aszZ D (3 * g) 0 ≠ 0 ∧
      IntermediateField.adjoin K (Set.range (Work.MotC5N3.aszResVec D g)) = ⊤ := by
  haveI : CharP 𝕜 5 := charP_of_algebra_charP (𝕜 := 𝕜) (K := K)
  refine ⟨aszZ_three_mul_zero_ne_zero D hD g, ?_⟩
  have hz0 : asZOmA D (3 * g) 0 ≠ 0 := aszZ_three_mul_zero_ne_zero D hD g
  have hamb := asResidualGenA_from D (3 * g) hz0
    (Work.MotV5.Contrib.asZResRecoverySelfA D hD (3 * g) hz0)
  refine (adjoin_subtype_eq_top_iff (twistFieldAS D (3 * g))
    (Set.range (aszResVec D g))).mpr ?_
  have hgoal : IntermediateField.adjoin K (Set.range (fun i : Fin 3 =>
      aszZ D (3 * g) (⟨i.1 + 1, by omega⟩ : Fin 5) / aszZ D (3 * g) 0))
      = twistFieldAS D (3 * g) := by
    simpa only [aszZ_eq_asZOmA] using hamb
  rwa [coe_image_range_aszResVec D g]

end Work.MotC5N3
