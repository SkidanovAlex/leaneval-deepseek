/-
# ZeroFreeTables — `OtherLamCountBounded_of_jutilaNP`

**The last link between the project's *actual* Jutila node and Heath-Brown's Table 7.**

## The gap this file closes

`Work.ZeroFreeTables.HBTable7_of_jutila_only` reduces Table 7 to the near-line *count*
`Work.ZeroFreeTables.OtherLamCountBounded`, and `Work.ZeroFreeTables.OtherLamCountBounded_of_jutila`
derives that count from the **all-character** form of Jutila's log-free family zero-density estimate
(`Work.LinnikAreas.FamilyZeroDensityJutila`, i.e. `Σ_{χ mod q} N(σ,T,χ) ≤ C(qT)^{(2+ε)(1-σ)}`).

That all-character form is **not** the project's node: it is *not a theorem* (its `χ = 1` part is a
sharp density statement for `ζ` at `σ = 4/5`, which is beyond the literature; see the header of
`Submission/Work/LinnikAreas/area2.lean`).  The project's node — the one the fleet is proving and
the one recorded, verbatim, as `Work.ZeroDensity.Jutila.jutilaNonPrincipal` — is the **non-principal**
form

  `Work.LinnikAreas.FamilyZeroDensityJutilaNP`:
  `Σ_{χ ≠ 1} N(σ,T,χ) ≤ C_ε (qT)^{(2+ε)(1-σ)}` for `4/5 ≤ σ ≤ 1`, `T ≥ 1`,

which *is* Jutila's Theorem 1 (1.7) and *is* Heath-Brown's (1.4) for the non-principal part.

This file proves that the non-principal form already suffices for Table 7:

* `otherLamCount_le_zeroCountSumNP` — the *non-principal* refinement of the counting
  `otherLamCount χ₁ Λ H ≤ Σ_{χ ≠ 1} N(1 - max Λ 0/log q, max H 1, χ)`.  (The existing
  `otherLamCount_le_zeroCountSum` bounds `otherLamCount` by the sum over **all** characters, which is
  useless here: the `χ = 1` term is exactly the `ζ`-part that is not a theorem.)  The refinement is
  legitimate because `otherLamCount`'s summand already excludes the character `χ = 1`, so the
  `χ = 1` term of the family sum is not needed.
* `OtherLamCountBounded_of_jutilaNP` — `FamilyZeroDensityJutilaNP ⟹ OtherLamCountBounded`.
* `HBTable7_of_jutilaNP` / `HBTable7_of_jutilaNP_only` — `HBTable7` from the non-principal node
  together with the (now unconditional) `λ₀`-rows `Lam0Table7_of_wide` and the per-row data
  `HBTable7_rowData`.

## Consequence

```
theorem HBTable7_proof : Work.ZeroFreeTables.HBTable7 :=
  Work.ZeroFreeTables.HBTable7_of_jutilaNP_only
    (Work.LinnikAreas.familyZeroDensityJutilaNP_of_chapter
      Work.ZeroDensity.Jutila.jutilaNonPrincipal)
```

closes the target as soon as the node `Work.ZeroDensity.Jutila.jutilaNonPrincipal` (the `sorry` in
`Submission/Work/ZeroDensity/Jutila/jutilaNonPrincipal.lean`) is discharged: no principal-character
(`ζ`) input is required anywhere on this route.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HBTable7_of_count
import Submission.Work.LinnikAreas.FarBoundOfJutilaMontgomery
import Submission.Work.ZeroFreeTables.rpow_three_le_exp
import Submission.Work.ZeroFreeTables.otherLamCount_le_zeroCountSum
import Submission.Work.ZeroFreeTables.HBTable7_rowData
import Submission.Work.ZeroFreeTables.Lam0Table7_of_wide

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

/-! ## 1. The non-principal refinement of the counting -/

/-- From `λ(ρ) = (1 - Re ρ)·log q ≤ Λ` and `2 ≤ q` deduce `1 - max Λ 0 / log q ≤ Re ρ`. -/
private lemma one_sub_max_div_log_le_re_np {q : ℕ} [NeZero q] (hq : 2 ≤ q) {ρ : ℂ} {Λ : ℝ}
    (h : Work.LinnikContract.lamOf q ρ ≤ Λ) :
    1 - max Λ 0 / Real.log (q : ℝ) ≤ ρ.re := by
  have hlogpos : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have h1 : (1 - ρ.re) * Real.log (q : ℝ) ≤ max Λ 0 :=
    le_trans (by simpa [Work.LinnikContract.lamOf] using h) (le_max_left _ _)
  have h2 : 1 - ρ.re ≤ max Λ 0 / Real.log (q : ℝ) := (le_div_iff₀ hlogpos).mpr h1
  linarith

/-- The summand of `otherLamCount χ₁ Λ H`, as a function of the pair `(χ, ρ)`. -/
private def otherTermNP {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (Λ H : ℝ)
    (p : DirichletCharacter ℂ q × ℂ) : ℝ :=
  if p.1 ≠ 1 ∧ p.1 ≠ χ₁ ∧ p.1 ≠ χ₁⁻¹ ∧ Work.LinnikContract.zeroMult p.1 p.2 ≠ 0 ∧
      |p.2.im| ≤ H ∧ Work.LinnikContract.lamOf q p.2 ≤ Λ
    then (Work.LinnikContract.zeroMult p.1 p.2 : ℝ) else 0

/-- The summand of `zeroCountIn χ σ T`, *with the principal character discarded*. -/
private def countTermNP {q : ℕ} [NeZero q] (σ T : ℝ)
    (p : DirichletCharacter ℂ q × ℂ) : ℝ :=
  if p.1 ≠ 1 ∧ σ ≤ p.2.re ∧ p.2.re ≤ 1 ∧ |p.2.im| ≤ T
    then (Work.LinnikContract.zeroMult p.1 p.2 : ℝ) else 0

/-- **The non-principal counting.**  `otherLamCount χ₁ Λ H` is at most the multiplicity-weighted
number of zeros `ρ` of the characters `χ ≠ 1` mod `q` with
`1 - max Λ 0 / log q ≤ Re ρ ≤ 1` and `|Im ρ| ≤ max H 1`.

This is `Work.ZeroFreeTables.otherLamCount_le_zeroCountSum` with the sum over the whole family
replaced by the sum over `Finset.univ.erase 1`: the extra factor `p.1 ≠ 1` in the comparison
summand removes exactly the principal character, whose near-line count is a `ζ`-density statement
that is *not* available, and which `otherLamCount` never uses. -/
theorem otherLamCount_le_zeroCountSumNP {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (χ₁ : DirichletCharacter ℂ q) (Λ H : ℝ) :
    Work.ZeroFreeTables.otherLamCount χ₁ Λ H ≤
      ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        Work.LinnikAreas.zeroCountIn χ (1 - max Λ 0 / Real.log (q : ℝ)) (max H 1) := by
  classical
  set σ : ℝ := 1 - max Λ 0 / Real.log (q : ℝ) with hσ
  set T : ℝ := max H 1 with hT
  -- pointwise domination of the summands
  have hFG : otherTermNP (q := q) χ₁ Λ H ≤ countTermNP (q := q) σ T := by
    intro p
    simp only [otherTermNP, countTermNP]
    by_cases hc : p.1 ≠ 1 ∧ p.1 ≠ χ₁ ∧ p.1 ≠ χ₁⁻¹ ∧ Work.LinnikContract.zeroMult p.1 p.2 ≠ 0 ∧
        |p.2.im| ≤ H ∧ Work.LinnikContract.lamOf q p.2 ≤ Λ
    · obtain ⟨h1, h2, h3, hzm, him, hlam⟩ := hc
      rw [if_pos ⟨h1, h2, h3, hzm, him, hlam⟩]
      have hcond : p.1 ≠ 1 ∧ σ ≤ p.2.re ∧ p.2.re ≤ 1 ∧ |p.2.im| ≤ T :=
        ⟨h1,
         by rw [hσ]; exact one_sub_max_div_log_le_re_np hq hlam,
         le_of_lt (Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one p.1 hzm),
         by rw [hT]; exact le_trans him (le_max_left H 1)⟩
      rw [if_pos hcond]
    · rw [if_neg hc]
      split_ifs with hg
      · exact Nat.cast_nonneg _
      · exact le_refl 0
  -- both summands are finitely supported (their supports lie in a finite union of boxes)
  have hGfin : Function.HasFiniteSupport (countTermNP (q := q) σ T) := by
    rw [Function.HasFiniteSupport]
    refine (Finset.finite_toSet (Finset.univ.biUnion (fun χ : DirichletCharacter ℂ q =>
      ((Work.LinnikAreas.boxMaxZeroAux.finite_zeroMult_box χ σ T).toFinset).image
        (fun z : ℂ => (χ, z))))).subset ?_
    intro p hp
    rw [Function.mem_support] at hp
    have hc : p.1 ≠ 1 ∧ σ ≤ p.2.re ∧ p.2.re ≤ 1 ∧ |p.2.im| ≤ T := by
      by_contra h
      exact hp (by simp only [countTermNP, if_neg h])
    have hzm : Work.LinnikContract.zeroMult p.1 p.2 ≠ 0 := by
      intro h
      exact hp (by simp only [countTermNP, if_pos hc, h, Nat.cast_zero])
    refine Finset.mem_biUnion.mpr ⟨p.1, Finset.mem_univ _, Finset.mem_image.mpr ⟨p.2, ?_, rfl⟩⟩
    rw [Set.Finite.mem_toFinset]
    exact ⟨hzm, hc.2.1, hc.2.2.1, hc.2.2.2⟩
  have hFfin : Function.HasFiniteSupport (otherTermNP (q := q) χ₁ Λ H) := by
    rw [Function.HasFiniteSupport]
    refine (Finset.finite_toSet (Finset.univ.biUnion (fun χ : DirichletCharacter ℂ q =>
      ((Work.LinnikAreas.boxMaxZeroAux.finite_zeroMult_box χ σ H).toFinset).image
        (fun z : ℂ => (χ, z))))).subset ?_
    intro p hp
    rw [Function.mem_support] at hp
    have hc : p.1 ≠ 1 ∧ p.1 ≠ χ₁ ∧ p.1 ≠ χ₁⁻¹ ∧ Work.LinnikContract.zeroMult p.1 p.2 ≠ 0 ∧
        |p.2.im| ≤ H ∧ Work.LinnikContract.lamOf q p.2 ≤ Λ := by
      by_contra h
      exact hp (by simp only [otherTermNP, if_neg h])
    obtain ⟨h1, h2, h3, hzm, him, hlam⟩ := hc
    refine Finset.mem_biUnion.mpr ⟨p.1, Finset.mem_univ _, Finset.mem_image.mpr ⟨p.2, ?_, rfl⟩⟩
    rw [Set.Finite.mem_toFinset]
    exact ⟨hzm, by rw [hσ]; exact one_sub_max_div_log_le_re_np hq hlam,
      le_of_lt (Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one p.1 hzm), him⟩
  have hle : Work.ZeroFreeTables.otherLamCount χ₁ Λ H ≤
      ∑ᶠ p : DirichletCharacter ℂ q × ℂ, countTermNP (q := q) σ T p :=
    calc Work.ZeroFreeTables.otherLamCount χ₁ Λ H
        = ∑ᶠ p : DirichletCharacter ℂ q × ℂ, otherTermNP (q := q) χ₁ Λ H p := rfl
      _ ≤ ∑ᶠ p : DirichletCharacter ℂ q × ℂ, countTermNP (q := q) σ T p :=
          finsum_le_finsum' hFfin hGfin hFG
  -- the iterated sum of `countTermNP` is the sum over the non-principal characters
  have hinner : ∀ χ : DirichletCharacter ℂ q,
      (∑ᶠ ρ : ℂ, countTermNP (q := q) σ T (χ, ρ))
        = if χ ≠ 1 then Work.LinnikAreas.zeroCountIn χ σ T else 0 := by
    intro χ
    by_cases hχ : χ ≠ 1
    · rw [if_pos hχ]
      refine finsum_congr fun ρ => ?_
      simp only [countTermNP]
      by_cases hc : σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
      · rw [if_pos ⟨hχ, hc.1, hc.2.1, hc.2.2⟩, if_pos hc]
      · rw [if_neg (fun h => hc ⟨h.2.1, h.2.2.1, h.2.2.2⟩), if_neg hc]
    · rw [if_neg hχ]
      refine finsum_eq_zero_of_forall_eq_zero fun ρ => ?_
      have h1 : ¬ (χ ≠ 1 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T) := fun h => hχ h.1
      simp only [countTermNP]
      rw [if_neg h1]
  have hsum : (∑ᶠ p : DirichletCharacter ℂ q × ℂ, countTermNP (q := q) σ T p)
      = ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          Work.LinnikAreas.zeroCountIn χ σ T := by
    rw [finsum_prod_eq_sum _ hGfin]
    rw [Finset.sum_congr rfl (fun χ _ => hinner χ)]
    rw [← Finset.sum_filter]
    congr 1
    ext χ
    simp
  rw [hsum] at hle
  exact hle

/-! ## 2. The count from the non-principal node -/

/-- **The near-line count `OtherLamCountBounded` from the non-principal Jutila node.**

`Work.LinnikAreas.FamilyZeroDensityJutilaNP` at `ε = 1`, `σ = 1 - max Λ 0/log q`,
`T = max H 1` gives (`Λ ≤ 3`, `H ≤ 10 log q`, `q ≥ 15·10⁶`)
`otherLamCount χ₁ Λ H ≤ C·(qT)^{3(1-σ)} = C·(qT)^{3 max Λ 0/log q} ≤ C·e^{27}`.

No principal-character input is used: the counting step is the non-principal refinement
`otherLamCount_le_zeroCountSumNP` above. -/
theorem OtherLamCountBounded_of_jutilaNP (h : Work.LinnikAreas.FamilyZeroDensityJutilaNP) :
    Work.ZeroFreeTables.OtherLamCountBounded := by
  obtain ⟨CJ, hCJpos, hCJ⟩ := h 1 (by norm_num)
  refine ⟨CJ * Real.exp 27, mul_pos hCJpos (Real.exp_pos 27), 15000000, ?_⟩
  intro q hq _inst χ₁ Λ H hΛ hH
  have hq2 : 2 ≤ q := by omega
  -- `log q ≥ 15` for `q ≥ 15000000`
  have hlog15 : 15 ≤ Real.log (q : ℝ) := by
    refine (Real.le_log_iff_exp_le (by positivity)).mpr ?_
    have h1 : Real.exp 15 = Real.exp 1 ^ 15 := by
      rw [show (15:ℝ) = ((15:ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
    have h2 : Real.exp 1 ^ 15 < (3 : ℝ) ^ 15 :=
      pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos 1).le (by norm_num : (15:ℕ) ≠ 0)
    have h3 : (3 : ℝ) ^ 15 ≤ (q : ℝ) := by
      have h4 : (3 : ℝ) ^ 15 = 14348907 := by norm_num
      rw [h4]
      exact_mod_cast (by omega : 14348907 ≤ q)
    linarith
  have hlogpos : 0 < Real.log (q : ℝ) := by linarith
  -- the range conditions of Jutila's estimate at `σ = 1 - max Λ 0 / log q`, `T = max H 1`
  have hσlo : (4 : ℝ) / 5 ≤ 1 - max Λ 0 / Real.log (q : ℝ) := by
    have hmax : max Λ 0 ≤ 3 := max_le hΛ (by norm_num)
    have hdiv : max Λ 0 / Real.log (q : ℝ) ≤ 1 / 5 := by
      rw [div_le_div_iff₀ hlogpos (by norm_num : (0:ℝ) < 5)]
      nlinarith [hmax, hlog15]
    linarith
  have hσhi : 1 - max Λ 0 / Real.log (q : ℝ) ≤ 1 := by
    have : 0 ≤ max Λ 0 / Real.log (q : ℝ) := div_nonneg (le_max_right _ _) hlogpos.le
    linarith
  have hT1 : 1 ≤ max H 1 := le_max_right _ _
  have hbound := hCJ q hq2 (1 - max Λ 0 / Real.log (q : ℝ)) (max H 1) hσlo hσhi hT1
  have hbound' : (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
      Work.LinnikAreas.zeroCountIn χ (1 - max Λ 0 / Real.log (q : ℝ)) (max H 1))
      ≤ CJ * ((q : ℝ) * max H 1) ^ (3 * (1 - (1 - max Λ 0 / Real.log (q : ℝ)))) := by
    have hb := hbound
    rw [show (2 : ℝ) + 1 = 3 by norm_num] at hb
    exact hb
  have hTq : max H 1 ≤ 10 * Real.log (q : ℝ) :=
    max_le (le_trans hH le_rfl) (by linarith)
  have hexp : 3 * (1 - (1 - max Λ 0 / Real.log (q : ℝ)))
      = 3 * (max Λ 0 / Real.log (q : ℝ)) := by ring
  have hkey : ((q : ℝ) * max H 1) ^ (3 * (1 - (1 - max Λ 0 / Real.log (q : ℝ))))
      ≤ Real.exp 27 := by
    rw [hexp]
    exact rpow_three_le_exp hlog15 hΛ hT1 hTq
  calc otherLamCount χ₁ Λ H
      ≤ ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          Work.LinnikAreas.zeroCountIn χ (1 - max Λ 0 / Real.log (q : ℝ)) (max H 1) :=
        otherLamCount_le_zeroCountSumNP hq2 χ₁ Λ H
    _ ≤ CJ * ((q : ℝ) * max H 1) ^ (3 * (1 - (1 - max Λ 0 / Real.log (q : ℝ)))) := hbound'
    _ ≤ CJ * Real.exp 27 := mul_le_mul_of_nonneg_left hkey hCJpos.le

/-! ## 3. The consumer: Table 7 from the non-principal node -/

/-- **Heath-Brown's Table 7 from the non-principal Jutila node** (and the `λ₀`-rows of `χ₁`). -/
theorem HBTable7_of_jutilaNP (h : Work.LinnikAreas.FamilyZeroDensityJutilaNP)
    (hlam0 : Work.ZeroFreeTables.Lam0Table7) : Work.ZeroFreeTables.HBTable7 :=
  Work.ZeroFreeTables.HBTable7_of_count (OtherLamCountBounded_of_jutilaNP h) hlam0
    Work.ZeroFreeTables.HBTable7_rowData

/-- **Heath-Brown's Table 7 from the non-principal Jutila node alone.**  The `λ₀`-input is
unconditional (`Lam0Table7_of_wide`), so the single remaining input is the non-principal log-free
family count `FamilyZeroDensityJutilaNP` — verbatim the project's node
`Work.ZeroDensity.Jutila.jutilaNonPrincipal`
(`Work.LinnikAreas.familyZeroDensityJutilaNP_of_chapter`). -/
theorem HBTable7_of_jutilaNP_only (h : Work.LinnikAreas.FamilyZeroDensityJutilaNP) :
    Work.ZeroFreeTables.HBTable7 :=
  HBTable7_of_jutilaNP h Work.ZeroFreeTables.Lam0Table7_of_wide

end Work.ZeroFreeTables
