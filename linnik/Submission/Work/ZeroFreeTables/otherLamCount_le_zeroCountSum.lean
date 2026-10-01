import Mathlib
import Submission.Work.ZeroFreeTables.HBTable7_defs2
import Submission.Work.LinnikAreas.Setup
import Submission.Work.LinnikAreas.boxMaxZero

/-!
# `otherLamCount ≤ Σ_χ N(χ, 1 - max Λ 0 / log q, max H 1)`

The counting function `Work.ZeroFreeTables.otherLamCount χ₁ Λ H` counts (with multiplicity) the
zeros `ρ` of the characters `χ ∉ {1, χ₁, χ₁⁻¹}` with `λ(ρ) = (1 - Re ρ)·log q ≤ Λ` and
`|Im ρ| ≤ H`.  It is a *sub*-multiset of the family count
`∑_χ Work.LinnikAreas.zeroCountIn χ σ T`, where `σ = 1 - max Λ 0 / log q` and `T = max H 1`:
a zero counted on the left has `(1 - Re ρ)·log q ≤ Λ ≤ max Λ 0`, hence
`Re ρ ≥ 1 - max Λ 0 / log q = σ` (because `log q > 0`), and `|Im ρ| ≤ H ≤ max H 1`; the
multiplicity `zeroMult χ ρ` is the same in both counts.  The zero is automatically in the strip
`Re ρ ≤ 1` because a zero of a completed `L`-function lies in the critical strip
(`Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one`).

Both sides are finite sums over the (finite) zero set in a compact box, so the inequality reduces
to a pointwise comparison of the summands; this is formalised by writing the left-hand side as a
`finsum` over the product type `DirichletCharacter ℂ q × ℂ`, comparing it pointwise with the
analogous summand of the family count (`finsum_le_finsum'`), and re-indexing the product sum as an
iterated sum (`finsum_prod_eq_sum`, proved below from `Finset.sum_fiberwise` and
`Finset.sum_image`).

The extra characters `1, χ₁, χ₁⁻¹` on the right-hand side only add nonnegative terms, so they are
harmless.
-/

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

/-- From `λ(ρ) = (1 - Re ρ)·log q ≤ Λ` and `2 ≤ q` deduce `1 - max Λ 0 / log q ≤ Re ρ`.
Since `log q > 0` and `Λ ≤ max Λ 0`, this is just `1 - Re ρ ≤ max Λ 0 / log q`. -/
private lemma one_sub_max_div_log_le_re {q : ℕ} [NeZero q] (hq : 2 ≤ q) {ρ : ℂ} {Λ : ℝ}
    (h : Work.LinnikContract.lamOf q ρ ≤ Λ) :
    1 - max Λ 0 / Real.log (q : ℝ) ≤ ρ.re := by
  have hlogpos : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have h1 : (1 - ρ.re) * Real.log (q : ℝ) ≤ max Λ 0 :=
    le_trans (by simpa [Work.LinnikContract.lamOf] using h) (le_max_left _ _)
  have h2 : 1 - ρ.re ≤ max Λ 0 / Real.log (q : ℝ) := (le_div_iff₀ hlogpos).mpr h1
  linarith

/-- The summand of `otherLamCount χ₁ Λ H`, as a function of the pair `(χ, ρ)`. -/
private def otherTerm {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (Λ H : ℝ)
    (p : DirichletCharacter ℂ q × ℂ) : ℝ :=
  if p.1 ≠ 1 ∧ p.1 ≠ χ₁ ∧ p.1 ≠ χ₁⁻¹ ∧ Work.LinnikContract.zeroMult p.1 p.2 ≠ 0 ∧
      |p.2.im| ≤ H ∧ Work.LinnikContract.lamOf q p.2 ≤ Λ
    then (Work.LinnikContract.zeroMult p.1 p.2 : ℝ) else 0

/-- The summand of `zeroCountIn χ σ T`, as a function of the pair `(χ, ρ)`. -/
private def countTerm {q : ℕ} [NeZero q] (σ T : ℝ)
    (p : DirichletCharacter ℂ q × ℂ) : ℝ :=
  if σ ≤ p.2.re ∧ p.2.re ≤ 1 ∧ |p.2.im| ≤ T then (Work.LinnikContract.zeroMult p.1 p.2 : ℝ)
  else 0

/-- **Re-indexing a `finsum` over a product as an iterated sum.**  For a finitely supported
function `f` on `α × β` with `α` finite, `∑ᶠ p, f p = ∑ a, ∑ᶠ b, f (a, b)`.  (The hypothesis of
finite support is necessary: `finsum` is a junk value on infinite supports.) -/
lemma finsum_prod_eq_sum {α β M : Type*} [Fintype α] [AddCommMonoid M]
    (f : α × β → M) (hf : Function.HasFiniteSupport f) :
    ∑ᶠ p : α × β, f p = ∑ a, ∑ᶠ b, f (a, b) := by
  classical
  have hmem : ∀ p : α × β, p ∈ hf.toFinset ↔ f p ≠ 0 := fun p => hf.mem_toFinset
  have hL : ∑ᶠ p : α × β, f p = ∑ p ∈ hf.toFinset, f p :=
    finsum_eq_finsetSum_of_support_subset f (fun p hp => (hmem p).mpr hp)
  have hinner : ∀ a : α, ∑ᶠ b, f (a, b) = ∑ p ∈ hf.toFinset.filter (fun p => p.1 = a), f p := by
    intro a
    have hsub : Function.support (fun b => f (a, b)) ⊆
        ↑((hf.toFinset.filter (fun p => p.1 = a)).image (fun p => p.2)) := by
      intro b hb
      exact Finset.mem_coe.mpr
        (Finset.mem_image.mpr ⟨(a, b), Finset.mem_filter.mpr ⟨(hmem _).mpr hb, rfl⟩, rfl⟩)
    have hinj : Set.InjOn (fun p : α × β => p.2)
        ↑(hf.toFinset.filter (fun p => p.1 = a)) := by
      intro x hx y hy hxy
      have hx' := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
      have hy' := Finset.mem_filter.mp (Finset.mem_coe.mp hy)
      exact Prod.ext (by rw [hx'.2, hy'.2]) hxy
    rw [finsum_eq_finsetSum_of_support_subset (fun b => f (a, b)) hsub]
    rw [Finset.sum_image (f := fun b => f (a, b))
      (s := hf.toFinset.filter (fun p => p.1 = a)) (g := fun p => p.2) hinj]
    exact Finset.sum_congr rfl (fun p hp => by rw [← (Finset.mem_filter.mp hp).2])
  calc ∑ᶠ p : α × β, f p = ∑ p ∈ hf.toFinset, f p := hL
    _ = ∑ a, ∑ p ∈ hf.toFinset.filter (fun p => p.1 = a), f p :=
        (Finset.sum_fiberwise hf.toFinset (fun p : α × β => p.1) f).symm
    _ = ∑ a, ∑ᶠ b, f (a, b) := Finset.sum_congr rfl (fun a _ => (hinner a).symm)

/-- `otherLamCount χ₁ Λ H` is at most the multiplicity-weighted number of zeros `ρ` of *all*
characters mod `q` with `1 - max Λ 0 / log q ≤ Re ρ ≤ 1` and `|Im ρ| ≤ max H 1`. -/
theorem otherLamCount_le_zeroCountSum {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (χ₁ : DirichletCharacter ℂ q) (Λ H : ℝ) :
    Work.ZeroFreeTables.otherLamCount χ₁ Λ H ≤
      ∑ χ : DirichletCharacter ℂ q,
        Work.LinnikAreas.zeroCountIn χ (1 - max Λ 0 / Real.log (q : ℝ)) (max H 1) := by
  classical
  set σ : ℝ := 1 - max Λ 0 / Real.log (q : ℝ) with hσ
  set T : ℝ := max H 1 with hT
  -- pointwise domination of the summands
  have hFG : otherTerm (q := q) χ₁ Λ H ≤ countTerm (q := q) σ T := by
    intro p
    simp only [otherTerm, countTerm]
    by_cases hc : p.1 ≠ 1 ∧ p.1 ≠ χ₁ ∧ p.1 ≠ χ₁⁻¹ ∧ Work.LinnikContract.zeroMult p.1 p.2 ≠ 0 ∧
        |p.2.im| ≤ H ∧ Work.LinnikContract.lamOf q p.2 ≤ Λ
    · obtain ⟨h1, h2, h3, hzm, him, hlam⟩ := hc
      rw [if_pos ⟨h1, h2, h3, hzm, him, hlam⟩]
      have hcond : σ ≤ p.2.re ∧ p.2.re ≤ 1 ∧ |p.2.im| ≤ T :=
        ⟨by rw [hσ]; exact one_sub_max_div_log_le_re hq hlam,
         le_of_lt (Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one p.1 hzm),
         by rw [hT]; exact le_trans him (le_max_left H 1)⟩
      rw [if_pos hcond]
    · rw [if_neg hc]
      split_ifs with hg
      · exact Nat.cast_nonneg _
      · exact le_refl 0
  -- both summands are finitely supported (their supports lie in a finite union of boxes)
  have hGfin : Function.HasFiniteSupport (countTerm (q := q) σ T) := by
    rw [Function.HasFiniteSupport]
    refine (Finset.finite_toSet (Finset.univ.biUnion (fun χ : DirichletCharacter ℂ q =>
      ((Work.LinnikAreas.boxMaxZeroAux.finite_zeroMult_box χ σ T).toFinset).image
        (fun z : ℂ => (χ, z))))).subset ?_
    intro p hp
    rw [Function.mem_support] at hp
    have hc : σ ≤ p.2.re ∧ p.2.re ≤ 1 ∧ |p.2.im| ≤ T := by
      by_contra h
      exact hp (by simp only [countTerm, if_neg h])
    have hzm : Work.LinnikContract.zeroMult p.1 p.2 ≠ 0 := by
      intro h
      exact hp (by simp only [countTerm, if_pos hc, h, Nat.cast_zero])
    refine Finset.mem_biUnion.mpr ⟨p.1, Finset.mem_univ _, Finset.mem_image.mpr ⟨p.2, ?_, rfl⟩⟩
    rw [Set.Finite.mem_toFinset]
    exact ⟨hzm, hc.1, hc.2.1, hc.2.2⟩
  have hFfin : Function.HasFiniteSupport (otherTerm (q := q) χ₁ Λ H) := by
    rw [Function.HasFiniteSupport]
    refine (Finset.finite_toSet (Finset.univ.biUnion (fun χ : DirichletCharacter ℂ q =>
      ((Work.LinnikAreas.boxMaxZeroAux.finite_zeroMult_box χ σ H).toFinset).image
        (fun z : ℂ => (χ, z))))).subset ?_
    intro p hp
    rw [Function.mem_support] at hp
    have hc : p.1 ≠ 1 ∧ p.1 ≠ χ₁ ∧ p.1 ≠ χ₁⁻¹ ∧ Work.LinnikContract.zeroMult p.1 p.2 ≠ 0 ∧
        |p.2.im| ≤ H ∧ Work.LinnikContract.lamOf q p.2 ≤ Λ := by
      by_contra h
      exact hp (by simp only [otherTerm, if_neg h])
    obtain ⟨h1, h2, h3, hzm, him, hlam⟩ := hc
    refine Finset.mem_biUnion.mpr ⟨p.1, Finset.mem_univ _, Finset.mem_image.mpr ⟨p.2, ?_, rfl⟩⟩
    rw [Set.Finite.mem_toFinset]
    exact ⟨hzm, by rw [hσ]; exact one_sub_max_div_log_le_re hq hlam,
      le_of_lt (Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one p.1 hzm), him⟩
  have hmain : Work.ZeroFreeTables.otherLamCount χ₁ Λ H ≤
      ∑ χ : DirichletCharacter ℂ q, Work.LinnikAreas.zeroCountIn χ σ T := by
    calc Work.ZeroFreeTables.otherLamCount χ₁ Λ H
        = ∑ᶠ p : DirichletCharacter ℂ q × ℂ, otherTerm (q := q) χ₁ Λ H p := rfl
      _ ≤ ∑ᶠ p : DirichletCharacter ℂ q × ℂ, countTerm (q := q) σ T p :=
          finsum_le_finsum' hFfin hGfin hFG
      _ = ∑ χ : DirichletCharacter ℂ q, ∑ᶠ ρ : ℂ, countTerm (q := q) σ T (χ, ρ) :=
          finsum_prod_eq_sum _ hGfin
      _ = ∑ χ : DirichletCharacter ℂ q, Work.LinnikAreas.zeroCountIn χ σ T := by
          refine Finset.sum_congr rfl (fun χ _ => ?_)
          rfl
  simpa [hσ, hT] using hmain

end Work.ZeroFreeTables
