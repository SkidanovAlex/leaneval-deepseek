import Mathlib
import Submission.Work.Diff.STE.flat.Sobolev
import Submission.Work.Diff.STE.flat.Sobolev.tsum_annulus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Summability of the dyadic block masses

The `(wt ·)^j`-weighted `ℓ²` mass of the whole coefficient family `γ` is the *sum over the dyadic
levels* of the block masses `blockMass j m γ`: the dyadic annuli `annulus m` partition the frequency
lattice `ℤ^ι` (`mem_annulus_annulusIdx`, `eq_annulusIdx_of_mem`), so the double family of weighted
masses is the pushforward of the total weighted mass along the injective map
`k ↦ (annulusIdx k, k)`.  Since all terms are nonnegative, a nonnegative-Tonelli argument converts
summability of the total mass into summability of the sequence `m ↦ blockMass j m γ`.
-/

namespace Work.Diff.STE.flat.Sobolev

open MeasureTheory BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The block of a family at an annulus containing the frequency is the family itself. -/
lemma blockFun_apply_mem {E : Type*} [Zero E] (g : (ι → ℤ) → E) {m : ℕ} {k : ι → ℤ}
    (hk : k ∈ annulus m) : blockFun m g k = g k := by
  classical
  simp only [blockFun]
  exact if_pos hk

/-- The `(wt ·)^j`-weighted mass of the `m`-th block, as the sum of the pointwise block of the
weighted mass family.  Both summands agree: on `annulus m` they are `(wt k)^j ‖γ k‖²`, and off it
they vanish. -/
lemma blockMass_eq_tsum_blockFun (j : ℝ) (m : ℕ) (γ : (ι → ℤ) → ℂ) :
    blockMass j m γ =
      ∑' k : ι → ℤ, blockFun m (fun k => (Work.Diff.STE.wt k) ^ j * ‖γ k‖ ^ 2) k := by
  classical
  rw [blockMass]
  refine tsum_congr fun k => ?_
  by_cases hk : k ∈ annulus m
  · rw [blockCoeff_apply_mem m γ hk, blockFun_apply_mem _ hk]
  · rw [blockCoeff_apply_not_mem m γ hk, blockFun_apply_of_not_mem _ hk, norm_zero]
    ring

theorem summable_blockMass {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ℝ) (γ : (ι → ℤ) → ℂ)
    (hM : Summable fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ j * ‖γ k‖ ^ 2) :
    Summable fun m : ℕ => Work.Diff.STE.flat.blockMass j m γ := by
  classical
  set g : (ι → ℤ) → ℝ := fun k => (Work.Diff.STE.wt k) ^ j * ‖γ k‖ ^ 2 with hgdef
  have hg : Summable g := hM
  -- the weighted mass is nonnegative
  have hgnn : ∀ k : ι → ℤ, 0 ≤ g k := fun k =>
    mul_nonneg (Real.rpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) j) (sq_nonneg _)
  have hfnn : ∀ p : ℕ × (ι → ℤ), 0 ≤ blockFun p.1 g p.2 := by
    rintro ⟨m, k⟩
    by_cases hk : k ∈ annulus m
    · rw [blockFun_apply_mem _ hk]; exact hgnn k
    · rw [blockFun_apply_of_not_mem _ hk]
  -- the double family is obtained from `g` by the injective map `k ↦ (annulusIdx k, k)`
  have hcomp : Summable (fun k : ι → ℤ => blockFun (annulusIdx k) g k) :=
    hg.congr fun k => (blockFun_apply_annulusIdx g k).symm
  have he : Function.Injective (fun k : ι → ℤ => (annulusIdx k, k)) :=
    fun _ _ hkl => congrArg Prod.snd hkl
  have hzero : ∀ p ∉ Set.range (fun k : ι → ℤ => (annulusIdx k, k)),
      blockFun p.1 g p.2 = 0 := by
    rintro ⟨m, k⟩ hp
    exact blockFun_apply_of_ne_annulusIdx (m := m) (k := k) g fun h =>
      hp ⟨k, by simp [h]⟩
  have hsum : Summable (fun p : ℕ × (ι → ℤ) => blockFun p.1 g p.2) :=
    (Function.Injective.summable_iff
      (f := fun p : ℕ × (ι → ℤ) => blockFun p.1 g p.2)
      (g := fun k : ι → ℤ => (annulusIdx k, k)) he hzero).mp hcomp
  -- nonnegative Tonelli: summability of the double family gives summability of the iterated sums
  have hout : Summable fun m : ℕ => ∑' k : ι → ℤ, blockFun m g k :=
    ((summable_prod_of_nonneg (f := fun p : ℕ × (ι → ℤ) => blockFun p.1 g p.2) hfnn).mp
      hsum).2
  exact hout.congr fun m => (blockMass_eq_tsum_blockFun j m γ).symm

end Work.Diff.STE.flat.Sobolev
