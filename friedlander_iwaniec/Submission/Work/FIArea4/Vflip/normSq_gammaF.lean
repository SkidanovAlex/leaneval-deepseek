/-
# The `ℓ²` norm of the flipped coefficients `γ' = gammaF γ`

The `r ↔ s` flip of the dyadic dual variance replaces the coefficient matrix `γ` by
`γ'_{b d} = [ (b,d)=1 ] γ_{b⁻¹ mod d, d} · (b | d')` (`gammaF`).  Since the Jacobi factor has
absolute value `1` and `a ↦ a⁻¹` permutes the reduced residue classes mod `d`, the flip is an
isometry of the `ℓ²` norm of the coefficient matrix:

`∑_{D<d≤2D} ∑_{a<d} |γ'_{a d}|² = ∑_{D<d≤2D} ∑_{a<d} |γ_{a d}|²`,

provided `γ_{a d} = 0` whenever `(a,d) ≠ 1` (the class sums are supported on the reduced
classes; here this is the hypothesis `hγ`).

This is used in `Wdyad_symm` to transfer the bound on `W(D)` for the flipped matrix back to `W(D)`.
-/
import Mathlib
import Submission.Work.FIArea4.Vflip.Wdyad_symm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4.Vflip

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The inverse of `a` in `ZMod d`, written through the canonical representative in `[0,d)`. -/
private def invIdx (d a : ℕ) : ℕ := ((a : ZMod d)⁻¹).val

/-- The Jacobi factor `(a | d')` has absolute value `1` when `(a,d) = 1`. -/
private lemma normSq_cast_jacobiSym (a d : ℕ) (h : Nat.Coprime a d) :
    Complex.normSq (((jacobiSym (a : ℤ) (Work.FIPlan.oddPart d) : ℤ) : ℂ)) = 1 := by
  have hcop' : Nat.Coprime a (Work.FIPlan.oddPart d) :=
    Nat.Coprime.coprime_dvd_right (oddPart_dvd_local d) h
  have hg : (a : ℤ).gcd ((Work.FIPlan.oddPart d : ℕ) : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]; exact hcop'
  rcases jacobiSym.eq_one_or_neg_one hg with hJ | hJ
  · rw [hJ]; norm_num
  · rw [hJ]; norm_num

/-- On the reduced classes, `|γ'_{a d}|² = |γ_{a⁻¹ mod d, d}|²`. -/
private lemma normSq_gammaF_of_coprime (γ : ℕ → ℕ → ℂ) {a d : ℕ} (h : Nat.Coprime a d) :
    Complex.normSq (gammaF γ a d) = Complex.normSq (γ (invIdx d a) d) := by
  rw [gammaF, if_pos h, Complex.normSq_mul, normSq_cast_jacobiSym a d h, mul_one]
  rfl

/-- Off the reduced classes, `γ'` vanishes. -/
private lemma normSq_gammaF_of_not_coprime (γ : ℕ → ℕ → ℂ) {a d : ℕ} (h : ¬ Nat.Coprime a d) :
    Complex.normSq (gammaF γ a d) = 0 := by
  rw [gammaF, if_neg h, Complex.normSq_zero]

/-- `a ↦ a⁻¹` maps reduced classes to reduced classes. -/
private lemma invIdx_coprime {d a : ℕ} [NeZero d] (h : Nat.Coprime a d) :
    Nat.Coprime (invIdx d a) d := by
  refine (ZMod.isUnit_iff_coprime (invIdx d a) d).mp ?_
  rw [show ((invIdx d a : ℕ) : ZMod d) = (a : ZMod d)⁻¹ from ZMod.natCast_zmod_val _]
  have hu : IsUnit (a : ZMod d) := (ZMod.isUnit_iff_coprime a d).mpr h
  obtain ⟨u, hu_eq⟩ := hu
  rw [← hu_eq, ZMod.inv_coe_unit]
  exact (u⁻¹).isUnit

/-- `a ↦ a⁻¹` is an involution on `0 ≤ a < d`, `(a,d) = 1`. -/
private lemma invIdx_invol {d a : ℕ} [NeZero d] (h : Nat.Coprime a d) (ha : a < d) :
    invIdx d (invIdx d a) = a := by
  have hu : IsUnit (a : ZMod d) := (ZMod.isUnit_iff_coprime a d).mpr h
  have h1 : (((invIdx d a : ℕ)) : ZMod d) = (a : ZMod d)⁻¹ := ZMod.natCast_zmod_val _
  have h2 : ((((invIdx d a : ℕ)) : ZMod d))⁻¹ = (a : ZMod d) := by
    rw [h1, ZMod.inv_eq_of_mul_eq_one d _ _ (ZMod.inv_mul_of_unit _ hu)]
  show ((((invIdx d a : ℕ)) : ZMod d)⁻¹).val = a
  rw [h2, ZMod.val_natCast, Nat.mod_eq_of_lt ha]

/-- The per-modulus identity: the `ℓ²` norm of the flipped column is unchanged. -/
private lemma sum_normSq_gammaF {d : ℕ} (hd : 0 < d) (γ : ℕ → ℕ → ℂ)
    (hγ : ∀ a, γ a d ≠ 0 → Nat.Coprime a d) :
    (∑ a ∈ Finset.range d, Complex.normSq (gammaF γ a d))
      = (∑ a ∈ Finset.range d, Complex.normSq (γ a d)) := by
  haveI : NeZero d := ⟨hd.ne'⟩
  set S : Finset ℕ := (Finset.range d).filter (fun a => Nat.Coprime a d) with hSdef
  have hSsub : S ⊆ Finset.range d := by
    intro a ha; rw [hSdef] at ha; exact (Finset.mem_filter.mp ha).1
  have hS1 : (∑ a ∈ S, Complex.normSq (gammaF γ a d))
      = ∑ a ∈ Finset.range d, Complex.normSq (gammaF γ a d) := by
    refine Finset.sum_subset hSsub (fun a ha hna => ?_)
    have hnc : ¬ Nat.Coprime a d := fun hc =>
      hna (by rw [hSdef]; exact Finset.mem_filter.mpr ⟨ha, hc⟩)
    exact normSq_gammaF_of_not_coprime γ hnc
  have hS2 : (∑ a ∈ S, Complex.normSq (gammaF γ a d))
      = ∑ a ∈ S, Complex.normSq (γ (invIdx d a) d) := by
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [hSdef] at ha
    exact normSq_gammaF_of_coprime γ (Finset.mem_filter.mp ha).2
  have hbij : (∑ a ∈ S, Complex.normSq (γ (invIdx d a) d))
      = ∑ a ∈ S, Complex.normSq (γ a d) := by
    refine Finset.sum_bij' (fun a _ => invIdx d a) (fun b _ => invIdx d b) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      rw [hSdef] at ha ⊢
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (ZMod.val_lt _), invIdx_coprime (Finset.mem_filter.mp ha).2⟩
    · intro b hb
      rw [hSdef] at hb ⊢
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (ZMod.val_lt _), invIdx_coprime (Finset.mem_filter.mp hb).2⟩
    · intro a ha
      rw [hSdef] at ha
      exact invIdx_invol (Finset.mem_filter.mp ha).2 (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
    · intro a ha
      rw [hSdef] at ha
      exact invIdx_invol (Finset.mem_filter.mp ha).2 (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
    · intro a _
      rfl
  have hS3 : (∑ a ∈ S, Complex.normSq (γ a d))
      = ∑ a ∈ Finset.range d, Complex.normSq (γ a d) := by
    refine Finset.sum_subset hSsub (fun a ha hna => ?_)
    have hnc : ¬ Nat.Coprime a d := fun hc =>
      hna (by rw [hSdef]; exact Finset.mem_filter.mpr ⟨ha, hc⟩)
    have hz : γ a d = 0 := by
      by_contra hc
      exact hnc (hγ a hc)
    rw [hz, Complex.normSq_zero]
  calc (∑ a ∈ Finset.range d, Complex.normSq (gammaF γ a d))
      = ∑ a ∈ S, Complex.normSq (gammaF γ a d) := hS1.symm
    _ = ∑ a ∈ S, Complex.normSq (γ (invIdx d a) d) := hS2
    _ = ∑ a ∈ S, Complex.normSq (γ a d) := hbij
    _ = ∑ a ∈ Finset.range d, Complex.normSq (γ a d) := hS3

theorem normSq_gammaF (D : ℕ) (γ : ℕ → ℕ → ℂ) (hγ : ∀ a d, γ a d ≠ 0 → Nat.Coprime a d) :
    (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d,
        Complex.normSq (Work.FIArea4.Vflip.gammaF γ a d))
      = (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d)) := by
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hdpos : 0 < d := by
    have := (Finset.mem_Ioc.mp hd).1
    omega
  exact sum_normSq_gammaF hdpos γ (fun a => hγ a d)

end

end Work.FIArea4.Vflip
