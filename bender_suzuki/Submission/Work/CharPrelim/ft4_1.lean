import Mathlib
import Submission.Work.CharPrelim.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.CharPrelim.ft4_1`: FT 4.1, `λ(1)^2 ≤ [X : Z(X)]`

Feit--Thompson, *Solvability of groups of odd order*, Pacific J. Math. **13** (1963), Lemma 4.1
(p. 783): for a finite group `X` with centre `Z = Z(X)` and an irreducible complex character
`λ ∈ Irr X`,

`λ(1)^2 ≤ [X : Z]`.

## The mathematics

Two ingredients enter.

* **`‖χ z‖ = χ(1)` for `z` central.**  Column orthogonality at `z`
  (`Work.CharCore.column_orthogonality_conj`) gives `∑_χ ‖χ z‖^2 = |C_X(z)| = |X|` because
  `z` is central, while `∑_χ χ(1)^2 = |X|` (`Work.CharCore.sum_irr_degree_sq`).  Termwise
  `‖χ z‖ ≤ χ(1)` (`Work.CharCore.norm_char_le`), so every term is equal.  This is
  `normSq_eq_irrDeg_sq_of_mem_center` / `norm_char_eq_irrDeg_of_mem_center` below.
* **The norm identity `∑_x ‖χ x‖^2 = |X|`.**  This is `⟨χ, χ⟩ = 1`
  (`Work.CharCore.irr_orthonormal`) read in the definition of `Work.CharCore.cfInner`:
  `cfInner χ χ = |X|⁻¹ ∑_x ‖χ x‖^2 ∈ ℂ` (`sum_normSq_eq_card` below).

Then `|Z| · λ(1)^2 = ∑_{z ∈ Z} ‖λ z‖^2 ≤ ∑_{x ∈ X} ‖λ x‖^2 = |X|`, and dividing by
`|Z| > 0` while `|X| = |Z| · [X : Z]` (`Subgroup.index_mul_card`) gives the claim.
-/

noncomputable section

set_option linter.style.haveILetI false

open Classical

namespace Work.CharPrelim

variable {X : Type*} [Group X] [Fintype X]

/-- **The norm identity for an irreducible character.**  The `cfInner` of an irreducible
character with itself is `1` (`Work.CharCore.irr_orthonormal`), i.e.
`|X|⁻¹ ∑_x ‖χ x‖^2 = 1`; multiplying by `|X|` (after replacing the `Fintype.card` occurring in
`cfInner` by `Nat.card`) gives `∑_x ‖χ x‖^2 = |X|`. -/
theorem sum_normSq_eq_card {χ : X → ℂ} (hχ : χ ∈ Work.CharCore.Irr X) :
    ∑ x : X, ‖χ x‖ ^ 2 = (Nat.card X : ℝ) := by
  have h1 : Work.CharCore.cfInner χ χ = 1 := Work.CharCore.cfInner_self_mem_Irr hχ
  have hcard_ne : (Nat.card X : ℂ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h2 : Work.CharCore.cfInner χ χ
      = (Nat.card X : ℂ)⁻¹ * ∑ x : X, ((‖χ x‖ ^ 2 : ℝ) : ℂ) := by
    rw [Work.CharCore.cfInner, Fintype.card_eq_nat_card]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h3 : (Nat.card X : ℂ)⁻¹ * (∑ x : X, ((‖χ x‖ ^ 2 : ℝ) : ℂ)) = 1 := by
    rw [← h2]; exact h1
  have hS : (∑ x : X, ((‖χ x‖ ^ 2 : ℝ) : ℂ)) = (Nat.card X : ℂ) := by
    have hh := congrArg (fun t => (Nat.card X : ℂ) * t) h3
    rw [mul_one, ← mul_assoc, mul_inv_cancel₀ hcard_ne, one_mul] at hh
    exact hh
  have h2' : ((∑ x : X, ‖χ x‖ ^ 2 : ℝ) : ℂ) = (Nat.card X : ℂ) := by
    rw [Complex.ofReal_sum]; exact hS
  exact Complex.ofReal_inj.mp h2'

/-- Transport a sum of real numbers out of `ℂ`: if the `ℂ`-valued sum of the casts of
`f : ι → ℝ` over `s` equals the natural number `c`, then the real sum equals `c`. -/
theorem ofReal_finset_sum_eq {ι : Type*} (s : Finset ι) (f : ι → ℝ) (c : ℕ)
    (h : (∑ i ∈ s, ((f i : ℝ) : ℂ)) = (c : ℂ)) : ∑ i ∈ s, f i = (c : ℝ) := by
  have h2 : ((∑ i ∈ s, f i : ℝ) : ℂ) = ((c : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, h, Complex.ofReal_natCast]
  exact Complex.ofReal_inj.mp h2

/-- **The value of an irreducible character at a central element.**  For `z ∈ Z(X)` the value
`χ z` has modulus exactly the degree `χ(1)`.

Column orthogonality at `z` and `∑_χ χ(1)^2 = |X|` show that
`∑_χ ‖χ z‖^2 = ∑_χ χ(1)^2 = |X|`; since `‖χ z‖ ≤ χ(1)` termwise, all terms coincide. -/
theorem normSq_eq_irrDeg_sq_of_mem_center {χ : X → ℂ} (hχ : χ ∈ Work.CharCore.Irr X) {z : X}
    (hz : z ∈ Subgroup.center X) :
    (‖χ z‖ ^ 2 : ℝ) = ((Work.CharCore.irrDeg χ : ℝ)) ^ 2 := by
  have hcent : Subgroup.centralizer ({z} : Set X) = ⊤ := by
    rw [Subgroup.centralizer_eq_top_iff_subset]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]; exact hz
  -- `∑_χ ‖χ z‖^2 = |X|`, from column orthogonality at the central element `z`
  have hAℂ : (∑ ψ ∈ Work.CharCore.Irr X, ((‖ψ z‖ ^ 2 : ℝ) : ℂ)) = (Nat.card X : ℂ) := by
    have hcol := Work.CharCore.column_orthogonality_conj (G := X) (IsConj.refl z)
    rw [hcent, Subgroup.card_top] at hcol
    rw [← hcol]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hA := ofReal_finset_sum_eq (Work.CharCore.Irr X) (fun ψ => ‖ψ z‖ ^ 2) (Nat.card X) hAℂ
  -- `∑_χ χ(1)^2 = |X|`, from `sum_irr_degree_sq`
  have hBℂ : (∑ ψ ∈ Work.CharCore.Irr X,
      Complex.ofReal (((Work.CharCore.irrDeg ψ : ℝ)) ^ 2)) = (Nat.card X : ℂ) := by
    rw [← Work.CharCore.sum_irr_degree_sq]
    refine Finset.sum_congr rfl fun ψ hψ => ?_
    rw [Work.CharCore.irrDeg_spec hψ, Complex.ofReal_pow, Complex.ofReal_natCast]
  have hB := ofReal_finset_sum_eq (Work.CharCore.Irr X)
    (fun ψ => ((Work.CharCore.irrDeg ψ : ℝ)) ^ 2) (Nat.card X) hBℂ
  -- termwise `‖ψ z‖ ≤ ψ(1)`
  have hle : ∀ ψ ∈ Work.CharCore.Irr X,
      (‖ψ z‖ ^ 2 : ℝ) ≤ ((Work.CharCore.irrDeg ψ : ℝ)) ^ 2 := by
    intro ψ hψ
    exact pow_le_pow_left₀ (norm_nonneg _) (Work.CharCore.norm_char_le hψ z) 2
  exact (Finset.sum_eq_sum_iff_of_le hle).mp (hA.trans hB.symm) χ hχ

/-- **Companion of FT 4.1: `χ` has constant modulus `χ(1)` on the centre.**  Immediate from
`normSq_eq_irrDeg_sq_of_mem_center` since both `‖χ z‖` and `χ(1)` are nonnegative. -/
theorem norm_char_eq_irrDeg_of_mem_center {χ : X → ℂ} (hχ : χ ∈ Work.CharCore.Irr X) {z : X}
    (hz : z ∈ Subgroup.center X) :
    ‖χ z‖ = (Work.CharCore.irrDeg χ : ℝ) := by
  have h := normSq_eq_irrDeg_sq_of_mem_center hχ hz
  have h1 : |‖χ z‖| = |(Work.CharCore.irrDeg χ : ℝ)| :=
    (sq_eq_sq_iff_abs_eq_abs _ _).mp h
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)] at h1

/-- FT 4.1: `λ(1)^2 ≤ [X : Z(X)]` for `λ ∈ Irr X`.
Proof route: (1) for `z ∈ Subgroup.center X`, `‖λ z‖ = irrDeg λ`, because column orthogonality with `g = h = z` gives `∑ χ ∈ Irr X, ‖χ z‖^2 = |C_X(z)| = |X|` while `∑ χ ∈ Irr X, (irrDeg χ)^2 = |X|` (`sum_irr_degree_sq`) and `‖χ z‖ ≤ irrDeg χ` termwise (`norm_char_le`), so each term is equal; (2) `(irrDeg λ)^2 * |Z| = ∑_{z ∈ Z} ‖λ z‖^2 ≤ ∑_{x : X} ‖λ x‖^2 ≤ |X| * (irrDeg λ)^2`; (3) conclude `(irrDeg λ)^2 ≤ (Subgroup.center X).index = |X| / |Z|`. -/
theorem ft4_1 {X : Type*} [Group X] [Fintype X] {χ : X → ℂ} (hχ : χ ∈ Work.CharCore.Irr X) :
    Work.CharCore.irrDeg χ ^ 2 ≤ (Subgroup.center X).index := by
  have hsumX : (∑ x : X, (‖χ x‖ ^ 2 : ℝ)) = (Nat.card X : ℝ) := sum_normSq_eq_card hχ
  -- `|Z| · χ(1)^2 ≤ |X|`, by summing the central values and bounding by the whole group
  have hbound : (Nat.card ↥(Subgroup.center X) : ℝ) * ((Work.CharCore.irrDeg χ : ℝ)) ^ 2
      ≤ (Nat.card X : ℝ) := by
    have hcmp : (∑ z : ↥(Subgroup.center X), (‖χ (z : X)‖ ^ 2 : ℝ))
        ≤ ∑ x : X, (‖χ x‖ ^ 2 : ℝ) := by
      rw [← Finset.sum_subtype (s := Finset.univ.filter (fun x : X => x ∈ Subgroup.center X))
            (by intro x; simp) (f := fun x : X => (‖χ x‖ ^ 2 : ℝ))]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun x _ _ => by positivity)
    have hsumZ : (∑ z : ↥(Subgroup.center X), (‖χ (z : X)‖ ^ 2 : ℝ))
        = (Nat.card ↥(Subgroup.center X) : ℝ) * ((Work.CharCore.irrDeg χ : ℝ)) ^ 2 := by
      rw [Finset.sum_congr rfl (fun z (_ : z ∈ Finset.univ) =>
            normSq_eq_irrDeg_sq_of_mem_center hχ z.2)]
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ← Nat.card_eq_fintype_card]
    rw [hsumZ, hsumX] at hcmp
    exact hcmp
  -- the same inequality in `ℕ`
  have hnat : Nat.card ↥(Subgroup.center X) * Work.CharCore.irrDeg χ ^ 2 ≤ Nat.card X := by
    have hcast : ((Nat.card ↥(Subgroup.center X) * Work.CharCore.irrDeg χ ^ 2 : ℕ) : ℝ)
        ≤ (Nat.card X : ℝ) := by
      push_cast
      exact hbound
    exact_mod_cast hcast
  haveI : Nonempty ↥(Subgroup.center X) := ⟨1, Subgroup.one_mem _⟩
  have hpos : 0 < Nat.card ↥(Subgroup.center X) := Nat.card_pos
  -- cancel the positive factor `|Z|` from `χ(1)^2 · |Z| ≤ |X| = [X : Z] · |Z|`
  have h2 : Work.CharCore.irrDeg χ ^ 2 * Nat.card ↥(Subgroup.center X)
      ≤ (Subgroup.center X).index * Nat.card ↥(Subgroup.center X) := by
    rw [Subgroup.index_mul_card, Nat.mul_comm]
    exact hnat
  exact Nat.le_of_mul_le_mul_right h2 hpos

end Work.CharPrelim
