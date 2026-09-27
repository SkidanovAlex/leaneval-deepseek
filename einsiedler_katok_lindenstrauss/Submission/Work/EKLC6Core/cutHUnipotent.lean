import Mathlib
import Submission.Work.EKLC6Core.cutHDefs
import Submission.Work.EKLC6Core.uniform_contraction_horo

/-!
# `Work.EKLC6Core.cutHUnipotent`

A subgroup `U ≤ SL₃(ℝ)` contracted by the diagonal flow `aDiag t` (in the sense that
`aDiag t ^ n · u · (aDiag t ^ n)⁻¹ → 1` for every `u ∈ U`) consists of *unipotent* elements:
`(u - 1) ^ 3 = 0` for every `u ∈ U`.

**Argument.**  By `Work.EKLC6Core.uniform_contraction_horo` (the entry pattern forced by the
contraction hypothesis) every `u ∈ U` has identity entries in the non-strictly-contracted
directions: with `A = u - 1`,

`A i j = 0` whenever `t j ≤ t i`.

Thus a non-zero entry of `A` in position `(i,j)` forces `t i < t j`, so the support of `A` is
"strictly upper triangular" with respect to the weight function `t`.  Consequently every
non-zero term of the triple product `A³` would produce a chain of strict inequalities
`t i < t l < t k < t j`; but a function on `Fin 3` has only three values and can carry no
strictly increasing chain of length `4` (`no_chain_four`).  Hence `A³ = 0` entrywise.
-/

namespace Work.EKLC6Core

open Work.EKLContract

/-- **There is no strictly increasing chain of length `4` in `Fin 3`.**  A function
`t : Fin 3 → ℝ` cannot satisfy `t i < t l < t k < t j`.

The proof counts, for each `a`, the number of indices below `a`,
`n a = #{c | t c < t a}`; this is a strictly increasing function of `t a`, and `n a ≤ 2` because
`a` itself is never counted.  A chain of length `4` would give `n i < n l < n k < n j ≤ 2`, an
impossible chain of strict natural number inequalities. -/
lemma no_chain_four {t : Fin 3 → ℝ} {i l k j : Fin 3}
    (h1 : t i < t l) (h2 : t l < t k) (h3 : t k < t j) : False := by
  -- the count of indices below `a` is strictly increasing in `t a`
  have hmono : ∀ a b : Fin 3, t a < t b →
      (Finset.univ.filter (fun c => t c < t a)).card <
        (Finset.univ.filter (fun c => t c < t b)).card := by
    intro a b hab
    refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩)
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact lt_trans hc hab
    · intro heq
      have ha : a ∈ Finset.univ.filter (fun c => t c < t b) := by
        simp [hab]
      rw [← heq] at ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      exact absurd ha (lt_irrefl (t a))
  -- `a` is never counted among the indices below `a`, so the count is at most `2`
  have hle : ∀ a : Fin 3, (Finset.univ.filter (fun c => t c < t a)).card ≤ 2 := by
    intro a
    have hsub : Finset.univ.filter (fun c => t c < t a) ⊆ Finset.univ.erase a := by
      intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact fun h => absurd (h ▸ hc) (lt_irrefl (t a))
    calc (Finset.univ.filter (fun c => t c < t a)).card
        ≤ (Finset.univ.erase a).card := Finset.card_le_card hsub
      _ = 2 := by simp
  have h1' := hmono i l h1
  have h2' := hmono l k h2
  have h3' := hmono k j h3
  have h4' := hle j
  omega

theorem cutHUnipotent {U : Subgroup Work.EKLContract.SL3} {t : Fin 3 → ℝ}
    (hcontr : ∀ u ∈ U, Filter.Tendsto
      (fun n : ℕ => Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹)
      Filter.atTop (nhds 1)) :
    ∀ u ∈ U, ((u : Matrix (Fin 3) (Fin 3) ℝ) - 1) ^ 3 = 0 := by
  intro u hu
  -- The entry pattern: entries in the non-strictly-contracted directions are those of `1`.
  have hpat : ∀ i j : Fin 3, t i ≥ t j →
      (u : Matrix (Fin 3) (Fin 3) ℝ) i j = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j :=
    (uniform_contraction_horo hcontr).1 u hu
  set A : Matrix (Fin 3) (Fin 3) ℝ := (u : Matrix (Fin 3) (Fin 3) ℝ) - 1 with hAdef
  -- `A` vanishes on the "lower triangular" region `t j ≤ t i`.
  have hA : ∀ i j : Fin 3, t j ≤ t i → A i j = 0 := by
    intro i j hij
    have h := hpat i j hij
    rw [hAdef, Matrix.sub_apply, h, sub_self]
  -- Hence `A ^ 3 = 0`, the support being strictly upper triangular for the weight `t`.
  have hcube : A ^ 3 = 0 := by
    ext i j
    rw [pow_succ, pow_succ, pow_one, Matrix.zero_apply]
    simp only [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hkj : A k j = 0
    · simp [hkj]
    · -- the `k`-term of the outer sum vanishes as well
      have hsum : ∑ l, A i l * A l k = 0 := by
        refine Finset.sum_eq_zero fun l _ => ?_
        by_cases hil : A i l = 0
        · simp [hil]
        · by_cases hlk : A l k = 0
          · simp [hlk]
          · -- a non-zero product would give the forbidden chain `t i < t l < t k < t j`
            exfalso
            have htil : t i < t l := by
              by_contra h
              exact hil (hA i l (not_lt.mp h))
            have htlk : t l < t k := by
              by_contra h
              exact hlk (hA l k (not_lt.mp h))
            have htkj : t k < t j := by
              by_contra h
              exact hkj (hA k j (not_lt.mp h))
            exact no_chain_four htil htlk htkj
      rw [hsum, zero_mul]
  exact hcube

end Work.EKLC6Core
