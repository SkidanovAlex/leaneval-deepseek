import Mathlib
import Submission.Commons.Combinatorics.Transference.cE_annulus_selfadjoint
import Submission.Commons.Combinatorics.Transference.cE_compl_orthogonal
import Submission.Commons.Combinatorics.Transference.cE_compl_restriction
import Submission.Commons.Combinatorics.Transference.sq_div_le_sum_sq_of_corr

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

/-- Summing over the complement of a finite set `s` equals the indicator-weighted sum over `univ`. -/
lemma sum_univ_sdiff_eq_indicator {X : Type*} [Fintype X] [DecidableEq X]
    (s : Finset X) (g : X → ℝ) :
    ∑ x ∈ Finset.univ \ s, g x = ∑ x, (if x ∈ s then (0 : ℝ) else g x) := by
  rw [Finset.sdiff_eq_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : x ∈ s <;> simp [h]

/-- **Energy increment with exceptional sets** (the Furstenberg tower step of Green–Tao
Proposition 7.2).  `P`, `Q` are finite σ-algebras on `X` given by their atoms, with `Q` refining
`P`; `Ω ⊆ Ω'`, where `Ω` is a union of `P`-atoms and `Ω'` a union of `Q`-atoms.  If `h` is
`Q`-measurable and bounded by `M > 0`, if `γ ≥ 0` is bounded by the pairing of the `Ω'`-residual
`f - 𝔼(f|P)` with `h`, if `𝔼(f|P)` is bounded by `B ≥ 0` outside `Ω`, and the annulus carries
little `(f - 𝔼(f|P))`-mass, then the `L²` energy of the conditional expectation increases when
passing from `P` to `Q`. -/
theorem energy_increment_exceptional {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (P Q : X → Finset X) (hPmem : ∀ x, x ∈ P x)
    (hPeq : ∀ x y : X, y ∈ P x → P y = P x) (hQmem : ∀ x, x ∈ Q x)
    (hQeq : ∀ x y : X, y ∈ Q x → Q y = Q x) (href : ∀ x, Q x ⊆ P x)
    {Ω Ω' : Finset X} (hΩsub : Ω ⊆ Ω') (hΩ : ∀ x ∈ Ω, P x ⊆ Ω)
    (hΩ' : ∀ x ∈ Ω', Q x ⊆ Ω')
    (f h : X → ℝ) (hh : ∀ x y : X, y ∈ Q x → h y = h x)
    {B M γ E : ℝ} (hM : 0 < M) (hγ0 : 0 ≤ γ) (hB0 : 0 ≤ B)
    (hA : ∀ x, x ∉ Ω → |((P x).card : ℝ)⁻¹ * (∑ y ∈ P x, f y)| ≤ B)
    (hhM : ∀ x, |h x| ≤ M)
    (hγ : γ ≤ |∑ x ∈ Finset.univ \ Ω',
        (f x - ((P x).card : ℝ)⁻¹ * (∑ y ∈ P x, f y)) * h x|)
    (hE : ∑ x ∈ Ω' \ Ω, |f x - ((P x).card : ℝ)⁻¹ * (∑ y ∈ P x, f y)| ≤ E) :
    ∑ x ∈ Finset.univ \ Ω, (((P x).card : ℝ)⁻¹ * (∑ y ∈ P x, f y)) ^ 2
        + γ ^ 2 / ((Fintype.card X : ℝ) * M ^ 2)
      ≤ ∑ x ∈ Finset.univ \ Ω', (((Q x).card : ℝ)⁻¹ * (∑ y ∈ Q x, f y)) ^ 2
        + B ^ 2 * ((Ω' \ Ω).card : ℝ) + 2 * B * E := by
  classical
  set a : X → ℝ := fun x => ((P x).card : ℝ)⁻¹ * (∑ y ∈ P x, f y) with ha
  set b : X → ℝ := fun x => ((Q x).card : ℝ)⁻¹ * (∑ y ∈ Q x, f y) with hb
  set U : Finset X := Finset.univ \ Ω with hU
  set T : Finset X := Finset.univ \ Ω' with hT
  set An : Finset X := Ω' \ Ω with hAn
  -- ## Hypotheses rewritten in terms of `a`, `b`
  have hγf : γ ≤ |∑ x ∈ T, (f x - a x) * h x| := by
    simpa only [hT, a] using hγ
  have hE' : ∑ x ∈ An, |f x - a x| ≤ E := by
    simpa only [hAn, a] using hE
  have hAb : ∀ x, x ∉ Ω → |a x| ≤ B := by
    intro x hx
    simpa only [a] using hA x hx
  -- ## Finset decompositions of `U`
  have hTU : T ⊆ U := by
    intro x hx
    simp only [hT, hU, Finset.mem_sdiff, Finset.mem_univ, true_and] at hx ⊢
    exact fun hxΩ => hx (hΩsub hxΩ)
  have hUT : U \ T = An := by
    ext x
    simp only [hT, hU, hAn, Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨not_not.mp h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, not_not.mpr h1⟩
  have hsplit : ∀ g : X → ℝ, ∑ x ∈ U, g x = ∑ x ∈ T, g x + ∑ x ∈ An, g x := by
    intro g
    rw [← Finset.sum_sdiff hTU, hUT, add_comm]
  -- ## Orthogonality of the residual over `U`
  have hortho : ∑ x ∈ U, a x * (b x - a x) = 0 := by
    have h0 : ∑ x ∈ Finset.univ \ Ω, a x * (b x - a x) = 0 := by
      rw [sum_univ_sdiff_eq_indicator Ω (fun x => a x * (b x - a x))]
      have hif : ∑ x, (if x ∈ Ω then (0 : ℝ) else a x * (b x - a x))
          = ∑ x, (if x ∈ Ω then (0 : ℝ) else 1) * (a x * (b x - a x)) := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases h : x ∈ Ω <;> simp [h]
      rw [hif]
      simpa only [a, b] using cE_compl_orthogonal P Q hPmem hPeq hQmem hQeq href hΩ f
    simpa only [hU] using h0
  -- ## The Pythagorean energy identity on `U`
  have hab : ∑ x ∈ U, a x * b x = ∑ x ∈ U, (a x) ^ 2 := by
    have h1 : ∑ x ∈ U, a x * b x = ∑ x ∈ U, (a x * a x + a x * (b x - a x)) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [h1, Finset.sum_add_distrib, hortho, add_zero]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have henergy : ∑ x ∈ U, (b x) ^ 2 = ∑ x ∈ U, (a x) ^ 2 + ∑ x ∈ U, (b x - a x) ^ 2 := by
    have key : ∑ x ∈ U, (b x - a x) ^ 2 = ∑ x ∈ U, (b x) ^ 2 - ∑ x ∈ U, (a x) ^ 2 := by
      have hpt : ∀ x, (b x - a x) ^ 2 = (b x) ^ 2 - 2 * (a x * b x) + (a x) ^ 2 :=
        fun x => by ring
      rw [Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, hab]
      ring
    linarith
  -- ## The annulus self-adjointness identity
  have hAnnulus : ∑ x ∈ An, a x * (b x - a x) = ∑ x ∈ An, a x * (f x - a x) := by
    rw [hAn]
    have hbpt : ∀ x, ((P x).card : ℝ)⁻¹ * (∑ y ∈ P x, f y * (b x - a x)) = a x * (b x - a x) := by
      intro x
      simp only [a]
      rw [← Finset.sum_mul]
      ring
    have hfpt : ∀ x, ((P x).card : ℝ)⁻¹ * (∑ y ∈ P x, f y * (f x - a x)) = a x * (f x - a x) := by
      intro x
      simp only [a]
      rw [← Finset.sum_mul]
      ring
    rw [show (∑ x ∈ Ω' \ Ω, a x * (b x - a x))
          = ∑ x ∈ Ω' \ Ω, ((P x).card : ℝ)⁻¹ * (∑ y ∈ P x, f y * (b x - a x)) from
          Finset.sum_congr rfl (fun x _ => (hbpt x).symm),
      show (∑ x ∈ Ω' \ Ω, a x * (f x - a x))
          = ∑ x ∈ Ω' \ Ω, ((P x).card : ℝ)⁻¹ * (∑ y ∈ P x, f y * (f x - a x)) from
          Finset.sum_congr rfl (fun x _ => (hfpt x).symm)]
    exact cE_annulus_selfadjoint P Q hPmem hPeq hQmem hQeq href hΩsub hΩ hΩ' f
  -- ## Bound on the `a`-energy of the annulus
  have hAab : ∑ x ∈ An, (a x) ^ 2 ≤ B ^ 2 * (An.card : ℝ) := by
    calc ∑ x ∈ An, (a x) ^ 2 ≤ ∑ x ∈ An, B ^ 2 := by
          apply Finset.sum_le_sum
          intro x hx
          have hxnot : x ∉ Ω := by
            rw [hAn] at hx
            exact (Finset.mem_sdiff.mp hx).2
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg (a x)) (hAb x hxnot) 2
      _ = B ^ 2 * (An.card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
  -- ## The mass bound `∑_An a·(f - a) ≤ B·E`
  have hEbound : ∑ x ∈ An, a x * (f x - a x) ≤ B * E := by
    calc ∑ x ∈ An, a x * (f x - a x)
        ≤ ∑ x ∈ An, |a x * (f x - a x)| :=
          Finset.sum_le_sum (fun x _ => le_abs_self _)
      _ = ∑ x ∈ An, |a x| * |f x - a x| := by
          apply Finset.sum_congr rfl
          intro x _
          rw [abs_mul]
      _ ≤ ∑ x ∈ An, B * |f x - a x| := by
          apply Finset.sum_le_sum
          intro x hx
          have hxnot : x ∉ Ω := by
            rw [hAn] at hx
            exact (Finset.mem_sdiff.mp hx).2
          exact mul_le_mul_of_nonneg_right (hAb x hxnot) (abs_nonneg _)
      _ = B * ∑ x ∈ An, |f x - a x| := by rw [Finset.mul_sum]
      _ ≤ B * E := mul_le_mul_of_nonneg_left hE' hB0
  -- ## Correlation bound on `T`
  have hcr : ∑ x ∈ T, (f x - a x) * h x = ∑ x ∈ T, (b x - a x) * h x := by
    simpa only [hT, a, b] using
      cE_compl_restriction P Q hPmem hPeq hQmem hQeq href hΩ' f h hh
  have hcorr : γ ^ 2 / ((Fintype.card X : ℝ) * M ^ 2) ≤ ∑ x ∈ T, (b x - a x) ^ 2 := by
    apply sq_div_le_sum_sq_of_corr (S := T) (f := fun x => b x - a x) (h := h) hM hγ0 hhM
    rw [← hcr]
    exact hγf
  -- ## The annulus algebraic relation
  have hpt1 : ∑ x ∈ An, (b x - a x) ^ 2
      = ∑ x ∈ An, (b x) ^ 2 - 2 * (∑ x ∈ An, a x * b x) + ∑ x ∈ An, (a x) ^ 2 := by
    rw [Finset.sum_congr rfl
      (fun x _ => by ring : ∀ x ∈ An,
        (b x - a x) ^ 2 = (b x) ^ 2 - 2 * (a x * b x) + (a x) ^ 2)]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hab2 : ∑ x ∈ An, a x * b x = ∑ x ∈ An, (a x) ^ 2 + ∑ x ∈ An, a x * (f x - a x) := by
    have h1 : ∑ x ∈ An, a x * b x = ∑ x ∈ An, (a x * a x + a x * (b x - a x)) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [h1, Finset.sum_add_distrib, hAnnulus]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hArel : (∑ x ∈ An, (b x - a x) ^ 2) - (∑ x ∈ An, (b x) ^ 2)
      = -(∑ x ∈ An, (a x) ^ 2) - 2 * (∑ x ∈ An, a x * (f x - a x)) := by
    rw [hpt1, hab2]; ring
  -- ## The final algebraic identity
  have hid : (∑ x ∈ T, (b x) ^ 2)
      = (∑ x ∈ U, (a x) ^ 2) + (∑ x ∈ T, (b x - a x) ^ 2)
        - (∑ x ∈ An, (a x) ^ 2) - 2 * (∑ x ∈ An, a x * (f x - a x)) := by
    have hb := hsplit (fun x => (b x) ^ 2)
    have hd := hsplit (fun x => (b x - a x) ^ 2)
    linarith [henergy, hb, hd, hArel]
  -- ## Combine
  have hkey : (∑ x ∈ U, (a x) ^ 2) + γ ^ 2 / ((Fintype.card X : ℝ) * M ^ 2)
      ≤ (∑ x ∈ T, (b x) ^ 2) + B ^ 2 * (An.card : ℝ) + 2 * B * E := by
    rw [hid]
    linarith [hcorr, hAab, hEbound]
  exact hkey

end Commons.Combinatorics.Transference
