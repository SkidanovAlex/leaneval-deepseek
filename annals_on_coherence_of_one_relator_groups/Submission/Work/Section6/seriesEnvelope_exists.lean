import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.SeriesEnvelope
import Submission.Work.ORHughesFree.NaturalExtension.SeriesP
import Submission.Work.ORHughesFree.NaturalExtension.exists_Psi
import Submission.Work.ORHughesFree.NaturalExtension.ultrafilterEnvelope_exists2
import Submission.Work.ORHughesFree.NaturalExtension.tok_injective

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.Section6

open Matrix Filter
open Work.ORHughesFree
open Work.ORHughesFree.NaturalExtension

/-- Auxiliary: the pointwise `∗` on `W U` sends the Toeplitz family of `p` to that of
`starSkewL p` (this is `starSkewL_toeplitz` read off coordinatewise). -/
theorem star_toeplitzFamily {U : Type} [Ring U] [StarRing U]
    [MulSemiringAction (Multiplicative ℤ) U] [StarAction U] (p : SkewL U) :
    star (toeplitzFamily p) = toeplitzFamily (starSkewL p) := by
  funext n
  exact (starSkewL_toeplitz (n + 1) p).symm

theorem seriesEnvelope_exists {U : Type} [Ring U] [StarRing U]
    [Work.ORHughesFree.IsStarRegular U]
    [MulSemiringAction (Multiplicative ℤ) U]
    (hpos : Work.ORHughesFree.IsPositiveDefiniteStarRegular U)
    (rk : Work.ORHughesFree.SylvesterRank U) (hrk : rk.IsFaithful)
    (hstar : ∀ (n : Multiplicative ℤ) (x : U), star (n • x) = n • star x)
    (hτ : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) U),
      rk.rk n m (A.map (fun a => (Multiplicative.ofAdd (1 : ℤ)) • a)) = rk.rk n m A)
    (rkE : Work.ORHughesFree.SylvesterRank (SkewMonoidAlgebra U (Multiplicative ℤ)))
    (h : Work.ORHughesFree.IsNaturalExtension rk rkE) :
    Nonempty (Work.ORHughesFree.NaturalExtension.SeriesEnvelope (U := U) hpos rk hstar hτ rkE) := by
  classical
  haveI hSA : StarAction U := ⟨hstar⟩
  obtain ⟨ω, hω⟩ := exists_ultrafilter_le_atTop
  obtain ⟨hW_star, hW_pd⟩ := productStarRegular (U := U) hpos
  haveI : IsStarRegular (W U) := hW_star
  haveI : IsPositiveDefiniteStarRegular (W U) := hW_pd
  have hI_star : ∀ x ∈ SPideal ω rk, star x ∈ SPideal ω rk :=
    fun x hx => star_mem_of_mem_ideal (SPideal ω rk) hx
  letI : StarRing (SP ω rk) := starRingQuotient (SPideal ω rk) hI_star
  obtain ⟨hP_star, hP_pd⟩ := starRegularQuotient (R := W U) hW_pd (SPideal ω rk) hI_star
  haveI : IsStarRegular (SP ω rk) := hP_star
  haveI : IsPositiveDefiniteStarRegular (SP ω rk) := hP_pd
  -- The series map `Ψ` and the polynomial map `Φ = Ψ ∘ (−↦t^{±1})`.
  let Ψ : SkewLaurentSeries U →+* SP ω rk := psiHom ω hω rk
  let Φ : SkewL U →+* SP ω rk := Ψ.comp SkewLaurentSeries.toRingHom
  have hη : ∀ q : SkewL U, Φ q = mkSP ω rk (toeplitzFamily q) := by
    intro q
    show mkSP ω rk (tok (SkewLaurentSeries.toRingHom q)) = mkSP ω rk (toeplitzFamily q)
    rw [tok_toRingHom_eq_toeplitzFamily q]
  -- ## The two defining clauses of the natural extension for `Φ`
  have hmat_const : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) U),
      (skewLaurentConst n m A).map Φ = (A.map toeplitzConstHom).map (mkSP ω rk) := by
    intro n m A
    ext i j
    show Φ (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) (A i j)) =
      mkSP ω rk (toeplitzConstHom (A i j))
    rw [hη]
    rfl
  have hnatural_const : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) U),
      (SylvesterRank.pullback Φ (rkSP ω rk)).rk n m (skewLaurentConst n m A) = rk.rk n m A := by
    intro n m A
    show (rkSP ω rk).rk n m ((skewLaurentConst n m A).map Φ) = rk.rk n m A
    rw [hmat_const n m A, rkSP_apply_mk ω rk n m (A.map toeplitzConstHom),
      rkAmp_apply ω rk n m (A.map toeplitzConstHom), blimRank]
    have hflat : ∀ k : ℕ, flatW n m (A.map toeplitzConstHom) k =
        trunc (k+1) (skewLaurentConst n m A) := by
      intro k
      have h1 : A.map toeplitzConstHom = toeplitzMatrix (skewLaurentConst n m A) := by
        ext i j; rfl
      rw [h1]
      exact flatW_toeplitzMatrix (skewLaurentConst n m A) k
    have hev : ∀ᶠ k in Filter.atTop,
        rk.rk (n * (k+1)) (m * (k+1)) (flatW n m (A.map toeplitzConstHom) k) /
            ((k+1 : ℕ) : ℝ) = rk.rk n m A := by
      filter_upwards with k
      rw [hflat k, rk_trunc_skewLaurentConst_univ rk hτ A (k+1)]
      have hk : (((k+1 : ℕ)) : ℝ) ≠ 0 := by positivity
      field_simp
    rw [blim_congr ω hω hev, blim_const ω (rk.rk n m A)]
  have hmat_onePlus : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) U),
      (onePlusAt n A).map Φ = (toeplitzMatrix (onePlusAt n A)).map (mkSP ω rk) := by
    intro n A
    ext i j
    show Φ ((onePlusAt n A) i j) = mkSP ω rk (toeplitzMatrix (onePlusAt n A) i j)
    rw [hη]
    rfl
  have hnatural_onePlus : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) U),
      (SylvesterRank.pullback Φ (rkSP ω rk)).rk n n (onePlusAt n A) = n := by
    intro n A
    show (rkSP ω rk).rk n n ((onePlusAt n A).map Φ) = (n : ℝ)
    rw [hmat_onePlus n A, rkSP_apply_mk ω rk n n (toeplitzMatrix (onePlusAt n A)),
      rkAmp_apply ω rk n n (toeplitzMatrix (onePlusAt n A)), blimRank]
    have hev : ∀ᶠ k in Filter.atTop,
        rk.rk (n * (k+1)) (n * (k+1)) (flatW n n (toeplitzMatrix (onePlusAt n A)) k) /
            ((k+1 : ℕ) : ℝ) = (n : ℝ) := by
      filter_upwards with k
      rw [flatW_toeplitzMatrix, rk_trunc_onePlusAt_univ rk A (k+1)]
      have hk : (((k+1 : ℕ)) : ℝ) ≠ 0 := by positivity
      field_simp
    rw [blim_congr ω hω hev, blim_const ω (n : ℝ)]
  have hnatural : IsNaturalExtension rk (SylvesterRank.pullback Φ (rkSP ω rk)) :=
    ⟨hnatural_const, hnatural_onePlus⟩
  -- ## The remaining properties of `Φ` and `Ψ`
  have hrank : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) (SkewL U)),
      rkE.rk n m A = (rkSP ω rk).rk n m (A.map Φ) := by
    intro n m A
    rw [naturalExtension_unique rk hτ h hnatural n m A]
    rfl
  have hΦ_star : ∀ p : SkewL U, Φ (starSkewL p) = star (Φ p) := by
    intro p
    show Φ (starSkewL p) = starQuot (SPideal ω rk) (Φ p)
    rw [hη (starSkewL p), hη p, starQuot_mk (SPideal ω rk) hI_star (toeplitzFamily p),
      star_toeplitzFamily p]
  have hΦ_inj : Function.Injective Φ := by
    intro p q hpq
    by_contra hne
    have hne' : p - q ≠ 0 := sub_ne_zero.mpr hne
    have h2 : SkewLaurentSeries.toRingHom (p - q) ≠ 0 :=
      fun h0 => hne' (SkewLaurentSeries.toRingHom_injective h0)
    have hz : mkSP ω rk (tok (SkewLaurentSeries.toRingHom (p - q))) = 0 := by
      have h3 : Φ (p - q) = 0 := by rw [map_sub, hpq, sub_self]
      exact h3
    exact tok_injective ω hω rk hrk hτ _ h2 hz
  have hΨ_inj : Function.Injective Ψ := by
    intro p q hpq
    by_contra hne
    have hz : mkSP ω rk (tok (p - q)) = 0 := by
      have h3 : Ψ (p - q) = 0 := by rw [map_sub, hpq, sub_self]
      exact h3
    exact tok_injective ω hω rk hrk hτ _ (sub_ne_zero.mpr hne) hz
  exact ⟨
    { P := SP ω rk
      ringP := inferInstance
      starP := inferInstance
      isStarRegularP := hP_star
      positiveDefiniteP := hP_pd
      rkP := rkSP ω rk
      faithfulP := rkSP_faithful ω rk
      fω := Φ
      fω_star := hΦ_star
      fω_injective := hΦ_inj
      rank_compat := hrank
      Ψ := Ψ
      Ψ_extends := fun p => rfl
      Ψ_injective := hΨ_inj }⟩

end Work.Section6
