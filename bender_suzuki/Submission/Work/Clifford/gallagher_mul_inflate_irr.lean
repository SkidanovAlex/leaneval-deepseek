import Mathlib
import Submission.Work.Clifford.Orbit
import Submission.Work.Clifford.gallagher_isometry
import Submission.Work.Clifford.simple_of_finrank_hom_self_eq_one
import Submission.Work.Clifford.cfInner_eq_ite_of_mem_Irr
import Submission.Work.CharCore.vchar_norm_one
import Submission.Work.CharCore.isVChar_mul
import Submission.Work.CharCore.isChar_mul
import Submission.Work.CharCore.mem_Irr_iff_fdrep
import Submission.Work.CharCore.isChar_character

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Clifford.gallagher_mul_inflate_irr`

**Gallagher's theorem, one half** (Isaacs, *Character Theory of Finite Groups*, 6.17): if
`N ⊴ G`, `θ ∈ Irr N` extends to `χ ∈ Irr G`, and `β ∈ Irr(G ⧸ N)` is irreducible on the
quotient, then the product `χ · Inf β` is again irreducible.

The argument has two ingredients.

* `χ · Inf β` is a genuine character, hence a virtual character: `χ` is the character of a
  simple representation, and `Inf β` is the character of the inflation of the simple
  representation of `G ⧸ N` affording `β` along the quotient map `G →* G ⧸ N`; the pointwise
  product of characters is a character (`Work.CharCore.isChar_mul`).

* Its norm is `⟪β, β⟫ = 1`, by Gallagher's isometry
  (`Work.Clifford.gallagher_isometry`) and the orthonormality of the irreducible characters of
  `G ⧸ N` (`Work.Clifford.cfInner_eq_ite_of_mem_Irr`).

A virtual character of norm one is `±` an irreducible character
(`Work.CharCore.vchar_norm_one`); the minus sign is excluded by evaluating at `1`, where
`(χ · Inf β) 1 = χ 1 · β 1` is a positive real number whereas `-ψ 1` is negative for any
irreducible `ψ`.
-/

noncomputable section

open Classical

namespace Work.Clifford

/-- `Work.Clifford.Irr` and `Work.CharCore.Irr` are the same set of functions. -/
theorem mem_Irr_charCore_iff' {G : Type*} [Group G] [Fintype G] {χ : G → ℂ} :
    χ ∈ Work.Clifford.Irr G ↔ χ ∈ Work.CharCore.Irr G :=
  (Work.Clifford.mem_Irr).trans (Work.CharCore.mem_Irr_iff_fdrep χ).symm

/-- The inflation to `G` of a finite dimensional complex representation of `G ⧸ N`, obtained by
composing with the quotient map `G →* G ⧸ N`. -/
def inflateRep {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (V : FDRep ℂ (G ⧸ N)) : FDRep ℂ G :=
  FDRep.of (V.ρ.comp (QuotientGroup.mk' N))

/-- The character of the inflated representation is the inflation of the character. -/
theorem inflateRep_character {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (V : FDRep ℂ (G ⧸ N)) :
    (inflateRep (N := N) V).character = Work.Clifford.inflateFun N V.character := by
  funext g
  show V.character (QuotientGroup.mk' N g) = V.character (QuotientGroup.mk g)
  rfl

/-- The inflation of an irreducible character of `G ⧸ N` is a character of `G`. -/
theorem isChar_inflateFun {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [N.Normal]
    [Fintype (G ⧸ N)] {β : G ⧸ N → ℂ} (hβ : β ∈ Work.Clifford.Irr (G ⧸ N)) :
    Work.CharCore.IsChar (Work.Clifford.inflateFun N β) := by
  obtain ⟨V, _hV, hVβ⟩ := Work.Clifford.mem_Irr.mp hβ
  have hchar : (inflateRep (N := N) V).character = Work.Clifford.inflateFun N β := by
    rw [inflateRep_character (N := N) V, hVβ]
  rw [← hchar]
  exact Work.CharCore.isChar_character _

/-- **Gallagher's theorem** (`Irr`-side): if `N ⊴ G`, `θ ∈ Irr N` extends to `χ ∈ Irr G`, and
`β ∈ Irr(G ⧸ N)`, then `χ · Inf β ∈ Irr G`. -/
theorem gallagher_mul_inflate_irr {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [N.Normal] [Fintype N]
    [Fintype (G ⧸ N)]
    {θ : N → ℂ} (hθ : θ ∈ Work.Clifford.Irr N) {χ : G → ℂ} (hχ : χ ∈ Work.Clifford.Irr G)
    (hext : Work.Clifford.Extends N χ θ) {β : G ⧸ N → ℂ} (hβ : β ∈ Work.Clifford.Irr (G ⧸ N)) :
    χ * Work.Clifford.inflateFun N β ∈ Work.Clifford.Irr G := by
  -- `χ · Inf β` is a virtual character
  have hVχ : Work.CharCore.IsVChar χ := Work.CharCore.IsVChar.of_mem_Irr ((mem_Irr_charCore_iff').mp hχ)
  have hVβ : Work.CharCore.IsVChar (Work.Clifford.inflateFun N β) :=
    Work.CharCore.IsChar.toVChar (isChar_inflateFun hβ)
  have hV : Work.CharCore.IsVChar (χ * Work.Clifford.inflateFun N β) :=
    Work.CharCore.isVChar_mul hVχ hVβ
  -- its norm is `⟪β, β⟫ = 1`, by Gallagher's isometry
  have hnorm : Work.CharCore.cfInner (χ * Work.Clifford.inflateFun N β)
      (χ * Work.Clifford.inflateFun N β) = 1 := by
    have h1 : Work.Clifford.cfInner (χ * Work.Clifford.inflateFun N β)
        (χ * Work.Clifford.inflateFun N β) = 1 := by
      rw [Work.Clifford.gallagher_isometry (N := N) hθ hχ hext β β,
        Work.Clifford.cfInner_eq_ite_of_mem_Irr hβ hβ]
      simp
    exact h1
  obtain ⟨ψ, hψ, hcase⟩ := Work.CharCore.vchar_norm_one hV hnorm
  rcases hcase with h | h
  · rw [h]; exact (mem_Irr_charCore_iff').mpr hψ
  · -- the sign is positive: `(χ · Inf β) 1 = χ 1 · β 1 > 0`
    exfalso
    have hf1 : (χ * Work.Clifford.inflateFun N β) 1
        = ((Work.CharCore.irrDeg χ : ℂ) * (Work.CharCore.irrDeg β : ℂ)) := by
      rw [Pi.mul_apply]
      show χ 1 * β (QuotientGroup.mk (1 : G))
        = ((Work.CharCore.irrDeg χ : ℂ) * (Work.CharCore.irrDeg β : ℂ))
      rw [QuotientGroup.mk_one N,
        Work.CharCore.irrDeg_spec ((mem_Irr_charCore_iff').mp hχ),
        Work.CharCore.irrDeg_spec ((mem_Irr_charCore_iff').mp hβ)]
    have hreal : (Work.CharCore.irrDeg χ : ℝ) * (Work.CharCore.irrDeg β : ℝ)
        = -(Work.CharCore.irrDeg ψ : ℝ) := by
      have h2 : ((Work.CharCore.irrDeg χ : ℂ) * (Work.CharCore.irrDeg β : ℂ))
          = -(Work.CharCore.irrDeg ψ : ℂ) := by
        rw [← hf1, h]
        show -(ψ 1) = -(Work.CharCore.irrDeg ψ : ℂ)
        rw [Work.CharCore.irrDeg_spec hψ]
      have := congrArg Complex.re h2
      simpa using this
    have hpχ : (0 : ℝ) < (Work.CharCore.irrDeg χ : ℝ) :=
      Work.CharCore.irrDeg_pos' ((mem_Irr_charCore_iff').mp hχ)
    have hpβ : (0 : ℝ) < (Work.CharCore.irrDeg β : ℝ) :=
      Work.CharCore.irrDeg_pos' ((mem_Irr_charCore_iff').mp hβ)
    have hpψ : (0 : ℝ) < (Work.CharCore.irrDeg ψ : ℝ) := Work.CharCore.irrDeg_pos' hψ
    nlinarith [mul_pos hpχ hpβ]

end Work.Clifford
