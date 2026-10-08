import Mathlib
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.linear_char_iff_deg_one
import Submission.Work.CharCore.exists_irr_of_monoidHom
import Submission.Work.CharCore.irrDeg_eq_one_of_commutative
import Submission.Work.CharCore.sum_irr_degree_sq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The number of irreducible characters of degree one

For a finite group `G`, the irreducible complex characters of degree one are exactly the
characters of the one-dimensional representations, i.e. the compositions `g ↦ (φ g : ℂ)` of a
monoid homomorphism `φ : G →* ℂˣ` with the inclusion `ℂˣ → ℂ`
(`Work.CharCore.linear_char_iff_deg_one`).  Since `ℂˣ` is abelian, such homomorphisms are the
same as homomorphisms out of the abelianisation `Abelianization G = G ⧸ [G, G]`; hence the
irreducible characters of degree one of `G` are exactly the inflations of the irreducible
characters of `G ⧸ [G, G]`.  As every irreducible character of an abelian group has degree one
(`Work.CharCore.irrDeg_eq_one_of_commutative`) and the sum of the squares of the degrees of the
irreducible characters equals the order of the group (`Work.CharCore.sum_irr_degree_sq`), the
abelian group `G ⧸ [G, G]` has exactly `|G ⧸ [G, G]|` irreducible characters.

## Main result

* `Work.CharCore.card_irr_deg_one`
-/

noncomputable section

open Classical

namespace Work.CharCore

variable {G : Type*} [Group G] [Fintype G]

/-- **The number of irreducible characters of degree one equals the order of the
abelianisation.** -/
theorem card_irr_deg_one {G : Type*} [Group G] [Fintype G] :
    ((Irr G).filter (fun χ => irrDeg χ = 1)).card = Nat.card (G ⧸ commutator G) := by
  classical
  haveI hfin : Finite (Abelianization G) :=
    Finite.of_surjective (Abelianization.of) QuotientGroup.mk_surjective
  haveI hfinA : Fintype (Abelianization G) := Fintype.ofFinite (Abelianization G)
  -- The invariant we use: the number of irreducible characters of `G ⧸ [G, G]`.
  have hab : ((Irr (Abelianization G)).card : ℂ) = (Nat.card (Abelianization G) : ℂ) := by
    have hdeg1 : ∀ χ ∈ Irr (Abelianization G), χ 1 ^ 2 = (1 : ℂ) := by
      intro χ hχ
      rw [irrDeg_spec hχ, irrDeg_eq_one_of_commutative hχ]
      norm_num
    have hsum : ∑ χ ∈ Irr (Abelianization G), χ 1 ^ 2 = ((Irr (Abelianization G)).card : ℂ) := by
      rw [Finset.sum_congr rfl hdeg1, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [← hsum, sum_irr_degree_sq]
  -- The degree-one irreducible characters of `G` are the inflations of the irreducible
  -- characters of `Abelianization G`.
  have hset : (Irr G).filter (fun χ => irrDeg χ = 1)
      = (Irr (Abelianization G)).image
          (fun χ : Abelianization G → ℂ => fun g : G => χ (Abelianization.of g)) := by
    apply Finset.ext
    intro χ
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hχ, hdeg⟩
      obtain ⟨φ, hφ⟩ := (linear_char_iff_deg_one hχ).mp hdeg
      obtain ⟨χ', hχ', hχ'eq⟩ := exists_irr_of_monoidHom (Abelianization.lift φ)
      exact ⟨χ', hχ', funext fun g => by
        rw [hχ'eq (Abelianization.of g), Abelianization.lift_apply_of φ g, hφ g]⟩
    · rintro ⟨χ', hχ', rfl⟩
      have hdeg' : irrDeg χ' = 1 := irrDeg_eq_one_of_commutative hχ'
      obtain ⟨ψ, hψ⟩ := (linear_char_iff_deg_one hχ').mp hdeg'
      have hchar : (fun g : G => χ' (Abelianization.of g))
          = fun g : G => ((ψ.comp (Abelianization.of)) g : ℂ) := by
        funext g
        rw [hψ (Abelianization.of g), MonoidHom.comp_apply]
      have hmem2 : (fun g : G => ((ψ.comp (Abelianization.of)) g : ℂ)) ∈ Irr G := by
        obtain ⟨χ₀, hχ₀, hχ₀eq⟩ := exists_irr_of_monoidHom (ψ.comp (Abelianization.of))
        rw [show (fun g : G => ((ψ.comp (Abelianization.of)) g : ℂ)) = χ₀ from
          funext fun g => (hχ₀eq g).symm]
        exact hχ₀
      refine ⟨?_, ?_⟩
      · rw [hchar]
        exact hmem2
      · rw [hchar]
        exact (linear_char_iff_deg_one hmem2).mpr ⟨ψ.comp (Abelianization.of), fun g => rfl⟩
  rw [hset, Finset.card_image_of_injective]
  · exact Nat.cast_inj.mp hab
  · intro χ₁ χ₂ h
    funext a
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
    exact congrFun h g

end Work.CharCore
