import Mathlib
import Submission.Work.BG.hatInjCongruentEq
import Submission.Work.BG.HatInjDefs
import Submission.Work.BG.Thm43Defs

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.GW2.C16 Work.GW2.C23 Subgroup

/-- **Uniqueness of `ν̂`** for an arbitrary class function `ν` of `H₀`.

Any two irreducible characters `θ`, `θ'` of `B` which are both `≡ ν (mod 2)` on
`B` (the `HatOf` relation) coincide.  The point is that the `HatOf` conditions are
available at *every* element of `B`: since `B = B₁ ⊓ B₂ ≤ U = C.P.U ≤ H₀`, every
`b : ↥D.B` has an underlying element lying in `C.P.H0`, so `HatOf` gives
`θ b ≡ ν h ≡ θ' b (mod 2)`; `B` has odd order (`B ≤ U`, and `U = O(H)` is odd),
so the two-character form of Bender–Glauberman Lemma 1.8
(`Work.BG.hatInjCongruentEq`) applies.

(Compared with `Work.BG.Hat`, which proves the same uniqueness inside `HatProp`,
no hypothesis `D.n = 2` or `ν ∈ 𝒮₄(C)` is needed: those are only used there to
identify `C_U(σ)` with `B` for the existence half.) -/
theorem HatUniq {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G)
    (hc : Work.GW2.C16.Compat D C)
    (ν : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ) :
    ∀ θ θ' : OddOrder.RepresentationTheory.ClassFunction ↥D.B ℂ,
      Work.GW2.C23.HatOf D C ν θ → Work.GW2.C23.HatOf D C ν θ' → θ = θ' := by
  intro θ θ' hθ hθ'
  haveI : Fintype ↥D.B := Fintype.ofFinite _
  refine hatInjCongruentEq (K := ↥D.B) ?_ hθ.1 hθ'.1 ?_
  · -- `B ≤ U` and `U` has odd order
    have hBU : D.B ≤ C.P.U := fun x hx => by rw [hc.U_eq]; exact hx.1.1
    exact Odd.of_dvd_nat (odd_card_U_of_compat hc) (Subgroup.card_dvd_of_le hBU)
  · -- pointwise congruence on all of `B`
    intro b
    have hbU : (b : G) ∈ C.P.U := by rw [hc.U_eq]; exact b.2.1.1
    let h : ↥C.P.H0 := ⟨(b : G), C.P.U_le_H0 hbU⟩
    have hmem : (h : G) ∈ D.B := b.2
    have h1 : AlgIntModTwo (ν h) (θ ⟨h, hmem⟩) := hθ.2 h hmem
    have h2 : AlgIntModTwo (ν h) (θ' ⟨h, hmem⟩) := hθ'.2 h hmem
    have hb_eq : (⟨h, hmem⟩ : ↥D.B) = b := Subtype.ext rfl
    rw [hb_eq] at h1 h2
    exact h1.symm.trans h2

end Work.BG
