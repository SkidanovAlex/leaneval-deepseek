import Mathlib
import Submission.Work.BG.L41Aux
import Submission.Work.BG.S02
import Submission.Work.BG.rem31Shape
import Submission.Work.BG.lemma36Defs

namespace Work.BG

/-- **The `D.n = 2` configuration of BG Lemma 3.6.**  If `D.n = 2` then every `Λ`-orbit of
`Irr(H₀)` has exactly `D.n = 2` elements.

This is the fact that supplies `hfix` (`sconj C ν ≠ ν` on `𝒮(χ)`) in the `D.n = 2` sub-case of
Step 3: for `ν₀ ∈ 𝒮(χ)`, `Work.BG.lamOrbit_subset_bset_of_badCase` gives `Λν₀ ⊆ 𝒮(χ)`, and
`Work.BG.bset_orbit_struct` part 2 then forces `Λν₀ = {ν₀}` if `sconj C ν₀ = ν₀` — contradicting
`|Λν₀| = D.n = 2`.

Route (both ingredients are already proved, sorry-free, in `Submission.Work.BG.L41Aux`):
`Work.BG.L41Aux.quotGroup_card_two` turns `D.n = 2` into `Nat.card (quotGroup C.P) = 2`, and
`Work.BG.L41Aux.lamOrbit_ncard_eq_two` then gives `(lamOrbit C μ).ncard = 2` for every irreducible
`μ` as soon as a non-trivial `β₂ : quotGroup C.P →* ℂˣ` is exhibited (it exists because a group of
order `2` has a non-trivial character, `dualC2_generic` in
`Submission.Work.BG.lemma17_iii_dualC2`).  Since `D.n = 2`, `|H₀ : U| = 2` and `H₀ = U × ⟨t⟩`
(`t` is central in `H ⊇ H₀`), the orbit really has `2 = D.n` elements. -/
theorem lamOrbit_ncard_eq_two_of_n_eq_two {G : Type} [Group G] [Finite G]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) (hDC : Work.GW2.C16.Compat D C)
    [Fintype ↥C.P.H0] [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    [Fintype (Work.BG.quotGroup C.P →* ℂˣ)]
    {ν : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ}
    (hν : OddOrder.RepresentationTheory.IsIrreducibleCharacter ν) :
    D.n = 2 → (Work.BG.lamOrbit C ν).ncard = D.n := by
  intro hn
  -- Instances used by the §2 library, derived from `[Finite G]`.
  have : Fintype G := Fintype.ofFinite G
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (by
      have h1 : (1 : ℕ) ≤ Nat.card G :=
        Nat.one_le_iff_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩)
      exact_mod_cast (Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp h1)))
  -- `D.n = 2` forces `|H₀/U| = 2`.
  have h2 : Nat.card (quotGroup C.P) = 2 := quotGroup_card_two D C hDC hn
  -- A group of order two has a character taking the value `-1` at `t`, hence non-trivial.
  obtain ⟨β₂, hβ₂val⟩ := exists_negChar C
  have hβ : β₂ ≠ 1 := by
    intro h
    have h1 : lamCF C (1 : quotGroup C.P →* ℂˣ) C.t = 1 := by
      rw [lamCF_one_eq]
      simp
    rw [h, h1] at hβ₂val
    norm_num at hβ₂val
  rw [hn]
  exact lamOrbit_ncard_eq_two C h2 hβ hν

end Work.BG
