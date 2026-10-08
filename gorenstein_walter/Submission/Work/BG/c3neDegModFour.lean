import Mathlib
import Submission.Work.BG.lemma17_ii
import Submission.Work.BG.rem31Shape
import Submission.Work.BG.rem31Orth
import Submission.Work.BG.rem31StabCard
import Submission.Work.BG.rem31IndexUin
import Submission.Work.BG.bset_orbit_struct
import Submission.Work.BG.s02_lemma21
import Submission.Work.BG.thm32
import Submission.Work.BG.lemma24
import Submission.Work.BG.lemma18LinearIndependent
import Submission.Work.BG.CharBridge
import Submission.Work.BG.l34ne_orbit_deg_dvd
import Submission.Work.BG.s02_sum_irr_eq_finsum_bset
import Submission.Work.BG.inner_pmIrr_eq_pm_one
import Submission.Work.BG.l34ne_deg_mod_four

/-!
# Area BG: `4 ∣ χ(1)` in the `|Λν| = 4`, `|Λξ| ≠ 4` branch of BG 1981, Lemma 3.4

`Work.BG.c3neDegModFour` is the degree count of Bender–Glauberman 1981, Lemma 3.4 (p. 209), in
the branch where the exceptional configuration `𝒮(χ) = bset C f χ = {ν, ν^s, ξ}` has
`D.n = |Λν| = 4` (with `Λν` stable under `s`) and the third member `ξ` is `s`-fixed with
`|Λξ| ≠ 4` (hence `|Λξ| = 2` by Remark 3.1) and `ξ(1) = 2·(odd)`.  It is exactly the statement
that the caller `Work.BG.c3ExcNeFour` needs: then `4 ∣ χ(1)`.

The mathematical content (BG p. 209) is: the coherent map (`Work.BG.lemma24`) gives
`χ = ε·(ν + ν^s) + δ·ξ` on `H₀` modulo the `U`-supported part, with `ε = (χ, f ν) = ±1`,
`δ = (χ, f ξ) = ±1`; so `Φ := χ|_{H₀} - ε·(ν + ν^s) - δ·ξ` is a virtual character of `H₀`
vanishing on `T = H₀ ∖ U`, and

  `χ(1) = 2ε·ν(1) + δ·ξ(1) + Φ(1)`.

For such `Φ` one has `D.n ∣ Φ(1)`: Fourier inversion writes `Φ = Σ_σ (Φ,σ)·σ` with the
coefficients `(Φ,σ)` constant along `Λ`-orbits (`λ_β·Φ = Φ` for `Φ` supported on `U`), so `Φ`
is an integer combination of orbit sums, whose degrees `|Λσ|·σ(1)` are multiples of `D.n` by
Remark 3.1 (`Work.BG.rem31Shape`).  Finally `ν(1)` is odd (`ν|_U` is irreducible and `U` has
odd order) and `ξ(1) = 2·(odd)`, so `2ε·ν(1) + δ·ξ(1) ≡ 2 + 2 ≡ 0 (mod 4)`.

This statement is already carried by the shared library, proved in full, as
`Work.BG.l34ne_deg_mod_four` (and, under the same statement, `Work.BG.c3deDegModFour`); the
present declaration is the `c3`-family entry point consumed by `Work.BG.c3ExcNeFour`, and it is
discharged by citing that result rather than duplicating its ~300-line development.  Its axiom
footprint is `[propext, Classical.choice, Quot.sound]`.
-/

namespace Work.BG

theorem c3neDegModFour {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C16.Compat D C → Work.GW2.C16.Sec3Hyp D →
    ∀ f : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ → OddOrder.RepresentationTheory.ClassFunction G ℂ,
      Work.GW2.C16.IsCoherent C f →
    ∀ χ : OddOrder.RepresentationTheory.ClassFunction G ℂ, Work.BG.IsPmIrr χ →
    ∀ ν ∈ Work.GW2.C16.bset C f χ, Work.BG.sconj C ν ≠ ν →
      (Work.BG.sconj C ν ∉ Work.BG.lamOrbit C ν ∨ (Work.BG.lamOrbit C ν).ncard = D.n) →
      (Work.BG.lamOrbit C ν).ncard = 4 →
      Work.BG.sconj C '' Work.BG.lamOrbit C ν = Work.BG.lamOrbit C ν →
      D.n = 4 →
      ∀ ξ ∈ Work.GW2.C16.bset C f χ, ξ ≠ ν → ξ ≠ Work.BG.sconj C ν →
        Work.BG.sconj C ξ = ξ → (Work.BG.lamOrbit C ξ).ncard ≠ 4 →
        Work.GW2.C16.bset C f χ = {ν, Work.BG.sconj C ν, ξ} →
        (∃ m : ℤ, ξ 1 = (2 : ℂ) * (m : ℂ) ∧ Odd m) →
        ∃ k : ℤ, χ 1 = (4 : ℂ) * (k : ℂ) :=
  fun hDC hS3 f hf χ hχ ν hν hne hdisj h4 hinv hD4 ξ hξ hξν hξνs hξs hξ4 hbset hξdeg =>
    l34ne_deg_mod_four D C hDC hS3 f hf χ hχ ν hν hne hdisj h4 hinv hD4
      ξ hξ hξν hξνs hξs hξ4 hbset hξdeg

end Work.BG
