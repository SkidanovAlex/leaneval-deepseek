import Mathlib
import Submission.Work.CFT.Kummer.Defs
import Submission.Work.CFT.Kummer.Hypotheses
import Submission.Work.CFT.Kummer.Estimate
import Submission.Work.CFT.Kummer.TotallyRealCubic
import Submission.Work.CFT.Kummer.finrank_H1Fp_mulEquiv
import Submission.Work.CFT.Kummer.finrank_H2Fp_mulEquiv
import Submission.Work.Tower.Shafarevich.Estimate

/-!
# Shafarevich's estimate in the form consumed by the Golod–Shafarevich tower

`Work.Tower.Shafarevich.H2Estimate C₀` is the arithmetic input of the tower construction
(paper Proposition 3.5 / A.10) in the cohomological form used in `Work.Tower.Shafarevich`:
for every finite everywhere-unramified Galois `3`-extension `K` of a totally real cubic field `F`
which is maximal among those in which a finite set `T` of primes (with trivial Frobenius class in
the Frattini quotient) splits completely,

`dim_{𝔽₃} H²(Gal(K/F), 𝔽₃) ≤ dim_{𝔽₃} H¹(Gal(K/F), 𝔽₃) + C₀ + |T|`.

This file shows that `H2Estimate 2` follows from the Kummer/Shafarevich input of this area: it
suffices that, for every totally real cubic `F`, the maximal everywhere-unramified pro-`3` group
`G = Gal(F_∅(3)/F)` is available with the Kummer–Shafarevich facts
(`Work.CFT.Kummer.UnramifiedShafarevich`) and Koch's transfer
(`Work.CFT.Kummer.KochTransfer`), and that every finite level `K/F` of the tower is a quotient
`G ⧸ N` of `G` by the normal closure `N` of at most `|T|` elements whose killing leaves the
generator rank unchanged — the situation when the Frobenius classes of the primes of `T` lie in
the Frattini subgroup of `G`.

## Main definitions and results

* `Work.CFT.Kummer.UnramifiedPresentation` — the presentation data of the tower described above.
* `Work.CFT.Kummer.H2Estimate_two_of_unramifiedPresentation` — `H2Estimate 2` from it.
-/

open scoped nonZeroDivisors
open NumberField

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Work.CFT.Kummer

/-- **Presentation data for the Golod–Shafarevich tower.**  For every totally real cubic field `F`
there is a group `G` modelling the maximal everywhere-unramified pro-`3` group `Gal(F_∅(3)/F)`
which satisfies the Kummer–Shafarevich facts `UnramifiedShafarevich F 3 G` and Koch's transfer
`KochTransfer 3 G`, and every finite everywhere-unramified Galois `3`-extension `K/F` which is
maximal for complete splitting of a set `T` of primes arises as `Gal(K/F) ≃ G ⧸ N` for some normal
`N` which is the normal closure of at most `|T|` elements and whose killing does not change the
generator rank (`dim H¹(G ⧸ N) = dim H¹(G)`; this holds when the Frobenius classes of the primes
of `T` lie in the Frattini subgroup of `G`). -/
def UnramifiedPresentation : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F],
    Module.finrank ℚ F = 3 →
    ∃ (G : Type) (_ : Group G) (_hU : UnramifiedShafarevich F 3 G) (_ : KochTransfer 3 G),
      ∀ (K : Type) [Field K] [NumberField K] [Algebra F K] [FiniteDimensional F K]
        [IsGalois F K],
        Work.Tower.IsUnramifiedExtension F K → IsPGroup 3 (Gal(K/F)) →
        ∀ (T : Finset (Ideal (𝓞 F))),
          Work.Tower.Shafarevich.IsFrobeniusTrivialInFrattini F T →
          Work.Tower.Shafarevich.IsMaximalSplittingExtension F K T →
          ∃ (N : Subgroup G) (_ : N.Normal) (k : ℕ) (g : Fin k → G), k ≤ T.card ∧
            N = Subgroup.normalClosure (Set.range g) ∧
            Module.finrank (ZMod 3) (H1Fp 3 (G ⧸ N)) = Module.finrank (ZMod 3) (H1Fp 3 G) ∧
            Nonempty (G ⧸ N ≃* Gal(K/F))

/-- **Shafarevich's estimate `H2Estimate 2` for the tower**, from the Kummer-theoretic input of
this area: `dim_{𝔽₃} H²(Gal(K/F)) ≤ dim_{𝔽₃} H¹(Gal(K/F)) + 2 + |T|`, with the constant
`2 = r₁ + r₂ - 1 + δ_{F,3}` for a totally real cubic `F` and `p = 3`. -/
theorem H2Estimate_two_of_unramifiedPresentation (h : UnramifiedPresentation) :
    Work.Tower.Shafarevich.H2Estimate 2 := by
  intro F _ _ _ hdeg K _ _ _ _ _ hK h3 T hT hmax
  obtain ⟨G, instG, hU, hKoch, hquot⟩ := h F hdeg
  obtain ⟨N, hN, k, g, hk, hNg, hgen, ⟨e⟩⟩ := hquot K hK h3 T hT hmax
  letI := instG
  letI := hU
  cases hNg
  have key := finrank_H2Fp_quotient_le_two_of_rank_delta F G hKoch k g hgen
    (units_rank_eq_two_of_totallyReal_cubic F hdeg)
    (deltaK_eq_zero_of_totallyReal F 3 (by norm_num) (by norm_num))
  rw [finrank_H2Fp_mulEquiv e, finrank_H1Fp_mulEquiv e] at key
  have key' : Module.finrank (ZMod 3) (Work.Tower.Shafarevich.H2Fp 3 (K ≃ₐ[F] K)) ≤
      Module.finrank (ZMod 3) (Work.Tower.Shafarevich.H1Fp 3 (K ≃ₐ[F] K)) + 2 + k := key
  omega

end Work.CFT.Kummer
