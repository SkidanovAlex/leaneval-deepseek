import Mathlib
import Submission.Work.DSEQP.gf_defs
import Submission.Work.DSEQP.DZA.Vocab
import Submission.Work.DSEQP.DZA.Arith
import Submission.Work.DSEQP.DZA.Chart
import Submission.Work.DSEQP.DZA.ToAway

/-!
# `Work.DSEQP.DZA.gf_degzero_away`

The chart ring `Away (MvPolynomial.homogeneousSubmodule (Fin (N+1)) A) (xS S)` of the standard
chart `D₊(x_S)` of `ℙᴺ_A` is the degree-zero part `degZero (homSub A (N+1)) S` of the
localization of the polynomial ring `A[x₀,…,x_N]` at the variables indexed by `S`, and the two
restriction maps (`Work.DSCOH.resAt` and `Work.DSEQP.awayRes`) correspond under the identification.
The isomorphism is the obvious one on the generating fractions `m / xS S ^ k`
(`m ∈ 𝒜 (k · S.card)`); its construction and properties are in the auxiliary modules
`Submission.Work.DSEQP.DZA.{Arith,Chart,ToAway}`.
-/

open MvPolynomial HomogeneousLocalization

namespace Work.DSEQP.DZA

universe a

theorem gf_degzero_away (A : Type a) [CommRing A] {N : ℕ} :
    ∃ e : ∀ (S : Finset (Fin (N + 1))), S.Nonempty →
      (↥(Work.DSCOH.degZero (A := A) (M := MvPolynomial (Fin (N + 1)) A)
          (Work.DSCOH.homSub A (N + 1)) S) ≃ₗ[A]
        HomogeneousLocalization.Away (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S)),
      ∀ (S T : Finset (Fin (N + 1))) (hST : S ⊆ T) (hS : S.Nonempty) (hT : T.Nonempty)
        (x : ↥(Work.DSCOH.degZero (A := A) (M := MvPolynomial (Fin (N + 1)) A)
          (Work.DSCOH.homSub A (N + 1)) S)),
        e T hT ⟨Work.DSCOH.resAt (A := A) (M := MvPolynomial (Fin (N + 1)) A) hST x.1,
            Work.DSCOH.resAt_degZero (A := A) (M := MvPolynomial (Fin (N + 1)) A) hST x.1 x.2⟩
          = Work.DSEQP.awayRes (A := A) (N := N) hST (e S hS x) := by
  refine ⟨fun S hS => e (A := A) (N := N) S hS, ?_⟩
  intro S T hST _hS _hT x
  show toAway (A := A) (N := N) T (Work.DSCOH.degPartRestrict (A := A) (n := N + 1)
        (M := MvPolynomial (Fin (N + 1)) A) (Work.DSCOH.homSub A (N + 1))
        (Work.DSCOH.resAt (A := A) (M := MvPolynomial (Fin (N + 1)) A) hST)
        (fun y hy => Work.DSCOH.resAt_degZero (A := A)
          (M := MvPolynomial (Fin (N + 1)) A) hST y hy) x)
      = Work.DSEQP.awayRes (A := A) (N := N) hST (toAway (A := A) (N := N) S x)
  exact toAway_natural (A := A) (N := N) hST x

end Work.DSEQP.DZA
