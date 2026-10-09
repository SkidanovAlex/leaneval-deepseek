import Mathlib
import Submission.Work.AbsoluteKummer.Defs
import Submission.Work.AbsoluteKummer.Basic
import Submission.Work.AbsoluteKummer.Coefficients
import Submission.Work.AbsoluteKummer.SES
import Submission.Work.AbsoluteKummer.SES.exists_connecting_exact
import Submission.Work.AbsoluteKummer.Kummer.kummerSES
import Submission.Work.AbsoluteKummer.Hilbert90.H1_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteKummer.Kummer

open scoped Classical

noncomputable section

/-- **The Kummer isomorphism** `kˣ/(kˣ)ⁿ ≃ H¹(G_k, μ_n)`, in the form of the low-degree exact
sequence of the Kummer sequence `1 → μ_n(k̄) → k̄ˣ →^{n} k̄ˣ → 1`.

Concretely: for the short exact sequence `0 → μ_n(k̄) →^{ι} k̄ˣ →^{π} k̄ˣ → 0` of discrete
`G_k`-modules, the connecting map `δ : H⁰(G_k, k̄ˣ) → H¹(G_k, μ_n(k̄))` has kernel the image of
`H⁰(π) : H⁰(G_k, k̄ˣ) → H⁰(G_k, k̄ˣ)`, which is exactly the image of the `n`-th power map on
`kˣ = H⁰(G_k, k̄ˣ)`.  Since `H¹(G_k, k̄ˣ) = 0` (Hilbert 90), `δ` is surjective, so the first
isomorphism theorem gives

`H⁰(G_k, k̄ˣ) / im(H⁰(π)) ≃+ H¹(G_k, μ_n(k̄))`. -/
theorem kummerQuotientEquiv {k : Type*} [Field k] [IsGalois k (AlgebraicClosure k)] {n : ℕ} [NeZero n] : Nonempty ((Work.AbsoluteKummer.H0 (Work.AbsoluteKummer.G k) (Additive (AlgebraicClosure k)ˣ) ⧸ (Work.GroupCohomology.mapH0 (Work.AbsoluteKummer.G k) (Work.AbsoluteKummer.Kummer.kummerPi (k := k) n) (Work.AbsoluteKummer.Kummer.kummerPi_equivariant (k := k) n)).range) ≃+ Work.AbsoluteKummer.H1 (Work.AbsoluteKummer.G k) (Additive (rootsOfUnity n (AlgebraicClosure k)))) := by
  classical
  -- The Kummer short exact sequence, in the literal form in which its `pi` is `kummerPi`.
  let S : Work.AbsoluteKummer.ShortExactSeq (Work.AbsoluteKummer.G k)
      (Additive (rootsOfUnity n (AlgebraicClosure k))) (Additive (AlgebraicClosure k)ˣ)
      (Additive (AlgebraicClosure k)ˣ) :=
    { iota := Work.AbsoluteKummer.Kummer.kummerIota (k := k) n
      pi := Work.AbsoluteKummer.Kummer.kummerPi (k := k) n
      iota_equivariant := Work.AbsoluteKummer.Kummer.kummerIota_equivariant (k := k) n
      pi_equivariant := Work.AbsoluteKummer.Kummer.kummerPi_equivariant (k := k) n
      iota_injective := Work.AbsoluteKummer.Kummer.kummerIota_injective (k := k) n
      pi_surjective := Work.AbsoluteKummer.Kummer.kummerPi_surjective (k := k) n
      range_iota_eq_ker_pi := Work.AbsoluteKummer.Kummer.kummerIota_range_eq_ker_pi (k := k) n
      isDiscreteM := Work.AbsoluteKummer.isDiscreteModule_addRootsOfUnity k n
      isDiscreteN := Work.AbsoluteKummer.isDiscreteModule_addUnits k
      isDiscreteP := Work.AbsoluteKummer.isDiscreteModule_addUnits k }
  -- The connecting map of the long exact sequence in low degrees.
  obtain ⟨δ, hker, hrange⟩ := Work.AbsoluteKummer.SES.exists_connecting_exact S
  -- Hilbert 90: `H¹(G_k, k̄ˣ) = 0`, hence `δ` is surjective.
  have hsub : ∀ x y : Work.AbsoluteKummer.H1 (Work.AbsoluteKummer.G k)
      (Additive (AlgebraicClosure k)ˣ), x = y := fun a b => by
    rw [Work.AbsoluteKummer.Hilbert90.H1_eq_zero a,
      Work.AbsoluteKummer.Hilbert90.H1_eq_zero b]
  have htop : δ.range = ⊤ := by
    rw [eq_top_iff]
    intro y _
    rw [hrange, AddMonoidHom.mem_ker]
    exact hsub _ _
  have hsurj : Function.Surjective δ := AddMonoidHom.range_eq_top.mp htop
  -- First isomorphism theorem, glued with the identification of the kernel of `δ`.
  exact ⟨(QuotientAddGroup.quotientAddEquivOfEq hker).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective δ hsurj)⟩

end

end Work.AbsoluteKummer.Kummer
