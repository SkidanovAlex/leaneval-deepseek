import Mathlib
import Submission.Work.SSGRoute.E7Fin.lamQuotAction
import Submission.NK.LocalInputs.PowerQuotient.LamIndex
import Submission.Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The order of `Λ / pΛ`

Lane `Work.SSGRoute.E7Fin`, the count underlying the `Γ`-module `Λ/pΛ` of
`E7Fin/lamQuotAction.lean`.  For a number field `K`, a finite place `𝔮` and the prime `p` below it,
the lattice `Λ = log U¹ ⊆ K_𝔮` is a `ℤ_p`-lattice of rank `[K_𝔮 : ℚ_p]`, so its `p`-power quotient
has order `p ^ [K_𝔮 : ℚ_p]`:

  `Nat.card (Λ / pΛ) = p ^ localDegree K 𝔮`.

This is a restatement of `NK.LocalInputs.PowerQuotient.relIndex_Lam_map_mul_p`
(`[Λ : pΛ] = p ^ localDegree K 𝔮`) transported from the relative index of the image `pΛ ⊆ κ`
to the cardinality of the abstract quotient `↥Λ ⧸ pΛ`.

The only bookkeeping is that `p Λ`, as an *abstract* subgroup of `↥Λ`, is the preimage of the
image `p • Λ` of the ambient multiplication-by-`p` map under the inclusion `Λ ↪ κ`.
-/

namespace Work.SSGRoute.E7Fin

open NK.LocalInputs.PowerQuotient

theorem natCard_LamQuot
    {K : Type} [Field K] [NumberField K] {𝔮 : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)} {p M : ℕ}
    (D : Work.SSGRoute.E7Fin.CanonLogData 𝔮 M) (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K)) p) :
    Nat.card (Work.SSGRoute.E7Fin.LamQuot D hp hres) =
      p ^ NK.LocalInputs.localDegree K 𝔮 := by
  -- `p • x` on the completion is multiplication by the integer `p`
  have hhom : nsmulAddMonoidHom (α := 𝔮.adicCompletion K) p
      = AddMonoidHom.mulLeft ((p : ℕ) : 𝔮.adicCompletion K) := by
    ext x
    simp [nsmul_eq_mul]
  -- `pΛ`, as a subgroup of `↥Λ`, is the preimage of the image of multiplication by `p` on `κ`
  have hB : ((LamSub D hp hres).map (nsmulAddMonoidHom (α := 𝔮.adicCompletion K) p)).comap
        (LamSub D hp hres).subtype
      = (nsmulAddMonoidHom (α := ↥(LamSub D hp hres)) p).range := by
    ext x
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_map, AddMonoidHom.mem_range]
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩
    · rintro ⟨y, rfl⟩
      exact ⟨(y : 𝔮.adicCompletion K), y.2, rfl⟩
  have hindex : (pLamSub D hp hres).index =
      ((LamSub D hp hres).map (AddMonoidHom.mulLeft ((p : ℕ) : 𝔮.adicCompletion K))).relIndex
        (LamSub D hp hres) := by
    unfold pLamSub
    rw [← hB, AddSubgroup.index_comap, AddSubgroup.range_subtype, hhom]
  rw [← AddSubgroup.index_eq_card, hindex]
  exact relIndex_Lam_map_mul_p D.toLogData hp hres _
    (Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one 𝔮)

end Work.SSGRoute.E7Fin
