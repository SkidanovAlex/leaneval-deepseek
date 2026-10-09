import Submission.Work.SSGRoute.E7Fin.natCard_LamQuot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `𝔽_p`-dimension of `Λ/pΛ`

Lane `Work.SSGRoute.coker_obstruction_pt`, lattice half of `(C-ISO)`: the dimension form of the
order computation `E7Fin.natCard_LamQuot`.

`Λ = log U¹` is a `ℤ_p`-lattice of rank `[K_𝔮 : ℚ_p]` (`NK.LocalInputs.localDegree K 𝔮`), so its
`p`-power quotient `Λ/pΛ` is an `𝔽_p`-vector space of dimension `[K_𝔮 : ℚ_p]`
(`E7Fin.lamQuotModule`).  This is the numerical input for the rank statement `Λ/pΛ ≅ 𝔽_p[Γ'']^c` of
Milne *ADT* I.2.11: the rank of the free `𝔽_p[Γ'']`-module there is `[L_w : ℚ_p]` and
`[K_v : ℚ_p] = |Γ''| · [L_w : ℚ_p] = dim_{𝔽_p} Λ/pΛ`.

## Main result

* `E7Fin.finrank_LamQuot`
-/

namespace Work.SSGRoute.E7Fin

noncomputable section

/-- **The `𝔽_p`-dimension of `Λ/pΛ` is `[K_𝔮 : ℚ_p]`.**  Immediate from
`E7Fin.natCard_LamQuot` and `Module.natCard_eq_pow_finrank`. -/
theorem finrank_LamQuot
    {K : Type} [Field K] [NumberField K] {𝔮 : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)} {p M : ℕ}
    (D : CanonLogData 𝔮 M) (hp : p.Prime) [Fact p.Prime] [NeZero p]
    (hres : CharP (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K)) p) :
    Module.finrank (ZMod p) (LamQuot D hp hres) = NK.LocalInputs.localDegree K 𝔮 := by
  have hcard := natCard_LamQuot D hp hres
  haveI hfin : Finite (LamQuot D hp hres) := by
    refine Finite.of_not_infinite ?_
    intro hinf
    have h0 : Nat.card (LamQuot D hp hres) = 0 := Nat.card_eq_zero.mpr (Or.inr hinf)
    rw [h0] at hcard
    exact (pow_ne_zero _ hp.ne_zero) hcard.symm
  haveI : Module.Finite (ZMod p) (LamQuot D hp hres) := Module.Finite.of_finite
  have hpow : Nat.card (LamQuot D hp hres)
      = p ^ Module.finrank (ZMod p) (LamQuot D hp hres) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := LamQuot D hp hres), Nat.card_zmod]
  rw [hpow] at hcard
  exact Nat.pow_right_injective hp.two_le hcard

end

end Work.SSGRoute.E7Fin
