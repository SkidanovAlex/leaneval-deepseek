import Mathlib
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.Defs
import Submission.NK.GlobalCFTdeep.SecondInequality.pow_mem_normGroup_adicCompletion

set_option linter.style.haveILetI false

namespace NK.GlobalCFTdeep.SecondInequality.KummerCase

/-- **`p`-th powers of local units at `Q` are local norms from `L` at `q`.**

Let `L / K` be a finite Galois extension of number fields whose Galois group has prime order `p`,
let `Q` be a finite place of `K` and `q` a place of `L` above `Q`.  Then every `p`-th power of an
element of `K_Qˣ` is the norm of an element of `L_qˣ` under the local norm
`N_{L_q/K_Q} : L_qˣ →* K_Qˣ`.

Indeed, `Gal(L_q/K_Q)` is cyclic of order dividing `p`, so the norm group has index dividing `p`
in `K_Qˣ` (the norm index theorem of local class field theory), whence every `p`-th power is a
norm. -/
theorem localPow_mem_localNormFinite {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {p : ℕ} (hp : p.Prime) (hcard : Nat.card (L ≃ₐ[K] L) = p)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) {x : (Q.adicCompletion K)ˣ}
    (hx : x ∈ NK.GlobalCFTdeep.SecondInequality.KummerCase.localPow (K := K) p
      (NK.GlobalCFT.Place.ofFinite Q)) :
    ∃ u : (q.adicCompletion L)ˣ, NK.GlobalCFT.Place.localNormFinite q Q hq u = x := by
  -- register `q | Q` as an instance so that the canonical `K_Q`-algebra structure on `L_q` is
  -- available (it is `NK.LocalReciprocity.instAlgebraAdicCompletion`)
  haveI : q.asIdeal.LiesOver Q.asIdeal := hq
  -- `x` is a `p`-th power, say `x = y ^ p`
  rw [localPow] at hx
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hx
  have hy' : y ^ p = x := hy
  -- every `p`-th power is a norm: the norm index divides `p`
  have hpow : y ^ p ∈
      NK.LocalReciprocity.normGroup (Q.adicCompletion K) (q.adicCompletion L) :=
    NK.GlobalCFTdeep.SecondInequality.pow_mem_normGroup_adicCompletion
      (K := K) (L := L) hp hcard Q q y
  rw [NK.LocalReciprocity.normGroup_eq_range] at hpow
  -- the norm group is the range of the local norm map
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hpow
  refine ⟨u, ?_⟩
  rw [show NK.GlobalCFT.Place.localNormFinite q Q hq =
      Units.map (Algebra.norm (Q.adicCompletion K)) from rfl, hu, hy']

end NK.GlobalCFTdeep.SecondInequality.KummerCase
