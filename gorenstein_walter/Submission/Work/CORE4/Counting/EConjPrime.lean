import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.PSL2.Card
import Submission.Work.CORE4.Counting.ConjOrbitEq
import Submission.Work.CORE4.Counting.NormalizerCard
import Submission.Work.CORE4.Counting.NormalizerIndex
import Submission.Work.CORE4.Counting.PrimeCount

namespace Work.CORE4.Counting

/-- Bender's "E has cyclic S_p-subgroups": if q = pF^kF, k is the even half and k' the odd half of q -+ 1, and r is an odd prime with r ≠ pF and r ∣ k, then any two subgroups of PSL(2, GF pF kF) of order r are conjugate. Proof: L2TorusNormalizerProp gives, for every order-r subgroup Y, that N(Y) is dihedral with 2|C(Y)| = q ± 1, so the conjugation orbit of Y has size |E : N(Y)| = 2qkk'/(q ± 1), which is qk or qk'; L2PrimeSubgroupCountProp gives that the total number of order-r subgroups is qk'. A partition of qk' objects into parts of size qk or qk' must contain a part of size qk' (since k ∣ k' is impossible for k ≥ 2 as gcd(k,k') = 1), and that part is everything. -/
theorem EConjPrime (hcount : Work.GW2.L2PrimeSubgroupCountProp)
    (htorus : Work.GW2.L2TorusNormalizerProp)
    (pF kF k k' r : ℕ) [Fact pF.Prime]
    (hodd : Odd pF) (hq5 : 5 ≤ pF ^ kF)
    (hk : Even k) (hk' : Odd k')
    (hdisj : (2 * k = pF ^ kF + 1 ∧ 2 * k' = pF ^ kF - 1) ∨
             (2 * k = pF ^ kF - 1 ∧ 2 * k' = pF ^ kF + 1))
    (hr : r.Prime) (hr2 : r ≠ 2) (hrp : r ≠ pF) (hrk : r ∣ k) :
    ∀ Y Y' : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF)),
      Nat.card Y = r → Nat.card Y' = r →
      ∃ e : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF),
        Y' = Y.map (MulAut.conj e).toMonoidHom := by
  intro Y Y' hY hY'
  have hcountS : {X : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF)) |
      Nat.card X = r}.ncard = pF ^ kF * k' :=
    PrimeCount hcount pF kF k k' r hodd hq5 hk hk' hdisj hr hr2 hrp hrk
  have hN : Nat.card (Subgroup.normalizer
      (Y : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF)))) = 2 * k :=
    NormalizerCard htorus pF kF k k' r hodd hq5 hk hk' hdisj hr hr2 hrp hrk Y hY
  have hidx : (Subgroup.normalizer
      (Y : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF)))).index =
      pF ^ kF * k' :=
    NormalizerIndex pF kF k k' hodd hq5 hdisj Y hN
  exact ConjOrbitEq r (pF ^ kF * k') hcountS Y hY hidx Y' hY'

end Work.CORE4.Counting
