import Submission.Work.DSM2p.One
import Submission.Work.DSM2p.N8_flat_pIntClosure_CSAlgOne
import Submission.Work.DSM2p.flat_quot_ideal_of_flat
import Submission.Work.DSM2p.CSIntegralClosureOne_faithfullyFlat_of_flatModVarpi
import Submission.Work.DSM2p.CSCompletionOne_faithfullyFlat_of_CSIntegralClosureOne

/-!
# `(H2)` for the one-polynomial cover: `B_F ⧸ pB_F` is faithfully flat over `A ⧸ (p)`

This assembles the target `(H2)` of the area for the one-polynomial construction
(`CSCompletionOne A p ϖ F`, see `Submission/Work/DSM2p/One.lean` and the lead design
`sources/dsmap/direct_summand_m2p_h2_design.md`):

* `N8_flat_pIntClosure_CSAlgOne` — `A'_F` is `A`-flat;
* `flat_quot_ideal_of_flat` — base change gives `A'_F ⧸ ϖA'_F` flat over `A ⧸ (ϖ)`;
* `CSIntegralClosureOne_faithfullyFlat_of_flatModVarpi` — ČS `Andre-lem`: flatness mod `ϖ`
  gives *faithful* flatness of `A'_F ⧸ pA'_F` over `A ⧸ (p)`;
* `CSCompletionOne_faithfullyFlat_of_CSIntegralClosureOne` — transport along
  `B_F ⧸ pB_F ≅ A'_F ⧸ pA'_F`.
-/

namespace Work.DSM2p

set_option synthInstance.maxHeartbeats 1600000 in
theorem CSCompletionOne_faithfullyFlat (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime]
    (P : DSMap.PerfectoidData p A) (F : Polynomial A) (hF : F.Monic) (hFd : 0 < F.natDegree) :
    Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A)})
      (CSCompletionOne A p (P.ϖ 0) F ⧸
        (Ideal.span {(p : A)}).map (algebraMap A (CSCompletionOne A p (P.ϖ 0) F))) :=
  CSCompletionOne_faithfullyFlat_of_CSIntegralClosureOne A p P F
    (CSIntegralClosureOne_faithfullyFlat_of_flatModVarpi A p P F hF hFd
      (flat_quot_ideal_of_flat (Ideal.span {(P.ϖ 0 : A)})
        (N8_flat_pIntClosure_CSAlgOne A p P F hF)))

end Work.DSM2p
