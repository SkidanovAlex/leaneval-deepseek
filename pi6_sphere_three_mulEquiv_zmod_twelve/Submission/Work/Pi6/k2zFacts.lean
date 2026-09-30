import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.K2Z.defs
import Submission.Work.Pi6.K2Z.integral
import Submission.Work.Pi6.K2Z.fieldHalf
import Submission.Work.Pi6.K2Z.fgFromPrimes
import Submission.Work.Pi6.K2Z.kronH_bij
import Submission.Work.Pi6.K2Z.redNat
import Submission.Work.Pi6.KronBridge
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-! Guidance from the project lead (the requester):

AREA K2Z (pi6). Read REFS/NOTES_LEAD_PI6.md §4 (general setup + "K2Z"). You may assume MSSHolds (hypothesis hM).
Statement: every K(ℤ,2) range model X through N ≥ 10 has H^{2k}(X;ℤ) = ℤ·x^k and H^{2k+1}(X;ℤ) = 0 (k ≤ 4), and over
every field 𝕜, H^{2k}(X;𝕜) = 𝕜·w^k with w^k ≠ 0 and H^{odd} = 0 (k ≤ 4). cpow is the cup power in Interfaces.lean.
Route: path fibration mpathQ (constant map at x₀) : mpath → X (Work.Serre.mpathQ_isSerreFibration), total space
contractible (paths from x₀), fibre ≃ₜ based loops (Work.Serre.mpathQ_fibreHomeo), a K(ℤ,1) model through N−1
(fibration LES, or Work.Stems.isEMSpaceUpTo_loop after a homeomorphism to Path x₀ x₀). K(ℤ,1) models have the
homology of the circle: Work.EMFG.kOneComparison with Work.EMFG.sphOne_isEMSpaceUpTo and the sphere homology
(Work.Cohomology.sphereHomologyTop/Zero). Two rows ⇒ with u ∈ E^{0,1}: e := d_2 u spans H^2, Leibniz d_2(b·u) = ±b·e,
everything must die ⇒ ∪e : H^s → H^{s+2} iso and H^1 = 0 ⇒ the field statement.
Finite type hypotheses of MSSHolds: H_*(X;ℤ) f.g. (Work.EMFG.emHomologyFG proves Work.PiS.EMHomologyFG) ⇒ H_*(X;𝕜)
finite-dim (Bockstein LES) ⇒ H^*(X;𝕜) finite-dim (duality Work.StemsB.fieldDualUCT / kronH_bijective_field).
Integral part from all fields (NOTES): H_i f.g., odd degrees vanish mod every p and rationally ⇒ H_odd = 0, H_even ≅ ℤ;
H^{2k}(X;ℤ) ≅ Hom(H_{2k},ℤ) needs a DEGREE-LOCAL UCT (uctDual assumes all homology free — prove the local version);
x^k = m·generator with m ≠ 0 and p ∤ m for all p (reduce mod p; reduction commutes with cup) ⇒ m = ±1.
Suggested children: Pi6/K2Z/loopFibre, Pi6/K2Z/finiteType, Pi6/K2Z/gysinField, Pi6/K2Z/localUCT, Pi6/K2Z/integral.
Internally prove the field part for models through N ≥ 8 (EMM2's loops need it).
-/

namespace Work.Pi6

/-- **Area K2Z.**  The cohomology of `K(ℤ,2)` range models through degree `9`: integrally
`H^{2k} = ℤ·x^k` and `H^{odd} = 0`; over every field `H^{2k} = 𝕜·w^k ≠ 0` and `H^{odd} = 0` (`k ≤ 4`).

The field half is `Work.Pi6.K2Z.fieldHalf` (the two-row forcing argument for the path–loop
fibration, using `Work.Pi6.MSSHolds`); the integral half is `Work.Pi6.K2Z.integralPart_of`, built from
the integral homology computation `Work.Pi6.K2Z.fgFromPrimes`, the degree-local universal
coefficient theorem `Work.Pi6.K2Z.kronH_bij` and the multiplicative coefficient reduction
`Work.Pi6.K2Z.redNat`. -/
theorem k2zFacts (hM : Work.Pi6.MSSHolds) : Work.Pi6.K2ZFacts := by
  intro X _inst x₀ N hN hX
  refine ⟨?_, ?_⟩
  · refine Work.Pi6.K2Z.integralPart_of x₀ N hN hX ?_ ?_ ?_ ?_
    · exact Work.Pi6.K2Z.fgFromPrimes hM X x₀ N hN hX
    · intro n hn
      exact Work.Pi6.K2Z.kronH_bij X n hn
    · intro 𝕜 _
      exact Work.Pi6.K2Z.fieldHalf hM X x₀ N hN hX 𝕜
    · intro p _
      refine ⟨Classical.choose (Work.Pi6.K2Z.redNat p X),
        Classical.choose (Classical.choose_spec (Work.Pi6.K2Z.redNat p X)), ?_, ?_⟩
      · exact (Classical.choose_spec (Classical.choose_spec (Work.Pi6.K2Z.redNat p X))).1
      · intro n x c
        exact (Classical.choose_spec (Classical.choose_spec (Work.Pi6.K2Z.redNat p X))).2 n x c
  · intro 𝕜 _
    exact Work.Pi6.K2Z.fieldHalf hM X x₀ N hN hX 𝕜

end Work.Pi6
