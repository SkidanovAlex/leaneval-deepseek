import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.StemsB.WangE4
import Submission.Work.StemsB.CollarModel
import Submission.Work.Rat.coverFibreDataSerre
import Submission.Work.Stems.Engine.C2EvenRange
import Submission.Work.Stems.fibreOfHomeomorphLoopSpace
import Submission.Work.Stems.isHurewiczFibration_homotopyFibreFst
import Submission.Work.Cohomology.PairSequence
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.sphereHomologyZero
import Submission.Work.Stems.sphereConnectivity
import Submission.Work.Stems.HurewiczFirstDegree
import Submission.Work.Pi6.EFACTS.p3Model
import Submission.Work.Pi6.EFACTS.fibreModel
import Submission.Work.Pi6.EFACTS.h3hom
import Submission.Work.Pi6.EFACTS.eHomology
import Submission.Work.Pi6.EFACTS.h4mod2
import Submission.Work.Pi6.EFACTS.modTwoSquare
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-! Guidance from the project lead (the requester):

AREA EFACTS (pi6). Read REFS/NOTES_LEAD_PI6.md §5. Assume MSSHolds and K2ZFacts.
Statement: for E = Ecov g3 (homotopy fibre of a Postnikov section g3 : S3 → P3): H_4(E;ℤ) ≅ ZMod 2, H_5 = 0,
H_6 ≅ ZMod 3, H_7 = 0, and every nonzero u ∈ H^4(E;𝔽₂) has u² ≠ 0.
Integral route: the library's INTEGRAL Wang sequence with derivation over a sphere: Work.StemsB.wangSphereE4
(exactness) + Work.StemsB.wangSphereDerivation_exists (θ is a derivation of degree −(b−1)), for a Hurewicz fibration
p : E → SphModel b with FibrewiseTrivial over sphLoopOuter b and sphLoopBig b. You need: (i) homotopyFibreFst is a
Hurewicz fibration (pullback of the path fibration: isHurewiczFibration_pullbackSnd, isHurewiczFibration_trackMap);
(ii) a homeomorphism Sph 3 ≃ₜ SphModel 3 = OnePoint ℝ³ and transport of all data; (iii) fibrewiseTrivial_of_contraction
on the two contractible pieces. The fibre over s3 is ΩP3, a K(ℤ,2) through 11: K2ZFacts gives H^{2k} = ℤx^k.
E 3-connected ⇒ θ(x) = ±1 ⇒ θ(x^k) = ±k x^{k−1} ⇒ H^{2k+1}(E;ℤ) = ℤ/k, H^{even>0}(E;ℤ) = 0 for k ≤ 4.
To homology without Ext: H^*(E;ℚ) = 0 in positive degrees ≤ 9 (rational Wang, Work.Serre.serreE4, or the ranks) so the
Bockstein of 0 → ℤ → ℚ → ℚ/ℤ → 0 gives H^n(E;ℚ/ℤ) ≅ H^{n+1}(E;ℤ); and H^n(E;ℚ/ℤ) ≅ Hom(H_n(E), ℚ/ℤ) (ℚ/ℤ is injective:
copy the proof of Work.StemsB.fieldDualUCT, it only uses exactness of Hom(−, coefficient)). Finite group with dual ℤ/k is ℤ/k.
Mod-2 square: MSS over 𝔽₂ for E → S3 (two columns): d_3 x = e_3, d_3(x²) = 0 ⇒ x² ∈ E_∞^{0,4} ⇒ (edge_fibre) x² is the
restriction of some u ∈ H^4(E;𝔽₂), and H^4(E;𝔽₂) is 1-dim ⇒ every u ≠ 0 restricts to x², u² restricts to x^4 ≠ 0.
Suggested children: Pi6/EFACTS/hurewiczFib, Pi6/EFACTS/sphModelTransport, Pi6/EFACTS/wangIntegral,
Pi6/EFACTS/qzDuality, Pi6/EFACTS/modTwoSquare.
-/

namespace Work.Pi6

/-- **π₆ of the 3-sphere, through the cover `E = S³⟨3⟩`.**

The integral cohomology of `E` in degrees `4…8` (`Work.Pi6.EFACTS.eCoh`, from the **integral** Wang
sequence of `E → S³` with fibre `K(ℤ,2)`, whose transgression multiplicativity is proved in
`Work.Pi6.EFACTS.Z/`) gives `H⁴ = 0`, `H⁵ ≅ ℤ/2`, `H⁶ = 0`, `H⁷ ≅ ℤ/3`, `H⁸ = 0`.  The universal
coefficient theorem (`Work.Pi6.UCT.uctZ`, clause (B)) together with the rational acyclicity then
transports this to `H₄(E) ≅ ℤ/2`, `H₅(E) = 0`, `H₆(E) ≅ ℤ/3`, `H₇(E) = 0`
(`Work.Pi6.EFACTS.eHomology`), and the mod-2 square — `H⁴(E;𝔽₂) ≅ 𝔽₂` by the coefficient change
`h4mod2`, every nonzero class restricting to `x²` in the fibre — is
`Work.Pi6.EFACTS.modTwoSquare`. -/
theorem eFacts (hM : Work.Pi6.MSSHolds) (hZ : Work.Pi6.K2ZFacts) : Work.Pi6.EFacts := by
  intro P3 _ g3 hP3
  have hfib : Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) 11 (Work.Pi6.EFACTS.fib g3)
      (Work.Pi6.EFACTS.fibPt g3) :=
    Work.Pi6.EFACTS.fibreModel g3 (Work.Pi6.EFACTS.p3Model g3 hP3)
  obtain ⟨hh4, hh5, hh6, hh7⟩ := Work.Pi6.EFACTS.eHomology g3 hP3 hfib hZ
  have h3h : Subsingleton (Work.Pi6.HR ℤ (Work.Pi6.Ecov g3) 3) :=
    Work.Pi6.EFACTS.h3hom g3 hP3
  have h4 : Nonempty (Work.Pi6.Coh (ZMod 2) (Work.Pi6.Ecov g3) 4 ≃ₗ[ZMod 2] ZMod 2) :=
    Work.Pi6.EFACTS.h4mod2 g3 hh4 h3h
  exact ⟨hh4, hh5, hh6, hh7, Work.Pi6.EFACTS.modTwoSquare g3 hM hfib hZ h4⟩

end Work.Pi6
