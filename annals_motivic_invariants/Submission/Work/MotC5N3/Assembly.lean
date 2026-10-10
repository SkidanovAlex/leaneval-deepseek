import Mathlib
import ChallengeDeps
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotC5N3.AK
import Submission.Work.MotC5N3.CensusAux
import Submission.Work.MotC5N3.CensusNonzero
import Submission.Work.MotC5N3.CharFive
import Submission.Work.MotC5N3.ShiftProj
import Submission.Work.MotC5N3.Nodes.ExistsASData
import Submission.Work.MotC5N3.twistFieldAS_eq
import Submission.Work.MotC5N3.constantsOnly_K_AS
import Submission.Work.MotC5N3.lam_AS
import Submission.Work.MotC5N3.censusAS2_class_sdual
import Submission.Work.MotC5N3.censusAS2_class_sAS
import Submission.Work.MotC5N3.JunkFwVec0
import Submission.Work.MotC5N3.JunkBwVec4
import Submission.Work.MotC5N3.chartIsoAS2
import Submission.Work.MotC5N3.bwVecAS2_four_ne_zero
import Submission.Work.MotC5N3.sAS2_ne_zero
import Submission.Work.MotV5.LinkCert_of_algEquiv
import Submission.Work.MotWire.CertN3
import Submission.Work.MotV5.exists_kleinData_shiftProj

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The generic AS census and the nodes G-LK, N5

* `censusAS2Gen` — the eleven clauses of `Work.MotC5N3.CensusAS2Gen` for the Klein data
  `(aK K D, bK K D)` and an arbitrary class `g ∉ ℘(K)`, assembled from the pieces proved in
  `Submission/Work/MotC5N3/`;
* `linkCertAS` — **G-LK**: the Crauder–Katz link certificate `Work.MotV.LinkCert K` between the two
  Artin–Schreier twists `Work.MotC5N3.twistFieldAS D g` and `Work.MotC5N3.twistFieldAS D (2 • g)`;
* `not_gen_three_of_val_charFive` — **N5**: `¬ GenByPseudoRegularizable K 3` for every infinite field
  `K` of characteristic `5` carrying a discrete valuation `v : K → ℤᵐ⁰` with a uniformiser.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

-- `ℤᵐ⁰` is the *scoped* notation `WithZero (Multiplicative ℤ)`; this file had never been
-- elaborated before (its whole dependency chain was still blocked), so the `open scoped` was
-- missing.  Without it the notation does not parse.
open scoped WithZero

namespace Work.MotC5N3
noncomputable section

open Work.MotC5N3

/-- **The generic AS census for the Klein datum `D` and the class `g`**, assembled from its eleven
clauses: the `sdualAS2` class clause (`censusAS2_class_sdual`), the `sAS2` clause
(`censusAS2_class_sAS`), the two vacuous/`linAS2`-clauses (`censusAS2_linAS`,
`censusAS2_cubAS_of_bwVec4`), the two junk clauses (`JunkFwVec0`, `JunkBwVec4`), the two
non-vanishing divisors (`FdivAS2_ne_zero`, `GdivAS2_ne_zero` with `sAS2_ne_zero`,
`bwVecAS2_four_ne_zero`, `sdualAS2_ne_zero`) and the chart isomorphism (`chartIsoAS2`). -/
theorem censusAS2Gen (K : Type) [Field K] [CharP K 5] {𝕜 : Type} [Field 𝕜] [Algebra 𝕜 K]
    (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) (g : K)
    (hg : ¬ ∃ u : K, u ^ 5 - u = g) : CensusAS2Gen K D hD g := by
  obtain ⟨hpr, hht, hres⟩ := censusAS2_class_sdual K D hD g hg
  exact ⟨hpr, hht, hres,
    censusAS2_class_sAS K D hD g hg,
    censusAS2_linAS (aK K D) (bK K D) (aK_sq_sub_ne D hD),
    censusAS2_cubAS_of_bwVec4 (aK K D) (bK K D) g (aK_sq_sub_ne D hD)
      (JunkBwVec4 K D hD g hg),
    JunkFwVec0 K D hD g hg,
    JunkBwVec4 K D hD g hg,
    FdivAS2_ne_zero K D hD g hg (sAS2_ne_zero K D hD g hg),
    GdivAS2_ne_zero K D hD g (bwVecAS2_four_ne_zero K D hD g hg)
      (sdualAS2_ne_zero K D g hht),
    chartIsoAS2 K D hD g⟩

/-- **G-LK**: the Crauder–Katz link certificate between the two Artin–Schreier twist fields of the
Klein curve over the base field `K` itself. -/
theorem linkCertAS (K : Type) [Field K] [CharP K 5] {𝕜 : Type} [Field 𝕜] [Algebra 𝕜 K]
    (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) (g : K)
    (hg : ¬ ∃ u : K, u ^ 5 - u = g) :
    Nonempty (Work.MotV.LinkCert K ↥(twistFieldAS D g) ↥(twistFieldAS D (2 • g))) :=
  linkCertAS_of_censusAS2_gen K D hD g (censusAS2Gen K D hD g hg)

/-- **N5**: the `n = 3` characteristic-`5` result over any infinite field with a discrete
valuation (the char-5 analogue of `Work.MotT.not_gen_three_of_val`). -/
theorem not_gen_three_of_val_charFive (K : Type) [Field K] [Infinite K] (hk : ringChar K = 5)
    (v : Valuation K ℤᵐ⁰) {π : K} (hπ : v π = Work.MotT.vOne) :
    ¬ MotivicInvariants.GenByPseudoRegularizable K 3 := by
  haveI : CharP K 5 := by rw [← hk]; exact ringChar.charP K
  have hg := not_mem_pe_inv_uniformizer v hπ
  have hD : Work.MotV5.KleinData.ASGood (Work.MotV5.D11 K) :=
    ⟨Work.MotV5.good11 K, Work.MotV5.nonconstant11 K, Work.MotV5.generates11 K,
      Work.MotV5.D11_smooth K⟩
  obtain ⟨τ, τ₂, σS, σ, σ₂, h1, h2⟩ :=
    Nodes.exists_ASData K (Work.MotV5.D11 K) hD (D11_shiftCompatProj K (K := K)) π⁻¹ hg
  obtain ⟨L⟩ := linkCertAS K (Work.MotV5.D11 K) hD π⁻¹ hg
  obtain ⟨L'⟩ := Work.MotV5.LinkCert_of_algEquiv
    (IntermediateField.equivOfEq (twistFieldAS_eq K (Work.MotV5.D11 K) hD _ τ σS σ h1))
    (IntermediateField.equivOfEq (twistFieldAS_eq K (Work.MotV5.D11 K) hD _ τ₂ σS σ₂ h2)) L
  have hCO := constantsOnly_K_AS K (Work.MotV5.D11 K) hD π⁻¹ hg π⁻¹ (Or.inl rfl) τ σS σ h1
  have hR := rigidity_AS_val_of_lam lam_AS K (Work.MotV5.D11 K) hD v (by simp) (by simp) (by simp)
    hπ τ τ₂ σS σ σ₂ h1 h2
  exact Work.MotWire.not_gen_three_of_linkCert K L' hCO hR

end
end Work.MotC5N3
