/-
# `Work.FQC.Height` — the height-shift theorem

This file assembles the quasiconformal deformation of the attracting Écalle cylinder
(Hubbard–Schleicher §2 / Nakane–Schleicher Theorem 3.2) into the statement consumed by the
`F` side of the mandelbar drive:

`∀ h : ℝ, ∃ c₂, ∃ d₂ : RootParabolic c₂, critHeight d₂ = h`

— i.e. every real value occurs as the critical Écalle height of a root-parabolic parameter.

The pipeline is

1. `conj_is_tricorn` : the principal solution `θ = principal (muQC d fl t)` of the invariant
   Beltrami coefficient `muQC d fl t` conjugates `T_c` to another antipolynomial `T_{c₂}`
   (M2′ + Liouville);
2. `zero_of_conj` : such a `θ` fixes `0`, so it carries the critical orbit of `T_c` to the
   critical orbit of `T_{c₂}`;
3. `transfer_parabolic` : `π` transfers the root-parabolic structure, giving `d₂ : RootParabolic c₂`;
4. `height_after` : the transported Fatou coordinate `ℓ_t ∘ φa ∘ θ⁻¹` realises the new parameter,
   and (with MNS's phase normalisation) shifts the critical height by `t/2`.

The remaining inputs are those of `EcalleInput` in `Work.FQC.Flower`: the flower with MNS's phase
normalisation, the petal structure (`PetalInput`), the petal-direction input (`SimpleTransfer`) and
the uniqueness of the Fatou coordinate up to a real constant (`FatouUnique`).
-/
import Mathlib
import Submission.Work.FQC.Flower
import Submission.Work.FQC.Petal
import Submission.Work.FQC.conj_is_tricorn_pg
import Submission.Work.FQC.zero_of_conj
import Submission.Work.FQC.transfer_parabolic
import Submission.Work.FQC.height_after_pg
import Submission.Work.FQC.muQC_admissible_pg
import Submission.Work.FQC.transfer_bottcher
import Submission.Work.FQC.transfer_rays

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology ComplexConjugate
open MeasureTheory Filter Set Function
open Classical

noncomputable section

namespace Work.FQC

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.EL (RootParabolic F K)

/-- **The height-shift theorem.**  Every real number is the critical Écalle height of some
root-parabolic parameter: the quasiconformal deformation of the attracting Écalle cylinder moves
the critical height by an arbitrary prescribed amount.

The hypotheses are the inputs of `EcalleInput` (see `Work.FQC.Flower`), written out:

* `fl` : a Leau–Fatou flower of `d`, with the petal structure `hpetal`;
* `hphase` : MNS's phase normalisation `Re φa (tap) ≡ 1/4 (mod 1)`;
* `hsimple` : the petal-direction input on the transferred parabolic point;
* `hU` : uniqueness of the Fatou coordinate up to a real constant. -/
theorem heightShift {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (hpetal : PetalInput d fl)
    (hphase : saw ((fl.φa (phasePoint d fl)).re) = 1 / 2)
    (hsimple : ∀ t : ℝ, SimpleTransfer d fl hpetal.Pg t)
    (hU : FatouUnique) (h : ℝ) :
    ∃ c₂ : ℂ, ∃ d₂ : RootParabolic c₂, critHeight d₂ = h := by
  set t : ℝ := 2 * (h - critHeightAt d (EcalleData.ofFlower d fl)) with ht
  obtain ⟨c₂, hconj⟩ := conj_is_tricorn_pg d fl hpetal t
  have h0 : (Work.MRMT.Found.principal (muQC d fl hpetal.Pg t)) 0 = 0 :=
    zero_of_conj (Work.MRMT.Found.principal (muQC d fl hpetal.Pg t)).bijective hconj
  have hs : iteratedDeriv 2 (F c₂) ((Work.MRMT.Found.principal (muQC d fl hpetal.Pg t)) d.z₁) ≠ 0 :=
    hsimple t c₂ (Work.MRMT.Found.principal (muQC d fl hpetal.Pg t)) rfl hconj
  obtain ⟨d₂⟩ := transfer_parabolic d (Work.MRMT.Found.principal (muQC d fl hpetal.Pg t)) hconj
    (Work.MRMT.Found.principal_decay (muQC_admissible_pg d fl hpetal t)) h0 hs
  obtain ⟨E₂, hE₂⟩ := height_after_pg d fl hpetal t d₂ hconj h0 hphase
  refine ⟨c₂, d₂, ?_⟩
  have hA : critHeight d₂ = critHeightAt d₂ E₂ := hU.eq d₂ (EcalleData.canonical d₂) E₂
  have hB : critHeight d = critHeightAt d (EcalleData.ofFlower d fl) :=
    hU.eq d (EcalleData.canonical d) (EcalleData.ofFlower d fl)
  calc critHeight d₂ = critHeightAt d₂ E₂ := hA
    _ = critHeightAt d (EcalleData.ofFlower d fl) + t / 2 := hE₂
    _ = critHeight d + t / 2 := by rw [← hB]
    _ = h := by rw [ht, hB]; ring

end Work.FQC

end
