/-
# SeedPortraitCert — the rays `12/33` and `13/33` do not land at the parabolic point

Area `Submission/Work/SeedPortraitCert/`.  The chain (`Chain.lean`) puts the landing point of the
`12/33`-ray in the periodic family `CTA KT 0` and that of the `13/33`-ray in `CTB KT 0`; the
numerical certificate (`ZbDisj.lean`) says that both sets miss the box `Zb`.  Hence, at any
parameter `c` of the seed box `Xb` and for any point `z₁ ∈ Zb`,

  `¬ LandsN hN (12/33) z₁`   and   `¬ LandsN hN (13/33) z₁`

(the two angles are `372/1023` and `403/1023`).
-/
import Mathlib
import Submission.Work.SeedPortraitCert.ZbDisj

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedPortraitCert

open Work.SeedCertRay
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

noncomputable section

/-- The landing point of the `12/33`-ray is *not* in the box `Zb`: it lies in the periodic
component of the chain, which misses `Zb`. -/
theorem not_landsN_angA0 {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hc : c ∈ Mandelbar) (hc2 : ‖c‖ ≤ 2)
    (hcX : Xb.mem c) {z₁ : ℂ} (hz1 : Zb.mem z₁) : ¬ Work.EL.LandsN hN (angA 0) z₁ := by
  intro h
  exact CTA_KT0_disj z₁ (landsN_mem_CTA hN (chainA hN hφ hc hc2 hcX) h) hz1

/-- The landing point of the `13/33`-ray is *not* in the box `Zb`. -/
theorem not_landsN_angB0 {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hc : c ∈ Mandelbar) (hc2 : ‖c‖ ≤ 2)
    (hcX : Xb.mem c) {z₁ : ℂ} (hz1 : Zb.mem z₁) : ¬ Work.EL.LandsN hN (angB 0) z₁ := by
  intro h
  exact CTB_KT0_disj z₁ (landsN_mem_CTB hN (chainB hN hφ hc hc2 hcX) h) hz1

/-- **`12/33` does not land at `z₁ ∈ Zb`** (the angle `12/33 = 4/11`). -/
theorem not_landsN_12_33 {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hc : c ∈ Mandelbar) (hc2 : ‖c‖ ≤ 2)
    (hcX : Xb.mem c) {z₁ : ℂ} (hz1 : Zb.mem z₁) : ¬ Work.EL.LandsN hN (12 / 33) z₁ := by
  have h := not_landsN_angA0 hN hφ hc hc2 hcX hz1
  rwa [angA_zero] at h

/-- **`13/33` does not land at `z₁ ∈ Zb`.** -/
theorem not_landsN_13_33 {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hc : c ∈ Mandelbar) (hc2 : ‖c‖ ≤ 2)
    (hcX : Xb.mem c) {z₁ : ℂ} (hz1 : Zb.mem z₁) : ¬ Work.EL.LandsN hN (13 / 33) z₁ := by
  have h := not_landsN_angB0 hN hφ hc hc2 hcX hz1
  rwa [angB_zero] at h

/-- **`372/1023 = 12/33` does not land at `z₁ ∈ Zb`** (the form used by the portrait
argument). -/
theorem not_landsN_372 {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hc : c ∈ Mandelbar) (hc2 : ‖c‖ ≤ 2)
    (hcX : Xb.mem c) {z₁ : ℂ} (hz1 : Zb.mem z₁) :
    ¬ Work.EL.LandsN hN ((372 : ℝ) / 1023) z₁ := by
  have h := not_landsN_12_33 hN hφ hc hc2 hcX hz1
  rwa [show ((12 : ℝ) / 33) = (372 : ℝ) / 1023 by norm_num] at h

/-- **`403/1023 = 13/33` does not land at `z₁ ∈ Zb`.** -/
theorem not_landsN_403 {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hc : c ∈ Mandelbar) (hc2 : ‖c‖ ≤ 2)
    (hcX : Xb.mem c) {z₁ : ℂ} (hz1 : Zb.mem z₁) :
    ¬ Work.EL.LandsN hN ((403 : ℝ) / 1023) z₁ := by
  have h := not_landsN_13_33 hN hφ hc hc2 hcX hz1
  rwa [show ((13 : ℝ) / 33) = (403 : ℝ) / 1023 by norm_num] at h

end

end Work.SeedPortraitCert
