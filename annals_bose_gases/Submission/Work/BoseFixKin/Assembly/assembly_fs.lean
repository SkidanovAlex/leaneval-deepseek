import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseFixKin.Assembly.core_budget_fs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixKin.Assembly.assembly_fs` — the momentum-space budget on the coupled regime

Node N2 of `BOSE_BCLASH_LEAD.md`.  The pointwise budget in momentum space

```
(1+K)/2 · ε_T (dℓ)⁻² raSym ℓ d p + b (1/2)⁻¹ ‖p‖²/(ℓ²‖p‖²+1/2)
  + (1−ε_T) tprSym ℓ (2s) C p + ε_T tprSym ℓ (2ds) C p  ≤  ‖p‖²
```

for every `(ℓ,d,s,ε_T,b) ∈ KinRegimeFS (cFS K C)` and every `p`.  It is the reduction of the
scalar three-region budget `core_budget_fs` (node N1) along the box-momentum scaling
`q = ℓ‖p‖`: multiply by `ℓ² > 0` and use the three scaling identities
`raTerm_scale`, `gapTerm_scale`, `tprSym_scale` of `Work.BoseKinLoc.Assembly.assembly_two_regime`.

The difference from `Work.BoseKinLoc.Assembly.AssemblySymbolAt`'s version is exactly the
momentum factor `(1+K)/2` on the first term (and the coupled regime `KinRegimeFS`), which is what
the crude `MomBound`'s existential `b₀` contributes through `K = 1/(16 b₀)`.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixKin.Assembly

open Work.BoseFixKin
open Work.BoseKinLoc Work.BoseKinLoc.Assembly

/-- **The momentum-space budget on the coupled regime** (node N2). -/
theorem assembly_fs {K C : ℝ} (hK : 0 ≤ K) (hC : 0 < C) :
    ∀ ℓ d s εT b : ℝ, KinRegimeFS (cFS K C) ℓ d s εT b → ∀ p : ℝ³,
      (1 + K) / 2 * εT * (d * ℓ) ^ (-2 : ℤ) * raSym ℓ d p
        + b * (1 / 2 : ℝ)⁻¹ * (‖p‖ ^ 2 / (ℓ ^ 2 * ‖p‖ ^ 2 + 1 / 2))
        + ((1 - εT) * tprSym ℓ (2 * s) C p + εT * tprSym ℓ (2 * (d * s)) C p)
      ≤ ‖p‖ ^ 2 := by
  intro ℓ d s εT b hreg p
  obtain ⟨hℓ, hd, hd1, hs, hsc, hε, hεc, hcpl, hb, hbc⟩ := hreg
  set q : ℝ := ℓ * ‖p‖ with hqdef
  have hℓ2 : 0 < ℓ ^ 2 := by positivity
  have hcore := core_budget_fs (q := q) hK hC (by positivity) hd hd1 hs hsc hε.le hεc hcpl
    hb.le hbc
  have e1 : ℓ ^ 2 * ((1 + K) / 2 * εT * (d * ℓ) ^ (-2 : ℤ) * raSym ℓ d p)
      = (1 + K) / 2 * εT * q ^ 2 / (1 + d ^ 2 * q ^ 2) := by
    have h := Work.BoseKinLoc.Assembly.raTerm_scale ℓ d hℓ hd p
    rw [← hqdef] at h
    rw [show ℓ ^ 2 * ((1 + K) / 2 * εT * (d * ℓ) ^ (-2 : ℤ) * raSym ℓ d p)
        = (1 + K) / 2 * εT * (ℓ ^ 2 * ((d * ℓ) ^ (-2 : ℤ) * raSym ℓ d p)) by ring, h]
    ring
  have e2 : ℓ ^ 2 * (b * (1 / 2 : ℝ)⁻¹ * (‖p‖ ^ 2 / (ℓ ^ 2 * ‖p‖ ^ 2 + 1 / 2)))
      = b * (1 / 2 : ℝ)⁻¹ * (q ^ 2 / (q ^ 2 + 1 / 2)) := by
    have h := Work.BoseKinLoc.Assembly.gapTerm_scale ℓ (1 / 2) hℓ p
    rw [← hqdef] at h
    rw [show ℓ ^ 2 * (b * (1 / 2 : ℝ)⁻¹ * (‖p‖ ^ 2 / (ℓ ^ 2 * ‖p‖ ^ 2 + 1 / 2)))
        = b * (1 / 2 : ℝ)⁻¹ * (ℓ ^ 2 * (‖p‖ ^ 2 / (ℓ ^ 2 * ‖p‖ ^ 2 + 1 / 2))) by ring, h]
  have e3 : ℓ ^ 2 * ((1 - εT) * tprSym ℓ (2 * s) C p) = (1 - εT) * tprR (2 * s) C q := by
    have h := Work.BoseKinLoc.Assembly.tprSym_scale ℓ (2 * s) C hℓ p
    rw [← hqdef] at h
    rw [show ℓ ^ 2 * ((1 - εT) * tprSym ℓ (2 * s) C p)
        = (1 - εT) * (ℓ ^ 2 * tprSym ℓ (2 * s) C p) by ring, h]
  have e4 : ℓ ^ 2 * (εT * tprSym ℓ (2 * (d * s)) C p) = εT * tprR (2 * (d * s)) C q := by
    have h := Work.BoseKinLoc.Assembly.tprSym_scale ℓ (2 * (d * s)) C hℓ p
    rw [← hqdef] at h
    rw [show ℓ ^ 2 * (εT * tprSym ℓ (2 * (d * s)) C p)
        = εT * (ℓ ^ 2 * tprSym ℓ (2 * (d * s)) C p) by ring, h]
  have e5 : ℓ ^ 2 * ‖p‖ ^ 2 = q ^ 2 := by rw [hqdef]; ring
  apply (mul_le_mul_iff_of_pos_left hℓ2).mp
  rw [mul_add, mul_add, mul_add, e1, e2, e3, e4, e5]
  linarith [hcore]

end Work.BoseFixKin.Assembly
