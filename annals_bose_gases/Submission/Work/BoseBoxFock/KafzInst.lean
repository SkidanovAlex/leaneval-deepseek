import ChallengeDeps
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Work.BoseBoxFock.hNH_honest
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.KafzInst` — the dictionary of `H2ndHon`, instantiated

`KafzDict.hW_H2ndF` and `KafzDict.bomb_H2ndF_eq_integral` are stated for an abstract
family `(f, g, NH, PHs, E, gHat0)`.  This file instantiates them at the honest model
`Work.BoseBoxFock.H2ndHon` (FS `eq:HLambdaSecond` on the honest modes), using
`hNH_honest` for the transport of the high-momentum number `n₊^H`.

Deliverables:
* `BNHHon` — the spectator operator `BNH` with `split (NH_H y) = lift (BNHHon) (split y)`;
* `KvecHon` — the 25-slot spectator family of `H2ndHon`;
* `hW_H2ndHon` — the dictionary `split (H2ndHon x) = (Σ_{i<25} monoOp (pvecF i) (qvecF i)
  (KvecHon … i)) (split x)`;
* `bomb_H2ndHon_eq_integral` — the exact `c`-number substitution at the honest model.
-/

noncomputable section

open scoped BigOperators Real Topology

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

/-- The spectator operator `BNH` of the honest `n₊^H`: the exact RHS of
`hNH_honest`, i.e. `(1/32)Σ_{k} η_H(k) a_k^C†a_k^C` in the complex Fock space of the
excited modes. -/
noncomputable def BNHHon (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) :
    cfock (Excited (HM μ).m) →ₗ[ℂ] cfock (Excited (HM μ).m) :=
  (1 / 32 : ℂ) • ∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N),
    (((etaH fu (((Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl
          * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2) ^ (-(1 : ℝ))
          * Real.sqrt (μ * BoseGases.a v))
        (kmomLab (ellH v μ) (HM μ).N k)) : ℝ) : ℂ) •
      ((creOfE ((HM μ).f k)).comp (annOfE ((HM μ).f k)))

/-- The 25-slot spectator family of the honest dictionary. -/
noncomputable def KvecHon (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) :
    ℕ → cfock (Excited (HM μ).m) →ₗ[ℂ] cfock (Excited (HM μ).m) :=
  KvecF (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
    ((HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
    (HonestBoxFam v h fc fu HM μ).E (8 * π * BoseGases.a v)

/-- `split (NH y) = lift (BNHHon …) (split y)` at the honest family. -/
theorem hNH_BNHHon (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) :
    ∀ y : RealFock (HM μ).m,
      split ((HonestBoxFam v h fc fu HM μ).T.NH y)
        = lift (BNHHon v h fc fu HM μ) (split y) := by
  intro y
  rw [hNH_honest (v := v) (h := h) (fc := fc) (fu := fu) (HM := HM) μ y]
  rfl

/-- The `θ`-mode annihilation of the honest family transports under `split`. -/
theorem hTa_honest (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (s : Lab (HM μ).N) (hs : s ≠ 0)
    (y : RealFock (HM μ).m) :
    split ((HonestBoxFam v h fc fu HM μ).T.ta s y)
      = lift (annOfE ((HM μ).g s)) (split y) :=
  split_annOf ((HM μ).g s) ((HM μ).hg0 s hs) y

/-- The `θ`-mode creation of the honest family transports under `split`. -/
theorem hTaDag_honest (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (s : Lab (HM μ).N) (hs : s ≠ 0)
    (y : RealFock (HM μ).m) :
    split ((HonestBoxFam v h fc fu HM μ).T.taDag s y)
      = lift (creOfE ((HM μ).g s)) (split y) :=
  split_creOf ((HM μ).g s) ((HM μ).hg0 s hs) y

/-- **The dictionary of `H2ndHon`.** -/
theorem hW_H2ndHon (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) :
    ∀ y : RealFock (HM μ).m,
      split (H2ndHon v h fc fu HM μ y)
        = (∑ i ∈ Finset.range 25,
            monoOp (pvecF i) (qvecF i) (KvecHon v h fc fu HM μ i)) (split y) := by
  intro y
  exact hW_H2ndF (f := (HM μ).f) (g := (HM μ).g) (NH := (HonestBoxFam v h fc fu HM μ).T.NH)
    (BNH := BNHHon v h fc fu HM μ)
    (PHs := (HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
    (E := (HonestBoxFam v h fc fu HM μ).E) (gHat0 := 8 * π * BoseGases.a v)
    (hNH_BNHHon v h fc fu HM μ) (HM μ).hf0 (HM μ).hg0 y

/-- **The exact `c`-number substitution at the honest model** (FS `eq:IntroK(z)`). -/
theorem bomb_H2ndHon_eq_integral (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ)
    (Ψ : RealFock (HM μ).m) :
    bomb (HM μ).m Ψ (H2ndHon v h fc fu HM μ Ψ)
      = ∫ z : ℂ, (∑ i ∈ Finset.range 25,
            z ^ (pvecF i) * (starRingEnd ℂ z) ^ (qvecF i) *
              inner ℂ (Phi (split Ψ) z) (KvecHon v h fc fu HM μ i (Phi (split Ψ) z))).re
          ∂gauss := by
  exact bomb_H2ndF_eq_integral (f := (HM μ).f) (g := (HM μ).g)
    (NH := (HonestBoxFam v h fc fu HM μ).T.NH) (BNH := BNHHon v h fc fu HM μ)
    (PHs := (HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
    (E := (HonestBoxFam v h fc fu HM μ).E) (gHat0 := 8 * π * BoseGases.a v)
    (hNH_BNHHon v h fc fu HM μ) (HM μ).hf0 (HM μ).hg0 Ψ

end Work.BoseBoxFock
