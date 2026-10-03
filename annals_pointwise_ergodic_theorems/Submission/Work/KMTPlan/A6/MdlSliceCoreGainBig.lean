/-
# `Work.KMTPlan.A6.MdlSliceCoreGainBig` — the frozen-`t` core of the large-scale model
estimate at `(2,2,1)` (paper `model-est-2`, `all-all-large-2`)

This file contains the target
`Work.KMTPlan.A6.MdlSliceCoreGain P r C₀ j₁ j₂` (Krause–Mirek–Tao, *Pointwise ergodic theorems
for non-conventional bilinear polynomial averages*, Annals 195 (2022), §8, Theorem `model-est-2`,
estimate `all-all-large-2` at `(p₁,p₂,p) = (2,2,1)`).

## CRITICAL PATH: this file's target is the remaining input of area A6

`Submission/Work/KMTPlan/A6/LowModelGainEstimate.lean` (sorry-free) proves
`Work.KMTPlan.A6.LowModelGain` from `MdlSliceCoreGainBig` at `j₁ = j₂ = 0`; the whole A6 chain
(`LowModelGain` → `LowCase` → `AreaA6`) therefore rests on this theorem.

## Structure (2026-10-03): the import cycle broken by a port

`MdlSliceCoreGainMemLp` (defined in `Submission.Work.A6Big.Defs`, re-exported here) is the
`ℓ²`-case of the target, and essentially the whole §8 assembly of the workspace is stated in terms
of it — so every module of that assembly imports *this* file and could never be imported by it.
The port under `Submission/Work/A6Big/` breaks the cycle: it carries a copy of the team's §8 chain
(84 modules, ≈ 22 000 lines — the transitive importers of this file) in which the import of
`Submission.Work.KMTPlan.A6.MdlSliceCoreGainBig` is replaced by
`Submission.Work.A6Big.Defs`.  Declaration *names* are namespace- not file-bound, so the bodies are
verbatim; only the few files broken by concurrent edits of the original lane needed local repair.
The port is a *snapshot*: re-sync it from the originals when those change (see
`_bigscratch/mkport.py`).

The final assembly of the port is `Submission/Work/A6Big/Wiring.lean`:
`Work.KMTPlan.A6.MdlSliceCoreGainProved` assembles `MdlSliceCoreGain` from the gated §8 adelic form
`A6Clean.adelicFormPropRangePosB`, the loss-form (no-gain) slice bound `A6Clean.mdlSliceNoGain`,
the `ZMod Q` variational chain `ZModVariationalChainProb`, the finitely many bad scales
`MdlSliceBadPart`, the loss absorption `lossAbsorbTwo` and the case-splitting consumer
`A6Clean.MdlSliceCoreGainMemLp_of_pieces_split`, together with the exponent reduction
`exists_range_le_vr` (`variationalNorm` is antitone in the exponent, and the arithmetic inputs hold
only for `2 < r < 2d/(d-1) = adelicRTop P`).

## What is in this file

* the target `MdlSliceCoreGainBig`, proved by `Submission/Work/KMTPlan/A6Lead/coreGainWiring.lean`
  (`Work.KMTPlan.A6Lead.MdlSliceCoreGainWired`) from the *corrected* gated §8 adelic producer
  `Work.KMTPlan.A6Lead.adelicFormPropRangePosBLead` and the PROVED loss-form slice bound
  `Work.KMTPlan.A6LH.MdlSliceNoGainAtProved`;
* the definitions `mdlSliceF`, `mdlSliceG`, `mdlSliceJ_eq_Btwist`, `mdlSliceSymbF/G`,
  `MdlSliceCoreGainMemLp` and the `ℓ²`-reduction `MdlSliceCoreGain_of_memLp` now live in
  `Submission.Work.A6Big.Defs` and are re-exported here (importing is transitive, so every module
  that imported this file for those names still sees them).

(An earlier revision of this file imported `Submission.Work.A6Big.Wiring`, a *copy* of the §8
assembly under `Submission/Work/A6Big/`.  That copy makes every consumer of this file load the
whole copied chain, whose declarations duplicate the `KMTPlan` originals — which is a hard build
error for any module that also imports the originals.  The copy is therefore no longer used here;
the definitions module `Submission.Work.A6Big.Defs` is the only part of the copy this file needs,
and it is clash-free.)
-/
import Submission.Work.KMTPlan.A6Lead.coreGainWiring

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.KMTPlan.A6

/-- **The frozen-`t` core estimate of the large-scale model tuple** (paper Theorem
`model-est-2`, estimate `all-all-large-2` at `(p₁,p₂,p) = (2,2,1)`, for each fixed `t ∈ [1/2,1]`).
Proved from the §8 assembly, see the module docstring. -/
theorem MdlSliceCoreGainBig (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (hA1 : Work.KMTContract.AreaA1)
    (hI : Work.KMTContract.ImprovKMT P)
    (j₁ j₂ : ℤ) (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ)) :
    Work.KMTPlan.A6.MdlSliceCoreGain P r C₀ j₁ j₂ :=
  Work.KMTPlan.A6Lead.MdlSliceCoreGainWired P hd r hr C₀ hC₀ hA1 hI j₁ j₂ hj₁ hj₂

end Work.KMTPlan.A6
