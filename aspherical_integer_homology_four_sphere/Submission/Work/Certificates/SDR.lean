/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `Certificates/`: strong deformation retract certificates

An `SDR C` is the data showing that the complex `C` is homotopy equivalent to the complex with
`b k` free generators in degree `k` and zero boundary maps: sparse maps

* `Z k : ℤ^{(b k)} → C_k` (sends the generators to cycles),
* `ρ k : C_k → ℤ^{(b k)}` (kills boundaries),
* `h k : C_k → C_{k+1}` (a homotopy),

subject to `∂Z = 0`, `ρ∂ = 0`, `ρZ = 1` and `1 - Zρ = ∂h + h∂`.  `SDR.check` decides these
equations *sparsely* (on the generators of the free modules), and `SDR.sound` turns a passing
check into the isomorphism `H_k(C) ≅ ℤ^{(b k)}` -- see `Submission/Work/Certificates/SDR/sound.lean`.
-/

import Mathlib
import Submission.Work.Certificates.Sparse
import Submission.Work.Certificates.ChainCx

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Certificates

/-- A strong-deformation-retract certificate for the chain complex `C`: sparse maps `Z`, `ρ`,
`h` showing that `C` retracts onto `ℤ^{(b k)}` in each degree.  `N` bounds the interesting
degrees: `C` is zero in degree `≥ N` and `b` vanishes there. -/
structure SDR (C : FinChainCx) where
  /-- The degree bound: above `N` everything is zero. -/
  N : ℕ
  /-- The ranks `b k` of the homology. -/
  b : ℕ → ℕ
  /-- `Z k : ℤ^{(b k)} → C_k`, the section (its image consists of cycles). -/
  Z : ∀ k, SOp (C.dim k) (b k)
  /-- `ρ k : C_k → ℤ^{(b k)}`, the retraction. -/
  ρ : ∀ k, SOp (b k) (C.dim k)
  /-- `h k : C_k → C_{k+1}`, the homotopy. -/
  h : ∀ k, SOp (C.dim (k+1)) (C.dim k)
  /-- `C` has no cells in degree `≥ N`. -/
  dim_zero : ∀ k, N ≤ k → C.dim k = 0
  /-- `b` vanishes in degree `≥ N`. -/
  b_zero : ∀ k, N ≤ k → b k = 0

namespace SDR

variable {C : FinChainCx}

/-- The four equations at degree `k` (`∂Z = 0` and `ρ∂ = 0` in degree `k+1`, `ρZ = 1` in
degree `k`, and `1 - Zρ = ∂h + h∂` in degree `k+1`), evaluated sparsely. -/
def checkDeg (S : SDR C) (k : ℕ) : Bool :=
  ((C.bd k).mul (S.Z (k+1))).eqb (SOp.zero (C.dim k) (S.b (k+1))) &&
  ((S.ρ k).mul (C.bd k)).eqb (SOp.zero (S.b k) (C.dim (k+1))) &&
  ((S.ρ k).mul (S.Z k)).eqb (SOp.id (S.b k)) &&
  ((SOp.id (C.dim (k+1))).sub ((S.Z (k+1)).mul (S.ρ (k+1)))).eqb
      (((C.bd (k+1)).mul (S.h (k+1))).add ((S.h k).mul (C.bd k)))

/-- The check of an `SDR` certificate: `∂Z = 0`, `ρ∂ = 0`, `ρZ = 1` and `1 - Zρ = ∂h + h∂`,
in all degrees up to `N` (the remaining ones are zero automatically, by `dim_zero`/`b_zero`).
Degrees above `N` are covered by the `N`-th iteration and by the triviality of `SOp 0 0`. -/
def check (S : SDR C) : Bool :=
  ((SOp.id (C.dim 0)).sub ((S.Z 0).mul (S.ρ 0))).eqb ((C.bd 0).mul (S.h 0)) &&
  (List.range S.N).all S.checkDeg

/-- `∂ Z = 0` in degree `k + 1`. -/
def checkZ (S : SDR C) (k : ℕ) : Bool :=
  ((C.bd k).mul (S.Z (k+1))).eqb (SOp.zero (C.dim k) (S.b (k+1)))

/-- `ρ ∂ = 0` in degree `k + 1`. -/
def checkRho (S : SDR C) (k : ℕ) : Bool :=
  ((S.ρ k).mul (C.bd k)).eqb (SOp.zero (S.b k) (C.dim (k+1)))

/-- `ρ Z = 1` in degree `k`. -/
def checkRhoZ (S : SDR C) (k : ℕ) : Bool :=
  ((S.ρ k).mul (S.Z k)).eqb (SOp.id (S.b k))

/-- `1 - Z ρ = ∂ h + h ∂` in degree `k + 1`. -/
def checkHom (S : SDR C) (k : ℕ) : Bool :=
  ((SOp.id (C.dim (k+1))).sub ((S.Z (k+1)).mul (S.ρ (k+1)))).eqb
    (((C.bd (k+1)).mul (S.h (k+1))).add ((S.h k).mul (C.bd k)))

/-- `1 - Z ρ = ∂ h` in degree `0` (there is no `∂` below degree `0`). -/
def checkHomZero (S : SDR C) : Bool :=
  ((SOp.id (C.dim 0)).sub ((S.Z 0).mul (S.ρ 0))).eqb ((C.bd 0).mul (S.h 0))

/-- `checkDeg` is the conjunction of the four sparse equations of degree `k`. -/
theorem checkDeg_eq (S : SDR C) (k : ℕ) :
    S.checkDeg k = (S.checkZ k && S.checkRho k && S.checkRhoZ k && S.checkHom k) := rfl

/-- `check` is the degree-`0` homotopy equation together with the four equations in every
degree below `N`: the form in which the check can be verified one degree at a time (the
kernel cost of a single `decide` is proportional to the data of that degree). -/
theorem check_eq (S : SDR C) :
    S.check = (S.checkHomZero && (List.range S.N).all
      (fun k => S.checkZ k && S.checkRho k && S.checkRhoZ k && S.checkHom k)) := rfl

end SDR

end Work.Certificates
