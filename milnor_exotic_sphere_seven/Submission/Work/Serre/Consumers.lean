import Submission.Work.Serre.Models
import Submission.Work.Serre.Engine
import Submission.Work.Serre.serreE0
import Submission.Work.Serre.serreE2a
import Submission.Work.Serre.serreE2b
import Submission.Work.Serre.serreE2d
import Submission.Work.Serre.serreK2
import Submission.Work.Serre.serrePostnikov
import Submission.Work.Serre.serreE0OfRange
import Submission.Work.Serre.serreAugmentationZero
import Submission.Work.Serre.piMapN_monoidHom
import Submission.Work.Serre.isEMSpace_of_homotopyEquiv
import Submission.Work.Serre.loopSpace_isEMSpace
import Submission.Work.Serre.StableExact
import Submission.Work.Serre.serreE4
import Submission.Work.Drive.RationalHurewicz
import Submission.Work.RatHurewicz.Consumers
import Submission.Work.RatHurewicz.SphereConnectivity
import Submission.Work.StemsB.RatVanishing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# SUBPROJECT SERRE — the consumers S1, S2, S3

`Submission/Work/Drive/SERRE_BLUEPRINT.md` §3.

* `Work.Serre.SerreS1` — **rational vanishing Hurewicz**: `(k-1)`-connected plus vanishing rational
  homology in degrees `≤ M ≤ 2k-2` implies torsion homotopy groups in those degrees.
* `Work.Serre.SerreS2` — the drive's contract `Work.Drive.StableStemsTorsion` itself.  Two
  unconditional reductions are proved here from the workspace:
  `Work.RatHurewicz.RationalHurewiczStable` (the RATHUREWICZ crux) and
  `Work.StemsB.RatVanishesStems` both imply it.
* `Work.Serre.SerreS3` — the drive's `Work.Drive.RationalHurewiczStable3`, whose assembly is
  RATHUREWICZ's.

The *assemblies* of the blueprint (S1 from C0 + C3 + E3(a); S2 from C0 + C2(odd) + S1) are recorded
as the `Prop`s `SerreS1OfC0C3E3a`, `SerreS2OfC0C2oddS1`, `SerreS3OfC0C2S1` and
`SerreC2OfC0E3aE3b`; they are the remaining formalisation debt of this chapter.

## Index conventions

`PiTorsion X x₀ m` is "`π_{m+1}(X,x₀)` is torsion", which is the shape of
`Work.Drive.StableStemsTorsion`; a statement about `π_j` is written with `m = j - 1`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

/-! ## S1 — rational vanishing Hurewicz -/

/-- **S1 (blueprint §3).**  *Rational vanishing Hurewicz.*  Let `X` be `(k-1)`-connected
(`k ≥ 2`) and suppose that `H_{m+1}(X;ℚ) = 0` for `k ≤ m+1 ≤ M`, where `M ≤ 2k-2` (the range of the
rational Hurewicz theorem).  Then `π_{m+1}(X,x₀)` is a torsion group for `k ≤ m+1 ≤ M`.

The blueprint's proof: kill the homotopy groups one at a time; the fibre `ΩP_m(X) = K(π_m X, m-1)`
of `X → P_m(X)` has torsion `π_m X` and is therefore rationally acyclic (C3), so E3(a) preserves
the vanishing of the rational homology, and the first-degree integral Hurewicz theorem identifies
`π_m(X)` with the (torsion) group `H_m(X;ℤ)`.  Iterating up to `M` gives the statement. -/
def SerreS1 : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (X : Type) [TopologicalSpace X] (x₀ : X),
    (∀ i < k, Subsingleton (HomotopyGroup (Fin i) X x₀)) →
    ∀ M : ℕ, M ≤ 2 * k - 2 →
      (∀ m : ℕ, k ≤ m + 1 → m + 1 ≤ M → IsZero (ratH (TopCat.of X) (m + 1))) →
      ∀ m : ℕ, k ≤ m + 1 → m + 1 ≤ M → PiTorsion X x₀ m

/-- **S1 is implied by the workspace's rational Hurewicz contract**
(`Work.Drive.RationalHurewiczStable`, the RATHUREWICZ crux): given the vanishing of `H_{m+1}(X;ℚ)`,
the integral homology in that degree is torsion
(`Work.RatHurewicz.torsion_of_subsingleton_ratHomology`), hence so is the Hurewicz image, and the
contract concludes.  This is the *proved* part of S1: the remaining content is the derivation of
S1 from C0 + C3 + E3(a), which is the blueprint's argument. -/
theorem serreS1_of_rationalHurewiczStable (h : Work.Drive.RationalHurewiczStable) : SerreS1 := by
  intro k hk X _ x₀ hconn M hM hvan m hkm hmM
  exact Work.RatHurewicz.pi_torsion_of_ratHomology_vanishing h k hk X x₀ hconn m
    (by omega) (subsingleton_of_isZero (hvan m hkm hmM))

/-! ## S2 — the drive's contract -/

/-- **S2 (blueprint §3).**  The drive's contract: the stable stems `π_{n+j}(Sⁿ)`, `1 ≤ j ≤ 8`, are
torsion.  (`Work.Drive.StableStemsTorsion`, `Submission/Work/Drive/Interfaces.lean`.) -/
def SerreS2 : Prop := Work.Drive.StableStemsTorsion

/-- **S2 from the workspace's rational Hurewicz contract** (proved): the RATHUREWICZ corollary
`Work.RatHurewicz.stableStemsTorsion_of_rationalHurewiczStable'`. -/
theorem serreS2_of_rationalHurewiczStable (h : Work.Drive.RationalHurewiczStable) : SerreS2 :=
  Work.RatHurewicz.stableStemsTorsion_of_rationalHurewiczStable' h

/-- **S2 from the rational vanishing of the stable stems** (proved):
`Work.StemsB.stableStemsTorsion_of_ratVanishes`. -/
theorem serreS2_of_ratVanishesStems (h : Work.StemsB.RatVanishesStems) : SerreS2 :=
  Work.StemsB.stableStemsTorsion_of_ratVanishes h

/-! ## S3 — the short-range rational Hurewicz contract -/

/-- **S3 (blueprint §3).**  `Work.Drive.RationalHurewiczStable3`, the one-degree-short form of the
rational Hurewicz contract that area THOM consumes; its assembly is the subproject RATHUREWICZ's
(`Submission/Work/RatHurewicz/`). -/
def SerreS3 : Prop := Work.Drive.RationalHurewiczStable3

/-- The full contract implies S3 (proved in `Work.Drive`). -/
theorem serreS3_of_rationalHurewiczStable (h : Work.Drive.RationalHurewiczStable) : SerreS3 :=
  Work.Drive.rationalHurewiczStable3_of_stable h

/-! ## The assemblies of the blueprint, as statements

Each is a precise implication between the contract-`Prop`s above, whose proof is the corresponding
piece of the blueprint's argument.  They are the formalisation debt of the chapter: they are
*stated* here (so that they can be attacked), not asserted. -/

/-- **The blueprint's S1 derivation**: Postnikov models (C0), the acyclicity of torsion
Eilenberg–MacLane spaces (C3) and the mapping theorem (E3(a)) imply the rational vanishing
Hurewicz theorem. -/
def SerreS1OfC0C3E3a : Prop := SerreC0 → SerreC3 → SerreE3a → SerreS1

/-- **Freudenthal's suspension theorem, in the form the STEMS contract needs** (blueprint §3,
last line; from homotopy excision, subproject RATHUREWICZ).  For `1 ≤ n` and `i + 3 ≤ n`, torsion
of `π_{n+i+2}(S^{n+1})` implies torsion of `π_{n+i+1}(Sⁿ)`: the suspension
`π_{n+i+1}(Sⁿ) → π_{n+i+2}(S^{n+1})` is an isomorphism in the range `n + i + 1 ≤ 2n - 2`, which is
`i + 3 ≤ n`.

This input is *needed*: `SerreC2odd` covers only **odd** `n` (for even `n` the cover `Eₙ` is not
rationally acyclic — `K(ℤ,n)_ℚ = ℚ[x_n]`), so the even case of the STEMS contract is obtained by
suspending into the odd case. -/
def SerreFreudenthal : Prop :=
  ∀ (n i : ℕ), 1 ≤ n → i + 3 ≤ n →
    (∀ y₀ : Sph (n + 1), PiTorsion (Sph (n + 1)) y₀ (n + 1 + i)) →
    ∀ x₀ : Sph n, PiTorsion (Sph n) x₀ (n + i)

/-- **The blueprint's S2 derivation**: models (C0), the odd step of the induction (C2 odd: the
`(n-1)`-connected cover of `Sⁿ`, `n` odd, is rationally acyclic), the rational vanishing Hurewicz
theorem (S1) and Freudenthal's suspension theorem imply the STEMS contract.  For odd `n` the cover
`Eₙ` is `n`-connected (long exact sequence of `Eₙ → Sⁿ → Lₙ` plus `Work.RatHurewicz.SphereConnected`)
with `π_j(Eₙ) ≅ π_j(Sⁿ)` for `j > n`, and `n + i + 1 ≤ 2n - 2` is exactly `i + 3 ≤ n`; the even case
follows from the odd one by `SerreFreudenthal`. -/
def SerreS2OfC0C2oddS1 : Prop := SerreC0 → SerreC2odd → SerreS1 → SerreFreudenthal → SerreS2

/-- **The blueprint's C2 derivation**: the `K(ℤ,n)` models (C0), the even step C1 (the base of the
induction) and the degenerate cases E3(a), E3(b) and E4 (the Wang sequence with the derivation
property) imply the even and odd steps C2. -/
def SerreC2OfC0C1E3E4 : Prop := SerreC0 → SerreC1 → SerreE3a → SerreE3b → SerreE4 →
  SerreC2even ∧ SerreC2odd

end

end Work.Serre
