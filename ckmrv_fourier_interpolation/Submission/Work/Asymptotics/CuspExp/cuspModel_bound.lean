/-
# The model correction `MK - AexpZ` of the CKMRV kernel

`Work.Asymptotics.CuspExp.cuspModel_bound`: the model `MK ℓ d` of the CKMRV kernel differs
from the non-decaying part `AexpZ (Gcusp ℓ d)` of its cusp-`i∞` expansion by `O(‖E(z)‖)`.

Write `E = E(z) = Work.Residues.Ept z` and `q = E² = Work.Asymptotics.mq z`.  Every model in
`Work.Asymptotics.CuspExp.Models` is a Laurent polynomial in `E` (with coefficients the
`τ`-atoms `φ_vec`, `E₄`, `E₆`, `Δ`, `ψ₂`, `ψ₄`, `cuspL ℓ` and the constants `π`, `I`), and
`Work.Asymptotics.AexpZ` collects the coefficients of `E⁻²`, `E⁻¹`, `E⁰`.  Expanding
`MK ℓ d τ z - AexpZ (Gcusp ℓ d) τ z` in powers of `E` (see the `## Expansion` note below), the
coefficients of `E⁻²`, `E⁻¹` and `E⁰` cancel identically -- the only relation between the
`τ`-atoms needed is `Δ(τ)·j(τ) = E₄(τ)³`, used to rewrite the occurrences of `j(τ)` -- and the
remainder is `E · (polynomial in E of degree ≤ 11)`.

This file

* performs this expansion explicitly (`cmTerms8`, `cmTerms24` and `cmF8`, `cmF24`, obtained
  by machine algebra over the free Laurent ring in `E`, `π`, `I`, with `j(τ)` eliminated),
* proves the resulting algebraic identities `cm_key8`, `cm_key24` by `field_simp`/`ring`,
* bounds `cmF8`, `cmF24` on a compact set of `τ`'s, and
* deduces `cuspModel_bound`.

The expansion data are the coefficients of the monomials
`c · π^k · I^l · (atoms) · z^d · E^m` of `(MK - AexpZ)/E`: `cmTerms8`/`cmTerms24` list them as
`CTerm` structures (rational coefficient `c`, `π`-power `k`, `I`-power `l`, the atom
multiplicities `mult` as indices into `cmAtoms`, the `z`-degree `d` and the `E`-degree `m`).
-/
import Mathlib
import Submission.Work.Asymptotics.CuspExp.Models
import Submission.Work.Asymptotics.CuspExp.Basic
import Submission.Work.Asymptotics.CuspExp.Exp
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.Asymptotics.MiddleRange.exists_bound_phiVec_phitVec
import Submission.Work.Asymptotics.psi_InP

namespace Work.Asymptotics.CuspExp

open UpperHalfPlane

noncomputable section

set_option maxHeartbeats 0

/-! ## The expansion data -/

/-- The `τ`-atoms occurring in the expansion, indexed by `Fin 10`:
`φ_{-2}, φ_0, φ_2, E₄, E₆, Δ⁻¹, Δ, ψ₂, ψ₄, cuspL ℓ`. -/
def cmAtoms (ℓ : Work.Kernels.LogLambdaData) : Fin 10 → ℍ → ℂ :=
  ![fun τ => Work.Kernels.phiVec τ 0, fun τ => Work.Kernels.phiVec τ 1,
    fun τ => Work.Kernels.phiVec τ 2, Work.Kernels.E4Fun, Work.Kernels.E6Fun,
    fun τ => (Work.Kernels.DeltaFun τ)⁻¹, Work.Kernels.DeltaFun,
    fun τ => Work.Kernels.psi2 ℓ τ, fun τ => Work.Kernels.psi4 ℓ τ,
    fun _ => cuspL ℓ]

/-- The `π`-power occurring in the expansion (`k = -1, 0, 1, 2` occur). -/
def cmPif (k : ℤ) : ℂ :=
  if k = -1 then (Real.pi : ℂ)⁻¹ else if k = 1 then (Real.pi : ℂ)
  else if k = 2 then (Real.pi : ℂ) ^ 2 else 1

/-- The `I`-power occurring in the expansion (`k = -1, 0, 1` occur). -/
def cmIif (k : ℤ) : ℂ := if k = -1 then Complex.I⁻¹ else if k = 1 then Complex.I else 1

/-- A monomial of the correction `(MK - AexpZ)/E`: rational coefficient, `π`- and `I`-powers,
atom multiplicities, and the `z`- and `E`-degrees. -/
structure CTerm where
  c : ℚ
  pk : ℤ
  ik : ℤ
  mult : List (Fin 10)
  zd : ℕ
  ed : ℕ
  deriving DecidableEq, Repr

/-- The value of a monomial. -/
def CTerm.ev (ℓ : Work.Kernels.LogLambdaData) (t : CTerm) (τ z : ℍ) : ℂ :=
  (t.c : ℂ) * cmPif t.pk * cmIif t.ik * ((t.mult.map (fun i => cmAtoms ℓ i τ)).prod)
    * ((z : ℂ)) ^ t.zd * (Work.Residues.Ept z) ^ t.ed

/-- The monomials of `(MK^{(8)} - AexpZ)/E`. -/
def cmTerms8 : List CTerm :=
  [⟨(2 : ℚ), -1, 0, [8], 0, 0⟩,
  ⟨(-4 : ℚ), -1, 0, [3], 0, 0⟩,
  ⟨(1/288 : ℚ), -1, 0, [3, 3, 4, 5, 7], 0, 0⟩,
  ⟨(-1/288 : ℚ), -1, 0, [3, 3, 3, 5, 8], 0, 0⟩,
  ⟨(54 : ℚ), -1, 0, [8], 0, 1⟩,
  ⟨(6 : ℚ), -1, 0, [3], 0, 1⟩,
  ⟨(-1/6 : ℚ), -1, 0, [3, 3, 4, 5, 7], 0, 1⟩,
  ⟨(-1/12 : ℚ), -1, 0, [3, 3, 3, 5, 8], 0, 1⟩,
  ⟨(-492 : ℚ), -1, 0, [3, 9], 0, 1⟩,
  ⟨(1/2 : ℚ), -1, 0, [3, 3, 3, 3, 5, 9], 0, 1⟩,
  ⟨(120 : ℚ), 0, 1, [0, 4], 0, 1⟩,
  ⟨(-1/2 : ℚ), 0, 1, [0, 3, 3, 3, 4, 5], 0, 1⟩,
  ⟨(-492 : ℚ), 0, 1, [3], 1, 1⟩,
  ⟨(1/2 : ℚ), 0, 1, [3, 3, 3, 3, 5], 1, 1⟩,
  ⟨(164 : ℚ), 1, 0, [1, 3], 1, 1⟩,
  ⟨(-1/6 : ℚ), 1, 0, [1, 3, 3, 3, 3, 5], 1, 1⟩,
  ⟨(-44 : ℚ), 1, 0, [0, 4], 1, 1⟩,
  ⟨(1/6 : ℚ), 1, 0, [0, 3, 3, 3, 4, 5], 1, 1⟩,
  ⟨(-1/72 : ℚ), 2, -1, [2, 3, 3, 4, 5], 2, 1⟩,
  ⟨(-28 : ℚ), 2, -1, [1, 3], 2, 1⟩,
  ⟨(1/36 : ℚ), 2, -1, [1, 3, 3, 3, 3, 5], 2, 1⟩,
  ⟨(4 : ℚ), 2, -1, [0, 4], 2, 1⟩,
  ⟨(-1/72 : ℚ), 2, -1, [0, 3, 3, 3, 4, 5], 2, 1⟩,
  ⟨(-480 : ℚ), -1, 0, [8], 0, 2⟩,
  ⟨(3936 : ℚ), -1, 0, [3], 0, 2⟩,
  ⟨(-28/9 : ℚ), -1, 0, [3, 3, 4, 5, 7], 0, 2⟩,
  ⟨(46/9 : ℚ), -1, 0, [3, 3, 3, 5, 8], 0, 2⟩,
  ⟨(-4 : ℚ), -1, 0, [3, 3, 3, 3, 5], 0, 2⟩,
  ⟨(1/288 : ℚ), -1, 0, [3, 3, 3, 3, 3, 4, 5, 5, 7], 0, 2⟩,
  ⟨(-1/288 : ℚ), -1, 0, [3, 3, 3, 3, 3, 3, 5, 5, 8], 0, 2⟩,
  ⟨(73440 : ℚ), -1, 0, [8], 0, 3⟩,
  ⟨(-5904 : ℚ), -1, 0, [3], 0, 3⟩,
  ⟨(241/2 : ℚ), -1, 0, [3, 3, 4, 5, 7], 0, 3⟩,
  ⟨(-493/2 : ℚ), -1, 0, [3, 3, 3, 5, 8], 0, 3⟩,
  ⟨(6 : ℚ), -1, 0, [3, 3, 3, 3, 5], 0, 3⟩,
  ⟨(-1/6 : ℚ), -1, 0, [3, 3, 3, 3, 3, 4, 5, 5, 7], 0, 3⟩,
  ⟨(1/6 : ℚ), -1, 0, [3, 3, 3, 3, 3, 3, 5, 5, 8], 0, 3⟩,
  ⟨(34560 : ℚ), -1, 0, [3, 9], 0, 3⟩,
  ⟨(-132 : ℚ), -1, 0, [3, 3, 3, 3, 5, 9], 0, 3⟩,
  ⟨(144000 : ℚ), 0, 1, [0, 4], 0, 3⟩,
  ⟨(-240 : ℚ), 0, 1, [0, 3, 3, 3, 4, 5], 0, 3⟩,
  ⟨(34560 : ℚ), 0, 1, [3], 1, 3⟩,
  ⟨(-132 : ℚ), 0, 1, [3, 3, 3, 3, 5], 1, 3⟩,
  ⟨(-11520 : ℚ), 1, 0, [1, 3], 1, 3⟩,
  ⟨(44 : ℚ), 1, 0, [1, 3, 3, 3, 3, 5], 1, 3⟩,
  ⟨(-47040 : ℚ), 1, 0, [0, 4], 1, 3⟩,
  ⟨(76 : ℚ), 1, 0, [0, 3, 3, 3, 4, 5], 1, 3⟩,
  ⟨(31/3 : ℚ), 2, -1, [2, 3, 3, 4, 5], 2, 3⟩,
  ⟨(-1/72 : ℚ), 2, -1, [2, 3, 3, 3, 3, 3, 4, 5, 5], 2, 3⟩,
  ⟨(2576 : ℚ), 2, -1, [1, 3], 2, 3⟩,
  ⟨(-8 : ℚ), 2, -1, [1, 3, 3, 3, 3, 5], 2, 3⟩,
  ⟨(3832 : ℚ), 2, -1, [0, 4], 2, 3⟩,
  ⟨(-6 : ℚ), 2, -1, [0, 3, 3, 3, 4, 5], 2, 3⟩,
  ⟨(-576000 : ℚ), -1, 0, [8], 0, 4⟩,
  ⟨(-276480 : ℚ), -1, 0, [3], 0, 4⟩,
  ⟨(1520/3 : ℚ), -1, 0, [3, 3, 4, 5, 7], 0, 4⟩,
  ⟨(1360/3 : ℚ), -1, 0, [3, 3, 3, 5, 8], 0, 4⟩,
  ⟨(1056 : ℚ), -1, 0, [3, 3, 3, 3, 5], 0, 4⟩,
  ⟨(-11/18 : ℚ), -1, 0, [3, 3, 3, 3, 3, 4, 5, 5, 7], 0, 4⟩,
  ⟨(11/18 : ℚ), -1, 0, [3, 3, 3, 3, 3, 3, 5, 5, 8], 0, 4⟩,
  ⟨(12096000 : ℚ), -1, 0, [8], 0, 5⟩,
  ⟨(414720 : ℚ), -1, 0, [3], 0, 5⟩,
  ⟨(-560 : ℚ), -1, 0, [3, 3, 4, 5, 7], 0, 5⟩,
  ⟨(-16720 : ℚ), -1, 0, [3, 3, 3, 5, 8], 0, 5⟩,
  ⟨(-1584 : ℚ), -1, 0, [3, 3, 3, 3, 5], 0, 5⟩,
  ⟨(1/2 : ℚ), -1, 0, [3, 3, 3, 3, 3, 4, 5, 5, 7], 0, 5⟩,
  ⟨(-1/2 : ℚ), -1, 0, [3, 3, 3, 3, 3, 3, 5, 5, 8], 0, 5⟩,
  ⟨(43545600 : ℚ), -1, 0, [3, 9], 0, 5⟩,
  ⟨(-60480 : ℚ), -1, 0, [3, 3, 3, 3, 5, 9], 0, 5⟩,
  ⟨(20736000 : ℚ), 0, 1, [0, 4], 0, 5⟩,
  ⟨(-28800 : ℚ), 0, 1, [0, 3, 3, 3, 4, 5], 0, 5⟩,
  ⟨(43545600 : ℚ), 0, 1, [3], 1, 5⟩,
  ⟨(-60480 : ℚ), 0, 1, [3, 3, 3, 3, 5], 1, 5⟩,
  ⟨(-14515200 : ℚ), 1, 0, [1, 3], 1, 5⟩,
  ⟨(20160 : ℚ), 1, 0, [1, 3, 3, 3, 3, 5], 1, 5⟩,
  ⟨(-5760000 : ℚ), 1, 0, [0, 4], 1, 5⟩,
  ⟨(7680 : ℚ), 1, 0, [0, 3, 3, 3, 4, 5], 1, 5⟩,
  ⟨(2373120 : ℚ), 2, -1, [1, 3], 2, 5⟩,
  ⟨(-3184 : ℚ), 2, -1, [1, 3, 3, 3, 3, 5], 2, 5⟩,
  ⟨(385920 : ℚ), 2, -1, [0, 4], 2, 5⟩,
  ⟨(-488 : ℚ), 2, -1, [0, 3, 3, 3, 4, 5], 2, 5⟩,
  ⟨(-82944000 : ℚ), -1, 0, [8], 0, 6⟩,
  ⟨(-348364800 : ℚ), -1, 0, [3], 0, 6⟩,
  ⟨(-48000 : ℚ), -1, 0, [3, 3, 4, 5, 7], 0, 6⟩,
  ⟨(163200 : ℚ), -1, 0, [3, 3, 3, 5, 8], 0, 6⟩,
  ⟨(483840 : ℚ), -1, 0, [3, 3, 3, 3, 5], 0, 6⟩,
  ⟨(200/3 : ℚ), -1, 0, [3, 3, 3, 3, 3, 4, 5, 5, 7], 0, 6⟩,
  ⟨(-200/3 : ℚ), -1, 0, [3, 3, 3, 3, 3, 3, 5, 5, 8], 0, 6⟩,
  ⟨(248832000 : ℚ), -1, 0, [8], 0, 7⟩,
  ⟨(522547200 : ℚ), -1, 0, [3], 0, 7⟩,
  ⟨(144000 : ℚ), -1, 0, [3, 3, 4, 5, 7], 0, 7⟩,
  ⟨(-489600 : ℚ), -1, 0, [3, 3, 3, 5, 8], 0, 7⟩,
  ⟨(-725760 : ℚ), -1, 0, [3, 3, 3, 3, 5], 0, 7⟩,
  ⟨(-200 : ℚ), -1, 0, [3, 3, 3, 3, 3, 4, 5, 5, 7], 0, 7⟩,
  ⟨(200 : ℚ), -1, 0, [3, 3, 3, 3, 3, 3, 5, 5, 8], 0, 7⟩,
  ⟨(165888000 : ℚ), 1, 0, [0, 4], 1, 7⟩,
  ⟨(-230400 : ℚ), 1, 0, [0, 3, 3, 3, 4, 5], 1, 7⟩,
  ⟨(-58060800 : ℚ), 2, -1, [1, 3], 2, 7⟩,
  ⟨(80640 : ℚ), 2, -1, [1, 3, 3, 3, 3, 5], 2, 7⟩,
  ⟨(-25344000 : ℚ), 2, -1, [0, 4], 2, 7⟩,
  ⟨(34560 : ℚ), 2, -1, [0, 3, 3, 3, 4, 5], 2, 7⟩,
  ⟨(331776000 : ℚ), 2, -1, [0, 4], 2, 9⟩,
  ⟨(-460800 : ℚ), 2, -1, [0, 3, 3, 3, 4, 5], 2, 9⟩]

/-- The monomials of `(MK^{(24)} - AexpZ)/E`. -/
def cmTerms24 : List CTerm :=
  [⟨(2976 : ℚ), -1, 0, [6], 0, 0⟩,
  ⟨(-41/18 : ℚ), -1, 0, [3, 4, 7], 0, 0⟩,
  ⟨(77/18 : ℚ), -1, 0, [3, 3, 8], 0, 0⟩,
  ⟨(-4 : ℚ), -1, 0, [3, 3, 3], 0, 0⟩,
  ⟨(1/288 : ℚ), -1, 0, [3, 3, 3, 3, 4, 5, 7], 0, 0⟩,
  ⟨(-1/288 : ℚ), -1, 0, [3, 3, 3, 3, 3, 5, 8], 0, 0⟩,
  ⟨(-4608 : ℚ), -1, 0, [6], 0, 1⟩,
  ⟨(107/4 : ℚ), -1, 0, [3, 4, 7], 0, 1⟩,
  ⟨(589/4 : ℚ), -1, 0, [3, 3, 8], 0, 1⟩,
  ⟨(6 : ℚ), -1, 0, [3, 3, 3], 0, 1⟩,
  ⟨(13/288 : ℚ), -1, 0, [3, 3, 3, 3, 4, 5, 7], 0, 1⟩,
  ⟨(-85/288 : ℚ), -1, 0, [3, 3, 3, 3, 3, 5, 8], 0, 1⟩,
  ⟨(-1/6912 : ℚ), -1, 0, [3, 3, 3, 3, 3, 3, 3, 4, 5, 5, 7], 0, 1⟩,
  ⟨(1/6912 : ℚ), -1, 0, [3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 8], 0, 1⟩,
  ⟨(-92448 : ℚ), -1, 0, [6, 9], 0, 1⟩,
  ⟨(360 : ℚ), 0, 1, [0, 3, 3, 4], 0, 1⟩,
  ⟨(-1/2 : ℚ), 0, 1, [0, 3, 3, 3, 3, 3, 4, 5], 0, 1⟩,
  ⟨(-92448 : ℚ), 0, 1, [6], 1, 1⟩,
  ⟨(-1/3 : ℚ), 1, 0, [2, 3, 4], 1, 1⟩,
  ⟨(33120 : ℚ), 1, 0, [1, 6], 1, 1⟩,
  ⟨(-10/3 : ℚ), 1, 0, [1, 3, 3, 3], 1, 1⟩,
  ⟨(-373/3 : ℚ), 1, 0, [0, 3, 3, 4], 1, 1⟩,
  ⟨(1/6 : ℚ), 1, 0, [0, 3, 3, 3, 3, 3, 4, 5], 1, 1⟩,
  ⟨(251/36 : ℚ), 2, -1, [2, 3, 4], 2, 1⟩,
  ⟨(-1/72 : ℚ), 2, -1, [2, 3, 3, 3, 3, 4, 5], 2, 1⟩,
  ⟨(-4696 : ℚ), 2, -1, [1, 6], 2, 1⟩,
  ⟨(-11/18 : ℚ), 2, -1, [1, 3, 3, 3], 2, 1⟩,
  ⟨(395/36 : ℚ), 2, -1, [0, 3, 3, 4], 2, 1⟩,
  ⟨(-1/72 : ℚ), 2, -1, [0, 3, 3, 3, 3, 3, 4, 5], 2, 1⟩,
  ⟨(739584 : ℚ), -1, 0, [6], 0, 2⟩,
  ⟨(316/3 : ℚ), -1, 0, [3, 4, 7], 0, 2⟩,
  ⟨(-4636/3 : ℚ), -1, 0, [3, 3, 8], 0, 2⟩,
  ⟨(-25/18 : ℚ), -1, 0, [3, 3, 3, 3, 4, 5, 7], 0, 2⟩,
  ⟨(61/18 : ℚ), -1, 0, [3, 3, 3, 3, 3, 5, 8], 0, 2⟩,
  ⟨(1/864 : ℚ), -1, 0, [3, 3, 3, 3, 3, 3, 3, 4, 5, 5, 7], 0, 2⟩,
  ⟨(-1/864 : ℚ), -1, 0, [3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 8], 0, 2⟩,
  ⟨(-1109376 : ℚ), -1, 0, [6], 0, 3⟩,
  ⟨(11892 : ℚ), -1, 0, [3, 4, 7], 0, 3⟩,
  ⟨(-7572 : ℚ), -1, 0, [3, 3, 8], 0, 3⟩,
  ⟨(-131/12 : ℚ), -1, 0, [3, 3, 3, 3, 4, 5, 7], 0, 3⟩,
  ⟨(59/12 : ℚ), -1, 0, [3, 3, 3, 3, 3, 5, 8], 0, 3⟩,
  ⟨(-1/288 : ℚ), -1, 0, [3, 3, 3, 3, 3, 3, 3, 4, 5, 5, 7], 0, 3⟩,
  ⟨(1/288 : ℚ), -1, 0, [3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 8], 0, 3⟩,
  ⟨(49835520 : ℚ), -1, 0, [6, 9], 0, 3⟩,
  ⟨(-92448 : ℚ), -1, 0, [3, 3, 3, 9], 0, 3⟩,
  ⟨(8928 : ℚ), 0, 1, [0, 3, 3, 4], 0, 3⟩,
  ⟨(-12 : ℚ), 0, 1, [0, 3, 3, 3, 3, 3, 4, 5], 0, 3⟩,
  ⟨(49835520 : ℚ), 0, 1, [6], 1, 3⟩,
  ⟨(-92448 : ℚ), 0, 1, [3, 3, 3], 1, 3⟩,
  ⟨(-16611840 : ℚ), 1, 0, [1, 6], 1, 3⟩,
  ⟨(30816 : ℚ), 1, 0, [1, 3, 3, 3], 1, 3⟩,
  ⟨(-96 : ℚ), 1, 0, [0, 3, 3, 4], 1, 3⟩,
  ⟨(7942/3 : ℚ), 2, -1, [2, 3, 4], 2, 3⟩,
  ⟨(-11/3 : ℚ), 2, -1, [2, 3, 3, 3, 3, 4, 5], 2, 3⟩,
  ⟨(2902464 : ℚ), 2, -1, [1, 6], 2, 3⟩,
  ⟨(-15452/3 : ℚ), 2, -1, [1, 3, 3, 3], 2, 3⟩,
  ⟨(-722/3 : ℚ), 2, -1, [0, 3, 3, 4], 2, 3⟩,
  ⟨(1/3 : ℚ), 2, -1, [0, 3, 3, 3, 3, 3, 4, 5], 2, 3⟩,
  ⟨(-398684160 : ℚ), -1, 0, [6], 0, 4⟩,
  ⟨(205440 : ℚ), -1, 0, [3, 4, 7], 0, 4⟩,
  ⟨(-205440 : ℚ), -1, 0, [3, 3, 8], 0, 4⟩,
  ⟨(739584 : ℚ), -1, 0, [3, 3, 3], 0, 4⟩,
  ⟨(-884/3 : ℚ), -1, 0, [3, 3, 3, 3, 4, 5, 7], 0, 4⟩,
  ⟨(884/3 : ℚ), -1, 0, [3, 3, 3, 3, 3, 5, 8], 0, 4⟩,
  ⟨(598026240 : ℚ), -1, 0, [6], 0, 5⟩,
  ⟨(-1546560 : ℚ), -1, 0, [3, 4, 7], 0, 5⟩,
  ⟨(1546560 : ℚ), -1, 0, [3, 3, 8], 0, 5⟩,
  ⟨(-1109376 : ℚ), -1, 0, [3, 3, 3], 0, 5⟩,
  ⟨(2232 : ℚ), -1, 0, [3, 3, 3, 3, 4, 5, 7], 0, 5⟩,
  ⟨(-2232 : ℚ), -1, 0, [3, 3, 3, 3, 3, 5, 8], 0, 5⟩,
  ⟨(11695104000 : ℚ), -1, 0, [6, 9], 0, 5⟩,
  ⟨(-16727040 : ℚ), -1, 0, [3, 3, 3, 9], 0, 5⟩,
  ⟨(11695104000 : ℚ), 0, 1, [6], 1, 5⟩,
  ⟨(-16727040 : ℚ), 0, 1, [3, 3, 3], 1, 5⟩,
  ⟨(-4448618496 : ℚ), 1, 0, [1, 6], 1, 5⟩,
  ⟨(6315264 : ℚ), 1, 0, [1, 3, 3, 3], 1, 5⟩,
  ⟨(71424 : ℚ), 1, 0, [0, 3, 3, 4], 1, 5⟩,
  ⟨(-96 : ℚ), 1, 0, [0, 3, 3, 3, 3, 3, 4, 5], 1, 5⟩,
  ⟨(59520 : ℚ), 2, -1, [2, 3, 4], 2, 5⟩,
  ⟨(-80 : ℚ), 2, -1, [2, 3, 3, 3, 3, 4, 5], 2, 5⟩,
  ⟨(674989056 : ℚ), 2, -1, [1, 6], 2, 5⟩,
  ⟨(-929280 : ℚ), 2, -1, [1, 3, 3, 3], 2, 5⟩,
  ⟨(-6144 : ℚ), 2, -1, [0, 3, 3, 4], 2, 5⟩,
  ⟨(8 : ℚ), 2, -1, [0, 3, 3, 3, 3, 3, 4, 5], 2, 5⟩,
  ⟨(-93560832000 : ℚ), -1, 0, [6], 0, 6⟩,
  ⟨(4838400 : ℚ), -1, 0, [3, 4, 7], 0, 6⟩,
  ⟨(-4838400 : ℚ), -1, 0, [3, 3, 8], 0, 6⟩,
  ⟨(133816320 : ℚ), -1, 0, [3, 3, 3], 0, 6⟩,
  ⟨(-6720 : ℚ), -1, 0, [3, 3, 3, 3, 4, 5, 7], 0, 6⟩,
  ⟨(6720 : ℚ), -1, 0, [3, 3, 3, 3, 3, 5, 8], 0, 6⟩,
  ⟨(140341248000 : ℚ), -1, 0, [6], 0, 7⟩,
  ⟨(-43545600 : ℚ), -1, 0, [3, 4, 7], 0, 7⟩,
  ⟨(43545600 : ℚ), -1, 0, [3, 3, 8], 0, 7⟩,
  ⟨(-200724480 : ℚ), -1, 0, [3, 3, 3], 0, 7⟩,
  ⟨(60480 : ℚ), -1, 0, [3, 3, 3, 3, 4, 5, 7], 0, 7⟩,
  ⟨(-60480 : ℚ), -1, 0, [3, 3, 3, 3, 3, 5, 8], 0, 7⟩,
  ⟨(250822656000 : ℚ), -1, 0, [6, 9], 0, 7⟩,
  ⟨(-348364800 : ℚ), -1, 0, [3, 3, 3, 9], 0, 7⟩,
  ⟨(250822656000 : ℚ), 0, 1, [6], 1, 7⟩,
  ⟨(-348364800 : ℚ), 0, 1, [3, 3, 3], 1, 7⟩,
  ⟨(-183166894080 : ℚ), 1, 0, [1, 6], 1, 7⟩,
  ⟨(249937920 : ℚ), 1, 0, [1, 3, 3, 3], 1, 7⟩,
  ⟨(12733341696 : ℚ), 2, -1, [1, 6], 2, 7⟩,
  ⟨(-16395264 : ℚ), 2, -1, [1, 3, 3, 3], 2, 7⟩,
  ⟨(142848 : ℚ), 2, -1, [0, 3, 3, 4], 2, 7⟩,
  ⟨(-192 : ℚ), 2, -1, [0, 3, 3, 3, 3, 3, 4, 5], 2, 7⟩,
  ⟨(-2006581248000 : ℚ), -1, 0, [6], 0, 8⟩,
  ⟨(2786918400 : ℚ), -1, 0, [3, 3, 3], 0, 8⟩,
  ⟨(3009871872000 : ℚ), -1, 0, [6], 0, 9⟩,
  ⟨(-4180377600 : ℚ), -1, 0, [3, 3, 3], 0, 9⟩,
  ⟨(-2073467289600 : ℚ), 1, 0, [1, 6], 1, 9⟩,
  ⟨(2786918400 : ℚ), 1, 0, [1, 3, 3, 3], 1, 9⟩,
  ⟨(-387089694720 : ℚ), 2, -1, [1, 6], 2, 9⟩,
  ⟨(535265280 : ℚ), 2, -1, [1, 3, 3, 3], 2, 9⟩,
  ⟨(-8293869158400 : ℚ), 2, -1, [1, 6], 2, 11⟩,
  ⟨(11147673600 : ℚ), 2, -1, [1, 3, 3, 3], 2, 11⟩]

/-- The correction `(MK^{(8)} - AexpZ)/E`, as the sum of its monomials. -/
def cmF8 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  ((cmTerms8.map (fun t => t.ev ℓ τ z)).sum)

/-- The correction `(MK^{(24)} - AexpZ)/E`, as the sum of its monomials. -/
def cmF24 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  ((cmTerms24.map (fun t => t.ev ℓ τ z)).sum)

/-! ## The algebraic identities -/

lemma cm_mq_eq_Ept_sq (z : ℍ) : Work.Asymptotics.mq z = Work.Residues.Ept z ^ 2 := by
  rw [Work.Asymptotics.mq, Work.Kernels.qParamFun, Work.Residues.Ept]
  rw [sq, ← Complex.exp_add]
  congr 1
  ring

/-- The unfolding of the models, used for both identities. -/
macro "cm_unfold" : tactic =>
  `(tactic|
    simp (config := {decide := true}) only
      [Work.Asymptotics.MK, Work.Asymptotics.Gcusp, Work.Asymptotics.AexpZ,
       Work.Asymptotics.Gcusp8, Work.Asymptotics.Gcusp24, Work.Asymptotics.MP8,
       Work.Asymptotics.MM8, Work.Asymptotics.MP24, Work.Asymptotics.MM24,
       Work.Asymptotics.tphi0, Work.Asymptotics.tphi1, Work.Asymptotics.tphi2,
       Work.Asymptotics.mE4, Work.Asymptotics.mE6, Work.Asymptotics.mE8,
       Work.Asymptotics.mE10, Work.Asymptotics.mE14, Work.Asymptotics.minvJ,
       Work.Asymptotics.mR, Work.Asymptotics.mG, Work.Asymptotics.mE14D,
       Work.Asymptotics.mE10D, Work.Asymptotics.minvD, Work.Asymptotics.mW,
       Work.Asymptotics.mD, Work.Kernels.E14Fun, Work.Kernels.E10Fun,
       Work.Kernels.E8Fun, Work.Kernels.jInvariantFun, cm_mq_eq_Ept_sq,
       cmAtoms, cmPif, cmIif, CTerm.ev, Fin.isValue, Matrix.cons_val,
       List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
       List.sum_cons, List.sum_nil, zpow_neg, inv_pow, if_true, if_false])

theorem cm_key8 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    Work.Asymptotics.MK ℓ 8 τ z - Work.Asymptotics.AexpZ (Work.Asymptotics.Gcusp ℓ 8) τ z
      = Work.Residues.Ept z * cmF8 ℓ τ z := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hΔ : Work.Kernels.DeltaFun τ ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  have hE : Work.Residues.Ept z ≠ 0 := Work.Residues.Ept_ne_zero z
  cm_unfold
  rw [cmF8, cmTerms8]
  cm_unfold
  field_simp
  ring

theorem cm_key24 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    Work.Asymptotics.MK ℓ 24 τ z - Work.Asymptotics.AexpZ (Work.Asymptotics.Gcusp ℓ 24) τ z
      = Work.Residues.Ept z * cmF24 ℓ τ z := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hΔ : Work.Kernels.DeltaFun τ ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  have hE : Work.Residues.Ept τ ≠ 0 := Work.Residues.Ept_ne_zero τ
  cm_unfold
  rw [cmF24, cmTerms24]
  cm_unfold
  field_simp
  ring

/-! ## Bounding the monomials -/

lemma cm_norm_ofReal (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  have h : ‖(r : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    ring
  have h2 : |r| ^ 2 = r ^ 2 := sq_abs r
  nlinarith [norm_nonneg ((r : ℂ)), abs_nonneg r]

lemma cm_norm_rat (c : ℚ) : ‖(c : ℂ)‖ = |(c : ℝ)| := by
  rw [← Complex.ofReal_ratCast c, cm_norm_ofReal]

lemma cm_pif_bound (k : ℤ) : ‖cmPif k‖ ≤ 16 := by
  unfold cmPif
  split_ifs with h1 h2 h3
  · rw [norm_inv, cm_norm_ofReal, abs_of_pos Real.pi_pos]
    rw [inv_le_comm₀ (by positivity) (by norm_num : (0 : ℝ) < 16)]
    linarith [Real.pi_gt_three]
  · rw [cm_norm_ofReal, abs_of_pos Real.pi_pos]
    linarith [Real.pi_lt_four]
  · rw [norm_pow, cm_norm_ofReal, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_lt_four, Real.pi_pos]
  · rw [norm_one]; norm_num

lemma cm_iif_bound (k : ℤ) : ‖cmIif k‖ ≤ 1 := by
  unfold cmIif
  split_ifs with h1 h2
  · rw [norm_inv, Complex.norm_I]; norm_num
  · rw [Complex.norm_I]
  · rw [norm_one]

/-- A product of nonnegative reals each at most `B ≥ 0` is at most `B ^ length`. -/
lemma cm_list_prod_le_pow (l : List ℝ) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ x ∈ l, x ≤ B) (h0 : ∀ x ∈ l, 0 ≤ x) : l.prod ≤ B ^ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha : a ≤ B := h a (List.mem_cons_self ..)
      have hl : l.prod ≤ B ^ l.length :=
        ih (fun x hx => h x (List.mem_cons_of_mem a hx))
           (fun x hx => h0 x (List.mem_cons_of_mem a hx))
      have hl0 : 0 ≤ l.prod :=
        List.prod_nonneg (fun x hx => h0 x (List.mem_cons_of_mem a hx))
      rw [List.prod_cons, List.length_cons, pow_succ']
      exact mul_le_mul ha hl hl0 hB

/-- A sum of complex numbers, bounded by a constant on the terms. -/
lemma cm_norm_sum_map_le {α : Type*} (l : List α) (f : α → ℂ) :
    ‖(l.map f).sum‖ ≤ (l.map (fun x => ‖f x‖)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
      exact le_trans (norm_add_le (f a) _) (add_le_add le_rfl ih)

lemma cm_list_sum_le (l : List ℝ) (c : ℝ) (h : ∀ x ∈ l, x ≤ c) :
    l.sum ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha : a ≤ c := h a (List.mem_cons_self ..)
      have hl : l.sum ≤ l.length * c := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
      rw [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      linarith

/-- The atoms are bounded on a compact set of `τ`'s. -/
lemma cm_atom_bound (ℓ : Work.Kernels.LogLambdaData) {K : Set ℍ} (hK : IsCompact K) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ τ ∈ K, ∀ i : Fin 10, ‖cmAtoms ℓ i τ‖ ≤ B := by
  obtain ⟨⟨P, hP0, hP⟩, _⟩ :=
    Work.Asymptotics.MiddleRange.exists_bound_phiVec_phitVec hK hK
  obtain ⟨B4, hB4⟩ := hK.exists_bound_of_continuousOn
    ((Work.Kernels.ClassicalFacts.E4Fun_mem_InP).1.continuous).continuousOn
  obtain ⟨B6, hB6⟩ := hK.exists_bound_of_continuousOn
    ((Work.Kernels.ClassicalFacts.E6Fun_mem_InP).1.continuous).continuousOn
  obtain ⟨Bd, hBd⟩ := hK.exists_bound_of_continuousOn
    ((Work.Kernels.ClassicalFacts.DeltaFun_mem_InP).1.continuous).continuousOn
  have hDne : ∀ τ ∈ K, Work.Kernels.DeltaFun τ ≠ 0 :=
    fun τ _ => Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  obtain ⟨Bdi, hBdi⟩ := hK.exists_bound_of_continuousOn
    (((Work.Kernels.ClassicalFacts.DeltaFun_mem_InP).1.continuous).continuousOn.inv₀ hDne)
  obtain ⟨Bp2, hBp2⟩ := hK.exists_bound_of_continuousOn
    ((Work.Asymptotics.psi_InP ℓ).1.1.continuous).continuousOn
  obtain ⟨Bp4, hBp4⟩ := hK.exists_bound_of_continuousOn
    ((Work.Asymptotics.psi_InP ℓ).2.1.continuous).continuousOn
  set B : ℝ := max P 0 + max B4 0 + max B6 0 + max Bd 0 + max Bdi 0 + max Bp2 0
    + max Bp4 0 + (‖cuspL ℓ‖ + 1) with hBdef
  have hPle : P ≤ B := by
    rw [hBdef]; nlinarith [le_max_left P 0, le_max_right B4 0, le_max_right B6 0,
      le_max_right Bd 0, le_max_right Bdi 0, le_max_right Bp2 0, le_max_right Bp4 0,
      norm_nonneg (cuspL ℓ)]
  have hB4le : B4 ≤ B := by
    rw [hBdef]; nlinarith [le_max_left B4 0, le_max_right P 0, le_max_right B6 0,
      le_max_right Bd 0, le_max_right Bdi 0, le_max_right Bp2 0, le_max_right Bp4 0,
      norm_nonneg (cuspL ℓ)]
  have hB6le : B6 ≤ B := by
    rw [hBdef]; nlinarith [le_max_left B6 0, le_max_right P 0, le_max_right B4 0,
      le_max_right Bd 0, le_max_right Bdi 0, le_max_right Bp2 0, le_max_right Bp4 0,
      norm_nonneg (cuspL ℓ)]
  have hBdle : Bd ≤ B := by
    rw [hBdef]; nlinarith [le_max_left Bd 0, le_max_right P 0, le_max_right B4 0,
      le_max_right B6 0, le_max_right Bdi 0, le_max_right Bp2 0, le_max_right Bp4 0,
      norm_nonneg (cuspL ℓ)]
  have hBdile : Bdi ≤ B := by
    rw [hBdef]; nlinarith [le_max_left Bdi 0, le_max_right P 0, le_max_right B4 0,
      le_max_right B6 0, le_max_right Bd 0, le_max_right Bp2 0, le_max_right Bp4 0,
      norm_nonneg (cuspL ℓ)]
  have hBp2le : Bp2 ≤ B := by
    rw [hBdef]; nlinarith [le_max_left Bp2 0, le_max_right P 0, le_max_right B4 0,
      le_max_right B6 0, le_max_right Bd 0, le_max_right Bdi 0, le_max_right Bp4 0,
      norm_nonneg (cuspL ℓ)]
  have hBp4le : Bp4 ≤ B := by
    rw [hBdef]; nlinarith [le_max_left Bp4 0, le_max_right P 0, le_max_right B4 0,
      le_max_right B6 0, le_max_right Bd 0, le_max_right Bdi 0, le_max_right Bp2 0,
      norm_nonneg (cuspL ℓ)]
  have hBcl : ‖cuspL ℓ‖ ≤ B := by
    rw [hBdef]; nlinarith [le_max_right P 0, le_max_right B4 0, le_max_right B6 0,
      le_max_right Bd 0, le_max_right Bdi 0, le_max_right Bp2 0, le_max_right Bp4 0,
      norm_nonneg (cuspL ℓ)]
  refine ⟨B, ?_, ?_⟩
  · rw [hBdef]
    nlinarith [le_max_left P 0, le_max_right P 0, le_max_left B4 0, le_max_right B4 0,
      le_max_left B6 0, le_max_right B6 0, le_max_left Bd 0, le_max_right Bd 0,
      le_max_left Bdi 0, le_max_right Bdi 0, le_max_left Bp2 0, le_max_right Bp2 0,
      le_max_left Bp4 0, le_max_right Bp4 0, norm_nonneg (cuspL ℓ)]
  · intro τ hτ i
    fin_cases i <;> simp only [cmAtoms, Fin.isValue]
    · exact le_trans (hP τ hτ 0) hPle
    · exact le_trans (hP τ hτ 1) hPle
    · exact le_trans (hP τ hτ 2) hPle
    · exact le_trans (hB4 τ hτ) hB4le
    · exact le_trans (hB6 τ hτ) hB6le
    · exact le_trans (hBdi τ hτ) hBdile
    · exact le_trans (hBd τ hτ) hBdle
    · exact le_trans (hBp2 τ hτ) hBp2le
    · exact le_trans (hBp4 τ hτ) hBp4le
    · exact hBcl

/-- **The bound for a single monomial.** -/
lemma cm_ev_bound {B : ℝ} {ℓ : Work.Kernels.LogLambdaData} {τ z : ℍ}
    (t : CTerm) (hB1 : 1 ≤ B) (hatoms : ∀ i : Fin 10, ‖cmAtoms ℓ i τ‖ ≤ B)
    (hlen : t.mult.length ≤ 11) (hzd : t.zd ≤ 2) (hc : |t.c| ≤ (10000000000000 : ℚ)) :
    ‖t.ev ℓ τ z‖ ≤ 160000000000000 * B ^ 11 * cuspW z ^ 2 := by
  rw [CTerm.ev, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow]
  have hc' : ‖(t.c : ℂ)‖ ≤ 10000000000000 := by
    rw [cm_norm_rat]
    exact_mod_cast hc
  have hp : ‖cmPif t.pk‖ ≤ 16 := cm_pif_bound t.pk
  have hi : ‖cmIif t.ik‖ ≤ 1 := cm_iif_bound t.ik
  have hprod : ‖(t.mult.map (fun i => cmAtoms ℓ i τ)).prod‖ ≤ B ^ 11 := by
    have h1 : ‖(t.mult.map (fun i => cmAtoms ℓ i τ)).prod‖
        ≤ (List.map norm (List.map (fun i => cmAtoms ℓ i τ) t.mult)).prod :=
      List.norm_prod_le _
    have h2 := cm_list_prod_le_pow (List.map norm (List.map (fun i => cmAtoms ℓ i τ) t.mult)) B
      (le_trans zero_le_one hB1)
      (by
        intro x hx
        rw [List.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        rw [List.mem_map] at hy
        obtain ⟨i, _, rfl⟩ := hy
        exact hatoms i)
      (by
        intro x hx
        rw [List.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        exact norm_nonneg _)
    rw [List.length_map, List.length_map] at h2
    exact le_trans h1 (le_trans h2 (pow_le_pow_right₀ hB1 hlen))
  have hz : ‖(z : ℂ)‖ ^ t.zd ≤ cuspW z ^ 2 := by
    calc ‖(z : ℂ)‖ ^ t.zd ≤ cuspW z ^ t.zd :=
          pow_le_pow_left₀ (norm_nonneg _) (coe_norm_le_cuspW z) _
      _ ≤ cuspW z ^ 2 := pow_le_pow_right₀ (cuspW_one_le z) hzd
  have hE : ‖(Work.Residues.Ept z)‖ ^ t.ed ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) (le_of_lt (Work.Residues.norm_Ept_lt_one z))
  have h1 : ‖(t.c : ℂ)‖ * ‖cmPif t.pk‖ * ‖cmIif t.ik‖ ≤ 160000000000000 := by
    have h2 : ‖(t.c : ℂ)‖ * ‖cmPif t.pk‖ ≤ 10000000000000 * 16 :=
      mul_le_mul hc' hp (norm_nonneg _) (by norm_num)
    have h3 : ‖(t.c : ℂ)‖ * ‖cmPif t.pk‖ * ‖cmIif t.ik‖ ≤ 10000000000000 * 16 * 1 :=
      mul_le_mul h2 hi (norm_nonneg _) (by norm_num)
    linarith
  calc ‖(t.c : ℂ)‖ * ‖cmPif t.pk‖ * ‖cmIif t.ik‖
        * ‖(t.mult.map (fun i => cmAtoms ℓ i τ)).prod‖ * ‖(z : ℂ)‖ ^ t.zd
        * ‖(Work.Residues.Ept z)‖ ^ t.ed
      ≤ 160000000000000 * B ^ 11 * cuspW z ^ 2 * 1 := by
        refine mul_le_mul (mul_le_mul (mul_le_mul h1 hprod (norm_nonneg _) (by positivity))
          hz (by positivity) (by positivity)) hE (by positivity) (by positivity)
    _ = 160000000000000 * B ^ 11 * cuspW z ^ 2 := by ring

/-- The per-monomial data of both lists: length, `z`-degree and coefficient bound. -/
lemma cm_terms_props :
    (∀ t ∈ cmTerms8, t.mult.length ≤ 11 ∧ t.zd ≤ 2 ∧ |t.c| ≤ (10000000000000 : ℚ)) ∧
    (∀ t ∈ cmTerms24, t.mult.length ≤ 11 ∧ t.zd ≤ 2 ∧ |t.c| ≤ (10000000000000 : ℚ)) := by
  constructor
  · intro t ht
    simp only [cmTerms8, List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> refine ⟨by decide, by decide, by norm_num⟩
  · intro t ht
    simp only [cmTerms24, List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> refine ⟨by decide, by decide, by norm_num⟩

/-- **The bound for `cmF8`.** -/
theorem cm_F8_bound {B : ℝ} {ℓ : Work.Kernels.LogLambdaData} {τ z : ℍ}
    (hB1 : 1 ≤ B) (hatoms : ∀ i : Fin 10, ‖cmAtoms ℓ i τ‖ ≤ B) :
    ‖cmF8 ℓ τ z‖ ≤ (cmTerms8.length : ℝ) * (160000000000000 * B ^ 11 * cuspW z ^ 2) := by
  have h1 : ‖cmF8 ℓ τ z‖ ≤ (cmTerms8.map (fun t => ‖t.ev ℓ τ z‖)).sum := by
    rw [cmF8]
    exact cm_norm_sum_map_le cmTerms8 (fun t => t.ev ℓ τ z)
  have h2 : (cmTerms8.map (fun t => ‖t.ev ℓ τ z‖)).sum
      ≤ (cmTerms8.map (fun _ => 160000000000000 * B ^ 11 * cuspW z ^ 2)).sum := by
    refine List.sum_le_sum ?_
    intro t ht
    obtain ⟨hl, hz, hc⟩ := cm_terms_props.1 t ht
    exact cm_ev_bound t hB1 hatoms hl hz hc
  have h3 : (cmTerms8.map (fun _ => 160000000000000 * B ^ 11 * cuspW z ^ 2)).sum
      = (cmTerms8.length : ℝ) * (160000000000000 * B ^ 11 * cuspW z ^ 2) := by
    rw [show (cmTerms8.map (fun _ => 160000000000000 * B ^ 11 * cuspW z ^ 2))
        = List.replicate cmTerms8.length (160000000000000 * B ^ 11 * cuspW z ^ 2)
        from List.map_const', List.sum_replicate, nsmul_eq_mul]
  linarith [h1, h2, h3]

/-- **The bound for `cmF24`.** -/
theorem cm_F24_bound {B : ℝ} {ℓ : Work.Kernels.LogLambdaData} {τ z : ℍ}
    (hB1 : 1 ≤ B) (hatoms : ∀ i : Fin 10, ‖cmAtoms ℓ i τ‖ ≤ B) :
    ‖cmF24 ℓ τ z‖ ≤ (cmTerms24.length : ℝ) * (160000000000000 * B ^ 11 * cuspW z ^ 2) := by
  have h1 : ‖cmF24 ℓ τ z‖ ≤ (cmTerms24.map (fun t => ‖t.ev ℓ τ z‖)).sum := by
    rw [cmF24]
    exact cm_norm_sum_map_le cmTerms24 (fun t => t.ev ℓ τ z)
  have h2 : (cmTerms24.map (fun t => ‖t.ev ℓ τ z‖)).sum
      ≤ (cmTerms24.map (fun _ => 160000000000000 * B ^ 11 * cuspW z ^ 2)).sum := by
    refine List.sum_le_sum ?_
    intro t ht
    obtain ⟨hl, hz, hc⟩ := cm_terms_props.2 t ht
    exact cm_ev_bound t hB1 hatoms hl hz hc
  have h3 : (cmTerms24.map (fun _ => 160000000000000 * B ^ 11 * cuspW z ^ 2)).sum
      = (cmTerms24.length : ℝ) * (160000000000000 * B ^ 11 * cuspW z ^ 2) := by
    rw [show (cmTerms24.map (fun _ => 160000000000000 * B ^ 11 * cuspW z ^ 2))
        = List.replicate cmTerms24.length (160000000000000 * B ^ 11 * cuspW z ^ 2)
        from List.map_const', List.sum_replicate, nsmul_eq_mul]
  linarith [h1, h2, h3]

/-! ## The model bound -/

/-- The model `MK ℓ d` of the CKMRV kernel `K^{(d)}` (the sum of the truncated expansions of the individual atoms, see `CuspExp/Models.lean`) differs from the non-decaying part `AexpZ (Gcusp ℓ d)` of the cusp expansion by `O(‖E(z)‖)`:  the coefficients of `E(z)⁻²`, `E(z)⁻¹` and `E(z)⁰` in `MK ℓ d τ z - AexpZ (Gcusp ℓ d) τ z` vanish identically, i.e. `MK ℓ d τ z - AexpZ (Gcusp ℓ d) τ z = E(z) * (bounded)`.  The vanishing is an algebraic identity between the atoms of `τ` and of `z`; the only relation between them needed is `DeltaFun τ * jInvariantFun τ = E4Fun τ ^ 3` (which holds by definition of `jInvariantFun` since `Δ ≠ 0`). -/
theorem cuspModel_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ C M : ℝ, 0 < C ∧ 0 ≤ M ∧ ∀ τ ∈ K, ∀ z : UpperHalfPlane,
      ‖Work.Asymptotics.MK ℓ d τ z - Work.Asymptotics.AexpZ (Work.Asymptotics.Gcusp ℓ d) τ z‖ ≤
        C * (Work.Asymptotics.cuspW z) ^ M * ‖Work.Residues.Ept z‖ := by
  obtain ⟨B, hB1, hB⟩ := cm_atom_bound ℓ hK
  rcases hd with rfl | rfl
  · refine ⟨(cmTerms8.length : ℝ) * (160000000000000 * B ^ 11) + 1, 2, by positivity,
      by norm_num, fun τ hτ z => ?_⟩
    have hb := cm_F8_bound (ℓ := ℓ) (τ := τ) (z := z) hB1 (hB τ hτ)
    rw [cm_key8 ℓ τ z, norm_mul]
    have hE0 : (0:ℝ) ≤ ‖Work.Residues.Ept z‖ := norm_nonneg _
    have hcw : (0:ℝ) ≤ cuspW z ^ 2 := by positivity
    have hA : ‖Work.Residues.Ept z‖ * ‖cmF8 ℓ τ z‖
        ≤ ‖Work.Residues.Ept z‖
            * ((cmTerms8.length : ℝ) * (160000000000000 * B ^ 11 * cuspW z ^ 2)) :=
      mul_le_mul_of_nonneg_left hb hE0
    have hB : ‖Work.Residues.Ept z‖
          * ((cmTerms8.length : ℝ) * (160000000000000 * B ^ 11 * cuspW z ^ 2))
        ≤ ((cmTerms8.length : ℝ) * (160000000000000 * B ^ 11) + 1) * cuspW z ^ 2
            * ‖Work.Residues.Ept z‖ := by
      have h1 : (cmTerms8.length : ℝ) * (160000000000000 * B ^ 11) * cuspW z ^ 2
          ≤ ((cmTerms8.length : ℝ) * (160000000000000 * B ^ 11) + 1) * cuspW z ^ 2 := by
        refine mul_le_mul_of_nonneg_right ?_ hcw
        linarith
      have h2 : ‖Work.Residues.Ept z‖
            * ((cmTerms8.length : ℝ) * (160000000000000 * B ^ 11 * cuspW z ^ 2))
          = (cmTerms8.length : ℝ) * (160000000000000 * B ^ 11) * cuspW z ^ 2
            * ‖Work.Residues.Ept z‖ := by ring
      rw [h2]
      exact mul_le_mul_of_nonneg_right h1 hE0
    rw [Real.rpow_ofNat]
    exact le_trans hA hB
  · refine ⟨(cmTerms24.length : ℝ) * (160000000000000 * B ^ 11) + 1, 2, by positivity,
      by norm_num, fun τ hτ z => ?_⟩
    have hb := cm_F24_bound (ℓ := ℓ) (τ := τ) (z := z) hB1 (hB τ hτ)
    rw [cm_key24 ℓ τ z, norm_mul]
    have hE0 : (0:ℝ) ≤ ‖Work.Residues.Ept z‖ := norm_nonneg _
    have hcw : (0:ℝ) ≤ cuspW z ^ 2 := by positivity
    have hA : ‖Work.Residues.Ept z‖ * ‖cmF24 ℓ τ z‖
        ≤ ‖Work.Residues.Ept z‖
            * ((cmTerms24.length : ℝ) * (160000000000000 * B ^ 11 * cuspW z ^ 2)) :=
      mul_le_mul_of_nonneg_left hb hE0
    have hB : ‖Work.Residues.Ept z‖
          * ((cmTerms24.length : ℝ) * (160000000000000 * B ^ 11 * cuspW z ^ 2))
        ≤ ((cmTerms24.length : ℝ) * (160000000000000 * B ^ 11) + 1) * cuspW z ^ 2
            * ‖Work.Residues.Ept z‖ := by
      have h1 : (cmTerms24.length : ℝ) * (160000000000000 * B ^ 11) * cuspW z ^ 2
          ≤ ((cmTerms24.length : ℝ) * (160000000000000 * B ^ 11) + 1) * cuspW z ^ 2 := by
        refine mul_le_mul_of_nonneg_right ?_ hcw
        linarith
      have h2 : ‖Work.Residues.Ept z‖
            * ((cmTerms24.length : ℝ) * (160000000000000 * B ^ 11 * cuspW z ^ 2))
          = (cmTerms24.length : ℝ) * (160000000000000 * B ^ 11) * cuspW z ^ 2
            * ‖Work.Residues.Ept z‖ := by ring
      rw [h2]
      exact mul_le_mul_of_nonneg_right h1 hE0
    rw [Real.rpow_ofNat]
    exact le_trans hA hB
end

end Work.Asymptotics.CuspExp
