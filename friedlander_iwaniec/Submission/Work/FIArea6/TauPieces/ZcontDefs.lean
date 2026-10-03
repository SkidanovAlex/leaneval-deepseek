/-
# `Submission.Work.FIArea6.TauPieces.ZcontDefs`

Vocabulary for the contour-continuation brick `ZcontExistsBound` (*FI* (16.31)–(16.35)).

The paper regroups the Dirichlet series (16.30)

  `Z(s) = Σ_{(n,Π)=1} λ_m(n) μ(n) γ(n;C) n^{-s}`   (`Zsfun`)

into a product `Z = M·P·Q` (16.31)–(16.34) and then continues `M(s)` past `re s = 1` by writing

  `M(s) = Φ(s)/L(s)`,   `Φ(s) = ∏_p (1 - λ(p)p^{-s})/(1 - λ(p)p^{-s} + (λ(p)² - λ(p²))p^{-2s})`

the Euler product that converges absolutely in `re s > 1/2` (it is `M(s)L(s,ψ)`).  Here

* `Phifac χ m s` is `Φ(s)` (already defined in `TsumHeartDefs`);
* `Zcand Pa χ m d Lam` is the candidate continuation
  `Φ(s)·(Λ(s)/((4d/π)^s Γ(s+|m|/2)))^{-1}·P(s)·Q(s)` of `Z`, the factor `(Λ/heckeArch)^{-1}`
  being the continuation of `1/L(s,ψ)` (bounded by *FI* (16.23)).
-/
import Mathlib
import Submission.Work.FIArea6.TauPieces.TsumHeartDefs
import Submission.Work.FITop4.Bridge.area5_6_defs

set_option autoImplicit false

namespace Work.FIArea6.TauPieces

open scoped BigOperators

noncomputable section

/-- The local deviation factor `Φ_p(s) - 1 = -((λ(p)² - λ(p²))·p^{-2s})/localL_p(s)` written as
the corresponding quotient: `Φ_p(s) = (1 - λ(p)p^{-s})/localL_p(s)`. -/
def PhiLocal (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ) (p : ℕ) : ℂ :=
  (1 - Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s)) / localL chi m p s

/-- **The candidate continuation of `Z`** (*FI* (16.31)–(16.35)): the product of the absolutely
convergent Euler product `Φ`, the continuation `(Λ/heckeArch)^{-1}` of `1/L(s,ψ)`, and the two
finite factors `P`, `Q`. -/
def Zcand (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (d : ℕ) (Lam : ℂ → ℂ) :
    ℂ → ℂ :=
  fun s => Phifac chi m s * (Lam s / Work.FITop4.Bridge.heckeArch d m s)⁻¹
    * Pfac Pa chi m s * Qfac Pa chi m s

lemma Zcand_apply (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (d : ℕ)
    (Lam : ℂ → ℂ) (s : ℂ) :
    Zcand Pa chi m d Lam s = Phifac chi m s * (Lam s / Work.FITop4.Bridge.heckeArch d m s)⁻¹
      * Pfac Pa chi m s * Qfac Pa chi m s := rfl

lemma Phifac_eq_tprod_PhiLocal (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ) :
    Phifac chi m s = ∏' p : Nat.Primes, PhiLocal chi m s (p : ℕ) := rfl

end

end Work.FIArea6.TauPieces
