import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.H0Conj
import Submission.Work.BG.s02_lemma22Sq
import Submission.Work.BG.CharBridge
import Submission.Work.BG.lambda_mul_irreducible
import Submission.Work.BG.lemma22Gen
import Submission.Work.BG.lemma22EvalW
import Submission.Work.BG.invJCard

/-!
# Area BG: `Lemma22KappaProp` (Bender–Glauberman 1981, Lemma 2.2, the form used in §2.4–2.5)

`Work.GW2.C16.Lemma22KappaProp D C` is the `κ`-form of Lemma 2.2 of Bender–Glauberman,
J. Algebra 70 (1981), pp. 205–207: for an `s`-fixed linear character `κ` of `H₀`
(`κ(1) = 1`, `κ = 1` on `S₀`) and any `β : H₀/U →* ℂˣ`, under the hypothesis that either
`ν := λ_β κ` is not `s`-fixed or `λ_β` is a non-trivial `s`-fixed linear character with
`|H : C_H(t₁)| = |H : C_H(t₂)|`,

`|G : H| · Σ_{χ ∈ Irr G} χ(t)²/χ(1) · (χ, (κ - λ_β κ)^G)_G = 2 k²`.

It is the assembly of three statements:

* `Work.BG.lemma22Gen` — **L22-G**: the general identity (`μ`, `ν` `Λ`-equivalent)
  `|G:H| Σ_χ χ(t)²/χ(1) (χ, (μ-ν)*) = Σ_{θ ∈ Irr H} (Σ_{x ∈ J} θ(x))²/θ(1) (θ, μ^H - ν^H)`;
* `Work.BG.lemma22EvalW` — **L22-W**: the evaluation of the right-hand side, `= 2|J|²`;
* `Work.BG.invJCard` — **G9**: `|J| = k`.

The bookkeeping performed here is the transport of the `Sec2Ctx` context to the `BGData`
notation via `Compat D C` (`C.P.H = D.H`, `C.P.H0 = H1 D`, `C.t = D.t`), together with the
`Fintype`/`Invertible` instances that the three statements ask for (`↥C.P.H` inside a finite
group `G`).
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

/-- `Invertible` for the cardinality of a subgroup of a finite group (needed to state the
inner product on `↥C.P.H`). -/
noncomputable def lemma22Kappa_invCardSub {G : Type} [Group G] [Fintype G] (S : Subgroup G) :
    Invertible (Nat.card ↥S : ℂ) :=
  invertibleOfNonzero (by
    rw [Nat.cast_ne_zero]
    exact Nat.card_ne_zero.mpr ⟨⟨1, S.one_mem⟩, inferInstance⟩)

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem lemma22Kappa {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    [Fintype (OddOrder.RepresentationTheory.IrreducibleCharacter G)] :
    Work.GW2.C16.Lemma22KappaProp D C := by
  intro hc κ β hκ hκ1 hκs hκS0 hcase
  -- The instances the three auxiliary statements ask for on the ambient subgroup `↥C.P.H`.
  haveI : Fintype ↥C.P.H := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥C.P.H : ℂ) := lemma22Kappa_invCardSub C.P.H
  haveI : Invertible (Nat.card ↥(H0in C.P) : ℂ) := by
    have h : Nat.card ↥(H0in C.P) = Nat.card ↥C.P.H0 :=
      Nat.card_congr (H0inEquiv C.P).toEquiv
    rw [h]; infer_instance
  haveI : Fintype (IrreducibleCharacter ↥C.P.H) := inferInstance
  -- `λ_β κ` is irreducible and `Λ`-equivalent to `κ`.
  have hνirr : IsIrreducibleCharacter (lamCF C β * κ) :=
    lambda_mul_irreducible C.P (⟨β, rfl⟩ : lamCF C β ∈ Lambda C.P) hκ
  have hlam : LamEquiv C κ (lamCF C β * κ) := ⟨β, rfl⟩
  -- L22-G, specialised to `μ = κ`, `ν = λ_β κ`.
  have hgen := lemma22Gen C κ (lamCF C β * κ) hκ hνirr hlam
  -- L22-W, the same data.
  have heval := lemma22EvalW D C hc κ β hκ hκ1 hκs hκS0 hcase
  -- Chain the two identities.
  have hkey := hgen.trans heval
  -- Transport `C.P.H.index` to `D.H.index` and `|J|` to `k`.
  have hidx : (C.P.H.index : ℂ) = (D.H.index : ℂ) := by rw [hc.H_eq]
  have hcard : ((invJ C).card : ℂ) = (D.k : ℂ) := by rw [invJCard D C hc]
  rw [hidx, hcard] at hkey
  exact hkey

end Work.BG
