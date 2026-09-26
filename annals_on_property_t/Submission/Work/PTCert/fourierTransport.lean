import Mathlib
import Submission.Work.PTCert.GlueDefs
import Submission.Work.PTCert.twistedFourierCriterion
import Submission.Work.PTCert.psdSignedPerm
import Submission.Work.PTCert.transportKey
import Submission.Work.PTCert.transportRho

/-! Guidance from the project lead (the requester):

Context: `Submission/Work/PTCert/GlueDefs.lean` (definitions + Props; read it first) glues the
kernel-checked certificate data to the proved generic chain (`Chain.lean`, `Math.lean`,
`Interfaces.lean`; all their Props are already PROVED: avgPrinciple, labelPrinciple, gramSOS,
avgGram, avgMatInvariant, rowFormula, psdOfBlock, psdSignedPerm, ldlScaledPrinciple,
twistedFourierCriterion, residualAbsorption, letterAction, signCodes8, sigmaGroupFacts, modelSound,
permCheckKSound, ...). The design note is `NOTES_LEAD_glue.md` at the workspace root.
Do NOT change GlueDefs.lean. If the statement is false, `declare_false` with a concrete counterexample.
Put helper lemmas in your own file or under `Submission/Work/PTCert/<yourLemma>/`.
Math (verify each step). Let ρ x := rep (τ x) for x a representative; ν_x := nu (τ x), so
τ x = act ν_x (ρ x). Put s x := chiS (S.map p) (ν_x) (= ±1).
Key identity, for representatives x̄, ȳ:
  fourierW act M (S.map p) (ρ x̄) (ρ ȳ) = s x̄ * s ȳ * fourierW act M S x̄ ȳ.
Proof: ρ x̄ = act ν_x (τ x̄) (act ν ∘ act ν = id). M (act ν u) (act a v) = M u (act (ν + a) v) (invariance
+ char 2). Then act c (τ ȳ) = τ (act (c ∘ p) ȳ) (hypothesis with a := fun i => c (p i)), and
M (τ u) (τ v) = M u v. Reindex a ↦ d := (a + ν_x + ν_y) ∘ p (a bijection of Fin m → ZMod 2) and use
chiS (S.map p) (fun i => d (p.symm i)) = chiS S d (Finset.prod_map) and chiS_add.
ρ is a bijection of {x // rep x = x}: its inverse is x ↦ rep (τ.symm x) (τ.symm also normalises
the action: from the hypothesis, τ.symm (act a x) = act (fun i => a (p i)) (τ.symm x)).
Rep invariance: rep (act a x) = rep x.
Conclude with `psdSignedPerm` (Chain.lean: PSDSignedPerm, proved: `Work.PTCert.psdSignedPerm` or grep)
applied to M := the S-block, τ := ρ⁻¹ as an Equiv of the subtype, signs s ∘ ρ⁻¹.

Implementation.  The key scalar identity is `Work.PTCert.transportKey`
(`Submission/Work/PTCert/transportKey.lean`), the representative-transport facts (that
`x ↦ rep (τ x)` and `x ↦ rep (τ.symm x)` are mutually inverse on `{x // rep x = x}`) are
`Work.PTCert.transportRho` (`Submission/Work/PTCert/transportRho.lean`), and the small shared
facts (`chiS_map`, `act_neg`, `tau_act`, `tau_symm_act`) are in
`Submission/Work/PTCert/fourierTransport/Common.lean`.
-/

namespace Work.PTCert

open Submission.PTCert
open scoped BigOperators

theorem fourierTransport : FourierTransport := by
  intro m ι _instF _instD act hact_add hact_zero M hM rep nu hnu hrep hrepact τ p hτ hMτ S hS
  classical
  -- The two maps on the set `{x // rep x = x}` of representatives of the `act`-orbits:
  -- `σi x = rep (τ.symm x)` (the inverse transport) and `ρi x = rep (τ x)`.
  let σi : {x : ι // rep x = x} → {x : ι // rep x = x} :=
    fun x => ⟨rep (τ.symm x.1), hrep (τ.symm x.1)⟩
  let ρi : {x : ι // rep x = x} → {x : ι // rep x = x} :=
    fun x => ⟨rep (τ x.1), hrep (τ x.1)⟩
  -- `transportRho`: these are mutually inverse.
  have hρσ : ∀ x : {x : ι // rep x = x}, ρi (σi x) = x := by
    intro x
    apply Subtype.ext
    have h := (transportRho act hact_add hact_zero rep nu hnu hrepact τ p hτ).1 x.1
    show rep (τ (rep (τ.symm x.1))) = x.1
    rw [h]; exact x.2
  have hσρ : ∀ x : {x : ι // rep x = x}, σi (ρi x) = x := by
    intro x
    apply Subtype.ext
    have h := (transportRho act hact_add hact_zero rep nu hnu hrepact τ p hτ).2 x.1
    show rep (τ.symm (rep (τ x.1))) = x.1
    rw [h]; exact x.2
  let e : {x : ι // rep x = x} ≃ {x : ι // rep x = x} := ⟨σi, ρi, hρσ, hσρ⟩
  -- The `p(S)`-block is the `S`-block conjugated by `e` and the signs `χ_{p(S)}(ν)`.
  let sgn : {x : ι // rep x = x} → ℝ := fun x => chiS (S.map p.toEmbedding) (nu (τ (σi x).1))
  have hsgn : ∀ x, sgn x = 1 ∨ sgn x = -1 :=
    fun x => chiS_pm (S.map p.toEmbedding) (nu (τ (σi x).1))
  have key : ∀ x y : {x : ι // rep x = x},
      fourierW act M (S.map p.toEmbedding) x.1 y.1 =
        sgn x * sgn y * fourierW act M S (e x).1 (e y).1 := by
    intro x y
    have hx : rep (τ (σi x).1) = x.1 := Subtype.ext_iff.mp (hρσ x)
    have hy : rep (τ (σi y).1) = y.1 := Subtype.ext_iff.mp (hρσ y)
    have hk := transportKey act hact_add hact_zero M hM rep nu hnu τ p hτ hMτ S (σi x).1 (σi y).1
    rw [hx, hy] at hk
    exact hk
  have hres := psdSignedPerm (Matrix.of fun (x y : {x : ι // rep x = x}) => fourierW act M S x.1 y.1)
    e sgn hsgn hS
  convert hres using 1
  ext x y
  exact key x y

end Work.PTCert
