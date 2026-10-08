import Submission.Work.BG.Defs
import Submission.Work.BG.Lambda
import Submission.OddOrder.GroupTheory.RepresentationTheory.Inertia
import Submission.OddOrder.GroupTheory.RepresentationTheory.InflationCharacter
import Submission.OddOrder.GroupTheory.RepresentationTheory.InducedCharacter

/-!
# Area BG: the `s`-action on `CF(H₀)` (design pass 8, `_design_gw/Core8BG.lean`)

Bender–Glauberman's Lemma 1.7(iii) and the Coherence Theorem 2.3 need the action
`ν ↦ ν^s` of `s ∈ H ∖ H₀` on the class functions of `H₀`, where `H₀ ⊴ H ≤ G` is the
index-two subgroup of Hypothesis 1.2.  The Feit–Thompson character library has this action
(`ClassFunction.conjBy`, `ClassFunction.conjByMulEquiv`, `IsIrreducibleCharacter.conjBy`)
for a subgroup normal in its ambient group — here the ambient group must be `↥H` and the
subgroup `H₀.subgroupOf H` (the `conjBy` of `Inertia.lean` does not apply inside `G`,
because `H₀` is not normal in `G`).

This module transports that action to `ClassFunction ↥H₀` (where `Hyp12`'s class functions
live) along `Subgroup.subgroupOfEquivOfLe`, following `_design_gw/Core8BG.lean`:

* `Work.BG.H0in P`, `Work.BG.H0inEquiv P` — `H₀` inside `↥H` and the identification
  `↥(H₀.subgroupOf H) ≃* ↥H₀`;
* `Work.BG.conjMulEquiv P s` — conjugation by `s` as an automorphism of `H₀`;
* `Work.BG.conjByH P s ν` — `ν^s = ν ∘ (h ↦ s h s⁻¹)`;
* `Work.BG.IsIrreducibleCharacter.conjByH` — irreducibility is preserved;
* the interface statements `ConjByHTransportProp` (agreement with the library action on
  `CF(H₀.subgroupOf H)`), `ConjByHMulProp` (`(ν^{s₁})^{s₂} = ν^{s₁s₂}`) and
  `InduceConjByHProp` (`(ν^s)^G = ν^G`, which is why BG's `δ_j` carries the `λ₂` factor).
-/

namespace Work.BG

open OddOrder.RepresentationTheory

variable {G : Type} [Group G] [Finite G]

/-- `H₀` as a (normal) subgroup of the ambient group `↥P.H`. -/
abbrev H0in (P : Hyp12 G) : Subgroup ↥P.H := P.H0.subgroupOf P.H

instance H0in_normal (P : Hyp12 G) : (H0in P).Normal := P.H0_normal

/-- `↥(H₀.subgroupOf H) ≃* ↥H₀`. -/
noncomputable def H0inEquiv (P : Hyp12 G) : ↥(H0in P) ≃* ↥P.H0 :=
  Subgroup.subgroupOfEquivOfLe P.H0_le_H

/-- Conjugation by `s ∈ H` as an automorphism of `H₀`: `h ↦ s h s⁻¹`. -/
noncomputable def conjMulEquiv (P : Hyp12 G) (s : ↥P.H) : ↥P.H0 ≃* ↥P.H0 :=
  ((H0inEquiv P).symm.trans
    (ClassFunction.conjByMulEquiv (G := ↥P.H) (H := H0in P) s)).trans (H0inEquiv P)

theorem conjMulEquiv_apply (P : Hyp12 G) (s : ↥P.H) (h : ↥P.H0) :
    ((conjMulEquiv P s h : ↥P.H0) : G) = (s : G) * (h : G) * (s : G)⁻¹ := rfl

/-- `ν^s := ν ∘ (h ↦ s h s⁻¹)`, the `s`-conjugate of a class function of `H₀`; this is the
library's convention for `ClassFunction.conjBy`. -/
noncomputable def conjByH (P : Hyp12 G) (s : ↥P.H) (ν : ClassFunction ↥P.H0 ℂ) :
    ClassFunction ↥P.H0 ℂ :=
  ClassFunction.compHom (conjMulEquiv P s).toMonoidHom ν

theorem conjByH_apply (P : Hyp12 G) (s : ↥P.H) (ν : ClassFunction ↥P.H0 ℂ) (h : ↥P.H0) :
    conjByH P s ν h = ν (conjMulEquiv P s h) := rfl

/-- Irreducibility is preserved by `ν ↦ ν^s`. -/
theorem IsIrreducibleCharacter.conjByH (P : Hyp12 G) (s : ↥P.H)
    {ν : ClassFunction ↥P.H0 ℂ} (hν : IsIrreducibleCharacter ν) :
    IsIrreducibleCharacter (conjByH P s ν) :=
  IsIrreducibleCharacter.compHom_of_surjective (conjMulEquiv P s).surjective hν

/-- Agreement with the library action on `CF(H₀.subgroupOf H)`, the frame of area BG's
Remark 1.4 files. -/
def ConjByHTransportProp : Prop :=
  ∀ (P : Hyp12 G) (s : ↥P.H) (ν : ClassFunction ↥P.H0 ℂ),
    ClassFunction.compHom (H0inEquiv P).toMonoidHom (conjByH P s ν) =
      ClassFunction.conjBy (G := ↥P.H) (H := H0in P) s
        (ClassFunction.compHom (H0inEquiv P).toMonoidHom ν)

/-- `(ν^{s₁})^{s₂} = ν^{s₁ s₂}`, in the same order as the library's `ClassFunction.conjBy_mul`. -/
def ConjByHMulProp : Prop :=
  ∀ (P : Hyp12 G) (s₁ s₂ : ↥P.H) (ν : ClassFunction ↥P.H0 ℂ),
    conjByH P (s₁ * s₂) ν = conjByH P s₂ (conjByH P s₁ ν)

/-- Induction to `G` does not see `s`: `(ν^s)^G = ν^G`.  This is why BG's `δ_j` must carry
the `λ₂` factor (`δ_j = ν_j - λ₂ν_j^s`, not `ν_j - ν_j^s`). -/
def InduceConjByHProp [Fintype G] : Prop :=
  ∀ (P : Hyp12 G) (s : ↥P.H) [Invertible (Nat.card P.H0 : ℂ)]
    (ν : ClassFunction ↥P.H0 ℂ),
    ClassFunction.induce P.H0 (conjByH P s ν) = ClassFunction.induce P.H0 ν

/-- **The formal target of Bender–Glauberman 1981, Lemma 1.7(iii).**

For `|H₀ : U| = 2` (so `Λ = {1, λ₂}`), for a system `rep` of `Λ`-orbit representatives of
`Irr(H₀)` satisfying the freeness condition `hfree` (which makes `lambdaOrbitSum P μ` the
orbit sum with each element counted once — see `NOTES_lemma17_corrected.md`), for
`s ∈ H ∖ H₀` and `χ ∈ ZIrr G`:

`χ(g) = Σ_{ν ∈ rep} (χ, (ν − λ₂ν^s)^G)_G · ν(g)`  for all `g ∈ T = H₀ ∖ U`.

This is (ii) + (i) (`Work.BG.lemma17_ii` with `Work.BG.lambdaOrbitSum_apply_eq_zero_of_not_mem_U`),
and it is what Lemma 1.9 and §§3–4 of the paper use: on `T` the orbit sums `r(Λν)` vanish,
leaving only the `ε`-terms.  Note `ν^s` is `Work.BG.conjByH P s ν` (there is no `conjBy`
inside `G`, since `H₀` is not normal in `G`; see `H0Conj.lean`), and the `λ₂` factor is
essential: with `δ = ν − ν^s` one would get `δ^G = 0` (that is
`Work.BG.InduceConjByHProp`). -/
def Lemma17iiiProp : Prop :=
  ∀ {G : Type} [Group G] [Finite G] [Fintype G] (P : Hyp12 G)
    [(P.U.subgroupOf P.H0).Normal] [Fintype ↥P.H0] [Invertible (Nat.card ↥P.H0 : ℂ)]
    [Invertible (Nat.card G : ℂ)] [Fintype (quotGroup P →* ℂˣ)]
    [Fintype (IrreducibleCharacter ↥P.H0)]
    (h2 : Nat.card (quotGroup P) = 2)
    (s : ↥P.H) (hs : s ∉ H0in P)
    {lam2 : quotGroup P →* ℂˣ} (hlam2 : lam2 ≠ 1)
    (rep : Finset (ClassFunction ↥P.H0 ℂ))
    (hirr : ∀ μ ∈ rep, IsIrreducibleCharacter μ)
    (hfree : ∀ μ ∈ rep, Function.Injective (fun β : quotGroup P →* ℂˣ =>
      ClassFunction.compHom (quotMk P) (linearClassFunction β) * μ))
    (hdisj : ∀ μ ∈ rep, ∀ ν ∈ rep, μ ≠ ν → ¬ ∃ lam ∈ Lambda P, lam * μ = ν)
    (hov : ∀ ν : IrreducibleCharacter ↥P.H0, ∃ μ ∈ rep,
      ((ν : ClassFunction ↥P.H0 ℂ) = μ) ∨ ∃ lam ∈ Lambda P,
        (ν : ClassFunction ↥P.H0 ℂ) = lam * μ)
    (χ : ClassFunction G ℂ) (hχ : χ ∈ ZIrr G),
    ∀ g : ↥P.H0, g ∉ P.U.subgroupOf P.H0 →
      χ (g : G) = ∑ ν ∈ rep,
        (ClassFunction.inner χ (ClassFunction.induce P.H0
          (ν - ClassFunction.compHom (quotMk P) (linearClassFunction lam2) *
            conjByH P s ν))) * ν g

end Work.BG
