import Submission.Work.Tame.Chapter10
import Submission.Work.Spine.Defs
import Submission.Work.Frobenius.Defs
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.CohApps` — Feit–Thompson Chapter III §11–§12 (area P2-05)

Source of record: W. Feit and J. G. Thompson, *Solvability of groups of odd order*,
Pacific J. Math. **13** (1963), 775–1029, Chapter III pp. 816–829.  The transcription used is
`Submission/Work/ft1963/tex/ch3a.md`, `ch3b.md`; every display was re-checked against the text
layer of the published PDF (`https://msp.org/pjm/1963/13-3/pjm-v13-n3-p03-s.pdf`), which caught
one error in the transcription of Lemma 12.1 (see `NOTES.md`).

This module fixes the vocabulary of §11–§12:

* `L0g L0hat = 𝔏₀ = N(L̂₀)`, `LhatImg φ = L̂ ⊆ 𝔏 = 𝔏₀/ℌ₀`, `infl φ` (pullback of characters along
  `φ`);
* the equivalence relation of §11 (v) (`SameDegWt`), the equivalence class `ClassOf S χ`, the
  subset `SofA S 𝔄 = 𝓢(𝔄)` of (vi), the set `Sset K L̂` of §11 (iii);
* `Hyp11_1`, `Hyp11_2`, `Hyp11_3` (pp. 817, 819, 821) verbatim;
* `Hyp12_1` (pp. 823–824) verbatim together with the notation (12.1)–(12.5).

## Conventions

* `X` is FT's ambient group `𝔛`; `𝔏₀ = N(L̂₀)` and `𝔏 = 𝔏₀/ℌ₀` are *subgroups of the ambient
  group*, so a character of `𝔏` is a function `𝔏 → ℂ` and a character of `𝔏₀` is a function
  `↥𝔏₀ → ℂ`.  FT identify characters of `𝔏` with class functions of `𝔏₀` trivial on `ℌ₀`; we
  present `𝔏` by a surjective homomorphism `φ : ↥𝔏₀ →* 𝔏` with kernel `ℌ₀` and pull characters
  back along `φ` (`infl φ`).  All the conditions (ii)–(vi) of Hypothesis 11.1 are then stated
  in the quotient group `𝔏` exactly as in the paper, and the coherence conclusion is stated for
  `infl φ 𝓢` in `𝔏₀ = N(L̂₀)`, which is where the Dade map of Definition 9.1 lives.
* "character" = `Work.CharCore.IsChar`, "irreducible character" = `Work.CharCore.Irr`,
  degree = `Work.CharCore.irrDeg`, weight = `Work.Tame.rwt`; `Work.Tame.FTCoherent`,
  `Work.Tame.Subcoherent`, `Work.Tame.tau` are Definition 10.1, Definition 10.2 and the Dade
  map (9.4) of Chapter III.
-/

noncomputable section

open Classical
open scoped Pointwise

namespace Work.CohApps

universe u

variable {X : Type u}

/-! ## §11: the setup `𝔏₀ = N(L̂₀)`, `𝔏 = 𝔏₀/ℌ₀` -/

section Setup

variable [Group X] [Fintype X]

/-- FT's `𝔏₀ = N(L̂₀)`, the normalizer of the tamely imbedded set `L̂₀`. -/
abbrev L0g (L0hat : Set X) : Subgroup X := Work.Tame.Lgrp L0hat

/-- FT's `L̂ ⊆ 𝔏 = 𝔏₀/ℌ₀`: the image of `L̂₀` under the quotient map `φ : 𝔏₀ → 𝔏`. -/
def LhatImg {L0hat : Set X} {Lb : Type u} [Group Lb]
    (φ : ↥(L0g L0hat) →* Lb) : Set Lb :=
  φ '' {l : ↥(L0g L0hat) | (l : X) ∈ L0hat}

@[simp] theorem mem_LhatImg {L0hat : Set X} {Lb : Type u} [Group Lb]
    {φ : ↥(L0g L0hat) →* Lb} {y : Lb} :
    y ∈ LhatImg φ ↔ ∃ l : ↥(L0g L0hat), (l : X) ∈ L0hat ∧ φ l = y := Iff.rfl

/-- Pullback ("inflation") of a function on `𝔏` to `𝔏₀` along `φ : 𝔏₀ →* 𝔏`.  This is how
Feit–Thompson identify characters of the quotient `𝔏 = 𝔏₀/ℌ₀` with class functions of `𝔏₀`:
the Dade map `τ` of Definition 9.1 is defined on class functions of `𝔏₀ = N(L̂₀)`, so this is
the only way to say that `𝓢` is coherent. -/
def infl {L0hat : Set X} {Lb : Type u} [Group Lb]
    (φ : ↥(L0g L0hat) →* Lb) (f : Lb → ℂ) : ↥(L0g L0hat) → ℂ :=
  fun l => f (φ l)

@[simp] theorem infl_apply {L0hat : Set X} {Lb : Type u} [Group Lb]
    (φ : ↥(L0g L0hat) →* Lb) (f : Lb → ℂ) (l : ↥(L0g L0hat)) : infl φ f l = f (φ l) := rfl

/-- The pullback of a function on a subgroup `𝔎 ≤ 𝔏` to its preimage `𝔎' = 𝔎 ∩ 𝔏₀` under the
quotient map `φ : 𝔏₀ →* 𝔏`.  This is the transport used by "induction commutes with inflation"
(`indFun_infl`): `Ind_{φ⁻¹𝔎}^{𝔏₀}(θ ∘ φ) = (Ind_𝔎^𝔏 θ) ∘ φ`. -/
def resInfl {L0hat : Set X} {Lb : Type u} [Group Lb]
    (φ : ↥(L0g L0hat) →* Lb) (K : Subgroup Lb) (θ : ↥K → ℂ) : ↥(K.comap φ) → ℂ :=
  fun x => θ ⟨φ x, x.2⟩

@[simp] theorem resInfl_apply {L0hat : Set X} {Lb : Type u} [Group Lb]
    (φ : ↥(L0g L0hat) →* Lb) (K : Subgroup Lb) (θ : ↥K → ℂ) (x : ↥(K.comap φ)) :
    resInfl φ K θ x = θ ⟨φ x, x.2⟩ := rfl

/-- Feit–Thompson's `𝓢` in Hypothesis 11.1 (iii): the set of characters of `𝔏` induced by
non-principal irreducible characters of `𝔎` which vanish outside `L̂`. -/
noncomputable def Sset {Y : Type*} [Group Y] [Fintype Y]
    (K : Subgroup Y) (Lhat : Set Y) : Finset (Y → ℂ) :=
  (((CharCore.Irr ↥K).filter (fun θ => θ ≠ 1)).image
      (fun θ => Induction.indFun K θ)).filter (fun χ => ∀ l : Y, l ∉ Lhat → χ l = 0)

/-- Hypothesis 11.1 (v): two characters are *equivalent* if they have the same degree and the
same weight `‖χ‖²`. -/
def SameDegWt {Y : Type*} [Group Y] [Fintype Y] (χ ψ : Y → ℂ) : Prop :=
  CharCore.irrDeg χ = CharCore.irrDeg ψ ∧ Tame.rwt χ = Tame.rwt ψ

/-- The equivalence class of `χ` in `S` for the relation of Hypothesis 11.1 (v). -/
noncomputable def ClassOf {Y : Type*} [Group Y] [Fintype Y]
    (S : Finset (Y → ℂ)) (χ : Y → ℂ) : Finset (Y → ℂ) :=
  S.filter (fun μ => SameDegWt μ χ)

/-- Hypothesis 11.1 (vi): `𝓢(𝔄)`, the subset of `𝓢` consisting of the characters equivalent to
some character of `𝓢` that has `𝔄` in its kernel. -/
noncomputable def SofA {Y : Type*} [Group Y] [Fintype Y]
    (S : Finset (Y → ℂ)) (A : Subgroup Y) : Finset (Y → ℂ) :=
  S.filter (fun χ => ∃ μ ∈ S, SameDegWt χ μ ∧ (A : Set Y) ⊆ CharCore.charKernel μ)

/-- Definition 10.1 in the quotient presentation of §11: `𝓢` (a set of characters of `𝔏`) is
coherent, i.e. `infl φ 𝓢` is coherent in `𝔏₀ = N(L̂₀)` for the Dade map of `L̂₀`. -/
def CoherentQuot (L0hat : Set X) (n : ℕ) (Hs : Fin n → Subgroup X)
    {Lb : Type u} [Group Lb] [Fintype Lb] (φ : ↥(L0g L0hat) →* Lb)
    (S : Finset (Lb → ℂ)) : Prop :=
  Tame.FTCoherent L0hat n Hs (S.image (infl φ))

/-- Hypothesis 11.1 (v): each equivalence class of `𝓢` is either subcoherent in `𝓢` or consists
of irreducible characters. -/
def ClassIrrOrSub (L0hat : Set X) (n : ℕ) (Hs : Fin n → Subgroup X)
    {Lb : Type u} [Group Lb] [Fintype Lb] (φ : ↥(L0g L0hat) →* Lb)
    (S : Finset (Lb → ℂ)) (χ : Lb → ℂ) : Prop :=
  (ClassOf S χ : Set (Lb → ℂ)) ⊆ (CharCore.Irr Lb : Set (Lb → ℂ)) ∨
    ∃ τstar : (↥(L0g L0hat) → ℂ) →ₗ[ℤ] (X → ℂ),
      Tame.Subcoherent L0hat n Hs (S.image (infl φ))
        ((ClassOf S χ).image (infl φ)) τstar

end Setup

/-! ## Hypothesis 11.1 (p. 817) -/

section Main

variable [Group X] [Fintype X]

/-- **Feit–Thompson Hypothesis 11.1** (ch. III p. 817).  `L̂₀` is a tamely imbedded subset of
`𝔛` with `𝔏₀ = N(L̂₀)` of odd order, `ℌ₀ ⊴ 𝔏₀` and `L̂₀` a union of `ℌ₀`-cosets; `𝔏 = 𝔏₀/ℌ₀`
(presented by the surjective `φ`, with `ℌ₀ = ker φ`), `L̂` the image of `L̂₀`; `ℌ, 𝔎 ⊴ 𝔏` with
`ℌ` nilpotent and

(11.1)  `ℌ ⊆ ⋃_{H ∈ ℌ^#} C(H) ∩ 𝔎 ⊆ L̂ ⊆ 𝔎 ⊆ 𝔏`;

`𝓢` is the set of all characters of `𝔏` induced by non-principal irreducible characters of `𝔎`
which vanish outside `L̂`, and it consists of pairwise orthogonal characters; there is `d` with
`d·|𝔏:𝔎| ∣ χ(1)` for `χ ∈ 𝓢` and `𝓢` contains an irreducible of degree `d·|𝔏:𝔎|`; each
equivalence class of `𝓢` (same degree and same weight) is subcoherent in `𝓢` or consists of
irreducible characters.

The centralizers in (11.1) are those of the group `𝔏` (Feit–Thompson ch. I p. 777: `C(H)`
without subscript is the centralizer in the group under discussion).

The normal subgroup `ℌ₀` of `𝔏₀` is not a separate parameter: only the quotient map `φ` enters
(i)–(vi), and it enters only through the surjectivity of `φ` and through the condition `sat`
which says that `L̂₀` is a union of cosets of `ker φ`. -/
structure Hyp11_1 (L0hat : Set X) (n : ℕ) (Hs : Fin n → Subgroup X)
    (Lb : Type u) [Group Lb] [Fintype Lb] where
  /-- (i) `L̂₀` is tamely imbedded in `𝔛`. -/
  tamely : Tame.IsTamelyImbedded L0hat n Hs
  /-- the non-degeneracy normalisation of Definition 9.1 (`𝔇 ≠ ∅ ∨ n = 0`), the field
  `HasTameData` of `Tame.Hyp10_1`; it is required to use the Dade map `τ` of (9.4) and hence
  Theorem 10.1.  Feit–Thompson's Hypothesis 11.1 does not mention it because their `L̂` is a
  genuine tamely imbedded set; in every application `𝔇 ≠ ∅` or `n = 0`. -/
  tameData : Tame.HasTameData L0hat n Hs
  /-- (i) `𝔏₀ = N(L̂₀)` has odd order. -/
  odd_card : Odd (Nat.card ↥(L0g L0hat))
  /-- the quotient map `𝔏₀ →* 𝔏`. -/
  φ : ↥(L0g L0hat) →* Lb
  /-- `φ` is onto, i.e. `𝔏 = 𝔏₀/ℌ₀`. -/
  surj : Function.Surjective φ
  /-- (i) `L̂₀` is a union of cosets of `ℌ₀ = ker φ`. -/
  sat : ∀ l y : ↥(L0g L0hat), φ l = φ y → (l : X) ∈ L0hat → (y : X) ∈ L0hat
  /-- (ii) `ℌ ⊴ 𝔏`. -/
  H : Subgroup Lb
  /-- (ii) `𝔎 ⊴ 𝔏`. -/
  K : Subgroup Lb
  H_normal : H.Normal
  K_normal : K.Normal
  /-- (ii) `ℌ` is nilpotent. -/
  H_nilpotent : Group.IsNilpotent ↥H
  /-- (iii) `𝓢`. -/
  S : Finset (Lb → ℂ)
  /-- (iv) the integer `d`. -/
  d : ℕ
  hd : 1 ≤ d
  /-- (11.1), first inclusion: `ℌ ⊆ ⋃_{H ∈ ℌ^#} C(H) ∩ 𝔎`. -/
  h11_1_a : (H : Set Lb) ⊆ ⋃ h ∈ Tame.punct (H : Set Lb),
      (((Subgroup.centralizer ({h} : Set Lb)) ⊓ K : Subgroup Lb) : Set Lb)
  /-- (11.1), second inclusion: `⋃_{H ∈ ℌ^#} C(H) ∩ 𝔎 ⊆ L̂`. -/
  h11_1_b : (⋃ h ∈ Tame.punct (H : Set Lb),
      (((Subgroup.centralizer ({h} : Set Lb)) ⊓ K : Subgroup Lb) : Set Lb)) ⊆ LhatImg φ
  /-- (11.1), third inclusion: `L̂ ⊆ 𝔎`. -/
  h11_1_c : LhatImg φ ⊆ (K : Set Lb)
  /-- (iii) `𝓢` is the set of all characters of `𝔏` induced by non-principal irreducible
  characters of `𝔎` which vanish outside `L̂`. -/
  S_eq : S = Sset K (LhatImg φ)
  /-- (iii) `𝓢` consists of pairwise orthogonal characters. -/
  S_orth : ∀ χ ∈ S, ∀ ψ ∈ S, χ ≠ ψ → Coherence.cfInner χ ψ = 0
  /-- (iv) `d·|𝔏:𝔎| ∣ χ(1)` for `χ ∈ 𝓢`. -/
  S_dvd : ∀ χ ∈ S, (d * K.index) ∣ CharCore.irrDeg χ
  /-- (iv) `𝓢` contains an irreducible character of degree `d·|𝔏:𝔎|`. -/
  S_irr : ∃ χ ∈ S, χ ∈ CharCore.Irr Lb ∧ CharCore.irrDeg χ = d * K.index
  /-- (v) each equivalence class of `𝓢` is subcoherent in `𝓢` or consists of irreducible
  characters. -/
  classes : ∀ χ ∈ S, ClassIrrOrSub L0hat n Hs φ S χ

/-- **Feit–Thompson Theorem 11.1** (ch. III p. 817).

Suppose that Hypothesis 11.1 is satisfied, let `ℌ₁ ⊴ 𝔏` with `ℌ₁ ≤ ℌ` and
`|ℌ:ℌ₁| > 4d²|𝔏:𝔎|² + 1` (11.5).  If `𝓢(ℌ₁)` is coherent and contains an irreducible character
of degree `d|𝔏:𝔎|`, then `𝓢` is coherent. -/
def FT11_1 (L0hat : Set X) (n : ℕ) (Hs : Fin n → Subgroup X) : Prop :=
  ∀ (Lb : Type u) [Group Lb] [Fintype Lb] (h : Hyp11_1 L0hat n Hs Lb)
    (H1 : Subgroup Lb), H1.Normal → H1 ≤ h.H →
    4 * h.d ^ 2 * h.K.index ^ 2 + 1 < H1.relIndex h.H →
    CoherentQuot L0hat n Hs h.φ (SofA h.S H1) →
    (∃ χ ∈ SofA h.S H1, χ ∈ CharCore.Irr Lb ∧
      CharCore.irrDeg χ = h.d * h.K.index) →
    CoherentQuot L0hat n Hs h.φ h.S

/-! ## Hypothesis 11.2 (p. 819) and Hypothesis 11.3 (p. 821) -/

/-- `𝔏/𝔎` is a Frobenius group with Frobenius kernel `ℌ/𝔎` (`𝔎 ⊴ 𝔏`).  This is the
formulation, in the vocabulary of `Work.Spine`, of Feit–Thompson's "`𝔏/𝔎` is a Frobenius group
with Frobenius kernel `ℌ/𝔎`": `𝔎` is identified with its image in the quotient, which is a
non-trivial proper normal subgroup of `𝔏/𝔎` containing the centralizer of each of its
non-identity elements. -/
def IsFrobeniusOver (Lb : Type u) [Group Lb] (H K : Subgroup Lb) (hK : K.Normal) : Prop :=
  letI := hK
  FTSpine.IsFrobeniusIn (⊤ : Subgroup (Lb ⧸ K)) (H.map (QuotientGroup.mk' K))

/-- FT Hypothesis 11.2 (ii): `𝔏/ℌ'` is a Frobenius group with Frobenius kernel `ℌ/ℌ'`
(`ℌ' = [ℌ,ℌ]`). -/
def IsFrobeniusQuotDerived (Lb : Type u) [Group Lb] (H : Subgroup Lb) (hH : H.Normal) : Prop :=
  letI := hH
  IsFrobeniusOver Lb H ⁅H, H⁆ inferInstance

/-- FT's `ℌ' = [ℌ,ℌ]`. -/
def derived {Lb : Type u} [Group Lb] (H : Subgroup Lb) : Subgroup Lb := ⁅H, H⁆

/-- FT's `[ℌ,ℌ']`, occurring in Lemma 11.5. -/
def commDerived {Lb : Type u} [Group Lb] (H : Subgroup Lb) : Subgroup Lb :=
  ⁅H, derived H⁆

/-- **Feit–Thompson Hypothesis 11.2** (ch. III p. 819).  (i) Hypothesis 11.1 *and equation
(11.2)* — `ℌ = L̂ = 𝔎 ⊂ 𝔏` — are satisfied; *thus* `d = 1` (Feit–Thompson state this
consequence as part of the hypothesis, and Lemmas 11.1–11.6 use it).  (ii) `|𝔏|` is odd and
`𝔏/ℌ'` is a Frobenius group with Frobenius kernel `ℌ/ℌ'`. -/
structure Hyp11_2 (L0hat : Set X) (n : ℕ) (Hs : Fin n → Subgroup X)
    (Lb : Type u) [Group Lb] [Fintype Lb] extends Hyp11_1 L0hat n Hs Lb where
  /-- (11.2): `ℌ = L̂`. -/
  eq_11_2_a : (H : Set Lb) = LhatImg φ
  /-- (11.2): `L̂ = 𝔎`. -/
  eq_11_2_b : LhatImg φ = (K : Set Lb)
  /-- (11.2): `𝔎 ⊂ 𝔏`. -/
  eq_11_2_c : K ≠ ⊤
  /-- (i) `d = 1`. -/
  d_eq_one : d = 1
  /-- (ii) `|𝔏|` is odd. -/
  odd_L : Odd (Nat.card Lb)
  /-- (ii) `𝔏/ℌ'` is a Frobenius group with Frobenius kernel `ℌ/ℌ'`. -/
  frobenius : IsFrobeniusQuotDerived Lb H H_normal

/-- **Feit–Thompson Hypothesis 11.3** (ch. III p. 821).  Hypothesis 11.2 and: there are primes
`p`, `q` and positive integers `a`, `b` with `|𝔏:ℌ| = p^b` and
`|ℌ:ℌ'| = |ℌ:D(ℌ)| = q^a`.  (`D(𝔛)` is the Frattini subgroup, ch. I p. 777.) -/
structure Hyp11_3 (L0hat : Set X) (n : ℕ) (Hs : Fin n → Subgroup X)
    (Lb : Type u) [Group Lb] [Fintype Lb] extends Hyp11_2 L0hat n Hs Lb where
  /-- the prime `p` of (ii). -/
  p : ℕ
  /-- the prime `q` of (ii). -/
  q : ℕ
  hp : p.Prime
  hq : q.Prime
  /-- the exponent `a`. -/
  a : ℕ
  /-- the exponent `b`. -/
  b : ℕ
  /-- `|𝔏:ℌ| = p^b`. -/
  index_eq : K.index = p ^ b
  /-- `|ℌ:ℌ'| = q^a`. -/
  deriv_eq : H.relIndex ⁅H, H⁆ = q ^ a
  /-- `|ℌ:D(ℌ)| = q^a` (`D(ℌ) = Φ(ℌ)`). -/
  frattini_eq : H.relIndex (PGroup.frattiniIn H) = q ^ a

end Main

end Work.CohApps
