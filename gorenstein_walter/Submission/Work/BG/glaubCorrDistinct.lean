import Mathlib
import Submission.Work.BG.Defs
import Submission.Work.BG.Glauberman
import Submission.Work.BG.GlaubermanAssembly
import Submission.Work.BG.CharBridge
import Submission.Work.BG.lemma18LinearIndependent
import Submission.Work.BG.glaubValue
import Submission.Work.BG.glaubMultCongruence
import Submission.Work.BG.hatInjCongruentEq
import Submission.Work.BG.centralInvolution
import Submission.Work.BG.restrictToFixed
import Submission.Work.BG.fixedRestrict
import Submission.Work.BG.rangeCardLt
import Submission.Work.BG.invariantOddConstituent
import Submission.Work.BG.parityTransfer
import Submission.Work.BG.hatInjCore
import Submission.Work.BG.hatInjCountAlt
import Submission.Work.BG.hatInjParity

/-!
# Area BG: distinct `S`-invariant irreducibles are distinguished modulo `2` on `C_U(S)`

The target `Work.BG.glaubCorrDistinct`: for a `2`-group `S` acting by automorphisms `φ` on a
group `U` of odd order, two **distinct** `S`-invariant irreducible characters `α ≠ α'` of `U`
differ modulo `2` (Bender–Glauberman's `≡`) at some point of `C_U(S) = fixedSubgroupS φ`.

Mathematically this is the *injectivity* of Glauberman's correspondence
`α ↦ α*` (BG 1981, Lemma 1.9, "moreover each `β` corresponds to a unique `α`"): if
`α ≡ α'` at every point of `C_U(S)`, then `α` and `α'` have the same `α*` (the congruence
form of Lemma 1.9, `Work.BG.glaubValue`), hence are equal.

The proof below is organised as follows.

* `Work.BG.isOddMult_iff_eq_of_oddMultUnique` — the `∀ θ ↔ θ = β` form of `OddMultUnique`.
* `Work.BG.pointwiseTwoInj_of_twoInj` — the `|S| = 2` case in *pointwise* form, obtained from
  the odd-constituent form `Work.BG.glaubTwoDistinct` together with the congruence
  `Work.BG.algIntModTwo_of_oddMult_fixedSubgroup` (a direct consequence of
  `Work.BG.glaubMultCongruence` and the uniqueness of the odd constituent,
  `Work.BG.baseOddMult`) and `Work.BG.hatInjCongruentEq`.
* `Work.BG.CorrInjAtMost` / `Work.BG.corrInjAtMost_of_base` — the induction on `|φ(S)|`:
  for a non-trivial image pick a central involution `σ = φ s₀` of `φ(S)`, let
  `U₁ = C_U(σ)`, `α₁, α₁'` the `σ`-constituents of `α, α'` on `U₁`; `S` acts on `U₁` with a
  strictly smaller image (`Work.BG.restrictToFixed`, `Work.BG.rangeCardLt`),
  `α₁, α₁'` are invariant (`Work.BG.invariantOddConstituent`), and the pointwise congruence on
  `C_U(S)` transfers to `α₁, α₁'` by the `σ`-congruences (`Work.BG.parityTransfer` is not even
  needed for this step).  The induction hypothesis gives `α₁ = α₁'`, and then two applications
  of the `|S| = 2` case give `α = α'`.
* `Work.BG.glaubCorrDistinct` — contraposition of the induction statement at
  `n = |φ(S)|`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

/-! ## 0. Elementary helpers -/

/-- The `∀ θ ↔ θ = β` form of `OddMultUnique`: from uniqueness of the odd constituent `γ` of
`α|_K` and an odd-multiplicity witness `β`, every odd-multiplicity constituent of `α|_K`
equals `β`. -/
theorem isOddMult_iff_eq_of_oddMultUnique {U : Type} [Group U] [Finite U] (K : Subgroup U)
    (α : IrreducibleCharacter U) {β : IrreducibleCharacter K} (h : OddMultUnique K α)
    (hβ : IsOddMult K (α : ClassFunction U ℂ) (β : ClassFunction K ℂ)) :
    ∀ θ : IrreducibleCharacter K,
      IsOddMult K (α : ClassFunction U ℂ) (θ : ClassFunction K ℂ) ↔ θ = β := by
  obtain ⟨γ, hγ, huniq⟩ := h
  have hγβ : γ = β := (huniq β hβ).symm
  intro θ
  exact ⟨fun hθ => (huniq θ hθ).trans hγβ, fun hθ => hθ ▸ hβ⟩

/-- **Values of the odd constituent of `α|_K` are congruent to those of `α` modulo `2`**, for
`K = C_U(σ)` (`σ` an involution) — the `|A| = 2` case of `Work.BG.glaubValue`, in the form
needed below.  (Bender–Glauberman 1981, p. 202: `α ≡ α*` on `B`.) -/
theorem algIntModTwo_of_oddMult_fixedSubgroup {U : Type} [Group U] [Finite U] [Fintype U]
    [Invertible (Nat.card U : ℂ)] (hU : Odd (Nat.card U)) (σ : MulAut U) (hσ : σ * σ = 1)
    (α : IrreducibleCharacter U)
    (hα : ∀ u : U, (α : ClassFunction U ℂ) (σ u) = (α : ClassFunction U ℂ) u)
    (β : IrreducibleCharacter ↥(fixedSubgroup σ))
    (hβ : IsOddMult (fixedSubgroup σ) (α : ClassFunction U ℂ)
      (β : ClassFunction ↥(fixedSubgroup σ) ℂ)) :
    ∀ b : ↥(fixedSubgroup σ),
      AlgIntModTwo ((α : ClassFunction U ℂ) (b : U))
        ((β : ClassFunction ↥(fixedSubgroup σ) ℂ) b) := by
  haveI : Fintype ↥(fixedSubgroup σ) := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥(fixedSubgroup σ) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  refine glaubMultCongruence (fixedSubgroup σ) (α : ClassFunction U ℂ) α.isIrreducible β ?_
  intro θ
  exact (oddMultBridge (fixedSubgroup σ) (α : ClassFunction U ℂ)
      (θ : ClassFunction ↥(fixedSubgroup σ) ℂ)).symm.trans
    (isOddMult_iff_eq_of_oddMultUnique (fixedSubgroup σ) α
      (baseOddMult hU σ hσ α hα) hβ θ)

/-! ## 1. The `|S| = 2` case in pointwise form -/

/-- The `|S| = 2` base case of the injectivity induction, in the *pointwise* form used by the
induction: if two `σ`-invariant irreducible characters of an odd-order group `U` agree
modulo `2` at every point of `C_U(σ)`, they are equal. -/
def PointwiseTwoInjProp : Prop :=
  ∀ {U : Type} [Group U] [Finite U] [Fintype U] [Invertible (Nat.card U : ℂ)]
    (hU : Odd (Nat.card U)) (σ : MulAut U) (hσ : σ * σ = 1)
    (α α' : ClassFunction U ℂ) (hα : IsIrreducibleCharacter α)
    (hα' : IsIrreducibleCharacter α')
    (hinv : ∀ u : U, α (σ u) = α u) (hinv' : ∀ u : U, α' (σ u) = α' u)
    (hcong : ∀ b : ↥(fixedSubgroup σ), AlgIntModTwo (α (b : U)) (α' (b : U))), α = α'

/-- The odd-constituent form of the base case (`Work.BG.glaubTwoDistinct`), as a `Prop`. -/
def TwoInjProp : Prop :=
  ∀ {U : Type} [Group U] [Finite U] [Fintype U] [Invertible (Nat.card U : ℂ)]
    (hU : Odd (Nat.card U)) (σ : MulAut U) (hσ : σ * σ = 1)
    (α α' : ClassFunction U ℂ) (hα : IsIrreducibleCharacter α)
    (hα' : IsIrreducibleCharacter α')
    (hinv : ∀ u : U, α (σ u) = α u) (hinv' : ∀ u : U, α' (σ u) = α' u) (hne : α ≠ α')
    (β : ClassFunction ↥(fixedSubgroup σ) ℂ) (hβ : IsIrreducibleCharacter β)
    (hodd : IsOddMult (fixedSubgroup σ) α β)
    (hodd' : IsOddMult (fixedSubgroup σ) α' β), False

/-- **The `|S| = 2` case.**  This is exactly `Work.BG.glauberman_injective` — the injectivity of
Glauberman's correspondence for an involution, proved in the repository from the count
`Work.BG.hatInjCountAlt` and the column parity `Work.BG.hatInjParity` — together with the two
combinations `α ≡ α*` resp. `α' ≡ α'*` of values modulo `2` on `C_U(σ)`. -/
theorem pointwiseTwoInj : PointwiseTwoInjProp := by
  intro U _ _ _ _ hU σ hσ α α' hα hα' hinv hinv' hcong
  haveI : Fintype ↥(fixedSubgroup σ) := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥(fixedSubgroup σ) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  exact glauberman_injective hU σ hσ (hatInjCountAlt hU σ hσ)
    (fun β => hatInjParity hU σ hσ β) hα hinv hα' hinv' (fun c => hcong c)

/-- The pointwise form of the `|S| = 2` case follows from the odd-constituent form
`Work.BG.glaubTwoDistinct`: assuming a pointwise congruence on `C_U(σ)`, the odd constituents
`β` of `α|_B` and `β'` of `α'|_B` are congruent modulo `2` (`glaubMultCongruence`), hence equal
(`Work.BG.hatInjCongruentEq`, since `|B|` is odd), and then `glaubTwoDistinct` applies. -/
theorem pointwiseTwoInj_of_twoInj (h : TwoInjProp) : PointwiseTwoInjProp := by
  intro U _ _ _ _ hU σ hσ α α' hα hα' hinv hinv' hcong
  by_contra hne
  obtain ⟨β, hβodd, _⟩ := baseOddMult hU σ hσ ⟨α, hα⟩ hinv
  obtain ⟨β', hβ'odd, _⟩ := baseOddMult hU σ hσ ⟨α', hα'⟩ hinv'
  have hcβ := algIntModTwo_of_oddMult_fixedSubgroup hU σ hσ ⟨α, hα⟩ hinv β hβodd
  have hcβ' := algIntModTwo_of_oddMult_fixedSubgroup hU σ hσ ⟨α', hα'⟩ hinv' β' hβ'odd
  haveI : Fintype ↥(fixedSubgroup σ) := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥(fixedSubgroup σ) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hBodd : Odd (Nat.card ↥(fixedSubgroup σ)) :=
    Odd.of_dvd_nat hU (Subgroup.card_subgroup_dvd_card _)
  have hβcong : ∀ b : ↥(fixedSubgroup σ),
      AlgIntModTwo ((β : ClassFunction ↥(fixedSubgroup σ) ℂ) b)
        ((β' : ClassFunction ↥(fixedSubgroup σ) ℂ) b) :=
    fun b => ((hcβ b).symm.trans (hcong b)).trans (hcβ' b)
  have hβeq : (β : ClassFunction ↥(fixedSubgroup σ) ℂ) =
      (β' : ClassFunction ↥(fixedSubgroup σ) ℂ) :=
    hatInjCongruentEq hBodd β.isIrreducible β'.isIrreducible hβcong
  exact h hU σ hσ α α' hα hα' hinv hinv' hne
    (β : ClassFunction ↥(fixedSubgroup σ) ℂ) β.isIrreducible hβodd (hβeq.symm ▸ hβ'odd)

/-! ## 2. The induction on `|φ(S)|` -/

/-- Injectivity of Glauberman's correspondence in pointwise form, with the induction measure
`|φ(S)| ≤ n`: two distinct `S`-invariant irreducible characters of `U` cannot agree modulo `2`
at every point of `C_U(S)`. -/
def CorrInjAtMost (n : ℕ) : Prop :=
  ∀ {S U : Type} [Group S] [Group U] [Finite S] [Finite U] [Fintype U]
    [Invertible (Nat.card U : ℂ)], IsPGroup 2 S → Odd (Nat.card U) →
    ∀ φ : S →* MulAut U, Nat.card φ.range ≤ n →
    ∀ α α' : ClassFunction U ℂ, IsIrreducibleCharacter α → IsIrreducibleCharacter α' →
      (∀ (s : S) (u : U), α (φ s u) = α u) → (∀ (s : S) (u : U), α' (φ s u) = α' u) →
      (∀ b : ↥(fixedSubgroupS φ), AlgIntModTwo (α (b : U)) (α' (b : U))) →
      α = α'

/-- **The induction step.**  Trivial action: `C_U(S) = U`, so the pointwise congruence holds on
all of `U` and `Work.BG.hatInjCongruentEq` gives `α = α'`.  Otherwise pick a central involution
`σ = φ s₀` of `φ(S)` (`Work.BG.centralInvolution`), reduce to `U₁ = C_U(σ)`
(`Work.BG.restrictToFixed`, `Work.BG.fixedRestrict`, `Work.BG.rangeCardLt`,
`Work.BG.invariantOddConstituent`), apply the induction hypothesis to the `σ`-constituents
`α₁, α₁'` (their congruence on `C_U(S)` is a consequence of the `σ`-congruences
`α ≡ α₁`, `α' ≡ α₁'` on `U₁`), and finish with the `|S| = 2` case for the pair `(α, α')`. -/
theorem corrInjAtMost_of_base (hbase : PointwiseTwoInjProp) : ∀ n, CorrInjAtMost n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S U _ _ _ _ _ _ hS hU φ hn α α' hα hα' hinv hinv' hcong
    by_cases hφ : φ.range = ⊥
    · -- trivial action: `C_U(S) = U`
      have hfix : fixedSubgroupS φ = ⊤ := by
        ext u
        simp only [mem_fixedSubgroupS, Subgroup.mem_top, iff_true]
        intro s
        have hs : φ s ∈ φ.range := ⟨s, rfl⟩
        rw [hφ, Subgroup.mem_bot] at hs
        rw [hs]; rfl
      refine hatInjCongruentEq hU hα hα' (fun u => ?_)
      exact hcong ⟨u, by rw [hfix]; trivial⟩
    · -- the induction step
      obtain ⟨s₀, hs₀1, hs₀2, hs₀c⟩ := centralInvolution hS φ hφ
      obtain ⟨φ₁, hφ₁⟩ := restrictToFixed φ (φ s₀) hs₀c
      obtain ⟨hle, heq⟩ := fixedRestrict φ s₀ φ₁ hφ₁
      have hlt := rangeCardLt φ s₀ hs₀1 φ₁ hφ₁
      obtain ⟨α₁, hα₁odd, huniq₁⟩ := baseOddMult hU (φ s₀) hs₀2 ⟨α, hα⟩ (hinv s₀)
      obtain ⟨α₁', hα₁'odd, huniq₁'⟩ := baseOddMult hU (φ s₀) hs₀2 ⟨α', hα'⟩ (hinv' s₀)
      have hodd₁ := isOddMult_iff_eq_of_oddMultUnique (fixedSubgroup (φ s₀)) ⟨α, hα⟩
        (baseOddMult hU (φ s₀) hs₀2 ⟨α, hα⟩ (hinv s₀)) hα₁odd
      have hodd₁' := isOddMult_iff_eq_of_oddMultUnique (fixedSubgroup (φ s₀)) ⟨α', hα'⟩
        (baseOddMult hU (φ s₀) hs₀2 ⟨α', hα'⟩ (hinv' s₀)) hα₁'odd
      have hinvα₁ := invariantOddConstituent φ s₀ φ₁ hφ₁ ⟨α, hα⟩ α₁ (fun s u => hinv s u) hodd₁
      have hinvα₁' := invariantOddConstituent φ s₀ φ₁ hφ₁ ⟨α', hα'⟩ α₁'
        (fun s u => hinv' s u) hodd₁'
      -- the `σ`-congruences on `U₁ = C_U(σ)`
      have hcα := algIntModTwo_of_oddMult_fixedSubgroup hU (φ s₀) hs₀2 ⟨α, hα⟩ (hinv s₀)
        α₁ hα₁odd
      have hcα' := algIntModTwo_of_oddMult_fixedSubgroup hU (φ s₀) hs₀2 ⟨α', hα'⟩ (hinv' s₀)
        α₁' hα₁'odd
      -- the pointwise congruence for the induction hypothesis
      have hcong₁ : ∀ b : ↥(fixedSubgroupS φ₁),
          AlgIntModTwo ((α₁ : ClassFunction ↥(fixedSubgroup (φ s₀)) ℂ)
              (b : ↥(fixedSubgroup (φ s₀))))
            ((α₁' : ClassFunction ↥(fixedSubgroup (φ s₀)) ℂ)
              (b : ↥(fixedSubgroup (φ s₀)))) := by
        rw [heq]
        intro b
        have hbmem : ((b : ↥(fixedSubgroup (φ s₀))) : U) ∈ fixedSubgroupS φ :=
          Subgroup.mem_subgroupOf.mp b.2
        have hbcong := hcong ⟨((b : ↥(fixedSubgroup (φ s₀))) : U), hbmem⟩
        exact ((hcα (b : ↥(fixedSubgroup (φ s₀)))).symm.trans hbcong).trans
          (hcα' (b : ↥(fixedSubgroup (φ s₀))))
      have hU₁odd : Odd (Nat.card ↥(fixedSubgroup (φ s₀))) :=
        Odd.of_dvd_nat hU (Subgroup.card_subgroup_dvd_card _)
      haveI : Fintype ↥(fixedSubgroup (φ s₀)) := Fintype.ofFinite _
      haveI : Invertible (Nat.card ↥(fixedSubgroup (φ s₀)) : ℂ) :=
        invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
      have hIH := ih (Nat.card φ₁.range) (lt_of_lt_of_le hlt hn) hS hU₁odd φ₁ le_rfl
        (α₁ : ClassFunction ↥(fixedSubgroup (φ s₀)) ℂ)
        (α₁' : ClassFunction ↥(fixedSubgroup (φ s₀)) ℂ)
        α₁.isIrreducible α₁'.isIrreducible hinvα₁ hinvα₁' hcong₁
      -- transfer back and apply the `|S| = 2` case
      refine hbase hU (φ s₀) hs₀2 α α' hα hα' (fun u => hinv s₀ u) (fun u => hinv' s₀ u)
        (fun y => ?_)
      have hyeq : (fun f : ClassFunction ↥(fixedSubgroup (φ s₀)) ℂ =>
            f (y : ↥(fixedSubgroup (φ s₀)))) (α₁ : ClassFunction _ ℂ) =
          (fun f : ClassFunction ↥(fixedSubgroup (φ s₀)) ℂ =>
            f (y : ↥(fixedSubgroup (φ s₀)))) (α₁' : ClassFunction _ ℂ) :=
        congrArg (fun f : ClassFunction ↥(fixedSubgroup (φ s₀)) ℂ => f y) hIH
      have h1 : AlgIntModTwo ((α : ClassFunction U ℂ) (y : U))
          ((fun f : ClassFunction ↥(fixedSubgroup (φ s₀)) ℂ =>
            f (y : ↥(fixedSubgroup (φ s₀)))) (α₁ : ClassFunction _ ℂ)) := hcα y
      have h2 : AlgIntModTwo ((α' : ClassFunction U ℂ) (y : U))
          ((fun f : ClassFunction ↥(fixedSubgroup (φ s₀)) ℂ =>
            f (y : ↥(fixedSubgroup (φ s₀)))) (α₁' : ClassFunction _ ℂ)) := hcα' y
      rw [hyeq] at h1
      exact h1.trans h2.symm

/-- **Distinct `S`-invariant irreducible characters differ modulo `2` on `C_U(S)`**
(Glauberman's correspondence is injective; Bender–Glauberman 1981, Lemma 1.9 "moreover"). -/
theorem glaubCorrDistinct {S U : Type} [Group S] [Group U] [Finite S] [Finite U] [Fintype U]
    [Invertible (Nat.card U : ℂ)] (hS : IsPGroup 2 S) (hU : Odd (Nat.card U))
    (φ : S →* MulAut U) [Fintype ↥(fixedSubgroupS φ)]
    [Invertible (Nat.card ↥(fixedSubgroupS φ) : ℂ)]
    (α α' : ClassFunction U ℂ) (hα : IsIrreducibleCharacter α)
    (hα' : IsIrreducibleCharacter α')
    (hinv : ∀ (s : S) (u : U), α (φ s u) = α u)
    (hinv' : ∀ (s : S) (u : U), α' (φ s u) = α' u) (hne : α ≠ α') :
    ∃ b : ↥(fixedSubgroupS φ), ¬ AlgIntModTwo (α ↑b) (α' ↑b) := by
  by_contra h
  simp only [not_exists, not_not] at h
  exact hne (corrInjAtMost_of_base pointwiseTwoInj
    (Nat.card φ.range) hS hU φ le_rfl α α' hα hα' hinv hinv' h)

end Work.BG
