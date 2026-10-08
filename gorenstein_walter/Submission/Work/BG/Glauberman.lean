import Submission.Work.BG.Defs
import Submission.Work.BG.glauberman_two
import Submission.OddOrder.GroupTheory.RepresentationTheory.InducedTransport
import Submission.OddOrder.GroupTheory.RepresentationTheory.Clifford

/-!
# Area BG: BG Lemma 1.9 for a general 2-group `S` (design pass 11)

Copied verbatim from `Submission/Work/_design_gw/Core11BG.lean` (namespace `GW2.C11BG`) into
`Work.BG`, as instructed by the lead's design pass 11.  The two assembly theorems and the
instance bridge are **proved**; the seven leaves are `Prop`s awaiting dispatch.

**Route (no quotient groups, no new representation theory).**  Strong induction on
`|φ(S)|` (the image of `S` in `Aut U`), not on `|S|`:

* `φ(S) = 1`: `C_U(S) = U`; this is `glauberman_two` at `σ = 1` (`fixedSubgroup 1 = ⊤`).
* `φ(S) ≠ 1`: `φ(S)` is a non-trivial 2-group, so its centre contains an involution
  `σ = φ s₀` (BG-L1).  Put `U₁ := C_U(σ) = fixedSubgroup σ`.
  1. `glauberman_two` (proved) for `σ`: a unique `α₁ ∈ Irr(U₁)` with `(α|U₁, α₁)` odd;
     equivalently *every other* constituent of `α|U₁` has **even** multiplicity.
  2. `S` acts on `U₁` (`σ` is central in `φ(S)`): `φ₁ : S →* Aut(U₁)` (BG-L2), and
     `C_{U₁}(φ₁) = C_U(φ)` viewed inside `U₁` (BG-L3).  `φ₁ s₀ = 1` while `φ s₀ ≠ 1`, so
     `|φ₁(S)| < |φ(S)|` (BG-L4) and the induction hypothesis applies to `(U₁, φ₁)`.
  3. `α₁` is `φ₁`-invariant: `α₁^s` has the same (odd) multiplicity in `α|U₁ = (α|U₁)^s`, so
     `α₁^s = α₁` by uniqueness (BG-L5).
  4. **Parity transfer** (BG-L6): for every `β ∈ Irr(C_U(S))`,
     `(α|_C, β) ≡ (α₁|_C, β) (mod 2)`, because `α|_C = Σ_θ m_θ θ|_C` over `θ ∈ Irr(U₁)`, all
     `m_θ` and `(θ|_C, β)` are natural numbers, `m_θ` is even for `θ ≠ α₁` and odd for `α₁`.
  5. So the `β` with odd multiplicity for `α` are exactly those for `α₁`, and the induction
     hypothesis gives exactly one.

The "`S → S/Z`" step the paper leaves implicit is replaced by step 2 (restricting the same `S`
to `U₁`); the orbit argument usually quoted is not needed, because step 1 already says that
*all* `θ ≠ α₁` (invariant or not) have even multiplicity.

[CHECKED] in GAP (`_design_gw/gw11_bg.g`, `gw11_bg2.g`): for `U ∈ {C₃², 3^{1+2}_±, F₂₁,
C₃×F₂₁, C₅², 5^{1+2}_+, F₂₁², F₂₁×C₃²}` and **every** conjugacy class of 2-subgroups `P` of
`Aut(U)` (115 pairs `(U,P)`, `|P|` up to 32): uniqueness of the odd constituent, invariance of
`α₁`, and the parity transfer of step 4 hold for every `P`-invariant `α`; in all cases
`#Irr_P(U) = #Irr(C_U(P))`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory Subgroup

/-! ## 0. Instance-free vocabulary -/

/-- `(α|_K, θ)` is an odd integer.  The `Fintype`/`Invertible` instances are chosen inside, so
that this can be rewritten along an equality of subgroups `K = K'` (`rw`/`subst` work). -/
noncomputable def IsOddMult {U : Type} [Group U] [Finite U] (K : Subgroup U)
    (α : ClassFunction U ℂ) (θ : ClassFunction K ℂ) : Prop :=
  letI : Fintype K := Fintype.ofFinite K
  letI : Invertible (Nat.card K : ℂ) := invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  ∃ k : ℤ, ClassFunction.inner (ClassFunction.restrict K α) θ = (2 * k + 1 : ℂ)

/-- Lemma 1.9's conclusion relative to a subgroup `K ≤ U`. -/
def OddMultUnique {U : Type} [Group U] [Finite U] (K : Subgroup U)
    (α : IrreducibleCharacter U) : Prop :=
  ∃! β : IrreducibleCharacter K, IsOddMult K (α : ClassFunction U ℂ) (β : ClassFunction K ℂ)

/-- `α` is invariant under every `φ s`. -/
def IsInvariant {S U : Type} [Group S] [Group U] (φ : S →* MulAut U)
    (α : ClassFunction U ℂ) : Prop :=
  ∀ (s : S) (u : U), α (φ s u) = α u

/-- The general statement in instance-free form, with the induction measure `|φ(S)| ≤ n`. -/
def GlaubAtMost (n : ℕ) : Prop :=
  ∀ {S U : Type} [Group S] [Group U] [Finite S] [Finite U], IsPGroup 2 S → Odd (Nat.card U) →
    ∀ φ : S →* MulAut U, Nat.card φ.range ≤ n →
    ∀ α : IrreducibleCharacter U, IsInvariant φ (α : ClassFunction U ℂ) →
      OddMultUnique (fixedSubgroupS φ) α

/-! ## 1. Leaves -/

/-- **BG-L0 (instance bridge).**  `IsOddMult` agrees with the instance-parametric form used in
`glauberman_two` and `glaubermanGeneralProp`.  Proof: `Fintype`/`Invertible` are subsingletons;
`unfold IsOddMult; congr!` (or `Subsingleton.elim` on both instances). -/
def OddMultBridgeProp : Prop :=
  ∀ {U : Type} [Group U] [Finite U] [Fintype U] (K : Subgroup U) [Fintype K]
    [Invertible (Nat.card K : ℂ)] (α : ClassFunction U ℂ) (θ : ClassFunction K ℂ),
    IsOddMult K α θ ↔
      ∃ k : ℤ, ClassFunction.inner (ClassFunction.restrict K α) θ = (2 * k + 1 : ℂ)

/-- **BG-L1 (a central involution of the image).**  If `φ(S) ≠ 1` for a 2-group `S`, some
`φ s₀` is an involution commuting with every `φ s`.  Proof: `IsPGroup.map`,
`IsPGroup.center_nontrivial` on `φ.range`, Cauchy (`exists_prime_orderOf_dvd_card`) in the
centre. -/
def CentralInvolutionProp : Prop :=
  ∀ {S U : Type} [Group S] [Group U] [Finite S], IsPGroup 2 S → ∀ φ : S →* MulAut U,
    φ.range ≠ ⊥ →
    ∃ s₀ : S, φ s₀ ≠ 1 ∧ φ s₀ * φ s₀ = 1 ∧ ∀ s : S, φ s * φ s₀ = φ s₀ * φ s

/-- **BG-L2 (the restricted action).**  If `σ` commutes with every `φ s`, then `S` acts on
`U₁ = fixedSubgroup σ` by restriction.  Proof: `φ s` maps `U₁` into itself
(`σ (φ s u) = φ s (σ u) = φ s u`), similarly `(φ s)⁻¹`; build the `MulEquiv` and check
`map_one`/`map_mul` by `ext`. -/
def RestrictToFixedProp : Prop :=
  ∀ {S U : Type} [Group S] [Group U] (φ : S →* MulAut U) (σ : MulAut U),
    (∀ s : S, φ s * σ = σ * φ s) →
    ∃ φ₁ : S →* MulAut ↥(fixedSubgroup σ),
      ∀ (s : S) (u : ↥(fixedSubgroup σ)), ((φ₁ s u : ↥(fixedSubgroup σ)) : U) = φ s u

/-- **BG-L3 (fixed points of the restricted action).**  With `σ = φ s₀`:
`C_U(φ) ≤ U₁` and `C_{U₁}(φ₁) = C_U(φ) ∩ U₁` as a subgroup of `U₁`.  Proof: unfold
`fixedSubgroupS`, `Subgroup.mem_subgroupOf`, use the defining property of `φ₁`. -/
def FixedRestrictProp : Prop :=
  ∀ {S U : Type} [Group S] [Group U] (φ : S →* MulAut U) (s₀ : S)
    (φ₁ : S →* MulAut ↥(fixedSubgroup (φ s₀))),
    (∀ (s : S) (u : ↥(fixedSubgroup (φ s₀))), ((φ₁ s u : ↥(fixedSubgroup (φ s₀))) : U) = φ s u) →
    fixedSubgroupS φ ≤ fixedSubgroup (φ s₀) ∧
      fixedSubgroupS φ₁ = (fixedSubgroupS φ).subgroupOf (fixedSubgroup (φ s₀))

/-- **BG-L4 (the measure drops).**  `φ₁ s₀ = 1` (it is `σ` restricted to its own fixed points),
`ker φ ≤ ker φ₁` and `s₀ ∈ ker φ₁ \ ker φ`; hence `|φ₁(S)| < |φ(S)|`.  Proof:
`QuotientGroup.quotientKerEquivRange` (both ranges are `S/ker`), and
`Subgroup.card_lt_of_lt` on the kernels. -/
def RangeCardLtProp : Prop :=
  ∀ {S U : Type} [Group S] [Group U] [Finite S] (φ : S →* MulAut U) (s₀ : S),
    φ s₀ ≠ 1 →
    ∀ φ₁ : S →* MulAut ↥(fixedSubgroup (φ s₀)),
    (∀ (s : S) (u : ↥(fixedSubgroup (φ s₀))), ((φ₁ s u : ↥(fixedSubgroup (φ s₀))) : U) = φ s u) →
    Nat.card φ₁.range < Nat.card φ.range

/-- **BG-L5 (the odd constituent is invariant).**  If `α` is `φ`-invariant and `α₁` is the only
irreducible of `U₁` with odd multiplicity in `α|U₁`, then `α₁` is `φ₁`-invariant.  Proof: for
`s : S` let `e := φ₁ s`; `θ ↦ compHom e θ` permutes `Irr(U₁)`
(`IsIrreducibleCharacter.compHom_of_surjective`), `compHom e (α|U₁) = α|U₁` (invariance of
`α`), and `inner_compHom_of_mulEquiv` gives the same multiplicity, so
`compHom e α₁ = α₁` by uniqueness. -/
def InvariantOddConstituentProp : Prop :=
  ∀ {S U : Type} [Group S] [Group U] [Finite U] (φ : S →* MulAut U) (s₀ : S)
    (φ₁ : S →* MulAut ↥(fixedSubgroup (φ s₀))),
    (∀ (s : S) (u : ↥(fixedSubgroup (φ s₀))), ((φ₁ s u : ↥(fixedSubgroup (φ s₀))) : U) = φ s u) →
    ∀ (α : IrreducibleCharacter U) (α₁ : IrreducibleCharacter ↥(fixedSubgroup (φ s₀))),
      IsInvariant φ (α : ClassFunction U ℂ) →
      (∀ θ : IrreducibleCharacter ↥(fixedSubgroup (φ s₀)),
        IsOddMult (fixedSubgroup (φ s₀)) (α : ClassFunction U ℂ) (θ : ClassFunction _ ℂ) ↔
          θ = α₁) →
      IsInvariant φ₁ (α₁ : ClassFunction ↥(fixedSubgroup (φ s₀)) ℂ)

/-- **BG-L6 (parity transfer — the core of the induction step).**  `C ≤ U₁ ≤ U`, `α ∈ Irr U`,
and `α₁` the only irreducible of `U₁` with odd multiplicity in `α|U₁`.  Then for every
`β ∈ Irr C`: `(α|_C, β)` is odd iff `(α₁|_C, β)` is odd (the latter computed in `U₁`, with `β`
transported along `e : C.subgroupOf U₁ ≃* C`).

Proof: `sum_inner_irreducibleCharacter_smul` expands `α|U₁ = Σ_θ m_θ • θ`; restriction is
linear and `compHom e (α|_C) = (α|U₁)|_{C.subgroupOf U₁}` (`ext; rfl`); `inner_compHom_of_mulEquiv`
moves the inner product to `C.subgroupOf U₁`; so `(α|_C, β) = Σ_θ m_θ (θ|, β')`.  Every `m_θ`
and `(θ|, β')` is a natural number (`restrictionMultiplicity_natCast`); `m_θ` is even for
`θ ≠ α₁` (a natural that is not odd) and odd for `θ = α₁`.  Reduce mod 2. -/
def ParityTransferProp : Prop :=
  ∀ {U : Type} [Group U] [Finite U] (U₁ C : Subgroup U) (hC : C ≤ U₁)
    (α : IrreducibleCharacter U) (α₁ : IrreducibleCharacter U₁),
    (∀ θ : IrreducibleCharacter U₁,
      IsOddMult U₁ (α : ClassFunction U ℂ) (θ : ClassFunction U₁ ℂ) ↔ θ = α₁) →
    ∀ β : IrreducibleCharacter C,
      IsOddMult C (α : ClassFunction U ℂ) (β : ClassFunction C ℂ) ↔
        IsOddMult (C.subgroupOf U₁) (α₁ : ClassFunction U₁ ℂ)
          (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hC).toMonoidHom
            (β : ClassFunction C ℂ))

/-- **BG-L6b (transport of `Irr` along `C.subgroupOf U₁ ≃* C`).**  `β ↦ compHom e β` is a
bijection `Irr C → Irr (C.subgroupOf U₁)` (inverse `compHom e.symm`).  With BG-L6 it turns
`OddMultUnique (C.subgroupOf U₁) α₁` into `OddMultUnique C α`. -/
def OddMultUniqueTransportProp : Prop :=
  ∀ {U : Type} [Group U] [Finite U] (U₁ C : Subgroup U) (hC : C ≤ U₁)
    (α : IrreducibleCharacter U) (α₁ : IrreducibleCharacter U₁),
    (∀ β : IrreducibleCharacter C,
      IsOddMult C (α : ClassFunction U ℂ) (β : ClassFunction C ℂ) ↔
        IsOddMult (C.subgroupOf U₁) (α₁ : ClassFunction U₁ ℂ)
          (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hC).toMonoidHom
            (β : ClassFunction C ℂ))) →
    OddMultUnique (C.subgroupOf U₁) α₁ → OddMultUnique C α

/-- **BG-L7 (base cases from the proved `glauberman_two`, in `OddMultUnique` form).**
(a) For an automorphism `σ` with `σ² = 1` and `σ`-invariant `α`:
`OddMultUnique (fixedSubgroup σ) α` (`glauberman_two` + BG-L0).
(b) If `φ.range = ⊥` then `fixedSubgroupS φ = ⊤ = fixedSubgroup 1`, so (a) at `σ = 1` gives
`OddMultUnique (fixedSubgroupS φ) α` (`rw` along the subgroup equality). -/
def BaseOddMultProp : Prop :=
  ∀ {U : Type} [Group U] [Finite U], Odd (Nat.card U) →
    ∀ (σ : MulAut U), σ * σ = 1 → ∀ α : IrreducibleCharacter U,
      (∀ u : U, (α : ClassFunction U ℂ) (σ u) = (α : ClassFunction U ℂ) u) →
      OddMultUnique (fixedSubgroup σ) α

/-! ## 2. Assembly -/

/-- The induction (`Nat.strong_induction_on n`): the case `φ.range = ⊥` is BG-L7(b); otherwise
BG-L1 gives `σ = φ s₀`, BG-L7(a) gives `α₁` (and, by uniqueness, "odd ↔ `θ = α₁`"), BG-L2/L3/L4/L5
give `(U₁, φ₁, α₁)` with smaller measure, the induction hypothesis gives
`OddMultUnique (fixedSubgroupS φ₁) α₁`, rewrite with BG-L3, and finish with BG-L6 + BG-L6b. -/
theorem glaubAtMost_of_leaves (h0 : BaseOddMultProp) (h1 : CentralInvolutionProp)
    (h2 : RestrictToFixedProp) (h3 : FixedRestrictProp) (h4 : RangeCardLtProp)
    (h5 : InvariantOddConstituentProp) (h6 : ParityTransferProp)
    (h6b : OddMultUniqueTransportProp) : ∀ n, GlaubAtMost n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S U _ _ _ _ hS hU φ hn α hα
  by_cases hφ : φ.range = ⊥
  · have hfix : fixedSubgroupS φ = fixedSubgroup (1 : MulAut U) := by
      ext u
      simp only [mem_fixedSubgroupS, mem_fixedSubgroup]
      constructor
      · intro _; rfl
      · intro _ s
        have hs : φ s ∈ φ.range := ⟨s, rfl⟩
        rw [hφ, Subgroup.mem_bot] at hs
        rw [hs]; rfl
    rw [hfix]
    exact h0 hU 1 (by simp) α (fun u => rfl)
  · obtain ⟨s₀, hs₀1, hs₀2, hs₀c⟩ := h1 hS φ hφ
    obtain ⟨φ₁, hφ₁⟩ := h2 φ (φ s₀) hs₀c
    obtain ⟨α₁, hα₁, huniq⟩ := h0 hU (φ s₀) hs₀2 α (fun u => hα s₀ u)
    have hodd : ∀ θ : IrreducibleCharacter ↥(fixedSubgroup (φ s₀)),
        IsOddMult (fixedSubgroup (φ s₀)) (α : ClassFunction U ℂ) (θ : ClassFunction _ ℂ) ↔
          θ = α₁ := fun θ => ⟨fun h => huniq θ h, fun h => h ▸ hα₁⟩
    obtain ⟨hle, heq⟩ := h3 φ s₀ φ₁ hφ₁
    have hlt := h4 φ s₀ hs₀1 φ₁ hφ₁
    have hinv := h5 φ s₀ φ₁ hφ₁ α α₁ hα hodd
    have hU₁odd : Odd (Nat.card ↥(fixedSubgroup (φ s₀))) :=
      Odd.of_dvd_nat hU (Subgroup.card_subgroup_dvd_card _)
    have hIH := ih (Nat.card φ₁.range) (lt_of_lt_of_le hlt hn) hS hU₁odd φ₁ le_rfl α₁ hinv
    rw [heq] at hIH
    exact h6b _ _ hle α α₁ (h6 _ _ hle α α₁ hodd) hIH

/-- The area's target from the instance-free form: take `n := Nat.card φ.range`, then BG-L0 to
convert `OddMultUnique (fixedSubgroupS φ) α` into the instance-parametric conclusion of
`Work.BG.glaubermanGeneralProp`. -/
theorem glaubermanGeneral_of_glaubAtMost (h : ∀ n, GlaubAtMost n) (hb : OddMultBridgeProp) :
    Work.BG.glaubermanGeneralProp := by
  intro S U _ _ _ _ _ _ hS hU φ _ _ α hα
  obtain ⟨β, hβ, huniq⟩ := h (Nat.card φ.range) hS hU φ le_rfl α hα
  exact ⟨β, (hb _ _ _).1 hβ, fun β' hβ' => huniq β' ((hb _ _ _).2 hβ')⟩

/-- BG-L0 is checked here. -/
theorem oddMultBridge : OddMultBridgeProp := by
  intro U _ _ _ K _ _ α θ
  unfold IsOddMult
  congr!
  all_goals exact Subsingleton.elim _ _

end Work.BG
