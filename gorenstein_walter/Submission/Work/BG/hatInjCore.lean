import Mathlib
import Submission.Work.BG.HatInjDefs
import Submission.Work.BG.glauberman_two
import Submission.Work.BG.glaubMultCongruence
import Submission.Work.BG.hatInjCongruentEq

/-!
# Area BG: injectivity of the Glauberman correspondence (abstract core of `HatInjProp`)

For a finite group `U` of odd order with an involutive automorphism `σ` and `C = C_U(σ)`:

* (`glauberman_two`, already proved) every `σ`-invariant `α ∈ Irr U` has a **unique**
  `β ∈ Irr C` occurring with odd multiplicity in `α|_C` — the "row" structure;
* (`hatInjParity`, delegated separately) for every `β ∈ Irr C` an **odd** number of
  `σ`-invariant `α ∈ Irr U` has `β` occurring with odd multiplicity — the "column" parity;
* (`hatInjCount`, delegated separately) `#{σ-invariant α ∈ Irr U} = |Irr C|`.

Row-sum `1` + column-odd + equal cardinalities force each column to have exactly one entry: the
correspondence `α ↦ α*` is a bijection, in particular injective.  Combining this with the
value-form congruence `α ≡ α* (mod 2)` on `C` (`glaubMultCongruence`) and
`hatInjCongruentEq` (two congruent irreducibles of an odd-order group coincide) yields:
`σ`-invariant irreducibles of `U` that agree modulo `2` on `C` are equal.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

variable {U : Type} [Group U]

/-- `β` occurs with odd multiplicity in the restriction of `α` to `C_U(σ)`. -/
def OddMult (σ : MulAut U) [Fintype ↥(fixedSubgroup σ)]
    [Invertible (Nat.card ↥(fixedSubgroup σ) : ℂ)]
    (α : IrreducibleCharacter U) (β : IrreducibleCharacter ↥(fixedSubgroup σ)) : Prop :=
  ∃ k : ℤ, ClassFunction.inner (ClassFunction.restrict (fixedSubgroup σ) (α : ClassFunction U ℂ))
    (β : ClassFunction ↥(fixedSubgroup σ) ℂ) = ((2 * k + 1 : ℤ) : ℂ)

theorem oddMult_iff {U : Type} [Group U] (σ : MulAut U) [Fintype ↥(fixedSubgroup σ)]
    [Invertible (Nat.card ↥(fixedSubgroup σ) : ℂ)]
    (α : IrreducibleCharacter U) (β : IrreducibleCharacter ↥(fixedSubgroup σ)) :
    OddMult σ α β ↔ ∃ k : ℤ,
      ClassFunction.inner (ClassFunction.restrict (fixedSubgroup σ) (α : ClassFunction U ℂ))
        (β : ClassFunction ↥(fixedSubgroup σ) ℂ) = 2 * (k : ℂ) + 1 := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [hk]; push_cast; ring⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [hk]; push_cast; ring⟩

theorem glauberman_injective {U : Type} [Group U] [Finite U] [Fintype U]
    [Invertible (Nat.card U : ℂ)] (hU : Odd (Nat.card U)) (σ : MulAut U) (hσ : σ * σ = 1)
    [Fintype ↥(fixedSubgroup σ)] [Invertible (Nat.card ↥(fixedSubgroup σ) : ℂ)]
    (hcount : Nat.card (SigmaInvIrr U σ) = Nat.card (IrreducibleCharacter ↥(fixedSubgroup σ)))
    (hparity : ∀ β : IrreducibleCharacter ↥(fixedSubgroup σ),
      Odd (Nat.card {α : SigmaInvIrr U σ // OddMult σ (α : IrreducibleCharacter U) β}))
    {α α' : ClassFunction U ℂ} (hα : IsIrreducibleCharacter α) (hαinv : ∀ u, α (σ u) = α u)
    (hα' : IsIrreducibleCharacter α') (hα'inv : ∀ u, α' (σ u) = α' u)
    (hcong : ∀ c : ↥(fixedSubgroup σ), AlgIntModTwo (α c) (α' c)) : α = α' := by
  classical
  -- ## Step 1: the row structure (existence and uniqueness of the odd constituent)
  have row : ∀ a : SigmaInvIrr U σ, ∃! β : IrreducibleCharacter ↥(fixedSubgroup σ),
      OddMult σ (a : IrreducibleCharacter U) β := by
    intro a
    obtain ⟨β, hβ, huniq⟩ := glauberman_two hU σ hσ (a : IrreducibleCharacter U) a.2
    refine ⟨β, (oddMult_iff σ (a : IrreducibleCharacter U) β).mpr hβ, ?_⟩
    intro γ hγ
    exact huniq γ ((oddMult_iff σ (a : IrreducibleCharacter U) γ).mp hγ)
  let φ : SigmaInvIrr U σ → IrreducibleCharacter ↥(fixedSubgroup σ) := fun a => (row a).choose
  have φ_spec : ∀ a : SigmaInvIrr U σ, OddMult σ (a : IrreducibleCharacter U) (φ a) :=
    fun a => (row a).choose_spec.1
  have φ_uniq : ∀ (a : SigmaInvIrr U σ) (β : IrreducibleCharacter ↥(fixedSubgroup σ)),
      OddMult σ (a : IrreducibleCharacter U) β → β = φ a :=
    fun a β h => (row a).choose_spec.2 β h
  -- ## Step 2: the chosen constituent is congruent to `a` modulo `2` on `C`
  have cong_φ : ∀ a : SigmaInvIrr U σ, ∀ c : ↥(fixedSubgroup σ),
      AlgIntModTwo (((a : IrreducibleCharacter U) : ClassFunction U ℂ) c)
        (((φ a : IrreducibleCharacter ↥(fixedSubgroup σ)) : ClassFunction ↥(fixedSubgroup σ) ℂ) c) := by
    intro a c
    exact glaubMultCongruence (fixedSubgroup σ)
      (((a : IrreducibleCharacter U)) : ClassFunction U ℂ) a.1.2 (φ a)
      (fun θ => ⟨fun h => φ_uniq a θ ((oddMult_iff σ (a : IrreducibleCharacter U) θ).mpr h),
          fun h => (oddMult_iff σ (a : IrreducibleCharacter U) θ).mp (h ▸ φ_spec a)⟩) c
  -- ## Step 3: each fibre of `φ` is a singleton
  have fiber_eq : ∀ β : IrreducibleCharacter ↥(fixedSubgroup σ),
      Nat.card {a : SigmaInvIrr U σ // φ a = β}
        = Nat.card {a : SigmaInvIrr U σ // OddMult σ (a : IrreducibleCharacter U) β} :=
    fun β => Nat.card_congr (Equiv.subtypeEquivRight
      (fun a => ⟨fun h => h ▸ φ_spec a, fun h => (φ_uniq a β h).symm⟩))
  have fiber_odd : ∀ β : IrreducibleCharacter ↥(fixedSubgroup σ),
      Odd (Nat.card {a : SigmaInvIrr U σ // φ a = β}) := by
    intro β
    rw [fiber_eq β]
    exact hparity β
  -- the fibres are the level sets of `φ`, so their sizes sum to `|X| = |Y|`
  have hsum : Fintype.card (SigmaInvIrr U σ)
      = ∑ β : IrreducibleCharacter ↥(fixedSubgroup σ),
          (Finset.univ.filter (fun a : SigmaInvIrr U σ => φ a = β)).card := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := φ)
      (fun a _ => Finset.mem_univ _)
  have hcard_eq : ∀ β : IrreducibleCharacter ↥(fixedSubgroup σ),
      (Finset.univ.filter (fun a : SigmaInvIrr U σ => φ a = β)).card
        = Nat.card {a : SigmaInvIrr U σ // φ a = β} := by
    intro β
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have htot : (∑ β : IrreducibleCharacter ↥(fixedSubgroup σ),
        Nat.card {a : SigmaInvIrr U σ // φ a = β})
      = Fintype.card (IrreducibleCharacter ↥(fixedSubgroup σ)) := by
    have h1 : (∑ β : IrreducibleCharacter ↥(fixedSubgroup σ),
          Nat.card {a : SigmaInvIrr U σ // φ a = β}) = Fintype.card (SigmaInvIrr U σ) := by
      rw [hsum]
      exact Finset.sum_congr rfl (fun β _ => (hcard_eq β).symm)
    rw [h1, ← Nat.card_eq_fintype_card, hcount, Nat.card_eq_fintype_card]
  have hge : ∀ β : IrreducibleCharacter ↥(fixedSubgroup σ),
      1 ≤ Nat.card {a : SigmaInvIrr U σ // φ a = β} := by
    intro β
    obtain ⟨k, hk⟩ := fiber_odd β
    omega
  have fiber_one : ∀ β : IrreducibleCharacter ↥(fixedSubgroup σ),
      Nat.card {a : SigmaInvIrr U σ // φ a = β} = 1 := by
    intro β
    have hzero : (∑ β' : IrreducibleCharacter ↥(fixedSubgroup σ),
        (Nat.card {a : SigmaInvIrr U σ // φ a = β'} - 1)) = 0 := by
      have h1 : (∑ β' : IrreducibleCharacter ↥(fixedSubgroup σ),
            ((Nat.card {a : SigmaInvIrr U σ // φ a = β'} - 1) + 1))
          = ∑ β' : IrreducibleCharacter ↥(fixedSubgroup σ),
              Nat.card {a : SigmaInvIrr U σ // φ a = β'} :=
        Finset.sum_congr rfl (fun β' _ => Nat.sub_add_cancel (hge β'))
      rw [Finset.sum_add_distrib] at h1
      rw [htot, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at h1
      omega
    have hle := Finset.single_le_sum
      (f := fun β' : IrreducibleCharacter ↥(fixedSubgroup σ) =>
        Nat.card {a : SigmaInvIrr U σ // φ a = β'} - 1)
      (fun x _ => Nat.zero_le _) (Finset.mem_univ β)
    rw [hzero] at hle
    have := hge β
    omega
  -- ## Step 4: conclude
  let a : SigmaInvIrr U σ := ⟨⟨α, hα⟩, hαinv⟩
  let a' : SigmaInvIrr U σ := ⟨⟨α', hα'⟩, hα'inv⟩
  have hphi : (φ a : ClassFunction ↥(fixedSubgroup σ) ℂ)
      = (φ a' : ClassFunction ↥(fixedSubgroup σ) ℂ) := by
    refine hatInjCongruentEq (K := ↥(fixedSubgroup σ))
      (Odd.of_dvd_nat hU (Subgroup.card_subgroup_dvd_card _))
      (θ := (φ a).1) (θ' := (φ a').1) (φ a).2 (φ a').2 ?_
    intro c
    exact (cong_φ a c).symm.trans ((hcong c).trans (cong_φ a' c))
  have hφeq : φ a = φ a' := Subtype.ext hphi
  have hfiber : (⟨a, rfl⟩ : {x : SigmaInvIrr U σ // φ x = φ a})
      = ⟨a', hφeq.symm ▸ rfl⟩ := by
    obtain ⟨z, hz⟩ := Nat.card_eq_one_iff_exists.mp (fiber_one (φ a))
    exact (hz _).trans (hz _).symm
  have haeq : a = a' := Subtype.ext_iff.mp hfiber
  have : (a : ClassFunction U ℂ) = (a' : ClassFunction U ℂ) :=
    congrArg (fun x : SigmaInvIrr U σ => (x : ClassFunction U ℂ)) haeq
  simpa using this

end Work.BG
