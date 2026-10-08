import Mathlib
import Submission.Work.BG.Glauberman
import Submission.Work.BG.glauberman_two
import Submission.Work.BG.CharBridge

/-!
# Area BG: parity transfer (BG-L6 of the Bender–Glauberman §1 induction)

`Work.BG.ParityTransferProp` (BG-L6) is the core of the induction step of
Bender–Glauberman 1981, Lemma 1.9 (Glauberman's character correspondence) in the
general form needed for a 2-group `S` acting on an odd-order group `U`:

given `C ≤ U₁ ≤ U`, an irreducible `α ∈ Irr(U)` whose restriction to `U₁` has a
*unique* irreducible constituent `α₁` of odd multiplicity, and `β ∈ Irr(C)`, the
multiplicity of `β` in `α|_C` is odd **iff** the multiplicity of the transport of
`β` to `C.subgroupOf U₁` in `α₁|_{C.subgroupOf U₁}` is odd.

The proof has two halves.

* `parityTransfer_aux` is the abstract Fourier/parity computation: for a virtual
  character `A ∈ ℤ[Irr M]` (`M` of any order) and `K ≤ M`, if `A` has a unique
  irreducible constituent `β₀` of odd multiplicity, then for every `γ ∈ Irr(K)` the
  multiplicity of `γ` in `A|_K` is odd iff its multiplicity in `β₀|_K` is odd.  This
  is a reindexing of the expansion `A = Σ_β m_β β` together with
  `restrictionMultiplicity_natCast` and reduction mod 2.

* `parityTransfer` instantiates it with `M = U₁`, `A = α|_{U₁}`, `β₀ = α₁`,
  `K = C.subgroupOf U₁` and `γ = β ∘ e` (where `e : C.subgroupOf U₁ ≃* C`), and uses
  `ClassFunction.restrict_subgroupOf_restrict` (restriction in stages) and
  `inner_compHom_of_mulEquiv` (the inner product is invariant under a group
  isomorphism) to identify the two sides.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

/-- **Parity transfer, abstract form.**  Let `A ∈ ℤ[Irr M]` be a virtual character of a
finite group `M`, let `K ≤ M`, `γ ∈ Irr(K)` and suppose `A` has a unique irreducible
constituent `β₀` (`huniq`) whose multiplicity is odd (`hβ₀`).  Then the multiplicity of
`γ` in `A|_K` is odd if and only if its multiplicity in `β₀|_K` is odd.

Expanding `A = Σ_β m_β β` (`sum_inner_irreducibleCharacter_smul`, `mem_ZIrr_inner_int`),
restricting to `K` and pairing with `γ` gives `⟨A|_K, γ⟩ = Σ_β m_β ⟨β|_K, γ⟩`, with all
factors integral: the `m_β` are integers which are even for `β ≠ β₀` and odd for `β = β₀`,
and the `⟨β|_K, γ⟩` are natural numbers (`restrictionMultiplicity_natCast`).  Reducing the
sum mod 2 leaves `⟨β₀|_K, γ⟩`. -/
theorem parityTransfer_aux {M : Type} [Group M] [Finite M] [Fintype M]
    [Invertible (Nat.card M : ℂ)]
    {K : Subgroup M} [Fintype ↥K] [Invertible (Nat.card ↥K : ℂ)]
    (A : ClassFunction M ℂ) (hA : A ∈ ZIrr M)
    (γ : IrreducibleCharacter ↥K) (β₀ : IrreducibleCharacter M)
    (hβ₀ : ∃ k : ℤ, ClassFunction.inner A (β₀ : ClassFunction M ℂ) = (2 * k + 1 : ℂ))
    (huniq : ∀ β : IrreducibleCharacter M,
      (∃ k : ℤ, ClassFunction.inner A (β : ClassFunction M ℂ) = (2 * k + 1 : ℂ)) → β = β₀) :
    ((∃ k : ℤ, ClassFunction.inner (ClassFunction.restrict K A)
        (γ : ClassFunction ↥K ℂ) = (2 * k + 1 : ℂ)) ↔
      (∃ k : ℤ, ClassFunction.inner (ClassFunction.restrict K (β₀ : ClassFunction M ℂ))
        (γ : ClassFunction ↥K ℂ) = (2 * k + 1 : ℂ))) := by
  classical
  haveI : Fintype (IrreducibleCharacter M) := Fintype.ofFinite _
  -- a uniform description of `(2k+1 : ℂ)`
  have hc01 : ∀ k : ℤ, ((2 * k + 1 : ℤ) : ℂ) = 2 * (k : ℂ) + 1 := by
    intro k
    rw [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one]
  -- oddness of an integer is the same as oddness of its image in `ℂ`
  have key : ∀ z : ℤ, ((∃ k : ℤ, (z : ℂ) = (2 * k + 1 : ℂ)) ↔ Odd z) := by
    intro z
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Int.cast_inj.mp (by rw [hc01 k]; exact hk)⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by rw [hk]; exact hc01 k⟩
  -- multiplicities of `A` at the irreducibles of `M` (integers)
  choose m hm using fun β : IrreducibleCharacter M => mem_ZIrr_inner_int (G := M) β hA
  -- multiplicities of `γ` in the restrictions of the irreducibles of `M` (natural numbers)
  have hn' : ∀ β : IrreducibleCharacter M, ∃ k : ℕ,
      ClassFunction.inner (ClassFunction.restrict K (β : ClassFunction M ℂ))
        (γ : ClassFunction ↥K ℂ) = (k : ℂ) := by
    intro β
    obtain ⟨k, hk⟩ := IrreducibleCharacter.restrictionMultiplicity_natCast K β γ
    exact ⟨k, by rw [← ClassFunction.restrictionMultiplicity_def]; exact hk⟩
  choose n hn using hn'
  -- Fourier expansion of `A`, restricted to `K`
  have hregroup : ∀ s : Finset (IrreducibleCharacter M),
      ClassFunction.restrict K (∑ β ∈ s,
          (ClassFunction.inner A (β : ClassFunction M ℂ)) • (β : ClassFunction M ℂ)) =
        ∑ β ∈ s, (ClassFunction.inner A (β : ClassFunction M ℂ)) •
          ClassFunction.restrict K (β : ClassFunction M ℂ) := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, ClassFunction.restrict_add,
          ClassFunction.restrict_smul, ih]
  have hexp : ClassFunction.inner (ClassFunction.restrict K A) (γ : ClassFunction ↥K ℂ)
      = ∑ β : IrreducibleCharacter M, (m β : ℂ) * (n β : ℂ) := by
    calc ClassFunction.inner (ClassFunction.restrict K A) (γ : ClassFunction ↥K ℂ)
        = ClassFunction.inner (ClassFunction.restrict K (∑ β : IrreducibleCharacter M,
            (ClassFunction.inner A (β : ClassFunction M ℂ)) • (β : ClassFunction M ℂ)))
            (γ : ClassFunction ↥K ℂ) := by
            rw [sum_inner_irreducibleCharacter_smul A]
      _ = ClassFunction.inner (∑ β : IrreducibleCharacter M,
            (ClassFunction.inner A (β : ClassFunction M ℂ)) •
              ClassFunction.restrict K (β : ClassFunction M ℂ))
            (γ : ClassFunction ↥K ℂ) := by rw [hregroup Finset.univ]
      _ = ∑ β : IrreducibleCharacter M, (ClassFunction.inner A (β : ClassFunction M ℂ)) *
            ClassFunction.inner (ClassFunction.restrict K (β : ClassFunction M ℂ))
              (γ : ClassFunction ↥K ℂ) := by
            rw [inner_sum_left]
            exact Finset.sum_congr rfl fun β _ => by rw [ClassFunction.inner_smul_left]
      _ = ∑ β : IrreducibleCharacter M, (m β : ℂ) * (n β : ℂ) :=
            Finset.sum_congr rfl fun β _ => by rw [hm β, hn β]
  -- the ℤ-valued total
  set S : ℤ := ∑ β : IrreducibleCharacter M, m β * (n β : ℤ) with hSdef
  have hcast : ClassFunction.inner (ClassFunction.restrict K A) (γ : ClassFunction ↥K ℂ)
      = (S : ℂ) := by
    rw [hexp, hSdef, Int.cast_sum]
    exact Finset.sum_congr rfl fun β _ => by push_cast; ring
  -- `m β₀` is odd, `m β` is even for `β ≠ β₀`
  have hodd₀ : Odd (m β₀) := by
    obtain ⟨k, hk⟩ := hβ₀
    refine ⟨k, ?_⟩
    have h3 : ((m β₀ : ℤ) : ℂ) = ((2 * k + 1 : ℤ) : ℂ) := by
      rw [hc01 k, ← hm β₀]
      exact hk
    exact Int.cast_inj.mp h3
  have heven : ∀ β : IrreducibleCharacter M, β ≠ β₀ → Even (m β) := by
    intro β hβ
    by_contra hE
    obtain ⟨k, hk⟩ := (Int.not_even_iff_odd).mp hE
    have h2 : ClassFunction.inner A (β : ClassFunction M ℂ) = (2 * k + 1 : ℂ) := by
      rw [hm β, hk, hc01 k]
    exact hβ (huniq β ⟨k, h2⟩)
  -- `S ≡ n β₀ (mod 2)`
  have hevenS : Even (S - (n β₀ : ℤ)) := by
    have hsplit : S = (∑ β ∈ Finset.univ.erase β₀, m β * (n β : ℤ)) +
        m β₀ * (n β₀ : ℤ) := by
      rw [hSdef]
      exact (Finset.sum_erase_add _ _ (Finset.mem_univ β₀)).symm
    have heven1 : Even (∑ β ∈ Finset.univ.erase β₀, m β * (n β : ℤ)) :=
      Finset.even_sum (fun β => m β * (n β : ℤ)) fun β hβ => by
        rw [Finset.mem_erase] at hβ
        exact Even.mul_right (heven β hβ.1) _
    obtain ⟨k, hk⟩ := hodd₀
    have heven2 : Even ((m β₀ - 1) * (n β₀ : ℤ)) :=
      Even.mul_right (⟨k, by rw [hk]; ring⟩ : Even (m β₀ - 1)) _
    have hkey : S - (n β₀ : ℤ) =
        (∑ β ∈ Finset.univ.erase β₀, m β * (n β : ℤ)) +
          ((m β₀ - 1) * (n β₀ : ℤ)) := by
      rw [hsplit]; ring
    rw [hkey]
    exact heven1.add heven2
  have hpar : Odd S ↔ Odd (n β₀ : ℤ) := by
    obtain ⟨t, ht⟩ := hevenS
    have hS' : S = (n β₀ : ℤ) + 2 * t := by linarith
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k - t, by omega⟩
    · rintro ⟨k, hk⟩
      exact ⟨k + t, by omega⟩
  -- both sides are the corresponding oddness
  have hL : (∃ k : ℤ, ClassFunction.inner (ClassFunction.restrict K A)
      (γ : ClassFunction ↥K ℂ) = (2 * k + 1 : ℂ)) ↔ Odd S := by
    rw [hcast]
    exact key S
  have hR : (∃ k : ℤ, ClassFunction.inner (ClassFunction.restrict K (β₀ : ClassFunction M ℂ))
      (γ : ClassFunction ↥K ℂ) = (2 * k + 1 : ℂ)) ↔ Odd (n β₀ : ℤ) := by
    rw [hn β₀, ← Int.cast_natCast]
    exact key (n β₀ : ℤ)
  exact hL.trans (hpar.trans hR.symm)

/-- **BG-L6 (parity transfer).**  `C ≤ U₁ ≤ U`, `α ∈ Irr(U)`, `α₁ ∈ Irr(U₁)` the unique
irreducible of `U₁` of odd multiplicity in `α|_{U₁}`.  Then for every `β ∈ Irr(C)` the
multiplicity of `β` in `α|_C` is odd iff the multiplicity of the transport of `β` to
`C.subgroupOf U₁` in `α₁|_{C.subgroupOf U₁}` is odd. -/
theorem parityTransfer : Work.BG.ParityTransferProp := by
  intro U _ _ U₁ C hC α α₁ huniq β
  classical
  haveI : Fintype U := Fintype.ofFinite U
  haveI : Fintype U₁ := Fintype.ofFinite U₁
  haveI : Fintype C := Fintype.ofFinite C
  haveI : Fintype (C.subgroupOf U₁) := Fintype.ofFinite _
  haveI hI₁ : Invertible (Nat.card U₁ : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI hI₂ : Invertible (Nat.card C : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI hI₃ : Invertible (Nat.card (C.subgroupOf U₁) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let e : ↥(C.subgroupOf U₁) ≃* ↥C := Subgroup.subgroupOfEquivOfLe hC
  let A : ClassFunction ↥U₁ ℂ := ClassFunction.restrict U₁ (α : ClassFunction U ℂ)
  have hA : A = ClassFunction.restrict U₁ (α : ClassFunction U ℂ) := rfl
  let γ : IrreducibleCharacter ↥(C.subgroupOf U₁) :=
    ⟨ClassFunction.compHom e.toMonoidHom (β : ClassFunction C ℂ),
      IsIrreducibleCharacter.compHom_of_surjective e.surjective β.isIrreducible⟩
  have hγval : (γ : ClassFunction ↥(C.subgroupOf U₁) ℂ)
      = ClassFunction.compHom e.toMonoidHom (β : ClassFunction C ℂ) := rfl
  have hAz : A ∈ ZIrr ↥U₁ := by
    rw [hA]; exact ClassFunction.restrict_mem_ZIrr U₁ α.mem_ZIrr
  -- `α₁` has odd multiplicity in `A = α|_{U₁}`
  have hβ₀ : ∃ k : ℤ, ClassFunction.inner A (α₁ : ClassFunction ↥U₁ ℂ) = (2 * k + 1 : ℂ) := by
    have h := (oddMultBridge U₁ (α : ClassFunction U ℂ)
      (α₁ : ClassFunction ↥U₁ ℂ)).1 ((huniq α₁).mpr rfl)
    rw [← hA] at h
    exact h
  -- and it is the only such irreducible
  have huniq' : ∀ θ : IrreducibleCharacter ↥U₁,
      (∃ k : ℤ, ClassFunction.inner A (θ : ClassFunction ↥U₁ ℂ) = (2 * k + 1 : ℂ)) → θ = α₁ := by
    intro θ hθ
    have hodd : IsOddMult U₁ (α : ClassFunction U ℂ) (θ : ClassFunction ↥U₁ ℂ) :=
      (oddMultBridge U₁ (α : ClassFunction U ℂ) (θ : ClassFunction ↥U₁ ℂ)).2 (by
        rw [hA] at hθ; exact hθ)
    exact (huniq θ).1 hodd
  have haux := parityTransfer_aux (M := ↥U₁) (K := C.subgroupOf U₁) A hAz γ α₁ hβ₀ huniq'
  -- the `C`-side of the auxiliary statement is the multiplicity in `α|_C`
  have hLHS : (∃ k : ℤ, ClassFunction.inner (ClassFunction.restrict (C.subgroupOf U₁) A)
        (γ : ClassFunction ↥(C.subgroupOf U₁) ℂ) = (2 * k + 1 : ℂ))
      ↔ (∃ k : ℤ, ClassFunction.inner (ClassFunction.restrict C (α : ClassFunction U ℂ))
        (β : ClassFunction C ℂ) = (2 * k + 1 : ℂ)) := by
    have h1 : ClassFunction.restrict (C.subgroupOf U₁) A
        = ClassFunction.compHom e.toMonoidHom
            (ClassFunction.restrict C (α : ClassFunction U ℂ)) := by
      rw [hA]
      exact ClassFunction.restrict_subgroupOf_restrict hC (α : ClassFunction U ℂ)
    rw [h1, hγval,
      inner_compHom_of_mulEquiv e (ClassFunction.restrict C (α : ClassFunction U ℂ))
        (β : ClassFunction C ℂ)]
  rw [← hγval]
  have hL : IsOddMult C (α : ClassFunction U ℂ) (β : ClassFunction C ℂ) ↔
      (∃ k : ℤ, ClassFunction.inner (ClassFunction.restrict C (α : ClassFunction U ℂ))
        (β : ClassFunction C ℂ) = (2 * k + 1 : ℂ)) :=
    oddMultBridge C (α : ClassFunction U ℂ) (β : ClassFunction C ℂ)
  have hR : IsOddMult (C.subgroupOf U₁) (α₁ : ClassFunction ↥U₁ ℂ)
        (γ : ClassFunction ↥(C.subgroupOf U₁) ℂ) ↔
      (∃ k : ℤ, ClassFunction.inner
        (ClassFunction.restrict (C.subgroupOf U₁) (α₁ : ClassFunction ↥U₁ ℂ))
        (γ : ClassFunction ↥(C.subgroupOf U₁) ℂ) = (2 * k + 1 : ℂ)) :=
    oddMultBridge (C.subgroupOf U₁) (α₁ : ClassFunction ↥U₁ ℂ)
      (γ : ClassFunction ↥(C.subgroupOf U₁) ℂ)
  rw [hL, hR]
  exact hLHS.symm.trans haux

end Work.BG
