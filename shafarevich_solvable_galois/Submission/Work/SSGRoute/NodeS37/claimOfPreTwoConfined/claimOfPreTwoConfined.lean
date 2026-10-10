import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.NodeS37.tblockBasics
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.NodeS37.claimOfPreTwoConfined

open _root_.SSGRoute

open scoped Pointwise

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# The confinement of the classes of the `p = 2` §4 recursion outside the escape prime

`Work.SSGRoute.ZDataTwo.TwoRec.PreTwo`'s clause (7) confines the `m`-th class `z_m = χ_{b_m}` of the
Schmidt--Wingberg `p = 2` recursion to the `K`-classes of the stage-`m` place set `T_m` **and** of the
escape prime `Q_m = (s.f m).1`: it kills the inertia of every finite place `B` that is
`K`-non-conjugate to all blocks of `T_m` and to `Q_m`.

The lemma below removes the first exclusion: **every** finite place `B` that is not `K`-conjugate to
the escape prime `Q_m` has its inertia killed by `z_m`.  The extra cases are the blocks of `T_m`
themselves, which are settled without any arithmetic:

* at a block above a `k`-class of `S`, the invariant's realisation clause gives `z_m = y` on the local
  group, and the hypothesis `hyT` kills `y` on inertia there;
* at a block above the `k`-class of an earlier escape prime `Q_l` (`l < m`), the attachment of the
  block is unique (`NodeS37.attach_unique`), so the realisation clause and the collapse of the
  prescribed datum (`TwoRec.prescDatum_eq_of_attachment`) give `z_m = e_{l,ρ} · z_l` on the local
  group; the scalar `e_{l,ρ}` vanishes at `ρ = 1`, and otherwise `NodeS37.tblock_not_gesKConj_sibling`
  and `ZDataMup.siblingPlace_not_gesKConj` show that the block is `K`-non-conjugate to all of `T_l`
  and to `Q_l`, so that clause (7) *at the earlier stage* `l` gives `z_l = 0` on the inertia there.

The two `K`-conjugacy facts are the whole content: `m`-blocks above `S` are `k`-non-conjugate to the
escape primes, and `m`-blocks above `Q_l` are `k`-non-conjugate to `S` and to the other escape primes
(`PreTwo`'s clauses (4), (5), together with `TBlock_covers_S`).
-/

/-- **No escape prime of the `p = 2` recursion is `k`-conjugate to a place of `S`.**  The place set
`TBlock S s.f l` carries a `K`-class representative above every `k`-class of `S`; a `k`-conjugate of
an element of `S` therefore has a representative in `TBlock S s.f l`, which `K`-conjugacy would make
`K`-conjugate to the stage's own escape prime `(s.f l).1` -- forbidden by the invariant. -/
theorem escape_not_isConjPlace_S {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K Λ : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω] [FiniteDimensional k Λ] [IsGalois k Λ]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (y : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (s : Work.SSGRoute.ZDataTwo.TwoRec.St (K := K))
    (hs : ∀ n, Work.SSGRoute.ZDataTwo.TwoRec.PreTwo (K := K) Λ ζ hζ hζK S y n s) :
    ∀ (n l : ℕ), l < n → ∀ A₀ ∈ S, ¬ SSGRoute.IsConjPlace k A₀ ((s.f l).1) := by
  intro n l hln A₀ hA₀ hconj
  obtain ⟨A', hA', hA'Q⟩ :=
    Work.SSGRoute.ZDataTwo.TwoRec.TBlock_covers_S (K := K) (S := S) (f := s.f) (m := l) hA₀ hconj
  obtain ⟨-, -, -, -, h5, -, -, -, -⟩ := hs n
  exact h5 l hln A' hA' hA'Q

theorem claimOfPreTwoConfined {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K Λ : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω] [FiniteDimensional k Λ] [IsGalois k Λ] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (y : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (s : Work.SSGRoute.ZDataTwo.TwoRec.St (K := K))
    (hs : ∀ n, Work.SSGRoute.ZDataTwo.TwoRec.PreTwo (K := K) Λ ζ hζ hζK S y n s) :
    ∀ m : ℕ, ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K ((s.f m).1) B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 σ = 0 := by
  intro m B hBfin hQB σ hσK hσI
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hs (m + 1)
  have hm : m < m + 1 := Nat.lt_succ_self m
  -- the escape primes below stage `m` are `K`-split, and pairwise `k`-fresh
  have hsplitK : ∀ j < m, SSGRoute.IsSplitIn k K (s.f j).1 :=
    fun j hj => Work.SSGRoute.NodeS35.isSplitIn_of_le hKΛ (h2 j (by omega))
  have hdisjLt : ∀ i j : ℕ, i < j → j < m → ¬ SSGRoute.IsConjPlace k (s.f i).1 (s.f j).1 :=
    fun i j hij hjm => h4 i j hij (by omega)
  have hdisjNe : ∀ j l : ℕ, j < m → l < m → j ≠ l →
      ¬ SSGRoute.IsConjPlace k (s.f j).1 (s.f l).1 := by
    intro j l hj hl hne hc
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact h4 j l hlt (by omega) hc
    · exact h4 l j hgt (by omega) (Work.SSGRoute.isConjPlace_symm hc)
  -- the local statement: `z_m` kills the inertia of every block of the stage-`m` place set
  have key : ∀ A ∈ Work.SSGRoute.ZDataTwo.TwoRec.TBlock S s.f m, SSGRoute.IsFinPlace k A →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 σ = 0 := by
    intro A hA hAfin σ hσK hσI
    have hreal := h6 m hm A hA σ ⟨hσI.1, hσK⟩
    rcases Work.SSGRoute.ZDataTwo.TwoRec.TBlock_mem_cases (K := K) hA with
      ⟨A₀, hA₀, ρ, hAtt⟩ | ⟨l, hl, ρ, hAtt⟩
    · -- the block lies above a `k`-class of `S`
      obtain ⟨τ, -, hτ⟩ := hAtt
      have hconj : ∃ A₀ ∈ S, SSGRoute.IsConjPlace k A₀ A :=
        ⟨A₀, hA₀, ⟨τ * Work.SSGRoute.ZDataMup.galLift K ρ,
          by rw [mul_smul]; simpa [Work.SSGRoute.ZDataMup.siblingPlace] using hτ⟩⟩
      have hz : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 σ = y σ := by
        have hzero : Work.SSGRoute.ZDataTwo.TwoRec.prescDatum (K := K) ζ hζ hζK S y s.f m A σ
            = 0 :=
          congrFun (Work.SSGRoute.ZDataTwo.TwoRec.prescDatum_eq_zero_of_isConjPlace (K := K)
            (ζ := ζ) (hζ := hζ) (hζK := hζK) (S := S) (y := y) (f := s.f) (m := m) (A := A)
            hconj) σ
        rw [hreal, hzero, add_zero]
      rw [hz]
      exact hyT A hAfin hconj σ hσK hσI
    · -- the block lies above the `k`-class of an earlier escape prime
      have hQlA : SSGRoute.IsConjPlace k ((s.f l).1) A := by
        obtain ⟨τ, -, hτ⟩ := hAtt
        exact ⟨τ * Work.SSGRoute.ZDataMup.galLift K ρ,
          by rw [mul_smul]; simpa [Work.SSGRoute.ZDataMup.siblingPlace] using hτ⟩
      have hAQ : SSGRoute.IsConjPlace k A ((s.f l).1) := Work.SSGRoute.isConjPlace_symm hQlA
      have hSnotA : ¬ ∃ A₀ ∈ S, SSGRoute.IsConjPlace k A₀ A := by
        rintro ⟨A₀, hA₀, hc⟩
        exact escape_not_isConjPlace_S (K := K) (Λ := Λ) ζ hζ hζK S y s hs (m + 1) l (by omega)
          A₀ hA₀ (Work.SSGRoute.isConjPlace_trans hc hAQ)
      have huniq : ∀ l' : ℕ, l' < m → ∀ ρ' : K ≃ₐ[k] K,
          Work.SSGRoute.gesKConj K (Work.SSGRoute.ZDataMup.siblingPlace K ρ' (s.f l').1) A →
          l' = l ∧ ρ' = ρ := by
        intro l' hl' ρ' h'
        have hq := Work.SSGRoute.NodeS37.attach_unique (K := K) (f := s.f) hsplitK hdisjNe
          (A := A) (q := (l, ρ)) (q' := (l', ρ')) hl hl' hAtt h'
        exact ⟨(congrArg Prod.fst hq).symm, (congrArg Prod.snd hq).symm⟩
      have hpresc := Work.SSGRoute.ZDataTwo.TwoRec.prescDatum_eq_of_attachment (K := K)
        (ζ := ζ) (hζ := hζ) (hζK := hζK) (S := S) (y := y) (f := s.f) (m := m) (A := A)
        hSnotA (l := l) hl hAtt huniq
      have hz : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 σ
          = Work.SSGRoute.ZDataTwo.TwoRec.eScalar ζ hζ hζK s.f l m ρ •
              Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f l).2 σ := by
        have hpσ : Work.SSGRoute.ZDataTwo.TwoRec.prescDatum (K := K) ζ hζ hζK S y s.f m A σ
            = - y σ + Work.SSGRoute.ZDataTwo.TwoRec.eScalar ζ hζ hζK s.f l m ρ •
                Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f l).2 σ :=
          congrFun hpresc σ
        rw [hreal, hpσ]; abel
      rw [hz]
      by_cases he : Work.SSGRoute.ZDataTwo.TwoRec.eScalar ζ hζ hζK s.f l m ρ = 0
      · rw [he, zero_smul]
      · have hρ : ρ ≠ 1 := by
          intro hρ1
          exact he (by rw [Work.SSGRoute.ZDataTwo.TwoRec.eScalar]; exact dif_pos hρ1)
        -- the block is `K`-non-conjugate to every block of the earlier place set
        have hTl : ∀ A' ∈ Work.SSGRoute.ZDataTwo.TwoRec.TBlock S s.f l,
            ¬ Work.SSGRoute.gesKConj K A' A := by
          intro A' hA' hconj
          exact Work.SSGRoute.NodeS37.tblock_not_gesKConj_sibling (K := K) (S := S) (m := m)
            (f := s.f) hdisjLt (fun j hj A'' hA'' => h5 j (by omega) A'' hA'') l hl ρ hρ A' hA'
            (Work.SSGRoute.H9.swGesKConj_trans hconj
              (Work.SSGRoute.H9.swGesKConj_symm hAtt))
        -- and to the earlier escape prime itself
        have hQlK : ¬ Work.SSGRoute.gesKConj K ((s.f l).1) A := by
          intro hconj
          exact (Work.SSGRoute.ZDataMup.siblingPlace_not_gesKConj K hρ (hsplitK l hl))
            (Work.SSGRoute.H9.swGesKConj_trans hconj (Work.SSGRoute.H9.swGesKConj_symm hAtt))
        have hzl : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f l).2 σ = 0 := by
          obtain ⟨-, -, -, -, -, -, -, h8l, -⟩ := hs (l + 1)
          exact h8l l (Nat.lt_succ_self l) A hAfin hTl hQlK σ hσK hσI
        rw [hzl, smul_zero]
  -- the confinement clause, when `B` is `K`-non-conjugate to the whole place set
  by_cases hT : ∀ A ∈ Work.SSGRoute.ZDataTwo.TwoRec.TBlock S s.f m,
      ¬ Work.SSGRoute.gesKConj K A B
  · exact h8 m hm B hBfin hT hQB σ hσK hσI
  · -- otherwise `B` is a `K`-conjugate of a block, and the local statement transports
    push Not at hT
    obtain ⟨A, hA, hAB⟩ := hT
    obtain ⟨v, hvK, hvA⟩ := hAB
    have hAfin : SSGRoute.IsFinPlace k A :=
      (Work.SSGRoute.isFinPlace_smul_iff A v).mp (by rw [hvA]; exact hBfin)
    have hv1 : SSGRoute.res k K v = 1 := by
      rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker K]; exact hvK
    have hσ1 : SSGRoute.res k K σ = 1 := by
      rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker K]; exact hσK
    have hσ'K : v⁻¹ * σ * v ∈ K.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker K, MonoidHom.mem_ker, map_mul, map_mul,
        map_inv, hv1, hσ1]
      simp
    have hσ'I : SSGRoute.IsInertia k A (v⁻¹ * σ * v) :=
      (Work.SSGRoute.isInertia_conj A v (v⁻¹ * σ * v)).mp (by
        have h1 : v * (v⁻¹ * σ * v) * v⁻¹ = σ := by group
        rw [h1, hvA]
        exact hσI)
    have hkey := key A hA hAfin (v⁻¹ * σ * v) hσ'K hσ'I
    have hconjv := Work.SSGRoute.ZDataMup.nodeKummerCocharZMod_conj (K := K) (ζ := ζ)
      (hζ := hζ) (hζK := hζK) (b := (s.f m).2) hvK (v⁻¹ * σ * v)
    have h1 : v * (v⁻¹ * σ * v) * v⁻¹ = σ := by group
    rw [h1] at hconjv
    rw [hconjv]
    exact hkey

end Work.SSGRoute.NodeS37.claimOfPreTwoConfined
