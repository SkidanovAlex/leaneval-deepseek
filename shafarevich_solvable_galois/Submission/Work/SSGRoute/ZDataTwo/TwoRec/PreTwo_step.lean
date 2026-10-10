import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.P2Core.siblingPlace
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.inv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The one-stage step of the `p = 2` §4 recursion

`Work.SSGRoute.ZDataTwo.TwoRec.PreTwo_step`: from a history satisfying the prefix invariant
`TwoRec.PreTwo` at stage `n`, the escape oracle `TwoRec.Oracle` (i.e. the proved
`Work.SSGRoute.P2Core.escapeStepNormalised`) applied at the place set `TBlock S s.f n` with the
global datum `y` and the prescribed datum `prescDatum` produces a new escape prime and class such
that the invariant holds at stage `n+1`.

This is the `p = 2` mirror of `Work.SSGRoute.H9.Pre_step`
(`Submission/Work/SSGRoute/H9/swHistKExists_proved.lean`).
-/

open scoped Pointwise

namespace Work.SSGRoute.ZDataTwo.TwoRec

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  [IsAlgClosed Ω]
variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  [IsSepClosure ↥K Ω]

/-! ## Two auxiliary facts about the place set -/

/-- **The membership cases of `TBlock` in `k`-level form**: an element of `TBlock S f m` is
`k`-conjugate to an element of `S`, or to one of the escape primes `(f j).1` with `j < m`. -/
theorem TBlock_mem_cases_k {S : Finset (ValuationSubring Ω)}
    {f : ℕ → (ValuationSubring Ω × (↥K)ˣ)} {m : ℕ} {A : ValuationSubring Ω}
    (hA : A ∈ TBlock S f m) :
    (∃ A₀ ∈ S, SSGRoute.IsConjPlace k A₀ A) ∨
      (∃ j : ℕ, j < m ∧ SSGRoute.IsConjPlace k (f j).1 A) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [TBlock] at hA
  obtain ⟨A'', hA'', hA''A⟩ := Work.SSGRoute.H9.krep_mem_classes K _ A hA
  have hA''A' : SSGRoute.IsConjPlace k A A'' := by
    obtain ⟨τ, -, hτ⟩ := hA''A
    exact ⟨τ, hτ⟩
  rcases Finset.mem_union.mp hA'' with h1 | h2
  · obtain ⟨A₀, hA₀, hA₀A''⟩ :=
      Work.SSGRoute.ZDataMup.kleadReps_mem_conjPlace (p := 2) K h1
    exact Or.inl ⟨A₀, hA₀, SSGRoute.isConjPlace_trans hA₀A'' (SSGRoute.isConjPlace_symm hA''A')⟩
  · obtain ⟨j, hj, hjmem⟩ := Finset.mem_biUnion.mp h2
    obtain ⟨A₀, hA₀, hA₀A''⟩ :=
      Work.SSGRoute.ZDataMup.kleadReps_mem_conjPlace (p := 2) K hjmem
    rw [Finset.mem_singleton] at hA₀
    subst hA₀
    exact Or.inr ⟨j, Finset.mem_range.mp hj, SSGRoute.isConjPlace_trans hA₀A'' (SSGRoute.isConjPlace_symm hA''A')⟩

/-- **The attachment of a block of the recursion to a pair `(l, ρ)` is unique.**  If the escape
primes `f j` (`j < n`) are split in `K` and pairwise non-`k`-conjugate, then a place `A` can be
`K`-conjugate to the `ρ`-sibling of `(f l).1` for at most one pair `(l, ρ)`. -/
theorem siblingPlace_attach_unique {f : ℕ → (ValuationSubring Ω × (↥K)ˣ)} {n : ℕ}
    (hsplitK : ∀ l : ℕ, l < n → SSGRoute.IsSplitIn k K (f l).1)
    (hdisjk : ∀ l l' : ℕ, l < n → l' < n → l ≠ l' →
      ¬ SSGRoute.IsConjPlace k (f l).1 (f l').1)
    {A : ValuationSubring Ω} {l l' : ℕ} (hl : l < n) (hl' : l' < n) {ρ ρ' : K ≃ₐ[k] K}
    (h : Work.SSGRoute.gesKConj K (Work.SSGRoute.ZDataMup.siblingPlace K ρ (f l).1) A)
    (h' : Work.SSGRoute.gesKConj K (Work.SSGRoute.ZDataMup.siblingPlace K ρ' (f l').1) A) :
    l = l' ∧ ρ = ρ' := by
  have hQsplitK : ∀ i : Fin n, SSGRoute.IsSplitIn k K ((fun i : Fin n => (f i).1) i) :=
    fun i => hsplitK i i.2
  have hQdisj : ∀ i j : Fin n, SSGRoute.IsConjPlace k ((fun i : Fin n => (f i).1) i)
      ((fun i : Fin n => (f j).1) j) → i = j := by
    intro i j hij
    by_contra hne
    exact hdisjk i j i.2 j.2 (fun h => hne (Fin.ext h)) hij
  obtain ⟨hle, hρe⟩ := P2Core.siblingPlace_gesKConj_iff K n (fun i : Fin n => (f i).1) hQsplitK
    hQdisj ⟨l, hl⟩ ⟨l', hl'⟩ ρ ρ'
    (Work.SSGRoute.H9.swGesKConj_trans h (Work.SSGRoute.H9.swGesKConj_symm h'))
  exact ⟨by simpa using congrArg Fin.val hle, hρe⟩

/-! ## The step -/

theorem PreTwo_step {Λ : IntermediateField k Ω} [FiniteDimensional k Λ] [IsGalois k Λ]
    (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (2 : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (O : Oracle (K := K) Λ ζ hζ hζK)
    {n : ℕ} {s : St (k := k) (Ω := Ω) (K := K)}
    (hs : PreTwo (K := K) Λ ζ hζ hζK S y n s) :
    ∃ s' : St (k := k) (Ω := Ω) (K := K), (∀ m < n, s'.f m = s.f m) ∧
      PreTwo (K := K) Λ ζ hζ hζK S y (n + 1) s' := by
  classical
  obtain ⟨hfin, hsplit, hdisjK, hdisjk, hexcl, hreal, hinv, hconf, hnorm⟩ := hs
  set T : Finset (ValuationSubring Ω) := TBlock S s.f n with hTdef
  -- ## the `K`- and `k`-level structure of the escape primes
  have hsplitK : ∀ l : ℕ, l < n → SSGRoute.IsSplitIn k K (s.f l).1 :=
    fun l hl => Work.SSGRoute.NodeS35.isSplitIn_of_le (K := K) (N := Λ) hKΛ (hsplit l hl)
  have hdisjkK : ∀ l l' : ℕ, l < n → l' < n → l ≠ l' →
      ¬ SSGRoute.IsConjPlace k (s.f l).1 (s.f l').1 := by
    intro l l' hl hl' hne hc
    rcases lt_or_gt_of_ne hne with h | h
    · exact hdisjk l l' h hl' hc
    · exact hdisjk l' l h hl (SSGRoute.isConjPlace_symm hc)
  have hattach_unique : ∀ {A : ValuationSubring Ω} {l : ℕ} {ρ : K ≃ₐ[k] K}, l < n →
      Work.SSGRoute.gesKConj K (Work.SSGRoute.ZDataMup.siblingPlace K ρ (s.f l).1) A →
      ∀ l' : ℕ, l' < n → ∀ ρ' : K ≃ₐ[k] K,
        Work.SSGRoute.gesKConj K (Work.SSGRoute.ZDataMup.siblingPlace K ρ' (s.f l').1) A →
        l' = l ∧ ρ' = ρ :=
    fun {_ _ _} hl h l' hl' ρ' h' => by
      obtain ⟨h1, h2⟩ := siblingPlace_attach_unique (K := K) hsplitK hdisjkK hl hl' h h'
      exact ⟨h1.symm, h2.symm⟩
  -- ## the oracle hypotheses
  have hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A :=
    TBlock_isFinPlace (K := K) hSfin (fun j hj => hfin j hj)
  have hTdisj : ∀ A ∈ T, ∀ B ∈ T, Work.SSGRoute.gesKConj K A B → A = B := by
    intro A hA B hB h
    rw [hTdef] at hA hB
    exact TBlock_disj (K := K) A hA B hB h
  have hTcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (2 : Ω) < 1 ∨
        ∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ Λ.fixingSubgroup) →
      ∃ A ∈ T, Work.SSGRoute.gesKConj K A B := by
    intro B hB hcond
    have hram : SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (2 : Ω) < 1 := by
      rcases hcond with h | ⟨σ, -, hσI, hσΛ⟩
      · exact Or.inr h
      · exact Or.inl ⟨σ, hσI, hσΛ⟩
    obtain ⟨A₀, hA₀, hA₀B⟩ := hSram B hB hram
    obtain ⟨A', hA', hA'B⟩ := TBlock_covers_S (K := K) (S := S) (f := s.f) (m := n) hA₀ hA₀B
    exact ⟨A', by rw [hTdef]; exact hA', hA'B⟩
  -- the S-attachment dichotomy for a block of `T`
  have hcase : ∀ A ∈ T, (∃ A₀ ∈ S, SSGRoute.IsConjPlace k A₀ A) ∨
      (∃ l : ℕ, l < n ∧ ∃ ρ : K ≃ₐ[k] K,
        Work.SSGRoute.gesKConj K (Work.SSGRoute.ZDataMup.siblingPlace K ρ (s.f l).1) A) := by
    intro A hA
    rw [hTdef] at hA
    rcases TBlock_mem_cases (K := K) hA with ⟨A₀, hA₀, ρ, hconj⟩ | ⟨l, hl, ρ, hconj⟩
    · refine Or.inl ⟨A₀, hA₀, ?_⟩
      obtain ⟨τ, -, hτ⟩ := hconj
      exact ⟨τ * Work.SSGRoute.ZDataMup.galLift K ρ, by rw [mul_smul]; exact hτ⟩
    · exact Or.inr ⟨l, hl, ρ, hconj⟩
  have hgram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0 := by
    intro B hB hBT hns σ hσK hσI
    refine hyS B hB ?_ hns σ hσK hσI
    intro A₀ hA₀ hconj
    obtain ⟨A', hA', hA'B⟩ := TBlock_covers_S (K := K) (S := S) (f := s.f) (m := n) hA₀ hconj
    exact hBT A' (by rw [hTdef]; exact hA') hA'B
  have hh : ∀ A ∈ T, ∀ x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      ∀ z ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
        prescDatum (K := K) ζ hζ hζK S y s.f n A (x * z)
          = prescDatum (K := K) ζ hζ hζK S y s.f n A x
            + prescDatum (K := K) ζ hζ hζK S y s.f n A z :=
    fun A _ => prescDatum_add (K := K) hy n A
  have hhc : ∀ A ∈ T, ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ x ∈ U, x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup →
        prescDatum (K := K) ζ hζ hζK S y s.f n A x = 0 :=
    fun A _ => prescDatum_locConst (K := K) hy (hyc := hyc) n A
  have horth : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
        prescDatum (K := K) ζ hζ hζK S y s.f n A σ = 0) ∨
      SSGRoute.IsSplitIn k Λ A := by
    intro A hA
    rcases hcase A hA with hSatt | ⟨l, hl, ρ, hconj⟩
    · exact Or.inl (fun σ _ => by rw [prescDatum_eq_zero_of_isConjPlace (K := K) hSatt])
    · refine Or.inr ?_
      obtain ⟨τ, -, hτA⟩ := hconj
      rw [← hτA]
      exact (SSGRoute.isSplitIn_conj Λ (P2Core.fixingSubgroup_normal Λ)
        (Work.SSGRoute.ZDataMup.siblingPlace K ρ (s.f l).1) τ).mpr
        (P2Core.siblingPlace_isSplitIn K Λ ρ (s.f l).1 (hsplit l hl))
  have hinertia : ∀ A ∈ T, ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ →
      y σ + prescDatum (K := K) ζ hζ hζK S y s.f n A σ = 0 := by
    intro A hA σ hσK hσI
    by_cases hSatt : ∃ A₀ ∈ S, SSGRoute.IsConjPlace k A₀ A
    · rw [prescDatum_eq_zero_of_isConjPlace (K := K) hSatt, add_zero]
      exact hyT A (hTfin A hA) hSatt σ hσK hσI
    · rcases hcase A hA with hS' | ⟨l, hl, ρ, hconj⟩
      · exact absurd hS' hSatt
      · have huniqA := hattach_unique hl hconj
        rw [prescDatum_apply_eq_of_attachment (K := K) (hS := hSatt) hl hconj huniqA]
        rw [show y σ + (- y σ + eScalar (K := K) ζ hζ hζK s.f l n ρ •
              Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f l).2 σ)
            = eScalar (K := K) ζ hζ hζK s.f l n ρ •
              Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f l).2 σ
          from by ring]
        by_cases hρ : ρ = 1
        · rw [eScalar, dif_pos hρ, zero_smul]
        · rw [eScalar, dif_neg hρ]
          have hχ0 : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f l).2 σ = 0 := by
            refine hconf l hl A (hTfin A hA) ?_ ?_ σ hσK hσI
            · intro A' hA' hA'A
              have hA'n : A' ∈ TBlock S s.f n := TBlock_mono (K := K) (le_of_lt hl) hA'
              have hAA' : A' = A :=
                TBlock_disj (K := K) (S := S) (f := s.f) (m := n) A' hA'n A
                  (by rw [hTdef] at hA; exact hA) hA'A
              rw [hAA'] at hA'
              rcases TBlock_mem_cases_k (K := K) hA' with hS'' | ⟨j, hj, hjconj⟩
              · exact hSatt hS''
              · refine hdisjkK j l (lt_trans hj hl) hl (by omega) ?_
                obtain ⟨τ, -, hτ⟩ := hconj
                exact SSGRoute.isConjPlace_trans hjconj
                  (SSGRoute.isConjPlace_symm
                    ⟨τ * Work.SSGRoute.ZDataMup.galLift K ρ, by rw [mul_smul]; exact hτ⟩)
            · intro hQlA
              exact Work.SSGRoute.ZDataMup.siblingPlace_not_gesKConj K hρ (hsplitK l hl)
                (Work.SSGRoute.H9.swGesKConj_trans hQlA
                  (Work.SSGRoute.H9.swGesKConj_symm hconj))
          rw [hχ0, smul_zero]
  have hhhinf : ∀ A ∈ T, ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 →
      prescDatum (K := K) ζ hζ hζK S y s.f n A c = 0 := by
    intro A hA c hc hc2
    by_cases hSatt : ∃ A₀ ∈ S, SSGRoute.IsConjPlace k A₀ A
    · rw [prescDatum_eq_zero_of_isConjPlace (K := K) hSatt]
    · rcases hcase A hA with hS' | ⟨l, hl, ρ, hconj⟩
      · exact absurd hS' hSatt
      · have huniqA := hattach_unique hl hconj
        rw [prescDatum_apply_eq_of_attachment (K := K) (hS := hSatt) hl hconj huniqA]
        rw [hyinf c hc hc2, hinv l hl c hc hc2, neg_zero, smul_zero, add_zero]
  -- ## the oracle
  obtain ⟨b, Q, hQfin, hQsplit, hQnotT, hQnotTk, hrealQ, hinvQ, hconfQ, hnormQ⟩ :=
    O T hTfin hTdisj hTcov y hy hyc hgram (prescDatum (K := K) ζ hζ hζK S y s.f n)
      hh hhc horth hinertia hyinf hhhinf
  -- ## the new history
  set f' : ℕ → (ValuationSubring Ω × (↥K)ˣ) := Function.update s.f n (Q, b) with hf'def
  have hfn : f' n = (Q, b) := by rw [hf'def, Function.update_apply, if_pos rfl]
  have hfm : ∀ m < n, f' m = s.f m := by
    intro m hm
    rw [hf'def, Function.update_of_ne (by omega : m ≠ n)]
  have hTcongr : ∀ m ≤ n, TBlock S f' m = TBlock S s.f m :=
    fun m hm => TBlock_congr (K := K) (fun i hi => hfm i (lt_of_lt_of_le hi hm))
  have hPcongr : ∀ m ≤ n, prescDatum (K := K) ζ hζ hζK S y f' m
      = prescDatum (K := K) ζ hζ hζK S y s.f m :=
    fun m hm => prescDatum_congr (K := K) (fun i hi => hfm i (lt_of_lt_of_le hi hm))
  have c1 : ∀ m < n + 1, SSGRoute.IsSplitIn k Λ (f' m).1 := by
    intro m hm
    rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm' | hm''
    · rw [hfm m hm']; exact hsplit m hm'
    · rw [hm'', hfn]; exact hQsplit
  have c2 : ∀ m l : ℕ, m < l → l < n + 1 →
      ¬ Work.SSGRoute.gesKConj K (f' m).1 (f' l).1 := by
    intro m l hml hl
    rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl' | hl''
    · rw [hfm m (lt_trans hml hl'), hfm l hl']; exact hdisjK m l hml hl'
    · rw [hl''] at hml ⊢
      rw [hfm m hml, hfn]
      intro hconj
      obtain ⟨A, hA, hAQ⟩ := TBlock_covers_Q (K := K) (S := S) (f := s.f) (m := n) hml
        (⟨1, one_smul _ _⟩ : SSGRoute.IsConjPlace k (s.f m).1 (s.f m).1)
      exact hQnotT A (by rw [hTdef]; exact hA) (Work.SSGRoute.H9.swGesKConj_trans hAQ hconj)
  have c3 : ∀ m l : ℕ, m < l → l < n + 1 →
      ¬ SSGRoute.IsConjPlace k (f' m).1 (f' l).1 := by
    intro m l hml hl
    rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl' | hl''
    · rw [hfm m (lt_trans hml hl'), hfm l hl']; exact hdisjk m l hml hl'
    · rw [hl''] at hml ⊢
      rw [hfm m hml, hfn]
      intro hconj
      obtain ⟨A, hA, hAQ⟩ := TBlock_covers_Q (K := K) (S := S) (f := s.f) (m := n) hml
        (⟨1, one_smul _ _⟩ : SSGRoute.IsConjPlace k (s.f m).1 (s.f m).1)
      exact hQnotTk A (by rw [hTdef]; exact hA)
        (SSGRoute.isConjPlace_trans (by
          obtain ⟨τ, -, hτ⟩ := hAQ
          exact ⟨τ, hτ⟩) hconj)
  have c4 : ∀ m < n + 1, ∀ A ∈ TBlock S f' m, ¬ Work.SSGRoute.gesKConj K A (f' m).1 := by
    intro m hm A hA
    rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm' | hm''
    · rw [hTcongr m (le_of_lt hm')] at hA
      rw [hfm m hm']
      exact hexcl m hm' A hA
    · rw [hm''] at hA ⊢
      rw [hTcongr n le_rfl] at hA
      rw [hfn]
      exact hQnotT A (by rw [hTdef]; exact hA)
  have c5 : ∀ m < n + 1, ∀ A ∈ TBlock S f' m,
      ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (f' m).2 σ
          = y σ + prescDatum (K := K) ζ hζ hζK S y f' m A σ := by
    intro m hm A hA σ hσ
    rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm' | hm''
    · rw [hTcongr m (le_of_lt hm')] at hA
      rw [hfm m hm', hPcongr m (le_of_lt hm')]
      exact hreal m hm' A hA σ hσ
    · rw [hm''] at hA ⊢
      rw [hTcongr n le_rfl] at hA
      rw [hfn, hPcongr n le_rfl]
      exact hrealQ A (by rw [hTdef]; exact hA) σ hσ
  have c6 : ∀ m < n + 1, ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (f' m).2 c = 0 := by
    intro m hm c hc hc2
    rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm' | hm''
    · rw [hfm m hm']; exact hinv m hm' c hc hc2
    · rw [hm'', hfn]; exact hinvQ c hc hc2
  have c7 : ∀ m < n + 1, ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ TBlock S f' m, ¬ Work.SSGRoute.gesKConj K A B) →
      (¬ Work.SSGRoute.gesKConj K (f' m).1 B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (f' m).2 σ = 0 := by
    intro m hm B hB hBT hQB σ hσK hσI
    rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm' | hm''
    · rw [hfm m hm']
      rw [hfm m hm'] at hQB
      refine hconf m hm' B hB ?_ hQB σ hσK hσI
      intro A hA hc
      exact hBT A (by rw [hTcongr m (le_of_lt hm')]; exact hA) hc
    · rw [hm''] at hQB hBT ⊢
      rw [hfn] at hQB ⊢
      refine hconfQ B hB ?_ hQB σ hσK hσI
      intro A hA hc
      rw [hTdef] at hA
      rw [← hTcongr n le_rfl] at hA
      exact hBT A hA hc
  have c8 : ∀ m < n + 1, ∃ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K,
      ((f' m).1).comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔮 ∧
      Odd (FractionalIdeal.count ↥K 𝔮
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          ((f' m).2 : ↥K))) := by
    intro m hm
    rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm' | hm''
    · rw [hfm m hm']; exact hnorm m hm'
    · rw [hm'', hfn]; exact hnormQ
  have c0 : ∀ m < n + 1, SSGRoute.IsFinPlace k (f' m).1 := by
    intro m hm
    rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm' | hm''
    · rw [hfm m hm']; exact hfin m hm'
    · rw [hm'', hfn]; exact hQfin
  exact ⟨⟨f'⟩, fun m hm => hfm m hm, c0, c1, c2, c3, c4, c5, c6, c7, c8⟩

end Work.SSGRoute.ZDataTwo.TwoRec
