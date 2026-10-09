import Mathlib
import Submission.Work.SSGRoute.P2Close.Defs
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.defs
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.inv
import Submission.Work.SSGRoute.NodeS37.tblockBasics
import Submission.Work.SSGRoute.ZDataTwo.confinement_on_conj_blocks
import Submission.Work.SSGRoute.ZDataMup.swCoreDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.P2Close

open scoped Pointwise

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  [IsAlgClosed Ω]

/-- The two `p = 2` encodings of the level-`K` Kummer cochain agree on `K.fixingSubgroup`:
`ZSplit.nodeKummerCocharZMod` (the `kummerCharZMod`-based cochain of the escape steps) and
`Work.SSGRoute.nodeKummerCochar` (the `kummerChar`-based cochain of the §4 assembly) are both the
Kummer index of `b` at a chosen square root of `b`, and the Kummer index is independent of that
choice (`Work.SSGRoute.kummerIdx_congr`). -/
lemma nodeKummerCocharZMod_eq_nodeKummerCochar_apply {K : IntermediateField k Ω} {ζ : Ω}
    {hζK : ζ ∈ K} {hζ : IsPrimitiveRoot ζ 2} {b : (↥K)ˣ} {σ : Ω ≃ₐ[k] Ω}
    (hσ : σ ∈ K.fixingSubgroup) :
    Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ =
      Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b σ := by
  rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK)
      (hζ := hζ) (β := b) hσ,
    Work.SSGRoute.nodeKummerCochar, Work.SSGRoute.kummerCochar_apply K _ _ b hσ,
    Work.SSGRoute.kummerChar_apply, Work.SSGRoute.kummerCharZMod_apply]
  exact (Work.SSGRoute.kummerIdx_congr 2 _ b (Work.SSGRoute.kummerSqrt_pow b)
    (Work.SSGRoute.kummerSqrtUnitZMod_pow 2 b) _).symm

/-- **Clause (d) at the `S`-places: the stage-`m` class agrees with `y` on the local group of every
finite place `B` that is `k`-conjugate to a place of `S`.**

`y` enters `PreTwo` only through the prescription at the `S`-attached blocks of the place set, and
there `prescDatum = 0`: so the realisation clause of `PreTwo` at the `S`-blocks of
`TBlock S s.f 0` (which are also blocks of `TBlock S s.f m`, by `TBlock_mono`) reads
`χ_{b_m} = y` on the local groups `decomp k A ⊓ G_K`.  `ZDataMup.clause_one_of_covering`
transports that agreement from the representatives of the `K`-classes above `S` to every
`k`-conjugate, using the conjugacy invariance of `χ_{b_m}` and of `y` (the latter is exactly the
content of the hypothesis `hy`). -/
theorem preTwo_agreement {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K Λ : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K] [IsSepClosure ↥K Ω] [FiniteDimensional k Λ] [IsGalois k Λ]
    (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (2 : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (s : Work.SSGRoute.ZDataTwo.TwoRec.St (k := k) (Ω := Ω) (K := K))
    (hs : ∀ n, Work.SSGRoute.P2Close.PreTwoC (K := K) Λ ζ hζ hζK S y n s) (m : ℕ) :
    ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
        Work.SSGRoute.nodeKummerCochar K ζ hζK hζ (s.f m).2 σ = y σ := by
  classical
  -- the prefix invariant at stage `m + 1`, whose realisation clause concerns the index `m`
  have hP : Work.SSGRoute.ZDataTwo.TwoRec.PreTwo (K := K) Λ ζ hζ hζK S y (m + 1) s :=
    (hs (m + 1)).1
  obtain ⟨-, -, -, -, -, hreal, -, -, -⟩ := hP
  -- agreement at the `S`-attached blocks: there the prescribed datum vanishes
  have hT : ∀ A ∈ Work.SSGRoute.ZDataTwo.TwoRec.TBlock S s.f 0,
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k A →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 σ = y σ := by
    intro A hA σ hσK hσA
    -- every block of `TBlock S s.f 0` is `k`-conjugate to a place of `S`
    have hwit : ∃ A₀ ∈ S, SSGRoute.IsConjPlace k A₀ A := by
      rcases Work.SSGRoute.ZDataTwo.TwoRec.TBlock_mem_cases (K := K) (S := S) (f := s.f)
          (m := 0) hA with ⟨A₀, hA₀, ρ, hconj⟩ | ⟨l, hl, ρ, hconj⟩
      · exact ⟨A₀, hA₀, Work.SSGRoute.isConjPlace_trans
          (Work.SSGRoute.isConjPlace_symm
            (Work.SSGRoute.NodeS37.siblingPlace_isConjPlace ρ A₀))
          (Work.SSGRoute.NodeS37.gesKConj_isConjPlace hconj)⟩
      · exact absurd hl (Nat.not_lt_zero l)
    -- and it is a block of `TBlock S s.f m` as well
    have hA' : A ∈ Work.SSGRoute.ZDataTwo.TwoRec.TBlock S s.f m :=
      Work.SSGRoute.ZDataTwo.TwoRec.TBlock_mono (K := K) (S := S) (f := s.f)
        (Nat.zero_le m) hA
    rw [hreal m (Nat.lt_succ_self m) A hA' σ (Subgroup.mem_inf.mpr ⟨hσA, hσK⟩),
      congrFun (Work.SSGRoute.ZDataTwo.TwoRec.prescDatum_eq_zero_of_isConjPlace
        (K := K) (ζ := ζ) (hζ := hζ) (hζK := hζK) (S := S) (y := y) (f := s.f)
        (m := m) hwit) σ]
    simp
  intro B hB hBS σ hσ
  have hσK : σ ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hσ).2
  have hσB : σ ∈ SSGRoute.decomp k B := (Subgroup.mem_inf.mp hσ).1
  -- the `S`-attached blocks of `TBlock S s.f 0` cover every `k`-conjugate of a place of `S`
  have hcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∃ A ∈ Work.SSGRoute.ZDataTwo.TwoRec.TBlock S s.f 0,
        ∃ τ ∈ K.fixingSubgroup, τ • A = B := by
    rintro B _ ⟨A₀, hA₀, hconj⟩
    obtain ⟨A', hA', τ, hτ, hτA⟩ :=
      Work.SSGRoute.ZDataTwo.TwoRec.TBlock_covers_S (K := K) (S := S) (f := s.f) (m := 0)
        hA₀ hconj
    exact ⟨A', hA', τ, hτ, hτA⟩
  have hmain := Work.SSGRoute.ZDataMup.clause_one_of_covering (p := 2) K ζ hζ hζK (s.f m).2 y
    hy S (Work.SSGRoute.ZDataTwo.TwoRec.TBlock S s.f 0) hcov hT B hB hBS σ hσK hσB
  rw [← nodeKummerCocharZMod_eq_nodeKummerCochar_apply (K := K) (ζ := ζ) (hζK := hζK)
    (hζ := hζ) (b := (s.f m).2) hσK]
  exact hmain

end Work.SSGRoute.P2Close
