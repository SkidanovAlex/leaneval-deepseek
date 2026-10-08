import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.rem31Shape
import Submission.Work.BG.thm32
import Submission.Work.BG.bset_orbit_struct
import Submission.Work.BG.lemma24
import Submission.Work.BG.CharBridge
import Submission.Work.BG.HatInjDefs
import Submission.Work.BG.l34ne_restrict_shape
import Submission.Work.BG.chiDegDegreeIdentity
import Submission.Work.BG.chiDegDiffInvariant
import Submission.Work.BG.chiDegOrbitCardMulDegree
import Submission.Work.BG.chiDegOrbitConstantSum
import Submission.Work.BG.chiDegEsum

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

variable {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]

/-! ## Small standing-configuration facts

`𝒮(χ) = bset C f χ` is `s`-stable, the standard disjunction forces `D.n = 4`, and in the
standing configuration `𝒮(χ)` has exactly the three members `ν, ν^s, ξ`.
(These are self-contained copies of the corresponding facts in
`Submission/Work/BG/l34ExcNeFourAux.lean`, kept here so that this file depends only on
already-frozen modules.) -/

theorem chiDegSconjMemBset (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) {η : ClassFunction ↥C.P.H0 ℂ} (hη : η ∈ bset C f χ) :
    sconj C η ∈ bset C f χ := by
  refine ⟨IsIrreducibleCharacter.conjByH C.P C.s hη.1, ?_⟩
  have hk : η ∈ orbitKey C η := Or.inl (s02c_LamEquiv_refl C η)
  have hfix : f (sconj C η) = f η := ((hf.1 η hη.1) η hk η hk hη.1 hη.1).2.1
  rw [hfix]
  exact hη.2

theorem chiDegNEqFour (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    {ν : ClassFunction ↥C.P.H0 ℂ}
    (hdisj : sconj C ν ∉ lamOrbit C ν ∨ (lamOrbit C ν).ncard = D.n)
    (hinv : sconj C '' lamOrbit C ν = lamOrbit C ν) (h4 : (lamOrbit C ν).ncard = 4) :
    D.n = 4 := by
  have hm : ν ∈ lamOrbit C ν := mem_lamOrbit_self C ν
  have hs : sconj C ν ∈ sconj C '' lamOrbit C ν := ⟨ν, hm, rfl⟩
  rw [hinv] at hs
  rcases hdisj with h | h
  · exact absurd hs h
  · rw [h4] at h
    exact h.symm

theorem chiDegBsetEq (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hDC : Compat D C) (hS3 : Sec3Hyp D)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ)
    {ν ξ : ClassFunction ↥C.P.H0 ℂ} (hν : ν ∈ bset C f χ) (hne : sconj C ν ≠ ν)
    (hξ : ξ ∈ bset C f χ) (hξν : ξ ≠ ν) (hξνs : ξ ≠ sconj C ν) :
    bset C f χ = {ν, sconj C ν, ξ} := by
  haveI : Fintype (IrreducibleCharacter ↥C.P.H0) := Fintype.ofFinite (IrreducibleCharacter ↥C.P.H0)
  have h2 : sconj C ν ∈ bset C f χ := chiDegSconjMemBset C f hf χ hν
  have hsub : ({ν, sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ)) ⊆ bset C f χ := by
    intro η hη
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hη
    rcases hη with rfl | rfl | rfl
    · exact hν
    · exact h2
    · exact hξ
  have h1 : ν ∉ ({sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => hne h.symm, fun h => hξν h.symm⟩
  have h2' : sconj C ν ∉ ({ξ} : Set (ClassFunction ↥C.P.H0 ℂ)) := by
    simp only [Set.mem_singleton_iff]
    exact fun h => hξνs h.symm
  have hcard : ({ν, sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ)).ncard = 3 := by
    rw [show ({ν, sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ))
        = insert ν (insert (sconj C ν) ({ξ} : Set (ClassFunction ↥C.P.H0 ℂ))) from rfl,
      Set.ncard_insert_of_notMem h1 (Set.toFinite _),
      Set.ncard_insert_of_notMem h2' (Set.toFinite _), Set.ncard_singleton]
  have hle : (bset C f χ).ncard ≤ 3 := thm32 D C hDC hS3 f hf χ hχ
  have hfin : (bset C f χ).Finite := s02_bset_finite C f χ
  have hb : (bset C f χ).ncard ≤ ({ν, sconj C ν, ξ} : Set (ClassFunction ↥C.P.H0 ℂ)).ncard := by
    rw [hcard]; exact hle
  exact (Set.eq_of_subset_of_ncard_le hsub hb hfin).symm

/-- The degree of an irreducible character of an odd-order group is odd. -/
theorem chiDegOddDegree {K : Type} [Group K] [Finite K] [Fintype K] {φ : ClassFunction K ℂ}
    (hK : Odd (Nat.card K)) (hφ : IsIrreducibleCharacter φ) :
    ∃ m : ℤ, φ 1 = (m : ℂ) ∧ Odd m := by
  obtain ⟨n, _, hval, hdvd⟩ := hφ.exists_natDegree_charValue_one_dvd_card
  have hodd : Odd n := Odd.of_dvd_nat hK hdvd
  obtain ⟨t, ht⟩ := hodd
  exact ⟨(n : ℤ), by rw [hval]; norm_num, ⟨(t : ℤ), by push_cast [ht]; ring⟩⟩

/-- Frobenius reciprocity in the orientation used below: `(χ, θ^G) = (χ|_{H₀}, θ)`. -/
theorem chiDegInnerIndEqRestrict (C : Sec2Ctx G) [Fintype ↥C.P.H0]
    [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (χ : ClassFunction G ℂ) (θ : ClassFunction ↥C.P.H0 ℂ) :
    ClassFunction.inner χ (ClassFunction.induce C.P.H0 θ) =
      ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) θ := by
  calc ClassFunction.inner χ (ClassFunction.induce C.P.H0 θ)
      = star (ClassFunction.inner (ClassFunction.induce C.P.H0 θ) χ) :=
        ClassFunction.inner_star_comm _ _
    _ = star (ClassFunction.inner θ (ClassFunction.restrict C.P.H0 χ)) := by
        rw [ClassFunction.inner_induce_eq_inner_restrict C.P.H0 θ χ]
    _ = star (star (ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) θ)) := by
        rw [ClassFunction.inner_star_comm]
    _ = ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) θ := star_star _

/-- The multiplicity `(χ, θ^G)` is an integer (`χ ∈ ℤ[Irr G]`). -/
theorem chiDegMInt (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ) (θ : IrreducibleCharacter ↥C.P.H0) :
    ∃ m : ℤ,
      ClassFunction.inner χ (ClassFunction.induce C.P.H0 (θ : ClassFunction ↥C.P.H0 ℂ)) =
        (m : ℂ) := by
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite ↥C.P.H0
  have hχZ : χ ∈ ZIrr G := mem_ZIrr_of_isPmIrr hχ
  have hres : ClassFunction.restrict C.P.H0 χ ∈ ZIrr ↥C.P.H0 :=
    ClassFunction.restrict_mem_ZIrr C.P.H0 hχZ
  obtain ⟨m, hm⟩ := mem_ZIrr_inner_int θ hres
  refine ⟨m, ?_⟩
  rw [chiDegInnerIndEqRestrict]
  exact hm

/-- The coherent coefficient `(χ, f θ)` is an integer (it is `0` off `𝒮(χ)` and `±1` on it). -/
theorem chiDegEInt (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsPmIrr χ) (θ : IrreducibleCharacter ↥C.P.H0) :
    ∃ m : ℤ,
      ClassFunction.inner χ (f (θ : ClassFunction ↥C.P.H0 ℂ)) = (m : ℂ) := by
  by_cases hmem : (θ : ClassFunction ↥C.P.H0 ℂ) ∈ bset C f χ
  · have hpm : ClassFunction.inner χ (f (θ : ClassFunction ↥C.P.H0 ℂ)) = 1 ∨
        ClassFunction.inner χ (f (θ : ClassFunction ↥C.P.H0 ℂ)) = -1 :=
      ((bset_orbit_struct C f hf χ hχ).1 (θ : ClassFunction ↥C.P.H0 ℂ) hmem).2.2
    rcases hpm with h | h
    · exact ⟨1, by rw [h]; norm_num⟩
    · exact ⟨-1, by rw [h]; norm_num⟩
  · have h0 : ClassFunction.inner χ (f (θ : ClassFunction ↥C.P.H0 ℂ)) = 0 := by
      by_contra hne
      exact hmem ⟨θ.2, hne⟩
    exact ⟨0, by rw [h0]; norm_num⟩

/-! ## The degree congruence `4 ∣ χ(1)` -/

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem chi_deg_mod_four {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C16.Compat D C → Work.GW2.C16.Sec3Hyp D →
    ∀ f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ, Work.GW2.C16.IsCoherent C f →
    ∀ χ : ClassFunction G ℂ, Work.BG.IsPmIrr χ →
    ∀ ν ∈ Work.GW2.C16.bset C f χ, Work.BG.sconj C ν ≠ ν →
      (Work.BG.sconj C ν ∉ Work.BG.lamOrbit C ν ∨ (Work.BG.lamOrbit C ν).ncard = D.n) →
      (Work.BG.lamOrbit C ν).ncard = 4 →
      Work.BG.sconj C '' Work.BG.lamOrbit C ν = Work.BG.lamOrbit C ν →
      ∀ ξ ∈ Work.GW2.C16.bset C f χ, ξ ≠ ν → ξ ≠ Work.BG.sconj C ν →
      Work.BG.sconj C ξ = ξ → (Work.BG.lamOrbit C ξ).ncard ≠ 4 →
      ∃ k : ℤ, χ 1 = (4 : ℂ) * (k : ℂ) := by
  intro hDC hS3 f hf χ hχ ν hν hne hdisj h4 hinv ξ hξ hξν hξνs hξs hξ4
  classical
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite ↥C.P.H0
  haveI : Fintype (IrreducibleCharacter ↥C.P.H0) := Fintype.ofFinite (IrreducibleCharacter ↥C.P.H0)
  haveI : Fintype ↥(C.P.U) := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥(C.P.U) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- ## the standing configuration
  have hD4 : D.n = 4 := chiDegNEqFour D C hdisj hinv h4
  have hbset : bset C f χ = {ν, sconj C ν, ξ} :=
    chiDegBsetEq D C hDC hS3 f hf χ hχ hν hne hξ hξν hξνs
  obtain ⟨⟨β, hβirr, hνβ, hsνβ⟩, ⟨α₁, α₂, hα₁irr, hα₂irr, hαne, hα1eq, hξα⟩, hcardξ⟩ :=
    l34ne_restrict_shape D C hDC hS3 f hf χ hχ ν hν hne hdisj h4 hinv hD4 ξ hξ hξν hξνs
      hξs hξ4
  have hUodd : Odd (Nat.card ↥(C.P.U)) := odd_card_U_of_compat hDC
  have hβodd : ∃ m : ℤ, β 1 = (m : ℂ) ∧ Odd m := chiDegOddDegree hUodd hβirr
  have hαodd : ∃ m : ℤ, α₁ 1 = (m : ℂ) ∧ Odd m := chiDegOddDegree hUodd hα₁irr
  -- ## the three summand functions
  set M : IrreducibleCharacter ↥C.P.H0 → ℂ :=
    fun θ => ClassFunction.inner χ (ClassFunction.induce C.P.H0 (θ : ClassFunction ↥C.P.H0 ℂ))
    with hM
  set E : IrreducibleCharacter ↥C.P.H0 → ℂ :=
    fun θ => ClassFunction.inner χ (f (θ : ClassFunction ↥C.P.H0 ℂ)) with hE
  set Df : IrreducibleCharacter ↥C.P.H0 → ℂ := fun θ => M θ - E θ with hDf
  -- **(A)** the Fourier degree identity `χ(1) = Σ_θ (χ, θ^G) θ(1)`
  have hA : (∑ θ : IrreducibleCharacter ↥C.P.H0,
      M θ * ((θ : ClassFunction ↥C.P.H0 ℂ) 1)) = χ 1 := by
    rw [hM]
    exact chiDegDegreeIdentity C χ
  -- **(E)** the coherent part `Σ_θ (χ, f θ) θ(1) ∈ 4ℤ`
  have hEsum : ∃ k : ℤ, (∑ θ : IrreducibleCharacter ↥C.P.H0,
      E θ * ((θ : ClassFunction ↥C.P.H0 ℂ) 1)) = 4 * (k : ℂ) := by
    rw [hE]
    exact chiDegEsum C f hf χ hχ hν hξ hne hξν hξνs hbset hνβ hsνβ hξα hα1eq hβodd hαodd
  -- **(B)** `Df` is constant on `Λ`-orbits
  have hDinv : ∀ μ ν : IrreducibleCharacter ↥C.P.H0,
      LamEquiv C (μ : ClassFunction ↥C.P.H0 ℂ) (ν : ClassFunction ↥C.P.H0 ℂ) →
      Df μ = Df ν := by
    intro μ ν hLam
    have h := chiDegDiffInvariant C f hf χ μ ν hLam
    rw [hDf]
    simp only [hM, hE]
    linear_combination h
  -- **(C)** `Df` is integer-valued
  have hDint : ∀ θ : IrreducibleCharacter ↥C.P.H0, ∃ m : ℤ, Df θ = (m : ℂ) := by
    intro θ
    obtain ⟨m1, hm1⟩ := chiDegMInt C χ hχ θ
    obtain ⟨m2, hm2⟩ := chiDegEInt C f hf χ hχ θ
    rw [hDf]
    simp only [hM, hE]
    exact ⟨m1 - m2, by rw [hm1, hm2]; push_cast; ring⟩
  -- **(D)** each `Λ`-orbit carries a degree sum divisible by `4`
  have horb : ∀ θ : IrreducibleCharacter ↥C.P.H0,
      ∃ z : ℤ, ((lamOrbit C (θ : ClassFunction ↥C.P.H0 ℂ)).ncard : ℂ) *
        ((θ : ClassFunction ↥C.P.H0 ℂ) 1) = 4 * (z : ℂ) :=
    fun θ => chiDegOrbitCardMulDegree D C hDC hS3 hD4 (θ : ClassFunction ↥C.P.H0 ℂ) θ.2
  -- **(F)** the correction part `Σ_θ Df θ · θ(1) ∈ 4ℤ`
  obtain ⟨k1, hk1⟩ := hEsum
  obtain ⟨k2, hk2⟩ := chiDegOrbitConstantSum C Df hDinv hDint horb
  -- ## assemble
  refine ⟨k1 + k2, ?_⟩
  have hsplit : (∑ θ : IrreducibleCharacter ↥C.P.H0,
        M θ * ((θ : ClassFunction ↥C.P.H0 ℂ) 1))
      = (∑ θ : IrreducibleCharacter ↥C.P.H0, E θ * ((θ : ClassFunction ↥C.P.H0 ℂ) 1))
        + (∑ θ : IrreducibleCharacter ↥C.P.H0, Df θ * ((θ : ClassFunction ↥C.P.H0 ℂ) 1)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun θ _ => ?_
    rw [hDf]
    simp only [hM, hE]
    ring
  rw [← hA, hsplit, hk1, hk2]
  push_cast
  ring

end Work.BG
