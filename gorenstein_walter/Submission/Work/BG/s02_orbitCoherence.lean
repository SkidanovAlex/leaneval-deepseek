import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.s02_vi
import Submission.Work.BG.s02_lemma21Ext
import Submission.Work.BG.s02_assemblyCore
import Submission.Work.BG.s02_twoCase
import Submission.Work.BG.s02_commonConstituent
import Submission.Work.BG.s02_abstractCoherence
import Submission.Work.BG.s02_gram
import Submission.Work.BG.s02_lemma17T
import Submission.Work.BG.s02_lamDual
import Submission.Work.BG.s02_lemma21
import Submission.Work.BG.s02_commonSupportSingleton
import Submission.Work.BG.s02_indDiff
import Submission.Work.BG.s02_lamOrbit_ne
import Submission.Work.BG.s02_quot_data
import Submission.Work.BG.lambda_mul_irreducible
import Submission.Work.BG.centralValue
import Submission.Work.BG.CharBridge
import Submission.Work.BG.Lambda
import Submission.Work.BG.sconjLam
import Submission.Work.BG.remark15Disjoint
import Submission.Work.BG.s02_lemma21_aux
import Submission.Work.BG.s02_noFailThm

namespace Work.BG

open OddOrder.RepresentationTheory
open Classical

variable {G : Type} [Group G] [Finite G]

set_option linter.style.haveILetI false

/-- The `Λ`-orbit of an irreducible character of `H₀` has `2`-power order `≥ 2`
(Bender–Glauberman Lemma 2.1(c)). -/
theorem oc_orbitCard {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (C : Sec2Ctx G) {ν : ClassFunction ↥C.P.H0 ℂ} (hν : IsIrreducibleCharacter ν) :
    ∃ k : ℕ, (lamOrbit C ν).ncard = 2 ^ (k + 1) := by
  classical
  have hcomm : ∀ a b : quotGroup C.P, a * b = b * a := (s02_quot_data C).1
  letI : CommGroup (quotGroup C.P) :=
    { (inferInstance : Group (quotGroup C.P)) with mul_comm := hcomm }
  obtain ⟨n, hn⟩ := (s02_quot_data C).2
  have hcardM : Nat.card (lamDual C) = 2 ^ n := by
    have h : Nat.card (quotGroup C.P →* ℂˣ) = Nat.card (quotGroup C.P) :=
      CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (quotGroup C.P) ℂ
    exact h.trans hn
  have hdvd : (lamOrbit C ν).ncard ∣ 2 ^ n := by
    rw [ncard_lamOrbit_eq_index]
    have h := Subgroup.index_dvd_card (lamStab C ν)
    rwa [hcardM] at h
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hge : 2 ≤ 2 ^ k := by
    obtain ⟨β, hβ⟩ := s02_lamOrbit_ne C ν hν
    have hsub : ({ν, lamCF C β * ν} : Set (ClassFunction ↥C.P.H0 ℂ)) ⊆ lamOrbit C ν := by
      intro x hx
      rcases hx with h | h
      · rw [h]; exact mem_lamOrbit_self C ν
      · rw [h]; exact ⟨β, rfl⟩
    have h2 : ({ν, lamCF C β * ν} : Set (ClassFunction ↥C.P.H0 ℂ)).ncard = 2 :=
      Set.ncard_pair (Ne.symm hβ)
    calc (2 : ℕ) = ({ν, lamCF C β * ν} : Set (ClassFunction ↥C.P.H0 ℂ)).ncard := h2.symm
      _ ≤ (lamOrbit C ν).ncard := Set.ncard_le_ncard hsub (orbit_finite C ν)
      _ = 2 ^ k := hk
  have hk1 : 1 ≤ k := by
    rcases k with _ | k
    · simp at hge
    · exact Nat.succ_le_succ (Nat.zero_le k)
  exact ⟨k - 1, by rw [hk, Nat.sub_add_cancel hk1]⟩

/-- `Λν` has at least two elements. -/
theorem oc_orbitCard_ge_two {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (C : Sec2Ctx G) {ν : ClassFunction ↥C.P.H0 ℂ}
    (hν : IsIrreducibleCharacter ν) : 2 ≤ (lamOrbit C ν).ncard := by
  obtain ⟨k, hk⟩ := oc_orbitCard C hν
  rw [hk]
  calc (2 : ℕ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.succ_le_succ (Nat.zero_le k))

section Transversal
variable (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ)

private def OcRel (x y : {x : ClassFunction ↥C.P.H0 ℂ // x ∈ lamOrbit C ν}) : Prop :=
  y.1 = x.1 ∨ y.1 = sconj C x.1

private theorem OcRel_refl (x : {x : ClassFunction ↥C.P.H0 ℂ // x ∈ lamOrbit C ν}) :
    OcRel C ν x x := Or.inl rfl

private theorem OcRel_symm {x y : {x : ClassFunction ↥C.P.H0 ℂ // x ∈ lamOrbit C ν}}
    (h : OcRel C ν x y) : OcRel C ν y x := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rw [h, sconj_sconj])

private theorem OcRel_trans {x y z : {x : ClassFunction ↥C.P.H0 ℂ // x ∈ lamOrbit C ν}}
    (h1 : OcRel C ν x y) (h2 : OcRel C ν y z) : OcRel C ν x z := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact Or.inl (h2.trans h1)
  · exact Or.inr (by rw [h2, h1])
  · exact Or.inr (by rw [h2, h1])
  · exact Or.inl (by rw [h2, h1, sconj_sconj])

private abbrev OcSetoid : Setoid {x : ClassFunction ↥C.P.H0 ℂ // x ∈ lamOrbit C ν} where
  r := OcRel C ν
  iseqv := ⟨OcRel_refl C ν, fun h => OcRel_symm C ν h, fun h1 h2 => OcRel_trans C ν h1 h2⟩

/-- The set of `s`-classes of the orbit `Λν`. -/
private abbrev OcIdx : Type := Quotient (OcSetoid C ν)

private def OcOfMem (x : {y : ClassFunction ↥C.P.H0 ℂ // y ∈ lamOrbit C ν}) :
    OcIdx C ν := Quotient.mk (OcSetoid C ν) x

private noncomputable def OcRep (q : OcIdx C ν) : ClassFunction ↥C.P.H0 ℂ := (Quotient.out q).1

private theorem OcRep_mem (q : OcIdx C ν) : OcRep C ν q ∈ lamOrbit C ν := (Quotient.out q).2

private noncomputable instance OcIdxFintype : Fintype (OcIdx C ν) := by
  classical
  haveI : Fintype {x : ClassFunction ↥C.P.H0 ℂ // x ∈ lamOrbit C ν} :=
    Set.Finite.fintype (orbit_finite C ν)
  exact Fintype.ofSurjective (fun x => (Quotient.mk (OcSetoid C ν) x : OcIdx C ν))
    (fun q => Quotient.exists_rep q)

private theorem OcRep_spec (x : ClassFunction ↥C.P.H0 ℂ) (hx : x ∈ lamOrbit C ν) :
    ∃! i : OcIdx C ν, x = OcRep C ν i ∨ x = sconj C (OcRep C ν i) := by
  classical
  refine ⟨OcOfMem C ν ⟨x, hx⟩, ?_, ?_⟩
  · exact Quotient.exact (Quotient.out_eq (OcOfMem C ν ⟨x, hx⟩))
  · intro i hi
    have h : (Quotient.mk (OcSetoid C ν) (Quotient.out i) : OcIdx C ν) =
        OcOfMem C ν ⟨x, hx⟩ :=
      Quotient.sound (by
        rcases hi with h | h
        · exact Or.inl h
        · exact Or.inr h)
    rw [← h, Quotient.out_eq i]

/-- The canonical `s`-class index of `x ∈ Λν` satisfies the transversal property. -/
private theorem OcRep_spec_val (x : ClassFunction ↥C.P.H0 ℂ) (hx : x ∈ lamOrbit C ν) :
    x = OcRep C ν (OcOfMem C ν ⟨x, hx⟩) ∨ x = sconj C (OcRep C ν (OcOfMem C ν ⟨x, hx⟩)) :=
  Quotient.exact (Quotient.out_eq (OcOfMem C ν ⟨x, hx⟩))

private theorem OcIdx_unique {i k : OcIdx C ν}
    (h : OcRep C ν i = OcRep C ν k ∨ OcRep C ν i = sconj C (OcRep C ν k)) : i = k := by
  obtain ⟨j, _, huniq⟩ := OcRep_spec C ν (OcRep C ν i) (OcRep_mem C ν i)
  exact (huniq i (Or.inl rfl)).trans (huniq k h).symm

private theorem OcMk_OcRep (i : OcIdx C ν) :
    Quotient.mk (OcSetoid C ν)
      (⟨OcRep C ν i, OcRep_mem C ν i⟩ : {x : ClassFunction ↥C.P.H0 ℂ // x ∈ lamOrbit C ν})
      = i := by
  have h2 : (⟨OcRep C ν i, OcRep_mem C ν i⟩ : {x : ClassFunction ↥C.P.H0 ℂ // x ∈ lamOrbit C ν})
      = Quotient.out i := Subtype.ext rfl
  rw [h2, Quotient.out_eq]

/-- Every element of the key `Λν ∪ (Λν)^s` is `r i` or `r i ^s`, for a unique `i`. -/
private theorem OcIdx_cover (x : ClassFunction ↥C.P.H0 ℂ) (hx : x ∈ orbitKey C ν) :
    ∃! i : OcIdx C ν, x = OcRep C ν i ∨ x = sconj C (OcRep C ν i) := by
  rcases hx with hx | hx
  · exact OcRep_spec C ν x hx
  · obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨j, hj, huniq⟩ := OcRep_spec C ν y hy
    refine ⟨j, ?_, ?_⟩
    · rcases hj with hj | hj
      · exact Or.inr (by rw [hj])
      · exact Or.inl (by rw [hj, sconj_sconj])
    · intro i hi
      have hyi : y = OcRep C ν i ∨ y = sconj C (OcRep C ν i) := by
        rcases hi with h | h
        · refine Or.inr ?_
          calc y = sconj C (sconj C y) := (sconj_sconj C y).symm
            _ = sconj C (OcRep C ν i) := by rw [h]
        · refine Or.inl ?_
          calc y = sconj C (sconj C y) := (sconj_sconj C y).symm
            _ = OcRep C ν i := by
                rw [h]
                exact sconj_sconj C (OcRep C ν i)
      exact huniq i hyi

/-- The non-fixed indices. -/
private abbrev OcNF : Set (OcIdx C ν) := {i | sconj C (OcRep C ν i) ≠ OcRep C ν i}
/-- The fixed indices. -/
private abbrev OcFx : Set (OcIdx C ν) := {i | sconj C (OcRep C ν i) = OcRep C ν i}
/-- Indices `i` whose `s`-class meets `Λν` in two points. -/
private abbrev OcP : Set (OcIdx C ν) :=
  {i | sconj C (OcRep C ν i) ∈ lamOrbit C ν ∧ sconj C (OcRep C ν i) ≠ OcRep C ν i}
/-- The fixed points of `s` on `Λν`. -/
private abbrev OcFixed : Set (ClassFunction ↥C.P.H0 ℂ) :=
  {x | x ∈ lamOrbit C ν ∧ sconj C x = x}
/-- `s` maps `Λν` onto itself. -/
private abbrev OcSInv : Prop := sconj C '' lamOrbit C ν = lamOrbit C ν

private theorem OcFx_eq_compl_NF : OcFx C ν = (OcNF C ν)ᶜ := by
  ext i
  exact ⟨fun hf hn => hn hf, fun hc => by_contra fun hf => hc hf⟩

private theorem OcFx_disj_NF : Disjoint (OcFx C ν) (OcNF C ν) := by
  rw [Set.disjoint_left]
  intro i hf hn
  exact hn hf

private theorem OcFx_union_NF : OcFx C ν ∪ OcNF C ν = Set.univ := by
  rw [OcFx_eq_compl_NF, Set.compl_union_self]

private theorem OcIdx_ncard_split :
    Nat.card (OcIdx C ν) = (OcFx C ν).ncard + (OcNF C ν).ncard := by
  have hfin1 : (OcFx C ν).Finite := Set.finite_univ.subset (Set.subset_univ _)
  have hfin2 : (OcNF C ν).Finite := Set.finite_univ.subset (Set.subset_univ _)
  rw [← Set.ncard_univ (α := OcIdx C ν), ← OcFx_union_NF C ν,
    Set.ncard_union_eq (OcFx_disj_NF C ν) hfin1 hfin2]

private theorem OcRep_mk_of_fixed {x : ClassFunction ↥C.P.H0 ℂ} (hx1 : x ∈ lamOrbit C ν)
    (hx2 : sconj C x = x) :
    OcRep C ν (OcOfMem C ν (⟨x, hx1⟩ : {y : ClassFunction ↥C.P.H0 ℂ // y ∈ lamOrbit C ν})) = x := by
  rcases OcRep_spec_val C ν x hx1 with hj | hj
  · exact hj.symm
  · calc OcRep C ν (OcOfMem C ν (⟨x, hx1⟩ : {y : ClassFunction ↥C.P.H0 ℂ // y ∈ lamOrbit C ν}))
        = sconj C (sconj C (OcRep C ν (OcOfMem C ν
            (⟨x, hx1⟩ : {y : ClassFunction ↥C.P.H0 ℂ // y ∈ lamOrbit C ν})))) :=
          (sconj_sconj C _).symm
      _ = sconj C x := (congrArg (sconj C) hj).symm
      _ = x := hx2

private noncomputable def OcFxEquivFixed :
    {i : OcIdx C ν // i ∈ OcFx C ν} ≃ {x : ClassFunction ↥C.P.H0 ℂ // x ∈ OcFixed C ν} where
  toFun i := ⟨OcRep C ν i.1, OcRep_mem C ν i.1, i.2⟩
  invFun x := ⟨OcOfMem C ν ⟨x.1, x.2.1⟩, by
    have h := OcRep_mk_of_fixed C ν x.2.1 x.2.2
    show sconj C (OcRep C ν (OcOfMem C ν ⟨x.1, x.2.1⟩)) =
      OcRep C ν (OcOfMem C ν ⟨x.1, x.2.1⟩)
    rw [h]; exact x.2.2⟩
  left_inv i := by
    apply Subtype.ext
    show OcOfMem C ν ⟨OcRep C ν i.1, OcRep_mem C ν i.1⟩ = i.1
    exact OcMk_OcRep C ν i.1
  right_inv x := by
    apply Subtype.ext
    exact OcRep_mk_of_fixed C ν x.2.1 x.2.2

private theorem OcFx_ncard_eq_fixed : (OcFx C ν).ncard = (OcFixed C ν).ncard := by
  rw [← Nat.card_coe_set_eq (OcFx C ν), ← Nat.card_coe_set_eq (OcFixed C ν)]
  exact Nat.card_congr (OcFxEquivFixed C ν)

private theorem OcOrb_ncard_eq :
    (lamOrbit C ν).ncard = Nat.card (OcIdx C ν) + (OcP C ν).ncard := by
  classical
  set f : OcIdx C ν ⊕ {i : OcIdx C ν // i ∈ OcP C ν} → ClassFunction ↥C.P.H0 ℂ :=
    Sum.elim (fun i => OcRep C ν i) (fun i => sconj C (OcRep C ν i.1)) with hf
  have hinj : Function.Injective f := by
    intro p q hpq
    rcases p with i | ⟨i, hi⟩ <;> rcases q with k | ⟨k, hk⟩
    · simp only [hf, Sum.elim_inl] at hpq
      exact congrArg Sum.inl (OcIdx_unique C ν (Or.inl hpq))
    · simp only [hf, Sum.elim_inl, Sum.elim_inr] at hpq
      have hik : i = k := OcIdx_unique C ν (Or.inr hpq)
      rw [hik] at hpq
      exact absurd hpq.symm hk.2
    · simp only [hf, Sum.elim_inl, Sum.elim_inr] at hpq
      have hik : k = i := OcIdx_unique C ν (Or.inr hpq.symm)
      rw [hik] at hpq
      exact absurd hpq hi.2
    · simp only [hf, Sum.elim_inr] at hpq
      refine congrArg Sum.inr (Subtype.ext (OcIdx_unique C ν (Or.inl ?_)))
      rw [← sconj_sconj C (OcRep C ν i), ← sconj_sconj C (OcRep C ν k), hpq]
  have himg : f '' Set.univ = lamOrbit C ν := by
    ext x
    constructor
    · rintro ⟨p, -, hp⟩
      rcases p with i | ⟨i, hi⟩
      · rw [← hp]; exact OcRep_mem C ν i
      · rw [← hp]; exact hi.1
    · intro hx
      obtain ⟨j, hj, -⟩ := OcRep_spec C ν x hx
      rcases hj with hj | hj
      · exact ⟨Sum.inl j, Set.mem_univ _, by rw [hf]; exact hj.symm⟩
      · by_cases hfix : sconj C (OcRep C ν j) = OcRep C ν j
        · exact ⟨Sum.inl j, Set.mem_univ _, by rw [hf]; exact (hj.trans hfix).symm⟩
        · exact ⟨Sum.inr ⟨j, ⟨by rw [← hj]; exact hx, hfix⟩⟩, Set.mem_univ _,
            by rw [hf]; exact hj.symm⟩
  rw [← himg, Set.ncard_image_of_injective _ hinj, Set.ncard_univ, Nat.card_sum,
    Nat.card_coe_set_eq]

private theorem OcSInv_of_mem {x : ClassFunction ↥C.P.H0 ℂ}
    (hx : x ∈ lamOrbit C ν) (hs : sconj C x ∈ lamOrbit C ν) : OcSInv C ν := by
  have h1 : sconj C '' lamOrbit C ν = lamOrbit C (sconj C ν) :=
    s02c_sconj_image_lamOrbit C (sconjLam C) ν
  have hxν : lamOrbit C x = lamOrbit C ν := (s02c_lamOrbit_eq_of_lamEquiv C hx).symm
  have hxs : sconj C x ∈ lamOrbit C x := by rw [hxν]; exact hs
  have hsn : sconj C x ∈ lamOrbit C (sconj C ν) := by rw [← h1]; exact ⟨x, hx, rfl⟩
  have heq : lamOrbit C (sconj C ν) = lamOrbit C x :=
    (s02c_lamOrbit_eq_of_lamEquiv C
      (s02c_LamEquiv_trans C hxs (s02c_LamEquiv_symm C hsn))).symm
  show sconj C '' lamOrbit C ν = lamOrbit C ν
  rw [h1, heq, hxν]

private theorem OcSInv_iff :
    OcSInv C ν ↔ ∀ i : OcIdx C ν, sconj C (OcRep C ν i) ∈ lamOrbit C ν := by
  constructor
  · intro h i
    rw [← h]; exact ⟨OcRep C ν i, OcRep_mem C ν i, rfl⟩
  · intro h
    refine Set.Subset.antisymm ?_ ?_
    · rintro x ⟨y, hy, rfl⟩
      obtain ⟨j, hj, -⟩ := OcRep_spec C ν y hy
      rcases hj with hj | hj
      · rw [hj]; exact h j
      · rw [hj, sconj_sconj]; exact OcRep_mem C ν j
    · intro x hx
      obtain ⟨j, hj, -⟩ := OcRep_spec C ν x hx
      rcases hj with hj | hj
      · rw [hj]
        exact ⟨sconj C (OcRep C ν j), h j, by rw [sconj_sconj]⟩
      · exact ⟨OcRep C ν j, OcRep_mem C ν j, hj.symm⟩

private theorem OcP_eq_NF_of_sInv (h : OcSInv C ν) : OcP C ν = OcNF C ν := by
  ext i
  exact ⟨fun hi => hi.2, fun hi => ⟨(OcSInv_iff C ν).mp h i, hi⟩⟩

private theorem OcP_eq_empty_of_not_sInv (h : ¬ OcSInv C ν) : OcP C ν = ∅ := by
  ext i
  constructor
  · intro hi
    exact absurd (OcSInv_of_mem C ν (OcRep_mem C ν i) hi.1) h
  · exact fun hi => absurd hi (Set.notMem_empty i)

private theorem OcFixed_ncard_of_sInv (hν : IsIrreducibleCharacter ν) (h : OcSInv C ν) :
    (OcFixed C ν).ncard = 2 := by
  have hmem : sconj C ν ∈ lamOrbit C ν := by
    rw [← h]; exact ⟨ν, mem_lamOrbit_self C ν, rfl⟩
  have hβ : ∃ β : quotGroup C.P →* ℂˣ, sconj C ν = lamCF C β * ν := hmem
  obtain ⟨β, hβ'⟩ := hβ
  exact card_fixed C ν hν hβ'

private theorem OcFixed_eq_empty_of_not_sInv (h : ¬ OcSInv C ν) : OcFixed C ν = ∅ := by
  ext x
  constructor
  · intro hx
    obtain ⟨hx1, hx2⟩ := hx
    exact absurd (OcSInv_of_mem C ν hx1 (by rw [hx2]; exact hx1)) h
  · exact fun hx => absurd hx (Set.notMem_empty x)

end Transversal


section Stage3
variable [Fintype G] [Invertible (Nat.card G : ℂ)]
variable (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
variable (ν : ClassFunction ↥C.P.H0 ℂ)

private noncomputable def OcA (i : OcIdx C ν) : ℕ := by
  classical
  exact if sconj C (OcRep C ν i) = OcRep C ν i then 2 else 1

private theorem OcA_eq_one_iff (i : OcIdx C ν) : OcA C ν i = 1 ↔ i ∈ OcNF C ν := by
  classical
  rw [OcA]
  by_cases h : sconj C (OcRep C ν i) = OcRep C ν i <;> simp [h, OcNF]

private theorem OcA_eq_two_iff (i : OcIdx C ν) : OcA C ν i = 2 ↔ i ∈ OcFx C ν := by
  classical
  rw [OcA]
  by_cases h : sconj C (OcRep C ν i) = OcRep C ν i <;> simp [h, OcFx]

private theorem OcA_one_or_two (i : OcIdx C ν) : OcA C ν i = 1 ∨ OcA C ν i = 2 := by
  classical
  rw [OcA]
  by_cases h : sconj C (OcRep C ν i) = OcRep C ν i <;> simp [h]

private theorem OcRep_irr (hν : IsIrreducibleCharacter ν) (i : OcIdx C ν) :
    IsIrreducibleCharacter (OcRep C ν i) :=
  irreducible_of_mem_lamOrbit C (OcRep_mem C ν i) hν

private theorem OcRep_lamEquiv (i k : OcIdx C ν) : LamEquiv C (OcRep C ν i) (OcRep C ν k) :=
  s02c_LamEquiv_trans C (s02c_LamEquiv_symm C (OcRep_mem C ν i)) (OcRep_mem C ν k)

private theorem OcRep_ne (i k : OcIdx C ν) (h : i ≠ k) : OcRep C ν i ≠ OcRep C ν k :=
  fun hh => h (OcIdx_unique C ν (Or.inl hh))

private theorem OcRep_ne_v (i k : OcIdx C ν) (h : i ≠ k) : OcRep C ν k ≠ OcRep C ν i :=
  fun hh => h (OcIdx_unique C ν (Or.inl hh.symm))

private theorem OcRep_ne_c (i k : OcIdx C ν) (h : i ≠ k) :
    OcRep C ν i ≠ sconj C (OcRep C ν k) :=
  fun hh => h (OcIdx_unique C ν (Or.inr hh))

private theorem OcRep_ne_c' (i k : OcIdx C ν) (h : i ≠ k) :
    OcRep C ν k ≠ sconj C (OcRep C ν i) :=
  fun hh => h (OcIdx_unique C ν (Or.inr hh)).symm

private theorem OcCH_apply (α β : ClassFunction ↥C.P.H0 ℂ) :
    cH C α β = (if β = α then (1 : ℂ) else 0) + (if β = sconj C α then 1 else 0) := rfl

private theorem OcCHeq (i k : OcIdx C ν) :
    ((if OcRep C ν k = OcRep C ν i then (1 : ℂ) else 0) +
      (if OcRep C ν k = sconj C (OcRep C ν i) then 1 else 0)) =
    (if i = k then (OcA C ν i : ℂ) else 0) := by
  classical
  by_cases hik : i = k
  · subst hik
    by_cases hf : sconj C (OcRep C ν i) = OcRep C ν i
    · rw [if_pos rfl, if_pos hf.symm, OcA, if_pos hf]
      norm_num
    · rw [if_pos rfl, if_neg (fun h => hf h.symm), OcA, if_neg hf]
      norm_num
  · rw [if_neg hik, if_neg (OcRep_ne_v C ν i k hik), if_neg (OcRep_ne_c' C ν i k hik)]
    norm_num

private theorem OcGram (hν : IsIrreducibleCharacter ν) (i1 : OcIdx C ν)
    (hi1 : i1 ∈ OcNF C ν) (i k : OcIdx C ν)
    (hi : i ≠ i1) (hk : k ≠ i1) :
    ClassFunction.inner (ind C (OcRep C ν i1 - OcRep C ν i))
      (ind C (OcRep C ν i1 - OcRep C ν k)) =
      (OcA C ν i1 : ℂ) + if i = k then (OcA C ν i : ℂ) else 0 := by
  classical
  rw [s02_gram C (OcRep C ν i1) (OcRep C ν i) (OcRep C ν i1) (OcRep C ν k)
    (OcRep_irr C ν hν i1) (OcRep_irr C ν hν i) (OcRep_irr C ν hν i1) (OcRep_irr C ν hν k)
    (OcRep_lamEquiv C ν i1 i) (OcRep_lamEquiv C ν i1 k)]
  rw [OcCH_apply, OcCH_apply, OcCH_apply, OcCH_apply]
  have h1 : OcA C ν i1 = 1 := (OcA_eq_one_iff C ν i1).mpr hi1
  rw [if_pos rfl, if_neg (fun h : OcRep C ν i1 = sconj C (OcRep C ν i1) => hi1 h.symm),
    if_neg (OcRep_ne C ν k i1 hk), if_neg (OcRep_ne_c C ν k i1 hk),
    if_neg (OcRep_ne_v C ν i i1 hi), if_neg (OcRep_ne_c' C ν i i1 hi)]
  rw [OcCHeq C ν i k, h1]
  ring

private theorem OcInd_sub (θ θ' : ClassFunction ↥C.P.H0 ℂ) :
    ind C (θ - θ') = ind C θ - ind C θ' := by
  have h1 : (-θ' : ClassFunction ↥C.P.H0 ℂ) = (-1 : ℂ) • θ' := by ext x; simp
  simp only [ind, sub_eq_add_neg]
  rw [ClassFunction.induce_add, h1, ClassFunction.induce_smul]
  simp

private theorem OcInd_conj (θ : ClassFunction ↥C.P.H0 ℂ) :
    ind C (sconj C θ) = ind C θ := induce_conjByH C.P C.s θ

private theorem OcD_mem (hν : IsIrreducibleCharacter ν) (i1 i : OcIdx C ν) :
    ind C (OcRep C ν i1 - OcRep C ν i) ∈ ZIrr G :=
  (s02_indDiff C (OcRep C ν i1) (OcRep C ν i) (OcRep_irr C ν hν i1)
    (OcRep_irr C ν hν i) (OcRep_lamEquiv C ν i1 i)).1

private theorem OcD_deg (hν : IsIrreducibleCharacter ν) (i1 i : OcIdx C ν) :
    ind C (OcRep C ν i1 - OcRep C ν i) 1 = 0 :=
  (s02_indDiff C (OcRep C ν i1) (OcRep C ν i) (OcRep_irr C ν hν i1)
    (OcRep_irr C ν hν i) (OcRep_lamEquiv C ν i1 i)).2

private theorem OcD_self (i1 : OcIdx C ν) :
    ind C (OcRep C ν i1 - OcRep C ν i1) = 0 := by
  rw [sub_self]
  ext g
  simp [ind, ClassFunction.induce_apply, ClassFunction.induceSum_apply]

private noncomputable def OcF (g : OcIdx C ν → ClassFunction G ℂ) :
    ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ := by
  classical
  exact fun ξ => if h : ∃ i : OcIdx C ν, ξ = OcRep C ν i ∨ ξ = sconj C (OcRep C ν i)
    then g (Classical.choose h) else 0

private theorem OcF_eq_of (g : OcIdx C ν → ClassFunction G ℂ) (i : OcIdx C ν)
    (u : ClassFunction ↥C.P.H0 ℂ) (hu : u ∈ orbitKey C ν)
    (hi : u = OcRep C ν i ∨ u = sconj C (OcRep C ν i)) :
    OcF C ν g u = g i := by
  classical
  obtain ⟨i₀, hi₀, huniq⟩ := OcIdx_cover C ν u hu
  have hex : ∃ k : OcIdx C ν, u = OcRep C ν k ∨ u = sconj C (OcRep C ν k) := ⟨i₀, hi₀⟩
  show (if h : ∃ k : OcIdx C ν, u = OcRep C ν k ∨ u = sconj C (OcRep C ν k)
    then g (Classical.choose h) else 0) = g i
  rw [dif_pos hex]
  have hch : Classical.choose hex = i₀ := huniq _ (Classical.choose_spec hex)
  rw [hch, (huniq i hi).symm]

private theorem OcF_sconj (g : OcIdx C ν → ClassFunction G ℂ) (u : ClassFunction ↥C.P.H0 ℂ)
    (hu : u ∈ orbitKey C ν) : OcF C ν g (sconj C u) = OcF C ν g u := by
  obtain ⟨i, hi, -⟩ := OcIdx_cover C ν u hu
  have hs : sconj C u ∈ orbitKey C ν := s02c_sconj_mem_orbitKey C hu
  rw [OcF_eq_of C ν g i (sconj C u) hs (by
        rcases hi with h | h
        · exact Or.inr (by rw [h])
        · exact Or.inl (by rw [h, sconj_sconj])),
    OcF_eq_of C ν g i u hu hi]

private theorem OcNF_ncard_sInv (hν : IsIrreducibleCharacter ν) (hs : OcSInv C ν) :
    (OcNF C ν).ncard = Nat.card (OcIdx C ν) - 2 := by
  have h1 := OcIdx_ncard_split C ν
  rw [OcFx_ncard_eq_fixed C ν, OcFixed_ncard_of_sInv C ν hν hs] at h1
  omega

private theorem OcNF_ncard_not_sInv (hs : ¬ OcSInv C ν) :
    (OcNF C ν).ncard = Nat.card (OcIdx C ν) := by
  have h1 := OcIdx_ncard_split C ν
  rw [OcFx_ncard_eq_fixed C ν, OcFixed_eq_empty_of_not_sInv C ν hs, Set.ncard_empty] at h1
  omega

private theorem OcIdx_card_ge_two (hν : IsIrreducibleCharacter ν) :
    2 ≤ Fintype.card (OcIdx C ν) := by
  rw [Fintype.card_eq_nat_card, OcIdx_ncard_split C ν, OcFx_ncard_eq_fixed C ν]
  by_cases hs : OcSInv C ν
  · rw [OcFixed_ncard_of_sInv C ν hν hs]; omega
  · rw [OcFixed_eq_empty_of_not_sInv C ν hs, Set.ncard_empty, OcNF_ncard_not_sInv C ν hs,
      Nat.zero_add]
    have hO := OcOrb_ncard_eq C ν
    rw [OcP_eq_empty_of_not_sInv C ν hs, Set.ncard_empty, add_zero] at hO
    have := oc_orbitCard_ge_two C hν
    omega

private theorem OcNF_pos (hν : IsIrreducibleCharacter ν) (h : 3 ≤ Fintype.card (OcIdx C ν)) :
    0 < (OcNF C ν).ncard := by
  have hN : 3 ≤ Nat.card (OcIdx C ν) := by rw [← Fintype.card_eq_nat_card]; exact h
  by_cases hs : OcSInv C ν
  · rw [OcNF_ncard_sInv C ν hν hs]; omega
  · rw [OcNF_ncard_not_sInv C ν hs]; omega

private theorem OcOrb_ne_six (hν : IsIrreducibleCharacter ν) (k : ℕ)
    (h : (lamOrbit C ν).ncard = 2 ^ (k + 1)) : (lamOrbit C ν).ncard ≠ 6 := by
  intro h6
  rw [h] at h6
  have h3 : 3 ∣ 2 ^ (k + 1) := by rw [h6]; norm_num
  have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

private theorem OcNF_three (hν : IsIrreducibleCharacter ν) (h : 4 ≤ Fintype.card (OcIdx C ν)) :
    3 ≤ (OcNF C ν).ncard := by
  have hN : 4 ≤ Nat.card (OcIdx C ν) := by rw [← Fintype.card_eq_nat_card]; exact h
  by_cases hs : OcSInv C ν
  · rw [OcNF_ncard_sInv C ν hν hs]
    by_contra hcon
    push_neg at hcon
    have h4 : Nat.card (OcIdx C ν) = 4 := by omega
    have hO := OcOrb_ncard_eq C ν
    rw [OcP_eq_NF_of_sInv C ν hs, h4, OcNF_ncard_sInv C ν hν hs, h4] at hO
    obtain ⟨k, hk⟩ := oc_orbitCard C hν
    exact OcOrb_ne_six C ν hν k hk (by omega)
  · rw [OcNF_ncard_not_sInv C ν hs]; omega

private theorem OcExists_nonfixed (hν : IsIrreducibleCharacter ν)
    (h : 3 ≤ Fintype.card (OcIdx C ν)) : ∃ i : OcIdx C ν, i ∈ OcNF C ν := by
  have hne : 0 < (OcNF C ν).ncard := OcNF_pos C ν hν h
  exact (Set.ncard_pos (Set.finite_univ.subset (Set.subset_univ _))).mp hne

private theorem OcExists_three (hν : IsIrreducibleCharacter ν) (h : 4 ≤ Fintype.card (OcIdx C ν)) :
    ∃ i1 i2 i3 : OcIdx C ν, i1 ≠ i2 ∧ i1 ≠ i3 ∧ i2 ≠ i3 ∧
      i1 ∈ OcNF C ν ∧ i2 ∈ OcNF C ν ∧ i3 ∈ OcNF C ν := by
  have h3 : 3 ≤ (OcNF C ν).ncard := OcNF_three C ν hν h
  have hfin : (OcNF C ν).Finite := Set.finite_univ.subset (Set.subset_univ _)
  set S : Finset (OcIdx C ν) := Set.Finite.toFinset hfin with hS
  have hScard : 3 ≤ S.card := by
    rw [hS, ← Set.ncard_eq_toFinset_card (OcNF C ν) hfin]
    exact h3
  obtain ⟨i1, hi1⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  obtain ⟨i2, hi2⟩ := Finset.card_pos.mp (by
    rw [Finset.card_erase_of_mem hi1]; omega : 0 < (S.erase i1).card)
  obtain ⟨i3, hi3⟩ := Finset.card_pos.mp (by
    rw [Finset.card_erase_of_mem hi2, Finset.card_erase_of_mem hi1]; omega :
      0 < ((S.erase i1).erase i2).card)
  have hmemS : ∀ {a : OcIdx C ν}, a ∈ S → a ∈ OcNF C ν := fun ha => by
    rw [hS] at ha; exact (Set.Finite.mem_toFinset hfin).mp ha
  have h21 : i2 ≠ i1 := (Finset.mem_erase.mp hi2).1
  have h31 : i3 ≠ i1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi3).2).1
  have h32 : i3 ≠ i2 := (Finset.mem_erase.mp hi3).1
  have hi2S : i2 ∈ S := Finset.mem_of_mem_erase hi2
  have hi3S : i3 ∈ S := (Finset.mem_erase.mp (Finset.mem_erase.mp hi3).2).2
  exact ⟨i1, i2, i3, h21.symm, h31.symm, h32.symm, hmemS hi1, hmemS hi2S, hmemS hi3S⟩

private theorem OcExists_ne (i1 : OcIdx C ν) (h : 3 ≤ Fintype.card (OcIdx C ν)) :
    ∃ i2 i3 : OcIdx C ν, i2 ≠ i3 ∧ i2 ≠ i1 ∧ i3 ≠ i1 := by
  have hcard : 2 ≤ (Finset.univ.erase i1).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i1), Finset.card_univ]
    omega
  obtain ⟨i2, hi2⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.erase i1).card)
  obtain ⟨i3, hi3⟩ := Finset.card_pos.mp (by
    rw [Finset.card_erase_of_mem hi2]; omega : 0 < ((Finset.univ.erase i1).erase i2).card)
  exact ⟨i2, i3, (Finset.mem_erase.mp hi3).1.symm, (Finset.mem_erase.mp hi2).1,
    (Finset.mem_erase.mp (Finset.mem_erase.mp hi3).2).1⟩

private theorem OcA_const_two (hν : IsIrreducibleCharacter ν)
    (h : Fintype.card (OcIdx C ν) ≤ 2) (i k : OcIdx C ν) :
    OcA C ν i = OcA C ν k := by
  rw [Fintype.card_eq_nat_card] at h
  have hmem : ∀ i : OcIdx C ν, i ∈ OcFx C ν ∨ i ∈ OcNF C ν := by
    intro i
    have h := OcFx_union_NF C ν
    have : i ∈ OcFx C ν ∪ OcNF C ν := by rw [h]; trivial
    exact this
  have hfin : (OcNF C ν).Finite := Set.finite_univ.subset (Set.subset_univ _)
  by_cases hs : OcSInv C ν
  · have h1 : (OcNF C ν).ncard = 0 := by rw [OcNF_ncard_sInv C ν hν hs]; omega
    have hne : OcNF C ν = ∅ := (Set.ncard_eq_zero hfin).mp h1
    have hFi : i ∈ OcFx C ν := by
      rcases hmem i with h' | h'
      · exact h'
      · rw [hne] at h'; exact absurd h' (Set.notMem_empty i)
    have hFk : k ∈ OcFx C ν := by
      rcases hmem k with h' | h'
      · exact h'
      · rw [hne] at h'; exact absurd h' (Set.notMem_empty k)
    rw [(OcA_eq_two_iff C ν i).mpr hFi, (OcA_eq_two_iff C ν k).mpr hFk]
  · have h1 : (OcFx C ν).ncard = 0 := by
      rw [OcFx_ncard_eq_fixed C ν, OcFixed_eq_empty_of_not_sInv C ν hs, Set.ncard_empty]
    have hne : OcFx C ν = ∅ :=
      (Set.ncard_eq_zero (Set.finite_univ.subset (Set.subset_univ _))).mp h1
    have hNi : i ∈ OcNF C ν := by
      rcases hmem i with h' | h'
      · rw [hne] at h'; exact absurd h' (Set.notMem_empty i)
      · exact h'
    have hNk : k ∈ OcNF C ν := by
      rcases hmem k with h' | h'
      · rw [hne] at h'; exact absurd h' (Set.notMem_empty k)
      · exact h'
    rw [(OcA_eq_one_iff C ν i).mpr hNi, (OcA_eq_one_iff C ν k).mpr hNk]

private theorem OcA_eq (i : OcIdx C ν) :
    OcA C ν i = if sconj C (OcRep C ν i) = OcRep C ν i then 2 else 1 := rfl

private theorem OcCH_diag (i : OcIdx C ν) :
    (1 : ℂ) + (if OcRep C ν i = sconj C (OcRep C ν i) then 1 else 0) = (OcA C ν i : ℂ) := by
  classical
  rw [OcA_eq]
  by_cases h : sconj C (OcRep C ν i) = OcRep C ν i
  · rw [if_pos h, if_pos h.symm]; norm_num
  · rw [if_neg h, if_neg (fun hh => h hh.symm)]; norm_num

private theorem OcGram_two (hν : IsIrreducibleCharacter ν) (i1 i2 : OcIdx C ν) (h12 : i1 ≠ i2) :
    ClassFunction.inner (ind C (OcRep C ν i1 - OcRep C ν i2))
      (ind C (OcRep C ν i1 - OcRep C ν i2)) = (OcA C ν i1 : ℂ) + (OcA C ν i2 : ℂ) := by
  classical
  rw [s02_gram C (OcRep C ν i1) (OcRep C ν i2) (OcRep C ν i1) (OcRep C ν i2)
    (OcRep_irr C ν hν i1) (OcRep_irr C ν hν i2) (OcRep_irr C ν hν i1) (OcRep_irr C ν hν i2)
    (OcRep_lamEquiv C ν i1 i2) (OcRep_lamEquiv C ν i1 i2)]
  rw [OcCH_apply, OcCH_apply, OcCH_apply, OcCH_apply]
  rw [if_pos rfl, if_pos rfl,
    if_neg (OcRep_ne_v C ν i1 i2 h12), if_neg (OcRep_ne_c C ν i2 i1 (Ne.symm h12)),
    if_neg (OcRep_ne C ν i1 i2 h12), if_neg (OcRep_ne_c C ν i1 i2 h12)]
  rw [← OcCH_diag C ν i1, ← OcCH_diag C ν i2]
  ring

private theorem OcInd_diff (hν : IsIrreducibleCharacter ν) (g : OcIdx C ν → ClassFunction G ℂ)
    (i1 : OcIdx C ν)
    (h2 : ∀ i, ind C (OcRep C ν i1 - OcRep C ν i) = g i1 - g i)
    {μ v : ClassFunction ↥C.P.H0 ℂ} (hμ : μ ∈ orbitKey C ν) (hv : v ∈ orbitKey C ν) :
    ind C (μ - v) = OcF C ν g μ - OcF C ν g v := by
  classical
  obtain ⟨iμ, hiμ, -⟩ := OcIdx_cover C ν μ hμ
  obtain ⟨iν, hiν, -⟩ := OcIdx_cover C ν v hv
  have hfμ : OcF C ν g μ = g iμ := OcF_eq_of C ν g iμ μ hμ hiμ
  have hfν : OcF C ν g v = g iν := OcF_eq_of C ν g iν v hv hiν
  have hindμ : ind C μ = ind C (OcRep C ν iμ) := by
    rcases hiμ with h | h
    · rw [h]
    · rw [h]; exact OcInd_conj C _
  have hindν : ind C v = ind C (OcRep C ν iν) := by
    rcases hiν with h | h
    · rw [h]
    · rw [h]; exact OcInd_conj C _
  have hgi : ∀ i, g i = g i1 - ind C (OcRep C ν i1 - OcRep C ν i) := by
    intro i; rw [h2 i]; abel
  have hL : ind C (μ - v) = ind C (OcRep C ν iμ - OcRep C ν iν) := by
    rw [OcInd_sub, hindμ, hindν]
    rw [OcInd_sub]
  have hR : OcF C ν g μ - OcF C ν g v = ind C (OcRep C ν iμ - OcRep C ν iν) := by
    have hD : ind C (OcRep C ν iμ - OcRep C ν iν) =
        ind C (OcRep C ν i1 - OcRep C ν iν) - ind C (OcRep C ν i1 - OcRep C ν iμ) := by
      rw [OcInd_sub, OcInd_sub, OcInd_sub] <;> abel
    rw [hfμ, hfν, hgi iμ, hgi iν]
    rw [show g i1 - ind C (OcRep C ν i1 - OcRep C ν iμ) -
        (g i1 - ind C (OcRep C ν i1 - OcRep C ν iν)) =
        ind C (OcRep C ν i1 - OcRep C ν iν) - ind C (OcRep C ν i1 - OcRep C ν iμ)
        from by abel]
    exact hD.symm
  rw [hL, hR]

private theorem OcVi (hν : IsIrreducibleCharacter ν) (g : OcIdx C ν → ClassFunction G ℂ)
    (i1 : OcIdx C ν)
    (h1 : ∀ i, g i ∈ ZIrr G ∧ ClassFunction.inner (g i) (g i) = (OcA C ν i : ℂ))
    (h2 : ∀ i, ind C (OcRep C ν i1 - OcRep C ν i) = g i1 - g i)
    {ξ : ClassFunction ↥C.P.H0 ℂ} (hξO : ξ ∈ lamOrbit C ν)
    (hξi : IsIrreducibleCharacter ξ) (hξns : sconj C ξ ≠ ξ)
    (hnot : ¬ ((lamOrbit C ξ).ncard = 4 ∧ sconj C '' lamOrbit C ξ = lamOrbit C ξ)) :
    OcF C ν g ξ (C.t : G) = 2 * ξ C.t := by
  classical
  have hξk : ξ ∈ orbitKey C ν := Or.inl hξO
  obtain ⟨μ, hμ, hμns, hμt⟩ := s02_lemma21Ext C ξ hξi hξns hnot
  have hμν : μ ∈ lamOrbit C ν := by
    rw [← s02c_lamOrbit_eq_of_lamEquiv C hξO] at hμ
    exact hμ
  have hμk : μ ∈ orbitKey C ν := Or.inl hμν
  have hμi : IsIrreducibleCharacter μ := irreducible_of_mem_lamOrbit C hμ hξi
  obtain ⟨iμ, hiμ, -⟩ := OcIdx_cover C ν μ hμk
  obtain ⟨iξ, hiξ, -⟩ := OcIdx_cover C ν ξ hξk
  have hfμ : OcF C ν g μ = g iμ := OcF_eq_of C ν g iμ μ hμk hiμ
  have hfξ : OcF C ν g ξ = g iξ := OcF_eq_of C ν g iξ ξ hξk hiξ
  have hAiμ : OcA C ν iμ = 1 := by
    rw [OcA_eq_one_iff]
    rcases hiμ with h | h
    · intro hc; exact hμns (by rw [h, hc])
    · intro hc
      exact hμns (by rw [h, sconj_sconj]; exact hc.symm)
  have hAiξ : OcA C ν iξ = 1 := by
    rw [OcA_eq_one_iff]
    rcases hiξ with h | h
    · intro hc; exact hξns (by rw [h, hc])
    · intro hc
      exact hξns (by rw [h, sconj_sconj]; exact hc.symm)
  have hpmμ : IsPmIrr (OcF C ν g μ) := by
    rw [hfμ]
    refine isPmIrr_of_mem_ZIrr_inner_self_eq_one (h1 iμ).1 ?_
    rw [(h1 iμ).2, hAiμ]; norm_num
  have hpmξ : IsPmIrr (OcF C ν g ξ) := by
    rw [hfξ]
    refine isPmIrr_of_mem_ZIrr_inner_self_eq_one (h1 iξ).1 ?_
    rw [(h1 iξ).2, hAiξ]; norm_num
  have hlam : LamEquiv C μ ξ := s02c_LamEquiv_symm C hμ
  have hind : ind C (μ - ξ) = OcF C ν g μ - OcF C ν g ξ :=
    OcInd_diff C ν hν g i1 h2 hμk hξk
  exact s02_vi C μ ξ hμi hξi hlam hμns hξns hμt _ _ hpmμ hpmξ hind

private theorem Oc_f_img (x : ClassFunction ↥C.P.H0 ℂ) :
    sconj C '' lamOrbit C x = lamOrbit C (sconj C x) :=
  s02c_sconj_image_lamOrbit C (sconjLam C) x

private theorem Oc_sconj_inj : Function.Injective (sconj C (G := G)) :=
  fun a b h => by rw [← sconj_sconj C a, ← sconj_sconj C b, h]

private theorem OcCoherentOfG (hν : IsIrreducibleCharacter ν) (g : OcIdx C ν → ClassFunction G ℂ)
    (i1 : OcIdx C ν)
    (h1 : ∀ i, g i ∈ ZIrr G ∧ ClassFunction.inner (g i) (g i) = (OcA C ν i : ℂ))
    (h2 : ∀ i, ind C (OcRep C ν i1 - OcRep C ν i) = g i1 - g i)
    (h3 : ∀ i k, i ≠ k → DisjointCF (g i) (g k)) :
    GoodOn C (orbitKey C ν) (OcF C ν g) := by
  classical
  intro μ hμ v hv hμi hvi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨iν, hiν, -⟩ := OcIdx_cover C ν v hv
    rw [OcF_eq_of C ν g iν v hv hiν]
    exact (h1 iν).1
  · exact OcF_sconj C ν g v hv
  · obtain ⟨iν, hiν, -⟩ := OcIdx_cover C ν v hv
    have hfν : OcF C ν g v = g iν := OcF_eq_of C ν g iν v hv hiν
    have hiff : sconj C v = v ↔ iν ∈ OcFx C ν := by
      rcases hiν with hiν | hiν
      · rw [hiν, OcFx]
        exact Iff.rfl
      · rw [hiν, OcFx, sconj_sconj]
        exact ⟨fun h => h.symm, fun h => h.symm⟩
    rw [hfν, (h1 iν).2]
    by_cases hfx : sconj C v = v
    · rw [if_pos hfx]
      rw [(OcA_eq_two_iff C ν iν).mpr (hiff.mp hfx)]
      norm_num
    · rw [if_neg hfx]
      rw [(OcA_eq_one_iff C ν iν).mpr (fun hc => hfx (hiff.mpr hc))]
      norm_num
  · intro hlm
    exact OcInd_diff C ν hν g i1 h2 hμ hv
  · intro hlm hne hnes
    obtain ⟨iμ, hiμ, -⟩ := OcIdx_cover C ν μ hμ
    obtain ⟨iν, hiν, -⟩ := OcIdx_cover C ν v hv
    have hfμ : OcF C ν g μ = g iμ := OcF_eq_of C ν g iμ μ hμ hiμ
    have hfν : OcF C ν g v = g iν := OcF_eq_of C ν g iν v hv hiν
    rw [hfμ, hfν]
    refine h3 iμ iν ?_
    intro hik
    rw [hik] at hiμ
    rcases hiμ with h | h <;> rcases hiν with h' | h'
    · exact hne (h.trans h'.symm)
    · exact hnes (by rw [h, h', sconj_sconj])
    · exact hnes (by rw [h, h'])
    · exact hne (h.trans h'.symm)
  · intro hns hnot
    obtain ⟨iν, hiν, -⟩ := OcIdx_cover C ν v hv
    have hrepO : OcRep C ν iν ∈ lamOrbit C ν := OcRep_mem C ν iν
    have hrepi : IsIrreducibleCharacter (OcRep C ν iν) := OcRep_irr C ν hν iν
    have hnsrep : sconj C (OcRep C ν iν) ≠ OcRep C ν iν := by
      rcases hiν with h | h
      · intro hc; exact hns (by rw [h, hc])
      · intro hc; exact hns (by rw [h, sconj_sconj]; exact hc.symm)
    have hnotrep : ¬ ((lamOrbit C (OcRep C ν iν)).ncard = 4 ∧
        sconj C '' lamOrbit C (OcRep C ν iν) = lamOrbit C (OcRep C ν iν)) := by
      rcases hiν with h | h
      · rw [h] at hnot; exact hnot
      · intro hcon
        apply hnot
        have hlam : lamOrbit C (sconj C (OcRep C ν iν)) = lamOrbit C (OcRep C ν iν) := by
          rw [← Oc_f_img C (OcRep C ν iν)]; exact hcon.2
        constructor
        · rw [h, hlam]; exact hcon.1
        · rw [h, Oc_f_img, sconj_sconj, hlam]
    have hvi := OcVi C ν hν g i1 h1 h2 hrepO hrepi hnsrep hnotrep
    rcases hiν with h | h
    · rw [h]; exact hvi
    · rw [h, OcF_sconj C ν g (OcRep C ν iν) (Or.inl hrepO), sconj_apply_t]
      exact hvi

private theorem OcExists_tvalue (hν : IsIrreducibleCharacter ν) (i1 : OcIdx C ν)
    (hi1 : i1 ∈ OcNF C ν) (h4 : 4 ≤ Fintype.card (OcIdx C ν)) :
    ∃ i2 : OcIdx C ν, i2 ∈ OcNF C ν ∧ i2 ≠ i1 ∧
      OcRep C ν i2 C.t = - OcRep C ν i1 C.t := by
  have hnotex : ¬ ((lamOrbit C (OcRep C ν i1)).ncard = 4 ∧
      sconj C '' lamOrbit C (OcRep C ν i1) = lamOrbit C (OcRep C ν i1)) := by
    intro hcon
    obtain ⟨h4a, h4b⟩ := hcon
    rw [← s02c_lamOrbit_eq_of_lamEquiv C (OcRep_mem C ν i1)] at h4a h4b
    rw [Fintype.card_eq_nat_card] at h4
    by_cases hs : OcSInv C ν
    · have hO := OcOrb_ncard_eq C ν
      rw [OcP_eq_NF_of_sInv C ν hs, OcNF_ncard_sInv C ν hν hs] at hO
      omega
    · exact hs h4b
  -- `r i1` has nonzero value at `t` (Lemma 2.1-a: `ν(t) = ±ν(1) ≠ 0`)
  have hri1t : OcRep C ν i1 C.t ≠ 0 := by
    obtain ⟨β, hβ⟩ := OcRep_mem C ν i1
    have hcv := centralValue C ν hν
    rw [hβ, mul_apply_t C β ν]
    refine mul_ne_zero (β (tU C)).ne_zero ?_
    rcases hcv.1 with h | h
    · rw [h]; exact hcv.2
    · rw [h]; exact neg_ne_zero.mpr hcv.2
  obtain ⟨μ, hμO, hμns, hμt⟩ := s02_lemma21Ext C (OcRep C ν i1) (OcRep_irr C ν hν i1)
    (by intro hc; exact hi1 hc) hnotex
  have hμν : μ ∈ lamOrbit C ν := by
    rw [← s02c_lamOrbit_eq_of_lamEquiv C (OcRep_mem C ν i1)] at hμO
    exact hμO
  obtain ⟨i2, hi2, -⟩ := OcIdx_cover C ν μ (Or.inl hμν)
  have hi2NF : i2 ∈ OcNF C ν := by
    rcases hi2 with hi2 | hi2
    · intro hc; exact hμns (by rw [hi2, hc])
    · intro hc
      exact hμns (by rw [hi2, sconj_sconj]; exact hc.symm)
  have hne : i2 ≠ i1 := by
    intro heq
    rw [heq] at hi2
    have hμt' : μ C.t = OcRep C ν i1 C.t := by
      rcases hi2 with h | h
      · rw [h]
      · rw [h, sconj_apply_t]
    rw [hμt'] at hμt
    have hx : OcRep C ν i1 C.t = 0 := by
      have h5 := congrArg (fun y : ℂ => y + OcRep C ν i1 C.t) hμt
      rw [neg_add_cancel] at h5
      have h6 : (2 : ℂ) * OcRep C ν i1 C.t = 0 := by rw [two_mul]; exact h5
      exact (mul_eq_zero.mp h6).resolve_left (by norm_num)
    exact hri1t hx
  refine ⟨i2, hi2NF, hne, ?_⟩
  rcases hi2 with hi2 | hi2
  · rw [hi2] at hμt; exact hμt
  · calc OcRep C ν i2 C.t = sconj C (OcRep C ν i2) C.t := (sconj_apply_t C _).symm
      _ = μ C.t := by rw [hi2]
      _ = - OcRep C ν i1 C.t := hμt

private theorem OcExists_third (hν : IsIrreducibleCharacter ν) (i1 i2 : OcIdx C ν)
    (hi1 : i1 ∈ OcNF C ν) (hi2 : i2 ∈ OcNF C ν) (h4 : 4 ≤ Fintype.card (OcIdx C ν)) :
    ∃ i3 : OcIdx C ν, i3 ∈ OcNF C ν ∧ i3 ≠ i1 ∧ i3 ≠ i2 := by
  have h3 : 3 ≤ (OcNF C ν).ncard := OcNF_three C ν hν h4
  by_contra hcon
  have hsub : OcNF C ν ⊆ ({i1, i2} : Set (OcIdx C ν)) := by
    intro x hx
    by_cases hx1 : x = i1
    · exact Or.inl hx1
    · by_cases hx2 : x = i2
      · exact Or.inr hx2
      · exact absurd ⟨x, hx, hx1, hx2⟩ hcon
  have h2 : (({i1, i2} : Set (OcIdx C ν))).ncard ≤ 2 := by
    rcases eq_or_ne i1 i2 with h | h
    · rw [h]; simp
    · rw [Set.ncard_pair h]
  have := Set.ncard_le_ncard hsub (Set.finite_univ.subset (Set.subset_univ _))
  omega

private theorem OcNoFail (hν : IsIrreducibleCharacter ν) (i1 i2 i3 j : OcIdx C ν)
    (hi1 : i1 ∈ OcNF C ν) (hi2 : i2 ∈ OcNF C ν) (hj : OcA C ν j = 2)
    (h12 : i1 ≠ i2) (h13 : i1 ≠ i3) (h23 : i2 ≠ i3)
    (hj1 : j ≠ i1) (hj2 : j ≠ i2) (hj3 : j ≠ i3)
    (ht2 : OcRep C ν i2 C.t = - OcRep C ν i1 C.t) :
    ¬ FailConfig (fun i => ind C (OcRep C ν i1 - OcRep C ν i)) i1 i2 i3 j :=
  s02_noFailThm C (OcRep C ν) i1 i2 i3 j
    (fun i => OcRep_irr C ν hν i)
    (fun i => OcRep_lamEquiv C ν i1 i)
    (fun ξ _ hξl => OcIdx_cover C ν ξ (Or.inl (by
      rw [s02c_lamOrbit_eq_of_lamEquiv C (OcRep_mem C ν i1)]
      exact hξl)))
    h12 h13 h23 hj1 hj2 hj3
    (by intro hc; exact hi1 hc)
    (by intro hi2c; exact hi2 hi2c)
    ht2
    ((OcA_eq_two_iff C ν j).mp hj)

end Stage3

theorem s02_orbitCoherence {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.BG.OrbitCoherenceProp C := by
  intro ν hν
  classical
  rcases Nat.lt_or_ge (Fintype.card (OcIdx C ν)) 3 with hlt | h3
  · have hle : Fintype.card (OcIdx C ν) ≤ 2 := by omega
    have hcard : Fintype.card (OcIdx C ν) = 2 := le_antisymm hle (OcIdx_card_ge_two C ν hν)
    obtain ⟨i1⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card (OcIdx C ν))
    obtain ⟨i2, hi21⟩ := Fintype.exists_ne_of_one_lt_card
      (by omega : 1 < Fintype.card (OcIdx C ν)) i1
    have h12 : i1 ≠ i2 := hi21.symm
    have hconst : OcA C ν i1 = OcA C ν i2 := OcA_const_two C ν hν hle i1 i2
    have hDnorm : ClassFunction.inner (ind C (OcRep C ν i1 - OcRep C ν i2))
        (ind C (OcRep C ν i1 - OcRep C ν i2)) = 2 * (OcA C ν i1 : ℂ) := by
      rw [OcGram_two C ν hν i1 i2 h12, hconst]; ring
    obtain ⟨g1, g2, hg1Z, hg2Z, hg1n, hg2n, hDeq, hdisj⟩ :=
      s02_twoCase (ind C (OcRep C ν i1 - OcRep C ν i2)) (OcA C ν i1)
        (OcA_one_or_two C ν i1) (OcD_mem C ν hν i1 i2) (OcD_deg C ν hν i1 i2) hDnorm
    have hcov : ∀ i : OcIdx C ν, i = i1 ∨ i = i2 := by
      intro i
      by_contra hc
      push_neg at hc
      have h3f : ({i1, i2, i} : Finset (OcIdx C ν)).card = 3 := by
        have h1 : i1 ∉ ({i2, i} : Finset (OcIdx C ν)) := by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨h12, fun h => hc.1 h.symm⟩
        have h2 : i2 ∉ ({i} : Finset (OcIdx C ν)) := by
          simp only [Finset.mem_singleton]
          exact fun h => hc.2 h.symm
        rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
          Finset.card_singleton]
      have := Finset.card_le_card (Finset.subset_univ ({i1, i2, i} : Finset (OcIdx C ν)))
      rw [Finset.card_univ, hcard] at this
      omega
    set gg : OcIdx C ν → ClassFunction G ℂ := fun i => if i = i1 then g1 else g2 with hgg
    have hgg1 : gg i1 = g1 := by rw [hgg]; simp
    have hgg2 : gg i2 = g2 := by rw [hgg]; simp [Ne.symm h12]
    have hdisj' : ∀ i k : OcIdx C ν, i ≠ k → DisjointCF (gg i) (gg k) := by
      intro i k hik
      rcases hcov i with hi | hi <;> rcases hcov k with hk | hk
      · exact absurd (hi.trans hk.symm) hik
      · rw [hi, hk, hgg1, hgg2]; exact hdisj
      · rw [hi, hk, hgg2, hgg1]
        exact fun χ => (hdisj χ).symm
      · exact absurd (hi.trans hk.symm) hik
    refine ⟨OcF C ν gg, OcCoherentOfG C ν hν gg i1 ?_ ?_ hdisj'⟩
    · intro i
      rcases hcov i with hi | hi
      · rw [hi, hgg1]; exact ⟨hg1Z, hg1n⟩
      · rw [hi, hgg2]
        exact ⟨hg2Z, by rw [hg2n, ← hconst]⟩
    · intro i
      rcases hcov i with hi | hi
      · rw [hi, hgg1, OcD_self C ν i1, sub_self]
      · rw [hi, hgg1, hgg2]; exact hDeq
  · obtain ⟨i1, hi1⟩ := OcExists_nonfixed C ν hν h3
    have ha1 : OcA C ν i1 = 1 := (OcA_eq_one_iff C ν i1).mpr hi1
    set D : OcIdx C ν → ClassFunction G ℂ :=
      fun i => ind C (OcRep C ν i1 - OcRep C ν i) with hD
    have hDmem : ∀ i, D i ∈ ZIrr G := fun i => OcD_mem C ν hν i1 i
    have hDdeg : ∀ i, D i 1 = 0 := fun i => OcD_deg C ν hν i1 i
    have hDself : D i1 = 0 := OcD_self C ν i1
    have hgram : ∀ i k, i ≠ i1 → k ≠ i1 → ClassFunction.inner (D i) (D k) =
        (OcA C ν i1 : ℂ) + if i = k then (OcA C ν i : ℂ) else 0 :=
      fun i k hi hk => OcGram C ν hν i1 hi1 i k hi hk
    by_cases h4 : 4 ≤ Fintype.card (OcIdx C ν)
    · obtain ⟨i2, hi2, h21', ht2⟩ := OcExists_tvalue C ν hν i1 hi1 h4
      have h12 : i1 ≠ i2 := h21'.symm
      obtain ⟨i3, hi3, h31, h32⟩ := OcExists_third C ν hν i1 i2 hi1 hi2 h4
      have h13 : i1 ≠ i3 := fun h => h31 h.symm
      have h23 : i2 ≠ i3 := fun h => h32 h.symm
      have ha2 : OcA C ν i2 = 1 := (OcA_eq_one_iff C ν i2).mpr hi2
      have ha3 : OcA C ν i3 = 1 := (OcA_eq_one_iff C ν i3).mpr hi3
      obtain ⟨gg, hgg1, hgg2, hgg3, -⟩ :=
        s02_abstractCoherence (K := G) i1 i2 i3 h12 h13 h23 (OcA C ν)
          (OcA_one_or_two C ν) ha1 (fun _ => ⟨ha2, ha3⟩)
          D hDmem hDself hDdeg hgram
          (fun j hj1 hj2 hj3 haj => OcNoFail C ν hν i1 i2 i3 j hi1 hi2 haj
            h12 h13 h23 hj1 hj2 hj3 ht2)
      refine ⟨OcF C ν gg, OcCoherentOfG C ν hν gg i1 hgg1 ?_ hgg3⟩
      intro i; exact hgg2 i
    · have hcard3 : Fintype.card (OcIdx C ν) = 3 := by omega
      obtain ⟨i2, i3, h23, h21, h31⟩ := OcExists_ne C ν i1 h3
      have h12 : i1 ≠ i2 := fun h => h21 h.symm
      have h13 : i1 ≠ i3 := fun h => h31 h.symm
      obtain ⟨gg, hgg1, hgg2, hgg3, -⟩ :=
        s02_abstractCoherence (K := G) i1 i2 i3 h12 h13 h23 (OcA C ν)
          (OcA_one_or_two C ν) ha1 (fun hc => by omega)
          D hDmem hDself hDdeg hgram
          (fun j hj1 hj2 hj3 _ => by
            exfalso
            have hset : ({i1, i2, i3} : Finset (OcIdx C ν)) = Finset.univ := by
              apply Finset.eq_univ_of_card
              have h1 : i1 ∉ ({i2, i3} : Finset (OcIdx C ν)) := by
                simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                exact ⟨h12, h13⟩
              have h2 : i2 ∉ ({i3} : Finset (OcIdx C ν)) := by
                simp only [Finset.mem_singleton]
                exact h23
              rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
                Finset.card_singleton, hcard3]
            have : j ∈ ({i1, i2, i3} : Finset (OcIdx C ν)) := by
              rw [hset]; exact Finset.mem_univ j
            simp only [Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with h | h | h
            · exact hj1 h
            · exact hj2 h
            · exact hj3 h)
      refine ⟨OcF C ν gg, OcCoherentOfG C ν hν gg i1 hgg1 ?_ hgg3⟩
      intro i; exact hgg2 i

end Work.BG
