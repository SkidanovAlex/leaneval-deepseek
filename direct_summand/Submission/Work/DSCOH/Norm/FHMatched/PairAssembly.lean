/-
Area DSCOH (curric-46) — the normalization comparison: assembly of the "matched" half of the
first (sorting) homotopy identity of Stacks 20.23.6 (`Work.DSCOH.Norm.firstHom_matched`).

The homotopy identity expands the `x`-component of `d ≫ h + h ≫ d` into the two families of
terms `dhTerm` (from `d ≫ h`) and `hdTerm` (from `h ≫ d`).  This file contains the *index-level*
part of the cancellation: the "matched" pairs of `dhTerm`s (those with `b ≠ castSucc a`,
`b ≠ pos2A x a`) are reindexed by the map

  `pairMap x (c, a') = (A, b)`,  `A = (Tuple.sort x)⁻¹ c).succAbove a'`,  `readA x A b = c`,

which is a bijection onto the non-matched index set; on each fibre the `dhTerm` and the `hdTerm`
are negatives of each other (the two inputs of this are supplied by the companion modules
`Work.DSCOH.PairingIndex.pairing_index` and `Work.DSCOH.PairingSign.pairing_sign`).

The main results here are `firstHom_matched_of_neg` (the reduction of the target identity to the
term-wise equality) and `firstHom_matched_of_pairing` (the same from the two pairing inputs).
-/
import Mathlib
import Submission.Work.DSCOH.Norm.FirstHomDefs
import Submission.Work.DSCOH.Norm.SortSection
import Submission.Work.DSCOH.Norm.ReadFib.readAFiber

namespace Work.DSCOH.Norm.FHMatched

open CategoryTheory Limits Opposite TopologicalSpace
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

universe u v w

variable {ι : Type*} [LinearOrder ι] [Fintype ι]

/-! ## The position reading a given value -/

/-- Every value is read by at least one position of the `a`-th read of `x` (`readA` is a
surjection `Fin (k+2) → Fin (k+1)`). -/
theorem readA_exists {k : ℕ} (x : Fin (k+1) → ι) (a : Fin (k+1)) (c : Fin (k+1)) :
    ∃ b : Fin (k+2), readA x a b = c := by
  obtain ⟨h1, h2⟩ := ReadFib.readAFiber x a
  by_cases hc : c = Tuple.sort x a
  · exact ⟨Fin.castSucc a, by
      rw [hc]
      exact (h1 (Fin.castSucc a)).mpr (Or.inl rfl)⟩
  · obtain ⟨b, hb, _⟩ := h2 c hc
    exact ⟨b, hb⟩

/-- A chosen position reading the value `c` in the `a`-th read of `x`. -/
noncomputable def pairB {k : ℕ} (x : Fin (k+1) → ι) (a : Fin (k+1)) (c : Fin (k+1)) :
    Fin (k+2) :=
  Classical.choose (readA_exists x a c)

theorem pairB_spec {k : ℕ} (x : Fin (k+1) → ι) (a : Fin (k+1)) (c : Fin (k+1)) :
    readA x a (pairB x a c) = c :=
  Classical.choose_spec (readA_exists x a c)

/-! ## The pairing map -/

/-- The pairing of the `(c,a')`-index of a `hdTerm` with the non-matched `(A,b)`-index of a
`dhTerm`: `A` is the position of the entry `c` among the `a'`-th of the entries of `x` with the
entry `c` removed (in sorted order), and `b` reads `c` in the `A`-th read of `x`. -/
noncomputable def pairMap {k : ℕ} (x : Fin (k+2) → ι) (p : Fin (k+2) × Fin (k+1)) :
    Fin (k+2) × Fin (k+3) :=
  (((Tuple.sort x).symm p.1).succAbove p.2,
    pairB x (((Tuple.sort x).symm p.1).succAbove p.2) p.1)

@[simp]
theorem pairMap_fst {k : ℕ} (x : Fin (k+2) → ι) (p : Fin (k+2) × Fin (k+1)) :
    (pairMap x p).1 = ((Tuple.sort x).symm p.1).succAbove p.2 := rfl

@[simp]
theorem pairMap_snd {k : ℕ} (x : Fin (k+2) → ι) (p : Fin (k+2) × Fin (k+1)) :
    (pairMap x p).2 = pairB x (((Tuple.sort x).symm p.1).succAbove p.2) p.1 := rfl

theorem pairMap_read {k : ℕ} (x : Fin (k+2) → ι) (p : Fin (k+2) × Fin (k+1)) :
    readA x (pairMap x p).1 (pairMap x p).2 = p.1 := by
  rw [pairMap_fst, pairMap_snd]
  exact pairB_spec x _ _

/-- The index set of the "non-matched" `dhTerm`s. -/
noncomputable def goodSet {k : ℕ} (x : Fin (k+2) → ι) : Finset (Fin (k+2) × Fin (k+3)) :=
  Finset.univ.filter
    (fun q => ¬ (q.2 = Fin.castSucc q.1 ∨ q.2 = pos2A x q.1))

theorem pairMap_mem_goodSet {k : ℕ} (x : Fin (k+2) → ι) (p : Fin (k+2) × Fin (k+1)) :
    pairMap x p ∈ goodSet x := by
  rw [goodSet, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hcon
  have hne : p.1 ≠ Tuple.sort x (pairMap x p).1 := by
    intro h
    have h1 : (Tuple.sort x).symm p.1 = (pairMap x p).1 := by
      rw [h, Equiv.symm_apply_apply]
    rw [pairMap_fst] at h1
    exact Fin.succAbove_ne ((Tuple.sort x).symm p.1) p.2 h1.symm
  refine hne ?_
  rw [← pairMap_read x p]
  exact ((ReadFib.readAFiber x (pairMap x p).1).1 (pairMap x p).2).mpr hcon

theorem pairMap_inj {k : ℕ} (x : Fin (k+2) → ι) : Function.Injective (pairMap x) := by
  intro p q hpq
  have h1 : (pairMap x p).1 = (pairMap x q).1 := congrArg Prod.fst hpq
  have h2 : (pairMap x p).2 = (pairMap x q).2 := congrArg Prod.snd hpq
  have hc : p.1 = q.1 := by
    rw [← pairMap_read x p, ← pairMap_read x q, h1, h2]
  refine Prod.ext hc ?_
  have hs : ((Tuple.sort x).symm p.1).succAbove p.2
      = ((Tuple.sort x).symm q.1).succAbove q.2 := by
    rw [← pairMap_fst x p, ← pairMap_fst x q]
    exact h1
  rw [hc] at hs
  exact (Fin.strictMono_succAbove ((Tuple.sort x).symm q.1)).injective hs

theorem pairMap_image {k : ℕ} (x : Fin (k+2) → ι) :
    Finset.univ.image (pairMap x) = goodSet x := by
  refine Finset.Subset.antisymm ?_ ?_
  · intro q hq
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hq
    exact pairMap_mem_goodSet x p
  · intro q hq
    rw [goodSet, Finset.mem_filter] at hq
    obtain ⟨-, hqcond⟩ := hq
    set c : Fin (k+2) := readA x q.1 q.2 with hc
    have hcne : c ≠ Tuple.sort x q.1 := by
      intro h
      exact hqcond (((ReadFib.readAFiber x q.1).1 q.2).mp (hc ▸ h))
    have hAne : q.1 ≠ (Tuple.sort x).symm c := by
      intro h
      have h' : Tuple.sort x q.1 = c := by
        rw [h, Equiv.apply_symm_apply]
      exact hcne h'.symm
    obtain ⟨a', ha'⟩ := Fin.exists_succAbove_eq hAne
    refine Finset.mem_image.mpr ⟨(c, a'), Finset.mem_univ _, ?_⟩
    refine Prod.ext ?_ ?_
    · show (pairMap x (c, a')).1 = q.1
      rw [pairMap_fst]
      exact ha'
    · show (pairMap x (c, a')).2 = q.2
      rw [pairMap_snd, ha']
      exact ExistsUnique.unique ((ReadFib.readAFiber x q.1).2 c hcne)
        (pairB_spec x q.1 c) hc.symm

/-! ## The categorical comparison of the two canonical composites -/

section Categorical

variable {X : Type*} [TopologicalSpace X] {A : Type*} [CommRing A]
variable [HasProducts (ModuleCat A)]

/-- The hom-sets of `(Opens X)ᵒᵖ` are subsingletons, so two `P.map`s of morphisms with the same
source and target are equal. -/
theorem thin_map_eq {P : (Opens X)ᵒᵖ ⥤ ModuleCat A} {V W : (Opens X)ᵒᵖ} (f g : V ⟶ W) :
    P.map f = P.map g := by
  rw [Subsingleton.elim f g]

/-- The `hdTerm` composite (before the scalar), at the level of `P`. -/
noncomputable def hdComp (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X) {k : ℕ}
    (x : Fin (k+2) → ι) (c : Fin (k+2)) (a' : Fin (k+1)) :
    allTerm P U (k+1) ⟶ tupleMod P U x :=
  piX P U (k+1) (zA (del x c) a') ≫ resA P U (del x c) a' ≫ resDel P U x c

/-- The `dhTerm` composite (before the scalar), at the level of `P`. -/
noncomputable def dhComp (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X) {k : ℕ}
    (x : Fin (k+2) → ι) (a : Fin (k+2)) (b : Fin (k+3)) :
    allTerm P U (k+1) ⟶ tupleMod P U x :=
  piX P U (k+1) (del (zA x a) b) ≫ resDel P U (zA x a) b ≫ resA P U x a

theorem dhTerm_eq_comp (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X) {k : ℕ}
    (x : Fin (k+2) → ι) (a : Fin (k+2)) (b : Fin (k+3)) :
    dhTerm P U x a b = ((-1 : ℤ) ^ ((a : ℕ) + (b : ℕ)) * signA x a) • dhComp P U x a b := rfl

theorem hdTerm_eq_comp (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X) {k : ℕ}
    (x : Fin (k+2) → ι) (c : Fin (k+2)) (a' : Fin (k+1)) :
    hdTerm P U x c a' = ((-1 : ℤ) ^ ((c : ℕ) + (a' : ℕ)) * signA (del x c) a') •
      hdComp P U x c a' := rfl

/-- The `hdTerm`- and the `dhTerm`-composites at paired indices are equal (the tuple identity of
the pairing). -/
theorem canonical_dh_hd (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X) {k : ℕ}
    (x : Fin (k+2) → ι) (p : Fin (k+2) × Fin (k+1))
    (hidx : (Fin.succAbove p.1) ∘ readA (del x p.1) p.2
        = readA x (Fin.succAbove ((Tuple.sort x).symm p.1) p.2) ∘ (Fin.succAbove (pairMap x p).2)) :
    hdComp P U x p.1 p.2 = dhComp P U x (pairMap x p).1 (pairMap x p).2 := by
  have htup : zA (del x p.1) p.2 = del (zA x (pairMap x p).1) (pairMap x p).2 := by
    funext q
    simp only [zA_apply, del_apply]
    exact congrArg x (congrFun hidx q)
  have hP : P.map ((opZ U (del x p.1) p.2).op ≫ (homOfLE (leOfHom (opDel U x p.1))).op)
      = eqToHom (congrArg (fun u : Fin (k+2) → ι => tupleMod P U u) htup)
        ≫ P.map (((homOfLE (leOfHom (opDel U (zA x (pairMap x p).1) (pairMap x p).2))).op
              ≫ (opZ U x (pairMap x p).1).op)) := by
    rw [← eqToHom_map P (p := congrArg (fun u : Fin (k+2) → ι => op (tupleOp U u)) htup)]
    rw [← P.map_comp]
    exact thin_map_eq _ _
  rw [hdComp, dhComp]
  simp only [piX, resA, resDel]
  rw [← P.map_comp]
  rw [hP, ← Category.assoc,
    Pi.π_comp_eqToHom (f := fun y : Fin (k+2) → ι => tupleMod P U y) htup, ← P.map_comp]

/-- The term-wise cancellation of a `dhTerm` at a paired index against the corresponding
`hdTerm`, from the index identity `hidx` and the sign identity `hsign` of the pairing. -/
theorem pairMap_neg_of {P : (Opens X)ᵒᵖ ⥤ ModuleCat A} {U : ι → Opens X} {k : ℕ}
    (x : Fin (k+2) → ι) (p : Fin (k+2) × Fin (k+1))
    (hidx : (Fin.succAbove p.1) ∘ readA (del x p.1) p.2
        = readA x (Fin.succAbove ((Tuple.sort x).symm p.1) p.2) ∘ (Fin.succAbove (pairMap x p).2))
    (hsign : (-1 : ℤ) ^ ((p.1 : ℕ) + (p.2 : ℕ)) * signA (del x p.1) p.2
        = - ((-1 : ℤ) ^ (((Fin.succAbove ((Tuple.sort x).symm p.1) p.2 : Fin (k+2)) : ℕ)
              + ((pairMap x p).2 : ℕ)) *
            signA x (Fin.succAbove ((Tuple.sort x).symm p.1) p.2))) :
    dhTerm P U x (pairMap x p).1 (pairMap x p).2 = - hdTerm P U x p.1 p.2 := by
  have h1 := dhTerm_eq_comp (P := P) (U := U) (x := x) (a := (pairMap x p).1)
    (b := (pairMap x p).2)
  have h2 := hdTerm_eq_comp (P := P) (U := U) (x := x) (c := p.1) (a' := p.2)
  have h3 := canonical_dh_hd P U x p hidx
  rw [h1, h2, ← h3, pairMap_fst, hsign, neg_smul, neg_neg]

/-! ## The assembly -/

/-- **The "matched" half of the first homotopy identity**: from the term-wise equality
`dhTerm (pairMap x p) = - hdTerm p` for every `p`, the sum of the non-matched `dhTerm`s plus the
sum of all `hdTerm`s vanishes. -/
theorem firstHom_matched_of_neg {k : ℕ} (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X)
    (x : Fin (k+2) → ι)
    (hneg : ∀ p : Fin (k+2) × Fin (k+1),
      dhTerm P U x (pairMap x p).1 (pairMap x p).2 = - hdTerm P U x p.1 p.2) :
    (Finset.univ.sum (fun a : Fin (k+2) => Finset.univ.sum (fun b : Fin (k+3) =>
        if b = Fin.castSucc a ∨ b = pos2A x a then 0 else dhTerm P U x a b)))
      + (Finset.univ.sum (fun c : Fin (k+2) => Finset.univ.sum (fun a' : Fin (k+1) =>
          hdTerm P U x c a'))) = 0 := by
  rw [← Fintype.sum_prod_type'
        (f := fun a b => if b = Fin.castSucc a ∨ b = pos2A x a then 0 else dhTerm P U x a b),
      ← Fintype.sum_prod_type' (f := fun c a' => hdTerm P U x c a')]
  have hT : (∑ q : Fin (k+2) × Fin (k+3),
        (if q.2 = Fin.castSucc q.1 ∨ q.2 = pos2A x q.1 then 0 else dhTerm P U x q.1 q.2))
      = ∑ q ∈ goodSet x, dhTerm P U x q.1 q.2 := by
    rw [goodSet, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    by_cases h : q.2 = Fin.castSucc q.1 ∨ q.2 = pos2A x q.1 <;> simp [h]
  have hsum : (∑ q ∈ goodSet x, dhTerm P U x q.1 q.2)
      = ∑ p : Fin (k+2) × Fin (k+1), dhTerm P U x (pairMap x p).1 (pairMap x p).2 := by
    rw [← pairMap_image x, Finset.sum_image]
    intro p _ q _ hpq
    exact pairMap_inj x hpq
  have hneg' : (∑ p : Fin (k+2) × Fin (k+1),
        dhTerm P U x (pairMap x p).1 (pairMap x p).2)
      = - ∑ p : Fin (k+2) × Fin (k+1), hdTerm P U x p.1 p.2 := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun p _ => hneg p)
  rw [hT, hsum, hneg']
  abel

/-- **The "matched" half of the first homotopy identity**, from the two pairing inputs: the index
identity (`pairing_index`) and the sign identity (`pairing_sign`) for the map `pairMap`. -/
theorem firstHom_matched_of_pairing {k : ℕ} (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X)
    (x : Fin (k+2) → ι)
    (hidx : ∀ (c : Fin (k+2)) (a' : Fin (k+1)) (b : Fin (k+3)),
      readA x (Fin.succAbove ((Tuple.sort x).symm c) a') b = c →
      (Fin.succAbove c) ∘ readA (del x c) a'
        = readA x (Fin.succAbove ((Tuple.sort x).symm c) a') ∘ (Fin.succAbove b))
    (hsign : ∀ (c : Fin (k+2)) (a' : Fin (k+1)) (b : Fin (k+3)),
      readA x (Fin.succAbove ((Tuple.sort x).symm c) a') b = c →
      (-1 : ℤ) ^ ((c : ℕ) + (a' : ℕ)) * signA (del x c) a'
        = - ((-1 : ℤ) ^ (((Fin.succAbove ((Tuple.sort x).symm c) a' : Fin (k+2)) : ℕ)
              + (b : ℕ)) *
            signA x (Fin.succAbove ((Tuple.sort x).symm c) a'))) :
    (Finset.univ.sum (fun a : Fin (k+2) => Finset.univ.sum (fun b : Fin (k+3) =>
        if b = Fin.castSucc a ∨ b = pos2A x a then 0 else dhTerm P U x a b)))
      + (Finset.univ.sum (fun c : Fin (k+2) => Finset.univ.sum (fun a' : Fin (k+1) =>
          hdTerm P U x c a'))) = 0 := by
  refine firstHom_matched_of_neg P U x (fun p => ?_)
  have hb : readA x (Fin.succAbove ((Tuple.sort x).symm p.1) p.2) (pairMap x p).2 = p.1 := by
    rw [← pairMap_fst x p]
    exact pairMap_read x p
  exact pairMap_neg_of x p (hidx p.1 p.2 (pairMap x p).2 hb)
    (hsign p.1 p.2 (pairMap x p).2 hb)

end Categorical

end Work.DSCOH.Norm.FHMatched
