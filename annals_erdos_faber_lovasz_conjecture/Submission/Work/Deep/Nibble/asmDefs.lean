import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.AsmBase

/-!
# The state of the §7 assembly step

This module fixes the vocabulary that the §7 assembly step (`asmStep`) uses:
the *remaining reservoir* `RcurOf` and the *remaining defect set* `ScurOf` of the
paper's induction (efl.tex:1793), and the enumeration `blockEquiv` of a block of
colours `I k` by `Fin (I k).card` together with the reindexed seed family
`blockSeed`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

local notation "Hypergraph" => ErdosFaberLovaszConjecture.Hypergraph

noncomputable section

variable {n D K : ℕ}

/-- The cone's hypergraph type on `Fin n`, as an abbreviation. -/
abbrev Hyp (n : ℕ) := ErdosFaberLovaszConjecture.Hypergraph (Fin n)

/-- **The remaining reservoir** after the colours of `Proc I j` have been served:
the paper's `R_i = R ∖ ⋃_{k<i} ⋃_{N ∈ 𝓝_k} N`. -/
def RcurOf (R : Hypergraph (Fin n)) (I : Fin K → Finset (Fin D))
    (Nf : Fin D → Set (Set (Fin n))) (j : ℕ) : Hypergraph (Fin n) :=
  R \ (⋃ c ∈ Proc I j, Nf c)

/-- **The remaining defect set** after the colours of `Proc I j` have been
served: the paper's `S_i = S ∖ ⋃_{k<i} ⋃_{N ∈ 𝓝_k} (U ∖ V(N))`. -/
def ScurOf (S U : Set (Fin n)) (I : Fin K → Finset (Fin D))
    (Nf : Fin D → Set (Set (Fin n))) (j : ℕ) : Set (Fin n) :=
  S \ (⋃ c ∈ Proc I j, (U \ famVert (Nf c)))

theorem mem_RcurOf {R : Hypergraph (Fin n)} {I : Fin K → Finset (Fin D)}
    {Nf : Fin D → Set (Set (Fin n))} {j : ℕ} {e : Set (Fin n)} :
    e ∈ RcurOf R I Nf j ↔ e ∈ R ∧ ∀ c ∈ Proc I j, e ∉ Nf c := by
  classical
  simp only [RcurOf, Set.mem_sdiff, Set.mem_iUnion, exists_prop, not_exists, not_and]

theorem mem_ScurOf {S U : Set (Fin n)} {I : Fin K → Finset (Fin D)}
    {Nf : Fin D → Set (Set (Fin n))} {j : ℕ} {v : Fin n} :
    v ∈ ScurOf S U I Nf j ↔ v ∈ S ∧ ∀ c ∈ Proc I j, v ∉ U \ famVert (Nf c) := by
  classical
  simp only [ScurOf, Set.mem_sdiff, Set.mem_iUnion, exists_prop, not_exists, not_and]

/-- A proper edge `e` of `𝓜`, as an edge object. -/
def propObj (𝓜 : MultiHypergraph n) (e : Set (Fin n)) (he : e ∈ 𝓜.edges) : EdgeObj 𝓜 :=
  Sum.inl ⟨e, he⟩

@[simp]
theorem propObj_toSet (𝓜 : MultiHypergraph n) (e : Set (Fin n)) (he : e ∈ 𝓜.edges) :
    EdgeObj.toSet (propObj 𝓜 e he) = e := rfl

/-- The `k`-th copy of the singleton edge `{w}` of `𝓜`, as an edge object. -/
def copyObj (𝓜 : MultiHypergraph n) (w : Fin n) (k : Fin (𝓜.singles w)) : EdgeObj 𝓜 :=
  Sum.inr ⟨(w, (k : ℕ)), k.2⟩

@[simp]
theorem copyObj_toSet (𝓜 : MultiHypergraph n) (w : Fin n) (k : Fin (𝓜.singles w)) :
    EdgeObj.toSet (copyObj 𝓜 w k) = ({w} : Set (Fin n)) := by
  simp [copyObj]

theorem copyObj_injective (𝓜 : MultiHypergraph n) (w : Fin n) :
    Function.Injective (copyObj 𝓜 w) := by
  intro k k' h
  have h' : (⟨(w, (k : ℕ)), k.2⟩ : {p : Fin n × ℕ // p.2 < 𝓜.singles p.1})
      = ⟨(w, (k' : ℕ)), k'.2⟩ := Sum.inr.inj h
  exact Fin.ext (by simpa using congrArg (fun p => p.1.2) h')

theorem RcurOf_subset (R : Hypergraph (Fin n)) (I : Fin K → Finset (Fin D))
    (Nf : Fin D → Set (Set (Fin n))) (j : ℕ) : RcurOf R I Nf j ⊆ R :=
  Set.sdiff_subset

theorem ScurOf_subset (S U : Set (Fin n)) (I : Fin K → Finset (Fin D))
    (Nf : Fin D → Set (Set (Fin n))) (j : ℕ) : ScurOf S U I Nf j ⊆ S :=
  Set.sdiff_subset

/-- The enumeration of the block `I k` of colours by `Fin (I k).card`. -/
def blockEquiv (I : Fin K → Finset (Fin D)) (k : Fin K) :
    Fin (I k).card ≃ ↥(I k) :=
  (Finset.equivFin (I k)).symm

theorem blockEquiv_mem (I : Fin K → Finset (Fin D)) (k : Fin K) (i : Fin (I k).card) :
    ((blockEquiv I k i : ↥(I k)) : Fin D) ∈ I k := (blockEquiv I k i).2

/-- The `i`-th colour of the block `I k`. -/
def blockColour (I : Fin K → Finset (Fin D)) (k : Fin K) (i : Fin (I k).card) : Fin D :=
  ((blockEquiv I k i : ↥(I k)) : Fin D)

theorem blockColour_mem (I : Fin K → Finset (Fin D)) (k : Fin K) (i : Fin (I k).card) :
    blockColour I k i ∈ I k := (blockEquiv I k i).2

theorem blockColour_eq_symm {I : Fin K → Finset (Fin D)} {k : Fin K} {c : Fin D}
    (hc : c ∈ I k) : blockColour I k ((blockEquiv I k).symm ⟨c, hc⟩) = c := by
  simp [blockColour]

theorem blockColour_injective (I : Fin K → Finset (Fin D)) (k : Fin K) :
    Function.Injective (blockColour I k) := by
  intro i i' h
  have h' : (blockEquiv I k i : ↥(I k)) = (blockEquiv I k i' : ↥(I k)) := Subtype.ext h
  exact (blockEquiv I k).injective h'

theorem exists_blockColour {I : Fin K → Finset (Fin D)} {k : Fin K} {c : Fin D}
    (hc : c ∈ I k) : ∃ i : Fin (I k).card, blockColour I k i = c := by
  obtain ⟨i, hi⟩ := (blockEquiv I k).surjective ⟨c, hc⟩
  exact ⟨i, congrArg (fun x : ↥(I k) => (x : Fin D)) hi⟩


/-- **The new family of colour classes** after the part `I k` has been served:
the colours of `I k` receive the absorbed matchings `Nabs`, all others keep
their old matchings `Nf`. -/
def extend (Nf : Fin D → Set (Set (Fin n))) (I : Fin K → Finset (Fin D)) (k : Fin K)
    (Nabs : Fin (I k).card → Set (Set (Fin n))) : Fin D → Set (Set (Fin n)) :=
  fun c => if h : c ∈ I k then Nabs ((blockEquiv I k).symm ⟨c, h⟩) else Nf c

theorem extend_of_mem {Nf : Fin D → Set (Set (Fin n))} {I : Fin K → Finset (Fin D)}
    {k : Fin K} {Nabs : Fin (I k).card → Set (Set (Fin n))} {c : Fin D} (hc : c ∈ I k) :
    extend Nf I k Nabs c = Nabs ((blockEquiv I k).symm ⟨c, hc⟩) := dif_pos hc

theorem extend_of_not_mem {Nf : Fin D → Set (Set (Fin n))} {I : Fin K → Finset (Fin D)}
    {k : Fin K} {Nabs : Fin (I k).card → Set (Set (Fin n))} {c : Fin D} (hc : c ∉ I k) :
    extend Nf I k Nabs c = Nf c := dif_neg hc

theorem extend_blockColour {Nf : Fin D → Set (Set (Fin n))} {I : Fin K → Finset (Fin D)}
    {k : Fin K} (Nabs : Fin (I k).card → Set (Set (Fin n))) (i : Fin (I k).card) :
    extend Nf I k Nabs (blockColour I k i) = Nabs i := by
  rw [extend_of_mem (blockColour_mem I k i)]
  congr 1
  exact (blockEquiv I k).symm_apply_apply i

theorem extend_apply_symm {Nf : Fin D → Set (Set (Fin n))} {I : Fin K → Finset (Fin D)}
    {k : Fin K} {Nabs : Fin (I k).card → Set (Set (Fin n))} {c : Fin D} (hc : c ∈ I k) :
    extend Nf I k Nabs c = Nabs ((blockEquiv I k).symm ⟨c, hc⟩) := dif_pos hc

/-- The seeds of the block, reindexed by `Fin (I k).card`. -/
def blockSeed (I : Fin K → Finset (Fin D)) (M : Fin D → Set (Set (Fin n)))
    (k : Fin K) : Fin (I k).card → Set (Set (Fin n)) :=
  fun i => M (blockColour I k i)

theorem blockSeed_apply (I : Fin K → Finset (Fin D)) (M : Fin D → Set (Set (Fin n)))
    (k : Fin K) (i : Fin (I k).card) : blockSeed I M k i = M (blockColour I k i) := rfl

@[simp]
theorem RcurOf_zero (R : Hypergraph (Fin n)) (I : Fin K → Finset (Fin D))
    (Nf : Fin D → Set (Set (Fin n))) : RcurOf R I Nf 0 = R := by
  simp [RcurOf, Proc]

@[simp]
theorem ScurOf_zero (S U : Set (Fin n)) (I : Fin K → Finset (Fin D))
    (Nf : Fin D → Set (Set (Fin n))) : ScurOf S U I Nf 0 = S := by
  simp [ScurOf, Proc]

end

end Work.Deep.Nibble
