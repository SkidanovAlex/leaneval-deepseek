import Mathlib
import Submission.Work.Peluse.Prop36SW.PeelData
import Submission.Work.Peluse.Prop36SW.pDirEqDir

namespace Work.Peluse.Prop36SW

noncomputable section

open Work.Peluse.UControl

/-!
# The peeled state's hypothesis family is the conclusion's short family

One peel of the §5 chain replaces the state's slot type `ι` by `PeelSlot s₀ = {s // s ≠ s₀}` and its
multiplicity function `kω` by `peelKω kω s₀`.  The hypothesis family of the *new* state is indexed by
`FamIdx (peelKω kω s₀)`, i.e. by the nonempty subsets of the peeled slots, and consists of the
directions

`arithIcc (∑_{s ∈ ω} peelP s q · b s) M₁`,

while the *conclusion* of the ladder (after peeling its long directions, see `conclPeelLongG`)
involves the short family `shortFamG kω p M₁ a b s₀`, indexed by the nonempty subsets of the original
slots avoiding `s₀`.  These are the same family of direction sets: the two index types are identified
by mapping a subset of the peeled slots to its image in the original slots (an injective map), and the
two sums agree because `peelP s q = p s.1.1 q.1.1.1` and the parameters `b` are evaluated at the
corresponding slot.

This module proves that identification (`boxNormPowPeelFamily`), via the index equivalence
`peelIdxSymm` and the pointwise identity `peelIdxSymm_pDirFamG_eq`.
-/

/-- The embedding of the slots of the peeled state into the slots of the original state. -/
def peelSlotEmb {ι : Type} (s₀ : Slot ι (fun _ => 1)) :
    Slot (PeelSlot s₀) (fun _ => 1) ↪ Slot ι (fun _ => 1) where
  toFun := fun x => x.1.1
  inj' := by
    rintro ⟨x1, x2⟩ ⟨y1, y2⟩ h
    have h1 : x1 = y1 := Subtype.ext h
    obtain rfl : x2 = y2 := Subsingleton.elim x2 y2
    rw [h1]

/-- The map on nonempty subsets of the slots induced by the embedding of the peeled slots: a
nonempty subset of the peeled slots is a nonempty subset of the original slots avoiding `s₀`. -/
def peelSetFun {ι : Type} [DecidableEq ι] (s₀ : Slot ι (fun _ => 1)) (ω : SlotSet (PeelSlot s₀) (fun _ => 1)) :
    {t : Finset (Slot ι (fun _ => 1)) // t.Nonempty ∧ s₀ ∉ t} :=
  ⟨ω.1.image (fun x => x.1.1), Finset.image_nonempty.mpr ω.2, by
    intro hmem
    rw [Finset.mem_image] at hmem
    obtain ⟨x, -, hx⟩ := hmem
    exact x.1.2 hx⟩

lemma peelSetFun_injective {ι : Type} [DecidableEq ι] (s₀ : Slot ι (fun _ => 1)) :
    Function.Injective (peelSetFun s₀) := by
  intro ω ω' h
  have h1 : ω.1.image (fun x => x.1.1) = ω'.1.image (fun x => x.1.1) := congrArg Subtype.val h
  exact Subtype.ext (Finset.image_injective (peelSlotEmb s₀).injective h1)

lemma peelSetFun_surjective {ι : Type} [DecidableEq ι] (s₀ : Slot ι (fun _ => 1)) :
    Function.Surjective (peelSetFun s₀) := by
  classical
  rintro ⟨t, ht⟩
  set hf : Set.InjOn (fun x : Slot (PeelSlot s₀) (fun _ => 1) => x.1.1) ((fun x => x.1.1) ⁻¹' ↑t) :=
    fun a _ b _ h => (peelSlotEmb s₀).injective h with hfdef
  refine ⟨⟨t.preimage (fun x => x.1.1) hf, ?_⟩, ?_⟩
  · obtain ⟨y, hy⟩ := ht.1
    refine ⟨⟨⟨y, fun hy0 => ht.2 (hy0 ▸ hy)⟩, 0⟩, ?_⟩
    rw [Finset.mem_preimage]
    exact hy
  · refine Subtype.ext ?_
    show Finset.image (fun x : Slot (PeelSlot s₀) (fun _ => 1) => x.1.1)
      (t.preimage (fun x => x.1.1) hf) = t
    rw [Finset.image_preimage (fun x : Slot (PeelSlot s₀) (fun _ => 1) => x.1.1) t hf]
    exact Finset.filter_true_of_mem (fun x hx =>
      ⟨⟨⟨x, fun hx0 => ht.2 (hx0 ▸ hx)⟩, 0⟩, rfl⟩)

/-- The nonempty subsets of the peeled slots are the nonempty subsets of the original slots
avoiding `s₀`. -/
def peelSetEquiv {ι : Type} [DecidableEq ι] (s₀ : Slot ι (fun _ => 1)) :
    SlotSet (PeelSlot s₀) (fun _ => 1) ≃
      {t : Finset (Slot ι (fun _ => 1)) // t.Nonempty ∧ s₀ ∉ t} :=
  Equiv.ofBijective (peelSetFun s₀) ⟨peelSetFun_injective s₀, peelSetFun_surjective s₀⟩

lemma peelSetEquiv_apply {ι : Type} [DecidableEq ι] (s₀ : Slot ι (fun _ => 1))
    (ω : SlotSet (PeelSlot s₀) (fun _ => 1)) :
    (peelSetEquiv s₀ ω).1 = ω.1.image (fun x => x.1.1) := rfl

lemma peelSetEquiv_symm_image {ι : Type} [DecidableEq ι] (s₀ : Slot ι (fun _ => 1))
    (t : {t : Finset (Slot ι (fun _ => 1)) // t.Nonempty ∧ s₀ ∉ t}) :
    ((peelSetEquiv s₀).symm t).1.image (fun x => x.1.1) = t.1 := by
  have h : ((peelSetEquiv s₀) ((peelSetEquiv s₀).symm t)).1 = t.1 :=
    congrArg Subtype.val (Equiv.apply_symm_apply (peelSetEquiv s₀) t)
  rw [peelSetEquiv_apply] at h
  exact h

/-- The index type of the peeled state's hypothesis family (`FamIdx (peelKω kω s₀)`) is the short
index type of the ladder's conclusion (`ShortIdx kω s₀`).  The `Fin` coordinates are transported
along the identification of the underlying subsets of the slots. -/
def peelIdxSymm {ι : Type} [Fintype ι] [DecidableEq ι] (kω : SlotSet ι (fun _ => 1) → ℕ)
    (s₀ : Slot ι (fun _ => 1)) :
    ShortIdx (k := fun _ : ι => 1) kω s₀ ≃ FamIdx (peelKω kω s₀) :=
  Equiv.sigmaCongr (peelSetEquiv s₀).symm (fun t => finCongr (by
    simp only [peelKω]
    congr 1
    exact Subtype.ext (peelSetEquiv_symm_image s₀ t).symm))

lemma peelIdxSymm_apply_fst {ι : Type} [Fintype ι] [DecidableEq ι]
    (kω : SlotSet ι (fun _ => 1) → ℕ) (s₀ : Slot ι (fun _ => 1))
    (y : ShortIdx (k := fun _ : ι => 1) kω s₀) :
    ((peelIdxSymm kω s₀) y).1 = (peelSetEquiv s₀).symm y.1 := rfl

/-- The peeled state's coefficient function combines with the peeled parameters to reproduce the
original coefficient function on the corresponding slots. -/
lemma pDirG_peelP_eq {ι : Type} [Fintype ι] [DecidableEq ι] {P : Type} 
    [DecidableEq P] (p : ι → P → ℤ) (M₁ M₂ : ℕ) (A : Finset P) (γ' : ℝ) (t' : ℕ)
    (s₀ : Slot ι (fun _ => 1)) (q : PeelParam p M₁ M₂ A γ' t' s₀)
    (ω : SlotSet (PeelSlot s₀) (fun _ => 1)) :
    pDirG (peelP p M₁ M₂ A γ' t' s₀) M₁ q
        (fun s' : Slot (PeelSlot s₀) (fun _ => 1) => q.1.2.1 s'.1.1) ω
      = arithIcc (∑ z ∈ ω.1.image (fun x : Slot (PeelSlot s₀) (fun _ => 1) => x.1.1),
          p z.1 q.1.1.1 * q.1.2.1 z) M₁ := by
  rw [pDirG]
  congr 1
  rw [Finset.sum_image (g := fun x : Slot (PeelSlot s₀) (fun _ => 1) => x.1.1)
    (f := fun z : Slot ι (fun _ => 1) => p z.1 q.1.1.1 * q.1.2.1 z)
    (fun a _ b _ h => (peelSlotEmb s₀).injective h)]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  simp only [peelP]

/-- The short direction family of the conclusion, as a function of the short index type itself (the
unfolding of `shortFamG` along `Fintype.equivFin`). -/
def shortFamRaw {ι : Type} [Fintype ι] [DecidableEq ι] (kω : SlotSet ι (fun _ => 1) → ℕ)
    {P : Type} (p : ι → P → ℤ) (M₁ : ℕ) (a : P) (b : Slot ι (fun _ => 1) → ℤ)
    (s₀ : Slot ι (fun _ => 1)) (y : ShortIdx (k := fun _ : ι => 1) kω s₀) : Finset ℤ :=
  arithIcc (∑ s ∈ y.1.1, p s.1 a * b s) M₁

lemma shortFamG_eq_shortFamRaw {ι : Type} [Fintype ι] [DecidableEq ι]
    (kω : SlotSet ι (fun _ => 1) → ℕ) {P : Type} (p : ι → P → ℤ) (M₁ : ℕ) (a : P)
    (b : Slot ι (fun _ => 1) → ℤ) (s₀ : Slot ι (fun _ => 1))
    (j : Fin (Fintype.card (ShortIdx (k := fun _ : ι => 1) kω s₀))) :
    shortFamG kω p M₁ a b s₀ j
      = shortFamRaw kω p M₁ a b s₀
          ((Fintype.equivFin (ShortIdx (k := fun _ : ι => 1) kω s₀)).symm j) := rfl

/-- **The direction set of the peeled state's family at the index `peelIdxSymm y` is the short
direction set of the conclusion at `y`.** -/
lemma peelIdxSymm_pDirFamG_eq {ι : Type} [Fintype ι] [DecidableEq ι] {P : Type} 
    [DecidableEq P] (kω : SlotSet ι (fun _ => 1) → ℕ) (p : ι → P → ℤ) (M₁ M₂ : ℕ) (A : Finset P)
    (γ' : ℝ) (t' : ℕ) (s₀ : Slot ι (fun _ => 1)) (q : PeelParam p M₁ M₂ A γ' t' s₀)
    (y : ShortIdx (k := fun _ : ι => 1) kω s₀) :
    pDirFamG (peelP p M₁ M₂ A γ' t' s₀) M₁ q
        (fun s' : Slot (PeelSlot s₀) (fun _ => 1) => q.1.2.1 s'.1.1) ((peelIdxSymm kω s₀) y)
      = shortFamRaw kω p M₁ q.1.1.1 q.1.2.1 s₀ y := by
  rcases y with ⟨t, r⟩
  show pDirG (peelP p M₁ M₂ A γ' t' s₀) M₁ q
      (fun s' : Slot (PeelSlot s₀) (fun _ => 1) => q.1.2.1 s'.1.1)
      (((peelIdxSymm kω s₀) ⟨t, r⟩).1) = shortFamRaw kω p M₁ q.1.1.1 q.1.2.1 s₀ ⟨t, r⟩
  rw [peelIdxSymm_apply_fst, pDirG_peelP_eq, peelSetEquiv_symm_image]
  rfl

theorem boxNormPowPeelFamily {ι : Type} [Fintype ι] [DecidableEq ι] {P : Type} 
    [DecidableEq P] (kω : Work.Peluse.UControl.SlotSet ι (fun _ => 1) → ℕ) (p : ι → P → ℤ)
    (M₁ M₂ : ℕ) (A : Finset P) (γ' : ℝ) (t' : ℕ)
    (s₀ : Work.Peluse.UControl.Slot ι (fun _ => 1))
    (q : Work.Peluse.Prop36SW.PeelParam p M₁ M₂ A γ' t' s₀) (S : Finset ℤ) (f : ℤ → ℂ) :
    Work.Peluse.boxNormPow (Fintype.card (Work.Peluse.UControl.FamIdx (Work.Peluse.Prop36SW.peelKω kω s₀)))
        (fun j => Work.Peluse.Prop36SW.pDirFamG (Work.Peluse.Prop36SW.peelP p M₁ M₂ A γ' t' s₀) M₁ q
          (fun s' : Work.Peluse.UControl.Slot (Work.Peluse.Prop36SW.PeelSlot s₀) (fun _ => 1) =>
            q.1.2.1 s'.1.1)
          ((Fintype.equivFin
            (Work.Peluse.UControl.FamIdx (Work.Peluse.Prop36SW.peelKω kω s₀))).symm j)) S f
      = Work.Peluse.boxNormPow
          (Fintype.card (Work.Peluse.Prop36SW.ShortIdx (k := fun _ : ι => 1) kω s₀))
          (Work.Peluse.Prop36SW.shortFamG kω p M₁ q.1.1.1 q.1.2.1 s₀) S f := by
  classical
  have hcard : Fintype.card (FamIdx (peelKω kω s₀))
      = Fintype.card (ShortIdx (k := fun _ : ι => 1) kω s₀) :=
    (Fintype.card_congr (peelIdxSymm kω s₀)).symm
  rw [boxNormPow_family_equiv (φ := (peelIdxSymm kω s₀).symm)
      (Q := fun j => pDirFamG (peelP p M₁ M₂ A γ' t' s₀) M₁ q
        (fun s' : Slot (PeelSlot s₀) (fun _ => 1) => q.1.2.1 s'.1.1) j)
      (e := Fintype.equivFin (FamIdx (peelKω kω s₀)))
      (e' := Fintype.equivFin (ShortIdx (k := fun _ : ι => 1) kω s₀)) hcard S f]
  congr 1
  funext j
  exact peelIdxSymm_pDirFamG_eq kω p M₁ M₂ A γ' t' s₀ q
    ((Fintype.equivFin (ShortIdx (k := fun _ : ι => 1) kω s₀)).symm j)

end

end Work.Peluse.Prop36SW
