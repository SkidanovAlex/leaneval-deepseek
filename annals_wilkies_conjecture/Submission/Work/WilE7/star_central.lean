import Mathlib
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.Prop9
import Submission.Work.WilE7.pad_eval
import Submission.Work.WilE7.pad_set
import Submission.Work.WilE7.pad_proj
import Submission.Work.WilE7.pad_component_proj
import Submission.Work.WilE7.pad_z
import Submission.Work.WilE7.pad_deg
import Submission.Work.WilE7.star_algebra
import Submission.Work.WilE7.star_deg_zero
import Submission.Work.WilE7.cylImage_props
import Submission.Work.WilE7.cylImage_card
import Submission.Work.WilE7.star_proj
import Submission.Work.WilE7.list_filter
import Submission.Work.WilE7.list_sum_tools
import Submission.Work.WilE7.set_glue

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilE7

open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-!
## From BV Proposition 9 to the sharp cell decomposition of `*`-sets

`Work.WilE7.Prop9` (BV Proposition 9) produces, for a *fixed* format bound `F` and a *fixed*
base dimension `n`, one triple `(a, b, c)` working uniformly in the number of sets `k`, in the
fibre dimension `m` and in the degree `D`: a cylindrical decomposition of the cube `[-1,1]^n`
compatible with the projections of all the sets, of size `≤ b(D, k)` and with `*`-bounded cells.

`star_central` is BV Theorem 1 (sharp cell decomposition of `*`-sets) in the form needed by this
development: given a list of `*`-pieces, one decomposition of the cube compatible with every
piece, with the same bounds, the same `a` and the same polynomial `c`.

The proof follows BV, *Proof of Theorem 1*:

* pad each piece to the common ambient fibre dimension `n + F` (admissible: the format bound
  forces `P.m ≤ F`), and apply `Prop9` **in the full space** `ℝ^{n+F}` with fibre dimension `0`;
  this separates the pieces from each other, so that every cell is compatible with each whole
  (padded) set;
* a cell is preconnected (`IsCell` is a graph or a band over a preconnected base, and the cells
  of a cylindrical decomposition are `IsCell`), so a cell is compatible with every *connected
  component* of the padded set as well;
* projecting the decomposition to `ℝ^n` (`cylImage`) preserves compatibility with the projection
  of the component (`cylImage_compat`), and that projection is exactly the `*`-piece
  (`pad_component_proj`).

The only topology input is preconnectedness of a cylindrical cell, proved below (the band over a
preconnected base is preconnected); the argument is the standard "slices are intervals, the
continuity locus is open" one.
-/

/-! ## Bands over a preconnected base -/

/-- The open vertical band `{p : X × ℝ | a p.1 < p.2 < b p.1}`. -/
private def ctBand {X : Type*} (a b : X → EReal) : Set (X × ℝ) :=
  {p | a p.1 < (p.2 : EReal) ∧ (p.2 : EReal) < b p.1}

/-- The vertical slice of the band over `x`. -/
private def ctSlice {X : Type*} (x : X) (a b : X → EReal) : Set (X × ℝ) :=
  {p | p.1 = x ∧ a x < (p.2 : EReal) ∧ (p.2 : EReal) < b x}

/-- The base points whose slice meets the open set `u`. -/
private def ctBase {X : Type*} (a b : X → EReal) (u : Set (X × ℝ)) : Set X :=
  {x | ∃ y : ℝ, a x < (y : EReal) ∧ (y : EReal) < b x ∧ (x, y) ∈ u}

private lemma ctSlice_eq_prod {X : Type*} (a b : X → EReal) (x : X) :
    ctSlice x a b = ({x} : Set X) ×ˢ {y : ℝ | a x < (y : EReal) ∧ (y : EReal) < b x} := by
  ext p
  simp only [ctSlice, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_singleton_iff]

private lemma ctSlice_subset {X : Type*} (a b : X → EReal) (x : X) :
    ctSlice x a b ⊆ ctBand a b := by
  intro p hp
  simp only [ctSlice, Set.mem_ofPred_eq] at hp
  simp only [ctBand, Set.mem_ofPred_eq]
  rw [hp.1]
  exact ⟨hp.2.1, hp.2.2⟩

/-- Every slice of the band is preconnected (an interval in the vertical direction). -/
private lemma isPreconnected_ctSlice {X : Type*} [TopologicalSpace X] (a b : X → EReal) (x : X) :
    IsPreconnected (ctSlice x a b) := by
  rw [ctSlice_eq_prod]
  refine IsPreconnected.prod isPreconnected_singleton ?_
  rw [isPreconnected_iff_ordConnected, Set.ordConnected_iff]
  intro y₁ hy₁ y₂ hy₂ _ z hz
  simp only [Set.mem_ofPred_eq, Set.mem_Icc] at hy₁ hy₂ hz ⊢
  exact ⟨hy₁.1.trans_le (EReal.coe_le_coe hz.1), (EReal.coe_le_coe hz.2).trans_lt hy₂.2⟩

/-- The base points whose slice meets an open set form an open set. -/
private lemma isOpen_ctBase {X : Type*} [TopologicalSpace X] {a b : X → EReal}
    (ha : Continuous a) (hb : Continuous b) {u : Set (X × ℝ)} (hu : IsOpen u) :
    IsOpen (ctBase a b u) := by
  have heq : ctBase a b u
      = ⋃ y : ℝ, (a ⁻¹' Set.Iio (y : EReal)) ∩ (b ⁻¹' Set.Ioi (y : EReal)) ∩
          ((fun x : X => (x, y)) ⁻¹' u) := by
    ext x
    simp only [ctBase, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_preimage]
    exact ⟨fun ⟨y, h1, h2, h3⟩ => ⟨y, ⟨⟨h1, h2⟩, h3⟩⟩,
      fun ⟨y, ⟨⟨h1, h2⟩, h3⟩⟩ => ⟨y, h1, h2, h3⟩⟩
  rw [heq]
  refine isOpen_iUnion fun y => ?_
  exact ((ha.isOpen_preimage _ (isOpen_Iio' _)).inter
    (hb.isOpen_preimage _ (isOpen_Ioi' _))).inter
    ((continuous_id.prodMk continuous_const).isOpen_preimage _ hu)

/-- The band over a preconnected space is preconnected. -/
private theorem isPreconnected_ctBand {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {a b : X → EReal} (ha : Continuous a) (hb : Continuous b) (hab : ∀ x, a x < b x) :
    IsPreconnected (ctBand a b) := by
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hsub hdisj
  have hdich : ∀ x : X, ctSlice x a b ⊆ u ∨ ctSlice x a b ⊆ v := by
    intro x
    refine isPreconnected_iff_subset_of_disjoint.mp (isPreconnected_ctSlice a b x) u v hu hv
      ((ctSlice_subset a b x).trans hsub) ?_
    rw [← Set.disjoint_iff_inter_eq_empty]
    exact (Set.disjoint_iff_inter_eq_empty.mpr hdisj).mono_left (ctSlice_subset a b x)
  have hP : IsOpen (ctBase a b u) := isOpen_ctBase ha hb hu
  have hQ : IsOpen (ctBase a b v) := isOpen_ctBase ha hb hv
  have hcover : (Set.univ : Set X) ⊆ ctBase a b u ∪ ctBase a b v := by
    intro x _
    obtain ⟨y, h1, h2⟩ := EReal.exists_between_coe_real (hab x)
    rcases hsub (show (x, y) ∈ ctBand a b from ⟨h1, h2⟩) with h | h
    · exact Or.inl ⟨y, h1, h2, h⟩
    · exact Or.inr ⟨y, h1, h2, h⟩
  have hdisjPQ : (Set.univ : Set X) ∩ (ctBase a b u ∩ ctBase a b v) = ∅ := by
    rw [Set.univ_inter, ← Set.not_nonempty_iff_eq_empty]
    rintro ⟨x, hxP, hxQ⟩
    simp only [ctBase, Set.mem_ofPred_eq] at hxP hxQ
    obtain ⟨y₁, ha₁, hb₁, hu₁⟩ := hxP
    obtain ⟨y₂, ha₂, hb₂, hv₂⟩ := hxQ
    rcases hdich x with h | h
    · have hmem : (x, y₂) ∈ ctBand a b ∩ (u ∩ v) :=
        ⟨⟨ha₂, hb₂⟩, h ⟨rfl, ha₂, hb₂⟩, hv₂⟩
      rw [hdisj] at hmem
      exact hmem
    · have hmem : (x, y₁) ∈ ctBand a b ∩ (u ∩ v) :=
        ⟨⟨ha₁, hb₁⟩, hu₁, h ⟨rfl, ha₁, hb₁⟩⟩
      rw [hdisj] at hmem
      exact hmem
  rcases isPreconnected_iff_subset_of_disjoint.mp
      (isPreconnected_univ : IsPreconnected (Set.univ : Set X))
      (ctBase a b u) (ctBase a b v) hP hQ hcover hdisjPQ with hUP | hUQ
  · left
    intro p hp
    simp only [ctBand, Set.mem_ofPred_eq] at hp
    have hxP : p.1 ∈ ctBase a b u := hUP (Set.mem_univ p.1)
    simp only [ctBase, Set.mem_ofPred_eq] at hxP
    obtain ⟨y, hay, hyb, hxy⟩ := hxP
    rcases hdich p.1 with hh | hh
    · exact hh ⟨rfl, hp.1, hp.2⟩
    · exfalso
      have hmem : (p.1, y) ∈ ctBand a b ∩ (u ∩ v) :=
        ⟨⟨hay, hyb⟩, hxy, hh ⟨rfl, hay, hyb⟩⟩
      rw [hdisj] at hmem
      exact hmem
  · right
    intro p hp
    simp only [ctBand, Set.mem_ofPred_eq] at hp
    have hxQ : p.1 ∈ ctBase a b v := hUQ (Set.mem_univ p.1)
    simp only [ctBase, Set.mem_ofPred_eq] at hxQ
    obtain ⟨y, hay, hyb, hxy⟩ := hxQ
    rcases hdich p.1 with hh | hh
    · exfalso
      have hmem : (p.1, y) ∈ ctBand a b ∩ (u ∩ v) :=
        ⟨⟨hay, hyb⟩, hh ⟨rfl, hay, hyb⟩, hxy⟩
      rw [hdisj] at hmem
      exact hmem
    · exact hh ⟨rfl, hp.1, hp.2⟩

/-- The band between two continuous `EReal`-valued functions over a preconnected base is
preconnected. -/
private theorem isPreconnected_bandOf {α : Type*} [TopologicalSpace α] {C : Set α}
    (hC : IsPreconnected C) {a b : α → EReal} (ha : ContinuousOn a C) (hb : ContinuousOn b C)
    (hab : ∀ x ∈ C, a x < b x) :
    IsPreconnected {p : α × ℝ | p.1 ∈ C ∧ a p.1 < (p.2 : EReal) ∧ (p.2 : EReal) < b p.1} := by
  haveI : PreconnectedSpace C := isPreconnected_iff_preconnectedSpace.mp hC
  have ha' : Continuous (fun x : C => a x.1) :=
    ha.comp_continuous continuous_subtype_val (fun x => x.2)
  have hb' : Continuous (fun x : C => b x.1) :=
    hb.comp_continuous continuous_subtype_val (fun x => x.2)
  have hcore : IsPreconnected (ctBand (fun x : C => a x.1) (fun x : C => b x.1)) :=
    isPreconnected_ctBand ha' hb' (fun x => hab x.1 x.2)
  have hcont : ContinuousOn (fun p : C × ℝ => (p.1.1, p.2))
      (ctBand (fun x : C => a x.1) (fun x : C => b x.1)) :=
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).continuousOn
  have himg := hcore.image (fun p : C × ℝ => (p.1.1, p.2)) hcont
  have heq : (fun p : C × ℝ => (p.1.1, p.2)) ''
        ctBand (fun x : C => a x.1) (fun x : C => b x.1)
      = {p : α × ℝ | p.1 ∈ C ∧ a p.1 < (p.2 : EReal) ∧ (p.2 : EReal) < b p.1} := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      simp only [ctBand, Set.mem_ofPred_eq] at hq
      exact ⟨q.1.2, hq.1, hq.2⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨(⟨p.1, h1⟩, p.2), by
        simp only [ctBand, Set.mem_ofPred_eq]
        exact ⟨h2, h3⟩, rfl⟩
  rw [heq] at himg
  exact himg

/-! ## Preconnectedness of cylindrical cells -/

/-- A graph cell over a preconnected base is preconnected: it is the image of the base under the
continuous map `x ↦ Fin.snoc x (f x)`. -/
private lemma isPreconnected_graphCell {n : ℕ} {C : Set (Fin n → ℝ)} (hC : IsPreconnected C)
    (f : (Fin n → ℝ) → ℝ) (hf : ContinuousOn f C) :
    IsPreconnected {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧ z (Fin.last n) = f (Fin.init z)} := by
  have hcont : ContinuousOn (fun x : Fin n → ℝ => (Fin.snoc x (f x) : Fin (n + 1) → ℝ)) C := by
    intro x hx
    exact (continuous_id.continuousWithinAt).finSnoc (hf x hx)
  have hset : {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧ z (Fin.last n) = f (Fin.init z)}
      = (fun x : Fin n → ℝ => (Fin.snoc x (f x) : Fin (n + 1) → ℝ)) '' C := by
    ext z
    constructor
    · intro hz
      refine ⟨Fin.init z, hz.1, ?_⟩
      show Fin.snoc (Fin.init z) (f (Fin.init z)) = z
      rw [← hz.2]
      exact Fin.snoc_init_self z
    · rintro ⟨x, hx, rfl⟩
      exact ⟨by simpa using hx, by simp⟩
  rw [hset]
  exact hC.image _ hcont

/-- A band cell over a preconnected base is preconnected: it is the image of the band under the
continuous map `p ↦ Fin.snoc p.1 p.2`. -/
private lemma isPreconnected_bandCell {n : ℕ} {C : Set (Fin n → ℝ)} (hC : IsPreconnected C)
    (a b : (Fin n → ℝ) → EReal) (ha : ContinuousOn a C) (hb : ContinuousOn b C)
    (hab : ∀ x ∈ C, a x < b x) :
    IsPreconnected {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧
        a (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
        ((z (Fin.last n) : ℝ) : EReal) < b (Fin.init z)} := by
  have hband : IsPreconnected
      {p : (Fin n → ℝ) × ℝ | p.1 ∈ C ∧ a p.1 < (p.2 : EReal) ∧ (p.2 : EReal) < b p.1} :=
    isPreconnected_bandOf hC ha hb hab
  have hcont : ContinuousOn
      (fun p : (Fin n → ℝ) × ℝ => (Fin.snoc p.1 p.2 : Fin (n + 1) → ℝ))
      {p : (Fin n → ℝ) × ℝ | p.1 ∈ C ∧ a p.1 < (p.2 : EReal) ∧ (p.2 : EReal) < b p.1} :=
    ((Continuous.finSnoc (A := fun _ : Fin (n + 1) => ℝ) continuous_fst
      continuous_snd)).continuousOn
  have hset : {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧
        a (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
        ((z (Fin.last n) : ℝ) : EReal) < b (Fin.init z)}
      = (fun p : (Fin n → ℝ) × ℝ => (Fin.snoc p.1 p.2 : Fin (n + 1) → ℝ)) ''
          {p : (Fin n → ℝ) × ℝ | p.1 ∈ C ∧ a p.1 < (p.2 : EReal) ∧ (p.2 : EReal) < b p.1} := by
    ext z
    constructor
    · intro hz
      refine ⟨(Fin.init z, z (Fin.last n)), hz, ?_⟩
      exact Fin.snoc_init_self z
    · rintro ⟨p, hp, rfl⟩
      simpa [Fin.init_snoc, Fin.snoc_last] using hp
  rw [hset]
  exact hband.image _ hcont

/-- A cylindrical cell is preconnected: `univ ⊆ ℝ⁰` is a subsingleton, a graph cell is the image
of its base under a continuous map, and a band cell is handled by `isPreconnected_bandOf`. -/
theorem isPreconnected_of_isCell : ∀ {n : ℕ} {c : Set (Fin n → ℝ)}, IsCell n c →
    IsPreconnected c := by
  intro n c h
  induction h with
  | zero => exact isPreconnected_univ
  | graph hC f hf ih => exact isPreconnected_graphCell ih f hf
  | band hC a b ha hb hab ih => exact isPreconnected_bandCell ih a b ha hb hab

/-- The cells of a cylindrical decomposition are preconnected. -/
theorem isPreconnected_of_mem_isCylDecompOn : ∀ {n : ℕ} {A : Set (Fin n → ℝ)}
    {C : Finset (Set (Fin n → ℝ))}, IsCylDecompOn n A C → ∀ c ∈ C, IsPreconnected c := by
  intro n
  induction n with
  | zero =>
      intro A C h c hc
      rcases h with ⟨hA, hC⟩ | ⟨hA, hC⟩
      · subst hC
        rw [Finset.mem_singleton] at hc
        rw [hc]
        exact isPreconnected_univ
      · subst hC
        exact absurd hc (Finset.notMem_empty c)
  | succ n ih =>
      intro A C h c hc
      exact isPreconnected_of_isCell (h.1 c hc).1

/-! ## The main statement -/

theorem star_central (h9 : Work.WilE7.Prop9) (F n : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : Polynomial ℕ),
      ∀ (D : ℕ) (L : List (WilkiesDesign.E.StarPiece n)),
        (∀ P ∈ L, P.X.fmt ≤ F) → (∀ P ∈ L, P.X.deg ≤ D) →
        ∃ C : Finset (Set (Fin n → ℝ)),
          WilkiesDesign.E.IsCylDecompOn n (WilkiesDesign.E.cubeC n) C ∧
          (∀ P ∈ L, ∀ κ ∈ C, κ ⊆ P.set ∨ Disjoint κ P.set) ∧
          C.card ≤ MvPolynomial.eval ![D, L.length] b ∧
          ∀ κ ∈ C, WilkiesDesign.E.Star a (c.eval D) n κ := by
  -- `Prop9` at format `n + 2F` and base dimension `n + F`, with fibre dimension `0`.
  obtain ⟨a0, b0, c0, h0⟩ := h9 (n + 2 * F) (n + F)
  refine ⟨a0, b0, c0, ?_⟩
  intro D L hfmt hdeg
  -- The format bound forces the fibre dimension of each piece to be `≤ F`.
  have hmmF : ∀ i : Fin L.length, (L.get i).m ≤ F := by
    intro i
    have h := hfmt (L.get i) (List.get_mem L i)
    have h' : (n + (L.get i).m) + (L.get i).X.r ≤ F := h
    omega
  -- The family of padded pieces, in `ℝ^{(n+F)+0}`.
  let X : Fin L.length → SemiPf (n + F) :=
    fun i => SemiPf.pad (Nat.add_le_add_left (hmmF i) n) (L.get i).X
  have hbound : ∀ i, (X i).fmt ≤ n + 2 * F ∧ (X i).deg ≤ D := by
    intro i
    have hr : (L.get i).X.r ≤ F := by
      have h := hfmt (L.get i) (List.get_mem L i)
      have h' : (n + (L.get i).m) + (L.get i).X.r ≤ F := h
      omega
    refine ⟨?_, ?_⟩
    · show (n + F) + (L.get i).X.r ≤ n + 2 * F
      omega
    · show (SemiPf.pad (Nat.add_le_add_left (hmmF i) n) (L.get i).X).deg ≤ D
      exact le_trans (pad_deg.2.2 (Nat.add_le_add_left (hmmF i) n) (L.get i).X)
        (hdeg (L.get i) (List.get_mem L i))
  obtain ⟨C', hC'decomp, hC'compat, hC'card, hC'star⟩ := h0 D L.length 0 X hbound
  -- Project the decomposition of `ℝ^{n+F}` to `ℝ^n`.
  refine ⟨cylImage n F C', ?_, ?_, ?_, ?_⟩
  · exact cylImage_props.1 hC'decomp
  · -- Compatibility with the projection of the component of each piece.
    intro P hP κ hκ
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hP
    subst P
    have hcomp := (pad_component_proj (n := n) (m := (L.get i).m) (M := F)
      (hmmF i) (L.get i).X (L.get i).p).2
    have hYset : projFirst n F '' connectedComponentIn (X i).set (padZ (n + F) (L.get i).p)
        = (L.get i).set := by
      show projFirst n F '' connectedComponentIn
          (SemiPf.pad (Nat.add_le_add_left (hmmF i) n) (L.get i).X).set
            (padZ (n + F) (L.get i).p)
        = projFirst n (L.get i).m '' connectedComponentIn (L.get i).X.set (L.get i).p
      exact hcomp
    have hYcube : connectedComponentIn (X i).set (padZ (n + F) (L.get i).p) ⊆ cubeC (n + F) :=
      fun y hy => Work.WilE8.SemiPf.set_subset_cube (X i) (connectedComponentIn_subset _ _ hy)
    have hYcompat : ∀ c ∈ C', c ⊆ connectedComponentIn (X i).set (padZ (n + F) (L.get i).p)
        ∨ Disjoint c (connectedComponentIn (X i).set (padZ (n + F) (L.get i).p)) := by
      intro c hc
      rcases hC'compat i c hc with hsub | hdisj
      · rw [projFirst_zero_image] at hsub
        exact set_glue.2.1 (isPreconnected_of_mem_isCylDecompOn hC'decomp c hc) hsub
      · rw [projFirst_zero_image] at hdisj
        exact Or.inr (hdisj.mono_right (connectedComponentIn_subset _ _))
    have hkey := cylImage_compat n F hC'decomp hYcube hYcompat κ hκ
    rw [hYset] at hkey
    exact hkey
  · exact le_trans (cylImage_card C') hC'card
  · intro κ hκ
    obtain ⟨c, hc, hcκ⟩ := (cylImage_props.2.2 (C := C') (κ := κ)).mp hκ
    rw [← hcκ]
    exact star_proj.2 (hC'star c hc).1

end Work.WilE7
