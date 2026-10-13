/-
  WilG1 / Cell / generic_continuity.

  Rudimentary generic continuity for the frozen sharply o-minimal structure `SOMin`:
  if the graph of `f : ℝⁿ → ℝ` is an `Ω`-set, then the set of points at which `f` is
  discontinuous has empty interior.

  Proof outline.  Let `C` be the sharp cell decomposition of `ℝⁿ⁺¹` adapted to the single set
  `graphOf f` (`S.SharpCD`).  For a cell `κ ∈ C`:

  * either `κ` is disjoint from `graphOf f`; or
  * `κ ⊆ graphOf f`, in which case `κ` cannot be a *band* cell (a band contains two points with
    the same first `n` coordinates, and `graphOf f` meets each vertical line at most once), so
    `κ` is a *graph* cell, `κ = {z | Fin.init z ∈ D ∧ z (Fin.last n) = g (Fin.init z)}` with
    `g` continuous on the base cell `D`, and `f = g` on `D = projLast κ`.

  Consequently `f` is continuous on `projLast κ` for every cell `κ` meeting `graphOf f`, and in
  particular the discontinuity set of `f` is contained in

    `⋃ {projLast κ \ interior (projLast κ) : κ ∈ C}`.

  Each member of this union is an `Ω`-set (projection, interior, complement, intersection) with
  uniform format/degree bounds and has empty interior (`interior (s \ interior s) = ∅`).

  The last ingredient is that a finite union of thin `Ω`-sets is thin (`gc_thin_union_finset`).
  The refinement by a sharp cylindrical decomposition turns every thin set into a union of thin
  *cells*; a thin cell is nowhere dense (graph cells are graphs of continuous functions, band
  cells with a thin base have thin closure), and a finite union of nowhere dense sets is nowhere
  dense.  That cell lemma, together with the relevant `Fin.snoc`/`Fin.init` bookkeeping, is
  self-contained here (`gc_cell_isNowhereDense_of_thin` and the `gc_`-prefixed lemmas around
  it) so that this file depends only on the frozen definitions, the `Ω`-calculus of
  `Work.WilG1.Basic` / `Work.WilG1.Calc.interior_mem`, and Mathlib.
-/
import Mathlib
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.Calc.interior_mem
import Submission.Work.WilG1.Cell.isNowhereDense_graph

set_option autoImplicit false
noncomputable section

open Classical
open scoped Topology

namespace Work.WilG1.Cell

open WilkiesDesign WilkiesConjecture

/-! ## Bookkeeping for `Fin.snoc` on `ℝⁿ` -/

/-- `Fin.snoc` with the codomain pinned to `ℝ`, avoiding dependent-type inference issues. -/
abbrev snocR {n : ℕ} (p : Fin n → ℝ) (x : ℝ) : Fin (n + 1) → ℝ := Fin.snoc p x

@[simp] theorem snocR_castSucc {n : ℕ} (p : Fin n → ℝ) (x : ℝ) (i : Fin n) :
    snocR p x (Fin.castSucc i) = p i := Fin.snoc_castSucc _ _ _

@[simp] theorem snocR_last {n : ℕ} (p : Fin n → ℝ) (x : ℝ) : snocR p x (Fin.last n) = x :=
  Fin.snoc_last _ _

theorem init_snocR {n : ℕ} (p : Fin n → ℝ) (x : ℝ) : Fin.init (snocR p x) = p :=
  Fin.init_snoc (α := fun _ => ℝ) x p

theorem snocR_init_self {n : ℕ} (q : Fin (n + 1) → ℝ) :
    snocR (Fin.init q) (q (Fin.last n)) = q :=
  Fin.snoc_init_self q

/-- `projLast` drops the last coordinate, i.e. it is the image under `Fin.init`. -/
theorem projLast_eq_image {n : ℕ} (A : Set (Fin (n + 1) → ℝ)) :
    projLast A = Fin.init '' A := by
  ext x; constructor
  · rintro ⟨t, ht⟩; exact ⟨snocR x t, ht, init_snocR x t⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z (Fin.last n), by rw [Fin.snoc_init_self]; exact hz⟩

/-! ## The graph representation of a cell contained in a graph -/

/-- **A cell contained in the graph of a function is a graph cell**, and the function agrees
with `f` on the base cell.  Concretely: if `κ` is a cell of `ℝⁿ⁺¹` contained in `graphOf f`,
then `f` is continuous on `projLast κ`.

The content is that a *band* cell over a nonempty base contains two points with the same first
`n` coordinates, whereas `graphOf f` meets each such vertical line at most once.  `IsCell`'s
`zero` constructor cannot produce a subset of `ℝⁿ⁺¹` with `n + 1 ≥ 1`. -/
theorem continuousOn_of_isCell_subset_graphOf {n : ℕ} {κ : Set (Fin (n + 1) → ℝ)}
    {f : (Fin n → ℝ) → ℝ} (h : IsCell (n + 1) κ) (hsub : κ ⊆ graphOf f) :
    ContinuousOn f (projLast κ) := by
  cases h with
  | graph hC g hg =>
      rename_i C
      have hproj : projLast
          {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧ z (Fin.last n) = g (Fin.init z)} = C := by
        ext x; constructor
        · rintro ⟨t, ht⟩
          simp only [Set.mem_ofPred_eq, init_snocR] at ht
          exact ht.1
        · intro hx
          refine ⟨g x, ?_⟩
          simp only [Set.mem_ofPred_eq, init_snocR, snocR_last]
          exact ⟨hx, trivial⟩
      have hfg : ∀ x ∈ C, f x = g x := by
        intro x hx
        have hmem : snocR x (g x) ∈
            {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧ z (Fin.last n) = g (Fin.init z)} := by
          simp only [Set.mem_ofPred_eq, init_snocR, snocR_last]
          exact ⟨hx, trivial⟩
        have h1 := hsub hmem
        simp only [graphOf, Set.mem_ofPred_eq, snocR_last, init_snocR] at h1
        exact h1.symm
      rw [hproj]
      exact hg.congr (fun x hx => hfg x hx)
  | band hC a b ha hb hab =>
      rename_i C
      by_cases hne : C.Nonempty
      · exfalso
        obtain ⟨y, hy⟩ := hne
        obtain ⟨t, ht1, ht2⟩ := EReal.lt_iff_exists_real_btwn.mp (hab y hy)
        obtain ⟨t', ht1', ht2'⟩ := EReal.lt_iff_exists_real_btwn.mp ht1
        have hmem : ∀ s : ℝ, a y < (s : EReal) → (s : EReal) < b y →
            snocR y s ∈ {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧
              a (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
              ((z (Fin.last n) : ℝ) : EReal) < b (Fin.init z)} := by
          intro s h1 h2
          simp only [Set.mem_ofPred_eq, init_snocR, snocR_last]
          exact ⟨hy, h1, h2⟩
        have e1 : f y = t := by
          have h1 := hsub (hmem t ht1 ht2)
          simp only [graphOf, Set.mem_ofPred_eq, snocR_last, init_snocR] at h1
          exact h1.symm
        have e2 : f y = t' := by
          have h1 := hsub (hmem t' ht1' (lt_trans ht2' ht2))
          simp only [graphOf, Set.mem_ofPred_eq, snocR_last, init_snocR] at h1
          exact h1.symm
        have : t' = t := by rw [← e2, ← e1]
        exact absurd this (ne_of_lt (EReal.coe_lt_coe_iff.mp ht2'))
      · have hCeq : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
        have hproj : projLast
            {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧
              a (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
              ((z (Fin.last n) : ℝ) : EReal) < b (Fin.init z)} = ∅ := by
          rw [projLast]
          ext x; constructor
          · rintro ⟨t, ht⟩
            simp only [Set.mem_ofPred_eq] at ht
            rw [hCeq] at ht
            exact ht.1.elim
          · intro hx; exact absurd hx (Set.notMem_empty x)
        rw [hproj]
        exact fun x hx => absurd hx (Set.notMem_empty x)

/-! ## Two elementary set-theoretic facts -/

/-- `interior (s \ interior s) = ∅` for any set `s`. -/
theorem interior_diff_interior_self {α : Type*} [TopologicalSpace α] (s : Set α) :
    interior (s \ interior s) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have h1 : x ∈ interior s := interior_mono Set.diff_subset hx
  have h2 : x ∈ s \ interior s := interior_subset hx
  exact h2.2 h1

/-! ## `Ω`-membership of `projLast κ \ interior (projLast κ)` -/

/-- If `κ ∈ S.Ω a (c.eval D) (n+1)` then
`projLast κ \ interior (projLast κ) ∈ S.Ω a' (b'.eval D) n`
with bounds `a'`, `b'` independent of `κ`. -/
theorem omega_projLast_diff {S : SOMin} {n a D : ℕ} {c : Polynomial ℕ}
    {κ : Set (Fin (n + 1) → ℝ)} (hκ : κ ∈ S.Ω a (c.eval D) (n + 1)) :
    projLast κ \ interior (projLast κ) ∈
      S.Ω (max (a + 1) (a + 1 + 3 * n + 42 + 1) + 1)
        ((c + (Polynomial.C 12 * Polynomial.C (c.eval D) + Polynomial.C 60)).eval D) n := by
  have h1 : projLast κ ∈ S.Ω (a + 1) (c.eval D) n := S.proj hκ
  have h2 : interior (projLast κ) ∈ S.Ω (a + 1 + 3 * n + 42)
      ((Polynomial.C 12 * Polynomial.C (c.eval D) + Polynomial.C 60).eval D) n :=
    Work.WilG1.Calc.interior_mem (b := Polynomial.C (c.eval D)) (by simpa using h1)
  have h3 : (interior (projLast κ))ᶜ ∈ S.Ω (a + 1 + 3 * n + 42 + 1)
      ((Polynomial.C 12 * Polynomial.C (c.eval D) + Polynomial.C 60).eval D) n := S.compl h2
  have h4 := Work.WilG1.Omega.inter₂ h1 h3
  rw [Set.sdiff_eq]
  exact h4

/-! ## Cylindrical decompositions: covering cells

These are thin wrappers around the definition of `IsCylDecomp`, kept local so that the file has
no dependencies beyond the frozen definitions. -/

/-- Every cylindrical decomposition of `ℝⁿ` covers `ℝⁿ`. -/
theorem gc_exists_mem_of_cylDecomp {n : ℕ} {C : Finset (Set (Fin n → ℝ))}
    (h : IsCylDecomp n C) (z : Fin n → ℝ) : ∃ κ ∈ C, z ∈ κ := by
  cases n with
  | zero =>
      rw [IsCylDecomp] at h
      exact ⟨Set.univ, by rw [h]; simp, trivial⟩
  | succ m => exact h.2.2.1 z

/-- Every member of a cylindrical decomposition of `ℝⁿ` is a cell. -/
theorem gc_isCell_of_mem_cylDecomp {n : ℕ} {C : Finset (Set (Fin n → ℝ))}
    (h : IsCylDecomp n C) {κ : Set (Fin n → ℝ)} (hκ : κ ∈ C) : IsCell n κ := by
  cases n with
  | zero =>
      rw [IsCylDecomp] at h
      rw [h, Finset.mem_singleton] at hκ
      subst hκ
      exact IsCell.zero
  | succ m => exact (h.1 κ hκ).1

/-! ## Thin cells are nowhere dense -/

/-- `Fin.init`, viewed as a map on the space `Fin (n+1) → ℝ`, is continuous. -/
theorem gc_continuous_fin_init {n : ℕ} :
    Continuous (Fin.init : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) := by
  apply continuous_pi
  intro i
  simpa only [Fin.init] using continuous_apply (Fin.castSucc i)

/-- The inclusion `interior (init ⁻¹' T) ⊆ init ⁻¹' interior T`, where `init` drops the last
coordinate; it holds because `init` admits a continuous section. -/
theorem gc_interior_preimage_init_subset {n : ℕ} (T : Set (Fin n → ℝ)) :
    interior ((Fin.init : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) ⁻¹' T) ⊆
      (Fin.init : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) ⁻¹' interior T := by
  intro x hx
  rw [mem_interior_iff_mem_nhds] at hx
  rw [Set.mem_preimage, mem_interior_iff_mem_nhds]
  let g : (Fin n → ℝ) → (Fin (n + 1) → ℝ) := fun y => Fin.snoc y (x (Fin.last n))
  have hg : Continuous g := by
    exact Continuous.finSnoc continuous_id continuous_const
  have hgx : g (Fin.init x) = x := by
    simp only [g, Fin.snoc_init_self]
  have hmem : g ⁻¹' (Fin.init ⁻¹' T) ∈ nhds (Fin.init x) := by
    rw [← hgx] at hx
    exact (hg.continuousAt (x := Fin.init x)).preimage_mem_nhds hx
  have hset : (g ⁻¹' (Fin.init ⁻¹' T)) = T := by
    ext y
    simp only [Set.mem_preimage, g, Fin.init_snoc]
  rwa [hset] at hmem

/-- If `C ⊆ ℝⁿ` has nonempty interior and `a x < b x` are `EReal`-valued functions continuous
on `C`, then the open band over `C` between the graphs of `a` and `b` has nonempty interior. -/
theorem gc_interior_band_nonempty {n : ℕ} {C : Set (Fin n → ℝ)} {a b : (Fin n → ℝ) → EReal}
    (ha : ContinuousOn a C) (hb : ContinuousOn b C) (hab : ∀ x ∈ C, a x < b x)
    (hC : (interior C).Nonempty) :
    (interior {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧
      a (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
      ((z (Fin.last n) : ℝ) : EReal) < b (Fin.init z)}).Nonempty := by
  obtain ⟨x, hx⟩ := hC
  have hxC : x ∈ C := interior_subset hx
  obtain ⟨t, hat, htb⟩ := EReal.exists_between_coe_real (hab x hxC)
  obtain ⟨q1, haq1, hq1t⟩ := EReal.exists_between_coe_real hat
  obtain ⟨q2, htq2, hq2b⟩ := EReal.exists_between_coe_real htb
  have hq1_lt_t : q1 < t := EReal.coe_lt_coe_iff.mp hq1t
  have ht_lt_q2 : t < q2 := EReal.coe_lt_coe_iff.mp htq2
  have hpre1 : a ⁻¹' (Set.Iio ((q1 : ℝ) : EReal)) ∈ 𝓝[C] x :=
    (ha x hxC).preimage_mem_nhdsWithin (isOpen_Iio.mem_nhds haq1)
  have hpre2 : b ⁻¹' (Set.Ioi ((q2 : ℝ) : EReal)) ∈ 𝓝[C] x :=
    (hb x hxC).preimage_mem_nhdsWithin (isOpen_Ioi.mem_nhds hq2b)
  rw [mem_nhdsWithin] at hpre1 hpre2
  obtain ⟨V1, hV1open, hxV1, hV1sub⟩ := hpre1
  obtain ⟨V2, hV2open, hxV2, hV2sub⟩ := hpre2
  let W : Set (Fin n → ℝ) := V1 ∩ V2 ∩ interior C
  have hWopen : IsOpen W := (hV1open.inter hV2open).inter isOpen_interior
  have hxW : x ∈ W := ⟨⟨hxV1, hxV2⟩, hx⟩
  have hWsubC : W ⊆ C := fun y hy => interior_subset hy.2
  have hW1 : ∀ y ∈ W, a y < ((q1 : ℝ) : EReal) := by
    intro y hy
    simpa only [Set.mem_preimage, Set.mem_Iio] using hV1sub ⟨hy.1.1, hWsubC hy⟩
  have hW2 : ∀ y ∈ W, ((q2 : ℝ) : EReal) < b y := by
    intro y hy
    simpa only [Set.mem_preimage, Set.mem_Ioi] using hV2sub ⟨hy.1.2, hWsubC hy⟩
  let z : Fin (n + 1) → ℝ := Fin.snoc x t
  have hzinit : Fin.init z = x := by simp [z]
  have hzlast : z (Fin.last n) = t := by simp [z]
  let O : Set (Fin (n + 1) → ℝ) :=
    Fin.init ⁻¹' W ∩ (fun z' => z' (Fin.last n)) ⁻¹' Set.Ioi q1 ∩
      (fun z' => z' (Fin.last n)) ⁻¹' Set.Iio q2
  have hOopen : IsOpen O :=
    ((hWopen.preimage gc_continuous_fin_init).inter
      (isOpen_Ioi.preimage (continuous_apply (Fin.last n)))).inter
      (isOpen_Iio.preimage (continuous_apply (Fin.last n)))
  have hzO : z ∈ O := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change Fin.init z ∈ W
      rw [hzinit]; exact hxW
    · change z (Fin.last n) ∈ Set.Ioi q1
      rw [Set.mem_Ioi, hzlast]; exact hq1_lt_t
    · change z (Fin.last n) ∈ Set.Iio q2
      rw [Set.mem_Iio, hzlast]; exact ht_lt_q2
  have hOsub : O ⊆ {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧
      a (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
      ((z (Fin.last n) : ℝ) : EReal) < b (Fin.init z)} := by
    intro w hw
    obtain ⟨⟨hwW, hwq1⟩, hwq2⟩ := hw
    change Fin.init w ∈ W at hwW
    simp only [Set.mem_preimage, Set.mem_Ioi] at hwq1
    simp only [Set.mem_preimage, Set.mem_Iio] at hwq2
    refine ⟨hWsubC hwW, ?_, ?_⟩
    · exact (hW1 (Fin.init w) hwW).trans (EReal.coe_lt_coe_iff.mpr hwq1)
    · exact (EReal.coe_lt_coe_iff.mpr hwq2).trans (hW2 (Fin.init w) hwW)
  exact ⟨z, interior_maximal hOsub hOopen hzO⟩

/-- A band cell with empty interior is nowhere dense, provided the induction hypothesis that
its base cell is nowhere dense whenever it is thin. -/
theorem gc_band_cell_isNowhereDense {n : ℕ} {C : Set (Fin n → ℝ)} {a b : (Fin n → ℝ) → EReal}
    (ha : ContinuousOn a C) (hb : ContinuousOn b C) (hab : ∀ x ∈ C, a x < b x)
    (ihC : interior C = ∅ → IsNowhereDense C)
    (hint : interior {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧
      a (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
      ((z (Fin.last n) : ℝ) : EReal) < b (Fin.init z)} = ∅) :
    IsNowhereDense {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧
      a (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
      ((z (Fin.last n) : ℝ) : EReal) < b (Fin.init z)} := by
  have hCint : interior C = ∅ := by
    by_contra hne
    have hne' : (interior C).Nonempty := Set.nonempty_iff_ne_empty.mpr hne
    have h := gc_interior_band_nonempty ha hb hab hne'
    rw [hint] at h
    exact h.ne_empty rfl
  have hcell : IsNowhereDense C := ihC hCint
  rw [IsNowhereDense] at hcell ⊢
  refine Set.eq_empty_of_subset_empty ?_
  have hcont : Continuous (Fin.init : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) :=
    continuous_pi fun i => continuous_apply (Fin.castSucc i)
  have hsub : interior (closure {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧
        a (Fin.init z) < ((z (Fin.last n) : ℝ) : EReal) ∧
        ((z (Fin.last n) : ℝ) : EReal) < b (Fin.init z)}) ⊆
      {z : Fin (n + 1) → ℝ | Fin.init z ∈ interior (closure C)} :=
    (interior_mono ((closure_mono (fun z hz => hz.1)).trans
      (hcont.closure_preimage_subset C))).trans (gc_interior_preimage_init_subset (closure C))
  rw [hcell] at hsub
  exact hsub

/-- A cell with empty interior is nowhere dense. -/
theorem gc_cell_isNowhereDense_of_thin :
    ∀ {n : ℕ} {κ : Set (Fin n → ℝ)}, IsCell n κ → interior κ = ∅ → IsNowhereDense κ := by
  intro n κ h
  induction h with
  | zero =>
      intro hint
      exfalso
      have hne : (Set.univ : Set (Fin 0 → ℝ)).Nonempty := ⟨Fin.elim0, Set.mem_univ _⟩
      obtain ⟨x, hx⟩ := hne
      rw [IsOpen.interior_eq isOpen_univ] at hint
      rw [hint] at hx
      exact hx
  | graph hC f hf _ih =>
      intro _hint
      exact isNowhereDense_graph hf
  | band hC a b ha hb hab ih =>
      intro hint
      exact gc_band_cell_isNowhereDense ha hb hab ih hint

/-- A finite union of cells contained in a set of empty interior is nowhere dense. -/
theorem gc_isNowhereDense_biUnion_cells {n : ℕ} {C : Finset (Set (Fin n → ℝ))}
    {A : Set (Fin n → ℝ)} (hcell : ∀ κ ∈ C, IsCell n κ) (hsub : ∀ κ ∈ C, κ ⊆ A)
    (hint : interior A = ∅) : IsNowhereDense (⋃ κ ∈ C, κ) := by
  refine IsNowhereDense.biUnion (u := C) (f := fun κ => κ) (fun κ hκ => ?_)
  have hintκ : interior κ = ∅ :=
    Set.eq_empty_of_subset_empty (by rw [← hint]; exact interior_mono (hsub κ hκ))
  exact gc_cell_isNowhereDense_of_thin (hcell κ hκ) hintκ

/-! ## A thin `Ω`-set is nowhere dense -/

/-- A thin `Ω`-set is nowhere dense.  Refine by a sharp cell decomposition: `A` is the union of
the cells contained in it, each of which is thin, hence nowhere dense. -/
theorem gc_isNowhereDense_of_Ω {S : SOMin} (hcd : S.SharpCD) {n a D : ℕ} {b : Polynomial ℕ}
    {A : Set (Fin n → ℝ)} (hA : A ∈ S.Ω a (b.eval D) n) (hint : interior A = ∅) :
    IsNowhereDense A := by
  obtain ⟨a', b', c', hsharp⟩ := hcd a n
  obtain ⟨C, hdec, hsep, -, -⟩ := hsharp (b.eval D) 1 (fun _ => A) (fun _ => hA)
  have hcover : ∀ z : Fin n → ℝ, ∃ κ ∈ C, z ∈ κ := fun z => gc_exists_mem_of_cylDecomp hdec z
  have hcell : ∀ κ ∈ C, IsCell n κ := fun κ hκ => gc_isCell_of_mem_cylDecomp hdec hκ
  have hAeq : A = ⋃ κ ∈ C.filter (fun κ => κ ⊆ A), κ := by
    ext z; constructor
    · intro hz
      obtain ⟨κ, hκC, hzκ⟩ := hcover z
      have hsub : κ ⊆ A := by
        rcases hsep 0 κ hκC with h | hd
        · exact h
        · exact absurd hz (Set.disjoint_left.mp hd hzκ)
      exact Set.mem_biUnion (Finset.mem_filter.mpr ⟨hκC, hsub⟩) hzκ
    · intro hz
      obtain ⟨κ, hκ, hzκ⟩ := Set.mem_iUnion₂.mp hz
      exact (Finset.mem_filter.mp hκ).2 hzκ
  rw [hAeq]
  exact gc_isNowhereDense_biUnion_cells (C := C.filter (fun κ => κ ⊆ A))
    (fun κ hκ => hcell κ (Finset.mem_filter.mp hκ).1)
    (fun κ hκ => (Finset.mem_filter.mp hκ).2) hint

/-- A finite union of thin `Ω`-sets is thin. -/
theorem gc_thin_union_finset {S : SOMin} (hcd : S.SharpCD) {n a D : ℕ} {b : Polynomial ℕ}
    (C : Finset (Set (Fin n → ℝ))) (hC : ∀ A ∈ C, A ∈ S.Ω a (b.eval D) n)
    (hint : ∀ A ∈ C, interior A = ∅) :
    interior (⋃₀ ((C : Set (Set (Fin n → ℝ))))) = ∅ := by
  rw [Set.sUnion_eq_biUnion]
  have hnd : IsNowhereDense (⋃ A ∈ C, A) :=
    IsNowhereDense.biUnion (u := C) (f := fun A => A)
      (fun A hA => gc_isNowhereDense_of_Ω hcd (hC A hA) (hint A hA))
  have hnd' : interior (closure (⋃ A ∈ C, A)) = ∅ := hnd
  exact Set.eq_empty_of_subset_empty (fun x hx => by
    have h1 : x ∈ interior (closure (⋃ A ∈ C, A)) := interior_mono subset_closure hx
    rw [hnd'] at h1
    exact h1)

/-! ## Generic continuity -/

theorem generic_continuity {S : WilkiesDesign.SOMin} (hcd : S.SharpCD) {n F D : ℕ}
    (f : (Fin n → ℝ) → ℝ) (hf : WilkiesDesign.graphOf f ∈ S.Ω F D (n + 1)) :
    interior {x : Fin n → ℝ | ¬ ContinuousAt f x} = ∅ := by
  -- Sharp cell decomposition of `ℝⁿ⁺¹` adapted to the graph of `f`.
  obtain ⟨a, _b, c, hsharp⟩ := hcd F (n + 1)
  obtain ⟨C, hCyl, hsplit, -, hmem⟩ :=
    hsharp D 1 (fun _ : Fin 1 => graphOf f) (fun _ => hf)
  -- The family of `Ω`-sets whose union is thin.
  let T : Finset (Set (Fin n → ℝ)) :=
    C.image (fun κ => projLast κ \ interior (projLast κ))
  have hbounds : ∀ A ∈ T, A ∈
      S.Ω (max (a + 1) (a + 1 + 3 * n + 42 + 1) + 1)
        ((c + (Polynomial.C 12 * Polynomial.C (c.eval D) + Polynomial.C 60)).eval D) n := by
    intro A hA
    obtain ⟨κ, hκC, rfl⟩ := Finset.mem_image.mp hA
    exact omega_projLast_diff (hmem κ hκC)
  have hthin_each : ∀ A ∈ T, interior A = ∅ := by
    intro A hA
    obtain ⟨κ, hκC, rfl⟩ := Finset.mem_image.mp hA
    exact interior_diff_interior_self _
  have hthin : interior (⋃₀ (T : Set (Set (Fin n → ℝ)))) = ∅ :=
    gc_thin_union_finset hcd T hbounds hthin_each
  -- The discontinuity set is contained in that union.
  have hsub : {x : Fin n → ℝ | ¬ ContinuousAt f x} ⊆ ⋃₀ (T : Set (Set (Fin n → ℝ))) := by
    intro x hx
    -- the cell containing `(x, f x)`
    obtain ⟨κ, hκC, hzκ⟩ := gc_exists_mem_of_cylDecomp hCyl (snocR x (f x))
    have hzgraph : snocR x (f x) ∈ graphOf f := by
      simp only [graphOf, Set.mem_ofPred_eq, snocR_last, init_snocR]
    -- that cell is contained in the graph, hence its base carries `f` continuously
    have hκsub : κ ⊆ graphOf f := by
      rcases hsplit 0 κ hκC with h | h
      · exact h
      · exact absurd hzgraph (Set.disjoint_left.mp h hzκ)
    have hcont : ContinuousOn f (projLast κ) :=
      continuousOn_of_isCell_subset_graphOf (gc_isCell_of_mem_cylDecomp hCyl hκC) hκsub
    have hxproj : x ∈ projLast κ := by
      rw [projLast]; exact ⟨f x, hzκ⟩
    refine Set.mem_sUnion.mpr ⟨projLast κ \ interior (projLast κ), ?_, ?_⟩
    · exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨κ, hκC, rfl⟩)
    · refine ⟨hxproj, ?_⟩
      intro hxint
      exact hx ((hcont.mono interior_subset).continuousAt
        (IsOpen.mem_nhds isOpen_interior hxint))
  -- Conclude by monotonicity of the interior.
  have hfin : interior {x : Fin n → ℝ | ¬ ContinuousAt f x} ⊆
      interior (⋃₀ (T : Set (Set (Fin n → ℝ)))) := interior_mono hsub
  rw [hthin] at hfin
  exact Set.Subset.antisymm hfin (Set.empty_subset _)

end Work.WilG1.Cell
