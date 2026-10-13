import Mathlib
import Submission.Work.WilG4a.CD.fibDerivDefs
import Submission.Work.WilG4a.Cells
import Submission.Work.WilG4a.Bounds
import Submission.Work.WilG4a.CD.badLocusUnion_mem
import Submission.Work.WilG4a.CD.badLoci_cellDecomp
import Submission.Work.WilG1.Cell.thin_closure
import Submission.Work.WilG1.Main
import Submission.Work.WilkiesH.Strat.cellData

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4a.CD

open WilkiesDesign

/-!
# The cylindrical decomposition of the bad locus, and the fibre germ condition

This file assembles `Work.WilG4a.CD.cellDecomp_germ`.  The construction is:

* the bad locus `V = badLocus f j` is `Ω`-definable with format `a₀` and degree
  `b₀.eval ![D,j]` (`Work.WilG4a.badLocus_mem`);
* sharp cell decomposition with input format `a₀` in dimension `p+1` refines `V` by a
  cylindrical decomposition `C`, whose cells are `Ω`-definable and whose cardinality is
  polynomially bounded; the two polynomial bounds are merged into a single
  `MvPolynomial (Fin 2) ℕ` exactly as in `Work.WilG4a.CD.badLoci_cellDecomp`;
* the extra fibre-germ condition on a cell `κ₀` follows from the fact that the band cells over
  a base cell of non-empty interior have non-empty interior, hence cannot lie in the thin `V`;
  so the bad cells over such a base are graph cells, whose fibres over a fixed parameter are
  single points.  Hence the fibre of `V` over any point of such a base is finite
  (`fibre_finite_of_cylDecomp_aux`), and a finite fibre is avoided by some punctured
  neighbourhood (`fibGerm_of_fibre_finite` below).
-/

/-! ## The base of a cell is the image of the cell under `Fin.init` -/

/-- For a graph cell (given by its membership characterisation) the projection to the first
`m` coordinates is exactly the base. -/
private lemma init_image_eq_of_graph {m : ℕ} {κ : Set (Fin (m + 1) → ℝ)} {τ : Set (Fin m → ℝ)}
    {γ : (Fin m → ℝ) → ℝ}
    (hiff : ∀ z : Fin (m + 1) → ℝ, z ∈ κ ↔ Fin.init z ∈ τ ∧ z (Fin.last m) = γ (Fin.init z)) :
    Fin.init '' κ = τ := by
  apply Set.Subset.antisymm
  · rintro u ⟨z, hz, rfl⟩
    exact ((hiff z).mp hz).1
  · intro u hu
    refine ⟨Fin.snoc u (γ u), ?_, by simp⟩
    exact (hiff (Fin.snoc u (γ u))).mpr ⟨by simpa using hu, by simp⟩

/-- For a band cell (given by its membership characterisation) the projection to the first `m`
coordinates is exactly the base. -/
private lemma init_image_eq_of_band {m : ℕ} {κ : Set (Fin (m + 1) → ℝ)} {τ : Set (Fin m → ℝ)}
    {a b : (Fin m → ℝ) → EReal} (hab : ∀ x ∈ τ, a x < b x)
    (hiff : ∀ z : Fin (m + 1) → ℝ, z ∈ κ ↔ Fin.init z ∈ τ ∧
      a (Fin.init z) < ((z (Fin.last m) : ℝ) : EReal) ∧
      ((z (Fin.last m) : ℝ) : EReal) < b (Fin.init z)) :
    Fin.init '' κ = τ := by
  apply Set.Subset.antisymm
  · rintro u ⟨z, hz, rfl⟩
    exact ((hiff z).mp hz).1
  · intro u hu
    obtain ⟨t, ht1, ht2⟩ := EReal.lt_iff_exists_real_btwn.mp (hab u hu)
    refine ⟨Fin.snoc u t, ?_, by simp⟩
    exact (hiff (Fin.snoc u t)).mpr ⟨by simpa using hu, by simpa using ht1, by simpa using ht2⟩

/-! ## The fibre of a thin set over a thick base cell is finite -/

/-- **Fibre finiteness.**  Let `C` be a cylindrical decomposition of `ℝ^{p+1}` every cell of
which is contained in, or disjoint from, a set `V` of empty interior.  If `κ₀ ∈ C` has a base
`Fin.init '' κ₀` with non-empty interior, then the vertical fibre of `V` over any point of that
base is finite.

Indeed, the band cells over a base of non-empty interior have non-empty interior, so a band
cell of `C` cannot be contained in the thin `V`; hence the bad cells meeting the fibre are
graph cells, whose fibre over a parameter is a single point.  There are only finitely many
cells. -/
private theorem fibre_finite_of_cylDecomp_aux {p : ℕ} {C : Finset (Set (Fin (p + 1) → ℝ))}
    {V : Set (Fin (p + 1) → ℝ)} (hC : WilkiesDesign.IsCylDecomp (p + 1) C)
    (href : ∀ κ ∈ C, κ ⊆ V ∨ Disjoint κ V) (hV : interior V = ∅)
    {κ₀ : Set (Fin (p + 1) → ℝ)} (hκ₀ : κ₀ ∈ C)
    (hint : (interior (Fin.init '' κ₀)).Nonempty)
    (l : Fin p → ℝ) (hl : l ∈ Fin.init '' κ₀) :
    {y : ℝ | Fin.snoc l y ∈ V}.Finite := by
  classical
  set B : Set (Fin p → ℝ) := Fin.init '' κ₀ with hB
  -- the bases of the cells form a cylindrical decomposition of `ℝ^p`
  have hbasedec : WilkiesDesign.IsCylDecomp p (C.image (fun c => Fin.init '' c)) := by
    obtain ⟨_, _, _, h4⟩ := hC
    exact h4
  have hpd := Work.WilG1.Cell.pairwiseDisjoint_of_cylDecomp hbasedec
  -- every cell whose base contains `l` has base `B`
  have hbase_uniq : ∀ κ ∈ C, l ∈ Fin.init '' κ → Fin.init '' κ = B := by
    intro κ hκC hlκ
    have h1 : Fin.init '' κ ∈ C.image (fun c => Fin.init '' c) :=
      Finset.mem_image.mpr ⟨κ, hκC, rfl⟩
    have h2 : B ∈ C.image (fun c => Fin.init '' c) := by
      rw [hB]; exact Finset.mem_image.mpr ⟨κ₀, hκ₀, rfl⟩
    exact Set.pairwiseDisjoint_iff.mp hpd
      (Finset.mem_coe.mpr h1) (Finset.mem_coe.mpr h2) ⟨l, hlκ, hl⟩
  -- the cells with base `B`
  set G : Finset (Set (Fin (p + 1) → ℝ)) := C.filter (fun κ => Fin.init '' κ = B) with hG
  -- the fibre of `V` over `l` is covered by the fibres of the cells of `G`
  have hcover : ∀ y : ℝ, Fin.snoc l y ∈ V → ∃ κ ∈ G, Fin.snoc l y ∈ κ := by
    intro y _hy
    obtain ⟨κ, hκC, hzκ⟩ := Work.WilG1.Cell.exists_mem_of_cylDecomp hC (Fin.snoc l y)
    refine ⟨κ, ?_, hzκ⟩
    exact Finset.mem_filter.mpr
      ⟨hκC, hbase_uniq κ hκC ⟨Fin.snoc l y, hzκ, by simp⟩⟩
  -- each cell of `G` has a singleton or empty fibre over `l`, and is either disjoint from `V`
  -- or cannot be contained in it
  have hfinG : ∀ κ ∈ G,
      ({y : ℝ | Fin.snoc l y ∈ κ} ∩ {y : ℝ | Fin.snoc l y ∈ V}).Finite := by
    intro κ hκG
    obtain ⟨hκC, hκB⟩ := Finset.mem_filter.mp hκG
    have hlκ : l ∈ Fin.init '' κ := by rw [hκB]; exact hl
    have hcell : WilkiesDesign.IsCell (p + 1) κ :=
      Work.WilG1.Cell.isCell_of_mem_cylDecomp hC hκC
    by_cases hdisj : Disjoint κ V
    · refine Set.Finite.subset Set.finite_empty ?_
      rintro y ⟨hyκ, hyV⟩
      exact Set.disjoint_left.mp hdisj hyκ hyV
    · have hsub : κ ⊆ V := (href κ hκC).resolve_right hdisj
      rcases Work.WilG1.Cell.cell_cases hcell with hg | hb
      · -- graph cell: the fibre over `l` is a single point
        obtain ⟨τ, γ, _hcont, hiff⟩ := hg
        have hτ : τ = B := (init_image_eq_of_graph hiff).symm.trans hκB
        have hlτ : l ∈ τ := by rw [hτ]; exact hl
        have hsgl : {y : ℝ | Fin.snoc l y ∈ κ} = {γ l} := by
          ext y
          rw [Set.mem_singleton_iff]
          constructor
          · intro hy
            have h := (hiff (Fin.snoc l y)).mp hy
            rw [Fin.init_snoc, Fin.snoc_last] at h
            exact h.2
          · intro hy
            subst hy
            exact (hiff (Fin.snoc l (γ l))).mpr ⟨by simpa using hlτ, by simp⟩
        rw [hsgl]
        exact (Set.finite_singleton (γ l)).subset Set.inter_subset_left
      · -- band cell: non-empty interior, contradicting `κ ⊆ V` and `interior V = ∅`
        obtain ⟨τ, a, b, ha, hb, hab, hiff⟩ := hb
        exfalso
        have hτ : τ = B := (init_image_eq_of_band hab hiff).symm.trans hκB
        have hintτ : (interior τ).Nonempty := by rw [hτ]; exact hint
        have hbandint := Work.WilG1.Cell.interior_band_nonempty ha hb hab hintτ
        have hκeq : {z : Fin (p + 1) → ℝ | Fin.init z ∈ τ ∧
            a (Fin.init z) < ((z (Fin.last p) : ℝ) : EReal) ∧
            ((z (Fin.last p) : ℝ) : EReal) < b (Fin.init z)} = κ :=
          Set.ext (fun z => (hiff z).symm)
        rw [hκeq] at hbandint
        have hInt : (interior V).Nonempty :=
          Set.Nonempty.mono (interior_mono hsub) hbandint
        rw [hV] at hInt
        exact hInt.ne_empty rfl
  -- a finite union of finite sets
  have hbig : (⋃ κ ∈ (G : Set (Set (Fin (p + 1) → ℝ))),
      ({y : ℝ | Fin.snoc l y ∈ κ} ∩ {y : ℝ | Fin.snoc l y ∈ V})).Finite :=
    Set.Finite.biUnion G.finite_toSet (fun κ hκ => hfinG κ (Finset.mem_coe.mp hκ))
  refine hbig.subset ?_
  intro y hy
  obtain ⟨κ, hκG, hyκ⟩ := hcover y hy
  exact Set.mem_biUnion (Finset.mem_coe.mpr hκG) ⟨hyκ, hy⟩

/-- A point whose fibre `{y | Fin.snoc l y ∈ V}` of `V` is finite has a punctured
neighbourhood (in the fibre direction) disjoint from `V`: the fibre minus the point itself is
finite, hence closed, hence a neighbourhood of the point misses it. -/
private theorem fibGerm_of_fibre_finite {p : ℕ} {V : Set (Fin (p + 1) → ℝ)}
    (l : Fin p → ℝ) (x : ℝ) (h : {y : ℝ | Fin.snoc l y ∈ V}.Finite) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : ℝ, t ≠ x → |t - x| < ρ → Fin.snoc l t ∉ V := by
  have hfin : ({y : ℝ | Fin.snoc l y ∈ V} \ {x}).Finite := h.subset Set.sdiff_subset
  have hclosed : IsClosed ({y : ℝ | Fin.snoc l y ∈ V} \ {x}) := hfin.isClosed
  have hopen : IsOpen ({y : ℝ | Fin.snoc l y ∈ V} \ {x})ᶜ := hclosed.isOpen_compl
  have hx : x ∈ ({y : ℝ | Fin.snoc l y ∈ V} \ {x})ᶜ := by simp
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hx)
  refine ⟨ρ, hρ, fun t ht hρt hmem => ?_⟩
  have hmem' : t ∈ ({y : ℝ | Fin.snoc l y ∈ V} \ {x}) := ⟨hmem, by simpa using ht⟩
  have htball : t ∈ Metric.ball x ρ := by
    rw [Metric.mem_ball, Real.dist_eq]
    exact hρt
  exact hball htball hmem'

/-! ## The bad locus is thin -/

/-- The `C^j` locus of a family member is open, hence its interior is itself, so the bad locus
is exactly the non-`C^j` locus. -/
private theorem isOpen_contDiffAt_famFun {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) (j : ℕ) :
    IsOpen {x : Fin (p + 1) → ℝ | ContDiffAt ℝ j (Work.WilG4a.famFun f) x} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  exact (show ContDiffAt ℝ j (Work.WilG4a.famFun f) x from hx).eventually (by simp)

/-- The bad locus of a definable family member has empty interior: it is exactly the locus
where the member fails to be `C^j`, and that locus is thin (`G1_generic_smooth_proved`). -/
private theorem badLocus_interior_eq_empty_aux (S : WilkiesDesign.SOMin)
    (hcd : WilkiesDesign.SOMin.SharpCD S) (p F0 : ℕ) :
    ∀ (D j : ℕ) {f : (Fin p → ℝ) → ℝ → ℝ}, Work.WilG4a.graphFam f ∈ S.Ω F0 D (p + 1 + 1) →
      interior (Work.WilG4a.badLocus f j) = ∅ := by
  intro D j f hf
  have hOpen := isOpen_contDiffAt_famFun f j
  have hbad : Work.WilG4a.badLocus f j =
      {x : Fin (p + 1) → ℝ | ¬ ContDiffAt ℝ j (Work.WilG4a.famFun f) x} := by
    have h1 : Work.WilG4a.smoothLocus f j =
        {x : Fin (p + 1) → ℝ | ContDiffAt ℝ j (Work.WilG4a.famFun f) x} := by
      rw [Work.WilG4a.smoothLocus]
      exact hOpen.interior_eq
    rw [Work.WilG4a.badLocus, h1]
    ext x
    simp
  rw [hbad]
  exact WilkiesDesign.CG.G1_generic_smooth_proved S hcd (Work.WilG4a.famFun f)
    (by simpa [Work.WilG4a.graphOf_famFun] using hf) j

/-! ## The main theorem -/

/-- A cylindrical decomposition of `ℝ^{p+1}` refining the bad locus `V_j = badLocus f j`, whose cells are `Ω`-definable with sharp bounds, and one extra property: for every cell `κ₀` whose base cell `Fin.init '' κ₀` has non-empty interior, the punctured fibre neighbourhood of every point of the tube over `Fin.init '' κ₀` lies in `smoothLocus f j`. (A band cell over a base with non-empty interior has non-empty interior, so it cannot lie in the thin `V_j`; hence the bad cells over such a base are graph cells, whose fibres over a fixed parameter are single points at positive distance from one another.) -/
theorem cellDecomp_germ (S : WilkiesDesign.SOMin) (hcd : WilkiesDesign.SOMin.SharpCD S)
    (hder : WilkiesDesign.SOMin.SharpDeriv S) (p F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D j : ℕ) {f : (Fin p → ℝ) → ℝ → ℝ}, Work.WilG4a.graphFam f ∈ S.Ω F0 D (p + 1 + 1) →
        ∃ C : Finset (Set (Fin (p + 1) → ℝ)),
          WilkiesDesign.IsCylDecomp (p + 1) C ∧
          C.card ≤ MvPolynomial.eval ![D, j] b ∧
          (∀ κ ∈ C, κ ∈ S.Ω a (MvPolynomial.eval ![D, j] b) (p + 1)) ∧
          (∀ κ ∈ C, Disjoint κ (Work.WilG4a.badLocus f j) ∨ κ ⊆ Work.WilG4a.badLocus f j) ∧
          (∀ κ₀ ∈ C, (interior (Fin.init '' κ₀)).Nonempty → ∀ l ∈ (Fin.init '' κ₀), ∀ x : ℝ,
            Work.WilG4a.CD.fibGerm f j (Fin.snoc l x)) := by
  -- format and degree of the bad locus `V_j`
  obtain ⟨a₀, b₀, hb₀⟩ := Work.WilG4a.badLocus_mem S hder p F0
  -- sharp cell decomposition at input format `a₀`, dimension `p+1`
  obtain ⟨a₁, b₁, c₁, hb₁⟩ := hcd a₀ (p + 1)
  -- `d₁` shifts the count polynomial `b₁` from `j+1` to `j`, `d₂` substitutes `b₀` for `D`
  obtain ⟨d₁, hd₁⟩ := Work.WilG4a.exists_eval_shift b₁
  obtain ⟨d₂, hd₂⟩ := Work.WilG4a.exists_eval_comp d₁ b₀
  refine ⟨a₁, Polynomial.eval₂ MvPolynomial.C b₀ c₁ + d₂, ?_⟩
  intro D j f hf
  have hfam : Work.WilG4a.badLocus f j ∈ S.Ω a₀ (MvPolynomial.eval ![D, j] b₀) (p + 1) :=
    hb₀ D j hf
  -- the refining decomposition, with the family `Fin (j+1) → {V_j}` enumerated so that the
  -- second variable of the count bound is `j+1`
  obtain ⟨C, hCyl, href, hcard, hmem⟩ :=
    hb₁ (MvPolynomial.eval ![D, j] b₀) (j + 1) (fun _ : Fin (j + 1) => Work.WilG4a.badLocus f j)
      (fun _ => hfam)
  refine ⟨C, hCyl, ?_, ?_, ?_, ?_⟩
  · -- the cardinality bound
    have hshift : b₁.eval ![MvPolynomial.eval ![D, j] b₀, j + 1] = d₂.eval ![D, j] :=
      (hd₁ (MvPolynomial.eval ![D, j] b₀) j).trans (hd₂ D j)
    calc C.card ≤ b₁.eval ![MvPolynomial.eval ![D, j] b₀, j + 1] := hcard
      _ = d₂.eval ![D, j] := hshift
      _ ≤ (Polynomial.eval₂ MvPolynomial.C b₀ c₁ + d₂).eval ![D, j] := by
          rw [MvPolynomial.eval_add]
          exact Nat.le_add_left _ _
  · -- the `Ω`-membership of the cells
    intro κ hκ
    refine Work.WilG4a.mono_D_le S (hmem κ hκ) ?_
    rw [MvPolynomial.eval_add, eval_eval₂_C]
    exact Nat.le_add_right _ _
  · -- refinement of the bad locus
    intro κ hκ
    exact (href 0 κ hκ).symm
  · -- the fibre-germ condition
    intro κ₀ hκ₀ hint l hl x
    change Fin.snoc l x ∈ Work.WilG4a.CD.fibGerm f j
    rw [mem_fibGerm]
    have hVint : interior (Work.WilG4a.badLocus f j) = ∅ :=
      badLocus_interior_eq_empty_aux S hcd p F0 D j hf
    have href' : ∀ κ ∈ C,
        κ ⊆ Work.WilG4a.badLocus f j ∨ Disjoint κ (Work.WilG4a.badLocus f j) :=
      fun κ hκ => href 0 κ hκ
    have hfin : {y : ℝ | Fin.snoc l y ∈ Work.WilG4a.badLocus f j}.Finite :=
      fibre_finite_of_cylDecomp_aux hCyl href' hVint hκ₀ hint l hl
    obtain ⟨ρ, hρ, hspec⟩ := fibGerm_of_fibre_finite l x hfin
    refine ⟨ρ, hρ, fun t ht hρt => ?_⟩
    have hnot : Fin.snoc l t ∉ Work.WilG4a.badLocus f j :=
      hspec t (by simpa using ht) (by simpa using hρt)
    simpa [Fin.init_snoc, Work.WilG4a.badLocus] using hnot

end Work.WilG4a.CD
