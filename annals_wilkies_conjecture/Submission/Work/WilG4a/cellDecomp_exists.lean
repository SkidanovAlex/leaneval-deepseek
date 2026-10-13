/-
  WilG4a — the existence of the cell decomposition behind BNZ Lemma 5.3 (`n = 1`).

  `Work.WilG4a.CellDecomp S p` asks for a finite family of `Ω`-definable cells covering the
  strip over `Λ`, each either *good* (its fibres are points or intervals on which every slice
  `x ↦ F i l x` is `C^{r+1}` with constant-signed derivatives) or *degenerate* (all fibres
  subsingletons).

  The construction refines a cylindrical decomposition of `ℝ^{p+1}` against, for every family
  member `i`,

  * the locus where the *slice* `x ↦ F i l x` fails to be `C^{r+1}` (`CD.sliceContDiffAt_mem`),
  * the loci where its `j`-th derivative exists and vanishes, for `j ≤ r+1`
    (the fibre-derivative graph `CD.fibDerivGraph_mem`).

  For a cell `κ` of such a decomposition either `κ ⊆` some slice-bad locus — then every fibre
  of `κ` is contained in a finite set (`CD.slice_bad_finite`), so the fibre is a subsingleton
  and `κ` is degenerate — or `κ` meets no slice-bad locus, in which case every slice is
  `C^{r+1}` on every fibre, and the refinement against the vanishing loci forces the derivatives
  to have constant sign there.
-/
import Mathlib
import Submission.Work.WilG4a.f1affine1_defs
import Submission.Work.WilG4a.Cells
import Submission.Work.WilG4a.isCell_fiber
import Submission.Work.WilG4a.signConst_ivt
import Submission.Work.WilG4a.mvpoly_eval_mono
import Submission.Work.WilG4a.count_poly_comp
import Submission.Work.WilG4a.CD.badLoci_cellDecomp
import Submission.Work.WilG4a.CD.cellDecomp_refining
import Submission.Work.WilG4a.CD.sliceContDiffAt_mem
import Submission.Work.WilG4a.CD.fibDerivGraph_mem
import Submission.Work.WilG4a.CD.slice_bad_finite
import Submission.Work.WilG4a.CD.fibre_inter_I

set_option autoImplicit false
set_option maxHeartbeats 3500000
noncomputable section
open Classical
namespace Work.WilG4a
open WilkiesDesign WilkiesConjecture

variable {p : ℕ}

/-! ## 1. The slice loci of a family member -/

/-- The locus where the slice `x ↦ f l x` is `C^j` at `x`. -/
def sliceCj (f : (Fin p → ℝ) → ℝ → ℝ) (j : ℕ) : Set (Fin (p + 1) → ℝ) :=
  {z | ContDiffAt ℝ j (fun x : ℝ => f (Fin.init z) x) (z (Fin.last p))}

/-- The locus where the slice's `j`-th derivative exists and vanishes. -/
def sliceZero (f : (Fin p → ℝ) → ℝ → ℝ) (j : ℕ) : Set (Fin (p + 1) → ℝ) :=
  projLast (CD.fibDerivGraph f j ∩ {w : Fin (p + 2) → ℝ | w (Fin.last (p + 1)) = 0})

theorem mem_sliceCj {f : (Fin p → ℝ) → ℝ → ℝ} {j : ℕ} {z : Fin (p + 1) → ℝ} :
    z ∈ sliceCj f j ↔ ContDiffAt ℝ j (fun x : ℝ => f (Fin.init z) x) (z (Fin.last p)) :=
  Iff.rfl

theorem mem_sliceZero {f : (Fin p → ℝ) → ℝ → ℝ} {j : ℕ} {z : Fin (p + 1) → ℝ} :
    z ∈ sliceZero f j ↔
      ContDiffAt ℝ j (fun x : ℝ => f (Fin.init z) x) (z (Fin.last p)) ∧
        iteratedDeriv j (fun x : ℝ => f (Fin.init z) x) (z (Fin.last p)) = 0 := by
  constructor
  · rintro ⟨y, hy⟩
    simp only [Set.mem_inter_iff, CD.fibDerivGraph, Set.mem_setOf_eq, projLast,
      Fin.init_snoc, Fin.snoc_last] at hy
    exact ⟨hy.1.1, by rw [← hy.1.2, hy.2]⟩
  · rintro ⟨h1, h2⟩
    exact ⟨_, by
      simp only [Set.mem_inter_iff, CD.fibDerivGraph, Set.mem_setOf_eq, projLast,
        Fin.init_snoc, Fin.snoc_last]
      exact ⟨⟨h1, rfl⟩, h2⟩⟩

/-- **The vanishing loci are `Ω`-definable** (given the fibre-derivative graph). -/
theorem sliceZero_mem_of_fibDerivGraph (S : SOMin) (p F0 : ℕ)
    (h : ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ), ∀ (D j : ℕ) {f : (Fin p → ℝ) → ℝ → ℝ},
      graphFam f ∈ S.Ω F0 D (p + 1 + 1) →
        CD.fibDerivGraph f j ∈ S.Ω a (MvPolynomial.eval ![D, j] b) (p + 2)) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ), ∀ (D j : ℕ) {f : (Fin p → ℝ) → ℝ → ℝ},
      graphFam f ∈ S.Ω F0 D (p + 1 + 1) →
        sliceZero f j ∈ S.Ω a (MvPolynomial.eval ![D, j] b) (p + 1) := by
  obtain ⟨a, b, hb⟩ := h
  refine ⟨max a (p + 2) + 2, b + 1, ?_⟩
  intro D j f hf
  have h₁ : CD.fibDerivGraph f j ∈ S.Ω (max a (p + 2)) (MvPolynomial.eval ![D, j] b) (p + 2) :=
    mono_F_le S (hb D j hf) (le_max_left _ _)
  have h₂ : {z : Fin (p + 2) → ℝ | z (Fin.last (p + 1)) = 0} ∈
      S.Ω (max a (p + 2)) 1 (p + 2) := by
    have h0 : {z : Fin (p + 2) → ℝ | MvPolynomial.eval z
        (MvPolynomial.X (Fin.last (p + 1)) : MvPolynomial (Fin (p + 2)) ℝ) = 0} ∈
        S.Ω (p + 2) 1 (p + 2) := by
      have h' := S.hyp (p + 2) (MvPolynomial.X (Fin.last (p + 1)) :
        MvPolynomial (Fin (p + 2)) ℝ)
      rwa [MvPolynomial.totalDegree_X] at h'
    have h'' : {z : Fin (p + 2) → ℝ | z (Fin.last (p + 1)) = 0} ∈
        S.Ω (p + 2) 1 (p + 2) := by
      convert h0 using 1
      ext z; simp
    exact mono_F_le S h'' (le_max_right _ _)
  have h₃ : (⋂ i : Fin 2, (if i = 0 then CD.fibDerivGraph f j
      else {z : Fin (p + 2) → ℝ | z (Fin.last (p + 1)) = 0})) ∈
      S.Ω (max a (p + 2) + 1)
        (∑ i : Fin 2, (if i = 0 then MvPolynomial.eval ![D, j] b else 1)) (p + 2) :=
    S.inter (fun i : Fin 2 => if i = 0 then MvPolynomial.eval ![D, j] b else 1)
      (fun i : Fin 2 => if i = 0 then CD.fibDerivGraph f j
        else {z : Fin (p + 2) → ℝ | z (Fin.last (p + 1)) = 0})
      (by intro i; fin_cases i <;> simpa using ‹_›)
  have h₄ := S.proj h₃
  have hsplit : (⋂ i : Fin 2, (if i = 0 then CD.fibDerivGraph f j
      else {z : Fin (p + 2) → ℝ | z (Fin.last (p + 1)) = 0})) =
      CD.fibDerivGraph f j ∩ {z : Fin (p + 2) → ℝ | z (Fin.last (p + 1)) = 0} := by
    ext z
    simp [Fin.forall_fin_two]
  rw [hsplit] at h₄
  have hset : projLast (CD.fibDerivGraph f j ∩
      {z : Fin (p + 2) → ℝ | z (Fin.last (p + 1)) = 0}) = sliceZero f j := rfl
  rw [hset] at h₄
  refine mono_FD_le S h₄ (by omega) ?_
  have hsum : (∑ i : Fin 2, (if i = 0 then MvPolynomial.eval ![D, j] b else 1)) =
      MvPolynomial.eval ![D, j] b + 1 := by
    rw [Fin.sum_univ_two]; simp
  rw [hsum, MvPolynomial.eval_add]
  simp

/-- The strip is `Ω`-definable with format and degree independent of `D` and `r`. -/
theorem strip_mem_y (S : SOMin) (p : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ D r : ℕ, strip p ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (p + 1) := by
  classical
  refine ⟨p + 4, MvPolynomial.C 6, ?_⟩
  intro D r
  have h1 : {z : Fin (p + 1) → ℝ | 0 < z (Fin.last p)} ∈
      S.Ω (p + 1 + 2) 3 (p + 1) := by
    have h := WilG1.Calc.pos_mem (S := S) D
      (MvPolynomial.X (Fin.last p) : MvPolynomial (Fin (p + 1)) ℝ)
    have hset : {x : Fin (p + 1) → ℝ | 0 < MvPolynomial.eval x
        (MvPolynomial.X (Fin.last p) : MvPolynomial (Fin (p + 1)) ℝ)}
        = {z : Fin (p + 1) → ℝ | 0 < z (Fin.last p)} := by
      ext z; simp
    rw [hset] at h
    refine mono_FD_le S h le_rfl ?_
    simp only [Polynomial.eval_C]
    have : (MvPolynomial.X (Fin.last p) : MvPolynomial (Fin (p + 1)) ℝ).totalDegree + 2 ≤ 3 := by
      rw [MvPolynomial.totalDegree_X]
    omega
  have h2 : {z : Fin (p + 1) → ℝ | z (Fin.last p) < 1} ∈
      S.Ω (p + 1 + 2) 3 (p + 1) := by
    have h := WilG1.Calc.pos_mem (S := S) D
      (1 - MvPolynomial.X (Fin.last p) : MvPolynomial (Fin (p + 1)) ℝ)
    have hset : {x : Fin (p + 1) → ℝ | 0 < MvPolynomial.eval x
        (1 - MvPolynomial.X (Fin.last p) : MvPolynomial (Fin (p + 1)) ℝ)}
        = {z : Fin (p + 1) → ℝ | z (Fin.last p) < 1} := by
      ext z
      simp only [Set.mem_setOf_eq]
      rw [show MvPolynomial.eval z (1 - MvPolynomial.X (Fin.last p) :
        MvPolynomial (Fin (p + 1)) ℝ) = 1 - z (Fin.last p) by simp]
      constructor <;> intro h <;> linarith
    rw [hset] at h
    have htd : (1 - MvPolynomial.X (Fin.last p) :
        MvPolynomial (Fin (p + 1)) ℝ).totalDegree ≤ 1 := by
      refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
      rw [max_le_iff]
      exact ⟨by simp, by rw [MvPolynomial.totalDegree_X]⟩
    refine mono_FD_le S h le_rfl ?_
    simp only [Polynomial.eval_C]
    omega
  have h3 : (⋂ i : Fin 2, (if i = 0 then {z : Fin (p + 1) → ℝ | 0 < z (Fin.last p)}
      else {z : Fin (p + 1) → ℝ | z (Fin.last p) < 1})) ∈
      S.Ω (p + 1 + 2 + 1) (3 + 3) (p + 1) :=
    S.inter (fun _ : Fin 2 => 3)
      (fun i : Fin 2 => if i = 0 then {z : Fin (p + 1) → ℝ | 0 < z (Fin.last p)}
        else {z : Fin (p + 1) → ℝ | z (Fin.last p) < 1})
      (by intro i; fin_cases i <;> simpa using ‹_›)
  have hset : (⋂ i : Fin 2, (if i = 0 then {z : Fin (p + 1) → ℝ | 0 < z (Fin.last p)}
      else {z : Fin (p + 1) → ℝ | z (Fin.last p) < 1})) = strip p := by
    ext z
    simp only [Set.mem_iInter, Fin.forall_fin_two, Set.mem_setOf_eq, strip, I,
      Set.mem_Ioo]
    exact ⟨fun h => h, fun h => h⟩
  rw [hset] at h3
  refine mono_FD_le S h3 (by omega) ?_
  simp [Polynomial.eval_C]

/-! ## 2. The refinement family -/

/-- The refinement family attached to a family `F`: the member indexed by `(i, 0)` is the
slice-`C^{r+1}`-bad locus of `F i`, and the member indexed by `(i, j+1)` is the locus where the
`j`-th slice derivative of `F i` exists and vanishes (`j ≤ r+1`). -/
def refFam {k : ℕ} (r : ℕ) (F : Fin k → (Fin p → ℝ) → ℝ → ℝ) :
    Fin k × Fin (r + 3) → Set (Fin (p + 1) → ℝ) :=
  fun it => if (it.2 : ℕ) = 0 then (sliceCj (F it.1) (r + 1))ᶜ
    else sliceZero (F it.1) ((it.2 : ℕ) - 1)

theorem refFam_zero {k : ℕ} (r : ℕ) (F : Fin k → (Fin p → ℝ) → ℝ → ℝ) (i : Fin k) :
    refFam r F (i, 0) = (sliceCj (F i) (r + 1))ᶜ := by
  simp [refFam]

theorem refFam_succ {k : ℕ} (r : ℕ) (F : Fin k → (Fin p → ℝ) → ℝ → ℝ) (i : Fin k)
    (j : Fin (r + 2)) :
    refFam r F (i, j.succ) = sliceZero (F i) (j : ℕ) := by
  have h : ((j.succ : Fin (r + 3)) : ℕ) = (j : ℕ) + 1 := rfl
  simp only [refFam, h, Nat.add_sub_cancel]
  rw [if_neg (by omega)]

/-- Every member of the refinement family is `Ω`-definable with a format independent of `D`,
`r` and `k` and a degree polynomial in `D` and `r`. -/
theorem refFam_mem (S : SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) (p F0 : ℕ) :
    ∃ (F' : ℕ) (B : MvPolynomial (Fin 2) ℕ),
      ∀ (D r k : ℕ) (F : Fin k → (Fin p → ℝ) → ℝ → ℝ),
        (∀ i, graphFam (F i) ∈ S.Ω F0 D (p + 1 + 1)) →
        ∀ it : Fin k × Fin (r + 3),
          refFam r F it ∈ S.Ω F' (MvPolynomial.eval ![D, r] B) (p + 1) := by
  classical
  obtain ⟨aC, bC, hC⟩ := CD.sliceContDiffAt_mem S hcd hder p F0
  obtain ⟨aZ, bZ, hZ⟩ := CD.fibDerivGraph_mem S hcd hder p F0
  obtain ⟨aSZ, bSZ, hSZ⟩ := sliceZero_mem_of_fibDerivGraph S p F0 (by
    refine ⟨aZ, bZ, ?_⟩
    intro D j f hf
    show {w : Fin (p + 2) → ℝ |
        ContDiffAt ℝ j (fun x : ℝ => f (Fin.init (Fin.init w)) x) ((Fin.init w) (Fin.last p)) ∧
          w (Fin.last (p + 1)) = iteratedDeriv j (fun x : ℝ => f (Fin.init (Fin.init w)) x)
            ((Fin.init w) (Fin.last p))} ∈ S.Ω aZ (MvPolynomial.eval ![D, j] bZ) (p + 2)
    exact hZ D j hf)
  obtain ⟨bC', hbC'⟩ := exists_eval_shift bC
  obtain ⟨bSZ', hbSZ'⟩ := exists_eval_shift bSZ
  refine ⟨max (aC + 1) aSZ, bC' + bSZ', ?_⟩
  intro D r k F hF it
  rcases Fin.eq_zero_or_eq_succ it.2 with h0 | ⟨j, hj⟩
  · have hit : it = (it.1, 0) := Prod.ext rfl (by rw [h0])
    rw [hit, refFam_zero]
    have hmem : sliceCj (F it.1) (r + 1) ∈
        S.Ω aC (MvPolynomial.eval ![D, r + 1] bC) (p + 1) := hC D (r + 1) (hF it.1)
    rw [hbC' D r] at hmem
    refine mono_FD_le S (S.compl hmem) (by omega) ?_
    rw [MvPolynomial.eval_add]
    exact Nat.le_add_right _ _
  · have hit : it = (it.1, j.succ) := Prod.ext rfl (by rw [← hj])
    rw [hit, refFam_succ]
    have hmem : sliceZero (F it.1) (j : ℕ) ∈
        S.Ω aSZ (MvPolynomial.eval ![D, (j : ℕ)] bSZ) (p + 1) := hSZ D (j : ℕ) (f := F it.1) (hF it.1)
    refine mono_FD_le S hmem (by omega) ?_
    have hj' : (j : ℕ) ≤ r + 1 := by have := j.isLt; omega
    have h1 := mvpoly_eval_mono (D := D) (j := (j : ℕ)) (r := r + 1) bSZ hj'
    rw [hbSZ' D r] at h1
    rw [MvPolynomial.eval_add]
    exact le_trans h1 (Nat.le_add_left _ _)

/-! ## 3. The dichotomy -/

/-- A cell contained in a slice-bad locus has subsingleton fibres: a non-trivial fibre is an
interval, hence contains `x < z < y` whenever it contains two distinct points, and is therefore
infinite — but it is also contained in the finite bad locus of the slice. -/
theorem fibre_subsingleton_of_bad (S : SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv)
    {F0 D0 r : ℕ} {f : (Fin p → ℝ) → ℝ → ℝ}
    (hf : graphFam f ∈ S.Ω F0 D0 (p + 1 + 1))
    {κ : Set (Fin (p + 1) → ℝ)} (hcell : WilkiesDesign.IsCell (p + 1) κ)
    (hbad : κ ⊆ (sliceCj f (r + 1))ᶜ) (l : Fin p → ℝ) :
    (fibre κ l).Subsingleton := by
  change ({y : ℝ | Fin.snoc l y ∈ κ}).Subsingleton
  have hsub : {y : ℝ | Fin.snoc l y ∈ κ} ⊆
      {y : ℝ | ¬ ContDiffAt ℝ (↑(r + 1)) (fun t : ℝ => f l t) y} := by
    intro y hy
    have h := hbad hy
    rw [Set.mem_compl_iff] at h
    rw [mem_sliceCj] at h
    simp only [Fin.init_snoc, Fin.snoc_last] at h
    exact h
  have hfin : ({y : ℝ | Fin.snoc l y ∈ κ}).Finite :=
    (CD.slice_bad_finite S hcd hder f hf l (r + 1)).subset hsub
  rcases isCell_fiber p hcell l with ⟨x, hx⟩ | ⟨a, b, hb⟩
  · rw [hx]; exact Set.subsingleton_singleton
  · rw [Set.Subsingleton]
    intro x hx' y hy'
    rw [hb] at hx' hy'
    by_contra hxy
    rcases lt_or_gt_of_ne hxy with hlt | hlt
    · have hI : Set.Ioo x y ⊆ {z : ℝ | Fin.snoc l z ∈ κ} := by
        intro z hz
        rw [hb]
        exact ⟨lt_trans hx'.1 (EReal.coe_lt_coe_iff.mpr hz.1),
          lt_trans (EReal.coe_lt_coe_iff.mpr hz.2) hy'.2⟩
      exact Set.Ioo_infinite hlt (hfin.subset hI)
    · have hI : Set.Ioo y x ⊆ {z : ℝ | Fin.snoc l z ∈ κ} := by
        intro z hz
        rw [hb]
        exact ⟨lt_trans hy'.1 (EReal.coe_lt_coe_iff.mpr hz.1),
          lt_trans (EReal.coe_lt_coe_iff.mpr hz.2) hx'.2⟩
      exact Set.Ioo_infinite hlt (hfin.subset hI)

/-- The `j`-th derivative of a `C^n` function is continuous on an open set, for `j ≤ n`. -/
theorem continuousOn_iteratedDeriv_le {n j : ℕ} {f : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hf : ContDiffOn ℝ n f s) (hj : j ≤ n) : ContinuousOn (iteratedDeriv j f) s := by
  have h1 : ContinuousOn (iteratedDerivWithin j f s) s :=
    ContDiffOn.continuousOn_iteratedDerivWithin hf (by exact_mod_cast hj) hs.uniqueDiffOn
  exact h1.congr fun x hx => ((iteratedDerivWithin_of_isOpen (n := j) hs) hx).symm

/-- `Disjoint s tᶜ` gives `s ⊆ t`. -/
theorem subset_of_disjoint_compl {α : Type*} {s t : Set α} (h : Disjoint s tᶜ) : s ⊆ t :=
  fun x hx => by
    by_contra hxt
    exact (Set.disjoint_left.mp h hx) (by simpa using hxt)

/-- The fibres of `κ ∩ strip` are points or intervals, for a cell `κ`. -/
theorem fibre_structure_inter_strip {κ : Set (Fin (p + 1) → ℝ)}
    (hcell : WilkiesDesign.IsCell (p + 1) κ) (l : Fin p → ℝ) :
    (fibre (κ ∩ strip p) l).Subsingleton ∨ ∃ A B : ℝ, fibre (κ ∩ strip p) l = Set.Ioo A B := by
  have hfib_eq : fibre (κ ∩ strip p) l = {y : ℝ | Fin.snoc l y ∈ κ} ∩ I := by
    ext y
    simp only [fibre, Set.mem_inter_iff, Set.mem_setOf_eq, strip_mem_iff_snoc]
  rcases isCell_fiber p hcell l with ⟨x, hx⟩ | ⟨a, b, hb⟩
  · rw [hfib_eq, hx]
    exact Or.inl (fun a ha b hb' =>
      (Set.mem_singleton_iff.mp (Set.inter_subset_left ha)).trans
        (Set.mem_singleton_iff.mp (Set.inter_subset_left hb')).symm)
  · rcases CD.fibre_inter_I (s := {y : ℝ | Fin.snoc l y ∈ κ}) (Or.inr ⟨a, b, hb⟩) with
      hss | ⟨A, B, hAB⟩
    · exact Or.inl (by rw [hfib_eq]; exact hss)
    · exact Or.inr ⟨A, B, by rw [hfib_eq]; exact hAB⟩

theorem goodCell_of_refine {k r : ℕ} {F : Fin k → (Fin p → ℝ) → ℝ → ℝ}
    {κ : Set (Fin (p + 1) → ℝ)}
    (hfib : ∀ l : Fin p → ℝ,
      (fibre κ l).Subsingleton ∨ ∃ A B : ℝ, fibre κ l = Set.Ioo A B)
    (hstrip : κ ⊆ strip p)
    (hgood : ∀ i, κ ⊆ sliceCj (F i) (r + 1))
    (hZ : ∀ (i : Fin k) (j : ℕ), j ≤ r + 1 →
      Disjoint κ (sliceZero (F i) j) ∨ κ ⊆ sliceZero (F i) j) :
    GoodCell_w k r F κ := by
  have hCj : ∀ (i : Fin k) (l : Fin p → ℝ) (x : ℝ), x ∈ fibre κ l →
      ContDiffAt ℝ (↑r + 1) (fun y : ℝ => F i l y) x := by
    intro i l x hx
    have h := hgood i hx
    have h2 : ContDiffAt ℝ (↑(r + 1)) (fun y : ℝ => F i l y) x := by
      simpa only [mem_sliceCj, Fin.init_snoc, Fin.snoc_last] using h
    refine ContDiffAt.of_le h2 ?_
    rw [show ((r : WithTop ℕ∞) + 1) = ((r + 1 : ℕ) : WithTop ℕ∞) by push_cast; ring]
  refine ⟨hstrip, hfib, ?_⟩
  intro i l
  constructor
  · rcases hfib l with hss | ⟨A, B, hAB⟩
    · rcases Set.Subsingleton.eq_empty_or_singleton hss with hE | ⟨A, hA⟩
      · rw [hE]; exact contDiffOn_empty
      · rw [show fibre κ l = {A} from hA]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact contDiffWithinAt_singleton
    · have hfibAB : fibre κ l = Set.Ioo A B := hAB
      rw [hfibAB]
      intro x hx
      exact (hCj i l x (by rw [hfibAB]; exact hx)).contDiffWithinAt
  · intro j hj
    rcases hfib l with hss | ⟨A, B, hAB⟩
    · rcases Set.Subsingleton.eq_empty_or_singleton hss with hE | ⟨A, hA⟩
      · rw [hE]
        left; intro y hy; exact absurd hy (Set.notMem_empty y)
      · rw [show fibre κ l = {A} from hA]
        rcases le_total 0 (iteratedDeriv j (fun y : ℝ => F i l y) A) with h | h
        · left; intro y hy; rw [Set.mem_singleton_iff] at hy; rw [hy]; exact h
        · right; intro y hy; rw [Set.mem_singleton_iff] at hy; rw [hy]; exact h
    · have hfibAB : fibre κ l = Set.Ioo A B := hAB
      rw [hfibAB]
      by_cases hAB' : A < B
      · by_cases hsub : κ ⊆ sliceZero (F i) j
        · left
          intro y hy
          have hyf : y ∈ fibre κ l := by rw [hfibAB]; exact hy
          have hyκ : Fin.snoc l y ∈ κ := hyf
          have h0 := (mem_sliceZero.mp (hsub hyκ)).2
          simp only [Fin.init_snoc, Fin.snoc_last] at h0
          rw [h0]
        · have hdisj : Disjoint κ (sliceZero (F i) j) := (hZ i j hj).resolve_right hsub
          have hne : ∀ y ∈ Set.Ioo A B, iteratedDeriv j (fun y : ℝ => F i l y) y ≠ 0 := by
            intro y hy h0
            have hyf : y ∈ fibre κ l := by rw [hfibAB]; exact hy
            have hyκ : Fin.snoc l y ∈ κ := hyf
            have hmem : Fin.snoc l y ∈ sliceZero (F i) j := by
              rw [mem_sliceZero]
              refine ⟨?_, ?_⟩
              · simpa only [Fin.init_snoc, Fin.snoc_last] using
                  (ContDiffAt.of_le (hCj i l y hyf)
                    (show (j : WithTop ℕ∞) ≤ ((r + 1 : ℕ) : WithTop ℕ∞) by exact_mod_cast hj))
              · simpa only [Fin.init_snoc, Fin.snoc_last] using h0
            exact (Set.disjoint_left.mp hdisj hyκ) hmem
          have hcont : ContinuousOn (iteratedDeriv j (fun y : ℝ => F i l y)) (Set.Ioo A B) := by
            have hcd : ContDiffOn ℝ (r + 1) (fun y : ℝ => F i l y) (Set.Ioo A B) :=
              fun y hy => (hCj i l y (by rw [hfibAB]; exact hy)).contDiffWithinAt
            exact continuousOn_iteratedDeriv_le isOpen_Ioo hcd hj
          exact signConst_ivt hAB' _ hcont hne
      · left
        intro y hy
        exact absurd (lt_of_lt_of_le hy.2 (le_of_not_gt hAB')) (not_lt_of_gt hy.1)

/-! ## 4. The cell decomposition -/

theorem cellDecomp_exists (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) (p : ℕ) : Work.WilG4a.CellDecomp S p := by
  intro F0
  obtain ⟨F', B, hB⟩ := refFam_mem S hcd hder p F0
  obtain ⟨aS, bS, hS⟩ := strip_mem_y S p
  obtain ⟨aR, bR, cR, hR⟩ := CD.cellDecomp_refining S hcd (p + 1) (max F' aS)
  obtain ⟨cc, hcc⟩ := count_poly_comp bR (B + bS)
  refine ⟨max aR aS + 1, Polynomial.eval₂ MvPolynomial.C (B + bS) cR + bS, cc, ?_⟩
  intro D r k Λ F hF hI
  let X : Fin k × Fin (r + 3) → Set (Fin (p + 1) → ℝ) := refFam r F
  have hX : ∀ it, X it = refFam r F it := fun it => rfl
  have hfam : ∀ it : Fin k × Fin (r + 3),
      X it ∈ S.Ω (max F' aS) (MvPolynomial.eval ![D, r] (B + bS)) (p + 1) := by
    intro it
    rw [hX it]
    refine mono_FD_le S (hB D r k F hF it) (le_max_left _ _) ?_
    rw [MvPolynomial.eval_add]
    exact Nat.le_add_right _ _
  obtain ⟨m, hm, κ, hmem, hcell, hcover, hrefine⟩ :=
    hR (D := MvPolynomial.eval ![D, r] (B + bS)) (ι := Fin k × Fin (r + 3)) (X := X) hfam
  refine ⟨m, ?_, fun σ => κ σ ∩ strip p, ?_, ?_, ?_⟩
  · have hcard : Fintype.card (Fin k × Fin (r + 3)) = k * (r + 3) := by
      rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    have hm' : m ≤ MvPolynomial.eval
        ![MvPolynomial.eval ![D, r] (B + bS), 2 * (k * (r + 3))] bR := by
      have hmono : MvPolynomial.eval
            ![MvPolynomial.eval ![D, r] (B + bS), k * (r + 3)] bR ≤
          MvPolynomial.eval ![MvPolynomial.eval ![D, r] (B + bS), 2 * (k * (r + 3))] bR :=
        mvpoly_eval_mono (D := MvPolynomial.eval ![D, r] (B + bS)) (j := k * (r + 3))
          (r := 2 * (k * (r + 3))) bR (by omega)
      rw [hcard] at hm
      exact le_trans hm hmono
    have hcc' : (MvPolynomial.eval
        ![MvPolynomial.eval ![D, r] (B + bS), 2 * (k * (r + 3))] bR : ℝ) ≤
        MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ)] cc := hcc D r k
    calc (m : ℝ) ≤ (MvPolynomial.eval
          ![MvPolynomial.eval ![D, r] (B + bS), 2 * (k * (r + 3))] bR : ℝ) := by
          exact_mod_cast hm'
      _ ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ)] cc := hcc'
  · intro σ
    have h1 : κ σ ∈ S.Ω aR (cR.eval (MvPolynomial.eval ![D, r] (B + bS))) (p + 1) := hmem σ
    have h2 : strip p ∈ S.Ω aS (MvPolynomial.eval ![D, r] bS) (p + 1) := hS D r
    have h3 := S.inter (F := max aR aS) (n := p + 1) (k := 2)
      (D := fun i : Fin 2 => if i = 0 then cR.eval (MvPolynomial.eval ![D, r] (B + bS))
        else MvPolynomial.eval ![D, r] bS)
      (A := fun i : Fin 2 => if i = 0 then κ σ else strip p)
      (by
        intro i
        fin_cases i
        · simpa using mono_F_le S h1 (le_max_left _ _)
        · simpa using mono_F_le S h2 (le_max_right _ _))
    have hset : (⋂ i : Fin 2, (if i = 0 then κ σ else strip p)) = κ σ ∩ strip p := by
      ext z; simp [Fin.forall_fin_two]
    rw [hset] at h3
    have hdeg : (∑ i : Fin 2, (if i = 0 then cR.eval (MvPolynomial.eval ![D, r] (B + bS))
        else MvPolynomial.eval ![D, r] bS)) =
        MvPolynomial.eval ![D, r] (Polynomial.eval₂ MvPolynomial.C (B + bS) cR + bS) := by
      have hB' : cR.eval (MvPolynomial.eval ![D, r] (B + bS))
          = MvPolynomial.eval ![D, r] (Polynomial.eval₂ MvPolynomial.C (B + bS) cR) :=
        (CD.eval_eval₂_C (B + bS) cR D r).symm
      rw [Fin.sum_univ_two, hB', MvPolynomial.eval_add]
      simp
    rw [hdeg] at h3
    exact h3
  · intro σ
    by_cases hbad : ∃ i : Fin k, κ σ ⊆ (sliceCj (F i) (r + 1))ᶜ
    · right
      intro l
      exact fun x hx y hy =>
        fibre_subsingleton_of_bad S hcd hder (hF hbad.choose) (hcell σ) hbad.choose_spec l
          (Set.inter_subset_left hx) (Set.inter_subset_left hy)
    · left
      have hgoodi : ∀ i : Fin k, κ σ ⊆ sliceCj (F i) (r + 1) := by
        intro i
        rcases hrefine (i, 0) σ with hdis | hsub
        · rw [hX, refFam_zero] at hdis
          exact subset_of_disjoint_compl hdis
        · rw [hX, refFam_zero] at hsub
          exact absurd hsub (fun hh => hbad ⟨i, hh⟩)
      refine goodCell_of_refine (F := F) (κ := κ σ ∩ strip p)
        (fun l => fibre_structure_inter_strip (hcell σ) l) Set.inter_subset_right ?_ ?_
      · intro i z hz
        exact hgoodi i (Set.inter_subset_left hz)
      · intro i j hj
        have h1 := hrefine (i, (⟨j, by omega⟩ : Fin (r + 2)).succ) σ
        rw [hX, refFam_succ] at h1
        rcases h1 with hdis | hsub
        · exact Or.inl (hdis.mono_left Set.inter_subset_left)
        · exact Or.inr (Set.inter_subset_left.trans hsub)
  · intro l hl x hx
    obtain ⟨σ, hσ⟩ := hcover (Fin.snoc l x)
    refine ⟨σ, hσ, ?_⟩
    rwa [strip_mem_iff_snoc]

end Work.WilG4a
