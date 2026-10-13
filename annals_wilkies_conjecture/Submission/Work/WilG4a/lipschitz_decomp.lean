import Mathlib
import Submission.Work.WilG4a.LipChartsDefs
import Submission.Work.WilG4a.Cells
import Submission.Work.WilG4a.lip_loci_defs
import Submission.Work.WilG4a.exists_cell_partition_refining
import Submission.Work.WilG4a.degree_poly_comp
import Submission.Work.WilG4a.sliceDerivContAlt
import Submission.Work.WilG4a.domLociAlt
import Submission.Work.WilG4a.isCell_fibre_real
import Submission.Work.WilG4a.eval_pair_bound

/-!
# BNZ Lemma 5.3 (`n = 1`): the Lipschitz cell decomposition

The theorem `Work.WilG4a.lipschitz_decomp` is Piece 2 of the `n = 1` family lemma
(`lipschitz_charts`): a sharp cell decomposition of `R^{p+1}` (parameters times the
variable) compatible with the Lipschitz loci `(sliceDerivCont f)^c`, `domSet f g`,
`posSet f`, `negSet f` and the strip `{0 < x < 1}`; each cell is either a `GoodCell`
for a chosen dominating index or has all fibres subsingletons.

The individual `Omega`-membership statements of the loci are proved in the sibling
modules `sliceDerivCont_mem`, `domLoci_mem` and combined here; the dichotomy between the
two kinds of cells is proved in `cell_dichotomy` below, using `SliceTame` to force the
degeneracy of the cells lying inside the bad loci and the one-variable fibre shape
(`isCell_fibre_real`).
-/

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG4a
open WilkiesConjecture WilkiesDesign

variable {p : ℕ}

theorem ld_a (f : (Fin p → ℝ) → ℝ → ℝ) : sliceDerivCont f ⊆ sliceDiff f := by
  intro z hz
  obtain ⟨s, hs, _⟩ := hz
  exact hs.differentiableAt

theorem update_last_snoc (l : Fin p → ℝ) (x x' : ℝ) :
    Function.update (Fin.snoc l x : Fin (p+1) → ℝ) (Fin.last p) x' = Fin.snoc l x' := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · simp [Function.update, Fin.snoc_castSucc]
  · simp [Function.update]

theorem sliceFun_update (f : (Fin p → ℝ) → ℝ → ℝ) (z : Fin (p+1) → ℝ) (a : ℝ) :
    sliceFun f (Function.update z (Fin.last p) a) = sliceFun f z := by
  funext y
  simp only [sliceFun]
  congr 1
  funext i
  by_cases hi : i = Fin.last p
  · subst hi; simp [Function.update]
  · simp [Function.update, hi]

theorem ld_c (f : (Fin p → ℝ) → ℝ → ℝ) (l : Fin p → ℝ) (x' : ℝ) :
    sliceFun f (Fin.snoc l x') = fun y : ℝ => f l y := by
  funext y
  have hupd : Function.update (Fin.snoc l x' : Fin (p+1) → ℝ) (Fin.last p) y = Fin.snoc l y :=
    update_last_snoc l x' y
  rw [sliceFun, hupd, famFun_apply]

theorem ld_c' (f : (Fin p → ℝ) → ℝ → ℝ) (l : Fin p → ℝ) (x' : ℝ) (s : ℝ) :
    IsSliceDeriv f (Fin.snoc l x') s ↔ HasDerivAt (f l) s x' := by
  rw [IsSliceDeriv, ld_c, Fin.snoc_last]

theorem ld_bad (f : (Fin p → ℝ) → ℝ → ℝ) (l : Fin p → ℝ) (x : ℝ) :
    (Fin.snoc l x ∈ (sliceDerivCont f)ᶜ) ↔
      ¬ (DifferentiableAt ℝ (f l) x ∧
        ∃ s : ℝ, HasDerivAt (f l) s x ∧
          ∀ ε > 0, ∃ δ > 0, ∀ x' : ℝ, |x' - x| < δ →
            ∃ s' : ℝ, HasDerivAt (f l) s' x' ∧ |s' - s| < ε) := by
  have key : sliceDerivCont f (Fin.snoc l x) ↔
      (DifferentiableAt ℝ (f l) x ∧
        ∃ s : ℝ, HasDerivAt (f l) s x ∧
          ∀ ε > 0, ∃ δ > 0, ∀ x' : ℝ, |x' - x| < δ →
            ∃ s' : ℝ, HasDerivAt (f l) s' x' ∧ |s' - s| < ε) := by
    rw [sliceDerivCont]
    constructor
    · rintro ⟨s, hs, hc⟩
      have hs' : HasDerivAt (f l) s x := (ld_c' f l x s).mp hs
      refine ⟨hs'.differentiableAt, s, hs', ?_⟩
      intro ε hε
      obtain ⟨δ, hδ, hδ'⟩ := hc ε hε
      refine ⟨δ, hδ, fun x' hx' => ?_⟩
      obtain ⟨s', hs', hc'⟩ := hδ' x' (by simpa [Fin.snoc_last] using hx')
      exact ⟨s', (ld_c' f l x' s').mp (by rwa [update_last_snoc] at hs'), hc'⟩
    · rintro ⟨hd, s, hs, hc⟩
      refine ⟨s, (ld_c' f l x s).mpr hs, ?_⟩
      intro ε hε
      obtain ⟨δ, hδ, hδ'⟩ := hc ε hε
      refine ⟨δ, hδ, fun x' hx' => ?_⟩
      obtain ⟨s', hs', hc'⟩ := hδ' x' (by simpa [Fin.snoc_last] using hx')
      exact ⟨s', by rw [update_last_snoc, ld_c']; exact hs', hc'⟩
  rw [Set.mem_compl_iff]
  exact not_congr key

theorem isSliceDeriv_unique (f : (Fin p → ℝ) → ℝ → ℝ) (z : Fin (p+1) → ℝ) {s t : ℝ}
    (hs : IsSliceDeriv f z s) (ht : IsSliceDeriv f z t) : s = t :=
  hs.unique ht

-- interval contained in a set of empty interior is empty
theorem eq_empty_of_subset_interior_empty {a b : ℝ} {A : Set ℝ} (h : Set.Ioo a b ⊆ A)
    (hint : interior A = ∅) : a ≥ b := by
  by_contra hlt
  have hlt' : a < b := not_le.mp hlt
  have : ((a + b) / 2) ∈ interior A :=
    interior_mono h (by rw [isOpen_Ioo.interior_eq]; exact ⟨by linarith, by linarith⟩)
  rw [hint] at this
  exact this





theorem subset_of_disjoint_compl_y {α : Type*} {A B : Set α} (h : Disjoint A Bᶜ) : A ⊆ B :=
  fun x hx => by
    by_contra hxB
    exact Set.disjoint_left.mp h hx hxB

theorem cell_dichotomy
    (S : WilkiesDesign.SOMin) (p F0 : ℕ) (htame : SliceTame S p F0)
    (hisCellReal : ∀ {C : Set (Fin (p+1) → ℝ)}, WilkiesDesign.IsCell (p+1) C → C ⊆ strip p →
      ∀ l : Fin p → ℝ, (fibre C l).Subsingleton ∨ ∃ a b : ℝ, fibre C l = Set.Ioo a b)
    (D k : ℕ) (F : Fin (k+1) → (Fin p → ℝ) → ℝ → ℝ)
    (hgraph : ∀ i, graphFam (F i) ∈ S.Ω F0 D (p + 1 + 1))
    (hid : F (Fin.last k) = (fun _ x => x))
    (m : ℕ) (κ : Fin m → Set (Fin (p+1) → ℝ))
    (hcellstrip : ∀ σ, (WilkiesDesign.IsCell (p+1) (κ σ) ∧ κ σ ⊆ strip p) ∨ κ σ = ∅)
    (hrefc : ∀ (σ : Fin m) (i : Fin (k+1)),
        Disjoint (κ σ) ((sliceDerivCont (F i))ᶜ) ∨ κ σ ⊆ (sliceDerivCont (F i))ᶜ)
    (hrefd : ∀ (σ : Fin m) (i j : Fin (k+1)),
        Disjoint (κ σ) (domSet (F i) (F j)) ∨ κ σ ⊆ domSet (F i) (F j))
    (hrefp : ∀ (σ : Fin m) (i : Fin (k+1)),
        Disjoint (κ σ) (posSet (F i)) ∨ κ σ ⊆ posSet (F i))
    (hrefn : ∀ (σ : Fin m) (i : Fin (k+1)),
        Disjoint (κ σ) (negSet (F i)) ∨ κ σ ⊆ negSet (F i)) :
    ∃ i₁ : Fin m → Fin (k+1),
      ∀ σ, GoodCell (k+1) F (κ σ) (i₁ σ) ∨ ∀ l, (fibre (κ σ) l).Subsingleton := by
  classical
  have key : ∀ σ, (∀ l, (fibre (κ σ) l).Subsingleton) ∨ ∃ i₁, GoodCell (k+1) F (κ σ) i₁ := by
    intro σ
    by_cases hdeg : ∀ l, (fibre (κ σ) l).Subsingleton
    · exact Or.inl hdeg
    · right
      obtain ⟨l₀, hns⟩ := not_forall.mp hdeg
      obtain ⟨hcell, hstrip⟩ : WilkiesDesign.IsCell (p+1) (κ σ) ∧ κ σ ⊆ strip p := by
        rcases hcellstrip σ with h | h
        · exact h
        · exfalso
          refine hns ?_
          rw [h]
          simp [fibre]
      obtain ⟨y₁, hy₁, y₂, hy₂, hne⟩ :
          ∃ y₁ ∈ fibre (κ σ) l₀, ∃ y₂ ∈ fibre (κ σ) l₀, y₁ ≠ y₂ := by
        by_contra hc
        apply hns
        intro x hx y hy
        by_contra hxy
        exact hc ⟨x, hx, y, hy, hxy⟩
      let z₀ : Fin (p+1) → ℝ := Fin.snoc l₀ y₁
      have hz₀ : z₀ ∈ κ σ := hy₁
      have hsc : ∀ i, κ σ ⊆ sliceDerivCont (F i) := by
        intro i
        rcases hrefc σ i with hdis | hsub
        · exact subset_of_disjoint_compl_y hdis
        · exfalso
          rcases hisCellReal hcell hstrip l₀ with hsub' | ⟨a, b, hab⟩
          · exact hns hsub'
          · have hablt : a < b := by
              by_contra h
              have h' : b ≤ a := not_lt.mp h
              have hy₁' : y₁ ∈ Set.Ioo a b := by rw [← hab]; exact hy₁
              exact absurd (by linarith [hy₁'.1, hy₁'.2, h']) (lt_irrefl y₁)
            have hbadsub : Set.Ioo a b ⊆ {x : ℝ | ¬ (DifferentiableAt ℝ (F i l₀) x ∧
                ∃ s : ℝ, HasDerivAt (F i l₀) s x ∧
                  ∀ ε > 0, ∃ δ > 0, ∀ x' : ℝ, |x' - x| < δ →
                    ∃ s' : ℝ, HasDerivAt (F i l₀) s' x' ∧ |s' - s| < ε)} := by
              intro y hy
              have hyfib : y ∈ fibre (κ σ) l₀ := by rw [hab]; exact hy
              have hmem : Fin.snoc l₀ y ∈ κ σ := hyfib
              exact (ld_bad (F i) l₀ y).mp (hsub hmem)
            exact absurd hablt (not_lt.mpr
              (eq_empty_of_subset_interior_empty hbadsub (htame D (hgraph i) l₀)))
      have hz₀sd : ∀ i, IsSliceDeriv (F i) z₀ (xDeriv (F i) z₀) :=
        fun i => ((ld_a (F i)) (hsc i hz₀)).hasDerivAt
      obtain ⟨i₁, _, himax⟩ := Finset.exists_max_image Finset.univ
        (fun i : Fin (k+1) => |xDeriv (F i) z₀|) Finset.univ_nonempty
      refine ⟨i₁, ?_, ?_, ?_, ?_, ?_⟩
      · intro j; exact Set.Subset.trans (hsc j) (ld_a (F j))
      · intro j; exact hsc j
      · intro j
        rcases hrefd σ j i₁ with hdis | hsub
        · exfalso
          refine (Set.disjoint_left.mp hdis) hz₀ ⟨xDeriv (F j) z₀, xDeriv (F i₁) z₀,
            hz₀sd j, hz₀sd i₁, ?_⟩
          exact himax j (Finset.mem_univ j)
        · exact hsub
      · have hsdne : xDeriv (F i₁) z₀ ≠ 0 := by
          have hle := himax (Fin.last k) (Finset.mem_univ _)
          have hlast : xDeriv (F (Fin.last k)) z₀ = 1 := by
            have hfun : sliceFun (F (Fin.last k)) z₀ = fun y : ℝ => y := by
              rw [show z₀ = Fin.snoc l₀ y₁ from rfl, hid, ld_c]
            rw [xDeriv, hfun]
            exact deriv_id (z₀ (Fin.last p))
          rw [hlast, abs_one] at hle
          intro h0
          rw [h0, abs_zero] at hle
          exact absurd hle (by norm_num)
        rcases lt_or_gt_of_ne hsdne with hneg | hpos
        · right
          rcases hrefn σ i₁ with hdis | hsub
          · exfalso
            exact (Set.disjoint_left.mp hdis) hz₀ ⟨xDeriv (F i₁) z₀, hz₀sd i₁, hneg⟩
          · exact hsub
        · left
          rcases hrefp σ i₁ with hdis | hsub
          · exfalso
            exact (Set.disjoint_left.mp hdis) hz₀ ⟨xDeriv (F i₁) z₀, hz₀sd i₁, hpos⟩
          · exact hsub
      · intro l
        exact hisCellReal hcell hstrip l
  have key2 : ∀ σ, ∃ i₁ : Fin (k+1),
      (∀ l, (fibre (κ σ) l).Subsingleton) ∨ GoodCell (k+1) F (κ σ) i₁ := by
    intro σ
    rcases key σ with h | ⟨i, hi⟩
    · exact ⟨Fin.last k, Or.inl h⟩
    · exact ⟨i, Or.inr hi⟩
  refine ⟨fun σ => Classical.choose (key2 σ), fun σ => ?_⟩
  exact (Classical.choose_spec (key2 σ)).elim Or.inr Or.inl


theorem poly_to_mv (q : Polynomial ℕ) :
    ∃ b : MvPolynomial (Fin 2) ℕ, ∀ D : ℕ, MvPolynomial.eval ![D, 1] b = q.eval D := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
      obtain ⟨bp, hbp⟩ := hp
      obtain ⟨bq, hbq⟩ := hq
      exact ⟨bp + bq, fun D => by
        rw [MvPolynomial.eval_add, hbp D, hbq D, Polynomial.eval_add]⟩
  | monomial n a =>
      exact ⟨MvPolynomial.C a * MvPolynomial.X 0 ^ n, fun D => by
        rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_pow, MvPolynomial.eval_X,
          Polynomial.eval_monomial]
        simp⟩

theorem empty_mem (S : WilkiesDesign.SOMin) {n D : ℕ} :
    (∅ : Set (Fin n → ℝ)) ∈ S.Ω (n + 1) D n := by
  have hmem : (∅ : Set (Fin n → ℝ)) = (Set.univ : Set (Fin n → ℝ))ᶜ := by simp
  rw [hmem]
  refine Work.WilG1.Omega.mono (S.compl ?_) le_rfl (Nat.zero_le D)
  have h := S.hyp n (0 : MvPolynomial (Fin n) ℝ)
  rw [MvPolynomial.totalDegree_zero] at h
  simpa using h

theorem card_idx (k : ℕ) :
    Fintype.card (Option (Sum (Fin (k+1) × Fin (k+1)) (Fin (k+1) × Fin 3)))
      = MvPolynomial.eval ![k, 1] (1 + (MvPolynomial.X 0 + 1)^2 +
          3 * (MvPolynomial.X 0 + 1) : MvPolynomial (Fin 2) ℕ) := by
  simp only [Fintype.card_option, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  simp [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_pow, MvPolynomial.eval_X]
  ring

theorem lipschitz_decomp_core
    (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv)
    (p F0 : ℕ) (htame : SliceTame S p F0)
    (hslice : ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (D : ℕ) {f : (Fin p → ℝ) → ℝ → ℝ},
      graphFam f ∈ S.Ω F0 D (p + 1 + 1) → sliceDerivCont f ∈ S.Ω a (b.eval D) (p + 1))
    (hdom : ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (D : ℕ) {f g : (Fin p → ℝ) → ℝ → ℝ},
      graphFam f ∈ S.Ω F0 D (p + 1 + 1) → graphFam g ∈ S.Ω F0 D (p + 1 + 1) →
      domSet f g ∈ S.Ω a (b.eval D) (p + 1) ∧
      posSet f ∈ S.Ω a (b.eval D) (p + 1) ∧
      negSet f ∈ S.Ω a (b.eval D) (p + 1))
    (hisCellReal : ∀ {C : Set (Fin (p+1) → ℝ)}, WilkiesDesign.IsCell (p+1) C → C ⊆ strip p →
      ∀ l : Fin p → ℝ, (fibre C l).Subsingleton ∨ ∃ a b : ℝ, fibre C l = Set.Ioo a b)
    (hbnd : ∀ bp Bp Fp : MvPolynomial (Fin 2) ℕ, ∃ cc : MvPolynomial (Fin 3) ℝ, ∀ D k : ℕ,
      (MvPolynomial.eval ![MvPolynomial.eval ![D, 1] Bp, MvPolynomial.eval ![k, 1] Fp] bp : ℝ) ≤
        MvPolynomial.eval ![(D : ℝ), (1 : ℝ), (k : ℝ)] cc) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (cc : MvPolynomial (Fin 3) ℝ),
      ∀ (D k : ℕ) (Λ : Set (Fin p → ℝ)) (F : Fin (k+1) → (Fin p → ℝ) → ℝ → ℝ),
        (∀ i, graphFam (F i) ∈ S.Ω F0 D (p + 1 + 1)) →
        (∀ i, ∀ l ∈ Λ, ∀ x ∈ I, F i l x ∈ I) →
        F (Fin.last k) = (fun _ x => x) →
        ∃ (m : ℕ), (m : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (1 : ℝ), (k : ℝ)] cc ∧
          ∃ (κ : Fin m → Set (Fin (p+1) → ℝ)) (i₁ : Fin m → Fin (k+1)),
            (∀ σ, κ σ ∈ S.Ω a (MvPolynomial.eval ![D, 1] b) (p + 1)) ∧
            (∀ σ, κ σ ⊆ strip p) ∧
            (∀ l ∈ Λ, ∀ x ∈ I, ∃ σ, Fin.snoc l x ∈ κ σ) ∧
            (∀ σ, GoodCell (k+1) F (κ σ) (i₁ σ) ∨
              ∀ l, (fibre (κ σ) l).Subsingleton) := by
  classical
  obtain ⟨a₁, b₁, h₁⟩ := hslice
  obtain ⟨a₂, b₂, h₂⟩ := hdom
  obtain ⟨B', hB'⟩ := poly_to_mv (b₁ + b₂ + Polynomial.C 6)
  set A : ℕ := max (max (a₁+1) a₂) (p + 4) with hA
  obtain ⟨a₀, b₀, c₀, H⟩ := exists_cell_partition_refining S hcd A (p + 1)
  obtain ⟨b, hb⟩ := degree_poly_comp B' c₀
  obtain ⟨cc, hcc⟩ := hbnd b₀ B' (1 + (MvPolynomial.X 0 + 1)^2 + 3 * (MvPolynomial.X 0 + 1))
  refine ⟨max a₀ (p + 2), b, cc, ?_⟩
  intro D k Λ F hΩ hI hid
  set BD : ℕ := (b₁ + b₂ + Polynomial.C 6).eval D with hBD
  have hB'D : MvPolynomial.eval ![D, 1] B' = BD := by rw [hB', hBD]
  have hBDval : BD = b₁.eval D + b₂.eval D + 6 := by
    rw [hBD]; simp [Polynomial.eval_add]
  have hb1le : b₁.eval D ≤ BD := by omega
  have hb2le : b₂.eval D ≤ BD := by omega
  have h6le : 6 ≤ BD := by omega
  have hdeg : c₀.eval BD = MvPolynomial.eval ![D, 1] b := by
    rw [hb D 1, hB'D]
  -- the loci, at format `A` and degree `BD`
  have hlocC : ∀ i : Fin (k+1), (sliceDerivCont (F i))ᶜ ∈ S.Ω A BD (p+1) := fun i =>
    Work.WilG1.Omega.mono (S.compl (h₁ D (hΩ i)))
      (le_trans (le_max_left _ _) (le_max_left _ _)) hb1le
  have hlocD : ∀ i j : Fin (k+1), domSet (F i) (F j) ∈ S.Ω A BD (p+1) := fun i j =>
    Work.WilG1.Omega.mono (h₂ D (hΩ i) (hΩ j)).1
      (le_trans (le_max_right _ _) (le_max_left _ _)) hb2le
  have hlocP : ∀ i : Fin (k+1), posSet (F i) ∈ S.Ω A BD (p+1) := fun i =>
    Work.WilG1.Omega.mono (h₂ D (hΩ i) (hΩ i)).2.1
      (le_trans (le_max_right _ _) (le_max_left _ _)) hb2le
  have hlocN : ∀ i : Fin (k+1), negSet (F i) ∈ S.Ω A BD (p+1) := fun i =>
    Work.WilG1.Omega.mono (h₂ D (hΩ i) (hΩ i)).2.2
      (le_trans (le_max_right _ _) (le_max_left _ _)) hb2le
  have hlocS : strip p ∈ S.Ω A BD (p+1) :=
    Work.WilG1.Omega.mono (strip_mem S p D) (le_max_right _ _) (by simpa using h6le)
  -- the family to refine against
  let Fd : MvPolynomial (Fin 2) ℕ := 1 + (MvPolynomial.X 0 + 1)^2 + 3 * (MvPolynomial.X 0 + 1)
  let ι := Option (Sum (Fin (k+1) × Fin (k+1)) (Fin (k+1) × Fin 3))
  let X : ι → Set (Fin (p+1) → ℝ) := fun t => match t with
    | none => strip p
    | some (Sum.inl (i, j)) => domSet (F i) (F j)
    | some (Sum.inr (i, j)) => if j = (0 : Fin 3) then (sliceDerivCont (F i))ᶜ
        else if j = (1 : Fin 3) then posSet (F i) else negSet (F i)
  have hX : ∀ t : ι, X t ∈ S.Ω A BD (p+1) := by
    intro t
    rcases t with _ | u
    · exact hlocS
    · rcases u with ⟨i, j⟩ | ⟨i, j⟩
      · exact hlocD i j
      · fin_cases j
        · exact hlocC i
        · exact hlocP i
        · exact hlocN i
  obtain ⟨m, hmc, κ, hκΩ, hκcell, hκcov, hκdisj, hκref⟩ := H BD ι X hX
  -- truncate to the strip
  let κ' : Fin m → Set (Fin (p+1) → ℝ) := fun σ => if κ σ ⊆ strip p then κ σ else ∅
  have hκ'strip : ∀ σ, κ' σ ⊆ strip p := by
    intro σ
    by_cases h : κ σ ⊆ strip p
    · rw [show κ' σ = κ σ from if_pos h]; exact h
    · rw [show κ' σ = ∅ from if_neg h]; exact Set.empty_subset _
  have hκ'Ω : ∀ σ, κ' σ ∈ S.Ω (max a₀ (p+2)) (MvPolynomial.eval ![D, 1] b) (p+1) := by
    intro σ
    by_cases h : κ σ ⊆ strip p
    · rw [show κ' σ = κ σ from if_pos h]
      exact Work.WilG1.Omega.mono (hκΩ σ) (le_max_left _ _) (le_of_eq hdeg)
    · rw [show κ' σ = ∅ from if_neg h]
      exact Work.WilG1.Omega.mono (empty_mem S (n := p+1) (D := c₀.eval BD))
        (le_max_right _ _) (le_of_eq hdeg)
  have hcellstrip : ∀ σ, (WilkiesDesign.IsCell (p+1) (κ' σ) ∧ κ' σ ⊆ strip p) ∨ κ' σ = ∅ := by
    intro σ
    by_cases h : κ σ ⊆ strip p
    · exact Or.inl ⟨by rw [show κ' σ = κ σ from if_pos h]; exact hκcell σ, hκ'strip σ⟩
    · exact Or.inr (show κ' σ = ∅ from if_neg h)
  have hrefc : ∀ (σ : Fin m) (i : Fin (k+1)),
      Disjoint (κ' σ) ((sliceDerivCont (F i))ᶜ) ∨ κ' σ ⊆ (sliceDerivCont (F i))ᶜ := by
    intro σ i
    by_cases h : κ σ ⊆ strip p
    · rw [show κ' σ = κ σ from if_pos h]
      simpa [X] using hκref (some (Sum.inr (i, (0 : Fin 3)))) σ
    · rw [show κ' σ = ∅ from if_neg h]; exact Or.inr (Set.empty_subset _)
  have hrefd : ∀ (σ : Fin m) (i j : Fin (k+1)),
      Disjoint (κ' σ) (domSet (F i) (F j)) ∨ κ' σ ⊆ domSet (F i) (F j) := by
    intro σ i j
    by_cases h : κ σ ⊆ strip p
    · rw [show κ' σ = κ σ from if_pos h]
      simpa [X] using hκref (some (Sum.inl (i, j))) σ
    · rw [show κ' σ = ∅ from if_neg h]; exact Or.inr (Set.empty_subset _)
  have hrefp : ∀ (σ : Fin m) (i : Fin (k+1)),
      Disjoint (κ' σ) (posSet (F i)) ∨ κ' σ ⊆ posSet (F i) := by
    intro σ i
    by_cases h : κ σ ⊆ strip p
    · rw [show κ' σ = κ σ from if_pos h]
      simpa [X] using hκref (some (Sum.inr (i, (1 : Fin 3)))) σ
    · rw [show κ' σ = ∅ from if_neg h]; exact Or.inr (Set.empty_subset _)
  have hrefn : ∀ (σ : Fin m) (i : Fin (k+1)),
      Disjoint (κ' σ) (negSet (F i)) ∨ κ' σ ⊆ negSet (F i) := by
    intro σ i
    by_cases h : κ σ ⊆ strip p
    · rw [show κ' σ = κ σ from if_pos h]
      simpa [X] using hκref (some (Sum.inr (i, (2 : Fin 3)))) σ
    · rw [show κ' σ = ∅ from if_neg h]; exact Or.inr (Set.empty_subset _)
  obtain ⟨i₁, hdich⟩ := cell_dichotomy S p F0 htame hisCellReal D k F hΩ hid m κ'
    hcellstrip hrefc hrefd hrefp hrefn
  refine ⟨m, ?_, κ', i₁, hκ'Ω, hκ'strip, ?_, hdich⟩
  · have hmc' : (m : ℝ) ≤ (MvPolynomial.eval ![BD, Fintype.card ι] b₀ : ℝ) := by
      exact_mod_cast hmc
    have hcard : Fintype.card ι = MvPolynomial.eval ![k, 1] Fd := card_idx k
    calc (m : ℝ) ≤ (MvPolynomial.eval ![BD, Fintype.card ι] b₀ : ℝ) := hmc'
      _ = (MvPolynomial.eval ![MvPolynomial.eval ![D, 1] B', MvPolynomial.eval ![k, 1] Fd] b₀ : ℝ) := by
          rw [hcard, hB'D]
      _ ≤ MvPolynomial.eval ![(D : ℝ), (1 : ℝ), (k : ℝ)] cc := hcc D k
  · intro l hl x hx
    obtain ⟨σ, hσ⟩ := hκcov (Fin.snoc l x)
    have hzmem : Fin.snoc l x ∈ strip p := by
      simpa [strip, Fin.snoc_last] using hx
    have hstripcase : Disjoint (κ σ) (strip p) ∨ κ σ ⊆ strip p := by
      simpa [X] using hκref none σ
    have hsub : κ σ ⊆ strip p := by
      rcases hstripcase with hdis | hsub
      · exfalso
        exact Set.disjoint_left.mp hdis hσ hzmem
      · exact hsub
    exact ⟨σ, by rw [show κ' σ = κ σ from if_pos hsub]; exact hσ⟩


/-- **BNZ Lemma 5.3 (`n = 1`), Piece 2: the Lipschitz cell decomposition.** -/
theorem lipschitz_decomp (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv)
    (p F0 : ℕ) (htame : Work.WilG4a.SliceTame S p F0) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (cc : MvPolynomial (Fin 3) ℝ),
      ∀ (D k : ℕ) (Λ : Set (Fin p → ℝ)) (F : Fin (k+1) → (Fin p → ℝ) → ℝ → ℝ),
        (∀ i, Work.WilG4a.graphFam (F i) ∈ S.Ω F0 D (p + 1 + 1)) →
        (∀ i, ∀ l ∈ Λ, ∀ x ∈ Work.WilG4a.I, F i l x ∈ Work.WilG4a.I) →
        F (Fin.last k) = (fun _ x => x) →
        ∃ (m : ℕ), (m : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (1 : ℝ), (k : ℝ)] cc ∧
          ∃ (κ : Fin m → Set (Fin (p+1) → ℝ)) (i₁ : Fin m → Fin (k+1)),
            (∀ σ, κ σ ∈ S.Ω a (MvPolynomial.eval ![D, 1] b) (p + 1)) ∧
            (∀ σ, κ σ ⊆ Work.WilG4a.strip p) ∧
            (∀ l ∈ Λ, ∀ x ∈ Work.WilG4a.I, ∃ σ, Fin.snoc l x ∈ κ σ) ∧
            (∀ σ, Work.WilG4a.GoodCell (k+1) F (κ σ) (i₁ σ) ∨
              ∀ l, (Work.WilG4a.fibre (κ σ) l).Subsingleton) :=
  lipschitz_decomp_core S hcd hder p F0 htame (sliceDerivCont_memAlt S p F0) (domLoci_memAlt S p F0)
    (fun {C} hC hstrip l => isCell_fibre_real p hC hstrip l) eval_pair_bound

end Work.WilG4a
