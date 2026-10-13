/-
  WilG1/Choice/G1Sel/OneDimG1 — the one-dimensional case of effective definable choice,
  assembled from the *proved* selection-set membership `Choice.selSet_mem` and the minimal
  selection `Eff.minGraph`.

  Given `X ∈ S.Ω F D (p+1)` and a sharp cylindrical decomposition `C` of `ℝ^{p+1}` adapted to
  `X` (from `hcd`), the set
    `Sg = ⋃ κ ∈ C.filter (· ⊆ X), (selSet κ (projPar κ))`
  is an `Ω`-set contained in `X`, and over every parameter whose fibre in `X` is nonempty its
  fibre is a nonempty finite set of reals.  `minGraph X Sg` is therefore the graph of a genuine
  function, `Ω`-definable with uniform bounds; its section lies in `X`.

  This is the `n = 1` instance of `G1_choice`; `Choice/G1_choice_proved.lean` iterates it.
-/
import Mathlib
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.ChoiceDefs
import Submission.Work.WilG1.Choice.SelDefs
import Submission.Work.WilG1.Choice.Eff.Defs
import Submission.Work.WilG1.Choice.selSet_mem
import Submission.Work.WilG1.Choice.selSet_fibre
import Submission.Work.WilG1.Choice.cylDecomp_cell_of_mem
import Submission.Work.WilG4a.isCell_fiber
import Submission.Work.WilG5.Basic
import Submission.Work.WilG1.Choice.G1Sel.minGraphFibreG1
import Submission.Work.WilG1.Choice.G1Sel.minGraphOmegaG1

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
open Classical
open scoped BigOperators

namespace Work.WilG1.Choice.G1Sel

open WilkiesDesign WilkiesConjecture

/-! ## 1. `Ω`-bookkeeping for finite families -/

/-- Binary union with additive degrees (the format is unchanged). -/
theorem union2_nat {S : SOMin} {n F D₁ D₂ : ℕ} {A B : Set (Fin n → ℝ)}
    (hA : A ∈ S.Ω F D₁ n) (hB : B ∈ S.Ω F D₂ n) : A ∪ B ∈ S.Ω F (D₁ + D₂) n := by
  have h := S.union (fun i : Fin 2 => if i = 0 then D₁ else D₂)
      (fun i : Fin 2 => if i = 0 then A else B)
      (by intro i; fin_cases i
          · simpa using hA
          · simpa using hB)
  rw [Work.WilG1.Omega.iUnion_fin_two] at h
  rw [show (∑ i : Fin 2, (if i = 0 then D₁ else D₂)) = D₁ + D₂ from by
    rw [Fin.sum_univ_two]; simp] at h
  exact h

/-- Binary intersection with additive degrees. -/
theorem inter2_nat {S : SOMin} {n F₁ F₂ D₁ D₂ : ℕ} {A B : Set (Fin n → ℝ)}
    (hA : A ∈ S.Ω F₁ D₁ n) (hB : B ∈ S.Ω F₂ D₂ n) :
    A ∩ B ∈ S.Ω (max F₁ F₂ + 1) (D₁ + D₂) n := by
  have h1 : A ∈ S.Ω (max F₁ F₂) D₁ n := Omega.mono hA (le_max_left _ _) le_rfl
  have h2 : B ∈ S.Ω (max F₁ F₂) D₂ n := Omega.mono hB (le_max_right _ _) le_rfl
  have h := S.inter (fun i : Fin 2 => if i = 0 then D₁ else D₂)
      (fun i : Fin 2 => if i = 0 then A else B)
      (by intro i; fin_cases i
          · simpa using h1
          · simpa using h2)
  rw [Work.WilG1.Omega.iInter_fin_two] at h
  rw [show (∑ i : Fin 2, (if i = 0 then D₁ else D₂)) = D₁ + D₂ from by
    rw [Fin.sum_univ_two]; simp] at h
  exact h

/-- A union over a `Finset`: the format is unchanged and the degree is multiplied by the
cardinality. -/
theorem finset_biUnion_mem {S : SOMin} {n : ℕ} {α : Type*} (s : Finset α)
    (Fam : α → Set (Fin n → ℝ)) {A D₀ : ℕ} (hA : n + 6 ≤ A)
    (h : ∀ a ∈ s, Fam a ∈ S.Ω A D₀ n) :
    (⋃ a ∈ (s : Set α), Fam a) ∈ S.Ω A (s.card * D₀) n := by
  classical
  induction s using Finset.induction with
  | empty =>
    have he : (⋃ a ∈ ((∅ : Finset α) : Set α), Fam a) = (∅ : Set (Fin n → ℝ)) := by
      ext z
      simp
    rw [he, Finset.card_empty, Nat.zero_mul]
    have h0 : (∅ : Set (Fin n → ℝ)) ∈ S.Ω n 0 n := by
      have h := S.hyp n (1 : MvPolynomial (Fin n) ℝ)
      have hset : {x : Fin n → ℝ |
          MvPolynomial.eval x (1 : MvPolynomial (Fin n) ℝ) = 0} = ∅ := by
        ext x
        simp
      rw [hset, MvPolynomial.totalDegree_one] at h
      exact h
    exact Omega.mono h0 (by omega) le_rfl
  | insert a s ha ih =>
    have hsum : (⋃ b ∈ ((insert a s : Finset α) : Set α), Fam b) =
        Fam a ∪ (⋃ b ∈ (s : Set α), Fam b) := by
      ext z
      simp only [Set.mem_iUnion, Set.mem_union, Finset.mem_coe, Finset.mem_insert]
      constructor
      · rintro ⟨b, hb | hb, hz⟩
        · exact Or.inl (by rwa [hb] at hz)
        · exact Or.inr ⟨b, hb, hz⟩
      · rintro (hz | ⟨b, hb, hz⟩)
        · exact ⟨a, Or.inl rfl, hz⟩
        · exact ⟨b, Or.inr hb, hz⟩
    rw [hsum]
    have h1 : Fam a ∈ S.Ω A D₀ n := h a (Finset.mem_insert_self a s)
    have h2 : (⋃ b ∈ (s : Set α), Fam b) ∈ S.Ω A (s.card * D₀) n :=
      ih (fun b hb => h b (Finset.mem_insert_of_mem hb))
    have h3 := union2_nat h1 h2
    rw [Finset.card_insert_of_notMem ha, Nat.add_mul, Nat.one_mul]
    refine Omega.mono h3 le_rfl ?_
    exact le_of_eq (Nat.add_comm D₀ (s.card * D₀))

/-! ## 2. The one-dimensional case -/

/-- **One-dimensional effective definable choice.**  Every `Ω`-set `X ⊆ ℝ^{p+1}` admits a
section `f : ℝ^p → ℝ` whose graph is an `Ω`-set with format and degree depending only on `F`
and `p`. -/
theorem oneDimG1 {S : WilkiesDesign.SOMin} (hcd : S.SharpCD) (F p : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (D : ℕ) (X : Set (Fin (p + 1) → ℝ)),
      X ∈ S.Ω F D (p + 1) →
      ∃ f : (Fin p → ℝ) → ℝ,
        (∀ l : Fin p → ℝ, (∃ t : ℝ, Fin.snoc l t ∈ X) → Fin.snoc l (f l) ∈ X) ∧
        WilkiesDesign.graphOf f ∈ S.Ω a (b.eval D) (p + 1) := by
  classical
  obtain ⟨a₀, b₀, c₀, hCD⟩ := hcd F (p + 1)
  let Dsel : Polynomial ℕ :=
    Polynomial.C (200 * (p + 2)) * (c₀ + c₀) + Polynomial.C (2000 * (p + 2))
  let bSg : Polynomial ℕ := Work.WilG1.psubst b₀ 1 * (Polynomial.X + Dsel)
  let bStar : Polynomial ℕ :=
    Polynomial.C (200 * (p + 2)) * (Polynomial.X + bSg) + Polynomial.C (2000 * (p + 2))
  let A₁ : ℕ := max (a₀ + (a₀ + 1) + 8 * p + 200) F + 1
  obtain ⟨aStar, hmin⟩ := minGraphOmegaG1 (S := S) p F A₁
  refine ⟨aStar, bStar, ?_⟩
  intro D X hX
  obtain ⟨C, hdec, hadapt, hcard, hcells⟩ := hCD D 1 (fun _ : Fin 1 => X) (fun _ => hX)
  have hadapt' : ∀ κ ∈ C, κ ⊆ X ∨ Disjoint κ X := fun κ hκ => hadapt 0 κ hκ
  let s : Finset (Set (Fin (p + 1) → ℝ)) := C.filter (fun κ => κ ⊆ X)
  let Sg : Set (Fin (p + 1) → ℝ) := Work.WilG1.Choice.Eff.sigmaOf C X
  have hA₁ge : p + 1 + 6 ≤ A₁ := by
    have hp : p ≤ 8 * p := by omega
    simp only [A₁]
    omega
  have hfam : ∀ κ ∈ s, Work.WilG1.Choice.Eff.selOf κ ∩ X ∈
      S.Ω A₁ (Dsel.eval D + D) (p + 1) := by
    intro κ hκ
    obtain ⟨hκC, -⟩ := Finset.mem_filter.mp hκ
    have hK : κ ∈ S.Ω a₀ (c₀.eval D) (p + 1) := hcells κ hκC
    have hR : Work.WilG1.projPar κ ∈ S.Ω (a₀ + 1) (c₀.eval D) p := S.proj hK
    have hsel : Work.WilG1.Choice.Eff.selOf κ ∈
        S.Ω (a₀ + (a₀ + 1) + 8 * p + 200) (Dsel.eval D) (p + 1) :=
      selSet_mem (S := S) hK hR
    have hsel' : Work.WilG1.Choice.Eff.selOf κ ∈
        S.Ω (max (a₀ + (a₀ + 1) + 8 * p + 200) F) (Dsel.eval D) (p + 1) :=
      Omega.mono hsel (le_max_left _ _) le_rfl
    have hX' : X ∈ S.Ω (max (a₀ + (a₀ + 1) + 8 * p + 200) F) D (p + 1) :=
      Omega.mono hX (le_max_right _ _) le_rfl
    have hInt : Work.WilG1.Choice.Eff.selOf κ ∩ X ∈
        S.Ω (max (max (a₀ + (a₀ + 1) + 8 * p + 200) F)
            (max (a₀ + (a₀ + 1) + 8 * p + 200) F) + 1) (Dsel.eval D + D) (p + 1) :=
      inter2_nat (S := S) hsel' hX'
    simpa only [max_self, A₁] using hInt
  have hSgmem : Sg ∈ S.Ω A₁ (s.card * (Dsel.eval D + D)) (p + 1) := by
    rw [show Sg = ⋃ κ ∈ (s : Set (Set (Fin (p + 1) → ℝ))),
        (Work.WilG1.Choice.Eff.selOf κ ∩ X) from rfl]
    exact finset_biUnion_mem (S := S) s
      (fun κ => Work.WilG1.Choice.Eff.selOf κ ∩ X) hA₁ge hfam
  have hcard' : s.card ≤ (Work.WilG1.psubst b₀ 1).eval D := by
    calc s.card ≤ C.card := Finset.card_filter_le _ _
      _ ≤ MvPolynomial.eval ![D, 1] b₀ := hcard
      _ = (Work.WilG1.psubst b₀ 1).eval D := (Work.WilG1.eval_psubst b₀ 1 D).symm
  have hdeg : s.card * (Dsel.eval D + D) ≤ bSg.eval D := by
    have hb : bSg.eval D =
        (Work.WilG1.psubst b₀ 1).eval D * (D + Dsel.eval D) := by
      simp only [bSg, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X]
    rw [hb]
    refine le_trans (Nat.mul_le_mul_right _ hcard') (le_of_eq ?_)
    rw [Nat.add_comm]
  have hSgmem' : Sg ∈ S.Ω A₁ (bSg.eval D) (p + 1) := Omega.mono hSgmem le_rfl hdeg
  have hX'' : X ∈ S.Ω F (Polynomial.X.eval D) (p + 1) := by simpa using hX
  have hGmem : Work.WilG1.Choice.Eff.minGraph X Sg ∈ S.Ω aStar (bStar.eval D) (p + 1) :=
    hmin D Polynomial.X bSg X Sg hX'' hSgmem'
  have hfib : ∀ l : Fin p → ℝ, ∃! t : ℝ,
      Fin.snoc l t ∈ Work.WilG1.Choice.Eff.minGraph X Sg := by
    intro l
    by_cases hl : ∃ t : ℝ, Fin.snoc l t ∈ X
    · exact minGraphFibreG1 (p := p) (C := C) (X := X) (l := l) hdec hadapt' hl
    · refine ⟨0, ?_, ?_⟩
      · change Fin.snoc l 0 ∈ Work.WilG1.Choice.Eff.minGraph X Sg
        rw [Work.WilG1.Choice.Eff.mem_minGraph]
        exact Or.inl ⟨by simp, by simpa using hl⟩
      · intro t ht
        change Fin.snoc l t ∈ Work.WilG1.Choice.Eff.minGraph X Sg at ht
        rw [Work.WilG1.Choice.Eff.mem_minGraph] at ht
        rcases ht with ⟨h0, -⟩ | ⟨hmem, -⟩
        · simpa using h0
        · exact absurd ⟨t, Work.WilG1.Choice.Eff.sigmaOf_subset hmem⟩ hl
  let f : (Fin p → ℝ) → ℝ := fun l => Classical.choose (ExistsUnique.exists (hfib l))
  have hfG : ∀ l : Fin p → ℝ,
      Fin.snoc l (f l) ∈ Work.WilG1.Choice.Eff.minGraph X Sg := fun l =>
    Classical.choose_spec (ExistsUnique.exists (hfib l))
  have hfuniq : ∀ (l : Fin p → ℝ) (t : ℝ),
      Fin.snoc l t ∈ Work.WilG1.Choice.Eff.minGraph X Sg → t = f l := fun l t ht =>
    (ExistsUnique.unique (hfib l) (hfG l) ht).symm
  have hgraph : WilkiesDesign.graphOf f = Work.WilG1.Choice.Eff.minGraph X Sg := by
    ext z
    simp only [WilkiesDesign.graphOf, Set.mem_ofPred_eq]
    constructor
    · intro h
      have hthis := hfG (Fin.init z)
      rw [← h, Fin.snoc_init_self z] at hthis
      exact hthis
    · intro h
      rw [← Fin.snoc_init_self z] at h
      exact hfuniq (Fin.init z) (z (Fin.last p)) h
  refine ⟨f, ?_, ?_⟩
  · intro l hne
    have hmem : Fin.snoc l (f l) ∈ Sg := by
      rcases (Work.WilG1.Choice.Eff.mem_minGraph.mp (hfG l)) with ⟨-, hnot⟩ | ⟨hmem, -⟩
      · exfalso
        obtain ⟨t, ht⟩ := hne
        exact hnot ⟨t, by simpa using ht⟩
      · exact hmem
    exact Work.WilG1.Choice.Eff.sigmaOf_subset hmem
  · rw [hgraph]
    exact hGmem

end Work.WilG1.Choice.G1Sel
