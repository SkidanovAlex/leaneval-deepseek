import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilkiesH.Strat.Defs
import Submission.Work.WilkiesH.Strat.rft.Master
import Submission.Work.WilkiesH.Strat.dimLE_iUnion_fin
import Submission.Work.WilG5.Basic
import Submission.Work.WilG5.Interior.interior_charts

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical
namespace Work.WilkiesH.Strat
open WilkiesDesign WilkiesConjecture
open Work.WilG5
variable {S : WilkiesDesign.SOMin}

/-!
# The assembly of `rel_frontier_thin` from the cell-frontier lemma

A point of `X ∩ V` lies in a cell `κ` of a cylindrical decomposition of `ℝⁿ` compatible with the
pair `(X ∩ V, V)`; since `X ∩ V` is a union of cells, `κ ⊆ X ∩ V ⊆ V`, so points of
`V \ X ⊆ V \ κ` show that `X ∩ V ∩ closure (V \ X)` meets `κ` only inside
`κ ∩ closure (V \ κ)` — the relative frontier of the cell in `V`.  The cell-frontier lemma
covers that relative frontier by an `Ω`-set of dimension `≤ μ - 1`, and a finite union of such
sets is again of dimension `≤ μ - 1` by `dimLE_iUnion_fin` (via `SharpCD`).
-/
theorem rel_frontier_thin_of_crux {S : WilkiesDesign.SOMin} (hcd : S.SharpCD)
    (hcrux : ∀ F n : ℕ, ∃ (a : ℕ) (pm : MvPolynomial (Fin 2) ℕ),
      ∀ (μ D Dv : ℕ) (V κ : Set (Fin n → ℝ)),
        V ∈ S.Ω F Dv n → WilkiesConjecture.IsSemialgebraic V → WilkiesDesign.DimLE V μ →
        κ ∈ S.Ω F D n → WilkiesDesign.IsCell n κ → κ.Nonempty → κ ⊆ V →
        ∃ W : Set (Fin n → ℝ),
          W ∈ S.Ω a (MvPolynomial.eval ![(D + Dv : ℕ), (n + 1 : ℕ)] pm) n ∧ W ⊆ κ ∧
          WilkiesDesign.DimLE W (μ - 1) ∧ κ ∩ closure (V \ κ) ⊆ W) :
    ∀ F n : ℕ, ∃ (a : ℕ) (pm : MvPolynomial (Fin 2) ℕ),
      ∀ (μ D Dv : ℕ) (X V : Set (Fin n → ℝ)),
        X ∈ S.Ω F D n → V ∈ S.Ω F Dv n → WilkiesConjecture.IsSemialgebraic V →
        WilkiesDesign.DimLE V μ →
        WilkiesDesign.DimLE (X ∩ V ∩ closure (V \ X)) (μ - 1) := by
  intro F n
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- `ℝ⁰` is a point: everything is zero-dimensional
    subst hn0
    refine ⟨0, 0, fun μ D Dv X V _ _ _ _ => ?_⟩
    have hsub : (X ∩ V ∩ closure (V \ X)).Subsingleton :=
      fun a b _ _ => Subsingleton.elim _ _
    refine Work.WilkiesH.Dim.dimLE_mono
      (fun e => interior_eq_empty_of_subsingleton' (n := 0 + 1) (by omega)
        (hsub.image (fun x : Fin 0 → ℝ => x ∘ e))) (by omega)
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    -- the cell-frontier data and the decomposition format depend only on `(F, m)`
    obtain ⟨a₁, b₁, c₁, H⟩ := hcd (F + 1) (m + 1)
    obtain ⟨a, pm, hcrux'⟩ := hcrux (max (F + 1) a₁) (m + 1)
    refine ⟨a, pm, fun μ D Dv X V hX hV hVsem hVdim => ?_⟩
    have hA : X ∩ V ∈ S.Ω (F + 1) (D + Dv) (m + 1) := by
      have h := S.inter (F := F) (n := m + 1) (k := 2) ![D, Dv] ![X, V]
        (by intro i; fin_cases i <;> simp [hX, hV])
      rw [show (⋂ i : Fin 2, (![X, V] : Fin 2 → Set (Fin (m + 1) → ℝ)) i) = X ∩ V from by
        ext y; simp [Fin.forall_fin_two]] at h
      simpa [Fin.sum_univ_two] using h
    have hV' : V ∈ S.Ω (F + 1) (D + Dv) (m + 1) := mem_mono hV _ _ (by omega) (by omega)
    obtain ⟨CD, hcyl, hcomp, hcard, hmem⟩ := H (D + Dv) 2 ![X ∩ V, V] (by
      intro i; fin_cases i
      · simpa using hA
      · simpa using hV')
    rw [WilkiesDesign.IsCylDecomp] at hcyl
    -- the subfamily of cells contained in `V`
    let CDv : Finset (Set (Fin (m + 1) → ℝ)) := CD.filter (fun κ => κ ⊆ V)
    let E : Fin CDv.card ≃ ↥CDv :=
      (finCongr (Fintype.card_coe CDv).symm).trans (Fintype.equivFin ↥CDv).symm
    let e : Fin CDv.card → Set (Fin (m + 1) → ℝ) := fun j => (E j).1
    have he_mem : ∀ j, e j ∈ CDv := fun j => (E j).2
    have he_cd : ∀ j, e j ∈ CD := fun j => (Finset.mem_filter.mp (he_mem j)).1
    have he_sub : ∀ j, e j ⊆ V := fun j => (Finset.mem_filter.mp (he_mem j)).2
    have he_surj : ∀ κ ∈ CDv, ∃ j, e j = κ := fun κ hκ => ⟨E.symm ⟨κ, hκ⟩, by simp [e]⟩
    have heΩ : ∀ j, e j ∈ S.Ω (max (F + 1) a₁) (c₁.eval (D + Dv)) (m + 1) :=
      fun j => mem_mono (hmem _ (he_cd j)) _ _ (le_max_right _ _) le_rfl
    have hcell : ∀ j, WilkiesDesign.IsCell (m + 1) (e j) := fun j => (hcyl.1 _ (he_cd j)).1
    have hne : ∀ j, (e j).Nonempty := fun j => (hcyl.1 _ (he_cd j)).2
    have hV'' : V ∈ S.Ω (max (F + 1) a₁) Dv (m + 1) :=
      mem_mono hV _ _ (le_trans (Nat.le_succ F) (le_max_left (F + 1) a₁)) le_rfl
    classical
    let W : Fin CDv.card → Set (Fin (m + 1) → ℝ) := fun j =>
      Classical.choose (hcrux' μ (c₁.eval (D + Dv)) Dv V (e j) hV'' hVsem hVdim
        (heΩ j) (hcell j) (hne j) (he_sub j))
    have hWspec : ∀ j,
        (W j ∈ S.Ω a (MvPolynomial.eval ![((c₁.eval (D + Dv)) + Dv : ℕ), (m + 1 + 1 : ℕ)] pm)
            (m + 1) ∧
         W j ⊆ e j ∧ WilkiesDesign.DimLE (W j) (μ - 1) ∧ e j ∩ closure (V \ e j) ⊆ W j) := by
      intro j
      have h := Classical.choose_spec (hcrux' μ (c₁.eval (D + Dv)) Dv V (e j) hV'' hVsem hVdim
        (heΩ j) (hcell j) (hne j) (he_sub j))
      simpa [W] using h
    have hWmem : ∀ j, W j ∈
        S.Ω a (MvPolynomial.eval ![((c₁.eval (D + Dv)) + Dv : ℕ), (m + 1 + 1 : ℕ)] pm) (m + 1) :=
      fun j => (hWspec j).1
    have hWdim : ∀ j, WilkiesDesign.DimLE (W j) (μ - 1) := fun j => (hWspec j).2.2.1
    have hcover : X ∩ V ∩ closure (V \ X) ⊆ ⋃ j, W j := by
      intro x hx
      obtain ⟨⟨hxX, hxV⟩, hxcl⟩ := hx
      obtain ⟨κ, hκCD, hxκ⟩ := hcyl.2.2.1 x
      have hκA : κ ⊆ X ∩ V := by
        rcases hcomp 0 κ hκCD with h | h
        · simpa using h
        · exact absurd hxκ (fun hxκ => Set.disjoint_left.mp h hxκ ⟨hxX, hxV⟩)
      have hκV : κ ⊆ V := fun y hy => (hκA hy).2
      obtain ⟨j, hj⟩ := he_surj κ (Finset.mem_filter.mpr ⟨hκCD, hκV⟩)
      have hxej : x ∈ e j := by rw [hj]; exact hxκ
      refine Set.mem_iUnion.mpr ⟨j, ?_⟩
      refine (hWspec j).2.2.2 ⟨hxej, ?_⟩
      have hmono : V \ X ⊆ V \ e j := by
        intro y hy
        exact ⟨hy.1, fun hyej => hy.2 (hκA (by rw [← hj]; exact hyej)).1⟩
      exact closure_mono hmono hxcl
    have hunion : WilkiesDesign.DimLE (⋃ j, W j) (μ - 1) :=
      dimLE_iUnion_fin (S := S) hcd (A := W) hWmem hWdim
    exact WilG5.Interior.dimLE_mono hunion hcover

end Work.WilkiesH.Strat
