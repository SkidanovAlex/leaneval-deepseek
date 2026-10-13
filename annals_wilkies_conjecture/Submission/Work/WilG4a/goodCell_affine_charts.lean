import Mathlib
import Submission.Work.WilG4a.f1affine1_defs
import Submission.Work.WilG4a.affine_reparam_bound
import Submission.Work.WilG4a.affine_comb_graph_mem
import Submission.Work.WilG4a.CD.eval_bind_shift
import Submission.Work.WilG4a.affine_cover_params
import Submission.Work.WilG4a.goodCell_chart_conditions

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG4a

/-! ## The fibre end points of a good cell lie in `[0,1]` -/

private lemma fibre_endpoint_bounds {p k r : ℕ} {F : Fin k → (Fin p → ℝ) → ℝ → ℝ}
    {κ : Set (Fin (p + 1) → ℝ)} {Λ : Set (Fin p → ℝ)} {lo hi : (Fin p → ℝ) → ℝ}
    (hcell : Work.WilG4a.GoodCell_w k r F κ)
    (hne : ∀ l ∈ Λ, ∃ x : ℝ, Fin.snoc l x ∈ κ)
    (hfib : ∀ l ∈ Λ, Work.WilG4a.fibre κ l = Set.Ioo (lo l) (hi l)) :
    ∀ l ∈ Λ, lo l < hi l ∧ 0 ≤ lo l ∧ hi l ≤ 1 := by
  intro l hl
  obtain ⟨x, hx⟩ := hne l hl
  have hone : x ∈ Set.Ioo (lo l) (hi l) := by
    rw [← hfib l hl]; exact hx
  have hlt : lo l < hi l := lt_trans hone.1 hone.2
  have hsub : Work.WilG4a.fibre κ l ⊆ Work.WilG4a.I := by
    intro y hy
    have hy' := hcell.1 hy
    simpa [Work.WilG4a.strip] using hy'
  rw [hfib l hl] at hsub
  have hiff := (Set.Ioo_subset_Ioo_iff hlt).mp hsub
  exact ⟨hlt, hiff.1, hiff.2⟩

theorem goodCell_affine_charts (S : WilkiesDesign.SOMin) (hG3a : ∀ (r : ℕ) (f : ℝ → ℝ), ContDiffOn ℝ (r + 1) f (Set.Ioo 0 1) → (∀ x ∈ Set.Ioo (0 : ℝ) 1, f x ∈ Set.Ioo (0 : ℝ) 1) → (∀ j ≤ r + 1, (∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ iteratedDerivWithin j f (Set.Ioo 0 1) x) ∨ (∀ x ∈ Set.Ioo (0 : ℝ) 1, iteratedDerivWithin j f (Set.Ioo 0 1) x ≤ 0)) → ∀ M : ℝ, 1 < M → ∀ j ≤ r, ∀ x ∈ Set.Ioo (0 : ℝ) 1, (j : ℝ) / M < x → x < 1 - j / M → |iteratedDerivWithin j f (Set.Ioo 0 1) x| < M ^ j) (hG3b : ∀ (r : ℕ) (ε : ℝ), 0 < ε → ε < 1 → ∃ s : Finset (ℝ × ℝ), (s.card : ℝ) ≤ 8 * (r + 1) * (-Real.log ε + 2) ∧ (∀ p ∈ s, 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < 1 ∧ (p.2 - p.1) * (r + 1) ≤ min p.1 (1 - p.2)) ∧ (Set.Icc ε (1 - ε) ⊆ (⋃ p ∈ s, Set.Icc p.1 p.2))) (p : ℕ) (F0 Fκ : ℕ) (bκ : MvPolynomial (Fin 2) ℕ) : ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : MvPolynomial (Fin 4) ℝ), ∀ (D r k : ℕ) (ε : ℝ), 0 < ε → ε < 1 → ∀ (Λ : Set (Fin p → ℝ)) (F : Fin k → (Fin p → ℝ) → ℝ → ℝ) (κ : Set (Fin (p + 1) → ℝ)) (lo hi : (Fin p → ℝ) → ℝ), (∀ i, Work.WilG4a.graphFam (F i) ∈ S.Ω F0 D (p + 1 + 1)) → (∀ i, ∀ l ∈ Λ, ∀ x ∈ Work.WilG4a.I, F i l x ∈ Work.WilG4a.I) → Work.WilG4a.GoodCell_w k r F κ → κ ∈ S.Ω Fκ (MvPolynomial.eval ![D, r] bκ) (p + 1) → WilkiesDesign.graphOf lo ∈ S.Ω Fκ (MvPolynomial.eval ![D, r] bκ) (p + 1) → WilkiesDesign.graphOf hi ∈ S.Ω Fκ (MvPolynomial.eval ![D, r] bκ) (p + 1) → (∀ l ∈ Λ, ∃ x : ℝ, Fin.snoc l x ∈ κ) → (∀ l ∈ Λ, Work.WilG4a.fibre κ l = Set.Ioo (lo l) (hi l)) → ∃ Φ : Finset (((Fin p → ℝ) → ℝ) × ((Fin p → ℝ) → ℝ)), (Φ.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c ∧ (∀ αβ ∈ Φ, WilkiesDesign.graphOf αβ.1 ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (p + 1) ∧ WilkiesDesign.graphOf αβ.2 ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (p + 1) ∧ ∀ l ∈ Λ, 0 < αβ.2 l ∧ 0 ≤ αβ.1 l ∧ αβ.1 l + αβ.2 l ≤ 1 ∧ ∀ i, ContDiffOn ℝ r (fun t : ℝ => F i l (αβ.1 l + αβ.2 l * t)) Work.WilG4a.I ∧ ∀ m ≤ r, ∀ t ∈ Work.WilG4a.I, |iteratedDeriv m (fun t : ℝ => F i l (αβ.1 l + αβ.2 l * t)) t| ≤ 1) ∧ (∀ l ∈ Λ, ∀ x ∈ Work.WilG4a.I, (∃ t ∈ Work.WilG4a.I, x = lo l + (hi l - lo l) * t) → ∃ αβ ∈ Φ, ∃ t ∈ Work.WilG4a.I, |αβ.1 l + αβ.2 l * t - x| < ε) := by
  classical
  obtain ⟨aΩ, bΩ, hΩaff⟩ := affine_comb_graph_mem S p Fκ
  set bnew : MvPolynomial (Fin 2) ℕ :=
    MvPolynomial.aeval (![bκ, MvPolynomial.X 1] : Fin 2 → MvPolynomial (Fin 2) ℕ) bΩ with hbnew
  set cc : MvPolynomial (Fin 4) ℝ :=
    MvPolynomial.C 8 * (MvPolynomial.X (1 : Fin 4) + MvPolynomial.C 1) *
      (MvPolynomial.X (3 : Fin 4) + MvPolynomial.C 4) + MvPolynomial.C 2 with hcc
  refine ⟨aΩ, bnew, cc, ?_⟩
  intro D r k ε hε hε1 Λ F κ lo hi hFΩ hFI hcell hκΩ hloΩ hhiΩ hne hfib
  have hbnds := fibre_endpoint_bounds hcell hne hfib
  obtain ⟨s, hsP, hscard, hscov⟩ := affine_cover_params hG3b r hε hε1
  have hbEval : MvPolynomial.eval ![D, r] bnew
      = MvPolynomial.eval ![MvPolynomial.eval ![D, r] bκ, r] bΩ := by
    rw [hbnew, Work.WilG4a.CD.eval_aeval_eq]
    have hvec : (fun i : Fin 2 => MvPolynomial.eval ![D, r]
          ((![bκ, MvPolynomial.X 1] : Fin 2 → MvPolynomial (Fin 2) ℕ) i))
        = ![MvPolynomial.eval ![D, r] bκ, r] := by
      funext i
      fin_cases i <;> simp
    rw [hvec]
  refine ⟨s.image (fun q : ℝ × ℝ =>
      ((fun l : Fin p → ℝ => lo l + (hi l - lo l) * q.1),
       (fun l : Fin p → ℝ => (hi l - lo l) * q.2))), ?_, ?_, ?_⟩
  · -- cardinality of the chart family
    have hcard1 : ((s.image (fun q : ℝ × ℝ =>
        ((fun l : Fin p → ℝ => lo l + (hi l - lo l) * q.1),
         (fun l : Fin p → ℝ => (hi l - lo l) * q.2)))).card : ℝ) ≤ (s.card : ℝ) := by
      exact_mod_cast Finset.card_image_le
    have hev : ∀ x : Fin 4 → ℝ, MvPolynomial.eval x cc
        = 8 * (x (1 : Fin 4) + 1) * (x (3 : Fin 4) + 4) + 2 := by
      intro x
      simp only [hcc, MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C,
        MvPolynomial.eval_X]
    have hccEval : MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cc
        = 8 * ((r : ℝ) + 1) * (-Real.log ε + 4) + 2 := by
      have := hev ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε]
      simpa using this
    have hcard2 : (s.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cc := by
      rw [hccEval]; exact hscard
    exact le_trans hcard1 hcard2
  · -- the graphs of the chart coefficients are `Ω`-definable, and the chart is valid
    intro αβ hαβ
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hαβ
    obtain ⟨hq2, hq1, hqsum, hqcov⟩ := hsP q hq
    have hAΩ : WilkiesDesign.graphOf (fun l : Fin p → ℝ => lo l + (hi l - lo l) * q.1) ∈
        S.Ω aΩ (MvPolynomial.eval ![D, r] bnew) (p + 1) := by
      have h := hΩaff (MvPolynomial.eval ![D, r] bκ) r hloΩ hhiΩ (0 : ℝ) (1 - q.1) q.1
      have hfun : (fun l : Fin p → ℝ => (0 : ℝ) + (1 - q.1) * lo l + q.1 * hi l)
          = (fun l : Fin p → ℝ => lo l + (hi l - lo l) * q.1) := by
        funext l; ring
      rw [hfun] at h
      rw [← hbEval] at h
      exact h
    have hBΩ : WilkiesDesign.graphOf (fun l : Fin p → ℝ => (hi l - lo l) * q.2) ∈
        S.Ω aΩ (MvPolynomial.eval ![D, r] bnew) (p + 1) := by
      have h := hΩaff (MvPolynomial.eval ![D, r] bκ) r hloΩ hhiΩ (0 : ℝ) (-q.2) q.2
      have hfun : (fun l : Fin p → ℝ => (0 : ℝ) + (-q.2) * lo l + q.2 * hi l)
          = (fun l : Fin p → ℝ => (hi l - lo l) * q.2) := by
        funext l; ring
      rw [hfun] at h
      rw [← hbEval] at h
      exact h
    refine ⟨hAΩ, hBΩ, ?_⟩
    intro l hl
    exact goodCell_chart_conditions hG3a hcell hFI hne hfib (a := q.1) (b := q.2)
      hq2 hq1 hqsum hqcov l hl
  · -- the charts `ε`-cover the fibre
    intro l hl x hxI ht
    obtain ⟨t, htI, hxt⟩ := ht
    obtain ⟨q, hq, τ, hτ, hdist⟩ := hscov t htI
    obtain ⟨hlt, hlo0, hhi1⟩ := hbnds l hl
    refine ⟨((fun l : Fin p → ℝ => lo l + (hi l - lo l) * q.1),
      (fun l : Fin p → ℝ => (hi l - lo l) * q.2)), ?_, τ, hτ, ?_⟩
    · exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
    · have hd0 : 0 ≤ hi l - lo l := by linarith
      have hd1 : hi l - lo l ≤ 1 := by linarith
      have hkey : (lo l + (hi l - lo l) * q.1) + ((hi l - lo l) * q.2) * τ - x
          = (hi l - lo l) * (q.1 + q.2 * τ - t) := by
        rw [hxt]; ring
      rw [hkey, abs_mul, abs_of_nonneg hd0]
      calc (hi l - lo l) * |q.1 + q.2 * τ - t|
          ≤ 1 * |q.1 + q.2 * τ - t| := mul_le_mul_of_nonneg_right hd1 (abs_nonneg _)
        _ = |q.1 + q.2 * τ - t| := one_mul _
        _ < ε := hdist

end Work.WilG4a
