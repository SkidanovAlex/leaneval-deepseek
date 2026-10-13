import Mathlib
import Submission.Work.WilG4a.f1affine1_defs
import Submission.Work.WilG4a.affine_reparam_bound
import Submission.Work.WilG4a.fibre_endpoints_bounds
import Submission.Work.WilG4a.affine_comp_contDiffOn
import Submission.Work.WilG4a.affine_comp_sameSign

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4a

theorem goodCell_chart_conditions
    (hG3a : ∀ (r : ℕ) (f : ℝ → ℝ), ContDiffOn ℝ (r + 1) f (Set.Ioo 0 1) → (∀ x ∈ Set.Ioo (0 : ℝ) 1, f x ∈ Set.Ioo (0 : ℝ) 1) → (∀ j ≤ r + 1, (∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ iteratedDerivWithin j f (Set.Ioo 0 1) x) ∨ (∀ x ∈ Set.Ioo (0 : ℝ) 1, iteratedDerivWithin j f (Set.Ioo 0 1) x ≤ 0)) → ∀ M : ℝ, 1 < M → ∀ j ≤ r, ∀ x ∈ Set.Ioo (0 : ℝ) 1, (j : ℝ) / M < x → x < 1 - j / M → |iteratedDerivWithin j f (Set.Ioo 0 1) x| < M ^ j)
    {p k r : ℕ} {F : Fin k → (Fin p → ℝ) → ℝ → ℝ} {κ : Set (Fin (p + 1) → ℝ)}
    {Λ : Set (Fin p → ℝ)} {lo hi : (Fin p → ℝ) → ℝ}
    (hcell : Work.WilG4a.GoodCell_w k r F κ)
    (hI : ∀ i : Fin k, ∀ l ∈ Λ, ∀ x ∈ Work.WilG4a.I, F i l x ∈ Work.WilG4a.I)
    (hne : ∀ l ∈ Λ, ∃ x : ℝ, Fin.snoc l x ∈ κ)
    (hfib : ∀ l ∈ Λ, Work.WilG4a.fibre κ l = Set.Ioo (lo l) (hi l))
    {a b : ℝ} (hb : 0 < b) (ha : 0 ≤ a) (hab : a + b ≤ 1)
    (hcov : b * ((r : ℝ) + 1) ≤ min a (1 - (a + b))) :
    ∀ l ∈ Λ, 0 < (hi l - lo l) * b ∧ 0 ≤ lo l + (hi l - lo l) * a ∧
      lo l + (hi l - lo l) * a + (hi l - lo l) * b ≤ 1 ∧
      ∀ i : Fin k,
        ContDiffOn ℝ r (fun t : ℝ =>
          F i l (lo l + (hi l - lo l) * a + (hi l - lo l) * b * t)) Work.WilG4a.I ∧
        ∀ m ≤ r, ∀ t ∈ Work.WilG4a.I,
          |iteratedDeriv m (fun t : ℝ =>
            F i l (lo l + (hi l - lo l) * a + (hi l - lo l) * b * t)) t| ≤ 1 := by
  intro l hl
  have hne_l : ∃ x : ℝ, Fin.snoc l x ∈ κ := hne l hl
  have hfib_l : fibre κ l = Set.Ioo (lo l) (hi l) := hfib l hl
  obtain ⟨hlt, hlo0, hhi1, hsub⟩ :=
    fibre_endpoints_bounds (p := p) hcell.1 hne_l hfib_l
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- positivity of the chart width
    exact mul_pos (sub_pos.mpr hlt) hb
  · -- nonnegativity of the chart offset
    exact add_nonneg hlo0 (mul_nonneg (sub_nonneg.mpr hlt.le) ha)
  · -- the chart stays inside `[0,1]`
    calc lo l + (hi l - lo l) * a + (hi l - lo l) * b
        = lo l + (hi l - lo l) * (a + b) := by ring
      _ ≤ lo l + (hi l - lo l) * 1 := by
            have := mul_le_mul_of_nonneg_left hab (sub_nonneg.mpr hlt.le); linarith
      _ = hi l := by ring
      _ ≤ 1 := hhi1
  · intro i
    -- the slice `x ↦ F i l x` restricted to the fibre is `C^{r+1}` with signed derivatives
    have hψ : ContDiffOn ℝ (r + 1) (fun x : ℝ => F i l x) (Set.Ioo (lo l) (hi l)) := by
      have h := (hcell.2.2 i l).1
      rwa [hfib_l] at h
    -- pull it back by the affine map `x = lo + (hi - lo) * t`
    have hf : ContDiffOn ℝ (r + 1) (fun x : ℝ => F i l (lo l + (hi l - lo l) * x)) I :=
      affine_comp_contDiffOn hlt hψ
    have hIφ : ∀ x ∈ I, F i l (lo l + (hi l - lo l) * x) ∈ I := by
      intro x hx
      have hmem : lo l + (hi l - lo l) * x ∈ Set.Ioo (lo l) (hi l) := by
        constructor
        · nlinarith [hx.1, hlt]
        · nlinarith [hx.2, hlt]
      exact hI i l hl _ (hsub hmem)
    have hsignφ : ∀ j ≤ r + 1,
        (∀ x ∈ I, 0 ≤ iteratedDeriv j (fun x : ℝ => F i l (lo l + (hi l - lo l) * x)) x) ∨
        (∀ x ∈ I, iteratedDeriv j (fun x : ℝ => F i l (lo l + (hi l - lo l) * x)) x ≤ 0) := by
      intro j hj
      have hsig := (hcell.2.2 i l).2 j hj
      rw [hfib_l] at hsig
      exact affine_comp_sameSign hlt hψ hj hsig
    have hbound := affine_reparam_bound hG3a r
      (fun x : ℝ => F i l (lo l + (hi l - lo l) * x)) hf hIφ hsignφ
      (α := a) (β := b) hb ha hab hcov
    refine ⟨?_, ?_⟩
    · -- smoothness of the final chart
      have hfr : ContDiffOn ℝ r (fun x : ℝ => F i l (lo l + (hi l - lo l) * x)) I :=
        hf.of_le (Nat.cast_le.mpr (Nat.le_succ r))
      have hmap : Set.MapsTo (fun t : ℝ => a + b * t) I I := by
        intro t ht
        simp only [Set.mem_Ioo] at ht ⊢
        constructor <;> nlinarith [ht.1, ht.2, ha, hb, hab]
      have hc2 : ContDiffOn ℝ r (fun t : ℝ => a + b * t) I := by fun_prop
      have hcomp : ContDiffOn ℝ r
          (fun t : ℝ => F i l (lo l + (hi l - lo l) * (a + b * t))) I :=
        ContDiffOn.comp (g := fun x : ℝ => F i l (lo l + (hi l - lo l) * x))
          (f := fun t : ℝ => a + b * t) hfr hc2 hmap
      refine hcomp.congr (fun t _ => ?_)
      congr 1
      ring
    · -- the derivative bounds
      intro m hm t ht
      have hbb := hbound m hm t ht
      have hfun : (fun s : ℝ => F i l (lo l + (hi l - lo l) * (a + b * s))) =
          (fun s : ℝ => F i l (lo l + (hi l - lo l) * a + (hi l - lo l) * b * s)) := by
        funext s; congr 1; ring
      rw [hfun] at hbb
      exact hbb

end Work.WilG4a
