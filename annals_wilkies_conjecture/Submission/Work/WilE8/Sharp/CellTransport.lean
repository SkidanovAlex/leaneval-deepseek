/-
  WilE8 — transporting `IsCell`/cylindrical decompositions along `psiV`.

  `psiV : ℝⁿ → (-1,1)ⁿ` is a coordinatewise homeomorphism onto the open cube.  The key facts:

  * the projection of an `IsCell` is its base (hence an `IsCell`);
  * `projLast A = Fin.init '' A`;
  * `psiV ⁻¹' (projLast A) = projLast (psiV ⁻¹' A)` for `A ⊆ ocube`;
  * `psiV ⁻¹' κ` of an `IsCell` `κ ⊆ ocube` is again an `IsCell`.

  For the last point the band boundaries are reflected through `ePsiInv` and the graph values
  through `psiR`.
-/
import Mathlib
import Submission.Work.WilE8.Basic
import Submission.Work.WilE8.Sharp.PsiEReal
import Submission.Work.WilE8.StarR.psiV_preimage_init_ocube

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
namespace Work.WilE8.Sharp

open WilkiesDesign WilkiesDesign.E

/-! ## Bookkeeping for `Fin.snoc` -/

abbrev snocR {n : ℕ} (p : Fin n → ℝ) (x : ℝ) : Fin (n+1) → ℝ := Fin.snoc p x

@[simp] theorem snocR_castSucc {n : ℕ} (p : Fin n → ℝ) (x : ℝ) (i : Fin n) :
    snocR p x (Fin.castSucc i) = p i := Fin.snoc_castSucc _ _ _

@[simp] theorem snocR_last {n : ℕ} (p : Fin n → ℝ) (x : ℝ) : snocR p x (Fin.last n) = x :=
  Fin.snoc_last _ _

theorem init_snocR {n : ℕ} (p : Fin n → ℝ) (x : ℝ) : Fin.init (snocR p x) = p :=
  Fin.init_snoc (α := fun _ => ℝ) x p

theorem snocR_init_self {n : ℕ} (q : Fin (n+1) → ℝ) :
    snocR (Fin.init q) (q (Fin.last n)) = q := Fin.snoc_init_self q

/-! ## Basic facts -/

theorem ocube_subset_cube (n : ℕ) : ocube n ⊆ WilkiesDesign.E.cubeC n :=
  fun _ hx i => le_of_lt (hx i)

theorem projLast_eq_init {n : ℕ} (A : Set (Fin (n+1) → ℝ)) : projLast A = Fin.init '' A := by
  ext x
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨snocR x t, ht, init_snocR x t⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z (Fin.last n), by rw [Fin.snoc_init_self]; exact hz⟩

/-- `psiR` is continuous on `(-1,1)`. -/
theorem continuousOn_psiR : ContinuousOn Work.WilE10.psiR (Set.Ioo (-1:ℝ) 1) := by
  intro u hu
  rw [Set.mem_Ioo] at hu
  have hpos : 0 < 1 - u ^ 2 := by nlinarith
  change ContinuousWithinAt (fun x : ℝ => x / Real.sqrt (1 - x ^ 2)) (Set.Ioo (-1:ℝ) 1) u
  exact ContinuousAt.continuousWithinAt
    (ContinuousAt.div continuousAt_id
      ((continuous_const.sub (continuous_id.pow 2)).continuousAt.sqrt)
      (ne_of_gt (Real.sqrt_pos.mpr hpos)))

/-- Precomposition with `psiV` preserves `ContinuousOn`. -/
theorem continuousOn_comp_psiV {n : ℕ} {β : Type*} [TopologicalSpace β]
    {C : Set (Fin n → ℝ)} {g : (Fin n → ℝ) → β} (hg : ContinuousOn g C) :
    ContinuousOn (fun y : Fin n → ℝ => g (psiV y)) (psiV ⁻¹' C) :=
  hg.comp (continuous_psiV n).continuousOn (fun _ hy => hy)

/-! ## The projection of a cell -/

/-- The projection of an `IsCell` (the base of the cylinder) is the base cell. -/
theorem isCell_projLast {n : ℕ} {κ : Set (Fin (n+1) → ℝ)} (h : IsCell (n+1) κ) :
    IsCell n (projLast κ) := by
  cases h with
  | graph hC f hf =>
      rename_i C
      have hset : Fin.init '' {z : Fin (n+1) → ℝ |
          Fin.init z ∈ C ∧ z (Fin.last n) = f (Fin.init z)} = C := by
        refine Set.Subset.antisymm (fun x hx => ?_) (fun y hy => ?_)
        · obtain ⟨z, hz, rfl⟩ := hx; exact hz.1
        · exact ⟨snocR y (f y), ⟨by rw [init_snocR]; exact hy, by rw [snocR_last, init_snocR]⟩, init_snocR y (f y)⟩
      rw [projLast_eq_init, hset]
      exact hC
  | band hC a b ha hb hab =>
      rename_i C
      have hset : Fin.init '' {z : Fin (n+1) → ℝ | Fin.init z ∈ C ∧
          a (Fin.init z) < ↑(z (Fin.last n)) ∧ ↑(z (Fin.last n)) < b (Fin.init z)} = C := by
        refine Set.Subset.antisymm (fun x hx => ?_) (fun y hy => ?_)
        · obtain ⟨z, hz, rfl⟩ := hx; exact hz.1
        · obtain ⟨t, ht1, ht2⟩ := EReal.lt_iff_exists_real_btwn.mp (hab y hy)
          exact ⟨snocR y t,
            ⟨by rw [init_snocR]; exact hy, by rw [snocR_last, init_snocR]; exact ht1,
                 by rw [snocR_last, init_snocR]; exact ht2⟩, init_snocR y t⟩
      rw [projLast_eq_init, hset]
      exact hC

/-! ## Strictness of `ePsiInv` on the relevant range -/

/-- `ePsiInv` is strictly increasing across the range in which the band boundaries live. -/
theorem ePsiInv_lt_of_lt {a b : EReal} (hab : a < b) (ha : a < (1:ℝ)) (hb : (-1:ℝ) < b) :
    ePsiInv a < ePsiInv b := by
  have hmaxlt : max a (((-1:ℝ)) : EReal) < min b ((1:ℝ) : EReal) := by
    rw [max_lt_iff]
    exact ⟨lt_min hab ha, lt_min hb (EReal.coe_lt_coe (by norm_num : (-1:ℝ) < 1))⟩
  obtain ⟨q, hq1, hq2⟩ := EReal.lt_iff_exists_real_btwn.mp hmaxlt
  have hca : a < (q : EReal) := lt_of_le_of_lt (le_max_left _ _) hq1
  have hcb : (q : EReal) < b := lt_of_lt_of_le hq2 (min_le_left _ _)
  have hcq_neg : (-1:ℝ) < q := EReal.coe_lt_coe_iff.mp (lt_of_le_of_lt (le_max_right _ _) hq1)
  have hcq_pos : q < 1 := EReal.coe_lt_coe_iff.mp (lt_of_lt_of_le hq2 (min_le_right _ _))
  have habs : |q| < 1 := abs_lt.mpr ⟨hcq_neg, hcq_pos⟩
  have hpsi : psi (Work.WilE10.psiR q) = q := Work.WilE10.psi_psiR habs
  have ha' : a < ((psi (Work.WilE10.psiR q) : ℝ) : EReal) := by rw [hpsi]; exact hca
  have hb' : ((psi (Work.WilE10.psiR q) : ℝ) : EReal) < b := by rw [hpsi]; exact hcb
  exact lt_trans (ePsiInv_lt_coe_iff.mpr ha') (coe_lt_ePsiInv_iff.mpr hb')

/-! ## Pullback of the two cell constructors -/

theorem psiV_preimage_graph {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hf : ∀ y ∈ C, |f y| < 1) :
    psiV ⁻¹' {z : Fin (n+1) → ℝ | Fin.init z ∈ C ∧ z (Fin.last n) = f (Fin.init z)}
      = {z : Fin (n+1) → ℝ | Fin.init z ∈ psiV ⁻¹' C ∧
          z (Fin.last n) = Work.WilE10.psiR (f (psiV (Fin.init z)))} := by
  ext x
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Work.WilE8.StarR.init_psiV]
  constructor
  · rintro ⟨h1, h2⟩
    have hf1 : |f (psiV (Fin.init x))| < 1 := hf _ h1
    refine ⟨h1, ?_⟩
    have h3 : psi (x (Fin.last n)) = f (psiV (Fin.init x)) := h2
    rw [← Work.WilE10.psi_psiR hf1] at h3
    exact Work.WilE10.psi_injective h3
  · rintro ⟨h1, h2⟩
    have hf1 : |f (psiV (Fin.init x))| < 1 := hf _ h1
    refine ⟨h1, ?_⟩
    have h3 : psi (x (Fin.last n)) = f (psiV (Fin.init x)) := by
      rw [h2, Work.WilE10.psi_psiR hf1]
    exact h3

theorem psiV_preimage_band {n : ℕ} {C : Set (Fin n → ℝ)} {a b : (Fin n → ℝ) → EReal} :
    psiV ⁻¹' {z : Fin (n+1) → ℝ | Fin.init z ∈ C ∧
        a (Fin.init z) < ↑(z (Fin.last n)) ∧ ↑(z (Fin.last n)) < b (Fin.init z)}
      = {z : Fin (n+1) → ℝ | Fin.init z ∈ psiV ⁻¹' C ∧
          ePsiInv (a (psiV (Fin.init z))) < ↑(z (Fin.last n)) ∧
          ↑(z (Fin.last n)) < ePsiInv (b (psiV (Fin.init z)))} := by
  ext x
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Work.WilE8.StarR.init_psiV]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, ePsiInv_lt_coe_iff.mpr h2, coe_lt_ePsiInv_iff.mpr h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, ePsiInv_lt_coe_iff.mp h2, coe_lt_ePsiInv_iff.mp h3⟩

/-! ## The main transport lemma -/

theorem psiV_preimage_isCell : ∀ (n : ℕ) {κ : Set (Fin n → ℝ)},
    IsCell n κ → κ.Nonempty → κ ⊆ ocube n → IsCell n (psiV ⁻¹' κ) := by
  intro n
  induction n with
  | zero =>
      intro κ h hne hoc
      cases h with
      | zero => rw [Set.preimage_univ]; exact IsCell.zero
  | succ n ih =>
      intro κ h hne hoc
      cases h with
      | graph hC f hf =>
          rename_i C
          have hCne : C.Nonempty := by
            obtain ⟨z, hz1, hz2⟩ := hne
            exact ⟨Fin.init z, hz1⟩
          have hCoc : C ⊆ ocube n := by
            intro y hy
            have hz : snocR y (f y) ∈ ({z : Fin (n+1) → ℝ |
                Fin.init z ∈ C ∧ z (Fin.last n) = f (Fin.init z)} : Set (Fin (n+1) → ℝ)) := by
              simp only [Set.mem_ofPred_eq, init_snocR, snocR_last]
              exact ⟨hy, trivial⟩
            intro i
            have := hoc hz (Fin.castSucc i)
            simpa [snocR_castSucc] using this
          have hCellC : IsCell n (psiV ⁻¹' C) := ih hC hCne hCoc
          have hf1 : ∀ y ∈ C, |f y| < 1 := by
            intro y hy
            have hz : snocR y (f y) ∈ ({z : Fin (n+1) → ℝ |
                Fin.init z ∈ C ∧ z (Fin.last n) = f (Fin.init z)} : Set (Fin (n+1) → ℝ)) := by
              simp only [Set.mem_ofPred_eq, init_snocR, snocR_last]
              exact ⟨hy, trivial⟩
            have hmem := hoc hz (Fin.last n)
            rwa [snocR_last] at hmem
          have hcont : ContinuousOn (fun y : Fin n → ℝ => Work.WilE10.psiR (f (psiV y)))
              (psiV ⁻¹' C) :=
            continuousOn_psiR.comp (continuousOn_comp_psiV hf)
              (fun y hy => abs_lt.mp (hf1 (psiV y) hy))
          rw [psiV_preimage_graph hf1]
          exact IsCell.graph hCellC _ hcont
      | band hC a b ha hb hab =>
          rename_i C
          have hCne : C.Nonempty := by
            obtain ⟨z, hz1, hz2, hz3⟩ := hne
            exact ⟨Fin.init z, hz1⟩
          have hCoc : C ⊆ ocube n := by
            intro y hy
            obtain ⟨t, ht1, ht2⟩ := EReal.lt_iff_exists_real_btwn.mp (hab y hy)
            have hz : snocR y t ∈ ({z : Fin (n+1) → ℝ | Fin.init z ∈ C ∧
                a (Fin.init z) < ↑(z (Fin.last n)) ∧ ↑(z (Fin.last n)) < b (Fin.init z)}
                : Set (Fin (n+1) → ℝ)) := by
              simp only [Set.mem_ofPred_eq, init_snocR, snocR_last]
              exact ⟨hy, ht1, ht2⟩
            intro i
            have := hoc hz (Fin.castSucc i)
            simpa [snocR_castSucc] using this
          have hCellC : IsCell n (psiV ⁻¹' C) := ih hC hCne hCoc
          have hfib : ∀ y ∈ C, a y < (1:ℝ) ∧ (-1:ℝ) < b y := by
            intro y hy
            obtain ⟨t, ht1, ht2⟩ := EReal.lt_iff_exists_real_btwn.mp (hab y hy)
            have hz : snocR y t ∈ ({z : Fin (n+1) → ℝ | Fin.init z ∈ C ∧
                a (Fin.init z) < ↑(z (Fin.last n)) ∧ ↑(z (Fin.last n)) < b (Fin.init z)}
                : Set (Fin (n+1) → ℝ)) := by
              simp only [Set.mem_ofPred_eq, init_snocR, snocR_last]
              exact ⟨hy, ht1, ht2⟩
            have hmem := hoc hz (Fin.last n)
            rw [snocR_last, abs_lt] at hmem
            exact ⟨lt_trans ht1 (EReal.coe_lt_coe hmem.2),
              lt_trans (EReal.coe_lt_coe hmem.1) ht2⟩
          have hcontA : ContinuousOn (fun y : Fin n → ℝ => ePsiInv (a (psiV y))) (psiV ⁻¹' C) :=
            Continuous.comp_continuousOn continuous_ePsiInv (continuousOn_comp_psiV ha)
          have hcontB : ContinuousOn (fun y : Fin n → ℝ => ePsiInv (b (psiV y))) (psiV ⁻¹' C) :=
            Continuous.comp_continuousOn continuous_ePsiInv (continuousOn_comp_psiV hb)
          have hAB : ∀ y ∈ psiV ⁻¹' C, ePsiInv (a (psiV y)) < ePsiInv (b (psiV y)) :=
            fun y hy => ePsiInv_lt_of_lt (hab _ hy) (hfib _ hy).1 (hfib _ hy).2
          rw [psiV_preimage_band (C := C) (a := a) (b := b)]
          exact IsCell.band hCellC _ _ hcontA hcontB hAB

/-! ## Commutation with the projection -/

theorem psiV_preimage_projLast {n : ℕ} {A : Set (Fin (n+1) → ℝ)} (hA : A ⊆ ocube (n+1)) :
    psiV ⁻¹' (projLast A) = projLast (psiV ⁻¹' A) := by
  have h := Work.WilE8.StarR.psiV_preimage_init_ocube (n := n) (Z := A)
  have hset : WilkiesDesign.E.cubeC (n+1) ∩ (A ∩ ocube (n+1)) = A := by
    refine Set.Subset.antisymm (fun z hz => hz.2.1) (fun z hz => ⟨?_, hz, hA hz⟩)
    exact ocube_subset_cube (n+1) (hA hz)
  rw [hset] at h
  rw [← projLast_eq_init A] at h
  exact h

end Work.WilE8.Sharp
