import Mathlib
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilG4c.StepFiberEnds
import Submission.Work.WilG4c.GraphOfComp
import Submission.Work.WilG4c.FibreInterp
import Submission.Work.WilG4c.AffineInterpGraph
import Submission.Work.WilG4c.StepCellAux1

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-! ### Helper lemmas for `StepCellGraph` (part 2: the tower) -/

/-! ## 8. The tower construction -/

/-- The affine interpolant `z ↦ lo (init z) + (hi (init z) − lo (init z)) * z (last)`. -/
def gf {p N : ℕ} (lo hi : (Fin (p + N) → ℝ) → ℝ) : (Fin (p + N + 1) → ℝ) → ℝ :=
  fun z => lo (Fin.init z) + (hi (Fin.init z) - lo (Fin.init z)) * (z (Fin.last (p + N)))

/-- The substitution map carrying the parametrisation of the projected cell. -/
def pf {p N : ℕ} (WN : (Fin (p + N) → ℝ) → (Fin N → ℝ)) :
    (Fin (p + N + 1) → ℝ) → (Fin (p + N + 1) → ℝ) :=
  fun w => Fin.snoc (Fin.append (fun i : Fin p => w (Fin.castSucc (Fin.castAdd N i)))
    (WN (Fin.init w))) (w (Fin.last (p + N)))

/-- The parametrisation of the cell one level up. -/
def WF {p N : ℕ} (lo hi : (Fin (p + N) → ℝ) → ℝ) (WN : (Fin (p + N) → ℝ) → (Fin N → ℝ)) :
    (Fin (p + N + 1) → ℝ) → (Fin (N + 1) → ℝ) :=
  fun w => Fin.snoc (WN (Fin.init w)) (gf lo hi (pf WN w))

theorem gf_snoc {p N : ℕ} (lo hi : (Fin (p + N) → ℝ) → ℝ) (q : Fin (p + N) → ℝ) (s : ℝ) :
    gf lo hi (Fin.snoc q s) = lo q + (hi q - lo q) * s := by
  simp only [gf, Fin.init_snoc, Fin.snoc_last]

theorem pf_snoc {p N : ℕ} (WN : (Fin (p + N) → ℝ) → (Fin N → ℝ)) (l : Fin p → ℝ)
    (u : Fin N → ℝ) (s : ℝ) :
    pf WN (Fin.append (n := N + 1) l (Fin.snoc u s : Fin (N + 1) → ℝ)) =
      Fin.snoc (Fin.append (n := N) l (WN (Fin.append (n := N) l u))) s := by
  have h1 : (fun i : Fin p => Fin.append (n := N + 1) l (Fin.snoc u s : Fin (N + 1) → ℝ)
      (Fin.castSucc (Fin.castAdd N i))) = l := by
    funext i
    rw [castSucc_castAdd]
    exact Fin.append_left l (Fin.snoc u s : Fin (N + 1) → ℝ) i
  have h2 : Fin.init (Fin.append (n := N + 1) l (Fin.snoc u s : Fin (N + 1) → ℝ)) = Fin.append l u := by
    rw [initAppend_succ, Fin.init_snoc]
  have h3 : Fin.append (n := N + 1) l (Fin.snoc u s : Fin (N + 1) → ℝ) (Fin.last (p + N)) = s := by
    rw [← natAdd_last, Fin.append_right, Fin.snoc_last]
  simp only [pf]
  rw [h1, h2, h3]

theorem pf_snoc' {p N : ℕ} (WN : (Fin (p + N) → ℝ) → (Fin N → ℝ)) (l : Fin p → ℝ)
    (u : Fin N → ℝ) (s : ℝ) :
    pf WN (Fin.snoc (Fin.append (n := N) l u) s : Fin (p + N + 1) → ℝ) =
      Fin.snoc (Fin.append (n := N) l (WN (Fin.append (n := N) l u))) s := by
  simp only [pf, Fin.init_snoc, Fin.snoc_castSucc, Fin.append_left, Fin.snoc_last]

theorem pf_left {p N : ℕ} (WN : (Fin (p + N) → ℝ) → (Fin N → ℝ)) (w : Fin (p + N + 1) → ℝ)
    (i : Fin p) : pf WN w (Fin.castSucc (Fin.castAdd N i)) = w (Fin.castSucc (Fin.castAdd N i)) := by
  simp only [pf, Fin.snoc_castSucc, Fin.append_left]

theorem pf_mid {p N : ℕ} (WN : (Fin (p + N) → ℝ) → (Fin N → ℝ)) (w : Fin (p + N + 1) → ℝ)
    (j : Fin N) : pf WN w (Fin.castSucc (Fin.natAdd p j)) = WN (Fin.init w) j := by
  simp only [pf, Fin.snoc_castSucc, Fin.append_right]

theorem pf_last {p N : ℕ} (WN : (Fin (p + N) → ℝ) → (Fin N → ℝ)) (w : Fin (p + N + 1) → ℝ) :
    pf WN w (Fin.last (p + N)) = w (Fin.last (p + N)) := by
  simp only [pf, Fin.snoc_last]

theorem WF_castSucc {p N : ℕ} (lo hi : (Fin (p + N) → ℝ) → ℝ)
    (WN : (Fin (p + N) → ℝ) → (Fin N → ℝ)) (w : Fin (p + N + 1) → ℝ) (j : Fin N) :
    WF lo hi WN w (Fin.castSucc j) = WN (Fin.init w) j := by
  simp only [WF, Fin.snoc_castSucc]

theorem WF_last {p N : ℕ} (lo hi : (Fin (p + N) → ℝ) → ℝ)
    (WN : (Fin (p + N) → ℝ) → (Fin N → ℝ)) (w : Fin (p + N + 1) → ℝ) :
    WF lo hi WN w (Fin.last N) = gf lo hi (pf WN w) := by
  simp only [WF, Fin.snoc_last]

/-! ## 8b. The computation rules at the statement's shapes -/

theorem WF_castSucc_apply {p N : ℕ} (lo hi : (Fin (p + N) → ℝ) → ℝ)
    (WN : (Fin (p + N) → ℝ) → (Fin N → ℝ)) (l : Fin p → ℝ) (t : Fin (N + 1) → ℝ)
    (j : Fin N) :
    WF lo hi WN (Fin.append (n := N + 1) l t) (Fin.castSucc j) =
      WN (Fin.append (n := N) l (Fin.init t)) j := by
  rw [WF_castSucc]
  congr 1
  exact initAppend_succ l t

theorem WF_last_apply {p N : ℕ} (lo hi : (Fin (p + N) → ℝ) → ℝ)
    (WN : (Fin (p + N) → ℝ) → (Fin N → ℝ)) (l : Fin p → ℝ) (t : Fin (N + 1) → ℝ) :
    WF lo hi WN (Fin.append (n := N + 1) l t) (Fin.last N) =
      lo (Fin.append (n := N) l (WN (Fin.append (n := N) l (Fin.init t)))) +
      (hi (Fin.append (n := N) l (WN (Fin.append (n := N) l (Fin.init t)))) -
       lo (Fin.append (n := N) l (WN (Fin.append (n := N) l (Fin.init t))))) *
        (t (Fin.last N)) := by
  have ht : Fin.append (n := N + 1) l t = Fin.append (n := N + 1) l
      (Fin.snoc (Fin.init t) (t (Fin.last N)) : Fin (N + 1) → ℝ) := by
    simp only [Fin.snoc_init_self]
  rw [ht, WF_last, pf_snoc WN l (Fin.init t) (t (Fin.last N)), gf_snoc]

theorem WF_append_last {p N : ℕ} (lo hi : (Fin (p + N) → ℝ) → ℝ)
    (WN : (Fin (p + N) → ℝ) → (Fin N → ℝ)) (l : Fin p → ℝ) (t : Fin (N + 1) → ℝ) :
    Fin.append (n := N + 1) l (WF lo hi WN (Fin.append (n := N + 1) l t)) =
      Fin.snoc (Fin.append (n := N) l (WN (Fin.append (n := N) l (Fin.init t))))
        (lo (Fin.append (n := N) l (WN (Fin.append (n := N) l (Fin.init t)))) +
         (hi (Fin.append (n := N) l (WN (Fin.append (n := N) l (Fin.init t)))) -
          lo (Fin.append (n := N) l (WN (Fin.append (n := N) l (Fin.init t))))) *
           (t (Fin.last N))) := by
  have ht : Fin.append (n := N + 1) l t = Fin.append (n := N + 1) l
      (Fin.snoc (Fin.init t) (t (Fin.last N)) : Fin (N + 1) → ℝ) := by
    simp only [Fin.snoc_init_self]
  rw [ht]
  simp only [WF, Fin.append_snoc, initAppend_succ, Fin.init_snoc]
  rw [pf_snoc' WN l (Fin.init t) (t (Fin.last N)), gf_snoc]

/-! ## 9. The induction -/

theorem stepCellGraph_aux (S : SOMin) : ∀ (N : ℕ) (p F0 : ℕ), ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
    ∀ (D : ℕ) (C : Finset (Set (Fin (p + N) → ℝ))), IsCylDecomp (p + N) C →
      (∀ κ ∈ C, κ ∈ S.Ω F0 D (p + N)) →
      ∀ (κ : Set (Fin (p + N) → ℝ)), κ ∈ C → κ ⊆ inCubeSet p N →
      ∀ (Λ : Set (Fin p → ℝ)), (∀ l ∈ Λ, ∃ y : Fin N → ℝ, Fin.append l y ∈ κ) →
        ∃ W : (Fin (p + N) → ℝ) → (Fin N → ℝ),
          (∀ j : Fin N, graphOf (fun z : Fin (p + N) → ℝ => W z j) ∈
              S.Ω a (MvPolynomial.eval ![D, 1] b) (p + N + 1)) ∧
          (∀ l ∈ Λ, ∀ t ∈ openCube N, W (Fin.append l t) ∈ openCube N) ∧
          (∀ l ∈ Λ, ∀ t ∈ openCube N, Fin.append l (W (Fin.append l t)) ∈ κ) ∧
          (∀ l ∈ Λ, ∀ y : Fin N → ℝ, Fin.append l y ∈ κ →
            ∃ t ∈ openCube N, W (Fin.append l t) = y) := by
  intro N
  induction N with
  | zero =>
    intro p F0
    refine ⟨0, 1, ?_⟩
    intro D C hC hΩ κ hκ hsub Λ hΛ
    refine ⟨fun _ => fun i : Fin 0 => Fin.elim0 i, ?_, ?_, ?_, ?_⟩
    · intro j; exact Fin.elim0 j
    · intro l hl t ht i; exact Fin.elim0 i
    · intro l hl t ht
      obtain ⟨y, hy⟩ := hΛ l hl
      have hU : (fun i : Fin 0 => Fin.elim0 i) = y := by funext i; exact Fin.elim0 i
      simp only [hU]
      exact hy
    · intro l hl y hy
      refine ⟨y, ?_, ?_⟩
      · intro i; exact Fin.elim0 i
      · funext i; exact Fin.elim0 i
  | succ N ih =>
    intro p F0
    obtain ⟨aN, bN, hN⟩ := ih p (F0 + 1)
    obtain ⟨a0, b0, h0⟩ := StepFiberEnds S (p + N) F0
    obtain ⟨aP, hP⟩ := graphOf_pad S (p + N)
    obtain ⟨aA, cA, hA⟩ := AffineInterpGraph S (p + N)
    obtain ⟨Cg1, Cg2, hGC⟩ := GraphOfComp_uniform S (p + N + 1)
    refine ⟨max (max (p + N + 2) (aN + aP))
        (a0 + aA + max (p + N + 2) (aN + aP) + Cg1),
      (bN + MvPolynomial.C 2) + (MvPolynomial.C 2 * b0 + MvPolynomial.C cA)
        + MvPolynomial.C (p + N + 1) * (bN + MvPolynomial.C 3) + MvPolynomial.C Cg2, ?_⟩
    intro D C hC hΩ κ hκ hsub Λ hΛ
    set F₂ : ℕ := max (p + N + 2) (aN + aP) with hF₂
    set D₁ : ℕ := MvPolynomial.eval ![D, 1] (MvPolynomial.C 2 * b0 + MvPolynomial.C cA) with hD₁
    set D₂ : ℕ := MvPolynomial.eval ![D, 1] (bN + MvPolynomial.C 3) with hD₂
    -- the image decomposition
    have hC2 : IsCylDecomp (p + N) (C.image (fun c => Fin.init '' c)) := by
      have h := (WilkiesDesign.IsCylDecomp.eq_2 (p + N) C).mp hC
      exact h.2.2.2
    have hcell : IsCell (p + N + 1) κ := by
      have h := (WilkiesDesign.IsCylDecomp.eq_2 (p + N) C).mp hC
      exact (h.1 κ hκ).1
    have hΩ2 : ∀ Z ∈ C.image (fun c => Fin.init '' c), Z ∈ S.Ω (F0 + 1) D (p + N) := by
      intro Z hZ
      obtain ⟨κ0, hκ0, rfl⟩ := Finset.mem_image.mp hZ
      rw [image_init_eq_projLast]
      exact S.proj (hΩ κ0 hκ0)
    have hsub2 : (Fin.init '' κ) ⊆ inCubeSet p N := by
      rintro z ⟨z0, hz0, rfl⟩
      have hz := hsub hz0
      rw [mem_inCubeSet_iff (p := p) (N := N + 1)] at hz
      rw [mem_inCubeSet_iff (p := p) (N := N)]
      intro j
      have h1 : (Fin.castSucc (Fin.natAdd p j) : Fin (p + N + 1)) = Fin.natAdd p (Fin.castSucc j) := by
        apply Fin.ext
        simp
      simp only [Fin.init]
      rw [h1]
      exact hz (Fin.castSucc j)
    have hΛ2 : ∀ l ∈ Λ, ∃ y : Fin N → ℝ, Fin.append l y ∈ Fin.init '' κ := by
      intro l hl
      obtain ⟨y, hy⟩ := hΛ l hl
      exact ⟨Fin.init y, Fin.append (n := N + 1) l y, hy, initAppend_succ l y⟩
    obtain ⟨WN, hWg, hWc, hWm, hWs⟩ :=
      hN D (C.image (fun c => Fin.init '' c)) hC2 hΩ2 (Fin.init '' κ)
        (Finset.mem_image.mpr ⟨κ, hκ, rfl⟩) hsub2 Λ hΛ2
    -- the fibre ends of κ
    have hside : ∀ z ∈ κ, z (Fin.last (p + N)) ∈ Set.Ioo (0 : ℝ) 1 := by
      intro z hz
      have hz' := hsub hz
      rw [mem_inCubeSet_iff (p := p) (N := N + 1)] at hz'
      have h2 := hz' (Fin.last N)
      rwa [natAdd_last] at h2
    obtain ⟨lo, hi, hlomem, himem, hprops⟩ := h0 D 1 κ (hΩ κ hκ) hside
    -- the padded graphs
    have hpad : ∀ j : Fin N, graphOf (fun w : Fin (p + N + 1) → ℝ => WN (Fin.init w) j) ∈
        S.Ω (aN + aP) (MvPolynomial.eval ![D, 1] (bN + MvPolynomial.C 2))
          (p + N + 1 + 1) := by
      intro j
      exact hP aN D bN (fun z : Fin (p + N) → ℝ => WN z j) (hWg j)
    -- the fibre over `q`
    have hfib : ∀ (q : Fin (p + N) → ℝ), q ∈ Fin.init '' κ →
        (∀ s ∈ Set.Ioo (0 : ℝ) 1, Fin.snoc q (lo q + (hi q - lo q) * s) ∈ κ) ∧
        (∀ s ∈ Set.Ioo (0 : ℝ) 1, lo q + (hi q - lo q) * s ∈ Set.Ioo (0 : ℝ) 1) ∧
        (∀ y : ℝ, Fin.snoc q y ∈ κ →
          ∃ s ∈ Set.Ioo (0 : ℝ) 1, lo q + (hi q - lo q) * s = y) := by
      intro q hqmem
      obtain ⟨z, hz, hzinit⟩ := hqmem
      have hne : (∃ x : ℝ, Fin.snoc q x ∈ κ) := ⟨z (Fin.last (p + N)), by
        rw [← hzinit]
        exact (snoc_init' z).symm ▸ hz⟩
      have h01 : ∀ x : ℝ, Fin.snoc q x ∈ κ → 0 < x ∧ x < 1 := by
        intro x hx
        have h' := hsub hx
        rw [mem_inCubeSet_iff (p := p) (N := N + 1)] at h'
        have h2 := h' (Fin.last N)
        rw [natAdd_last] at h2
        exact (snoc_last' q x) ▸ h2
      have hslice := cell_slice hcell q
      obtain ⟨hint, hsurj⟩ := FibreInterp (F := {x : ℝ | snocM q x ∈ κ}) hne h01 hslice
        (hprops q hne).1 (hprops q hne).2.1 (hprops q hne).2.2
      exact ⟨fun s hs => hint s hs, fun s hs => h01 _ (hint s hs), hsurj⟩
    refine ⟨WF lo hi WN, ?_, ?_, ?_, ?_⟩
    · -- 1. the coordinate graphs
      intro j
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · have h := hpad j'
        simp only [WF_castSucc]
        refine Work.WilG1.Omega.mono h ?_ ?_
        · exact le_trans (le_max_right (p + N + 2) (aN + aP)) (le_max_left _ _)
        · simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C]
          omega
      · have hg : graphOf (gf lo hi) ∈ S.Ω (a0 + aA) D₁ (p + N + 1 + 1) := by
          rw [hD₁]
          exact hA a0 D b0 lo hi hlomem himem
        have hcoord : ∀ i : Fin (p + N + 1),
            graphOf (fun x : Fin (p + N + 1) → ℝ => pf WN x i) ∈ S.Ω F₂ D₂ (p + N + 1 + 1) := by
          intro i
          rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
          · cases i' using Fin.addCases with
            | left i'' =>
                have h := graphOf_coord S (p + N) (Fin.castSucc (Fin.castAdd N i''))
                have heq : (fun x : Fin (p + N + 1) → ℝ =>
                    pf WN x (Fin.castSucc (Fin.castAdd N i'')))
                    = (fun x : Fin (p + N + 1) → ℝ => x (Fin.castSucc (Fin.castAdd N i''))) := by
                  funext x
                  exact pf_left WN x i''
                rw [heq]
                refine Work.WilG1.Omega.mono h ?_ ?_
                · rw [hF₂]; exact le_max_left _ _
                · rw [hD₂]
                  simp only [MvPolynomial.eval_add, MvPolynomial.eval_C]
                  omega
            | right j' =>
                have h := hpad j'
                have heq : (fun x : Fin (p + N + 1) → ℝ =>
                    pf WN x (Fin.castSucc (Fin.natAdd p j')))
                    = (fun x : Fin (p + N + 1) → ℝ => WN (Fin.init x) j') := by
                  funext x
                  exact pf_mid WN x j'
                rw [heq]
                refine Work.WilG1.Omega.mono h ?_ ?_
                · rw [hF₂]; exact le_max_right _ _
                · rw [hD₂]
                  simp only [MvPolynomial.eval_add, MvPolynomial.eval_C]
                  omega
          · have h := graphOf_coord S (p + N) (Fin.last (p + N))
            have heq : (fun x : Fin (p + N + 1) → ℝ => pf WN x (Fin.last (p + N)))
                = (fun x : Fin (p + N + 1) → ℝ => x (Fin.last (p + N))) := by
              funext x
              exact pf_last WN x
            rw [heq]
            refine Work.WilG1.Omega.mono h ?_ ?_
            · rw [hF₂]; exact le_max_left _ _
            · rw [hD₂]
              simp only [MvPolynomial.eval_add, MvPolynomial.eval_C]
              omega
        have hlast := hGC (gf lo hi) (pf WN) hg hcoord
        simp only [WF_last]
        refine Work.WilG1.Omega.mono hlast ?_ ?_
        · exact le_max_right F₂ _
        · rw [hD₁, hD₂]
          simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C]
          omega
    · -- 2. the parametrisation maps the cube into the cube
      intro l hl t ht
      rw [openCube, Set.mem_ofPred_eq] at ht
      intro i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · rw [WF_castSucc_apply lo hi WN l t j]
        exact hWc l hl (Fin.init t) (fun k => ht (Fin.castSucc k)) j
      · rw [WF_last_apply lo hi WN l t]
        have hu : Fin.init t ∈ openCube N := fun k => ht (Fin.castSucc k)
        exact (hfib (Fin.append (n := N) l (WN (Fin.append (n := N) l (Fin.init t))))
          (hWm l hl (Fin.init t) hu)).2.1 (t (Fin.last N)) (ht (Fin.last N))
    · -- 3. the image lies in κ
      intro l hl t ht
      rw [openCube, Set.mem_ofPred_eq] at ht
      have hu : Fin.init t ∈ openCube N := fun k => ht (Fin.castSucc k)
      rw [WF_append_last lo hi WN l t]
      exact (hfib (Fin.append (n := N) l (WN (Fin.append (n := N) l (Fin.init t))))
        (hWm l hl (Fin.init t) hu)).1 (t (Fin.last N)) (ht (Fin.last N))
    · -- 4. surjectivity
      intro l hl y hy
      have hy' : Fin.append l (Fin.init y) ∈ Fin.init '' κ :=
        ⟨Fin.append (n := N + 1) l y, hy, initAppend_succ l y⟩
      obtain ⟨t', ht'mem, ht'eq⟩ := hWs l hl (Fin.init y) hy'
      have hyfib : Fin.snoc (Fin.append (n := N) l (WN (Fin.append (n := N) l t')))
          (y (Fin.last N)) ∈ κ := by
        rw [ht'eq, ← Fin.append_snoc l (Fin.init y) (y (Fin.last N)), Fin.snoc_init_self y]
        exact hy
      obtain ⟨s, hs, hseq⟩ := (hfib (Fin.append (n := N) l (WN (Fin.append (n := N) l t')))
        (hWm l hl t' ht'mem)).2.2 (y (Fin.last N)) hyfib
      refine ⟨Fin.snoc t' s, ?_, ?_⟩
      · intro i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
        · simpa only [Fin.snoc_castSucc] using ht'mem j
        · simpa only [Fin.snoc_last] using hs
      · funext i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
        · rw [WF_castSucc_apply lo hi WN l (Fin.snoc t' s) j]
          simp only [Fin.init_snoc, ht'eq, Fin.init]
        · rw [WF_last_apply lo hi WN l (Fin.snoc t' s)]
          simp only [Fin.init_snoc, Fin.snoc_last]
          exact hseq


end Work.WilG4c
