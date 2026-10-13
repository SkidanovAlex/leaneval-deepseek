import Mathlib
import Submission.Work.WilG4c.StepCellGraph
import Submission.Work.WilG4c.StepCellAux1
import Submission.Work.WilG4c.StepCellAux2
import Submission.Work.Wilkies.Defs

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## Continuity helpers -/

theorem continuous_fin_init {m : ℕ} :
    Continuous (fun z : Fin (m + 1) → ℝ => Fin.init z) := by
  rw [continuous_pi_iff]
  intro i
  exact continuous_apply i.castSucc

theorem continuous_fin_append {p N : ℕ} (l : Fin p → ℝ) :
    Continuous (fun u : Fin N → ℝ => Fin.append l u) := by
  rw [continuous_pi_iff]
  intro i
  cases i using Fin.addCases with
  | left i' =>
    have h : (fun u : Fin N → ℝ => Fin.append l u (Fin.castAdd N i')) = fun _ => l i' := by
      funext u; exact Fin.append_left l u i'
    rw [h]; exact continuous_const
  | right j =>
    have h : (fun u : Fin N → ℝ => Fin.append l u (Fin.natAdd p j)) = fun u => u j := by
      funext u; exact Fin.append_right l u j
    rw [h]; exact continuous_apply j

/-! ## Continuity of the fibre ends on the projection of a cell -/

/-- The fibre ends of a cell are continuous on the projection of the cell. -/
theorem fibreEndCont (m : ℕ) (κ : Set (Fin (m + 1) → ℝ)) (hκ : IsCell (m + 1) κ)
    (hI : ∀ z ∈ κ, z (Fin.last m) ∈ Set.Ioo (0 : ℝ) 1)
    (lo hi : (Fin m → ℝ) → ℝ)
    (hlo : ∀ l : Fin m → ℝ, (∃ x : ℝ, Fin.snoc l x ∈ κ) →
      (∀ x : ℝ, Fin.snoc l x ∈ κ → lo l ≤ x) ∧
      (∀ u : ℝ, lo l < u → ∃ x : ℝ, Fin.snoc l x ∈ κ ∧ x < u))
    (hhi : ∀ l : Fin m → ℝ, (∃ x : ℝ, Fin.snoc l x ∈ κ) →
      (∀ x : ℝ, Fin.snoc l x ∈ κ → x ≤ hi l) ∧
      (∀ u : ℝ, u < hi l → ∃ x : ℝ, Fin.snoc l x ∈ κ ∧ u < x)) :
    ContinuousOn lo (Fin.init '' κ) ∧ ContinuousOn hi (Fin.init '' κ) := by
  classical
  cases hκ with
  | graph hC f hf =>
    rename_i C
    set K : Set (Fin (m + 1) → ℝ) :=
      {z | Fin.init z ∈ C ∧ z (Fin.last m) = f (Fin.init z)} with hKdef
    have hK : Fin.init '' K = C := by
      rw [hKdef]
      ext q
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz.1
      · intro hq
        refine ⟨Fin.snoc q (f q), ?_, by simp⟩
        rw [Set.mem_ofPred_eq]
        simp only [Fin.init_snoc, Fin.snoc_last]
        exact ⟨hq, trivial⟩
    have hfib : ∀ l : Fin m → ℝ, l ∈ C → Fin.snoc l (f l) ∈ K := by
      intro l hl
      rw [hKdef, Set.mem_ofPred_eq]
      simp only [Fin.init_snoc, Fin.snoc_last]
      exact ⟨hl, trivial⟩
    have hval : ∀ l : Fin m → ℝ, l ∈ C → lo l = f l := by
      intro l hl
      have hmem : Fin.snoc l (f l) ∈ K := hfib l hl
      obtain ⟨h1, h2⟩ := hlo l ⟨f l, hmem⟩
      have hle : lo l ≤ f l := h1 (f l) hmem
      rcases lt_or_eq_of_le hle with hlt | heq
      · obtain ⟨x, hxK, hxlt⟩ := h2 (f l) hlt
        have hxeq : x = f l := by
          rw [hKdef, Set.mem_ofPred_eq] at hxK
          simp only [Fin.init_snoc, Fin.snoc_last] at hxK
          exact hxK.2
        exact absurd hxlt (not_lt.mpr (le_of_eq hxeq.symm))
      · exact heq
    have hval' : ∀ l : Fin m → ℝ, l ∈ C → hi l = f l := by
      intro l hl
      have hmem : Fin.snoc l (f l) ∈ K := hfib l hl
      obtain ⟨h1, h2⟩ := hhi l ⟨f l, hmem⟩
      have hle : f l ≤ hi l := h1 (f l) hmem
      rcases lt_or_eq_of_le hle with hlt | heq
      · obtain ⟨x, hxK, hxlt⟩ := h2 (f l) hlt
        have hxeq : x = f l := by
          rw [hKdef, Set.mem_ofPred_eq] at hxK
          simp only [Fin.init_snoc, Fin.snoc_last] at hxK
          exact hxK.2
        exact absurd (hxeq ▸ hxlt) (lt_irrefl _)
      · exact heq.symm
    constructor
    · rw [hK]; exact hf.congr hval
    · rw [hK]; exact hf.congr hval'
  | band hC a b ha hb hab =>
    rename_i C
    set K : Set (Fin (m + 1) → ℝ) :=
      {z | Fin.init z ∈ C ∧ a (Fin.init z) < ((z (Fin.last m) : ℝ) : EReal) ∧
        ((z (Fin.last m) : ℝ) : EReal) < b (Fin.init z)} with hKdef
    have hK : Fin.init '' K = C := by
      rw [hKdef]
      ext q
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz.1
      · intro hq
        obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.mp (hab q hq)
        refine ⟨Fin.snoc q r, ?_, by simp⟩
        rw [Set.mem_ofPred_eq]
        simp only [Fin.init_snoc, Fin.snoc_last]
        exact ⟨hq, hr1, hr2⟩
    have hmem : ∀ (l : Fin m → ℝ) (x : ℝ), l ∈ C →
        (Fin.snoc l x ∈ K ↔ a l < ((x : ℝ) : EReal) ∧ ((x : ℝ) : EReal) < b l) := by
      intro l x hl
      rw [hKdef, Set.mem_ofPred_eq]
      simp only [Fin.init_snoc, Fin.snoc_last]
      exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨hl, h.1, h.2⟩⟩
    have hfib : ∀ l : Fin m → ℝ, l ∈ C → ∃ x : ℝ, Fin.snoc l x ∈ K := by
      intro l hl
      obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.mp (hab l hl)
      exact ⟨r, (hmem l r hl).mpr ⟨hr1, hr2⟩⟩
    have key_lo : ∀ l : Fin m → ℝ, l ∈ C → ((lo l : ℝ) : EReal) = a l := by
      intro l hl
      refine le_antisymm ?_ ?_
      · by_contra hcon
        rw [not_le] at hcon
        obtain ⟨x0, hx0K⟩ := hfib l hl
        have hx0 := (hmem l x0 hl).mp hx0K
        have hmin : a l < min (((x0 : ℝ) : EReal)) (((lo l : ℝ) : EReal)) :=
          lt_min hx0.1 hcon
        obtain ⟨q, hq1, hq2⟩ := EReal.lt_iff_exists_real_btwn.mp hmin
        have hq2' : ((q : ℝ) : EReal) < b l :=
          lt_trans (lt_of_lt_of_le hq2 (min_le_left _ _)) hx0.2
        have hqK : Fin.snoc l q ∈ K := (hmem l q hl).mpr ⟨hq1, hq2'⟩
        have hle : lo l ≤ q := (hlo l ⟨x0, hx0K⟩).1 q hqK
        have hcoe : ((lo l : ℝ) : EReal) ≤ ((q : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr hle
        have hlt : ((q : ℝ) : EReal) < ((lo l : ℝ) : EReal) :=
          lt_of_lt_of_le hq2 (min_le_right _ _)
        exact absurd hcoe (not_le.mpr hlt)
      · by_contra hcon
        rw [not_le] at hcon
        obtain ⟨q, hq1, hq2⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
        have hqgt : lo l < q := EReal.coe_lt_coe_iff.mp hq1
        obtain ⟨x, hxK, hxlt⟩ := (hlo l (hfib l hl)).2 q hqgt
        have hx1 : a l < ((x : ℝ) : EReal) := ((hmem l x hl).mp hxK).1
        have hx2 : ((x : ℝ) : EReal) < a l :=
          lt_trans (EReal.coe_lt_coe_iff.mpr hxlt) hq2
        exact absurd (lt_trans hx1 hx2) (lt_irrefl _)
    have key_hi : ∀ l : Fin m → ℝ, l ∈ C → ((hi l : ℝ) : EReal) = b l := by
      intro l hl
      refine le_antisymm ?_ ?_
      · by_contra hcon
        rw [not_le] at hcon
        obtain ⟨q, hq1, hq2⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
        have hqgt : q < hi l := EReal.coe_lt_coe_iff.mp hq2
        obtain ⟨x, hxK, hxlt⟩ := (hhi l (hfib l hl)).2 q hqgt
        have hx1 : ((x : ℝ) : EReal) < b l := ((hmem l x hl).mp hxK).2
        have hx2 : b l < ((x : ℝ) : EReal) :=
          lt_trans hq1 (EReal.coe_lt_coe_iff.mpr hxlt)
        exact absurd (lt_trans hx2 hx1) (lt_irrefl _)
      · by_contra hcon
        rw [not_le] at hcon
        obtain ⟨x0, hx0K⟩ := hfib l hl
        have hx0 := (hmem l x0 hl).mp hx0K
        have hmin : b l > max (((x0 : ℝ) : EReal)) (((hi l : ℝ) : EReal)) :=
          max_lt hx0.2 hcon
        obtain ⟨q, hq1, hq2⟩ := EReal.lt_iff_exists_real_btwn.mp hmin
        have hq1' : a l < ((q : ℝ) : EReal) :=
          lt_trans hx0.1 (lt_of_le_of_lt (le_max_left _ _) hq1)
        have hqK : Fin.snoc l q ∈ K := (hmem l q hl).mpr ⟨hq1', hq2⟩
        have hle : q ≤ hi l := (hhi l ⟨x0, hx0K⟩).1 q hqK
        have hcoe : ((q : ℝ) : EReal) ≤ ((hi l : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr hle
        have hlt : ((hi l : ℝ) : EReal) < ((q : ℝ) : EReal) :=
          lt_of_le_of_lt (le_max_right _ _) hq1
        exact absurd hcoe (not_le.mpr hlt)
    have hcont_lo : ContinuousOn lo C := by
      intro l hl
      have h1 : ContinuousWithinAt (fun x : Fin m → ℝ => ((lo x : ℝ) : EReal)) C l :=
        (ha l hl).congr (fun x hx => key_lo x hx) (key_lo l hl)
      exact (EReal.tendsto_coe).mp h1
    have hcont_hi : ContinuousOn hi C := by
      intro l hl
      have h1 : ContinuousWithinAt (fun x : Fin m → ℝ => ((hi x : ℝ) : EReal)) C l :=
        (hb l hl).congr (fun x hx => key_hi x hx) (key_hi l hl)
      exact (EReal.tendsto_coe).mp h1
    constructor
    · rw [hK]; exact hcont_lo
    · rw [hK]; exact hcont_hi

/-- **Cell tower with continuity.**  Strengthened form of the cell parametrisation: besides the
four properties of `StepCellGraph`, the tower map is continuous in the fibre variable. -/
theorem cellTowerCont_aux (S : SOMin) : ∀ (N : ℕ) (p F0 : ℕ),
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
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
            ∃ t ∈ openCube N, W (Fin.append l t) = y) ∧
          (∀ l ∈ Λ, ContinuousOn (fun t : Fin N → ℝ => W (Fin.append l t)) (openCube N)) := by
  intro N
  induction N with
  | zero =>
    intro p F0
    refine ⟨0, 1, ?_⟩
    intro D C hC hΩ κ hκ hsub Λ hΛ
    refine ⟨fun _ => fun i : Fin 0 => Fin.elim0 i, ?_, ?_, ?_, ?_, ?_⟩
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
    · intro l hl
      refine (continuousOn_const (c := (fun i : Fin 0 => Fin.elim0 i : Fin 0 → ℝ))).congr ?_
      intro t ht
      rfl
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
      have h1 : (Fin.castSucc (Fin.natAdd p j) : Fin (p + N + 1)) =
          Fin.natAdd p (Fin.castSucc j) := by
        apply Fin.ext
        simp
      simp only [Fin.init]
      rw [h1]
      exact hz (Fin.castSucc j)
    have hΛ2 : ∀ l ∈ Λ, ∃ y : Fin N → ℝ, Fin.append l y ∈ Fin.init '' κ := by
      intro l hl
      obtain ⟨y, hy⟩ := hΛ l hl
      exact ⟨Fin.init y, Fin.append (n := N + 1) l y, hy, initAppend_succ l y⟩
    obtain ⟨WN, hWg, hWc, hWm, hWs, hWcont⟩ :=
      hN D (C.image (fun c => Fin.init '' c)) hC2 hΩ2 (Fin.init '' κ)
        (Finset.mem_image.mpr ⟨κ, hκ, rfl⟩) hsub2 Λ hΛ2
    have hside : ∀ z ∈ κ, z (Fin.last (p + N)) ∈ Set.Ioo (0 : ℝ) 1 := by
      intro z hz
      have hz' := hsub hz
      rw [mem_inCubeSet_iff (p := p) (N := N + 1)] at hz'
      have h2 := hz' (Fin.last N)
      rwa [natAdd_last] at h2
    obtain ⟨lo, hi, hlomem, himem, hprops⟩ := h0 D 1 κ (hΩ κ hκ) hside
    have hFEcont : ContinuousOn lo (Fin.init '' κ) ∧ ContinuousOn hi (Fin.init '' κ) :=
      fibreEndCont (p + N) κ hcell hside lo hi
        (fun l hl => ⟨fun x hx => ((hprops l hl).1 x hx).1, (hprops l hl).2.1⟩)
        (fun l hl => ⟨fun x hx => ((hprops l hl).1 x hx).2, (hprops l hl).2.2⟩)
    have hpad : ∀ j : Fin N, graphOf (fun w : Fin (p + N + 1) → ℝ => WN (Fin.init w) j) ∈
        S.Ω (aN + aP) (MvPolynomial.eval ![D, 1] (bN + MvPolynomial.C 2))
          (p + N + 1 + 1) := by
      intro j
      exact hP aN D bN (fun z : Fin (p + N) → ℝ => WN z j) (hWg j)
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
    refine ⟨WF lo hi WN, ?_, ?_, ?_, ?_, ?_⟩
    · intro j
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
    · intro l hl t ht
      rw [openCube, Set.mem_ofPred_eq] at ht
      intro i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · rw [WF_castSucc_apply lo hi WN l t j]
        exact hWc l hl (Fin.init t) (fun k => ht (Fin.castSucc k)) j
      · rw [WF_last_apply lo hi WN l t]
        have hu : Fin.init t ∈ openCube N := fun k => ht (Fin.castSucc k)
        exact (hfib (Fin.append (n := N) l (WN (Fin.append (n := N) l (Fin.init t))))
          (hWm l hl (Fin.init t) hu)).2.1 (t (Fin.last N)) (ht (Fin.last N))
    · intro l hl t ht
      rw [openCube, Set.mem_ofPred_eq] at ht
      have hu : Fin.init t ∈ openCube N := fun k => ht (Fin.castSucc k)
      rw [WF_append_last lo hi WN l t]
      exact (hfib (Fin.append (n := N) l (WN (Fin.append (n := N) l (Fin.init t))))
        (hWm l hl (Fin.init t) hu)).1 (t (Fin.last N)) (ht (Fin.last N))
    · intro l hl y hy
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
    · intro l hl
      have hWcontl : ContinuousOn (fun u : Fin N → ℝ => WN (Fin.append (n := N) l u))
          (openCube N) := hWcont l hl
      have hg1 : ContinuousOn
          (fun t : Fin (N + 1) → ℝ => WN (Fin.append (n := N) l (Fin.init t)))
          (openCube (N + 1)) := by
        refine ContinuousOn.comp (f := fun t : Fin (N + 1) → ℝ => Fin.init t)
          (g := fun u : Fin N → ℝ => WN (Fin.append (n := N) l u))
          (s := openCube (N + 1)) (t := openCube N) hWcontl ?_ ?_
        · exact continuous_fin_init.continuousOn.mono (Set.subset_univ _)
        · intro t ht
          exact fun j => ht (Fin.castSucc j)
      have hU : ContinuousOn (fun t : Fin (N + 1) → ℝ =>
          Fin.append (n := N) l (WN (Fin.append (n := N) l (Fin.init t))))
          (openCube (N + 1)) := by
        refine ContinuousOn.comp (g := fun u : Fin N → ℝ => Fin.append (n := N) l u)
          (f := fun t : Fin (N + 1) → ℝ => WN (Fin.append (n := N) l (Fin.init t)))
          (t := Set.univ) (s := openCube (N + 1)) ?_ hg1 ?_
        · exact (continuous_fin_append (p := p) (N := N) l).continuousOn
        · intro t ht
          exact Set.mem_univ _
      have hLo : ContinuousOn (fun t : Fin (N + 1) → ℝ =>
          lo (Fin.append (n := N) l (WN (Fin.append (n := N) l (Fin.init t)))))
          (openCube (N + 1)) := by
        refine ContinuousOn.comp hFEcont.1 hU ?_
        intro t ht
        exact hWm l hl (Fin.init t) (fun j => ht (Fin.castSucc j))
      have hHi : ContinuousOn (fun t : Fin (N + 1) → ℝ =>
          hi (Fin.append (n := N) l (WN (Fin.append (n := N) l (Fin.init t)))))
          (openCube (N + 1)) := by
        refine ContinuousOn.comp hFEcont.2 hU ?_
        intro t ht
        exact hWm l hl (Fin.init t) (fun j => ht (Fin.castSucc j))
      rw [continuousOn_pi]
      intro i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · exact (continuousOn_pi.mp hg1 j).congr (fun t ht => WF_castSucc_apply lo hi WN l t j)
      · refine (hLo.add ((hHi.sub hLo).mul
          (continuous_apply (Fin.last N)).continuousOn)).congr ?_
        intro t ht
        exact WF_last_apply lo hi WN l t

theorem CellTowerCont (S : WilkiesDesign.SOMin) (p N F0 : ℕ) : ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
    ∀ (D : ℕ) (C : Finset (Set (Fin (p + N) → ℝ))), WilkiesDesign.IsCylDecomp (p + N) C →
      (∀ κ ∈ C, κ ∈ S.Ω F0 D (p + N)) →
      ∀ (κ : Set (Fin (p + N) → ℝ)), κ ∈ C → κ ⊆ Work.WilG4c.inCubeSet p N →
      ∀ (Λ : Set (Fin p → ℝ)), (∀ l ∈ Λ, ∃ y : Fin N → ℝ, Fin.append l y ∈ κ) →
        ∃ Ψ : (Fin p → ℝ) → (Fin N → ℝ) → (Fin N → ℝ),
          (∀ j : Fin N,
            WilkiesDesign.CG.famGraph (fun l t => Ψ l t j) ∈ S.Ω a (MvPolynomial.eval ![D, 1] b) (p + N + 1)) ∧
          (∀ l ∈ Λ, ∀ t ∈ WilkiesDesign.openCube N, Ψ l t ∈ WilkiesDesign.openCube N) ∧
          (∀ l ∈ Λ, ∀ t ∈ WilkiesDesign.openCube N, Fin.append l (Ψ l t) ∈ κ) ∧
          (∀ l ∈ Λ, ∀ y : Fin N → ℝ, Fin.append l y ∈ κ → ∃ t ∈ WilkiesDesign.openCube N, Ψ l t = y) ∧
          (∀ l ∈ Λ, ContinuousOn (fun t : Fin N → ℝ => Ψ l t) (WilkiesDesign.openCube N)) := by
  obtain ⟨a, b, h⟩ := cellTowerCont_aux S N p F0
  refine ⟨a, b, ?_⟩
  intro D C hC hΩ κ hκ hsub Λ hΛ
  obtain ⟨W, hWg, hWc, hWm, hWs, hWcont⟩ := h D C hC hΩ κ hκ hsub Λ hΛ
  refine ⟨fun l t => W (Fin.append l t), ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    have heq : (fun z : Fin (p + N) → ℝ =>
        W (Fin.append (fun i => z (Fin.castAdd N i)) (fun j => z (Fin.natAdd p j))) j)
        = (fun z : Fin (p + N) → ℝ => W z j) := by
      funext z
      rw [Fin.append_castAdd_natAdd]
    show graphOf (fun z : Fin (p + N) → ℝ =>
        W (Fin.append (fun i => z (Fin.castAdd N i)) (fun j => z (Fin.natAdd p j))) j) ∈
      S.Ω a (MvPolynomial.eval ![D, 1] b) (p + N + 1)
    rw [heq]
    exact hWg j
  · intro l hl t ht
    exact hWc l hl t ht
  · intro l hl t ht
    exact hWm l hl t ht
  · intro l hl y hy
    exact hWs l hl y hy
  · intro l hl
    exact hWcont l hl

end Work.WilG4c
