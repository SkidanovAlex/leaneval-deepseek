/-
  WilG5 / Interior — the charts for the part of `X` inside the open cube.

  `interior_charts` is the "interior half" of the effective algebraic lemma.  The sharp cell
  decomposition (`S.SharpCD`) decomposes `X ∩ openCube n` into finitely many cells `κ`; each
  cell is parametrised (and `ε`-covered) from the cube of dimension `d ≤ μ` by the F-lemma
  (`hF`), which is the content of `Work.WilG5.Interior.cell_charts`, one cell at a time.

  This file performs the assembly:

  * `X ∩ openCube n` is intersected with the open cube (an `Ω`-set) so that it can be fed to
    `SharpCD`; the extra intersection only adds a constant `16 * n + 16` to the degree, which is
    harmless because the cell count and the cell degrees are polynomials in the degree;

  * the per-cell chart families are glued with `Finset.biUnion` over the (attached) cells, and
    their cardinalities are summed;

  * the single polynomial `p` is produced by the bookkeeping lemma
    `Work.WilG5.Interior.count_combine`, which combines the number of cells (`SharpCD`'s
    `b.eval ![D + K, 1]`) with the F-lemma count for every source dimension `μ' ≤ n`
    (uniformity in `μ` comes from summing the finitely many bounds).
-/
import Mathlib
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG5.Defs
import Submission.Work.WilG5.Interior.cell_charts
import Submission.Work.WilG5.Interior.count_combine

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical

namespace Work.WilG5.Interior

open WilkiesDesign WilkiesConjecture

/-! ## Elementary helpers -/

/-- The open cube is contained in the closed cube. -/
theorem openCube_subset_cube01 (n : ℕ) : openCube n ⊆ cube01 n :=
  fun _ hx i => ⟨le_of_lt (hx i).1, le_of_lt (hx i).2⟩

/-- `DimLE` is monotone in the set. -/
theorem dimLE_mono {n μ : ℕ} {X κ : Set (Fin n → ℝ)} (h : DimLE X μ) (hsub : κ ⊆ X) :
    DimLE κ μ := by
  intro e
  have h1 : interior ((fun x : Fin n → ℝ => x ∘ ⇑e) '' κ) ⊆
      interior ((fun x : Fin n → ℝ => x ∘ ⇑e) '' X) :=
    interior_mono (Set.image_mono hsub)
  rw [h e] at h1
  exact le_bot_iff.mp h1

/-- A cylindrical decomposition covers the ambient space.  (In dimension `0` the definition
does not state this explicitly, whence the case split.) -/
theorem cylinder_decomp_cover {n : ℕ} {C : Finset (Set (Fin n → ℝ))}
    (h : IsCylDecomp n C) : ∀ z : Fin n → ℝ, ∃ c ∈ C, z ∈ c := by
  classical
  cases n with
  | zero => intro z
            have hC : C = {Set.univ} := h
            rw [hC]
            exact ⟨Set.univ, Finset.mem_singleton_self Set.univ, trivial⟩
  | succ m => exact h.2.2.1

/-- A member of a cylindrical decomposition is a cell. -/
theorem isCell_of_isCylDecomp {n : ℕ} {C : Finset (Set (Fin n → ℝ))} (h : IsCylDecomp n C)
    {c : Set (Fin n → ℝ)} (hc : c ∈ C) : IsCell n c := by
  classical
  cases n with
  | zero =>
      have hC : C = {Set.univ} := h
      have hc' : c = Set.univ := by
        rw [hC] at hc
        exact Finset.mem_singleton.mp hc
      rw [hc']
      exact IsCell.zero
  | succ m => exact (h.1 c hc).1

/-- A member of a cylindrical decomposition is nonempty. -/
theorem nonempty_of_isCylDecomp {n : ℕ} {C : Finset (Set (Fin n → ℝ))} (h : IsCylDecomp n C)
    {c : Set (Fin n → ℝ)} (hc : c ∈ C) : c.Nonempty := by
  classical
  cases n with
  | zero =>
      have hC : C = {Set.univ} := h
      have hc' : c = Set.univ := by
        rw [hC] at hc
        exact Finset.mem_singleton.mp hc
      rw [hc']
      exact ⟨Fin.elim0, trivial⟩
  | succ m => exact (h.1 c hc).2

/-! ## The charts -/

theorem interior_charts (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hF : ∀ p n, WilkiesDesign.CG.FLem S p n) (F n : ℕ) :
    ∃ p : MvPolynomial (Fin 3) ℝ, (∀ m ∈ p.support, 0 ≤ p.coeff m) ∧
      ∀ (D r : ℕ) (ε : ℝ), 0 < ε → ε < 1 → ∀ (μ : ℕ) (X : Set (Fin n → ℝ)),
        μ ≤ n → X ⊆ WilkiesDesign.cube01 n → X ∈ S.Ω F D n → WilkiesDesign.DimLE X μ →
        ∃ Φ : Finset ((Fin μ → ℝ) → (Fin n → ℝ)),
          (Φ.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), -Real.log ε] p ∧
          (∀ φ ∈ Φ, (∀ t ∈ WilkiesDesign.openCube μ, φ t ∈ X) ∧
            ContDiffOn ℝ r φ (WilkiesDesign.openCube μ) ∧
            ∀ k ≤ r, ∀ t ∈ WilkiesDesign.openCube μ, ‖iteratedFDeriv ℝ k φ t‖ ≤ 1) ∧
          ∀ x ∈ X, x ∈ WilkiesDesign.openCube n → ∃ φ ∈ Φ, ∃ t ∈ WilkiesDesign.openCube μ, dist (φ t) x < ε := by
  classical
  -- The format and the degree of the open cube, and the cell decomposition format.
  obtain ⟨A_cd, b_cd, c_cd, hCD⟩ := hcd (max F (4 * n + 24) + 1) n
  -- Per source dimension `μ' ≤ n`, the F-lemma count polynomial of `cell_charts`.
  choose cOf hcOf using fun μ : Fin (n + 1) =>
    cell_charts S hF n A_cd μ.val (Nat.le_of_lt_succ μ.isLt)
  -- The single bookkeeping polynomial.
  obtain ⟨p, hpnn, hp⟩ := count_combine (c := cOf) b_cd c_cd (16 * n + 16) n
  refine ⟨p, hpnn, ?_⟩
  intro D r ε hε0 hε1 μ X hμ hsub hX hdim
  have hs : 0 ≤ -Real.log ε := by
    have h := Real.log_neg hε0 hε1
    linarith
  -- `X ∩ openCube n` is an `Ω`-set.
  have hXo : X ∩ openCube n ∈ S.Ω (max F (4 * n + 24) + 1) (D + (16 * n + 16)) n := by
    have h1 : X ∈ S.Ω (max F (4 * n + 24)) D n :=
      mem_mono hX _ _ (le_max_left _ _) le_rfl
    have h2 : openCube n ∈ S.Ω (max F (4 * n + 24)) (16 * n + 16) n :=
      mem_mono (openCube_mem (S := S)) _ _ (le_max_right _ _) le_rfl
    have h := S.inter (fun i : Fin 2 => if i = 0 then D else 16 * n + 16)
      (fun i : Fin 2 => if i = 0 then X else openCube n)
      (by intro i
          fin_cases i
          · simpa using h1
          · simpa using h2)
    rw [show (∑ i : Fin 2, (if i = 0 then D else 16 * n + 16)) = D + (16 * n + 16) from by
      simp [Fin.sum_univ_two]] at h
    have hset : (⋂ i : Fin 2, if i = 0 then X else openCube n) = X ∩ openCube n := by
      ext z; simp [Fin.forall_fin_two]
    rwa [hset] at h
  -- Sharp cell decomposition of `X ∩ openCube n`.
  obtain ⟨Cdex, hcyl, hsep, hcard, hdeg⟩ :=
    hCD (D + (16 * n + 16)) 1 (fun _ : Fin 1 => X ∩ openCube n) (fun _ => hXo)
  have hcover : ∀ z : Fin n → ℝ, ∃ c ∈ Cdex, z ∈ c := cylinder_decomp_cover hcyl
  -- The chart family of a single cell `κ ⊆ X ∩ openCube n`.
  have cellFam : ∀ (κ : Set (Fin n → ℝ)), κ ∈ Cdex → κ ⊆ X ∩ openCube n →
      ∃ Ψ : Finset ((Fin μ → ℝ) → (Fin n → ℝ)),
        (Ψ.card : ℝ) ≤ ∑ j : Fin (n + 1),
            |(cOf j).eval
              ![(↑(c_cd.eval (D + (16 * n + 16))) : ℝ), (r : ℝ), (n : ℝ), -Real.log ε]| ∧
        (∀ φ ∈ Ψ, (∀ t ∈ openCube μ, φ t ∈ X) ∧ ContDiffOn ℝ r φ (openCube μ) ∧
          ∀ k ≤ r, ∀ t ∈ openCube μ, ‖iteratedFDeriv ℝ k φ t‖ ≤ 1) ∧
        (∀ x ∈ κ, x ∈ openCube n → ∃ φ ∈ Ψ, ∃ t ∈ openCube μ, dist (φ t) x < ε) := by
    intro κ hκmem hκsub
    have hcell : IsCell n κ := isCell_of_isCylDecomp hcyl hκmem
    have hne : κ.Nonempty := nonempty_of_isCylDecomp hcyl hκmem
    have hκX : κ ⊆ X := fun z hz => (hκsub hz).1
    have hκopen : κ ⊆ openCube n := fun z hz => (hκsub hz).2
    have hκcube : κ ⊆ cube01 n := fun z hz => hsub (hκX hz)
    have hdimκ : DimLE κ μ := dimLE_mono hdim hκX
    have hΩ : κ ∈ S.Ω A_cd (c_cd.eval (D + (16 * n + 16))) n := hdeg κ hκmem
    obtain ⟨Ψ, hΨcard, hΨgood, hΨcov⟩ :=
      hcOf ⟨μ, Nat.lt_succ_of_le hμ⟩ (c_cd.eval (D + (16 * n + 16))) r ε hε0 hε1
        κ hcell hne hκcube hκopen hΩ hdimκ
    refine ⟨Ψ, ?_, ?_, hΨcov⟩
    · have hnn : 0 ≤ (cOf ⟨μ, Nat.lt_succ_of_le hμ⟩).eval
          ![(↑(c_cd.eval (D + (16 * n + 16))) : ℝ), (r : ℝ), (n : ℝ), -Real.log ε] :=
        le_trans (Nat.cast_nonneg _) hΨcard
      have hsingle :
          |(cOf ⟨μ, Nat.lt_succ_of_le hμ⟩).eval
              ![(↑(c_cd.eval (D + (16 * n + 16))) : ℝ), (r : ℝ), (n : ℝ), -Real.log ε]| ≤
            ∑ j : Fin (n + 1),
              |(cOf j).eval
                ![(↑(c_cd.eval (D + (16 * n + 16))) : ℝ), (r : ℝ), (n : ℝ), -Real.log ε]| :=
        Finset.single_le_sum (s := Finset.univ)
          (f := fun j : Fin (n + 1) =>
            |(cOf j).eval
              ![(↑(c_cd.eval (D + (16 * n + 16))) : ℝ), (r : ℝ), (n : ℝ), -Real.log ε]|)
          (a := ⟨μ, Nat.lt_succ_of_le hμ⟩)
          (fun j _ => abs_nonneg _) (Finset.mem_univ _)
      calc (Ψ.card : ℝ)
          ≤ (cOf ⟨μ, Nat.lt_succ_of_le hμ⟩).eval
              ![(↑(c_cd.eval (D + (16 * n + 16))) : ℝ), (r : ℝ), (n : ℝ), -Real.log ε] := hΨcard
        _ = |(cOf ⟨μ, Nat.lt_succ_of_le hμ⟩).eval
              ![(↑(c_cd.eval (D + (16 * n + 16))) : ℝ), (r : ℝ), (n : ℝ), -Real.log ε]| :=
              (abs_of_nonneg hnn).symm
        _ ≤ ∑ j : Fin (n + 1),
              |(cOf j).eval
                ![(↑(c_cd.eval (D + (16 * n + 16))) : ℝ), (r : ℝ), (n : ℝ), -Real.log ε]| :=
              hsingle
    · intro φ hφ
      obtain ⟨h1, h2, h3⟩ := hΨgood φ hφ
      exact ⟨fun t ht => hκX (h1 t ht), h2, h3⟩
  -- The union of the chart families of the cells contained in `X ∩ openCube n`.
  let Φf : {κ // κ ∈ Cdex} → Finset ((Fin μ → ℝ) → (Fin n → ℝ)) :=
    fun κ => if h : κ.val ⊆ X ∩ openCube n then
      Classical.choose (cellFam κ.val κ.property h) else ∅
  let Φ : Finset ((Fin μ → ℝ) → (Fin n → ℝ)) := Cdex.attach.biUnion Φf
  have hunfold : ∀ κ : {κ // κ ∈ Cdex}, Φf κ =
      if h : κ.val ⊆ X ∩ openCube n then Classical.choose (cellFam κ.val κ.property h)
      else ∅ := fun _ => rfl
  -- Cardinality.
  have hΦcard : (Φ.card : ℝ) ≤ (Cdex.card : ℝ) *
      (∑ j : Fin (n + 1),
        |(cOf j).eval
          ![(↑(c_cd.eval (D + (16 * n + 16))) : ℝ), (r : ℝ), (n : ℝ), -Real.log ε]|) := by
    have h1 : Φ.card ≤ ∑ κ ∈ Cdex.attach, (Φf κ).card := Finset.card_biUnion_le
    have h2 : ∀ κ ∈ Cdex.attach,
        ((Φf κ).card : ℝ) ≤ ∑ j : Fin (n + 1),
          |(cOf j).eval
            ![(↑(c_cd.eval (D + (16 * n + 16))) : ℝ), (r : ℝ), (n : ℝ), -Real.log ε]| := by
      intro κ _
      rw [hunfold κ]
      by_cases h : κ.val ⊆ X ∩ openCube n
      · rw [dite_eq_left h]
        exact (Classical.choose_spec (cellFam κ.val κ.property h)).1
      · rw [dite_eq_right h]
        simp only [Finset.card_empty, Nat.cast_zero]
        exact Finset.sum_nonneg (fun j _ => abs_nonneg _)
    calc (Φ.card : ℝ) ≤ ((∑ κ ∈ Cdex.attach, (Φf κ).card : ℕ) : ℝ) := by exact_mod_cast h1
      _ = ∑ κ ∈ Cdex.attach, ((Φf κ).card : ℝ) := by push_cast; rfl
      _ ≤ ∑ κ ∈ Cdex.attach, ∑ j : Fin (n + 1),
            |(cOf j).eval
              ![(↑(c_cd.eval (D + (16 * n + 16))) : ℝ), (r : ℝ), (n : ℝ), -Real.log ε]| :=
          Finset.sum_le_sum h2
      _ = (Cdex.attach.card : ℝ) * (∑ j : Fin (n + 1),
            |(cOf j).eval
              ![(↑(c_cd.eval (D + (16 * n + 16))) : ℝ), (r : ℝ), (n : ℝ), -Real.log ε]|) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (Cdex.card : ℝ) * (∑ j : Fin (n + 1),
            |(cOf j).eval
              ![(↑(c_cd.eval (D + (16 * n + 16))) : ℝ), (r : ℝ), (n : ℝ), -Real.log ε]|) := by
          rw [Finset.card_attach]
  refine ⟨Φ, ?_, ?_, ?_⟩
  · -- the cardinality bound
    refine le_trans hΦcard ?_
    have hb : (Cdex.card : ℝ) ≤ (b_cd.eval ![D + (16 * n + 16), 1] : ℝ) := by
      exact_mod_cast hcard
    have hnn : 0 ≤ ∑ j : Fin (n + 1),
        |(cOf j).eval
          ![(↑(c_cd.eval (D + (16 * n + 16))) : ℝ), (r : ℝ), (n : ℝ), -Real.log ε]| :=
      Finset.sum_nonneg (fun j _ => abs_nonneg _)
    calc (Cdex.card : ℝ) * (∑ j : Fin (n + 1),
          |(cOf j).eval
            ![(↑(c_cd.eval (D + (16 * n + 16))) : ℝ), (r : ℝ), (n : ℝ), -Real.log ε]|)
        ≤ (b_cd.eval ![D + (16 * n + 16), 1] : ℝ) * (∑ j : Fin (n + 1),
          |(cOf j).eval
            ![(↑(c_cd.eval (D + (16 * n + 16))) : ℝ), (r : ℝ), (n : ℝ), -Real.log ε]|) :=
          mul_le_mul_of_nonneg_right hb hnn
      _ ≤ p.eval ![(D : ℝ), (r : ℝ), -Real.log ε] := hp D r (-Real.log ε) hs
  · -- values, smoothness and jet bounds
    intro φ hφ
    obtain ⟨κ, _, hφκ⟩ :=
      Finset.mem_biUnion.mp (show φ ∈ Cdex.attach.biUnion Φf from hφ)
    rw [hunfold κ] at hφκ
    by_cases h : κ.val ⊆ X ∩ openCube n
    · rw [dite_eq_left h] at hφκ
      exact (Classical.choose_spec (cellFam κ.val κ.property h)).2.1 φ hφκ
    · rw [dite_eq_right h] at hφκ
      exact absurd hφκ (Finset.notMem_empty φ)
  · -- the `ε`-cover of `X ∩ openCube n`
    intro x hx hxo
    obtain ⟨κ, hκC, hxκ⟩ := hcover x
    have hκsub : κ ⊆ X ∩ openCube n := by
      rcases hsep (0 : Fin 1) κ hκC with hh | hd
      · exact hh
      · exact (Set.disjoint_left.mp hd hxκ ⟨hx, hxo⟩).elim
    obtain ⟨φ, hφ, t, ht, hdist⟩ :=
      (Classical.choose_spec (cellFam κ hκC hκsub)).2.2 x hxκ hxo
    refine ⟨φ, ?_, t, ht, hdist⟩
    show φ ∈ Cdex.attach.biUnion Φf
    refine Finset.mem_biUnion.mpr ⟨⟨κ, hκC⟩, ?_, ?_⟩
    · simp
    · rw [hunfold ⟨κ, hκC⟩, dite_eq_left hκsub]
      exact hφ

end Work.WilG5.Interior
