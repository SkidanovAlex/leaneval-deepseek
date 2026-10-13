/-
  WilE9 / Sharp — the input assembly of the sharp-derivative construction (BNZ §3).

  The target `Work.WilE9.Sharp.layer_strata` turns a `Gen`-presentation of the graph of a
  function `f` into

  * a `*`-set `Z` with `graphOf f = psiV ⁻¹' Z` (`hE8`, the `Gen → StarR` reduction of area E8),
  * a finite list `S` of *effectively smooth strata* (`AEStratum n`, the strata of
    `Work.WilE9G.EffStratAE`) whose components `A.comp` project into `Z` and cover `Z` over the
    base points outside a null set `N` (the almost-everywhere covering form of the corrected
    geometric input),

  with the numerical bounds `|S| ≤ b₁ D`, `A.E.deg ≤ b₁ D`, `A.E.X.fmt ≤ a₁` and
  `A.E.X.basics.length ≤ b₁ D + 1` depending only on the format bound `F` and the ambient
  dimension `n`.

  The argument is:

  1. `hE8` gives `Z` (a `*`-set of `*`-degree `≤ p D`, `p.eval 0 = 0`) with
     `graphOf f = psiV ⁻¹' Z`; `hstar` decomposes `Z` into `*`-pieces
     `P : StarPiece (n+1)` with `#pieces ≤ p D + 1`, formats `≤ a` and total degree `≤ p D`.
  2. Each piece is reindexed to the `(n, 1+m)` shape (`pcX`, `pcP`, `LayerDefs`), where
     `stratProj '' connectedComponentIn (pcX P).set (pcP P) = StarPiece.set P`.
  3. The corrected geometric input `EffStratAE` is applied to that reindexed piece at the
     transported base point; its covering conclusion is exactly what the layer needs, and its
     fibre-finiteness hypothesis is discharged here: off the null set, the fibre of a `*`-piece
     over a base point of the open cube has at most three points (`finite_fiber_of_cube`), because
     the piece lies in the closed cube and meets the open cube inside the ψ-graph of `f`.
  4. The bounds add up because each piece contributes at most `b (p D)` strata of degree
     `≤ b (p D)` and there are at most `p D + 1` pieces, so the polynomial
     `b₁ := (p + 1) * (b.comp p) + 1` dominates `(p D + 1) * b (p D)`.

  The numerical bookkeeping `Layer.lengthBound` and the coordinate reindexing API of `LayerDefs`
  are the shared library pieces this file is built on.
-/
import Mathlib
import Submission.Work.WilE9.Sharp.Vocab
import Submission.Work.WilE9.Sharp.LayerDefs
import Submission.Work.WilE9.Sharp.Main
import Submission.Work.WilE9.Sharp.Layer.lengthBound
import Submission.Work.WilE9.Sharp.AE.finite_fiber_of_cube
import Submission.Work.WilE9G.Defs
import Submission.Work.WilE9.Psi.psiInv_psi
import Submission.Work.WilE9.Psi.psi_psiInv
import Submission.Work.WilE9.Ift.OneShot.poly_eval_le

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Classical Topology
namespace Work.WilE9.Sharp
open WilkiesDesign WilkiesDesign.E
open Work.WilE9.Ift.OneShot

/-! ## Null sets of a finite list of pieces -/

/-- A finite union (indexed by a list) of null sets is null. -/
theorem volume_iUnion_list {n : ℕ} {α : Type*} (L : List α) (Nf : α → Set (Fin n → ℝ))
    (h : ∀ a ∈ L, MeasureTheory.volume (Nf a) = 0) :
    MeasureTheory.volume (⋃ a ∈ L, Nf a) = 0 := by
  induction L with
  | nil =>
    have hset : (⋃ a ∈ ([] : List α), Nf a) = (∅ : Set (Fin n → ℝ)) := by
      ext x
      simp
    rw [hset, MeasureTheory.measure_empty]
  | cons a t ih =>
    have hsub : (⋃ b ∈ (a :: t), Nf b) ⊆ Nf a ∪ (⋃ b ∈ t, Nf b) := by
      intro x hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨b, hx⟩ := hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨hb, hx⟩ := hx
      rcases List.mem_cons.mp hb with rfl | hb
      · exact Or.inl hx
      · exact Or.inr (Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨hb, hx⟩⟩)
    refine MeasureTheory.measure_mono_null hsub ?_
    refine MeasureTheory.measure_union_null (h a (by simp)) (ih ?_)
    intro b hb
    exact h b (List.mem_cons_of_mem _ hb)

/-! ## Every `*`-piece lies in the closed cube -/

/-- Every `*`-piece of `ℝ^{n+1}` is contained in the closed cube. -/
theorem layer_starPiece_set_subset_cube {n : ℕ} (P : StarPiece (n + 1)) :
    StarPiece.set P ⊆ cubeC (n + 1) := by
  rintro y ⟨z, hz, rfl⟩ i
  exact (connectedComponentIn_subset P.X.set P.p hz).1 (Fin.castAdd P.m i)

/-! ## The assembly -/

theorem layer_strata
    (hE8 : ∀ F n : ℕ, ∃ (a : ℕ) (p : Polynomial ℕ), p.eval 0 = 0 ∧
      ∀ (D : ℕ) (X : Set (Fin n → ℝ)), WilkiesDesign.E.Gen F D n X →
        WilkiesDesign.E.StarR a (p.eval D) n X)
    (hstar : ∀ {F D n : ℕ} {Y : Set (Fin n → ℝ)}, WilkiesDesign.E.Star F D n Y →
      ∃ L : List (WilkiesDesign.E.StarPiece n),
        Y = (⋃ P ∈ L, WilkiesDesign.E.StarPiece.set P) ∧ L.length ≤ D + 1 ∧
          (∀ P ∈ L, P.X.fmt ≤ F) ∧ (L.map fun P => P.X.deg).sum ≤ D)
    (hEff : Work.WilE9G.EffStratAE) :
    ∀ F n : ℕ, ∃ (a₁ : ℕ) (b₁ : Polynomial ℕ),
      ∀ (D : ℕ) (f : (Fin n → ℝ) → ℝ),
        WilkiesDesign.E.Gen F D (n + 1) (WilkiesDesign.graphOf f) →
        ∃ (Z : Set (Fin (n + 1) → ℝ)) (S : List (AEStratum n)),
          WilkiesDesign.graphOf f = WilkiesDesign.E.psiV ⁻¹' Z ∧
          S.length ≤ b₁.eval D ∧
          (∀ A ∈ S, A.E.X.fmt ≤ a₁ ∧ A.E.deg ≤ b₁.eval D ∧
            A.E.X.basics.length ≤ b₁.eval D + 1 ∧ A.E.Good ∧ A.q ∈ A.E.X.set ∧
            (∀ w ∈ A.comp, stratProj w ∈ Z)) ∧
          ∃ N : Set (Fin n → ℝ), MeasureTheory.volume N = 0 ∧
            ∀ y ∈ Z, Fin.init y ∉ N → (∀ j : Fin n, |Fin.init y j| < 1) →
              y ∈ ⋃ A ∈ S, stratProj '' A.comp := by
  intro F n
  obtain ⟨a, p, hp0, hE8a⟩ := hE8 F (n + 1)
  obtain ⟨aH, bH, hEffH⟩ := hEff a
  refine ⟨aH, (p + 1) * (bH.comp p) + 1, ?_⟩
  intro D f hGen
  obtain ⟨Z, hStarZ, hZeq⟩ := hE8a D (graphOf f) hGen
  obtain ⟨L, hZdecomp, hLlen, hLfmt, hLdeg⟩ := hstar hStarZ
  -- every piece of the decomposition lies in `Z`
  have hZsub : ∀ P ∈ L, StarPiece.set P ⊆ Z := by
    intro P hP x hx
    rw [hZdecomp]
    exact Set.mem_iUnion₂.mpr ⟨P, hP, hx⟩
  -- the stratum list and the null set attached to one `*`-piece
  let g : StarPiece (n + 1) → List (AEStratum n) := fun P =>
    if h : P.X.fmt ≤ a ∧ P.p ∈ P.X.set then
      (hEffH n P.m (pcX P) (pcP P) (pcX_fmt_le P h.1) (pcP_mem P h.2)).choose
    else []
  let Nf : StarPiece (n + 1) → Set (Fin n → ℝ) := fun P =>
    if h : P.X.fmt ≤ a ∧ P.p ∈ P.X.set then
      (hEffH n P.m (pcX P) (pcP P) (pcX_fmt_le P h.1) (pcP_mem P h.2)).choose_spec.2.2.choose
    else ∅
  have hg : ∀ (P : StarPiece (n + 1)) (h : P.X.fmt ≤ a ∧ P.p ∈ P.X.set),
      g P = (hEffH n P.m (pcX P) (pcP P) (pcX_fmt_le P h.1) (pcP_mem P h.2)).choose := by
    intro P h
    simp only [g]
    rw [dif_pos h]
  have hNf : ∀ (P : StarPiece (n + 1)) (h : P.X.fmt ≤ a ∧ P.p ∈ P.X.set),
      Nf P =
        (hEffH n P.m (pcX P) (pcP P) (pcX_fmt_le P h.1)
          (pcP_mem P h.2)).choose_spec.2.2.choose := by
    intro P h
    simp only [Nf]
    rw [dif_pos h]
  -- the specification of one `*`-piece
  have hgspec : ∀ (P : StarPiece (n + 1)), StarPiece.set P ⊆ Z →
      ∀ (h : P.X.fmt ≤ a ∧ P.p ∈ P.X.set),
      (g P).length ≤ bH.eval P.X.deg ∧
      (∀ A ∈ g P, A.E.X.fmt ≤ aH ∧ A.E.deg ≤ bH.eval P.X.deg ∧
        A.E.X.basics.length ≤ bH.eval P.X.deg ∧ A.E.Good ∧ A.q ∈ A.E.X.set ∧
        (∀ w ∈ A.comp, stratProj w ∈ StarPiece.set P)) ∧
      MeasureTheory.volume (Nf P) = 0 ∧
      (∀ y ∈ StarPiece.set P, Fin.init y ∉ Nf P → (∀ j : Fin n, |Fin.init y j| < 1) →
        y ∈ ⋃ A ∈ g P, stratProj '' A.comp) := by
    intro P hZP h
    have key := (hEffH n P.m (pcX P) (pcP P) (pcX_fmt_le P h.1) (pcP_mem P h.2)).choose_spec
    rw [hg P h, hNf P h]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [pcX_deg P] using key.1
    · intro A hA
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := key.2.1 A hA
      refine ⟨h1, ?_, ?_, h4, h5, ?_⟩
      · have h2' : A.2.1.deg ≤ bH.eval (pcX P).deg := h2
        rw [pcX_deg P] at h2'
        exact h2'
      · have h3' : A.2.1.X.basics.length ≤ bH.eval (pcX P).deg := h3
        rw [pcX_deg P] at h3'
        exact h3'
      · intro w hw
        have hw' := h6 w hw
        rwa [stratProj_image_component P] at hw'
    · exact key.2.2.choose_spec.1
    · intro y hy hyN hyoc
      refine key.2.2.choose_spec.2 y ?_ hyN ?_
      · rw [stratProj_image_component P]
        exact hy
      · rw [stratProj_image_component P]
        exact Work.WilE9.Sharp.AE.finite_fiber_of_cube hZeq hZP
          (layer_starPiece_set_subset_cube P) hyoc
  -- the length bound and null set of one piece
  have hg_len : ∀ P ∈ L, (g P).length ≤ bH.eval P.X.deg := by
    intro P hP
    by_cases hmem : P.p ∈ P.X.set
    · exact (hgspec P (hZsub P hP) ⟨hLfmt P hP, hmem⟩).1
    · have hnil : g P = [] := by
        simp only [g]
        rw [dif_neg]
        intro hc; exact hmem hc.2
      rw [hnil]
      exact Nat.zero_le _
  have hNfvol : ∀ P ∈ L, MeasureTheory.volume (Nf P) = 0 := by
    intro P hP
    by_cases hmem : P.p ∈ P.X.set
    · exact (hgspec P (hZsub P hP) ⟨hLfmt P hP, hmem⟩).2.2.1
    · have hnil : Nf P = ∅ := by
        simp only [Nf]
        rw [dif_neg]
        intro hc; exact hmem hc.2
      rw [hnil, MeasureTheory.measure_empty]
  -- the degree bound of a single piece
  have hD' : ∀ P ∈ L, P.X.deg ≤ p.eval D := by
    intro P hP
    have h1 : P.X.deg ≤ (L.map fun Q => Q.X.deg).sum :=
      List.le_sum_of_mem (List.mem_map_of_mem hP)
    omega
  -- the numerical evaluation of the chosen polynomial bound
  have hb1 : (((p + 1) * (bH.comp p) + 1)).eval D
      = (p.eval D + 1) * bH.eval (p.eval D) + 1 := by
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one, Polynomial.eval_add,
      Polynomial.eval_one, Polynomial.eval_comp]
  have hB : bH.eval (p.eval D) ≤ (((p + 1) * (bH.comp p) + 1)).eval D := by
    rw [hb1]
    exact le_trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)) (Nat.le_succ _)
  set Ntot : Set (Fin n → ℝ) := ⋃ P ∈ L, Nf P with hNtot
  have hNtot_sub : ∀ P ∈ L, Nf P ⊆ Ntot := by
    intro P hP x hx
    rw [hNtot]
    exact Set.mem_iUnion₂.mpr ⟨P, hP, hx⟩
  refine ⟨Z, L.flatMap g, hZeq, ?_, ?_, Ntot, ?_, ?_⟩
  · -- length bound
    have h1 : (L.flatMap g).length ≤ (p.eval D + 1) * bH.eval (p.eval D) :=
      Layer.lengthBound L g bH (p.eval D) hLlen
        (fun P hP => (hg_len P hP).trans (poly_eval_le (hD' P hP)))
    rw [hb1]
    exact h1.trans (Nat.le_succ _)
  · -- the numerical bounds on the strata
    intro A hA
    obtain ⟨P, hP, hAP⟩ := List.mem_flatMap.mp hA
    have hmem : P.p ∈ P.X.set := by
      by_contra hc
      have hnil : g P = [] := by
        simp only [g]
        rw [dif_neg]
        intro hconj; exact hc hconj.2
      rw [hnil] at hAP
      exact List.not_mem_nil hAP
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
      (hgspec P (hZsub P hP) ⟨hLfmt P hP, hmem⟩).2.1 A hAP
    refine ⟨h1, ?_, ?_, h4, h5, ?_⟩
    · exact h2.trans ((poly_eval_le (hD' P hP)).trans hB)
    · exact (h3.trans ((poly_eval_le (hD' P hP)).trans hB)).trans (le_add_right le_rfl)
    · intro w hw
      exact hZsub P hP (h6 w hw)
  · -- the null set is null
    exact volume_iUnion_list L Nf hNfvol
  · -- the covering
    intro y hyZ hyN hyoc
    rw [hZdecomp, Set.mem_iUnion] at hyZ
    obtain ⟨P, hyZ⟩ := hyZ
    rw [Set.mem_iUnion] at hyZ
    obtain ⟨hP, hyP⟩ := hyZ
    have hmem : P.p ∈ P.X.set := by
      by_contra hc
      rw [starPiece_set_eq_empty P hc] at hyP
      exact hyP
    have hspec := hgspec P (hZsub P hP) ⟨hLfmt P hP, hmem⟩
    have hyNf : Fin.init y ∉ Nf P := fun hc => hyN (hNtot_sub P hP hc)
    have hcovP := hspec.2.2.2 y hyP hyNf hyoc
    rw [Set.mem_iUnion] at hcovP
    obtain ⟨A, hcovP⟩ := hcovP
    rw [Set.mem_iUnion] at hcovP
    obtain ⟨hAP, hyA⟩ := hcovP
    exact Set.mem_iUnion.mpr ⟨A, Set.mem_iUnion.mpr
      ⟨List.mem_flatMap.mpr ⟨P, hP, hAP⟩, hyA⟩⟩

end Work.WilE9.Sharp
