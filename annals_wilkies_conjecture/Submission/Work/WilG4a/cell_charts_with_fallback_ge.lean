import Mathlib
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG4a.Cells
import Submission.Work.WilG4a.f1affine1_defs
import Submission.Work.WilG4a.goodCell_affine_charts
import Submission.Work.WilG4a.goodCell_chart_conditions
import Submission.Work.WilG4a.sInf_sSup_fibre_graph_mem
import Submission.Work.WilG4a.ite_graph_mem
import Submission.Work.WilG4a.affine_cover_params
import Submission.Work.WilG4a.fibre_eq_Ioo_of_nonSubsingleton
import Submission.Work.WilG4a.lt_locus_graph_mem

namespace Work.WilG4a

/-- A subsingleton subset of `ℝ` (possibly empty) has equal infimum and supremum. -/
theorem cfb_subsingleton_sInf_eq_sSup_y {s : Set ℝ} (h : s.Subsingleton) : sInf s = sSup s := by
  rcases h.eq_empty_or_singleton with h0 | ⟨x, hx⟩
  · rw [h0, Real.sInf_empty, Real.sSup_empty]
  · rw [hx, csInf_singleton, csSup_singleton]

/-- **Fibre dichotomy for a good cell.**  The fibre of a good cell `κ` over a parameter `l` is
either a subsingleton (with `sInf = sSup`) or the open interval spanned by its own infimum and
supremum, of positive length and lying inside `I = (0,1)`. -/
theorem cfb_fibre_dichotomy_y {p k r : ℕ} {F : Fin k → (Fin p → ℝ) → ℝ → ℝ}
    {κ : Set (Fin (p + 1) → ℝ)} (hcell : GoodCell_w k r F κ) (l : Fin p → ℝ) :
    (fibre κ l).Subsingleton ∧ sInf (fibre κ l) = sSup (fibre κ l) ∨
      (fibre κ l = Set.Ioo (sInf (fibre κ l)) (sSup (fibre κ l)) ∧
        sInf (fibre κ l) < sSup (fibre κ l) ∧
        0 ≤ sInf (fibre κ l) ∧ sSup (fibre κ l) ≤ 1) := by
  obtain ⟨hstrip, hdich, -⟩ := hcell
  rcases hdich l with hsub | ⟨a, b, hfib⟩
  · exact Or.inl ⟨hsub, cfb_subsingleton_sInf_eq_sSup_y hsub⟩
  · rcases Set.eq_empty_or_nonempty (fibre κ l) with hempty | ⟨y, hy⟩
    · have hsub' : (fibre κ l).Subsingleton := by
        rw [hempty]; exact Set.subsingleton_empty
      exact Or.inl ⟨hsub', cfb_subsingleton_sInf_eq_sSup_y hsub'⟩
    · have hy' : y ∈ Set.Ioo a b := by rw [← hfib]; exact hy
      have hlt : a < b := hy'.1.trans hy'.2
      have hsInf : sInf (fibre κ l) = a := by rw [hfib]; exact csInf_Ioo hlt
      have hsSup : sSup (fibre κ l) = b := by rw [hfib]; exact csSup_Ioo hlt
      have hsubI : Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) 1 := by
        intro z hz
        have hzmem : z ∈ fibre κ l := by rw [hfib]; exact hz
        have hzI : z ∈ I := by simpa using hstrip hzmem
        simpa [I] using hzI
      obtain ⟨h0a, hb1⟩ := bounds_of_Ioo_subset_Ioo hsubI hlt
      exact Or.inr ⟨by rw [hsInf, hsSup]; exact hfib, by rw [hsInf, hsSup]; exact hlt,
        by rw [hsInf]; exact h0a, by rw [hsSup]; exact hb1⟩

theorem cell_charts_with_fallback_ge (S : WilkiesDesign.SOMin) (hG3a : ∀ (r : ℕ) (f : ℝ → ℝ), ContDiffOn ℝ (r + 1) f (Set.Ioo 0 1) → (∀ x ∈ Set.Ioo (0 : ℝ) 1, f x ∈ Set.Ioo (0 : ℝ) 1) → (∀ j ≤ r + 1, (∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ iteratedDerivWithin j f (Set.Ioo 0 1) x) ∨ (∀ x ∈ Set.Ioo (0 : ℝ) 1, iteratedDerivWithin j f (Set.Ioo 0 1) x ≤ 0)) → ∀ M : ℝ, 1 < M → ∀ j ≤ r, ∀ x ∈ Set.Ioo (0 : ℝ) 1, (j : ℝ) / M < x → x < 1 - j / M → |iteratedDerivWithin j f (Set.Ioo 0 1) x| < M ^ j) (hG3b : ∀ (r : ℕ) (ε : ℝ), 0 < ε → ε < 1 → ∃ s : Finset (ℝ × ℝ), (s.card : ℝ) ≤ 8 * (r + 1) * (-Real.log ε + 2) ∧ (∀ p ∈ s, 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < 1 ∧ (p.2 - p.1) * (r + 1) ≤ min p.1 (1 - p.2)) ∧ (Set.Icc ε (1 - ε) ⊆ (⋃ p ∈ s, Set.Icc p.1 p.2))) (p : ℕ) (F0 Fκ : ℕ) (bκ : MvPolynomial (Fin 2) ℕ) : ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : MvPolynomial (Fin 4) ℝ), ∀ (D r k : ℕ) (ε : ℝ), 0 < ε → ε < 1 → ∀ (Λ : Set (Fin p → ℝ)) (F : Fin k → (Fin p → ℝ) → ℝ → ℝ) (κ : Set (Fin (p + 1) → ℝ)) (α₀ β₀ : (Fin p → ℝ) → ℝ), (∀ i, Work.WilG4a.graphFam (F i) ∈ S.Ω F0 D (p + 1 + 1)) → (∀ i, ∀ l ∈ Λ, ∀ x ∈ Work.WilG4a.I, F i l x ∈ Work.WilG4a.I) → Work.WilG4a.GoodCell_w k r F κ → κ ∈ S.Ω Fκ (MvPolynomial.eval ![D, r] bκ) (p + 1) → WilkiesDesign.graphOf α₀ ∈ S.Ω Fκ (MvPolynomial.eval ![D, r] bκ) (p + 1) → WilkiesDesign.graphOf β₀ ∈ S.Ω Fκ (MvPolynomial.eval ![D, r] bκ) (p + 1) → (∀ l ∈ Λ, 0 ≤ β₀ l ∧ 0 ≤ α₀ l ∧ α₀ l + β₀ l ≤ 1 ∧ ∀ i, ContDiffOn ℝ r (fun t : ℝ => F i l (α₀ l + β₀ l * t)) Work.WilG4a.I ∧ ∀ m ≤ r, ∀ t ∈ Work.WilG4a.I, |iteratedDeriv m (fun t : ℝ => F i l (α₀ l + β₀ l * t)) t| ≤ 1) → ∃ Φ : Finset (((Fin p → ℝ) → ℝ) × ((Fin p → ℝ) → ℝ)), (Φ.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c ∧ (∀ αβ ∈ Φ, WilkiesDesign.graphOf αβ.1 ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (p + 1) ∧ WilkiesDesign.graphOf αβ.2 ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (p + 1) ∧ (∀ l ∈ Λ, 0 ≤ αβ.2 l ∧ 0 ≤ αβ.1 l ∧ αβ.1 l + αβ.2 l ≤ 1 ∧ ∀ i, ContDiffOn ℝ r (fun t : ℝ => F i l (αβ.1 l + αβ.2 l * t)) Work.WilG4a.I ∧ ∀ m ≤ r, ∀ t ∈ Work.WilG4a.I, |iteratedDeriv m (fun t : ℝ => F i l (αβ.1 l + αβ.2 l * t)) t| ≤ 1)) ∧ (∀ l ∈ Λ, ¬ (Work.WilG4a.fibre κ l).Subsingleton → ∀ x ∈ Work.WilG4a.fibre κ l, ∃ αβ ∈ Φ, 0 < αβ.2 l ∧ ∃ t ∈ Work.WilG4a.I, |αβ.1 l + αβ.2 l * t - x| < ε) := by
  classical
  -- ============================================================================
  -- Choice of the format/degree data, depending only on `S, p, F0, Fκ, bκ`.
  -- ============================================================================
  -- The fibre end points of a cell of format `Fκ` and degree `bκ` are `Ω`-definable with
  -- format `aE` and degree affine in `bκ`.
  obtain ⟨aE, cE, dE, hE⟩ := sInf_sSup_fibre_graph_mem S p Fκ
  -- The ambient format/degree at which the cell `κ` and its fibre end points are both
  -- presented.  `bq` dominates both `bκ` and `cE * bκ + dE`.
  set Fq : ℕ := Fκ + aE with hFq
  set bq : MvPolynomial (Fin 2) ℕ :=
    bκ + (MvPolynomial.C cE * bκ + MvPolynomial.C dE) with hbq
  -- The affine charts of a good cell (on its non-degeneracy locus).
  obtain ⟨aG, bG, cG, hG⟩ := goodCell_affine_charts S hG3a hG3b p F0 Fq bq
  -- The non-degeneracy locus `{l | sInf (fibre κ l) < sSup (fibre κ l)}`.
  obtain ⟨aP, bP, hP⟩ := lt_locus_graph_mem S p Fq
  -- Re-express the degree of the non-degeneracy locus directly in `D` (composition of the
  -- degree polynomial of the input with `bq`).
  set bPc : MvPolynomial (Fin 2) ℕ :=
    MvPolynomial.aeval ![bq, MvPolynomial.X 1] bP with hbPc
  -- The common format and degree at which the case-split gluing is performed.
  set a0 : ℕ := Fq + aG + aP + 4 with ha0
  set bcom : MvPolynomial (Fin 2) ℕ := bq + bG + bPc with hbcom
  -- The gluing (`if-then-else`) operation on graphs.
  obtain ⟨aGl, bGl, hGl⟩ := ite_graph_mem S p a0
  refine ⟨aGl, MvPolynomial.aeval ![bcom, MvPolynomial.X 1] bGl, cG, ?_⟩
  intro D r k ε hε hε1 Λ F κ α₀ β₀ hFΩ hFI hcell hκΩ hα0Ω hβ0Ω hcond
  -- ============================================================================
  -- Evaluation of the degree polynomials.
  -- ============================================================================
  have hbq_eval : MvPolynomial.eval ![D, r] bq
      = MvPolynomial.eval ![D, r] bκ
        + (cE * MvPolynomial.eval ![D, r] bκ + dE) := by
    rw [hbq]
    simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  have hbq_ge : MvPolynomial.eval ![D, r] bκ ≤ MvPolynomial.eval ![D, r] bq := by
    rw [hbq_eval]; omega
  have hbq_ge_ends :
      cE * MvPolynomial.eval ![D, r] bκ + dE ≤ MvPolynomial.eval ![D, r] bq := by
    rw [hbq_eval]; omega
  -- ============================================================================
  -- The fibre end points `lo = sInf (fibre κ ·)` and `hi = sSup (fibre κ ·)`.
  -- ============================================================================
  set lo : (Fin p → ℝ) → ℝ := fun l => sInf (fibre κ l) with hlo
  set hi : (Fin p → ℝ) → ℝ := fun l => sSup (fibre κ l) with hhi
  have hstrip : ∀ z ∈ κ, z (Fin.last p) ∈ I := fun z hz => hcell.1 hz
  have hEapp := hE (MvPolynomial.eval ![D, r] bκ) κ hκΩ hstrip
  have hloE : WilkiesDesign.graphOf lo ∈
      S.Ω aE (cE * MvPolynomial.eval ![D, r] bκ + dE) (p + 1) := by
    rw [hlo]; simpa [fibre] using hEapp.1
  have hhiE : WilkiesDesign.graphOf hi ∈
      S.Ω aE (cE * MvPolynomial.eval ![D, r] bκ + dE) (p + 1) := by
    rw [hhi]; simpa [fibre] using hEapp.2
  -- Raise everything to the common format `Fq` and degree `eval bq`.
  have hlo_q : WilkiesDesign.graphOf lo ∈ S.Ω Fq (MvPolynomial.eval ![D, r] bq) (p + 1) :=
    Work.WilG5.mem_mono hloE Fq (MvPolynomial.eval ![D, r] bq)
      (by rw [hFq]; omega) hbq_ge_ends
  have hhi_q : WilkiesDesign.graphOf hi ∈ S.Ω Fq (MvPolynomial.eval ![D, r] bq) (p + 1) :=
    Work.WilG5.mem_mono hhiE Fq (MvPolynomial.eval ![D, r] bq)
      (by rw [hFq]; omega) hbq_ge_ends
  have hκ_q : κ ∈ S.Ω Fq (MvPolynomial.eval ![D, r] bq) (p + 1) :=
    Work.WilG5.mem_mono hκΩ Fq (MvPolynomial.eval ![D, r] bq)
      (by rw [hFq]; omega) hbq_ge
  have hα0_q : WilkiesDesign.graphOf α₀ ∈ S.Ω Fq (MvPolynomial.eval ![D, r] bq) (p + 1) :=
    Work.WilG5.mem_mono hα0Ω Fq (MvPolynomial.eval ![D, r] bq)
      (by rw [hFq]; omega) hbq_ge
  have hβ0_q : WilkiesDesign.graphOf β₀ ∈ S.Ω Fq (MvPolynomial.eval ![D, r] bq) (p + 1) :=
    Work.WilG5.mem_mono hβ0Ω Fq (MvPolynomial.eval ![D, r] bq)
      (by rw [hFq]; omega) hbq_ge
  -- ============================================================================
  -- `Ω`-membership of the non-degeneracy locus `{l | lo l < hi l}`.
  -- ============================================================================
  have hPm : {l : Fin p → ℝ | lo l < hi l} ∈
      S.Ω aP (MvPolynomial.eval ![MvPolynomial.eval ![D, r] bq, r] bP) p :=
    hP (MvPolynomial.eval ![D, r] bq) r hlo_q hhi_q
  have hbPc_eval : MvPolynomial.eval ![D, r] bPc
      = MvPolynomial.eval ![MvPolynomial.eval ![D, r] bq, r] bP := by
    rw [hbPc, Work.WilG4a.CD.eval_aeval_eq]
    have hfun : (fun i : Fin 2 => MvPolynomial.eval (![D, r] : Fin 2 → ℕ)
        ((![bq, MvPolynomial.X 1] : Fin 2 → MvPolynomial (Fin 2) ℕ) i))
        = (![MvPolynomial.eval ![D, r] bq, r] : Fin 2 → ℕ) := by
      funext i
      fin_cases i <;> simp
    rw [hfun]
  have hPm' : {l : Fin p → ℝ | lo l < hi l} ∈ S.Ω aP (MvPolynomial.eval ![D, r] bPc) p := by
    rw [hbPc_eval]; exact hPm
  have hP0 : {l : Fin p → ℝ | lo l < hi l} ∈ S.Ω a0 (MvPolynomial.eval ![D, r] bcom) p :=
    Work.WilG5.mem_mono hPm' a0 (MvPolynomial.eval ![D, r] bcom)
      (by rw [ha0]; omega)
      (by rw [hbcom]; simp only [MvPolynomial.eval_add]; omega)
  -- ============================================================================
  -- The dichotomies for the fibre of a good cell.
  -- ============================================================================
  have fib_of_lt : ∀ l : Fin p → ℝ, lo l < hi l →
      fibre κ l = Set.Ioo (lo l) (hi l) ∧ (fibre κ l).Nonempty := by
    intro l hlt
    rcases cfb_fibre_dichotomy_y hcell l with ⟨hsub, hss⟩ | ⟨h1, h2, h3, h4⟩
    · exfalso
      have hEq : lo l = hi l := by rw [hlo, hhi]; exact hss
      exact (ne_of_lt hlt) hEq
    · have h1' : fibre κ l = Set.Ioo (lo l) (hi l) := by rw [hlo, hhi]; exact h1
      have h2' : lo l < hi l := by rw [hlo, hhi]; exact h2
      exact ⟨h1', by rw [h1']; exact Set.nonempty_Ioo.mpr h2'⟩
  have fib_of_not_sub : ∀ l : Fin p → ℝ, ¬ (fibre κ l).Subsingleton →
      fibre κ l = Set.Ioo (lo l) (hi l) ∧ lo l < hi l := by
    intro l hns
    rcases cfb_fibre_dichotomy_y hcell l with ⟨hsub, hss⟩ | ⟨h1, h2, h3, h4⟩
    · exact absurd hsub hns
    · exact ⟨by rw [hlo, hhi]; exact h1, by rw [hlo, hhi]; exact h2⟩
  -- ============================================================================
  -- The cell charts, on the base `Λ' = Λ ∩ {lo < hi}`.
  -- ============================================================================
  set Λ' : Set (Fin p → ℝ) := {l | l ∈ Λ ∧ lo l < hi l} with hΛ'
  have hΛ'mem : ∀ l : Fin p → ℝ, l ∈ Λ' → l ∈ Λ ∧ lo l < hi l := by
    intro l hl
    rw [hΛ'] at hl
    exact hl
  have hFI' : ∀ i, ∀ l ∈ Λ', ∀ x ∈ I, F i l x ∈ I := by
    intro i l hl x hx
    exact hFI i l (hΛ'mem l hl).1 x hx
  have hΛ'fib : ∀ l ∈ Λ', fibre κ l = Set.Ioo (lo l) (hi l) := by
    intro l hl
    exact (fib_of_lt l (hΛ'mem l hl).2).1
  have hΛ'ne : ∀ l ∈ Λ', ∃ x : ℝ, Fin.snoc l x ∈ κ := by
    intro l hl
    obtain ⟨x, hx⟩ := (fib_of_lt l (hΛ'mem l hl).2).2
    exact ⟨x, hx⟩
  obtain ⟨Ψ, hΨcard, hΨcharts, hΨcov⟩ :=
    hG D r k ε hε hε1 Λ' F κ lo hi hFΩ hFI' hcell hκ_q hlo_q hhi_q hΛ'ne hΛ'fib
  -- ============================================================================
  -- The glued charts.
  -- ============================================================================
  set P : Set (Fin p → ℝ) := {l | lo l < hi l} with hPset
  have hPcom : P ∈ S.Ω a0 (MvPolynomial.eval ![D, r] bcom) p := by
    rw [hPset]; exact hP0
  have hdeg : ∀ (X : MvPolynomial (Fin 2) ℕ),
      MvPolynomial.eval ![MvPolynomial.eval ![D, r] bcom, r] X
        = MvPolynomial.eval ![D, r] (MvPolynomial.aeval ![bcom, MvPolynomial.X 1] X) := by
    intro X
    rw [Work.WilG4a.CD.eval_aeval_eq]
    have hfun : (fun i : Fin 2 => MvPolynomial.eval (![D, r] : Fin 2 → ℕ)
        ((![bcom, MvPolynomial.X 1] : Fin 2 → MvPolynomial (Fin 2) ℕ) i))
        = (![MvPolynomial.eval ![D, r] bcom, r] : Fin 2 → ℕ) := by
      funext i
      fin_cases i <;> simp
    rw [hfun]
  refine ⟨Ψ.image (fun uv : ((Fin p → ℝ) → ℝ) × ((Fin p → ℝ) → ℝ) =>
      (iteFun P uv.1 α₀, iteFun P uv.2 β₀)), ?_, ?_, ?_⟩
  · -- cardinality
    have h1 : ((Ψ.image (fun uv : ((Fin p → ℝ) → ℝ) × ((Fin p → ℝ) → ℝ) =>
        (iteFun P uv.1 α₀, iteFun P uv.2 β₀))).card : ℝ) ≤ (Ψ.card : ℝ) := by
      exact_mod_cast Finset.card_image_le
    exact le_trans h1 hΨcard
  · -- the two coefficient graphs of each chart, and the chart conditions on all of `Λ`
    intro αβ hαβ
    obtain ⟨uv, huv, rfl⟩ := Finset.mem_image.mp hαβ
    have hcellcom : WilkiesDesign.graphOf uv.1 ∈
        S.Ω a0 (MvPolynomial.eval ![D, r] bcom) (p + 1) :=
      Work.WilG5.mem_mono (hΨcharts uv huv).1 a0 (MvPolynomial.eval ![D, r] bcom)
        (by rw [ha0]; omega)
        (by rw [hbcom]; simp only [MvPolynomial.eval_add]; omega)
    have hfallcom : WilkiesDesign.graphOf α₀ ∈
        S.Ω a0 (MvPolynomial.eval ![D, r] bcom) (p + 1) :=
      Work.WilG5.mem_mono hα0_q a0 (MvPolynomial.eval ![D, r] bcom)
        (by rw [ha0]; omega)
        (by rw [hbcom]; simp only [MvPolynomial.eval_add]; omega)
    have hg1 := hGl (MvPolynomial.eval ![D, r] bcom) r hPcom hcellcom hfallcom
    have hcellcom2 : WilkiesDesign.graphOf uv.2 ∈
        S.Ω a0 (MvPolynomial.eval ![D, r] bcom) (p + 1) :=
      Work.WilG5.mem_mono (hΨcharts uv huv).2.1 a0 (MvPolynomial.eval ![D, r] bcom)
        (by rw [ha0]; omega)
        (by rw [hbcom]; simp only [MvPolynomial.eval_add]; omega)
    have hfallcom2 : WilkiesDesign.graphOf β₀ ∈
        S.Ω a0 (MvPolynomial.eval ![D, r] bcom) (p + 1) :=
      Work.WilG5.mem_mono hβ0_q a0 (MvPolynomial.eval ![D, r] bcom)
        (by rw [ha0]; omega)
        (by rw [hbcom]; simp only [MvPolynomial.eval_add]; omega)
    have hg2 := hGl (MvPolynomial.eval ![D, r] bcom) r hPcom hcellcom2 hfallcom2
    refine ⟨?_, ?_, ?_⟩
    · rw [← hdeg bGl]; exact hg1
    · rw [← hdeg bGl]; exact hg2
    · intro l hl
      by_cases hlP : l ∈ P
      · have hl' : l ∈ Λ' := by
          refine ⟨hl, ?_⟩
          simpa [hPset] using hlP
        have hc := (hΨcharts uv huv).2.2 l hl'
        simp only [iteFun, ite_eq_left hlP]
        exact ⟨le_of_lt hc.1, hc.2⟩
      · have hc := hcond l hl
        simpa only [iteFun, ite_eq_right hlP] using hc
  · -- the `ε`-covering of the fibres of `κ`
    intro l hl hns x hx
    obtain ⟨hfib, hlt⟩ := fib_of_not_sub l hns
    have hl' : l ∈ Λ' := ⟨hl, hlt⟩
    have hxIoo : x ∈ Set.Ioo (lo l) (hi l) := by rw [← hfib]; exact hx
    have hxI : x ∈ I := by
      have hxmem : x ∈ fibre κ l := by rw [hfib]; exact hxIoo
      simpa using hcell.1 hxmem
    have hd : 0 < hi l - lo l := sub_pos.mpr hlt
    set t : ℝ := (x - lo l) / (hi l - lo l) with ht
    have htI : t ∈ I := by
      rw [ht]
      constructor
      · exact div_pos (sub_pos.mpr hxIoo.1) hd
      · rw [div_lt_one hd]; linarith [hxIoo.2]
    have hxeq : x = lo l + (hi l - lo l) * t := by
      rw [ht, mul_div_cancel₀ _ (ne_of_gt hd)]
      ring
    obtain ⟨uv, huv, τ, hτ, hdist⟩ := hΨcov l hl' x hxI ⟨t, htI, hxeq⟩
    have hlP : l ∈ P := by simpa [hPset] using hlt
    have hβpos : 0 < uv.2 l := ((hΨcharts uv huv).2.2 l hl').1
    refine ⟨(iteFun P uv.1 α₀, iteFun P uv.2 β₀), ?_, ?_, τ, hτ, ?_⟩
    · exact Finset.mem_image.mpr ⟨uv, huv, rfl⟩
    · simpa only [iteFun, ite_eq_left hlP] using hβpos
    · simpa only [iteFun, ite_eq_left hlP] using hdist

end Work.WilG4a
