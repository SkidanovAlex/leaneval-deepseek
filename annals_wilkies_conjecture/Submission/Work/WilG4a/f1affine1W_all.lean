import Mathlib
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG4a.Cells
import Submission.Work.WilG4a.F1Affine1W
import Submission.Work.WilG4a.signConst_decomposition
import Submission.Work.WilG4a.fiber_endpoints
import Submission.Work.WilG4a.affine_comb_graph_mem
import Submission.Work.WilG4a.affine_reparam_bound
import Submission.Work.WilG4a.ite_graph_mem
import Submission.Work.WilG4a.ChartUnion
import Submission.Work.WilG4a.Bounds
import Submission.Work.WilG4a.f1affine1_of_parts_ge
import Submission.Work.WilG4a.trivial_fallback

set_option maxHeartbeats 1000000

namespace Work.WilG4a

open WilkiesConjecture WilkiesDesign

/-!
## The argument

The corrected (`β ≥ 0`) assembly `Work.WilG4a.f1affine1_ge_all` already produces, for every `p`,
a family `Φ` of charts with `0 ≤ β l`, `0 ≤ α l`, `α l + β l ≤ 1` whose *non-degenerate*
members (`0 < β l`) `ε`-cover `I` at every `l ∈ Λ`.  `F1Affine1W` demands one extra *per-chart*
condition, absent from the `_ge` statement: the image clause `∀ t ∈ I, α l + β l t ∈ I`.

That clause is manufactured from the `_ge` data with no reference to the construction: for a
chart `(α, β)` put `α' := if β l = 0 then 1/2 else α l`.

* At a parameter with `β l ≠ 0` (hence `β l > 0`, since `0 ≤ β l`) the image clause follows from
  `0 ≤ α l`, `α l + β l ≤ 1` and `t ∈ (0,1)`: `0 < α l + β l t < α l + β l ≤ 1`.
* At a parameter with `β l = 0` the chart is constant with value `1/2 ∈ I`, and the composite
  `t ↦ F i l (1/2)` is constant, so it is `C^r` with all derivatives of order `≥ 1` vanishing and
  the value `F i l (1/2) ∈ I` giving the `m = 0` bound.  This is exactly the device of
  `Work.WilG4a.trivial_fallback_chart`.

The modification is `Ω`-invisible in format/degree terms: `{l | β l = 0}` is the projection of
`graphOf β ∩ {z | z_last = 0}` (`zeroLocus_graph_mem`), and the case-split of two `Ω`-graphs is
`Ω` (`ite_graph_memD`), both with parameters depending only on `p, a, b`.  The `ε`-cover is
untouched, because every chart that participates in the cover has `β l > 0` at the parameter in
question, where `α' = α`.

Hence `F1AffineGe S p → F1Affine1W S p`, and composing with the proved `f1affine1_ge_all` gives
the target.
-/

/-! ## Elementary facts about `iteFun` -/

theorem iteFun_of_mem {α : Type*} {β : Sort*} (P : Set α) (f g : α → β) {l : α}
    (hl : l ∈ P) : iteFun P f g l = f l := by
  simp [iteFun, hl]

theorem iteFun_not_mem {α : Type*} {β : Sort*} (P : Set α) (f g : α → β) {l : α}
    (hl : l ∉ P) : iteFun P f g l = g l := by
  simp [iteFun, hl]

/-- The graph of a case-split function is `Ω`-definable with format `FC + 4` and degree
polynomial `C 4 * X 0`, whenever the case-set and both graphs are `Ω FC D` (this is
`Work.WilG4a.ite_graph_mem` with the format and degree written out explicitly). -/
theorem ite_graph_memD (S : WilkiesDesign.SOMin) (p FC : ℕ) :
    ∀ (D : ℕ) {P : Set (Fin p → ℝ)} {f g : (Fin p → ℝ) → ℝ},
      P ∈ S.Ω FC D p → graphOf f ∈ S.Ω FC D (p + 1) → graphOf g ∈ S.Ω FC D (p + 1) →
        graphOf (iteFun P f g) ∈ S.Ω (FC + 4) (4 * D) (p + 1) := by
  intro D P f g hP hf hg
  have hproj : {z : Fin (p + 1) → ℝ | Fin.init z ∈ P} ∈ S.Ω (FC + 1) D (p + 1) :=
    S.prod_right hP
  have hprojC : ({z : Fin (p + 1) → ℝ | Fin.init z ∈ P})ᶜ ∈ S.Ω (FC + 2) D (p + 1) :=
    Work.WilG5.mem_mono (S.compl hproj) (FC + 2) D (by omega) (le_refl D)
  have hf1 : graphOf f ∈ S.Ω (FC + 1) D (p + 1) :=
    Work.WilG5.mem_mono hf (FC + 1) D (by omega) (le_refl D)
  have hg2 : graphOf g ∈ S.Ω (FC + 2) D (p + 1) :=
    Work.WilG5.mem_mono hg (FC + 2) D (by omega) (le_refl D)
  have hA : graphOf f ∩ {z : Fin (p + 1) → ℝ | Fin.init z ∈ P} ∈
      S.Ω (FC + 4) (D + D) (p + 1) :=
    Work.WilG5.mem_mono (inter_mem_ite hf1 hproj) (FC + 4) (D + D) (by omega) (le_refl _)
  have hB : graphOf g ∩ ({z : Fin (p + 1) → ℝ | Fin.init z ∈ P})ᶜ ∈
      S.Ω (FC + 4) (D + D) (p + 1) :=
    Work.WilG5.mem_mono (inter_mem_ite hg2 hprojC) (FC + 4) (D + D) (by omega) (le_refl _)
  have hU : (graphOf f ∩ {z : Fin (p + 1) → ℝ | Fin.init z ∈ P}) ∪
      (graphOf g ∩ ({z : Fin (p + 1) → ℝ | Fin.init z ∈ P})ᶜ) ∈
      S.Ω (FC + 4) ((D + D) + (D + D)) (p + 1) := union_mem hA hB
  rw [← graphOf_iteFun_eq] at hU
  have hdeg : (D + D) + (D + D) = 4 * D := by omega
  rw [hdeg] at hU
  exact hU

/-- The zero locus `{l | β l = 0}` of an `Ω`-graph is `Ω`-definable: it is the projection
(`SOMin.proj`) of the intersection of `graphOf β` with the hyperplane `z_last = 0`
(`Work.WilG4a.graphOf_const_mem`).  Format `max a (p+1) + 2`, degree `D + 1`. -/
theorem zeroLocus_graph_mem (S : WilkiesDesign.SOMin) (p a : ℕ) :
    ∀ (D : ℕ) {β : (Fin p → ℝ) → ℝ},
      graphOf β ∈ S.Ω a D (p + 1) →
      {l : Fin p → ℝ | β l = 0} ∈ S.Ω (max a (p + 1) + 2) (D + 1) p := by
  intro D β hβ
  have hzero : graphOf (fun _ : Fin p → ℝ => (0 : ℝ)) ∈ S.Ω (p + 1) 1 (p + 1) :=
    graphOf_const_mem S p 0
  have hβ' : graphOf β ∈ S.Ω (max a (p + 1)) D (p + 1) :=
    mono_F_le S hβ (le_max_left _ _)
  have hz' : graphOf (fun _ : Fin p → ℝ => (0 : ℝ)) ∈ S.Ω (max a (p + 1)) 1 (p + 1) :=
    mono_F_le S hzero (le_max_right _ _)
  have hinter : graphOf β ∩ graphOf (fun _ : Fin p → ℝ => (0 : ℝ)) ∈
      S.Ω (max a (p + 1) + 1) (D + 1) (p + 1) := inter_mem_ite hβ' hz'
  have hproj := S.proj hinter
  have hset : WilkiesDesign.projLast (graphOf β ∩
      graphOf (fun _ : Fin p → ℝ => (0 : ℝ))) = {l : Fin p → ℝ | β l = 0} := by
    ext l
    constructor
    · rintro ⟨t, ht⟩
      rw [Set.mem_inter_iff] at ht
      have h1 : t = β l := by
        simpa [WilkiesDesign.graphOf] using ht.1
      have h2 : t = 0 := by
        simpa [WilkiesDesign.graphOf] using ht.2
      simp only [Set.mem_ofPred_eq]
      rw [← h1, h2]
    · intro hl
      refine ⟨0, ?_⟩
      simp only [Set.mem_inter_iff, WilkiesDesign.graphOf, Set.mem_ofPred_eq]
      exact ⟨by simpa using hl.symm, by norm_num⟩
  rw [hset] at hproj
  exact hproj

/-- **`F1Affine1W` from `F1AffineGe`.**  The extra per-chart image condition of `F1Affine1W`
is forced by replacing `α` by `α' = if β l = 0 then 1/2 else α l`; the cover is unaffected
because the covering charts have `β l > 0` at the parameter at which they cover. -/
theorem f1affineW_of_f1affineGe (S : WilkiesDesign.SOMin) (p : ℕ)
    (h : Work.WilG4a.F1AffineGe S p) : Work.WilG4a.F1Affine1W S p := by
  classical
  intro F0
  obtain ⟨a, b, c, hc⟩ := h F0
  refine ⟨(max a (p + 1) + 2) + 4,
    b + MvPolynomial.C 4 * (b + MvPolynomial.C 1), c, ?_⟩
  intro D r k ε hε hε1 Λ F hFΩ hFI
  obtain ⟨Φ, hcard, hcharts, hcov⟩ := hc D r k ε hε hε1 Λ F hFΩ hFI
  refine ⟨Φ.image (fun αβ : ((Fin p → ℝ) → ℝ) × ((Fin p → ℝ) → ℝ) =>
      (iteFun {l : Fin p → ℝ | αβ.2 l = 0} (fun _ : Fin p → ℝ => (1 / 2 : ℝ)) αβ.1, αβ.2)),
    ?_, ?_, ?_⟩
  · -- cardinality: an image of a finset has no more elements
    have h1 : ((Φ.image (fun αβ : ((Fin p → ℝ) → ℝ) × ((Fin p → ℝ) → ℝ) =>
        (iteFun {l : Fin p → ℝ | αβ.2 l = 0} (fun _ : Fin p → ℝ => (1 / 2 : ℝ)) αβ.1,
          αβ.2))).card : ℝ) ≤ (Φ.card : ℝ) := by
      exact_mod_cast Finset.card_image_le
    exact le_trans h1 hcard
  · -- the per-chart conditions, with the image clause forced
    rintro ⟨α, β⟩ hmem
    obtain ⟨αβ, hαβ, hEq⟩ := Finset.mem_image.mp hmem
    simp only [Prod.mk.injEq] at hEq
    obtain ⟨hEq1, hEq2⟩ := hEq
    rw [← hEq1, ← hEq2]
    dsimp only
    have hchart := hcharts αβ hαβ
    rw [Chart1Ge] at hchart
    obtain ⟨hαΩ, hβΩ, hpt⟩ := hchart
    set α' : (Fin p → ℝ) → ℝ :=
      iteFun {l : Fin p → ℝ | αβ.2 l = 0} (fun _ : Fin p → ℝ => (1 / 2 : ℝ)) αβ.1 with hα'def
    have hα'val : ∀ l : Fin p → ℝ, αβ.2 l = 0 → α' l = 1 / 2 := by
      intro l hl
      rw [hα'def]
      exact iteFun_of_mem _ _ _ (by simpa using hl)
    have hα'val' : ∀ l : Fin p → ℝ, αβ.2 l ≠ 0 → α' l = αβ.1 l := by
      intro l hl
      rw [hα'def]
      exact iteFun_not_mem _ _ _ (show l ∉ {l : Fin p → ℝ | αβ.2 l = 0} from by simpa using hl)
    -- the common format `max a (p+1) + 2` and the common degree `eval b + 1`
    have hZmem : {l : Fin p → ℝ | αβ.2 l = 0} ∈ S.Ω (max a (p + 1) + 2)
        (MvPolynomial.eval ![D, r] b + 1) p :=
      zeroLocus_graph_mem S p a (MvPolynomial.eval ![D, r] b) hβΩ
    have hαFC : graphOf αβ.1 ∈ S.Ω (max a (p + 1) + 2)
        (MvPolynomial.eval ![D, r] b + 1) (p + 1) :=
      mono_FD_le S hαΩ (by omega) (by omega)
    have hconstFC : graphOf (fun _ : Fin p → ℝ => (1 / 2 : ℝ)) ∈
        S.Ω (max a (p + 1) + 2) (MvPolynomial.eval ![D, r] b + 1) (p + 1) :=
      mono_FD_le S (graphOf_const_mem S p (1 / 2)) (by omega) (by omega)
    have hite := ite_graph_memD S p (max a (p + 1) + 2)
      (MvPolynomial.eval ![D, r] b + 1) hZmem hconstFC hαFC
    have hb' : MvPolynomial.eval ![D, r] (b + MvPolynomial.C 4 * (b + MvPolynomial.C 1))
        = MvPolynomial.eval ![D, r] b + 4 * (MvPolynomial.eval ![D, r] b + 1) := by
      rw [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C,
        MvPolynomial.eval_add, MvPolynomial.eval_C]
    refine ⟨?_, ?_, ?_⟩
    · rw [hα'def]
      exact mono_D_le S hite (by rw [hb']; omega)
    · exact mono_FD_le S hβΩ (by omega) (by rw [hb']; omega)
    · -- the pointwise conditions
      intro l hl
      obtain ⟨hβ0, hα0, hsum, hcomp⟩ := hpt l hl
      by_cases hlZ : αβ.2 l = 0
      · -- degenerate parameter: the chart is constant with value `1/2`
        have hα'lv := hα'val l hlZ
        have hhalf : (1 / 2 : ℝ) ∈ Work.WilG4a.I := by norm_num [Work.WilG4a.I]
        refine ⟨hβ0, by rw [hα'lv]; norm_num, by rw [hα'lv, hlZ]; norm_num, ?_, ?_⟩
        · intro t ht
          rw [hα'lv, hlZ]
          norm_num [Work.WilG4a.I]
        · intro i
          have hconst : (fun t : ℝ => F i l (α' l + αβ.2 l * t))
              = fun _ : ℝ => F i l (1 / 2) := by
            funext t
            rw [hα'lv, hlZ]
            simp
          refine ⟨?_, ?_⟩
          · rw [hconst]
            exact contDiffOn_const
          · intro m hm t ht
            rw [hconst, iteratedDeriv_const]
            split_ifs with hm0
            · rcases Set.mem_Ioo.mp (hFI i l hl (1 / 2) hhalf) with ⟨h1, h2⟩
              rw [abs_le]
              exact ⟨by linarith, by linarith⟩
            · norm_num
      · -- non-degenerate parameter: `α' = α`, and `β l > 0` gives the image clause
        have hβpos : 0 < αβ.2 l := lt_of_le_of_ne hβ0 (Ne.symm hlZ)
        have hα'lv := hα'val' l hlZ
        refine ⟨hβ0, by rw [hα'lv]; exact hα0, by rw [hα'lv]; exact hsum, ?_, ?_⟩
        · intro t ht
          obtain ⟨ht0, ht1⟩ := Set.mem_Ioo.mp ht
          rw [hα'lv]
          have hlt : αβ.2 l * t < αβ.2 l := by
            simpa using mul_lt_mul_of_pos_left ht1 hβpos
          exact ⟨by have := mul_pos hβpos ht0; linarith, by linarith⟩
        · intro i
          have heq : (fun t : ℝ => F i l (α' l + αβ.2 l * t))
              = (fun t : ℝ => F i l (αβ.1 l + αβ.2 l * t)) := by
            funext t
            rw [hα'lv]
          rw [heq]
          exact hcomp i
  · -- the `ε`-cover is unchanged, because the covering charts have `β l > 0`
    intro l hl x hx
    obtain ⟨αβ, hαβ, hβpos, t, ht, hdist⟩ := hcov l hl x hx
    refine ⟨(iteFun {l : Fin p → ℝ | αβ.2 l = 0} (fun _ : Fin p → ℝ => (1 / 2 : ℝ)) αβ.1,
      αβ.2), Finset.mem_image.mpr ⟨αβ, hαβ, rfl⟩, hβpos, t, ht, ?_⟩
    dsimp only
    have hv : iteFun {l : Fin p → ℝ | αβ.2 l = 0} (fun _ : Fin p → ℝ => (1 / 2 : ℝ)) αβ.1 l
        = αβ.1 l :=
      iteFun_not_mem _ _ _
        (show l ∉ {l : Fin p → ℝ | αβ.2 l = 0} from by simpa using ne_of_gt hβpos)
    rw [hv]
    exact hdist

/-- The corrected BNZ Corollary 5.5 (lead audit 2026-10-11: the frozen `F1Affine` is false at `p = 1`), in `ℝ`-coordinates, in every parameter dimension.  With `F1AffineW`'s two weakenings — a chart may be degenerate (`β l = 0`) at some parameters, and conversely the degenerate choice is always admissible as a fallback — the cell-based construction works, and the `ε`-cover is still required to be achieved by non-degenerate charts.  Adapt the proved `f1affine1_ge_all` (the same statement without the per-chart image clause `∀ t ∈ I, α l + β l t ∈ I`), which holds for the non-degenerate charts already and can be forced for the degenerate ones by deleting them from `Φ`. -/
theorem f1affine1W_all (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) (hL1 : ∀ (p F0 : ℕ), ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (cc : MvPolynomial (Fin 3) ℝ), ∀ (D r k : ℕ) (F : Fin k → (Fin p → ℝ) → ℝ → ℝ), (∀ i, Work.WilG4a.graphFam (F i) ∈ S.Ω F0 D (p + 1 + 1)) → ∃ (m : ℕ), (m : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ)] cc ∧ ∃ (κ : Fin m → Set (Fin (p + 1) → ℝ)), (∀ σ, κ σ ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (p + 1)) ∧ (∀ z : Fin (p + 1) → ℝ, ∃ σ, z ∈ κ σ) ∧ (∀ σ σ' : Fin m, σ ≠ σ' → Disjoint (κ σ) (κ σ')) ∧ (∀ σ (l : Fin p → ℝ), (∃ x : ℝ, Fin.snoc l x ∈ κ σ) → (∃ x : ℝ, Work.WilG4a.fibre (κ σ) l = {x}) ∨ (∃ a b : EReal, Work.WilG4a.fibre (κ σ) l = {y : ℝ | a < (y : EReal) ∧ (y : EReal) < b})) ∧ (∀ (σ : Fin m) (i : Fin k) (j : ℕ), j ≤ r + 2 → Disjoint (κ σ) (Work.WilG4a.badLocus (F i) j) ∨ κ σ ⊆ Work.WilG4a.badLocus (F i) j) ∧ (∀ (σ : Fin m) (i : Fin k) (j : ℕ), j ≤ r + 2 → Disjoint (κ σ) (Work.WilG4a.derivZeroSet (F i) j) ∨ κ σ ⊆ Work.WilG4a.derivZeroSet (F i) j) ∧ (∀ (σ : Fin m) (i : Fin k) (j : ℕ), j ≤ r + 1 → ∀ (l : Fin p → ℝ) (u v : ℝ), u < v → Set.Ioo u v ⊆ Work.WilG4a.fibre (κ σ) l → Disjoint (κ σ) (Work.WilG4a.badLocus (F i) (r + 2)) → (Disjoint (κ σ) (Work.WilG4a.derivZeroSet (F i) j) ∨ κ σ ⊆ Work.WilG4a.derivZeroSet (F i) j) → (∀ x ∈ Set.Ioo u v, ContDiffAt ℝ (r + 2) (fun y : ℝ => F i l y) x) ∧ ((∀ x ∈ Set.Ioo u v, 0 ≤ iteratedDeriv j (fun y : ℝ => F i l y) x) ∨ (∀ x ∈ Set.Ioo u v, iteratedDeriv j (fun y : ℝ => F i l y) x ≤ 0)))) (hG3a : ∀ (r : ℕ) (f : ℝ → ℝ), ContDiffOn ℝ (r + 1) f (Set.Ioo 0 1) → (∀ x ∈ Set.Ioo (0 : ℝ) 1, f x ∈ Set.Ioo (0 : ℝ) 1) → (∀ j ≤ r + 1, (∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ iteratedDerivWithin j f (Set.Ioo 0 1) x) ∨ (∀ x ∈ Set.Ioo (0 : ℝ) 1, iteratedDerivWithin j f (Set.Ioo 0 1) x ≤ 0)) → ∀ M : ℝ, 1 < M → ∀ j ≤ r, ∀ x ∈ Set.Ioo (0 : ℝ) 1, (j : ℝ) / M < x → x < 1 - j / M → |iteratedDerivWithin j f (Set.Ioo 0 1) x| < M ^ j) (hG3b : ∀ (r : ℕ) (ε : ℝ), 0 < ε → ε < 1 → ∃ s : Finset (ℝ × ℝ), (s.card : ℝ) ≤ 8 * (r + 1) * (-Real.log ε + 2) ∧ (∀ q ∈ s, 0 < q.1 ∧ q.1 < q.2 ∧ q.2 < 1 ∧ (q.2 - q.1) * (r + 1) ≤ min q.1 (1 - q.2)) ∧ (Set.Icc ε (1 - ε) ⊆ (⋃ q ∈ s, Set.Icc q.1 q.2))) : ∀ p : ℕ, Work.WilG4a.F1Affine1W S p := by
  intro p
  exact f1affineW_of_f1affineGe S p (f1affine1_ge_all S hcd hder hL1 hG3a hG3b p)

end Work.WilG4a
