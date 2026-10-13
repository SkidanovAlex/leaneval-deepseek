import Mathlib
import Submission.Work.WilkG4c.ExactCellDefs
import Submission.Work.WilkG4c.ExactCellCore
import Submission.Work.WilkG4c.ExactCellMem
import Submission.Work.WilkG4c.ExactCellDiff
import Submission.Work.WilkG4c.ExactCellGraph
import Submission.Work.WilG4c.StepFiberEnds
import Submission.Work.WilG4c.cellFibre_param
import Submission.Work.WilG4c.graphOfLinComb_mem
import Submission.Work.WilG4c.graphOfCompGen
import Submission.Work.WilG4c.CellMonoDeriv
import Submission.Work.WilG1.Cell.isCell_of_mem_cylDecomp
import Submission.Work.WilkG4c.slice_abs_sub_le
import Submission.Work.WilkG4c.exists_eval_dom
import Submission.Work.WilkG4c.hasDerivAt_snoc
import Submission.Work.WilkG4c.deriv_snoc_eq_fderiv
import Submission.Work.WilkG4c.mem_Ioo_min_max_of_injOn

set_option autoImplicit false

noncomputable section
open Classical
open scoped Topology

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilG0 Work.WilG1

/-- **BNZ Lemma 5.5, per cell (`r = 1`, exact cover).**  Let `κ` be an `Ω`-bounded cell of a
cylindrical decomposition `C` of `ℝ^{p+1}` (coordinates `(λ,s)`), whose fibre over `Λ` is
nonempty and which lies in `inCubeSet p 1`; let `T : Fin k → (Fin p → ℝ) → (Fin 1 → ℝ) → ℝ` be a
tuple of one-variable definable families over `Λ` whose members are `C¹` on `κ`, take values in
`(0,1)` there and one of which is the *identity* `u ↦ u 0`, and such that on `κ` one member
dominates the absolute values of the `s`-derivatives of all members.  Then there is a single
chart `φ` of the `1`-cube with `Ω`-bounded coordinates (format independent of `D, D1`, degree
polynomial in `D, D1`), mapping the cube into the cell's fibre, hitting *every* point of the
cell's fibre with `(0,1)`-coordinate, and such that for *every* member the composite
`τ ↦ T_a(λ, φ(λ,·)(τ))` is differentiable on `(0,1)` with derivative bounded by `1` in absolute
value.

This is the per-cell engine of BNZ Lemma 5.5: with the identity among the members, the
dominating member `T₁` satisfies `|T₁'| ≥ 1` on `κ` (its derivative dominates the identity's
`1`), hence is monotone there; so `φ := T₁⁻¹ ∘ (the affine map onto the image interval of `T₁`
over the cell's fibre)` is well defined, maps *onto* the cell's fibre (this is the **exact**
cover — in contrast to the `ε`-cover of `Work.WilkG4c.F1Affine`), and
`|(T_a ∘ φ)'| = |T_a'/T₁'| · |affine'| ≤ 1` by the domination and because the image interval has
length `≤ 1` (values in `(0,1)`).  The fibre ends of `κ` are `Ω`-bounded by `StepFiberEnds`
(from `κ ∈ S.Ω F1 D1 (p+1)`), the graph of the inverse is `Ω`-bounded by
`Work.WilG5.reindex_mem` (reindexing the graph of `T₁`), and `graphOfCompGen` composes it with
the affine map. -/
theorem ChartsExactCell (S : WilkiesDesign.SOMin) (p : ℕ) :
    ∀ (F0 F1 : ℕ), ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D D1 k : ℕ) (Λ : Set (Fin p → ℝ)) (C : Finset (Set (Fin (p + 1) → ℝ)))
        (κ : Set (Fin (p + 1) → ℝ))
        (T : Fin k → (Fin p → ℝ) → (Fin 1 → ℝ) → ℝ),
        (∃ i : Fin k, ∀ (l : Fin p → ℝ) (u : Fin 1 → ℝ), T i l u = u 0) →
        (∀ i, WilkiesDesign.CG.famGraph (T i) ∈ S.Ω F0 D (p + 1 + 1)) →
        κ ∈ S.Ω F1 D1 (p + 1) →
        (∀ i, ∀ w ∈ κ, T i (Fin.init w) (fun _ : Fin 1 => w (Fin.last p)) ∈ Set.Ioo (0 : ℝ) 1) →
        WilkiesDesign.IsCylDecomp (p + 1) C →
        κ ∈ C →
        κ ⊆ Work.WilG4c.inCubeSet p 1 →
        (∀ i, ∀ w ∈ κ, ContDiffAt ℝ 1 (fun z : Fin (p + 1) → ℝ =>
            T i (Fin.init z) (fun _ : Fin 1 => z (Fin.last p))) w) →
        (∃ i : Fin k, ∀ a : Fin k, ∀ w ∈ κ,
            |fderiv ℝ (fun z : Fin (p + 1) → ℝ =>
                T a (Fin.init z) (fun _ : Fin 1 => z (Fin.last p))) w
              (Pi.single (Fin.last p) 1)|
          ≤ |fderiv ℝ (fun z : Fin (p + 1) → ℝ =>
                T i (Fin.init z) (fun _ : Fin 1 => z (Fin.last p))) w
              (Pi.single (Fin.last p) 1)|) →
        (∀ l ∈ Λ, ∃ s : ℝ, Fin.snoc l s ∈ κ) →
        ∃ φ : Work.WilkG4c.ChartTuple p 1,
          (∀ j : Fin 1, WilkiesDesign.CG.famGraph (φ j)
            ∈ S.Ω a (MvPolynomial.eval ![D, D1] b) (p + 1 + 1)) ∧
          (∀ l ∈ Λ, ∀ t ∈ WilkiesDesign.openCube 1,
            φ 0 l t ∈ Set.Ioo (0 : ℝ) 1 ∧ Fin.snoc l (φ 0 l t) ∈ κ) ∧
          (∀ a : Fin k, ∀ l ∈ Λ, ∀ τ ∈ Set.Ioo (0 : ℝ) 1,
            DifferentiableAt ℝ (fun τ' : ℝ => T a l (fun _ : Fin 1 => φ 0 l (fun _ => τ'))) τ ∧
            |deriv (fun τ' : ℝ => T a l (fun _ : Fin 1 => φ 0 l (fun _ => τ'))) τ| ≤ 1) ∧
          (∀ l ∈ Λ, ∀ s ∈ Set.Ioo (0 : ℝ) 1, Fin.snoc l s ∈ κ →
            ∃ t ∈ WilkiesDesign.openCube 1, φ 0 l t = s) := by
  intro F0 F1
  -- ### the constants of the two `StepFiberEnds` invocations and of the two composition lemmas
  obtain ⟨aE2, bE2, hE2⟩ := Work.WilG4c.StepFiberEnds S p
    (max (F1 + 2 * ((p + 2) + (p + 1)) + 1) (F0 + 2 * ((p + 2) + (p + 2)) + 1) + 1 + 1)
  obtain ⟨aE3, bE3, hE3⟩ := Work.WilG4c.StepFiberEnds S (p + 1)
    (max (F1 + 2 * ((p + 2) + (p + 1)) + 1) (F0 + 2 * ((p + 2) + (p + 2)) + 1) + 1)
  obtain ⟨aLC, cLC, hLC⟩ := Work.WilG4c.graphOfLinComb_mem S (p + 1)
  obtain ⟨cCG1, cCG2, hCG⟩ := Work.WilG4c.graphOfCompGen S (p + 1) (p + 1)
  obtain ⟨b2', hb2'⟩ := exists_eval_dom bE2 4 0
  obtain ⟨b3', hb3'⟩ := exists_eval_dom bE3 4 0
  refine ⟨aE3 + max ((aE2 + 2 * ((p + 2) + (p + 1)) + 1)
      + (aE2 + 2 * ((p + 2) + (p + 1)) + 1) + (p + 1 + 1) + aLC) (p + 1 + 1) + cCG1,
    b3' + MvPolynomial.C (p + 1) * ((b2' + MvPolynomial.C 2) + (b2' + MvPolynomial.C 2)
      + MvPolynomial.C 1 + MvPolynomial.C cLC) + MvPolynomial.C cCG2, ?_⟩
  intro D D1 k Λ C κ T hid hFam hκΩ hval hdec hκC hκcube hC1 hdom hfib
  have hcell : IsCell (p + 1) κ := Work.WilG1.Cell.isCell_of_mem_cylDecomp hdec hκC
  obtain ⟨iD, hdomD⟩ := hdom
  obtain ⟨i0, hid0⟩ := hid
  -- the flattened members, the dominating one and the identity one
  let Fd : (Fin (p + 1) → ℝ) → ℝ :=
    fun w => T iD (Fin.init w) (fun _ => w (Fin.last p))
  have hflatD : graphOf Fd ∈ S.Ω F0 D (p + 2) := by
    have h := hFam iD
    rw [famGraph_eq_graphOf_flatFam] at h
    exact h
  have hder_id : ∀ z : Fin (p + 1) → ℝ,
      fderiv ℝ (fun w : Fin (p + 1) → ℝ => T i0 (Fin.init w) (fun _ => w (Fin.last p))) z
        (Pi.single (Fin.last p) (1 : ℝ)) = 1 := by
    intro z
    have hflat_id_fun : (fun w : Fin (p + 1) → ℝ => T i0 (Fin.init w)
          (fun _ => w (Fin.last p))) = fun x : Fin (p + 1) → ℝ => x (Fin.last p) := by
      funext x
      simp only [hid0]
    have hd : DifferentiableAt ℝ (fun x : Fin (p + 1) → ℝ => x (Fin.last p))
        (Fin.snoc (Fin.init z) (z (Fin.last p))) := by fun_prop
    have h := deriv_snoc_eq_fderiv (fun x : Fin (p + 1) → ℝ => x (Fin.last p)) (Fin.init z)
      (z (Fin.last p)) hd
    rw [Fin.snoc_init_self] at h
    have h2 : deriv (fun s' : ℝ => (Fin.snoc (Fin.init z) s') (Fin.last p))
        (z (Fin.last p)) = 1 := by
      have he : (fun s' : ℝ => (Fin.snoc (Fin.init z) s') (Fin.last p)) = fun s' => s' := by
        funext s'
        exact Fin.snoc_last _ _
      rw [he]
      simp
    rw [h2] at h
    rw [hflat_id_fun]
    exact h.symm
  -- ### the two auxiliary sets, and their last-coordinate conditions
  have hZtl : invSet κ Fd ∈ S.Ω
      (max (F1 + 2 * ((p + 2) + (p + 1)) + 1) (F0 + 2 * ((p + 2) + (p + 2)) + 1) + 1)
      ((D1 + 2) + (D + 2)) (p + 2) := invSet_mem S hκΩ hflatD
  have hZim : imgSet κ Fd ∈ S.Ω
      (max (F1 + 2 * ((p + 2) + (p + 1)) + 1) (F0 + 2 * ((p + 2) + (p + 2)) + 1) + 1 + 1)
      ((D1 + 2) + (D + 2)) (p + 1) := imgSet_mem S hκΩ hflatD
  have hZtl_last : ∀ z ∈ invSet κ Fd, z (Fin.last (p + 1)) ∈ Set.Ioo (0 : ℝ) 1 := by
    intro z hz
    rw [mem_invSet_self] at hz
    have h := inCubeSet_one_last (p := p)
      (w := (Fin.snoc (Fin.init (Fin.init z)) (z (Fin.last (p + 1))) : Fin (p + 1) → ℝ))
      (hκcube hz.1)
    simpa using h
  have hZim_last : ∀ z ∈ imgSet κ Fd, z (Fin.last p) ∈ Set.Ioo (0 : ℝ) 1 := by
    intro z hz
    obtain ⟨s, hs⟩ := hz
    rw [← Fin.snoc_init_self z] at hs
    rw [mem_invSet] at hs
    obtain ⟨hs1, hs2⟩ := hs
    have hv := hval iD (Fin.snoc (Fin.init z) s) hs1
    simp only [Fin.init_snoc, Fin.snoc_last] at hv hs2
    rw [← hs2]
    simpa [Fd, Fin.init_snoc, Fin.snoc_last] using hv
  -- ### the fibre ends of the image and the inverse
  obtain ⟨α, β, hαgraph, hβgraph, hαβprop⟩ :=
    hE2 ((D1 + 2) + (D + 2)) 0 (imgSet κ Fd) hZim hZim_last
  obtain ⟨g, _, hggraph, _, hgprop⟩ :=
    hE3 ((D1 + 2) + (D + 2)) 0 (invSet κ Fd) hZtl hZtl_last
  have h2deg : MvPolynomial.eval ![(D1 + 2) + (D + 2), 0] bE2
      ≤ MvPolynomial.eval ![D, D1] b2' := hb2' D D1 ((D1 + 2) + (D + 2)) (by omega)
  have h3deg : MvPolynomial.eval ![(D1 + 2) + (D + 2), 0] bE3
      ≤ MvPolynomial.eval ![D, D1] b3' := hb3' D D1 ((D1 + 2) + (D + 2)) (by omega)
  -- ### the `Ω`-bound for the chart
  have hgraph : famGraph (chartVal g α β) ∈ S.Ω
      (aE3 + max ((aE2 + 2 * ((p + 2) + (p + 1)) + 1)
        + (aE2 + 2 * ((p + 2) + (p + 1)) + 1) + (p + 1 + 1) + aLC) (p + 1 + 1) + cCG1)
      (MvPolynomial.eval ![D, D1]
        (b3' + MvPolynomial.C (p + 1) * ((b2' + MvPolynomial.C 2) + (b2' + MvPolynomial.C 2)
          + MvPolynomial.C 1 + MvPolynomial.C cLC) + MvPolynomial.C cCG2)) (p + 1 + 1) :=
    exactCell_graph S p aLC cLC cCG1 cCG2 hLC hCG D D1 aE2 aE3 bE2 b2' bE3 b3' α β g
      hαgraph hβgraph hggraph h2deg h3deg
  -- ### fibre-convexity of `κ` and the expansion estimate for the dominating member
  have hfibconv : ∀ w ∈ κ, ∀ w' ∈ κ, Fin.init w = Fin.init w' → ∀ t : ℝ,
      w (Fin.last p) ≤ t → t ≤ w' (Fin.last p) → Fin.snoc (Fin.init w) t ∈ κ := by
    intro w hw w' hw' hinit t h1 h2
    have hord := Work.WilG4c.ordConnected_fibre_of_isCell hcell (Fin.init w)
    have hwK : w (Fin.last p) ∈ Work.WilG4c.fibre p κ (Fin.init w) := by
      show Fin.snoc (Fin.init w) (w (Fin.last p)) ∈ κ
      rwa [Fin.snoc_init_self]
    have hw'K : w' (Fin.last p) ∈ Work.WilG4c.fibre p κ (Fin.init w) := by
      show Fin.snoc (Fin.init w) (w' (Fin.last p)) ∈ κ
      rw [hinit]
      rwa [Fin.snoc_init_self]
    have hmem := hord.out hwK hw'K ⟨h1, h2⟩
    rwa [Work.WilG4c.fibre] at hmem
  have hexp : ∀ w ∈ κ, ∀ w' ∈ κ, Fin.init w = Fin.init w' →
      |w (Fin.last p) - w' (Fin.last p)| ≤ |Fd w - Fd w'| := by
    intro w hw w' hw' hinit
    have h := slice_abs_sub_le (g := Fd) (κ := κ) 1 one_pos hfibconv
      (fun z hz => hC1 iD z hz) (fun z hz => by
        have h1 := hder_id z
        have h2 := hdomD i0 z hz
        rw [h1] at h2
        simpa using h2)
      w hw w' hw' hinit
    simpa using h
  -- ### the fibre ends of `κ`
  obtain ⟨aFEk, bFEk, hFEk⟩ := Work.WilG4c.StepFiberEnds S p F1
  obtain ⟨loK, hiK, _, _, hloK⟩ := hFEk D1 0 κ hκΩ
    (fun z hz => inCubeSet_one_last (hκcube hz))
  -- ### the per-parameter facts
  have hcore : ∀ l ∈ Λ, CellFacts κ Fd g α β l := by
    intro l hl
    have hlne : ∃ s : ℝ, Fin.snoc l s ∈ κ := hfib l hl
    have hcontf : ∀ x : ℝ, Fin.snoc l x ∈ κ →
        ContinuousAt (fun s : ℝ => Fd (Fin.snoc l s)) x := by
      intro x hx
      have hd : DifferentiableAt ℝ Fd (Fin.snoc l x) :=
        (hC1 iD (Fin.snoc l x) hx).differentiableAt (by norm_num)
      exact (hasDerivAt_snoc hd).continuousAt
    have hKord : ({s : ℝ | Fin.snoc l s ∈ κ}).OrdConnected :=
      Work.WilG4c.ordConnected_fibre_of_isCell hcell l
    obtain ⟨hdich, _, _⟩ := Work.WilG4c.cellFibre_param hcell hloK l hlne
    have hdich' : (∃ c : ℝ, {s : ℝ | Fin.snoc l s ∈ κ} = {c}) ∨
        (∃ A B : ℝ, A < B ∧ {s : ℝ | Fin.snoc l s ∈ κ} = Set.Ioo A B) := by
      rcases hdich with ⟨c, _, _, hc⟩ | ⟨A, B, hAB, _, _, hK⟩
      · exact Or.inl ⟨c, hc⟩
      · exact Or.inr ⟨A, B, hAB, hK⟩
    have hmem_img : ∃ η : ℝ, Fin.snoc l η ∈ imgSet κ Fd :=
      ⟨Fd (Fin.snoc l (Classical.choose hlne)), (mem_imgSet).mpr
        ⟨Classical.choose hlne, Classical.choose_spec hlne, rfl⟩⟩
    have hαβprop' := hαβprop l hmem_img
    have hglo : ∀ u : Fin (p + 1) → ℝ, (∃ x : ℝ, Fin.snoc u x ∈ invSet κ Fd) →
        (∀ x : ℝ, Fin.snoc u x ∈ invSet κ Fd → g u ≤ x) ∧
        (∀ v : ℝ, g u < v → ∃ x : ℝ, Fin.snoc u x ∈ invSet κ Fd ∧ x < v) := by
      intro u hu
      obtain ⟨h1, h2, _⟩ := hgprop u hu
      exact ⟨fun x hx => (h1 x hx).1, h2⟩
    exact exactCell_core (f := Fd) hκcube (fun w hw => hval iD w hw) hexp
      hcontf hKord hdich' hαβprop' hglo hlne
  -- ### the chart and its three properties
  refine ⟨fun _ => chartVal g α β, ?_, ?_, ?_, ?_⟩
  · intro j
    exact hgraph
  · intro l hl t ht
    exact exactCell_mem (hcore l hl) hκcube t ht
  · intro a l hl τ hτ
    refine exactCell_diff (fa := fun (a : Fin k) (s : ℝ) => T a l (fun _ => s))
      (dfa := fun (a : Fin k) (x : ℝ) =>
        fderiv ℝ (fun w : Fin (p + 1) → ℝ => T a (Fin.init w) (fun _ => w (Fin.last p)))
          (Fin.snoc l x) (Pi.single (Fin.last p) 1))
      (df := fun x : ℝ => fderiv ℝ Fd (Fin.snoc l x) (Pi.single (Fin.last p) 1))
      (hcore l hl) ?_ ?_ ?_ ?_ ?_ a τ hτ
    · intro x hx
      have hd : DifferentiableAt ℝ Fd (Fin.snoc l x) :=
        (hC1 iD (Fin.snoc l x) hx).differentiableAt (by norm_num)
      exact (hasDerivAt_snoc hd).continuousAt
    · intro x hx
      exact hasDerivAt_snoc ((hC1 iD (Fin.snoc l x) hx).differentiableAt (by norm_num))
    · intro x hx
      have h1 := hder_id (Fin.snoc l x)
      have h2 := hdomD i0 (Fin.snoc l x) hx
      rw [h1] at h2
      simpa using h2
    · intro a x hx
      have hd : DifferentiableAt ℝ (fun w : Fin (p + 1) → ℝ => T a (Fin.init w)
          (fun _ => w (Fin.last p))) (Fin.snoc l x) :=
        (hC1 a (Fin.snoc l x) hx).differentiableAt (by norm_num)
      have h := hasDerivAt_snoc hd
      simpa only [Fin.init_snoc, Fin.snoc_last] using h
    · intro a x hx
      exact hdomD a (Fin.snoc l x) hx
  · intro l hl s hs hκs
    exact exactCell_surj (hcore l hl) s hs hκs

end Work.WilkG4c
