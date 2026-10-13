import Mathlib
import Submission.Work.WilkiesH.Basic
import Submission.Work.WilkiesH.Cell
import Submission.Work.WilkiesH.Cell.cellDimLE_of_isCell_dimLE
import Submission.Work.WilkiesH.Cell.isCell_nonempty
import Submission.Work.WilkiesH.Dim.dimLE_mono
import Submission.Work.WilkiesH.Mfd.Defs
import Submission.Work.WilkiesH.Strat.BadCell
import Submission.Work.WilkiesH.Strat.CellBand
import Submission.Work.WilkiesH.Strat.cell_par_exists
import Submission.Work.WilkiesH.Strat.rft.Master

/-!
# Auxiliary facts for the `μ`-regular part of an `Ω`-set

This file collects the elementary geometric facts behind
`Work.WilkiesH.Strat.regular_part_cover`:

* `cell_chart_dim_le`: for a cell `κ` with a chart over `m` coordinates
  (`Work.WilkiesH.Cell.Good`), the number `m` is bounded by any `μ` with `DimLE V μ`, `κ ⊆ V`;
* `cellBand_dimLE`: for a cell `κ ∈ S.Ω F D n` the number `d` of band steps of its
  construction bounds the o-minimal dimension of `κ` (the tameness input, via
  `Work.WilkiesH.Strat.cell_par_exists` and the dimension theorem
  `Work.WilkiesH.Strat.dimLE_of_graphOver` for `Ω`-graphs);
* the "technical core" `isGraphAt_of_cell_of_locally_full`: a cell `κ ⊆ V` of `V` which is
  `V`-locally full at a point `x ∈ κ` (there is an open `U ∋ x` with `U ∩ V ⊆ κ`) and which is
  not `(μ-1)`-thin is a `μ`-regular point of `V` (`Work.WilkiesH.IsGraphAt μ V x`).
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkiesH.Strat.RegAux

open WilkiesDesign WilkiesConjecture
open Work.WilkiesH

/-! ## 1. Coordinate projections -/

/-- Restriction of functions `Fin m → ℝ` along an embedding `e : Fin p ↪ Fin m` is an open
map: a coordinate projection of a product is open. -/
theorem isOpenMap_compEmbedding {p m : ℕ} (e : Fin p ↪ Fin m) :
    IsOpenMap (fun u : Fin m → ℝ => u ∘ e) := by
  intro s hs
  rw [isOpen_pi_iff]
  intro f hf
  rw [Set.mem_image] at hf
  obtain ⟨x, hxs, hxf⟩ := hf
  rw [isOpen_pi_iff] at hs
  obtain ⟨I, u, hu, hIu⟩ := hs x hxs
  refine ⟨Finset.univ.filter (fun i : Fin p => e i ∈ I), fun i => u (e i), ?_, ?_⟩
  · intro a ha
    rw [Finset.mem_filter] at ha
    exact ⟨(hu (e a) ha.2).1, by rw [← hxf]; exact (hu (e a) ha.2).2⟩
  · intro g hg
    refine ⟨Function.extend e g x, hIu ?_, ?_⟩
    · rw [Set.mem_pi]
      intro j hj
      by_cases hjr : ∃ i, e i = j
      · obtain ⟨i, hi⟩ := hjr
        have hiJ : i ∈ Finset.univ.filter (fun i : Fin p => e i ∈ I) := by
          rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hi ▸ hj⟩
        have hgi : g i ∈ u (e i) := Set.mem_pi.mp hg i (Finset.mem_coe.mpr hiJ)
        rw [← hi, Function.Injective.extend_apply e.injective g x i]
        exact hgi
      · rw [Function.extend_apply' g x j hjr]
        exact (hu j hj).2
    · funext i
      show Function.extend e g x (e i) = g i
      rw [Function.Injective.extend_apply e.injective g x i]

/-- The projection of an open nonempty set onto a set of coordinates has nonempty interior. -/
theorem interior_image_compEmbedding_nonempty {p m : ℕ} (f : Fin p ↪ Fin m)
    {U : Set (Fin m → ℝ)} (hU : IsOpen U) (hne : U.Nonempty) :
    (interior ((fun u : Fin m → ℝ => u ∘ f) '' U)).Nonempty := by
  have himg : IsOpen ((fun u : Fin m → ℝ => u ∘ f) '' U) := isOpenMap_compEmbedding f U hU
  rw [himg.interior_eq]
  exact hne.image _

/-! ## 2. The dimension of a cell chart -/

/-- **A chart dimension is bounded by any `DimLE` bound.**  If `κ ⊆ V` is a cell with a chart
over the coordinates selected by `e : Fin m ↪ Fin n` (so that `ProjE e κ` is open and
nonempty), and `DimLE V μ`, then `m ≤ μ`. -/
theorem cell_chart_dim_le {n μ m : ℕ} {κ V : Set (Fin n → ℝ)} (hκV : κ ⊆ V)
    (hVdim : DimLE V μ) (e : Fin m ↪ Fin n) (hopen : IsOpen (Cell.ProjE e κ))
    (hne : (Cell.ProjE e κ).Nonempty) : m ≤ μ := by
  by_contra hcon
  push_neg at hcon
  have hle : μ + 1 ≤ m := hcon
  let f : Fin (μ + 1) ↪ Fin m :=
    ⟨fun i => ⟨i.val, by omega⟩, by
      intro a b hab
      exact Fin.ext (by simpa using congrArg Fin.val hab)⟩
  let e' : Fin (μ + 1) ↪ Fin n := f.trans e
  have himg : (fun u : Fin m → ℝ => u ∘ f) '' (Cell.ProjE e κ) = Cell.ProjE e' κ := by
    ext w
    constructor
    · rintro ⟨u, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y ∘ e, ⟨y, hy, rfl⟩, rfl⟩
  have hnonempty := interior_image_compEmbedding_nonempty f hopen hne
  rw [himg] at hnonempty
  have hempty : interior (Cell.ProjE e' κ) = ∅ := dimLE_of_subset hVdim hκV e'
  rw [hempty] at hnonempty
  exact Set.not_nonempty_empty hnonempty

/-- **A chart dimension is at least `μ` for a cell which is not `(μ-1)`-thin.** -/
theorem cell_chart_dim_ge {n μ m : ℕ} {κ : Set (Fin n → ℝ)} (hcell : CellDimLE n κ m)
    (hμ : ¬ CellDimLE n κ (μ - 1)) : μ ≤ m := by
  by_contra hcon
  push_neg at hcon
  exact hμ (hcell.mono (by omega))

/-! ## 3. The band count bounds the dimension of an `Ω`-cell -/

/-- **The band count bounds the dimension of an `Ω`-cell.**  For a cell `κ ∈ S.Ω F D n` the
o-minimal dimension of `κ` is at most the number of band steps in its construction.  (This is
the tameness input: for an arbitrary continuous cell the statement fails, e.g. for the graph of
a continuous surjection `ℝ → [0,1]²`; for `Ω`-cells the graph parametrisation of
`Work.WilkiesH.Strat.cell_par_exists` turns `κ` into the image of an `Ω`-graph, to which the
dimension theorem `Work.WilkiesH.Strat.dimLE_of_graphOver` applies.) -/
theorem cellBand_dimLE {S : WilkiesDesign.SOMin} (hcd : S.SharpCD) {n d F D : ℕ}
    {κ : Set (Fin n → ℝ)} (h : CellBand n κ d) (hΩ : κ ∈ S.Ω F D n) : DimLE κ d := by
  obtain ⟨e, U, ψ, A, L, hUo, hUne, hcont, hinj, hψU, hsec, hΓmem⟩ :=
    cell_par_exists (S := S) h (Cell.isCell_nonempty (CellBand.isCell h)) F D hΩ
  set Γ : Set (Fin (d + n) → ℝ) :=
    {z : Fin (d + n) → ℝ | (fun i : Fin d => z (Fin.castAdd n i)) ∈ U ∧
      (fun j : Fin n => z (Fin.natAdd d j)) = ψ (fun i : Fin d => z (Fin.castAdd n i))}
    with hΓdef
  have hGrmem : Γ ∈ S.Ω A L (d + n) := hΓmem
  have hgr : GraphOver d Γ := by
    intro z hz z' hz' heq
    obtain ⟨hz1, hz2⟩ := hz
    obtain ⟨hz1', hz2'⟩ := hz'
    refine eq_of_castAdd_natAdd heq ?_
    intro j
    have hz2j : z (Fin.natAdd d j) = ψ (fun i : Fin d => z (Fin.castAdd n i)) j :=
      congrFun hz2 j
    have hz2'j : z' (Fin.natAdd d j) = ψ (fun i : Fin d => z' (Fin.castAdd n i)) j :=
      congrFun hz2' j
    rw [hz2j, hz2'j]
    congr 1
    exact funext heq
  have hdim : DimLE (Work.WilG5.lastN n Γ) d :=
    (dimLE_of_graphOver (S := S) hcd d n A L Γ hGrmem hgr).1
  refine dimLE_of_subset hdim ?_
  intro y hy
  rw [← hψU] at hy
  obtain ⟨u, huU, rfl⟩ := hy
  refine ⟨u, ?_⟩
  rw [hΓdef]
  refine ⟨by simpa [Fin.append_left] using huU, ?_⟩
  funext j
  simp only [Fin.append_left, Fin.append_right]

/-! ## 4. The technical core -/

/-- **A cell which is `V`-locally full at one of its points is regular there**, chart form: if
`κ = Φ '' Ωc` is a cell charted over `m` coordinates, `m = μ`, `x ∈ κ` lies in an open `U` with
`U ∩ V ⊆ κ`, and `κ ⊆ V`, then `V` is a `μ`-dimensional graph at `x`. -/
theorem isGraphAt_of_chart {n m μ : ℕ} {κ V : Set (Fin n → ℝ)} (hm : m = μ)
    (e : Fin m ↪ Fin n) {Ωc : Set (Fin m → ℝ)} (hΩo : IsOpen Ωc)
    (Φ : (Fin m → ℝ) → (Fin n → ℝ)) (hcont : ContinuousOn Φ Ωc)
    (hΦW : Φ '' Ωc = κ) (hsec : ∀ u ∈ Ωc, Φ u ∘ e = u)
    (hκV : κ ⊆ V) {x : Fin n → ℝ} (hx : x ∈ κ)
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hxU : x ∈ U) (hUV : U ∩ V ⊆ κ) :
    IsGraphAt μ V x := by
  subst hm
  -- `x` is on the graph
  obtain ⟨ux, huxΩ, huxx⟩ := hΦW ▸ hx
  have hxe : x ∘ e = ux := by rw [← huxx, hsec ux huxΩ]
  have hΦx : Φ (x ∘ e) = x := by rw [hxe]; exact huxx
  -- a box inside `U`
  obtain ⟨δ, hδ, hboxU⟩ := mem_interior_iff_boxAround.mp
    (mem_interior_iff_mem_nhds.mpr (hU.mem_nhds hxU))
  have hxbox : x ∈ boxAround x δ :=
    mem_boxAround.mpr fun i => by rw [sub_self, abs_zero]; exact hδ
  refine ⟨e, {t : Fin m → ℝ | t ∈ Ωc ∧ Φ t ∈ boxAround x δ}, Φ, δ, hδ, ?_, ?_, ?_,
    ⟨x ∘ e, ⟨by rw [hxe]; exact huxΩ, by rw [hΦx]; exact hxbox⟩, hΦx⟩, ?_⟩
  · -- the chart domain is open
    exact ContinuousOn.isOpen_inter_preimage hcont hΩo (isOpen_boxAround x δ)
  · exact hcont.mono (fun t ht => ht.1)
  · intro t ht
    exact hsec t ht.1
  · intro y hy
    constructor
    · intro hyV
      have hyκ : y ∈ κ := hUV ⟨hboxU hy, hyV⟩
      rw [← hΦW] at hyκ
      obtain ⟨t, htΩ, hty⟩ := hyκ
      exact ⟨t, ⟨htΩ, by rw [hty]; exact hy⟩, hty⟩
    · rintro ⟨t, ⟨htΩ, htbox⟩, ht_eq⟩
      rw [← ht_eq]
      exact hκV (hΦW ▸ ⟨t, htΩ, rfl⟩)

/-- **A cell which is `V`-locally full at one of its points is regular there.**  If `κ ⊆ V` is
a cell of `V` with `DimLE V μ`, `x ∈ κ` lies in an open `U` with `U ∩ V ⊆ κ`, and `κ` is not
`(μ-1)`-thin, then `V` is a `μ`-dimensional graph at `x`. -/
theorem isGraphAt_of_cell_of_locally_full {n μ : ℕ} {κ V : Set (Fin n → ℝ)}
    (hκ : IsCell n κ) (hκV : κ ⊆ V) (hVdim : DimLE V μ)
    (hμ : ¬ CellDimLE n κ (μ - 1)) {x : Fin n → ℝ} (hx : x ∈ κ)
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hxU : x ∈ U) (hUV : U ∩ V ⊆ κ) :
    IsGraphAt μ V x := by
  obtain ⟨m, e, Φ, hcell, hopen, hcont, hleft, hright⟩ := Cell.good_of_isCell hκ
  have hne : (Cell.ProjE e κ).Nonempty := ⟨x ∘ e, x, hx, rfl⟩
  have hmle : m ≤ μ := cell_chart_dim_le hκV hVdim e hopen hne
  have hmge : μ ≤ m := cell_chart_dim_ge hcell hμ
  have hm : m = μ := le_antisymm hmle hmge
  have hΦW : Φ '' Cell.ProjE e κ = κ := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro y ⟨u, hu, rfl⟩
      obtain ⟨z, hz, hzu⟩ := hu
      rw [← hzu, hleft z hz]
      exact hz
    · intro y hy
      exact ⟨y ∘ e, ⟨y, hy, rfl⟩, hleft y hy⟩
  exact isGraphAt_of_chart hm e hopen Φ hcont hΦW (fun u hu => hright u hu) hκV hx hU hxU hUV

end Work.WilkiesH.Strat.RegAux
