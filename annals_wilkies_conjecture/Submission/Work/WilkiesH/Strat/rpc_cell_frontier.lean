import Mathlib
import Submission.Work.WilkiesH.Mfd.Defs
import Submission.Work.WilkiesH.Strat.Defs
import Submission.Work.WilkiesH.Strat.dimLE_iUnion_fin
import Submission.Work.WilkiesH.Strat.CellBand
import Submission.Work.WilkiesH.Strat.bandChart_of_cellBand
import Submission.Work.WilkiesH.Strat.rp_aux
import Submission.Work.WilkiesH.Strat.SI.frontierThin
import Submission.Work.WilkiesH.Strat.cell_par_exists
import Submission.Work.WilkiesH.Strat.omega_closure_v2
import Submission.Work.WilkiesH.Strat.BadCell
import Submission.Work.WilkiesH.Omega.semialg_subset_intersection_zeroLocus
import Submission.Work.WilkiesH.Omega.interior_zeroLocus_eq_empty
import Submission.Work.WilkiesI.LocalGraphOfPderiv

/-!
# The relative frontier of a cell is thin

This file contains, in the namespace `Work.WilkiesH.Strat.RPC`, a self-contained proof of the
cell-frontier lemma `Work.WilkiesH.Strat.RPC.frontierThin`, the last geometric input of the
regular-part cover `Work.WilkiesH.Strat.regular_part_cover` (BNZ §2.3).

The geometric core is `RPC.badParams_interior_empty` — "the branch/singular locus of a
semialgebraic set of dimension `d` accumulated by a `d`-dimensional chart is thin" — obtained from

* `Omega.semialg_subset_intersection_zeroLocus`: for every extra coordinate `j` a nonzero fibre
  polynomial `Qⱼ` vanishing on `V`;
* `squarefree_excision_snoc`: a squarefree replacement `Gⱼ` of `Qⱼ`, with the same roots off the
  non-vanishing locus `{lⱼ ≠ 0}` and all roots simple;
* `Work.WilkiesI.LocalGraphOfPderiv`: the root of `Gⱼ` near a simple root `(u, ψ u j)` is unique.

Rolle's theorem (`RPC.pderiv_eq_zero_of_two_roots`) shows that a parameter `u` at which the chart
is accumulated by `V \ κ` forces `(u, ψ u j)` to be a *multiple* root of `Gⱼ (u, ·)`, contradicting
the uniqueness of the simple root; hence the bad parameter set lies in the finite union of the
zero sets of the `lⱼ`, which has empty interior.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical

namespace Work.WilkiesH.Strat

open WilkiesDesign WilkiesConjecture
open Work.WilkiesH
open scoped Topology

namespace RPC

/-- A finite union of closed sets with empty interior has empty interior. -/
theorem interior_iUnion_eq_empty {α ι : Type*} [TopologicalSpace α] [Finite ι] {Z : ι → Set α}
    (hZc : ∀ i, IsClosed (Z i)) (hZe : ∀ i, interior (Z i) = ∅) :
    interior (⋃ i, Z i) = ∅ := by
  refine Set.subset_empty_iff.mp ?_
  have hND : IsNowhereDense (⋃ i, Z i) :=
    IsNowhereDense.iUnion fun i => (hZc i).isNowhereDense_iff.mpr (hZe i)
  exact (interior_mono subset_closure).trans_eq hND

/-- A coordinate slab is open. -/
theorem isOpen_coordBall {n : ℕ} (j : Fin n) (c r : ℝ) :
    IsOpen {z : Fin n → ℝ | |z j - c| < r} := by
  have h : {z : Fin n → ℝ | |z j - c| < r} =
      (fun z : Fin n → ℝ => z j - c) ⁻¹' Set.Ioo (-r) r := by
    ext z; simp [abs_lt]
  rw [h]
  exact isOpen_Ioo.preimage ((continuous_apply j).sub continuous_const)

/-- Rolle's theorem for the fibre polynomial `s ↦ P (u, s)`. -/
theorem pderiv_eq_zero_of_two_roots {k : ℕ} (P : MvPolynomial (Fin (k + 1)) ℝ) (u : Fin k → ℝ)
    {a b : ℝ} (hab : a < b) (ha : MvPolynomial.eval (Fin.snoc u a) P = 0)
    (hb : MvPolynomial.eval (Fin.snoc u b) P = 0) :
    ∃ c ∈ Set.Ioo a b,
      MvPolynomial.eval (Fin.snoc u c) (MvPolynomial.pderiv (Fin.last k) P) = 0 := by
  set f : ℝ → ℝ := fun s => MvPolynomial.eval (Fin.snoc u s) P
  have hderiv : ∀ s : ℝ, HasDerivAt f
      (MvPolynomial.eval (Fin.snoc u s) (MvPolynomial.pderiv (Fin.last k) P)) s :=
    fun s => Work.WilkiesI.hasDerivAt_eval_snoc P u s
  have hcont : Continuous f := continuous_iff_continuousAt.mpr fun s => (hderiv s).continuousAt
  have hf0 : f a = f b := by simp only [f]; rw [ha, hb]
  obtain ⟨c, hc, hc0⟩ := exists_deriv_eq_zero hab hcont.continuousOn hf0
  exact ⟨c, hc, by rw [← (hderiv c).deriv]; exact hc0⟩

/-- **The bad parameter set of a chart has empty interior.**

Let `κ` be a cell of `ℝⁿ` charted over the coordinate projection `e : Fin d ↪ Fin n`: `κ` is the
graph of a continuous section `ψ` of that projection over the *open* set `U = ProjE e κ`, and
`V ⊇ κ` is semialgebraic of dimension `≤ d`.  Then the set of parameters `u ∈ U` whose graph point
`ψ u` is a limit point of `V \ κ` has empty interior.

`DimLE V d` and `Omega.semialg_subset_intersection_zeroLocus` produce, for every extra coordinate
`j ∉ range e`, a nonzero fibre polynomial `Qⱼ` vanishing on `V`; `squarefree_excision_snoc`
replaces it by `Gⱼ`, with the same roots off the non-vanishing locus `{lⱼ ≠ 0}`, all of them
simple.  If `u` has `lⱼ u ≠ 0` for all `j` and `ψ u` is a limit point of `V \ κ`, take `y ∈ V ∖ κ`
close to `ψ u` and let `j` be an extra coordinate where `y` differs from `ψ (y ∘ e)`: then
`y j` and `ψ (y ∘ e) j` are two distinct roots of the fibre `Gⱼ (y ∘ e, ·)`, so Rolle gives a
parameter `t` strictly between them with a vanishing `Y`-derivative; letting `y → ψ u` shows that
`(u, ψ u j)` is a *multiple* root of `Gⱼ (u, ·)`.  But `Work.WilkiesI.LocalGraphOfPderiv` shows
that the root of `Gⱼ` near `(u, ψ u j)` is unique, so `y j = ψ (y ∘ e) j`; as this holds for every
extra `j` (and the coordinates in `range e` agree by construction), `y = ψ (y ∘ e) ∈ κ`, a
contradiction.  Hence the bad set lies in the finite union of the zero sets of the `lⱼ`, which is
closed with empty interior. -/
theorem badParams_interior_empty {n d : ℕ} (e : Fin d ↪ Fin n)
    {U : Set (Fin d → ℝ)} {ψ : (Fin d → ℝ) → (Fin n → ℝ)} {V κ : Set (Fin n → ℝ)}
    (hVsem : WilkiesConjecture.IsSemialgebraic V) (hVdim : WilkiesDesign.DimLE V d)
    (hUo : IsOpen U) (hψc : ContinuousOn ψ U) (hψsec : ∀ u ∈ U, ψ u ∘ e = u)
    (hψim : ψ '' U = κ) (hκV : κ ⊆ V) :
    interior {u : Fin d → ℝ | u ∈ U ∧ ψ u ∈ closure (V \ κ)} = ∅ := by
  classical
  obtain ⟨Q, hQne, hQzero⟩ := Omega.semialg_subset_intersection_zeroLocus hVsem hVdim
  let Qj : {j : Fin n // j ∉ Set.range e} → MvPolynomial (Fin (d + 1)) ℝ :=
    fun j => Q (extEmb e j.1 j.2)
  have hQjne : ∀ j, Qj j ≠ 0 := fun j => hQne _
  have hQjzero : ∀ (j : {j : Fin n // j ∉ Set.range e}) (y : Fin n → ℝ), y ∈ V →
      MvPolynomial.eval (Fin.snoc (y ∘ e) (y j.1)) (Qj j) = 0 := by
    intro j y hy
    rw [← eval_extEmb e j.2 y]
    exact hQzero y hy _
  choose G l hl hsq using fun j => squarefree_excision_snoc (Qj j) (hQjne j)
  have hkey : ∀ u : Fin d → ℝ, u ∈ U →
      (∀ j : {j : Fin n // j ∉ Set.range e}, MvPolynomial.eval u (l j) ≠ 0) →
      ψ u ∈ closure (V \ κ) → False := by
    intro u huU hlu hucl
    have hψuV : ψ u ∈ V := hκV (hψim ▸ ⟨u, huU, rfl⟩)
    have hQju : ∀ j, MvPolynomial.eval (Fin.snoc u (ψ u j.1)) (Qj j) = 0 := by
      intro j
      have h := hQjzero j (ψ u) hψuV
      rwa [hψsec u huU] at h
    have hroot0 : ∀ j, MvPolynomial.eval (Fin.snoc u (ψ u j.1)) (G j) = 0 := fun j =>
      ((hsq j u (hlu j)).1 (ψ u j.1)).mpr (hQju j)
    have hgrad0 : ∀ j, MvPolynomial.eval (Fin.snoc u (ψ u j.1))
        (MvPolynomial.pderiv (Fin.last d) (G j)) ≠ 0 := fun j =>
      (hsq j u (hlu j)).2 _ (hroot0 j)
    choose Uj gj δj hδj hUjo hUjsub hgjcont hgjbase hgjgraph using fun j =>
      Work.WilkiesI.LocalGraphOfPderiv (G j) (Fin.snoc u (ψ u j.1)) (hroot0 j) (hgrad0 j)
    let W : Set (Fin d → ℝ) := U ∩ (⋂ j : {j : Fin n // j ∉ Set.range e},
          {w : Fin d → ℝ | MvPolynomial.eval w (l j) ≠ 0}) ∩
        (⋂ j : {j : Fin n // j ∉ Set.range e}, ψ ⁻¹' boxAround (ψ u) (δj j)) ∩
        (⋂ j : {j : Fin n // j ∉ Set.range e}, boxAround u (δj j))
    have hW : W ∈ 𝓝 u := by
      refine Filter.inter_mem (Filter.inter_mem (Filter.inter_mem (hUo.mem_nhds huU) ?_) ?_) ?_
      · refine Filter.iInter_mem.mpr fun j => ?_
        have hcont : Continuous fun w : Fin d → ℝ => MvPolynomial.eval w (l j) :=
          MvPolynomial.continuous_eval (l j)
        have hclosed : IsClosed {w : Fin d → ℝ | MvPolynomial.eval w (l j) = 0} :=
          isClosed_eq hcont continuous_const
        refine hclosed.isOpen_compl.mem_nhds ?_
        simpa using hlu j
      · refine Filter.iInter_mem.mpr fun j => ?_
        exact (hψc.continuousAt (hUo.mem_nhds huU)).preimage_mem_nhds
          ((isOpen_boxAround (ψ u) (δj j)).mem_nhds (mem_boxAround.mpr fun i => by
            rw [sub_self, abs_zero]; exact hδj j))
      · refine Filter.iInter_mem.mpr fun j => ?_
        exact (isOpen_boxAround u (δj j)).mem_nhds (mem_boxAround.mpr fun i => by
          rw [sub_self, abs_zero]; exact hδj j)
    have hN : ((⋂ j : {j : Fin n // j ∉ Set.range e},
        {z : Fin n → ℝ | |z j.1 - ψ u j.1| < δj j}) ∩
        {z : Fin n → ℝ | z ∘ e ∈ W}) ∈ 𝓝 (ψ u) := by
      refine Filter.inter_mem ?_ ?_
      · refine Filter.iInter_mem.mpr fun j =>
          (isOpen_coordBall j.1 (ψ u j.1) (δj j)).mem_nhds ?_
        simpa using hδj j
      · have hproj : Continuous fun z : Fin n → ℝ => z ∘ e :=
          continuous_pi fun i => continuous_apply (e i)
        refine hproj.continuousAt.preimage_mem_nhds ?_
        show W ∈ 𝓝 (ψ u ∘ e)
        rw [hψsec u huU]
        exact hW
    obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp hN
    obtain ⟨y, hyVκ, hydist⟩ := Metric.mem_closure_iff.mp hucl η hη
    have hyN : y ∈ (⋂ j : {j : Fin n // j ∉ Set.range e},
        {z : Fin n → ℝ | |z j.1 - ψ u j.1| < δj j}) ∩ {z : Fin n → ℝ | z ∘ e ∈ W} :=
      hball (Metric.mem_ball.mpr (by rw [dist_comm]; exact hydist))
    have hycoord : ∀ j : {j : Fin n // j ∉ Set.range e}, |y j.1 - ψ u j.1| < δj j :=
      fun j => Set.mem_iInter.mp hyN.1 j
    have hyW : y ∘ e ∈ W := hyN.2
    obtain ⟨⟨⟨hvU, hvl⟩, hvψ⟩, hvb⟩ := hyW
    let v : Fin d → ℝ := y ∘ e
    have hψvV : ψ v ∈ V := hκV (hψim ▸ ⟨v, hvU, rfl⟩)
    have hfinal : ∀ j : {j : Fin n // j ∉ Set.range e}, y j.1 = ψ v j.1 := by
      intro j
      have hlne : MvPolynomial.eval v (l j) ≠ 0 := Set.mem_iInter.mp hvl j
      have hQjv : MvPolynomial.eval (Fin.snoc v (ψ v j.1)) (Qj j) = 0 := by
        have h := hQjzero j (ψ v) hψvV
        rwa [hψsec v hvU] at h
      have hboxv : ∀ i : Fin d, |v i - u i| < δj j :=
        fun i => mem_boxAround.mp (Set.mem_iInter.mp hvb j) i
      have hboxψv : ∀ i : Fin (d + 1),
          |(Fin.snoc v (ψ v j.1) : Fin (d + 1) → ℝ) i -
            (Fin.snoc u (ψ u j.1) : Fin (d + 1) → ℝ) i| < δj j := by
        intro i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
        · simpa using hboxv i'
        · simpa using mem_boxAround.mp (Set.mem_iInter.mp hvψ j) j.1
      have hboxy : ∀ i : Fin (d + 1),
          |(Fin.snoc v (y j.1) : Fin (d + 1) → ℝ) i -
            (Fin.snoc u (ψ u j.1) : Fin (d + 1) → ℝ) i| < δj j := by
        intro i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
        · simpa using hboxv i'
        · simpa using hycoord j
      have hx1 : Fin.snoc v (y j.1) ∈
          {x : Fin (d + 1) → ℝ | MvPolynomial.eval x (G j) = 0 ∧
            ∀ i : Fin (d + 1),
              |x i - (Fin.snoc u (ψ u j.1) : Fin (d + 1) → ℝ) i| < δj j} :=
        ⟨((hsq j v hlne).1 (y j.1)).mpr (hQjzero j y hyVκ.1), hboxy⟩
      have hx2 : Fin.snoc v (ψ v j.1) ∈
          {x : Fin (d + 1) → ℝ | MvPolynomial.eval x (G j) = 0 ∧
            ∀ i : Fin (d + 1),
              |x i - (Fin.snoc u (ψ u j.1) : Fin (d + 1) → ℝ) i| < δj j} :=
        ⟨((hsq j v hlne).1 (ψ v j.1)).mpr hQjv, hboxψv⟩
      rw [hgjgraph j] at hx1 hx2
      have h1 : y j.1 = gj j v := by simpa using hx1.2.1
      have h2 : ψ v j.1 = gj j v := by simpa using hx2.2.1
      rw [h1, h2]
    have hyeq : y = ψ v := by
      funext i
      by_cases hi : i ∈ Set.range e
      · obtain ⟨i', rfl⟩ := hi
        have h1 : y (e i') = v i' := rfl
        have h2 : ψ v (e i') = v i' := congrFun (hψsec v hvU) i'
        rw [h1, h2]
      · exact hfinal ⟨i, hi⟩
    have hψvκ : ψ v ∈ κ := hψim ▸ ⟨v, hvU, rfl⟩
    exact hyVκ.2 (hyeq.symm ▸ hψvκ)
  have hsub : {u : Fin d → ℝ | u ∈ U ∧ ψ u ∈ closure (V \ κ)} ⊆
      ⋃ j : {j : Fin n // j ∉ Set.range e}, {u : Fin d → ℝ | MvPolynomial.eval u (l j) = 0} := by
    intro u hu
    obtain ⟨huU, hucl⟩ := hu
    by_contra hcon
    have hcon' : ∀ j : {j : Fin n // j ∉ Set.range e}, MvPolynomial.eval u (l j) ≠ 0 := by
      intro j hj
      exact hcon (Set.mem_iUnion.mpr ⟨j, hj⟩)
    exact hkey u huU hcon' hucl
  have hZ : interior (⋃ j : {j : Fin n // j ∉ Set.range e},
      {u : Fin d → ℝ | MvPolynomial.eval u (l j) = 0}) = ∅ :=
    interior_iUnion_eq_empty (fun j => isClosed_eq (MvPolynomial.continuous_eval (l j))
      continuous_const) (fun j => Omega.interior_zeroLocus_eq_empty (l j) (hl j))
  have h1 : interior {u : Fin d → ℝ | u ∈ U ∧ ψ u ∈ closure (V \ κ)} ⊆
      interior (⋃ j : {j : Fin n // j ∉ Set.range e},
        {u : Fin d → ℝ | MvPolynomial.eval u (l j) = 0}) := interior_mono hsub
  rw [hZ] at h1
  exact Set.subset_empty_iff.mp h1

/-- **The relative frontier of a cell is thin.**  For every `F, n` there are a format `a` and a
two-variable polynomial `pm` such that for every cell `κ ∈ S.Ω F D n` contained in a semialgebraic
`V ∈ S.Ω F Dv n` of dimension `≤ μ`, the relative frontier `κ ∩ closure (V \ κ)` is contained in
an `Ω`-set `W ⊆ κ` of dimension `≤ μ - 1` and degree bounded by `pm (D + Dv, n + 1)`. -/
theorem frontierThin {S : WilkiesDesign.SOMin} (hcd : S.SharpCD) :
    ∀ F n : ℕ, ∃ (a : ℕ) (pm : MvPolynomial (Fin 2) ℕ),
      ∀ (μ D Dv : ℕ) (V κ : Set (Fin n → ℝ)),
        V ∈ S.Ω F Dv n → WilkiesConjecture.IsSemialgebraic V → WilkiesDesign.DimLE V μ →
        κ ∈ S.Ω F D n → WilkiesDesign.IsCell n κ → κ.Nonempty → κ ⊆ V →
        ∃ W : Set (Fin n → ℝ),
          W ∈ S.Ω a (MvPolynomial.eval ![(D + Dv : ℕ), (n + 1 : ℕ)] pm) n ∧ W ⊆ κ ∧
          WilkiesDesign.DimLE W (μ - 1) ∧ κ ∩ closure (V \ κ) ⊆ W := by
  intro F n
  obtain ⟨acl, qcl, hcl⟩ := omega_closure_v2 (S := S) hcd (F + 8) n
  obtain ⟨pm, hpm⟩ := SI.exists_pm_deg_le n qcl
  refine ⟨max (F + 8) acl + 1, pm, ?_⟩
  intro μ D Dv V κ hV hVsem hVdim hκ hcell hne hκV
  have hκ6 : κ ∈ S.Ω (F + 6) D n := Work.WilG5.mem_mono hκ _ _ (by omega) le_rfl
  have hκ7 : κᶜ ∈ S.Ω (F + 7) D n := S.compl hκ6
  have hV7 : V ∈ S.Ω (F + 7) Dv n := Work.WilG5.mem_mono hV _ _ (by omega) le_rfl
  have hdiff : V \ κ ∈ S.Ω (F + 8) (Dv + D) n := by
    have h := Work.WilG0.Omega_inter2_le hV7 hκ7
    simpa [Set.sdiff_eq] using h
  obtain ⟨C, hCmem, hCchar⟩ := hcl (Dv + D) (V \ κ) hdiff
  have hCeq : C = closure (V \ κ) := by
    have h1 : C = closureSet (V \ κ) := by
      ext x
      rw [hCchar]
      rfl
    rw [h1, SI.Book.closureSet_eq_closure]
  have hWmem : κ ∩ C ∈ S.Ω (max (F + 8) acl + 1)
      (MvPolynomial.eval ![(D + Dv : ℕ), (n + 1 : ℕ)] pm) n := by
    refine Work.WilG5.mem_mono
      (Work.WilG0.Omega_inter2_le (Work.WilG5.mem_mono hκ6 _ _ (by omega) le_rfl) hCmem)
      _ _ le_rfl ?_
    rw [show Dv + D = D + Dv from by omega]
    have h := hpm D Dv
    rwa [show Dv + D = D + Dv from by omega] at h
  have hdim : WilkiesDesign.DimLE (κ ∩ closure (V \ κ)) (μ - 1) := by
    obtain ⟨d, hcb⟩ := exists_cellBand_of_isCell hcell
    by_cases hdle : d ≤ μ - 1
    · exact dimLE_of_subset
        (Dim.dimLE_mono (RegAux.cellBand_dimLE (S := S) hcd hcb hκ) hdle)
        Set.inter_subset_left
    · have hdge : μ ≤ d := by omega
      obtain ⟨e₀, Φ₀, hUo₀, hΦ₀c, hΦ₀l, hΦ₀r⟩ := bandChart_of_cellBand hcb
      have hne₀ : (Cell.ProjE e₀ κ).Nonempty := hne.image (fun x => x ∘ e₀)
      have hdμ : d ≤ μ := RegAux.cell_chart_dim_le hκV hVdim e₀ hUo₀ hne₀
      have hd : d = μ := le_antisymm hdμ hdge
      have hcbμ : CellBand n κ μ := hd ▸ hcb
      obtain ⟨e, U, ψ, A, L, hUo, hUne, hψc, -, hψim, hψsec, hΓ⟩ :=
        cell_par_exists (S := S) hcbμ hne (F + 2) D
          (Work.WilG5.mem_mono hκ _ _ (by omega) le_rfl)
      have hempty : interior {u : Fin μ → ℝ | u ∈ U ∧ ψ u ∈ closure (V \ κ)} = ∅ :=
        badParams_interior_empty (e := e) hVsem hVdim hUo hψc hψsec hψim hκV
      have hkey : WilkiesDesign.DimLE
          (ψ '' {u : Fin μ → ℝ | u ∈ U ∧ ψ u ∈ closure (V \ κ)}) (μ - 1) :=
        SI.dimLE_frontier_image (S := S) hcd e hΓ (by rw [← hCeq]; exact hCmem) hψsec hempty
      have himg : ψ '' {u : Fin μ → ℝ | u ∈ U ∧ ψ u ∈ closure (V \ κ)} =
          κ ∩ closure (V \ κ) := by
        refine Set.Subset.antisymm ?_ ?_
        · rintro y ⟨u, ⟨huU, huC⟩, rfl⟩
          exact ⟨hψim ▸ ⟨u, huU, rfl⟩, huC⟩
        · rintro y ⟨hyκ, hyC⟩
          rw [← hψim] at hyκ
          obtain ⟨u, huU, rfl⟩ := hyκ
          exact ⟨u, ⟨huU, hyC⟩, rfl⟩
      rwa [himg] at hkey
  exact ⟨κ ∩ closure (V \ κ), by rw [← hCeq]; exact hWmem, Set.inter_subset_left, hdim,
    subset_rfl⟩

end RPC

end Work.WilkiesH.Strat
