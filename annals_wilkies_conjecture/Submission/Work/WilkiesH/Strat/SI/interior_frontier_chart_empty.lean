import Mathlib
import Submission.Work.WilkiesH.Omega.semialg_subset_intersection_zeroLocus
import Submission.Work.WilkiesH.Omega.interior_zeroLocus_eq_empty
import Submission.Work.WilkiesH.Strat.SingDefs
import Submission.Work.WilkiesH.Strat.BadCell
import Submission.Work.WilkiesI.LocalGraphOfPderiv
import Submission.Work.WilkiesH.Strat.SI.exists_pderiv_eq_zero_of_two_roots

/-!
# The bad parameters of a chart have empty interior

For a semialgebraic set `V ⊆ ℝⁿ` of dimension `≤ d` and a chart `ψ : U → ℝⁿ` over a coordinate
embedding `e : Fin d ↪ Fin n` (open `U`, `ψ u ∘ e = u`, `ψ '' U = κ ⊆ V`), the set of parameters
`u ∈ U` whose chart point `ψ u` is a limit point of `V \ κ` has empty interior.

The argument is a *branch* argument (not an iteration of Rolle's theorem).
`Omega.semialg_subset_intersection_zeroLocus` supplies, for every extra coordinate
`j ∉ range e`, a nonzero fibre polynomial `Qⱼ ∈ ℝ[x_1,…,x_d,Y]` vanishing on the projection of `V`
to the coordinates `range e ∪ {j}`; `squarefree_excision_snoc` replaces it by a polynomial `Gⱼ`
with the same roots off the non-vanishing locus of a nonzero `lⱼ ∈ ℝ[x_1,…,x_d]`, all of them
simple.  If `u` is a bad parameter at which every `lⱼ` is nonzero, then near `(u, ψ u j)` the zero
set of `Gⱼ` is the graph of a continuous function (`Work.WilkiesI.LocalGraphOfPderiv`), and both
`y j` and `ψ (y ∘ e) j` — for `y ∈ V \ κ` close to `ψ u` — are points of that zero set inside the
box, so they coincide; doing this for every extra coordinate (the remaining coordinates agree by
construction) gives `y = ψ (y ∘ e) ∈ κ`, contradicting `y ∈ V \ κ`.  Hence the bad parameters all
lie in the finite union of the zero sets of the `lⱼ`, a finite union of closed sets with empty
interior.

(This is the same line of proof as `Work.WilkiesH.Strat.RPC.badParams_interior_empty` in
`Strat/rpc_cell_frontier.lean`, which derives it from the same three inputs.)
-/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical

namespace Work.WilkiesH.Strat.SI

open WilkiesDesign WilkiesConjecture
open Work.WilkiesH
open Filter
open scoped Topology

/-- A finite union of closed sets with empty interior has empty interior. -/
theorem interior_iUnion_of_isClosed_eq_empty' {α ι : Type*} [TopologicalSpace α] [Finite ι]
    {Z : ι → Set α} (hZc : ∀ i, IsClosed (Z i)) (hZe : ∀ i, interior (Z i) = ∅) :
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

theorem interior_frontier_chart_empty {n d : ℕ} (e : Fin d ↪ Fin n)
    {U : Set (Fin d → ℝ)} {ψ : (Fin d → ℝ) → (Fin n → ℝ)} {V κ : Set (Fin n → ℝ)}
    (hVsem : WilkiesConjecture.IsSemialgebraic V)
    (hVdim : WilkiesDesign.DimLE V d)
    (hUo : IsOpen U) (hψc : ContinuousOn ψ U) (hψsec : ∀ u ∈ U, ψ u ∘ e = u)
    (hψim : ψ '' U = κ) (hκV : κ ⊆ V) :
    interior {u : Fin d → ℝ | u ∈ U ∧ ψ u ∈ closure (V \ κ)} = ∅ := by
  classical
  -- the certificates: a nonzero fibre polynomial for every extra coordinate
  obtain ⟨Q, hQne, hQzero⟩ :=
    Work.WilkiesH.Omega.semialg_subset_intersection_zeroLocus (n := n) (μ := d) hVsem hVdim
  let J := {j : Fin n // j ∉ Set.range e}
  let Qj : J → MvPolynomial (Fin (d + 1)) ℝ := fun j => Q (Work.WilkiesH.Strat.extEmb e j.1 j.2)
  have hQjne : ∀ j : J, Qj j ≠ 0 := fun j => hQne _
  have hQjzero : ∀ (j : J) (y : Fin n → ℝ), y ∈ V →
      MvPolynomial.eval (Fin.snoc (y ∘ e) (y j.1)) (Qj j) = 0 := by
    intro j y hy
    rw [← Work.WilkiesH.Strat.eval_extEmb e j.2 y]
    exact hQzero y hy _
  -- squarefree excision of each certificate
  choose G l hl hsq using fun j : J => Work.WilkiesH.Strat.squarefree_excision_snoc (Qj j) (hQjne j)
  -- the key pointwise statement
  have hkey : ∀ u : Fin d → ℝ, u ∈ U →
      (∀ j : J, MvPolynomial.eval u (l j) ≠ 0) → ψ u ∈ closure (V \ κ) → False := by
    intro u huU hlu hucl
    have hψuV : ψ u ∈ V := hκV (by rw [← hψim]; exact ⟨u, huU, rfl⟩)
    have hQju : ∀ j : J, MvPolynomial.eval (Fin.snoc u (ψ u j.1)) (Qj j) = 0 := by
      intro j
      have h := hQjzero j (ψ u) hψuV
      rwa [hψsec u huU] at h
    have hroot0 : ∀ j : J, MvPolynomial.eval (Fin.snoc u (ψ u j.1)) (G j) = 0 := fun j =>
      ((hsq j u (hlu j)).1 (ψ u j.1)).mpr (hQju j)
    have hgrad0 : ∀ j : J, MvPolynomial.eval (Fin.snoc u (ψ u j.1))
        (MvPolynomial.pderiv (Fin.last d) (G j)) ≠ 0 := fun j =>
      (hsq j u (hlu j)).2 _ (hroot0 j)
    -- the zero set of `G j` near `(u, ψ u j)` is the graph of a function
    choose Uj gj δj hδj hUjo hUjsub hgjcont hgjbase hgjgraph using fun j : J =>
      Work.WilkiesI.LocalGraphOfPderiv (G j) (Fin.snoc u (ψ u j.1)) (hroot0 j) (hgrad0 j)
    -- a neighbourhood of `u` on which all the data is nondegenerate
    let W : Set (Fin d → ℝ) :=
      U ∩ (⋂ j : J, {w : Fin d → ℝ | MvPolynomial.eval w (l j) ≠ 0}) ∩
        (⋂ j : J, ψ ⁻¹' boxAround (ψ u) (δj j)) ∩
        (⋂ j : J, boxAround u (δj j))
    have hW : W ∈ 𝓝 u := by
      refine Filter.inter_mem (Filter.inter_mem (Filter.inter_mem (hUo.mem_nhds huU) ?_) ?_) ?_
      · refine Filter.iInter_mem.mpr fun j => ?_
        exact (isClosed_eq (MvPolynomial.continuous_eval (l j)) continuous_const).isOpen_compl.mem_nhds
          (by simpa using hlu j)
      · refine Filter.iInter_mem.mpr fun j => ?_
        refine (hψc.continuousAt (hUo.mem_nhds huU)).preimage_mem_nhds
          ((isOpen_boxAround (ψ u) (δj j)).mem_nhds (mem_boxAround.mpr fun i => by
            rw [sub_self, abs_zero]; exact hδj j))
      · refine Filter.iInter_mem.mpr fun j => ?_
        exact (isOpen_boxAround u (δj j)).mem_nhds (mem_boxAround.mpr fun i => by
          rw [sub_self, abs_zero]; exact hδj j)
    -- a neighbourhood of `ψ u` inside which the extra coordinates stay in the graphs
    have hN : ((⋂ j : J, {z : Fin n → ℝ | |z j.1 - ψ u j.1| < δj j}) ∩
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
    have hyN : y ∈ (⋂ j : J, {z : Fin n → ℝ | |z j.1 - ψ u j.1| < δj j}) ∩
        {z : Fin n → ℝ | z ∘ e ∈ W} :=
      hball (Metric.mem_ball.mpr (by rw [dist_comm]; exact hydist))
    have hycoord : ∀ j : J, |y j.1 - ψ u j.1| < δj j :=
      fun j => Set.mem_iInter.mp hyN.1 j
    have hyW : y ∘ e ∈ W := hyN.2
    obtain ⟨⟨⟨hvU, hvl⟩, hvψ⟩, hvb⟩ := hyW
    let v : Fin d → ℝ := y ∘ e
    have hvU' : v ∈ U := hvU
    have hψvV : ψ v ∈ V := hκV (by rw [← hψim]; exact ⟨v, hvU', rfl⟩)
    -- both `y j` and `ψ v j` lie in the graph of `gj j`
    have hfinal : ∀ j : J, y j.1 = ψ v j.1 := by
      intro j
      have hlne : MvPolynomial.eval v (l j) ≠ 0 := Set.mem_iInter.mp hvl j
      have hQjv : MvPolynomial.eval (Fin.snoc v (ψ v j.1)) (Qj j) = 0 := by
        have h := hQjzero j (ψ v) hψvV
        rwa [hψsec v hvU'] at h
      have hQjy : MvPolynomial.eval (Fin.snoc v (y j.1)) (Qj j) = 0 := hQjzero j y hyVκ.1
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
        ⟨((hsq j v hlne).1 (y j.1)).mpr hQjy, hboxy⟩
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
        have h2 : ψ v (e i') = v i' := congrFun (hψsec v hvU') i'
        rw [h1, h2]
      · exact hfinal ⟨i, hi⟩
    have hψvκ : ψ v ∈ κ := hψim ▸ ⟨v, hvU', rfl⟩
    exact hyVκ.2 (hyeq.symm ▸ hψvκ)
  -- the bad parameter set is contained in the zero sets of the `l j`
  have hsub : {u : Fin d → ℝ | u ∈ U ∧ ψ u ∈ closure (V \ κ)} ⊆
      ⋃ j : J, {u : Fin d → ℝ | MvPolynomial.eval u (l j) = 0} := by
    intro u hu
    obtain ⟨huU, hucl⟩ := hu
    by_contra hcon
    have hcon' : ∀ j : J, MvPolynomial.eval u (l j) ≠ 0 := by
      intro j hj
      exact hcon (Set.mem_iUnion.mpr ⟨j, hj⟩)
    exact hkey u huU hcon' hucl
  have hZ : interior (⋃ j : J, {u : Fin d → ℝ | MvPolynomial.eval u (l j) = 0}) = ∅ :=
    interior_iUnion_of_isClosed_eq_empty'
      (fun j => isClosed_eq (MvPolynomial.continuous_eval (l j)) continuous_const)
      (fun j => Work.WilkiesH.Omega.interior_zeroLocus_eq_empty (l j) (hl j))
  exact Set.subset_empty_iff.mp ((interior_mono hsub).trans_eq hZ)

end Work.WilkiesH.Strat.SI
