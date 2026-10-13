import Mathlib
import Submission.Work.WilkiesH.Basic
import Submission.Work.WilkiesH.Mfd.Defs
import Submission.Work.WilkiesH.Strat.Defs
import Submission.Work.WilkiesH.Strat.CellBand
import Submission.Work.WilkiesH.Strat.cell_par_exists
import Submission.Work.WilkiesH.Strat.bandChart_of_cellBand
import Submission.Work.WilkiesH.Strat.rp_aux
import Submission.Work.WilkiesH.Strat.rft.Master
import Submission.Work.WilkiesH.Strat.omega_closure_v2
import Submission.Work.WilkiesH.Strat.poly_bound_rpc
import Submission.Work.WilkiesH.Strat.SI.polybook
import Submission.Work.WilkiesH.Strat.SI.interior_frontier_chart_empty
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG0.API
import Submission.Work.WilG0.Omega_inter2_le

/-!
# The relative frontier of an `Ω`-cell is thin

`Work.WilkiesH.Strat.SI.frontierThin` is the geometric input of the regular-part cover
(`Work.WilkiesH.Strat.SI.regularPartCover`): for an `Ω`-cell `κ ⊆ V` contained in a
semialgebraic `V` of dimension `≤ μ`, the relative frontier `κ ∩ closure (V \ κ)` is covered by
an `Ω`-set `W ⊆ κ` of dimension `≤ μ - 1`, with format and degree bounded in terms of
`(D + D_v, n + 1)`.

The proof takes `W := κ ∩ closure (V \ κ)` itself (an `Ω`-set, because `κ ∈ Ω` and the closure of
the `Ω`-set `V \ κ` is `Ω`, `omega_closure_v2`).  The dimension bound is the content: with `d` the
number of band steps of `κ` (`CellBand`), one has `d ≤ μ`
(`RegAux.cell_chart_dim_le` applied to the band chart of `κ`), so

* either `d ≤ μ - 1`, and then `DimLE κ d` (`RegAux.cellBand_dimLE`) gives the bound by
  monotonicity;
* or `d = μ`, and then the frontier is thin because in the band chart `ψ : U ≅ κ` over the `d`
  coordinates selected by `e : Fin d ↪ Fin n`, the chart image
  `B = {u ∈ U | ψ u ∈ closure (V \ κ)}` has empty interior (`SI.interior_frontier_chart_empty`:
  Rolle's theorem on the fibre polynomials of the semialgebraic `V`), so the `Ω`-graph dimension
  theorem `dimLE_of_graphOver` applied to the lifted graph
  `Γ ∩ {z | (z ∘ Fin.natAdd d) ∈ closure (V \ κ)}` gives `DimLE (ψ '' B) (d - 1)`.
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkiesH.Strat.SI

open WilkiesDesign WilkiesConjecture
open Work.WilkiesH

/-! ## 1. Polynomial bookkeeping -/

/-- There is a two-variable natural polynomial `pm` with
`D + q.eval (D_v + D) ≤ pm (D + D_v, n + 1)` for all `D, D_v`. -/
theorem exists_pm_deg_le (n : ℕ) (q : Polynomial ℕ) :
    ∃ pm : MvPolynomial (Fin 2) ℕ, ∀ D Dv : ℕ,
      D + q.eval (Dv + D) ≤ MvPolynomial.eval ![(D + Dv : ℕ), (n + 1 : ℕ)] pm := by
  refine ⟨MvPolynomial.C (q.eval 1) * (MvPolynomial.X 0 + MvPolynomial.C 1) ^ q.natDegree +
      MvPolynomial.X 0, fun D Dv => ?_⟩
  have hX : MvPolynomial.eval ![(D + Dv : ℕ), (n + 1 : ℕ)]
      (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℕ) = D + Dv := by simp
  have hpow : MvPolynomial.eval ![(D + Dv : ℕ), (n + 1 : ℕ)]
      ((MvPolynomial.X 0 + MvPolynomial.C 1 : MvPolynomial (Fin 2) ℕ) ^ q.natDegree)
      = (D + Dv + 1) ^ q.natDegree := by
    rw [MvPolynomial.eval_pow, MvPolynomial.eval_add, hX, MvPolynomial.eval_C]
  have hval : MvPolynomial.eval ![(D + Dv : ℕ), (n + 1 : ℕ)]
      (MvPolynomial.C (q.eval 1) * (MvPolynomial.X 0 + MvPolynomial.C 1) ^ q.natDegree +
        MvPolynomial.X 0) = q.eval 1 * (D + Dv + 1) ^ q.natDegree + (D + Dv) := by
    rw [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C, hpow, hX]
  rw [hval]
  have h1 : q.eval (Dv + D) ≤ q.eval 1 * (D + Dv + 1) ^ q.natDegree := by
    have h := Work.WilkiesH.Strat.poly_eval_le_eval_one_rpc q (Dv + D)
    rwa [show Dv + D + 1 = D + Dv + 1 from by omega] at h
  calc D + q.eval (Dv + D) ≤ D + q.eval 1 * (D + Dv + 1) ^ q.natDegree :=
        Nat.add_le_add_left h1 D
    _ = q.eval 1 * (D + Dv + 1) ^ q.natDegree + D := by ring
    _ ≤ q.eval 1 * (D + Dv + 1) ^ q.natDegree + (D + Dv) :=
        Nat.add_le_add_left (Nat.le_add_right D Dv) _

/-! ## 2. The chart-frontier dimension transfer -/

/-- **The chart-frontier dimension transfer.**  If `ψ : U → ℝⁿ` is a section of the coordinate
projection along `e : Fin μ ↪ Fin n` (`ψ u ∘ e = u`), the lifted graph `Γ = {(u, ψ u)}` is an
`Ω`-set, and `B = {u ∈ U | ψ u ∈ C}` has empty interior in the chart coordinates, then the image
`ψ '' B` is `(μ-1)`-thin: the lift `Γ ∩ {z | z ∘ Fin.natAdd μ ∈ C}` is a graph over its first `μ`
coordinates whose source is thin, and `dimLE_of_graphOver` applies. -/
theorem dimLE_frontier_image {S : WilkiesDesign.SOMin} (hcd : S.SharpCD)
    {n μ A L F' D' : ℕ} (e : Fin μ ↪ Fin n)
    {U : Set (Fin μ → ℝ)} {ψ : (Fin μ → ℝ) → (Fin n → ℝ)} {C : Set (Fin n → ℝ)}
    (hΓ : {z : Fin (μ + n) → ℝ |
        (fun i : Fin μ => z (Fin.castAdd n i)) ∈ U ∧
        (fun j : Fin n => z (Fin.natAdd μ j)) = ψ (fun i : Fin μ => z (Fin.castAdd n i))}
        ∈ S.Ω A L (μ + n))
    (hC : C ∈ S.Ω F' D' n)
    (hsec : ∀ u ∈ U, ψ u ∘ e = u)
    (hempty : interior {u : Fin μ → ℝ | u ∈ U ∧ ψ u ∈ C} = ∅) :
    WilkiesDesign.DimLE (ψ '' {u : Fin μ → ℝ | u ∈ U ∧ ψ u ∈ C}) (μ - 1) := by
  set Z : Set (Fin (μ + n) → ℝ) :=
    {z : Fin (μ + n) → ℝ |
        (fun i : Fin μ => z (Fin.castAdd n i)) ∈ U ∧
        (fun j : Fin n => z (Fin.natAdd μ j)) =
          ψ (fun i : Fin μ => z (Fin.castAdd n i))} ∩
      {z : Fin (μ + n) → ℝ | (fun j : Fin n => z (Fin.natAdd μ j)) ∈ C} with hZdef
  -- the coordinate projections of `Fin.append`
  have hAL : ∀ (a : Fin μ → ℝ) (b : Fin n → ℝ),
      (fun i : Fin μ => (Fin.append a b : Fin (μ + n) → ℝ) (Fin.castAdd n i)) = a :=
    fun a b => funext fun i => Fin.append_left a b i
  have hAR : ∀ (a : Fin μ → ℝ) (b : Fin n → ℝ),
      (fun j : Fin n => (Fin.append a b : Fin (μ + n) → ℝ) (Fin.natAdd μ j)) = b :=
    fun a b => funext fun j => Fin.append_right a b j
  -- membership in `Z`
  have hmemZ : ∀ z : Fin (μ + n) → ℝ,
      z ∈ Z ↔ (fun i : Fin μ => z (Fin.castAdd n i)) ∈ U ∧
        (fun j : Fin n => z (Fin.natAdd μ j)) = ψ (fun i : Fin μ => z (Fin.castAdd n i)) ∧
        (fun j : Fin n => z (Fin.natAdd μ j)) ∈ C := by
    intro z
    rw [hZdef]
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    tauto
  have hZmem0 : Z ∈ S.Ω (max A (F' + 64 * ((μ + n) + n) + 64) + 1)
      (L + (D' + 32 * ((μ + n) + n) + 32)) (μ + n) := by
    have h1 : Work.WilG5.coordPre (Fin.natAdd μ) C ∈
        S.Ω (F' + 64 * ((μ + n) + n) + 64) (D' + 32 * ((μ + n) + n) + 32) (μ + n) :=
      Work.WilG5.coordPre_mem hC
    have h2 : {z : Fin (μ + n) → ℝ | (fun j : Fin n => z (Fin.natAdd μ j)) ∈ C} =
        Work.WilG5.coordPre (Fin.natAdd μ) C := rfl
    have h3 : ({z : Fin (μ + n) → ℝ |
        (fun i : Fin μ => z (Fin.castAdd n i)) ∈ U ∧
        (fun j : Fin n => z (Fin.natAdd μ j)) =
          ψ (fun i : Fin μ => z (Fin.castAdd n i))} :
          Set (Fin (μ + n) → ℝ)) ∈ S.Ω A L (μ + n) := hΓ
    rw [hZdef, h2]
    exact Work.WilG0.Omega_inter2_le h3 h1
  have hgr : Work.WilkiesH.Strat.GraphOver μ Z := by
    intro z hz z' hz' hcast
    have hzΓ := (hmemZ z).mp hz
    have hz'Γ := (hmemZ z').mp hz'
    refine Work.WilkiesH.Strat.eq_of_castAdd_natAdd (fun i => hcast i) (fun j => ?_)
    rw [congrFun hzΓ.2.1 j, congrFun hz'Γ.2.1 j]
    exact congrArg (fun w : Fin μ → ℝ => ψ w j) (funext fun i => hcast i)
  have hproj : Work.WilG5.projN (n := μ) n Z = {u : Fin μ → ℝ | u ∈ U ∧ ψ u ∈ C} := by
    ext u
    rw [Work.WilkiesH.Strat.mem_projN']
    constructor
    · rintro ⟨y, hy⟩
      have hy' := (hmemZ (Fin.append u y)).mp hy
      refine ⟨?_, ?_⟩
      · rw [← hAL u y]; exact hy'.1
      · have h2 : (fun j : Fin n => (Fin.append u y : Fin (μ + n) → ℝ) (Fin.natAdd μ j)) ∈ C :=
          hy'.2.2
        have h3 : y ∈ C := by rwa [hAR u y] at h2
        have h4 : ψ u = y := by rw [← hAL u y, ← hy'.2.1, hAR u y]
        rw [h4]; exact h3
    · rintro ⟨huU, huC⟩
      refine ⟨ψ u, (hmemZ (Fin.append u (ψ u))).mpr ⟨?_, ?_, ?_⟩⟩
      · rw [hAL u (ψ u)]; exact huU
      · rw [hAR u (ψ u), hAL u (ψ u)]
      · rw [hAR u (ψ u)]; exact huC
  have hlast : Work.WilG5.lastN (n := μ) n Z = ψ '' {u : Fin μ → ℝ | u ∈ U ∧ ψ u ∈ C} := by
    ext y
    rw [Work.WilkiesH.Strat.mem_lastN']
    constructor
    · rintro ⟨x, hx⟩
      have hx' := (hmemZ (Fin.append x y)).mp hx
      have h1 : y ∈ C := by
        have h : (fun j : Fin n => (Fin.append x y : Fin (μ + n) → ℝ) (Fin.natAdd μ j)) ∈ C :=
          hx'.2.2
        rwa [hAR x y] at h
      have h2 : ψ x = y := by rw [← hAL x y, ← hx'.2.1, hAR x y]
      exact ⟨x, ⟨by rw [← hAL x y]; exact hx'.1, by rw [h2]; exact h1⟩, h2⟩
    · rintro ⟨u, ⟨huU, huC⟩, rfl⟩
      refine ⟨u, (hmemZ (Fin.append u (ψ u))).mpr ⟨?_, ?_, ?_⟩⟩
      · rw [hAL u (ψ u)]; exact huU
      · rw [hAR u (ψ u), hAL u (ψ u)]
      · rw [hAR u (ψ u)]; exact huC
  have hdim := (Work.WilkiesH.Strat.dimLE_of_graphOver (S := S) hcd μ n _ _ Z hZmem0 hgr).2
    (by rw [hproj]; exact hempty)
  rwa [hlast] at hdim

/-! ## 3. The relative frontier of a cell is thin -/

theorem frontierThin {S : WilkiesDesign.SOMin} (hcd : S.SharpCD) :
    ∀ F n : ℕ, ∃ (a : ℕ) (pm : MvPolynomial (Fin 2) ℕ),
      ∀ (μ D Dv : ℕ) (V κ : Set (Fin n → ℝ)),
        V ∈ S.Ω F Dv n → WilkiesConjecture.IsSemialgebraic V → WilkiesDesign.DimLE V μ →
        κ ∈ S.Ω F D n → WilkiesDesign.IsCell n κ → κ.Nonempty → κ ⊆ V →
        ∃ W : Set (Fin n → ℝ),
          W ∈ S.Ω a (MvPolynomial.eval ![(D + Dv : ℕ), (n + 1 : ℕ)] pm) n ∧ W ⊆ κ ∧
          WilkiesDesign.DimLE W (μ - 1) ∧ κ ∩ closure (V \ κ) ⊆ W := by
  intro F n
  obtain ⟨acl, qcl, hcl⟩ := Work.WilkiesH.Strat.omega_closure_v2 (S := S) hcd (F + 8) n
  obtain ⟨pm, hpm⟩ := exists_pm_deg_le n qcl
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
    have h1 : C = Work.WilkiesH.Strat.closureSet (V \ κ) := by
      ext x
      rw [hCchar]
      rfl
    rw [h1, Work.WilkiesH.Strat.SI.Book.closureSet_eq_closure]
  have hWmem : κ ∩ C ∈ S.Ω (max (F + 8) acl + 1)
      (MvPolynomial.eval ![(D + Dv : ℕ), (n + 1 : ℕ)] pm) n := by
    refine Work.WilG5.mem_mono
      (Work.WilG0.Omega_inter2_le (Work.WilG5.mem_mono hκ6 _ _ (by omega) le_rfl) hCmem)
      _ _ le_rfl ?_
    rw [show Dv + D = D + Dv from by omega]
    have h := hpm D Dv
    rwa [show Dv + D = D + Dv from by omega] at h
  have hdim : WilkiesDesign.DimLE (κ ∩ closure (V \ κ)) (μ - 1) := by
    obtain ⟨d, hcb⟩ := Work.WilkiesH.Strat.exists_cellBand_of_isCell hcell
    by_cases hdle : d ≤ μ - 1
    · exact Work.WilkiesH.dimLE_of_subset
        (Work.WilkiesH.Dim.dimLE_mono
          (Work.WilkiesH.Strat.RegAux.cellBand_dimLE (S := S) hcd hcb hκ) hdle)
        Set.inter_subset_left
    · have hdge : μ ≤ d := by omega
      obtain ⟨e₀, Φ₀, hUo₀, hΦ₀c, hΦ₀l, hΦ₀r⟩ := Work.WilkiesH.Strat.bandChart_of_cellBand hcb
      have hne₀ : (Work.WilkiesH.Cell.ProjE e₀ κ).Nonempty := hne.image (fun x => x ∘ e₀)
      have hdμ : d ≤ μ := Work.WilkiesH.Strat.RegAux.cell_chart_dim_le hκV hVdim e₀ hUo₀ hne₀
      have hd : d = μ := le_antisymm hdμ hdge
      have hcbμ : Work.WilkiesH.Strat.CellBand n κ μ := hd ▸ hcb
      obtain ⟨e, U, ψ, A, L, hUo, hUne, hψc, -, hψim, hψsec, hΓ⟩ :=
        Work.WilkiesH.Strat.cell_par_exists (S := S) hcbμ hne (F + 2) D
          (Work.WilG5.mem_mono hκ _ _ (by omega) le_rfl)
      have hempty : interior {u : Fin μ → ℝ | u ∈ U ∧ ψ u ∈ closure (V \ κ)} = ∅ :=
        Work.WilkiesH.Strat.SI.interior_frontier_chart_empty (e := e) hVsem hVdim
          hUo hψc hψsec hψim hκV
      have hkey : WilkiesDesign.DimLE
          (ψ '' {u : Fin μ → ℝ | u ∈ U ∧ ψ u ∈ closure (V \ κ)}) (μ - 1) :=
        dimLE_frontier_image (S := S) hcd e hΓ (by rw [← hCeq]; exact hCmem) hψsec hempty
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

end Work.WilkiesH.Strat.SI
