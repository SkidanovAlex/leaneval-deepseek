import Mathlib
import Submission.Work.WilkiesH.Strat.CellBand
import Submission.Work.WilkiesH.Cell.cellDimLE_of_isCell_dimLE
import Submission.Work.WilG5.Basic
import Submission.Work.WilG5.Reindex2
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilkiesH.Strat.bandChart_of_cellBand

/-!
# A band cell is a graph over an open set in the band coordinates

A `CellBand n κ d`-cell (a cylindrical cell whose construction uses exactly `d` band steps)
is, after forgetting the graph steps, the graph of a continuous injective map `ψ` over an open
subset `U ⊆ ℝ^d` of the band coordinates, and this graph is again an `Ω`-set (with a format and
degree depending only on the format and degree of `κ`).

This is the "parametrised cell" input of the counting argument: it turns a band cell into a
`d`-dimensional `Ω`-set which is a graph over an open set, i.e. into the situation in which the
interpolation/stratification arguments apply.

The proof splits in two independent parts:
* `bandChart_of_cellBand` (module `Submission.Work.WilkiesH.Strat.bandChart_of_cellBand`)
  supplies a `d`-coordinate chart `x ↦ x ∘ e` with `ProjE e κ` open and a continuous section `Φ`;
* `sectionGraph_mem` below shows that the graph of this section is `Ω`-definable, using
  `coordPre_mem` (lift to the last `n` coordinates) and `relSet_mem` (the coordinate
  identification `u i = x (e i)`); and `exists_injective_extension` makes the section globally
  injective without changing it on `ProjE e κ`.
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkiesH.Strat

open WilkiesDesign
open Work.WilkiesH.Cell (ProjE)

/-- **The graph of a coordinate projection over an `Ω`-set is an `Ω`-set.**

For an embedding `e : Fin d ↪ Fin n` and an `Ω`-set `κ ⊆ ℝⁿ`, the set of `(u, x) ∈ ℝ^{d+n}`
with `x ∈ κ` and `u i = x (e i)` is an `Ω`-set (in `ℝ^{d+n}`, the `u`-block first, the
`x`-block last).

It is the intersection of the lift `coordPre (Fin.natAdd d) κ` of `κ` to the last `n`
coordinates with the relation set `relSet e`. -/
theorem sectionGraph_mem {S : WilkiesDesign.SOMin} {n d F D : ℕ} {κ : Set (Fin n → ℝ)}
    (e : Fin d ↪ Fin n) (hκ : κ ∈ S.Ω F D n) :
    ∃ A L : ℕ, ({w : Fin (d + n) → ℝ |
      (fun j : Fin n => w (Fin.natAdd d j)) ∈ κ ∧
      (∀ i : Fin d, w (Fin.castAdd n i) = w (Fin.natAdd d (e i)))} : Set (Fin (d + n) → ℝ))
      ∈ S.Ω A L (d + n) := by
  set F₁ : ℕ := F + 64 * ((d + n) + n) + 64 with hF₁
  set D₁ : ℕ := D + 32 * ((d + n) + n) + 32 with hD₁
  set F₂ : ℕ := 4 * (d + n) + 8 with hF₂
  set D₂ : ℕ := 2 * d + 4 with hD₂
  have h1 : Work.WilG5.coordPre (Fin.natAdd d) κ ∈ S.Ω F₁ D₁ (d + n) :=
    Work.WilG5.coordPre_mem hκ
  have h2 : Work.WilG5.relSet (e : Fin d → Fin n) ∈ S.Ω F₂ D₂ (d + n) :=
    Work.WilG5.relSet_mem _
  have h1' : Work.WilG5.coordPre (Fin.natAdd d) κ ∈ S.Ω (max F₁ F₂) D₁ (d + n) :=
    Work.WilG5.mem_mono h1 _ _ (le_max_left _ _) le_rfl
  have h2' : Work.WilG5.relSet (e : Fin d → Fin n) ∈ S.Ω (max F₁ F₂) D₂ (d + n) :=
    Work.WilG5.mem_mono h2 _ _ (le_max_right _ _) le_rfl
  have hJ := S.inter (F := max F₁ F₂) (n := d + n) (k := 2)
    (fun i : Fin 2 => if i = 0 then D₁ else D₂)
    (fun i : Fin 2 => if i = 0 then Work.WilG5.coordPre (Fin.natAdd d) κ
      else Work.WilG5.relSet (e : Fin d → Fin n))
    (by intro i
        fin_cases i
        · simpa using h1'
        · simpa using h2')
  rw [show (∑ i : Fin 2, (if i = 0 then D₁ else D₂)) = D₁ + D₂ from by
    simp [Fin.sum_univ_two]] at hJ
  have hJset : (⋂ i : Fin 2, (if i = 0 then Work.WilG5.coordPre (Fin.natAdd d) κ
      else Work.WilG5.relSet (e : Fin d → Fin n))) =
      Work.WilG5.coordPre (Fin.natAdd d) κ ∩ Work.WilG5.relSet (e : Fin d → Fin n) := by
    ext z; simp [Fin.forall_fin_two]
  rw [hJset] at hJ
  refine ⟨max F₁ F₂ + 1, D₁ + D₂, ?_⟩
  have hset : ({w : Fin (d + n) → ℝ |
      (fun j : Fin n => w (Fin.natAdd d j)) ∈ κ ∧
      (∀ i : Fin d, w (Fin.castAdd n i) = w (Fin.natAdd d (e i)))} : Set (Fin (d + n) → ℝ))
      = Work.WilG5.coordPre (Fin.natAdd d) κ ∩ Work.WilG5.relSet (e : Fin d → Fin n) := by
    ext w
    simp only [Set.mem_inter_iff, Work.WilG5.coordPre, Work.WilG5.relSet, Set.mem_ofPred_eq,
      Function.comp_def]
  rw [hset]
  exact hJ

/-- **Extending a partial section to a globally injective map.**

If `Φ : ℝ^d → ℝⁿ` is continuous on `U` and satisfies `Φ u ∘ e = u` on `U`, then `Φ` can be
replaced by a globally injective `ψ` which agrees with `Φ` on `U` (and hence still satisfies
`ψ u ∘ e = u` there).

Indeed the map `g u j = u (choose (∃ i, e i = j))` (and `0` off the image of `e`) satisfies
`g u ∘ e = u` for every `u`, hence is injective; and `ψ u = if u ∈ U then Φ u else g u` is
injective because `ψ u ∘ e = u` holds at every `u` at which `ψ u = g u`, while on `U` the
section identity `Φ u ∘ e = u` gives the same conclusion. -/
theorem exists_injective_extension {n d : ℕ} (e : Fin d ↪ Fin n) {U : Set (Fin d → ℝ)}
    (Φ : (Fin d → ℝ) → (Fin n → ℝ)) (hcont : ContinuousOn Φ U)
    (hright : ∀ u ∈ U, Φ u ∘ e = u) :
    ∃ ψ : (Fin d → ℝ) → (Fin n → ℝ), ContinuousOn ψ U ∧ Function.Injective ψ ∧
      (∀ u ∈ U, ψ u = Φ u) ∧ (∀ u ∈ U, ψ u ∘ e = u) := by
  let g : (Fin d → ℝ) → (Fin n → ℝ) := fun u j =>
    if h : ∃ i : Fin d, e i = j then u (Classical.choose h) else 0
  have hg : ∀ u, g u ∘ e = u := by
    intro u
    funext i
    have h : ∃ i' : Fin d, e i' = e i := ⟨i, rfl⟩
    simp only [g, Function.comp_apply, dif_pos h]
    rw [e.injective (Classical.choose_spec h)]
  refine ⟨fun u => if u ∈ U then Φ u else g u, ?_, ?_, ?_, ?_⟩
  · exact hcont.congr (fun u hu => by rw [if_pos hu])
  · intro u v huv
    by_cases hu : u ∈ U
    · by_cases hv : v ∈ U
      · have huv' : Φ u = Φ v := by simpa [hu, hv] using huv
        rw [← hright u hu, ← hright v hv, huv']
      · have huv' : Φ u = g v := by simpa [hu, hv] using huv
        have hvu : v = u := by rw [← hg v, ← huv', hright u hu]
        exact absurd (hvu.symm ▸ hu) hv
    · by_cases hv : v ∈ U
      · have huv' : g u = Φ v := by simpa [hu, hv] using huv
        have huvv : u = v := by rw [← hg u, huv', hright v hv]
        exact absurd (huvv ▸ hv) hu
      · have huv' : g u = g v := by simpa [hu, hv] using huv
        rw [← hg u, ← hg v, huv']
  · intro u hu
    dsimp only; rw [if_pos hu]
  · intro u hu
    dsimp only; rw [if_pos hu]
    exact hright u hu

theorem cell_par_exists {S : WilkiesDesign.SOMin} {n d : ℕ} {κ : Set (Fin n → ℝ)}
    (hcb : Work.WilkiesH.Strat.CellBand n κ d) (hne : κ.Nonempty) (F D : ℕ)
    (hκ : κ ∈ S.Ω F D n) :
    ∃ (e : Fin d ↪ Fin n) (U : Set (Fin d → ℝ)) (ψ : (Fin d → ℝ) → (Fin n → ℝ)) (A L : ℕ),
      IsOpen U ∧ U.Nonempty ∧ ContinuousOn ψ U ∧ Function.Injective ψ ∧ ψ '' U = κ ∧
      (∀ u ∈ U, ψ u ∘ e = u) ∧
      ({z : Fin (d + n) → ℝ |
        (fun i : Fin d => z (Fin.castAdd n i)) ∈ U ∧
        (fun j : Fin n => z (Fin.natAdd d j)) = ψ (fun i : Fin d => z (Fin.castAdd n i))})
        ∈ S.Ω A L (d + n) := by
  obtain ⟨e, Φ, hUopen, hΦcont, hΦleft, hΦright⟩ := bandChart_of_cellBand hcb
  let U : Set (Fin d → ℝ) := ProjE e κ
  have hΦim : Φ '' U = κ := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨y, hy, hyu⟩ := hu
      rw [← hyu, hΦleft y hy]
      exact hy
    · intro hx
      exact ⟨x ∘ e, ⟨x, hx, rfl⟩, hΦleft x hx⟩
  have hUne : U.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨x ∘ e, x, hx, rfl⟩
  obtain ⟨ψ, hψcont, hψinj, hψeq, hψright⟩ :=
    exists_injective_extension e Φ hΦcont hΦright
  have hψim : ψ '' U = κ := by
    have hcongr : ψ '' U = Φ '' U := by
      apply Set.image_congr
      intro u hu
      exact hψeq u hu
    rw [hcongr, hΦim]
  obtain ⟨A, L, hG⟩ := sectionGraph_mem (S := S) e hκ
  refine ⟨e, U, ψ, A, L, hUopen, hUne, hψcont, hψinj, hψim, hψright, ?_⟩
  have hset : ({z : Fin (d + n) → ℝ |
        (fun i : Fin d => z (Fin.castAdd n i)) ∈ U ∧
        (fun j : Fin n => z (Fin.natAdd d j)) = ψ (fun i : Fin d => z (Fin.castAdd n i))})
      = {w : Fin (d + n) → ℝ |
        (fun j : Fin n => w (Fin.natAdd d j)) ∈ κ ∧
        (∀ i : Fin d, w (Fin.castAdd n i) = w (Fin.natAdd d (e i)))} := by
    ext z
    constructor
    · rintro ⟨hzU, hzlast⟩
      have hxκ : (fun j : Fin n => z (Fin.natAdd d j)) ∈ κ := by
        rw [← hψim]
        exact ⟨fun i : Fin d => z (Fin.castAdd n i), hzU, hzlast.symm⟩
      refine ⟨hxκ, ?_⟩
      intro i
      have h1 := congrFun (hψright (fun i : Fin d => z (Fin.castAdd n i)) hzU) i
      simp only [Function.comp_apply] at h1
      rw [← h1, ← hzlast]
    · rintro ⟨hxκ, hrel⟩
      have heq : (fun j : Fin n => z (Fin.natAdd d j)) ∘ e
          = (fun i : Fin d => z (Fin.castAdd n i)) :=
        funext (fun i => (hrel i).symm)
      have huU : (fun i : Fin d => z (Fin.castAdd n i)) ∈ U := ⟨_, hxκ, heq⟩
      have hxu : ψ (fun i : Fin d => z (Fin.castAdd n i))
          = (fun j : Fin n => z (Fin.natAdd d j)) := by
        rw [hψeq _ huU]
        rw [← heq]
        exact hΦleft _ hxκ
      exact ⟨huU, hxu.symm⟩
  rw [hset]
  exact hG

end Work.WilkiesH.Strat
