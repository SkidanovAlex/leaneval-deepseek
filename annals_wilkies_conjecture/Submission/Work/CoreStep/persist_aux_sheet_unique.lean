import Mathlib
import Submission.Work.WilE7.CoreStep.GermDefs

noncomputable section
open Classical Filter Topology
open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign

namespace Work.CoreStep

/-! ### Two elementary facts about the coordinate projections

These are used only to turn continuity of the sheets into explicit metric neighbourhoods. -/

theorem SheetUnique.continuous_projFirst (n m : ℕ) :
    Continuous (projFirst n m : (Fin (n + m) → ℝ) → (Fin n → ℝ)) :=
  continuous_pi fun _ => continuous_apply _

theorem SheetUnique.continuous_projSnd (n m : ℕ) :
    Continuous (projSnd n m : (Fin (n + m) → ℝ) → (Fin m → ℝ)) :=
  continuous_pi fun _ => continuous_apply _

/-- Every point of `ℝ^{n+m}` is the concatenation of its two coordinate projections. -/
theorem SheetUnique.append_projFirst_projSnd {n m : ℕ} (z : Fin (n + m) → ℝ) :
    Fin.append (projFirst n m z) (projSnd n m z) = z := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [Fin.append_left, projFirst]
  · simp [Fin.append_right, projSnd]

/-- **Local uniqueness of the sheet `s j`.**

Let `T` be a piece at the absolute split `0 + (n + (m+1))`, `C ⊆ ℝⁿ` a base set, and
`s : Fin k → C → ℝ^{m+1}` a finite family of sheets, continuous on `C` and *jointly injective* at
every point of `C`.  Suppose that over `C` the piece `absSet T` is covered by the graphs of the
sheets (`hcov`).  Then for every `j` and every `x₀ ∈ C` the sheet `s j` is the *only* branch of
`absSet T` above `C`, near the point `(x₀, s j x₀)`.

Proof.  For a fixed other branch `j' ≠ j` put `ε = dist (s j x₀) (s j' x₀) > 0` (strictly
positive by joint injectivity at `x₀`) and let `δ > 0` be a continuity radius of `s j'` on `C` at
`x₀` for the target radius `ε/2`.  Then

`W j' = {z : dist (π_n z) x₀ < δ} ∩ {z : ε/2 < dist (π_{m+1} z) (s j' x₀)}`

is a neighbourhood of `(x₀, s j x₀)` which contains *no* point of `absSet T` above `C` whose fibre
coordinate equals `s j'`: indeed such a point `z` has `s j' (π_n z) = π_{m+1} z = s j' (π_n z)`
with `π_n z ∈ C` and `dist (π_n z) x₀ < δ`, so `dist (π_{m+1} z) (s j' x₀) < ε/2`, contradicting
the second condition.  Intersecting over the finitely many `j' ≠ j` gives a neighbourhood `V` of
`(x₀, s j x₀)`.  Now let `x ∈ C` and `z ∈ absSet T ∩ V` with `π_n z = x`.  By `hcov` there is
`j'` with `s j' x = π_{m+1} z`; if `j' = j` we are done, and otherwise `z` would lie in
`absSet T`, above `C`, with fibre coordinate `s j' x`, contradicting `z ∈ V`.  Finally
`z = Fin.append (π_n z) (π_{m+1} z)` reassembles `z` from its two projections. -/
theorem persist_aux_sheet_unique {n m k : ℕ}
    (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (C : Set (Fin n → ℝ))
    (s : Fin k → (Fin n → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ j : Fin k, ContinuousOn (s j) C)
    (hinj : ∀ x : Fin n → ℝ, x ∈ C → Function.Injective fun j : Fin k => s j x)
    (hcov : ∀ z : Fin (n + (m + 1)) → ℝ, z ∈ Work.WilE7.MainDesign.absSet T →
        WilkiesDesign.E.projFirst n (m + 1) z ∈ C →
        ∃ j : Fin k, s j (WilkiesDesign.E.projFirst n (m + 1) z) =
          WilkiesDesign.E.projSnd n (m + 1) z)
    (j : Fin k) (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ C) :
    ∃ V ∈ nhds (Fin.append x₀ (s j x₀)),
      ∃ U ∈ nhds x₀, ∀ x ∈ C ∩ U, ∀ z ∈ Work.WilE7.MainDesign.absSet T,
        WilkiesDesign.E.projFirst n (m + 1) z = x → z ∈ V →
        z = Fin.append x (s j x) := by
  classical
  -- For every other branch `j'`, a neighbourhood of `(x₀, s j x₀)` in which no point of
  -- `absSet T` above `C` can have fibre coordinate `s j'`.
  have key : ∀ j' : {j' : Fin k // j' ≠ j},
      ∃ W : Set (Fin (n + (m + 1)) → ℝ), W ∈ nhds (Fin.append x₀ (s j x₀)) ∧
        (∀ z, z ∈ absSet T → projFirst n (m + 1) z ∈ C →
          projSnd n (m + 1) z = s j'.1 (projFirst n (m + 1) z) → z ∉ W) := by
    rintro ⟨j', hj'⟩
    have hne : s j x₀ ≠ s j' x₀ := by
      intro h
      exact hj' (hinj x₀ hx₀ h).symm
    set ε : ℝ := dist (s j x₀) (s j' x₀) with hε
    have hεpos : 0 < ε := by rw [hε]; exact dist_pos.mpr hne
    obtain ⟨δ, hδpos, hδ⟩ :=
      Metric.continuousWithinAt_iff.mp (hcont j' x₀ hx₀) (ε / 2) (by linarith)
    have hA : {z : Fin (n + (m + 1)) → ℝ | dist (projFirst n (m + 1) z) x₀ < δ} ∈
        nhds (Fin.append x₀ (s j x₀)) := by
      refine (isOpen_lt ((SheetUnique.continuous_projFirst n (m + 1)).dist continuous_const)
        continuous_const).mem_nhds ?_
      have hp : projFirst n (m + 1) (Fin.append x₀ (s j x₀)) = x₀ :=
        funext fun i => Fin.append_left _ _ i
      change dist (projFirst n (m + 1) (Fin.append x₀ (s j x₀))) x₀ < δ
      rw [hp, dist_self]
      exact hδpos
    have hB : {z : Fin (n + (m + 1)) → ℝ | ε / 2 < dist (projSnd n (m + 1) z) (s j' x₀)} ∈
        nhds (Fin.append x₀ (s j x₀)) := by
      refine (isOpen_lt continuous_const
        ((SheetUnique.continuous_projSnd n (m + 1)).dist continuous_const)).mem_nhds ?_
      have hp : projSnd n (m + 1) (Fin.append x₀ (s j x₀)) = s j x₀ :=
        funext fun i => Fin.append_right _ _ i
      change ε / 2 < dist (projSnd n (m + 1) (Fin.append x₀ (s j x₀))) (s j' x₀)
      rw [hp, ← hε]
      linarith
    refine ⟨_, Filter.inter_mem hA hB, ?_⟩
    rintro z hzT hzC hzSnd hzW
    have hz1 : dist (projFirst n (m + 1) z) x₀ < δ := hzW.1
    have hz2 : ε / 2 < dist (projSnd n (m + 1) z) (s j' x₀) := hzW.2
    have hlt := hδ hzC hz1
    rw [← hzSnd] at hlt
    linarith
  choose W hW hWkey using key
  refine ⟨⋂ j', W j', Filter.iInter_mem.mpr hW, Set.univ, Filter.univ_mem, ?_⟩
  intro x hx z hzT hbase hzV
  by_contra hne
  obtain ⟨j', hj'⟩ := hcov z hzT (by rw [hbase]; exact hx.1)
  have hjne : j' ≠ j := by
    intro hjj
    refine hne ?_
    rw [← SheetUnique.append_projFirst_projSnd z, ← hj', hbase, hjj]
  exact (hWkey ⟨j', hjne⟩ z hzT (by rw [hbase]; exact hx.1) hj'.symm)
    (Set.mem_iInter.mp hzV ⟨j', hjne⟩)

end Work.CoreStep
