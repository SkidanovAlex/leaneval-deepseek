import Mathlib
import Submission.Work.Diff.EXT.evolX.lapCommAuxDefs
import Submission.Work.Diff.EXT.evolX.substC.LapOpEJetAll
import Submission.Work.Diff.EXT.evolX.cktSwapBoundW
import Submission.Work.Diff.EXT.lapComm_tower
import Submission.Work.Diff.EXT.jetSmoothDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A shut-in copy of the jet-level Weitzenböck source bound

`Submission/Work/Diff/EXT/evolX/lapComm_src_jets.lean` cannot compile: it declares
`Work.Diff.EXT.evolX.ckt_finCast` while its import `ckt_adjacent_swap_bound` now imports
`swapDiffDefs`, which declares the same name; and its assembly step is still a `sorry`.  This module
provides an independent copy of the target theorem, under the name
`Work.Diff.EXT.evolX.lapComm_src_jetsB`, together with a local copy of the entry lemmas of `tupIns`
(so that it does not import the broken module).  `Work.Diff.EXT.ladderEfD_stepB` and
`Work.Diff.EXT.evolCompKFixReact_allB` consume it, and `Work.Diff.EXT.evolK_of_flow` can be pointed
at the resulting chain.

The mathematics is the plan written in the docstring of the broken module: the `j`-th jet of the
frame-traced tower is `∑_i ckt d (tupIns …)` (`lapOpE_jetAllC`), the two sums differ by the shift of
the double frame insertion by one slot, and that shift is the composite of the two adjacent
swaps `tupSwap d (j+1)` and `tupSwap d j`, each costing `Shape (d-2)` by
`ckt_adjacent_swap_bound`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.evolX

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## Entry lemmas for `tupIns` (local copies) -/

/-- `tupIns` on the canonical index type of `Fin.append`. -/
noncomputable def tupInsAuxBC (m j : ℕ)
    (Ef : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (G : Fin (m + 4 + j) → Work.Diff.EXT.TField (I := I) (M := M))
    (i : Fin (Module.finrank ℝ E)) :
    Fin (j + (m + 4 + 1 + 1)) → Work.Diff.EXT.TField (I := I) (M := M) :=
  Fin.append (fun t : Fin j => G ⟨t.val, by omega⟩)
    (Fin.cons (Ef i) (Fin.cons (Ef i) (fun t : Fin (m + 4) => G ⟨j + t.val, by omega⟩)))

theorem tupIns_eq_auxBC {m j : ℕ}
    (Ef : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (G : Fin (m + 4 + j) → Work.Diff.EXT.TField (I := I) (M := M))
    (i : Fin (Module.finrank ℝ E)) (r : Fin ((m + 2 + j) + 4)) :
    tupIns (I := I) (M := M) m j Ef G i r
      = tupInsAuxBC (I := I) (M := M) m j Ef G i ⟨r.val, by omega⟩ := by
  have h : (Fin.cast (by omega : (m + 2 + j) + 4 = j + (m + 4 + 1 + 1)) r
      : Fin (j + (m + 4 + 1 + 1))) = ⟨r.val, by omega⟩ := Fin.ext rfl
  simp only [tupIns, tupInsAuxBC, h]

theorem tupInsAuxB_apply_leftC {m j : ℕ}
    (Ef : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (G : Fin (m + 4 + j) → Work.Diff.EXT.TField (I := I) (M := M))
    (i : Fin (Module.finrank ℝ E)) (t : Fin j) :
    tupInsAuxBC (I := I) (M := M) m j Ef G i (Fin.castAdd (m + 4 + 1 + 1) t)
      = G ⟨t.val, by omega⟩ := by
  simp only [tupInsAuxBC, Fin.append_left]

theorem tupInsAuxB_apply_rightC {m j : ℕ}
    (Ef : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (G : Fin (m + 4 + j) → Work.Diff.EXT.TField (I := I) (M := M))
    (i : Fin (Module.finrank ℝ E)) (t : Fin (m + 4 + 1 + 1)) :
    tupInsAuxBC (I := I) (M := M) m j Ef G i (Fin.natAdd j t)
      = ((Fin.cons (Ef i) (Fin.cons (Ef i) (fun t : Fin (m + 4) => G ⟨j + t.val, by omega⟩)) :
          Fin (m + 4 + 1 + 1) → Work.Diff.EXT.TField (I := I) (M := M))) t := by
  simp only [tupInsAuxBC, Fin.append_right]

/-- Entries of `tupIns` below the two frame slots. -/
theorem tupIns_apply_ltBC {m j : ℕ}
    (Ef : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (G : Fin (m + 4 + j) → Work.Diff.EXT.TField (I := I) (M := M))
    (i : Fin (Module.finrank ℝ E)) {r : Fin ((m + 2 + j) + 4)} (hr : (r : ℕ) < j) :
    tupIns (I := I) (M := M) m j Ef G i r = G ⟨r.val, by omega⟩ := by
  rw [tupIns_eq_auxBC]
  have hidx : (⟨r.val, by omega⟩ : Fin (j + (m + 4 + 1 + 1)))
      = Fin.castAdd (m + 4 + 1 + 1) ⟨r.val, hr⟩ := Fin.ext rfl
  rw [hidx, tupInsAuxB_apply_leftC]

/-- Entries of `tupIns` in the two frame slots. -/
theorem tupIns_apply_frameBC {m j : ℕ}
    (Ef : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (G : Fin (m + 4 + j) → Work.Diff.EXT.TField (I := I) (M := M))
    (i : Fin (Module.finrank ℝ E)) {r : Fin ((m + 2 + j) + 4)}
    (hr : (r : ℕ) = j ∨ (r : ℕ) = j + 1) :
    tupIns (I := I) (M := M) m j Ef G i r = Ef i := by
  rw [tupIns_eq_auxBC]
  have hidx : (⟨r.val, by omega⟩ : Fin (j + (m + 4 + 1 + 1)))
      = Fin.natAdd j ⟨(r : ℕ) - j, by omega⟩ := by
    ext; simp; omega
  rw [hidx, tupInsAuxB_apply_rightC]
  rcases hr with h | h
  · have h0 : (⟨(r : ℕ) - j, by omega⟩ : Fin (m + 4 + 1 + 1)) = 0 := by ext; simp; omega
    rw [h0, Fin.cons_zero]
  · have h1 : (⟨(r : ℕ) - j, by omega⟩ : Fin (m + 4 + 1 + 1)) = 1 := by ext; simp; omega
    rw [h1]; rfl

/-- Entries of `tupIns` above the two frame slots (shifted by two). -/
theorem tupIns_apply_geBC {m j : ℕ}
    (Ef : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (G : Fin (m + 4 + j) → Work.Diff.EXT.TField (I := I) (M := M))
    (i : Fin (Module.finrank ℝ E)) {r : Fin ((m + 2 + j) + 4)} (hr : j + 2 ≤ (r : ℕ)) :
    tupIns (I := I) (M := M) m j Ef G i r = G ⟨r.val - 2, by omega⟩ := by
  rw [tupIns_eq_auxBC]
  have hidx : (⟨r.val, by omega⟩ : Fin (j + (m + 4 + 1 + 1)))
      = Fin.natAdd j ⟨(r : ℕ) - j, by omega⟩ := by
    ext; simp; omega
  rw [hidx, tupInsAuxB_apply_rightC]
  obtain ⟨t', ht'⟩ : ∃ t' : Fin (m + 4),
      (⟨(r : ℕ) - j, by omega⟩ : Fin (m + 4 + 1 + 1)) = Fin.succ (Fin.succ t') :=
    ⟨⟨(r : ℕ) - j - 2, by omega⟩, by ext; simp; omega⟩
  have ht'val : (t' : ℕ) + 2 = (r : ℕ) - j := by
    have h := congrArg Fin.val ht'
    simp at h
    omega
  rw [ht']
  simp only [Fin.cons_succ]
  congr 1
  ext
  simp only [Fin.val_mk]
  omega

/-! ## The shift of the double frame insertion is the composite of the two swaps -/

/-- **The double frame insertion shifted by one slot.**  Applying the adjacent swaps at `j` and at
`j+1` to `tupIns (m+1) j` (the tuple `(G_0,…,G_{j-1},E,E,G_j,…)`) gives `tupIns m (j+1)`
(the tuple `(G_0,…,G_j,E,E,G_{j+1},…)`), up to the arity cast. -/
theorem tupSwap_shiftBC {N m j : ℕ} (h1 : (m + 1) + 4 + j = N) (h2 : m + 4 + (j + 1) = N)
    (Ef : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (G : Fin N → Work.Diff.EXT.TField (I := I) (M := M))
    (i : Fin (Module.finrank ℝ E)) (r : Fin (((m + 1) + 2 + j) + 4)) :
    tupSwap (I := I) (M := M) ((m + 1) + 2 + j) j (by omega)
        (tupSwap (I := I) (M := M) ((m + 1) + 2 + j) (j + 1) (by omega)
          (tupIns (I := I) (M := M) (m + 1) j Ef
            (fun r' : Fin ((m + 1) + 4 + j) => G (Fin.cast h1 r')) i)) r
      = tupIns (I := I) (M := M) m (j + 1) Ef
          (fun r' : Fin (m + 4 + (j + 1)) => G (Fin.cast h2 r')) i
          (Fin.cast (by omega) r) := by
  have hcast : (Fin.cast (by omega : ((m + 1) + 2 + j) + 4 = (m + 2 + (j + 1)) + 4) r
      : Fin ((m + 2 + (j + 1)) + 4)) = ⟨r.val, by omega⟩ := Fin.ext rfl
  rw [hcast]
  by_cases h0 : (r : ℕ) < j
  · simp only [tupSwap_of_ne (I := I) (M := M) (d := ((m + 1) + 2 + j)) (p := j) (r := r) _ (by first | (simp only [Fin.val_mk]; omega) | (simp only [Fin.val_mk]) | omega) (by first | (simp only [Fin.val_mk]; omega) | (simp only [Fin.val_mk]) | omega),
      tupSwap_of_ne (I := I) (M := M) (d := ((m + 1) + 2 + j)) (p := j + 1) (r := r) _ (by first | (simp only [Fin.val_mk]; omega) | (simp only [Fin.val_mk]) | omega) (by first | (simp only [Fin.val_mk]; omega) | (simp only [Fin.val_mk]) | omega),
      tupIns_apply_ltBC (I := I) (M := M) (m := m + 1) (j := j) (r := r) Ef _ i h0,
      tupIns_apply_ltBC (I := I) (M := M) (m := m) (j := j + 1) (r := ⟨r.val, by omega⟩)
        Ef _ i (by first | (simp only [Fin.val_mk]; omega) | (simp only [Fin.val_mk]) | omega)] <;> (first | rfl | (congr 1; exact Fin.ext rfl))
  · by_cases h1' : (r : ℕ) = j
    · have hr : r = ⟨j, by omega⟩ := Fin.ext h1'
      rw [hr]
      simp only [tupSwap_at_p (I := I) (M := M) (d := ((m + 1) + 2 + j)) (p := j) _,
        tupSwap_at_p (I := I) (M := M) (d := ((m + 1) + 2 + j)) (p := j + 1) _,
        tupIns_apply_geBC (I := I) (M := M) (m := m + 1) (j := j) (r := ⟨j + 2, by omega⟩)
          Ef _ i (by first | (simp only [Fin.val_mk]; omega) | (simp only [Fin.val_mk]) | omega),
        tupIns_apply_ltBC (I := I) (M := M) (m := m) (j := j + 1) (r := ⟨j, by omega⟩)
          Ef _ i (by first | (simp only [Fin.val_mk]; omega) | (simp only [Fin.val_mk]) | omega)] <;> (first | rfl | (congr 1; exact Fin.ext rfl))
    · by_cases h2' : (r : ℕ) = j + 1
      · have hr : r = ⟨j + 1, by omega⟩ := Fin.ext h2'
        rw [hr]
        simp only [tupSwap_at_p_succ (I := I) (M := M) (d := ((m + 1) + 2 + j)) (p := j) _,
          tupSwap_of_ne (I := I) (M := M) (d := ((m + 1) + 2 + j)) (p := j + 1) (r := ⟨j, by omega⟩) _ (by first | (simp only [Fin.val_mk]; omega) | (simp only [Fin.val_mk]) | omega) (by first | (simp only [Fin.val_mk]; omega) | (simp only [Fin.val_mk]) | omega),
          tupIns_apply_frameBC (I := I) (M := M) (m := m + 1) (j := j)
            (r := ⟨j, by omega⟩) Ef _ i (Or.inl rfl),
          tupIns_apply_frameBC (I := I) (M := M) (m := m) (j := j + 1)
            (r := ⟨j + 1, by omega⟩) Ef _ i (Or.inl rfl)] <;> (first | rfl | (congr 1; exact Fin.ext rfl))
      · by_cases h3 : (r : ℕ) = j + 2
        · have hr : r = ⟨j + 2, by omega⟩ := Fin.ext h3
          rw [hr]
          simp only [tupSwap_of_ne (I := I) (M := M) (d := ((m + 1) + 2 + j)) (p := j) (r := ⟨j + 2, by omega⟩) _ (by first | (simp only [Fin.val_mk]; omega) | (simp only [Fin.val_mk]) | omega) (by first | (simp only [Fin.val_mk]; omega) | (simp only [Fin.val_mk]) | omega),
            tupSwap_at_p_succ (I := I) (M := M) (d := ((m + 1) + 2 + j)) (p := j + 1) _,
            tupIns_apply_frameBC (I := I) (M := M) (m := m + 1) (j := j)
              (r := ⟨j + 1, by omega⟩) Ef _ i (Or.inr rfl),
            tupIns_apply_frameBC (I := I) (M := M) (m := m) (j := j + 1)
              (r := ⟨j + 2, by omega⟩) Ef _ i (Or.inr rfl)] <;> (first | rfl | (congr 1; exact Fin.ext rfl))
        · simp only [tupSwap_of_ne (I := I) (M := M) (d := ((m + 1) + 2 + j)) (p := j) (r := r) _ (by first | (simp only [Fin.val_mk]; omega) | (simp only [Fin.val_mk]) | omega) (by first | (simp only [Fin.val_mk]; omega) | (simp only [Fin.val_mk]) | omega),
            tupSwap_of_ne (I := I) (M := M) (d := ((m + 1) + 2 + j)) (p := j + 1) (r := r) _ (by first | (simp only [Fin.val_mk]; omega) | (simp only [Fin.val_mk]) | omega) (by first | (simp only [Fin.val_mk]; omega) | (simp only [Fin.val_mk]) | omega),
            tupIns_apply_geBC (I := I) (M := M) (m := m + 1) (j := j) (r := r) Ef _ i (by first | (simp only [Fin.val_mk]; omega) | (simp only [Fin.val_mk]) | omega),
            tupIns_apply_geBC (I := I) (M := M) (m := m) (j := j + 1) (r := ⟨r.val, by omega⟩)
              Ef _ i (by first | (simp only [Fin.val_mk]; omega) | (simp only [Fin.val_mk]) | omega)] <;> (first | rfl | (congr 1; exact Fin.ext rfl))


/-! ## The product bookkeeping -/

/-- The index permutation implemented by `tupSwap`. -/
noncomputable def swapIdxBC (d p : ℕ) (hp : p + 2 ≤ d) (r : Fin (d + 4)) : Fin (d + 4) :=
  if (r : ℕ) = p then ⟨p + 1, by omega⟩ else if (r : ℕ) = p + 1 then ⟨p, by omega⟩ else r

theorem tupSwap_eq_swapIdxBC (d p : ℕ) (hp : p + 2 ≤ d) (G : Fin (d + 4) → TField (I := I) (M := M))
    (r : Fin (d + 4)) : tupSwap (I := I) (M := M) d p hp G r = G (swapIdxBC d p hp r) := rfl

theorem swapIdxB_involC (d p : ℕ) (hp : p + 2 ≤ d) (r : Fin (d + 4)) :
    swapIdxBC d p hp (swapIdxBC d p hp r) = r := by
  apply Fin.ext
  simp only [swapIdxBC]
  split_ifs <;> simp_all <;> try omega

theorem swapIdxB_bijectiveC (d p : ℕ) (hp : p + 2 ≤ d) : Function.Bijective (swapIdxBC d p hp) :=
  ⟨fun a b h => by
      have h' := congrArg (swapIdxBC d p hp) h
      rw [swapIdxB_involC, swapIdxB_involC] at h'
      exact h',
    fun b => ⟨swapIdxBC d p hp b, swapIdxB_involC d p hp b⟩⟩

/-- **`tupSwap` does not change a product over the tuple.** -/
theorem prod_tupSwapBC {d p : ℕ} (hp : p + 2 ≤ d)
    (f : Work.Diff.EXT.TField (I := I) (M := M) → ℝ)
    (G : Fin (d + 4) → Work.Diff.EXT.TField (I := I) (M := M)) :
    (∏ r : Fin (d + 4), f (tupSwap (I := I) (M := M) d p hp G r)) = ∏ r : Fin (d + 4), f (G r) := by
  have hbij := swapIdxB_bijectiveC d p hp
  have h : (∏ r : Fin (d + 4), f (G (swapIdxBC d p hp r))) = ∏ r : Fin (d + 4), f (G r) :=
    (Fintype.prod_bijective (Equiv.ofBijective (swapIdxBC d p hp) hbij) hbij
      (fun r => f (G r)) (fun r => f (G (swapIdxBC d p hp r)))
      (fun r => by simp only [Equiv.ofBijective_apply]; rw [swapIdxB_involC])).symm
  simpa only [tupSwap_eq_swapIdxBC] using h

/-- Reindexing a product along `Fin.cast`. -/
theorem prod_reindexC {N M : ℕ} (h : N = M) (f : Fin M → ℝ) :
    (∏ r : Fin N, f (Fin.cast h r)) = ∏ r : Fin M, f r := by
  subst h
  simp


/-- **The product of the metric norms of the entries of `tupIns (m+1) j`** equals the product of the
norms of the underlying tuple `W` (the two frame slots have norm one). -/
theorem prod_gNrm_tupInsBC [T2Space M] {m j N : ℕ} (h : (m + 1) + 4 + j = N)
    (g : SMet I M) (x : M) (Ef : Fin (Module.finrank ℝ E) → TField (I := I) (M := M))
    (hONx : Submission.Diff.IsONFrame g x (fun i => Ef i x))
    (W : Fin N → TField (I := I) (M := M)) (i : Fin (Module.finrank ℝ E)) :
    (∏ r : Fin (((m + 1) + 2 + j) + 4),
        gNrm g x (tupIns (I := I) (M := M) (m + 1) j Ef
          (fun r' : Fin ((m + 1) + 4 + j) => W (Fin.cast h r')) i r x))
      = ∏ r : Fin N, gNrm g x (W r x) := by
  have hA : (j + 2) + (m + 5) = (((m + 1) + 2 + j) + 4) := by omega
  have hB : j + (m + 5) = N := by omega
  rw [(Fintype.prod_bijective (finCongr hA) (finCongr hA).bijective
    (fun r : Fin ((j + 2) + (m + 5)) => gNrm g x (tupIns (I := I) (M := M) (m + 1) j Ef
      (fun r' : Fin ((m + 1) + 4 + j) => W (Fin.cast h r')) i (Fin.cast hA r) x))
    (fun r : Fin (((m + 1) + 2 + j) + 4) => gNrm g x (tupIns (I := I) (M := M) (m + 1) j Ef
      (fun r' : Fin ((m + 1) + 4 + j) => W (Fin.cast h r')) i r x))
    (fun r => by simp only [finCongr_apply])).symm]
  rw [Fin.prod_univ_add]
  rw [Fin.prod_univ_add]
  -- the first block
  have b1 : (∏ t : Fin j, gNrm g x (tupIns (I := I) (M := M) (m + 1) j Ef
        (fun r' : Fin ((m + 1) + 4 + j) => W (Fin.cast h r')) i
        (Fin.cast hA (Fin.castAdd (m + 5) (Fin.castAdd 2 t))) x))
      = ∏ t : Fin j, gNrm g x (W ⟨t.val, by omega⟩ x) := by
    refine Finset.prod_congr rfl fun t _ => ?_
    have e : (Fin.cast hA (Fin.castAdd (m + 5) (Fin.castAdd 2 t))
        : Fin (((m + 1) + 2 + j) + 4)) = ⟨t.val, by omega⟩ := Fin.ext rfl
    rw [e, tupIns_apply_ltBC (I := I) (M := M) (m := m + 1) (j := j) (r := ⟨t.val, by omega⟩)
      _ _ i (by simp only [Fin.val_mk]; omega)]
    congr 1
  -- the two frame slots
  have b2 : (∏ t : Fin 2, gNrm g x (tupIns (I := I) (M := M) (m + 1) j Ef
        (fun r' : Fin ((m + 1) + 4 + j) => W (Fin.cast h r')) i
        (Fin.cast hA (Fin.castAdd (m + 5) (Fin.natAdd j t))) x)) = 1 := by
    rw [Fin.prod_univ_two]
    have e0 : (Fin.cast hA (Fin.castAdd (m + 5) (Fin.natAdd j (0 : Fin 2)))
        : Fin (((m + 1) + 2 + j) + 4)) = ⟨j, by omega⟩ := Fin.ext rfl
    have e1 : (Fin.cast hA (Fin.castAdd (m + 5) (Fin.natAdd j (1 : Fin 2)))
        : Fin (((m + 1) + 2 + j) + 4)) = ⟨j + 1, by omega⟩ := Fin.ext rfl
    rw [e0, e1, tupIns_apply_frameBC (I := I) (M := M) (m := m + 1) (j := j)
          (r := ⟨j, by omega⟩) _ _ i (Or.inl rfl),
      tupIns_apply_frameBC (I := I) (M := M) (m := m + 1) (j := j)
          (r := ⟨j + 1, by omega⟩) _ _ i (Or.inr rfl),
      gNrm_eq_one_of_isONFrame g x hONx i, one_mul]
  -- the third block
  have b3 : (∏ s : Fin (m + 5), gNrm g x (tupIns (I := I) (M := M) (m + 1) j Ef
        (fun r' : Fin ((m + 1) + 4 + j) => W (Fin.cast h r')) i
        (Fin.cast hA (Fin.natAdd (j + 2) s)) x))
      = ∏ s : Fin (m + 5), gNrm g x (W ⟨j + s.val, by omega⟩ x) := by
    refine Finset.prod_congr rfl fun s _ => ?_
    have h1 : (Fin.cast hA (Fin.natAdd (j + 2) s) : Fin (((m + 1) + 2 + j) + 4))
        = ⟨(j + 2) + s.val, by omega⟩ := Fin.ext rfl
    rw [h1, tupIns_apply_geBC (I := I) (M := M) (m := m + 1) (j := j)
      (r := ⟨(j + 2) + s.val, by omega⟩) Ef
      (fun r' : Fin ((m + 1) + 4 + j) => W (Fin.cast h r')) i
      (by first | (simp only [Fin.val_mk]; omega) | omega)]
    have h2 : (Fin.cast h ⟨(j + 2) + s.val - 2, by omega⟩ : Fin N) = ⟨j + s.val, by omega⟩ :=
      Fin.ext (by show ((j + 2) + s.val - 2) = j + s.val; omega)
    rw [h2]
  rw [b1, b2, b3]
  have hR : (∏ r : Fin N, gNrm g x (W r x))
      = (∏ t : Fin j, gNrm g x (W ⟨t.val, by omega⟩ x))
        * ∏ s : Fin (m + 5), gNrm g x (W ⟨j + s.val, by omega⟩ x) := by
    rw [(Fintype.prod_bijective (finCongr hB) (finCongr hB).bijective
      (fun r : Fin (j + (m + 5)) => gNrm g x (W (Fin.cast hB r) x))
      (fun r : Fin N => gNrm g x (W r x))
      (fun r => by rw [finCongr_apply])).symm]
    rw [show (∏ r : Fin (j + (m + 5)), gNrm g x (W (Fin.cast hB r) x))
        = (∏ t : Fin j, gNrm g x (W (Fin.cast hB (Fin.castAdd (m + 5) t)) x))
          * ∏ s : Fin (m + 5), gNrm g x (W (Fin.cast hB (Fin.natAdd j s)) x)
        from Fin.prod_univ_add _]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine Finset.prod_congr rfl fun t _ => ?_
      congr 1
    · refine Finset.prod_congr rfl fun s _ => ?_
      congr 1
  rw [hR]
  ring


/-- The tuple-level form of `tupSwap_shiftBC`. -/
theorem tupSwap_shiftBTC {N m j : ℕ} (h1 : (m + 1) + 4 + j = N) (h2 : m + 4 + (j + 1) = N)
    (Ef : Fin (Module.finrank ℝ E) → TField (I := I) (M := M))
    (G : Fin N → TField (I := I) (M := M)) (i : Fin (Module.finrank ℝ E)) :
    tupSwap (I := I) (M := M) ((m + 1) + 2 + j) j (by omega)
        (tupSwap (I := I) (M := M) ((m + 1) + 2 + j) (j + 1) (by omega)
          (tupIns (I := I) (M := M) (m + 1) j Ef
            (fun r' : Fin ((m + 1) + 4 + j) => G (Fin.cast h1 r')) i))
      = fun r : Fin (((m + 1) + 2 + j) + 4) =>
          tupIns (I := I) (M := M) m (j + 1) Ef
            (fun r' : Fin (m + 4 + (j + 1)) => G (Fin.cast h2 r')) i (Fin.cast (by omega) r) := by
  funext r
  exact tupSwap_shiftBC (I := I) (M := M) h1 h2 Ef G i r

/-- The entries of `tupIns` are smooth when the tuple and the frame are. -/
theorem smooth_tupInsBC {m j : ℕ}
    (Ef : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (hEf : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (Ef i))
    (G : Fin (m + 4 + j) → Work.Diff.EXT.TField (I := I) (M := M))
    (hG : ∀ r, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (G r))
    (i : Fin (Module.finrank ℝ E)) (r : Fin ((m + 2 + j) + 4)) :
    Work.Diff.GE.SmoothFieldT (I := I) (M := M) (tupIns (I := I) (M := M) m j Ef G i r) := by
  by_cases h0 : (r : ℕ) < j
  · rw [tupIns_apply_ltBC (I := I) (M := M) Ef G i h0]; exact hG _
  · by_cases h1 : (r : ℕ) = j
    · rw [tupIns_apply_frameBC (I := I) (M := M) Ef G i (Or.inl h1)]; exact hEf i
    · by_cases h2 : (r : ℕ) = j + 1
      · rw [tupIns_apply_frameBC (I := I) (M := M) Ef G i (Or.inr h2)]; exact hEf i
      · rw [tupIns_apply_geBC (I := I) (M := M) Ef G i (by omega)]; exact hG _

/-- The entries of a swapped tuple are smooth when the tuple is. -/
theorem smooth_tupSwapBC {d p : ℕ} (hp : p + 2 ≤ d)
    (G : Fin (d + 4) → Work.Diff.EXT.TField (I := I) (M := M))
    (hG : ∀ r, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (G r))
    (r : Fin (d + 4)) :
    Work.Diff.GE.SmoothFieldT (I := I) (M := M)
      (tupSwap (I := I) (M := M) d p hp G r) := by
  rw [tupSwap_eq_swapIdxBC]
  exact hG _

/-- **The jet-level Weitzenböck (Laplacian–commutator) source bound**, as an independent copy of
`Work.Diff.EXT.evolX.lapComm_src_jets`. -/
theorem lapComm_src_jetsWC
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M] (k j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ), Submission.Diff.IsRicciFlow G T →
        ∀ t ∈ Set.Ico 0 T, ∀ x : M,
        ∀ Ef : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M),
          Work.Diff.EXT.IsFrameNear (I := I) (M := M) (G t) x Ef →
        ∀ (N : ℕ) (h1 : (k + 1 + 4) + j = N) (h2 : (k + 4) + (j + 1) = N)
          (w : Fin N → TangentSpace I x),
          |Work.Diff.EXT.jetAll (G t) j (k + 1 + 4)
              (Work.Diff.EXT.lapOpE (I := I) (M := M) Ef (G t) (k + 1))
              (fun r : Fin ((k + 1 + 4) + j) => Submission.Diff.smoothExt x (w (Fin.cast h1 r))) x
            - Work.Diff.EXT.jetAll (G t) (j + 1) (k + 4)
              (Work.Diff.EXT.lapOpE (I := I) (M := M) Ef (G t) k)
              (fun r : Fin ((k + 4) + (j + 1)) => Submission.Diff.smoothExt x (w (Fin.cast h2 r))) x|
          ≤ C * Work.Diff.EXT.Shape (G t) x ((k + 1) + j)
              * Finset.univ.prod (fun r : Fin N => Real.sqrt ((G t).inner x (w r) (w r))) := by
  have hLC : Submission.Diff.LCSmooth I M := Work.EXT.lcSmooth_noBoundary (I := I) (M := M)
  obtain ⟨C₁, hC₁0, hsw₁⟩ :=
    ckt_adjacent_swap_boundW (I := I) (M := M) hLC ((k + 1) + 2 + j) (j + 1) (by omega)
  obtain ⟨C₂, hC₂0, hsw₂⟩ :=
    ckt_adjacent_swap_boundW (I := I) (M := M) hLC ((k + 1) + 2 + j) j (by omega)
  refine ⟨(Module.finrank ℝ E : ℝ) * (C₁ + C₂), by positivity, ?_⟩
  intro G T hflow t ht x Ef hEf N h1 h2 w
  obtain ⟨hEfsm, hON⟩ := hEf
  have hONx : Submission.Diff.IsONFrame (G t) x (fun i => Ef i x) := hON.self_of_nhds
  set W : Fin N → Work.Diff.EXT.TField (I := I) (M := M) :=
    fun r => Submission.Diff.smoothExt x (w r) with hW
  set P : ℝ := ∏ r : Fin N, Real.sqrt ((G t).inner x (w r) (w r)) with hP
  have hWsm : ∀ r, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (W r) :=
    fun r => Work.Diff.GE.smoothExt_cmdiff x (w r)
  set T₁ : Fin (Module.finrank ℝ E) → Fin (((k + 1) + 2 + j) + 4) →
      Work.Diff.EXT.TField (I := I) (M := M) :=
    fun i => tupIns (I := I) (M := M) (k + 1) j Ef (fun r' => W (Fin.cast h1 r')) i with hT₁
  set T₂ : Fin (Module.finrank ℝ E) → Fin (((k + 1) + 2 + j) + 4) →
      Work.Diff.EXT.TField (I := I) (M := M) :=
    fun i r => tupIns (I := I) (M := M) k (j + 1) Ef (fun r' => W (Fin.cast h2 r')) i
      (Fin.cast (by omega) r) with hT₂
  have hT₁sm : ∀ i r, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (T₁ i r) := fun i =>
    smooth_tupInsBC (I := I) (M := M) (m := k + 1) (j := j) Ef hEfsm
      (fun r' => W (Fin.cast h1 r')) (fun r' => hWsm _) i
  -- the two jet formulas, on the common arity
  have hA : Work.Diff.EXT.jetAll (G t) j (k + 1 + 4)
        (Work.Diff.EXT.lapOpE (I := I) (M := M) Ef (G t) (k + 1))
        (fun r : Fin ((k + 1 + 4) + j) => W (Fin.cast h1 r)) x
      = ∑ i : Fin (Module.finrank ℝ E), ckt (G t) ((k + 1) + 2 + j) (T₁ i) x := by
    rw [lapOpE_jetAllC (I := I) (M := M) hLC (G t) x (k + 1) j Ef hEfsm hON
      (fun r : Fin ((k + 1 + 4) + j) => W (Fin.cast h1 r)) (fun r => hWsm _)]
  have hB : Work.Diff.EXT.jetAll (G t) (j + 1) (k + 4)
        (Work.Diff.EXT.lapOpE (I := I) (M := M) Ef (G t) k)
        (fun r : Fin ((k + 4) + (j + 1)) => W (Fin.cast h2 r)) x
      = ∑ i : Fin (Module.finrank ℝ E), ckt (G t) ((k + 1) + 2 + j) (T₂ i) x := by
    rw [lapOpE_jetAllC (I := I) (M := M) hLC (G t) x k (j + 1) Ef hEfsm hON
      (fun r : Fin ((k + 4) + (j + 1)) => W (Fin.cast h2 r)) (fun r => hWsm _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact ckt_finCast (I := I) (M := M) (by omega) (G t) x _
  -- every product occurring below is `P`
  have hPT₁ : ∀ i : Fin (Module.finrank ℝ E),
      (∏ r : Fin (((k + 1) + 2 + j) + 4), Work.Diff.EXT.gNrm (G t) x (T₁ i r x)) = P := by
    intro i
    have h := prod_gNrm_tupInsBC (I := I) (M := M) (h := h1) (g := G t) (x := x) (Ef := Ef)
      (hONx := hONx) (W := W) (i := i)
    have hT : T₁ i = tupIns (I := I) (M := M) (k + 1) j Ef (fun r' => W (Fin.cast h1 r')) i := rfl
    rw [hT]
    rw [h]
    rw [hP]
    refine Finset.prod_congr rfl fun r _ => ?_
    show Work.Diff.EXT.gNrm (G t) x (Submission.Diff.smoothExt x (w r) x)
      = Real.sqrt ((G t).inner x (w r) (w r))
    rw [Work.Diff.GE.smoothExt_apply]
  have hPM : ∀ i : Fin (Module.finrank ℝ E),
      (∏ r : Fin (((k + 1) + 2 + j) + 4), Work.Diff.EXT.gNrm (G t) x
        ((tupSwap (I := I) (M := M) ((k + 1) + 2 + j) (j + 1) (by omega) (T₁ i)) r x)) = P := by
    intro i
    rw [prod_tupSwapBC (I := I) (M := M) (d := (k + 1) + 2 + j) (p := j + 1) (by omega)
      (fun X => Work.Diff.EXT.gNrm (G t) x (X x)) (T₁ i), hPT₁ i]
  -- the per-component bound
  have hterm : ∀ i : Fin (Module.finrank ℝ E),
      |ckt (G t) ((k + 1) + 2 + j) (T₁ i) x - ckt (G t) ((k + 1) + 2 + j) (T₂ i) x|
        ≤ (C₁ + C₂) * Work.Diff.EXT.Shape (G t) x ((k + 1) + j) * P := by
    intro i
    have hsw₁' := hsw₁ (G t) x (T₁ i) (hT₁sm i)
    have hsw₂' := hsw₂ (G t) x
      (tupSwap (I := I) (M := M) ((k + 1) + 2 + j) (j + 1) (by omega) (T₁ i))
      (fun r => smooth_tupSwapBC (I := I) (M := M) (p := j + 1) (by omega) (T₁ i) (hT₁sm i) r)
    rw [show ((k + 1) + 2 + j) - 2 = (k + 1) + j from by omega] at hsw₁'
    rw [show ((k + 1) + 2 + j) - 2 = (k + 1) + j from by omega] at hsw₂'
    have hmid : ckt (G t) ((k + 1) + 2 + j)
          (tupSwap (I := I) (M := M) ((k + 1) + 2 + j) j (by omega)
            (tupSwap (I := I) (M := M) ((k + 1) + 2 + j) (j + 1) (by omega) (T₁ i))) x
        = ckt (G t) ((k + 1) + 2 + j) (T₂ i) x := by
      have hshift := tupSwap_shiftBTC (I := I) (M := M) (h1 := h1) (h2 := h2) (Ef := Ef)
        (G := W) i
      have hT₁' : T₁ i = tupIns (I := I) (M := M) (k + 1) j Ef
          (fun r' => W (Fin.cast h1 r')) i := rfl
      have hT₂' : T₂ i = fun r : Fin (((k + 1) + 2 + j) + 4) =>
          tupIns (I := I) (M := M) k (j + 1) Ef
            (fun r' => W (Fin.cast h2 r')) i (Fin.cast (by omega) r) := by
        funext r
        rfl
      rw [hT₁', hT₂', hshift]
    have hsplit := abs_sub_le (ckt (G t) ((k + 1) + 2 + j) (T₁ i) x)
      (ckt (G t) ((k + 1) + 2 + j)
        (tupSwap (I := I) (M := M) ((k + 1) + 2 + j) (j + 1) (by omega) (T₁ i)) x)
      (ckt (G t) ((k + 1) + 2 + j) (T₂ i) x)
    rw [hPT₁ i] at hsw₁'
    rw [hPM i, hmid] at hsw₂'
    linarith [hsw₁', hsw₂', hsplit, mul_nonneg (add_nonneg hC₁0 hC₂0)
      (Work.Diff.EXT.Shape_nonneg (G t) x ((k + 1) + j))]
  have hsum := Finset.sum_sub_distrib (s := Finset.univ)
    (f := fun i : Fin (Module.finrank ℝ E) => ckt (G t) ((k + 1) + 2 + j) (T₁ i) x)
    (g := fun i : Fin (Module.finrank ℝ E) => ckt (G t) ((k + 1) + 2 + j) (T₂ i) x)
  rw [hA, hB, ← hsum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun i _ => hterm i)) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring_nf
  exact le_of_eq (by ring)

end Work.Diff.EXT.evolX
