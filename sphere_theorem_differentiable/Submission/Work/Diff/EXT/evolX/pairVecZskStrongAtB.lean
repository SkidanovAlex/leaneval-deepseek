import Mathlib
import Submission.Work.Diff.EXT.evolX.compLadderDefs
import Submission.Work.Diff.EXT.evolX.jetAllPrecomp
import Submission.Work.Diff.EXT.evolX.ZskPair
import Submission.Work.Diff.EXT.evolX.ladderEf_base
import Submission.Work.Diff.EXT.jetSmoothDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.evolX

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-! ## The slot permutation taking the tower to the curvature vector

`Zsk g W k s` is the level-`k` curvature vector with the inserted slot at position `s`, and its
pairing with the last slot of the tuple is `ckt g k` on the tuple whose entries have been
relabelled.  The relabelling is the bijection of `Fin (k+4)`

`sigFun i = i` for `i < s`, `s ↦ k+3`, `i ↦ i-1` for `i > s`,

the cyclic shift of the segment `[s, k+3]` (it moves `s` to the last position and everything after
`s` down by one).  The first four lemmas below are its `Fin`-level description, the next two its
two-sided inverse `sigInv` (the shift the other way: `k+3 ↦ s`, `i ↦ i+1` for `s ≤ i < k+3`). -/

/-- **The slot permutation of `Zsk`**: `i` for `i < s`, `k+3` at `i = s`, and `i - 1` for `i > s`. -/
noncomputable def sigFun (k : ℕ) (s : Fin (k + 4)) : Fin (k + 4) → Fin (k + 4) :=
  fun i => if h : (i : ℕ) < (s : ℕ) then i
    else if (i : ℕ) = (s : ℕ) then ⟨k + 3, by omega⟩
    else ⟨(i : ℕ) - 1, by have := i.isLt; omega⟩

/-- **The inverse slot permutation**: `i` for `i < s`, `s` at `i = k+3`, and `i + 1` for
`s ≤ i < k+3`. -/
noncomputable def sigInv (k : ℕ) (s : Fin (k + 4)) : Fin (k + 4) → Fin (k + 4) :=
  fun j => if h : (j : ℕ) < (s : ℕ) then j
    else if h2 : (j : ℕ) = k + 3 then s
    else ⟨(j : ℕ) + 1, by have := j.isLt; omega⟩

theorem sigFun_eq_self (k : ℕ) (s : Fin (k + 4)) (i : Fin (k + 4)) (h : (i : ℕ) < (s : ℕ)) :
    sigFun k s i = i := by
  simp only [sigFun, dif_pos h]

theorem sigFun_eq_last (k : ℕ) (s : Fin (k + 4)) (i : Fin (k + 4)) (h : (i : ℕ) = (s : ℕ)) :
    sigFun k s i = ⟨k + 3, by omega⟩ := by
  have h1 : ¬ (i : ℕ) < (s : ℕ) := by omega
  simp only [sigFun, dif_neg h1, if_pos h]

theorem sigFun_eq_pred (k : ℕ) (s : Fin (k + 4)) (i : Fin (k + 4))
    (h1 : ¬ (i : ℕ) < (s : ℕ)) (h2 : (i : ℕ) ≠ (s : ℕ)) :
    sigFun k s i = ⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ := by
  simp only [sigFun, dif_neg h1, if_neg h2]

theorem sigInv_eq_self (k : ℕ) (s : Fin (k + 4)) (j : Fin (k + 4)) (h : (j : ℕ) < (s : ℕ)) :
    sigInv k s j = j := by
  simp only [sigInv, dif_pos h]

theorem sigInv_eq_last (k : ℕ) (s : Fin (k + 4)) (j : Fin (k + 4))
    (h1 : ¬ (j : ℕ) < (s : ℕ)) (h2 : (j : ℕ) = k + 3) :
    sigInv k s j = s := by
  simp only [sigInv, dif_neg h1, dif_pos h2]

theorem sigInv_eq_succ (k : ℕ) (s : Fin (k + 4)) (j : Fin (k + 4))
    (h1 : ¬ (j : ℕ) < (s : ℕ)) (h2 : (j : ℕ) ≠ k + 3) :
    sigInv k s j = ⟨(j : ℕ) + 1, by have := j.isLt; omega⟩ := by
  simp only [sigInv, dif_neg h1, dif_neg h2]

/-- `sigInv` is a right inverse of `sigFun`. -/
theorem sigInv_fun (k : ℕ) (s : Fin (k + 4)) (i : Fin (k + 4)) :
    sigInv k s (sigFun k s i) = i := by
  by_cases h1 : (i : ℕ) < (s : ℕ)
  · rw [sigFun_eq_self k s i h1, sigInv_eq_self k s i h1]
  · by_cases h2 : (i : ℕ) = (s : ℕ)
    · rw [sigFun_eq_last k s i h2]
      have h3 : ¬ ((⟨k + 3, by omega⟩ : Fin (k + 4)) : ℕ) < (s : ℕ) := by
        have := s.isLt; simp only [Fin.val_mk]; omega
      rw [sigInv_eq_last k s ⟨k + 3, by omega⟩ h3 rfl]
      exact Fin.ext h2.symm
    · have hlt : (s : ℕ) < (i : ℕ) := by have := i.isLt; omega
      rw [sigFun_eq_pred k s i h1 h2]
      have h4 : ¬ ((⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin (k + 4)) : ℕ) < (s : ℕ) := by
        simp only [Fin.val_mk]; omega
      have h5 : ((⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin (k + 4)) : ℕ) ≠ k + 3 := by
        simp only [Fin.val_mk]; omega
      rw [sigInv_eq_succ k s ⟨(i : ℕ) - 1, by omega⟩ h4 h5]
      apply Fin.ext
      simp only [Fin.val_mk]
      omega

/-- `sigInv` is a left inverse of `sigFun`. -/
theorem sigFun_inv (k : ℕ) (s : Fin (k + 4)) (j : Fin (k + 4)) :
    sigFun k s (sigInv k s j) = j := by
  by_cases h1 : (j : ℕ) < (s : ℕ)
  · rw [sigInv_eq_self k s j h1, sigFun_eq_self k s j h1]
  · by_cases h2 : (j : ℕ) = k + 3
    · rw [sigInv_eq_last k s j h1 h2]
      rw [sigFun_eq_last k s s rfl]
      exact Fin.ext h2.symm
    · have hj := sigInv_eq_succ k s j h1 h2
      rw [hj]
      have h4 : ¬ ((⟨(j : ℕ) + 1, by have := j.isLt; omega⟩ : Fin (k + 4)) : ℕ) < (s : ℕ) := by
        simp only [Fin.val_mk]; omega
      have h5 : ((⟨(j : ℕ) + 1, by have := j.isLt; omega⟩ : Fin (k + 4)) : ℕ) ≠ (s : ℕ) := by
        simp only [Fin.val_mk]; omega
      rw [sigFun_eq_pred k s ⟨(j : ℕ) + 1, by omega⟩ h4 h5]
      apply Fin.ext
      simp only [Fin.val_mk]
      omega

/-- **The slot permutation of `Zsk`, as a bijection of `Fin (k+4)`.** -/
noncomputable def sigEquiv (k : ℕ) (s : Fin (k + 4)) : Fin (k + 4) ≃ Fin (k + 4) :=
  ⟨sigFun k s, sigInv k s, sigInv_fun k s, sigFun_inv k s⟩

/-! ## The relabelling of the tuple of `Zsk` -/

/-- **`skipMap` followed by `castSucc` is `sigFun`** at every slot different from the inserted
slot `s`. -/
theorem skipMap_castSucc_eq_sigFun (k : ℕ) (s : Fin (k + 4)) (i : Fin (k + 4)) (hi : i ≠ s) :
    (skipMap k s i).castSucc = sigFun k s i := by
  apply Fin.ext
  simp only [skipMap, sigFun, Fin.val_castSucc]
  by_cases h1 : (i : ℕ) < (s : ℕ)
  · rw [dif_pos h1, dif_pos h1]
  · rw [dif_neg h1, dif_neg h1]
    by_cases h2 : (i : ℕ) = (s : ℕ)
    · exact absurd (Fin.ext h2) hi
    · rw [if_neg h2]

/-- **Inserting the last entry at the slot `s` of the `skipMap`-relabelled tuple is the
`sigFun`-relabelled tuple.**  This is the tuple identity behind `ZskPair`. -/
theorem update_skipMap_eq (k : ℕ) (s : Fin (k + 4))
    (F : Fin (k + 4) → Work.Diff.EXT.TField (I := I) (M := M)) :
    Function.update (fun j : Fin (k + 4) => F (skipMap k s j).castSucc) s
      (F (Fin.last (k + 3))) = fun i => F (sigFun k s i) := by
  funext i
  by_cases hi : i = s
  · rw [hi, Function.update_self]
    exact congrArg F (by rw [sigFun_eq_last k s s rfl]; exact Fin.ext rfl)
  · rw [Function.update_of_ne hi]
    exact congrArg F (skipMap_castSucc_eq_sigFun k s i hi)

/-! ## The germ identity -/

/-- A property that holds eventually at `x` holds eventually at every point of a neighbourhood
of `x`. -/
theorem eventually_ONFrameAt (g : Submission.Diff.SMet I M) (x : M)
    (W : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (h : ONFrameAt g x W) : ∀ᶠ y in 𝓝 x, ONFrameAt g y W := by
  obtain ⟨U, hU, hsub⟩ := Filter.eventually_iff_exists_mem.mp h
  obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp hU
  filter_upwards [hVopen.mem_nhds hxV] with y hyV
  exact Filter.mem_of_superset (hVopen.mem_nhds hyV) (hVsub.trans hsub)

/-- **The value of `pairVec g (Zsk g W k s)` is the tower `ckt g k` on the `sigFun`-relabelled
tuple.**  Near a point where `W` is an orthonormal frame, `ZskPair` identifies the pairing of the
curvature vector with the value of the tower on the tuple with the last entry inserted at the slot
`s`; by `update_skipMap_eq` that tuple is the relabelled one. -/
theorem pairVec_Zsk_germ (g : Submission.Diff.SMet I M) (x : M)
    (W : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (hW : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (W i))
    (hON : ONFrameAt g x W)
    {k : ℕ} (s : Fin (k + 4))
    (F : Fin (k + 4) → Work.Diff.EXT.TField (I := I) (M := M))
    (hF : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i)) :
    pairVec (I := I) (M := M) g (Zsk (I := I) (M := M) g W k s) F
      =ᶠ[𝓝 x] fun y => Work.Diff.EXT.ckt g k (fun i => F (sigFun k s i)) y := by
  filter_upwards [eventually_ONFrameAt (I := I) (M := M) g x W hON] with y hy
  have hW' : ∀ i, SmTf (I := I) (M := M) (W i) := fun i => hW i
  have hΨ : ∀ r : Fin (k + 3), SmTf (I := I) (M := M)
      ((fun i : Fin (k + 3) => F i.castSucc) r) := fun r => hF _
  have hzp := ZskPair (I := I) (M := M) g y W hW' hy k s
    (fun i : Fin (k + 3) => F i.castSucc) hΨ (F (Fin.last (k + 3))) (hF _)
  show g.inner y (Zsk (I := I) (M := M) g W k s
      (fun i : Fin (k + 3) => F i.castSucc) y) (F (Fin.last (k + 3)) y)
    = Work.Diff.EXT.ckt g k (fun i => F (sigFun k s i)) y
  rw [hzp, update_skipMap_eq]

/-- **`StrongAt` is invariant under the slot permutation that turns the tower into the curvature
vector.**  A fresh copy of `Work.Diff.EXT.evolX.pairVecZskStrongAt` (same statement), which is the
last open helper of the jet bound for the contracted tower
`Work.Diff.EXT.evolX.substOp_jets_le_v2`.

`Work.Diff.EXT.evolX.pairVec g U` is the pairing operator `F ↦ ⟪U (firstPart F), lastPart F⟫` of a
vector-valued operator `U` (of arity `K + 1`), and `Work.Diff.EXT.evolX.Zsk g W k s` is the level-`k`
curvature vector at the slot `s` (its pairing with `D` is `ckt g k` with `D` inserted in slot `s`,
`Work.Diff.EXT.evolX.ZskPair`).  The claim is that the strength of `pairVec (Zsk …)` is the same as
the strength of the tower itself.

Route: `pairVec (Zsk g W k s)` differs from `ckt g k` by the *slot permutation*
`slotPerm`/`firstPart`/`lastPart` of `compLadderDefs` — i.e. by a reindexing `ρ` of the `k + 4`
slots (`ρ i = i` for `i < s`, `i - 1` for `i > s`, `k + 3` for `i = s`), which is a bijection of
`Fin (k+4)`.
`Work.Diff.EXT.evolX.jetAllPrecomp` (proved) is precisely the equivariance of `jetAll` under such a
permutation, so unpacking `StrongAt` on both sides and applying it to the permuted tuple identifies
the two bounds verbatim (the metric-norm product is permutation invariant, and a permuted smooth
tuple is smooth).  `hON` (orthonormality of `W` near `x`) and `hW` are inherited hypotheses of
`pairVec`/`Zsk`; `hCT` is the nonnegativity of the constant sequence. -/
theorem pairVecZskStrongAtB
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (W : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (hW : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (W i))
    (hON : Filter.Eventually (fun y : M =>
        Submission.Diff.IsONFrame g y (fun i => W i y)) (nhds x))
    {k : ℕ} (s : Fin (k + 4)) {CT : ℕ → ℝ} (hCT : ∀ a, 0 ≤ CT a)
    (htower : Work.Diff.EXT.evolX.StrongAt g x k CT
      (Work.Diff.EXT.ckt (I := I) (M := M) g k)) :
    Work.Diff.EXT.evolX.StrongAt g x k CT
      (Work.Diff.EXT.evolX.pairVec (I := I) (M := M) g
        (Work.Diff.EXT.evolX.Zsk (I := I) (M := M) g W k s)) := by
  intro a G hG
  have _ : 0 ≤ CT a := hCT a
  have h1 : Work.Diff.EXT.jetAll g a ((k + 3) + 1)
      (pairVec (I := I) (M := M) g (Zsk (I := I) (M := M) g W k s)) G x
      = Work.Diff.EXT.jetAll g a ((k + 3) + 1)
        (fun F' y => Work.Diff.EXT.ckt g k (fun i => F' (sigEquiv k s i)) y) G x :=
    jetAll_congr_of_eventuallyEq_smooth' (I := I) (M := M) (K := (k + 3) + 1) (j := a) hLC
      (S := pairVec (I := I) (M := M) g (Zsk (I := I) (M := M) g W k s))
      (S' := fun F' y => Work.Diff.EXT.ckt g k (fun i => F' (sigEquiv k s i)) y) (x := x)
      (fun F hF => pairVec_Zsk_germ (I := I) (M := M) g x W hW hON s F hF) G (fun i => hG i)
  have h2 : Work.Diff.EXT.jetAll g a ((k + 3) + 1)
        (fun F' y => Work.Diff.EXT.ckt g k (fun i => F' (sigEquiv k s i)) y) G x
      = Work.Diff.EXT.jetAll g a ((k + 3) + 1) (Work.Diff.EXT.ckt g k)
          (fun i => G (slotPerm (sigEquiv k s) a i)) x :=
    congrFun (jetAllPrecomp (I := I) (M := M) g (sigEquiv k s)
      (Work.Diff.EXT.ckt g k) a G) x
  have h3 := htower a (fun i => G (slotPerm (sigEquiv k s) a i)) (fun i => hG _)
  have hprod : (∏ r : Fin ((k + 3) + 1 + a),
        Real.sqrt (g.inner x (G (slotPerm (sigEquiv k s) a r) x)
          (G (slotPerm (sigEquiv k s) a r) x)))
      = ∏ r : Fin ((k + 3) + 1 + a), Real.sqrt (g.inner x (G r x) (G r x)) :=
    Fintype.prod_bijective (slotPerm (sigEquiv k s) a) (precomp_slotPerm_bijective (sigEquiv k s) a)
      (fun r => Real.sqrt (g.inner x (G (slotPerm (sigEquiv k s) a r) x)
        (G (slotPerm (sigEquiv k s) a r) x)))
      (fun r => Real.sqrt (g.inner x (G r x) (G r x))) (fun _ => rfl)
  rw [h1, h2]
  exact le_trans h3 (le_of_eq (by rw [hprod]))

end Work.Diff.EXT.evolX
