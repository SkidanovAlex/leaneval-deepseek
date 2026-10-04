import Mathlib
import Submission.Work.Diff.EXT.curvDefs
import Submission.Work.Diff.EXT.curvDefs2
import Submission.Work.Diff.EXT.covK_linearL
import Submission.Work.Diff.EXT.covK_germ

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## Globalising a field which is smooth on a neighbourhood of the base point

Mathlib's `SmoothBumpFunction` gives smooth cut-off functions on a manifold supported in an
arbitrary neighbourhood of a point, and `ContMDiffOn.smul_section_of_tsupport` shows that the
product of such a cut-off with a section that is smooth on an open set containing its topological
support is globally smooth.  This globalises a field that is smooth on a neighbourhood of `x`. -/

/-- A field which is `C^∞` on a neighbourhood of `x` agrees near `x` with a globally `C^∞`
field.  (No `NormalSpace`/`SigmaCompactSpace` on `M` is needed: the cut-off is a `SmoothBumpFunction`
at `x` and no partition of unity is used.) -/
theorem SmoothNear.exists_global [T2Space M] {X : TField (I := I) (M := M)} {x : M}
    (hX : SmoothNear (I := I) (M := M) X x) :
    ∃ X' : TField (I := I) (M := M),
      SmoothTField (I := I) (M := M) X' ∧ X' =ᶠ[𝓝 x] X := by
  obtain ⟨U, hU, hXU⟩ := hX
  obtain ⟨ψ, -, hψ⟩ :
      ∃ ψ : SmoothBumpFunction I x, True ∧ tsupport (ψ : M → ℝ) ⊆ interior U :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
      (isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hU))
  refine ⟨(ψ : M → ℝ) • X, ?_, ?_⟩
  · exact ContMDiffOn.smul_section_of_tsupport (V := TangentSpace I) ψ.contMDiff.contMDiffOn
      isOpen_interior hψ (hXU.mono interior_subset)
  · filter_upwards [ψ.eventuallyEq_one] with y hy
    rw [Pi.smul_apply', hy, Pi.one_apply, one_smul]

/-- Version of `SmoothNear.exists_global` for a finite family of fields. -/
theorem SmoothNear.exists_global_family [T2Space M] {ι : Type*}
    {X : ι → TField (I := I) (M := M)} {x : M}
    (hX : ∀ i, SmoothNear (I := I) (M := M) (X i) x) :
    ∃ X' : ι → TField (I := I) (M := M),
      (∀ i, SmoothTField (I := I) (M := M) (X' i)) ∧ ∀ i, X' i =ᶠ[𝓝 x] X i := by
  have h : ∀ i, ∃ W : TField (I := I) (M := M),
      SmoothTField (I := I) (M := M) W ∧ W =ᶠ[𝓝 x] X i :=
    fun i => (hX i).exists_global
  choose W hW using h
  exact ⟨W, fun i => (hW i).1, fun i => (hW i).2⟩

/-! ## Value dependence of the iteration `ckt` for globally smooth tuples

This is `Work.Diff.EXT.ckt_val_dep_all` of `Submission/Work/Diff/EXT/covKRmExt_tensorial.lean`,
transported to the present import set (which contains the `L`-variant of the iteration). -/

/-- **Value dependence of the iteration in all slots at once.**  If two `(k+4)`-tuples of globally
smooth fields have the same values at `x`, then the values of the `k`-th iterate `ckt` at `x`
agree. -/
theorem ckt_valueDep_all [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (k : ℕ) (x : M) {F F' : Fin (k + 4) → TField (I := I) (M := M)}
    (hF : ∀ s, SmoothF (F s))
    (hF' : ∀ s, SmoothF (F' s))
    (h : ∀ s, F s x = F' s x) :
    ckt g k F x = ckt g k F' x := by
  -- the hybrid tuple: the slots in `t` are taken from `F'`, the others from `F`
  set H : Finset (Fin (k + 4)) → (Fin (k + 4) → TField (I := I) (M := M)) :=
    fun t s => if s ∈ t then F' s else F s with hHdef
  have hH : ∀ t s, SmoothF (H t s) := by
    intro t s
    rw [hHdef]
    by_cases hs : s ∈ t
    · simp only [ite_eq_left hs]
      exact hF' s
    · simp only [ite_eq_right hs]
      exact hF s
  have hHself : ∀ t s, s ∉ t → H t s = F s := by
    intro t s hs
    rw [hHdef]
    simp only [ite_eq_right hs]
  -- replacing one more slot of the hybrid tuple does not change the value at `x`
  have hstep : ∀ (t : Finset (Fin (k + 4))) (s : Fin (k + 4)), s ∉ t →
      ckt g k (H t) x = ckt g k (H (insert s t)) x := by
    intro t s hs
    have hupd : H (insert s t) = Function.update (H t) s (F' s) := by
      funext u
      simp only [hHdef, Function.update_apply]
      by_cases hu : u = s
      · subst hu
        simp
      · rw [ite_eq_right hu]
        simp only [Finset.mem_insert, hu, false_or]
    rw [hupd]
    have hsd := ckt_val_dep hLC g k x (hH t) s (hF s) (hF' s) (h s)
    have hsame : Function.update (H t) s (F s) = H t := by
      funext u
      rw [Function.update_apply]
      by_cases hu : u = s
      · rw [ite_eq_left hu, hu]
        exact (hHself t s hs).symm
      · rw [ite_eq_right hu]
    rwa [hsame] at hsd
  have hchain : ckt g k (H ∅) x = ckt g k (H Finset.univ) x :=
    Finset.induction_on (motive := fun t => ckt g k (H ∅) x = ckt g k (H t) x)
      (Finset.univ : Finset (Fin (k + 4))) rfl
      (fun a t ha ih => by rw [ih, hstep t a ha])
  have h0 : H ∅ = F := by
    funext s
    simp [hHdef]
  have h1 : H Finset.univ = F' := by
    funext s
    simp [hHdef]
  rwa [h0, h1] at hchain

/-- **Tensoriality of `∇^k Rm` for globally smooth tuples.**  If two tuples of globally smooth
fields have the same values at `x`, then `covKRmExt g k` takes the same value at `x` on them. -/
theorem covKRmExt_valueDep_global [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (k : ℕ) (x : M)
    (v v' : Fin k → TField (I := I) (M := M))
    (A A' B B' C C' D D' : TField (I := I) (M := M))
    (hv : ∀ i, SmoothF (v i)) (hv' : ∀ i, SmoothF (v' i))
    (hA : SmoothF A) (hA' : SmoothF A')
    (hB : SmoothF B) (hB' : SmoothF B')
    (hC : SmoothF C) (hC' : SmoothF C')
    (hD : SmoothF D) (hD' : SmoothF D')
    (hvv : ∀ i, v i x = v' i x) (hAA : A x = A' x) (hBB : B x = B' x)
    (hCC : C x = C' x) (hDD : D x = D' x) :
    covKRmExt g k v A B C D x = covKRmExt g k v' A' B' C' D' x := by
  have hFs : ∀ s, SmoothF ((mkT v (quadF A B C D)) s) := by
    intro s
    refine Fin.addCases ?_ ?_ s
    · intro i
      rw [mkT_castAdd]
      exact hv i
    · intro p
      rw [mkT_natAdd]
      fin_cases p
      · simpa using hA
      · simpa using hB
      · simpa using hC
      · simpa using hD
  have hFs' : ∀ s, SmoothF ((mkT v' (quadF A' B' C' D')) s) := by
    intro s
    refine Fin.addCases ?_ ?_ s
    · intro i
      rw [mkT_castAdd]
      exact hv' i
    · intro p
      rw [mkT_natAdd]
      fin_cases p
      · simpa using hA'
      · simpa using hB'
      · simpa using hC'
      · simpa using hD'
  have hvals : ∀ s, (mkT v (quadF A B C D)) s x = (mkT v' (quadF A' B' C' D')) s x := by
    intro s
    refine Fin.addCases ?_ ?_ s
    · intro i
      rw [mkT_castAdd, mkT_castAdd]
      exact hvv i
    · intro p
      rw [mkT_natAdd, mkT_natAdd]
      fin_cases p
      · simpa using hAA
      · simpa using hBB
      · simpa using hCC
      · simpa using hDD
  have hthis : ckt g k (mkT v (quadF A B C D)) x = ckt g k (mkT v' (quadF A' B' C' D')) x :=
    ckt_valueDep_all hLC g k x hFs hFs' hvals
  rwa [ckt_quadF, ckt_quadF] at hthis

/-- **Value-dependence (tensoriality) of `∇^k Rm` for fields smooth on a neighbourhood of `x`**
(`KrValueDepN`, see `Submission/Work/Diff/EXT/curvDefs2.lean`): if two tuples of tangent fields are
each smooth on a neighbourhood of `x` and have the same values at `x`, then `covKRmExt g k` takes the
same value at `x` on them.  Assumes the field-level linearity `KrLinear g k` (proved as
`covK_linearL`) and the germ-locality `KrGerm g k` (proved as `covK_germ`).

ROUTE (see the review for details):

* `Work.Diff.EXT.covKRmExt_tensorial` (this directory, sorry-free) already gives steps (1) and (3)
  for *globally* smooth tuples: check its exact statement first and reuse it.
* "Killing": for a globally smooth tuple `F` and a globally smooth `Z` with `Z x = 0`, the value
  `covKRmExt g k (split (update F s Z)) x` is `0`: in the chart at `x` write
  `Z = ∑ j, f j • σ j` near `x` (`σ j` the chart frame, smooth on the chart source, a basis there)
  and use `KrLinear`'s homogeneity with the coefficient `f j x = 0`.
* Globalise fields that are only smooth on a neighbourhood of `x`: pull a bump function on `E` back
  through the chart at `x` (`ContDiffBump`; NOTE the review's warning that
  `exists_contMDiffMap_one_nhds_of_subset_interior` needs `[NormalSpace M] [SigmaCompactSpace M]`,
  which are NOT available here, so a chart-local bump must be used).  Then apply `KrGerm` to compare
  with the original fields, and finish with the globally smooth case. -/
theorem covK_valueDepN
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [T2Space M] (hLC : Submission.Diff.LCSmooth I M)
    (g : Submission.Diff.SMet I M) (k : ℕ)
    (hL : KrLinear (I := I) (M := M) g k) (hG : KrGerm (I := I) (M := M) g k) :
    KrValueDepN (I := I) (M := M) g k := by
  -- The field-level linearity `hL` is not needed below: it is the ingredient from which the
  -- single-slot value dependence `Work.Diff.EXT.ckt_val_dep` (module `covK_linearL`) is derived,
  -- and that lemma is what is actually used to prove the globally smooth case here.
  intro V V' A A' B B' C C' D D' x hV hV' hA hA' hB hB' hC hC' hD hD'
    hv hAA hBB hCC hDD
  -- globalise every field, keeping its germ at `x`
  obtain ⟨Vg, hVgS, hVgE⟩ := SmoothNear.exists_global_family (ι := Fin k) hV
  obtain ⟨Vg', hVg'S, hVg'E⟩ := SmoothNear.exists_global_family (ι := Fin k) hV'
  obtain ⟨Ag, hAgS, hAgE⟩ := hA.exists_global
  obtain ⟨Ag', hAg'S, hAg'E⟩ := hA'.exists_global
  obtain ⟨Bg, hBgS, hBgE⟩ := hB.exists_global
  obtain ⟨Bg', hBg'S, hBg'E⟩ := hB'.exists_global
  obtain ⟨Cg, hCgS, hCgE⟩ := hC.exists_global
  obtain ⟨Cg', hCg'S, hCg'E⟩ := hC'.exists_global
  obtain ⟨Dg, hDgS, hDgE⟩ := hD.exists_global
  obtain ⟨Dg', hDg'S, hDg'E⟩ := hD'.exists_global
  -- replace the fields by their globalisations using germ-locality
  have e1 : covKRmExt g k V A B C D x = covKRmExt g k Vg Ag Bg Cg Dg x :=
    hG V Vg A Ag B Bg C Cg D Dg x
      (fun j => (hV j).smoothAt) (fun j => (SmoothTField.smoothNear (hVgS j) x).smoothAt)
      hA.smoothAt (SmoothTField.smoothNear hAgS x).smoothAt
      hB.smoothAt (SmoothTField.smoothNear hBgS x).smoothAt
      hC.smoothAt (SmoothTField.smoothNear hCgS x).smoothAt
      hD.smoothAt (SmoothTField.smoothNear hDgS x).smoothAt
      (fun j => (hVgE j).symm) hAgE.symm hBgE.symm hCgE.symm hDgE.symm
  have e2 : covKRmExt g k V' A' B' C' D' x = covKRmExt g k Vg' Ag' Bg' Cg' Dg' x :=
    hG V' Vg' A' Ag' B' Bg' C' Cg' D' Dg' x
      (fun j => (hV' j).smoothAt) (fun j => (SmoothTField.smoothNear (hVg'S j) x).smoothAt)
      hA'.smoothAt (SmoothTField.smoothNear hAg'S x).smoothAt
      hB'.smoothAt (SmoothTField.smoothNear hBg'S x).smoothAt
      hC'.smoothAt (SmoothTField.smoothNear hCg'S x).smoothAt
      hD'.smoothAt (SmoothTField.smoothNear hDg'S x).smoothAt
      (fun j => (hVg'E j).symm) hAg'E.symm hBg'E.symm hCg'E.symm hDg'E.symm
  rw [e1, e2]
  -- the globally smooth case
  exact covKRmExt_valueDep_global hLC g k x Vg Vg' Ag Ag' Bg Bg' Cg Cg' Dg Dg'
    hVgS hVg'S hAgS hAg'S hBgS hBg'S hCgS hCg'S hDgS hDg'S
    (fun j => by rw [(hVgE j).eq_of_nhds, (hVg'E j).eq_of_nhds]; exact hv j)
    (by rw [hAgE.eq_of_nhds, hAg'E.eq_of_nhds]; exact hAA)
    (by rw [hBgE.eq_of_nhds, hBg'E.eq_of_nhds]; exact hBB)
    (by rw [hCgE.eq_of_nhds, hCg'E.eq_of_nhds]; exact hCC)
    (by rw [hDgE.eq_of_nhds, hDg'E.eq_of_nhds]; exact hDD)

end Work.Diff.EXT
