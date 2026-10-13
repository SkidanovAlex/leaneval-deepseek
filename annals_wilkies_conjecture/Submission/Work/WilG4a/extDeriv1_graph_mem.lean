import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.Calc.lt_mem
import Submission.Work.WilG4b.posPoly_mem
import Submission.Work.WilG4a.diffLocus_mem
import Submission.Work.WilG4a.Cells
import Submission.Work.WilG4b.thrSet_mem

namespace Work.WilG4a

open WilkiesDesign WilkiesConjecture

/-!
  `Work.WilG4a.extDeriv1_graph_mem`.

  For a one-variable function `g` whose graph is `Ω F D 2`-definable in a sharply o-minimal
  structure with sharp derivatives, the graph of `deriv g` extended by `0` off the `C¹`-locus
  is `Ω`-definable, with format and degree depending only on `F` and `D`.

  The set displayed in the statement splits as `A ∪ B` with

  * `A = {z | DifferentiableAt ℝ g (z 0) ∧ z 1 = deriv g (z 0)} ∩ {z | ContDiffAt ℝ 1 g (z 0)}`
    — this is exactly the set produced by `S.SharpDeriv` applied to `g` in dimension `1`
    (the `C¹`-locus is open, so it coincides with the interior of the `C¹`-locus, and the
    first-order partial derivative in the single direction is `deriv`);
  * `B = {z | ¬ ContDiffAt ℝ 1 g (z 0) ∧ z 1 = 0}` — the complement of the `C¹`-locus
    (an `Ω`-set, since it is the complement of the projection of the sharp-derivative set)
    lifted to `ℝ²`, intersected with the hyperplane `z 1 = 0`.

  The bookkeeping is: `B` needs three extra format steps (projection, complement, product)
  and one intersection step, whence `a + 4`; the degree is `P + (P + 1)` where `P` is the
  polynomial in `D` produced by `S.SharpDeriv`.
-/

/-- `(Fin.init z) 0 = z 0` for `z : Fin 2 → ℝ`. -/
lemma extDeriv1_fin_init_apply_zero (z : Fin 2 → ℝ) : (Fin.init z) 0 = z 0 := rfl

/-- The interior of the `C¹`-locus of a one-variable function, in `ℝ¹`-coordinates. -/
def extDeriv1_smoothLocus (g : ℝ → ℝ) : Set (Fin 1 → ℝ) :=
  interior {x : Fin 1 → ℝ | ContDiffAt ℝ 1 (Work.WilG4b.thrDinG g) x}

/-- The `SharpDeriv` set for `g`: the graph of `∂₀ (y ↦ g (y 0))` over the interior of the
`C¹`-locus (the set that `S.SharpDeriv` exhibits as an `Ω`-set). -/
def extDeriv1_graphSet (g : ℝ → ℝ) : Set (Fin 2 → ℝ) :=
  {z | Fin.init z ∈ extDeriv1_smoothLocus g ∧
    z (Fin.last 1) = iteratedFDeriv ℝ 1 (Work.WilG4b.thrDinG g) (Fin.init z)
      (fun _ : Fin 1 => Pi.single (0 : Fin 1) 1)}

/-- Projecting the sharp-derivative set forgets the value of the derivative. -/
lemma extDeriv1_projLast_graphSet (g : ℝ → ℝ) :
    projLast (extDeriv1_graphSet g) = extDeriv1_smoothLocus g := by
  ext x
  constructor
  · rintro ⟨t, ht⟩
    simpa only [extDeriv1_graphSet, Set.mem_ofPred_eq, Fin.init_snoc] using ht.1
  · intro hx
    refine ⟨iteratedFDeriv ℝ 1 (Work.WilG4b.thrDinG g) x
      (fun _ : Fin 1 => Pi.single (0 : Fin 1) 1), ?_⟩
    simp only [extDeriv1_graphSet, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last]
    exact ⟨hx, trivial⟩

/-- The "good" part of the extension is exactly the sharp-derivative set: the `C¹`-locus is
open, so it agrees with the interior of the `C¹`-locus. -/
lemma extDeriv1_good_eq (g : ℝ → ℝ) :
    ({z : Fin 2 → ℝ | DifferentiableAt ℝ g (z 0) ∧ z 1 = deriv g (z 0)} ∩
      {z : Fin 2 → ℝ | ContDiffAt ℝ 1 g (z 0)}) = extDeriv1_graphSet g := by
  ext z
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, extDeriv1_graphSet, extDeriv1_smoothLocus]
  constructor
  · rintro ⟨⟨hd, hz1⟩, hc⟩
    have hc' : ContDiffAt ℝ 1 g ((Fin.init z) 0) := by
      rwa [extDeriv1_fin_init_apply_zero]
    refine ⟨(Work.WilG4b.thrMem_interior_c1 g (Fin.init z)).2 hc', ?_⟩
    rw [Work.WilG4b.thrIteratedFDeriv g (Fin.init z) hc']
    rw [extDeriv1_fin_init_apply_zero]
    exact hz1
  · rintro ⟨hint, hlast⟩
    have hc : ContDiffAt ℝ 1 g (z 0) := (Work.WilG4b.thrMem_interior_c1 g (Fin.init z)).1 hint
    refine ⟨⟨hc.differentiableAt_one, ?_⟩, hc⟩
    rw [← extDeriv1_fin_init_apply_zero (z := z)]
    rw [← Work.WilG4b.thrIteratedFDeriv g (Fin.init z)
      (by rwa [extDeriv1_fin_init_apply_zero])]
    exact hlast

/-- The "bad" part of the extension: the complement of the `C¹`-locus in the first
coordinate, intersected with the zero hyperplane in the second. -/
lemma extDeriv1_bad_eq (g : ℝ → ℝ) :
    ({z : Fin 2 → ℝ | ¬ ContDiffAt ℝ 1 g (z 0) ∧ z 1 = 0}) =
      ({z : Fin 2 → ℝ | Fin.init z ∈ (extDeriv1_smoothLocus g)ᶜ}
        ∩ {z : Fin 2 → ℝ | z 1 = 0}) := by
  ext z
  simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq, extDeriv1_smoothLocus]
  rw [Work.WilG4b.thrMem_interior_c1 g (Fin.init z)]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rwa [← extDeriv1_fin_init_apply_zero (z := z)] at h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rwa [extDeriv1_fin_init_apply_zero] at h1, h2⟩

/-- The hyperplane `z 1 = 0` in `ℝ²`. -/
lemma extDeriv1_lastCoord_zero_mem (S : WilkiesDesign.SOMin) :
    {z : Fin 2 → ℝ | z 1 = 0} ∈ S.Ω 2 1 2 := by
  have h := S.hyp 2 (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℝ)
  rw [MvPolynomial.totalDegree_X] at h
  convert h using 2
  ext z
  simp [MvPolynomial.eval_X]

theorem extDeriv1_graph_mem (S : WilkiesDesign.SOMin) (hder : S.SharpDeriv) (F : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (D : ℕ) (g : ℝ → ℝ),
      WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2 →
      (({z : Fin 2 → ℝ | DifferentiableAt ℝ g (z 0) ∧ z 1 = deriv g (z 0)} ∩
        {z : Fin 2 → ℝ | ContDiffAt ℝ 1 g (z 0)}) ∪
        {z : Fin 2 → ℝ | ¬ ContDiffAt ℝ 1 g (z 0) ∧ z 1 = 0}) ∈ S.Ω a (b.eval D) 2 := by
  obtain ⟨a, b, hb⟩ := hder F 1
  refine ⟨a + 4, Work.WilG1.psubst b 1 + (Work.WilG1.psubst b 1 + Polynomial.C 1), ?_⟩
  intro D g hg
  have hPeval : (Work.WilG1.psubst b 1).eval D = MvPolynomial.eval ![D, 1] b :=
    Work.WilG1.eval_psubst b 1 D
  have hSd : extDeriv1_graphSet g ∈ S.Ω a ((Work.WilG1.psubst b 1).eval D) 2 := by
    rw [hPeval]
    exact hb D (fun y : Fin 1 → ℝ => g (y 0)) hg 1 (fun _ : Fin 1 => (0 : Fin 1))
  have hA : ({z : Fin 2 → ℝ | DifferentiableAt ℝ g (z 0) ∧ z 1 = deriv g (z 0)} ∩
      {z : Fin 2 → ℝ | ContDiffAt ℝ 1 g (z 0)}) ∈ S.Ω a ((Work.WilG1.psubst b 1).eval D) 2 := by
    rw [extDeriv1_good_eq g]; exact hSd
  have hA' : ({z : Fin 2 → ℝ | DifferentiableAt ℝ g (z 0) ∧ z 1 = deriv g (z 0)} ∩
      {z : Fin 2 → ℝ | ContDiffAt ℝ 1 g (z 0)})
      ∈ S.Ω (a + 4) ((Work.WilG1.psubst b 1).eval D) 2 :=
    Work.WilG1.Omega.mono hA (by omega) le_rfl
  have hproj : projLast (extDeriv1_graphSet g)
      ∈ S.Ω (a + 1) ((Work.WilG1.psubst b 1).eval D) 1 :=
    S.proj hSd
  have hproj' : extDeriv1_smoothLocus g ∈ S.Ω (a + 1) ((Work.WilG1.psubst b 1).eval D) 1 := by
    rw [← extDeriv1_projLast_graphSet g]; exact hproj
  have hcompl : (extDeriv1_smoothLocus g)ᶜ ∈ S.Ω (a + 2) ((Work.WilG1.psubst b 1).eval D) 1 :=
    S.compl hproj'
  have hlift : {z : Fin 2 → ℝ | Fin.init z ∈ (extDeriv1_smoothLocus g)ᶜ}
      ∈ S.Ω (a + 3) ((Work.WilG1.psubst b 1).eval D) 2 :=
    S.prod_right hcompl
  have hzero : {z : Fin 2 → ℝ | z 1 = 0} ∈ S.Ω (a + 3) ((Polynomial.C 1).eval D) 2 := by
    have h1 : {z : Fin 2 → ℝ | z 1 = 0} ∈ S.Ω 2 ((Polynomial.C 1).eval D) 2 := by
      simpa using extDeriv1_lastCoord_zero_mem S
    exact Work.WilG1.Omega.mono h1 (by omega) le_rfl
  have hbad0 := Work.WilG1.Omega.inter₂ hlift hzero
  have hbad : ({z : Fin 2 → ℝ | Fin.init z ∈ (extDeriv1_smoothLocus g)ᶜ}
        ∩ {z : Fin 2 → ℝ | z 1 = 0})
      ∈ S.Ω (a + 4) ((Work.WilG1.psubst b 1 + Polynomial.C 1).eval D) 2 :=
    Work.WilG1.Omega.mono hbad0 (by simp only [max_self]; omega) le_rfl
  have hbad' : ({z : Fin 2 → ℝ | ¬ ContDiffAt ℝ 1 g (z 0) ∧ z 1 = 0})
      ∈ S.Ω (a + 4) ((Work.WilG1.psubst b 1 + Polynomial.C 1).eval D) 2 := by
    rw [extDeriv1_bad_eq g]; exact hbad
  have hu := Work.WilG1.Omega.union₂ hA' hbad'
  exact Work.WilG1.Omega.mono hu (by simp only [max_self]; omega) le_rfl

end Work.WilG4a
