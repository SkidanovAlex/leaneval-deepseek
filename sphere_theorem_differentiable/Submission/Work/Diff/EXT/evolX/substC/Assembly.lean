import Mathlib
import Submission.Work.Diff.EXT.evolX.substB.Defs
import Submission.Work.Diff.EXT.evolX.Stw_extStep
import Submission.Work.Diff.EXT.evolX.Stw_bound
import Submission.Work.Diff.EXT.evolX.substOp_eq_SOp_comp
import Submission.Work.Diff.EXT.evolX.pairVecZskStrongAtB
import Submission.Work.Diff.EXT.evolX.pairVecZskJetSmooth
import Submission.Work.Diff.EXT.evolX.jetAllPrecomp
import Submission.Work.Diff.EXT.evolX.sumWordsChoose
import Submission.Work.Diff.EXT.evolX.ladderEf_base
import Submission.Work.Diff.GE.dRicPhi_eq_sum_covRm

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.evolX.substC

/-! ## 1. The ladder identity (own copy) -/

theorem jetAll_SOp_eq_sumC
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M) {K : ℕ}
    (V : (Fin 2 → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (U : (Fin K → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (hVs : Work.Diff.EXT.JetSmoothOp (I := I) (M := M) g 3
      (pairVec (I := I) (M := M) g V) x)
    (hUs : Work.Diff.EXT.JetSmoothOp (I := I) (M := M) g (K + 1)
      (pairVec (I := I) (M := M) g U) x)
    (hstep : ∀ (a : ℕ) (w : Word a)
      (F : Fin (K + 2 + (a + 1)) → Work.Diff.EXT.TField (I := I) (M := M)),
        (∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i)) →
        Filter.EventuallyEq (nhds x)
          (fun y : M => Work.Diff.EXT.extStep (I := I) (M := M) g
            (Stw (I := I) (M := M) g V U a w) F y)
          (fun y : M => Stw (I := I) (M := M) g V U (a + 1)
              (Word.cons true w) F y
            + Stw (I := I) (M := M) g V U (a + 1) (Word.cons false w) F y))
    (a : ℕ) (F : Fin (K + 2 + a) → Work.Diff.EXT.TField (I := I) (M := M))
    (hF : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i)) :
    Filter.EventuallyEq (nhds x)
      (fun y : M => Work.Diff.EXT.jetAll g a (K + 2) (SOp (I := I) (M := M) g V U) F y)
      (fun y : M => Finset.univ.sum (fun w : Word a =>
        Stw (I := I) (M := M) g V U a w F y)) := by
  classical
  induction a with
  | zero =>
      filter_upwards with y
      have huniv : (Finset.univ : Finset (Word 0)) = {Word.nil} :=
        Finset.eq_singleton_iff_unique_mem.mpr
          ⟨Finset.mem_univ _, fun b _ => Subsingleton.elim b Word.nil⟩
      show SOp (I := I) (M := M) g V U F y
        = ∑ w : Word 0, Stw (I := I) (M := M) g V U 0 w F y
      rw [huniv, Finset.sum_singleton]
      exact (congrFun (stb_Stw_zero (I := I) (M := M) g V U F) y).symm
  | succ l ih =>
      have htail : ∀ i : Fin (K + 2 + l), Work.Diff.EXT.SmoothF (I := I) (M := M)
          ((fun t : Fin (K + 2 + l) => F t.succ) i) := fun i => hF i.succ
      have h1 : Work.Diff.EXT.extStep (I := I) (M := M) g
            (Work.Diff.EXT.jetAll g l (K + 2) (SOp (I := I) (M := M) g V U)) F
          =ᶠ[nhds x] Work.Diff.EXT.extStep (I := I) (M := M) g
            (fun (G : Fin (K + 2 + l) → Work.Diff.EXT.TField (I := I) (M := M)) (y : M) =>
              Finset.univ.sum (fun w : Word l => Stw (I := I) (M := M) g V U l w G y)) F :=
        Work.Diff.EXT.extStep_congr_at (I := I) (M := M) g _ _ F x
          (ih (fun t : Fin (K + 2 + l) => F t.succ) htail)
          (fun s => ih (Function.update (fun t : Fin (K + 2 + l) => F t.succ) s
              (Work.Diff.EXT.dirF g ((fun t : Fin (K + 2 + l) => F t.succ) s) (F 0)))
            (Work.Diff.EXT.smoothF_update' htail s
              (Work.Diff.EXT.dirF_smooth (I := I) (M := M) hLC g (htail s) (hF 0))))
      have h2 := stb_extStep_sum (I := I) (M := M) hLC g x V U hVs hUs l F hF
      have h3 : (fun y : M => Finset.univ.sum (fun w : Word l =>
            Work.Diff.EXT.extStep (I := I) (M := M) g (Stw (I := I) (M := M) g V U l w) F y))
          =ᶠ[nhds x] (fun y : M => Finset.univ.sum (fun w' : Word (l + 1) =>
            Stw (I := I) (M := M) g V U (l + 1) w' F y)) := by
        filter_upwards [Filter.eventually_all.mpr
          (fun w : Word l => hstep l w F hF)] with y hy
        rw [Finset.sum_congr rfl (fun w _ => hy w), stb_sum_cons g V U l F y]
      change (fun y : M => Work.Diff.EXT.extStep (I := I) (M := M) g
          (Work.Diff.EXT.jetAll g l (K + 2) (SOp (I := I) (M := M) g V U)) F y)
        =ᶠ[nhds x] (fun y : M => Finset.univ.sum (fun w' : Word (l + 1) =>
            Stw (I := I) (M := M) g V U (l + 1) w' F y))
      exact h1.trans (h2.trans h3)

/-! ## 2. The assembly of the jet bound for the contracted tower -/

/-- **The jet bound for the contracted tower.** -/
theorem substOp_jets_le_C
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    (k : ℕ) (s : Fin (k + 4)) (CT CV : ℕ → ℝ)
    (hCT : ∀ a, 0 ≤ CT a) (hCV : ∀ a, 0 ≤ CV a)
    (g : Submission.Diff.SMet I M) (x : M)
    (V : (Fin 2 → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (htower : Work.Diff.EXT.evolX.StrongAt g x k CT
      (Work.Diff.EXT.ckt (I := I) (M := M) g k))
    (hV : Work.Diff.EXT.evolX.StrongAt g x 1 CV
      (Work.Diff.EXT.evolX.pairOp (I := I) (M := M) g V))
    (hTs : Work.Diff.EXT.JetSmoothOp (I := I) (M := M) g (k + 4)
      (Work.Diff.EXT.ckt (I := I) (M := M) g k) x)
    (hVs : Work.Diff.EXT.JetSmoothOp (I := I) (M := M) g 3
      (Work.Diff.EXT.evolX.pairOp (I := I) (M := M) g V) x)
    (a : ℕ) (G : Fin ((k + 5) + a) → Work.Diff.EXT.TField (I := I) (M := M))
    (hG : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (G i)) :
    |Work.Diff.EXT.jetAll g a (k + 5)
        (Work.Diff.EXT.evolX.substOp (I := I) (M := M) g k s V) G x|
      ≤ (Finset.sum (Finset.range (a + 1))
            (fun b => ((Nat.choose a b : ℕ) : ℝ) * CT b * CV (a - b)))
        * Work.Diff.EXT.Shape g x (k + 1 + a)
        * Finset.univ.prod (fun r : Fin ((k + 5) + a) =>
            Real.sqrt (g.inner x (G r x) (G r x))) := by
  classical
  obtain ⟨W, hWs, hONev, -⟩ := Work.Diff.GE.exists_smooth_onframe (I := I) (M := M) g x
  have hUs : Work.Diff.EXT.JetSmoothOp (I := I) (M := M) g ((k + 3) + 1)
      (pairVec (I := I) (M := M) g (Zsk (I := I) (M := M) g W k s)) x :=
    pairVecZskJetSmooth (I := I) (M := M) hLC g x W hWs hONev s hTs
  have hUst : Work.Diff.EXT.evolX.StrongAt g x k CT
      (pairVec (I := I) (M := M) g (Zsk (I := I) (M := M) g W k s)) :=
    pairVecZskStrongAtB (I := I) (M := M) hLC g x W hWs hONev s hCT htower
  -- the permuted tuple
  set G' : Fin ((k + 5) + a) → Work.Diff.EXT.TField (I := I) (M := M) :=
    fun i => G (slotPerm (brhoEquiv k s) a i) with hG'def
  have hG'sf : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (G' i) := fun i => hG _
  -- the product over the permuted tuple
  have hprod_eq :
      Finset.univ.prod (fun r : Fin ((k + 5) + a) =>
          Real.sqrt (g.inner x (G' r x) (G' r x)))
        = Finset.univ.prod (fun r : Fin ((k + 5) + a) =>
            Real.sqrt (g.inner x (G r x) (G r x))) := by
    rw [hG'def]
    refine Fintype.prod_bijective (slotPerm (brhoEquiv k s) a)
      (precomp_slotPerm_bijective (brhoEquiv k s) a) _ _ (fun r => ?_)
    simp
  -- (1) locality: `substOp` agrees near `x` with `SOp` applied after `brho`
  have hgerm : ∀ (F : Fin (k + 5) → Work.Diff.EXT.TField (I := I) (M := M)),
      (∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i)) →
      (fun y : M => SOp (I := I) (M := M) g V (Zsk (I := I) (M := M) g W k s)
        (fun i : Fin (k + 5) => F (brho k s i)) y)
      =ᶠ[nhds x] (fun y : M => substOp (I := I) (M := M) g k s V F y) :=
    fun F hF => substOp_eq_SOp_comp (I := I) (M := M) g x k s V W hWs hONev F hF
  have hloc : Work.Diff.EXT.jetAll g a (k + 5)
        (Work.Diff.EXT.evolX.substOp (I := I) (M := M) g k s V) G x
      = Work.Diff.EXT.jetAll g a (k + 5)
          (fun (F : Fin (k + 5) → Work.Diff.EXT.TField (I := I) (M := M)) (y : M) =>
            SOp (I := I) (M := M) g V (Zsk (I := I) (M := M) g W k s)
              (fun i : Fin (k + 5) => F (brho k s i)) y) G x :=
    (jetAll_congr_of_eventuallyEq_smooth' (I := I) (M := M) hLC (x := x) hgerm G hG).symm
  -- (2) the slot permutation
  have hprec : Work.Diff.EXT.jetAll g a (k + 5)
        (fun (F : Fin (k + 5) → Work.Diff.EXT.TField (I := I) (M := M)) (y : M) =>
          SOp (I := I) (M := M) g V (Zsk (I := I) (M := M) g W k s)
            (fun i : Fin (k + 5) => F (brho k s i)) y) G x
      = Work.Diff.EXT.jetAll g a (k + 5)
          (SOp (I := I) (M := M) g V (Zsk (I := I) (M := M) g W k s)) G' x := by
    rw [hG'def]
    exact congrFun (jetAllPrecomp (I := I) (M := M) g (brhoEquiv k s)
      (SOp (I := I) (M := M) g V (Zsk (I := I) (M := M) g W k s)) a G) x
  -- (3) the ladder identity
  have hstep : ∀ (n : ℕ) (w : Word n)
      (F : Fin ((k + 3) + 2 + (n + 1)) → Work.Diff.EXT.TField (I := I) (M := M)),
      (∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i)) →
      Filter.EventuallyEq (nhds x)
        (fun y : M => Work.Diff.EXT.extStep (I := I) (M := M) g
          (Stw (I := I) (M := M) g V (Zsk (I := I) (M := M) g W k s) n w) F y)
        (fun y : M => Stw (I := I) (M := M) g V (Zsk (I := I) (M := M) g W k s) (n + 1)
            (Word.cons true w) F y
          + Stw (I := I) (M := M) g V (Zsk (I := I) (M := M) g W k s) (n + 1)
            (Word.cons false w) F y) :=
    fun n w F hF => Stw_extStep (I := I) (M := M) hLC g x V
      (Zsk (I := I) (M := M) g W k s) hVs hUs n w F hF
  have hlad := jetAll_SOp_eq_sumC (I := I) (M := M) hLC g x V
    (Zsk (I := I) (M := M) g W k s) hVs hUs hstep a G' hG'sf
  have hsum : Work.Diff.EXT.jetAll g a (k + 5)
        (SOp (I := I) (M := M) g V (Zsk (I := I) (M := M) g W k s)) G' x
      = ∑ w : Word a, Stw (I := I) (M := M) g V (Zsk (I := I) (M := M) g W k s) a w G' x :=
    hlad.eq_of_nhds
  -- (4) the per-state bound
  have hb : ∀ w : Word a,
      |Stw (I := I) (M := M) g V (Zsk (I := I) (M := M) g W k s) a w G' x|
        ≤ CT (wCntT w) * CV (wCntF w)
          * Real.sqrt (Work.Diff.EXT.curvNormK g x (k + wCntT w))
          * Real.sqrt (Work.Diff.EXT.curvNormK g x (1 + wCntF w))
          * Finset.univ.prod (fun r : Fin ((k + 5) + a) =>
              Real.sqrt (g.inner x (G' r x) (G' r x))) :=
    fun w => Stw_bound (I := I) (M := M) hLC g x V (Zsk (I := I) (M := M) g W k s)
      hVs hUs hCV hCT 1 k hV hUst a w G' hG'sf
  have hP0 : 0 ≤ Finset.univ.prod (fun r : Fin ((k + 5) + a) =>
      Real.sqrt (g.inner x (G' r x) (G' r x))) :=
    Finset.prod_nonneg fun r _ => Real.sqrt_nonneg _
  have hterm : ∀ w : Word a,
      CT (wCntT w) * CV (wCntF w)
        * Real.sqrt (Work.Diff.EXT.curvNormK g x (k + wCntT w))
        * Real.sqrt (Work.Diff.EXT.curvNormK g x (1 + wCntF w))
        * Finset.univ.prod (fun r : Fin ((k + 5) + a) =>
            Real.sqrt (g.inner x (G' r x) (G' r x)))
      ≤ CT (wCntT w) * CV (a - wCntT w) * Work.Diff.EXT.Shape g x (k + 1 + a)
        * Finset.univ.prod (fun r : Fin ((k + 5) + a) =>
            Real.sqrt (g.inner x (G' r x) (G' r x))) := by
    intro w
    have hshape := Work.Diff.EXT.sqrt_mul_sqrt_le_Shape (I := I) (M := M) g x
      (a := k + wCntT w) (b := 1 + wCntF w) (m := k + 1 + a)
      (by have hw := Work.Diff.EXT.evolX.wCntT_add_wCntF w
          simp only [Work.Diff.EXT.evolX.wCntF_eq w] at *
          omega)
    rw [Work.Diff.EXT.evolX.wCntF_eq w] at hshape
    rw [Work.Diff.EXT.evolX.wCntF_eq w]
    calc CT (wCntT w) * CV (a - wCntT w)
          * Real.sqrt (Work.Diff.EXT.curvNormK g x (k + wCntT w))
          * Real.sqrt (Work.Diff.EXT.curvNormK g x (1 + (a - wCntT w)))
          * Finset.univ.prod (fun r : Fin ((k + 5) + a) =>
              Real.sqrt (g.inner x (G' r x) (G' r x)))
        = (CT (wCntT w) * CV (a - wCntT w))
            * (Real.sqrt (Work.Diff.EXT.curvNormK g x (k + wCntT w))
              * Real.sqrt (Work.Diff.EXT.curvNormK g x (1 + (a - wCntT w))))
            * Finset.univ.prod (fun r : Fin ((k + 5) + a) =>
                Real.sqrt (g.inner x (G' r x) (G' r x))) := by ring
      _ ≤ (CT (wCntT w) * CV (a - wCntT w)) * Work.Diff.EXT.Shape g x (k + 1 + a)
            * Finset.univ.prod (fun r : Fin ((k + 5) + a) =>
                Real.sqrt (g.inner x (G' r x) (G' r x))) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hshape (mul_nonneg (hCT _) (hCV _))) hP0
      _ = CT (wCntT w) * CV (a - wCntT w) * Work.Diff.EXT.Shape g x (k + 1 + a)
            * Finset.univ.prod (fun r : Fin ((k + 5) + a) =>
                Real.sqrt (g.inner x (G' r x) (G' r x))) := by ring
  -- (5) the arithmetic of the word sum
  have hsum_eq : (∑ w : Word a, CT (wCntT w) * CV (a - wCntT w)
        * Work.Diff.EXT.Shape g x (k + 1 + a)
        * Finset.univ.prod (fun r : Fin ((k + 5) + a) =>
            Real.sqrt (g.inner x (G' r x) (G' r x))))
      = (Finset.sum (Finset.range (a + 1))
            (fun b => ((Nat.choose a b : ℕ) : ℝ) * CT b * CV (a - b)))
        * Work.Diff.EXT.Shape g x (k + 1 + a)
        * Finset.univ.prod (fun r : Fin ((k + 5) + a) =>
            Real.sqrt (g.inner x (G r x) (G r x))) := by
    rw [sumWordsChoose a (fun b => CT b * CV (a - b) * Work.Diff.EXT.Shape g x (k + 1 + a)
      * Finset.univ.prod (fun r : Fin ((k + 5) + a) =>
          Real.sqrt (g.inner x (G' r x) (G' r x))))]
    rw [hprod_eq]
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  calc |Work.Diff.EXT.jetAll g a (k + 5)
        (Work.Diff.EXT.evolX.substOp (I := I) (M := M) g k s V) G x|
      = |∑ w : Word a,
          Stw (I := I) (M := M) g V (Zsk (I := I) (M := M) g W k s) a w G' x| := by
        rw [hloc, hprec, hsum]
    _ ≤ ∑ w : Word a,
          |Stw (I := I) (M := M) g V (Zsk (I := I) (M := M) g W k s) a w G' x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ w : Word a,
          CT (wCntT w) * CV (wCntF w)
            * Real.sqrt (Work.Diff.EXT.curvNormK g x (k + wCntT w))
            * Real.sqrt (Work.Diff.EXT.curvNormK g x (1 + wCntF w))
            * Finset.univ.prod (fun r : Fin ((k + 5) + a) =>
                Real.sqrt (g.inner x (G' r x) (G' r x))) :=
        Finset.sum_le_sum (fun w _ => hb w)
    _ ≤ ∑ w : Word a,
          CT (wCntT w) * CV (a - wCntT w) * Work.Diff.EXT.Shape g x (k + 1 + a)
            * Finset.univ.prod (fun r : Fin ((k + 5) + a) =>
                Real.sqrt (g.inner x (G' r x) (G' r x))) :=
        Finset.sum_le_sum (fun w _ => hterm w)
    _ = (Finset.sum (Finset.range (a + 1))
            (fun b => ((Nat.choose a b : ℕ) : ℝ) * CT b * CV (a - b)))
        * Work.Diff.EXT.Shape g x (k + 1 + a)
        * Finset.univ.prod (fun r : Fin ((k + 5) + a) =>
            Real.sqrt (g.inner x (G r x) (G r x))) := hsum_eq

end Work.Diff.EXT.evolX.substC
