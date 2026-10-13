/-
  Subproject WilE9G / Assembly — the covering step of the final assembly.

  Given the per-basic ambient strata `LB`, the Lagrange strata `Ef` with their hitting sets `sf`,
  the null sets (instantiated at the chosen direction `c` and base point `Fin.init y`), and a point
  `y` in the projection of the component of `z₀` whose `P`-fibre is finite, one finds a pair
  `(i, j)` and a hitting point `q ∈ sf i j` such that `y` is the projection of the component of
  `Ef i j` through `q`, and such that that whole component projects into `P`.
-/
import Mathlib
import Submission.Work.WilE9G.Defs
import Submission.Work.WilE9G.Cover
import Submission.Work.WilE9G.Assembly.Defs
import Submission.Work.WilE9G.Assembly.Step1
import Submission.Work.WilE9G.Assembly.Step3
import Submission.Work.WilE9G.Assembly.ambCatX_props
import Submission.Work.WilE9G.Assembly.lagStratumAE_mem
import Submission.Work.WilE9G.Assembly.lagStratumAE_component_proj_subset
import Submission.Work.WilE9G.Assembly.stratProj_lagPoint
import Submission.Work.WilE9G.Assembly.FrozenAux

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Classical Topology Filter MeasureTheory
namespace Work.WilE9G

open WilkiesDesign WilkiesDesign.E Work.WilE9G.Lagrange
open Work.WilE9G.Assembly

/-- **The covering step.** -/
theorem cover_step' {n m : ℕ} (X X0 : SemiPf (n + (1 + m))) (z₀ : Fin (n + (1 + m)) → ℝ)
    (hX0set : X0.set = X.set) (hz0 : z₀ ∈ X0.set)
    (y : Fin (n + 1) → ℝ)
    (hy : y ∈ Work.WilE9.Sharp.stratProj '' connectedComponentIn X.set z₀)
    (hfin : (fibrePiece X z₀ (Fin.init y)).Finite)
    (LB : (i : Fin X0.basics.length) → List (AmbStratum (n + (1 + m))))
    (hLBunion : ∀ i, (⟨X0.r, X0.c, [X0.basics.get i]⟩ : SemiPf (n + (1 + m))).set
      = ⋃ S ∈ LB i, S.X.set)
    (hLBgood : ∀ (i : Fin X0.basics.length) (S : AmbStratum (n + (1 + m))),
      S ∈ LB i → S.Good)
    (c : Fin (1 + m) → ℝ)
    (Ef : (i : Fin X0.basics.length) → (j : Fin (LB i).length) →
      Work.WilE9.Sharp.EffStratum n (m + ((LB i).get j).j + 1))
    (hEf_eq : ∀ (i : Fin X0.basics.length) (j : Fin (LB i).length),
      Ef i j = lagStratumAE (ambCatX ((LB i).get j) X0)
        (Work.WilE7.EAPoly.inr (r₁ := ((LB i).get j).X.r) (X0.basics.get i).pos.prod) c)
    (sf : (i : Fin X0.basics.length) → (j : Fin (LB i).length) →
      Finset (Fin (n + (1 + (m + ((LB i).get j).j + 1))) → ℝ))
    (hsf_sub : ∀ (i : Fin X0.basics.length) (j : Fin (LB i).length), ↑(sf i j) ⊆ (Ef i j).X.set)
    (hsf_hit : ∀ (i : Fin X0.basics.length) (j : Fin (LB i).length)
      (x : Fin (n + (1 + (m + ((LB i).get j).j + 1))) → ℝ),
      x ∈ (Ef i j).X.set → ∃ y ∈ sf i j,
        connectedComponentIn (Ef i j).X.set x = connectedComponentIn (Ef i j).X.set y)
    (hsubN : ∀ (i : Fin X0.basics.length) (j : Fin (LB i).length)
      (z : Fin (n + (1 + m)) → ℝ), z ∈ (ambCatX ((LB i).get j) X0).X.set →
      projBase (Nat.le_add_right n (1 + m)) z = Fin.init y →
      (ambCatX ((LB i).get j) X0).IsBaseSubmersiveAt (Nat.le_add_right n (1 + m)) z)
    (hndN : ∀ (i : Fin X0.basics.length) (j : Fin (LB i).length)
      (z : Fin (n + (1 + m)) → ℝ), z ∈ (ambCatX ((LB i).get j) X0).X.set →
      projBase (Nat.le_add_right n (1 + m)) z = Fin.init y →
      ∀ (mu : Fin ((LB i).get j).j → ℝ) (mu0 : ℝ),
        LagEq (ambCatX ((LB i).get j) X0)
          (Work.WilE7.EAPoly.inr (r₁ := ((LB i).get j).X.r) (X0.basics.get i).pos.prod) c z mu mu0 →
        LagNorm mu mu0 →
        (lagJac (ambCatX ((LB i).get j) X0)
          (Work.WilE7.EAPoly.inr (r₁ := ((LB i).get j).X.r)
            (X0.basics.get i).pos.prod) c z mu mu0).det ≠ 0) :
    ∃ (i : Fin X0.basics.length) (j : Fin (LB i).length)
      (q : Fin (n + (1 + (m + ((LB i).get j).j + 1))) → ℝ),
      q ∈ sf i j ∧
      y ∈ Work.WilE9.Sharp.stratProj '' connectedComponentIn (Ef i j).X.set q ∧
      (∀ w ∈ connectedComponentIn (Ef i j).X.set q,
        Work.WilE9.Sharp.stratProj w ∈
          Work.WilE9.Sharp.stratProj '' connectedComponentIn X.set z₀) := by
  classical
  obtain ⟨w0, hw0c, hw0y⟩ := hy
  have hw0X : w0 ∈ X.set := connectedComponentIn_subset _ _ hw0c
  have hw0X0 : w0 ∈ X0.set := by rw [hX0set]; exact hw0X
  have hw0cc : w0 ∈ connectedComponentIn X0.set z₀ := by rw [hX0set]; exact hw0c
  have hbase : projBase (Nat.le_add_right n (1 + m)) w0 = Fin.init y := by
    rw [projBase_eq_init_stratProj, hw0y]
  -- the basic that holds at `w0`
  obtain ⟨B, hBmem, hBholds⟩ := hw0X0.2
  obtain ⟨iv, hiv, hivget⟩ := List.mem_iff_getElem.mp hBmem
  let i : Fin X0.basics.length := ⟨iv, hiv⟩
  have hget : X0.basics.get i = B := List.get_eq_getElem.trans hivget
  have hBmem' : X0.basics.get i ∈ X0.basics := List.get_mem X0.basics i
  have hBholds' : (X0.basics.get i).holds X0.c w0 := by rw [hget]; exact hBholds
  have hw0β : w0 ∈ (⟨X0.r, X0.c, [X0.basics.get i]⟩ : SemiPf (n + (1 + m))).set :=
    ⟨hw0X0.1, X0.basics.get i, List.mem_singleton_self _, hBholds'⟩
  have hU0 : w0 ∈ ⋃ S ∈ LB i, S.X.set := hLBunion i ▸ hw0β
  -- the maximiser
  obtain ⟨w', hw'K, hw'B, hw'max⟩ :=
    exists_maximiser X0 z₀ hz0 w0 hw0cc (X0.basics.get i) hBmem' hBholds' c
  have hw'comp0 : w' ∈ connectedComponentIn X0.set z₀ :=
    (connectedComponentIn_subset _ _ hw'K).1
  have hw'X0 : w' ∈ X0.set := connectedComponentIn_subset _ _ hw'comp0
  have hw'β : w' ∈ (⟨X0.r, X0.c, [X0.basics.get i]⟩ : SemiPf (n + (1 + m))).set :=
    ⟨hw'X0.1, X0.basics.get i, List.mem_singleton_self _, hw'B⟩
  have hU' : w' ∈ ⋃ S ∈ LB i, S.X.set := hLBunion i ▸ hw'β
  obtain ⟨T', hT'mem, hw'T'⟩ := Set.mem_iUnion₂.mp hU'
  obtain ⟨jv, hjv, hjvget⟩ := List.mem_iff_getElem.mp hT'mem
  let j' : Fin (LB i).length := ⟨jv, hjv⟩
  have hgetT' : (LB i).get j' = T' := List.get_eq_getElem.trans hjvget
  have hT'mem' : (LB i).get j' ∈ LB i := List.get_mem (LB i) j'
  have hw'j' : w' ∈ ((LB i).get j').X.set := by rw [hgetT']; exact hw'T'
  -- the intrinsic data of the stratum of `w'`
  have hbhu := basic_holds_of_union X0 (X0.basics.get i) hBmem' (LB i) (hLBunion i) hT'mem'
  have hT'good : ((LB i).get j').Good := hLBgood i _ hT'mem'
  have hbpos := ambCatX_good_pos X0 ((LB i).get j') (X0.basics.get i) hT'good hbhu.2
  have hS'good : (ambCatX ((LB i).get j') X0).Good := hbpos.1
  have hS's : (ambCatX ((LB i).get j') X0).X.set = ((LB i).get j').X.set :=
    (ambCatX_props ((LB i).get j') X0).1
  have hS'sub : (ambCatX ((LB i).get j') X0).X.set ⊆ X0.set := by
    rw [hS's]; exact hbhu.1
  have hS'B : ∀ z ∈ (ambCatX ((LB i).get j') X0).X.set, (X0.basics.get i).holds X0.c z := by
    intro z hz; exact hbhu.2 z (by rwa [hS's] at hz)
  have hw'S' : w' ∈ (ambCatX ((LB i).get j') X0).X.set := by rw [hS's]; exact hw'j'
  have hPhi' : ∀ z ∈ (ambCatX ((LB i).get j') X0).X.set,
      eaEval (ambCatX ((LB i).get j') X0).X.c
          (Work.WilE7.EAPoly.inr (r₁ := ((LB i).get j').X.r) (X0.basics.get i).pos.prod) z
        = eaEval X0.c (X0.basics.get i).pos.prod z := hbpos.2.2
  -- the null conditions, at the base point of `w0`
  have hsub'' : ∀ z ∈ (ambCatX ((LB i).get j') X0).X.set,
      projBase (Nat.le_add_right n (1 + m)) z = projBase (Nat.le_add_right n (1 + m)) w0 →
      (ambCatX ((LB i).get j') X0).IsBaseSubmersiveAt (Nat.le_add_right n (1 + m)) z :=
    fun z hz hzb => hsubN i j' z hz (by rw [hzb, hbase])
  have hnd'' : ∀ z ∈ (ambCatX ((LB i).get j') X0).X.set,
      projBase (Nat.le_add_right n (1 + m)) z = projBase (Nat.le_add_right n (1 + m)) w0 →
      ∀ (mu : Fin ((LB i).get j').j → ℝ) (mu0 : ℝ),
        LagEq (ambCatX ((LB i).get j') X0)
          (Work.WilE7.EAPoly.inr (r₁ := ((LB i).get j').X.r) (X0.basics.get i).pos.prod) c z mu mu0 →
        LagNorm mu mu0 →
        (lagJac (ambCatX ((LB i).get j') X0)
          (Work.WilE7.EAPoly.inr (r₁ := ((LB i).get j').X.r)
            (X0.basics.get i).pos.prod) c z mu mu0).det ≠ 0 :=
    fun z hz hzb mu mu0 hEq hNorm =>
      hndN i j' z hz (by rw [hzb, hbase]) mu mu0 hEq hNorm
  -- the Lagrange data
  obtain ⟨mu, mu0, hEq, hNorm, hdet⟩ :=
    lagrange_of_maximiser X0 z₀ hz0 w0 w' hw0cc (X0.basics.get i) hBmem' hBholds' c
      hw'K hw'B hw'max (ambCatX ((LB i).get j') X0) hS'good hS'sub hS'B hw'S'
      (Work.WilE7.EAPoly.inr (r₁ := ((LB i).get j').X.r) (X0.basics.get i).pos.prod)
      hPhi' hsub'' hnd''
  have hmemE : lagPoint w' mu mu0 ∈ (Ef i j').X.set := by
    rw [hEf_eq i j']
    exact lagStratumAE_mem (ambCatX ((LB i).get j') X0)
      (Work.WilE7.EAPoly.inr (r₁ := ((LB i).get j').X.r) (X0.basics.get i).pos.prod) c
      hS'good w' mu mu0 hw'S' hEq hNorm hdet
  -- the hitting point of the component
  obtain ⟨q, hq, hqcomp⟩ := hsf_hit i j' (lagPoint w' mu mu0) hmemE
  have hcompq : lagPoint w' mu mu0 ∈ connectedComponentIn (Ef i j').X.set q := by
    rw [← hqcomp]; exact mem_connectedComponentIn hmemE
  -- the whole component projects into `P`
  have hcompproj := lagStratumAE_component_proj_subset (ambCatX ((LB i).get j') X0)
    (Work.WilE7.EAPoly.inr (r₁ := ((LB i).get j').X.r) (X0.basics.get i).pos.prod) c X z₀
    (fun z hz => by rw [← hX0set]; exact hS'sub hz) q
    ⟨lagPoint w' mu mu0, by rw [← hEf_eq i j']; exact hcompq, by
      rw [(Lagrange.lagPoint_apply (n := n) (m := m) (j := ((LB i).get j').j)
        (by omega) w' mu mu0).1]
      rw [← hX0set]; exact hw'comp0⟩
  have hqpred : ∀ w ∈ connectedComponentIn (Ef i j').X.set q,
      Work.WilE9.Sharp.stratProj w ∈
        Work.WilE9.Sharp.stratProj '' connectedComponentIn X.set z₀ := by
    intro w hw
    rw [hEf_eq i j'] at hw
    exact hcompproj w hw
  -- `y` is the projection of the Lagrange point
  have hspw' : Work.WilE9.Sharp.stratProj w' = y := by
    have hfin' : (fibrePiece X0 z₀ (projBase (Nat.le_add_right n (1 + m)) w0)).Finite := by
      have h1 : fibrePiece X0 z₀ (projBase (Nat.le_add_right n (1 + m)) w0)
          = fibrePiece X z₀ (Fin.init y) := by
        show {y' | y' ∈ Work.WilE9.Sharp.stratProj '' connectedComponentIn X0.set z₀ ∧
            Fin.init y' = projBase (Nat.le_add_right n (1 + m)) w0}
          = {y' | y' ∈ Work.WilE9.Sharp.stratProj '' connectedComponentIn X.set z₀ ∧
            Fin.init y' = Fin.init y}
        rw [hX0set, hbase]
      rw [h1]; exact hfin
    have hzcf : w0 ∈ compFibre X0 z₀ (projBase (Nat.le_add_right n (1 + m)) w0) := by
      refine ⟨hw0cc, ?_⟩
      show Fin.init (Work.WilE9.Sharp.stratProj w0) = projBase (Nat.le_add_right n (1 + m)) w0
      rw [projBase_eq_init_stratProj]
    exact (stratProj_eq_of_mem_compFibre' (X := X0) (z₀ := z₀)
      (x := projBase (Nat.le_add_right n (1 + m)) w0) hfin' hzcf hw'K).trans hw0y
  exact ⟨i, j', q, hq,
    ⟨lagPoint w' mu mu0, hcompq, by rw [Assembly.stratProj_lagPoint w' mu mu0]; exact hspw'⟩,
    hqpred⟩

end Work.WilE9G
