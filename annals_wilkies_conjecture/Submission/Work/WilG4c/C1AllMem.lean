import Mathlib
import Submission.Work.WilG4c.StepLipHighAux
import Submission.Work.WilG4c.StepBadLoc
import Submission.Work.WilG4c.StepLipR0Aux1
import Submission.Work.WilG5.Reindex

namespace Work.WilG4c

open WilkiesDesign

/-!
## `Ω`-membership of the "whole fibre is `C¹`" set

`Work.WilkG4c.C1All f` is the set of `(l,s) ∈ ℝ^{p+1}` such that the joint function `famFunHat f`
is `C¹` at every point `(l,s,y)` of the fibre over the *whole* open cube in `y`.

It is `Ω`-definable whenever the graph of `f` is: writing
`LocSet p n f = interior {x | ContDiffAt ℝ 1 (famFunHat f) x}` for the interior of the joint `C¹`
locus (which `S.SharpDeriv` exhibits as an `Ω`-set, via its derivative graph `DgSet`), one has the
identity

  `C1All f = (projN n ( (coordPre (reidx p n) (LocSet p n f))ᶜ ∩ coordPre cubeIdx (openCube n) ))ᶜ`.

Indeed, for a point `Fin.append u y` of `ℝ^{(p+1)+n}`, membership in `coordPre (reidx p n)
(LocSet p n f)` says `xPt u y ∈ LocSet` (`Work.WilkG4c.append_comp_reidx`) and membership in
`coordPre cubeIdx (openCube n)` says `y ∈ openCube n` (`Fin.append_right`).  Projecting the `y`
block and complementing turns `∃ y ∈ openCube n, xPt u y ∉ LocSet` into the universal statement
`∀ y ∈ openCube n, xPt u y ∈ LocSet` defining `C1All f`.

All the `Ω`-bookkeeping is done through `Work.WilG5.coordPre_mem`, `Work.WilkG4c.inter2_nat`,
`Work.WilG5.projN_mem` and `SOMin.compl`; the resulting degree is a polynomial in `D` alone (the
parameter `r` of the statement is unused), obtained by substituting `X₁ := 1` into `b1`
(`Work.WilG1.psubst`) and adding the accumulated constant.
-/

theorem C1AllMem (S : WilkiesDesign.SOMin) (hder : S.SharpDeriv) (p n F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D r : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ),
        WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
        Work.WilkG4c.C1All f ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (p + 1) := by
  obtain ⟨a1, b1, h1⟩ := hder F0 (p + (n + 1))
  -- `afmt1`: a convenient common format bound for the cube/c`C¹`-locus pieces.
  let afmt1 : ℕ := a1 + 64 * (((p + 1) + n) + (p + (n + 1))) + 64 * (((p + 1) + n) + n)
      + 32 * n + 16 * n + n + 1000
  -- additive constants in the degree bounds coming from `coordPre_mem`
  let c1 : ℕ := 32 * (((p + 1) + n) + (p + (n + 1))) + 32
  let c2 : ℕ := (16 * n + 16) + 32 * (((p + 1) + n) + n) + 32
  let kdeg : ℕ := c1 + c2
  refine ⟨afmt1 + 2 + n + 1,
    (Work.WilG1.psubst b1 1 + Polynomial.C kdeg).toMvPolynomial (0 : Fin 2), ?_⟩
  intro D r f hd
  -- the graph of `famFunHat f` is `famGraph f`
  have hd' : WilkiesDesign.graphOf (Work.WilkG4c.famFunHat f) ∈ S.Ω F0 D (p + (n + 1) + 1) := by
    simpa [Work.WilkG4c.famGraph_eq_graphOf_famFunHat] using hd
  -- `SharpDeriv` applied at order `1` in the `x`-direction gives the derivative graph `DgSet`
  have hDg : Work.WilkG4c.DgSet p n f ∈ S.Ω a1 (MvPolynomial.eval ![D, 1] b1)
      (p + (n + 1) + 1) :=
    h1 D (Work.WilkG4c.famFunHat f) hd' 1 (fun _ : Fin 1 => Work.WilkG4c.xDirHat p n)
  -- its projection is the interior of the joint `C¹` locus
  have hLoc : Work.WilkG4c.LocSet p n f ∈ S.Ω (a1 + 1) (MvPolynomial.eval ![D, 1] b1)
      (p + (n + 1)) := by
    have h := S.proj hDg
    rwa [Work.WilkG4c.projLast_DgSet] at h
  -- reindex `(l,x,y) ↦ (l,x | y)` and complement
  have hpre0 := Work.WilG5.coordPre_mem (S := S) (ι := Work.WilkG4c.reidx p n) hLoc
  have hpre : Work.WilG5.coordPre (Work.WilkG4c.reidx p n) (Work.WilkG4c.LocSet p n f) ∈
      S.Ω afmt1 (MvPolynomial.eval ![D, 1] b1 + c1) ((p + 1) + n) := by
    refine Work.WilG5.mem_mono hpre0 afmt1 (MvPolynomial.eval ![D, 1] b1 + c1) ?_ ?_
    · show a1 + 1 + 64 * (p + 1 + n + (p + (n + 1))) + 64 ≤ afmt1
      omega
    · show MvPolynomial.eval ![D, 1] b1 + 32 * (p + 1 + n + (p + (n + 1))) + 32
          ≤ MvPolynomial.eval ![D, 1] b1 + c1
      omega
  have hc : (Work.WilG5.coordPre (Work.WilkG4c.reidx p n) (Work.WilkG4c.LocSet p n f))ᶜ ∈
      S.Ω (afmt1 + 1) (MvPolynomial.eval ![D, 1] b1 + c1) ((p + 1) + n) := S.compl hpre
  -- the cube condition on the `y` block
  have hcube0 := Work.WilG5.coordPre_mem (S := S)
      (ι := fun j : Fin n => Fin.natAdd (p + 1) j) (Work.WilG5.openCube_mem (S := S) (n := n))
  have hcube : Work.WilG5.coordPre (fun j : Fin n => Fin.natAdd (p + 1) j)
      (WilkiesDesign.openCube n) ∈ S.Ω afmt1 c2 ((p + 1) + n) := by
    refine Work.WilG5.mem_mono hcube0 afmt1 c2 ?_ ?_
    · show 4 * n + 24 + 64 * (p + 1 + n + n) + 64 ≤ afmt1
      omega
    · show 16 * n + 16 + 32 * (p + 1 + n + n) + 32 ≤ c2
      omega
  -- the joint set `{(l,x,y) : y ∈ openCube n ∧ xPt(l,x,y) ∉ LocSet}`
  set hint : Set (Fin ((p + 1) + n) → ℝ) :=
    (Work.WilG5.coordPre (Work.WilkG4c.reidx p n) (Work.WilkG4c.LocSet p n f))ᶜ ∩
      Work.WilG5.coordPre (fun j : Fin n => Fin.natAdd (p + 1) j) (WilkiesDesign.openCube n)
    with hhint
  have hint_mem : hint ∈ S.Ω (afmt1 + 2) (MvPolynomial.eval ![D, 1] b1 + kdeg) ((p + 1) + n) := by
    rw [hhint]
    refine Work.WilG5.mem_mono (Work.WilkG4c.inter2_nat hc hcube) (afmt1 + 2)
      (MvPolynomial.eval ![D, 1] b1 + kdeg) ?_ ?_
    · show max (afmt1 + 1) afmt1 + 1 ≤ afmt1 + 2
      omega
    · show (MvPolynomial.eval ![D, 1] b1 + c1) + c2 ≤ MvPolynomial.eval ![D, 1] b1 + kdeg
      omega
  -- project the `y` block away and complement
  have hproj : Work.WilG5.projN n hint ∈ S.Ω (afmt1 + 2 + n) (MvPolynomial.eval ![D, 1] b1 + kdeg)
      (p + 1) :=
    Work.WilG5.projN_mem n (afmt1 + 2) (MvPolynomial.eval ![D, 1] b1 + kdeg) hint_mem
  have hfinal0 : (Work.WilG5.projN n hint)ᶜ ∈ S.Ω (afmt1 + 2 + n + 1)
      (MvPolynomial.eval ![D, 1] b1 + kdeg) (p + 1) := S.compl hproj
  -- the complement of the projection is exactly `C1All f`
  have hC1 : Work.WilkG4c.C1All f = (Work.WilG5.projN n hint)ᶜ := by
    rw [hhint]
    ext u
    have key : ∀ y : Fin n → ℝ,
        Fin.append u y ∈ ((Work.WilG5.coordPre (Work.WilkG4c.reidx p n) (Work.WilkG4c.LocSet p n f))ᶜ ∩
          Work.WilG5.coordPre (fun j : Fin n => Fin.natAdd (p + 1) j) (WilkiesDesign.openCube n))
        ↔ y ∈ WilkiesDesign.openCube n ∧
            ¬ (Work.WilkG4c.xPt (fun i : Fin p => u (Fin.castSucc i)) (u (Fin.last p)) y
                ∈ Work.WilkG4c.LocSet p n f) := by
      intro y
      have hcc : (Fin.append u y ∈ Work.WilG5.coordPre (Work.WilkG4c.reidx p n)
            (Work.WilkG4c.LocSet p n f))
          ↔ (Fin.append u y ∘ Work.WilkG4c.reidx p n ∈ Work.WilkG4c.LocSet p n f) := Iff.rfl
      have hcq : (Fin.append u y ∈ Work.WilG5.coordPre (fun j : Fin n => Fin.natAdd (p + 1) j)
            (WilkiesDesign.openCube n)) ↔ (y ∈ WilkiesDesign.openCube n) := by
        show ((Fin.append u y) ∘ (fun j : Fin n => Fin.natAdd (p + 1) j)) ∈ WilkiesDesign.openCube n
          ↔ y ∈ WilkiesDesign.openCube n
        rw [show (Fin.append u y) ∘ (fun j : Fin n => Fin.natAdd (p + 1) j) = y from by
          funext j; rw [Function.comp_apply, Fin.append_right]]
      rw [Set.mem_inter_iff, Set.mem_compl_iff, hcc, hcq, Work.WilkG4c.append_comp_reidx u y]
      tauto
    rw [Work.WilkG4c.C1All, Set.mem_ofPred_eq, Set.mem_compl_iff, Work.WilG5.projN,
      Set.mem_ofPred_eq]
    constructor
    · rintro h ⟨y, hy⟩
      have hk := (key y).mp hy
      exact hk.2 (h y hk.1)
    · intro h y hy
      by_contra hx
      exact h ⟨y, (key y).mpr ⟨hy, hx⟩⟩
  rw [hC1]
  -- the degree bound supplied by `b` is `eval ![D,1] b1 + kdeg`
  have hB : MvPolynomial.eval ![D, r]
        ((Work.WilG1.psubst b1 1 + Polynomial.C kdeg).toMvPolynomial (0 : Fin 2))
      = MvPolynomial.eval ![D, 1] b1 + kdeg := by
    rw [MvPolynomial.eval_toMvPolynomial, Matrix.cons_val_zero, Polynomial.eval_add,
      Polynomial.eval_C, Work.WilG1.eval_psubst]
  exact Work.WilG5.mem_mono hfinal0 (afmt1 + 2 + n + 1)
    ((MvPolynomial.eval ![D, r]) ((Work.WilG1.psubst b1 1 + Polynomial.C kdeg).toMvPolynomial (0 : Fin 2)))
    (by omega) (le_of_eq hB.symm)

end Work.WilG4c
