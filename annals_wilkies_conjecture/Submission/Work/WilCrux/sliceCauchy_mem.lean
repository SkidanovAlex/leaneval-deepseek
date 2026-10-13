import Mathlib
import Submission.Work.WilCrux.SliceCauchyDefs
import Submission.Work.WilCrux.SliceCauchyBig
import Submission.Work.WilCrux.SliceCauchyEq
import Submission.Work.WilCrux.SCBig.core_mem
import Submission.Work.WilCrux.SCBig.hyp_mem
import Submission.Work.WilCrux.SCBig.thresh_mem
import Submission.Work.WilG1.Basic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open Classical

namespace Work.WilCrux

open WilkiesDesign

/-- `dDir` is the order-one iterated derivative. -/
theorem scb_dDir_eq_iteratedFDeriv {m : ℕ} (f : (Fin m → ℝ) → ℝ) (i : Fin m) (z : Fin m → ℝ) :
    Work.WilG4b.dDir f i z = iteratedFDeriv ℝ 1 f z (fun _ : Fin 1 => Pi.single i 1) := by
  simp [Work.WilG4b.dDir]

/-- `SharpDeriv` at order one: derivative graphs are `Ω`-sets with uniform format and with
degree `b.eval ![D,1]`.  (A local copy of `Work.WilG4b.derivGraph_mem`, to avoid the
name clash between the several copies in the workspace.) -/
theorem scb_derivGraph_mem (S : SOMin) (hder : S.SharpDeriv) (m F0 : ℕ) :
    ∃ (A : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D : ℕ) (f : (Fin m → ℝ) → ℝ) (i : Fin m),
        WilkiesDesign.graphOf f ∈ S.Ω F0 D (m + 1) →
          Work.WilG4b.derivGraph f i ∈ S.Ω A (MvPolynomial.eval ![D, 1] b) (m + 1) := by
  obtain ⟨a, b, hb⟩ := hder F0 m
  refine ⟨a, b, fun D f i hf => ?_⟩
  have h := hb D f hf 1 (fun _ : Fin 1 => i)
  have hset : Work.WilG4b.derivGraph f i =
      {z : Fin (m + 1) → ℝ | Fin.init z ∈ interior {x | ContDiffAt ℝ 1 f x} ∧
        z (Fin.last m) = iteratedFDeriv ℝ 1 f (Fin.init z) (fun _ : Fin 1 => Pi.single i 1)} := by
    ext z
    simp only [Work.WilG4b.derivGraph, Work.WilG4b.c1Loc, scb_dDir_eq_iteratedFDeriv]
  rw [hset]
  exact h

/-- **`sliceCauchySet` is `Ω`-definable, uniformly in `j`, `k` and `ε`.**

Let `M := a + b`, `f := Work.WilG4c.famFun G` and `i := Fin.natAdd a j : Fin M`.  By
`Work.WilG4b.derivGraph_mem` (needing `hder`) and `Work.WilG4c.graphOf_famFun`, the derivative
graph `T := Work.WilG4b.derivGraph f i ⊆ ℝ^{M+1}` is `Ω`-definable, with format a constant and
degree a polynomial in `D`, *independent of* `j`.  Recall
`u ∈ T ↔ Fin.init u ∈ Work.WilG4b.c1Loc f ∧ u (Fin.last M) = Work.WilG4b.dDir f i (Fin.init u)`,
so `T` is the graph of `u ↦ dDir f i u` over `c1Loc f`.

Intended construction (in the big ambient space `ℝ^N` with `N := (a + 1 + 2*b) + 2`, whose
coordinates are read as `(w, η, z, z', y, y')` with `w : Fin a`, `η : ℝ`, `z, z' : Fin b`,
`y, y' : ℝ`):

* let `e1 : Fin (M+1) → Fin N` send the `a` parameter coordinates of `T` to the `w`-block, the
  `b` fibre coordinates of `T` to the `z`-block, and the value coordinate of `T` to `y`;
  let `e2` be the same with `z'` and `y'`;  then `u ∘ e1 = Fin.snoc (Fin.append w z) y`;
* the set
  `Z := {u | 1/((k:ℝ)+1) < η ∧ η ≤ 1 ∧ z ≠ 0 ∧ (∀ j, |z j| < η) ∧ z' ≠ 0
            ∧ (∀ j, |z' j| < η) ∧ u ∘ e1 ∈ T ∧ u ∘ e2 ∈ T ∧ |y - y'| < ε}`
  is `Ω`-definable (each conjunct is either a coordinate positivity/hypersurface atom of
  `Work.WilG1.Calc.pos_mem`/`hyp_mem`, or the preimage of `T` under the fixed reindexing `e1`,
  `e2` (`Work.WilG5.coordPre_mem`); `z ≠ 0` is the finite union over `j` of `z j < 0 ∨ 0 < z j`);
* then: project the last two coordinates (`y`, `y'`) away and complement, obtaining
  `{(w,η,z,z') : ¬∃ y y', (u∘e1 ∈ T ∧ u∘e2 ∈ T ∧ |y - y'| < ε)}`;
  intersect with the hypothesis set `{(w,η,z,z') : z ≠ 0 ∧ (∀j,|z j|<η) ∧ z' ≠ 0 ∧ (∀j,|z' j|<η)}`;
  project away the last `2*b` coordinates (`z`, `z'`) and complement, obtaining
  `{(w,η) : ∀ z z', Hyp → ∃ y y', (u∘e1 ∈ T ∧ u∘e2 ∈ T ∧ |y - y'| < ε)}`;  intersect with
  `{(w,η) : 1/((k:ℝ)+1) < η ∧ η ≤ 1}` and project away `η` (one coordinate);  the resulting
  subset of `ℝ^a` is `sliceCauchySet G j k ε`;
* the existential over `y` (resp. `y'`) together with `u ∘ e1 ∈ T` is equivalent to
  `Fin.append w z ∈ c1Loc f`, and the corresponding `y` is then forced to be
  `dDir f i (Fin.append w z)`; `‖z‖ < η ↔ ∀ j, |z j| < η` holds because `η > 0` is implied by
  `1/((k:ℝ)+1) < η` (use `pi_norm_lt_iff`).

Because the only dependence on `j`, `k` and `ε` is through constant coefficients inside
`pos_mem`-atoms (whose format is the ambient dimension `+ 2` and whose degree is a constant) and
through `e1`/`e2` (fixed by `a`, `b`), the format is a constant `A` and the degree is `q.eval D`
with `q` a fixed polynomial, independent of `j`, `k` and `ε`. -/
theorem sliceCauchy_mem (S : WilkiesDesign.SOMin) (hder : S.SharpDeriv) {a b F D : ℕ}
    (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (hG : WilkiesDesign.CG.famGraph G ∈ S.Ω F D (a + b + 1)) :
    ∃ (A : ℕ) (q : Polynomial ℕ), ∀ (j : Fin b) (k : ℕ) (ε : ℝ),
      sliceCauchySet G j k ε ∈ S.Ω A (q.eval D) a := by
  -- The derivative graph, uniformly in the fibre direction `j`.
  obtain ⟨aDer, bDer, hbDer⟩ := scb_derivGraph_mem S hder (a + b) F
  -- The three constituent `Ω`-memberships.
  obtain ⟨Ac, qc, hcm⟩ := SCBig.core_mem S a b
  obtain ⟨Ah, qh, hhm⟩ := SCBig.hyp_mem S a b
  obtain ⟨At, qt, htm⟩ := SCBig.thresh_mem S a
  have hgf : WilkiesDesign.graphOf (Work.WilG4c.famFun G) ∈ S.Ω F D (a + b + 1) := by
    rwa [Work.WilG4c.graphOf_famFun]
  refine ⟨max (max ((aDer + Ac) + 2 + 1) Ah + 1 + (b + b) + 1) At + 1 + 1,
    (qc.comp (Work.WilG1.psubst bDer 1) + qh) + qt, ?_⟩
  intro j k ε
  rw [← bigSet_eq]
  rw [bigSet]
  -- the derivative graph of the `j`-th direction
  have hT : Work.WilG4b.derivGraph (Work.WilG4c.famFun G) (Fin.natAdd a j) ∈
      S.Ω aDer ((Work.WilG1.psubst bDer 1).eval D) ((a + b) + 1) := by
    have h := hbDer D (Work.WilG4c.famFun G) (Fin.natAdd a j) hgf
    rwa [← Work.WilG1.eval_psubst] at h
  -- the core set
  have hcore0 := hcm aDer ((Work.WilG1.psubst bDer 1).eval D)
      (Work.WilG4b.derivGraph (Work.WilG4c.famFun G) (Fin.natAdd a j)) ε hT
  have hcore : coreSet (a := a) (b := b)
      (Work.WilG4b.derivGraph (Work.WilG4c.famFun G) (Fin.natAdd a j)) ε ∈ S.Ω (aDer + Ac)
      ((qc.comp (Work.WilG1.psubst bDer 1)).eval D) (((a + 1) + (b + b)) + 2) := by
    simpa [Polynomial.eval_comp] using hcore0
  -- project away `y, y'` and complement
  have h1 := Work.WilG5.projN_mem (S := S) (n := (a + 1) + (b + b)) 2 (aDer + Ac) _ hcore
  have h2 := S.compl h1
  -- intersect with the hypothesis set
  have hhyp : hypSet (a := a) (b := b) ∈ S.Ω Ah (qh.eval D) ((a + 1) + (b + b)) := hhm D
  have h3 := Work.WilG1.Omega.inter₂ h2 hhyp
  rw [Set.inter_comm] at h3
  -- project away `z, z'` and complement
  have h4 := Work.WilG5.projN_mem (S := S) (n := a + 1) (b + b) _ _ h3
  have h5 := S.compl h4
  -- intersect with the threshold set
  have hthr : threshSet (a := a) k ∈ S.Ω At (qt.eval D) (a + 1) := htm k D
  have h6 := Work.WilG1.Omega.inter₂ h5 hthr
  rw [Set.inter_comm] at h6
  -- project away `η`
  exact Work.WilG5.projN_mem (S := S) (n := a) 1 _ _ h6

end Work.WilCrux
