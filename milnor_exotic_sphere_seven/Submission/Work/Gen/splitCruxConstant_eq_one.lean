import Mathlib
import Submission.Work.Gen.eSymDef
import Submission.Work.LerayHirsch.FibreRestrict
import Submission.Work.Gen.LineTensor
import Submission.Work.Whitney.chernClass_whitneySum_top
import Submission.Work.LerayHirsch.LH
import Submission.Work.Whitney.Stability
import Submission.Work.Whitney.ChernRelDefs
import Submission.Work.Thom.trivialChern
import Submission.Work.Kunneth.PointMain
import Submission.Work.LerayHirsch.paracompactSpace_projSpace
import Submission.Work.LerayHirsch.t2Space_projSpace

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Work.Gen

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]

/-! ## Auxiliary lemmas: the elementary symmetric class of a family of line bundles

The three lemmas below are the elementary algebra of `Work.Gen.eSym` used in the evaluation of the
universal constant `δ n` on the test family `ε ⊕ ℓ ⊕ ⋯ ⊕ ℓ` over `P(ℂ^n)`. -/

/-- **`eSym` vanishes above the number of variables.** -/
theorem splitCrux_eSym_above {n : ℕ}
    (M : Fin n → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) {k : ℕ} (hk : n < k) :
    eSym n M k = 0 := by
  induction n generalizing k with
  | zero => exact eSym_zero_rank (by omega)
  | succ n ih =>
    rw [eSym_succ]
    have h1 : eSym n (fun i => M (Fin.castSucc i)) k = 0 := ih _ (by omega)
    have h2 : eSym n (fun i => M (Fin.castSucc i)) (k - 1) = 0 := ih _ (by omega)
    rw [h1, h2, zero_add]
    by_cases hk1 : 1 ≤ k
    · rw [dif_pos hk1]
      simp only [Work.Whitney.cupChern_def, Work.Cohomology.cupH'_zero_right,
        Work.Thom.cohTransport_zero]
    · rw [dif_neg hk1]

/-- **The top elementary symmetric class of a constant family is the power of the line class.** -/
theorem splitCrux_eSym_const (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) (p : ℕ) :
    eSym p (fun _ : Fin p => L) p = Work.Kunneth.pow2 (chernClass 1 1 L) p := by
  induction p with
  | zero =>
    rw [eSym_zero, Work.Kunneth.pow2_zero]
  | succ p ih =>
    rw [eSym_succ]
    have h1 : eSym p (fun _ : Fin p => L) (p + 1) = 0 :=
      splitCrux_eSym_above _ (by omega)
    have h3 : eSym p (fun _ : Fin p => L) ((p + 1) - 1)
        = Work.Kunneth.pow2 (chernClass 1 1 L) p := by
      simpa using ih
    rw [h1, zero_add, dif_pos (by omega : 1 ≤ p + 1), h3, Work.Kunneth.pow2_succ,
      Work.Whitney.ChernRel.cupChern_comm p 1 (Work.Kunneth.pow2 (chernClass 1 1 L) p)
        (chernClass 1 1 L)]
    exact Work.LerayHirsch.cohTransport_congr_proof _ _

/-- **`eSym` of a family whose last member is the trivial line bundle**: the trivial summand
contributes nothing. -/
theorem splitCrux_eSym_snoc_trivial [Inhabited ι] {p : ℕ}
    (f : Fin p → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) (k : ℕ) :
    eSym (p + 1)
        (Fin.snoc (α := fun _ : Fin (p + 1) => VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
          f (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)) k
      = eSym p f k := by
  rw [eSym_succ]
  have hcomp : (fun i : Fin p => Fin.snoc (α := fun _ : Fin (p + 1) =>
        VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) f
        (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) (Fin.castSucc i)) = f :=
    funext fun i => Fin.snoc_castSucc (α := fun _ : Fin (p + 1) =>
      VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) _ _ _
  rw [hcomp, Fin.snoc_last]
  rw [Work.Thom.chernClass_trivial (m := 1) (j := 1) (by norm_num)]
  by_cases hk : 1 ≤ k
  · rw [dif_pos hk]
    simp only [Work.Whitney.cupChern_def, Work.Cohomology.cupH'_zero_left,
      Work.Thom.cohTransport_zero, add_zero]
  · rw [dif_neg hk, add_zero]

/-- **The top Chern class of an iterated sum of copies of a line bundle** is the power of the
first Chern class. -/
theorem splitCrux_chernClass_lineSumCore_const
    (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) (p : ℕ) :
    chernClass p p (Work.LerayHirsch.lineSumCore p (fun _ : Fin p => L))
      = Work.Kunneth.pow2 (chernClass 1 1 L) p := by
  induction p with
  | zero =>
    rw [Work.LerayHirsch.lineSumCore_zero, Work.Thom.chernClass_zero_eq_oneH,
      Work.Kunneth.pow2_zero]
    exact (Work.Thom.cohTransport_rfl
      (Work.Cohomology.oneH ℤ (Work.Whitney.ssB B))).symm
  | succ p ih =>
    rw [Work.LerayHirsch.lineSumCore_succ]
    rw [show (fun x : Fin (p + 1) => L) ∘ Fin.castSucc = (fun _ : Fin p => L) from rfl]
    rw [Work.Whitney.chernClass_whitneySum_top, ih, Work.Kunneth.pow2_succ]

/-- **Dropping a trailing trivial summand**: for a family of line bundles whose last member is the
trivial bundle, the Chern classes of the iterated sum do not see it (stability). -/
theorem splitCrux_chernClass_lineSumCore_snoc_trivial [Inhabited ι] {p : ℕ}
    (f : Fin p → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) (j : ℕ) :
    chernClass (p + 1) j (Work.LerayHirsch.lineSumCore (p + 1)
        (Fin.snoc (α := fun _ : Fin (p + 1) => VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
          f (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)))
      = chernClass p j (Work.LerayHirsch.lineSumCore p f) := by
  rw [Work.LerayHirsch.lineSumCore_succ]
  rw [show (Fin.snoc (α := fun _ : Fin (p + 1) =>
        VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) f
        (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)) ∘ Fin.castSucc = f from
      funext fun i => Fin.snoc_castSucc (α := fun _ : Fin (p + 1) =>
        VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
        (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) f i]
  rw [Fin.snoc_last, Work.Whitney.chernClass_whitneySum_trivial]

/-- **The universal constant of the split crux is `1`.**

`hδ` is the split crux *up to a universal constant*: the second-highest Chern class of a direct sum
of `n` line bundles is `δ n` times the `(n-1)`-st elementary symmetric class of the first Chern
classes, uniformly over the family and the base.

To prove `δ n = 1` test on `B = ProjSpace (trivial rank-n bundle over a point)`
(the tree's `ℙ ℂ (EuclideanSpace ℂ (Fin n))`), with the family (all over the SAME index type, e.g.
`ι = PUnit × Fin n`):  `M 0 = eps` (the trivial line bundle) and `M k = tautLineP n` (the
tautological line bundle `Work.LerayHirsch.tautLineP n`, whose `c1` is
`Work.LerayHirsch.zetaP n =: zeta`) for `1 <= k <= n-1`.

* `c_{n-1}(lineSumCore n M) = c_{n-1}(L(+)...(+)L)`  after dropping the trivial summand (stability,
  `Work.Whitney.chernClass_whitneySum_trivial`) `= zeta^(n-1)`
  (`chernClass_whitneySum_top` iterated: the top Chern class of a sum of `n-1` line bundles with
  `c1 = zeta`);
* `eSym n M (n-1) = zeta^(n-1)`  (the `eSym` recursion; the first variable is `0`, so the only
  surviving `(n-1)`-subset product is `zeta^(n-1)`);
* `H^{2n-2}(P(CC^n); Z)` is free of rank one on `zeta^(n-1)`, and `zeta^(n-1) != 0`
  (`Work.Kunneth`/`PointMain` functional, or the top Leray-Hirsch basis element), so
  `zeta^(n-1) = δ n * zeta^(n-1)` forces `δ n = 1`.
* `n = 0, 1`: `chernClass n (n-1) = chernClass n 0` is the unit class and `eSym n M 0` likewise
  (`Work.Thom.chernClass_zero_eq_oneH`), so `δ n * 1 = 1`. -/
theorem splitCruxConstant_eq_one
    (δ : ℕ → ℤ)
    (hδ : ∀ (n : ℕ) {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B]
      {ι : Type} [Fintype ι] (M : Fin n → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι),
      Work.Thom.chernClass n (n - 1) (Work.LerayHirsch.lineSumCore n M)
        = δ n • Work.Gen.eSym n M (n - 1)) :
    ∀ n : ℕ, δ n = 1 := by
  intro n
  cases n with
  | zero =>
    let Z : VectorBundleCore ℂ PUnit (EuclideanSpace ℂ (Fin 1)) PUnit :=
      Work.LerayHirsch.trivCore 1
    let B : Type := Work.LerayHirsch.ProjSpace Z
    haveI hpar : ParacompactSpace B := Work.LerayHirsch.paracompactSpace_projSpace Z
    haveI ht2 : T2Space B := Work.LerayHirsch.t2Space_projSpace Z
    let ι : Type := PUnit × Fin 1
    let M : Fin 0 → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι := Fin.elim0
    have h := hδ 0 M
    have hLHS : Work.Thom.chernClass 0 (0 - 1) (Work.LerayHirsch.lineSumCore 0 M)
        = Work.LerayHirsch.zetaPow Z 0 := by
      rw [Work.Thom.chernClass_zero_eq_oneH, Work.LerayHirsch.zetaPow_zero,
        Work.Thom.cohTransport_rfl]
    have hRHS : Work.Gen.eSym 0 M (0 - 1) = Work.LerayHirsch.zetaPow Z 0 := by
      rw [Work.LerayHirsch.zetaPow_zero, Work.Thom.cohTransport_rfl, Work.Gen.eSym_zero,
        Work.Thom.cohTransport_rfl]
    rw [hLHS, hRHS] at h
    exact Work.Kunneth.smul_zetaPow_injective 0 0 le_rfl (δ 0) 1 (by simpa using h.symm)
  | succ m =>
    let Z : VectorBundleCore ℂ PUnit (EuclideanSpace ℂ (Fin (m + 1))) PUnit :=
      Work.LerayHirsch.trivCore (m + 1)
    let B : Type := Work.LerayHirsch.ProjSpace Z
    haveI hpar : ParacompactSpace B := Work.LerayHirsch.paracompactSpace_projSpace Z
    haveI ht2 : T2Space B := Work.LerayHirsch.t2Space_projSpace Z
    let ι : Type := PUnit × Fin (m + 1)
    let L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι := Work.LerayHirsch.tautLine Z
    let M : Fin (m + 1) → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι :=
      Fin.snoc (α := fun _ : Fin (m + 1) =>
          VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
        (fun _ : Fin m => L) (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
    have h := hδ (m + 1) M
    have hzeta : Work.Kunneth.pow2 (Work.Thom.chernClass 1 1 L) m
        = Work.LerayHirsch.zetaPow Z m := by
      have hc : Work.Thom.chernClass 1 1 L = Work.LerayHirsch.zeta Z := by
        rw [Work.LerayHirsch.zeta_def, Work.Thom.cohTransport_rfl]
      rw [hc, Work.Kunneth.pow2_zeta]
    have hLHS : Work.Thom.chernClass (m + 1) ((m + 1) - 1)
        (Work.LerayHirsch.lineSumCore (m + 1) M) = Work.LerayHirsch.zetaPow Z m :=
      (Work.Gen.splitCrux_chernClass_lineSumCore_snoc_trivial (f := fun _ : Fin m => L)
          ((m + 1) - 1)).trans
        ((Work.Gen.splitCrux_chernClass_lineSumCore_const L m).trans hzeta)
    have hRHS : Work.Gen.eSym (m + 1) M ((m + 1) - 1) = Work.LerayHirsch.zetaPow Z m :=
      (Work.Gen.splitCrux_eSym_snoc_trivial (f := fun _ : Fin m => L) ((m + 1) - 1)).trans
        ((Work.Gen.splitCrux_eSym_const L m).trans hzeta)
    rw [hLHS, hRHS] at h
    exact Work.Kunneth.smul_zetaPow_injective m m le_rfl (δ (m + 1)) 1 (by
      simpa using h.symm)

end

end Work.Gen
