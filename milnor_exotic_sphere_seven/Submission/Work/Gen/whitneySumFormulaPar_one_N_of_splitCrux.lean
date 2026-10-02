import Mathlib
import Submission.Work.Gen.eSymDef
import Submission.Work.Gen.whitneyLowDegree
import Submission.Work.LerayHirsch.whitneySumFormulaPar_one_of_splitLines
import Submission.Work.LerayHirsch.SplitLines
import Submission.Work.LerayHirsch.FlagBundle
import Submission.Work.Kunneth.kunnethCP
import Submission.Work.Whitney.chernClass_whitneySum_top
import Submission.Work.Gen.chernProductSum_line
import Submission.Work.Gen.chernProductSum_comm
import Submission.Work.Gen.puncturedParacompactT2
import Submission.Work.Gen.splitDiagonal
import Submission.Work.Gen.chernProductSum_top_line
import Submission.Work.Gen.chernProductSum_high_line

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.Gen

open Work.TangentClasses Work.Thom

noncomputable section

/-!
# The `(1,N)` Whitney family from the split crux

This module reduces the whole `(1,N)` family of the Whitney sum formula over paracompact Hausdorff
bases to

* `Work.LerayHirsch.WhitneySumFormulaSplit`'s diagonal — here `Work.Gen.splitDiagonal`, the
  `(1,k)@k` case of the split case, which is the input `hcrux` (the second-highest Chern class of a
  direct sum of `n` line bundles, `c_{n-1}(lineSumCore n M) = eSym n M (n-1)`) combined with the
  top-degree multiplicativity `Work.Whitney.chernClass_whitneySum_top`;

and the two topological/cohomological bookkeeping facts

* the punctured total space of a bundle over a paracompact Hausdorff base is again paracompact
  Hausdorff (`Work.Gen.puncturedParacompactT2`), the instance needed by the *peeling* step;
* the collapse of `chernProductSum` for a line bundle in the first slot in the top and in the
  high degrees (`Work.Gen.chernProductSum_top_line`, `Work.Gen.chernProductSum_high_line`).

The route is:

1. `Work.Gen.splitDiagonal` gives the `(1,k)@k` case of the split formula;
2. the flag bundle (`Work.LerayHirsch.splittingPrinciple_of_kunnethCP_aux`, whose side conditions
   `Work.Kunneth.kunnethCP` and `Work.LerayHirsch.paracompactSpace_projSpace` are proved) turns it
   into the *general* core `Core(k)`: `c_k(L ⊕ F) = chernProductSum L F k` for an arbitrary rank-`k`
   bundle `F` (`Work.Gen.core`);
3. the peeling over the punctured total space of the second summand (`Work.Gen.peelStep_snd_par`,
   which is the paracompact-base form of `Work.Gen.chernClass_whitneySum_peelStep_snd`) turns
   `Core(k)` into the whole `(1,N)@k` family for `k ≤ N` (`Work.Gen.oneFamilyPar`);
4. the remaining degrees `k = N+1` and `k > N+1` are the top-degree multiplicativity and the
   vanishing above the rank.
-/

/-- **The punctured total space is paracompact Hausdorff** (`Work.Gen.puncturedParacompactT2`),
packaged as a `Prop` so that it can be passed around as a hypothesis. -/
def PuncturedPar : Prop :=
  ∀ {B F ι : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F] [Fintype ι]
    (Z : VectorBundleCore ℝ B F ι),
    ParacompactSpace ↥(Work.Thom.zeroComplement Z) ∧
      T2Space ↥(Work.Thom.zeroComplement Z)

/-- `Work.Gen.puncturedParacompactT2` as a proposition. -/
theorem puncturedPar : PuncturedPar := fun Z => Work.Gen.puncturedParacompactT2 Z

/-- **The split diagonal**, as the hypothesis of the reduction (`Work.Gen.splitDiagonal` with the
crux already applied). -/
def SplitDiagAll : Prop :=
  ∀ (k : ℕ) {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B]
    {ι ι' : Type} [Fintype ι] [Fintype ι']
    (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
    (M : Fin k → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι'),
    Work.Thom.chernClass (1 + k) k
        (Work.Whitney.whitneySum L (Work.LerayHirsch.lineSumCore k M))
      = Work.Whitney.chernProductSum L (Work.LerayHirsch.lineSumCore k M) k

/-- **The general core, packaged as a proposition**: the `(1,k)@k` case of the Whitney formula for
an arbitrary rank-`k` bundle. -/
def CoreAll : Prop :=
  ∀ (k : ℕ) {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B]
    {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (F : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin k)) ι₂),
    Work.Thom.chernClass (1 + k) k (Work.Whitney.whitneySum L F)
      = Work.Whitney.chernProductSum L F k

/-- **The general core `(1,k)@k`, from the split diagonal, via the flag bundle.**

Pulling back along the flag bundle `π : P → B` of `F` (`Work.LerayHirsch.FlagWitness`, whose
`π^*` is injective on cohomology) turns `π^*(L ⊕ F) ≅ π^*L ⊕ lineSumCore k W.L` into a split sum, so
the split diagonal computes the left-hand side, and naturality plus the isomorphism identify the
right-hand sides. -/
theorem core {k : ℕ} {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B]
    {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (F : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin k)) ι₂)
    (hsplit : SplitDiagAll) :
    Work.Thom.chernClass (1 + k) k (Work.Whitney.whitneySum L F)
      = Work.Whitney.chernProductSum L F k := by
  obtain ⟨P, tP, hparP, ht2P, ⟨W⟩⟩ := Work.LerayHirsch.splittingPrinciple_of_kunnethCP_aux
    Work.Kunneth.kunnethCP (fun Z => Work.LerayHirsch.paracompactSpace_projSpace Z) k F
  letI : TopologicalSpace P := tP
  letI : ParacompactSpace P := hparP
  letI : T2Space P := ht2P
  letI : Fintype W.ιL := W.finL
  refine W.inj (2 * k) ?_
  rw [← Work.Thom.chernClass_comap (Work.Whitney.whitneySum L F) W.π,
    Work.Whitney.whitneySum_bundleComap, Work.Whitney.chernProductSum_CohMap]
  have hstep : Work.Thom.chernClass (1 + k) k
        (Work.Whitney.whitneySum (Work.Thom.bundleComap L W.π) (Work.Thom.bundleComap F W.π))
      = Work.Thom.chernClass (1 + k) k
        (Work.Whitney.whitneySum (Work.Thom.bundleComap L W.π)
          (Work.LerayHirsch.lineSumCore k W.L)) := by
    obtain ⟨e'⟩ := Work.LerayHirsch.nonempty_bundleIso_whitneySum_snd
      (Work.Thom.bundleComap L W.π) (Work.Thom.bundleComap F W.π)
      (Work.LerayHirsch.lineSumCore k W.L) W.iso.some
    exact Work.Thom.chernClass_BundleIso _ _ e'
  rw [hstep, hsplit k (Work.Thom.bundleComap L W.π) W.L]
  exact (Work.Whitney.chernProductSum_congr_second (Work.Thom.bundleComap L W.π)
    (Work.Thom.bundleComap F W.π) (Work.LerayHirsch.lineSumCore k W.L) k
    (fun i => Work.Thom.chernClass_BundleIso _ _ W.iso.some)).symm

/-- `CoreAll` from the split diagonal. -/
theorem coreAll (hsplit : SplitDiagAll) : CoreAll := by
  intro k B _ _ _ ι₁ ι₂ _ _ L F
  exact core L F hsplit

/-- **The peeling step of the Whitney sum formula, in the paracompact form.**  If the formula holds
for the ranks `(1, s)` over every paracompact Hausdorff base, then it holds for the ranks
`(1, s+1)` in degree `k ≤ s`: this is the descent over the punctured total space of the second
summand (`Work.Whitney.chernClass_whitneySum_pullback_eq_snd`), whose base is paracompact Hausdorff
by `Work.Gen.puncturedParacompactT2`. -/
theorem peelStep_snd_par {s k : ℕ} (hpar : PuncturedPar) (hk : k ≤ s)
    (IH : ∀ {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B]
      {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
      (A' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
      (B' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin s)) ι₂),
      Work.Thom.chernClass (1 + s) k (Work.Whitney.whitneySum A' B')
        = Work.Whitney.chernProductSum A' B' k)
    {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B]
    {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (B' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (s + 1))) ι₂) :
    Work.Thom.chernClass (1 + (s + 1)) k (Work.Whitney.whitneySum A B')
      = Work.Whitney.chernProductSum A B' k := by
  haveI hpar1 : ParacompactSpace ↥(Work.Thom.zeroComplement (Work.Thom.realification B')) :=
    (hpar (Work.Thom.realification B')).1
  haveI hpar2 : T2Space ↥(Work.Thom.zeroComplement (Work.Thom.realification B')) :=
    (hpar (Work.Thom.realification B')).2
  have hbij : Function.Bijective
      ((Work.Thom.CohMap (Work.Whitney.punctProjE B') ℤ (2 * k)).hom) :=
    Work.Thom.bijective_proj_zeroComplementA (k := 2 * k) (Work.Thom.realification B')
      (Work.Thom.finrank_real_euclidean_complex (s + 1))
      (Work.Thom.thomClassRank (s + 1) (Nat.succ_le_succ (Nat.zero_le s)) B') (by omega)
  refine hbij.1 ?_
  rw [← Work.Thom.chernClass_comap (Work.Whitney.whitneySum A B') (Work.Whitney.punctProjE B'),
    Work.Whitney.chernProductSum_CohMap A B' (Work.Whitney.punctProjE B')]
  rw [Work.Whitney.chernClass_whitneySum_pullback_eq_snd (E := A) (F := B') (r := 1) (s := s)]
  rw [IH (Work.Thom.bundleComap A (Work.Whitney.punctProjE B'))
    (Work.Thom.tautQuotient (m := s) B')]
  exact Work.Whitney.chernProductSum_congr_second (Work.Thom.bundleComap A (Work.Whitney.punctProjE B'))
    (Work.Thom.tautQuotient (m := s) B') (Work.Thom.bundleComap B' (Work.Whitney.punctProjE B')) k
    (fun i => (Work.Whitney.chernClass_bundleComap_proj_eq_tautQuotient (j := i) B').symm)

/-- **The `(1,n)` family from the general core, over paracompact Hausdorff bases**: for every `n`,
every `k ≤ n`, every line bundle `L` and every rank-`n` bundle `F`,
`c_k(L ⊕ F) = chernProductSum L F k`.  The induction on `n` peels the second summand over its
punctured total space; the base case `k = n` is the core `CoreAll`. -/
theorem oneFamilyPar (hpar : PuncturedPar) (hcore : CoreAll) :
    ∀ (n : ℕ) {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B]
      {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] (k : ℕ) (hk : k ≤ n)
      (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
      (F : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin n)) ι₂),
      Work.Thom.chernClass (1 + n) k (Work.Whitney.whitneySum L F)
        = Work.Whitney.chernProductSum L F k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro B _htB _hparB _ht2B ι₁ ι₂ _ _ k hk L F
    rcases eq_or_lt_of_le hk with heq | hlt
    · subst heq
      exact hcore k L F
    · rcases Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0) with ⟨s, rfl⟩
      have IH : ∀ {B' : Type} [TopologicalSpace B'] [ParacompactSpace B'] [T2Space B']
          {ι₁' ι₂' : Type} [Fintype ι₁'] [Fintype ι₂']
          (A' : VectorBundleCore ℂ B' (EuclideanSpace ℂ (Fin 1)) ι₁')
          (B'' : VectorBundleCore ℂ B' (EuclideanSpace ℂ (Fin s)) ι₂'),
          Work.Thom.chernClass (1 + s) k (Work.Whitney.whitneySum A' B'')
            = Work.Whitney.chernProductSum A' B'' k :=
        fun {B'} _ _ _ {ι₁'} {ι₂'} _ _ A' B'' => ih s (by omega) k (by omega) A' B''
      exact peelStep_snd_par (s := s) (k := k) hpar (by omega) IH L F

/-- **Degree congruence of `Work.Thom.chernClass`**: the degree argument of `chernClass` may be
replaced by a (propositionally) equal one, at the price of the corresponding degree cast. -/
theorem chernClass_degree_congr {m j j' : ℕ} {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (h : j = j') :
    Work.Thom.chernClass m j' Z
      = Work.Thom.cohTransport (congrArg (fun t => 2 * t) h) (Work.Thom.chernClass m j Z) := by
  subst h
  rw [Work.Thom.cohTransport_rfl]

/-- **The top-degree collapse** (`Work.Gen.chernProductSum_top_line`), packaged. -/
def TopLine : Prop :=
  ∀ {B : Type} [TopologicalSpace B] {ι ι' : Type} [Fintype ι] [Fintype ι']
    {m : ℕ} (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
    (W : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι'),
    Work.Whitney.chernProductSum L W (m + 1)
      = Work.Thom.cohTransport (by omega : 2 * (1 + m) = 2 * (m + 1))
          (Work.Whitney.cupChern 1 m (Work.Thom.chernClass 1 1 L)
            (Work.Thom.chernClass m m W))

/-- **The high-degree vanishing** (`Work.Gen.chernProductSum_high_line`), packaged. -/
def HighLine : Prop :=
  ∀ {B : Type} [TopologicalSpace B] {ι ι' : Type} [Fintype ι] [Fintype ι']
    {m : ℕ} (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
    (W : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') {k : ℕ},
    m + 1 < k → Work.Whitney.chernProductSum L W k = 0

/-- The `(1,N)` family from the pieces: `CoreAll` (the general core, from the split diagonal and the
flag bundle) covers the degrees `k ≤ N` by `Work.Gen.oneFamilyPar`, the top degree `k = N+1` is the
multiplicativity of the top Chern class (`Work.Whitney.chernClass_whitneySum_top`) with the collapse
`TopLine`, and the degrees `k > N+1` vanish on both sides. -/
theorem target_all (hpar : PuncturedPar) (hcore : CoreAll)
    (htop : TopLine) (hhigh : HighLine) :
    ∀ N : ℕ, Work.LerayHirsch.WhitneySumFormulaPar 1 N := by
  intro N B _htB _hparB _ht2B ι₁ ι₂ _ _ Z₁ Z₂ k
  by_cases hk : k ≤ N
  · exact oneFamilyPar hpar hcore N k hk Z₁ Z₂
  · have hNk : N < k := by omega
    rcases eq_or_lt_of_le (show N + 1 ≤ k by omega) with heq | hlt
    · have hgoal : Work.Thom.chernClass (1 + N) (N + 1) (Work.Whitney.whitneySum Z₁ Z₂)
          = Work.Whitney.chernProductSum Z₁ Z₂ (N + 1) := by
        rw [htop Z₁ Z₂]
        have hdeg := chernClass_degree_congr (Z := Work.Whitney.whitneySum Z₁ Z₂)
          (by omega : 1 + N = N + 1)
        have htop' := Work.Whitney.chernClass_whitneySum_top Z₁ Z₂
        rw [hdeg, htop']
      rw [← heq]
      exact hgoal
    · have hzero : Work.Thom.chernClass (1 + N) k (Work.Whitney.whitneySum Z₁ Z₂) = 0 :=
        Work.Thom.chernClass_eq_zero_of_lt (Z := Work.Whitney.whitneySum Z₁ Z₂) (by omega)
      rw [hzero, hhigh Z₁ Z₂ (show N + 1 < k by omega)]

/-- **The `(1,N)` Whitney sum formula from the split crux.**

`hcrux` is the split crux: for `n >= 1` line bundles `M 0 ... M (n-1)` over a paracompact Hausdorff
base, the *second-highest* Chern class of their direct sum is the `(n-1)`-st elementary symmetric
class of the first Chern classes (`Work.Gen.eSym`).

Route to the conclusion (all pieces are on disk):
1. `hcrux` + `Work.Whitney.chernClass_whitneySum_top` (the top degree, iterated over the
   `lineSumCore` recursion) + the peeling lemmas of `Submission/Work/Gen/whitneyLowDegree.lean`
   give the *general split* statement `c_k(lineSumCore m M) = eSym m M k` for all `m, k`
   (degrees `k <= m-2` by peeling, which uses `Work.Gen.chernClass_whitneySum_one_family` applied to
   the *general* rank-`k` core `Core(k)`; that general core follows from `hcrux` at levels `k` and
   `k+1` by the flag bundle `Work.LerayHirsch.splittingPrinciple_of_kunnethCP_aux`, exactly as in
   the proof of `Work.LerayHirsch.whitneySumFormulaPar_one_of_splitLines`).
2. Hence `Work.LerayHirsch.WhitneySumFormulaSplit` (the split case with the second summand
   `lineSumCore n M`).
3. `Work.LerayHirsch.whitneySumFormulaPar_one_of_splitLines` with the proved side conditions
   `Work.Kunneth.kunnethCP` and `Work.LerayHirsch.paracompactSpace_projSpace` turns the split case
   into `forall N, WhitneySumFormulaPar 1 N`. -/
theorem whitneySumFormulaPar_one_N_of_splitCrux
    (hcrux : ∀ (n : ℕ) {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B]
      {ι : Type} [Fintype ι] (M : Fin n → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι),
      Work.Thom.chernClass n (n - 1) (Work.LerayHirsch.lineSumCore n M)
        = Work.Gen.eSym n M (n - 1)) :
    ∀ N : ℕ, Work.LerayHirsch.WhitneySumFormulaPar 1 N := by
  have hdiag : SplitDiagAll := by
    intro k B _ _ _ ι ι' _ _ L M
    exact Work.Gen.splitDiagonal hcrux k L M
  have htop : TopLine := by
    intro B _ ι ι' _ _ m L W
    exact Work.Gen.chernProductSum_top_line L W
  have hhigh : HighLine := by
    intro B _ ι ι' _ _ m L W k hk
    exact Work.Gen.chernProductSum_high_line (k := k) L W hk
  exact target_all puncturedPar (coreAll hdiag) htop hhigh

end

end Work.Gen
