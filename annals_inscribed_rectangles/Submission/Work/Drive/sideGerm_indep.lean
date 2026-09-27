import Mathlib
import Submission.Work.Drive.sideGermDefs
import Submission.Work.Drive.planeChartDefs
import Submission.Work.Drive.sideGerm_good_exists
import Submission.Work.Drive.sideGerm_parity_eq_of_close_loop
import Submission.Work.Drive.sideGermLocalconstUnconditional
import Submission.Work.Drive.coreLoop_disjoint_rotCapping
import Submission.Work.Drive.chartIsSmooth

/-!
# Independence of the germ side value from the chart perturbation family

`Work.Drive.sideGerm Ξ Q c w` is defined as a *germ* in the perturbation parameter: it is `1` iff every
sufficiently small chart perturbation `t` at which the perturbed pair is regular (`GoodAt`) has odd
count.  The value is claimed to be **independent of the family** `Ξ` used to probe the regularity — and
that is what this file proves, for any two chart perturbations `Ξ` (of dimension `m`) and `Ξ'` (of
dimension `m'`) of a plane chart `Q`, at every angle `w` at which the loop misses the rotated plane.

## The mechanism

Two ingredients of the workspace enter:

* `Work.Drive.sideGerm_parity_eq_of_close_loop` — for a *single* family, the parity of the count is
  locally constant on the good configurations near `0` (the L6 family engine along a ramped path, with
  the parametric Sard supplying regularity);
* `Work.Drive.sideGerm_good_exists` — the Sard existence: good configurations accumulate at `0`.

These give, for each family separately, that the germ value is `1` exactly when *the* parity of the
good configurations near `0` is odd.  The germ is therefore intrinsic as soon as the *parities* of two
families agree — and that is the only cross-family input.

It is obtained without any two-family Sard: the two families are **composed** into one,
`pairPert Ξ Ξ' a = Ξ a₁ ∘ Ξ' a₂` (splitting the `m + m'` parameters of the composite into an
`m`-block and an `m'`-block).  The composite is again a chart perturbation (its parameter-derivative
is onto because the *first* block alone already moves the chart; `Ξ' 0 = id`), and it *contains* both
families as sub-families: at the parameters `(t, 0)` (resp. `(0, t')`) the perturbed chart is
`Ξ t ∘ Q` (resp. `Ξ' t' ∘ Q`), so the good predicate and the count of the composite at those
parameters are literally those of `Ξ` (resp. `Ξ'`).  Applying the single-family parity locality to the
composite then identifies the parities of the two families, and the germ bookkeeping of
`sideGerm_eq_one_iff_frequently_good_odd` finishes.

The angle hypothesis `w ∈ Zc γ` enters exactly once, through
`Work.Drive.disjoint_range_coreLoop_rotCapping_chartDisk`, which turns it into the *loop-vs-plane*
disjointness hypothesis of the parity locality (this is the only form of `Zc γ` the parity argument
consumes, cf. `SIDEGERM_SETTLEMENT.md` §1bis).
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

set_option linter.unusedVariables false

abbrev pairSplit (m m' : ℕ) : EuclideanSpace ℝ (Fin (m + m')) →L[ℝ]
    EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m') :=
  (EuclideanSpace.finAddEquivProd (n := m) (m := m')).toContinuousLinearMap

lemma pairSplit_apply (m m' : ℕ) (a : EuclideanSpace ℝ (Fin (m + m'))) :
    pairSplit m m' a = (EuclideanSpace.finAddEquivProd (n := m) (m := m')) a := rfl

/-- The inclusion of the first block. -/
def embFst (m m' : ℕ) : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin (m + m')) :=
  (EuclideanSpace.finAddEquivProd (n := m) (m := m')).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ _ _)

/-- The inclusion of the second block. -/
def embSnd (m m' : ℕ) : EuclideanSpace ℝ (Fin m') →L[ℝ] EuclideanSpace ℝ (Fin (m + m')) :=
  (EuclideanSpace.finAddEquivProd (n := m) (m := m')).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℝ _ _)

@[simp] lemma embFst_apply (m m' : ℕ) (t : EuclideanSpace ℝ (Fin m)) :
    embFst m m' t = (EuclideanSpace.finAddEquivProd (n := m) (m := m')).symm (t, 0) := by
  simp [embFst]

@[simp] lemma embSnd_apply (m m' : ℕ) (t : EuclideanSpace ℝ (Fin m')) :
    embSnd m m' t = (EuclideanSpace.finAddEquivProd (n := m) (m := m')).symm (0, t) := by
  simp [embSnd]

@[simp] lemma pairSplit_embFst (m m' : ℕ) (t : EuclideanSpace ℝ (Fin m)) :
    pairSplit m m' (embFst m m' t) = (t, 0) := by
  rw [pairSplit_apply, embFst_apply]
  exact ContinuousLinearEquiv.apply_symm_apply _ _

@[simp] lemma pairSplit_embSnd (m m' : ℕ) (t : EuclideanSpace ℝ (Fin m')) :
    pairSplit m m' (embSnd m m' t) = (0, t) := by
  rw [pairSplit_apply, embSnd_apply]
  exact ContinuousLinearEquiv.apply_symm_apply _ _

@[simp] lemma pairSplit_zero (m m' : ℕ) :
    pairSplit m m' (0 : EuclideanSpace ℝ (Fin (m + m'))) = 0 := by
  simp [pairSplit_apply]

/-- **The composite chart perturbation** of two chart perturbations: the `m`-block of the parameter
acts first, then the `m'`-block. -/
def pairPert {m m' : ℕ} (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Ξ' : EuclideanSpace ℝ (Fin m') → CappingSpace → CappingSpace)
    (a : EuclideanSpace ℝ (Fin (m + m'))) : CappingSpace → CappingSpace :=
  fun p => Ξ (pairSplit m m' a).1 (Ξ' (pairSplit m m' a).2 p)

@[simp] lemma pairPert_apply {m m' : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Ξ' : EuclideanSpace ℝ (Fin m') → CappingSpace → CappingSpace)
    (a : EuclideanSpace ℝ (Fin (m + m'))) (p : CappingSpace) :
    pairPert Ξ Ξ' a p = Ξ (pairSplit m m' a).1 (Ξ' (pairSplit m m' a).2 p) := rfl

lemma pairPert_zero {m m' : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Ξ' : EuclideanSpace ℝ (Fin m') → CappingSpace → CappingSpace)
    {Q : ℂ → CappingSpace} (hΞ : ChartPert Q m Ξ) (hΞ' : ChartPert Q m' Ξ') :
    ∀ p : CappingSpace, pairPert Ξ Ξ' 0 p = p := by
  intro p
  show Ξ (pairSplit m m' 0).1 (Ξ' (pairSplit m m' 0).2 p) = p
  rw [pairSplit_zero]
  simp only [Prod.fst_zero, Prod.snd_zero]
  rw [hΞ'.1, hΞ.1]

lemma pairPert_embFst {m m' : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Ξ' : EuclideanSpace ℝ (Fin m') → CappingSpace → CappingSpace)
    {Q : ℂ → CappingSpace} (hΞ' : ChartPert Q m' Ξ')
    (t : EuclideanSpace ℝ (Fin m)) :
    pairPert Ξ Ξ' (embFst m m' t) = fun p => Ξ t p := by
  funext p
  rw [pairPert_apply, pairSplit_embFst, hΞ'.1]

lemma pairPert_embSnd {m m' : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Ξ' : EuclideanSpace ℝ (Fin m') → CappingSpace → CappingSpace)
    {Q : ℂ → CappingSpace} (hΞ : ChartPert Q m Ξ)
    (t : EuclideanSpace ℝ (Fin m')) :
    pairPert Ξ Ξ' (embSnd m m' t) = fun p => Ξ' t p := by
  funext p
  rw [pairPert_apply, pairSplit_embSnd, hΞ.1]


lemma embFst_add_embSnd (m m' : ℕ) (t : EuclideanSpace ℝ (Fin m))
    (s : EuclideanSpace ℝ (Fin m')) :
    embFst m m' t + embSnd m m' s
      = (EuclideanSpace.finAddEquivProd (n := m) (m := m')).symm (t, s) := by
  rw [embFst_apply, embSnd_apply, ← map_add]
  congr 1
  simp

/-! ## The composite is again a chart perturbation -/

theorem contMDiff_pairPert {m m' : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Ξ' : EuclideanSpace ℝ (Fin m') → CappingSpace → CappingSpace)
    {Q : ℂ → CappingSpace} (hΞ : ChartPert Q m Ξ) (hΞ' : ChartPert Q m' Ξ') :
    ContMDiff ((𝓡 (m + m')).prod (𝓡 4)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin (m + m')) × CappingSpace => pairPert Ξ Ξ' q.1 q.2) := by
  have hsplit : ContMDiff ((𝓡 (m + m')).prod (𝓡 4))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m')))
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin (m + m')) × CappingSpace => pairSplit m m' q.1) :=
    (pairSplit m m').contMDiff.comp contMDiff_fst
  have h1 : ContMDiff ((𝓡 (m + m')).prod (𝓡 4)) (𝓡 m) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin (m + m')) × CappingSpace => (pairSplit m m' q.1).1) :=
    (ContinuousLinearMap.fst ℝ _ _).contMDiff.comp hsplit
  have h2' : ContMDiff ((𝓡 (m + m')).prod (𝓡 4)) (𝓡 m') ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin (m + m')) × CappingSpace => (pairSplit m m' q.1).2) :=
    (ContinuousLinearMap.snd ℝ _ _).contMDiff.comp hsplit
  have hinner : ContMDiff ((𝓡 (m + m')).prod (𝓡 4)) ((𝓡 m').prod (𝓡 4))
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin (m + m')) × CappingSpace =>
        ((pairSplit m m' q.1).2, q.2)) :=
    h2'.prodMk contMDiff_snd
  have h2 : ContMDiff ((𝓡 (m + m')).prod (𝓡 4)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin (m + m')) × CappingSpace =>
        Ξ' (pairSplit m m' q.1).2 q.2) :=
    hΞ'.2.1.comp hinner
  have hpair : ContMDiff ((𝓡 (m + m')).prod (𝓡 4)) ((𝓡 m).prod (𝓡 4))
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin (m + m')) × CappingSpace =>
        ((pairSplit m m' q.1).1, Ξ' (pairSplit m m' q.1).2 q.2)) :=
    h1.prodMk h2
  exact hΞ.2.1.comp hpair


/-- **Surjectivity of the outer differential from the composite.**  If `f ∘ j` has surjective
differential at `x` and `j x = a`, then the differential of `f` at `a` is surjective. -/
lemma surjective_of_comp_mfderiv {m m' : ℕ}
    {j : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin (m + m'))}
    {a : EuclideanSpace ℝ (Fin (m + m'))} {x : EuclideanSpace ℝ (Fin m)}
    (hj : j x = a) {f : EuclideanSpace ℝ (Fin (m + m')) → CappingSpace}
    (hf : MDifferentiableAt (𝓡 (m + m')) (𝓡 4) f a)
    (hjm : MDifferentiableAt (𝓡 m) (𝓡 (m + m')) j x)
    (hsurj : Function.Surjective (mfderiv (𝓡 m) (𝓡 4) (f ∘ j) x)) :
    Function.Surjective (mfderiv (𝓡 (m + m')) (𝓡 4) f a) := by
  have hf' : MDifferentiableAt (𝓡 (m + m')) (𝓡 4) f (j x) := by rw [hj]; exact hf
  have h := mfderiv_comp (I := 𝓡 m) (I' := 𝓡 (m + m')) (I'' := 𝓡 4)
    (f := j) (g := f) x hf' hjm
  rw [hj] at h
  rw [h] at hsurj
  intro w
  obtain ⟨v, hv⟩ := hsurj w
  refine ⟨mfderiv (𝓡 m) (𝓡 (m + m')) j x v, ?_⟩
  rw [← hv]
  rfl

theorem surjective_mfderiv_pairPert {m m' : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Ξ' : EuclideanSpace ℝ (Fin m') → CappingSpace → CappingSpace)
    {Q : ℂ → CappingSpace} (hΞ : ChartPert Q m Ξ)
    (hsm : ContMDiff ((𝓡 (m + m')).prod (𝓡 4)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin (m + m')) × CappingSpace => pairPert Ξ Ξ' q.1 q.2))
    (a : EuclideanSpace ℝ (Fin (m + m'))) (p : CappingSpace) :
    Function.Surjective (mfderiv (𝓡 (m + m')) (𝓡 4) (fun a' => pairPert Ξ Ξ' a' p) a) := by
  classical
  set c : EuclideanSpace ℝ (Fin m') := (pairSplit m m' a).2 with hc
  let j : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin (m + m')) :=
    fun t => embFst m m' t + embSnd m m' c
  have hj : j (pairSplit m m' a).1 = a := by
    show embFst m m' (pairSplit m m' a).1 + embSnd m m' c = a
    rw [embFst_add_embSnd]
    have hpair : ((pairSplit m m' a).1, c) = pairSplit m m' a := by
      rw [hc, Prod.mk.eta]
    rw [hpair, pairSplit_apply]
    exact ContinuousLinearEquiv.symm_apply_apply _ _
  have hcomp : (fun t : EuclideanSpace ℝ (Fin m) => pairPert Ξ Ξ' (j t) p)
      = fun t => Ξ t (Ξ' c p) := by
    funext t
    show Ξ (pairSplit m m' (j t)).1 (Ξ' (pairSplit m m' (j t)).2 p) = Ξ t (Ξ' c p)
    have hjt : pairSplit m m' (j t) = (t, c) := by
      show pairSplit m m' (embFst m m' t + embSnd m m' c) = (t, c)
      rw [embFst_add_embSnd, pairSplit_apply, ContinuousLinearEquiv.apply_symm_apply]
    rw [hjt]
  have hjdiff : MDifferentiableAt (𝓡 m) (𝓡 (m + m')) j ((pairSplit m m' a).1) := by
    have hd : DifferentiableAt ℝ j ((pairSplit m m' a).1) :=
      (embFst m m').differentiableAt.add_const (embSnd m m' c)
    exact hd.mdifferentiableAt
  have hΦdiff : MDifferentiableAt (𝓡 (m + m')) (𝓡 4)
      (fun a' => pairPert Ξ Ξ' a' p) a :=
    ((hsm.contMDiffAt (x := (a, p))).comp a
      (ContMDiffAt.prodMk contMDiffAt_id contMDiffAt_const)).mdifferentiableAt (by simp)
  have hΦdiff' : MDifferentiableAt (𝓡 (m + m')) (𝓡 4)
      (fun a' => pairPert Ξ Ξ' a' p) (j ((pairSplit m m' a).1)) := by
    rw [hj]; exact hΦdiff
  have hchain := mfderiv_comp (I := 𝓡 m) (I' := 𝓡 (m + m')) (I'' := 𝓡 4)
      (f := j) (g := fun a' => pairPert Ξ Ξ' a' p) ((pairSplit m m' a).1) hΦdiff' hjdiff
  rw [hj] at hchain
  have hsurj_comp : Function.Surjective
      (mfderiv (𝓡 m) (𝓡 4) ((fun a' => pairPert Ξ Ξ' a' p) ∘ j) ((pairSplit m m' a).1)) := by
    rw [show ((fun a' => pairPert Ξ Ξ' a' p) ∘ j) = fun t => Ξ t (Ξ' c p) from hcomp]
    exact hΞ.2.2 _ _
  exact surjective_of_comp_mfderiv hj hΦdiff hjdiff hsurj_comp

theorem chartPert_pairPert {m m' : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Ξ' : EuclideanSpace ℝ (Fin m') → CappingSpace → CappingSpace)
    {Q : ℂ → CappingSpace} (hΞ : ChartPert Q m Ξ) (hΞ' : ChartPert Q m' Ξ') :
    ChartPert Q (m + m') (pairPert Ξ Ξ') :=
  ⟨pairPert_zero Ξ Ξ' hΞ hΞ', contMDiff_pairPert Ξ Ξ' hΞ hΞ',
    fun t p => surjective_mfderiv_pairPert Ξ Ξ' hΞ (contMDiff_pairPert Ξ Ξ' hΞ hΞ') t p⟩

/-! ## The sub-families of the composite

At the parameters `(t, 0)` the composite attains the chart of `Ξ` at `t`; at the parameters `(0, t')`
the chart of `Ξ'` at `t'`.  Hence the good predicate and the count of the composite agree with those
of the sub-families. -/

lemma pertChart_pairPert_embFst {m m' : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Ξ' : EuclideanSpace ℝ (Fin m') → CappingSpace → CappingSpace)
    {Q : ℂ → CappingSpace} (hΞ' : ChartPert Q m' Ξ')
    (t : EuclideanSpace ℝ (Fin m)) :
    pertChart (pairPert Ξ Ξ') Q (embFst m m' t) = pertChart Ξ Q t := by
  funext z
  show pairPert Ξ Ξ' (embFst m m' t) (Q z) = Ξ t (Q z)
  rw [pairPert_embFst Ξ Ξ' hΞ' t]

lemma pertChart_pairPert_embSnd {m m' : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Ξ' : EuclideanSpace ℝ (Fin m') → CappingSpace → CappingSpace)
    {Q : ℂ → CappingSpace} (hΞ : ChartPert Q m Ξ)
    (t : EuclideanSpace ℝ (Fin m')) :
    pertChart (pairPert Ξ Ξ') Q (embSnd m m' t) = pertChart Ξ' Q t := by
  funext z
  show pairPert Ξ Ξ' (embSnd m m' t) (Q z) = Ξ' t (Q z)
  rw [pairPert_embSnd Ξ Ξ' hΞ t]

lemma goodAt_pairPert_embFst {m m' : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Ξ' : EuclideanSpace ℝ (Fin m') → CappingSpace → CappingSpace)
    {Q : ℂ → CappingSpace} (hΞ' : ChartPert Q m' Ξ') (c : ℝ) (w : UnitAddCircle)
    (t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    GoodAt (pairPert Ξ Ξ') Q c w (embFst m m' t.1, embFst m m' t.2) ↔ GoodAt Ξ Q c w t := by
  have h1 := pertChart_pairPert_embFst Ξ Ξ' hΞ' (Q := Q) t.1
  have h2 := pertChart_pairPert_embFst Ξ Ξ' hΞ' (Q := Q) t.2
  simp only [GoodAt, h1, h2]

lemma cntAt_pairPert_embFst {m m' : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Ξ' : EuclideanSpace ℝ (Fin m') → CappingSpace → CappingSpace)
    {Q : ℂ → CappingSpace} (hΞ' : ChartPert Q m' Ξ') (c : ℝ) (w : UnitAddCircle)
    (t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    CntAt (pairPert Ξ Ξ') Q c w (embFst m m' t.1, embFst m m' t.2) = CntAt Ξ Q c w t := by
  have h1 := pertChart_pairPert_embFst Ξ Ξ' hΞ' (Q := Q) t.1
  have h2 := pertChart_pairPert_embFst Ξ Ξ' hΞ' (Q := Q) t.2
  simp only [CntAt, h1, h2]

lemma goodAt_pairPert_embSnd {m m' : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Ξ' : EuclideanSpace ℝ (Fin m') → CappingSpace → CappingSpace)
    {Q : ℂ → CappingSpace} (hΞ : ChartPert Q m Ξ) (c : ℝ) (w : UnitAddCircle)
    (t : EuclideanSpace ℝ (Fin m') × EuclideanSpace ℝ (Fin m')) :
    GoodAt (pairPert Ξ Ξ') Q c w (embSnd m m' t.1, embSnd m m' t.2) ↔ GoodAt Ξ' Q c w t := by
  have h1 := pertChart_pairPert_embSnd Ξ Ξ' hΞ (Q := Q) t.1
  have h2 := pertChart_pairPert_embSnd Ξ Ξ' hΞ (Q := Q) t.2
  simp only [GoodAt, h1, h2]

lemma cntAt_pairPert_embSnd {m m' : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Ξ' : EuclideanSpace ℝ (Fin m') → CappingSpace → CappingSpace)
    {Q : ℂ → CappingSpace} (hΞ : ChartPert Q m Ξ) (c : ℝ) (w : UnitAddCircle)
    (t : EuclideanSpace ℝ (Fin m') × EuclideanSpace ℝ (Fin m')) :
    CntAt (pairPert Ξ Ξ') Q c w (embSnd m m' t.1, embSnd m m' t.2) = CntAt Ξ' Q c w t := by
  have h1 := pertChart_pairPert_embSnd Ξ Ξ' hΞ (Q := Q) t.1
  have h2 := pertChart_pairPert_embSnd Ξ Ξ' hΞ (Q := Q) t.2
  simp only [CntAt, h1, h2]

/-! ## Norm bounds for the two blocks -/

lemma norm_embFst_le {m m' : ℕ} (t : EuclideanSpace ℝ (Fin m)) :
    ‖embFst m m' t‖ ≤ (‖embFst m m'‖ + 1) * ‖t‖ := by
  have h := ContinuousLinearMap.le_opNorm (embFst m m') t
  have h1 : (0 : ℝ) ≤ ‖t‖ := norm_nonneg _
  have h2 : ‖embFst m m'‖ * ‖t‖ ≤ (‖embFst m m'‖ + 1) * ‖t‖ := by
    apply mul_le_mul_of_nonneg_right _ h1
    linarith
  linarith [h, h2]

lemma norm_embSnd_le {m m' : ℕ} (t : EuclideanSpace ℝ (Fin m')) :
    ‖embSnd m m' t‖ ≤ (‖embSnd m m'‖ + 1) * ‖t‖ := by
  have h := ContinuousLinearMap.le_opNorm (embSnd m m') t
  have h1 : (0 : ℝ) ≤ ‖t‖ := norm_nonneg _
  have h2 : ‖embSnd m m'‖ * ‖t‖ ≤ (‖embSnd m m'‖ + 1) * ‖t‖ := by
    apply mul_le_mul_of_nonneg_right _ h1
    linarith
  linarith [h, h2]


/-! ## The germ value from a single small good configuration -/

lemma zmod2_zero_ne_one : (0 : ZMod 2) ≠ 1 := by decide

lemma zmod2_eq_of_eq_one_iff {a b : ZMod 2} (h : a = 1 ↔ b = 1) : a = b := by
  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases h01 a with ha | ha <;> rcases h01 b with hb | hb
  · rw [ha, hb]
  · rw [ha, hb] at h ⊢
    exact absurd (h.mpr rfl) zmod2_zero_ne_one
  · rw [ha, hb] at h ⊢
    exact absurd (h.mp rfl) zmod2_zero_ne_one
  · rw [ha, hb]

/-- **The germ value at an angle is the parity of any small good configuration.**  If the good
configurations of a ball of radius `ε` all have the same parity (the uniformity supplied by the
parity locality), then the germ value is `1` exactly when that common parity is odd. -/
theorem sideGerm_eq_one_iff_odd_of_uniform {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (w : UnitAddCircle)
    (hA : ∃ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
      GoodAt Ξ Q c w t)
    {ε : ℝ} (hε : 0 < ε)
    (hpar : ∀ t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
      ‖t‖ < ε → ‖t'‖ < ε → GoodAt Ξ Q c w t → GoodAt Ξ Q c w t' →
        Odd (CntAt Ξ Q c w t) = Odd (CntAt Ξ Q c w t'))
    {t₀ : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)}
    (hg₀ : GoodAt Ξ Q c w t₀) (ht₀ : ‖t₀‖ < ε) :
    sideGerm Ξ Q c w = 1 ↔ Odd (CntAt Ξ Q c w t₀) := by
  have hU : ∃ ε' : ℝ, 0 < ε' ∧ ∀ t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
      ‖t‖ < ε' → ‖t'‖ < ε' → GoodAt Ξ Q c w t → GoodAt Ξ Q c w t' →
        Odd (CntAt Ξ Q c w t) = Odd (CntAt Ξ Q c w t') := ⟨ε, hε, hpar⟩
  rw [sideGerm_eq_one_iff_frequently_good_odd Ξ Q c w hA hU]
  constructor
  · intro hf
    obtain ⟨t, ⟨hg, ho⟩, ht⟩ := (hf.and_eventually (Metric.ball_mem_nhds 0 hε)).exists
    have ht : ‖t‖ < ε := by simpa using ht
    rw [← hpar t t₀ ht ht₀ hg hg₀]
    exact ho
  · intro ho
    refine (hA.and_eventually (Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin m) ×
      EuclideanSpace ℝ (Fin m)) hε)).mono ?_
    rintro t ⟨hg, ht⟩
    have ht : ‖t‖ < ε := by simpa using ht
    exact ⟨hg, by rw [hpar t t₀ ht ht₀ hg hg₀]; exact ho⟩

/-! ## Norm bounds for the embedded configurations -/

lemma norm_embFst_pair_lt {m m' : ℕ}
    {t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)} {r : ℝ} (hr : 0 < r)
    (ht : ‖t‖ < r / (‖embFst m m'‖ + 1)) :
    ‖(embFst m m' t.1, embFst m m' t.2)‖ < r := by
  have hC : 0 < ‖embFst m m'‖ + 1 := by positivity
  have hlt : (‖embFst m m'‖ + 1) * max ‖t.1‖ ‖t.2‖ < r := by
    have h := (lt_div_iff₀ hC).mp ht
    rw [Prod.norm_def] at h
    linarith
  calc ‖(embFst m m' t.1, embFst m m' t.2)‖
      = max ‖embFst m m' t.1‖ ‖embFst m m' t.2‖ := Prod.norm_def _
    _ ≤ max ((‖embFst m m'‖ + 1) * ‖t.1‖) ((‖embFst m m'‖ + 1) * ‖t.2‖) :=
        max_le_max (norm_embFst_le t.1) (norm_embFst_le t.2)
    _ = (‖embFst m m'‖ + 1) * max ‖t.1‖ ‖t.2‖ := (mul_max_of_nonneg _ _ hC.le).symm
    _ < r := hlt

lemma norm_embSnd_pair_lt {m m' : ℕ}
    {t : EuclideanSpace ℝ (Fin m') × EuclideanSpace ℝ (Fin m')} {r : ℝ} (hr : 0 < r)
    (ht : ‖t‖ < r / (‖embSnd m m'‖ + 1)) :
    ‖(embSnd m m' t.1, embSnd m m' t.2)‖ < r := by
  have hC : 0 < ‖embSnd m m'‖ + 1 := by positivity
  have hlt : (‖embSnd m m'‖ + 1) * max ‖t.1‖ ‖t.2‖ < r := by
    have h := (lt_div_iff₀ hC).mp ht
    rw [Prod.norm_def] at h
    linarith
  calc ‖(embSnd m m' t.1, embSnd m m' t.2)‖
      = max ‖embSnd m m' t.1‖ ‖embSnd m m' t.2‖ := Prod.norm_def _
    _ ≤ max ((‖embSnd m m'‖ + 1) * ‖t.1‖) ((‖embSnd m m'‖ + 1) * ‖t.2‖) :=
        max_le_max (norm_embSnd_le t.1) (norm_embSnd_le t.2)
    _ = (‖embSnd m m'‖ + 1) * max ‖t.1‖ ‖t.2‖ := (mul_max_of_nonneg _ _ hC.le).symm
    _ < r := hlt

/-! ## The independence -/

theorem sideGerm_indep {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    (hγinj : Function.Injective γ)
    {Q : ℂ → Work.Drive.CappingSpace} (hQ : Work.Drive.IsPlaneChart γ hγne Q) {m m' : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → Work.Drive.CappingSpace → Work.Drive.CappingSpace)
    (Ξ' : EuclideanSpace ℝ (Fin m') → Work.Drive.CappingSpace → Work.Drive.CappingSpace)
    (c : ℝ) (hΞ : Work.Drive.ChartPert Q m Ξ) (hΞ' : Work.Drive.ChartPert Q m' Ξ')
    (hc : 0 < c) (hcbot : ∀ p ∈ Work.Drive.chartDisk Q, c < Work.Drive.levelOf p) :
    ∀ w : UnitAddCircle, w ∈ Work.Drive.Zc γ →
      Work.Drive.sideGerm Ξ Q c w = Work.Drive.sideGerm Ξ' Q c w := by
  intro w hw
  have hQd : IsChartData Q := IsChartData_of_isPlaneChart hQ
  have hQsm : IsSmoothChart Q := IsSmoothChart_of_isPlaneChart hQ
  have hloop : Disjoint (Set.range (coreLoop Q)) (rotCapping w '' chartDisk Q) :=
    disjoint_range_coreLoop_rotCapping_chartDisk hγne hγinj hQ hw
  have hΞc : ChartPert Q (m + m') (pairPert Ξ Ξ') := chartPert_pairPert Ξ Ξ' hΞ hΞ'
  obtain ⟨ε, δ, hε, hδ, hpar⟩ := sideGerm_parity_eq_of_close_loop Ξ Q c hΞ hQd hc hcbot w hloop
  obtain ⟨ε', δ', hε', hδ', hpar'⟩ :=
    sideGerm_parity_eq_of_close_loop Ξ' Q c hΞ' hQd hc hcbot w hloop
  obtain ⟨ε'', δ'', hε'', hδ'', hpar''⟩ :=
    sideGerm_parity_eq_of_close_loop (pairPert Ξ Ξ') Q c hΞc hQd hc hcbot w hloop
  have hA : ∃ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
      GoodAt Ξ Q c w t := sideGerm_good_exists Ξ Q c hΞ hQsm hc w
  have hA' : ∃ᶠ t : EuclideanSpace ℝ (Fin m') × EuclideanSpace ℝ (Fin m') in 𝓝 0,
      GoodAt Ξ' Q c w t := sideGerm_good_exists Ξ' Q c hΞ' hQsm hc w
  -- the two small good configurations
  have hb1 : ∀ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0, ‖t‖ < ε := by
    filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin m) ×
      EuclideanSpace ℝ (Fin m)) hε] with t ht
    simpa using ht
  have hb2 : ∀ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
      ‖t‖ < ε'' / (‖embFst m m'‖ + 1) := by
    have hpos : 0 < ε'' / (‖embFst m m'‖ + 1) := by positivity
    filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin m) ×
      EuclideanSpace ℝ (Fin m)) hpos] with t ht
    simpa using ht
  have hb1' : ∀ᶠ t : EuclideanSpace ℝ (Fin m') × EuclideanSpace ℝ (Fin m') in 𝓝 0, ‖t‖ < ε' := by
    filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin m') ×
      EuclideanSpace ℝ (Fin m')) hε'] with t ht
    simpa using ht
  have hb2' : ∀ᶠ t : EuclideanSpace ℝ (Fin m') × EuclideanSpace ℝ (Fin m') in 𝓝 0,
      ‖t‖ < ε'' / (‖embSnd m m'‖ + 1) := by
    have hpos : 0 < ε'' / (‖embSnd m m'‖ + 1) := by positivity
    filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin m') ×
      EuclideanSpace ℝ (Fin m')) hpos] with t ht
    simpa using ht
  obtain ⟨t, ⟨htg, htε⟩, htC⟩ := ((hA.and_eventually hb1).and_eventually hb2).exists
  obtain ⟨t', ⟨htg', htε'⟩, htC'⟩ := ((hA'.and_eventually hb1').and_eventually hb2').exists
  -- the embedded configurations
  have hAg : GoodAt (pairPert Ξ Ξ') Q c w (embFst m m' t.1, embFst m m' t.2) :=
    (goodAt_pairPert_embFst Ξ Ξ' (Q := Q) hΞ' c w t).mpr htg
  have hBg : GoodAt (pairPert Ξ Ξ') Q c w (embSnd m m' t'.1, embSnd m m' t'.2) :=
    (goodAt_pairPert_embSnd Ξ Ξ' (Q := Q) hΞ c w t').mpr htg'
  have hAn : ‖(embFst m m' t.1, embFst m m' t.2)‖ < ε'' :=
    norm_embFst_pair_lt (m := m) (m' := m') (by positivity) htC
  have hBn : ‖(embSnd m m' t'.1, embSnd m m' t'.2)‖ < ε'' :=
    norm_embSnd_pair_lt (m := m) (m' := m') (by positivity) htC'
  have hparAB : Odd (CntAt (pairPert Ξ Ξ') Q c w (embFst m m' t.1, embFst m m' t.2))
      = Odd (CntAt (pairPert Ξ Ξ') Q c w (embSnd m m' t'.1, embSnd m m' t'.2)) :=
    hpar'' _ _ w hAn hBn (by rw [dist_self]; exact hδ'') hAg hBg
  have hparEq : Odd (CntAt Ξ Q c w t) = Odd (CntAt Ξ' Q c w t') := by
    rw [← cntAt_pairPert_embFst Ξ Ξ' (Q := Q) hΞ' c w t,
      ← cntAt_pairPert_embSnd Ξ Ξ' (Q := Q) hΞ c w t']
    exact hparAB
  -- the two germ values
  have hiff : sideGerm Ξ Q c w = 1 ↔ Odd (CntAt Ξ Q c w t) :=
    sideGerm_eq_one_iff_odd_of_uniform Ξ Q c w hA hε
      (fun s s' hs hs' hg hg' => hpar s s' w hs hs' (by rw [dist_self]; exact hδ) hg hg')
      htg htε
  have hiff' : sideGerm Ξ' Q c w = 1 ↔ Odd (CntAt Ξ' Q c w t') :=
    sideGerm_eq_one_iff_odd_of_uniform Ξ' Q c w hA' hε'
      (fun s s' hs hs' hg hg' => hpar' s s' w hs hs' (by rw [dist_self]; exact hδ') hg hg')
      htg' htε'
  exact zmod2_eq_of_eq_one_iff (hiff.trans ((iff_of_eq hparEq).trans hiff'.symm))

end

end Work.Drive
