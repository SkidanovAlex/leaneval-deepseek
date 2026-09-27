import Mathlib
import Submission.Work.Drive.Whitney.whitneyDiscDefs
import Submission.Work.Projection.dimH_image_le_of_contDiffOn
import Submission.Work.Projection.Defs

/-!
# The chartwise parametrisation of the avoidance-bad translation parameters

`Work.Drive.Whitney.badAvoid f γ₁ γ₂` is the set of translation parameters `v` for which the
candidate Whitney disc `discMap f γ₁ γ₂ v` meets `f '' M` inside the open square `discSq`.

Since `discBump (0,0)` does not vanish on `discSq`, a bad `v` with witness `(p, y)` is recovered
from the three other blocks of `v` by solving for the `(0,0)`-block.  This file sets up that
inverse map (`badAvoidParam`) together with its domain (`badAvoidDom`) and its basic properties:
the domain is open, the parametrisation is `C^∞` there, and it is surjective onto the bad set.

The source of the parametrisation is
`(ℝ × ℝ) × ℝ^n × ({k : Fin 2 × Fin 2 // k ≠ (0,0)} → ℝ^{2n})`, of dimension `2 + n + 3*(2n)`,
which is the dimension bound `7*n + 2` of the target.
-/

open scoped Manifold ContDiff
open Set Metric
open scoped ENNReal Topology

namespace Work.Drive.Whitney

noncomputable section

/-- The three blocks of the translation parameter other than the `(0,0)`-block. -/
abbrev discIdxFree : Type := {k : Fin 2 × Fin 2 // k ≠ (0,0)}

/-- The source of the chartwise parametrisation of the bad parameters. -/
abbrev discParamSrc (n : ℕ) : Type :=
  (ℝ × ℝ) × EuclideanSpace ℝ (Fin n) × (discIdxFree → EuclideanSpace ℝ (Fin (2 * n)))

/-- The domain of the parametrisation of the bad parameters in the chart at `x₀`: the open
square in the disc plane, the chart target, and all the free blocks. -/
def badAvoidDom {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (x₀ : M) : Set (discParamSrc n) :=
  discSq ×ˢ (chartAt (EuclideanSpace ℝ (Fin n)) x₀).target ×ˢ Set.univ

/-- The part of the perturbation contributed by the three free blocks. -/
def discFreeSum {n : ℕ} (p : ℝ × ℝ) (w : discIdxFree → EuclideanSpace ℝ (Fin (2 * n))) :
    EuclideanSpace ℝ (Fin (2 * n)) :=
  ∑ k : discIdxFree, discBump k.1 p • w k

/-- The value of the `(0,0)`-block forced by the values of the other three blocks. -/
def badAvoidSolve {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (γ₁ γ₂ : ℝ → M) (x₀ : M)
    (q : discParamSrc n) : EuclideanSpace ℝ (Fin (2 * n)) :=
  (discBump (0, 0) q.1)⁻¹ •
    (f ((chartAt (EuclideanSpace ℝ (Fin n)) x₀).symm q.2.1) - baseDisc f γ₁ γ₂ q.1
      - discFreeSum q.1 q.2.2)

/-- The chartwise inverse of the "solve for the `(0,0)`-block" map: from a point `p` of the open
square, a chart coordinate `y` and the three free blocks `w`, produce the translation parameter
`v` with `v k = w k` for `k ≠ (0,0)` and `v (0,0)` chosen so that `discMap v p = f (chart⁻¹ y)`. -/
def badAvoidParam {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (γ₁ γ₂ : ℝ → M) (x₀ : M) :
    discParamSrc n → (Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n)) :=
  fun q k => if hk : k = (0, 0) then badAvoidSolve f γ₁ γ₂ x₀ q else q.2.2 ⟨k, hk⟩

@[simp] lemma badAvoidParam_zero {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (γ₁ γ₂ : ℝ → M) (x₀ : M) (q : discParamSrc n) :
    badAvoidParam f γ₁ γ₂ x₀ q (0, 0) = badAvoidSolve f γ₁ γ₂ x₀ q :=
  dif_pos rfl

lemma badAvoidParam_of_ne {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (γ₁ γ₂ : ℝ → M) (x₀ : M) (q : discParamSrc n)
    {k : Fin 2 × Fin 2} (hk : k ≠ (0, 0)) :
    badAvoidParam f γ₁ γ₂ x₀ q k = q.2.2 ⟨k, hk⟩ :=
  dif_neg hk

end

end Work.Drive.Whitney

namespace Work.Drive.Whitney

noncomputable section

open scoped Manifold ContDiff
open Set Metric
open scoped ENNReal Topology

variable {n : ℕ}

/-- Splitting a sum over the four blocks into the `(0,0)`-block and the remaining three. -/
lemma sum_split_zero {E : Type*} [AddCommMonoid E] (g : Fin 2 × Fin 2 → E) :
    (∑ k : Fin 2 × Fin 2, g k) = g (0, 0) + ∑ k : discIdxFree, g k.1 := by
  classical
  rw [← Finset.sum_erase_add Finset.univ g (Finset.mem_univ (0, 0))]
  rw [Finset.sum_subtype (p := fun k : Fin 2 × Fin 2 => k ≠ (0, 0))
    (Finset.univ.erase (0, 0)) (fun x => by simp) g]
  rw [add_comm]

/-- The perturbation sum split at the `(0,0)`-block. -/
lemma discPert_split {n : ℕ} (v : (Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n)))
    (p : ℝ × ℝ) :
    discPert v p = discBump (0, 0) p • v (0, 0)
      + ∑ k : discIdxFree, discBump k.1 p • v k.1 := by
  rw [discPert, sum_split_zero (fun k => discBump k p • v k)]

open scoped ENNReal Topology

variable {n : ℕ}

/-- The parametrisation reproduces the three free blocks. -/
lemma discPert_badAvoidParam {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (γ₁ γ₂ : ℝ → M) (x₀ : M) (q : discParamSrc n) :
    discPert (badAvoidParam f γ₁ γ₂ x₀ q) q.1
      = discBump (0, 0) q.1 • badAvoidSolve f γ₁ γ₂ x₀ q + discFreeSum q.1 q.2.2 := by
  rw [discPert_split, discFreeSum]
  have h1 : discBump (0, 0) q.1 • badAvoidParam f γ₁ γ₂ x₀ q (0, 0)
      = discBump (0, 0) q.1 • badAvoidSolve f γ₁ γ₂ x₀ q := by
    rw [badAvoidParam_zero]
  have h2 : (∑ k : discIdxFree, discBump k.1 q.1 • badAvoidParam f γ₁ γ₂ x₀ q k.1)
      = ∑ k : discIdxFree, discBump k.1 q.1 • q.2.2 k :=
    Finset.sum_congr rfl fun k _ => by rw [badAvoidParam_of_ne f γ₁ γ₂ x₀ q k.2]
  rw [h1, h2]

/-- The domain of the parametrisation is open. -/
lemma isOpen_badAvoidDom {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (x₀ : M) : IsOpen (badAvoidDom (n := n) x₀) := by
  rw [badAvoidDom, discSq]
  exact (isOpen_Ioo.prod isOpen_Ioo).prod
    ((chartAt (EuclideanSpace ℝ (Fin n)) x₀).open_target.prod isOpen_univ)

/-- The interpolated base disc is smooth. -/
lemma contDiff_baseDisc {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (γ₁ γ₂ : ℝ → M)
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hγ₁ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₁)
    (hγ₂ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₂) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (baseDisc f γ₁ γ₂) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => f (γ₁ s)) :=
    (hf.comp hγ₁).contDiff
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => f (γ₂ s)) :=
    (hf.comp hγ₂).contDiff
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => sigR p.1) := by
    rw [show (fun p : ℝ × ℝ => sigR p.1) = (fun p : ℝ × ℝ => (p.1 + 1) / 2) from rfl]
    fun_prop
  rw [show baseDisc f γ₁ γ₂ = (fun p : ℝ × ℝ =>
      (1 - p.2) • f (γ₁ (sigR p.1)) + p.2 • f (γ₂ (sigR p.1))) from rfl]
  have hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => (1 : ℝ) - p.2) := by
    fun_prop
  have hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => (p.2 : ℝ)) := by
    fun_prop
  exact (hA.smul (h1.comp hs)).add (hB.smul (h2.comp hs))

/-- The chart representation of `f` is smooth on the chart target. -/
lemma contDiffOn_chartRepG {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (x₀ : M) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => f ((chartAt (EuclideanSpace ℝ (Fin n)) x₀).symm y))
      (chartAt (EuclideanSpace ℝ (Fin n)) x₀).target := by
  have h : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => f ((chartAt (EuclideanSpace ℝ (Fin n)) x₀).symm y))
      (chartAt (EuclideanSpace ℝ (Fin n)) x₀).target :=
    ContMDiffOn.comp (t := (Set.univ : Set M)) hf.contMDiffOn
      (contMDiffOn_chart_symm (x := x₀)) (Set.subset_univ _)
  exact h.contDiffOn

/-- The chartwise parametrisation of the bad parameters is `C^1`. -/
lemma contDiffOn_badAvoidParam {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (γ₁ γ₂ : ℝ → M)
    (hγ₁ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₁)
    (hγ₂ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₂)
    (x₀ : M) :
    ContDiffOn ℝ 1 (badAvoidParam f γ₁ γ₂ x₀) (badAvoidDom x₀) := by
  have hfst : ContDiffOn ℝ 1 (fun q : discParamSrc n => q.1) (badAvoidDom x₀) := by fun_prop
  have hsnd : ContDiffOn ℝ 1 (fun q : discParamSrc n => q.2.1) (badAvoidDom x₀) := by fun_prop
  have hsnd2 : ContDiffOn ℝ 1 (fun q : discParamSrc n => q.2.2) (badAvoidDom x₀) := by fun_prop
  have hbaseC : ContDiff ℝ 1 (baseDisc f γ₁ γ₂) :=
    (contDiff_baseDisc f γ₁ γ₂ hf hγ₁ hγ₂).of_le (by norm_num)
  have hbase : ContDiffOn ℝ 1 (fun q : discParamSrc n => baseDisc f γ₁ γ₂ q.1)
      (badAvoidDom x₀) :=
    ContDiff.comp_contDiffOn (f := fun q : discParamSrc n => q.1)
      (g := baseDisc f γ₁ γ₂) hbaseC hfst
  have hrepC : ContDiffOn ℝ 1 (fun y : EuclideanSpace ℝ (Fin n) =>
      f ((chartAt (EuclideanSpace ℝ (Fin n)) x₀).symm y))
      (chartAt (EuclideanSpace ℝ (Fin n)) x₀).target :=
    (contDiffOn_chartRepG f hf x₀).of_le (by norm_num)
  have hrep' : ContDiffOn ℝ 1 (fun q : discParamSrc n =>
      f ((chartAt (EuclideanSpace ℝ (Fin n)) x₀).symm q.2.1)) (badAvoidDom x₀) :=
    ContDiffOn.comp (f := fun q : discParamSrc n => q.2.1)
      (g := fun y : EuclideanSpace ℝ (Fin n) =>
        f ((chartAt (EuclideanSpace ℝ (Fin n)) x₀).symm y))
      (t := (chartAt (EuclideanSpace ℝ (Fin n)) x₀).target)
      hrepC hsnd (fun q hq => hq.2.1)
  have hfree : ContDiffOn ℝ 1 (fun q : discParamSrc n => discFreeSum q.1 q.2.2)
      (badAvoidDom x₀) := by
    have hfun : (fun q : discParamSrc n => discFreeSum q.1 q.2.2)
        = fun q => ∑ k : discIdxFree, discBump k.1 q.1 • q.2.2 k := by
      funext q
      rw [discFreeSum]
    rw [hfun]
    refine ContDiffOn.sum (s := Finset.univ) fun k _ => ?_
    have hb : ContDiffOn ℝ 1 (fun q : discParamSrc n => discBump k.1 q.1) (badAvoidDom x₀) :=
      ((contDiff_discBump k.1).of_le (by norm_num)).comp_contDiffOn hfst
    have hc : ContDiffOn ℝ 1 (fun q : discParamSrc n => q.2.2 k) (badAvoidDom x₀) :=
      (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : discIdxFree => EuclideanSpace ℝ (Fin (2 * n))) k).contDiff.comp_contDiffOn
        hsnd2
    exact hb.smul hc
  rw [contDiffOn_pi]
  intro k
  by_cases hk : k = (0, 0)
  · have hfun : (fun q : discParamSrc n => badAvoidParam f γ₁ γ₂ x₀ q k)
        = fun q => badAvoidSolve f γ₁ γ₂ x₀ q := by
      funext q
      rw [hk, badAvoidParam_zero]
    rw [hfun]
    have hfun2 : badAvoidSolve f γ₁ γ₂ x₀ = (fun q : discParamSrc n =>
        (discBump (0, 0) q.1)⁻¹ • (f ((chartAt (EuclideanSpace ℝ (Fin n)) x₀).symm q.2.1)
          - baseDisc f γ₁ γ₂ q.1 - discFreeSum q.1 q.2.2)) := rfl
    rw [hfun2]
    have h₁ : ContDiffOn ℝ 1 (fun q : discParamSrc n => discBump (0, 0) q.1)
        (badAvoidDom x₀) :=
      ((contDiff_discBump (0, 0)).of_le (by norm_num)).comp_contDiffOn hfst
    have h₂ : ∀ q : discParamSrc n, q ∈ badAvoidDom x₀ → discBump (0, 0) q.1 ≠ 0 :=
      fun q hq => discBump_zero_ne hq.1
    refine ContDiffOn.smul (h₁.inv h₂) ?_
    exact ContDiffOn.sub (ContDiffOn.sub hrep' hbase) hfree
  · have hfun : (fun q : discParamSrc n => badAvoidParam f γ₁ γ₂ x₀ q k)
        = fun q => q.2.2 ⟨k, hk⟩ := by
      funext q
      exact badAvoidParam_of_ne f γ₁ γ₂ x₀ q hk
    rw [hfun]
    exact (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : discIdxFree => EuclideanSpace ℝ (Fin (2 * n)))
      ⟨k, hk⟩).contDiff.comp_contDiffOn hsnd2

/-- The parametrisation is the inverse of the map recording the three free blocks and the image
point: it recovers `v` from `(p, y, v|_free)`. -/
lemma badAvoidParam_eq_of {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (γ₁ γ₂ : ℝ → M) (x₀ : M)
    (q : discParamSrc n) (v : (Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n)))
    (hq : q ∈ badAvoidDom x₀)
    (hw : ∀ k : discIdxFree, v k.1 = q.2.2 k)
    (hv : discMap f γ₁ γ₂ v q.1 = f ((chartAt (EuclideanSpace ℝ (Fin n)) x₀).symm q.2.1)) :
    badAvoidParam f γ₁ γ₂ x₀ q = v := by
  have hp : q.1 ∈ discSq := hq.1
  have hpert : discPert v q.1
      = discBump (0, 0) q.1 • v (0, 0) + discFreeSum q.1 q.2.2 := by
    rw [discPert_split, discFreeSum]
    have h2 : (∑ k : discIdxFree, discBump k.1 q.1 • v k.1)
        = ∑ k : discIdxFree, discBump k.1 q.1 • q.2.2 k :=
      Finset.sum_congr rfl fun k _ => by rw [hw k]
    rw [h2]
  have hkey : f ((chartAt (EuclideanSpace ℝ (Fin n)) x₀).symm q.2.1)
      - baseDisc f γ₁ γ₂ q.1 - discFreeSum q.1 q.2.2
      = discBump (0, 0) q.1 • v (0, 0) := by
    have h := hv
    rw [discMap, hpert] at h
    rw [← h]
    abel
  funext k
  rw [badAvoidParam]
  by_cases hk : k = (0, 0)
  · rw [dif_pos hk, hk, badAvoidSolve, hkey,
      inv_smul_smul₀ (discBump_zero_ne hp)]
  · rw [dif_neg hk]
    exact (hw ⟨k, hk⟩).symm

/-- The parametrisation indeed produces a bad parameter. -/
lemma discMap_badAvoidParam {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (γ₁ γ₂ : ℝ → M) (x₀ : M)
    {p : ℝ × ℝ} (hp : p ∈ discSq) (y : EuclideanSpace ℝ (Fin n))
    (w : discIdxFree → EuclideanSpace ℝ (Fin (2 * n))) :
    discMap f γ₁ γ₂ (badAvoidParam f γ₁ γ₂ x₀ (p, y, w)) p
      = f ((chartAt (EuclideanSpace ℝ (Fin n)) x₀).symm y) := by
  rw [discMap, discPert_badAvoidParam, badAvoidSolve,
    smul_inv_smul₀ (discBump_zero_ne hp)]
  abel

/-- `badAvoid` is covered by the chartwise parametrisations. -/
lemma badAvoid_subset_param {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (γ₁ γ₂ : ℝ → M)
    (p : ℕ → M) (hp : ∀ y : M, ∃ i, y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).source) :
    badAvoid f γ₁ γ₂ ⊆ ⋃ i, badAvoidParam f γ₁ γ₂ (p i) '' badAvoidDom (p i) := by
  rintro v ⟨p₀, hp₀, y, hy⟩
  obtain ⟨i, hi⟩ := hp y
  refine Set.mem_iUnion.2 ⟨i, ?_⟩
  refine ⟨(p₀, (chartAt (EuclideanSpace ℝ (Fin n)) (p i)) y, fun k => v k.1), ?_, ?_⟩
  · exact ⟨hp₀, (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).map_source hi, trivial⟩
  · refine badAvoidParam_eq_of f γ₁ γ₂ (p i) _ v
      ⟨hp₀, (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).map_source hi, trivial⟩
      (fun k => rfl) ?_
    show discMap f γ₁ γ₂ v p₀ = f (((chartAt (EuclideanSpace ℝ (Fin n)) (p i)).symm)
      ((chartAt (EuclideanSpace ℝ (Fin n)) (p i)) y))
    rw [(chartAt (EuclideanSpace ℝ (Fin n)) (p i)).left_inv hi]
    exact hy

/-- The three free blocks together with the chart coordinate have dimension `7 * n + 2`. -/
lemma finrank_discParamSrc (n : ℕ) : Module.finrank ℝ (discParamSrc n) = 7 * n + 2 := by
  have hcard : Fintype.card discIdxFree = 3 := by
    rw [Fintype.card_subtype_compl (fun k : Fin 2 × Fin 2 => k = (0, 0)),
      Fintype.card_prod, Fintype.card_fin, Fintype.card_unique]
  have h2 : Module.finrank ℝ (ℝ × ℝ) = 2 := by
    rw [Module.finrank_prod]
    simp
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by
    rw [finrank_euclideanSpace, Fintype.card_fin]
  have h3 : Module.finrank ℝ (discIdxFree → EuclideanSpace ℝ (Fin (2 * n))) = 3 * (2 * n) := by
    rw [Module.finrank_pi_fintype]
    simp only [finrank_euclideanSpace, Fintype.card_fin]
    rw [Finset.sum_const_nat (m := 2 * n) (f := fun _ : discIdxFree => 2 * n) (fun i _ => rfl),
      Finset.card_univ, hcard]
  have hsplit : Module.finrank ℝ (discParamSrc n)
      = Module.finrank ℝ (ℝ × ℝ)
        + (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))
          + Module.finrank ℝ (discIdxFree → EuclideanSpace ℝ (Fin (2 * n)))) := by
    show Module.finrank ℝ ((ℝ × ℝ) × (EuclideanSpace ℝ (Fin n) ×
      (discIdxFree → EuclideanSpace ℝ (Fin (2 * n))))) = _
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_prod]
  rw [hsplit, h2, hn, h3]
  ring

end

end Work.Drive.Whitney
