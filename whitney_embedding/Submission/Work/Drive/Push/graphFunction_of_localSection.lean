import Mathlib
import Submission.Work.Whitney.CutPush.local_graph_data

namespace Work.Drive.Push

open scoped Topology

set_option linter.unusedVariables false

/-- **The local graph presentation of `f` over the first factor of `L`.**

Given a smooth left inverse `σ` (on `U`) of the first component `x ↦ (L (f x)).1`, the map `f` is
locally the graph of a *globally* smooth function `h` of that first component: near `x₀` one has
`(L (f x)).2 = h ((L (f x)).1)`.

The function `h` is built as a bump function `χ` (supported inside `S`, `= 1` near `(L (f x₀)).1`)
times the smooth-on-`S` function `v ↦ (L (f (σ v))).2`; the product is globally smooth by the gluing
lemma of `CutPush/local_graph_data`. -/
theorem graphFunction_of_localSection {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (L : EuclideanSpace ℝ (Fin (2 * n)) ≃L[ℝ]
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (x₀ : M)
    (σ : EuclideanSpace ℝ (Fin n) → M)
    (S : Set (EuclideanSpace ℝ (Fin n))) (U : Set M)
    (hS : IsOpen S)
    (hGS : (L (f x₀)).1 ∈ S)
    (hσS : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u => f (σ u)) S)
    (hU : IsOpen U) (hx₀U : x₀ ∈ U)
    (hright : ∀ u ∈ S, (L (f (σ u))).1 = u)
    (hleft : ∀ x ∈ U, σ ((L (f x)).1) = x)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (O : Set M) (h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      IsOpen O ∧ x₀ ∈ O ∧
      (∀ x ∈ O, (L (f x)).1 ∈ Metric.ball ((L (f x₀)).1) ε) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h ∧
      (∀ x ∈ O, (L (f x)).2 = h ((L (f x)).1)) := by
  classical
  -- the first component `φ x = (L (f x)).1`, continuous since `f` is
  set φ : M → EuclideanSpace ℝ (Fin n) := fun x => (L (f x)).1 with hφdef
  have hφcont : Continuous φ := by
    have h1 : Continuous fun x : M => L (f x) :=
      L.continuous.comp hf.continuous
    exact (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))).continuous.comp h1
  -- bump function supported inside `S`, `= 1` near `φ x₀`
  obtain ⟨χ, r, hr, hχc, hχ1, _hχνn, hχsupp⟩ :=
    Work.Whitney.CutPush.exists_contDiffBump_near (E := EuclideanSpace ℝ (Fin n)) hS hGS
  -- the smooth-on-`S` function whose graph we take
  set g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun v => (L (f (σ v))).2 with hgdef
  have hgOn : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g S := by
    have hσ' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v => f (σ v)) S :=
      hσS.contDiffOn
    have hclm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : EuclideanSpace ℝ (Fin (2 * n)) => (L y).2) :=
      ((ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n))
        (EuclideanSpace ℝ (Fin n))).comp
          (L : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ]
            (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))).contDiff
    have hcomp : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v => (L (f (σ v))).2) S :=
      hclm.comp_contDiffOn hσ'
    simpa only [hgdef] using hcomp
  -- the graph function
  set hfun : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun v => χ v • g v with hhdef
  have hOn : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) hfun S :=
    hχc.contDiffOn.smul hgOn
  have hsupp : tsupport hfun ⊆ S := by
    refine (closure_mono ?_).trans hχsupp
    intro v hv
    simp only [Function.mem_support] at hv ⊢
    intro hv0
    exact hv (by simp [hhdef, hv0])
  have hfun_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) hfun :=
    Work.Whitney.CutPush.contDiff_of_contDiffOn_of_tsupport_subset hS hOn hsupp
  -- the open set on which everything holds
  refine ⟨U ∩ φ ⁻¹' S ∩ φ ⁻¹' (Metric.ball (φ x₀) r) ∩ φ ⁻¹' (Metric.ball (φ x₀) ε),
    hfun, ?_, ?_, ?_, hfun_smooth, ?_⟩
  · exact IsOpen.inter (IsOpen.inter (IsOpen.inter hU (hS.preimage hφcont))
      ((Metric.isOpen_ball).preimage hφcont)) ((Metric.isOpen_ball).preimage hφcont)
  · refine ⟨⟨⟨hx₀U, hGS⟩, ?_⟩, ?_⟩
    · exact Metric.mem_ball.mpr (by simpa using hr)
    · exact Metric.mem_ball.mpr (by simpa using hε)
  · intro x hx
    exact hx.2
  · intro x hx
    obtain ⟨⟨⟨hxU, _hxS⟩, hxballr⟩, _hxballε⟩ := hx
    have hχval : χ (φ x) = 1 := hχ1 _ (le_of_lt hxballr)
    have hσx : σ (φ x) = x := by
      have := hleft x hxU
      simpa [hφdef] using this
    have hmain : hfun (φ x) = (L (f x)).2 := by
      simp only [hhdef]
      rw [hχval, one_smul]
      simp only [hgdef]
      rw [hσx]
    exact hmain.symm

end Work.Drive.Push
