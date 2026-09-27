import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.isCritical_iff_chartRep
import Submission.Work.Drive.N2.isCritical_nondegCrit_congr_add

namespace Work.Drive.N2

open scoped Manifold ContDiff
open Filter

/-- Criticality and nondegeneracy at a point depend only on the germ of the function at that
point. -/
lemma isCritical_nondegCrit_congr_eventuallyEq {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    {f g : M → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) (hg : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ g)
    (x : M) (h : f =ᶠ[nhds x] g) :
    (Work.Drive.Morse.IsCritical f x ↔ Work.Drive.Morse.IsCritical g x) ∧
      (Work.Drive.Morse.NondegCrit f x ↔ Work.Drive.Morse.NondegCrit g x) := by
  have h' : f =ᶠ[nhds x] (fun y : M => g y + 0) :=
    h.trans (Filter.EventuallyEq.of_eq (by funext y; simp))
  exact isCritical_nondegCrit_congr_add hf hg x 0 h'

open scoped Manifold ContDiff in
/-- **A bump perturbation supported near an isolated nondegenerate critical point does not move the
critical set, for small enough size.**  Let `f` be smooth, `p` a nondegenerate critical point of `f`,
`T` an open neighbourhood of `p` whose closure is contained in the source of the chart at `p` and
contains no critical point of `f` other than `p`, and let `χ` be a smooth bump equal to `1` near `p`
and supported in `T`.  Then all sufficiently small multiples `f + ε χ` are smooth, have exactly the
same critical points as `f` (and all of them nondegenerate), and differ from `f` only at `p`
(at the other critical points), with `(f + ε χ) p = f p + ε`.

Proof plan: put `e = extChartAt (𝓡 2) p`, `c = e p`, `F = f ∘ e.symm`, `V = interior {x | χ x = 1}`
(open, contains `p`), `K = closure T \ V` (closed in the compact `M`, hence compact, and contained in
`e.source`).  On `K` the derivative of `f` does not vanish: if `x ∈ K` were critical, then
`fderiv ℝ F (e x) = 0` (by `Work.Drive.N2.isCritical_iff_chartRep`, using `x ∈ closure T ⊆ e.source`),
and `x ≠ p` because `p ∈ V ⊆ Kᶜ`; this contradicts `hTnd`.  So `m = inf {‖fderiv ℝ F (e x)‖ : x ∈ K}`
is positive (`e '' K` is compact) and `M = sup {‖fderiv ℝ (χ ∘ e.symm) (e x)‖ : x ∈ K}` is finite;
take `δ = m / (M + 1)` (if `K = ∅` take `δ = 1`).  If `x ∈ K` and `0 < ε < δ`, the chart
representation of `f + εχ` is `y ↦ F y + ε * χ (e.symm y)`, so `fderiv` of it at `e x` has norm at
least `m - ε * M > 0`; hence `f + εχ` is not critical at `x` while `f` is not critical at `x` either.
Outside `closure T` the bump vanishes on a neighbourhood, and on `V` it is identically `1`, so off `K`
the two criticality predicates agree by the germ argument; for the nondegeneracy conjunct use that on
`V` the function `f + εχ` equals `f + ε` and off `closure T` it equals `f` on a neighbourhood. -/
theorem exists_perturbation_delta {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] [T2Space M]
    [CompactSpace M] (f : M → ℝ)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hnd : ∀ x, Work.Drive.Morse.IsCritical f x → Work.Drive.Morse.NondegCrit f x)
    (p : M) (hp : Work.Drive.Morse.NondegCrit f p)
    (T : Set M) (hTopen : IsOpen T) (hpT : p ∈ T)
    (hTnd : ∀ x, Work.Drive.Morse.IsCritical f x → x ∈ closure T → x = p)
    (hTchart : closure T ⊆ (extChartAt (𝓡 2) p).source)
    (χ : M → ℝ) (hχ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ)
    (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (hχp : χ p = 1)
    (hχsupp : Function.support χ ⊆ T)
    (hχV : ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ ∀ x ∈ V, χ x = 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
        ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun x => f x + ε * χ x) ∧
        (∀ x, Work.Drive.Morse.IsCritical (fun x => f x + ε * χ x) x ↔
          Work.Drive.Morse.IsCritical f x) ∧
        (∀ x, Work.Drive.Morse.IsCritical (fun x => f x + ε * χ x) x →
          Work.Drive.Morse.NondegCrit (fun x => f x + ε * χ x) x) ∧
        (∀ x, Work.Drive.Morse.IsCritical f x → x ≠ p → f x + ε * χ x = f x) ∧
        (fun x => f x + ε * χ x) p = f p + ε := by
  classical
  obtain ⟨V, hVopen, hpV, hV1⟩ := hχV
  set e := extChartAt (𝓡 2) p with he
  set F : EuclideanSpace ℝ (Fin 2) → ℝ := fun y => f (e.symm y) with hF
  set G : EuclideanSpace ℝ (Fin 2) → ℝ := fun y => χ (e.symm y) with hG
  set K : Set M := closure T \ V with hKdef
  have hKcpt : IsCompact K := by
    rw [hKdef, Set.sdiff_eq]
    exact (isClosed_closure.inter hVopen.isClosed_compl).isCompact
  have hKsub : K ⊆ e.source := fun x hx => hTchart hx.1
  have hs_cpt : IsCompact (e '' K) :=
    hKcpt.image_of_continuousOn ((continuousOn_extChartAt (I := 𝓡 2) p).mono hKsub)
  have hs_sub : e '' K ⊆ e.target := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := hy
    exact e.map_source (hKsub hx)
  have hFcd : ContDiffOn ℝ ∞ F e.target := by
    have h1 : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ℝ) ∞ (f ∘ e.symm) e.target :=
      (hf.contMDiffOn (s := Set.univ)).comp (contMDiffOn_extChartAt_symm (I := 𝓡 2) p)
        (fun y _ => Set.mem_univ _)
    exact h1.contDiffOn
  have hGcd : ContDiffOn ℝ ∞ G e.target := by
    have h1 : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ℝ) ∞ (χ ∘ e.symm) e.target :=
      (hχ.contMDiffOn (s := Set.univ)).comp (contMDiffOn_extChartAt_symm (I := 𝓡 2) p)
        (fun y _ => Set.mem_univ _)
    exact h1.contDiffOn
  have hcontF : ContinuousOn (fun y => ‖fderiv ℝ F y‖) (e '' K) :=
    ((hFcd.continuousOn_fderiv_of_isOpen (isOpen_extChartAt_target p) (by simp)).norm).mono hs_sub
  have hcontG : ContinuousOn (fun y => ‖fderiv ℝ G y‖) (e '' K) :=
    ((hGcd.continuousOn_fderiv_of_isOpen (isOpen_extChartAt_target p) (by simp)).norm).mono hs_sub
  -- the derivative of `f` does not vanish on `K`
  have hcritchart : ∀ x ∈ K, ¬ Work.Drive.Morse.IsCritical f x := by
    intro x hxK hcrit
    have hxsrc : x ∈ e.source := hKsub hxK
    have hzero : fderiv ℝ F (e x) = 0 := (isCritical_iff_chartRep f hf p x hxsrc).mp hcrit
    have hxp : x = p := hTnd x hcrit hxK.1
    exact hxK.2 (hxp ▸ hpV)
  have hpos : ∀ y ∈ e '' K, (0 : ℝ) < ‖fderiv ℝ F y‖ := by
    rintro y ⟨x, hxK, rfl⟩
    exact norm_pos_iff.mpr
      fun h => hcritchart x hxK ((isCritical_iff_chartRep f hf p x (hKsub hxK)).mpr h)
  obtain ⟨m, hm0, hmin⟩ : ∃ m : ℝ, 0 < m ∧ ∀ y ∈ e '' K, m ≤ ‖fderiv ℝ F y‖ :=
    hs_cpt.exists_forall_le' hcontF hpos
  have hbd : BddAbove ((fun y => ‖fderiv ℝ G y‖) '' (e '' K)) := hs_cpt.bddAbove_image hcontG
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ y ∈ e '' K, ‖fderiv ℝ G y‖ ≤ M := by
    obtain ⟨M, hM⟩ := hbd
    exact ⟨M, fun y hy => hM (Set.mem_image_of_mem _ hy)⟩
  refine ⟨m / (max M 0 + 1), div_pos hm0 (by have := le_max_right M 0; linarith), ?_⟩
  intro ε hε hεδ
  have hsm : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun x => f x + ε * χ x) :=
    hf.add (contMDiff_const.mul hχ)
  have hmM : ε * max M 0 < m := by
    have h1 : ε * (max M 0 + 1) < m :=
      (lt_div_iff₀ (by have := le_max_right M 0; linarith)).mp hεδ
    have h2 : ε * max M 0 ≤ ε * (max M 0 + 1) :=
      mul_le_mul_of_nonneg_left (by linarith [le_max_right M 0]) (le_of_lt hε)
    linarith
  -- on `K` the perturbation has no critical point either
  have hKnot : ∀ x ∈ K, ¬ Work.Drive.Morse.IsCritical (fun y => f y + ε * χ y) x := by
    intro x hxK hcrit
    have hxsrc : x ∈ e.source := hKsub hxK
    have h1 : fderiv ℝ (fun y => F y + ε * G y) (e x) = 0 :=
      (isCritical_iff_chartRep (fun y => f y + ε * χ y) hsm p x hxsrc).mp hcrit
    have h2 : fderiv ℝ (fun y => F y + ε * G y) (e x)
        = fderiv ℝ F (e x) + ε • fderiv ℝ G (e x) := by
      have hxt : e x ∈ e.target := e.map_source hxsrc
      have htop : e.target ∈ nhds (e x) := (isOpen_extChartAt_target p).mem_nhds hxt
      have hFd : DifferentiableAt ℝ F (e x) := (hFcd.contDiffAt htop).differentiableAt (by simp)
      have hGd : DifferentiableAt ℝ G (e x) := (hGcd.contDiffAt htop).differentiableAt (by simp)
      exact (hFd.hasFDerivAt.add (hGd.hasFDerivAt.const_mul ε)).fderiv
    rw [h2] at h1
    have hle1 : m ≤ ‖fderiv ℝ F (e x)‖ := hmin (e x) ⟨x, hxK, rfl⟩
    have hle2 : ‖fderiv ℝ G (e x)‖ ≤ max M 0 :=
      (hM (e x) ⟨x, hxK, rfl⟩).trans (le_max_left M 0)
    have hneg : fderiv ℝ F (e x) = -(ε • fderiv ℝ G (e x)) := eq_neg_of_add_eq_zero_left h1
    have hnorm : ‖fderiv ℝ F (e x)‖ = ε * ‖fderiv ℝ G (e x)‖ := by
      rw [hneg, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    rw [hnorm] at hle1
    have := hle1.trans (mul_le_mul_of_nonneg_left hle2 (le_of_lt hε))
    linarith
  have hVgerm : ∀ x ∈ V, (fun y => f y + ε * χ y) =ᶠ[nhds x] (fun y => f y + ε) := by
    intro x hx
    filter_upwards [hVopen.mem_nhds hx] with y hy
    rw [hV1 y hy, mul_one]
  have hOutgerm : ∀ x, x ∉ closure T → (fun y => f y + ε * χ y) =ᶠ[nhds x] f := by
    intro x hx
    filter_upwards [(isClosed_closure.isOpen_compl).mem_nhds hx] with y hy
    have hyT : y ∉ T := fun h => hy (subset_closure h)
    have hχy : χ y = 0 := by
      by_contra hc
      exact hyT (hχsupp (by rw [Function.mem_support]; exact hc))
    rw [hχy, mul_zero, add_zero]
  have hcritiff : ∀ x, Work.Drive.Morse.IsCritical (fun y => f y + ε * χ y) x ↔
      Work.Drive.Morse.IsCritical f x := by
    intro x
    by_cases hxV : x ∈ V
    · exact (isCritical_nondegCrit_congr_add hsm hf x ε (hVgerm x hxV)).1
    · by_cases hxT : x ∈ closure T
      · exact ⟨fun hc => absurd hc (hKnot x ⟨hxT, hxV⟩),
          fun hc => absurd (hTnd x hc hxT ▸ hpV) hxV⟩
      · exact (isCritical_nondegCrit_congr_eventuallyEq hsm hf x (hOutgerm x hxT)).1
  refine ⟨hsm, hcritiff, ?_, ?_, ?_⟩
  · intro x hx
    have hxf : Work.Drive.Morse.IsCritical f x := (hcritiff x).mp hx
    by_cases hxV : x ∈ V
    · exact ((isCritical_nondegCrit_congr_add hsm hf x ε (hVgerm x hxV)).2).mpr (hnd x hxf)
    · by_cases hxT : x ∈ closure T
      · exact absurd hx (hKnot x ⟨hxT, hxV⟩)
      · exact ((isCritical_nondegCrit_congr_eventuallyEq hsm hf x (hOutgerm x hxT)).2).mpr
          (hnd x hxf)
  · intro x hx hxp
    have hxT : x ∉ closure T := fun h => hxp (hTnd x hx h)
    have hχx : χ x = 0 := by
      by_contra hc
      exact hxT (subset_closure (hχsupp (by rw [Function.mem_support]; exact hc)))
    rw [hχx, mul_zero, add_zero]
  · show f p + ε * χ p = f p + ε
    rw [hχp, mul_one]

end Work.Drive.N2
