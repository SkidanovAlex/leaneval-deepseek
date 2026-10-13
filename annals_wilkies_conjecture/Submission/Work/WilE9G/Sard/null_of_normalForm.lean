import Mathlib
import Submission.Work.WilE9G.Sard.Basic
import Submission.Work.WilE2.RegVals.Basic
import Submission.Work.WilE2.RegVals.reg_aux
import Submission.Work.WilE2.RegVals.isClosed_setOf_not_surjective

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory
open scoped Topology

namespace Work.WilE9G.Sard

/-! ## Auxiliary definitions and lemmas -/

/-- Forgetting the `j`-th coordinate, as a continuous linear map. -/
def dropJ {n : ℕ} (j : Fin (n+1)) : (Fin (n+1) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun l => ContinuousLinearMap.proj (j.succAbove l))

theorem dropJ_apply {n : ℕ} (j : Fin (n+1)) (z : Fin (n+1) → ℝ) :
    dropJ j z = fun l => z (j.succAbove l) := by
  funext l
  rw [dropJ, ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply]

/-- Reassemble a vector from its `j`-th coordinate and the remaining coordinates. -/
theorem insertNth_dropJ {n : ℕ} (j : Fin (n+1)) (z : Fin (n+1) → ℝ) :
    Fin.insertNth (α := fun _ => ℝ) j (z j) (dropJ j z) = z := by
  rw [dropJ_apply]
  exact Work.WilE2.RegVals.insertNth_self j z

/-- `insCLM n i` is surjective. -/
theorem insCLM_surjective_aux {n : ℕ} (i : Fin (n+1)) : Function.Surjective (insCLM n i) := by
  intro y
  exact ⟨(y i, del i y), by rw [insCLM_apply, ins_del]⟩

/-- The map `(w,t) ↦ insertNth i t w` is analytic. -/
theorem analyticAt_insI {k : ℕ} (i : Fin (k+1)) (q : (Fin k → ℝ) × ℝ) :
    AnalyticAt ℝ (fun q : (Fin k → ℝ) × ℝ =>
      Fin.insertNth (α := fun _ => ℝ) i q.2 q.1) q := by
  apply AnalyticAt.pi
  intro m
  by_cases hm : m = i
  · have h : (fun q : (Fin k → ℝ) × ℝ =>
        Fin.insertNth (α := fun _ => ℝ) i q.2 q.1 m) = fun q => q.2 := by
      funext q; rw [hm, Fin.insertNth_apply_same]
    rw [h]
    exact ContinuousLinearMap.analyticAt (ContinuousLinearMap.snd ℝ (Fin k → ℝ) ℝ) q
  · obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq hm
    have h : (fun q : (Fin k → ℝ) × ℝ =>
        Fin.insertNth (α := fun _ => ℝ) i q.2 q.1 m) = fun q => q.1 l := by
      funext q; rw [← hl, Fin.insertNth_apply_succAbove]
    rw [h]
    exact ContinuousLinearMap.analyticAt
      ((ContinuousLinearMap.proj l).comp (ContinuousLinearMap.fst ℝ (Fin k → ℝ) ℝ)) q

/-- The map `w ↦ insertNth i c w` is analytic. -/
theorem analyticAt_insIc {k : ℕ} (i : Fin (k+1)) (c : ℝ) (w : Fin k → ℝ) :
    AnalyticAt ℝ (fun w' : Fin k → ℝ => Fin.insertNth (α := fun _ => ℝ) i c w') w := by
  apply AnalyticAt.pi
  intro m
  by_cases hm : m = i
  · have h : (fun w' : Fin k → ℝ => Fin.insertNth (α := fun _ => ℝ) i c w' m) = fun _ => c := by
      funext w'; rw [hm, Fin.insertNth_apply_same]
    rw [h]
    exact analyticAt_const
  · obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq hm
    have h : (fun w' : Fin k → ℝ => Fin.insertNth (α := fun _ => ℝ) i c w' m) = fun w' => w' l := by
      funext w'; rw [← hl, Fin.insertNth_apply_succAbove]
    rw [h]
    exact ContinuousLinearMap.analyticAt
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) l) w

/-- The `w ↦ insertNth i c w` is continuous. -/
theorem continuous_insIc {k : ℕ} (i : Fin (k+1)) (c : ℝ) :
    Continuous (fun w : Fin k → ℝ => Fin.insertNth (α := fun _ => ℝ) i c w) :=
  continuous_iff_continuousAt.mpr fun w => (analyticAt_insIc i c w).continuousAt

/-- The joint slice map is analytic wherever `g` is. -/
theorem analyticAt_sliceMap {k n : ℕ} (i : Fin (k+1)) (j : Fin (n+1))
    {g : (Fin (k+1) → ℝ) → (Fin (n+1) → ℝ)} {W : Set (Fin (k+1) → ℝ)}
    {q : (Fin k → ℝ) × ℝ}
    (hW : ∀ y ∈ W, AnalyticAt ℝ g y)
    (hq : Fin.insertNth (α := fun _ => ℝ) i q.2 q.1 ∈ W) :
    AnalyticAt ℝ (fun q : (Fin k → ℝ) × ℝ =>
      dropJ j (g (Fin.insertNth (α := fun _ => ℝ) i q.2 q.1))) q := by
  have hinsI := analyticAt_insI i q
  have hg : AnalyticAt ℝ g (Fin.insertNth (α := fun _ => ℝ) i q.2 q.1) := hW _ hq
  have h1 : AnalyticAt ℝ (fun q : (Fin k → ℝ) × ℝ =>
      g (Fin.insertNth (α := fun _ => ℝ) i q.2 q.1)) q := AnalyticAt.comp hg hinsI
  exact AnalyticAt.comp
    (ContinuousLinearMap.analyticAt (dropJ j) (g (Fin.insertNth (α := fun _ => ℝ) i q.2 q.1))) h1

/-- The slice map `w ↦ dropJ j (g (insertNth i c w))` is analytic wherever `g` is. -/
theorem analyticAt_slice {k n : ℕ} (i : Fin (k+1)) (j : Fin (n+1))
    {g : (Fin (k+1) → ℝ) → (Fin (n+1) → ℝ)} {W : Set (Fin (k+1) → ℝ)} {c : ℝ}
    (hW : ∀ y ∈ W, AnalyticAt ℝ g y) {w : Fin k → ℝ}
    (hw : Fin.insertNth (α := fun _ => ℝ) i c w ∈ W) :
    AnalyticAt ℝ (fun w' : Fin k → ℝ =>
      dropJ j (g (Fin.insertNth (α := fun _ => ℝ) i c w'))) w := by
  have hinsIc := analyticAt_insIc i c w
  have hg : AnalyticAt ℝ g (Fin.insertNth (α := fun _ => ℝ) i c w) := hW _ hw
  have h1 : AnalyticAt ℝ (fun w' : Fin k → ℝ =>
      g (Fin.insertNth (α := fun _ => ℝ) i c w')) w := AnalyticAt.comp hg hinsIc
  exact AnalyticAt.comp
    (ContinuousLinearMap.analyticAt (dropJ j) (g (Fin.insertNth (α := fun _ => ℝ) i c w))) h1

/-- The closed ball intersected with the critical set is compact, provided the derivative is
continuous at every point of the ball. -/
theorem aux_compact_critSet {n m : ℕ} {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {c : Fin n → ℝ} {ρ : ℝ}
    (hc : ∀ x ∈ Metric.closedBall c ρ, ContinuousAt (fderiv ℝ f) x) :
    IsCompact (Metric.closedBall c ρ ∩ {z | ¬ Function.Surjective (fderiv ℝ f z)}) := by
  refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨?_, ?_⟩
  · rw [isClosed_iff_nhds]
    intro x hx
    have hx1 : x ∈ Metric.closedBall c ρ := by
      by_contra h
      have hcompl : (Metric.closedBall c ρ)ᶜ ∈ nhds x :=
        Metric.isClosed_closedBall.isOpen_compl.mem_nhds h
      obtain ⟨y, hy, hyS⟩ := hx _ hcompl
      exact hy hyS.1
    refine ⟨hx1, ?_⟩
    by_contra hnot
    have hsurj : Function.Surjective (fderiv ℝ f x) := not_not.mp hnot
    have hopen : (fderiv ℝ f) ⁻¹'
        {T : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ) | Function.Surjective T} ∈ nhds x :=
      (hc x hx1).preimage_mem_nhds
        (Work.WilE2.RegVals.isOpen_setOf_surjective.mem_nhds hsurj)
    obtain ⟨y, hy, hyS⟩ := hx _ hopen
    exact hyS.2 hy
  · exact Metric.isBounded_closedBall.subset Set.inter_subset_left

/-- **Slice criticality.**  If `g` is locally in the normal form `g (ins i t w) = ins j t (H (w,t))`
and is differentiable at `ins i t w`, then surjectivity of the slice derivative
`fderiv (fun w' => H (w',t)) w` forces surjectivity of `fderiv g (ins i t w)`. -/
theorem aux_slice_criticality {k n : ℕ} (i : Fin (k+1)) (j : Fin (n+1))
    {g : (Fin (k+1) → ℝ) → (Fin (n+1) → ℝ)} {H : (Fin k → ℝ) × ℝ → (Fin n → ℝ)}
    {w : Fin k → ℝ} {t : ℝ}
    (hg : DifferentiableAt ℝ g (Fin.insertNth (α := fun _ => ℝ) i t w))
    (hH : DifferentiableAt ℝ H (w, t))
    (hnorm : ∀ᶠ q in nhds (w, t),
      g (Fin.insertNth (α := fun _ => ℝ) i q.2 q.1) = Fin.insertNth (α := fun _ => ℝ) j q.2 (H q))
    (hslice : Function.Surjective (fderiv ℝ (fun w' => H (w', t)) w)) :
    Function.Surjective (fderiv ℝ g (Fin.insertNth (α := fun _ => ℝ) i t w)) := by
  classical
  -- the slice derivative is `dH ∘ inl`
  have hslice' : Function.Surjective
      ((fderiv ℝ H (w, t)).comp (ContinuousLinearMap.inl ℝ (Fin k → ℝ) ℝ)) := by
    rw [← Work.WilE2.RegVals.fderiv_slice H w t hH]
    exact hslice
  have hHsurj : Function.Surjective (fderiv ℝ H (w, t)) :=
    Function.Surjective.of_comp hslice'
  -- `dH × id` is onto
  have hprod : Function.Surjective
      ((fderiv ℝ H (w, t)).prod (ContinuousLinearMap.snd ℝ (Fin k → ℝ) ℝ)) :=
    (Work.WilE2.RegVals.surjective_prod_snd_iff (fderiv ℝ H (w, t))).mpr hslice'
  -- the swapped version, which is the derivative of `q ↦ (q.2, H q)`
  have hprod' : Function.Surjective
      ((ContinuousLinearMap.snd ℝ (Fin k → ℝ) ℝ).prod (fderiv ℝ H (w, t))) := by
    rintro ⟨s, y⟩
    obtain ⟨p, hp⟩ := hprod (y, s)
    exact ⟨p, by
      rw [ContinuousLinearMap.prod_apply]
      exact Prod.ext (congrArg Prod.snd hp) (congrArg Prod.fst hp)⟩
  -- the derivative of the reassembled map is onto
  have hΨsurj : Function.Surjective (fderiv ℝ
      (fun q : (Fin k → ℝ) × ℝ => insCLM n j (q.2, H q)) (w, t)) := by
    have hA : HasFDerivAt (fun q : (Fin k → ℝ) × ℝ => (q.2, H q))
        ((ContinuousLinearMap.snd ℝ (Fin k → ℝ) ℝ).prod (fderiv ℝ H (w, t))) (w, t) :=
      (ContinuousLinearMap.snd ℝ (Fin k → ℝ) ℝ).hasFDerivAt.prodMk hH.hasFDerivAt
    have h2 := ((insCLM n j).hasFDerivAt.comp (w, t) hA).fderiv
    have hgoal : (fun q : (Fin k → ℝ) × ℝ => insCLM n j (q.2, H q))
        = (⇑(insCLM n j)) ∘ (fun q : (Fin k → ℝ) × ℝ => (q.2, H q)) := rfl
    rw [hgoal, h2]
    exact (insCLM_surjective_aux j).comp hprod'
  -- transfer along the normal form to `g`
  have heq : (fun q : (Fin k → ℝ) × ℝ => g (Fin.insertNth (α := fun _ => ℝ) i q.2 q.1))
      =ᶠ[nhds (w, t)] (fun q : (Fin k → ℝ) × ℝ => insCLM n j (q.2, H q)) := by
    filter_upwards [hnorm] with q hq
    rw [hq, insCLM_apply]
  have hgc : fderiv ℝ (fun q : (Fin k → ℝ) × ℝ =>
        g (Fin.insertNth (α := fun _ => ℝ) i q.2 q.1)) (w, t)
      = fderiv ℝ (fun q : (Fin k → ℝ) × ℝ => insCLM n j (q.2, H q)) (w, t) :=
    heq.fderiv_eq
  have hchain : fderiv ℝ (fun q : (Fin k → ℝ) × ℝ =>
        g (Fin.insertNth (α := fun _ => ℝ) i q.2 q.1)) (w, t)
      = (fderiv ℝ g (Fin.insertNth (α := fun _ => ℝ) i t w)).comp
          (fderiv ℝ (fun q : (Fin k → ℝ) × ℝ =>
            Fin.insertNth (α := fun _ => ℝ) i q.2 q.1) (w, t)) := by
    have hs : DifferentiableAt ℝ (fun q : (Fin k → ℝ) × ℝ =>
        Fin.insertNth (α := fun _ => ℝ) i q.2 q.1) (w, t) := (analyticAt_insI i (w, t)).differentiableAt
    have h1 : HasFDerivAt (fun q : (Fin k → ℝ) × ℝ =>
          g (Fin.insertNth (α := fun _ => ℝ) i q.2 q.1))
        ((fderiv ℝ g (Fin.insertNth (α := fun _ => ℝ) i t w)).comp
          (fderiv ℝ (fun q : (Fin k → ℝ) × ℝ =>
            Fin.insertNth (α := fun _ => ℝ) i q.2 q.1) (w, t))) (w, t) :=
      hg.hasFDerivAt.comp (w, t) hs.hasFDerivAt
    exact h1.fderiv
  have hmain : Function.Surjective
      ((fderiv ℝ g (Fin.insertNth (α := fun _ => ℝ) i t w)).comp
        (fderiv ℝ (fun q : (Fin k → ℝ) × ℝ =>
          Fin.insertNth (α := fun _ => ℝ) i q.2 q.1) (w, t))) := by
    rw [← hchain, hgc]
    exact hΨsurj
  exact Function.Surjective.of_comp hmain

/-- **The regular-case slice reduction of Morse–Sard.**  If `g : ℝ^{k+1} → ℝᵐ` is analytic at `y₀`
and one component of `g` is literally one of the coordinates, `g y j = y i` near `y₀`, then the
critical values of `g` over a neighbourhood of `y₀` are null, given Morse–Sard in dimension `k`.
The relevant slices are `w ↦ drop j (g (insert i t w)) : ℝ^k → ℝ^{m-1}`. -/
theorem null_of_normalForm {k m : ℕ} {g : (Fin (k+1) → ℝ) → (Fin m → ℝ)} {y₀ : Fin (k+1) → ℝ}
    (hg : AnalyticAt ℝ g y₀) (i : Fin (k+1)) (j : Fin m)
    (hnorm : ∀ᶠ y in nhds y₀, g y j = y i)
    (IH : SardNull k) :
    ∃ W : Set (Fin (k+1) → ℝ), IsOpen W ∧ y₀ ∈ W ∧
      MeasureTheory.volume (g '' (critSet g ∩ W)) = 0 := by
  rcases m with _ | n
  · exact Fin.elim0 j
  have hWf_mem : ∀ᶠ y in nhds y₀, AnalyticAt ℝ g y ∧ g y j = y i :=
    hg.eventually_analyticAt.and hnorm
  obtain ⟨R, hRpos, hR⟩ := Metric.mem_nhds_iff.mp hWf_mem
  set ρ : ℝ := R / 2 with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; linarith
  have hcb : Metric.closedBall y₀ ρ ⊆ Metric.ball y₀ R := by
    intro y hy
    rw [Metric.mem_closedBall] at hy
    rw [Metric.mem_ball]
    rw [dist_eq_norm] at hy ⊢
    rw [hρdef] at hy
    linarith
  have hWf : ∀ y ∈ Metric.closedBall y₀ ρ, AnalyticAt ℝ g y ∧ g y j = y i :=
    fun y hy => hR (hcb hy)
  have hdf : ∀ y ∈ Metric.closedBall y₀ ρ, DifferentiableAt ℝ g y :=
    fun y hy => (hWf y hy).1.differentiableAt
  -- the joint slice map
  let H : (Fin k → ℝ) × ℝ → (Fin n → ℝ) :=
    fun q => dropJ j (g (Fin.insertNth (α := fun _ => ℝ) i q.2 q.1))
  -- the compact piece of the critical set
  set Scrit : Set (Fin (k+1) → ℝ) := Metric.closedBall y₀ ρ ∩ critSet g with hScritdef
  -- the map sending a critical point to its critical value in split coordinates
  let Λ : (Fin (k+1) → ℝ) → ℝ × (Fin n → ℝ) := fun z => (z i, dropJ j (g z))
  set T : Set (ℝ × (Fin n → ℝ)) := Λ '' Scrit with hTdef
  have hScritcomp : IsCompact Scrit := by
    rw [hScritdef]
    exact aux_compact_critSet (f := g) (c := y₀) (ρ := ρ) fun x hx =>
      (AnalyticAt.contDiffAt (hWf x hx).1 : ContDiffAt ℝ 1 g x).continuousAt_fderiv one_ne_zero
  have hΛcont : ContinuousOn Λ Scrit := by
    intro z hz
    obtain ⟨hz1, _⟩ := hz
    have hgc : ContinuousAt g z := (hWf z hz1).1.continuousAt
    have h1 : ContinuousWithinAt (fun z : Fin (k+1) → ℝ => z i) Scrit z :=
      (continuous_apply i).continuousAt.continuousWithinAt
    have h2 : ContinuousWithinAt (fun z : Fin (k+1) → ℝ => dropJ j (g z)) Scrit z :=
      (ContinuousAt.comp ((dropJ j).continuous.continuousAt) hgc).continuousWithinAt
    exact h1.prodMk h2
  have hTcomp : IsCompact T := by
    rw [hTdef]
    exact hScritcomp.image_of_continuousOn hΛcont
  have hTmeas : MeasurableSet T := hTcomp.measurableSet
  -- the slices of `T` are null
  have hslice : ∀ c : ℝ, volume {v : Fin n → ℝ | (c, v) ∈ T} = 0 := by
    intro c
    set Uc : Set (Fin k → ℝ) :=
      {w | Fin.insertNth (α := fun _ => ℝ) i c w ∈ Metric.ball y₀ R} with hUcdef
    have hUcopen : IsOpen Uc :=
      Metric.isOpen_ball.preimage (continuous_insIc i c)
    have hHan : AnalyticOn ℝ (fun w : Fin k → ℝ =>
        dropJ j (g (Fin.insertNth (α := fun _ => ℝ) i c w))) Uc := by
      intro w hw
      exact (analyticAt_slice i j (fun y hy => (hR hy).1) hw).analyticWithinAt
    have hsub : {v : Fin n → ℝ | (c, v) ∈ T} ⊆
        (fun w : Fin k → ℝ => dropJ j (g (Fin.insertNth (α := fun _ => ℝ) i c w))) ''
          (critSet (fun w : Fin k → ℝ => dropJ j (g (Fin.insertNth (α := fun _ => ℝ) i c w))) ∩ Uc) := by
      intro v hv
      rw [hTdef] at hv
      obtain ⟨z, hzScrit, hzLam⟩ := hv
      obtain ⟨hz1, hz2⟩ := hzScrit
      have hzi : z i = c := congrArg Prod.fst hzLam
      have hz2' : dropJ j (g z) = v := congrArg Prod.snd hzLam
      have hzd : Fin.insertNth (α := fun _ => ℝ) i c (del i z) = z := by
        rw [← hzi]; exact ins_del i z
      have hcrit : ¬ Function.Surjective (fderiv ℝ g z) := hz2
      have hdd : ¬ Function.Surjective
          (fderiv ℝ (fun w' : Fin k → ℝ => H (w', c)) (del i z)) := by
        intro hsurj
        refine hcrit (?_)
        have hkey := aux_slice_criticality i j
          (g := g) (H := H) (w := del i z) (t := c)
          (by rw [hzd]; exact hdf z hz1)
          (analyticAt_sliceMap i j (fun y hy => (hR hy).1) (show Fin.insertNth (α := fun _ => ℝ) i c (del i z) ∈ Metric.ball y₀ R by
            rw [hzd]; exact hcb hz1)).differentiableAt
          (by
            -- the normal-form relation holds on a neighbourhood of `(del i z, c)`
            have hopen : IsOpen {q : (Fin k → ℝ) × ℝ |
                Fin.insertNth (α := fun _ => ℝ) i q.2 q.1 ∈ Metric.ball y₀ R} :=
              Metric.isOpen_ball.preimage (continuous_iff_continuousAt.mpr fun q =>
                (analyticAt_insI i q).continuousAt)
            have hmem : (del i z, c) ∈ {q : (Fin k → ℝ) × ℝ |
                Fin.insertNth (α := fun _ => ℝ) i q.2 q.1 ∈ Metric.ball y₀ R} := by
              show Fin.insertNth (α := fun _ => ℝ) i c (del i z) ∈ Metric.ball y₀ R
              rw [hzd]; exact hcb hz1
            filter_upwards [hopen.mem_nhds hmem] with q hq
            have hqj : g (Fin.insertNth (α := fun _ => ℝ) i q.2 q.1) j = q.2 :=
              (hR hq).2.trans (Fin.insertNth_apply_same (α := fun _ => ℝ) i q.2 q.1)
            show g (Fin.insertNth (α := fun _ => ℝ) i q.2 q.1) =
              Fin.insertNth (α := fun _ => ℝ) j q.2 (dropJ j (g (Fin.insertNth (α := fun _ => ℝ) i q.2 q.1)))
            simpa only [hqj] using
              (insertNth_dropJ j (g (Fin.insertNth (α := fun _ => ℝ) i q.2 q.1))).symm)
          hsurj
        rwa [hzd] at hkey
      refine ⟨del i z, ⟨?_, ?_⟩, ?_⟩
      · -- `del i z` is a critical point of the slice
        show del i z ∈ critSet (fun w : Fin k → ℝ => dropJ j (g (Fin.insertNth (α := fun _ => ℝ) i c w)))
        show ¬ Function.Surjective (fderiv ℝ (fun w' : Fin k → ℝ =>
          dropJ j (g (Fin.insertNth (α := fun _ => ℝ) i c w'))) (del i z))
        simpa only [H] using hdd
      · -- `del i z ∈ Uc`
        show Fin.insertNth (α := fun _ => ℝ) i c (del i z) ∈ Metric.ball y₀ R
        rw [hzd]; exact hcb hz1
      · -- the value agrees
        show dropJ j (g (Fin.insertNth (α := fun _ => ℝ) i c (del i z))) = v
        rw [hzd]; exact hz2'
    refine le_antisymm ?_ bot_le
    calc volume {v : Fin n → ℝ | (c, v) ∈ T}
        ≤ volume ((fun w : Fin k → ℝ => dropJ j (g (Fin.insertNth (α := fun _ => ℝ) i c w))) ''
            (critSet (fun w : Fin k → ℝ => dropJ j (g (Fin.insertNth (α := fun _ => ℝ) i c w))) ∩ Uc)) :=
          measure_mono hsub
      _ = 0 := IH n (fun w : Fin k → ℝ => dropJ j (g (Fin.insertNth (α := fun _ => ℝ) i c w))) Uc
          hUcopen hHan
  have hTnull : volume T = 0 :=
    Work.WilE2.RegVals.volume_eq_zero_of_slices_null_real hTmeas hslice
  have hnullT : volume
      ((⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) j).symm) '' T) = 0 := by
    rw [Work.WilE2.image_null_iff_of_measurePreserving
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) j).symm)
      (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) j).symm T]
    exact hTnull
  refine ⟨Metric.ball y₀ ρ, Metric.isOpen_ball, Metric.mem_ball_self hρpos, ?_⟩
  refine measure_mono_null ?_ hnullT
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨hzcrit, hzball⟩ := hz
  have hzcb : z ∈ Metric.closedBall y₀ ρ := Metric.ball_subset_closedBall hzball
  have hzScrit : z ∈ Scrit := by rw [hScritdef]; exact ⟨hzcb, hzcrit⟩
  have hzWf := hWf z hzcb
  refine ⟨Λ z, ?_, ?_⟩
  · rw [hTdef]; exact ⟨z, hzScrit, rfl⟩
  · rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
    show Fin.insertNth (α := fun _ => ℝ) j (Λ z).1 (Λ z).2 = g z
    show Fin.insertNth (α := fun _ => ℝ) j (z i) (dropJ j (g z)) = g z
    rw [← hzWf.2]
    exact insertNth_dropJ j (g z)

end Work.WilE9G.Sard
