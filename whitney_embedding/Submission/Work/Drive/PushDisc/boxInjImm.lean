import Mathlib
import Submission.Work.Drive.Whitney.modelChart
import Submission.Work.Routing.injOn_nhds_of_compact_of_locallyInjOn

/-!
# Uniform injectivity/immersion on a box over a compact base

`Work.Drive.PushDisc.boxInjImm`: a smooth self-map `θ` of the model space
`Mdl k = ℝ × ℝ × ℝ^k × ℝ^k` which is injective on the "base plane" over a compact `P ⊆ ℝ²`
and whose derivative is injective there is injective, with injective derivative, on the whole
box `{(x,y,v,w) : (x,y) ∈ P, ‖v‖ ≤ δ, ‖w‖ ≤ δ}` for some `δ > 0`.

The proof is point-set:

* the core `S = {(p.1, p.2, 0, 0) : p ∈ P}` is compact, `θ` is injective on it and `fderiv ℝ θ`
  is injective at each of its points (the two hypotheses);
* `fderiv ℝ θ` is continuous and the points where a continuous linear endomorphism is injective
  form an open set (the complement of `{det = 0}`), so the set of such points is an open
  neighbourhood of the compact `S`;
* the same for the set of points near which `θ` is injective, obtained from
  `Work.Routing.injOn_nhds_of_compact_of_locallyInjOn` and the inverse function theorem
  (`local_injOn_of_injective_fderiv_mdl`);
* two thickenings of `S` (which contain the boxes for small `δ`) sit inside these two open sets.
-/

namespace Work.Drive.PushDisc

open Set Metric

/-- A continuous linear endomorphism of the model space is injective exactly when its determinant
does not vanish. -/
private theorem injective_iff_det_ne_zero {k : ℕ}
    (f : Work.Drive.Whitney.Mdl k →L[ℝ] Work.Drive.Whitney.Mdl k) :
    Function.Injective f ↔ f.det ≠ 0 := by
  have h : f.det = 0 ↔ ¬ Function.Injective ⇑f := by
    rw [ContinuousLinearMap.det, LinearMap.det_eq_zero_iff_ker_ne_bot]
    simp only [ne_eq, LinearMap.ker_eq_bot]
    exact Iff.rfl
  simp only [ne_eq, h, not_not]

/-- **Local injectivity from an injective derivative on the model space.**  If `ψ : Mdl k → Mdl k`
is `C^∞` and `fderiv ℝ ψ u₀` is injective, then `ψ` is injective on some open neighbourhood
of `u₀` (the inverse function theorem, for the model space). -/
private theorem local_injOn_of_injective_fderiv_mdl {k : ℕ}
    {ψ : Work.Drive.Whitney.Mdl k → Work.Drive.Whitney.Mdl k} {u₀ : Work.Drive.Whitney.Mdl k}
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hinj : Function.Injective (fderiv ℝ ψ u₀)) :
    ∃ W : Set (Work.Drive.Whitney.Mdl k), IsOpen W ∧ u₀ ∈ W ∧ Set.InjOn ψ W := by
  classical
  set A : Work.Drive.Whitney.Mdl k →L[ℝ] Work.Drive.Whitney.Mdl k := fderiv ℝ ψ u₀ with hA
  have hker : LinearMap.ker A.toLinearMap = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  obtain ⟨g, hg⟩ := A.toLinearMap.exists_leftInverse_of_injective hker
  let G : Work.Drive.Whitney.Mdl k →L[ℝ] Work.Drive.Whitney.Mdl k :=
    LinearMap.toContinuousLinearMap g
  have hGA : G ∘L A = ContinuousLinearMap.id ℝ (Work.Drive.Whitney.Mdl k) := by
    apply ContinuousLinearMap.ext
    intro v
    have hv := LinearMap.congr_fun hg v
    simpa [G] using hv
  have hnz : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hψat : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ u₀ := hψ.contDiffAt
  have hΨcont : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => G (ψ u)) u₀ :=
    G.contDiff.contDiffAt.comp u₀ hψat
  have hΨderiv : HasFDerivAt (fun u => G (ψ u)) (G ∘L A) u₀ :=
    HasFDerivAt.comp u₀ (G.hasFDerivAt (x := ψ u₀)) (hψat.differentiableAt hnz |>.hasFDerivAt)
  have hΨderiv' : HasFDerivAt (fun u => G (ψ u))
      ((ContinuousLinearEquiv.refl ℝ (Work.Drive.Whitney.Mdl k) :
        Work.Drive.Whitney.Mdl k →L[ℝ] Work.Drive.Whitney.Mdl k)) u₀ := by
    have h := hΨderiv.congr_fderiv hGA
    simpa [ContinuousLinearEquiv.coe_refl] using h
  have hS : HasStrictFDerivAt (fun u => G (ψ u))
      ((ContinuousLinearEquiv.refl ℝ (Work.Drive.Whitney.Mdl k) :
        Work.Drive.Whitney.Mdl k →L[ℝ] Work.Drive.Whitney.Mdl k)) u₀ :=
    hΨcont.hasStrictFDerivAt' hΨderiv' hnz
  obtain ⟨S, hSmem, hSinj⟩ := Filter.eventually_iff_exists_mem.mp hS.eventually_left_inverse
  obtain ⟨W, hWsub, hWopen, hu₀W⟩ := _root_.mem_nhds_iff.mp hSmem
  refine ⟨W, hWopen, hu₀W, ?_⟩
  intro a ha b hb hab
  have h1 := hSinj a (hWsub ha)
  have h2 := hSinj b (hWsub hb)
  rw [← h1, ← h2, congrArg G hab]

/-- The distance from a point of the model space to the corresponding core point is the maximum of
the two vertical norms. -/
private lemma dist_core {k : ℕ} (ξ : Work.Drive.Whitney.Mdl k) :
    dist ξ ((ξ.1, ξ.2.1, (0 : EuclideanSpace ℝ (Fin k)), 0) : Work.Drive.Whitney.Mdl k)
      = max ‖ξ.2.2.1‖ ‖ξ.2.2.2‖ := by
  rw [dist_eq_norm]
  simp [Prod.norm_def]

theorem boxInjImm {k : ℕ} (θ : Work.Drive.Whitney.Mdl k → Work.Drive.Whitney.Mdl k)
    (hθ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ)
    (P : Set (ℝ × ℝ)) (hP : IsCompact P)
    (hbase : Set.InjOn (fun p : ℝ × ℝ => θ (p.1, p.2, 0, 0)) P)
    (himm : ∀ p ∈ P, Function.Injective (fderiv ℝ θ (p.1, p.2, 0, 0))) :
    ∃ δ : ℝ, 0 < δ ∧
      Set.InjOn θ {ξ : Work.Drive.Whitney.Mdl k |
        (ξ.1, ξ.2.1) ∈ P ∧ ‖ξ.2.2.1‖ ≤ δ ∧ ‖ξ.2.2.2‖ ≤ δ} ∧
      (∀ ξ ∈ {ξ : Work.Drive.Whitney.Mdl k |
        (ξ.1, ξ.2.1) ∈ P ∧ ‖ξ.2.2.1‖ ≤ δ ∧ ‖ξ.2.2.2‖ ≤ δ},
        Function.Injective (fderiv ℝ θ ξ)) := by
  classical
  -- the core: the image of `P` in the base plane
  set zz : ℝ × ℝ → Work.Drive.Whitney.Mdl k := fun p => (p.1, p.2, 0, 0) with hzz
  have hzzcont : Continuous zz := by rw [hzz]; fun_prop
  have hScomp : IsCompact (zz '' P) := hP.image hzzcont
  -- `θ` is injective on the core
  have hInjS : Set.InjOn θ (zz '' P) := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hpq
    rw [hzz] at hpq
    rw [hzz, hbase hp hq hpq]
  -- `fderiv θ` is injective at the points of the core
  have hImmS : ∀ ξ ∈ zz '' P, Function.Injective (fderiv ℝ θ ξ) := by
    rintro _ ⟨p, hp, rfl⟩
    rw [hzz]
    exact himm p hp
  -- an open neighbourhood of the core on which `θ` is injective
  obtain ⟨O, hOopen, hSO, hInjO⟩ :=
    Work.Routing.injOn_nhds_of_compact_of_locallyInjOn hScomp
      (fun ξ hξ => local_injOn_of_injective_fderiv_mdl hθ (hImmS ξ hξ))
      (fun ξ _ => hθ.continuous.continuousAt) hInjS
  -- the (open) set of points with injective derivative
  have hVopen : IsOpen {ξ : Work.Drive.Whitney.Mdl k |
      Function.Injective (fderiv ℝ θ ξ)} := by
    have hfderiv_cont : Continuous (fun ξ : Work.Drive.Whitney.Mdl k => fderiv ℝ θ ξ) :=
      hθ.continuous_fderiv (by simp)
    have hdet_cont : Continuous (fun ξ : Work.Drive.Whitney.Mdl k => (fderiv ℝ θ ξ).det) :=
      ContinuousLinearMap.continuous_det.comp hfderiv_cont
    have heq : {ξ : Work.Drive.Whitney.Mdl k | Function.Injective (fderiv ℝ θ ξ)}
        = {ξ | (fderiv ℝ θ ξ).det ≠ 0} := by
      ext ξ
      exact injective_iff_det_ne_zero _
    rw [heq]
    exact isOpen_ne.preimage hdet_cont
  -- thickenings of the compact core inside the two open sets
  obtain ⟨ε₁, hε₁pos, hε₁sub⟩ := hScomp.exists_thickening_subset_open hOopen hSO
  obtain ⟨ε₂, hε₂pos, hε₂sub⟩ :=
    hScomp.exists_thickening_subset_open hVopen (fun ξ hξ => hImmS ξ hξ)
  have hdist : ∀ ξ : Work.Drive.Whitney.Mdl k, dist ξ (zz (ξ.1, ξ.2.1)) = max ‖ξ.2.2.1‖ ‖ξ.2.2.2‖ := by
    intro ξ
    rw [hzz, dist_core]
  refine ⟨min ε₁ ε₂ / 2, by positivity, ?_, ?_⟩
  · -- injectivity on the box
    intro ξ hξ η hη hEq
    have hmem : ∀ {ζ : Work.Drive.Whitney.Mdl k},
        (ζ.1, ζ.2.1) ∈ P → ‖ζ.2.2.1‖ ≤ min ε₁ ε₂ / 2 → ‖ζ.2.2.2‖ ≤ min ε₁ ε₂ / 2 →
        ζ ∈ thickening ε₁ (zz '' P) := by
      intro ζ hb hv hw
      rw [mem_thickening_iff]
      refine ⟨zz (ζ.1, ζ.2.1), ⟨(ζ.1, ζ.2.1), hb, rfl⟩, ?_⟩
      rw [hdist]
      exact lt_of_le_of_lt (max_le hv hw)
        (by linarith [min_le_left ε₁ ε₂, hε₁pos])
    exact hInjO (hε₁sub (hmem hξ.1 hξ.2.1 hξ.2.2))
      (hε₁sub (hmem hη.1 hη.2.1 hη.2.2)) hEq
  · -- injective derivative on the box
    intro ξ hξ
    have hmem : ξ ∈ thickening ε₂ (zz '' P) := by
      rw [mem_thickening_iff]
      refine ⟨zz (ξ.1, ξ.2.1), ⟨(ξ.1, ξ.2.1), hξ.1, rfl⟩, ?_⟩
      rw [hdist]
      exact lt_of_le_of_lt (max_le hξ.2.1 hξ.2.2)
        (by linarith [min_le_right ε₁ ε₂, hε₂pos])
    exact hε₂sub hmem

end Work.Drive.PushDisc
