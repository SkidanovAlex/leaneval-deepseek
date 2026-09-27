import Mathlib
import Submission.Work.Whitney.CutPush.oblique_shear

/-!
# The local graph data over a moving plane: a smooth left inverse gives the graph presentation

`CutPush/NOTES_STATE_S57.md` §4 item 3.  The parametric inverse function theorem data of
`CutPush/slice_graph.lean` (`exists_ift_data`) provides, for a smooth family of slices
`Ψ : ℝ × ℝ^k → ℝ^N` and each parameter `s ∈ [0,1]`, open sets `U ∋ 0` and `W ∋ 0` and a *smooth left
inverse* `h` on `W` of `y ↦ pr_P (Ψ (s, y))` (a `ContDiffOn` function on `W`).

This file converts that datum into the graph presentation that the SLICE brick consumes: a *globally*
smooth `Pᗮ`-valued function `g` with

    Ψ (s, x) - g (pr_P (Ψ (s, x))) ∈ P      for `x` near `x₀`,

which is exactly the local hypothesis `hgraph` of `exists_smooth_graph_function_oblique` (with
`pi := P.subtypeL.comp P.orthogonalProjectionOnto`, whose range is `P` and whose kernel is `Pᗮ`).

The construction (as prescribed by both reviewers of the delegated statement) is

    g y = χ (pr_P y) • (Ψ (s, h (pr_P y)) - pr_P (Ψ (s, h (pr_P y)))),

with `χ` a bump function, `= 1` near the base point `pr_P (Ψ (s, x₀))` and supported inside `W`; the
values lie in `Pᗮ` for free since `z - pr_P z ∈ Pᗮ`, and near `x₀` the bump is `1` and `h` inverts
`pr_P ∘ Ψ (s, ·)`, so `g (pr_P (Ψ (s, x))) = Ψ (s,x) - pr_P (Ψ (s,x))` and the difference is
`pr_P (Ψ (s,x)) ∈ P`.

Two small reusable lemmas come first: a smooth function that is smooth on an open set containing its
topological support is globally smooth, and bumps with prescribed small support exist.
-/

namespace Work.Whitney.CutPush

open scoped Topology ContDiff

set_option linter.unusedVariables false

/-- **Gluing across the support.**  A map which is `C^∞` on an open set containing its topological
support is globally `C^∞`.  (The point outside `tsupport f` is trivial: `f` vanishes on a neighbourhood
of it.) -/
theorem contDiff_of_contDiffOn_of_tsupport_subset {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f U)
    (hts : tsupport f ⊆ U) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact hf.contDiffAt (hU.mem_nhds hx)
  · have hx' : x ∉ tsupport f := fun h => hx (hts h)
    have hmem : (tsupport f)ᶜ ∈ 𝓝 x := (isClosed_tsupport f).isOpen_compl.mem_nhds hx'
    have hev : f =ᶠ[𝓝 x] 0 := Filter.mem_of_superset hmem fun y hy => by
      have hy' : y ∉ Function.support f := fun h => hy (subset_tsupport f h)
      simpa [Function.mem_support] using hy'
    exact (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq hev

/-- **Bumps with prescribed small support.**  Every point of an open set `W` has a smooth `[0,1]`-valued
bump which is `1` on a ball around it and whose topological support is inside `W`. -/
theorem exists_contDiffBump_near {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [HasContDiffBump E] {W : Set E} (hW : IsOpen W) {c : E} (hc : c ∈ W) :
    ∃ (χ : E → ℝ) (r : ℝ), 0 < r ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧
      (∀ x, dist x c ≤ r → χ x = 1) ∧ (∀ x, 0 ≤ χ x) ∧ tsupport χ ⊆ W := by
  obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hc)
  let f : ContDiffBump c := ⟨ε / 4, ε / 2, by linarith, by linarith⟩
  have hrin : f.rIn = ε / 4 := rfl
  have hrout : f.rOut = ε / 2 := rfl
  refine ⟨f, ε / 4, by linarith, f.contDiff, ?_, fun x => f.nonneg, ?_⟩
  · intro x hx
    refine f.one_of_mem_closedBall ?_
    rw [Metric.mem_closedBall, hrin]
    exact hx
  · rw [f.tsupport_eq, hrout]
    intro x hx
    refine hεW ?_
    rw [Metric.mem_ball]
    rw [Metric.mem_closedBall] at hx
    linarith

/-- **The local graph presentation from a smooth left inverse.**  This is the step that converts the
parametric IFT datum (`exists_ift_data`) into the graph hypothesis consumed by
`exists_smooth_graph_function_oblique`.  Both reviewers of the delegated statement confirmed it and
prescribed the construction carried out here. -/
theorem exists_local_graph_data_of_leftInverse {N k : ℕ}
    (P : Submodule ℝ (EuclideanSpace ℝ (Fin N)))
    (Ψ : ℝ × EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin N))
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin k) => Ψ p))
    (s : ℝ) (x₀ : EuclideanSpace ℝ (Fin k))
    (U : Set (EuclideanSpace ℝ (Fin k))) (hU : IsOpen U) (hx₀U : x₀ ∈ U)
    (W : Set ↥P) (hW : IsOpen W)
    (h : ↥P → EuclideanSpace ℝ (Fin k))
    (hWmem : ∀ x ∈ U, P.orthogonalProjectionOnto (Ψ (s, x)) ∈ W)
    (hleft : ∀ x ∈ U, h (P.orthogonalProjectionOnto (Ψ (s, x))) = x)
    (hsmooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h W) :
    ∃ (δ : ℝ) (O : Set (EuclideanSpace ℝ (Fin N)))
      (g : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)),
      0 < δ ∧ IsOpen O ∧ Ψ (s, x₀) ∈ O ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      (∀ y, g y ∈ Pᗮ) ∧
      (∀ x ∈ Metric.ball x₀ δ,
        Ψ (s, x) - g ((P.subtypeL.comp P.orthogonalProjectionOnto) (Ψ (s, x))) ∈ P) := by
  classical
  -- the base point of the slice at `x₀`, and a bump supported inside `W` and `= 1` near it
  have hu₀W : P.orthogonalProjectionOnto (Ψ (s, x₀)) ∈ W := hWmem x₀ hx₀U
  obtain ⟨χ, r, hr, hχc, hχ1, hχνn, hχsupp⟩ := exists_contDiffBump_near (E := ↥P) hW hu₀W
  -- the projected map and the vertical part
  set πP : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) :=
    P.subtypeL.comp P.orthogonalProjectionOnto with hπPdef
  have hπP_apply : ∀ v : EuclideanSpace ℝ (Fin N),
      πP v = (P.orthogonalProjectionOnto v : EuclideanSpace ℝ (Fin N)) := fun v => rfl
  set ρ : ↥P → EuclideanSpace ℝ (Fin N) :=
    fun u => Ψ (s, h u) - πP (Ψ (s, h u)) with hρdef
  set g : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) :=
    fun y => χ (P.orthogonalProjectionOnto y) • ρ (P.orthogonalProjectionOnto y) with hgdef
  -- the vertical part lands in `Pᗮ`
  have hgen : ∀ v : EuclideanSpace ℝ (Fin N), v - πP v ∈ Pᗮ := by
    intro v
    rw [← Submodule.orthogonalProjectionOnto_eq_zero_iff (K := P)]
    show P.orthogonalProjectionOnto (v - πP v) = 0
    have hπv : P.orthogonalProjectionOnto (πP v) = P.orthogonalProjectionOnto v := by
      rw [hπP_apply v]
      exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (P.orthogonalProjectionOnto v)
    rw [map_sub, hπv, sub_self]
  have hρmem : ∀ u : ↥P, ρ u ∈ Pᗮ := fun u => hgen (Ψ (s, h u))
  -- smoothness of the vertical part on `W`, and of `g` everywhere (gluing lemma)
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ↥P => (s, h u)) W :=
    (contDiffOn_const (c := s)).prodMk hsmooth
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ↥P => Ψ (s, h u)) W :=
    hΨ.comp_contDiffOn h1
  have hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ W := by
    show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : ↥P => Ψ (s, h u) - πP (Ψ (s, h u))) W
    exact h2.sub (πP.contDiff.comp_contDiffOn h2)
  have hχpr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin N) => χ (P.orthogonalProjectionOnto y)) :=
    hχc.comp (P.orthogonalProjectionOnto : EuclideanSpace ℝ (Fin N) →L[ℝ] ↥P).contDiff
  have hρpr : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin N) => ρ (P.orthogonalProjectionOnto y))
      (P.orthogonalProjectionOnto ⁻¹' W) :=
    hρ.comp (P.orthogonalProjectionOnto : EuclideanSpace ℝ (Fin N) →L[ℝ] ↥P).contDiff.contDiffOn
      (fun y hy => hy)
  have hgOn : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g (P.orthogonalProjectionOnto ⁻¹' W) := by
    show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin N) =>
        χ (P.orthogonalProjectionOnto y) • ρ (P.orthogonalProjectionOnto y)) _
    exact hχpr.contDiffOn.smul hρpr
  have hgsupp : tsupport g ⊆ P.orthogonalProjectionOnto ⁻¹' W := by
    have h1 : tsupport g ⊆ tsupport
        (fun y : EuclideanSpace ℝ (Fin N) => χ (P.orthogonalProjectionOnto y)) := by
      refine closure_mono ?_
      intro y hy
      have hy' : χ (P.orthogonalProjectionOnto y) ≠ 0 := by
        intro h0
        exact hy (by simp [hgdef, h0])
      simpa [Function.mem_support] using hy'
    refine h1.trans ?_
    intro y hy
    have himg := image_closure_subset_closure_image
      (P.orthogonalProjectionOnto : EuclideanSpace ℝ (Fin N) →L[ℝ] ↥P).continuous
      (s := Function.support (fun y : EuclideanSpace ℝ (Fin N) => χ (P.orthogonalProjectionOnto y)))
    have hy2 : P.orthogonalProjectionOnto y ∈ closure
        ((P.orthogonalProjectionOnto : EuclideanSpace ℝ (Fin N) →L[ℝ] ↥P) ''
          Function.support (fun y : EuclideanSpace ℝ (Fin N) => χ (P.orthogonalProjectionOnto y))) :=
      himg ⟨y, by simpa [tsupport] using hy, rfl⟩
    refine hχsupp (closure_mono ?_ hy2)
    rintro z ⟨w, hw, rfl⟩
    simpa [Function.mem_support] using hw
  have hgsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g :=
    contDiff_of_contDiffOn_of_tsupport_subset
      (hW.preimage (P.orthogonalProjectionOnto : EuclideanSpace ℝ (Fin N) →L[ℝ] ↥P).continuous)
      hgOn hgsupp
  -- a δ on which the bump is `1` and everything stays inside `U`
  have hφcont : ContinuousAt
      (fun x : EuclideanSpace ℝ (Fin k) => P.orthogonalProjectionOnto (Ψ (s, x))) x₀ :=
    ((P.orthogonalProjectionOnto : EuclideanSpace ℝ (Fin N) →L[ℝ] ↥P).continuous.comp
      (hΨ.continuous.comp (continuous_const.prodMk continuous_id))).continuousAt
  have hev : ∀ᶠ x in 𝓝 x₀,
      dist (P.orthogonalProjectionOnto (Ψ (s, x)))
        (P.orthogonalProjectionOnto (Ψ (s, x₀))) ≤ r :=
    hφcont.tendsto.eventually (Metric.closedBall_mem_nhds _ hr)
  obtain ⟨δ₁, hδ₁, hδ₁sub⟩ := Metric.mem_nhds_iff.mp hev
  obtain ⟨δ₂, hδ₂, hδ₂sub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx₀U)
  refine ⟨min δ₁ δ₂, Set.univ, g, lt_min hδ₁ hδ₂, isOpen_univ, Set.mem_univ _, hgsm,
    fun y => Submodule.smul_mem _ _ (hρmem _), ?_⟩
  intro x hx
  have hxU : x ∈ U := hδ₂sub (Metric.ball_subset_ball (min_le_right _ _) hx)
  have hxd : dist (P.orthogonalProjectionOnto (Ψ (s, x)))
      (P.orthogonalProjectionOnto (Ψ (s, x₀))) ≤ r :=
    hδ₁sub (Metric.ball_subset_ball (min_le_left _ _) hx)
  have hχval : χ (P.orthogonalProjectionOnto (Ψ (s, x))) = 1 := hχ1 _ hxd
  have hh : h (P.orthogonalProjectionOnto (Ψ (s, x))) = x := hleft x hxU
  have hval : g (πP (Ψ (s, x))) = Ψ (s, x) - πP (Ψ (s, x)) := by
    show χ (P.orthogonalProjectionOnto (πP (Ψ (s, x))))
        • ρ (P.orthogonalProjectionOnto (πP (Ψ (s, x)))) = Ψ (s, x) - πP (Ψ (s, x))
    rw [hπP_apply (Ψ (s, x)),
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (P.orthogonalProjectionOnto (Ψ (s, x))),
      hχval]
    show (1 : ℝ) • (Ψ (s, h (P.orthogonalProjectionOnto (Ψ (s, x))))
        - πP (Ψ (s, h (P.orthogonalProjectionOnto (Ψ (s, x)))))) = Ψ (s, x) - πP (Ψ (s, x))
    rw [hh, one_smul]
  have hfinal : Ψ (s, x) - g (πP (Ψ (s, x))) = πP (Ψ (s, x)) := by
    rw [hval]
    abel
  rw [hfinal]
  simpa [hπP_apply] using (P.orthogonalProjectionOnto (Ψ (s, x))).2

end Work.Whitney.CutPush
