import Mathlib
import Submission.Work.Drive.interior_projection_zeroSet_of_rank_except
import Submission.Work.Drive.rankZeroSetTool
import Submission.Work.Drive.interior_zeroSet_projection_empty

/-!
# Projection of a zero set with a rank hypothesis outside an exceptional set
(`NormedSpace`-only form)

This file proves `Work.Drive.interior_projection_zeroSet_of_rank_except_normed`, the
`NormedSpace`-only form of `Work.Drive.interior_projection_zeroSet_of_rank_except`
(`Submission/Work/Drive/interior_projection_zeroSet_of_rank_except.lean`).  The three
`[InnerProductSpace ℝ ·]` hypotheses are weakened to `[NormedSpace ℝ ·]`.

The existing proof uses the inner product in exactly one place, inside the local brick: the
codomain of `Ψ` is restricted to the range `R = (fderiv ℝ Ψ p).range` of the derivative by
composing with the *orthogonal* projection `R.orthogonalProjectionOnto`.  Any complement of `R`
does the job, so the brick is replaced by the algebraic projection
`Submodule.projectionOnto R q hq` (with `q` a complement of `R`, `Submodule.exists_isCompl`),
turned into a continuous linear map by `LinearMap.toContinuousLinearMap`.  The only place where
the projection is used is `Submodule.projectionOnto_apply_left hq y`, exactly as the
`[simp]` fact `Submodule.orthogonalProjectionOnto_mem_subspace_eq_self` was used before.

Everything else in the proof (`Work.Drive.exists_lipschitz_param_of_fderiv_surjective`,
`Real.dimH_univ_eq_finrank`, `Real.dimH_of_nonempty_interior`, the Lindelöf cover, the final
open-ball contradiction) is already `NormedSpace`-only and is copied unchanged.

The intermediate names are distinct from the originals
(`exists_small_nbhd_rank_gt_normed`), because the original file is imported by others.
-/

open scoped Topology

set_option linter.style.haveILetI false

namespace Work.Drive

/-- **Local parametrisation of a zero set where the derivative has large rank.**

Let `Ψ : V × W → F` be `C¹` near a zero `p` at which the derivative has rank strictly larger
than `finrank ℝ W`.  Then there are an open neighbourhood `O` of `p` and a set `U ⊆ V` of
Hausdorff dimension at most `finrank ℝ V - 1` such that the projection to `V` of the zero set
in `O` is contained in `U`.

The proof restricts the codomain of `Ψ` to the range `R = (fderiv ℝ Ψ p).range` by composing
with the (algebraic) projection `π : F →L[ℝ] R` onto `R` along a complement `q` of `R`.  The
composed map `π ∘ Ψ` is a submersion at `p` (its derivative `π ∘ DΨ p` has range `R`, by
`Submodule.projectionOnto_apply_left`), so its level set is, near `p`, a locally Lipschitz image
of the kernel of `π ∘ DΨ p` (implicit function theorem,
`exists_lipschitz_param_of_fderiv_surjective`).  That kernel has dimension
`finrank ℝ (V × W) - finrank ℝ R ≤ finrank ℝ V - 1`, and the Lipschitz projection to `V` does
not increase Hausdorff dimension. -/
theorem exists_small_nbhd_rank_gt_normed
    {V W F : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {Ψ : V × W → F} (hΨ : ContDiff ℝ 1 Ψ)
    {p : V × W} (hp : Ψ p = 0)
    (hrank : Module.finrank ℝ W < Module.finrank ℝ (fderiv ℝ Ψ p).range) :
    ∃ (O : Set (V × W)) (U : Set V), IsOpen O ∧ p ∈ O ∧
      dimH U ≤ ((Module.finrank ℝ V - 1 : ℕ) : ENNReal) ∧
      Prod.fst '' (O ∩ {q : V × W | Ψ q = 0}) ⊆ U := by
  classical
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (fderiv ℝ Ψ p).range
  set πL : F →ₗ[ℝ] (fderiv ℝ Ψ p).range :=
    Submodule.projectionOnto (fderiv ℝ Ψ p).range q hq with hπL
  set π : F →L[ℝ] (fderiv ℝ Ψ p).range := LinearMap.toContinuousLinearMap πL with hπ
  set g : V × W → (fderiv ℝ Ψ p).range := fun x => π (Ψ x) with hg
  have h1 : HasFDerivAt g (π.comp (fderiv ℝ Ψ p)) p := by
    have h2 := (ContinuousLinearMap.hasFDerivAt π).comp p
      ((hΨ.contDiffAt.hasStrictFDerivAt (by norm_num)).hasFDerivAt)
    simpa [hg, Function.comp_def] using h2
  have hgc : fderiv ℝ g p = π.comp (fderiv ℝ Ψ p) := h1.fderiv
  have hrange : (π.comp (fderiv ℝ Ψ p)).range = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    obtain ⟨x, hx⟩ := y.2
    refine ⟨x, ?_⟩
    show π ((fderiv ℝ Ψ p) x) = y
    have hy : (fderiv ℝ Ψ p) x = (y : F) := hx
    rw [hy]
    show π (y : F) = y
    simp only [hπ, hπL, LinearMap.coe_toContinuousLinearMap']
    exact Submodule.projectionOnto_apply_left hq y
  have hsurj : (fderiv ℝ g p).range = ⊤ := by
    simpa only [hgc] using hrange
  have hkerrank : Module.finrank ℝ (fderiv ℝ g p).ker ≤ Module.finrank ℝ V - 1 := by
    have key : Module.finrank ℝ (fderiv ℝ g p).range +
        Module.finrank ℝ (fderiv ℝ g p).ker = Module.finrank ℝ (V × W) :=
      LinearMap.finrank_range_add_finrank_ker _
    rw [hsurj, finrank_top, Module.finrank_prod] at key
    omega
  have hcont : ContDiffAt ℝ 1 g p := by
    have h3 : ContDiffAt ℝ 1 (fun x : V × W => π (Ψ x)) p :=
      (π.contDiff.comp hΨ).contDiffAt (x := p)
    simpa [hg] using h3
  obtain ⟨O, hOo, hpO, γ, C, L, hlip, hcov⟩ :=
    Work.Drive.exists_lipschitz_param_of_fderiv_surjective (f := g) (a := p) hcont hsurj
  refine ⟨O, Prod.fst '' (γ '' C), hOo, hpO, ?_, ?_⟩
  · calc dimH (Prod.fst '' (γ '' C))
        ≤ dimH (γ '' C) :=
          (ContinuousLinearMap.fst ℝ V W).lipschitz.lipschitzOnWith.dimH_image_le
      _ ≤ dimH C := hlip.dimH_image_le
      _ ≤ dimH (Set.univ : Set ((fderiv ℝ g p).ker)) := dimH_mono (Set.subset_univ _)
      _ = ((Module.finrank ℝ ((fderiv ℝ g p).ker) : ℕ) : ENNReal) :=
          Real.dimH_univ_eq_finrank _
      _ ≤ ((Module.finrank ℝ V - 1 : ℕ) : ENNReal) := by exact_mod_cast hkerrank
  · rintro v ⟨z, ⟨hzO, hzΨ⟩, rfl⟩
    have hgz : g z = g p := by
      show π (Ψ z) = π (Ψ p)
      rw [hzΨ, hp, map_zero]
    obtain ⟨y, hyC, hyz⟩ := hcov z hzO hgz
    exact ⟨γ y, ⟨y, hyC, rfl⟩, by rw [hyz]⟩

/-- The `NormedSpace`-only form of `Work.Drive.interior_projection_zeroSet_of_rank_except`
(`Submission/Work/Drive/interior_projection_zeroSet_of_rank_except.lean`): the three hypotheses
`[InnerProductSpace ℝ ·]` on `V`, `W`, `F` are weakened to `[NormedSpace ℝ ·]`. -/
theorem interior_projection_zeroSet_of_rank_except_normed
    {V W F : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {Ψ : V × W → F} (hΨ : ContDiff ℝ 1 Ψ)
    {Z Z₀ : Set (V × W)} (hZ : IsCompact Z) (hZ₀c : IsClosed Z₀)
    (hrank : ∀ p ∈ Z, p ∉ Z₀ → Ψ p = 0 →
      Module.finrank ℝ W < Module.finrank ℝ (fderiv ℝ Ψ p).range)
    (hZ₀ : interior (Prod.fst '' (Z ∩ Z₀ ∩ {p : V × W | Ψ p = 0})) = ∅) :
    interior (Prod.fst '' (Z ∩ {p : V × W | Ψ p = 0})) = ∅ := by
  classical
  set S : Set (V × W) := Z ∩ {p : V × W | Ψ p = 0} with hS
  set S₀ : Set (V × W) := Z ∩ Z₀ ∩ {p : V × W | Ψ p = 0} with hS₀
  set S₁ : Set (V × W) := Z ∩ Z₀ᶜ ∩ {p : V × W | Ψ p = 0} with hS₁
  have hS_eq : S = S₀ ∪ S₁ := by
    rw [hS, hS₀, hS₁]
    ext x
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq]
    tauto
  by_cases hS₁e : S₁ = ∅
  · -- The whole zero set is exceptional; conclude by hypothesis.
    have hSeq : S = S₀ := by rw [hS_eq, hS₁e, Set.union_empty]
    rw [hSeq]; exact hZ₀
  · -- The complement of `Z₀` carries genuine zeros; cover it by small pieces.
    haveI : Nonempty (↥S₁) :=
      Set.nonempty_coe_sort.mpr (Set.nonempty_iff_ne_empty.mpr hS₁e)
    have hdata : ∀ p : S₁, ∃ (O : Set (V × W)) (U : Set V), IsOpen O ∧ p.1 ∈ O ∧
        dimH U ≤ ((Module.finrank ℝ V - 1 : ℕ) : ENNReal) ∧
        Prod.fst '' (O ∩ {q : V × W | Ψ q = 0}) ⊆ U :=
      fun p => exists_small_nbhd_rank_gt_normed hΨ p.2.2 (hrank p.1 p.2.1.1 p.2.1.2 p.2.2)
    choose O U hOo hpO hUdim hUsub using hdata
    have hcover : S₁ ⊆ ⋃ p : S₁, O p :=
      fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hpO ⟨x, hx⟩⟩
    obtain ⟨f, hf⟩ := IsLindelof.indexed_countable_subcover (s := S₁)
      (IsLindelof.of_coe (s := S₁)) O hOo hcover
    have hsub : Prod.fst '' S₁ ⊆ ⋃ n, U (f n) := by
      rintro x ⟨q', hq', rfl⟩
      have h1 : q' ∈ ⋃ n, O (f n) := hf hq'
      rw [Set.mem_iUnion] at h1
      obtain ⟨n, hn⟩ := h1
      exact Set.mem_iUnion.mpr ⟨n, hUsub (f n) ⟨q', ⟨hn, hq'.2⟩, rfl⟩⟩
    have hdim : dimH (Prod.fst '' S₁) ≤ ((Module.finrank ℝ V - 1 : ℕ) : ENNReal) := by
      calc dimH (Prod.fst '' S₁) ≤ dimH (⋃ n, U (f n)) := dimH_mono hsub
        _ = ⨆ n, dimH (U (f n)) := dimH_iUnion _
        _ ≤ _ := iSup_le fun n => hUdim (f n)
    have hS₀cpt : IsCompact S₀ := by
      rw [hS₀, Set.inter_assoc]
      exact hZ.inter_right (hZ₀c.inter (isClosed_singleton.preimage hΨ.continuous))
    have hclo : IsClosed (Prod.fst '' S₀) := (hS₀cpt.image continuous_fst).isClosed
    have hVpos : 1 ≤ Module.finrank ℝ V := by
      obtain ⟨p⟩ := (inferInstance : Nonempty (↥S₁))
      have h1 : Module.finrank ℝ (fderiv ℝ Ψ p.1).range ≤ Module.finrank ℝ (V × W) :=
        LinearMap.finrank_range_le (fderiv ℝ Ψ p.1).toLinearMap
      have h2 : Module.finrank ℝ (V × W) = Module.finrank ℝ V + Module.finrank ℝ W :=
        Module.finrank_prod
      have h3 := hrank p.1 p.2.1.1 p.2.1.2 p.2.2
      omega
    -- The exceptional projection is closed with empty interior; a residual open ball would
    -- have to lie in the projection of `S₁`, contradicting `dimH < finrank ℝ V`.
    refine Set.not_nonempty_iff_eq_empty.mp ?_
    rintro ⟨x, hx⟩
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
    have hnotsub : ¬ (Metric.ball x r ⊆ Prod.fst '' S₀) := by
      intro hsub'
      have hne' : (interior (Prod.fst '' S₀)).Nonempty :=
        ⟨x, mem_interior_iff_mem_nhds.mpr
          (Filter.mem_of_superset (Metric.ball_mem_nhds x hr) hsub')⟩
      rw [hZ₀] at hne'
      exact Set.not_nonempty_empty hne'
    have hopen : IsOpen (Metric.ball x r \ Prod.fst '' S₀) := by
      rw [Set.sdiff_eq]
      exact Metric.isOpen_ball.inter hclo.isOpen_compl
    have hne2 : (Metric.ball x r \ Prod.fst '' S₀).Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at h
      exact hnotsub h
    have hcont : Metric.ball x r \ Prod.fst '' S₀ ⊆ Prod.fst '' S₁ := by
      rintro y ⟨hyb, hyS₀⟩
      have hyS : y ∈ Prod.fst '' S := hball hyb
      rw [hS_eq, Set.image_union] at hyS
      rcases hyS with h | h
      · exact absurd h hyS₀
      · exact h
    have hint : (interior (Prod.fst '' S₁)).Nonempty :=
      hne2.mono (interior_maximal hcont hopen)
    have hdimV := Real.dimH_of_nonempty_interior hint
    have hle : ((Module.finrank ℝ V : ℕ) : ENNReal) ≤
        ((Module.finrank ℝ V - 1 : ℕ) : ENNReal) := by
      rw [← hdimV]; exact hdim
    have hlt : ((Module.finrank ℝ V - 1 : ℕ) : ENNReal) <
        ((Module.finrank ℝ V : ℕ) : ENNReal) := by
      have h := Nat.sub_lt (n := Module.finrank ℝ V) (m := 1) (by omega) (by norm_num)
      exact_mod_cast h
    exact absurd hle (not_le.mpr hlt)

end Work.Drive
