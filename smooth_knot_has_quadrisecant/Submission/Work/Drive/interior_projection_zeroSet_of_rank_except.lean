import Mathlib
import Submission.Work.Drive.interior_zeroSet_projection_empty

/-!
# Projection of a zero set with a rank hypothesis outside an exceptional set

This file proves `Work.Drive.interior_projection_zeroSet_of_rank_except`.

Let `V, W, F` be finite dimensional real inner product spaces, `Ψ : V × W → F` a `C¹` map,
`Z ⊆ V × W` compact and `Z₀ ⊆ V × W` closed.  Assume that at every zero `p ∈ Z \ Z₀` of `Ψ`
the derivative `DΨ p : V × W → F` has rank strictly larger than `dim W`, i.e.

`finrank ℝ W < finrank ℝ (fderiv ℝ Ψ p).range`,

and that the projection to `V` of the exceptional zero set `Z ∩ Z₀ ∩ {Ψ = 0}` has empty
interior.  Then the projection to `V` of the whole zero set `Z ∩ {Ψ = 0}` has empty interior.

The mathematical content is a dimension count.  At a zero `p ∈ Z \ Z₀` the hypothesis says
that the kernel of `DΨ p` has dimension `finrank ℝ (V × W) - rank ≥ finrank ℝ V + finrank ℝ W -
(finrank ℝ W + 1) = finrank ℝ V - 1 < finrank ℝ V`.  The level set of `Ψ` near `p` is contained
in a locally Lipschitz image of (an open subset of) the kernel of a surjective-on-the-range
restriction of `DΨ p`, and a Lipschitz image of a set of Hausdorff dimension `< finrank ℝ V`
has empty interior.  Since the projection of the exceptional part `Z ∩ Z₀` is closed with empty
interior, and the projection of the complement `Z \ Z₀` is covered by countably many such small
pieces (Lindelöf countability, then `dimH` is countably stable), the union has empty interior.

## Contents

* `exists_small_nbhd_rank_gt` — the local statement: near a zero of `Ψ` at which `DΨ` has rank
  larger than `dim W`, the projection of the zero set is contained in a set of Hausdorff dimension
  at most `finrank ℝ V - 1`;
* `interior_projection_zeroSet_of_rank_except` — the global statement.
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
with the orthogonal projection `A : F →L[ℝ] R` onto `R`.  The composed map `A ∘ Ψ` is a
submersion at `p` (its derivative `A ∘ DΨ p` has range `R`), so its level set is, near `p`, a
locally Lipschitz image of the kernel of `A ∘ DΨ p` (implicit function theorem,
`exists_lipschitz_param_of_fderiv_surjective`).  That kernel has dimension
`finrank ℝ (V × W) - finrank ℝ R ≤ finrank ℝ V - 1`, and the Lipschitz projection to `V` does
not increase Hausdorff dimension. -/
theorem exists_small_nbhd_rank_gt
    {V W F : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {Ψ : V × W → F} (hΨ : ContDiff ℝ 1 Ψ)
    {p : V × W} (hp : Ψ p = 0)
    (hrank : Module.finrank ℝ W < Module.finrank ℝ (fderiv ℝ Ψ p).range) :
    ∃ (O : Set (V × W)) (U : Set V), IsOpen O ∧ p ∈ O ∧
      dimH U ≤ ((Module.finrank ℝ V - 1 : ℕ) : ENNReal) ∧
      Prod.fst '' (O ∩ {q : V × W | Ψ q = 0}) ⊆ U := by
  let T : (V × W) →L[ℝ] F := fderiv ℝ Ψ p
  let R : Submodule ℝ F := T.range
  let A : F →L[ℝ] R := R.orthogonalProjectionOnto
  have hcont : ContDiffAt ℝ 1 (fun q : V × W => A (Ψ q)) p :=
    (A.contDiff.contDiffAt).comp p hΨ.contDiffAt
  have hfderiv : fderiv ℝ (fun q : V × W => A (Ψ q)) p = A.comp T := by
    have h1 : HasFDerivAt (fun q : V × W => A (Ψ q)) (A.comp T) p := by
      simpa only [Function.comp_def] using
        (A.hasFDerivAt (x := Ψ p)).comp p
          ((hΨ.contDiffAt.hasStrictFDerivAt (by norm_num)).hasFDerivAt)
    exact h1.fderiv
  have hrange : (A.comp T).range = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    obtain ⟨v, hv⟩ := LinearMap.mem_range.mp (show (y : F) ∈ T.range from y.2)
    refine ⟨v, ?_⟩
    have hmem : T v ∈ R := ⟨v, rfl⟩
    have hthis : A (T v) = (⟨T v, hmem⟩ : R) :=
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨T v, hmem⟩
    change A (T v) = y
    rw [hthis]
    exact Subtype.ext hv
  obtain ⟨O, hOo, hpO, γ, C, L, hlip, hcov⟩ :=
    exists_lipschitz_param_of_fderiv_surjective (f := fun q : V × W => A (Ψ q)) hcont
      (by rw [hfderiv]; exact hrange)
  refine ⟨O, Prod.fst '' (γ '' C), hOo, hpO, ?_, ?_⟩
  · calc dimH (Prod.fst '' (γ '' C))
        ≤ dimH (γ '' C) :=
          (ContinuousLinearMap.fst ℝ V W).lipschitz.lipschitzOnWith.dimH_image_le
      _ ≤ dimH C := hlip.dimH_image_le
      _ ≤ dimH (Set.univ : Set ((fderiv ℝ (fun q : V × W => A (Ψ q)) p).ker)) :=
          dimH_mono (Set.subset_univ _)
      _ = ((Module.finrank ℝ ((fderiv ℝ (fun q : V × W => A (Ψ q)) p).ker) : ℕ) : ENNReal) :=
          Real.dimH_univ_eq_finrank _
      _ ≤ ((Module.finrank ℝ V - 1 : ℕ) : ENNReal) := by
          have hrank' : Module.finrank ℝ W < Module.finrank ℝ T.range := hrank
          have h1 := LinearMap.finrank_range_add_finrank_ker (A.comp T).toLinearMap
          have h2 : Module.finrank ℝ ((A.comp T).range) = Module.finrank ℝ T.range := by
            rw [hrange, finrank_top]
          have h3 : Module.finrank ℝ (V × W) = Module.finrank ℝ V + Module.finrank ℝ W :=
            Module.finrank_prod
          have h4 : Module.finrank ℝ ((A.comp T).ker) ≤ Module.finrank ℝ V - 1 := by omega
          rw [hfderiv]
          exact_mod_cast h4
  · rintro x ⟨q, ⟨hqO, hqΨ⟩, rfl⟩
    obtain ⟨y, hyC, hyq⟩ := hcov q hqO (by rw [hqΨ, hp, map_zero])
    exact ⟨γ y, ⟨y, hyC, rfl⟩, by rw [hyq]⟩

theorem interior_projection_zeroSet_of_rank_except
    {V W F : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
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
      fun p => exists_small_nbhd_rank_gt hΨ p.2.2 (hrank p.1 p.2.1.1 p.2.1.2 p.2.2)
    choose O U hOo hpO hUdim hUsub using hdata
    have hcover : S₁ ⊆ ⋃ p : S₁, O p :=
      fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hpO ⟨x, hx⟩⟩
    obtain ⟨f, hf⟩ := IsLindelof.indexed_countable_subcover (s := S₁)
      (IsLindelof.of_coe (s := S₁)) O hOo hcover
    have hsub : Prod.fst '' S₁ ⊆ ⋃ n, U (f n) := by
      rintro x ⟨q, hq, rfl⟩
      have h1 : q ∈ ⋃ n, O (f n) := hf hq
      rw [Set.mem_iUnion] at h1
      obtain ⟨n, hn⟩ := h1
      exact Set.mem_iUnion.mpr ⟨n, hUsub (f n) ⟨q, ⟨hn, hq.2⟩, rfl⟩⟩
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
