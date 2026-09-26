import Mathlib
import Submission.Work.Drive.interior_zeroSet_projection_empty

/-!
# The zero set of a map with a rank condition has small projection

`Work.Proj.interior_zeroSet_projection_empty_of_rank` is a local copy of the rank form of the
implicit-function-theorem dimension count used by the genericity arguments in this directory:
if `Ψ : V × W → F` is `C¹`, `Kv` and `K` are compact and at every zero `p` of `Ψ` in `Kv × K`
the derivative of `Ψ` has rank `> finrank ℝ W`, then the set of `v ∈ Kv` for which `Ψ v` vanishes
somewhere on `K` has **empty interior**.

It is copied here (with the proof of the version in
`Submission/Work/Drive/exists_close_transverse_noInflection.lean`) so that the patch-stratum files
of `Submission/Work/Drive/patchStrata.lean` do not have to import that (currently evolving) module.
-/

open scoped Topology

namespace Work.Proj

/-- **The projection of a rank-`>finrank W` zero set has empty interior.**  See the module
docstring. -/
theorem interior_zeroSet_projection_empty_of_rank
    {V W F : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {Ψ : V × W → F} (hΨ : ContDiff ℝ 1 Ψ)
    {Kv : Set V} (hKv : IsCompact Kv) {K : Set W} (hK : IsCompact K)
    (hrank : ∀ p ∈ Kv ×ˢ K, Ψ p = 0 →
      Module.finrank ℝ W < Module.finrank ℝ (fderiv ℝ Ψ p).range) :
    interior {v : V | v ∈ Kv ∧ ∃ w ∈ K, Ψ (v, w) = 0} = ∅ := by
  classical
  set S : Set V := {v : V | v ∈ Kv ∧ ∃ w ∈ K, Ψ (v, w) = 0} with hSdef
  set Z : Set (V × W) := (Kv ×ˢ K) ∩ {p : V × W | Ψ p = 0} with hZdef
  have hZc : IsCompact Z := by
    rw [hZdef]
    exact (hKv.prod hK).inter_right (isClosed_singleton.preimage hΨ.continuous)
  have hSeq : S = Prod.fst '' Z := by
    rw [hSdef, hZdef]
    ext v
    constructor
    · rintro ⟨hvK, w, hwK, hw⟩
      exact ⟨(v, w), ⟨⟨hvK, hwK⟩, hw⟩, rfl⟩
    · rintro ⟨p, ⟨⟨hp1, hp2⟩, hp3⟩, rfl⟩
      exact ⟨hp1, p.2, hp2, hp3⟩
  have hchart : ∀ p : Z, ∃ (O : Set (V × W)) (γ : V × W → V × W) (C : Set (V × W)),
      IsOpen O ∧ p.1 ∈ O ∧ (∀ x ∈ O, Ψ x = 0 → x ∈ γ '' C) ∧
        dimH (γ '' C) ≤ ((Module.finrank ℝ V - 1 : ℕ) : ENNReal) := by
    intro p
    obtain ⟨hpmem, hp0⟩ := p.2
    have hdim : Module.finrank ℝ W < Module.finrank ℝ (fderiv ℝ Ψ p.1).range :=
      hrank p.1 hpmem hp0
    obtain ⟨q, hq⟩ := Submodule.exists_isCompl (fderiv ℝ Ψ p.1).range
    set πL : F →ₗ[ℝ] (fderiv ℝ Ψ p.1).range :=
      Submodule.projectionOnto (fderiv ℝ Ψ p.1).range q hq with hπL
    set π : F →L[ℝ] (fderiv ℝ Ψ p.1).range := LinearMap.toContinuousLinearMap πL with hπ
    set g : V × W → (fderiv ℝ Ψ p.1).range := fun x => π (Ψ x) with hg
    have h1 : HasFDerivAt g (π.comp (fderiv ℝ Ψ p.1)) p.1 := by
      have h2 := (ContinuousLinearMap.hasFDerivAt π).comp p.1
        ((hΨ.contDiffAt.hasStrictFDerivAt (by norm_num)).hasFDerivAt)
      simpa [hg, Function.comp_def] using h2
    have hgc : fderiv ℝ g p.1 = π.comp (fderiv ℝ Ψ p.1) := h1.fderiv
    have hsurj : (fderiv ℝ g p.1).range = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro y
      obtain ⟨x, hx⟩ := y.2
      refine ⟨x, ?_⟩
      show fderiv ℝ g p.1 x = y
      rw [hgc]
      show π ((fderiv ℝ Ψ p.1) x) = y
      have hy : (fderiv ℝ Ψ p.1) x = (y : F) := hx
      rw [hy]
      show π (y : F) = y
      simp only [hπ, hπL, LinearMap.coe_toContinuousLinearMap']
      exact Submodule.projectionOnto_apply_left hq y
    have hkerrank : Module.finrank ℝ (fderiv ℝ g p.1).ker ≤ Module.finrank ℝ V - 1 := by
      have key : Module.finrank ℝ (fderiv ℝ g p.1).range +
          Module.finrank ℝ (fderiv ℝ g p.1).ker = Module.finrank ℝ (V × W) :=
        LinearMap.finrank_range_add_finrank_ker _
      rw [hsurj, finrank_top, Module.finrank_prod] at key
      omega
    have hcontdiff : ContDiffAt ℝ 1 g p.1 := by
      have h3 : ContDiffAt ℝ 1 (fun x : V × W => π (Ψ x)) p.1 :=
        (π.contDiff.comp hΨ).contDiffAt (x := p.1)
      simpa [hg] using h3
    obtain ⟨O, hOo, hpO, γ₀, C₀, L, hLip, hcov⟩ :=
      Work.Drive.exists_lipschitz_param_of_fderiv_surjective (f := g) (a := p.1) hcontdiff hsurj
    refine ⟨O, (fun x : V × W =>
        if h : x ∈ (fderiv ℝ g p.1).ker then γ₀ ⟨x, h⟩ else 0),
      Subtype.val '' C₀, hOo, hpO, ?_, ?_⟩
    · intro x hx hx0
      have hxg : g x = g p.1 := by
        show π (Ψ x) = π (Ψ p.1)
        rw [hx0, hp0, map_zero]
      obtain ⟨z, hzC, hzγ⟩ := hcov x hx hxg
      refine ⟨(z : V × W), ⟨z, hzC, rfl⟩, ?_⟩
      simp only [dif_pos z.2]
      exact hzγ
    · have hset : (fun x : V × W =>
          if h : x ∈ (fderiv ℝ g p.1).ker then γ₀ ⟨x, h⟩ else 0) '' (Subtype.val '' C₀)
          = γ₀ '' C₀ := by
        ext y
        constructor
        · rintro ⟨x, ⟨z, hzC, rfl⟩, hxy⟩
          refine ⟨z, hzC, ?_⟩
          simpa only [dif_pos z.2] using hxy
        · rintro ⟨z, hzC, rfl⟩
          exact ⟨(z : V × W), ⟨z, hzC, rfl⟩, by simp only [dif_pos z.2]⟩
      rw [hset]
      calc dimH (γ₀ '' C₀) ≤ dimH C₀ := hLip.dimH_image_le
        _ ≤ dimH (Set.univ : Set ((fderiv ℝ g p.1).ker)) := dimH_mono (Set.subset_univ _)
        _ = ((Module.finrank ℝ ((fderiv ℝ g p.1).ker) : ℕ) : ENNReal) :=
            Real.dimH_univ_eq_finrank _
        _ ≤ ((Module.finrank ℝ V - 1 : ℕ) : ENNReal) := by exact_mod_cast hkerrank
  choose O γ C hOo hpO hcov hdim using hchart
  have hZcover : Z ⊆ ⋃ p : Z, O p := fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hpO ⟨x, hx⟩⟩
  obtain ⟨t, ht⟩ := hZc.elim_finite_subcover O (fun p => hOo p) hZcover
  have hpiece : ∀ p : Z, dimH (Prod.fst '' (Z ∩ O p)) ≤
      ((Module.finrank ℝ V - 1 : ℕ) : ENNReal) := by
    intro p
    calc dimH (Prod.fst '' (Z ∩ O p))
        ≤ dimH (Prod.fst '' (γ p '' C p)) := by
          refine dimH_mono ?_
          rintro v ⟨q, ⟨hqZ, hqO⟩, rfl⟩
          obtain ⟨w, hw, hwq⟩ := hcov p q hqO hqZ.2
          exact ⟨γ p w, ⟨w, hw, rfl⟩, by rw [hwq]⟩
      _ ≤ dimH (γ p '' C p) :=
          (ContinuousLinearMap.fst ℝ V W).lipschitz.lipschitzOnWith.dimH_image_le
      _ ≤ _ := hdim p
  have hsubS : S ⊆ ⋃ p ∈ (t : Set Z), Prod.fst '' (Z ∩ O p) := by
    rw [hSeq]
    rintro v ⟨q, hqZ, rfl⟩
    have h1 : q ∈ ⋃ p ∈ (t : Set Z), O p := by
      have h2 := ht hqZ
      simpa only [Set.mem_iUnion, Finset.mem_coe] using h2
    rw [Set.mem_iUnion] at h1
    obtain ⟨p, h1⟩ := h1
    rw [Set.mem_iUnion] at h1
    obtain ⟨hp, hqOp⟩ := h1
    exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, ⟨q, ⟨hqZ, hqOp⟩, rfl⟩⟩⟩
  have hbound : dimH S ≤ ((Module.finrank ℝ V - 1 : ℕ) : ENNReal) := by
    calc dimH S ≤ dimH (⋃ p ∈ (t : Set Z), Prod.fst '' (Z ∩ O p)) := dimH_mono hsubS
      _ = ⨆ p ∈ (t : Set Z), dimH (Prod.fst '' (Z ∩ O p)) :=
          dimH_bUnion (t.finite_toSet.countable) _
      _ ≤ ((Module.finrank ℝ V - 1 : ℕ) : ENNReal) := iSup₂_le fun p _ => hpiece p
  by_contra hne
  have hSne : (interior S).Nonempty := Set.nonempty_iff_ne_empty.mpr hne
  have hdimS : dimH S = ((Module.finrank ℝ V : ℕ) : ENNReal) :=
    Real.dimH_of_nonempty_interior hSne
  rw [hdimS] at hbound
  have hpos : 1 ≤ Module.finrank ℝ V := by
    obtain ⟨v, hv⟩ := hSne
    have hvS : v ∈ S := interior_subset hv
    rw [hSdef] at hvS
    obtain ⟨hvK, w, hwK, hw⟩ := hvS
    have h1 : Module.finrank ℝ W < Module.finrank ℝ (fderiv ℝ Ψ (v, w)).range :=
      hrank (v, w) ⟨hvK, hwK⟩ hw
    have h2 : Module.finrank ℝ (fderiv ℝ Ψ (v, w)).range +
        Module.finrank ℝ (fderiv ℝ Ψ (v, w)).ker = Module.finrank ℝ (V × W) :=
      LinearMap.finrank_range_add_finrank_ker _
    rw [Module.finrank_prod] at h2
    omega
  have hlt : ((Module.finrank ℝ V - 1 : ℕ) : ENNReal) <
      ((Module.finrank ℝ V : ℕ) : ENNReal) :=
    by exact_mod_cast Nat.sub_lt hpos Nat.zero_lt_one
  exact absurd hbound (not_le.mpr hlt)

end Work.Proj
