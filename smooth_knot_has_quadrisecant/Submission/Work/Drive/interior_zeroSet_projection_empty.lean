import Mathlib
import Submission.Work.Drive.volume_image_lipschitzOnWith_zero

/-!
# The projection of a fibrewise-submersive zero set has empty interior

`Work.Drive.interior_zeroSet_projection_empty`: let `Ψ : V × W → F` be `C¹` (`V, W, F` finite
dimensional real inner product spaces) with `finrank ℝ W < finrank ℝ F`, let `Kv ⊆ V` and `K ⊆ W`
be compact, and assume that at every zero `p = (v, w) ∈ Kv × K` the partial derivative of `Ψ` in
the `V`-variable, `v' ↦ Ψ (v', w)`, is *surjective* onto `F`.  Then

`{v | v ∈ Kv ∧ ∃ w ∈ K, Ψ (v, w) = 0}`

has empty interior in `V`.

The proof is a dimension count.  At a zero `p` the full derivative `DΨ p : V × W → F` is
surjective, so near `p` the zero set of `Ψ` is the image of a `C¹` (hence locally Lipschitz) map
defined on `(DΨ p).ker`, a space of dimension `finrank ℝ (V × W) - finrank ℝ F`.  Since
`finrank ℝ W < finrank ℝ F`, this is `< finrank ℝ V`, and a Lipschitz image of a subset of a
lower-dimensional space has Hausdorff dimension `< finrank ℝ V`, hence empty interior (a set with
nonempty interior has Hausdorff dimension `finrank ℝ V`).  Compactness of `Kv × K` turns the local
descriptions into a finite cover.

## Contents

* `partial_fderiv_range_eq_top` — surjectivity of the partial derivative upgrades to surjectivity of
  the full derivative (used to identify `(DΨ p).ker` and to invoke the implicit function theorem);
* `exists_lipschitz_param_of_fderiv_surjective` — the local Lipschitz parametrisation of a level
  set of a submersion (implicit function theorem in the `HasStrictFDerivAt.implicitFunctionOfComplemented`
  form, plus `HasStrictFDerivAt.exists_lipschitzOnWith`);
* `interior_zeroSet_projection_empty` — the statement above.
-/


open scoped Topology

namespace Work.Drive

/-- If `Ψ` is `C¹` at `p = (v, w)` and the partial derivative in the first variable,
`v' ↦ Ψ (v', w)`, has a surjective derivative `A` at `v`, then the full derivative `fderiv ℝ Ψ p`
is surjective: it is `A` composed with the inclusion `V → V × W`, so its range contains the range
of `A`. -/
theorem partial_fderiv_range_eq_top
    {V W F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ψ : V × W → F} {p : V × W} {A : V →L[ℝ] F}
    (hΨ : ContDiffAt ℝ 1 Ψ p) (hAsurj : Function.Surjective A)
    (hA : HasFDerivAt (fun v' : V => Ψ (v', p.2)) A p.1) :
    (fderiv ℝ Ψ p).range = ⊤ := by
  have hs : HasStrictFDerivAt Ψ (fderiv ℝ Ψ p) p := hΨ.hasStrictFDerivAt (by norm_num)
  have hcomp : HasFDerivAt (fun v' : V => Ψ (v', p.2))
      ((fderiv ℝ Ψ p).comp (ContinuousLinearMap.inl ℝ V W)) p.1 := by
    simpa only [Function.comp_def] using hs.hasFDerivAt.comp p.1 (hasFDerivAt_prodMk_left p.1 p.2)
  have hAeq : A = (fderiv ℝ Ψ p).comp (ContinuousLinearMap.inl ℝ V W) := hA.unique hcomp
  rw [LinearMap.range_eq_top]
  intro y
  obtain ⟨v, hv⟩ := hAsurj y
  refine ⟨(v, 0), ?_⟩
  have h2 : A v = (fderiv ℝ Ψ p) ((ContinuousLinearMap.inl ℝ V W) v) :=
    congrArg (fun (L : V →L[ℝ] F) => L v) hAeq
  have h3 : (fderiv ℝ Ψ p) ((ContinuousLinearMap.inl ℝ V W) v) = y := h2.symm.trans hv
  have hinl : (ContinuousLinearMap.inl ℝ V W) v = (v, 0) := rfl
  rwa [← hinl]

/-- **The zero set of a submersion is locally a Lipschitz image of `ker` of the derivative.**

Let `f : E → F` be `C¹` at `a` (with `E`, `F` finite dimensional over `ℝ`) and suppose the
derivative `fderiv ℝ f a` is surjective.  Then there are an open neighbourhood `O` of `a` and a map
`γ : ker (fderiv ℝ f a) → E` which is Lipschitz on a set `C` and such that every point of `O` at
which `f` takes the value `f a` lies in `γ '' C`.

This is the implicit function theorem in the "complemented kernel" form
(`HasStrictFDerivAt.implicitFunctionOfComplemented`): the level set of `f` near `a` is the image
of the implicit function, which is strictly differentiable at `0` and hence Lipschitz on a
neighbourhood of `0`. -/
theorem exists_lipschitz_param_of_fderiv_surjective
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E → F} {a : E} (hf : ContDiffAt ℝ 1 f a) (hf' : (fderiv ℝ f a).range = ⊤) :
    ∃ (O : Set E) (_ : IsOpen O) (_ : a ∈ O)
      (γ : (fderiv ℝ f a).ker → E) (C : Set (fderiv ℝ f a).ker) (L : NNReal),
      LipschitzOnWith L γ C ∧ ∀ x ∈ O, f x = f a → x ∈ γ '' C := by
  have hf_strict : HasStrictFDerivAt f (fderiv ℝ f a) a := hf.hasStrictFDerivAt (by norm_num)
  have hker : (fderiv ℝ f a).ker.ClosedComplemented :=
    ContinuousLinearMap.ker_closedComplemented_of_finiteDimensional_range (fderiv ℝ f a)
  let Φ : F → (fderiv ℝ f a).ker → E :=
    hf_strict.implicitFunctionOfComplemented f (fderiv ℝ f a) hf' hker
  let pr : E → (fderiv ℝ f a).ker := fun x =>
    (hf_strict.implicitToOpenPartialHomeomorphOfComplemented f (fderiv ℝ f a) hf' hker x).2
  have hγ : HasStrictFDerivAt (Φ (f a)) (fderiv ℝ f a).ker.subtypeL 0 :=
    hf_strict.to_implicitFunctionOfComplemented hf' hker
  obtain ⟨L, s, hs, hLip⟩ := hγ.exists_lipschitzOnWith
  have heq : ∀ᶠ x in 𝓝 a, Φ (f x) (pr x) = x :=
    hf_strict.eq_implicitFunctionOfComplemented hf' hker
  have hpr_cont : Continuous pr := by
    have h1 : pr = fun x : E => Classical.choose hker (x - a) := by
      funext x
      simp only [pr, HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented_apply]
    rw [h1]
    exact (Classical.choose hker).continuous.comp (continuous_id.sub continuous_const)
  have hpr_zero : pr a = 0 := by
    simp only [pr, HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented_apply,
      sub_self, map_zero]
  have hpr_nhds : pr ⁻¹' s ∈ 𝓝 a :=
    hpr_cont.continuousAt.preimage_mem_nhds (by rw [hpr_zero]; exact hs)
  have hfin : ({x : E | Φ (f x) (pr x) = x} ∩ pr ⁻¹' s) ∈ 𝓝 a :=
    Filter.inter_mem heq hpr_nhds
  refine ⟨interior ({x : E | Φ (f x) (pr x) = x} ∩ pr ⁻¹' s), isOpen_interior,
    mem_interior_iff_mem_nhds.mpr hfin, Φ (f a), s, L, hLip, ?_⟩
  intro x hx hx0
  have hsub : x ∈ {x : E | Φ (f x) (pr x) = x} ∩ pr ⁻¹' s := interior_subset hx
  exact ⟨pr x, hsub.2, by rw [← hx0, hsub.1]⟩

/-- **The projection of the zero set has empty interior.**  See the module docstring. -/
theorem interior_zeroSet_projection_empty
    {V W F : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (hd : Module.finrank ℝ W < Module.finrank ℝ F)
    {Ψ : V × W → F} (hΨ : ContDiff ℝ 1 Ψ)
    {Kv : Set V} (hKv : IsCompact Kv) {K : Set W} (hK : IsCompact K)
    (hsurj : ∀ p ∈ Kv ×ˢ K, Ψ p = 0 →
      ∃ A : V →L[ℝ] F, Function.Surjective A ∧
        HasFDerivAt (fun v' : V => Ψ (v', p.2)) A p.1) :
    interior {v : V | v ∈ Kv ∧ ∃ w ∈ K, Ψ (v, w) = 0} = ∅ := by
  let D : ℕ := Module.finrank ℝ V + Module.finrank ℝ W - Module.finrank ℝ F
  set S : Set V := {v : V | v ∈ Kv ∧ ∃ w ∈ K, Ψ (v, w) = 0} with hS
  by_contra hne
  have hSne : (interior S).Nonempty := Set.nonempty_iff_ne_empty.mpr hne
  have hdimS : dimH S = ((Module.finrank ℝ V : ℕ) : ENNReal) :=
    Real.dimH_of_nonempty_interior hSne
  set Z : Set (V × W) := (Kv ×ˢ K) ∩ {p : V × W | Ψ p = 0} with hZ
  have hZc : IsCompact Z := by
    rw [hZ]
    exact (hKv.prod hK).inter_right (isClosed_singleton.preimage hΨ.continuous)
  have hS_eq : S = Prod.fst '' Z := by
    rw [hS, hZ]
    ext v
    constructor
    · rintro ⟨hvK, w, hwK, hw⟩
      exact ⟨(v, w), ⟨⟨hvK, hwK⟩, hw⟩, rfl⟩
    · rintro ⟨p, ⟨⟨hp1, hp2⟩, hp3⟩, rfl⟩
      exact ⟨hp1, p.2, hp2, hp3⟩
  -- Local Lipschitz parametrisation of the zero set at every zero point.
  have hcover_data : ∀ p : Z, ∃ (O : Set (V × W)) (γ : (fderiv ℝ Ψ p.1).ker → V × W)
      (C : Set (fderiv ℝ Ψ p.1).ker) (L : NNReal),
      IsOpen O ∧ p.1 ∈ O ∧ LipschitzOnWith L γ C ∧
        ∀ q ∈ O, Ψ q = 0 → q.1 ∈ Prod.fst '' (γ '' C) := by
    intro p
    have hpmem : p.1 ∈ Kv ×ˢ K := p.2.1
    have hp0 : Ψ p.1 = 0 := p.2.2
    obtain ⟨A, hAsurj, hAda⟩ := hsurj p.1 hpmem hp0
    have hf' : (fderiv ℝ Ψ p.1).range = ⊤ :=
      partial_fderiv_range_eq_top hΨ.contDiffAt hAsurj hAda
    obtain ⟨O, hOo, hpO, γ, C, L, hLip, hcov⟩ :=
      exists_lipschitz_param_of_fderiv_surjective hΨ.contDiffAt hf'
    refine ⟨O, γ, C, L, hOo, hpO, hLip, ?_⟩
    intro q hq hq0
    obtain ⟨y, hyC, hyq⟩ := hcov q hq (by rw [hq0, hp0])
    exact ⟨γ y, ⟨y, hyC, rfl⟩, congrArg Prod.fst hyq⟩
  choose O γ C L hOo hpO hLip hcov using hcover_data
  have hZcover : Z ⊆ ⋃ p : Z, O p := fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hpO ⟨x, hx⟩⟩
  obtain ⟨t, ht⟩ := hZc.elim_finite_subcover O (fun p => hOo p) hZcover
  -- Each piece of the finite cover is contained in a Lipschitz image of a kernel of dimension `D`.
  have hpiece : ∀ p : Z, dimH (Prod.fst '' (Z ∩ O p)) ≤ (D : ENNReal) := by
    intro p
    have hpmem : p.1 ∈ Kv ×ˢ K := p.2.1
    have hp0 : Ψ p.1 = 0 := p.2.2
    obtain ⟨A, hAsurj, hAda⟩ := hsurj p.1 hpmem hp0
    have hf' : (fderiv ℝ Ψ p.1).range = ⊤ :=
      partial_fderiv_range_eq_top hΨ.contDiffAt hAsurj hAda
    have hkereq : Module.finrank ℝ ((fderiv ℝ Ψ p.1).ker) = D := by
      have h1 : Module.finrank ℝ (fderiv ℝ Ψ p.1).range
          + Module.finrank ℝ ((fderiv ℝ Ψ p.1).ker) = Module.finrank ℝ (V × W) :=
        LinearMap.finrank_range_add_finrank_ker _
      have h2 : Module.finrank ℝ (fderiv ℝ Ψ p.1).range = Module.finrank ℝ F := by
        rw [hf', finrank_top]
      have h3 : Module.finrank ℝ (V × W) = Module.finrank ℝ V + Module.finrank ℝ W :=
        Module.finrank_prod
      simp only [D]
      omega
    calc dimH (Prod.fst '' (Z ∩ O p))
        ≤ dimH (Prod.fst '' (γ p '' C p)) := by
          refine dimH_mono ?_
          rintro v ⟨q, ⟨hqZ, hqO⟩, rfl⟩
          exact hcov p q hqO hqZ.2
      _ ≤ dimH (γ p '' C p) :=
          (ContinuousLinearMap.fst ℝ V W).lipschitz.lipschitzOnWith.dimH_image_le
      _ ≤ dimH (C p) := (hLip p).dimH_image_le
      _ ≤ dimH (Set.univ : Set ((fderiv ℝ Ψ p.1).ker)) := dimH_mono (Set.subset_univ _)
      _ = ((Module.finrank ℝ ((fderiv ℝ Ψ p.1).ker) : ℕ) : ENNReal) :=
          Real.dimH_univ_eq_finrank _
      _ = (D : ENNReal) := by rw [hkereq]
  have hsubS : S ⊆ ⋃ p ∈ (t : Set Z), Prod.fst '' (Z ∩ O p) := by
    rw [hS_eq]
    rintro v ⟨q, hqZ, rfl⟩
    have h1 : q ∈ ⋃ p ∈ (t : Set Z), O p := by
      have h2 := ht hqZ
      simpa only [Set.mem_iUnion, Finset.mem_coe] using h2
    rw [Set.mem_iUnion] at h1
    obtain ⟨p, h1⟩ := h1
    rw [Set.mem_iUnion] at h1
    obtain ⟨hp, hqOp⟩ := h1
    exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, ⟨q, ⟨hqZ, hqOp⟩, rfl⟩⟩⟩
  have hbound : dimH S ≤ (D : ENNReal) := by
    calc dimH S ≤ dimH (⋃ p ∈ (t : Set Z), Prod.fst '' (Z ∩ O p)) := dimH_mono hsubS
      _ = ⨆ p ∈ (t : Set Z), dimH (Prod.fst '' (Z ∩ O p)) :=
          dimH_bUnion (t.finite_toSet.countable) _
      _ ≤ (D : ENNReal) := iSup₂_le fun p _ => hpiece p
  -- `D < finrank ℝ V`, because `finrank ℝ W < finrank ℝ F` and `finrank ℝ V ≥ 1`.
  have hVpos : 1 ≤ Module.finrank ℝ V := by
    obtain ⟨v₀, hv₀⟩ := hSne
    have hv₀S : v₀ ∈ S := interior_subset hv₀
    rw [hS] at hv₀S
    obtain ⟨hv₀K, w₀, hw₀K, hw₀⟩ := hv₀S
    obtain ⟨A, hAsurj, -⟩ := hsurj (v₀, w₀) ⟨hv₀K, hw₀K⟩ hw₀
    have hle : Module.finrank ℝ F ≤ Module.finrank ℝ V :=
      LinearMap.finrank_le_finrank_of_surjective hAsurj
    omega
  have hlt : (D : ENNReal) < ((Module.finrank ℝ V : ℕ) : ENNReal) := by
    have hnat : D < Module.finrank ℝ V := by
      have hpos := hVpos
      simp only [D]
      omega
    exact_mod_cast hnat
  rw [hdimS] at hbound
  exact (not_le.mpr hlt) hbound

end Work.Drive
