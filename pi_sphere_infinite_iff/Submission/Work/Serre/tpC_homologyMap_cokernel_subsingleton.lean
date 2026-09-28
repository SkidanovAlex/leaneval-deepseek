import Mathlib
import Submission.Work.Kunneth.Chapter
import Submission.Work.Serre.tpMapLin_component
import Submission.Work.Serre.exact_lTensor_cokernel

/-!
# Right exactness of `tpC C -` on rational homology

For a chain map `φ : D' ⟶ D` of chain complexes of `ℤ`-modules with `C` degreewise free, the
degreewise short exact sequence `0 → tpC C D' → tpC C D → tpC C (cokernel φ) → 0` gives a long
exact sequence in homology; hence the cokernel of `H_n(tpC C D') → H_n(tpC C D)` embeds into
`H_n(tpC C (cokernel φ))`.  Consequently, if the rationalisation of `H_j(tpC C (cokernel φ))`
is trivial for `j ≤ N`, then the rationalisation of
`coker (homologyMap (tpMap C C D' D 𝟙 φ) n)` is trivial for `n ≤ N`.
-/

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Serre

noncomputable section

set_option linter.style.haveILetI false

/-! ## The rationalisation of a torsion module -/

theorem tensorRat_subsingleton_of_torsion {A : Type*} [AddCommGroup A]
    (h : ∀ a : A, ∃ n : ℕ, 0 < n ∧ n • a = 0) : Subsingleton (TensorProduct ℤ A ℚ) := by
  rw [subsingleton_iff]
  intro x y
  have hzero : ∀ z : TensorProduct ℤ A ℚ, z = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul g q =>
        obtain ⟨n, hn, hng⟩ := h g
        have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
        have hng' : (n : ℤ) • g = 0 := by simpa using hng
        have hq : q = (n : ℤ) • (q / (n : ℚ)) := by
          rw [← Int.cast_smul_eq_zsmul ℚ (n : ℤ) (q / (n : ℚ)), smul_eq_mul, Int.cast_natCast]
          rw [eq_comm, mul_comm, div_mul_cancel₀ q hn0]
        rw [hq, TensorProduct.tmul_smul, TensorProduct.smul_tmul', hng']
        simp
    | add a b ha hb => rw [ha, hb, add_zero]
  rw [hzero x, hzero y]

theorem torsion_of_subsingleton_tensorRat {A : Type*} [AddCommGroup A]
    (h : Subsingleton (TensorProduct ℤ A ℚ)) (a : A) : ∃ n : ℕ, 0 < n ∧ n • a = 0 := by
  by_contra hc
  push Not at hc
  have key : ∀ z : ℤ, z • a = 0 → z = 0 := by
    intro z hz
    obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg z
    · rw [hn] at hz
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · omega
      · exact absurd (by simpa using hz) (hc n hpos)
    · rw [hn, neg_smul, neg_eq_zero] at hz
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · omega
      · exact absurd (by simpa using hz) (hc n hpos)
  set f : ℤ →ₗ[ℤ] A := LinearMap.toSpanSingleton ℤ A a with hf_def
  have hf_apply : ∀ z : ℤ, f z = z • a := by intro z; simp [hf_def]
  have hf : Function.Injective f := by
    intro m n hmn
    have h1 : (m - n) • a = 0 := by rw [sub_smul, ← hf_apply, ← hf_apply, hmn, sub_self]
    have h2 := key (m - n) h1
    omega
  have hinj : Function.Injective (f.rTensor ℚ) :=
    Module.Flat.rTensor_preserves_injective_linearMap f hf
  have hone : ((1 : ℤ) ⊗ₜ[ℤ] (1 : ℚ)) ≠ 0 := by
    intro hz
    have := congrArg (TensorProduct.lid ℤ ℚ) hz
    simp [TensorProduct.lid_tmul] at this
  have hzero : (f.rTensor ℚ) ((1 : ℤ) ⊗ₜ[ℤ] (1 : ℚ)) = 0 := by
    rw [LinearMap.rTensor_tmul, hf_apply]
    simp only [one_zsmul]
    exact Subsingleton.elim _ _
  exact hone (hinj (by rw [hzero, map_zero]))

theorem torsion_of_subsingleton_tensorRat_gen {A : Type*} [AddCommGroup A] {M : Module ℤ A}
    (h : @Subsingleton (@TensorProduct ℤ _ A ℚ _ _ M _)) (a : A) :
    ∃ n : ℕ, 0 < n ∧ n • a = 0 := by
  have hM : M = AddCommGroup.toIntModule A := Subsingleton.elim _ _
  rw [hM] at h
  exact torsion_of_subsingleton_tensorRat h a

theorem tensorRat_subsingleton_of_torsion_gen {A : Type*} [AddCommGroup A] {M : Module ℤ A}
    (h : ∀ a : A, ∃ n : ℕ, 0 < n ∧ n • a = 0) :
    @Subsingleton (@TensorProduct ℤ _ A ℚ _ _ M _) := by
  have hM : M = AddCommGroup.toIntModule A := Subsingleton.elim _ _
  rw [hM]
  exact tensorRat_subsingleton_of_torsion h

attribute [-instance] AddCommGroup.toIntModule

/-! ## 2. component tools for the Koszul tensor product -/

theorem tpX_sum_lof_gen (A B : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ)
    (z : Work.Kunneth.tpX A B n) :
    ∑ j : Work.Kunneth.tpIdx n, Work.Kunneth.tpLof A B n j (z j) = z := by
  apply DirectSum.ext
  intro k
  rw [← DirectSum.coeFnLinearMap_apply (R := ℤ)
    (v := ∑ j : Work.Kunneth.tpIdx n, Work.Kunneth.tpLof A B n j (z j))]
  rw [map_sum, Finset.sum_apply, Finset.sum_eq_single k]
  · simp only [DirectSum.coeFnLinearMap_apply, DirectSum.lof_apply]
  · intro j _ hj
    change DirectSum.component ℤ (Work.Kunneth.tpIdx n)
      (fun rs => Work.Kunneth.tpSummand A B rs.1.1 rs.1.2) k
        (DirectSum.lof ℤ (Work.Kunneth.tpIdx n)
          (fun rs => Work.Kunneth.tpSummand A B rs.1.1 rs.1.2) j (z j)) = 0
    rw [DirectSum.component.of]
    simp [hj]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

theorem tpX_eq_zero_of_forall_component (A B : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ)
    (z : Work.Kunneth.tpX A B n) (h : ∀ j, z j = 0) : z = 0 := by
  conv_lhs => rw [← tpX_sum_lof_gen A B n z]
  simp [h]

/-! ## 3. the two delegated inputs -/

/-- The component formula in the application form. -/
theorem tpMapLin_apply (C C' D D' : ChainComplex (ModuleCat ℤ) ℕ) (f : C ⟶ C') (g : D ⟶ D')
    (n : ℕ) (pq : Work.Kunneth.tpIdx n) (x : Work.Kunneth.tpX C D n) :
    (Work.Kunneth.tpMapLin C C' D D' f g n x) pq
      = TensorProduct.map (f.f pq.1.1).hom (g.f pq.1.2).hom (x pq) :=
  tpMapLin_component C C' D D' f g n pq x

/-! ## 4. the zero map -/

theorem tpMapLin_zero_right (C C' D D' : ChainComplex (ModuleCat ℤ) ℕ) (f : C ⟶ C') (n : ℕ) :
    Work.Kunneth.tpMapLin C C' D D' f (0 : D ⟶ D') n = 0 := by
  apply LinearMap.ext
  intro x
  apply tpX_eq_zero_of_forall_component
  intro pq
  rw [tpMapLin_apply, HomologicalComplex.zero_f, ModuleCat.hom_zero, TensorProduct.map_zero_right]
  simp

theorem tpMap_zero_right (C C' D D' : ChainComplex (ModuleCat ℤ) ℕ) (f : C ⟶ C') :
    Work.Kunneth.tpMap C C' D D' f (0 : D ⟶ D') = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [Work.Kunneth.tpMap_f, HomologicalComplex.zero_f]
  apply ModuleCat.hom_ext
  show Work.Kunneth.tpMapLin C C' D D' f (0 : D ⟶ D') n
    = (0 : (Work.Kunneth.tpX C D n) →ₗ[ℤ] (Work.Kunneth.tpX C' D' n))
  exact tpMapLin_zero_right C C' D D' f n

/-! ## 5. the degreewise algebraic facts -/

theorem tpMapLin_injective (C D' D : ChainComplex (ModuleCat ℤ) ℕ) (φ : D' ⟶ D)
    (hφ : Mono φ) (hC : ∀ i, Module.Free ℤ ↥(C.X i)) (n : ℕ) :
    Function.Injective (Work.Kunneth.tpMapLin C C D' D (𝟙 C) φ n) := by
  haveI : Mono φ := hφ
  intro x y hxy
  have hker : ∀ z : Work.Kunneth.tpX C D' n,
      Work.Kunneth.tpMapLin C C D' D (𝟙 C) φ n z = 0 → z = 0 := by
    intro z hz
    apply tpX_eq_zero_of_forall_component
    intro pq
    have h2 := congrArg (DirectSum.component ℤ (Work.Kunneth.tpIdx n)
        (fun rs => Work.Kunneth.tpSummand C D rs.1.1 rs.1.2) pq) hz
    rw [map_zero, tpMapLin_component] at h2
    rw [HomologicalComplex.id_f, ModuleCat.hom_id] at h2
    haveI : Module.Free ℤ ↥(C.X pq.1.1) := hC pq.1.1
    haveI : Module.Flat ℤ ↥(C.X pq.1.1) := Module.Flat.of_free
    have hmono : Function.Injective ((φ.f pq.1.2).hom) :=
      (ModuleCat.mono_iff_injective _).mp (inferInstance : Mono (φ.f pq.1.2))
    have hinj : Function.Injective (TensorProduct.map
        (LinearMap.id : ↥(C.X pq.1.1) →ₗ[ℤ] ↥(C.X pq.1.1)) ((φ.f pq.1.2).hom)) := by
      have h := Module.Flat.lTensor_preserves_injective_linearMap
        (M := ↥(C.X pq.1.1)) (φ.f pq.1.2).hom hmono
      simpa only [LinearMap.lTensor_def] using h
    have h3 : DirectSum.component ℤ (Work.Kunneth.tpIdx n)
        (fun rs => Work.Kunneth.tpSummand C D' rs.1.1 rs.1.2) pq z = 0 :=
      hinj (by rw [h2, map_zero])
    exact h3
  have hsub : Work.Kunneth.tpMapLin C C D' D (𝟙 C) φ n (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  exact sub_eq_zero.mp (hker (x - y) hsub)

theorem tpMapLin_surjective (C D D' : ChainComplex (ModuleCat ℤ) ℕ) (φ : D' ⟶ D) (n : ℕ) :
    Function.Surjective
      (Work.Kunneth.tpMapLin C C D (CategoryTheory.Limits.cokernel φ) (𝟙 C)
        (CategoryTheory.Limits.cokernel.π φ) n) := by
  intro w
  have hsur : ∀ pq : Work.Kunneth.tpIdx n,
      ∃ y : Work.Kunneth.tpSummand C D pq.1.1 pq.1.2,
        LinearMap.lTensor ↥(C.X pq.1.1)
          (((CategoryTheory.Limits.cokernel.π φ).f pq.1.2).hom) y = w pq := by
    intro pq
    have hepi : Function.Surjective (((CategoryTheory.Limits.cokernel.π φ).f pq.1.2).hom) :=
      (ModuleCat.epi_iff_surjective _).mp inferInstance
    exact LinearMap.lTensor_surjective (↥(C.X pq.1.1)) hepi (w pq)
  choose y hy using hsur
  refine ⟨∑ pq : Work.Kunneth.tpIdx n, Work.Kunneth.tpLof C D n pq (y pq), ?_⟩
  rw [map_sum]
  rw [show (∑ pq : Work.Kunneth.tpIdx n,
        Work.Kunneth.tpMapLin C C D (CategoryTheory.Limits.cokernel φ) (𝟙 C)
          (CategoryTheory.Limits.cokernel.π φ) n (Work.Kunneth.tpLof C D n pq (y pq)))
      = ∑ pq : Work.Kunneth.tpIdx n,
          Work.Kunneth.tpLof C (CategoryTheory.Limits.cokernel φ) n pq (w pq) from by
    apply Finset.sum_congr rfl
    intro pq _
    rw [Work.Kunneth.tpMapLin_tpLof]
    congr 1
    simpa only [LinearMap.lTensor_def, HomologicalComplex.id_f, ModuleCat.hom_id] using hy pq]
  exact tpX_sum_lof_gen C (CategoryTheory.Limits.cokernel φ) n w

theorem cokernel_π_comp_apply {M N : ModuleCat ℤ} (f : M ⟶ N) (y : ↥M) :
    CategoryTheory.Limits.cokernel.π f ((ModuleCat.Hom.hom f) y) = 0 := by
  have h := congrArg ModuleCat.Hom.hom (CategoryTheory.Limits.cokernel.condition f)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
  have h2 := congrArg (fun (g : ↥M →ₗ[ℤ] ↥(CategoryTheory.Limits.cokernel f)) => g y) h
  simpa using h2

theorem hom_comp_cokernel_f (D' D : ChainComplex (ModuleCat ℤ) ℕ) (φ : D' ⟶ D) (q : ℕ) :
    (((CategoryTheory.Limits.cokernel.π φ).f q).hom).comp (((φ.f q).hom)) = 0 := by
  have h1 : (φ.f q) ≫ (CategoryTheory.Limits.cokernel.π φ).f q = 0 := by
    rw [← HomologicalComplex.comp_f, CategoryTheory.Limits.cokernel.condition]
    rfl
  have h2 := congrArg ModuleCat.Hom.hom h1
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_zero] using h2

theorem tpMapLin_range_eq_ker (C D' D : ChainComplex (ModuleCat ℤ) ℕ) (φ : D' ⟶ D) (n : ℕ) :
    LinearMap.range (Work.Kunneth.tpMapLin C C D' D (𝟙 C) φ n)
      = LinearMap.ker (Work.Kunneth.tpMapLin C C D (CategoryTheory.Limits.cokernel φ) (𝟙 C)
          (CategoryTheory.Limits.cokernel.π φ) n) := by
  apply le_antisymm
  · rintro w ⟨x, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply tpX_eq_zero_of_forall_component
    intro pq
    rw [tpMapLin_apply, tpMapLin_apply, HomologicalComplex.id_f, ModuleCat.hom_id]
    rw [← LinearMap.lTensor_def, ← LinearMap.lTensor_def]
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    rw [hom_comp_cokernel_f D' D φ pq.1.2, LinearMap.lTensor_def, TensorProduct.map_zero_right]
    simp
  · intro w hw
    rw [LinearMap.mem_ker] at hw
    have hmem : ∀ pq : Work.Kunneth.tpIdx n,
        w pq ∈ LinearMap.range (LinearMap.lTensor ↥(C.X pq.1.1) ((φ.f pq.1.2).hom)) := by
      intro pq
      have h1 : LinearMap.lTensor ↥(C.X pq.1.1)
          (((CategoryTheory.Limits.cokernel.π φ).f pq.1.2).hom) (w pq) = 0 := by
        have h2 := congrArg (DirectSum.component ℤ (Work.Kunneth.tpIdx n)
          (fun rs => Work.Kunneth.tpSummand C (CategoryTheory.Limits.cokernel φ) rs.1.1 rs.1.2) pq) hw
        rw [map_zero, tpMapLin_component] at h2
        rw [HomologicalComplex.id_f, ModuleCat.hom_id] at h2
        exact h2
      rw [(LinearMap.exact_iff.mp (exact_lTensor_cokernel D' D φ (C.X pq.1.1) pq.1.2)).symm]
      exact LinearMap.mem_ker.mpr h1
    choose y hy using hmem
    refine ⟨∑ pq : Work.Kunneth.tpIdx n, Work.Kunneth.tpLof C D' n pq (y pq), ?_⟩
    rw [map_sum]
    rw [show (∑ pq : Work.Kunneth.tpIdx n,
          Work.Kunneth.tpMapLin C C D' D (𝟙 C) φ n (Work.Kunneth.tpLof C D' n pq (y pq)))
        = ∑ pq : Work.Kunneth.tpIdx n, Work.Kunneth.tpLof C D n pq (w pq) from by
      apply Finset.sum_congr rfl
      intro pq _
      rw [Work.Kunneth.tpMapLin_tpLof]
      congr 1
      simpa only [LinearMap.lTensor_def, HomologicalComplex.id_f, ModuleCat.hom_id] using hy pq]
    exact tpX_sum_lof_gen C D n w

/-! ## 6. the short exact sequence of complexes -/

theorem tpMapSES_zero (C D' D : ChainComplex (ModuleCat ℤ) ℕ) (φ : D' ⟶ D) :
    Work.Kunneth.tpMap C C D' D (𝟙 C) φ ≫
      Work.Kunneth.tpMap C C D (CategoryTheory.Limits.cokernel φ) (𝟙 C)
        (CategoryTheory.Limits.cokernel.π φ) = 0 := by
  rw [Work.Kunneth.tpMap_comp, CategoryTheory.Limits.cokernel.condition, Category.comp_id]
  exact tpMap_zero_right C C D' (CategoryTheory.Limits.cokernel φ) (𝟙 C)

theorem tpMapSES_shortExact (C D' D : ChainComplex (ModuleCat ℤ) ℕ) (φ : D' ⟶ D)
    (hφ : Mono φ) (hC : ∀ i, Module.Free ℤ ↥(C.X i)) :
    (ShortComplex.mk (Work.Kunneth.tpMap C C D' D (𝟙 C) φ)
      (Work.Kunneth.tpMap C C D (CategoryTheory.Limits.cokernel φ) (𝟙 C)
        (CategoryTheory.Limits.cokernel.π φ)) (tpMapSES_zero C D' D φ)).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun q => ?_)
  apply ModuleCat.shortComplex_shortExact
  · rw [← ShortComplex.ShortExact.moduleCat_exact_iff_function_exact,
      ShortComplex.moduleCat_exact_iff_range_eq_ker]
    simp only [ShortComplex.map_f, ShortComplex.map_g, HomologicalComplex.eval_map,
      Work.Kunneth.tpMap_f, ModuleCat.hom_ofHom]
    exact tpMapLin_range_eq_ker C D' D φ q
  · simp only [ShortComplex.map_f, HomologicalComplex.eval_map, Work.Kunneth.tpMap_f,
      ModuleCat.hom_ofHom]
    exact tpMapLin_injective C D' D φ hφ hC q
  · simp only [ShortComplex.map_g, HomologicalComplex.eval_map, Work.Kunneth.tpMap_f,
      ModuleCat.hom_ofHom]
    exact tpMapLin_surjective C D D' φ q

theorem tpC_homologyMap_cokernel_subsingleton (C D D' : ChainComplex (ModuleCat ℤ) ℕ) (N : ℕ)
    (φ : D' ⟶ D) (hφ : CategoryTheory.Mono φ) (hC : ∀ i, Module.Free ℤ ↥(C.X i))
    (hquot : ∀ j, j ≤ N → Subsingleton (TensorProduct ℤ
        ↥((Work.Kunneth.tpC C (CategoryTheory.Limits.cokernel φ)).homology j) ℚ)) :
    ∀ n, n ≤ N → Subsingleton (TensorProduct ℤ
        ↥(CategoryTheory.Limits.cokernel
            (HomologicalComplex.homologyMap
              (Work.Kunneth.tpMap C C D' D (CategoryTheory.CategoryStruct.id C) φ) n)) ℚ) := by
  intro n hn
  have hS : (ShortComplex.mk (Work.Kunneth.tpMap C C D' D (𝟙 C) φ)
      (Work.Kunneth.tpMap C C D (CategoryTheory.Limits.cokernel φ) (𝟙 C)
        (CategoryTheory.Limits.cokernel.π φ)) (tpMapSES_zero C D' D φ)).ShortExact :=
    tpMapSES_shortExact C D' D φ hφ hC
  have hrange : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Kunneth.tpMap C C D' D (𝟙 C) φ) n)).range
      = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Kunneth.tpMap C C D (CategoryTheory.Limits.cokernel φ) (𝟙 C)
          (CategoryTheory.Limits.cokernel.π φ)) n)).ker :=
    ShortComplex.Exact.moduleCat_range_eq_ker (hS.homology_exact₂ n)
  have htors : ∀ b : ↥((Work.Kunneth.tpC C (CategoryTheory.Limits.cokernel φ)).homology n),
      ∃ m : ℕ, 0 < m ∧ m • b = 0 :=
    fun b => torsion_of_subsingleton_tensorRat_gen (hquot n hn) b
  apply tensorRat_subsingleton_of_torsion_gen
  intro a
  obtain ⟨x, hx⟩ := (ModuleCat.epi_iff_surjective (CategoryTheory.Limits.cokernel.π
    (HomologicalComplex.homologyMap (Work.Kunneth.tpMap C C D' D (𝟙 C) φ) n))).mp
      (inferInstance : Epi (CategoryTheory.Limits.cokernel.π
        (HomologicalComplex.homologyMap (Work.Kunneth.tpMap C C D' D (𝟙 C) φ) n))) a
  obtain ⟨m, hmpos, hm⟩ := htors (HomologicalComplex.homologyMap
    (Work.Kunneth.tpMap C C D (CategoryTheory.Limits.cokernel φ) (𝟙 C)
      (CategoryTheory.Limits.cokernel.π φ)) n x)
  refine ⟨m, hmpos, ?_⟩
  have hmem : m • x ∈ LinearMap.ker (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Kunneth.tpMap C C D (CategoryTheory.Limits.cokernel φ) (𝟙 C)
        (CategoryTheory.Limits.cokernel.π φ)) n)) := by
    apply LinearMap.mem_ker.mpr
    rw [map_nsmul, hm]
  rw [← hrange] at hmem
  obtain ⟨y, hy⟩ := hmem
  rw [← hx, ← map_nsmul, ← hy]
  exact cokernel_π_comp_apply _ y

end

end Work.Serre
