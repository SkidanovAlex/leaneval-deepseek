import Mathlib

/-!
# Auxiliary lemmas for the local criterion of flatness

Self-contained proofs of the tensor-computations used in
`Submission/Work/DSG4b/localCriterionOfFlatnessPrime.lean`.  They are stated in the same generality
as the corresponding lemmas of the `LCFPrime` subproject.
-/

namespace Work.DSG4b

open TensorProduct LinearMap

/-- The components of an element of `M ⊗[R] (P × Q)` under `TensorProduct.prodRight`
are obtained by tensoring with the two projections. -/
lemma prodRight_apply {R M P Q : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] (w : M ⊗[R] (P × Q)) :
    TensorProduct.prodRight R R M P Q w =
      (LinearMap.lTensor M (LinearMap.fst R P Q) w, LinearMap.lTensor M (LinearMap.snd R P Q) w) := by
  induction w using TensorProduct.inductionOn with
  | tmul m p => simp
  | add x y hx hy => simp only [map_add, hx, hy, Prod.mk_add_mk]

/-- **Descent step of the local criterion of flatness.**  Let `A` be an ideal of the local ring `R`
and `x ∈ R \ A` with `𝔪 x ⊆ A`.  If `M ⊗[R] 𝔪 → M ⊗[R] R` and `M ⊗[R] (A + Rx) → M ⊗[R] R` are
injective, then so is `M ⊗[R] A → M ⊗[R] R`.

Indeed `0 → 𝔪 → A × R → A + Rx → 0`, `r ↦ (-rx, r)`, `(a,r) ↦ a + rx`, is exact (here
`(A : x) = 𝔪` is used), so after tensoring with `M` the kernel of `M ⊗ (A + Rx) → M ⊗ R`
(which is zero) surjects onto the kernel of `M ⊗ A → M ⊗ (A + Rx)`; this identifies the latter
with the image of `M ⊗ 𝔪 → M ⊗ A`, which is injective because `M ⊗ 𝔪 → M ⊗ R` is. -/
theorem injective_lTensor_of_sup_span {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (A : Ideal R) (x : R) (hxA : x ∉ A)
    (hmul : ∀ a ∈ IsLocalRing.maximalIdeal R, a * x ∈ A)
    (h𝔪 : Function.Injective (LinearMap.lTensor M (Submodule.subtype (IsLocalRing.maximalIdeal R))))
    (hinj : Function.Injective (LinearMap.lTensor M (Submodule.subtype (A ⊔ Ideal.span {x})))) :
    Function.Injective (LinearMap.lTensor M (Submodule.subtype A)) := by
  -- `(A : x) = 𝔪`
  have key : ∀ r : R, r * x ∈ A → r ∈ IsLocalRing.maximalIdeal R := by
    intro r hr
    by_contra hmem
    obtain ⟨u, rfl⟩ := IsLocalRing.notMem_maximalIdeal.mp hmem
    have h : (↑u⁻¹ : R) * (↑u * x) ∈ A := A.mul_mem_left _ hr
    rw [← mul_assoc, Units.inv_mul, one_mul] at h
    exact hxA h
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro ξ hξ
  rw [LinearMap.mem_ker] at hξ
  set B : Ideal R := A ⊔ Ideal.span {x} with hBdef
  let F : IsLocalRing.maximalIdeal R →ₗ[R] R :=
    (LinearMap.mulRight R x).comp (Submodule.subtype _)
  have hFmem : ∀ r : IsLocalRing.maximalIdeal R, F r ∈ A := fun r => hmul r r.2
  let ftop : IsLocalRing.maximalIdeal R →ₗ[R] A := F.codRestrict A hFmem
  let f : IsLocalRing.maximalIdeal R →ₗ[R] A × R := (-ftop).prod (Submodule.subtype _)
  let G : A × R →ₗ[R] R := (Submodule.subtype A).comp (LinearMap.fst R A R) +
    (LinearMap.mulRight R x).comp (LinearMap.snd R A R)
  have hGmem : ∀ p : A × R, G p ∈ B := by
    intro p
    refine B.add_mem (Ideal.mem_sup_left p.1.2) (Ideal.mem_sup_right ?_)
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self x)
  let g : A × R →ₗ[R] B := G.codRestrict B hGmem
  have hgval : ∀ p : A × R, ((g p : B) : R) = (p.1 : R) + p.2 * x := fun p => rfl
  have hf1 : ∀ r : IsLocalRing.maximalIdeal R, ((f r).1 : R) = -((r : R) * x) := fun r => rfl
  have hf2 : ∀ r : IsLocalRing.maximalIdeal R, (f r).2 = (r : R) := fun r => rfl
  have hfg : Function.Exact f g := by
    rw [LinearMap.exact_iff]
    refine le_antisymm ?_ ?_
    · intro p hp
      have hp0 : ((p.1 : R) + p.2 * x) = 0 := by
        have h : g p = 0 := hp
        have h2 := congrArg (fun z : B => (z : R)) h
        rwa [hgval p] at h2
      have hneg : p.2 * x = -(p.1 : R) := eq_neg_of_add_eq_zero_right hp0
      have hrmem : p.2 * x ∈ A := by rw [hneg]; exact A.neg_mem p.1.2
      refine ⟨⟨p.2, key p.2 hrmem⟩, ?_⟩
      refine Prod.ext ?_ ?_
      · refine Subtype.ext ?_
        rw [hf1, hneg]
        simp
      · rw [hf2]
    · intro p hp
      obtain ⟨r, hr⟩ := LinearMap.mem_range.mp hp
      rw [← hr]
      show g (f r) = 0
      refine Subtype.ext ?_
      rw [hgval, hf1 r, hf2 r]
      simp
  have hgsurj : Function.Surjective g := by
    intro b
    have hb : (b : R) ∈ A ⊔ Ideal.span {x} := b.2
    rw [Submodule.mem_sup] at hb
    obtain ⟨a, ha, c, hc, hac⟩ := hb
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hc
    refine ⟨(⟨a, ha⟩, r), ?_⟩
    refine Subtype.ext ?_
    rw [hgval]
    show a + r * x = ↑b
    rw [← hac, hr, mul_comm]
  -- the element of `M ⊗ (A × R)` with components `(ξ, 0)`
  let ζ : M ⊗[R] (A × R) := (TensorProduct.prodRight R R M A R).symm (ξ, 0)
  have hζ : TensorProduct.prodRight R R M A R ζ = (ξ, 0) :=
    (TensorProduct.prodRight R R M A R).apply_symm_apply (ξ, 0)
  have h1 : LinearMap.lTensor M (LinearMap.fst R A R) ζ = ξ := by
    have := prodRight_apply ζ
    rw [hζ] at this
    simpa using (Prod.ext_iff.mp this).1.symm
  have h2 : LinearMap.lTensor M (LinearMap.snd R A R) ζ = 0 := by
    have := prodRight_apply ζ
    rw [hζ] at this
    simpa using (Prod.ext_iff.mp this).2.symm
  have hgz : LinearMap.lTensor M g ζ = 0 := by
    apply hinj
    have hdecomp : Submodule.subtype B ∘ₗ g = G := rfl
    have hGsum : G = (Submodule.subtype A).comp (LinearMap.fst R A R) +
        (LinearMap.mulRight R x).comp (LinearMap.snd R A R) := rfl
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hdecomp, hGsum,
      LinearMap.lTensor_add, LinearMap.add_apply, LinearMap.lTensor_comp, LinearMap.lTensor_comp,
      LinearMap.comp_apply, LinearMap.comp_apply, h1, h2, hξ]
    simp
  -- exactness of the tensor sequence identifies the kernel with the image of `M ⊗ 𝔪 → M ⊗ A`
  have hex := LinearMap.exact_iff.mp (lTensor_exact M hfg hgsurj)
  have hmem : ζ ∈ LinearMap.range (LinearMap.lTensor M f) := by
    rw [← hex]
    exact hgz
  obtain ⟨η, hη⟩ := hmem
  have hfst : LinearMap.lTensor M (LinearMap.fst R A R ∘ₗ f) η = ξ := by
    rw [LinearMap.lTensor_comp, LinearMap.comp_apply, hη]; exact h1
  have hsnd : LinearMap.lTensor M (LinearMap.snd R A R ∘ₗ f) η = 0 := by
    rw [LinearMap.lTensor_comp, LinearMap.comp_apply, hη]; exact h2
  have hsnd_eq : LinearMap.snd R A R ∘ₗ f =
      Submodule.subtype (IsLocalRing.maximalIdeal R) := by
    ext r; rfl
  have hη0 : η = 0 := by
    refine h𝔪 ?_
    rw [← hsnd_eq, hsnd, map_zero]
  rw [← hfst, hη0, map_zero]

/-- The image of `M ⊗[R] (J ^ n * I) → M ⊗[R] I` is contained in `J ^ n • ⊤`: on simple tensors
`m ⊗ (j * i)` the image is `j • (m ⊗ i)`. -/
theorem map_lTensor_mul_le_smul_top {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (J I : Ideal R) (n : ℕ) :
    Submodule.map (LinearMap.lTensor M (Submodule.inclusion (Ideal.mul_le_right : J ^ n * I ≤ I))) ⊤ ≤
      J ^ n • (⊤ : Submodule R (TensorProduct R M I)) := by
  -- the set of `z ∈ R` for which the statement holds is an ideal, and contains `J ^ n * I`
  let P : Submodule R R :=
    { carrier := {z : R | ∃ hz : z ∈ I, ∀ m : M,
        (m ⊗ₜ[R] (⟨z, hz⟩ : ↥I)) ∈ J ^ n • (⊤ : Submodule R (M ⊗[R] ↥I))}
      zero_mem' := ⟨I.zero_mem, fun m => by
        rw [show (⟨0, I.zero_mem⟩ : ↥I) = 0 from Subtype.ext rfl, TensorProduct.tmul_zero]
        exact Submodule.zero_mem _⟩
      add_mem' := fun {a b} ⟨ha, hha⟩ ⟨hb, hhb⟩ => ⟨I.add_mem ha hb, fun m => by
        have h1 : (⟨a + b, I.add_mem ha hb⟩ : ↥I) = ⟨a, ha⟩ + ⟨b, hb⟩ := Subtype.ext rfl
        rw [h1, TensorProduct.tmul_add]
        exact Submodule.add_mem _ (hha m) (hhb m)⟩
      smul_mem' := fun r {a} ⟨ha, hha⟩ => ⟨I.smul_mem r ha, fun m => by
        have h1 : (⟨r • a, I.smul_mem r ha⟩ : ↥I) = r • (⟨a, ha⟩ : ↥I) := Subtype.ext rfl
        rw [h1, TensorProduct.tmul_smul]
        exact Submodule.smul_mem _ r (hha m)⟩ }
  have hP : J ^ n * I ≤ P := Submodule.mul_le.mpr (fun j hj i hi =>
    ⟨Ideal.mul_le_right (Ideal.mul_mem_mul hj hi), fun m => by
      have h1 : (⟨j * i, Ideal.mul_le_right (Ideal.mul_mem_mul hj hi)⟩ : ↥I) =
          j • (⟨i, hi⟩ : ↥I) := Subtype.ext rfl
      rw [h1, TensorProduct.tmul_smul]
      exact Submodule.smul_mem_smul hj trivial⟩)
  have key : ∀ x : M ⊗[R] ↥(J ^ n * I),
      LinearMap.lTensor M (Submodule.inclusion (Ideal.mul_le_right : J ^ n * I ≤ I)) x ∈
        J ^ n • (⊤ : Submodule R (M ⊗[R] ↥I)) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul m y =>
        obtain ⟨hz, hst⟩ := hP y.2
        have hy : (Submodule.inclusion (Ideal.mul_le_right : J ^ n * I ≤ I)) y =
            (⟨(y : R), hz⟩ : ↥I) := Subtype.ext rfl
        rw [LinearMap.lTensor_tmul, hy]
        exact hst m
    | add x y hx hy =>
        rw [map_add]
        exact Submodule.add_mem _ hx hy
  rw [Submodule.map_le_iff_le_comap]
  intro x _
  exact key x

/-- If `M` is a finite `S`-module and `I` is an ideal of the Noetherian ring `R`, then `M ⊗[R] I`
is a finite `S`-module: pick generators `s i` of `I` over `R`, then `M ⊗[R] I` is a quotient of
`(Fin n → M)`. -/
theorem moduleFinite_tensorProduct_ideal {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] [IsNoetherianRing R]
    [Module.Finite S M] (I : Ideal R) : Module.Finite S (TensorProduct R M I) := by
  have hnoeth : IsNoetherian R R := isNoetherianRing_iff.mp ‹IsNoetherianRing R›
  obtain ⟨n, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian I)
  have hsI : ∀ i, s i ∈ I := fun i => hs ▸ Submodule.subset_span (Set.mem_range_self i)
  let e : Fin n → ↥I := fun i => ⟨s i, hsI i⟩
  let ψ : (Fin n → M) →ₗ[S] M ⊗[R] ↥I :=
    { toFun := fun v => ∑ i, v i ⊗ₜ[R] e i
      map_add' := by
        intro v w
        simp only [Pi.add_apply, TensorProduct.add_tmul, Finset.sum_add_distrib]
      map_smul' := by
        intro c v
        simp only [Pi.smul_apply, RingHom.id_apply]
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← TensorProduct.smul_tmul'] }
  refine Module.Finite.of_surjective ψ ?_
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul m y =>
      have hyI : (y : R) ∈ Submodule.span R (Set.range s) := by rw [hs]; exact y.2
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hyI
      refine ⟨fun i => c i • m, ?_⟩
      show (∑ i, (c i • m) ⊗ₜ[R] e i) = m ⊗ₜ[R] y
      have hy : (∑ i, c i • e i) = y := Subtype.ext (by simpa using hc)
      rw [← hy, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [TensorProduct.smul_tmul]
  | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, ha, hb]⟩

/-- **Tensor chase for the general case of the local criterion of flatness.**  If
`M ⊗[R] (I ⊔ J) → M ⊗[R] R` is injective and `ξ ∈ M ⊗[R] I` is killed by `M ⊗[R] I → M ⊗[R] R`,
then `ξ` lies in the image of `M ⊗[R] (I ⊓ J) → M ⊗[R] I`.

Indeed `0 → I ⊓ J → I × J → I + J → 0`, `z ↦ (z,z)`, `(a,b) ↦ a - b`, is exact, and
`lTensor M (I ⊓ J → I) = lTensor M (fst ∘ f)`. -/
theorem mem_range_lTensor_inf_of_lTensor_eq_zero {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (I J : Ideal R)
    (hinj : Function.Injective (LinearMap.lTensor M (Submodule.subtype (I ⊔ J))))
    (ξ : TensorProduct R M I) (hξ : LinearMap.lTensor M (Submodule.subtype I) ξ = 0) :
    ξ ∈ LinearMap.range (LinearMap.lTensor M (Submodule.inclusion (inf_le_left : I ⊓ J ≤ I))) := by
  set B : Ideal R := I ⊔ J with hBdef
  let f : ↥(I ⊓ J) →ₗ[R] ↥I × ↥J :=
    (Submodule.inclusion (inf_le_left : I ⊓ J ≤ I)).prod
      (Submodule.inclusion (inf_le_right : I ⊓ J ≤ J))
  let G : ↥I × ↥J →ₗ[R] R := (Submodule.subtype I).comp (LinearMap.fst R ↥I ↥J) -
    (Submodule.subtype J).comp (LinearMap.snd R ↥I ↥J)
  have hGmem : ∀ p : ↥I × ↥J, G p ∈ B := by
    intro p
    exact B.sub_mem (Ideal.mem_sup_left p.1.2) (Ideal.mem_sup_right p.2.2)
  let g : ↥I × ↥J →ₗ[R] B := G.codRestrict B hGmem
  have hgval : ∀ p : ↥I × ↥J, ((g p : B) : R) = (p.1 : R) - p.2 := fun p => rfl
  have hf1 : ∀ z : ↥(I ⊓ J), ((f z).1 : R) = (z : R) := fun z => rfl
  have hf2 : ∀ z : ↥(I ⊓ J), ((f z).2 : R) = (z : R) := fun z => rfl
  have hfg : Function.Exact f g := by
    rw [LinearMap.exact_iff]
    refine le_antisymm ?_ ?_
    · intro p hp
      have hp0 : ((p.1 : R) - p.2) = 0 := by
        have h : g p = 0 := hp
        have h2 := congrArg (fun z : B => (z : R)) h
        rwa [hgval p] at h2
      have heq : (p.1 : R) = (p.2 : R) := sub_eq_zero.mp hp0
      refine ⟨⟨(p.1 : R), p.1.2, heq ▸ p.2.2⟩, ?_⟩
      refine Prod.ext ?_ ?_
      · refine Subtype.ext ?_
        rw [hf1]
      · refine Subtype.ext ?_
        rw [hf2, heq]
    · intro p hp
      obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hp
      rw [← hz]
      show g (f z) = 0
      refine Subtype.ext ?_
      rw [hgval, hf1 z, hf2 z]
      simp
  have hgsurj : Function.Surjective g := by
    intro b
    have hb : (b : R) ∈ I ⊔ J := b.2
    rw [Submodule.mem_sup] at hb
    obtain ⟨a, ha, c, hc, hac⟩ := hb
    refine ⟨(⟨a, ha⟩, ⟨-c, J.neg_mem hc⟩), ?_⟩
    refine Subtype.ext ?_
    rw [hgval]
    show a - -c = ↑b
    rw [sub_neg_eq_add]
    exact hac
  let ζ : M ⊗[R] (↥I × ↥J) := (TensorProduct.prodRight R R M ↥I ↥J).symm (ξ, 0)
  have hζ : TensorProduct.prodRight R R M ↥I ↥J ζ = (ξ, 0) :=
    (TensorProduct.prodRight R R M ↥I ↥J).apply_symm_apply (ξ, 0)
  have h1 : LinearMap.lTensor M (LinearMap.fst R ↥I ↥J) ζ = ξ := by
    have := prodRight_apply ζ
    rw [hζ] at this
    simpa using (Prod.ext_iff.mp this).1.symm
  have h2 : LinearMap.lTensor M (LinearMap.snd R ↥I ↥J) ζ = 0 := by
    have := prodRight_apply ζ
    rw [hζ] at this
    simpa using (Prod.ext_iff.mp this).2.symm
  have hgz : LinearMap.lTensor M g ζ = 0 := by
    apply hinj
    have hdecomp : Submodule.subtype B ∘ₗ g = G := rfl
    have hGsum : G = (Submodule.subtype I).comp (LinearMap.fst R ↥I ↥J) -
        (Submodule.subtype J).comp (LinearMap.snd R ↥I ↥J) := rfl
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hdecomp, hGsum,
      LinearMap.lTensor_sub, LinearMap.sub_apply, LinearMap.lTensor_comp, LinearMap.lTensor_comp,
      LinearMap.comp_apply, LinearMap.comp_apply, h1, h2, hξ]
    simp
  have hex := LinearMap.exact_iff.mp (lTensor_exact M hfg hgsurj)
  have hmem : ζ ∈ LinearMap.range (LinearMap.lTensor M f) := by
    rw [← hex]
    exact hgz
  obtain ⟨η, hη⟩ := hmem
  have hfst : LinearMap.lTensor M (LinearMap.fst R ↥I ↥J ∘ₗ f) η = ξ := by
    rw [LinearMap.lTensor_comp, LinearMap.comp_apply, hη]; exact h1
  have hfsteq : LinearMap.fst R ↥I ↥J ∘ₗ f = Submodule.inclusion (inf_le_left : I ⊓ J ≤ I) := by
    ext z; rfl
  rw [hfsteq] at hfst
  exact ⟨η, hfst⟩

end Work.DSG4b
