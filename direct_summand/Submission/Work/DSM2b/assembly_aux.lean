import Mathlib
import Submission.Work.DSM2b.FlatSetup
import Submission.Work.DSM2b.limit_kernel_range

/-!
# Assembly for Bhatt's Proposition 4.1 (flat part)

This file reduces the flatness statement to three explicit inputs, which are proved separately:

* `hA`  : `B ⧸ π ^ n B` is flat over `R ⧸ π ^ n R` for every `n` (`Work.DSM2b.flat_mod_pow_base`);
* `hAR` : the elementwise Artin–Rees consequence, with a uniform shift `c`
          (`Work.DSM2b.exists_pow_sub_mem_ker`);
* `hsyz`: the mod-`π ^ n` syzygy statement (`Work.DSM2b.syzygy_mod_pow`).

The main content here is

* the "coordinate" statement `ker (linCombB a) ≤ spanBase (ker a)`, obtained by combining `hsyz`
  with the limit step `Work.DSM2b.mem_range_of_forall_sub_mem` and a presentation of `ker a`;
* the transfer to `LinearMap.lTensor B` and the flatness criterion
  `Module.Flat.iff_lTensor_injective`.
-/

namespace Work.DSM2b

universe u

open TensorProduct

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

/-! ## Coordinate preliminaries -/

/-- Membership in `I • ⊤` for a coordinate module is coordinatewise membership in `I`. -/
lemma mem_smul_top_fin_iff (I : Ideal B) {t : ℕ} (x : Fin t → B) :
    x ∈ I • (⊤ : Submodule B (Fin t → B)) ↔ ∀ i, x i ∈ I := by
  constructor
  · intro hx i
    have hle : I • (⊤ : Submodule B (Fin t → B)) ≤ Submodule.pi Set.univ (fun _ => I) := by
      rw [Submodule.smul_le]
      intro a ha m _ j
      simpa using Ideal.mul_mem_right (m j) I ha
    have h := hle hx
    rw [Submodule.mem_pi] at h
    exact h i (Set.mem_univ i)
  · intro hx
    rw [← sum_single_smul_eq x]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul (hx j) Submodule.mem_top

/-- `coordBase` on a standard basis vector: the corresponding column. -/
lemma coordBase_single {k m : ℕ} (g : (Fin k → R) →ₗ[R] (Fin m → R)) (j : Fin k) :
    coordBase (B := B) g (Pi.single j 1) = coeffMap (B := B) (g (Pi.single j 1)) := by
  ext i
  rw [coordBase_apply, coeffMap_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro l _ hlj
    rw [Pi.single_eq_of_ne hlj, mul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- The range of `coordBase g` is the `B`-span of the range of `g`. -/
lemma range_coordBase_eq_spanBase_range {k m : ℕ} (g : (Fin k → R) →ₗ[R] (Fin m → R)) :
    LinearMap.range (coordBase (B := B) g) = spanBase (B := B) (LinearMap.range g) := by
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, rfl⟩
    rw [spanBase, ← sum_single_smul_eq x, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_smul, coordBase_single]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g (Pi.single j 1), ⟨_, rfl⟩, rfl⟩)
  · rw [spanBase, Submodule.span_le]
    rintro y ⟨v, ⟨x, rfl⟩, rfl⟩
    exact ⟨coeffMap x, coordBase_coeffMap g x⟩

/-- The coordinate form `R ^ k → R ^ 1` of a linear form. -/
lemma pi_finOne_apply {l : ℕ} (a : (Fin l → R) →ₗ[R] R) (x : Fin l → R) :
    (LinearMap.pi (fun _ : Fin 1 => a)) x = fun _ => a x := by
  funext i
  rw [LinearMap.pi_apply]

lemma ker_pi_finOne {l : ℕ} (a : (Fin l → R) →ₗ[R] R) :
    LinearMap.ker (LinearMap.pi (fun _ : Fin 1 => a)) = LinearMap.ker a := by
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_ker, pi_finOne_apply]
  exact ⟨fun h => congrFun h 0, fun h => funext fun _ => h⟩

lemma coordBase_pi_finOne_apply {l : ℕ} (a : (Fin l → R) →ₗ[R] R) (u : Fin l → B) :
    coordBase (B := B) (LinearMap.pi (fun _ : Fin 1 => a)) u =
      fun _ => linCombB (B := B) (fun j => a (Pi.single j 1)) u := by
  funext i
  rw [coordBase_apply, linCombB_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [pi_finOne_apply]

/-- The tautological vanishing: `f` kills the kernel of `I.subtype ∘ f`. -/
lemma comp_subtype_ker_eq_zero {l : ℕ} (I : Submodule R R) (f : (Fin l → R) →ₗ[R] I) :
    f.comp (LinearMap.ker (I.subtype.comp f)).subtype = 0 := by
  ext s
  have hs : I.subtype (f (s : Fin l → R)) = (0 : R) := by
    simpa only [LinearMap.mem_ker, LinearMap.comp_apply] using s.2
  exact hs

/-! ## The main coordinate statement -/

section Assembly

variable (π : R) [IsNoetherianRing R]

/-- **Flatness of `R → B` from the three ingredients.** -/
theorem flat_of_flat_mod_base_aux
    (hBπ : IsSMulRegular B (algebraMap R B π))
    [IsAdicComplete (Ideal.span {algebraMap R B π}) B]
    (hA : ∀ n : ℕ, Module.Flat (R ⧸ Ideal.span {π ^ n})
      (B ⧸ (Ideal.span {π ^ n}).map (algebraMap R B)))
    (hAR : ∀ {k m : ℕ} (g : (Fin k → R) →ₗ[R] (Fin m → R)), ∃ c, ∀ n (x : Fin k → R),
      (∀ i, g x i ∈ Ideal.span {π} ^ n) →
        ∃ z : Fin k → R, x - π ^ (n - c) • z ∈ LinearMap.ker g)
    (hsyz : ∀ {k m : ℕ} (g : (Fin k → R) →ₗ[R] (Fin m → R)) (c : ℕ),
      (∀ n (x : Fin k → R), (∀ i, g x i ∈ Ideal.span {π} ^ n) →
        ∃ z : Fin k → R, x - π ^ (n - c) • z ∈ LinearMap.ker g) →
      (∀ n : ℕ, Module.Flat (R ⧸ Ideal.span {π ^ n})
        (B ⧸ (Ideal.span {π ^ n}).map (algebraMap R B))) →
      ∀ n {y : Fin k → B}, (∀ i, coordBase g y i ∈ Ideal.span {algebraMap R B π} ^ n) →
        ∃ w : Fin k → B, w ∈ spanBase (LinearMap.ker g) ∧
          ∀ i, (y - w) i ∈ Ideal.span {algebraMap R B π} ^ (n - c)) :
    Module.Flat R B := by
  -- (1) the coordinate statement
  have key : ∀ {l : ℕ} (a : (Fin l → R) →ₗ[R] R) {u : Fin l → B},
      linCombB (fun i => a (Pi.single i 1)) u = 0 → u ∈ spanBase (LinearMap.ker a) := by
    intro l a u hu
    -- a presentation of `ker a`
    haveI : Module.Finite R (LinearMap.ker a) := inferInstance
    obtain ⟨t, ρ₀, hρ₀⟩ := Module.Finite.exists_fin' R (LinearMap.ker a)
    set ρ : (Fin t → R) →ₗ[R] (Fin l → R) := (LinearMap.ker a).subtype.comp ρ₀ with hρdef
    have hρrange : LinearMap.range ρ = LinearMap.ker a := by
      rw [hρdef, LinearMap.range_comp, LinearMap.range_eq_top.mpr hρ₀, Submodule.map_top,
        Submodule.range_subtype]
    -- Artin–Rees constants
    obtain ⟨ca, hca⟩ := hAR (LinearMap.pi (fun _ : Fin 1 => a))
    obtain ⟨cρ, hcρ⟩ := hAR ρ
    -- the approximation property
    have happrox : ∀ N, ∃ z : Fin t → B, ∀ i, (u - coordBase ρ z) i ∈
        Ideal.span {algebraMap R B π} ^ N := by
      intro N
      have hcoord : ∀ i : Fin 1, coordBase (LinearMap.pi (fun _ : Fin 1 => a)) u i ∈
          Ideal.span {algebraMap R B π} ^ (N + ca) := by
        intro i
        rw [coordBase_pi_finOne_apply]
        simp [hu]
      obtain ⟨w, hw, hwmem⟩ :=
        hsyz (LinearMap.pi (fun _ : Fin 1 => a)) ca hca hA (N + ca) hcoord
      have hw' : w ∈ spanBase (LinearMap.ker a) := by
        rw [ker_pi_finOne] at hw
        exact hw
      rw [← hρrange, ← range_coordBase_eq_spanBase_range ρ] at hw'
      obtain ⟨z, hz⟩ := hw'
      refine ⟨z, fun i => ?_⟩
      have hwmem' : (u - w) i ∈ Ideal.span {algebraMap R B π} ^ N := by
        have h := hwmem i
        rwa [Nat.add_sub_cancel] at h
      rw [hz]
      exact hwmem'
    -- the limit step
    rw [← hρrange, ← range_coordBase_eq_spanBase_range ρ]
    refine mem_range_of_forall_sub_mem π (coordBase ρ) cρ ?_ u happrox
    intro N z hz
    obtain ⟨w, hw, hwmem⟩ := hsyz ρ cρ hcρ hA N hz
    exact ⟨w, spanBase_ker_le_ker_coordBase ρ hw, hwmem⟩
  -- (2) transfer to `LinearMap.lTensor`
  have keyl : ∀ {l : ℕ} (a : (Fin l → R) →ₗ[R] R),
      LinearMap.ker (LinearMap.lTensor B a) ≤
        LinearMap.range (LinearMap.lTensor B (LinearMap.ker a).subtype) := by
    intro l a x hx
    have hy0 : linCombB (fun i => a (Pi.single i 1))
        (TensorProduct.piScalarRight R B B (Fin l) x) = 0 := by
      have h := rid_lTensor_linComb_eq (R := R) (B := B)
        (w := fun i => a (Pi.single i 1)) x
      rw [linComb_apply_single a] at h
      rw [← h, LinearMap.mem_ker.mp hx]
      simp
    have hy : TensorProduct.piScalarRight R B B (Fin l) x ∈ spanBase (LinearMap.ker a) :=
      key a hy0
    obtain ⟨s, hs⟩ := exists_map_of_mem_spanBase' (B := B) (LinearMap.ker a) hy
    refine LinearMap.mem_range.mpr ⟨s, ?_⟩
    rw [LinearEquiv.symm_apply_apply] at hs
    exact hs
  -- (3) the flatness criterion
  rw [Module.Flat.iff_lTensor_injective]
  intro I hI
  haveI : Module.Finite R I := Module.Finite.iff_fg.mpr hI
  obtain ⟨l, f, hf⟩ := Module.Finite.exists_fin' R I
  set a : (Fin l → R) →ₗ[R] R := I.subtype.comp f with hadef
  have haeq : LinearMap.lTensor B a =
      (LinearMap.lTensor B I.subtype).comp (LinearMap.lTensor B f) := by
    rw [hadef, LinearMap.lTensor_comp]
  have hzf : f.comp (LinearMap.ker a).subtype = 0 := by
    rw [hadef]
    exact comp_subtype_ker_eq_zero I f
  intro x y hxy
  have hsub : (LinearMap.lTensor B I.subtype) (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨x', hx'⟩ : ∃ x', LinearMap.lTensor B f x' = x - y :=
    LinearMap.lTensor_surjective B hf (x - y)
  have hax : (LinearMap.lTensor B a) x' = 0 := by
    rw [haeq, LinearMap.comp_apply, hx', hsub]
  obtain ⟨s, hs⟩ := keyl a hax
  have hz : x - y = 0 := by
    rw [← hx', ← hs, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
      show f ∘ₗ (LinearMap.ker a).subtype = 0 from hzf]
    simp
  exact sub_eq_zero.mp hz

/-! ## Elementwise Artin–Rees -/

/-- **Elementwise Artin–Rees.**  There is a constant `c` such that any `x : R ^ k` whose image
`g x` is divisible by `π ^ n` coordinatewise agrees with `π ^ (n - c) • z` modulo `ker g`. -/
lemma exists_pow_sub_mem_ker_aux {R : Type u} [CommRing R] [IsNoetherianRing R] (π : R) {k m : ℕ}
    (g : (Fin k → R) →ₗ[R] (Fin m → R)) :
    ∃ c : ℕ, ∀ n (x : Fin k → R), (∀ i, g x i ∈ Ideal.span {π} ^ n) →
      ∃ z : Fin k → R, x - π ^ (n - c) • z ∈ LinearMap.ker g := by
  obtain ⟨c, hc⟩ :=
    Ideal.exists_pow_inf_eq_pow_smul (Ideal.span {π}) (M := Fin m → R) (LinearMap.range g)
  refine ⟨c, fun n x hx => ?_⟩
  have hxmem : g x ∈ ((Ideal.span {π}) ^ n • (⊤ : Submodule R (Fin m → R)) : Submodule R _) :=
    (mem_smul_top_fin_iff (I := (Ideal.span {π}) ^ n) (x := g x)).mpr hx
  have hxrange : g x ∈ LinearMap.range g := ⟨x, rfl⟩
  have hstep : ((Ideal.span {π}) ^ n • (⊤ : Submodule R (Fin m → R))) ⊓ LinearMap.range g ≤
      (Ideal.span {π}) ^ (n - c) • LinearMap.range g := by
    by_cases hn : c ≤ n
    · rw [hc n hn, Submodule.smul_le]
      intro a ha v hv
      exact Submodule.smul_mem_smul ha hv.2
    · rw [Nat.sub_eq_zero_of_le (le_of_lt (not_le.mp hn)), pow_zero, one_smul]
      exact inf_le_right
  have hmem : g x ∈ (Ideal.span {π} ^ (n - c) : Ideal R) • LinearMap.range g :=
    hstep ⟨hxmem, hxrange⟩
  have hsmul : (Ideal.span {π} ^ (n - c) : Ideal R) • LinearMap.range g ≤
      Submodule.map (LinearMap.lsmul R (Fin m → R) (π ^ (n - c))) (LinearMap.range g) := by
    rw [Submodule.smul_le]
    intro a ha v hv
    rw [Ideal.span_singleton_pow] at ha
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp ha
    refine ⟨r • v, Submodule.smul_mem _ _ hv, ?_⟩
    rw [LinearMap.lsmul_apply, ← mul_smul]
  obtain ⟨w, hw, hwe⟩ := hsmul hmem
  have hwe' : π ^ (n - c) • w = g x := by
    rw [← LinearMap.lsmul_apply]
    exact hwe
  have hw' : w ∈ LinearMap.range g := hw
  rw [LinearMap.mem_range] at hw'
  obtain ⟨z, rfl⟩ := hw'
  refine ⟨z, ?_⟩
  rw [LinearMap.sub_mem_ker_iff, map_smul, hwe']

end Assembly

end Work.DSM2b
