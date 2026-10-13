import Mathlib
import Submission.Work.DSG4b.LCF.Basic

namespace Work.DSG4b.LCF

open TensorProduct LinearMap

/-- Elementary step of the local criterion of flatness.

Let `(R, 𝔪)` be a local ring, `M` an `R`-module, `A ⊆ R` an ideal and `x ∈ R` with `x ∉ A` and
`𝔪 · x ⊆ A`.  If tensoring the inclusions `𝔪 ↪ R` and `A ⊔ (x) ↪ R` with `M` stays injective, then
so does tensoring `A ↪ R`.

Mathematically this is the statement that `Tor₁(M, R/𝔪) = Tor₁(M, R/(A + (x))) = 0` forces
`Tor₁(M, R/A) = 0`: from `𝔪 · x ⊆ A` and `x ∉ A` one gets `(A : x) = 𝔪`, hence the quotient
`(A + (x))/A ≅ R/𝔪`, and the long exact sequence of `0 → (A + (x))/A → R/A → R/(A + (x)) → 0`
does the rest.

Formally we avoid derived functors altogether: `B := A ⊔ (x)` is presented by
`0 → 𝔪 → R × A → B → 0`, `r ↦ (r, -rx)`, whose tensoring with `M` is right exact. -/
theorem injective_lTensor_of_sup_span {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M]
    [Module R M] (A : Ideal R) (x : R) (hxA : x ∉ A)
    (hmul : ∀ a ∈ IsLocalRing.maximalIdeal R, a * x ∈ A)
    (h𝔪 : Function.Injective (LinearMap.lTensor M (IsLocalRing.maximalIdeal R).subtype))
    (hinj : Function.Injective (LinearMap.lTensor M (Submodule.subtype (A ⊔ Ideal.span {x})))) :
    Function.Injective (LinearMap.lTensor M (Submodule.subtype A)) := by
  let B : Submodule R R := (A : Submodule R R) ⊔ (Ideal.span {x} : Submodule R R)
  have hinjB : Function.Injective (LinearMap.lTensor M (Submodule.subtype B)) := hinj
  have hxB : x ∈ B := Submodule.mem_sup_right (Ideal.mem_span_singleton_self x)
  -- Key point: `r * x ∈ A ↔ r ∈ 𝔪`, i.e. the annihilator `(A : x)` (which contains `𝔪` by `hmul`)
  -- is exactly `𝔪`, because `x ∉ A` and `𝔪` is maximal.
  have key : ∀ r : R, r * x ∈ A ↔ r ∈ IsLocalRing.maximalIdeal R := by
    intro r
    refine ⟨fun hr => ?_, fun hr => hmul r hr⟩
    by_contra hrm
    have hunit : IsUnit r := IsLocalRing.notMem_maximalIdeal.mp hrm
    obtain ⟨u, hu⟩ := hunit
    have hxA' : x ∈ A := by
      have h1 : (↑u⁻¹ : R) * (r * x) ∈ A := A.mul_mem_left _ hr
      rwa [← hu, ← mul_assoc, Units.inv_mul, one_mul] at h1
    exact hxA hxA'
  -- The map `𝔪 → A`, `r ↦ -rx`.
  let ha : IsLocalRing.maximalIdeal R →ₗ[R] R :=
    (LinearMap.mulRight R x).comp (IsLocalRing.maximalIdeal R).subtype
  have hA : ∀ m : IsLocalRing.maximalIdeal R, (-ha) m ∈ (A : Submodule R R) := by
    intro m
    rw [LinearMap.neg_apply]
    exact A.neg_mem (hmul (m : R) m.2)
  let fA : IsLocalRing.maximalIdeal R →ₗ[R] (A : Submodule R R) :=
    (-ha).codRestrict (A : Submodule R R) hA
  -- The map `R → B`, `r ↦ rx`.
  let g : R →ₗ[R] B :=
    { toFun := fun r => ⟨r * x, by simpa using B.smul_mem r hxB⟩
      map_add' := by intro a b; ext; simp [add_mul]
      map_smul' := by intro c a; ext; simp [mul_assoc] }
  let subAB : (A : Submodule R R) →ₗ[R] B := Submodule.inclusion le_sup_left
  -- The presentation `𝔪 → R × A → B → 0` of `B`.
  let f : IsLocalRing.maximalIdeal R →ₗ[R] R × (A : Submodule R R) :=
    (IsLocalRing.maximalIdeal R).subtype.prod fA
  let φ : R × (A : Submodule R R) →ₗ[R] B := g.coprod subAB
  have hfφ_apply : ∀ m : IsLocalRing.maximalIdeal R, φ (f m) = 0 := by
    intro m; ext
    simp only [φ, f, LinearMap.coprod_apply, LinearMap.prod_apply, Submodule.coe_zero]
    simp [g, fA, subAB, ha]
  have hfφ : Function.Exact ⇑f ⇑φ := by
    rw [LinearMap.exact_iff]
    apply le_antisymm
    · intro y hy
      rw [LinearMap.mem_ker] at hy
      obtain ⟨r, a⟩ := y
      rw [LinearMap.mem_range]
      have hsum : r * x + (a : R) = 0 := by
        have h := congrArg (fun z : B => (z : R)) hy
        simpa [φ, g, subAB, LinearMap.coprod_apply, f] using h
      have hAx : r * x = -(a : R) := by
        rw [eq_neg_iff_add_eq_zero]; exact hsum
      have hr : r ∈ IsLocalRing.maximalIdeal R :=
        (key r).mp (by rw [hAx]; exact A.neg_mem a.2)
      refine ⟨⟨r, hr⟩, ?_⟩
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        change -(r * x) = (a : R)
        rw [hAx, neg_neg]
    · intro y hy
      rw [LinearMap.mem_range] at hy
      obtain ⟨m, rfl⟩ := hy
      rw [LinearMap.mem_ker]
      exact hfφ_apply m
  have hφsurj : Function.Surjective φ := by
    intro b
    have hb : (b : R) ∈ (A : Submodule R R) ⊔ (Ideal.span {x} : Submodule R R) := b.2
    rw [Submodule.mem_sup] at hb
    obtain ⟨y, hy, z, hz, hyz⟩ := hb
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    refine ⟨(r, ⟨y, hy⟩), ?_⟩
    apply Subtype.ext
    show r * x + y = (b : R)
    rw [← hyz]; ring
  -- Right exactness of `M ⊗ -` applied to the presentation of `B`.
  have hexact : Function.Exact ⇑(lTensor M f) ⇑(lTensor M φ) := lTensor_exact M hfφ hφsurj
  have hker_eq : (lTensor M φ).ker = (lTensor M f).range := LinearMap.exact_iff.mp hexact
  have hmain : Function.Injective (LinearMap.lTensor M subAB) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro z hz
    rw [LinearMap.mem_ker] at hz
    let u : (A : Submodule R R) →ₗ[R] R × (A : Submodule R R) :=
      LinearMap.inr R R (A : Submodule R R)
    have hφu : φ ∘ₗ u = subAB := by simpa [φ, u] using LinearMap.coprod_inr g subAB
    have hzu : lTensor M φ (lTensor M u z) = 0 := by
      have h1 : lTensor M φ (lTensor M u z) = lTensor M subAB z := by
        rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hφu]
      rw [h1, hz]
    have hmem : lTensor M u z ∈ (lTensor M φ).ker := by
      rw [LinearMap.mem_ker]; exact hzu
    rw [hker_eq, LinearMap.mem_range] at hmem
    obtain ⟨w, hw⟩ := hmem
    have hw0 : w = 0 := by
      apply h𝔪
      have h2 : lTensor M (LinearMap.fst R R (A : Submodule R R)) (lTensor M f w)
          = lTensor M (IsLocalRing.maximalIdeal R).subtype w := by
        rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, LinearMap.fst_prod]
      have h3 : lTensor M (LinearMap.fst R R (A : Submodule R R)) (lTensor M u z) = 0 := by
        rw [show lTensor M (LinearMap.fst R R (A : Submodule R R)) (lTensor M u z)
            = lTensor M (LinearMap.fst R R (A : Submodule R R) ∘ₗ u) z by
              rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp],
            show u = LinearMap.inr R R (A : Submodule R R) from rfl,
            LinearMap.fst_comp_inr]
        simp
      rw [← h2, hw, h3, LinearMap.map_zero]
    have hz1 : lTensor M (LinearMap.snd R R (A : Submodule R R)) (lTensor M f w)
        = lTensor M fA w := by
      rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, LinearMap.snd_prod]
    have hz2 : lTensor M (LinearMap.snd R R (A : Submodule R R)) (lTensor M u z) = z := by
      rw [show lTensor M (LinearMap.snd R R (A : Submodule R R)) (lTensor M u z)
          = lTensor M (LinearMap.snd R R (A : Submodule R R) ∘ₗ u) z by
            rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp],
          show u = LinearMap.inr R R (A : Submodule R R) from rfl,
          LinearMap.snd_comp_inr, LinearMap.lTensor_id]
      rfl
    have hz0 : z = lTensor M fA w := by rw [← hz2, ← hw, hz1]
    rw [hz0, hw0]
    simp
  -- Finally `lTensor M A.subtype` is the composite `lTensor M B.subtype ∘ lTensor M subAB`.
  have hsubAR : Submodule.subtype (A : Submodule R R) = Submodule.subtype B ∘ₗ subAB := by
    ext a; rfl
  rw [hsubAR, LinearMap.lTensor_comp]
  exact hinjB.comp hmain

end Work.DSG4b.LCF
