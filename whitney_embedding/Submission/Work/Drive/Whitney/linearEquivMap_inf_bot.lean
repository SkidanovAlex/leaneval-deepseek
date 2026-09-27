import Mathlib

set_option maxHeartbeats 1000000

/-!
# A pointwise linear-algebra input for the design of the common-base correction

`Work.Drive.Whitney.exists_linearEquiv_map_inf_eq_bot_of_notMem`: for two `n`-planes `T`, `K` of
`ℝ^{2n}`, a nonzero `u ∈ T` and a vector `w ∉ K`, there is a linear equivalence `A` of `ℝ^{2n}` with
`A u = w` and `A T ⊓ K = ⊥`.  This is the pointwise core of the design in
`NOTES_commonBase_crux_S131.md` §8.2.2.
-/

namespace Work.Drive.Whitney

open scoped Manifold ContDiff
open Submodule

variable {n : ℕ}

/-- **The pinned `1`-dimensional isomorphism `ℝ ∙ u ≃ ℝ ∙ w`** (for nonzero `u`, `w`). -/
theorem span_equiv_span_of_ne_zero {M M' : Type*} [AddCommGroup M] [Module ℝ M]
    [AddCommGroup M'] [Module ℝ M'] {u : M} {w : M'}
    (hu : u ≠ 0) (hw : w ≠ 0) :
    ∃ e : (Submodule.span ℝ ({u} : Set M)) ≃ₗ[ℝ] (Submodule.span ℝ ({w} : Set M')),
      e ⟨u, Submodule.mem_span_singleton_self u⟩ = ⟨w, Submodule.mem_span_singleton_self w⟩ := by
  have hku : LinearMap.ker (LinearMap.toSpanSingleton ℝ M u) = ⊥ :=
    LinearMap.ker_toSpanSingleton ℝ hu
  have hkw : LinearMap.ker (LinearMap.toSpanSingleton ℝ M' w) = ⊥ :=
    LinearMap.ker_toSpanSingleton ℝ hw
  set ψu : ℝ ≃ₗ[ℝ] (Submodule.span ℝ ({u} : Set M)) :=
    (LinearEquiv.ofInjective (LinearMap.toSpanSingleton ℝ M u)
        (LinearMap.ker_eq_bot.mp hku)).trans
      (LinearEquiv.ofEq _ _ (LinearMap.range_toSpanSingleton u)) with hψu
  set ψw : ℝ ≃ₗ[ℝ] (Submodule.span ℝ ({w} : Set M')) :=
    (LinearEquiv.ofInjective (LinearMap.toSpanSingleton ℝ M' w)
        (LinearMap.ker_eq_bot.mp hkw)).trans
      (LinearEquiv.ofEq _ _ (LinearMap.range_toSpanSingleton w)) with hψw
  have h1u : ψu 1 = ⟨u, Submodule.mem_span_singleton_self u⟩ := by
    apply Subtype.ext
    simp [hψu, LinearMap.toSpanSingleton_apply_one]
  have h1w : ψw 1 = ⟨w, Submodule.mem_span_singleton_self w⟩ := by
    apply Subtype.ext
    simp [hψw, LinearMap.toSpanSingleton_apply_one]
  refine ⟨ψu.symm.trans ψw, ?_⟩
  rw [LinearEquiv.trans_apply, ← h1u, ← h1w, LinearEquiv.symm_apply_apply]

/-- **An `n`-plane through a vector, missing a given `n`-plane.** -/
theorem exists_compl_plane_through (K : Submodule ℝ (EuclideanSpace ℝ (Fin (2 * n))))
    (hK : Module.finrank ℝ K = n) {w : EuclideanSpace ℝ (Fin (2 * n))} (hw : w ∉ K) :
    ∃ S : Submodule ℝ (EuclideanSpace ℝ (Fin (2 * n))),
      Module.finrank ℝ S = n ∧ w ∈ S ∧ S ⊓ K = ⊥ := by
  classical
  have hw0 : w ≠ 0 := by rintro rfl; exact hw (Submodule.zero_mem K)
  have hE : Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * n))) = 2 * n := by
    rw [finrank_euclideanSpace, Fintype.card_fin]
  have hspan1 : Module.finrank ℝ (Submodule.span ℝ ({w} : Set (EuclideanSpace ℝ (Fin (2 * n))))) = 1 :=
    finrank_span_singleton hw0
  have hinf : K ⊓ Submodule.span ℝ ({w} : Set (EuclideanSpace ℝ (Fin (2 * n)))) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro x ⟨hxK, hxL⟩
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hxL
    rw [← ha] at hxK
    by_cases hza : a = 0
    · rw [← ha, hza, zero_smul]
    · have hwK : w ∈ K := by
        have h1 := inv_smul_smul₀ hza w
        rw [← h1]
        exact Submodule.smul_mem K a⁻¹ hxK
      exact absurd hwK hw
  obtain ⟨R, hR⟩ := Submodule.exists_isCompl
    (K ⊔ Submodule.span ℝ ({w} : Set (EuclideanSpace ℝ (Fin (2 * n)))))
  have hdisj : Submodule.span ℝ ({w} : Set (EuclideanSpace ℝ (Fin (2 * n)))) ⊓ R = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro x ⟨hxL, hxR⟩
    exact hR.disjoint.le_bot ⟨Submodule.mem_sup_right hxL, hxR⟩
  have htop : Submodule.span ℝ ({w} : Set (EuclideanSpace ℝ (Fin (2 * n)))) ⊔ R ⊔ K = ⊤ := by
    have h1 : (K ⊔ Submodule.span ℝ ({w} : Set (EuclideanSpace ℝ (Fin (2 * n))))) ⊔ R = ⊤ :=
      hR.sup_eq_top
    rw [← h1]
    ac_rfl
  have hmeet : (Submodule.span ℝ ({w} : Set (EuclideanSpace ℝ (Fin (2 * n)))) ⊔ R) ⊓ K = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro x ⟨hxS, hxK⟩
    obtain ⟨y, hy, r, hr, rfl⟩ := Submodule.mem_sup.mp hxS
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hy
    rw [← ha] at hxK ⊢
    have hrmem : r ∈ K ⊔ Submodule.span ℝ ({w} : Set (EuclideanSpace ℝ (Fin (2 * n)))) := by
      have h1 : a • w + r - a • w = r := by abel
      rw [← h1]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left hxK)
        (Submodule.mem_sup_right (Submodule.smul_mem _ a (Submodule.mem_span_singleton_self w)))
    have hr0 : r = 0 := hR.disjoint.le_bot ⟨hrmem, hr⟩
    rw [hr0, add_zero] at hxK ⊢
    by_cases hza : a = 0
    · rw [hza, zero_smul]
    · have hwK : w ∈ K := by
        have h1 := inv_smul_smul₀ hza w
        rw [← h1]
        exact Submodule.smul_mem K a⁻¹ hxK
      exact absurd hwK hw
  have hcompl : IsCompl (Submodule.span ℝ ({w} : Set (EuclideanSpace ℝ (Fin (2 * n)))) ⊔ R) K :=
    ⟨by rw [disjoint_iff_inf_le]; exact hmeet.le, by rw [codisjoint_iff_le_sup]; exact htop.ge⟩
  have hfin : Module.finrank ℝ
      ↥(Submodule.span ℝ ({w} : Set (EuclideanSpace ℝ (Fin (2 * n)))) ⊔ R) = n := by
    have h := Submodule.finrank_add_eq_of_isCompl hcompl
    rw [hK, hE] at h
    omega
  exact ⟨Submodule.span ℝ ({w} : Set (EuclideanSpace ℝ (Fin (2 * n)))) ⊔ R, hfin,
    Submodule.mem_sup_left (Submodule.mem_span_singleton_self w), hmeet⟩

/-- **A pinned isomorphism of submodules of equal finite dimension.**  For nonzero `u ∈ T`, `w ∈ S`
and `finrank T = finrank S`, there is an isomorphism `T ≃ₗ S` sending `u` to `w`.

Proof: take any isomorphism `e₁ : T ≃ S`, put `a := e₁ u`, `b := w`, and correct the pin by the
transvection `g := id + (b - a) ⊗ ψ` on `↥S`, where the functional `ψ` satisfies `ψ a = 1` and
`ψ b ≠ 0` (an explicit combination of inner-product functionals).  Then `g a = b`, and `g` is
invertible because `1 + ψ (b - a) = ψ b ≠ 0`. -/
theorem exists_linearEquiv_map_eq {T S : Submodule ℝ (EuclideanSpace ℝ (Fin (2 * n)))}
    {u w : EuclideanSpace ℝ (Fin (2 * n))} (hu : u ∈ T) (hwS : w ∈ S)
    (hu0 : u ≠ 0) (hw0 : w ≠ 0) (hTS : Module.finrank ℝ T = Module.finrank ℝ S) :
    ∃ e : ↥T ≃ₗ[ℝ] ↥S, e ⟨u, hu⟩ = ⟨w, hwS⟩ := by
  classical
  have huT : (⟨u, hu⟩ : ↥T) ≠ 0 := fun h => hu0 (congrArg Subtype.val h)
  have hb0 : (⟨w, hwS⟩ : ↥S) ≠ 0 := fun h => hw0 (congrArg Subtype.val h)
  let e₁ : ↥T ≃ₗ[ℝ] ↥S := LinearEquiv.ofFinrankEq ↥T ↥S hTS
  set a : ↥S := e₁ ⟨u, hu⟩ with ha
  set b : ↥S := ⟨w, hwS⟩ with hb
  have ha0 : a ≠ 0 := by
    intro h
    have h1 : (⟨u, hu⟩ : ↥T) = 0 := e₁.injective (by rw [← ha, map_zero]; exact h)
    exact huT h1
  -- the two building-block functionals
  let φa : ↥S →ₗ[ℝ] ℝ :=
    { toFun := fun x => inner ℝ a x
      map_add' := fun x y => inner_add_right a x y
      map_smul' := fun c x => by
        rw [inner_smul_right]
        rfl }
  let φb : ↥S →ₗ[ℝ] ℝ :=
    { toFun := fun x => inner ℝ b x
      map_add' := fun x y => inner_add_right b x y
      map_smul' := fun c x => by
        rw [inner_smul_right]
        rfl }
  have hφa_a : φa a = ‖a‖ ^ 2 := by
    show inner ℝ a a = ‖a‖ ^ 2
    exact real_inner_self_eq_norm_sq a
  have hφa_b : φa b = inner ℝ a b := rfl
  have hφb_b : φb b = ‖b‖ ^ 2 := by
    show inner ℝ b b = ‖b‖ ^ 2
    exact real_inner_self_eq_norm_sq b
  have hφb_a : φb a = inner ℝ a b := by
    show inner ℝ b a = inner ℝ a b
    exact real_inner_comm a b
  have hnza : (‖a‖ ^ 2)⁻¹ * ‖a‖ ^ 2 = 1 :=
    inv_mul_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr ha0))
  have hnzb : (‖b‖ ^ 2)⁻¹ * ‖b‖ ^ 2 = 1 :=
    inv_mul_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hb0))
  -- the functional with the two required properties
  have hex : ∃ ψ : ↥S →ₗ[ℝ] ℝ, ψ a = 1 ∧ ψ b ≠ 0 := by
    by_cases hcase : inner ℝ a b = 0
    · refine ⟨((‖a‖ ^ 2)⁻¹) • φa + ((‖b‖ ^ 2)⁻¹) • φb, ?_, ?_⟩
      · simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hφa_a, hφb_a,
          hcase, real_inner_comm, mul_zero, add_zero, hnza]
      · intro hzero
        have h1 : ((‖a‖ ^ 2)⁻¹) * φa b + ((‖b‖ ^ 2)⁻¹) * φb b = 0 := hzero
        rw [hφa_b, hφb_b, hcase, mul_zero, zero_add, hnzb] at h1
        exact one_ne_zero h1
    · refine ⟨((‖a‖ ^ 2)⁻¹) • φa, ?_, ?_⟩
      · simp only [LinearMap.smul_apply, smul_eq_mul, hφa_a, hnza]
      · intro hzero
        have h1 : ((‖a‖ ^ 2)⁻¹) * φa b = 0 := hzero
        rw [hφa_b] at h1
        exact hcase ((mul_eq_zero.mp h1).resolve_left
          (inv_ne_zero (pow_ne_zero 2 (norm_ne_zero_iff.mpr ha0))))
  obtain ⟨ψ, hψa, hψb⟩ := hex
  -- the transvection and its two properties
  let g : ↥S →ₗ[ℝ] ↥S :=
    LinearMap.id + (LinearMap.toSpanSingleton ℝ ↥S (b - a)).comp ψ
  have hga : g a = b := by
    show a + ψ a • (b - a) = b
    rw [hψa, one_smul]
    abel
  have hgker : LinearMap.ker g = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have h2 : x + ψ x • (b - a) = 0 := hx
    have h3 : ψ x + ψ x * (ψ b - 1) = 0 := by
      have := congrArg ψ h2
      rw [map_add, map_smul, map_sub, map_zero, hψa] at this
      exact this
    have hψx : ψ x = 0 := by
      have h4 : ψ x * ψ b = 0 := by nlinarith [h3]
      rcases mul_eq_zero.mp h4 with h | h
      · exact h
      · exact absurd h hψb
    rw [hψx, zero_smul, add_zero] at h2
    exact h2
  have hginj : Function.Injective g := LinearMap.ker_eq_bot.mp hgker
  have hgsurj : Function.Surjective g := by
    intro y
    refine ⟨y - (ψ y / ψ b) • (b - a), ?_⟩
    show y - (ψ y / ψ b) • (b - a) + ψ (y - (ψ y / ψ b) • (b - a)) • (b - a) = y
    have hψ : ψ (y - (ψ y / ψ b) • (b - a)) = ψ y / ψ b := by
      rw [map_sub, map_smul, map_sub, hψa, smul_eq_mul]
      field_simp
      ring
    rw [hψ]
    abel
  refine ⟨e₁.trans (LinearEquiv.ofBijective g ⟨hginj, hgsurj⟩), ?_⟩
  show g a = b
  exact hga

end Work.Drive.Whitney
