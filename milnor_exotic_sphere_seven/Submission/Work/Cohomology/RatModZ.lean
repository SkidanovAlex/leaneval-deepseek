import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `ℚ ⧸ ℤ` as an injective `ℤ`-module

This file provides the elementary divisible/injective statements about `ℚ` and `ℚ ⧸ ℤ` that are
used to compare integral and rational cohomology: both `ℚ` and `ℚ ⧸ ℤ` are injective `ℤ`-modules
(they are divisible), a fact proved here through Baer's criterion.

## Main definitions and results

* `Work.Cohomology.ratIntSub` — the subgroup `ℤ ⊆ ℚ` as a `ℤ`-submodule;
* `Work.Cohomology.qZ` — the quotient `ℚ ⧸ ℤ`;
* `Work.Cohomology.mem_ratIntSub` — `q ∈ ℤ ↔ ∃ z : ℤ, (z : ℚ) = q`;
* `Work.Cohomology.qZ_divisible` — `ℚ ⧸ ℤ` is divisible;
* `Work.Cohomology.injective_rat`, `Work.Cohomology.injective_qZ` — `ℚ` and `ℚ ⧸ ℤ` are
  injective `ℤ`-modules;
* `Work.Cohomology.intEquiv` — `ℤ ≃ₗ[ℤ] ↥ratIntSub`.
-/

namespace Work.Cohomology

noncomputable section

/-- The subgroup `ℤ ⊆ ℚ`, as a `ℤ`-submodule of `ℚ`. -/
abbrev ratIntSub : Submodule ℤ ℚ := Submodule.span ℤ ({(1 : ℚ)} : Set ℚ)

/-- The quotient `ℚ ⧸ ℤ`, as a `ℤ`-module. -/
abbrev qZ : Type := ℚ ⧸ ratIntSub

/-- The elements of `ratIntSub` are exactly the images of the integers. -/
lemma mem_ratIntSub {q : ℚ} : q ∈ ratIntSub ↔ ∃ z : ℤ, (z : ℚ) = q := by
  rw [ratIntSub, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨z, hz⟩; exact ⟨z, by simpa using hz⟩
  · rintro ⟨z, hz⟩; exact ⟨z, by simpa using hz⟩

/-- The quotient map `ℚ → ℚ ⧸ ℤ` sends `q` to `0` exactly on the integers. -/
lemma mkQ_qZ_eq_zero {q : ℚ} : (Submodule.mkQ ratIntSub q : qZ) = 0 ↔ q ∈ ratIntSub :=
  Submodule.Quotient.mk_eq_zero ratIntSub

/-- **`ℚ ⧸ ℤ` is divisible**: every element is divisible by every nonzero integer. -/
lemma qZ_divisible (y : qZ) (n : ℤ) (hn : n ≠ 0) : ∃ c : qZ, n • c = y := by
  obtain ⟨q, hq⟩ := Submodule.mkQ_surjective ratIntSub y
  refine ⟨Submodule.mkQ ratIntSub (q / n), ?_⟩
  rw [← hq, ← map_zsmul]
  congr 1
  rw [zsmul_eq_mul]
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  field_simp

/-- **Baer's criterion for `ℚ`**: `ℚ` is divisible, hence satisfies Baer's criterion over `ℤ`. -/
lemma baer_rat : Module.Baer ℤ ℚ := by
  intro I g
  obtain ⟨n, hn⟩ : ∃ n, I = Ideal.span {n} :=
    ⟨Submodule.IsPrincipal.generator I, (Submodule.IsPrincipal.span_singleton_generator I).symm⟩
  subst hn
  by_cases hn0 : n = 0
  · subst hn0
    refine ⟨0, ?_⟩
    intro x hx
    have hx0 : x = 0 := by simpa using hx
    subst hx0
    rw [show (⟨0, hx⟩ : Ideal.span ({0} : Set ℤ)) = 0 from Subtype.ext rfl]
    simp
  · refine ⟨LinearMap.toSpanSingleton ℤ ℚ
      (g ⟨n, Submodule.mem_span_singleton.mpr ⟨1, by simp⟩⟩ / n), ?_⟩
    intro x hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨c, hc⟩ := hx
    subst hc
    rw [LinearMap.toSpanSingleton_apply]
    have h1 : (⟨c • n, hx⟩ : Ideal.span ({n} : Set ℤ))
        = c • ⟨n, Submodule.mem_span_singleton.mpr ⟨1, by simp⟩⟩ := Subtype.ext rfl
    rw [h1, map_smul]
    simp only [zsmul_eq_mul]
    push_cast
    have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
    field_simp

/-- **Baer's criterion for `ℚ ⧸ ℤ`**. -/
lemma baer_qZ : Module.Baer ℤ qZ := by
  intro I g
  obtain ⟨n, hn⟩ : ∃ n, I = Ideal.span {n} :=
    ⟨Submodule.IsPrincipal.generator I, (Submodule.IsPrincipal.span_singleton_generator I).symm⟩
  subst hn
  by_cases hn0 : n = 0
  · subst hn0
    refine ⟨0, ?_⟩
    intro x hx
    have hx0 : x = 0 := by simpa using hx
    subst hx0
    rw [show (⟨0, hx⟩ : Ideal.span ({0} : Set ℤ)) = 0 from Subtype.ext rfl]
    simp
  · obtain ⟨c, hc⟩ : ∃ c : qZ,
        n • c = g ⟨n, Submodule.mem_span_singleton.mpr ⟨1, by simp⟩⟩ := by
      obtain ⟨q, hq⟩ := Submodule.mkQ_surjective ratIntSub
        (g ⟨n, Submodule.mem_span_singleton.mpr ⟨1, by simp⟩⟩)
      refine ⟨Submodule.mkQ ratIntSub (q / n), ?_⟩
      rw [← hq, ← map_zsmul]
      congr 1
      rw [zsmul_eq_mul]
      have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
      field_simp
    refine ⟨LinearMap.toSpanSingleton ℤ qZ c, ?_⟩
    intro x hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨m, hm⟩ := hx
    subst hm
    rw [LinearMap.toSpanSingleton_apply]
    have h1 : (⟨m • n, hx⟩ : Ideal.span ({n} : Set ℤ))
        = m • ⟨n, Submodule.mem_span_singleton.mpr ⟨1, by simp⟩⟩ := Subtype.ext rfl
    rw [h1, map_smul]
    have hmn : (m • n : ℤ) = m * n := by rw [zsmul_eq_mul, Int.cast_id]
    rw [hmn, mul_smul, hc]

/-- **`ℚ` is an injective `ℤ`-module.** -/
theorem injective_rat : Module.Injective ℤ ℚ := Module.Baer.injective baer_rat

/-- **`ℚ ⧸ ℤ` is an injective `ℤ`-module.** -/
theorem injective_qZ : Module.Injective ℤ qZ := Module.Baer.injective baer_qZ

/-- The integers, as a `ℤ`-submodule, are linearly equivalent to `ℤ ⊆ ℚ`. -/
noncomputable def intEquiv : ℤ ≃ₗ[ℤ] ↥ratIntSub :=
  LinearEquiv.ofBijective
    { toFun := fun z => ⟨(z : ℚ), mem_ratIntSub.mpr ⟨z, rfl⟩⟩
      map_add' := by intro a b; apply Subtype.ext; push_cast; ring
      map_smul' := by
        intro a b
        apply Subtype.ext
        show ((a * b : ℤ) : ℚ) = a • ((b : ℤ) : ℚ)
        rw [zsmul_eq_mul]
        push_cast
        ring }
    ⟨fun a b h => by
        have h2 : ((a : ℚ)) = (b : ℚ) := congrArg Subtype.val h
        exact_mod_cast h2,
      fun q => ⟨(mem_ratIntSub.mp q.2).choose, by
        apply Subtype.ext
        exact (mem_ratIntSub.mp q.2).choose_spec⟩⟩

end

end Work.Cohomology
