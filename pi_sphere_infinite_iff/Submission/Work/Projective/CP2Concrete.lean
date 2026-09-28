import Mathlib
import Submission.Work.Projective.CP2Homology
import Submission.Work.SignatureBordism.Numbers

/-!
# `ℂP²` in the cochain model: the hyperplane class, the fundamental class and the numbers

This module attaches the cohomology and homology of the *concrete* manifold `ℂP²` — computed by
Mayer–Vietoris in `Submission/Work/Projective/CP2Cohomology.lean` and `CP2Homology.lean` — to the
cochain model of `Submission/Work/SignatureBordism/`:

* `Work.Projective.cp2SSet` — the `SSet` model `TopCat.toSSet (TopCat.of (CP 2))` of `ℂP²`;
* `Work.Projective.cp2H ∈ H²(ℂP²;ℤ)` — the hyperplane class, spanning `H²` (`cp2H_span`), obtained
  from the Mayer–Vietoris isomorphism `singularCohomology_two_cp2`;
* `Work.Projective.cp2C ∈ H₄(ℂP²;ℤ)` — the fundamental class, spanning `H₄` (`cp2C_span`),
  obtained from `singularHomology_four_cp2`;
* `Work.Projective.cp2P1 = 3 · (h ⌣ h)` — the first Pontryagin class of `TℂP²` (from
  `p₁ = c₁² - 2c₂` and `c₁ = 3h`, `c₂ = 3h²`, cf. `Work.Projective.pClass1_eq_two`);
* `Work.Projective.cp2SelfIntersection = ⟨h ⌣ h, [ℂP²]⟩` — the middle self-intersection, the one
  piece of *geometric* input (Poincaré duality for the closed oriented `4`-manifold `ℂP²`: it is
  `±1`, in particular nonzero), with the **generator check**
  `Work.Projective.cp2_hirzebruchFour`: `⟨p₁(TℂP²), [ℂP²]⟩ = 3 σ(ℂP²)`.

The companion file `Submission/Work/Projective/CP2Cohomology.lean` proves
`H²(ℂP²;ℤ) ≅ ℤ` and `H⁴(ℂP²;ℤ) ≅ ℤ`, and `CP2Homology.lean` proves `H₄(ℂP²;ℤ) ≅ ℤ`; together with
the named self-intersection input these are exactly the hypotheses of the interface
`Work.Projective.CP2Model` of `Submission/Work/Projective/Interface.lean`.
-/

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace Work.Projective

open CategoryTheory Limits Work.Cohomology Work.SignatureBordism

noncomputable section

/-- The simplicial-set model of the manifold `ℂP²` used throughout the workspace's cochain
chapter: the singular simplicial set of the topological space `ℂP²`. -/
abbrev cp2SSet : SSet := TopCat.toSSet.obj (CPSpace 2)

/-- The chosen isomorphism `H²(ℂP²;ℤ) ≅ ℤ` (Mayer–Vietoris). -/
noncomputable def cp2CohIso :
    (cochainC ℤ cp2SSet).homology 2 ≅ ModuleCat.of ℤ ℤ :=
  Classical.choice singularCohomology_two_cp2

/-- **The hyperplane class `h ∈ H²(ℂP²;ℤ)`** — the image of `1` under the Mayer–Vietoris
isomorphism; it generates `H²(ℂP²;ℤ) ≅ ℤ`. -/
noncomputable def cp2H : (cochainC ℤ cp2SSet).homology 2 := cp2CohIso.inv (1 : ℤ)

/-- The chosen isomorphism `H₄(ℂP²;ℤ) ≅ ℤ` (Mayer–Vietoris). -/
noncomputable def cp2HomIso :
    (chainC ℤ cp2SSet).homology 4 ≅ ModuleCat.of ℤ ℤ :=
  Classical.choice singularHomology_four_cp2

/-- **The fundamental class `[ℂP²] ∈ H₄(ℂP²;ℤ)`** — the image of `1` under the Mayer–Vietoris
isomorphism; it generates `H₄(ℂP²;ℤ) ≅ ℤ`. -/
noncomputable def cp2C : (chainC ℤ cp2SSet).homology 4 := cp2HomIso.inv (1 : ℤ)

/-- A `ℤ`-module is spanned by a single element iff every element is an integer multiple of it.
(The same statement as `Work.Cohomology.span_singleton_eq_top_iff`, restated here so that this
module keeps its light imports; `int_smul_eq_zsmul` identifies the two `ℤ`-scalar
multiplications.) -/
lemma span_singleton_eq_top_iff' {M : Type*} [AddCommGroup M] [Module ℤ M] (x : M) :
    Submodule.span ℤ {x} = ⊤ ↔ ∀ z : M, ∃ a : ℤ, z = a • x := by
  have bridge : ∀ (a : ℤ), (LinearMap.toSpanSingleton ℤ M x) a = (a • x : M) := by
    intro a
    rw [LinearMap.toSpanSingleton_apply]
    exact int_smul_eq_zsmul (inferInstance : Module ℤ M) a x
  constructor
  · intro h z
    have hmem : z ∈ Submodule.span ℤ {x} := by rw [h]; trivial
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    have ha' : (LinearMap.toSpanSingleton ℤ M x) a = z := by
      rw [LinearMap.toSpanSingleton_apply]; exact ha
    exact ⟨a, by rw [← ha', bridge]⟩
  · intro h
    rw [Submodule.eq_top_iff']
    intro z
    obtain ⟨a, ha⟩ := h z
    rw [ha, ← bridge a]
    exact Submodule.smul_mem _ a (Submodule.subset_span (Set.mem_singleton x))

/-- A surjective `ℤ`-linear map sends a generator to a generator. -/
lemma exists_smul_of_surjective' {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (f : M →ₗ[ℤ] N) (hf : Function.Surjective f) {x : M}
    (h : ∀ z : M, ∃ a : ℤ, z = a • x) : ∀ z : N, ∃ a : ℤ, z = a • (f x) := by
  intro z
  obtain ⟨w, rfl⟩ := hf z
  obtain ⟨a, ha⟩ := h w
  exact ⟨a, by rw [ha, map_zsmul]⟩

/-- An isomorphism `M ≅ ℤ` exhibits the preimage of `1` as a generator of `M`. -/
theorem span_singleton_eq_top_of_iso {M : ModuleCat ℤ} (e : M ≅ ModuleCat.of ℤ ℤ) :
    Submodule.span ℤ {e.inv (1 : ℤ)} = ⊤ := by
  rw [span_singleton_eq_top_iff']
  intro z
  exact exists_smul_of_surjective' (ModuleCat.Hom.hom e.inv)
    ((ModuleCat.epi_iff_surjective _).mp inferInstance) (fun v : ℤ => ⟨v, by simp⟩) z

/-- **`h` spans `H²(ℂP²;ℤ)`.** -/
theorem cp2H_span : Submodule.span ℤ {cp2H} = ⊤ :=
  span_singleton_eq_top_of_iso cp2CohIso

/-- **`[ℂP²]` spans `H₄(ℂP²;ℤ)`.** -/
theorem cp2C_span : Submodule.span ℤ {cp2C} = ⊤ :=
  span_singleton_eq_top_of_iso cp2HomIso

/-- **The first Pontryagin class of `TℂP²`**: `p₁ = 3 · (h ⌣ h)`, from `p₁ = c₁² - 2c₂` with
`c₁(TℂP²) = 3h` and `c₂ = 3h²` (cf. `Work.Projective.pClass1_eq_two`). -/
noncomputable def cp2P1 : (cochainC ℤ cp2SSet).homology 4 :=
  (3 : ℤ) • cupH' ℤ cp2SSet 2 2 cp2H cp2H

/-- **The middle self-intersection of `ℂP²`**, `⟨h ⌣ h, [ℂP²]⟩`: the self-intersection number of
the hyperplane class.  Poincaré duality for the closed oriented `4`-manifold `ℂP²` says that this
number is `±1` (it is the degree of the tautological line bundle), in particular nonzero; that
single geometric input is named here (`cp2SelfIntersection_ne_zero` is *not* proved in this
chapter, exactly as `Work.SignatureBordism.NumbersInSpan8` names its geometric input). -/
noncomputable def cp2SelfIntersection : ℤ :=
  interForm ℤ cp2SSet 2 2 cp2C cp2H cp2H

/-- **The `p₁`-number of `ℂP²`**: `⟨p₁(TℂP²), [ℂP²]⟩ = 3 · ⟨h ⌣ h, [ℂP²]⟩`. -/
theorem cp2_p1Number :
    p₁Number cp2SSet cp2C cp2P1 = 3 * cp2SelfIntersection := by
  rw [p₁Number, cp2P1, cp2SelfIntersection, map_zsmul, LinearMap.smul_apply, smul_eq_mul,
    interForm_apply]

/-- **The signature of `ℂP²`**: the middle cohomology `H²(ℂP²;ℤ) = ℤ⟨h⟩` is one-dimensional and
the intersection form is the `1 × 1` form `(⟨h ⌣ h, [ℂP²]⟩)`, so the signature is the sign of the
self-intersection. -/
theorem cp2_sigma (hm : cp2SelfIntersection ≠ 0) :
    sigma 2 cp2SSet cp2C = if 0 < cp2SelfIntersection then 1 else -1 :=
  sigma_of_span_singleton 2 cp2SSet cp2C cp2H cp2H_span (by
    rw [cp2SelfIntersection, interForm_apply]) hm

/-- **The signature of `ℂP²` is its middle self-intersection number** (which is `±1` by Poincaré
duality). -/
theorem cp2_sigma_eq (hm : cp2SelfIntersection = 1 ∨ cp2SelfIntersection = -1) :
    sigma 2 cp2SSet cp2C = cp2SelfIntersection := by
  rcases hm with h | h
  · rw [cp2_sigma (by rw [h]; norm_num), h,
      if_pos (by norm_num : (0 : ℤ) < 1)]
  · rw [cp2_sigma (by rw [h]; norm_num), h,
      if_neg (by norm_num : ¬((0 : ℤ) < -1))]

/-- **The generator check for `ℂP²`**: the first Pontryagin number of `ℂP²` is three times its
signature, `⟨p₁(TℂP²), [ℂP²]⟩ = 3 σ(ℂP²)` — the dimension-`4` Hirzebruch identity, for the numbers
computed from the manifold, modulo the single named geometric input that the middle
self-intersection is `±1` (Poincaré duality for the closed oriented `4`-manifold `ℂP²`). -/
theorem cp2_hirzebruchFour (hm : cp2SelfIntersection = 1 ∨ cp2SelfIntersection = -1) :
    HirzebruchFour (sigma 2 cp2SSet cp2C) (p₁Number cp2SSet cp2C cp2P1) := by
  rw [HirzebruchFour, cp2_p1Number, cp2_sigma_eq hm]

end

end Work.Projective
