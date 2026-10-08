import Submission.Work.Clifford.CFun

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Clifford.Orbit`: the conjugation action of `G` on functions on a normal subgroup

For `N ⊴ G` the group `G` acts on the set of functions `N → ℂ` by `θ^g(x) = θ (g * x * g⁻¹)`
(`Work.Clifford.conjFun`).  This file develops the API of that action: it is additive and
`ℂ`-linear, it fixes class functions, the inertia group `I_G(θ) = inertia N θ` contains `N` when
`θ` is a class function, the orbit `charOrbit N θ = {θ^g : g ∈ G}` is `G`-stable, and the orbit
sum `orbitSum N θ` is a `G`-invariant class function on `N` — the object whose positive multiples
are the restrictions of the irreducible characters of `G` (Clifford's theorem).
-/

noncomputable section

set_option linter.unusedSectionVars false

open Classical

namespace Work.Clifford

universe u

variable {G : Type u} [Group G] [Fintype G]
variable {N : Subgroup G} [N.Normal]

/-! ### The action is additive and `ℂ`-linear -/

@[simp] theorem conjFun_zero (g : G) : conjFun N g (0 : N → ℂ) = 0 := by
  ext n; simp [conjFun]

@[simp] theorem conjFun_add (g : G) (f₁ f₂ : N → ℂ) :
    conjFun N g (f₁ + f₂) = conjFun N g f₁ + conjFun N g f₂ := by
  ext n; simp [conjFun]

@[simp] theorem conjFun_neg (g : G) (f : N → ℂ) : conjFun N g (-f) = -conjFun N g f := by
  ext n; simp [conjFun]

@[simp] theorem conjFun_sub (g : G) (f₁ f₂ : N → ℂ) :
    conjFun N g (f₁ - f₂) = conjFun N g f₁ - conjFun N g f₂ := by
  ext n; simp [conjFun]

@[simp] theorem conjFun_smul (g : G) (c : ℂ) (f : N → ℂ) :
    conjFun N g (c • f) = c • conjFun N g f := by
  ext n; simp [conjFun]

theorem conjFun_sum {ι : Type*} (g : G) (s : Finset ι) (F : ι → N → ℂ) :
    conjFun N g (∑ i ∈ s, F i) = ∑ i ∈ s, conjFun N g (F i) := by
  ext n
  simp only [conjFun, Finset.sum_apply]

/-- Conjugation by an element of `N` fixes class functions on `N`. -/
theorem conjFun_eq_self_of_isClassFun {f : N → ℂ} (hf : IsClassFun f) {g : G} (hg : g ∈ N) :
    conjFun N g f = f := by
  ext n
  exact hf n ⟨g, hg⟩

/-- The inertia group of a class function contains the subgroup. -/
theorem le_inertia {θ : N → ℂ} (hθ : IsClassFun θ) : N ≤ inertia N θ := by
  intro n hn
  rw [mem_inertia]
  exact conjFun_eq_self_of_isClassFun hθ hn

/-- The inertia group of an irreducible character contains the subgroup. -/
theorem le_inertia_of_mem_Irr {θ : N → ℂ} (hθ : θ ∈ Irr N) : N ≤ inertia N θ :=
  le_inertia (IsClassFun.of_mem_Irr hθ)

/-! ### The orbit and its sum -/

theorem mem_charOrbit {θ φ : N → ℂ} :
    φ ∈ charOrbit N θ ↔ ∃ g : G, conjFun N g θ = φ := by
  simp only [charOrbit, Finset.mem_image, Finset.mem_univ, true_and]

theorem conjFun_mem_charOrbit (θ : N → ℂ) (g : G) : conjFun N g θ ∈ charOrbit N θ :=
  mem_charOrbit.mpr ⟨g, rfl⟩

@[simp] theorem theta_mem_charOrbit (θ : N → ℂ) : θ ∈ charOrbit N θ := by
  simpa using conjFun_mem_charOrbit θ 1

theorem charOrbit_nonempty (θ : N → ℂ) : (charOrbit N θ).Nonempty :=
  ⟨θ, theta_mem_charOrbit θ⟩

/-- The orbit of a conjugate of `θ` is the orbit of `θ`. -/
theorem charOrbit_conjFun (g : G) (θ : N → ℂ) :
    charOrbit N (conjFun N g θ) = charOrbit N θ := by
  have h2 : (Finset.univ.image fun h : G => g * h) = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]
    intro x
    exact Finset.mem_image.mpr ⟨g⁻¹ * x, Finset.mem_univ _, by group⟩
  simp only [charOrbit]
  have h1 : (fun h : G => conjFun N h (conjFun N g θ)) =
      (fun h : G => conjFun N h θ) ∘ fun h : G => g * h := by
    funext h
    simp only [Function.comp_apply]
    rw [conjFun_mul]
  rw [h1, ← Finset.image_image, h2]

theorem charOrbit_eq_of_mem {θ φ : N → ℂ} (h : φ ∈ charOrbit N θ) :
    charOrbit N φ = charOrbit N θ := by
  obtain ⟨g, rfl⟩ := mem_charOrbit.mp h
  exact charOrbit_conjFun g θ

theorem conjFun_mem_charOrbit_of_mem {θ φ : N → ℂ} (h : φ ∈ charOrbit N θ) (g : G) :
    conjFun N g φ ∈ charOrbit N θ := by
  rw [← charOrbit_eq_of_mem h]
  exact conjFun_mem_charOrbit φ g

/-- The orbit sum is invariant under conjugation by `G`. -/
theorem conjFun_orbitSum (g : G) (θ : N → ℂ) : conjFun N g (orbitSum N θ) = orbitSum N θ := by
  ext n
  simp only [orbitSum, conjFun]
  exact Finset.sum_nbij' (conjFun N g) (conjFun N g⁻¹)
    (fun φ hφ => conjFun_mem_charOrbit_of_mem hφ g)
    (fun φ hφ => conjFun_mem_charOrbit_of_mem hφ g⁻¹)
    (fun φ _ => by simp)
    (fun φ _ => by simp)
    (fun φ _ => rfl)

/-- The orbit sum is always a class function on `N`. -/
theorem isClassFun_orbitSum (θ : N → ℂ) : IsClassFun (orbitSum N θ) := by
  intro x y
  show orbitSum N θ (y * x * y⁻¹) = orbitSum N θ x
  simp only [orbitSum]
  refine Finset.sum_nbij' (conjFun N (y : G)) (conjFun N (y : G)⁻¹)
    (fun φ hφ => conjFun_mem_charOrbit_of_mem hφ (y : G))
    (fun φ hφ => conjFun_mem_charOrbit_of_mem hφ (y : G)⁻¹)
    (fun φ _ => by simp) (fun φ _ => by simp) (fun φ _ => rfl)

end Work.Clifford
