/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area ZASS2: the vocabulary of the endgame (step Z6.6)

This file fixes the vocabulary used by `Work.ZASS2.zassEndgame` and by the lemmas
proved for it in the neighbouring files of `Work/ZASS2/`.

Given field coordinates `C : ZassCoords G X inf zero U` (Z6.0) we

* build the affine chart `coordsEquiv C : X ≃ ℙ C.E (Fin 2 → C.E)`, i.e. `Φ = ptEquiv ∘ Θ`;
* build the permutation `phiPerm C g` of `ℙ¹` induced by `g : G` (i.e. `Φ ∘ (g • ·) ∘ Φ⁻¹`)
  and its monoid homomorphism version `phiHom C : G →* Equiv.Perm (ℙ¹)`;
* record the action of `PSL(2, C.E)` on `ℙ¹` with its range `pslRange C` and the injectivity
  of `pslPermHom C : PSL(2, C.E) →* Equiv.Perm (ℙ¹)`;
* record the involution `swapOpt C s` of `Option C.E` induced by an element `s` interchanging
  `inf` and `zero`, together with its explicit form under the hypothesis
  `C.Θ (s • x) = some (c / y)` of Z6.5′;
* transport `ZassCoords` along a ring equivalence of the coefficient field
  (`transportCoords`), which is how `Work.ZASS2.zassEndgame` reaches `GaloisField p k`.

The mathematical content of the endgame itself (Z6.6) is in `Work.ZASS2.zassEndgame`.
-/
import Mathlib
import Submission.Work.ZASS2.zassCoord
import Submission.Work.PSL2.Basic
import Submission.Work.ZASS.bruhat_decomposition

open scoped MatrixGroups LinearAlgebra.Projectivization
open Matrix

namespace Work.ZASS2

open Work.GW2
open Work.Zassenhaus (borel pairStab)

variable {G X : Type} [Group G] [MulAction G X] {inf zero : X} {U : Subgroup G}

/-! ## The affine chart -/

/-- The affine chart of the coordinates `C`, as a bijection `X ≃ ℙ¹(C.E)`:
`Φ = ptEquiv ∘ Θ` (`∞ ↦ ∞`, `x ↦ [Θ x : 1]`). -/
noncomputable def coordsEquiv (C : ZassCoords G X inf zero U) :
    X ≃ ℙ C.E (Fin 2 → C.E) :=
  C.Θ.trans (ptEquiv C.E)

@[simp] theorem coordsEquiv_apply (C : ZassCoords G X inf zero U) (x : X) :
    coordsEquiv C x = ptEquiv C.E (C.Θ x) := rfl

@[simp] theorem coordsEquiv_inf (C : ZassCoords G X inf zero U) :
    coordsEquiv C inf = Work.PSL2.ptInf C.E := by
  rw [coordsEquiv_apply, C.Θ_inf, ptEquiv_none]

@[simp] theorem coordsEquiv_zero (C : ZassCoords G X inf zero U) :
    coordsEquiv C zero = Work.PSL2.ptZero C.E := by
  rw [coordsEquiv_apply, C.Θ_zero, ptEquiv_some, Work.PSL2.ptOf_zero]

/-- `coordsEquiv C` is injective (it is an equivalence); convenient in `simp` form. -/
theorem coordsEquiv_injective (C : ZassCoords G X inf zero U) :
    Function.Injective (coordsEquiv C) := (coordsEquiv C).injective

/-! ## The permutation of `ℙ¹` induced by `g : G` -/

/-- The permutation `Φ ∘ (g • ·) ∘ Φ⁻¹` of `ℙ¹` induced by `g : G`. -/
noncomputable def phiPerm (C : ZassCoords G X inf zero U) (g : G) :
    Equiv.Perm (ℙ C.E (Fin 2 → C.E)) where
  toFun y := coordsEquiv C (g • (coordsEquiv C).symm y)
  invFun y := coordsEquiv C (g⁻¹ • (coordsEquiv C).symm y)
  left_inv y := by simp [coordsEquiv]
  right_inv y := by simp [coordsEquiv]

@[simp] theorem phiPerm_apply (C : ZassCoords G X inf zero U) (g : G)
    (y : ℙ C.E (Fin 2 → C.E)) :
    phiPerm C g y = coordsEquiv C (g • (coordsEquiv C).symm y) := rfl

/-- On the image of `coordsEquiv`, `phiPerm C g` is the action of `g`. -/
theorem phiPerm_coordsEquiv (C : ZassCoords G X inf zero U) (g : G) (x : X) :
    phiPerm C g (coordsEquiv C x) = coordsEquiv C (g • x) := by
  rw [phiPerm_apply, Equiv.symm_apply_apply]

/-- `phiPerm` is a monoid homomorphism in `g`, as a plain function. -/
noncomputable def phiHom (C : ZassCoords G X inf zero U) :
    G →* Equiv.Perm (ℙ C.E (Fin 2 → C.E)) where
  toFun := phiPerm C
  map_one' := by
    ext y
    rw [phiPerm_apply, one_smul, Equiv.Perm.one_apply, Equiv.apply_symm_apply]
  map_mul' := fun g g' => by
    ext y
    rw [Equiv.Perm.mul_apply, phiPerm_apply, phiPerm_apply, phiPerm_apply, mul_smul,
      Equiv.symm_apply_apply]

@[simp] theorem phiHom_apply (C : ZassCoords G X inf zero U) (g : G) :
    phiHom C g = phiPerm C g := rfl

theorem phiPerm_one (C : ZassCoords G X inf zero U) : phiPerm C 1 = 1 :=
  map_one (phiHom C)

theorem phiPerm_mul (C : ZassCoords G X inf zero U) (g g' : G) :
    phiPerm C (g * g') = phiPerm C g * phiPerm C g' :=
  map_mul (phiHom C) g g'

/-! ## The action of `PSL(2, C.E)` and its range -/

/-- The action of `PSL(2, C.E)` on `ℙ¹(C.E)`, as a monoid homomorphism. -/
noncomputable def pslPermHom (C : ZassCoords G X inf zero U) :
    PSL(2, C.E) →* Equiv.Perm (ℙ C.E (Fin 2 → C.E)) :=
  MulAction.toPermHom (PSL(2, C.E)) (ℙ C.E (Fin 2 → C.E))

@[simp] theorem pslPermHom_apply (C : ZassCoords G X inf zero U) (p : PSL(2, C.E)) :
    pslPermHom C p = MulAction.toPerm p := rfl

/-- `PSL(2,C.E)` acts faithfully on `ℙ¹(C.E)` (Mathlib's
`Matrix.ProjectiveSpecialLinearGroup.toPermHom_injective`, transported to `toPermHom`). -/
theorem pslPermHom_injective (C : ZassCoords G X inf zero U) :
    Function.Injective (pslPermHom C) := by
  intro g h hgh
  exact FaithfulSMul.eq_of_smul_eq_smul (α := ℙ C.E (Fin 2 → C.E)) (m₁ := g) (m₂ := h)
    (fun y => by
      have hh := DFunLike.congr_fun hgh y
      simpa [pslPermHom, MulAction.toPermHom_apply, MulAction.toPerm_apply] using hh)

/-- The image of `PSL(2,C.E)` inside `Equiv.Perm (ℙ¹(C.E))`. -/
noncomputable def pslRange (C : ZassCoords G X inf zero U) :
    Subgroup (Equiv.Perm (ℙ C.E (Fin 2 → C.E))) :=
  (pslPermHom C).range

theorem mem_pslRange_iff (C : ZassCoords G X inf zero U)
    {q : Equiv.Perm (ℙ C.E (Fin 2 → C.E))} :
    q ∈ pslRange C ↔ ∃ p : PSL(2, C.E), pslPermHom C p = q := Iff.rfl

theorem phiPerm_mem_pslRange_iff (C : ZassCoords G X inf zero U) (g : G) :
    phiPerm C g ∈ pslRange C ↔ ∃ p : PSL(2, C.E), pslPermHom C p = phiPerm C g :=
  Iff.rfl

/-- If a `PSL(2,C.E)`-element acts on `X` exactly as `g` does, then `phiPerm C g` is its
image.  This is the form in which the three generating cases of Z6.6 are used. -/
theorem phiPerm_eq_pslPermHom (C : ZassCoords G X inf zero U) {g : G} {p : PSL(2, C.E)}
    (h : ∀ x : X, coordsEquiv C (g • x) = p • coordsEquiv C x) :
    phiPerm C g = pslPermHom C p := by
  ext y
  obtain ⟨x, rfl⟩ := (coordsEquiv C).surjective y
  rw [phiPerm_apply, Equiv.symm_apply_apply, h x, pslPermHom,
    MulAction.toPermHom_apply, MulAction.toPerm_apply]

/-! ## The involution of `Option C.E` induced by `s` -/

/-- The map `Option C.E → Option C.E` induced by `s` in the affine chart,
i.e. `Θ ∘ (s • ·) ∘ Θ⁻¹`. -/
noncomputable def swapOpt (C : ZassCoords G X inf zero U) (s : G) : Option C.E → Option C.E :=
  fun o => C.Θ (s • (C.Θ).symm o)

theorem swapOpt_apply (C : ZassCoords G X inf zero U) (s : G) (o : Option C.E) :
    swapOpt C s o = C.Θ (s • (C.Θ).symm o) := rfl

/-- On the image of `Θ`, `swapOpt C s` is the action of `s`. -/
theorem swapOpt_theta (C : ZassCoords G X inf zero U) (s : G) (x : X) :
    swapOpt C s (C.Θ x) = C.Θ (s • x) := by
  rw [swapOpt_apply, Equiv.symm_apply_apply]

theorem swapOpt_none (C : ZassCoords G X inf zero U) (s : G)
    (hsinf : s • inf = zero) : swapOpt C s none = some 0 := by
  have h1 : (C.Θ).symm none = inf := by
    rw [Equiv.symm_apply_eq, C.Θ_inf]
  rw [swapOpt_apply, h1, hsinf, C.Θ_zero]

theorem swapOpt_some_zero (C : ZassCoords G X inf zero U) (s : G)
    (hszero : s • zero = inf) : swapOpt C s (some 0) = none := by
  have h1 : (C.Θ).symm (some 0) = zero := by
    rw [Equiv.symm_apply_eq, C.Θ_zero]
  rw [swapOpt_apply, h1, hszero, C.Θ_inf]

theorem swapOpt_some_ne_zero (C : ZassCoords G X inf zero U) (s : G) {c : C.E}
    (hform : ∀ (x : X) (y : C.E), y ≠ 0 → C.Θ x = some y → C.Θ (s • x) = some (c / y))
    {y : C.E} (hy : y ≠ 0) : swapOpt C s (some y) = some (c / y) := by
  have h := hform ((C.Θ).symm (some y)) y hy (Equiv.apply_symm_apply C.Θ (some y))
  simpa [swapOpt_apply] using h

/-- Under `s • x = c / ·`, the induced map on the affine chart is an involution. -/
theorem swapOpt_involutive (C : ZassCoords G X inf zero U) (s : G) {c : C.E} (hc0 : c ≠ 0)
    (hform : ∀ (x : X) (y : C.E), y ≠ 0 → C.Θ x = some y → C.Θ (s • x) = some (c / y))
    (hsinf : s • inf = zero) (hszero : s • zero = inf) :
    Function.Involutive (swapOpt C s) := by
  intro o
  cases o with
  | none => rw [swapOpt_none C s hsinf, swapOpt_some_zero C s hszero]
  | some y =>
      by_cases hy : y = 0
      · subst hy
        rw [swapOpt_some_zero C s hszero, swapOpt_none C s hsinf]
      · have hy' : c / y ≠ 0 := div_ne_zero hc0 hy
        rw [swapOpt_some_ne_zero C s hform hy, swapOpt_some_ne_zero C s hform hy',
          div_div_eq_mul_div, mul_comm c y, mul_div_cancel_right₀ _ hc0]

/-- If the action of `G` on `X` is faithful, the hypothesis `s • x = c / Θ x` forces
`s * s = 1`. -/
theorem mul_self_eq_one_of_swapOpt (C : ZassCoords G X inf zero U) (s : G) [FaithfulSMul G X]
    {c : C.E} (hc0 : c ≠ 0)
    (hform : ∀ (x : X) (y : C.E), y ≠ 0 → C.Θ x = some y → C.Θ (s • x) = some (c / y))
    (hsinf : s • inf = zero) (hszero : s • zero = inf) : s * s = 1 := by
  refine FaithfulSMul.eq_of_smul_eq_smul (α := X) (m₁ := s * s) (m₂ := 1) (fun x => ?_)
  have h := swapOpt_involutive C s hc0 hform hsinf hszero (C.Θ x)
  rw [swapOpt_theta, swapOpt_theta] at h
  have h2 : C.Θ ((s * s) • x) = C.Θ x := by
    rw [mul_smul]; exact h
  have h3 : (s * s) • x = x := C.Θ.injective h2
  rw [h3, one_smul]

/-! ## The generated subgroup -/

/-- The Bruhat decomposition of Z6.1 exhibits `G` as generated by `U`, the two-point
stabilizer `G_{∞0}` and the involution `s`. -/
theorem closure_union_pairStab_singleton_eq_top (hdec : U ⊔ pairStab G inf zero = borel G inf)
    {s : G}
    (hbru : ∀ g : G, g ∈ borel G inf ∨
      ∃ q : (borel G inf) × U, g = (q.1 : G) * s * (q.2 : G)) :
    Subgroup.closure ((U : Set G) ∪ (pairStab G inf zero : Set G) ∪ {s}) = ⊤ := by
  set S : Set G := (U : Set G) ∪ (pairStab G inf zero : Set G) ∪ {s} with hS
  have hB : borel G inf ≤ Subgroup.closure S := by
    rw [← hdec]
    refine sup_le ?_ ?_
    · exact (Set.subset_union_left.trans Set.subset_union_left).trans Subgroup.subset_closure
    · exact (Set.subset_union_right.trans Set.subset_union_left).trans Subgroup.subset_closure
  rw [eq_top_iff]
  intro g _
  rcases hbru g with hg | ⟨q, hq⟩
  · exact hB hg
  · rw [hq]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (hB q.1.2) ?_) ?_
    · exact Subgroup.subset_closure (by simp [hS])
    · exact Subgroup.subset_closure (by simp [hS])

/-! ## Transporting coordinates along a ring equivalence of the field -/

/-- Transport `ZassCoords` along a ring equivalence `e : C.E ≃+* F` of the coefficient
fields.  `Θ` becomes `Option.map e ∘ Θ`, `τ` and `α` are postcomposed with `e`. -/
@[reducible] noncomputable def transportCoords (C : ZassCoords G X inf zero U) {F : Type}
    [Field F] [Fintype F] (e : C.E ≃+* F) : ZassCoords G X inf zero U where
  E := F
  Θ := C.Θ.trans (Equiv.optionCongr e)
  Θ_inf := by simp [Equiv.trans_apply, C.Θ_inf]
  Θ_zero := by simp [Equiv.trans_apply, C.Θ_zero, map_zero]
  τ := fun u => e (C.τ u)
  τ_bij := e.bijective.comp C.τ_bij
  trans := by
    intro u x
    show Equiv.optionCongr e (C.Θ ((u : G) • x)) =
      (Equiv.optionCongr e (C.Θ x)).map (fun t => t + e (C.τ u))
    rw [C.trans u x, Equiv.optionCongr_apply, Equiv.optionCongr_apply, Option.map_map]
    cases C.Θ x with
    | none => rfl
    | some a => simp [map_add]
  α := fun h => e (C.α h)
  scale := by
    intro h x
    show Equiv.optionCongr e (C.Θ ((h : G) • x)) =
      (Equiv.optionCongr e (C.Θ x)).map (fun t => e (C.α h) * t)
    rw [C.scale h x, Equiv.optionCongr_apply, Equiv.optionCongr_apply, Option.map_map]
    cases C.Θ x with
    | none => rfl
    | some a => simp [map_mul]
  α_range := by
    intro e₀ he₀
    constructor
    · rintro ⟨h, hh⟩
      have hα : C.α h ≠ 0 := fun h0 => he₀ (by rw [← hh, h0, map_zero])
      obtain ⟨d, hd⟩ := (C.α_range (C.α h) hα).mp ⟨h, rfl⟩
      exact ⟨e d, by rw [← hh, hd, map_mul]⟩
    · rintro ⟨r, hr⟩
      have hr0 : r ≠ 0 := fun h0 => he₀ (by rw [hr, h0, mul_zero])
      have hs0 : e.symm r ≠ 0 := fun h0 => hr0 ((RingEquiv.map_eq_zero_iff e.symm).mp h0)
      obtain ⟨h₀, hh₀⟩ := (C.α_range (e.symm r * e.symm r)
        (mul_ne_zero hs0 hs0)).mpr ⟨e.symm r, rfl⟩
      exact ⟨h₀, by simp only [hh₀, map_mul, RingEquiv.apply_symm_apply, hr]⟩

@[simp] theorem transportCoords_Θ (C : ZassCoords G X inf zero U) {F : Type} [Field F]
    [Fintype F] (e : C.E ≃+* F) (x : X) :
    (transportCoords C e).Θ x = Option.map e (C.Θ x) := rfl

@[simp] theorem transportCoords_τ (C : ZassCoords G X inf zero U) {F : Type} [Field F]
    [Fintype F] (e : C.E ≃+* F) (u : U) :
    (transportCoords C e).τ u = e (C.τ u) := rfl

@[simp] theorem transportCoords_α (C : ZassCoords G X inf zero U) {F : Type} [Field F]
    [Fintype F] (e : C.E ≃+* F) (h : pairStab G inf zero) :
    (transportCoords C e).α h = e (C.α h) := rfl

end Work.ZASS2
