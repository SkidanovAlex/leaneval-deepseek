import Mathlib
import Submission.Work.Pi6.EMM2.K4Kit
import Submission.Work.Pi6.EMM2.SSKit
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-!
# Area EMM2 / K4F: the transgression of the class of `H³` of the fibre

For the mod-2 Serre spectral sequence `S` of a fibration `p` with fibre `F` and base `B` such that
`H⁰(B)` and `H³(F)` are one-dimensional, `H²(B) = H³(B) = H¹(F) = H²(F) = 0` and `H³(E) = 0`, the
differential `d₄ : E₄^{0,3} → E₄^{4,0}` is nonzero on some element.

The argument is purely on the pages: the class `x = e₂⁻¹(1 ⊗ f)` (`f ≠ 0` a generator of `H³(F)`,
`1` the unit of `H⁰(B)`) is nonzero on `E₂^{0,3}`; nothing maps into `(0,3)` (the sources
`(-2,4)`, `(-3,3)`, `(-4,6)` of the incoming differentials lie in negative bidegrees) and the two
outgoing targets `(2,2)` and `(3,1)` vanish (`H²(B) = H²(F) = 0`, `H³(B) = H¹(F) = 0`), so `x`
survives to a nonzero class `u` of `E₄^{0,3}`.  Finally `H³(E) = 0` gives `E₅^{0,3} = 0`, and since
nothing maps into `(0,3)`, the projection `ker d₄ → E₅^{0,3}` is injective; hence `d₄ u ≠ 0`.
-/

namespace Work.Pi6.EMM2.K4F

open CategoryTheory CategoryTheory.Limits

/-- Two-step survival: a nonzero class of `E₂^a` whose outgoing differentials on the pages `2` and
`3` land in vanishing groups, and whose incoming sources on those pages vanish, is nonzero on
`E₄^a`. -/
theorem exists_ne_zero_page_four {𝕜 : Type} [Field 𝕜] (S : CohSS 𝕜) (a : ℤ × ℤ)
    (ht2 : IsZero (S.E 2 (a + vr 2))) (ht3 : IsZero (S.E 3 (a + vr 3)))
    (hs2 : IsZero (S.E 2 (a - vr 2))) (hs3 : IsZero (S.E 3 (a - vr 3)))
    (x : S.E 2 a) (hx : x ≠ 0) : ∃ y : S.E 4 a, y ≠ 0 :=
  ⟨S.nextClass 3 a ht3 (S.nextClass 2 a ht2 x),
   (S.nextClass_ne_zero_iff 3 (by norm_num) a ht3 hs3 _).mpr
     ((S.nextClass_ne_zero_iff 2 (by norm_num) a ht2 hs2 x).mpr hx)⟩

theorem transgression {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (e₀ : E)
    (N : ℕ) (S : Work.Pi6.CohSS (ZMod 2)) (hS : Work.Pi6.IsSerreMSS S p e₀ N) (hN : 8 ≤ N)
    (hB0 : Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) B 0) = 1)
    (hF3 : Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) (Work.Pi6.EMM2.Fib p e₀) 3) = 1)
    (hB2 : CategoryTheory.Limits.IsZero (Work.Pi6.Coh (ZMod 2) B 2))
    (hB3 : CategoryTheory.Limits.IsZero (Work.Pi6.Coh (ZMod 2) B 3))
    (hF1 : CategoryTheory.Limits.IsZero (Work.Pi6.Coh (ZMod 2) (Work.Pi6.EMM2.Fib p e₀) 1))
    (hF2 : CategoryTheory.Limits.IsZero (Work.Pi6.Coh (ZMod 2) (Work.Pi6.EMM2.Fib p e₀) 2))
    (hE3 : CategoryTheory.Limits.IsZero (Work.Pi6.Coh (ZMod 2) E 3)) :
    ∃ u : S.E 4 ((0 : ℤ), (3 : ℤ)),
      (S.d 4 ((0 : ℤ), (3 : ℤ)) (((0 : ℤ), (3 : ℤ)) + Work.Pi6.vr 4)).hom u ≠ 0 := by
  have hS' := hS
  obtain ⟨e2, -, hvanish, -, -, -⟩ := hS'
  -- a nonzero class of `H³(F)` and the unit of `H⁰(B)`
  obtain ⟨f, hf⟩ := k4_exists_ne_zero (𝕜 := ZMod 2) hF3
  have hone : one (ZMod 2) B ≠ 0 := k4_one_ne_zero (𝕜 := ZMod 2) hB0
  have hx0 : (e2 0 3 (by omega) (by omega)).inv.hom
      (one (ZMod 2) B ⊗ₜ[ZMod 2] f) ≠ 0 :=
    k4_e2_inv_tmul_ne_zero (p := p) (e₀ := e₀) S (e2 0 3 (by omega) (by omega)) hone hf
  -- the two outgoing targets of `(0,3)` on pages `2` and `3` vanish
  have ht2 : IsZero (S.E 2 (((0 : ℤ), (3 : ℤ)) + Work.Pi6.vr 2)) := by
    rw [show (((0 : ℤ), (3 : ℤ)) + Work.Pi6.vr 2) = ((2 : ℤ), (2 : ℤ)) by
      ext <;> norm_num [Work.Pi6.vr]]
    exact k4_isZero_E2_left p e₀ S N hS (s := 2) (q := 2) (by omega) (by omega) hB2
  have ht3 : IsZero (S.E 3 (((0 : ℤ), (3 : ℤ)) + Work.Pi6.vr 3)) := by
    rw [show (((0 : ℤ), (3 : ℤ)) + Work.Pi6.vr 3) = ((3 : ℤ), (1 : ℤ)) by
      ext <;> norm_num [Work.Pi6.vr]]
    exact S.isZero_succ (r := 2) (by norm_num) ((3 : ℤ), (1 : ℤ))
      (k4_isZero_E2_left p e₀ S N hS (s := 3) (q := 1) (by omega) (by omega) hB3)
  -- nothing maps into `(0,3)` on pages `2` and `3`
  have hs2 : IsZero (S.E 2 (((0 : ℤ), (3 : ℤ)) - Work.Pi6.vr 2)) := by
    rw [show (((0 : ℤ), (3 : ℤ)) - Work.Pi6.vr 2) = ((-2 : ℤ), (4 : ℤ)) by
      ext <;> norm_num [Work.Pi6.vr]]
    exact S.isZero_quad 2 ((-2 : ℤ), (4 : ℤ)) (Or.inl (by norm_num))
  have hs3 : IsZero (S.E 3 (((0 : ℤ), (3 : ℤ)) - Work.Pi6.vr 3)) := by
    rw [show (((0 : ℤ), (3 : ℤ)) - Work.Pi6.vr 3) = ((-3 : ℤ), (5 : ℤ)) by
      ext <;> norm_num [Work.Pi6.vr]]
    exact S.isZero_quad 3 ((-3 : ℤ), (5 : ℤ)) (Or.inl (by norm_num))
  -- consequently the class survives to a nonzero class of `E₄^{0,3}`
  obtain ⟨u, hu⟩ := exists_ne_zero_page_four S (((0 : ℤ), (3 : ℤ))) ht2 ht3 hs2 hs3
    ((e2 0 3 (by omega) (by omega)).inv.hom (one (ZMod 2) B ⊗ₜ[ZMod 2] f)) hx0
  refine ⟨u, fun hdu => hu ?_⟩
  -- `E₅^{0,3} = 0` makes `d₄` injective on `E₄^{0,3}`
  have hE5 : IsZero (S.E (4 + 1) ((0 : ℤ), (3 : ℤ))) :=
    hvanish 3 (by norm_num) (by omega) (ModuleCat.subsingleton_of_isZero hE3) 0 3 rfl
  haveI : Subsingleton (S.E (4 + 1) ((0 : ℤ), (3 : ℤ))) := ModuleCat.subsingleton_of_isZero hE5
  have hproj : S.proj 4 ((0 : ℤ), (3 : ℤ)) ⟨u, hdu⟩ = 0 := Subsingleton.elim _ _
  have hmem := (S.proj_ker 4 ((0 : ℤ), (3 : ℤ)) (by norm_num) ⟨u, hdu⟩).mp hproj
  -- and nothing maps into `(0,3)` on page `4` either
  have hsrc : IsZero (S.E 4 (((0 : ℤ), (3 : ℤ)) - Work.Pi6.vr 4)) := by
    rw [show (((0 : ℤ), (3 : ℤ)) - Work.Pi6.vr 4) = ((-4 : ℤ), (6 : ℤ)) by
      ext <;> norm_num [Work.Pi6.vr]]
    exact S.isZero_quad 4 ((-4 : ℤ), (6 : ℤ)) (Or.inl (by norm_num))
  obtain ⟨y, hy⟩ := hmem
  haveI : Subsingleton (S.E 4 (((0 : ℤ), (3 : ℤ)) - Work.Pi6.vr 4)) :=
    ModuleCat.subsingleton_of_isZero hsrc
  have hy0 : y = 0 := Subsingleton.elim _ _
  rw [hy0, map_zero] at hy
  exact hy.symm

end Work.Pi6.EMM2.K4F
