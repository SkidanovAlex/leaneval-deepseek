import Mathlib
import Submission.Work.SSS.baseRowDefs
import Submission.Work.SSS.LESFacts
import Submission.Work.SSS.FgQuotBasic

/-!
# The first step of the image filtration of `H_m(F_m)`

For a saturated filtration `ξ` of a chain complex `C` of `ℤ`-modules, the `s`-th stratum of the
image filtration of `H_m(F_m)` is `Psi ξ m s = im(H_m(F_s) → H_m(F_m))`.  The bottom row argument
needs `FgQuot (Psi ξ m (s-1)) (Psi ξ m s)`, and this file proves the `s = 0` case:

`Psi ξ m 0 = im(H_m(F_0) → H_m(F_m))` is finitely generated, as soon as the `E²` term `E²_{0,m}`
is (i.e. the quotient of `H_m(F_0)` by the image of the connecting map `k : E¹_{1,m} → E¹_{0,m}`).

The proof: the connecting map `k = kF ξ 0 m` has image the kernel of the map on homology induced by
`F_0 ↪ F_1`.  Hence `hE` gives finitely many generators of `H_m(F_0)` modulo that kernel; their
images generate the image of `H_m(F_0) → H_m(F_m)` (which factors through `H_m(F_1)`), so the latter
is finitely generated.
-/

set_option autoImplicit false

namespace Work.SSS.Lem

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- Finiteness of the range of `homologyMap φ i` only depends on the index through its value. -/
lemma fg_range_homologyMap_shift {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) {i j : ℕ}
    (h : i = j) :
    (LinearMap.range (HomologicalComplex.homologyMap φ i).hom).FG ↔
      (LinearMap.range (HomologicalComplex.homologyMap φ j).hom).FG := by
  subst h
  rfl

/-- If `⊤ ≤ ker f ⊔ span S` for a finite set `S ⊆ A`, then the range of `f : A →ₗ[ℤ] B` is
finitely generated: `f(K ⊔ span S) = f(span S) = span (f '' S)`. -/
lemma fg_range_of_generators {A B : Type*} [AddCommGroup A] [Module ℤ A] [AddCommGroup B]
    [Module ℤ B] (f : A →ₗ[ℤ] B) (S : Set A) (hS : S.Finite)
    (h : (⊤ : Submodule ℤ A) ≤ LinearMap.ker f ⊔ Submodule.span ℤ S) :
    (LinearMap.range f).FG := by
  have htop : LinearMap.ker f ⊔ Submodule.span ℤ S = ⊤ := top_unique h
  rw [LinearMap.range_eq_map, ← htop, Submodule.map_sup, Submodule.map_span]
  have hker : Submodule.map f (LinearMap.ker f) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro y ⟨x, hx, rfl⟩
    simpa using hx
  rw [hker, bot_sup_eq]
  exact Submodule.fg_span (hS.image (f : A → B))

theorem fgQuot_Psi_zero {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Work.SSS.Filtration C) (m : ℕ)
    (hm : 1 ≤ m) (hE : Work.SSS.E2quot ξ 0 m) :
    Work.SSS.FgQuot ⊥ (Work.SSS.Psi ξ m 0) := by
  -- Unfold `hE` on the first page: its two submodules are `im d¹_{1,m}` and `ker d¹_{0,m}`.
  have hd0 : (E1Complex ξ m).d 0 (0 - 1) = 0 := by
    simp only [E1Complex]
    exact ChainComplex.of_d_ne (X := fun s => E1 ξ s m) (d := fun s => d1 ξ s m)
      (i := 0) (j := 0) (by omega)
  have hd1 : (E1Complex ξ m).d 1 0 = d1 ξ 0 m := by
    simp only [E1Complex]
    exact ChainComplex.of_d (fun s => E1 ξ s m) (fun s => d1 ξ s m) 0
  have hE1 : FgQuot (LinearMap.range (d1 ξ 0 m).hom) ⊤ := by
    have h := hE
    simp only [E2quot] at h
    rw [hd0, hd1] at h
    simp only [ModuleCat.hom_zero, LinearMap.ker_zero] at h
    exact h
  -- The first differential is the connecting map `k` of the filtration, whose image is the kernel
  -- of the map induced by `F_0 ↪ F_1` (exactness of the long exact sequence of the filtration).
  have hles : LinearMap.range (d1 ξ 0 m).hom =
      LinearMap.ker (HomologicalComplex.homologyMap (incF ξ.F 0) (0 + m)).hom := by
    rw [show (d1 ξ 0 m).hom = (kF ξ 0 m).hom from by
      rw [d1]; exact congrArg ModuleCat.Hom.hom (Category.comp_id _)]
    exact range_kF_eq_ker_incF ξ 0 m
  rw [hles] at hE1
  -- Hence `H_m(F_0)` is generated, modulo `ker (H_m(F_0) → H_m(F_1))`, by finitely many elements.
  obtain ⟨S, hSfin, -, hSle⟩ := (fgQuot_iff_generators (R := ℤ)).mp hE1
  have hf : (LinearMap.range (HomologicalComplex.homologyMap (incF ξ.F 0) (0 + m)).hom).FG :=
    fg_range_of_generators _ S hSfin hSle
  -- Shift the index `0 + m` to `m`.
  have hf' : (LinearMap.range (HomologicalComplex.homologyMap (incF ξ.F 0) m).hom).FG :=
    (fg_range_homologyMap_shift (incF ξ.F 0) (Nat.zero_add m)).mp hf
  -- `H_m(F_0) → H_m(F_m)` factors through `H_m(F_1)`, so its image is the image of a finitely
  -- generated submodule, hence finitely generated.
  have hgoal : (Psi ξ m 0).FG := by
    rw [Psi, dif_pos (Nat.zero_le m)]
    have hfac : ξ.F.map (homOfLE (Nat.zero_le m)) =
        incF ξ.F 0 ≫ ξ.F.map (homOfLE hm) := by
      rw [incF, ← Functor.map_comp, homOfLE_comp]
    rw [hfac, HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp, LinearMap.range_comp]
    exact Submodule.FG.map _ hf'
  -- Finally `Psi ξ m 0` is finitely generated, hence `FgQuot ⊥ (Psi ξ m 0)`.
  obtain ⟨S, hSfin, hS⟩ := Submodule.fg_def.mp hgoal
  refine (fgQuot_iff_generators (R := ℤ)).mpr ⟨S, hSfin, ?_, ?_⟩
  · rw [← hS]; exact Submodule.subset_span
  · rw [← hS, bot_sup_eq]

end

end Work.SSS.Lem
