import Mathlib
import Submission.Work.SSS.Packet

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The `s = 0` base case of the graded-piece statement of the convergence packet

For a saturated filtration `ξ` of a chain complex `C` of `ℤ`-modules, the `E²` term `E2 ξ 0 n` of
the spectral sequence controls the bottom piece `Phi ξ n 0 = im(H_n(F_0) → H_n(C))` of the image
filtration: the latter is a quotient (indeed the image under `H_n(F_1) → H_n(C)`) of the former.
Concretely, writing `δ = kF ξ 0 n : H_{n+1}(F_1/F_0) → H_n(F_0)` for the connecting map of the
short exact sequence `0 → F_0 → F_1 → F_1/F_0 → 0`:

* `E2 ξ 0 n = H_0(E1Complex ξ n)` is the cokernel of the only incoming differential
  `d1 ξ 0 n = kF ξ 0 n ≫ jF ξ 0 n = kF ξ 0 n` (since `jF ξ 0 n = 𝟙`);
* `H_n(F_0)/im δ = coker δ` maps onto `Phi ξ n 0`, because
  `im δ = ker(H_n(F_0) → H_n(F_1))` and `incl 0 = (F_0 → F_1) ≫ incl 1`.

Hence `Module.Finite ℤ (E2 ξ 0 n)` implies that `Phi ξ n 0`, being the range of a map out of the
cokernel `K` of `kF ξ 0 n` (which is finite), is finitely generated.  This is the `s = 0` case of
`Work.SSS.gradedField` / of the `graded` field of `Work.SSS.SSPacket`; the case `s ≥ 1` is
`Work.SSS.graded_succ`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.SSS.GradedZero

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {C : ChainComplex (ModuleCat ℤ) ℕ}

/-- **`H_0` is the cokernel of the incoming differential.**  For a `ℕ`-indexed chain complex `K` of
`ℤ`-modules, the incoming differential to degree `0` is `K.d 1 0` and the outgoing one is
`K.d 0 0 = 0`, so `K.homology 0` is the cokernel of `K.d 1 0`.

This is `K.homologyIsoSc' 1 0 0` followed by the identification of the homology of the short complex
`K.X 1 → K.X 0 → 0` with the cokernel of its first map. -/
noncomputable def homologyZeroIsoCoker (K : ChainComplex (ModuleCat ℤ) ℕ) :
    K.homology 0 ≅ cokernel (K.d 1 0) :=
  (HomologicalComplex.homologyIsoSc' K 1 0 0
    (ComplexShape.prev_eq' (ComplexShape.down ℕ) (i := 0) (j := 1) (by simp [ComplexShape.down]))
    (by rw [ComplexShape.next_eq_self']; intro k; simp [ComplexShape.down])).trans
  (ShortComplex.RightHomologyData.homologyIso
    (ShortComplex.RightHomologyData.ofHasCokernel (K.sc' 1 0 0) (by
      rw [HomologicalComplex.shortComplexFunctor'_obj_g]
      exact K.shape 0 0 (by simp [ComplexShape.down]))))

/-- Finiteness of the range of an induced homology map is insensitive to an equal degree. -/
theorem fg_range_homologyMap_eq {K L : ChainComplex (ModuleCat ℤ) ℕ} (f : K ⟶ L) {i j : ℕ}
    (h : i = j) (hf : (LinearMap.range (HomologicalComplex.homologyMap f i).hom).FG) :
    (LinearMap.range (HomologicalComplex.homologyMap f j).hom).FG := by
  subst h; exact hf

/-- The `s = 0` differential of the E¹ row complex is the connecting map `kF ξ 0 n`:  the other
factor `jF ξ 0 n` is the identity because `grF ξ.F 0 = F_0`. -/
theorem d1_zero_eq_kF (ξ : Filtration C) (n : ℕ) : d1 ξ 0 n = kF ξ 0 n := by
  rw [d1, jF.eq_1]
  exact Category.comp_id _

/-- The differential of `E1Complex ξ n` in degree `0` is `d1 ξ 0 n = kF ξ 0 n`. -/
theorem E1Complex_d_zero (ξ : Filtration C) (n : ℕ) :
    (E1Complex ξ n).d 1 0 = kF ξ 0 n := by
  rw [show (E1Complex ξ n).d 1 0 = d1 ξ 0 n from
    ChainComplex.of_d (fun s => E1 ξ s n) (fun s => d1 ξ s n) 0,
    d1_zero_eq_kF ξ n]

/-- **The left column in degree `0` is the cokernel of the connecting map.** -/
noncomputable def E2_zero_iso_coker (ξ : Filtration C) (n : ℕ) :
    E2 ξ 0 n ≅ cokernel (kF ξ 0 n) :=
  (homologyZeroIsoCoker (E1Complex ξ n)).trans
    (eqToIso (congrArg (fun (f : (E1Complex ξ n).X 1 ⟶ (E1Complex ξ n).X 0) =>
      cokernel f) (E1Complex_d_zero ξ n)))

/-- Finiteness of `E2 ξ 0 n` transfers to its model, the cokernel of `kF ξ 0 n`. -/
theorem cokernel_kF_finite (ξ : Filtration C) (n : ℕ)
    (hE : Module.Finite ℤ (E2 ξ 0 n)) :
    Module.Finite ℤ (cokernel (kF ξ 0 n) : ModuleCat ℤ) := by
  haveI : Module.Finite ℤ (E2 ξ 0 n) := hE
  exact Module.Finite.equiv (E2_zero_iso_coker ξ n).toLinearEquiv

/-- **The bottom piece of the image filtration is a quotient of the left column.**  If `E2 ξ 0 n` is
finitely generated then so is `Phi ξ n 0 = im(H_n(F_0) → H_n(C))`. -/
theorem graded_zero (C : ChainComplex (ModuleCat ℤ) ℕ) (ξ : Work.SSS.Filtration C) (n : ℕ)
    (hE : Module.Finite ℤ (Work.SSS.E2 ξ 0 n)) :
    (Work.SSS.Phi ξ n (0 : ℤ)).FG := by
  -- the connecting map `kF ξ 0 n` dies in `H_n(C)`: it lands in `ker(H_n(F_0) → H_n(F_1))`,
  -- and `incl 0` factors through `F_1 → C`
  have hzero : Work.SSS.kF ξ 0 n ≫ HomologicalComplex.homologyMap (ξ.incl 0) (0 + n) = 0 := by
    have hK : Work.SSS.kF ξ 0 n ≫
        HomologicalComplex.homologyMap (Work.SSS.incF ξ.F 0) (0 + n) = 0 :=
      ShortComplex.ShortExact.δ_comp (Work.SSS.sesF_shortExact ξ 0) ((0+1) + n) (0 + n)
        (by simp [ComplexShape.down]; omega)
    have hfac : ξ.incl 0 = Work.SSS.incF ξ.F 0 ≫ ξ.incl 1 := (ξ.compat (Nat.le_succ 0)).symm
    rw [hfac, HomologicalComplex.homologyMap_comp, ← Category.assoc, hK, zero_comp]
  -- `kF` therefore induces a map out of its cokernel, with the same range as `incl 0`
  let K : ModuleCat ℤ := cokernel (Work.SSS.kF ξ 0 n)
  let d : K ⟶ C.homology (0 + n) :=
    cokernel.desc (Work.SSS.kF ξ 0 n) (HomologicalComplex.homologyMap (ξ.incl 0) (0 + n)) hzero
  have hdπ : cokernel.π (Work.SSS.kF ξ 0 n) ≫ d
      = HomologicalComplex.homologyMap (ξ.incl 0) (0 + n) := cokernel.π_desc _ _ _
  have hd_range : d.hom.range
      = (HomologicalComplex.homologyMap (ξ.incl 0) (0 + n)).hom.range := by
    have h2 : (cokernel.π (Work.SSS.kF ξ 0 n) ≫ d).hom
        = d.hom ∘ₗ (cokernel.π (Work.SSS.kF ξ 0 n)).hom := ModuleCat.hom_comp _ _
    have hsurj : Function.Surjective ⇑(cokernel.π (Work.SSS.kF ξ 0 n)).hom :=
      (ModuleCat.epi_iff_surjective _).mp inferInstance
    have htop : (cokernel.π (Work.SSS.kF ξ 0 n)).hom.range = ⊤ :=
      LinearMap.range_eq_top.mpr hsurj
    calc d.hom.range = Submodule.map d.hom (⊤ : Submodule ℤ K) :=
          (Submodule.map_top d.hom).symm
      _ = Submodule.map d.hom (cokernel.π (Work.SSS.kF ξ 0 n)).hom.range := by rw [htop]
      _ = (d.hom ∘ₗ (cokernel.π (Work.SSS.kF ξ 0 n)).hom).range :=
            (LinearMap.range_comp _ _).symm
      _ = (HomologicalComplex.homologyMap (ξ.incl 0) (0 + n)).hom.range := by rw [← h2, hdπ]
  have hA : d.hom.range.FG := by
    have htop : (⊤ : Submodule ℤ K).FG := Module.finite_def.mp (cokernel_kF_finite ξ n hE)
    have hmap := htop.map d.hom
    rwa [Submodule.map_top] at hmap
  -- `Phi ξ n 0` is `im(H_n(F_0) → H_n(C))`, i.e. the range of `homologyMap (incl 0) n`
  have hPhi : Work.SSS.Phi ξ n (0 : ℤ)
      = (HomologicalComplex.homologyMap (ξ.incl 0) n).hom.range := by
    rw [Work.SSS.Phi, if_neg (show ¬ ((0 : ℤ) < 0) by norm_num)]
    rfl
  rw [hPhi]
  exact fg_range_homologyMap_eq (ξ.incl 0) (Nat.zero_add n) (by rw [← hd_range]; exact hA)

end

end Work.SSS.GradedZero
