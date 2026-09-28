import Mathlib
import Submission.Work.Stems.HurewiczSphere

set_option backward.isDefEq.respectTransparency false

/-!
# Homology bookkeeping for the simplicial/cubical bridge

Generic facts about the homology functor of a chain complex of `ℤ`-modules (`ℤ`-linearity of
`homologyMap`, the cycle `cyclesMap` of a chain map, and the rank-one computation
`Hₙ(Sⁿ;ℤ) = ℤ·sphereGenerator`).
-/

open CategoryTheory AlgebraicTopology

namespace Work.RatHurewicz.Bridge

noncomputable section

/-- Naturality of `homologyπ` under `homologyMap`. -/
theorem homologyMap_homologyπ {K L : ChainComplex (ModuleCat ℤ) ℕ}
    [∀ i, K.HasHomology i] [∀ i, L.HasHomology i] (φ : K ⟶ L) (i : ℕ) (z : K.cycles i) :
    (ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ i)) (K.homologyπ i z)
      = L.homologyπ i (HomologicalComplex.cyclesMap φ i z) := by
  have h := HomologicalComplex.homologyπ_naturality (φ := φ) (i := i)
  have h2 := congrArg (fun (g : K.cycles i ⟶ L.homology i) => (ModuleCat.Hom.hom g) z) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2

/-- The underlying chain of the `cyclesMap` of a cycle. -/
theorem iCycles_cyclesMap {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) (i : ℕ)
    (z : K.cycles i) :
    (ModuleCat.Hom.hom (L.iCycles i)) (HomologicalComplex.cyclesMap φ i z)
      = (ModuleCat.Hom.hom (φ.f i)) ((ModuleCat.Hom.hom (K.iCycles i)) z) := by
  have h := HomologicalComplex.cyclesMap_i (φ := φ) (i := i)
  have h2 := congrArg (fun (g : K.cycles i ⟶ L.X i) => (ModuleCat.Hom.hom g) z) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2

/-- The `ℤ`-linearity of `homologyMap`. -/
theorem homologyMap_zsmul {K L : ChainComplex (ModuleCat ℤ) ℕ}
    [∀ i, K.HasHomology i] [∀ i, L.HasHomology i] (φ : K ⟶ L) (i : ℕ) (k : ℤ)
    (x : K.homology i) :
    (ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ i)) (k • x)
      = k • (ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ i)) x :=
  map_zsmul _ k x

/-- A `ℤ`-linear map out of `Hₙ(Sⁿ;ℤ)` which kills the chosen generator kills every class. -/
theorem homologyMap_eq_zero_of_sphereGenerator_eq_zero (n : ℕ) (hn : 1 ≤ n)
    {H' : Type} [AddCommGroup H'] [Module ℤ H']
    (l : (Work.Cohomology.singularChains ℤ (TopCat.of (Work.Stems.sphere n))).homology n →ₗ[ℤ] H')
    (hl : l (Work.Stems.sphereGenerator n hn) = 0)
    (u : (Work.Cohomology.singularChains ℤ (TopCat.of (Work.Stems.sphere n))).homology n) :
    l u = 0 := by
  set I := Classical.choice (Work.Cohomology.sphereHomologyTop n hn) with hI
  have h1 : (ModuleCat.Hom.hom I.inv) ((ModuleCat.Hom.hom I.hom) u) = u := by
    have h := congrArg ModuleCat.Hom.hom I.hom_inv_id
    rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
    exact LinearMap.congr_fun h u
  have h2 : (ModuleCat.Hom.hom I.inv) (1 : ℤ) = Work.Stems.sphereGenerator n hn := rfl
  have h3 : l.comp (ModuleCat.Hom.hom I.inv) = 0 := by
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    rw [h2, hl]
  rw [← h1, ← LinearMap.comp_apply, h3]
  simp


/-- The composite of `ℤ → K.X n`, `1 ↦ x`, with the differential is zero when `x` is a cycle. -/
theorem cycleOf_aux (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (x : K.X n)
    (hx : (K.d n (n - 1)) x = 0) :
    ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (K.X n) x) ≫ K.d n (n - 1) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change (K.d n (n - 1)) ((LinearMap.toSpanSingleton ℤ (K.X n) x) 1) = 0
  rw [LinearMap.toSpanSingleton_apply, one_smul]
  exact hx

/-- The cycle of a chain which is killed by the differential. -/
noncomputable def cycleOf (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (hn : 1 ≤ n) (x : K.X n)
    (hx : K.d n (n - 1) x = 0) : K.cycles n :=
  (K.liftCycles (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (K.X n) x)) (n - 1)
    ((ComplexShape.down ℕ).next_eq' (ComplexShape.down_mk n (n - 1) (Nat.sub_add_cancel hn)))
    (cycleOf_aux K n x hx)).hom (1 : ℤ)

/-- The underlying chain of `cycleOf`. -/
theorem iCycles_cycleOf (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (hn : 1 ≤ n) (x : K.X n)
    (hx : K.d n (n - 1) x = 0) :
    (ModuleCat.Hom.hom (K.iCycles n)) (cycleOf K n hn x hx) = x := by
  have hlift := HomologicalComplex.liftCycles_i (K := K) (i := n)
    (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (K.X n) x)) (n - 1)
    ((ComplexShape.down ℕ).next_eq' (ComplexShape.down_mk n (n - 1) (Nat.sub_add_cancel hn)))
    (cycleOf_aux K n x hx)
  have h2 := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶ K.X n) => (ModuleCat.Hom.hom g) (1 : ℤ)) hlift
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  change (ModuleCat.Hom.hom (K.iCycles n))
    ((ModuleCat.Hom.hom (K.liftCycles (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (K.X n) x))
      (n - 1) ((ComplexShape.down ℕ).next_eq' (ComplexShape.down_mk n (n - 1) (Nat.sub_add_cancel hn)))
      (cycleOf_aux K n x hx))) (1 : ℤ)) = x
  rw [h2]
  change (LinearMap.toSpanSingleton ℤ (K.X n) x) 1 = x
  rw [LinearMap.toSpanSingleton_apply, one_smul]

/-- A `ℤ`-linear map out of `Hₙ(Sⁿ;ℤ)` which kills the chosen generator is zero. -/
theorem homologyMap_eq_zero_of_sphereGenerator_eq_zero' (n : ℕ) (hn : 1 ≤ n)
    {H' : Type} [AddCommGroup H'] [Module ℤ H']
    (l : (Work.Cohomology.singularChains ℤ (TopCat.of (Work.Stems.sphere n))).homology n →ₗ[ℤ] H')
    (hl : l (Work.Stems.sphereGenerator n hn) = 0) :
    l = 0 :=
  LinearMap.ext fun u => homologyMap_eq_zero_of_sphereGenerator_eq_zero n hn l hl u

end

end Work.RatHurewicz.Bridge
