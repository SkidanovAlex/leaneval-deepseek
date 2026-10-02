import Mathlib
import Submission.Work.Serre.serreS2OfC0C2oddS1

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The bottom cell of a range model of `K(ℤ,n)`

`Work.Serre.IsEMSpaceUpTo ℤ n _ N X pt` says that `X` is a model of `K(ℤ,n)` through degree `N`:
`πₙ(X,pt) ≃* ℤ`, `π_i(X,pt)` trivial for `i < n` and for `n < i ≤ N`.

The main result produces a based map `f : Sⁿ → X` (with `f s₀ = pt`) whose induced map
`Work.Serre.piMapN f n s₀ : πₙ(Sⁿ) → πₙ(X)` is bijective, i.e. the "bottom cell" of the model,
realising a generator of `πₙ(X) ≅ ℤ`.  It is the range-model version of
`Work.Serre.exists_bijective_piMapN'` (`Submission/Work/Serre/serreS2OfC0C2oddS1.lean`), which is
stated for an *unbounded* `Work.Serre.IsEMSpace`; the proof there uses only `πₙ(X) ≅ ℤ` and the
triviality of `π_i(X)` for `i ≤ n` (the injectivity of the Hurewicz map in degree `n` needs
connectivity up to `n - 1` only), so it adapts verbatim to a range model.

This is what lets the sphere-specific route to the stable stems consume the *range* models of
`Work.Serre.serreC0Range` (proved) in place of the unbounded `Work.Serre.SerreC0` (which would need
an infinite cell attachment).
-/

open scoped Topology Topology.Homotopy unitInterval
open Work.Serre

namespace Work.RatHurewicz

noncomputable section

/-- **The bottom cell of a range model, in the `(m+1)` index shape.** -/
theorem exists_bijective_piMapN_aux (m N : ℕ) (hm : 1 ≤ m) (X : Type) [TopologicalSpace X] (pt : X)
    (hE : IsEMSpaceUpTo ℤ (m+1) (by omega : 0 < m+1) N X pt) :
    ∃ (s₀ : Sph (m+1)) (f : C(Sph (m+1), X)),
      f s₀ = pt ∧ Function.Bijective (piMapN f (m+1) s₀) := by
  obtain ⟨φ⟩ := hE.1
  let g₀ : HomotopyGroup (Fin (m+1)) X pt := φ.symm (Multiplicative.ofAdd (1:ℤ))
  obtain ⟨γ, hγ⟩ : ∃ γ : Ω^ (Fin (m+1)) X pt, (⟦γ⟧ : HomotopyGroup (Fin (m+1)) X pt) = g₀ :=
    ⟨Quotient.out g₀, Quotient.out_eq g₀⟩
  have h1 : (1:ℕ) ≤ m+1 := Nat.succ_le_succ (Nat.zero_le m)
  have h2 : (2:ℕ) ≤ m+1 := Nat.succ_le_succ hm
  refine ⟨Work.Stems.collapseMap (m+1) h1 0, Work.Stems.cubeLift (m+1) h1 γ, ?_⟩
  set s₀ := Work.Stems.collapseMap (m+1) h1 0 with hs₀def
  set f := Work.Stems.cubeLift (m+1) h1 γ with hfdef
  set x := f s₀ with hxdef
  have hs : x = pt := by
    have hcomp := Work.Stems.cubeLift_comp (m+1) h1 γ
    have h1' : f s₀ = γ.1 0 := by
      have := congrFun (congrArg DFunLike.coe hcomp) 0
      simpa [f, s₀, ContinuousMap.comp_apply] using this
    rw [hxdef, h1', γ.2 0 (zero_mem_cube_boundary (m+1) h1)]
  -- the cube at the base point `x` with the same underlying map
  let γ' : Ω^ (Fin (m+1)) X x := ⟨γ.1, fun q hq => (γ.2 q hq).trans hs.symm⟩
  let ψ : HomotopyGroup (Fin (m+1)) X x ≃* Multiplicative ℤ :=
    (Work.StemsB.homotopyGroupCast hs m).trans φ
  let g : HomotopyGroup (Fin (m+1)) X x := ⟦γ'⟧
  have hcastg : Work.StemsB.homotopyGroupCast hs m g = g₀ := by
    show Work.StemsB.homotopyGroupCast hs m (⟦γ'⟧ : HomotopyGroup (Fin (m+1)) X x) = g₀
    rw [show g₀ = (⟦γ⟧ : HomotopyGroup (Fin (m+1)) X pt) from hγ.symm]
    exact homotopyGroupCast_mk_eq hs γ' γ rfl
  have hψg : ψ g = Multiplicative.ofAdd (1:ℤ) := by
    show φ (Work.StemsB.homotopyGroupCast hs m g) = _
    rw [hcastg]
    exact φ.apply_symm_apply _
  have hpow : ∀ y : HomotopyGroup (Fin (m+1)) X x, y = g ^ (Multiplicative.toAdd (ψ y)) := by
    intro y
    set k := Multiplicative.toAdd (ψ y) with hk
    have h1 : ψ y = (Multiplicative.ofAdd (1:ℤ)) ^ k := by
      have hz : (Multiplicative.ofAdd (1:ℤ)) ^ k = Multiplicative.ofAdd k := by
        rw [← ofAdd_zsmul, smul_eq_mul, mul_one]
      rw [hz, hk]
      exact (ofAdd_toAdd (x := ψ y)).symm
    have h2 : y = ψ.symm ((Multiplicative.ofAdd (1:ℤ)) ^ k) := by
      rw [← h1, ψ.symm_apply_apply]
    rw [h2, map_zpow, ← hψg, ψ.symm_apply_apply]
  have horder : ∀ k : ℤ, g ^ k = 1 → k = 0 := by
    intro k hk
    have h : (Multiplicative.ofAdd (1:ℤ)) ^ k = 1 := by
      rw [← hψg, ← map_zpow, hk, map_one]
    rw [← ofAdd_zsmul k (1:ℤ)] at h
    simp only [smul_eq_mul, mul_one] at h
    exact ofAdd_eq_one.mp h
  -- the value of the descent on the collapse class
  have hFc : Work.StemsB.πmap f m s₀ (⟦collapseLoop (m+1) h1⟧ :
      HomotopyGroup (Fin (m+1)) (Sph (m+1)) s₀) = g := by
    have hcomp := Work.Stems.cubeLift_comp (m+1) h1 γ
    rw [Work.StemsB.πmap_apply_mk]
    show (⟦Work.StemsB.genLoopMap f (m+1) (collapseLoop (m+1) h1)⟧ :
      HomotopyGroup (Fin (m+1)) X x) = g
    have hgen : Work.StemsB.genLoopMap f (m+1) (collapseLoop (m+1) h1) = γ' := by
      apply Subtype.ext
      apply ContinuousMap.ext
      intro t
      change f ((collapseLoop (m+1) h1) t) = γ' t
      change f ((Work.Stems.collapseMap (m+1) h1) t) = γ.1 t
      simpa [f, ContinuousMap.comp_apply] using congrFun (congrArg DFunLike.coe hcomp) t
    rw [hgen]
  -- Hurewicz injectivity for the model
  have hXinj : Function.Injective (Work.Stems.hurewiczMap (m+1) h1 x) := by
    refine hurewiczMap_injective_of_conn' (m+1) h2 x (fun i hi => ?_)
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      have hpath : PathConnectedSpace X := by
        haveI h0 : Subsingleton (HomotopyGroup (Fin 0) X pt) := hE.2 0 (by omega) (Or.inl (by omega))
        have hZ : Subsingleton (ZerothHomotopy X) :=
          (HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := pt)).surjective.subsingleton
        exact pathConnectedSpace_iff_zerothHomotopy.mpr ⟨⟨ZerothHomotopy.mk pt⟩, hZ⟩
      haveI : PathConnectedSpace X := hpath
      haveI hZ : Subsingleton (ZerothHomotopy X) :=
        (pathConnectedSpace_iff_zerothHomotopy (X := X)).mp hpath |>.2
      exact ⟨fun u v => (HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x)).injective
        (Subsingleton.elim _ _)⟩
    · have hi' : i ≠ m+1 := by omega
      have hsub : Subsingleton (HomotopyGroup (Fin i) X pt) := hE.2 i hi' (Or.inl (by omega))
      have hidx : i - 1 + 1 = i := Nat.sub_add_cancel (by omega)
      haveI hsub' : Subsingleton (HomotopyGroup (Fin (i-1+1)) X pt) := by
        rw [hidx]; exact hsub
      exact hidx ▸ (Work.StemsB.homotopyGroupCast hs (i-1)).symm.surjective.subsingleton
  -- the Hurewicz class of the generator is the image of the sphere generator
  have hHg : (CategoryTheory.ConcreteCategory.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of (Sph (m+1))) (TopCat.of X) (TopCat.ofHom f))
      (m+1))) (Work.Stems.sphereGenerator (m+1) h1)
      = Work.Stems.hurewiczMap (m+1) h1 x g := by
    rw [← hurewiczChain_collapseLoop m, ← Work.Stems.hurewiczMap_mk]
    rw [← hFc]
    exact (Work.Stems.hurewiczMap_natural (m+1) h1 f ⟦collapseLoop (m+1) h1⟧).symm
  -- ℤ-linearity of the Hurewicz map
  have hzsmul : ∀ k : ℤ, k • Work.Stems.hurewiczMap (m+1) h1 x g
      = Work.Stems.hurewiczMap (m+1) h1 x (g ^ k) := by
    intro k
    calc k • Work.Stems.hurewiczMap (m+1) h1 x g
        = k • Work.Stems.hurewiczHom m x (Additive.ofMul g) := by
          simp [Work.Stems.hurewiczHom_apply]
      _ = Work.Stems.hurewiczHom m x (k • Additive.ofMul g) := (map_zsmul _ k _).symm
      _ = Work.Stems.hurewiczHom m x (Additive.ofMul (g ^ k)) := by rw [ofMul_zpow]
      _ = Work.Stems.hurewiczMap (m+1) h1 x (g ^ k) := by
          simp [Work.Stems.hurewiczHom_apply]
  refine ⟨hs, ?_, ?_⟩
  · intro a b hab
    apply hurewiczMap_sphere_injective (m+1) h2 s₀
    have hnat_a := Work.Stems.hurewiczMap_natural (m+1) h1 f a
    have hnat_b := Work.Stems.hurewiczMap_natural (m+1) h1 f b
    set H := CategoryTheory.ConcreteCategory.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of (Sph (m+1))) (TopCat.of X) (TopCat.ofHom f)) (m+1))
      with hHdef
    set e := Classical.choice (Work.Cohomology.sphereHomologyTop (m+1) h1) with hedef
    set k := ModuleCat.Hom.hom e.hom
      (Work.Stems.hurewiczMap (m+1) h1 s₀ a - Work.Stems.hurewiczMap (m+1) h1 s₀ b) with hkdef
    have hab' : HomotopyGroup.map f a = HomotopyGroup.map f b := hab
    have hstep1 : H (Work.Stems.hurewiczMap (m+1) h1 s₀ a
        - Work.Stems.hurewiczMap (m+1) h1 s₀ b) = 0 := by
      rw [map_sub, ← hnat_a, ← hnat_b, hab', sub_self]
    have hstep2 : k • Work.Stems.hurewiczMap (m+1) h1 x g = 0 := by
      have hmod := module_eq_zsmul_gen e
        (Work.Stems.hurewiczMap (m+1) h1 s₀ a - Work.Stems.hurewiczMap (m+1) h1 s₀ b)
      have hgen : ModuleCat.Hom.hom e.inv (1:ℤ) = Work.Stems.sphereGenerator (m+1) h1 := rfl
      calc k • Work.Stems.hurewiczMap (m+1) h1 x g
          = k • H (ModuleCat.Hom.hom e.inv (1:ℤ)) := by rw [hgen, hHg]
        _ = H (k • ModuleCat.Hom.hom e.inv (1:ℤ)) := (map_zsmul _ k _).symm
        _ = H (Work.Stems.hurewiczMap (m+1) h1 s₀ a
              - Work.Stems.hurewiczMap (m+1) h1 s₀ b) := by rw [← hmod]
        _ = 0 := hstep1
    have hk0 : k = 0 := by
      have hgk : Work.Stems.hurewiczMap (m+1) h1 x (g ^ k) = 0 := by
        rw [← hzsmul k]
        exact hstep2
      have hg1 : g ^ k = 1 := by
        apply hXinj
        rw [hgk, Work.Stems.hurewiczMap_one]
      exact horder k hg1
    have hzero : Work.Stems.hurewiczMap (m+1) h1 s₀ a
        - Work.Stems.hurewiczMap (m+1) h1 s₀ b = 0 := by
      have hk0' : ModuleCat.Hom.hom e.hom
          (Work.Stems.hurewiczMap (m+1) h1 s₀ a - Work.Stems.hurewiczMap (m+1) h1 s₀ b) = 0 := hk0
      rw [module_eq_zsmul_gen e
        (Work.Stems.hurewiczMap (m+1) h1 s₀ a - Work.Stems.hurewiczMap (m+1) h1 s₀ b),
        hk0', zero_smul]
    exact sub_eq_zero.mp hzero
  · intro y
    let c : HomotopyGroup (Fin (m+1)) (Sph (m+1)) s₀ := ⟦collapseLoop (m+1) h1⟧
    have hcF : Work.StemsB.πmap f m s₀ c = g := hFc
    refine ⟨c ^ (Multiplicative.toAdd (ψ y)), ?_⟩
    show Work.StemsB.πmap f m s₀ (c ^ (Multiplicative.toAdd (ψ y))) = y
    rw [map_zpow, hcF]
    exact (hpow y).symm

/-- **The bottom cell of a range model of `K(ℤ,n)`.**  A range model of `K(ℤ,n)` through degree
`N` admits a based map `f : Sⁿ → X` inducing a bijection on `πₙ`. -/
theorem exists_bijective_piMapN_rangeModel (n N : ℕ) (hn : 2 ≤ n)
    (X : Type) [TopologicalSpace X] (pt : X)
    (hX : Work.Serre.IsEMSpaceUpTo ℤ n (by omega) N X pt) :
    ∃ (s₀ : Work.Serre.Sph n) (f : C(Work.Serre.Sph n, X)),
      f s₀ = pt ∧ Function.Bijective (Work.Serre.piMapN f n s₀) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.sub_add_cancel (by omega)).symm⟩
  exact exists_bijective_piMapN_aux m N (by omega) X pt hX

end

end Work.RatHurewicz
