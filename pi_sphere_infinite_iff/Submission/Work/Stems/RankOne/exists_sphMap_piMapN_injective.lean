import Mathlib
import Submission.Work.Stems.rankOne_hurewicz_torsion
import Submission.Work.RatHurewicz.exists_bijective_piMapN_rangeModel
import Submission.Work.Stems.HurewiczFirstDegree

/-!
# The bottom cell of a rank-one space

If `X` has trivial homotopy groups in degrees `≤ N` except in degree `n` (where `H_n(X;ℚ) ≅ ℚ`),
then some based map `f : Sⁿ → X` induces an *injection* `πₙ(Sⁿ) → πₙ(X)`: the image of the collapse
class is a non-torsion element of `πₙ(X)`, which exists because otherwise `H_n(X;ℚ) = 0`
(`Work.Stems.rankOne_hurewicz_torsion`).

This is the "non-torsion element" input of the odd step of the rank-one Eilenberg--MacLane
computation (`Work.Stems.rankOne_oddStep`), whose cover argument needs a sphere map realising a
class of infinite order.
-/

open scoped Topology Topology.Homotopy unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Stems

/-- The Hurewicz map does not depend on the proof of `1 ≤ n` it carries. -/
theorem hurewiczMap_proof_congr (n : ℕ) (h1 h2 : 1 ≤ n) {X : Type} [TopologicalSpace X] (x₀ : X) :
    hurewiczMap n h1 x₀ = hurewiczMap n h2 x₀ :=
  congrArg (fun hn => hurewiczMap n hn x₀) (Subsingleton.elim h1 h2)

end Work.Stems

namespace Work.Stems.RankOne

theorem exists_sphMap_piMapN_injective {X : Type} [TopologicalSpace X] (x₀ : X) {n N : ℕ}
    (hn : 3 ≤ n) (hN : n ≤ N)
    (hvan : ∀ j : ℕ, j ≤ N → j ≠ n → Subsingleton (HomotopyGroup (Fin j) X x₀))
    (hgen : Nonempty (Work.Serre.ratH (TopCat.of X) n ≅ ModuleCat.of ℚ ℚ)) :
    ∃ (s₀ : Work.Serre.Sph n) (f : C(Work.Serre.Sph n, X)),
      f s₀ = x₀ ∧ Function.Injective (Work.Serre.piMapN f n s₀) := by
  -- work in the successor degree `n = m + 1`
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.sub_add_cancel (by omega)).symm⟩
  have h1 : (1 : ℕ) ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
  have h2 : (2 : ℕ) ≤ m + 1 := by omega
  have hconn : ∀ i : ℕ, i < m + 1 → Subsingleton (HomotopyGroup (Fin i) X x₀) :=
    fun i hi => hvan i (by omega) (by omega)
  -- a class of infinite order in `π_{m+1}(X,x₀)`
  have hnontor : ∃ α : HomotopyGroup (Fin (m + 1)) X x₀, ∀ k : ℕ, 0 < k → α ^ k ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hz : IsZero (Work.Serre.ratH (TopCat.of X) (m + 1)) :=
      Work.Stems.rankOne_hurewicz_torsion (k := m + 1) (by omega) x₀ hconn hcon
    obtain ⟨e⟩ := hgen
    have hzq : IsZero (ModuleCat.of ℚ ℚ) := IsZero.of_iso hz e.symm
    haveI : Subsingleton ℚ := ModuleCat.isZero_iff_subsingleton.mp hzq
    exact one_ne_zero (Subsingleton.elim (1 : ℚ) 0)
  obtain ⟨α, hα⟩ := hnontor
  obtain ⟨γ, hγ⟩ : ∃ γ : Ω^ (Fin (m + 1)) X x₀, (⟦γ⟧ : HomotopyGroup (Fin (m + 1)) X x₀) = α :=
    ⟨Quotient.out α, Quotient.out_eq α⟩
  refine ⟨Work.Stems.collapseMap (m + 1) h1 0, Work.Stems.cubeLift (m + 1) h1 γ, ?_, ?_⟩
  · -- the map is based
    have hcomp := Work.Stems.cubeLift_comp (m + 1) h1 γ
    have hval : (Work.Stems.cubeLift (m + 1) h1 γ) (Work.Stems.collapseMap (m + 1) h1 0)
        = γ.1 0 := by
      have h := congrFun (congrArg DFunLike.coe hcomp) 0
      simpa [ContinuousMap.comp_apply] using h
    rw [hval, γ.2 0 (Work.Serre.zero_mem_cube_boundary (m + 1) h1)]
  · -- injectivity on `π_{m+1}`
    set s₀ := Work.Stems.collapseMap (m + 1) h1 0 with hs₀def
    set f := Work.Stems.cubeLift (m + 1) h1 γ with hfdef
    set x := f s₀ with hxdef
    have hs : x = x₀ := by
      have hcomp := Work.Stems.cubeLift_comp (m + 1) h1 γ
      have hval : f s₀ = γ.1 0 := by
        have h := congrFun (congrArg DFunLike.coe hcomp) 0
        simpa [f, s₀, ContinuousMap.comp_apply] using h
      rw [hxdef, hval, γ.2 0 (Work.Serre.zero_mem_cube_boundary (m + 1) h1)]
    -- the same cube, based at `x`
    let γ' : Ω^ (Fin (m + 1)) X x := ⟨γ.1, fun q hq => (γ.2 q hq).trans hs.symm⟩
    let α' : HomotopyGroup (Fin (m + 1)) X x := ⟦γ'⟧
    have hcast : Work.StemsB.homotopyGroupCast hs m α' = α :=
      (Work.Serre.homotopyGroupCast_mk_eq hs γ' γ rfl).trans hγ
    -- `α'` has infinite order as well
    have hα' : ∀ k : ℤ, α' ^ k = 1 → k = 0 := by
      intro k hk
      have hkα : α ^ k = 1 := by
        have h := congrArg (⇑(Work.StemsB.homotopyGroupCast hs m)) hk
        rw [map_zpow, map_one, hcast] at h
        exact h
      rcases lt_trichotomy k 0 with hlt | heq | hgt
      · have hneg : α ^ (-k) = 1 := by rw [zpow_neg, hkα, inv_one]
        have hnat : α ^ ((-k).toNat) = 1 := by
          rw [← zpow_natCast, Int.toNat_of_nonneg (le_of_lt (by omega : (0 : ℤ) < -k))]
          exact hneg
        exact absurd hnat (hα _ (by omega))
      · exact heq
      · have hnat : α ^ (k.toNat) = 1 := by
          rw [← zpow_natCast, Int.toNat_of_nonneg (le_of_lt hgt)]
          exact hkα
        exact absurd hnat (hα _ (by omega))
    -- the value of the induced map on the collapse class
    have hcomp := Work.Stems.cubeLift_comp (m + 1) h1 γ
    have hFc : Work.StemsB.πmap f m s₀
        (⟦Work.Serre.collapseLoop (m + 1) h1⟧ :
          HomotopyGroup (Fin (m + 1)) (Work.Serre.Sph (m + 1)) s₀) = α' := by
      rw [Work.StemsB.πmap_apply_mk]
      show (⟦Work.StemsB.genLoopMap f (m + 1) (Work.Serre.collapseLoop (m + 1) h1)⟧ :
        HomotopyGroup (Fin (m + 1)) X x) = α'
      have hgen : Work.StemsB.genLoopMap f (m + 1) (Work.Serre.collapseLoop (m + 1) h1) = γ' := by
        apply Subtype.ext
        apply ContinuousMap.ext
        intro t
        change f ((Work.Serre.collapseLoop (m + 1) h1) t) = γ' t
        change f ((Work.Stems.collapseMap (m + 1) h1) t) = γ.1 t
        simpa [f, ContinuousMap.comp_apply] using congrFun (congrArg DFunLike.coe hcomp) t
      rw [hgen]
    -- Hurewicz injectivity on the model
    have hXinj : Function.Injective (Work.Stems.hurewiczMap (m + 1) h1 x) := by
      refine Work.Serre.hurewiczMap_injective_of_conn' (m + 1) h2 x (fun i hi => ?_)
      rcases Nat.eq_zero_or_pos i with hi0 | hipos
      · subst hi0
        have hpath : PathConnectedSpace X := by
          haveI h0 : Subsingleton (HomotopyGroup (Fin 0) X x₀) := hconn 0 (by omega)
          have hZ : Subsingleton (ZerothHomotopy X) :=
            (HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x₀)).surjective.subsingleton
          exact pathConnectedSpace_iff_zerothHomotopy.mpr ⟨⟨ZerothHomotopy.mk x₀⟩, hZ⟩
        haveI : PathConnectedSpace X := hpath
        haveI hZ : Subsingleton (ZerothHomotopy X) :=
          (pathConnectedSpace_iff_zerothHomotopy (X := X)).mp hpath |>.2
        exact ⟨fun u v => (HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x)).injective
          (Subsingleton.elim _ _)⟩
      · have hidx : i - 1 + 1 = i := Nat.sub_add_cancel (by omega)
        have hsub : Subsingleton (HomotopyGroup (Fin i) X x₀) := hconn i (by omega)
        haveI hsub' : Subsingleton (HomotopyGroup (Fin (i - 1 + 1)) X x₀) := by
          rw [hidx]; exact hsub
        exact hidx ▸ (Work.StemsB.homotopyGroupCast hs (i - 1)).symm.surjective.subsingleton
    -- the Hurewicz class of the collapse class is the sphere generator
    have hHgen : CategoryTheory.ConcreteCategory.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (TopCat.of (Work.Serre.Sph (m + 1))) (TopCat.of X)
          (TopCat.ofHom f)) (m + 1)) (Work.Stems.sphereGenerator (m + 1) h1)
        = Work.Stems.hurewiczMap (m + 1) h1 x α' := by
      rw [← Work.Serre.hurewiczChain_collapseLoop m, ← Work.Stems.hurewiczMap_mk]
      rw [← hFc]
      exact (Work.Stems.hurewiczMap_natural (m + 1) h1 f
        ⟦Work.Serre.collapseLoop (m + 1) h1⟧).symm
    -- ℤ-linearity of the Hurewicz map
    have hzsmul : ∀ k : ℤ, k • Work.Stems.hurewiczMap (m + 1) h1 x α'
        = Work.Stems.hurewiczMap (m + 1) h1 x (α' ^ k) := by
      intro k
      calc k • Work.Stems.hurewiczMap (m + 1) h1 x α'
          = k • Work.Stems.hurewiczHom m x (Additive.ofMul α') := by
            simp [Work.Stems.hurewiczHom_apply]
        _ = Work.Stems.hurewiczHom m x (k • Additive.ofMul α') := (map_zsmul _ k _).symm
        _ = Work.Stems.hurewiczHom m x (Additive.ofMul (α' ^ k)) := by rw [ofMul_zpow]
        _ = Work.Stems.hurewiczMap (m + 1) h1 x (α' ^ k) := by
            simp [Work.Stems.hurewiczHom_apply]
    -- the argument of the auxiliary proof, with `g` replaced by the non-torsion class `α'`
    intro a b hab
    apply Work.Serre.hurewiczMap_sphere_injective (m + 1) h2 s₀
    have hnat_a := Work.Stems.hurewiczMap_natural (m + 1) h1 f a
    have hnat_b := Work.Stems.hurewiczMap_natural (m + 1) h1 f b
    set H := CategoryTheory.ConcreteCategory.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of (Work.Serre.Sph (m + 1))) (TopCat.of X)
        (TopCat.ofHom f)) (m + 1)) with hHdef
    set e := Classical.choice (Work.Cohomology.sphereHomologyTop (m + 1) h1) with hedef
    set k := ModuleCat.Hom.hom e.hom
      (Work.Stems.hurewiczMap (m + 1) h1 s₀ a - Work.Stems.hurewiczMap (m + 1) h1 s₀ b) with hkdef
    have hab' : HomotopyGroup.map f a = HomotopyGroup.map f b := hab
    have hstep1 : H (Work.Stems.hurewiczMap (m + 1) h1 s₀ a
        - Work.Stems.hurewiczMap (m + 1) h1 s₀ b) = 0 := by
      rw [map_sub, ← hnat_a, ← hnat_b, hab', sub_self]
    have hstep2 : k • Work.Stems.hurewiczMap (m + 1) h1 x α' = 0 := by
      have hmod := Work.Serre.module_eq_zsmul_gen e
        (Work.Stems.hurewiczMap (m + 1) h1 s₀ a - Work.Stems.hurewiczMap (m + 1) h1 s₀ b)
      have hgen : ModuleCat.Hom.hom e.inv (1 : ℤ) = Work.Stems.sphereGenerator (m + 1) h1 := rfl
      calc k • Work.Stems.hurewiczMap (m + 1) h1 x α'
          = k • H (ModuleCat.Hom.hom e.inv (1 : ℤ)) := by rw [hgen, hHgen]
        _ = H (k • ModuleCat.Hom.hom e.inv (1 : ℤ)) := (map_zsmul _ k _).symm
        _ = H (Work.Stems.hurewiczMap (m + 1) h1 s₀ a
              - Work.Stems.hurewiczMap (m + 1) h1 s₀ b) := by rw [← hmod]
        _ = 0 := hstep1
    have hk0 : k = 0 := by
      have hgk : Work.Stems.hurewiczMap (m + 1) h1 x (α' ^ k) = 0 := by
        rw [← hzsmul k]
        exact hstep2
      have hg1 : α' ^ k = 1 := by
        apply hXinj
        rw [hgk, Work.Stems.hurewiczMap_one]
      exact hα' k hg1
    have hzero : Work.Stems.hurewiczMap (m + 1) h1 s₀ a
        - Work.Stems.hurewiczMap (m + 1) h1 s₀ b = 0 := by
      have hk0' : ModuleCat.Hom.hom e.hom
          (Work.Stems.hurewiczMap (m + 1) h1 s₀ a - Work.Stems.hurewiczMap (m + 1) h1 s₀ b)
          = 0 := hk0
      rw [Work.Serre.module_eq_zsmul_gen e
        (Work.Stems.hurewiczMap (m + 1) h1 s₀ a - Work.Stems.hurewiczMap (m + 1) h1 s₀ b),
        hk0', zero_smul]
    exact sub_eq_zero.mp hzero

end Work.Stems.RankOne
