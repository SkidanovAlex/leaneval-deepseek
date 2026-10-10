import Mathlib.GroupTheory.Nilpotent
import Mathlib.Tactic.Have
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Submission.Work.SSGRoute.E7bDefs
import Submission.Work.SSGRoute.exists_level_localPthPower
import Submission.Work.SSGRoute.exists_localKummerLevelMaps
import Submission.Work.SSGRoute.extHMap_homEquiv0_apply_one
import Submission.Work.SSGRoute.localKummerSES1_shortExact
import Submission.Work.SSGRoute.localKummerSES2_shortExact
import Submission.Work.SSGRoute.localLevel_zetaCoeff
import Submission.Work.SSGRoute.subsingleton_extH_localUnitsK_one

/-!
# The local Kummer input for `Work.SSGRoute.detectAbove_sub_step` (Z6)

`dass_local_kummer_dies` is the local Kummer input that the dévissage step Z6 needs: a class of
`H²(D_w, 𝔽_p)` whose Kummer pushforward along a non-zero `z : 𝔽_p → K_wˣ` vanishes dies after
inflation to a higher level.  Its statement and proof follow the sibling node
`Submission/Work/SSGRoute/local_kummer_dies.lean` (`Work.SSGRoute.local_kummer_dies`); it is
reproduced here, with `dass`-`prefixed` names, because that module does not currently build, and this
step of the E7b dévissage cannot be assembled without it.  Once the sibling module builds, this
module can be dropped and `Submission/Work/SSGRoute/detectAbove_sub_step.lean` can import it again.
-/


namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

set_option maxHeartbeats 1000000

set_option backward.isDefEq.respectTransparency false

noncomputable section

/-! ## Helpers for `local_kummer_dies` -/

/-- `Additive.ofMul` is a section of `Additive.toMul`. -/
theorem dass_ofMul_toMul_additive' {α : Type*} (x : Additive α) :
    Additive.ofMul (Additive.toMul x) = x :=
  Equiv.apply_symm_apply Additive.ofMul x

/-- A degree-`0` `Ext`-class killing `1` is zero. -/
theorem dass_extH_zero_of_apply_one {G : Type} [Group G] {A : Rep.{0} Coeff G}
    (y : extH A 0) (h : (Abelian.Ext.homEquiv₀ y) (1 : Coeff) = 0) : y = 0 := by
  letI := A.hV2
  have hm : (Rep.Hom.hom (Abelian.Ext.homEquiv₀ y)).toLinearMap = 0 := by
    apply LinearMap.ext_ring
    rw [Representation.IntertwiningMap.toLinearMap_apply]
    exact h
  have hφ : Abelian.Ext.homEquiv₀ y = 0 := by
    apply Rep.hom_ext
    exact Representation.IntertwiningMap.ext hm
  rw [← Abelian.Ext.mk₀_homEquiv₀_apply y, hφ, Abelian.Ext.mk₀_zero]

/-- The Kummer datum at the place `w`, assembled from the two short exact sequences. -/
noncomputable def dass_localKummerDatumOf (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) (p : ℕ) [Fact p.Prime]
    (z : Rep.trivial Coeff (decompK (k := k) w) (ZMod p) ⟶ localUnitsK (k := k) w)
    (hz : z ≠ 0) : KummerDatum p (decompK (k := k) w) where
  A := localUnitsK (k := k) w
  P := localPthRep k K w p
  Q := localKummerQuot k K w p
  z := z
  pth := localPthMap k K w p
  hz0 := Classical.choose (localKummerSES1_shortExact k K w p z hz)
  incl := localPthIncl k K w p
  quot := localKummerQuotMap k K w p
  hiq := Classical.choose (localKummerSES2_shortExact k K w p)
  hS1 := Classical.choose_spec (localKummerSES1_shortExact k K w p z hz)
  hS2 := Classical.choose_spec (localKummerSES2_shortExact k K w p)

theorem dass_local_kummer_dies (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K)
    (z : Rep.trivial Coeff (decompK (k := k) w) (ZMod p) ⟶ localUnitsK (k := k) w) (hz : z ≠ 0)
    (x : extH (Rep.trivial Coeff (decompK (k := k) w) (ZMod p)) 2)
    (hx : x.comp (Abelian.Ext.mk₀ z) (add_zero 2) = 0) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra k L) (_ : Algebra K L)
      (_ : IsScalarTower k K L) (_ : FiniteDimensional k L) (_ : IsGalois k L)
      (w' : NK.GlobalCFT.Place L) (_ : NK.GlobalCFT.Place.LiesOver w' w)
      (g : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
      (_ : ∀ σ, ((g σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L)),
      extHMap g (trivResInv g (ZMod p)) x = 0 := by
  classical
  -- the Kummer datum at the base level, and the two-step decomposition of `x`
  let D : KummerDatum p (decompK (k := k) w) := dass_localKummerDatumOf k K w p z hz
  have hA1 : Subsingleton (extH D.A 1) := subsingleton_extH_localUnitsK_one k K w
  obtain ⟨b, hb⟩ := kummerDatum_factor (D := D) hA1 x hx
  -- the value of `b`, lifted to `K_wˣ`
  set bval : (localUnitsK (k := k) w ⧸ localPthSub k K w p) :=
    (Abelian.Ext.homEquiv₀ b) (1 : Coeff) with hbval
  obtain ⟨b0a, hb0a⟩ := Submodule.mkQ_surjective (localPthSub k K w p) bval
  set b0u : (NK.GlobalCFT.Place.localField K w)ˣ := Additive.toMul b0a with hb0u
  have hb0 : Submodule.mkQ (localPthSub k K w p) (Additive.ofMul b0u) = bval := by
    change Submodule.mkQ (localPthSub k K w p)
      ((Additive.ofMul (Additive.toMul b0a) : localUnitsK (k := k) w)) = bval
    rw [dass_ofMul_toMul_additive']
    exact hb0a
  -- the level at which `b0u` becomes a `p`-th power
  obtain ⟨L, hFL, hNFL, hALk, hALK, hST, hFD, hGal, w', hw', y, hy⟩ :=
    exists_level_localPthPower p k K w b0u
  letI : Algebra k L := hALk
  letI : Algebra K L := hALK
  letI : IsScalarTower k K L := hST
  letI : FiniteDimensional k L := hFD
  letI : IsGalois k L := hGal
  -- the level data
  obtain ⟨g, hg⟩ := decompK_restrict_exists k K L w w' hw'
  obtain ⟨ι, hι⟩ := localUnitsMap_exists k K L w w' hw' g hg
  obtain ⟨-, z', hz', hz'val⟩ := localLevel_zetaCoeff p w w' hw' g hg ι hι z hz
  -- the level Kummer datum and the morphism of Kummer data
  let D' : KummerDatum p (decompK (k := k) w') := dass_localKummerDatumOf k L w' p z' hz'
  obtain ⟨⟨iP0, hs3, hs2⟩, ⟨iQ0, hs4, hiQval0⟩⟩ :=
    exists_localKummerLevelMaps k K L p w w' hw' g ι
  let iP : Rep.res g D.P ⟶ D'.P := iP0
  let iQ : Rep.res g D.Q ⟶ D'.Q := iQ0
  have hiQval : ∀ a : ↑(localUnitsK (k := k) w),
      (Rep.Hom.hom iQ) (Submodule.mkQ (localPthSub k K w p) a)
        = Submodule.mkQ (localPthSub k L w' p) ((Rep.Hom.hom ι) a) := hiQval0
  have sq1 : Rep.resMap g D.z ≫ ι = trivResInv g (ZMod p) ≫ D'.z := by
    refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext ?_))
    intro a
    show ι.hom (z.hom a) = z'.hom a
    exact (hz'val a).symm
  let F : KummerDatumHom g D D' :=
    { iA := ι, iP := iP, iQ := iQ, iz := trivResInv g (ZMod p),
      sq1 := sq1, sq2 := hs2, sq3 := hs3, sq4 := hs4 }
  have hbQ : extHMap g iQ b = 0 := by
    apply dass_extH_zero_of_apply_one
    rw [extHMap_homEquiv0_apply_one g iQ b]
    rw [← hbval, ← hb0]
    rw [hiQval (Additive.ofMul b0u), hι b0u, hy]
    change ((Submodule.mkQ (localPthSub k L w' p)) (Additive.ofMul (y ^ p)) :
      localUnitsK (k := k) w' ⧸ localPthSub k L w' p) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact (mem_localPthSub_iff k L w' p _).mpr
      ⟨Additive.ofMul y, nsmul_ofMul_eq _ p y⟩
  refine ⟨L, hFL, hNFL, hALk, hALK, hST, hFD, hGal, w', hw', g, hg, ?_⟩
  have hfin := kummerDatumHom_extHMap g D D' F b hbQ
  rw [hb]
  exact hfin

end

end Work.SSGRoute

