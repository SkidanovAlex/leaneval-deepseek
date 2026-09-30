import Mathlib
import Submission.Work.Pi6.HALG.defs
import Submission.Work.Pi6.EMZ.BocksteinCore
import Submission.Work.Pi6.BOCK.coeffSESShortExact
import Submission.Work.SSS.ExpTensLES
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The mod-2 Bockstein short exact sequence (area HALG)

For every topological space `X` and every `n`, the coefficient sequence
`0 → ℤ --·2--> ℤ --red--> ℤ/2 → 0` tensored with the (degreewise free) singular chain complex of
`X` is a short exact sequence of chain complexes, whose long exact homology sequence is

`… → H_{n+1}(X;ℤ) --·2--> H_{n+1}(X;ℤ) --red--> H_{n+1}(X;𝔽₂) --δ--> H_n(X;ℤ) --·2--> …`.

Cutting three consecutive terms out of it gives the Bockstein short exact sequence

`0 → H_{n+1}(X;ℤ)/2H_{n+1}(X;ℤ) --i--> H_{n+1}(X;𝔽₂) --p--> H_n(X;ℤ)[2] → 0`.

The chain-level input is `Work.Pi6.EMZ.bockSES 2 X` with `Work.Pi6.EMZ.bockSES_shortExact`
(short exactness of the coefficient sequence `Work.Pi6.EMZ.coeffSES 2` is
`Work.Pi6.BOCK.coeffSESShortExact`, using the degreewise freeness `Work.Pi6.EMZ.chZ_flat`).
The long exact sequence is `HomologicalComplex.HomologySequence`
(`ShortComplex.ShortExact.homology_exact₁/₂/₃`), and the two outer homology groups are identified
with `H_{n+1}(X;ℤ)` and `H_{n+1}(X;𝔽₂)` by `Work.Pi6.EMZ.expTensUnitHomologyIso` and
`Work.Pi6.EMZ.expTensCoeffAddEquiv`; the map `·2` on the first term is identified with
multiplication by `2` on homology by `homologyMap_bockSES_f`.

The three-term reduction of a long exact sequence is the elementary lemma `sesOfThreeExact`, and
the final pass from additive maps to `ℤ`-linear maps is `zLin`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.Pi6.HALG

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory

noncomputable section

/-! ## 0. An additive map between `ℤ`-modules is `ℤ`-linear -/

/-- An additive homomorphism between `ℤ`-modules is `ℤ`-linear (the `ℤ`-module structure on an
additive group is unique).  This bridge lets the whole argument be carried out with additive maps,
where no instance diamonds (module structure from a `ModuleCat` object versus `AddCommGroup`) can
arise, and only at the very end be turned into the `ℤ`-linear maps requested by `BocksteinTwo`. -/
def zLin {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module ℤ M] [Module ℤ N]
    (f : M →+ N) : M →ₗ[ℤ] N where
  toFun := f
  map_add' := f.map_add
  map_smul' := fun n x => by
    have h1 := Int.cast_smul_eq_zsmul ℤ n x
    have h2 := Int.cast_smul_eq_zsmul ℤ n (f x)
    simp only [Int.cast_id, RingHom.id_apply] at h1 h2 ⊢
    rw [h1, h2]
    exact f.map_zsmul n x

/-- Multiplication by `2` on a `ℤ`-module, evaluated. -/
theorem mulTwo_apply {M : ModuleCat ℤ} (x : ↥M) : (mulTwo M).hom x = (2 : ℤ) • x := by
  show ((2 : ℤ) • 𝟙 M).hom x = (2 : ℤ) • x
  rw [Work.Pi6.EMZ.smul_id_hom_apply 2 M x]

/-! ## 1. The map `·2` on the coefficient-extended chain complex, on homology -/

/-- Whiskering a chain complex with `·2` on the coefficients is `·2` on the coefficient-extended
complex. -/
theorem expTensHom_two_smul_id (K : ChainComplex (ModuleCat ℤ) ℕ) (M : ModuleCat ℤ) :
    Work.SSS.expTensHom K ((2 : ℤ) • 𝟙 M) = (2 : ℤ) • 𝟙 (Work.SSS.expTens K M) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.zsmul_f_apply, HomologicalComplex.id_f, Work.SSS.expTensHom_f]
  show K.X n ◁ ((2 : ℤ) • 𝟙 M) = (2 : ℤ) • 𝟙 (K.X n ⊗ M)
  rw [two_zsmul, MonoidalPreadditive.whiskerLeft_add, MonoidalCategory.whiskerLeft_id, two_zsmul]

/-- Multiplication by `2` on a chain complex induces multiplication by `2` on homology. -/
theorem homologyMap_two_smul_id (K : ChainComplex (ModuleCat ℤ) ℕ) (k : ℕ) :
    HomologicalComplex.homologyMap ((2 : ℤ) • 𝟙 K) k = mulTwo (K.homology k) := by
  have h : ((2 : ℤ) • 𝟙 K) = 𝟙 K + 𝟙 K := two_zsmul _
  rw [h, HomologicalComplex.homologyMap_add, HomologicalComplex.homologyMap_id]
  show 𝟙 (K.homology k) + 𝟙 (K.homology k) = mulTwo (K.homology k)
  rw [show mulTwo (K.homology k) = (2 : ℤ) • 𝟙 (K.homology k) from rfl, two_zsmul]

/-- **The first map of the Bockstein sequence is multiplication by `2` on `H_{k}(X;ℤ)`.** -/
theorem homologyMap_bockSES_f (X : Type) [TopologicalSpace X] (k : ℕ) :
    HomologicalComplex.homologyMap (Work.Pi6.EMZ.bockSES 2 X).f k
      = mulTwo ((Work.SSS.expTens (Work.Pi6.EMZ.chZ X) Work.Pi6.EMZ.zZ).homology k) := by
  rw [show (Work.Pi6.EMZ.bockSES 2 X).f
      = Work.SSS.expTensHom (Work.Pi6.EMZ.chZ X) ((2 : ℤ) • 𝟙 Work.Pi6.EMZ.zZ) from rfl,
    expTensHom_two_smul_id, homologyMap_two_smul_id]

/-! ## 2. Two general lemmas: conjugation of exactness, and the three-term reduction -/

/-- **Exactness is preserved by conjugation with additive isomorphisms.** -/
theorem Function.Exact.conjAdd {A B C A' B' C' : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    {f : A → B} {g : B → C} (h : Function.Exact f g) (eA : A ≃+ A') (eB : B ≃+ B') (eC : C ≃+ C') :
    Function.Exact (fun x => eB (f (eA.symm x))) (fun y => eC (g (eB.symm y))) := by
  intro y
  constructor
  · intro hy
    have hy' : eC (g (eB.symm y)) = 0 := hy
    have h1 : g (eB.symm y) = 0 := eC.injective (by rw [hy', map_zero])
    obtain ⟨x, hx⟩ := (h (eB.symm y)).mp h1
    refine ⟨eA x, ?_⟩
    show eB (f (eA.symm (eA x))) = y
    rw [AddEquiv.symm_apply_apply, hx, AddEquiv.apply_symm_apply]
  · rintro ⟨x, hx⟩
    have h2 : eB (f (eA.symm x)) = y := hx
    have h3 : g (eB.symm y) = 0 := by
      rw [← h2, AddEquiv.symm_apply_apply]
      exact (h (f (eA.symm x))).mpr ⟨eA.symm x, rfl⟩
    show eC (g (eB.symm y)) = 0
    rw [h3, map_zero]

/-- **The short exact sequence attached to three consecutive terms of a long exact sequence.**
If `A --f--> A --g--> B --δ--> A' --f'--> A'` is exact, then `g` induces an injection
`A/fA ↪ B` whose image is the kernel of the corestriction of `δ` to `ker f'`, so that

`0 → A/fA --i--> B --p--> ker f' → 0`

is short exact.  (Here `f` and `f'` are the two endomorphisms `·2` at the two degrees.) -/
theorem sesOfThreeExact {A B A' : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup A']
    (f : A →+ A) (g : A →+ B) (δ : B →+ A') (f' : A' →+ A')
    (h1 : Function.Exact f g) (h2 : Function.Exact g δ) (h3 : Function.Exact δ f') :
    ∃ (i : (A ⧸ f.range) →+ B) (p : B →+ ↥f'.ker),
      Function.Injective i ∧ Function.Exact (⇑i) (⇑p) ∧ Function.Surjective p := by
  have hkerg : f.range = g.ker := (Function.Exact.addMonoidHom_ker_eq h1).symm
  have hkergδ : g.range = δ.ker := (Function.Exact.addMonoidHom_ker_eq h2).symm
  have hkerδ : δ.range = f'.ker := (Function.Exact.addMonoidHom_ker_eq h3).symm
  have hle : f.range ≤ g.ker := hkerg ▸ le_refl _
  let i : (A ⧸ f.range) →+ B := QuotientAddGroup.lift f.range g hle
  let p : B →+ ↥f'.ker := δ.codRestrict f'.ker
    (fun x => by rw [← hkerδ]; exact AddMonoidHom.mem_range.mpr ⟨x, rfl⟩)
  have hi : Function.Injective i := by
    rw [← AddMonoidHom.ker_eq_bot_iff, AddSubgroup.eq_bot_iff_forall]
    intro z hz
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    have hx : g x = 0 := by simpa [i] using AddMonoidHom.mem_ker.mp hz
    exact (QuotientAddGroup.eq_zero_iff x).mpr (by rw [hkerg]; exact AddMonoidHom.mem_ker.mpr hx)
  have hp : Function.Surjective p := by
    intro y
    have hy : (y : A') ∈ δ.range := by rw [hkerδ]; exact y.2
    obtain ⟨x, hx⟩ := AddMonoidHom.mem_range.mp hy
    exact ⟨x, Subtype.ext (by simpa [p] using hx)⟩
  have hex : Function.Exact (⇑i) (⇑p) := by
    intro y
    constructor
    · intro hy
      have hy' : δ y = 0 := by simpa [p] using congrArg Subtype.val hy
      have hyg : y ∈ g.range := by rw [hkergδ]; exact AddMonoidHom.mem_ker.mpr hy'
      obtain ⟨x, hx⟩ := AddMonoidHom.mem_range.mp hyg
      refine ⟨QuotientAddGroup.mk x, ?_⟩
      rw [show i (QuotientAddGroup.mk x) = g x from QuotientAddGroup.lift_mk f.range hle x, hx]
    · rintro ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
      refine Subtype.ext ?_
      show δ (g x) = 0
      exact AddMonoidHom.mem_ker.mp (by rw [← hkergδ]; exact AddMonoidHom.mem_range.mpr ⟨x, rfl⟩)
  exact ⟨i, p, hi, hex, hp⟩

/-! ## 3. The Bockstein short exact sequence -/

/-- **The mod-2 Bockstein sequence**, with additive maps.  This is `BocksteinTwo` before the final
pass to `ℤ`-linear maps: the maps live in the quotient `H_{n+1}(X;ℤ)/2H_{n+1}(X;ℤ)` and the
subgroup `H_n(X;ℤ)[2]` of `2`-torsion. -/
theorem bocksteinAux (X : Type) [TopologicalSpace X] (n : ℕ) :
    ∃ (i : ↥(twoCok (HR ℤ X (n + 1))) →+ ↥(HR (ZMod 2) X (n + 1)))
      (p : ↥(HR (ZMod 2) X (n + 1)) →+ ↥(twoKer (HR ℤ X n))),
      Function.Injective i ∧ Function.Exact (⇑i) (⇑p) ∧ Function.Surjective p := by
  have hS : (Work.Pi6.EMZ.coeffSES 2).ShortExact :=
    Work.Pi6.BOCK.coeffSESShortExact 2 (by norm_num)
  have hSE : (Work.Pi6.EMZ.bockSES 2 X).ShortExact :=
    Work.Pi6.EMZ.bockSES_shortExact 2 (by norm_num) X hS
  have hij : (ComplexShape.down ℕ).Rel (n + 1) n := by simp [ComplexShape.down]
  -- exactness of the three consecutive terms of the long exact sequence
  have hE1 : Function.Exact
      (HomologicalComplex.homologyMap (Work.Pi6.EMZ.bockSES 2 X).f (n + 1)).hom.toAddMonoidHom
      (HomologicalComplex.homologyMap (Work.Pi6.EMZ.bockSES 2 X).g (n + 1)).hom.toAddMonoidHom :=
    LinearMap.exact_iff.mpr (hSE.homology_exact₂ (n + 1)).moduleCat_range_eq_ker.symm
  have hE2 : Function.Exact
      (HomologicalComplex.homologyMap (Work.Pi6.EMZ.bockSES 2 X).g (n + 1)).hom.toAddMonoidHom
      (hSE.δ (n + 1) n hij).hom.toAddMonoidHom :=
    LinearMap.exact_iff.mpr (hSE.homology_exact₃ (n + 1) n hij).moduleCat_range_eq_ker.symm
  have hE3 : Function.Exact
      (hSE.δ (n + 1) n hij).hom.toAddMonoidHom
      (HomologicalComplex.homologyMap (Work.Pi6.EMZ.bockSES 2 X).f n).hom.toAddMonoidHom :=
    LinearMap.exact_iff.mpr (hSE.homology_exact₁ (n + 1) n hij).moduleCat_range_eq_ker.symm
  -- the identifications of the homology of the three terms with `H(X;ℤ)` and `H(X;𝔽₂)`
  let e1 : ↥((Work.SSS.expTens (Work.Pi6.EMZ.chZ X) Work.Pi6.EMZ.zZ).homology (n + 1)) ≃+
      ↥(HR ℤ X (n + 1)) :=
    (Iso.toLinearEquiv (Work.Pi6.EMZ.expTensUnitHomologyIso X (n + 1))).toAddEquiv
  let e0 : ↥((Work.SSS.expTens (Work.Pi6.EMZ.chZ X) Work.Pi6.EMZ.zZ).homology n) ≃+
      ↥(HR ℤ X n) :=
    (Iso.toLinearEquiv (Work.Pi6.EMZ.expTensUnitHomologyIso X n)).toAddEquiv
  let e2 : ↥((Work.SSS.expTens (Work.Pi6.EMZ.chZ X) (Work.Pi6.EMZ.Mp 2)).homology (n + 1)) ≃+
      ↥(HR (ZMod 2) X (n + 1)) := Work.Pi6.EMZ.expTensCoeffAddEquiv 2 (by norm_num) X (n + 1)
  -- the conjugated maps
  let G : ↥(HR ℤ X (n + 1)) →+ ↥(HR (ZMod 2) X (n + 1)) :=
    e2.toAddMonoidHom.comp
      ((HomologicalComplex.homologyMap (Work.Pi6.EMZ.bockSES 2 X).g (n + 1)).hom.toAddMonoidHom.comp
        e1.symm.toAddMonoidHom)
  let Δ : ↥(HR (ZMod 2) X (n + 1)) →+ ↥(HR ℤ X n) :=
    e0.toAddMonoidHom.comp ((hSE.δ (n + 1) n hij).hom.toAddMonoidHom.comp e2.symm.toAddMonoidHom)
  -- the conjugated maps are the matrix entries announced
  have hF : (fun x : ↥(HR ℤ X (n + 1)) =>
        e1 ((HomologicalComplex.homologyMap (Work.Pi6.EMZ.bockSES 2 X).f (n + 1)).hom (e1.symm x)))
      = ⇑((mulTwo (HR ℤ X (n + 1))).hom.toAddMonoidHom) := by
    funext x
    show e1 ((HomologicalComplex.homologyMap (Work.Pi6.EMZ.bockSES 2 X).f (n + 1)).hom (e1.symm x))
      = (mulTwo (HR ℤ X (n + 1))).hom x
    rw [homologyMap_bockSES_f]
    rw [mulTwo_apply, mulTwo_apply]
    rw [two_zsmul, map_add, two_zsmul, AddEquiv.apply_symm_apply]
  have hF' : (fun x : ↥(HR ℤ X n) =>
        e0 ((HomologicalComplex.homologyMap (Work.Pi6.EMZ.bockSES 2 X).f n).hom (e0.symm x)))
      = ⇑((mulTwo (HR ℤ X n)).hom.toAddMonoidHom) := by
    funext x
    show e0 ((HomologicalComplex.homologyMap (Work.Pi6.EMZ.bockSES 2 X).f n).hom (e0.symm x))
      = (mulTwo (HR ℤ X n)).hom x
    rw [homologyMap_bockSES_f]
    rw [mulTwo_apply, mulTwo_apply]
    rw [two_zsmul, map_add, two_zsmul, AddEquiv.apply_symm_apply]
  have hG : (fun y : ↥(HR ℤ X (n + 1)) =>
        e2 ((HomologicalComplex.homologyMap (Work.Pi6.EMZ.bockSES 2 X).g (n + 1)).hom (e1.symm y)))
      = ⇑G := rfl
  have hΔ : (fun y : ↥(HR (ZMod 2) X (n + 1)) =>
        e0 ((hSE.δ (n + 1) n hij).hom (e2.symm y))) = ⇑Δ := rfl
  -- conjugation of the three exactness statements
  have c1 := Function.Exact.conjAdd hE1 e1 e1 e2
  have c2 := Function.Exact.conjAdd hE2 e1 e2 e0
  have c3 := Function.Exact.conjAdd hE3 e2 e0 e0
  have hex1 : Function.Exact ⇑((mulTwo (HR ℤ X (n + 1))).hom.toAddMonoidHom) ⇑G := by
    rw [← hF, ← hG]; exact c1
  have hex2 : Function.Exact (⇑G) (⇑Δ) := by
    rw [← hG, ← hΔ]; exact c2
  have hex3 : Function.Exact (⇑Δ) ⇑((mulTwo (HR ℤ X n)).hom.toAddMonoidHom) := by
    rw [← hΔ, ← hF']; exact c3
  obtain ⟨i, p, hi, hex, hp⟩ := sesOfThreeExact
    ((mulTwo (HR ℤ X (n + 1))).hom.toAddMonoidHom) G Δ
    ((mulTwo (HR ℤ X n)).hom.toAddMonoidHom) hex1 hex2 hex3
  exact ⟨i, p, hi, hex, hp⟩

/-- **The mod-2 Bockstein short exact sequence (area HALG).**

Write `Submission/Work/Pi6/HALG/bocksteinTwo.lean` (module `Submission.Work.Pi6.HALG.bocksteinTwo`,
namespace `Work.Pi6.HALG`), a sorry-free proof of `Work.Pi6.HALG.BocksteinTwo` (defined in
`Submission/Work/Pi6/HALG/defs.lean` as: for every space `X` and degree `n` there are `ℤ`-linear
maps `H_{n+1}(X;ℤ)/2H_{n+1}(X;ℤ) → H_{n+1}(X;𝔽₂) → H_n(X;ℤ)[2]` that are injective, exact in the
middle, and surjective). -/
theorem bocksteinTwo : Work.Pi6.HALG.BocksteinTwo := by
  classical
  refine ⟨fun X _ n => zLin (bocksteinAux X n).choose,
    fun X _ n => zLin (bocksteinAux X n).choose_spec.choose, ?_⟩
  intro X _ n
  exact (bocksteinAux X n).choose_spec.choose_spec

end

end Work.Pi6.HALG
