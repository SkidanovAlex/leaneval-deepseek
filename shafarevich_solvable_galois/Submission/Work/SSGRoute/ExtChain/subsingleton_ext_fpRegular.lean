import Mathlib
import Submission.Work.SSGRoute.ExtChain.ext_vanishing_fpRegular
import Submission.Work.SSGRoute.PT.pt_ext_shapiro
import Submission.Work.SSGRoute.ExtH1Defs
import Submission.Work.SSGRoute.phi1_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The dévissage base case `Ext^{≥2}_G(𝔽_p[G], A) = 0`

The coefficient sequence `0 → ℤ --p--> ℤ → 𝔽_p → 0`, tensored with the group algebra `ℤ[G]`,
gives the two-term free resolution of the regular `𝔽_p[G]`-module

    `0 → ℤ[G] --p--> ℤ[G] → 𝔽_p[G] → 0`,

whose middle term `ℤ[G]` is projective (it is the free `ℤ[G]`-module of rank one).  The long
exact sequence in the first variable therefore gives, for `n ≥ 1`,

    `Ext^n_G(ℤ[G], A) → Ext^{n+1}_G(𝔽_p[G], A) → Ext^{n+1}_G(ℤ[G], A)`,

and both outer terms vanish (`Ext^{≥1}` of the projective module `ℤ[G]`): the image of the
connecting map is all of `Ext^{n+1}_G(𝔽_p[G], A)` and it is a single point because its source is
trivial.  Hence `Ext^{≥2}_G(𝔽_p[G], A) = 0`.

Everything is checked elementwise on coefficients, through `MonoidAlgebra.coeff`; the reduction
`ℤ[G] → 𝔽_p[G]` is the coefficientwise `leftRegularReduceFun` of
`Submission.Work.SSGRoute.ExtChain.ext_vanishing_fpRegular`.
-/

namespace Work.SSGRoute.ExtChain

open CategoryTheory SSGRoute.PTExt

noncomputable section

variable (p : ℕ) (G : Type) [Group G]

/-! ## Coefficient computations on the group algebra -/

/-- Coefficients of a scalar multiple in `ℤ[G]`: the scalar acts coefficientwise. -/
theorem coeff_smul_leftRegular (c : Coeff) (x : MonoidAlgebra Coeff G) (a : G) :
    (c • x).coeff a = c * x.coeff a := by
  rw [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]

/-- Coefficients of a scalar multiple in `𝔽_p[G]`: the `Coeff = ULift ℤ`-action is the underlying
`ℤ`-action, hence coefficientwise multiplication by the image of the integer in `𝔽_p`. -/
theorem coeff_smul_zmod (c : Coeff) (y : MonoidAlgebra (ZMod p) G) (a : G) :
    (c • y).coeff a = (c.down : ZMod p) * y.coeff a := by
  rw [ULift.smul_def, ← Int.cast_smul_eq_zsmul (ZMod p) c.down]
  rw [Algebra.smul_def, MonoidAlgebra.coe_algebraMap]
  simp

/-- The reduction `ℤ[G] → 𝔽_p[G]` is `Coeff`-linear. -/
theorem leftRegularReduceFun_smul (c : Coeff) (x : MonoidAlgebra Coeff G) :
    leftRegularReduceFun p G (c • x) = c • leftRegularReduceFun p G x := by
  ext a
  rw [leftRegularReduceFun_coeff, coeff_smul_leftRegular, coeff_smul_zmod,
    leftRegularReduceFun_coeff, ULift.mul_down, Int.cast_mul]

/-- Multiplication by `p` is injective on `ℤ[G]`. -/
theorem smulByP_injective [Fact p.Prime] {x y : MonoidAlgebra Coeff G}
    (h : (p : Coeff) • x = (p : Coeff) • y) : x = y := by
  ext a
  have h' : (((p : Coeff) • x).coeff a).down = (((p : Coeff) • y).coeff a).down := by rw [h]
  simp only [coeff_smul_leftRegular, ULift.mul_down, ULift.down_natCast] at h'
  exact mul_left_cancel₀ (by exact_mod_cast (Fact.out : p.Prime).ne_zero : (p : ℤ) ≠ 0) h'

/-- The reduction kills `p`-multiples. -/
theorem leftRegularReduceFun_smulByP (x : MonoidAlgebra Coeff G) :
    leftRegularReduceFun p G ((p : Coeff) • x) = 0 := by
  rw [leftRegularReduceFun_smul]
  ext a
  rw [coeff_smul_zmod, leftRegularReduceFun_coeff, ULift.down_natCast]
  have hp0 : ((p : ℤ) : ZMod p) = 0 := by
    push_cast
    exact ZMod.natCast_self p
  rw [hp0, zero_mul]
  simp

/-- The reduction is surjective: lift each coefficient of `𝔽_p` to its canonical integer
representative. -/
theorem leftRegularReduceFun_mapRange_val (y : MonoidAlgebra (ZMod p) G) [NeZero p] :
    leftRegularReduceFun p G
      (MonoidAlgebra.ofCoeff
        (Finsupp.mapRange (fun c : ZMod p => ULift.up ((c.val : ℤ)))
          (by rw [ZMod.val_zero]; rfl) y.coeff)) = y := by
  ext a
  rw [leftRegularReduceFun_coeff, Finsupp.mapRange_apply, ULift.down_up]
  simpa using ZMod.natCast_zmod_val (y.coeff a)

/-- **Exactness at the middle term**: an element of `ℤ[G]` whose reduction modulo `p` vanishes is
a `p`-multiple. -/
theorem exists_smulByP_eq_of_reduce_eq_zero (x : MonoidAlgebra Coeff G)
    (hx : leftRegularReduceFun p G x = 0) :
    ∃ y : MonoidAlgebra Coeff G, (p : Coeff) • y = x := by
  have hx' : ∀ a : G, ((x.coeff a).down : ZMod p) = 0 := fun a => by
    have h := congrArg (fun z : MonoidAlgebra (ZMod p) G => z.coeff a) hx
    rw [leftRegularReduceFun_coeff, MonoidAlgebra.coeff_zero, Finsupp.coe_zero,
      Pi.zero_apply] at h
    exact h
  refine ⟨MonoidAlgebra.ofCoeff
    (Finsupp.mapRange (fun c : Coeff => ULift.up ((c.down : ℤ) / (p : ℤ)))
      (by rw [ULift.zero_down, Int.zero_ediv]; rfl) x.coeff), ?_⟩
  ext a
  rw [coeff_smul_leftRegular, ULift.mul_down, ULift.down_natCast, Finsupp.mapRange_apply,
    ULift.down_up]
  exact Int.mul_ediv_cancel'
    ((ZMod.intCast_zmod_eq_zero_iff_dvd (x.coeff a).down p).mp (hx' a))

/-! ## The two-term resolution of the regular `𝔽_p[G]`-module -/

/-- **Multiplication by `p`** on the regular representation `ℤ[G]`. -/
def regMulByP : Rep.leftRegular Coeff G ⟶ Rep.leftRegular Coeff G :=
  Rep.ofHom
    { toLinearMap := (p : Coeff) • (1 : MonoidAlgebra Coeff G →ₗ[Coeff] MonoidAlgebra Coeff G)
      isIntertwining' := fun g => by ext x; simp }

/-- The underlying map of `regMulByP` is multiplication by `p`. -/
@[simp] theorem regMulByP_apply (x : Rep.leftRegular Coeff G) :
    Rep.Hom.hom (regMulByP p G) x = (p : Coeff) • x := rfl

/-- The underlying map of `regMulByP`, as a function on the group algebra. -/
theorem regMulByP_hom_coe (x : MonoidAlgebra Coeff G) :
    (⇑(Rep.Hom.hom (regMulByP p G))) x = (p : Coeff) • x := rfl

/-- **The reduction** `ℤ[G] → 𝔽_p[G]`, coefficientwise (`leftRegularReduceFun`), as a morphism of
`G`-representations with coefficients `Coeff = ULift ℤ`. -/
def regReduce : Rep.leftRegular Coeff G ⟶ modRep G (MonoidAlgebra (ZMod p) G) :=
  Rep.ofHom
    { toLinearMap :=
      { toFun := leftRegularReduceFun p G
        map_add' := fun x y => by ext a; simp [leftRegularReduceFun]
        map_smul' := fun (c : Coeff) (x : MonoidAlgebra Coeff G) =>
          leftRegularReduceFun_smul p G c x }
      isIntertwining' := fun g => by
        apply LinearMap.ext; intro x; ext a; simp [Representation.coeff_ofMulAction] }

/-- The underlying map of `regReduce` is the coefficientwise reduction. -/
@[simp] theorem regReduce_apply (x : MonoidAlgebra Coeff G) :
    Rep.Hom.hom (regReduce p G) x = leftRegularReduceFun p G x := rfl

/-- The underlying map of `regReduce`, as a function on the group algebra. -/
theorem regReduce_hom_coe (x : MonoidAlgebra Coeff G) :
    (⇑(Rep.Hom.hom (regReduce p G))) x = leftRegularReduceFun p G x := rfl

/-! ## The short exact sequence -/

/-- **The two-term resolution** `0 → ℤ[G] --p--> ℤ[G] → 𝔽_p[G] → 0` in `Rep Coeff G`. -/
def coeffSESReg : ShortComplex (Rep.{0, 0, 0} Coeff G) :=
  ShortComplex.mk (regMulByP p G) (regReduce p G) (by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    show (⇑(Rep.Hom.hom (regReduce p G))) ((⇑(Rep.Hom.hom (regMulByP p G))) x) = 0
    rw [regMulByP_hom_coe, regReduce_hom_coe]
    exact leftRegularReduceFun_smulByP p G x)

/-- The first map of the resolution is injective. -/
theorem mono_regMulByP [Fact p.Prime] : Mono (regMulByP p G) := by
  rw [Rep.mono_iff_injective]
  intro x y h
  exact smulByP_injective p G h

/-- The second map of the resolution is surjective. -/
theorem epi_regReduce [Fact p.Prime] : Epi (regReduce p G) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [Rep.epi_iff_surjective]
  intro y
  exact ⟨_, leftRegularReduceFun_mapRange_val p G y⟩

/-- Exactness at the middle term of the resolution. -/
theorem exact_regReduce {x : Rep.leftRegular Coeff G}
    (hx : (⇑(Rep.Hom.hom (regReduce p G))) x = 0) :
    ∃ y, (⇑(Rep.Hom.hom (regMulByP p G))) y = x := by
  rw [regReduce_hom_coe] at hx
  obtain ⟨y, hy⟩ := exists_smulByP_eq_of_reduce_eq_zero p G x hx
  exact ⟨y, hy⟩

/-- **The two-term resolution of `𝔽_p[G]` is short exact.** -/
theorem coeffSESReg_shortExact [Fact p.Prime] : (coeffSESReg p G).ShortExact := by
  refine Commons.RepresentationTheory.GroupCohomology.shortExact_of_mono_epi_elementwise
    (k := Coeff) (G := G) (coeffSESReg p G) (mono_regMulByP p G) (epi_regReduce p G) ?_
  intro x hx
  exact exact_regReduce p G hx

/-! ## Dimension shifting -/

universe u v

/-- **Dimension shifting.**  If `0 → S.X₁ → S.X₂ → S.X₃ → 0` is short exact in an abelian category
with `S.X₁` and `S.X₂` projective, then `Ext^{n+2}(S.X₃, Y) = 0` for every `Y`, every `n`: in the
long exact sequence in the first variable,

    `Ext^{n+1}(S.X₁, Y) → Ext^{n+2}(S.X₃, Y) → Ext^{n+2}(S.X₂, Y)`

the outer terms vanish, so the connecting map is onto and its source is trivial. -/
theorem subsingleton_ext_add_two_of_projective {C : Type u} [Category.{v} C] [Abelian C]
    [HasExt C] (S : ShortComplex C) (hS : S.ShortExact) [Projective S.X₁] [Projective S.X₂]
    (Y : C) (n : ℕ) : Subsingleton (Abelian.Ext S.X₃ Y (n + 2)) := by
  have h₂ : Function.Exact
      (⇑(hS.extClass.precomp Y (show 1 + (n + 1) = n + 1 + 1 by omega) :
        Abelian.Ext S.X₁ Y (n + 1) →+ Abelian.Ext S.X₃ Y (n + 1 + 1)))
      (⇑((Abelian.Ext.mk₀ S.g).precomp Y (zero_add (n + 1 + 1)) :
        Abelian.Ext S.X₃ Y (n + 1 + 1) →+ Abelian.Ext S.X₂ Y (n + 1 + 1))) :=
    (ShortComplex.ab_exact_iff_function_exact _).mp
      (CategoryTheory.Abelian.Ext.contravariant_sequence_exact₃' hS Y (n + 1) (n + 1 + 1)
        (by omega))
  haveI : Subsingleton (Abelian.Ext S.X₁ Y (n + 1)) :=
    Abelian.Ext.subsingleton_of_projective S.X₁ Y n
  haveI : Subsingleton (Abelian.Ext S.X₂ Y (n + 1 + 1)) :=
    Abelian.Ext.subsingleton_of_projective S.X₂ Y (n + 1)
  have key : ∀ z : Abelian.Ext S.X₃ Y (n + 2),
      z ∈ Set.range (hS.extClass.precomp Y (show 1 + (n + 1) = n + 1 + 1 by omega)) :=
    fun z => (h₂ z).mp (Subsingleton.elim _ _)
  refine ⟨fun a b => ?_⟩
  obtain ⟨a', ha'⟩ := key a
  obtain ⟨b', hb'⟩ := key b
  rw [← ha', ← hb', Subsingleton.elim a' b']

/-- **The dévissage base case.**  For the *regular* `𝔽_p[G]`-module (the free module of rank one)
`Ext^{≥2}` with coefficients in any `A` vanishes. -/
theorem subsingleton_ext_fpRegular (p : ℕ) [Fact p.Prime] (G : Type) [Group G]
    (A : Rep.{0, 0, 0} SSGRoute.PTExt.Coeff G) (r : ℕ) (hr : 2 ≤ r) :
    Subsingleton (CategoryTheory.Abelian.Ext.{0}
      (SSGRoute.PTExt.modRep G (MonoidAlgebra (ZMod p) G)) A r) := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- both ends of the resolution `0 → ℤ[G] --p--> ℤ[G] → 𝔽_p[G] → 0` are the free (hence
  -- projective) module `ℤ[G]`
  haveI hP₁ : Projective (coeffSESReg p G).X₁ := Rep.leftRegular_projective
  haveI hP₂ : Projective (coeffSESReg p G).X₂ := Rep.leftRegular_projective
  exact subsingleton_ext_add_two_of_projective (C := Rep.{0, 0, 0} Coeff G)
    (S := coeffSESReg p G) (coeffSESReg_shortExact p G) A m

end

end Work.SSGRoute.ExtChain
