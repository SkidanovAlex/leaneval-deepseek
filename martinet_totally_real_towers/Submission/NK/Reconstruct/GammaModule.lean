import Submission.NK.Reconstruct.GammaObject
import Submission.NK.Reconstruct.GammaSup
import Submission.NK.Reconstruct.ellRestrict_surjective

/-!
# The topological `ℤ_ℓ`-module structure of `Γ_K`

Shimizu (arXiv:2009.10431, §4) uses that `Γ_K = (G_K^{ab,(ℓ)})/torsion` is a (pro)finite
`ℤ_ℓ`-module.  This file builds that structure on the object `NK.Reconstruct.Gamma K K' ℓ`
constructed in `GammaObject.lean`.

The construction is in three layers.

* **The canonical exponent.**  The ℓ-part `NK.Reconstruct.ellPart A ℓ` of a finite commutative
  group is a finite ℓ-group, so it is killed by some power of ℓ; the least such exponent is
  `NK.Reconstruct.ellExp A ℓ` (`NK.Reconstruct.exists_pow_ellPart_eq_one`,
  `NK.Reconstruct.pow_ellExp_eq_one`).  It is monotone under surjections:
  `NK.Reconstruct.ellExp_le_of_surjective`.
* **The level structure.**  A finite abelian group killed by `ℓ ^ N` is a `ZMod (ℓ ^ N)`-module
  (`AddCommGroup.zmodModule`), and pulling back along the ring homomorphism
  `PadicInt.toZModPow : ℤ_[ℓ] →+* ZMod (ℓ ^ N)` (`Module.compHom`) makes it a `ℤ_ℓ`-module:
  `NK.Reconstruct.instModuleAdditiveEllPart`.  The scalar action is computed explicitly in
  `NK.Reconstruct.smul_ellPart_eq_pow`: multiplication by `a : ℤ_ℓ` is the power map with
  exponent `(toZModPow N a).val`.
* **The limit.**  The transition maps `NK.Reconstruct.ellRestrict` are `ℤ_ℓ`-linear
  (`NK.Reconstruct.ellRestrictAdd_smul`, proved from the explicit computation of the action and
  from the compatibility `PadicInt.cast_toZModPow` of the reductions `ℤ_ℓ → ZMod (ℓ ^ N)`), so the
  carrier of `Γ_K` — cut out in the product of the finite levels by the equations
  `ellRestrict (f M) = f L` — is closed under the `ℤ_ℓ`-action, and
  `Function.Injective.module` gives the `Module (PadicInt ℓ) (Additive (Gamma K K' ℓ))` structure
  `NK.Reconstruct.instModuleAdditiveGamma`.

Nothing in the reconstruction uses this structure; it is part of item (1) of the deliverable (the
vocabulary of the abelianised route).
-/

set_option linter.unusedSectionVars false

namespace NK.Reconstruct

open scoped Pointwise

/-! ## The canonical exponent of an ℓ-part -/

/-- **The ℓ-part of a finite commutative group is killed by a power of ℓ.** -/
theorem exists_pow_ellPart_eq_one {A : Type*} [CommGroup A] [Finite A] (ℓ : ℕ) :
    ∃ N : ℕ, ∀ x : ellPart A ℓ, x ^ (ℓ ^ N) = 1 := by
  classical
  haveI := Fintype.ofFinite (ellPart A ℓ)
  have hx : ∀ x : ellPart A ℓ, ∃ n : ℕ, x ^ (ℓ ^ n) = 1 := fun x => by
    obtain ⟨n, hn⟩ := (mem_ellPart_iff ℓ (x : A)).mp x.2
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  refine ⟨(Finset.univ.sup fun x : ellPart A ℓ => (hx x).choose), fun x => ?_⟩
  have hle : (hx x).choose ≤ (Finset.univ.sup fun x : ellPart A ℓ => (hx x).choose) :=
    Finset.le_sup (f := fun x : ellPart A ℓ => (hx x).choose) (Finset.mem_univ x)
  rw [show ℓ ^ (Finset.univ.sup fun x : ellPart A ℓ => (hx x).choose)
      = ℓ ^ (hx x).choose * ℓ ^ ((Finset.univ.sup fun x : ellPart A ℓ => (hx x).choose)
          - (hx x).choose) from by rw [← pow_add, Nat.add_sub_of_le hle]]
  rw [pow_mul, (hx x).choose_spec, one_pow]

/-- **The canonical exponent of the ℓ-part** of a finite commutative group: the least `N` with
`x ^ (ℓ ^ N) = 1` for all `x` in the ℓ-part. -/
noncomputable def ellExp (A : Type*) [CommGroup A] [Finite A] (ℓ : ℕ) : ℕ := by
  classical
  exact Nat.find (exists_pow_ellPart_eq_one (A := A) ℓ)

/-- The defining property of `NK.Reconstruct.ellExp`. -/
theorem pow_ellExp_eq_one {A : Type*} [CommGroup A] [Finite A] (ℓ : ℕ) (x : ellPart A ℓ) :
    x ^ (ℓ ^ ellExp A ℓ) = 1 := by
  classical
  exact Nat.find_spec (exists_pow_ellPart_eq_one (A := A) ℓ) x

/-- **The canonical exponent is monotone under surjections**: a quotient cannot have a larger
exponent. -/
theorem ellExp_le_of_surjective {A B : Type*} [CommGroup A] [CommGroup B] [Finite A] [Finite B]
    (ℓ : ℕ) (f : A →* B) (hf : Function.Surjective f) : ellExp B ℓ ≤ ellExp A ℓ := by
  classical
  refine Nat.find_min' (exists_pow_ellPart_eq_one (A := B) ℓ) ?_
  intro x
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp
    (show (x : B) ∈ (ellPart A ℓ).map f from by
      rw [ellPart_map_eq_of_surjective ℓ f hf]
      exact x.2)
  refine Subtype.ext ?_
  rw [Subgroup.coe_pow, Subgroup.coe_one, ← hyx, ← map_pow]
  rw [show y ^ (ℓ ^ ellExp A ℓ) = 1 from by
    have := congrArg (fun z : ellPart A ℓ => (z : A)) (pow_ellExp_eq_one (A := A) ℓ ⟨y, hy⟩)
    simpa using this, map_one]

/-! ## The `ℤ_ℓ`-module structure on a finite ℓ-part -/

/-- A finite abelian group killed by `ℓ ^ N` is a `ZMod (ℓ ^ N)`-module. -/
noncomputable instance instModuleZModAdditiveEllPart {A : Type*} [CommGroup A] [Finite A] (ℓ : ℕ)
    [Fact ℓ.Prime] : Module (ZMod (ℓ ^ ellExp A ℓ)) (Additive (ellPart A ℓ)) :=
  AddCommGroup.zmodModule (fun x => by
    rw [← ofMul_toMul x, ← ofMul_pow, pow_ellExp_eq_one]
    rfl)

/-- **The canonical `ℤ_ℓ`-module structure on the ℓ-part**: the scalar action of `ℤ_ℓ` factors
through the reduction `ℤ_ℓ → ZMod (ℓ ^ N)`, `N = ellExp A ℓ`. -/
noncomputable instance instModuleAdditiveEllPart {A : Type*} [CommGroup A] [Finite A] (ℓ : ℕ)
    [Fact ℓ.Prime] : Module (PadicInt ℓ) (Additive (ellPart A ℓ)) :=
  Module.compHom (Additive (ellPart A ℓ)) (PadicInt.toZModPow (p := ℓ) (ellExp A ℓ))

/-- **The canonical `ZMod n`-scalar action is the power map with exponent the representative**:
for the module structure `AddCommGroup.zmodModule h` on a group killed by `n`, the scalar action of
`c : ZMod n` is the `c.val`-fold sum, i.e. (in multiplicative notation) the `c.val`-th power. -/
theorem zmodModule_smul_eq_val {n : ℕ} [NeZero n] {G : Type*} [AddCommGroup G]
    (h : ∀ x : G, n • x = 0) (c : ZMod n) (x : G) :
    (letI := AddCommGroup.zmodModule h; c • x) = c.val • x := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  rfl

/-- The `ZMod (ℓ ^ N)`-scalar action on an ℓ-part is the power map with exponent the representative
of the reduction. -/
theorem zmod_smul_ellPart_eq_val {A : Type*} [CommGroup A] [Finite A] (ℓ : ℕ) [Fact ℓ.Prime]
    (c : ZMod (ℓ ^ ellExp A ℓ)) (x : Additive (ellPart A ℓ)) :
    (letI := instModuleZModAdditiveEllPart (A := A) ℓ; c • x) = c.val • x :=
  zmodModule_smul_eq_val (n := ℓ ^ ellExp A ℓ)
    (G := Additive (ellPart A ℓ))
    (h := fun x => by
      rw [← ofMul_toMul x, ← ofMul_pow, pow_ellExp_eq_one]
      rfl) c x

/-- **The explicit scalar action of `ℤ_ℓ` on an ℓ-part**: multiplication by `a` is the power map
with exponent the representative `(PadicInt.toZModPow N a).val` of the reduction of `a` modulo
`ℓ ^ N`, where `N = NK.Reconstruct.ellExp`. -/
theorem smul_ellPart_eq_pow {A : Type*} [CommGroup A] [Finite A] (ℓ : ℕ) [Fact ℓ.Prime]
    (a : PadicInt ℓ) (x : ellPart A ℓ) :
    a • (Additive.ofMul x)
      = Additive.ofMul (x ^ (PadicInt.toZModPow (p := ℓ) (ellExp A ℓ) a).val) := by
  show (PadicInt.toZModPow (p := ℓ) (ellExp A ℓ) a) • (Additive.ofMul x) = _
  rw [show (PadicInt.toZModPow (p := ℓ) (ellExp A ℓ) a) • (Additive.ofMul x)
      = (PadicInt.toZModPow (p := ℓ) (ellExp A ℓ) a).val • (Additive.ofMul x) from
    zmod_smul_ellPart_eq_val ℓ _ _]
  rw [ofMul_pow]


/-! ## Linearity of the transition maps -/

section Level

variable {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K'] [Algebra K K']
  [IsGalois K K']

/-- The additive form of the transition map `NK.Reconstruct.ellRestrict`. -/
noncomputable def ellRestrictAdd (ℓ : ℕ) (L M : FrobLevel K K') (h : L.L ≤ M.L) :
    Additive (LevelEllPart M.L ℓ) →+ Additive (LevelEllPart L.L ℓ) :=
  (ellRestrict ℓ L M h).toAdditive

@[simp] theorem ellRestrictAdd_apply (ℓ : ℕ) (L M : FrobLevel K K') (h : L.L ≤ M.L)
    (x : Additive (LevelEllPart M.L ℓ)) :
    Additive.toMul (ellRestrictAdd ℓ L M h x) = ellRestrict ℓ L M h (Additive.toMul x) := rfl

/-- The canonical exponent of a level is at most that of any larger level (the ℓ-part of the
smaller level is a quotient of that of the larger one). -/
theorem ellExp_level_le (ℓ : ℕ) {L M : FrobLevel K K'} (h : L.L ≤ M.L) :
    ellExp (LevelAbelianization L.L) ℓ ≤ ellExp (LevelAbelianization M.L) ℓ :=
  ellExp_le_of_surjective ℓ (levelRestrict L M h) (levelRestrict_surjective L M h)

/-- **The transition maps of the tower are `ℤ_ℓ`-linear.** -/
theorem ellRestrictAdd_smul (ℓ : ℕ) [Fact ℓ.Prime] {L M : FrobLevel K K'} (h : L.L ≤ M.L)
    (a : PadicInt ℓ) (x : Additive (LevelEllPart M.L ℓ)) :
    ellRestrictAdd ℓ L M h (a • x) = a • ellRestrictAdd ℓ L M h x := by
  obtain ⟨y, rfl⟩ : ∃ y : LevelEllPart M.L ℓ, Additive.ofMul y = x :=
    ⟨Additive.toMul x, ofMul_toMul x⟩
  set Nl := ellExp (LevelAbelianization L.L) ℓ with hNl
  set Nm := ellExp (LevelAbelianization M.L) ℓ with hNm
  have hle : Nl ≤ Nm := ellExp_level_le ℓ h
  have hM : a • (Additive.ofMul y)
      = Additive.ofMul (y ^ (PadicInt.toZModPow (p := ℓ) Nm a).val) :=
    smul_ellPart_eq_pow (A := LevelAbelianization M.L) ℓ a y
  have hadd : ellRestrictAdd ℓ L M h (Additive.ofMul y)
      = Additive.ofMul (ellRestrict ℓ L M h y) := rfl
  have hL : a • (Additive.ofMul (ellRestrict ℓ L M h y))
      = Additive.ofMul ((ellRestrict ℓ L M h y) ^ (PadicInt.toZModPow (p := ℓ) Nl a).val) :=
    smul_ellPart_eq_pow (A := LevelAbelianization L.L) ℓ a _
  rw [hM, hadd, hL]
  show Additive.ofMul (ellRestrict ℓ L M h (y ^ (PadicInt.toZModPow (p := ℓ) Nm a).val))
      = Additive.ofMul ((ellRestrict ℓ L M h y) ^ (PadicInt.toZModPow (p := ℓ) Nl a).val)
  simp only [map_pow]
  congr 1
  rw [pow_eq_pow_iff_modEq]
  have hord : orderOf (ellRestrict ℓ L M h y) ∣ ℓ ^ Nl :=
    orderOf_dvd_of_pow_eq_one (pow_ellExp_eq_one (A := LevelAbelianization L.L) ℓ _)
  refine Nat.ModEq.of_dvd hord ?_
  rw [← ZMod.natCast_eq_natCast_iff]
  have hVM : ((PadicInt.toZModPow (p := ℓ) Nm a).val : ZMod (ℓ ^ Nl))
      = PadicInt.toZModPow (p := ℓ) Nl a := by
    rw [← ZMod.cast_natCast (R := ZMod (ℓ ^ Nl)) (m := ℓ ^ Nl) (n := ℓ ^ Nm)
      (pow_dvd_pow ℓ hle) ((PadicInt.toZModPow (p := ℓ) Nm a).val)]
    rw [ZMod.natCast_zmod_val]
    exact PadicInt.cast_toZModPow Nl Nm hle a
  rw [hVM, ZMod.natCast_zmod_val]

end Level

/-! ## The `ℤ_ℓ`-module structure on the limit `Γ_K` -/

section Gamma

variable {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K'] [Algebra K K']
  [IsGalois K K'] {ℓ : ℕ} [Fact ℓ.Prime]

/-- **The compatible families are closed under the `ℤ_ℓ`-action**: this is the coherence
computation that makes `Γ_K` a `ℤ_ℓ`-module, using the linearity of the transition maps
(`NK.Reconstruct.ellRestrictAdd_smul`) and the compatibility of the family. -/
theorem compatible_smul (a : PadicInt ℓ) (F : Gamma K K' ℓ) :
    Compatible ℓ fun L => Additive.toMul (a • Additive.ofMul (F.1 L)) := by
  intro L M h
  show ellRestrict ℓ L M h (Additive.toMul (a • Additive.ofMul (F.1 M)))
      = Additive.toMul (a • Additive.ofMul (F.1 L))
  rw [← ellRestrictAdd_apply ℓ L M h (a • Additive.ofMul (F.1 M)),
    ellRestrictAdd_smul ℓ h a (Additive.ofMul (F.1 M))]
  show Additive.toMul (a • ellRestrictAdd ℓ L M h (Additive.ofMul (F.1 M)))
      = Additive.toMul (a • Additive.ofMul (F.1 L))
  rw [show ellRestrictAdd ℓ L M h (Additive.ofMul (F.1 M)) = Additive.ofMul (F.1 L) from by
    rw [← F.2 L M h]
    rfl]

/-- The `ℤ_ℓ`-action on the limit `Γ_K`, defined componentwise. -/
noncomputable instance instSMulAdditiveGamma :
    SMul (PadicInt ℓ) (Additive (Gamma K K' ℓ)) where
  smul a F := Additive.ofMul
    ⟨fun L => Additive.toMul (a • Additive.ofMul ((Additive.toMul F).1 L)),
      compatible_smul a (Additive.toMul F)⟩

/-- The inclusion of `Γ_K` into the product of its finite levels, additively. -/
noncomputable def gammaAddHom :
    Additive (Gamma K K' ℓ) →+ (∀ L : FrobLevel K K', Additive (LevelEllPart L.L ℓ)) where
  toFun F := fun L => Additive.ofMul ((Additive.toMul F).1 L)
  map_zero' := by funext L; rfl
  map_add' a b := by funext L; rfl

theorem gammaAddHom_injective : Function.Injective (gammaAddHom (K := K) (K' := K') (ℓ := ℓ)) := by
  intro a b h
  have h1 : (Additive.toMul a).1 = (Additive.toMul b).1 := by
    have := funext_iff.mp h
    funext L
    have hL := congrArg (fun z => Additive.toMul (z L)) h
    simpa [gammaAddHom] using hL
  exact Additive.toMul.injective (Subtype.ext h1)

/-- **`Γ_K` is a `ℤ_ℓ`-module.**  The structure is obtained from the product of the finite levels
(a `ℤ_ℓ`-module) along the injective inclusion `Γ_K → ∏_L Γ_{L,ℓ}`
(`Function.Injective.module`), the scalar action being the componentwise one
(`NK.Reconstruct.compatible_smul`). -/
noncomputable instance instModuleAdditiveGamma :
    Module (PadicInt ℓ) (Additive (Gamma K K' ℓ)) :=
  Function.Injective.module (PadicInt ℓ) (gammaAddHom (K := K) (K' := K') (ℓ := ℓ))
    (gammaAddHom_injective (K := K) (K' := K') (ℓ := ℓ)) (fun _ _ => rfl)

end Gamma

end NK.Reconstruct
