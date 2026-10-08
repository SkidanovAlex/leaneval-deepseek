import Mathlib
import Submission.Work.Hering.AppVIII.SemiLinDefs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Auxiliary material for the solvability of `semiLin K`

`K` is a finite field of characteristic two.  This file collects the definitions and elementary
lemmas used in `Submission.Work.Hering.AppVIII.semiLin_solvable`.

The group `semiLin K ≤ Equiv.Perm (K × K)` consists of the maps
`(x,y) ↦ (a₁ · Φ^i x, η x + a₂ · Φ^i y)` where `Φ = x ↦ x^2` is the Frobenius automorphism.

* `gammaLin K` : the group `Γ ≤ Equiv.Perm K` of semilinear maps `x ↦ a · Φ^i x` of `K`;
* `gammaSemilin K` : the hom `Γ →* (frobPermHom K).range` extracting the semilinear part `Φ^i`;
* `gammaScalar K` : the (abelian) subgroup of scalars `x ↦ a x` inside `Γ`;
* `semiFirst`, `semiSecond` : the two projections `semiLin K →* Γ`;
* `semiPsi` : the product hom `semiLin K →* Γ × Γ`, whose kernel is shown to be abelian;
* `shearSub K` : the abelian subgroup of shear maps `(x,y) ↦ (x, η x + y)` inside `semiLin K`.
-/

set_option autoImplicit false

noncomputable section

namespace Work.Hering.AppVIII

variable (K : Type*) [Field K] [CharP K 2] [Finite K]

/-! ## Powers of the Frobenius as permutations of `K` -/

theorem frobPerm_bij (n : ℤ) : Function.Bijective (fun x : K => (frobK K ^ n) x) :=
  ⟨fun _ _ h => (frobK K ^ n).injective h, fun y => ⟨(frobK K ^ (-n)) y, by simp⟩⟩

/-- The permutation `x ↦ Φ^n x` of `K`, where `Φ` is the Frobenius automorphism. -/
def frobPermFun (n : ℤ) : Equiv.Perm K :=
  Equiv.ofBijective (fun x : K => (frobK K ^ n) x) (frobPerm_bij K n)

theorem frobPermFun_apply (n : ℤ) (x : K) : frobPermFun K n x = (frobK K ^ n) x := rfl

/-- The powers of the Frobenius as a hom `ℤ →* Equiv.Perm K`. -/
def frobPermHom : Multiplicative ℤ →* Equiv.Perm K where
  toFun n := frobPermFun K n.toAdd
  map_one' := by
    apply Equiv.ext
    intro x
    rw [frobPermFun_apply, toAdd_one, frobK_pow_apply_zero]
    rfl
  map_mul' := by
    intro m n
    apply Equiv.ext
    intro x
    rw [frobPermFun_apply, Equiv.Perm.mul_def, Equiv.trans_apply, frobPermFun_apply,
      frobPermFun_apply, toAdd_mul, frobK_pow_apply_comp]

/-! ## The semilinear group `Γ ≤ Equiv.Perm K` -/

/-- The set of semilinear permutations `x ↦ a · Φ^i x` of `K` (with `a ≠ 0`). -/
def gammaSet : Set (Equiv.Perm K) :=
  {f | ∃ (a : K) (i : ℤ), a ≠ 0 ∧ ∀ x : K, f x = a * (frobK K ^ i) x}

theorem gammaSet_mul_mem {f g : Equiv.Perm K} (hf : f ∈ gammaSet K) (hg : g ∈ gammaSet K) :
    f * g ∈ gammaSet K := by
  obtain ⟨a, i, ha, hf'⟩ := hf
  obtain ⟨b, j, hb, hg'⟩ := hg
  refine ⟨a * (frobK K ^ i) b, i + j, mul_ne_zero ha (frobK_pow_ne_zero K i hb), fun x => ?_⟩
  rw [Equiv.Perm.mul_def, Equiv.trans_apply, hg', hf']
  simp only [map_mul, frobK_pow_apply_comp]
  ring

theorem gammaSet_inv_mem {f : Equiv.Perm K} (hf : f ∈ gammaSet K) : f⁻¹ ∈ gammaSet K := by
  obtain ⟨a, i, ha, hf'⟩ := hf
  refine ⟨((frobK K ^ (-i)) a)⁻¹, -i, inv_ne_zero (frobK_pow_ne_zero K (-i) ha), fun x => ?_⟩
  have key : f (((frobK K ^ (-i)) a)⁻¹ * (frobK K ^ (-i)) x) = x := by
    rw [hf']
    simp only [map_mul, map_inv₀, frobK_pow_apply_neg_comp]
    rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  show f.symm x = _
  exact (Equiv.symm_apply_eq f).mpr key.symm

/-- The semilinear group `Γ = {x ↦ a · Φ^i x} ≤ Equiv.Perm K`. -/
def gammaLin : Subgroup (Equiv.Perm K) where
  carrier := gammaSet K
  one_mem' := ⟨1, 0, one_ne_zero, fun x => by simp⟩
  mul_mem' := gammaSet_mul_mem K
  inv_mem' := gammaSet_inv_mem K

theorem gamma_one_ne_zero (f : gammaLin K) : f.1 1 ≠ 0 := by
  obtain ⟨a, i, ha, hf⟩ := f.2
  have h1 : f.1 1 = a := by simpa using hf 1
  rw [h1]; exact ha

/-- The "semilinear part" of an element of `Γ`: `x ↦ f x · (f 1)⁻¹`
(which equals `Φ^i` when `f = a Φ^i`). -/
def gammaHFun (f : gammaLin K) : Equiv.Perm K :=
  MulAction.toPermHom Kˣ K (Units.mk0 (f.1 1) (gamma_one_ne_zero K f))⁻¹ * f.1

theorem gammaHFun_apply (f : gammaLin K) (x : K) :
    gammaHFun K f x = (f.1 1)⁻¹ * f.1 x := by
  rw [gammaHFun, Equiv.Perm.mul_def, Equiv.trans_apply, MulAction.toPermHom_apply,
    MulAction.toPerm_apply, Units.smul_def, smul_eq_mul]
  simp

theorem gammaHFun_formula {f : gammaLin K} {a : K} {i : ℤ} (ha : a ≠ 0)
    (hf : ∀ x : K, f.1 x = a * (frobK K ^ i) x) (x : K) :
    gammaHFun K f x = (frobK K ^ i) x := by
  rw [gammaHFun_apply, hf x, hf 1]
  simp only [map_one, mul_one]
  rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]

theorem gammaHFun_mul (f g : gammaLin K) :
    gammaHFun K (f * g) = gammaHFun K f * gammaHFun K g := by
  obtain ⟨a, i, ha, hf⟩ := f.2
  obtain ⟨b, j, hb, hg⟩ := g.2
  have hfg : ∀ y : K, (f * g).1 y = (a * (frobK K ^ i) b) * (frobK K ^ (i + j)) y := by
    intro y
    rw [Subgroup.coe_mul, Equiv.Perm.mul_def, Equiv.trans_apply, hg y,
      hf (b * (frobK K ^ j) y)]
    simp only [map_mul, frobK_pow_apply_comp]
    ring
  apply Equiv.ext
  intro x
  rw [gammaHFun_formula K (mul_ne_zero ha (frobK_pow_ne_zero K i hb)) hfg x,
    Equiv.Perm.mul_def, Equiv.trans_apply, gammaHFun_formula K ha hf,
    gammaHFun_formula K hb hg, frobK_pow_apply_comp]

theorem gammaHFun_one : gammaHFun K (1 : gammaLin K) = 1 := by
  apply Equiv.ext
  intro x
  rw [gammaHFun_apply]
  simp

/-- The hom `Γ →* Equiv.Perm K` extracting the semilinear part `Φ^i` of `a Φ^i ∈ Γ`. -/
def gammaH : gammaLin K →* Equiv.Perm K where
  toFun := gammaHFun K
  map_one' := gammaHFun_one K
  map_mul' := gammaHFun_mul K

theorem gammaH_apply (f : gammaLin K) (x : K) :
    gammaH K f x = (f.1 1)⁻¹ * f.1 x :=
  gammaHFun_apply K f x

theorem gammaH_formula {f : gammaLin K} {a : K} {i : ℤ} (ha : a ≠ 0)
    (hf : ∀ x : K, f.1 x = a * (frobK K ^ i) x) (x : K) :
    gammaH K f x = (frobK K ^ i) x :=
  gammaHFun_formula K ha hf x

theorem gammaH_mem (f : gammaLin K) : gammaH K f ∈ (frobPermHom K).range := by
  obtain ⟨a, i, ha, hf⟩ := f.2
  rw [MonoidHom.mem_range]
  refine ⟨Multiplicative.ofAdd i, ?_⟩
  apply Equiv.ext
  intro x
  show frobPermFun K i x = gammaH K f x
  rw [frobPermFun_apply, gammaH_formula K ha hf]

/-- The semilinear part as a hom into the image of `ℤ → Equiv.Perm K`, `i ↦ Φ^i`. -/
def gammaSemilin : gammaLin K →* (frobPermHom K).range :=
  (gammaH K).codRestrict _ (gammaH_mem K)

theorem gammaSemilin_coe (f : gammaLin K) :
    ((gammaSemilin K f : (frobPermHom K).range) : Equiv.Perm K) = gammaH K f := rfl

theorem gammaSemilin_apply (f : gammaLin K) (x : K) :
    ((gammaSemilin K f : (frobPermHom K).range) : Equiv.Perm K) x = (f.1 1)⁻¹ * f.1 x :=
  gammaH_apply K f x

instance frobRange_isSolvable : Group.IsSolvable ↥(frobPermHom K).range :=
  Group.isSolvable_of_surjective (MonoidHom.rangeRestrict_surjective (frobPermHom K))

/-! ## The scalar subgroup of `Γ` -/

/-- The scalar permutation `x ↦ a · x` attached to a unit `a`, as an element of `Γ`. -/
def scalarGammaFun (u : Kˣ) : gammaLin K :=
  ⟨MulAction.toPermHom Kˣ K u, by
    refine ⟨(u : K), 0, Units.ne_zero u, fun x => ?_⟩
    rw [MulAction.toPermHom_apply, MulAction.toPerm_apply, Units.smul_def, smul_eq_mul]
    simp⟩

theorem scalarGammaFun_apply (u : Kˣ) (x : K) :
    ((scalarGammaFun K u : gammaLin K) : Equiv.Perm K) x = (u : K) * x := by
  show (MulAction.toPermHom Kˣ K u) x = (u : K) * x
  rw [MulAction.toPermHom_apply, MulAction.toPerm_apply, Units.smul_def, smul_eq_mul]

/-- The scalars as a hom `Kˣ →* Γ`. -/
def scalarGamma : Kˣ →* gammaLin K where
  toFun := scalarGammaFun K
  map_one' := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    rw [scalarGammaFun_apply]
    simp
  map_mul' := by
    intro u v
    apply Subtype.ext
    apply Equiv.ext
    intro x
    rw [scalarGammaFun_apply, Subgroup.coe_mul, Equiv.Perm.mul_def, Equiv.trans_apply,
      scalarGammaFun_apply, scalarGammaFun_apply]
    rw [Units.val_mul, mul_assoc]

theorem scalarGamma_apply (u : Kˣ) (x : K) :
    ((scalarGamma K u : gammaLin K) : Equiv.Perm K) x = (u : K) * x :=
  scalarGammaFun_apply K u x

/-- The subgroup `Λ ≤ Γ` of scalar maps `x ↦ a x`. -/
def gammaScalar : Subgroup (gammaLin K) :=
  (scalarGamma K).range

instance gammaScalar_isSolvable : Group.IsSolvable ↥(gammaScalar K) :=
  Group.isSolvable_of_surjective (MonoidHom.rangeRestrict_surjective (scalarGamma K))

theorem gammaSemilin_ker : (gammaSemilin K).ker = gammaScalar K := by
  ext f
  constructor
  · intro hf
    rw [MonoidHom.mem_ker] at hf
    have h1 : gammaH K f = 1 := by
      have h2 := congrArg (fun g : (frobPermHom K).range => (g : Equiv.Perm K)) hf
      rwa [gammaSemilin_coe, Subgroup.coe_one] at h2
    have hx : ∀ x : K, f.1 x = (f.1 1) * x := by
      intro x
      have h2 : gammaH K f x = x := by rw [h1]; rfl
      rw [gammaH_apply] at h2
      rw [← congrArg (fun z => (f.1 1) * z) h2, ← mul_assoc,
        mul_inv_cancel₀ (gamma_one_ne_zero K f), one_mul]
    rw [gammaScalar, MonoidHom.mem_range]
    refine ⟨Units.mk0 (f.1 1) (gamma_one_ne_zero K f), ?_⟩
    apply Subtype.ext
    apply Equiv.ext
    intro x
    rw [scalarGamma_apply, hx x]
    simp
  · intro hf
    rw [gammaScalar, MonoidHom.mem_range] at hf
    obtain ⟨u, hu⟩ := hf
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    apply Equiv.ext
    intro x
    rw [gammaSemilin_coe, Subgroup.coe_one, gammaH_apply, ← hu, scalarGamma_apply,
      scalarGamma_apply, mul_one]
    show (↑u : K)⁻¹ * ((↑u : K) * x) = x
    rw [← mul_assoc, inv_mul_cancel₀ (Units.ne_zero u), one_mul]

instance gammaLin_isSolvable : Group.IsSolvable (gammaLin K) :=
  Group.isSolvable_of_ker_le_range (gammaScalar K).subtype (gammaSemilin K)
    (le_of_eq (by rw [Subgroup.range_subtype]; exact gammaSemilin_ker K))

/-! ## The abelian subgroup of shear maps of `semiLin K` -/

/-- The subgroup of shear maps `(x,y) ↦ (x, η x + y)` inside `semiLin K`. -/
def shearSub : Subgroup (semiLin K) :=
  (shearLin K).comap (semiLin K).subtype

theorem mem_shearSub_iff (f : semiLin K) :
    f ∈ shearSub K ↔ ∃ η : K → K, ∀ x y : K, f.1 (x, y) = (x, η x + y) :=
  Subgroup.mem_comap

/-! ## The two projections `semiLin K →* Γ` -/

theorem semiFirst_bij (f : semiLin K) : Function.Bijective (fun x : K => (f.1 (x, 0)).1) := by
  obtain ⟨a₁, a₂, ha₁, ha₂, i, η, hf⟩ := f.2
  constructor
  · intro x y hxy
    have h2 : a₁ * (frobK K ^ i) x = a₁ * (frobK K ^ i) y := by
      simpa only [hf x 0, hf y 0] using hxy
    exact (frobK K ^ i).injective (mul_left_cancel₀ ha₁ h2)
  · intro y
    refine ⟨(frobK K ^ (-i)) (a₁⁻¹ * y), ?_⟩
    show (f.1 ((frobK K ^ (-i)) (a₁⁻¹ * y), 0)).1 = y
    rw [hf _ 0]
    simp only [frobK_pow_apply_neg_comp]
    rw [← mul_assoc, mul_inv_cancel₀ ha₁, one_mul]

/-- The first projection `x ↦ (f (x,0)).1` of an element of `semiLin K`, as a permutation. -/
def semiFirstPerm (f : semiLin K) : Equiv.Perm K :=
  Equiv.ofBijective (fun x : K => (f.1 (x, 0)).1) (semiFirst_bij K f)

theorem semiFirstPerm_apply (f : semiLin K) (x : K) :
    semiFirstPerm K f x = (f.1 (x, 0)).1 := rfl

theorem semiFirstPerm_formula {f : semiLin K} {a₁ a₂ : K} {i : ℤ} {η : K → K}
    (hf : ∀ x y : K, f.1 (x, y) = (a₁ * (frobK K ^ i) x, η x + a₂ * (frobK K ^ i) y))
    (x : K) : semiFirstPerm K f x = a₁ * (frobK K ^ i) x := by
  show (f.1 (x, 0)).1 = a₁ * (frobK K ^ i) x
  rw [hf x 0]

theorem semiFirstPerm_mem (f : semiLin K) : semiFirstPerm K f ∈ gammaSet K := by
  obtain ⟨a₁, a₂, ha₁, ha₂, i, η, hf⟩ := f.2
  exact ⟨a₁, i, ha₁, fun x => semiFirstPerm_formula K hf x⟩

theorem semiFirst_mul (f g : semiLin K) :
    semiFirstPerm K (f * g) = semiFirstPerm K f * semiFirstPerm K g := by
  obtain ⟨a₁, a₂, ha₁, ha₂, i, η, hf⟩ := f.2
  apply Equiv.ext
  intro x
  have h1 : f.1 (g.1 (x, 0)) = f.1 ((g.1 (x, 0)).1, (g.1 (x, 0)).2) := by
    rw [Prod.eta]
  show (f.1 (g.1 (x, 0))).1 = (semiFirstPerm K f * semiFirstPerm K g) x
  rw [Equiv.Perm.mul_def, Equiv.trans_apply, semiFirstPerm_apply, semiFirstPerm_apply]
  rw [h1, hf (g.1 (x, 0)).1 (g.1 (x, 0)).2, hf (g.1 (x, 0)).1 0]

/-- The first projection `semiLin K →* Γ`, `f ↦ (x ↦ (f (x,0)).1)`. -/
def semiFirst : semiLin K →* gammaLin K where
  toFun f := ⟨semiFirstPerm K f, semiFirstPerm_mem K f⟩
  map_one' := by
    apply Subtype.ext
    show semiFirstPerm K 1 = 1
    apply Equiv.ext
    intro x
    simp [semiFirstPerm_apply]
  map_mul' := by
    intro f g
    apply Subtype.ext
    show semiFirstPerm K (f * g) = semiFirstPerm K f * semiFirstPerm K g
    exact semiFirst_mul K f g

theorem semiSecond_bij (f : semiLin K) :
    Function.Bijective (fun y : K => (f.1 (0, y)).2 - (f.1 (0, 0)).2) := by
  obtain ⟨a₁, a₂, ha₁, ha₂, i, η, hf⟩ := f.2
  constructor
  · intro x y hxy
    have h2 : a₂ * (frobK K ^ i) x = a₂ * (frobK K ^ i) y := by
      simpa only [hf 0 x, hf 0 y, hf 0 0, map_zero, mul_zero, add_zero,
        add_sub_cancel_left] using hxy
    exact (frobK K ^ i).injective (mul_left_cancel₀ ha₂ h2)
  · intro y
    refine ⟨(frobK K ^ (-i)) (a₂⁻¹ * y), ?_⟩
    show (f.1 (0, (frobK K ^ (-i)) (a₂⁻¹ * y))).2 - (f.1 (0, 0)).2 = y
    rw [hf 0 _, hf 0 0]
    simp only [map_zero, mul_zero, add_zero, frobK_pow_apply_neg_comp]
    rw [add_sub_cancel_left, ← mul_assoc, mul_inv_cancel₀ ha₂, one_mul]

/-- The second projection `y ↦ (f (0,y)).2 - (f (0,0)).2` of `semiLin K`, as a permutation. -/
def semiSecondPerm (f : semiLin K) : Equiv.Perm K :=
  Equiv.ofBijective (fun y : K => (f.1 (0, y)).2 - (f.1 (0, 0)).2) (semiSecond_bij K f)

theorem semiSecondPerm_apply (f : semiLin K) (y : K) :
    semiSecondPerm K f y = (f.1 (0, y)).2 - (f.1 (0, 0)).2 := rfl

theorem semiSecondPerm_formula {f : semiLin K} {a₁ a₂ : K} {i : ℤ} {η : K → K}
    (hf : ∀ x y : K, f.1 (x, y) = (a₁ * (frobK K ^ i) x, η x + a₂ * (frobK K ^ i) y))
    (y : K) : semiSecondPerm K f y = a₂ * (frobK K ^ i) y := by
  show (f.1 (0, y)).2 - (f.1 (0, 0)).2 = a₂ * (frobK K ^ i) y
  rw [hf 0 y, hf 0 0]
  simp only [map_zero, mul_zero, add_zero]
  rw [add_sub_cancel_left]

theorem semiSecondPerm_mem (f : semiLin K) : semiSecondPerm K f ∈ gammaSet K := by
  obtain ⟨a₁, a₂, ha₁, ha₂, i, η, hf⟩ := f.2
  exact ⟨a₂, i, ha₂, fun y => semiSecondPerm_formula K hf y⟩

theorem semiSecond_mul (f g : semiLin K) :
    semiSecondPerm K (f * g) = semiSecondPerm K f * semiSecondPerm K g := by
  obtain ⟨a₁, a₂, ha₁, ha₂, i, η, hf⟩ := f.2
  obtain ⟨b₁, b₂, hb₁, hb₂, j, ζ, hg⟩ := g.2
  apply Equiv.ext
  intro y
  have hgy : g.1 (0, y) = (0, ζ 0 + b₂ * (frobK K ^ j) y) := by
    rw [hg 0 y]
    simp
  have hg0 : g.1 (0, 0) = (0, ζ 0) := by
    rw [hg 0 0]
    simp
  have hw : semiSecondPerm K g y = b₂ * (frobK K ^ j) y := semiSecondPerm_formula K hg y
  show (f.1 (g.1 (0, y))).2 - (f.1 (g.1 (0, 0))).2
      = (semiSecondPerm K f * semiSecondPerm K g) y
  rw [Equiv.Perm.mul_def, Equiv.trans_apply, semiSecondPerm_apply, hw]
  rw [hgy, hg0]
  rw [hf 0 (ζ 0 + b₂ * (frobK K ^ j) y), hf 0 (ζ 0), hf 0 (b₂ * (frobK K ^ j) y),
    hf 0 0]
  simp only [map_zero, map_add, mul_zero, mul_add, add_zero, map_mul, frobK_pow_apply_comp]
  ring

/-- The second projection `semiLin K →* Γ`, `f ↦ (y ↦ (f (0,y)).2 - (f (0,0)).2)`. -/
def semiSecond : semiLin K →* gammaLin K where
  toFun f := ⟨semiSecondPerm K f, semiSecondPerm_mem K f⟩
  map_one' := by
    apply Subtype.ext
    show semiSecondPerm K 1 = 1
    apply Equiv.ext
    intro y
    simp [semiSecondPerm_apply]
  map_mul' := by
    intro f g
    apply Subtype.ext
    show semiSecondPerm K (f * g) = semiSecondPerm K f * semiSecondPerm K g
    exact semiSecond_mul K f g

/-- The product of the two projections `semiLin K →* Γ × Γ`. -/
def semiPsi : semiLin K →* gammaLin K × gammaLin K :=
  (semiFirst K).prod (semiSecond K)


/-! ## Solvability of the shear subgroup -/

theorem shear_comm {f g : Equiv.Perm (K × K)} {η ζ : K → K}
    (hf : ∀ x y : K, f (x, y) = (x, η x + y)) (hg : ∀ x y : K, g (x, y) = (x, ζ x + y)) :
    f * g = g * f := by
  apply Equiv.ext
  rintro ⟨x, y⟩
  rw [Equiv.Perm.mul_def, Equiv.trans_apply, Equiv.Perm.mul_def, Equiv.trans_apply,
    hg x y, hf x (ζ x + y), hf x y, hg x (η x + y)]
  congr 1
  ring

theorem shearSub_isSolvable (K : Type*) [Field K] [CharP K 2] [Finite K] :
    Group.IsSolvable ↥(shearSub K) := by
  refine Group.isSolvable_of_comm (fun f g => ?_)
  obtain ⟨η, hf⟩ := (mem_shearSub_iff K f).mp f.2
  obtain ⟨ζ, hg⟩ := (mem_shearSub_iff K g).mp g.2
  rw [Subtype.ext_iff, Subtype.ext_iff]
  simp only [Subgroup.coe_mul]
  exact shear_comm K hf hg

/-! ## The kernel of `semiPsi` -/

theorem semiPsi_ker_le_shearSub (K : Type*) [Field K] [CharP K 2] [Finite K]
    (f : semiLin K) (hf : f ∈ (semiPsi K).ker) : f ∈ shearSub K := by
  rw [MonoidHom.mem_ker] at hf
  have h1 : semiFirst K f = 1 :=
    congrArg (fun p : gammaLin K × gammaLin K => p.1) hf
  have h2 : semiSecond K f = 1 :=
    congrArg (fun p : gammaLin K × gammaLin K => p.2) hf
  obtain ⟨a₁, a₂, ha₁, ha₂, i, η, hf'⟩ := f.2
  have e1 : ∀ x : K, a₁ * (frobK K ^ i) x = x := by
    intro x
    have hx : semiFirstPerm K f x = x :=
      congrArg (fun (p : gammaLin K) => (p : Equiv.Perm K) x) h1
    rw [← semiFirstPerm_formula K hf' x]
    exact hx
  have e2 : ∀ y : K, a₂ * (frobK K ^ i) y = y := by
    intro y
    have hy : semiSecondPerm K f y = y :=
      congrArg (fun (p : gammaLin K) => (p : Equiv.Perm K) y) h2
    rw [← semiSecondPerm_formula K hf' y]
    exact hy
  rw [mem_shearSub_iff K f]
  exact ⟨η, fun x y => by rw [hf' x y, e1 x, e2 y]⟩
