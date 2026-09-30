import Mathlib
import Submission.Work.Pi6.SQM.Defs
import Submission.Work.Cohomology.KroneckerH
import Submission.Work.Cohomology.kronH_bijective_field
import Submission.Work.SSS.E2Zero.homologypi_eq_zero_iff
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# SQM: reduction of (co)chains along `ℤ → 𝔽₂` and the 0/1 lifts

Area `SQM`'s `torsionOfNonliftable` is pure chain/cochain arithmetic with 0/1 lifts plus field
duality.  This file fixes the vocabulary:

* `valZ : 𝔽₂ → ℤ` — the section `0 ↦ 0`, `1 ↦ 1` of the reduction;
* `liftZ` — the 0/1 integral lift of a mod-2 cochain;
* `redC`, `red4` — reduction of integral cochains along `ℤ → 𝔽₂`, resp. `ℤ → ℤ/4`;
* `redChain` — reduction of integral chains along `ℤ → 𝔽₂` (coproduct-wise);
* `eZ`, `eF` — the identification of the singular chains with the free module on the simplices
  (`ModuleCat.finsuppCoconeIsColimit`), which is what makes `redChain` computable coefficientwise.

The mathematical statements live in the sibling files.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQM

noncomputable section

open Work.Cohomology (Cochain genEval cochainDiff cohomologyClassOf chainC cochainC genElt
  genEval_ext genEval_add genEval_smul genEval_cochainDiff)

/-! ## The 0/1 section `𝔽₂ → ℤ` -/

/-- The section of the reduction `ℤ → 𝔽₂`: `valZ 0 = 0`, `valZ 1 = 1`. -/
def valZ (a : F2) : ℤ := (a.val : ℤ)

@[simp] theorem valZ_zero : valZ 0 = 0 := by simp [valZ]

@[simp] theorem valZ_one : valZ 1 = 1 := by
  simp [valZ, ZMod.val_one]

/-- `valZ` is a section of the reduction `ℤ → 𝔽₂`. -/
theorem intCast_valZ (a : F2) : ((valZ a : ℤ) : F2) = a := by
  simp [valZ, ZMod.natCast_val]

/-! ## Reduction and lifting of cochains -/

/-- **Reduction of an integral cochain to a mod-2 cochain** (generatorwise). -/
def redC (Y : SSet) (n : ℕ) (α : Cochain ℤ Y n) : Cochain F2 Y n :=
  ((Y.isColimitChainComplexXCofan (ModuleCat.of F2 F2) n).desc
    (Cofan.mk (ModuleCat.of F2 F2)
      (fun σ : Y _⦋n⦌ => ModuleCat.ofHom (LinearMap.toSpanSingleton F2 F2
        (((genEval ℤ Y α σ : ℤ)) : F2))))).hom

/-- The generator formula for `redC`. -/
theorem ιChainComplex_redC (Y : SSet) (n : ℕ) (α : Cochain ℤ Y n) (σ : Y _⦋n⦌) :
    Y.ιChainComplex (R := ModuleCat.of F2 F2) σ ≫
        (Y.isColimitChainComplexXCofan (ModuleCat.of F2 F2) n).desc
          (Cofan.mk (ModuleCat.of F2 F2)
            (fun τ : Y _⦋n⦌ => ModuleCat.ofHom (LinearMap.toSpanSingleton F2 F2
              (((genEval ℤ Y α τ : ℤ)) : F2)))) =
      ModuleCat.ofHom (LinearMap.toSpanSingleton F2 F2 (((genEval ℤ Y α σ : ℤ)) : F2)) :=
  Cofan.IsColimit.fac _ _ _

/-- **The 0/1 integral lift of a mod-2 cochain**. -/
def liftZ (Y : SSet) (n : ℕ) (x : Cochain F2 Y n) : Cochain ℤ Y n :=
  ((Y.isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n).desc
    (Cofan.mk (ModuleCat.of ℤ ℤ)
      (fun σ : Y _⦋n⦌ => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ℤ
        (valZ (genEval F2 Y x σ)))))).hom

/-- The generator formula for `liftZ`. -/
theorem ιChainComplex_liftZ (Y : SSet) (n : ℕ) (x : Cochain F2 Y n) (σ : Y _⦋n⦌) :
    Y.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ ≫
        (Y.isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n).desc
          (Cofan.mk (ModuleCat.of ℤ ℤ)
            (fun τ : Y _⦋n⦌ => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ℤ
              (valZ (genEval F2 Y x τ))))) =
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ℤ (valZ (genEval F2 Y x σ))) :=
  Cofan.IsColimit.fac _ _ _

/-- **Reduction of an integral cochain to a `ℤ/4` cochain** (generatorwise). -/
def red4 (Y : SSet) (n : ℕ) (α : Cochain ℤ Y n) : Cochain (ZMod 4) Y n :=
  ((Y.isColimitChainComplexXCofan (ModuleCat.of (ZMod 4) (ZMod 4)) n).desc
    (Cofan.mk (ModuleCat.of (ZMod 4) (ZMod 4))
      (fun σ : Y _⦋n⦌ => ModuleCat.ofHom (LinearMap.toSpanSingleton (ZMod 4) (ZMod 4)
        (((genEval ℤ Y α σ : ℤ)) : ZMod 4))))).hom

/-- The generator formula for `red4`. -/
theorem ιChainComplex_red4 (Y : SSet) (n : ℕ) (α : Cochain ℤ Y n) (σ : Y _⦋n⦌) :
    Y.ιChainComplex (R := ModuleCat.of (ZMod 4) (ZMod 4)) σ ≫
        (Y.isColimitChainComplexXCofan (ModuleCat.of (ZMod 4) (ZMod 4)) n).desc
          (Cofan.mk (ModuleCat.of (ZMod 4) (ZMod 4))
            (fun τ : Y _⦋n⦌ => ModuleCat.ofHom (LinearMap.toSpanSingleton (ZMod 4) (ZMod 4)
              (((genEval ℤ Y α τ : ℤ)) : ZMod 4)))) =
      ModuleCat.ofHom (LinearMap.toSpanSingleton (ZMod 4) (ZMod 4)
        (((genEval ℤ Y α σ : ℤ)) : ZMod 4)) :=
  Cofan.IsColimit.fac _ _ _

/-- The value of `redC` on generators. -/
theorem genEval_redC (Y : SSet) (n : ℕ) (α : Cochain ℤ Y n) (σ : Y _⦋n⦌) :
    genEval F2 Y (redC Y n α) σ = ((genEval ℤ Y α σ : ℤ) : F2) := by
  have h2 := congrArg (fun (g : ModuleCat.of F2 F2 ⟶ ModuleCat.of F2 F2) => g.hom 1)
    (ιChainComplex_redC Y n α σ)
  simpa only [redC, genEval, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply, one_smul] using h2

/-- The value of `liftZ` on generators. -/
theorem genEval_liftZ (Y : SSet) (n : ℕ) (x : Cochain F2 Y n) (σ : Y _⦋n⦌) :
    genEval ℤ Y (liftZ Y n x) σ = valZ (genEval F2 Y x σ) := by
  have h2 := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ) => g.hom 1)
    (ιChainComplex_liftZ Y n x σ)
  simpa only [liftZ, genEval, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply, one_smul] using h2

/-- The value of `red4` on generators. -/
theorem genEval_red4 (Y : SSet) (n : ℕ) (α : Cochain ℤ Y n) (σ : Y _⦋n⦌) :
    genEval (ZMod 4) Y (red4 Y n α) σ = ((genEval ℤ Y α σ : ℤ) : ZMod 4) := by
  have h2 := congrArg (fun (g : ModuleCat.of (ZMod 4) (ZMod 4) ⟶ ModuleCat.of (ZMod 4) (ZMod 4))
    => g.hom 1) (ιChainComplex_red4 Y n α σ)
  simpa only [red4, genEval, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply, one_smul] using h2

/-- The mod-2 reduction of the 0/1 lift of a mod-2 cochain is the cochain itself. -/
theorem redC_liftZ (Y : SSet) (n : ℕ) (x : Cochain F2 Y n) : redC Y n (liftZ Y n x) = x := by
  apply genEval_ext
  intro σ
  rw [genEval_redC, genEval_liftZ, intCast_valZ]

/-! ## Reduction of chains -/

/-- **Reduction of integral chains to mod-2 chains**, induced by `ℤ → 𝔽₂` on the generators. -/
def redChain (Y : SSet) (m : ℕ) :
    (↥((chainC ℤ Y).X m)) →ₗ[ℤ] (↥((chainC F2 Y).X m)) :=
  ((Y.isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) m).desc
    (Cofan.mk (ModuleCat.of ℤ ↥((chainC F2 Y).X m))
      (fun σ : Y _⦋m⦌ => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ↥((chainC F2 Y).X m)
        (genElt F2 Y σ))))).hom

/-- The generator formula for `redChain`. -/
theorem ιChainComplex_redChain (Y : SSet) (m : ℕ) (σ : Y _⦋m⦌) :
    Y.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ ≫
        (Y.isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) m).desc
          (Cofan.mk (ModuleCat.of ℤ ↥((chainC F2 Y).X m))
            (fun τ : Y _⦋m⦌ => ModuleCat.ofHom
              (LinearMap.toSpanSingleton ℤ ↥((chainC F2 Y).X m) (genElt F2 Y τ)))) =
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ↥((chainC F2 Y).X m) (genElt F2 Y σ)) :=
  Cofan.IsColimit.fac _ _ _

/-- The value of `redChain` on generators. -/
theorem redChain_genElt (Y : SSet) (m : ℕ) (σ : Y _⦋m⦌) :
    redChain Y m (genElt ℤ Y σ) = genElt F2 Y σ := by
  have h2 := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ↥((chainC F2 Y).X m)) => g.hom 1)
    (ιChainComplex_redChain Y m σ)
  simpa only [redChain, genElt, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply, one_smul] using h2

/-- The `ℤ`-chains in degree `m` are the free module on the `m`-simplices. -/
noncomputable def eZ (Y : SSet) (m : ℕ) :
    (chainC ℤ Y).X m ≅ ModuleCat.of ℤ (Y _⦋m⦌ →₀ ℤ) :=
  (Y.isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) m).coconePointUniqueUpToIso
    (ModuleCat.finsuppCoconeIsColimit ℤ ℤ (Y _⦋m⦌))

/-- The `𝔽₂`-chains in degree `m` are the free module on the `m`-simplices. -/
noncomputable def eF (Y : SSet) (m : ℕ) :
    (chainC F2 Y).X m ≅ ModuleCat.of F2 (Y _⦋m⦌ →₀ F2) :=
  (Y.isColimitChainComplexXCofan (ModuleCat.of F2 F2) m).coconePointUniqueUpToIso
    (ModuleCat.finsuppCoconeIsColimit F2 F2 (Y _⦋m⦌))

/-- The generator formula for `eZ`. -/
theorem ιChainComplex_eZ (Y : SSet) (m : ℕ) (σ : Y _⦋m⦌) :
    Y.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ ≫ (eZ Y m).hom =
      ModuleCat.ofHom (Finsupp.lsingle σ : ℤ →ₗ[ℤ] (Y _⦋m⦌ →₀ ℤ)) := by
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    (Y.isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) m)
    (ModuleCat.finsuppCoconeIsColimit ℤ ℤ (Y _⦋m⦌)) (Discrete.mk σ)
  simpa only [eZ, ModuleCat.finsuppCocone, Cofan.mk_ι_app, SSet.chainComplexXCofan] using h

/-- The generator formula for `eF`. -/
theorem ιChainComplex_eF (Y : SSet) (m : ℕ) (σ : Y _⦋m⦌) :
    Y.ιChainComplex (R := ModuleCat.of F2 F2) σ ≫ (eF Y m).hom =
      ModuleCat.ofHom (Finsupp.lsingle σ : F2 →ₗ[F2] (Y _⦋m⦌ →₀ F2)) := by
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    (Y.isColimitChainComplexXCofan (ModuleCat.of F2 F2) m)
    (ModuleCat.finsuppCoconeIsColimit F2 F2 (Y _⦋m⦌)) (Discrete.mk σ)
  simpa only [eF, ModuleCat.finsuppCocone, Cofan.mk_ι_app, SSet.chainComplexXCofan] using h

/-- `eZ` sends a generator to the corresponding basis vector. -/
theorem eZ_genElt (Y : SSet) (m : ℕ) (σ : Y _⦋m⦌) :
    (eZ Y m).hom (genElt ℤ Y σ) = Finsupp.single σ 1 := by
  have h2 := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶ (ModuleCat.of ℤ (Y _⦋m⦌ →₀ ℤ))) => g.hom 1)
    (ιChainComplex_eZ Y m σ)
  simpa only [genElt, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    Finsupp.lsingle_apply] using h2

/-- `eF` sends a generator to the corresponding basis vector. -/
theorem eF_genElt (Y : SSet) (m : ℕ) (σ : Y _⦋m⦌) :
    (eF Y m).hom (genElt F2 Y σ) = Finsupp.single σ 1 := by
  have h2 := congrArg (fun (g : ModuleCat.of F2 F2 ⟶ (ModuleCat.of F2 (Y _⦋m⦌ →₀ F2))) => g.hom 1)
    (ιChainComplex_eF Y m σ)
  simpa only [genElt, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    Finsupp.lsingle_apply] using h2


/-! ## Arithmetic in `ℤ/4` and `ℤ` -/

/-- The reduction `ℤ/4 → ℤ/2` is the usual reduction of integers. -/
theorem r42_intCast (m : ℤ) : r42 ((m : ℤ) : ZMod 4) = ((m : ℤ) : F2) :=
  RingHom.congr_fun (RingHom.ext_int (r42.comp (Int.castRingHom (ZMod 4)))
    (Int.castRingHom (ZMod 2))) m

/-- An element of `ℤ/4` killed by the reduction to `ℤ/2` is `2`-torsion. -/
theorem two_mul_eq_zero_of_r42_eq_zero (a : ZMod 4) (h : r42 a = 0) : 2 * a = 0 := by
  have ha : ((a.val : ℤ) : ZMod 4) = a := by
    rw [show ((a.val : ℤ) : ZMod 4) = ((a.val : ℕ) : ZMod 4) from by push_cast; ring]
    simp [ZMod.natCast_val]
  have h1 : ((a.val : ℤ) : ZMod 2) = 0 := by
    rw [← r42_intCast (a.val), ha]
    exact h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
  obtain ⟨k, hk⟩ := h1
  rw [← ha, show (2 : ZMod 4) * ((a.val : ℤ) : ZMod 4) = ((2 * a.val : ℤ) : ZMod 4) from by
    push_cast; ring, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact ⟨k, by rw [hk]; ring⟩

/-- `2 * (n / 2) = n` for even integers. -/
theorem two_mul_ediv_two (n : ℤ) (h : (2 : ℤ) ∣ n) : 2 * (n / 2) = n := by
  obtain ⟨k, rfl⟩ := h
  rw [Int.mul_ediv_cancel_left k (by norm_num : (2 : ℤ) ≠ 0)]

/-! ## Extensionality and ℤ-linearity of the reductions -/

/-- Two `ℤ`-linear maps on the `n`-chains of a simplicial set which agree on the generators
(a simplex) are equal. -/
theorem chain_ext {Y : SSet} {m : ℕ} {T : Type} [AddCommGroup T] [Module ℤ T]
    (f g : (↥((chainC ℤ Y).X m)) →ₗ[ℤ] T)
    (h : ∀ σ : Y _⦋m⦌, f (genElt ℤ Y σ) = g (genElt ℤ Y σ)) : f = g := by
  have key : (ModuleCat.ofHom f : (chainC ℤ Y).X m ⟶ ModuleCat.of ℤ T) =
      ModuleCat.ofHom g := by
    apply SSet.chainComplex_hom_ext
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    show f ((Y.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1)
      = g ((Y.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1)
    exact h σ
  simpa only [ModuleCat.hom_ofHom] using congrArg ModuleCat.Hom.hom key

/-- `genEval` is compatible with integer scalar multiplication. -/
theorem genEval_zsmul (Y : SSet) {R : Type} [CommRing R] {m : ℕ} (r : ℤ) (f : Cochain R Y m)
    (σ : Y _⦋m⦌) : genEval R Y (r • f) σ = r • genEval R Y f σ := by
  simp only [genEval, LinearMap.smul_apply]

/-- `redC` is additive. -/
theorem redC_add (Y : SSet) (n : ℕ) (α β : Cochain ℤ Y n) :
    redC Y n (α + β) = redC Y n α + redC Y n β := by
  apply genEval_ext
  intro σ
  simp only [genEval_redC, genEval_add]
  push_cast
  ring

/-- `redC` is `ℤ`-homogeneous. -/
theorem redC_smul (Y : SSet) (n : ℕ) (r : ℤ) (α : Cochain ℤ Y n) :
    redC Y n (r • α) = r • redC Y n α := by
  apply genEval_ext
  intro σ
  simp only [genEval_redC, genEval_zsmul, zsmul_eq_mul]
  push_cast
  ring

/-- `red4` is additive. -/
theorem red4_add (Y : SSet) (n : ℕ) (α β : Cochain ℤ Y n) :
    red4 Y n (α + β) = red4 Y n α + red4 Y n β := by
  apply genEval_ext
  intro σ
  simp only [genEval_red4, genEval_add]
  push_cast
  ring

/-- `red4` is `ℤ`-homogeneous. -/
theorem red4_smul (Y : SSet) (n : ℕ) (r : ℤ) (α : Cochain ℤ Y n) :
    red4 Y n (r • α) = r • red4 Y n α := by
  apply genEval_ext
  intro σ
  simp only [genEval_red4, genEval_zsmul, zsmul_eq_mul]
  push_cast
  ring

/-- `redC` as a `ℤ`-linear map. -/
def redCLM (Y : SSet) (n : ℕ) : Cochain ℤ Y n →ₗ[ℤ] Cochain F2 Y n where
  toFun := redC Y n
  map_add' := redC_add Y n
  map_smul' := redC_smul Y n

/-- `red4` as a `ℤ`-linear map. -/
def red4LM (Y : SSet) (n : ℕ) : Cochain ℤ Y n →ₗ[ℤ] Cochain (ZMod 4) Y n where
  toFun := red4 Y n
  map_add' := red4_add Y n
  map_smul' := red4_smul Y n

@[simp] theorem redCLM_apply (Y : SSet) (n : ℕ) (α : Cochain ℤ Y n) :
    redCLM Y n α = redC Y n α := rfl

@[simp] theorem red4LM_apply (Y : SSet) (n : ℕ) (α : Cochain ℤ Y n) :
    red4LM Y n α = red4 Y n α := rfl

/-- `redC` commutes with the coboundary. -/
theorem redC_cochainDiff (Y : SSet) (n : ℕ) (α : Cochain ℤ Y n) :
    redC Y (n + 1) (cochainDiff ℤ Y α) = cochainDiff F2 Y (redC Y n α) := by
  apply genEval_ext
  intro σ
  have h1 : genEval F2 Y (redC Y (n + 1) (cochainDiff ℤ Y α)) σ
      = ((∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) * genEval ℤ Y α (Y.δ i σ) : ℤ) : F2) := by
    rw [genEval_redC, genEval_cochainDiff]
  have h2 : genEval F2 Y (cochainDiff F2 Y (redC Y n α)) σ
      = ∑ i : Fin (n + 2), (-1 : F2) ^ (i : ℕ) * ((genEval ℤ Y α (Y.δ i σ) : ℤ) : F2) := by
    rw [genEval_cochainDiff]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [genEval_redC]
  rw [h1, h2]
  push_cast
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- `red4` commutes with the coboundary. -/
theorem red4_cochainDiff (Y : SSet) (n : ℕ) (α : Cochain ℤ Y n) :
    red4 Y (n + 1) (cochainDiff ℤ Y α) = cochainDiff (ZMod 4) Y (red4 Y n α) := by
  apply genEval_ext
  intro σ
  have h1 : genEval (ZMod 4) Y (red4 Y (n + 1) (cochainDiff ℤ Y α)) σ
      = ((∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) * genEval ℤ Y α (Y.δ i σ) : ℤ) : ZMod 4) := by
    rw [genEval_red4, genEval_cochainDiff]
  have h2 : genEval (ZMod 4) Y (cochainDiff (ZMod 4) Y (red4 Y n α)) σ
      = ∑ i : Fin (n + 2), (-1 : ZMod 4) ^ (i : ℕ) * ((genEval ℤ Y α (Y.δ i σ) : ℤ) : ZMod 4) := by
    rw [genEval_cochainDiff]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [genEval_red4]
  rw [h1, h2]
  push_cast
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- The reduction `ℤ/4 → ℤ/2` of the values of `red4` recovers `redC`. -/
theorem r42_genEval_red4 (Y : SSet) (n : ℕ) (α : Cochain ℤ Y n) (σ : Y _⦋n⦌) :
    r42 (genEval (ZMod 4) Y (red4 Y n α) σ) = genEval F2 Y (redC Y n α) σ := by
  rw [genEval_red4, genEval_redC, r42_intCast]

/-- Twice a cochain vanishes after reduction to `𝔽₂`. -/
theorem redC_two_smul (Y : SSet) (n : ℕ) (α : Cochain ℤ Y n) :
    redC Y n ((2 : ℤ) • α) = 0 := by
  rw [← redCLM_apply, map_smul, redCLM_apply, ← Int.cast_smul_eq_zsmul F2 2,
    show ((2 : ℤ) : F2) = 0 from by decide, zero_smul]

/-- An integral cochain whose reduction to `𝔽₂` vanishes becomes `2`-torsion in `ℤ/4`. -/
theorem two_smul_red4_eq_zero {Y : SSet} {n : ℕ} (ρ : Cochain ℤ Y n)
    (h : redC Y n ρ = 0) : (2 : ℤ) • red4 Y n ρ = 0 := by
  apply genEval_ext
  intro σ
  rw [genEval_zsmul]
  have hr : r42 (genEval (ZMod 4) Y (red4 Y n ρ) σ) = 0 := by
    rw [r42_genEval_red4, h]
    rfl
  have h2 : (2 : ZMod 4) * genEval (ZMod 4) Y (red4 Y n ρ) σ = 0 :=
    two_mul_eq_zero_of_r42_eq_zero _ hr
  rwa [← Int.cast_smul_eq_zsmul (ZMod 4) 2, smul_eq_mul]

/-! ## The pairing of an integral cochain with an integral chain, reduced -/

/-- The pairing `c ↦ ⟨α, c⟩` with values in `𝔽₂`, as a `ℤ`-linear map. -/
def pairingL (Y : SSet) (n : ℕ) (α : Cochain ℤ Y n) :
    (↥((chainC ℤ Y).X n)) →ₗ[ℤ] F2 :=
  (LinearMap.toSpanSingleton ℤ F2 (1 : F2)).comp α

/-- The reduction of the pairing, as a `ℤ`-linear map. -/
def pairingZ (Y : SSet) (n : ℕ) (α : Cochain ℤ Y n) :
    (↥((chainC ℤ Y).X n)) →ₗ[ℤ] F2 where
  toFun c := (redC Y n α) (redChain Y n c)
  map_add' x y := by rw [map_add, map_add]
  map_smul' r x := by
    simp only [RingHom.id_apply]
    rw [LinearMap.map_smul (redChain Y n) r x, ← Int.cast_smul_eq_zsmul F2 r, map_smul,
      Int.cast_smul_eq_zsmul F2 r]

theorem pairingZ_apply (Y : SSet) (n : ℕ) (α : Cochain ℤ Y n) (c : ↥((chainC ℤ Y).X n)) :
    pairingZ Y n α c = (redC Y n α) (redChain Y n c) := rfl

/-- **The pairing reduces correctly**: `⟨α, c⟩ mod 2 = ⟨α mod 2, c mod 2⟩`. -/
theorem pairingRedC (Y : SSet) (n : ℕ) (α : Cochain ℤ Y n) (c : ↥((chainC ℤ Y).X n)) :
    ((α c : ℤ) : F2) = (redC Y n α) (redChain Y n c) := by
  have key : pairingL Y n α = pairingZ Y n α := by
    apply chain_ext
    intro σ
    rw [pairingZ_apply]
    show (LinearMap.toSpanSingleton ℤ F2 (1 : F2)) (α (genElt ℤ Y σ))
      = (redC Y n α) (redChain Y n (genElt ℤ Y σ))
    rw [redChain_genElt]
    show (LinearMap.toSpanSingleton ℤ F2 (1 : F2)) (genEval ℤ Y α σ)
      = genEval F2 Y (redC Y n α) σ
    rw [genEval_redC, LinearMap.toSpanSingleton_apply, zsmul_eq_mul, mul_one]
  have h2 := LinearMap.congr_fun key c
  rw [show ((α c : ℤ) : F2) = pairingL Y n α c from by
    simp only [pairingL, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, zsmul_eq_mul,
      mul_one]]
  rw [h2, pairingZ_apply]

/-- The coboundary is additive on cochains. -/
theorem cochainDiff_sub {R : Type} [CommRing R] {Y : SSet} {k : ℕ}
    (γ γ' : Cochain R Y k) :
    cochainDiff R Y (γ - γ') = cochainDiff R Y γ - cochainDiff R Y γ' := by
  simp only [cochainDiff, LinearMap.sub_comp]

/-- The coboundary is homogeneous on cochains. -/
theorem cochainDiff_smul {R : Type} [CommRing R] {Y : SSet} {k : ℕ}
    (r : R) (γ : Cochain R Y k) :
    cochainDiff R Y (r • γ) = r • cochainDiff R Y γ := by
  simp only [cochainDiff, LinearMap.smul_comp]

/-- The pairing of an integral cochain with a chain is `ℤ`-linear in the chain. -/
theorem cochain_apply_zsmul {Y : SSet} {k : ℕ} (α : Cochain ℤ Y k) (r : ℤ)
    (c : ↥((chainC ℤ Y).X k)) : α (r • c) = r * (α c) := by
  rw [map_zsmul]
  exact Int.zsmul_eq_mul r (α c)

/-- A cocycle of the cochain complex of a simplicial set is a cocycle. -/
theorem cochainDiff_congr_apply {R : Type} [CommRing R] {Y : SSet} {k : ℕ}
    (γ γ' : Cochain R Y k) (h : γ = γ') (x : ↥((chainC R Y).X k)) : γ x = γ' x :=
  congrArg (fun f => f x) h

/-! ## Halving an integral cochain -/

/-- The generatorwise half of an integral cochain. -/
def halfCochain (Y : SSet) (n : ℕ) (β : Cochain ℤ Y n) : Cochain ℤ Y n :=
  ((Y.isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n).desc
    (Cofan.mk (ModuleCat.of ℤ ℤ) (fun σ : Y _⦋n⦌ => ModuleCat.ofHom
      (LinearMap.toSpanSingleton ℤ ℤ (genEval ℤ Y β σ / 2))))).hom

/-- The generator formula for `halfCochain`. -/
theorem ιChainComplex_halfCochain (Y : SSet) (n : ℕ) (β : Cochain ℤ Y n) (σ : Y _⦋n⦌) :
    Y.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ ≫
        (Y.isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n).desc
          (Cofan.mk (ModuleCat.of ℤ ℤ) (fun τ : Y _⦋n⦌ => ModuleCat.ofHom
            (LinearMap.toSpanSingleton ℤ ℤ (genEval ℤ Y β τ / 2)))) =
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ℤ (genEval ℤ Y β σ / 2)) :=
  Cofan.IsColimit.fac _ _ _

/-- The value of `halfCochain` on generators. -/
theorem genEval_halfCochain (Y : SSet) (n : ℕ) (β : Cochain ℤ Y n) (σ : Y _⦋n⦌) :
    genEval ℤ Y (halfCochain Y n β) σ = genEval ℤ Y β σ / 2 := by
  have h2 := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ) => g.hom 1)
    (ιChainComplex_halfCochain Y n β σ)
  simpa only [halfCochain, genEval, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply, one_smul] using h2

/-- `2 • (β/2) = β` when all the values of `β` are even. -/
theorem two_smul_halfCochain (Y : SSet) (n : ℕ) (β : Cochain ℤ Y n)
    (h : ∀ σ : Y _⦋n⦌, (2 : ℤ) ∣ genEval ℤ Y β σ) :
    (2 : ℤ) • halfCochain Y n β = β := by
  apply chain_ext
  intro σ
  show genEval ℤ Y ((2 : ℤ) • halfCochain Y n β) σ = genEval ℤ Y β σ
  rw [genEval_smul, genEval_halfCochain, zsmul_eq_mul]
  obtain ⟨k, hk⟩ := h σ
  rw [hk, Int.mul_ediv_cancel_left k (by norm_num : (2 : ℤ) ≠ 0)]
  ring

/-- An integral cochain killed by `2` is zero. -/
theorem two_smul_cochain_eq_zero {Y : SSet} {n : ℕ} (β : Cochain ℤ Y n)
    (h : (2 : ℤ) • β = 0) : β = 0 := by
  apply chain_ext
  intro σ
  show genEval ℤ Y β σ = 0
  have h2 : (2 : ℤ) * genEval ℤ Y β σ = 0 := by
    have h3 : genEval ℤ Y ((2 : ℤ) • β) σ = 0 := by rw [h]; rfl
    rwa [genEval_smul, zsmul_eq_mul] at h3
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd h (by norm_num)
  · exact h

/-- The generatorwise values of `δ(ỹ)` for a lift `ỹ = liftZ y` of a mod-2 cocycle `y` are even. -/
theorem intCast_genEval_coboundary_liftZ (Y : SSet) (n : ℕ) (y : Cochain F2 Y n)
    (hy : cochainDiff F2 Y y = 0) (σ : Y _⦋n + 1⦌) :
    ((genEval ℤ Y (cochainDiff ℤ Y (liftZ Y n y)) σ : ℤ) : F2) = 0 := by
  have h1 : genEval F2 Y (redC Y (n + 1) (cochainDiff ℤ Y (liftZ Y n y))) σ = 0 := by
    rw [redC_cochainDiff, redC_liftZ, hy]
    rfl
  simpa only [genEval_redC] using h1

end

end Work.Pi6.SQM
