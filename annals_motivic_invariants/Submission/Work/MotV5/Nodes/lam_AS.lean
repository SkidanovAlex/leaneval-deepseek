import Mathlib
import Submission.Work.MotV5.ASTwistData
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotC2.aut_functionField
import Submission.Work.MotV5.asTwistFieldTrue_basic
import Submission.Work.MotT.extend_algEquiv_of_linearDisjoint
import Submission.Work.MotV5.Nodes.shiftOf_eq_transAlgEquiv
import Submission.Work.MotV5.RigAS.twistFieldTrue_sup_asRoot
import Submission.Work.MotV5.LamAS.asPsi
import Submission.Work.MotV5.LamAS.asPsi_aux
import Submission.Work.MotV5.LamAS.asTransport
import Submission.Work.MotV5.LamAS.asIota_range
import Submission.Work.MotV5.LamAS.asML_c2
import Submission.Work.MotV5.LamAS.asSigmaLift_eq_trans
import Submission.Work.MotV5.LamAS.asSigmaLift_comm
import Submission.Work.MotV5.LamAS.asF_transfer
import Submission.Work.MotV5.LamAS.asF_linearDisjoint
import Submission.Work.MotV5.LamAS.asExtendTheta
import Submission.Work.MotV5.LamAS.asL2_isGalois
import Submission.Work.MotV5.LamAS.asExtension
import Submission.Work.MotV5.LamAS.asCompare
import Submission.Work.MotV5.LamAS.root_eq_asRoot_add
import Submission.Work.MotV5.LamAS.CoordNe.asTwistPoint_coords_ne
import Submission.Work.MotV5.LamAS.FixPsi.asPsi_fixes_asF
import Submission.Work.MotV5.LamAS.asDefect
import Submission.Work.MotV5.GenAux_sigmaS_pow_five_kleinField
import Submission.Work.MotV5.kleinField_eq_adjoin_genXY
import Submission.Work.MotC2.FuncExt
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

set_option maxHeartbeats 24000000

namespace Work.MotV5.LamAS

variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]

/-! ## Auxiliary lemmas for the assembly of `lam_AS` -/

/-- From `z • T = 0` with `T ≠ 0` and `5 • T = 0`, conclude `5 ∣ z`. -/
theorem five_dvd_of_zsmul_eq_zero {A : Type*} [AddCommGroup A] {T : A}
    (h5 : (5 : ℕ) • T = 0) (hne : T ≠ 0) {z : ℤ} (hz : z • T = 0) : (5 : ℤ) ∣ z := by
  have h5z : (5 : ℤ) • T = 0 := by
    rw [show (5 : ℤ) = ((5 : ℕ) : ℤ) from rfl, natCast_zsmul, h5]
  have hz' : z • T = 0 := hz
  rw [show z = 5 * (z / 5) + z % 5 from (Int.mul_ediv_add_emod z 5).symm] at hz'
  rw [add_zsmul] at hz'
  have hz1 : (5 * (z / 5)) • T = 0 := by
    rw [mul_comm (5 : ℤ) (z / 5), mul_zsmul, h5z, smul_zero]
  rw [hz1, zero_add] at hz'
  have hlt : z % 5 < 5 := Int.emod_lt_of_pos z (by norm_num)
  have hge : 0 ≤ z % 5 := Int.emod_nonneg z (by norm_num)
  have hr0 : z % 5 = 0 := by
    interval_cases hc : (z % 5)
    · rfl
    · exfalso; rw [one_zsmul] at hz'; exact hne hz'
    · exfalso
      have h4 : (4 : ℤ) • T = 0 := by
        rw [show (4 : ℤ) = 2 * 2 from rfl, mul_zsmul, hz', smul_zero]
      have h1T : (1 : ℤ) • T = 0 := by
        rw [show (1 : ℤ) = 5 - 4 from rfl, sub_zsmul, h5z, h4]
        simp
      rw [one_zsmul] at h1T; exact hne h1T
    · exfalso
      have h6 : (6 : ℤ) • T = 0 := by
        rw [show (6 : ℤ) = 2 * 3 from rfl, mul_zsmul, hz', smul_zero]
      have h1T : (1 : ℤ) • T = 0 := by
        rw [show (1 : ℤ) = 6 - 5 from rfl, sub_zsmul, h6, h5z]
        simp
      rw [one_zsmul] at h1T; exact hne h1T
    · exfalso
      have h1T : (1 : ℤ) • T = 0 := by
        rw [show (1 : ℤ) = 5 - 4 from rfl, sub_zsmul, h5z, hz']
        simp
      rw [one_zsmul] at h1T; exact hne h1T
  refine ⟨z / 5, ?_⟩
  have h := Int.mul_ediv_add_emod z 5
  rw [hr0, add_zero] at h
  exact h.symm

/-- **Integer multiples of `T` depend only on the residue modulo `5`** when `5 • T = 0`. -/
theorem smul_eq_of_intCast_eq {𝕃 : Type*} [Field 𝕃] [CharP 𝕃 5] {A : Type*} [AddCommGroup A]
    {a b : ℤ} (h : ((a : ℤ) : 𝕃) = ((b : ℤ) : 𝕃)) (T : A) (h5 : (5 : ℕ) • T = 0) :
    a • T = b • T := by
  have h0 : ((a - b : ℤ) : 𝕃) = 0 := by
    have h1 : (((a : ℤ) : 𝕃) - ((b : ℤ) : 𝕃)) = 0 := by rw [h, sub_self]
    simpa using h1
  have hdvd : (5 : ℤ) ∣ (a - b) := (CharP.intCast_eq_zero_iff 𝕃 5 (a - b)).mp h0
  obtain ⟨c, hc⟩ := hdvd
  have h5z : (5 : ℤ) • T = 0 := by
    rw [show (5 : ℤ) = ((5 : ℕ) : ℤ) from rfl, natCast_zsmul, h5]
  have hsub : a • T - b • T = 0 := by
    rw [sub_eq_add_neg, ← sub_zsmul, hc]
    rw [show (5 : ℤ) * c = c * 5 from mul_comm 5 c, mul_zsmul, h5z, smul_zero]
  exact sub_eq_zero.mp hsub

/-- The two algebra maps `ℤ → ↥(asL2)` and `↥(asL2) → Kb` compose to the structure map. -/
theorem asL2_intCast_comp (f₁ f₂ : RatFunc 𝕜) (z : ℤ) :
    (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (Work.MotV.Kb 𝕜))
        ((algebraMap ℤ ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) z)
      = (algebraMap ℤ (Work.MotV.Kb 𝕜)) z := by
  have h : ((algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (Work.MotV.Kb 𝕜)).comp
      (algebraMap ℤ ↥(asL2 (𝕜 := 𝕜) f₁ f₂))) = algebraMap ℤ (Work.MotV.Kb 𝕜) :=
    RingHom.ext_int _ _
  rw [← RingHom.comp_apply, h]

/-- `asIota` carries the basis `1,x,y,x²,xy` of the `L`-model to the basis of the `Kb`-model. -/
theorem asIota_kleinBas (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜) (m : Fin 5) :
    asIota D f₁ f₂ (Work.MotV.kleinBas D ↥(asL2 (𝕜 := 𝕜) f₁ f₂) m) =
      Work.MotV.kleinBas D (Work.MotV.Kb 𝕜) m := by
  have hX := asIota_genX D f₁ f₂
  have hY := asIota_genY D f₁ f₂
  fin_cases m
  · change asIota D f₁ f₂ (1 : asML D f₁ f₂) = (1 : Work.MotV.Om D)
    exact map_one _
  · exact hX
  · exact hY
  · change asIota D f₁ f₂ (Work.MotV.genX (D.E.baseChange ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) ^ 2)
      = Work.MotV.genX (D.E.baseChange (Work.MotV.Kb 𝕜)) ^ 2
    rw [map_pow, hX]
  · change asIota D f₁ f₂ (Work.MotV.genX (D.E.baseChange ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) *
        Work.MotV.genY (D.E.baseChange ↥(asL2 (𝕜 := 𝕜) f₁ f₂)))
      = Work.MotV.genX (D.E.baseChange (Work.MotV.Kb 𝕜)) *
        Work.MotV.genY (D.E.baseChange (Work.MotV.Kb 𝕜))
    rw [map_mul, hX, hY]

/-- `asIota` carries the Klein coordinates of the `L`-model to those of the `Kb`-model. -/
theorem asIota_kleinCoord (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜) (i : Fin 5) :
    asIota D f₁ f₂ (Work.MotV.kleinCoord D ↥(asL2 (𝕜 := 𝕜) f₁ f₂) i) =
      Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i := by
  rw [Work.MotV.kleinCoord_eq_sum, Work.MotV.kleinCoord_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, asIota_algebraMap, asIota_kleinBas]
  congr 1

/-- **The projective fifth-torsion shift preserves `Ω = kleinField ⊔ LImage`.** -/
theorem sigmaS_mem_Omega (D : Work.MotV.KleinData 𝕜) (hD : D.Good) (f₁ f₂ : RatFunc 𝕜)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (hσS : Work.MotV5.KleinData.ShiftOf D σS) :
    ∀ x ∈ (Work.MotV5.kleinField D ⊔ LImage D (asL2 (𝕜 := 𝕜) f₁ f₂)),
      σS x ∈ (Work.MotV5.kleinField D ⊔ LImage D (asL2 (𝕜 := 𝕜) f₁ f₂)) := by
  obtain ⟨lam, hlam0, hshift⟩ := hσS
  have hκ0 : Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0 ≠ 0 := hD.coord0_ne (Work.MotV.Kb 𝕜)
  have hκ1 : Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 1 ≠ 0 := by
    intro h1
    have h := hshift 0
    rw [show (0 : Fin 5) + 1 = 1 from rfl, h1, mul_zero] at h
    exact hκ0 (σS.injective (by rw [h, map_zero]))
  let f : Work.MotV.Om D →ₐ[RatFunc 𝕜] Work.MotV.Om D :=
    (σS.restrictScalars (RatFunc 𝕜)).toAlgHom
  have hf : ∀ x, f x = σS x := fun x => rfl
  have hle : (Work.MotV5.kleinField D ⊔ LImage D (asL2 (𝕜 := 𝕜) f₁ f₂)) ≤
      (Work.MotV5.kleinField D ⊔ LImage D (asL2 (𝕜 := 𝕜) f₁ f₂)).comap f := by
    refine sup_le ?_ ?_
    · rw [Work.MotV5.kleinField]
      refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro z ⟨i, rfl⟩
      change f (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i /
          Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0) ∈
        (Work.MotV5.kleinField D ⊔ LImage D (asL2 (𝕜 := 𝕜) f₁ f₂))
      have hgen : ∀ j : Fin 5, Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) j /
          Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0 ∈ Work.MotV5.kleinField D := by
        intro j
        rw [Work.MotV5.kleinField]
        exact IntermediateField.subset_adjoin _ _ (Set.mem_range_self j)
      have h0 := hshift 0
      rw [show (0 : Fin 5) + 1 = 1 from rfl] at h0
      have key : f (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i /
            Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0) =
          (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) (i + 1) /
            Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0) *
          (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 1 /
            Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0)⁻¹ := by
        rw [hf, map_div₀, hshift i, h0]
        field_simp
      rw [key]
      exact (le_sup_left : Work.MotV5.kleinField D ≤
        Work.MotV5.kleinField D ⊔ LImage D (asL2 (𝕜 := 𝕜) f₁ f₂))
        (mul_mem (hgen (i + 1)) (inv_mem (hgen 1)))
    · intro z hz
      change f z ∈ (Work.MotV5.kleinField D ⊔ LImage D (asL2 (𝕜 := 𝕜) f₁ f₂))
      obtain ⟨c, hc, hcz⟩ := (mem_LImage_iff D (asL2 (𝕜 := 𝕜) f₁ f₂) z).mp hz
      have hσz : f z = z := by
        rw [← hcz, hf, σS.commutes c]
      rw [hσz]
      exact (le_sup_right : LImage D (asL2 (𝕜 := 𝕜) f₁ f₂) ≤
        Work.MotV5.kleinField D ⊔ LImage D (asL2 (𝕜 := 𝕜) f₁ f₂)) hz
  exact fun x hx => hle hx

/-- **`asRoot (f₁ - f₂)` lies in `L = K⟮asRoot f₁, asRoot f₂⟯`.** -/
theorem asRoot_sub_mem (f₁ f₂ : RatFunc 𝕜) :
    Work.MotV5.asRoot (f₁ - f₂) ∈ asL2 (𝕜 := 𝕜) f₁ f₂ := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set A : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) := ⟨Work.MotV5.asRoot f₁, asRoot_mem_asL2_left f₁ f₂⟩ with hAdef
  set B : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) := ⟨Work.MotV5.asRoot f₂, asRoot_mem_asL2_right f₁ f₂⟩ with hBdef
  have hA : A ^ 5 - A = algebraMap (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) f₁ := by
    apply Subtype.ext
    change (A : Work.MotV.Kb 𝕜) ^ 5 - (A : Work.MotV.Kb 𝕜) = _
    rw [hAdef, Work.MotV5.asRoot_spec]
    exact IsScalarTower.algebraMap_apply (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (Work.MotV.Kb 𝕜) f₁
  have hB : B ^ 5 - B = algebraMap (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) f₂ := by
    apply Subtype.ext
    change (B : Work.MotV.Kb 𝕜) ^ 5 - (B : Work.MotV.Kb 𝕜) = _
    rw [hBdef, Work.MotV5.asRoot_spec]
    exact IsScalarTower.algebraMap_apply (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (Work.MotV.Kb 𝕜) f₂
  have hΔ : (A - B) ^ 5 - (A - B) = algebraMap (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (f₁ - f₂) := by
    have key : (A - B) ^ 5 - (A - B) = (A ^ 5 - A) - (B ^ 5 - B) := by
      rw [sub_pow_char]; ring
    rw [key, hA, hB, map_sub]
  have hβ : (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (Work.MotV.Kb 𝕜) (A - B)) ^ 5
      - algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (Work.MotV.Kb 𝕜) (A - B)
      = algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (f₁ - f₂) := by
    rw [← map_pow, ← map_sub, hΔ,
      IsScalarTower.algebraMap_apply (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (Work.MotV.Kb 𝕜)]
  obtain ⟨m, hm⟩ := root_eq_asRoot_add (f₁ - f₂) hβ
  set y : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) := (A - B) - algebraMap ℤ ↥(asL2 (𝕜 := 𝕜) f₁ f₂) ((m : Fin 5) : ℤ)
    with hydef
  have hyval : algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (Work.MotV.Kb 𝕜) y =
      Work.MotV5.asRoot (f₁ - f₂) := by
    rw [hydef, map_sub, asL2_intCast_comp f₁ f₂, hm]
    refl_ring1
  rw [← hyval]
  exact y.2

/-- **`asRoot (f₁ + f₂)` lies in `L = K⟮asRoot f₁, asRoot f₂⟯`.** -/
theorem asRoot_add_mem (f₁ f₂ : RatFunc 𝕜) :
    Work.MotV5.asRoot (f₁ + f₂) ∈ asL2 (𝕜 := 𝕜) f₁ f₂ := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set A : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) := ⟨Work.MotV5.asRoot f₁, asRoot_mem_asL2_left f₁ f₂⟩ with hAdef
  set B : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) := ⟨Work.MotV5.asRoot f₂, asRoot_mem_asL2_right f₁ f₂⟩ with hBdef
  have hA : A ^ 5 - A = algebraMap (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) f₁ := by
    apply Subtype.ext
    change (A : Work.MotV.Kb 𝕜) ^ 5 - (A : Work.MotV.Kb 𝕜) = _
    rw [hAdef, Work.MotV5.asRoot_spec]
    exact IsScalarTower.algebraMap_apply (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (Work.MotV.Kb 𝕜) f₁
  have hB : B ^ 5 - B = algebraMap (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) f₂ := by
    apply Subtype.ext
    change (B : Work.MotV.Kb 𝕜) ^ 5 - (B : Work.MotV.Kb 𝕜) = _
    rw [hBdef, Work.MotV5.asRoot_spec]
    exact IsScalarTower.algebraMap_apply (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (Work.MotV.Kb 𝕜) f₂
  have hΔ : (A + B) ^ 5 - (A + B) = algebraMap (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (f₁ + f₂) := by
    have key : (A + B) ^ 5 - (A + B) = (A ^ 5 - A) + (B ^ 5 - B) := by
      rw [add_pow_char]; ring
    rw [key, hA, hB, map_add]
  have hβ : (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (Work.MotV.Kb 𝕜) (A + B)) ^ 5
      - algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (Work.MotV.Kb 𝕜) (A + B)
      = algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (f₁ + f₂) := by
    rw [← map_pow, ← map_sub, hΔ,
      IsScalarTower.algebraMap_apply (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (Work.MotV.Kb 𝕜)]
  obtain ⟨m, hm⟩ := root_eq_asRoot_add (f₁ + f₂) hβ
  set y : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) := (A + B) - algebraMap ℤ ↥(asL2 (𝕜 := 𝕜) f₁ f₂) ((m : Fin 5) : ℤ)
    with hydef
  have hyval : algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (Work.MotV.Kb 𝕜) y =
      Work.MotV5.asRoot (f₁ + f₂) := by
    rw [hydef, map_sub, asL2_intCast_comp f₁ f₂, hm]
    refl_ring1
  rw [← hyval]
  exact y.2

/-- **The Galois shift of `asRoot (f₁ - f₂)` is `χ₁ - χ₂`.** -/
theorem asShift_sub_eq (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜)
    (A B C : ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
    (hA : A ^ 5 - A = algebraMap (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) f₁)
    (hB : B ^ 5 - B = algebraMap (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) f₂)
    (hC : C ^ 5 - C = algebraMap (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (f₁ - f₂))
    (γ : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜] ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) :
    algebraMap ℤ ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (((asShift D f₁ f₂ (f₁ - f₂) C hC γ : Fin 5) : ℤ))
      = algebraMap ℤ ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (((asShift D f₁ f₂ f₁ A hA γ : Fin 5) : ℤ))
        - algebraMap ℤ ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (((asShift D f₁ f₂ f₂ B hB γ : Fin 5) : ℤ)) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hAspec := asShift_spec D f₁ f₂ f₁ A hA γ
  have hBspec := asShift_spec D f₁ f₂ f₂ B hB γ
  have hCspec := asShift_spec D f₁ f₂ (f₁ - f₂) C hC γ
  have hΔ : (A - B) ^ 5 - (A - B) = algebraMap (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (f₁ - f₂) := by
    have key : (A - B) ^ 5 - (A - B) = (A ^ 5 - A) - (B ^ 5 - B) := by
      rw [sub_pow_char]; ring
    rw [key, hA, hB, map_sub]
  have hzero : ((A - B) - C) ^ 5 - ((A - B) - C) = 0 := by
    have key : ((A - B) - C) ^ 5 - ((A - B) - C)
        = ((A - B) ^ 5 - (A - B)) - (C ^ 5 - C) := by
      rw [sub_pow_char]; ring
    rw [key, hΔ, hC, sub_self]
  obtain ⟨m, hm⟩ := exists_fin_five_of_pow_five_sub_eq_zero ((A - B) - C) hzero
  have hAB : A - B = C + ((m : Fin 5) : ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) := by
    rw [sub_eq_iff_eq_add] at hm
    rw [hm, add_comm]
  have hfixm : γ ((m : Fin 5) : ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) = ((m : Fin 5) : ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) :=
    map_natCast γ (m : ℕ)
  have h1 : γ (A - B) = (A - B) + (algebraMap ℤ ↥(asL2 (𝕜 := 𝕜) f₁ f₂)
      (((asShift D f₁ f₂ f₁ A hA γ : Fin 5) : ℤ)) - algebraMap ℤ ↥(asL2 (𝕜 := 𝕜) f₁ f₂)
      (((asShift D f₁ f₂ f₂ B hB γ : Fin 5) : ℤ))) := by
    rw [map_sub, hAspec, hBspec]
    refl_ring1
  have h2 : γ (A - B) = (A - B) + algebraMap ℤ ↥(asL2 (𝕜 := 𝕜) f₁ f₂)
      (((asShift D f₁ f₂ (f₁ - f₂) C hC γ : Fin 5) : ℤ)) := by
    rw [hAB, map_add, hCspec, hfixm]
    refl_ring1
  exact (add_left_cancel (h1.symm.trans h2)).symm

/-- **The Galois shift of `asRoot (f₁ + f₂)` is `χ₁ + χ₂`.** -/
theorem asShift_add_eq (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜)
    (A B C : ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
    (hA : A ^ 5 - A = algebraMap (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) f₁)
    (hB : B ^ 5 - B = algebraMap (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) f₂)
    (hC : C ^ 5 - C = algebraMap (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (f₁ + f₂))
    (γ : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜] ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) :
    algebraMap ℤ ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (((asShift D f₁ f₂ (f₁ + f₂) C hC γ : Fin 5) : ℤ))
      = algebraMap ℤ ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (((asShift D f₁ f₂ f₁ A hA γ : Fin 5) : ℤ))
        + algebraMap ℤ ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (((asShift D f₁ f₂ f₂ B hB γ : Fin 5) : ℤ)) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hAspec := asShift_spec D f₁ f₂ f₁ A hA γ
  have hBspec := asShift_spec D f₁ f₂ f₂ B hB γ
  have hCspec := asShift_spec D f₁ f₂ (f₁ + f₂) C hC γ
  have hΔ : (A + B) ^ 5 - (A + B) = algebraMap (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (f₁ + f₂) := by
    have key : (A + B) ^ 5 - (A + B) = (A ^ 5 - A) + (B ^ 5 - B) := by
      rw [add_pow_char]; ring
    rw [key, hA, hB, map_add]
  have hzero : ((A + B) - C) ^ 5 - ((A + B) - C) = 0 := by
    have key : ((A + B) - C) ^ 5 - ((A + B) - C)
        = ((A + B) ^ 5 - (A + B)) - (C ^ 5 - C) := by
      rw [sub_pow_char]; ring
    rw [key, hΔ, hC, sub_self]
  obtain ⟨m, hm⟩ := exists_fin_five_of_pow_five_sub_eq_zero ((A + B) - C) hzero
  have hAB : A + B = C + ((m : Fin 5) : ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) := by
    rw [sub_eq_iff_eq_add] at hm
    rw [hm, add_comm]
  have hfixm : γ ((m : Fin 5) : ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) = ((m : Fin 5) : ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) :=
    map_natCast γ (m : ℕ)
  have h1 : γ (A + B) = (A + B) + (algebraMap ℤ ↥(asL2 (𝕜 := 𝕜) f₁ f₂)
      (((asShift D f₁ f₂ f₁ A hA γ : Fin 5) : ℤ)) + algebraMap ℤ ↥(asL2 (𝕜 := 𝕜) f₁ f₂)
      (((asShift D f₁ f₂ f₂ B hB γ : Fin 5) : ℤ))) := by
    rw [map_add, hAspec, hBspec]
    refl_ring1
  have h2 : γ (A + B) = (A + B) + algebraMap ℤ ↥(asL2 (𝕜 := 𝕜) f₁ f₂)
      (((asShift D f₁ f₂ (f₁ + f₂) C hC γ : Fin 5) : ℤ)) := by
    rw [hAB, map_add, hCspec, hfixm]
    refl_ring1
  exact (add_left_cancel (h1.symm.trans h2)).symm


/-- **`σS ^ 5 = 1`.**  A projective fifth-torsion shift (`σS κᵢ = λ κ_{i+1}`) is an automorphism
whose fifth power is the identity: `σS ^ 5` fixes the Klein coordinates up to a common scalar, hence
fixes the Klein field, and the Klein field is `K(x, y)`, so `σS ^ 5 = 1`. -/
theorem sigmaS_pow_five_eq_one (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (hσS : Work.MotV5.KleinData.ShiftOf D σS) :
    σS ^ 5 = 1 := by
  haveI hEell : D.E.IsElliptic := hD.1.elliptic
  have hGood : Work.MotV.KleinData.Good D := hD.1
  have hpow : ∀ n : ℕ, ∀ x : Work.MotV.Om D,
      ((σS.restrictScalars (RatFunc 𝕜)) ^ n) x = (σS ^ n) x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
        intro x
        rw [pow_succ', AlgEquiv.mul_apply, ih, pow_succ', AlgEquiv.mul_apply,
          AlgEquiv.restrictScalars_apply]
  have hgenX : Work.MotV.genX (D.E.baseChange (Work.MotV.Kb 𝕜)) ∈ Work.MotV5.kleinField D := by
    rw [Work.MotV5.kleinField_eq_adjoin_genXY 𝕜 D hGood]
    exact IntermediateField.subset_adjoin _ _ (by simp)
  have hgenY : Work.MotV.genY (D.E.baseChange (Work.MotV.Kb 𝕜)) ∈ Work.MotV5.kleinField D := by
    rw [Work.MotV5.kleinField_eq_adjoin_genXY 𝕜 D hGood]
    exact IntermediateField.subset_adjoin _ _ (by simp)
  have hbridgeX : Work.MotV.genX (D.E.baseChange (Work.MotV.Kb 𝕜)) =
      Work.MotC2.genX (D.E.baseChange (Work.MotV.Kb 𝕜)) := by
    rw [Work.MotV.genX, Work.MotC2.genX, Work.MotC2.coordX_eq_mk]
  have hbridgeY : Work.MotV.genY (D.E.baseChange (Work.MotV.Kb 𝕜)) =
      Work.MotC2.genY (D.E.baseChange (Work.MotV.Kb 𝕜)) := by
    rw [Work.MotV.genY, Work.MotC2.genY, Work.MotC2.coordY_eq_mk]
  have hfixX : (σS ^ 5) (Work.MotC2.genX (D.E.baseChange (Work.MotV.Kb 𝕜))) =
      Work.MotC2.genX (D.E.baseChange (Work.MotV.Kb 𝕜)) := by
    rw [← hbridgeX]
    have h := Work.MotV5.GenAux_sigmaS_pow_five_kleinField 𝕜 D hGood σS hσS
      (Work.MotV.genX (D.E.baseChange (Work.MotV.Kb 𝕜))) hgenX
    rwa [hpow 5 (Work.MotV.genX (D.E.baseChange (Work.MotV.Kb 𝕜)))] at h
  have hfixY : (σS ^ 5) (Work.MotC2.genY (D.E.baseChange (Work.MotV.Kb 𝕜))) =
      Work.MotC2.genY (D.E.baseChange (Work.MotV.Kb 𝕜)) := by
    rw [← hbridgeY]
    have h := Work.MotV5.GenAux_sigmaS_pow_five_kleinField 𝕜 D hGood σS hσS
      (Work.MotV.genY (D.E.baseChange (Work.MotV.Kb 𝕜))) hgenY
    rwa [hpow 5 (Work.MotV.genY (D.E.baseChange (Work.MotV.Kb 𝕜)))] at h
  refine Work.MotC2.funcAlgEquiv_ext_genX_genY (D.E.baseChange (Work.MotV.Kb 𝕜))
    (σS ^ 5) 1 ?_ ?_
  · simpa using hfixX
  · simpa using hfixY

/-- **The lift of the fifth-torsion shift `σS` to `M = L(E)`.**  A `RatFunc 𝕜`-algebra automorphism
`σS'` of `M` with `asIota (σS' x) = σS (asIota x)` for all `x`, which acts trivially on the
constants `L`.  It exists because `σS` preserves `Ω = range asIota` (`hσSΩ`) and `σS ^ 5 = 1`, so
`σS` permutes `Ω`. -/
theorem asSigmaLift_ext (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (f₁ f₂ : RatFunc 𝕜)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (hRange : (asIota D f₁ f₂).fieldRange =
      Work.MotV5.kleinField D ⊔ LImage D (asL2 (𝕜 := 𝕜) f₁ f₂))
    (hσSΩ : ∀ x ∈ (Work.MotV5.kleinField D ⊔ LImage D (asL2 (𝕜 := 𝕜) f₁ f₂)),
      σS x ∈ (Work.MotV5.kleinField D ⊔ LImage D (asL2 (𝕜 := 𝕜) f₁ f₂)))
    (σS5 : σS ^ 5 = 1) :
    ∃ σS' : asML D f₁ f₂ ≃ₐ[↥(asL2 (𝕜 := 𝕜) f₁ f₂)] asML D f₁ f₂,
      (∀ x : asML D f₁ f₂, asIota D f₁ f₂ (σS' x) = σS (asIota D f₁ f₂ x)) ∧
      (∀ l : ↥(asL2 (𝕜 := 𝕜) f₁ f₂),
        σS' (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) l) =
          algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) l) := by
  classical
  have hσSiter : ∀ n : ℕ, ∀ z ∈ (Work.MotV5.kleinField D ⊔ LImage D (asL2 (𝕜 := 𝕜) f₁ f₂)),
      (σS ^ n) z ∈ (Work.MotV5.kleinField D ⊔ LImage D (asL2 (𝕜 := 𝕜) f₁ f₂)) := by
    intro n
    induction n with
    | zero => intro z hz; simpa using hz
    | succ n ih =>
        intro z hz
        rw [pow_succ', AlgEquiv.mul_apply]
        exact hσSΩ _ (ih z hz)
  have hcrux : ∀ y ∈ (Work.MotV5.kleinField D ⊔ LImage D (asL2 (𝕜 := 𝕜) f₁ f₂)),
      ∃ z ∈ (Work.MotV5.kleinField D ⊔ LImage D (asL2 (𝕜 := 𝕜) f₁ f₂)), σS z = y := by
    intro y hy
    refine ⟨(σS ^ 4) y, hσSiter 4 y hy, ?_⟩
    have h1 : σS ((σS ^ 4) y) = (σS ^ 5) y := by
      conv_rhs => rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ', AlgEquiv.mul_apply]
    rw [h1, σS5, AlgEquiv.one_apply]
  have hex : ∀ x : asML D f₁ f₂, ∃ y : asML D f₁ f₂,
      asIota D f₁ f₂ y = σS (asIota D f₁ f₂ x) := by
    intro x
    have hσxΩ : σS (asIota D f₁ f₂ x) ∈ (Work.MotV5.kleinField D ⊔
        LImage D (asL2 (𝕜 := 𝕜) f₁ f₂)) :=
      hσSΩ _ (by
        rw [← hRange]
        exact (AlgHom.mem_fieldRange (f := asIota D f₁ f₂)).mpr ⟨x, rfl⟩)
    exact (AlgHom.mem_fieldRange (f := asIota D f₁ f₂)).mp (by rw [hRange]; exact hσxΩ)
  let ψ : asML D f₁ f₂ → asML D f₁ f₂ := fun x => Classical.choose (hex x)
  have hψ : ∀ x, asIota D f₁ f₂ (ψ x) = σS (asIota D f₁ f₂ x) := fun x =>
    Classical.choose_spec (hex x)
  have hψadd : ∀ x y : asML D f₁ f₂, ψ (x + y) = ψ x + ψ y := by
    intro x y
    apply asIota_injective D f₁ f₂
    calc asIota D f₁ f₂ (ψ (x + y)) = σS (asIota D f₁ f₂ (x + y)) := hψ (x + y)
      _ = σS (asIota D f₁ f₂ x + asIota D f₁ f₂ y) := by rw [map_add]
      _ = σS (asIota D f₁ f₂ x) + σS (asIota D f₁ f₂ y) := by rw [map_add]
      _ = asIota D f₁ f₂ (ψ x) + asIota D f₁ f₂ (ψ y) := by rw [hψ x, hψ y]
      _ = asIota D f₁ f₂ (ψ x + ψ y) := by rw [map_add]
  have hψmul : ∀ x y : asML D f₁ f₂, ψ (x * y) = ψ x * ψ y := by
    intro x y
    apply asIota_injective D f₁ f₂
    calc asIota D f₁ f₂ (ψ (x * y)) = σS (asIota D f₁ f₂ (x * y)) := hψ (x * y)
      _ = σS (asIota D f₁ f₂ x * asIota D f₁ f₂ y) := by rw [map_mul]
      _ = σS (asIota D f₁ f₂ x) * σS (asIota D f₁ f₂ y) := by rw [map_mul]
      _ = asIota D f₁ f₂ (ψ x) * asIota D f₁ f₂ (ψ y) := by rw [hψ x, hψ y]
      _ = asIota D f₁ f₂ (ψ x * ψ y) := by rw [map_mul]
  have hψone : ψ 1 = 1 := by
    apply asIota_injective D f₁ f₂
    calc asIota D f₁ f₂ (ψ 1) = σS (asIota D f₁ f₂ 1) := hψ 1
      _ = σS 1 := by rw [map_one]
      _ = 1 := by rw [map_one]
      _ = asIota D f₁ f₂ 1 := by rw [map_one]
  have hψzero : ψ 0 = 0 := by
    apply asIota_injective D f₁ f₂
    calc asIota D f₁ f₂ (ψ 0) = σS (asIota D f₁ f₂ 0) := hψ 0
      _ = σS 0 := by rw [map_zero]
      _ = 0 := by rw [map_zero]
      _ = asIota D f₁ f₂ 0 := by rw [map_zero]
  let ψrh : asML D f₁ f₂ →+* asML D f₁ f₂ :=
    { toFun := ψ, map_one' := hψone, map_mul' := hψmul, map_zero' := hψzero, map_add' := hψadd }
  have hψinj : Function.Injective ψ := by
    intro a b hab
    have h1 : σS (asIota D f₁ f₂ a) = σS (asIota D f₁ f₂ b) := by
      rw [← hψ a, ← hψ b, hab]
    exact asIota_injective D f₁ f₂ (σS.injective h1)
  have hψsurj : Function.Surjective ψ := by
    intro m
    have hmΩ : asIota D f₁ f₂ m ∈ (Work.MotV5.kleinField D ⊔
        LImage D (asL2 (𝕜 := 𝕜) f₁ f₂)) := by
      rw [← hRange]
      exact (AlgHom.mem_fieldRange (f := asIota D f₁ f₂)).mpr ⟨m, rfl⟩
    obtain ⟨z, hzΩ, hz⟩ := hcrux (asIota D f₁ f₂ m) hmΩ
    obtain ⟨x, hx⟩ := (AlgHom.mem_fieldRange (f := asIota D f₁ f₂)).mp (by
      rw [hRange]; exact hzΩ)
    refine ⟨x, ?_⟩
    apply asIota_injective D f₁ f₂
    rw [hψ x, hx, hz]
  let ψe : asML D f₁ f₂ ≃+* asML D f₁ f₂ :=
    RingEquiv.ofBijective ψrh ⟨hψinj, hψsurj⟩
  have hLψ : ∀ l : ↥(asL2 (𝕜 := 𝕜) f₁ f₂),
      ψe (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) l) =
        algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) l := by
    intro l
    apply asIota_injective D f₁ f₂
    calc asIota D f₁ f₂ (ψe (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) l))
        = asIota D f₁ f₂ (ψ (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) l)) := rfl
      _ = σS (asIota D f₁ f₂ (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) l)) :=
            hψ (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) l)
      _ = σS (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (l : Work.MotV.Kb 𝕜)) := by
            rw [asIota_algebraMap D f₁ f₂ l]
      _ = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (l : Work.MotV.Kb 𝕜) :=
            σS.commutes (l : Work.MotV.Kb 𝕜)
      _ = asIota D f₁ f₂ (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) l) := by
            rw [asIota_algebraMap D f₁ f₂ l]
  refine ⟨AlgEquiv.ofRingEquiv (f := ψe) hLψ, ?_, ?_⟩
  · intro x
    show asIota D f₁ f₂ (AlgEquiv.ofRingEquiv (f := ψe) hLψ x) = σS (asIota D f₁ f₂ x)
    rw [show AlgEquiv.ofRingEquiv (f := ψe) hLψ x = ψ x from rfl]
    exact hψ x
  · intro l
    exact (AlgEquiv.ofRingEquiv (f := ψe) hLψ).commutes l

end Work.MotV5.LamAS

namespace Work.MotV5.Nodes

open WeierstrassCurve WeierstrassCurve.Affine
open Work.MotV5.LamAS
open Work.MotV5.LamAS.CoordNe
open Work.MotV5.LamAS.FixPsi

/-! ## Auxiliary lemmas: the trivial Artin–Schreier class

Two inputs for the branch of `lam_AS` in which the twisting class is trivial (equivalently
`asRoot g ∈ K`):

* the Klein cone has the **explicit point** `(0, 1, b/a, -b/a, -1)` — a polynomial identity;
* in characteristic `5` the "Galois coordinate" map `y ↦ asCoord w y` is an **interpolation map**
  at the five distinct nodes `w, w+1, …, w+4`, hence (for `w ∈ K`) it is surjective over `K`.

Together they yield the conclusion of `lam_AS`, with `ε = 1`, whenever `asRoot g ∈ K` — i.e. for
the degenerate twisting class `g ∈ ℘(K)`. -/

/-- **The Klein cone has an explicit nonzero point.**  `(0, 1, b/a, -b/a, -1)` lies on all five
Klein Pfaffians for any `a ≠ 0` (the identities are polynomial in `a, b`).  Note `a ≠ 0` and
`b ≠ 0` hold for the Klein data of this branch (`KleinData.Good.ab_ne`). -/
theorem kleinP_explicit_point {𝕜 : Type} [Field 𝕜] (a b : 𝕜) (ha : a ≠ 0) :
    ∀ k : Fin 5, Work.MotK.kleinP a b ![0, 1, b / a, -(b / a), -1] k = 0 := by
  intro k
  fin_cases k <;>
    simp only [Work.MotK.kleinP_zero', Work.MotK.kleinP_one', Work.MotK.kleinP_two',
      Work.MotK.kleinP_three', Work.MotK.kleinP_four', Work.MotK.kleinP0, Work.MotK.kleinP1,
      Work.MotK.kleinP2, Work.MotK.kleinP3, Work.MotK.kleinP4, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val] <;>
    field_simp <;> ring

/-- The Klein Pfaffians are compatible with ring homomorphisms (they are polynomials with integer
coefficients). -/
theorem kleinP_map {𝕜 L : Type} [Field 𝕜] [Field L] (f : 𝕜 →+* L) (a b : 𝕜) (x : Fin 5 → 𝕜)
    (k : Fin 5) :
    Work.MotK.kleinP (f a) (f b) (fun i => f (x i)) k = f (Work.MotK.kleinP a b x k) := by
  fin_cases k <;>
    simp only [Work.MotK.kleinP_zero', Work.MotK.kleinP_one', Work.MotK.kleinP_two',
      Work.MotK.kleinP_three', Work.MotK.kleinP_four', Work.MotK.kleinP0, Work.MotK.kleinP1,
      Work.MotK.kleinP2, Work.MotK.kleinP3, Work.MotK.kleinP4] <;>
    simp only [map_sub, map_mul, map_pow, map_neg, map_add]

/-- **The Galois-coordinate map is an interpolation map.**  In characteristic `5` the five nodes
`w, w+1, …, w+4` are pairwise distinct, so for every `x : Fin 5 → L` there is `y : Fin 5 → L` with
`asCoord w y = x` (the coefficients of the Lagrange interpolation polynomial of `x` at those
nodes).  Applied with `w ∈ K = RatFunc 𝕜` and `x` a constant vector, it produces `y : Fin 5 → K`. -/
theorem exists_asCoord_eq {L : Type} [Field L] [CharP L 5] (w : L) (x : Fin 5 → L) :
    ∃ y : Fin 5 → L, Work.MotV.asCoord w y = x := by
  classical
  have hchar : ∀ i j : Fin 5, ((i : ℕ) : L) = ((j : ℕ) : L) → i = j := by
    have key : ∀ m n : ℕ, m < 5 → n < 5 → ((m : ℕ) : L) = ((n : ℕ) : L) → m = n := by
      intro m n hm hn h
      rcases le_total m n with hle | hle
      · have h0 : (((n - m : ℕ)) : L) = 0 := by rw [Nat.cast_sub hle, h, sub_self]
        have hdvd : 5 ∣ (n - m) := (CharP.cast_eq_zero_iff L 5 (n - m)).mp h0
        have hlt : n - m < 5 := lt_of_le_of_lt (Nat.sub_le n m) hn
        interval_cases hnm : (n - m) <;> omega
      · have h0 : (((m - n : ℕ)) : L) = 0 := by rw [Nat.cast_sub hle, ← h, sub_self]
        have hdvd : 5 ∣ (m - n) := (CharP.cast_eq_zero_iff L 5 (m - n)).mp h0
        have hlt : m - n < 5 := lt_of_le_of_lt (Nat.sub_le m n) hm
        interval_cases hmn : (m - n) <;> omega
    intro i j hij
    exact Fin.ext (key (i : ℕ) (j : ℕ) i.isLt j.isLt hij)
  set v : Fin 5 → L := fun i => w + (i : L) with hv
  have hinj : Set.InjOn v (↑(Finset.univ : Finset (Fin 5))) := by
    intro i _ j _ hij
    exact hchar i j (add_left_cancel hij)
  set f : Polynomial L := (Lagrange.interpolate (Finset.univ : Finset (Fin 5)) v) x with hf
  have hdeg : f.natDegree < 5 := by
    rcases eq_or_ne f 0 with h0 | h0
    · rw [h0, Polynomial.natDegree_zero]; norm_num
    · rw [Polynomial.natDegree_lt_iff_degree_lt h0, hf]
      simpa using Lagrange.degree_interpolate_lt (s := (Finset.univ : Finset (Fin 5))) (v := v) x
        hinj
  refine ⟨fun j => f.coeff (j : ℕ), ?_⟩
  funext i
  rw [Work.MotV.asCoord]
  have heval : f.eval (w + (i : L)) = x i := by
    rw [hf]
    exact Lagrange.eval_interpolate_at_node x hinj (Finset.mem_univ i)
  have hsum : f.eval (w + (i : L)) = ∑ n ∈ Finset.range 5, f.coeff n * (w + (i : L)) ^ n :=
    Polynomial.eval_eq_sum_range' hdeg (w + (i : L))
  rw [hsum, ← Fin.sum_univ_eq_sum_range (fun n => f.coeff n * (w + (i : L)) ^ n) 5] at heval
  simpa using heval

/-- **The degenerate twisting class.**  If `asRoot g ∈ K` — i.e. `g` is an Artin–Schreier value
`c ^ 5 - c` — then the conclusion of `lam_AS` holds for the parameter `g` (with `ε = 1`): there is a
nonzero `y : Fin 5 → RatFunc 𝕜` whose Galois coordinates `asCoord (asRoot g) y` lie on the Klein
cone.

Proof: push the explicit point `(0, 1, b/a, -b/a, -1)` of `kleinP_explicit_point` into `K`, and
interpolate it at the nodes `W, W+1, …, W+4` (`exists_asCoord_eq`). -/
theorem exists_y_of_asRoot_mem (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (ha : D.a ≠ 0) (hb : D.b ≠ 0) (g : RatFunc 𝕜) (W : RatFunc 𝕜)
    (hW : algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) W = Work.MotV5.asRoot g) :
    ∃ y : Fin 5 → RatFunc 𝕜, y ≠ 0 ∧
      ∀ k, Work.MotK.kleinP (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a)
        (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b)
        (Work.MotV.asCoord (Work.MotV5.asRoot g)
          (fun j => algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (y j))) k = 0 := by
  classical
  haveI : CharP (RatFunc 𝕜) 5 :=
    charP_of_injective_algebraMap (algebraMap 𝕜 (RatFunc 𝕜)).injective 5
  set x : Fin 5 → RatFunc 𝕜 :=
    fun i => algebraMap 𝕜 (RatFunc 𝕜) (![0, 1, D.b / D.a, -(D.b / D.a), -1] i) with hxdef
  have hx1 : x 1 = 1 := by
    show algebraMap 𝕜 (RatFunc 𝕜) (![0, 1, D.b / D.a, -(D.b / D.a), -1] 1) = 1
    norm_num
  have hx : ∀ k, Work.MotK.kleinP (algebraMap 𝕜 (RatFunc 𝕜) D.a)
      (algebraMap 𝕜 (RatFunc 𝕜) D.b) x k = 0 := by
    intro k
    have h0 := kleinP_explicit_point D.a D.b ha k
    have h1 := kleinP_map (algebraMap 𝕜 (RatFunc 𝕜)) D.a D.b
      ![0, 1, D.b / D.a, -(D.b / D.a), -1] k
    rw [h0, map_zero] at h1
    simpa [hxdef] using h1
  have hxne : x ≠ 0 := by
    intro h
    have h1 := congrFun h 1
    rw [hx1] at h1
    exact one_ne_zero (α := RatFunc 𝕜) (by simpa using h1)
  obtain ⟨y, hy⟩ := exists_asCoord_eq W x
  have hyne : y ≠ 0 := by
    intro h0
    have h1 : Work.MotV.asCoord W y = 0 := by
      rw [h0]
      funext i
      rw [Work.MotV.asCoord]
      simp
    rw [hy] at h1
    exact hxne h1
  refine ⟨y, hyne, ?_⟩
  have hcoe : ∀ i, Work.MotV.asCoord (Work.MotV5.asRoot g)
      (fun j => algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (y j)) i
      = algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (x i) := by
    intro i
    rw [← hW, ← hy]
    simp only [Work.MotV.asCoord, map_sum, map_mul, map_pow, map_add, map_natCast]
  intro k
  have hfun : Work.MotV.asCoord (Work.MotV5.asRoot g)
      (fun j => algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (y j))
      = fun i => algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (x i) := funext hcoe
  rw [hfun]
  rw [IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (Work.MotV.Kb 𝕜) D.a,
      IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (Work.MotV.Kb 𝕜) D.b]
  rw [kleinP_map (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜)) (algebraMap 𝕜 (RatFunc 𝕜) D.a)
    (algebraMap 𝕜 (RatFunc 𝕜) D.b) x k, hx k, map_zero]

/-! ## The two-root model `M = K(W₁,W₂)(E)`

Both twist fields of `lam_AS` live in the compositum `M = K(W₁,W₂)(E) ⊆ Om D`, the function field
of the Klein curve over the compositum `L = K(W₁,W₂)` of the two Artin–Schreier fields.  This is
where the isomorphism `θ` extends (`Work.MotT.extend_algEquiv_of_linearDisjoint`: both `Fᵢ` are
linearly disjoint from `L` over `K` — their constants in `Kb 𝕜` are `K`, by
`asTwistFieldTrue_constants` — and `Fᵢ ⊔ L = M`) and where the classification
`Work.MotC2.aut_functionField` applies. -/

variable {𝕜 : Type} [Field 𝕜]

noncomputable section

/-- The image of `L = K(W₁, W₂)` in `Om D`. -/
def asK2D (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜) :
    IntermediateField (RatFunc 𝕜) (Work.MotV.Om D) :=
  IntermediateField.adjoin (RatFunc 𝕜)
    ({algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot f₁),
      algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot f₂)} :
        Set (Work.MotV.Om D))

/-- The model `M = K(W₁,W₂)(E) ⊆ Om D`. -/
def asM2 (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜) :
    IntermediateField (RatFunc 𝕜) (Work.MotV.Om D) :=
  Work.MotV5.kleinField D ⊔ asK2D D f₁ f₂

theorem asRoot_mem_asK2D_left (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜) :
    algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot f₁) ∈ asK2D D f₁ f₂ :=
  IntermediateField.subset_adjoin _ _ (by simp)

theorem asRoot_mem_asK2D_right (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜) :
    algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot f₂) ∈ asK2D D f₁ f₂ :=
  IntermediateField.subset_adjoin _ _ (by simp)

theorem asK2D_le_asM2 (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜) :
    asK2D D f₁ f₂ ≤ asM2 D f₁ f₂ := le_sup_right

theorem kleinField_le_asM2 (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜) :
    Work.MotV5.kleinField D ≤ asM2 D f₁ f₂ := le_sup_left

theorem asK2D_comm (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜) :
    asK2D D f₁ f₂ = asK2D D f₂ f₁ := by
  rw [asK2D, asK2D, Set.pair_comm]

theorem asM2_comm (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜) :
    asM2 D f₁ f₂ = asM2 D f₂ f₁ := by
  rw [asM2, asM2, asK2D_comm]

theorem asFieldL_le_asM2 (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜) :
    Work.MotV5.asFieldL D f₁ ≤ asM2 D f₁ f₂ := by
  rw [asM2, Work.MotV5.asFieldL]
  refine sup_le le_sup_left (le_trans ?_ le_sup_right)
  rw [asK2D]
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact IntermediateField.subset_adjoin _ _ (by simp)

theorem asTwistFieldTrue_le_asM2 (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    {f₁ f₂ : RatFunc 𝕜} (hg : g = f₁ ∨ g = f₂) :
    Work.MotV5.asTwistFieldTrue D g τ σS ≤ asM2 D f₁ f₂ := by
  rcases hg with hg | hg
  · rw [hg]
    exact le_trans (Work.MotV5.asTwistFieldTrue_le_asFieldL D f₁ τ σS) (asFieldL_le_asM2 D f₁ f₂)
  · rw [hg]
    exact le_trans (Work.MotV5.asTwistFieldTrue_le_asFieldL D f₂ τ σS)
      ((asFieldL_le_asM2 D f₂ f₁).trans (le_of_eq (asM2_comm D f₁ f₂).symm))

/-! ## Design of the remaining pieces of the proof of `lam_AS`

The two proved special cases above (`exists_y_of_asRoot_mem`) cover the *degenerate* twisting
class.  The general proof is the transposition of the characteristic-`≠ 5` node `T4`
(`Work.MotT.twist_iso_pointK`, proved) to the Artin–Schreier branch, and runs as follows.

Let `L = K(W₁,W₂)` (`asK2D`) and `M = L(E)` (`asM2 = kleinField ⊔ asK2D`); the twist fields
`Fᵢ = asTwistFieldTrue D fᵢ τᵢ σS` satisfy `Fᵢ ≤ M`.

1. *(done, workspace)* `Fᵢ ⊔ K(Wᵢ) = asFieldL D fᵢ` (`Work.MotV5.RigAS.twistFieldTrue_sup_asRoot`),
   `Fᵢ ∩ Kb = K` (`asTwistFieldTrue_constants`), hence `Fᵢ ⊔ L = M`.
2. *(to do)* the extension of `θ : F₁ ≅ F₂` to `Θ : M ≃ₐ[L] M` with `Θ|F₁ = θ`
   (`Work.MotT.extend_algEquiv_of_linearDisjoint`, generic: linear disjointness from step 1 +
   `Fᵢ ⊔ L = ⊤`).
3. *(available)* node C2 over `L`: `Work.MotC2.aut_functionField` gives `Θ = τ_Q ∘ neg^ε`
   (`Q ∈ E(L)`, `ε : Fin 2`).
4. *(to do)* the comparison `Θ ψ^{(1)}_γ Θ⁻¹ = ψ^{(2)}_γ` for the twisted Galois actions
   `ψ^{(i)}_γ = σS^{χᵢ(γ)} ∘ γ̃` — as in `Work.MotT.T4_compare`: both sides are `K`-automorphisms of
   `M` acting as `γ` on `L` and fixing `F₂ = Θ(F₁)` pointwise, and `M` is generated by them.
5. *(to do)* the defect computation: with `σS = τ_T` a translation
   (`Work.MotV5.GenAux_neg_conj_sigmaS` excludes the `neg`-alternative;
   `Work.MotV5.Nodes.shiftOf_eq_transAlgEquiv`) and `neg τ_Q neg = τ_{-Q}`, the comparison gives
   `γQ - Q = (χ₂ ± χ₁)(γ)·T` for all `γ ∈ Gal(K̄/K)`: `∓Q` is then a *twisted* point of the AS
   class `f₁ ∓ f₂`.
6. *(to do, the crux)* the coordinate extraction: from a point `Q` with `γQ - Q = χ_g(γ)T` produce
   `y : Fin 5 → K` with `kleinP a b (asCoord (asRoot g) y) = 0`.  The candidates are the
   interpolation coefficients of the Klein point `(κ_i(Q))_i` at the nodes `W+i` (the AS analogue
   of `Work.MotT.twistPointK_coords`, which uses `y_j = w'^{-j} κ_j(R)`); the rationality of `y` is
   the projective Galois invariance, and it needs the normalisation of the Klein coordinates
   (a Hilbert-90-type step, or the canonical normalisation of the Klein model).

   **Trap (found by review of `exists_ratFunc_of_galois_shift`, a false statement).**  In
   characteristic `5` the fixed field of `Gal(Kb/K)` is *not* `K` but the purely inseparable
   closure `K^{p^{-∞}}`; `x i := t^{1/5}` is fixed by every `K`-automorphism of `Kb` and is not
   rational, and `x i := w + i` for `w = asRoot g ∉ K` is *shifted* (satisfying the naive
   Galois-shift hypothesis) without being rational.  So the rationality of the interpolation
   coefficients `y` must come from the *twisted* structure (they are the coordinates of a
   `K`-point of the twist, i.e. elements of `K` by construction), not from Galois invariance alone;
   equivalently one must track the normalising scalars `Λ_χ(Q)` explicitly.  Note also that the
   conclusion's point `asCoord (asRoot g) y` has *irrational* coordinates in the Klein model when
   `g ∉ ℘(K)` — only its twisted coordinates are rational — so it is not the naive `C(K) ≠ ∅`.
7. assembly, with `ε = ±1` from the two branches (`ε = 0`: the class `f₁ - f₂`; `ε = 1`: `f₁+f₂`),
   and the degenerate case of §1 (`exists_y_of_asRoot_mem`) for the branch in which the twisting
   class of `f₁ ∓ f₂` is trivial. -/


/-- **Node LAM_AS — an isomorphism of two Artin–Schreier twists produces a point of a twisted
Klein curve.**  (Corrected form of `Work.MotV5.Nodes.twistField_iso_class`; see the docstring of
`Submission/Work/MotV5/Nodes/twistField_iso_class.lean` for why the statement is for a
`RatFunc 𝕜`-linear isomorphism and why the conclusion is a *point* rather than a class identity.)

Let `f₁, f₂ : RatFunc 𝕜` carry admissible twisting data (`Work.MotV5.ASTwistData`, sharing the
projective fifth-torsion shift `σS`).  If the two twist fields are isomorphic as `RatFunc 𝕜`-algebras
then there are `ε = ±1` and a nonzero tuple `y : Fin 5 → RatFunc 𝕜` whose Galois coordinates for the
parameter `f₁ - ε f₂` satisfy the Klein equations, i.e. the twisted Klein curve `C^AS_{f₁ - ε f₂}`
has a `K`-rational point.  This is the honest output of the cocycle computation
(`Work.MotC2.aut_functionField` classifies the extension of `θ` to `L(E)` as `τ_R ∘ (neg)^ε`); it is
consumed by `Work.MotV5.fifthPowAtPoles_of_asPoint` (proved) and thereby contradicts the proved
`Work.MotV5.exponent_rigidity_AS` for the pair `f₁ = fAS 𝕜`, `f₂ = 2 • fAS 𝕜`. -/
theorem lam_AS (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (f₁ f₂ : RatFunc 𝕜)
    (τ₁ τ₂ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ₁ σ₂ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (h1 : Work.MotV5.ASTwistData 𝕜 D f₁ τ₁ σS σ₁)
    (h2 : Work.MotV5.ASTwistData 𝕜 D f₂ τ₂ σS σ₂)
    (θ : ↥(Work.MotV5.asTwistFieldTrue D f₁ τ₁ σS) ≃ₐ[RatFunc 𝕜]
      ↥(Work.MotV5.asTwistFieldTrue D f₂ τ₂ σS)) :
    ∃ (ε : ℤ) (_ : ε = 1 ∨ ε = -1) (y : Fin 5 → RatFunc 𝕜), y ≠ 0 ∧
      ∀ k, Work.MotK.kleinP (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a)
        (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b)
        (Work.MotV.asCoord
          (Work.MotV5.asRoot (f₁ - algebraMap 𝕜 (RatFunc 𝕜) ((ε : ℤ) : 𝕜) * f₂))
          (fun j => algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (y j))) k = 0 := by

  classical
  haveI hDec : DecidableEq ↥(asL2 (𝕜 := 𝕜) f₁ f₂) := Classical.decEq _
  haveI hGal : IsGalois (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) := (asL2_isGalois 𝕜 f₁ f₂).1
  haveI hFin : FiniteDimensional (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) := (asL2_isGalois 𝕜 f₁ f₂).2
  haveI hEllD : D.E.IsElliptic := hD.1.elliptic
  haveI hEll : (asE2 D f₁ f₂).IsElliptic :=
    inferInstanceAs ((D.E.map (algebraMap 𝕜 ↥(asL2 (𝕜 := 𝕜) f₁ f₂))).IsElliptic)
  have hRange := asIota_range 𝕜 D hD f₁ f₂
  have hσSΩ := sigmaS_mem_Omega D hD.1 f₁ f₂ σS h1.hσS
  obtain ⟨σS', hσS', -⟩ := asSigmaLift_ext D hD f₁ f₂ σS hRange hσSΩ
    (sigmaS_pow_five_eq_one D hD σS h1.hσS)
  have hcomm := asSigmaLift_comm 𝕜 D hD f₁ f₂ σS h1.hσS σS' hσS'
  -- ### the two Artin–Schreier roots
  set W₁ : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) :=
    ⟨Work.MotV5.asRoot f₁, asRoot_mem_asL2_left f₁ f₂⟩ with hW₁def
  set W₂ : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) :=
    ⟨Work.MotV5.asRoot f₂, asRoot_mem_asL2_right f₁ f₂⟩ with hW₂def
  have hW₁ : W₁ ^ 5 - W₁ = algebraMap (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) f₁ := by
    apply Subtype.ext
    change (W₁ : Work.MotV.Kb 𝕜) ^ 5 - (W₁ : Work.MotV.Kb 𝕜) = _
    rw [hW₁def, Work.MotV5.asRoot_spec]
    exact IsScalarTower.algebraMap_apply (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (Work.MotV.Kb 𝕜) f₁
  have hW₂ : W₂ ^ 5 - W₂ = algebraMap (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) f₂ := by
    apply Subtype.ext
    change (W₂ : Work.MotV.Kb 𝕜) ^ 5 - (W₂ : Work.MotV.Kb 𝕜) = _
    rw [hW₂def, Work.MotV5.asRoot_spec]
    exact IsScalarTower.algebraMap_apply (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (Work.MotV.Kb 𝕜) f₂
  -- ### the extension of `θ`
  obtain ⟨hF1, hsup1, -⟩ := asF_transfer 𝕜 D hD f₁ f₂ f₁ τ₁ σS σ₁ h1 (Or.inl rfl) hRange
  obtain ⟨hF2, hsup2, -⟩ := asF_transfer 𝕜 D hD f₁ f₂ f₂ τ₂ σS σ₂ h2 (Or.inr rfl) hRange
  have hLI1 := asF_linearDisjoint 𝕜 D hD f₁ f₂ f₁ τ₁ σS σ₁ h1 (Or.inl rfl)
  have hLI2 := asF_linearDisjoint 𝕜 D hD f₁ f₂ f₂ τ₂ σS σ₂ h2 (Or.inr rfl)
  obtain ⟨Θ, hΘext⟩ := asExtendTheta 𝕜 D hD f₁ f₂ τ₁ τ₂ σS hF1 hF2 hLI1 hLI2 hsup1 hsup2 θ
  have hΘmem : ∀ x ∈ asF D f₁ f₂ f₁ τ₁ σS, Θ x ∈ asF D f₁ f₂ f₂ τ₂ σS := by
    intro x hx
    show asIota D f₁ f₂ (Θ x) ∈ Work.MotV5.asTwistFieldTrue D f₂ τ₂ σS
    rw [hΘext ⟨x, hx⟩ hx]
    exact (θ ⟨asIota D f₁ f₂ x, hx⟩).2
  -- ### node C2 over `L`
  obtain ⟨Q, ε₂, hQε⟩ := asML_c2 𝕜 D hD f₁ f₂ Θ
  obtain ⟨T, hσS'T, hT5, hTne⟩ := asSigmaLift_eq_trans 𝕜 D hD f₁ f₂ σS h1.hσS σS' hσS'
  -- ### the twisted Galois actions
  have hfix₁ : ∀ γ, ∀ x ∈ asF D f₁ f₂ f₁ τ₁ σS, asPsi D f₁ f₂ f₁ σS' W₁ hW₁ γ x = x :=
    fun γ => asPsi_fixes_asF 𝕜 D hD f₁ f₂ f₁ τ₁ σS σ₁ h1 (Or.inl rfl) hRange σS' hσS'
      hcomm W₁ hW₁ γ
  have hfix₂ : ∀ γ, ∀ x ∈ asF D f₁ f₂ f₂ τ₂ σS, asPsi D f₁ f₂ f₂ σS' W₂ hW₂ γ x = x :=
    fun γ => asPsi_fixes_asF 𝕜 D hD f₁ f₂ f₂ τ₂ σS σ₂ h2 (Or.inr rfl) hRange σS' hσS'
      hcomm W₂ hW₂ γ
  have hcomp : ∀ γ, Θ.restrictScalars (RatFunc 𝕜) * (asPsi D f₁ f₂ f₁ σS' W₁ hW₁ γ) =
      (asPsi D f₁ f₂ f₂ σS' W₂ hW₂ γ) * Θ.restrictScalars (RatFunc 𝕜) :=
    fun γ => asCompare 𝕜 D hD f₁ f₂ f₁ f₂ τ₁ τ₂ σS σS' W₁ W₂ hW₁ hW₂ γ Θ hΘmem hsup1
      (hfix₁ γ) (hfix₂ γ)
  have hdefect : ∀ γ, WeierstrassCurve.Affine.Point.map (W' := D.E) (S := 𝕜)
        (F := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) (K := ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
        (γ.restrictScalars 𝕜).toAlgHom Q - Q =
      ((-1 : ℤ) ^ (ε₂ : ℕ) * ((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ) -
        ((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ)) • T :=
    fun γ => asDefect 𝕜 D hD f₁ f₂ f₁ f₂ τ₁ τ₂ σS σS' W₁ W₂ hW₁ hW₂ ε₂ Q T hσS'T Θ hQε
      hcomp γ
  -- ### the twist property of `T`
  have hQshift : ∃ lam : Work.MotC2.Func (D.E.baseChange ↥(asL2 (𝕜 := 𝕜) f₁ f₂)), lam ≠ 0 ∧
      ∀ i : Fin 5, Work.MotC2.transAlgEquiv (D.E.baseChange ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) T
        (Work.MotV.kleinCoord D ↥(asL2 (𝕜 := 𝕜) f₁ f₂) i) =
          lam * Work.MotV.kleinCoord D ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (i + 1) := by
    obtain ⟨lam0, hlam0ne, hlam0⟩ := h1.hσS
    have hκ1 : Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 1 ≠ 0 := by
      intro h1'
      have h := hlam0 0
      rw [show (0 : Fin 5) + 1 = 1 from rfl, h1', mul_zero] at h
      exact hD.1.coord0_ne (Work.MotV.Kb 𝕜) (σS.injective (by rw [h, map_zero]))
    have hκ0r : Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0 ∈ (asIota D f₁ f₂).fieldRange := by
      rw [← asIota_kleinCoord D f₁ f₂ 0]
      exact AlgHom.mem_fieldRange.mpr ⟨_, rfl⟩
    have hκ1r : Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 1 ∈ (asIota D f₁ f₂).fieldRange := by
      rw [← asIota_kleinCoord D f₁ f₂ 1]
      exact AlgHom.mem_fieldRange.mpr ⟨_, rfl⟩
    have hσSκ0 : σS (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0) ∈ (asIota D f₁ f₂).fieldRange := by
      rw [hRange]
      refine hσSΩ _ ?_
      rw [← asIota_kleinCoord D f₁ f₂ 0, ← hRange]
      exact AlgHom.mem_fieldRange.mpr ⟨_, rfl⟩
    have hlam : lam0 = σS (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0) *
        (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 1)⁻¹ := by
      rw [hlam0 0]
      rw [show (0 : Fin 5) + 1 = 1 from rfl]
      field_simp
    have hmem : lam0 ∈ (asIota D f₁ f₂).fieldRange := by
      rw [hlam]
      exact mul_mem hσSκ0 (inv_mem hκ1r)
    obtain ⟨lam, hlam'⟩ := AlgHom.mem_fieldRange.mp hmem
    refine ⟨lam, ?_, ?_⟩
    · intro h0
      rw [h0, map_zero] at hlam'
      exact hlam0ne hlam'.symm
    · intro i
      apply asIota_injective D f₁ f₂
      rw [← hσS'T]
      calc asIota D f₁ f₂ (σS' (Work.MotV.kleinCoord D ↥(asL2 (𝕜 := 𝕜) f₁ f₂) i))
          = σS (asIota D f₁ f₂ (Work.MotV.kleinCoord D ↥(asL2 (𝕜 := 𝕜) f₁ f₂) i)) :=
            hσS' _
        _ = σS (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i) := by rw [asIota_kleinCoord]
        _ = lam0 * Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) (i + 1) := hlam0 i
        _ = asIota D f₁ f₂ (lam * Work.MotV.kleinCoord D ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (i + 1)) := by
            rw [map_mul, asIota_kleinCoord, hlam']
  -- ### the two branches of node C2
  have hmapQ : ∀ γ : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜] ↥(asL2 (𝕜 := 𝕜) f₁ f₂),
      WeierstrassCurve.Affine.Point.map (W' := D.E) (S := RatFunc 𝕜)
          (F := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) (K := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) γ.toAlgHom Q
        = WeierstrassCurve.Affine.Point.map (W' := D.E) (S := 𝕜)
          (F := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) (K := ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
          (γ.restrictScalars 𝕜).toAlgHom Q := fun γ => rfl
  have hε01 : ε₂ = 0 ∨ ε₂ = 1 := by fin_cases ε₂ <;> simp
  rcases hε01 with hε | hε
  · -- #### ε₂ = 0 : the class is `f₁ - f₂`
    have hpow : (-1 : ℤ) ^ (ε₂ : ℕ) = 1 := by rw [hε]; norm_num
    have hcf : (⟨Work.MotV5.asRoot (f₁ - f₂), asRoot_sub_mem f₁ f₂⟩ : ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) ^ 5
        - ⟨Work.MotV5.asRoot (f₁ - f₂), asRoot_sub_mem f₁ f₂⟩
        = algebraMap (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (f₁ - f₂) := by
      apply Subtype.ext
      change (Work.MotV5.asRoot (f₁ - f₂) : Work.MotV.Kb 𝕜) ^ 5
        - (Work.MotV5.asRoot (f₁ - f₂) : Work.MotV.Kb 𝕜) = _
      rw [Work.MotV5.asRoot_spec]
      exact IsScalarTower.algebraMap_apply (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂)
        (Work.MotV.Kb 𝕜) (f₁ - f₂)
    let d : (↥(asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜] ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) → Fin 5 :=
      fun γ => asShift D f₁ f₂ (f₁ - f₂) ⟨Work.MotV5.asRoot (f₁ - f₂), asRoot_sub_mem f₁ f₂⟩ hcf γ
    have hd : ∀ γ, γ ⟨Work.MotV5.asRoot (f₁ - f₂), asRoot_sub_mem f₁ f₂⟩
        = ⟨Work.MotV5.asRoot (f₁ - f₂), asRoot_sub_mem f₁ f₂⟩
          + algebraMap ℤ ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (((d γ : Fin 5) : ℤ)) :=
      fun γ => asShift_spec D f₁ f₂ (f₁ - f₂)
        ⟨Work.MotV5.asRoot (f₁ - f₂), asRoot_sub_mem f₁ f₂⟩ hcf γ
    have hdef0 : ∀ γ, WeierstrassCurve.Affine.Point.map (W' := D.E) (S := 𝕜)
          (F := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) (K := ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
          (γ.restrictScalars 𝕜).toAlgHom Q - Q =
        (((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ) -
          ((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ)) • T := by
      intro γ
      have h := hdefect γ
      rw [hpow] at h
      simpa using h
    by_cases hQ0 : Q = 0
    · -- the trivial class
      have hd0 : ∀ γ, d γ = 0 := by
        intro γ
        have h := hdef0 γ
        rw [hQ0, WeierstrassCurve.Affine.Point.map_zero, sub_zero] at h
        have hz : (((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ) -
            ((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ)) • T = 0 := h.symm
        have hdvd := five_dvd_of_zsmul_eq_zero hT5 hTne hz
        have hcast : algebraMap ℤ ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (((d γ : Fin 5) : ℤ))
            = algebraMap ℤ ↥(asL2 (𝕜 := 𝕜) f₁ f₂)
              (((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ) -
                ((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ)) := by
          rw [asShift_sub_eq D f₁ f₂ W₁ W₂
            ⟨Work.MotV5.asRoot (f₁ - f₂), asRoot_sub_mem f₁ f₂⟩ hW₁ hW₂ hcf γ, map_sub]
        have hzero : algebraMap ℤ ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (((d γ : Fin 5) : ℤ)) = 0 := by
          rw [hcast]
          obtain ⟨c, hc⟩ := hdvd
          rw [hc, map_mul]
          have h5z : algebraMap ℤ ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (5 : ℤ) = 0 := by
            rw [show (5 : ℤ) = ((5 : ℕ) : ℤ) from rfl, map_natCast, CharP.cast_eq_zero]
          rw [h5z, zero_mul]
        have hdvd2 : (5 : ℤ) ∣ ((d γ : Fin 5) : ℤ) :=
          (CharP.intCast_eq_zero_iff ↥(asL2 (𝕜 := 𝕜) f₁ f₂) 5 _).mp hzero
        obtain ⟨c, hc⟩ := hdvd2
        exact Fin.ext (by have := (d γ).isLt; omega)
      have hfixed : ∀ γ : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜] ↥(asL2 (𝕜 := 𝕜) f₁ f₂),
          γ ⟨Work.MotV5.asRoot (f₁ - f₂), asRoot_sub_mem f₁ f₂⟩
            = ⟨Work.MotV5.asRoot (f₁ - f₂), asRoot_sub_mem f₁ f₂⟩ := by
        intro γ
        rw [hd γ, hd0 γ]
        simp
      obtain ⟨W, hW⟩ := (IsGalois.mem_range_algebraMap_iff_fixed
        (⟨Work.MotV5.asRoot (f₁ - f₂), asRoot_sub_mem f₁ f₂⟩ :
          ↥(asL2 (𝕜 := 𝕜) f₁ f₂))).mpr hfixed
      have hWas : algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) W = Work.MotV5.asRoot (f₁ - f₂) := by
        have h := congrArg (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (Work.MotV.Kb 𝕜)) hW
        rw [← IsScalarTower.algebraMap_apply (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂)
          (Work.MotV.Kb 𝕜) W] at h
        exact h
      obtain ⟨y, hyne, hyk⟩ := exists_y_of_asRoot_mem 𝕜 D
        (fun ha => hD.1.ab_ne (by rw [ha, zero_mul])) (fun hb => hD.1.ab_ne (by rw [hb, mul_zero]))
        (f₁ - f₂) W hWas
      refine ⟨1, Or.inl rfl, y, hyne, fun k => ?_⟩
      have hpar : f₁ - algebraMap 𝕜 (RatFunc 𝕜) ((1 : ℤ) : 𝕜) * f₂ = f₁ - f₂ := by simp
      rw [hpar]
      exact hyk k
    · -- the non-degenerate case: extract the Klein point of `C^AS_{f₁-f₂}`
      have hR : ∀ γ, WeierstrassCurve.Affine.Point.map (W' := D.E) (S := RatFunc 𝕜)
          (F := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) (K := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) γ.toAlgHom Q
          = Q + ((d γ : ℕ) • T) := by
        intro γ
        have h := hdef0 γ
        rw [← hmapQ γ] at h
        have hcast : algebraMap ℤ ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (((d γ : Fin 5) : ℤ))
            = algebraMap ℤ ↥(asL2 (𝕜 := 𝕜) f₁ f₂)
              (((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ) -
                ((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ)) := by
          rw [asShift_sub_eq D f₁ f₂ W₁ W₂
            ⟨Work.MotV5.asRoot (f₁ - f₂), asRoot_sub_mem f₁ f₂⟩ hW₁ hW₂ hcf γ, map_sub]
        have hsmul := smul_eq_of_intCast_eq hcast T hT5
        rw [sub_eq_iff_eq_add] at h
        rw [add_comm] at h
        rw [h, ← hsmul, natCast_zsmul]
      obtain ⟨y, hyne, hyk⟩ := Work.MotV5.LamAS.CoordNe.asTwistPoint_coords_ne D hD (f₁ - f₂)
        (asL2 (𝕜 := 𝕜) f₁ f₂) (asRoot_sub_mem f₁ f₂) T Q hQ0 hQshift d hd hR
      refine ⟨1, Or.inl rfl, y, hyne, fun k => ?_⟩
      have hpar : f₁ - algebraMap 𝕜 (RatFunc 𝕜) ((1 : ℤ) : 𝕜) * f₂ = f₁ - f₂ := by simp
      rw [hpar]
      exact hyk k
  · -- #### ε₂ = 1 : the class is `f₁ + f₂`
    have hpow : (-1 : ℤ) ^ (ε₂ : ℕ) = -1 := by rw [hε]; norm_num
    have hca : (⟨Work.MotV5.asRoot (f₁ + f₂), asRoot_add_mem f₁ f₂⟩ : ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) ^ 5
        - ⟨Work.MotV5.asRoot (f₁ + f₂), asRoot_add_mem f₁ f₂⟩
        = algebraMap (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (f₁ + f₂) := by
      apply Subtype.ext
      change (Work.MotV5.asRoot (f₁ + f₂) : Work.MotV.Kb 𝕜) ^ 5
        - (Work.MotV5.asRoot (f₁ + f₂) : Work.MotV.Kb 𝕜) = _
      rw [Work.MotV5.asRoot_spec]
      exact IsScalarTower.algebraMap_apply (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂)
        (Work.MotV.Kb 𝕜) (f₁ + f₂)
    let d : (↥(asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜] ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) → Fin 5 :=
      fun γ => asShift D f₁ f₂ (f₁ + f₂) ⟨Work.MotV5.asRoot (f₁ + f₂), asRoot_add_mem f₁ f₂⟩ hca γ
    have hd : ∀ γ, γ ⟨Work.MotV5.asRoot (f₁ + f₂), asRoot_add_mem f₁ f₂⟩
        = ⟨Work.MotV5.asRoot (f₁ + f₂), asRoot_add_mem f₁ f₂⟩
          + algebraMap ℤ ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (((d γ : Fin 5) : ℤ)) :=
      fun γ => asShift_spec D f₁ f₂ (f₁ + f₂)
        ⟨Work.MotV5.asRoot (f₁ + f₂), asRoot_add_mem f₁ f₂⟩ hca γ
    have hdef1 : ∀ γ, WeierstrassCurve.Affine.Point.map (W' := D.E) (S := 𝕜)
          (F := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) (K := ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
          (γ.restrictScalars 𝕜).toAlgHom Q - Q =
        (-(((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ)) -
          ((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ)) • T := by
      intro γ
      have h := hdefect γ
      rw [hpow] at h
      simpa using h
    by_cases hQ0 : Q = 0
    · -- the trivial class
      have hd0 : ∀ γ, d γ = 0 := by
        intro γ
        have h := hdef1 γ
        rw [hQ0, WeierstrassCurve.Affine.Point.map_zero, sub_zero] at h
        have hz : (-(((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ)) -
            ((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ)) • T = 0 := h.symm
        have hdvd := five_dvd_of_zsmul_eq_zero hT5 hTne hz
        have hz0 : algebraMap ℤ ↥(asL2 (𝕜 := 𝕜) f₁ f₂)
            (-(((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ)) -
              ((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ)) = 0 := by
          obtain ⟨c, hc⟩ := hdvd
          rw [hc, map_mul]
          have h5z : algebraMap ℤ ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (5 : ℤ) = 0 := by
            rw [show (5 : ℤ) = ((5 : ℕ) : ℤ) from rfl, map_natCast, CharP.cast_eq_zero]
          rw [h5z, zero_mul]
        have hsum : algebraMap ℤ ↥(asL2 (𝕜 := 𝕜) f₁ f₂)
            (((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ) +
              ((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ)) = 0 := by
          have hneg : algebraMap ℤ ↥(asL2 (𝕜 := 𝕜) f₁ f₂)
              (((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ) +
                ((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ))
              = -algebraMap ℤ ↥(asL2 (𝕜 := 𝕜) f₁ f₂)
                (-(((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ)) -
                  ((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ)) := by
            rw [map_add, map_sub, map_neg]
            refl_ring1
          rw [hneg, hz0, neg_zero]
        have hcast : algebraMap ℤ ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (((d γ : Fin 5) : ℤ))
            = algebraMap ℤ ↥(asL2 (𝕜 := 𝕜) f₁ f₂)
              (((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ) +
                ((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ)) := by
          rw [asShift_add_eq D f₁ f₂ W₁ W₂
            ⟨Work.MotV5.asRoot (f₁ + f₂), asRoot_add_mem f₁ f₂⟩ hW₁ hW₂ hca γ]
          exact (map_add (algebraMap ℤ ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
            (((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ))
            (((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ))).symm
        have hzero : algebraMap ℤ ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (((d γ : Fin 5) : ℤ)) = 0 := by
          rw [hcast, hsum]
        have hdvd2 : (5 : ℤ) ∣ ((d γ : Fin 5) : ℤ) :=
          (CharP.intCast_eq_zero_iff ↥(asL2 (𝕜 := 𝕜) f₁ f₂) 5 _).mp hzero
        obtain ⟨c, hc⟩ := hdvd2
        exact Fin.ext (by have := (d γ).isLt; omega)
      have hfixed : ∀ γ : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) ≃ₐ[RatFunc 𝕜] ↥(asL2 (𝕜 := 𝕜) f₁ f₂),
          γ ⟨Work.MotV5.asRoot (f₁ + f₂), asRoot_add_mem f₁ f₂⟩
            = ⟨Work.MotV5.asRoot (f₁ + f₂), asRoot_add_mem f₁ f₂⟩ := by
        intro γ
        rw [hd γ, hd0 γ]
        simp
      obtain ⟨W, hW⟩ := (IsGalois.mem_range_algebraMap_iff_fixed
        (⟨Work.MotV5.asRoot (f₁ + f₂), asRoot_add_mem f₁ f₂⟩ :
          ↥(asL2 (𝕜 := 𝕜) f₁ f₂))).mpr hfixed
      have hWas : algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) W = Work.MotV5.asRoot (f₁ + f₂) := by
        have h := congrArg (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (Work.MotV.Kb 𝕜)) hW
        rw [← IsScalarTower.algebraMap_apply (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂)
          (Work.MotV.Kb 𝕜) W] at h
        exact h
      obtain ⟨y, hyne, hyk⟩ := exists_y_of_asRoot_mem 𝕜 D
        (fun ha => hD.1.ab_ne (by rw [ha, zero_mul])) (fun hb => hD.1.ab_ne (by rw [hb, mul_zero]))
        (f₁ + f₂) W hWas
      refine ⟨-1, Or.inr rfl, y, hyne, fun k => ?_⟩
      have hpar : f₁ - algebraMap 𝕜 (RatFunc 𝕜) (((-1 : ℤ)) : 𝕜) * f₂ = f₁ + f₂ := by simp
      rw [hpar]
      exact hyk k
    · -- the non-degenerate case
      have hR : ∀ γ, WeierstrassCurve.Affine.Point.map (W' := D.E) (S := RatFunc 𝕜)
          (F := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) (K := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) γ.toAlgHom (-Q)
          = -Q + ((d γ : ℕ) • T) := by
        intro γ
        have h := hdef1 γ
        rw [← hmapQ γ] at h
        have hcast : algebraMap ℤ ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (((d γ : Fin 5) : ℤ))
            = algebraMap ℤ ↥(asL2 (𝕜 := 𝕜) f₁ f₂)
              (((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ) +
                ((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ)) := by
          rw [asShift_add_eq D f₁ f₂ W₁ W₂
            ⟨Work.MotV5.asRoot (f₁ + f₂), asRoot_add_mem f₁ f₂⟩ hW₁ hW₂ hca γ]
          exact (map_add (algebraMap ℤ ↥(asL2 (𝕜 := 𝕜) f₁ f₂))
            (((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ))
            (((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ))).symm
        have hsmul := smul_eq_of_intCast_eq hcast T hT5
        have hz' : -(-(((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ)) -
              ((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ))
            = ((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ) +
              ((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ) := by ring
        rw [sub_eq_iff_eq_add] at h
        calc WeierstrassCurve.Affine.Point.map (W' := D.E) (S := RatFunc 𝕜)
              (F := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) (K := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) γ.toAlgHom (-Q)
            = -WeierstrassCurve.Affine.Point.map (W' := D.E) (S := RatFunc 𝕜)
              (F := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) (K := ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) γ.toAlgHom Q :=
                map_neg _ _
          _ = -(Q + (-(((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ)) -
                ((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ)) • T) := by rw [h, add_comm]
          _ = -Q + (-(-(((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ)) -
                ((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ))) • T := by
                rw [neg_add, neg_zsmul]
          _ = -Q + (((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ) +
                ((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ)) • T := by rw [hz']
          _ = -Q + ((d γ : Fin 5) : ℤ) • T := by rw [← hsmul]
          _ = -Q + (d γ : ℕ) • T := by rw [natCast_zsmul]
      obtain ⟨y, hyne, hyk⟩ := Work.MotV5.LamAS.CoordNe.asTwistPoint_coords_ne D hD (f₁ + f₂)
        (asL2 (𝕜 := 𝕜) f₁ f₂) (asRoot_add_mem f₁ f₂) T (-Q)
        (fun h0 => hQ0 (neg_eq_zero.mp h0)) hQshift d hd hR
      refine ⟨-1, Or.inr rfl, y, hyne, fun k => ?_⟩
      have hpar : f₁ - algebraMap 𝕜 (RatFunc 𝕜) (((-1 : ℤ)) : 𝕜) * f₂ = f₁ + f₂ := by simp
      rw [hpar]
      exact hyk k


end

end Work.MotV5.Nodes
