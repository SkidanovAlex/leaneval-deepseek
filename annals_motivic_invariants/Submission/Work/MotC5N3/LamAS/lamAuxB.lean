import Mathlib
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotC2.aut_functionField
import Submission.Work.MotC5N3.TwistField.asTwistFieldTrue_basic
import Submission.Work.MotT.extend_algEquiv_of_linearDisjoint
import Submission.Work.MotC5N3.Nodes.shiftOf_eq_transAlgEquiv
import Submission.Work.MotC5N3.RigAS.twistFieldTrue_sup_asRoot
import Submission.Work.MotC5N3.LamAS.asPsi
import Submission.Work.MotC5N3.LamAS.asPsi_aux
import Submission.Work.MotC5N3.LamAS.asTransport
import Submission.Work.MotC5N3.LamAS.asIota_range
import Submission.Work.MotC5N3.LamAS.asML_c2
import Submission.Work.MotC5N3.LamAS.asSigmaLift_eq_trans
import Submission.Work.MotC5N3.LamAS.asSigmaLift_comm
import Submission.Work.MotC5N3.LamAS.asF_transfer
import Submission.Work.MotC5N3.LamAS.asF_linearDisjoint
import Submission.Work.MotC5N3.LamAS.asExtendTheta
import Submission.Work.MotC5N3.LamAS.asL2_isGalois
import Submission.Work.MotC5N3.LamAS.asExtension
import Submission.Work.MotC5N3.LamAS.asCompare
import Submission.Work.MotC5N3.LamAS.root_eq_asRoot_add
import Submission.Work.MotC5N3.LamAS.CoordNe.asTwistPoint_coords_ne
import Submission.Work.MotC5N3.LamAS.FixPsi.asPsi_fixes_asF
import Submission.Work.MotC5N3.LamAS.asDefect
import Submission.Work.MotC5N3.GenAux_sigmaS_pow_five_kleinField
import Submission.Work.MotC5N3.TwistField.kleinField_eq_adjoin_genXY
import Submission.Work.MotC2.FuncExt
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 4000000

namespace Work.MotC5N3.LamAS
variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5] {K : Type} [Field K] [Algebra 𝕜 K] [CharP K 5]

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
theorem asL2_intCast_comp (f₁ f₂ : K) (z : ℤ) :
    (algebraMap ↥(asL2 f₁ f₂) (Work.MotC5N3.KbA K))
        ((algebraMap ℤ ↥(asL2 f₁ f₂)) z)
      = (algebraMap ℤ (Work.MotC5N3.KbA K)) z := by
  have h : ((algebraMap ↥(asL2 f₁ f₂) (Work.MotC5N3.KbA K)).comp
      (algebraMap ℤ ↥(asL2 f₁ f₂))) = algebraMap ℤ (Work.MotC5N3.KbA K) :=
    RingHom.ext_int _ _
  rw [← RingHom.comp_apply, h]

/-- `asIota` carries the basis `1,x,y,x²,xy` of the `L`-model to the basis of the `Kb`-model. -/
theorem asIota_kleinBas (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : K) (m : Fin 5) :
    asIota D f₁ f₂ (Work.MotV.kleinBas D ↥(asL2 f₁ f₂) m) =
      Work.MotV.kleinBas D (Work.MotC5N3.KbA K) m := by
  have hX := asIota_genX D f₁ f₂
  have hY := asIota_genY D f₁ f₂
  fin_cases m
  · change asIota D f₁ f₂ (1 : asML D f₁ f₂) = (1 : Work.MotC5N3.OmA K D)
    exact map_one _
  · exact hX
  · exact hY
  · change asIota D f₁ f₂ (Work.MotV.genX (D.E.baseChange ↥(asL2 f₁ f₂)) ^ 2)
      = Work.MotV.genX (D.E.baseChange (Work.MotC5N3.KbA K)) ^ 2
    rw [map_pow, hX]
  · change asIota D f₁ f₂ (Work.MotV.genX (D.E.baseChange ↥(asL2 f₁ f₂)) *
        Work.MotV.genY (D.E.baseChange ↥(asL2 f₁ f₂)))
      = Work.MotV.genX (D.E.baseChange (Work.MotC5N3.KbA K)) *
        Work.MotV.genY (D.E.baseChange (Work.MotC5N3.KbA K))
    rw [map_mul, hX, hY]

/-- `asIota` carries the Klein coordinates of the `L`-model to those of the `Kb`-model. -/
theorem asIota_kleinCoord (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : K) (i : Fin 5) :
    asIota D f₁ f₂ (Work.MotV.kleinCoord D ↥(asL2 f₁ f₂) i) =
      Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i := by
  rw [Work.MotV.kleinCoord_eq_sum, Work.MotV.kleinCoord_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, asIota_algebraMap, asIota_kleinBas]
  congr 1

/-- **The projective fifth-torsion shift preserves `Ω = kleinField ⊔ LImage`.** -/
theorem sigmaS_mem_Omega (D : Work.MotV.KleinData 𝕜) (hD : D.Good) (f₁ f₂ : K)
    (σS : Work.MotC5N3.OmA K D ≃ₐ[Work.MotC5N3.KbA K] Work.MotC5N3.OmA K D)
    (hσS : Work.MotC5N3.KleinData.ShiftOf D σS) :
    ∀ x ∈ (Work.MotC5N3.kleinField K D ⊔ LImage D (asL2 f₁ f₂)),
      σS x ∈ (Work.MotC5N3.kleinField K D ⊔ LImage D (asL2 f₁ f₂)) := by
  obtain ⟨lam, hlam0, hshift⟩ := hσS
  have hκ0 : Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0 ≠ 0 := hD.coord0_ne (Work.MotC5N3.KbA K)
  have hκ1 : Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 1 ≠ 0 := by
    intro h1
    have h := hshift 0
    rw [show (0 : Fin 5) + 1 = 1 from rfl, h1, mul_zero] at h
    exact hκ0 (σS.injective (by rw [h, map_zero]))
  let f : Work.MotC5N3.OmA K D →ₐ[K] Work.MotC5N3.OmA K D :=
    (σS.restrictScalars (K)).toAlgHom
  have hf : ∀ x, f x = σS x := fun x => rfl
  have hle : (Work.MotC5N3.kleinField K D ⊔ LImage D (asL2 f₁ f₂)) ≤
      (Work.MotC5N3.kleinField K D ⊔ LImage D (asL2 f₁ f₂)).comap f := by
    refine sup_le ?_ ?_
    · rw [Work.MotC5N3.kleinField]
      refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro z ⟨i, rfl⟩
      change f (Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i /
          Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0) ∈
        (Work.MotC5N3.kleinField K D ⊔ LImage D (asL2 f₁ f₂))
      have hgen : ∀ j : Fin 5, Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) j /
          Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0 ∈ Work.MotC5N3.kleinField K D := by
        intro j
        rw [Work.MotC5N3.kleinField]
        exact IntermediateField.subset_adjoin _ _ (Set.mem_range_self j)
      have h0 := hshift 0
      rw [show (0 : Fin 5) + 1 = 1 from rfl] at h0
      have key : f (Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i /
            Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0) =
          (Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) (i + 1) /
            Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0) *
          (Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 1 /
            Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0)⁻¹ := by
        rw [hf, map_div₀, hshift i, h0]
        field_simp
      rw [key]
      exact (le_sup_left : Work.MotC5N3.kleinField K D ≤
        Work.MotC5N3.kleinField K D ⊔ LImage D (asL2 f₁ f₂))
        (mul_mem (hgen (i + 1)) (inv_mem (hgen 1)))
    · intro z hz
      change f z ∈ (Work.MotC5N3.kleinField K D ⊔ LImage D (asL2 f₁ f₂))
      obtain ⟨c, hc, hcz⟩ := (mem_LImage_iff D (asL2 f₁ f₂) z).mp hz
      have hσz : f z = z := by
        rw [← hcz, hf, σS.commutes c]
      rw [hσz]
      exact (le_sup_right : LImage D (asL2 f₁ f₂) ≤
        Work.MotC5N3.kleinField K D ⊔ LImage D (asL2 f₁ f₂)) hz
  exact fun x hx => hle hx

/-- **`asRoot (f₁ - f₂)` lies in `L = K⟮asRoot f₁, asRoot f₂⟯`.** -/
theorem asRoot_sub_mem (f₁ f₂ : K) :
    Work.MotC5N3.asRoot (f₁ - f₂) ∈ asL2 f₁ f₂ := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set A : ↥(asL2 f₁ f₂) := ⟨Work.MotC5N3.asRoot f₁, asRoot_mem_asL2_left f₁ f₂⟩ with hAdef
  set B : ↥(asL2 f₁ f₂) := ⟨Work.MotC5N3.asRoot f₂, asRoot_mem_asL2_right f₁ f₂⟩ with hBdef
  have hA : A ^ 5 - A = algebraMap (K) ↥(asL2 f₁ f₂) f₁ := by
    apply Subtype.ext
    change (A : Work.MotC5N3.KbA K) ^ 5 - (A : Work.MotC5N3.KbA K) = _
    rw [hAdef, Work.MotC5N3.asRoot_spec]
    exact IsScalarTower.algebraMap_apply (K) ↥(asL2 f₁ f₂) (Work.MotC5N3.KbA K) f₁
  have hB : B ^ 5 - B = algebraMap (K) ↥(asL2 f₁ f₂) f₂ := by
    apply Subtype.ext
    change (B : Work.MotC5N3.KbA K) ^ 5 - (B : Work.MotC5N3.KbA K) = _
    rw [hBdef, Work.MotC5N3.asRoot_spec]
    exact IsScalarTower.algebraMap_apply (K) ↥(asL2 f₁ f₂) (Work.MotC5N3.KbA K) f₂
  have hΔ : (A - B) ^ 5 - (A - B) = algebraMap (K) ↥(asL2 f₁ f₂) (f₁ - f₂) := by
    have key : (A - B) ^ 5 - (A - B) = (A ^ 5 - A) - (B ^ 5 - B) := by
      rw [sub_pow_char]; ring
    rw [key, hA, hB, map_sub]
  have hβ : (algebraMap ↥(asL2 f₁ f₂) (Work.MotC5N3.KbA K) (A - B)) ^ 5
      - algebraMap ↥(asL2 f₁ f₂) (Work.MotC5N3.KbA K) (A - B)
      = algebraMap (K) (Work.MotC5N3.KbA K) (f₁ - f₂) := by
    rw [← map_pow, ← map_sub, hΔ,
      IsScalarTower.algebraMap_apply (K) ↥(asL2 f₁ f₂) (Work.MotC5N3.KbA K)]
  obtain ⟨m, hm⟩ := root_eq_asRoot_add (f₁ - f₂) hβ
  set y : ↥(asL2 f₁ f₂) := (A - B) - algebraMap ℤ ↥(asL2 f₁ f₂) ((m : Fin 5) : ℤ)
    with hydef
  have hyval : algebraMap ↥(asL2 f₁ f₂) (Work.MotC5N3.KbA K) y =
      Work.MotC5N3.asRoot (f₁ - f₂) := by
    rw [hydef, map_sub, asL2_intCast_comp f₁ f₂, hm]
    refl_ring1
  rw [← hyval]
  exact y.2

/-- **`asRoot (f₁ + f₂)` lies in `L = K⟮asRoot f₁, asRoot f₂⟯`.** -/
theorem asRoot_add_mem (f₁ f₂ : K) :
    Work.MotC5N3.asRoot (f₁ + f₂) ∈ asL2 f₁ f₂ := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set A : ↥(asL2 f₁ f₂) := ⟨Work.MotC5N3.asRoot f₁, asRoot_mem_asL2_left f₁ f₂⟩ with hAdef
  set B : ↥(asL2 f₁ f₂) := ⟨Work.MotC5N3.asRoot f₂, asRoot_mem_asL2_right f₁ f₂⟩ with hBdef
  have hA : A ^ 5 - A = algebraMap (K) ↥(asL2 f₁ f₂) f₁ := by
    apply Subtype.ext
    change (A : Work.MotC5N3.KbA K) ^ 5 - (A : Work.MotC5N3.KbA K) = _
    rw [hAdef, Work.MotC5N3.asRoot_spec]
    exact IsScalarTower.algebraMap_apply (K) ↥(asL2 f₁ f₂) (Work.MotC5N3.KbA K) f₁
  have hB : B ^ 5 - B = algebraMap (K) ↥(asL2 f₁ f₂) f₂ := by
    apply Subtype.ext
    change (B : Work.MotC5N3.KbA K) ^ 5 - (B : Work.MotC5N3.KbA K) = _
    rw [hBdef, Work.MotC5N3.asRoot_spec]
    exact IsScalarTower.algebraMap_apply (K) ↥(asL2 f₁ f₂) (Work.MotC5N3.KbA K) f₂
  have hΔ : (A + B) ^ 5 - (A + B) = algebraMap (K) ↥(asL2 f₁ f₂) (f₁ + f₂) := by
    have key : (A + B) ^ 5 - (A + B) = (A ^ 5 - A) + (B ^ 5 - B) := by
      rw [add_pow_char]; ring
    rw [key, hA, hB, map_add]
  have hβ : (algebraMap ↥(asL2 f₁ f₂) (Work.MotC5N3.KbA K) (A + B)) ^ 5
      - algebraMap ↥(asL2 f₁ f₂) (Work.MotC5N3.KbA K) (A + B)
      = algebraMap (K) (Work.MotC5N3.KbA K) (f₁ + f₂) := by
    rw [← map_pow, ← map_sub, hΔ,
      IsScalarTower.algebraMap_apply (K) ↥(asL2 f₁ f₂) (Work.MotC5N3.KbA K)]
  obtain ⟨m, hm⟩ := root_eq_asRoot_add (f₁ + f₂) hβ
  set y : ↥(asL2 f₁ f₂) := (A + B) - algebraMap ℤ ↥(asL2 f₁ f₂) ((m : Fin 5) : ℤ)
    with hydef
  have hyval : algebraMap ↥(asL2 f₁ f₂) (Work.MotC5N3.KbA K) y =
      Work.MotC5N3.asRoot (f₁ + f₂) := by
    rw [hydef, map_sub, asL2_intCast_comp f₁ f₂, hm]
    refl_ring1
  rw [← hyval]
  exact y.2

/-- **The Galois shift of `asRoot (f₁ - f₂)` is `χ₁ - χ₂`.** -/
theorem asShift_sub_eq (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : K)
    (A B C : ↥(asL2 f₁ f₂))
    (hA : A ^ 5 - A = algebraMap (K) ↥(asL2 f₁ f₂) f₁)
    (hB : B ^ 5 - B = algebraMap (K) ↥(asL2 f₁ f₂) f₂)
    (hC : C ^ 5 - C = algebraMap (K) ↥(asL2 f₁ f₂) (f₁ - f₂))
    (γ : ↥(asL2 f₁ f₂) ≃ₐ[K] ↥(asL2 f₁ f₂)) :
    algebraMap ℤ ↥(asL2 f₁ f₂) (((asShift D f₁ f₂ (f₁ - f₂) C hC γ : Fin 5) : ℤ))
      = algebraMap ℤ ↥(asL2 f₁ f₂) (((asShift D f₁ f₂ f₁ A hA γ : Fin 5) : ℤ))
        - algebraMap ℤ ↥(asL2 f₁ f₂) (((asShift D f₁ f₂ f₂ B hB γ : Fin 5) : ℤ)) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hAspec := asShift_spec D f₁ f₂ f₁ A hA γ
  have hBspec := asShift_spec D f₁ f₂ f₂ B hB γ
  have hCspec := asShift_spec D f₁ f₂ (f₁ - f₂) C hC γ
  have hΔ : (A - B) ^ 5 - (A - B) = algebraMap (K) ↥(asL2 f₁ f₂) (f₁ - f₂) := by
    have key : (A - B) ^ 5 - (A - B) = (A ^ 5 - A) - (B ^ 5 - B) := by
      rw [sub_pow_char]; ring
    rw [key, hA, hB, map_sub]
  have hzero : ((A - B) - C) ^ 5 - ((A - B) - C) = 0 := by
    have key : ((A - B) - C) ^ 5 - ((A - B) - C)
        = ((A - B) ^ 5 - (A - B)) - (C ^ 5 - C) := by
      rw [sub_pow_char]; ring
    rw [key, hΔ, hC, sub_self]
  obtain ⟨m, hm⟩ := exists_fin_five_of_pow_five_sub_eq_zero ((A - B) - C) hzero
  have hAB : A - B = C + ((m : Fin 5) : ↥(asL2 f₁ f₂)) := by
    rw [sub_eq_iff_eq_add] at hm
    rw [hm, add_comm]
  have hfixm : γ ((m : Fin 5) : ↥(asL2 f₁ f₂)) = ((m : Fin 5) : ↥(asL2 f₁ f₂)) :=
    map_natCast γ (m : ℕ)
  have h1 : γ (A - B) = (A - B) + (algebraMap ℤ ↥(asL2 f₁ f₂)
      (((asShift D f₁ f₂ f₁ A hA γ : Fin 5) : ℤ)) - algebraMap ℤ ↥(asL2 f₁ f₂)
      (((asShift D f₁ f₂ f₂ B hB γ : Fin 5) : ℤ))) := by
    rw [map_sub, hAspec, hBspec]
    refl_ring1
  have h2 : γ (A - B) = (A - B) + algebraMap ℤ ↥(asL2 f₁ f₂)
      (((asShift D f₁ f₂ (f₁ - f₂) C hC γ : Fin 5) : ℤ)) := by
    rw [hAB, map_add, hCspec, hfixm]
    refl_ring1
  exact (add_left_cancel (h1.symm.trans h2)).symm

/-- **The Galois shift of `asRoot (f₁ + f₂)` is `χ₁ + χ₂`.** -/
theorem asShift_add_eq (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : K)
    (A B C : ↥(asL2 f₁ f₂))
    (hA : A ^ 5 - A = algebraMap (K) ↥(asL2 f₁ f₂) f₁)
    (hB : B ^ 5 - B = algebraMap (K) ↥(asL2 f₁ f₂) f₂)
    (hC : C ^ 5 - C = algebraMap (K) ↥(asL2 f₁ f₂) (f₁ + f₂))
    (γ : ↥(asL2 f₁ f₂) ≃ₐ[K] ↥(asL2 f₁ f₂)) :
    algebraMap ℤ ↥(asL2 f₁ f₂) (((asShift D f₁ f₂ (f₁ + f₂) C hC γ : Fin 5) : ℤ))
      = algebraMap ℤ ↥(asL2 f₁ f₂) (((asShift D f₁ f₂ f₁ A hA γ : Fin 5) : ℤ))
        + algebraMap ℤ ↥(asL2 f₁ f₂) (((asShift D f₁ f₂ f₂ B hB γ : Fin 5) : ℤ)) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hAspec := asShift_spec D f₁ f₂ f₁ A hA γ
  have hBspec := asShift_spec D f₁ f₂ f₂ B hB γ
  have hCspec := asShift_spec D f₁ f₂ (f₁ + f₂) C hC γ
  have hΔ : (A + B) ^ 5 - (A + B) = algebraMap (K) ↥(asL2 f₁ f₂) (f₁ + f₂) := by
    have key : (A + B) ^ 5 - (A + B) = (A ^ 5 - A) + (B ^ 5 - B) := by
      rw [add_pow_char]; ring
    rw [key, hA, hB, map_add]
  have hzero : ((A + B) - C) ^ 5 - ((A + B) - C) = 0 := by
    have key : ((A + B) - C) ^ 5 - ((A + B) - C)
        = ((A + B) ^ 5 - (A + B)) - (C ^ 5 - C) := by
      rw [sub_pow_char]; ring
    rw [key, hΔ, hC, sub_self]
  obtain ⟨m, hm⟩ := exists_fin_five_of_pow_five_sub_eq_zero ((A + B) - C) hzero
  have hAB : A + B = C + ((m : Fin 5) : ↥(asL2 f₁ f₂)) := by
    rw [sub_eq_iff_eq_add] at hm
    rw [hm, add_comm]
  have hfixm : γ ((m : Fin 5) : ↥(asL2 f₁ f₂)) = ((m : Fin 5) : ↥(asL2 f₁ f₂)) :=
    map_natCast γ (m : ℕ)
  have h1 : γ (A + B) = (A + B) + (algebraMap ℤ ↥(asL2 f₁ f₂)
      (((asShift D f₁ f₂ f₁ A hA γ : Fin 5) : ℤ)) + algebraMap ℤ ↥(asL2 f₁ f₂)
      (((asShift D f₁ f₂ f₂ B hB γ : Fin 5) : ℤ))) := by
    rw [map_add, hAspec, hBspec]
    refl_ring1
  have h2 : γ (A + B) = (A + B) + algebraMap ℤ ↥(asL2 f₁ f₂)
      (((asShift D f₁ f₂ (f₁ + f₂) C hC γ : Fin 5) : ℤ)) := by
    rw [hAB, map_add, hCspec, hfixm]
    refl_ring1
  exact (add_left_cancel (h1.symm.trans h2)).symm


/-- **`σS ^ 5 = 1`.**  A projective fifth-torsion shift (`σS κᵢ = λ κ_{i+1}`) is an automorphism
whose fifth power is the identity: `σS ^ 5` fixes the Klein coordinates up to a common scalar, hence
fixes the Klein field, and the Klein field is `K(x, y)`, so `σS ^ 5 = 1`. -/
theorem sigmaS_pow_five_eq_one (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (σS : Work.MotC5N3.OmA K D ≃ₐ[Work.MotC5N3.KbA K] Work.MotC5N3.OmA K D)
    (hσS : Work.MotC5N3.KleinData.ShiftOf D σS) :
    σS ^ 5 = 1 := by
  haveI hEell : D.E.IsElliptic := hD.1.elliptic
  have hGood : Work.MotV.KleinData.Good D := hD.1
  have hpow : ∀ n : ℕ, ∀ x : Work.MotC5N3.OmA K D,
      ((σS.restrictScalars (K)) ^ n) x = (σS ^ n) x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
        intro x
        rw [pow_succ', AlgEquiv.mul_apply, ih, pow_succ', AlgEquiv.mul_apply,
          AlgEquiv.restrictScalars_apply]
  have hgenX : Work.MotV.genX (D.E.baseChange (Work.MotC5N3.KbA K)) ∈ Work.MotC5N3.kleinField K D := by
    rw [Work.MotC5N3.kleinField_eq_adjoin_genXY 𝕜 D hGood]
    exact IntermediateField.subset_adjoin _ _ (by simp)
  have hgenY : Work.MotV.genY (D.E.baseChange (Work.MotC5N3.KbA K)) ∈ Work.MotC5N3.kleinField K D := by
    rw [Work.MotC5N3.kleinField_eq_adjoin_genXY 𝕜 D hGood]
    exact IntermediateField.subset_adjoin _ _ (by simp)
  have hbridgeX : Work.MotV.genX (D.E.baseChange (Work.MotC5N3.KbA K)) =
      Work.MotC2.genX (D.E.baseChange (Work.MotC5N3.KbA K)) := by
    rw [Work.MotV.genX, Work.MotC2.genX, Work.MotC2.coordX_eq_mk]
  have hbridgeY : Work.MotV.genY (D.E.baseChange (Work.MotC5N3.KbA K)) =
      Work.MotC2.genY (D.E.baseChange (Work.MotC5N3.KbA K)) := by
    rw [Work.MotV.genY, Work.MotC2.genY, Work.MotC2.coordY_eq_mk]
  have hfixX : (σS ^ 5) (Work.MotC2.genX (D.E.baseChange (Work.MotC5N3.KbA K))) =
      Work.MotC2.genX (D.E.baseChange (Work.MotC5N3.KbA K)) := by
    rw [← hbridgeX]
    have h := Work.MotC5N3.GenAux_sigmaS_pow_five_kleinField 𝕜 D hGood σS hσS
      (Work.MotV.genX (D.E.baseChange (Work.MotC5N3.KbA K))) hgenX
    rwa [hpow 5 (Work.MotV.genX (D.E.baseChange (Work.MotC5N3.KbA K)))] at h
  have hfixY : (σS ^ 5) (Work.MotC2.genY (D.E.baseChange (Work.MotC5N3.KbA K))) =
      Work.MotC2.genY (D.E.baseChange (Work.MotC5N3.KbA K)) := by
    rw [← hbridgeY]
    have h := Work.MotC5N3.GenAux_sigmaS_pow_five_kleinField 𝕜 D hGood σS hσS
      (Work.MotV.genY (D.E.baseChange (Work.MotC5N3.KbA K))) hgenY
    rwa [hpow 5 (Work.MotV.genY (D.E.baseChange (Work.MotC5N3.KbA K)))] at h
  refine Work.MotC2.funcAlgEquiv_ext_genX_genY (D.E.baseChange (Work.MotC5N3.KbA K))
    (σS ^ 5) 1 ?_ ?_
  · simpa using hfixX
  · simpa using hfixY

/-- **The lift of the fifth-torsion shift `σS` to `M = L(E)`.**  A `K`-algebra automorphism
`σS'` of `M` with `asIota (σS' x) = σS (asIota x)` for all `x`, which acts trivially on the
constants `L`.  It exists because `σS` preserves `Ω = range asIota` (`hσSΩ`) and `σS ^ 5 = 1`, so
`σS` permutes `Ω`. -/
theorem asSigmaLift_ext (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (f₁ f₂ : K)
    (σS : Work.MotC5N3.OmA K D ≃ₐ[Work.MotC5N3.KbA K] Work.MotC5N3.OmA K D)
    (hRange : (asIota D f₁ f₂).fieldRange =
      Work.MotC5N3.kleinField K D ⊔ LImage D (asL2 f₁ f₂))
    (hσSΩ : ∀ x ∈ (Work.MotC5N3.kleinField K D ⊔ LImage D (asL2 f₁ f₂)),
      σS x ∈ (Work.MotC5N3.kleinField K D ⊔ LImage D (asL2 f₁ f₂)))
    (σS5 : σS ^ 5 = 1) :
    ∃ σS' : asML D f₁ f₂ ≃ₐ[↥(asL2 f₁ f₂)] asML D f₁ f₂,
      (∀ x : asML D f₁ f₂, asIota D f₁ f₂ (σS' x) = σS (asIota D f₁ f₂ x)) ∧
      (∀ l : ↥(asL2 f₁ f₂),
        σS' (algebraMap ↥(asL2 f₁ f₂) (asML D f₁ f₂) l) =
          algebraMap ↥(asL2 f₁ f₂) (asML D f₁ f₂) l) := by
  classical
  have hσSiter : ∀ n : ℕ, ∀ z ∈ (Work.MotC5N3.kleinField K D ⊔ LImage D (asL2 f₁ f₂)),
      (σS ^ n) z ∈ (Work.MotC5N3.kleinField K D ⊔ LImage D (asL2 f₁ f₂)) := by
    intro n
    induction n with
    | zero => intro z hz; simpa using hz
    | succ n ih =>
        intro z hz
        rw [pow_succ', AlgEquiv.mul_apply]
        exact hσSΩ _ (ih z hz)
  have hcrux : ∀ y ∈ (Work.MotC5N3.kleinField K D ⊔ LImage D (asL2 f₁ f₂)),
      ∃ z ∈ (Work.MotC5N3.kleinField K D ⊔ LImage D (asL2 f₁ f₂)), σS z = y := by
    intro y hy
    refine ⟨(σS ^ 4) y, hσSiter 4 y hy, ?_⟩
    have h1 : σS ((σS ^ 4) y) = (σS ^ 5) y := by
      conv_rhs => rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ', AlgEquiv.mul_apply]
    rw [h1, σS5, AlgEquiv.one_apply]
  have hex : ∀ x : asML D f₁ f₂, ∃ y : asML D f₁ f₂,
      asIota D f₁ f₂ y = σS (asIota D f₁ f₂ x) := by
    intro x
    have hσxΩ : σS (asIota D f₁ f₂ x) ∈ (Work.MotC5N3.kleinField K D ⊔
        LImage D (asL2 f₁ f₂)) :=
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
    have hmΩ : asIota D f₁ f₂ m ∈ (Work.MotC5N3.kleinField K D ⊔
        LImage D (asL2 f₁ f₂)) := by
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
  have hLψ : ∀ l : ↥(asL2 f₁ f₂),
      ψe (algebraMap ↥(asL2 f₁ f₂) (asML D f₁ f₂) l) =
        algebraMap ↥(asL2 f₁ f₂) (asML D f₁ f₂) l := by
    intro l
    apply asIota_injective D f₁ f₂
    calc asIota D f₁ f₂ (ψe (algebraMap ↥(asL2 f₁ f₂) (asML D f₁ f₂) l))
        = asIota D f₁ f₂ (ψ (algebraMap ↥(asL2 f₁ f₂) (asML D f₁ f₂) l)) := rfl
      _ = σS (asIota D f₁ f₂ (algebraMap ↥(asL2 f₁ f₂) (asML D f₁ f₂) l)) :=
            hψ (algebraMap ↥(asL2 f₁ f₂) (asML D f₁ f₂) l)
      _ = σS (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (l : Work.MotC5N3.KbA K)) := by
            rw [asIota_algebraMap D f₁ f₂ l]
      _ = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (l : Work.MotC5N3.KbA K) :=
            σS.commutes (l : Work.MotC5N3.KbA K)
      _ = asIota D f₁ f₂ (algebraMap ↥(asL2 f₁ f₂) (asML D f₁ f₂) l) := by
            rw [asIota_algebraMap D f₁ f₂ l]
  refine ⟨AlgEquiv.ofRingEquiv (f := ψe) hLψ, ?_, ?_⟩
  · intro x
    show asIota D f₁ f₂ (AlgEquiv.ofRingEquiv (f := ψe) hLψ x) = σS (asIota D f₁ f₂ x)
    rw [show AlgEquiv.ofRingEquiv (f := ψe) hLψ x = ψ x from rfl]
    exact hψ x
  · intro l
    exact (AlgEquiv.ofRingEquiv (f := ψe) hLψ).commutes l

end Work.MotC5N3.LamAS
