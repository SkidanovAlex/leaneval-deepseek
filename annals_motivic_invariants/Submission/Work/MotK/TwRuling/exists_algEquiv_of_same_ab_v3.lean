import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotK.TwRuling.KleinMuId
import Submission.Work.MotC2.PoleOrder
import Submission.Work.MotC2.TranslationDefs
import Submission.Work.MotTDG.Setup
import Submission.Work.MotTDG.TdiagAux
import Submission.Work.MotTDG.exists_algHom_of_point_between
import Submission.Work.MotTDG.exists_algHom_of_point
import Submission.Work.MotC.adjoin_genX_genY_eq_top
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TwRuling

open WeierstrassCurve WeierstrassCurve.Affine
open scoped IntermediateField

/-- The function field of `E` base changed to `K` (definitionally equal to `FunctionField E`). -/
abbrev FF {K : Type} [Field K] (D : Work.MotV.KleinData K) : Type :=
  FunctionField (D.E.baseChange K)

/-- `Work.MotV.genX` is `Work.MotC.C6.genX`. -/
theorem MotV_genX_eq_C6 {K : Type} [Field K] (E : WeierstrassCurve K) :
    Work.MotV.genX E = Work.MotC.C6.genX E := rfl

/-- `Work.MotV.genY` is `Work.MotC.C6.genY`. -/
theorem MotV_genY_eq_C6 {K : Type} [Field K] (E : WeierstrassCurve K) :
    Work.MotV.genY E = Work.MotC.C6.genY E := by
  rw [Work.MotV.genY, Work.MotC.C6.genY, AdjoinRoot.mk_X]

/-- `vwQuad` is homogeneous of degree `2`. -/
theorem vwQuad_smul {R : Type*} [CommRing R] (a₁ a₂ a₃ a₄ a₆ c : R) (v : Fin 5 → R) :
    Work.MotTDG.vwQuad a₁ a₂ a₃ a₄ a₆ (fun i => c * v i)
      = fun k => c ^ 2 * Work.MotTDG.vwQuad a₁ a₂ a₃ a₄ a₆ v k := by
  funext k
  fin_cases k <;>
    simp only [Work.MotTDG.vwQuad, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk] <;>
    first | refl_ring1 | ring

/-- If `vwQuad a v = 0` and `v 0 ≠ 0`, then `(v 1 / v 0, v 2 / v 0)` is a point of the curve. -/
theorem equation_of_vwQuad_eq_zero {R : Type*} [Field R] (W : WeierstrassCurve R) {v : Fin 5 → R}
    (hv0 : v 0 ≠ 0) (h : Work.MotTDG.vwQuad W.a₁ W.a₂ W.a₃ W.a₄ W.a₆ v = 0) :
    WeierstrassCurve.Affine.Equation W (v 1 / v 0) (v 2 / v 0) := by
  have hw0 : (fun i => (v 0)⁻¹ * v i) 0 = 1 := inv_mul_cancel₀ hv0
  have hwq : Work.MotTDG.vwQuad W.a₁ W.a₂ W.a₃ W.a₄ W.a₆ (fun i => (v 0)⁻¹ * v i) = 0 := by
    rw [vwQuad_smul]
    funext k
    rw [h]
    simp
  rw [WeierstrassCurve.Affine.equation_iff]
  simpa only [div_eq_inv_mul] using Work.MotTDG.relation_of_vwQuad_eq_zero hw0 hwq

/-- **Algebraicity is transitive along the Weierstrass equation**, two-curve form: if `(U, V)` lies
on a Weierstrass curve `E` over `K` pushed to an arbitrary field extension `F ⊇ K`, and `U` is
algebraic over `K`, then so is `V`.  (Generalisation of `Work.MotTDG.isAlgebraic_of_equation` to an
arbitrary ambient field.) -/
theorem isAlg_of_equation_between {K : Type} [Field K] (E : WeierstrassCurve K)
    {F : Type} [Field F] [Algebra K F] {U V : F}
    (h : WeierstrassCurve.Affine.Equation (E.map (algebraMap K F)) U V)
    (hU : IsAlgebraic K U) : IsAlgebraic K V := by
  have hUint : IsIntegral K U := isAlgebraic_iff_isIntegral.mp hU
  let K' : IntermediateField K F := K⟮U⟯
  have hUmem : U ∈ K' := IntermediateField.mem_adjoin_simple_self K U
  let b : K' := ⟨algebraMap K F E.a₁ * U + algebraMap K F E.a₃,
      K'.add_mem (K'.mul_mem (IntermediateField.algebraMap_mem K' E.a₁) hUmem)
        (IntermediateField.algebraMap_mem K' E.a₃)⟩
  let c : K' := ⟨-(U ^ 3 + algebraMap K F E.a₂ * U ^ 2 + algebraMap K F E.a₄ * U
        + algebraMap K F E.a₆),
      K'.neg_mem (K'.add_mem (K'.add_mem (K'.add_mem (K'.pow_mem hUmem 3)
        (K'.mul_mem (IntermediateField.algebraMap_mem K' E.a₂) (K'.pow_mem hUmem 2)))
        (K'.mul_mem (IntermediateField.algebraMap_mem K' E.a₄) hUmem))
        (IntermediateField.algebraMap_mem K' E.a₆))⟩
  have hmonic : (Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c :
      Polynomial K').Monic := by
    rw [show (Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c : Polynomial K')
        = Polynomial.X ^ 2 + (Polynomial.C b * Polynomial.X + Polynomial.C c) from by ring]
    refine Polynomial.monic_X_pow_add ?_
    calc (Polynomial.C b * Polynomial.X + Polynomial.C c : Polynomial K').degree
          ≤ max (Polynomial.C b * Polynomial.X).degree (Polynomial.C c).degree :=
            Polynomial.degree_add_le _ _
      _ ≤ max 1 0 := by
          refine max_le_max ?_ ?_
          · exact Polynomial.degree_C_mul_X_le b
          · exact Polynomial.degree_C_le
      _ < (2 : WithBot ℕ) := by norm_num
  have heval : Polynomial.eval₂ (algebraMap K' F) V
      (Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c) = 0 := by
    have key : Polynomial.eval₂ (algebraMap K' F) V
        (Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c)
        = V ^ 2 + (algebraMap K F E.a₁ * U + algebraMap K F E.a₃) * V
          + -(U ^ 3 + algebraMap K F E.a₂ * U ^ 2 + algebraMap K F E.a₄ * U
            + algebraMap K F E.a₆) := by
      simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
        Polynomial.eval₂_X, Polynomial.eval₂_C, IntermediateField.algebraMap_apply]
      simp only [b, c, zpow_ofNat]
    rw [key]
    have h' := h
    rw [WeierstrassCurve.Affine.equation_iff, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at h'
    linear_combination (norm := first | refl_ring1 | ring1) h'
  haveI : Module.Finite K K' := IntermediateField.adjoin.finiteDimensional hUint
  haveI : Algebra.IsAlgebraic K K' := Algebra.IsAlgebraic.of_finite K K'
  exact IsIntegral.trans_isAlgebraic K ⟨_, hmonic, heval⟩

theorem exists_algEquiv_of_same_ab_v3 (K : Type) [Field K] (D D' : Work.MotV.KleinData K)
    (ha : D.a = D'.a) (hb : D.b = D'.b) (hab : D'.a * D'.b ≠ 0)
    (hkl : ∀ (L : Type) [Field L] [Algebra K L] (k : Fin 5),
      Work.MotK.kleinP (algebraMap K _ D.a) (algebraMap K _ D.b)
        (Work.MotV.kleinCoord D L) k = 0)
    (hkl' : ∀ (L : Type) [Field L] [Algebra K L] (k : Fin 5),
      Work.MotK.kleinP (algebraMap K _ D'.a) (algebraMap K _ D'.b)
        (Work.MotV.kleinCoord D' L) k = 0)
    (h0 : ∀ (L : Type) [Field L] [Algebra K L], Work.MotV.kleinCoord D L 0 ≠ 0)
    (hsp : ∃ e : Fin 5 → Fin 5 → K, ∀ (L : Type) [Field L] [Algebra K L] (m : Fin 5),
      Work.MotV.kleinBas D L m =
        ∑ i, algebraMap L _ (algebraMap K L (e m i)) * Work.MotV.kleinCoord D L i)
    (hsp' : ∃ e : Fin 5 → Fin 5 → K, ∀ (L : Type) [Field L] [Algebra K L] (m : Fin 5),
      Work.MotV.kleinBas D' L m =
        ∑ i, algebraMap L _ (algebraMap K L (e m i)) * Work.MotV.kleinCoord D' L i) :
    Nonempty (WeierstrassCurve.Affine.FunctionField D'.E ≃ₐ[K]
      WeierstrassCurve.Affine.FunctionField D.E) := by
  have hsp'2 := hsp'
  obtain ⟨e', he'⟩ := hsp'2
  obtain ⟨e, he⟩ := hsp
  -- abbreviations
  let MF : Matrix (Fin 5) (Fin 5) (FF D) :=
    Work.MotTDG.matMul (Work.MotTDG.eL D' (FF D) e') (Work.MotTDG.cL D (FF D))
  have hMF : MF = Work.MotTDG.matMul (Work.MotTDG.eL D' (FF D) e')
      (Work.MotTDG.cL D (FF D)) := rfl
  let v : Fin 5 → FF D := fun m => ∑ j, MF m j * Work.MotTDG.basE (D.E.baseChange K) j
  have hv : v = fun m => ∑ j, MF m j * Work.MotTDG.basE (D.E.baseChange K) j := rfl
  -- the matrix identity `C' . M = C`
  have hCM : Work.MotTDG.matMul (Work.MotTDG.cL D' (FF D)) MF
      = Work.MotTDG.cL D (FF D) := by
    rw [hMF, ← Work.MotTDG.matMul_assoc,
      Work.MotTDG.cL_matMul_eL D' (FF D) e' (he' (FF D)), Work.MotTDG.one_matMul]
  -- `C' . v = kleinCoord D K`
  have hC'v : ∀ i : Fin 5, ∑ m, Work.MotTDG.cL D' (FF D) i m * v m
      = Work.MotV.kleinCoord D K i := by
    intro i
    have hMsum : ∀ j : Fin 5, (∑ m : Fin 5, Work.MotTDG.cL D' (FF D) i m * MF m j)
        = Work.MotTDG.cL D (FF D) i j := by
      intro j
      have hh := congrFun (congrFun hCM i) j
      simpa only [Work.MotTDG.matMul_apply] using hh
    calc ∑ m, Work.MotTDG.cL D' (FF D) i m * v m
        = ∑ m, Work.MotTDG.cL D' (FF D) i m
            * (∑ j, MF m j * Work.MotTDG.basE (D.E.baseChange K) j) := rfl
      _ = ∑ m, ∑ j, (Work.MotTDG.cL D' (FF D) i m * MF m j)
            * Work.MotTDG.basE (D.E.baseChange K) j := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          first | refl_ring1 | ring
      _ = ∑ j, ∑ m, (Work.MotTDG.cL D' (FF D) i m * MF m j)
            * Work.MotTDG.basE (D.E.baseChange K) j := Finset.sum_comm
      _ = ∑ j, (∑ m, Work.MotTDG.cL D' (FF D) i m * MF m j)
            * Work.MotTDG.basE (D.E.baseChange K) j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_mul]
      _ = ∑ j, Work.MotTDG.cL D (FF D) i j * Work.MotTDG.basE (D.E.baseChange K) j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hMsum j]
      _ = Work.MotV.kleinCoord D K i := by
          rw [Work.MotTDG.kleinCoord_eq_cL D K i]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [Work.MotTDG.cL, Algebra.algebraMap_self, RingHom.id_apply]
  -- `kleinP (C' v) = 0`
  have hvklein : ∀ k : Fin 5,
      Work.MotK.kleinP (algebraMap K (FF D) D'.a) (algebraMap K (FF D) D'.b)
        (fun i => ∑ m, Work.MotTDG.cL D' (FF D) i m * v m) k = 0 := by
    intro k
    have h := hkl K k
    rw [ha, hb] at h
    have heq : (fun i => ∑ m, Work.MotTDG.cL D' (FF D) i m * v m)
        = Work.MotV.kleinCoord D K := funext hC'v
    rw [heq]
    exact h
  -- the Veronese--Weierstrass quadrics of `D'` vanish at `v`
  have hvw : Work.MotTDG.vwQuad ((D'.E).baseChange (FF D)).a₁ ((D'.E).baseChange (FF D)).a₂
      ((D'.E).baseChange (FF D)).a₃ ((D'.E).baseChange (FF D)).a₄
      ((D'.E).baseChange (FF D)).a₆ v = 0 :=
    vwQuad_eq_zero_of_kleinP D D' hab hkl' hsp' (FF D) v hvklein
  -- components of `vwQuad v = 0`
  have hc0 : v 0 * v 3 - v 1 ^ 2 = 0 := by
    have hh := congrFun hvw 0
    simpa only [Work.MotTDG.vwQuad, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_succ, Matrix.cons_val, Pi.zero_apply] using hh
  have hc1 : v 0 * v 4 - v 1 * v 2 = 0 := by
    have hh := congrFun hvw 1
    simpa only [Work.MotTDG.vwQuad, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_succ, Matrix.cons_val, Pi.zero_apply] using hh
  have hc3 : v 2 ^ 2 + ((D'.E).baseChange (FF D)).a₁ * v 1 * v 2
      + ((D'.E).baseChange (FF D)).a₃ * v 0 * v 2 - v 1 * v 3
      - ((D'.E).baseChange (FF D)).a₂ * v 0 * v 3
      - ((D'.E).baseChange (FF D)).a₄ * v 0 * v 1
      - ((D'.E).baseChange (FF D)).a₆ * v 0 ^ 2 = 0 := by
    have hh := congrFun hvw 3
    simpa only [Work.MotTDG.vwQuad, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_succ, Matrix.cons_val, Pi.zero_apply] using hh
  have hc4 : v 2 * v 4 - v 3 ^ 2 - ((D'.E).baseChange (FF D)).a₂ * v 1 * v 3
      - ((D'.E).baseChange (FF D)).a₄ * v 0 * v 3 - ((D'.E).baseChange (FF D)).a₆ * v 0 * v 1
      + ((D'.E).baseChange (FF D)).a₁ * v 1 * v 4
      + ((D'.E).baseChange (FF D)).a₃ * v 0 * v 4 = 0 := by
    have hh := congrFun hvw 4
    simpa only [Work.MotTDG.vwQuad, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_succ, Matrix.cons_val, Pi.zero_apply] using hh
  -- step 2: `v 0 ≠ 0`
  have hv0 : v 0 ≠ 0 := by
    intro hv0z
    have hz1 : v 1 = 0 := by
      have hh := hc0
      rw [hv0z] at hh
      exact sq_eq_zero_iff.mp (by linear_combination -hh)
    have hz2 : v 2 = 0 := by
      have hh := hc3
      rw [hv0z, hz1] at hh
      exact sq_eq_zero_iff.mp (by linear_combination hh)
    have hz3 : v 3 = 0 := by
      have hh := hc4
      rw [hv0z, hz1, hz2] at hh
      exact sq_eq_zero_iff.mp (by linear_combination -hh)
    have hvn : ∀ m : Fin 5, m ≠ 4 → v m = 0 := by
      intro m hm
      fin_cases m
      · exact hv0z
      · exact hz1
      · exact hz2
      · exact hz3
      · exact absurd rfl hm
    have hκ4 : ∀ i : Fin 5, Work.MotV.kleinCoord D K i
        = Work.MotTDG.cL D' (FF D) i 4 * v 4 := by
      intro i
      rw [← hC'v i]
      have hif : ∀ m : Fin 5, Work.MotTDG.cL D' (FF D) i m * v m
          = if m = 4 then Work.MotTDG.cL D' (FF D) i 4 * v 4 else 0 := by
        intro m
        by_cases hm : m = 4
        · subst hm; simp
        · rw [hvn m hm, mul_zero]; simp [hm]
      calc ∑ m, Work.MotTDG.cL D' (FF D) i m * v m
          = ∑ m, (if m = 4 then Work.MotTDG.cL D' (FF D) i 4 * v 4 else 0) :=
            Finset.sum_congr rfl fun m _ => hif m
        _ = Work.MotTDG.cL D' (FF D) i 4 * v 4 := by simp
    -- `bas m = v 4 * S m` with `S m` algebraic
    have hSm : ∀ m : Fin 5, IsAlgebraic K
        (∑ i, algebraMap K (FF D) (e m i) * Work.MotTDG.cL D' (FF D) i 4) := by
      intro m
      refine Work.MotTDG.Tdiag_isAlgebraic_finset_sum
        (fun i => algebraMap K (FF D) (e m i) * Work.MotTDG.cL D' (FF D) i 4) Finset.univ ?_
      intro i _
      exact (isAlgebraic_algebraMap (e m i)).mul
        (isAlgebraic_algebraMap (D'.coord i 4))
    have hbas : ∀ m : Fin 5, Work.MotTDG.basE (D.E.baseChange K) m = v 4
        * (∑ i, algebraMap K (FF D) (e m i) * Work.MotTDG.cL D' (FF D) i 4) := by
      intro m
      have hh := he K m
      rw [show Work.MotV.kleinBas D K m = Work.MotTDG.basE (D.E.baseChange K) m from rfl] at hh
      rw [hh, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hκ4 i]
      simp only [Algebra.algebraMap_self, RingHom.id_apply]
      first | refl_ring1 | ring
    have hS0ne : (∑ i, algebraMap K (FF D) (e (0 : Fin 5) i)
        * Work.MotTDG.cL D' (FF D) i 4) ≠ 0 := by
      intro hz
      have h1 := hbas 0
      rw [Work.MotTDG.basE_zero, hz, mul_zero] at h1
      exact one_ne_zero h1
    have hv4alg : IsAlgebraic K (v 4) := by
      have h1 := hbas 0
      rw [Work.MotTDG.basE_zero] at h1
      have hmul : (∑ i, algebraMap K (FF D) (e (0 : Fin 5) i)
          * Work.MotTDG.cL D' (FF D) i 4) * v 4 = 1 := by
        rw [mul_comm]; exact h1.symm
      rw [← inv_eq_of_mul_eq_one_right hmul]
      exact (hSm 0).inv
    have hgenalg : IsAlgebraic K (Work.MotV.genX (D.E.baseChange K)) := by
      have h1 := hbas 1
      rw [Work.MotTDG.basE_one] at h1
      rw [h1]
      exact hv4alg.mul (hSm 1)
    rw [Work.MotTDG.genX_eq] at hgenalg
    exact (Work.MotC2.transcendental_genX (D.E.baseChange K)) hgenalg
  -- step 3: `v 3 = v 1^2/v0`, `v 4 = v 1 v 2 / v 0`
  have hv3eq : v 3 = v 1 ^ 2 / v 0 := by
    rw [eq_div_iff hv0]
    linear_combination (norm := first | refl_ring1 | ring1) hc0
  have hv4eq : v 4 = v 1 * v 2 / v 0 := by
    rw [eq_div_iff hv0]
    linear_combination (norm := first | refl_ring1 | ring1) hc1
  -- step 3b: `v = v 0 • w`
  let U : FF D := v 1 / v 0
  let V : FF D := v 2 / v 0
  let w : Fin 5 → FF D := ![1, U, V, U ^ 2, U * V]
  have hw0 : w 0 = 1 := rfl
  have hw1 : w 1 = U := rfl
  have hw2 : w 2 = V := rfl
  have hw3 : w 3 = U ^ 2 := rfl
  have hw4 : w 4 = U * V := rfl
  have hUdef : U = v 1 / v 0 := rfl
  have hVdef : V = v 2 / v 0 := rfl
  have hvw_eq : ∀ m : Fin 5, v m = v 0 * w m := by
    intro m
    fin_cases m
    · change v 0 = v 0 * w 0
      rw [hw0, mul_one]
    · change v 1 = v 0 * w 1
      rw [hw1, hUdef, mul_div_cancel₀ (v 1) hv0]
    · change v 2 = v 0 * w 2
      rw [hw2, hVdef, mul_div_cancel₀ (v 2) hv0]
    · change v 3 = v 0 * w 3
      rw [hw3, hUdef, hv3eq]
      field_simp <;> ring
    · change v 4 = v 0 * w 4
      rw [hw4, hUdef, hVdef, hv4eq]
      field_simp <;> ring
  -- step 3c: `kleinCoord D K i / v 0 = ∑ m cL D' F i m * w m`
  have hκw : ∀ i : Fin 5, Work.MotV.kleinCoord D K i / v 0
      = ∑ m, Work.MotTDG.cL D' (FF D) i m * w m := by
    intro i
    have hS : ∑ m, Work.MotTDG.cL D' (FF D) i m * v m
        = v 0 * ∑ m, Work.MotTDG.cL D' (FF D) i m * w m := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hvw_eq m]
      first | refl_ring1 | ring
    rw [div_eq_iff hv0, ← hC'v i, hS]
    first | refl_ring1 | ring
  -- step 3d: `bas m / v 0 = ∑ i e m i (kleinCoord i / v 0)`
  have hbaseq : ∀ m : Fin 5, Work.MotTDG.basE (D.E.baseChange K) m / v 0
      = ∑ i, algebraMap K (FF D) (e m i) * (Work.MotV.kleinCoord D K i / v 0) := by
    intro m
    have hh := he K m
    rw [show Work.MotV.kleinBas D K m = Work.MotTDG.basE (D.E.baseChange K) m from rfl] at hh
    rw [hh, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_div_assoc]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
  -- step 3e: `U` is transcendental
  have hU : Transcendental K U := by
    intro hUalg
    have hValg : IsAlgebraic K V := by
      have hV' : V = v 2 / v 0 := hVdef
      rw [hV']
      exact isAlg_of_equation_between (D'.E)
        (by
          rw [hUdef]
          exact equation_of_vwQuad_eq_zero ((D'.E).baseChange (FF D)) hv0 hvw)
        hUalg
    have hwalg : ∀ m : Fin 5, IsAlgebraic K (w m) := by
      intro m
      fin_cases m
      · change IsAlgebraic K (w 0)
        rw [hw0]; exact isAlgebraic_one
      · change IsAlgebraic K (w 1)
        rw [hw1, hUdef]; exact hUalg
      · change IsAlgebraic K (w 2)
        rw [hw2, hVdef]; exact hValg
      · change IsAlgebraic K (w 3)
        rw [hw3, hUdef]; exact hUalg.pow 2
      · change IsAlgebraic K (w 4)
        rw [hw4, hUdef, hVdef]; exact hUalg.mul hValg
    have hηalg : ∀ i : Fin 5, IsAlgebraic K (Work.MotV.kleinCoord D K i / v 0) := by
      intro i
      rw [hκw i]
      exact Work.MotTDG.Tdiag_isAlgebraic_finset_sum
        (fun m => Work.MotTDG.cL D' (FF D) i m * w m) Finset.univ
        (fun m _ => (isAlgebraic_algebraMap (D'.coord i m)).mul (hwalg m))
    have hη : ∀ m : Fin 5, IsAlgebraic K
        (∑ i, algebraMap K (FF D) (e m i) * (Work.MotV.kleinCoord D K i / v 0)) := by
      intro m
      exact Work.MotTDG.Tdiag_isAlgebraic_finset_sum
        (fun i => algebraMap K (FF D) (e m i) * (Work.MotV.kleinCoord D K i / v 0)) Finset.univ
        (fun i _ => (isAlgebraic_algebraMap (e m i)).mul (hηalg i))
    have h1alg : IsAlgebraic K ((1 : FF D) / v 0) := by
      have h := hη 0
      rw [← hbaseq 0, Work.MotTDG.basE_zero] at h
      exact h
    have hv0alg : IsAlgebraic K (v 0) := by
      have h := h1alg.inv
      rwa [one_div, inv_inv] at h
    have hgenalg : IsAlgebraic K (Work.MotV.genX (D.E.baseChange K)) := by
      have h1 := hη 1
      rw [← hbaseq 1] at h1
      have hb1 : Work.MotTDG.basE (D.E.baseChange K) 1
          = v 0 * (Work.MotTDG.basE (D.E.baseChange K) 1 / v 0) := by
        field_simp <;> ring
      rw [← Work.MotTDG.basE_one, hb1]
      exact hv0alg.mul h1
    rw [Work.MotTDG.genX_eq] at hgenalg
    exact (Work.MotC2.transcendental_genX (D.E.baseChange K)) hgenalg
  -- step 4: the map `Θ`
  have hUV : WeierstrassCurve.Affine.Equation
      ((D'.E).map (algebraMap K (FF D))) U V := by
    rw [hUdef, hVdef]
    exact equation_of_vwQuad_eq_zero ((D'.E).baseChange (FF D)) hv0 hvw
  obtain ⟨Θ, hΘx, hΘy⟩ :=
    Work.MotTDG.exists_algHom_of_point_between K (D'.E) (FF D) U V hUV hU
  -- `Θ` sends the `basE` of `D'` to `w`
  have hΘbas : ∀ m : Fin 5, Θ (Work.MotTDG.basE (D'.E) m) = w m := by
    intro m
    fin_cases m
    · change Θ (Work.MotTDG.basE (D'.E) 0) = w 0
      rw [Work.MotTDG.basE_zero, map_one, hw0]
    · change Θ (Work.MotTDG.basE (D'.E) 1) = w 1
      rw [Work.MotTDG.basE_one, hΘx, hw1]
    · change Θ (Work.MotTDG.basE (D'.E) 2) = w 2
      rw [Work.MotTDG.basE_two, hΘy, hw2]
    · change Θ (Work.MotTDG.basE (D'.E) 3) = w 3
      rw [Work.MotTDG.basE_three, map_pow, hΘx, hw3]
    · change Θ (Work.MotTDG.basE (D'.E) 4) = w 4
      rw [Work.MotTDG.basE_four, map_mul, hΘx, hΘy, hw4]
  -- the transferred Klein coordinates
  let κ' : Fin 5 → WeierstrassCurve.Affine.FunctionField D'.E :=
    fun i => ∑ m, algebraMap K (WeierstrassCurve.Affine.FunctionField D'.E) (D'.coord i m)
      * Work.MotTDG.basE (D'.E) m
  have hκ'def : ∀ i : Fin 5, κ' i
      = ∑ m, algebraMap K (WeierstrassCurve.Affine.FunctionField D'.E) (D'.coord i m)
        * Work.MotTDG.basE (D'.E) m := fun i => rfl
  have hΘκ' : ∀ i : Fin 5, Θ (κ' i) = Work.MotV.kleinCoord D K i / v 0 := by
    intro i
    have h1 : Θ (κ' i) = ∑ m, algebraMap K (FF D) (D'.coord i m) * w m := by
      rw [hκ'def i, map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_mul, AlgHom.commutes, hΘbas m]
    rw [h1]
    exact (hκw i).symm
  -- `genX` and `genY` of `D.E` lie in the image
  have hdiv : ∀ m : Fin 5, Work.MotTDG.basE (D.E.baseChange K) m / v 0 ∈ Θ.fieldRange := by
    intro m
    rw [AlgHom.mem_fieldRange]
    refine ⟨∑ i, algebraMap K (WeierstrassCurve.Affine.FunctionField D'.E) (e m i) * κ' i, ?_⟩
    rw [map_sum]
    have hsum : (∑ i, Θ (algebraMap K (WeierstrassCurve.Affine.FunctionField D'.E) (e m i)
          * κ' i))
        = ∑ i, algebraMap K (FF D) (e m i) * (Work.MotV.kleinCoord D K i / v 0) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, AlgHom.commutes, hΘκ' i]
    rw [hsum, ← hbaseq m]
  have h0div : (1 : FF D) / v 0 ∈ Θ.fieldRange := by
    have h := hdiv 0
    rwa [Work.MotTDG.basE_zero] at h
  have hv0mem : v 0 ∈ Θ.fieldRange := by
    rw [AlgHom.mem_fieldRange] at h0div ⊢
    obtain ⟨s, hs⟩ := h0div
    refine ⟨s⁻¹, ?_⟩
    rw [map_inv₀, hs, one_div, inv_inv]
  have hmem : ∀ m : Fin 5, Work.MotTDG.basE (D.E.baseChange K) m ∈ Θ.fieldRange := by
    intro m
    rw [show Work.MotTDG.basE (D.E.baseChange K) m
        = v 0 * (Work.MotTDG.basE (D.E.baseChange K) m / v 0) from by
          rw [mul_div_cancel₀ (Work.MotTDG.basE (D.E.baseChange K) m) hv0]]
    exact Θ.fieldRange.mul_mem hv0mem (hdiv m)
  have hrange : Θ.fieldRange = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← Work.MotC.adjoin_genX_genY_eq_top (D.E.baseChange K),
      IntermediateField.adjoin_le_iff]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · subst hx
      have h := hmem 1
      rw [Work.MotTDG.basE_one] at h
      rwa [MotV_genX_eq_C6 (D.E.baseChange K)] at h
    · subst hx
      have h := hmem 2
      rw [Work.MotTDG.basE_two] at h
      rwa [MotV_genY_eq_C6 (D.E.baseChange K)] at h
  have hsurj : Function.Surjective Θ := (AlgHom.fieldRange_eq_top).mp hrange
  have hinj : Function.Injective Θ := by
    intro a b hab
    by_contra hne
    have h1 : a - b ≠ 0 := sub_ne_zero.mpr hne
    have h2 : Θ (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have h3 : (1 : FF D) = 0 := by
      have := congrArg Θ (mul_inv_cancel₀ h1)
      rw [map_mul, map_one, h2, zero_mul] at this
      exact this.symm
    exact one_ne_zero h3
  exact ⟨AlgEquiv.ofBijective Θ ⟨hinj, hsurj⟩⟩

end Work.MotK.TwRuling
