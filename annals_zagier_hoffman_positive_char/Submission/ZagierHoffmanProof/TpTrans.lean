import Submission.ZagierHoffmanProof.TpAux
import Submission.ZagierHoffmanProof.AmbZeta

/-!
# The (LD)/(LW) transports of Dac's Theorem 6.2 for the `ambH`-datum

* `lseries_relationP` (Step 1): a `K`-linear relation between MZV's of tuples with `q ∤ s_i`
  transports, via the bridge (4.2) for the Anderson–Thakur datum, to a vanishing relation between
  the corresponding `L`-series values (with the `Γ`-scaled coefficients of Dac §6.2).
* `linearIndependent_of_bridgeP` (Step 2, (LW)): `K`-independence of the MZV's implies
  `K`-independence of the `L`-series values.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
open Polynomial PowerSeries Finset
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## §1. `ambGammaF` lies in `ambK` and does not vanish -/

lemma ambGammaF_mem_ambK (n : ℕ) : ambGammaF F n ∈ ambK F := by
  rcases le_or_gt n (Nat.card F) with h | h
  · rw [ambGammaF_of_le F h]; exact Subfield.one_mem _
  · rw [ambGammaF_of_gt F h]
    exact (ambK F).sub_mem ((ambK F).pow_mem (ambTheta_mem_ambK F) _) (ambTheta_mem_ambK F)

lemma ambTheta_pow_ne_ambTheta : (ambTheta F) ^ Nat.card F ≠ ambTheta F := by
  intro h
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  have h1 : Valued.v ((ambTheta F) ^ Nat.card F) = Valued.v (ambTheta F) := by rw [h]
  rw [Valuation.map_pow, v_ambTheta, ← WithZero.exp_nsmul] at h1
  have h2 : (Nat.card F : ℚ) * ((Nat.card F : ℚ) - 1) = ((Nat.card F : ℚ) - 1) := by
    simpa [nsmul_eq_mul] using WithZero.exp_injective h1
  have h3 : ((Nat.card F : ℚ) - 1) * ((Nat.card F : ℚ) - 1) = 0 := by nlinarith [h2]
  have h4 : ((Nat.card F : ℚ) - 1) = 0 := mul_self_eq_zero.mp h3
  have hc2 : (2 : ℚ) ≤ Nat.card F := by exact_mod_cast hq2
  linarith [h4, hc2]

lemma ambGammaF_ne_zero (n : ℕ) : ambGammaF F n ≠ 0 := by
  rcases le_or_gt n (Nat.card F) with h | h
  · rw [ambGammaF_of_le F h]; exact one_ne_zero
  · rw [ambGammaF_of_gt F h]
    exact sub_ne_zero.mpr (ambTheta_pow_ne_ambTheta F)

lemma eval_map_ambCoeff_poly (p : Polynomial F) :
    (Polynomial.eval (ambTheta F) (p.map (ambCoeff F)))
      = ambKHomAmb F (algebraMap (Polynomial F) (RatFunc F) p) := by
  rw [Polynomial.eval_map, ambKHomAmb_eq, ambKEquiv_apply, ambKHom_algebraMap, ambKPolyHom_apply]
  rfl

/-! ## §2. Step 1 (LD): the `L`-series relation -/

theorem lseries_relationP {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝔰 : ι → Σ r : ℕ, Fin r → ℕ+)
    (hpos : ∀ i, 0 < (𝔰 i).1)
    (hsup : ∀ i j, ((𝔰 i).2 j : ℕ) ≤ 2 * Nat.card F - 2)
    (w : ℕ) (hwt : ∀ i, ∑ j : Fin (𝔰 i).1, ((𝔰 i).2 j : ℕ) = w)
    (a : ι → Polynomial F)
    (h : ∑ i, ((a i : RatFunc F)) • ζ_A F ((𝔰 i).2) = 0) :
    ∑ i, (((a i).map (ambCoeff F))
        * ∏ i' ∈ Finset.univ.erase i, gammaPolyTup F ((𝔰 i').2)).eval (ambTheta F)
      * evalSeriesGen (tmL (Nat.card F) (ambOmega F) (tupleListHP F ((𝔰 i).2)))
          (ambTheta F) = 0 := by
  classical
  -- the Ambient form of the assumed relation
  have hrel : (∑ i, ((a i).map (ambCoeff F)).eval (ambTheta F)
      * ambInfHom F (ζ_A F ((𝔰 i).2))) = 0 := by
    have h1 := ambInfHom_zeta_A_relation (F := F) (fun i => (𝔰 i).1) hpos
      (fun i => (𝔰 i).2) (fun i => ((a i : RatFunc F))) h
    have h2 : ∀ i, ((ambKEquiv F ((a i : RatFunc F)) : ↥(ambK F)) : Ambient F)
        = ((a i).map (ambCoeff F)).eval (ambTheta F) := by
      intro i
      have h3 : ((a i : RatFunc F)) = algebraMap (Polynomial F) (RatFunc F) (a i) := rfl
      rw [h3, ← ambKHomAmb_apply, ← eval_map_ambCoeff_poly F (a i)]
    rw [← h1]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h2 i]
  -- the bridge identity per index
  have hbr : ∀ i, (ambPiTilde F) ^ w
      * evalSeriesGen (tmL (Nat.card F) (ambOmega F) (tupleListHP F ((𝔰 i).2))) (ambTheta F)
      = (∏ j : Fin (𝔰 i).1, ambGammaF F (((𝔰 i).2 j : ℕ)))
        * ambInfHom F (ζ_A F ((𝔰 i).2)) := by
    intro i
    have h1 := bridgeP_tuple F ((𝔰 i).2) (hpos i) (hsup i)
    rwa [hwt i] at h1
  -- the `Γ`-scaled coefficients
  have hΓ : ∀ i, (∏ j : Fin (𝔰 i).1, ambGammaF F (((𝔰 i).2 j : ℕ)))
      = (gammaPolyTup F ((𝔰 i).2)).eval (ambTheta F) :=
    fun i => (eval_gammaPolyTup F ((𝔰 i).2)).symm
  have hcf : ∀ i, (((a i).map (ambCoeff F))
        * ∏ i' ∈ Finset.univ.erase i, gammaPolyTup F ((𝔰 i').2)).eval (ambTheta F)
      * (∏ j : Fin (𝔰 i).1, ambGammaF F (((𝔰 i).2 j : ℕ)))
      = ((a i).map (ambCoeff F)).eval (ambTheta F)
        * ∏ i', (gammaPolyTup F ((𝔰 i').2)).eval (ambTheta F) := by
    intro i
    rw [Polynomial.eval_mul, Polynomial.eval_prod, hΓ i,
      show (((a i).map (ambCoeff F)).eval (ambTheta F)
          * (∏ i' ∈ Finset.univ.erase i, (gammaPolyTup F ((𝔰 i').2)).eval (ambTheta F))
          * (gammaPolyTup F ((𝔰 i).2)).eval (ambTheta F))
        = ((a i).map (ambCoeff F)).eval (ambTheta F)
          * ((∏ i' ∈ Finset.univ.erase i, (gammaPolyTup F ((𝔰 i').2)).eval (ambTheta F))
            * (gammaPolyTup F ((𝔰 i).2)).eval (ambTheta F)) from by ring,
      Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  have hmain : (ambPiTilde F) ^ w
      * (∑ i, (((a i).map (ambCoeff F))
          * ∏ i' ∈ Finset.univ.erase i, gammaPolyTup F ((𝔰 i').2)).eval (ambTheta F)
        * evalSeriesGen (tmL (Nat.card F) (ambOmega F) (tupleListHP F ((𝔰 i).2)))
            (ambTheta F)) = 0 := by
    have hstep : ∀ i, (ambPiTilde F) ^ w
        * ((((a i).map (ambCoeff F))
            * ∏ i' ∈ Finset.univ.erase i, gammaPolyTup F ((𝔰 i').2)).eval (ambTheta F)
          * evalSeriesGen (tmL (Nat.card F) (ambOmega F) (tupleListHP F ((𝔰 i).2)))
              (ambTheta F))
        = ((a i).map (ambCoeff F)).eval (ambTheta F)
          * (∏ i', (gammaPolyTup F ((𝔰 i').2)).eval (ambTheta F))
          * ambInfHom F (ζ_A F ((𝔰 i).2)) := by
      intro i
      rw [show (ambPiTilde F) ^ w
            * ((((a i).map (ambCoeff F))
                * ∏ i' ∈ Finset.univ.erase i, gammaPolyTup F ((𝔰 i').2)).eval (ambTheta F)
              * evalSeriesGen (tmL (Nat.card F) (ambOmega F) (tupleListHP F ((𝔰 i).2)))
                  (ambTheta F))
          = ((((a i).map (ambCoeff F))
                * ∏ i' ∈ Finset.univ.erase i, gammaPolyTup F ((𝔰 i').2)).eval (ambTheta F))
            * ((ambPiTilde F) ^ w
              * evalSeriesGen (tmL (Nat.card F) (ambOmega F) (tupleListHP F ((𝔰 i).2)))
                  (ambTheta F)) from by ring,
        hbr i, ← mul_assoc, hcf i]
    rw [Finset.mul_sum, Finset.sum_congr rfl (fun i _ => hstep i)]
    have hsum2 : (∑ i, ((a i).map (ambCoeff F)).eval (ambTheta F)
          * (∏ i', (gammaPolyTup F ((𝔰 i').2)).eval (ambTheta F))
          * ambInfHom F (ζ_A F ((𝔰 i).2)))
        = (∏ i', (gammaPolyTup F ((𝔰 i').2)).eval (ambTheta F))
          * ∑ i, ((a i).map (ambCoeff F)).eval (ambTheta F) * ambInfHom F (ζ_A F ((𝔰 i).2)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [hsum2, hrel, mul_zero]
  refine mul_eq_zero.mp hmain |>.resolve_left ?_
  exact pow_ne_zero _ (ambPiTilde_ne_zero F)

/-! ## §3. Step 2 (LW): independence of the `L`-series values -/

theorem linearIndependent_of_bridgeP {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝔰 : ι → Σ r : ℕ, Fin r → ℕ+)
    (hpos : ∀ i, 0 < (𝔰 i).1)
    (hsup : ∀ i j, ((𝔰 i).2 j : ℕ) ≤ 2 * Nat.card F - 2)
    (w : ℕ) (hwt : ∀ i, ∑ j : Fin (𝔰 i).1, ((𝔰 i).2 j : ℕ) = w)
    (h : LinearIndependent (RatFunc F) (fun i => ζ_A F ((𝔰 i).2))) :
    LinearIndependent (ambK F)
      (fun i => evalSeriesGen (tmL (Nat.card F) (ambOmega F) (tupleListHP F ((𝔰 i).2)))
        (ambTheta F)) := by
  classical
  have hΓmem : ∀ i, (∏ j : Fin (𝔰 i).1, ambGammaF F (((𝔰 i).2 j : ℕ))) ∈ ambK F :=
    fun i => (ambK F).prod_mem (fun j _ => ambGammaF_mem_ambK F _)
  have hbr : ∀ i, (ambPiTilde F) ^ w
      * evalSeriesGen (tmL (Nat.card F) (ambOmega F) (tupleListHP F ((𝔰 i).2)))
          (ambTheta F)
      = (∏ j : Fin (𝔰 i).1, ambGammaF F (((𝔰 i).2 j : ℕ)))
        * ambInfHom F (ζ_A F ((𝔰 i).2)) := by
    intro i
    have h1 := bridgeP_tuple F ((𝔰 i).2) (hpos i) (hsup i)
    rwa [hwt i] at h1
  rw [Fintype.linearIndependent_iffₛ] at h ⊢
  intro f g hfg i
  -- the Ambient relation
  have hab : (∑ i, ((f i : Ambient F) - (g i : Ambient F))
      * (∏ j : Fin (𝔰 i).1, ambGammaF F (((𝔰 i).2 j : ℕ)))
      * ambInfHom F (ζ_A F ((𝔰 i).2))) = 0 := by
    have h1 : (∑ i, ((f i : Ambient F) - (g i : Ambient F))
        * evalSeriesGen (tmL (Nat.card F) (ambOmega F) (tupleListHP F ((𝔰 i).2)))
            (ambTheta F)) = 0 := by
      have e1 : (∑ i, f i • evalSeriesGen (tmL (Nat.card F) (ambOmega F)
              (tupleListHP F ((𝔰 i).2))) (ambTheta F))
          = ∑ i, (f i : Ambient F) * evalSeriesGen (tmL (Nat.card F) (ambOmega F)
              (tupleListHP F ((𝔰 i).2))) (ambTheta F) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Algebra.smul_def]
        rfl
      have e2 : (∑ i, g i • evalSeriesGen (tmL (Nat.card F) (ambOmega F)
              (tupleListHP F ((𝔰 i).2))) (ambTheta F))
          = ∑ i, (g i : Ambient F) * evalSeriesGen (tmL (Nat.card F) (ambOmega F)
              (tupleListHP F ((𝔰 i).2))) (ambTheta F) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Algebra.smul_def]
        rfl
      rw [e1, e2] at hfg
      have h2 : (∑ i, ((f i : Ambient F) - (g i : Ambient F))
            * evalSeriesGen (tmL (Nat.card F) (ambOmega F) (tupleListHP F ((𝔰 i).2)))
                (ambTheta F))
          = (∑ i, (f i : Ambient F) * evalSeriesGen (tmL (Nat.card F) (ambOmega F)
                (tupleListHP F ((𝔰 i).2))) (ambTheta F))
            - ∑ i, (g i : Ambient F) * evalSeriesGen (tmL (Nat.card F) (ambOmega F)
                (tupleListHP F ((𝔰 i).2))) (ambTheta F) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
      rw [h2, hfg, sub_self]
    have h3 : (∑ i, ((f i : Ambient F) - (g i : Ambient F))
        * (∏ j : Fin (𝔰 i).1, ambGammaF F (((𝔰 i).2 j : ℕ)))
        * ambInfHom F (ζ_A F ((𝔰 i).2)))
      = (ambPiTilde F) ^ w * (∑ i, ((f i : Ambient F) - (g i : Ambient F))
        * evalSeriesGen (tmL (Nat.card F) (ambOmega F) (tupleListHP F ((𝔰 i).2)))
            (ambTheta F)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [show (ambPiTilde F) ^ w * (((f i : Ambient F) - (g i : Ambient F))
          * evalSeriesGen (tmL (Nat.card F) (ambOmega F) (tupleListHP F ((𝔰 i).2)))
              (ambTheta F))
        = ((f i : Ambient F) - (g i : Ambient F))
          * ((ambPiTilde F) ^ w
            * evalSeriesGen (tmL (Nat.card F) (ambOmega F) (tupleListHP F ((𝔰 i).2)))
                (ambTheta F)) from by ring, hbr i]
      ring
    rw [h3, h1, mul_zero]
  -- the corresponding `RatFunc`-relation
  have hmem : ∀ i, ((f i : Ambient F) - (g i : Ambient F))
      * (∏ j : Fin (𝔰 i).1, ambGammaF F (((𝔰 i).2 j : ℕ))) ∈ ambK F :=
    fun i => (ambK F).mul_mem ((ambK F).sub_mem (f i).2 (g i).2) (hΓmem i)
  let c : ι → RatFunc F := fun i => (ambKEquiv F).symm
    (⟨((f i : Ambient F) - (g i : Ambient F))
      * (∏ j : Fin (𝔰 i).1, ambGammaF F (((𝔰 i).2 j : ℕ))), hmem i⟩ : ↥(ambK F))
  have hci_eq : ∀ i, ambInfHom F (c i • ζ_A F ((𝔰 i).2))
      = ((f i : Ambient F) - (g i : Ambient F))
        * (∏ j : Fin (𝔰 i).1, ambGammaF F (((𝔰 i).2 j : ℕ)))
        * ambInfHom F (ζ_A F ((𝔰 i).2)) := by
    intro i
    rw [Algebra.smul_def, map_mul]
    congr 1
    have hcoe : (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)) (c i)
        = ((c i : RatFunc F) : RatFunc.CompletionAtInfty F) := rfl
    rw [hcoe, ambInfHom_coe, ambKHomAmb_apply]
    dsimp only [c]
    rw [RingEquiv.apply_symm_apply]
  have hzeta : (∑ i, c i • ζ_A F ((𝔰 i).2)) = 0 := by
    apply ambInfHom_injective
    rw [map_zero, map_sum]
    exact (Finset.sum_congr rfl (fun i _ => hci_eq i)).trans hab
  have hzero : (∑ i, (0 : RatFunc F) • ζ_A F ((𝔰 i).2)) = 0 := by simp
  have hc0 := h _ _ (hzeta.trans hzero.symm) i
  have h1 : (⟨((f i : Ambient F) - (g i : Ambient F))
      * (∏ j : Fin (𝔰 i).1, ambGammaF F (((𝔰 i).2 j : ℕ))), hmem i⟩ : ↥(ambK F)) = 0 := by
    have h2 := congrArg (ambKEquiv F) hc0
    dsimp only [c] at h2
    simpa using h2
  have hΓne : (⟨∏ j : Fin (𝔰 i).1, ambGammaF F (((𝔰 i).2 j : ℕ)), hΓmem i⟩
      : ↥(ambK F)) ≠ 0 := by
    intro hh
    have h2 : (∏ j : Fin (𝔰 i).1, ambGammaF F (((𝔰 i).2 j : ℕ))) = 0 :=
      congrArg Subtype.val hh
    exact Finset.prod_ne_zero_iff.mpr (fun j _ => ambGammaF_ne_zero F _) h2
  have h3 : (⟨(f i : Ambient F) - (g i : Ambient F),
      (ambK F).sub_mem (f i).2 (g i).2⟩ : ↥(ambK F)) = 0 := by
    have h4 : (⟨((f i : Ambient F) - (g i : Ambient F))
          * (∏ j : Fin (𝔰 i).1, ambGammaF F (((𝔰 i).2 j : ℕ))), hmem i⟩ : ↥(ambK F))
        = (⟨(f i : Ambient F) - (g i : Ambient F),
            (ambK F).sub_mem (f i).2 (g i).2⟩ : ↥(ambK F))
          * (⟨∏ j : Fin (𝔰 i).1, ambGammaF F (((𝔰 i).2 j : ℕ)), hΓmem i⟩ : ↥(ambK F)) :=
      Subtype.ext rfl
    rw [h4] at h1
    exact (mul_eq_zero.mp h1).resolve_right hΓne
  exact Subtype.ext (sub_eq_zero.mp (congrArg Subtype.val h3))

end ZagierHoffmanPositiveChar
