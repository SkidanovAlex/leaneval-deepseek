import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.PSDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
Product trial states of N identical one-particle bumps, and the a priori upper
bound on their Rayleigh quotient.

Given a one-particle function `φ : ℝ³ → ℝ` with the interface properties
(ContDiff ∞, support inside the cube `cube L`, sup bound `sp`, `L²`-norm 1),
this module produces an admissible `N`-particle trial state `Ψ` (a product of
`N` copies of `φ` on the `N` coordinates) whose Rayleigh quotient is bounded by

    boxQuot N L v Ψ ≤ (N : ℝ) · ∫ |φ · Δφ| + (N : ℝ)² · sp · ∫ |v| .

The single target lemma is `productState_facts` below; do not change its
statement.  Helper lemmas may be added freely.
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory Laplacian
open scoped ContDiff Topology Real
open MeasureTheory

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)


/-! ## Measure-theoretic helpers for the cross-term bound -/

/-- `|v|` is integrable for `v ∈ L¹`. -/
lemma ps_v_abs_integrable {v : ℝ³ → ℝ} (hv1 : MemLp v 1) : Integrable (fun x : ℝ³ => |v x|) := by
  have hvInt : Integrable v := (memLp_one_iff_integrable.mp hv1)
  have hnorm : Integrable (fun x : ℝ³ => ‖v x‖) := hvInt.norm
  simpa using hnorm

/-- `|v|` is in `L¹` for `v ∈ L¹`. -/
lemma ps_v_abs_memLp {v : ℝ³ → ℝ} (hv1 : MemLp v 1) : MemLp (fun x : ℝ³ => |v x|) 1 := by
  exact (memLp_one_iff_integrable.mpr (ps_v_abs_integrable hv1))

/-- The involution `y ↦ c − y` as a measurable equivalence of `ℝ³`. -/
noncomputable def psNegTransEquiv (c : ℝ³) : ℝ³ ≃ᵐ ℝ³ where
  toEquiv :=
    { toFun := fun y => c - y
      invFun := fun y => c - y
      left_inv := by intro y; exact sub_sub_cancel c y
      right_inv := by intro y; exact sub_sub_cancel c y }
  measurable_toFun := by
    have hc : Continuous (fun y : ℝ³ => c - y) := continuous_const.sub continuous_id
    exact hc.measurable
  measurable_invFun := by
    have hc : Continuous (fun y : ℝ³ => c - y) := continuous_const.sub continuous_id
    exact hc.measurable

/-- The map `y ↦ c − y` preserves volume. -/
lemma ps_negTrans_measurePreserving (c : ℝ³) : MeasurePreserving (psNegTransEquiv c) := by
  have hneg : (volume : Measure ℝ³).map (fun y : ℝ³ => -y) = volume :=
    (Measure.measurePreserving_neg (volume : Measure ℝ³)).map_eq
  have hadd : (volume : Measure ℝ³).map (fun z : ℝ³ => c + z) = volume :=
    (measurePreserving_add_left (μ := (volume : Measure ℝ³)) c).map_eq
  refine ⟨(psNegTransEquiv c).measurable, ?_⟩
  have hcomp : (fun y : ℝ³ => c - y) = (fun z : ℝ³ => c + z) ∘ (fun y : ℝ³ => -y) := by
    funext y
    simp [sub_eq_add_neg]
  calc
    (volume : Measure ℝ³).map (⇑(psNegTransEquiv c))
        = (volume : Measure ℝ³).map (fun y : ℝ³ => c - y) := by
          simpa [psNegTransEquiv]
    _ = (volume : Measure ℝ³).map ((fun z : ℝ³ => c + z) ∘ (fun y : ℝ³ => -y)) := by rw [hcomp]
    _ = ((volume : Measure ℝ³).map (fun y : ℝ³ => -y)).map (fun z : ℝ³ => c + z) := by
          rw [← Measure.map_map (g := fun z : ℝ³ => c + z) (f := fun y : ℝ³ => -y)]
          · fun_prop
          · fun_prop
    _ = volume := by rw [hneg, hadd]

/-- Change of variables `y ↦ c − y`. -/
lemma ps_integral_negTrans (c : ℝ³) {f : ℝ³ → ℝ} :
    (∫ y : ℝ³, f (c - y)) = ∫ x : ℝ³, f x := by
  have hmp := ps_negTrans_measurePreserving c
  have h := hmp.integral_comp (psNegTransEquiv c).measurableEmbedding f
  simpa [psNegTransEquiv] using h

/-- The whole-space integral of `|v (c − ·)|` equals `∫|v|`. -/
lemma ps_integral_abs_negTrans {v : ℝ³ → ℝ} (c : ℝ³) :
    (∫ y : ℝ³, |v (c - y)|) = ∫ x : ℝ³, |v x| := by
  simpa using (ps_integral_negTrans c (f := fun x : ℝ³ => |v x|))

/-- For an `L¹` potential, the `|v (c − ·)|` integral over the cube is at most `∫|v|`. -/
lemma ps_cube_integral_abs_sub_le {L : ℝ} {v : ℝ³ → ℝ} (hv1 : MemLp v 1) (c : ℝ³) :
    (∫ y in cube L, |v (c - y)|) ≤ (∫ x : ℝ³, |v x|) := by
  have hInt : Integrable (fun y : ℝ³ => |v (c - y)|) volume := by
    have hmp := ps_negTrans_measurePreserving c
    have hb := hmp.integrable_comp_emb (psNegTransEquiv c).measurableEmbedding
      (g := fun x : ℝ³ => |v x|)
    exact hb.mpr (ps_v_abs_integrable hv1)
  calc
    (∫ y in cube L, |v (c - y)|) ≤ ∫ y : ℝ³, |v (c - y)| := by
          exact setIntegral_le_integral hInt (by filter_upwards with y; exact abs_nonneg _)
    _ = ∫ x : ℝ³, |v x| := by
          simpa using (ps_integral_negTrans c (f := fun x : ℝ³ => |v x|))

/-- The one-particle box integral of `|v (c − w 0)|` is at most `∫|v|`. -/
lemma ps_box1_abs_v_le {L : ℝ} {v : ℝ³ → ℝ} (hv1 : MemLp v 1) (c : ℝ³) :
    (∫ w in box 1 L, |v (c - w 0)|) ≤ ∫ x : ℝ³, |v x| := by
  calc
    (∫ w in box 1 L, |v (c - w 0)|) = ∫ y in cube L, |v (c - y)| :=
      integral_box1 (L := L) (f := fun y => |v (c - y)|)
    _ ≤ ∫ x : ℝ³, |v x| := ps_cube_integral_abs_sub_le hv1 c

/-- `crossSum n 1 v u w` has a single summation index. -/
lemma ps_crossSum_one {n : ℕ} (v : ℝ³ → ℝ) (u : X n) (w : X 1) :
    crossSum n 1 v u w = ∑ i : Fin n, v (u i - w 0) := by
  unfold crossSum
  apply Finset.sum_congr rfl
  intro i hi
  have hin : (∑ j : Fin 1, v (u i - w j)) = v (u i - w 0) := by
    rw [Fin.sum_univ_one]
  exact hin

/-- `|v (c − w 0)|` is integrable over the one-particle box. -/
lemma ps_box1_vsub_integrable {L : ℝ} {v : ℝ³ → ℝ} (hv1 : MemLp v 1) (c : ℝ³) :
    IntegrableOn (fun w : X 1 => |v (c - w 0)|) (box 1 L) volume := by
  -- cube version: |v (c − y)| integrable over the cube, from whole-space integrability
  have hwhole : Integrable (fun y : ℝ³ => |v (c - y)|) volume := by
    have hmp := ps_negTrans_measurePreserving c
    have hb := hmp.integrable_comp_emb (psNegTransEquiv c).measurableEmbedding
      (g := fun x : ℝ³ => |v x|)
    exact hb.mpr (ps_v_abs_integrable hv1)
  have hcube : IntegrableOn (fun y : ℝ³ => |v (c - y)|) (cube L) volume := by
    exact hwhole.mono_measure Measure.restrict_le_self
  -- transport along the one-particle evaluation
  have hmp2 : MeasurePreserving oneEval (volume.restrict (box 1 L)) (volume.restrict (cube L)) := by
    simpa [box1_preimage] using (oneEval_measurePreserving.restrict_preimage_emb
      oneEval.measurableEmbedding (cube L))
  have hb2 := hmp2.integrable_comp_emb oneEval.measurableEmbedding
    (g := fun y : ℝ³ => |v (c - y)|)
  -- hb2 : Integrable (fun w => |v (c − oneEval w)|) (box1) ↔ Integrable |v(c−·)| (cube)
  exact hb2.mpr hcube

/-- Fubini for a two-block box integral: `∫ over box (n+1) of G(first,last)` is the
iterated integral over the two boxes. -/
lemma ps_box_iter {n : ℕ} {L : ℝ} (G : X n → X 1 → ℝ)
    (hGint : IntegrableOn (fun x : X (n+1) => G (firstBlock n 1 x) (lastBlock n 1 x))
      (box (n+1) L) volume) :
    (∫ x in box (n+1) L, G (firstBlock n 1 x) (lastBlock n 1 x)) =
      ∫ u in box n L, (∫ w in box 1 L, G u w) := by
  have hmp : MeasurePreserving (blockSplitEquiv n 1)
      (volume.restrict (box (n+1) L))
      ((volume.restrict (box n L)).prod (volume.restrict (box 1 L))) :=
    blockSplit_measurePreserving_restrict n 1 L
  have hpt : (fun x : X (n+1) => G (firstBlock n 1 x) (lastBlock n 1 x)) =
      (fun p : X n × X 1 => G p.1 p.2) ∘ (blockSplitEquiv n 1) := by
    funext x
    simp [blockSplitEquiv_apply]
  have hcomp : Integrable (fun p : X n × X 1 => G p.1 p.2)
      ((volume.restrict (box n L)).prod (volume.restrict (box 1 L))) := by
    have hb := hmp.integrable_comp_emb (blockSplitEquiv n 1).measurableEmbedding
      (g := fun p : X n × X 1 => G p.1 p.2)
    refine hb.mp ?_
    rw [← hpt]
    exact hGint.integrable
  calc
    (∫ x in box (n+1) L, G (firstBlock n 1 x) (lastBlock n 1 x))
        = ∫ x : X (n+1), (fun p : X n × X 1 => G p.1 p.2)
            (blockSplitEquiv n 1 x) ∂(volume.restrict (box (n+1) L)) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [blockSplitEquiv_apply]
    _ = ∫ p : X n × X 1, G p.1 p.2
          ∂((volume.restrict (box n L)).prod (volume.restrict (box 1 L))) := by
          exact hmp.integral_comp (blockSplitEquiv n 1).measurableEmbedding
            (fun p : X n × X 1 => G p.1 p.2)
    _ = ∫ u : X n, (∫ w : X 1, G u w
          ∂(volume.restrict (box 1 L)))
          ∂(volume.restrict (box n L)) := by
          exact MeasureTheory.integral_prod (f := fun p : X n × X 1 => G p.1 p.2) hcomp
    _ = ∫ u in box n L, (∫ w in box 1 L, G u w) := by rfl

/-- For each `i`, the cross pair with the added particle is bounded by `sp·∫|v|·den`. -/
lemma ps_Ji_abs_box_le {n : ℕ} {L : ℝ} {v : ℝ³ → ℝ} {φ : ℝ³ → ℝ} {sp : ℝ}
    (hL : 0 < L) (hv1 : MemLp v 1) (hsp0 : 0 ≤ sp) (hφc : ContDiff ℝ ∞ φ)
    (hφts : tsupport φ ⊆ interior (cube L)) (hφsq : ∀ x : ℝ³, (φ x)^2 ≤ sp)
    (hφnorm : (∫ x : ℝ³, (φ x)^2) = 1) (Φn : CInfty0Box n L) (i : Fin n) :
    (∫ x in box (n+1) L,
        ((psProdState Φn (oneState (φ := φ) hφc hφts hφnorm) : X (n+1) → ℝ) x)^2 *
          |v ((firstBlock n 1 x) i - (lastBlock n 1 x) 0)|)
      ≤ sp * (∫ x : ℝ³, |v x|) * psDen n L Φn := by
  let Φ1 : CInfty0Box 1 L := oneState (φ := φ) hφc hφts hφnorm
  let f1 : X n → ℝ := (Φn : X n → ℝ)
  let f2 : X 1 → ℝ := (Φ1 : X 1 → ℝ)
  let Ψ : CInfty0Box (n+1) L := psProdState Φn Φ1
  let P : X (n+1) → ℝ := prodState n 1 f1 f2
  let B : ℝ := ∫ x : ℝ³, |v x|
  have hP : (Ψ : X (n+1) → ℝ) = P := by
    dsimp [Ψ, Φ1, P, f1, f2]
    rw [psProdState_coe]
  have hf2sq : ∀ w : X 1, (f2 w)^2 ≤ sp := by
    intro w
    dsimp [f2, Φ1]
    exact oneState_sq_le hφc hφts hφnorm hφsq w
  have hf1int : IntegrableOn (fun u : X n => (f1 u)^2) (box n L) volume := by
    have hc : Continuous (fun u : X n => (f1 u)^2) := (psi_contDiff Φn).continuous.pow 2
    exact ContinuousOn.integrableOn_compact (box_compact hL) hc.continuousOn
  -- the whole product-state integrand is integrable over the big box
  have hFint : IntegrableOn (fun x : X (n+1) =>
      (P x)^2 * |v ((firstBlock n 1 x) i - (lastBlock n 1 x) 0)|) (box (n+1) L) volume := by
    let i' : Fin (n+1) := Fin.castAdd 1 i
    let j' : Fin (n+1) := Fin.natAdd n (0 : Fin 1)
    have hne : i' ≠ j' := by
      intro h
      have hv1' : (i' : ℕ) < n := by simpa [i'] using i.isLt
      have hv2 : n ≤ (j' : ℕ) := by dsimp [j']; exact Nat.le_add_right n 0
      rw [h] at hv1'
      exact (not_lt_of_ge hv2) hv1'
    have hb := integrableOn_Ψ2_v (N := n+1) (L := L) hL (ps_v_abs_memLp hv1) Ψ hne
    have hidx1 : ∀ x : X (n+1), (firstBlock n 1 x) i = x i' := by
      intro x; dsimp [i']; rfl
    have hidx2 : ∀ x : X (n+1), (lastBlock n 1 x) 0 = x j' := by
      intro x; dsimp [j']; rfl
    have heq : (fun x : X (n+1) =>
        (P x)^2 * |v ((firstBlock n 1 x) i - (lastBlock n 1 x) 0)|) =
        (fun x : X (n+1) => ((Ψ : X (n+1) → ℝ) x)^2 * |v (x i' - x j')|) := by
      funext x
      rw [hidx1 x, hidx2 x]
      rw [hP]
    simpa [heq] using hb
  -- Fubini over the two blocks
  have hFub : (∫ x in box (n+1) L,
      (P x)^2 * |v ((firstBlock n 1 x) i - (lastBlock n 1 x) 0)|) =
      ∫ u in box n L, (f1 u)^2 * (∫ w in box 1 L, (f2 w)^2 * |v (u i - w 0)|) := by
    let G : X n → X 1 → ℝ := fun u w => (f1 u)^2 * (f2 w)^2 * |v (u i - w 0)|
    have hGint : IntegrableOn (fun x : X (n+1) =>
        G (firstBlock n 1 x) (lastBlock n 1 x)) (box (n+1) L) volume := by
      have hg : (fun x : X (n+1) =>
          G (firstBlock n 1 x) (lastBlock n 1 x)) =
          (fun x : X (n+1) =>
            (P x)^2 * |v ((firstBlock n 1 x) i - (lastBlock n 1 x) 0)|) := by
        funext x
        change (f1 (firstBlock n 1 x))^2 * (f2 (lastBlock n 1 x))^2 *
            |v ((firstBlock n 1 x) i - (lastBlock n 1 x) 0)| =
          (prodState n 1 f1 f2 x)^2 *
            |v ((firstBlock n 1 x) i - (lastBlock n 1 x) 0)|
        dsimp [prodState]
        ring
      rw [hg]
      exact hFint
    have hf := ps_box_iter (n := n) (L := L) G hGint
    calc
      (∫ x in box (n+1) L,
          (P x)^2 * |v ((firstBlock n 1 x) i - (lastBlock n 1 x) 0)|)
          = ∫ x in box (n+1) L, G (firstBlock n 1 x) (lastBlock n 1 x) := by
            apply integral_congr_ae
            filter_upwards with x
            change (P x)^2 * |v ((firstBlock n 1 x) i - (lastBlock n 1 x) 0)| =
              (f1 (firstBlock n 1 x))^2 * (f2 (lastBlock n 1 x))^2 *
                |v ((firstBlock n 1 x) i - (lastBlock n 1 x) 0)|
            dsimp [P]
            dsimp [prodState]
            ring
      _ = ∫ u in box n L, (∫ w in box 1 L, G u w) := hf
      _ = ∫ u in box n L, (f1 u)^2 * (∫ w in box 1 L, (f2 w)^2 * |v (u i - w 0)|) := by
            apply integral_congr_ae
            filter_upwards with u
            have hp : (∫ w in box 1 L, G u w) =
                (f1 u)^2 * (∫ w in box 1 L, (f2 w)^2 * |v (u i - w 0)|) := by
              calc
                (∫ w in box 1 L, G u w)
                    = ∫ w in box 1 L, (f1 u)^2 * ((f2 w)^2 * |v (u i - w 0)|) := by
                      apply integral_congr_ae
                      filter_upwards with w
                      dsimp [G]
                      ring
                _ = (f1 u)^2 * (∫ w in box 1 L, (f2 w)^2 * |v (u i - w 0)|) := by
                      simpa using (integral_const_mul ((f1 u)^2)
                        (fun w : X 1 => (f2 w)^2 * |v (u i - w 0)|))
            rw [hp]
  -- inner bound
  have hinner : ∀ u : X n, (∫ w in box 1 L, (f2 w)^2 * |v (u i - w 0)|) ≤ sp * B := by
    intro u
    have hgint : IntegrableOn (fun w : X 1 => sp * |v (u i - w 0)|) (box 1 L) volume := by
      exact (ps_box1_vsub_integrable (L := L) hv1 (u i)).const_mul sp
    have hmono := integral_mono_of_nonneg (μ := volume.restrict (box 1 L))
      (f := fun w => (f2 w)^2 * |v (u i - w 0)|)
      (g := fun w => sp * |v (u i - w 0)|)
      (by filter_upwards with w; exact mul_nonneg (sq_nonneg (f2 w)) (abs_nonneg _))
      hgint
      (by filter_upwards with w; exact mul_le_mul_of_nonneg_right (hf2sq w) (abs_nonneg _))
    calc
      (∫ w in box 1 L, (f2 w)^2 * |v (u i - w 0)|)
          ≤ ∫ w in box 1 L, sp * |v (u i - w 0)| := by simpa using hmono
      _ = sp * (∫ w in box 1 L, |v (u i - w 0)|) := by rw [integral_const_mul]
      _ ≤ sp * B := mul_le_mul_of_nonneg_left (ps_box1_abs_v_le (L := L) hv1 (u i)) hsp0
  -- assemble
  have hle1 : (∫ x in box (n+1) L,
      (P x)^2 * |v ((firstBlock n 1 x) i - (lastBlock n 1 x) 0)|)
      ≤ ∫ u in box n L, (f1 u)^2 * (sp * B) := by
    rw [hFub]
    have hf0 : 0 ≤ᵐ[volume.restrict (box n L)]
        (fun u : X n => (f1 u)^2 * (∫ w in box 1 L, (f2 w)^2 * |v (u i - w 0)|)) := by
      filter_upwards with u
      exact mul_nonneg (sq_nonneg (f1 u)) (integral_nonneg (fun w =>
        mul_nonneg (sq_nonneg (f2 w)) (abs_nonneg (v (u i - w 0)))))
    have hg' : IntegrableOn (fun u : X n => sp * B * (f1 u)^2) (box n L) volume := by
      exact hf1int.const_mul (sp * B)
    have hg : IntegrableOn (fun u : X n => (f1 u)^2 * (sp * B)) (box n L) volume := by
      have heq : (fun u : X n => sp * B * (f1 u)^2) = (fun u : X n => (f1 u)^2 * (sp * B)) := by
        funext u
        ring
      rw [heq] at hg'
      exact hg'
    have hle : ∀ᵐ u ∂(volume.restrict (box n L)),
        (f1 u)^2 * (∫ w in box 1 L, (f2 w)^2 * |v (u i - w 0)|) ≤ (f1 u)^2 * (sp * B) := by
      filter_upwards with u
      exact mul_le_mul_of_nonneg_left (hinner u) (sq_nonneg (f1 u))
    simpa using (integral_mono_of_nonneg (μ := volume.restrict (box n L)) hf0 hg hle)
  calc
    (∫ x in box (n+1) L,
        ((psProdState Φn (oneState (φ := φ) hφc hφts hφnorm) : X (n+1) → ℝ) x)^2 *
          |v ((firstBlock n 1 x) i - (lastBlock n 1 x) 0)|)
        = ∫ x in box (n+1) L,
            (P x)^2 * |v ((firstBlock n 1 x) i - (lastBlock n 1 x) 0)| := by
          apply integral_congr_ae
          filter_upwards with x
          dsimp [Ψ, Φ1, P, f1, f2]
          rw [psProdState_coe]
    _ ≤ ∫ u in box n L, (f1 u)^2 * (sp * B) := hle1
    _ = (sp * B) * (∫ u in box n L, (f1 u)^2) := by
          rw [integral_mul_const (sp * B) (fun u : X n => (f1 u)^2)]
          ring
    _ = sp * B * psDen n L Φn := by
          have hD1 : (∫ u in box n L, (f1 u)^2) = psDen n L Φn := rfl
          rw [hD1]
    _ = sp * (∫ x : ℝ³, |v x|) * psDen n L Φn := by
          simp only [B]

/-- The cross interaction of `Φₙ` with one added particle is bounded. -/
lemma psCross_add_one_abs_le {n : ℕ} {L : ℝ} {v : ℝ³ → ℝ} {φ : ℝ³ → ℝ} {sp : ℝ}
    (hL : 0 < L) (hv1 : MemLp v 1) (hsp0 : 0 ≤ sp) (hφc : ContDiff ℝ ∞ φ)
    (hφts : tsupport φ ⊆ interior (cube L)) (hφsq : ∀ x : ℝ³, (φ x)^2 ≤ sp)
    (hφnorm : (∫ x : ℝ³, (φ x)^2) = 1) (Φn : CInfty0Box n L) :
    |psCross (L := L) v (psProdState Φn (oneState (φ := φ) hφc hφts hφnorm))| ≤
      (n : ℝ) * sp * (∫ x : ℝ³, |v x|) * psDen n L Φn := by
  let Φ1 : CInfty0Box 1 L := oneState (φ := φ) hφc hφts hφnorm
  let Ψ : CInfty0Box (n+1) L := psProdState Φn Φ1
  let f1 : X n → ℝ := (Φn : X n → ℝ)
  let f2 : X 1 → ℝ := (Φ1 : X 1 → ℝ)
  let P : X (n+1) → ℝ := prodState n 1 f1 f2
  let B : ℝ := ∫ x : ℝ³, |v x|
  have hP : (Ψ : X (n+1) → ℝ) = P := by
    simp [Ψ, Φ1, P, f1, f2, psProdState_coe]
  -- the cross integrand collapses to a single sum
  have hinteg : psCross (L := L) v Ψ =
      ∑ i : Fin n, ∫ x in box (n+1) L,
        (P x)^2 * v ((firstBlock n 1 x) i - (lastBlock n 1 x) 0) := by
    calc
      psCross (L := L) v Ψ
          = ∫ x in box (n+1) L, (P x)^2 *
              crossSum n 1 v (firstBlock n 1 x) (lastBlock n 1 x) := by
            unfold psCross
            rw [hP]
      _ = ∫ x in box (n+1) L, (P x)^2 *
            (∑ i : Fin n, v ((firstBlock n 1 x) i - (lastBlock n 1 x) 0)) := by
            apply integral_congr_ae
            filter_upwards with x
            rw [ps_crossSum_one]
      _ = ∫ x in box (n+1) L,
            ∑ i : Fin n, (P x)^2 * v ((firstBlock n 1 x) i - (lastBlock n 1 x) 0) := by
            apply integral_congr_ae
            filter_upwards with x
            rw [Finset.mul_sum]
      _ = ∑ i : Fin n, ∫ x in box (n+1) L,
            (P x)^2 * v ((firstBlock n 1 x) i - (lastBlock n 1 x) 0) := by
            -- finite-sum interchange
            have hf (i : Fin n) : IntegrableOn (fun x : X (n+1) =>
                (P x)^2 * v ((firstBlock n 1 x) i - (lastBlock n 1 x) 0)) (box (n+1) L) volume := by
              -- transport of coordinate indices
              have hne : Fin.castAdd 1 i ≠ Fin.natAdd n (0 : Fin 1) := by
                intro h
                have hv1' : (Fin.castAdd 1 i).val < n := by
                  simpa using i.isLt
                have hv2 : n ≤ (Fin.natAdd n (0 : Fin 1)).val := by
                  dsimp [Fin.natAdd]
                  exact Nat.le_add_right n 0
                rw [h] at hv1'
                exact (not_lt_of_ge hv2) hv1'
              have hb := integrableOn_Ψ2_v (N := n+1) (L := L) hL hv1 Ψ hne
              have heq : (fun x : X (n+1) =>
                  (P x)^2 * v ((firstBlock n 1 x) i - (lastBlock n 1 x) 0)) =
                  (fun x : X (n+1) =>
                    ((Ψ : X (n+1) → ℝ) x)^2 *
                      v (x (Fin.castAdd 1 i) - x (Fin.natAdd n 0))) := by
                funext x
                simp [P, f1, f2, prodState, firstBlock, lastBlock, hP, pow_two]
              simpa [heq] using hb
            -- use the integral_finsetSum
            rw [integral_finsetSum (s := Finset.univ)
              (f := fun i x => (P x)^2 * v ((firstBlock n 1 x) i - (lastBlock n 1 x) 0))
              (fun i hi => (hf i).integrable)]
  have hC : |psCross (L := L) v Ψ| ≤ ∑ i : Fin n,
      ∫ x in box (n+1) L, (P x)^2 * |v ((firstBlock n 1 x) i - (lastBlock n 1 x) 0)| := by
    calc
      |psCross (L := L) v Ψ|
          = |∑ i : Fin n, ∫ x in box (n+1) L,
              (P x)^2 * v ((firstBlock n 1 x) i - (lastBlock n 1 x) 0)| := by rw [hinteg]
      _ ≤ ∑ i : Fin n, |∫ x in box (n+1) L,
              (P x)^2 * v ((firstBlock n 1 x) i - (lastBlock n 1 x) 0)| := by
            exact Finset.abs_sum_le_sum_abs (fun i : Fin n =>
              ∫ x in box (n+1) L, (P x)^2 * v ((firstBlock n 1 x) i - (lastBlock n 1 x) 0))
              Finset.univ
      _ ≤ ∑ i : Fin n, ∫ x in box (n+1) L,
            (P x)^2 * |v ((firstBlock n 1 x) i - (lastBlock n 1 x) 0)| := by
            apply Finset.sum_le_sum
            intro i hi
            have h_abs : |∫ x in box (n+1) L,
                  (P x)^2 * v ((firstBlock n 1 x) i - (lastBlock n 1 x) 0)| ≤
                ∫ x in box (n+1) L,
                  |(P x)^2 * v ((firstBlock n 1 x) i - (lastBlock n 1 x) 0)| := by
              change |∫ x : X (n+1),
                  (P x)^2 * v ((firstBlock n 1 x) i - (lastBlock n 1 x) 0)
                    ∂(volume.restrict (box (n+1) L))| ≤
                ∫ x : X (n+1),
                  |(P x)^2 * v ((firstBlock n 1 x) i - (lastBlock n 1 x) 0)|
                    ∂(volume.restrict (box (n+1) L))
              exact abs_integral_le_integral_abs (μ := volume.restrict (box (n+1) L))
                (f := fun x : X (n+1) =>
                  (P x)^2 * v ((firstBlock n 1 x) i - (lastBlock n 1 x) 0))
            have h_abs_eq : (∫ x in box (n+1) L,
                  |(P x)^2 * v ((firstBlock n 1 x) i - (lastBlock n 1 x) 0)|) =
                ∫ x in box (n+1) L,
                  (P x)^2 * |v ((firstBlock n 1 x) i - (lastBlock n 1 x) 0)| := by
              apply integral_congr_ae
              filter_upwards with x
              rw [abs_mul, abs_of_nonneg (sq_nonneg (P x))]
            exact h_abs.trans_eq h_abs_eq
  have hJi (i : Fin n) : (∫ x in box (n+1) L,
      (P x)^2 * |v ((firstBlock n 1 x) i - (lastBlock n 1 x) 0)|) ≤ sp * B * psDen n L Φn := by
    -- unfold P = coe Ψ
    have hb := ps_Ji_abs_box_le (n := n) (L := L) (v := v) (φ := φ) (sp := sp)
      hL hv1 hsp0 hφc hφts hφsq hφnorm Φn i
    simpa [B, P, f1, f2, Ψ, Φ1, hP] using hb
  calc
    |psCross (L := L) v (psProdState Φn (oneState (φ := φ) hφc hφts hφnorm))|
        ≤ ∑ i : Fin n, ∫ x in box (n+1) L,
            (P x)^2 * |v ((firstBlock n 1 x) i - (lastBlock n 1 x) 0)| := by
          simpa [Ψ, Φ1] using hC
    _ ≤ ∑ i : Fin n, sp * B * psDen n L Φn := by
          exact Finset.sum_le_sum (fun i hi => hJi i)
    _ = (n : ℝ) * sp * B * psDen n L Φn := by
          simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
          ring
    _ = (n : ℝ) * sp * (∫ x : ℝ³, |v x|) * psDen n L Φn := by
          simp only [B]

/-- Adding one particle to a state increases the Rayleigh quotient by at most
the one-particle kinetic `∫|φΔφ|` plus `n` cross terms of size `sp·∫|v|`. -/
lemma boxQuot_add_one {n : ℕ} {L : ℝ} {v : ℝ³ → ℝ} {φ : ℝ³ → ℝ} {sp : ℝ}
    (hL : 0 < L) (hv1 : MemLp v 1) (hsp0 : 0 ≤ sp) (hφc : ContDiff ℝ ∞ φ)
    (hφts : tsupport φ ⊆ interior (cube L)) (hφsq : ∀ x : ℝ³, (φ x)^2 ≤ sp)
    (hφnorm : (∫ x : ℝ³, (φ x)^2) = 1) (Φn : CInfty0Box n L) :
    boxQuot (n+1) L v (psProdState Φn (oneState (φ := φ) hφc hφts hφnorm)) ≤
      boxQuot n L v Φn + (∫ x : ℝ³, |φ x * Δ φ x|) +
        (n : ℝ) * sp * (∫ x : ℝ³, |v x|) := by
  let Φ1 : CInfty0Box 1 L := oneState (φ := φ) hφc hφts hφnorm
  let Ψ : CInfty0Box (n+1) L := psProdState Φn Φ1
  let D1 : ℝ := psDen n L Φn
  let A : ℝ := ∫ x : ℝ³, |φ x * Δ φ x|
  let B : ℝ := ∫ x : ℝ³, |v x|
  have hD1pos : 0 < D1 := by
    have h := box_sq_integral_pos (N := n) (L := L) hL Φn
    simpa [D1, psDen, pow_two] using h
  have hD2 : psDen 1 L Φ1 = 1 := by
    dsimp [Φ1]
    exact oneState_den hφc hφts hφnorm
  have hnum1 : |psNum 1 L v Φ1| ≤ A := by
    dsimp [Φ1, A]
    exact psNum_one_abs_le (v := v) hφc hφts hφnorm
  have hC : |psCross (L := L) v Ψ| ≤ (n : ℝ) * sp * B * D1 := by
    dsimp [Ψ, Φ1, D1, B]
    exact psCross_add_one_abs_le (n := n) (L := L) (v := v) (φ := φ) (sp := sp)
      hL hv1 hsp0 hφc hφts hφsq hφnorm Φn
  have hDen : psDen (n+1) L Ψ = D1 := by
    calc
      psDen (n+1) L Ψ = psDen n L Φn * psDen 1 L Φ1 := by
            dsimp [Ψ]
            exact psDen_prod Φn Φ1
      _ = psDen n L Φn * 1 := by rw [hD2]
      _ = D1 := by simp [D1]
  have hNum : psNum (n+1) L v Ψ =
      psNum n L v Φn + D1 * psNum 1 L v Φ1 + psCross (L := L) v Ψ := by
    calc
      psNum (n+1) L v Ψ
          = psNum n L v Φn * psDen 1 L Φ1 + psDen n L Φn * psNum 1 L v Φ1 +
            psCross (L := L) v Ψ := by
            dsimp [Ψ]
            rw [psNum_prod (N1 := n) (N2 := 1) hL hv1 Φn Φ1]
      _ = psNum n L v Φn * 1 + D1 * psNum 1 L v Φ1 + psCross (L := L) v Ψ := by
            rw [hD2]
      _ = psNum n L v Φn + D1 * psNum 1 L v Φ1 + psCross (L := L) v Ψ := by
            rw [mul_one]
  have hQ : boxQuot (n+1) L v Ψ = psNum n L v Φn / D1 + psNum 1 L v Φ1 +
      psCross (L := L) v Ψ / D1 := by
    calc
      boxQuot (n+1) L v Ψ = psNum (n+1) L v Ψ / psDen (n+1) L Ψ := boxQuot_eq_ps Ψ
      _ = (psNum n L v Φn + D1 * psNum 1 L v Φ1 + psCross (L := L) v Ψ) / D1 := by
            rw [hNum, hDen]
      _ = psNum n L v Φn / D1 + psNum 1 L v Φ1 + psCross (L := L) v Ψ / D1 := by
            field_simp [ne_of_gt hD1pos]
  have hboxn : boxQuot n L v Φn = psNum n L v Φn / D1 := by
    dsimp [D1]
    exact boxQuot_eq_ps Φn
  have hnum1le : psNum 1 L v Φ1 ≤ A := le_abs_self (psNum 1 L v Φ1) |>.trans hnum1
  have hCdiv : psCross (L := L) v Ψ / D1 ≤ (n : ℝ) * sp * B := by
    calc
      psCross (L := L) v Ψ / D1 ≤ |psCross (L := L) v Ψ| / D1 := by
            exact div_le_div_of_nonneg_right (le_abs_self _) (le_of_lt hD1pos)
      _ ≤ ((n : ℝ) * sp * B * D1) / D1 := by
            exact div_le_div_of_nonneg_right hC (le_of_lt hD1pos)
      _ = (n : ℝ) * sp * B := by
            field_simp [ne_of_gt hD1pos]
  have hle : boxQuot (n+1) L v Ψ ≤ boxQuot n L v Φn + A + (n : ℝ) * sp * B := by
    rw [hQ, ← hboxn]
    nlinarith [hnum1le, hCdiv]
  simpa [Ψ, Φ1, A, B, mul_assoc] using hle

/-! ## The main result -/

/-- For a one-particle state `φ` (smooth, supported in the cube, `L²`-normalised,
with pointwise square bound `sp`), an `N`-particle product trial state has
Rayleigh quotient at most `N·∫|φΔφ| + N²·sp·∫|v|`. -/
lemma productState_facts {N : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hL : 0 < L) (hv1 : MemLp v 1)
    {φ : ℝ³ → ℝ} {sp : ℝ} (hsp0 : 0 ≤ sp) (hφc : ContDiff ℝ ∞ φ)
    (hφts : tsupport φ ⊆ interior (cube L)) (hφsq : ∀ x : ℝ³, (φ x) ^ 2 ≤ sp)
    (hφnorm : (∫ x : ℝ³, (φ x) ^ 2) = 1) :
    ∃ Ψ : CInfty0Box N L,
      boxQuot N L v Ψ ≤ (N : ℝ) * (∫ x : ℝ³, |φ x * Δ φ x|) +
        (N : ℝ) ^ 2 * sp * (∫ x : ℝ³, |v x|) := by
  let A : ℝ := ∫ x : ℝ³, |φ x * Δ φ x|
  let B : ℝ := ∫ x : ℝ³, |v x|
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact integral_nonneg (fun x => abs_nonneg (φ x * Δ φ x))
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact integral_nonneg (fun x => abs_nonneg (v x))
  have hmain : ∀ n : ℕ, ∃ Φ : CInfty0Box n L,
      boxQuot n L v Φ ≤ (n : ℝ) * A + (n : ℝ) ^ 2 * sp * B := by
    intro n
    induction n with
    | zero =>
        have hne : Nonempty (CInfty0Box 0 L) := nonempty_CInfty0Box 0 hL
        rcases hne with ⟨Φ0⟩
        refine ⟨Φ0, ?_⟩
        have hq0 : boxQuot 0 L v Φ0 = 0 := by
          rw [boxQuot_eq_ps Φ0]
          have hnum0 : psNum 0 L v Φ0 = 0 := by
            unfold psNum
            have hz : (fun x : X 0 => (Φ0 : X 0 → ℝ) x * 𝓗 0 v (Φ0 : X 0 → ℝ) x) = 0 := by
              funext x
              have hH : 𝓗 0 v (Φ0 : X 0 → ℝ) x = 0 := by
                unfold _root_.BoseGases.𝓗
                simp
              simp [hH]
            rw [hz]
            simp
          rw [hnum0]
          simp
        rw [hq0]
        norm_num
    | succ n ih =>
        rcases ih with ⟨Φn, hb⟩
        refine ⟨psProdState Φn (oneState (φ := φ) hφc hφts hφnorm), ?_⟩
        have hstep := boxQuot_add_one (n := n) (L := L) (v := v) (φ := φ) (sp := sp)
          hL hv1 hsp0 hφc hφts hφsq hφnorm Φn
        have hspB : 0 ≤ sp * B := mul_nonneg hsp0 hB0
        have hn0 : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
        have hpoly : (n : ℝ) ^ 2 + (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by
          rw [Nat.cast_add, Nat.cast_one]
          nlinarith
        calc
          boxQuot (n + 1) L v (psProdState Φn (oneState (φ := φ) hφc hφts hφnorm))
              ≤ boxQuot n L v Φn + A + (n : ℝ) * sp * B := hstep
          _ ≤ ((n : ℝ) * A + (n : ℝ) ^ 2 * sp * B) + A + (n : ℝ) * sp * B := by linarith [hb]
          _ = ((n + 1 : ℕ) : ℝ) * A + ((n : ℝ) ^ 2 + (n : ℝ)) * (sp * B) := by
                rw [Nat.cast_add, Nat.cast_one]
                ring
          _ ≤ ((n + 1 : ℕ) : ℝ) * A + ((n + 1 : ℕ) : ℝ) ^ 2 * (sp * B) := by
                have hm : ((n : ℝ) ^ 2 + (n : ℝ)) * (sp * B) ≤
                    ((n + 1 : ℕ) : ℝ) ^ 2 * (sp * B) :=
                  mul_le_mul_of_nonneg_right hpoly hspB
                nlinarith [hm]
          _ = ((n + 1 : ℕ) : ℝ) * A + ((n + 1 : ℕ) : ℝ) ^ 2 * sp * B := by ring
  rcases hmain N with ⟨Φ, hb⟩
  refine ⟨Φ, ?_⟩
  simpa [A, B, mul_assoc, mul_left_comm, mul_comm] using hb
