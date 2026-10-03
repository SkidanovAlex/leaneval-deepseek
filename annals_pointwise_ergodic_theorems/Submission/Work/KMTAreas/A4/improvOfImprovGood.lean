import Mathlib
import Submission.Work.KMTAreas.A4.ImprovGoodDefs
import Submission.Work.KMTAreas.A4.kmtProjMono
import Submission.Work.KMTAreas.A4.goodArcIndexDecay
import Submission.Work.KMTAreas.A4.smallLogAbsorb

/-!
# From the good-major-arc form of `improv` to `ImprovKMT`

`Work.KMTAreas.A4.ImprovGood P` is the single-scale minor-arc estimate `improv` of Krause--Mirek--Tao
§5 *in the regime in which the paper proves it*: the pair `(l, l - Log N)` has good major arcs (with
a constant `Cρ` depending on `ρ`), and the estimate carries the single gain `2^{-c l}`, with `c`
independent of `ρ`.

`Work.KMTContract.ImprovKMT P` is the same estimate without the good-major-arc hypothesis, and with
the secondary term `(Log N)^{-c/ρ}`.

The reduction is the paper's "monotonicity of the projection in `(l,k)`" argument, made explicit in
`ROUTE_LEAD.md` §5 / the docstring of `ImprovKMT`:

* if `(l, l - Log N)` has good major arcs, apply the good-arc estimate directly;
* otherwise let `l' ≤ l` be the **largest** index with good major arcs.  Since `GoodMajorArcs` is
  monotone in `l` (for `Cρ ≥ 0`) the index `l = 0` is good as soon as `Log N ≥ Cρ`, so `l'` exists
  unless `Log N < Cρ`, and in the latter case `0 ≤ l'` is unavailable -- but then every index is bad
  and the crude single-scale Hölder bound `‖Ã_N(f,g)‖_{ℓ¹} ≤ ‖f‖_{ℓ²}‖g‖_{ℓ²}` suffices, because
  `(Log N)^{-c/ρ}` is then bounded below by the positive constant `Cρ^{-c/ρ}`.
* In the remaining case `l' < l` one has `l' + 1 ∉ [0,l]` good, i.e.
  `Log N < (l'+1) + Cρ 2^{ρ(l'+1)}`, and the elementary decay `2^{-c l'} ≲ (Log N)^{-c/ρ}` of
  `Work.KMTAreas.A4.goodArcIndexDecay` applies.  The minor-arc hypothesis transfers from `l` to `l'`
  by `Work.KMTAreas.A4.kmtProjMono` (`Π_{≤l',≤k'} = T_m ∘ Π_{≤l,≤k}` for `l' ≤ l`, `k' ≤ k`).
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat BigOperators
open PointwiseErgodicTheorems
open Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger
open Work.Analysis.IWMultiplier
open Work.Analysis.EndVar
open Work.KMTContract

namespace Work.KMTAreas.A4

noncomputable section

/-! ## Elementary facts about the scales -/

/-- `Log N = ⌊log₂ max(N,2)⌋ ≥ 1`. -/
private lemma logN_ge_one (N : ℕ) : (1 : ℤ) ≤ logN N := by
  rw [show logN N = (Nat.log 2 (max N 2) : ℤ) from rfl]
  have h : 1 ≤ Nat.log 2 (max N 2) :=
    Nat.le_log_of_pow_le (by norm_num) (by omega)
  exact_mod_cast h

/-- **Monotonicity of the good-major-arc condition in `(l,k)`.**  For `ρ ≥ 0` and `Cρ ≥ 0` the
condition `k ≤ -Cρ 2^{ρ l}` is decreasing in `l` and increasing in `k`. -/
private lemma goodMajorArcs_mono {ρ Cρ : ℝ} (hρ : 0 ≤ ρ) (hCρ : 0 ≤ Cρ) {l l' : ℕ} (hl : l' ≤ l)
    {k k' : ℤ} (hk : k' ≤ k) (h : GoodMajorArcs ρ Cρ l k) : GoodMajorArcs ρ Cρ l' k' := by
  rw [GoodMajorArcs] at h ⊢
  have hl' : (l' : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hp : ρ * (l' : ℝ) ≤ ρ * (l : ℝ) := mul_le_mul_of_nonneg_left hl' hρ
  have hpow : (2 : ℝ) ^ (ρ * (l' : ℝ)) ≤ (2 : ℝ) ^ (ρ * (l : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hp
  have hstep : -Cρ * (2 : ℝ) ^ (ρ * (l : ℝ)) ≤ -Cρ * (2 : ℝ) ^ (ρ * (l' : ℝ)) := by
    nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (ρ * (l' : ℝ))]
  have hk' : (k' : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  linarith

/-! ## `ℝ≥0∞` bookkeeping -/

/-- `(a : ℝ≥0∞) * ofReal q = ofReal (a * q)`. -/
private lemma coe_mul_ofReal (a : ℝ≥0) (q : ℝ) :
    (a : ℝ≥0∞) * ENNReal.ofReal q = ENNReal.ofReal ((a : ℝ) * q) := by
  rw [ENNReal.ofReal_mul a.coe_nonneg, ENNReal.ofReal_coe_nnreal]

/-- `((a * b) : ℝ≥0∞) * ofReal q = ofReal (a * b * q)`. -/
private lemma coe_mul_ofReal' (a b : ℝ≥0) (q : ℝ) :
    ((a * b : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal q = ENNReal.ofReal ((a : ℝ) * (b : ℝ) * q) := by
  rw [ENNReal.coe_mul, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (a : ℝ) * (b : ℝ)),
    ENNReal.ofReal_mul a.coe_nonneg, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]

/-- Monotonicity of `a * F * G` in `a`. -/
private lemma ennreal_mul_mul_mono {a b : ℝ≥0∞} (h : a ≤ b) (F G : ℝ≥0∞) :
    a * F * G ≤ b * F * G :=
  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h bot_le) bot_le

/-- Absorption step: a real bound of the shape `Cg * q ≤ Cg * K * q'` lifts to `ℝ≥0∞`. -/
private lemma key_step {Cg K : ℝ≥0} {q q' : ℝ}
    (h : (Cg : ℝ) * q ≤ (Cg : ℝ) * (K : ℝ) * q') :
    (Cg : ℝ≥0∞) * ENNReal.ofReal q ≤ ((Cg * K : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal q' :=
  calc (Cg : ℝ≥0∞) * ENNReal.ofReal q = ENNReal.ofReal ((Cg : ℝ) * q) := coe_mul_ofReal Cg q
    _ ≤ ENNReal.ofReal ((Cg : ℝ) * (K : ℝ) * q') := ENNReal.ofReal_le_ofReal h
    _ = ((Cg * K : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal q' := (coe_mul_ofReal' Cg K q').symm

/-! ## The reduction -/

theorem improvOfImprovGood (P : Polynomial ℤ)
    (h : Work.KMTAreas.A4.ImprovGood P) : Work.KMTContract.ImprovKMT P := by
  classical
  obtain ⟨c, hc, hmain⟩ := h
  refine ⟨c, hc, ?_⟩
  intro ρ hρ0 hρ1
  obtain ⟨Cρ, Cg, hCρ, hCg, hbound⟩ := hmain ρ hρ0 hρ1
  obtain ⟨K₁, _hK₁pos, hK₁⟩ := goodArcIndexDecay hc hρ0 hCρ hCg
  obtain ⟨K₂, _hK₂pos, hK₂⟩ := smallLogAbsorb hc hρ0 hCρ hCg
  refine ⟨Cg * max 1 (max K₁ K₂), ?_⟩
  set K : ℝ≥0 := max 1 (max K₁ K₂) with hKdef
  have hK₁le : K₁ ≤ K := by
    rw [hKdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hK₂le : K₂ ≤ K := by
    rw [hKdef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hKge1 : 1 ≤ K := by rw [hKdef]; exact le_max_left _ _
  intro N l f g hN hf hg hproj
  set A : ℝ≥0∞ := eLpNorm (fun x : ℤ => AhalfR TZ (N : ℝ≥0) X P f g x) 1 Measure.count with hA
  set F : ℝ≥0∞ := eLpNorm f 2 Measure.count with hF
  set G : ℝ≥0∞ := eLpNorm g 2 Measure.count with hG
  set Lr : ℝ := ((logN N : ℤ) : ℝ) with hLr
  set U : ℝ := (2 : ℝ) ^ (-(c * (l : ℝ))) with hU
  have hx1 : (1 : ℝ) ≤ Lr := by rw [hLr]; exact_mod_cast logN_ge_one N
  have hU0 : (0 : ℝ) ≤ U := by rw [hU]; exact Real.rpow_nonneg (by norm_num) _
  have hV0 : (0 : ℝ) ≤ Lr ^ (-(c / ρ)) := Real.rpow_nonneg (le_trans zero_le_one hx1) _
  have hUle : U ≤ U + Lr ^ (-(c / ρ)) := le_add_of_nonneg_right hV0
  have hVle : Lr ^ (-(c / ρ)) ≤ U + Lr ^ (-(c / ρ)) := le_add_of_nonneg_left hU0
  have hCgK : (Cg : ℝ≥0) ≤ Cg * K := by
    calc Cg = Cg * 1 := (mul_one Cg).symm
      _ ≤ Cg * K := mul_le_mul_of_nonneg_left hKge1 (by positivity)
  have hCK : (Cg : ℝ≥0∞) ≤ ((Cg * K : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_le_coe]; exact hCgK
  by_cases hcase : Cρ ≤ Lr
  · -- `Log N ≥ Cρ`, so the index `0` has good major arcs and the good indices `≤ l` form a
    -- nonempty finite set
    let good : ℕ → Prop := fun l' => GoodMajorArcs ρ Cρ l' ((l' : ℤ) - logN N)
    have h0 : good 0 := by
      show GoodMajorArcs ρ Cρ 0 ((0 : ℤ) - logN N)
      rw [GoodMajorArcs]
      have hcast : (((0 : ℤ) - logN N : ℤ) : ℝ) = -Lr := by rw [hLr]; push_cast; ring
      rw [hcast]
      have hexp : (2 : ℝ) ^ (ρ * ((0 : ℕ) : ℝ)) = 1 := by norm_num
      rw [hexp, mul_one]
      linarith
    let s : Finset ℕ := (Finset.range (l + 1)).filter good
    have hsne : s.Nonempty := by
      refine ⟨0, ?_⟩
      rw [show s = (Finset.range (l + 1)).filter good from rfl]
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h0⟩
    let l' : ℕ := s.max' hsne
    have hl'mem : l' ∈ s := by simpa only [l'] using Finset.max'_mem s hsne
    have hgoodl' : good l' := (Finset.mem_filter.mp hl'mem).2
    have hl'le : l' ≤ l := by
      have h1 := (Finset.mem_filter.mp hl'mem).1
      simp only [Finset.mem_range] at h1
      omega
    by_cases heq : l' = l
    · -- the index `l` itself has good major arcs: apply the good-arc estimate at `l`
      have hgoodA : GoodMajorArcs ρ Cρ l ((l : ℤ) - logN N) := by
        have := hgoodl'
        rw [heq] at this
        exact this
      have hb := hbound N l f g hN hf hg hgoodA hproj
      have hstep1 : (Cg : ℝ≥0∞) * ENNReal.ofReal U * F * G
          ≤ (Cg : ℝ≥0∞) * ENNReal.ofReal (U + Lr ^ (-(c / ρ))) * F * G :=
        ennreal_mul_mul_mono
          (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hUle) bot_le) F G
      have hstep2 : (Cg : ℝ≥0∞) * ENNReal.ofReal (U + Lr ^ (-(c / ρ))) * F * G
          ≤ (((Cg * K : ℝ≥0)) : ℝ≥0∞) * ENNReal.ofReal (U + Lr ^ (-(c / ρ))) * F * G :=
        ennreal_mul_mul_mono (mul_le_mul_of_nonneg_right hCK bot_le) F G
      exact hb.trans (hstep1.trans hstep2)
    · -- `l' < l` is the largest good index
      have hlt : l' < l := lt_of_le_of_ne hl'le heq
      have hnotgood : ¬ good (l' + 1) := by
        intro hg
        have hmem' : l' + 1 ∈ s := by
          rw [show s = (Finset.range (l + 1)).filter good from rfl]
          exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hg⟩
        have := Finset.le_max' s (l' + 1) hmem'
        omega
      have hgen : Lr < ((l' : ℝ) + 1) + Cρ * (2 : ℝ) ^ (ρ * ((l' : ℝ) + 1)) := by
        have h1 : ¬ (((((l' + 1 : ℕ) : ℤ) - logN N : ℤ) : ℝ)
            ≤ -Cρ * (2 : ℝ) ^ (ρ * (((l' + 1 : ℕ) : ℝ)))) := by
          simpa only [good, GoodMajorArcs] using hnotgood
        have h2 := not_le.mp h1
        have hcast : ((((l' + 1 : ℕ) : ℤ) - logN N : ℤ) : ℝ) = (l' : ℝ) + 1 - Lr := by
          rw [hLr]; push_cast; ring
        have hexp : ρ * (((l' + 1 : ℕ) : ℝ)) = ρ * ((l' : ℝ) + 1) := by push_cast; ring
        rw [hcast, hexp] at h2
        linarith
      -- the minor-arc hypothesis transfers from `l` to `l'`
      have hproj' : kmtProj ρ l' (-(logN N) + (l' : ℤ)) f = 0 ∨
          kmtProj ρ l' ((P.natDegree : ℤ) * (-(logN N) + (l' : ℤ))) g = 0 := by
        rcases hproj with hf0 | hg0
        · left
          refine kmtProjMono ρ hρ0 hρ1 hl'le ?_ hf hf0
          omega
        · right
          refine kmtProjMono ρ hρ0 hρ1 hl'le ?_ hg hg0
          have h1 : (-(logN N) + (l' : ℤ)) ≤ (-(logN N) + (l : ℤ)) := by omega
          exact mul_le_mul_of_nonneg_left h1 (Int.natCast_nonneg _)
      have hb := hbound N l' f g hN hf hg hgoodl' hproj'
      have hnum : Cg * (2 : ℝ) ^ (-(c * (l' : ℝ))) ≤ Cg * (K : ℝ) * Lr ^ (-(c / ρ)) := by
        refine (hK₁ Lr l' hx1 hgen).trans ?_
        have hKK : (K₁ : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK₁le
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKK hCg.le) hV0
      have hstep1 : (Cg : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l' : ℝ)))) * F * G
          ≤ (((Cg * K : ℝ≥0)) : ℝ≥0∞) * ENNReal.ofReal (Lr ^ (-(c / ρ))) * F * G :=
        ennreal_mul_mul_mono (key_step hnum) F G
      have hstep2 : (((Cg * K : ℝ≥0)) : ℝ≥0∞) * ENNReal.ofReal (Lr ^ (-(c / ρ))) * F * G
          ≤ (((Cg * K : ℝ≥0)) : ℝ≥0∞) * ENNReal.ofReal (U + Lr ^ (-(c / ρ))) * F * G :=
        ennreal_mul_mul_mono
          (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hVle) bot_le) F G
      exact hb.trans (hstep1.trans hstep2)
  · -- `Log N < Cρ`: every index is bad, and the crude Hölder bound suffices
    simp only [not_le] at hcase
    have hrel : (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ = (1 : ℝ≥0∞)⁻¹ := by
      rw [inv_one, ENNReal.inv_two_add_inv_two]
    have htriv : A ≤ F * G :=
      eLpNorm_AhalfR_le TZ measurePreserving_TZ (N : ℝ≥0) X P hrel (by norm_num) hf hg
    have hnum : 1 ≤ Cg * (K : ℝ) * Lr ^ (-(c / ρ)) := by
      refine (hK₂ Lr hx1 hcase).trans ?_
      have hKK : (K₂ : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK₂le
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKK hCg.le) hV0
    have h1 : (1 : ℝ≥0∞) ≤ (((Cg * K : ℝ≥0)) : ℝ≥0∞) * ENNReal.ofReal (Lr ^ (-(c / ρ))) :=
      calc (1 : ℝ≥0∞) = ENNReal.ofReal (1 : ℝ) := ENNReal.ofReal_one.symm
        _ ≤ ENNReal.ofReal (Cg * (K : ℝ) * Lr ^ (-(c / ρ))) := ENNReal.ofReal_le_ofReal hnum
        _ = (((Cg * K : ℝ≥0)) : ℝ≥0∞) * ENNReal.ofReal (Lr ^ (-(c / ρ))) :=
              (coe_mul_ofReal' Cg K (Lr ^ (-(c / ρ)))).symm
    have hstep0 : F * G ≤ ((((Cg * K : ℝ≥0)) : ℝ≥0∞) * ENNReal.ofReal (Lr ^ (-(c / ρ))))
        * (F * G) := by
      calc F * G = 1 * (F * G) := (one_mul _).symm
        _ ≤ ((((Cg * K : ℝ≥0)) : ℝ≥0∞) * ENNReal.ofReal (Lr ^ (-(c / ρ)))) * (F * G) :=
              mul_le_mul_of_nonneg_right h1 bot_le
    have hstep1 : A ≤ (((Cg * K : ℝ≥0)) : ℝ≥0∞) * ENNReal.ofReal (Lr ^ (-(c / ρ))) * (F * G) :=
      htriv.trans hstep0
    have hstep2 : ((((Cg * K : ℝ≥0)) : ℝ≥0∞) * ENNReal.ofReal (Lr ^ (-(c / ρ)))) * (F * G)
        ≤ ((((Cg * K : ℝ≥0)) : ℝ≥0∞) * ENNReal.ofReal (U + Lr ^ (-(c / ρ)))) * (F * G) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hVle) bot_le) bot_le
    have hstep3 : (((Cg * K : ℝ≥0)) : ℝ≥0∞) * ENNReal.ofReal (U + Lr ^ (-(c / ρ))) * (F * G)
        = (((Cg * K : ℝ≥0)) : ℝ≥0∞) * ENNReal.ofReal (U + Lr ^ (-(c / ρ))) * F * G := by ring
    exact hstep1.trans (hstep2.trans hstep3.le)

end

end Work.KMTAreas.A4
