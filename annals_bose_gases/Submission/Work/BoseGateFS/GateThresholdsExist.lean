import ChallengeDeps
import Submission.Work.BoseB7.fsEnv_closed
import Submission.Work.BoseGateFS.GateThresholds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseGateFS.GateThresholdsExist` — the small-parameter bundle is inhabited

`Work.BoseGateFS.GateThresholds v h fc fu R` is the node's explicit `Ng`/`εg`
bundle.  This module proves `Nonempty (GateThresholds v h fc fu R)` for every
`0 < a v` and every `R`, i.e. the node's parameter arithmetic is not an extra
hypothesis of `exists_honestGateFS_of_fsRows`.

Everything is a monomial in `t = μa³` (at `X = (μa³)^{1/323}`):

| scalar | closed form |
|---|---|
| `ℓ = ellH v μ` | `a t^{-163/323}` (`Work.BoseBox.sideAt_eq_rpow`) |
| `K_H a` | `a^{11/6} t^{-549/1292}` (`fsKHVal_eq`) |
| `K_L` | `t^{-21/646}` (`fsKLVal_eq`) |
| `s`, `d`, `ε_T` | `t^{1/323}`, `t^{6/323}`, `t^{23/1292}` |
| `√(μa)` | `t^{1/2}/a` |

so each of the ten diluteness conditions is an inequality
`t^{q} ≤ C(a, R)` for some `q > 0`, satisfied as soon as `t ≤ C^{1/q}`.  The
bundle takes `εg` to be the minimum of these (together with `1`) and
`Ng μ = ⌈M μ⌉` with `M μ` the maximum of the four cube-size conditions
(`ℓ`-weights of `1`, `(4K_Ha)^{-1}`, `4K_L√(μa)` and `2K_L√(μa)`).

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped BigOperators Pointwise Real

namespace Work.BoseGateFS

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open _root_.BoseGases Submission.BoseGases

/-! ## 1. Two `Real.rpow` helpers -/

/-- `(C^{1/e})^e = C` for `C > 0`, `e > 0`. -/
lemma rpow_one_div_pow_cancel {C e : ℝ} (hC : 0 < C) (he : 0 < e) :
    (C ^ (1 / e)) ^ e = C := by
  rw [← Real.rpow_mul hC.le, one_div, inv_mul_cancel₀ (ne_of_gt he), Real.rpow_one]

/-- `t^e ≤ C` from `t ≤ C^{1/e}` (`C > 0`, `e > 0`, `t > 0`). -/
lemma rpow_le_of_le_rpow {t C e : ℝ} (ht : 0 < t) (hC : 0 < C) (he : 0 < e)
    (h : t ≤ C ^ (1 / e)) : t ^ e ≤ C := by
  have h1 : t ^ e ≤ (C ^ (1 / e)) ^ e := Real.rpow_le_rpow ht.le h he.le
  rwa [rpow_one_div_pow_cancel hC he] at h1

/-- `a · t^{-q} = a / t^{q}` for `t > 0`. -/
lemma mul_rpow_neg_eq_div {b t q : ℝ} (ht : 0 < t) :
    b * t ^ (-q) = b / t ^ q := by
  rw [Real.rpow_neg ht.le, div_eq_mul_inv]

/-! ## 2. The closed forms of the honest scalars -/

/-- The box side at the honest parameters: `ellH v μ = a v · (dil v μ)^{-163/323}`. -/
lemma ellH_eq_rpow {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} (hμ : 0 < μ)
    (hav : 0 < a v) :
    ellH v μ = a v * (μ * (a v) ^ 3) ^ (-(163 / 323 : ℝ)) := by
  have hpos : 0 < Work.BoseBox.sideAt μ (a v) := Work.BoseBox.sideAt_pos hμ hav
  rw [ellH, if_pos hpos]
  exact Work.BoseBox.sideAt_eq_rpow hav hμ

/-- The honest `K_H`: `K_H = t^{-549/1292}` at `t = dil v μ`. -/
lemma honE_KH_eq {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    {HM : ∀ μ : ℝ, HonestModes v μ} {μ : ℝ} (hμ : 0 < μ) (hav : 0 < a v) :
    (honE v h fc fu HM μ).KH = (μ * (a v) ^ 3) ^ (-(549 / 1292 : ℝ)) := by
  have ht : 0 < μ * (a v) ^ 3 := mul_pos hμ (pow_pos hav 3)
  rw [show (honE v h fc fu HM μ).KH
      = (Work.BoseFixR.KzEnvFs v h μ (honF v h fc fu HM μ) fc).KH from rfl]
  rw [Work.BoseFixR.KzEnvFs_KH_val ht, Work.BoseBox.fsXp]
  norm_num

/-- The honest `K_L`: `K_L = t^{-21/646}` at `t = dil v μ`. -/
lemma honE_KL_eq {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    {HM : ∀ μ : ℝ, HonestModes v μ} {μ : ℝ} (hμ : 0 < μ) (hav : 0 < a v) :
    (honE v h fc fu HM μ).KL = (μ * (a v) ^ 3) ^ (-(21 / 646 : ℝ)) := by
  have ht : 0 < μ * (a v) ^ 3 := mul_pos hμ (pow_pos hav 3)
  rw [show (honE v h fc fu HM μ).KL
      = (Work.BoseFixR.KzEnvFs v h μ (honF v h fc fu HM μ) fc).KL from rfl]
  rw [Work.BoseFixR.KzEnvFs_KL_val ht, Work.BoseBox.fsXp]
  norm_num

/-- The honest `s`: `s = t^{1/323}`. -/
lemma honE_s_eq {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    {HM : ∀ μ : ℝ, HonestModes v μ} {μ : ℝ} :
    (honE v h fc fu HM μ).s = (μ * (a v) ^ 3) ^ (1 / 323 : ℝ) := by
  rw [show (honE v h fc fu HM μ).s
      = (Work.BoseFixR.KzEnvFs v h μ (honF v h fc fu HM μ) fc).s from rfl]
  rw [Work.BoseFixR.KzEnvFs_s_val, Work.BoseBox.fsXp]

/-- The honest `d`: `d = t^{6/323}`. -/
lemma honE_d_eq {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    {HM : ∀ μ : ℝ, HonestModes v μ} {μ : ℝ} :
    (honE v h fc fu HM μ).d = (μ * (a v) ^ 3) ^ (6 / 323 : ℝ) := by
  rw [show (honE v h fc fu HM μ).d
      = (Work.BoseFixR.KzEnvFs v h μ (honF v h fc fu HM μ) fc).d from rfl]
  rw [Work.BoseFixR.KzEnvFs_d_val, Work.BoseBox.fsXp]

/-- The honest `ε_T`: `ε_T = t^{23/1292}`. -/
lemma honE_eT_eq {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    {HM : ∀ μ : ℝ, HonestModes v μ} {μ : ℝ} :
    (honE v h fc fu HM μ).eT = (μ * (a v) ^ 3) ^ (23 / 1292 : ℝ) := by
  rw [show (honE v h fc fu HM μ).eT
      = (Work.BoseFixR.KzEnvFs v h μ (honF v h fc fu HM μ) fc).eT from rfl]
  rw [Work.BoseFixR.KzEnvFs_eT_val, Work.BoseBox.fsXp]
  norm_num


/-! ## 3. Power comparisons at `0 < t ≤ 1` -/

/-- For `0 < t ≤ 1`, a larger exponent gives a smaller power. -/
lemma rpow_le_rpow_of_le_one {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) {q q' : ℝ} (h : q' ≤ q) :
    t ^ q ≤ t ^ q' := by
  have h2 : t ^ (q - q') ≤ 1 := Real.rpow_le_one h0.le h1 (by linarith)
  calc t ^ q = t ^ q' * t ^ (q - q') := by
        rw [← Real.rpow_add h0]; ring_nf
    _ ≤ t ^ q' * 1 := mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg h0.le _)
    _ = t ^ q' := mul_one _

/-! ## 4. The bundle is inhabited -/

set_option maxHeartbeats 3200000 in
/-- **The small-parameter bundle is inhabited.**  `Ng μ` is the ceiling of the
maximum of the cube-size conditions, `εg` the minimum of the three diluteness
thresholds together with `1`. -/
theorem exists_gateThresholds {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v}
    (fc fu : LowCut) (hav : 0 < a v) (R : ℝ) :
    Nonempty (GateThresholds v h fc fu R) := by
  classical
  have hapos : 0 < a v := hav
  have hRpos : (0 : ℝ) < max R 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hchi : (0 : ℝ) < Submission.BoseGases.chiR0 := Submission.BoseGases.chiR0_pos
  let M : ℝ → ℝ := fun μ => max (2 * ellH v μ / Real.pi)
    (max (ellH v μ / (2 * Real.pi * (Work.BoseBox.fsXp (μ * (a v) ^ 3) (-(549 / 4 : ℝ))
        * (a v))))
      (8 * ellH v μ * Work.BoseBox.fsXp (μ * (a v) ^ 3) (-(21 / 2 : ℝ))
        * Real.sqrt (μ * (a v)) / Real.pi))
  let b2 : ℝ := (a v) ^ (1 / (163 / 323 : ℝ))
  let b4 : ℝ := (2 * (a v) / max R 1) ^ (1 / (549 / 1292 : ℝ))
  let b5 : ℝ := ((a v) * Submission.BoseGases.chiR0 / max R 1) ^ (1 / (163 / 323 : ℝ))
  let b7 : ℝ := ((1 / 2 : ℝ)) ^ (1 / (3 / 323 : ℝ))
  let b10 : ℝ := ((1 / 16 : ℝ)) ^ (1 / (55 / 1292 : ℝ))
  let b11 : ℝ := ((1 / 32 : ℝ)) ^ (1 / (99 / 1292 : ℝ))
  let b12 : ℝ := ((1 / 8 : ℝ)) ^ (1 / (75 / 1292 : ℝ))
  let b13 : ℝ := (a v) ^ (1 / (549 / 1292 : ℝ))
  refine ⟨{ Ng := fun μ => Nat.ceil (M μ),
             εg := min 1 (min b2 (min b4 (min b5 (min b7 (min b10 (min b11 (min b12 b13))))))),
             pos := lt_min one_pos (lt_min (Real.rpow_pos_of_pos hapos _)
               (lt_min (Real.rpow_pos_of_pos (by positivity) _)
               (lt_min (Real.rpow_pos_of_pos (by positivity) _)
               (lt_min (Real.rpow_pos_of_pos (by norm_num) _)
               (lt_min (Real.rpow_pos_of_pos (by norm_num) _)
               (lt_min (Real.rpow_pos_of_pos (by norm_num) _)
               (lt_min (Real.rpow_pos_of_pos (by norm_num) _)
                 (Real.rpow_pos_of_pos hapos _)))))))),
             le_one := min_le_left _ _,
             cube := ?_,
             dil := ?_,
             dilTau := ?_,
             dilKH := ?_ }⟩
  · -- the cube conditions
    intro HM hN μ hμ hε
    have hMN : M μ ≤ ((HM μ).N : ℝ) := Nat.ceil_le.mp (hN μ)
    have hℓpos : 0 < ellH v μ := ellH_pos v μ
    have hKH : (honE v h fc fu HM μ).KH = (μ * (a v) ^ 3) ^ (-(549 / 1292 : ℝ)) :=
      honE_KH_eq hμ hapos
    have hKL : (honE v h fc fu HM μ).KL = (μ * (a v) ^ 3) ^ (-(21 / 646 : ℝ)) :=
      honE_KL_eq hμ hapos
    have hfsKH : Work.BoseBox.fsXp (μ * (a v) ^ 3) (-(549 / 4 : ℝ))
        = (μ * (a v) ^ 3) ^ (-(549 / 1292 : ℝ)) := by
      rw [Work.BoseBox.fsXp]; norm_num
    have hfsKL : Work.BoseBox.fsXp (μ * (a v) ^ 3) (-(21 / 2 : ℝ))
        = (μ * (a v) ^ 3) ^ (-(21 / 646 : ℝ)) := by
      rw [Work.BoseBox.fsXp]; norm_num
    have hT : (0 : ℝ) < μ * (a v) ^ 3 := mul_pos hμ (pow_pos hapos 3)
    have hK1 : (0 : ℝ) < (μ * (a v) ^ 3) ^ (-(549 / 1292 : ℝ)) := Real.rpow_pos_of_pos hT _
    have hK2 : (0 : ℝ) < (μ * (a v) ^ 3) ^ (-(21 / 646 : ℝ)) := Real.rpow_pos_of_pos hT _
    have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
    have hs : 0 ≤ Real.sqrt (μ * (a v)) := Real.sqrt_nonneg _
    have hMex : M μ = max (2 * ellH v μ / Real.pi)
        (max (ellH v μ / (2 * Real.pi * (Work.BoseBox.fsXp (μ * (a v) ^ 3) (-(549 / 4 : ℝ))
            * (a v))))
          (8 * ellH v μ * Work.BoseBox.fsXp (μ * (a v) ^ 3) (-(21 / 2 : ℝ))
            * Real.sqrt (μ * (a v)) / Real.pi)) := rfl
    have hA : 2 * ellH v μ / Real.pi ≤ M μ := by rw [hMex]; exact le_max_left _ _
    have hB : ellH v μ / (2 * Real.pi * (Work.BoseBox.fsXp (μ * (a v) ^ 3) (-(549 / 4 : ℝ))
        * (a v))) ≤ M μ := by
      rw [hMex]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    have hC : 8 * ellH v μ * Work.BoseBox.fsXp (μ * (a v) ^ 3) (-(21 / 2 : ℝ))
        * Real.sqrt (μ * (a v)) / Real.pi ≤ M μ := by
      rw [hMex]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    have h1 : 2 * ellH v μ / Real.pi ≤ ((HM μ).N : ℝ) := le_trans hA hMN
    have h2 : ellH v μ / (2 * Real.pi * ((μ * (a v) ^ 3) ^ (-(549 / 1292 : ℝ)) * (a v)))
        ≤ ((HM μ).N : ℝ) := by
      rw [hfsKH] at hB
      exact le_trans hB hMN
    have h3 : 8 * ellH v μ * (μ * (a v) ^ 3) ^ (-(21 / 646 : ℝ)) * Real.sqrt (μ * (a v))
        / Real.pi ≤ ((HM μ).N : ℝ) := by
      rw [hfsKL] at hC
      exact le_trans hC hMN
    have h4 : 2 * ellH v μ * (μ * (a v) ^ 3) ^ (-(21 / 646 : ℝ)) * Real.sqrt (μ * (a v))
        / Real.pi ≤ ((HM μ).N : ℝ) := by
      have hnon : 0 ≤ ellH v μ * (μ * (a v) ^ 3) ^ (-(21 / 646 : ℝ)) * Real.sqrt (μ * (a v))
          / Real.pi := div_nonneg (mul_nonneg (mul_nonneg hℓpos.le hK2.le) hs) hπ.le
      have hEq : 2 * ellH v μ * (μ * (a v) ^ 3) ^ (-(21 / 646 : ℝ)) * Real.sqrt (μ * (a v))
            / Real.pi
          = 2 * (ellH v μ * (μ * (a v) ^ 3) ^ (-(21 / 646 : ℝ)) * Real.sqrt (μ * (a v))
              / Real.pi) := by ring
      have hEq8 : 8 * ellH v μ * (μ * (a v) ^ 3) ^ (-(21 / 646 : ℝ)) * Real.sqrt (μ * (a v))
            / Real.pi
          = 8 * (ellH v μ * (μ * (a v) ^ 3) ^ (-(21 / 646 : ℝ)) * Real.sqrt (μ * (a v))
              / Real.pi) := by ring
      rw [hEq8] at h3
      rw [hEq]
      linarith [h3, hnon]
    have huv : uvRad (ellH v μ) (HM μ).N
        = Real.pi * ((HM μ).N : ℝ) / (2 * ellH v μ) := by
      rw [uvRad]; field_simp; ring
    have hNR : (0 : ℝ) < ((HM μ).N : ℝ) := lt_of_lt_of_le (by positivity : 0 < M μ) hMN
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- C1
      rw [huv, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ellH v μ)]
      have h := (div_le_iff₀ hπ).mp h1
      nlinarith [h]
    · -- C2
      have hgoal : 1 / (4 * ((μ * (a v) ^ 3) ^ (-(549 / 1292 : ℝ)) * (a v)))
          ≤ Real.pi * ((HM μ).N : ℝ) / (2 * ellH v μ) := by
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ellH v μ)]
        rw [div_mul_eq_mul_div,
          div_le_iff₀ (by positivity : (0 : ℝ) < 4 * ((μ * (a v) ^ 3) ^ (-(549 / 1292 : ℝ))
            * (a v)))]
        have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi
          * ((μ * (a v) ^ 3) ^ (-(549 / 1292 : ℝ)) * (a v)))).mp h2
        nlinarith [h]
      rwa [show 4 * (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat
            = 4 * ((honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat) from by ring,
          show (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat
            = (μ * (a v) ^ 3) ^ (-(549 / 1292 : ℝ)) * (a v) from by rw [hKH]; rfl,
          huv]
    · -- C3
      have hgoal : 4 * ((μ * (a v) ^ 3) ^ (-(21 / 646 : ℝ)) * Real.sqrt (μ * (a v)))
          ≤ Real.pi * ((HM μ).N : ℝ) / (2 * ellH v μ) := by
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ellH v μ)]
        have h := (div_le_iff₀ hπ).mp h3
        nlinarith [h]
      rwa [show 4 * ((honE v h fc fu HM μ).KL * Real.sqrt ((honE v h fc fu HM μ).mu
              * (honE v h fc fu HM μ).aScat))
            = 4 * ((μ * (a v) ^ 3) ^ (-(21 / 646 : ℝ)) * Real.sqrt (μ * (a v))) from by
          rw [hKL]; rfl,
          huv]
    · -- C4
      have hgoal : ellH v μ * (2 * ((μ * (a v) ^ 3) ^ (-(21 / 646 : ℝ))
              * Real.sqrt (μ * (a v)))
            + 2 * (Real.pi * ((HM μ).N : ℝ) / (2 * ellH v μ))) / (2 * Real.pi)
          ≤ ((HM μ).N : ℝ) := by
        have h := (div_le_iff₀ hπ).mp h4
        field_simp
        nlinarith [h, hℓpos, hK2.le, hs, hπ, hNR]
      rwa [show 2 * ((honE v h fc fu HM μ).KL * Real.sqrt ((honE v h fc fu HM μ).mu
              * (honE v h fc fu HM μ).aScat))
            = 2 * ((μ * (a v) ^ 3) ^ (-(21 / 646 : ℝ)) * Real.sqrt (μ * (a v))) from by
          rw [hKL]; rfl,
          huv]
  · -- the diluteness conditions
    intro HM hN μ hμ hε
    have hKH : (honE v h fc fu HM μ).KH = (μ * (a v) ^ 3) ^ (-(549 / 1292 : ℝ)) :=
      honE_KH_eq hμ hapos
    have hKL : (honE v h fc fu HM μ).KL = (μ * (a v) ^ 3) ^ (-(21 / 646 : ℝ)) :=
      honE_KL_eq hμ hapos
    have hs := honE_s_eq (v := v) (h := h) (fc := fc) (fu := fu) (HM := HM) (μ := μ)
    have haScat : (honE v h fc fu HM μ).aScat = a v := rfl
    have hmu : (honE v h fc fu HM μ).mu = μ := rfl
    have hellE : (honE v h fc fu HM μ).ell = ellH v μ := by
      rw [ellH, if_pos (Work.BoseBox.sideAt_pos hμ hapos)]
      rfl
    have hT : (0 : ℝ) < μ * (a v) ^ 3 := mul_pos hμ (pow_pos hapos 3)
    have hε' : μ * (a v) ^ 3
        ≤ min 1 (min b2 (min b4 (min b5 (min b7 (min b10 (min b11 (min b12 b13))))))) := hε
    have hT1 : μ * (a v) ^ 3 ≤ 1 := le_trans hε' (min_le_left _ _)
    have e2 : μ * (a v) ^ 3 ≤ b2 :=
      le_trans hε' (le_trans (min_le_right _ _) (min_le_left _ _))
    have e4 : μ * (a v) ^ 3 ≤ b4 :=
      le_trans hε' (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
    have e5 : μ * (a v) ^ 3 ≤ b5 :=
      le_trans hε' (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _))))
    have e7 : μ * (a v) ^ 3 ≤ b7 :=
      le_trans hε' (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))))
    have e10 : μ * (a v) ^ 3 ≤ b10 :=
      le_trans hε' (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (min_le_left _ _))))))
    have e11 : μ * (a v) ^ 3 ≤ b11 :=
      le_trans hε' (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
            (min_le_left _ _)))))))
    have e12 : μ * (a v) ^ 3 ≤ b12 :=
      le_trans hε' (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _) (min_le_left _ _))))))))
    have e13 : μ * (a v) ^ 3 ≤ b13 :=
      le_trans hε' (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _) (min_le_right _ _))))))))
    have p2 : (μ * (a v) ^ 3) ^ (163 / 323 : ℝ) ≤ a v :=
      rpow_le_of_le_rpow hT hapos (by norm_num) e2
    have p4 : (μ * (a v) ^ 3) ^ (549 / 1292 : ℝ) ≤ 2 * (a v) / max R 1 :=
      rpow_le_of_le_rpow hT (by positivity) (by norm_num) e4
    have p5 : (μ * (a v) ^ 3) ^ (163 / 323 : ℝ)
        ≤ a v * Submission.BoseGases.chiR0 / max R 1 :=
      rpow_le_of_le_rpow hT (by positivity) (by norm_num) e5
    have p7 : (μ * (a v) ^ 3) ^ (3 / 323 : ℝ) ≤ 1 / 2 :=
      rpow_le_of_le_rpow hT (by norm_num) (by norm_num) e7
    have p10 : (μ * (a v) ^ 3) ^ (55 / 1292 : ℝ) ≤ 1 / 16 :=
      rpow_le_of_le_rpow hT (by norm_num) (by norm_num) e10
    have p11 : (μ * (a v) ^ 3) ^ (99 / 1292 : ℝ) ≤ 1 / 32 :=
      rpow_le_of_le_rpow hT (by norm_num) (by norm_num) e11
    have p12 : (μ * (a v) ^ 3) ^ (75 / 1292 : ℝ) ≤ 1 / 8 :=
      rpow_le_of_le_rpow hT (by norm_num) (by norm_num) e12
    have p13 : (μ * (a v) ^ 3) ^ (549 / 1292 : ℝ) ≤ a v :=
      rpow_le_of_le_rpow hT hapos (by norm_num) e13
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- `1 ≤ ℓ`
      rw [ellH_eq_rpow hμ hapos]
      simp only [Real.rpow_neg hT.le]
      rw [← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hT _)]
      simpa using p2
    · -- `R ≤ 2 K_H a`
      rw [hKH, haScat]
      simp only [Real.rpow_neg hT.le]
      rw [show 2 * (((μ * (a v) ^ 3) ^ (549 / 1292 : ℝ))⁻¹ * a v)
          = 2 * (a v * ((μ * (a v) ^ 3) ^ (549 / 1292 : ℝ))⁻¹) from by ring]
      rw [← div_eq_mul_inv]
      rw [show 2 * (a v / (μ * (a v) ^ 3) ^ (549 / 1292 : ℝ))
          = (2 * a v) / (μ * (a v) ^ 3) ^ (549 / 1292 : ℝ) from by ring]
      by_cases hR : R ≤ 0
      · have hpostv : (0 : ℝ) < (2 * a v) / (μ * (a v) ^ 3) ^ (549 / 1292 : ℝ) := by
          positivity
        linarith
      · have hR0 : 0 < R := lt_of_not_ge hR
        rw [le_div_iff₀ (Real.rpow_pos_of_pos hT _)]
        have h2 : (2 * a v) / max R 1 ≤ (2 * a v) / R :=
          div_le_div_of_nonneg_left (by positivity) hR0 (le_max_left _ _)
        have h3 : R * ((2 * a v) / R) = 2 * a v := by field_simp
        have h4 : R * (μ * (a v) ^ 3) ^ (549 / 1292 : ℝ)
            ≤ R * ((2 * a v) / max R 1) := mul_le_mul_of_nonneg_left p4 hR0.le
        have h5 : R * ((2 * a v) / max R 1) ≤ R * ((2 * a v) / R) :=
          mul_le_mul_of_nonneg_left h2 hR0.le
        linarith [h4, h5, h3.le, h3.ge]
    · -- `R ≤ ℓ χ_{R₀}`
      rw [ellH_eq_rpow hμ hapos]
      simp only [Real.rpow_neg hT.le]
      rw [← div_eq_mul_inv]
      rw [show a v / (μ * (a v) ^ 3) ^ (163 / 323 : ℝ) * Submission.BoseGases.chiR0
          = (a v * Submission.BoseGases.chiR0) / (μ * (a v) ^ 3) ^ (163 / 323 : ℝ) from by
        ring]
      by_cases hR : R ≤ 0
      · have hpostv : (0 : ℝ) < (a v * Submission.BoseGases.chiR0)
            / (μ * (a v) ^ 3) ^ (163 / 323 : ℝ) := by positivity
        linarith
      · have hR0 : 0 < R := lt_of_not_ge hR
        rw [le_div_iff₀ (Real.rpow_pos_of_pos hT _)]
        have h2 : a v * Submission.BoseGases.chiR0 / max R 1
            ≤ a v * Submission.BoseGases.chiR0 / R :=
          div_le_div_of_nonneg_left (by positivity) hR0 (le_max_left _ _)
        have h3 : R * ((a v * Submission.BoseGases.chiR0) / R)
            = a v * Submission.BoseGases.chiR0 := by field_simp
        have h4 : R * (μ * (a v) ^ 3) ^ (163 / 323 : ℝ)
            ≤ R * ((a v * Submission.BoseGases.chiR0) / max R 1) :=
          mul_le_mul_of_nonneg_left p5 hR0.le
        have h5 : R * ((a v * Submission.BoseGases.chiR0) / max R 1)
            ≤ R * ((a v * Submission.BoseGases.chiR0) / R) :=
          mul_le_mul_of_nonneg_left h2 hR0.le
        linarith [h4, h5, h3.le, h3.ge]
    · -- `(dil v μ)^{3/323} ≤ 1/2`
      rw [show Work.BoseFixR.dil v μ = μ * (a v) ^ 3 from rfl]
      exact p7
    · -- `K_L √(μa) · K_H a ≤ 1/16`
      have hKHa : (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat
          = a v * (μ * (a v) ^ 3) ^ (-(549 / 1292 : ℝ)) := by
        rw [hKH, haScat, mul_comm]
      have hsqrt : Real.sqrt ((honE v h fc fu HM μ).mu * (honE v h fc fu HM μ).aScat)
          = (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) / (a v) := by
        rw [hmu, haScat]
        have h1 : μ * (a v) = (μ * (a v) ^ 3) / (a v) ^ 2 := by field_simp
        rw [h1, Real.sqrt_div (by positivity),
          show Real.sqrt ((a v) ^ 2) = a v from Real.sqrt_sq hapos.le, Real.sqrt_eq_rpow]
      rw [hKL, hsqrt, hKHa]
      have hL : (μ * (a v) ^ 3) ^ (-(21 / 646 : ℝ))
            * ((μ * (a v) ^ 3) ^ (1 / 2 : ℝ) / (a v))
            * (a v * (μ * (a v) ^ 3) ^ (-(549 / 1292 : ℝ)))
          = (μ * (a v) ^ 3) ^ (-(21 / 646 : ℝ))
            * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) * (μ * (a v) ^ 3) ^ (-(549 / 1292 : ℝ)) := by
        field_simp
      rw [hL]
      have hpow : (μ * (a v) ^ 3) ^ (-(21 / 646 : ℝ)) * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)
            * (μ * (a v) ^ 3) ^ (-(549 / 1292 : ℝ))
          = (μ * (a v) ^ 3) ^ (55 / 1292 : ℝ) := by
        rw [← Real.rpow_add hT, ← Real.rpow_add hT]
        congr 1
        norm_num
      rw [hpow]
      exact p10
    · -- `K_H a / (s ℓ) ≤ 1/32`
      have hslA : (honE v h fc fu HM μ).s * (ellH v μ)
          = a v * (μ * (a v) ^ 3) ^ (-(162 / 323 : ℝ)) := by
        rw [hs, ellH_eq_rpow hμ hapos]
        rw [show (μ * (a v) ^ 3) ^ (1 / 323 : ℝ)
              * (a v * (μ * (a v) ^ 3) ^ (-(163 / 323 : ℝ)))
            = a v * ((μ * (a v) ^ 3) ^ (1 / 323 : ℝ)
              * (μ * (a v) ^ 3) ^ (-(163 / 323 : ℝ))) from by ring]
        rw [← Real.rpow_add hT]
        congr 1
        norm_num
      have hKHa : (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat
          = a v * (μ * (a v) ^ 3) ^ (-(549 / 1292 : ℝ)) := by
        rw [hKH, haScat, mul_comm]
      rw [hellE, hKHa, hslA]
      have hL : a v * (μ * (a v) ^ 3) ^ (-(549 / 1292 : ℝ))
            / (a v * (μ * (a v) ^ 3) ^ (-(162 / 323 : ℝ)))
          = (μ * (a v) ^ 3) ^ (-(549 / 1292 : ℝ))
            / (μ * (a v) ^ 3) ^ (-(162 / 323 : ℝ)) := by
        field_simp
      rw [hL]
      have hgoal2 : (μ * (a v) ^ 3) ^ (-(549 / 1292 : ℝ))
            / (μ * (a v) ^ 3) ^ (-(162 / 323 : ℝ)) ≤ 1 / 32 := by
        rw [div_eq_mul_inv, ← Real.rpow_neg hT.le]
        rw [← Real.rpow_add hT]
        rw [show (-(549 / 1292 : ℝ) + -(-(162 / 323 : ℝ))) = 99 / 1292 from by norm_num]
        exact p11
      exact hgoal2
  · -- the `τ̃`-Lipschitz régime: `(2 d s ℓ)⁻¹ ≤ (1/4)(4K_Ha)⁻¹`
    intro HM hN μ hμ hε
    have hKH : (honE v h fc fu HM μ).KH = (μ * (a v) ^ 3) ^ (-(549 / 1292 : ℝ)) :=
      honE_KH_eq hμ hapos
    have haScat : (honE v h fc fu HM μ).aScat = a v := rfl
    have hellE : (honE v h fc fu HM μ).ell = ellH v μ := by
      rw [ellH, if_pos (Work.BoseBox.sideAt_pos hμ hapos)]
      rfl
    have hT : (0 : ℝ) < μ * (a v) ^ 3 := mul_pos hμ (pow_pos hapos 3)
    have hε' : μ * (a v) ^ 3
        ≤ min 1 (min b2 (min b4 (min b5 (min b7 (min b10 (min b11 (min b12 b13))))))) := hε
    have e12 : μ * (a v) ^ 3 ≤ b12 :=
      le_trans hε' (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _) (min_le_left _ _))))))))
    have e13 : μ * (a v) ^ 3 ≤ b13 :=
      le_trans hε' (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _) (min_le_right _ _))))))))
    have p12 : (μ * (a v) ^ 3) ^ (75 / 1292 : ℝ) ≤ 1 / 8 :=
      rpow_le_of_le_rpow hT (by norm_num) (by norm_num) e12
    have p13 : (μ * (a v) ^ 3) ^ (549 / 1292 : ℝ) ≤ a v :=
      rpow_le_of_le_rpow hT hapos (by norm_num) e13
    rw [honE_d_eq, honE_s_eq, hellE, ellH_eq_rpow hμ hapos, hKH, haScat]
    -- `(2 t^{6/323} t^{1/323} (a t^{-163/323}))⁻¹ ≤ (1/4) (4 t^{-549/1292} a)⁻¹`
    have h8 : (8 : ℝ) ≤ (μ * (a v) ^ 3) ^ (-(75 / 1292) : ℝ) := by
      rw [Real.rpow_neg hT.le]
      have h1 : (1 : ℝ) / (1 / 8) ≤ 1 / (μ * (a v) ^ 3) ^ (75 / 1292 : ℝ) :=
        one_div_le_one_div_of_le (Real.rpow_pos_of_pos hT _) p12
      simpa using h1
    have hcong : (1 / 4 : ℝ) * (4 * (μ * (a v) ^ 3) ^ (-(549 / 1292) : ℝ) * a v)⁻¹
        = (4 * (4 * (μ * (a v) ^ 3) ^ (-(549 / 1292) : ℝ) * a v))⁻¹ := by
      rw [mul_inv, mul_inv]
      ring
    rw [hcong]
    rw [inv_le_inv₀ (by positivity) (by positivity)]
    have hexp1 : (μ * (a v) ^ 3) ^ (6 / 323 : ℝ) * (μ * (a v) ^ 3) ^ (1 / 323 : ℝ)
        = (μ * (a v) ^ 3) ^ (7 / 323 : ℝ) := by
      rw [← Real.rpow_add hT]; norm_num
    have hexp2 : (μ * (a v) ^ 3) ^ (7 / 323 : ℝ) * (μ * (a v) ^ 3) ^ (-(163 / 323) : ℝ)
        = (μ * (a v) ^ 3) ^ (-(156 / 323) : ℝ) := by
      rw [← Real.rpow_add hT]; norm_num
    have hexp3 : (μ * (a v) ^ 3) ^ (-(156 / 323) : ℝ)
        = (μ * (a v) ^ 3) ^ (-(549 / 1292) : ℝ)
          * (μ * (a v) ^ 3) ^ (-(75 / 1292) : ℝ) := by
      rw [← Real.rpow_add hT]; norm_num
    have hX : 0 < (μ * (a v) ^ 3) ^ (-(549 / 1292) : ℝ) := Real.rpow_pos_of_pos hT _
    have hstep : 8 * (μ * (a v) ^ 3) ^ (-(549 / 1292) : ℝ)
        ≤ (μ * (a v) ^ 3) ^ (-(549 / 1292) : ℝ)
          * (μ * (a v) ^ 3) ^ (-(75 / 1292) : ℝ) := by
      have hh := mul_le_mul_of_nonneg_left h8 hX.le
      linarith [hh]
    calc 4 * (4 * (μ * (a v) ^ 3) ^ (-(549 / 1292) : ℝ) * a v)
        = 16 * a v * (μ * (a v) ^ 3) ^ (-(549 / 1292) : ℝ) := by ring
      _ = 2 * a v * (8 * (μ * (a v) ^ 3) ^ (-(549 / 1292) : ℝ)) := by ring
      _ ≤ 2 * a v * ((μ * (a v) ^ 3) ^ (-(549 / 1292) : ℝ)
            * (μ * (a v) ^ 3) ^ (-(75 / 1292) : ℝ)) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = 2 * a v * (μ * (a v) ^ 3) ^ (-(156 / 323) : ℝ) := by rw [← hexp3]
      _ = 2 * a v * ((μ * (a v) ^ 3) ^ (7 / 323 : ℝ)
            * (μ * (a v) ^ 3) ^ (-(163 / 323) : ℝ)) := by rw [← hexp2]
      _ = 2 * a v * ((μ * (a v) ^ 3) ^ (6 / 323 : ℝ)
            * (μ * (a v) ^ 3) ^ (1 / 323 : ℝ)
            * (μ * (a v) ^ 3) ^ (-(163 / 323) : ℝ)) := by rw [← hexp1]
      _ = 2 * (μ * (a v) ^ 3) ^ (6 / 323 : ℝ) * (μ * (a v) ^ 3) ^ (1 / 323 : ℝ)
            * (a v * (μ * (a v) ^ 3) ^ (-(163 / 323) : ℝ)) := by ring
  · -- the régime row `K_H a ≥ 1`: `t^{549/1292} ≤ a v`
    intro HM hN μ hμ hε
    have hKH : (honE v h fc fu HM μ).KH = (μ * (a v) ^ 3) ^ (-(549 / 1292 : ℝ)) :=
      honE_KH_eq hμ hapos
    have haScat : (honE v h fc fu HM μ).aScat = a v := rfl
    have hT : (0 : ℝ) < μ * (a v) ^ 3 := mul_pos hμ (pow_pos hapos 3)
    have hε' : μ * (a v) ^ 3
        ≤ min 1 (min b2 (min b4 (min b5 (min b7 (min b10 (min b11 (min b12 b13))))))) := hε
    have e13 : μ * (a v) ^ 3 ≤ b13 :=
      le_trans hε' (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _) (min_le_right _ _))))))))
    have p13 : (μ * (a v) ^ 3) ^ (549 / 1292 : ℝ) ≤ a v :=
      rpow_le_of_le_rpow hT hapos (by norm_num) e13
    rw [hKH, haScat, Real.rpow_neg hT.le]
    rw [show ((μ * (a v) ^ 3) ^ (549 / 1292 : ℝ))⁻¹ * a v
        = a v / (μ * (a v) ^ 3) ^ (549 / 1292 : ℝ) from by
      rw [div_eq_mul_inv]; ring]
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hT _)]
    simpa using p13

end Work.BoseGateFS
