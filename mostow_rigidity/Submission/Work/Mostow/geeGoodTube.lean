import Mathlib
import Submission.Work.Mostow.geodDeps
import Submission.Work.Mostow.tubeIneq
import Submission.Work.Mostow.tubeMeasure_ball2
import Submission.Work.Mostow.resStd_hom_discrete
import Submission.Work.Mostow.thinStrataGap
import Submission.Work.Mostow.centralizer_acts_fermi
import Submission.Work.Mostow.centralizer_mem_SetStabStd
import Submission.Work.Mostow.geeArithFull

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal

/-! ## Helper: discreteness passes to subsets -/

private lemma gee_isDiscrete_subset {X : Type*} [TopologicalSpace X] {s t : Set X}
    (ht : IsDiscrete t) (h : s ⊆ t) : IsDiscrete s := by
  rw [isDiscrete_iff_nhdsNE] at ht ⊢
  intro x hx
  have hle : nhdsWithin x ({x}ᶜ) ⊓ Filter.principal s ≤
      nhdsWithin x ({x}ᶜ) ⊓ Filter.principal t :=
    inf_le_inf le_rfl (Filter.principal_mono.mpr h)
  rw [ht x (h hx)] at hle
  exact le_bot_iff.mp hle

/-! **Tube arithmetic at the standard stratum (the "good case" of the strata gap).**

Route.  Take `η₁ > 0`, `Cn > 0` from `Work.Mostow.tubeIneq`
(`Submission/Work/Mostow/tubeIneq.lean`) and put `κ := η₁ / (2 * Real.sinh 2)`.  Given `Λ, D, R` with
`rotN R ≤ κ ≤ 1`, set `ρ := Real.arsinh (η₁ / (2 * rotN R)) - 1 ≥ 1`, which gives
`2 * Real.sinh (ρ+1) * rotN R ≤ η₁`.  A fundamental domain `DY` of
`ΓY := Subgroup.closure (resStd k m '' (centralizer {blk k m 1 R} ⊓ Λ))` exists by
`Work.Mostow.exists_fundamentalDomain_gen` (`Submission/Work/Mostow/thinStrataGap.lean`); its
discreteness is `Work.Mostow.resStd_hom_discrete` and it lives in `PO k 1`, so `hCovk` gives
`volH k DY ≥ ofReal v`.  Combine `Work.Mostow.tubeIneq` (the covering bound, whose kernel set is
`{c // c ∈ Λ ∧ c ∈ centralizer {blk k m 1 R} ∧ resStd k m c = 1}`) with
`Work.Mostow.tubeMeasure_ball2`
(`tubeMeasure k m (closedBall 0 ρ) ≥ ofReal (c₁ * Real.exp ((k+m-1) * ρ))`) and with the supplied
kernel bound `|K| ≤ ofReal (CK * (rotN R) ^ (-(m:ℝ)/2))`.  Since
`Real.exp ρ ≥ Real.exp (-1) * (η₁ / (2 * rotN R))` and `rotN R ≤ 1`, this yields
`ofReal (c * (rotN R) ^ (-α)) ≤ volH (k+m) D` for some `c, α > 0`; any `α ≤ (k+m-1) - m/2` works,
e.g. `α = 1`, because `2 ≤ k, 1 ≤ m` give `(k+m-1) - m/2 ≥ 3/2`.  `c` may depend on `CK, k, m`;
`CK` is a parameter (the conclusion must not force `c` to be independent of `CK`, since the tube
bound only gives `c ∝ 1/CK`). -/
theorem geeGoodTube (k m : ℕ) (hAk : Submission.Mostow.POActionProp k)
    (hIk : Submission.Mostow.HypIsometryProp k)
    (hA : Submission.Mostow.POActionProp (k + m)) (hI : Submission.Mostow.HypIsometryProp (k + m))
    (hCovk : Submission.Mostow.CovolLB k) (hk : 2 ≤ k) (hm : 1 ≤ m) :
    ∀ CK : ℝ, 0 < CK → ∃ c α κ : ℝ, 0 < c ∧ 0 < α ∧ 0 < κ ∧ κ ≤ 1 ∧
      ∀ (Λ : Subgroup (PO (k + m) 1)) (D : Set (E (k + m))) (R : E m ≃ₗᵢ[ℝ] E m),
        IsDiscrete (Λ : Set (PO (k + m) 1)) →
        IsFundamentalDomain Λ D (volH (k + m)) →
        blk k m 1 R ∈ Λ → (∀ w : E m, R w = w → w = 0) →
        0 < rotN R → rotN R ≤ κ →
        (Nat.card {c : PO (k + m) 1 // c ∈ Λ ∧ c ∈ Subgroup.centralizer {blk k m 1 R} ∧
            resStd k m c = 1} : ENNReal) ≤ ENNReal.ofReal (CK * (rotN R) ^ (-(m : ℝ) / 2)) →
        ENNReal.ofReal (c * (rotN R) ^ (-α)) ≤ volH (k + m) D := by
  intro CK hCK
  obtain ⟨η₁, hη₁, Cn, hCn, htubeI⟩ := tubeIneq k m hAk hIk hA hI
  obtain ⟨v, hv, hCov⟩ := hCovk
  obtain ⟨c₁, c₂, hc₁, hc₂, hball⟩ := tubeMeasure_ball2 k m hm (by omega : 2 ≤ k + m)
  set N : ℕ := k + m - 1 with hNdef
  have hNcast : ((k + m : ℕ) - 1 : ℝ) = (N : ℝ) := by
    rw [hNdef]; push_cast [Nat.cast_sub (by omega : 1 ≤ k + m)]; ring
  have hNge : 1 + (m : ℝ) / 2 ≤ (N : ℝ) := by
    rw [hNcast.symm]
    have h1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
    have h2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    push_cast [Nat.cast_sub (by omega : 1 ≤ k + m)]
    linarith
  have hsinh2 : 0 < Real.sinh 2 := Real.sinh_pos_iff.mpr (by norm_num)
  have hkm2 : 2 ≤ k + m := by omega
  have hcpos : (0 : ℝ) < v * c₁ * Real.exp (-(N : ℝ)) * η₁ ^ N / (Cn * CK) :=
    div_pos (mul_pos (mul_pos (mul_pos hv hc₁) (Real.exp_pos _)) (pow_pos hη₁ N))
      (mul_pos hCn hCK)
  refine ⟨v * c₁ * Real.exp (-(N : ℝ)) * η₁ ^ N / (Cn * CK), 1,
    min 1 (η₁ / (2 * Real.sinh 2)), hcpos, one_pos, lt_min one_pos (by positivity),
    min_le_left _ _, ?_⟩
  intro Λ D R hdisc hD hb hRnfix hθpos hθκ hKcard
  -- ### the stratum stabiliser and the restricted lattice
  let Cc : Subgroup (PO (k + m) 1) :=
    Subgroup.centralizer ({blk k m 1 R} : Set (PO (k + m) 1)) ⊓ Λ
  let ΓY : Subgroup (PO k 1) :=
    Subgroup.closure (resStd k m '' (Cc : Set (PO (k + m) 1)))
  have hCcdisc : IsDiscrete (SetLike.coe Cc) :=
    gee_isDiscrete_subset hdisc (fun x hx => (Subgroup.mem_inf.mp hx).2)
  have hCcstab : ∀ c ∈ Cc, c ∈ SetStabStd k m := fun c hc =>
    centralizer_mem_SetStabStd k m hAk hIk hA hI R hRnfix c (Subgroup.mem_inf.mp hc).1
  have hΓYdisc : IsDiscrete (SetLike.coe ΓY) :=
    ((resStd_hom_discrete k m hAk hIk hA hI).2 Cc hCcdisc hCcstab).1
  obtain ⟨DY, hDY⟩ := exists_fundamentalDomain_gen k hAk hIk ΓY hΓYdisc
  -- ### the tube radius
  set ρ : ℝ := Real.arsinh (η₁ / (2 * rotN R)) - 1 with hρdef
  have hθκ' : rotN R ≤ η₁ / (2 * Real.sinh 2) := le_trans hθκ (min_le_right _ _)
  have hθle1 : rotN R ≤ 1 := le_trans hθκ (min_le_left _ _)
  have hkey : 2 * Real.sinh 2 * rotN R ≤ η₁ := by
    have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sinh 2)).mp hθκ'
    linarith
  have hxge : Real.sinh 2 ≤ η₁ / (2 * rotN R) :=
    (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * rotN R)).mpr (by linarith)
  have harsinh : (2 : ℝ) ≤ Real.arsinh (η₁ / (2 * rotN R)) :=
    calc (2 : ℝ) = Real.arsinh (Real.sinh 2) := (Real.arsinh_sinh 2).symm
      _ ≤ Real.arsinh (η₁ / (2 * rotN R)) := Real.arsinh_le_arsinh.mpr hxge
  have hρ1 : 1 ≤ ρ := by rw [hρdef]; linarith
  have hρ0 : 0 ≤ ρ := le_trans zero_le_one hρ1
  have htubec : 2 * Real.sinh (ρ + 1) * rotN R ≤ η₁ := by
    have h1 : ρ + 1 = Real.arsinh (η₁ / (2 * rotN R)) := by rw [hρdef]; ring
    rw [h1, Real.sinh_arsinh]
    field_simp
    linarith
  -- ### the covering bound
  have hmain : volH k DY * tubeMeasure k m (Metric.closedBall 0 ρ) ≤
      ENNReal.ofReal Cn *
        (Nat.card {c : PO (k + m) 1 // c ∈ Λ ∧ c ∈ Subgroup.centralizer {blk k m 1 R} ∧
          resStd k m c = 1} : ENNReal) * volH (k + m) D :=
    htubeI Λ D hdisc hD R hb hRnfix DY hDY ρ hρ0 htubec
  have hDYlb : ENNReal.ofReal v ≤ volH k DY := hCov ΓY hΓYdisc DY hDY
  have htmLb : ENNReal.ofReal (c₁ * Real.exp ((N : ℝ) * ρ)) ≤
      tubeMeasure k m (Metric.closedBall 0 ρ) := by
    have h := (hball ρ hρ1).1
    rwa [hNcast] at h
  have hstep : ENNReal.ofReal v * ENNReal.ofReal (c₁ * Real.exp ((N : ℝ) * ρ)) ≤
      volH k DY * tubeMeasure k m (Metric.closedBall 0 ρ) :=
    mul_le_mul' hDYlb htmLb
  have hchain : ENNReal.ofReal (v * (c₁ * Real.exp ((N : ℝ) * ρ))) ≤
      ENNReal.ofReal (Cn * (CK * (rotN R) ^ (-(m : ℝ) / 2))) * volH (k + m) D := by
    have h1 : ENNReal.ofReal (v * (c₁ * Real.exp ((N : ℝ) * ρ)))
        = ENNReal.ofReal v * ENNReal.ofReal (c₁ * Real.exp ((N : ℝ) * ρ)) :=
      ENNReal.ofReal_mul (le_of_lt hv)
    have h2 : ENNReal.ofReal Cn * ENNReal.ofReal (CK * (rotN R) ^ (-(m : ℝ) / 2))
        = ENNReal.ofReal (Cn * (CK * (rotN R) ^ (-(m : ℝ) / 2))) :=
      (ENNReal.ofReal_mul (le_of_lt hCn)).symm
    rw [h1, ← h2]
    exact le_trans hstep (le_trans hmain (mul_le_mul' (mul_le_mul' (le_refl _) hKcard) (le_refl _)))
  have hqpos : 0 < Cn * (CK * (rotN R) ^ (-(m : ℝ) / 2)) :=
    mul_pos hCn (mul_pos hCK (Real.rpow_pos_of_pos hθpos _))
  have hpq : ENNReal.ofReal ((v * (c₁ * Real.exp ((N : ℝ) * ρ))) /
        (Cn * (CK * (rotN R) ^ (-(m : ℝ) / 2)))) ≤ volH (k + m) D := by
    rw [ENNReal.ofReal_div_of_pos hqpos]
    refine (ENNReal.div_le_iff (ne_of_gt (ENNReal.ofReal_pos.mpr hqpos))
      ENNReal.ofReal_ne_top).mpr ?_
    calc ENNReal.ofReal (v * (c₁ * Real.exp ((N : ℝ) * ρ)))
        ≤ ENNReal.ofReal (Cn * (CK * (rotN R) ^ (-(m : ℝ) / 2))) * volH (k + m) D := hchain
      _ = volH (k + m) D * ENNReal.ofReal (Cn * (CK * (rotN R) ^ (-(m : ℝ) / 2))) := mul_comm _ _
  have harith : (v * c₁ * Real.exp (-(N : ℝ)) * η₁ ^ N / (Cn * CK)) * (rotN R) ^ (-1 : ℝ)
      ≤ (v * (c₁ * Real.exp ((N : ℝ) * ρ))) / (Cn * (CK * (rotN R) ^ (-(m : ℝ) / 2))) :=
    geeArithFull N m v c₁ η₁ Cn CK (rotN R) ρ hv hc₁ hη₁ hCn hCK hθpos hθle1 hNge hρdef
  exact le_trans (ENNReal.ofReal_le_ofReal harith) hpq

end Work.Mostow
