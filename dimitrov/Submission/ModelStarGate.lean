import Mathlib
import Submission.ModelStarFamily
import Submission.ModelStarFamilyDir
import Submission.ModelStarExists
import Submission.ModelStarDominating
import Submission.Step3Bridge
import Submission.Step3Decomp
import Submission.Commons.Analysis.Complex.exists_strictMono_unit_enum

/-!
# ModelStarGate -- the assembly of the general-s "(EX)" input from the KKM output

This module reduces the whole "dominating model star" route to the single
topological input `Submission.ModelStarExists.KKM` (the KKM lemma to which the
fleet's `Commons.Topology.Simplex.kkm_standardSimplex` is being proved):

  * `gap`, `weight`: the cyclic gap vector of an increasing enumeration `θ` of a
    unit Finset `u` and the corresponding (FORCED) weight vector `r`, with
    `0 < r`, `Σ r = 1` (`sum_gap` is the telescoping `Σ gap = 2π`), and
    `r (j+1) = (θ (j+1) − θ j)/(2π)` -- the hypothesis of
    `ModelStarFamilyDir.direction_rotation`;
  * `unit_case_of_kkm`: **the unit case of `Step3.sym_maximality`** follows from
    `KKM`.  Its proof: enumerate `u` (`Commons.Analysis.Complex.exists_strictMono_unit_enum`),
    apply `ModelStarExists.exists_tip_all_ge_of_kkm` to the weight vector, read off
    the positive gaps (`gap_pos_of_tips`), build the model star with junctions
    `eAngle (arcLo g k)`, use `ArcGood` + `arcGood_direction` for the spike
    directions and `direction_rotation` to identify them with `ρ⁻¹ · u`, and
    finish with `ModelStarDominating.rootSeq_one_le_inv_theta_of_modelStar` plus
    the rotation invariance `Step3Decomp.rootSeq_rotation`.
-/

noncomputable section

open scoped Real BigOperators Topology
open Set Filter

namespace Submission.ModelStarGate

open Submission.ModelStarFamily
open Submission.ModelStarFamilyDir (arcLo_mono arcLo_injective arcLo_lt_two_pi Theta direction_rotation arcGood_direction_of)
open Submission.ModelStarBoundary2 (eAngle)

variable {s : ℕ}

/-- The unwrapped angle sequence of an enumeration `θ` of the circle: the
`s`-periodic continuation whose period is `2π`. -/
def unwrap (θ : Fin s → ℝ) (hs : 0 < s) (i : ℕ) : ℝ :=
  θ ⟨i % s, Nat.mod_lt i hs⟩ + 2 * Real.pi * ((i / s : ℕ) : ℝ)

lemma unwrap_period (θ : Fin s → ℝ) (hs : 0 < s) (i : ℕ) :
    unwrap θ hs (i + s) = unwrap θ hs i + 2 * Real.pi := by
  have hidx : (⟨(i + s) % s, Nat.mod_lt (i + s) hs⟩ : Fin s) = ⟨i % s, Nat.mod_lt i hs⟩ :=
    Fin.ext (Nat.add_mod_right i s)
  unfold unwrap
  rw [hidx, Nat.add_div_right i hs]
  push_cast
  ring

lemma unwrap_of_lt {θ : Fin s → ℝ} (hs : 0 < s) {i : ℕ} (hi : i < s) :
    unwrap θ hs i = θ ⟨i, hi⟩ := by
  have hidx : (⟨i % s, Nat.mod_lt i hs⟩ : Fin s) = ⟨i, hi⟩ :=
    Fin.ext (Nat.mod_eq_of_lt hi)
  unfold unwrap
  rw [hidx, Nat.div_eq_of_lt hi]
  ring

/-- The FORCED weight vector: `r j := (Θ (j+s) − Θ (j+s−1)) / 2π`, i.e. the
angular gap from the `(j−1)`-st prescribed direction to the `j`-th, divided by
`2π`. -/
def weight (θ : Fin s → ℝ) (hs : 0 < s) (j : Fin s) : ℝ :=
  (unwrap θ hs (j.val + s) - unwrap θ hs (j.val + s - 1)) / (2 * Real.pi)

lemma weight_zero (θ : Fin s → ℝ) (hs : 0 < s) :
    weight θ hs ⟨0, hs⟩ = (θ ⟨0, hs⟩ + 2 * Real.pi - θ ⟨s - 1, by omega⟩) / (2 * Real.pi) := by
  have h1 : unwrap θ hs s = θ ⟨0, hs⟩ + 2 * Real.pi := by
    have h := unwrap_period θ hs 0
    rw [zero_add] at h
    rw [h, unwrap_of_lt hs hs]
  have h2 : unwrap θ hs (s - 1) = θ ⟨s - 1, by omega⟩ := unwrap_of_lt hs (by omega)
  unfold weight
  rw [zero_add, h1, h2]

lemma weight_of_pos {θ : Fin s → ℝ} (hs : 0 < s) {j : Fin s} (hj : 0 < j.val) :
    weight θ hs j = (θ j - θ ⟨j.val - 1, by have := j.isLt; omega⟩) / (2 * Real.pi) := by
  have hle : j.val - 1 + s = j.val + s - 1 := by have := j.isLt; omega
  have h1 : unwrap θ hs (j.val + s) = θ j + 2 * Real.pi := by
    have h := unwrap_period θ hs j.val
    rw [unwrap_of_lt hs j.isLt] at h
    rw [h]
  have h2 : unwrap θ hs (j.val + s - 1) = θ ⟨j.val - 1, by have := j.isLt; omega⟩ + 2 * Real.pi := by
    rw [← hle, unwrap_period]
    rw [unwrap_of_lt hs (by have := j.isLt; omega)]
  unfold weight
  rw [h1, h2]
  ring

lemma weight_pos {θ : Fin s → ℝ} (hmono : StrictMono θ) (hlo : ∀ k, 0 ≤ θ k)
    (hhi : ∀ k, θ k < 2 * Real.pi) (hs : 0 < s) (j : Fin s) : 0 < weight θ hs j := by
  rcases eq_or_lt_of_le (Nat.zero_le j.val) with h | h
  · have hj : j = ⟨0, hs⟩ := Fin.ext h.symm
    rw [hj, weight_zero θ hs]
    have h1 := hhi ⟨s - 1, by omega⟩
    have h2 := hlo ⟨0, hs⟩
    exact div_pos (by linarith [Real.pi_pos]) (by positivity)
  · rw [weight_of_pos hs h]
    have hlt : (⟨j.val - 1, by have := j.isLt; omega⟩ : Fin s) < j := by
      simp only [Fin.lt_def]
      have := j.isLt
      omega
    exact div_pos (by linarith [hmono hlt]) (by positivity)

lemma sum_weight (θ : Fin s → ℝ) (hs : 0 < s) : ∑ j : Fin s, weight θ hs j = 1 := by
  have hshift : (∑ j : Fin s, (unwrap θ hs (j.val + s) - unwrap θ hs (j.val + s - 1)))
      = ∑ i ∈ Finset.range s,
          ((fun k => unwrap θ hs (k + s - 1)) (i + 1) - (fun k => unwrap θ hs (k + s - 1)) i) := by
    rw [Fin.sum_univ_eq_sum_range
      (fun i => unwrap θ hs (i + s) - unwrap θ hs (i + s - 1)) s]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only []
    have h : i + 1 + s - 1 = i + s := by omega
    rw [h]
  have htel : (∑ i ∈ Finset.range s,
      ((fun k => unwrap θ hs (k + s - 1)) (i + 1) - (fun k => unwrap θ hs (k + s - 1)) i))
      = unwrap θ hs (s + s - 1) - unwrap θ hs (0 + s - 1) :=
    Finset.sum_range_sub (fun k => unwrap θ hs (k + s - 1)) s
  have hper : unwrap θ hs (s + s - 1) = unwrap θ hs (s - 1) + 2 * Real.pi := by
    rw [show s + s - 1 = (s - 1) + s by omega, unwrap_period]
  have hzero : unwrap θ hs (0 + s - 1) = unwrap θ hs (s - 1) := by rw [zero_add]
  have hnum : (∑ j : Fin s, (unwrap θ hs (j.val + s) - unwrap θ hs (j.val + s - 1)))
      = 2 * Real.pi := by
    rw [hshift, htel, hper, hzero]
    ring
  have h : (∑ j : Fin s, weight θ hs j)
      = (∑ j : Fin s, (unwrap θ hs (j.val + s) - unwrap θ hs (j.val + s - 1))) / (2 * Real.pi) := by
    simp only [weight]
    rw [Finset.sum_div]
  rw [h, hnum]
  field_simp

/-- The direction gap of consecutive prescribed angles equals `2π` times the
weight: the hypothesis of `ModelStarFamilyDir.direction_rotation`. -/
lemma weight_gap {θ : Fin s → ℝ} (hs : 0 < s) {j : Fin s} (hj : j.val + 1 < s) :
    θ ⟨j.val + 1, hj⟩ - θ j = 2 * Real.pi * weight θ hs ⟨j.val + 1, hj⟩ := by
  have h1 : unwrap θ hs (j.val + 1 + s) = θ ⟨j.val + 1, hj⟩ + 2 * Real.pi := by
    rw [unwrap_period θ hs (j.val + 1), unwrap_of_lt hs hj]
  have h2 : unwrap θ hs (j.val + 1 + s - 1) = θ j + 2 * Real.pi := by
    have h : j.val + 1 + s - 1 = j.val + s := by omega
    rw [h, unwrap_period θ hs j.val, unwrap_of_lt hs j.isLt]
  have h3 : (⟨j.val + 1, hj⟩ : Fin s).val + s = j.val + 1 + s := rfl
  have h4 : (⟨j.val + 1, hj⟩ : Fin s).val + s - 1 = j.val + 1 + s - 1 := rfl
  unfold weight
  rw [h3, h4, h1, h2]
  field_simp
  ring

/-! ## The assembly -/

/-- **The unit case of `Step3.sym_maximality` from the KKM lemma.** -/
theorem unit_case_of_kkm (hkkm : Submission.ModelStarExists.KKM)
    (u : Finset ℂ) (hu : ∀ w ∈ u, ‖w‖ = 1) (hcard : 1 ≤ u.card) :
    Filter.limsup (Submission.Step3Bridge.rootSeq u 1) Filter.atTop
      ≤ (4 : ℝ) ^ (-1 / (u.card : ℝ)) := by
  classical
  have hs : 0 < u.card := by omega
  have hne : u.Nonempty := Finset.card_pos.mp hs
  set c : ℝ := (4 : ℝ) ^ (1 / (u.card : ℝ)) with hcdef
  have hc0 : 0 ≤ c := by rw [hcdef]; exact Real.rpow_nonneg (by norm_num) _
  have hcpos : 0 < c := by rw [hcdef]; exact Real.rpow_pos_of_pos (by norm_num) _
  -- (1) enumerate the directions
  obtain ⟨θ, hθmono, hθrange, -, hθsurj⟩ :=
    Commons.Analysis.Complex.exists_strictMono_unit_enum u hu hne
  have hθlo : ∀ k, 0 ≤ θ k := fun k => (hθrange k).1
  have hθhi : ∀ k, θ k < 2 * Real.pi := fun k => (hθrange k).2
  -- (2) the forced weight vector
  have hr : ∀ k : Fin u.card, 0 < weight θ hs k := fun k => weight_pos hθmono hθlo hθhi hs k
  have hsumr : (∑ k : Fin u.card, weight θ hs k) = 1 := sum_weight θ hs
  -- (3) the KKM output
  obtain ⟨g, hgsimp, hgtips⟩ :=
    Submission.ModelStarExists.exists_tip_all_ge_of_kkm hkkm hs (weight θ hs) hr hsumr
  have hsumg : (∑ k : Fin u.card, g k) = 1 := hgsimp.2
  have hgp : ∀ k : Fin u.card, 0 < g k := fun k =>
    Submission.ModelStarExists.gap_pos_of_tips hs (weight θ hs) hr hsumr hgtips k
  have hg0 : ∀ k : Fin u.card, 0 ≤ g k := fun k => (hgp k).le
  -- (4) the model star data
  have hφmono : Monotone (arcLo g) := arcLo_mono hg0
  have hφinj : Function.Injective (arcLo g) := arcLo_injective hgp
  have hφlo : ∀ k, 0 ≤ arcLo g k := fun k => junc_nonneg hg0 k
  have hφhi : ∀ k, arcLo g k < 2 * Real.pi := fun k => arcLo_lt_two_pi hgp hsumg k
  -- (5) the per-arc `ArcGood` data
  choose U M hAG using fun j : Fin u.card =>
    Submission.ModelStarImageSeg.exists_arcGood (s := u.card) hs
      (z₀ := fun k => eAngle (arcLo g k)) (r := weight θ hs) (φ := arcLo g)
      (fun k => rfl) hφlo hφhi hsumr hφmono hφinj hr j
  -- (6) the arc directions
  have hdir : ∀ j : Fin u.card, U j = eAngle (Theta (weight θ hs) g j) := fun j =>
    arcGood_direction_of hs (weight θ hs) g hr hgp hsumr hsumg j (hAG j)
  -- (7) the rotation matching the prescribed pattern
  set ρ : ℂ := eAngle (θ ⟨0, hs⟩ - Theta (weight θ hs) g ⟨0, hs⟩) with hρdef
  have hrot : ∀ j : Fin u.card, eAngle (θ j) = ρ * U j := by
    intro j
    rw [hdir j]
    exact direction_rotation (weight θ hs) g hs θ
      (fun k hk => weight_gap (θ := θ) hs hk) j
  have hρunit : ‖ρ‖ = 1 := by
    rw [hρdef]
    exact Submission.ModelStarBoundary4.eAngle_norm _
  have hρne : ρ ≠ 0 := by
    intro h; rw [h, norm_zero] at hρunit; norm_num at hρunit
  -- (8) the rotated direction set
  set u₁ : Finset ℂ := u.image (fun w : ℂ => ρ⁻¹ * w) with hu₁def
  have hu₁ : ∀ w ∈ u₁, ‖w‖ = 1 := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨v, hv, rfl⟩
    rw [norm_mul, norm_inv, hρunit, inv_one, one_mul]
    exact hu v hv
  have hu₁card : u₁.card = u.card := by
    rw [hu₁def]
    refine Finset.card_image_of_injOn ?_
    intro a _ b _ hab
    exact mul_left_cancel₀ (inv_ne_zero hρne) hab
  have hu₁ne : u₁.Nonempty := by
    obtain ⟨v, hv⟩ := hne
    exact ⟨ρ⁻¹ * v, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩
  -- (9) the tips dominate the spike length
  have hcM : ∀ j : Fin u.card, c ≤ M j := by
    intro j
    refine le_trans (hgtips j) ?_
    rw [tip_eq_tip_of_mem hg0 j]
    refine csSup_le ⟨rhoG (weight θ hs) g (arcLo g j), arcLo g j,
      left_mem_Icc.mpr (arcLo_le_arcHi hg0 j), rfl⟩ ?_
    rintro y ⟨t, ht, rfl⟩
    have ht' : t ∈ Set.Icc (arcLo g j)
        (Submission.ModelStarImageSeg.nextJunction (arcLo g) hs j) := by
      rw [show Submission.ModelStarImageSeg.nextJunction (arcLo g) hs j
          = Submission.ModelStarImageSeg.nextJunction (junc g) hs j from rfl,
        ← arcHi_eq_nextJunction (g := g) hs hsumg j]
      exact ht
    have h := (hAG j).2.2.2.1 t ht'
    simpa only [rhoG, Submission.ModelStarBoundary3.rho, arcLo, junc] using h
  -- (10) the containment
  have hsub : Step3.dirStar u₁ c
      ⊆ Submission.ModelStarExterior.modelStarImage (fun k => eAngle (arcLo g k))
        (weight θ hs) := by
    intro X hX
    rcases hX with ⟨w, hw, hXseg⟩
    rcases Finset.mem_image.mp hw with ⟨v, hv, rfl⟩
    obtain ⟨j, hj⟩ := hθsurj v hv
    have hwj : ρ⁻¹ * v = U j := by
      have h3 : v = ρ * U j := hj.symm.trans (hrot j)
      rw [h3, ← mul_assoc, inv_mul_cancel₀ hρne, one_mul]
    rw [hwj] at hXseg
    rcases (Submission.XTransfer.mem_segment_zero_iff ((c : ℂ) * U j) X).mp hXseg
      with ⟨t, ht, hXeq⟩
    have htc : t * c ∈ Set.Icc 0 (M j) := by
      refine ⟨mul_nonneg ht.1 hc0, ?_⟩
      calc t * c ≤ 1 * c := mul_le_mul_of_nonneg_right ht.2 hc0
        _ = c := one_mul _
        _ ≤ M j := hcM j
    have hmem := (hAG j).2.2.2.2 (t * c) htc
    rw [hXeq]
    convert hmem using 1
    rw [Complex.real_smul]
    push_cast
    ring
  -- (11) the dominating-model-star bound for the rotated directions
  have hdom := Submission.ModelStarDominating.rootSeq_one_le_inv_theta_of_modelStar
    hu₁ (by rw [hu₁card]; exact hcard) hcpos hs
    (fun k => rfl) (fun k => Submission.ModelStarBoundary4.eAngle_norm _) hr hsumr
    hφmono hφinj hφlo hφhi hsub
  -- (12) rotation invariance
  have heq : ∀ n : ℕ, Submission.Step3Bridge.rootSeq u₁ 1 n
      = Submission.Step3Bridge.rootSeq u 1 n := by
    intro n
    have h := Submission.Step3Decomp.rootSeq_rotation ρ⁻¹ (by
      rw [norm_inv, hρunit, inv_one]) u 1 n
    rw [hu₁def]
    exact h
  have hlim : Filter.limsup (Submission.Step3Bridge.rootSeq u₁ 1) Filter.atTop
      = Filter.limsup (Submission.Step3Bridge.rootSeq u 1) Filter.atTop := by
    refine congrArg (fun f : ℕ → ℝ => Filter.limsup f Filter.atTop) ?_
    funext n
    exact heq n
  have hexp : (1 : ℝ) / c = (4 : ℝ) ^ (-1 / (u.card : ℝ)) := by
    rw [hcdef, one_div, ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 4)]
    ring_nf
  rw [hexp] at hdom
  rw [← hlim]
  exact hdom

end Submission.ModelStarGate
