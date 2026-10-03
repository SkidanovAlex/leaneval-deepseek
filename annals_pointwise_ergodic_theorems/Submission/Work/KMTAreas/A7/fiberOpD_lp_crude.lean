import Mathlib
import Submission.Work.KMTAreas.A7.SmallFibreDefs
import Submission.Work.KMTAreas.A7.cw_etaCut_decay
import Submission.Work.KMTAreas.A7.eLpNorm_lattice_conv_le

namespace Work.KMTAreas.A7

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

/-! ## Elementary prerequisites -/

/-- The lattice majorant `∑_{j : ℤ} 1/(1+|j|)²` is summable. -/
private lemma summable_one_div_sq_int_priv :
    Summable (fun j : ℤ => 1 / (1 + |(j : ℝ)|) ^ 2) := by
  have hnat : Summable (fun n : ℕ => 1 / (1 + (n : ℝ)) ^ 2) := by
    have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num : (1 : ℕ) < 2)
    have h2 := h.comp_injective (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) Nat.succ_injective
    have h3 : (fun n : ℕ => (fun m : ℕ => 1 / (m : ℝ) ^ 2) (Nat.succ n))
        = fun n : ℕ => 1 / (1 + (n : ℝ)) ^ 2 := by
      funext n
      simp [Nat.cast_add, Nat.cast_one, add_comm]
    rwa [Function.comp_def, h3] at h2
  have hnat' : Summable (fun n : ℕ => 1 / (1 + |((n : ℤ) : ℝ)|) ^ 2) := by
    simpa using hnat
  have hneg' : Summable (fun n : ℕ => 1 / (1 + |((-(↑n + 1) : ℤ) : ℝ)|) ^ 2) := by
    have h2 := (summable_nat_add_iff 1).mpr hnat
    refine h2.congr (fun n => ?_)
    have hcast : ((-(↑n + 1) : ℤ) : ℝ) = -((n : ℝ) + 1) := by push_cast; ring
    rw [hcast, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
    simp [Nat.cast_add, Nat.cast_one]
  exact Summable.of_nat_of_neg_add_one hnat' hneg'

/-- The exact-height arithmetic character is bounded by the cardinality of its frequency set
(every character has modulus one). -/
private lemma norm_arithCharD_le_card (ρ : ℝ) (l : ℕ) (y : ℤ) :
    ‖arithCharD ρ l y‖ ≤ ((diffFreqs ρ l).card : ℝ) := by
  calc ‖arithCharD ρ l y‖ ≤ ∑ α ∈ diffFreqs ρ l, ‖fourier (T := 1) y α‖ := norm_sum_le _ _
    _ = ∑ _α ∈ diffFreqs ρ l, (1 : ℝ) := by
        refine Finset.sum_congr rfl (fun α _ => ?_)
        rw [fourier_apply]
        exact Circle.norm_coe _
    _ = ((diffFreqs ρ l).card : ℝ) := by simp

/- **The crude (kernel-`ℓ¹`/Young) fibre bound**, valid for bounded height and bounded `k`; it is
the fallback of the §7 fibre estimate in the finitely many cases where the good-arcs hypothesis
`GoodMajorArcs ρ Cρ l (-(2u))` of `Work.KMTAreas.A7.fiberOpCum_lp_goodArcs` fails.

`fiberOpD ρ l m n₀ v x = ∑'_j arithCharD ρ l (n₀-j) · cw m j · v(x-j)` is convolution with the
kernel `κ(j) = arithCharD ρ l (n₀-j)·cw m j`, and `‖κ‖_{ℓ¹} ≤ #(diffFreqs ρ l) · ∑_j ‖cw m j‖`
(because `|fourier y α| ≤ 1`).  For `l ≤ L₀` the first factor is a constant depending on
`(ρ, L₀)`, and for `|k| ≤ K₀` the second is bounded by taking the maximum of the constants of
`Work.KMTAreas.A7.cw_etaCut_decay k` over the finite set `k ∈ [-K₀,K₀]`.  Young's inequality on
`ℤ` with `Measure.count` (`Work.KMTAreas.A7.eLpNorm_lattice_conv_le` at `q = 1`) then gives the
bound (`eLpNorm v = ⊤` is trivial since `C > 0`). -/
theorem fiberOpD_lp_crude {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {p : ENNReal} (hp : 1 < p)
    (htp : p < ⊤) (L₀ : ℕ) (K₀ : ℤ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l : ℕ), l ≤ L₀ → ∀ (k : ℤ), |k| ≤ K₀ →
      ∀ (n₀ : ℤ) (v : ℤ → ℂ),
        MeasureTheory.eLpNorm
            (fun x : ℤ => Work.KMTAreas.A7.fiberOpD ρ l
              (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k) n₀ v x)
            p MeasureTheory.Measure.count
          ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm v p MeasureTheory.Measure.count := by
  classical
  -- the decay constants supplied by the cutoff theory
  have hdec : ∀ k : ℤ, ∃ C : ℝ, 0 < C ∧ ∀ j : ℤ,
      ‖cw (etaCut Work.KMTContract.kmtEta k) j‖ ≤ C / (1 + |(j : ℝ)|) ^ 2 :=
    fun k => cw_etaCut_decay k
  let D : ℤ → ℝ := fun k => Classical.choose (hdec k)
  have hDpos : ∀ k : ℤ, 0 < D k := fun k => (Classical.choose_spec (hdec k)).1
  have hDb : ∀ (k j : ℤ), ‖cw (etaCut Work.KMTContract.kmtEta k) j‖
        ≤ D k / (1 + |(j : ℝ)|) ^ 2 := fun k => (Classical.choose_spec (hdec k)).2
  -- the cardinality bound for the exact-height arithmetic frequency sets
  have hcard : ∀ l : ℕ, l ≤ L₀ → (diffFreqs ρ l).card ≤ (iwArithFreqs ρ L₀).card := by
    intro l hl
    refine Finset.card_le_card (fun α hα => ?_)
    rw [diffFreqs] at hα
    by_cases h0 : l = 0
    · rw [if_pos h0] at hα
      exact iwArithFreqs_mono hρ hρ1 (Nat.zero_le L₀) hα
    · rw [if_neg h0] at hα
      exact iwArithFreqs_mono hρ hρ1 hl (Finset.mem_sdiff.mp hα).1
  set A : ℝ := ((iwArithFreqs ρ L₀).card : ℝ) with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  -- the uniform bound on the decay constants over `|k| ≤ K₀`
  set Dm : ℝ := max 1 (∑ k ∈ Finset.Icc (-K₀) K₀, D k) with hDm
  have hDm1 : 1 ≤ Dm := by rw [hDm]; exact le_max_left _ _
  have hDmle : ∀ k : ℤ, |k| ≤ K₀ → D k ≤ Dm := by
    intro k hk
    have hmem : k ∈ Finset.Icc (-K₀) K₀ := by
      rw [Finset.mem_Icc]; exact abs_le.mp hk
    have hs := Finset.single_le_sum (s := Finset.Icc (-K₀) K₀) (f := D)
      (fun i _ => le_of_lt (hDpos i)) hmem
    exact hs.trans (by rw [hDm]; exact le_max_right _ _)
  -- the lattice majorant
  have hS : Summable (fun j : ℤ => 1 / (1 + |(j : ℝ)|) ^ 2) := summable_one_div_sq_int_priv
  set Ls : ℝ := ∑' j : ℤ, 1 / (1 + |(j : ℝ)|) ^ 2 with hLs
  set Cc : ℝ := max 1 (A * Dm * Ls) with hCc
  have hCcpos : 0 < Cc := lt_of_lt_of_le one_pos (by rw [hCc]; exact le_max_left _ _)
  refine ⟨Cc, hCcpos, ?_⟩
  intro l hl k hk n₀ v
  have hp_ne_top : p ≠ ⊤ := ne_of_lt htp
  set pr : ℝ := p.toReal with hprdef
  have hp_eq : ENNReal.ofReal pr = p := by
    rw [hprdef]; exact ENNReal.ofReal_toReal hp_ne_top
  have hpr1 : 1 ≤ pr := by
    have h1 : (1 : ENNReal).toReal < pr := by
      rw [hprdef, ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_ne_top]
      simpa using hp
    simpa using h1.le
  -- the convolution kernel
  set c : ℤ → ℂ := fun j =>
    arithCharD ρ l (n₀ - j) * cw (etaCut Work.KMTContract.kmtEta k) j with hc
  have hchar : ∀ y : ℤ, ‖arithCharD ρ l y‖ ≤ A := by
    intro y
    exact (norm_arithCharD_le_card ρ l y).trans (by rw [hA]; exact_mod_cast hcard l hl)
  have hpt : ∀ j : ℤ, ‖c j‖ ≤ A * Dm * (1 / (1 + |(j : ℝ)|) ^ 2) := by
    intro j
    have hdm : D k / (1 + |(j : ℝ)|) ^ 2 ≤ Dm / (1 + |(j : ℝ)|) ^ 2 :=
      div_le_div_of_nonneg_right (hDmle k hk) (by positivity)
    have hcj : c j = arithCharD ρ l (n₀ - j) * cw (etaCut Work.KMTContract.kmtEta k) j := by
      rw [hc]
    calc ‖c j‖ = ‖arithCharD ρ l (n₀ - j)‖
            * ‖cw (etaCut Work.KMTContract.kmtEta k) j‖ := by rw [hcj, norm_mul]
      _ ≤ A * (Dm / (1 + |(j : ℝ)|) ^ 2) :=
          mul_le_mul (hchar _) ((hDb k j).trans hdm) (norm_nonneg _) hA0
      _ = A * Dm * (1 / (1 + |(j : ℝ)|) ^ 2) := by ring
  have hMaj : Summable (fun j : ℤ => A * Dm * (1 / (1 + |(j : ℝ)|) ^ 2)) :=
    hS.mul_left (A * Dm)
  have hsumc : Summable (fun j : ℤ => ‖c j‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hpt hMaj
  have hbound : (∑' j : ℤ, ‖c j‖) ≤ A * Dm * Ls := by
    calc (∑' j : ℤ, ‖c j‖) ≤ ∑' j : ℤ, A * Dm * (1 / (1 + |(j : ℝ)|) ^ 2) :=
          Summable.tsum_le_tsum hpt hsumc hMaj
      _ = A * Dm * Ls := by rw [tsum_mul_left, hLs]
  have hleCc : A * Dm * Ls ≤ Cc := by rw [hCc]; exact le_max_right _ _
  have hker : (∑' j : ℤ, ENNReal.ofReal ‖c j‖) ≤ ENNReal.ofReal Cc := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => norm_nonneg _) hsumc]
    exact ENNReal.ofReal_le_ofReal (hbound.trans hleCc)
  -- Young's inequality on the lattice
  have hY := eLpNorm_lattice_conv_le (p := pr) hpr1 1 le_rfl c v
  rw [hp_eq] at hY
  have hLHS : (fun x : ℤ => fiberOpD ρ l
        (etaCut Work.KMTContract.kmtEta k) n₀ v x)
      = fun n : ℤ => ∑' j : ℤ, c j * v (n - j * ((1 : ℕ) : ℤ)) := by
    funext x
    rw [fiberOpD]
    refine tsum_congr (fun j => ?_)
    simp only [hc, Nat.cast_one, mul_one]
  rw [hLHS]
  exact hY.trans (mul_le_mul_left hker _)

end Work.KMTAreas.A7
