import Mathlib
import Submission.GM.Interfaces
import Submission.LargeValues.KeyProp
import Submission.Work.GM.S2.Defs
import Submission.Work.GM.S2.hhat_decay
import Submission.Work.GM.S2.log_window1
import Submission.Work.GM.S2.hhat_reflection
import Submission.Work.GM.S2.divisor_bound
import Submission.Work.GM.S2.holder_hb4
import Submission.Work.GM.S2.pair_sum_bound
import Submission.Work.GM.S2.s2_reduction_aux

/-! Guidance from the project lead (the requester):

This is a whole AREA (GM §6: Lemma 6.2 and Prop 6.1 with k = 4), assuming Heath-Brown (`hHB`).
Delegate pieces with request_review + request_lemma under Submission/Work/GM/S2/.
Paper: REFS/GuthMaynard_2405.20552.txt, Section 6 (and Lemma 4.3 in Section 4).

Route: S₂ = 3N³ hhat 0 0 Σ_{t₁,t₂}|Σ_{m≠0} hhat (t₁-t₂) (mN)|² + tiny (terms with t₁ ≠ t₃ die by
separation). Then the reflection (Lemma 6.2) turns Σ_{m≠0} ĥ_t(mN), |t| ∼ MN, into a Dirichlet
polynomial of length ≈ M ≤ T/N = N^{1/5}; Hölder to the 4th power (divisor bound for the
coefficients of the 4th power) and Heath-Brown on the length-M⁴ polynomial give (6.4).

The pieces of this area are: `hhat_decay` (Lemma 4.3), `log_window1` (Fourier-in-log
representation of the weight `ψ = w²`, for the `1/u`-weighted form used by the reflection),
`hhat_reflection` (GM Lemma 6.2, in the form `|Σ_{m≤Y} ĥ_t(mN)| ≤ C ∫ ‖ĝ₁(ξ)‖
(1+|t+2πξ|)^{-1/2} ‖Σ_{m≤Y} m^{i(t+2πξ)}‖ dξ`), `holder_hb4` (Hölder k = 4 + divisor bound +
Heath-Brown on the pair sum), `pair_sum_bound` (the dyadic reflection classes + the previous
two, giving the pair sum bound), and `s2_reduction` (`S₂ = 3N³ ĥ_0(0) Σ|Σ_m ĥ|² + O(T^{-10})`).
-/

open Complex Finset MeasureTheory
open scoped BigOperators Topology
set_option autoImplicit false

namespace Work.GM.S2

/-- `Spart 2 N ∅ = 0` (there are no `t`-summands). -/
lemma spart_empty (N : ℕ) : Submission.GM.Spart 2 N (∅ : Finset ℝ) = 0 := by
  unfold Submission.GM.Spart Submission.GM.Iterm
  simp

/-- The final exponent bookkeeping: combining the reduction (`hred`), the pair-sum bound (`hps`)
and the trivial bound for the `T^{-10}` error gives the `S₂Statement` shape. -/
lemma final_arith {ns ms R δ hc P S : ℝ}
    (hns1 : 1 ≤ ns) (hms1 : 1 ≤ ms) (hR1 : 1 ≤ R) (hhc : 0 ≤ hc)
    {Crd Cps : ℝ} (hCrd : 0 < Crd) (hCps : 0 < Cps) (hms10 : ms ^ (-10 : ℝ) ≤ ns ^ (2 + δ))
    (hred : S ≤ Crd * ns ^ 3 * hc * P + ms ^ (-10 : ℝ))
    (hps : P ≤ Cps * ns ^ δ * (R ^ 2 / ns + ms / ns ^ 2 * R ^ ((7:ℝ)/4)
              + R ^ ((29:ℝ)/16) * ms ^ ((1:ℝ)/8) / ns)) :
    S ≤ (Crd * Cps * hc + 2) * ns ^ δ *
          (ns ^ 2 * R ^ 2 + ms * ns * R ^ ((7:ℝ)/4) + ns ^ 2 * R ^ ((29:ℝ)/16) * ms ^ ((1:ℝ)/8)) := by
  have hns0 : 0 < ns := lt_of_lt_of_le one_pos hns1
  have hms0 : 0 < ms := lt_of_lt_of_le one_pos hms1
  have hR0 : 0 ≤ R := le_trans zero_le_one hR1
  have hAid : ns^3 * (R ^ 2 / ns + ms / ns ^ 2 * R ^ ((7:ℝ)/4)
              + R ^ ((29:ℝ)/16) * ms ^ ((1:ℝ)/8) / ns)
      = ns ^ 2 * R ^ 2 + ms * ns * R ^ ((7:ℝ)/4)
              + ns ^ 2 * R ^ ((29:ℝ)/16) * ms ^ ((1:ℝ)/8) := by
    field_simp
  have hBnn : 0 ≤ ns ^ 2 * R ^ 2 + ms * ns * R ^ ((7:ℝ)/4)
              + ns ^ 2 * R ^ ((29:ℝ)/16) * ms ^ ((1:ℝ)/8) := by
    have h1 : 0 ≤ ns^2*R^2 := by positivity
    have h2 : 0 ≤ ms*ns*R^((7:ℝ)/4) := by
      have := Real.rpow_nonneg hR0 ((7:ℝ)/4); positivity
    have h3 : 0 ≤ ns^2*R^((29:ℝ)/16)*ms^((1:ℝ)/8) := by
      have ha := Real.rpow_nonneg hR0 ((29:ℝ)/16)
      have hb := Real.rpow_nonneg hms0.le ((1:ℝ)/8)
      positivity
    linarith
  have hnnδ : 0 ≤ ns ^ δ := Real.rpow_nonneg hns0.le δ
  have hstep : S ≤ (Crd * Cps * hc) * ns ^ δ *
        (ns ^ 2 * R ^ 2 + ms * ns * R ^ ((7:ℝ)/4) + ns ^ 2 * R ^ ((29:ℝ)/16) * ms ^ ((1:ℝ)/8))
      + ms ^ (-10 : ℝ) := by
    refine le_trans hred ?_
    have hmono : Crd * ns^3 * hc * P ≤ Crd * ns^3 * hc *
        (Cps * ns ^ δ * (R ^ 2 / ns + ms / ns ^ 2 * R ^ ((7:ℝ)/4)
              + R ^ ((29:ℝ)/16) * ms ^ ((1:ℝ)/8) / ns)) :=
      mul_le_mul_of_nonneg_left hps (by positivity)
    have heq : Crd * ns ^ 3 * hc * (Cps * ns ^ δ *
          (R ^ 2 / ns + ms / ns ^ 2 * R ^ ((7:ℝ)/4) + R ^ ((29:ℝ)/16) * ms ^ ((1:ℝ)/8) / ns))
        = (Crd * Cps * hc) * ns ^ δ *
          (ns ^ 2 * R ^ 2 + ms * ns * R ^ ((7:ℝ)/4) + ns ^ 2 * R ^ ((29:ℝ)/16) * ms ^ ((1:ℝ)/8)) := by
      have hsym : ns ^ 2 * R ^ 2 + ms * ns * R ^ ((7:ℝ)/4) + ns ^ 2 * R ^ ((29:ℝ)/16) * ms ^ ((1:ℝ)/8)
          = ns ^ 3 * (R ^ 2 / ns + ms / ns ^ 2 * R ^ ((7:ℝ)/4)
              + R ^ ((29:ℝ)/16) * ms ^ ((1:ℝ)/8) / ns) := hAid.symm
      rw [hsym]
      ring_nf
    calc Crd * ns ^ 3 * hc * P + ms ^ (-10 : ℝ)
        ≤ Crd * ns ^ 3 * hc * (Cps * ns ^ δ * (R ^ 2 / ns + ms / ns ^ 2 * R ^ ((7:ℝ)/4)
              + R ^ ((29:ℝ)/16) * ms ^ ((1:ℝ)/8) / ns)) + ms ^ (-10 : ℝ) :=
          add_le_add hmono le_rfl
      _ = (Crd * Cps * hc) * ns ^ δ *
          (ns ^ 2 * R ^ 2 + ms * ns * R ^ ((7:ℝ)/4) + ns ^ 2 * R ^ ((29:ℝ)/16) * ms ^ ((1:ℝ)/8))
          + ms ^ (-10 : ℝ) := by rw [heq]
  have hBge : ms ^ (-10 : ℝ) ≤ ns ^ δ * (ns ^ 2 * R ^ 2 + ms * ns * R ^ ((7:ℝ)/4)
              + ns ^ 2 * R ^ ((29:ℝ)/16) * ms ^ ((1:ℝ)/8)) := by
    have hR2 : 1 ≤ R^2 := by nlinarith
    have h1 : ns^2 ≤ ns^2*R^2 := by nlinarith [sq_nonneg ns]
    have h5 : 0 ≤ ms*ns*R^((7:ℝ)/4) := by
      have := Real.rpow_nonneg hR0 ((7:ℝ)/4); positivity
    have h6 : 0 ≤ ns^2*R^((29:ℝ)/16)*ms^((1:ℝ)/8) := by
      have ha := Real.rpow_nonneg hR0 ((29:ℝ)/16)
      have hb := Real.rpow_nonneg hms0.le ((1:ℝ)/8); positivity
    have hm10 : ms ^ (-10 : ℝ) ≤ ns ^ δ * ns ^ 2 := by
      have h := hms10
      rw [add_comm, Real.rpow_add hns0] at h
      simpa using h
    have hstep2 : ns ^ δ * ns ^ 2 ≤ ns ^ δ * (ns^2*R^2 + ms*ns*R^((7:ℝ)/4)
        + ns^2*R^((29:ℝ)/16)*ms^((1:ℝ)/8)) := by
      apply mul_le_mul_of_nonneg_left _ hnnδ
      linarith
    linarith
  have hfin : (Crd * Cps * hc) * ns ^ δ *
        (ns ^ 2 * R ^ 2 + ms * ns * R ^ ((7:ℝ)/4) + ns ^ 2 * R ^ ((29:ℝ)/16) * ms ^ ((1:ℝ)/8))
        + ms ^ (-10 : ℝ)
      ≤ (Crd * Cps * hc + 2) * ns ^ δ *
        (ns ^ 2 * R ^ 2 + ms * ns * R ^ ((7:ℝ)/4) + ns ^ 2 * R ^ ((29:ℝ)/16) * ms ^ ((1:ℝ)/8)) := by
    have h : ms ^ (-10 : ℝ) ≤ ns ^ δ * (ns ^ 2 * R ^ 2 + ms * ns * R ^ ((7:ℝ)/4)
              + ns ^ 2 * R ^ ((29:ℝ)/16) * ms ^ ((1:ℝ)/8)) := hBge
    have hCnn : 0 ≤ Crd * Cps * hc := by positivity
    nlinarith [hBnn, hnnδ, h, hCnn]
  linarith [hstep, hfin]

/-- GM §6 (Lemma 6.2, Prop 6.1 with k = 4), assuming Heath-Brown; see
`Submission/GM/Interfaces.lean`. -/
theorem s2_of_hb (hHB : Submission.GM.HBStatement) : Submission.GM.S2Statement := by
  intro ε δ hε hδ
  obtain ⟨⟨hxi, ht⟩, _htail⟩ := hhat_decay
  obtain ⟨hinv, hint, hga, hgf⟩ := log_window1
  have hDiv : ∀ δ' : ℝ, 0 < δ' → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ((n.divisors.card : ℝ)) ≤ C * (n : ℝ) ^ δ' := divisor_bound
  obtain ⟨Crd, hCrdpos, Nrd, hred⟩ := s2_reduction_aux hxi ht ε hε
  obtain ⟨Cr, hCrpos, hrefl⟩ := hhat_reflection hinv hint hgf
  have hhb := holder_hb4 hHB hDiv
  obtain ⟨Cps, hCpspos, Nps, hps⟩ :=
    pair_sum_bound hhb ⟨Cr, hCrpos, hrefl⟩ hxi hga hgf ε δ hε hδ
  refine ⟨Crd * Cps * ‖Submission.GM.hhat 0 0‖ + 2, by positivity, max Nps (max Nrd 1), ?_⟩
  intro N hN W hW hsep
  have hNps : Nps ≤ N := le_trans (le_max_left _ _) hN
  have hNrd : Nrd ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN)
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN)
  rcases Nat.eq_zero_or_pos W.card with h0 | hpos
  · have hWe : W = ∅ := Finset.card_eq_zero.mp h0
    subst hWe
    rw [spart_empty N, norm_zero]
    have h1 : (0:ℝ) ^ ((7:ℝ)/4) = 0 := Real.zero_rpow (by norm_num)
    have h2 : (0:ℝ) ^ ((29:ℝ)/16) = 0 := Real.zero_rpow (by norm_num)
    rw [Finset.card_empty, Nat.cast_zero, h1, h2]
    simp
  · set ns : ℝ := (N:ℝ) with hnsdef
    set ms : ℝ := Submission.LargeValues.M N with hmsdef
    set R : ℝ := (W.card : ℝ) with hRdef
    have hns1 : 1 ≤ ns := by rw [hnsdef]; exact_mod_cast hN1
    have hms1 : 1 ≤ ms := by rw [hmsdef]; exact Submission.LargeValues.M_ge_one hN1
    have hR1 : 1 ≤ R := by rw [hRdef]; exact_mod_cast hpos
    have hms10 : ms ^ (-10 : ℝ) ≤ ns ^ (2 + δ) := by
      have hM : Submission.LargeValues.M N = (N:ℝ) ^ ((6:ℝ)/5) := rfl
      rw [hmsdef, hnsdef, hM]
      have hmult : ((6:ℝ)/5) * (-10:ℝ) = -12 := by norm_num
      rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ (N:ℝ)), hmult]
      apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1)
      linarith
    have hred' : ‖Submission.GM.Spart 2 N W‖ ≤
        Crd * ns ^ 3 * ‖Submission.GM.hhat 0 0‖ *
          (∑ t₁ ∈ W, ∑ t₂ ∈ W,
            ‖∑' (m : {m : ℤ // m ≠ 0}), Submission.GM.hhat (t₁ - t₂) ((m : ℝ) * (N : ℝ))‖ ^ 2)
        + ms ^ (-10 : ℝ) := by
      have h := hred N hNrd W hW hsep
      rw [hnsdef, hmsdef]
      exact h
    have hps' : (∑ t₁ ∈ W, ∑ t₂ ∈ W,
            ‖∑' (m : {m : ℤ // m ≠ 0}), Submission.GM.hhat (t₁ - t₂) ((m : ℝ) * (N : ℝ))‖ ^ 2)
        ≤ Cps * ns ^ δ * (R ^ 2 / ns + ms / ns ^ 2 * R ^ ((7:ℝ)/4)
            + R ^ ((29:ℝ)/16) * ms ^ ((1:ℝ)/8) / ns) := by
      have h := hps N hNps W hW hsep
      rw [hnsdef, hmsdef, hRdef]
      exact h
    have hmain := final_arith hns1 hms1 hR1 (norm_nonneg _) hCrdpos hCpspos hms10 hred' hps'
    rw [hnsdef, hmsdef, hRdef] at hmain
    exact hmain

end Work.GM.S2
