import Mathlib
import Submission.Work.Diff.Alg.Pinch.Chat_shift_inclusion_any

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The shift inclusion `R + Iso n ∈ Ĉ(s) → R + 2 • Iso n ∈ Ĉ(s+δ)` with an explicit threshold

`Work.Diff.Alg.Pinch.Chat_shift_inclusion_any` proves the *existential* form: for every `N > 0` and
`s > 0` there is `δ > 0` such that

`R + Iso n ∈ Ĉ(s)`,  `scalAlg R ≤ N`  ⟹  `R + 2 • Iso n ∈ Ĉ(s + δ)`.

Its proof only uses three *explicit* numerical conditions on `δ`, namely (with `M = N + n(n-1)`,
`Ca = n/2 + 1`, `K = 1 + 2(n-1)(anyAA n s + Ca)`, `c₀ = min (1/(1+(n-2)(s+1)²)) (4/((n-2)+8(s+1)))`,
`L = (1/2/K)(n-1)c₀` and `D2 = (n-2)C_ric + 1`)

* `δ ≤ n/(4·Ca·M)`,
* `δ ≤ 1/(2·K·C_EF·C_T·M)`,
* `δ·M·D2 ≤ L`,

together with `0 < δ ≤ 1`.  This file records the resulting *threshold form*: any `δ` satisfying the
three numerical conditions above obeys the shift inclusion.  This is the shape needed when the
thresholds are assembled by hand from external data (a single `min` of all thresholds is hard to
use): the caller produces `δ` from its own estimates and only has to check the three inequalities.

The proof is the body of `Chat_shift_inclusion_any` with the explicit `min`-definition of `δ` (and
the derivation of the three conditions from it) replaced by the corresponding hypotheses.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg Work.Diff.Alg.Pinch Work.Diff.Alg.Pinch.ChatAny

variable {n : ℕ}

set_option maxHeartbeats 2000000

theorem chat_shift_threshold (n : ℕ) (hn : 2 ≤ n) (N : ℝ) (hN : 0 < N)
    {C_EF C_T C_ric : ℝ} (hC_EFpos : 0 ≤ C_EF) (hC_Tpos : 0 ≤ C_T) (hC_ricpos : 0 ≤ C_ric)
    (hC_EF : ∀ D : Submission.Diff.Alg.Curv4 n, Submission.Diff.Alg.IsAlgCurv D →
      ∀ x y z w : Fin n → ℝ,
        |Work.Diff.Alg.Pinch.Cone.EF D x y z w| ≤
          C_EF * ‖D‖ * Work.Diff.Alg.Pinch.Cone.EF (Submission.Diff.Alg.Iso n) x y z w)
    (hC_T : ∀ S : Submission.Diff.Alg.Curv4 n, Submission.Diff.Alg.IsAlgCurv S →
      Submission.Diff.Alg.InPIC2 S →
        ‖Work.Diff.Alg.Pinch.knProd (Work.Diff.Alg.Pinch.ric0 S) (Work.Diff.Alg.Pinch.id2 n)‖ ≤
          C_T * Submission.Diff.Alg.scalAlg S)
    (hC_ric : ∀ S : Submission.Diff.Alg.Curv4 n, Submission.Diff.Alg.IsAlgCurv S →
      Submission.Diff.Alg.InPIC2 S → ∀ v : Fin n → ℝ,
        |∑ i, ∑ j, Work.Diff.Alg.Pinch.ric0 S i j * v i * v j| ≤
          C_ric * Submission.Diff.Alg.scalAlg S * (∑ i, v i * v i))
    {s δ : ℝ} (hs : 0 < s) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hδCa : δ ≤ (n : ℝ) / (4 * ((n : ℝ) / 2 + 1) * (N + (n : ℝ) * ((n : ℝ) - 1))))
    (hδK : δ ≤ 1 / (2 * (1 + 2 * ((n : ℝ) - 1) *
        (Work.Diff.Alg.Pinch.ChatAny.anyAA n s + ((n : ℝ) / 2 + 1)))
        * C_EF * C_T * (N + (n : ℝ) * ((n : ℝ) - 1))))
    (hδL : δ * (N + (n : ℝ) * ((n : ℝ) - 1)) * (((n : ℝ) - 2) * C_ric + 1)
      ≤ 1 / 2 / (1 + 2 * ((n : ℝ) - 1) * (Work.Diff.Alg.Pinch.ChatAny.anyAA n s + ((n : ℝ) / 2 + 1)))
        * ((n : ℝ) - 1)
        * min (1 / (1 + ((n : ℝ) - 2) * (s + 1) ^ 2)) (4 / (((n : ℝ) - 2) + 8 * (s + 1)))) :
    ∀ R : Submission.Diff.Alg.Curv4 n,
      R + Submission.Diff.Alg.Iso n ∈ Work.Diff.Alg.Pinch.Chat n s →
      Submission.Diff.Alg.scalAlg R ≤ N →
      R + (2 : ℝ) • Submission.Diff.Alg.Iso n ∈ Work.Diff.Alg.Pinch.Chat n (s + δ) := by
  -- the numerical data, exactly as in `Chat_shift_inclusion_any`
  set M : ℝ := N + (n : ℝ) * ((n : ℝ) - 1) with hMdef
  set Ca : ℝ := (n : ℝ) / 2 + 1 with hCadef
  set K : ℝ := 1 + 2 * ((n : ℝ) - 1) * (anyAA n s + Ca) with hKdef
  set c0 : ℝ := min (1 / (1 + ((n : ℝ) - 2) * (s + 1) ^ 2))
    (4 / (((n : ℝ) - 2) + 8 * (s + 1))) with hc0def
  set L : ℝ := (1 / 2 / K) * ((n : ℝ) - 1) * c0 with hLdef
  set D2 : ℝ := ((n : ℝ) - 2) * C_ric + 1 with hD2def
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hc : (0 : ℝ) ≤ (n : ℝ) - 2 := chat_c_nonneg hn
  have hMpos : 0 < M := by
    rw [hMdef]
    have : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) := by positivity
    linarith
  have hCapos : 0 < Ca := by rw [hCadef]; positivity
  have hK1 : 1 ≤ K := by
    rw [hKdef]
    have h1 : 0 ≤ (n : ℝ) - 1 := le_of_lt hn1
    have h2 : 0 ≤ anyAA n s + Ca := by
      have := ChatAny.anyAA_nonneg n hn hs.le
      linarith [hCapos]
    nlinarith
  have hc0pos : 0 < c0 := by
    rw [hc0def]
    exact lt_min (one_div_pos.mpr (by nlinarith [hc, sq_nonneg (s + 1)]))
      (div_pos (by norm_num) (by nlinarith [hc, hs]))
  have hLpos : 0 < L := by
    rw [hLdef]
    have h1 : 0 < 1 / 2 / K := div_pos (by norm_num) (lt_of_lt_of_le one_pos hK1)
    have h2 : (0 : ℝ) < (n : ℝ) - 1 := hn1
    positivity
  have hD2pos : 0 < D2 := by
    rw [hD2def]
    have h1 : 0 ≤ ((n : ℝ) - 2) * C_ric := mul_nonneg hc hC_ricpos
    linarith
  -- strict positivity of the constants in the denominator of the `C_EF`-estimate: if one of them
  -- vanished, the threshold `hδK` would read `δ ≤ 0`, contradicting `0 < δ`
  have hCEF : 0 < C_EF := by
    rcases eq_or_lt_of_le hC_EFpos with h | h
    · exfalso
      have hden0 : 2 * K * C_EF * C_T * M = 0 := by rw [← h]; ring
      have hk := hδK
      rw [hden0] at hk
      simp only [div_zero] at hk
      linarith
    · exact h
  have hCT : 0 < C_T := by
    rcases eq_or_lt_of_le hC_Tpos with h | h
    · exfalso
      have hden0 : 2 * K * C_EF * C_T * M = 0 := by rw [← h]; ring
      have hk := hδK
      rw [hden0] at hk
      simp only [div_zero] at hk
      linarith
    · exact h
  have hdenpos : 0 < 2 * K * C_EF * C_T * M := by
    have h1 : (0 : ℝ) < 2 * K := by linarith
    exact mul_pos (mul_pos (mul_pos h1 hCEF) hCT) hMpos
  have hδ0le : 0 ≤ δ := le_of_lt hδ0
  -- the two consequences of the threshold hypotheses that the argument actually uses
  have hδK' : δ * C_EF * C_T * M ≤ 1 / 2 / K := by
    rw [le_div_iff₀ (lt_of_lt_of_le one_pos hK1)]
    have h4 : δ * (2 * K * C_EF * C_T * M) ≤ 1 := by
      have h5 : (1 / (2 * K * C_EF * C_T * M)) * (2 * K * C_EF * C_T * M) = 1 :=
        div_mul_cancel₀ 1 (ne_of_gt hdenpos)
      have h6 : δ * (2 * K * C_EF * C_T * M)
          ≤ (1 / (2 * K * C_EF * C_T * M)) * (2 * K * C_EF * C_T * M) :=
        mul_le_mul_of_nonneg_right hδK hdenpos.le
      linarith [h6, h5]
    have h7 : δ * C_EF * C_T * M * K * 2 = δ * (2 * K * C_EF * C_T * M) := by ring
    linarith [h4, h7.le, h7.ge]
  have hδL' : δ * M * D2 ≤ L := hδL
  intro R hXR hRscal
  -- step 1: extract `S` with `X = ell a b S`
  have hXmem : R + Iso n ∈ Ccone (n := n) (anyAA n s) (anyBB s) (anyPP n s) := by
    rw [← ChatAny.chat_eq_cone_param n]
    exact hXR
  obtain ⟨S, hS, hXS⟩ := hXmem
  have hSalg : IsAlgCurv S := hS.1
  have hSpic : InPIC2 S := hS.2.1
  have hSric : RicPinch (anyPP n s) S := hS.2.2
  have hσ0 : 0 ≤ scalAlg S := (inPIC2_metric_basic n).2.2 S hSpic
  have hnis : (n : ℝ) ≠ 0 := ne_of_gt hn0
  -- step 2: `scalAlg S ≤ M`
  have hXscal : scalAlg (R + Iso n) = (1 + 2 * ((n : ℝ) - 1) * anyAA n s) * scalAlg S := by
    rw [← hXS]
    exact scalAlg_ell_of_ne n (anyAA n s) (anyBB s) hnis hSalg
  have hXscalR : scalAlg (R + Iso n) = scalAlg R + (n : ℝ) * ((n : ℝ) - 1) := by
    rw [scalAlg_add, scalAlg_iso]
  have hXM : scalAlg (R + Iso n) ≤ M := by
    rw [hXscalR, hMdef]; linarith
  have ha1 : 1 ≤ 1 + 2 * ((n : ℝ) - 1) * anyAA n s := by
    have h1 : 0 ≤ (n : ℝ) - 1 := le_of_lt hn1
    have h2 := ChatAny.anyAA_nonneg n hn hs.le
    nlinarith
  have hσM : scalAlg S ≤ M := by
    calc scalAlg S ≤ (1 + 2 * ((n : ℝ) - 1) * anyAA n s) * scalAlg S :=
          le_mul_of_one_le_left hσ0 ha1
      _ = scalAlg (R + Iso n) := hXscal.symm
      _ ≤ M := hXM
  -- step 3: the parameter bounds
  obtain ⟨hbb1, hbb2⟩ := ChatAny.anyBB_shift (s := s) (δ := δ) hδ0le
  obtain ⟨haa1, haa2⟩ := ChatAny.anyAA_shift n hn hs hδ0le
  obtain ⟨hpp1, hpp2⟩ := ChatAny.anyPP_shift_le n hn hs hδ0le
  have hc0le : c0 ≤ 1 - anyPP n (s + δ) := by
    rw [hc0def]
    exact ChatAny.one_sub_anyPP_ge n hn hs hδ0le hδ1
  have hP'lt : anyPP n (s + δ) < 1 := ChatAny.anyPP_shift_lt_one n hn hs hδ0le hδ1
  have hb0' : (0 : ℝ) ≤ anyBB (s + δ) := le_min (by linarith : (0 : ℝ) ≤ s + δ) (by norm_num)
  have hden1ge : 1 ≤ 1 + ((n : ℝ) - 2) * anyBB (s + δ) := by
    have := mul_nonneg hc hb0'
    linarith
  have hden1 : 0 < 1 + ((n : ℝ) - 2) * anyBB (s + δ) := by linarith [hden1ge]
  have hden2 : 0 < 1 + 2 * ((n : ℝ) - 1) * anyAA n (s + δ) := by
    have ha' : 0 ≤ anyAA n (s + δ) := ChatAny.anyAA_nonneg n hn (by linarith : (0 : ℝ) ≤ s + δ)
    have h1 : 0 ≤ (n : ℝ) - 1 := le_of_lt hn1
    have h2 : 0 ≤ 2 * ((n : ℝ) - 1) * anyAA n (s + δ) := by positivity
    linarith
  have hden2le : 1 + 2 * ((n : ℝ) - 1) * anyAA n (s + δ) ≤ K := by
    have h := ChatAny.one_add_two_anyAA_le n hn hs hδ0le hδ1
    rw [hKdef, hCadef]
    exact h
  have haa2' : anyAA n (s + δ) - anyAA n s ≤ Ca * δ := by
    rw [hCadef]
    exact haa2
  -- `γ₁`
  have hg1abs : |chSg1 n (anyBB s) (anyBB (s + δ))|
      = (anyBB (s + δ) - anyBB s) / (1 + ((n : ℝ) - 2) * anyBB (s + δ)) := by
    rw [chSg1, abs_div, abs_of_pos hden1,
      abs_of_nonpos (by linarith : anyBB s - anyBB (s + δ) ≤ 0), neg_sub]
  have hg1le : |chSg1 n (anyBB s) (anyBB (s + δ))| ≤ δ := by
    rw [hg1abs, div_le_iff₀ hden1]
    have h1 : δ * 1 ≤ δ * (1 + ((n : ℝ) - 2) * anyBB (s + δ)) :=
      mul_le_mul_of_nonneg_left hden1ge hδ0le
    linarith [hbb2, h1]
  -- the numerator of `γ₂`
  have hnum : (1 : ℝ) / 2 ≤ 1 + 2 * scalAlg S * (anyAA n s - anyAA n (s + δ)) / (n : ℝ) := by
    have hσa : scalAlg S * (anyAA n (s + δ) - anyAA n s) ≤ (n : ℝ) / 4 := by
      have h1 : scalAlg S * (anyAA n (s + δ) - anyAA n s) ≤ M * (Ca * δ) :=
        mul_le_mul hσM haa2' (sub_nonneg.mpr haa1) hMpos.le
      have h3 : M * (Ca * δ) ≤ M * (Ca * (n / (4 * Ca * M))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hδCa hCapos.le) hMpos.le
      have h4 : M * (Ca * (n / (4 * Ca * M))) = (n : ℝ) / 4 := by
        field_simp
      linarith [h1, h3, h4.le]
    have hkey : -(1 / 2) * (n : ℝ) ≤ 2 * scalAlg S * (anyAA n s - anyAA n (s + δ)) := by
      have h2 : 2 * scalAlg S * (anyAA n s - anyAA n (s + δ))
          = -(2 * (scalAlg S * (anyAA n (s + δ) - anyAA n s))) := by ring
      rw [h2]
      linarith [hσa]
    have hkey2 : -(1 / 2) ≤ 2 * scalAlg S * (anyAA n s - anyAA n (s + δ)) / (n : ℝ) := by
      rw [le_div_iff₀ hn0]
      linarith [hkey]
    linarith [hkey2]
  have hγ₂ge : (1 : ℝ) / 2 / K ≤ chSg2 n (anyAA n s) (anyAA n (s + δ)) 1 (scalAlg S) := by
    rw [chSg2, div_le_div_iff₀ (lt_of_lt_of_le one_pos hK1) hden2]
    have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK1
    calc (1 / 2) * (1 + 2 * ((n : ℝ) - 1) * anyAA n (s + δ))
        ≤ (1 / 2) * K := mul_le_mul_of_nonneg_left hden2le (by norm_num)
      _ ≤ (1 + 2 * scalAlg S * (anyAA n s - anyAA n (s + δ)) / (n : ℝ)) * K :=
          mul_le_mul_of_nonneg_right hnum hK0
  -- the two room inequalities
  have hroom1 : |chSg1 n (anyBB s) (anyBB (s + δ))| * C_EF * C_T * scalAlg S
      ≤ chSg2 n (anyAA n s) (anyAA n (s + δ)) 1 (scalAlg S) := by
    have h1 : |chSg1 n (anyBB s) (anyBB (s + δ))| * C_EF * C_T * scalAlg S
        ≤ δ * C_EF * C_T * M := by
      have h2 : |chSg1 n (anyBB s) (anyBB (s + δ))| * C_EF ≤ δ * C_EF :=
        mul_le_mul_of_nonneg_right hg1le hC_EFpos
      have h3 : |chSg1 n (anyBB s) (anyBB (s + δ))| * C_EF * C_T ≤ δ * C_EF * C_T :=
        mul_le_mul_of_nonneg_right h2 hC_Tpos
      exact mul_le_mul h3 hσM hσ0 (by positivity)
    linarith [h1, hδK', hγ₂ge]
  have hroom2 : chSg2 n (anyAA n s) (anyAA n (s + δ)) 1 (scalAlg S) * ((n : ℝ) - 1)
        * (1 - anyPP n (s + δ))
      ≥ |chSg1 n (anyBB s) (anyBB (s + δ))| * ((n : ℝ) - 2) * C_ric * scalAlg S
        + scalAlg S * (anyPP n (s + δ) - anyPP n s) / (n : ℝ) := by
    have hLHS : L ≤ chSg2 n (anyAA n s) (anyAA n (s + δ)) 1 (scalAlg S) * ((n : ℝ) - 1)
        * (1 - anyPP n (s + δ)) := by
      have h1 : (1 / 2 / K) * ((n : ℝ) - 1) * c0 ≤
          chSg2 n (anyAA n s) (anyAA n (s + δ)) 1 (scalAlg S) * ((n : ℝ) - 1)
            * (1 - anyPP n (s + δ)) := by
        have h1a : (0 : ℝ) ≤ (n : ℝ) - 1 := le_of_lt hn1
        calc (1 / 2 / K) * ((n : ℝ) - 1) * c0
            ≤ chSg2 n (anyAA n s) (anyAA n (s + δ)) 1 (scalAlg S) * ((n : ℝ) - 1) * c0 :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hγ₂ge h1a) hc0pos.le
          _ ≤ chSg2 n (anyAA n s) (anyAA n (s + δ)) 1 (scalAlg S) * ((n : ℝ) - 1)
                * (1 - anyPP n (s + δ)) := by
              refine mul_le_mul_of_nonneg_left hc0le ?_
              exact mul_nonneg (le_trans (le_of_lt (div_pos (by norm_num)
                (lt_of_lt_of_le one_pos hK1))) hγ₂ge) h1a
      have h2 : L = (1 / 2 / K) * ((n : ℝ) - 1) * c0 := by
        rw [hLdef]
      linarith [h1, h2.le]
    have hRHS : |chSg1 n (anyBB s) (anyBB (s + δ))| * ((n : ℝ) - 2) * C_ric * scalAlg S
        + scalAlg S * (anyPP n (s + δ) - anyPP n s) / (n : ℝ) ≤ δ * M * D2 := by
      have h1 : |chSg1 n (anyBB s) (anyBB (s + δ))| * ((n : ℝ) - 2) * C_ric * scalAlg S
          ≤ δ * ((n : ℝ) - 2) * C_ric * M := by
        have h1a : |chSg1 n (anyBB s) (anyBB (s + δ))| * ((n : ℝ) - 2) ≤ δ * ((n : ℝ) - 2) :=
          mul_le_mul_of_nonneg_right hg1le hc
        have h1b : |chSg1 n (anyBB s) (anyBB (s + δ))| * ((n : ℝ) - 2) * C_ric
            ≤ δ * ((n : ℝ) - 2) * C_ric :=
          mul_le_mul_of_nonneg_right h1a hC_ricpos
        exact mul_le_mul h1b hσM hσ0 (by positivity)
      have h2 : scalAlg S * (anyPP n (s + δ) - anyPP n s) / (n : ℝ) ≤ δ * M := by
        rw [div_le_iff₀ hn0]
        have h2a : scalAlg S * (anyPP n (s + δ) - anyPP n s) ≤ M * ((n : ℝ) * δ) :=
          mul_le_mul hσM hpp2 (sub_nonneg.mpr hpp1) hMpos.le
        linarith [h2a]
      have h3 : δ * ((n : ℝ) - 2) * C_ric * M + δ * M = δ * M * D2 := by
        rw [hD2def]; ring
      linarith [h1, h2, h3.le]
    linarith [hLHS, hRHS, hδL']
  -- step 4: apply the core
  have hcore : S + chSg1 n (anyBB s) (anyBB (s + δ)) • knProd (ric0 S) (id2 n)
      + chSg2 n (anyAA n s) (anyAA n (s + δ)) 1 (scalAlg S) • Iso n
      ∈ Dpic (n := n) (anyPP n (s + δ)) :=
    ChatAny.dpic_shift_core n hn hC_EFpos hC_Tpos hC_ricpos hC_EF hC_T hC_ric
      hpp1 hP'lt hSalg hSpic hSric rfl ⟨hroom1, hroom2⟩
  -- step 5: the inverse identity and the conclusion
  have hlinv : linv (anyAA n (s + δ)) (anyBB (s + δ)) (R + Iso n + Iso n)
      = S + chSg1 n (anyBB s) (anyBB (s + δ)) • knProd (ric0 S) (id2 n)
        + chSg2 n (anyAA n s) (anyAA n (s + δ)) 1 (scalAlg S) • Iso n := by
    have ha' : 1 + 2 * ((n : ℝ) - 1) * anyAA n (s + δ) ≠ 0 := ne_of_gt hden2
    have hb' : 1 + ((n : ℝ) - 2) * anyBB (s + δ) ≠ 0 := ne_of_gt hden1
    have h1 := linv_ell_add_smul_Iso n hnis (a := anyAA n s) (b := anyBB s)
      (a' := anyAA n (s + δ)) (b' := anyBB (s + δ)) (t := 1) ha' hb' hSalg
    rw [one_smul, hXS] at h1
    exact h1
  have hXalg : IsAlgCurv (R + Iso n + Iso n) := by
    have hX' : IsAlgCurv (R + Iso n) := by
      rw [← hXS]
      exact ell_isAlgCurv n (anyAA n s) (anyBB s) hSalg
    exact isAlgCurv_add hX' (Iso_algCurv n)
  have ha' : 1 + 2 * ((n : ℝ) - 1) * anyAA n (s + δ) ≠ 0 := ne_of_gt hden2
  have hb' : 1 + ((n : ℝ) - 2) * anyBB (s + δ) ≠ 0 := ne_of_gt hden1
  have hmem : R + Iso n + Iso n ∈ Ccone (n := n) (anyAA n (s + δ)) (anyBB (s + δ))
      (anyPP n (s + δ)) :=
    ⟨linv (anyAA n (s + δ)) (anyBB (s + δ)) (R + Iso n + Iso n), hlinv ▸ hcore,
      ell_linv n ha' hb' hXalg⟩
  have hgoal : R + Iso n + Iso n ∈ Chat n (s + δ) := by
    rw [ChatAny.chat_eq_cone_param n]
    exact hmem
  have h2 : R + (2 : ℝ) • Iso n = R + Iso n + Iso n := by
    rw [show (2 : ℝ) = 1 + 1 from by norm_num, add_smul, one_smul]
    abel
  rw [h2]
  exact hgoal

end Work.Diff.Alg.Pinch
