import Mathlib
import Submission.Work.Diff.Alg.Pinch.Chat_shift_inclusion_any

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The uniform (large-`s`) shift inclusion for the Brendle–Schoen cones `Ĉ(s)`

The pointwise shift inclusion `Chat_shift_inclusion_any` gives, for each fixed `s > 0` and each
level `N`, a `δ(s) > 0` such that

`R + Iso n ∈ Ĉ(s)`, `scalAlg R ≤ N`  ⟹  `R + 2 • Iso n ∈ Ĉ(s + δ(s))`.

The Boehm–Wilking pinching-set machinery needs this with a **single** `δ`, uniform in `s` ranging
over the second branch `s ≥ 1/2` of the family.  This file proves exactly that:

`∃ δ₂ > 0, ∀ δ ∈ (0, δ₂], ∀ s ≥ 1/2, ∀ R, R + Iso n ∈ Ĉ(s) → scalAlg R ≤ N → R + 2 • Iso n ∈ Ĉ(s+δ)`.

## Proof

For `s ≥ 1/2` (and then also for `s + δ ≥ 1/2`) the family is the *single* cone

`Ĉ(s) = ℓ_{s,1/2}(Dpic p(s))`,  `p(s) = 1 - 4/((n-2) + 8s)`,

i.e. the Boehm–Wilking parameter `b = 1/2` is fixed (`ChatAny.chat_eq_cone_param` combined with
the branch identities `anyAA_ge_half`, `anyBB_ge_half`, `anyPP_ge_half`).

Write `X = R + Iso n = ℓ_{s,1/2} S` with `S ∈ Dpic p(s)`, `σ = scalAlg S`, and
`M = N + n(n-1) ≥ scalAlg X = (1 + 2(n-1)s) σ`.  By the Boehm–Wilking inverse identity
(`ChatShift.linv_ell_add_smul_Iso`) the shifted tensor is

`linv_{s+δ,1/2}(X + Iso n) = S + γ₂ • Iso n`,  `γ₂ = (1 - 2σδ/n)/(1 + 2(n-1)(s+δ))`,

the `Ric₀ ∧ id`-term dropping out because `b = b' = 1/2` (`chSg1 n (1/2) (1/2) = 0`).  So
`X + Iso n ∈ Ĉ(s+δ)` reduces to the two scalar "room" inequalities `ChSRoom` of
`ChatShiftDefs`, which are established by `chat_room_half`: with `U = (n-2) + 8s` and
`A = 1 + 2(n-1)s`,

* `1 - 2σδ/n ≥ 1/2` (from `σ n ≤ M` and `12 M δ ≤ n(n-1)`; this is the positivity of `γ₂`), and
* the second room inequality, cleared of denominators, is
  `32 σ δ (A + 2(n-1)δ) ≤ 4(n-1)(1 - 2σδ/n) n U`,
  which follows from `σ n ≤ M`, `12 M δ ≤ n(n-1)`, `δ ≤ 1` and the elementary
  `4(A + 2(n-1)) ≤ 3 n U` (worst case `s = 1/2`, improving as `s → ∞` — this is the uniformity).

The choice `δ₂ = min 1 (n(n-1)/(12M))` therefore works for every `s ≥ 1/2`, with room to spare.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

set_option maxHeartbeats 1000000

/-- In the branch `s ≥ 1/2` the `a`-parameter of the family is `s`. -/
lemma anyAA_ge_half (n : ℕ) (_hn : 2 ≤ n) {s : ℝ} (hs : 1 / 2 ≤ s) : ChatAny.anyAA n s = s := by
  rw [ChatAny.anyAA_eq]
  split_ifs with h
  · rw [le_antisymm h hs, ChatAny.chatA_half]
  · rfl

/-- In the branch `s ≥ 1/2` the `b`-parameter of the family is `1/2`. -/
lemma anyBB_ge_half {s : ℝ} (hs : 1 / 2 ≤ s) : ChatAny.anyBB s = 1 / 2 := by
  rw [ChatAny.anyBB_eq]
  split_ifs with h
  · rw [le_antisymm h hs]
  · rfl

/-- In the branch `s ≥ 1/2` the `p`-parameter of the family is `1 - 4/((n-2) + 8s)`. -/
lemma anyPP_ge_half (n : ℕ) (_hn : 2 ≤ n) {s : ℝ} (hs : 1 / 2 ≤ s) :
    ChatAny.anyPP n s = 1 - 4 / ((n : ℝ) - 2 + 8 * s) := by
  rw [ChatAny.anyPP_eq]
  split_ifs with h
  · rw [le_antisymm h hs, ChatAny.chatP_half]
    norm_num
  · rfl

/-- In the branch `b = b' = 1/2` the `Ric₀ ∧ id`-coefficient of the shift identity vanishes. -/
lemma chSg1_half_half (n : ℕ) : chSg1 n (1 / 2) (1 / 2) = 0 := by
  simp [chSg1]

/-- **The room inequalities in the branch `s ≥ 1/2`, uniformly in `s`.**

For `s ≥ 1/2`, `0 ≤ σ` with `σ (1 + 2(n-1)s) ≤ M` and `0 < δ ≤ min 1 (n(n-1)/(12M))` the two
scalar room conditions `ChSRoom` of the shift inclusion hold, with `b = b' = 1/2` (so the constants
`C_EF, C_T, C_ric` are irrelevant) and `t = 1`.

This is the quantitative core of the uniform shift: the only `s`-dependence left is through
`σ ≤ M/(1 + 2(n-1)s)`, and the inequalities are worst at `s = 1/2`. -/
lemma chat_room_half (n : ℕ) (hn : 2 ≤ n) (C_EF C_T C_ric M s σ δ : ℝ)
    (hM : 0 < M) (hs : 1 / 2 ≤ s) (hσ : 0 ≤ σ)
    (hσM : σ * (1 + 2 * ((n : ℝ) - 1) * s) ≤ M)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hδM : δ ≤ (n : ℝ) * ((n : ℝ) - 1) / (12 * M)) :
    ChSRoom n C_EF C_T C_ric s (s + δ) (1 / 2) (1 / 2)
      (1 - 4 / ((n : ℝ) - 2 + 8 * s)) (1 - 4 / ((n : ℝ) - 2 + 8 * (s + δ))) 1 σ := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by linarith
  have hnn1 : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) := mul_nonneg hn0.le hn1
  set A : ℝ := 1 + 2 * ((n : ℝ) - 1) * s with hAdef
  set H : ℝ := 1 + 2 * ((n : ℝ) - 1) * (s + δ) with hHdef
  set U : ℝ := (n : ℝ) - 2 + 8 * s with hUdef
  set U' : ℝ := (n : ℝ) - 2 + 8 * (s + δ) with hU'def
  have hAp : 0 < A := by rw [hAdef]; nlinarith [hs, hnR]
  have hAge : (n : ℝ) ≤ A := by rw [hAdef]; nlinarith [hs, hnR]
  have hu : 0 < U := by rw [hUdef]; linarith [hs]
  have hu' : 0 < U' := by rw [hU'def]; linarith [hs, hδ0]
  have hHp : 0 < H := by rw [hHdef]; nlinarith [hs, hnR, hδ0]
  have hHle : H ≤ A + 2 * ((n : ℝ) - 1) := by rw [hHdef, hAdef]; nlinarith [hδ1]
  have h4H : 4 * (A + 2 * ((n : ℝ) - 1)) ≤ 3 * (n : ℝ) * U := by
    rw [hUdef, hAdef]; nlinarith [hs, hnR]
  -- (1) the scalar bounds
  have hσn : σ * (n : ℝ) ≤ M := by
    have h : σ * (n : ℝ) ≤ σ * A := mul_le_mul_of_nonneg_left hAge hσ
    linarith
  have hδ12 : 12 * M * δ ≤ (n : ℝ) * ((n : ℝ) - 1) := by
    have h := (le_div_iff₀ (show (0:ℝ) < 12 * M by positivity)).mp hδM
    linarith [h]
  have hnum : (1 : ℝ) / 2 ≤ 1 - 2 * σ * δ / (n : ℝ) := by
    have hs3 : 4 * σ * δ * (n:ℝ) * (n:ℝ) ≤ (n:ℝ) * ((n:ℝ) - 1) * (n:ℝ) / 3 := by
      have hs1 : 4 * σ * δ * (n : ℝ) ≤ 4 * M * δ := by
        have h0 : (0:ℝ) ≤ 4 * δ := mul_nonneg (by norm_num) hδ0.le
        have h := mul_le_mul_of_nonneg_right hσn h0
        linarith [h]
      have hs1' : 4 * σ * δ * (n : ℝ) * (n : ℝ) ≤ 4 * M * δ * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hs1 hn0.le
      have hs2 : 4 * M * δ * (n : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) * (n : ℝ) / 3 := by
        have h0 : (0:ℝ) ≤ (1:ℝ)/3 * (n:ℝ) := mul_nonneg (by norm_num) hn0.le
        have h := mul_le_mul_of_nonneg_right hδ12 h0
        linarith [h]
      linarith [hs1', hs2]
    have hs4 : 4 * σ * δ ≤ ((n : ℝ) - 1) / 3 := by
      have h3' : 4 * σ * δ * (n:ℝ) * (n:ℝ) ≤ (((n:ℝ) - 1)/3 * (n:ℝ)) * (n:ℝ) := by linarith [hs3]
      have h3'' : 4 * σ * δ * (n:ℝ) ≤ ((n:ℝ) - 1)/3 * (n:ℝ) := le_of_mul_le_mul_right h3' hn0
      exact le_of_mul_le_mul_right h3'' hn0
    rw [show (1 : ℝ) / 2 ≤ 1 - 2 * σ * δ / (n : ℝ) ↔ 2 * σ * δ / (n : ℝ) ≤ 1 / 2 by
      constructor <;> intro h <;> linarith, div_le_iff₀ hn0]
    nlinarith [hs4, hnR]
  -- (2) the shift identity for `chSg2`
  have hchSg2 : chSg2 n s (s + δ) 1 σ = (1 - 2 * σ * δ / (n : ℝ)) / H := by
    rw [chSg2, hHdef]
    congr 1
    ring
  -- (3) the key estimate
  have hGn : 32 * σ * δ * H * (n : ℝ) ≤ 2 * ((n : ℝ) - 1) * (n : ℝ) ^ 2 * U := by
    have e1 : 32 * (σ * (n : ℝ)) * δ * H ≤ 32 * M * δ * H := by
      have h0 : (0:ℝ) ≤ 32 * δ * H := mul_nonneg (mul_nonneg (by norm_num) hδ0.le) hHp.le
      have h := mul_le_mul_of_nonneg_right hσn h0
      linarith [h]
    have e2 : 32 * M * δ * H ≤ (8/3) * ((n : ℝ) * ((n : ℝ) - 1)) * H := by
      have h0 : (0:ℝ) ≤ (8:ℝ)/3 * H := mul_nonneg (by norm_num) hHp.le
      have h := mul_le_mul_of_nonneg_right hδ12 h0
      linarith [h]
    have e3 : (8/3) * ((n : ℝ) * ((n : ℝ) - 1)) * H
        ≤ (8/3) * ((n : ℝ) * ((n : ℝ) - 1)) * (A + 2 * ((n:ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left hHle (mul_nonneg (by norm_num) hnn1)
    have e4 : (8/3) * ((n : ℝ) * ((n : ℝ) - 1)) * (A + 2 * ((n:ℝ) - 1))
        ≤ 2 * ((n : ℝ) - 1) * (n : ℝ) ^ 2 * U := by
      have h0 : (0:ℝ) ≤ (2:ℝ)/3 * ((n:ℝ) * ((n:ℝ) - 1)) := mul_nonneg (by norm_num) hnn1
      have h := mul_le_mul_of_nonneg_right h4H h0
      linarith [h]
    linarith [e1, e2, e3, e4]
  have hdiv : 32 * σ * δ * H ≤ 2 * ((n : ℝ) - 1) * (n : ℝ) * U := by
    have h1 : 32 * σ * δ * H * (n:ℝ) ≤ (2 * ((n:ℝ)-1) * (n:ℝ) * U) * (n:ℝ) := by linarith [hGn]
    exact le_of_mul_le_mul_right h1 hn0
  have hG : 32 * σ * δ * H ≤ 4 * ((n : ℝ) - 1) * (1 - 2 * σ * δ / (n : ℝ)) * (n : ℝ) * U := by
    have h0 : (0:ℝ) ≤ 4 * ((n : ℝ) - 1) * (n : ℝ) * U :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hn1) hn0.le) hu.le
    have h := mul_le_mul_of_nonneg_left hnum h0
    linarith [hdiv, h]
  have hUU' : U' - U = 8 * δ := by rw [hU'def, hUdef]; ring
  have hkey : σ * (4 / U - 4 / U') / (n : ℝ)
      ≤ (1 - 2 * σ * δ / (n : ℝ)) / H * ((n : ℝ) - 1) * (4 / U') := by
    have hdP : 4 / U - 4 / U' = 32 * δ / (U * U') := by
      rw [div_sub_div _ _ (ne_of_gt hu) (ne_of_gt hu')]
      congr 1
      linarith [hUU']
    rw [hdP]
    have eL : σ * (32 * δ / (U * U')) / (n : ℝ) = 32 * σ * δ / ((n : ℝ) * U * U') := by
      field_simp
    have eR : (1 - 2 * σ * δ / (n : ℝ)) / H * ((n : ℝ) - 1) * (4 / U')
        = 4 * ((n : ℝ) - 1) * (1 - 2 * σ * δ / (n : ℝ)) / (H * U') := by
      field_simp
    rw [eL, eR]
    rw [div_le_div_iff₀ (mul_pos (mul_pos hn0 hu) hu') (mul_pos hHp hu')]
    have h := mul_le_mul_of_nonneg_right hG hu'.le
    linarith [h]
  -- (4) the two room inequalities
  unfold ChSRoom
  rw [chSg1_half_half]
  simp only [abs_zero, zero_mul, zero_add]
  constructor
  · rw [hchSg2]
    exact div_nonneg (by linarith [hnum]) hHp.le
  · have h1 : (1:ℝ) - (1 - 4 / U') = 4 / U' := by ring
    have h2 : (1 - 4 / U') - (1 - 4 / U) = 4 / U - 4 / U' := by ring
    rw [hchSg2, h1, h2]
    exact hkey

/-- **The uniform large-`s` shift inclusion.**  For every `n ≥ 2` and every bound `N > 0` on
`scalAlg R` there is a *single* `δ₂ > 0` such that for every `s ≥ 1/2` and every `δ ∈ (0, δ₂]`

`R + Iso n ∈ Ĉ(s)`, `scalAlg R ≤ N`  ⟹  `R + 2 • Iso n ∈ Ĉ(s + δ)`. -/
theorem Chat_large_shift (n : ℕ) (hn : 2 ≤ n) (N : ℝ) (hN : 0 < N) :
    ∃ δ₂ : ℝ, 0 < δ₂ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₂ →
      ∀ s : ℝ, 1 / 2 ≤ s → ∀ R : Submission.Diff.Alg.Curv4 n,
        R + Submission.Diff.Alg.Iso n ∈ Work.Diff.Alg.Pinch.Chat n s →
        Submission.Diff.Alg.scalAlg R ≤ N →
        R + (2 : ℝ) • Submission.Diff.Alg.Iso n ∈ Work.Diff.Alg.Pinch.Chat n (s + δ) := by
  obtain ⟨C_EF, hC_EFpos, hC_EF⟩ := EF_algCurv_bound n
  obtain ⟨C_T₀, hC_T₀0, hC_T₀⟩ := ChatShift.knProd_ric0_norm_bound n
  obtain ⟨C_ric₀, hC_ric₀0, hC_ric₀⟩ := ChatShift.ric0_form_bound n
  set C_T : ℝ := max C_T₀ 1 with hC_Tdef
  set C_ric : ℝ := max C_ric₀ 1 with hC_ricdef
  have hC_Tpos : 0 < C_T := lt_max_iff.mpr (Or.inr one_pos)
  have hC_ricpos : 0 < C_ric := lt_max_iff.mpr (Or.inr one_pos)
  have hC_T : ∀ S : Curv4 n, IsAlgCurv S → InPIC2 S →
      ‖knProd (ric0 S) (id2 n)‖ ≤ C_T * scalAlg S := by
    intro S h1 h2
    refine (hC_T₀ S h1 h2).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) ((inPIC2_metric_basic n).2.2 S h2)
  have hC_ric : ∀ S : Curv4 n, IsAlgCurv S → InPIC2 S → ∀ v : Fin n → ℝ,
      |∑ i, ∑ j, ric0 S i j * v i * v j| ≤ C_ric * scalAlg S * (∑ i, v i * v i) := by
    intro S h1 h2 v
    refine (hC_ric₀ S h1 h2 v).trans ?_
    have hσ : 0 ≤ scalAlg S := (inPIC2_metric_basic n).2.2 S h2
    have hV : 0 ≤ ∑ i, v i * v i := Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hσ) hV
  -- numerical data
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by linarith
  have hnn1 : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) := mul_nonneg hn0.le hn1
  have hnis : ((n : ℝ)) ≠ 0 := ne_of_gt hn0
  set M : ℝ := N + (n : ℝ) * ((n : ℝ) - 1) with hMdef
  have hMpos : 0 < M := by
    rw [hMdef]
    linarith [hN, hnn1]
  refine ⟨min 1 ((n : ℝ) * ((n : ℝ) - 1) / (12 * M)), lt_min one_pos ?_, ?_⟩
  · exact div_pos (mul_pos hn0 (by linarith)) (by positivity)
  intro δ hδ0 hδle s hs R hXR hRscal
  have hδ1 : δ ≤ 1 := le_trans hδle (min_le_left _ _)
  have hδM : δ ≤ (n : ℝ) * ((n : ℝ) - 1) / (12 * M) := le_trans hδle (min_le_right _ _)
  have hs0 : 0 < s := by linarith
  have hsδ : 1 / 2 ≤ s + δ := by linarith
  have hchats : Chat n s = Ccone (n := n) s (1 / 2) (1 - 4 / ((n : ℝ) - 2 + 8 * s)) := by
    rw [ChatAny.chat_eq_cone_param n, anyAA_ge_half n hn hs, anyBB_ge_half hs,
      anyPP_ge_half n hn hs]
  have hchats' : Chat n (s + δ)
      = Ccone (n := n) (s + δ) (1 / 2) (1 - 4 / ((n : ℝ) - 2 + 8 * (s + δ))) := by
    rw [ChatAny.chat_eq_cone_param n, anyAA_ge_half n hn hsδ, anyBB_ge_half hsδ,
      anyPP_ge_half n hn hsδ]
  rw [hchats] at hXR
  obtain ⟨S, hSmem, hXS⟩ := hXR
  have hSalg : IsAlgCurv S := hSmem.1
  have hSpic : InPIC2 S := hSmem.2.1
  have hSric : RicPinch (1 - 4 / ((n : ℝ) - 2 + 8 * s)) S := hSmem.2.2
  have hσ0 : 0 ≤ scalAlg S := (inPIC2_metric_basic n).2.2 S hSpic
  have hXscal : scalAlg (R + Iso n) = (1 + 2 * ((n : ℝ) - 1) * s) * scalAlg S := by
    rw [← hXS]
    exact scalAlg_ell_of_ne n s (1 / 2) hnis hSalg
  have hXscalR : scalAlg (R + Iso n) = scalAlg R + (n : ℝ) * ((n : ℝ) - 1) := by
    rw [scalAlg_add, scalAlg_iso]
  have hXM : scalAlg (R + Iso n) ≤ M := by
    rw [hXscalR, hMdef]; linarith
  have hσM : scalAlg S * (1 + 2 * ((n : ℝ) - 1) * s) ≤ M := by
    rw [mul_comm, ← hXscal]
    exact hXM
  have hroom : ChSRoom n C_EF C_T C_ric s (s + δ) (1 / 2) (1 / 2)
      (1 - 4 / ((n : ℝ) - 2 + 8 * s)) (1 - 4 / ((n : ℝ) - 2 + 8 * (s + δ))) 1 (scalAlg S) :=
    chat_room_half n hn C_EF C_T C_ric M s (scalAlg S) δ hMpos hs hσ0 hσM hδ0 hδ1 hδM
  have hu : (0 : ℝ) < (n : ℝ) - 2 + 8 * s := by linarith
  have hu' : (0 : ℝ) < (n : ℝ) - 2 + 8 * (s + δ) := by linarith
  have hPle : 1 - 4 / ((n : ℝ) - 2 + 8 * s) ≤ 1 - 4 / ((n : ℝ) - 2 + 8 * (s + δ)) := by
    have h : 4 / ((n : ℝ) - 2 + 8 * (s + δ)) ≤ 4 / ((n : ℝ) - 2 + 8 * s) := by
      exact div_le_div_of_nonneg_left (by norm_num) hu (by linarith)
    linarith
  have hP'lt : 1 - 4 / ((n : ℝ) - 2 + 8 * (s + δ)) < 1 := by
    have h : 0 < 4 / ((n : ℝ) - 2 + 8 * (s + δ)) := by positivity
    linarith
  have hcore : S + chSg1 n (1 / 2) (1 / 2) • knProd (ric0 S) (id2 n)
      + chSg2 n s (s + δ) 1 (scalAlg S) • Iso n
      ∈ Dpic (n := n) (1 - 4 / ((n : ℝ) - 2 + 8 * (s + δ))) :=
    ChatAny.dpic_shift_core n hn hC_EFpos.le hC_Tpos.le hC_ricpos.le hC_EF hC_T hC_ric
      hPle hP'lt hSalg hSpic hSric rfl hroom
  have ha' : 1 + 2 * ((n : ℝ) - 1) * (s + δ) ≠ 0 := by
    have h : 0 < 1 + 2 * ((n : ℝ) - 1) * (s + δ) := by nlinarith [hs, hnR, hδ0]
    exact ne_of_gt h
  have hb' : 1 + ((n : ℝ) - 2) * (1 / 2) ≠ 0 := by
    have h : 0 < 1 + ((n : ℝ) - 2) * (1 / 2) := by nlinarith [hnR]
    exact ne_of_gt h
  have hlinv : linv (s + δ) (1 / 2) (R + Iso n + Iso n)
      = S + chSg1 n (1 / 2) (1 / 2) • knProd (ric0 S) (id2 n)
        + chSg2 n s (s + δ) 1 (scalAlg S) • Iso n := by
    have h1 := linv_ell_add_smul_Iso n hnis (a := s) (b := 1 / 2) (a' := s + δ) (b' := 1 / 2)
      (t := 1) ha' hb' hSalg
    rw [one_smul, hXS] at h1
    exact h1
  have hXalg : IsAlgCurv (R + Iso n + Iso n) := by
    rw [← hXS]
    exact isAlgCurv_add (ell_isAlgCurv n s (1 / 2) hSalg) (Iso_algCurv n)
  have hmem : R + Iso n + Iso n
      ∈ Ccone (n := n) (s + δ) (1 / 2) (1 - 4 / ((n : ℝ) - 2 + 8 * (s + δ))) :=
    ⟨linv (s + δ) (1 / 2) (R + Iso n + Iso n), hlinv ▸ hcore, ell_linv n ha' hb' hXalg⟩
  have h2 : R + (2 : ℝ) • Iso n = R + Iso n + Iso n := by
    rw [show (2 : ℝ) = 1 + 1 from by norm_num, add_smul, one_smul]
    abel
  rw [hchats', h2]
  exact hmem

end Work.Diff.Alg.Pinch
