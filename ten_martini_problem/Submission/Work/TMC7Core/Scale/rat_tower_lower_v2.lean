import Mathlib
import Submission.Work.TMC7Core.LDT
import Submission.Work.TMC7Core.Scale.prop9_aux
import Submission.Work.TMC7Core.Scale.scale_tower_step
import Submission.Work.TMC7Core.Scale.rat_excess_rate_explicit
import Submission.Work.TMComp.C7Aux.tower_lower_arith
import Submission.Work.TMComp.C7Aux.rtlSchedule
import Submission.Work.TMC7Core.Scale.rtlRunLeV2
import Submission.Work.TMC7Core.Scale.rtlSumEpsOwn
import Submission.Work.TMC7Core.Scale.polyExpDecayV2
import Submission.Work.TMC7Core.Scale.rtlMMTwoMulLtV2
import Submission.Work.TMC7Core.Scale.logDivDecayV2

namespace Work.TMC7Core.Scale

open Work.TMComp.C7Aux

namespace RTLH

/-- Monotonicity of the chain `Q` on `[0,k]` from strict increase on `[0,k)`. -/
lemma Q_mono_le {Q : ℕ → ℕ} {k : ℕ} (hmono : ∀ i < k, Q i < Q (i+1)) :
    ∀ {i j : ℕ}, i ≤ j → j ≤ k → Q i ≤ Q j := by
  have key : ∀ j, j ≤ k → ∀ i ≤ j, Q i ≤ Q j := by
    intro j
    induction j with
    | zero => intro _ i hi; rw [Nat.le_zero.mp hi]
    | succ j ih =>
        intro hjk i hij
        rcases Nat.eq_or_lt_of_le hij with h | h
        · rw [h]
        · exact le_trans (ih (by omega) i (by omega)) (le_of_lt (hmono j (by omega)))
  intro i j hij hjk
  exact key j hjk i hij

/-- Telescoping lower bound along a tower with step loss `2 D + e`. -/
lemma seq_lower {l D e : ℕ → ℝ} {T : ℕ}
    (hstep : ∀ u < T, l u ≤ l (u+1) + 2 * D u + e u) :
    l 0 - 2 * (∑ u ∈ Finset.range T, D u) - (∑ u ∈ Finset.range T, e u) ≤ l T := by
  have h := Finset.sum_range_sub l T
  have hle : ∑ i ∈ Finset.range T, (-(2 * D i + e i))
      ≤ ∑ i ∈ Finset.range T, (l (i+1) - l i) := by
    refine Finset.sum_le_sum (fun i hi => ?_)
    have := hstep i (Finset.mem_range.mp hi)
    linarith
  rw [h] at hle
  have h2 : ∑ i ∈ Finset.range T, (-(2 * D i + e i))
      = -(2 * (∑ i ∈ Finset.range T, D i) + ∑ i ∈ Finset.range T, e i) := by
    rw [Finset.sum_neg_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  rw [h2] at hle
  linarith

/-- Iterated contraction: `D T ≤ D 0 · ∏ 1/m + Σ e` when `D (u+1) ≤ D u/m u + e u`. -/
lemma seq_le_of_cont {D e : ℕ → ℝ} {m : ℕ → ℕ}
    (hm1 : ∀ u, 1 ≤ m u) (he0 : ∀ u, 0 ≤ e u) :
    ∀ T : ℕ, (∀ u < T, D (u+1) ≤ D u / (m u : ℝ) + e u) →
      D T ≤ D 0 * (∏ u ∈ Finset.range T, (1 / (m u : ℝ))) + (∑ u ∈ Finset.range T, e u) := by
  intro T
  induction T with
  | zero => intro _; simp
  | succ T ih =>
    intro hcont
    have hct := hcont T (Nat.lt_succ_self T)
    have hih := ih (fun u hu => hcont u (by omega))
    have hmpos : (0 : ℝ) < (m T : ℝ) := by exact_mod_cast (hm1 T)
    have hsum_nn : 0 ≤ ∑ u ∈ Finset.range T, e u := Finset.sum_nonneg (fun u _ => he0 u)
    have hle1 : D T / (m T : ℝ)
        ≤ (D 0 * (∏ u ∈ Finset.range T, (1 / (m u : ℝ))) + (∑ u ∈ Finset.range T, e u))
          / (m T : ℝ) := div_le_div_of_nonneg_right hih (le_of_lt hmpos)
    have hle2 : (∑ u ∈ Finset.range T, e u) / (m T : ℝ) ≤ ∑ u ∈ Finset.range T, e u :=
      div_le_self hsum_nn (by exact_mod_cast hm1 T)
    have hExp : (D 0 * (∏ u ∈ Finset.range T, (1 / (m u : ℝ))) + (∑ u ∈ Finset.range T, e u))
          / (m T : ℝ)
        = D 0 * ((∏ u ∈ Finset.range T, (1 / (m u : ℝ))) * (1 / (m T : ℝ)))
          + (∑ u ∈ Finset.range T, e u) / (m T : ℝ) := by
      field_simp
    rw [Finset.prod_range_succ, Finset.sum_range_succ]
    linarith [hct, hle1, hle2, hExp]

/-- For `q ≥ 80/cκ²`, `10 q ≤ exp (cκ q / 2)`. -/
lemma exp_ge_ten_mul {cκ : ℝ} (hcκ : 0 < cκ) {q : ℕ} (hq : 80 / cκ ^ 2 ≤ (q : ℝ)) :
    10 * (q : ℝ) ≤ Real.exp (cκ * (q : ℝ) / 2) := by
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  set x : ℝ := cκ * (q : ℝ) / 2 with hx
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hsum : (∑ i ∈ Finset.range 3, x ^ i / ((i.factorial : ℕ) : ℝ)) ≤ Real.exp x :=
    Real.sum_le_exp_of_nonneg hx0 3
  have he : (∑ i ∈ Finset.range 3, x ^ i / ((i.factorial : ℕ) : ℝ)) = 1 + x + x ^ 2 / 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    norm_num [Nat.factorial]
  rw [he] at hsum
  have hx2 : x ^ 2 / 2 ≤ Real.exp x := by nlinarith [hsum, hx0]
  have hx2' : x ^ 2 / 2 = cκ ^ 2 / 8 * ((q : ℝ) ^ 2) := by
    rw [hx]; field_simp; ring
  have hfin : cκ ^ 2 / 8 * ((q : ℝ) ^ 2) ≤ Real.exp (cκ * (q : ℝ) / 2) := by
    rw [← hx2', ← hx]; exact hx2
  calc 10 * (q : ℝ) = cκ ^ 2 / 8 * (80 / cκ ^ 2 * (q : ℝ)) := by field_simp; ring
    _ ≤ cκ ^ 2 / 8 * ((q : ℝ) * (q : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right hq hq0
    _ = cκ ^ 2 / 8 * ((q : ℝ) ^ 2) := by ring
    _ ≤ Real.exp (cκ * (q : ℝ) / 2) := hfin

/-- The product of `1/m` over a range with `m ≥ 1` is at most `1/(m 0)`. -/
lemma prod_inv_le_first {m : ℕ → ℕ} (hm1 : ∀ u, 1 ≤ m u) :
    ∀ {s : ℕ}, 1 ≤ s → (∏ u ∈ Finset.range s, (1 / (m u : ℝ))) ≤ 1 / (m 0 : ℝ) := by
  intro s
  induction s with
  | zero => intro h; omega
  | succ s ih =>
      intro _
      rcases Nat.eq_zero_or_pos s with h | h
      · subst h; simp
      · rw [Finset.prod_range_succ]
        have hle0 : 0 ≤ ∏ u ∈ Finset.range s, (1 / (m u : ℝ)) :=
          Finset.prod_nonneg (fun u _ => by positivity)
        have hfac : (1 / (m s : ℝ)) ≤ 1 := by
          rw [div_le_one (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hm1 s)))]
          exact_mod_cast hm1 s
        exact le_trans (mul_le_of_le_one_right hle0 hfac) (ih (by omega))

/-- Nonnegativity of a finite-scale average at any scale `N ≥ 1`. -/
lemma lyapAvg_nonneg_of_pos (α lam : ℝ) (E : ℂ) {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ Work.TMC7Core.lyapAvg α lam E N := by
  have := Work.TMC7Core.Scale.lyapAvg_nonneg' α lam E (N - 1)
  rwa [Nat.sub_add_cancel hN] at this

end RTLH

open RTLH

/-- The invariant carried along the finite tower. -/
private def RTLInv (l D e : ℕ → ℝ) (m : ℕ → ℕ) (kap : ℝ) (s : ℕ) : Prop :=
  (l 0 - 2 * (∑ u ∈ Finset.range s, D u) - (∑ u ∈ Finset.range s, e u) ≤ l s)
  ∧ (D s ≤ D 0 * (∏ u ∈ Finset.range s, (1 / (m u : ℝ))) + (∑ u ∈ Finset.range s, e u))
  ∧ ((∑ u ∈ Finset.range s, D u) ≤ D 0 + 3/2 * (D 0 / (m 0 : ℝ) + ∑ u ∈ Finset.range s, e u))
  ∧ (100 * kap < l s)
  ∧ (D s < l s / 10)

end Work.TMC7Core.Scale

namespace Work.TMC7Core.Scale
open Work.TMComp.C7Aux
open RTLH

set_option maxHeartbeats 20000000 in
/-- The finite rational tower of Case II of the C7 dichotomy (`S1` of
`Submission/Work/TMC7Core/C7_INPUTS_LEAD.md`). Should live in `namespace Work.TMC7Core.Scale`.
At a rational frequency `ω = P k/Q k` where the chain `P i/Q i` are good approximants of `ω`
(cross-distance `< 1/Q i²`, growth `Q (i+1) ≤ e^{b Q i}`), with a level `200κ < L_{N₀}` and the
pairing `(9/10) L_{N₀} < L_{2N₀}` at a scale `N₀ ≥ C κ⁻² Q 0`, the two-scale quantity
`P(ω,E,N₀) = 2 L_{2N₀} - L_{N₀}` is at most `L(ω,E)` up to an error exponentially small in
`Q 0`. Route: climb the avalanche tower from `N₀` with `Scale.scale_tower_step`, one window per
chain element (multipliers `≈ e^{cκQ_i/2}/5`), telescope with `Scale.finite_tower_lower` /
`Work.TMComp.C7Aux.tower_lower_arith`, close at a top scale `N_S = m_fin · Q k ≥ e^{cκQ k/4}/2`
with `Scale.rat_excess_rate_explicit`. See `Scale/S1_GUIDE.md` and (important for correctness,
the `D₀/m₀` factor) `S1_BOOKKEEPING_NOTE.md`. -/
theorem rat_tower_lower_v2 (lam : ℝ) (K : Set ℝ) (c C C₀ : ℝ)
    (hLDT : Work.TMC7Core.HasLDTOn lam K c C) (hLEB : Work.TMC7Core.HasLEBound lam K C₀)
    (hc1 : c ≤ 1) (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 200) (b : ℝ) (hb : 0 < b) :
    ∃ B T : ℝ, 0 < B ∧ ∀ (k : ℕ) (P : ℕ → ℤ) (Q : ℕ → ℕ),
      (∀ i ≤ k, 1 ≤ Q i) → (∀ i < k, Q i < Q (i + 1)) →
      (∀ i ≤ k, Nat.Coprime (Int.natAbs (P i)) (Q i)) →
      (∀ i < k, |(P k : ℝ) / (Q k) - (P i : ℝ) / (Q i)| < 1 / ((Q i : ℝ) ^ 2)) →
      (∀ i < k, (Q (i + 1) : ℝ) ≤ Real.exp (b * (Q i : ℝ))) →
      T ≤ (Q 0 : ℝ) →
      ∀ E ∈ K, ∀ N₀ : ℕ, C * (κ ^ 2)⁻¹ * (Q 0 : ℝ) ≤ (N₀ : ℝ) →
      200 * κ < Work.TMC7Core.lyapAvg ((P k : ℝ) / (Q k)) lam (E : ℂ) N₀ →
      (9 / 10) * Work.TMC7Core.lyapAvg ((P k : ℝ) / (Q k)) lam (E : ℂ) N₀
          < Work.TMC7Core.lyapAvg ((P k : ℝ) / (Q k)) lam (E : ℂ) (2 * N₀) →
      2 * Work.TMC7Core.lyapAvg ((P k : ℝ) / (Q k)) lam (E : ℂ) (2 * N₀)
          - Work.TMC7Core.lyapAvg ((P k : ℝ) / (Q k)) lam (E : ℂ) N₀
        ≤ Work.TMC7Core.lyap ((P k : ℝ) / (Q k)) lam (E : ℂ)
          + B * Real.exp (-(c * κ * (Q 0 : ℝ) / 8)) := by
  classical
  have hc0 : 0 < c := hLDT.1
  have hC1 : 1 ≤ C := hLDT.2.1
  have hC0pos : 0 < C₀ := hLEB.1
  have hC0nn : 0 ≤ C₀ := le_of_lt hC0pos
  have hκ100 : κ ≤ 1/100 := by linarith
  set cκ : ℝ := c * κ with hcκdef
  have hcκpos : 0 < cκ := by rw [hcκdef]; positivity
  set A : ℝ := C * (κ ^ 2)⁻¹ with hAdef
  have hApos : 0 < A := by rw [hAdef]; positivity
  set Sb : ℕ := Nat.ceil (4 * b / cκ) + 1 with hSbdef
  have hSbreal : 4 * b / cκ < (Sb : ℝ) := by
    rw [hSbdef]; push_cast
    linarith [Nat.le_ceil (4 * b / cκ)]
  have hexpden : 0 < 1 - Real.exp (-(cκ / 2)) := by
    have h1 : Real.exp (-(cκ / 2)) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith
  obtain ⟨Bp, Tp, hBppos, hpoly⟩ := polyExpDecayV2 (cκ / 8) (by positivity)
  set Ke : ℝ := (Sb + 1) * (76 * C₀ + 9) / (1 - Real.exp (-(cκ / 2))) + (76 * C₀ + 9) with hKedef
  have hKepos : 0 < Ke := by rw [hKedef]; positivity
  have hKe_ge9 : (76 * C₀ + 9) ≤ Ke := by
    rw [hKedef]
    have : 0 ≤ (Sb + 1) * (76 * C₀ + 9) / (1 - Real.exp (-(cκ / 2))) := by positivity
    linarith
  have hKe1 : 1 ≤ Ke := le_trans (by linarith) hKe_ge9
  have hTKe1 : 1 ≤ Ke / κ := by
    rw [le_div_iff₀ hκ]
    linarith [hKe1, hκ1, hκ]
  set TF : Finset ℝ := {3, 4 * Real.log 10 / cκ, A, 80 / cκ ^ 2, 4 * Real.log 2 / cκ,
      2 * Real.log (Ke / κ) / cκ, 2 * Real.log (30 * C₀ / κ) / cκ, Tp} with hTF
  have hTFne : TF.Nonempty := by rw [hTF]; exact ⟨3, by simp⟩
  set T : ℝ := TF.max' hTFne with hTdef
  have hT3 : (3 : ℝ) ≤ T := by
    rw [hTdef]; exact Finset.le_max' TF 3 (by rw [hTF]; simp)
  have hTlog10 : 4 * Real.log 10 / cκ ≤ T := by
    rw [hTdef]; exact Finset.le_max' TF _ (by rw [hTF]; simp)
  have hTA : A ≤ T := by
    rw [hTdef]; exact Finset.le_max' TF _ (by rw [hTF]; simp)
  have hT80 : 80 / cκ ^ 2 ≤ T := by
    rw [hTdef]; exact Finset.le_max' TF _ (by rw [hTF]; simp)
  have hTlog2 : 4 * Real.log 2 / cκ ≤ T := by
    rw [hTdef]; exact Finset.le_max' TF _ (by rw [hTF]; simp)
  have hTKe2 : 2 * Real.log (Ke / κ) / cκ ≤ T := by
    rw [hTdef]; exact Finset.le_max' TF _ (by rw [hTF]; simp)
  have hT30b : 2 * Real.log (30 * C₀ / κ) / cκ ≤ T := by
    rw [hTdef]; exact Finset.le_max' TF _ (by rw [hTF]; simp)
  have hTp : Tp ≤ T := by
    rw [hTdef]; exact Finset.le_max' TF _ (by rw [hTF]; simp)
  have hke_e_mult : ∀ x : ℝ, Real.exp (cκ * x / 2) * Real.exp (-(cκ * x / 2)) = 1 := by
    intro x; rw [← Real.exp_add]; ring_nf; simp
  have hKe_e : Ke * Real.exp (-(cκ * T / 2)) ≤ κ := by
    have hpos : 0 < Ke / κ := div_pos hKepos hκ
    have h1 : Real.log (Ke / κ) ≤ cκ * T / 2 := by
      have := (div_le_iff₀ hcκpos).mp hTKe2; linarith
    have h2 : Ke / κ ≤ Real.exp (cκ * T / 2) := (Real.log_le_iff_le_exp hpos).mp h1
    rw [div_le_iff₀ hκ] at h2
    have he := hke_e_mult T
    calc Ke * Real.exp (-(cκ * T / 2))
        ≤ (Real.exp (cκ * T / 2) * κ) * Real.exp (-(cκ * T / 2)) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = κ := by
        have h3 : (Real.exp (cκ * T / 2) * κ) * Real.exp (-(cκ * T / 2))
            = κ * (Real.exp (cκ * T / 2) * Real.exp (-(cκ * T / 2))) := by ring
        rw [h3, he, mul_one]
  have h30_e : 30 * C₀ * Real.exp (-(cκ * T / 2)) ≤ κ := by
    have hpos : 0 < 30 * C₀ / κ := div_pos (by positivity) hκ
    have h1 : Real.log (30 * C₀ / κ) ≤ cκ * T / 2 := by
      have := (div_le_iff₀ hcκpos).mp hT30b; linarith
    have h2 : 30 * C₀ / κ ≤ Real.exp (cκ * T / 2) := (Real.log_le_iff_le_exp hpos).mp h1
    rw [div_le_iff₀ hκ] at h2
    have he := hke_e_mult T
    calc 30 * C₀ * Real.exp (-(cκ * T / 2))
        = (30 * C₀) * Real.exp (-(cκ * T / 2)) := by ring
      _ ≤ (Real.exp (cκ * T / 2) * κ) * Real.exp (-(cκ * T / 2)) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = κ := by
        have h3 : (Real.exp (cκ * T / 2) * κ) * Real.exp (-(cκ * T / 2))
            = κ * (Real.exp (cκ * T / 2) * Real.exp (-(cκ * T / 2))) := by ring
        rw [h3, he, mul_one]
  have hBpos : 0 < 7 * Ke + 30 * C₀ + 2 * (C₀ + 1) * (1 + cκ / 4) * Bp := by
    have h1 : 0 < 7 * Ke := by linarith [hKepos]
    have h2 : 0 ≤ 30 * C₀ := by linarith [hC0nn]
    have h3 : 0 ≤ (C₀ + 1) := by linarith [hC0nn]
    have h4 : 0 < 1 + cκ / 4 := by linarith [hcκpos]
    have h5 : 0 < 2 * ((C₀ + 1) * (1 + cκ / 4) * Bp) :=
      mul_pos (by norm_num) (mul_pos (mul_pos (by linarith [hC0nn]) h4) hBppos)
    linarith
  refine ⟨7 * Ke + 30 * C₀ + 2 * (C₀ + 1) * (1 + cκ / 4) * Bp, T, hBpos, ?_⟩
  intro k P Q hQ1 hQmono hQcop hap hgrowth hTle E hEK N₀ hN₀ge hlev hpair
  have hQk1 : 1 ≤ Q k := hQ1 k le_rfl
  have hQ0Q : ∀ {i j : ℕ}, i ≤ j → j ≤ k → (Q i : ℝ) ≤ (Q j : ℝ) := fun hij hjk =>
    by exact_mod_cast Q_mono_le hQmono hij hjk
  have hTleQ : ∀ i ≤ k, T ≤ (Q i : ℝ) := fun i hi => le_trans hTle (hQ0Q (Nat.zero_le i) hi)
  set ω : ℝ := (P k : ℝ) / (Q k) with hωdef
  have hom : ∀ i ≤ k, |ω - (P i : ℝ) / (Q i : ℝ)| < 1 / ((Q i : ℝ) ^ 2) := by
    intro i hi
    rcases lt_or_eq_of_le hi with h | h
    · rw [hωdef]; exact hap i h
    · subst h
      rw [hωdef, sub_self, abs_zero]
      positivity
  have h3Q : ∀ i ≤ k, (3 : ℝ) ≤ (Q i : ℝ) := fun i hi => le_trans hT3 (hTleQ i hi)
  have h10Q : ∀ i ≤ k, 10 * (Q i : ℝ) ≤ Real.exp (cκ * (Q i : ℝ) / 2) := fun i hi =>
    exp_ge_ten_mul hcκpos (le_trans hT80 (hTleQ i hi))
  have hbig : ∀ i ≤ k, Real.log 10 ≤ cκ * (Q i : ℝ) / 4 := by
    intro i hi
    have hQ := hTleQ i hi
    have h1 : 4 * Real.log 10 ≤ T * cκ := by
      have := (div_le_iff₀ hcκpos).mp hTlog10; linarith
    have h2 : T * cκ ≤ (Q i : ℝ) * cκ := mul_le_mul_of_nonneg_right hQ (le_of_lt hcκpos)
    linarith
  have hbig2 : ∀ i ≤ k, 2 ≤ Real.exp (cκ * (Q i : ℝ) / 2) / (5 * (Q i : ℝ)) := by
    intro i hi
    have hQi : (0 : ℝ) < (Q i : ℝ) := by
      have : 1 ≤ Q i := hQ1 i hi
      exact_mod_cast this
    rw [le_div_iff₀ (by positivity)]
    linarith [h10Q i hi]
  have hA0 : A * (Q 0 : ℝ) ≤ (N₀ : ℝ) := by rw [hAdef]; exact hN₀ge
  have hN₀1 : 1 ≤ N₀ := by
    have hk2 : (1 : ℝ) ≤ (κ ^ 2)⁻¹ := by
      have h1 : κ ^ 2 ≤ 1 := by nlinarith [hκ, hκ1]
      have h2 : (0 : ℝ) < κ ^ 2 := by positivity
      rw [inv_eq_one_div, le_div_iff₀ h2]; linarith
    have hQ0 : (1 : ℝ) ≤ (Q 0 : ℝ) := by exact_mod_cast hQ1 0 (Nat.zero_le k)
    have h1 : (1 : ℝ) ≤ C * (κ ^ 2)⁻¹ * (Q 0 : ℝ) := by
      have ha : (1 : ℝ) ≤ C * (κ ^ 2)⁻¹ := by
        calc (1 : ℝ) = 1 * 1 := by ring
          _ ≤ C * (κ ^ 2)⁻¹ := mul_le_mul hC1 hk2 zero_le_one (le_trans zero_le_one hC1)
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ C * (κ ^ 2)⁻¹ * (Q 0 : ℝ) := mul_le_mul ha hQ0 zero_le_one (by positivity)
    have h2 : (1 : ℝ) ≤ (N₀ : ℝ) := by linarith [hN₀ge, h1]
    exact_mod_cast h2
  set ii : ℕ → ℕ := fun s => rtli A cκ Q k N₀ s with hiidef
  set mm : ℕ → ℕ := fun s => rtlMM cκ Q (ii s) with hmmdef
  set Nf : ℕ → ℕ := fun s => rtlN A cκ Q k N₀ s with hNfdef
  have hNfapp : ∀ s, Nf s = rtlN A cκ Q k N₀ s := fun _ => rfl
  have hiiapp : ∀ s, ii s = rtli A cκ Q k N₀ s := fun _ => rfl
  have hmmapp : ∀ s, mm s = rtlMM cκ Q (rtli A cκ Q k N₀ s) := fun _ => rfl
  have hii_le : ∀ s, ii s ≤ k := fun s => by rw [hiiapp s]; exact rtli_le A cκ Q k N₀ s
  have hQ0_le_ii : ∀ s, (Q 0 : ℝ) ≤ (Q (ii s) : ℝ) := fun s =>
    by exact_mod_cast Q_mono_le hQmono (Nat.zero_le (ii s)) (hii_le s)
  have hT_le_Qii : ∀ s, T ≤ (Q (ii s) : ℝ) := fun s => le_trans hTle (hQ0_le_ii s)
  have hmm1 : ∀ s, 1 ≤ mm s := fun s => by
    rw [hmmapp s]; exact rtlMM_pos cκ Q (hQ1 (ii s) (hii_le s))
  have hmm3 : ∀ s, 3 ≤ mm s := fun s => by
    rw [hmmapp s]
    exact rtlMM_three_le cκ Q (by
      have := h3Q (ii s) (hii_le s)
      exact_mod_cast this)
  have hNf0 : Nf 0 = N₀ := rfl
  have hNfsucc : ∀ s, Nf (s+1) = mm s * Nf s := fun _ => rfl
  have hNf_pos : ∀ s, 1 ≤ Nf s := fun s => le_trans hN₀1 (by
    rw [hNfapp s]; exact N₀_le_rtlN A cκ Q k N₀ hQ1 s)
  have hii_mono : Monotone ii := fun a b hab => by
    rw [hiiapp a, hiiapp b]
    exact rtli_mono A cκ Q k N₀ hQ1 hA0 hab
  have hii_spec : ∀ s, A * (Q (ii s) : ℝ) ≤ (Nf s : ℝ) := fun s => by
    rw [hiiapp s, hNfapp s]
    exact rtli_spec (le_trans hA0 (by exact_mod_cast N₀_le_rtlN A cκ Q k N₀ hQ1 s))
  set l : ℕ → ℝ := fun s => lyapAvg ω lam (E : ℂ) (Nf s) with hldef
  set Df : ℕ → ℝ := fun s => l s - lyapAvg ω lam (E : ℂ) (2 * Nf s) with hDfdef
  set ef : ℕ → ℝ := fun s => 9 * (4 * C₀ + 1) * Real.exp (-(cκ * (Q (ii s) : ℝ) / 2))
      + 4 * C₀ / (mm s : ℝ) with hefdef
  have hlapp : ∀ s, l s = lyapAvg ω lam (E : ℂ) (Nf s) := fun _ => rfl
  have hDfapp : ∀ s, Df s = l s - lyapAvg ω lam (E : ℂ) (2 * Nf s) := fun _ => rfl
  have hefapp : ∀ s, ef s = 9 * (4 * C₀ + 1) * Real.exp (-(cκ * (Q (ii s) : ℝ) / 2))
      + 4 * C₀ / (mm s : ℝ) := fun _ => rfl
  have hef_nn : ∀ s, 0 ≤ ef s := fun s => by
    rw [hefapp s]
    have h41 : 0 ≤ 9 * (4 * C₀ + 1) := by linarith [hC0nn]
    have hE : 0 ≤ Real.exp (-(cκ * (Q (ii s) : ℝ) / 2)) := (Real.exp_pos _).le
    have hm : (0:ℝ) < (mm s : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one (hmm1 s))
    exact add_nonneg (mul_nonneg h41 hE) (div_nonneg (by linarith [hC0nn]) hm.le)
  have hD_nn : ∀ s, 0 ≤ Df s := fun s => by
    rw [hDfapp s]
    have := lyapAvg_two_le ω lam (E : ℂ) (Nf s)
    linarith
  have hl0 : l 0 = lyapAvg ω lam (E : ℂ) N₀ := by rw [hlapp 0, hNf0]
  have hD0eq : Df 0 = lyapAvg ω lam (E : ℂ) N₀ - lyapAvg ω lam (E : ℂ) (2 * N₀) := by
    rw [hDfapp 0, hl0, hNf0]
  have hD0le : Df 0 ≤ C₀ := by
    have h1 : lyapAvg ω lam (E : ℂ) N₀ ≤ C₀ := hasLEBound_lyapAvg_le hLEB hEK ω N₀
    have h2 : 0 ≤ lyapAvg ω lam (E : ℂ) (2 * N₀) :=
      lyapAvg_nonneg_of_pos ω lam (E : ℂ) (by omega)
    rw [hD0eq]; linarith
  have hD0lt : Df 0 < l 0 / 10 := by
    rw [hD0eq, hl0]; linarith [hpair]
  have hmm0_ge : Real.exp (cκ * (Q 0 : ℝ) / 2) / 10 ≤ (mm 0 : ℝ) := by
    have h1 : Real.exp (cκ * (Q (rtli A cκ Q k N₀ 0) : ℝ) / 2) / 10
        ≤ (rtlMM cκ Q (rtli A cκ Q k N₀ 0) : ℝ) :=
      rtlMM_ge cκ Q (rtli A cκ Q k N₀ 0) (hbig2 (ii 0) (hii_le 0))
    have h2 : Real.exp (cκ * (Q 0 : ℝ) / 2) ≤ Real.exp (cκ * (Q (rtli A cκ Q k N₀ 0) : ℝ) / 2) :=
      Real.exp_le_exp.mpr (by have hh := hQ0_le_ii 0; linarith [mul_le_mul_of_nonneg_left hh hcκpos.le])
    have h3 : (mm 0 : ℝ) = (rtlMM cκ Q (rtli A cκ Q k N₀ 0) : ℝ) := rfl
    rw [h3]
    exact le_trans (div_le_div_of_nonneg_right h2 (by norm_num : (0:ℝ) ≤ 10)) h1
  have hreach : ∀ n, min n k ≤ ii (n * Sb) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        by_cases hge : k ≤ ii (n * Sb)
        · have hmono := hii_mono (Nat.mul_le_mul_right Sb (Nat.le_succ n))
          have h1 : k ≤ ii ((n+1) * Sb) := le_trans hge hmono
          exact le_trans (min_le_right _ _) h1
        · push_neg at hge
          have hle : ii (n * Sb) ≤ ii ((n+1) * Sb) := hii_mono (Nat.mul_le_mul_right Sb (Nat.le_succ n))
          have hne : ii (n * Sb) ≠ ii ((n+1) * Sb) := by
            intro hcon
            have hr := rtlRunLeV2 A cκ b Q k N₀ hApos hcκpos hb hQ1 hgrowth hA0
              hbig hbig2 hge rfl hcon.symm (Nat.mul_le_mul_right Sb (Nat.le_succ n))
            have hr' : (((n:ℝ)+1) * (Sb:ℝ) - (n:ℝ) * (Sb:ℝ)) * (cκ/4) < b := by
              simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_one] using hr
            have hSb : ((n:ℝ)+1) * (Sb:ℝ) - (n:ℝ) * (Sb:ℝ) = (Sb:ℝ) := by ring
            rw [hSb] at hr'
            have hb' : b < (Sb : ℝ) * cκ / 4 := by
              have := hSbreal
              rw [div_lt_iff₀ hcκpos] at this
              linarith
            linarith [hr']
          have hlt : ii (n * Sb) < ii ((n+1) * Sb) := lt_of_le_of_ne hle hne
          have hnk : n < k := by
            by_contra hc; push_neg at hc
            have : min n k = k := min_eq_right hc
            omega
          calc min (n+1) k = n + 1 := by rw [min_eq_left (by omega : n+1 ≤ k)]
            _ ≤ ii ((n+1) * Sb) := by omega
  have hexS : ∃ s, ii s = k := by
    refine ⟨(k+1) * Sb, le_antisymm (hii_le _) ?_⟩
    have h := hreach (k+1)
    rw [min_eq_right (by omega : k ≤ k+1)] at h
    exact h
  set S : ℕ := Nat.find hexS + 1 with hSdef
  have hSsub : S - 1 = Nat.find hexS := by rw [hSdef]; omega
  have hS1 : 1 ≤ S := by rw [hSdef]; omega
  have hiiS : ii (S-1) = k := by rw [hSsub]; exact Nat.find_spec hexS
  have hii_lt : ∀ t < S - 1, ii t < k := by
    intro t ht
    refine lt_of_le_of_ne (hii_le t) (fun h => ?_)
    have := Nat.find_min' hexS h
    have h2 : Nat.find hexS = S - 1 := by rw [hSsub]
    omega
  have hsum_lt : (∑ s ∈ Finset.range (S-1), ef s) ≤
      (Sb + 1) * (76 * C₀ + 9) * Real.exp (-(cκ * (Q 0 : ℝ) / 2)) / (1 - Real.exp (-(cκ / 2))) := by
    have hcongr : (∑ s ∈ Finset.range (S-1), ef s)
        = (∑ t ∈ Finset.range (S-1),
            (9 * (4 * C₀ + 1) * Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ t) : ℝ) / 2))
              + 4 * C₀ / (rtlMM cκ Q (rtli A cκ Q k N₀ t) : ℝ))) := by
      apply Finset.sum_congr rfl
      intro t _
      show 9 * (4 * C₀ + 1) * Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ t) : ℝ) / 2))
            + 4 * C₀ / (rtlMM cκ Q (rtli A cκ Q k N₀ t) : ℝ) = _
      rfl
    rw [hcongr]
    exact rtlSumEpsOwn A cκ b C₀ Q k N₀ Sb (S-1) hApos hcκpos hb hC0nn hSbreal
      hQ1 hQmono hgrowth hA0 hbig hbig2 (fun t ht => hii_lt t ht)
  have hlast : ef (S-1) ≤ (76 * C₀ + 9) * Real.exp (-(cκ * (Q 0 : ℝ) / 2)) := by
    have hrt : rtli A cκ Q k N₀ (S-1) = k := by rw [← hiiapp (S-1)]; exact hiiS
    have hmmk : (mm (S-1) : ℝ) = (rtlMM cκ Q k : ℝ) := by rw [hmmapp (S-1), hrt]
    have hge : Real.exp (cκ * (Q k : ℝ) / 2) / 10 ≤ (rtlMM cκ Q k : ℝ) :=
      rtlMM_ge cκ Q k (hbig2 k le_rfl)
    have hmpos : 0 < (rtlMM cκ Q k : ℝ) := lt_of_lt_of_le (div_pos (Real.exp_pos _) (by norm_num : (0:ℝ) < 10)) hge
    have he : Real.exp (cκ * (Q k : ℝ) / 2) * Real.exp (-(cκ * (Q k : ℝ) / 2)) = 1 :=
      hke_e_mult (Q k)
    have hb1 : 4 * C₀ / (rtlMM cκ Q k : ℝ) ≤ 40 * C₀ * Real.exp (-(cκ * (Q k : ℝ) / 2)) := by
      rw [div_le_iff₀ hmpos]
      have h2 : 10 * Real.exp (-(cκ * (Q k : ℝ) / 2)) * (Real.exp (cκ * (Q k : ℝ) / 2) / 10) = 1 := by
        linarith [he]
      have h4 : 10 * Real.exp (-(cκ * (Q k : ℝ) / 2)) * (Real.exp (cκ * (Q k : ℝ) / 2) / 10)
          ≤ 10 * Real.exp (-(cκ * (Q k : ℝ) / 2)) * (rtlMM cκ Q k : ℝ) :=
        mul_le_mul_of_nonneg_left hge (by positivity)
      have h3 : 1 ≤ 10 * Real.exp (-(cκ * (Q k : ℝ) / 2)) * (rtlMM cκ Q k : ℝ) := by linarith [h2, h4]
      have h5 : 4 * C₀ * 1 ≤ 4 * C₀ * (10 * Real.exp (-(cκ * (Q k : ℝ) / 2)) * (rtlMM cκ Q k : ℝ)) :=
        mul_le_mul_of_nonneg_left h3 (by linarith [hC0nn])
      linarith [h5]
    rw [hefapp (S-1), hmmk]
    have hk' : Q (ii (S-1)) = Q k := by rw [hiiS]
    rw [hk']
    have hsum : 9 * (4*C₀+1) * Real.exp (-(cκ * (Q k : ℝ) / 2)) + 40 * C₀ * Real.exp (-(cκ * (Q k : ℝ) / 2))
        = (76 * C₀ + 9) * Real.exp (-(cκ * (Q k : ℝ) / 2)) := by ring
    have hstep1 : 9 * (4*C₀+1) * Real.exp (-(cκ * (Q k : ℝ) / 2)) + 4 * C₀ / (rtlMM cκ Q k : ℝ)
        ≤ (76 * C₀ + 9) * Real.exp (-(cκ * (Q k : ℝ) / 2)) := by
      have h3 : 9 * (4*C₀+1) * Real.exp (-(cκ * (Q k : ℝ) / 2)) + 4 * C₀ / (rtlMM cκ Q k : ℝ)
          ≤ 9 * (4*C₀+1) * Real.exp (-(cκ * (Q k : ℝ) / 2)) + 40 * C₀ * Real.exp (-(cκ * (Q k : ℝ) / 2)) :=
        add_le_add le_rfl hb1
      linarith [h3, hsum]
    have hexp_le : Real.exp (-(cκ * (Q k : ℝ) / 2)) ≤ Real.exp (-(cκ * (Q 0 : ℝ) / 2)) :=
      Real.exp_le_exp.mpr (by have hh : (Q 0 : ℝ) ≤ (Q k : ℝ) := hQ0Q (Nat.zero_le k) le_rfl; linarith [mul_le_mul_of_nonneg_left hh hcκpos.le])
    have hstep2 : (76 * C₀ + 9) * Real.exp (-(cκ * (Q k : ℝ) / 2))
        ≤ (76 * C₀ + 9) * Real.exp (-(cκ * (Q 0 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hexp_le (by linarith [hC0nn])
    linarith [hstep1, hstep2]
  have hEfull : (∑ s ∈ Finset.range S, ef s) ≤ Ke * Real.exp (-(cκ * (Q 0 : ℝ) / 2)) := by
    have hSdec : S = (S-1) + 1 := by omega
    rw [hSdec, Finset.sum_range_succ, hKedef]
    have h3 : (Sb + 1) * (76 * C₀ + 9) * Real.exp (-(cκ * (Q 0 : ℝ) / 2)) / (1 - Real.exp (-(cκ / 2)))
        + (76 * C₀ + 9) * Real.exp (-(cκ * (Q 0 : ℝ) / 2))
        = ((Sb + 1) * (76 * C₀ + 9) / (1 - Real.exp (-(cκ / 2))) + (76 * C₀ + 9))
          * Real.exp (-(cκ * (Q 0 : ℝ) / 2)) := by ring
    linarith [hsum_lt, hlast, h3]
  have hD0term : 3 * Df 0 / (mm 0 : ℝ) ≤ 30 * C₀ * Real.exp (-(cκ * (Q 0 : ℝ) / 2)) := by
    have hm0 : Real.exp (cκ * (Q 0 : ℝ) / 2) / 10 ≤ (mm 0 : ℝ) := hmm0_ge
    have h1 : 3 * Df 0 / (mm 0 : ℝ) ≤ 3 * C₀ / (Real.exp (cκ * (Q 0 : ℝ) / 2) / 10) :=
      div_le_div₀ (by positivity) (by linarith [hD0le]) (by positivity) hm0
    have h2 : 3 * C₀ / (Real.exp (cκ * (Q 0 : ℝ) / 2) / 10)
        = 30 * C₀ * Real.exp (-(cκ * (Q 0 : ℝ) / 2)) := by
      rw [Real.exp_neg]
      field_simp
      ring
    linarith
  have hInv0 : RTLInv l Df ef mm κ 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show l 0 - 2 * (∑ u ∈ Finset.range 0, Df u) - (∑ u ∈ Finset.range 0, ef u) ≤ l 0
      first
        | (rw [Finset.sum_range_zero, Finset.sum_range_zero, mul_zero, sub_zero, sub_zero]
           exact le_refl _)
        | (rw [Finset.sum_range_zero, Finset.sum_range_zero, mul_zero, sub_zero, sub_zero])
    · show Df 0 ≤ Df 0 * (∏ u ∈ Finset.range 0, (1 / (mm u : ℝ))) + (∑ u ∈ Finset.range 0, ef u)
      first
        | (rw [Finset.prod_range_zero, Finset.sum_range_zero, mul_one, add_zero]
           exact le_refl _)
        | (rw [Finset.prod_range_zero, Finset.sum_range_zero, mul_one, add_zero])
    · simp only [Finset.sum_range_zero]
      have h1 : 0 ≤ Df 0 := hD_nn 0
      have h2 : (0 : ℝ) < (mm 0 : ℝ) := by exact_mod_cast hmm1 0
      have h3 : 0 ≤ 3/2 * (Df 0 / (mm 0 : ℝ)) :=
        mul_nonneg (by norm_num) (div_nonneg (hD_nn 0) ((by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one (hmm1 0)) : (0:ℝ) < (mm 0 : ℝ)).le))
      linarith
    · rw [hl0]; linarith [hlev]
    · rw [hD0eq, hl0]; linarith [hpair]
  have stage : ∀ u : ℕ, u < S → 100 * κ < l u → Df u < l u / 10 →
      (l u ≤ l (u+1) + 2 * Df u + ef u) ∧ (Df (u+1) ≤ Df u / (mm u : ℝ) + ef u) := by
    intro u hu hlevu hpairu
    have hiu : ii u ≤ k := hii_le u
    have hQu1 : 1 ≤ Q (ii u) := hQ1 (ii u) hiu
    have hcopu : Nat.Coprime (Int.natAbs (P (ii u))) (Q (ii u)) := hQcop (ii u) hiu
    have happu : |ω - (P (ii u) : ℝ) / (Q (ii u) : ℝ)| < 1 / ((Q (ii u) : ℝ) ^ 2) := hom (ii u) hiu
    have hqCu : C * (κ ^ 2)⁻¹ ≤ (Q (ii u) : ℝ) := by
      have h := hTA; rw [hAdef] at h
      exact le_trans h (hT_le_Qii u)
    have hNu : C * (κ ^ 2)⁻¹ * (Q (ii u) : ℝ) ≤ (Nf u : ℝ) := by
      have h := hii_spec u; rw [hAdef] at h
      exact h
    have hmq : ((2 * mm u : ℕ) : ℝ) < Real.exp (c * κ * (Q (ii u) : ℝ) / 2) := by
      have h6i : 6 * (Q (ii u) : ℝ) ≤ Real.exp (cκ * (Q (ii u) : ℝ) / 2) := by
        linarith [h10Q (ii u) hiu]
      have hlt := rtlMMTwoMulLtV2 cκ Q (rtli A cκ Q k N₀ u) h6i
      have h2 : ((2 * mm u : ℕ) : ℝ) = 2 * (rtlMM cκ Q (rtli A cκ Q k N₀ u) : ℝ) := by
        push_cast; rfl
      rw [h2]
      exact hlt
    have h2Nu : (9/10) * l u < lyapAvg ω lam (E:ℂ) (2 * Nf u) := by
      rw [hDfapp u] at hpairu
      linarith
    have hstep := scale_tower_step lam K c C C₀ hLDT hLEB hc1 κ hκ hκ100 E hEK ω (P (ii u)) (Q (ii u))
      hQu1 hcopu hqCu happu (Nf u) hNu (by rw [← hlapp u]; exact hlevu) h2Nu (mm u) (hmm3 u) hmq
    obtain ⟨h1, h2⟩ := hstep
    refine ⟨?_, ?_⟩
    · have hef_ge : (4*C₀+1)*Real.exp (-(c*κ*(Q (ii u):ℝ)/2)) + 4*C₀/(mm u:ℝ) ≤ ef u := by
        show (4*C₀+1)*Real.exp (-(c*κ*(Q (ii u):ℝ)/2)) + 4*C₀/(mm u:ℝ)
            ≤ 9*(4*C₀+1)*Real.exp (-(cκ*(Q (ii u):ℝ)/2)) + 4*C₀/(mm u:ℝ)
        have hE : 0 ≤ Real.exp (-(c*κ*(Q (ii u):ℝ)/2)) := (Real.exp_pos _).le
        nlinarith [hE, hC0nn]
      have hlow : -(ef u) ≤ lyapAvg ω lam (E:ℂ) (mm u * Nf u) + lyapAvg ω lam (E:ℂ) (Nf u)
          - 2 * lyapAvg ω lam (E:ℂ) (2 * Nf u) :=
        le_trans (neg_le_neg hef_ge) (abs_le.mp h1).1
      show l u ≤ l (u+1) + 2 * Df u + ef u
      rw [hDfapp u]
      show lyapAvg ω lam (E:ℂ) (Nf u)
          ≤ lyapAvg ω lam (E:ℂ) (mm u * Nf u) + 2 * (lyapAvg ω lam (E:ℂ) (Nf u)
              - lyapAvg ω lam (E:ℂ) (2 * Nf u)) + ef u
      linarith [hlow]
    · have hef_ub : 2 * ((4*C₀+1)*Real.exp (-(c*κ*(Q (ii u):ℝ)/2))) ≤ ef u := by
        show 2*((4*C₀+1)*Real.exp (-(c*κ*(Q (ii u):ℝ)/2)))
            ≤ 9*(4*C₀+1)*Real.exp (-(cκ*(Q (ii u):ℝ)/2)) + 4*C₀/(mm u:ℝ)
        have hE : 0 ≤ Real.exp (-(c*κ*(Q (ii u):ℝ)/2)) := (Real.exp_pos _).le
        have hA' : 2 * ((4*C₀+1) * Real.exp (-(c*κ*(Q (ii u):ℝ)/2)))
            ≤ 9 * ((4*C₀+1) * Real.exp (-(c*κ*(Q (ii u):ℝ)/2))) := by nlinarith [hE, hC0nn]
        have hq : 0 ≤ 4*C₀/(mm u : ℝ) := div_nonneg (by linarith [hC0nn]) (Nat.cast_nonneg _)
        linarith [hA', hq]
      have hup : (lyapAvg ω lam (E:ℂ) (mm u * Nf u) - lyapAvg ω lam (E:ℂ) (2 * (mm u * Nf u)))
          - (1/(mm u:ℝ)) * (lyapAvg ω lam (E:ℂ) (Nf u) - lyapAvg ω lam (E:ℂ) (2 * Nf u)) ≤ ef u :=
        le_trans (abs_le.mp h2).2 hef_ub
      show Df (u+1) ≤ Df u / (mm u : ℝ) + ef u
      rw [hDfapp (u+1), hDfapp u]
      show lyapAvg ω lam (E:ℂ) (mm u * Nf u) - lyapAvg ω lam (E:ℂ) (2 * (mm u * Nf u))
          ≤ (lyapAvg ω lam (E:ℂ) (Nf u) - lyapAvg ω lam (E:ℂ) (2 * Nf u)) / (mm u : ℝ) + ef u
      have hdiv : (1/(mm u:ℝ)) * (lyapAvg ω lam (E:ℂ) (Nf u) - lyapAvg ω lam (E:ℂ) (2 * Nf u))
          = (lyapAvg ω lam (E:ℂ) (Nf u) - lyapAvg ω lam (E:ℂ) (2 * Nf u)) / (mm u : ℝ) := by ring
      linarith [hup, hdiv]
  have key : ∀ s, 1 ≤ s → (∀ u < s, RTLInv l Df ef mm κ u) → s ≤ S →
      RTLInv l Df ef mm κ s := by
    intro s hs1 ih hsS
    have hcont : ∀ u < s, Df (u+1) ≤ Df u / (mm u : ℝ) + ef u := fun u hu =>
      (stage u (lt_of_lt_of_le hu hsS) (ih u hu).2.2.2.1 (ih u hu).2.2.2.2).2
    have hlow : ∀ u < s, l u ≤ l (u+1) + 2 * Df u + ef u := fun u hu =>
      (stage u (lt_of_lt_of_le hu hsS) (ih u hu).2.2.2.1 (ih u hu).2.2.2.2).1
    have hA : l 0 - 2 * (∑ u ∈ Finset.range s, Df u) - (∑ u ∈ Finset.range s, ef u) ≤ l s :=
      seq_lower hlow
    have hB : Df s ≤ Df 0 * (∏ u ∈ Finset.range s, (1 / (mm u : ℝ))) + (∑ u ∈ Finset.range s, ef u) :=
      seq_le_of_cont hmm1 hef_nn s hcont
    have hC : (∑ u ∈ Finset.range s, Df u) ≤ Df 0 + 3/2 * (Df 0 / (mm 0 : ℝ) + ∑ u ∈ Finset.range s, ef u) := by
      have hDM : 0 ≤ Df ((s-1)+1) := by rw [Nat.sub_add_cancel hs1]; exact hD_nn s
      have hrec : ∀ t < s-1, Df (t+2) ≤ Df (t+1)/3 + ef (t+1) := by
        intro t ht
        have h := hcont (t+1) (by omega)
        have h3 : (3:ℝ) ≤ (mm (t+1) : ℝ) := by exact_mod_cast hmm3 (t+1)
        have hnn : 0 ≤ Df (t+1) := hD_nn (t+1)
        have : Df (t+1)/(mm (t+1) : ℝ) ≤ Df (t+1)/3 := div_le_div_of_nonneg_left hnn (by norm_num) h3
        linarith
      have hb := D_sum_bound Df ef (s-1) hDM hrec
      have hsplit1 : (∑ u ∈ Finset.range s, Df u) = Df 0 + ∑ t ∈ Finset.range (s-1), Df (t+1) := by
        have hh := Finset.sum_range_succ' Df (s-1)
        rw [Nat.sub_add_cancel hs1] at hh
        linarith
      have hsplit2 : (∑ u ∈ Finset.range s, ef u) = ef 0 + ∑ t ∈ Finset.range (s-1), ef (t+1) := by
        have hh := Finset.sum_range_succ' ef (s-1)
        rw [Nat.sub_add_cancel hs1] at hh
        linarith
      have hD1 : Df 1 ≤ Df 0/(mm 0 : ℝ) + ef 0 := hcont 0 (by omega)
      rw [hsplit1, hsplit2]
      linarith [hb, hD1]
    have hsig : (∑ u ∈ Finset.range s, ef u) ≤ Ke * Real.exp (-(cκ * (Q 0 : ℝ) / 2)) :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hsS)
        (fun _ _ _ => hef_nn _)) hEfull
    have hD0lt' : Df 0 < l 0 / 10 := (ih 0 (by omega)).2.2.2.2
    have hD : 100 * κ < l s := by
      have h1 : l 0 - 2 * Df 0 - 3 * Df 0 / (mm 0 : ℝ) - 4 * (∑ u ∈ Finset.range s, ef u) ≤ l s := by
        have h1a : l 0 - 2 * (Df 0 + 3/2 * (Df 0 / (mm 0 : ℝ) + ∑ u ∈ Finset.range s, ef u))
            - (∑ u ∈ Finset.range s, ef u) ≤ l s := by linarith [hA, hC]
        have h1b : l 0 - 2 * (Df 0 + 3/2 * (Df 0 / (mm 0 : ℝ) + ∑ u ∈ Finset.range s, ef u))
            - (∑ u ∈ Finset.range s, ef u)
            = l 0 - 2 * Df 0 - 3 * Df 0 / (mm 0 : ℝ) - 4 * (∑ u ∈ Finset.range s, ef u) := by ring
        linarith [h1a, h1b]
      have h2 : 160 * κ < l 0 - 2 * Df 0 := by
        have h7 : 200 * κ < l 0 := by rw [hl0]; exact hlev
        linarith [hD0lt', h7]
      have h3 : 3 * Df 0 / (mm 0 : ℝ) ≤ κ := by
        have hexp : Real.exp (-(cκ * (Q 0 : ℝ) / 2)) ≤ Real.exp (-(cκ * T / 2)) :=
          Real.exp_le_exp.mpr (by linarith [mul_le_mul_of_nonneg_left hTle hcκpos.le])
        have h5 : 30 * C₀ * Real.exp (-(cκ * (Q 0 : ℝ) / 2)) ≤ 30 * C₀ * Real.exp (-(cκ * T / 2)) :=
          mul_le_mul_of_nonneg_left hexp (by linarith [hC0nn])
        linarith [hD0term, h5, h30_e]
      have h4 : 4 * (∑ u ∈ Finset.range s, ef u) ≤ 4 * κ := by
        have hexp : Real.exp (-(cκ * (Q 0 : ℝ) / 2)) ≤ Real.exp (-(cκ * T / 2)) :=
          Real.exp_le_exp.mpr (by linarith [mul_le_mul_of_nonneg_left hTle hcκpos.le])
        have h5 : Ke * Real.exp (-(cκ * (Q 0 : ℝ) / 2)) ≤ Ke * Real.exp (-(cκ * T / 2)) :=
          mul_le_mul_of_nonneg_left hexp hKepos.le
        linarith [hsig, h5, hKe_e]
      linarith [h1, h2, h3, h4]
    have hE : Df s < l s / 10 := by
      have hRs : (∏ u ∈ Finset.range s, (1 / (mm u : ℝ))) ≤ 1 / (mm 0 : ℝ) :=
        prod_inv_le_first hmm1 hs1
      have hDf0nn : 0 ≤ Df 0 := hD_nn 0
      have h1 : Df 0 * (∏ u ∈ Finset.range s, (1 / (mm u : ℝ))) ≤ 10 * C₀ * Real.exp (-(cκ * (Q 0 : ℝ) / 2)) := by
        have hm0 : Real.exp (cκ * (Q 0 : ℝ) / 2) / 10 ≤ (mm 0 : ℝ) := hmm0_ge
        have h2 : Df 0 * (∏ u ∈ Finset.range s, (1 / (mm u : ℝ))) ≤ Df 0 / (mm 0 : ℝ) :=
          le_trans (mul_le_mul_of_nonneg_left hRs hDf0nn) (by ring_nf; simp)
        have h3 : Df 0 / (mm 0 : ℝ) ≤ C₀ / (Real.exp (cκ * (Q 0 : ℝ) / 2) / 10) :=
          div_le_div₀ hC0nn hD0le (by positivity) hm0
        have h4 : C₀ / (Real.exp (cκ * (Q 0 : ℝ) / 2) / 10)
            = 10 * C₀ * Real.exp (-(cκ * (Q 0 : ℝ) / 2)) := by
          rw [Real.exp_neg]; field_simp
        linarith
      have h2 : Df s ≤ 10 * C₀ * Real.exp (-(cκ * (Q 0 : ℝ) / 2)) + Ke * Real.exp (-(cκ * (Q 0 : ℝ) / 2)) := by
        linarith [hB, h1, hsig]
      have hexp : Real.exp (-(cκ * (Q 0 : ℝ) / 2)) ≤ Real.exp (-(cκ * T / 2)) :=
        Real.exp_le_exp.mpr (by linarith [mul_le_mul_of_nonneg_left hTle hcκpos.le])
      have h5 : 10 * C₀ * Real.exp (-(cκ * (Q 0 : ℝ) / 2)) ≤ κ := by
        have h5a : 10 * C₀ * Real.exp (-(cκ * (Q 0 : ℝ) / 2)) ≤ 10 * C₀ * Real.exp (-(cκ * T / 2)) :=
          mul_le_mul_of_nonneg_left hexp (by linarith [hC0nn])
        linarith [h5a, h30_e]
      have h6 : Ke * Real.exp (-(cκ * (Q 0 : ℝ) / 2)) ≤ κ := by
        have h6a : Ke * Real.exp (-(cκ * (Q 0 : ℝ) / 2)) ≤ Ke * Real.exp (-(cκ * T / 2)) :=
          mul_le_mul_of_nonneg_left hexp hKepos.le
        linarith [h6a, hKe_e]
      linarith [hD, h2, h5, h6]
    exact ⟨hA, hB, hC, hD, hE⟩
  have hInv : ∀ s, s ≤ S → RTLInv l Df ef mm κ s := fun s =>
    Nat.strong_induction_on s (fun s ih hsS =>
      match Nat.eq_zero_or_pos s with
      | Or.inl h => h ▸ hInv0
      | Or.inr h => key s h (fun u hu => ih u hu (le_trans (le_of_lt hu) hsS)) hsS)
  have hstep_all : ∀ s, s < S → l s ≤ l (s+1) + 2 * Df s + ef s := fun s hs =>
    (stage s hs (hInv s (le_of_lt hs)).2.2.2.1 (hInv s (le_of_lt hs)).2.2.2.2).1
  have hpair_all : ∀ s, s < S → Df (s+1) ≤ Df s / (mm s : ℝ) + ef s := fun s hs =>
    (stage s hs (hInv s (le_of_lt hs)).2.2.2.1 (hInv s (le_of_lt hs)).2.2.2.2).2
  have harith := tower_lower_arith l Df ef mm S hS1 (fun s _ => hmm3 s) (fun s _ => hef_nn s)
    (fun s _ => hD_nn s) hstep_all hpair_all
  have hmmS_eq : mm (S-1) = rtlMM cκ Q k := by
    have hrt : rtli A cκ Q k N₀ (S-1) = k := by rw [← hiiapp (S-1)]; exact hiiS
    rw [hmmapp (S-1), hrt]
  have hdiv : Q k ∣ Nf S := by
    have hSdec : S = (S-1)+1 := by omega
    rw [hSdec, hNfsucc, hmmS_eq]
    exact dvd_mul_of_dvd_left (rtlMM_dvd cκ Q k) _
  set mf : ℕ := Nf S / Q k with hmfdef
  have hmfmul : mf * Q k = Nf S := Nat.div_mul_cancel hdiv
  have hmf1 : 1 ≤ mf := by
    rw [hmfdef, Nat.one_le_div_iff (by omega : 0 < Q k)]
    have h1 : Q k ≤ mm (S-1) := by
      rw [hmmS_eq]
      show Q k ≤ rtlMM cκ Q k
      unfold rtlMM
      calc Q k = Q k * 1 := (Nat.mul_one _).symm
        _ ≤ Q k * max 1 (Nat.floor (Real.exp (cκ * (Q k : ℝ) / 2) / (5 * (Q k : ℝ)))) :=
            Nat.mul_le_mul_left _ (le_max_left 1 _)
    have h2 : mm (S-1) ≤ Nf S := by
      have hSdec : S = (S-1)+1 := by omega
      rw [hSdec, hNfsucc]
      calc mm (S-1) = mm (S-1) * 1 := (Nat.mul_one _).symm
        _ ≤ mm (S-1) * Nf (S-1) := Nat.mul_le_mul_left _ (hNf_pos (S-1))
    exact le_trans h1 h2
  have hbound : ∀ (N : ℕ) (x : ℝ), uAvg ω lam (E : ℂ) N x ≤ C₀ := hLEB.2 E hEK ω
  have hclose := rat_excess_rate_explicit (P k) (Q k) hQk1 lam E C₀ hC0pos hbound mf hmf1
  have hmfmulR : (mf : ℝ) * (Q k : ℝ) = (Nf S : ℝ) := by rw [← Nat.cast_mul, hmfmul]
  have hlS : lyapAvg ω lam (E : ℂ) (mf * Q k) = l S := by rw [hmfmul, hlapp S]
  have hlS' : l S - lyap ω lam (E : ℂ)
      ≤ (C₀ * ((Q k : ℝ) + 1) + 1) * (1 + Real.log ((mf : ℝ) * (Q k : ℝ))) / ((mf : ℝ) * (Q k : ℝ)) := by
    have hc := hclose; rw [hlS] at hc; exact hc
  have hPS : 2 * lyapAvg ω lam (E : ℂ) (2 * N₀) - lyapAvg ω lam (E : ℂ) N₀ = l 0 - 2 * Df 0 := by
    rw [hDfapp 0, hl0, hNf0]; ring
  have hclosing : (C₀ * ((Q k : ℝ) + 1) + 1) * (1 + Real.log ((mf : ℝ) * (Q k : ℝ))) / ((mf : ℝ) * (Q k : ℝ))
      ≤ 2 * (C₀ + 1) * (1 + cκ / 4) * Bp * Real.exp (-(cκ * (Q 0 : ℝ) / 8)) := by
    rw [hmfmulR]
    have hM1 : 1 ≤ Real.exp (cκ * (Q k : ℝ) / 4) / 2 := by
      have h1 : Real.log 2 ≤ cκ * (Q k : ℝ) / 4 := by
        have h2 : 4 * Real.log 2 ≤ (Q k : ℝ) * cκ := by
          have h3 := (div_le_iff₀ hcκpos).mp hTlog2
          have h4 : (Q 0 : ℝ) ≤ (Q k : ℝ) := hQ0Q (Nat.zero_le k) le_rfl
          linarith [h3, mul_le_mul_of_nonneg_right (le_trans hTle h4) hcκpos.le]
        linarith
      have h2 : (2:ℝ) ≤ Real.exp (cκ * (Q k : ℝ) / 4) :=
        (Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 2)).mp h1
      linarith
    have hNfS_ge : Real.exp (cκ * (Q k : ℝ) / 4) / 2 ≤ (Nf S : ℝ) := by
      have h1 : Real.exp (cκ * (Q k : ℝ) / 2) / 10 ≤ (mm (S-1) : ℝ) := by
        rw [hmmS_eq]; exact rtlMM_ge cκ Q k (hbig2 k le_rfl)
      have h10 : (10:ℝ) ≤ Real.exp (cκ * (Q k : ℝ) / 4) :=
        (Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 10)).mp (by
          have h3 := (div_le_iff₀ hcκpos).mp hTlog10
          have h4 : (Q 0 : ℝ) ≤ (Q k : ℝ) := hQ0Q (Nat.zero_le k) le_rfl
          linarith [h3, mul_le_mul_of_nonneg_right (le_trans hTle h4) hcκpos.le])
      have hE : Real.exp (cκ * (Q k : ℝ) / 2)
          = Real.exp (cκ * (Q k : ℝ) / 4) * Real.exp (cκ * (Q k : ℝ) / 4) := by
        rw [← Real.exp_add]; congr 1; ring
      have h2 : Real.exp (cκ * (Q k : ℝ) / 4) / 2 ≤ Real.exp (cκ * (Q k : ℝ) / 2) / 10 := by
        rw [hE, div_le_div_iff₀ (by norm_num : (0:ℝ) < 2) (by norm_num : (0:ℝ) < 10)]
        nlinarith [h10, Real.exp_pos (cκ * (Q k : ℝ) / 4)]
      have h3 : mm (S-1) ≤ Nf S := by
        have hSdec : S = (S-1)+1 := by omega
        rw [hSdec, hNfsucc]
        calc mm (S-1) = mm (S-1) * 1 := (Nat.mul_one _).symm
          _ ≤ mm (S-1) * Nf (S-1) := Nat.mul_le_mul_left _ (hNf_pos (S-1))
      linarith [h1, h2, (by exact_mod_cast h3 : (mm (S-1) : ℝ) ≤ (Nf S : ℝ))]
    have hlogle := logDivDecayV2 hM1 hNfS_ge
    have hMlog : Real.log (Real.exp (cκ * (Q k : ℝ) / 4) / 2) = cκ * (Q k : ℝ) / 4 - Real.log 2 := by
      rw [Real.log_div (Real.exp_ne_zero _) (by norm_num : (2:ℝ) ≠ 0), Real.log_exp]
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h1 : (1 + Real.log (Nf S)) / (Nf S)
        ≤ 2 * (1 + cκ * (Q k : ℝ) / 4) * Real.exp (-(cκ * (Q k : ℝ) / 4)) := by
      refine le_trans hlogle ?_
      rw [hMlog, Real.exp_neg]
      have hEpos : 0 < Real.exp (cκ * (Q k : ℝ) / 4) := Real.exp_pos _
      calc (1 + (cκ * (Q k : ℝ) / 4 - Real.log 2)) / (Real.exp (cκ * (Q k : ℝ) / 4) / 2)
          = 2 * (1 + (cκ * (Q k : ℝ) / 4 - Real.log 2)) * (Real.exp (cκ * (Q k : ℝ) / 4))⁻¹ := by
            field_simp
        _ ≤ 2 * (1 + cκ * (Q k : ℝ) / 4) * (Real.exp (cκ * (Q k : ℝ) / 4))⁻¹ := by
            have hnn : 0 ≤ Real.log 2 * (Real.exp (cκ * (Q k : ℝ) / 4))⁻¹ :=
              mul_nonneg hlog2 (inv_nonneg.mpr (Real.exp_pos _).le)
            linarith [hnn]
    calc (C₀ * ((Q k : ℝ) + 1) + 1) * (1 + Real.log (Nf S)) / (Nf S)
        = (C₀ * ((Q k : ℝ) + 1) + 1) * ((1 + Real.log (Nf S)) / (Nf S)) := by ring
      _ ≤ (C₀ * ((Q k : ℝ) + 1) + 1)
            * (2 * (1 + cκ * (Q k : ℝ) / 4) * Real.exp (-(cκ * (Q k : ℝ) / 4))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 2 * (C₀ + 1) * (1 + cκ / 4) * ((Q k : ℝ) + 1) ^ 2 * Real.exp (-(cκ * (Q k : ℝ) / 4)) := by
          have hQk0 : 0 ≤ (Q k : ℝ) := Nat.cast_nonneg _
          have h1 : C₀ * ((Q k : ℝ) + 1) + 1 ≤ (C₀ + 1) * ((Q k : ℝ) + 1) := by linarith [hQk0]
          have h2 : 1 + cκ * (Q k : ℝ) / 4 ≤ (1 + cκ / 4) * ((Q k : ℝ) + 1) := by
            linarith [hQk0, hcκpos]
          have hE : 0 ≤ Real.exp (-(cκ * (Q k : ℝ) / 4)) := (Real.exp_pos _).le
          have h4 : (C₀ * ((Q k : ℝ) + 1) + 1) * (2 * (1 + cκ * (Q k : ℝ) / 4))
              ≤ 2 * (C₀ + 1) * (1 + cκ / 4) * ((Q k : ℝ) + 1) ^ 2 := by
            have h5 := mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ) ≤ 2))
              (by positivity) (by positivity)
            linarith [h5]
          have h6 : ((C₀ * ((Q k : ℝ) + 1) + 1) * (2 * (1 + cκ * (Q k : ℝ) / 4))) * Real.exp (-(cκ * (Q k : ℝ) / 4))
              ≤ (2 * (C₀ + 1) * (1 + cκ / 4) * ((Q k : ℝ) + 1) ^ 2) * Real.exp (-(cκ * (Q k : ℝ) / 4)) :=
            mul_le_mul_of_nonneg_right h4 hE
          have h7 : (C₀ * ((Q k : ℝ) + 1) + 1) * (2 * (1 + cκ * (Q k : ℝ) / 4) * Real.exp (-(cκ * (Q k : ℝ) / 4)))
              = ((C₀ * ((Q k : ℝ) + 1) + 1) * (2 * (1 + cκ * (Q k : ℝ) / 4))) * Real.exp (-(cκ * (Q k : ℝ) / 4)) := by ring
          have h8 : 2 * (C₀ + 1) * (1 + cκ / 4) * ((Q k : ℝ) + 1) ^ 2 * Real.exp (-(cκ * (Q k : ℝ) / 4))
              = (2 * (C₀ + 1) * (1 + cκ / 4) * ((Q k : ℝ) + 1) ^ 2) * Real.exp (-(cκ * (Q k : ℝ) / 4)) := by ring
          linarith [h6, h7, h8]
      _ ≤ 2 * (C₀ + 1) * (1 + cκ / 4) * Bp * Real.exp (-(cκ * (Q 0 : ℝ) / 8)) := by
          have hp := hpoly (Q k) (le_trans hTp (le_trans hTle (hQ0Q (Nat.zero_le k) le_rfl)))
          have hexp : Real.exp (-(cκ * (Q k : ℝ) / 4))
              = Real.exp (-(cκ / 8 * (Q k : ℝ))) * Real.exp (-(cκ * (Q k : ℝ) / 8)) := by
            rw [← Real.exp_add]; congr 1; ring
          have hexple : Real.exp (-(cκ * (Q k : ℝ) / 8)) ≤ Real.exp (-(cκ * (Q 0 : ℝ) / 8)) :=
            Real.exp_le_exp.mpr (by have hh : (Q 0 : ℝ) ≤ (Q k : ℝ) := hQ0Q (Nat.zero_le k) le_rfl; linarith [mul_le_mul_of_nonneg_left hh hcκpos.le])
          have hpos : 0 ≤ 2 * (C₀ + 1) * (1 + cκ / 4) := by
            have h1 : 0 ≤ C₀ + 1 := by linarith
            have h2 : 0 ≤ 1 + cκ / 4 := by linarith
            have h3 : 0 ≤ (C₀ + 1) * (1 + cκ / 4) := mul_nonneg h1 h2
            linarith
          have hposB : 0 ≤ 2 * (C₀ + 1) * (1 + cκ / 4) * Bp := by
            have h3 : 0 ≤ 2 * (C₀ + 1) * (1 + cκ / 4) * Bp :=
              mul_nonneg hpos hBppos.le
            linarith
          rw [hexp]
          have hstep : 2 * (C₀ + 1) * (1 + cκ / 4) * (((Q k : ℝ) + 1) ^ 2 * Real.exp (-(cκ / 8 * (Q k : ℝ))))
              ≤ 2 * (C₀ + 1) * (1 + cκ / 4) * Bp :=
            mul_le_mul_of_nonneg_left hp hpos
          have hE2 : 0 ≤ Real.exp (-(cκ * (Q k : ℝ) / 8)) := (Real.exp_pos _).le
          calc 2 * (C₀ + 1) * (1 + cκ / 4) * ((Q k : ℝ) + 1) ^ 2
                * (Real.exp (-(cκ / 8 * (Q k : ℝ))) * Real.exp (-(cκ * (Q k : ℝ) / 8)))
              = (2 * (C₀ + 1) * (1 + cκ / 4) * (((Q k : ℝ) + 1) ^ 2 * Real.exp (-(cκ / 8 * (Q k : ℝ)))))
                * Real.exp (-(cκ * (Q k : ℝ) / 8)) := by ring
            _ ≤ (2 * (C₀ + 1) * (1 + cκ / 4) * Bp) * Real.exp (-(cκ * (Q k : ℝ) / 8)) :=
                mul_le_mul_of_nonneg_right hstep hE2
            _ ≤ 2 * (C₀ + 1) * (1 + cκ / 4) * Bp * Real.exp (-(cκ * (Q 0 : ℝ) / 8)) :=
                mul_le_mul_of_nonneg_left hexple hposB
  have he1 : Real.exp (-(cκ * (Q 0 : ℝ) / 2)) ≤ Real.exp (-(cκ * (Q 0 : ℝ) / 8)) :=
    Real.exp_le_exp.mpr (by have h0 : 0 ≤ (Q 0 : ℝ) := Nat.cast_nonneg _; linarith [mul_nonneg hcκpos.le h0])
  have hD0term' : 3 * Df 0 / (mm 0 : ℝ) ≤ 30 * C₀ * Real.exp (-(cκ * (Q 0 : ℝ) / 8)) :=
    le_trans hD0term (mul_le_mul_of_nonneg_left he1 (by positivity))
  have hEfull' : 7 * (∑ s ∈ Finset.range S, ef s) ≤ 7 * Ke * Real.exp (-(cκ * (Q 0 : ℝ) / 8)) := by
    have h1 : 7 * (∑ s ∈ Finset.range S, ef s) ≤ 7 * (Ke * Real.exp (-(cκ * (Q 0 : ℝ) / 2))) :=
      mul_le_mul_of_nonneg_left hEfull (by norm_num)
    have h2 : Ke * Real.exp (-(cκ * (Q 0 : ℝ) / 2)) ≤ Ke * Real.exp (-(cκ * (Q 0 : ℝ) / 8)) :=
      mul_le_mul_of_nonneg_left he1 hKepos.le
    linarith [h1, h2]
  have hfin : 2 * lyapAvg ω lam (E : ℂ) (2 * N₀) - lyapAvg ω lam (E : ℂ) N₀
      ≤ lyap ω lam (E : ℂ) + (7 * Ke + 30 * C₀ + 2 * (C₀ + 1) * (1 + cκ / 4) * Bp)
        * Real.exp (-(cκ * (Q 0 : ℝ) / 8)) := by
    have h1 : 2 * lyapAvg ω lam (E : ℂ) (2 * N₀) - lyapAvg ω lam (E : ℂ) N₀
        ≤ lyap ω lam (E : ℂ) + ((C₀ * ((Q k : ℝ) + 1) + 1) * (1 + Real.log ((mf : ℝ) * (Q k : ℝ))) / ((mf : ℝ) * (Q k : ℝ)))
          + 30 * C₀ * Real.exp (-(cκ * (Q 0 : ℝ) / 8)) + 7 * Ke * Real.exp (-(cκ * (Q 0 : ℝ) / 8)) := by
      linarith [hPS, harith, hlS', hD0term', hEfull']
    linarith [h1, hclosing]
  exact hfin

end Work.TMC7Core.Scale
