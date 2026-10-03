import Mathlib
import Submission.Work.FIChain.BprimeWindowIntegrated

namespace Work.FIPiChain.P1Aw

open Work.FIChain
open Finset MeasureTheory
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
# `BprimeWindowInt_ge` — the integrated `(B′)`-window at every large `B`

`Work.FIChain.BprimeWindowIntegrated` proves the integrated `Π`-free `(B′)`-window from
`Prop41StatementPiBig`, but at a `B` that is *output* by the proof (the `B` of the pointwise
`(B*)`-input `Aw_le_of_PiBig`).  The consumers (the `PrimSumSigned` endgame at a free `B`) need
the window for *every* `B ≥ B₁`, with `B₁` a fixed constant.

The passage is exactly the one recorded in the design (`PIREMOVAL_LEAD.md` §3 P1): the only
`B`-dependent inputs of `BprimeWindowIntegrated` are

* the pointwise `(B*)`-input `Aw ≤ KA·Ã·L^{-2^26}` on `u ∈ [lo/D, hi]`, whose range condition is
  `u ≤ sc x B·(e·Yc x B)`;
* the range lemmas `window_margin_sharp B`, `Yc_lower_sharp B` and `bprime_window_tail_le B`,
  which hold for *every* `B > 0`.

Since `sc x B·Yc x B = √x/L^{B+2}` is *antitone* in `B` for `L = log x ≥ 1`
(`sc_mul_Yc_eq`, `sc_mul_Yc_antitone` below), the range condition for `B` is *implied* by the one
for `B₁ ≤ B`; hence the same `KA` works for every `B ≥ B₁`
(`Aw_le_of_PiBig_uniformB`).  Everything else carries over verbatim; only `KT` (the Rankin tail
constant of `bprime_window_tail_le B`) is allowed to depend on `B`, which is harmless because the
constant `K` of the conclusion is existentially quantified *inside* the `∀ B` binder.
-/

/-- `sc x B · Yc x B = √x / (log x)^{B+2}`: the `B`-dependence of the window top in closed form
(the `2^{Jc}` of `sc` and the `1/(sc·L^{B+2})` of `Yc` cancel). -/
private theorem sc_mul_Yc_eq (x : ℕ) {B : ℝ} (hL : 1 ≤ Real.log (x : ℝ)) :
    sc x B * Yc x B = Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ (B + 2) := by
  have hLpos : 0 < Real.log (x : ℝ) := lt_of_lt_of_le one_pos hL
  have hscne : sc x B ≠ 0 := by rw [sc]; positivity
  have hLpne : (Real.log (x : ℝ)) ^ (B + 2) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hLpos _)
  rw [Yc]
  field_simp

/-- `sc x B · Yc x B` is antitone in `B` (for `log x ≥ 1`): `√x/L^{B+2}` decreases in `B`. -/
private theorem sc_mul_Yc_antitone (x : ℕ) (hL : 1 ≤ Real.log (x : ℝ)) :
    Antitone (fun B : ℝ => sc x B * Yc x B) := by
  intro B B' hBB'
  have hLpos : 0 < Real.log (x : ℝ) := lt_of_lt_of_le one_pos hL
  change sc x B' * Yc x B' ≤ sc x B * Yc x B
  rw [sc_mul_Yc_eq x hL, sc_mul_Yc_eq x hL]
  refine div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (Real.rpow_pos_of_pos hLpos _) ?_
  exact Real.rpow_le_rpow_of_exponent_le hL (by linarith)

/-- **The pointwise `(B*)`-input, uniform in `B`.**  `Aw_le_of_PiBig` produces the `(B*)`-bound
for the single `B` of the range condition `u ≤ sc x B·(e·Yc x B)`; because that range is
antitone in `B`, the same constant `K` works for every `B ≥ B₁`. -/
private theorem Aw_le_of_PiBig_uniformB (h : Work.FITop4.Prop41StatementPiBig) (η : ℝ)
    (hη : 0 < η) (hη32 : η < 3 / 32) :
    ∃ B₁ K : ℝ, ∃ x₀ : ℕ, 0 < B₁ ∧ 0 < K ∧ ∀ B : ℝ, B₁ ≤ B → ∀ x : ℕ, x₀ ≤ x → ∀ u : ℝ,
      (x : ℝ) ^ ((1 : ℝ) / 4 + η / 2) + 2 < u →
      u ≤ sc x B * (Real.exp 1 * Yc x B) →
      Aw x (Pzc x) u
        ≤ K * AcountAtilC x * (Real.log (x : ℝ)) ^ (-((2 : ℝ) ^ (26 : ℕ))) := by
  obtain ⟨B, K, x₀, hBpos, hKpos, hAw⟩ := Aw_le_of_PiBig h η hη hη32
  refine ⟨B, K, max x₀ 3, hBpos, hKpos, ?_⟩
  intro B' hB' x hx u hulo huhi
  have hx₀ : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx3 : 3 ≤ x := le_trans (le_max_right _ _) hx
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hL1 : (1 : ℝ) ≤ Real.log (x : ℝ) := by
    rw [Real.le_log_iff_exp_le hxpos]
    have h3 : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx3
    linarith [Real.exp_one_lt_three]
  have hmono : sc x B' * (Real.exp 1 * Yc x B') ≤ sc x B * (Real.exp 1 * Yc x B) := by
    rw [show sc x B' * (Real.exp 1 * Yc x B') = Real.exp 1 * (sc x B' * Yc x B') by ring,
      show sc x B * (Real.exp 1 * Yc x B) = Real.exp 1 * (sc x B * Yc x B) by ring]
    exact mul_le_mul_of_nonneg_left (sc_mul_Yc_antitone x hL1 hB') (Real.exp_pos 1).le
  exact hAw x hx₀ u hulo (le_trans huhi hmono)

/-- **The integrated `(B′)`-window, uniformly in `B`.**  Verbatim copy of
`Work.FIChain.BprimeWindowIntegrated` at `η = 1/64`, with the pointwise `(B*)`-input replaced by
its `B`-uniform form: the window is established for every `B ≥ B₁`, with the constant `K`
(existentially quantified inside the `∀ B`) allowed to depend on `B` through the Rankin tail. -/
theorem BprimeWindowInt_ge (h : Work.FITop4.Prop41StatementPiBig) :
    ∃ B₁ : ℝ, 0 < B₁ ∧ ∀ B : ℝ, B₁ ≤ B → ∃ K : ℝ, ∃ x₀ : ℕ, 0 < K ∧ ∀ x : ℕ, x₀ ≤ x →
      Work.FIChain.BprimeWindowInt Work.FIChain.atilc x Work.FIChain.wc
        (K * Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-(4 : ℤ)))
        (Work.FIChain.Yc x B / (Work.FIChain.Deltac x : ℝ))
        (Work.FIChain.sc x B * (Real.exp 1 * Work.FIChain.Yc x B)) := by
  obtain ⟨B₁, KA, xA, hB₁pos, hKApos, hAwPi⟩ :=
    Aw_le_of_PiBig_uniformB h (1 / 64) (by norm_num) (by norm_num)
  refine ⟨B₁, hB₁pos, ?_⟩
  intro B hB
  have hBpos : 0 < B := lt_of_lt_of_le hB₁pos hB
  have hη : (0 : ℝ) < 1 / 64 := by norm_num
  have hη32 : (1 : ℝ) / 64 < 3 / 32 := by norm_num
  -- the three inputs
  obtain ⟨CB, hCBpos, xB, hBwAll⟩ := Xf_Bw_le
  have hκ40pos : (0 : ℝ) < (2 : ℝ) ^ (40 : ℕ) := by positivity
  have hκ30 : (2 : ℝ) ^ (30 : ℕ) ≤ (2 : ℝ) ^ (40 : ℕ) := by norm_num
  obtain ⟨KT, xT, hKTpos, htail⟩ := bprime_window_tail_le B ((2 : ℝ) ^ (40 : ℕ)) hBpos hκ30
  -- the range conditions
  have hKEv : ∀ᶠ x : ℕ in Filter.atTop,
      ((x : ℝ) ^ ((1 : ℝ) / 4 + (1 / 64) / 2) + 2) * (Dpi x ((2 : ℝ) ^ (40 : ℕ)) : ℝ)
          < Yc x B / (Deltac x : ℝ)
      ∧ (x : ℝ) ^ ((5 : ℝ) / 16) ≤ Yc x B
      ∧ (1 : ℝ) ≤ Work.FITop.Lam1 x
      ∧ (Deltac x : ℝ) ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 100)
      ∧ (2 : ℝ) ≤ (x : ℝ) ^ ((5 : ℝ) / 16 - 1 / 100)
      ∧ (Dpi x ((2 : ℝ) ^ (40 : ℕ)) : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2)
      ∧ Real.exp 1 ≤ Real.log (x : ℝ)
      ∧ (1 : ℝ) ≤ Real.log (x : ℝ) := by
    filter_upwards [window_margin_sharp B ((2 : ℝ) ^ (40 : ℕ)) hBpos hκ40pos (1 / 64) hη hη32,
      Yc_lower_sharp B hBpos,
      Work.FITop.FI_ev_Lam1_ge_one,
      Work.FITop.FI_ev_Delta1_le_two_Lam1,
      Work.FITop.FI_ev_rpow_ge_nat ((5 : ℝ) / 16 - 1 / 100) (by norm_num) 2,
      eventually_Dpi_le_rpow ((2 : ℝ) ^ (40 : ℕ)) (1 / 2) hκ40pos (by norm_num),
      Work.FITop.FI_ev_log_ge_nat (Real.exp 1),
      Work.FITop.FI_ev_log_ge_nat 1] with x hwin hYc hLam1 hDel hpow hDle hloge hlog1
    refine ⟨hwin, hYc, hLam1, ?_, hpow, hDle, hloge, hlog1⟩
    simpa only [Deltac, Work.FITop.Delta1, Work.FITop.Lam1] using hDel
  rw [Filter.eventually_atTop] at hKEv
  obtain ⟨xE, hxE⟩ := hKEv
  refine ⟨2 * Real.sqrt (KA * CB) + KT, max (max xA xB) (max xT xE), by positivity, ?_⟩
  intro x hx
  have hxA : xA ≤ x :=
    le_trans (le_trans (le_max_left xA xB) (le_max_left (max xA xB) (max xT xE))) hx
  have hxB : xB ≤ x :=
    le_trans (le_trans (le_max_right xA xB) (le_max_left (max xA xB) (max xT xE))) hx
  have hxT : xT ≤ x :=
    le_trans (le_trans (le_max_left xT xE) (le_max_right (max xA xB) (max xT xE))) hx
  have hxE' : xE ≤ x :=
    le_trans (le_trans (le_max_right xT xE) (le_max_right (max xA xB) (max xT xE))) hx
  obtain ⟨hwin, hYclow, hLam1, hDelle, hpow2, hDle, hloge, hlog1⟩ := hxE x hxE'
  -- the parameters
  let κ : ℝ := (2 : ℝ) ^ (40 : ℕ)
  let D : ℝ := (Dpi x κ : ℝ)
  let Pz : ℕ := Pzc x
  let lo : ℝ := Yc x B / (Deltac x : ℝ)
  let hi : ℝ := sc x B * (Real.exp 1 * Yc x B)
  let L : ℝ := Real.log (x : ℝ)
  have hxpos : (0 : ℝ) < (x : ℝ) :=
    lt_trans one_pos ((Real.log_pos_iff (Nat.cast_nonneg x)).mp (lt_of_lt_of_le one_pos hlog1))
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hlog1
  have hsc_pos : 0 < sc x B := by rw [sc]; positivity
  have hLp_pos : 0 < L ^ (B + 2) := Real.rpow_pos_of_pos hLpos _
  have hYc_pos : 0 < Yc x B := by
    rw [Yc]
    exact div_pos (Real.sqrt_pos.mpr hxpos) (mul_pos hsc_pos (Real.rpow_pos_of_pos hLpos _))
  have hDel1 : 1 ≤ Deltac x := Nat.ceil_pos.mpr (lt_of_lt_of_le one_pos (by
    simpa only [Deltac, Work.FITop.Delta1] using hLam1))
  have hDeltac_pos : 0 < (Deltac x : ℝ) := by exact_mod_cast (by omega : 0 < Deltac x)
  have hDpi1 : 1 ≤ Dpi x κ := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hD1 : 1 ≤ D := by
    rw [show D = (Dpi x κ : ℝ) from rfl]
    exact_mod_cast hDpi1
  have hDpos : 0 < D := lt_of_lt_of_le one_pos hD1
  have hlo_pos : 0 < lo := by
    rw [show lo = Yc x B / (Deltac x : ℝ) from rfl]
    exact div_pos hYc_pos hDeltac_pos
  -- the identity `hi = e·√x/L^{B+2}`
  have hhi_eq : hi = Real.exp 1 * Real.sqrt (x : ℝ) / L ^ (B + 2) := by
    show sc x B * (Real.exp 1 * (Real.sqrt (x : ℝ) / (sc x B * L ^ (B + 2))))
      = Real.exp 1 * Real.sqrt (x : ℝ) / L ^ (B + 2)
    have hscne : sc x B ≠ 0 := ne_of_gt hsc_pos
    have hLpne : L ^ (B + 2) ≠ 0 := ne_of_gt hLp_pos
    field_simp
  have hhi_pos : 0 < hi := by
    rw [hhi_eq]
    exact div_pos (mul_pos (Real.exp_pos 1) (Real.sqrt_pos.mpr hxpos)) hLp_pos
  have hloD_pos : 0 < lo / D := div_pos hlo_pos hDpos
  -- `e ≤ L^{B+2}`, whence `hi ≤ √x`
  have hexp_le : Real.exp 1 ≤ L ^ (B + 2) := by
    have h1 : Real.exp 1 ≤ L ^ (2 : ℝ) := by
      rw [Real.rpow_two]
      nlinarith [hloge, hlog1, Real.exp_pos 1]
    exact h1.trans (Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith [hBpos]))
  have hhi_le : hi ≤ Real.sqrt (x : ℝ) := by
    rw [hhi_eq, div_le_iff₀ hLp_pos]
    calc Real.exp 1 * Real.sqrt (x : ℝ) = Real.sqrt (x : ℝ) * Real.exp 1 := by ring
      _ ≤ Real.sqrt (x : ℝ) * L ^ (B + 2) :=
          mul_le_mul_of_nonneg_left hexp_le (Real.sqrt_nonneg _)
  have hD_le : D ≤ Real.sqrt (x : ℝ) := by
    rw [show D = (Dpi x κ : ℝ) from rfl, Real.sqrt_eq_rpow]
    exact hDle
  -- `lo ≥ 1`
  have hDeltac_le : (Deltac x : ℝ) ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 100) := hDelle
  have hx100_le : 2 * (x : ℝ) ^ ((1 : ℝ) / 100) ≤ (x : ℝ) ^ ((5 : ℝ) / 16) := by
    calc 2 * (x : ℝ) ^ ((1 : ℝ) / 100)
        ≤ (x : ℝ) ^ ((5 : ℝ) / 16 - 1 / 100) * (x : ℝ) ^ ((1 : ℝ) / 100) :=
          mul_le_mul_of_nonneg_right hpow2 (Real.rpow_nonneg hxpos.le _)
      _ = (x : ℝ) ^ ((5 : ℝ) / 16) := by
          rw [← Real.rpow_add hxpos]
          norm_num
  have hlo_ge_one : 1 ≤ lo := by
    rw [show lo = Yc x B / (Deltac x : ℝ) from rfl, one_le_div hDeltac_pos]
    exact le_trans (le_trans hDeltac_le hx100_le) hYclow
  -- `lo ≤ hi`
  have hhi_eq2 : hi = Real.exp 1 * lo * (sc x B * (Deltac x : ℝ)) := by
    rw [hhi_eq, show lo = Yc x B / (Deltac x : ℝ) from rfl, Yc]
    have hscne : sc x B ≠ 0 := ne_of_gt hsc_pos
    have hLpne : L ^ (B + 2) ≠ 0 := ne_of_gt hLp_pos
    have hDne : (Deltac x : ℝ) ≠ 0 := ne_of_gt hDeltac_pos
    field_simp
    ring
  have hlo_le_hi : lo ≤ hi := by
    rw [hhi_eq2]
    have hsc1 : (1 : ℝ) ≤ sc x B := by rw [sc]; exact one_le_pow₀ (by norm_num)
    have hDe1 : (1 : ℝ) ≤ (Deltac x : ℝ) := by exact_mod_cast hDel1
    have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have h1 : (1 : ℝ) ≤ Real.exp 1 * (sc x B * (Deltac x : ℝ)) := by
      have h2 : (1 : ℝ) * 1 ≤ sc x B * (Deltac x : ℝ) :=
        mul_le_mul hsc1 hDe1 zero_le_one (le_trans zero_le_one hsc1)
      nlinarith [he1, h2]
    calc lo = lo * 1 := (mul_one lo).symm
      _ ≤ lo * (Real.exp 1 * (sc x B * (Deltac x : ℝ))) :=
          mul_le_mul_of_nonneg_left h1 hlo_pos.le
      _ = Real.exp 1 * lo * (sc x B * (Deltac x : ℝ)) := by ring
  have hloD_le_hi : lo / D ≤ hi :=
    le_trans (div_le_self hlo_pos.le hD1) hlo_le_hi
  -- the `(B*)`-input applies on the whole range `[lo/D, hi]`
  have hloD_gt : (x : ℝ) ^ ((1 : ℝ) / 4 + (1 / 64) / 2) + 2 < lo / D := by
    rw [lt_div_iff₀ hDpos]
    exact hwin
  have hAwr : ∀ u ∈ Set.Icc (lo / D) hi,
      Aw x Pz u ≤ KA * AcountAtilC x * (Real.log (x : ℝ)) ^ (-((2 : ℝ) ^ (26 : ℕ))) := by
    intro u hu
    exact hAwPi B hB x hxA u (lt_of_lt_of_le hloD_gt hu.1) hu.2
  have hBwr : ∀ u ∈ Set.Icc (lo / D) hi,
      Bw x Pz u ≤ CB * AcountAtilC x * (Real.log (x : ℝ)) ^ (262144 : ℕ) :=
    fun u _ => hBwAll x Pz hxB u
  -- the log-length
  have hratio : hi / (lo / D) ≤ (x : ℝ) := by
    have h1 : hi * D ≤ (x : ℝ) := by
      have h2 : hi * D ≤ Real.sqrt (x : ℝ) * Real.sqrt (x : ℝ) :=
        mul_le_mul hhi_le hD_le (le_of_lt hDpos) (Real.sqrt_nonneg _)
      rwa [Real.mul_self_sqrt hxpos.le] at h2
    rw [div_div_eq_mul_div, div_le_iff₀ hlo_pos]
    nlinarith [h1, hlo_ge_one, hxpos]
  have hR : Real.log hi - Real.log (lo / D) ≤ 2 * Real.log (x : ℝ) := by
    rw [← Real.log_div hhi_pos.ne' hloD_pos.ne']
    have h2 : Real.log (hi / (lo / D)) ≤ Real.log (x : ℝ) :=
      Real.log_le_log (div_pos hhi_pos hloD_pos) hratio
    linarith [hlog1]
  -- the pointwise split of the `b₁`-sum
  have hunion : s1F Pz D ∪ s2F Pz x κ = (ProdP Pz).divisors := by
    ext b₁
    simp only [s1F, s2F, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro hb
      by_cases hle : ((b₁ : ℝ)) ≤ D
      · exact Or.inl ⟨hb, hle⟩
      · exact Or.inr ⟨hb, by
          have hlt : (Dpi x κ : ℝ) < (b₁ : ℝ) := by
            rw [show D = (Dpi x κ : ℝ) from rfl] at hle
            exact lt_of_not_ge hle
          exact_mod_cast hlt⟩
  have hdisj : Disjoint (s1F Pz D) (s2F Pz x κ) := by
    rw [Finset.disjoint_left]
    intro b hb1 hb2
    rw [s1F, Finset.mem_filter] at hb1
    rw [s2F, Finset.mem_filter] at hb2
    have h1 : (b : ℝ) ≤ (Dpi x κ : ℝ) := hb1.2
    have h2 : (Dpi x κ : ℝ) < (b : ℝ) := by exact_mod_cast hb2.2
    exact absurd h1 (not_le.mpr h2)
  have hpt : ∀ t : ℝ, (∑ m ∈ Finset.Icc 1 x, wc m * |Submission.ASP.Xsum atilc x m t (2 * t)|)
      ≤ (∑ m ∈ Finset.Icc 1 x, wc m * |∑ b₁ ∈ s1F Pz D,
            (ArithmeticFunction.moebius b₁ : ℝ) * Xf x Pz (m * b₁) (t / b₁)|)
        + (∑ m ∈ Finset.Icc 1 x, wc m * |∑ b₁ ∈ s2F Pz x κ,
            (ArithmeticFunction.moebius b₁ : ℝ) * Xf x Pz (m * b₁) (t / b₁)|) := by
    intro t
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun m hm => ?_)
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    rw [Xsum_eq_sum_Xf x Pz m hm1 t, ← hunion, Finset.sum_union hdisj]
    refine le_trans (mul_le_mul_of_nonneg_left (abs_add_le _ _) (wc_nonneg m)) (le_of_eq ?_)
    rw [mul_add]
  -- the integral bound
  have hF1int := integrable_G1 x Pz D hlo_pos hlo_le_hi
  have hF2int := integrable_G2 x Pz κ hlo_pos hlo_le_hi
  have hsplit : (∫ t in lo..hi,
        (∑ m ∈ Finset.Icc 1 x, wc m * |Submission.ASP.Xsum atilc x m t (2 * t)|) / t)
      ≤ (∫ t in lo..hi, (∑ m ∈ Finset.Icc 1 x, wc m * |∑ b₁ ∈ s1F Pz D,
            (ArithmeticFunction.moebius b₁ : ℝ) * Xf x Pz (m * b₁) (t / b₁)|) / t)
        + (∫ t in lo..hi, (∑ m ∈ Finset.Icc 1 x, wc m * |∑ b₁ ∈ s2F Pz x κ,
            (ArithmeticFunction.moebius b₁ : ℝ) * Xf x Pz (m * b₁) (t / b₁)|) / t) := by
    refine le_trans (intervalIntegral.integral_mono_on hlo_le_hi
      (integrable_Xsum_sum x hlo_pos hlo_le_hi) (hF1int.add hF2int)
      (fun t ht => ?_)) (le_of_eq (intervalIntegral.integral_add hF1int hF2int))
    refine le_trans (div_le_div_of_nonneg_right (hpt t) (le_trans hlo_pos.le ht.1)) ?_
    rw [add_div]
  have hF1b := bprime_window_main_le x Pz D lo hi hDpos hlo_pos hloD_le_hi hlo_le_hi
    KA CB hKApos.le hCBpos.le hAwr hBwr hlog1 hR
  have hF2b : (∫ t in lo..hi, (∑ m ∈ Finset.Icc 1 x, wc m * |∑ b₁ ∈ s2F Pz x κ,
        (ArithmeticFunction.moebius b₁ : ℝ) * Xf x Pz (m * b₁) (t / b₁)|) / t)
      ≤ KT * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(4 : ℤ)) := htail x hxT
  have hmain : (∫ t in lo..hi,
        (∑ m ∈ Finset.Icc 1 x, wc m * |Submission.ASP.Xsum atilc x m t (2 * t)|) / t)
      ≤ (2 * Real.sqrt (KA * CB) + KT) * AcountAtilC x * L ^ (-(4 : ℤ)) := by
    refine le_trans hsplit (le_trans (add_le_add hF1b hF2b) (le_of_eq ?_))
    rw [show L = Real.log (x : ℝ) from rfl]
    ring
  rw [BprimeWindowInt]
  exact hmain

end

end Work.FIPiChain.P1Aw
