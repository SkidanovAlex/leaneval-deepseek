import Mathlib
import Submission.Work.OddVolterra.WinData.wide_defs
import Submission.Work.OddVolterra.WinData.Kden_jets_ext
import Submission.Work.OddExistence.Manifest.zrad_sharp
import Submission.Work.OddVolterra.Window.KvecDefs
import Submission.Work.OddExistence.Manifest.aw_toolkit
import Submission.Work.OddVolterra.Existence.aw_t_jet

/-!
# Box membership and derivative bound for the jet curve on the *wide* slope square

This file discharges `WinData.kjet_mem_boxW_deriv`, the wide-square analogue of
`Window.KJet_mem_box_deriv`:

for a perturbation `h` supported in `[1 - 2τ, 1 - τ]` with `|h^{(k)}| ≤ 1/100` for `k ≤ n+2`,
`σ, a ∈ [1/4, 19/20]`, `z 0, z 1 ≥ 1/5` and `|z i| ≤ 2`, the jet curve `u ↦ KJet n h σ z u`
takes its value at `a` in the wide box `KJboxW n (KJbz n)` and its `u`-derivative is bounded
by `KJbz n`.

Route (mirroring `Window/KJet_mem_box_deriv.lean`, whose private estimates are re-proved here for
the wider square `[1/4, 19/20]²`):

* the radicand data (`1/100 ≤ krad ≤ 20`, `|∂_a krad| ≤ 20`) is `WinData.krad_jets` with the
  general slope box `A = 1/4`;
* the radicand *jet* bound `|∂_a^j Zrad| ≤ 2 ^ (n+2) * 100 = KJbz n` is proved here from scratch:
  the only `∃`-form version available (`ZS.Zrad_jet_bounds_sharp`) hides the constant, so the
  elementary Leibniz/affine estimate is redone with the explicit constant `201/100` for the jets
  of the affine function `v ↦ line h v t`, which is valid on the whole square `[1/4, 19/20]²`.
-/

namespace Work.OddVolterra.WinData

open Work.OddVolterra
open scoped Topology ContDiff

noncomputable section

/-! ## Elementary one-dimensional estimates -/

/-- `|x - y| ≤ |x| + |y|`. -/
private lemma kw_abs_sub_le_abs_add (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  simpa [sub_eq_add_neg] using abs_add_le x (-y)

/-- The jets of `v ↦ v * c`. -/
private lemma kw_iteratedDeriv_mul_right (c a : ℝ) (k : ℕ) :
    iteratedDeriv k (fun v : ℝ => v * c) a = if k = 0 then a * c else if k = 1 then c else 0 := by
  have he : (fun v : ℝ => v * c) = fun v => c * id v := by
    funext v; rw [id_eq]; ring
  rw [he, iteratedDeriv_const_mul (c := c) (f := id) contDiffAt_id, iteratedDeriv_id]
  split_ifs <;> ring

/-- The jets of the affine function `v ↦ v * t + h v` in terms of the jets of `h`. -/
private lemma kw_iteratedDeriv_affine {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (t a : ℝ)
    (k : ℕ) :
    iteratedDeriv k (fun v : ℝ => v * t + h v) a
      = iteratedDeriv k (fun v : ℝ => v * t) a + iteratedDeriv k h a := by
  have h1 : ContDiffAt ℝ (k : ℕ) (fun v : ℝ => v * t) a := by fun_prop
  have h2 : ContDiffAt ℝ (k : ℕ) h a := hh.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  change iteratedDeriv k ((fun v : ℝ => v * t) + h) a = _
  rw [iteratedDeriv_add h1 h2]

/-- Jet bound for the affine function `v ↦ v * t + h v` on `|a| ≤ 1`. -/
private lemma kw_affine_jet_le {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {δ t a : ℝ}
    (ha : |a| ≤ 1) {k : ℕ} (hk : |iteratedDeriv k h a| ≤ δ) :
    |iteratedDeriv k (fun v : ℝ => v * t + h v) a| ≤ |t| + δ := by
  have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) hk
  rw [kw_iteratedDeriv_affine hh t a k]
  have h1 : |iteratedDeriv k (fun v : ℝ => v * t) a| ≤ |t| := by
    rw [kw_iteratedDeriv_mul_right]
    split_ifs with h0 h1'
    · calc |a * t| = |a| * |t| := abs_mul a t
        _ ≤ 1 * |t| := mul_le_mul_of_nonneg_right ha (abs_nonneg t)
        _ = |t| := by ring
    · exact le_rfl
    · simpa using abs_nonneg t
  calc |iteratedDeriv k (fun v : ℝ => v * t) a + iteratedDeriv k h a|
      ≤ |iteratedDeriv k (fun v : ℝ => v * t) a| + |iteratedDeriv k h a| := abs_add_le _ _
    _ ≤ |t| + δ := add_le_add h1 hk

/-- Smoothness of the affine function `v ↦ v * t + h v` at any finite order. -/
private lemma kw_contDiffAt_affine {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (t a : ℝ)
    (N : ℕ) : ContDiffAt ℝ (N : ℕ) (fun v : ℝ => v * t + h v) a := by
  have h1 : ContDiffAt ℝ (N : ℕ) (fun v : ℝ => v * t) a := by fun_prop
  have h2 : ContDiffAt ℝ (N : ℕ) h a := hh.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  simpa using h1.add h2

/-! ## The radicand-jet bound on the wide square -/

/-- **The explicit radicand-jet bound on the wide square `σ, a ∈ [1/4, 19/20]`.**

This is the wide analogue of `kjm_zrad_jet` (`Window/KJet_mem_box_deriv.lean`) and of the
`∃`-form `ZS.Zrad_jet_bounds_sharp`; the constant `2 ^ (n+2) * 100 = KJbz n` is explicit, so the
result can be compared with the box constant. -/
private lemma kw_zrad_jet_le (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hjet : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {σ a t : ℝ} (ha : |a| ≤ 19 / 20) (hσ : |σ| ≤ 19 / 20) (ht : |t| ≤ 2) {j : ℕ}
    (hj : j ≤ n + 2) :
    |iteratedDeriv j (fun v : ℝ => KernelExt.Zrad h (v, σ, t)) a| ≤ (2 : ℝ) ^ (n + 2) * 100 := by
  have hpow : (1 : ℝ) ≤ 2 ^ (n + 2) := one_le_pow₀ (by norm_num)
  have ha1 : |a| ≤ 1 := by linarith
  have hline_jet : ∀ k ≤ n + 2, |iteratedDeriv k (fun v : ℝ => line h v t) a| ≤ 201 / 100 := by
    intro k hk
    have hb := kw_affine_jet_le hh (δ := 1 / 100) (t := t) (a := a) ha1 (k := k) (hjet k hk a)
    have he : (fun v : ℝ => line h v t) = fun v : ℝ => v * t + h v := rfl
    rw [he]
    linarith [hb, ht]
  have hσline : |line h σ t| ≤ 201 / 100 := by
    have hhσ : |h σ| ≤ 1 / 100 := by simpa using hjet 0 (by omega) σ
    have h1 : |line h σ t| ≤ |σ| * |t| + 1 / 100 := by
      show |σ * t + h σ| ≤ |σ| * |t| + 1 / 100
      calc |σ * t + h σ| ≤ |σ * t| + |h σ| := abs_add_le _ _
        _ = |σ| * |t| + |h σ| := by rw [abs_mul]
        _ ≤ |σ| * |t| + 1 / 100 := by linarith [hhσ]
    have h2 : |σ| * |t| + 1 / 100 ≤ 201 / 100 := by
      nlinarith [hσ, ht, abs_nonneg σ, abs_nonneg t]
    linarith
  have hfun : (fun v : ℝ => KernelExt.Zrad h (v, σ, t))
      = (fun _ : ℝ => line h σ t ^ 2) - (fun v : ℝ => line h v t ^ 2) := by
    funext v
    simp only [KernelExt.Zrad, Pi.sub_apply]
  rcases eq_or_ne j 0 with hj0 | hj0
  · subst hj0
    rw [hfun]
    simp only [iteratedDeriv_zero, Pi.sub_apply]
    have hline_a : |line h a t| ≤ 201 / 100 := by
      simpa using hline_jet 0 (by omega)
    have hb : |line h σ t ^ 2 - line h a t ^ 2| ≤ 100 := by
      calc |line h σ t ^ 2 - line h a t ^ 2|
          ≤ |line h σ t ^ 2| + |line h a t ^ 2| := kw_abs_sub_le_abs_add _ _
        _ = |line h σ t| ^ 2 + |line h a t| ^ 2 := by rw [abs_pow, abs_pow]
        _ ≤ 100 := by nlinarith [hσline, hline_a, abs_nonneg (line h σ t),
            abs_nonneg (line h a t)]
    calc |line h σ t ^ 2 - line h a t ^ 2| ≤ 100 := hb
      _ ≤ (2 : ℝ) ^ (n + 2) * 100 := by nlinarith [hpow]
  · have hcd : ContDiffAt ℝ (j : ℕ) (fun v : ℝ => line h v t ^ 2) a :=
      (kw_contDiffAt_affine hh t a j).pow 2
    have hsplit : iteratedDeriv j (fun v : ℝ => KernelExt.Zrad h (v, σ, t)) a
        = - iteratedDeriv j (fun v : ℝ => line h v t ^ 2) a := by
      rw [hfun, iteratedDeriv_sub contDiffAt_const hcd, iteratedDeriv_const]
      simp only [if_neg hj0, zero_sub]
    rw [hsplit, abs_neg]
    have heq : (fun v : ℝ => line h v t ^ 2)
        = (fun v : ℝ => line h v t) * (fun v : ℝ => line h v t) := by
      funext v; simp only [Pi.mul_apply]; ring
    rw [heq]
    have hmul := Work.OddVolterra.Existence.aw_prod_jet_le (f := fun v : ℝ => line h v t) (g := fun v : ℝ => line h v t)
      (a := a) (A := 201 / 100) (B := 201 / 100) (N := n + 2) (by norm_num) (by norm_num)
      hline_jet hline_jet (kw_contDiffAt_affine hh t a (n + 2))
      (kw_contDiffAt_affine hh t a (n + 2)) hj
    refine hmul.trans ?_
    calc (2 : ℝ) ^ j * (201 / 100 * (201 / 100))
        ≤ (2 : ℝ) ^ (n + 2) * (201 / 100 * (201 / 100)) :=
          mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj) (by norm_num)
      _ ≤ (2 : ℝ) ^ (n + 2) * 100 := mul_le_mul_of_nonneg_left (by norm_num) (by positivity)

/-! ## Elementary jet-of-`h` helpers -/

/-- The derivative of the `m`-th derivative of `f` is the `(m+1)`-st derivative of `f`. -/
private lemma kw_deriv_iteratedDeriv_succ (f : ℝ → ℝ) (m : ℕ) (a : ℝ) :
    deriv (fun u : ℝ => iteratedDeriv m f u) a = iteratedDeriv (m + 1) f a := by
  rw [show (fun u : ℝ => iteratedDeriv m f u) = iteratedDeriv m f from rfl,
    ← iteratedDeriv_succ (n := m) (f := f)]

/-- `KJbz n` is at least `20`. -/
private lemma kw_twenty_le_KJbz (n : ℕ) : 20 ≤ Window.KJbz n := by
  have h2 : (4 : ℝ) ≤ 2 ^ (n + 2) := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  simp only [Window.KJbz]
  nlinarith

/-- `kradLo (1/4)` is above the box lower corner `1/100`. -/
private lemma kw_kradLo_quarter : (1 : ℝ) / 100 ≤ kradLo (1 / 4) := by
  rw [kradLo]
  norm_num

/-! ## Smoothness of the jet curve -/

/-- The jet curve `u ↦ KJet n h σ z u` is `C^∞` when `h` is. -/
private lemma kw_contDiff_KJet (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ : ℝ)
    (z : St) : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => Window.KJet n h σ z u) := by
  rw [contDiff_pi]
  intro i
  cases i
  case aa =>
    show ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => u)
    exact contDiff_id
  case sg =>
    show ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => σ)
    exact contDiff_const
  case t1 =>
    show ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => -(z 0))
    exact contDiff_const
  case t2 =>
    show ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => z 1)
    exact contDiff_const
  case kd1 =>
    show ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => krad h σ (-(z 0)) u)
    exact contDiff_krad hh σ (-(z 0))
  case kd2 =>
    show ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => krad h σ (z 1) u)
    exact contDiff_krad hh σ (z 1)
  case c2 =>
    show ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => z 2)
    exact contDiff_const
  case c3 =>
    show ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => z 3)
    exact contDiff_const
  case Z1 k =>
    have hF : ContDiff ℝ (⊤ : ℕ∞) (fun v : ℝ => (σ - v) * krad h σ (-(z 0)) v) :=
      (contDiff_const.sub contDiff_id).mul (contDiff_krad hh σ (-(z 0)))
    simpa [kjet, iteratedDeriv_eq_iterate] using hF.iterate_deriv k.1
  case Z2 k =>
    have hF : ContDiff ℝ (⊤ : ℕ∞) (fun v : ℝ => (σ - v) * krad h σ (z 1) v) :=
      (contDiff_const.sub contDiff_id).mul (contDiff_krad hh σ (z 1))
    simpa [kjet, iteratedDeriv_eq_iterate] using hF.iterate_deriv k.1
  case w j =>
    simpa [iteratedDeriv_eq_iterate] using hh.iterate_deriv (j.1 + 1)

/-! ## The main lemma -/

theorem kjet_mem_boxW_deriv (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hjet : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {σ : ℝ} (hσ : σ ∈ Set.Icc (1 / 4 : ℝ) (19 / 20)) {z : Work.OddVolterra.St}
    (hz0 : (1 / 5 : ℝ) ≤ z 0) (hz1 : (1 / 5 : ℝ) ≤ z 1) (hz : ∀ i : Fin 4, |z i| ≤ 2)
    {a : ℝ} (ha : a ∈ Set.Icc (1 / 4 : ℝ) (19 / 20)) :
    Work.OddVolterra.Window.KJet n h σ z a ∈
        Work.OddVolterra.WinData.KJboxW n (Work.OddVolterra.Window.KJbz n) ∧
      ‖deriv (fun u : ℝ => Work.OddVolterra.Window.KJet n h σ z u) a‖
        ≤ Work.OddVolterra.Window.KJbz n := by
  have hB0 : 0 ≤ Window.KJbz n := Window.KJbz_nonneg n
  have hB1 : 1 ≤ Window.KJbz n := Window.one_le_KJbz n
  have hB20 : 20 ≤ Window.KJbz n := kw_twenty_le_KJbz n
  have hσ1 : (1 / 4 : ℝ) ≤ σ := hσ.1
  have hσ2 : σ ≤ 19 / 20 := hσ.2
  have ha1 : (1 / 4 : ℝ) ≤ a := ha.1
  have ha2 : a ≤ 19 / 20 := ha.2
  have hσabs : |σ| ≤ 19 / 20 := abs_le.mpr ⟨by linarith, hσ2⟩
  have haabs : |a| ≤ 19 / 20 := abs_le.mpr ⟨by linarith, ha2⟩
  have hz0abs : |z 0| ≤ 2 := hz 0
  have hz1abs : |z 1| ≤ 2 := hz 1
  have ht1abs : |(-(z 0))| ≤ 2 := by rw [abs_neg]; exact hz0abs
  have ht2abs : |z 1| ≤ 2 := hz1abs
  have ht1low : (1 / 5 : ℝ) ≤ |(-(z 0))| := by
    rw [abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ z 0)]
    exact hz0
  have ht2low : (1 / 5 : ℝ) ≤ |z 1| := by
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ z 1)]
    exact hz1
  have hδ0 : (0 : ℝ) ≤ 1 / 100 := by norm_num
  have hδ1 : (1 : ℝ) / 100 ≤ 1 / 100 := le_rfl
  have hδ1' : (1 : ℝ) / 100 ≤ 1 := by norm_num
  have hjet2 : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
    fun k hk s => hjet k (by omega) s
  have hh1 : ContDiff ℝ (1 : ℕ∞) h := hh.of_le (by norm_num)
  -- the radicand data on the wide square, from `krad_jets` with the general slope box `A = 1/4`
  obtain ⟨hk1lo', hk1hi', -, hk1d, -⟩ :=
    krad_jets hh hsupp (δ := 1 / 100) hδ0 hδ1 hjet2 (A := (1 / 4 : ℝ)) (by norm_num)
      ha1 hσ1 (by linarith [hσ2]) (by linarith [ha2]) ht1low ht1abs
  obtain ⟨hk2lo', hk2hi', -, hk2d, -⟩ :=
    krad_jets hh hsupp (δ := 1 / 100) hδ0 hδ1 hjet2 (A := (1 / 4 : ℝ)) (by norm_num)
      ha1 hσ1 (by linarith [hσ2]) (by linarith [ha2]) ht2low ht2abs
  have hk1lo : (1 / 100 : ℝ) ≤ krad h σ (-(z 0)) a :=
    le_trans kw_kradLo_quarter hk1lo'
  have hk2lo : (1 / 100 : ℝ) ≤ krad h σ (z 1) a :=
    le_trans kw_kradLo_quarter hk2lo'
  -- the radicand-jet bounds
  have hZ1 : ∀ j : ℕ, j ≤ n + 2 → |kjet h σ (-(z 0)) a j| ≤ Window.KJbz n := by
    intro j hj
    rw [Window.kjet_eq_Zrad hh1 σ (-(z 0)) a j, Window.KJbz]
    exact kw_zrad_jet_le n hh hjet haabs hσabs ht1abs hj
  have hZ2 : ∀ j : ℕ, j ≤ n + 2 → |kjet h σ (z 1) a j| ≤ Window.KJbz n := by
    intro j hj
    rw [Window.kjet_eq_Zrad hh1 σ (z 1) a j, Window.KJbz]
    exact kw_zrad_jet_le n hh hjet haabs hσabs ht2abs hj
  have hcd1 : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => Window.KJet n h σ z u) :=
    kw_contDiff_KJet n hh σ z
  have hd1 : ∀ i : Window.KJIx n, DifferentiableAt ℝ (fun u : ℝ => Window.KJet n h σ z u i) a :=
    fun i => (((contDiff_pi.mp hcd1) i).contDiffAt).differentiableAt (by simp)
  have hconst_deriv : ∀ c : ℝ, |deriv (fun _ : ℝ => c) a| ≤ Window.KJbz n := by
    intro c
    have h0 : deriv (fun _ : ℝ => c) a = 0 := by simp
    rw [h0, abs_zero]
    exact hB0
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i
    cases i
    case aa =>
      show (1 / 4 : ℝ) ≤ a
      exact ha1
    case sg =>
      show (1 / 4 : ℝ) ≤ σ
      exact hσ1
    case t1 =>
      show (-2 : ℝ) ≤ -(z 0)
      linarith [(abs_le.mp hz0abs).2]
    case t2 =>
      show (1 / 5 : ℝ) ≤ z 1
      exact hz1
    case kd1 =>
      show (1 / 100 : ℝ) ≤ krad h σ (-(z 0)) a
      exact hk1lo
    case kd2 =>
      show (1 / 100 : ℝ) ≤ krad h σ (z 1) a
      exact hk2lo
    case c2 =>
      show (-2 : ℝ) ≤ z 2
      linarith [(abs_le.mp (hz 2)).1]
    case c3 =>
      show (-2 : ℝ) ≤ z 3
      linarith [(abs_le.mp (hz 3)).1]
    case Z1 k =>
      show -(Window.KJbz n) ≤ kjet h σ (-(z 0)) a k.1
      linarith [neg_le_abs (kjet h σ (-(z 0)) a k.1), hZ1 k.1 (le_of_lt k.2)]
    case Z2 k =>
      show -(Window.KJbz n) ≤ kjet h σ (z 1) a k.1
      linarith [neg_le_abs (kjet h σ (z 1) a k.1), hZ2 k.1 (le_of_lt k.2)]
    case w j =>
      show (-1 / 100 : ℝ) ≤ iteratedDeriv (j.1 + 1) h a
      have hj := hjet (j.1 + 1) (by have := j.2; omega) a
      linarith [neg_le_abs (iteratedDeriv (j.1 + 1) h a), hj]
  · intro i
    cases i
    case aa =>
      show a ≤ 19 / 20
      exact ha2
    case sg =>
      show σ ≤ 19 / 20
      exact hσ2
    case t1 =>
      show -(z 0) ≤ -(1 / 5)
      linarith
    case t2 =>
      show z 1 ≤ 2
      linarith [(abs_le.mp hz1abs).2]
    case kd1 =>
      show krad h σ (-(z 0)) a ≤ 20
      exact hk1hi'
    case kd2 =>
      show krad h σ (z 1) a ≤ 20
      exact hk2hi'
    case c2 =>
      show z 2 ≤ 2
      linarith [(abs_le.mp (hz 2)).2]
    case c3 =>
      show z 3 ≤ 2
      linarith [(abs_le.mp (hz 3)).2]
    case Z1 k =>
      show kjet h σ (-(z 0)) a k.1 ≤ Window.KJbz n
      linarith [le_abs_self (kjet h σ (-(z 0)) a k.1), hZ1 k.1 (le_of_lt k.2)]
    case Z2 k =>
      show kjet h σ (z 1) a k.1 ≤ Window.KJbz n
      linarith [le_abs_self (kjet h σ (z 1) a k.1), hZ2 k.1 (le_of_lt k.2)]
    case w j =>
      show iteratedDeriv (j.1 + 1) h a ≤ 1 / 100
      have hj := hjet (j.1 + 1) (by have := j.2; omega) a
      linarith [le_abs_self (iteratedDeriv (j.1 + 1) h a), hj]
  · have hder1c :
        ∀ i : Window.KJIx n, |deriv (fun u : ℝ => Window.KJet n h σ z u i) a| ≤ Window.KJbz n := by
      intro i
      cases i
      case aa =>
        show |deriv (fun u : ℝ => u) a| ≤ Window.KJbz n
        have h1 : deriv (fun u : ℝ => u) a = 1 := by simp
        rw [h1, abs_one]
        exact hB1
      case sg =>
        show |deriv (fun _ : ℝ => σ) a| ≤ Window.KJbz n
        exact hconst_deriv σ
      case t1 =>
        show |deriv (fun _ : ℝ => -(z 0)) a| ≤ Window.KJbz n
        exact hconst_deriv (-(z 0))
      case t2 =>
        show |deriv (fun _ : ℝ => z 1) a| ≤ Window.KJbz n
        exact hconst_deriv (z 1)
      case kd1 =>
        show |deriv (fun u : ℝ => krad h σ (-(z 0)) u) a| ≤ Window.KJbz n
        linarith [hk1d, hB20]
      case kd2 =>
        show |deriv (fun u : ℝ => krad h σ (z 1) u) a| ≤ Window.KJbz n
        linarith [hk2d, hB20]
      case c2 =>
        show |deriv (fun _ : ℝ => z 2) a| ≤ Window.KJbz n
        exact hconst_deriv (z 2)
      case c3 =>
        show |deriv (fun _ : ℝ => z 3) a| ≤ Window.KJbz n
        exact hconst_deriv (z 3)
      case Z1 k =>
        show |deriv (fun u : ℝ => kjet h σ (-(z 0)) u k.1) a| ≤ Window.KJbz n
        rw [(kjet_succ h σ (-(z 0)) a k.1).symm]
        exact hZ1 (k.1 + 1) (by have := k.2; omega)
      case Z2 k =>
        show |deriv (fun u : ℝ => kjet h σ (z 1) u k.1) a| ≤ Window.KJbz n
        rw [(kjet_succ h σ (z 1) a k.1).symm]
        exact hZ2 (k.1 + 1) (by have := k.2; omega)
      case w j =>
        show |deriv (fun u : ℝ => iteratedDeriv (j.1 + 1) h u) a| ≤ Window.KJbz n
        rw [kw_deriv_iteratedDeriv_succ h (j.1 + 1) a]
        show |iteratedDeriv (j.1 + 2) h a| ≤ Window.KJbz n
        exact le_trans (le_trans (hjet (j.1 + 2) (by have := j.2; omega) a) hδ1') hB1
    rw [pi_norm_le_iff_of_nonneg hB0]
    intro i
    have h1 : (deriv (fun u : ℝ => Window.KJet n h σ z u) a) i
        = deriv (fun u : ℝ => Window.KJet n h σ z u i) a := congrFun (deriv_pi hd1) i
    rw [h1, Real.norm_eq_abs]
    exact hder1c i

end

end Work.OddVolterra.WinData
