import Mathlib
import Submission.Commons.Topology.Metric.exists_point_avoiding_lines
import Submission.Commons.Topology.Metric.dist_toLp_update
import Submission.Commons.LinearAlgebra.exists_generic_config
import Submission.Commons.Analysis.Calculus.absolutelyContinuousOnInterval_and_deriv_bound_of_differenceQuotient

namespace Commons.Topology.Metric

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Set MeasureTheory
open scoped ENNReal NNReal

/-! ## Pasting Lipschitz functions -/

/-- Pasting two Lipschitz functions: if `f` is Lipschitz with constant `K₁` on `[a,c]`, `g` is
Lipschitz with constant `K₂` on `[c,b]`, and `f c = g c`, then the function equal to `f` on
`(-∞, c]` and to `g` on `(c, ∞)` is Lipschitz with constant `max K₁ K₂` on `[a,b]`. -/
theorem lipschitzOnWith_paste {X : Type*} [PseudoMetricSpace X]
    {f g : ℝ → X} {a c b : ℝ} {K₁ K₂ : NNReal} (hac : a ≤ c) (hcb : c ≤ b) (hfc : f c = g c)
    (hf : LipschitzOnWith K₁ f (Icc a c)) (hg : LipschitzOnWith K₂ g (Icc c b)) :
    LipschitzOnWith (max K₁ K₂) (fun x : ℝ => if x ≤ c then f x else g x) (Icc a b) := by
  rw [lipschitzOnWith_iff_dist_le_mul] at hf hg ⊢
  have hM₁ : (K₁ : ℝ) ≤ ((max K₁ K₂ : NNReal) : ℝ) := by exact_mod_cast le_max_left K₁ K₂
  have hM₂ : (K₂ : ℝ) ≤ ((max K₁ K₂ : NNReal) : ℝ) := by exact_mod_cast le_max_right K₁ K₂
  have hmain : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y →
      dist (if x ≤ c then f x else g x) (if y ≤ c then f y else g y)
        ≤ ((max K₁ K₂ : NNReal) : ℝ) * dist x y := by
    intro x hx y hy hxy
    rw [mem_Icc] at hx hy
    rcases le_or_gt y c with hyc | hcy
    · have hxc : x ≤ c := le_trans hxy hyc
      have hd : dist (if x ≤ c then f x else g x) (if y ≤ c then f y else g y)
          = dist (f x) (f y) := by rw [if_pos hxc, if_pos hyc]
      rw [hd]
      calc dist (f x) (f y)
          ≤ K₁ * dist x y := hf x ⟨hx.1, hxc⟩ y ⟨hy.1, hyc⟩
        _ ≤ ((max K₁ K₂ : NNReal) : ℝ) * dist x y :=
            mul_le_mul_of_nonneg_right hM₁ dist_nonneg
    · rcases le_or_gt x c with hxc | hcx
      · have hd : dist (if x ≤ c then f x else g x) (if y ≤ c then f y else g y)
            = dist (f x) (g y) := by rw [if_pos hxc, if_neg (not_le_of_gt hcy)]
        rw [hd]
        have h1 : dist (f x) (f c) ≤ K₁ * dist x c := hf x ⟨hx.1, hxc⟩ c ⟨hac, le_rfl⟩
        have h2 : dist (g c) (g y) ≤ K₂ * dist c y := hg c ⟨le_rfl, hcb⟩ y ⟨le_of_lt hcy, hy.2⟩
        have hdxc : dist x c = c - x := by rw [Real.dist_eq, abs_of_nonpos (by linarith : x - c ≤ 0)]; ring
        have hdcy : dist c y = y - c := by rw [Real.dist_eq, abs_of_nonpos (by linarith : c - y ≤ 0)]; ring
        have hdxy : dist x y = y - x := by rw [Real.dist_eq, abs_of_nonpos (by linarith : x - y ≤ 0)]; ring
        have h3 : dist (f x) (g y) ≤ K₁ * (c - x) + K₂ * (y - c) := by
          have ht : dist (f x) (g y) ≤ dist (f x) (f c) + dist (g c) (g y) := by
            calc dist (f x) (g y) ≤ dist (f x) (f c) + dist (f c) (g y) := dist_triangle _ _ _
              _ = dist (f x) (f c) + dist (g c) (g y) := by rw [hfc]
          rw [hdxc] at h1
          rw [hdcy] at h2
          exact ht.trans (add_le_add h1 h2)
        refine h3.trans ?_
        rw [hdxy]
        have h4 : K₁ * (c - x) + K₂ * (y - c)
            ≤ ((max K₁ K₂ : NNReal) : ℝ) * (c - x) + ((max K₁ K₂ : NNReal) : ℝ) * (y - c) :=
          add_le_add (mul_le_mul_of_nonneg_right hM₁ (by linarith))
            (mul_le_mul_of_nonneg_right hM₂ (by linarith))
        refine h4.trans (le_of_eq ?_)
        ring
      · have hd : dist (if x ≤ c then f x else g x) (if y ≤ c then f y else g y)
            = dist (g x) (g y) := by rw [if_neg (not_le_of_gt hcx), if_neg (not_le_of_gt hcy)]
        rw [hd]
        calc dist (g x) (g y) ≤ K₂ * dist x y := hg x ⟨le_of_lt hcx, hx.2⟩ y ⟨le_of_lt hcy, hy.2⟩
          _ ≤ ((max K₁ K₂ : NNReal) : ℝ) * dist x y :=
              mul_le_mul_of_nonneg_right hM₂ dist_nonneg
  intro x hx y hy
  rcases le_total x y with hxy | hyx
  · exact hmain x hx y hy hxy
  · rw [dist_comm (if x ≤ c then f x else g x) (if y ≤ c then f y else g y), dist_comm x y]
    exact hmain y hy x hx hyx

/-- A Lipschitz function on an interval is absolutely continuous there. -/
lemma absolutelyContinuousOnInterval_of_lipschitzOnWith {X : Type*} [PseudoMetricSpace X]
    {f : ℝ → X} {a b : ℝ} (hab : a ≤ b) {K : NNReal} (hf : LipschitzOnWith K f (Icc a b)) :
    AbsolutelyContinuousOnInterval f a b :=
  (hf.mono (by rw [uIcc_of_le hab])).absolutelyContinuousOnInterval

/-- A Lipschitz function on an interval has finite `L²` norm of its derivative on that interval. -/
theorem lintegral_deriv_sq_lt_top_of_lipschitzOnWith
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {a b : ℝ} (hab : a ≤ b) {K : NNReal} {f : ℝ → F}
    (hf : LipschitzOnWith K f (Icc a b)) :
    (∫⁻ t in Ioc a b, ENNReal.ofReal (‖deriv f t‖ ^ 2)) < ⊤ := by
  have hcont : ContinuousOn f (Icc a b) := hf.continuousOn
  rw [lipschitzOnWith_iff_dist_le_mul] at hf
  set M : ℝ := (K : ℝ) * Real.sqrt (b - a) with hMdef
  have hM : 0 ≤ M := by rw [hMdef]; positivity
  have hMsq : M ^ 2 = (K : ℝ) ^ 2 * (b - a) := by
    rw [hMdef, mul_pow, Real.sq_sqrt (sub_nonneg.mpr hab)]
  have h : ∀ s ∈ Ioo (0:ℝ) (b - a),
      ∫⁻ t in Ioc a (b - s), ENNReal.ofReal (‖s⁻¹ • (f (t + s) - f t)‖ ^ 2)
        ≤ ENNReal.ofReal (M ^ 2) := by
    intro s hs
    have hs0 : 0 < s := hs.1
    have hle : ∀ t ∈ Ioc a (b - s), ENNReal.ofReal (‖s⁻¹ • (f (t + s) - f t)‖ ^ 2)
        ≤ ENNReal.ofReal ((K : ℝ) ^ 2) := by
      intro t ht
      rw [mem_Ioc] at ht
      obtain ⟨hat, htsb⟩ := ht
      have htIcc : t ∈ Icc a b := ⟨hat.le, by linarith⟩
      have htsIcc : t + s ∈ Icc a b := ⟨by linarith, by linarith⟩
      have hdist : dist (f t) (f (t + s)) ≤ (K : ℝ) * s := by
        have hh := hf t htIcc (t + s) htsIcc
        rwa [show dist t (t + s) = s from by
          rw [Real.dist_eq, show t - (t + s) = -s by ring, abs_neg, abs_of_pos hs0]] at hh
      have hnorm : ‖s⁻¹ • (f (t + s) - f t)‖ ≤ (K : ℝ) := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hs0.le),
          ← dist_eq_norm, dist_comm]
        calc s⁻¹ * dist (f t) (f (t + s)) ≤ s⁻¹ * ((K:ℝ) * s) :=
              mul_le_mul_of_nonneg_left hdist (inv_nonneg.mpr hs0.le)
          _ = (K:ℝ) := by field_simp
      exact ENNReal.ofReal_le_ofReal
        (pow_le_pow_left₀ (norm_nonneg (s⁻¹ • (f (t + s) - f t))) hnorm 2)
    calc ∫⁻ t in Ioc a (b - s), ENNReal.ofReal (‖s⁻¹ • (f (t + s) - f t)‖ ^ 2)
        ≤ ∫⁻ t in Ioc a (b - s), ENNReal.ofReal ((K:ℝ) ^ 2) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          exact hle t ht
      _ = ENNReal.ofReal ((K:ℝ) ^ 2) * volume (Ioc a (b - s)) := setLIntegral_const _ _
      _ = ENNReal.ofReal ((K:ℝ) ^ 2) * ENNReal.ofReal (b - s - a) := by rw [Real.volume_Ioc]
      _ = ENNReal.ofReal ((K:ℝ) ^ 2 * (b - s - a)) := by
            rw [ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal ((K:ℝ) ^ 2 * (b - a)) :=
            ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
      _ = ENNReal.ofReal (M ^ 2) := by rw [hMsq]
  exact lt_of_le_of_lt (Commons.Analysis.Calculus.absolutelyContinuousOnInterval_and_deriv_bound_of_differenceQuotient
    hab hM hcont h).2 ENNReal.ofReal_lt_top

/-- A single body can be moved from `p` to `q` in `E \ F` (with `F` finite, `p, q ∉ F`) by a
Lipschitz path, hence by an absolutely continuous path with finite `L²` derivative norm. -/
theorem exists_lipschitz_path_avoiding_finset
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : 2 ≤ Module.finrank ℝ E) (F : Finset E) {p q : E} (hp : p ∉ F) (hq : q ∉ F) :
    ∃ (K : NNReal) (γ : ℝ → E), γ 0 = p ∧ γ 1 = q ∧ LipschitzOnWith K γ (Icc 0 1) ∧
      ∀ t ∈ Icc (0:ℝ) 1, γ t ∉ F := by
  obtain ⟨c, hcF, hcl, hcr⟩ := exists_point_avoiding_lines hdim F p q hp hq
  have hf : LipschitzOnWith (NNReal.mk (2 * ‖c - p‖) (by positivity))
      (fun t : ℝ => p + (2*t) • (c - p)) (Icc 0 (1/2)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro u _ v _
    rw [dist_eq_norm, dist_eq_norm]
    have h : p + (2*u)•(c-p) - (p + (2*v)•(c-p)) = (2*(u-v)) • (c-p) := by
      rw [add_sub_add_left_eq_sub, ← sub_smul, show (2:ℝ)*u - 2*v = 2*(u-v) by ring]
    rw [h, norm_smul]
    rw [show ‖(2*(u-v) : ℝ)‖ = 2 * |u - v| by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]]
    rw [show ‖u - v‖ = |u - v| by rw [Real.norm_eq_abs]]
    rw [NNReal.coe_mk]
    exact le_of_eq (by ring)
  have hg : LipschitzOnWith (NNReal.mk (2 * ‖c - q‖) (by positivity))
      (fun t : ℝ => q + (2 - 2*t) • (c - q)) (Icc (1/2) 1) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro u _ v _
    rw [dist_eq_norm, dist_eq_norm]
    have h : q + (2 - 2*u)•(c-q) - (q + (2 - 2*v)•(c-q)) = (2*(v-u)) • (c-q) := by
      rw [add_sub_add_left_eq_sub, ← sub_smul, show (2:ℝ) - 2*u - (2 - 2*v) = 2*(v-u) by ring]
    rw [h, norm_smul]
    rw [show ‖(2*(v-u) : ℝ)‖ = 2 * |v - u| by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]]
    rw [show ‖u - v‖ = |u - v| by rw [Real.norm_eq_abs]]
    rw [show |v - u| = |u - v| by rw [abs_sub_comm]]
    rw [NNReal.coe_mk]
    exact le_of_eq (by ring)
  have hfc : p + (2*(1/2:ℝ)) • (c - p) = q + (2 - 2*(1/2:ℝ)) • (c - q) := by
    have h1 : p + (2*(1/2:ℝ)) • (c - p) = c := by
      rw [show (2:ℝ)*(1/2) = 1 by norm_num, one_smul]; abel
    have h2 : q + (2 - 2*(1/2:ℝ)) • (c - q) = c := by
      rw [show (2:ℝ) - 2*(1/2) = 1 by norm_num, one_smul]; abel
    exact h1.trans h2.symm
  have hpaste : LipschitzOnWith (max (NNReal.mk (2 * ‖c - p‖) (by positivity))
        (NNReal.mk (2 * ‖c - q‖) (by positivity)))
      (fun t : ℝ => if t ≤ 1/2 then p + (2*t) • (c - p) else q + (2 - 2*t) • (c - q))
      (Icc 0 1) :=
    lipschitzOnWith_paste (by norm_num) (by norm_num) hfc hf hg
  refine ⟨max (NNReal.mk (2 * ‖c - p‖) (by positivity))
      (NNReal.mk (2 * ‖c - q‖) (by positivity)),
    fun t : ℝ => if t ≤ 1/2 then p + (2*t) • (c - p) else q + (2 - 2*t) • (c - q),
    ?_, ?_, hpaste, ?_⟩
  · change (if (0:ℝ) ≤ 1/2 then p + (2*0) • (c - p) else q + (2 - 2*0) • (c - q)) = p
    rw [if_pos (by norm_num : ((0:ℝ) ≤ 1/2)), show (2:ℝ)*0 = 0 by norm_num, zero_smul, add_zero]
  · change (if (1:ℝ) ≤ 1/2 then p + (2*1) • (c - p) else q + (2 - 2*1) • (c - q)) = q
    rw [if_neg (by norm_num : ¬ ((1:ℝ) ≤ 1/2)), show (2:ℝ) - 2*1 = 0 by norm_num, zero_smul,
      add_zero]
  · intro t ht
    rw [mem_Icc] at ht
    change (if t ≤ 1/2 then p + (2*t) • (c - p) else q + (2 - 2*t) • (c - q)) ∉ F
    by_cases hle : t ≤ 1/2
    · rw [if_pos hle]
      intro hmem
      by_cases ht0 : t = 0
      · have : p ∈ F := by simpa [ht0] using hmem
        exact hp this
      · have h2t : (2*t) ≠ 0 := by
          intro hc; apply ht0; linarith
        have hkey : c = p + (2*t)⁻¹ • ((p + (2*t) • (c - p)) - p) := by
          rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ h2t, one_smul]
          abel
        exact (hcl (p + (2*t) • (c - p)) hmem ((2*t)⁻¹)) hkey
    · rw [if_neg hle]
      intro hmem
      by_cases ht1 : t = 1
      · have : q ∈ F := by simpa [ht1] using hmem
        exact hq this
      · have hq2t : (2 - 2*t) ≠ 0 := by
          intro hc; apply ht1; linarith
        have hkey : c = q + (2 - 2*t)⁻¹ • ((q + (2 - 2*t) • (c - q)) - q) := by
          rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hq2t, one_smul]
          abel
        exact (hcr (q + (2 - 2*t) • (c - q)) hmem ((2 - 2*t)⁻¹)) hkey

/-! ## The `N`-body concatenation of single-body moves -/

section Defs

variable {E : Type*} {N : ℕ}

/-- The configuration of the `N` bodies just before the `m`-th individual move.  Bodies are moved
one at a time: first each body `k = 0, …, N-1` is moved from `x k` to `z k`, then each body `k` is
moved from `z k` to `y k`.  Here `m` runs from `0` to `2N`. -/
noncomputable def nbodySrcState (x y z : Fin N → E) (m : ℕ) : Fin N → E :=
  if m ≤ N then (fun i => if i.val < m then z i else x i)
  else (fun i => if i.val < m - N then y i else z i)

/-- The configuration `nbodySrcState` as an element of `EuclideanSpace E (Fin N)`. -/
noncomputable def nbodyState (x y z : Fin N → E) (m : ℕ) : EuclideanSpace E (Fin N) :=
  WithLp.toLp 2 (nbodySrcState x y z m)

/-- The `m`-th individual move, as a curve of configurations of `EuclideanSpace E (Fin N)`. -/
noncomputable def nbodyPiece (x y z : Fin N → E) (ψA ψB : Fin N → ℝ → E)
    (m : Fin (2*N)) : ℝ → EuclideanSpace E (Fin N) :=
  if h : (m : ℕ) < N then
    (fun s => WithLp.toLp 2 (Function.update (nbodySrcState x y z (m : ℕ)) ⟨(m : ℕ), h⟩
      (ψA ⟨(m : ℕ), h⟩ s)))
  else
    (fun s => WithLp.toLp 2 (Function.update (nbodySrcState x y z (m : ℕ))
      ⟨(m : ℕ) - N, by have := m.2; omega⟩ (ψB ⟨(m : ℕ) - N, by have := m.2; omega⟩ s)))

/-- The Lipschitz constant of the `m`-th individual move. -/
noncomputable def nbodyKp (KA KB : Fin N → NNReal) (m : Fin (2*N)) : NNReal :=
  if h : (m : ℕ) < N then KA ⟨(m : ℕ), h⟩
  else KB ⟨(m : ℕ) - N, by have := m.2; omega⟩

/-- Concatenating the individual moves: `nbodyConcat x P` is the path that starts at `x` and
performs move `P n` during the time interval `[n, n+1]`. -/
noncomputable def nbodyConcat (x : EuclideanSpace E (Fin N))
    (P : Fin (2*N) → ℝ → EuclideanSpace E (Fin N)) : ℕ → ℝ → EuclideanSpace E (Fin N)
  | 0, _ => x
  | n+1, t => if t ≤ (n : ℝ) then nbodyConcat x P n t
      else if h : n < 2*N then P ⟨n, h⟩ (t - n) else x

/-- The running maximum of the Lipschitz constants of the first `n` moves. -/
noncomputable def nbodyK (Kp : Fin (2*N) → NNReal) : ℕ → NNReal
  | 0 => 0
  | n+1 => max (nbodyK Kp n) (if h : n < 2*N then Kp ⟨n, h⟩ else 0)

end Defs

section StateLemmas

variable {E : Type*} {N : ℕ}

lemma nbodySrcState_of_le (x y z : Fin N → E) {m : ℕ} (hm : m ≤ N) :
    nbodySrcState x y z m = fun i => if i.val < m then z i else x i := by
  rw [nbodySrcState, if_pos hm]

lemma nbodySrcState_of_ge (x y z : Fin N → E) {m : ℕ} (hm : N ≤ m) :
    nbodySrcState x y z m = fun i => if i.val < m - N then y i else z i := by
  rcases eq_or_lt_of_le hm with h | h
  · subst h
    rw [nbodySrcState, if_pos le_rfl]
    funext i
    rw [show N - N = 0 by omega, if_neg (Nat.not_lt_zero _), if_pos i.2]
  · rw [nbodySrcState, if_neg (not_le_of_gt h)]

lemma nbodySrcState_zero (x y z : Fin N → E) : nbodySrcState x y z 0 = x := by
  rw [nbodySrcState_of_le x y z (Nat.zero_le N)]
  funext i
  simp

lemma nbodySrcState_last (x y z : Fin N → E) (hN : 0 < N) : nbodySrcState x y z (2*N) = y := by
  rw [nbodySrcState_of_ge x y z (by omega : N ≤ 2*N)]
  funext i
  rw [show 2*N - N = N by omega, if_pos i.2]

lemma nbodySrcState_self_lt (x y z : Fin N → E) {M : ℕ} (hM : M < N) :
    nbodySrcState x y z M ⟨M, hM⟩ = x ⟨M, hM⟩ := by
  rw [nbodySrcState_of_le x y z (le_of_lt hM)]
  simp

lemma nbodySrcState_self_ge (x y z : Fin N → E) {M : ℕ} (hMN : N ≤ M) (hM : M < 2*N) :
    nbodySrcState x y z M ⟨M - N, by omega⟩ = z ⟨M - N, by omega⟩ := by
  rw [nbodySrcState_of_ge x y z hMN]
  simp

lemma nbodySrcState_succ_lt (x y z : Fin N → E) {M : ℕ} (hM : M < N) :
    nbodySrcState x y z (M+1) =
      Function.update (nbodySrcState x y z M) ⟨M, hM⟩ (z ⟨M, hM⟩) := by
  rw [nbodySrcState_of_le x y z (by omega : M + 1 ≤ N), nbodySrcState_of_le x y z (le_of_lt hM)]
  funext i
  rw [Function.update_apply]
  by_cases hi : i = ⟨M, hM⟩
  · subst hi
    simp
  · rw [if_neg hi]
    have hiv : i.val ≠ M := fun hv => hi (Fin.ext hv)
    rcases lt_or_gt_of_ne hiv with h | h
    · rw [if_pos h, if_pos (by omega : i.val < M + 1)]
    · rw [if_neg (by omega : ¬ i.val < M), if_neg (by omega : ¬ i.val < M + 1)]

lemma nbodySrcState_succ_ge (x y z : Fin N → E) {M : ℕ} (hMN : N ≤ M) (hM : M < 2*N) :
    nbodySrcState x y z (M+1) =
      Function.update (nbodySrcState x y z M) ⟨M - N, by omega⟩ (y ⟨M - N, by omega⟩) := by
  rw [nbodySrcState_of_ge x y z (by omega : N ≤ M + 1), nbodySrcState_of_ge x y z hMN]
  funext i
  rw [Function.update_apply, show M + 1 - N = M - N + 1 by omega]
  by_cases hi : i = ⟨M - N, by omega⟩
  · subst hi
    simp
  · rw [if_neg hi]
    have hiv : i.val ≠ M - N := fun hv => hi (Fin.ext hv)
    rcases lt_or_gt_of_ne hiv with h | h
    · rw [if_pos h, if_pos (by omega : i.val < M - N + 1)]
    · rw [if_neg (by omega : ¬ i.val < M - N), if_neg (by omega : ¬ i.val < M - N + 1)]

lemma nbodyState_zero (x : EuclideanSpace E (Fin N)) (y z : Fin N → E) :
    nbodyState (fun i => x i) y z 0 = x := by
  rw [nbodyState, nbodySrcState_zero, WithLp.toLp_ofLp]

/-- Each intermediate configuration has pairwise distinct coordinates. -/
lemma nbodySrcState_collFree (x y z : Fin N → E) (hx : ∀ i j, i ≠ j → x i ≠ x j)
    (hy : ∀ i j, i ≠ j → y i ≠ y j)
    (hz : (∀ i j, i ≠ j → z i ≠ z j) ∧ (∀ i j, z i ≠ x j) ∧ (∀ i j, z i ≠ y j))
    (m : ℕ) : ∀ i j, i ≠ j → nbodySrcState x y z m i ≠ nbodySrcState x y z m j := by
  intro i j hij
  rcases le_or_gt m N with hm | hm
  · rw [nbodySrcState_of_le x y z hm]
    simp only []
    by_cases hi : i.val < m
    · by_cases hj : j.val < m
      · rw [if_pos hi, if_pos hj]; exact hz.1 i j hij
      · rw [if_pos hi, if_neg hj]; exact hz.2.1 i j
    · by_cases hj : j.val < m
      · rw [if_neg hi, if_pos hj]; exact fun h => hz.2.1 j i h.symm
      · rw [if_neg hi, if_neg hj]; exact hx i j hij
  · rw [nbodySrcState_of_ge x y z (le_of_lt hm)]
    simp only []
    by_cases hi : i.val < m - N
    · by_cases hj : j.val < m - N
      · rw [if_pos hi, if_pos hj]; exact hy i j hij
      · rw [if_pos hi, if_neg hj]; exact fun h => hz.2.2 j i h.symm
    · by_cases hj : j.val < m - N
      · rw [if_neg hi, if_pos hj]; exact hz.2.2 i j
      · rw [if_neg hi, if_neg hj]; exact hz.1 i j hij

lemma nbodyPiece_apply_zero (x y z : Fin N → E) (ψA ψB : Fin N → ℝ → E)
    (hA : ∀ k, ψA k 0 = x k) (hB : ∀ k, ψB k 0 = z k) (m : Fin (2*N)) :
    nbodyPiece x y z ψA ψB m 0 = nbodyState x y z (m : ℕ) := by
  rw [nbodyPiece]
  by_cases h : (m:ℕ) < N
  · rw [dif_pos h, hA, nbodyState]
    congr 1
    rw [← nbodySrcState_self_lt x y z h]
    exact Function.update_eq_self _ _
  · rw [dif_neg h, hB, nbodyState]
    congr 1
    have hMN : N ≤ (m:ℕ) := by omega
    rw [← nbodySrcState_self_ge x y z hMN m.2]
    exact Function.update_eq_self _ _

lemma nbodyPiece_apply_one (x y z : Fin N → E) (ψA ψB : Fin N → ℝ → E)
    (hA : ∀ k, ψA k 1 = z k) (hB : ∀ k, ψB k 1 = y k) (m : Fin (2*N)) :
    nbodyPiece x y z ψA ψB m 1 = nbodyState x y z ((m : ℕ) + 1) := by
  rw [nbodyPiece]
  by_cases h : (m:ℕ) < N
  · rw [dif_pos h, hA, nbodyState]
    congr 1
    rw [← nbodySrcState_succ_lt x y z h]
  · rw [dif_neg h, hB, nbodyState]
    congr 1
    have hMN : N ≤ (m:ℕ) := by omega
    rw [← nbodySrcState_succ_ge x y z hMN m.2]

/-- Changing the `k`-th coordinate of a collision-free configuration keeps it collision-free,
provided the new value avoids all the other coordinates. -/
lemma collisionFree_update {w : Fin N → E} (hw : ∀ i j, i ≠ j → w i ≠ w j)
    {k : Fin N} {a : E} (ha : ∀ j, j ≠ k → a ≠ w j) :
    ∀ i j, i ≠ j → (Function.update w k a) i ≠ (Function.update w k a) j := by
  intro i j hij
  rw [Function.update_apply, Function.update_apply]
  by_cases hik : i = k
  · rw [if_pos hik]
    by_cases hjk : j = k
    · rw [if_pos hjk]
      exact fun _ => hij (hik.trans hjk.symm)
    · rw [if_neg hjk]
      exact ha j hjk
  · rw [if_neg hik]
    by_cases hjk : j = k
    · rw [if_pos hjk]
      exact fun h => ha i hik h.symm
    · rw [if_neg hjk]
      exact hw i j hij

section Assembly

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {N : ℕ}

/-- Translation of a Lipschitz function. -/
lemma lipschitzOnWith_sub_const {X : Type*} [PseudoMetricSpace X] {f : ℝ → X} {K : NNReal}
    {c : ℝ} (hf : LipschitzOnWith K f (Icc 0 1)) :
    LipschitzOnWith K (fun t : ℝ => f (t - c)) (Icc c (c + 1)) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  rw [mem_Icc] at hs ht
  have h1 : s - c ∈ Icc 0 1 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have h2 : t - c ∈ Icc 0 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hh := (lipschitzOnWith_iff_dist_le_mul.mp hf) (s - c) h1 (t - c) h2
  rwa [show dist (s - c) (t - c) = dist s t from by
    rw [Real.dist_eq, Real.dist_eq, show s - c - (t - c) = s - t by ring]] at hh

/-- The `m`-th individual move is Lipschitz. -/
lemma nbodyPiece_lipschitz (x y z : Fin N → E) (ψA ψB : Fin N → ℝ → E)
    (KA KB : Fin N → NNReal)
    (hA : ∀ k, LipschitzOnWith (KA k) (ψA k) (Icc 0 1))
    (hB : ∀ k, LipschitzOnWith (KB k) (ψB k) (Icc 0 1))
    (m : Fin (2*N)) :
    LipschitzOnWith (nbodyKp KA KB m) (nbodyPiece x y z ψA ψB m) (Icc 0 1) := by
  rw [nbodyPiece]
  by_cases h : (m:ℕ) < N
  · rw [dif_pos h, nbodyKp, dif_pos h]
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    simp only []
    rw [dist_toLp_update]
    exact (lipschitzOnWith_iff_dist_le_mul.mp (hA ⟨(m:ℕ), h⟩)) s hs t ht
  · rw [dif_neg h, nbodyKp, dif_neg h]
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    simp only []
    rw [dist_toLp_update]
    exact (lipschitzOnWith_iff_dist_le_mul.mp (hB ⟨(m:ℕ) - N, by have := m.2; omega⟩)) s hs t ht

/-- Each individual move stays collision-free. -/
lemma nbodyPiece_collFree (x y z : Fin N → E) (ψA ψB : Fin N → ℝ → E)
    (avA : ∀ k : Fin N, ∀ s ∈ Icc (0:ℝ) 1, ∀ i : Fin N, i ≠ k →
      ψA k s ≠ (if i.val < k.val then z i else x i))
    (avB : ∀ k : Fin N, ∀ s ∈ Icc (0:ℝ) 1, ∀ i : Fin N, i ≠ k →
      ψB k s ≠ (if i.val < k.val then y i else z i))
    (hx : ∀ i j, i ≠ j → x i ≠ x j) (hy : ∀ i j, i ≠ j → y i ≠ y j)
    (hz : (∀ i j, i ≠ j → z i ≠ z j) ∧ (∀ i j, z i ≠ x j) ∧ (∀ i j, z i ≠ y j))
    (m : Fin (2*N)) {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    ∀ i j, i ≠ j → nbodyPiece x y z ψA ψB m s i ≠ nbodyPiece x y z ψA ψB m s j := by
  rw [nbodyPiece]
  by_cases h : (m:ℕ) < N
  · rw [dif_pos h]
    refine collisionFree_update (fun i j hij => nbodySrcState_collFree x y z hx hy hz (m:ℕ) i j hij) ?_
    intro j hjk heq
    rw [nbodySrcState_of_le x y z (le_of_lt h)] at heq
    exact avA ⟨(m:ℕ), h⟩ s hs j hjk heq
  · rw [dif_neg h]
    have hMN : N ≤ (m:ℕ) := by omega
    refine collisionFree_update (fun i j hij => nbodySrcState_collFree x y z hx hy hz (m:ℕ) i j hij) ?_
    intro j hjk heq
    rw [nbodySrcState_of_ge x y z hMN] at heq
    exact avB ⟨(m:ℕ) - N, by have := m.2; omega⟩ s hs j hjk heq

/-- Stabilization: once the path has passed time `n` it stays at its value there. -/
lemma nbodyConcat_stabilize (x : EuclideanSpace E (Fin N))
    (P : Fin (2*N) → ℝ → EuclideanSpace E (Fin N)) :
    ∀ n n' : ℕ, n ≤ n' → ∀ t : ℝ, t ≤ (n:ℝ) → nbodyConcat x P n' t = nbodyConcat x P n t := by
  intro n n'
  induction n' with
  | zero =>
    intro hn t ht
    have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
    rw [hn0]
  | succ n' ih =>
    intro hn t ht
    rcases eq_or_lt_of_le hn with h | h
    · rw [← h]
    · have hle : n ≤ n' := Nat.lt_succ_iff.mp h
      rw [nbodyConcat, if_pos (le_trans ht (by exact_mod_cast hle))]
      exact ih hle t ht

/-- The path equals the `n`-th intermediate configuration at time `n`. -/
lemma nbodyConcat_self (x : EuclideanSpace E (Fin N))
    (P : Fin (2*N) → ℝ → EuclideanSpace E (Fin N)) (S : ℕ → EuclideanSpace E (Fin N))
    (h0 : S 0 = x) (hstep : ∀ m (hm : m < 2*N), P ⟨m, hm⟩ 1 = S (m+1)) :
    ∀ n, n ≤ 2*N → nbodyConcat x P n n = S n := by
  intro n
  induction n with
  | zero => intro _; rw [nbodyConcat]; exact h0.symm
  | succ n ih =>
    intro hn
    simp only [nbodyConcat]
    have hne : ¬ (((n+1:ℕ):ℝ) ≤ (n:ℝ)) := by
      rw [Nat.cast_add, Nat.cast_one]; exact not_le.mpr (lt_add_one _)
    rw [if_neg hne]
    rw [dif_pos (by omega : n < 2*N)]
    rw [show (((n+1:ℕ):ℝ) - (n:ℝ)) = 1 by rw [Nat.cast_add, Nat.cast_one]; ring]
    exact hstep n (by omega)

/-- On `[m, m+1]` the concatenated path performs move `m`. -/
lemma nbodyConcat_apply (x : EuclideanSpace E (Fin N))
    (P : Fin (2*N) → ℝ → EuclideanSpace E (Fin N)) (S : ℕ → EuclideanSpace E (Fin N))
    (h0 : S 0 = x) (hstep : ∀ m (hm : m < 2*N), P ⟨m, hm⟩ 1 = S (m+1))
    (hzero : ∀ m (hm : m < 2*N), P ⟨m, hm⟩ 0 = S m)
    {m : ℕ} (hm : m < 2*N) {t : ℝ} (ht : t ∈ Icc (m:ℝ) ((m:ℝ)+1)) :
    nbodyConcat x P (2*N) t = P ⟨m, hm⟩ (t - m) := by
  rw [mem_Icc] at ht
  rw [nbodyConcat_stabilize x P (m+1) (2*N) (by omega) t
    (by rw [Nat.cast_add, Nat.cast_one]; linarith)]
  simp only [nbodyConcat]
  by_cases hlt : t ≤ (m:ℝ)
  · rw [if_pos hlt]
    have ht' : t = (m:ℝ) := le_antisymm hlt ht.1
    rw [ht', sub_self]
    rw [nbodyConcat_self x P S h0 hstep m (by omega)]
    exact (hzero m hm).symm
  · rw [if_neg hlt, dif_pos hm]

/-- The concatenated path is collision-free as long as each move is. -/
lemma nbodyConcat_collFree (x : EuclideanSpace E (Fin N))
    (P : Fin (2*N) → ℝ → EuclideanSpace E (Fin N))
    (hxcf : ∀ i j, i ≠ j → x i ≠ x j)
    (hPcf : ∀ m (hm : m < 2*N), ∀ s ∈ Icc (0:ℝ) 1, ∀ i j, i ≠ j →
      P ⟨m,hm⟩ s i ≠ P ⟨m,hm⟩ s j) :
    ∀ n, n ≤ 2*N → ∀ t ∈ Icc (0:ℝ) n, ∀ i j, i ≠ j →
      nbodyConcat x P n t i ≠ nbodyConcat x P n t j := by
  intro n
  induction n with
  | zero =>
    intro _ t ht i j hij
    rw [nbodyConcat]
    exact hxcf i j hij
  | succ n ih =>
    intro hn t ht i j hij
    rw [mem_Icc] at ht
    simp only [nbodyConcat]
    by_cases hlt : t ≤ (n:ℝ)
    · rw [if_pos hlt]
      exact ih (by omega) t ⟨ht.1, hlt⟩ i j hij
    · rw [if_neg hlt, dif_pos (by omega : n < 2*N)]
      refine hPcf n (by omega) (t - n) ⟨by linarith, ?_⟩ i j hij
      have h1 : ((n+1:ℕ):ℝ) = (n:ℝ) + 1 := by rw [Nat.cast_add, Nat.cast_one]
      linarith

/-- The concatenated path is Lipschitz, with the running maximum of the individual constants. -/
lemma nbodyConcat_lipschitz (x : EuclideanSpace E (Fin N))
    (P : Fin (2*N) → ℝ → EuclideanSpace E (Fin N)) (S : ℕ → EuclideanSpace E (Fin N))
    (h0 : S 0 = x) (hstep : ∀ m (hm : m < 2*N), P ⟨m, hm⟩ 1 = S (m+1))
    (hzero : ∀ m (hm : m < 2*N), P ⟨m, hm⟩ 0 = S m)
    (Kp : Fin (2*N) → NNReal) (hKp : ∀ m, LipschitzOnWith (Kp m) (P m) (Icc 0 1)) :
    ∀ n, n ≤ 2*N → LipschitzOnWith (nbodyK Kp n) (nbodyConcat x P n) (Icc 0 n) := by
  intro n
  induction n with
  | zero =>
    intro _
    apply LipschitzOnWith.of_dist_le_mul
    intro s _ t _
    simp only [nbodyConcat, nbodyK]
    simp
  | succ n ih =>
    intro hn
    have hnl : n < 2*N := by omega
    have hf : LipschitzOnWith (nbodyK Kp n) (nbodyConcat x P n) (Icc 0 (n:ℝ)) := ih (by omega)
    have hg : LipschitzOnWith (Kp ⟨n, hnl⟩) (fun t : ℝ => P ⟨n, hnl⟩ (t - (n:ℝ)))
        (Icc (n:ℝ) ((n:ℝ) + 1)) :=
      lipschitzOnWith_sub_const (c := (n:ℝ)) (hKp ⟨n, hnl⟩)
    have hfc : nbodyConcat x P n (n:ℝ) = P ⟨n, hnl⟩ ((n:ℝ) - n) := by
      rw [nbodyConcat_self x P S h0 hstep n (by omega), sub_self]
      exact (hzero n hnl).symm
    have hp := lipschitzOnWith_paste (show (0:ℝ) ≤ (n:ℝ) by positivity)
      (show (n:ℝ) ≤ ((n:ℝ) + 1) by linarith) hfc hf hg
    have hfun : nbodyConcat x P (n+1) =
        fun t : ℝ => if t ≤ (n:ℝ) then nbodyConcat x P n t else P ⟨n, hnl⟩ (t - (n:ℝ)) := by
      funext t
      simp only [nbodyConcat]
      by_cases ht : t ≤ (n:ℝ)
      · rw [if_pos ht, if_pos ht]
      · rw [if_neg ht, if_neg ht, dif_pos hnl]
    rw [hfun, show nbodyK Kp (n+1) = max (nbodyK Kp n) (Kp ⟨n, hnl⟩) from by
      simp only [nbodyK, dif_pos hnl],
      show Icc (0:ℝ) (((n+1:ℕ):ℝ)) = Icc 0 ((n:ℝ) + 1) from by rw [Nat.cast_add, Nat.cast_one]]
    exact hp

end Assembly

end StateLemmas

/-- In a finite-dimensional real inner product space `E` of dimension at least two, two
collision-free configurations `x y` of `EuclideanSpace E (Fin N)` (pairwise distinct coordinates)
are joined by a curve `γ` on some `[0,τ]`, `τ > 0`, that is absolutely continuous, collision-free
at every time, and whose derivative has finite `L²` norm on `(0,τ]`.

This strengthens `Commons.Topology.Metric.exists_absolutelyContinuousOnInterval_avoiding_collisions`
by the `L²` bound, which follows from the fact that the path can be taken Lipschitz: build the path
one body at a time (`EuclideanSpace E (Fin N)` is `Fin N → E`), each individual move being a
Lipschitz (e.g. piecewise-linear-ish) path in `E \ (finite set)`, which exists because
`2 ≤ finrank ℝ E`.  A Lipschitz path is absolutely continuous
(`LipschitzOnWith.absolutelyContinuousOnInterval`) and its derivative is bounded a.e. by the
Lipschitz constant, so the `L²` integral is finite. -/
theorem exists_path_avoiding_collisions_with_deriv_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : 2 ≤ Module.finrank ℝ E) {N : ℕ}
    {x y : EuclideanSpace E (Fin N)}
    (hx : ∀ i j, i ≠ j → x i ≠ x j) (hy : ∀ i j, i ≠ j → y i ≠ y j) :
    ∃ (τ : ℝ) (γ : ℝ → EuclideanSpace E (Fin N)), 0 < τ ∧ γ 0 = x ∧ γ τ = y ∧
      AbsolutelyContinuousOnInterval γ 0 τ ∧
      (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (‖deriv γ t‖ ^ 2)) < ⊤ ∧
      ∀ t ∈ Set.Icc 0 τ, ∀ i j, i ≠ j → γ t i ≠ γ t j := by
  classical
  by_cases hN : N = 0
  · subst hN
    haveI : Subsingleton (EuclideanSpace E (Fin 0)) := inferInstance
    have hconst : LipschitzOnWith 0 (fun _ : ℝ => x) (Icc 0 1) :=
      LipschitzOnWith.of_dist_le_mul (fun a _ b _ => by simp)
    refine ⟨1, fun _ => x, one_pos, rfl, Subsingleton.elim x y, ?_, ?_, ?_⟩
    · exact absolutelyContinuousOnInterval_of_lipschitzOnWith (by norm_num) hconst
    · exact lintegral_deriv_sq_lt_top_of_lipschitzOnWith (by norm_num) hconst
    · intro t _ i j hij
      exact absurd (Subsingleton.elim i j) hij
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
    let xFn : Fin N → E := fun i => x i
    let yFn : Fin N → E := fun i => y i
    obtain ⟨z, hz1, hz2, hz3⟩ := Commons.LinearAlgebra.exists_generic_config xFn yFn
    have hz : (∀ i j, i ≠ j → z i ≠ z j) ∧ (∀ i j, z i ≠ xFn j) ∧ (∀ i j, z i ≠ yFn j) :=
      ⟨hz1, hz2, hz3⟩
    -- the individual moves
    have hmoveA : ∀ k : Fin N, ∃ (K : NNReal) (ψ : ℝ → E),
        ψ 0 = xFn k ∧ ψ 1 = z k ∧ LipschitzOnWith K ψ (Icc 0 1) ∧
        ∀ t ∈ Icc (0:ℝ) 1, ψ t ∉ (Finset.univ.erase k).image
          (fun i : Fin N => if i.val < k.val then z i else xFn i) := by
      intro k
      have hpk : xFn k ∉ (Finset.univ.erase k).image
          (fun i : Fin N => if i.val < k.val then z i else xFn i) := by
        intro hmem
        obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hmem
        rw [Finset.mem_erase] at hi
        obtain ⟨hik, _⟩ := hi
        by_cases hlt : i.val < k.val
        · rw [if_pos hlt] at heq
          exact hz2 i k heq
        · rw [if_neg hlt] at heq
          exact hx i k hik heq
      have hqk : z k ∉ (Finset.univ.erase k).image
          (fun i : Fin N => if i.val < k.val then z i else xFn i) := by
        intro hmem
        obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hmem
        rw [Finset.mem_erase] at hi
        obtain ⟨hik, _⟩ := hi
        by_cases hlt : i.val < k.val
        · rw [if_pos hlt] at heq
          exact hz1 i k hik heq
        · rw [if_neg hlt] at heq
          exact hz2 k i heq.symm
      exact exists_lipschitz_path_avoiding_finset hdim _ hpk hqk
    have hmoveB : ∀ k : Fin N, ∃ (K : NNReal) (ψ : ℝ → E),
        ψ 0 = z k ∧ ψ 1 = yFn k ∧ LipschitzOnWith K ψ (Icc 0 1) ∧
        ∀ t ∈ Icc (0:ℝ) 1, ψ t ∉ (Finset.univ.erase k).image
          (fun i : Fin N => if i.val < k.val then yFn i else z i) := by
      intro k
      have hpk : z k ∉ (Finset.univ.erase k).image
          (fun i : Fin N => if i.val < k.val then yFn i else z i) := by
        intro hmem
        obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hmem
        rw [Finset.mem_erase] at hi
        obtain ⟨hik, _⟩ := hi
        by_cases hlt : i.val < k.val
        · rw [if_pos hlt] at heq
          exact hz3 k i heq.symm
        · rw [if_neg hlt] at heq
          exact hz1 i k hik heq
      have hqk : yFn k ∉ (Finset.univ.erase k).image
          (fun i : Fin N => if i.val < k.val then yFn i else z i) := by
        intro hmem
        obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hmem
        rw [Finset.mem_erase] at hi
        obtain ⟨hik, _⟩ := hi
        by_cases hlt : i.val < k.val
        · rw [if_pos hlt] at heq
          exact hy i k hik heq
        · rw [if_neg hlt] at heq
          exact hz3 i k heq
      exact exists_lipschitz_path_avoiding_finset hdim _ hpk hqk
    choose KA ψA hψA0 hψA1 hψAlip hψAav using hmoveA
    choose KB ψB hψB0 hψB1 hψBlip hψBav using hmoveB
    have havA : ∀ k : Fin N, ∀ s ∈ Icc (0:ℝ) 1, ∀ i : Fin N, i ≠ k →
        ψA k s ≠ (if i.val < k.val then z i else xFn i) := by
      intro k s hs i hik
      exact fun h => hψAav k s hs
        (Finset.mem_image.mpr ⟨i, Finset.mem_erase.mpr ⟨hik, Finset.mem_univ i⟩, h.symm⟩)
    have havB : ∀ k : Fin N, ∀ s ∈ Icc (0:ℝ) 1, ∀ i : Fin N, i ≠ k →
        ψB k s ≠ (if i.val < k.val then yFn i else z i) := by
      intro k s hs i hik
      exact fun h => hψBav k s hs
        (Finset.mem_image.mpr ⟨i, Finset.mem_erase.mpr ⟨hik, Finset.mem_univ i⟩, h.symm⟩)
    -- the concatenated path
    let P : Fin (2*N) → ℝ → EuclideanSpace E (Fin N) := nbodyPiece xFn yFn z ψA ψB
    let S : ℕ → EuclideanSpace E (Fin N) := fun m => nbodyState xFn yFn z m
    have hPz : ∀ m (hm : m < 2*N), P ⟨m, hm⟩ 0 = S m :=
      fun m hm => nbodyPiece_apply_zero xFn yFn z ψA ψB hψA0 hψB0 ⟨m, hm⟩
    have hPo : ∀ m (hm : m < 2*N), P ⟨m, hm⟩ 1 = S (m+1) :=
      fun m hm => nbodyPiece_apply_one xFn yFn z ψA ψB hψA1 hψB1 ⟨m, hm⟩
    have hS0 : S 0 = x := nbodyState_zero x yFn z
    have hKp : ∀ m, LipschitzOnWith (nbodyKp KA KB m) (P m) (Icc 0 1) :=
      fun m => nbodyPiece_lipschitz xFn yFn z ψA ψB KA KB hψAlip hψBlip m
    have hPcf : ∀ m (hm : m < 2*N), ∀ s ∈ Icc (0:ℝ) 1, ∀ i j, i ≠ j →
        P ⟨m, hm⟩ s i ≠ P ⟨m, hm⟩ s j :=
      fun m hm s hs i j hij =>
        nbodyPiece_collFree xFn yFn z ψA ψB havA havB hx hy hz ⟨m, hm⟩ hs i j hij
    have hLip := nbodyConcat_lipschitz x P S hS0 hPo hPz (nbodyKp KA KB) hKp (2*N) le_rfl
    have hcf := nbodyConcat_collFree x P hx hPcf (2*N) le_rfl
    refine ⟨((2*N : ℕ) : ℝ), nbodyConcat x P (2*N), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact_mod_cast Nat.mul_pos (by norm_num) hNpos
    · rw [nbodyConcat_stabilize x P 0 (2*N) (Nat.zero_le _) 0
        (by norm_num : (0:ℝ) ≤ ((0:ℕ):ℝ))]
      rfl
    · rw [nbodyConcat_self x P S hS0 hPo (2*N) le_rfl]
      change nbodyState xFn yFn z (2*N) = y
      rw [nbodyState, nbodySrcState_last xFn yFn z hNpos]
    · exact absolutelyContinuousOnInterval_of_lipschitzOnWith (by positivity) hLip
    · exact lintegral_deriv_sq_lt_top_of_lipschitzOnWith (by positivity) hLip
    · intro t ht i j hij
      exact hcf t ht i j hij

end Commons.Topology.Metric
