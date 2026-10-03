import Mathlib
import Submission.Work.A3.real_poly_levelSet_volume_le
import Submission.Work.A3.min_rpow_integral_bound
import Submission.Work.A3.oscInt_levelSet_le
import Submission.Work.A3.integrable_min_rpow

/-!
# The singular-integral bound for the A3 circle method

`Work.A3.singInt Q N β = ∫_t e^{-2πi β Q(t)}` is the singular integral of the circle-method
major arcs.  This file proves the sharp (first-derivative-test) estimate

  `∫_ℝ ‖singInt Q N β‖^{2s} dβ ≤ C^{2s} N^{2s-d}`,  `d = Q.natDegree`,  `2s > d`,

by bounding the integrand pointwise by `min N (C |β|^{-1/d})` and integrating.

The proof of the pointwise bound is a van der Corput first-derivative argument: split `[0,N]` at
the zeros of `Q''` (a finite set of at most `d-2` points); on the pieces `Q''` has constant sign,
so `Q'` is monotone, and the level set `{|Q'| ≤ λ/β}` of a monotone function is an interval --
on its complement the first-derivative test applies.  The measure of the level set is controlled
by the sublevel-set bound for polynomials.
-/

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace Work.A3

open Polynomial MeasureTheory

noncomputable section

/-- The polynomial phase `t ↦ β P(t)`. -/
def polyPhase (P : Polynomial ℝ) (β : ℝ) : ℝ → ℝ := fun t => β * P.eval t

lemma deriv_polyPhase (P : Polynomial ℝ) (β : ℝ) :
    deriv (polyPhase P β) = fun t => β * (P.derivative).eval t := by
  funext t
  have hfun : polyPhase P β = fun s : ℝ => (Polynomial.C β * P).eval s := by
    funext s
    simp only [polyPhase, Polynomial.eval_mul, Polynomial.eval_C]
  rw [hfun, (Polynomial.hasDerivAt (Polynomial.C β * P) t).deriv]
  simp only [Polynomial.derivative_mul, Polynomial.derivative_C, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_zero, zero_mul, zero_add]

lemma deriv_deriv_polyPhase (P : Polynomial ℝ) (β : ℝ) :
    deriv (deriv (polyPhase P β)) = fun t => β * (P.derivative.derivative).eval t := by
  have h1 : deriv (polyPhase P β) = polyPhase P.derivative β := deriv_polyPhase P β
  rw [h1]
  exact deriv_polyPhase P.derivative β

lemma continuous_polyPhase (P : Polynomial ℝ) (β : ℝ) : Continuous (polyPhase P β) := by
  change Continuous (fun t : ℝ => β * P.eval t)
  exact continuous_const.mul (Polynomial.continuous P)

lemma contDiffOn_polyPhase (P : Polynomial ℝ) (β : ℝ) (a b : ℝ) :
    ContDiffOn ℝ 2 (polyPhase P β) (Set.Icc a b) := by
  change ContDiffOn ℝ 2 (fun t : ℝ => β * P.eval t) (Set.Icc a b)
  exact contDiffOn_const.mul (contDiffOn_poly_eval P)

/-- If `g` is continuous on `[a,b]` and has no zeros in the interior, then it has constant
(weak) sign there. -/
lemma sign_const_of_no_zero {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Set.Icc a b))
    (hno : ∀ z : ℝ, z ∈ Set.Ioo a b → g z ≠ 0) :
    (∀ x : ℝ, x ∈ Set.Ioo a b → 0 ≤ g x) ∨ (∀ x : ℝ, x ∈ Set.Ioo a b → g x ≤ 0) := by
  by_contra h
  push_neg at h
  obtain ⟨x, hxab, hxg⟩ := h.1
  obtain ⟨y, hyab, hyg⟩ := h.2
  have hzex : ∃ z ∈ Set.Ioo a b, g z = 0 := by
    rcases le_total x y with hxy | hyx
    · have hcont : ContinuousOn g (Set.Icc x y) :=
        hg.mono (Set.Icc_subset_Icc hxab.1.le hyab.2.le)
      have hmem : (0 : ℝ) ∈ Set.Ioo (g x) (g y) := ⟨hxg, hyg⟩
      obtain ⟨z, hz, hzg⟩ := intermediate_value_Ioo hxy hcont hmem
      exact ⟨z, ⟨lt_trans hxab.1 hz.1, lt_trans hz.2 hyab.2⟩, hzg⟩
    · have hcont : ContinuousOn (fun t => -g t) (Set.Icc y x) :=
        (hg.mono (Set.Icc_subset_Icc hyab.1.le hxab.2.le)).neg
      have hmem : (0 : ℝ) ∈ Set.Ioo (-g y) (-g x) := ⟨by linarith, by linarith⟩
      obtain ⟨z, hz, hzg⟩ := intermediate_value_Ioo hyx hcont hmem
      exact ⟨z, ⟨lt_trans hyab.1 hz.1, lt_trans hz.2 hxab.2⟩, by simpa using hzg⟩
  obtain ⟨z, hzab, hz0⟩ := hzex
  exact hno z hzab hz0

/-- Splitting the level-set measure along a subdivision of the interval. -/
lemma measure_levelset_split (Q : Set ℝ) (hQm : MeasurableSet Q)
    {a z b : ℝ} (haz : a ≤ z) (hzb : z ≤ b) :
    volume {t ∈ Set.Icc a z | t ∈ Q} + volume {t ∈ Set.Icc z b | t ∈ Q}
      = volume {t ∈ Set.Icc a b | t ∈ Q} := by
  have hs : {t ∈ Set.Icc a z | t ∈ Q} = Q ∩ Set.Icc a z := by
    ext t; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
  have hs' : {t ∈ Set.Icc z b | t ∈ Q} = Q ∩ Set.Icc z b := by
    ext t; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
  have hu : {t ∈ Set.Icc a b | t ∈ Q} = Q ∩ Set.Icc a b := by
    ext t; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
  rw [hs, hs', hu]
  have hunion : (Q ∩ Set.Icc a z) ∪ (Q ∩ Set.Icc z b) = Q ∩ Set.Icc a b := by
    rw [← Set.inter_union_distrib_left, Set.Icc_union_Icc_eq_Icc haz hzb]
  have hinter : (Q ∩ Set.Icc a z) ∩ (Q ∩ Set.Icc z b) ⊆ {z} := by
    rintro t ⟨⟨-, h1, h2⟩, ⟨-, h3, -⟩⟩
    simp only [Set.mem_singleton_iff]
    exact le_antisymm h2 h3
  have hzero : volume ((Q ∩ Set.Icc a z) ∩ (Q ∩ Set.Icc z b)) = 0 :=
    measure_mono_null hinter (measure_singleton z)
  have h := measure_union_add_inter (μ := volume) (Q ∩ Set.Icc a z)
    (t := Q ∩ Set.Icc z b) (hQm.inter measurableSet_Icc)
  rw [hunion, hzero, add_zero] at h
  exact h.symm

/-- The base case of the induction: on an interval where `P''` has no zero in the interior
the van der Corput first-derivative bound applies directly. -/
lemma oscInt_base (P : Polynomial ℝ) (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam)
    (hD2 : ∀ (f : ℝ → ℝ) (u v m : ℝ), u ≤ v → 0 < m → ContDiffOn ℝ 2 f (Set.Icc u v) →
      (∀ x : ℝ, x ∈ Set.Ioo u v → 0 ≤ deriv (deriv f) x) →
      ‖∫ x in u..v, oscPhase f x‖ ≤
        (volume {t ∈ Set.Icc u v | |deriv f t| ≤ m}).toReal + 16 / m)
    {a b : ℝ} (hab : a ≤ b)
    (hno : ∀ z : ℝ, z ∈ Set.Ioo a b → (P.derivative.derivative).eval z ≠ 0) :
    ‖∫ x in a..b, oscPhase (polyPhase P β) x‖ ≤
      (volume {t ∈ Set.Icc a b | |deriv (polyPhase P β) t| ≤ lam}).toReal + 16 / lam := by
  rcases sign_const_of_no_zero hab (continuousOn_poly_eval P.derivative.derivative (Set.Icc a b))
    hno with hpos | hneg
  · exact hD2 (polyPhase P β) a b lam hab hlam (contDiffOn_polyPhase P β a b) (fun x hx => by
      rw [deriv_deriv_polyPhase]
      exact mul_nonneg hβ.le (hpos x hx))
  · have hfun : polyPhase P (-β) = -(polyPhase P β) := by
      funext t
      change (-β) * P.eval t = -(β * P.eval t)
      ring
    have hset : {t ∈ Set.Icc a b | |deriv (polyPhase P (-β)) t| ≤ lam}
        = {t ∈ Set.Icc a b | |deriv (polyPhase P β) t| ≤ lam} := by
      ext t
      simp only [Set.mem_setOf_eq]
      rw [deriv_polyPhase, deriv_polyPhase]
      have h1 : |(-β) * (P.derivative).eval t| = |β * (P.derivative).eval t| := by
        rw [show (-β) * (P.derivative).eval t = -(β * (P.derivative).eval t) by ring, abs_neg]
      rw [h1]
    have hnorm : ‖∫ x in a..b, oscPhase (polyPhase P (-β)) x‖
        = ‖∫ x in a..b, oscPhase (polyPhase P β) x‖ := by
      rw [hfun]
      exact norm_intervalIntegral_oscPhase_neg (polyPhase P β) hab (continuous_polyPhase P β)
    have h := hD2 (polyPhase P (-β)) a b lam hab hlam (contDiffOn_polyPhase P (-β) a b)
      (fun x hx => by
        rw [deriv_deriv_polyPhase]
        have hx0 : (P.derivative.derivative).eval x ≤ 0 := hneg x hx
        nlinarith [hβ])
    rwa [hset, hnorm] at h

/-- The induction engine. -/
lemma oscInt_le_levelSet_aux (P : Polynomial ℝ) (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam)
    (hD2 : ∀ (f : ℝ → ℝ) (u v m : ℝ), u ≤ v → 0 < m → ContDiffOn ℝ 2 f (Set.Icc u v) →
      (∀ x : ℝ, x ∈ Set.Ioo u v → 0 ≤ deriv (deriv f) x) →
      ‖∫ x in u..v, oscPhase f x‖ ≤
        (volume {t ∈ Set.Icc u v | |deriv f t| ≤ m}).toReal + 16 / m) :
    ∀ (n : ℕ) (a b : ℝ), a ≤ b → ∀ (s : Finset ℝ), s.card ≤ n →
      (∀ z : ℝ, z ∈ Set.Ioo a b → (P.derivative.derivative).eval z = 0 → z ∈ s) →
      ‖∫ x in a..b, oscPhase (polyPhase P β) x‖ ≤
        (volume {t ∈ Set.Icc a b | |deriv (polyPhase P β) t| ≤ lam}).toReal
          + 16 * 2 ^ n / lam := by
  intro n
  induction n with
  | zero =>
      intro a b hab s hs hz
      have hne : ∀ z : ℝ, z ∈ Set.Ioo a b → (P.derivative.derivative).eval z ≠ 0 := by
        intro z hzab hz0
        have hmem : z ∈ s := hz z hzab hz0
        rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hs)] at hmem
        exact absurd hmem (Finset.notMem_empty z)
      have hbase := oscInt_base P β lam hβ hlam hD2 hab hne
      simpa using hbase
  | succ n ih =>
      intro a b hab s hs hz
      have hQm : MeasurableSet {t : ℝ | |deriv (polyPhase P β) t| ≤ lam} := by
        have hcont : Continuous fun t : ℝ => deriv (polyPhase P β) t := by
          rw [deriv_polyPhase]
          exact continuous_const.mul (Polynomial.continuous P.derivative)
        have heq : {t : ℝ | |deriv (polyPhase P β) t| ≤ lam}
            = (fun t : ℝ => deriv (polyPhase P β) t) ⁻¹' Set.Icc (-lam) lam := by
          ext t
          simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Icc, abs_le]
        rw [heq]
        exact (isClosed_Icc.preimage hcont).measurableSet
      by_cases hzero : ∃ z ∈ s, z ∈ Set.Ioo a b ∧ (P.derivative.derivative).eval z = 0
      · obtain ⟨z, hzs, hzab, hz0⟩ := hzero
        have haz : a ≤ z := hzab.1.le
        have hzb : z ≤ b := hzab.2.le
        have hcard : (s.erase z).card ≤ n := by
          have h1 : (s.erase z).card + 1 = s.card := Finset.card_erase_add_one hzs
          omega
        have hc1 : ∀ z' : ℝ, z' ∈ Set.Ioo a z →
            (P.derivative.derivative).eval z' = 0 → z' ∈ s.erase z := by
          intro z' hz' hz'0
          refine Finset.mem_erase.mpr ⟨?_, hz z' ⟨hz'.1, lt_trans hz'.2 hzab.2⟩ hz'0⟩
          exact ne_of_lt hz'.2
        have hc2 : ∀ z' : ℝ, z' ∈ Set.Ioo z b →
            (P.derivative.derivative).eval z' = 0 → z' ∈ s.erase z := by
          intro z' hz' hz'0
          refine Finset.mem_erase.mpr ⟨?_, hz z' ⟨lt_trans hzab.1 hz'.1, hz'.2⟩ hz'0⟩
          exact ne_of_gt hz'.1
        have h1 := ih a z haz (s.erase z) hcard hc1
        have h2 := ih z b hzb (s.erase z) hcard hc2
        have hint1 : IntervalIntegrable (oscPhase (polyPhase P β)) volume a z :=
          (continuous_oscPhase (continuous_polyPhase P β)).intervalIntegrable a z
        have hint2 : IntervalIntegrable (oscPhase (polyPhase P β)) volume z b :=
          (continuous_oscPhase (continuous_polyPhase P β)).intervalIntegrable z b
        have hsplit : ‖∫ x in a..b, oscPhase (polyPhase P β) x‖
            ≤ ‖∫ x in a..z, oscPhase (polyPhase P β) x‖
              + ‖∫ x in z..b, oscPhase (polyPhase P β) x‖ := by
          rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
          exact norm_add_le _ _
        have hmeas := measure_levelset_split {t : ℝ | |deriv (polyPhase P β) t| ≤ lam} hQm haz hzb
        simp only [Set.mem_setOf_eq] at hmeas
        have hfin1 : volume {t ∈ Set.Icc a z | |deriv (polyPhase P β) t| ≤ lam} ≠ ⊤ := by
          have hle : {t ∈ Set.Icc a z | |deriv (polyPhase P β) t| ≤ lam} ⊆ Set.Icc a z :=
            fun t ht => ht.1
          refine ne_of_lt (lt_of_le_of_lt (measure_mono hle) ?_)
          rw [Real.volume_Icc]
          exact ENNReal.ofReal_lt_top
        have hfin2 : volume {t ∈ Set.Icc z b | |deriv (polyPhase P β) t| ≤ lam} ≠ ⊤ := by
          have hle : {t ∈ Set.Icc z b | |deriv (polyPhase P β) t| ≤ lam} ⊆ Set.Icc z b :=
            fun t ht => ht.1
          refine ne_of_lt (lt_of_le_of_lt (measure_mono hle) ?_)
          rw [Real.volume_Icc]
          exact ENNReal.ofReal_lt_top
        have hmeas' : (volume {t ∈ Set.Icc a z | |deriv (polyPhase P β) t| ≤ lam}).toReal
            + (volume {t ∈ Set.Icc z b | |deriv (polyPhase P β) t| ≤ lam}).toReal
            = (volume {t ∈ Set.Icc a b | |deriv (polyPhase P β) t| ≤ lam}).toReal := by
          rw [← ENNReal.toReal_add hfin1 hfin2, hmeas]
        calc ‖∫ x in a..b, oscPhase (polyPhase P β) x‖
            ≤ ‖∫ x in a..z, oscPhase (polyPhase P β) x‖
                + ‖∫ x in z..b, oscPhase (polyPhase P β) x‖ := hsplit
          _ ≤ ((volume {t ∈ Set.Icc a z | |deriv (polyPhase P β) t| ≤ lam}).toReal
                + 16 * 2 ^ n / lam)
              + ((volume {t ∈ Set.Icc z b | |deriv (polyPhase P β) t| ≤ lam}).toReal
                + 16 * 2 ^ n / lam) := add_le_add h1 h2
          _ = (volume {t ∈ Set.Icc a z | |deriv (polyPhase P β) t| ≤ lam}).toReal
              + (volume {t ∈ Set.Icc z b | |deriv (polyPhase P β) t| ≤ lam}).toReal
              + 2 * (16 * 2 ^ n / lam) := by ring
          _ = (volume {t ∈ Set.Icc a b | |deriv (polyPhase P β) t| ≤ lam}).toReal
              + 2 * (16 * 2 ^ n / lam) := by rw [hmeas']
          _ = (volume {t ∈ Set.Icc a b | |deriv (polyPhase P β) t| ≤ lam}).toReal
              + 16 * 2 ^ (n + 1) / lam := by
              have hmain : 2 * (16 * 2 ^ n / lam) = 16 * 2 ^ (n + 1) / lam := by
                rw [pow_succ]
                ring
              rw [hmain]
      · refine le_trans (oscInt_base P β lam hβ hlam hD2 hab ?_) ?_
        · intro z hzab hz0
          exact hzero ⟨z, hz z hzab hz0, hzab, hz0⟩
        · have h2n : (1 : ℝ) ≤ 2 ^ (n + 1) := one_le_pow₀ (by norm_num)
          have hmul : (16 : ℝ) ≤ 16 * 2 ^ (n + 1) := by nlinarith [h2n]
          have := div_le_div_of_nonneg_right hmul hlam.le
          linarith



/-! ## The level-set bound for the derivative and the pointwise bound -/

/-- The level set of `deriv (polyPhase P β)` (threshold `lam`) lies in a level set of `P'`
(threshold `lam/β`). -/
lemma levelSet_deriv_subset (P : Polynomial ℝ) {β lam : ℝ} (hβ : 0 < β) {a b : ℝ} :
    {t ∈ Set.Icc a b | |deriv (polyPhase P β) t| ≤ lam}
      ⊆ {t : ℝ | |(P.derivative).eval t| ≤ lam / β} := by
  intro t ht
  rw [deriv_polyPhase] at ht
  have h1 : β * |(P.derivative).eval t| ≤ lam := by
    simpa only [abs_mul, abs_of_pos hβ] using ht.2
  change |(P.derivative).eval t| ≤ lam / β
  rw [le_div_iff₀ hβ, mul_comm]
  exact h1

/-- `(β^(-1/d))^d = β⁻¹` for `β > 0`, `d > 0`. -/
lemma rpow_neg_inv_pow (β : ℝ) (hβ : 0 < β) (d : ℕ) (hd : 0 < d) :
    (β ^ (-(1 : ℝ) / (d : ℝ))) ^ d = β⁻¹ := by
  rw [← Real.rpow_natCast (β ^ (-(1 : ℝ) / (d : ℝ))) d]
  rw [← Real.rpow_mul hβ.le]
  have hd0 : ((d : ℕ) : ℝ) ≠ 0 := by positivity
  have hexp : (-(1 : ℝ) / (d : ℝ)) * (d : ℝ) = -1 := by
    field_simp
  rw [hexp, Real.rpow_neg_one]

/-- `(x^n)^(1/n) = x` for `x > 0`, `n > 0`. -/
lemma rpow_nat_pow_inv (x : ℝ) (hx : 0 < x) (n : ℕ) (hn : 0 < n) :
    (x ^ n) ^ (((n : ℕ) : ℝ))⁻¹ = x := by
  rw [← Real.rpow_natCast x n]
  rw [← Real.rpow_mul hx.le]
  have hn0 : (((n : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [mul_inv_cancel₀ hn0, Real.rpow_one]

/-- The norm of the singular integral is unchanged when `β` is negated. -/
lemma singInt_norm_neg (Q : Polynomial ℤ) (N : ℕ) (β : ℝ) :
    ‖singInt Q N β‖ = ‖singInt Q N (-β)‖ := by
  have hN : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  set f : ℝ → ℝ := fun t => β * (Qreal Q).eval t with hf
  set g : ℝ → ℝ := fun t => -β * (Qreal Q).eval t with hg
  have hgf : g = -f := by
    funext t
    simp only [hg, hf, Pi.neg_apply]
    ring
  rw [singInt_eq_integral_oscPhase, singInt_eq_integral_oscPhase]
  rw [show (fun t => β * (Qreal Q).eval t) = f from rfl,
      show (fun t => -β * (Qreal Q).eval t) = g from rfl, hgf, oscPhase_neg_fun]
  rw [intervalIntegral_star (fun x => oscPhase f x) (0:ℝ) (N:ℝ)
    ((continuous_oscPhase (by rw [hf]; exact continuous_const.mul (Polynomial.continuous _))).intervalIntegrable
      (0:ℝ) (N:ℝ))]
  rw [starRingEnd_apply, norm_star]

/-- The pointwise bound for the singular integral at positive `β`. -/
lemma singInt_le_pos (Q : Polynomial ℤ) (hd : 2 ≤ Q.natDegree)
    (hD2 : ∀ (f : ℝ → ℝ) (u v m : ℝ), u ≤ v → 0 < m → ContDiffOn ℝ 2 f (Set.Icc u v) →
      (∀ x : ℝ, x ∈ Set.Ioo u v → 0 ≤ deriv (deriv f) x) →
      ‖∫ x in u..v, oscPhase f x‖ ≤
        (volume {t ∈ Set.Icc u v | |deriv f t| ≤ m}).toReal + 16 / m)
    (Clev : ℝ) (hClevpos : 0 < Clev)
    (hClev : ∀ ε : ℝ, 0 < ε → volume {t : ℝ | |((Qreal Q).derivative).eval t| ≤ ε}
        ≤ ENNReal.ofReal (Clev * ε ^ ((((Qreal Q).derivative).natDegree : ℝ))⁻¹))
    {N : ℕ} {β : ℝ} (hβ : 0 < β) :
    ‖singInt Q N β‖ ≤ min (N : ℝ)
      ((Clev + 16 * 2 ^ (Q.natDegree - 2)) * β ^ (-(1 : ℝ) / (Q.natDegree : ℝ))) := by
  set P := Qreal Q with hPdef
  have hPd : P.natDegree = Q.natDegree := by
    rw [hPdef, Qreal]
    exact Polynomial.natDegree_map_eq_of_injective (f := Int.castRingHom ℝ)
      (fun a b h => Int.cast_injective h) Q
  set mu : ℝ := β ^ (-(1 : ℝ) / (Q.natDegree : ℝ)) with hmudef
  have hmupos : 0 < mu := Real.rpow_pos_of_pos hβ _
  set lam : ℝ := β * mu ^ (Q.natDegree - 1) with hlamdef
  have hlamp : 0 < lam := mul_pos hβ (pow_pos hmupos _)
  have hmupow : mu ^ Q.natDegree = β⁻¹ := by
    rw [hmudef]
    exact rpow_neg_inv_pow β hβ Q.natDegree (by omega)
  have hlam_inv : lam = mu⁻¹ := by
    have hmune : mu ≠ 0 := ne_of_gt hmupos
    have hpd : mu ^ (Q.natDegree - 1) * mu = mu ^ Q.natDegree := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ Q.natDegree)]
    have h1 : (β * mu ^ (Q.natDegree - 1)) * mu = 1 := by
      rw [mul_assoc, hpd, hmupow, mul_inv_cancel₀ (ne_of_gt hβ)]
    have h2 : mu⁻¹ * mu = 1 := inv_mul_cancel₀ hmune
    rw [hlamdef]
    exact mul_right_cancel₀ hmune (by rw [h1, h2])
  have hlamβ : lam / β = mu ^ (Q.natDegree - 1) := by
    rw [hlamdef]; field_simp
  have hlevel : (volume {t ∈ Set.Icc (0:ℝ) (N:ℝ) | |deriv (polyPhase P β) t| ≤ lam}).toReal
      ≤ Clev * mu := by
    have hsubset : {t ∈ Set.Icc (0:ℝ) (N:ℝ) | |deriv (polyPhase P β) t| ≤ lam}
        ⊆ {t : ℝ | |((Qreal Q).derivative).eval t| ≤ lam / β} := by
      rw [hPdef]
      exact levelSet_deriv_subset (Qreal Q) hβ
    have hbound : volume {t : ℝ | |((Qreal Q).derivative).eval t| ≤ lam / β}
        ≤ ENNReal.ofReal (Clev * (lam / β) ^ ((((Qreal Q).derivative).natDegree : ℝ))⁻¹) :=
      hClev (lam / β) (div_pos hlamp hβ)
    have hexp : (lam / β) ^ ((((Qreal Q).derivative).natDegree : ℝ))⁻¹ = mu := by
      rw [hlamβ, Polynomial.natDegree_derivative, hPd]
      exact rpow_nat_pow_inv mu hmupos (Q.natDegree - 1) (by omega)
    rw [hexp] at hbound
    have hfin : ENNReal.ofReal (Clev * mu) ≠ ⊤ := ENNReal.ofReal_ne_top
    calc (volume {t ∈ Set.Icc (0:ℝ) (N:ℝ) | |deriv (polyPhase P β) t| ≤ lam}).toReal
        ≤ (ENNReal.ofReal (Clev * mu)).toReal :=
          ENNReal.toReal_mono hfin ((measure_mono hsubset).trans hbound)
      _ = Clev * mu := ENNReal.toReal_ofReal (by positivity)
  have hP''ne : P.derivative.derivative ≠ 0 := by
    intro h
    have h1 : P.derivative.natDegree = 0 := (Polynomial.derivative_eq_zero).mp h
    rw [Polynomial.natDegree_derivative, hPd] at h1
    omega
  have hzmem : ∀ z : ℝ, z ∈ Set.Ioo (0:ℝ) (N:ℝ) →
      (P.derivative.derivative).eval z = 0 → z ∈ (P.derivative.derivative).roots.toFinset := by
    intro z _ hz0
    refine Multiset.mem_toFinset.mpr ?_
    rw [Polynomial.mem_roots']
    exact ⟨hP''ne, hz0⟩
  have hroots : (P.derivative.derivative).roots.toFinset.card ≤ (P.derivative.derivative).natDegree :=
    (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _)
  have hmain := oscInt_le_levelSet_aux P β lam hβ hlamp hD2
    (P.derivative.derivative).natDegree (0:ℝ) (N:ℝ) (Nat.cast_nonneg N)
    (P.derivative.derivative).roots.toFinset hroots hzmem
  have hsing : ‖singInt Q N β‖ = ‖∫ x in (0:ℝ)..(N:ℝ), oscPhase (polyPhase P β) x‖ := by
    rw [hPdef, singInt_eq_integral_oscPhase]
    rfl
  have hnd : 2 ^ ((P.derivative.derivative).natDegree) ≤ 2 ^ (Q.natDegree - 2) := by
    apply Nat.pow_le_pow_right (by norm_num)
    rw [Polynomial.natDegree_derivative, Polynomial.natDegree_derivative, hPd]
    omega
  have hnd' : (2 : ℝ) ^ ((P.derivative.derivative).natDegree) ≤ (2 : ℝ) ^ (Q.natDegree - 2) := by
    exact_mod_cast hnd
  have hbig : ‖singInt Q N β‖
      ≤ (Clev + 16 * 2 ^ (Q.natDegree - 2)) * mu := by
    rw [hsing]
    calc ‖∫ x in (0:ℝ)..(N:ℝ), oscPhase (polyPhase P β) x‖
        ≤ (volume {t ∈ Set.Icc (0:ℝ) (N:ℝ) | |deriv (polyPhase P β) t| ≤ lam}).toReal
            + 16 * 2 ^ ((P.derivative.derivative).natDegree) / lam := hmain
      _ ≤ Clev * mu + 16 * 2 ^ ((P.derivative.derivative).natDegree) * mu := by
          have h2 : 16 * 2 ^ ((P.derivative.derivative).natDegree) / lam
              = 16 * 2 ^ ((P.derivative.derivative).natDegree) * mu := by
            rw [hlam_inv, div_eq_mul_inv, inv_inv]
          rw [h2]
          exact add_le_add hlevel le_rfl
      _ ≤ (Clev + 16 * 2 ^ (Q.natDegree - 2)) * mu := by
          have hmul : (16 : ℝ) * 2 ^ ((P.derivative.derivative).natDegree)
              ≤ 16 * 2 ^ (Q.natDegree - 2) := by nlinarith [hnd']
          have h3 := mul_le_mul_of_nonneg_right hmul hmupos.le
          nlinarith [h3]
  have htriv : ‖singInt Q N β‖ ≤ (N : ℝ) := by
    rw [singInt_eq_integral_oscPhase]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := (N:ℝ)) (C := 1)
      (f := fun t => oscPhase (fun t => β * (Qreal Q).eval t) t) (fun t _ => oscPhase_norm_le _ t)
    simpa using h
  rw [hmudef] at hbig
  exact le_min htriv hbig

/-- The pointwise bound for the singular integral, for all `β ≠ 0`. -/
lemma singInt_pointwise (Q : Polynomial ℤ) (hd : 2 ≤ Q.natDegree)
    (hD2 : ∀ (f : ℝ → ℝ) (u v m : ℝ), u ≤ v → 0 < m → ContDiffOn ℝ 2 f (Set.Icc u v) →
      (∀ x : ℝ, x ∈ Set.Ioo u v → 0 ≤ deriv (deriv f) x) →
      ‖∫ x in u..v, oscPhase f x‖ ≤
        (volume {t ∈ Set.Icc u v | |deriv f t| ≤ m}).toReal + 16 / m)
    (hLevel : ∀ (R : Polynomial ℝ), 1 ≤ R.natDegree → ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε →
      volume {t : ℝ | |R.eval t| ≤ ε} ≤ ENNReal.ofReal (C * ε ^ ((R.natDegree : ℝ)⁻¹))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), ∀ β : ℝ, β ≠ 0 →
      ‖singInt Q N β‖ ≤ min (N : ℝ) (C * |β| ^ (-(1 : ℝ) / (Q.natDegree : ℝ))) := by
  have hQd : (Qreal Q).natDegree = Q.natDegree := by
    rw [Qreal]
    exact Polynomial.natDegree_map_eq_of_injective (f := Int.castRingHom ℝ)
      (fun a b h => Int.cast_injective h) Q
  obtain ⟨Clev, hClevpos, hClev⟩ := hLevel (Qreal Q).derivative (by
    rw [Polynomial.natDegree_derivative, hQd]; omega)
  refine ⟨Clev + 16 * 2 ^ (Q.natDegree - 2), by positivity, ?_⟩
  intro N β hβne
  rcases lt_or_gt_of_ne hβne.symm with hpos | hneg
  · have h := singInt_le_pos Q hd hD2 Clev hClevpos hClev (N := N) (β := β) hpos
    rw [abs_of_pos hpos]
    exact h
  · rw [singInt_norm_neg]
    have h := singInt_le_pos Q hd hD2 Clev hClevpos hClev (N := N) (β := -β) (by linarith)
    rw [abs_of_neg hneg]
    exact h

/-- Final assembly (with the three delegated inputs as hypotheses). -/
theorem singInt_bound_of (Q : Polynomial ℤ) (hd : 2 ≤ Q.natDegree)
    (hD2 : ∀ (f : ℝ → ℝ) (u v m : ℝ), u ≤ v → 0 < m → ContDiffOn ℝ 2 f (Set.Icc u v) →
      (∀ x : ℝ, x ∈ Set.Ioo u v → 0 ≤ deriv (deriv f) x) →
      ‖∫ x in u..v, oscPhase f x‖ ≤
        (volume {t ∈ Set.Icc u v | |deriv f t| ≤ m}).toReal + 16 / m)
    (hLevel : ∀ (R : Polynomial ℝ), 1 ≤ R.natDegree → ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε →
      volume {t : ℝ | |R.eval t| ≤ ε} ≤ ENNReal.ofReal (C * ε ^ ((R.natDegree : ℝ)⁻¹)))
    (hD3 : ∀ (C : ℝ), 0 < C → ∀ (d : ℕ), 2 ≤ d → ∃ K : ℝ, 0 < K ∧
      ∀ (N s : ℕ), 1 ≤ N → d < 2 * s →
        ∫ β : ℝ, (min (N : ℝ) (C * |β| ^ (-(1 : ℝ) / (d : ℝ)))) ^ (2 * s)
          ≤ K ^ (2 * s) * (N : ℝ) ^ (2 * s - d))
    (hD4 : ∀ (C : ℝ), 0 < C → ∀ (d : ℕ), 1 ≤ d → ∀ (N s : ℕ), d < 2 * s →
      MeasureTheory.Integrable
        (fun β : ℝ => (min (N : ℝ) (C * |β| ^ (-(1 : ℝ) / (d : ℝ)))) ^ (2 * s))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N s : ℕ), 1 ≤ N → 1 ≤ s → Q.natDegree < 2 * s →
      ∫ β : ℝ, ‖singInt Q N β‖ ^ (2 * s) ≤ C ^ (2 * s) * (N : ℝ) ^ (2 * s - Q.natDegree) := by
  obtain ⟨C₁, hC₁pos, hpt⟩ := singInt_pointwise Q hd hD2 hLevel
  obtain ⟨K, hKpos, hK⟩ := hD3 C₁ hC₁pos Q.natDegree hd
  refine ⟨K, hKpos, ?_⟩
  intro N s hN hs hds
  have hint := hD4 C₁ hC₁pos Q.natDegree (by omega) N s hds
  have hle : ∀ᵐ β : ℝ, ‖singInt Q N β‖ ^ (2 * s)
      ≤ (min (N : ℝ) (C₁ * |β| ^ (-(1 : ℝ) / (Q.natDegree : ℝ)))) ^ (2 * s) := by
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null ?_ (measure_singleton (0:ℝ))
    intro β hβ
    simp only [Set.mem_setOf_eq, not_le] at hβ
    by_contra h0
    have hpow := pow_le_pow_left₀ (norm_nonneg (singInt Q N β)) (hpt N β h0) (2 * s)
    exact absurd hpow (not_le.mpr hβ)
  calc ∫ β, ‖singInt Q N β‖ ^ (2 * s)
      ≤ ∫ β, (min (N : ℝ) (C₁ * |β| ^ (-(1 : ℝ) / (Q.natDegree : ℝ)))) ^ (2 * s) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun β => by positivity) hint hle
    _ ≤ K ^ (2 * s) * (N : ℝ) ^ (2 * s - Q.natDegree) := hK N s hN hds


/-- **The singular-integral bound of the A3 circle method.**  For a polynomial `Q : ℤ[X]` of
degree `d ≥ 2` there is `C > 0` with `∫_ℝ ‖singInt Q N β‖^{2s} dβ ≤ C^{2s} N^{2s-d}` for all
`N ≥ 1` and all `s` with `2s > d`. -/
theorem singInt_bound (Q : Polynomial ℤ) (hd : 2 ≤ Polynomial.natDegree Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N s : ℕ), 1 ≤ N → 1 ≤ s → Polynomial.natDegree Q < 2 * s →
      ∫ β : ℝ, ‖Work.A3.singInt Q N β‖ ^ (2 * s) ≤
        C ^ (2 * s) * (N : ℝ) ^ (2 * s - Polynomial.natDegree Q) :=
  singInt_bound_of Q hd
    (fun f u v m hu hv hf hp => oscInt_levelSet_le f hu hv hf hp)
    (fun R hR => real_poly_levelSet_volume_le R hR)
    (fun C hC d hdc => min_rpow_integral_bound C hC d hdc)
    (fun C hC d hdc N s hs => integrable_min_rpow C hC d hdc N s hs)

end

end Work.A3
