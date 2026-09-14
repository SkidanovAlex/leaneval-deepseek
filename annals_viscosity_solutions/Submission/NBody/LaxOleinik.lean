import Submission.NBody.Dominated
import Submission.NBody.Minimizer
import Mathlib

/-!
# The Lax--Oleinik semigroup

Section 2 of Maderna–Venturelli.  For an extended-valued `u : Eᴺ → ℝ≥0∞` the backward
Lax--Oleinik semigroup is `laxoTau m u t x = ⨅ y, u y + φ(y,x,t)` (`φ` the fixed-time action
potential) and its `h`-version is `laxo m h u x = ⨅ y, u y + φ_h(y,x)`.

Proved here: monotonicity, commutation with constants, the semigroup law
`laxoTau m (laxoTau m u s) t = laxoTau m u (s+t)`, the identity
`laxo m h u x = ⨅ t : {t // 0 < t}, laxoTau m u t x + ofReal h * ofReal t`, and the fact that a
dominated function satisfies `u ≤ T_t u + ht`.

Everything here is fully proved.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-! ## Concatenation and splitting for the fixed-time action potential -/

/-- **Concatenation inequality** for the fixed-time action potential. -/
theorem actionPotTau_le_add_of {m : Fin N → ℝ} {x y z : EN E N} {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) :
    actionPotTau m x z (s + t) ≤ actionPotTau m x y s + actionPotTau m y z t := by
  let P : Type _ := {γ : ℝ → EN E N // γ 0 = x ∧ γ s = y ∧ AbsolutelyContinuousOnInterval γ 0 s}
  let Q : Type _ := {γ : ℝ → EN E N // γ 0 = y ∧ γ t = z ∧ AbsolutelyContinuousOnInterval γ 0 t}
  have hxy : actionPotTau m x y s = ⨅ p : P, actionOn m 0 p.1 0 s := rfl
  have hyz : actionPotTau m y z t = ⨅ q : Q, actionOn m 0 q.1 0 t := rfl
  have key : ∀ (p : P) (q : Q),
      actionPotTau m x z (s + t) ≤ actionOn m 0 p.1 0 s + actionOn m 0 q.1 0 t := by
    intro p q
    have hqac : AbsolutelyContinuousOnInterval (fun u : ℝ => q.1 (u - s)) s (s + t) := by
      have h := Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_comp_affine
        (f := q.1) (a := 0) (b := t) (c := 1) (d := -s) (by norm_num) q.2.2.2
      have h2 : (0 - -s) / 1 = s := by ring
      have h3 : (t - -s) / 1 = s + t := by ring
      rw [h2, h3] at h
      have hfun : (fun t_1 : ℝ => q.1 (1 * t_1 + -s)) = fun u : ℝ => q.1 (u - s) := by
        funext u
        rw [one_mul, sub_eq_add_neg]
      rwa [hfun] at h
    have hfc : p.1 s = (fun u : ℝ => q.1 (u - s)) s := by
      simp only [sub_self, q.2.1, p.2.2.1]
    have hconcat : AbsolutelyContinuousOnInterval
        (fun u : ℝ => if u ≤ s then p.1 u else q.1 (u - s)) 0 (s + t) :=
      Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_concat
        (le_of_lt hs) (by linarith) hfc p.2.2.2 hqac
    have hle := actionPotTau_le_of (m := m) (x := x) (y := z) (τ := s + t)
      (γ := fun u : ℝ => if u ≤ s then p.1 u else q.1 (u - s))
      (by show (if (0 : ℝ) ≤ s then p.1 0 else q.1 (0 - s)) = x
          rw [if_pos (le_of_lt hs)]
          exact p.2.1)
      (by show (if (s + t) ≤ s then p.1 (s + t) else q.1 (s + t - s)) = z
          rw [if_neg (by linarith), show s + t - s = t by ring]
          exact q.2.2.1)
      hconcat
    exact hle.trans (le_of_eq (actionOn_concat hs ht))
  calc actionPotTau m x z (s + t)
      ≤ ⨅ (p : P), ⨅ (q : Q),
          (actionOn m 0 p.1 0 s + actionOn m 0 q.1 0 t) :=
        le_iInf fun p => le_iInf fun q => key p q
    _ = (⨅ (p : P), actionOn m 0 p.1 0 s) + (⨅ (q : Q), actionOn m 0 q.1 0 t) := by
        trans ⨅ (p : P), (actionOn m 0 p.1 0 s + ⨅ (q : Q), actionOn m 0 q.1 0 t)
        · exact iInf_congr fun p => (ENNReal.add_iInf (a := actionOn m 0 p.1 0 s)).symm
        · exact (ENNReal.iInf_add (f := fun p : P => actionOn m 0 p.1 0 s)
            (a := ⨅ q : Q, actionOn m 0 q.1 0 t)).symm
    _ = actionPotTau m x y s + actionPotTau m y z t := by rw [hxy, hyz]

/-- **Splitting inequality** for the fixed-time action potential. -/
theorem iInf_add_actionPotTau_le {m : Fin N → ℝ} {x z : EN E N} {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (⨅ y : EN E N, actionPotTau m x y s + actionPotTau m y z t) ≤ actionPotTau m x z (s + t) := by
  let P : Type _ := {γ : ℝ → EN E N //
    γ 0 = x ∧ γ (s + t) = z ∧ AbsolutelyContinuousOnInterval γ 0 (s + t)}
  have hxz : actionPotTau m x z (s + t) = ⨅ p : P, actionOn m 0 p.1 0 (s + t) := rfl
  rw [hxz]
  refine le_iInf fun p => ?_
  have hsub : AbsolutelyContinuousOnInterval p.1 0 s :=
    p.2.2.2.mono (by
      rw [uIcc_of_le hs, uIcc_of_le (by linarith : (0:ℝ) ≤ s + t)]
      exact Set.Icc_subset_Icc_right (by linarith))
  have h1 : actionPotTau m x (p.1 s) s ≤ actionOn m 0 p.1 0 s :=
    actionPotTau_le_of (m := m) (x := x) (y := p.1 s) (τ := s) (γ := p.1) p.2.1 rfl hsub
  have hshiftac : AbsolutelyContinuousOnInterval (fun u : ℝ => p.1 (u + s)) 0 t := by
    have h := Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_comp_affine
      (f := p.1) (a := 0) (b := s + t) (c := 1) (d := s) (by norm_num) p.2.2.2
    have h2 : (0 - s) / 1 = -s := by ring
    have h3 : (s + t - s) / 1 = t := by ring
    rw [h2, h3] at h
    have hsub : Set.uIcc (0:ℝ) t ⊆ Set.uIcc (-s) t := by
      rw [uIcc_of_le (by linarith : (0:ℝ) ≤ t), uIcc_of_le (by linarith : -s ≤ t)]
      exact Set.Icc_subset_Icc (by linarith) le_rfl
    have h2' := h.mono hsub
    have hfun : (fun t_1 : ℝ => p.1 (1 * t_1 + s)) = fun u : ℝ => p.1 (u + s) := by
      funext u
      rw [one_mul]
    rwa [hfun] at h2'
  have h2 : actionPotTau m (p.1 s) z t ≤ actionOn m 0 p.1 s (s + t) := by
    have h := actionPotTau_le_of (m := m) (x := p.1 s) (y := z) (τ := t)
      (γ := fun u : ℝ => p.1 (u + s)) (by simp)
      (by show p.1 (t + s) = z
          rw [show t + s = s + t from by ring]
          exact p.2.2.1) hshiftac
    rwa [actionOn_comp_add_const (m := m) (h := 0) (γ := p.1) (a := s) (L := t)] at h
  calc (⨅ y : EN E N, actionPotTau m x y s + actionPotTau m y z t)
      ≤ actionPotTau m x (p.1 s) s + actionPotTau m (p.1 s) z t := iInf_le _ _
    _ ≤ actionOn m 0 p.1 0 s + actionOn m 0 p.1 s (s + t) := add_le_add h1 h2
    _ = actionOn m 0 p.1 0 (s + t) := (actionOn_add (m := m) (h := 0) (γ := p.1) hs (by linarith)).symm

/-- **Additivity of the fixed-time action potential over the splitting time.** -/
theorem actionPotTau_eq_iInf_add {m : Fin N → ℝ} {x z : EN E N} {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) :
    actionPotTau m x z (s + t)
      = ⨅ y : EN E N, actionPotTau m x y s + actionPotTau m y z t :=
  le_antisymm (le_iInf fun y => actionPotTau_le_add_of (y := y) hs ht)
    (iInf_add_actionPotTau_le hs.le ht.le)

/-! ## The semigroup -/

/-- The backward Lax--Oleinik semigroup at fixed time, on extended-valued functions. -/
noncomputable def laxoTau (m : Fin N → ℝ) (u : EN E N → ℝ≥0∞) (t : ℝ) (x : EN E N) : ℝ≥0∞ :=
  ⨅ y, u y + actionPotTau m y x t

/-- The Lax--Oleinik semigroup with the energy level `h` built in. -/
noncomputable def laxo (m : Fin N → ℝ) (h : ℝ) (u : EN E N → ℝ≥0∞) (x : EN E N) : ℝ≥0∞ :=
  ⨅ y, u y + actionPot m h y x

lemma laxoTau_mono {m : Fin N → ℝ} {u v : EN E N → ℝ≥0∞} (h : ∀ y, u y ≤ v y)
    (t : ℝ) (x : EN E N) : laxoTau m u t x ≤ laxoTau m v t x :=
  iInf_mono fun y => add_le_add (h y) le_rfl

lemma laxoTau_add_const {m : Fin N → ℝ} (u : EN E N → ℝ≥0∞) (c : ℝ≥0∞) (t : ℝ)
    (x : EN E N) : laxoTau m (fun y => u y + c) t x = laxoTau m u t x + c := by
  unfold laxoTau
  rw [show (⨅ y, (u y + c) + actionPotTau m y x t)
      = ⨅ y, (u y + actionPotTau m y x t) + c from
    iInf_congr fun y => by rw [add_assoc, add_comm c, add_assoc]]
  exact ENNReal.iInf_add.symm

/-- **The semigroup law.** -/
theorem laxoTau_semigroup {m : Fin N → ℝ} {u : EN E N → ℝ≥0∞} {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (x : EN E N) :
    laxoTau m (laxoTau m u s) t x = laxoTau m u (s + t) x := by
  have hL : laxoTau m (laxoTau m u s) t x
      = ⨅ z : EN E N, ⨅ y : EN E N,
          ((u z + actionPotTau m z y s) + actionPotTau m y x t) := by
    unfold laxoTau
    rw [iInf_comm]
    exact iInf_congr fun y => ENNReal.iInf_add
  have hR : laxoTau m u (s + t) x
      = ⨅ z : EN E N, ⨅ y : EN E N,
          ((u z + actionPotTau m z y s) + actionPotTau m y x t) := by
    unfold laxoTau
    refine iInf_congr fun z => ?_
    rw [actionPotTau_eq_iInf_add hs ht, ENNReal.add_iInf]
    exact iInf_congr fun y => by rw [add_assoc]
  rw [hL, hR]

/-- **`laxo` is the infimum over all times of `laxoTau` plus `ht`.** -/
theorem laxo_eq_iInf_laxoTau {m : Fin N → ℝ} {h : ℝ} (hm : ∀ i, 0 ≤ m i) (hh : 0 ≤ h)
    (u : EN E N → ℝ≥0∞) (x : EN E N) :
    laxo m h u x = ⨅ t : {t : ℝ // 0 < t},
      laxoTau m u t.1 x + ENNReal.ofReal h * ENNReal.ofReal t.1 := by
  have hL : laxo m h u x = ⨅ y : EN E N, ⨅ t : {t : ℝ // 0 < t},
      (u y + (actionPotTau m y x t.1 + ENNReal.ofReal h * ENNReal.ofReal t.1)) := by
    unfold laxo
    refine iInf_congr fun y => ?_
    rw [actionPot_eq_iInf_actionPotTau hm hh, ENNReal.add_iInf]
  have hR : (⨅ t : {t : ℝ // 0 < t}, laxoTau m u t.1 x + ENNReal.ofReal h * ENNReal.ofReal t.1)
      = ⨅ t : {t : ℝ // 0 < t}, ⨅ y : EN E N,
          (u y + (actionPotTau m y x t.1 + ENNReal.ofReal h * ENNReal.ofReal t.1)) := by
    refine iInf_congr fun t => ?_
    unfold laxoTau
    rw [ENNReal.iInf_add]
    simp only [add_assoc]
  rw [hL, hR, iInf_comm]

/-- **A dominated function satisfies `u ≤ T_t u + ht`.** -/
theorem Dominated.ofReal_le_laxoTau {m : Fin N → ℝ} {h : ℝ} (hm : ∀ i, 0 ≤ m i) (hh : 0 ≤ h)
    {u : EN E N → ℝ} (hu : Dominated m h u) {t : ℝ} (ht : 0 < t) (x : EN E N) :
    ENNReal.ofReal (u x) ≤ laxoTau m (fun y => ENNReal.ofReal (u y)) t x
      + ENNReal.ofReal h * ENNReal.ofReal t := by
  rw [laxoTau, ENNReal.iInf_add]
  refine le_iInf fun y => ?_
  have hdom : ENNReal.ofReal (u x - u y) ≤ actionPot m h y x := hu y x
  have h2 : ENNReal.ofReal (u x - u y)
      ≤ actionPotTau m y x t + ENNReal.ofReal h * ENNReal.ofReal t := by
    rw [actionPot_eq_iInf_actionPotTau hm hh y x] at hdom
    exact hdom.trans (iInf_le (f := fun t' : {t' : ℝ // 0 < t'} =>
      actionPotTau m y x t'.1 + ENNReal.ofReal h * ENNReal.ofReal t'.1) ⟨t, ht⟩)
  calc ENNReal.ofReal (u x)
      ≤ ENNReal.ofReal (u x - u y) + ENNReal.ofReal (u y) := by
        simpa only [sub_add_cancel] using (ENNReal.ofReal_add_le (p := u x - u y) (q := u y))
    _ ≤ (actionPotTau m y x t + ENNReal.ofReal h * ENNReal.ofReal t) + ENNReal.ofReal (u y) :=
        add_le_add h2 le_rfl
    _ = (ENNReal.ofReal (u y) + actionPotTau m y x t) + ENNReal.ofReal h * ENNReal.ofReal t := by
        rw [add_assoc, add_comm (ENNReal.ofReal h * ENNReal.ofReal t) (ENNReal.ofReal (u y)),
          ← add_assoc, add_comm (actionPotTau m y x t) (ENNReal.ofReal (u y))]

end Submission.NBody
