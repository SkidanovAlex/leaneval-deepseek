/-
# Parameter rays of the mandelbar: escape radius and symmetry

This file sets up the basic dynamical objects for the antiholomorphic unicritical
family `T_c(z) = (conj z)^2 + c` used in Hubbard--Schleicher's proof that the
mandelbar (tricorn) is not path connected, and proves the elementary "escape
radius" facts on which the whole parameter-ray theory rests.

## Main definitions

* `Work.ParamRays.orbit c z n` : the `n`-th iterate `T_c^[n] z`.
* `Work.ParamRays.critOrbit c n` : the critical orbit `T_c^[n] 0`.
* `Work.ParamRays.BoundedOrbit c z` : the orbit of `z` is bounded.
* `Work.ParamRays.Escaping c z` : the orbit of `z` tends to infinity.
* `Work.ParamRays.filledJulia c` : the filled Julia set of `T_c`.
* `Work.ParamRays.escapeRadius` : the escape radius `2`.
* `Work.ParamRays.omega` : the rotation `exp (2 pi i / 3)`.

## Main results

* `Work.ParamRays.not_bounded_of_lt_norm` : `max 2 ‖c‖ < ‖z‖` implies that the
  orbit of `z` is unbounded (the escape criterion).
* `Work.ParamRays.mem_mandelbar_iff` : `c` is in the mandelbar iff the critical
  orbit stays in the closed disk of radius `2`.
* `Work.ParamRays.isCompact_mandelbar` : the mandelbar is compact.
* `Work.ParamRays.mandelbar_smul_omega`, `Work.ParamRays.mandelbar_conj` : the
  rotational and reflectional symmetries of the mandelbar.
-/
import ChallengeDeps

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Function
open scoped ComplexConjugate

namespace Work.ParamRays

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## The orbit and the escape criterion -/

/-- The `n`-th iterate of `z` under the antipolynomial `T_c(z) = (conj z)^2 + c`. -/
def orbit (c z : ℂ) (n : ℕ) : ℂ := (Tantibar c)^[n] z

/-- The critical orbit of `T_c`, starting at the critical point `0`. -/
def critOrbit (c : ℂ) (n : ℕ) : ℂ := orbit c 0 n

/-- The orbit of `z` under `T_c` is bounded. -/
def BoundedOrbit (c z : ℂ) : Prop := ∃ M : ℝ, ∀ n : ℕ, ‖orbit c z n‖ ≤ M

/-- The orbit of `z` under `T_c` escapes to infinity. -/
def Escaping (c z : ℂ) : Prop :=
  Filter.Tendsto (fun n : ℕ => ‖orbit c z n‖) Filter.atTop Filter.atTop

/-- The filled Julia set of `T_c`: the points whose orbit stays bounded. -/
def filledJulia (c : ℂ) : Set ℂ := {z | BoundedOrbit c z}

/-- The escape radius of the unicritical family `z ↦ z̄² + c`. -/
def escapeRadius : ℝ := 2

@[simp] theorem orbit_zero (c z : ℂ) : orbit c z 0 = z := rfl

@[simp] theorem critOrbit_zero (c : ℂ) : critOrbit c 0 = 0 := rfl

theorem orbit_succ (c z : ℂ) (n : ℕ) :
    orbit c z (n + 1) = Tantibar c (orbit c z n) := by
  simp [orbit, Function.iterate_succ_apply']

@[simp] theorem critOrbit_one (c : ℂ) : critOrbit c 1 = c := by
  simp [critOrbit, orbit, Tantibar]

theorem orbit_add (c z : ℂ) (m n : ℕ) :
    orbit c z (m + n) = orbit c (orbit c z m) n := by
  simp only [orbit]
  rw [Nat.add_comm m n, Function.iterate_add_apply]

theorem orbit_one_add (c z : ℂ) (n : ℕ) :
    orbit c z (n + 1) = orbit c (Tantibar c z) n := by
  simp only [orbit]
  exact Function.iterate_succ_apply (Tantibar c) n z

/-- The second iterate of `T_c` is the holomorphic quartic polynomial
`z ↦ (z^2 + conj c)^2 + c`. -/
theorem orbit_two_eq (c z : ℂ) :
    Tantibar c (Tantibar c z) = (z ^ 2 + conj c) ^ 2 + c := by
  simp only [Tantibar]
  rw [map_add, map_pow, Complex.conj_conj]

theorem critOrbit_two (c : ℂ) : critOrbit c 2 = conj c ^ 2 + c := by
  have h : critOrbit c 2 = Tantibar c (Tantibar c 0) := by
    simp only [critOrbit, orbit, show (2:ℕ) = 1 + 1 from rfl,
      Function.iterate_succ_apply', Function.iterate_zero, id_eq]
  rw [h, Tantibar, Tantibar, map_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0), zero_add]

theorem critOrbit_three (c : ℂ) : critOrbit c 3 = (c ^ 2 + conj c) ^ 2 + c := by
  have h : critOrbit c 3 = Tantibar c (Tantibar c (Tantibar c 0)) := by
    simp only [critOrbit, orbit, show (3:ℕ) = 2 + 1 from rfl,
      show (2:ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply', Function.iterate_zero, id_eq]
  rw [h, Tantibar, Tantibar, Tantibar, map_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0),
    zero_add, map_add, map_pow, Complex.conj_conj]

/-! ## The escape criterion -/

/-- Reverse triangle inequality for `T_c`: `‖w‖ ^ 2 - ‖c‖ ≤ ‖T_c w‖`. -/
theorem norm_sq_sub_le_norm_Tantibar (c w : ℂ) :
    ‖w‖ ^ 2 - ‖c‖ ≤ ‖Tantibar c w‖ := by
  have h : ‖(starRingEnd ℂ w) ^ 2‖ ≤ ‖Tantibar c w‖ + ‖c‖ := by
    calc ‖(starRingEnd ℂ w) ^ 2‖
        = ‖((starRingEnd ℂ w) ^ 2 + c) - c‖ := by ring_nf
      _ ≤ ‖(starRingEnd ℂ w) ^ 2 + c‖ + ‖c‖ := norm_sub_le _ _
      _ = ‖Tantibar c w‖ + ‖c‖ := rfl
  rw [norm_pow, Complex.norm_conj] at h
  linarith

theorem norm_Tantibar_le (c w : ℂ) : ‖Tantibar c w‖ ≤ ‖w‖ ^ 2 + ‖c‖ := by
  calc ‖Tantibar c w‖ = ‖(starRingEnd ℂ w) ^ 2 + c‖ := rfl
    _ ≤ ‖(starRingEnd ℂ w) ^ 2‖ + ‖c‖ := norm_add_le _ _
    _ = ‖w‖ ^ 2 + ‖c‖ := by rw [norm_pow, Complex.norm_conj]

/-- The escape estimate: if `‖z‖ > max 2 ‖c‖` then `‖T_c^[n] z‖` grows at least
linearly, with slope `‖z‖ * (‖z‖ - 2)`. -/
theorem norm_orbit_ge_add (c z : ℂ) (h : max 2 ‖c‖ < ‖z‖) :
    ∀ n : ℕ, ‖z‖ + n * (‖z‖ * (‖z‖ - 2)) ≤ ‖orbit c z n‖ := by
  have hz : 2 < ‖z‖ := lt_of_le_of_lt (le_max_left 2 ‖c‖) h
  have hc : ‖c‖ ≤ ‖z‖ := le_of_lt (lt_of_le_of_lt (le_max_right 2 ‖c‖) h)
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hw : ‖z‖ ≤ ‖orbit c z n‖ := by
      have : 0 ≤ (n : ℝ) * (‖z‖ * (‖z‖ - 2)) := by positivity
      linarith
    have hmono : ‖orbit c z n‖ * (‖orbit c z n‖ - 2) ≥ ‖z‖ * (‖z‖ - 2) := by
      have h1 : 1 ≤ ‖z‖ := by linarith
      nlinarith [hw, h1]
    have hcn : ‖c‖ ≤ ‖orbit c z n‖ := le_trans hc hw
    calc ‖z‖ + (↑(n + 1)) * (‖z‖ * (‖z‖ - 2))
        = (‖z‖ + ↑n * (‖z‖ * (‖z‖ - 2))) + ‖z‖ * (‖z‖ - 2) := by push_cast; ring
      _ ≤ ‖orbit c z n‖ + ‖z‖ * (‖z‖ - 2) := by linarith
      _ ≤ ‖orbit c z n‖ + ‖orbit c z n‖ * (‖orbit c z n‖ - 2) := by linarith
      _ = ‖orbit c z n‖ ^ 2 - ‖orbit c z n‖ := by ring
      _ ≤ ‖orbit c z n‖ ^ 2 - ‖c‖ := by linarith
      _ ≤ ‖Tantibar c (orbit c z n)‖ := norm_sq_sub_le_norm_Tantibar c _
      _ = ‖orbit c z (n + 1)‖ := by rw [orbit_succ]

/-- **Escape criterion.** If `max 2 ‖c‖ < ‖z‖` then the orbit of `z` escapes. -/
theorem escaping_of_lt_norm (c z : ℂ) (h : max 2 ‖c‖ < ‖z‖) : Escaping c z := by
  have hz : 2 < ‖z‖ := lt_of_le_of_lt (le_max_left 2 ‖c‖) h
  have hd : 0 < ‖z‖ * (‖z‖ - 2) := by nlinarith
  simp only [Escaping]
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨Nat.ceil (max 0 (b - ‖z‖) / (‖z‖ * (‖z‖ - 2))), fun n hn => ?_⟩
  have h1 := norm_orbit_ge_add c z h n
  have h2 : max 0 (b - ‖z‖) ≤ (n : ℝ) * (‖z‖ * (‖z‖ - 2)) := by
    have hn' : ((Nat.ceil (max 0 (b - ‖z‖) / (‖z‖ * (‖z‖ - 2))) : ℕ) : ℝ) ≤ n := by
      exact_mod_cast hn
    have h3 : max 0 (b - ‖z‖) / (‖z‖ * (‖z‖ - 2)) ≤
        (Nat.ceil (max 0 (b - ‖z‖) / (‖z‖ * (‖z‖ - 2))) : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ hd] at h3
    nlinarith
  linarith [le_max_right 0 (b - ‖z‖)]

theorem not_bounded_of_lt_norm (c z : ℂ) (h : max 2 ‖c‖ < ‖z‖) : ¬ BoundedOrbit c z := by
  rintro ⟨M, hM⟩
  have hev := escaping_of_lt_norm c z h
  simp only [Escaping] at hev
  rw [Filter.tendsto_atTop_atTop] at hev
  obtain ⟨i, hi⟩ := hev (M + 1)
  have h1 := hi i le_rfl
  have h2 := hM i
  linarith

theorem BoundedOrbit.shift {c z : ℂ} (h : BoundedOrbit c z) (n : ℕ) :
    BoundedOrbit c (orbit c z n) := by
  obtain ⟨M, hM⟩ := h
  exact ⟨M, fun m => by rw [← orbit_add]; exact hM (n + m)⟩

theorem norm_le_max_of_bounded (c z : ℂ) (h : BoundedOrbit c z) :
    ‖z‖ ≤ max 2 ‖c‖ := by
  by_contra hcon
  exact not_bounded_of_lt_norm c z (lt_of_not_ge hcon) h

/-! ## The mandelbar -/

theorem mem_mandelbar_iff_bounded (c : ℂ) :
    c ∈ Mandelbar ↔ BoundedOrbit c 0 := Iff.rfl

/-- The norm of the second critical value is at least `‖c‖ ^ 2 - ‖c‖`. -/
theorem norm_sq_sub_le_norm_critOrbit_two (c : ℂ) :
    ‖c‖ ^ 2 - ‖c‖ ≤ ‖critOrbit c 2‖ := by
  rw [critOrbit_two]
  simpa only [Tantibar] using norm_sq_sub_le_norm_Tantibar c c

/-- **Escape radius.** A parameter lies in the mandelbar iff its critical orbit
stays in the closed disk of radius `2`. -/
theorem mem_mandelbar_iff (c : ℂ) :
    c ∈ Mandelbar ↔ ∀ n : ℕ, ‖critOrbit c n‖ ≤ 2 := by
  refine ⟨fun hb n => ?_, fun h => ⟨2, h⟩⟩
  by_contra hcon
  have hn : 2 < ‖critOrbit c n‖ := lt_of_not_ge hcon
  have hb' : BoundedOrbit c 0 := hb
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    simp only [critOrbit_zero, norm_zero] at hn
    exact absurd hn (by norm_num)
  · by_cases hc : ‖c‖ ≤ ‖critOrbit c n‖
    · have hge : max 2 ‖c‖ < ‖critOrbit c (n + 1)‖ := by
        have h2 := norm_sq_sub_le_norm_Tantibar c (critOrbit c n)
        have hmax : max 2 ‖c‖ ≤ ‖critOrbit c n‖ := max_le (le_of_lt hn) hc
        have h3 : ‖critOrbit c n‖ < ‖critOrbit c n‖ ^ 2 - ‖c‖ := by nlinarith
        calc max 2 ‖c‖ ≤ ‖critOrbit c n‖ := hmax
          _ < ‖critOrbit c n‖ ^ 2 - ‖c‖ := h3
          _ ≤ ‖Tantibar c (critOrbit c n)‖ := h2
          _ = ‖critOrbit c (n + 1)‖ := by simp only [critOrbit]; rw [orbit_succ]
      exact not_bounded_of_lt_norm c _ hge (hb'.shift (n + 1))
    · have hclt : ‖critOrbit c n‖ < ‖c‖ := lt_of_not_ge hc
      have hc2 : 2 < ‖c‖ := lt_trans hn hclt
      have hge : max 2 ‖c‖ < ‖critOrbit c 2‖ := by
        rw [max_eq_right (le_of_lt hc2)]
        have h2 := norm_sq_sub_le_norm_critOrbit_two c
        nlinarith
      exact not_bounded_of_lt_norm c _ hge (hb'.shift 2)

theorem mandelbar_subset_closedBall : Mandelbar ⊆ Metric.closedBall 0 2 := by
  intro c hc
  rw [Metric.mem_closedBall, dist_zero_right]
  simpa using (mem_mandelbar_iff c).mp hc 1

theorem isBounded_mandelbar : Bornology.IsBounded Mandelbar :=
  Metric.isBounded_closedBall.subset mandelbar_subset_closedBall

theorem continuous_critOrbit (n : ℕ) : Continuous fun c : ℂ => critOrbit c n := by
  induction n with
  | zero => simpa using continuous_const
  | succ n ih =>
    have h : (fun c : ℂ => critOrbit c (n + 1)) =
        fun c : ℂ => (starRingEnd ℂ) (critOrbit c n) ^ 2 + c := by
      funext c
      rw [show critOrbit c (n + 1) = Tantibar c (critOrbit c n) from orbit_succ c 0 n]
      rfl
    rw [h]
    exact (((Complex.continuous_conj.comp ih).pow 2)).add continuous_id

theorem isClosed_mandelbar : IsClosed Mandelbar := by
  have h : Mandelbar = ⋂ n : ℕ, {c : ℂ | ‖critOrbit c n‖ ≤ 2} := by
    ext c
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact mem_mandelbar_iff c
  rw [h]
  exact isClosed_iInter fun n => isClosed_le (continuous_critOrbit n).norm continuous_const

theorem isCompact_mandelbar : IsCompact Mandelbar :=
  Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_mandelbar, isBounded_mandelbar⟩

theorem zero_mem_mandelbar : (0 : ℂ) ∈ Mandelbar := by
  rw [mem_mandelbar_iff]
  intro n
  have h : critOrbit 0 n = 0 := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [show critOrbit 0 (n + 1) = Tantibar 0 (critOrbit 0 n) from orbit_succ 0 0 n, ih]
      simp [Tantibar]
  rw [h]
  norm_num

theorem mandelbar_nonempty : Mandelbar.Nonempty := ⟨0, zero_mem_mandelbar⟩

/-! ## Symmetries -/

/-- The rotation by `2π/3` acting on parameter space. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

theorem omega_ne_zero : omega ≠ 0 := by
  rw [omega]
  exact Complex.exp_ne_zero _

theorem omega_cube : omega ^ 3 = 1 := by
  rw [omega, ← Complex.exp_nat_mul]
  have h : ((3 : ℕ) : ℂ) * (2 * ↑Real.pi * Complex.I / 3) = 2 * ↑Real.pi * Complex.I := by
    push_cast; ring
  rw [h, Complex.exp_two_pi_mul_I]

theorem norm_omega : ‖omega‖ = 1 := by
  rw [omega, Complex.norm_exp]
  norm_num

theorem omega_sq_eq_conj : omega ^ 2 = conj omega := by
  have hmul : omega * omega ^ 2 = 1 := by rw [← pow_succ', omega_cube]
  rw [← inv_eq_of_mul_eq_one_right hmul, Complex.inv_eq_conj norm_omega]

/-- `T_c` is equivariant under the rotation `z ↦ ω z`: the rotation conjugates
`T_c` to `T_{ω c}`. -/
theorem Tantibar_omega (c z : ℂ) :
    Tantibar (omega * c) (omega * z) = omega * Tantibar c z := by
  have hω : conj omega ^ 2 = omega := by
    rw [pow_two, ← map_mul, ← pow_two, omega_sq_eq_conj, Complex.conj_conj]
  simp only [Tantibar]
  rw [map_mul, mul_pow, hω]
  ring

theorem orbit_omega (c z : ℂ) (n : ℕ) :
    orbit (omega * c) (omega * z) n = omega * orbit c z n := by
  induction n with
  | zero => simp
  | succ n ih => rw [orbit_succ, orbit_succ, ih, Tantibar_omega]

theorem critOrbit_omega (c : ℂ) (n : ℕ) :
    critOrbit (omega * c) n = omega * critOrbit c n := by
  simp only [critOrbit]
  rw [← orbit_omega c 0 n, mul_zero]

theorem mandelbar_smul_omega {c : ℂ} (hc : c ∈ Mandelbar) : omega * c ∈ Mandelbar := by
  rw [mem_mandelbar_iff] at hc ⊢
  intro n
  rw [critOrbit_omega, norm_mul, norm_omega, one_mul]
  exact hc n

/-- `T_c` is conjugate to `T_{conj c}` under complex conjugation. -/
theorem Tantibar_conj (c z : ℂ) :
    Tantibar (conj c) (conj z) = conj (Tantibar c z) := by
  simp only [Tantibar, map_add, map_pow, Complex.conj_conj]

theorem orbit_conj (c z : ℂ) (n : ℕ) :
    orbit (conj c) (conj z) n = conj (orbit c z n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [orbit_succ, orbit_succ, ih, Tantibar_conj]

theorem critOrbit_conj (c : ℂ) (n : ℕ) :
    critOrbit (conj c) n = conj (critOrbit c n) := by
  simp only [critOrbit]
  rw [← orbit_conj c 0 n, map_zero]

theorem mandelbar_conj {c : ℂ} (hc : c ∈ Mandelbar) : conj c ∈ Mandelbar := by
  rw [mem_mandelbar_iff] at hc ⊢
  intro n
  rw [critOrbit_conj, Complex.norm_conj]
  exact hc n

end Work.ParamRays
