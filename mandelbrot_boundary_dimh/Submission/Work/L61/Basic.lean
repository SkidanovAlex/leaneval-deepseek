import Mathlib
import Submission.Work.Interfaces.Parabolic

/-!
# Lemma 6.1 (Shishikura §6) — shared definitions

`Submission/Work/L61/Basic.lean` collects the vocabulary for the proof of `L61Statement`
(the paper's Lemma 6.1): the pushed-down horn map `g = pushdown Ẽ_{f₀}`, its domain
`gdom = {0} ∪ π(B^u ∪ B^ℓ)`, its critical value `π v`, and the critical orbit `Kset`
together with `0`.

Nothing here uses `sorry`; the module is a plain definition/API module that the other
L61 lemmas import.
-/

namespace Work.L61

open MandelDim
open Set Function
open scoped Topology

noncomputable section

variable {f₀ : ℂ → ℂ} {D₀ : Set ℂ}

/-- The pushed-down horn map `g = pushdown Ẽ_{f₀}`, as a total function on `ℂ`. -/
def g (d : ParabData f₀ D₀) : ℂ → ℂ := pushdown d.E

/-- The critical value `π v` of `g`. -/
def critVal {d : ParabData f₀ D₀} (hd : HornData d) : ℂ := piExp hd.v

/-- The rescaled pushed-down horn map `ǧ = s g (ζ/s)` with `s = g''(0)/2`, the germ that lies in
the class `𝓕₀` (`HornData.g_F0`). -/
def gres (d : ParabData f₀ D₀) : ℂ → ℂ :=
  fun ζ => (deriv (deriv (g d)) 0 / 2) * g d (ζ / (deriv (deriv (g d)) 0 / 2))

/-- The domain of the pushed-down horn map: `Dom g = {0} ∪ π(B^u ∪ B^ℓ)`. -/
def gdom (d : ParabData f₀ D₀) (hd : HornData d) : Set ℂ :=
  insert 0 (piExp '' (hd.Bu ∪ hd.Bl))

/-- The critical orbit of `g`, together with `0`.  This is the set that every inverse
branch must avoid (its points are the critical values of the iterates of `g`, and `0` is
the omitted value needed for Montel). -/
def Kset (d : ParabData f₀ D₀) (hd : HornData d) : Set ℂ :=
  {0} ∪ Set.range (fun n : ℕ => (g d)^[n] (critVal hd))

/-! ## Elementary facts -/

@[simp] theorem g_zero (d : ParabData f₀ D₀) : g d 0 = 0 := by
  simp [g, pushdown]

theorem g_ne_zero (d : ParabData f₀ D₀) {ζ : ℂ} (h : ζ ≠ 0) : g d ζ ≠ 0 := by
  rw [g, pushdown]
  rw [if_neg h]
  intro hc
  exact Complex.exp_ne_zero _ hc

theorem g_eq_zero_iff (d : ParabData f₀ D₀) (ζ : ℂ) : g d ζ = 0 ↔ ζ = 0 := by
  rcases eq_or_ne ζ 0 with rfl | h
  · simp
  · exact iff_of_false (g_ne_zero d h) h

theorem critVal_mem_piExp {d : ParabData f₀ D₀} (hd : HornData d) :
    critVal hd ∈ piExp '' (hd.Bu ∪ hd.Bl) := by
  have h := hd.crit_orbit.1 0
  simpa [critVal] using h

theorem critVal_mem_gdom (d : ParabData f₀ D₀) (hd : HornData d) :
    critVal hd ∈ gdom d hd :=
  mem_insert_of_mem _ (critVal_mem_piExp hd)

theorem critVal_ne_zero {d : ParabData f₀ D₀} (hd : HornData d) : critVal hd ≠ 0 := by
  rw [critVal]
  intro hc
  exact Complex.exp_ne_zero _ hc

theorem zero_mem_Kset (d : ParabData f₀ D₀) (hd : HornData d) : (0 : ℂ) ∈ Kset d hd :=
  Or.inl rfl

theorem critVal_mem_Kset (d : ParabData f₀ D₀) (hd : HornData d) :
    critVal hd ∈ Kset d hd :=
  Or.inr ⟨0, by simp⟩

theorem Kset_crit_orbit (d : ParabData f₀ D₀) (hd : HornData d) (n : ℕ) :
    (g d)^[n] (critVal hd) ∈ Kset d hd :=
  Or.inr ⟨n, rfl⟩

/-- `Kset` is forward invariant. -/
theorem mapsTo_Kset (d : ParabData f₀ D₀) (hd : HornData d) :
    MapsTo (g d) (Kset d hd) (Kset d hd) := by
  rintro x (rfl | ⟨n, rfl⟩)
  · rw [g_zero]; exact zero_mem_Kset d hd
  · simpa [Function.iterate_succ_apply'] using Kset_crit_orbit d hd (n + 1)

/-- Every point of `Kset` is a point of `gdom`: the critical orbit stays in the domain
(`HornData.crit_orbit`) and `0 ∈ gdom`. -/
theorem Kset_subset_gdom (d : ParabData f₀ D₀) (hd : HornData d) :
    Kset d hd ⊆ gdom d hd := by
  rintro x (rfl | ⟨n, rfl⟩)
  · exact Set.mem_insert_iff.mpr (Or.inl rfl)
  · exact Set.mem_insert_iff.mpr (Or.inr (hd.crit_orbit.1 n))

/-! ## `T`-equivariance of the lifted horn map and the pushdown

These are the basic structural facts about `E = Φ ∘ φ` and `g = pushdown E` that the L61
argument uses.  (They duplicate `Work.Horn`'s cheap layer, kept here so that the L61 modules
depend only on `Interfaces/Parabolic.lean`.)
-/

theorem mem_DE {d : ParabData f₀ D₀} {w : ℂ} :
    w ∈ d.DE ↔ w ∈ d.Dφ ∧ d.φ w ∈ ParabolicBasin f₀ D₀ := Iff.rfl

/-- `E = Φ ∘ φ` is `T`-equivariant on `DE`. -/
theorem E_add_one (d : ParabData f₀ D₀) {w : ℂ} (hw : w ∈ d.DE) (hw1 : w + 1 ∈ d.DE) :
    d.E (w + 1) = d.E w + 1 := by
  rw [mem_DE] at hw hw1
  simp only [ParabData.E]
  rw [d.φ_abel w hw.1 hw1.1, d.Φ_abel (d.φ w) hw.2]

theorem IsTInvariant.add_int {D : Set ℂ} (hD : IsTInvariant D) {w : ℂ} (hw : w ∈ D)
    (k : ℤ) : w + k ∈ D := by
  induction k using Int.induction_on with
  | zero => simpa using hw
  | succ n ih =>
      have hEq : w + (((n : ℤ) + 1 : ℤ) : ℂ) = (w + (n : ℂ)) + 1 := by push_cast; ring
      rw [hEq]
      exact (hD (w + (n : ℂ))).mp ih
  | pred n ih =>
      have hEq : w + (((-(n : ℤ) - 1 : ℤ)) : ℂ) = (w + (-(n : ℂ))) - 1 := by push_cast; ring
      rw [hEq]
      exact (hD ((w + (-(n : ℂ))) - 1)).mpr (by simpa using ih)

/-- `E`-equivariance iterated in the positive direction. -/
theorem E_add_nat {E : ℂ → ℂ} {D : Set ℂ} (hD : IsTInvariant D)
    (hE : ∀ w ∈ D, w + 1 ∈ D → E (w + 1) = E w + 1) {w : ℂ} (hw : w ∈ D) (n : ℕ) :
    E (w + n) = E w + n := by
  induction n with
  | zero => simp
  | succ m ih =>
      have hmem : w + (m : ℂ) ∈ D := by
        simpa using IsTInvariant.add_int hD hw (m : ℤ)
      have hEq : w + ((m + 1 : ℕ) : ℂ) = (w + (m : ℂ)) + 1 := by push_cast; ring
      have hmem1 : (w + (m : ℂ)) + 1 ∈ D := by
        rw [← hEq]
        simpa using IsTInvariant.add_int hD hw (((m + 1 : ℕ)) : ℤ)
      rw [hEq, hE (w + (m : ℂ)) hmem hmem1, ih]
      push_cast; ring

/-- `E`-equivariance iterated in the negative direction. -/
theorem E_sub_nat {E : ℂ → ℂ} {D : Set ℂ} (hD : IsTInvariant D)
    (hE : ∀ w ∈ D, w + 1 ∈ D → E (w + 1) = E w + 1) {w : ℂ} (hw : w ∈ D) (n : ℕ) :
    E (w - n) = E w - n := by
  have hmem : w - (n : ℂ) ∈ D := by
    have h := IsTInvariant.add_int hD hw (-(n : ℤ))
    rw [show w + (((-(n : ℤ)) : ℤ) : ℂ) = w - (n : ℂ) by push_cast; ring] at h
    exact h
  have h1 := E_add_nat hD hE hmem n
  rw [show w - (n : ℂ) + (n : ℂ) = w by ring] at h1
  rw [h1]; ring

/-- `E`-equivariance iterated over the integers. -/
theorem E_add_int {E : ℂ → ℂ} {D : Set ℂ} (hD : IsTInvariant D)
    (hE : ∀ w ∈ D, w + 1 ∈ D → E (w + 1) = E w + 1) {w : ℂ} (hw : w ∈ D) (k : ℤ) :
    E (w + k) = E w + k := by
  rcases k with n | n
  · simpa using E_add_nat hD hE hw n
  · rw [show w + Int.negSucc n = w - ((n + 1 : ℕ) : ℂ) by push_cast [Int.negSucc]; ring]
    rw [E_sub_nat hD hE hw (n + 1)]
    push_cast [Int.negSucc]; ring

theorem piExp_ne_zero (w : ℂ) : piExp w ≠ 0 := Complex.exp_ne_zero _

theorem piExp_add_one (w : ℂ) : piExp (w + 1) = piExp w := by
  rw [piExp, piExp,
    show 2 * ↑Real.pi * Complex.I * (w + 1) =
      2 * ↑Real.pi * Complex.I * w + 2 * ↑Real.pi * Complex.I by ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem piExp_add_natCast (v : ℂ) (n : ℕ) : piExp (v + n) = piExp v := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [show v + ((m + 1 : ℕ) : ℂ) = (v + m) + 1 by push_cast; ring, piExp_add_one, ih]

theorem piExp_sub_natCast (v : ℂ) (n : ℕ) : piExp (v - n) = piExp v := by
  have h := piExp_add_natCast (v - n) n
  rw [show v - (n : ℂ) + n = v by ring] at h
  exact h.symm

theorem piExp_add_intCast (v : ℂ) (k : ℤ) : piExp (v + k) = piExp v := by
  rcases k with n | n
  · exact piExp_add_natCast v n
  · rw [show v + Int.negSucc n = v - ((n + 1 : ℕ) : ℂ) by push_cast [Int.negSucc]; ring]
    exact piExp_sub_natCast v (n + 1)

/-- Two points have the same `π`-image iff they differ by an integer. -/
theorem piExp_eq_iff {u v : ℂ} : piExp u = piExp v ↔ ∃ k : ℤ, u = v + k := by
  constructor
  · intro h
    simp only [piExp] at h
    have h2 : Complex.exp (2 * ↑Real.pi * Complex.I * u - (2 * ↑Real.pi * Complex.I * v)) = 1 := by
      rw [Complex.exp_sub, h, div_self (Complex.exp_ne_zero _)]
    rw [Complex.exp_eq_one_iff] at h2
    obtain ⟨n, hn⟩ := h2
    refine ⟨n, ?_⟩
    have hne : (2 * ↑Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
    have h3 : 2 * ↑Real.pi * Complex.I * (u - v) = 2 * ↑Real.pi * Complex.I * (n : ℂ) := by
      rw [show 2 * ↑Real.pi * Complex.I * u - 2 * ↑Real.pi * Complex.I * v =
        2 * ↑Real.pi * Complex.I * (u - v) by ring] at hn
      rw [hn]; ring
    linear_combination mul_left_cancel₀ hne h3
  · rintro ⟨k, rfl⟩
    exact piExp_add_intCast v k

theorem piExp_log_div (ζ : ℂ) (hζ : ζ ≠ 0) :
    piExp (Complex.log ζ / (2 * Real.pi * Complex.I)) = ζ := by
  rw [piExp,
    show 2 * ↑Real.pi * Complex.I * (Complex.log ζ / (2 * ↑Real.pi * Complex.I)) =
      Complex.log ζ by field_simp,
    Complex.exp_log hζ]

/-- `pushdown` of a `T`-equivariant map is the induced map on the cylinder: `g (π w) = π (E w)`. -/
theorem g_piExp (d : ParabData f₀ D₀) (hd : HornData d) {w : ℂ} (hw : w ∈ hd.Bu ∪ hd.Bl) :
    g d (piExp w) = piExp (d.E w) := by
  have hDd : IsTInvariant (hd.Bu ∪ hd.Bl) := fun v => by
    simp only [Set.mem_union] at *
    rw [hd.Bu_T v, hd.Bl_T v]
  have hE : ∀ v ∈ hd.Bu ∪ hd.Bl, v + 1 ∈ hd.Bu ∪ hd.Bl → d.E (v + 1) = d.E v + 1 :=
    fun v hv hv1 => E_add_one d (hd.sub hv) (hd.sub hv1)
  have hζ : piExp w ≠ 0 := piExp_ne_zero w
  rw [g, pushdown, if_neg hζ]
  obtain ⟨k, hk⟩ : ∃ k : ℤ, Complex.log (piExp w) / (2 * Real.pi * Complex.I) = w + k :=
    piExp_eq_iff.mp (by rw [piExp_log_div (piExp w) hζ])
  rw [hk, E_add_int hDd hE hw k, piExp_add_intCast]

/-- A point of `gdom` other than `0` has a lift in `Bu ∪ Bl`, and `g` is computed there. -/
theorem g_mem_lift (d : ParabData f₀ D₀) (hd : HornData d) {ζ : ℂ} (hζ : ζ ∈ gdom d hd)
    (hζ0 : ζ ≠ 0) : ∃ w ∈ hd.Bu ∪ hd.Bl, piExp w = ζ ∧ g d ζ = piExp (d.E w) := by
  obtain ⟨w, hw, hwζ⟩ : ∃ w ∈ hd.Bu ∪ hd.Bl, piExp w = ζ := by
    rcases hζ with h | h
    · exact absurd h hζ0
    · exact h
  exact ⟨w, hw, hwζ, by rw [← hwζ, g_piExp d hd hw]⟩

end

end Work.L61
