import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.aligned_defs
import Submission.Work.BW.exists_primitive_kernel
import Submission.Work.BW.F_bound_of_waldschmidt
import Submission.Work.BW.F_bound_of_waldschmidt_sharp
import Submission.Work.BW.F_bound_of_waldschmidt_sub_fixed
import Submission.Work.BW.relation_lattice_generating_pair
import Submission.Work.BW.aligned_basis_of_short_element
import Submission.Work.BW.exists_relation_span
import Submission.Work.BW.thetaC_exists_relation
import Submission.Work.BW.waldschmidt_relation_bound
import Submission.Work.BW.exists_short_second_element_fixed

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The aligned basis of the torsion-relation lattice (BW §6, ranks one and two)

Let `K` be a number field, `φ : K →+* ℂ`, `α : Fin m → K` with all `α i ≠ 0`, and
`ℓ : Fin m → ℂ` a family of logarithms, `Complex.exp (ℓ i) = φ (α i)`.  Assume the `ℓ i` are
`ℚ`-linearly dependent but every `m - 1` of them are independent, and put

`Γ = {y : Fin m → ℤ | IsOfFinOrder (∏ i, α i ^ (y i))}`  (`= Work.BW.GammaSub α hα`),

the *torsion-relation lattice*, of `ℤ`-rank at most two, together with the weighted `ℓ¹`-length
`F y = ∑ i, |y i| · (d · h′(αᵢ, ℓᵢ))` (`= Work.BW.wn`).

The theorem below produces two generators `e 0`, `e 1` of `Γ` which are *aligned*
(`θ (e 0) + θ (e 1) = 0`, i.e. `e 0 + e 1 ∈ ker θ = {y | ∑ yᵢℓᵢ = 0}`) whenever `e 1 ≠ 0`, and
*small*: the weighted `ℓ¹`-lengths are bounded by `(9 m d³)^m · ∏ i, h′(αᵢ, ℓᵢ)`.

## Proof architecture

Write `d = [K : ℚ]`, `θ y = ∑ i, (y i : ℂ) * ℓ i`, `F y = ∑ i, |y i| · d · h′(αᵢ, ℓᵢ)` and
`T = (9 m d³)^m ∏ i, h′(αᵢ, ℓᵢ)`.

* `Work.BW.waldschmidt_relation_bound` (Waldschmidt, Acta Arith. 37 (1980), Lemma 4.1, as quoted
  in BW §6; the per-coordinate form with the Mignotte refinement) supplies a nonzero kernel
  relation `t` with `|t k| ≤ (9 (m-1) d³)^{m-1} ∏_{j ≠ k} h′(αⱼ, ℓⱼ)`.
* `Work.BW.exists_primitive_kernel` divides `t` by its content, giving a *primitive* kernel
  element `r` with `F r ≤ F t`; `Work.BW.F_bound_of_waldschmidt_sharp_explicit` turns the
  coordinatewise bound on `t` into `F t ≤ T / (9 d²)`, so `F r ≤ T / (9 d²) ≤ T / 2`.  Since
  `ker θ = ℤ r` (`exists_int_smul_of_rat_prop` below, from the `ℚ`-generator of the relation
  space `Work.BW.exists_relation_span` plus primitivity), `r` is the kernel direction of `Γ`.
* If additionally some `y ∈ Γ` has `θ y ≠ 0` (rank two), then
  `Work.BW.exists_short_second_element_fixed` produces `u ∈ Γ` with `θ u ≠ 0` and
  `F u + F r ≤ T / 2`, and the lattice reduction `Work.BW.aligned_basis_of_short_element`
  turns the pair `(r, u)` into an *aligned* generating pair with `F e 0 + F e 1 ≤ T`.
* If `θ` vanishes on `Γ` (rank one), then `Γ = ℤ r` and `e 0 = r`, `e 1 = 0` works, the length
  bound being `F r ≤ T` by the arithmetic lemma `div_nine_sq_le_self`.

Finally `aligned_lattice_form_implies` converts the lattice-theoretic form (with `GammaSub` and
`wn`) into the exact statement of the theorem.

Beware of one formalisation trap: in Lean a trailing `* ∏ i, f i / c` parses as `* ∏ i, (f i / c)`.
The statements above carry explicit parentheses around such products.
-/

namespace Work.BW
open Complex

variable {K : Type*} [Field K] [NumberField K]

lemma mem_GammaSub_of_thetaC_eq_zero {m : ℕ} (φ : K →+* ℂ) (α : Fin m → K)
    (hα : ∀ i, α i ≠ 0) (ℓ : Fin m → ℂ) (hℓ : ∀ i, Complex.exp (ℓ i) = φ (α i))
    {y : Fin m → ℤ} (hy : thetaC ℓ y = 0) : y ∈ GammaSub α hα := by
  rw [mem_GammaSub, MuRelC]
  have h := exp_thetaC φ α ℓ hℓ y
  rw [hy, Complex.exp_zero] at h
  have h1 : (∏ i, α i ^ (y i : ℤ)) = 1 := φ.injective (by rw [← h, map_one])
  rw [h1]
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨1, one_pos, one_pow 1⟩

lemma coords_ne_zero_of_ker {m : ℕ} {ℓ : Fin m → ℂ}
    (hmin : ∀ i, LinearIndependent ℚ (fun j : {j : Fin m // j ≠ i} => ℓ j))
    {r : Fin m → ℤ} (hr : thetaC ℓ r = 0) (hr0 : r ≠ 0) : ∀ i, r i ≠ 0 := by
  intro i hi
  apply hr0
  funext j
  have hsum0 : ∑ x : {x : Fin m // x ≠ i}, (r x : ℚ) • ℓ x = 0 := by
    have h1 : ∀ x : {x : Fin m // x ≠ i}, (r x : ℚ) • ℓ x = (r x : ℂ) * ℓ x := by
      intro x
      have h : (r x : ℚ) • ℓ x = ((r x : ℚ) : ℂ) * ℓ x := Algebra.smul_def _ _
      simpa only [Rat.cast_intCast] using h
    have h2 : ∑ x : {x : Fin m // x ≠ i}, (r x : ℂ) * ℓ x
        = ∑ x ∈ Finset.univ.erase i, (r x : ℂ) * ℓ x :=
      (Finset.sum_subtype (Finset.univ.erase i) (p := fun x => x ≠ i)
        (fun x => by simp [Finset.mem_erase]) (fun x => (r x : ℂ) * ℓ x)).symm
    have h3 : ∑ x ∈ Finset.univ.erase i, (r x : ℂ) * ℓ x = thetaC ℓ r := by
      rw [thetaC, Finset.sum_erase Finset.univ (f := fun x => (r x : ℂ) * ℓ x) (a := i)
        (by simp [hi])]
    calc ∑ x : {x : Fin m // x ≠ i}, (r x : ℚ) • ℓ x
        = ∑ x : {x : Fin m // x ≠ i}, (r x : ℂ) * ℓ x := Finset.sum_congr rfl (fun x _ => h1 x)
      _ = ∑ x ∈ Finset.univ.erase i, (r x : ℂ) * ℓ x := h2
      _ = thetaC ℓ r := h3
      _ = 0 := hr
  have hall := Fintype.linearIndependent_iff.mp (hmin i) (fun x => (r x : ℚ)) hsum0
  by_cases hj : j = i
  · subst hj; exact hi
  · have := hall ⟨j, hj⟩
    simpa using this

lemma exists_int_smul_of_rat_prop {m : ℕ} {ℓ : Fin m → ℂ} {r y : Fin m → ℤ}
    (hr : thetaC ℓ r = 0) (hy : thetaC ℓ y = 0) (hr0 : r ≠ 0)
    (hprim : ∀ (k : ℤ) (z : Fin m → ℤ), thetaC ℓ z = 0 → 2 ≤ |k| → k • z ≠ r)
    (hprop : ∃ c : ℚ, ∀ i, (y i : ℚ) = c * (r i : ℚ)) :
    ∃ a : ℤ, y = a • r := by
  obtain ⟨c, hc⟩ := hprop
  have hex : ∃ i, r i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hr0 (funext h)
  obtain ⟨i₀, hi₀⟩ := hex
  have hcross : ∀ i, r i₀ * y i = y i₀ * r i := by
    intro i
    have h1 := hc i
    have h2 := hc i₀
    have h3 : (y i : ℚ) * (r i₀ : ℚ) = (y i₀ : ℚ) * (r i : ℚ) := by
      rw [h1, h2]; ring
    have h4 : ((r i₀ : ℤ) : ℚ) * ((y i : ℤ) : ℚ) = ((y i₀ : ℤ) : ℚ) * ((r i : ℤ) : ℚ) := by
      rw [mul_comm ((r i₀ : ℤ) : ℚ) ((y i : ℤ) : ℚ)]
      exact h3
    exact_mod_cast h4
  by_cases hB0 : y i₀ = 0
  · refine ⟨0, ?_⟩
    funext i
    have h := hcross i
    rw [hB0, zero_mul] at h
    have : y i = 0 := by
      rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hi₀
      · exact h'
    simp [this]
  · have hpos : 0 < (r i₀).gcd (y i₀) := Int.gcd_pos_of_ne_zero_left (y i₀) hi₀
    have hgne : ((r i₀).gcd (y i₀) : ℤ) ≠ 0 := by exact_mod_cast hpos.ne'
    set s : ℤ := (r i₀).gcdA (y i₀) with hs
    set t : ℤ := (r i₀).gcdB (y i₀) with ht
    set A' : ℤ := r i₀ / ((r i₀).gcd (y i₀) : ℤ) with hA'
    set B' : ℤ := y i₀ / ((r i₀).gcd (y i₀) : ℤ) with hB'
    have hbez' : ((r i₀).gcd (y i₀) : ℤ) = r i₀ * s + y i₀ * t := by
      rw [hs, ht]; exact Int.gcd_eq_gcd_ab _ _
    have hApp' : ((r i₀).gcd (y i₀) : ℤ) * A' = r i₀ := by
      rw [hA']; exact Int.mul_ediv_cancel' (Int.gcd_dvd_left _ _)
    have hBpp' : ((r i₀).gcd (y i₀) : ℤ) * B' = y i₀ := by
      rw [hB']; exact Int.mul_ediv_cancel' (Int.gcd_dvd_right _ _)
    have hcanc : A' * s + B' * t = 1 := by
      refine mul_left_cancel₀ hgne ?_
      calc ((r i₀).gcd (y i₀) : ℤ) * (A' * s + B' * t)
          = ((r i₀).gcd (y i₀) : ℤ) * A' * s + ((r i₀).gcd (y i₀) : ℤ) * B' * t := by ring
        _ = r i₀ * s + y i₀ * t := by rw [hApp', hBpp']
        _ = ((r i₀).gcd (y i₀) : ℤ) * 1 := by rw [← hbez']; ring
    have hAy : A' • y = B' • r := by
      have h1 : ((r i₀).gcd (y i₀) : ℤ) • (A' • y) = ((r i₀).gcd (y i₀) : ℤ) • (B' • r) := by
        rw [smul_smul, smul_smul, hApp', hBpp']
        exact funext fun i => by simpa [Pi.smul_apply, smul_eq_mul] using hcross i
      exact smul_right_injective (Fin m → ℤ) hgne h1
    set z : Fin m → ℤ := s • r + t • y with hz
    have hzθ : thetaC ℓ z = 0 := by
      rw [hz, thetaC_add, thetaC_smul, thetaC_smul, hr, hy, mul_zero, mul_zero, add_zero]
    have hyz : y = B' • z := by
      funext i
      have hAyi : A' * y i = B' * r i := by
        have := congrFun hAy i
        simpa [Pi.smul_apply, smul_eq_mul] using this
      have hkey : B' * (s * r i + t * y i) = y i := by
        calc B' * (s * r i + t * y i) = s * (B' * r i) + (B' * t) * y i := by ring
          _ = s * (A' * y i) + (B' * t) * y i := by rw [← hAyi]
          _ = (A' * s + B' * t) * y i := by ring
          _ = y i := by rw [hcanc]; ring
      simpa [hz, Pi.smul_apply, smul_eq_mul] using hkey.symm
    have hrz : r = A' • z := by
      funext i
      have hAyi : A' * y i = B' * r i := by
        have := congrFun hAy i
        simpa [Pi.smul_apply, smul_eq_mul] using this
      have hkey : A' * (s * r i + t * y i) = r i := by
        calc A' * (s * r i + t * y i) = (A' * s) * r i + t * (A' * y i) := by ring
          _ = (A' * s) * r i + t * (B' * r i) := by rw [hAyi]
          _ = (A' * s + B' * t) * r i := by ring
          _ = r i := by rw [hcanc]; ring
      simpa [hz, Pi.smul_apply, smul_eq_mul] using hkey.symm
    have hAle : ¬ (2 ≤ |A'|) := fun h2 => hprim A' z hzθ h2 hrz.symm
    have hAabs : |A'| ≤ 1 := by omega
    have hAne : A' ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hApp'
      exact hi₀ hApp'.symm
    have hA1 : A' = 1 ∨ A' = -1 := by
      rcases Int.abs_le_one_iff.mp hAabs with h | h | h
      · exact absurd h hAne
      · exact Or.inl h
      · exact Or.inr h
    rcases hA1 with h1 | h1
    · have hzr : z = r := by
        have hh := hrz.symm
        rw [h1, one_smul] at hh
        exact hh
      exact ⟨B', by rw [hyz, hzr]⟩
    · have hzr : z = -r := by
        have hh := hrz.symm
        rw [h1, neg_smul, one_smul] at hh
        have hh2 := congrArg Neg.neg hh
        simpa using hh2
      refine ⟨-B', ?_⟩
      rw [hyz, hzr, smul_neg, neg_smul]

/-- Auxiliary arithmetic: `A / (9 d²) ≤ A / 2` for `A ≥ 0`, `d ≥ 1`. -/
lemma div_nine_sq_le_half {A d : ℝ} (hA : 0 ≤ A) (hd : 1 ≤ d) : A / (9 * d ^ 2) ≤ A / 2 := by
  have h9 : (2 : ℝ) ≤ 9 * d ^ 2 := by nlinarith
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- Auxiliary arithmetic: `A / (9 d²) ≤ A` for `A ≥ 0`, `d ≥ 1`. -/
lemma div_nine_sq_le_self {A d : ℝ} (hA : 0 ≤ A) (hd : 1 ≤ d) : A / (9 * d ^ 2) ≤ A := by
  have h9 : (1 : ℝ) ≤ 9 * d ^ 2 := by nlinarith
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- The modified height is positive. -/
lemma hmod_pos_aux {K : Type*} [Field K] [NumberField K] (β : K) (ℓ : ℂ) : 0 < hmod β ℓ := by
  have hd : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by
    have h : 0 < Module.finrank ℚ K := Module.finrank_pos
    exact_mod_cast h
  have h1 : (0 : ℝ) < 1 / (Module.finrank ℚ K : ℝ) := by positivity
  refine lt_of_lt_of_le h1 ?_
  unfold hmod
  exact le_trans (le_max_right _ _) (le_max_right _ _)

/-- The lattice-theoretic form of the conclusion (phrased with `GammaSub` and the weighted
`ℓ¹`-norm `wn`) implies the exact form required by `relation_lattice_aligned_basis`. -/
lemma aligned_lattice_form_implies {m : ℕ} (α : Fin m → K) (hα : ∀ i, α i ≠ 0) (ℓ : Fin m → ℂ)
    (e : Fin 2 → Fin m → ℤ)
    (h1 : ∀ y : Fin m → ℤ, y ∈ GammaSub α hα ↔ ∃ a b : ℤ, y = a • e 0 + b • e 1)
    (h2 : e 0 ≠ 0 → (e 1 = 0 ∨ ∀ a b : ℤ, a • e 0 + b • e 1 = 0 → a = 0 ∧ b = 0))
    (h3 : e 1 = 0 →
      wn (fun i => (Module.finrank ℚ K : ℝ) * hmod (α i) (ℓ i)) (e 0) ≤
        (9 * (m : ℝ) * (Module.finrank ℚ K : ℝ) ^ 3) ^ m * ∏ i, hmod (α i) (ℓ i))
    (h4 : e 1 ≠ 0 →
      (∑ i, (e 0 i : ℂ) * ℓ i) + (∑ i, (e 1 i : ℂ) * ℓ i) = 0 ∧
      wn (fun i => (Module.finrank ℚ K : ℝ) * hmod (α i) (ℓ i)) (e 0) +
        wn (fun i => (Module.finrank ℚ K : ℝ) * hmod (α i) (ℓ i)) (e 1) ≤
          (9 * (m : ℝ) * (Module.finrank ℚ K : ℝ) ^ 3) ^ m * ∏ i, hmod (α i) (ℓ i)) :
    (∀ y : Fin m → ℤ, IsOfFinOrder (∏ i, α i ^ (y i : ℤ)) ↔ ∃ a b : ℤ, y = a • e 0 + b • e 1) ∧
    (e 0 ≠ 0 → (e 1 = 0 ∨ ∀ a b : ℤ, a • e 0 + b • e 1 = 0 → a = 0 ∧ b = 0)) ∧
    (e 1 = 0 →
      (∑ i, |(((e 0 i : ℤ)) : ℝ)| * ((Module.finrank ℚ K : ℝ) * hmod (α i) (ℓ i))) ≤
        (9 * (m : ℝ) * (Module.finrank ℚ K : ℝ) ^ 3) ^ m * ∏ i, hmod (α i) (ℓ i)) ∧
    (e 1 ≠ 0 →
      (∑ i, (e 0 i : ℂ) * ℓ i) + (∑ i, (e 1 i : ℂ) * ℓ i) = 0 ∧
      (∑ i, |(((e 0 i : ℤ)) : ℝ)| * ((Module.finrank ℚ K : ℝ) * hmod (α i) (ℓ i))) +
        (∑ i, |(((e 1 i : ℤ)) : ℝ)| * ((Module.finrank ℚ K : ℝ) * hmod (α i) (ℓ i))) ≤
          (9 * (m : ℝ) * (Module.finrank ℚ K : ℝ) ^ 3) ^ m * ∏ i, hmod (α i) (ℓ i)) := by
  refine ⟨?_, h2, ?_, ?_⟩
  · intro y
    exact (h1 y).trans Iff.rfl
  · intro h
    simpa [wn] using h3 h
  · intro h
    exact ⟨(h4 h).1, by simpa [wn] using (h4 h).2⟩

theorem relation_lattice_aligned_basis {K : Type*} [Field K] [NumberField K] {m : ℕ} (φ : K →+* ℂ)
    (α : Fin m → K) (hα : ∀ i, α i ≠ 0) (ℓ : Fin m → ℂ)
    (hℓ : ∀ i, Complex.exp (ℓ i) = φ (α i))
    (hdep : ¬ LinearIndependent ℚ ℓ)
    (hmin : ∀ i, LinearIndependent ℚ (fun j : {j : Fin m // j ≠ i} => ℓ j)) :
    ∃ e : Fin 2 → Fin m → ℤ,
      (∀ y : Fin m → ℤ, IsOfFinOrder (∏ i, α i ^ (y i : ℤ)) ↔ ∃ a b : ℤ, y = a • e 0 + b • e 1) ∧
      (e 0 ≠ 0 → (e 1 = 0 ∨ ∀ a b : ℤ, a • e 0 + b • e 1 = 0 → a = 0 ∧ b = 0)) ∧
      (e 1 = 0 →
        (∑ i, |(((e 0 i : ℤ)) : ℝ)| * ((Module.finrank ℚ K : ℝ) * hmod (α i) (ℓ i))) ≤
          (9 * (m : ℝ) * (Module.finrank ℚ K : ℝ) ^ 3) ^ m * ∏ i, hmod (α i) (ℓ i)) ∧
      (e 1 ≠ 0 →
        (∑ i, (e 0 i : ℂ) * ℓ i) + (∑ i, (e 1 i : ℂ) * ℓ i) = 0 ∧
        (∑ i, |(((e 0 i : ℤ)) : ℝ)| * ((Module.finrank ℚ K : ℝ) * hmod (α i) (ℓ i))) +
          (∑ i, |(((e 1 i : ℤ)) : ℝ)| * ((Module.finrank ℚ K : ℝ) * hmod (α i) (ℓ i))) ≤
            (9 * (m : ℝ) * (Module.finrank ℚ K : ℝ) ^ 3) ^ m * ∏ i, hmod (α i) (ℓ i)) := by
  classical
  have hd1 : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by
    have h : 0 < Module.finrank ℚ K := Module.finrank_pos
    exact_mod_cast h
  have hmodnn : ∀ i, 0 ≤ (Module.finrank ℚ K : ℝ) * hmod (α i) (ℓ i) :=
    fun i => mul_nonneg (by linarith) (hmod_pos_aux (α i) (ℓ i)).le
  -- the quantitative input
  obtain ⟨t, ht0, htθ, htbd⟩ := waldschmidt_relation_bound φ α hα ℓ hℓ hdep hmin
  -- the primitive kernel element
  obtain ⟨r, hrθ, hr0, hprim, hrwn⟩ :=
    exists_primitive_kernel ℓ t htθ ht0
      (fun i => (Module.finrank ℚ K : ℝ) * hmod (α i) (ℓ i)) hmodnn
  have hrc : wn (fun i => (Module.finrank ℚ K : ℝ) * hmod (α i) (ℓ i)) r ≤
      (9 * (m : ℝ) * (Module.finrank ℚ K : ℝ) ^ 3) ^ m * (∏ i, hmod (α i) (ℓ i)) /
        (9 * (Module.finrank ℚ K : ℝ) ^ 2) :=
    le_trans hrwn (F_bound_of_waldschmidt_sharp_explicit α ℓ t htbd)
  -- the arithmetic consequences
  have hTnn : 0 ≤ (9 * (m : ℝ) * (Module.finrank ℚ K : ℝ) ^ 3) ^ m * (∏ i, hmod (α i) (ℓ i)) :=
    mul_nonneg (pow_nonneg (by positivity) m)
      (Finset.prod_nonneg fun i _ => (hmod_pos_aux (α i) (ℓ i)).le)
  have hrc2 : wn (fun i => (Module.finrank ℚ K : ℝ) * hmod (α i) (ℓ i)) r ≤
      (9 * (m : ℝ) * (Module.finrank ℚ K : ℝ) ^ 3) ^ m * (∏ i, hmod (α i) (ℓ i)) / 2 :=
    le_trans hrc (div_nine_sq_le_half hTnn hd1)
  -- kernel structure
  have hker : ∀ y : Fin m → ℤ, thetaC ℓ y = 0 → ∃ a : ℤ, y = a • r := by
    intro y hy
    obtain ⟨r₀, hr₀, hr₀θ, hspan⟩ := exists_relation_span ℓ hdep hmin
    obtain ⟨c₁, hc₁⟩ := hspan (fun i => (r i : ℚ)) (by simpa [thetaC] using hrθ)
    obtain ⟨c₂, hc₂⟩ := hspan (fun i => (y i : ℚ)) (by simpa [thetaC] using hy)
    have hc₁0 : c₁ ≠ 0 := by
      intro h0
      apply hr0
      funext i
      have hri : (r i : ℚ) = c₁ * r₀ i := by
        have := congrFun hc₁ i
        simpa [Pi.smul_apply, smul_eq_mul] using this
      rw [h0, zero_mul] at hri
      exact_mod_cast hri
    refine exists_int_smul_of_rat_prop hrθ hy hr0 hprim ⟨c₂ / c₁, ?_⟩
    intro i
    have hri : (r i : ℚ) = c₁ * r₀ i := by
      have := congrFun hc₁ i
      simpa [Pi.smul_apply, smul_eq_mul] using this
    have hyi : (y i : ℚ) = c₂ * r₀ i := by
      have := congrFun hc₂ i
      simpa [Pi.smul_apply, smul_eq_mul] using this
    rw [hyi, hri]
    field_simp
  have hrmem : r ∈ GammaSub α hα := mem_GammaSub_of_thetaC_eq_zero φ α hα ℓ hℓ hrθ
  have hkerG : ∀ y : Fin m → ℤ, y ∈ GammaSub α hα → thetaC ℓ y = 0 → ∃ a : ℤ, y = a • r :=
    fun y _ hy => hker y hy
  have hlin : ∀ (a b : ℤ) (y z : Fin m → ℤ),
      thetaC ℓ (a • y + b • z) = (a : ℂ) * thetaC ℓ y + (b : ℂ) * thetaC ℓ z := by
    intro a b y z
    rw [thetaC_add, thetaC_smul, thetaC_smul]
  have hprimG : ∀ (k : ℤ) (y : Fin m → ℤ), y ∈ GammaSub α hα → 2 ≤ |k| → k • y ≠ r := by
    intro k y _ hk hky
    have hk0 : (k : ℂ) ≠ 0 := by
      have hk0' : k ≠ 0 := by
        intro h; rw [h] at hk; simp at hk
      exact_mod_cast hk0'
    have h1 : thetaC ℓ (k • y) = (k : ℂ) * thetaC ℓ y := thetaC_smul ℓ k y
    rw [hky, hrθ] at h1
    exact hprim k y ((mul_eq_zero.mp h1.symm).resolve_left hk0) hk hky
  obtain ⟨e₀, hgen₀, hind₀⟩ := relation_lattice_generating_pair φ α hα ℓ hℓ hdep hmin
  by_cases hrank : ∃ y : Fin m → ℤ, y ∈ GammaSub α hα ∧ thetaC ℓ y ≠ 0
  · obtain ⟨u, hu, huθ, hub⟩ :=
      exists_short_second_element_fixed φ α hα ℓ hℓ hdep hmin r hrmem hkerG hrc hrank
    obtain ⟨e', hgen', hind', h3', h4'⟩ :=
      aligned_basis_of_short_element (GammaSub α hα) e₀ hgen₀ hind₀ (thetaC ℓ) hlin
        (fun i => (Module.finrank ℚ K : ℝ) * hmod (α i) (ℓ i)) hmodnn
        ((9 * (m : ℝ) * (Module.finrank ℚ K : ℝ) ^ 3) ^ m * ∏ i, hmod (α i) (ℓ i)) hTnn
        r u hrmem hrθ hprimG hu huθ hub hrc2
    exact ⟨e', aligned_lattice_form_implies α hα ℓ e' hgen' hind' h3' h4'⟩
  · simp only [not_exists, not_and, not_not] at hrank
    let e' : Fin 2 → Fin m → ℤ := fun j => if j = (0 : Fin 2) then r else 0
    have he'0 : e' 0 = r := by simp [e']
    have he'1 : e' 1 = 0 := by simp [e']
    have hgen' : ∀ y : Fin m → ℤ, y ∈ GammaSub α hα ↔ ∃ a b : ℤ, y = a • e' 0 + b • e' 1 := by
      intro y
      constructor
      · intro hy
        obtain ⟨a, ha⟩ := hker y (hrank y hy)
        exact ⟨a, 0, by rw [ha, he'0, he'1]; simp⟩
      · rintro ⟨a, b, rfl⟩
        rw [he'0, he'1]
        simp only [smul_zero, add_zero]
        exact (GammaSub α hα).smul_mem a hrmem
    have h3' : e' 1 = 0 → wn (fun i => (Module.finrank ℚ K : ℝ) * hmod (α i) (ℓ i)) (e' 0) ≤
        (9 * (m : ℝ) * (Module.finrank ℚ K : ℝ) ^ 3) ^ m * ∏ i, hmod (α i) (ℓ i) := by
      intro _
      rw [he'0]
      exact le_trans hrc (div_nine_sq_le_self hTnn hd1)
    have h4' : e' 1 ≠ 0 → (∑ i, (e' 0 i : ℂ) * ℓ i) + (∑ i, (e' 1 i : ℂ) * ℓ i) = 0 ∧
        wn (fun i => (Module.finrank ℚ K : ℝ) * hmod (α i) (ℓ i)) (e' 0) +
          wn (fun i => (Module.finrank ℚ K : ℝ) * hmod (α i) (ℓ i)) (e' 1) ≤
            (9 * (m : ℝ) * (Module.finrank ℚ K : ℝ) ^ 3) ^ m * ∏ i, hmod (α i) (ℓ i) :=
      fun h => (h he'1).elim
    exact ⟨e', aligned_lattice_form_implies α hα ℓ e'
      hgen' (fun _ => Or.inl he'1) h3' h4'⟩

end Work.BW

