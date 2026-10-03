/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib

/-!
# §6 of Krause–Mirek–Tao: setting for the inverse-theoretic (minor arc) analysis

This module is the base of the `InverseTheory` area, which formalises Section 6 of
B. Krause, M. Mirek and T. Tao, *Pointwise ergodic theorems for non-conventional bilinear
polynomial averages*, Annals of Math. **195** (2022) — the deduction of the *single-scale minor
arc estimate* (`improv`) from the inverse theorem of Peluse–Prendiville/Peluse.

The reason this area exists separately is that nothing of its kind is in Mathlib: there is no
theory of major arcs on the frequency circle, no quantified inverse theorem for bilinear averages
of polynomial progressions, and no equidistribution theory of polynomial sequences.

## The objects defined here

* `jb` — the Japanese bracket `⟨t⟩ = (1 + t²)^{1/2}` of the paper's notation section, with
  `jbDecay n t = ⟨t⟩^{-n}` (the shape of the error terms of Lemma `calc`);
* `LogScale N` — the paper's logarithmic scale `Log N = ⌊log₂ N⌋` (so that
  `2 ^ LogScale N ≤ N < 2 ^ (LogScale N + 1)` for `N ≥ 1`);
* `ellOne`, `ellTwoSq`, `ellTwo`, `ellInf` — the `ℓ¹`, `ℓ²`, `ℓ^∞` seminorms on `ℤ → ℂ`;
* `AhalfZ N P f g` — the *upper-half* bilinear average
  `Ã_N(f,g)(x) = (1/N) ∑_{N/2 < n ≤ N} f (x + n) g (x + P(n))`
  on the integers.  This is the integer-shift model of `Submission.Ahalf` (with `T` the shift
  `x ↦ x + 1`, `P₁ = X` and `P₂ = P`); see `Submission.Work.Analysis.InverseTheory.Bridge` for
  the bridging lemma `AhalfZ_eq_Ahalf_shift`.
* `bilinPair f g` — the paper's bilinear pairing `⟨f, g⟩ = ∑_x f(x) g(x)` (no conjugation);
* `SupportIn f M` — `f` is supported in `[-M, M]`.

## Conventions

Everything is stated over the integers with *counting measure*; the Fourier transform on `ℤ` is
`Work.Analysis.InverseTheory.ZFourier` and the frequency circle is
`Work.Analysis.IonescuWainger.Circle = ℝ/ℤ` (both in `MajorArcs.lean`).
As in the paper, all constants are absolute unless a dependency is displayed; as there, `A ≲ B`
means `A ≤ C B`, and we always render `≲` as an explicit `≤` with an explicit constant, never as
an existential.
-/

set_option autoImplicit false

open scoped BigOperators FourierTransform
open MeasureTheory
open Polynomial

namespace Work.Analysis.InverseTheory

/-! ## The Japanese bracket -/

/-- The Japanese bracket `⟨t⟩ = (1 + t²)^{1/2}`. -/
noncomputable def jb (t : ℝ) : ℝ := Real.sqrt (1 + t ^ 2)

@[simp] theorem jb_zero : jb 0 = 1 := by simp [jb]

theorem jb_pos (t : ℝ) : 0 < jb t := Real.sqrt_pos.mpr (by positivity)

theorem jb_nonneg (t : ℝ) : 0 ≤ jb t := (jb_pos t).le

theorem one_le_jb (t : ℝ) : 1 ≤ jb t := by
  have h : (1 : ℝ) ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (1 + t ^ 2) := Real.sqrt_le_sqrt h
    _ = jb t := rfl

@[simp] theorem sq_jb (t : ℝ) : jb t ^ 2 = 1 + t ^ 2 := by
  rw [jb, Real.sq_sqrt (by positivity)]

theorem jb_eq_sqrt (t : ℝ) : jb t = Real.sqrt (1 + t ^ 2) := rfl

theorem abs_le_jb (t : ℝ) : |t| ≤ jb t := by
  rw [jb, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by linarith [sq_nonneg t])

theorem jb_le_one_add_abs (t : ℝ) : jb t ≤ 1 + |t| := by
  have h : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by
    rw [add_sq, one_pow, sq_abs]; nlinarith [abs_nonneg t]
  calc jb t = Real.sqrt (1 + t ^ 2) := rfl
    _ ≤ Real.sqrt ((1 + |t|) ^ 2) := Real.sqrt_le_sqrt h
    _ = 1 + |t| := Real.sqrt_sq (by positivity)

theorem jb_neg (t : ℝ) : jb (-t) = jb t := by rw [jb, jb, neg_sq]

theorem jb_abs (t : ℝ) : jb |t| = jb t := by rw [jb, jb, sq_abs]

theorem jb_mono {s t : ℝ} : jb s ≤ jb t ↔ s ^ 2 ≤ t ^ 2 := by
  rw [jb, jb, Real.sqrt_le_sqrt_iff (by positivity), add_le_add_iff_left]

theorem jb_le_jb_iff {s t : ℝ} : jb s ≤ jb t ↔ |s| ≤ |t| := by
  rw [jb_mono, sq_le_sq]

theorem jb_mul_self (t : ℝ) : jb t * jb t = 1 + t ^ 2 := by
  rw [← sq, sq_jb]

theorem jb_inv_le_one (t : ℝ) : (jb t)⁻¹ ≤ 1 := by
  rw [inv_le_one₀ (jb_pos t)]; exact one_le_jb t

theorem jb_inv_pos (t : ℝ) : 0 < (jb t)⁻¹ := inv_pos.mpr (jb_pos t)

theorem jb_inv_nonneg (t : ℝ) : 0 ≤ (jb t)⁻¹ := (jb_inv_pos t).le

/-- The paper's `⟨t⟩^{-n}`, written with natural powers; this is the shape of the error terms of
Lemma `calc`. -/
noncomputable def jbDecay (n : ℕ) (t : ℝ) : ℝ := (jb t)⁻¹ ^ n

theorem jbDecay_nonneg (n : ℕ) (t : ℝ) : 0 ≤ jbDecay n t := by
  rw [jbDecay]; exact pow_nonneg (jb_inv_nonneg t) n

theorem jbDecay_eq_rpow (n : ℕ) (t : ℝ) : jbDecay n t = (jb t) ^ (-(n : ℝ)) := by
  rw [jbDecay, ← Real.rpow_natCast ((jb t)⁻¹) n, Real.inv_rpow (jb_nonneg t) (n : ℝ),
    ← Real.rpow_neg (jb_nonneg t)]

theorem jbDecay_le_one (n : ℕ) (t : ℝ) : jbDecay n t ≤ 1 := by
  rw [jbDecay]
  calc (jb t)⁻¹ ^ n ≤ 1 := pow_le_one₀ (jb_inv_nonneg t) (jb_inv_le_one t)

theorem jbDecay_anti {m n : ℕ} (hmn : m ≤ n) (t : ℝ) : jbDecay n t ≤ jbDecay m t :=
  pow_le_pow_of_le_one (jb_inv_nonneg t) (jb_inv_le_one t) hmn

theorem jbDecay_add (m n : ℕ) (t : ℝ) : jbDecay (m + n) t = jbDecay m t * jbDecay n t := by
  rw [jbDecay, jbDecay, jbDecay, pow_add]

/-- `⟨t⟩ ≤ 2 max 1 |t|`: the bracket is comparable with `max 1 |t|`. -/
theorem jb_le_two_mul_max_one_abs (t : ℝ) : jb t ≤ 2 * max 1 |t| := by
  have h1 : 1 ≤ max 1 |t| := le_max_left _ _
  have h2 : |t| ≤ max 1 |t| := le_max_right _ _
  calc jb t ≤ 1 + |t| := jb_le_one_add_abs t
    _ ≤ max 1 |t| + max 1 |t| := by linarith
    _ = 2 * max 1 |t| := by ring

theorem max_one_abs_le_jb (t : ℝ) : max 1 |t| ≤ jb t :=
  max_le (one_le_jb t) (abs_le_jb t)

/-- The bracket is submultiplicative up to the factor `√2`. -/
theorem jb_add_le_sqrt_two_mul (s t : ℝ) : jb (s + t) ≤ Real.sqrt 2 * jb s * jb t := by
  have h : 1 + (s + t) ^ 2 ≤ 2 * ((1 + s ^ 2) * (1 + t ^ 2)) := by
    nlinarith [sq_nonneg (s - t)]
  have h2 : jb (s + t) ≤ Real.sqrt (2 * ((1 + s ^ 2) * (1 + t ^ 2))) := by
    rw [jb]; exact Real.sqrt_le_sqrt h
  refine h2.trans (le_of_eq ?_)
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_mul (by positivity)]
  simp only [jb]
  ring

/-! ## The real Fourier transform

The real-line Fourier transform `𝓕` is a scoped notation; to keep the statements of this area
independent of whether the `FourierTransform` notation has been opened, we expose it under the
plain name `realFourier`.  Likewise `SchwartzR` is the Schwartz space `𝓢(ℝ, ℂ)` without the
`SchwartzMap` notation. -/

/-- The Schwartz space `𝓢(ℝ, ℂ)`, under a name usable without the `SchwartzMap` notation. -/
abbrev SchwartzR : Type := SchwartzMap ℝ ℂ

/-- The Fourier transform of a function `ℝ → ℂ` (Mathlib's `𝓕`), under a plain name. -/
noncomputable def realFourier (f : ℝ → ℂ) (ξ : ℝ) : ℂ := 𝓕 f ξ

/-- The Fourier transform of a Schwartz function is the Fourier transform of the underlying
function. -/
theorem realFourier_coe (ψ : SchwartzR) (ξ : ℝ) : realFourier (ψ : ℝ → ℂ) ξ = (𝓕 ψ) ξ := rfl

/-! ## The logarithmic scale `Log N = ⌊log₂ N⌋` -/

/-- The paper's logarithmic scale `Log N = ⌊log₂ N⌋`. -/
def LogScale (N : ℕ) : ℕ := Nat.log2 N

theorem LogScale_eq_log_two (N : ℕ) : LogScale N = Nat.log 2 N := Nat.log2_eq_log_two

theorem pow_LogScale_le {N : ℕ} (hN : N ≠ 0) : 2 ^ LogScale N ≤ N := by
  rw [LogScale_eq_log_two]; exact Nat.pow_log_le_self 2 hN

theorem lt_pow_LogScale_succ (N : ℕ) : N < 2 ^ (LogScale N + 1) := by
  rw [LogScale_eq_log_two]; exact Nat.lt_pow_succ_log_self (by norm_num) N

theorem LogScale_mono : Monotone LogScale := fun _ _ h => by
  rw [LogScale_eq_log_two, LogScale_eq_log_two]; exact Nat.log_monotone h

theorem LogScale_le_self (N : ℕ) : LogScale N ≤ N := by
  rw [LogScale_eq_log_two]; exact Nat.log_le_self 2 N

@[simp] theorem LogScale_pow_two (k : ℕ) : LogScale (2 ^ k) = k := by
  rw [LogScale_eq_log_two]; exact Nat.log_pow (by norm_num) k

@[simp] theorem LogScale_zero : LogScale 0 = 0 := by simp [LogScale]

@[simp] theorem LogScale_one : LogScale 1 = 0 := by
  rw [LogScale_eq_log_two]; exact Nat.log_one_right 2

/-- The frequency-dual statement `2 ^ Log N ≤ N < 2 ^ (Log N + 1)`. -/
theorem pow_LogScale_le_and_lt {N : ℕ} (hN : 1 ≤ N) :
    2 ^ LogScale N ≤ N ∧ N < 2 ^ (LogScale N + 1) :=
  ⟨pow_LogScale_le (by omega), lt_pow_LogScale_succ N⟩

/-- `⟨Log N⟩ ≤ 1 + Log N`. -/
theorem jb_LogScale_le (N : ℕ) : jb (LogScale N) ≤ 1 + LogScale N := by
  have := jb_le_one_add_abs ((LogScale N : ℕ) : ℝ)
  simpa using this

/-! ## The discrete `ℓ^p` norms on `ℤ` -/

/-- The `ℓ¹(ℤ)` seminorm `∑_x ‖f x‖`. -/
noncomputable def ellOne (f : ℤ → ℂ) : ℝ := ∑' x : ℤ, ‖f x‖

/-- The squared `ℓ²(ℤ)` seminorm `∑_x ‖f x‖²`. -/
noncomputable def ellTwoSq (f : ℤ → ℂ) : ℝ := ∑' x : ℤ, ‖f x‖ ^ 2

/-- The `ℓ²(ℤ)` seminorm `(∑_x ‖f x‖²)^{1/2}`. -/
noncomputable def ellTwo (f : ℤ → ℂ) : ℝ := Real.sqrt (ellTwoSq f)

/-- The `ℓ^∞(ℤ)` seminorm `sup_x ‖f x‖`. -/
noncomputable def ellInf (f : ℤ → ℂ) : ℝ := ⨆ x : ℤ, ‖f x‖

theorem ellTwoSq_nonneg (f : ℤ → ℂ) : 0 ≤ ellTwoSq f := tsum_nonneg fun _ => by positivity

theorem ellTwo_nonneg (f : ℤ → ℂ) : 0 ≤ ellTwo f := Real.sqrt_nonneg _

theorem sq_ellTwo (f : ℤ → ℂ) : ellTwo f ^ 2 = ellTwoSq f :=
  Real.sq_sqrt (ellTwoSq_nonneg f)

theorem ellOne_nonneg (f : ℤ → ℂ) : 0 ≤ ellOne f := tsum_nonneg fun _ => norm_nonneg _

theorem le_ellInf {f : ℤ → ℂ} (hb : BddAbove (Set.range fun x : ℤ => ‖f x‖)) (x : ℤ) :
    ‖f x‖ ≤ ellInf f := le_ciSup hb x

theorem ellInf_le {f : ℤ → ℂ} {M : ℝ} (h : ∀ x : ℤ, ‖f x‖ ≤ M) : ellInf f ≤ M :=
  ciSup_le h

/-- The `ℓ^∞` seminorm of a finite-support function is attained, hence nonnegative. -/
theorem ellInf_nonneg {f : ℤ → ℂ} (hb : BddAbove (Set.range fun x : ℤ => ‖f x‖)) :
    0 ≤ ellInf f := by
  obtain ⟨x⟩ : Nonempty ℤ := ⟨0⟩
  exact (norm_nonneg (f 0)).trans (le_ellInf hb 0)

/-! ## The bilinear pairing and the halved average on `ℤ` -/

/-- The paper's bilinear pairing `⟨f, g⟩ = ∑_x f(x) g(x)` (no complex conjugation). -/
noncomputable def bilinPair (f g : ℤ → ℂ) : ℂ := ∑' x : ℤ, f x * g x

/-- The *upper-half* bilinear average on `ℤ`,
`Ã_N(f,g)(x) = (1/N) ∑_{N/2 < n ≤ N} f (x + n) g (x + P(n))`.

This is the integer-shift model of the paper's `Ã_N^{n,P(n)}`: it is
`Submission.Ahalf T N X P f g x` for `T` the shift `y ↦ y + 1` (see `AhalfZ_eq_Ahalf_shift`). -/
noncomputable def AhalfZ (N : ℕ) (P : ℤ[X]) (f g : ℤ → ℂ) (x : ℤ) : ℂ :=
  (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, f (x + (n : ℤ)) * g (x + P.eval (n : ℤ))

theorem AhalfZ_def (N : ℕ) (P : ℤ[X]) (f g : ℤ → ℂ) (x : ℤ) :
    AhalfZ N P f g x
      = (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, f (x + (n : ℤ)) * g (x + P.eval (n : ℤ)) :=
  rfl

@[simp] theorem AhalfZ_zero (P : ℤ[X]) (f g : ℤ → ℂ) (x : ℤ) : AhalfZ 0 P f g x = 0 := by
  simp [AhalfZ]

/-! ## Support conditions -/

/-- `f` is supported in `[-M, M]`. -/
def SupportIn (f : ℤ → ℂ) (M : ℕ) : Prop := ∀ x : ℤ, M < x.natAbs → f x = 0

theorem SupportIn.zero (M : ℕ) : SupportIn (0 : ℤ → ℂ) M := fun _ _ => rfl

theorem SupportIn.mono {f : ℤ → ℂ} {M M' : ℕ} (h : SupportIn f M) (hMM' : M ≤ M') :
    SupportIn f M' := fun x hx => h x (lt_of_le_of_lt hMM' hx)

theorem SupportIn.congr {f g : ℤ → ℂ} {M : ℕ} (h : SupportIn f M) (hfg : ∀ x, f x = g x) :
    SupportIn g M := fun x hx => by rw [← hfg x]; exact h x hx

theorem SupportIn.add {f g : ℤ → ℂ} {M : ℕ} (hf : SupportIn f M) (hg : SupportIn g M) :
    SupportIn (f + g) M := fun x hx => by simp [hf x hx, hg x hx]

theorem SupportIn.neg {f : ℤ → ℂ} {M : ℕ} (hf : SupportIn f M) : SupportIn (-f) M :=
  fun x hx => by simpa using hf x hx

theorem SupportIn.smul {f : ℤ → ℂ} {M : ℕ} (c : ℂ) (hf : SupportIn f M) :
    SupportIn (c • f) M := fun x hx => by rw [Pi.smul_apply, hf x hx, smul_zero]

/-- The only nonzero values of a function supported in `[-M, M]` lie in that interval. -/
theorem SupportIn.mem_Icc {f : ℤ → ℂ} {M : ℕ} (h : SupportIn f M) {x : ℤ} (hx : f x ≠ 0) :
    x ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) := by
  rw [Finset.mem_Icc]
  have h2 : x.natAbs ≤ M := not_lt.mp fun hc => hx (h x hc)
  have h3 : (x.natAbs : ℤ) ≤ (M : ℤ) := by exact_mod_cast h2
  have h4 : x ≤ x.natAbs := Int.le_natAbs
  have h5 : -x ≤ x.natAbs := by
    have := Int.le_natAbs (a := -x)
    simpa using this
  constructor <;> omega

end Work.Analysis.InverseTheory
