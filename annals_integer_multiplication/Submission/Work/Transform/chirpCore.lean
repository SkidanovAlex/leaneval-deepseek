import Mathlib
import Submission.Work.Transform.bluesteinDefs

/-!
# The chirp core identity (Bluestein, paper §3)

Let `ts = (t₁,…,t_d)` be a list of *even* positive integers and let `X, Y` be two lists of
naturals of the same length as `ts`, with `Yᵢ < tᵢ`.  Then

`expPi (Σᵢ dᵢ²/tᵢ) = expPi (Σᵢ xᵢ²/tᵢ + Σᵢ yᵢ²/tᵢ - 2 Σᵢ xᵢyᵢ/tᵢ)`

where `dᵢ = (xᵢ + tᵢ - yᵢ) mod tᵢ` is the `i`-th mixed-radix digit of the (componentwise)
difference of `X` and `Y` (`HvdH.subDigits`) and `expPi z = e^{πiz}`.  This is the identity which
identifies the Bluestein convolution kernel `expPi(Σᵢ (jᵢ-kᵢ)²/tᵢ)` with the product
`a_j · a_k · conj(a_{j-k})` of chirp factors.

The mathematical content is one-dimensional: for `t` even, `0 < t`, `y < t` and `x` arbitrary,
writing `x + t - y = t·q + d` gives `(x - y) - d = t·(q - 1) =: t·m`, hence

`(x - y)² - d² = 2·(d·m + m²·(t/2))·t`,

so `((x-y)² - d²)/t` is an even integer; `expPi` is invariant under adding `2πi·ℤ` to the
exponent.  The multidimensional statement is the induction over `ts`.
-/

set_option autoImplicit false

namespace Work.Transform

/-- One-dimensional chirp core: for even positive `t` and `y < t`, the exponent
`(x + t - y) % t` squared over `t` gives the same `expPi` as `(x - y)²/t`. -/
lemma chirpStep (t x y : ℕ) (ht0 : 0 < t) (hte : Even t) (hy : y < t) :
    expPi (((((x + t - y) % t) * ((x + t - y) % t) : ℕ) : ℝ) / (t : ℝ))
      = expPi ((((x : ℝ) - (y : ℝ)) ^ 2) / (t : ℝ)) := by
  obtain ⟨t', ht'⟩ := hte
  set d : ℕ := (x + t - y) % t with hd
  set q : ℕ := (x + t - y) / t with hq
  have hlin : ((q : ℤ) * (t : ℤ) + (d : ℤ)) = ((x + t - y : ℕ) : ℤ) := by
    have h : (x + t - y) / t * t + (x + t - y) % t = x + t - y := by
      rw [mul_comm]; exact Nat.div_add_mod _ _
    rw [hq, hd, ← Nat.cast_mul, ← Nat.cast_add, h]
  have hcast : ((x + t - y : ℕ) : ℤ) = (x : ℤ) + (t : ℤ) - (y : ℤ) := by
    have h2 : y ≤ x + t := by omega
    rw [Nat.cast_sub h2]
    push_cast
    ring
  set m : ℤ := (q : ℤ) - 1 with hm
  have hkey : (x : ℤ) - (y : ℤ) = (d : ℤ) + m * (t : ℤ) := by
    have h1 : (x : ℤ) - (y : ℤ) - (d : ℤ) = ((q : ℤ) - 1) * (t : ℤ) := by
      rw [sub_mul, one_mul]
      linarith [hlin, hcast]
    rw [hm]
    linarith [h1]
  have hkeyR : (x : ℝ) - (y : ℝ) = (d : ℝ) + (m : ℝ) * (t : ℝ) := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) hkey
    push_cast at h
    exact h
  have htR : (t : ℝ) = 2 * (t' : ℝ) := by
    have h := congrArg (fun z : ℕ => (z : ℝ)) ht'
    push_cast at h
    linarith
  have hnum : ((x : ℝ) - (y : ℝ)) ^ 2 - (d : ℝ) ^ 2
      = 2 * ((d * m + m ^ 2 * (t' : ℤ) : ℤ) : ℝ) * (t : ℝ) := by
    rw [hkeyR, htR]
    push_cast
    ring
  have htne : (t : ℝ) ≠ 0 := by exact_mod_cast ht0.ne'
  have hdiv : ((x : ℝ) - (y : ℝ)) ^ 2 / (t : ℝ) - (d : ℝ) ^ 2 / (t : ℝ)
      = 2 * (((d * m + m ^ 2 * (t' : ℤ) : ℤ)) : ℝ) := by
    rw [div_sub_div_same, hnum]
    field_simp
  have hexp := expPi_eq_of_sub_eq_two_mul (((x : ℝ) - (y : ℝ)) ^ 2 / (t : ℝ))
    ((d : ℝ) ^ 2 / (t : ℝ)) (d * m + m ^ 2 * (t' : ℤ)) hdiv
  rw [show ((((x + t - y) % t) * ((x + t - y) % t) : ℕ) : ℝ) / (t : ℝ)
        = (d : ℝ) ^ 2 / (t : ℝ) from by rw [hd]; push_cast; ring,
      ← hexp]

/-- Multidimensional chirp core, by induction on `ts`. -/
lemma chirpCore_aux : ∀ (ts X Y : List ℕ), X.length = ts.length → Y.length = ts.length →
    (∀ t ∈ ts, 0 < t) → (∀ t ∈ ts, Even t) →
    (∀ i, i < ts.length → Y.getD i 0 < ts.getD i 0) →
    expPi (HvdH.phase ts (HvdH.subDigits ts X Y) (HvdH.subDigits ts X Y))
      = expPi (HvdH.phase ts X X + HvdH.phase ts Y Y - 2 * HvdH.phase ts X Y) := by
  intro ts
  induction ts with
  | nil =>
      intro X Y hX hY hpos heven hYb
      have hX' : X = [] := List.eq_nil_of_length_eq_zero hX
      have hY' : Y = [] := List.eq_nil_of_length_eq_zero hY
      subst hX'; subst hY'
      simp [HvdH.phase, expPi]
  | cons t ts ih =>
      intro X Y hX hY hpos heven hYb
      obtain ⟨x, X', rfl⟩ : ∃ x X', X = x :: X' := by
        cases X with
        | nil => simp at hX
        | cons x X' => exact ⟨x, X', rfl⟩
      obtain ⟨y, Y', rfl⟩ : ∃ y Y', Y = y :: Y' := by
        cases Y with
        | nil => simp at hY
        | cons y Y' => exact ⟨y, Y', rfl⟩
      simp only [List.length_cons, Nat.succ.injEq] at hX hY
      have ht : 0 < t := hpos t (by simp)
      have hte : Even t := heven t (by simp)
      have hy : y < t := by simpa using hYb 0 (by simp)
      have hpos' : ∀ u ∈ ts, 0 < u := fun u hu => hpos u (by simp [hu])
      have heven' : ∀ u ∈ ts, Even u := fun u hu => heven u (by simp [hu])
      have hYb' : ∀ i, i < ts.length → Y'.getD i 0 < ts.getD i 0 := by
        intro i hi
        have h := hYb (i + 1) (by simpa using hi)
        simpa using h
      -- the algebraic identity identifying the two exponents
      have hRHS : ((x * x : ℕ) : ℝ) / (t : ℝ) + HvdH.phase ts X' X'
            + (((y * y : ℕ) : ℝ) / (t : ℝ) + HvdH.phase ts Y' Y')
            - 2 * (((x * y : ℕ) : ℝ) / (t : ℝ) + HvdH.phase ts X' Y')
          = (((x : ℝ) - (y : ℝ)) ^ 2) / (t : ℝ)
            + (HvdH.phase ts X' X' + HvdH.phase ts Y' Y' - 2 * HvdH.phase ts X' Y') := by
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
        push_cast
        ring
      simp only [HvdH.subDigits, HvdH.phase]
      rw [hRHS, expPi_add, expPi_add, chirpStep t x y ht hte hy,
          ih X' Y' hX hY hpos' heven' hYb']

theorem chirpCore (ts : List ℕ) (hpos : ∀ t ∈ ts, 0 < t) (heven : ∀ t ∈ ts, Even t)
    (X Y : List ℕ) (hX : X.length = ts.length) (hY : Y.length = ts.length)
    (hYb : ∀ i < ts.length, Y.getD i 0 < ts.getD i 0) :
    Work.Transform.expPi (HvdH.phase ts (HvdH.subDigits ts X Y) (HvdH.subDigits ts X Y))
      = Work.Transform.expPi (HvdH.phase ts X X + HvdH.phase ts Y Y
          - 2 * HvdH.phase ts X Y) :=
  chirpCore_aux ts X Y hX hY hpos heven hYb

end Work.Transform
