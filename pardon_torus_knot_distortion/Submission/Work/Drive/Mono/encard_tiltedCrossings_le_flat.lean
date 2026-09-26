import Mathlib
import Submission.Work.Drive.Mono.CutTransverse
import Submission.Work.Drive.Mono.TiltedTraceData
import Submission.Work.Drive.Mono.compPeriodic.component_of_periodic_open
import Submission.Work.Drive.Mono.compPeriodic.component_add_nat_mul
import Submission.Work.Drive.Mono.intervalZeros.unique_zero_of_deriv_ne_zero
import Submission.Work.Drive.Mono.intervalZeros.injOn_of_deriv_ne_zero

/-!
# The tilted crossing count is bounded by the flat crossing count

Let `K` be a knot, `PBox s c σ` Pardon's box and `{y | y (σ 2) = c (σ 2) + u}` the *flat* cutting
plane, counted by `B`.  Let `{y | inner ℝ v y = inner ℝ v c + u}` be a *tilted* plane which is
close to the flat one on the box (`hclose`, with `ε₀ > 0`), while the `σ 2`-coordinate of the knot

* has no critical point at distance `< ε₀` from the flat level inside the box (`hnoflatcrit`),
* is at distance `≥ ε₀` from the flat level on the box sphere (`hboxsph`),
* and the tilted height has no critical point where the flat coordinate is at distance `< ε₀`
  from the flat level inside the box (`htiltmono`).

Then the parameters of the tilted crossings inside the box in the fundamental interval are at most
`B`.

The mechanism is the set `A = {t | K.curve t ∈ PBox ∧ |g t| < ε₀}` where `g` is the flat
`σ 2`-coordinate minus its level: `A` is open (the box is open), `2π`-periodic (`K.curve` is), and
every point of `closure A \ A` carries `|g| = ε₀`.  On `A` both `deriv g` and `deriv φ` vanish
nowhere (`φ` the tilted height minus its level).  The components of `A` are therefore intervals of
length `≤ 2π` whose endpoints carry `|g| = ε₀ = ∓g`, so each component carries exactly one zero of
`g` (intermediate value theorem plus the injectivity forced by `deriv g ≠ 0`), while `deriv φ ≠ 0`
forces *at most* one zero of `φ` in each component.  Matching each `φ`-zero with the `g`-zero of
its own component, and reducing that zero modulo `2π`, gives an injection from the tilted
crossings into the flat ones.

The abstract statement is `Work.Drive.Mono.encard_zeroSet_le_of_periodic_open`.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

/-! ## Periodicity helpers -/

/-- A `T`-periodic set is `n * T`-periodic, for `n : ℕ`. -/
theorem mem_add_nat_mul_iff {A : Set ℝ} {T : ℝ} (hAper : ∀ t : ℝ, t + T ∈ A ↔ t ∈ A)
    (x : ℝ) (n : ℕ) : x + n * T ∈ A ↔ x ∈ A := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    have h : x + ((k : ℝ) + 1) * T = (x + k * T) + T := by ring
    rw [hcast, h, hAper, ih]

/-- A function with period `T` has period `n * T`, for `n : ℕ`. -/
theorem apply_add_nat_mul {f : ℝ → ℝ} {T : ℝ} (hf : ∀ t : ℝ, f (t + T) = f t)
    (x : ℝ) (n : ℕ) : f (x + n * T) = f x := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    have h : x + ((k : ℝ) + 1) * T = (x + k * T) + T := by ring
    rw [hcast, h, hf, ih]

/-- A `T`-periodic set is `k * T`-periodic, for `k : ℤ`. -/
theorem mem_add_int_mul_iff {A : Set ℝ} {T : ℝ} (hAper : ∀ t : ℝ, t + T ∈ A ↔ t ∈ A)
    (x : ℝ) (k : ℤ) : x + (k : ℝ) * T ∈ A ↔ x ∈ A := by
  rcases Int.eq_nat_or_neg k with ⟨n, hk | hk⟩
  · subst hk
    have hcast : (((n : ℤ)) : ℝ) = (n : ℝ) := by simp
    rw [hcast]
    exact mem_add_nat_mul_iff hAper x n
  · subst hk
    have hcast : ((-(n : ℤ) : ℤ) : ℝ) = -(n : ℝ) := by simp
    rw [hcast]
    have hgoal : x + (-(n : ℝ)) * T = x - n * T := by ring
    rw [hgoal]
    have h := mem_add_nat_mul_iff hAper (x - n * T) n
    have hx : x - n * T + n * T = x := by ring
    rw [hx] at h
    exact h.symm

/-- A function with period `T` has period `k * T`, for `k : ℤ`. -/
theorem apply_add_int_mul {f : ℝ → ℝ} {T : ℝ} (hf : ∀ t : ℝ, f (t + T) = f t)
    (x : ℝ) (k : ℤ) : f (x + (k : ℝ) * T) = f x := by
  rcases Int.eq_nat_or_neg k with ⟨n, hk | hk⟩
  · subst hk
    have hcast : (((n : ℤ)) : ℝ) = (n : ℝ) := by simp
    rw [hcast]
    exact apply_add_nat_mul hf x n
  · subst hk
    have hcast : ((-(n : ℤ) : ℤ) : ℝ) = -(n : ℝ) := by simp
    rw [hcast]
    have hgoal : x + (-(n : ℝ)) * T = x - n * T := by ring
    rw [hgoal]
    have h := apply_add_nat_mul hf (x - n * T) n
    have hx : x - n * T + n * T = x := by ring
    rw [hx] at h
    exact h.symm

/-! ## The abstract per-period count -/

/-- **Counting the zeros of `φ` against the zeros of `g`, one period.**
`A` is open and `T`-periodic with `Aᶜ` nonempty; on `A` both derivatives vanish nowhere and
`|g| < ε`, while on `closure A \ A` we have `ε ≤ |g|`.  Then in any half-open interval of length
`T` there are no more zeros of `φ` in `A` than there are zeros of `g` in `A`. -/
theorem encard_zeroSet_le_of_periodic_open
    {A : Set ℝ} {g φ : ℝ → ℝ} {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε)
    (hAopen : IsOpen A) (hAper : ∀ t : ℝ, t + T ∈ A ↔ t ∈ A) (hne : (Aᶜ).Nonempty)
    (hgcont : Continuous g) (hgper : ∀ t : ℝ, g (t + T) = g t) (hφper : ∀ t : ℝ, φ (t + T) = φ t)
    (hgd : ∀ t ∈ A, deriv g t ≠ 0) (hφd : ∀ t ∈ A, deriv φ t ≠ 0)
    (hgε : ∀ t ∈ A, |g t| < ε) (hbd : ∀ t ∈ closure A \ A, ε ≤ |g t|) :
    Set.encard {t : ℝ | t ∈ Set.Ico 0 T ∧ t ∈ A ∧ φ t = 0} ≤
      Set.encard {t : ℝ | t ∈ Set.Ico 0 T ∧ t ∈ A ∧ g t = 0} := by
  classical
  have hA_nat : ∀ (x : ℝ) (n : ℕ), x + n * T ∈ A ↔ x ∈ A := mem_add_nat_mul_iff hAper
  have hg_nat : ∀ (x : ℝ) (n : ℕ), g (x + n * T) = g x := apply_add_nat_mul hgper
  have hφ_nat : ∀ (x : ℝ) (n : ℕ), φ (x + n * T) = φ x := apply_add_nat_mul hφper
  have hA_int : ∀ (x : ℝ) (k : ℤ), x + (k : ℝ) * T ∈ A ↔ x ∈ A := mem_add_int_mul_iff hAper
  have hg_int : ∀ (x : ℝ) (k : ℤ), g (x + (k : ℝ) * T) = g x := apply_add_int_mul hgper
  -- component endpoints
  let a : ℝ → ℝ := fun t => sSup {s : ℝ | s ∉ A ∧ s < t}
  let b : ℝ → ℝ := fun t => sInf {s : ℝ | t < s ∧ s ∉ A}
  have hcomp : ∀ t ∈ A, a t < t ∧ t < b t ∧ Set.Ioo (a t) (b t) ⊆ A ∧
      a t ∈ closure A ∧ b t ∈ closure A ∧ a t ∉ A ∧ b t ∉ A :=
    fun t ht => compPeriodic.component_of_periodic_open hT hAopen hAper hne t ht
  have ha_lt : ∀ t ∈ A, a t < t := fun t ht => (hcomp t ht).1
  have hlt_b : ∀ t ∈ A, t < b t := fun t ht => (hcomp t ht).2.1
  have hsub : ∀ t ∈ A, Set.Ioo (a t) (b t) ⊆ A := fun t ht => (hcomp t ht).2.2.1
  have ha_cl : ∀ t ∈ A, a t ∈ closure A := fun t ht => (hcomp t ht).2.2.2.1
  have hb_cl : ∀ t ∈ A, b t ∈ closure A := fun t ht => (hcomp t ht).2.2.2.2.1
  have ha_nA : ∀ t ∈ A, a t ∉ A := fun t ht => (hcomp t ht).2.2.2.2.2.1
  have hb_nA : ∀ t ∈ A, b t ∉ A := fun t ht => (hcomp t ht).2.2.2.2.2.2
  have ht_Ioo : ∀ t ∈ A, t ∈ Set.Ioo (a t) (b t) := fun t ht => ⟨ha_lt t ht, hlt_b t ht⟩
  have hab_lt : ∀ t ∈ A, a t < b t := fun t ht => lt_trans (ha_lt t ht) (hlt_b t ht)
  have hadd : ∀ (t : ℝ) (n : ℕ), a (t + n * T) = a t + n * T ∧ b (t + n * T) = b t + n * T :=
    fun t n => compPeriodic.component_add_nat_mul hT hAper hne t n
  -- `|g| = ε` at the component endpoints
  have hcl_abs : closure A ⊆ {s : ℝ | |g s| ≤ ε} :=
    closure_minimal (fun s hs => le_of_lt (hgε s hs)) (isClosed_Iic.preimage hgcont.abs)
  have hga : ∀ t ∈ A, |g (a t)| = ε := fun t ht =>
    le_antisymm (hcl_abs (ha_cl t ht)) (hbd (a t) ⟨ha_cl t ht, ha_nA t ht⟩)
  have hgb : ∀ t ∈ A, |g (b t)| = ε := fun t ht =>
    le_antisymm (hcl_abs (hb_cl t ht)) (hbd (b t) ⟨hb_cl t ht, hb_nA t ht⟩)
  -- the unique zero of `g` in each component
  have hzero : ∀ t ∈ A, ∃! z : ℝ, z ∈ Set.Ioo (a t) (b t) ∧ g z = 0 := fun t ht =>
    intervalZeros.unique_zero_of_deriv_ne_zero (hab_lt t ht) hε hgcont.continuousOn
      (fun x hx => hgd x (hsub t ht hx)) (fun x hx => hgε x (hsub t ht hx))
      (hga t ht) (hgb t ht)
  let z : ℝ → ℝ := fun t => if ht : t ∈ A then Classical.choose (hzero t ht) else 0
  have hz_spec : ∀ t (ht : t ∈ A), z t ∈ Set.Ioo (a t) (b t) ∧ g (z t) = 0 := by
    intro t ht
    have h : z t = Classical.choose (hzero t ht) := by simp [z, dif_pos ht]
    rw [h]
    exact (Classical.choose_spec (hzero t ht)).1
  have hz_uniq : ∀ t (ht : t ∈ A) {y : ℝ}, y ∈ Set.Ioo (a t) (b t) → g y = 0 → y = z t := by
    intro t ht y hy hyg
    have h : z t = Classical.choose (hzero t ht) := by simp [z, dif_pos ht]
    rw [h]
    exact (Classical.choose_spec (hzero t ht)).2 y ⟨hy, hyg⟩
  -- the reduction modulo the period
  let Φ : ℝ → ℝ := fun t => z t - T * ((⌊z t / T⌋ : ℤ) : ℝ)
  have hΦ_Ico : ∀ t : ℝ, Φ t ∈ Set.Ico 0 T := by
    intro t
    have h1 : ((⌊z t / T⌋ : ℤ) : ℝ) ≤ z t / T := Int.floor_le _
    have h2 : z t / T < ((⌊z t / T⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    have hTne : T ≠ 0 := ne_of_gt hT
    have h3 : T * ((⌊z t / T⌋ : ℤ) : ℝ) ≤ z t := by
      have h := mul_le_mul_of_nonneg_left h1 (le_of_lt hT)
      rwa [mul_div_cancel₀ _ hTne] at h
    have h4 : z t < T * ((⌊z t / T⌋ : ℤ) : ℝ) + T := by
      have h := mul_lt_mul_of_pos_left h2 hT
      have hh : T * (((⌊z t / T⌋ : ℤ) : ℝ) + 1) = T * ((⌊z t / T⌋ : ℤ) : ℝ) + T := by ring
      rwa [hh, mul_div_cancel₀ _ hTne] at h
    exact ⟨by simp only [Φ]; linarith, by simp only [Φ]; linarith⟩
  have hΦ_mem : ∀ t ∈ A, Φ t ∈ A ∧ g (Φ t) = 0 := by
    intro t ht
    obtain ⟨hzm, hzg⟩ := hz_spec t ht
    have hztA : z t ∈ A := hsub t ht hzm
    have hrepr : Φ t = z t + ((-(⌊z t / T⌋) : ℤ) : ℝ) * T := by
      simp only [Φ, Int.cast_neg]
      ring
    constructor
    · rw [hrepr]
      exact (hA_int (z t) (-(⌊z t / T⌋))).mpr hztA
    · rw [hrepr, hg_int (z t) (-(⌊z t / T⌋))]
      exact hzg
  -- components with a common point coincide
  have hoverlap : ∀ {t₁ t₂ : ℝ}, t₁ ∈ A → t₂ ∈ A →
      (Set.Ioo (a t₁) (b t₁) ∩ Set.Ioo (a t₂) (b t₂)).Nonempty →
      Set.Ioo (a t₁) (b t₁) = Set.Ioo (a t₂) (b t₂) := by
    intro t₁ t₂ ht₁ ht₂ hne'
    obtain ⟨x, hx₁, hx₂⟩ := hne'
    have hae : a t₁ = a t₂ := by
      by_contra hne''
      rcases lt_or_gt_of_ne hne'' with hlt | hlt
      · exact ha_nA t₂ ht₂ (hsub t₁ ht₁ ⟨hlt, lt_trans hx₂.1 hx₁.2⟩)
      · exact ha_nA t₁ ht₁ (hsub t₂ ht₂ ⟨hlt, lt_trans hx₁.1 hx₂.2⟩)
    have hbe : b t₁ = b t₂ := by
      by_contra hne''
      rcases lt_or_gt_of_ne hne'' with hlt | hlt
      · exact hb_nA t₁ ht₁ (hsub t₂ ht₂ ⟨lt_trans hx₂.1 hx₁.2, hlt⟩)
      · exact hb_nA t₂ ht₂ (hsub t₁ ht₁ ⟨lt_trans hx₁.1 hx₂.2, hlt⟩)
    rw [hae, hbe]
  have hinj_φ_of : ∀ t ∈ A, Set.InjOn φ (Set.Ioo (a t) (b t)) := fun t ht =>
    intervalZeros.injOn_of_deriv_ne_zero (hab_lt t ht) (fun x hx => hφd x (hsub t ht hx))
  -- the contradiction step
  have step : ∀ (r s : ℝ) (n : ℕ), r ∈ Set.Ico 0 T → s ∈ Set.Ico 0 T → r ∈ A → s ∈ A →
      φ r = 0 → φ s = 0 → 1 ≤ n → z s = z r + n * T → False := by
    intro r s n hrIco hsIco hrA hsA hrφ hsφ hn1 hzs
    have huA : r + n * T ∈ A := (hA_nat r n).mpr hrA
    have htr := hadd r n
    have hmem : z s ∈ Set.Ioo (a (r + n * T)) (b (r + n * T)) := by
      rw [htr.1, htr.2, hzs]
      obtain ⟨hzr, _⟩ := hz_spec r hrA
      exact ⟨by linarith [hzr.1], by linarith [hzr.2]⟩
    have hIoo := hoverlap huA hsA ⟨z s, hmem, (hz_spec s hsA).1⟩
    have hs_mem : s ∈ Set.Ioo (a s) (b s) := ht_Ioo s hsA
    have hu_mem : r + n * T ∈ Set.Ioo (a s) (b s) := by
      rw [← hIoo]; exact ht_Ioo (r + n * T) huA
    have hφu : φ (r + n * T) = 0 := by rw [hφ_nat r n]; exact hrφ
    have hsu : s = r + n * T := (hinj_φ_of s hsA) hs_mem hu_mem (by rw [hφu, hsφ])
    have hTle : T ≤ r + n * T := by
      have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      have h0 : (0 : ℝ) ≤ r := hrIco.1
      nlinarith [hT, hn, h0, mul_nonneg (le_of_lt hT) h0]
    linarith [hsIco.2, hTle, hsu]
  refine Set.encard_le_encard_of_injOn (f := Φ)
    (s := {t : ℝ | t ∈ Set.Ico 0 T ∧ t ∈ A ∧ φ t = 0})
    (t := {t : ℝ | t ∈ Set.Ico 0 T ∧ t ∈ A ∧ g t = 0}) ?_ ?_
  · intro t ht
    exact ⟨hΦ_Ico t, (hΦ_mem t ht.2.1).1, (hΦ_mem t ht.2.1).2⟩
  · intro t₁ ht₁ t₂ ht₂ hΦeq
    obtain ⟨ht₁Ico, ht₁A, ht₁φ⟩ := ht₁
    obtain ⟨ht₂Ico, ht₂A, ht₂φ⟩ := ht₂
    set m₁ : ℤ := ⌊z t₁ / T⌋ with hm₁
    set m₂ : ℤ := ⌊z t₂ / T⌋ with hm₂
    have hΦeq' : z t₁ - T * ((m₁ : ℤ) : ℝ) = z t₂ - T * ((m₂ : ℤ) : ℝ) := by
      simpa only [Φ, ← hm₁, ← hm₂] using hΦeq
    have hkey : z t₁ = z t₂ + ((m₁ - m₂ : ℤ) : ℝ) * T := by
      have hcast : (((m₁ - m₂ : ℤ)) : ℝ) = (m₁ : ℝ) - (m₂ : ℝ) := by simp
      rw [hcast]
      linarith
    rcases lt_trichotomy m₁ m₂ with hlt | heq | hgt
    · -- `m₁ < m₂`
      set k : ℤ := m₂ - m₁ with hk
      have hk1 : 1 ≤ k := by rw [hk]; omega
      have hknn : 0 ≤ k := by omega
      set n : ℕ := k.toNat with hn
      have hkn : (n : ℤ) = k := by rw [hn]; exact Int.toNat_of_nonneg hknn
      have hn1 : 1 ≤ n := by omega
      have hzs : z t₂ = z t₁ + (n : ℝ) * T := by
        have hk' : ((m₁ - m₂ : ℤ) : ℝ) = -(k : ℝ) := by rw [hk]; push_cast; ring
        have hnk : (n : ℝ) = (k : ℝ) := by exact_mod_cast hkn
        rw [hk', ← hnk] at hkey
        linarith
      exact (step t₁ t₂ n ht₁Ico ht₂Ico ht₁A ht₂A ht₁φ ht₂φ hn1 hzs).elim
    · -- `m₁ = m₂`
      have hz_eq : z t₁ = z t₂ := by rw [heq] at hkey; simpa using hkey
      have hmem₂ : z t₁ ∈ Set.Ioo (a t₂) (b t₂) := by
        rw [hz_eq]; exact (hz_spec t₂ ht₂A).1
      have hIoo := hoverlap ht₁A ht₂A ⟨z t₁, (hz_spec t₁ ht₁A).1, hmem₂⟩
      have h₁ : t₁ ∈ Set.Ioo (a t₂) (b t₂) := by rw [← hIoo]; exact ht_Ioo t₁ ht₁A
      have h₂ : t₂ ∈ Set.Ioo (a t₂) (b t₂) := ht_Ioo t₂ ht₂A
      exact (hinj_φ_of t₂ ht₂A) h₁ h₂ (by rw [ht₁φ, ht₂φ])
    · -- `m₂ < m₁`
      set k : ℤ := m₁ - m₂ with hk
      have hk1 : 1 ≤ k := by rw [hk]; omega
      have hknn : 0 ≤ k := by omega
      set n : ℕ := k.toNat with hn
      have hkn : (n : ℤ) = k := by rw [hn]; exact Int.toNat_of_nonneg hknn
      have hn1 : 1 ≤ n := by omega
      have hzs : z t₁ = z t₂ + (n : ℝ) * T := by
        have hnk : (n : ℝ) = (k : ℝ) := by exact_mod_cast hkn
        rw [← hnk] at hkey
        exact hkey
      exact (step t₂ t₁ n ht₂Ico ht₁Ico ht₂A ht₁A ht₂φ ht₁φ hn1 hzs).elim

end

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set in
open scoped ENNReal Topology in
theorem encard_tiltedCrossings_le_flat
    (K : Knot) {s u ε₀ : ℝ} (hε₀ : 0 < ε₀) {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3} {B : ℕ}
    (hB : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧ (K.curve t) (σ 2) = c (σ 2) + u} ≤ B)
    (hclose : ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
        |inner ℝ v (K.curve t) - (inner ℝ v c + u) - ((K.curve t) (σ 2) - (c (σ 2) + u))| < ε₀)
    (hnoflatcrit : ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
        deriv (fun r : ℝ => (K.curve r) (σ 2)) t = 0 →
        ε₀ ≤ |(K.curve t) (σ 2) - (c (σ 2) + u)|)
    (hboxsph : ∀ t : ℝ, Submission.boxNorm c σ (K.curve t) = s →
        ε₀ ≤ |(K.curve t) (σ 2) - (c (σ 2) + u)|)
    (htiltmono : ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
        |(K.curve t) (σ 2) - (c (σ 2) + u)| < ε₀ →
        deriv (fun r : ℝ => inner ℝ v (K.curve r)) t ≠ 0) :
    Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧ inner ℝ v (K.curve t) = inner ℝ v c + u} ≤ B := by
  set g : ℝ → ℝ := fun t => (K.curve t) (σ 2) - (c (σ 2) + u) with hgdef
  set φ : ℝ → ℝ := fun t => inner ℝ v (K.curve t) - (inner ℝ v c + u) with hφdef
  set A : Set ℝ := {t : ℝ | K.curve t ∈ Submission.PBox s c σ ∧ |g t| < ε₀} with hAdef
  have hKc : Continuous K.curve := K.smooth.continuous
  have hgd_eq : ∀ t : ℝ, deriv g t = deriv (fun r : ℝ => (K.curve r) (σ 2)) t := by
    intro t; rw [hgdef]; exact deriv_sub_const _
  have hφd_eq : ∀ t : ℝ, deriv φ t = deriv (fun r : ℝ => inner ℝ v (K.curve r)) t := by
    intro t; rw [hφdef]; exact deriv_sub_const _
  have hgcont : Continuous g := by
    rw [hgdef]
    exact ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (σ 2)).comp hKc).sub continuous_const
  have hφcont : Continuous φ := by
    rw [hφdef]
    exact (continuous_const.inner hKc).sub continuous_const
  have hgper : ∀ t : ℝ, g (t + 2 * Real.pi) = g t := by
    intro t; rw [hgdef]; simp [K.periodic t]
  have hφper : ∀ t : ℝ, φ (t + 2 * Real.pi) = φ t := by
    intro t; rw [hφdef]; simp [K.periodic t]
  have hAopen : IsOpen A := by
    rw [hAdef]
    exact ((_root_.Work.Topology.SphereSlicing.isOpen_PBox s c σ).preimage hKc).inter
      (isOpen_lt hgcont.abs continuous_const)
  have hAper : ∀ t : ℝ, t + 2 * Real.pi ∈ A ↔ t ∈ A := by
    intro t
    have hc : K.curve (t + 2 * Real.pi) = K.curve t := K.periodic t
    have hg' : g (t + 2 * Real.pi) = g t := hgper t
    rw [hAdef]
    simp only [Set.mem_setOf_eq]
    rw [hc, hg']
  have hgderiv_ne : ∀ t ∈ A, deriv g t ≠ 0 := by
    intro t ht
    rw [hAdef] at ht
    obtain ⟨hP, hlt⟩ := ht
    intro h0
    rw [hgd_eq t] at h0
    have h1 := hnoflatcrit t hP h0
    have hsame : |g t| = |(K.curve t) (σ 2) - (c (σ 2) + u)| := by rw [hgdef]
    linarith
  have hAne : (Aᶜ).Nonempty := by
    by_contra hcon
    rw [nonempty_iff_ne_empty, not_not] at hcon
    have huniv : ∀ t : ℝ, t ∈ A := by
      intro t
      by_contra ht
      have : t ∈ Aᶜ := ht
      rw [hcon] at this
      exact this
    have hderiv : ∀ t : ℝ, deriv g t ≠ 0 := fun t => hgderiv_ne t (huniv t)
    have hdiff : DifferentiableOn ℝ g (Set.Ioo 0 (2 * Real.pi)) := fun x hx =>
      (differentiableAt_of_deriv_ne_zero (hderiv x)).differentiableWithinAt
    have hper : g (2 * Real.pi) = g 0 := by
      have h := hgper 0
      simpa using h
    obtain ⟨x, hx, hxd⟩ := exists_deriv_eq_slope g (by positivity : (0 : ℝ) < 2 * Real.pi)
      hgcont.continuousOn hdiff
    rw [hper, sub_self, zero_div] at hxd
    exact hderiv x hxd
  have hφderiv_ne : ∀ t ∈ A, deriv φ t ≠ 0 := by
    intro t ht
    rw [hAdef] at ht
    obtain ⟨hP, hlt⟩ := ht
    rw [hφd_eq t]
    refine htiltmono t hP ?_
    rwa [hgdef] at hlt
  have hAε : ∀ t ∈ A, |g t| < ε₀ := by
    intro t ht; rw [hAdef] at ht; exact ht.2
  have hclbox : closure A ⊆ {t : ℝ | Submission.boxNorm c σ (K.curve t) ≤ s} := by
    refine closure_minimal (fun t ht => ?_) ?_
    · rw [hAdef] at ht
      exact le_of_lt ((Submission.mem_PBox_iff s c σ (K.curve t)).mp ht.1)
    · exact isClosed_le ((_root_.Work.Topology.SphereSlicing.boxNorm_continuous c σ).comp hKc)
        continuous_const
  have hbd : ∀ t ∈ closure A \ A, ε₀ ≤ |g t| := by
    intro t ht
    obtain ⟨hcl, hnA⟩ := ht
    have hbox := hclbox hcl
    rw [hAdef] at hnA
    by_cases hbs : Submission.boxNorm c σ (K.curve t) = s
    · exact hboxsph t hbs
    · have hlt : Submission.boxNorm c σ (K.curve t) < s := lt_of_le_of_ne hbox hbs
      have hnot : ¬ |g t| < ε₀ := fun h =>
        hnA ⟨(Submission.mem_PBox_iff s c σ (K.curve t)).mpr hlt, h⟩
      linarith
  have hSh : {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
      K.curve t ∈ Submission.PBox s c σ ∧ inner ℝ v (K.curve t) = inner ℝ v c + u}
      = {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ t ∈ A ∧ φ t = 0} := by
    ext t
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, ?_, ?_⟩
      · rw [hAdef]
        refine ⟨h2, ?_⟩
        have h0 : inner ℝ v (K.curve t) - (inner ℝ v c + u) = 0 := sub_eq_zero.mpr h3
        have hsame : |g t| =
            |inner ℝ v (K.curve t) - (inner ℝ v c + u) - ((K.curve t) (σ 2) - (c (σ 2) + u))| := by
          rw [hgdef, h0, zero_sub]
          simp only [abs_neg]
        rw [hsame]
        exact hclose t h2
      · rw [hφdef]; linarith
    · rintro ⟨h1, h2, h3⟩
      rw [hAdef] at h2
      have hφ0 : inner ℝ v (K.curve t) - (inner ℝ v c + u) = 0 := by
        rw [hφdef] at h3; exact h3
      exact ⟨h1, h2.1, by linarith⟩
  have hSg : {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
      K.curve t ∈ Submission.PBox s c σ ∧ (K.curve t) (σ 2) = c (σ 2) + u}
      = {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ t ∈ A ∧ g t = 0} := by
    ext t
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, ?_, ?_⟩
      · rw [hAdef]
        refine ⟨h2, ?_⟩
        have hg0 : g t = 0 := by rw [hgdef]; linarith
        rw [hg0]
        simpa using hε₀
      · rw [hgdef]; linarith
    · rintro ⟨h1, h2, h3⟩
      rw [hAdef] at h2
      have hg0 : (K.curve t) (σ 2) - (c (σ 2) + u) = 0 := by
        rw [hgdef] at h3; exact h3
      exact ⟨h1, h2.1, by linarith⟩
  have hT : (0 : ℝ) < 2 * Real.pi := by positivity
  have hmain := encard_zeroSet_le_of_periodic_open hT hε₀ hAopen hAper hAne
    hgcont hgper hφper hgderiv_ne hφderiv_ne hAε hbd
  rw [hSh]
  refine hmain.trans ?_
  rw [← hSg]
  exact hB

end Work.Drive.Mono
