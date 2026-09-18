import Submission.DS.Theorem1
import Mathlib.NumberTheory.WellApproximable

open scoped Nat ENNReal NNReal
open Set Filter MeasureTheory Metric
open DuffinSchaefferConjecture

/-!
# Per-denominator correspondence `[0,1] ↔ 𝕊` (bridge lemma)

For `x ∈ (0,1)` and radius `ψ(q)/q ≤ 1/2`, being within the interval-radius of a
reduced fraction `a/q` (numerator coprime, any `a`) is the same as the circle-class of
`x` lying within the same radius of the class of a reduced fraction `m/q` with
`0 ≤ m < q`.

The map is the quotient `(·) : ℝ → AddCircle (1 : ℝ)` (real numbers modulo the
integers).  Circle norm of a difference of classes equals the distance to the nearest
integer shift; use `AddCircle.norm_eq` with the rounding `round`.
-/

namespace Submission.DS

/-- Projection to the circle is 1-Lipschitz: the circle distance between two classes is
at most the distance between the two representatives. -/
lemma circcorr_norm_le_abs_sub (x y : ℝ) :
    ‖(x : AddCircle (1 : ℝ)) - (y : AddCircle (1 : ℝ))‖ ≤ |x - y| := by
  have h := @QuotientAddGroup.norm_mk_le_norm ℝ _ (AddSubgroup.zmultiples (1 : ℝ)) (x - y)
  simpa using h

/-- Two reals give equal classes on the circle `ℝ ⧸ ℤ` iff they differ by an integer. -/
lemma circcorr_coe_eq_coe_int (u v : ℝ) :
    (u : AddCircle (1 : ℝ)) = (v : AddCircle (1 : ℝ)) ↔ ∃ n : ℤ, u - v = (n : ℝ) := by
  rw [QuotientAddGroup.eq]
  rw [AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    have hn' : (n : ℝ) = -u + v := by simpa [zsmul_eq_mul] using hn
    push_cast
    linarith
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    rw [zsmul_eq_mul]
    push_cast
    linarith

/-- Fractions `a/q` and `m/q` have the same circle class whenever `a = m + q * k`,
i.e. `m` is the residue of `a` modulo `q`. -/
lemma circcorr_div_class_eq_of_add_mul (a m k q : ℕ) (hq : 0 < q) (hc : a = m + q * k) :
    ((a : ℝ) / (q : ℝ) : AddCircle (1 : ℝ)) = ((m : ℝ) / (q : ℝ) : AddCircle (1 : ℝ)) := by
  rw [circcorr_coe_eq_coe_int]
  refine ⟨(k : ℤ), ?_⟩
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hq
  have hcR : (a : ℝ) = (m : ℝ) + (q : ℝ) * (k : ℝ) := by
    have hc' := congrArg (fun t : ℕ => (t : ℝ)) hc
    simpa [Nat.cast_add, Nat.cast_mul] using hc'
  rw [hcR]
  field_simp [hq0]
  ring_nf
  norm_cast

/-- The residue of a number coprime to `q` is again coprime to `q`. -/
lemma circcorr_coprime_mod {a q : ℕ} (_hq : 0 < q) (hcop : Nat.Coprime a q) :
    Nat.Coprime (a % q) q := by
  have hg : a.gcd q = (a % q).gcd q := by
    calc a.gcd q = q.gcd a := by rw [Nat.gcd_comm]
      _ = (a % q).gcd q := by rw [Nat.gcd_rec]
  unfold Nat.Coprime at hcop ⊢
  rwa [← hg]

/-- `Coprime (m + q) q` follows from `Coprime m q`. -/
lemma circcorr_coprime_add {m q : ℕ} (hcop : Nat.Coprime m q) : Nat.Coprime (m + q) q := by
  have h1 : Nat.Coprime (q + m) q := (Nat.coprime_self_add_left (m := q) (n := m)).mpr hcop
  simpa [Nat.add_comm] using h1

/-- `Coprime (q - m) q` follows from `Coprime m q` when `m < q`. -/
lemma circcorr_coprime_sub {m q : ℕ} (_hq : 0 < q) (hmq : m < q) (hcop : Nat.Coprime m q) :
    Nat.Coprime (q - m) q := by
  have hle : m ≤ q := le_of_lt hmq
  have h1 : Nat.Coprime q (q - m) := by
    exact (Nat.coprime_self_sub_right (m := m) (n := q) hle).mpr (Nat.coprime_comm.mp hcop)
  exact Nat.coprime_comm.mp h1

/-- A small circle-norm inequality gives the distance to the rounded representative. -/
lemma circcorr_abs_sub_round_of_norm_le (t : ℝ) {r : ℝ}
    (h : ‖(t : AddCircle (1 : ℝ))‖ ≤ r) : |t - (round t : ℝ)| ≤ r := by
  rw [AddCircle.norm_eq] at h
  simpa using h

/-- A point `x ∈ (0,1)` lies in `Acopr ψ q` iff its circle class is within radius
`ψ(q)/q` of the class of a reduced fraction `m/q` with `m < q`. -/
lemma mem_Acopr_iff_circle {ψ : ℕ+ → ℝ≥0} (q : ℕ+) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (hδ : (ψ q / q : NNReal) ≤ (1 / 2 : NNReal)) :
    x ∈ Acopr ψ q ↔
      ∃ m : ℕ, m < (q : ℕ) ∧ Nat.Coprime m (q : ℕ) ∧
        ‖((x : AddCircle (1 : ℝ)) - (((m : ℝ) / (q : ℝ)) : AddCircle (1 : ℝ)))‖ ≤
          ((ψ q / q : NNReal) : ℝ) := by
  classical
  let r : ℝ := ((ψ q / q : NNReal) : ℝ)
  have hr12 : r ≤ (1 / 2 : ℝ) := by
    have hδR : ((ψ q / q : NNReal) : ℝ) ≤ (((1 / 2 : NNReal) : ℝ)) := NNReal.coe_le_coe.mp hδ
    have hhalf : (((1 / 2 : NNReal) : ℝ)) = (1 / 2 : ℝ) := by norm_num [NNReal.coe_div]
    have h1 : ((ψ q / q : NNReal) : ℝ) ≤ (1 / 2 : ℝ) := by
      rw [← hhalf]
      exact hδR
    dsimp [r]
    exact h1
  have hq0 : 0 < (q : ℕ) := PNat.pos q
  have hq0R : 0 < (q : ℝ) := by exact_mod_cast hq0
  have hr0 : 0 ≤ r := by
    dsimp [r]
    positivity
  constructor
  · -- (→)
    intro hx
    rcases hx with ⟨a, hcopa, hineq⟩
    unfold inequality_1_7 at hineq
    let m : ℕ := a % (q : ℕ)
    have hmq : m < (q : ℕ) := by
      dsimp [m]
      exact Nat.mod_lt a hq0
    have hcopm : Nat.Coprime m (q : ℕ) := by
      dsimp [m]
      exact circcorr_coprime_mod hq0 hcopa
    have hEqClass : ((a : ℝ) / (q : ℝ) : AddCircle (1 : ℝ)) =
        ((m : ℝ) / (q : ℝ) : AddCircle (1 : ℝ)) := by
      dsimp [m]
      have hc : a = a % (q : ℕ) + (q : ℕ) * (a / (q : ℕ)) := by
        exact (Nat.mod_add_div a (q : ℕ)).symm
      exact circcorr_div_class_eq_of_add_mul a (a % (q : ℕ)) (a / (q : ℕ)) (q : ℕ) hq0 hc
    have hnorm : ‖((x : AddCircle (1 : ℝ)) - (((a : ℝ) / (q : ℝ)) : AddCircle (1 : ℝ)))‖ ≤ r := by
      have hle : ‖((x : AddCircle (1 : ℝ)) - (((a : ℝ) / (q : ℝ)) : AddCircle (1 : ℝ)))‖ ≤
          |x - (a : ℝ) / (q : ℝ)| := circcorr_norm_le_abs_sub x ((a : ℝ) / (q : ℝ))
      refine le_trans hle ?_
      simpa [r] using hineq
    refine ⟨m, hmq, hcopm, ?_⟩
    rwa [hEqClass] at hnorm
  · -- (←)
    rintro ⟨m, hmq, hcopm, hcirc⟩
    have hmqR : (m : ℝ) / (q : ℝ) < 1 := by
      exact (div_lt_one hq0R).mpr (by exact_mod_cast hmq)
    have hmq0R : 0 ≤ (m : ℝ) / (q : ℝ) := by positivity
    let t : ℝ := x - (m : ℝ) / (q : ℝ)
    have ht1 : t < 1 := by
      dsimp [t]
      linarith
    have ht2 : -1 < t := by
      dsimp [t]
      linarith
    have h' : ‖(t : AddCircle (1 : ℝ))‖ ≤ r := by
      dsimp [t]
      rw [← AddCircle.coe_sub] at hcirc
      exact hcirc
    have hk0 : |t - (round t : ℝ)| ≤ r := circcorr_abs_sub_round_of_norm_le t h'
    have hex : ∃ k : ℤ, |t - (k : ℝ)| ≤ r := ⟨round t, hk0⟩
    rcases hex with ⟨k, hk⟩
    have hk_abs := abs_le.mp hk
    have hk_upper : (k : ℝ) ≤ t + r := by linarith [hk_abs.2]
    have hk_lower : t - r ≤ (k : ℝ) := by linarith [hk_abs.1]
    have hk_lt2 : (k : ℝ) < 2 := by
      have : t + r < (2 : ℝ) := by nlinarith
      linarith
    have hk_gt2 : -2 < (k : ℝ) := by
      have : -2 < t - r := by nlinarith
      linarith
    have hk_lt2i : k < 2 := by exact_mod_cast hk_lt2
    have hk_gt2i : -2 < k := by exact_mod_cast hk_gt2
    have hkcases : k = -1 ∨ k = 0 ∨ k = 1 := by omega
    rcases hkcases with rfl | rfl | rfl
    · -- k = -1: use a = q - m
      have hkneg : |t - ((-1 : ℤ) : ℝ)| ≤ r := hk
      have hpos : 0 ≤ t + 1 := by nlinarith [ht2]
      have hlin : t + 1 ≤ r := by
        have hkm1 : |t + 1| ≤ r := by
          norm_num at hkneg
          simpa using hkneg
        rwa [abs_of_nonneg hpos] at hkm1
      have hsum : x + (1 - (m : ℝ) / (q : ℝ)) ≤ r := by
        dsimp [t] at hlin
        have hEq : x + (1 - (m : ℝ) / (q : ℝ)) = (x - (m : ℝ) / (q : ℝ)) + 1 := by ring
        rw [hEq]
        exact hlin
      have hx0le : 0 ≤ x := le_of_lt hx0
      have hmq1le : 0 ≤ 1 - (m : ℝ) / (q : ℝ) := by linarith [hmqR]
      have htri : |x - (1 - (m : ℝ) / (q : ℝ))| ≤ x + (1 - (m : ℝ) / (q : ℝ)) := by
        rw [abs_le]
        constructor <;> nlinarith
      let a : ℕ := (q : ℕ) - m
      have haq : ((a : ℝ) / (q : ℝ)) = 1 - (m : ℝ) / (q : ℝ) := by
        dsimp [a]
        have hle : m ≤ (q : ℕ) := le_of_lt hmq
        have h1 : (((q : ℕ) - m : ℕ) : ℝ) = (((q : ℕ) : ℝ) - (m : ℝ)) := Nat.cast_sub hle
        have hcast : (((q : ℕ) - m : ℕ) : ℝ) = (q : ℝ) - (m : ℝ) := by
          simpa using h1
        field_simp [hq0R.ne']
        rw [hcast]
      have hmain : |x - (a : ℝ) / (q : ℝ)| ≤ r := by
        rw [haq]
        exact le_trans htri hsum
      have hcopa : Nat.Coprime a (q : ℕ) := by
        dsimp [a]
        exact circcorr_coprime_sub hq0 hmq hcopm
      change ∃ a : ℕ, Nat.Coprime a (q : ℕ) ∧ inequality_1_7 ψ x a q
      refine ⟨a, hcopa, ?_⟩
      unfold inequality_1_7
      simpa [r] using hmain
    · -- k = 0: a = m
      have hmain : |x - (m : ℝ) / (q : ℝ)| ≤ r := by
        dsimp [t] at hk
        simpa using hk
      change ∃ a : ℕ, Nat.Coprime a (q : ℕ) ∧ inequality_1_7 ψ x a q
      refine ⟨m, hcopm, ?_⟩
      unfold inequality_1_7
      simpa [r] using hmain
    · -- k = 1: a = m + q
      let a : ℕ := m + (q : ℕ)
      have haq : ((a : ℝ) / (q : ℝ)) = (m : ℝ) / (q : ℝ) + 1 := by
        dsimp [a]
        have hcast : ((m + (q : ℕ) : ℕ) : ℝ) = (m : ℝ) + (q : ℝ) := by
          norm_num [Nat.cast_add]
        field_simp [hq0R.ne']
        rw [hcast]
      have hmain : |x - (a : ℝ) / (q : ℝ)| ≤ r := by
        rw [haq]
        have hEq : x - ((m : ℝ) / (q : ℝ) + 1) = x - (m : ℝ) / (q : ℝ) - 1 := by ring
        rw [hEq]
        dsimp [t] at hk
        simpa using hk
      have hcopa : Nat.Coprime a (q : ℕ) := by
        dsimp [a]
        exact circcorr_coprime_add hcopm
      change ∃ a : ℕ, Nat.Coprime a (q : ℕ) ∧ inequality_1_7 ψ x a q
      refine ⟨a, hcopa, ?_⟩
      unfold inequality_1_7
      simpa [r] using hmain

end Submission.DS
