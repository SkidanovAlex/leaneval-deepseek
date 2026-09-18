/-
# The Beresnevich–Velani layer: the Duffin–Schaeffer system and its `d`-scaled version

This file sets up the objects needed to run the mass transference principle on the
Duffin–Schaeffer system.

* `theta ψ d` is the rescaling `q ↦ q·(ψ(q)/q)^d`, whose Duffin–Schaeffer radii
  `theta(q)/q = (ψ(q)/q)^d` are the `d`-th powers of the radii of `ψ`;
* `Idx ψ d` is the (locally finite) set of coprime pairs `(a,q)` with
  `a ≤ q + theta(q)`, big enough to contain every solution of `|z - a/q| ≤ theta(q)/q`
  with `z ∈ [0,1]`;
* `A_eq_Icc_LS` identifies the challenge's set `𝒜 ψ` with the limsup of the intervals
  `B(a/q, ψ(q)/q)` over `Idx ψ d`.
-/

import Submission.Main.Transport

open scoped Nat ENNReal NNReal MeasureTheory Topology
open Set Filter MeasureTheory
open MeasureTheory.Measure
open DuffinSchaefferConjecture

namespace Submission.Main

/-- `θ(q) = q·(ψ(q)/q)^d`.  Its Duffin–Schaeffer radii `θ(q)/q = (ψ(q)/q)^d` are the
`d`-th powers of the radii `ψ(q)/q`. -/
noncomputable def theta (ψ : ℕ+ → ℝ≥0) (d : ℝ) : ℕ+ → ℝ≥0 :=
  fun q => q * ((ψ q / q : ℝ≥0) ^ d)

/-- The upper bound `q + θ(q)` for the numerators that can occur in `[0,1]`. -/
noncomputable def numBound (ψ : ℕ+ → ℝ≥0) (d : ℝ) (q : ℕ+) : ℝ :=
  (q : ℝ) + ((theta ψ d q : ℝ≥0) : ℝ)

/-- Truncated coprime pairs `(a,q)`: `gcd a q = 1` and `a ≤ q + θ(q)`. -/
abbrev Idx (ψ : ℕ+ → ℝ≥0) (d : ℝ) : Type :=
  {p : ℕ × ℕ+ // Nat.Coprime p.1 p.2 ∧ ((p.1 : ℕ) : ℝ) ≤ numBound ψ d p.2}

instance (ψ : ℕ+ → ℝ≥0) (d : ℝ) : Countable (Idx ψ d) := by
  unfold Idx
  infer_instance

/-- The centre `a/q` of the interval of the pair `(a,q)`. -/
noncomputable def ctrP (p : ℕ × ℕ+) : ℝ := (p.1 : ℝ) / (p.2 : ℝ)

/-- The radius `ψ(q)/q` attached to the pair `(a,q)`. -/
noncomputable def rrP (ψ : ℕ+ → ℝ≥0) (p : ℕ × ℕ+) : ℝ := (ψ p.2 : ℝ) / (p.2 : ℝ)

lemma rrP_nonneg (ψ : ℕ+ → ℝ≥0) (p : ℕ × ℕ+) : 0 ≤ rrP ψ p := by
  rw [rrP]
  positivity

/-- `rrP` is the NNReal quotient `ψ(q)/q` coerced to `ℝ`. -/
lemma rrP_eq_coe (ψ : ℕ+ → ℝ≥0) (p : ℕ × ℕ+) :
    rrP ψ p = ((ψ p.2 / p.2 : ℝ≥0) : ℝ) := by
  rw [rrP, NNReal.coe_div]
  norm_cast

/-- The radius of `θ` is the `d`-th power of the radius of `ψ`. -/
lemma rrP_theta (ψ : ℕ+ → ℝ≥0) (d : ℝ) (p : ℕ × ℕ+) :
    rrP (theta ψ d) p = (rrP ψ p) ^ d := by
  rw [rrP, rrP, theta]
  have hq : (p.2 : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (p.2 : ℝ) := by exact_mod_cast PNat.pos p.2
    exact ne_of_gt this
  rw [show (((p.2 : ℝ≥0) * ((ψ p.2 / (p.2 : ℝ≥0)) ^ d) : ℝ≥0) : ℝ)
        = (p.2 : ℝ) * (((ψ p.2 / (p.2 : ℝ≥0) : ℝ≥0)) : ℝ) ^ d by
    rw [NNReal.coe_mul, NNReal.coe_rpow]; norm_cast]
  rw [NNReal.coe_div] at *
  norm_cast
  field_simp

/-- Transfer of infinitude between a subtype and the corresponding set of pairs. -/
lemma infinite_subtype_iff {α : Type*} {P Q : α → Prop} :
    ({x : {a // P a} | Q x}.Infinite) ↔ ({x : α | P x ∧ Q x}.Infinite) := by
  have hval : Subtype.val '' {x : {a // P a} | Q x} = {x : α | P x ∧ Q x} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, hx⟩
    · rintro ⟨hy, hyQ⟩
      exact ⟨⟨y, hy⟩, hyQ, rfl⟩
  constructor
  · intro h
    have hinj : Set.InjOn (Subtype.val : {a // P a} → α) {x : {a // P a} | Q x} :=
      fun _ _ _ _ hxy => Subtype.val_injective hxy
    have h2 : (Subtype.val '' {x : {a // P a} | Q x}).Infinite := (Set.infinite_image_iff hinj).mpr h
    rwa [hval] at h2
  · intro h
    have h2 : (Subtype.val ⁻¹' {x : α | P x ∧ Q x}).Infinite :=
      h.preimage (by rintro y ⟨hy, -⟩; exact ⟨⟨y, hy⟩, rfl⟩)
    have h3 : Subtype.val ⁻¹' {x : α | P x ∧ Q x} = {x : {a // P a} | Q x} := by
      ext x
      exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
    rwa [h3] at h2

/-- `θ(q)/q = (ψ(q)/q)^d`. -/
lemma theta_radii (ψ : ℕ+ → ℝ≥0) (d : ℝ) (q : ℕ+) :
    ((theta ψ d q / q : ℝ≥0) : ℝ) = (rrP ψ (0, q)) ^ d := by
  rw [theta]
  have hq : (q : ℝ≥0) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast PNat.pos q)
  rw [mul_div_cancel_left₀ _ hq, NNReal.coe_rpow]
  rw [rrP, NNReal.coe_div]
  norm_cast

/-- A pair realising the inequality at level `q` with `z ≤ 1` has numerator at most
`q + q·r`. -/
lemma num_le_of_witness {z r : ℝ} (hz1 : z ≤ 1) (hr0 : 0 ≤ r) {q : ℕ+} {a : ℕ}
    (h : |z - (a : ℝ) / (q : ℝ)| ≤ r) : (a : ℝ) ≤ (q : ℝ) + (q : ℝ) * r := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast PNat.pos q
  rw [abs_le] at h
  have h1 : (a : ℝ) / (q : ℝ) ≤ z + r := by linarith [h.2]
  have h2 : (a : ℝ) ≤ (z + r) * (q : ℝ) := by
    have h3 : (a : ℝ) / (q : ℝ) * (q : ℝ) ≤ (z + r) * (q : ℝ) :=
      mul_le_mul_of_nonneg_right h1 (le_of_lt hq0)
    have h4 : (a : ℝ) / (q : ℝ) * (q : ℝ) = (a : ℝ) := by field_simp
    linarith [h3, h4.symm.le, h4.le]
  nlinarith [h2, hq0, hz1, hr0]

/-- A witness of the `θ`-inequality at `z ∈ [0,1]` belongs to the truncated index set. -/
lemma mem_numBound_of_theta_witness {ψ : ℕ+ → ℝ≥0} {d : ℝ} {z : ℝ} (hz1 : z ≤ 1)
    {p : ℕ × ℕ+} (h : |z - ctrP p| ≤ rrP (theta ψ d) p) :
    ((p.1 : ℕ) : ℝ) ≤ numBound ψ d p.2 := by
  have h' : |z - (p.1 : ℝ) / (p.2 : ℝ)| ≤ rrP (theta ψ d) p := h
  have hle := num_le_of_witness hz1 (rrP_nonneg _ _) h'
  have hkey : (p.2 : ℝ) * rrP (theta ψ d) p = ((theta ψ d p.2 : ℝ≥0) : ℝ) := by
    rw [rrP]
    have hq : (p.2 : ℝ) ≠ 0 := by
      have : (0 : ℝ) < (p.2 : ℝ) := by exact_mod_cast PNat.pos p.2
      exact ne_of_gt this
    field_simp
  rw [numBound, ← hkey]
  linarith

/-- The Duffin–Schaeffer inequality is the interval inequality with centre `a/q` and
radius `ψ(q)/q`. -/
lemma ineq_iff_abs (χ : ℕ+ → ℝ≥0) (z : ℝ) (p : ℕ × ℕ+) :
    inequality_1_7 χ z p.1 p.2 ↔ |z - ctrP p| ≤ rrP χ p := by
  rw [inequality_1_7, rrP_eq_coe, ctrP]
  rfl

/-- A witness of the `ψ`-inequality at `z ∈ [0,1]` belongs to the truncated index set,
provided `ψ(q) ≤ 1/2`. -/
lemma mem_numBound_of_psi_witness {ψ : ℕ+ → ℝ≥0} {d : ℝ} (hψ : ∀ q, ψ q ≤ 1/2)
    {z : ℝ} (hz1 : z ≤ 1) {p : ℕ × ℕ+} (h : |z - ctrP p| ≤ rrP ψ p) :
    ((p.1 : ℕ) : ℝ) ≤ numBound ψ d p.2 := by
  have hle := num_le_of_witness hz1 (rrP_nonneg _ _) h
  have hhalf : (p.2 : ℝ) * rrP ψ p ≤ 1 / 2 := by
    rw [rrP]
    have hq : (0 : ℝ) < (p.2 : ℝ) := by exact_mod_cast PNat.pos p.2
    have hψR : (ψ p.2 : ℝ) ≤ 1 / 2 := by exact_mod_cast hψ p.2
    field_simp
    nlinarith [hψR, hq]
  have hnum : (p.1 : ℝ) ≤ (p.2 : ℝ) + 1 / 2 := by linarith
  have hlt : (p.1 : ℝ) < (p.2 : ℝ) + 1 := by linarith
  have hnat : p.1 ≤ (p.2 : ℕ) := by
    have hlt' : (p.1 : ℕ) < (p.2 : ℕ) + 1 := by exact_mod_cast hlt
    exact Nat.lt_add_one_iff.mp hlt'
  have hθ0 : 0 ≤ ((theta ψ d p.2 : ℝ≥0) : ℝ) := by positivity
  rw [numBound]
  have : ((p.1 : ℕ) : ℝ) ≤ ((p.2 : ℕ) : ℝ) := by exact_mod_cast hnat
  linarith

/-- The unrestricted pair description of `𝒜`: the limsup over all coprime pairs. -/
theorem A_eq_Icc_pairs (χ : ℕ+ → ℝ≥0) :
    𝒜 χ = Set.Icc (0 : ℝ) 1 ∩
      {z : ℝ | {p : ℕ × ℕ+ | Nat.Coprime p.1 p.2 ∧ |z - ctrP p| ≤ rrP χ p}.Infinite} := by
  ext α
  constructor
  · intro hα
    obtain ⟨hα01, hαinf⟩ := hα
    refine ⟨hα01, ?_⟩
    refine hαinf.mono ?_
    rintro p ⟨hc, hi⟩
    exact ⟨hc, (ineq_iff_abs χ α p).mp hi⟩
  · rintro ⟨hα01, hαinf⟩
    refine ⟨hα01, ?_⟩
    refine hαinf.mono ?_
    rintro p ⟨hc, hi⟩
    exact ⟨hc, (ineq_iff_abs χ α p).mpr hi⟩

/-- `𝒜 ψ` is the limsup of the intervals over the truncated index set. -/
theorem A_eq_Icc_LS (ψ : ℕ+ → ℝ≥0) (d : ℝ) (hψ : ∀ q : ℕ+, ψ q ≤ 1 / 2) :
    𝒜 ψ = Set.Icc (0 : ℝ) 1 ∩
      {z : ℝ | {p : Idx ψ d | |z - ctrP p.1| ≤ rrP ψ p.1}.Infinite} := by
  rw [A_eq_Icc_pairs ψ]
  ext z
  constructor
  · rintro ⟨hz01, hzinf⟩
    refine ⟨hz01, ?_⟩
    refine (infinite_subtype_iff (P := fun p : ℕ × ℕ+ => Nat.Coprime p.1 p.2 ∧
        ((p.1 : ℕ) : ℝ) ≤ numBound ψ d p.2)
      (Q := fun p => |z - ctrP p| ≤ rrP ψ p)).mpr ?_
    refine hzinf.mono ?_
    rintro p ⟨hc, hi⟩
    exact ⟨⟨hc, mem_numBound_of_psi_witness hψ hz01.2 hi⟩, hi⟩
  · rintro ⟨hz01, hzinf⟩
    refine ⟨hz01, ?_⟩
    have hplain : ({p : ℕ × ℕ+ | (Nat.Coprime p.1 p.2 ∧
        ((p.1 : ℕ) : ℝ) ≤ numBound ψ d p.2) ∧ |z - ctrP p| ≤ rrP ψ p}).Infinite :=
      (infinite_subtype_iff (P := fun p : ℕ × ℕ+ => Nat.Coprime p.1 p.2 ∧
        ((p.1 : ℕ) : ℝ) ≤ numBound ψ d p.2)
        (Q := fun p => |z - ctrP p| ≤ rrP ψ p)).mp hzinf
    refine hplain.mono ?_
    rintro p ⟨⟨hc, -⟩, hi⟩
    exact ⟨hc, hi⟩

end Submission.Main
