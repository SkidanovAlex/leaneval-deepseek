import Mathlib
import Submission.Work.Mostow.gapA.defs
import Submission.Work.Mostow.pairStabDefs

/-!
# The geodesic `geodSet a b` is the set of points whose lift spans the two null vectors

`geodSet a b` is the equality locus in the reverse Cauchy–Schwarz inequality for the two null
vectors `nvec a = (a,1)`, `nvec b = (b,1)`:

`geodSet a b = {u | exp (β_a u + β_b u) = (1 - ⟪a,b⟫)/2}`

(`levMulGe` shows that the right-hand side is always `≤ 2 lev a u lev b u`).  This file proves
that this locus is exactly the set of points `u : E n` whose hyperboloid lift lies in the linear
span of `nvec a` and `nvec b`, i.e. the geodesic with endpoints `a` and `b` in the hyperboloid
model.

## Proof

Write `θ_ξ = nvec ξ` and `⟨x,y⟩ = mform x y` for the Minkowski form.  For `ξ ∈ Sph n` the vector
`θ_ξ` is null and `⟨hlift u, θ_ξ⟩ = -lev ξ u`, so with `p = lev a u`, `q = lev b u` and
`c = 1 - ⟪a,b⟫ = -⟨θ_a,θ_b⟩` the hypothesis `exp (β_a u + β_b u) = c/2` reads `p q = c/2`.

* (⇐) If `hlift u = α θ_a + β θ_b`, then `p = β c`, `q = α c` and
  `-1 = ⟨hlift u, hlift u⟩ = -2 α β c`, so `p q = α β c² = c/2`.
* (⇒) Put `y = hlift u - (q/c) θ_a - (p/c) θ_b`.  A direct expansion gives `y ⊥ θ_a`, `y ⊥ θ_b`
  and `⟨y,y⟩ = -1 + 2 p q / c = 0`.  Since `y` is orthogonal to `hlift (pairPoint a b)`
  (`hlift_pairPoint`: `pairPoint a b` is the midpoint of the geodesic, of lift
  `(2c)^{-1/2}(θ_a + θ_b)`), the reverse Cauchy–Schwarz argument
  (`mform_self_eq_zero_of_orth_hlift`: the orthogonal complement of a timelike vector is positive
  definite) forces `y = 0`.
-/

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-! ## Elementary pairings of the null vectors `nvec ξ = (ξ,1)` -/

/-- The Minkowski pairing of the null vector of `ξ` with the lift of `u`. -/
lemma mform_hlift_nvec (u ξ : E n) :
    mform (hlift u) (nvec ξ) = inner ℝ u ξ - tpart u :=
  mform_hlift_theta' ξ u

/-- The Minkowski pairing of two null vectors. -/
lemma mform_nvec_nvec (ξ η : E n) : mform (nvec ξ) (nvec η) = inner ℝ ξ η - 1 :=
  mform_theta_theta_pair ξ η

/-- The null vector of a boundary point is null. -/
lemma mform_nvec_self {ξ : E n} (hξ : ξ ∈ Sph n) : mform (nvec ξ) (nvec ξ) = 0 :=
  mform_theta_theta_sph ξ hξ

/-- `exp (busemann ξ u) = -⟨hlift u, nvec ξ⟩`. -/
lemma exp_busemann_eq_neg_mform_nvec (ξ : E n) (hξ : ξ ∈ Sph n) (u : E n) :
    Real.exp (busemann ξ u) = - mform (hlift u) (nvec ξ) :=
  exp_busemann_eq_neg_mform ξ hξ u

/-! ## Two expansions of the Minkowski form -/

/-- Expansion of the square of `x - r • A - s • B`. -/
lemma mform_decomp (x A B : Fin n ⊕ Fin 1 → ℝ) (r s : ℝ) :
    mform (x - r • A - s • B) (x - r • A - s • B)
      = mform x x - 2 * r * mform x A - 2 * s * mform x B
        + r ^ 2 * mform A A + s ^ 2 * mform B B + 2 * r * s * mform A B := by
  simp only [mform_sub_left, mform_sub_right, mform_smul_left, mform_smul_right,
    mform_comm (y := x), mform_comm B A]
  ring

/-- Pairing of `x - r • A - s • B` with `A`. -/
lemma mform_decomp_left (x A B : Fin n ⊕ Fin 1 → ℝ) (r s : ℝ) :
    mform (x - r • A - s • B) A = mform x A - r * mform A A - s * mform B A := by
  simp only [mform_sub_left, mform_smul_left]

/-- Pairing of `x - r • A - s • B` with `B`. -/
lemma mform_decomp_left' (x A B : Fin n ⊕ Fin 1 → ℝ) (r s : ℝ) :
    mform (x - r • A - s • B) B = mform x B - r * mform A B - s * mform B B := by
  simp only [mform_sub_left, mform_smul_left]

/-- A Minkowski-null vector orthogonal to the lift of a point of `ℍⁿ` vanishes. -/
lemma mform_self_eq_zero_of_orth_hlift (v : E n) (y : Fin n ⊕ Fin 1 → ℝ)
    (horth : mform y (hlift v) = 0) (hself : mform y y = 0) : y = 0 := by
  have h1 : inner ℝ (hspat y) v = htime y * tpart v := by
    have h := horth
    rw [mform_eq] at h
    simpa using sub_eq_zero.mp h
  have h2 : ‖hspat y‖ ^ 2 = (htime y) ^ 2 := by
    have h := hself
    rw [mform_eq, real_inner_self_eq_norm_sq] at h
    nlinarith [h]
  have hcs : (inner ℝ (hspat y) v) ^ 2 ≤ ‖hspat y‖ ^ 2 * ‖v‖ ^ 2 := by
    have h := real_inner_mul_inner_self_le (hspat y) v
    rw [← pow_two, real_inner_self_eq_norm_sq (hspat y), real_inner_self_eq_norm_sq v] at h
    exact h
  have ht0 : htime y = 0 := by
    rw [h1, mul_pow, h2, tpart_sq] at hcs
    have : (htime y) ^ 2 ≤ 0 := by nlinarith [hcs]
    have h3 : (htime y) ^ 2 = 0 := le_antisymm this (sq_nonneg _)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3
  have hsp0 : hspat y = 0 := by
    have h3 : ‖hspat y‖ ^ 2 = 0 := by rw [h2, ht0]; ring
    exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3)
  funext z
  rcases z with i | j
  · have hh := congrArg (fun w : E n => w i) hsp0
    simpa [hspat] using hh
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    simpa [htime] using ht0

/-! ## The main statement -/

theorem mem_geodSet_iff_span {n : ℕ} (a b : Submission.Mostow.E n) (ha : a ∈ Submission.Mostow.Sph n)
    (hb : b ∈ Submission.Mostow.Sph n) (hab : a ≠ b) (u : Submission.Mostow.E n) :
    u ∈ Work.Mostow.geodSet a b ↔
      ∃ α β : ℝ, Submission.Mostow.hlift u = α • Work.Mostow.nvec a + β • Work.Mostow.nvec b := by
  have hinner : inner ℝ a b < 1 :=
    inner_lt_one_of_ne_unit ((mem_Sph_iff a).1 ha) ((mem_Sph_iff b).1 hb) hab
  set c : ℝ := 1 - inner ℝ a b with hcdef
  have hcpos : 0 < c := by rw [hcdef]; linarith
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have hAA : mform (nvec a) (nvec a) = 0 := mform_nvec_self ha
  have hBB : mform (nvec b) (nvec b) = 0 := mform_nvec_self hb
  have hAB : mform (nvec a) (nvec b) = -c := by rw [mform_nvec_nvec, hcdef]; ring
  have hBA : mform (nvec b) (nvec a) = -c := by rw [mform_comm, hAB]
  have hxx : mform (hlift u) (hlift u) = -1 := mform_hlift_self u
  have hexpA : Real.exp (busemann a u) = -mform (hlift u) (nvec a) :=
    exp_busemann_eq_neg_mform_nvec a ha u
  have hexpB : Real.exp (busemann b u) = -mform (hlift u) (nvec b) :=
    exp_busemann_eq_neg_mform_nvec b hb u
  constructor
  · intro hgeo
    set p : ℝ := -mform (hlift u) (nvec a) with hpdef
    set q : ℝ := -mform (hlift u) (nvec b) with hqdef
    have hpq : p * q = c / 2 := by
      have hgeo' : Real.exp (busemann a u + busemann b u) = (1 - inner ℝ a b) / 2 := hgeo
      have h : Real.exp (busemann a u + busemann b u) = p * q := by
        rw [Real.exp_add, hexpA, hexpB, hpdef, hqdef]
      rw [h, ← hcdef] at hgeo'
      exact hgeo'
    refine ⟨q / c, p / c, ?_⟩
    set y : Fin n ⊕ Fin 1 → ℝ := hlift u - (q / c) • nvec a - (p / c) • nvec b with hydef
    have hyA : mform y (nvec a) = 0 := by
      rw [hydef, mform_decomp_left, hAA, hBA, hpdef, hqdef]
      field_simp
      ring
    have hyB : mform y (nvec b) = 0 := by
      rw [hydef, mform_decomp_left', hAB, hBB, hpdef, hqdef]
      field_simp
      ring
    have hyy : mform y y = 0 := by
      have hpq' : mform (hlift u) (nvec a) * mform (hlift u) (nvec b) = c / 2 := by
        have h := hpq
        rw [hpdef, hqdef] at h
        linarith [h]
      rw [hydef, mform_decomp, hxx, hAA, hBB, hAB, hpdef, hqdef]
      field_simp
      nlinarith [hpq']
    have hyAθ : mform y (theta a) = 0 := hyA
    have hyBθ : mform y (theta b) = 0 := hyB
    have hyp : mform y (hlift (pairPoint a b)) = 0 := by
      rw [hlift_pairPoint a b ha hb hab, mform_smul_right, mform_add_right, hyAθ, hyBθ,
        add_zero, mul_zero]
    have hy0 : y = 0 := mform_self_eq_zero_of_orth_hlift (pairPoint a b) y hyp hyy
    rw [hydef] at hy0
    have h1 : hlift u - (q / c) • nvec a = (p / c) • nvec b := by
      rw [sub_eq_zero] at hy0
      exact hy0
    have key : hlift u = (p / c) • nvec b + (q / c) • nvec a := sub_eq_iff_eq_add.mp h1
    rw [key]
    abel
  · rintro ⟨α, β, hαβ⟩
    have hp : -mform (hlift u) (nvec a) = β * c := by
      rw [hαβ, mform_add_left, mform_smul_left, mform_smul_left, hAA, hBA]
      ring
    have hq : -mform (hlift u) (nvec b) = α * c := by
      rw [hαβ, mform_add_left, mform_smul_left, mform_smul_left, hAB, hBB]
      ring
    have hsc : α * β * c = 1 / 2 := by
      have h1 : mform (hlift u) (hlift u) = -1 := hxx
      rw [hαβ] at h1
      simp only [mform_add_left, mform_add_right, mform_smul_left, mform_smul_right,
        hAA, hBB, hAB, hBA] at h1
      nlinarith [h1]
    show Real.exp (busemann a u + busemann b u) = (1 - inner ℝ a b) / 2
    rw [Real.exp_add, hexpA, hexpB, hp, hq, ← hcdef]
    nlinarith [hsc]

end

end Work.Mostow.gapA
