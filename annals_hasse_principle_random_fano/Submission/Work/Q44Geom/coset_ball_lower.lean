import Mathlib
import Submission.Work.Q44Geom.vdc_lower
import Submission.Work.Q44Geom.Setup

/-!
# Lower bound for the number of lattice points of a coset in a ball

For a sublattice `N ⊆ ℤ^5` of rank `2`, a vector `z` and a radius `R ≥ 2‖z‖`, the number of
points of the coset `z + N` of norm at most `R` is bounded below by a positive constant times
`R^2 / (λ₁(N) λ₂(N))`.

The argument is elementary.  By `Work.HP.Q44Child.lam_attained` there are two independent
lattice vectors `f 0, f 1 ∈ N` with `‖f 0‖ ≤ λ₁(N)` and `‖f 1‖ ≤ λ₂(N)`.  For
`a ∈ {0, …, ⌊R/(4λ₁)⌋}` and `b ∈ {0, …, ⌊R/(4λ₂)⌋}` the point
`z + a·f 0 + b·f 1` lies in the coset (the difference with `z` is in `N`), has norm at most
`‖z‖ + R/4 + R/4 ≤ R`, and distinct pairs give distinct points because `f 0, f 1` are linearly
independent.  Hence the count is at least
`(⌊R/(4λ₁)⌋+1)(⌊R/(4λ₂)⌋+1) ≥ R/(4λ₁) · R/(4λ₂) = R^2/(16 λ₁λ₂)`.
-/

set_option autoImplicit false

noncomputable section

namespace Work.Q44Geom

/-- For a linearly independent pair `f 0, f 1` in a `ℤ`-module the coefficient map
`(a, b) ↦ a • f 0 + b • f 1` is injective. -/
private lemma pair_smul_inj {f : Fin 2 → (Fin 5 → ℤ)} (hf : LinearIndependent ℤ f)
    {a a' b b' : ℤ} (h : a • f 0 + b • f 1 = a' • f 0 + b' • f 1) : a = a' ∧ b = b' := by
  have hzero : (a - a') • f 0 + (b - b') • f 1 = 0 := by
    have h' : (a • f 0 + b • f 1) - (a' • f 0 + b' • f 1) = 0 := sub_eq_zero.mpr h
    have heq : (a • f 0 + b • f 1) - (a' • f 0 + b' • f 1)
        = (a - a') • f 0 + (b - b') • f 1 := by
      rw [sub_smul, sub_smul]; abel
    rwa [heq] at h'
  have hsum : (∑ i : Fin 2, (![a - a', b - b'] : Fin 2 → ℤ) i • f i) = 0 := by
    rw [Fin.sum_univ_two]
    simpa using hzero
  have hg := Fintype.linearIndependent_iff.mp hf (![a - a', b - b'] : Fin 2 → ℤ) hsum
  exact ⟨sub_eq_zero.mp (hg 0), sub_eq_zero.mp (hg 1)⟩

theorem coset_ball_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : Submodule ℤ (Fin 5 → ℤ)), Work.HP.rk N = 2 →
      ∀ (z : Fin 5 → ℤ) (R : ℝ), 1 ≤ Work.HP.eNorm z → 2 * Work.HP.eNorm z ≤ R →
      c * (R ^ 2 / (Work.HP.lam N 1 * Work.HP.lam N 2))
        ≤ (({v : Fin 5 → ℤ | v - z ∈ N ∧ Work.HP.eNorm v ≤ R} : Set (Fin 5 → ℤ)).ncard : ℝ) := by
  classical
  refine ⟨1 / 16, by norm_num, ?_⟩
  intro N hNrk z R hz1 hzR
  -- Two independent lattice vectors of `N` respecting the successive minima.
  obtain ⟨f, hfN, hfLI, hfb⟩ :=
    Work.HP.Q44Child.lam_attained N 2 (by norm_num) (by omega)
  have hlam1 : 0 < Work.HP.lam N 1 := Work.HP.lam_pos N (by norm_num) (by omega)
  have hlam2 : 0 < Work.HP.lam N 2 := Work.HP.lam_pos N (by norm_num) (by omega)
  have hRnn : 0 ≤ R := by have := Work.HP.eNorm_nonneg z; linarith
  set k1 : ℕ := ⌊R / (4 * Work.HP.lam N 1)⌋₊ with hk1
  set k2 : ℕ := ⌊R / (4 * Work.HP.lam N 2)⌋₊ with hk2
  -- The box of lattice points of the coset inside the ball.
  let Φ : (Fin (k1 + 1) × Fin (k2 + 1)) → (Fin 5 → ℤ) :=
    fun p => (((p.1 : ℕ) : ℤ)) • f 0 + (((p.2 : ℕ) : ℤ)) • f 1
  let Ψ : (Fin (k1 + 1) × Fin (k2 + 1)) → (Fin 5 → ℤ) := fun p => z + Φ p
  have hΦinj : Function.Injective Φ := by
    intro p q hpq
    obtain ⟨h0, h1⟩ := pair_smul_inj hfLI (h := hpq)
    exact Prod.ext (Fin.ext (Int.ofNat.inj h0)) (Fin.ext (Int.ofNat.inj h1))
  have hmem : ∀ p, Ψ p - z ∈ N := by
    intro p
    have h1 : Ψ p - z = Φ p := by simp [Ψ]
    rw [h1]
    change (((p.1 : ℕ) : ℤ)) • f 0 + (((p.2 : ℕ) : ℤ)) • f 1 ∈ N
    exact Submodule.add_mem N (Submodule.smul_mem N _ (hfN 0))
      (Submodule.smul_mem N _ (hfN 1))
  have hfloor1 : (k1 : ℝ) ≤ R / (4 * Work.HP.lam N 1) := by
    rw [hk1]
    exact Nat.floor_le (div_nonneg hRnn (by positivity))
  have hfloor2 : (k2 : ℝ) ≤ R / (4 * Work.HP.lam N 2) := by
    rw [hk2]
    exact Nat.floor_le (div_nonneg hRnn (by positivity))
  have hnorm : ∀ p, Work.HP.eNorm (Ψ p) ≤ R := by
    intro p
    have ha : (((p.1 : ℕ) : ℝ)) ≤ R / (4 * Work.HP.lam N 1) := by
      have hp : (p.1 : ℕ) ≤ k1 := by have := p.1.2; omega
      exact (by exact_mod_cast hp : (((p.1 : ℕ) : ℝ)) ≤ (k1 : ℝ)).trans hfloor1
    have hb : (((p.2 : ℕ) : ℝ)) ≤ R / (4 * Work.HP.lam N 2) := by
      have hp : (p.2 : ℕ) ≤ k2 := by have := p.2.2; omega
      exact (by exact_mod_cast hp : (((p.2 : ℕ) : ℝ)) ≤ (k2 : ℝ)).trans hfloor2
    have hA : Work.HP.eNorm ((((p.1 : ℕ) : ℤ)) • f 0) ≤ R / 4 := by
      have hf0 : Work.HP.eNorm (f 0) ≤ Work.HP.lam N 1 := by simpa using hfb 0
      calc Work.HP.eNorm ((((p.1 : ℕ) : ℤ)) • f 0)
          = (((p.1 : ℕ) : ℝ)) * Work.HP.eNorm (f 0) := by
            rw [VDC.eNorm_smul_int, abs_of_nonneg (by positivity), Int.cast_natCast]
        _ ≤ (R / (4 * Work.HP.lam N 1)) * Work.HP.lam N 1 :=
            mul_le_mul ha hf0 (Work.HP.eNorm_nonneg _)
              (div_nonneg hRnn (by positivity))
        _ = R / 4 := by field_simp
    have hB : Work.HP.eNorm ((((p.2 : ℕ) : ℤ)) • f 1) ≤ R / 4 := by
      have hf1 : Work.HP.eNorm (f 1) ≤ Work.HP.lam N 2 := by simpa using hfb 1
      calc Work.HP.eNorm ((((p.2 : ℕ) : ℤ)) • f 1)
          = (((p.2 : ℕ) : ℝ)) * Work.HP.eNorm (f 1) := by
            rw [VDC.eNorm_smul_int, abs_of_nonneg (by positivity), Int.cast_natCast]
        _ ≤ (R / (4 * Work.HP.lam N 2)) * Work.HP.lam N 2 :=
            mul_le_mul hb hf1 (Work.HP.eNorm_nonneg _)
              (div_nonneg hRnn (by positivity))
        _ = R / 4 := by field_simp
    have hAB : Work.HP.eNorm
        ((((p.1 : ℕ) : ℤ)) • f 0 + (((p.2 : ℕ) : ℤ)) • f 1) ≤ R / 4 + R / 4 :=
      (VDC.eNorm_add_le _ _).trans (add_le_add hA hB)
    calc Work.HP.eNorm (Ψ p)
        = Work.HP.eNorm (z + ((((p.1 : ℕ) : ℤ)) • f 0 + (((p.2 : ℕ) : ℤ)) • f 1)) := rfl
      _ ≤ Work.HP.eNorm z + Work.HP.eNorm
            ((((p.1 : ℕ) : ℤ)) • f 0 + (((p.2 : ℕ) : ℤ)) • f 1) := VDC.eNorm_add_le _ _
      _ ≤ Work.HP.eNorm z + (R / 4 + R / 4) := add_le_add le_rfl hAB
      _ ≤ R := by linarith [hzR]
  have hΨinj : Function.Injective Ψ := by
    intro p q h
    exact hΦinj (add_left_cancel (by simpa only [Ψ] using h))
  have hsub : Set.range Ψ ⊆ {v : Fin 5 → ℤ | v - z ∈ N ∧ Work.HP.eNorm v ≤ R} := by
    rintro v ⟨p, rfl⟩
    exact ⟨hmem p, hnorm p⟩
  have hfin : ({v : Fin 5 → ℤ | v - z ∈ N ∧ Work.HP.eNorm v ≤ R} : Set (Fin 5 → ℤ)).Finite :=
    (Work.HP.MDBasic.finite_eNorm_le (ι := Fin 5) R).subset (fun v hv => hv.2)
  have hSle : ((Set.range Ψ).ncard : ℝ)
      ≤ (({v : Fin 5 → ℤ | v - z ∈ N ∧ Work.HP.eNorm v ≤ R} : Set (Fin 5 → ℤ)).ncard : ℝ) :=
    by exact_mod_cast (Set.ncard_le_ncard hsub hfin)
  have hrange : (Set.range Ψ).ncard = (k1 + 1) * (k2 + 1) := by
    rw [Set.ncard_range_of_injective hΨinj, Nat.card_eq_fintype_card, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_fin]
  have hcast : ((Set.range Ψ).ncard : ℝ) = ((k1 : ℝ) + 1) * ((k2 : ℝ) + 1) := by
    rw [hrange]; push_cast; ring
  have hb1 : R / (4 * Work.HP.lam N 1) ≤ ((k1 : ℝ) + 1) := by
    rw [hk1]; linarith [Nat.lt_floor_add_one (R / (4 * Work.HP.lam N 1))]
  have hb2 : R / (4 * Work.HP.lam N 2) ≤ ((k2 : ℝ) + 1) := by
    rw [hk2]; linarith [Nat.lt_floor_add_one (R / (4 * Work.HP.lam N 2))]
  have hprod : (R / (4 * Work.HP.lam N 1)) * (R / (4 * Work.HP.lam N 2))
      ≤ ((k1 : ℝ) + 1) * ((k2 : ℝ) + 1) :=
    mul_le_mul hb1 hb2 (div_nonneg hRnn (by positivity)) (by positivity)
  have hfinal : (1 / 16) * (R ^ 2 / (Work.HP.lam N 1 * Work.HP.lam N 2))
      ≤ ((k1 : ℝ) + 1) * ((k2 : ℝ) + 1) := by
    have heq : (R / (4 * Work.HP.lam N 1)) * (R / (4 * Work.HP.lam N 2))
        = (1 / 16) * (R ^ 2 / (Work.HP.lam N 1 * Work.HP.lam N 2)) := by
      field_simp; ring
    rwa [heq] at hprod
  calc (1 / 16) * (R ^ 2 / (Work.HP.lam N 1 * Work.HP.lam N 2))
      ≤ ((k1 : ℝ) + 1) * ((k2 : ℝ) + 1) := hfinal
    _ = ((Set.range Ψ).ncard : ℝ) := hcast.symm
    _ ≤ (({v : Fin 5 → ℤ | v - z ∈ N ∧ Work.HP.eNorm v ≤ R} : Set (Fin 5 → ℤ)).ncard : ℝ) := hSle

end Work.Q44Geom
