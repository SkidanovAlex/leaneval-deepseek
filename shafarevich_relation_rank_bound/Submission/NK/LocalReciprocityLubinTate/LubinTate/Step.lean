import Mathlib
import Submission.NK.LocalReciprocityLubinTate.LubinTate.Setup

/-!
# The induction step of Milne's Lemma I.2.11

Given the "gain" lemma `OrderGe.subst_sub` of `Setup.lean`, this file assembles the
one-step induction of Milne's Lemma 2.11: the effect of adding a correction of order `≥ m`
to a partial solution `ψ` of `f ∘ φ = φ ∘ g` on the coefficients of degree `≤ m` of the
discrepancy `D φ = f ∘ φ - φ ∘ g`.
-/

open MvPowerSeries

namespace NK.LocalReciprocityLubinTate.LubinTate

universe u

variable {A : Type u} [CommRing A] {n : ℕ}

/-- Substituting series of positive order into a series of order `≥ k` keeps order `≥ k`. -/
theorem OrderGe.subst {ι : Type*} [Finite ι] {τ : Type*} {a : ι → MvPowerSeries τ A}
    (ha : ∀ i, OrderGe 1 (a i)) {q : MvPowerSeries ι A} {k : ℕ} (hq : OrderGe k q) :
    OrderGe k (MvPowerSeries.subst a q) := by
  classical
  have ha' : ∀ i, (a i).constantCoeff = 0 := fun i => by
    have := ha i 0 (by simp); simpa using this
  intro e he
  rw [coeff_subst_degree ha' q e]
  refine Finset.sum_eq_zero fun d hd => ?_
  rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hd
  rw [hq d (by omega), zero_smul]

/-- `gSub n g i = g(X i)` has zero constant coefficient when `g` has. -/
theorem gSub_constantCoeff {g : MvPowerSeries (Fin 1) A} (hg : g.constantCoeff = 0)
    (i : Fin n) : (gSub n g i).constantCoeff = 0 := by
  have hXi : (MvPowerSeries.X i : MvPowerSeries (Fin n) A).constantCoeff = 0 := by simp
  have h := MvPowerSeries.constantCoeff_subst_eq_zero
    (a := (![MvPowerSeries.X i] : Fin 1 → MvPowerSeries (Fin n) A))
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun j => by
      fin_cases j; simpa using hXi) (fun j => by fin_cases j; simpa using hXi) hg
  simpa [gSub] using h

/-- `g(X) - πX` has order `≥ 2` for a Lubin–Tate series `g`. -/
theorem orderGe_two_sub_C_mul_X {g : MvPowerSeries (Fin 1) A} {π : A} (hg : g.constantCoeff = 0)
    (hg1 : MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) 1) g = π) :
    OrderGe 2 (g - MvPowerSeries.C π * MvPowerSeries.X (0 : Fin 1)) := by
  intro s hs
  have hsum : s.degree = s 0 := by rw [Finsupp.degree_eq_sum]; simp
  have hs' : s = 0 ∨ s = Finsupp.single (0 : Fin 1) 1 := by
    rcases Nat.eq_zero_or_pos (s 0) with h | h
    · left
      refine Finsupp.ext fun j => ?_
      fin_cases j
      simpa using h
    · right
      have h1 : s 0 = 1 := by omega
      refine Finsupp.ext fun j => ?_
      fin_cases j
      simpa using h1
  rcases hs' with rfl | rfl
  · simp [hg]
  · rw [map_sub, hg1, MvPowerSeries.coeff_C_mul]
    simp

/-- `gSub n g i = g(X i)` agrees with `π X i` modulo terms of degree `≥ 2` for a Lubin–Tate
series `g`. -/
theorem gSub_orderGe_two {g : MvPowerSeries (Fin 1) A} {π : A} (hg : g.constantCoeff = 0)
    (hg1 : MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) 1) g = π) (i : Fin n) :
    OrderGe 2 (gSub n g i - MvPowerSeries.C π * MvPowerSeries.X i) := by
  have hXi : (MvPowerSeries.X i : MvPowerSeries (Fin n) A).constantCoeff = 0 := by simp
  have hsub : MvPowerSeries.HasSubst (![MvPowerSeries.X i] : Fin 1 → MvPowerSeries (Fin n) A) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun j => by
      fin_cases j; simpa using hXi
  have hr := OrderGe.subst (a := (![MvPowerSeries.X i] : Fin 1 → MvPowerSeries (Fin n) A))
    (fun j => by fin_cases j; simpa using OrderGe.of_constantCoeff hXi)
    (orderGe_two_sub_C_mul_X hg hg1)
  rwa [show MvPowerSeries.subst ![MvPowerSeries.X i]
      (g - MvPowerSeries.C π * MvPowerSeries.X (0 : Fin 1))
      = gSub n g i - MvPowerSeries.C π * MvPowerSeries.X i from by
    rw [MvPowerSeries.subst_sub hsub, MvPowerSeries.subst_mul hsub, MvPowerSeries.subst_C,
      MvPowerSeries.subst_X hsub 0]
    simp [gSub]] at hr

/-- **Leading term of a substitution**: if `G i ≡ π X i` modulo terms of degree `≥ 2` and `G i` has
positive order, then substituting into a series `δ` of order `≥ m` multiplies the coefficients of
degree `≤ m` by `π ^ m`. -/
theorem coeff_subst_eq_of_orderGe {G : Fin n → MvPowerSeries (Fin n) A} {π : A}
    (hG1 : ∀ i, OrderGe 1 (G i))
    (hG2 : ∀ i, OrderGe 2 (G i - MvPowerSeries.C π * MvPowerSeries.X i))
    {δ : MvPowerSeries (Fin n) A} {m : ℕ} (hm : 1 ≤ m) (hδ : OrderGe m δ) :
    ∀ s : Fin n →₀ ℕ, s.degree ≤ m →
      MvPowerSeries.coeff s (MvPowerSeries.subst G δ) = π ^ m * MvPowerSeries.coeff s δ := by
  classical
  have hL1 : ∀ i : Fin n, OrderGe 1 (MvPowerSeries.C π * MvPowerSeries.X i) := fun i => by
    rw [← MvPowerSeries.smul_eq_C_mul]
    exact OrderGe.smul (OrderGe.of_constantCoeff (by simp)) π
  have hGAIN := OrderGe.subst_sub (τ := Fin n) (a := G)
    (b := fun i => MvPowerSeries.C π * MvPowerSeries.X i) (q := δ) (k := 2) (κ := m)
    (by norm_num) hm hG1 hL1 hG2 hδ
  intro s hs
  have heq : MvPowerSeries.coeff s (MvPowerSeries.subst G δ)
      = MvPowerSeries.coeff s
        (MvPowerSeries.subst (fun i => MvPowerSeries.C π * MvPowerSeries.X i) δ) := by
    have h := hGAIN s (by omega)
    rwa [map_sub, sub_eq_zero] at h
  rw [heq]
  rw [subst_C_mul_X_eq_rescale (fun _ : Fin n => π) δ, MvPowerSeries.coeff_rescale]
  have hprod : (s.prod fun _ m => π ^ m) = π ^ s.degree := by
    rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]
  rw [hprod]
  rcases eq_or_lt_of_le hs with hsm | hsm
  · rw [hsm]
  · rw [hδ s hsm, mul_zero, mul_zero]

/-- **The one-step induction of Milne's Lemma 2.11**: adding a correction of order `≥ m` to a
partial solution `ψ` (of positive order) changes each coefficient of degree `≤ m` of the
discrepancy `D` by `coeff s δ * (π - π ^ m)`. -/
theorem coeff_Dsub_add {f g : MvPowerSeries (Fin 1) A} {π : A}
    (hf : OrderGe 2 (f - MvPowerSeries.C π * MvPowerSeries.X (0 : Fin 1)))
    (hg : g.constantCoeff = 0) (hg1 : MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) 1) g = π)
    {ψ δ : MvPowerSeries (Fin n) A} {m : ℕ} (hm : 1 ≤ m) (hψ : OrderGe 1 ψ)
    (hδ : OrderGe m δ) :
    ∀ s : Fin n →₀ ℕ, s.degree ≤ m →
      MvPowerSeries.coeff s (Dsub n f g (ψ + δ))
        = MvPowerSeries.coeff s (Dsub n f g ψ) + MvPowerSeries.coeff s δ * (π - π ^ m) := by
  classical
  have hψδ : OrderGe 1 (ψ + δ) := hψ.add (hδ.mono hm)
  have hsub : MvPowerSeries.HasSubst (![ψ + δ] : Fin 1 → MvPowerSeries (Fin n) A) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun j => by
      fin_cases j; simpa using hψδ.constantCoeff
  have hsub' : MvPowerSeries.HasSubst (![ψ] : Fin 1 → MvPowerSeries (Fin n) A) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun j => by
      fin_cases j; simpa using hψ.constantCoeff
  have hG1 : ∀ i : Fin n, OrderGe 1 (gSub n g i) := fun i =>
    OrderGe.of_constantCoeff (gSub_constantCoeff hg i)
  have hG2 : ∀ i : Fin n, OrderGe 2 (gSub n g i - MvPowerSeries.C π * MvPowerSeries.X i) :=
    fun i => gSub_orderGe_two hg hg1 i
  have hGsub : MvPowerSeries.HasSubst (gSub n g) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => gSub_constantCoeff hg i
  -- the `f`-side
  have hfkey : ∀ s : Fin n →₀ ℕ, s.degree ≤ m →
      MvPowerSeries.coeff s (MvPowerSeries.subst ![ψ + δ] f)
        = MvPowerSeries.coeff s (MvPowerSeries.subst ![ψ] f) + π * MvPowerSeries.coeff s δ := by
    intro s hs
    have hsplit : MvPowerSeries.subst ![ψ + δ] f - MvPowerSeries.subst ![ψ] f
        - MvPowerSeries.C π * δ
        = MvPowerSeries.subst ![ψ + δ] (f - MvPowerSeries.C π * MvPowerSeries.X (0 : Fin 1))
          - MvPowerSeries.subst ![ψ] (f - MvPowerSeries.C π * MvPowerSeries.X (0 : Fin 1)) := by
      rw [MvPowerSeries.subst_sub hsub, MvPowerSeries.subst_sub hsub',
        MvPowerSeries.subst_mul hsub, MvPowerSeries.subst_mul hsub',
        MvPowerSeries.subst_C, MvPowerSeries.subst_C,
        MvPowerSeries.subst_X hsub (0 : Fin 1), MvPowerSeries.subst_X hsub' (0 : Fin 1)]
      simp only [Matrix.cons_val_zero]
      ring
    have hgain : OrderGe (m + 1)
        (MvPowerSeries.subst ![ψ + δ] (f - MvPowerSeries.C π * MvPowerSeries.X (0 : Fin 1))
          - MvPowerSeries.subst ![ψ] (f - MvPowerSeries.C π * MvPowerSeries.X (0 : Fin 1))) :=
      OrderGe.subst_sub (τ := Fin n) (a := (![ψ + δ] : Fin 1 → MvPowerSeries (Fin n) A))
        (b := (![ψ] : Fin 1 → MvPowerSeries (Fin n) A))
        (q := f - MvPowerSeries.C π * MvPowerSeries.X (0 : Fin 1)) (k := m) (κ := 2)
        hm (by norm_num) (fun i => by fin_cases i; simpa using hψδ)
        (fun i => by fin_cases i; simpa using hψ)
        (fun i => by fin_cases i; simpa using hδ) hf
    have hzero : MvPowerSeries.coeff s
        (MvPowerSeries.subst ![ψ + δ] f - MvPowerSeries.subst ![ψ] f
          - MvPowerSeries.C π * δ) = 0 := by
      rw [hsplit]
      exact hgain s (by omega)
    rw [map_sub, map_sub, MvPowerSeries.coeff_C_mul] at hzero
    linear_combination hzero
  -- the `g`-side
  have hgkey : ∀ s : Fin n →₀ ℕ, s.degree ≤ m →
      MvPowerSeries.coeff s (MvPowerSeries.subst (gSub n g) (ψ + δ))
        = MvPowerSeries.coeff s (MvPowerSeries.subst (gSub n g) ψ)
          + π ^ m * MvPowerSeries.coeff s δ := by
    intro s hs
    rw [MvPowerSeries.subst_add hGsub, map_add,
      coeff_subst_eq_of_orderGe hG1 hG2 hm hδ s hs]
  intro s hs
  have h1 := hfkey s hs
  have h2 := hgkey s hs
  show MvPowerSeries.coeff s (MvPowerSeries.subst ![ψ + δ] f
      - MvPowerSeries.subst (gSub n g) (ψ + δ))
    = MvPowerSeries.coeff s
        (MvPowerSeries.subst ![ψ] f - MvPowerSeries.subst (gSub n g) ψ)
      + MvPowerSeries.coeff s δ * (π - π ^ m)
  rw [map_sub, map_sub, h1, h2]
  ring

end NK.LocalReciprocityLubinTate.LubinTate
