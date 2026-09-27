import Mathlib

/-!
# Derivative bounds for the `√`-substitution

We show that the iterated derivatives of `y ↦ fderiv ℝ (p ↦ (p.1, √ p.2)) y` on the region
`0 < y.2 ≤ 1` grow at most like a constant times `(√ y.2)^{-(2m+1)}`.

The point of the estimate is that `fderiv ℝ (p ↦ (p.1, √ p.2)) y` is
`A + (2 √ y.2)⁻¹ • B` for two fixed continuous linear maps `A`, `B`; hence its iterated
derivatives only involve the higher derivatives of the one-variable function
`t ↦ (2 √ t)⁻¹ = d/dt √t`.
-/

namespace Work.Drive

open scoped Topology

noncomputable section

/-- `d/dt (√t)`, as a function of `t`: it is `(2 √t)⁻¹`. -/
private def dsqrt : ℝ → ℝ := fun t => (2 * Real.sqrt t)⁻¹

/-- Coefficients of the higher derivatives of `dsqrt`: `a 0 = 1/2` and
`a (n+1) = a n * (-(2n+1)/2)`. -/
private def acoeff : ℕ → ℝ := Nat.rec (1 / 2) (fun n a => a * (-((2 * (n : ℝ) + 1) / 2)))

private lemma acoeff_zero : acoeff 0 = 1 / 2 := rfl

private lemma acoeff_succ (n : ℕ) :
    acoeff (n + 1) = acoeff n * (-((2 * (n : ℝ) + 1) / 2)) := rfl

private lemma acoeff_abs_le (n : ℕ) : |acoeff n| ≤ ((n.factorial : ℕ) : ℝ) := by
  induction n with
  | zero => rw [acoeff_zero]; norm_num
  | succ n ih =>
    rw [acoeff_succ, abs_mul]
    have hle : |(-((2 * (n : ℝ) + 1) / 2))| ≤ ((n : ℝ) + 1) := by
      have hpos : (0 : ℝ) < (2 * (n : ℝ) + 1) / 2 := by positivity
      rw [abs_of_nonpos (by linarith)]
      linarith
    calc |acoeff n| * |(-((2 * (n : ℝ) + 1) / 2))|
        ≤ ((n.factorial : ℕ) : ℝ) * ((n : ℝ) + 1) :=
          mul_le_mul ih hle (abs_nonneg _) (by positivity)
      _ = (((n + 1).factorial : ℕ) : ℝ) := by
          rw [Nat.factorial_succ]; push_cast; ring

private lemma deriv_sqrt_zpow (k : ℤ) {t : ℝ} (ht : 0 < t) :
    deriv (fun s : ℝ => (Real.sqrt s) ^ k) t = ((k : ℝ) / 2) * (Real.sqrt t) ^ (k - 2) := by
  have hu : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.2 ht
  have hcomp : HasDerivAt (fun s : ℝ => (Real.sqrt s) ^ k)
      (((k : ℝ) * (Real.sqrt t) ^ (k - 1)) * (1 / (2 * Real.sqrt t))) t := by
    simpa only [Function.comp_def] using
      (hasDerivAt_zpow k (Real.sqrt t) (Or.inl (ne_of_gt hu))).comp t
        (Real.hasDerivAt_sqrt (ne_of_gt ht))
  rw [hcomp.deriv]
  have h1 : (1 / (2 * Real.sqrt t) : ℝ) = (1 / 2) * (Real.sqrt t) ^ (-1 : ℤ) := by
    rw [zpow_neg_one]; ring
  have h2 : (Real.sqrt t) ^ (k - 1) * (Real.sqrt t) ^ (-1 : ℤ) = (Real.sqrt t) ^ (k - 2) := by
    rw [← zpow_add₀ (ne_of_gt hu) (k - 1) (-1)]
    congr 1
    ring
  calc ((k : ℝ) * (Real.sqrt t) ^ (k - 1)) * (1 / (2 * Real.sqrt t))
      = ((k : ℝ) * (1 / 2)) * ((Real.sqrt t) ^ (k - 1) * (Real.sqrt t) ^ (-1 : ℤ)) := by
        rw [h1]; ring
    _ = ((k : ℝ) / 2) * (Real.sqrt t) ^ (k - 2) := by rw [h2]; ring

private lemma iteratedDeriv_dsqrt_eq :
    ∀ (n : ℕ) {t : ℝ}, 0 < t →
      iteratedDeriv n dsqrt t = acoeff n * (Real.sqrt t) ^ (-(2 * (n : ℤ) + 1)) := by
  intro n
  induction n with
  | zero =>
    intro t ht
    show dsqrt t = acoeff 0 * (Real.sqrt t) ^ (-(2 * ((0 : ℕ) : ℤ) + 1))
    rw [acoeff_zero, show (-(2 * ((0 : ℕ) : ℤ) + 1)) = (-1 : ℤ) by norm_num, zpow_neg_one]
    rw [dsqrt, mul_inv]
    ring
  | succ n ih =>
    intro t ht
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv n dsqrt =ᶠ[𝓝 t]
        (fun s : ℝ => acoeff n * (Real.sqrt s) ^ (-(2 * (n : ℤ) + 1))) := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
      exact ih hs
    rw [heq.deriv_eq, deriv_const_mul_field, deriv_sqrt_zpow (-(2 * (n : ℤ) + 1)) ht]
    have hexp : (-(2 * (n : ℤ) + 1)) - 2 = -(2 * (((n + 1 : ℕ) : ℤ)) + 1) := by
      push_cast
      ring
    have hcast : (((-(2 * (n : ℤ) + 1) : ℤ)) : ℝ) = -(2 * (n : ℝ) + 1) := by
      push_cast; ring
    rw [hcast, acoeff_succ, ← hexp]
    ring

private lemma iteratedDeriv_dsqrt_abs_le (n : ℕ) {t : ℝ} (ht : 0 < t) :
    |iteratedDeriv n dsqrt t| ≤ ((n.factorial : ℕ) : ℝ) / (Real.sqrt t) ^ (2 * n + 1) := by
  rw [iteratedDeriv_dsqrt_eq n ht, abs_mul]
  have hu : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.2 ht
  have hval : |(Real.sqrt t) ^ (-(2 * (n : ℤ) + 1))| = 1 / (Real.sqrt t) ^ (2 * n + 1) := by
    rw [abs_of_pos (zpow_pos hu (-(2 * (n : ℤ) + 1)))]
    have hz : (-(2 * (n : ℤ) + 1)) = -(((2 * n + 1 : ℕ)) : ℤ) := by push_cast; ring
    rw [hz, zpow_neg, zpow_natCast, one_div]
  rw [hval]
  have h1 : |acoeff n| * (1 / (Real.sqrt t) ^ (2 * n + 1))
      ≤ ((n.factorial : ℕ) : ℝ) * (1 / (Real.sqrt t) ^ (2 * n + 1)) :=
    mul_le_mul_of_nonneg_right (acoeff_abs_le n) (by positivity)
  simpa only [mul_one_div] using h1

private lemma contDiffOn_dsqrt : ContDiffOn ℝ (⊤ : WithTop ℕ∞) dsqrt (Set.Ioi (0 : ℝ)) := by
  have h1 : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (fun t : ℝ => 2 * Real.sqrt t) (Set.Ioi (0 : ℝ)) := by
    have hc : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (fun _ : ℝ => (2 : ℝ)) (Set.Ioi (0 : ℝ)) :=
      contDiffOn_const
    exact hc.mul (contDiffOn_id.sqrt (fun t ht => ne_of_gt ht))
  have h2 := h1.inv (fun t ht => by
    have h : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.2 ht
    positivity)
  exact h2

private lemma contDiffAt_dsqrt_snd (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (n : ℕ) {z : X × ℝ} (hz : 0 < z.2) :
    ContDiffAt ℝ ((n : ℕ∞) : WithTop ℕ∞) (fun y : X × ℝ => dsqrt y.2) z := by
  have hcd : ContDiffAt ℝ ((n : ℕ∞) : WithTop ℕ∞) dsqrt z.2 :=
    (contDiffOn_dsqrt.contDiffAt (isOpen_Ioi.mem_nhds hz)).of_le le_top
  have hsnd : ContDiffAt ℝ ((n : ℕ∞) : WithTop ℕ∞) (fun y : X × ℝ => y.2) z :=
    (contDiff_snd (𝕜 := ℝ)).contDiffAt
  exact hcd.comp z hsnd

/-- Pointwise bound for the iterated derivatives of `y ↦ dsqrt y.2 = (2√y.2)⁻¹`, stated for
the composition with the projection. -/
private lemma norm_iteratedFDeriv_dsqrt_comp_le {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (m : ℕ) {z : X × ℝ} (hz : 0 < z.2) :
    ‖iteratedFDeriv ℝ m (dsqrt ∘ (ContinuousLinearMap.snd ℝ X ℝ)) z‖
      ≤ ((m.factorial : ℕ) : ℝ) / (Real.sqrt z.2) ^ (2 * m + 1) := by
  have hsopen : IsOpen (Set.Ioi (0 : ℝ)) := isOpen_Ioi
  have hcomp := ContinuousLinearMap.iteratedFDerivWithin_comp_right (𝕜 := ℝ)
    (g := ContinuousLinearMap.snd ℝ X ℝ) (f := dsqrt) (s := Set.Ioi (0 : ℝ))
    (n := (⊤ : WithTop ℕ∞)) (x := z) contDiffOn_dsqrt hsopen.uniqueDiffOn
    (hsopen.preimage continuous_snd).uniqueDiffOn (show (ContinuousLinearMap.snd ℝ X ℝ) z ∈ Set.Ioi (0:ℝ) from hz)
    (i := m) le_top
  have hwit : iteratedFDerivWithin ℝ m (dsqrt ∘ ⇑(ContinuousLinearMap.snd ℝ X ℝ))
        ((ContinuousLinearMap.snd ℝ X ℝ) ⁻¹' Set.Ioi (0 : ℝ)) z
      = iteratedFDeriv ℝ m (dsqrt ∘ ⇑(ContinuousLinearMap.snd ℝ X ℝ)) z :=
    (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
      (f := dsqrt ∘ ⇑(ContinuousLinearMap.snd ℝ X ℝ)) m
      (hsopen.preimage continuous_snd)) hz
  rw [← hwit, hcomp]
  calc ‖(iteratedFDerivWithin ℝ m dsqrt (Set.Ioi (0 : ℝ)) (z.2)).compContinuousLinearMap
          (fun _ => ContinuousLinearMap.snd ℝ X ℝ)‖
      ≤ ‖iteratedFDerivWithin ℝ m dsqrt (Set.Ioi (0 : ℝ)) (z.2)‖ *
          ∏ _ : Fin m, ‖ContinuousLinearMap.snd ℝ X ℝ‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDerivWithin ℝ m dsqrt (Set.Ioi (0 : ℝ)) (z.2)‖ *
          ‖ContinuousLinearMap.snd ℝ X ℝ‖ ^ m := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ ‖iteratedFDerivWithin ℝ m dsqrt (Set.Ioi (0 : ℝ)) (z.2)‖ * 1 := by
        gcongr
        exact pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_snd_le ℝ X ℝ)
    _ = ‖iteratedDerivWithin m dsqrt (Set.Ioi (0 : ℝ)) (z.2)‖ := by
        rw [mul_one, norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
    _ = ‖iteratedDeriv m dsqrt (z.2)‖ := by
        rw [(iteratedDerivWithin_of_isOpen (𝕜 := ℝ) (n := m) (f := dsqrt) hsopen) hz]
    _ ≤ ((m.factorial : ℕ) : ℝ) / (Real.sqrt z.2) ^ (2 * m + 1) := by
        rw [Real.norm_eq_abs]
        exact iteratedDeriv_dsqrt_abs_le m hz

/-- Pointwise bound for the iterated derivatives of `y ↦ dsqrt y.2 = (2√y.2)⁻¹`. -/
private lemma norm_iteratedFDeriv_dsqrt_snd_le {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (m : ℕ) {z : X × ℝ} (hz : 0 < z.2) :
    ‖iteratedFDeriv ℝ m (fun y : X × ℝ => dsqrt y.2) z‖
      ≤ ((m.factorial : ℕ) : ℝ) / (Real.sqrt z.2) ^ (2 * m + 1) := by
  have he : iteratedFDeriv ℝ m (fun y : X × ℝ => dsqrt y.2)
      = iteratedFDeriv ℝ m (dsqrt ∘ ⇑(ContinuousLinearMap.snd ℝ X ℝ)) :=
    congrArg (iteratedFDeriv ℝ m) (funext fun y => rfl)
  rw [he]
  exact norm_iteratedFDeriv_dsqrt_comp_le (X := X) m hz

/-- The derivative of the `√`-substitution map `p ↦ (p.1, √p.2)` at a point with positive
second coordinate. -/
private lemma fderiv_sqrt_subst (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (y : X × ℝ) (hy : 0 < y.2) :
    fderiv ℝ (fun p : X × ℝ => ((p.1 : X), Real.sqrt p.2)) y
      = (ContinuousLinearMap.fst ℝ X ℝ).prod (0 : X × ℝ →L[ℝ] ℝ)
        + (2 * Real.sqrt y.2)⁻¹ •
            ((0 : X × ℝ →L[ℝ] X).prod (ContinuousLinearMap.snd ℝ X ℝ)) := by
  have h1 : HasFDerivAt (fun p : X × ℝ => (p.1 : X)) (ContinuousLinearMap.fst ℝ X ℝ) y :=
    (ContinuousLinearMap.fst ℝ X ℝ).hasFDerivAt
  have h2 : HasFDerivAt (fun p : X × ℝ => Real.sqrt p.2)
      (((2 * Real.sqrt y.2)⁻¹) • ContinuousLinearMap.snd ℝ X ℝ) y := by
    have h := (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.snd ℝ X ℝ)).sqrt (ne_of_gt hy)
    simpa using h
  have h3 : HasFDerivAt (fun p : X × ℝ => ((p.1 : X), Real.sqrt p.2))
      ((ContinuousLinearMap.fst ℝ X ℝ).prod
        (((2 * Real.sqrt y.2)⁻¹) • ContinuousLinearMap.snd ℝ X ℝ)) y := by
    simpa using h1.prodMk h2
  have hderiv : (ContinuousLinearMap.fst ℝ X ℝ).prod
        (((2 * Real.sqrt y.2)⁻¹) • ContinuousLinearMap.snd ℝ X ℝ)
      = (ContinuousLinearMap.fst ℝ X ℝ).prod (0 : X × ℝ →L[ℝ] ℝ)
        + (2 * Real.sqrt y.2)⁻¹ •
            ((0 : X × ℝ →L[ℝ] X).prod (ContinuousLinearMap.snd ℝ X ℝ)) := by
    apply ContinuousLinearMap.ext
    intro p
    simp [ContinuousLinearMap.prod_apply]
  rw [hderiv] at h3
  exact h3.fderiv

theorem sqrt_subst_fderiv_bound (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    ∃ b : ℕ → ℝ, (∀ m, 0 ≤ b m) ∧
      ∀ (z : X × ℝ), 0 < z.2 → z.2 ≤ 1 → ∀ m : ℕ,
        ‖iteratedFDeriv ℝ m
            (fun y : X × ℝ => fderiv ℝ (fun p : X × ℝ => ((p.1 : X), Real.sqrt p.2)) y) z‖
          ≤ b m / (Real.sqrt z.2) ^ (1 + 2 * m) := by
  classical
  let A : (X × ℝ) →L[ℝ] (X × ℝ) := (ContinuousLinearMap.fst ℝ X ℝ).prod (0 : X × ℝ →L[ℝ] ℝ)
  let B : (X × ℝ) →L[ℝ] (X × ℝ) := (0 : X × ℝ →L[ℝ] X).prod (ContinuousLinearMap.snd ℝ X ℝ)
  refine ⟨fun m => ‖A‖ + ‖B‖ * ((m.factorial : ℕ) : ℝ), fun m => by positivity, ?_⟩
  intro z hz0 hz1 m
  have hfderiv : ∀ y : X × ℝ, 0 < y.2 →
      fderiv ℝ (fun p : X × ℝ => ((p.1 : X), Real.sqrt p.2)) y = A + dsqrt y.2 • B := by
    intro y hy
    exact fderiv_sqrt_subst X y hy
  have hSopen : IsOpen {y : X × ℝ | 0 < y.2} := isOpen_Ioi.preimage continuous_snd
  have hzS : z ∈ {y : X × ℝ | 0 < y.2} := hz0
  have hcongr := iteratedFDerivWithin_congr (𝕜 := ℝ) (E := X × ℝ)
      (F := (X × ℝ) →L[ℝ] (X × ℝ))
      (s := {y : X × ℝ | 0 < y.2})
      (f₁ := fun y : X × ℝ =>
        fderiv ℝ (fun p : X × ℝ => ((p.1 : X), Real.sqrt p.2)) y)
      (f := fun y : X × ℝ => A + dsqrt y.2 • B)
      (fun y hy => hfderiv y hy) hzS m
  have h1 := (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (E := X × ℝ)
      (F := (X × ℝ) →L[ℝ] (X × ℝ))
      (f := fun y : X × ℝ =>
        fderiv ℝ (fun p : X × ℝ => ((p.1 : X), Real.sqrt p.2)) y) m hSopen) hzS
  have h2 := (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (E := X × ℝ)
      (F := (X × ℝ) →L[ℝ] (X × ℝ))
      (f := fun y : X × ℝ => A + dsqrt y.2 • B) m hSopen) hzS
  rw [← h1, hcongr, h2]
  rcases m with _ | k
  · -- m = 0
    rw [norm_iteratedFDeriv_zero]
    show ‖A + dsqrt z.2 • B‖
      ≤ (‖A‖ + ‖B‖ * ((Nat.factorial 0 : ℕ) : ℝ)) / (Real.sqrt z.2) ^ (1 + 2 * 0)
    rw [Nat.factorial_zero, Nat.cast_one, mul_one,
      show (1 + 2 * 0 : ℕ) = 1 by norm_num, pow_one]
    have hs : (0 : ℝ) < Real.sqrt z.2 := Real.sqrt_pos.2 hz0
    have hds : (0 : ℝ) < dsqrt z.2 := by rw [dsqrt]; positivity
    have hbnd : ‖A + dsqrt z.2 • B‖ ≤ ‖A‖ + dsqrt z.2 * ‖B‖ := by
      calc ‖A + dsqrt z.2 • B‖ ≤ ‖A‖ + ‖dsqrt z.2 • B‖ := norm_add_le _ _
        _ = ‖A‖ + ‖dsqrt z.2‖ * ‖B‖ := by rw [norm_smul]
        _ = ‖A‖ + dsqrt z.2 * ‖B‖ := by
            rw [Real.norm_eq_abs, abs_of_pos hds]
    refine hbnd.trans ?_
    have hsqrt1 : Real.sqrt z.2 ≤ 1 := Real.sqrt_le_one.2 hz1
    have hr : 1 ≤ (Real.sqrt z.2)⁻¹ := by
      rw [one_le_inv₀ hs]
      exact hsqrt1
    have hA : ‖A‖ ≤ ‖A‖ * (Real.sqrt z.2)⁻¹ := le_mul_of_one_le_right (norm_nonneg A) hr
    have hB : dsqrt z.2 * ‖B‖ ≤ ‖B‖ * (Real.sqrt z.2)⁻¹ := by
      have hds' : dsqrt z.2 ≤ (Real.sqrt z.2)⁻¹ := by
        rw [dsqrt, mul_inv]
        calc (2 : ℝ)⁻¹ * (Real.sqrt z.2)⁻¹ ≤ 1 * (Real.sqrt z.2)⁻¹ :=
              mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
          _ = (Real.sqrt z.2)⁻¹ := by ring
      calc dsqrt z.2 * ‖B‖ = ‖B‖ * dsqrt z.2 := by ring
        _ ≤ ‖B‖ * (Real.sqrt z.2)⁻¹ := mul_le_mul_of_nonneg_left hds' (norm_nonneg B)
    calc ‖A‖ + dsqrt z.2 * ‖B‖
        ≤ ‖A‖ * (Real.sqrt z.2)⁻¹ + ‖B‖ * (Real.sqrt z.2)⁻¹ := add_le_add hA hB
      _ = (‖A‖ + ‖B‖) * (Real.sqrt z.2)⁻¹ := by ring
      _ = (‖A‖ + ‖B‖) / Real.sqrt z.2 := by rw [div_eq_mul_inv]
  · -- m = k + 1
    rw [show (1 + 2 * (k + 1) : ℕ) = 2 * (k + 1) + 1 by ring]
    have hm0 : k + 1 ≠ 0 := Nat.succ_ne_zero k
    have hcd : ContDiffAt ℝ (((k + 1 : ℕ) : ℕ∞) : WithTop ℕ∞)
        (fun y : X × ℝ => dsqrt y.2) z := contDiffAt_dsqrt_snd X (k + 1) hz0
    have hbound : ‖iteratedFDeriv ℝ (k + 1) (fun y : X × ℝ => A + dsqrt y.2 • B) z‖
        ≤ ‖iteratedFDeriv ℝ (k + 1) (fun y : X × ℝ => dsqrt y.2 • B) z‖ := by
      have hsum : iteratedFDeriv ℝ (k + 1) (fun y : X × ℝ => A + dsqrt y.2 • B) z
          = iteratedFDeriv ℝ (k + 1) (fun _ : X × ℝ => A) z
            + iteratedFDeriv ℝ (k + 1) (fun y : X × ℝ => dsqrt y.2 • B) z := by
        rw [show (fun y : X × ℝ => A + dsqrt y.2 • B)
              = (fun _ : X × ℝ => A) + (fun y : X × ℝ => dsqrt y.2 • B) from rfl]
        exact iteratedFDeriv_add_apply (𝕜 := ℝ) (E := X × ℝ)
          (F := (X × ℝ) →L[ℝ] (X × ℝ))
          (f := fun _ : X × ℝ => A) (g := fun y : X × ℝ => dsqrt y.2 • B)
          contDiffAt_const (hcd.smul_const B)
      have hzero : iteratedFDeriv ℝ (k + 1) (fun _ : X × ℝ => A) z = 0 := by
        rw [show iteratedFDeriv ℝ (k + 1) (fun _ : X × ℝ => A)
              = 0 from iteratedFDeriv_const_of_ne (𝕜 := ℝ)
                (F := (X × ℝ) →L[ℝ] (X × ℝ)) hm0 A]
        rfl
      calc ‖iteratedFDeriv ℝ (k + 1) (fun y : X × ℝ => A + dsqrt y.2 • B) z‖
          = ‖iteratedFDeriv ℝ (k + 1) (fun _ : X × ℝ => A) z
              + iteratedFDeriv ℝ (k + 1) (fun y : X × ℝ => dsqrt y.2 • B) z‖ := by
              rw [hsum]
        _ ≤ ‖iteratedFDeriv ℝ (k + 1) (fun _ : X × ℝ => A) z‖
              + ‖iteratedFDeriv ℝ (k + 1) (fun y : X × ℝ => dsqrt y.2 • B) z‖ :=
              norm_add_le _ _
        _ = ‖iteratedFDeriv ℝ (k + 1) (fun y : X × ℝ => dsqrt y.2 • B) z‖ := by
              rw [hzero, norm_zero, zero_add]
    refine hbound.trans ?_
    have hmain : ‖iteratedFDeriv ℝ (k + 1) (fun y : X × ℝ => dsqrt y.2 • B) z‖
        ≤ ‖B‖ * ((((k + 1).factorial : ℕ) : ℝ) / (Real.sqrt z.2) ^ (2 * (k + 1) + 1)) := by
      have hfun : (fun y : X × ℝ => dsqrt y.2 • B)
          = (⇑(ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) B)) ∘
              (fun y : X × ℝ => dsqrt y.2) := by
        funext y; simp [ContinuousLinearMap.smulRight_apply]
      rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_left (𝕜 := ℝ) (E := X × ℝ) (F := ℝ)
          (G := (X × ℝ) →L[ℝ] (X × ℝ))
          (g := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) B)
          (f := fun y : X × ℝ => dsqrt y.2) (x := z) (i := k + 1) hcd (le_refl _)]
      have h1 : ‖ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) B‖ ≤ ‖B‖ := by
        rw [ContinuousLinearMap.norm_smulRight_apply]
        simp
      calc ‖(ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) B).compContinuousMultilinearMap
              (iteratedFDeriv ℝ (k + 1) (fun y : X × ℝ => dsqrt y.2) z)‖
          ≤ ‖ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) B‖ *
              ‖iteratedFDeriv ℝ (k + 1) (fun y : X × ℝ => dsqrt y.2) z‖ :=
            ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
        _ ≤ ‖B‖ * ‖iteratedFDeriv ℝ (k + 1) (fun y : X × ℝ => dsqrt y.2) z‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ ≤ ‖B‖ * ((((k + 1).factorial : ℕ) : ℝ) / (Real.sqrt z.2) ^ (2 * (k + 1) + 1)) :=
            mul_le_mul_of_nonneg_left
              (norm_iteratedFDeriv_dsqrt_snd_le (X := X) (k + 1) hz0) (norm_nonneg B)
    refine hmain.trans ?_
    show ‖B‖ * ((((k + 1).factorial : ℕ) : ℝ) / (Real.sqrt z.2) ^ (2 * (k + 1) + 1))
      ≤ (‖A‖ + ‖B‖ * (((k + 1).factorial : ℕ) : ℝ)) / (Real.sqrt z.2) ^ (2 * (k + 1) + 1)
    rw [add_div, ← mul_div_assoc]
    exact le_add_of_nonneg_left (by positivity)

end

end Work.Drive
