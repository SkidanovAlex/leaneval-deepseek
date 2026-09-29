import Submission.Work.TMComp.RotBasics.PSCont

/-!
# The Prüfer iteration `pruferIter`

`pruferIter α lam E n x t` is the `n`-fold Prüfer iteration of the transfer matrices
`tmR lam E (x + jα)` (`a(y) = E - 2λ cos 2πy`), starting from the angle `t`:

* shift identity in `t`, monotonicity in `t`;
* periodicity in `x`;
* the cocycle identity (splitting `n + m` into `m` steps after `n`);
* the bound `|F(t) - F(0) - t| ≤ 1`;
* continuity in `(α, E, x)`;
* antitonicity in `E`;
* `pruferIter` as the positive lift of the iterated transfer matrix `iterR`.
-/

namespace Work.TMComp.RotBasics

open Work.TMContract

noncomputable section

theorem pruferIter_zero (α lam E : ℝ) (x t : ℝ) : pruferIter α lam E 0 x t = t := by
  simp only [pruferIter]

theorem pruferIter_succ (α lam E : ℝ) (n : ℕ) (x t : ℝ) :
    pruferIter α lam E (n + 1) x t =
      pruferStep (E - 2 * lam * Real.cos (2 * Real.pi * (x + (n : ℝ) * α)))
        (pruferIter α lam E n x t) := by
  simp only [pruferIter]

theorem pruferIter_add_one (α lam E : ℝ) (n : ℕ) (x t : ℝ) :
    pruferIter α lam E n x (t + 1) = pruferIter α lam E n x t + 1 := by
  induction n generalizing t with
  | zero => simp [pruferIter_zero]
  | succ n ih => rw [pruferIter_succ, pruferIter_succ, ih, pruferStep_add_one]

theorem pruferIter_mono_t (α lam E : ℝ) (n : ℕ) (x : ℝ) :
    Monotone (fun t : ℝ => pruferIter α lam E n x t) := by
  induction n with
  | zero => intro s t h; simpa [pruferIter_zero] using h
  | succ n ih =>
    intro s t h
    change pruferIter α lam E (n + 1) x s ≤ pruferIter α lam E (n + 1) x t
    rw [pruferIter_succ, pruferIter_succ]
    exact pruferStep_mono _ (ih h)

theorem pruferIter_periodic_x (α lam E : ℝ) (n : ℕ) (x t : ℝ) :
    pruferIter α lam E n (x + 1) t = pruferIter α lam E n x t := by
  induction n generalizing x with
  | zero => simp [pruferIter_zero]
  | succ n ih =>
    rw [pruferIter_succ, pruferIter_succ, ih]
    congr 1
    rw [show E - 2 * lam * Real.cos (2 * Real.pi * (x + 1 + (n : ℝ) * α))
        = E - 2 * lam * Real.cos (2 * Real.pi * (x + (n : ℝ) * α) + 2 * Real.pi) by ring,
      Real.cos_add, Real.cos_two_pi, Real.sin_two_pi]
    ring

theorem pruferIter_periodic_x_int (α lam E : ℝ) (n : ℕ) (m : ℤ) (x t : ℝ) :
    pruferIter α lam E n (x + m) t = pruferIter α lam E n x t := by
  have hnat : ∀ (k : ℕ) (y : ℝ), pruferIter α lam E n (y + k) t = pruferIter α lam E n y t := by
    intro k y
    induction k with
    | zero => simp
    | succ k ih =>
      push_cast
      rw [show y + ((k : ℝ) + 1) = (y + (k : ℝ)) + 1 by ring, pruferIter_periodic_x, ih]
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg m
  · rw [hk]; push_cast; exact hnat k x
  · rw [hk]; push_cast
    have h := hnat k (x + -(k : ℝ))
    rw [show x + -(k : ℝ) + (k : ℝ) = x by ring] at h
    exact h.symm

theorem pruferIter_cocycle (α lam E : ℝ) (n m : ℕ) (x t : ℝ) :
    pruferIter α lam E (n + m) x t =
      pruferIter α lam E m (x + (n : ℝ) * α) (pruferIter α lam E n x t) := by
  induction m with
  | zero => simp [pruferIter_zero]
  | succ m ih =>
    rw [show n + (m + 1) = (n + m) + 1 by ring, pruferIter_succ, ih, pruferIter_succ]
    congr 1
    rw [show x + (n : ℝ) * α + (m : ℝ) * α = x + ((n + m : ℕ) : ℝ) * α by push_cast; ring]

theorem pruferIter_bound (α lam E : ℝ) (n : ℕ) (x t : ℝ) :
    |pruferIter α lam E n x t - pruferIter α lam E n x 0 - t| ≤ 1 := by
  have hmono : Monotone (fun s : ℝ => pruferIter α lam E n x s) := pruferIter_mono_t α lam E n x
  have hdeg : ∀ s : ℝ, pruferIter α lam E n x (s + 1) = pruferIter α lam E n x s + 1 :=
    fun s => pruferIter_add_one α lam E n x s
  have hnat : ∀ (k : ℕ) (s : ℝ), pruferIter α lam E n x (s + k) = pruferIter α lam E n x s + k := by
    intro k s
    induction k with
    | zero => simp
    | succ k ih =>
      push_cast
      rw [show s + ((k : ℝ) + 1) = (s + (k : ℝ)) + 1 by ring, hdeg, ih]
      ring
  have hshift : ∀ (m : ℤ) (s : ℝ), pruferIter α lam E n x (s + m)
      = pruferIter α lam E n x s + m := by
    intro m s
    obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg m
    · rw [hk]; push_cast; exact hnat k s
    · rw [hk]; push_cast
      have h := hnat k (s + -(k : ℝ))
      rw [show s + -(k : ℝ) + (k : ℝ) = s by ring] at h
      linarith
  have h0 : |pruferIter α lam E n x (t - ⌊t⌋) - pruferIter α lam E n x 0 - (t - ⌊t⌋)| ≤ 1 := by
    have hfl : (0 : ℝ) ≤ t - ⌊t⌋ := by
      have := Int.floor_le t; linarith
    have hfu : t - ⌊t⌋ < 1 := by
      have := Int.lt_floor_add_one t; linarith
    have h1 : pruferIter α lam E n x 0 ≤ pruferIter α lam E n x (t - ⌊t⌋) := hmono hfl
    have h2 : pruferIter α lam E n x (t - ⌊t⌋) ≤ pruferIter α lam E n x 0 + 1 := by
      have h3 : pruferIter α lam E n x (t - ⌊t⌋) ≤ pruferIter α lam E n x (1 : ℝ) :=
        hmono (le_of_lt hfu)
      rw [show (1 : ℝ) = 0 + 1 by ring, hdeg 0] at h3
      exact h3
    rw [abs_le]
    constructor <;> linarith
  have hmain : pruferIter α lam E n x t = pruferIter α lam E n x (t - ⌊t⌋) + ⌊t⌋ := by
    have h := hshift ⌊t⌋ (t - ⌊t⌋)
    rw [show t - (⌊t⌋ : ℝ) + ((⌊t⌋ : ℤ) : ℝ) = t by push_cast; ring] at h
    exact h
  rw [show pruferIter α lam E n x t - pruferIter α lam E n x 0 - t
      = pruferIter α lam E n x (t - ⌊t⌋) - pruferIter α lam E n x 0 - (t - ⌊t⌋) by
    rw [hmain]; ring]
  exact h0

theorem pruferIter_continuous (lam : ℝ) (n : ℕ) :
    Continuous (fun p : ℝ × ℝ × ℝ => pruferIter p.1 lam p.2.1 n p.2.2 0) := by
  induction n with
  | zero =>
    simp only [pruferIter_zero]
    exact continuous_const
  | succ n ih =>
    have hfun : (fun p : ℝ × ℝ × ℝ => pruferIter p.1 lam p.2.1 (n + 1) p.2.2 0)
        = fun p : ℝ × ℝ × ℝ =>
            pruferStep (p.2.1 - 2 * lam * Real.cos (2 * Real.pi * (p.2.2 + (n : ℝ) * p.1)))
              (pruferIter p.1 lam p.2.1 n p.2.2 0) := by
      funext p
      rw [pruferIter_succ]
    rw [hfun]
    have hg : Continuous (fun p : ℝ × ℝ × ℝ =>
        p.2.1 - 2 * lam * Real.cos (2 * Real.pi * (p.2.2 + (n : ℝ) * p.1))) := by fun_prop
    exact Continuous.comp (g := fun q : ℝ × ℝ => pruferStep q.1 q.2) pruferStep_continuous
      (hg.prodMk ih)

theorem pruferIter_antitone_E (α lam : ℝ) (n : ℕ) (x t : ℝ) :
    Antitone (fun E : ℝ => pruferIter α lam E n x t) := by
  intro E₁ E₂ h12
  induction n with
  | zero => simpa [pruferIter_zero]
  | succ n ih =>
    change pruferIter α lam E₂ (n + 1) x t ≤ pruferIter α lam E₁ (n + 1) x t
    rw [pruferIter_succ, pruferIter_succ]
    have h1 : pruferStep (E₂ - 2 * lam * Real.cos (2 * Real.pi * (x + (n : ℝ) * α)))
        (pruferIter α lam E₂ n x t)
        ≤ pruferStep (E₂ - 2 * lam * Real.cos (2 * Real.pi * (x + (n : ℝ) * α)))
          (pruferIter α lam E₁ n x t) :=
      pruferStep_mono _ ih
    have h2 : pruferStep (E₂ - 2 * lam * Real.cos (2 * Real.pi * (x + (n : ℝ) * α)))
          (pruferIter α lam E₁ n x t)
        ≤ pruferStep (E₁ - 2 * lam * Real.cos (2 * Real.pi * (x + (n : ℝ) * α)))
          (pruferIter α lam E₁ n x t) :=
      pruferStep_antitone _ (by linarith)
    linarith

theorem tmR_eq_comp (lam E y : ℝ) :
    tmR lam E y = comp (E - 2 * lam * Real.cos (2 * Real.pi * y)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tmR, comp]

theorem pruferIter_isPosLift (α lam E : ℝ) (n : ℕ) (x : ℝ) :
    IsPosLift (iterR α lam E n x) (fun t => pruferIter α lam E n x t) := by
  induction n with
  | zero =>
    intro t
    show smul (iterR α lam E 0 x) (vc t)
      = ‖smul (iterR α lam E 0 x) (vc t)‖ • vc (pruferIter α lam E 0 x t)
    rw [iterR, pruferIter_zero, smul_one, vc_norm, one_smul]
  | succ n ih =>
    intro t
    show smul (iterR α lam E (n + 1) x) (vc t)
      = ‖smul (iterR α lam E (n + 1) x) (vc t)‖ • vc (pruferIter α lam E (n + 1) x t)
    rw [iterR, pruferIter_succ, tmR_eq_comp]
    exact IsPosLift.comp (comp (E - 2 * lam * Real.cos (2 * Real.pi * (x + (n : ℝ) * α))))
      (iterR α lam E n x)
      (fun s => pruferStep (E - 2 * lam * Real.cos (2 * Real.pi * (x + (n : ℝ) * α))) s)
      (fun s => pruferIter α lam E n x s) (pruferStep_isPosLift _) ih t

end

end Work.TMComp.RotBasics
