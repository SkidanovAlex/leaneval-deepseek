import Mathlib
import Submission.Work.WilG4c.CritAux.HypoDefs
import Submission.Work.WilG4c.CritAux
import Submission.Work.WilG0.projLastIter_eq
import Submission.Work.WilG0.snocIt_natAdd
import Submission.Work.WilG0.snocIt_castAdd

namespace Work.WilG4cR

/-! ## The bookkeeping lemmas

Everything below is proved from the definitions, without touching the `sorry`-stubs
`Work.WilkG4c.CritAux.hypoRaw_eq_hypoRawE`, `Work.WilkG4c.CritAux.hypoBuild_eq_hypoRawE`.
-/

/-! ### Coordinate bookkeeping for `(x, r, y) ↦ (parPt x, y)` -/

/-- `Work.WilG0.snocIt` is the same gluing as `Fin.append`: it puts `x` in front and `w` at the
end. -/
theorem snocIt_eq_append (n m : ℕ) (x : Fin n → ℝ) (w : Fin m → ℝ) :
    Work.WilG0.snocIt n m x w = Fin.append x w := by
  funext k
  refine Fin.addCases (motive := fun k => Work.WilG0.snocIt n m x w k = Fin.append x w k) ?_ ?_ k
  · intro i
    rw [Work.WilG0.snocIt_castAdd, Fin.append_left]
  · intro j
    rw [Work.WilG0.snocIt_natAdd, Fin.append_right]

/-- The substitution `iotaA` reads the glued vector `(x, t, y)` as `(parPt x, y)`. -/
theorem iotaA_comp (p n : ℕ) (x : Fin (p + (n + 1)) → ℝ) (t : ℝ) (y : Fin (n + 1) → ℝ) :
    (Fin.append (Fin.snoc x t) y) ∘ Work.WilkG4c.iotaA p n
      = Fin.append (Work.WilkG4c.parPt x) y := by
  funext i
  refine Fin.addCases (motive := fun i =>
      ((Fin.append (Fin.snoc x t) y) ∘ Work.WilkG4c.iotaA p n) i
        = Fin.append (Work.WilkG4c.parPt x) y i) ?_ ?_ i
  · intro i'
    show Fin.append (Fin.snoc x t) y (Work.WilkG4c.iotaA p n (Fin.castAdd (n + 1) i'))
        = Fin.append (Work.WilkG4c.parPt x) y (Fin.castAdd (n + 1) i')
    simp only [Work.WilkG4c.iotaA, Fin.append_left, Fin.snoc_castSucc, Work.WilkG4c.parPt_apply]
  · intro j
    show Fin.append (Fin.snoc x t) y (Work.WilkG4c.iotaA p n (Fin.natAdd p j))
        = Fin.append (Work.WilkG4c.parPt x) y (Fin.natAdd p j)
    simp only [Work.WilkG4c.iotaA, Fin.append_right]

/-- The value of the ball polynomial at the glued vector `(x, t, y)` is `t² - Σ(y_j - z_j)²`,
where `z = cubePt x` is the fibre point. -/
theorem eval_ballP (p n : ℕ) (x : Fin (p + (n + 1)) → ℝ) (t : ℝ) (y : Fin (n + 1) → ℝ) :
    MvPolynomial.eval (Fin.append (Fin.snoc x t) y) (Work.WilkG4c.ballP p n)
      = t ^ 2 - ∑ j : Fin (n + 1), (y j - Work.WilkG4c.cubePt x j) ^ 2 := by
  simp only [Work.WilkG4c.ballP, MvPolynomial.eval_sub, MvPolynomial.eval_pow,
    MvPolynomial.eval_X, MvPolynomial.eval_sum, Fin.append_left, Fin.append_right,
    Fin.snoc_last, Fin.snoc_castSucc, Work.WilkG4c.cubePt_apply]

/-- Unfolding of the pullback set `HypoA`. -/
theorem mem_HypoA {p n : ℕ} {X : Set (Fin (p + (n + 1)) → ℝ)}
    {w : Fin (Work.WilkG4c.hypoM p n) → ℝ} :
    (w ∈ Work.WilkG4c.HypoA p n X) ↔ ¬ (w ∘ Work.WilkG4c.iotaA p n ∈ X) := Iff.rfl

/-- Unfolding of the positivity locus `HypoBall`. -/
theorem mem_HypoBall {p n : ℕ} {w : Fin (Work.WilkG4c.hypoM p n) → ℝ} :
    (w ∈ Work.WilkG4c.HypoBall p n) ↔ 0 < MvPolynomial.eval w (Work.WilkG4c.ballP p n) :=
  Iff.rfl

/-- A point of `ℝ^{p+(n+1)}` is the gluing of its parameter and cube parts. -/
theorem append_parPt_cubePt {p n : ℕ} (w : Fin (p + (n + 1)) → ℝ) :
    Fin.append (Work.WilkG4c.parPt w) (Work.WilkG4c.cubePt w) = w := by
  funext k
  refine Fin.addCases (motive := fun k =>
    Fin.append (Work.WilkG4c.parPt w) (Work.WilkG4c.cubePt w) k = w k) ?_ ?_ k
  · intro i
    simp only [Work.WilkG4c.parPt_apply, Fin.append_left]
  · intro j
    simp only [Work.WilkG4c.cubePt_apply, Fin.append_right]

/-! ### `HypoRaw = HypoRawE`: sup-ball versus Euclidean ball -/

/-- A Euclidean ball of radius `ρ` around `cubePt u` sits inside the sup ball of radius `ρ`
around `u` (sup norm is bounded by the `ℓ²` norm). -/
theorem hypoRaw_subset_hypoRawE (p n : ℕ) (X : Set (Fin (p + (n + 1)) → ℝ)) :
    Work.WilkG4c.HypoRaw p n X ⊆ Work.WilkG4c.HypoRawE p n X := by
  intro u hu
  rw [Work.WilkG4c.mem_HypoRaw] at hu
  obtain ⟨ρ, hρ, hball⟩ := hu
  refine ⟨ρ, hρ, ?_⟩
  intro y hy
  have hdist : dist y (Work.WilkG4c.cubePt u) < ρ := by
    rw [dist_pi_lt_iff hρ]
    intro j
    rw [Real.dist_eq]
    have h1 : (y j - Work.WilkG4c.cubePt u j) ^ 2 ≤
        ∑ i : Fin (n + 1), (y i - Work.WilkG4c.cubePt u i) ^ 2 :=
      Finset.single_le_sum (f := fun i => (y i - Work.WilkG4c.cubePt u i) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    have h2 : (y j - Work.WilkG4c.cubePt u j) ^ 2 < ρ ^ 2 := lt_of_le_of_lt h1 hy
    have h3 : |y j - Work.WilkG4c.cubePt u j| < |ρ| := sq_lt_sq.mp h2
    rwa [abs_of_pos hρ] at h3
  have hpar : Work.WilkG4c.parPt (Fin.append (Work.WilkG4c.parPt u) y)
      = Work.WilkG4c.parPt u := by
    funext i
    simp only [Work.WilkG4c.parPt_apply, Fin.append_left]
  have hcube : Work.WilkG4c.cubePt (Fin.append (Work.WilkG4c.parPt u) y) = y := by
    funext j
    simp only [Work.WilkG4c.cubePt_apply, Fin.append_right]
  exact hball (Fin.append (Work.WilkG4c.parPt u) y) hpar (by rwa [hcube])

/-- The sup ball of radius `r/(n+1)` sits inside the Euclidean ball of radius `r`. -/
theorem hypoRawE_subset_hypoRaw (p n : ℕ) (X : Set (Fin (p + (n + 1)) → ℝ)) :
    Work.WilkG4c.HypoRawE p n X ⊆ Work.WilkG4c.HypoRaw p n X := by
  intro u hu
  obtain ⟨r, hr, hball⟩ := hu
  have hρ : 0 < r / ((n + 1 : ℕ) : ℝ) := by positivity
  refine ⟨r / ((n + 1 : ℕ) : ℝ), hρ, ?_⟩
  intro w' hpar hdist
  have h1 : ∀ j : Fin (n + 1),
      (Work.WilkG4c.cubePt w' j - Work.WilkG4c.cubePt u j) ^ 2
        < (r / ((n + 1 : ℕ) : ℝ)) ^ 2 := by
    intro j
    have h2 : dist (Work.WilkG4c.cubePt w' j) (Work.WilkG4c.cubePt u j)
        < r / ((n + 1 : ℕ) : ℝ) :=
      (dist_pi_lt_iff hρ).mp hdist j
    rw [Real.dist_eq] at h2
    refine sq_lt_sq.mpr ?_
    rw [abs_of_pos hρ]
    exact h2
  have hcard : ∑ _j : Fin (n + 1), (r / ((n + 1 : ℕ) : ℝ)) ^ 2
      = ((n + 1 : ℕ) : ℝ) * (r / ((n + 1 : ℕ) : ℝ)) ^ 2 := by
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h4 : ∑ j : Fin (n + 1),
        (Work.WilkG4c.cubePt w' j - Work.WilkG4c.cubePt u j) ^ 2
      < ((n + 1 : ℕ) : ℝ) * (r / ((n + 1 : ℕ) : ℝ)) ^ 2 := by
    rw [← hcard]
    exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun j _ => h1 j)
  have h5 : ((n + 1 : ℕ) : ℝ) * (r / ((n + 1 : ℕ) : ℝ)) ^ 2 ≤ r ^ 2 := by
    have hc : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hcpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have heq : ((n + 1 : ℕ) : ℝ) * (r / ((n + 1 : ℕ) : ℝ)) ^ 2
        = r ^ 2 / ((n + 1 : ℕ) : ℝ) := by
      field_simp
    rw [heq, div_le_iff₀ hcpos]
    nlinarith [sq_nonneg r]
  have hsum := lt_of_lt_of_le h4 h5
  have hX := hball (Work.WilkG4c.cubePt w') hsum
  rw [← append_parPt_cubePt w', hpar]
  exact hX

/-! ### `HypoBuild = HypoRawE`: unfolding the construction -/

/-- The `Ω`-construction `HypoBuild`, written out: `x` lies in it iff there is a radius `t > 0`
with the whole Euclidean fibre ball of radius `t` around `x` contained in `X`. -/
theorem hypoBuild_eq_HypoRawE (p n : ℕ) (X : Set (Fin (p + (n + 1)) → ℝ)) :
    Work.WilkG4c.HypoBuild p n X = Work.WilkG4c.HypoRawE p n X := by
  ext x
  have key : (x ∈ Work.WilkG4c.HypoBuild p n X) ↔ ∃ t : ℝ, 0 < t ∧ ∀ y : Fin (n + 1) → ℝ,
        (∑ j : Fin (n + 1), (y j - Work.WilkG4c.cubePt x j) ^ 2 < t ^ 2) →
          Fin.append (Work.WilkG4c.parPt x) y ∈ X := by
    simp only [Work.WilkG4c.HypoBuild, Work.WilkG4c.hypoN, WilkiesDesign.projLast,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨t, ht⟩
      rw [Set.mem_inter_iff, Set.mem_compl_iff, Work.WilG0.projLastIter_eq] at ht
      simp only [Set.mem_ofPred_eq, Fin.snoc_last] at ht
      obtain ⟨hnot, hpos⟩ := ht
      refine ⟨t, hpos, fun y hy => ?_⟩
      have hz : ¬ (Work.WilG0.snocIt (p + (n + 1) + 1) (n + 1) (Fin.snoc x t) y
          ∈ Work.WilkG4c.HypoA p n X ∩ Work.WilkG4c.HypoBall p n) :=
        fun hcon => hnot ⟨y, hcon⟩
      rw [Set.mem_inter_iff, not_and_or] at hz
      rcases hz with hA | hB
      · have hzA : (Work.WilG0.snocIt (p + (n + 1) + 1) (n + 1) (Fin.snoc x t) y)
            ∘ Work.WilkG4c.iotaA p n ∈ X := by
          simp only [mem_HypoA, not_not] at hA
          exact hA
        rwa [snocIt_eq_append, iotaA_comp p n x t y] at hzA
      · have hzB : ¬ (0 < t ^ 2 - ∑ j : Fin (n + 1),
            (y j - Work.WilkG4c.cubePt x j) ^ 2) := by
          simp only [mem_HypoBall] at hB
          rwa [snocIt_eq_append, eval_ballP p n x t y] at hB
        exact absurd (sub_pos.mpr hy) hzB
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_, ?_⟩
      · rw [Set.mem_compl_iff, Work.WilG0.projLastIter_eq]
        simp only [Set.mem_ofPred_eq]
        intro hcon
        obtain ⟨y, hy⟩ := hcon
        rw [Set.mem_inter_iff] at hy
        obtain ⟨hA, hB⟩ := hy
        have hAz : ¬ (Fin.append (Work.WilkG4c.parPt x) y ∈ X) := by
          have h := hA
          simp only [mem_HypoA] at h
          rwa [snocIt_eq_append, iotaA_comp p n x t y] at h
        have hBz : 0 < t ^ 2 - ∑ j : Fin (n + 1),
            (y j - Work.WilkG4c.cubePt x j) ^ 2 := by
          have h := hB
          simp only [mem_HypoBall] at h
          rwa [snocIt_eq_append, eval_ballP p n x t y] at h
        exact hAz (ht.2 y (sub_pos.mp hBz))
      · simpa using ht.1
  rw [key]
  simp only [Work.WilkG4c.HypoRawE, Set.mem_ofPred_eq]

/-- **The ball-condensation operator equals its `Ω`-construction.**

`Work.WilkG4c.HypoRaw p n X` (defined in `Submission/Work/WilG4c/CritAux.lean`) is the set of
`u : ℝ^{p+(n+1)}` such that some *fibre* ball around `u` — with the parameter `parPt u` held
fixed, in the sup metric: `dist (cubePt w') (cubePt u) < ρ` — is contained in `X`.

`Work.WilkG4c.HypoBuild p n X` (`CritAux/HypoDefs.lean`) is the pure `Ω`-construction: pull back
`Xᶜ` along `(x,r,y) ↦ (parPt x, y)`, intersect with the *Euclidean* ball condition
`0 < r^2 - Σ_j (y_j - z_j)^2`, project the `y`-block away, complement, record `r > 0`, project `r`
away.  `Work.WilkG4c.HypoRawE p n X` is the intermediate Euclidean-ball description.

The equality decomposes into the two easy bookkeeping steps

* `HypoRaw = HypoRawE`: sup-ball vs. Euclidean-ball (`Fin N`-sup norm vs. ℓ²), using
  `dist_pi_lt_iff` / `Real.dist_eq` — a Euclidean ball of radius `r` sits in the sup ball of
  radius `r`, and contains the sup ball of radius `r/√(n+1)`;
* `HypoBuild = HypoRawE`: unfolding the complement/projection construction
  (`projLast`, `Work.WilG0.projLastIter`, `Work.WilG0.projLastIter_eq`) into the explicit
  `∃ r > 0, ∀ y, ...` form (`snocIt`, `iotaA`, `ballP`).

The `Ω`-membership of `HypoBuild` itself is already proved as
`Work.WilkG4c.CritAux.HypoBuild_mem` (in `CritAux/hypoRaw_mem.lean`, `sorry`-free), so this
equality is exactly the missing step for `Work.WilkG4c.CritAux.hypoRaw_mem`.

**Do not use** the `sorry`-stubs `Work.WilkG4c.CritAux.hypoRaw_eq_hypoRawE`,
`Work.WilkG4c.CritAux.hypoBuild_eq_hypoRawE`, `Work.WilkG4c.CritAux.hypoRaw_mem` (they contain
`sorry` and would poison the proof).  Prove the equality from the definitions. -/
theorem HypoRaw_eq_HypoBuild (p n : ℕ) (X : Set (Fin (p + (n + 1)) → ℝ)) :
    Work.WilkG4c.HypoRaw p n X = Work.WilkG4c.HypoBuild p n X := by
  rw [hypoBuild_eq_HypoRawE p n X]
  exact Set.Subset.antisymm (hypoRaw_subset_hypoRawE p n X) (hypoRawE_subset_hypoRaw p n X)

end Work.WilG4cR
