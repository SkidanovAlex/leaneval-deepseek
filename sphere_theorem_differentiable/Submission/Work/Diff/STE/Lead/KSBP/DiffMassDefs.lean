import Mathlib
import Submission.Work.Diff.STE.Lead.KSBP.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The second-difference tower of a coefficient family (vocabulary for `diff_mass_le`)

This file fixes the objects used by the proof of
`Work.Diff.STE.Lead.KSBP.diff_mass_le`: the estimate
`∑' m, ‖diffL l (coef ρ ε) m‖ ≤ C ε^{2|l|} ε^{-n}` for a smooth, compactly supported `ρ`.

Two towers are used, and they agree on the lattice `ε • ℤⁿ`:

* `csdiff2 i h Φ` is the second difference of `Φ` in the coordinate `i` with step `h`,
  `Φ z - 2 Φ (z - h eᵢ) + Φ (z - 2h eᵢ)`, and `cdiffL l h` iterates it over a list `l`;
  `diffL_coef` records that `diffL l (coef ρ ε)` is `cdiffL l ε` applied to `ρ` and read on
  the lattice: `diffL l (coef ρ ε) m = cdiffL l ε ρ (ε • m)`.

* `d1 i Φ = fun z ↦ fderiv ℝ Φ z eᵢ` is the directional derivative, and `dw w` iterates it
  over a list (word) `w` of coordinate directions.  `dw_csdiff2` shows that the two operators
  commute (`dw w (csdiff2 i h Φ) = csdiff2 i h (dw w Φ)`), which is what lets the main estimate
  be proved by induction on the list, the second difference at each step gaining a factor `ε²`
  and the tail losing two directional derivatives.

* `wvec w` is the tuple of coordinate unit vectors indexed by the word `w`; it is used to compare
  `dw` with the Fréchet tower `iteratedFDeriv` (see `norm_dw_le_iteratedFDeriv`).
-/

noncomputable section

open scoped BigOperators

namespace Work.Diff.STE.Lead.KSBP

variable {n : ℕ}

/-! ## The lattice point `ε • m` -/

/-- The point `ε • m` of `ℝⁿ` attached to a lattice point `m`. -/
def sm (ε : ℝ) (m : Fin n → ℤ) : Fin n → ℝ := fun j => ε * (m j : ℝ)

/-- The coercion of a lattice point to `ℝⁿ`. -/
def smc (m : Fin n → ℤ) : Fin n → ℝ := fun j => (m j : ℝ)

lemma sm_eq_smul (ε : ℝ) (m : Fin n → ℤ) : sm ε m = ε • smc m := rfl

lemma smc_sub (m c : Fin n → ℤ) : smc (m - c) = smc m - fun j => (c j : ℝ) := by
  funext j; simp [smc, Pi.sub_apply]

lemma sm_sub (ε : ℝ) (m c : Fin n → ℤ) :
    sm ε (m - c) = sm ε m - fun j => ε * (c j : ℝ) := by
  rw [sm_eq_smul, smc_sub, sm_eq_smul, smul_sub]; congr 1

lemma sm_sub_two (ε : ℝ) (i : Fin n) (m : Fin n → ℤ) :
    sm ε (m - (2 : ℤ) • Pi.single i (1 : ℤ)) = sm ε m - Pi.single i (2 * ε) := by
  rw [sm_sub]; congr 1; funext j
  by_cases h : j = i
  · subst h; simp [Pi.smul_apply, Pi.single_eq_same]; ring
  · simp [Pi.smul_apply, h]

lemma sm_sub_one (ε : ℝ) (i : Fin n) (m : Fin n → ℤ) :
    sm ε (m - Pi.single i (1 : ℤ)) = sm ε m - Pi.single i ε := by
  rw [sm_sub]; congr 1; funext j
  by_cases h : j = i
  · subst h; simp [Pi.single_eq_same]
  · simp [h]

/-! ## The continuous second-difference tower -/

/-- The second difference of `Φ` in the coordinate `i` with step `h`:
`Φ z - 2 Φ (z - h eᵢ) + Φ (z - 2h eᵢ)`. -/
def csdiff2 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (i : Fin n) (h : ℝ) (Φ : (Fin n → ℝ) → F) : (Fin n → ℝ) → F :=
  fun z => Φ z - (2 : ℝ) • Φ (z - Pi.single i h) + Φ (z - Pi.single i (2 * h))

lemma csdiff2_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (i : Fin n) (h : ℝ) (Φ : (Fin n → ℝ) → F) :
    csdiff2 i h Φ = Φ - (2 : ℝ) • (fun z => Φ (z - Pi.single i h))
      + (fun z => Φ (z - Pi.single i (2 * h))) := rfl

lemma csdiff2_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (i : Fin n) (h : ℝ) (Φ : (Fin n → ℝ) → F) (z : Fin n → ℝ) :
    csdiff2 i h Φ z = Φ z - (2 : ℝ) • Φ (z - Pi.single i h)
      + Φ (z - Pi.single i (2 * h)) := rfl

/-- The iterated second difference along a list of coordinates. -/
def cdiffL {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (l : List (Fin n)) (h : ℝ) (Φ : (Fin n → ℝ) → F) : (Fin n → ℝ) → F :=
  l.foldr (fun i b => csdiff2 i h b) Φ

@[simp] lemma cdiffL_nil {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (h : ℝ) (Φ : (Fin n → ℝ) → F) : cdiffL ([] : List (Fin n)) h Φ = Φ := rfl

lemma cdiffL_cons {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (i : Fin n) (l : List (Fin n)) (h : ℝ) (Φ : (Fin n → ℝ) → F) :
    cdiffL (i :: l) h Φ = csdiff2 i h (cdiffL l h Φ) := rfl

/-- **The lattice identity**: the iterated second difference of the coefficient family is the
continuous iterated second difference of `ρ`, read on the lattice. -/
theorem diff2_sm (Ψ : (Fin n → ℝ) → ℂ) (ε : ℝ) (i : Fin n) (m : Fin n → ℤ) :
    diff2 i (fun m => Ψ (sm ε m)) m = csdiff2 i ε Ψ (sm ε m) := by
  rw [diff2, csdiff2]
  rw [sm_sub_two, sm_sub_one]
  rw [RCLike.real_smul_eq_coe_mul]
  norm_num
  abel

/-- `diffL l (coef ρ ε)` is the `l`-fold second difference of `ρ` read on the lattice
`ε • ℤⁿ`. -/
theorem diffL_coef (ρ : (Fin n → ℝ) → ℝ) (ε : ℝ) (l : List (Fin n)) (m : Fin n → ℤ) :
    diffL l (coef ρ ε) m = cdiffL l ε (fun y => (ρ y : ℂ)) (sm ε m) := by
  induction l generalizing m with
  | nil => rfl
  | cons i l ih =>
      show diff2 i (diffL l (coef ρ ε)) m
        = csdiff2 i ε (cdiffL l ε (fun y => (ρ y : ℂ))) (sm ε m)
      rw [show diffL l (coef ρ ε)
            = fun m => cdiffL l ε (fun y => (ρ y : ℂ)) (sm ε m) from funext ih]
      exact diff2_sm _ ε i m

/-! ## The directional-derivative tower -/

/-- The directional derivative along the coordinate `i`: `Φ ↦ (z ↦ DΦ(z)(eᵢ))`. -/
def d1 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (i : Fin n) (Φ : (Fin n → ℝ) → F) : (Fin n → ℝ) → F :=
  fun z => fderiv ℝ Φ z (Pi.single i (1 : ℝ))

/-- The iterated directional derivative along a word `w` of coordinate directions. -/
def dw {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (w : List (Fin n)) (Φ : (Fin n → ℝ) → F) : (Fin n → ℝ) → F :=
  w.foldr (fun i b => d1 i b) Φ

@[simp] lemma dw_nil {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : (Fin n → ℝ) → F) : dw ([] : List (Fin n)) Φ = Φ := rfl

lemma dw_cons {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (i : Fin n) (w : List (Fin n)) (Φ : (Fin n → ℝ) → F) :
    dw (i :: w) Φ = d1 i (dw w Φ) := rfl

lemma dw_append {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (w w' : List (Fin n)) (Φ : (Fin n → ℝ) → F) :
    dw (w ++ w') Φ = dw w (dw w' Φ) := by
  simp only [dw, List.foldr_append]

/-- The tuple of coordinate unit vectors indexed by a word, used to evaluate an iterated
Fréchet derivative along the directions of the word. -/
def wvec (w : List (Fin n)) : Fin w.length → (Fin n → ℝ) :=
  fun j => Pi.single (w.get j) (1 : ℝ)

@[simp] lemma wvec_cons_zero (i : Fin n) (w : List (Fin n)) :
    wvec (i :: w) 0 = Pi.single i (1 : ℝ) := by simp [wvec]

@[simp] lemma wvec_cons_tail (i : Fin n) (w : List (Fin n)) :
    Fin.tail (wvec (i :: w)) = wvec w := by
  funext j; simp [wvec, Fin.tail]

/-! ## Smoothness -/

lemma contDiff_sub_const (c : Fin n → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℝ => z - c) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℝ => z) := contDiff_id
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Fin n → ℝ => c) := contDiff_const
  exact h1.sub h2

lemma contDiff_shift {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : (Fin n → ℝ) → F} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (c : Fin n → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℝ => Φ (z - c)) :=
  hΦ.comp (contDiff_sub_const c)

lemma contDiff_csdiff2 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : (Fin n → ℝ) → F} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (i : Fin n) (h : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (csdiff2 i h Φ) := by
  have h1 := contDiff_shift (Φ := Φ) hΦ (Pi.single i h)
  have h2 := contDiff_shift (Φ := Φ) hΦ (Pi.single i (2 * h))
  show ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℝ =>
    Φ z - (2 : ℝ) • Φ (z - Pi.single i h) + Φ (z - Pi.single i (2 * h)))
  exact (hΦ.sub (h1.const_smul (2 : ℝ))).add h2

lemma contDiff_d1 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : (Fin n → ℝ) → F} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (i : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (d1 i Φ) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ Φ) := hΦ.fderiv_right (by simp)
  have h2 := (ContinuousLinearMap.contDiff
      (ContinuousLinearMap.apply ℝ F (Pi.single i (1 : ℝ)))).comp h
  have h3 : (⇑((ContinuousLinearMap.apply ℝ F) (Pi.single i (1 : ℝ))) ∘ fderiv ℝ Φ)
      = fun z : Fin n → ℝ => fderiv ℝ Φ z (Pi.single i (1 : ℝ)) := by
    funext z; simp [Function.comp, ContinuousLinearMap.apply_apply]
  rw [h3] at h2
  show ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℝ => fderiv ℝ Φ z (Pi.single i (1 : ℝ)))
  exact h2

lemma contDiff_cdiffL {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (l : List (Fin n)) {Φ : (Fin n → ℝ) → F} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (h : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (cdiffL l h Φ) := by
  induction l with
  | nil => simpa using hΦ
  | cons i l ih => rw [cdiffL_cons]; exact contDiff_csdiff2 ih i h

lemma contDiff_dw {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (w : List (Fin n)) {Φ : (Fin n → ℝ) → F} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    ContDiff ℝ (⊤ : ℕ∞) (dw w Φ) := by
  induction w with
  | nil => simpa using hΦ
  | cons i w ih => rw [dw_cons]; exact contDiff_d1 ih i

/-! ## Commutation of the two towers -/

/-- The derivative of a translate of a function is the translate of the derivative. -/
lemma fderiv_shift {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : (Fin n → ℝ) → F) (c z : Fin n → ℝ) :
    fderiv ℝ (fun z => Φ (z - c)) z = fderiv ℝ Φ (z - c) := by
  rw [sub_eq_add_neg]
  exact fderiv_comp_add_right (-c)

lemma differentiableAt_shift {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : (Fin n → ℝ) → F} (hΦ : Differentiable ℝ Φ) (c z : Fin n → ℝ) :
    DifferentiableAt ℝ (fun z => Φ (z - c)) z :=
  hΦ.differentiableAt.comp z ((differentiableAt_id (𝕜 := ℝ) (x := z)).sub_const c)

/-- The derivative of a second difference is the second difference of the derivative. -/
lemma fderiv_csdiff2 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : (Fin n → ℝ) → F) (hΦ : Differentiable ℝ Φ) (i : Fin n) (h : ℝ) :
    fderiv ℝ (csdiff2 i h Φ) = fun z =>
      fderiv ℝ Φ z - (2 : ℝ) • fderiv ℝ (fun z => Φ (z - Pi.single i h)) z
        + fderiv ℝ (fun z => Φ (z - Pi.single i (2 * h))) z := by
  funext z
  have hΦz : DifferentiableAt ℝ Φ z := hΦ.differentiableAt
  have h1 : DifferentiableAt ℝ (fun z => Φ (z - Pi.single i h)) z := differentiableAt_shift hΦ _ z
  have h2 : DifferentiableAt ℝ (fun z => Φ (z - Pi.single i (2 * h))) z :=
    differentiableAt_shift hΦ _ z
  rw [csdiff2_eq]
  rw [fderiv_add (hΦz.sub (h1.const_smul (2 : ℝ))) h2,
      fderiv_sub hΦz (h1.const_smul (2 : ℝ)),
      fderiv_const_smul h1 (2 : ℝ)]

/-- Directional derivatives commute with second differences. -/
lemma d1_csdiff2 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : (Fin n → ℝ) → F) (hΦ : Differentiable ℝ Φ) (i j : Fin n) (h : ℝ) :
    d1 j (csdiff2 i h Φ) = csdiff2 i h (d1 j Φ) := by
  funext z
  rw [d1, csdiff2_apply, fderiv_csdiff2 Φ hΦ i h]
  simp only [d1, sub_apply, add_apply, smul_apply, fderiv_shift]

/-- The whole directional-derivative tower commutes with the second-difference tower. -/
lemma dw_csdiff2 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (w : List (Fin n)) {Φ : (Fin n → ℝ) → F} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (i : Fin n) (h : ℝ) :
    dw w (csdiff2 i h Φ) = csdiff2 i h (dw w Φ) := by
  induction w with
  | nil => rfl
  | cons j w ih =>
      rw [dw_cons, ih, show csdiff2 i h (dw (j :: w) Φ) = csdiff2 i h (d1 j (dw w Φ)) from by
        rw [dw_cons]]
      have hd : Differentiable ℝ (dw w Φ) := (contDiff_dw w hΦ).differentiable (by simp)
      exact d1_csdiff2 (dw w Φ) hd i j h

end Work.Diff.STE.Lead.KSBP
