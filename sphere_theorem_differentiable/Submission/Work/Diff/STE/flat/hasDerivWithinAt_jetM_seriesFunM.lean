import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.ENormSq_seriesFun_le
import Submission.Work.Diff.STE.pd_seriesFun
import Submission.Work.Diff.STE.flat.hasDerivWithinAt_seriesFunM

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Time differentiation of a matrix-valued Fourier series with a Lipschitz bound, at jet level

The target theorem `hasDerivWithinAt_jetM_seriesFunM` differentiates, at a point `t ∈ [0, τ)`, the
*spatial `2`-jet* of the coefficient-determined Fourier series of a family of coefficient families
`d : ℝ → (Fin n → ℤ) → MatC n`:

`fun s => jetM (seriesFunM (d s)) x`,  with derivative `jetM (seriesFunM d') x`.

`jetM u x = (u x, ∂ᵢ u x, ∂ᵢ∂ⱼ u x)` has three blocks, and each block is *again* a Fourier series of
a coefficient family obtained from `d s` by multiplication with the multiplier of the corresponding
derivatives:

* `seriesFunM (d s) x` — multiplier `1`;
* `pdM i (seriesFunM (d s)) x = seriesFunM (fun k => (2πi kᵢ) · d s k) x` (this is `pd_seriesFun`);
* `pdM i (pdM j (seriesFunM (d s))) x = seriesFunM (fun k => (2πi kᵢ)(2πi kⱼ) · d s k) x`
  (this is `pdList_seriesFun` for the list `[i, j]`).

So the whole content is the *multiplier* form of the entrywise theorem
`hasDerivWithinAt_seriesFunM`: if `mul` is a multiplier with `‖mul k‖ ≤ C ⟨k⟩^m`, `m ≤ 2`, then the
time derivative of `s ↦ seriesFunM (mul · d s ·) x` is `seriesFunM (mul · d' ·) x`, because

* the Lipschitz weight `G` of `d` may be replaced by `C ⟨k⟩² G k`, which is summable by the
  hypothesis `hG2` together with `⟨k⟩^m ≤ ⟨k⟩²`, and
* the summability of the multiplied family follows from the moment hypothesis `hmom` at order `m`.

This is exactly why the target statement carries the moment hypotheses `hmom`, `hmom'` for *every*
`N` (and `hG2` for the *squared* weight): the second-order multipliers need `m = 2`.
-/

namespace Work.Diff.STE.flat

open scoped BigOperators Topology
open Filter
open Work.Diff.STE.Flat (MatC Torus Jet seriesFunM pdM jetM)

set_option maxHeartbeats 1000000

noncomputable section

/-! ## The Fourier multiplier of a coordinate derivative -/

/-- The Fourier multiplier of the partial derivative `∂ᵢ`, as a scalar factor. -/
def mulFac {n : ℕ} (i : Fin n) (k : Fin n → ℤ) : ℂ := 2 * Real.pi * Complex.I * (k i : ℂ)

lemma dmul_eq_mulFac {n : ℕ} (i : Fin n) (c : (Fin n → ℤ) → ℂ) :
    Work.Diff.STE.dmul i c = fun k => mulFac i k * c k := rfl

private lemma norm_ofReal_mul_I (r : ℝ) : ‖((r : ℂ)) * Complex.I‖ = |r| := by simp

lemma norm_mulFac {n : ℕ} (i : Fin n) (k : Fin n → ℤ) :
    ‖mulFac i k‖ = 2 * Real.pi * |((k i : ℤ) : ℝ)| := by
  have h : mulFac i k = (((2 * Real.pi * ((k i : ℤ) : ℝ)) : ℝ) : ℂ) * Complex.I := by
    simp only [mulFac]; push_cast; ring
  rw [h, norm_ofReal_mul_I, abs_mul, abs_mul, abs_of_nonneg Real.pi_nonneg,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]

lemma norm_mulFac_le {n : ℕ} (i : Fin n) (k : Fin n → ℤ) :
    ‖mulFac i k‖ ≤ 2 * Real.pi * Work.Diff.STE.wt k := by
  rw [norm_mulFac]
  exact mul_le_mul_of_nonneg_left (Work.Diff.STE.abs_intCast_le_wt k i) (by positivity)

/-- The norm of the second-order multiplier. -/
lemma norm_mulFac_mul_le {n : ℕ} (i j : Fin n) (k : Fin n → ℤ) :
    ‖mulFac i k * mulFac j k‖ ≤ (2 * Real.pi) ^ 2 * (Work.Diff.STE.wt k) ^ 2 := by
  rw [norm_mul]
  calc ‖mulFac i k‖ * ‖mulFac j k‖
      ≤ (2 * Real.pi * Work.Diff.STE.wt k) * (2 * Real.pi * Work.Diff.STE.wt k) :=
        mul_le_mul (norm_mulFac_le i k) (norm_mulFac_le j k) (norm_nonneg _)
          (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt Real.pi_pos))
            (le_of_lt (Work.Diff.STE.wt_pos k)))
    _ = (2 * Real.pi) ^ 2 * (Work.Diff.STE.wt k) ^ 2 := by ring

/-! ## Summability of a multiplied coefficient family -/

/-- A polynomially bounded multiplier preserves weighted summability of norms. -/
lemma summable_norm_mul_mul_le {n : ℕ} (mul : (Fin n → ℤ) → ℂ) (C : ℝ) (m : ℕ)
    (hmul : ∀ k : Fin n → ℤ, ‖mul k‖ ≤ C * (Work.Diff.STE.wt k) ^ m)
    (d : (Fin n → ℤ) → ℂ)
    (hd : Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ m * ‖d k‖)) :
    Summable (fun k : Fin n → ℤ => ‖mul k * d k‖) := by
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) (hd.mul_left C)
  rw [norm_mul]
  calc ‖mul k‖ * ‖d k‖ ≤ (C * (Work.Diff.STE.wt k) ^ m) * ‖d k‖ :=
        mul_le_mul_of_nonneg_right (hmul k) (norm_nonneg _)
    _ = C * ((Work.Diff.STE.wt k) ^ m * ‖d k‖) := by ring

/-! ## The multiplier form of the term-by-term time differentiation -/

/-- **Time differentiation of a multiplied matrix Fourier series.**  If `‖mul k‖ ≤ C ⟨k⟩^m` with
`m ≤ 2`, then the series with coefficients `mul k · d s k` may be differentiated in `s` at `t` term
by term. -/
lemma hasDerivWithinAt_seriesFunM_mul {n : ℕ} {τ t : ℝ} (hτ : 0 < τ)
    (ht : t ∈ Set.Ico (0 : ℝ) τ) (x : Fin n → ℝ)
    (mul : (Fin n → ℤ) → ℂ) (C : ℝ) (hC : 0 ≤ C) (m : ℕ) (hm : m ≤ 2)
    (hmul : ∀ k : Fin n → ℤ, ‖mul k‖ ≤ C * (Work.Diff.STE.wt k) ^ m)
    (d : ℝ → (Fin n → ℤ) → MatC n)
    (d' : (Fin n → ℤ) → MatC n)
    (G : (Fin n → ℤ) → ℝ) (hG0 : ∀ k, 0 ≤ G k)
    (hG2 : Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ 2 * G k))
    (hmom : ∀ s ∈ Set.Ico (0 : ℝ) τ, ∀ (a b : Fin n),
      Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ m * ‖d s k a b‖))
    (hdiff : ∀ s ∈ Set.Ico (0 : ℝ) τ, ∀ (k : Fin n → ℤ) (a b : Fin n),
      ‖d s k a b - d t k a b‖ ≤ |s - t| * G k)
    (hder : ∀ (k : Fin n → ℤ) (a b : Fin n),
      HasDerivWithinAt (fun s : ℝ => d s k a b) (d' k a b) (Set.Ico (0 : ℝ) τ) t) :
    HasDerivWithinAt
      (fun s : ℝ => seriesFunM (fun k a b => mul k * d s k a b) x)
      (seriesFunM (fun k a b => mul k * d' k a b) x)
      (Set.Ico (0 : ℝ) τ) t := by
  refine hasDerivWithinAt_seriesFunM (τ := τ) (t := t) (x := x) hτ ht
    (fun s k a b => mul k * d s k a b) (fun k a b => mul k * d' k a b)
    (fun k => C * ((Work.Diff.STE.wt k) ^ 2 * G k)) (hG2.mul_left C) ?_ ?_ ?_ ?_
  · intro k
    exact mul_nonneg hC (mul_nonneg (pow_nonneg (Work.Diff.STE.wt_pos k).le 2) (hG0 k))
  · intro s hs k a b
    have hwt : (Work.Diff.STE.wt k) ^ m ≤ (Work.Diff.STE.wt k) ^ 2 :=
      pow_le_pow_right₀ (Work.Diff.STE.wt_one_le k) hm
    have h2 : C * ((Work.Diff.STE.wt k) ^ m * G k) ≤ C * ((Work.Diff.STE.wt k) ^ 2 * G k) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hwt (hG0 k)) hC
    calc ‖mul k * d s k a b - mul k * d t k a b‖
        = ‖mul k‖ * ‖d s k a b - d t k a b‖ := by rw [← mul_sub, norm_mul]
      _ ≤ (C * (Work.Diff.STE.wt k) ^ m) * (|s - t| * G k) :=
          mul_le_mul (hmul k) (hdiff s hs k a b) (norm_nonneg _)
            (mul_nonneg hC (pow_nonneg (Work.Diff.STE.wt_pos k).le m))
      _ = |s - t| * (C * ((Work.Diff.STE.wt k) ^ m * G k)) := by ring
      _ ≤ |s - t| * (C * ((Work.Diff.STE.wt k) ^ 2 * G k)) :=
          mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  · intro a b
    exact summable_norm_mul_mul_le mul C m hmul (fun k => d t k a b) (hmom t ht a b)
  · intro k a b
    exact (hder k a b).const_mul (mul k)

/-! ## `pdM` of a matrix Fourier series -/

/-- The `i`-th partial derivative of a matrix Fourier series, entrywise. -/
lemma pdM_seriesFunM_apply {n : ℕ} (i : Fin n) (χ : (Fin n → ℤ) → MatC n)
    (h : ∀ N : ℕ, ∀ a b : Fin n,
      Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ N * ‖χ k a b‖))
    (x : Fin n → ℝ) (a b : Fin n) :
    pdM i (seriesFunM χ) x a b
      = Work.Diff.STE.seriesFun (fun m => mulFac i m * χ m a b) x := by
  have hkey : pdM i (seriesFunM χ) x a b
      = Work.Diff.STE.seriesFun (Work.Diff.STE.dmul i (fun m => χ m a b)) x := by
    simp only [Work.Diff.STE.Flat.pdM, Work.Diff.STE.Flat.seriesFunM_apply]
    exact Work.Diff.STE.pd_seriesFun i (fun m => χ m a b) (fun N => h N a b) x
  rw [hkey]
  refine tsum_congr (fun k => ?_)
  simp only [Work.Diff.STE.dmul, mulFac]

/-- The `i`-th partial derivative of a matrix Fourier series, as a Fourier series. -/
lemma pdM_seriesFunM_eq {n : ℕ} (i : Fin n) (χ : (Fin n → ℤ) → MatC n)
    (h : ∀ N : ℕ, ∀ a b : Fin n,
      Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ N * ‖χ k a b‖))
    (x : Fin n → ℝ) :
    pdM i (seriesFunM χ) x = seriesFunM (fun k a b => mulFac i k * χ k a b) x :=
  funext (fun a => funext (fun b => pdM_seriesFunM_apply i χ h x a b))

/-- The second mixed partial derivative of a matrix Fourier series, entrywise. -/
lemma pdM_pdM_seriesFunM_apply {n : ℕ} (i j : Fin n) (χ : (Fin n → ℤ) → MatC n)
    (h : ∀ N : ℕ, ∀ a b : Fin n,
      Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ N * ‖χ k a b‖))
    (x : Fin n → ℝ) (a b : Fin n) :
    pdM i (pdM j (seriesFunM χ)) x a b
      = Work.Diff.STE.seriesFun (fun m => (mulFac i m * mulFac j m) * χ m a b) x := by
  have hkey : pdM i (pdM j (seriesFunM χ)) x a b
      = Work.Diff.STE.pdList [i, j] (Work.Diff.STE.seriesFun (fun m => χ m a b)) x := rfl
  rw [hkey, Work.Diff.STE.pdList_seriesFun [i, j] (fun z => χ z a b) (fun N => h N a b) x]
  refine tsum_congr (fun k => ?_)
  simp only [Work.Diff.STE.dmulV, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, mulFac]
/-- The second mixed partial derivative of a matrix Fourier series, as a Fourier series. -/
lemma pdM_pdM_seriesFunM_eq {n : ℕ} (i j : Fin n) (χ : (Fin n → ℤ) → MatC n)
    (h : ∀ N : ℕ, ∀ a b : Fin n,
      Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ N * ‖χ k a b‖))
    (x : Fin n → ℝ) :
    pdM i (pdM j (seriesFunM χ)) x
      = seriesFunM (fun k a b => (mulFac i k * mulFac j k) * χ k a b) x :=
  funext (fun a => funext (fun b => pdM_pdM_seriesFunM_apply i j χ h x a b))

/-! ## The time derivatives of the blocks of the jet -/

/-- The time derivatives of the family of first partial derivatives of `seriesFunM (d s)`. -/
lemma hasDerivWithinAt_pdM_seriesFunM {n : ℕ} {τ t : ℝ} (hτ : 0 < τ)
    (ht : t ∈ Set.Ico (0 : ℝ) τ) (x : Fin n → ℝ) (i : Fin n)
    (d : ℝ → (Fin n → ℤ) → MatC n) (d' : (Fin n → ℤ) → MatC n)
    (G : (Fin n → ℤ) → ℝ) (hG0 : ∀ k, 0 ≤ G k)
    (hG2 : Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ 2 * G k))
    (hmom : ∀ s ∈ Set.Ico (0 : ℝ) τ, ∀ (N : ℕ) (a b : Fin n),
      Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ N * ‖d s k a b‖))
    (hmom' : ∀ (N : ℕ) (a b : Fin n),
      Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ N * ‖d' k a b‖))
    (hdiff : ∀ s ∈ Set.Ico (0 : ℝ) τ, ∀ (k : Fin n → ℤ) (a b : Fin n),
      ‖d s k a b - d t k a b‖ ≤ |s - t| * G k)
    (hder : ∀ (k : Fin n → ℤ) (a b : Fin n),
      HasDerivWithinAt (fun s : ℝ => d s k a b) (d' k a b) (Set.Ico (0 : ℝ) τ) t) :
    HasDerivWithinAt (fun s : ℝ => pdM i (seriesFunM (d s)) x) (pdM i (seriesFunM d') x)
      (Set.Ico (0 : ℝ) τ) t := by
  have hstar : HasDerivWithinAt
      (fun s : ℝ => seriesFunM (fun k a b => mulFac i k * d s k a b) x)
      (seriesFunM (fun k a b => mulFac i k * d' k a b) x) (Set.Ico (0 : ℝ) τ) t :=
    hasDerivWithinAt_seriesFunM_mul hτ ht x (mulFac i) (2 * Real.pi) (by positivity) 1
      (by norm_num : (1 : ℕ) ≤ 2)
      (fun k => by simpa using norm_mulFac_le i k) d d' G hG0 hG2
      (fun s hs a b => by simpa using hmom s hs 1 a b) hdiff hder
  have hgoal := hstar.congr (fun s hs => pdM_seriesFunM_eq i (d s) (hmom s hs) x)
    (pdM_seriesFunM_eq i (d t) (hmom t ht) x)
  rw [← pdM_seriesFunM_eq i d' hmom' x] at hgoal
  exact hgoal

/-- The time derivatives of the family of second mixed partial derivatives of `seriesFunM (d s)`. -/
lemma hasDerivWithinAt_pdM_pdM_seriesFunM {n : ℕ} {τ t : ℝ} (hτ : 0 < τ)
    (ht : t ∈ Set.Ico (0 : ℝ) τ) (x : Fin n → ℝ) (i j : Fin n)
    (d : ℝ → (Fin n → ℤ) → MatC n) (d' : (Fin n → ℤ) → MatC n)
    (G : (Fin n → ℤ) → ℝ) (hG0 : ∀ k, 0 ≤ G k)
    (hG2 : Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ 2 * G k))
    (hmom : ∀ s ∈ Set.Ico (0 : ℝ) τ, ∀ (N : ℕ) (a b : Fin n),
      Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ N * ‖d s k a b‖))
    (hmom' : ∀ (N : ℕ) (a b : Fin n),
      Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ N * ‖d' k a b‖))
    (hdiff : ∀ s ∈ Set.Ico (0 : ℝ) τ, ∀ (k : Fin n → ℤ) (a b : Fin n),
      ‖d s k a b - d t k a b‖ ≤ |s - t| * G k)
    (hder : ∀ (k : Fin n → ℤ) (a b : Fin n),
      HasDerivWithinAt (fun s : ℝ => d s k a b) (d' k a b) (Set.Ico (0 : ℝ) τ) t) :
    HasDerivWithinAt (fun s : ℝ => pdM i (pdM j (seriesFunM (d s))) x)
      (pdM i (pdM j (seriesFunM d')) x) (Set.Ico (0 : ℝ) τ) t := by
  have hstar : HasDerivWithinAt
      (fun s : ℝ => seriesFunM (fun k a b => (mulFac i k * mulFac j k) * d s k a b) x)
      (seriesFunM (fun k a b => (mulFac i k * mulFac j k) * d' k a b) x)
      (Set.Ico (0 : ℝ) τ) t :=
    hasDerivWithinAt_seriesFunM_mul hτ ht x (fun k => mulFac i k * mulFac j k) ((2 * Real.pi) ^ 2)
      (by positivity) 2 le_rfl (fun k => norm_mulFac_mul_le i j k) d d' G hG0 hG2
      (fun s hs a b => by simpa using hmom s hs 2 a b) hdiff hder
  have hgoal := hstar.congr (fun s hs => pdM_pdM_seriesFunM_eq i j (d s) (hmom s hs) x)
    (pdM_pdM_seriesFunM_eq i j (d t) (hmom t ht) x)
  rw [← pdM_pdM_seriesFunM_eq i j d' hmom' x] at hgoal
  exact hgoal

end

theorem hasDerivWithinAt_jetM_seriesFunM {n : ℕ} {τ t : ℝ} (hτ : 0 < τ)
    (ht : t ∈ Set.Ico (0 : ℝ) τ) (x : Fin n → ℝ)
    (d : ℝ → (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n)
    (d' : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n)
    (G : (Fin n → ℤ) → ℝ) (hG : Summable G) (hG0 : ∀ k, 0 ≤ G k)
    (hG2 : Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ 2 * G k))
    (hmom : ∀ s ∈ Set.Ico (0 : ℝ) τ, ∀ (N : ℕ) (a b : Fin n),
      Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ N * ‖d s k a b‖))
    (hmom' : ∀ (N : ℕ) (a b : Fin n),
      Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ N * ‖d' k a b‖))
    (hdiff : ∀ s ∈ Set.Ico (0 : ℝ) τ, ∀ (k : Fin n → ℤ) (a b : Fin n),
      ‖d s k a b - d t k a b‖ ≤ |s - t| * G k)
    (hder : ∀ (k : Fin n → ℤ) (a b : Fin n),
      HasDerivWithinAt (fun s : ℝ => d s k a b) (d' k a b) (Set.Ico (0 : ℝ) τ) t) :
    HasDerivWithinAt
      (fun s : ℝ => Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM (d s)) x)
      (Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM d') x)
      (Set.Ico (0 : ℝ) τ) t := by
  have h1 : HasDerivWithinAt (fun s : ℝ => seriesFunM (d s) x) (seriesFunM d' x)
      (Set.Ico (0 : ℝ) τ) t :=
    hasDerivWithinAt_seriesFunM (τ := τ) (t := t) (x := x) hτ ht d d' G hG hG0
      (fun s hs k a b => hdiff s hs k a b) (fun a b => by simpa using hmom t ht 0 a b)
      (fun k a b => hder k a b)
  have h2 : HasDerivWithinAt (fun s : ℝ => fun i => pdM i (seriesFunM (d s)) x)
      (fun i => pdM i (seriesFunM d') x) (Set.Ico (0 : ℝ) τ) t :=
    hasDerivWithinAt_pi.mpr (fun i =>
      hasDerivWithinAt_pdM_seriesFunM hτ ht x i d d' G hG0 hG2 hmom hmom' hdiff hder)
  have h3 : HasDerivWithinAt (fun s : ℝ => fun i j => pdM i (pdM j (seriesFunM (d s))) x)
      (fun i j => pdM i (pdM j (seriesFunM d')) x) (Set.Ico (0 : ℝ) τ) t :=
    hasDerivWithinAt_pi.mpr (fun i => hasDerivWithinAt_pi.mpr (fun j =>
      hasDerivWithinAt_pdM_pdM_seriesFunM hτ ht x i j d d' G hG0 hG2 hmom hmom' hdiff hder))
  exact h1.prodMk (h2.prodMk h3)

end Work.Diff.STE.flat
