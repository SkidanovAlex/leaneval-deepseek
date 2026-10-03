/-
# The exact-height fibre vocabulary of the small-scale model operator

This module collects the *exact-height* (`diffFreqs`) counterparts of the fibre objects of
`A7/LargeInterface.lean` and the elementary identities that the §7 single-scale estimate needs:

* `arithCharD ρ l` — the arithmetic character of the exact-height frequency set
  `(ℚ/ℤ)_l = diffFreqs ρ l`;
* `smallArithKernel_eq_arithCharD` / `smallArithKernel_fiberTerm` — the factorisation of the
  exact-height arithmetic kernel as an average over the residues `n ∈ ℤ/qℤ` of products of the two
  arithmetic characters (the `form-1` identity of the paper, in the exact-height convention of the
  contract's pieces `Fpiece`, `Gpiece`);
* `fiberOpD`, `fiberOpPD` — the two exact-height *fibres*;
* `smallBtwist_eq_fiberSumD` — `smallBtwist` as the average of the products of the two fibres;
* `fiberOpD_eq_charSum` — the fibre as the arithmetic Fourier synthesis of the window pieces.

The exact-height convention (`diffFreqs ρ l = (ℚ/ℤ)_{≤l} \ (ℚ/ℤ)_{≤l-1}` for `l ≥ 1`, and
`diffFreqs ρ 0 = (ℚ/ℤ)_{≤0}`) is the one of the contract's pieces, hence of `smallBtwist` and of
the model operator `smallModelOp`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.SmallModelDefs
import Submission.Work.KMTAreas.A7.BilinOpLp
import Submission.Work.KMTAreas.A7.residueLp_mul_le

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

/-- **The exact-height arithmetic character**: the inverse Fourier transform of the exact-height
frequency set `diffFreqs ρ l`, i.e. `y ↦ ∑_{α ∈ (ℚ/ℤ)_l} e(α y)` where `(ℚ/ℤ)_l = diffFreqs ρ l`
is the set of arithmetic frequencies of exact height `2^l` (with `(ℚ/ℤ)_0 = {0}`). -/
noncomputable def arithCharD (ρ : ℝ) (l : ℕ) (y : ℤ) : ℂ :=
  ∑ α ∈ diffFreqs ρ l, fourier (T := 1) y α

/-- **Factorisation of the exact-height arithmetic kernel.**  The `q`-th arithmetic kernel of the
exact-height twisted bilinear multiplier is the average over the residues `n` of `q` of the
products of the two exact-height arithmetic character factors:

  `smallArithKernel ρ P q l₁ l₂ j₁ j₂ = q⁻¹ ∑_{n < q} C₁(n - j₁) C₂(P(n) - j₂)`,

where `Cᵢ = arithCharD ρ lᵢ`.  This is the exact-height counterpart of
`arithKernel_eq_arithChar`; the proof is identical, only the frequency finsets change. -/
theorem smallArithKernel_eq_arithCharD (ρ : ℝ) (P : Polynomial ℤ) (q : ℕ) (l₁ l₂ : ℕ) (j₁ j₂ : ℤ) :
    smallArithKernel ρ P q l₁ l₂ j₁ j₂
      = (q : ℂ)⁻¹ * ∑ n ∈ Finset.range q,
          arithCharD ρ l₁ ((n : ℤ) - j₁) * arithCharD ρ l₂ (P.eval (n : ℤ) - j₂) := by
  classical
  unfold smallArithKernel mZ arithCharD
  have hpt : ∀ (α₁ α₂ : Work.Analysis.IonescuWainger.Circle),
      ((↑q)⁻¹ * ∑ n ∈ Finset.range q,
          (fourier (T:=1) (↑n)) α₁ * (fourier (T:=1) (eval (↑n) P)) α₂)
          * (fourier (T:=1) (-j₁)) α₁ * (fourier (T:=1) (-j₂)) α₂
        = (↑q)⁻¹ * ∑ n ∈ Finset.range q,
            (fourier (T:=1) ((↑n) - j₁)) α₁ * (fourier (T:=1) (eval (↑n) P - j₂)) α₂ := by
    intro α₁ α₂
    have hf1 : ∀ n : ℕ, (fourier (T:=1) (↑n : ℤ)) α₁ * (fourier (T:=1) (-j₁)) α₁
        = (fourier (T:=1) ((↑n : ℤ) - j₁)) α₁ := by
      intro n
      rw [show ((n:ℤ) - j₁) = (n:ℤ) + (-j₁) by ring, fourier_add]
    have hf2 : ∀ n : ℕ, (fourier (T:=1) (eval (↑n) P)) α₂ * (fourier (T:=1) (-j₂)) α₂
        = (fourier (T:=1) (eval (↑n) P - j₂)) α₂ := by
      intro n
      rw [show (eval (↑n) P - j₂) = (eval (↑n) P) + (-j₂) by ring, fourier_add]
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← hf1 n, ← hf2 n]
    ring
  rw [Finset.sum_congr rfl (fun α₁ _ => Finset.sum_congr rfl (fun α₂ _ => hpt α₁ α₂))]
  rw [const_sum_three (diffFreqs ρ l₁) (diffFreqs ρ l₂) (Finset.range q) ((↑q)⁻¹)
      (fun α₁ α₂ n =>
        (fourier (T:=1) ((↑n:ℤ) - j₁)) α₁ * (fourier (T:=1) (eval (↑n) P - j₂)) α₂)]
  rw [Finset.mul_sum (Finset.range q) (fun n =>
      (∑ α₁ ∈ diffFreqs ρ l₁, (fourier (T:=1) ((↑n:ℤ) - j₁)) α₁)
        * (∑ α₂ ∈ diffFreqs ρ l₂, (fourier (T:=1) (eval (↑n) P - j₂)) α₂)) ((↑q)⁻¹)]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [Finset.sum_mul_sum (diffFreqs ρ l₁) (diffFreqs ρ l₂)
      (fun α₁ => (fourier (T:=1) ((↑n:ℤ) - j₁)) α₁)
      (fun α₂ => (fourier (T:=1) (eval (↑n) P - j₂)) α₂)]
  rw [Finset.mul_sum (diffFreqs ρ l₁) (fun α₁ => ∑ α₂ ∈ diffFreqs ρ l₂,
        (fourier (T:=1) ((↑n:ℤ) - j₁)) α₁ * (fourier (T:=1) (eval (↑n) P - j₂)) α₂) ((↑q)⁻¹)]
  rw [Finset.sum_congr rfl (fun α₁ _ => Finset.mul_sum (diffFreqs ρ l₂)
      (fun α₂ => (fourier (T:=1) ((↑n:ℤ) - j₁)) α₁
        * (fourier (T:=1) (eval (↑n) P - j₂)) α₂) ((↑q)⁻¹))]

/-- **Fibre form of the kernel of `smallBtwist`.**  The kernel of the exact-height twisted bilinear
multiplier is the average over the residues `n ∈ ℤ/qℤ` of the products of the two exact-height
arithmetic factors attached to `(j₁,j₂)`; this is
`smallArithKernel_eq_arithCharD` with the constants `cw mᵢ jᵢ`, `h (x-j₁)`, `k (x-j₂)`
distributed over the finite sum. -/
theorem smallArithKernel_fiberTerm (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (h k : ℤ → ℂ) (x j₁ j₂ : ℤ) :
    smallArithKernel ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ j₁ j₂ * cw m₁ j₁ * cw m₂ j₂
        * h (x - j₁) * k (x - j₂)
      = (arithQ ρ (max l₁ l₂) : ℂ)⁻¹ *
          ∑ n ∈ Finset.range (arithQ ρ (max l₁ l₂)),
            (arithCharD ρ l₁ ((n : ℤ) - j₁) * cw m₁ j₁ * h (x - j₁))
              * (arithCharD ρ l₂ (P.eval (n : ℤ) - j₂) * cw m₂ j₂ * k (x - j₂)) := by
  rw [smallArithKernel_eq_arithCharD]
  rw [show (∑ n ∈ Finset.range (arithQ ρ (max l₁ l₂)),
            (arithCharD ρ l₁ ((n : ℤ) - j₁) * cw m₁ j₁ * h (x - j₁))
              * (arithCharD ρ l₂ (P.eval (n : ℤ) - j₂) * cw m₂ j₂ * k (x - j₂)))
        = (∑ n ∈ Finset.range (arithQ ρ (max l₁ l₂)),
            (arithCharD ρ l₁ ((n : ℤ) - j₁) * arithCharD ρ l₂ (P.eval (n : ℤ) - j₂)))
            * (cw m₁ j₁ * cw m₂ j₂ * h (x - j₁) * k (x - j₂)) from by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun n _ => ?_
      ring]
  ring

/-- The **fibre** of the exact-height twisted projection at the residue `n₀` (first variable): the
convolution with the kernel `j ↦ arithCharD ρ l (n₀-j) · cw m j`.  It is the multiplier with symbol
`∑_{β ∈ (ℚ/ℤ)_l} e(β n₀) m(ξ-β)`. -/
noncomputable def fiberOpD (ρ : ℝ) (l : ℕ) (m : ℝ → ℂ) (n₀ : ℤ) (u : ℤ → ℂ) : ℤ → ℂ :=
  fun x => ∑' j : ℤ, arithCharD ρ l (n₀ - j) * cw m j * u (x - j)

/-- The fibre of the exact-height twisted projection at the residue `n₀` (second variable), with
the polynomial twist `P`. -/
noncomputable def fiberOpPD (ρ : ℝ) (P : Polynomial ℤ) (l : ℕ) (m : ℝ → ℂ) (n₀ : ℤ)
    (u : ℤ → ℂ) : ℤ → ℂ :=
  fun x => ∑' j : ℤ, arithCharD ρ l (P.eval n₀ - j) * cw m j * u (x - j)



/-- **Interchange of a double `tsum` with a finite sum of products** (a local copy of
`tsum_tsum_finset_factor`, to keep this file independent of the volatile
`Btwist_eq_fiberSum` module).  If `u n` and `v n` are summable for every `n ∈ S`, then

  `∑' j₁, ∑' j₂, ∑_{n∈S} u n j₁ · v n j₂ = ∑_{n∈S} (∑' j₁, u n j₁) · (∑' j₂, v n j₂)`. -/
lemma tsum_tsum_finset_factor' (S : Finset ℕ) (u v : ℕ → ℤ → ℂ)
    (hu : ∀ n ∈ S, Summable (u n)) (hv : ∀ n ∈ S, Summable (v n)) :
    (∑' j₁ : ℤ, ∑' j₂ : ℤ, ∑ n ∈ S, u n j₁ * v n j₂)
      = ∑ n ∈ S, (∑' j₁ : ℤ, u n j₁) * (∑' j₂ : ℤ, v n j₂) := by
  have inner : ∀ j₁ : ℤ, (∑' j₂ : ℤ, ∑ n ∈ S, u n j₁ * v n j₂)
      = ∑ n ∈ S, u n j₁ * (∑' j₂ : ℤ, v n j₂) := by
    intro j₁
    rw [((hasSum_sum (fun n hn => ((hv n hn).mul_left (u n j₁)).hasSum)).tsum_eq)]
    exact Finset.sum_congr rfl fun n _ => tsum_mul_left
  rw [tsum_congr inner]
  rw [((hasSum_sum (fun n hn => (((hu n hn).mul_right (∑' j₂ : ℤ, v n j₂))).hasSum)).tsum_eq)]
  exact Finset.sum_congr rfl fun n _ => tsum_mul_right

/-- **`form-1` for the exact-height twisted bilinear multiplier.**  `smallBtwist` is the average
over the residues `n₀ ∈ ℤ/qℤ` of the products of the two *exact-height fibres*:

  `smallBtwist ρ P l₁ l₂ m₁ m₂ h k x
     = q⁻¹ ∑_{n₀ < q} (fiberOpD ρ l₁ m₁ n₀ h x) · (fiberOpPD ρ P l₂ m₂ n₀ k x)`,

`q = arithQ ρ (max l₁ l₂)`.  The proof is the exact-height counterpart of
`Btwist_eq_fiberSum`: push the constant `q⁻¹` and the finite residue sum out of the two `tsum`s
(legitimate as soon as each of the two one-variable fibre families is summable). -/
theorem smallBtwist_eq_fiberSumD (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (h k : ℤ → ℂ) (x : ℤ)
    (h₁ : ∀ n₀ : ℤ, Summable (fun j : ℤ =>
      arithCharD ρ l₁ (n₀ - j) * cw m₁ j * h (x - j)))
    (h₂ : ∀ n₀ : ℤ, Summable (fun j : ℤ =>
      arithCharD ρ l₂ (P.eval n₀ - j) * cw m₂ j * k (x - j))) :
    smallBtwist ρ P l₁ l₂ m₁ m₂ h k x
      = (arithQ ρ (max l₁ l₂) : ℂ)⁻¹ *
          ∑ n₀ ∈ Finset.range (arithQ ρ (max l₁ l₂)),
            fiberOpD ρ l₁ m₁ (n₀ : ℤ) h x * fiberOpPD ρ P l₂ m₂ (n₀ : ℤ) k x := by
  classical
  have hfin : (∑' j₁ : ℤ, ∑' j₂ : ℤ, ∑ n ∈ Finset.range (arithQ ρ (max l₁ l₂)),
        (arithCharD ρ l₁ ((n : ℤ) - j₁) * cw m₁ j₁ * h (x - j₁))
          * (arithCharD ρ l₂ (P.eval (n : ℤ) - j₂) * cw m₂ j₂ * k (x - j₂)))
      = ∑ n₀ ∈ Finset.range (arithQ ρ (max l₁ l₂)),
          fiberOpD ρ l₁ m₁ (n₀ : ℤ) h x * fiberOpPD ρ P l₂ m₂ (n₀ : ℤ) k x := by
    rw [tsum_tsum_finset_factor' (Finset.range (arithQ ρ (max l₁ l₂)))
        (fun n j => arithCharD ρ l₁ ((n : ℤ) - j) * cw m₁ j * h (x - j))
        (fun n j => arithCharD ρ l₂ (P.eval (n : ℤ) - j) * cw m₂ j * k (x - j))
        (fun n _ => h₁ (n : ℤ)) (fun n _ => h₂ (n : ℤ))]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [fiberOpD, fiberOpPD]
  simp only [smallBtwist]
  rw [tsum_congr (fun j₁ => tsum_congr (fun j₂ =>
    smallArithKernel_fiberTerm ρ P l₁ l₂ m₁ m₂ h k x j₁ j₂))]
  simp only [tsum_mul_left]
  rw [hfin]


/-- **The synthesis identity for the exact-height fibre.**  The fibre `fiberOpD ρ l m n₀` is the
arithmetic Fourier synthesis of the *β-pieces* `u ↦ ∑_j e(-jβ)·cw m j · u(·-j)` of the window
symbol `m` at the exact-height frequencies:

  `fiberOpD ρ l m n₀ u x = ∑_{β ∈ (ℚ/ℤ)_l} e(β n₀) · (∑_j e(-jβ) cw m j u(x-j))`.

(The `β`-piece is the multiplier with symbol `m(·-β)`, by `fourierCoeff_comp_sub`.) -/
theorem fiberOpD_eq_charSum (ρ : ℝ) (l : ℕ) (m : ℝ → ℂ) (u : ℤ → ℂ) (n₀ : ℤ) (x : ℤ)
    (hsum : ∀ β ∈ diffFreqs ρ l,
      Summable (fun j : ℤ => fourier (T := 1) (-j) β * cw m j * u (x - j))) :
    fiberOpD ρ l m n₀ u x
      = ∑ β ∈ diffFreqs ρ l,
          fourier (T := 1) n₀ β * (∑' j : ℤ, fourier (T := 1) (-j) β * cw m j * u (x - j)) := by
  classical
  have h1 : ∀ j : ℤ, arithCharD ρ l (n₀ - j) * cw m j * u (x - j)
      = ∑ β ∈ diffFreqs ρ l,
          fourier (T := 1) n₀ β * (fourier (T := 1) (-j) β * cw m j * u (x - j)) := by
    intro j
    rw [arithCharD, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [show n₀ - j = n₀ + (-j) by ring, fourier_add]
    ring
  rw [fiberOpD]
  simp only [h1]
  rw [Summable.tsum_finsetSum]
  · refine Finset.sum_congr rfl fun β _ => ?_
    rw [tsum_mul_left]
  · exact fun β hβ => (hsum β hβ).mul_left _




/-- **The exact-height arithmetic character is `Q`-periodic** whenever `Q` kills every frequency of
`diffFreqs ρ l` (in particular for `Q = arithQ ρ l`). -/
theorem arithCharD_periodic {ρ : ℝ} {l : ℕ} (Q : ℕ)
    (hkill : ∀ α ∈ diffFreqs ρ l, (Q : ℤ) • α = 0) (y : ℤ) :
    arithCharD ρ l (y + (Q : ℤ)) = arithCharD ρ l y := by
  unfold arithCharD
  refine Finset.sum_congr rfl fun α hα => ?_
  have h1 : (Q : ℤ) • α = 0 := hkill α hα
  have h2 : fourier (T := 1) (Q : ℤ) α = 1 := by
    rw [fourier_apply, h1, AddCircle.toCircle_zero]; rfl
  rw [fourier_add, h2, mul_one]

/-- **The residue average of a `q`-periodic family.**  If `q ∣ q'` (both positive) and
`U x ·` is `q`-periodic, then `residueLp p q' U = residueLp p q U`: the extra blocks of length `q`
repeat the first one, and the two normalising factors `(q')⁻¹·(q'/q)` and `q⁻¹` agree. -/
theorem residueLp_eq_of_dvd {p : ℝ} {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q') (hdvd : q ∣ q')
    {U : ℤ → ℕ → ENNReal} (hper : ∀ x n₀, U x (n₀ + q) = U x n₀) :
    residueLp p q' U = residueLp p q U := by
  funext x
  have hper' : ∀ m n₀ : ℕ, U x (n₀ + q * m) = U x n₀ := by
    intro m
    induction m with
    | zero => intro n₀; simp
    | succ m ih =>
      intro n₀
      have hstep : n₀ + q * (m + 1) = (n₀ + q * m) + q := by ring
      rw [hstep, hper x (n₀ + q * m), ih n₀]
  have hblock : ∀ m : ℕ, (∑ n₀ ∈ Finset.range (q * m), ENNReal.rpow (U x n₀) p)
      = (m : ENNReal) * ∑ n₀ ∈ Finset.range q, ENNReal.rpow (U x n₀) p := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih]
      have hshiftq : (∑ n ∈ Finset.range q, ENNReal.rpow (U x (q * m + n)) p)
          = ∑ n ∈ Finset.range q, ENNReal.rpow (U x n) p :=
        Finset.sum_congr rfl (fun n _ => by
          rw [show q * m + n = n + q * m by ring, hper' m n])
      rw [hshiftq]
      push_cast
      ring
  obtain ⟨k, hk⟩ := hdvd
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hk; omega
    · exact h
  have hqne : (q : ENNReal) ≠ 0 := by exact_mod_cast hq.ne'
  have hqtop : (q : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top q
  have hkne : (k : ENNReal) ≠ 0 := by exact_mod_cast hkpos.ne'
  have hktop : (k : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top k
  have hmain : (q' : ENNReal)⁻¹ * (∑ n₀ ∈ Finset.range q', ENNReal.rpow (U x n₀) p)
      = (q : ENNReal)⁻¹ * (∑ n₀ ∈ Finset.range q, ENNReal.rpow (U x n₀) p) := by
    rw [hk, hblock k, Nat.cast_mul, ENNReal.mul_inv (Or.inl hqne) (Or.inl hqtop), mul_assoc]
    have hcancel : ∀ S : ENNReal, (k : ENNReal)⁻¹ * ((k : ENNReal) * S) = S := fun S => by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hkne hktop, one_mul]
    rw [hcancel]
  simp only [residueLp]
  rw [show (q' : ENNReal).rpow (-1) = (q' : ENNReal)⁻¹ from ENNReal.rpow_neg_one _,
    show (q : ENNReal).rpow (-1) = (q : ENNReal)⁻¹ from ENNReal.rpow_neg_one _, hmain]

end Work.KMTAreas.A7
