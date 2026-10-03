/-
# The window expansion of `⟨Ã*_N(h,g), F⟩` (main case of Proposition `lip-2`)

This module proves the elementary (but `tsum`-heavy) identity behind the main case of the
alternate inverse theorem for `g`, Krause--Mirek--Tao, §5.2:

`⟨Ã*_N(h,g), F⟩ = ∑_s ∑_y h y · 𝓕_ℤ F(y + s) · lip2Avg N P M γ g s y`

whenever `𝓕_ℤ F` is supported in the arc of radius `1/(2M)` around `γ` (`M ≥ 2`), `F`, `h`, `g`
are absolutely summable, and `lip2Avg` is the windowed polynomial average

`lip2Avg N P M γ g s y = (1/N) ∑_{N/2 < n ≤ N} win M γ (n - s) · g (y + P(n))`.

The only analytic input is the reproducing property of the window
(`Work.KMTAreas.A4.lip2Reproduce`): on the arc of radius `1/(2M)` the window reproduces `F`,
`F z = ∑_m win M γ m · F (z - m)`.  Everything else is Fubini for absolutely convergent series
and the change of variables `x = y + n`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.lip2MainDefs
import Submission.Work.KMTAreas.A4.lip2Reproduce

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators
open Polynomial

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-! ## `tsum` tools -/

/-- If a two-variable family on `ℤ × ℤ` is summable, then so is the partial sum in the second
variable, `s ↦ ∑'_y f y s`. -/
private theorem summable_tsum_swap {f : ℤ → ℤ → ℂ} (hf : Summable (Function.uncurry f)) :
    Summable fun s : ℤ => ∑' y : ℤ, f y s := by
  have hF : Summable fun p : ℤ × ℤ => f p.2 p.1 := hf.prod_symm
  have h : HasSum (fun s : ℤ => ∑' y : ℤ, f y s) (∑' p : ℤ × ℤ, f p.2 p.1) :=
    HasSum.prod_fiberwise hF.hasSum fun s => (hF.prod_factor s).hasSum
  exact h.summable

/-- The shear change of variables: for summable `a`, `b`, the family `(y, s) ↦ ‖a y‖ · ‖b (y+s)‖`
is summable, because `(y, s) ↦ (y, y + s)` is a bijection of `ℤ × ℤ`. -/
private theorem summable_mul_shift {a b : ℤ → ℂ} (ha : Summable fun x => ‖a x‖)
    (hb : Summable fun x => ‖b x‖) :
    Summable fun p : ℤ × ℤ => ‖a p.1‖ * ‖b (p.1 + p.2)‖ := by
  have h2 : Summable fun q : ℤ × ℤ => ‖a q.1‖ * ‖b q.2‖ :=
    Summable.mul_of_nonneg ha hb (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hinj : Function.Injective (fun p : ℤ × ℤ => (p.1, p.1 + p.2)) := by
    rintro ⟨y, s⟩ ⟨y', s'⟩ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (by omega)
  have h3 : Summable fun p : ℤ × ℤ =>
      (fun q : ℤ × ℤ => ‖a q.1‖ * ‖b q.2‖) (p.1, p.1 + p.2) :=
    h2.comp_injective hinj
  exact h3

/-! ## The reproducing property in shifted form -/

/-- **The reproducing property, shifted.**  If `𝓕_ℤ F` is supported in the arc of radius
`1/(2M)` around `γ` and `M ≥ 2`, then for all `z n : ℤ`,
`F z = ∑'_s win M γ (n - s) · F (z - n + s)`. -/
private theorem lip2Reproduce_shift {F : ℤ → ℂ} (hF : Summable fun x : ℤ => ‖F x‖)
    {M : ℝ} (hM : 2 ≤ M) {γ : FreqCircle}
    (hsupp : FourierSupportIn F (arcSet γ (1 / (2 * M)))) (z n : ℤ) :
    F z = ∑' s : ℤ, win M γ (n - s) * F (z - n + s) := by
  set e : ℤ ≃ ℤ := (Equiv.neg ℤ).trans (Equiv.addRight n) with he
  have hes : ∀ s : ℤ, e s = n - s := by
    intro s
    rw [he, Equiv.trans_apply]
    simp only [Equiv.neg_apply, Equiv.coe_addRight]
    ring
  calc F z = ∑' m : ℤ, win M γ m * F (z - m) := lip2Reproduce hF hM hsupp z
    _ = ∑' s : ℤ, win M γ (e s) * F (z - e s) :=
        (Equiv.tsum_eq e (fun m : ℤ => win M γ m * F (z - m))).symm
    _ = ∑' s : ℤ, win M γ (n - s) * F (z - n + s) :=
        tsum_congr fun s => by
          rw [hes s]
          rw [show z - (n - s) = z - n + s by ring]

/-! ## Elementary summability lemmas for the summands -/

/-- Translating the index of an absolutely summable sequence on `ℤ` preserves summability. -/
private theorem summable_shift_norm {F : ℤ → ℂ} (hF : Summable fun x : ℤ => ‖F x‖) (s : ℤ) :
    Summable fun y : ℤ => ‖F (y + s)‖ :=
  hF.comp_injective (fun a b hab => by omega)

/-- The summand of the right-hand side is summable in `y` for fixed `s, n`. -/
private theorem summable_window_shift_term {P : Polynomial ℤ} {M : ℝ} {γ : FreqCircle}
    {F h g : ℤ → ℂ} (hF : Summable fun x : ℤ => ‖F x‖)
    (hh : Summable fun x : ℤ => ‖h x‖) (hg : Summable fun x : ℤ => ‖g x‖) (s n : ℤ) :
    Summable fun y : ℤ => h y * F (y + s) * (win M γ (n - s) * g (y + P.eval n)) := by
  have hH : ∀ y : ℤ, ‖h y‖ ≤ ∑' y : ℤ, ‖h y‖ :=
    fun y => Summable.le_tsum hh y (fun _ _ => norm_nonneg _)
  have hG : ∀ y : ℤ, ‖g y‖ ≤ ∑' y : ℤ, ‖g y‖ :=
    fun y => Summable.le_tsum hg y (fun _ _ => norm_nonneg _)
  have hFs : Summable fun y : ℤ => ‖F (y + s)‖ := summable_shift_norm hF s
  refine Summable.of_norm_bounded
    (hFs.mul_left ((∑' y : ℤ, ‖h y‖) * ‖win M γ (n - s)‖ * (∑' y : ℤ, ‖g y‖))) fun y => ?_
  simp only [norm_mul]
  have hstep1 : ‖h y‖ * ‖F (y + s)‖
      ≤ (∑' y : ℤ, ‖h y‖) * ‖F (y + s)‖ :=
    mul_le_mul_of_nonneg_right (hH y) (norm_nonneg _)
  have hstep2 : ‖win M γ (n - s)‖ * ‖g (y + P.eval n)‖
      ≤ ‖win M γ (n - s)‖ * (∑' y : ℤ, ‖g y‖) :=
    mul_le_mul_of_nonneg_left (hG _) (norm_nonneg _)
  calc ‖h y‖ * ‖F (y + s)‖ * (‖win M γ (n - s)‖ * ‖g (y + P.eval n)‖)
      ≤ ((∑' y : ℤ, ‖h y‖) * ‖F (y + s)‖) * (‖win M γ (n - s)‖ * (∑' y : ℤ, ‖g y‖)) :=
        mul_le_mul hstep1 hstep2 (by positivity) (by positivity)
    _ = (∑' y : ℤ, ‖h y‖) * ‖win M γ (n - s)‖ * (∑' y : ℤ, ‖g y‖) * ‖F (y + s)‖ := by ring

/-- The summand of the left-hand side is summable in `x` for fixed `n`. -/
private theorem summable_ahalfTranspose_term {P : Polynomial ℤ}
    {F h g : ℤ → ℂ} (hF : Summable fun x : ℤ => ‖F x‖)
    (hh : Summable fun x : ℤ => ‖h x‖) (hg : Summable fun x : ℤ => ‖g x‖) (n : ℤ) :
    Summable fun x : ℤ => h (x - n) * g (x + P.eval n - n) * F x := by
  have hH : ∀ y : ℤ, ‖h y‖ ≤ ∑' y : ℤ, ‖h y‖ :=
    fun y => Summable.le_tsum hh y (fun _ _ => norm_nonneg _)
  have hG : ∀ y : ℤ, ‖g y‖ ≤ ∑' y : ℤ, ‖g y‖ :=
    fun y => Summable.le_tsum hg y (fun _ _ => norm_nonneg _)
  refine Summable.of_norm_bounded
    (hF.mul_left ((∑' y : ℤ, ‖h y‖) * (∑' y : ℤ, ‖g y‖))) fun x => ?_
  simp only [norm_mul]
  have hstep1 : ‖h (x - n)‖ * ‖g (x + P.eval n - n)‖
      ≤ (∑' y : ℤ, ‖h y‖) * (∑' y : ℤ, ‖g y‖) :=
    mul_le_mul (hH _) (hG _) (norm_nonneg _) (by positivity)
  calc ‖h (x - n)‖ * ‖g (x + P.eval n - n)‖ * ‖F x‖
      ≤ ((∑' y : ℤ, ‖h y‖) * (∑' y : ℤ, ‖g y‖)) * ‖F x‖ :=
        mul_le_mul_of_nonneg_right hstep1 (norm_nonneg _)

/-! ## Joint summability of the window correlation -/

/-- **Joint summability.**  For absolutely summable `F`, `h`, `g` and `M ≥ 1`, the family
`(y, s) ↦ ‖h y‖ ‖g (y + P n)‖ ‖win M γ (n - s)‖ ‖F (y + s)‖` is summable.

The point is that the `s`-dependence of `win` and the `y`-dependence of `g` can be replaced by
the (finite) sup norms `∑ ‖win‖` and `∑ ‖g‖`, leaving the shear `(y, s) ↦ (y, y + s)` of the
summable family `‖h y‖ ‖F (y + s)‖`. -/
private theorem summable_window_correlation {P : Polynomial ℤ} {M : ℝ} {γ : FreqCircle}
    {F h g : ℤ → ℂ} (hF : Summable fun x : ℤ => ‖F x‖)
    (hh : Summable fun x : ℤ => ‖h x‖) (hg : Summable fun x : ℤ => ‖g x‖)
    (hM : 1 ≤ M) (n : ℤ) :
    Summable fun p : ℤ × ℤ =>
      ‖h p.1‖ * ‖g (p.1 + P.eval n)‖ * ‖win M γ (n - p.2)‖ * ‖F (p.1 + p.2)‖ := by
  have hG : ∀ y : ℤ, ‖g y‖ ≤ ∑' y : ℤ, ‖g y‖ :=
    fun y => Summable.le_tsum hg y (fun _ _ => norm_nonneg _)
  have hCw : ∀ m : ℤ, ‖win M γ m‖ ≤ ∑' m : ℤ, ‖win M γ m‖ :=
    fun m => Summable.le_tsum (win_summable M hM γ) m (fun _ _ => norm_nonneg _)
  have hbase : Summable fun p : ℤ × ℤ => ‖h p.1‖ * ‖F (p.1 + p.2)‖ := summable_mul_shift hh hF
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_)
    (hbase.mul_left ((∑' y : ℤ, ‖g y‖) * (∑' m : ℤ, ‖win M γ m‖)))
  have h1 : ‖h p.1‖ * ‖g (p.1 + P.eval n)‖ ≤ ‖h p.1‖ * (∑' y : ℤ, ‖g y‖) :=
    mul_le_mul_of_nonneg_left (hG _) (norm_nonneg _)
  have h2 : ‖win M γ (n - p.2)‖ ≤ ∑' m : ℤ, ‖win M γ m‖ := hCw _
  calc ‖h p.1‖ * ‖g (p.1 + P.eval n)‖ * ‖win M γ (n - p.2)‖ * ‖F (p.1 + p.2)‖
      = (‖h p.1‖ * ‖g (p.1 + P.eval n)‖) * (‖win M γ (n - p.2)‖ * ‖F (p.1 + p.2)‖) := by ring
    _ ≤ (‖h p.1‖ * (∑' y : ℤ, ‖g y‖))
          * ((∑' m : ℤ, ‖win M γ m‖) * ‖F (p.1 + p.2)‖) :=
        mul_le_mul h1 (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)) (by positivity) (by positivity)
    _ = ((∑' y : ℤ, ‖g y‖) * (∑' m : ℤ, ‖win M γ m‖))
          * (‖h p.1‖ * ‖F (p.1 + p.2)‖) := by ring

/-- The complex form of the joint summability. -/
private theorem summable_window_correlation_complex {P : Polynomial ℤ} {M : ℝ} {γ : FreqCircle}
    {F h g : ℤ → ℂ} (hF : Summable fun x : ℤ => ‖F x‖)
    (hh : Summable fun x : ℤ => ‖h x‖) (hg : Summable fun x : ℤ => ‖g x‖)
    (hM : 1 ≤ M) (n : ℤ) :
    Summable fun p : ℤ × ℤ => h p.1 * g (p.1 + P.eval n) * win M γ (n - p.2) * F (p.1 + p.2) := by
  refine Summable.of_norm_bounded
    (summable_window_correlation (P := P) (γ := γ) hF hh hg hM n) fun p => ?_
  rw [norm_mul, norm_mul, norm_mul]

/-! ## The two per-`n` identities -/

/-- **Left expansion.**  For fixed `n`, the `x`-sum of the left-hand side equals the master sum
over `(y, s) ∈ ℤ × ℤ` (the change of variables `x = y + n`, followed by the reproducing property
of the window). -/
private theorem windowExpansion_left {P : Polynomial ℤ} {M : ℝ} {γ : FreqCircle}
    {F h g : ℤ → ℂ} (hF : Summable fun x : ℤ => ‖F x‖) (hM : 2 ≤ M)
    (hsupp : FourierSupportIn F (arcSet γ (1 / (2 * M))))
    (hh : Summable fun x : ℤ => ‖h x‖) (hg : Summable fun x : ℤ => ‖g x‖) (n : ℤ) :
    (∑' x : ℤ, h (x - n) * g (x + P.eval n - n) * F x)
      = ∑' p : ℤ × ℤ, h p.1 * g (p.1 + P.eval n) * win M γ (n - p.2) * F (p.1 + p.2) := by
  have hχ : Summable fun p : ℤ × ℤ =>
      h p.1 * g (p.1 + P.eval n) * win M γ (n - p.2) * F (p.1 + p.2) :=
    summable_window_correlation_complex hF hh hg (by linarith) n
  calc (∑' x : ℤ, h (x - n) * g (x + P.eval n - n) * F x)
      = ∑' y : ℤ, h y * g (y + P.eval n) * F (y + n) := by
        rw [← Equiv.tsum_eq (Equiv.addRight n)
          (fun x : ℤ => h (x - n) * g (x + P.eval n - n) * F x)]
        refine tsum_congr fun y => ?_
        change h ((y + n) - n) * g ((y + n) + P.eval n - n) * F (y + n)
            = h y * g (y + P.eval n) * F (y + n)
        rw [show (y + n) - n = y by ring,
          show (y + n) + P.eval n - n = y + P.eval n by ring]
    _ = ∑' y : ℤ, ∑' s : ℤ, h y * g (y + P.eval n) * (win M γ (n - s) * F (y + s)) := by
        refine tsum_congr fun y => ?_
        rw [lip2Reproduce_shift hF hM hsupp (y + n) n]
        rw [show (y + n) - n = y by ring]
        exact (tsum_mul_left (a := h y * g (y + P.eval n))
          (f := fun s : ℤ => win M γ (n - s) * F (y + s))).symm
    _ = ∑' p : ℤ × ℤ, h p.1 * g (p.1 + P.eval n) * win M γ (n - p.2) * F (p.1 + p.2) := by
        trans ∑' y : ℤ, ∑' s : ℤ, h y * g (y + P.eval n) * win M γ (n - s) * F (y + s)
        · exact tsum_congr fun y => tsum_congr fun s => by ring
        · exact (Summable.tsum_prod hχ).symm

/-- **Right expansion.**  For fixed `n`, the `(s, y)`-sum of the right-hand side equals the master
sum over `ℤ × ℤ` (Fubini for the absolutely summable window correlation). -/
private theorem windowExpansion_right {P : Polynomial ℤ} {M : ℝ} {γ : FreqCircle}
    {F h g : ℤ → ℂ} (hF : Summable fun x : ℤ => ‖F x‖)
    (hh : Summable fun x : ℤ => ‖h x‖) (hg : Summable fun x : ℤ => ‖g x‖)
    (hM : 1 ≤ M) (n : ℤ) :
    (∑' s : ℤ, ∑' y : ℤ, h y * F (y + s) * (win M γ (n - s) * g (y + P.eval n)))
      = ∑' p : ℤ × ℤ, h p.1 * g (p.1 + P.eval n) * win M γ (n - p.2) * F (p.1 + p.2) := by
  have hχ : Summable fun p : ℤ × ℤ =>
      h p.1 * F (p.1 + p.2) * (win M γ (n - p.2) * g (p.1 + P.eval n)) :=
    (summable_window_correlation_complex hF hh hg hM n).congr fun p => by ring
  calc (∑' s : ℤ, ∑' y : ℤ, h y * F (y + s) * (win M γ (n - s) * g (y + P.eval n)))
      = ∑' y : ℤ, ∑' s : ℤ, h y * F (y + s) * (win M γ (n - s) * g (y + P.eval n)) :=
        Summable.tsum_comm hχ
    _ = ∑' p : ℤ × ℤ, h p.1 * F (p.1 + p.2) * (win M γ (n - p.2) * g (p.1 + P.eval n)) :=
        (Summable.tsum_prod hχ).symm
    _ = ∑' p : ℤ × ℤ, h p.1 * g (p.1 + P.eval n) * win M γ (n - p.2) * F (p.1 + p.2) :=
        tsum_congr fun p => by ring

/-! ## The window expansion -/

theorem lip2WindowExpansion {N : ℕ} (hN : 1 ≤ N) (P : Polynomial ℤ) {M : ℝ} (hM : 2 ≤ M)
    {γ : Work.Analysis.InverseTheory.FreqCircle} {F : ℤ → ℂ}
    (hFsum : Summable fun x : ℤ => ‖F x‖)
    (hFsupp : Work.Analysis.InverseTheory.FourierSupportIn F
      (Work.KMTAreas.A4.arcSet γ (1 / (2 * M))))
    {g h : ℤ → ℂ} (hgsum : Summable fun y : ℤ => ‖g y‖)
    (hhsum : Summable fun y : ℤ => ‖h y‖) :
    Work.Analysis.InverseTheory.bilinPair
        (Work.Analysis.InverseTheory.AhalfTranspose N P h g) F
      = ∑' s : ℤ, ∑' y : ℤ, h y * F (y + s) * Work.KMTAreas.A4.lip2Avg N P M γ g s y := by
  classical
  have hM1 : (1 : ℝ) ≤ M := by linarith
  have hLHS : bilinPair (AhalfTranspose N P h g) F
      = (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, ∑' p : ℤ × ℤ,
          h p.1 * g (p.1 + P.eval (n : ℤ)) * win M γ ((n : ℤ) - p.2) * F (p.1 + p.2) := by
    rw [bilinPair]
    have hpt : ∀ x : ℤ, AhalfTranspose N P h g x * F x
        = (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
            h (x - (n : ℤ)) * g (x + P.eval (n : ℤ) - (n : ℤ)) * F x := by
      intro x
      rw [AhalfTranspose, mul_assoc, Finset.sum_mul]
    rw [tsum_congr hpt, tsum_mul_left]
    rw [Summable.tsum_finsetSum (s := Finset.Ioc (N / 2) N)
      (f := fun (n : ℕ) (x : ℤ) =>
        h (x - (n : ℤ)) * g (x + P.eval (n : ℤ) - (n : ℤ)) * F x)
      (fun n _ => summable_ahalfTranspose_term hFsum hhsum hgsum (n : ℤ))]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    exact windowExpansion_left hFsum hM hFsupp hhsum hgsum (n : ℤ)
  have hRHS : (∑' s : ℤ, ∑' y : ℤ, h y * F (y + s) * lip2Avg N P M γ g s y)
      = (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, ∑' p : ℤ × ℤ,
          h p.1 * g (p.1 + P.eval (n : ℤ)) * win M γ ((n : ℤ) - p.2) * F (p.1 + p.2) := by
    have hpt : ∀ s y : ℤ, h y * F (y + s) * lip2Avg N P M γ g s y
        = (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
            h y * F (y + s) * (win M γ ((n : ℤ) - s) * g (y + P.eval (n : ℤ))) := by
      intro s y
      rw [lip2Avg]
      have h1 : h y * F (y + s)
            * ((N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
                win M γ ((n : ℤ) - s) * g (y + P.eval (n : ℤ)))
          = (N : ℝ)⁻¹ * ((h y * F (y + s))
              * ∑ n ∈ Finset.Ioc (N / 2) N,
                win M γ ((n : ℤ) - s) * g (y + P.eval (n : ℤ))) := by ring
      rw [h1, Finset.mul_sum (s := Finset.Ioc (N / 2) N)
        (f := fun (n : ℕ) => win M γ ((n : ℤ) - s) * g (y + P.eval (n : ℤ)))]
    calc (∑' s : ℤ, ∑' y : ℤ, h y * F (y + s) * lip2Avg N P M γ g s y)
        = (N : ℝ)⁻¹ * ∑' s : ℤ, ∑' y : ℤ, ∑ n ∈ Finset.Ioc (N / 2) N,
            h y * F (y + s) * (win M γ ((n : ℤ) - s) * g (y + P.eval (n : ℤ))) := by
          rw [tsum_congr (fun s => tsum_congr (fun y => hpt s y))]
          simp_rw [tsum_mul_left]
      _ = (N : ℝ)⁻¹ * ∑' s : ℤ, ∑ n ∈ Finset.Ioc (N / 2) N, ∑' y : ℤ,
            h y * F (y + s) * (win M γ ((n : ℤ) - s) * g (y + P.eval (n : ℤ))) := by
          congr 1
          refine tsum_congr fun s => ?_
          exact Summable.tsum_finsetSum (s := Finset.Ioc (N / 2) N)
            (f := fun (n : ℕ) (y : ℤ) =>
              h y * F (y + s) * (win M γ ((n : ℤ) - s) * g (y + P.eval (n : ℤ))))
            (fun n _ => summable_window_shift_term hFsum hhsum hgsum s (n : ℤ))
      _ = (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, ∑' s : ℤ, ∑' y : ℤ,
            h y * F (y + s) * (win M γ ((n : ℤ) - s) * g (y + P.eval (n : ℤ))) := by
          congr 1
          refine Summable.tsum_finsetSum (s := Finset.Ioc (N / 2) N)
            (f := fun (n : ℕ) (s : ℤ) => ∑' y : ℤ,
              h y * F (y + s) * (win M γ ((n : ℤ) - s) * g (y + P.eval (n : ℤ)))) ?_
          intro n _
          have hcorr : Summable fun p : ℤ × ℤ =>
              h p.1 * F (p.1 + p.2) * (win M γ ((n : ℤ) - p.2) * g (p.1 + P.eval (n : ℤ))) :=
            (summable_window_correlation_complex hFsum hhsum hgsum hM1 (n : ℤ)).congr
              fun p => by ring
          exact summable_tsum_swap
            (f := fun (y : ℤ) (s : ℤ) =>
              h y * F (y + s) * (win M γ ((n : ℤ) - s) * g (y + P.eval (n : ℤ)))) hcorr
      _ = (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, ∑' p : ℤ × ℤ,
            h p.1 * g (p.1 + P.eval (n : ℤ)) * win M γ ((n : ℤ) - p.2) * F (p.1 + p.2) := by
          congr 1
          refine Finset.sum_congr rfl fun n _ => ?_
          exact windowExpansion_right hFsum hhsum hgsum hM1 (n : ℤ)
  exact hLHS.trans hRHS.symm

end Work.KMTAreas.A4
