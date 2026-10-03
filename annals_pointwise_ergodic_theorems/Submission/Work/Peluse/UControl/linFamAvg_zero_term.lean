import Mathlib
import Submission.Work.Peluse.UControl.pelusePetChapterDefs

/-!
# The `a = 0` term of `linFamAvg`

`linFamAvg D l c N M H f b β` is the average, over the parameter box `D.parBox l H`, of the
modulus of the multilinear correlation

`((N:ℂ)*(M:ℂ))⁻¹ * ∑'_x f x * ∑_{y ∈ [M]} ∏_{i ∈ |I_{l-1}|} C^{b i} f (x + petDir a i * y + β a i)`

along the linear configuration whose directions are the datum's own level-`(l-1)` family.

This file evaluates the family at the **zero parameter** `a = 0`: there every direction
`petDir D l c 0 i` vanishes (for `l ≥ 2`), so the `y`-sum degenerates to `M` copies of the same
product, the factor `(M : ℂ)` cancels against `((N:ℂ)*(M:ℂ))⁻¹`, and the balanced Boolean family
`b` (`#{b = false} = t-1`, `#|I_{l-1}| = 2t-1`) makes each summand the nonnegative real
`‖f x‖^{2t}`.  Hence the `a = 0` summand of `linFamAvg` is exactly
`(N:ℝ)⁻¹ * ∑_{x∈[-N,N]} ‖f x‖^{2t}`, and the average dominates it:

`((D.parBox l H).card:ℝ)⁻¹ * ((N:ℝ)⁻¹ * ∑_{x∈symIcc N} ‖f x‖^{2t}) ≤ linFamAvg D l c N M H f b 0`.

This is steps 1–2 of the "corner" argument of `NOTES_petChapter5_session13.md` §B: the corner of
Peluse's Proposition 3.4 (`⌊δ'M⌋ ≤ C`) needs precisely this lower bound for `linFamAvg`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Work.Peluse

/-! ## The zero parameter of the PET family -/

/-- Every `dir` at a *positive* level vanishes at the zero parameter family: the level-`(j+1)`
summand carries the factor `a (j+1) s = 0`. -/
lemma IdxDatum.dir_zero_of_pos (D : IdxDatum) (l : ℕ) (c : ℤ) :
    ∀ (j : ℕ) (w : D.I j), 1 ≤ j → D.dir l c j w (0 : (i : ℕ) → D.S i → ℤ) = 0 := by
  intro j w hj
  obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  simp [IdxDatum.dir]

/-- The padding of the zero parameter family is zero. -/
lemma IdxDatum.pad_zero (D : IdxDatum) (l : ℕ) : D.pad l (0 : D.Idx l) = 0 := by
  funext j s
  simp [IdxDatum.pad]

/-- At the zero parameter every PET direction vanishes (for `l ≥ 2`). -/
lemma IdxDatum.petDir_zero (D : IdxDatum) {l : ℕ} (hl : 2 ≤ l) (c : ℤ)
    (i : Fin (Fintype.card (D.I (l - 1)))) : petDir D l c (0 : D.Idx l) i = 0 := by
  unfold petDir
  rw [IdxDatum.pad_zero]
  exact IdxDatum.dir_zero_of_pos D l c (l - 1) _ (by omega)

/-! ## Three elementary lemmas -/

/-- A sum of a constant over `[1,M]` is `M` times the constant. -/
lemma Icc_one_sum_const (M : ℕ) (z : ℂ) : ∑ _y ∈ Finset.Icc 1 M, z = (M : ℂ) * z := by
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  norm_num

/-- Membership in `symIcc N` is the bound `|x| ≤ N`. -/
lemma symIcc_mem_iff_natAbs (N : ℕ) (x : ℤ) : x ∈ symIcc N ↔ x.natAbs ≤ N := by
  rw [symIcc, Finset.mem_Icc]
  constructor <;> intro h <;> omega

/-- The norm of a finite sum of nonnegative real numbers (viewed in `ℂ`) is the sum. -/
lemma norm_sum_ofReal_nonneg {s : Finset ℤ} {r : ℤ → ℝ} (hr : ∀ x ∈ s, 0 ≤ r x) :
    ‖∑ x ∈ s, ((r x : ℝ) : ℂ)‖ = ∑ x ∈ s, r x := by
  have h1 : ∑ x ∈ s, ((r x : ℝ) : ℂ) = (((∑ x ∈ s, r x : ℝ)) : ℂ) :=
    (Complex.ofReal_sum s r).symm
  have h2 : ‖(((∑ x ∈ s, r x : ℝ)) : ℂ)‖ = |∑ x ∈ s, r x| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [h1]
  rw [h2]
  rw [abs_of_nonneg (Finset.sum_nonneg hr)]

/-! ## The balanced Boolean product -/

/-- The elementary core of the computation: for `k = 2t-1` and a Boolean family `b` with exactly
`t-1` occurrences of `false`, the product `∏_i (if b i then conj z else z)` multiplied by `z` is
the nonnegative real `‖z‖^{2t}`.  (`#{b = true} = t`, so the `t` factors `conj z` pair with `z`
itself and the `t-1` factors `z`.) -/
lemma mul_prod_boole (z : ℂ) {k t : ℕ} (hk : k = 2 * t - 1) (ht : 1 ≤ t)
    (b : Fin k → Bool) (hb : (Finset.univ.filter (fun i => b i = false)).card = t - 1) :
    z * ∏ i : Fin k, (if b i then star z else z) = ((‖z‖ ^ (2 * t) : ℝ) : ℂ) := by
  classical
  have hsplit : ∏ i : Fin k, (if b i then star z else z)
      = (∏ i ∈ Finset.univ.filter (fun i => b i = false), z) *
        (∏ i ∈ Finset.univ.filter (fun i => ¬ (b i = false)), star z) := by
    rw [← Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset (Fin k))
      (fun i => b i = false) (fun i => if b i then star z else z)]
    congr 1
    · refine Finset.prod_congr rfl ?_
      intro i hi
      simp only [Finset.mem_filter] at hi
      simp [hi.2]
    · refine Finset.prod_congr rfl ?_
      intro i hi
      simp only [Finset.mem_filter] at hi
      have hbi : b i = true := by
        cases h : b i <;> simp_all
      simp [hbi]
  have hc : (Finset.univ.filter (fun i => ¬ (b i = false)) : Finset (Fin k)).card = t := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin k))) (p := fun i => b i = false)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    omega
  have hzp : z * z ^ (t - 1) = z ^ t := by
    rw [← pow_succ' z (t - 1), Nat.sub_add_cancel ht]
  have hstar : star z = (starRingEnd ℂ) z := rfl
  rw [hsplit, Finset.prod_const, Finset.prod_const, hc, hb, ← mul_assoc, hzp, ← mul_pow, hstar,
    Complex.mul_conj, ← Complex.ofReal_pow, Complex.normSq_eq_norm_sq, ← pow_mul]

/-! ## The core of the average -/

/-- The (complex) correlation at a fixed parameter `a`, whose modulus is averaged by `linFamAvg`. -/
def linCore (D : IdxDatum) (l : ℕ) (c : ℤ) (N M : ℕ) (f : ℤ → ℂ)
    (b : Fin (Fintype.card (D.I (l - 1))) → Bool)
    (β : D.Idx l → Fin (Fintype.card (D.I (l - 1))) → ℤ) (a : D.Idx l) : ℂ :=
  ((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, f x *
    ∑ y ∈ Finset.Icc 1 M,
      ∏ i : Fin (Fintype.card (D.I (l - 1))),
        (if b i then star (f (x + (petDir D l c a i * (y : ℤ) + β a i)))
          else f (x + (petDir D l c a i * (y : ℤ) + β a i)))

/-- `linFamAvg` is the average of `‖linCore‖` (definitional). -/
lemma linFamAvg_eq_card_mul_sum (D : IdxDatum) (l : ℕ) (c : ℤ) (N M H : ℕ) (f : ℤ → ℂ)
    (b : Fin (Fintype.card (D.I (l - 1))) → Bool)
    (β : D.Idx l → Fin (Fintype.card (D.I (l - 1))) → ℤ) :
    linFamAvg D l c N M H f b β
      = (((D.parBox l H).card : ℕ) : ℝ)⁻¹ *
        ∑ a ∈ D.parBox l H, ‖linCore D l c N M f b β a‖ := rfl

/-- **The `a = 0` term.**  At the zero parameter the correlation is the nonnegative real
`(N:ℝ)⁻¹ * ∑_{x∈[-N,N]} ‖f x‖^{2t}`. -/
lemma linCore_zero (D : IdxDatum) {l : ℕ} (hl : 2 ≤ l) (c : ℤ) (N M : ℕ) (f : ℤ → ℂ)
    (b : Fin (Fintype.card (D.I (l - 1))) → Bool) (t : ℕ)
    (hm : Fintype.card (D.I (l - 1)) = 2 * t - 1)
    (hb : (Finset.univ.filter (fun i => b i = false)).card = t - 1)
    (ht : 1 ≤ t) (hN : 0 < N) (hM : 0 < M) (hfs : SupportIn f N) :
    ‖linCore D l c N M f b (fun _ _ => 0) (0 : D.Idx l)‖
      = (N : ℝ)⁻¹ * ∑ x ∈ symIcc N, ‖f x‖ ^ (2 * t) := by
  classical
  set W : ℂ := ∑ x ∈ symIcc N, f x *
      ∏ i : Fin (Fintype.card (D.I (l - 1))), (if b i then star (f x) else f x) with hW
  have harg : ∀ (x : ℤ) (y : ℕ) (i : Fin (Fintype.card (D.I (l - 1)))),
      x + (petDir D l c (0 : D.Idx l) i * (y : ℤ) + (fun _ _ => (0 : ℤ)) (0 : D.Idx l) i) = x := by
    intro x y i
    rw [IdxDatum.petDir_zero D hl c i]
    ring
  have hy : ∀ x : ℤ, (∑ y ∈ Finset.Icc 1 M,
        ∏ i : Fin (Fintype.card (D.I (l - 1))),
          (if b i then star (f (x + (petDir D l c (0 : D.Idx l) i * (y : ℤ) +
              (fun _ _ => (0 : ℤ)) (0 : D.Idx l) i)))
            else f (x + (petDir D l c (0 : D.Idx l) i * (y : ℤ) +
              (fun _ _ => (0 : ℤ)) (0 : D.Idx l) i))))
      = (M : ℂ) * ∏ i : Fin (Fintype.card (D.I (l - 1))), (if b i then star (f x) else f x) := by
    intro x
    have hfun : (fun y : ℕ => ∏ i : Fin (Fintype.card (D.I (l - 1))),
          (if b i then star (f (x + (petDir D l c (0 : D.Idx l) i * (y : ℤ) +
              (fun _ _ => (0 : ℤ)) (0 : D.Idx l) i)))
            else f (x + (petDir D l c (0 : D.Idx l) i * (y : ℤ) +
              (fun _ _ => (0 : ℤ)) (0 : D.Idx l) i))))
        = fun _ : ℕ => ∏ i : Fin (Fintype.card (D.I (l - 1))),
            (if b i then star (f x) else f x) := by
      funext y
      simp only [harg]
    rw [hfun, Icc_one_sum_const]
  have hsupp : ∀ x : ℤ, x ∉ symIcc N →
      f x * ((M : ℂ) * ∏ i : Fin (Fintype.card (D.I (l - 1))),
        (if b i then star (f x) else f x)) = 0 := by
    intro x hx
    have hNx : N < x.natAbs := by
      rw [← not_le]
      intro hle
      exact hx ((symIcc_mem_iff_natAbs N x).mpr hle)
    rw [hfs x hNx, zero_mul]
  have hstep1 : linCore D l c N M f b (fun _ _ => 0) (0 : D.Idx l)
      = ((N : ℂ) * (M : ℂ))⁻¹ * (∑' x : ℤ, f x * ((M : ℂ) *
          ∏ i : Fin (Fintype.card (D.I (l - 1))), (if b i then star (f x) else f x))) := by
    unfold linCore
    congr 1
    apply tsum_congr
    intro x
    rw [hy x]
  have hstep2 : (∑' x : ℤ, f x * ((M : ℂ) * ∏ i : Fin (Fintype.card (D.I (l - 1))),
        (if b i then star (f x) else f x)))
      = ∑ x ∈ symIcc N, f x * ((M : ℂ) * ∏ i : Fin (Fintype.card (D.I (l - 1))),
        (if b i then star (f x) else f x)) :=
    tsum_eq_sum hsupp
  have hstep3 : (∑ x ∈ symIcc N, f x * ((M : ℂ) *
        ∏ i : Fin (Fintype.card (D.I (l - 1))), (if b i then star (f x) else f x)))
      = (M : ℂ) * W := by
    rw [hW, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  have hWnorm : ‖W‖ = ∑ x ∈ symIcc N, ‖f x‖ ^ (2 * t) := by
    rw [hW]
    have hterm : ∀ x : ℤ, f x * ∏ i : Fin (Fintype.card (D.I (l - 1))),
        (if b i then star (f x) else f x) = ((‖f x‖ ^ (2 * t) : ℝ) : ℂ) :=
      fun x => mul_prod_boole (f x) hm ht b hb
    rw [Finset.sum_congr rfl (fun x _ => hterm x)]
    exact norm_sum_ofReal_nonneg (fun x _ => pow_nonneg (norm_nonneg _) _)
  have hNM : ((N : ℝ) * (M : ℝ))⁻¹ *
      ((M : ℝ) * ∑ x ∈ symIcc N, ‖f x‖ ^ (2 * t)) =
      (N : ℝ)⁻¹ * ∑ x ∈ symIcc N, ‖f x‖ ^ (2 * t) := by
    have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    rw [mul_inv]
    field_simp
  calc ‖linCore D l c N M f b (fun _ _ => 0) (0 : D.Idx l)‖
      = ‖((N : ℂ) * (M : ℂ))⁻¹ * ((M : ℂ) * W)‖ := by rw [hstep1, hstep2, hstep3]
    _ = ‖((N : ℂ) * (M : ℂ))⁻¹‖ * (‖(M : ℂ)‖ * ‖W‖) := by rw [norm_mul, norm_mul]
    _ = (N : ℝ)⁻¹ * ∑ x ∈ symIcc N, ‖f x‖ ^ (2 * t) := by
        rw [hWnorm, norm_inv, norm_mul, norm_natCast, norm_natCast]
        exact hNM

/-! ## The theorem -/

theorem linFamAvg_zero_term {l : ℕ} (D : IdxDatum) (c : ℤ) (N M H : ℕ) (f : ℤ → ℂ)
    (b : Fin (Fintype.card (D.I (l - 1))) → Bool) (t : ℕ)
    (hm : Fintype.card (D.I (l - 1)) = 2 * t - 1)
    (hb : (Finset.univ.filter (fun i => b i = false)).card = t - 1)
    (ht : 1 ≤ t) (hl : 2 ≤ l) (hN : 0 < N) (hM : 0 < M) (hfs : SupportIn f N) :
    ((D.parBox l H).card : ℝ)⁻¹ * ((N : ℝ)⁻¹ * ∑ x ∈ symIcc N, ‖f x‖ ^ (2 * t))
      ≤ linFamAvg D l c N M H f b (fun _ _ => 0) := by
  classical
  rw [linFamAvg_eq_card_mul_sum]
  have hz : (0 : D.Idx l) ∈ D.parBox l H := by
    rw [IdxDatum.mem_parBox]
    intro j s
    simp
  have hle : ‖linCore D l c N M f b (fun _ _ => 0) (0 : D.Idx l)‖
      ≤ ∑ a ∈ D.parBox l H, ‖linCore D l c N M f b (fun _ _ => 0) a‖ :=
    Finset.single_le_sum (fun a _ => norm_nonneg _) hz
  rw [← linCore_zero D hl c N M f b t hm hb ht hN hM hfs]
  exact mul_le_mul_of_nonneg_left hle (by positivity)

end

end Work.Peluse.UControl
