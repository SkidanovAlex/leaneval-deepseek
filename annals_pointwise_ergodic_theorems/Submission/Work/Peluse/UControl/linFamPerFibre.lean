/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Peluse.PET.boxNormPow_control_linear_v2
import Submission.Work.Peluse.UControl.linFamPerFibreDefs

/-!
# The per-fibre form of the last step of the proof of Peluse's Proposition 3.4

Target: `Work.Peluse.UControl.linFamPerFibre`, the per-parameter (`a`) form of the last step of the
proof of Peluse's Proposition 3.4: the fibre `linFib` of the linear-configuration average at a single
parameter controls the level-`|I_{l-1}|` box-norm power of `f` along the datum's own direction family.

The proof is a direct application of the (proved) strengthened Lemma 4.10
`Work.Peluse.PET.boxNormPow_control_linear_v2` at `m = Fintype.card (D.I (l-1))` to

* the coefficient vector `cc` of `linFamPerFibreDefs` (`c 0 = 0`, `c (i+1) = petDir (pairIdx i)`),
  whose difference family `{c m - c i}` is the datum's own family reindexed by the bijection
  `idxPerm` (`cc_dir`, `idxPerm_bijective`);
* the slot functions `slotFun` (`F 0 = f`, the slots being translates of `f` or of its conjugate),

at the support `symIcc ((4·Cne+1)·N)`: the slot functions are translates of `f` by at most
`3·Cne·N`, so the support grows by the factor `(4·Cne+1)`, and the normalisation
`(N·M)⁻¹ = (4·Cne+1)·(((4·Cne+1)N)·M)⁻¹` shows that the hypothesis of Lemma 4.10 is exactly the
square of the fibre's normalisation.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped BigOperators
open Polynomial

namespace Work.Peluse.UControl

noncomputable section

open Work.Peluse

/-! ## Elementary consequences of the shift bound at a single parameter -/

/-- The shift bound at the single parameter `a` bounds the constant terms `β a i` by `3·Cne·N`
(evaluate at `y = 1` and `y = 2`). -/
lemma petBeta_le_three {D : IdxDatum} {l : ℕ} (c : ℤ) (a : D.Idx l)
    {M N Cne : ℕ} (hM : 2 ≤ M)
    (β : D.Idx l → Fin (Fintype.card (D.I (l - 1))) → ℤ)
    (hsh : ∀ i : Fin (Fintype.card (D.I (l - 1))), ∀ y ∈ Finset.Icc 1 M,
      |petDir D l c a i * (y : ℤ) + β a i| ≤ (Cne : ℤ) * (N : ℤ)) :
    ∀ i : Fin (Fintype.card (D.I (l - 1))), |β a i| ≤ 3 * (Cne : ℤ) * (N : ℤ) := by
  intro i
  have h1 := hsh i 1 (Finset.mem_Icc.mpr ⟨le_refl 1, by omega⟩)
  have h2 := hsh i 2 (Finset.mem_Icc.mpr ⟨by norm_num, hM⟩)
  have hd : |petDir D l c a i| ≤ 2 * (Cne : ℤ) * (N : ℤ) := by
    have h3 : petDir D l c a i = (petDir D l c a i * (2 : ℤ) + β a i)
        - (petDir D l c a i * (1 : ℤ) + β a i) := by ring
    rw [h3]
    calc |(petDir D l c a i * 2 + β a i) - (petDir D l c a i * 1 + β a i)|
        ≤ |petDir D l c a i * 2 + β a i| + |petDir D l c a i * 1 + β a i| := abs_sub _ _
      _ ≤ (Cne : ℤ) * (N : ℤ) + (Cne : ℤ) * (N : ℤ) := add_le_add h2 h1
      _ = 2 * (Cne : ℤ) * (N : ℤ) := by ring
  have h4 : β a i = (petDir D l c a i * (1 : ℤ) + β a i) - petDir D l c a i * (1 : ℤ) := by ring
  rw [h4]
  calc |(petDir D l c a i * 1 + β a i) - petDir D l c a i * 1|
      ≤ |petDir D l c a i * 1 + β a i| + |petDir D l c a i * 1| := abs_sub _ _
    _ ≤ (Cne : ℤ) * (N : ℤ) + 2 * (Cne : ℤ) * (N : ℤ) := by
        refine add_le_add h1 ?_
        rw [mul_one]; exact hd
    _ = 3 * (Cne : ℤ) * (N : ℤ) := by ring

/-- The shift bound at the single parameter `a` bounds the shifts `petDir·y` by `4·Cne·N`. -/
lemma petDir_mul_le_four {D : IdxDatum} {l : ℕ} (c : ℤ) (a : D.Idx l)
    {M N Cne : ℕ} (hM : 2 ≤ M)
    (β : D.Idx l → Fin (Fintype.card (D.I (l - 1))) → ℤ)
    (hsh : ∀ i : Fin (Fintype.card (D.I (l - 1))), ∀ y ∈ Finset.Icc 1 M,
      |petDir D l c a i * (y : ℤ) + β a i| ≤ (Cne : ℤ) * (N : ℤ)) :
    ∀ i : Fin (Fintype.card (D.I (l - 1))), ∀ y ∈ Finset.Icc 1 M,
      |petDir D l c a i * (y : ℤ)| ≤ 4 * (Cne : ℤ) * (N : ℤ) := by
  intro i y hy
  have h1 := hsh i y hy
  have hb := petBeta_le_three c a (D := D) hM β hsh i
  have h3 : petDir D l c a i * (y : ℤ) = (petDir D l c a i * (y : ℤ) + β a i) - β a i := by ring
  rw [h3]
  calc |(petDir D l c a i * (y : ℤ) + β a i) - β a i|
      ≤ |petDir D l c a i * (y : ℤ) + β a i| + |β a i| := abs_sub _ _
    _ ≤ (Cne : ℤ) * (N : ℤ) + 3 * (Cne : ℤ) * (N : ℤ) := add_le_add h1 hb
    _ = 4 * (Cne : ℤ) * (N : ℤ) := by ring

/-- A translate of `f` stays supported in the enlarged interval. -/
lemma supportIn_shift {f : ℤ → ℂ} {N : ℕ} (hfs : SupportIn f N) {p : ℤ} {N' : ℕ}
    (h : (N : ℤ) + |p| ≤ (N' : ℤ)) : SupportIn (Work.Peluse.shift p f) N' := by
  intro x hx
  show f (x + p) = 0
  apply hfs
  have hxZ : (N' : ℤ) < |x| := by
    have h2 : (N' : ℤ) < ((x.natAbs : ℕ) : ℤ) := by exact_mod_cast hx
    rwa [Int.natCast_natAbs] at h2
  have h2 : |x| ≤ |x + p| + |p| := by
    have h3 := abs_add_le (x + p) (-p)
    simpa [abs_neg, add_assoc] using h3
  have h4 : (N : ℤ) < |x + p| := by linarith
  have h5 : (N : ℤ) < (((x + p).natAbs : ℕ) : ℤ) := by rwa [Int.natCast_natAbs]
  exact_mod_cast h5

/-- The conjugate of a translate of `f` stays supported in the enlarged interval. -/
lemma supportIn_star_shift {f : ℤ → ℂ} {N : ℕ} (hfs : SupportIn f N) {p : ℤ} {N' : ℕ}
    (h : (N : ℤ) + |p| ≤ (N' : ℤ)) :
    SupportIn (fun x => star (f (x + p))) N' := by
  intro x hx
  have h1 : f (x + p) = 0 := supportIn_shift hfs h x hx
  show star (f (x + p)) = 0
  rw [h1, star_zero]

/-! ## Private abbreviations for the two correlations -/

/-- The (unnormalised) correlation of `linFib` at the parameter `a`. -/
private abbrev lsum (D : IdxDatum) (l : ℕ) (c : ℤ) (M : ℕ) (f : ℤ → ℂ)
    (b : Fin (Fintype.card (D.I (l - 1))) → Bool)
    (β : D.Idx l → Fin (Fintype.card (D.I (l - 1))) → ℤ) (a : D.Idx l) : ℂ :=
  ∑' x : ℤ, f x * ∑ y ∈ Finset.Icc 1 M,
    ∏ i : Fin (Fintype.card (D.I (l - 1))),
      (if b i then star (f (x + (petDir D l c a i * (y : ℤ) + β a i)))
        else f (x + (petDir D l c a i * (y : ℤ) + β a i)))

/-- The enlarged support scale `(4·Cne+1)·N`. -/
private abbrev Nl (Cne N : ℕ) : ℕ := (4 * Cne + 1) * N

/-- The fibre is the normalisation of the correlation `lsum` at the enlarged scale. -/
private lemma linFib_eq_norm (D : IdxDatum) (l : ℕ) (c : ℤ) (N M : ℕ) (f : ℤ → ℂ)
    (b : Fin (Fintype.card (D.I (l - 1))) → Bool)
    (β : D.Idx l → Fin (Fintype.card (D.I (l - 1))) → ℤ) (a : D.Idx l) (Cne : ℕ)
    (hN : 1 ≤ N) (hM : 1 ≤ M) :
    linFib D l c N M f b β a
      = ((4 * Cne + 1 : ℕ) : ℝ) * ‖(((Nl Cne N : ℕ) : ℂ) * (M : ℂ))⁻¹
          * lsum D l c M f b β a‖ := by
  have hN0 : (N : ℂ) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hM0 : (M : ℂ) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hC0 : (((4 * Cne + 1 : ℕ) : ℂ)) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hkey : ((N : ℂ) * (M : ℂ))⁻¹
      = (((4 * Cne + 1 : ℕ) : ℂ)) * ((((Nl Cne N : ℕ) : ℂ)) * (M : ℂ))⁻¹ := by
    rw [Nl, Nat.cast_mul]
    field_simp
  rw [linFib, lsum, hkey, mul_assoc, norm_mul, Complex.norm_natCast]

/-- The fibre is bounded by `3`. -/
private lemma linFib_le_three' {l : ℕ} (D : IdxDatum) (c : ℤ)
    (N M : ℕ) (f : ℤ → ℂ) (a : D.Idx l)
    (b : Fin (Fintype.card (D.I (l - 1))) → Bool)
    (β : D.Idx l → Fin (Fintype.card (D.I (l - 1))) → ℤ)
    (hN : 1 ≤ N) (hM : 1 ≤ M) (hf : ∀ x : ℤ, ‖f x‖ ≤ 1) (hfs : SupportIn f N) :
    linFib D l c N M f b β a ≤ 3 := by
  rw [linFib]
  have hcard : (symIcc N).card = 2 * N + 1 := by
    rw [symIcc]; simp; omega
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hsupp : ∀ x : ℤ, x ∉ (symIcc N) →
      f x * ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin (Fintype.card (D.I (l - 1))),
        (if b i then star (f (x + (petDir D l c a i * (y : ℤ) + β a i)))
          else f (x + (petDir D l c a i * (y : ℤ) + β a i))) = 0 := by
    intro x hx
    have hxN : N < x.natAbs := by
      rw [symIcc, Finset.mem_Icc] at hx
      omega
    rw [hfs x hxN, zero_mul]
  rw [tsum_eq_sum hsupp]
  have hstep : ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑ x ∈ symIcc N, f x *
        ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin (Fintype.card (D.I (l - 1))),
          (if b i then star (f (x + (petDir D l c a i * (y : ℤ) + β a i)))
            else f (x + (petDir D l c a i * (y : ℤ) + β a i)))‖
      ≤ ((N : ℝ) * (M : ℝ))⁻¹ * ((M : ℝ) * ((2 * N + 1 : ℕ) : ℝ)) := by
    rw [norm_mul]
    have hnorm : ‖((N : ℂ) * (M : ℂ))⁻¹‖ = ((N : ℝ) * (M : ℝ))⁻¹ := by
      rw [norm_inv, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    rw [hnorm]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ‖∑ x ∈ symIcc N, f x *
          ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin (Fintype.card (D.I (l - 1))),
            (if b i then star (f (x + (petDir D l c a i * (y : ℤ) + β a i)))
              else f (x + (petDir D l c a i * (y : ℤ) + β a i)))‖
        ≤ ∑ x ∈ symIcc N, (M : ℝ) := by
          refine le_trans (norm_sum_le _ _) ?_
          refine Finset.sum_le_sum (fun x _ => ?_)
          rw [norm_mul]
          refine le_trans (mul_le_mul_of_nonneg_right (hf x) (norm_nonneg _)) ?_
          rw [one_mul]
          refine le_trans (norm_sum_le _ _) ?_
          calc ∑ y ∈ Finset.Icc 1 M, ‖∏ i : Fin (Fintype.card (D.I (l - 1))),
                (if b i then star (f (x + (petDir D l c a i * (y : ℤ) + β a i)))
                  else f (x + (petDir D l c a i * (y : ℤ) + β a i)))‖
              ≤ ∑ _y ∈ Finset.Icc 1 M, (1 : ℝ) := by
                refine Finset.sum_le_sum (fun y _ => ?_)
                rw [norm_prod]
                refine Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => ?_)
                by_cases hbi : b i
                · simp [hbi, hf]
                · simp [hbi, hf]
            _ = (M : ℝ) := by
                rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; norm_num
      _ = (M : ℝ) * ((2 * N + 1 : ℕ) : ℝ) := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]; ring
  refine le_trans hstep ?_
  have hNM : ((N : ℝ) * (M : ℝ))⁻¹ * ((M : ℝ) * ((2 * N + 1 : ℕ) : ℝ))
      = ((2 * N + 1 : ℕ) : ℝ) / (N : ℝ) := by
    field_simp
  rw [hNM, div_le_iff₀ hN0]
  push_cast
  linarith

/-- **The direction family of Lemma 4.10 is the datum's own family.** -/
private lemma boxNormPow_slotFun_eq' {l : ℕ} (D : IdxDatum) (c : ℤ) (hl : 2 ≤ l)
    (hne : (Finset.univ : Finset (D.S (l - 1))).Nonempty) (a : D.Idx l) (f : ℤ → ℂ)
    (b : Fin (Fintype.card (D.I (l - 1))) → Bool)
    (β : D.Idx l → Fin (Fintype.card (D.I (l - 1))) → ℤ) (H : ℕ) (S : Finset ℤ) :
    Work.Peluse.boxNormPow (Fintype.card (D.I (l - 1)))
        (fun i : Fin (Fintype.card (D.I (l - 1))) =>
          Work.Peluse.arithIcc (cc D l c hne a
              ⟨Fintype.card (D.I (l - 1)), Nat.lt_succ_self _⟩
            - cc D l c hne a i.castSucc) H)
        S (slotFun D l hne f b β a ⟨Fintype.card (D.I (l - 1)), Nat.lt_succ_self _⟩)
      = Work.Peluse.boxNormPow (Fintype.card (D.I (l - 1)))
        (fun i : Fin (Fintype.card (D.I (l - 1))) =>
          Work.Peluse.arithIcc (petDir D l c a i) H)
        S f := by
  have hlast : slotFun D l hne f b β a ⟨Fintype.card (D.I (l - 1)), Nat.lt_succ_self _⟩
      = if b (fullSetIdx D l hne) then (fun x => star (f (x + β a (fullSetIdx D l hne))))
        else Work.Peluse.shift (β a (fullSetIdx D l hne)) f := by
    funext x
    rw [slotFun_pos_apply D l hne f b β a ⟨Fintype.card (D.I (l - 1)), Nat.lt_succ_self _⟩
        (by simp only [Fin.val_mk]; have := card_I_pos D l hne; omega) x,
      show predFinSucc _ ⟨Fintype.card (D.I (l - 1)), Nat.lt_succ_self _⟩ _ = lastIdx D l hne
        from Fin.ext (by simp [predFinSucc, lastIdx]),
      pairIdx_apply_last]
    by_cases hb : b (fullSetIdx D l hne)
    · simp [hb, Work.Peluse.shift]
    · simp [hb, Work.Peluse.shift]
  have hQ : (fun i : Fin (Fintype.card (D.I (l - 1))) =>
        Work.Peluse.arithIcc (cc D l c hne a
            ⟨Fintype.card (D.I (l - 1)), Nat.lt_succ_self _⟩
          - cc D l c hne a i.castSucc) H)
      = fun i : Fin (Fintype.card (D.I (l - 1))) =>
          Work.Peluse.arithIcc (petDir D l c a (idxPerm D l hne i)) H := by
    funext i
    rw [cc_dir D l hl c hne a i]
  rw [Work.Peluse.boxNormPow, Work.Peluse.boxNormPow, hQ]
  rw [Work.Peluse.Track.boxSumPow_comp_bij_proved
    (fun i : Fin (Fintype.card (D.I (l - 1))) => Work.Peluse.arithIcc (petDir D l c a i) H)
    S (slotFun D l hne f b β a ⟨Fintype.card (D.I (l - 1)), Nat.lt_succ_self _⟩)
    (idxPerm D l hne) (idxPerm_bijective D l hne)]
  rw [hlast]
  by_cases hb : b (fullSetIdx D l hne)
  · rw [if_pos hb,
      show (fun x => star (f (x + β a (fullSetIdx D l hne))))
        = (fun x => star ((Work.Peluse.shift (β a (fullSetIdx D l hne)) f) x)) from rfl,
      Work.Peluse.Pairing.boxSumPow_star, norm_star, Work.Peluse.BoxNorm.boxSumPow_shift]
  · rw [if_neg hb, Work.Peluse.BoxNorm.boxSumPow_shift]

/-! ## The target -/

theorem linFamPerFibre {l : ℕ} (D : Work.Peluse.UControl.IdxDatum) (c : ℤ) (hl : 2 ≤ l) :
    ∃ K : ℕ, 1 ≤ K ∧
      ∀ (N M : ℕ) (f : ℤ → ℂ) (Cne : ℕ) (a : D.Idx l)
        (b : Fin (Fintype.card (D.I (l - 1))) → Bool)
        (β : D.Idx l → Fin (Fintype.card (D.I (l - 1))) → ℤ) (Hf : ℕ) (γ' : ℝ),
        2 ≤ Fintype.card (D.I (l - 1)) → 1 ≤ N → 2 ≤ M → 1 ≤ Cne →
        (∀ x : ℤ, ‖f x‖ ≤ 1) → Work.Peluse.SupportIn f N →
        (∀ i : Fin (Fintype.card (D.I (l - 1))), ∀ y ∈ Finset.Icc 1 M,
          |Work.Peluse.UControl.petDir D l c a i * (y : ℤ) + β a i| ≤ (Cne : ℤ) * (N : ℤ)) →
        0 < γ' →
        Hf = ⌊γ' * (M : ℝ)⌋.toNat →
        1 ≤ Hf →
        γ' * (1000 * ((Fintype.card (D.I (l - 1)) : ℝ) + 1))
            ≤ ((N : ℝ) / (((4 * Cne + 1) * N : ℕ) : ℝ)) ^ 2
              * (Work.Peluse.UControl.linFib D l c N M f b β a) ^ 2 →
        ((((N : ℝ) / (((4 * Cne + 1) * N : ℕ) : ℝ)) ^ 2
              * (Work.Peluse.UControl.linFib D l c N M f b β a) ^ 2) / 1000) ^ K
          ≤ Work.Peluse.boxNormPow (Fintype.card (D.I (l - 1)))
              (fun i : Fin (Fintype.card (D.I (l - 1))) =>
                Work.Peluse.arithIcc (Work.Peluse.UControl.petDir D l c a i) Hf)
              (Work.Peluse.symIcc ((4 * Cne + 1) * N)) f := by
  by_cases hm : 0 < Fintype.card (D.I (l - 1))
  · obtain ⟨K, hK1, hK⟩ :=
      Work.Peluse.PET.boxNormPow_control_linear_v2 (m := Fintype.card (D.I (l - 1))) hm
    refine ⟨K, hK1, ?_⟩
    intro N M f Cne a b β Hf γ' h2 hN hM hCne hf hfs hsh hγ' hHf hHf1 hgauge
    have hne : (Finset.univ : Finset (D.S (l - 1))).Nonempty := by
      obtain ⟨s⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card (D.I (l - 1)))
      obtain ⟨x, hx⟩ := s.2
      exact ⟨x, Finset.mem_univ x⟩
    have hβ := petBeta_le_three c a (D := D) hM β hsh
    have hdir := petDir_mul_le_four c a (D := D) hM β hsh
    set γ : ℝ := ((N : ℝ) / (((4 * Cne + 1) * N : ℕ) : ℝ)) ^ 2
      * (linFib D l c N M f b β a) ^ 2 with hγdef
    by_cases hlf : linFib D l c N M f b β a = 0
    · -- the degenerate case: the fibre vanishes, so both sides are `0` and `≥ 0`
      have hγ0 : γ = 0 := by rw [hγdef, hlf]; ring
      have hK0 : K ≠ 0 := by omega
      rw [hγ0, zero_div, zero_pow hK0, Work.Peluse.boxNormPow]
      exact norm_nonneg _
    · -- the main case
      have hlfpos : 0 < linFib D l c N M f b β a :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hlf)
      set F : Fin (Fintype.card (D.I (l - 1)) + 1) → ℤ → ℂ :=
        slotFun D l hne f b β a with hFdef
      set cv : Fin (Fintype.card (D.I (l - 1)) + 1) → ℤ := cc D l c hne a with hcvdef
      -- ### the correlation identity: the slots of `linFib`, reindexed along `pairIdx`
      have hS : (∑' x : ℤ, F 0 x * ∑ y ∈ Finset.Icc 1 M,
            ∏ i : Fin (Fintype.card (D.I (l - 1))), F i.succ (x + cv i.succ * (y : ℤ)))
          = lsum D l c M f b β a := by
        rw [hFdef, hcvdef, lsum]
        refine tsum_congr fun x => ?_
        rw [slotFun_zero]
        congr 1
        exact Finset.sum_congr rfl fun y _ => prod_slot_eq D l c hne f b β a x (y : ℤ)
      -- ### the fibre is that correlation at the normalisation `(4·Cne+1)·((4·Cne+1)N·M)`
      have hnorm : ‖(((Nl Cne N : ℕ) : ℂ) * (M : ℂ))⁻¹ * lsum D l c M f b β a‖
          = linFib D l c N M f b β a / (((4 * Cne + 1 : ℕ)) : ℝ) := by
        rw [linFib_eq_norm D l c N M f b β a Cne hN (by omega)]
        have hpos : (0 : ℝ) < (((4 * Cne + 1 : ℕ)) : ℝ) := by positivity
        field_simp
      have hγeq : γ = ‖(((Nl Cne N : ℕ) : ℂ) * (M : ℂ))⁻¹ * lsum D l c M f b β a‖ ^ 2 := by
        have hcast : ((Nl Cne N : ℕ) : ℝ) = (((4 * Cne + 1 : ℕ)) : ℝ) * (N : ℝ) := by
          rw [Nl]; push_cast; ring
        have hratio : (N : ℝ) / (((4 * Cne + 1) * N : ℕ) : ℝ)
            = 1 / (((4 * Cne + 1 : ℕ)) : ℝ) := by
          rw [hcast]
          field_simp
        rw [hγdef, hratio, hnorm, div_pow, div_pow]
        field_simp
      have hΛv : γ ≤ ‖(((Nl Cne N : ℕ) : ℂ) * (M : ℂ))⁻¹ *
            (∑' x : ℤ, F 0 x * ∑ y ∈ Finset.Icc 1 M,
              ∏ i : Fin (Fintype.card (D.I (l - 1))),
                F i.succ (x + cv i.succ * (y : ℤ)))‖ ^ 2 := by
        rw [hS, ← hγeq]
      have hγpos : 0 < γ := by
        rw [hγdef]
        have : (0 : ℝ) < (N : ℝ) / (((4 * Cne + 1) * N : ℕ) : ℝ) := by positivity
        positivity
      have h3 : linFib D l c N M f b β a ≤ 3 := linFib_le_three' D c N M f a b β hN (by omega) hf hfs
      have hd5 : (5 : ℝ) ≤ (((4 * Cne + 1 : ℕ)) : ℝ) := by
        have h5 : 5 ≤ 4 * Cne + 1 := by omega
        exact_mod_cast h5
      have hγ1 : γ ≤ 1 := by
        rw [hγeq]
        have h1 : ‖(((Nl Cne N : ℕ) : ℂ) * (M : ℂ))⁻¹ * lsum D l c M f b β a‖ ≤ 3 / 5 := by
          rw [hnorm]
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < (((4 * Cne + 1 : ℕ)) : ℝ))]
          nlinarith [h3, hd5]
        calc ‖(((Nl Cne N : ℕ) : ℂ) * (M : ℂ))⁻¹ * lsum D l c M f b β a‖ ^ 2
            ≤ (3 / 5) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
          _ ≤ 1 := by norm_num
      -- ### the slot functions are `1`-bounded and supported in `symIcc ((4·Cne+1)·N)`
      have hFb : ∀ (i : Fin (Fintype.card (D.I (l - 1)) + 1)) (x : ℤ), ‖F i x‖ ≤ 1 := by
        intro i x
        rw [hFdef]
        exact slotFun_norm_le_one D l hne b β a hf i x
      have hbound : ∀ p : ℤ, |p| ≤ 3 * (Cne : ℤ) * (N : ℤ) →
          (N : ℤ) + |p| ≤ (((4 * Cne + 1) * N : ℕ) : ℤ) := by
        intro p hp
        have h1 : (N : ℤ) + |p| ≤ (N : ℤ) + 3 * (Cne : ℤ) * (N : ℤ) := by linarith
        have h2 : (N : ℤ) + 3 * (Cne : ℤ) * (N : ℤ) = ((3 * Cne + 1) * N : ℕ) := by
          push_cast; ring
        have h3 : ((3 * Cne + 1) * N : ℕ) ≤ (((4 * Cne + 1) * N : ℕ) : ℤ) := by
          exact_mod_cast Nat.mul_le_mul_right N (by omega : 3 * Cne + 1 ≤ 4 * Cne + 1)
        linarith
      have hFsup : ∀ i : Fin (Fintype.card (D.I (l - 1)) + 1),
          SupportIn (F i) ((4 * Cne + 1) * N) := by
        intro i
        by_cases hi : i.val = 0
        · rw [show i = 0 from Fin.ext hi, hFdef, slotFun_zero]
          exact hfs.mono (Nat.le_mul_of_pos_left N (by omega : 0 < 4 * Cne + 1))
        · intro x hx
          rw [hFdef, slotFun_pos_apply D l hne f b β a i hi x]
          by_cases hb : b (pairIdx D l hne (predFinSucc _ i hi))
          · rw [if_pos hb]
            exact supportIn_star_shift hfs (hbound _ (hβ _)) x hx
          · rw [if_neg hb]
            exact supportIn_shift hfs (hbound _ (hβ _)) x hx
      have hcy : ∀ y ∈ Finset.Icc 1 M, ∀ i : Fin (Fintype.card (D.I (l - 1)) + 1),
          |cv i * (y : ℤ)| ≤ (((4 * Cne + 1) * N : ℕ) : ℤ) := by
        intro y hy i
        by_cases hi : i.val = 0
        · rw [hcvdef, show i = 0 from Fin.ext hi, cc_zero, zero_mul, abs_zero]
          exact Int.natCast_nonneg _
        · rw [hcvdef, cc_pos D l c hne a i hi]
          refine le_trans (hdir _ y hy) ?_
          have h4 : 4 * (Cne : ℤ) * (N : ℤ) = ((4 * Cne * N : ℕ) : ℤ) := by push_cast; ring
          rw [h4]
          exact_mod_cast Nat.mul_le_mul_right N (by omega : 4 * Cne ≤ 4 * Cne + 1)
      have hgauge' : γ' ≤ γ / (1000 * ((Fintype.card (D.I (l - 1)) : ℝ) + 1)) := by
        rw [le_div_iff₀ (by positivity)]
        exact hgauge
      have hHf' : 1 ≤ ⌊γ' * (M : ℝ)⌋.toNat := by
        rw [← hHf]; exact hHf1
      -- ### Lemma 4.10 at the level `card (D.I (l-1))`
      have hres := hK cv (by rw [hcvdef]; exact cc_zero D l c hne a)
        (by positivity) (by omega) F hγpos hγ' hγ1 hFb hFsup hcy hgauge' hHf' hΛv
      -- ### identify the direction family of the conclusion with the datum's own family
      rw [← hHf] at hres
      have hconv : Work.Peluse.boxNormPow (Fintype.card (D.I (l - 1)))
            (fun i : Fin (Fintype.card (D.I (l - 1))) =>
              Work.Peluse.arithIcc (cv ⟨Fintype.card (D.I (l - 1)), Nat.lt_succ_self _⟩
                - cv i.castSucc) Hf)
            (Work.Peluse.symIcc ((4 * Cne + 1) * N))
            (F ⟨Fintype.card (D.I (l - 1)), Nat.lt_succ_self _⟩)
          = Work.Peluse.boxNormPow (Fintype.card (D.I (l - 1)))
            (fun i : Fin (Fintype.card (D.I (l - 1))) =>
              Work.Peluse.arithIcc (petDir D l c a i) Hf)
            (Work.Peluse.symIcc ((4 * Cne + 1) * N)) f := by
        rw [hFdef, hcvdef]
        exact boxNormPow_slotFun_eq' D c hl hne a f b β Hf (Work.Peluse.symIcc ((4 * Cne + 1) * N))
      rw [hconv] at hres
      simpa only [hγdef] using hres
  · refine ⟨1, le_refl 1, ?_⟩
    intro N M f Cne a b β Hf γ' h2 hN hM hCne hf hfs hsh hγ' hHf hHf1 hgauge
    exact absurd h2 (by omega)

end

end Work.Peluse.UControl
