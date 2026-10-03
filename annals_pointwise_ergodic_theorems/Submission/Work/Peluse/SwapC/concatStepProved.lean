import Mathlib
import Submission.Work.Peluse.SwapC.concatMain
import Submission.Work.Peluse.SwapC.concatFinish
import Submission.Work.Peluse.SwapCS0.pboxOneExplicit
import Submission.Work.Peluse.SwapCS0.acfCS

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.SwapC

noncomputable section

open Work.Peluse
open Work.Peluse.LadderP.Swap

/-!
# `Work.Peluse.SwapC.concatStepProved` — KKL Lemma 6.1

The concatenation step of Kravitz–Kuca–Leng §6, in the `pbox` vocabulary of this chapter.

* For `1 ≤ s` the argument is the full chain: the *expansion* (`Work.Peluse.SwapC.expansion`), the
  Gowers–Cauchy–Schwarz bound of the corner family, the *peel back* (`Work.Peluse.SwapC.peelBack`)
  and the power-mean brick `Work.Peluse.SwapC.concatFinish`, which produce
  `(δ²/3)^{2^{2s}} ≤ avg_p pbox (2s+1) (concatenated slots)`.
* The degenerate case `s = 0` is *not* covered by that chain (the level-`0` cube sum is complex, so
  no Gowers–Cauchy–Schwarz step is available), and is proved separately below by an elementary
  Cauchy–Schwarz inequality in `ℓ²`: with `a i = qH i` and `A τ = ∑'_x f (x+τ) · conj (f x)`,

  `pbox 1 [a] [b] = |S|⁻¹ M⁻⁴ ∑'_x ‖∑_m f (x + pdir a b m)‖²
                 = |S|⁻¹ M⁻⁴ (∑_{m,m'} A (pdir a b m − pdir a b m')).re`,

  and `(∑_{i,c,c'} A (a i (c−c')))² ≤ |S| ∑_{i,j,m,m'} A (a j (m₁−m₁') − a i (m₂−m₂'))`
  (`Work.Peluse.SwapCS0.acfCS`).  The case closes with `C = 1`, `e = 2`. -/

/-! ## 0. The autocorrelation -/

/-- The autocorrelation of `f` at lag `τ` (a finite sum when `f` is finitely supported). -/
abbrev acorr (f : ℤ → ℂ) (τ : ℤ) : ℂ := ∑' x : ℤ, f (x + τ) * star (f x)

/-- `avg` of a constant multiple. -/
lemma avg_const_mul {ι : Type} [Fintype ι] (c : ℝ) (F : ι → ℝ) :
    avg (fun i => c * F i) = c * avg F := by
  rw [avg, avg, (Finset.mul_sum Finset.univ F c).symm]
  ring

/-! ## 1. Elementary consequences of the translate-support hypothesis -/

/-- A function supported in the translate `x₀ + symIcc N` is finitely supported. -/
lemma finSuppZ_of_translate_support {N : ℕ} {x₀ : ℤ} {f : ℤ → ℂ}
    (hsup : ∀ x : ℤ, (N : ℤ) < |x - x₀| → f x = 0) : Work.Peluse.FinSuppZ f := by
  refine ⟨N + x₀.natAbs, fun x hx => hsup x ?_⟩
  have h1 : (N : ℤ) + (x₀.natAbs : ℤ) < (x.natAbs : ℤ) := by
    exact_mod_cast (by omega : N + x₀.natAbs < x.natAbs)
  have h2 : ((x.natAbs : ℤ) - (x₀.natAbs : ℤ)) ≤ |x - x₀| := by
    have h3 : |x| ≤ |x - x₀| + |x₀| := by simpa using abs_add_le (x - x₀) x₀
    have h4 : |x| = (x.natAbs : ℤ) := (Int.natCast_natAbs x).symm
    have h5 : |x₀| = (x₀.natAbs : ℤ) := (Int.natCast_natAbs x₀).symm
    rw [h4, h5] at h3
    linarith
  linarith

/-- The translate-support hypothesis, in the form `x ∉ S₀ → f x = 0`. -/
lemma vanishes_off_translate' {N : ℕ} {x₀ : ℤ} {f : ℤ → ℂ}
    (hsup : ∀ x : ℤ, (N : ℤ) < |x - x₀| → f x = 0) :
    ∀ x : ℤ, x ∉ (Work.Peluse.symIcc N).map (Equiv.addRight x₀).toEmbedding → f x = 0 := by
  intro x hx
  refine hsup x ?_
  have hz : x - x₀ ∉ Work.Peluse.symIcc N := fun hmem =>
    hx (Finset.mem_map.mpr ⟨x - x₀, hmem, by simp [Equiv.coe_addRight]⟩)
  have hlt : ¬ ((x - x₀).natAbs ≤ N) := fun hle => hz ((mem_symIcc_iff).mpr hle)
  have h3 : N < (x - x₀).natAbs := by omega
  rw [← Int.natCast_natAbs (x - x₀)]
  exact_mod_cast h3

/-! ## 2. The level-one box sum, explicitly -/

/-- `pbox 1 [a] [b]`, expressed through the autocorrelation. -/
lemma pbox_one_slots {M : ℕ} (a b : ℤ) (S : Finset ℤ) (f : ℤ → ℂ)
    (hf : Work.Peluse.FinSuppZ f) :
    pbox 1 (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) M S f
      = ((S.card : ℝ))⁻¹ * ((M : ℝ) ^ 4)⁻¹ *
        (∑ m : Fin M × Fin M, ∑ m' : Fin M × Fin M,
          acorr f (pdir a b m - pdir a b m')).re := by
  rw [Work.Peluse.SwapCS0.pboxOneExplicit (M := M) (q₁ := fun _ : Fin 1 => a)
    (q₂ := fun _ : Fin 1 => b) (S := S) f hf]
  congr 1
  have hg := Work.Peluse.SwapCS0.gramShift (σ := fun m : Fin M × Fin M => pdir a b m) f hf
  have hre := congrArg Complex.re hg
  simp only [Complex.ofReal_re, Complex.re_sum] at hre
  rw [hre]
  simp only [Complex.re_sum]

/-- `pbox 1 [a] [0]`, with the multiplicity `M²` of the raw slot collapsed. -/
lemma pbox_one_raw {M : ℕ} (a : ℤ) (S : Finset ℤ) (f : ℤ → ℂ)
    (hf : Work.Peluse.FinSuppZ f) :
    pbox 1 (fun _ : Fin 1 => a) (fun _ : Fin 1 => (0 : ℤ)) M S f
      = ((S.card : ℝ))⁻¹ * ((M : ℝ) ^ 2)⁻¹ *
        (∑ c : Fin M, ∑ c' : Fin M, acorr f (a * ((c : ℤ) - (c' : ℤ)))).re := by
  rw [pbox_one_slots a 0 S f hf]
  have harg : ∀ m m' : Fin M × Fin M,
      pdir a 0 m - pdir a 0 m' = a * (((m.1 : ℕ) : ℤ) - ((m'.1 : ℕ) : ℤ)) := by
    intro m m'
    simp only [pdir]
    ring
  have hcollapse' : ∀ (G : Fin M → Fin M → ℂ),
      (∑ m : Fin M × Fin M, ∑ m' : Fin M × Fin M, G m.1 m'.1)
        = (((M : ℝ) * (M : ℝ) : ℝ) : ℂ) * ∑ c : Fin M, ∑ c' : Fin M, G c c' := by
    intro G
    have h2gen : ∀ z : ℂ, (∑ _y : Fin M, ∑ _y' : Fin M, z)
        = (M : ℂ) * ((M : ℂ) * z) := by
      intro z
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc (∑ m : Fin M × Fin M, ∑ m' : Fin M × Fin M, G m.1 m'.1)
        = ∑ x : Fin M, ∑ y : Fin M, ∑ x' : Fin M, ∑ _y' : Fin M, G x x' := by
          simp only [Fintype.sum_prod_type]
      _ = ∑ x : Fin M, ∑ x' : Fin M, ∑ y : Fin M, ∑ _y' : Fin M, G x x' := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_comm]
      _ = ∑ x : Fin M, ∑ x' : Fin M, (M : ℂ) * ((M : ℂ) * G x x') := by
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => h2gen _
      _ = (((M : ℝ) * (M : ℝ) : ℝ) : ℂ) * ∑ c : Fin M, ∑ c' : Fin M, G c c' := by
          rw [show (((M : ℝ) * (M : ℝ) : ℝ) : ℂ) = (M : ℂ) * (M : ℂ) from by push_cast; ring]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x' _ => ?_
          ring
  have hcollapse : (∑ m : Fin M × Fin M, ∑ m' : Fin M × Fin M,
        acorr f (a * (((m.1 : ℕ) : ℤ) - ((m'.1 : ℕ) : ℤ))))
      = (((M : ℝ) * (M : ℝ) : ℝ) : ℂ)
        * ∑ c : Fin M, ∑ c' : Fin M, acorr f (a * ((c : ℤ) - (c' : ℤ))) :=
    hcollapse' (fun c c' => acorr f (a * ((c : ℤ) - (c' : ℤ))))
  have hre : (∑ m : Fin M × Fin M, ∑ m' : Fin M × Fin M,
        acorr f (pdir a 0 m - pdir a 0 m')).re
      = ((M : ℝ) * (M : ℝ)) * (∑ c : Fin M, ∑ c' : Fin M,
          acorr f (a * ((c : ℤ) - (c' : ℤ)))).re := by
    rw [Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun m' _ => by
      rw [harg m m']))]
    rw [hcollapse]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hre]
  have hM4 : ((M : ℝ) ^ 4)⁻¹ * (M : ℝ) ^ 2 = ((M : ℝ) ^ 2)⁻¹ := by
    have h2 : ((M : ℝ) ^ 4) = ((M : ℝ) ^ 2) ^ 2 := by ring
    rw [h2, pow_two, mul_inv]
    by_cases h : ((M : ℝ) ^ 2) = 0
    · rw [h]; ring
    · rw [mul_assoc, inv_mul_cancel₀ h, mul_one]
  rw [← hM4]
  ring

/-! ## 3. The `s = 0` case -/

/-- **KKL Lemma 6.1 at `s = 0`.** -/
theorem concatZeroCase {I : Type} [Fintype I] [Nonempty I] (qH : I → ℤ)
    (q₁ q₂ : I → Fin 0 → ℤ) (M N : ℕ) (x₀ : ℤ) (δ : ℝ) (f : ℤ → ℂ)
    (hM : 1 ≤ M) (hsup : ∀ x : ℤ, (N : ℤ) < |x - x₀| → f x = 0)
    (hbd : ∀ x : ℤ, ‖f x‖ ≤ 1) (hδ : 0 < δ)
    (h : δ ≤ avg (fun i : I => pbox 1 (Fin.cons (qH i) (q₁ i)) (Fin.cons (0 : ℤ) (q₂ i)) M
      (symIcc N) f)) :
    δ ^ 2 ≤ avg (fun p : I × I => pbox 1
        (Fin.snoc (Fin.append (q₁ p.1) (q₁ p.2)) (qH p.2))
        (Fin.snoc (Fin.append (q₂ p.1) (q₂ p.2)) (qH p.1)) M (symIcc N) f) := by
  classical
  have hfin : Work.Peluse.FinSuppZ f := finSuppZ_of_translate_support hsup
  have hvan : ∀ x : ℤ, x ∉ (symIcc N).map (Equiv.addRight x₀).toEmbedding → f x = 0 :=
    vanishes_off_translate' hsup
  have hSc : 0 < ((symIcc N).card : ℝ) := by
    have h0 : 0 < (symIcc N).card := Finset.card_pos.mpr ⟨0, by rw [mem_symIcc_iff]; simp⟩
    exact_mod_cast h0
  have hcardI : ((Fintype.card I : ℝ)) ≠ 0 := by
    have h0 : 0 < Fintype.card I := Fintype.card_pos_iff.mpr inferInstance
    exact_mod_cast (Nat.pos_iff_ne_zero.mp h0)
  -- the two invocations of the level-one formula
  have hypForm : ∀ i : I, pbox 1 (Fin.cons (qH i) (q₁ i)) (Fin.cons (0 : ℤ) (q₂ i)) M
      (symIcc N) f
      = ((symIcc N).card : ℝ)⁻¹ * ((M : ℝ) ^ 2)⁻¹ *
        (∑ c : Fin M, ∑ c' : Fin M, acorr f (qH i * ((c : ℤ) - (c' : ℤ)))).re := by
    intro i
    have hq : Fin.cons (qH i) (q₁ i) = (fun _ : Fin 1 => qH i) := by
      funext j; fin_cases j <;> simp
    have hq2 : Fin.cons (0 : ℤ) (q₂ i) = (fun _ : Fin 1 => (0 : ℤ)) := by
      funext j; fin_cases j <;> simp
    rw [hq, hq2]
    exact pbox_one_raw (qH i) (symIcc N) f hfin
  have conclForm : ∀ p : I × I, pbox 1
      (Fin.snoc (Fin.append (q₁ p.1) (q₁ p.2)) (qH p.2))
      (Fin.snoc (Fin.append (q₂ p.1) (q₂ p.2)) (qH p.1)) M (symIcc N) f
      = ((symIcc N).card : ℝ)⁻¹ * ((M : ℝ) ^ 4)⁻¹ *
        (∑ m : Fin M × Fin M, ∑ m' : Fin M × Fin M,
          acorr f (pdir (qH p.2) (qH p.1) m - pdir (qH p.2) (qH p.1) m')).re := by
    intro p
    have h1 : Fin.snoc (Fin.append (q₁ p.1) (q₁ p.2)) (qH p.2) = (fun _ : Fin 1 => qH p.2) := by
      funext j; fin_cases j <;> simp [Fin.snoc]
    have h2 : Fin.snoc (Fin.append (q₂ p.1) (q₂ p.2)) (qH p.1) = (fun _ : Fin 1 => qH p.1) := by
      funext j; fin_cases j <;> simp [Fin.snoc]
    rw [h1, h2, pbox_one_slots (qH p.2) (qH p.1) (symIcc N) f hfin]
  -- the two sums
  set P : ℝ := ∑ i : I, (∑ c : Fin M, ∑ c' : Fin M,
      acorr f (qH i * ((c : ℤ) - (c' : ℤ)))).re with hP
  set Q : ℝ := ∑ p : I × I, (∑ m : Fin M × Fin M, ∑ m' : Fin M × Fin M,
      acorr f (pdir (qH p.2) (qH p.1) m - pdir (qH p.2) (qH p.1) m')).re with hQ
  have hPeq : P = (∑ i : I, ∑ c : Fin M, ∑ c' : Fin M,
      acorr f (qH i * ((c : ℤ) - (c' : ℤ)))).re := by
    rw [hP]
    simp only [Complex.re_sum]
  have hQeq : Q = (∑ i : I, ∑ j : I, ∑ m : Fin M × Fin M, ∑ m' : Fin M × Fin M,
      acorr f (qH j * ((m.1 : ℤ) - (m'.1 : ℤ)) - qH i * ((m.2 : ℤ) - (m'.2 : ℤ)))).re := by
    rw [hQ, Fintype.sum_prod_type]
    simp only [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun m _ => ?_
    refine Finset.sum_congr rfl fun m' _ => ?_
    have harg : pdir (qH j) (qH i) m - pdir (qH j) (qH i) m'
        = qH j * ((m.1 : ℤ) - (m'.1 : ℤ)) - qH i * ((m.2 : ℤ) - (m'.2 : ℤ)) := by
      simp only [pdir]; ring
    rw [harg]
  -- the Cauchy–Schwarz of the `s = 0` case
  have hacf := Work.Peluse.SwapCS0.acfCS (I := I) (M := M) (a := qH) (f := f)
    ((symIcc N).map (Equiv.addRight x₀).toEmbedding) hvan hbd
  have hPQ : P ^ 2 ≤ ((symIcc N).card : ℝ) * Q := by
    have hcard : ((symIcc N).map (Equiv.addRight x₀).toEmbedding).card
        = (symIcc N).card := Finset.card_map _
    rw [← hPeq, ← hQeq, hcard] at hacf
    exact hacf
  -- the hypothesis, in terms of `P`
  have hhyp : δ ≤ ((symIcc N).card : ℝ)⁻¹ * ((M : ℝ) ^ 2)⁻¹ *
      (((Fintype.card I : ℝ))⁻¹ * P) := by
    have h2 : avg (fun i : I => ((symIcc N).card : ℝ)⁻¹ * ((M : ℝ) ^ 2)⁻¹ *
        (∑ c : Fin M, ∑ c' : Fin M, acorr f (qH i * ((c : ℤ) - (c' : ℤ)))).re)
        = ((symIcc N).card : ℝ)⁻¹ * ((M : ℝ) ^ 2)⁻¹ * ((Fintype.card I : ℝ))⁻¹ * P := by
      rw [avg_const_mul, avg, ← hP]
      ring
    rw [funext hypForm, h2] at h
    simpa only [mul_assoc] using h
  -- the conclusion, in terms of `Q`
  have hconcl : avg (fun p : I × I => pbox 1
      (Fin.snoc (Fin.append (q₁ p.1) (q₁ p.2)) (qH p.2))
      (Fin.snoc (Fin.append (q₂ p.1) (q₂ p.2)) (qH p.1)) M (symIcc N) f)
      = ((symIcc N).card : ℝ)⁻¹ * ((M : ℝ) ^ 4)⁻¹ *
        (((Fintype.card (I × I) : ℝ))⁻¹ * Q) := by
    have h2 : avg (fun p : I × I => ((symIcc N).card : ℝ)⁻¹ * ((M : ℝ) ^ 4)⁻¹ *
        (∑ m : Fin M × Fin M, ∑ m' : Fin M × Fin M,
          acorr f (pdir (qH p.2) (qH p.1) m - pdir (qH p.2) (qH p.1) m')).re)
        = ((symIcc N).card : ℝ)⁻¹ * ((M : ℝ) ^ 4)⁻¹ *
          (((Fintype.card (I × I) : ℝ))⁻¹ * Q) := by
      rw [avg_const_mul, avg, ← hQ]
    rw [funext conclForm, h2]
  rw [hconcl]
  -- the arithmetic
  have hcardII : (Fintype.card (I × I) : ℝ) = ((Fintype.card I : ℝ)) * ((Fintype.card I : ℝ)) := by
    rw [Fintype.card_prod]
    push_cast
    ring
  have hid : (((symIcc N).card : ℝ)⁻¹ * ((M : ℝ) ^ 2)⁻¹ * ((Fintype.card I : ℝ))⁻¹) ^ 2
        * ((symIcc N).card : ℝ)
      = ((symIcc N).card : ℝ)⁻¹ * ((M : ℝ) ^ 4)⁻¹
        * ((Fintype.card (I × I) : ℝ))⁻¹ := by
    rw [hcardII]
    have hS : ((symIcc N).card : ℝ) ≠ 0 := ne_of_gt hSc
    have hM0 : (M : ℝ) ≠ 0 := by
      have : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
      exact ne_of_gt this
    have hn : (Fintype.card I : ℝ) ≠ 0 := hcardI
    field_simp
  have hstep : δ ^ 2 ≤ (((symIcc N).card : ℝ)⁻¹ * ((M : ℝ) ^ 2)⁻¹
      * ((Fintype.card I : ℝ))⁻¹) ^ 2 * ((symIcc N).card : ℝ) * Q := by
    have h1 : δ ^ 2 ≤ (((symIcc N).card : ℝ)⁻¹ * ((M : ℝ) ^ 2)⁻¹
        * (((Fintype.card I : ℝ))⁻¹ * P)) ^ 2 :=
      pow_le_pow_left₀ (le_of_lt hδ) hhyp 2
    have h2 : (((symIcc N).card : ℝ)⁻¹ * ((M : ℝ) ^ 2)⁻¹
        * (((Fintype.card I : ℝ))⁻¹ * P)) ^ 2
        = (((symIcc N).card : ℝ)⁻¹ * ((M : ℝ) ^ 2)⁻¹
          * ((Fintype.card I : ℝ))⁻¹) ^ 2 * P ^ 2 := by ring
    rw [h2] at h1
    refine le_trans h1 ?_
    calc (((symIcc N).card : ℝ)⁻¹ * ((M : ℝ) ^ 2)⁻¹ * ((Fintype.card I : ℝ))⁻¹) ^ 2 * P ^ 2
        ≤ (((symIcc N).card : ℝ)⁻¹ * ((M : ℝ) ^ 2)⁻¹ * ((Fintype.card I : ℝ))⁻¹) ^ 2
            * (((symIcc N).card : ℝ) * Q) :=
          mul_le_mul_of_nonneg_left hPQ (sq_nonneg _)
      _ = (((symIcc N).card : ℝ)⁻¹ * ((M : ℝ) ^ 2)⁻¹ * ((Fintype.card I : ℝ))⁻¹) ^ 2
            * ((symIcc N).card : ℝ) * Q := by ring
  rw [hid] at hstep
  simpa only [mul_assoc] using hstep

/-! ## 4. The `s ≥ 1` case -/

/-- The power bookkeeping of the `s ≥ 1` case: with `C = 3^{-2^{2s}}` and `e = 2^{2s+1}`,
`C · δ^e = (δ²/3)^{2^{2s}}`. -/
lemma concatPowShift (s : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (3 : ℝ)⁻¹ ^ (2 ^ (2 * s)) * δ ^ (2 ^ (2 * s + 1))
      = (δ ^ 2 / 3) ^ ((2 : ℝ) ^ (2 * s)) := by
  have hr : (2 : ℝ) ^ (2 * s) = ((2 ^ (2 * s) : ℕ) : ℝ) := by push_cast; ring
  have hE : 2 * 2 ^ (2 * s) = 2 ^ (2 * s + 1) := by rw [pow_succ']
  rw [hr, Real.rpow_natCast, div_pow, ← pow_mul, hE]
  rw [div_eq_mul_inv, inv_pow]
  ring

/-- **KKL Lemma 6.1** (Kravitz–Kuca–Leng Lemma 6.1): the raw slot `qH i[M]` is concatenated across
two independent indices, the other slots doubled. -/
theorem concatStepProved : ∀ s : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ e : ℕ, 1 ≤ e ∧
    ∀ (I : Type) [Fintype I] [Nonempty I] (qH : I → ℤ) (q₁ q₂ : I → Fin s → ℤ)
      (M N : ℕ) (x₀ : ℤ) (δ : ℝ) (f : ℤ → ℂ),
      1 ≤ M → (∀ x : ℤ, (N : ℤ) < |x - x₀| → f x = 0) → (∀ x : ℤ, ‖f x‖ ≤ 1) → 0 < δ →
      δ ≤ Work.Peluse.LadderP.Swap.avg (fun i : I => Work.Peluse.LadderP.Swap.pbox (s + 1)
              (Fin.cons (qH i) (q₁ i)) (Fin.cons 0 (q₂ i)) M (Work.Peluse.symIcc N) f) →
      C * δ ^ e ≤ Work.Peluse.LadderP.Swap.avg (fun p : I × I =>
        Work.Peluse.LadderP.Swap.pbox (s + s + 1)
          (Fin.snoc (Fin.append (q₁ p.1) (q₁ p.2)) (qH p.2))
          (Fin.snoc (Fin.append (q₂ p.1) (q₂ p.2)) (qH p.1)) M (Work.Peluse.symIcc N) f) := by
  intro s
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs
    refine ⟨1, one_pos, 2, by norm_num, ?_⟩
    intro I _ _ qH q₁ q₂ M N x₀ δ f hM hsup hbd hδ h
    simpa only [one_mul, Nat.zero_add] using
      concatZeroCase qH q₁ q₂ M N x₀ δ f hM hsup hbd hδ h
  · refine ⟨(3 : ℝ)⁻¹ ^ (2 ^ (2 * s)), by positivity, 2 ^ (2 * s + 1), ?_, ?_⟩
    · exact Nat.one_le_two_pow
    · intro I _ _ qH q₁ q₂ M N x₀ δ f hM hsup hbd hδ h
      have hfin : Work.Peluse.FinSuppZ f := finSuppZ_of_translate_support hsup
      have hexp := expansion s M N hM hs qH q₁ q₂ δ f x₀ hδ hbd hsup hfin h
      have hfinC := concatFinish s M N hs qH q₁ q₂ δ f hδ hfin hexp
      rw [concatPowShift s hδ]
      exact hfinC

end

end Work.Peluse.SwapC
