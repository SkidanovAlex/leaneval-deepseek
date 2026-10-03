/-
# Glue lemmas for `Work.Peluse.SwapC.concatStep` (KKL Lemma 6.1)

The Cauchy–Schwarz step in the base variable (with the *support* set of `f` separated from the
*normalising* set of the hypothesis), the support bookkeeping for the gauge, and the assembly
lemmas of the concatenation step.  Nothing in this file uses `sorry`.
-/
import Mathlib
import Submission.Work.Peluse.SwapC.gauge_sq_eq
import Submission.Work.Peluse.SwapC.hyp_gauge
import Submission.Work.Peluse.SwapC.concat_ident
import Submission.Work.Peluse.SwapC.mCubeSum_split
import Submission.Work.Peluse.SwapC.pbox_peel
import Submission.Work.Peluse.SwapC.pbox_perm
import Submission.Work.Peluse.SwapC.pbox_eq_re
import Submission.Work.Peluse.SwapC.GCS

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.SwapC

noncomputable section

open Work.Peluse
open Work.Peluse.LadderP.Swap

/-! ## 1. Cauchy–Schwarz in the base variable

KKL step 3.  The hypothesis of the node bounds `δ` by the box norm of `f` normalised by `|S|`, and
`hyp_gauge` turns it into `δ·|S| ≤ Re ∑_y f y · gauge y`.  Cauchy–Schwarz in `y` then costs the
`ℓ²`-mass of `f`, which is bounded by the cardinality of its *support* (not of `S`); the node's
support is a translate of `S`, so the two cardinalities agree. -/

/-- **Cauchy–Schwarz in the base variable, with the support separated from the normalisation.**
If `f` vanishes off `S₀`, is `1`-bounded, and `δ·|S| ≤ Re ∑_x f x Φ x` with `S₀ ⊆ T` and
`|S₀| ≤ |S|`, then `δ²·|S| ≤ ∑_x ‖Φ x‖²`. -/
lemma csFin {S S₀ T : Finset ℤ} {f Φ : ℤ → ℂ} {δ : ℝ}
    (hf : ∀ x : ℤ, x ∉ S₀ → f x = 0) (hΦ : ∀ x : ℤ, x ∉ T → Φ x = 0)
    (hST : S₀ ⊆ T) (hcard : S₀.card ≤ S.card) (hb : ∀ x : ℤ, ‖f x‖ ≤ 1) (hδ : 0 ≤ δ)
    (hSpos : 0 < S.card)
    (h : δ * (S.card : ℝ) ≤ (∑' x : ℤ, f x * Φ x).re) :
    δ ^ 2 * (S.card : ℝ) ≤ ∑' x : ℤ, ‖Φ x‖ ^ 2 := by
  have htsum_f : (∑' x : ℤ, f x * Φ x) = ∑ x ∈ S₀, f x * Φ x :=
    tsum_eq_sum (s := S₀) (fun x hx => by rw [hf x hx, zero_mul])
  have htsum_Φ : (∑' x : ℤ, ‖Φ x‖ ^ 2) = ∑ x ∈ T, ‖Φ x‖ ^ 2 :=
    tsum_eq_sum (s := T) (fun x hx => by rw [hΦ x hx, norm_zero]; norm_num)
  have hfsum : ∑ x ∈ S₀, ‖f x‖ ^ 2 ≤ (S.card : ℝ) := by
    have hterm : ∀ x ∈ S₀, ‖f x‖ ^ 2 ≤ (1 : ℝ) := fun x _ => by
      have h1 : ‖f x‖ ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hb x) 2
      simpa using h1
    calc ∑ x ∈ S₀, ‖f x‖ ^ 2 ≤ ∑ _x ∈ S₀, (1 : ℝ) := Finset.sum_le_sum hterm
      _ = (S₀.card : ℝ) := by simp
      _ ≤ (S.card : ℝ) := by exact_mod_cast hcard
  have hΦsum : ∑ x ∈ S₀, ‖Φ x‖ ^ 2 ≤ ∑ x ∈ T, ‖Φ x‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hST fun x _ _ => sq_nonneg _
  have hcs : ‖∑ x ∈ S₀, f x * Φ x‖ ^ 2
      ≤ (S.card : ℝ) * (∑ x ∈ T, ‖Φ x‖ ^ 2) := by
    have h1 := Work.Peluse.BoxNorm.cauchySchwarzC S₀ f (fun x => star (Φ x))
    have h2 : (∑ x ∈ S₀, ‖f x‖ ^ 2) * (∑ x ∈ S₀, ‖star (Φ x)‖ ^ 2)
        ≤ (S.card : ℝ) * (∑ x ∈ T, ‖Φ x‖ ^ 2) := by
      have h3 : (∑ x ∈ S₀, ‖star (Φ x)‖ ^ 2) = ∑ x ∈ S₀, ‖Φ x‖ ^ 2 := by simp
      rw [h3]
      exact mul_le_mul hfsum hΦsum (Finset.sum_nonneg fun x _ => sq_nonneg _) (by positivity)
    have h4 : (∑ x ∈ S₀, f x * star (star (Φ x))) = ∑ x ∈ S₀, f x * Φ x := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [star_star]
    rw [h4] at h1
    exact le_trans h1 h2
  have hRe : δ * (S.card : ℝ) ≤ ‖∑ x ∈ S₀, f x * Φ x‖ := by
    calc δ * (S.card : ℝ) ≤ (∑' x : ℤ, f x * Φ x).re := h
      _ = (∑ x ∈ S₀, f x * Φ x).re := by rw [htsum_f]
      _ ≤ ‖∑ x ∈ S₀, f x * Φ x‖ := Complex.re_le_norm _
  have hsq : (δ * (S.card : ℝ)) ^ 2 ≤ ‖∑ x ∈ S₀, f x * Φ x‖ ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hδ (by positivity)) hRe 2
  have hchain : (δ * (S.card : ℝ)) ^ 2 ≤ (S.card : ℝ) * (∑ x ∈ T, ‖Φ x‖ ^ 2) :=
    le_trans hsq hcs
  have hmul : (δ * (S.card : ℝ)) ^ 2 = δ ^ 2 * (S.card : ℝ) * (S.card : ℝ) := by ring
  rw [hmul] at hchain
  rw [htsum_Φ]
  have hSposR : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hSpos
  have h₂ : (δ ^ 2 * (S.card : ℝ)) * (S.card : ℝ)
      ≤ (∑ x ∈ T, ‖Φ x‖ ^ 2) * (S.card : ℝ) := by
    nlinarith [hchain]
  exact le_of_mul_le_mul_right h₂ hSposR

/-! ## 2. Support of the gauge -/

/-- The `Rest`-product vanishes for a function supported in a *translate* of `symIcc N`: the sign
pattern with a single `1` at the first coordinate isolates the basic shift `y + v 0`. -/
lemma Rest_eq_zero_of_gt {d : ℕ} (hd : 0 < d) (v : Fin d → ℤ) {f : ℤ → ℂ} {N : ℕ} {x₀ : ℤ}
    (hsup : ∀ x : ℤ, (N : ℤ) < |x - x₀| → f x = 0) {y : ℤ}
    (hy : (N : ℤ) + ((v ⟨0, hd⟩).natAbs : ℤ) < |y - x₀|) : Rest v f y = 0 := by
  have hnat : |v ⟨0, hd⟩| = ((v ⟨0, hd⟩).natAbs : ℤ) := (Int.natCast_natAbs _).symm
  have htri : |y - x₀| ≤ |y + v ⟨0, hd⟩ - x₀| + |v ⟨0, hd⟩| := by
    have h := abs_add_le (y + v ⟨0, hd⟩ - x₀) (-(v ⟨0, hd⟩))
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
  have hy' : (N : ℤ) < |y + v ⟨0, hd⟩ - x₀| := by
    rw [hnat] at htri; linarith
  have hf0 : f (y + v ⟨0, hd⟩) = 0 := hsup _ hy'
  rw [Rest]
  refine Finset.prod_eq_zero (i := fun i : Fin d => decide (i = ⟨0, hd⟩)) ?_ ?_
  · rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    intro h
    have h2 : (fun i : Fin d => decide (i = ⟨0, hd⟩)) ⟨0, hd⟩
        = (0 : Fin d → Bool) ⟨0, hd⟩ := by rw [h]
    simp at h2
  · have hsh : cornerShift v (fun _ => 0) (fun i : Fin d => decide (i = ⟨0, hd⟩))
        = v ⟨0, hd⟩ := by
      rw [cornerShift]
      rw [Finset.sum_eq_single ⟨0, hd⟩]
      · simp
      · intro i _ hi
        have : (decide (i = ⟨0, hd⟩) : Bool) = false := by
          simp [hi]
        simp [this]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hsh, hf0]
    exact Function.iterate_fixed (by simp) (weight (fun i : Fin d => decide (i = ⟨0, hd⟩)))

/-! ## 3. The Cauchy–Schwarz step of the node -/

/-- **The Cauchy–Schwarz step** (KKL step 3): the node's hypothesis implies
`δ² |symIcc N| ≤ ∑'_y ‖gauge y‖²`. -/
theorem gaugeBound {I : Type} [Fintype I] [Nonempty I] (s M N : ℕ) (qH : I → ℤ)
    (q₁ q₂ : I → Fin s → ℤ) (δ : ℝ) (f : ℤ → ℂ) (x₀ : ℤ) (hM : 1 ≤ M) (hδ : 0 < δ)
    (hbd : ∀ x : ℤ, ‖f x‖ ≤ 1) (hsup : ∀ x : ℤ, (N : ℤ) < |x - x₀| → f x = 0)
    (h : δ ≤ avg (fun i : I =>
        pbox (s + 1) (Fin.cons (qH i) (q₁ i)) (Fin.cons 0 (q₂ i)) M (symIcc N) f)) :
    δ ^ 2 * ((symIcc N).card : ℝ) ≤ ∑' y : ℤ, ‖gauge s M qH q₁ q₂ f y‖ ^ 2 := by
  -- `f` is finitely supported
  have hfin : FinSuppZ f := ⟨N + x₀.natAbs, fun x hx => by
    refine hsup x ?_
    have h1 : (N : ℤ) + (x₀.natAbs : ℤ) < (x.natAbs : ℤ) := by
      exact_mod_cast (by omega : N + x₀.natAbs < x.natAbs)
    have h2 : ((x.natAbs : ℤ) - (x₀.natAbs : ℤ)) ≤ |x - x₀| := by
      have h3 : |x| ≤ |x - x₀| + |x₀| := by
        have := abs_add_le (x - x₀) x₀
        simpa using this
      have h4 : |x| = (x.natAbs : ℤ) := (Int.natCast_natAbs x).symm
      have h5 : |x₀| = (x₀.natAbs : ℤ) := (Int.natCast_natAbs x₀).symm
      rw [h4, h5] at h3
      linarith
    linarith⟩
  have hg := hyp_gauge s M qH q₁ q₂ N δ f hM hδ hbd hfin h
  -- the support set of `f` and the window containing the support of the gauge
  set S₀ : Finset ℤ := (symIcc N).map (Equiv.addRight x₀).toEmbedding with hS₀
  set Bq : ℕ := ∑ i : I, (qH i).natAbs with hBq
  set K : ℕ := N + 2 * M * Bq with hK
  set T : Finset ℤ := (symIcc K).map (Equiv.addRight x₀).toEmbedding with hT
  have hcardS₀ : S₀.card ≤ (symIcc N).card := by
    rw [hS₀, Finset.card_map]
  have hmemS₀ : ∀ z : ℤ, z ∈ S₀ ↔ z - x₀ ∈ symIcc N := by
    intro z
    rw [hS₀, Finset.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa using ha
    · intro hz
      exact ⟨z - x₀, hz, by simp [Equiv.coe_addRight]⟩
  have hmemT : ∀ z : ℤ, z ∈ T ↔ z - x₀ ∈ symIcc K := by
    intro z
    rw [hT, Finset.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa using ha
    · intro hz
      exact ⟨z - x₀, hz, by simp [Equiv.coe_addRight]⟩
  have hfvan : ∀ x : ℤ, x ∉ S₀ → f x = 0 := by
    intro x hx
    refine hsup x ?_
    have hz : x - x₀ ∉ symIcc N := fun hmem => hx ((hmemS₀ x).mpr hmem)
    have hlt : ¬ ((x - x₀).natAbs ≤ N) := fun hle => hz ((mem_symIcc_iff).mpr hle)
    have h3 : N < (x - x₀).natAbs := by omega
    rw [← Int.natCast_natAbs (x - x₀)]
    exact_mod_cast h3
  have hST : S₀ ⊆ T := by
    intro z hz
    rw [hS₀] at hz
    obtain ⟨a, ha, haz⟩ := Finset.mem_map.mp hz
    rw [hmemT]
    have haz' : z - x₀ = a := by
      have h1 : (Equiv.addRight x₀) a = z := haz
      simp only [Equiv.coe_addRight] at h1
      rw [← h1]; ring
    rw [haz']
    refine (mem_symIcc_iff).mpr ?_
    have ha' : a.natAbs ≤ N := mem_symIcc_iff.mp ha
    rw [hK]
    omega
  have hΦvan : ∀ y : ℤ, y ∉ T → gauge s M qH q₁ q₂ f y = 0 := by
    intro y hy
    have hyK : ((N : ℤ) + 2 * (M : ℤ) * (Bq : ℤ)) < |y - x₀| := by
      have hz : y - x₀ ∉ symIcc K := fun hmem => hy ((hmemT y).mpr hmem)
      have hlt : ¬ ((y - x₀).natAbs ≤ K) := fun hle => hz ((mem_symIcc_iff).mpr hle)
      have h3 : K < (y - x₀).natAbs := by omega
      have h4 : (K : ℤ) < |y - x₀| := by
        rw [← Int.natCast_natAbs (y - x₀)]
        exact_mod_cast h3
      rw [hK] at h4
      push_cast at h4
      exact h4
    have hRest : ∀ (i : I) (H H' : Fin (s + 1) → Fin M × Fin M),
        Rest (incr s M (qH i) (q₁ i) (q₂ i) H H') f y = 0 := by
      intro i H H'
      have hqi : (qH i).natAbs ≤ Bq := by
        rw [hBq]
        exact Finset.single_le_sum (f := fun j : I => (qH j).natAbs)
          (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
      have hb : (incr s M (qH i) (q₁ i) (q₂ i) H H' ⟨0, Nat.succ_pos s⟩).natAbs
          ≤ 2 * M * (qH i).natAbs := incr_zero_natAbs_le s M (qH i) (q₁ i) (q₂ i) H H'
      have hb2 : (incr s M (qH i) (q₁ i) (q₂ i) H H' ⟨0, Nat.succ_pos s⟩).natAbs
          ≤ 2 * M * Bq := le_trans hb (Nat.mul_le_mul_left (2 * M) hqi)
      have hcast : ((incr s M (qH i) (q₁ i) (q₂ i) H H' ⟨0, Nat.succ_pos s⟩).natAbs : ℤ)
          ≤ 2 * (M : ℤ) * (Bq : ℤ) := by
        have h2 : ((2 * M * Bq : ℕ) : ℤ) = 2 * (M : ℤ) * (Bq : ℤ) := by push_cast; ring
        calc ((incr s M (qH i) (q₁ i) (q₂ i) H H' ⟨0, Nat.succ_pos s⟩).natAbs : ℤ)
            ≤ ((2 * M * Bq : ℕ) : ℤ) := by exact_mod_cast hb2
          _ = 2 * (M : ℤ) * (Bq : ℤ) := h2
      refine Rest_eq_zero_of_gt (Nat.succ_pos s)
        (v := incr s M (qH i) (q₁ i) (q₂ i) H H') hsup ?_
      linarith
    have hunf : gauge s M qH q₁ q₂ f y
        = (((M : ℂ) ^ 4)⁻¹) ^ (s + 1) * (((Fintype.card I : ℂ))⁻¹ *
            ∑ i : I, ∑ H : Fin (s + 1) → Fin M × Fin M,
              ∑ H' : Fin (s + 1) → Fin M × Fin M,
                Rest (incr s M (qH i) (q₁ i) (q₂ i) H H') f y) := rfl
    rw [hunf, mul_eq_zero]
    right
    rw [mul_eq_zero]
    right
    refine Finset.sum_eq_zero fun i _ =>
      Finset.sum_eq_zero fun H _ => Finset.sum_eq_zero fun H' _ => hRest i H H'
  have hSpos : 0 < (symIcc N).card := by
    refine Finset.card_pos.mpr ⟨0, ?_⟩
    rw [mem_symIcc_iff]; simp
  exact csFin hfvan hΦvan hST hcardS₀ hbd hδ.le hSpos hg

/-! ## 4. The concatenated slot lists

The two halves of the concatenated box of KKL Lemma 6.1: the slots of the index `i₀` first, then
those of the index `i₁`. -/

/-- The concatenated slot list: the `s` slots of `qL`, then the `s` slots of `qR`
(index type `Fin (2 * s)`). -/
def catQ {s : ℕ} (qL qR : Fin s → ℤ) : Fin (2 * s) → ℤ :=
  fun j => if h : j.val < s then qL ⟨j.val, h⟩ else qR ⟨j.val - s, by omega⟩

/-- The concatenated direction family of the `2s`-fold box. -/
def catDir {s : ℕ} (M : ℕ) (qL₁ qL₂ qR₁ qR₂ : Fin s → ℤ) :
    Fin (2 * s) → (Fin M × Fin M) → ℤ :=
  fun j m => if h : j.val < s then
      pdir (qL₁ ⟨j.val, h⟩) (qL₂ ⟨j.val, h⟩) m
    else pdir (qR₁ ⟨j.val - s, by omega⟩) (qR₂ ⟨j.val - s, by omega⟩) m

/-- `catDir` is the `pdir`-direction family of `catQ`. -/
lemma catDir_eq {s : ℕ} (M : ℕ) (qL₁ qL₂ qR₁ qR₂ : Fin s → ℤ) :
    catDir M qL₁ qL₂ qR₁ qR₂ = fun j => pdir (catQ qL₁ qR₁ j) (catQ qL₂ qR₂ j) := by
  funext j
  unfold catDir catQ
  by_cases h : j.val < s <;> simp [h]

/-- The `mCubeSum` form of the concatenated `pbox`. -/
lemma pbox_catQ (s M : ℕ) (qL₁ qL₂ qR₁ qR₂ : Fin s → ℤ) (S : Finset ℤ) (f : ℤ → ℂ) :
    pbox (2 * s) (catQ qL₁ qR₁) (catQ qL₂ qR₂) M S f
      = ‖mCubeSum (2 * s) (Fin M × Fin M) (catDir M qL₁ qL₂ qR₁ qR₂) S (fun _ => f)‖ := by
  rw [pbox, pboxSum_eq_mCubeSum, catDir_eq]

/-! ## 5. The truncated corner family (KKL's inserted indicators)

In the concatenation identification the *mixed* corners (both halves of the sign pattern nonzero) are
the constant function `1` — it is not finitely supported, so its box power is junk-`0` and the
Gowers–Cauchy–Schwarz inequality cannot be applied directly.  KKL repair this by inserting the
indicator of `supp (B+B-B) - h₀`: on every point where the box product (with the constant `1`) is
nonzero, the mixed corner is evaluated in `B+B-B+dH0`, so replacing `1` by that indicator does not
change the product, while giving the mixed corners a support of cardinality `≤ 3 |symIcc N|`. -/

/-- The indicator of the window `(x₀ + symIcc (3N)) + dH0` (KKL's `1_{B+B-B-h₀}` with
`B = x₀ + symIcc N`). -/
def mixWin (x₀ dH0 : ℤ) (N : ℕ) : Finset ℤ :=
  (Work.Peluse.symIcc (3 * N)).map (Equiv.addRight (x₀ + dH0)).toEmbedding

/-- The corner family of the concatenation identification with the mixed corners truncated. -/
def cUBI (s : ℕ) (f : ℤ → ℂ) (x₀ dH0 dH1 : ℤ) (N : ℕ) (ε ε' : Fin s → Bool) : ℤ → ℂ :=
  if (∀ j : Fin s, ε j = false) ∨ (∀ j : Fin s, ε' j = false) then cUB s f dH0 dH1 ε ε'
  else fun z => if z ∈ mixWin x₀ dH0 N then 1 else 0

/-- The truncated corner family, indexed by the sign pattern of the `2s`-fold box. -/
def cFunI (s : ℕ) (f : ℤ → ℂ) (x₀ dH0 dH1 : ℤ) (N : ℕ) : (Fin (2 * s) → Bool) → ℤ → ℂ :=
  fun ω => cUBI s f x₀ dH0 dH1 N (cL s ω) (cR s ω)

/-- The truncated family agrees with `cFun` at the non-mixed corners. -/
lemma cFunI_eq_cFun {s : ℕ} {f : ℤ → ℂ} {x₀ dH0 dH1 : ℤ} {N : ℕ} {ω : Fin (2 * s) → Bool}
    (h : (∀ j : Fin s, cL s ω j = false) ∨ (∀ j : Fin s, cR s ω j = false)) :
    cFunI s f x₀ dH0 dH1 N ω = cFun s f dH0 dH1 ω := by
  rw [cFunI, cUBI, if_pos h, cFun_eq_cUB]

/-- At a mixed corner the truncated family is the indicator of `mixWin`. -/
lemma cFunI_eq_indicator {s : ℕ} {f : ℤ → ℂ} {x₀ dH0 dH1 : ℤ} {N : ℕ} {ω : Fin (2 * s) → Bool}
    (h : ¬ ((∀ j : Fin s, cL s ω j = false) ∨ (∀ j : Fin s, cR s ω j = false))) :
    cFunI s f x₀ dH0 dH1 N ω
      = fun z => if z ∈ mixWin x₀ dH0 N then (1 : ℂ) else 0 := by
  rw [cFunI, cUBI, if_neg h]

/-- The `ω = 0` corner is the kernel `\bar f(· + dH0) f(· + dH1)`. -/
lemma cFunI_zero {s : ℕ} (f : ℤ → ℂ) (x₀ dH0 dH1 : ℤ) (N : ℕ) :
    cFunI s f x₀ dH0 dH1 N 0 = fun y => star (f (y + dH0)) * f (y + dH1) := by
  have h0 : (∀ j : Fin s, cL s (0 : Fin (2 * s) → Bool) j = false) := fun j => rfl
  have h1 : (∀ j : Fin s, cR s (0 : Fin (2 * s) → Bool) j = false) := fun j => rfl
  rw [cFunI_eq_cFun (ω := 0) (Or.inl h0), cFun_eq_cUB]
  simp only [cUB, h0, h1, and_self]
  rw [if_pos (fun _ => trivial)]

/-! ## 6. The increment tuple of a `Fin.cons`-split shift tuple -/

/-- **The increment tuple of a split shift tuple.**  If `H = Fin.cons (a,c) k` and
`H' = Fin.cons (a',c') k'`, the increment tuple is the *raw* increment
`qH·(a+1) − qH·(a'+1)` followed by the slot differences of the tails.  This is the form in which
`concat_ident` is stated. -/
theorem incr_cons_form (s M : ℕ) (qH : ℤ) (q₁ q₂ : Fin s → ℤ) (a a' c c' : Fin M)
    (k k' : Fin s → Fin M × Fin M) :
    incr s M qH q₁ q₂ (Fin.cons (a, c) k) (Fin.cons (a', c') k')
      = Fin.cons (qH * (((a : ℕ) : ℤ) + 1) - qH * (((a' : ℕ) : ℤ) + 1))
          (fun j => pdir (q₁ j) (q₂ j) (k j) - pdir (q₁ j) (q₂ j) (k' j)) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp only [incr, Fin.cons_zero, pdir]
    ring
  · intro j
    simp only [incr, Fin.cons_succ]

/-- The same for a pair of raw coordinates with the *second* coordinates set to the default
element: the increment tuple is independent of them. -/
theorem incr_cons_form' (s M : ℕ) (hM : 0 < M) (qH : ℤ) (q₁ q₂ : Fin s → ℤ) (a a' : Fin M)
    (k k' : Fin s → Fin M × Fin M) :
    incr s M qH q₁ q₂ (Fin.cons (a, ⟨0, hM⟩) k) (Fin.cons (a', ⟨0, hM⟩) k')
      = Fin.cons (qH * (((a : ℕ) : ℤ) + 1) - qH * (((a' : ℕ) : ℤ) + 1))
          (fun j => pdir (q₁ j) (q₂ j) (k j) - pdir (q₁ j) (q₂ j) (k' j)) :=
  incr_cons_form s M qH q₁ q₂ a a' ⟨0, hM⟩ ⟨0, hM⟩ k k'

end

end Work.Peluse.SwapC
