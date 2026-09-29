import Mathlib
import Submission.Work.Holonomy3.defs
import Submission.Work.Holonomy3.balanced_indices
import Submission.CDT.DiscrepancyFour

/-!
# The linear system of the box principle (Siegel's lemma) for the fine holonomy bound

Definitions of the linear system used to prove `Work.Holonomy3.siegel` (the paper's Lemma
`Siegel`, the Thue--Siegel box principle step of §"The box principle step"):

* `balSet d m` — the set `V_m^d` of balanced species vectors (each `i : Fin m` occurs `d/m` times);
* `lowSet d D ε` — the `ε`-low discrepancy exponent vectors with all coordinates `≤ D`
  (the paper's set `k/D ∈ P_ε^d ∩ ℤ^d` of the template `(F construction)`);
* `rowSet d D ε δ m` — the exponent vectors whose Taylor coefficient of the auxiliary series is
  forced to vanish: the box `[0,(m-δ)D]^d` and the high-discrepancy part of `[0,(m+δ)D]^d`;
* `ColIdx`, `RowIdx` — the column and row index types of the linear system;
* `DenData`, `Dn`, `num`, `clearFac`, `rowFac`, `cFac`, `matEntry` — the denominator-clearing
  data and the integer matrix of the system, with `matEntry_spec`;
* `mkQ` — the auxiliary template `Q` built from an integer vector `y`;
* `sysCoeff` — the scalar coefficient `∏_s [x_s^{n_s-k_s}] f_{i_s}` of the template.
-/

namespace Work.Holonomy3

open Submission.CDTPlan Submission.CDT.Discrepancy
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {m r d : ℕ} {D : ℕ} {ε δ : ℝ}

/-! ## The index sets of the linear system -/

/-- The set `V_m^d` of balanced species vectors: each `i : Fin m` occurs exactly `d/m` times.
(The predicate is written out rather than as `Balanced` so that the definition is syntactically
equal to the one appearing in `Work.Holonomy3.balanced_indices`.) -/
def balSet (d m : ℕ) : Finset (Fin d → Fin m) :=
  Finset.univ.filter (fun i : Fin d → Fin m =>
    ∀ s : Fin m, (Finset.univ.filter (fun j : Fin d => i j = s)).card = d / m)

/-- The exponent vectors `k` with `k j ≤ D` whose normalised components `k/D` have box discrepancy
`< ε`: the paper's `k/D ∈ P_ε^d ∩ Z^d`. -/
noncomputable def lowSet (d D : ℕ) (ε : ℝ) : Finset (Fin d → ℕ) :=
  (Fintype.piFinset (fun _ : Fin d => Finset.range (D + 1))).filter
    (fun k : Fin d → ℕ => disc (fun j => (k j : ℝ) / (D : ℝ)) < ε)

/-- The exponent vectors whose Taylor coefficient of the auxiliary series must vanish:
`n ∈ [0,(m-δ)D]^d`, or `n ∈ [0,(m+δ)D]^d` with `n/((m+δ)D) ∉ P_ε^d`. -/
noncomputable def rowSet (d D : ℕ) (ε δ : ℝ) (m : ℕ) : Finset (Fin d → ℕ) :=
  (Fintype.piFinset (fun _ : Fin d => Finset.range (Nat.ceil ((m + δ) * D) + 1))).filter
    (fun n : Fin d → ℕ => (∀ j, (n j : ℝ) ≤ (m - δ) * D) ∨
      ((∀ j, (n j : ℝ) ≤ (m + δ) * D) ∧ ε ≤ disc (fun j => (n j : ℝ) / ((m + δ) * D))))

/-- The columns of the linear system: `(i,k)` with `i ∈ V_m^d` and `k ∈ P_ε^d ∩ [0,D]^d`. -/
abbrev ColIdx (d D : ℕ) (ε : ℝ) (m : ℕ) : Type :=
  {p : (Fin d → Fin m) × (Fin d → ℕ) // p.1 ∈ balSet d m ∧ p.2 ∈ lowSet d D ε}

/-- The rows of the linear system. -/
abbrev RowIdx (d D : ℕ) (ε δ : ℝ) (m : ℕ) : Type := {n : Fin d → ℕ // n ∈ rowSet d D ε δ m}

noncomputable instance colIdxFintype (d D : ℕ) (ε : ℝ) (m : ℕ) : Fintype (ColIdx d D ε m) :=
  Set.Finite.fintype ((Finset.finite_toSet ((balSet d m).product (lowSet d D ε))).subset (by
    intro p hp
    exact Finset.mem_product.mpr hp))

noncomputable instance rowIdxFintype (d D : ℕ) (ε δ : ℝ) (m : ℕ) : Fintype (RowIdx d D ε δ m) :=
  Set.Finite.fintype ((Finset.finite_toSet (rowSet d D ε δ m)).subset (by
    intro p hp
    exact hp))

/-! ## Two elementary facts on `lcmUpto` -/

lemma lcmUpto_ne_zero' (N : ℕ) : lcmUpto N ≠ 0 := Nat.lcmUpto_ne_zero N

lemma lcmUpto_dvd' {M N : ℕ} (h : M ≤ N) : lcmUpto M ∣ lcmUpto N := by
  unfold Submission.CDTPlan.lcmUpto
  exact Finset.lcm_mono (fun a ha => by simp only [Finset.mem_Icc] at ha ⊢; omega)

lemma dvd_lcmUpto' {n N : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ N) : n ∣ lcmUpto N := by
  unfold Submission.CDTPlan.lcmUpto
  exact Finset.dvd_lcm (f := id) (by simp only [Finset.mem_Icc]; exact ⟨h1, h2⟩)

/-! ## The denominator-clearing data -/

/-- The constants extracted from the denominator types of the species `f_i`: a common numerator
`Kmax` and exponent `Emax` and shift `cmax`, a common lcm array `bmax`, and a common denominator
`Nc` of the constant coefficients. -/
structure DenData {m r : ℕ} (b : Fin m → Fin r → ℕ) (e : Fin m → ℕ) (f : Fin m → PowerSeries ℚ)
    (hden : ∀ i : Fin m, HasDenomType (e i) (b i) (f i)) where
  Kmax : ℕ
  Emax : ℕ
  cmax : ℕ
  bmax : Fin r → ℕ
  Nc : ℕ
  hKmax : 1 ≤ Kmax
  hNc : 1 ≤ Nc
  Kc_dvd : ∀ i, (hden i).choose ∣ Kmax
  e_le : ∀ i, e i ≤ Emax
  cc_le : ∀ i, (hden i).choose_spec.choose ≤ cmax
  b_le : ∀ i j, b i j ≤ bmax j
  den_dvd : ∀ i, (PowerSeries.coeff 0 (f i)).den ∣ Nc

variable {b : Fin m → Fin r → ℕ} {e : Fin m → ℕ} {f : Fin m → PowerSeries ℚ}
  {hden : ∀ i : Fin m, HasDenomType (e i) (b i) (f i)}

/-- The canonical clearing data of a family with denominator types. -/
noncomputable def denData (hd : ∀ i : Fin m, HasDenomType (e i) (b i) (f i)) :
    DenData b e f hd where
  Kmax := max 1 (∏ i : Fin m, (hd i).choose)
  Emax := Finset.univ.sup (fun i : Fin m => e i)
  cmax := max 1 (Finset.univ.sup (fun i : Fin m => (hd i).choose_spec.choose))
  bmax := fun j => max 1 (Finset.univ.sup (fun i : Fin m => b i j))
  Nc := max 1 (∏ i : Fin m, (PowerSeries.coeff 0 (f i)).den)
  hKmax := le_max_left _ _
  hNc := le_max_left _ _
  Kc_dvd := fun i => by
    have h1 : (hd i).choose ∣ ∏ i : Fin m, (hd i).choose :=
      Finset.dvd_prod_of_mem (fun i : Fin m => (hd i).choose) (Finset.mem_univ i)
    have hpos : 0 < ∏ i : Fin m, (hd i).choose :=
      Finset.prod_pos (fun i _ => (hd i).choose_spec.choose_spec.1)
    rw [max_eq_right (by omega)]
    exact h1
  e_le := fun i => Finset.le_sup (f := fun i : Fin m => e i) (Finset.mem_univ i)
  cc_le := fun i => le_trans (Finset.le_sup
    (f := fun i : Fin m => (hd i).choose_spec.choose) (Finset.mem_univ i)) (le_max_right _ _)
  b_le := fun i j => le_trans (Finset.le_sup (f := fun i : Fin m => b i j) (Finset.mem_univ i))
    (le_max_right _ _)
  den_dvd := fun i => by
    rw [max_eq_right]
    · exact Finset.dvd_prod_of_mem (fun i : Fin m => (PowerSeries.coeff 0 (f i)).den)
        (Finset.mem_univ i)
    · have hpos : 0 < ∏ i : Fin m, (PowerSeries.coeff 0 (f i)).den :=
        Finset.prod_pos (fun i _ => (PowerSeries.coeff 0 (f i)).den_pos)
      omega

/-- The denominator of the `n`-th coefficient of species `i` (the constant coefficient is handled
through the field `Nc`). -/
noncomputable def Dn (C : DenData b e f hden) (i : Fin m) (n : ℕ) : ℕ :=
  if n = 0 then (PowerSeries.coeff 0 (f i)).den
  else (hden i).choose * n ^ (e i) * ∏ j, lcmUpto (b i j * n + (hden i).choose_spec.choose)

lemma Dn_pos (C : DenData b e f hden) (i : Fin m) (n : ℕ) : 0 < Dn C i n := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [Dn, if_pos rfl]; exact (PowerSeries.coeff 0 (f i)).den_pos
  · rw [Dn, if_neg hn]
    have h1 : 0 < (hden i).choose := (hden i).choose_spec.choose_spec.1
    have h2 : 0 < n ^ (e i) := pow_pos (Nat.pos_of_ne_zero hn) _
    have h3 : 0 < ∏ j, lcmUpto (b i j * n + (hden i).choose_spec.choose) :=
      Finset.prod_pos (fun j _ => Nat.lcmUpto_pos _)
    positivity

/-- The numerator of the `n`-th coefficient of species `i`, made explicit. -/
noncomputable def num (C : DenData b e f hden) (i : Fin m) (n : ℕ) : ℤ :=
  if h : n = 0 then (PowerSeries.coeff 0 (f i)).num
  else ((hden i).choose_spec.choose_spec.2 n (Nat.pos_of_ne_zero h)).choose

lemma num_spec (C : DenData b e f hden) (i : Fin m) (n : ℕ) :
    (num C i n : ℚ) = (Dn C i n : ℚ) * PowerSeries.coeff n (f i) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [num, Dn, dif_pos rfl, if_pos rfl]
    have h := Rat.num_div_den (PowerSeries.coeff 0 (f i))
    field_simp at h ⊢
    linarith [h]
  · rw [num, Dn, dif_neg hn, if_neg hn]
    have h := ((hden i).choose_spec.choose_spec.2 n (Nat.pos_of_ne_zero hn)).choose_spec
    rw [← h]
    push_cast
    ring

/-- The clearing factor attached to a single coordinate bounded by `N`. -/
noncomputable def clearFac (C : DenData b e f hden) (N : ℕ) : ℕ :=
  C.Kmax * (lcmUpto N) ^ C.Emax * ∏ j, lcmUpto (C.bmax j * N + C.cmax)

/-- The row multiplier of the row indexed by `n`. -/
noncomputable def rowFac (C : DenData b e f hden) (n : Fin d → ℕ) : ℕ :=
  ∏ s : Fin d, (C.Nc * clearFac C (n s))

lemma Dn_dvd (C : DenData b e f hden) (i : Fin m) {n N : ℕ} (hn : n ≤ N) :
    Dn C i n ∣ C.Nc * clearFac C N := by
  rcases eq_or_ne n 0 with rfl | hn0
  · rw [Dn, if_pos rfl]
    exact dvd_mul_of_dvd_left (C.den_dvd i) _
  · rw [Dn, if_neg hn0]
    have hK : (hden i).choose ∣ C.Kmax := C.Kc_dvd i
    have hpow : n ^ (e i) ∣ (lcmUpto N) ^ C.Emax := by
      have h1 : n ∣ lcmUpto N := dvd_lcmUpto' (Nat.pos_of_ne_zero hn0) hn
      exact dvd_trans (pow_dvd_pow_of_dvd h1 _) (pow_dvd_pow _ (C.e_le i))
    have hlcm : ∀ j : Fin r, lcmUpto (b i j * n + (hden i).choose_spec.choose) ∣
        lcmUpto (C.bmax j * N + C.cmax) := by
      intro j
      refine lcmUpto_dvd' ?_
      have h1 : b i j * n ≤ C.bmax j * N := Nat.mul_le_mul (C.b_le i j) hn
      have h2 : (hden i).choose_spec.choose ≤ C.cmax := C.cc_le i
      omega
    have hprod : (∏ j : Fin r, lcmUpto (b i j * n + (hden i).choose_spec.choose)) ∣
        (∏ j : Fin r, lcmUpto (C.bmax j * N + C.cmax)) :=
      Finset.prod_dvd_prod_of_dvd _ _ (fun j _ => hlcm j)
    refine dvd_mul_of_dvd_right ?_ C.Nc
    rw [clearFac]
    exact Nat.mul_dvd_mul (Nat.mul_dvd_mul hK hpow) hprod

/-- The cleared coefficient of the `n`-th coefficient of species `i`. -/
noncomputable def cFac (C : DenData b e f hden) (i : Fin m) (N n : ℕ) : ℤ :=
  num C i n * ((C.Nc * clearFac C N / Dn C i n : ℕ) : ℤ)

lemma cFac_spec (C : DenData b e f hden) (i : Fin m) {N n : ℕ} (hn : n ≤ N) :
    (cFac C i N n : ℚ) = (C.Nc * clearFac C N : ℚ) * PowerSeries.coeff n (f i) := by
  have hdvd := Dn_dvd C i hn
  have hpos := Dn_pos C i n
  have h1 : (cFac C i N n : ℚ) = (num C i n : ℚ) *
      ((C.Nc * clearFac C N / Dn C i n : ℕ) : ℚ) := by
    rw [cFac, Int.cast_mul, Int.cast_natCast]
  rw [h1, Nat.cast_div hdvd (by exact_mod_cast hpos.ne'), num_spec C i n, Nat.cast_mul]
  have hD : (Dn C i n : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
  field_simp

/-- The integer matrix of the linear system: the row multiplier times the coefficient
`∏_s [x_s^{n_s-k_s}] f_{i_s}`. -/
noncomputable def matEntry (C : DenData b e f hden) (n : Fin d → ℕ)
    (p : (Fin d → Fin m) × (Fin d → ℕ)) : ℤ :=
  ∏ s : Fin d, if p.2 s ≤ n s then cFac C (p.1 s) (n s) (n s - p.2 s) else 0

lemma matEntry_spec (C : DenData b e f hden) (n : Fin d → ℕ)
    (p : (Fin d → Fin m) × (Fin d → ℕ)) :
    (matEntry C n p : ℚ) = (rowFac C n : ℚ) *
      ∏ s : Fin d, (if p.2 s ≤ n s then PowerSeries.coeff (n s - p.2 s) (f (p.1 s)) else 0) := by
  simp only [matEntry, rowFac]
  rw [Int.cast_prod, Nat.cast_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun s _ => ?_)
  by_cases h : p.2 s ≤ n s
  · rw [if_pos h, if_pos h, cFac_spec C (p.1 s) (Nat.sub_le (n s) (p.2 s)), Nat.cast_mul]
  · rw [if_neg h, if_neg h]
    simp

/-- The scalar coefficient of the template at the exponent `n` (given as a function), for the
column `(i,k)`: `∏_s [x_s^{n_s-k_s}] f_{i_s}`. -/
noncomputable def sysCoeffFun (f : Fin m → PowerSeries ℚ) (n : Fin d → ℕ)
    (p : (Fin d → Fin m) × (Fin d → ℕ)) : ℚ :=
  ∏ s : Fin d, (if p.2 s ≤ n s then PowerSeries.coeff (n s - p.2 s) (f (p.1 s)) else 0)

/-- The scalar coefficient of the template at the multi-index `n`, for the column `(i,k)`. -/
noncomputable def sysCoeff (f : Fin m → PowerSeries ℚ) (n : Fin d →₀ ℕ)
    (p : (Fin d → Fin m) × (Fin d → ℕ)) : ℚ :=
  sysCoeffFun f (fun s => n s) p

/-! ## The auxiliary template attached to a vector `y` -/

/-- The auxiliary template `Q` attached to an integer vector `y` of the linear system: the
coefficient of the monomial `x^k` in `Q i` is `y (i,k)`, for `i ∈ V_m^d` and `k ∈ P_ε^d ∩ [0,D]^d`,
and `Q i = 0` for `i ∉ V_m^d`. -/
noncomputable def mkQ (y : ColIdx d D ε m → ℤ) : (Fin d → Fin m) → MvPolynomial (Fin d) ℚ :=
  fun i => if hi : i ∈ balSet d m then
      ∑ k ∈ (lowSet d D ε).attach,
        (y ⟨(i, k.1), hi, k.2⟩ : ℚ) • MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm k.1) 1
    else 0

lemma coeff_mkQ_zero (y : ColIdx d D ε m → ℤ) {i : Fin d → Fin m} (hi : i ∉ balSet d m)
    (k : Fin d →₀ ℕ) : (mkQ y i).coeff k = 0 := by
  rw [mkQ, dif_neg hi]
  simp

lemma coeff_mkQ (y : ColIdx d D ε m → ℤ) {i : Fin d → Fin m} (hi : i ∈ balSet d m)
    (k : Fin d →₀ ℕ) :
    (mkQ y i).coeff k =
      (if hk : Finsupp.equivFunOnFinite k ∈ lowSet d D ε then
        (y ⟨(i, Finsupp.equivFunOnFinite k), hi, hk⟩ : ℚ) else 0) := by
  classical
  rw [mkQ, dif_pos hi, MvPolynomial.coeff_sum]
  have key : ∀ x ∈ (lowSet d D ε).attach,
      ((y ⟨(i, x.1), hi, x.2⟩ : ℚ) •
          MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm x.1) 1).coeff k
        = if x.1 = Finsupp.equivFunOnFinite k then (y ⟨(i, x.1), hi, x.2⟩ : ℚ) else 0 := by
    intro x _
    rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial]
    by_cases h : x.1 = Finsupp.equivFunOnFinite k
    · rw [if_pos (by rw [h, Finsupp.equivFunOnFinite.symm_apply_apply]), if_pos h, smul_eq_mul,
        mul_one]
    · rw [if_neg (fun hc => h (by rw [← hc, Finsupp.equivFunOnFinite.apply_symm_apply])),
        if_neg h, smul_zero]
  rw [Finset.sum_congr rfl key]
  by_cases hk : Finsupp.equivFunOnFinite k ∈ lowSet d D ε
  · rw [dif_pos hk]
    refine (Finset.sum_eq_single ⟨Finsupp.equivFunOnFinite k, hk⟩ ?_ ?_).trans ?_
    · intro x _ hx
      rw [if_neg (fun hc => hx (Subtype.ext hc))]
    · intro h
      exact absurd (Finset.mem_attach _ _) h
    · rw [if_pos rfl]
  · rw [dif_neg hk]
    exact Finset.sum_eq_zero (fun x _ => by
      rw [if_neg (fun hc => hk (by rw [← hc]; exact x.2))])

lemma supported_mkQ (y : ColIdx d D ε m → ℤ) (i : Fin d → Fin m) :
    ∀ k ∈ (mkQ y i).support, Finsupp.equivFunOnFinite k ∈ lowSet d D ε := by
  classical
  intro k hk
  rw [MvPolynomial.mem_support_iff] at hk
  by_cases hi : i ∈ balSet d m
  · rw [coeff_mkQ y hi] at hk
    by_contra h
    exact hk (dif_neg h)
  · exact absurd (coeff_mkQ_zero y hi k) hk

lemma balanced_mkQ (y : ColIdx d D ε m → ℤ) {i : Fin d → Fin m} (hi : mkQ y i ≠ 0) :
    Balanced i := by
  classical
  by_contra h
  have hpos : ¬ (i ∈ balSet d m) := by
    intro hc
    simp only [balSet, Finset.mem_filter, Finset.mem_univ, true_and, Balanced] at hc
    exact h hc
  exact hi (by rw [mkQ, dif_neg hpos])

/-! ## Counting the columns and rows of the linear system -/

lemma card_colIdx (d D : ℕ) (ε : ℝ) (m : ℕ) :
    Fintype.card (ColIdx d D ε m) = (balSet d m).card * (lowSet d D ε).card := by
  have h1 : Fintype.card (ColIdx d D ε m)
      = Fintype.card (↥(balSet d m) × ↥(lowSet d D ε)) :=
    Fintype.card_congr
      { toFun := fun p => (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
        invFun := fun q => ⟨(q.1.1, q.2.1), q.1.2, q.2.2⟩
        left_inv := fun p => rfl
        right_inv := fun q => rfl }
  rw [h1, Fintype.card_prod, Fintype.card_coe, Fintype.card_coe]

lemma card_rowIdx (d D : ℕ) (ε δ : ℝ) (m : ℕ) :
    Fintype.card (RowIdx d D ε δ m) = (rowSet d D ε δ m).card :=
  Fintype.card_coe _

/-- The `(i,k)` of the box-principle system: the low-discrepancy exponent vectors with all
coordinates `≤ D`. -/
lemma mem_lowSet {k : Fin d → ℕ} :
    k ∈ lowSet d D ε ↔ (∀ j, k j ≤ D) ∧ disc (fun j => (k j : ℝ) / (D : ℝ)) < ε := by
  rw [lowSet, Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨h, hε⟩
    exact ⟨fun j => Nat.lt_succ_iff.mp (Finset.mem_range.mp (h j)), hε⟩
  · rintro ⟨h, hε⟩
    exact ⟨fun j => Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (h j)), hε⟩

lemma balSet_eq (d m : ℕ) : balSet d m =
    Finset.univ.filter (fun i : Fin d → Fin m =>
      ∀ s : Fin m, (Finset.univ.filter (fun j : Fin d => i j = s)).card = d / m) := rfl

lemma mem_balSet {i : Fin d → Fin m} : i ∈ balSet d m ↔ Balanced i := by
  simp only [balSet, Finset.mem_filter, Finset.mem_univ, true_and, Balanced]

/-- The vanishing conditions of the box principle: the box `[0,(m-δ)D]^d` and the
high-discrepancy part of `[0,(m+δ)D]^d`. -/
lemma mem_rowSet {n : Fin d → ℕ} :
    n ∈ rowSet d D ε δ m ↔
      (∀ j, n j ≤ Nat.ceil ((m + δ) * D)) ∧
      ((∀ j, (n j : ℝ) ≤ (m - δ) * D) ∨
        ((∀ j, (n j : ℝ) ≤ (m + δ) * D) ∧
          ε ≤ disc (fun j => (n j : ℝ) / ((m + δ) * D)))) := by
  rw [rowSet, Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨h, hε⟩
    exact ⟨fun j => Nat.lt_succ_iff.mp (Finset.mem_range.mp (h j)), hε⟩
  · rintro ⟨h, hε⟩
    exact ⟨fun j => Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (h j)), hε⟩

/-- The high-discrepancy rows (the second family of vanishing conditions), as a `Finset`. -/
noncomputable def badSet (d D : ℕ) (ε δ : ℝ) (m : ℕ) : Finset (Fin d → ℕ) :=
  (Fintype.piFinset (fun _ : Fin d => Finset.range (Nat.ceil ((m + δ) * D) + 1))).filter
    (fun n : Fin d → ℕ => (∀ j, (n j : ℝ) ≤ (m + δ) * D) ∧
      ε ≤ disc (fun j => (n j : ℝ) / ((m + δ) * D)))

/-- The rows of the system are contained in the union of the box `[0,(m-δ)D]^d` and the
high-discrepancy part of `[0,(m+δ)D]^d`. -/
lemma rowSet_subset_badSet_union (hδm : δ ≤ m) :
    rowSet d D ε δ m ⊆
      (Fintype.piFinset (fun _ : Fin d => Finset.range (Nat.floor ((m - δ) * D) + 1))) ∪
      (badSet d D ε δ m) := by
  intro n hn
  rw [mem_rowSet] at hn
  rw [Finset.mem_union]
  obtain ⟨hbase, hcond⟩ := hn
  rcases hcond with h1 | h2
  · left
    rw [Fintype.mem_piFinset]
    intro j
    rw [Finset.mem_range]
    have hle : n j ≤ Nat.floor ((m - δ) * D) := Nat.le_floor (h1 j)
    omega
  · right
    rw [badSet, Finset.mem_filter]
    refine ⟨?_, h2⟩
    rw [Fintype.mem_piFinset]
    exact fun j => Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (hbase j))

lemma card_rowSet_le (hδm : δ ≤ m) :
    (rowSet d D ε δ m).card ≤
      (Nat.floor ((m - δ) * D) + 1) ^ d + (badSet d D ε δ m).card := by
  refine le_trans (Finset.card_le_card (rowSet_subset_badSet_union hδm)) ?_
  refine le_trans (Finset.card_union_le _ _) ?_
  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_range]
  have h : (Finset.univ : Finset (Fin d)).card = d := Fintype.card_fin d
  rw [h]


end Work.Holonomy3
