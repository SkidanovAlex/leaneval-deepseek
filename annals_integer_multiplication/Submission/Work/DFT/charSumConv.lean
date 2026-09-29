import Mathlib
import Submission.Work.DFT.dftDefs
import Submission.Work.DFT.digitsBij
import Submission.Work.DFT.subDigitsFacts
import Submission.Work.DFT.charSumGen

/-!
# The orthogonality relation for the multidimensional DFT (paper §2.4)

The character sums appearing when composing multidimensional DFTs: for positive `ts`, the sum over
the full flat index box of `charExp ts c k = exp(2πi · Σᵢ cᵢ kᵢ / tᵢ)` is `ts.prod` when every
coordinate `cᵢ` is divisible by `tᵢ` and `0` otherwise (`charSumGen`).  Specialising to the
triple-difference coefficient list `(digits j) - (digits a) - (digits b)` identifies the flat index
`b` with `subIdx ts j a`, which is the fact `HvdH.convC` needs.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.DFT

/-- `getD` of `subN` at an index inside both lists. -/
lemma charSumConv_subN_getD : ∀ (X Y : List ℕ) (i : ℕ), i < X.length → i < Y.length →
    (subN X Y).getD i 0 = (X.getD i 0 : ℤ) - (Y.getD i 0 : ℤ)
  | [], _, i, hX, _ => by simp at hX
  | _::_, [], i, _, hY => by simp at hY
  | _::_, _::_, 0, _, _ => by simp [subN]
  | _::xs, _::ys, i+1, hX, hY => by
      simp only [subN_cons, List.getD_cons_succ]
      exact charSumConv_subN_getD xs ys i (by simpa using hX) (by simpa using hY)

/-- `getD` of `subNZ` at an index inside both lists. -/
lemma charSumConv_subNZ_getD : ∀ (C : List ℤ) (Y : List ℕ) (i : ℕ), i < C.length → i < Y.length →
    (subNZ C Y).getD i 0 = C.getD i 0 - (Y.getD i 0 : ℤ)
  | [], _, i, hC, _ => by simp at hC
  | _::_, [], i, _, hY => by simp at hY
  | _::_, _::_, 0, _, _ => by simp [subNZ]
  | _::cs, _::ys, i+1, hC, hY => by
      simp only [subNZ_cons, List.getD_cons_succ]
      exact charSumConv_subNZ_getD cs ys i (by simpa using hC) (by simpa using hY)

/-- The `i`-th entry of the triple difference `(X - Y) - Z`. -/
lemma charSumConv_subNZ_subN_getD (X Y Z : List ℕ) (i : ℕ) (hX : i < X.length) (hY : i < Y.length)
    (hZ : i < Z.length) :
    (subNZ (subN X Y) Z).getD i 0 = (X.getD i 0 : ℤ) - (Y.getD i 0 : ℤ) - (Z.getD i 0 : ℤ) := by
  have hlen : i < (subN X Y).length := by simp [subN]; omega
  rw [charSumConv_subNZ_getD (subN X Y) Z i hlen hZ, charSumConv_subN_getD X Y i hX hY]

/-- Two natural lists of the same length are equal iff they agree in `getD` at every index. -/
lemma charSumConv_list_eq_iff_getD {l₁ l₂ : List ℕ} {n : ℕ} (h₁ : l₁.length = n)
    (h₂ : l₂.length = n) : (∀ i < n, l₁.getD i 0 = l₂.getD i 0) ↔ l₁ = l₂ := by
  constructor
  · intro h
    refine List.ext_getElem (by omega) (fun i hi1 hi2 => ?_)
    have := h i (by omega)
    rwa [List.getD_eq_getElem _ _ hi1, List.getD_eq_getElem _ _ hi2] at this
  · intro h i hi; rw [h]

/-- Divisibility by a positive `t` of `x - y - z` (with `x,y,z ∈ [0,t)`) says that `z` is the
residue of `x - y`. -/
lemma charSumConv_dvd_iff_mod_eq (t x y z : ℕ) (_ht : 0 < t) (_hx : x < t) (hy : y < t)
    (hz : z < t) : ((t : ℤ) ∣ (x : ℤ) - y - z) ↔ z = (x + t - y) % t := by
  have hty : ((x + t - y : ℕ) : ℤ) = (x : ℤ) + t - y := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [show (x : ℤ) - y - z = ((x + t - y : ℕ) : ℤ) - z - t by rw [hty]; ring]
  have key : (↑t : ℤ) ∣ ((x + t - y : ℕ) : ℤ) - ↑z - ↑t ↔
      (↑t : ℤ) ∣ ((x + t - y : ℕ) : ℤ) - ↑z := by
    constructor
    · intro h
      have : ((x + t - y : ℕ) : ℤ) - ↑z = (((x + t - y : ℕ) : ℤ) - ↑z - ↑t) + ↑t := by ring
      rw [this]; exact Int.dvd_add h (dvd_refl _)
    · intro h; exact Int.dvd_sub h (dvd_refl _)
  rw [key, ← Nat.modEq_iff_dvd, Nat.ModEq, Nat.mod_eq_of_lt hz]

/-- The divisibility condition of `charSumGen` for the coefficient list
`(digits j) - (digits a) - (digits b)` holds iff `b` is the flat index of `j - a`. -/
lemma charSumConv_cond_iff_subIdx (ts : List ℕ) (hpos : ∀ t ∈ ts, 0 < t) (j a b : Fin ts.prod) :
    (∀ i < ts.length, (ts.getD i 0 : ℤ) ∣
        (subNZ (subN (HvdH.digits ts j) (HvdH.digits ts a)) (HvdH.digits ts b)).getD i 0) ↔
      (b : ℕ) = HvdH.subIdx ts (j : ℕ) (a : ℕ) := by
  obtain ⟨hdig1, hdig2, hdig3, hdig4⟩ := digitsBij ts hpos
  set X := HvdH.digits ts (j : ℕ) with hX
  set Y := HvdH.digits ts (a : ℕ) with hY
  set Z := HvdH.digits ts (b : ℕ) with hZ
  have hXlen : X.length = ts.length := by rw [hX]; exact hdig3 (j:ℕ)
  have hYlen : Y.length = ts.length := by rw [hY]; exact hdig3 (a:ℕ)
  have hZlen : Z.length = ts.length := by rw [hZ]; exact hdig3 (b:ℕ)
  have hXlt : ∀ i < ts.length, X.getD i 0 < ts.getD i 0 :=
    fun i hi => by rw [hX]; exact hdig2 (j:ℕ) j.isLt i hi
  have hYlt : ∀ i < ts.length, Y.getD i 0 < ts.getD i 0 :=
    fun i hi => by rw [hY]; exact hdig2 (a:ℕ) a.isLt i hi
  have hZlt : ∀ i < ts.length, Z.getD i 0 < ts.getD i 0 :=
    fun i hi => by rw [hZ]; exact hdig2 (b:ℕ) b.isLt i hi
  obtain ⟨hDlen, hDlt, hDget⟩ := subDigitsFacts ts X Y hpos hXlen hYlen
  have hper : ∀ i, i < ts.length →
      ((ts.getD i 0 : ℤ) ∣ (subNZ (subN X Y) Z).getD i 0 ↔
        Z.getD i 0 = (HvdH.subDigits ts X Y).getD i 0) := by
    intro i hi
    have hts : 0 < ts.getD i 0 :=
      hpos _ (by rw [List.getD_eq_getElem ts 0 hi]; exact List.getElem_mem hi)
    rw [charSumConv_subNZ_subN_getD X Y Z i (by omega) (by omega) (by omega),
        charSumConv_dvd_iff_mod_eq (ts.getD i 0) (X.getD i 0) (Y.getD i 0) (Z.getD i 0)
          hts (hXlt i hi) (hYlt i hi) (hZlt i hi), hDget i hi]
  have hstep1 : (∀ i, i < ts.length → (ts.getD i 0 : ℤ) ∣ (subNZ (subN X Y) Z).getD i 0) ↔
      (∀ i, i < ts.length → Z.getD i 0 = (HvdH.subDigits ts X Y).getD i 0) := by
    constructor
    · intro h i hi; exact (hper i hi).mp (h i hi)
    · intro h i hi; exact (hper i hi).mpr (h i hi)
  have hstep2 : (∀ i, i < ts.length → Z.getD i 0 = (HvdH.subDigits ts X Y).getD i 0) ↔
      Z = HvdH.subDigits ts X Y := charSumConv_list_eq_iff_getD hZlen hDlen
  have hsubIdx_eq : HvdH.subIdx ts (j:ℕ) (a:ℕ) = HvdH.undigits ts (HvdH.subDigits ts X Y) := by
    simp only [HvdH.subIdx]
    rw [← hX, ← hY]
  have hstep3 : Z = HvdH.subDigits ts X Y ↔ (b:ℕ) = HvdH.subIdx ts (j:ℕ) (a:ℕ) := by
    constructor
    · intro hZD
      have h1 : (b:ℕ) = HvdH.undigits ts Z := by rw [← hdig1 (b:ℕ) b.isLt, hZ]
      rw [h1, hZD, ← hsubIdx_eq]
    · intro hb
      have hb' : (b:ℕ) = HvdH.undigits ts (HvdH.subDigits ts X Y) := by rw [hb, hsubIdx_eq]
      have hZ' : Z = HvdH.digits ts (HvdH.undigits ts (HvdH.subDigits ts X Y)) := by rw [hZ, hb']
      rw [hZ', (hdig4 (HvdH.subDigits ts X Y) hDlen hDlt).1]
  exact hstep1.trans (hstep2.trans hstep3)

theorem charSumConv (ts : List ℕ) (hpos : ∀ t ∈ ts, 0 < t) (j a b : Fin ts.prod) :
    (∑ k : Fin ts.prod,
        charExp ts (subNZ (subN (HvdH.digits ts j) (HvdH.digits ts a)) (HvdH.digits ts b)) k) =
      if b = HvdH.subIdx ts j a then (ts.prod : ℂ) else 0 := by
  have hClen : (subNZ (subN (HvdH.digits ts (j:ℕ)) (HvdH.digits ts (a:ℕ)))
      (HvdH.digits ts (b:ℕ))).length = ts.length := by
    simp [subNZ, subN, digits_length]
  rw [charSumGen ts hpos (subNZ (subN (HvdH.digits ts (j:ℕ)) (HvdH.digits ts (a:ℕ)))
        (HvdH.digits ts (b:ℕ))) hClen]
  exact if_congr (charSumConv_cond_iff_subIdx ts hpos j a b) rfl rfl

end Work.DFT
