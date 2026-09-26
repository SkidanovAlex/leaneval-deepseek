import Mathlib
import Submission.Work.SGsep.hand.HandDefs2

namespace Work.SGsep.hand

open scoped Matrix
open Work.SG Work.SG.Data Work.SGsep.Hand Work.SGsep.Hand.Data

/-! ## Bézout for `V3` -/

/-- The gcd of the entries of a `V3` divides every entry. -/
theorem gcdV_dvd_coord (u : V3) :
    (V3.gcdV u : ℤ) ∣ u.x ∧ (V3.gcdV u : ℤ) ∣ u.y ∧ (V3.gcdV u : ℤ) ∣ u.z := by
  have h0 : V3.gcdV u ∣ u.x.natAbs := by
    rw [V3.gcdV]; exact dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)
  have h1 : V3.gcdV u ∣ u.y.natAbs := by
    rw [V3.gcdV]; exact dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
  have h2 : V3.gcdV u ∣ u.z.natAbs := by rw [V3.gcdV]; exact Nat.gcd_dvd_right _ _
  refine ⟨?_, ?_, ?_⟩
  · exact dvd_trans (by exact_mod_cast h0) (Int.natAbs_dvd.mpr (dvd_refl _))
  · exact dvd_trans (by exact_mod_cast h1) (Int.natAbs_dvd.mpr (dvd_refl _))
  · exact dvd_trans (by exact_mod_cast h2) (Int.natAbs_dvd.mpr (dvd_refl _))

/-- A primitive `V3` has gcd `1`. -/
theorem prim_gcdV_eq_one {u : V3} (hp : V3.Prim u) : V3.gcdV u = 1 := by
  obtain ⟨β, hβ⟩ := hp
  obtain ⟨h1, h2, h3⟩ := gcdV_dvd_coord u
  have hd : (V3.gcdV u : ℤ) ∣ 1 := by
    rw [← hβ]
    simp only [V3.dot]
    exact dvd_add (dvd_add (dvd_mul_of_dvd_right h1 β.x) (dvd_mul_of_dvd_right h2 β.y))
      (dvd_mul_of_dvd_right h3 β.z)
  exact Nat.dvd_one.mp (by
    have := (Int.natAbs_dvd_natAbs (a := (V3.gcdV u : ℤ)) (b := (1 : ℤ))).mpr hd
    simpa using this)

/-- The gcd scales by a positive factor. -/
theorem gcdV_smul {h : Nat} (_hh : 0 < h) (u : V3) :
    V3.gcdV (V3.smul (h : Int) u) = h * V3.gcdV u := by
  simp only [V3.gcdV, V3.smul, Int.natAbs_mul, Int.natAbs_natCast, Nat.gcd_mul_left]

/-- If `h > 0` divides every entry of `w` and `w / h` is primitive, then `gcdV w = h`. -/
theorem gcdV_eq_of_dvd_prim {w : V3} {h : Nat} (hh : 0 < h) (hdvd : V3.dvd (h : Int) w = true)
    (hprim : V3.Prim (V3.ediv w (h : Int))) : V3.gcdV w = h := by
  have hdvd' : ((h : Int) ∣ w.x ∧ (h : Int) ∣ w.y) ∧ (h : Int) ∣ w.z := by
    simpa [V3.dvd, Bool.and_eq_true, beq_iff_eq] using hdvd
  have hw : w = V3.smul (h : Int) (V3.ediv w (h : Int)) := by
    obtain ⟨wx, wy, wz⟩ := w
    simp only [V3.smul, V3.ediv, V3.mk.injEq]
    exact ⟨(Int.mul_ediv_cancel' hdvd'.1.1).symm, (Int.mul_ediv_cancel' hdvd'.1.2).symm,
      (Int.mul_ediv_cancel' hdvd'.2).symm⟩
  rw [hw, gcdV_smul hh, prim_gcdV_eq_one hprim, Nat.mul_one]

/-- `gcdV w = 1` makes `w` primitive (Bézout). -/
theorem prim_of_gcdV_eq_one {w : V3} (h : V3.gcdV w = 1) : V3.Prim w := by
  set d : ℕ := Nat.gcd w.x.natAbs w.y.natAbs with hd
  have hgd : Int.gcd w.x w.y = d := by rw [hd, Int.gcd_eq_natAbs]
  have hbez1 : ((d : ℕ) : ℤ) = w.x * Int.gcdA w.x w.y + w.y * Int.gcdB w.x w.y := by
    have := Int.gcd_eq_gcd_ab w.x w.y
    rwa [hgd] at this
  have hgcd2 : Int.gcd ((d : ℕ) : ℤ) w.z = 1 := by
    rw [Int.gcd_eq_natAbs]
    have hV : V3.gcdV w = Nat.gcd d w.z.natAbs := by rw [V3.gcdV, hd]
    rw [hV] at h
    simpa using h
  have hbez2 : (1 : ℤ) = ((d : ℕ) : ℤ) * Int.gcdA ((d : ℕ) : ℤ) w.z +
      w.z * Int.gcdB ((d : ℕ) : ℤ) w.z := by
    have := Int.gcd_eq_gcd_ab (((d : ℕ) : ℤ)) w.z
    rw [hgcd2] at this
    norm_num at this
    exact this
  refine ⟨⟨Int.gcdA w.x w.y * Int.gcdA ((d : ℕ) : ℤ) w.z,
    Int.gcdB w.x w.y * Int.gcdA ((d : ℕ) : ℤ) w.z,
    Int.gcdB ((d : ℕ) : ℤ) w.z⟩, ?_⟩
  set A : ℤ := Int.gcdA ((d : ℕ) : ℤ) w.z with hA
  set B : ℤ := Int.gcdB ((d : ℕ) : ℤ) w.z with hB
  rw [hbez1] at hbez2
  rw [hbez2]
  simp only [V3.dot]
  ring

/-! ## gcd and primitivity for `IVec` -/

/-- The gcd of the entries divides every entry. -/
theorem gcdIVec_dvd (v : IVec) (i : Fin 3) : (gcdIVec v : ℤ) ∣ v i := by
  have hd : gcdIVec v ∣ (v i).natAbs := by
    have h12 : gcdIVec v ∣ Nat.gcd (v 0).natAbs (v 1).natAbs := by
      rw [gcdIVec]; exact Nat.gcd_dvd_left _ _
    have h0 : gcdIVec v ∣ (v 0).natAbs := dvd_trans h12 (Nat.gcd_dvd_left _ _)
    have h1 : gcdIVec v ∣ (v 1).natAbs := dvd_trans h12 (Nat.gcd_dvd_right _ _)
    have h2 : gcdIVec v ∣ (v 2).natAbs := by rw [gcdIVec]; exact Nat.gcd_dvd_right _ _
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have h2 : (((v i).natAbs : ℕ) : ℤ) ∣ v i := Int.natAbs_dvd.mpr (dvd_refl _)
  exact dvd_trans (by exact_mod_cast hd) h2

/-- A common divisor of all entries divides the gcd. -/
theorem dvd_gcdIVec {d : Nat} {v : IVec} (h : ∀ i, (d : ℤ) ∣ v i) : d ∣ gcdIVec v := by
  have h0 : d ∣ (v 0).natAbs := by
    have := (Int.natAbs_dvd_natAbs (a := (d : ℤ)) (b := v 0)).mpr (h 0)
    rwa [Int.natAbs_natCast] at this
  have h1 : d ∣ (v 1).natAbs := by
    have := (Int.natAbs_dvd_natAbs (a := (d : ℤ)) (b := v 1)).mpr (h 1)
    rwa [Int.natAbs_natCast] at this
  have h2 : d ∣ (v 2).natAbs := by
    have := (Int.natAbs_dvd_natAbs (a := (d : ℤ)) (b := v 2)).mpr (h 2)
    rwa [Int.natAbs_natCast] at this
  rw [gcdIVec]
  exact Nat.dvd_gcd (Nat.dvd_gcd h0 h1) h2

/-- `d` divides every entry of a matrix-vector product. -/
theorem dvd_mulVec_of_dvd {B : IMat} {d : ℤ} {w : IVec} (h : ∀ j, d ∣ w j) (i : Fin 3) :
    d ∣ (B.mulVec w) i := by
  rw [Matrix.mulVec, dotProduct]
  exact Finset.dvd_sum (fun j _ => dvd_mul_of_dvd_right (h j) (B i j))

/-- The gcd of the entries is invariant under a unimodular substitution. -/
theorem gcdIVec_mulVec_unimodular {B : IMat} (hB : IsUnit B.det) (w : IVec) :
    gcdIVec (B.mulVec w) = gcdIVec w := by
  refine Nat.dvd_antisymm ?_ ?_
  · apply dvd_gcdIVec
    intro i
    have hmul : (invMat B).mulVec (B.mulVec w) = w := by
      rw [Matrix.mulVec_mulVec, invMat_mul hB, Matrix.one_mulVec]
    have hthis := dvd_mulVec_of_dvd (B := invMat B) (d := (gcdIVec (B.mulVec w) : ℤ))
      (fun j => gcdIVec_dvd (B.mulVec w) j) i
    rwa [hmul] at hthis
  · apply dvd_gcdIVec
    intro i
    exact dvd_mulVec_of_dvd (fun j => gcdIVec_dvd w j) i

/-- Primitivity is invariant under a unimodular substitution. -/
theorem primIVec_mulVec_unimodular {B : IMat} (hB : IsUnit B.det) {w : IVec}
    (hw : PrimIVec w) : PrimIVec (B.mulVec w) := by
  obtain ⟨β, hβ⟩ := hw
  refine ⟨(invMat B)ᵀ.mulVec β, ?_⟩
  rw [Matrix.dotProduct_mulVec]
  rw [← Matrix.mulVec_transpose, Matrix.mulVec_mulVec]
  rw [← Matrix.transpose_mul, invMat_mul hB, Matrix.transpose_one, Matrix.one_mulVec, hβ]

/-- The image lattice of the rank-one matrix `c wᵀ` meets `ℤ³` in `gcdIVec w · ℤ c`. -/
theorem latImg_rankOne {c w : IVec} (_hc : c ≠ 0) {v : IVec}
    (hv : toRVec v ∈ latImg (rankOne c w)) :
    ∃ t : Int, v = (t * (gcdIVec w : Int)) • c := by
  obtain ⟨y, hy⟩ := mem_latImg.mp hv
  rw [mulVec_toRVec] at hy
  have hv' : v = (rankOne c w).mulVec y := (toRVec_injective hy).symm
  set N : ℤ := ∑ j, w j * y j with hN
  have hcomp : ∀ i, (rankOne c w).mulVec y i = N * c i := by
    intro i
    rw [hN]
    simp only [rankOne, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    ring
  have hvN : v = N • c := by
    rw [hv']
    funext i
    rw [hcomp i, Pi.smul_apply, smul_eq_mul]
  have hdvd : (gcdIVec w : ℤ) ∣ N := by
    rw [hN]
    exact Finset.dvd_sum (fun j _ => dvd_mul_of_dvd_left (gcdIVec_dvd w j) (y j))
  refine ⟨N / (gcdIVec w : ℤ), ?_⟩
  rw [hvN]
  congr 1
  exact (Int.ediv_mul_cancel hdvd).symm

/-- The columns of `A` determine its `IMat` form as a rank-one matrix. -/
theorem cols_rankOne {A : M3} {c w : V3}
    (h : A.cols = [V3.smul w.x c, V3.smul w.y c, V3.smul w.z c]) :
    A.toIMat = rankOne c.toFun w.toFun := by
  simp only [M3.cols, List.cons.injEq, and_true, V3.smul, V3.mk.injEq] at h
  obtain ⟨⟨h00, h01, h02⟩, ⟨h10, h11, h12⟩, ⟨h20, h21, h22⟩⟩ := h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M3.toIMat, rankOne, V3.toFun, h00, h01, h02, h10, h11, h12, h20, h21, h22, mul_comm]

/-- gcd facts for integer vectors, used to compare the handedness values of two certificates.
`h > 0` with `h ∣ w` componentwise and `w / h` primitive characterises `gcdV w = h`; `gcdV = 1`
gives primitivity (Bézout); the gcd of the entries and primitivity are invariant under a
unimodular substitution; and the image lattice of the rank-one matrix `c wᵀ` is `gcdV w` times
`ℤ c`. -/
theorem gcd_v3 :
    (∀ {w : V3} {h : Nat}, 0 < h → V3.dvd (h : Int) w = true → V3.Prim (V3.ediv w (h : Int)) →
      V3.gcdV w = h) ∧
    (∀ {w : V3}, V3.gcdV w = 1 → V3.Prim w) ∧
    (∀ {B : IMat} (hB : IsUnit B.det) (w : IVec), gcdIVec (B.mulVec w) = gcdIVec w) ∧
    (∀ {B : IMat} (hB : IsUnit B.det) {w : IVec}, PrimIVec w → PrimIVec (B.mulVec w)) ∧
    (∀ {c w : IVec}, c ≠ 0 → ∀ {v : IVec}, toRVec v ∈ latImg (rankOne c w) →
      ∃ t : Int, v = (t * (gcdIVec w : Int)) • c) ∧
    (∀ {A : M3} {c w : V3}, A.cols = [V3.smul w.x c, V3.smul w.y c, V3.smul w.z c] →
      A.toIMat = rankOne c.toFun w.toFun) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w h hh hdvd hprim
    exact gcdV_eq_of_dvd_prim hh hdvd hprim
  · intro w h
    exact prim_of_gcdV_eq_one h
  · intro B hB w
    exact gcdIVec_mulVec_unimodular hB w
  · intro B hB w hw
    exact primIVec_mulVec_unimodular hB hw
  · intro c w hc v hv
    exact latImg_rankOne hc hv
  · intro A c w h
    exact cols_rankOne h

end Work.SGsep.hand
