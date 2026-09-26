import Mathlib
import Submission.Work.SG.SGsepDefs
import Submission.Work.SGsep.table_facts

/-!
# Glue lemmas for the `sym` (symmorphy-order) separation

This file collects the general, data-independent facts used by `Work.SGsep.sym_separates`:

* elementary closure facts for the lattice `ℤ³ ⊂ ℝ³` (`zLat`);
* naturality of `IsCob` (integral coboundaries) under an integral equivalence
  `IntEquiv P τ P' τ' U s`, for a *natural* multiple `c • τ` of the cocycle;
* uniqueness of the symmorphy order (`SymOrd`), via gcd-closure of the set of
  multiples of `τ` that are coboundaries (Bézout);
* completeness of `Data.primesOf` for orders `o ≤ 48`.

The naturality proof transports a witnessing potential `σ` by `σ' = U σ + c·s` (forward) and
`σ = U⁻¹ σ' − U⁻¹ (c·s)` (backward); the `s`-terms cancel against the affine conjugation.
-/

namespace Work.SGsep

open Work.SG
open scoped BigOperators
open Classical

/-! ## The `toRMat`/`Matrix.map` bridge and the coboundary defect -/

theorem toRMat_eq_map (U : IMat) : toRMat U = U.map (Int.cast : ℤ → ℝ) := rfl

/-- The defect of `v` relative to the potential `σ` at the element `A`. -/
def defect (v : IMat → Fin 3 → ℝ) (σ : Fin 3 → ℝ) (A : IMat) : Fin 3 → ℝ :=
  v A - (σ - (toRMat A).mulVec σ)

theorem isCob_iff_defect {P : Set IMat} {v : IMat → Fin 3 → ℝ} :
    IsCob P v ↔ ∃ σ : Fin 3 → ℝ, ∀ A ∈ P, defect v σ A ∈ zLat := Iff.rfl

/-! ## Closure of `zLat = ℤ³ ⊂ ℝ³` -/

theorem zLat_mulVec_int {q : Fin 3 → ℝ} (hq : q ∈ zLat) (M : IMat) :
    (toRMat M).mulVec q ∈ zLat := by
  obtain ⟨w, rfl⟩ := mem_zLat.mp hq
  rw [mulVec_toRVec]
  exact toRVec_mem_zLat _

theorem zLat_smul_int {q : Fin 3 → ℝ} (hq : q ∈ zLat) (a : ℤ) : (a : ℝ) • q ∈ zLat := by
  obtain ⟨w, rfl⟩ := mem_zLat.mp hq
  have h : (a : ℝ) • toRVec w = toRVec (a • w) := by funext i; simp [toRVec]
  rw [h]; exact toRVec_mem_zLat _

theorem zLat_smul_nat {q : Fin 3 → ℝ} (hq : q ∈ zLat) (c : ℕ) : (c : ℝ) • q ∈ zLat := by
  obtain ⟨w, rfl⟩ := mem_zLat.mp hq
  have h : (c : ℝ) • toRVec w = toRVec (c • w) := by funext i; simp [toRVec]
  rw [h]; exact toRVec_mem_zLat _

theorem zLat_add {q r : Fin 3 → ℝ} (hq : q ∈ zLat) (hr : r ∈ zLat) : q + r ∈ zLat :=
  AddSubgroup.add_mem _ hq hr

theorem zLat_sub {q r : Fin 3 → ℝ} (hq : q ∈ zLat) (hr : r ∈ zLat) : q - r ∈ zLat :=
  AddSubgroup.sub_mem _ hq hr

/-! ## Conjugation identities for `mulVec` -/

theorem conj_mulVec_U (U B : IMat) (x : Fin 3 → ℝ) (hU : IsUnit U.det) :
    (toRMat (U * B * U⁻¹)).mulVec ((toRMat U).mulVec x)
      = (toRMat U).mulVec ((toRMat B).mulVec x) := by
  have h1 : U * B * U⁻¹ * U = U * B := by
    rw [mul_assoc (U * B) U⁻¹ U, Matrix.nonsing_inv_mul U hU, mul_one]
  calc (toRMat (U * B * U⁻¹)).mulVec ((toRMat U).mulVec x)
      = (toRMat (U * B * U⁻¹) * toRMat U).mulVec x := Matrix.mulVec_mulVec x _ _
    _ = (toRMat (U * B * U⁻¹ * U)).mulVec x := by rw [← toRMat_mul]
    _ = (toRMat (U * B)).mulVec x := by rw [h1]
    _ = (toRMat U * toRMat B).mulVec x := by rw [toRMat_mul]
    _ = (toRMat U).mulVec ((toRMat B).mulVec x) := (Matrix.mulVec_mulVec x _ _).symm

theorem mulVec_Uinv_conj (U B : IMat) (x : Fin 3 → ℝ) (hU : IsUnit U.det) :
    (toRMat U⁻¹).mulVec ((toRMat (U * B * U⁻¹)).mulVec x)
      = (toRMat B).mulVec ((toRMat U⁻¹).mulVec x) := by
  have h1 : U⁻¹ * (U * B * U⁻¹) = B * U⁻¹ := by
    rw [← mul_assoc U⁻¹ (U * B) U⁻¹, ← mul_assoc U⁻¹ U B, Matrix.nonsing_inv_mul U hU, one_mul]
  calc (toRMat U⁻¹).mulVec ((toRMat (U * B * U⁻¹)).mulVec x)
      = (toRMat U⁻¹ * toRMat (U * B * U⁻¹)).mulVec x := Matrix.mulVec_mulVec x _ _
    _ = (toRMat (U⁻¹ * (U * B * U⁻¹))).mulVec x := by rw [← toRMat_mul]
    _ = (toRMat (B * U⁻¹)).mulVec x := by rw [h1]
    _ = (toRMat B * toRMat U⁻¹).mulVec x := by rw [toRMat_mul]
    _ = (toRMat B).mulVec ((toRMat U⁻¹).mulVec x) := (Matrix.mulVec_mulVec x _ _).symm

theorem mulVec_Uinv_U (U : IMat) (x : Fin 3 → ℝ) (hU : IsUnit U.det) :
    (toRMat U⁻¹).mulVec ((toRMat U).mulVec x) = x := by
  rw [Matrix.mulVec_mulVec, ← toRMat_mul,
    show U⁻¹ * U = 1 from Matrix.nonsing_inv_mul U hU, toRMat_one, Matrix.one_mulVec]

/-! ## Naturality of `IsCob` under `IntEquiv` -/

theorem IsCob_nat_smul {P P' : Set IMat} {τ τ' : IMat → Fin 3 → ℝ} {U : IMat} {s : Fin 3 → ℝ}
    (hU : IsUnit U.det) (h : IntEquiv P τ P' τ' U s) (c : ℕ) :
    IsCob P (fun A => (c : ℝ) • τ A) ↔ IsCob P' (fun A => (c : ℝ) • τ' A) := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨(toRMat U).mulVec σ + (c : ℝ) • s, ?_⟩
    intro A' hA'
    obtain ⟨B, hB, rfl⟩ := (h.1 A').mp hA'
    obtain ⟨n, hn⟩ := h.2 B hB
    have hn2 : τ' (U * B * U⁻¹)
        = (toRMat U).mulVec (τ B) + s - (toRMat (U * B * U⁻¹)).mulVec s + intVec n := hn
    have hb : (c : ℝ) • τ' (U * B * U⁻¹)
        = (toRMat U).mulVec ((c : ℝ) • τ B)
          + ((c : ℝ) • s - (toRMat (U * B * U⁻¹)).mulVec ((c : ℝ) • s))
          + (c : ℝ) • intVec n := by
      rw [hn2]; simp only [smul_add, smul_sub, Matrix.mulVec_smul]; abel
    have hdecomp : (c : ℝ) • τ B = σ - (toRMat B).mulVec σ
        + defect (fun A => (c : ℝ) • τ A) σ B := by rw [defect]; abel
    have key : (toRMat U).mulVec ((c : ℝ) • τ B)
          + ((c : ℝ) • s - (toRMat (U * B * U⁻¹)).mulVec ((c : ℝ) • s)) + (c : ℝ) • intVec n
          - (((toRMat U).mulVec σ + (c : ℝ) • s)
              - (toRMat (U * B * U⁻¹)).mulVec ((toRMat U).mulVec σ + (c : ℝ) • s))
        = (toRMat U).mulVec (defect (fun A => (c : ℝ) • τ A) σ B) + (c : ℝ) • intVec n := by
      rw [hdecomp]
      simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, conj_mulVec_U U B σ hU]
      abel
    show defect (fun A => (c : ℝ) • τ' A) ((toRMat U).mulVec σ + (c : ℝ) • s) (U * B * U⁻¹) ∈ zLat
    rw [defect, hb, key]
    exact zLat_add (zLat_mulVec_int (hσ B hB) U) (zLat_smul_nat (toRVec_mem_zLat n) c)
  · rintro ⟨σ', hσ'⟩
    refine ⟨(toRMat U⁻¹).mulVec σ' - (c : ℝ) • ((toRMat U⁻¹).mulVec s), ?_⟩
    intro B hB
    have hA' : U * B * U⁻¹ ∈ P' := (h.1 (U * B * U⁻¹)).mpr ⟨B, hB, rfl⟩
    obtain ⟨n, hn⟩ := h.2 B hB
    have hn2 : τ' (U * B * U⁻¹)
        = (toRMat U).mulVec (τ B) + s - (toRMat (U * B * U⁻¹)).mulVec s + intVec n := hn
    have hsub : (toRMat U⁻¹).mulVec (τ' (U * B * U⁻¹))
        = τ B + (toRMat U⁻¹).mulVec s - (toRMat B).mulVec ((toRMat U⁻¹).mulVec s)
          + (toRMat U⁻¹).mulVec (intVec n) := by
      have := congrArg (fun x => (toRMat U⁻¹).mulVec x) hn2
      simpa only [Matrix.mulVec_add, Matrix.mulVec_sub, mulVec_Uinv_U U _ hU,
        mulVec_Uinv_conj U B s hU] using this
    have hsub' : τ B = (toRMat U⁻¹).mulVec (τ' (U * B * U⁻¹))
        - (toRMat U⁻¹).mulVec s + (toRMat B).mulVec ((toRMat U⁻¹).mulVec s)
        - (toRMat U⁻¹).mulVec (intVec n) := by rw [hsub]; abel
    have hb' : (c : ℝ) • τ B
        = (toRMat U⁻¹).mulVec ((c : ℝ) • τ' (U * B * U⁻¹))
          - (c : ℝ) • ((toRMat U⁻¹).mulVec s)
          + (toRMat B).mulVec ((c : ℝ) • ((toRMat U⁻¹).mulVec s))
          - (c : ℝ) • ((toRMat U⁻¹).mulVec (intVec n)) := by
      rw [hsub']; simp only [smul_add, smul_sub, Matrix.mulVec_smul]
    have hdecomp' : (c : ℝ) • τ' (U * B * U⁻¹) = σ' - (toRMat (U * B * U⁻¹)).mulVec σ'
        + defect (fun A => (c : ℝ) • τ' A) σ' (U * B * U⁻¹) := by rw [defect]; abel
    have key : defect (fun A => (c : ℝ) • τ A)
          ((toRMat U⁻¹).mulVec σ' - (c : ℝ) • ((toRMat U⁻¹).mulVec s)) B
        = (toRMat U⁻¹).mulVec (defect (fun A => (c : ℝ) • τ' A) σ' (U * B * U⁻¹))
          - (c : ℝ) • ((toRMat U⁻¹).mulVec (intVec n)) := by
      rw [defect]
      simp only [hb', hdecomp', Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul,
        mulVec_Uinv_conj U B σ' hU]
      abel
    show defect (fun A => (c : ℝ) • τ A) ((toRMat U⁻¹).mulVec σ'
        - (c : ℝ) • ((toRMat U⁻¹).mulVec s)) B ∈ zLat
    rw [key]
    exact zLat_sub (zLat_mulVec_int (hσ' (U * B * U⁻¹) hA') U⁻¹)
      (zLat_smul_nat (zLat_mulVec_int (toRVec_mem_zLat n) U⁻¹) c)

/-! ## `IsCob` is closed under integer linear combinations -/

theorem IsCob_lin {P : Set IMat} {v w : IMat → Fin 3 → ℝ} (a b : ℤ)
    (hv : IsCob P v) (hw : IsCob P w) :
    IsCob P (fun A => (a : ℝ) • v A + (b : ℝ) • w A) := by
  obtain ⟨σv, hσv⟩ := hv
  obtain ⟨σw, hσw⟩ := hw
  refine ⟨(a : ℝ) • σv + (b : ℝ) • σw, ?_⟩
  intro A hA
  have hvA := hσv A hA
  have hwA := hσw A hA
  have key : (a : ℝ) • v A + (b : ℝ) • w A
      - (((a : ℝ) • σv + (b : ℝ) • σw)
        - (toRMat A).mulVec ((a : ℝ) • σv + (b : ℝ) • σw))
      = (a : ℝ) • (v A - (σv - (toRMat A).mulVec σv))
        + (b : ℝ) • (w A - (σw - (toRMat A).mulVec σw)) := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    module
  rw [key]
  exact zLat_add (zLat_smul_int hvA a) (zLat_smul_int hwA b)

/-- One-step defect propagation for a cocycle `τ` and natural multiple `c`: if the coboundary
defect of `c • τ` vanishes at `A` and at `B` and `τ (A * B) = τ A + A τ B + ℤ³`, then it vanishes
at `A * B`. -/
theorem defect_mul {τ : IMat → Fin 3 → ℝ} {c : ℕ} {σ : Fin 3 → ℝ} {A B : IMat} {n : IVec}
    (hc : τ (A * B) = τ A + (toRMat A).mulVec (τ B) + toRVec n)
    (hA : (c : ℝ) • τ A - (σ - (toRMat A).mulVec σ) ∈ zLat)
    (hB : (c : ℝ) • τ B - (σ - (toRMat B).mulVec σ) ∈ zLat) :
    (c : ℝ) • τ (A * B) - (σ - (toRMat (A * B)).mulVec σ) ∈ zLat := by
  have hkey : (c : ℝ) • τ (A * B) - (σ - (toRMat (A * B)).mulVec σ)
      = ((c : ℝ) • τ A - (σ - (toRMat A).mulVec σ))
        + (toRMat A).mulVec ((c : ℝ) • τ B - (σ - (toRMat B).mulVec σ))
        + (c : ℝ) • toRVec n := by
    rw [hc, toRMat_mul]
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      smul_add, smul_sub]
    abel
  rw [hkey]
  exact zLat_add (zLat_add hA (zLat_mulVec_int hB A)) (zLat_smul_nat (toRVec_mem_zLat n) c)

theorem IsCob_zero (P : Set IMat) : IsCob P (fun _ => 0) := by
  refine ⟨0, ?_⟩
  intro A _
  simpa [Matrix.mulVec_zero] using (zLat.zero_mem)

theorem IsCob_smul_nat {P : Set IMat} {v : IMat → Fin 3 → ℝ} (hv : IsCob P v) (c : ℕ) :
    IsCob P (fun A => (c : ℝ) • v A) := by
  have := IsCob_lin (P := P) (v := v) (w := fun _ => 0) (c : ℤ) 0 hv (IsCob_zero P)
  simpa using this

/-! ## Uniqueness of the symmorphy order -/

/-- `Nat.gcd`-closure of coboundarity of multiples of `τ`. -/
theorem IsCob_gcd {P : Set IMat} {τ : IMat → Fin 3 → ℝ} {c d : ℕ}
    (hc : IsCob P (fun A => (c : ℝ) • τ A))
    (hd : IsCob P (fun A => (d : ℝ) • τ A)) :
    IsCob P (fun A => ((Nat.gcd c d : ℕ) : ℝ) • τ A) := by
  have hlin := IsCob_lin (P := P) (v := fun A => (c : ℝ) • τ A)
    (w := fun A => (d : ℝ) • τ A) (Nat.gcdA c d) (Nat.gcdB c d) hc hd
  have heq : (fun A => ((Nat.gcd c d : ℕ) : ℝ) • τ A)
      = (fun A => ((Nat.gcdA c d : ℤ) : ℝ) • ((c : ℝ) • τ A)
          + ((Nat.gcdB c d : ℤ) : ℝ) • ((d : ℝ) • τ A)) := by
    funext A
    have hbez : ((Nat.gcd c d : ℕ) : ℝ)
        = (Nat.gcdA c d : ℝ) * (c : ℝ) + (Nat.gcdB c d : ℝ) * (d : ℝ) := by
      have h := Nat.gcd_eq_gcd_ab c d
      have hℝ := congrArg (fun z : ℤ => (z : ℝ)) h
      push_cast at hℝ
      rw [hℝ]; ring
    rw [hbez, add_smul, smul_smul, smul_smul]
  rw [heq]
  exact hlin

/-- The symmorphy order is unique: the set `{c : ℕ | c τ is a coboundary}` is nonempty
(`o τ` is one) and closed under `gcd` (Bézout), hence is the set of multiples of its least
positive element; `SymOrd`'s minimality clause pins that element to be `o`. -/
theorem SymOrd_unique {P : Set IMat} {τ : IMat → Fin 3 → ℝ} {o o' : ℕ}
    (h : SymOrd P τ o) (h' : SymOrd P τ o') : o = o' := by
  have dvd_of : ∀ (o₀ : ℕ), SymOrd P τ o₀ →
      ∀ c : ℕ, IsCob P (fun A => (c : ℝ) • τ A) → o₀ ∣ c := by
    intro o₀ ho₀ c hc
    set d := Nat.gcd o₀ c with hddef
    have hd : IsCob P (fun A => (d : ℝ) • τ A) := IsCob_gcd ho₀.2.1 hc
    have hdvd : d ∣ o₀ := Nat.gcd_dvd_left o₀ c
    have hdvd' : d ∣ c := Nat.gcd_dvd_right o₀ c
    have hdpos : 0 < d := Nat.gcd_pos_of_pos_left c ho₀.1
    rcases eq_or_lt_of_le (Nat.le_of_dvd ho₀.1 hdvd) with heq | hlt
    · rw [← heq]; exact hdvd'
    · exfalso
      have hdvd2 : d * (o₀ / d) = o₀ := Nat.mul_div_cancel' hdvd
      have hqne1 : o₀ / d ≠ 1 := by
        intro h1
        have := hdvd2
        rw [h1, mul_one] at this
        omega
      obtain ⟨p, hpp, hpdvd⟩ := Nat.exists_prime_and_dvd hqne1
      have hpo : p ∣ o₀ := by rw [← hdvd2]; exact Dvd.dvd.mul_left hpdvd d
      have hcop : o₀ / p = d * (o₀ / d / p) := by
        have h1 : p * (o₀ / d / p) = o₀ / d := Nat.mul_div_cancel' hpdvd
        have h2 : p * (d * (o₀ / d / p)) = o₀ := by
          rw [← mul_assoc, mul_comm p d, mul_assoc, h1, hdvd2]
        calc o₀ / p = p * (d * (o₀ / d / p)) / p := by rw [h2]
          _ = d * (o₀ / d / p) := Nat.mul_div_cancel_left _ hpp.pos
      have hgood : IsCob P (fun A => ((o₀ / p : ℕ) : ℝ) • τ A) := by
        have hstep := IsCob_smul_nat hd (o₀ / d / p)
        have heq : (fun A => ((o₀ / p : ℕ) : ℝ) • τ A)
            = (fun A => ((o₀ / d / p : ℕ) : ℝ) • ((d : ℝ) • τ A)) := by
          funext A; rw [hcop]; push_cast
          rw [mul_comm ((d : ℝ)) (((o₀ / d / p : ℕ) : ℝ)), smul_smul]
        rw [heq]; exact hstep
      exact ho₀.2.2 p hpp hpo hgood
  exact Nat.dvd_antisymm (dvd_of o h o' h'.2.1) (dvd_of o' h' o h.2.1)

/-- Naturality of the symmorphy order under an integral equivalence. -/
theorem SymOrd_nat {P P' : Set IMat} {τ τ' : IMat → Fin 3 → ℝ} {U : IMat} {s : Fin 3 → ℝ}
    (hU : IsUnit U.det) (h : IntEquiv P τ P' τ' U s) (o : ℕ) :
    SymOrd P τ o ↔ SymOrd P' τ' o := by
  simp only [SymOrd]
  refine and_congr_right' (and_congr ?_ ?_)
  · exact IsCob_nat_smul hU h o
  · constructor <;> intro H p hp hpd hc
    · exact H p hp hpd ((IsCob_nat_smul hU h (o / p)).mpr hc)
    · exact H p hp hpd ((IsCob_nat_smul hU h (o / p)).mp hc)

/-! ## `Data.primesOf` is complete for orders `≤ 48` -/

theorem primesOf_complete {o p : ℕ} (hpos : 0 < o) (ho : o ≤ 48)
    (hp : p.Prime) (hpd : p ∣ o) : p ∈ Data.primesOf o := by
  have hp48 : p ≤ 48 := le_trans (Nat.le_of_dvd hpos hpd) ho
  have hpprime_mem : p ∈ Data.smallPrimes := by
    have hdec : (List.range 49).all
        (fun q => decide (Nat.Prime q → q ∈ Data.smallPrimes)) = true := by decide
    exact of_decide_eq_true (List.all_eq_true.mp hdec p (List.mem_range.mpr (by omega))) hp
  have hmod : o % p = 0 := Nat.dvd_iff_mod_eq_zero.mp hpd
  simp only [Data.primesOf, List.mem_filter, hpprime_mem, true_and, beq_iff_eq, hmod]

end Work.SGsep
