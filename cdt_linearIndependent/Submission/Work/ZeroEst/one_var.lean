import Mathlib
import Submission.Work.ZeroEst.defs
import Submission.Work.ZeroEst.one_var_defs
import Submission.Work.ZeroEst.case_det
import Submission.Work.ZeroEst.fixed_deg_order_bound
import Submission.Work.ZeroEst.case_det_detdeg
import Submission.Work.ZeroEst.case_det_order_sum
import Submission.Work.ZeroEst.case_det_order_iter
import Submission.Work.ZeroEst.case_det_orbit_dot
import Submission.Work.ZeroEst.case_det_cramer
import Submission.Work.ZeroEst.lang24rat_clear

/-!
# Area Z, one variable: Shidlovsky's lemma (`D`-closed case)
-/

namespace Work.ZeroEst

open Submission.CDTPlan
open Polynomial PowerSeries

variable {m : ℕ}

/-- `F k = ⟨Λᵏ P, f⟩ = θᵏ R` for `R = ⟨P, f⟩`. -/
noncomputable def Fcomb (q : Polynomial ℚ) (A : Fin m → Fin m → Polynomial ℚ)
    (f : Fin m → PowerSeries ℚ) (P : Fin m → Polynomial ℚ) (k : ℕ) : PowerSeries ℚ :=
  ∑ i, ((orbit q A P k) i : PowerSeries ℚ) * f i

lemma Fcomb_zero (q : Polynomial ℚ) (A : Fin m → Fin m → Polynomial ℚ)
    (f : Fin m → PowerSeries ℚ) (P : Fin m → Polynomial ℚ) :
    Fcomb q A f P 0 = ∑ i, (P i : PowerSeries ℚ) * f i := by
  simp [Fcomb, orbit_zero]

/-- The order of a nonzero polynomial, viewed as a power series, is at most its `natDegree`. -/
lemma order_coe_natDegree_le (p : Polynomial ℚ) (hp : p ≠ 0) :
    (p : PowerSeries ℚ).order ≤ (p.natDegree : ℕ∞) := by
  refine PowerSeries.order_le p.natDegree ?_
  rw [Polynomial.coeff_coe, Polynomial.coeff_natDegree]
  exact Polynomial.leadingCoeff_ne_zero.mpr hp

/-- The `j`-th coefficient of the `l`-th auxiliary combination. -/
noncomputable def depCoeff {m r : ℕ} (V : Fin r → Fin m) (G : Polynomial ℚ)
    (B : Fin r → Fin m → Polynomial ℚ) (l : Fin r) (j : Fin m) : Polynomial ℚ :=
  if j ∈ Finset.univ.image V then (if j = V l then G else 0) else B l j

lemma depCoeff_self {m r : ℕ} {V : Fin r → Fin m} {G : Polynomial ℚ}
    {B : Fin r → Fin m → Polynomial ℚ} (l : Fin r) :
    depCoeff V G B l (V l) = G := by
  rw [depCoeff, if_pos (Finset.mem_image.mpr ⟨l, Finset.mem_univ _, rfl⟩), if_pos rfl]

lemma depCoeff_of_notMem {m r : ℕ} {V : Fin r → Fin m} {G : Polynomial ℚ}
    {B : Fin r → Fin m → Polynomial ℚ} {l : Fin r} {j : Fin m}
    (h : j ∉ Finset.univ.image V) : depCoeff V G B l j = B l j := by
  rw [depCoeff, if_neg h]

lemma depCoeff_of_mem_ne {m r : ℕ} {V : Fin r → Fin m} {G : Polynomial ℚ}
    {B : Fin r → Fin m → Polynomial ℚ} {l : Fin r} {j : Fin m}
    (hj : j ∈ Finset.univ.image V) (hne : j ≠ V l) : depCoeff V G B l j = 0 := by
  rw [depCoeff, if_pos hj, if_neg hne]

/-- **The cleared dependence identity.** -/
lemma cleared_combine {m r : ℕ} (q : Polynomial ℚ) (A : Fin m → Fin m → Polynomial ℚ)
    (f : Fin m → PowerSeries ℚ) (P : Fin m → Polynomial ℚ) (V : Fin r → Fin m)
    (G : Polynomial ℚ) (B : Fin r → Fin m → Polynomial ℚ) (hV : Function.Injective V)
    (k : ℕ) (hrelV : ∀ j, (∀ l, V l ≠ j) →
        G * orbit q A P k j = ∑ l, B l j * orbit q A P k (V l)) :
    (G : PowerSeries ℚ) * (∑ j, (orbit q A P k j : PowerSeries ℚ) * f j)
      = ∑ l, (orbit q A P k (V l) : PowerSeries ℚ)
          * (∑ j, (depCoeff V G B l j : PowerSeries ℚ) * f j) := by
  classical
  have hcoef : ∀ j, (G : PowerSeries ℚ) * (orbit q A P k j : PowerSeries ℚ)
      = ∑ l, (orbit q A P k (V l) : PowerSeries ℚ) * (depCoeff V G B l j : PowerSeries ℚ) := by
    intro j
    by_cases hj : j ∈ Finset.univ.image V
    · obtain ⟨l₀, -, rfl⟩ := Finset.mem_image.mp hj
      rw [Finset.sum_eq_single l₀]
      · rw [depCoeff_self]; exact mul_comm _ _
      · intro b _ hb
        have hz : depCoeff V G B b (V l₀) = 0 :=
          depCoeff_of_mem_ne (Finset.mem_image.mpr ⟨l₀, Finset.mem_univ _, rfl⟩)
            (fun h => hb (hV h).symm)
        rw [hz, Polynomial.coe_zero, mul_zero]
      · intro h; exact absurd (Finset.mem_univ l₀) h
    · have hne : ∀ l, V l ≠ j := fun l hl =>
        hj (Finset.mem_image.mpr ⟨l, Finset.mem_univ _, hl⟩)
      have h1 : (G : PowerSeries ℚ) * (orbit q A P k j : PowerSeries ℚ)
          = ∑ l, (B l j : PowerSeries ℚ) * (orbit q A P k (V l) : PowerSeries ℚ) := by
        have hh := congrArg (fun p : Polynomial ℚ => (p : PowerSeries ℚ)) (hrelV j hne)
        simpa only [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum, map_mul] using hh
      rw [h1]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [depCoeff_of_notMem hj]
      exact mul_comm _ _
  calc (G : PowerSeries ℚ) * (∑ j, (orbit q A P k j : PowerSeries ℚ) * f j)
      = ∑ j, ((G : PowerSeries ℚ) * (orbit q A P k j : PowerSeries ℚ)) * f j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by rw [mul_assoc])
    _ = ∑ j, (∑ l, (orbit q A P k (V l) : PowerSeries ℚ)
            * (depCoeff V G B l j : PowerSeries ℚ)) * f j := by
        exact Finset.sum_congr rfl (fun j _ => by rw [hcoef j])
    _ = ∑ j, ∑ l, ((orbit q A P k (V l) : PowerSeries ℚ)
            * (depCoeff V G B l j : PowerSeries ℚ)) * f j := by
        exact Finset.sum_congr rfl (fun j _ => by rw [Finset.sum_mul])
    _ = ∑ l, ∑ j, ((orbit q A P k (V l) : PowerSeries ℚ)
            * (depCoeff V G B l j : PowerSeries ℚ)) * f j := Finset.sum_comm
    _ = ∑ l, (orbit q A P k (V l) : PowerSeries ℚ)
          * (∑ j, (depCoeff V G B l j : PowerSeries ℚ) * f j) := by
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by rw [mul_assoc])


/-- **The dependent case of Shidlovsky's lemma**, given Lang's Lemma 2.4 in cleared form. -/
theorem caseB (m : ℕ) (q : Polynomial ℚ) (A : Fin m → Fin m → Polynomial ℚ)
    (f : Fin m → PowerSeries ℚ) (hq : q ≠ 0) (hpi : Submission.CDTPlan.PolyIndependent f)
    (hrel : ∀ i, (q : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) (f i)
      = ∑ j, (A i j : PowerSeries ℚ) * f j)
    (N : ℕ)
    (hK : ∀ (P : Fin m → Polynomial ℚ),
      ¬ LinearIndependent (RatFunc ℚ)
        (fun k : Fin m => (fun i => ((orbit q A P k) i : RatFunc ℚ))) →
      ∃ (r : ℕ) (hr : r < m) (V k0 : Fin r → Fin m) (G : Polynomial ℚ)
        (B : Fin r → Fin m → Polynomial ℚ),
        Function.Injective V ∧
        (Matrix.of (fun a b : Fin r => orbit q A P (k0 a) (V b))).det ≠ 0 ∧
        G ≠ 0 ∧ G.degree ≤ (N : WithBot ℕ) ∧
        (∀ l j, (B l j).degree ≤ (N : WithBot ℕ)) ∧
        (∀ k, k < m → ∀ j, (∀ l, V l ≠ j) →
          G * orbit q A P k j = ∑ l, B l j * orbit q A P k (V l))) :
    ∃ C : ℕ, ∀ (D : ℕ) (P : Fin m → Polynomial ℚ),
      DegLT P D → (∑ i, (P i : PowerSeries ℚ) * f i) ≠ 0 →
      ¬ LinearIndependent (RatFunc ℚ)
        (fun k : Fin m => (fun i => ((orbit q A P k) i : RatFunc ℚ))) →
      (∑ i, (P i : PowerSeries ℚ) * f i).order ≤ (m * D + C : ℕ∞) := by
  classical
  obtain ⟨N₁, hN₁⟩ := fixed_deg_order_bound m f N
  refine ⟨(m - 1) + (m - 1) * (m - 1) * dlt q A + N₁ + m, ?_⟩
  intro D P hP hRne hdep
  set R : PowerSeries ℚ := ∑ i, (P i : PowerSeries ℚ) * f i with hRdef
  obtain ⟨r, hr, V, k0, G, B, hVinj, hdet, hGne, hGdeg, hBdeg, hrelV⟩ := hK P hdep
  have hD1 : 1 ≤ D := by
    by_contra hlt
    have hD0 : D = 0 := by omega
    have hPz : ∀ i, P i = 0 := fun i => Polynomial.ext fun k => hP i k (by rw [hD0]; exact Nat.zero_le k)
    exact hRne (by rw [hRdef]; simp [hPz])
  have hrpos : 0 < m := lt_of_le_of_lt (Nat.zero_le r) hr
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h
      exfalso
      have hPz : ∀ j : Fin m, P j = 0 := by
        intro j
        have h0' : G * P j = 0 := by
          have h0 := hrelV 0 hrpos j (fun l => absurd l.isLt (by omega))
          simpa [orbit_zero] using h0
        rcases mul_eq_zero.mp h0' with h1 | h1
        · exact absurd h1 hGne
        · exact h1
      exact hRne (by rw [hRdef]; simp [hPz])
    · exact h
  let z : Fin r → PowerSeries ℚ := fun l => ∑ j, (depCoeff V G B l j : PowerSeries ℚ) * f j
  have hz_ne : ∀ l, z l ≠ 0 := by
    intro l hz
    have h0 := hpi (fun j => depCoeff V G B l j) hz (V l)
    rw [depCoeff_self] at h0
    exact hGne h0
  have hz_ord : ∀ l, (z l).order ≤ (N₁ : ℕ∞) := by
    intro l
    refine hN₁ (fun j => depCoeff V G B l j) ?_ (hz_ne l)
    intro j
    rw [depCoeff]
    split_ifs with h1 h2
    · exact hGdeg
    · exact bot_le
    · exact hBdeg l j
  have hrow : ∀ k, k < m → (∑ b : Fin r, (orbit q A P k (V b) : PowerSeries ℚ) * z b)
      = (G : PowerSeries ℚ) * (∑ j, (orbit q A P k j : PowerSeries ℚ) * f j) := by
    intro k hk
    exact (cleared_combine q A f P V G B hVinj k (fun j hj => hrelV k hk j hj)).symm
  have hF : ∀ k : ℕ, (∑ j, (orbit q A P k j : PowerSeries ℚ) * f j)
      = ((fun S => (q : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) S)^[k]) R := by
    intro k
    rw [hRdef]
    exact case_det_orbit_dot m q A f hrel P k
  let Mp : Matrix (Fin r) (Fin r) (Polynomial ℚ) := Matrix.of (fun a b => orbit q A P (k0 a) (V b))
  have hdeg : ∀ a b, (Mp a b).natDegree ≤ D + (m - 1) * dlt q A := by
    intro a b
    have hDg := (DegLT_iff_degree _ _).mp (orbit_DegLT q A P D hD1 hP (k0 a)) (V b)
    have hle : D + (k0 a : ℕ) * dlt q A ≤ D + (m - 1) * dlt q A :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ (by have := (k0 a).isLt; omega)) D
    calc (Mp a b).natDegree = (orbit q A P (k0 a) (V b)).natDegree := rfl
      _ ≤ D + (m - 1) * dlt q A := Polynomial.natDegree_le_iff_degree_le.mpr
            (le_of_lt (lt_of_lt_of_le hDg (by exact_mod_cast hle)))
  have hdetdeg : Mp.det.natDegree ≤ r * (D + (m - 1) * dlt q A) := case_det_detdeg Mp _ hdeg
  let M : Matrix (Fin r) (Fin r) (PowerSeries ℚ)
      := Matrix.of (fun a b => (orbit q A P (k0 a) (V b) : PowerSeries ℚ))
  have hMmap : M = Mp.map (fun p : Polynomial ℚ => (p : PowerSeries ℚ)) := by
    ext a b; simp [M, Mp, Matrix.map_apply]
  have hMdet : M.det = (Mp.det : PowerSeries ℚ) := by
    rw [hMmap]
    have key := RingHom.map_det (algebraMap (Polynomial ℚ) (PowerSeries ℚ)) Mp
    rw [RingHom.mapMatrix_apply] at key
    exact key.symm
  have hcramer : ∀ l, M.det * z l
      = ∑ a : Fin r, M.adjugate l a * ((G : PowerSeries ℚ)
          * ((fun S => (q : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) S)^[(k0 a : ℕ)]) R) := by
    intro l
    rw [cramer_aux M z l]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have hrowa : (∑ b, M a b * z b) = (G : PowerSeries ℚ)
        * ((fun S => (q : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) S)^[(k0 a : ℕ)]) R := by
      have h1 : (∑ b, M a b * z b)
          = ∑ b, (orbit q A P (k0 a) (V b) : PowerSeries ℚ) * z b :=
        Finset.sum_congr rfl (fun b _ => by simp [M])
      rw [h1, hrow (k0 a) (k0 a).isLt, hF (k0 a)]
    rw [hrowa]
  let l₀ : Fin r := ⟨0, hr1⟩
  have hkey : (G : PowerSeries ℚ).order + ((R.order.toNat - (m - 1) : ℕ) : ℕ∞)
      ≤ (Mp.det.natDegree : ℕ∞) + (N₁ : ℕ∞) := by
    have hstep : (G : PowerSeries ℚ).order + ((R.order.toNat - (m - 1) : ℕ) : ℕ∞)
        ≤ (M.det * z l₀).order := by
      rw [hcramer l₀]
      refine case_det_order_sum Finset.univ
        (fun a : Fin r => M.adjugate l₀ a * ((G : PowerSeries ℚ)
          * ((fun S => (q : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) S)^[(k0 a : ℕ)]) R))
        ((G : PowerSeries ℚ).order + ((R.order.toNat - (m - 1) : ℕ) : ℕ∞)) ?_
      intro a _
      have h1 : ((R.order.toNat - (m - 1) : ℕ) : ℕ∞)
          ≤ (((fun S => (q : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) S)^[(k0 a : ℕ)]) R).order := by
        refine le_trans (ENat.natCast_le_natCast.mpr ?_) (case_det_order_iter q R (k0 a))
        exact Nat.sub_le_sub_left (by have := (k0 a).isLt; omega) _
      have h2 : (G : PowerSeries ℚ).order + ((R.order.toNat - (m - 1) : ℕ) : ℕ∞)
          ≤ ((G : PowerSeries ℚ)
              * ((fun S => (q : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) S)^[(k0 a : ℕ)]) R).order := by
        rw [PowerSeries.order_mul]
        exact add_le_add (le_refl _) h1
      have h3 : ((G : PowerSeries ℚ)
              * ((fun S => (q : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) S)^[(k0 a : ℕ)]) R).order
          ≤ (M.adjugate l₀ a * ((G : PowerSeries ℚ)
              * ((fun S => (q : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) S)^[(k0 a : ℕ)]) R)).order :=
        le_trans (le_add_left le_rfl) (PowerSeries.le_order_mul _ _)
      exact le_trans h2 h3
    calc (G : PowerSeries ℚ).order + ((R.order.toNat - (m - 1) : ℕ) : ℕ∞)
        ≤ (M.det * z l₀).order := hstep
      _ = M.det.order + (z l₀).order := PowerSeries.order_mul _ _
      _ ≤ (Mp.det.natDegree : ℕ∞) + (N₁ : ℕ∞) := by
          refine add_le_add ?_ (hz_ord l₀)
          rw [hMdet]
          exact order_coe_natDegree_le Mp.det hdet
  have hmain : (R.order.toNat - (m - 1)) ≤ Mp.det.natDegree + N₁ := by
    have h2 : ((R.order.toNat - (m - 1) : ℕ) : ℕ∞)
        ≤ (Mp.det.natDegree : ℕ∞) + (N₁ : ℕ∞) :=
      le_trans (le_add_left le_rfl) hkey
    push_cast at h2
    exact ENat.natCast_le_natCast.mp h2
  rw [← PowerSeries.coe_toNat_order hRne]
  refine ENat.natCast_le_natCast.mpr ?_
  have h4 : Mp.det.natDegree ≤ (m - 1) * (D + (m - 1) * dlt q A) :=
    le_trans hdetdeg (Nat.mul_le_mul_right _ (by omega))
  have halo : Mp.det.natDegree + N₁ + (m - 1) ≤ m * D
      + ((m - 1) + (m - 1) * (m - 1) * dlt q A + N₁ + m) := by
    have h5 : (m - 1) * (D + (m - 1) * dlt q A)
        = (m - 1) * D + (m - 1) * (m - 1) * dlt q A := by
      rw [Nat.mul_add, ← Nat.mul_assoc]
    have h6 : (m - 1) * D ≤ m * D := Nat.mul_le_mul_right _ (by omega)
    omega
  calc R.order.toNat
      ≤ Mp.det.natDegree + N₁ + (m - 1) := by omega
    _ ≤ m * D + ((m - 1) + (m - 1) * (m - 1) * dlt q A + N₁ + m) := halo


/-- **Shidlovsky's lemma, one variable** (`D`-closed case, `ε = 0`). -/
theorem one_var (m : ℕ) (f : Fin m → PowerSeries ℚ)
    (hpi : Submission.CDTPlan.PolyIndependent f) (hdc : Submission.CDTPlan.DClosed f) :
    ∃ C : ℕ, ∀ (D : ℕ) (P : Fin m → Polynomial ℚ),
      (∀ i, (P i).degree < (D : WithBot ℕ)) →
      (∑ i, (P i : PowerSeries ℚ) * f i) ≠ 0 →
      (∑ i, (P i : PowerSeries ℚ) * f i).order ≤ (m * D + C : ℕ∞) := by
  classical
  obtain ⟨q, hq, A, hrel⟩ := hdc
  obtain ⟨N, hN⟩ := lang24rat_clear m q A hq
  obtain ⟨C₂, hC₂⟩ := caseB m q A f hq hpi hrel N hN
  refine ⟨(m * dlt q A * m + m + Finset.univ.sup (fun i => (f i).order.toNat)) + C₂, ?_⟩
  intro D P hP hRne
  have hP' : DegLT P D := (DegLT_iff_degree P D).mpr hP
  by_cases hLI : LinearIndependent (RatFunc ℚ)
      (fun k : Fin m => (fun i => ((orbit q A P k) i : RatFunc ℚ)))
  · refine le_trans (case_det m q A f hpi hrel P D hP' hRne hLI) ?_
    rw [Nat.cast_add, Nat.cast_mul]
    exact add_le_add (le_refl _)
      (ENat.natCast_le_natCast.mpr (Nat.le_add_right _ _))
  · refine le_trans (hC₂ D P hP' hRne hLI) ?_
    rw [Nat.cast_add]
    exact add_le_add (le_refl _)
      (ENat.natCast_le_natCast.mpr (Nat.le_add_left _ _))

end Work.ZeroEst
