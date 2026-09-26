import Mathlib
import Submission.Work.SG.SGRepDefs
import Submission.Work.SG.RepCoh_applyB
import Submission.Work.SG.RepCoh_elim
import Submission.Work.SG.RepCoh_reduceBl
import Submission.Work.SG.RepCoh_reps
import Submission.Work.SG.RepCoh_cz
import Submission.Work.SG.RepCoh_zrec
import Submission.Work.SG.RepCoh_conj
import Submission.Work.SG.RepCoh_cobsig
import Submission.Work.SG.RepCoh_sgTau
import Submission.Work.SG.RepCoh_cobstep

/-!
# Cocycle classification (`exists_sgRep_of_cocycle`)

Every cocycle `τ` on the `j`-th arithmetic representative `arithRep j` is integrally equivalent,
through a `det 1` element of its normaliser, to one of the listed space-group representatives of
that class (Zassenhaus's classification of space groups, certified by the kernel-checked
cohomology certificates of `Submission/Work/SG/Data/CohomTab.lean`).
-/

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem
open scoped Matrix BigOperators

namespace RC

/-! ## Auxiliary matrix and list facts used by the assembly -/

theorem tau0_cocycle (j : Fin 73) (τ : IMat → Fin 3 → ℝ) (hτ : IsIntCocycle (arithRep j) τ) :
    IsIntCocycle (arithRep j) (tau0 j τ) := by
  intro A hA B hB
  obtain ⟨m, hm⟩ := hτ A hA B hB
  refine ⟨m, ?_⟩
  funext c
  have hmc : τ (A * B) c = τ A c + ((castM A).mulVec (τ B)) c + (m c : ℝ) := by
    have h := congrFun hm c
    simpa only [castM, Pi.add_apply, intVec_apply] using h
  have hmul : ((castM A).mulVec (tau0 j τ B)) c
      = ((castM A).mulVec (τ B)) c + ((castM A).mulVec (s0 j τ)) c
        - ((castM A).mulVec ((castM B).mulVec (s0 j τ))) c := by
    have h1 : tau0 j τ B = τ B + s0 j τ - (castM B).mulVec (s0 j τ) := by
      funext c
      simp only [tau0, Pi.add_apply, Pi.sub_apply]
    rw [h1]
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Pi.add_apply, Pi.sub_apply]
  have h2 : ((castM (A * B)).mulVec (s0 j τ)) c
      = ((castM A).mulVec ((castM B).mulVec (s0 j τ))) c := by
    rw [castM_mul, Matrix.mulVec_mulVec]
  simp only [castM, tau0, Pi.add_apply, Pi.sub_apply, intVec_apply] at *
  rw [h2, hmc, hmul]
  ring

theorem sgArith_tgtK (j : Fin 73) (h : ℕ) (hh : h < (Cd j).reps.length) :
    sgArith (tgtK j h) = j := by
  have hclass := Cd_tgt_class j h hh
  have hklt := Cd_tgt_k j h hh
  have hval : (sgArith (tgtK j h)).val = j.val := by
    simp only [sgArith, tgtK, dif_pos hh, Data.repClass] at hclass ⊢
    rw [hclass, Nat.mod_eq_of_lt j.isLt]
  exact Fin.ext hval

theorem tgt_Umul (j : Fin 73) (h : ℕ) (hh : h < (Cd j).reps.length) :
    (Uc j h).toIMat * ((Cd j).targets.getD h default).Uinv.toIMat = 1 := by
  have hchk := Cd_tgt_chk j h hh
  simp only [Data.ConjCert.chk, Bool.and_eq_true, beq_iff_eq] at hchk
  have h1 : Data.M3.mul (Uc j h) ((Cd j).targets.getD h default).Uinv = Data.M3.one :=
    hchk.1.1
  rw [← CZ.toIMat_mul, h1, CZ.toIMat_one]

theorem castM_mulVec_add (U : IMat) (x y : Fin 3 → ℝ) :
    (castM U).mulVec (x + y) = (castM U).mulVec x + (castM U).mulVec y :=
  Matrix.mulVec_add _ _ _

theorem castM_mulVec_sub (U : IMat) (x y : Fin 3 → ℝ) :
    (castM U).mulVec (x - y) = (castM U).mulVec x - (castM U).mulVec y :=
  Matrix.mulVec_sub _ _ _

theorem castM_mulVec_intVec (U : IMat) (m : Fin 3 → ℤ) :
    (castM U).mulVec (intVec m) = intVec (U.mulVec m) := by
  have hU : U.mulVec m = fun i => U i 0 * m 0 + U i 1 * m 1 + U i 2 * m 2 := by
    funext i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  rw [hU]
  funext c
  simp only [castM, Matrix.mulVec, dotProduct, Fin.sum_univ_three, intVec, Matrix.map_apply,
    Pi.add_apply]
  push_cast
  ring

theorem inv_mul_self_of_mul_inv {U V : IMat} (h : U * V = 1) : U⁻¹ * U = 1 := by
  have hu : IsUnit U := ⟨Units.mk U V h (mul_eq_one_comm.mp h), rfl⟩
  exact Matrix.nonsing_inv_mul U ((Matrix.isUnit_iff_isUnit_det U).mp hu)

theorem castM_conj {U B : IMat} (hU : U⁻¹ * U = 1) (x : Fin 3 → ℝ) :
    (castM U).mulVec ((castM B).mulVec x)
      = (castM (U * B * U⁻¹)).mulVec ((castM U).mulVec x) := by
  have h2 : castM U⁻¹ * castM U = 1 := by rw [← castM_mul, hU, castM_one]
  have h1 : castM U * castM B * castM U⁻¹ * castM U = castM U * castM B := by
    rw [Matrix.mul_assoc, h2, Matrix.mul_one]
  have h3 : castM (U * B * U⁻¹) = castM U * castM B * castM U⁻¹ := by
    rw [castM_mul, castM_mul]
  simp only [h3, Matrix.mulVec_mulVec, h1]

theorem mul_self_inv_of_mul_inv {U V : IMat} (h : U * V = 1) : U * U⁻¹ = 1 := by
  have hu : IsUnit U := ⟨Units.mk U V h (mul_eq_one_comm.mp h), rfl⟩
  exact Matrix.mul_nonsing_inv U ((Matrix.isUnit_iff_isUnit_det U).mp hu)

theorem mapCast_eq_castM (X : IMat) : X.map (Int.cast : ℤ → ℝ) = castM X := rfl

theorem intVec_add (m n : Fin 3 → ℤ) : intVec (m + n) = intVec m + intVec n := by
  funext c
  simp [intVec]

theorem tau0_eq (j : Fin 73) (τ : IMat → Fin 3 → ℝ) (A : IMat) :
    tau0 j τ A = τ A + s0 j τ - (castM A).mulVec (s0 j τ) := by
  funext c
  simp only [tau0, Pi.add_apply, Pi.sub_apply]

/-- The rows of the relation matrix all have length `N3`. -/
theorem rowlen_flat (blk : List Data.M3) (r : ℕ) :
    (blk.flatMap (fun A => ((Data.M3.rows A).getD r Data.V3.zero).toList)).length
      = 3 * blk.length := by
  induction blk with
  | nil => simp
  | cons A t ih =>
      have h3 : (((Data.M3.rows A).getD r Data.V3.zero).toList).length = 3 := by
        cases Data.M3.rows A |>.getD r Data.V3.zero
        simp [Data.V3.toList]
      rw [List.flatMap_cons, List.length_append, ih, List.length_cons, h3]
      ring

theorem relRows_rowlen (j : Fin 73) :
    ∀ row ∈ Data.relRows (Ad j), row.length = N3 j := by
  intro row hrow
  simp only [Data.relRows, List.mem_flatMap, List.mem_range, List.mem_map] at hrow
  obtain ⟨g', -, i, -, r, -, heq⟩ := hrow
  rw [← heq, rowlen_flat]
  simp [N3, KK]

end RC

open RC

/-- Cocycle classification (Zassenhaus, certified): every cocycle on the `j`-th arithmetic
representative is integrally equivalent, by an element of determinant `1` of its normaliser, to
one of the listed space-group representatives of that class. -/
theorem exists_sgRep_of_cocycle (j : Fin 73) {τ : IMat → Fin 3 → ℝ}
    (hτ : IsIntCocycle (arithRep j) τ) :
    ∃ k : Fin 230, sgArith k = j ∧ ∃ U : IMat, U.det = 1 ∧ ∃ s : Fin 3 → ℝ,
      IntEquiv (arithRep j) τ (arithRep j) (sgTau k) U s := by
  obtain ⟨z, hz0, hzspec⟩ := exists_avgZ j hτ
  have hnR : ((Ad j).n : ℝ) ≠ 0 := by
    have h2 : (0 : ℕ) < (Ad j).n := N_pos j
    positivity
  have hnpos : 0 < ((Ad j).n : ℤ) := by
    have h2 : (0 : ℕ) < (Ad j).n := N_pos j
    exact_mod_cast h2
  have hint : ∀ i, i < N j → ∀ c,
      tau0 j τ (e j i) c = (z i c : ℝ) / ((Ad j).n : ℝ) := by
    intro i hi c
    have h := hzspec i hi c
    have h2 : (z i c : ℝ) / ((Ad j).n : ℝ) = tau0 j τ (e j i) c := by
      rw [h, show (N j : ℝ) = ((Ad j).n : ℝ) from rfl, mul_div_cancel_left₀ _ hnR]
    exact h2.symm
  have hcoc0 : IsIntCocycle (arithRep j) (tau0 j τ) := tau0_cocycle j τ hτ
  have hrec := RepCoh_zrec j (tau := tau0 j τ) hcoc0 hint
  obtain ⟨hB1, hB2⟩ := RepCoh_applyB j (z := z) hz0 hrec
  -- elimination
  have hwc : ∀ c, c < N3 j → ∀ q, c < q → q < N3 j →
      (wcComb (N3 j) (Data.relRows (Ad j)) (Cd j).wc c).getD q 0 % ((Ad j).n : ℤ) = 0 := by
    intro c hc q hcq hq
    rw [← wcC_eq j c]
    exact Cd_wc_hi j c hc q hq hcq
  have hwcp : ∀ c, c < N3 j →
      ((wcComb (N3 j) (Data.relRows (Ad j)) (Cd j).wc c).getD c 0
        - ((Ad j).n : ℤ) / ((Cd j).H.getD c []).getD c 1) % ((Ad j).n : ℤ) = 0 := by
    intro c hc
    rw [← wcC_eq j c]
    exact Cd_wc_piv j c hc
  obtain ⟨t, ht⟩ := RepCoh_elim (n := ((Ad j).n : ℤ)) (M := N3 j)
    (R := Data.relRows (Ad j)) (H := (Cd j).H) (wc := (Cd j).wc) hnpos
    (Cd_H_len j) (Cd_H_rowlen j) (fun c hc => (echAt_iff c _).mp (Cd_H_ech j c hc))
    (Cd_H_dvd j) (Cd_H_ann j) (relRows_rowlen j) (Cd_wc_len j) hwc hwcp (y := yvec j z) hB2
  -- pad `t` to length `N3`
  have htlen : ((List.range ((Cd j).H.length)).map (fun c => t.getD c 0)).length = N3 j := by
    rw [List.length_map, List.length_range, Cd_H_len]
  have hcd : ∀ q, q < N3 j →
      ((yvec j z).getD q 0
        - linC ((Cd j).H) ((List.range ((Cd j).H.length)).map (fun c => t.getD c 0)) q)
        % ((Ad j).n : ℤ) = 0 := by
    intro q hq
    rw [linC_getD_map]
    exact ht q hq
  -- the certified reduction package
  obtain ⟨hmain, hvadd, hvz, hvsub⟩ := RepCoh_reduceBl_corrected
  obtain ⟨hidem, hsubspan, hreduced, hredcong, hzerospan⟩ :=
    hmain (N3 j) (Cd j).Bl (Cd_Bl_len j)
      (fun c hc => by rw [BlR_getD]; exact Cd_Bl_rowlen j c hc)
      (fun c hc => by rw [BlR_getD]; exact (echAt_iff c _).mp (Cd_Bl_ech j c hc))
  have hnmem : ∀ q, q < N3 j → InSpan (BlR (Cd j).Bl) (N3 j) (vunit ((Ad j).n) (N3 j) q) := by
    intro q hq
    exact hzerospan _ (vunit_length _ _ _) (Bl_nunit j q hq)
  obtain ⟨h, hh, hInSpan⟩ := RepCoh_reps j hnmem
    (fun {x y} hx hy hxy => hredcong x y hx hy hxy) (yvec j z)
    ((List.range ((Cd j).H.length)).map (fun c => t.getD c 0)) (yvec_length j z) htlen hcd
  obtain ⟨lam, hlam⟩ := hInSpan
  -- the coboundary
  obtain ⟨σ, hσ, hσcob⟩ := RepCoh_cobsig j h hh (yvec j z) lam (yvec_length j z) hlam
  obtain ⟨hcz0, hczrec⟩ := RepCoh_cz j σ hσ
  have hcz0' : Data.V3.dvd ((Ad j).n) (CZ.ofFun (cz j σ 0)) = true := by
    rw [hcz0]; rfl
  obtain ⟨hcz1, -⟩ := RepCoh_applyB j (z := cz j σ) hcz0' hczrec
  have hstep := RepCoh_cobstep j hzspec hh hB1 hσ hσcob hcz1
  have hconj := RepCoh_conj j h hh
  have hU := inv_mul_self_of_mul_inv (tgt_Umul j h hh)
  have hU2 : (Uc j h).toIMat * (Uc j h).toIMat⁻¹ = 1 := mul_self_inv_of_mul_inv (tgt_Umul j h hh)
  -- the final assembly
  set s1 : Fin 3 → ℝ := fun c => -(σ.toFun c / ((Ad j).n : ℝ) ^ 2) with hs1
  set s2 : Fin 3 → ℝ := fun c => (sigc j h).toFun c / ((Ad j).n : ℝ) ^ 2 with hs2
  refine ⟨tgtK j h, sgArith_tgtK j h hh, (Uc j h).toIMat,
    (CZ.toIMat_det (Uc j h)).trans (Cd_tgt_det j h hh), ?_⟩
  refine ⟨fun c => ((castM (Uc j h).toIMat *ᵥ s0 j τ) c + (castM (Uc j h).toIMat *ᵥ s1) c + s2 c), ?_⟩
  constructor
  · exact hconj.1
  · intro B hB
    obtain ⟨i, hi, rfl⟩ := (mem_arithRep_iff j B).mp hB
    have hB'mem : (Uc j h).toIMat * e j i * ((Uc j h).toIMat)⁻¹ ∈ arithRep j :=
      (hconj.1 _).mpr ⟨e j i, e_mem j i hi, rfl⟩
    obtain ⟨i', hi', hi'eq⟩ := (mem_arithRep_iff j _).mp hB'mem
    obtain ⟨m2, hm2⟩ := hconj.2 (e j i) (e_mem j i hi)
    obtain ⟨m1, hm1⟩ := hstep.2 (e j i) (e_mem j i hi)
    rw [← hi'eq] at hm2
    rw [tauOnP_e j (tgtZ j h) i' hi', tauOnP_e j (srcZ j h) i hi] at hm2
    simp only [Matrix.mul_one, Matrix.one_mul, inv_one] at hm1
    rw [tauOnP_e j (srcZ j h) i hi, tauOnP_e j (fun i => tau0 j τ (e j i)) i hi] at hm1
    have hbr : sgTau (tgtK j h) (e j i') = tgtZ j h i' :=
      RepCoh_sgTau j (tgtK j h) (sgArith_tgtK j h hh) i' hi'
    refine ⟨(Uc j h).toIMat.mulVec m1 + m2, ?_⟩
    have hsdef : ((castM (Uc j h).toIMat *ᵥ s0 j τ) + (castM (Uc j h).toIMat *ᵥ s1) + s2 : Fin 3 → ℝ)
        = fun c => (castM (Uc j h).toIMat *ᵥ s0 j τ) c + (castM (Uc j h).toIMat *ᵥ s1) c
            + s2 c := rfl
    rw [← hi'eq, hbr, hm2, hm1, tau0_eq j τ (e j i), ← hsdef]
    simp only [← hi'eq, mapCast_eq_castM, hU2, castM_one, Matrix.map_one, Matrix.one_mulVec,
      Matrix.one_mul, Matrix.mul_one, Matrix.mulVec_mulVec,
      castM_mulVec_add, castM_mulVec_sub, castM_mulVec_intVec, castM_conj hU,
      Matrix.mulVec_add, Matrix.mulVec_sub, intVec_add]
    ring

end Work.SG
