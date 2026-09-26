import Mathlib
import Submission.Work.SG.SGRepDefs
import Submission.Work.SG.RepCoh_cz
import Submission.Work.SG.ApplyBDefs
import Submission.Work.SG.cobstepAux.applyB_cong3
import Submission.Work.SG.cobstepAux.dvd_ediv_real

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem
open scoped Matrix

/-!
# `RepCoh_cobstep`: the coboundary step of the cohomology classification

Given the integral cocycle numerator `z` of the averaged cocycle `τ₀ = τ + s₀ - A s₀`
(`z i = n · τ₀(e i)`, hypothesis `hz`), the `applyB` representative values (`hB1`), a vector `σ`
with `n ∣ (1 - g)σ` for every generator (`hσ`), the coboundary congruence for `σ`
(`hσcob`, `hcz1`), the averaged cocycle of the class `j` is integrally equivalent to the
cocycle read off the `h`-th `H¹` representative, with translation `-σ/n²`.

The mathematical content is the chain

  `Aᵢ - zᵢ + czᵢ ≡ 0 (mod n)`,  `Aᵢ = applyB(B[i], reps[h])`,  `czᵢ = (1 - eᵢ)σ / n`,

obtained from `n ∣ zᵢ - applyB(B[i], yvec z)` (`hB1`), `n ∣ czᵢ - applyB(B[i], yvec cz)` (`hcz1`)
and `yvec z ≡ reps[h] + yvec cz (mod n)` (`hσcob`) by the three-term congruence of `applyB`
(`cobstepAux.applyB_cong3`).  Dividing by `n²` and using `n ∣ (1 - eᵢ)σ` turns this into the real
identity `τ₀(eᵢ) = applyB(B[i], reps[h])/n + s - eᵢ s (mod ℤ³)` with `s = -σ/n²`
(`cobstepAux.dvd_ediv_real`), which is clause 2 of `IntEquiv` for `U = 1`.
-/

private theorem cob_toFun_sub (u v : Data.V3) : (Data.V3.sub u v).toFun = u.toFun - v.toFun := by
  funext c; fin_cases c <;> rfl

private theorem cob_ediv_coord (u : Data.V3) (m : ℤ) (c : Fin 3) :
    (Data.V3.ediv u m).toFun c = u.toFun c / m := by
  fin_cases c <;> rfl

private theorem cob_toFun_ediv (u : Data.V3) (m : ℤ) :
    (Data.V3.ediv u m).toFun = fun c => u.toFun c / m := by
  funext c; fin_cases c <;> rfl

private theorem cob_intVec_mat (A : Data.M3) (w : Data.V3) :
    ((A.toIMat).map (Int.cast : ℤ → ℝ)).mulVec (intVec w.toFun)
      = intVec (Data.M3.mulV A w).toFun := by
  funext c
  fin_cases c <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Data.M3.toIMat, Data.M3.mulV,
      Data.V3.toFun, intVec]

private theorem cob_bridge_s (A : Data.M3) (w : Data.V3) (m : ℕ) :
    ((A.toIMat).map (Int.cast : ℤ → ℝ)).mulVec (fun c => -((w.toFun c : ℝ) / (m : ℝ) ^ 2))
      = fun c => -(((Data.M3.mulV A w).toFun c : ℝ) / (m : ℝ) ^ 2) := by
  have h1 : (fun c : Fin 3 => -((w.toFun c : ℝ) / (m : ℝ) ^ 2))
      = (-(1 / (m : ℝ) ^ 2)) • intVec w.toFun := by
    funext c; simp only [intVec, Pi.smul_apply, smul_eq_mul]; ring
  rw [h1, Matrix.mulVec_smul, cob_intVec_mat]
  funext c
  simp only [intVec, Pi.smul_apply, smul_eq_mul]; ring

theorem RepCoh_cobstep (j : Fin 73) {τ : IMat → Fin 3 → ℝ} {z : ℕ → Fin 3 → ℤ}
    (hz : ∀ i, i < Work.SG.RC.N j → ∀ c,
      (z i c : ℝ) = (Work.SG.RC.N j : ℝ) * Work.SG.RC.tau0 j τ (Work.SG.RC.e j i) c)
    {h : ℕ} (hh : h < (Work.SG.RC.Cd j).reps.length)
    (hB1 : ∀ i, i < Work.SG.RC.N j → Data.V3.dvd ((Work.SG.RC.Ad j).n)
      (Data.V3.sub (CZ.ofFun (z i))
        (Data.applyB ((Data.bmats (Work.SG.RC.Ad j)).getD i []) (Work.SG.RC.yvec j z))) = true)
    {σ : Data.V3}
    (hσ : ∀ g, g < Work.SG.RC.KK j → Data.V3.dvd ((Work.SG.RC.Ad j).n)
      (Data.V3.sub σ (Data.M3.mulV (Work.SG.RC.gMt j g) σ)) = true)
    (hσcob : ∀ q, q < Work.SG.RC.N3 j →
      ((Work.SG.RC.vsub (Work.SG.RC.yvec j z) ((Work.SG.RC.Cd j).reps.getD h [])).getD q 0
        - (Work.SG.RC.yvec j (Work.SG.RC.cz j σ)).getD q 0) % ((Work.SG.RC.Ad j).n : ℤ) = 0)
    (hcz1 : ∀ i, i < Work.SG.RC.N j → Data.V3.dvd ((Work.SG.RC.Ad j).n)
      (Data.V3.sub (CZ.ofFun (Work.SG.RC.cz j σ i))
        (Data.applyB ((Data.bmats (Work.SG.RC.Ad j)).getD i []) (Work.SG.RC.yvec j (Work.SG.RC.cz j σ)))) = true) :
    IntEquiv (arithRep j) (Work.SG.RC.tauOnP j (fun i => Work.SG.RC.tau0 j τ (Work.SG.RC.e j i)))
      (arithRep j) (Work.SG.RC.tauOnP j (Work.SG.RC.srcZ j h)) 1
      (fun c => -((σ.toFun c) / ((Work.SG.RC.Ad j).n : ℝ) ^ 2)) := by
  have hrn : ((RC.Ad j).n : ℝ) ≠ 0 := by
    have hp := RC.N_pos j
    exact_mod_cast hp.ne'
  have hrep_len : ((RC.Cd j).reps.getD h []).length = RC.N3 j := by
    rw [List.getD_eq_getElem _ _ hh]
    exact (RC.Cd_reps_red j _ (List.getElem_mem hh)).1
  have hylen : (RC.yvec j z).length = 3 * RC.KK j := RC.yvec_len j z
  have hrlen : ((RC.Cd j).reps.getD h []).length = 3 * RC.KK j := hrep_len
  have hclen : (RC.yvec j (RC.cz j σ)).length = 3 * RC.KK j := RC.yvec_len j (RC.cz j σ)
  have h1inv : (1 : IMat)⁻¹ = 1 := Matrix.inv_eq_right_inv (by simp)
  have hone : ((1 : IMat).map (Int.cast : ℤ → ℝ)) = 1 := by
    ext p q
    fin_cases p <;> fin_cases q <;> simp [Matrix.map_apply]
  -- the key divisibility
  have hkey : ∀ i, i < RC.N j → ∀ c : Fin 3, ((RC.Ad j).n : ℤ) ∣
      (Data.applyB ((Data.bmats (RC.Ad j)).getD i []) ((RC.Cd j).reps.getD h [])).toFun c
        - z i c + RC.cz j σ i c := by
    intro i hi c
    have hi' : i < (RC.Ad j).n := hi
    have hBlen : ((Data.bmats (RC.Ad j)).getD i []).length = RC.KK j := ad_bmats_rowlen j i hi'
    have hcong : ∀ q, q < 3 * RC.KK j → ((RC.Ad j).n : ℤ) ∣
        (RC.yvec j z).getD q 0 - ((RC.Cd j).reps.getD h []).getD q 0
          - (RC.yvec j (RC.cz j σ)).getD q 0 := by
      intro q hq
      have hq3 : q < RC.N3 j := hq
      have hmod := hσcob q hq3
      have hv := RC.vsub_getD (RC.yvec_length j z) hrep_len q hq3
      rw [hv] at hmod
      exact Int.dvd_of_emod_eq_zero hmod
    have hcong3 := cobstepAux.applyB_cong3 ((Data.bmats (RC.Ad j)).getD i []) ((RC.Ad j).n)
      hBlen hylen hrlen hclen hcong c
    have hd1 : ((RC.Ad j).n : ℤ) ∣ z i c
        - (Data.applyB ((Data.bmats (RC.Ad j)).getD i []) (RC.yvec j z)).toFun c := by
      have hh1 := (RC.dvd_iff_toFun ((RC.Ad j).n)
        (Data.V3.sub (CZ.ofFun (z i))
          (Data.applyB ((Data.bmats (RC.Ad j)).getD i []) (RC.yvec j z)))).mp (hB1 i hi) c
      rwa [cob_toFun_sub, CZ.ofFun_toFun, Pi.sub_apply] at hh1
    have hd2 : ((RC.Ad j).n : ℤ) ∣ RC.cz j σ i c
        - (Data.applyB ((Data.bmats (RC.Ad j)).getD i []) (RC.yvec j (RC.cz j σ))).toFun c := by
      have hh2 := (RC.dvd_iff_toFun ((RC.Ad j).n)
        (Data.V3.sub (CZ.ofFun (RC.cz j σ i))
          (Data.applyB ((Data.bmats (RC.Ad j)).getD i []) (RC.yvec j (RC.cz j σ))))).mp (hcz1 i hi) c
      rwa [cob_toFun_sub, CZ.ofFun_toFun, Pi.sub_apply] at hh2
    have hsum : ((RC.Ad j).n : ℤ) ∣
        (Data.applyB ((Data.bmats (RC.Ad j)).getD i []) (RC.yvec j z)).toFun c
          - (Data.applyB ((Data.bmats (RC.Ad j)).getD i []) ((RC.Cd j).reps.getD h [])).toFun c
          - (Data.applyB ((Data.bmats (RC.Ad j)).getD i []) (RC.yvec j (RC.cz j σ))).toFun c :=
      hcong3
    have : (Data.applyB ((Data.bmats (RC.Ad j)).getD i []) ((RC.Cd j).reps.getD h [])).toFun c
        - z i c + RC.cz j σ i c
        = - (z i c - (Data.applyB ((Data.bmats (RC.Ad j)).getD i []) (RC.yvec j z)).toFun c)
          + (RC.cz j σ i c - (Data.applyB ((Data.bmats (RC.Ad j)).getD i [])
              (RC.yvec j (RC.cz j σ))).toFun c)
          - ((Data.applyB ((Data.bmats (RC.Ad j)).getD i []) (RC.yvec j z)).toFun c
              - (Data.applyB ((Data.bmats (RC.Ad j)).getD i []) ((RC.Cd j).reps.getD h [])).toFun c
              - (Data.applyB ((Data.bmats (RC.Ad j)).getD i [])
                  (RC.yvec j (RC.cz j σ))).toFun c) := by ring
    rw [this]
    exact dvd_sub (dvd_add (dvd_neg.mpr hd1) hd2) hsum
  -- the `(1 - e_i)σ` divisibility for every element
  have h2lemma : ∀ i, i < RC.N j → ∀ c : Fin 3,
      σ.toFun c - (Data.M3.mulV (RC.eM j i) σ).toFun c
        = ((RC.Ad j).n : ℤ) * RC.cz j σ i c := by
    intro i hi c
    have hdiv : ((RC.Ad j).n : ℤ) ∣ σ.toFun c - (Data.M3.mulV (RC.eM j i) σ).toFun c := by
      have hh := (RC.dvd_iff_toFun ((RC.Ad j).n)
        (Data.V3.sub σ (Data.M3.mulV (RC.eM j i) σ))).mp (CzAux.dvd_eM j σ hσ i hi) c
      rwa [cob_toFun_sub, Pi.sub_apply] at hh
    have hcz : RC.cz j σ i c
        = (σ.toFun c - (Data.M3.mulV (RC.eM j i) σ).toFun c) / ((RC.Ad j).n : ℤ) := by
      have hsub := congrFun (cob_toFun_sub σ (Data.M3.mulV (RC.eM j i) σ)) c
      show (Data.V3.ediv (Data.V3.sub σ (Data.M3.mulV (RC.eM j i) σ)) ((RC.Ad j).n)).toFun c
        = (σ.toFun c - (Data.M3.mulV (RC.eM j i) σ).toFun c) / ((RC.Ad j).n : ℤ)
      rw [cob_ediv_coord, hsub]
      rfl
    rw [hcz]
    exact (Int.mul_ediv_cancel' hdiv).symm
  -- `tau0 = z / n`
  have hz' : ∀ i, i < RC.N j → ∀ c : Fin 3,
      RC.tau0 j τ (RC.e j i) c = (z i c : ℝ) / ((RC.Ad j).n : ℝ) := by
    intro i hi c
    have hh := hz i hi c
    rw [show (RC.N j : ℝ) = ((RC.Ad j).n : ℝ) from rfl] at hh
    rw [eq_div_iff_mul_eq hrn, mul_comm]
    exact hh.symm
  refine ⟨?_, ?_⟩
  · intro A
    constructor
    · intro hA
      exact ⟨A, hA, by rw [h1inv, Matrix.one_mul, Matrix.mul_one]⟩
    · rintro ⟨B, hB, hAB⟩
      rw [hAB, h1inv, Matrix.one_mul, Matrix.mul_one]
      exact hB
  · intro B hB
    obtain ⟨i, hi, hBi⟩ := (RC.mem_arithRep_iff j B).mp hB
    subst hBi
    refine ⟨fun c => ((Data.applyB ((Data.bmats (RC.Ad j)).getD i [])
        ((RC.Cd j).reps.getD h [])).toFun c - z i c + RC.cz j σ i c) / ((RC.Ad j).n : ℤ), ?_⟩
    rw [h1inv, Matrix.one_mul, Matrix.mul_one, hone, Matrix.one_mulVec]
    rw [RC.tauOnP_e j (RC.srcZ j h) i hi,
      RC.tauOnP_e j (fun i => RC.tau0 j τ (RC.e j i)) i hi]
    funext c
    simp only [Pi.add_apply, Pi.sub_apply, RC.intVec_apply]
    have hsrc : RC.srcZ j h i c = ((Data.applyB ((Data.bmats (RC.Ad j)).getD i [])
        ((RC.Cd j).reps.getD h [])).toFun c : ℝ) / ((RC.Ad j).n : ℝ) := rfl
    have hs : (fun d : Fin 3 => -((σ.toFun d) / ((RC.Ad j).n : ℝ) ^ 2)) c
        = -((σ.toFun c : ℝ) / ((RC.Ad j).n : ℝ) ^ 2) := rfl
    have hMs : (((RC.e j i).map (Int.cast : ℤ → ℝ)).mulVec
          (fun d : Fin 3 => -((σ.toFun d) / ((RC.Ad j).n : ℝ) ^ 2))) c
        = -(((Data.M3.mulV (RC.eM j i) σ).toFun c : ℝ) / ((RC.Ad j).n : ℝ) ^ 2) := by
      rw [show RC.e j i = (RC.eM j i).toIMat from rfl]
      exact congrFun (cob_bridge_s (RC.eM j i) σ ((RC.Ad j).n)) c
    rw [hsrc, hMs, hz' i hi c]
    rw [cobstepAux.dvd_ediv_real ((RC.Ad j).n) (RC.N_pos j)
      ((Data.applyB ((Data.bmats (RC.Ad j)).getD i []) ((RC.Cd j).reps.getD h [])).toFun c)
      (z i c) (RC.cz j σ i c) (σ.toFun c) ((Data.M3.mulV (RC.eM j i) σ).toFun c)
      (hkey i hi c) (h2lemma i hi c)]
    ring

end Work.SG
