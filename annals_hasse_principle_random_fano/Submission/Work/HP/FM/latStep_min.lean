import Mathlib
import Submission.Work.HP.FM.RecDefs

set_option autoImplicit false
noncomputable section
open Finset
open scoped BigOperators

namespace Work.HP.FM

section Helpers

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Basic facts about `latMin` -/

omit [DecidableEq ι] in
lemma lsm_latMin_nonneg {R : ℕ} (Φ : LatMap (ι := ι) R) (i : ℕ) : 0 ≤ latMin Φ i := by
  rw [latMin]
  by_cases h : ({r : ℝ | 0 ≤ r ∧ ∃ f : Fin i → (Fin R → ℤ), LinearIndependent ℤ f ∧
      ∀ j, ‖Φ (fun k => (f j k : ℝ))‖ ≤ r} : Set ℝ).Nonempty
  · exact le_csInf h (fun r hr => hr.1)
  · rw [Set.not_nonempty_iff_eq_empty.mp h, Real.sInf_empty]

omit [DecidableEq ι] in
lemma lsm_latMin_one_le {R : ℕ} (Φ : LatMap (ι := ι) R) {w : Fin R → ℤ} (hw : w ≠ 0) :
    latMin Φ 1 ≤ ‖Φ (fun k => (w k : ℝ))‖ := by
  rw [latMin]
  refine csInf_le ⟨0, fun r hr => hr.1⟩ ?_
  refine ⟨norm_nonneg _, fun _ => w, ?_, fun _ => le_rfl⟩
  rw [linearIndependent_unique_iff]
  exact hw

lemma lsm_sq_le_sq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (h : a ≤ b) : a^2 ≤ b^2 := by
  rw [sq_le_sq, abs_of_nonneg ha, abs_of_nonneg (ha.trans h)]
  exact h

/-! ## Linearity and injectivity of the step map -/

lemma lsm_step_sum {R : ℕ} (D : RecData R ι) (a : Fin (R - 1) → ℝ) :
    D.step a = projU D.p (D.Φ (∑ j, a j • (fun k => (D.v j k : ℝ)))) := by
  rw [RecData.step, latStep_apply, RecData.p]
  rw [map_sum, map_sum]
  simp only [map_smul]

lemma lsm_p_ne_zero {R : ℕ} (D : RecData R ι) : D.p ≠ 0 := by
  intro h
  have h' : (fun j => (D.u j : ℝ)) = 0 := by
    apply D.Φ_inj
    rw [RecData.p] at h
    rw [h, map_zero]
  have hu0 : D.u = 0 := by
    funext j
    have hj := congrFun h' j
    simp only [Pi.zero_apply] at hj
    exact_mod_cast hj
  exact D.u_ne hu0

lemma lsm_step_injective {R : ℕ} (D : RecData R ι) : Function.Injective D.step := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  rw [lsm_step_sum] at ha
  rw [projU_eq_zero_iff D.p (lsm_p_ne_zero D)] at ha
  rw [Submodule.mem_span_singleton] at ha
  obtain ⟨c, hc⟩ := ha
  have hc2 : (∑ j, a j • (fun k => (D.v j k : ℝ))) = c • (fun k => (D.u k : ℝ)) := by
    apply D.Φ_inj
    rw [map_smul, ← RecData.p]
    exact hc.symm
  have hind : (-c) • (fun j => (D.u j : ℝ)) + ∑ i, a i • (fun j => (D.v i j : ℝ)) = 0 := by
    rw [hc2, neg_smul]
    exact neg_add_cancel _
  have := D.indep (-c, a) hind
  exact (Prod.ext_iff.mp this).2

/-! ## The lift bound -/

lemma lsm_lift_step {R : ℕ} (D : RecData R ι) (t : Fin (R - 1) → ℤ) :
    ∃ k : ℤ, ‖D.Φ (fun i => ((∑ j, t j • D.v j) i : ℝ)) + (k:ℝ) • D.p‖^2
      ≤ ‖D.step (fun j => (t j : ℝ))‖^2 + ‖D.p‖^2/4 := by
  set y : EuclideanSpace ℝ ι := D.Φ (fun i => ((∑ j, t j • D.v j) i : ℝ))
  set c : ℝ := (‖D.p‖^2)⁻¹ * inner ℝ y D.p
  refine ⟨-round c, ?_⟩
  have hdec : y = projU D.p y + c • D.p := by
    rw [projU_apply]; simp only [c]; abel
  have hz : D.step (fun j => (t j : ℝ)) = projU D.p y := by
    rw [RecData.step_cast]
  have hb : |c + ((-round c : ℤ) : ℝ)| ≤ 1/2 := by
    have : c + ((-round c : ℤ) : ℝ) = c - (round c : ℝ) := by push_cast; ring
    rw [this]; exact abs_sub_round c
  have key : y + (((-round c : ℤ)) : ℝ) • D.p
      = projU D.p y + (c + ((-round c:ℤ):ℝ)) • D.p := by
    conv_lhs => rw [hdec]
    rw [add_smul, add_assoc]
  rw [key, hz, norm_sq_add_smul']
  have hc2 : (c + ((-round c : ℤ) : ℝ))^2 ≤ (1/2:ℝ)^2 := by
    rw [sq_le_sq]; simpa using hb
  have hle : (c + ((-round c : ℤ) : ℝ))^2 * ‖D.p‖^2 ≤ (1/2:ℝ)^2 * ‖D.p‖^2 :=
    mul_le_mul_of_nonneg_right hc2 (sq_nonneg _)
  nlinarith [hle]

/-! ## Coordinate maps -/

def lsm_sigmaZ {R : ℕ} (v : Fin (R - 1) → (Fin R → ℤ)) :
    (Fin (R - 1) → ℤ) →ₗ[ℤ] (Fin R → ℤ) where
  toFun w := fun j => ∑ i, w i * v i j
  map_add' w w' := by
    funext j; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c w := by
    funext j; simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum, RingHom.id_apply]

lemma lsm_sigmaZ_eq_sum {R : ℕ} (v : Fin (R - 1) → (Fin R → ℤ)) (w : Fin (R - 1) → ℤ) :
    lsm_sigmaZ v w = ∑ i, w i • v i := by
  funext j
  simp only [lsm_sigmaZ, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

def lsm_TZ {R : ℕ} (u : Fin R → ℤ) (v : Fin (R - 1) → (Fin R → ℤ)) :
    (ℤ × (Fin (R - 1) → ℤ)) →ₗ[ℤ] (Fin R → ℤ) :=
  (LinearMap.toSpanSingleton ℤ (Fin R → ℤ) u).comp (LinearMap.fst ℤ ℤ (Fin (R - 1) → ℤ)) +
    (lsm_sigmaZ v).comp (LinearMap.snd ℤ ℤ (Fin (R - 1) → ℤ))

lemma lsm_TZ_apply {R : ℕ} (u : Fin R → ℤ) (v : Fin (R - 1) → (Fin R → ℤ))
    (a : ℤ) (w : Fin (R - 1) → ℤ) : lsm_TZ u v (a, w) = a • u + lsm_sigmaZ v w := by
  simp [lsm_TZ, LinearMap.toSpanSingleton_apply]

lemma lsm_psi_add_smul_u_eq_zero {R : ℕ} (D : RecData R ι) {t : Fin (R - 1) → ℤ} {m : ℤ}
    (h : (∑ l, t l • D.v l) + m • D.u = 0) : t = 0 := by
  have hcast0 : (fun j : Fin R => (((∑ l, t l • D.v l) + m • D.u) j : ℝ)) = 0 := by
    have h1 : (fun j : Fin R => (((∑ l, t l • D.v l) + m • D.u) j : ℝ))
        = (fun j => ((0 : Fin R → ℤ) j : ℝ)) :=
      congrArg (fun z : Fin R → ℤ => fun j => (z j : ℝ)) h
    rwa [show (fun j : Fin R => ((0 : Fin R → ℤ) j : ℝ)) = 0 from by funext j; simp] at h1
  have hsplit : (fun j : Fin R => (((∑ l, t l • D.v l) + m • D.u) j : ℝ))
      = (fun j => ((∑ l, t l • D.v l) j : ℝ)) + (m:ℝ) • (fun j => (D.u j : ℝ)) := by
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [hsplit, cast_sum_smul] at hcast0
  rw [add_comm] at hcast0
  have := D.indep (m, fun i => (t i : ℝ)) hcast0
  have ht : (fun i => (t i : ℝ)) = 0 := (Prod.ext_iff.mp this).2
  funext i
  have hi := congrFun ht i
  simp only [Pi.zero_apply] at hi
  exact_mod_cast hi

lemma lsm_Phi_cast_add_smul {R : ℕ} (D : RecData R ι) (t : Fin (R - 1) → ℤ) (m : ℤ) :
    D.Φ (fun kk => (((∑ l, t l • D.v l) + m • D.u) kk : ℝ))
      = D.Φ (fun kk => ((∑ l, t l • D.v l) kk : ℝ)) + (m:ℝ) • D.p := by
  have h : (fun kk => (((∑ l, t l • D.v l) + m • D.u) kk : ℝ))
      = (fun kk => ((∑ l, t l • D.v l) kk : ℝ)) + (m:ℝ) • (fun kk => (D.u kk : ℝ)) := by
    funext kk
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [h, map_add, map_smul]
  rfl

lemma lsm_cons_indep {R : ℕ} (D : RecData R ι) {j : ℕ} (f : Fin j → (Fin (R - 1) → ℤ))
    (hf : LinearIndependent ℤ f) (k : Fin j → ℤ) :
    LinearIndependent ℤ (Fin.cons D.u (fun i => (∑ l, f i l • D.v l) + k i • D.u)) := by
  have hTbij : Function.Bijective (lsm_TZ D.u D.v) := by
    have hfun : lsm_TZ D.u D.v = fun c : ℤ × (Fin (R - 1) → ℤ) =>
        c.1 • D.u + ∑ i, c.2 i • D.v i := by
      funext c; rw [lsm_TZ_apply, lsm_sigmaZ_eq_sum]
    rw [hfun]; exact D.bij
  have hφLI : LinearIndependent ℤ (Fin.cons (1, 0) (fun l : Fin j => (k l, f l))) := by
    rw [Fintype.linearIndependent_iff]
    intro d hd
    have hd2 : ∑ l : Fin j, d l.succ • f l = 0 := by
      have h := congrArg Prod.snd hd
      simpa [Fin.sum_univ_succ, Prod.snd_sum, Prod.smul_snd] using h
    have hcg : ∀ l : Fin j, d l.succ = 0 := by
      intro l
      exact (Fintype.linearIndependent_iff.mp hf) (fun l => d l.succ) hd2 l
    have hd0 : d 0 = 0 := by
      have h := congrArg Prod.fst hd
      have h3 : d 0 + ∑ l : Fin j, d l.succ * k l = 0 := by
        simpa [Fin.sum_univ_succ, Prod.fst_sum, Prod.smul_fst] using h
      have h4 : ∑ l : Fin j, d l.succ * k l = 0 := by simp [hcg]
      linarith
    intro i
    rcases Fin.eq_zero_or_eq_succ i with h | ⟨l, rfl⟩
    · rw [h]; exact hd0
    · exact hcg l
  have hcomp : lsm_TZ D.u D.v ∘ Fin.cons (1, 0) (fun l : Fin j => (k l, f l))
      = Fin.cons D.u (fun i => (∑ l, f i l • D.v l) + k i • D.u) := by
    funext i
    rcases Fin.eq_zero_or_eq_succ i with h | ⟨l, rfl⟩
    · rw [h]
      simp only [Function.comp_apply, Fin.cons_zero, lsm_TZ_apply, lsm_sigmaZ_eq_sum]
      rw [show (∑ i, (0 : Fin (R-1) → ℤ) i • D.v i) = 0 from by simp]
      simp
    · simp only [Function.comp_apply, Fin.cons_succ, lsm_TZ_apply, lsm_sigmaZ_eq_sum]
      abel
  rw [← hcomp]
  rw [Fintype.linearIndependent_iff] at hφLI ⊢
  intro d hd
  refine hφLI d ?_
  apply hTbij.1
  rw [map_zero]
  rw [← hd]
  simp only [map_sum, map_smul, Function.comp_apply]

/-! ## Rank / emptiness -/

lemma lsm_not_linind_of_lt {R m : ℕ} (h : R < m) (f : Fin m → (Fin R → ℤ)) :
    ¬ LinearIndependent ℤ f := by
  intro hf
  have hle := hf.fintype_card_le_finrank
  simp only [Fintype.card_fin, Module.finrank_fintype_fun_eq_card] at hle
  omega

omit [DecidableEq ι] in
lemma lsm_latMin_zero_of_lt {R k : ℕ} (Φ : LatMap (ι := ι) R) (h : R < k) : latMin Φ k = 0 := by
  rw [latMin]
  have hempty : {r : ℝ | 0 ≤ r ∧ ∃ f : Fin k → (Fin R → ℤ), LinearIndependent ℤ f ∧
      ∀ j, ‖Φ (fun i => (f j i : ℝ))‖ ≤ r} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro r ⟨-, f, hf, -⟩
    exact lsm_not_linind_of_lt h f hf
  rw [hempty, Real.sInf_empty]

omit [DecidableEq ι] in
lemma lsm_exists_linind_fin {R j : ℕ} (h : j ≤ R) :
    ∃ f : Fin j → (Fin R → ℤ), LinearIndependent ℤ f :=
  ⟨fun i => (Pi.basisFun ℤ (Fin R)) (Fin.castLE h i),
    (Pi.basisFun ℤ (Fin R)).linearIndependent.comp (Fin.castLE h) (Fin.castLE_injective h)⟩

end Helpers

/-! ## The main theorem -/

theorem latStep_min {ι : Type*} [Fintype ι] [DecidableEq ι] {R : ℕ} (D : Work.HP.FM.RecData R ι)
    (hu : ‖D.p‖ = Work.HP.latMin D.Φ 1) {j : ℕ} (hj : 1 ≤ j) :
    Work.HP.latMin D.Φ (j + 1) / 2 ≤ Work.HP.latMin D.step j := by
  classical
  set A : Set ℝ := {r : ℝ | 0 ≤ r ∧ ∃ f : Fin (j + 1) → (Fin R → ℤ), LinearIndependent ℤ f ∧
      ∀ i, ‖D.Φ (fun k => (f i k : ℝ))‖ ≤ r} with hA
  set B : Set ℝ := {r : ℝ | 0 ≤ r ∧ ∃ g : Fin j → (Fin (R - 1) → ℤ), LinearIndependent ℤ g ∧
      ∀ i, ‖D.step (fun k => (g i k : ℝ))‖ ≤ r} with hB
  have hAeq : latMin D.Φ (j + 1) = sInf A := by rw [latMin, hA]
  have hBeq : latMin D.step j = sInf B := by rw [latMin, hB]
  rw [hAeq, hBeq]
  have hBddA : BddBelow A := ⟨0, fun r hr => hr.1⟩
  rcases lt_or_ge R (j + 1) with hlt | hge
  · have hA0 : sInf A = 0 := by
      have hE : A = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro r ⟨-, f, hf, -⟩
        exact lsm_not_linind_of_lt hlt f hf
      rw [hE, Real.sInf_empty]
    rw [hA0, zero_div]
    simpa only [hBeq] using lsm_latMin_nonneg D.step j
  · have hjR : j ≤ R - 1 := by omega
    have hBne : B.Nonempty := by
      obtain ⟨g, hgLI⟩ := lsm_exists_linind_fin (R := R - 1) hjR
      refine ⟨∑ l, ‖D.step (fun k => (g l k : ℝ))‖,
        Finset.sum_nonneg (fun _ _ => norm_nonneg _), ?_⟩
      exact ⟨g, hgLI, fun l =>
        Finset.single_le_sum (f := fun i => ‖D.step (fun k => (g i k : ℝ))‖)
          (fun k _ => norm_nonneg _) (Finset.mem_univ l)⟩
    have hstep : ∀ r ∈ B, 2 * r ∈ A := by
      intro r hr
      obtain ⟨hr0, g, hgLI, hgr⟩ := hr
      obtain ⟨k0, hk0⟩ := lsm_lift_step D (g ⟨0, by omega⟩)
      have hg0 : g ⟨0, by omega⟩ ≠ 0 := hgLI.ne_zero ⟨0, by omega⟩
      have hwne : (∑ l, g ⟨0, by omega⟩ l • D.v l) + k0 • D.u ≠ 0 :=
        fun hw => hg0 (lsm_psi_add_smul_u_eq_zero D hw)
      have hp_le_x : ‖D.p‖
          ≤ ‖D.Φ (fun kk => (((∑ l, g ⟨0, by omega⟩ l • D.v l) + k0 • D.u) kk : ℝ))‖ := by
        rw [hu]
        exact lsm_latMin_one_le D.Φ hwne
      rw [lsm_Phi_cast_add_smul D (g ⟨0, by omega⟩) k0] at hp_le_x
      set X : EuclideanSpace ℝ ι :=
        D.Φ (fun kk => ((∑ l, g ⟨0, by omega⟩ l • D.v l) kk : ℝ)) + (k0 : ℝ) • D.p with hX
      have hk0' : ‖X‖ ^ 2
          ≤ ‖D.step (fun l => (g ⟨0, by omega⟩ l : ℝ))‖ ^ 2 + ‖D.p‖ ^ 2 / 4 := by
        rw [hX]; exact hk0
      have hx2 : ‖D.p‖ ^ 2 ≤ ‖X‖ ^ 2 := by
        rw [hX]; exact lsm_sq_le_sq_of_nonneg (norm_nonneg _) hp_le_x
      have hp_bound : ‖D.p‖ ≤ 2 * r := by
        have hz2 := lsm_sq_le_sq_of_nonneg (norm_nonneg _) (hgr ⟨0, by omega⟩)
        have hp2 : ‖D.p‖ ^ 2 ≤ (4 / 3) * r ^ 2 := by
          nlinarith [hk0', hx2, hz2, sq_nonneg ‖D.p‖]
        have hp4 : ‖D.p‖ ^ 2 ≤ (2 * r) ^ 2 := by nlinarith [hp2, sq_nonneg r]
        have h := sq_le_sq.mp hp4
        rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * r)] at h
        exact h
      choose kk hkk using fun i : Fin j => lsm_lift_step D (g i)
      have hFbnd : ∀ i : Fin j,
          ‖D.Φ (fun kk' => (((∑ l, g i l • D.v l) + kk i • D.u) kk' : ℝ))‖ ≤ 2 * r := by
        intro i
        rw [lsm_Phi_cast_add_smul D (g i) (kk i)]
        have hx2 : ‖D.Φ (fun kk => ((∑ l, g i l • D.v l) kk : ℝ)) + (kk i : ℝ) • D.p‖ ^ 2
            ≤ (2 * r) ^ 2 := by
          have h1 := hkk i
          have hz2 := lsm_sq_le_sq_of_nonneg (norm_nonneg _) (hgr i)
          have hp2 : ‖D.p‖ ^ 2 / 4 ≤ (2 * r) ^ 2 / 4 := by
            have := lsm_sq_le_sq_of_nonneg (norm_nonneg _) hp_bound
            linarith
          nlinarith [h1, hz2, hp2]
        have h := sq_le_sq.mp hx2
        rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * r)] at h
        exact h
      refine ⟨by linarith, Fin.cons D.u (fun i => (∑ l, g i l • D.v l) + kk i • D.u),
        lsm_cons_indep D g hgLI kk, ?_⟩
      intro i
      rcases Fin.eq_zero_or_eq_succ i with h | ⟨l, rfl⟩
      · rw [h, Fin.cons_zero]
        exact hp_bound
      · rw [Fin.cons_succ]
        exact hFbnd l
    exact le_csInf hBne (fun r hr => by
      have h2 := csInf_le hBddA (hstep r hr)
      linarith)

end Work.HP.FM
