import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2EightObjExists
import Submission.Work.CORE4.EightIdxDefs
import Submission.Work.CORE4.Case2EightA_le_FsupK0
import Submission.Work.CORE4.Case2SixEmbed

namespace Work.CORE4

open Work.GW2 Subgroup
open scoped Pointwise

variable {G : Type} [Group G]

/-! ## Two abstract lemmas about `Ω₁` on a product of two cyclic subgroups -/

/-- `omega1` is monotone in its subgroup argument. -/
theorem omega1_mono {p : ℕ} {P Q : Subgroup G} (h : P ≤ Q) :
    omega1 p P ≤ omega1 p Q :=
  Subgroup.closure_mono fun _ hx => ⟨h hx.1, hx.2⟩

/-- **The `p`-torsion of `F ⊔ K` is `Fp ⊔ Kp`**, when `F ⊓ K = ⊥`, `F ≤ N_G(K)`, the elements of
`F` and `K` commute, and `Fp ≤ F`, `Kp ≤ K` are exactly the sets of elements of `F`, resp. `K`, of
`p`-th power `1`.  (`F ⊔ K ≅ F × K` and the `p`-torsion of a direct product of two cyclic groups
is the product of the two torsions.) -/
theorem omega1_sup_eq_torsion {F K Fp Kp : Subgroup G} {p : ℕ}
    (hdisj : F ⊓ K = ⊥) (hleN : F ≤ Subgroup.normalizer (K : Set G))
    (hcomm : ∀ f ∈ F, ∀ k ∈ K, f * k = k * f)
    (hFp_le : Fp ≤ F) (hKp_le : Kp ≤ K)
    (hFp_omega : ∀ x ∈ F, x ^ p = 1 ↔ x ∈ Fp)
    (hKp_omega : ∀ x ∈ K, x ^ p = 1 ↔ x ∈ Kp) :
    omega1 p (F ⊔ K) = Fp ⊔ Kp := by
  have hcoe : (↑(F ⊔ K) : Set G) = (↑F : Set G) * (↑K : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right F K hleN
  apply le_antisymm
  · rw [omega1]
    refine (Subgroup.closure_le (Fp ⊔ Kp)).mpr ?_
    rintro z ⟨hzFK, hzp⟩
    have hz' : z ∈ (↑(F ⊔ K) : Set G) := hzFK
    rw [hcoe] at hz'
    obtain ⟨f, hf, k, hk, hfk⟩ := Set.mem_mul.mp hz'
    have hzp' : (f * k) ^ p = 1 := by rw [hfk]; exact hzp
    have hc : Commute f k := hcomm f hf k hk
    rw [hc.mul_pow] at hzp'
    have hfp : f ^ p = 1 := by
      have hmem : f ^ p ∈ F ⊓ K := by
        refine Subgroup.mem_inf.mpr ⟨F.pow_mem hf p, ?_⟩
        rw [eq_inv_of_mul_eq_one_left hzp']
        exact K.inv_mem (K.pow_mem hk p)
      have hb : f ^ p ∈ (⊥ : Subgroup G) := by rw [← hdisj]; exact hmem
      exact Subgroup.mem_bot.mp hb
    have hkp : k ^ p = 1 := by
      have hmem : k ^ p ∈ F ⊓ K := by
        refine Subgroup.mem_inf.mpr ⟨?_, K.pow_mem hk p⟩
        rw [eq_inv_of_mul_eq_one_right hzp']
        exact F.inv_mem (F.pow_mem hf p)
      have hb : k ^ p ∈ (⊥ : Subgroup G) := by rw [← hdisj]; exact hmem
      exact Subgroup.mem_bot.mp hb
    rw [← hfk]
    exact Subgroup.mul_mem_sup ((hFp_omega f hf).mp hfp) ((hKp_omega k hk).mp hkp)
  · refine sup_le ?_ ?_
    · intro x hx
      show x ∈ Subgroup.closure (omega1Set p (F ⊔ K))
      exact Subgroup.subset_closure ⟨Subgroup.mem_sup_left (hFp_le hx),
        (hFp_omega x (hFp_le hx)).mpr hx⟩
    · intro x hx
      show x ∈ Subgroup.closure (omega1Set p (F ⊔ K))
      exact Subgroup.subset_closure ⟨Subgroup.mem_sup_right (hKp_le hx),
        (hKp_omega x (hKp_le hx)).mpr hx⟩

/-! ## The main lemma -/

/-- Bender 1981, §4 (8): the `(p,p)`-subgroup `A ≤ F ⊔ K` of `Case2EightObj` is exactly
`Asub D p = Ω₁(F ⊔ K)`, and also `Ω₁(F ⊔ K₀)`, where `K₀ = F(U) ⊓ K`. -/
theorem EightAeqOmega (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ h.D.F → Nat.card ↥P = p →
          Work.GW2.Case2EightObj h.D p P A →
          A = Work.CORE4.Asub h.D p ∧
            A = Work.CORE4.omega1 p (h.D.F ⊔ Work.GW2.Case2Data.K0 h.D) := by
  intro G _ _ hbc B h p P A hp hPF hPcard hObj
  obtain ⟨-, -, -, hAle, hAcard, hAexp, -, _⟩ := hObj
  -- `p ∣ |F|`, `p ∣ |K₀|` (Bender's (6)), `p ∣ |K|`
  have hpF : p ∣ Nat.card ↥h.D.F := by
    rw [← hPcard]; exact Subgroup.card_dvd_of_le hPF
  have hFdvdK0 : Nat.card ↥h.D.F ∣ Nat.card ↥h.D.K0 :=
    Case2SixEmbed I G hbc B ⟨h.D, h.pre, h.F_ti, h.F_cyclic⟩
  have hpK0 : p ∣ Nat.card ↥h.D.K0 := hpF.trans hFdvdK0
  have hpK : p ∣ Nat.card ↥h.D.K := hpK0.trans (Subgroup.card_dvd_of_le inf_le_right)
  -- the `p`-torsion subgroups of `K` and `F`
  obtain ⟨Kp, hKp_le, hKp_card, hKp_omega⟩ :=
    CyclicOmegaPrime h.D.K p h.pre.K_cyclic hp hpK
  obtain ⟨Fp, hFp_le, hFp_card, hFp_omega⟩ :=
    CyclicOmegaPrime h.D.F p h.F_cyclic hp hpF
  have hP_le_Fp : P ≤ Fp := fun x hx =>
    (hFp_omega x (hPF hx)).mp (pow_eq_one_of_card_eq hPcard hx)
  have hPFp : P = Fp :=
    Subgroup.eq_of_le_of_card_ge hP_le_Fp (by rw [hFp_card, hPcard])
  have hP_omega : ∀ x ∈ h.D.F, x ^ p = 1 ↔ x ∈ P := by
    intro x hx; rw [hPFp]; exact hFp_omega x hx
  obtain ⟨-, -, -, -, hpuniq⟩ :=
    Case2EightPpSupUnique h.D.F h.D.K P Kp p (F_inf_K_eq_bot_c4 B h.D)
      (F_le_normalizer_K_c4 I B h.D) (F_commute_K_c4 I B h.D h.pre)
      hPF hKp_le hP_omega hKp_omega hPcard hKp_card
  -- `A = P ⊔ Kp = Fp ⊔ Kp`
  have hAeq : A = P ⊔ Kp := hpuniq A hAle hAcard hAexp
  -- `Ω₁(F ⊔ K) = Fp ⊔ Kp`
  have hOmega : omega1 p (h.D.F ⊔ h.D.K) = Fp ⊔ Kp :=
    omega1_sup_eq_torsion (F_inf_K_eq_bot_c4 B h.D) (F_le_normalizer_K_c4 I B h.D)
      (F_commute_K_c4 I B h.D h.pre) hFp_le hKp_le hFp_omega hKp_omega
  -- the `p`-torsion of `K` lies in `K₀`, hence `A ≤ F ⊔ K₀`
  have hKp_K0 : Kp ≤ h.D.K0 :=
    omegaPrime_le_of_card_dvd hp inf_le_right hpK0 hKp_card hKp_omega
  have hAleK0 : A ≤ h.D.F ⊔ h.D.K0 := by
    rw [hAeq]
    exact sup_le (le_trans hPF le_sup_left) (le_trans hKp_K0 le_sup_right)
  -- first conjunct: `A = Asub D p = Ω₁(F ⊔ K)`
  have hAsub : A = Asub h.D p := by
    show A = omega1 p (h.D.F ⊔ h.D.K)
    rw [hOmega, ← hPFp]
    exact hAeq
  refine ⟨hAsub, ?_⟩
  -- second conjunct: `A = Ω₁(F ⊔ K₀)`
  apply le_antisymm
  · intro x hx
    show x ∈ Subgroup.closure (omega1Set p (h.D.F ⊔ h.D.K0))
    exact Subgroup.subset_closure ⟨hAleK0 hx, hAexp x hx⟩
  · calc omega1 p (h.D.F ⊔ h.D.K0) ≤ omega1 p (h.D.F ⊔ h.D.K) :=
          omega1_mono (sup_le_sup le_rfl inf_le_right)
      _ = A := by rw [hOmega, ← hPFp]; exact hAeq.symm

end Work.CORE4
