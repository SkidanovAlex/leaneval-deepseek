import Mathlib
import Submission.Work.Mostow.gapA.tubeDefs
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.gapA.ematMulDet
import Submission.Work.Mostow.gapA.exists_fundamentalDomain
import Submission.Work.Mostow.gapA.unfoldTube
import Submission.Work.Mostow.gapA.packMeasureLe
import Submission.Work.Mostow.gapA.tubeSubsetTb
import Submission.Work.Mostow.gapA.sigIsometryGeodSet
import Submission.Work.Mostow.gapA.bdFixedRotation
import Submission.Work.Mostow.gapA.q0SubsetZpowers
import Submission.Work.Mostow.gapA.orderOfRotAbout
import Submission.Work.Mostow.gapA.sqrtTwoSinhAdd
import Submission.Work.Mostow.gapA.volH3Slab

namespace Work.Mostow.gapA
open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false


/-! ## Measurability of the coordinate functions -/

lemma tube_measurable_busemann (ξ : E 3) :
    Measurable (fun u : E 3 => busemann ξ u) := by
  have hcont : Continuous (fun u : E 3 => tpart u - inner ℝ u ξ) := by
    unfold tpart
    fun_prop
  exact Real.measurable_log.comp hcont.measurable

lemma tube_measurable_sig (a b : E 3) :
    Measurable (fun u : E 3 => sig a b u) := by
  unfold sig
  exact ((tube_measurable_busemann b).sub (tube_measurable_busemann a)).div_const 2

lemma tube_measurable_arcosh : Measurable (Real.arcosh : ℝ → ℝ) := by
  unfold Real.arcosh
  refine Real.measurable_log.comp ?_
  fun_prop

lemma tube_measurable_distGeod (a b : E 3) :
    Measurable (fun u : E 3 => distGeod a b u) := by
  unfold distGeod
  refine tube_measurable_arcosh.comp ?_
  have ha := tube_measurable_busemann a
  have hb := tube_measurable_busemann b
  exact ((ha.add hb).exp.const_mul 2).div_const (1 - inner ℝ a b) |>.sqrt

/-! ## Elementary structure of the centraliser of the rotation -/

/-- `b₀` commutes with every element of `C = cent Γ b₀`. -/
theorem comm_of_mem_cent {Γ : Subgroup (PO 3 1)} {b₀ c : PO 3 1} (hc : c ∈ cent Γ b₀) :
    b₀ * c = c * b₀ := by
  have h1 : c ∈ Subgroup.centralizer ({b₀} : Set (PO 3 1)) := hc.1
  exact Subgroup.mem_centralizer_iff.mp h1 b₀ (Set.mem_singleton b₀)

/-- Elements of `C` preserve the axis, hence permute its two endpoints. -/
theorem bd_pair_of_mem_cent (hA : Submission.Mostow.POActionProp 3)
    (hI : Submission.Mostow.HypIsometryProp 3) {a b : E 3} (ha : a ∈ Sph 3) (hb : b ∈ Sph 3)
    (hab : a ≠ b) {M : ℕ} (hM : 0 < M) {b₀ : PO 3 1}
    (hrot : IsRotationAbout b₀ a b (2 * Real.pi / (M : ℝ)))
    {Γ : Subgroup (PO 3 1)} {c : PO 3 1} (hc : c ∈ cent Γ b₀) :
    (bd c a = a ∨ bd c a = b) ∧ (bd c b = a ∨ bd c b = b) := by
  have hP := POBasic.ofProp hA
  have hcomm : b₀ * c = c * b₀ := comm_of_mem_cent hc
  have hb₀a : bd b₀ a = a :=
    ((bdFixedRotation hA hI a b ha hb hab M hM b₀ hrot) a ha).mpr (Or.inl rfl)
  have hb₀b : bd b₀ b = b :=
    ((bdFixedRotation hA hI a b ha hb hab M hM b₀ hrot) b hb).mpr (Or.inr rfl)
  have key : ∀ x ∈ ({a, b} : Set (E 3)), bd b₀ (bd c x) = bd c x := by
    intro x hx
    have hx' : x = a ∨ x = b := by simpa using hx
    have hfix : bd b₀ x = x := by rcases hx' with h | h <;> rw [h] <;> assumption
    have hxS : x ∈ Sph 3 := by rcases hx' with h | h <;> rw [h] <;> assumption
    calc bd b₀ (bd c x) = bd (b₀ * c) x := (hP.bd_mul b₀ c x hxS).symm
      _ = bd (c * b₀) x := by rw [hcomm]
      _ = bd c (bd b₀ x) := hP.bd_mul c b₀ x hxS
      _ = bd c x := by rw [hfix]
  refine ⟨?_, ?_⟩
  · exact ((bdFixedRotation hA hI a b ha hb hab M hM b₀ hrot) (bd c a)
      (hP.bd_mem c a ha)).mp (key a (by simp))
  · exact ((bdFixedRotation hA hI a b ha hb hab M hM b₀ hrot) (bd c b)
      (hP.bd_mem c b hb)).mp (key b (by simp))

/-- `bd c⁻¹ a = a ↔ bd c a = a`. -/
theorem bd_inv_iff (hA : Submission.Mostow.POActionProp 3) {a : E 3} (ha : a ∈ Sph 3)
    {c : PO 3 1} : bd c⁻¹ a = a ↔ bd c a = a := by
  have hP := POBasic.ofProp hA
  constructor
  · intro h
    have hh : bd c (bd c⁻¹ a) = bd c a := by rw [h]
    rw [← hP.bd_mul c c⁻¹ a ha, mul_inv_cancel, hP.bd_one a ha] at hh
    exact hh.symm
  · intro h
    have hh : bd c⁻¹ (bd c a) = bd c⁻¹ a := by rw [h]
    rw [← hP.bd_mul c⁻¹ c a ha, inv_mul_cancel, hP.bd_one a ha] at hh
    exact hh.symm

/-! ## The translation part `C⁺` -/

theorem eps_eq_pm_one (a : E 3) (c : PO 3 1) : eps a c = 1 ∨ eps a c = -1 := by
  unfold eps; split <;> simp

theorem eps_eq_one_iff {a : E 3} {c : PO 3 1} : eps a c = 1 ↔ bd c a = a := by
  unfold eps
  by_cases h : bd c a = a
  · rw [if_pos h]; exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [if_neg h]; exact ⟨fun hh => absurd hh.symm (by norm_num), fun hh => absurd hh h⟩

theorem eps_eq_neg_one_iff {a : E 3} {c : PO 3 1} : eps a c = -1 ↔ bd c a ≠ a := by
  unfold eps
  by_cases h : bd c a = a
  · rw [if_pos h]; exact ⟨fun hh => absurd hh (by norm_num), fun hh => absurd h hh⟩
  · rw [if_neg h]; exact ⟨fun _ => h, fun _ => rfl⟩

/-- The translation part of `C`: the elements fixing the endpoint `a`. -/
def Cplus (Γ : Subgroup (PO 3 1)) (b₀ : PO 3 1) (a : E 3) : Set (PO 3 1) :=
  {c | c ∈ cent Γ b₀ ∧ bd c a = a}

theorem one_mem_Cplus (hA : Submission.Mostow.POActionProp 3) {Γ : Subgroup (PO 3 1)}
    {b₀ : PO 3 1} {a : E 3} (ha : a ∈ Sph 3) : (1 : PO 3 1) ∈ Cplus Γ b₀ a :=
  ⟨Subgroup.one_mem _, (POBasic.ofProp hA).bd_one a ha⟩

theorem mul_mem_Cplus (hA : Submission.Mostow.POActionProp 3) {Γ : Subgroup (PO 3 1)}
    {b₀ c c' : PO 3 1} {a : E 3} (ha : a ∈ Sph 3)
    (hc : c ∈ Cplus Γ b₀ a) (hc' : c' ∈ Cplus Γ b₀ a) : c * c' ∈ Cplus Γ b₀ a := by
  have hP := POBasic.ofProp hA
  exact ⟨Subgroup.mul_mem _ hc.1 hc'.1, by rw [hP.bd_mul c c' a ha, hc'.2, hc.2]⟩

theorem inv_mem_Cplus (hA : Submission.Mostow.POActionProp 3) {Γ : Subgroup (PO 3 1)}
    {b₀ c : PO 3 1} {a : E 3} (ha : a ∈ Sph 3)
    (hc : c ∈ Cplus Γ b₀ a) : c⁻¹ ∈ Cplus Γ b₀ a :=
  ⟨Subgroup.inv_mem _ hc.1, (bd_inv_iff hA ha).mpr hc.2⟩

/-- `cent Γ b₀` is closed under multiplication. -/
theorem mul_mem_cent {Γ : Subgroup (PO 3 1)} {b₀ c c' : PO 3 1}
    (hc : c ∈ cent Γ b₀) (hc' : c' ∈ cent Γ b₀) : c * c' ∈ cent Γ b₀ :=
  ⟨Subgroup.mul_mem _ hc.1 hc'.1, Subgroup.mul_mem _ hc.2 hc'.2⟩

/-- `cent Γ b₀` is closed under inversion. -/
theorem inv_mem_cent {Γ : Subgroup (PO 3 1)} {b₀ c : PO 3 1} (hc : c ∈ cent Γ b₀) :
    c⁻¹ ∈ cent Γ b₀ :=
  ⟨Subgroup.inv_mem _ hc.1, Subgroup.inv_mem _ hc.2⟩

theorem eps_eq_one_of_mem_Cplus {Γ : Subgroup (PO 3 1)} {b₀ c : PO 3 1} {a : E 3}
    (hc : c ∈ Cplus Γ b₀ a) : eps a c = 1 := eps_eq_one_iff.mpr hc.2

/-- `bd c` is injective on the sphere. -/
theorem bd_injective_on_sph (hA : Submission.Mostow.POActionProp 3) (c : PO 3 1) :
    ∀ x y : E 3, x ∈ Sph 3 → y ∈ Sph 3 → bd c x = bd c y → x = y := by
  have hP := POBasic.ofProp hA
  intro x y hx hy hxy
  have h1 : bd c⁻¹ (bd c x) = bd c⁻¹ (bd c y) := by rw [hxy]
  have h2 : bd c⁻¹ (bd c x) = x := by
    rw [← hP.bd_mul c⁻¹ c x hx, inv_mul_cancel, hP.bd_one x hx]
  have h3 : bd c⁻¹ (bd c y) = y := by
    rw [← hP.bd_mul c⁻¹ c y hy, inv_mul_cancel, hP.bd_one y hy]
  rwa [h2, h3] at h1

/-- The transformation law for the Busemann coordinate `sig` under `c ∈ C`. -/
theorem sig_smul_of_mem_cent (hA : Submission.Mostow.POActionProp 3)
    (hI : Submission.Mostow.HypIsometryProp 3) {a b : E 3} (ha : a ∈ Sph 3) (hb : b ∈ Sph 3)
    (hab : a ≠ b) {M : ℕ} (hM : 0 < M) {b₀ : PO 3 1}
    (hrot : IsRotationAbout b₀ a b (2 * Real.pi / (M : ℝ)))
    {Γ : Subgroup (PO 3 1)} {c : PO 3 1} (hc : c ∈ cent Γ b₀) (u : E 3) :
    sig a b (c • u) = eps a c * sig a b u + psi a b c := by
  have hP := POBasic.ofProp hA
  have hJ := HypIsoData.ofProp hI
  have hc' : c⁻¹ ∈ cent Γ b₀ := ⟨Subgroup.inv_mem _ hc.1, Subgroup.inv_mem _ hc.2⟩
  obtain ⟨hp1, hp2⟩ := bd_pair_of_mem_cent hA hI ha hb hab hM hrot hc'
  have coc_b : busemann b (c • u) =
      busemann (bd c⁻¹ b) u + busemann b (c • (0 : E 3)) := by
    have h := hJ.busemann_cocycle c (bd c⁻¹ b) u (hP.bd_mem c⁻¹ b hb)
    have h2 : bd c (bd c⁻¹ b) = b := by
      rw [← hP.bd_mul c c⁻¹ b hb, mul_inv_cancel, hP.bd_one b hb]
    rwa [h2] at h
  have coc_a : busemann a (c • u) =
      busemann (bd c⁻¹ a) u + busemann a (c • (0 : E 3)) := by
    have h := hJ.busemann_cocycle c (bd c⁻¹ a) u (hP.bd_mem c⁻¹ a ha)
    have h2 : bd c (bd c⁻¹ a) = a := by
      rw [← hP.bd_mul c c⁻¹ a ha, mul_inv_cancel, hP.bd_one a ha]
    rwa [h2] at h
  rcases hp1 with h1 | h1
  · -- `bd c⁻¹ a = a`: a translation
    have hcase : bd c a = a := (bd_inv_iff hA ha).symm.mpr h1
    have h2 : bd c⁻¹ b = b := by
      rcases hp2 with h | h
      · exfalso
        have : a = b := by
          have hh : bd c (bd c⁻¹ a) = bd c (bd c⁻¹ b) := by rw [h1, h]
          rwa [← hP.bd_mul c c⁻¹ a ha, mul_inv_cancel, hP.bd_one a ha,
               ← hP.bd_mul c c⁻¹ b hb, mul_inv_cancel, hP.bd_one b hb] at hh
        exact hab this
      · exact h
    have heps : eps a c = 1 := by rw [eps_eq_one_iff]; exact hcase
    rw [heps]
    simp only [sig, psi]
    rw [coc_b, coc_a, h1, h2]
    ring
  · -- `bd c⁻¹ a = b`: a reversal
    have hcase : bd c a ≠ a := by
      intro h
      have h1' : bd c⁻¹ a = a := (bd_inv_iff hA ha).mpr h
      rw [h1'] at h1
      exact hab h1
    have h2 : bd c⁻¹ b = a := by
      rcases hp2 with h | h
      · exact h
      · exfalso
        have : a = b := by
          have hh : bd c (bd c⁻¹ a) = bd c (bd c⁻¹ b) := by rw [h1, h]
          rwa [← hP.bd_mul c c⁻¹ a ha, mul_inv_cancel, hP.bd_one a ha,
               ← hP.bd_mul c c⁻¹ b hb, mul_inv_cancel, hP.bd_one b hb] at hh
        exact hab this
    have heps : eps a c = -1 := by rw [eps_eq_neg_one_iff]; exact hcase
    rw [heps]
    simp only [sig, psi]
    rw [coc_b, coc_a, h1, h2]
    ring

/-- `psi` is a crossed homomorphism on `C`. -/
theorem psi_mul_of_mem_cent (hA : Submission.Mostow.POActionProp 3)
    (hI : Submission.Mostow.HypIsometryProp 3) {a b : E 3} (ha : a ∈ Sph 3) (hb : b ∈ Sph 3)
    (hab : a ≠ b) {M : ℕ} (hM : 0 < M) {b₀ : PO 3 1}
    (hrot : IsRotationAbout b₀ a b (2 * Real.pi / (M : ℝ)))
    {Γ : Subgroup (PO 3 1)} {c c' : PO 3 1} (hc : c ∈ cent Γ b₀) (hc' : c' ∈ cent Γ b₀) :
    psi a b (c * c') = psi a b c + eps a c * psi a b c' := by
  have hP := POBasic.ofProp hA
  have h1 := sig_smul_of_mem_cent hA hI ha hb hab hM hrot hc (c' • (0 : E 3))
  rw [← hP.mul_smul c c' (0 : E 3)] at h1
  simp only [psi] at h1 ⊢
  rw [h1]; ring

/-- `psi` is additive on the translation part `C⁺`. -/
theorem psi_add (hA : Submission.Mostow.POActionProp 3) (hI : Submission.Mostow.HypIsometryProp 3)
    {a b : E 3} (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b) {M : ℕ} (hM : 0 < M)
    {b₀ : PO 3 1} (hrot : IsRotationAbout b₀ a b (2 * Real.pi / (M : ℝ)))
    {Γ : Subgroup (PO 3 1)} {c c' : PO 3 1} (hc : c ∈ Cplus Γ b₀ a) (hc' : c' ∈ Cplus Γ b₀ a) :
    psi a b (c * c') = psi a b c + psi a b c' := by
  rw [psi_mul_of_mem_cent hA hI ha hb hab hM hrot hc.1 hc'.1, eps_eq_one_of_mem_Cplus hc, one_mul]

/-- `C` preserves the axis. -/
theorem cent_preserves_geodSet (hA : Submission.Mostow.POActionProp 3) {a b : E 3}
    {M : ℕ} (hM : 0 < M) {b₀ : PO 3 1}
    (hrot : IsRotationAbout b₀ a b (2 * Real.pi / (M : ℝ)))
    {Γ : Subgroup (PO 3 1)} {c : PO 3 1} (hc : c ∈ cent Γ b₀) (u : E 3) :
    c • u ∈ geodSet a b ↔ u ∈ geodSet a b := by
  have hP := POBasic.ofProp hA
  have hcomm : b₀ * c = c * b₀ := comm_of_mem_cent hc
  have h1 : ∀ v : E 3, b₀ • (c • v) = c • (b₀ • v) := by
    intro v
    rw [← hP.mul_smul c b₀ v, ← hcomm, hP.mul_smul b₀ c v]
  constructor
  · intro hu
    have huX : b₀ • (c • u) = c • u := (hrot.1 (c • u)).mpr hu
    rw [h1 u] at huX
    have h2 : c⁻¹ • (c • (b₀ • u)) = c⁻¹ • (c • u) := by rw [huX]
    rw [← hP.mul_smul c⁻¹ c (b₀ • u), ← hP.mul_smul c⁻¹ c u] at h2
    rw [inv_mul_cancel, hP.one_smul, hP.one_smul] at h2
    exact (hrot.1 u).mp h2
  · intro hu
    have huX : b₀ • u = u := (hrot.1 u).mpr hu
    exact (hrot.1 (c • u)).mp (by rw [h1 u, huX])

/-- `psi a b 1 = 0`. -/
theorem psi_one (hA : Submission.Mostow.POActionProp 3) (a b : E 3) :
    psi a b (1 : PO 3 1) = 0 := by
  have hP := POBasic.ofProp hA
  have h1 : busemann a (0 : E 3) = 0 := by simp [busemann, tpart]
  have h2 : busemann b (0 : E 3) = 0 := by simp [busemann, tpart]
  simp only [psi, sig]
  rw [hP.one_smul, h1, h2, sub_self, zero_div]

/-- `psi` of an inverse. -/
theorem psi_inv (hA : Submission.Mostow.POActionProp 3)
    (hI : Submission.Mostow.HypIsometryProp 3) {a b : E 3} (ha : a ∈ Sph 3) (hb : b ∈ Sph 3)
    (hab : a ≠ b) {M : ℕ} (hM : 0 < M) {b₀ : PO 3 1}
    (hrot : IsRotationAbout b₀ a b (2 * Real.pi / (M : ℝ)))
    {Γ : Subgroup (PO 3 1)} {c : PO 3 1} (hc : c ∈ cent Γ b₀) :
    psi a b c⁻¹ = - eps a c * psi a b c := by
  have hcomm := psi_mul_of_mem_cent hA hI ha hb hab hM hrot hc
    ⟨Subgroup.inv_mem _ hc.1, Subgroup.inv_mem _ hc.2⟩
  rw [mul_inv_cancel, psi_one hA a b] at hcomm
  rcases eps_eq_pm_one a c with he | he
  · rw [he] at hcomm ⊢
    ring_nf at hcomm ⊢
    linarith [hcomm]
  · rw [he] at hcomm ⊢
    ring_nf at hcomm ⊢
    linarith [hcomm]

/-- If `c ∈ C` reverses the axis, then so does `c⁻¹`, and both swap `a` and `b`. -/
theorem bd_swap_of_rev (hA : Submission.Mostow.POActionProp 3)
    (hI : Submission.Mostow.HypIsometryProp 3) {a b : E 3} (ha : a ∈ Sph 3) (hb : b ∈ Sph 3)
    (hab : a ≠ b) {M : ℕ} (hM : 0 < M) {b₀ : PO 3 1}
    (hrot : IsRotationAbout b₀ a b (2 * Real.pi / (M : ℝ)))
    {Γ : Subgroup (PO 3 1)} {c : PO 3 1} (hc : c ∈ cent Γ b₀) (hrev : bd c a = b) :
    bd c b = a ∧ bd c⁻¹ a = b ∧ bd c⁻¹ b = a := by
  have hP := POBasic.ofProp hA
  have hcinv : c⁻¹ ∈ cent Γ b₀ := ⟨Subgroup.inv_mem _ hc.1, Subgroup.inv_mem _ hc.2⟩
  have hinj := bd_injective_on_sph hA c
  have hcb : bd c b = a := by
    rcases (bd_pair_of_mem_cent hA hI ha hb hab hM hrot hc).2 with h | h
    · exact h
    · exact absurd (hinj b a hb ha (h.trans hrev.symm)) hab.symm
  have hcinva : bd c⁻¹ a = b := by
    rcases (bd_pair_of_mem_cent hA hI ha hb hab hM hrot hcinv).1 with h | h
    · exfalso
      have h2 : bd c (bd c⁻¹ a) = a := by
        rw [← hP.bd_mul c c⁻¹ a ha, mul_inv_cancel, hP.bd_one a ha]
      rw [h] at h2
      exact hab (h2.symm.trans hrev)
    · exact h
  have hcinvb : bd c⁻¹ b = a := by
    rcases (bd_pair_of_mem_cent hA hI ha hb hab hM hrot hcinv).2 with h | h
    · exact h
    · exfalso
      have h2 : bd c (bd c⁻¹ b) = b := by
        rw [← hP.bd_mul c c⁻¹ b hb, mul_inv_cancel, hP.bd_one b hb]
      rw [h] at h2
      exact hab (hcb.symm.trans h2)
  exact ⟨hcb, hcinva, hcinvb⟩

/-- `eps` is insensitive to inversion. -/
theorem eps_inv (hA : Submission.Mostow.POActionProp 3) {a : E 3} (ha : a ∈ Sph 3)
    (c : PO 3 1) : eps a c⁻¹ = eps a c := by
  by_cases h : bd c a = a
  · rw [eps_eq_one_iff.mpr ((bd_inv_iff hA ha).mpr h), eps_eq_one_iff.mpr h]
  · rw [eps_eq_neg_one_iff.mpr (fun hh => h ((bd_inv_iff hA ha).mp hh)), eps_eq_neg_one_iff.mpr h]

/-- For two elements of `C` acting in the same way on the endpoint `a`, the product
`c * c₁⁻¹` lies in the translation part `C⁺` and `psi` is additive on it. -/
theorem psi_mul_inv_of_same_eps (hA : Submission.Mostow.POActionProp 3)
    (hI : Submission.Mostow.HypIsometryProp 3) {a b : E 3} (ha : a ∈ Sph 3) (hb : b ∈ Sph 3)
    (hab : a ≠ b) {M : ℕ} (hM : 0 < M) {b₀ : PO 3 1}
    (hrot : IsRotationAbout b₀ a b (2 * Real.pi / (M : ℝ)))
    {Γ : Subgroup (PO 3 1)} {c c₁ : PO 3 1} (hc : c ∈ cent Γ b₀) (hc₁ : c₁ ∈ cent Γ b₀)
    (heps : eps a c = eps a c₁) :
    c * c₁⁻¹ ∈ Cplus Γ b₀ a ∧ psi a b (c * c₁⁻¹) = psi a b c - psi a b c₁ := by
  have hP := POBasic.ofProp hA
  have hc₁inv : c₁⁻¹ ∈ cent Γ b₀ := ⟨Subgroup.inv_mem _ hc₁.1, Subgroup.inv_mem _ hc₁.2⟩
  rcases eps_eq_pm_one a c with he | he
  · have hcC : c ∈ Cplus Γ b₀ a := ⟨hc, eps_eq_one_iff.mp he⟩
    have hc₁C : c₁ ∈ Cplus Γ b₀ a := ⟨hc₁, eps_eq_one_iff.mp (by rw [← heps]; exact he)⟩
    refine ⟨mul_mem_Cplus hA ha hcC (inv_mem_Cplus hA ha hc₁C), ?_⟩
    rw [psi_mul_of_mem_cent hA hI ha hb hab hM hrot hc hc₁inv,
      psi_inv hA hI ha hb hab hM hrot hc₁, eps_eq_one_of_mem_Cplus hcC,
      eps_eq_one_of_mem_Cplus hc₁C]
    ring
  · have he₁ : eps a c₁ = -1 := by rw [← heps]; exact he
    have hcrev : bd c a = b := by
      rcases (bd_pair_of_mem_cent hA hI ha hb hab hM hrot hc).1 with h | h
      · exact absurd (eps_eq_one_iff.mpr h) (by rw [he]; norm_num)
      · exact h
    have hc₁rev : bd c₁ a = b := by
      rcases (bd_pair_of_mem_cent hA hI ha hb hab hM hrot hc₁).1 with h | h
      · exact absurd (eps_eq_one_iff.mpr h) (by rw [he₁]; norm_num)
      · exact h
    obtain ⟨hcb, -, -⟩ := bd_swap_of_rev hA hI ha hb hab hM hrot hc hcrev
    obtain ⟨-, hc₁inva, -⟩ := bd_swap_of_rev hA hI ha hb hab hM hrot hc₁ hc₁rev
    refine ⟨⟨mul_mem_cent hc (inv_mem_cent hc₁), ?_⟩, ?_⟩
    · rw [hP.bd_mul c c₁⁻¹ a ha, hc₁inva, hcb]
    · rw [psi_mul_of_mem_cent hA hI ha hb hab hM hrot hc hc₁inv,
        psi_inv hA hI ha hb hab hM hrot hc₁, he, he₁]
      ring

/-- For two elements of `C` acting in the same way on `a` and with the same `psi`, the
quotient `c₁⁻¹ * c` lies in the kernel of `psi` on `C⁺`. -/
theorem psi_inv_mul_of_same_eps (hA : Submission.Mostow.POActionProp 3)
    (hI : Submission.Mostow.HypIsometryProp 3) {a b : E 3} (ha : a ∈ Sph 3) (hb : b ∈ Sph 3)
    (hab : a ≠ b) {M : ℕ} (hM : 0 < M) {b₀ : PO 3 1}
    (hrot : IsRotationAbout b₀ a b (2 * Real.pi / (M : ℝ)))
    {Γ : Subgroup (PO 3 1)} {c c₁ : PO 3 1} (hc : c ∈ cent Γ b₀) (hc₁ : c₁ ∈ cent Γ b₀)
    (heps : eps a c = eps a c₁) (hpsi : psi a b c = psi a b c₁) :
    c₁⁻¹ * c ∈ Cplus Γ b₀ a ∧ psi a b (c₁⁻¹ * c) = 0 := by
  have hP := POBasic.ofProp hA
  have hc₁inv : c₁⁻¹ ∈ cent Γ b₀ := ⟨Subgroup.inv_mem _ hc₁.1, Subgroup.inv_mem _ hc₁.2⟩
  have hepsinv : eps a c₁⁻¹ = eps a c := by
    rw [eps_inv hA ha c₁, heps]
  rcases eps_eq_pm_one a c with he | he
  · -- both are translations
    have hcC : c ∈ Cplus Γ b₀ a := ⟨hc, eps_eq_one_iff.mp he⟩
    have hc₁C : c₁ ∈ Cplus Γ b₀ a := ⟨hc₁, eps_eq_one_iff.mp (by rw [← heps]; exact he)⟩
    refine ⟨mul_mem_Cplus hA ha (inv_mem_Cplus hA ha hc₁C) hcC, ?_⟩
    rw [psi_mul_of_mem_cent hA hI ha hb hab hM hrot hc₁inv hc,
      psi_inv hA hI ha hb hab hM hrot hc₁, eps_eq_one_of_mem_Cplus hc₁C, hpsi, hepsinv,
      eps_eq_one_of_mem_Cplus hcC]
    ring
  · -- both are reversals
    have he₁ : eps a c₁ = -1 := by rw [← heps]; exact he
    have hcrev : bd c a = b := by
      rcases (bd_pair_of_mem_cent hA hI ha hb hab hM hrot hc).1 with h | h
      · exact absurd (eps_eq_one_iff.mpr h) (by rw [he]; norm_num)
      · exact h
    have hc₁rev : bd c₁ a = b := by
      rcases (bd_pair_of_mem_cent hA hI ha hb hab hM hrot hc₁).1 with h | h
      · exact absurd (eps_eq_one_iff.mpr h) (by rw [he₁]; norm_num)
      · exact h
    obtain ⟨-, -, hc₁invb⟩ := bd_swap_of_rev hA hI ha hb hab hM hrot hc₁ hc₁rev
    refine ⟨⟨mul_mem_cent (inv_mem_cent hc₁) hc, ?_⟩, ?_⟩
    · rw [hP.bd_mul c₁⁻¹ c a ha, hcrev, hc₁invb]
    · rw [psi_mul_of_mem_cent hA hI ha hb hab hM hrot hc₁inv hc,
        psi_inv hA hI ha hb hab hM hrot hc₁, hpsi, hepsinv, he, he₁]
      ring

/-- `psi c = 0` for `c ∈ C⁺` exactly when `c` fixes the axis pointwise. -/
theorem psi_eq_zero_iff_fix (hA : Submission.Mostow.POActionProp 3)
    (hI : Submission.Mostow.HypIsometryProp 3)
    {a b : E 3} (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b) {M : ℕ} (hM : 0 < M)
    {b₀ : PO 3 1} (hrot : IsRotationAbout b₀ a b (2 * Real.pi / (M : ℝ)))
    {Γ : Subgroup (PO 3 1)} {c : PO 3 1} (hc : c ∈ Cplus Γ b₀ a) :
    psi a b c = 0 ↔ ∀ u : E 3, u ∈ geodSet a b → c • u = u := by
  have hP := POBasic.ofProp hA
  have hJ := HypIsoData.ofProp hI
  obtain ⟨u₀, hu₀⟩ := (geodFacts 3 (by norm_num) hA hI a b ha hb hab).1
  constructor
  · intro h u hu
    have h1 := sig_smul_of_mem_cent hA hI ha hb hab hM hrot hc.1 u
    rw [eps_eq_one_of_mem_Cplus hc, one_mul, h] at h1
    have h2 : hdist u (c • u) = 0 := by
      have h3 : hdist u (c • u) = |sig a b u - sig a b (c • u)| :=
        sigIsometryGeodSet hA hI a b ha hb hab u (c • u) hu
          ((cent_preserves_geodSet hA hM hrot hc.1 u).mpr hu)
      rw [h3, h1]
      simp
    exact ((hJ.eq_zero u (c • u)).mp h2).symm
  · intro h
    have h1 := sig_smul_of_mem_cent hA hI ha hb hab hM hrot hc.1 u₀
    rw [eps_eq_one_of_mem_Cplus hc, one_mul] at h1
    rw [h u₀ hu₀] at h1
    linarith [h1]

/-- Finitely many elements of `C⁺` have small `psi`. -/
theorem finite_psi_small (hA : Submission.Mostow.POActionProp 3)
    (hI : Submission.Mostow.HypIsometryProp 3) (Γ : Subgroup (PO 3 1))
    (hdisc : IsDiscrete (SetLike.coe Γ))
    {a b : E 3} (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b) {M : ℕ} (hM : 0 < M)
    {b₀ : PO 3 1} (hrot : IsRotationAbout b₀ a b (2 * Real.pi / (M : ℝ)))
    (ε : ℝ) :
    {c : PO 3 1 | c ∈ Cplus Γ b₀ a ∧ |psi a b c| ≤ ε}.Finite := by
  have hP := POBasic.ofProp hA
  have hJ := HypIsoData.ofProp hI
  obtain ⟨u₀, hu₀⟩ := (geodFacts 3 (by norm_num) hA hI a b ha hb hab).1
  have hfin : {γ : Γ | hdist (0 : E 3) ((γ : PO 3 1) • (0 : E 3)) ≤
      2 * hdist (0 : E 3) u₀ + ε}.Finite := finite_nearStab hP hJ hdisc _
  refine Set.Finite.subset (hfin.image (fun γ : Γ => (γ : PO 3 1))) ?_
  intro c hc
  obtain ⟨hcp, hpsi⟩ := hc
  have hdisp : hdist u₀ (c • u₀) = |psi a b c| := by
    have h1 := sig_smul_of_mem_cent hA hI ha hb hab hM hrot hcp.1 u₀
    rw [eps_eq_one_of_mem_Cplus hcp, one_mul] at h1
    have h2 : hdist u₀ (c • u₀) = |sig a b u₀ - sig a b (c • u₀)| :=
      sigIsometryGeodSet hA hI a b ha hb hab u₀ (c • u₀) hu₀
        ((cent_preserves_geodSet hA hM hrot hcp.1 u₀).mpr hu₀)
    have hsub : sig a b u₀ - (sig a b u₀ + psi a b c) = - psi a b c := by ring
    rw [h2, h1, hsub, abs_neg]
  have hbdd : hdist (0 : E 3) (c • (0 : E 3)) ≤ 2 * hdist (0 : E 3) u₀ + ε := by
    have h1 : hdist (0 : E 3) (c • (0 : E 3)) ≤
        hdist (0 : E 3) (c • u₀) + hdist (c • u₀) (c • (0 : E 3)) :=
      hJ.triangle 0 (c • u₀) (c • (0 : E 3))
    have h2 : hdist (0 : E 3) (c • u₀) ≤ hdist (0 : E 3) u₀ + hdist u₀ (c • u₀) :=
      hJ.triangle 0 u₀ (c • u₀)
    rw [hJ.isom_smul c u₀ (0 : E 3), hJ.symm u₀ 0] at h1
    rw [hdisp] at h2
    linarith [h1, h2, hpsi]
  exact ⟨⟨c, hcp.1.2⟩, hbdd, rfl⟩

/-! ## The orientation character -/

/-- The orientation character is multiplicative. -/
theorem isOriented_mul_iff (hA : Submission.Mostow.POActionProp 3) (g g' : PO 3 1) :
    IsOriented (g * g') ↔ (IsOriented g ∧ IsOriented g') ∨ (¬ IsOriented g ∧ ¬ IsOriented g') := by
  obtain ⟨hmul, hone, hinv, hdet, hiff⟩ := ematMulDet
  have hg0 : (emat g).det ≠ 0 := by
    intro h0
    have h1 : (emat g).det * (emat g⁻¹).det = 1 := by
      rw [← Matrix.det_mul, ← hmul, mul_inv_cancel, hone, Matrix.det_one]
    rw [h0, zero_mul] at h1
    exact one_ne_zero h1.symm
  have hg0' : (emat g').det ≠ 0 := by
    intro h0
    have h1 : (emat g').det * (emat g'⁻¹).det = 1 := by
      rw [← Matrix.det_mul, ← hmul, mul_inv_cancel, hone, Matrix.det_one]
    rw [h0, zero_mul] at h1
    exact one_ne_zero h1.symm
  rw [hiff (g * g'), hmul, Matrix.det_mul]
  constructor
  · intro h
    rcases (mul_pos_iff.mp h) with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inl ⟨(hiff g).mpr ha, (hiff g').mpr hb⟩
    · exact Or.inr ⟨fun hcon => absurd ((hiff g).mp hcon) (not_lt.mpr (le_of_lt ha)),
        fun hcon => absurd ((hiff g').mp hcon) (not_lt.mpr (le_of_lt hb))⟩
  · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
    · exact mul_pos ((hiff g).mp ha) ((hiff g').mp hb)
    · have h1 : (emat g).det < 0 := by
        rcases lt_or_gt_of_ne hg0 with h | h
        · exact h
        · exact absurd ((hiff g).mpr h) ha
      have h2 : (emat g').det < 0 := by
        rcases lt_or_gt_of_ne hg0' with h | h
        · exact h
        · exact absurd ((hiff g').mpr h) hb
      exact mul_pos_of_neg_of_neg h1 h2

/-- The coset decomposition of `C` along `C⁺`. -/
theorem Cplus_coset (hA : Submission.Mostow.POActionProp 3)
    (hI : Submission.Mostow.HypIsometryProp 3) {a b : E 3} (ha : a ∈ Sph 3) (hb : b ∈ Sph 3)
    (hab : a ≠ b) {M : ℕ} (hM : 0 < M) {b₀ c : PO 3 1}
    (hrot : IsRotationAbout b₀ a b (2 * Real.pi / (M : ℝ)))
    {Γ : Subgroup (PO 3 1)} (hc : c ∈ cent Γ b₀) (hcrev : bd c a = b) :
    ∀ d ∈ cent Γ b₀, d ∈ Cplus Γ b₀ a ∨ ∃ e ∈ Cplus Γ b₀ a, d = c * e := by
  have hP := POBasic.ofProp hA
  have hcinv : c⁻¹ ∈ cent Γ b₀ := ⟨Subgroup.inv_mem _ hc.1, Subgroup.inv_mem _ hc.2⟩
  obtain ⟨-, -, hcrevb⟩ := bd_swap_of_rev hA hI ha hb hab hM hrot hc hcrev
  intro d hd
  by_cases hdm : d ∈ Cplus Γ b₀ a
  · exact Or.inl hdm
  · right
    have hdrev : bd d a = b := by
      rcases (bd_pair_of_mem_cent hA hI ha hb hab hM hrot hd).1 with h | h
      · exact absurd ⟨hd, h⟩ hdm
      · exact h
    refine ⟨c⁻¹ * d, ⟨⟨Subgroup.mul_mem _ hcinv.1 hd.1, Subgroup.mul_mem _ hcinv.2 hd.2⟩, ?_⟩, ?_⟩
    · rw [hP.bd_mul c⁻¹ d a ha, hdrev]
      exact hcrevb
    · group

/-- The kernel of `psi` on `C⁺` has at most `2M` elements. -/
theorem card_ker_le (hA : Submission.Mostow.POActionProp 3)
    (hI : Submission.Mostow.HypIsometryProp 3) (Γ : Subgroup (PO 3 1))
    {a b : E 3} (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b)
    {M : ℕ} (hM : 0 < M) {b₀ : PO 3 1}
    (hrot : IsRotationAbout b₀ a b (2 * Real.pi / (M : ℝ)))
    (hstab : ∀ g : PO 3 1, g ∈ Γ → (∀ u : E 3, u ∈ geodSet a b → g • u = u) →
      (∃ k : ℤ, g = b₀ ^ k) ∨ ¬ IsOriented g) :
    ({c : PO 3 1 | c ∈ Cplus Γ b₀ a ∧ psi a b c = 0} : Set (PO 3 1)).ncard ≤ 2 * M := by
  have hord : orderOf b₀ = M := orderOfRotAbout hA hI a b ha hb hab M hM b₀ hrot
  have hone : IsOriented (1 : PO 3 1) := by
    have h := (ematMulDet.2.2.2.2 (1 : PO 3 1))
    rw [h, ematMulDet.2.1, Matrix.det_one]; norm_num
  have hfix_of_ker : ∀ c : PO 3 1, c ∈ Cplus Γ b₀ a → psi a b c = 0 →
      ∀ u : E 3, u ∈ geodSet a b → c • u = u :=
    fun c hc h0 => (psi_eq_zero_iff_fix hA hI ha hb hab hM hrot hc).mp h0
  haveI : Finite ↥(Subgroup.zpowers b₀) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hord]; exact hM.ne')
  have hzp_fin : (Subgroup.zpowers b₀ : Set (PO 3 1)).Finite :=
    Set.finite_coe_iff.mp inferInstance
  have hzp_card : (Subgroup.zpowers b₀ : Set (PO 3 1)).ncard = M := by
    rw [← Nat.card_coe_set_eq]
    show Nat.card (Subgroup.zpowers b₀) = M
    rw [Nat.card_zpowers, hord]
  by_cases hsub : ({c : PO 3 1 | c ∈ Cplus Γ b₀ a ∧ psi a b c = 0} : Set (PO 3 1)) ⊆
      (Subgroup.zpowers b₀ : Set (PO 3 1))
  · calc ({c : PO 3 1 | c ∈ Cplus Γ b₀ a ∧ psi a b c = 0} : Set (PO 3 1)).ncard
        ≤ (Subgroup.zpowers b₀ : Set (PO 3 1)).ncard := Set.ncard_le_ncard hsub hzp_fin
      _ = M := hzp_card
      _ ≤ 2 * M := by omega
  · obtain ⟨σ, hσker, hσnot⟩ := Set.not_subset.mp hsub
    have hσno : ¬ IsOriented σ := by
      rcases hstab σ hσker.1.1.2 (hfix_of_ker σ hσker.1 hσker.2) with ⟨k, hk⟩ | h
      · exact absurd (by rw [hk]; exact (Subgroup.mem_zpowers_iff (g := b₀) (h := b₀ ^ k)).mpr ⟨k, rfl⟩) hσnot
      · exact h
    have hσinvno : ¬ IsOriented σ⁻¹ := by
      have h1 : IsOriented (σ * σ⁻¹) := by rw [mul_inv_cancel]; exact hone
      rcases (isOriented_mul_iff hA σ σ⁻¹).mp h1 with ⟨h2a, -⟩ | ⟨-, h2b⟩
      · exact absurd h2a hσno
      · exact h2b
    have hcover : ({c : PO 3 1 | c ∈ Cplus Γ b₀ a ∧ psi a b c = 0} : Set (PO 3 1)) ⊆
        (Subgroup.zpowers b₀ : Set (PO 3 1)) ∪ (σ • (Subgroup.zpowers b₀ : Set (PO 3 1))) := by
      intro c hc
      by_cases hco : IsOriented c
      · left
        rcases hstab c hc.1.1.2 (hfix_of_ker c hc.1 hc.2) with ⟨k, hk⟩ | h
        · exact hk ▸ (Subgroup.mem_zpowers_iff (g := b₀) (h := b₀ ^ k)).mpr ⟨k, rfl⟩
        · exact absurd hco h
      · right
        have h1 : IsOriented (σ⁻¹ * c) :=
          (isOriented_mul_iff hA σ⁻¹ c).mpr (Or.inr ⟨hσinvno, hco⟩)
        have hmem : σ⁻¹ * c ∈ Γ :=
          (Subgroup.mul_mem _ (Subgroup.inv_mem _ hσker.1.1) hc.1.1).2
        have hσu : ∀ u : E 3, u ∈ geodSet a b → σ • u = u :=
          fun u hu => hfix_of_ker σ hσker.1 hσker.2 u hu
        have hcu : ∀ u : E 3, u ∈ geodSet a b → c • u = u :=
          fun u hu => hfix_of_ker c hc.1 hc.2 u hu
        have hfix : ∀ u : E 3, u ∈ geodSet a b → (σ⁻¹ * c) • u = u := by
          intro u hu
          calc (σ⁻¹ * c) • u = σ⁻¹ • (c • u) := (POBasic.ofProp hA).mul_smul σ⁻¹ c u
            _ = σ⁻¹ • u := by rw [hcu u hu]
            _ = σ⁻¹ • (σ • u) := by rw [hσu u hu]
            _ = (σ⁻¹ * σ) • u := ((POBasic.ofProp hA).mul_smul σ⁻¹ σ u).symm
            _ = u := by rw [inv_mul_cancel, (POBasic.ofProp hA).one_smul]
        rcases hstab (σ⁻¹ * c) hmem hfix with ⟨k, hk⟩ | h
        · refine Set.mem_smul_set.mpr ⟨b₀ ^ k,
            (Subgroup.mem_zpowers_iff (g := b₀) (h := b₀ ^ k)).mpr ⟨k, rfl⟩, ?_⟩
          rw [smul_eq_mul]
          have : c = σ * (σ⁻¹ * c) := by group
          rw [this, hk]
        · exact absurd h1 h
    have hunion_fin : ((Subgroup.zpowers b₀ : Set (PO 3 1)) ∪
        (σ • (Subgroup.zpowers b₀ : Set (PO 3 1)))).Finite :=
      hzp_fin.union (hzp_fin.smul_set (a := σ))
    have hsmul_card : (σ • (Subgroup.zpowers b₀ : Set (PO 3 1))).ncard =
        (Subgroup.zpowers b₀ : Set (PO 3 1)).ncard := by
      rw [← Set.image_smul]
      exact Set.ncard_image_of_injective _ (fun x y hxy => by
        have h : σ * x = σ * y := hxy
        exact mul_left_cancel h)
    calc ({c : PO 3 1 | c ∈ Cplus Γ b₀ a ∧ psi a b c = 0} : Set (PO 3 1)).ncard
        ≤ ((Subgroup.zpowers b₀ : Set (PO 3 1)) ∪
            (σ • (Subgroup.zpowers b₀ : Set (PO 3 1)))).ncard :=
          Set.ncard_le_ncard hcover hunion_fin
      _ ≤ (Subgroup.zpowers b₀ : Set (PO 3 1)).ncard +
            (σ • (Subgroup.zpowers b₀ : Set (PO 3 1))).ncard := Set.ncard_union_le _ _
      _ = M + M := by rw [hsmul_card, hzp_card]
      _ = 2 * M := by ring

/-- The kernel of `psi` on `C⁺` has at most `M` elements when `3 ≤ M`. -/
theorem card_ker_le_three (hA : Submission.Mostow.POActionProp 3)
    (hI : Submission.Mostow.HypIsometryProp 3) (Γ : Subgroup (PO 3 1))
    {a b : E 3} (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b)
    {M : ℕ} (hM : 3 ≤ M) {b₀ : PO 3 1}
    (hrot : IsRotationAbout b₀ a b (2 * Real.pi / (M : ℝ)))
    (hstab : ∀ g : PO 3 1, g ∈ Γ → (∀ u : E 3, u ∈ geodSet a b → g • u = u) →
      (∃ k : ℤ, g = b₀ ^ k) ∨ ¬ IsOriented g) :
    ({c : PO 3 1 | c ∈ Cplus Γ b₀ a ∧ psi a b c = 0} : Set (PO 3 1)).ncard ≤ M := by
  have hM0 : 0 < M := by omega
  have hord : orderOf b₀ = M := orderOfRotAbout hA hI a b ha hb hab M hM0 b₀ hrot
  have hsub : ({c : PO 3 1 | c ∈ Cplus Γ b₀ a ∧ psi a b c = 0} : Set (PO 3 1)) ⊆
      (Subgroup.zpowers b₀ : Set (PO 3 1)) := by
    intro c hc
    obtain ⟨k, hk⟩ := q0SubsetZpowers hA hI Γ a b ha hb hab M hM b₀ hrot hstab c hc.1.1
      ((psi_eq_zero_iff_fix hA hI ha hb hab hM0 hrot hc.1).mp hc.2)
    rw [hk]; exact (Subgroup.mem_zpowers_iff (g := b₀) (h := b₀ ^ k)).mpr ⟨k, rfl⟩
  haveI : Finite ↥(Subgroup.zpowers b₀) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hord]; omega)
  have hzp_fin : (Subgroup.zpowers b₀ : Set (PO 3 1)).Finite :=
    Set.finite_coe_iff.mp inferInstance
  calc ({c : PO 3 1 | c ∈ Cplus Γ b₀ a ∧ psi a b c = 0} : Set (PO 3 1)).ncard
      ≤ (Subgroup.zpowers b₀ : Set (PO 3 1)).ncard := Set.ncard_le_ncard hsub hzp_fin
    _ = M := by
      rw [← Nat.card_coe_set_eq]
      show Nat.card (Subgroup.zpowers b₀) = M
      rw [Nat.card_zpowers, hord]

/-! ## The tube has infinite volume -/

theorem tube_vol_top (hA : Submission.Mostow.POActionProp 3)
    (hI : Submission.Mostow.HypIsometryProp 3)
    (a b : E 3) (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b)
    {M : ℕ} (hM : 0 < M) {b₀ : PO 3 1}
    (hrot : IsRotationAbout b₀ a b (2 * Real.pi / (M : ℝ))) {R : ℝ} (hR : 0 < R) :
    volH 3 {u : E 3 | distGeod a b u ≤ R} = ⊤ := by
  have hgs : Measurable fun u : E 3 => sig a b u := tube_measurable_sig a b
  have hgd : Measurable fun u : E 3 => distGeod a b u := tube_measurable_distGeod a b
  have hmeas : ∀ n : ℤ, MeasurableSet
      {u : E 3 | sig a b u ∈ Set.Ico (n : ℝ) ((n : ℝ) + 1) ∧ distGeod a b u ≤ R} := by
    intro n
    exact (MeasurableSet.preimage measurableSet_Ico hgs).inter
      (MeasurableSet.preimage measurableSet_Iic hgd)
  have hdisjG : ∀ m n : ℤ, m ≠ n → Disjoint
      {u : E 3 | sig a b u ∈ Set.Ico (m : ℝ) ((m : ℝ) + 1) ∧ distGeod a b u ≤ R}
      {u : E 3 | sig a b u ∈ Set.Ico (n : ℝ) ((n : ℝ) + 1) ∧ distGeod a b u ≤ R} := by
    intro m n hmn
    rw [Set.disjoint_left]
    rintro u ⟨hu1, -⟩ ⟨hu2, -⟩
    have hmn' : (m : ℝ) < (n : ℝ) ∨ (n : ℝ) < (m : ℝ) := by
      rcases lt_or_gt_of_ne (fun h : (m : ℝ) = (n : ℝ) => hmn (by exact_mod_cast h)) with h | h
      · exact Or.inl h
      · exact Or.inr h
    rcases hmn' with h | h
    · have hmnZ : m < n := by exact_mod_cast h
      have hle : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast (show m + 1 ≤ n from by omega)
      linarith [hu1.2, hu2.1, hle]
    · have hmnZ : n < m := by exact_mod_cast h
      have hle : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast (show n + 1 ≤ m from by omega)
      linarith [hu2.2, hu1.1, hle]
  have hdisj : Pairwise (fun m n : ℤ => AEDisjoint (volH 3)
      {u : E 3 | sig a b u ∈ Set.Ico (m : ℝ) ((m : ℝ) + 1) ∧ distGeod a b u ≤ R}
      {u : E 3 | sig a b u ∈ Set.Ico (n : ℝ) ((n : ℝ) + 1) ∧ distGeod a b u ≤ R}) :=
    fun m n hmn => (hdisjG m n hmn).aedisjoint
  have hmain : ⊤ ≤ volH 3 {u : E 3 | distGeod a b u ≤ R} := by
    calc volH 3 {u : E 3 | distGeod a b u ≤ R}
      ≥ volH 3 (⋃ n : ℤ, {u : E 3 | sig a b u ∈ Set.Ico (n : ℝ) ((n : ℝ) + 1) ∧
          distGeod a b u ≤ R}) :=
        measure_mono (fun u hu => by
          rw [Set.mem_iUnion] at hu
          exact hu.choose_spec.2)
    _ = ∑' n : ℤ, volH 3 {u : E 3 | sig a b u ∈ Set.Ico (n : ℝ) ((n : ℝ) + 1) ∧
          distGeod a b u ≤ R} :=
        measure_iUnion₀ hdisj (fun n => (hmeas n).nullMeasurableSet)
    _ = ∑' _ : ℤ, ENNReal.ofReal (Real.pi * (Real.sinh R) ^ 2) := by
        refine tsum_congr (fun n => ?_)
        rw [volH3Slab hA hI a b ha hb hab M hM b₀ hrot (n : ℝ) 1 R (by norm_num) (le_of_lt hR)]
        norm_num
    _ = ⊤ := ENNReal.tsum_const_eq_top_of_ne_zero (by
        rw [ENNReal.ofReal_ne_zero_iff]
        exact mul_pos Real.pi_pos (pow_pos (Real.sinh_pos_iff.mpr hR) 2))
  exact le_antisymm le_top hmain

/-! ## The multiplicity bound for the slab -/

theorem slab_multiplicity (hA : Submission.Mostow.POActionProp 3)
    (hI : Submission.Mostow.HypIsometryProp 3) (Γ : Subgroup (PO 3 1))
    {a b : E 3} (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b)
    {M : ℕ} (hM : 0 < M) {b₀ : PO 3 1}
    (hrot : IsRotationAbout b₀ a b (2 * Real.pi / (M : ℝ)))
    {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hmin : ∀ c : PO 3 1, c ∈ Cplus Γ b₀ a → psi a b c ≠ 0 → ℓ ≤ |psi a b c|)
    (hKfin : ({c : PO 3 1 | c ∈ Cplus Γ b₀ a ∧ psi a b c = 0} : Set (PO 3 1)).Finite)
    (R : ℝ) (z : E 3) :
    ({c : PO 3 1 | c ∈ cent Γ b₀ ∧
        c • z ∈ {u : E 3 | sig a b u ∈ Set.Ico 0 ℓ ∧ distGeod a b u ≤ R}} : Set (PO 3 1)).Finite ∧
      ({c : PO 3 1 | c ∈ cent Γ b₀ ∧
        c • z ∈ {u : E 3 | sig a b u ∈ Set.Ico 0 ℓ ∧ distGeod a b u ≤ R}} : Set (PO 3 1)).ncard ≤
        2 * ({c : PO 3 1 | c ∈ Cplus Γ b₀ a ∧ psi a b c = 0} : Set (PO 3 1)).ncard := by
  classical
  set K : Set (PO 3 1) := {c : PO 3 1 | c ∈ Cplus Γ b₀ a ∧ psi a b c = 0} with hK
  set S : Set (E 3) := {u : E 3 | sig a b u ∈ Set.Ico 0 ℓ ∧ distGeod a b u ≤ R} with hS
  set T : Set (PO 3 1) := {c : PO 3 1 | c ∈ cent Γ b₀ ∧ c • z ∈ S} with hT
  have hK_mem : ∀ c : PO 3 1, c ∈ K ↔ c ∈ Cplus Γ b₀ a ∧ psi a b c = 0 := by
    intro c; rw [hK, Set.mem_setOf_eq]
  have hS_mem : ∀ u : E 3, u ∈ S ↔ sig a b u ∈ Set.Ico 0 ℓ ∧ distGeod a b u ≤ R := by
    intro u; rw [hS, Set.mem_setOf_eq]
  have hT_mem : ∀ c : PO 3 1, c ∈ T ↔ c ∈ cent Γ b₀ ∧ c • z ∈ S := by
    intro c; rw [hT, Set.mem_setOf_eq]
  have hsmul_le : ∀ {s t : Set (PO 3 1)} {c₁ : PO 3 1}, s ⊆ c₁ • t → t.Finite →
      s.Finite ∧ s.ncard ≤ t.ncard := by
    intro s t c₁ hsub ht
    have hfin : (c₁ • t).Finite := ht.smul_set (a := c₁)
    have hcard : (c₁ • t).ncard = t.ncard := by
      rw [← Set.image_smul]
      exact Set.ncard_image_of_injective _ (fun x y hxy => by
        have h : c₁ * x = c₁ * y := hxy
        exact mul_left_cancel h)
    exact ⟨hfin.subset hsub, le_trans (Set.ncard_le_ncard hsub hfin) (le_of_eq hcard)⟩
  -- the part of `T` fixing the endpoint `a`
  have hpart1 : (T ∩ Cplus Γ b₀ a).Finite ∧ (T ∩ Cplus Γ b₀ a).ncard ≤ K.ncard := by
    by_cases hne : (T ∩ Cplus Γ b₀ a).Nonempty
    · obtain ⟨c₁, hc₁⟩ := hne
      have hc₁T : c₁ ∈ cent Γ b₀ ∧ c₁ • z ∈ S := (hT_mem c₁).mp hc₁.1
      have hstep : ∀ c : PO 3 1, c ∈ T → c ∈ Cplus Γ b₀ a →
          psi a b c ∈ Set.Ico (-(sig a b z)) (ℓ - sig a b z) := by
        intro c hc hcp
        have hcT : c ∈ cent Γ b₀ ∧ c • z ∈ S := (hT_mem c).mp hc
        have h1 := sig_smul_of_mem_cent hA hI ha hb hab hM hrot hcT.1 z
        rw [eps_eq_one_of_mem_Cplus hcp, one_mul] at h1
        have h2 : sig a b (c • z) ∈ Set.Ico 0 ℓ := ((hS_mem (c • z)).mp hcT.2).1
        rw [h1] at h2
        exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
      have hkey : ∀ c ∈ T ∩ Cplus Γ b₀ a, psi a b c = psi a b c₁ := by
        intro c hc
        have hbdd := hstep c hc.1 hc.2
        have hbdd₁ := hstep c₁ hc₁.1 hc₁.2
        by_contra hne'
        have hcT : c ∈ cent Γ b₀ ∧ c • z ∈ S := (hT_mem c).mp hc.1
        have heps : eps a c = eps a c₁ := by
          rw [eps_eq_one_of_mem_Cplus hc.2, eps_eq_one_of_mem_Cplus hc₁.2]
        have hmem := (psi_mul_inv_of_same_eps hA hI ha hb hab hM hrot hcT.1 hc₁T.1 heps).1
        have hprod := (psi_mul_inv_of_same_eps hA hI ha hb hab hM hrot hcT.1 hc₁T.1 heps).2
        have hne0 : psi a b (c * c₁⁻¹) ≠ 0 := by
          rw [hprod]; intro h0; exact hne' (by linarith)
        have hle := hmin (c * c₁⁻¹) hmem hne0
        have hlt : |psi a b c - psi a b c₁| < ℓ := by
          rw [abs_lt]
          exact ⟨by linarith [hbdd₁.2, hbdd.1], by linarith [hbdd.2, hbdd₁.1]⟩
        rw [hprod] at hle
        linarith
      have hsub : T ∩ Cplus Γ b₀ a ⊆ c₁ • K := by
        intro c hc
        have hψ := hkey c hc
        have hcT : c ∈ cent Γ b₀ ∧ c • z ∈ S := (hT_mem c).mp hc.1
        have heps : eps a c = eps a c₁ := by
          rw [eps_eq_one_of_mem_Cplus hc.2, eps_eq_one_of_mem_Cplus hc₁.2]
        obtain ⟨hmem, hzero⟩ :=
          psi_inv_mul_of_same_eps hA hI ha hb hab hM hrot hcT.1 hc₁T.1 heps hψ
        refine Set.mem_smul_set.mpr ⟨c₁⁻¹ * c, ?_, ?_⟩
        · rw [hK_mem]; exact ⟨hmem, hzero⟩
        · rw [smul_eq_mul]; group
      exact hsmul_le hsub hKfin
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      refine ⟨?_, ?_⟩
      · rw [hne]; exact Set.finite_empty
      · rw [hne, Set.ncard_empty]; exact Nat.zero_le _
  -- the part of `T` reversing the axis
  have hpart2 : (T ∩ (Cplus Γ b₀ a)ᶜ).Finite ∧ (T ∩ (Cplus Γ b₀ a)ᶜ).ncard ≤ K.ncard := by
    by_cases hne : (T ∩ (Cplus Γ b₀ a)ᶜ).Nonempty
    · obtain ⟨c₁, hc₁⟩ := hne
      have hc₁T : c₁ ∈ cent Γ b₀ ∧ c₁ • z ∈ S := (hT_mem c₁).mp hc₁.1
      have hc₁rev : bd c₁ a = b := by
        rcases (bd_pair_of_mem_cent hA hI ha hb hab hM hrot hc₁T.1).1 with h | h
        · exact absurd ⟨hc₁T.1, h⟩ hc₁.2
        · exact h
      have hstep : ∀ c : PO 3 1, c ∈ T → c ∉ Cplus Γ b₀ a →
          psi a b c ∈ Set.Ico (sig a b z) (sig a b z + ℓ) := by
        intro c hc hcn
        have hcT : c ∈ cent Γ b₀ ∧ c • z ∈ S := (hT_mem c).mp hc
        have hcrev : bd c a = b := by
          rcases (bd_pair_of_mem_cent hA hI ha hb hab hM hrot hcT.1).1 with h | h
          · exact absurd ⟨hcT.1, h⟩ hcn
          · exact h
        have h1 := sig_smul_of_mem_cent hA hI ha hb hab hM hrot hcT.1 z
        rw [eps_eq_neg_one_iff.mpr (fun hcon => hab ((hcrev.symm.trans hcon).symm)),
          neg_one_mul] at h1
        have h2 : sig a b (c • z) ∈ Set.Ico 0 ℓ := ((hS_mem (c • z)).mp hcT.2).1
        rw [h1] at h2
        exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
      have hkey : ∀ c ∈ T ∩ (Cplus Γ b₀ a)ᶜ, psi a b c = psi a b c₁ := by
        intro c hc
        have hbdd := hstep c hc.1 hc.2
        have hbdd₁ := hstep c₁ hc₁.1 hc₁.2
        by_contra hne'
        have hcT : c ∈ cent Γ b₀ ∧ c • z ∈ S := (hT_mem c).mp hc.1
        have hcrev : bd c a = b := by
          rcases (bd_pair_of_mem_cent hA hI ha hb hab hM hrot hcT.1).1 with h | h
          · exact absurd ⟨hcT.1, h⟩ hc.2
          · exact h
        have heps : eps a c = eps a c₁ := by
          rw [eps_eq_neg_one_iff.mpr (fun hcon => hab ((hcrev.symm.trans hcon).symm)),
            eps_eq_neg_one_iff.mpr (fun hcon => hab ((hc₁rev.symm.trans hcon).symm))]
        have hmem := (psi_mul_inv_of_same_eps hA hI ha hb hab hM hrot hcT.1 hc₁T.1 heps).1
        have hprod := (psi_mul_inv_of_same_eps hA hI ha hb hab hM hrot hcT.1 hc₁T.1 heps).2
        have hne0 : psi a b (c * c₁⁻¹) ≠ 0 := by
          rw [hprod]; intro h0; exact hne' (by linarith)
        have hle := hmin (c * c₁⁻¹) hmem hne0
        have hlt : |psi a b c - psi a b c₁| < ℓ := by
          rw [abs_lt]
          exact ⟨by linarith [hbdd₁.2, hbdd.1], by linarith [hbdd.2, hbdd₁.1]⟩
        rw [hprod] at hle
        linarith
      have hsub : T ∩ (Cplus Γ b₀ a)ᶜ ⊆ c₁ • K := by
        intro c hc
        have hψ := hkey c hc
        have hcT : c ∈ cent Γ b₀ ∧ c • z ∈ S := (hT_mem c).mp hc.1
        have hcrev : bd c a = b := by
          rcases (bd_pair_of_mem_cent hA hI ha hb hab hM hrot hcT.1).1 with h | h
          · exact absurd ⟨hcT.1, h⟩ hc.2
          · exact h
        have heps : eps a c = eps a c₁ := by
          rw [eps_eq_neg_one_iff.mpr (fun hcon => hab ((hcrev.symm.trans hcon).symm)),
            eps_eq_neg_one_iff.mpr (fun hcon => hab ((hc₁rev.symm.trans hcon).symm))]
        obtain ⟨hmem, hzero⟩ :=
          psi_inv_mul_of_same_eps hA hI ha hb hab hM hrot hcT.1 hc₁T.1 heps hψ
        refine Set.mem_smul_set.mpr ⟨c₁⁻¹ * c, ?_, ?_⟩
        · rw [hK_mem]; exact ⟨hmem, hzero⟩
        · rw [smul_eq_mul]; group
      exact hsmul_le hsub hKfin
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      refine ⟨?_, ?_⟩
      · rw [hne]; exact Set.finite_empty
      · rw [hne, Set.ncard_empty]; exact Nat.zero_le _
  have hTsub : T ⊆ (T ∩ Cplus Γ b₀ a) ∪ (T ∩ (Cplus Γ b₀ a)ᶜ) := by
    intro c hc
    by_cases h : c ∈ Cplus Γ b₀ a
    · exact Or.inl ⟨hc, h⟩
    · exact Or.inr ⟨hc, h⟩
  refine ⟨?_, ?_⟩
  · exact (hpart1.1.union hpart2.1).subset hTsub
  · calc T.ncard ≤ ((T ∩ Cplus Γ b₀ a) ∪ (T ∩ (Cplus Γ b₀ a)ᶜ)).ncard :=
        Set.ncard_le_ncard hTsub (hpart1.1.union hpart2.1)
      _ ≤ (T ∩ Cplus Γ b₀ a).ncard + (T ∩ (Cplus Γ b₀ a)ᶜ).ncard := Set.ncard_union_le _ _
      _ ≤ K.ncard + K.ncard := add_le_add hpart1.2 hpart2.2
      _ = 2 * K.ncard := by ring

/-! ## S9: the tube inequality -/

/-- S9 of the n=3 gap-A design. `Γ` lattice, `b₀ ∈ Γ` the `2π/M`-rotation about the geodesic `X = geodSet a b`; `C := Subgroup.centralizer {b₀} ⊓ Γ` preserves `X`; `Tb b₀ η₁ = {w | NearIdAt b₀ w η₁}`; `ρ>0`, `2 sinh (ρ+1) sin (π/M) ≤ η₁`. Conclusion (dichotomy): either some `g ∈ C` translates `X` by `ℓ>0` and some fundamental domain `Dc` of `C` has `volH 3 (Tb b₀ η₁ ∩ Dc) ≥ ℓ(π/M)sinh²ρ/2`, or every fundamental domain `Dc` of `C` has `volH 3 (Tb b₀ η₁ ∩ Dc) = ⊤`. Strategy: (i) `{distGeod a b ≤ ρ} ⊆ Tb b₀ η₁`; (ii) conjugate the axis to the standard geodesic and use `fermi`/`tubeMeasure`/`fermi_measurePreserving` for the volume computations; (iii) no translation in `C` ⟹ (by `hstab`, at most `2M` pointwise fixers plus one reflection coset) `C` is finite, so `Tb` is `C`-invariant and has infinite volume in every fundamental domain; (iv) a translation `ℓ` in `C` gives a fundamental domain of `⟨g, b₀⟩` consisting of a strip in Fermi coordinates, whose tube volume is `ℓ(2π/k)sinh²ρ/2 ≥ ℓ(π/M)sinh²ρ/2` with `k ≤ 2M`. -/
theorem tubeIneq3 (hA : Submission.Mostow.POActionProp 3) (hI : Submission.Mostow.HypIsometryProp 3)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO 3 1)) (hΓ : Submission.Mostow.HypLattice Γ)
    (a b : Submission.Mostow.E 3) (ha : a ∈ Submission.Mostow.Sph 3) (hb : b ∈ Submission.Mostow.Sph 3)
    (hab : a ≠ b) (M : ℕ) (hM : 0 < M) (b₀ : LeanEval.Geometry.MostowRigidity.PO 3 1)
    (hb₀ : b₀ ∈ Γ) (hrot : Work.Mostow.IsRotationAbout b₀ a b (2 * Real.pi / (M : ℝ)))
    (hstab : ∀ g : LeanEval.Geometry.MostowRigidity.PO 3 1, g ∈ Γ →
      (∀ u : Submission.Mostow.E 3, u ∈ Work.Mostow.geodSet a b → g • u = u) →
      (∃ k : ℤ, g = b₀ ^ k) ∨ ¬ Work.Mostow.IsOriented g)
    (D : Set (Submission.Mostow.E 3)) (hD : MeasureTheory.IsFundamentalDomain ↥Γ D (Submission.Mostow.volH 3))
    (η₁ : ℝ) (hη₁ : 0 < η₁) (ρ : ℝ) (hρ : 0 < ρ)
    (hρtube : 2 * Real.sinh (ρ + 1) * Real.sin (Real.pi / (M : ℝ)) ≤ η₁) :
    (∃ (g : LeanEval.Geometry.MostowRigidity.PO 3 1) (ℓ : ℝ) (Dc : Set (Submission.Mostow.E 3)),
        0 < ℓ ∧ g ∈ Subgroup.centralizer ({b₀} : Set (LeanEval.Geometry.MostowRigidity.PO 3 1)) ⊓ Γ ∧
        (∀ u : Submission.Mostow.E 3, u ∈ Work.Mostow.geodSet a b → Submission.Mostow.hdist u (g • u) = ℓ) ∧
        MeasureTheory.IsFundamentalDomain ↥(Subgroup.centralizer ({b₀} : Set (LeanEval.Geometry.MostowRigidity.PO 3 1)) ⊓ Γ) Dc
          (Submission.Mostow.volH 3) ∧
        ENNReal.ofReal (ℓ * (Real.pi / (M : ℝ)) * (Real.sinh ρ) ^ 2 / 2) ≤
          Submission.Mostow.volH 3 (Work.Mostow.Tb b₀ η₁ ∩ Dc)) ∨
    (∀ Dc : Set (Submission.Mostow.E 3),
      MeasureTheory.IsFundamentalDomain ↥(Subgroup.centralizer ({b₀} : Set (LeanEval.Geometry.MostowRigidity.PO 3 1)) ⊓ Γ) Dc
        (Submission.Mostow.volH 3) →
      Submission.Mostow.volH 3 (Work.Mostow.Tb b₀ η₁ ∩ Dc) = ⊤) := by
  classical
  have hP := POBasic.ofProp hA
  have hJ := HypIsoData.ofProp hI
  letI : MulAction (PO 3 1) (E 3) := { one_smul := hP.one_smul, mul_smul := hP.mul_smul }
  have hdisc : IsDiscrete (SetLike.coe Γ) := hΓ.1
  have hgf := geodFacts 3 (by norm_num) hA hI a b ha hb hab
  obtain ⟨u₀, hu₀⟩ := hgf.1
  have hM2 : 2 ≤ M := by
    by_contra hcon
    have hM1 : M = 1 := by omega
    subst hM1
    have hdisp0 : ∀ u : E 3, hdist u (b₀ • u) = 0 := by
      intro u
      rw [hrot.2 u]
      have h2 : (2 * Real.pi / ((1 : ℕ) : ℝ)) / 2 = Real.pi := by norm_num
      rw [h2, Real.sin_pi, mul_zero, Real.arsinh_zero, mul_zero]
    have hone : b₀ = 1 := hP.faithful b₀ (fun u => ((hJ.eq_zero u (b₀ • u)).mp (hdisp0 u)).symm)
    obtain ⟨uw, -, h2⟩ := hgf.2.2.2.2 u₀
    have h3 : distGeod a b uw = 0 := by
      rw [hgf.2.2.1]
      exact (hrot.1 uw).mp (by rw [hone, hP.one_smul])
    linarith
  have hsinpos : 0 < Real.sin (Real.pi / (M : ℝ)) := by
    have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
    have h1 : 0 < Real.pi / (M : ℝ) := div_pos Real.pi_pos hMpos
    have h2 : Real.pi / (M : ℝ) < Real.pi := by
      rw [div_lt_iff₀ hMpos]
      have hM2' : (2 : ℝ) ≤ M := by exact_mod_cast hM2
      nlinarith [Real.pi_pos]
    exact Real.sin_pos_of_pos_of_lt_pi h1 h2
  have hρin : 2 * Real.arsinh (Real.sinh (ρ + 1) * Real.sin (Real.pi / (M : ℝ))) < η₁ := by
    have hpos : 0 < Real.sinh (ρ + 1) * Real.sin (Real.pi / (M : ℝ)) :=
      mul_pos (Real.sinh_pos_iff.mpr (by linarith)) hsinpos
    have h2 : Real.sinh (Real.arsinh (Real.sinh (ρ + 1) * Real.sin (Real.pi / (M : ℝ)))) <
        Real.sinh (Real.sinh (ρ + 1) * Real.sin (Real.pi / (M : ℝ))) := by
      rw [Real.sinh_arsinh]
      exact Real.self_lt_sinh_iff.mpr hpos
    have h1 : Real.arsinh (Real.sinh (ρ + 1) * Real.sin (Real.pi / (M : ℝ))) <
        Real.sinh (ρ + 1) * Real.sin (Real.pi / (M : ℝ)) := Real.sinh_lt_sinh.mp h2
    linarith
  by_cases hcase : ∃ c : LeanEval.Geometry.MostowRigidity.PO 3 1,
      c ∈ Cplus Γ b₀ a ∧ psi a b c ≠ 0
  · -- ================= Case A =================
    obtain ⟨c₀, hc₀, hψ₀⟩ := hcase
    have hsetfin : ({c : PO 3 1 |
        c ∈ Cplus Γ b₀ a ∧ psi a b c ≠ 0 ∧ |psi a b c| ≤ |psi a b c₀|}).Finite :=
      (finite_psi_small hA hI Γ hdisc ha hb hab hM hrot |psi a b c₀|).subset
        (fun c hc => ⟨hc.1, hc.2.2⟩)
    obtain ⟨g, hgmem, hgmin⟩ :=
      Set.exists_min_image _ (fun c : PO 3 1 => |psi a b c|) hsetfin ⟨c₀, hc₀, hψ₀, le_rfl⟩
    have hgC : g ∈ Cplus Γ b₀ a := hgmem.1
    have hgψ : psi a b g ≠ 0 := hgmem.2.1
    set ℓ : ℝ := |psi a b g| with hℓdef
    have hℓpos : 0 < ℓ := by rw [hℓdef]; exact abs_pos.mpr hgψ
    have hmin : ∀ c : PO 3 1, c ∈ Cplus Γ b₀ a → psi a b c ≠ 0 → ℓ ≤ |psi a b c| := by
      intro c hc hcψ
      rw [hℓdef]
      by_cases hle : |psi a b c| ≤ |psi a b c₀|
      · exact hgmin c ⟨hc, hcψ, hle⟩
      · push_neg at hle
        exact le_trans hgmem.2.2 hle.le
    have hKfin : ({c : PO 3 1 | c ∈ Cplus Γ b₀ a ∧ psi a b c = 0} : Set (PO 3 1)).Finite :=
      (finite_psi_small hA hI Γ hdisc ha hb hab hM hrot 0).subset
        (fun c hc => ⟨hc.1, by rw [hc.2]; simp⟩)
    set K : Set (PO 3 1) := {c : PO 3 1 | c ∈ Cplus Γ b₀ a ∧ psi a b c = 0} with hKdef
    -- the radius
    set R : ℝ := max ρ (η₁ / 2 - 1 - 1/50) with hRdef
    have hRge : ρ ≤ R := le_max_left _ _
    have hRpos : 0 < R := lt_of_lt_of_le hρ hRge
    have hRin : 2 * Real.arsinh (Real.sinh (R + 1) * Real.sin (Real.pi / (M : ℝ))) < η₁ := by
      have hs1 : Real.sin (Real.pi / (M : ℝ)) ≤ 1 := Real.sin_le_one _
      have hs0 : 0 ≤ Real.sin (Real.pi / (M : ℝ)) := hsinpos.le
      have hkey : Real.sinh (R + 1) * Real.sin (Real.pi / (M : ℝ)) < Real.sinh (η₁ / 2) := by
        rcases max_cases ρ (η₁ / 2 - 1 - 1/50) with ⟨he, -⟩ | ⟨he, -⟩
        · have hRR : R + 1 = ρ + 1 := by rw [hRdef, he]
          rw [hRR]
          calc Real.sinh (ρ + 1) * Real.sin (Real.pi / (M : ℝ)) ≤ η₁ / 2 := by linarith [hρtube]
            _ < Real.sinh (η₁ / 2) := Real.self_lt_sinh_iff.mpr (by linarith)
        · have hRR : R + 1 = η₁ / 2 - 1/50 := by rw [hRdef, he]; ring
          rw [hRR]
          rcases lt_or_ge 0 (Real.sinh (η₁ / 2 - 1/50)) with hpos | hneg
          · calc Real.sinh (η₁ / 2 - 1/50) * Real.sin (Real.pi / (M : ℝ))
                ≤ Real.sinh (η₁ / 2 - 1/50) * 1 := mul_le_mul_of_nonneg_left hs1 hpos.le
              _ = Real.sinh (η₁ / 2 - 1/50) := mul_one _
              _ < Real.sinh (η₁ / 2) := Real.sinh_lt_sinh.mpr (by linarith)
          · calc Real.sinh (η₁ / 2 - 1/50) * Real.sin (Real.pi / (M : ℝ))
                ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hs0
              _ < Real.sinh (η₁ / 2) := Real.sinh_pos_iff.mpr (by linarith)
      have harsinh : Real.arsinh (Real.sinh (R + 1) * Real.sin (Real.pi / (M : ℝ))) < η₁ / 2 :=
        calc Real.arsinh (Real.sinh (R + 1) * Real.sin (Real.pi / (M : ℝ)))
            < Real.arsinh (Real.sinh (η₁ / 2)) :=
              Real.arsinh_lt_arsinh.mpr hkey
          _ = η₁ / 2 := Real.arsinh_sinh (η₁ / 2)
      linarith
    -- the slab and its volume
    set S : Set (E 3) := {u : E 3 | sig a b u ∈ Set.Ico 0 ℓ ∧ distGeod a b u ≤ R} with hSdef
    have hSmeas : MeasurableSet S := by
      rw [hSdef]
      exact (MeasurableSet.preimage measurableSet_Ico (tube_measurable_sig a b)).inter
        (MeasurableSet.preimage measurableSet_Iic (tube_measurable_distGeod a b))
    have hSsub : S ⊆ Tb b₀ η₁ := by
      rw [hSdef]
      intro u hu
      exact tubeSubsetTb hA hI a b ha hb hab M hM b₀ hrot η₁ R hη₁ hRin hu.2
    have hvolS : volH 3 S = ENNReal.ofReal (ℓ * Real.pi * (Real.sinh R) ^ 2) := by
      rw [hSdef]
      simpa using volH3Slab hA hI a b ha hb hab M hM b₀ hrot 0 ℓ R hℓpos.le hRpos.le
    -- the fundamental domain of the centraliser
    have hdiscC : IsDiscrete (SetLike.coe (Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ)) :=
      IsDiscrete.mono hdisc (fun c hc => hc.2)
    obtain ⟨Dc, hDc⟩ := exists_fundamentalDomain hA hI (Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ) hdiscC
    haveI hcountC : Countable ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ) :=
      Work.Mostow.countable_of_isDiscrete (PO 3 1) hdiscC
    haveI : MeasurableConstSMul ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ) (E 3) :=
      ⟨fun c => by
        show Measurable (fun x : E 3 => (c : PO 3 1) • x)
        exact ((hJ.contDiff_smul (c : PO 3 1)).continuous).measurable⟩
    haveI : SMulInvariantMeasure ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ) (E 3) (volH 3) :=
      ⟨fun c s hs => by
        show volH 3 ((fun x : E 3 => (c : PO 3 1) • x) ⁻¹' s) = volH 3 s
        exact (hJ.measurePreserving_smul (c : PO 3 1)).measure_preimage hs.nullMeasurableSet⟩
    have hTinv : ∀ c : ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ), ∀ x : E 3, x ∈ Tb b₀ η₁ ↔ c • x ∈ Tb b₀ η₁ := by
      intro c x
      show x ∈ Tb b₀ η₁ ↔ (c : PO 3 1) • x ∈ Tb b₀ η₁
      have hc : (c : PO 3 1) ∈ cent Γ b₀ := c.2
      have hcomm : (c : PO 3 1)⁻¹ * b₀ * (c : PO 3 1) = b₀ := by
        have hb : b₀ * (c : PO 3 1) = (c : PO 3 1) * b₀ := comm_of_mem_cent hc
        calc (c : PO 3 1)⁻¹ * b₀ * (c : PO 3 1)
            = (c : PO 3 1)⁻¹ * (b₀ * (c : PO 3 1)) := by group
          _ = (c : PO 3 1)⁻¹ * ((c : PO 3 1) * b₀) := by rw [hb]
          _ = b₀ := by group
      have h1 := nearIdAt_conj3 hA hI b₀ (c : PO 3 1) x η₁
      rw [hcomm] at h1
      exact h1.symm
    have hmult : ∀ z : E 3, {c : ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ) | c • z ∈ S}.Finite ∧
        {c : ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ) | c • z ∈ S}.ncard ≤ 2 * K.ncard := by
      intro z
      have h1 := slab_multiplicity hA hI Γ ha hb hab hM hrot hℓpos hmin hKfin R z
      have hinj : Set.InjOn (fun c : ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ) => (c : PO 3 1))
          {c : ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ) | c • z ∈ S} :=
        fun a _ b _ h => Subtype.ext h
      have himg : (fun c : ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ) => (c : PO 3 1)) ''
            {c : ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ) | c • z ∈ S} ⊆
            {c : PO 3 1 | c ∈ cent Γ b₀ ∧ c • z ∈ S} := by
        rintro d ⟨c, hc, rfl⟩
        exact ⟨c.2, hc⟩
      have hfin : {c : ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ) | c • z ∈ S}.Finite :=
        Set.Finite.of_finite_image (h1.1.subset himg) hinj
      refine ⟨hfin, ?_⟩
      have hcard : {c : ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ) | c • z ∈ S}.ncard =
          {c : PO 3 1 | c ∈ cent Γ b₀ ∧ c • z ∈ S}.ncard := by
        rw [← Set.ncard_image_of_injective _ (fun a b h => Subtype.ext h)]
        congr 1
        ext d
        constructor
        · rintro ⟨c, hc, rfl⟩; exact ⟨c.2, hc⟩
        · rintro ⟨hc, hz⟩; exact ⟨⟨d, hc⟩, hz, rfl⟩
      rw [hcard]
      exact h1.2
    have hpack := packMeasureLe (G := ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ)) (α := E 3) (μ := volH 3)
      (K := 2 * K.ncard) (D := Dc) (T := Tb b₀ η₁) (S := S)
      (fun c => by
        show Measurable (fun x : E 3 => (c : PO 3 1) • x)
        exact ((hJ.contDiff_smul (c : PO 3 1)).continuous).measurable)
      hDc (fun c x => hTinv c x) hSsub hSmeas.nullMeasurableSet hmult
    refine Or.inl ⟨g, ℓ, Dc, hℓpos, hgC.1, ?_, hDc, ?_⟩
    · -- the translation property
      intro u hu
      have h1 := sig_smul_of_mem_cent hA hI ha hb hab hM hrot hgC.1 u
      rw [eps_eq_one_of_mem_Cplus hgC, one_mul] at h1
      have h2 : hdist u (g • u) = |sig a b u - sig a b (g • u)| :=
        sigIsometryGeodSet hA hI a b ha hb hab u (g • u) hu
          ((cent_preserves_geodSet hA hM hrot hgC.1 u).mpr hu)
      rw [h2, h1]
      have h3 : sig a b u - (sig a b u + psi a b g) = -psi a b g := by ring
      rw [h3, abs_neg, hℓdef]
    · -- the volume bound
      have hKpos : 0 < K.ncard := by
        refine (Set.ncard_pos ?_).mpr ⟨1, ?_⟩
        · rw [hKdef]; exact hKfin
        · rw [hKdef]; exact ⟨one_mem_Cplus hA ha, psi_one hA a b⟩
      have ha0 : 0 ≤ ℓ * (Real.pi / (M : ℝ)) * (Real.sinh ρ) ^ 2 / 2 := by
        have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
        exact div_nonneg (mul_nonneg (mul_nonneg hℓpos.le (div_nonneg Real.pi_pos.le hMpos.le))
          (sq_nonneg _)) (by norm_num)
      have hreal : ((2 * K.ncard : ℕ) : ℝ) *
          (ℓ * (Real.pi / (M : ℝ)) * (Real.sinh ρ) ^ 2 / 2) ≤ ℓ * Real.pi * (Real.sinh R) ^ 2 := by
        rcases lt_or_ge 2 M with hM3 | hM2le
        · -- `3 ≤ M`
          have hKle : K.ncard ≤ M := by
            rw [hKdef]
            exact card_ker_le_three hA hI Γ ha hb hab hM3 hrot hstab
          have hKleR : ((2 * K.ncard : ℕ) : ℝ) ≤ 2 * M := by
            have h1 : (K.ncard : ℝ) ≤ (M : ℝ) := by exact_mod_cast hKle
            push_cast
            linarith
          have hstep3 : ℓ * Real.pi * (Real.sinh ρ) ^ 2 ≤ ℓ * Real.pi * (Real.sinh R) ^ 2 := by
            have h1 : Real.sinh ρ ≤ Real.sinh R := Real.sinh_le_sinh.mpr hRge
            have h2 : (Real.sinh ρ) ^ 2 ≤ (Real.sinh R) ^ 2 :=
              pow_le_pow_left₀ (Real.sinh_pos_iff.mpr hρ).le h1 2
            calc ℓ * Real.pi * (Real.sinh ρ) ^ 2 = (Real.sinh ρ) ^ 2 * (ℓ * Real.pi) := by ring
              _ ≤ (Real.sinh R) ^ 2 * (ℓ * Real.pi) :=
                  mul_le_mul_of_nonneg_right h2 (mul_nonneg hℓpos.le Real.pi_pos.le)
              _ = ℓ * Real.pi * (Real.sinh R) ^ 2 := by ring
          calc ((2 * K.ncard : ℕ) : ℝ) * (ℓ * (Real.pi / (M : ℝ)) * (Real.sinh ρ) ^ 2 / 2)
              ≤ (2 * M) * (ℓ * (Real.pi / (M : ℝ)) * (Real.sinh ρ) ^ 2 / 2) :=
                mul_le_mul_of_nonneg_right hKleR ha0
            _ = ℓ * Real.pi * (Real.sinh ρ) ^ 2 := by
                have hM0 : ((M : ℝ)) ≠ 0 := by
                  have h0 : (0 : ℝ) < M := by exact_mod_cast hM
                  linarith
                field_simp
            _ ≤ ℓ * Real.pi * (Real.sinh R) ^ 2 := hstep3
        · -- `M = 2`
          have hMeq : M = 2 := le_antisymm hM2le hM2
          have hKle4 : K.ncard ≤ 4 := by
            have h1 : K.ncard ≤ 2 * M := by
              rw [hKdef]
              exact card_ker_le hA hI Γ ha hb hab hM hrot hstab
            omega
          have hKleR : ((2 * K.ncard : ℕ) : ℝ) ≤ 8 := by
            have h1 : (K.ncard : ℝ) ≤ 4 := by exact_mod_cast hKle4
            push_cast
            linarith
          have hρtube2 : 2 * Real.sinh (ρ + 1) ≤ η₁ := by
            have h1 := hρtube
            rw [hMeq] at h1
            simpa only [Nat.cast_ofNat, Real.sin_pi_div_two, mul_one] using h1
          have hRbig : Real.sqrt 2 * Real.sinh ρ ≤ Real.sinh R := by
            have h3 : Real.sinh (ρ + 1) - 1 - 1/50 ≤ R := by
              rw [hRdef]
              have h4 := le_max_right ρ (η₁ / 2 - 1 - 1/50)
              linarith
            have h5 : Real.sqrt 2 * Real.sinh ρ + 1.05 ≤ Real.sinh (ρ + 1) :=
              sqrtTwoSinhAdd ρ hρ.le
            have h6 : Real.sqrt 2 * Real.sinh ρ ≤ Real.sinh (Real.sinh (ρ + 1) - 1 - 1/50) := by
              have h7 : Real.sqrt 2 * Real.sinh ρ ≤ Real.sinh (ρ + 1) - 1 - 1/50 := by linarith
              have h8 : 0 ≤ Real.sinh (ρ + 1) - 1 - 1/50 := by
                have h9 : 0 ≤ Real.sqrt 2 * Real.sinh ρ :=
                  mul_nonneg (Real.sqrt_nonneg 2) (Real.sinh_pos_iff.mpr hρ).le
                linarith
              exact le_trans h7 (Real.self_le_sinh_iff.mpr h8)
            calc Real.sqrt 2 * Real.sinh ρ ≤ Real.sinh (Real.sinh (ρ + 1) - 1 - 1/50) := h6
              _ ≤ Real.sinh R := Real.sinh_le_sinh.mpr h3
          have hsq : 2 * (Real.sinh ρ) ^ 2 ≤ (Real.sinh R) ^ 2 := by
            have h1 : (Real.sqrt 2 * Real.sinh ρ) ^ 2 ≤ (Real.sinh R) ^ 2 :=
              pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg 2) (Real.sinh_pos_iff.mpr hρ).le)
                hRbig 2
            have h2 : (Real.sqrt 2 * Real.sinh ρ) ^ 2 = 2 * (Real.sinh ρ) ^ 2 := by
              rw [mul_pow, Real.sq_sqrt (by norm_num)]
            rwa [h2] at h1
          rw [hMeq]
          have ha0' : 0 ≤ ℓ * (Real.pi / ((2 : ℕ) : ℝ)) * (Real.sinh ρ) ^ 2 / 2 := by
            simpa [hMeq] using ha0
          calc ((2 * K.ncard : ℕ) : ℝ) * (ℓ * (Real.pi / ((2 : ℕ) : ℝ)) * (Real.sinh ρ) ^ 2 / 2)
              ≤ 8 * (ℓ * (Real.pi / ((2 : ℕ) : ℝ)) * (Real.sinh ρ) ^ 2 / 2) :=
                mul_le_mul_of_nonneg_right hKleR ha0'
            _ = 2 * (ℓ * Real.pi * (Real.sinh ρ) ^ 2) := by
                ring
            _ ≤ ℓ * Real.pi * (Real.sinh R) ^ 2 := by
                calc 2 * (ℓ * Real.pi * (Real.sinh ρ) ^ 2)
                    = (ℓ * Real.pi) * (2 * (Real.sinh ρ) ^ 2) := by ring
                  _ ≤ (ℓ * Real.pi) * (Real.sinh R) ^ 2 :=
                      mul_le_mul_of_nonneg_left hsq (mul_nonneg hℓpos.le Real.pi_pos.le)
                  _ = ℓ * Real.pi * (Real.sinh R) ^ 2 := by ring
      have hKN0 : (((2 * K.ncard : ℕ)) : ℝ≥0∞) ≠ 0 := by
        exact_mod_cast (show (2 * K.ncard : ℕ) ≠ 0 by omega)
      have hKNtop : (((2 * K.ncard : ℕ)) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
      have hpack' : ENNReal.ofReal (ℓ * Real.pi * (Real.sinh R) ^ 2) ≤
          (((2 * K.ncard : ℕ)) : ℝ≥0∞) * volH 3 (Tb b₀ η₁ ∩ Dc) := by
        rw [← hvolS]
        exact hpack
      have h2 : (((2 * K.ncard : ℕ)) : ℝ≥0∞) *
          ENNReal.ofReal (ℓ * (Real.pi / (M : ℝ)) * (Real.sinh ρ) ^ 2 / 2) ≤
          ENNReal.ofReal (ℓ * Real.pi * (Real.sinh R) ^ 2) := by
        rw [← ENNReal.ofReal_natCast (2 * K.ncard),
          ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ ((2 * K.ncard : ℕ) : ℝ) by positivity)]
        exact ENNReal.ofReal_le_ofReal hreal
      have h3 : (((2 * K.ncard : ℕ)) : ℝ≥0∞) *
          ENNReal.ofReal (ℓ * (Real.pi / (M : ℝ)) * (Real.sinh ρ) ^ 2 / 2) ≤
          (((2 * K.ncard : ℕ)) : ℝ≥0∞) * volH 3 (Tb b₀ η₁ ∩ Dc) :=
        le_trans h2 hpack'
      exact (ENNReal.mul_le_mul_iff_right hKN0 hKNtop).mp h3
  · -- ================= Case B =================
    have hker_all : ∀ c : PO 3 1, c ∈ Cplus Γ b₀ a → psi a b c = 0 := by
      intro c hc
      by_contra hne
      exact hcase ⟨c, hc, hne⟩
    set K : Set (PO 3 1) := {c : PO 3 1 | c ∈ Cplus Γ b₀ a ∧ psi a b c = 0} with hKdef
    have hKfin : K.Finite := by
      rw [hKdef]
      exact (finite_psi_small hA hI Γ hdisc ha hb hab hM hrot 0).subset
        (fun c hc => ⟨hc.1, by rw [hc.2]; simp⟩)
    have hCfin : ({c : PO 3 1 | c ∈ cent Γ b₀} : Set (PO 3 1)).Finite := by
      by_cases hall : ∀ c ∈ cent Γ b₀, c ∈ Cplus Γ b₀ a
      · exact hKfin.subset (fun c hc => by
          rw [hKdef]; exact ⟨hall c hc, hker_all c (hall c hc)⟩)
      · push_neg at hall
        obtain ⟨c₀, hc₀mem, hc₀not⟩ := hall
        have hcrev : bd c₀ a = b := by
          rcases (bd_pair_of_mem_cent hA hI ha hb hab hM hrot hc₀mem).1 with h | h
          · exact absurd ⟨hc₀mem, h⟩ hc₀not
          · exact h
        have hcover : ({c : PO 3 1 | c ∈ cent Γ b₀} : Set (PO 3 1)) ⊆ K ∪ (c₀ • K) := by
          intro c hc
          rcases Cplus_coset hA hI ha hb hab hM hrot hc₀mem hcrev c hc with h | ⟨e, he, hce⟩
          · exact Or.inl (by rw [hKdef]; exact ⟨h, hker_all c h⟩)
          · refine Or.inr (Set.mem_smul_set.mpr ⟨e, ?_, ?_⟩)
            · rw [hKdef]; exact ⟨he, hker_all e he⟩
            · rw [smul_eq_mul]; exact hce.symm
        exact (hKfin.union (hKfin.smul_set (a := c₀))).subset hcover
    haveI : Finite ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ) := hCfin.to_subtype
    right
    intro Dc hDc
    have hvtop : volH 3 (Tb b₀ η₁) = ⊤ := by
      have hsub : {u : E 3 | distGeod a b u ≤ ρ} ⊆ Tb b₀ η₁ :=
        tubeSubsetTb hA hI a b ha hb hab M hM b₀ hrot η₁ ρ hη₁ hρin
      rw [eq_top_iff, ← tube_vol_top hA hI a b ha hb hab hM hrot hρ]
      exact measure_mono hsub
    have hdiscC : IsDiscrete (SetLike.coe (Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ)) :=
      IsDiscrete.mono hdisc (fun c hc => hc.2)
    haveI hcountC : Countable ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ) :=
      Work.Mostow.countable_of_isDiscrete (PO 3 1) hdiscC
    haveI : MeasurableConstSMul ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ) (E 3) :=
      ⟨fun c => by
        show Measurable (fun x : E 3 => (c : PO 3 1) • x)
        exact ((hJ.contDiff_smul (c : PO 3 1)).continuous).measurable⟩
    haveI : SMulInvariantMeasure ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ) (E 3) (volH 3) :=
      ⟨fun c s hs => by
        show volH 3 ((fun x : E 3 => (c : PO 3 1) • x) ⁻¹' s) = volH 3 s
        exact (hJ.measurePreserving_smul (c : PO 3 1)).measure_preimage hs.nullMeasurableSet⟩
    have hcardC : Nat.card ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ) ≠ 0 := by
      have hne : Nonempty ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ) := ⟨⟨1, Subgroup.one_mem _⟩⟩
      exact Nat.card_ne_zero.mpr ⟨hne, inferInstance⟩
    have hTinv_fwd : ∀ c : ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ), ∀ x : E 3,
        x ∈ Tb b₀ η₁ ↔ c • x ∈ Tb b₀ η₁ := by
      intro c x
      show x ∈ Tb b₀ η₁ ↔ (c : PO 3 1) • x ∈ Tb b₀ η₁
      have hc : (c : PO 3 1) ∈ cent Γ b₀ := c.2
      have hcomm : (c : PO 3 1)⁻¹ * b₀ * (c : PO 3 1) = b₀ := by
        have hb : b₀ * (c : PO 3 1) = (c : PO 3 1) * b₀ := comm_of_mem_cent hc
        calc (c : PO 3 1)⁻¹ * b₀ * (c : PO 3 1)
            = (c : PO 3 1)⁻¹ * (b₀ * (c : PO 3 1)) := by group
          _ = (c : PO 3 1)⁻¹ * ((c : PO 3 1) * b₀) := by rw [hb]
          _ = b₀ := by group
      have h1 := nearIdAt_conj3 hA hI b₀ (c : PO 3 1) x η₁
      rw [hcomm] at h1
      exact h1.symm
    have hTinv : ∀ c : ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ), (c • (Tb b₀ η₁)) =ᵐ[volH 3] (Tb b₀ η₁) := by
      intro c
      refine Filter.EventuallyEq.of_eq ?_
      ext x
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      exact (hTinv_fwd c⁻¹ x).symm
    have h1 := MeasureTheory.IsFundamentalDomain.measure_eq_card_smul_of_smul_ae_eq_self hDc
      (Tb b₀ η₁) hTinv
    rw [hvtop] at h1
    have h2 : (((Nat.card ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ) : ℕ)) : ℝ≥0∞) * volH 3 (Tb b₀ η₁ ∩ Dc) = ⊤ := by
      rw [← nsmul_eq_mul]
      exact h1.symm
    rcases ENNReal.mul_eq_top.mp h2 with ⟨-, htop⟩ | ⟨htop, -⟩
    · exact htop
    · exact absurd htop (ENNReal.natCast_ne_top _)

end

end Work.Mostow.gapA
