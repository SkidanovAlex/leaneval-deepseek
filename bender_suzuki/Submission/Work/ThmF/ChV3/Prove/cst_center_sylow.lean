import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.Prove.Step9Defs
import Submission.Work.ThmF.ChV3.Prove.cst_isPGroup
import Submission.Work.ThmF.ChV3.Prove.T_sig_facts
import Submission.Work.ThmF.ChV3.Prove.cP_inf_cst
import Submission.Work.ThmF.ChV3.Prove.P_on_L
import Submission.Work.ThmF.ChV3.Prove.sylow_of_center_centralizer
import Submission.Work.ThmF.ChV3.Prove.S1_centralizerP_eq
import Submission.Work.ThmF.ChV3.Prove.S2_commS_mem_R
import Submission.Work.ThmF.ChV3.Prove.S3_T_facts
import Submission.Work.ThmF.ChV3.Prove.L_facts
import Submission.Work.ThmF.ChV3.Prove.A_le_cst
import Submission.Work.ThmF.Prove.centDLowerCentralizerS
import Submission.Work.PGroup.card_sup_mul_card_inf
import Submission.Work.PGroup.lt_normalizer_inf

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint
open Pointwise

namespace Work.ThmF.ChV3.Prove

open Work.ThmF

variable {G : Type} [Group G] [Finite G]

/-! ## Elementary helpers -/

/-- Membership in a join as a product, when the left factor normalises the right one. -/
private lemma mem_sup_iff_exists_mul {A B : Subgroup G}
    (h : A ≤ Subgroup.normalizer (B : Set G)) {x : G} :
    x ∈ A ⊔ B ↔ ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  have hcoe : (↑(A ⊔ B) : Set G) = (↑A : Set G) * (↑B : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right A B h
  rw [show (x ∈ A ⊔ B) ↔ (x ∈ (↑(A ⊔ B) : Set G)) from Iff.rfl, hcoe]
  constructor
  · intro hx
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hx
    exact ⟨a, ha, b, hb, hab⟩
  · rintro ⟨a, ha, b, hb, hab⟩
    exact Set.mem_mul.mpr ⟨a, ha, b, hb, hab⟩

/-- In a subgroup of order `3`, an element is trivial as soon as it commutes with the second
member of a non-commuting pair. -/
private lemma eq_one_of_comm_of_ne_of_card_three {P : Subgroup G} (hP : Nat.card P = 3)
    {x : G} (hx : x ∈ P) {y : G} (hxy : x * y ≠ y * x) :
    ∀ v ∈ P, v * y = y * v → v = 1 := by
  intro v hv hvy
  by_contra hvne
  have hx3 : orderOf x = 3 := by
    have hdvd := Subgroup.orderOf_dvd_natCard P hx
    rw [hP] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) (fun hx1 => hxy (by rw [hx1, one_mul, mul_one]))
    · exact h
  have hv3 : orderOf v = 3 := by
    have hdvd := Subgroup.orderOf_dvd_natCard P hv
    rw [hP] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hvne
    · exact h
  have hzv : Subgroup.zpowers v = P := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hv) ?_
    rw [Nat.card_zpowers, hv3, hP]
  -- `v` commutes with `y`, so every element of `⟨v⟩ = P` does, in particular `x`
  have hle : Subgroup.zpowers v ≤ Subgroup.centralizer ({y} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hvy)
  have hxzp : x ∈ Subgroup.zpowers v := by rw [hzv]; exact hx
  exact hxy (Subgroup.mem_centralizer_singleton_iff.mp (hle hxzp))

/-- In `⟨z⟩` with `orderOf z = 3`, an element is `1`, `z` or `z²`. -/
private lemma mem_zpowers_eq_one_or {z w : G} (hz : orderOf z = 3)
    (hw : w ∈ Subgroup.zpowers z) : w = 1 ∨ w = z ∨ w = z ^ 2 := by
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz; exact absurd hz (by norm_num)
  have hz2 : z ^ 2 ≠ 1 := fun h =>
    absurd (show (3 : ℕ) ∣ 2 by rw [← hz]; exact orderOf_dvd_iff_pow_eq_one.mpr h)
      (by norm_num)
  have hz3 : z ≠ z ^ 2 := fun h => by
    have h1 : z = 1 := by
      have h2 := congrArg (fun u => z⁻¹ * u) h
      simpa [pow_two, mul_assoc] using h2.symm
    exact hz1 h1
  have hnot1 : (1 : G) ∉ ({z, z ^ 2} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h)
    · exact hz1 h.symm
    · exact hz2 h.symm
  have hnotz : z ∉ ({z ^ 2} : Set G) := by
    simpa only [Set.mem_singleton_iff] using hz3
  have hncard : ({1, z, z ^ 2} : Set G).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem hnot1, Set.ncard_insert_of_notMem hnotz, Set.ncard_singleton]
  have hcard : (Subgroup.zpowers z : Set G).ncard = 3 := by
    have h1 : Nat.card ↥(Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, hz]
    rw [← Nat.card_coe_set_eq]
    simpa using h1
  have hsub : ({1, z, z ^ 2} : Set G) ⊆ (Subgroup.zpowers z : Set G) := by
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with h | h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers z
    · rw [h]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers z) 2
  have heq : ({1, z, z ^ 2} : Set G) = (Subgroup.zpowers z : Set G) :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hncard, hcard])
  have hw' : w ∈ ({1, z, z ^ 2} : Set G) := by rw [heq]; exact hw
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hw'

/-- `V = C_D(t) ≤ C_G(st)`: `V` centralises `s` (Peterfalvi II Ch. V §2 Lemma 3 a) and `t`. -/
private lemma centD_le_cst {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) :
    Submission.Blueprint.centD H t ≤ Cst s t := by
  have hVs : Submission.Blueprint.centD H t ≤ Subgroup.centralizer ({s} : Set G) :=
    Work.ThmF.Prove.centDLowerCentralizerS c.split c.s_mem c.s_inv c.r_mem c.sid
  have hVt : Submission.Blueprint.centD H t ≤ Subgroup.centralizer ({t} : Set G) :=
    fun _ hx => (Subgroup.mem_inf.mp hx).2
  exact (le_inf hVs hVt).trans (centralizer_mul_le_centralizer (G := G) s t)

/-- An element of `Z₁ = ⟨st⟩` commutes with every element of `C_G(st)`. -/
private lemma comm_of_mem_z1_of_mem_cst {s t u w : G} (hw : w ∈ Cst s t) (hu : u ∈ Z1 s t) :
    u * w = w * u := by
  have hst : (s * t) * w = w * (s * t) :=
    ((Subgroup.mem_centralizer_singleton_iff (g := s * t) (k := w)).mp
      (show w ∈ Subgroup.centralizer ({s * t} : Set G) from hw)).symm
  have hle : Subgroup.zpowers (s * t) ≤ Subgroup.centralizer ({w} : Set G) :=
    Subgroup.zpowers_le.mpr
      ((Subgroup.mem_centralizer_singleton_iff (g := w) (k := s * t)).mpr hst)
  exact (Subgroup.mem_centralizer_singleton_iff (g := w) (k := u)).mp (hle hu)

/-! ## §3 step (14), first half: the centre of `C_G(st)` -/

/-- **§3 step (14), `Z(C_G(st)) ≤ Z₁`.**  An element `z` of `C_G(st)` centralising `C_G(st)` lies
in `R ⊔ Σ = C_G(P) ⊓ C_G(st)` (14b).  Writing `z = σ · (a · v)` with `σ ∈ Σ`, `a ∈ T`, `v ∈ P`:
`z` centralises `T`, and `a · v ∈ R` does, so `σ` centralises `T` and `σ = 1` (14a, faithfulness
of `Σ` on `T`); then `a` centralises `Σ` (`v ∈ P` does, as `Σ ≤ C_G(P)`), so `a ∈ C_T(Σ) = Z₁`
(14a); finally `v` centralises the witness `y ∈ L ⊆ C_G(st)` (because `a ∈ Z₁` commutes with
`C_G(st)`), and `P` acts faithfully on `L` (15c). -/
theorem cst_center_le_z1 {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (h7 : Work.ThmF.ChV3.Ker H Q P t = P) (hpf : Nat.card P = orderOf (s * t))
    {T : Subgroup G} (h11 : Work.ThmF.ChV3.Step11Out H Q t P h15.R T)
    (d : Work.ThmF.ChV3.Case102 H Q t s P)
    (hB : Work.ThmF.ChV3.CG P ⊓ Work.ThmF.ChV3.Cst s t =
          h15.R ⊔ Work.ThmF.ChV3.Sig H t P)
    (hA : (∀ σ ∈ Work.ThmF.ChV3.Sig H t P, σ ≠ 1 → ∃ x ∈ T, σ * x * σ⁻¹ ≠ x) ∧
      T ⊓ Work.ThmF.ChV3.CG (Work.ThmF.ChV3.Sig H t P) = Work.ThmF.ChV3.Z1 s t)
    (hC : ∃ x ∈ P, ∃ y ∈ Work.ThmF.ChV3.Lsub H s t, x * y ≠ y * x) :
    ∀ z ∈ Work.ThmF.ChV3.Cst s t,
      (∀ y ∈ Work.ThmF.ChV3.Cst s t, z * y = y * z) → z ∈ Work.ThmF.ChV3.Z1 s t := by
  classical
  -- ## standing facts
  have hPcst : P ≤ Cst s t := c.P_le.trans (centD_le_cst c)
  have hSigcst : Sig H t P ≤ Cst s t := (inf_le_left.trans (W_le_centD H t)).trans (centD_le_cst c)
  have hSigCG : Sig H t P ≤ CG P := inf_le_right
  have hTR : T ≤ h15.R := by rw [← h11.TPR]; exact le_sup_left
  have hPR : P ≤ h15.R := by rw [← h11.TPR]; exact le_sup_right
  -- `s * t ∈ T` (S3), hence `T ≤ C_G(st)`
  have h2S : ∀ g ∈ CG P, g * s * g⁻¹ * s⁻¹ ∈ h15.R :=
    S2_commS_mem_R hFT hC4 c hpf (S1_centralizerP_eq hFT hC4 c h15 h7 hpf).2.1 h15.hRn
  obtain ⟨-, hstT, -, -⟩ :=
    S3_T_facts hFT hC4 c hpf h15.m h15.hm h11 h7 h15.hcardR h15.hcq h2S
  have hTcst : T ≤ Cst s t := by
    intro x hxT
    rw [Cst, Subgroup.mem_centralizer_singleton_iff]
    exact mul_comm_of_mem h11.comm (hTR hxT) (hTR hstT)
  have hSigNR : Sig H t P ≤ Subgroup.normalizer (h15.R : Set G) := hSigCG.trans h15.hRn
  -- ## the centre of `C_G(st)` lies in `R ⊔ Σ`
  intro z hzCst hzcomm
  have hzCG : z ∈ CG P := by
    rw [CG, Subgroup.mem_centralizer_iff]
    intro p hp
    exact (hzcomm p (hPcst hp)).symm
  have hzR : z ∈ h15.R ⊔ Sig H t P := by
    have hz' : z ∈ CG P ⊓ Cst s t := ⟨hzCG, hzCst⟩
    rwa [hB] at hz'
  -- write `z = σ * r`, `σ ∈ Σ`, `r ∈ R`
  rw [sup_comm] at hzR
  obtain ⟨σ, hsig_mem, r, hrR, hσr⟩ := (mem_sup_iff_exists_mul hSigNR).mp hzR
  -- write `r = a * v`, `a ∈ T`, `v ∈ P`
  have hTcent : T ≤ Subgroup.centralizer (P : Set G) :=
    fun x hx => Subgroup.mem_centralizer_iff.mpr
      (fun p hp => (mul_comm_of_mem h11.comm (hTR hx) (hPR hp)).symm)
  have hTNR : T ≤ Subgroup.normalizer (P : Set G) :=
    hTcent.trans (Subgroup.centralizer_le_normalizer (P : Set G))
  have hrTP : r ∈ T ⊔ P := by rw [h11.TPR]; exact hrR
  obtain ⟨a, haT, v, hvP, hav⟩ := (mem_sup_iff_exists_mul hTNR).mp hrTP
  -- ## step 1: `σ = 1`
  have hσ1 : σ = 1 := by
    by_contra hσne
    obtain ⟨x, hxT, hxne⟩ := hA.1 σ hsig_mem hσne
    refine hxne ?_
    -- `a * v` commutes with `x` (both lie in the abelian `R`)
    have havx : (a * v) * x = x * (a * v) := by
      calc (a * v) * x = a * (v * x) := mul_assoc _ _ _
        _ = a * (x * v) := by rw [mul_comm_of_mem h11.comm (hPR hvP) (hTR hxT)]
        _ = (a * x) * v := (mul_assoc _ _ _).symm
        _ = (x * a) * v := by rw [mul_comm_of_mem h11.comm (hTR haT) (hTR hxT)]
        _ = x * (a * v) := mul_assoc _ _ _
    have hzx : z * x = x * z := hzcomm x (hTcst hxT)
    have hzx' : (σ * (a * v)) * x = x * (σ * (a * v)) := by
      rw [hav, hσr]
      exact hzx
    have hmid : σ * x * (a * v) = x * σ * (a * v) :=
      calc σ * x * (a * v) = σ * (x * (a * v)) := by group
        _ = σ * ((a * v) * x) := by rw [← havx]
        _ = (σ * (a * v)) * x := by group
        _ = x * (σ * (a * v)) := hzx'
        _ = (x * σ) * (a * v) := by group
        _ = x * σ * (a * v) := by group
    have hσx : σ * x = x * σ := mul_right_cancel hmid
    rw [hσx]
    group
  -- ## step 2: `a ∈ Z₁`
  have hzav : z = a * v := by rw [← hσr, hσ1, one_mul, ← hav]
  have haZ1 : a ∈ Z1 s t := by
    rw [← hA.2]
    refine Subgroup.mem_inf.mpr ⟨haT, ?_⟩
    rw [CG, Subgroup.mem_centralizer_iff]
    intro σ' hsig_mem'
    have hvσ : v * σ' = σ' * v :=
      Subgroup.mem_centralizer_iff.mp (hSigCG hsig_mem') v hvP
    have hzσ : z * σ' = σ' * z := hzcomm σ' (hSigcst hsig_mem')
    calc σ' * a = σ' * a * (v * v⁻¹) := by group
      _ = σ' * (a * v) * v⁻¹ := by group
      _ = σ' * z * v⁻¹ := by rw [hzav]
      _ = z * σ' * v⁻¹ := by rw [hzσ]
      _ = (a * v) * σ' * v⁻¹ := by rw [hzav]
      _ = a * (v * σ') * v⁻¹ := by group
      _ = a * (σ' * v) * v⁻¹ := by rw [hvσ]
      _ = a * σ' := by group
  -- ## step 3: `v = 1`
  have hv1 : v = 1 := by
    obtain ⟨x, hxP, y, hyL, hxy⟩ := hC
    have hyCst : y ∈ Cst s t := (Subgroup.mem_inf.mp hyL).2
    have hvz : v = a⁻¹ * z := by rw [hzav]; group
    have hay : a * y = y * a := comm_of_mem_z1_of_mem_cst hyCst haZ1
    have hinv : a⁻¹ * y = y * a⁻¹ := by
      calc a⁻¹ * y = a⁻¹ * (y * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * y) * a⁻¹ := by rw [← hay]
        _ = y * a⁻¹ := by group
    have hvy : v * y = y * v := by
      have hzy : z * y = y * z := hzcomm y hyCst
      calc v * y = (a⁻¹ * z) * y := by rw [hvz]
        _ = a⁻¹ * (z * y) := mul_assoc _ _ _
        _ = a⁻¹ * (y * z) := by rw [hzy]
        _ = (a⁻¹ * y) * z := (mul_assoc _ _ _).symm
        _ = (y * a⁻¹) * z := by rw [hinv]
        _ = y * (a⁻¹ * z) := mul_assoc _ _ _
        _ = y * v := by rw [hvz]
    exact eq_one_of_comm_of_ne_of_card_three d.p3 hxP hxy v hvP hvy
  -- ## conclusion
  have hza : z = a := by rw [hzav, hv1, mul_one]
  rwa [hza]

/-- **§3 step (14): `Z(C_G(st)) = Z₁`**, as an equality of subgroups. -/
theorem centerOf_cst_eq_z1 {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (h7 : Work.ThmF.ChV3.Ker H Q P t = P) (hpf : Nat.card P = orderOf (s * t))
    {T : Subgroup G} (h11 : Work.ThmF.ChV3.Step11Out H Q t P h15.R T)
    (d : Work.ThmF.ChV3.Case102 H Q t s P)
    (hB : Work.ThmF.ChV3.CG P ⊓ Work.ThmF.ChV3.Cst s t =
          h15.R ⊔ Work.ThmF.ChV3.Sig H t P)
    (hA : (∀ σ ∈ Work.ThmF.ChV3.Sig H t P, σ ≠ 1 → ∃ x ∈ T, σ * x * σ⁻¹ ≠ x) ∧
      T ⊓ Work.ThmF.ChV3.CG (Work.ThmF.ChV3.Sig H t P) = Work.ThmF.ChV3.Z1 s t)
    (hC : ∃ x ∈ P, ∃ y ∈ Work.ThmF.ChV3.Lsub H s t, x * y ≠ y * x) :
    Work.ThmF.centerOf (Work.ThmF.ChV3.Cst s t) = Work.ThmF.ChV3.Z1 s t := by
  refine le_antisymm ?_ ?_
  · intro u hu
    exact cst_center_le_z1 hFT hC4 c h15 h7 hpf h11 d hB hA hC u
      (Subgroup.mem_inf.mp hu).1 (fun y hy => (Work.ThmF.mem_centerOf.mp hu).2 y hy)
  · intro u hu
    refine Work.ThmF.mem_centerOf.mpr
      ⟨Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl) hu, ?_⟩
    intro y hy
    exact comm_of_mem_z1_of_mem_cst hy hu

/-- **§3 step (14): `C_G(Z(C_G(st))) = C_G(st)`.** -/
theorem centralizer_centerOf_cst_eq {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (h7 : Work.ThmF.ChV3.Ker H Q P t = P) (hpf : Nat.card P = orderOf (s * t))
    {T : Subgroup G} (h11 : Work.ThmF.ChV3.Step11Out H Q t P h15.R T)
    (d : Work.ThmF.ChV3.Case102 H Q t s P)
    (hB : Work.ThmF.ChV3.CG P ⊓ Work.ThmF.ChV3.Cst s t =
          h15.R ⊔ Work.ThmF.ChV3.Sig H t P)
    (hA : (∀ σ ∈ Work.ThmF.ChV3.Sig H t P, σ ≠ 1 → ∃ x ∈ T, σ * x * σ⁻¹ ≠ x) ∧
      T ⊓ Work.ThmF.ChV3.CG (Work.ThmF.ChV3.Sig H t P) = Work.ThmF.ChV3.Z1 s t)
    (hC : ∃ x ∈ P, ∃ y ∈ Work.ThmF.ChV3.Lsub H s t, x * y ≠ y * x) :
    Subgroup.centralizer (Work.ThmF.centerOf (Work.ThmF.ChV3.Cst s t) : Set G) =
      Work.ThmF.ChV3.Cst s t := by
  rw [centerOf_cst_eq_z1 hFT hC4 c h15 h7 hpf h11 d hB hA hC]
  rw [Work.ThmF.ChV3.Z1, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

/-! ## §3 step (14), assembled from the four leaves -/

/-- **§3 step (14)**, with the four leaf inputs `(13)`, `(14b)`, `(14a)`, `(15c)` as explicit
hypotheses. -/
theorem cst_center_sylow_of_leaves {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (h7 : Work.ThmF.ChV3.Ker H Q P t = P) (hpf : Nat.card P = orderOf (s * t))
    {T : Subgroup G} (h11 : Work.ThmF.ChV3.Step11Out H Q t P h15.R T)
    (d : Work.ThmF.ChV3.Case102 H Q t s P)
    (hPg : IsPGroup 3 ↥(Work.ThmF.ChV3.Cst s t))
    (hB : Work.ThmF.ChV3.CG P ⊓ Work.ThmF.ChV3.Cst s t =
          h15.R ⊔ Work.ThmF.ChV3.Sig H t P)
    (hA : (∀ σ ∈ Work.ThmF.ChV3.Sig H t P, σ ≠ 1 → ∃ x ∈ T, σ * x * σ⁻¹ ≠ x) ∧
      T ⊓ Work.ThmF.ChV3.CG (Work.ThmF.ChV3.Sig H t P) = Work.ThmF.ChV3.Z1 s t)
    (hC : ∃ x ∈ P, ∃ y ∈ Work.ThmF.ChV3.Lsub H s t, x * y ≠ y * x) :
    (∀ z ∈ Work.ThmF.ChV3.Cst s t, (∀ y ∈ Work.ThmF.ChV3.Cst s t, z * y = y * z) →
        z ∈ Work.ThmF.ChV3.Z1 s t) ∧
      Nat.card ↥(Work.ThmF.ChV3.Cst s t) = Work.ThmF.ChV3.pPart 3 (Nat.card G) := by
  refine ⟨cst_center_le_z1 hFT hC4 c h15 h7 hpf h11 d hB hA hC, ?_⟩
  have hZ : Nat.card ↥(Work.ThmF.centerOf (Cst s t)) = 3 := by
    rw [centerOf_cst_eq_z1 hFT hC4 c h15 h7 hpf h11 d hB hA hC]
    rw [Work.ThmF.ChV3.Z1, Nat.card_zpowers, d.f3]
  exact sylow_of_center_centralizer Nat.prime_three hPg hZ
    (centralizer_centerOf_cst_eq hFT hC4 c h15 h7 hpf h11 d hB hA hC)

theorem cst_center_sylow {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (h7 : Work.ThmF.ChV3.Ker H Q P t = P) (hpf : Nat.card P = orderOf (s * t))
    {T : Subgroup G} (h11 : Work.ThmF.ChV3.Step11Out H Q t P h15.R T)
    (d : Work.ThmF.ChV3.Case102 H Q t s P) :
    (∀ z ∈ Work.ThmF.ChV3.Cst s t, (∀ y ∈ Work.ThmF.ChV3.Cst s t, z * y = y * z) →
        z ∈ Work.ThmF.ChV3.Z1 s t) ∧
      Nat.card ↥(Work.ThmF.ChV3.Cst s t) = Work.ThmF.ChV3.pPart 3 (Nat.card G) :=
  cst_center_sylow_of_leaves hFT hC4 c h15 h7 hpf h11 d
    (cst_isPGroup hFT hC4 c h15 d)
    (cP_inf_cst hFT hC4 c h15 h7 hpf h11 d).1
    ⟨(T_sig_facts hFT hC4 c h15 h7 hpf h11 d).1,
      (T_sig_facts hFT hC4 c h15 h7 hpf h11 d).2.2⟩
    (P_on_L hFT hC4 c h15 h7 hpf h11 d).1

end Work.ThmF.ChV3.Prove
