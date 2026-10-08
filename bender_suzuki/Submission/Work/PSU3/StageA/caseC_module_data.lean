import Mathlib
import Submission.Work.PSU3.StageA.caseC_setup
import Submission.Work.PSU3.StageA.caseC_phi_rho_aux
import Submission.Work.PSU3.StageA.caseC_fpfXi
import Submission.Work.PSU3.StageA.typeB_scalar_aux
import Submission.Work.PSU3.StageA.caseC_isTypeB

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.PSU3.StageA

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

theorem conj_pow_mem_of_mem {V₀ : Subgroup G} {φ : MulAut G}
    (h : ∀ x : G, φ x * x⁻¹ ∈ V₀) : ∀ j : ℤ, ∀ x : G, (φ ^ j) x * x⁻¹ ∈ V₀ := by
  have hinv : ∀ x : G, (φ⁻¹) x * x⁻¹ ∈ V₀ := by
    intro x
    have h1 := h ((φ⁻¹) x)
    have h2 : φ ((φ⁻¹) x) = x := by simp
    rw [h2] at h1
    have h3 := V₀.inv_mem h1
    simpa using h3
  have hnat : ∀ j : ℕ, ∀ x : G, (φ ^ j) x * x⁻¹ ∈ V₀ := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
        intro x
        have ha : φ ((φ ^ j) x) * ((φ ^ j) x)⁻¹ ∈ V₀ := h _
        have hb : (φ ^ j) x * x⁻¹ ∈ V₀ := ih x
        have hs : (φ ^ (j + 1)) x * x⁻¹ =
            (φ ((φ ^ j) x) * ((φ ^ j) x)⁻¹) * ((φ ^ j) x * x⁻¹) := by
          rw [pow_succ', MulAut.mul_apply]; group
        rw [hs]; exact V₀.mul_mem ha hb
  have hinvnat : ∀ j : ℕ, ∀ x : G, ((φ⁻¹) ^ j) x * x⁻¹ ∈ V₀ := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
        intro x
        have ha : (φ⁻¹) (((φ⁻¹) ^ j) x) * (((φ⁻¹) ^ j) x)⁻¹ ∈ V₀ := hinv _
        have hb : ((φ⁻¹) ^ j) x * x⁻¹ ∈ V₀ := ih x
        have hs : ((φ⁻¹) ^ (j + 1)) x * x⁻¹ =
            ((φ⁻¹) (((φ⁻¹) ^ j) x) * (((φ⁻¹) ^ j) x)⁻¹) * (((φ⁻¹) ^ j) x * x⁻¹) := by
          rw [pow_succ', MulAut.mul_apply]; group
        rw [hs]; exact V₀.mul_mem ha hb
  intro j x
  obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg j
  · rw [hn, zpow_natCast]; exact hnat n x
  · rw [hn]
    have hs : φ ^ (-(n : ℤ)) = (φ⁻¹) ^ (n : ℤ) := by rw [zpow_neg, inv_zpow]
    rw [hs, zpow_natCast]; exact hinvnat n x

/-- Two elements of `Q` with equal image under `ψ` differ by an element of `Q₀sub`. -/
private lemma psi_eq_of_sub {F : Type} [AddCommGroup F] {ψ : ↥Q → F × F}
    (hadd : ∀ a b : ↥Q, ψ (a * b) = ψ a + ψ b)
    (hker : ∀ x : ↥Q, ψ x = 0 ↔ (x : G) ∈ Work.ThmF.Q0sub H)
    {x y : ↥Q} (h : ψ x = ψ y) : ((x * y⁻¹ : ↥Q) : G) ∈ Work.ThmF.Q0sub H := by
  have h1 : ψ (1 : ↥Q) = 0 := by
    have hh := hadd 1 1
    rw [mul_one] at hh
    have h2 : ψ 1 + ψ 1 = ψ 1 + 0 := by rw [add_zero]; exact hh.symm
    exact add_left_cancel h2
  have h2 : ∀ y : ↥Q, ψ y⁻¹ = -ψ y := by
    intro y
    have hh := hadd y y⁻¹
    rw [mul_inv_cancel, h1] at hh
    exact eq_neg_of_add_eq_zero_right hh.symm
  rw [← hker (x * y⁻¹), hadd, h2, h]
  simp


/-- The `ψ`/`μ` data of case c), obtained from `typeB_scalar` plus `FpfXi` and `IsTypeB`. -/
theorem caseC_psi_data_via_typeB {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp)
    (hcard : Nat.card Q = Nat.card (Work.ThmF.Q0sub H) ^ 3)
    (hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q)
    (hZ : ∀ x : ↥Q, (x : G) ∈ Work.ThmF.Q0sub H ↔ x * x = 1)
    (hW : ∀ w ∈ Work.ThmF.W H t, w ≠ 1 → ∀ x ∈ Q, w * x = x * w →
      x ∈ Work.ThmF.Q0sub H)
    {ζ : G} (hζ : ζ ∈ Work.ThmF.W H t) (hζ1 : ζ ≠ 1) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (ψ : ↥Q → F × F) (μ : Fˣ),
      Nat.card F = Nat.card ↥(Work.ThmF.Q0sub H) ∧
      (∀ a b : ↥Q, ψ (a * b) = ψ a + ψ b) ∧
      (∀ x : ↥Q, ψ x = 0 ↔ (x : G) ∈ Work.ThmF.Q0sub H) ∧
      Function.Surjective ψ ∧
      (∀ x : ↥Q,
        ψ (Work.PSU3.StageA.caseC_xi hS hC4
            (Work.PSU3.StageA.caseC_W_ne_bot (Q := Q) hζ hζ1) x) =
          ((μ : F) * (ψ x).1, (μ : F) * (ψ x).2)) := by
  classical
  have hWne : Work.ThmF.W H t ≠ ⊥ := caseC_W_ne_bot (Q := Q) hζ hζ1
  have hSuz : Work.Higman.IsSuzuki2Grp ↥Q := caseC_isSuzuki2Grp hS hC4 hnab hZ hWne
  have hfpf := caseC_fpfXi hS hC4 hHig hcard hζ hζ1
  have hB := caseC_isTypeB hS hC4 hHig hcard hnab hZ hW hζ hζ1
  obtain ⟨F, hF, hFint, ψ, hcardF, hadd, hker, hsurj, lam, hxi⟩ :=
    Work.PSU3.StageA.typeB_scalar hSuz hfpf hB
  have hcen : Subgroup.center ↥Q = (Work.ThmF.Q0sub H).subgroupOf Q :=
    caseC_center_subgroupOf hS hHig hZ hSuz
  refine ⟨F, hF, hFint, ψ, lam, ?_, hadd, ?_, hsurj, ?_⟩
  · have h1 : Nat.card ↥(Subgroup.center ↥Q) =
        Nat.card ↥((Work.ThmF.Q0sub H).subgroupOf Q) :=
      Nat.card_congr (MulEquiv.subgroupCongr hcen).toEquiv
    rw [hcardF, h1]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Q0sub_le_Q hS.split)).toEquiv
  · intro x
    rw [hker x, hcen, Subgroup.mem_subgroupOf]
  · intro x
    rw [hxi x]
    rfl

theorem caseC_module_data {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp)
    (hcard : Nat.card Q = Nat.card (Work.ThmF.Q0sub H) ^ 3)
    (hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q)
    (hZ : ∀ x : ↥Q, (x : G) ∈ Work.ThmF.Q0sub H ↔ x * x = 1)
    (hW : ∀ w ∈ Work.ThmF.W H t, w ≠ 1 → ∀ x ∈ Q, w * x = x * w →
      x ∈ Work.ThmF.Q0sub H)
    {ζ : G} (hζ : ζ ∈ Work.ThmF.W H t) (hζ1 : ζ ≠ 1) :
    Nonempty (Work.PSU3.StageA.CaseCModuleData H Q t) := by
  classical
  have hWne : Work.ThmF.W H t ≠ ⊥ := caseC_W_ne_bot (Q := Q) hζ hζ1
  obtain ⟨F₀, hF₀, hF₀int, φ, ρ, hcardF₀, hφbij, hφadd, hφconj⟩ :=
    caseC_phi_rho_data_aux hS hC4 hWne
  obtain ⟨F₁, hF₁, hF₁int, ψ₁, μ, hcardF₁, hψ₁add, hψ₁ker, hψ₁surj, hψ₁xi⟩ :=
    caseC_psi_data_via_typeB hS hC4 hHig hcard hnab hZ hW hζ hζ1
  letI : Field F₀ := hF₀
  letI : Fintype F₀ := hF₀int
  letI : Field F₁ := hF₁
  letI : Fintype F₁ := hF₁int
  have hcc : Fintype.card F₁ = Fintype.card F₀ := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcardF₁, hcardF₀]
  let θ : F₁ ≃+* F₀ := FiniteField.ringEquivOfCardEq hcc
  let μ₀ : F₀ˣ := Units.map θ.toMonoidHom μ
  let ψ : ↥Q → F₀ × F₀ := fun x => (θ (ψ₁ x).1, θ (ψ₁ x).2)
  have hψ₁zero : ψ₁ (1 : ↥Q) = 0 := by
    have h3 := hψ₁add 1 1
    rw [mul_one] at h3
    have h4 : ψ₁ 1 + ψ₁ 1 = ψ₁ 1 + 0 := by rw [add_zero]; exact h3.symm
    exact add_left_cancel h4
  have hψadd : ∀ a b : ↥Q, ψ (a * b) = ψ a + ψ b := by
    intro a b
    show (θ (ψ₁ (a * b)).1, θ (ψ₁ (a * b)).2) =
      (θ (ψ₁ a).1 + θ (ψ₁ b).1, θ (ψ₁ a).2 + θ (ψ₁ b).2)
    rw [hψ₁add a b]
    simp [map_add]
  have hψker : ∀ x : ↥Q, ψ x = 0 ↔ (x : G) ∈ Work.ThmF.Q0sub H := by
    intro x
    rw [← hψ₁ker x]
    constructor
    · intro h
      have h1 : (ψ₁ x).1 = 0 := θ.injective (by
        have := congrArg Prod.fst h
        simpa [ψ] using this)
      have h2 : (ψ₁ x).2 = 0 := θ.injective (by
        have := congrArg Prod.snd h
        simpa [ψ] using this)
      exact Prod.ext h1 h2
    · intro h
      show (θ (ψ₁ x).1, θ (ψ₁ x).2) = 0
      rw [h]
      simp
  have hψsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨x, hx⟩ := hψ₁surj (θ.symm y.1, θ.symm y.2)
    exact ⟨x, by simp [ψ, hx]⟩
  set N : ℕ := Nat.card ↥(Work.ThmF.Ksub H t) with hN
  have hξN : (caseC_xi hS hC4 hWne) ^ N = 1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rw [caseC_xi_pow_coe hS hC4 hWne N x, MulAut.one_apply]
    have hgN : ((caseC_gen hS hC4 hWne : ↥(Work.ThmF.Ksub H t)) : G) ^ N = 1 := by
      have h2 : (((caseC_gen hS hC4 hWne) ^ N : ↥(Work.ThmF.Ksub H t)) : G) = 1 := by
        rw [show N = orderOf (caseC_gen hS hC4 hWne) from
          (caseC_gen_orderOf hS hC4 hWne).symm, pow_orderOf_eq_one]
        rfl
      simpa only [Subgroup.coe_pow] using h2
    rw [hgN]; simp
  have hpowμ : ∀ i : ℕ, ∀ x : ↥Q,
      ψ₁ (((caseC_xi hS hC4 hWne) ^ i) x) = ((μ : F₁) ^ i) • (ψ₁ x) := by
    intro i
    induction i with
    | zero => intro x; simp
    | succ i ih =>
        intro x
        have hstep : ((caseC_xi hS hC4 hWne) ^ (i + 1)) x =
            (caseC_xi hS hC4 hWne) (((caseC_xi hS hC4 hWne) ^ i) x) := by
          rw [pow_succ', MulAut.mul_apply]
        rw [hstep, hψ₁xi, ih]
        ext <;> simp [smul_eq_mul, pow_succ', mul_assoc]
  have hμN : μ ^ N = 1 := by
    obtain ⟨x, hx⟩ := hψ₁surj ((1 : F₁), 0)
    have h := hpowμ N x
    rw [hx, hξN, MulAut.one_apply, hx] at h
    have h1 : (μ : F₁) ^ N = 1 := by
      have h2 := congrArg Prod.fst h
      simpa using h2.symm
    exact Units.ext (by simpa using h1)
  have hgtwo : 1 < Nat.card ↥(Work.ThmF.Q0sub H) := by
    obtain ⟨n, hn2, hncard⟩ := caseC_Q0sub_card hS hC4 hWne
    rw [hncard]
    exact Nat.one_lt_pow (by omega : n ≠ 0) (by norm_num)
  have hkey : ∀ m : ℕ, μ ^ m = 1 →
      ((caseC_gen hS hC4 hWne : ↥(Work.ThmF.Ksub H t)) : G) ^ m = 1 := by
    intro m hm
    by_contra hgm
    set φ := caseC_xi hS hC4 hWne with hφ
    set V₀ : Subgroup ↥Q := (Work.ThmF.Q0sub H).subgroupOf Q with hV
    have hinv : ∀ x : ↥Q, ψ₁ x⁻¹ = -ψ₁ x := by
      intro x
      have hh := hψ₁add x x⁻¹
      rw [mul_inv_cancel, hψ₁zero] at hh
      exact eq_neg_of_add_eq_zero_right hh.symm
    have hmval : (μ : F₁) ^ m = 1 := by
      have h5 := congrArg (fun u : F₁ˣ => (u : F₁)) hm
      simpa using h5
    have htriv : ∀ x : ↥Q, (φ ^ m) x * x⁻¹ ∈ V₀ := by
      intro x
      rw [hV, Subgroup.mem_subgroupOf, ← hψ₁ker]
      rw [hψ₁add, hpowμ m x, hmval, one_smul, hinv]
      simp
    have htrivz := conj_pow_mem_of_mem (V₀ := V₀) htriv
    have hne : ∃ x : ↥Q, (x : G) ∉ Work.ThmF.Q0sub H := by
      by_contra h
      push_neg at h
      have hle : Q ≤ Work.ThmF.Q0sub H := fun x hx => h ⟨x, hx⟩
      have hsub : Work.ThmF.Q0sub H = Q := le_antisymm (Q0sub_le_Q hS.split) hle
      have hc : Nat.card ↥(Work.ThmF.Q0sub H) = Nat.card ↥Q := by rw [hsub]
      rw [hcard] at hc
      have h5 : Nat.card ↥(Work.ThmF.Q0sub H) * Nat.card ↥(Work.ThmF.Q0sub H)^2 =
          Nat.card ↥(Work.ThmF.Q0sub H) * 1 := by
        rw [← pow_succ', mul_one]
        exact hc.symm
      have h4 : Nat.card ↥(Work.ThmF.Q0sub H)^2 = 1 :=
        Nat.eq_of_mul_eq_mul_left (by omega) h5
      nlinarith [h4, hgtwo]
    obtain ⟨x₀, hx₀0⟩ := hne
    have hx₀Q : (x₀ : G) ∈ Q := x₀.2
    set P : Subgroup G := Subgroup.zpowers
      (((caseC_gen hS hC4 hWne : ↥(Work.ThmF.Ksub H t)) : G) ^ m) with hP
    have hgmK : ((caseC_gen hS hC4 hWne : ↥(Work.ThmF.Ksub H t)) : G) ^ m ∈
        Work.ThmF.Kset H t := by
      have h7 := (Work.ThmF.Ksub H t).pow_mem (caseC_gen hS hC4 hWne).2 m
      exact (caseC_Ksub_cyc hS hC4 hWne).1 ▸ h7
    have hNodd : Odd (Nat.card ↥(Work.ThmF.Ksub H t)) := by
      obtain ⟨n, hn2, hncard⟩ := caseC_Q0sub_card hS hC4 hWne
      have h1 : Nat.card ↥(Work.ThmF.Ksub H t) = Nat.card ↥(Work.ThmF.Q0sub H) - 1 := by
        rw [caseC_card_Ksub hS hC4 hWne, caseC_card_Q0sub_eq hS hC4]; omega
      rw [h1, hncard]
      obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      rw [pow_succ]
      have hn1 : 1 ≤ n' := by omega
      have hle : 2 ≤ 2 ^ n' := by
        calc (2:ℕ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n' := Nat.pow_le_pow_right (by norm_num) hn1
      exact ⟨2 ^ n' - 1, by omega⟩
    have hPodd : Odd (Nat.card ↥P) := by
      rw [hP, Nat.card_zpowers]
      have h2 : orderOf (((caseC_gen hS hC4 hWne : ↥(Work.ThmF.Ksub H t)) : G) ^ m) =
          Nat.card ↥(Work.ThmF.Ksub H t) / (Nat.card ↥(Work.ThmF.Ksub H t)).gcd m := by
        rw [orderOf_pow, Subgroup.orderOf_coe, caseC_gen_orderOf hS hC4 hWne]
      rw [h2]
      exact Odd.of_dvd_nat hNodd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))
    have hPle : P ≤ Submission.Blueprint.twoPoint H t := by
      rw [hP]
      exact (Subgroup.zpowers_le.mpr (Work.ThmF.Kset_le_Ksub H t hgmK)).trans
        (Work.ThmF.Ksub_le_twoPoint (H := H) t)
    have hfixx : ∀ p ∈ P, p⁻¹ * (x₀ : G) * p * (x₀ : G)⁻¹ ∈ Work.ThmF.Q0sub H := by
      intro p hp
      rw [hP] at hp
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hp
      have hcoe : ((((φ ^ m) ^ (-j)) x₀ : ↥Q) : G) = p⁻¹ * (x₀ : G) * p := by
        have h2 : (φ ^ m) ^ (-j) = φ ^ (-(m * j)) := by
          have h3 : (φ ^ m : MulAut ↥Q) = φ ^ (m : ℤ) := (zpow_natCast φ m).symm
          rw [h3, ← zpow_mul]
          congr 1
          push_cast
          ring
        rw [h2, caseC_xi_zpow_coe]
        have hj' : ((caseC_gen hS hC4 hWne : ↥(Work.ThmF.Ksub H t)) : G) ^ (m * j) = p := by
          have h3 : ((caseC_gen hS hC4 hWne : ↥(Work.ThmF.Ksub H t)) : G) ^ (m : ℤ) =
              ((caseC_gen hS hC4 hWne : ↥(Work.ThmF.Ksub H t)) : G) ^ m := zpow_natCast _ _
          rw [show (m * j : ℤ) = (m : ℤ) * j from by push_cast; ring]
          rw [zpow_mul, h3]
          exact hj
        rw [← hj']
        group
      rw [← hcoe]
      have hfin := htrivz (-j) x₀
      rw [hV, Subgroup.mem_subgroupOf] at hfin
      exact hfin
    obtain ⟨y, hyQ, hy0, hyfix⟩ := caseC_exists_fixed_of_fixed_mod_Q0 hS hC4 hPle hPodd
      hx₀Q hx₀0 hfixx
    have hyc : ((caseC_gen hS hC4 hWne : ↥(Work.ThmF.Ksub H t)) : G) ^ m * y =
        y * ((caseC_gen hS hC4 hWne : ↥(Work.ThmF.Ksub H t)) : G) ^ m := by
      have h := hyfix (((caseC_gen hS hC4 hWne : ↥(Work.ThmF.Ksub H t)) : G) ^ m)
        (Subgroup.mem_zpowers _)
      have h2 : y * ((caseC_gen hS hC4 hWne : ↥(Work.ThmF.Ksub H t)) : G) ^ m =
          ((caseC_gen hS hC4 hWne : ↥(Work.ThmF.Ksub H t)) : G) ^ m * y := by
        calc y * ((caseC_gen hS hC4 hWne : ↥(Work.ThmF.Ksub H t)) : G) ^ m
            = (((caseC_gen hS hC4 hWne : ↥(Work.ThmF.Ksub H t)) : G) ^ m) *
                ((((caseC_gen hS hC4 hWne : ↥(Work.ThmF.Ksub H t)) : G) ^ m)⁻¹ * y *
                  ((caseC_gen hS hC4 hWne : ↥(Work.ThmF.Ksub H t)) : G) ^ m) := by group
          _ = (((caseC_gen hS hC4 hWne : ↥(Work.ThmF.Ksub H t)) : G) ^ m) * y := by rw [h]
      exact h2.symm
    have hy1 : y = 1 := Work.ThmF.ChV12.prop1a hS.situation hC4 H Q t hS.split _
      hgmK hgm y hyQ hyc.symm
    exact hy0 (by rw [hy1]; exact (Work.ThmF.Q0sub H).one_mem)
  have hμord : orderOf μ = N := by
    refine Nat.dvd_antisymm ?_ ?_
    · rw [orderOf_dvd_iff_pow_eq_one]; exact hμN
    · have h1 : ((caseC_gen hS hC4 hWne : ↥(Work.ThmF.Ksub H t)) : G) ^ (orderOf μ) = 1 :=
        hkey (orderOf μ) (pow_orderOf_eq_one μ)
      have h2 : orderOf (((caseC_gen hS hC4 hWne : ↥(Work.ThmF.Ksub H t)) : G)) ∣ orderOf μ :=
        orderOf_dvd_iff_pow_eq_one.mpr h1
      rwa [Subgroup.orderOf_coe, caseC_gen_orderOf hS hC4 hWne] at h2
  have hμ₀ord : orderOf μ₀ = N := by
    have h1 : orderOf μ₀ = orderOf μ :=
      orderOf_injective (Units.map θ.toMonoidHom)
        (fun a b hab => Units.ext (θ.injective (congrArg Units.val hab))) μ
    rw [h1, hμord]
  let eK : Multiplicative (ZMod N) ≃* ↥(Work.ThmF.Ksub H t) :=
    zmodMulEquivOfGenerator (g := caseC_gen hS hC4 hWne)
      (fun x => by rw [caseC_gen_spec hS hC4 hWne]; exact Subgroup.mem_top x) (n := N) rfl
  let eL : Multiplicative (ZMod N) ≃* ↥(Subgroup.zpowers μ₀) :=
    zmodMulEquivOfGenerator (g := ⟨μ₀, Subgroup.mem_zpowers μ₀⟩)
      (fun x => by
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp x.2
        exact Subgroup.mem_zpowers_iff.mpr ⟨j, Subtype.ext (by simpa using hj)⟩)
      (n := N) (by rw [Nat.card_zpowers, hμ₀ord])
  let Λ : ↥(Work.ThmF.Ksub H t) →* F₀ˣ :=
    (Subgroup.subtype (Subgroup.zpowers μ₀)).comp (eL.toMonoidHom.comp eK.symm.toMonoidHom)
  have hΛinj : Function.Injective Λ := by
    intro a b hab
    have h1 : eL (eK.symm a) = eL (eK.symm b) := by
      apply Subtype.ext
      exact hab
    exact eK.symm.injective (eL.injective h1)
  have hgenpos : 0 < orderOf (caseC_gen hS hC4 hWne) := by
    rw [caseC_gen_orderOf hS hC4 hWne]; exact Nat.card_pos
  have hpsiconj : ∀ (k : ↥(Work.ThmF.Ksub H t)) (x : ↥Q),
      ψ (conjQK hS.split k x) = ((Λ k : F₀) * (ψ x).1, (Λ k : F₀) * (ψ x).2) := by
    intro k x
    obtain ⟨n, hn⟩ := pow_eq_of_mem_zpowers hgenpos (by
      rw [caseC_gen_spec hS hC4 hWne]; exact Subgroup.mem_top k)
    have hkg : (k : G) = ((caseC_gen hS hC4 hWne : ↥(Work.ThmF.Ksub H t)) : G) ^ n := by
      rw [← hn]; rfl
    have hact : (conjQK hS.split k x : ↥Q) = ((caseC_xi hS hC4 hWne) ^ n) x := by
      apply Subtype.ext
      rw [conjQK_coe, caseC_xi_pow_coe, hkg]
    have hsymm : eK.symm k = Multiplicative.ofAdd ((n : ℤ) : ZMod N) := by
      rw [← hn, ← zpow_natCast (caseC_gen hS hC4 hWne) n]
      simp only [eK]
      rw [zmodMulEquivOfGenerator_symm_apply_zpow]
    have hΛk : (Λ k : F₀) = θ ((μ : F₁) ^ n) := by
      have h1 : eL (eK.symm k) =
          (⟨μ₀, Subgroup.mem_zpowers μ₀⟩ : ↥(Subgroup.zpowers μ₀)) ^ n := by
        rw [hsymm]
        simp only [eL]
        rw [zmodMulEquivOfGenerator_apply_ofAdd_intCast, zpow_natCast]
      have h3 : Λ k = μ₀ ^ n := by
        show Subgroup.subtype (Subgroup.zpowers μ₀) (eL (eK.symm k)) = μ₀ ^ n
        rw [h1]
        simp
      rw [h3]
      have h4 : ((μ₀ ^ n : F₀ˣ) : F₀) = (θ (μ : F₁)) ^ n := by
        rw [show μ₀ = Units.map θ.toMonoidHom μ from rfl]
        rfl
      rw [h4]
      exact (map_pow θ.toMonoidHom (μ : F₁) n).symm
    have hψval : ψ (((caseC_xi hS hC4 hWne) ^ n) x) =
        (θ ((μ : F₁) ^ n) * (ψ x).1, θ ((μ : F₁) ^ n) * (ψ x).2) := by
      change (θ (ψ₁ (((caseC_xi hS hC4 hWne) ^ n) x)).1,
        θ (ψ₁ (((caseC_xi hS hC4 hWne) ^ n) x)).2) = _
      rw [hpowμ n x]
      ext <;> simp only [ψ, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, map_mul]
    rw [hact, hψval, hΛk]
  exact ⟨⟨hS.split, F₀, hF₀, hF₀int, hcardF₀, φ, hφbij, hφadd, ρ, hφconj,
    ψ, hψadd, hψker, hψsurj, Λ, hΛinj, hpsiconj⟩⟩

end Work.PSU3.StageA
