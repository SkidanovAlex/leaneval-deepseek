import Mathlib
import Submission.Work.BrauerSuzuki.Q8.Ctx
import Submission.Work.BrauerSuzuki.Q8.Card
import Submission.Work.BrauerSuzuki.Q8.LamEta
import Submission.Work.BrauerSuzuki.Q8.Eta
import Submission.Work.BrauerSuzuki.Q8.Eta2
import Submission.Work.BrauerSuzuki.Q8.eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_four
import Submission.Work.CharCore.Basic
import Submission.Work.Induction.frobenius_reciprocity
import Submission.Work.Induction.frobenius_reciprocity_transposed
import Submission.Work.Induction.indFun_trans

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Classical
open scoped Pointwise

namespace Work.BrauerSuzuki.Q8

variable {G : Type*} [Group G] [Fintype G]

namespace Ctx

variable {x : G} {S : Sylow 2 G}

/-! ## Elementary membership and values of `λ`

`λ` is the linear character of `C* = C_G(⟨x⟩)` with kernel `T · H*`; it takes the value `1`
on `H*` and on `T`, and the value `-1` on the elements of `X = ⟨x⟩` of order `4`.
-/

/-- `x ∈ X`. -/
theorem x_mem_X (h : Ctx G x S) : x ∈ X x := Subgroup.mem_zpowers x

/-- `x ^ n ∈ X`. -/
theorem pow_mem_X (h : Ctx G x S) (n : ℕ) : x ^ n ∈ X x :=
  Subgroup.pow_mem (X x) h.x_mem_X n

/-- `x ^ 2 ∈ T`. -/
theorem sq_mem_T (h : Ctx G x S) : x ^ 2 ∈ T x := Subgroup.mem_zpowers (x ^ 2)

/-- `u ∈ H*` lies in `T · H*`. -/
theorem mem_THstar_of_mem_Hstar (h : Ctx G x S) (u : ↥(Hstar x)) :
    (u : G) ∈ (T x : Set G) * (Hstar x : Set G) :=
  ⟨1, (T x).one_mem, (u : G), u.2, by simp⟩

/-- `λ = 1` on `H*`. -/
theorem lamFun_Hstar (h : Ctx G x S) (u : ↥(Hstar x)) :
    lamFun x (⟨(u : G), h.Hstar_le_Cstar u.2⟩ : ↥(Cstar x)) = 1 := by
  rw [h.lamFun_eq_one_iff]
  exact h.mem_THstar_of_mem_Hstar u

/-- Multiplying an element of `C*` on the right by an element of `T · H*` does not change `λ`. -/
theorem lamFun_mul_of_mem_THstar (h : Ctx G x S) {a b : G} {ha : a ∈ Cstar x}
    {hb : b ∈ Cstar x} (hb1 : b ∈ (T x : Set G) * (Hstar x : Set G)) :
    lamFun x ((⟨a, ha⟩ : ↥(Cstar x)) * (⟨b, hb⟩ : ↥(Cstar x)))
      = lamFun x (⟨a, ha⟩ : ↥(Cstar x)) := by
  rw [h.lamFun_mul, (h.lamFun_eq_one_iff (⟨b, hb⟩ : ↥(Cstar x))).mpr hb1, mul_one]

/-- `λ = 1` on `T`. -/
theorem lamFun_T (h : Ctx G x S) {a : G} {p : a ∈ Cstar x} (ha : a ∈ T x) :
    lamFun x (⟨a, p⟩ : ↥(Cstar x)) = 1 := by
  rw [h.lamFun_eq_one_iff]
  exact ⟨a, ha, 1, (Hstar x).one_mem, by simp⟩

/-- An element of `X = ⟨x⟩` of order `4` lies in no `H*`-coset of `T · H*`. -/
theorem notMem_THstar_of_orderOf_eq_four (h : Ctx G x S) {a : G} (ha : a ∈ X x)
    (ha4 : orderOf a = 4) : a ∉ (T x : Set G) * (Hstar x : Set G) := by
  rintro ⟨t, ht, u, hu, htu⟩
  have huX : u ∈ X x := by
    have huu : u = t⁻¹ * a := by rw [← htu]; group
    rw [huu]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (h.T_le_X ht)) ha
  have huinf : u ∈ X x ⊓ Hstar x := Subgroup.mem_inf.mpr ⟨huX, hu⟩
  rw [h.infC] at huinf
  have hu1 : u = 1 := by simpa using huinf
  have hat : a ∈ T x := by
    have hatt : a = t := by rw [← htu, hu1]; simp
    rwa [hatt]
  have hdvd : orderOf a ∣ 2 := by
    have h1 := orderOf_dvd_natCard_of_mem hat
    rwa [h.T_card] at h1
  rw [ha4] at hdvd
  norm_num at hdvd

/-- `λ = -1` on the elements of `X = ⟨x⟩` of order `4`. -/
theorem lamFun_X_of_orderOf_eq_four (h : Ctx G x S) {a : G} {p : a ∈ Cstar x}
    (ha : a ∈ X x) (ha4 : orderOf a = 4) :
    lamFun x (⟨a, p⟩ : ↥(Cstar x)) = -1 := by
  rw [h.lamFun_eq_neg_one_iff]
  exact h.notMem_THstar_of_orderOf_eq_four ha ha4

/-- `x ^ 3 = x⁻¹`. -/
theorem x_cube_eq_inv (h : Ctx G x S) : x ^ 3 = x⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ, show 3 + 1 = 4 from rfl, show x ^ 4 = 1 from by rw [← h.hx4, pow_orderOf_eq_one]]

/-! ## An element of `N*` inverting `x`

Glauberman (1974), part (1): since `|S| = 8` and `X = ⟨x⟩` is cyclic of order `4`, we may take
`y ∈ S \ X`; then `y ∈ N*` and `y x y⁻¹ = x⁻¹`.
-/

theorem exists_conj_eq_inv (h : Ctx G x S) : ∃ y ∈ Nstar x, y * x * y⁻¹ = x⁻¹ := by
  have hne : (S : Subgroup G) ≠ X x := by
    intro heq
    have hc : Nat.card ↥(S : Subgroup G) = Nat.card ↥(X x) := by rw [heq]
    rw [h.card_S, h.X_card] at hc
    norm_num at hc
  obtain ⟨y, hyS, hyX⟩ : ∃ y ∈ (S : Subgroup G), y ∉ X x := by
    by_contra hcon
    push_neg at hcon
    exact hne (le_antisymm hcon h.X_le_S)
  have hyN : y ∈ Nstar x := h.le_N hyS
  refine ⟨y, hyN, ?_⟩
  have hmem : y * x * y⁻¹ ∈ X x := by
    rw [Nstar, Subgroup.mem_normalizer_iff] at hyN
    exact (hyN x).mp h.x_mem_X
  have ho4 : orderOf (y * x * y⁻¹) = 4 := by
    have hh := (MulAut.conj y).orderOf_eq x
    rw [MulAut.conj_apply] at hh
    rw [hh, h.hx4]
  have hne' : y * x * y⁻¹ ≠ x := by
    intro heq
    apply hyX
    have hcomm : y * x = x * y := by
      calc y * x = (y * x * y⁻¹) * y := by group
        _ = x * y := by rw [heq]
    have hyC : y ∈ Cstar x := by
      rw [Cstar, Subgroup.mem_centralizer_iff]
      intro a ha
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (show a ∈ Subgroup.zpowers x from ha)
      exact ((Commute.zpow_right hcomm k)).eq.symm
    have hyinf : y ∈ (S : Subgroup G) ⊓ Cstar x := Subgroup.mem_inf.mpr ⟨hyS, hyC⟩
    rw [h.infSC] at hyinf
    exact hyinf
  rcases eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_four h.hx4 hmem ho4 with h' | h'
  · exact absurd h' hne'
  · exact h'

/-- Conjugation by an element of `N*` inverting `x` identifies the `H*`-cosets of `x` and
`x⁻¹`, hence the corresponding sums. -/
theorem sum_conj_inv_shift (h : Ctx G x S) {χ : G → ℂ} (hχ : Work.CharCore.IsClassFun χ)
    {y : G} (hy : y ∈ Nstar x) (hyx : y * x * y⁻¹ = x⁻¹) :
    ∑ u : ↥(Hstar x), χ (x⁻¹ * (u : G)) = ∑ u : ↥(Hstar x), χ (x * (u : G)) := by
  have hyinv : y⁻¹ ∈ Nstar x := (Nstar x).inv_mem hy
  let f : ↥(Hstar x) → ↥(Hstar x) :=
    fun u => ⟨y * (u : G) * y⁻¹, h.Hstar_conj_Nstar hy u.2⟩
  let g : ↥(Hstar x) → ↥(Hstar x) :=
    fun u => ⟨y⁻¹ * (u : G) * (y⁻¹)⁻¹, h.Hstar_conj_Nstar hyinv u.2⟩
  have hleft : Function.LeftInverse g f := by
    intro u; apply Subtype.ext
    show y⁻¹ * (y * (u : G) * y⁻¹) * (y⁻¹)⁻¹ = (u : G); group
  have hright : Function.RightInverse g f := by
    intro u; apply Subtype.ext
    show y * (y⁻¹ * (u : G) * (y⁻¹)⁻¹) * y⁻¹ = (u : G); group
  let e : ↥(Hstar x) ≃ ↥(Hstar x) := ⟨f, g, hleft, hright⟩
  have hyx_inv : y * x⁻¹ * y⁻¹ = x := by
    have h1 : y * x⁻¹ * y⁻¹ = (y * x * y⁻¹)⁻¹ := by group
    rw [h1, hyx, inv_inv]
  have key : ∀ u : ↥(Hstar x), χ (x⁻¹ * (u : G)) = χ (x * ((e u) : G)) := by
    intro u
    have h2 : y * (x⁻¹ * (u : G)) * y⁻¹ = x * ((e u) : G) := by
      have hu : ((e u) : G) = y * (u : G) * y⁻¹ := rfl
      rw [hu]
      calc y * (x⁻¹ * (u : G)) * y⁻¹
          = (y * x⁻¹ * y⁻¹) * (y * (u : G) * y⁻¹) := by group
        _ = x * (y * (u : G) * y⁻¹) := by rw [hyx_inv]
    rw [← h2]
    exact (hχ (x⁻¹ * (u : G)) y).symm
  calc ∑ u : ↥(Hstar x), χ (x⁻¹ * (u : G))
      = ∑ u : ↥(Hstar x), χ (x * ((e u) : G)) :=
        Finset.sum_congr rfl (fun u _ => key u)
    _ = ∑ u : ↥(Hstar x), χ (x * (u : G)) :=
        Equiv.sum_comp e (fun v : ↥(Hstar x) => χ (x * (v : G)))

/-! ## Decomposition of `C*` into the four cosets `x ^ i H*`

`C* = X ⊔ H* = ⟨x⟩ × H*` with `X` cyclic of order `4`; hence
`(i, u) ↦ x ^ i u : Fin 4 × H* → C*` is a bijection.
-/

theorem sum_Cstar_eq_sum_fin4 (h : Ctx G x S) (F : ↥(Cstar x) → ℂ) :
    ∑ c : ↥(Cstar x), F c =
      ∑ i : Fin 4, ∑ u : ↥(Hstar x),
        F ((⟨x ^ (i : ℕ), h.X_le_Cstar (h.pow_mem_X (i : ℕ))⟩ : ↥(Cstar x))
            * (⟨(u : G), h.Hstar_le_Cstar u.2⟩ : ↥(Cstar x))) := by
  let φ : Fin 4 × ↥(Hstar x) → ↥(Cstar x) := fun p =>
    (⟨x ^ (p.1 : ℕ), h.X_le_Cstar (h.pow_mem_X (p.1 : ℕ))⟩ : ↥(Cstar x))
      * (⟨(p.2 : G), h.Hstar_le_Cstar p.2.2⟩ : ↥(Cstar x))
  have hval : ∀ p : Fin 4 × ↥(Hstar x), ((φ p : ↥(Cstar x)) : G) = x ^ (p.1 : ℕ) * (p.2 : G) := by
    intro p
    simp only [φ, Subgroup.coe_mul]
  have hbij : Function.Bijective φ := by
    rw [Fintype.bijective_iff_surjective_and_card]
    constructor
    · intro c
      obtain ⟨i, hi, u, hu, hcu⟩ :=
        exists_pow_mul_of_mem_centralizer h.hx4 h.supC h.comm (c := (c : G)) c.2
      refine ⟨(⟨i, hi⟩, ⟨u, hu⟩), ?_⟩
      apply Subtype.ext
      rw [hval]
      exact hcu.symm
    · rw [Fintype.card_prod, Fintype.card_fin,
        ← Nat.card_eq_fintype_card (α := ↥(Cstar x)), h.card_Cstar,
        Nat.card_eq_fintype_card (α := ↥(Hstar x))]
  have key := Fintype.sum_bijective φ hbij (fun p => F (φ p)) F (fun p => rfl)
  rw [Fintype.sum_prod_type] at key
  rw [key]

/-- **The key computation of step (6).** -/
theorem sum_Cstar_shift (h : Ctx G x S) {χ : G → ℂ} (hχ : Work.CharCore.IsClassFun χ) :
    ∑ c : ↥(Cstar x), (1 - lamFun x c) * χ (c : G) =
      4 * ∑ u : ↥(Hstar x), χ (x * (u : G)) := by
  rw [h.sum_Cstar_eq_sum_fin4 (fun c => (1 - lamFun x c) * χ (c : G))]
  change ∑ i : Fin 4, ∑ u : ↥(Hstar x),
      (1 - lamFun x ((⟨x ^ (i : ℕ), h.X_le_Cstar (h.pow_mem_X (i : ℕ))⟩ : ↥(Cstar x))
        * (⟨(u : G), h.Hstar_le_Cstar u.2⟩ : ↥(Cstar x))))
      * χ (((⟨x ^ (i : ℕ), h.X_le_Cstar (h.pow_mem_X (i : ℕ))⟩ : ↥(Cstar x))
        * (⟨(u : G), h.Hstar_le_Cstar u.2⟩ : ↥(Cstar x))) : G)
      = 4 * ∑ u : ↥(Hstar x), χ (x * (u : G))
  trans ∑ i : Fin 4, (1 - lamFun x (⟨x ^ (i : ℕ), h.X_le_Cstar (h.pow_mem_X (i : ℕ))⟩ : ↥(Cstar x)))
      * ∑ u : ↥(Hstar x), χ (x ^ (i : ℕ) * (u : G))
  · -- the summand only depends on `i` through `λ (x ^ i)`
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [h.lamFun_mul_of_mem_THstar (hb1 := h.mem_THstar_of_mem_Hstar u)]
  · -- evaluate `λ` on the four coset representatives
    have e0 : (1 - lamFun x (⟨x ^ ((0 : Fin 4) : ℕ), h.X_le_Cstar
        (h.pow_mem_X ((0 : Fin 4) : ℕ))⟩ : ↥(Cstar x))) = 0 := by
      rw [h.lamFun_T (a := x ^ ((0 : Fin 4) : ℕ))
        (by rw [show ((0 : Fin 4) : ℕ) = 0 from rfl, pow_zero]; exact (T x).one_mem)]
      ring
    have e1 : (1 - lamFun x (⟨x ^ ((1 : Fin 4) : ℕ), h.X_le_Cstar
        (h.pow_mem_X ((1 : Fin 4) : ℕ))⟩ : ↥(Cstar x))) = 2 := by
      rw [h.lamFun_X_of_orderOf_eq_four (a := x ^ ((1 : Fin 4) : ℕ))
        (by rw [show ((1 : Fin 4) : ℕ) = 1 from rfl, pow_one]; exact h.x_mem_X)
        (by rw [show ((1 : Fin 4) : ℕ) = 1 from rfl, pow_one]; exact h.hx4)]
      ring
    have e2 : (1 - lamFun x (⟨x ^ ((2 : Fin 4) : ℕ), h.X_le_Cstar
        (h.pow_mem_X ((2 : Fin 4) : ℕ))⟩ : ↥(Cstar x))) = 0 := by
      rw [h.lamFun_T (a := x ^ ((2 : Fin 4) : ℕ))
        (by rw [show ((2 : Fin 4) : ℕ) = 2 from rfl]; exact h.sq_mem_T)]
      ring
    have e3 : (1 - lamFun x (⟨x ^ ((3 : Fin 4) : ℕ), h.X_le_Cstar
        (h.pow_mem_X ((3 : Fin 4) : ℕ))⟩ : ↥(Cstar x))) = 2 := by
      rw [h.lamFun_X_of_orderOf_eq_four (a := x ^ ((3 : Fin 4) : ℕ))
        (by rw [show ((3 : Fin 4) : ℕ) = 3 from rfl]; exact h.pow_mem_X 3)
        (by rw [show ((3 : Fin 4) : ℕ) = 3 from rfl, orderOf_pow, h.hx4]; norm_num)]
      ring
    have hS1 : (∑ u : ↥(Hstar x), χ (x ^ ((1 : Fin 4) : ℕ) * (u : G)))
        = ∑ u : ↥(Hstar x), χ (x * (u : G)) := by
      refine Finset.sum_congr rfl (fun u _ => ?_)
      rw [show ((1 : Fin 4) : ℕ) = 1 from rfl, pow_one]
    have hS3 : (∑ u : ↥(Hstar x), χ (x ^ ((3 : Fin 4) : ℕ) * (u : G)))
        = ∑ u : ↥(Hstar x), χ (x * (u : G)) := by
      obtain ⟨y, hy, hyx⟩ := h.exists_conj_eq_inv
      have h1 : (∑ u : ↥(Hstar x), χ (x ^ ((3 : Fin 4) : ℕ) * (u : G)))
          = ∑ u : ↥(Hstar x), χ (x⁻¹ * (u : G)) := by
        refine Finset.sum_congr rfl (fun u _ => ?_)
        rw [show ((3 : Fin 4) : ℕ) = 3 from rfl, h.x_cube_eq_inv]
      rw [h1, h.sum_conj_inv_shift hχ hy hyx]
    rw [Fin.sum_univ_four, e0, e1, e2, e3, hS1, hS3]
    ring

end Ctx

open Classical in
theorem step6_inner_eta {G : Type*} [Group G] [Fintype G] {x : G} {S : Sylow 2 G}
    (h : Work.BrauerSuzuki.Q8.Ctx G x S) {χ : G → ℂ} (hχ : χ ∈ Work.CharCore.Irr G) :
    Work.CharCore.cfInner χ h.eta =
      (Nat.card ↥(Work.BrauerSuzuki.Q8.Hstar x) : ℂ)⁻¹ *
        ∑ u : ↥(Work.BrauerSuzuki.Q8.Hstar x), χ (x * (u : G)) := by
  have hcf : Work.CharCore.IsClassFun χ := Work.CharCore.isClassFun_of_mem_Irr hχ
  -- `η = Ind_{C*}^{G} (1 - λ)`
  have heta : h.eta = Work.Induction.indFun (Cstar x) (fun c : ↥(Cstar x) => 1 - lamFun x c) := by
    have hz : h.zeta = Work.Induction.indFun ((Cstar x).subgroupOf (Nstar x))
        (fun k => (fun c : ↥(Cstar x) => 1 - lamFun x c)
          (Subgroup.subgroupOfEquivOfLe h.Cstar_le_Nstar k)) := by
      rw [show h.zeta = Work.Induction.indFun ((Cstar x).subgroupOf (Nstar x)) h.phiKc from rfl]
      congr 1
    rw [show h.eta = Work.Induction.indFun (Nstar x) h.zeta from rfl, hz]
    exact Work.Induction.indFun_trans h.Cstar_le_Nstar (fun c : ↥(Cstar x) => 1 - lamFun x c)
  rw [heta, Work.Induction.frobenius_reciprocity_transposed (Cstar x) χ
        (fun c : ↥(Cstar x) => 1 - lamFun x c) hcf]
  rw [Work.CharCore.cfInner_apply]
  have hconj : ∀ c : ↥(Cstar x), starRingEnd ℂ (1 - lamFun x c) = 1 - lamFun x c := by
    intro c
    by_cases hc : (c : G) ∈ (T x : Set G) * (Hstar x : Set G)
    · rw [(h.lamFun_eq_one_iff c).mpr hc]; simp
    · rw [(h.lamFun_eq_neg_one_iff c).mpr hc]; simp
  have hsum : (∑ c : ↥(Cstar x),
        Work.Induction.resFun (Cstar x) χ c * starRingEnd ℂ (1 - lamFun x c))
      = ∑ c : ↥(Cstar x), (1 - lamFun x c) * χ (c : G) := by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [hconj c]
    simp only [Work.Induction.resFun_apply]
    ring
  rw [hsum, h.sum_Cstar_shift hcf]
  rw [show (Fintype.card ↥(Cstar x) : ℂ) = 4 * (Nat.card ↥(Hstar x) : ℂ) from by
    have hcardNat : Fintype.card ↥(Cstar x) = 4 * Nat.card ↥(Hstar x) := by
      rw [← Nat.card_eq_fintype_card (α := ↥(Cstar x)), h.card_Cstar]
    rw [hcardNat]; push_cast; ring]
  have hne : (Nat.card ↥(Hstar x) : ℂ) ≠ 0 := by
    have hpos : 0 < Nat.card ↥(Hstar x) := Nat.card_pos
    exact_mod_cast hpos.ne'
  field_simp

end Work.BrauerSuzuki.Q8
