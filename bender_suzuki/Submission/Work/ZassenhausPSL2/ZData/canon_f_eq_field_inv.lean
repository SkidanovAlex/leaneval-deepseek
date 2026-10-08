import Mathlib
import Submission.Work.ZassenhausPSL2.Defs
import Submission.Work.ZassenhausPSL2.Basic
import Submission.Work.ZassenhausPSL2.ZData.t_conj_eq_inv
import Submission.Work.ZassenhausPSL2.ZData.dStab_fpf_on_Q
import Submission.Work.RankOneUniqueness.qPt_injective
import Submission.Work.RankOneUniqueness.smul_qPt
import Submission.Work.RankOneUniqueness.t_smul_qPt
import Submission.Work.ZassenhausPSL2.ZData.card_dStab_eq_card_involutions
import Submission.Work.ZassenhausPSL2.ZData.Q_exponent_two_of_bounds
import Submission.Work.ZassenhausPSL2.ZData.feit_bound
import Submission.Work.ZassenhausPSL2.ZData.field_coordinates_of_regular

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausPSL2.ZData

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- `(d : G) * x * d⁻¹ ∈ Q` for `d ∈ twoPoint H t`, `x ∈ Q` (the normalizer form). -/
theorem mem_conj_Q (h : IsSplitRankOne H Q t) (d : twoPoint H t) (x : Q) :
    (d : G) * (x : G) * (d : G)⁻¹ ∈ Q :=
  (Subgroup.le_normalizer_iff.mp (le_trans inf_le_left h.normal)) (d : G) d.2 (x : G) x.2

/-- `t * d = d⁻¹ * t` when `t d t = d⁻¹`. -/
theorem t_mul_eq_inv_mul (ht : t * t = 1) (d : G) (hd : t * d * t = d⁻¹) :
    t * d = d⁻¹ * t := by
  calc t * d = (t * d) * (t * t) := by rw [ht, mul_one]
    _ = ((t * d) * t) * t := by group
    _ = d⁻¹ * t := by rw [hd]

/-- `f_iff` : the criterion for `f x = q`. -/
theorem f_iff (h : IsSplitRankOne H Q t) (C : Canon H Q t) {x : Q} (hx : (x : G) ≠ 1) :
    ∀ q : Q, C.f x = q ↔ t * (x : G) * t * (q : G)⁻¹ * t ∈ H := by
  intro q
  have hs := C.spec x hx
  have hgh : (C.g x : G) * (C.h x : G) ∈ H :=
    H.mul_mem (h.le (C.g x).2) ((Subgroup.mem_inf.mp (C.h x).2).1)
  have htinv : t * t = 1 := by
    rw [← pow_two, ← h.invol]; exact pow_orderOf_eq_one t
  constructor
  · intro hq
    have hmem' : t * (x : G) * t * (q : G)⁻¹ * t = (C.g x : G) * (C.h x : G) * (t * t) := by
      rw [hs, hq]; group
    rw [hmem', htinv, mul_one]; exact hgh
  · intro hmem
    have hkey : (⟨t * (x : G) * t * (q : G)⁻¹ * t, hmem⟩ : H).val * t * (q : G)
        = t * (x : G) * t := by
      show (t * (x : G) * t * (q : G)⁻¹ * t) * t * (q : G) = t * (x : G) * t
      calc (t * (x : G) * t * (q : G)⁻¹ * t) * t * (q : G)
          = t * (x : G) * t * (q : G)⁻¹ * (t * t) * (q : G) := by group
        _ = t * (x : G) * t * (q : G)⁻¹ * (q : G) := by rw [htinv, mul_one]
        _ = t * (x : G) * t := by group
    have hgg : (⟨(C.g x : G) * (C.h x : G), hgh⟩ : H).val * t * (C.f x : G)
        = t * (x : G) * t := by
      show (C.g x : G) * (C.h x : G) * t * (C.f x : G) = t * (x : G) * t
      rw [← hs]
    have hfin := Work.ZassenhausPSL2.decomp_unique h hkey hgg
    have : q = C.f x := congrArg Prod.snd hfin
    exact this.symm

/-- The candidate `q` with `t x t = A t q` is unique, phrased as the canonical form. -/
theorem f_eq_of_canon {h : IsSplitRankOne H Q t} {C : Canon H Q t} {x : Q}
    (hx : (x : G) ≠ 1) {A : G} (hA : A ∈ H) {q : Q}
    (hcanon : t * (x : G) * t = A * t * (q : G)) : C.f x = q := by
  have hgh : (C.g x : G) * (C.h x : G) ∈ H :=
    H.mul_mem (h.le (C.g x).2) ((Subgroup.mem_inf.mp (C.h x).2).1)
  have h1 : (⟨(C.g x : G) * (C.h x : G), hgh⟩ : H).val * t * (C.f x : G) = t * (x : G) * t := by
    show (C.g x : G) * (C.h x : G) * t * (C.f x : G) = t * (x : G) * t
    rw [← C.spec x hx]
  have h2 : (⟨A, hA⟩ : H).val * t * (q : G) = t * (x : G) * t := hcanon.symm
  exact congrArg Prod.snd (Work.ZassenhausPSL2.decomp_unique h h1 h2)

/-- **`f x = 1` is impossible** for `x ≠ 1`. -/
theorem f_ne_one (h : IsSplitRankOne H Q t) (C : Canon H Q t) {x : Q}
    (hx : (x : G) ≠ 1) : C.f x ≠ 1 := by
  intro hc
  have htinv : t * t = 1 := by
    rw [← pow_two, ← h.invol]; exact pow_orderOf_eq_one t
  have h1 := (f_iff h C hx 1).mp hc
  have he : t * (x : G) * t * ((1 : Q) : G)⁻¹ * t = t * (x : G) := by
    simp only [Subgroup.coe_one, inv_one, mul_one]
    rw [show t * (x : G) * t * t = t * (x : G) * (t * t) by group, htinv, mul_one]
  rw [he] at h1
  have h2 : t * (x : G) * (x : G)⁻¹ ∈ H := H.mul_mem h1 (H.inv_mem (h.le x.2))
  rw [mul_assoc, mul_inv_cancel, mul_one] at h2
  exact h.not_mem h2

/-- **D-equivariance of `f`.** -/
theorem f_conj (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H) (hQne : Q ≠ ⊥)
    (h2 : IsPGroup 2 Q) (C : Canon H Q t) (d : twoPoint H t) (x : Q) (hx : (x : G) ≠ 1)
    (helem : ∀ z : Q, (z : G) * (z : G) = 1) (hd : (d : G) * (x : G) * (d : G)⁻¹ ∈ Q)
    (hdq : (d : G)⁻¹ * (C.f x : G) * (d : G) ∈ Q) :
    C.f ⟨(d : G) * (x : G) * (d : G)⁻¹, hd⟩
      = ⟨(d : G)⁻¹ * (C.f x : G) * (d : G), hdq⟩ := by
  have htinv : t * t = 1 := by
    rw [← pow_two, ← h.invol]; exact pow_orderOf_eq_one t
  have htd : t * (d : G) * t = (d : G)⁻¹ :=
    t_conj_eq_inv H Q t h hz hQne h2 (d : G) d.2
  have htdl : t * (d : G) = (d : G)⁻¹ * t := t_mul_eq_inv_mul htinv (d : G) htd
  have hxinv : (x : G)⁻¹ = (x : G) := inv_eq_of_mul_eq_one_right (helem x)
  have hfxinv : (C.f x : G)⁻¹ = (C.f x : G) := inv_eq_of_mul_eq_one_right (helem (C.f x))
  have hdH : (d : G) ∈ H := (Subgroup.mem_inf.mp d.2).1
  set y : Q := ⟨(d : G) * (x : G) * (d : G)⁻¹, hd⟩ with hy_def
  have hyG : (y : G) = (d : G) * (x : G) * (d : G)⁻¹ := rfl
  have hxy : (x : G) = (d : G)⁻¹ * (y : G) * (d : G) := by
    rw [hy_def]; simp only [Subtype.coe_mk]; group
  have hyne : (y : G) ≠ 1 := by
    intro hc; exact hx (by rw [hxy, hc]; group)
  have hyinv : (y : G)⁻¹ = (y : G) := inv_eq_of_mul_eq_one_right (helem y)
  have hfyinv : (C.f y : G)⁻¹ = (C.f y : G) := inv_eq_of_mul_eq_one_right (helem (C.f y))
  have h1 : t • Work.RankOneUniqueness.qPt H t (x : G)
      = Work.RankOneUniqueness.qPt H t (C.f x : G) := by
    have hcanon : t * (x : G)⁻¹ * t = ((C.g x : G) * (C.h x : G)) * t * ((C.f x : G)) := by
      rw [hxinv]; exact C.spec x hx
    have hh := Work.RankOneUniqueness.t_smul_qPt h (x := (x : G)) (m := (C.g x : G) * (C.h x : G))
      (y := (C.f x : G)) x.2 hx
      (H.mul_mem (h.le (C.g x).2) ((Subgroup.mem_inf.mp (C.h x).2).1)) (C.f x).2 hcanon
    rwa [hfxinv] at hh
  have h2a : (d : G) • Work.RankOneUniqueness.qPt H t (x : G)
      = Work.RankOneUniqueness.qPt H t (y : G) := by
    have hfac : (d : G) * (x : G) = (y : G) * (d : G) := by rw [hyG]; group
    exact Work.RankOneUniqueness.smul_qPt h hdH x.2 y.2 d.2 hfac
  have h3 : t • Work.RankOneUniqueness.qPt H t (y : G)
      = Work.RankOneUniqueness.qPt H t ((d : G)⁻¹ * (C.f x : G) * (d : G)) := by
    rw [← h2a, smul_smul, htdl, ← smul_smul, h1]
    have hfac : (d : G)⁻¹ * (C.f x : G)
        = ((d : G)⁻¹ * (C.f x : G) * (d : G)) * (d : G)⁻¹ := by group
    exact Work.RankOneUniqueness.smul_qPt h (H.inv_mem hdH) (C.f x).2 hdq
      ((twoPoint H t).inv_mem d.2) hfac
  have h4 : t • Work.RankOneUniqueness.qPt H t (y : G)
      = Work.RankOneUniqueness.qPt H t (C.f y : G) := by
    have hAh' : (C.g y : G) * (C.h y : G) ∈ H :=
      H.mul_mem (h.le (C.g y).2) ((Subgroup.mem_inf.mp (C.h y).2).1)
    have hcanon : t * (y : G)⁻¹ * t = ((C.g y : G) * (C.h y : G)) * t * ((C.f y : G)) := by
      rw [hyinv]; exact C.spec y hyne
    have hh := Work.RankOneUniqueness.t_smul_qPt h (x := (y : G)) (m := (C.g y : G) * (C.h y : G))
      (y := (C.f y : G)) y.2 hyne hAh' (C.f y).2 hcanon
    rwa [hfyinv] at hh
  have hfin : ((C.f y : Q) : G) = (d : G)⁻¹ * (C.f x : G) * (d : G) :=
    Work.RankOneUniqueness.qPt_injective h (C.f y).2 hdq (h4.symm.trans h3)
  rw [hy_def] at hfin
  exact Subtype.ext hfin

/-- **`D` is transitive on `Q#`.**  From `|D| = |Q| - 1` and fixed-point-freeness. -/
theorem exists_conj_of_ne_one (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H)
    (hreg : Nat.card (twoPoint H t) = Nat.card Q - 1) {x y : Q}
    (hx : (x : G) ≠ 1) (hy : (y : G) ≠ 1) :
    ∃ d : twoPoint H t, (y : G) = (d : G) * (x : G) * (d : G)⁻¹ := by
  have hfpf := dStab_fpf_on_Q H Q t h hz
  set f : twoPoint H t → G := fun d => (d : G) * (x : G) * (d : G)⁻¹ with hf
  have hinj : Function.Injective f := by
    intro d₁ d₂ hd
    have hd' : (d₁ : G) * (x : G) * (d₁ : G)⁻¹ = (d₂ : G) * (x : G) * (d₂ : G)⁻¹ := hd
    have hconj : ((d₂ : G)⁻¹ * (d₁ : G)) * (x : G) * ((d₂ : G)⁻¹ * (d₁ : G))⁻¹ = (x : G) := by
      calc ((d₂ : G)⁻¹ * (d₁ : G)) * (x : G) * ((d₂ : G)⁻¹ * (d₁ : G))⁻¹
          = (d₂ : G)⁻¹ * ((d₁ : G) * (x : G) * (d₁ : G)⁻¹) * (d₂ : G) := by group
        _ = (d₂ : G)⁻¹ * ((d₂ : G) * (x : G) * (d₂ : G)⁻¹) * (d₂ : G) := by rw [hd']
        _ = (x : G) := by group
    have hmem : (d₂ : G)⁻¹ * (d₁ : G) ∈ twoPoint H t :=
      (twoPoint H t).mul_mem ((twoPoint H t).inv_mem d₂.2) d₁.2
    have h1 : (d₂ : G)⁻¹ * (d₁ : G) = 1 := by
      by_contra hne
      exact hx (hfpf _ hmem hne (x : G) x.2 hconj)
    exact Subtype.ext (inv_mul_eq_one.mp h1).symm
  have hsub : Set.range f ⊆ (Q : Set G) \ {1} := by
    rintro z ⟨d, rfl⟩
    refine ⟨mem_conj_Q h d x, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro hc
    refine hx ?_
    have hc' : (d : G) * (x : G) * (d : G)⁻¹ = 1 := hc
    rw [show (x : G) = (d : G)⁻¹ * ((d : G) * (x : G) * (d : G)⁻¹) * (d : G) by group, hc']
    group
  have hcardS : (Set.range f).ncard = Nat.card (twoPoint H t) := Set.ncard_range_of_injective hinj
  have hcardT : ((Q : Set G) \ {1}).ncard = Nat.card Q - 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem (Q.one_mem)]
    rfl
  have hle : ((Q : Set G) \ {1}).ncard ≤ (Set.range f).ncard := by
    rw [hcardT, hcardS]; exact le_of_eq hreg.symm
  have heq := Set.eq_of_subset_of_ncard_le hsub hle
  have hyS : (y : G) ∈ Set.range f := by
    rw [heq]
    exact ⟨y.2, by simp only [Set.mem_singleton_iff]; exact hy⟩
  obtain ⟨d, hd⟩ := hyS
  exact ⟨d, hd.symm⟩

/-- `(d : G)⁻¹ * x * d ∈ Q` for `d ∈ twoPoint H t`, `x ∈ Q`. -/
theorem mem_conj_Q_inv (h : IsSplitRankOne H Q t) (d : twoPoint H t) (x : Q) :
    (d : G)⁻¹ * (x : G) * (d : G) ∈ Q := by
  have h1 : (d : G)⁻¹ * (x : G) * ((d : G)⁻¹)⁻¹ ∈ Q :=
    (Subgroup.le_normalizer_iff.mp (le_trans inf_le_left h.normal)) (d : G)⁻¹
      ((twoPoint H t).inv_mem d.2) (x : G) x.2
  rwa [inv_inv] at h1

/-- `e z = 0 → z = 1` for an additive isomorphism `e`. -/
theorem e_eq_zero_iff {n : ℕ} (e : Q ≃ GaloisField 2 n) (hadd : ∀ x y : Q, e (x * y) = e x + e y)
    (z : Q) : e z = 0 ↔ z = 1 := by
  have he1 : e 1 = 0 := by
    have h := hadd 1 1
    rw [mul_one] at h
    exact (add_left_cancel (show (e 1 : GaloisField 2 n) + 0 = e 1 + e 1 by rw [add_zero]; exact h)).symm
  constructor
  · intro hz
    refine e.injective ?_
    rw [hz, he1]
  · intro hz; rw [hz]; exact he1

/-- **Constancy of `e (f x) * e x`.** -/
theorem prod_f_eq_const (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H) (hQne : Q ≠ ⊥)
    (h2 : IsPGroup 2 Q) (C : Canon H Q t) {n : ℕ} (e : Q ≃ GaloisField 2 n)
    (φ : twoPoint H t ≃* (GaloisField 2 n)ˣ)
    (hadd : ∀ x y : Q, e (x * y) = e x + e y)
    (hact : ∀ (d : twoPoint H t) (x : Q),
        e ⟨(d : G) * (x : G) * (d : G)⁻¹, mem_conj_Q h d x⟩ = (φ d : GaloisField 2 n) * e x)
    (helem : ∀ z : Q, (z : G) * (z : G) = 1)
    (hreg : Nat.card (twoPoint H t) = Nat.card Q - 1) :
    ∃ c : GaloisField 2 n, c ≠ 0 ∧ ∀ x : Q, x ≠ 1 → e (C.f x) * e x = c := by
  have he1 : e 1 = 0 := (e_eq_zero_iff e hadd 1).mpr rfl
  have hene : ∀ z : Q, z ≠ 1 → e z ≠ 0 := fun z hz h0 => hz ((e_eq_zero_iff e hadd z).mp h0)
  obtain ⟨x₀, hx₀⟩ : ∃ z : Q, z ≠ 1 := by
    by_contra hh
    simp only [not_exists, not_not] at hh
    exact hQne (le_antisymm (fun z hz => by
      rw [Subgroup.mem_bot]; exact congrArg Subtype.val (hh ⟨z, hz⟩)) bot_le)
  have hx₀G : (x₀ : G) ≠ 1 := fun hc => hx₀ (Subtype.ext hc)
  refine ⟨e (C.f x₀) * e x₀, ?_, ?_⟩
  · exact mul_ne_zero (hene _ (f_ne_one h C hx₀G)) (hene x₀ hx₀)
  · intro x hx
    have hxG : (x : G) ≠ 1 := fun hc => hx (Subtype.ext hc)
    obtain ⟨d, hd⟩ := exists_conj_of_ne_one h hz hreg hx₀G hxG
    have hxe : x = ⟨(d : G) * (x₀ : G) * (d : G)⁻¹, mem_conj_Q h d x₀⟩ :=
      Subtype.ext hd
    have hfx : C.f x = ⟨(d : G)⁻¹ * (C.f x₀ : G) * (d : G), mem_conj_Q_inv h d (C.f x₀)⟩ := by
      rw [hxe]
      exact f_conj h hz hQne h2 C d x₀ hx₀G helem (mem_conj_Q h d x₀)
        (mem_conj_Q_inv h d (C.f x₀))
    have ex : e x = (φ d : GaloisField 2 n) * e x₀ := by
      have hh := hact d x₀
      rwa [← hxe] at hh
    have hphi : (φ (d⁻¹) : GaloisField 2 n) = (φ d : GaloisField 2 n)⁻¹ := by
      rw [show φ (d⁻¹) = (φ d)⁻¹ from map_inv φ d]
      exact Units.val_inv_eq_inv_val (φ d)
    have efx : e (C.f x) = (φ d : GaloisField 2 n)⁻¹ * e (C.f x₀) := by
      rw [hfx]
      have hh := hact (d⁻¹) (C.f x₀)
      have helt : (⟨(d : G)⁻¹ * (C.f x₀ : G) * (d : G), mem_conj_Q_inv h d (C.f x₀)⟩ : Q)
          = ⟨((d⁻¹ : twoPoint H t) : G) * (C.f x₀ : G) * (((d⁻¹ : twoPoint H t) : G))⁻¹,
              mem_conj_Q h d⁻¹ (C.f x₀)⟩ := by
        refine Subtype.ext ?_
        show (d : G)⁻¹ * (C.f x₀ : G) * (d : G)
            = ((d⁻¹ : twoPoint H t) : G) * (C.f x₀ : G) * (((d⁻¹ : twoPoint H t) : G))⁻¹
        rw [show ((d⁻¹ : twoPoint H t) : G) = (d : G)⁻¹ by rfl]
        group
      rw [helt, hh, hphi]
    have hne : (φ d : GaloisField 2 n) ≠ 0 := (φ d).ne_zero
    rw [efx, ex,
      show ((φ d : GaloisField 2 n)⁻¹ * e (C.f x₀)) * ((φ d : GaloisField 2 n) * e x₀)
        = ((φ d : GaloisField 2 n)⁻¹ * (φ d : GaloisField 2 n)) * (e (C.f x₀) * e x₀) by ring,
      inv_mul_cancel₀ hne, one_mul]

/-- In a finite field of characteristic two, every element is a square, so `c⁻¹` has a square
root for `c ≠ 0`. -/
theorem exists_sq_eq_inv {n : ℕ} (hn : 1 ≤ n) (c : GaloisField 2 n) (hc : c ≠ 0) :
    ∃ α : GaloisField 2 n, α * α = c⁻¹ := by
  letI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 n (by omega)]
  have h1 : c ^ (2 ^ n - 1) = 1 := by
    have hh := FiniteField.pow_card_sub_one_eq_one c hc
    rwa [hcard] at hh
  have h2n : 2 ≤ 2 ^ n := by
    simpa using pow_le_pow_right₀ (show (1 : ℕ) ≤ 2 by norm_num) hn
  have hpn : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
  have hp : (2 ^ (n - 1) - 1) * 2 = 2 ^ n - 2 := by omega
  refine ⟨c ^ (2 ^ (n - 1) - 1), ?_⟩
  rw [← pow_two, ← pow_mul, hp]
  exact eq_inv_of_mul_eq_one_right (by
    rw [← pow_succ']
    have : 2 ^ n - 2 + 1 = 2 ^ n - 1 := by omega
    rw [this, h1])

/-- `D = twoPoint H t` is abelian (an involution inverting all its elements). -/
theorem twoPoint_abelian (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H) (hQne : Q ≠ ⊥)
    (h2 : IsPGroup 2 Q) : IsAbelianSubgroup (twoPoint H t) := by
  intro a ha b hb
  have hta := t_conj_eq_inv H Q t h hz hQne h2 a ha
  have htb := t_conj_eq_inv H Q t h hz hQne h2 b hb
  have htab := t_conj_eq_inv H Q t h hz hQne h2 (a * b) ((twoPoint H t).mul_mem ha hb)
  have h1 : t * (a * b) * t = (t * a * t) * (t * b * t) := by
    have h' : t⁻¹ = t := Work.ZassenhausPSL2.t_inv h
    have hmem : ∀ z : G, (MulAut.conj t) z = t * z * t := fun z => by rw [MulAut.conj_apply, h']
    rw [← hmem (a * b), map_mul, hmem a, hmem b]
  rw [h1, hta, htb, mul_inv_rev] at htab
  have h3 : b * a = a * b := by
    have := congrArg Inv.inv htab
    simpa [mul_inv_rev] using this
  exact h3.symm

/-- If every element of `Q` has order dividing two, then `#Inv(Q) = |Q| - 1`. -/
theorem ncard_involutions_exp (helem : ∀ z : Q, (z : G) * (z : G) = 1) :
    (involutions (Q : Set G)).ncard = Nat.card Q - 1 := by
  have hset : involutions (Q : Set G) = (Q : Set G) \ {1} := by
    ext u
    constructor
    · intro hu
      obtain ⟨hu1, hu2⟩ := hu
      exact ⟨hu1, by rintro rfl; exact absurd hu2 (by norm_num [orderOf_one])⟩
    · rintro ⟨hu1, hu2⟩
      refine ⟨hu1, ?_⟩
      have h2 : u ^ 2 = 1 := by rw [pow_two]; exact helem ⟨u, hu1⟩
      have hdvd : orderOf u ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hh | hh
      · exact absurd (orderOf_eq_one_iff.mp hh) hu2
      · exact hh
  rw [hset, Set.ncard_sdiff_singleton_of_mem (Q.one_mem)]
  rfl

/-- The full assembly. -/
theorem canon_f_eq_field_inv {G : Type} [Group G] [Finite G] (H Q : Subgroup G) (t : G)
    (C : Work.ZassenhausPSL2.Canon H Q t)
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hz : Submission.Blueprint.IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (hab : Submission.Blueprint.IsAbelianSubgroup Q)
    (hsimple : IsSimpleGroup G) :
    ∃ (n : ℕ) (_ : 1 ≤ n) (e : Q ≃ GaloisField 2 n)
      (φ : Submission.Blueprint.twoPoint H t ≃* (GaloisField 2 n)ˣ),
      (∀ x y : Q, e (x * y) = e x + e y) ∧
      (∀ (d : Submission.Blueprint.twoPoint H t) (x : Q),
        e ⟨(d : G) * (x : G) * (d : G)⁻¹,
            (Subgroup.le_normalizer_iff.mp (le_trans inf_le_left h.normal))
              (d : G) d.2 (x : G) x.2⟩
          = (φ d : GaloisField 2 n) * e x) ∧
      (∀ x : Q, x ≠ 1 → e (C.f x) * e x = 1) := by
  have hQne : Q ≠ ⊥ := by
    intro hbot
    have htwo : twoPoint H t = H := by
      have hs : Q ⊔ twoPoint H t = H := h.sup_eq
      rw [hbot, bot_sup_eq] at hs
      exact hs
    have hodd : Odd (Nat.card (twoPoint H t)) := h.stronglyEmbedded.2.2 t h.not_mem
    rw [htwo] at hodd
    exact (Nat.not_odd_iff_even.mpr h.stronglyEmbedded.2.1) hodd
  have hInvEq : Nat.card (twoPoint H t) = (involutions (Q : Set G)).ncard :=
    card_dStab_eq_card_involutions H Q t h hz hQne h2
  have hbound : 2 * Nat.card (twoPoint H t) + 1 ≥ Nat.card Q :=
    feit_bound H Q t h hz h2 hab hsimple
  have helemQ : ∀ x : Q, x ^ 2 = 1 :=
    Q_exponent_two_of_bounds Q h2 hab (Nat.card (twoPoint H t)) hInvEq hbound
  have helem : ∀ z : Q, (z : G) * (z : G) = 1 := fun z => by
    have hh : z * z = 1 := by rw [← pow_two]; exact helemQ z
    simpa using congrArg (fun w : Q => (w : G)) hh
  have hreg : Nat.card (twoPoint H t) = Nat.card Q - 1 := by
    rw [← ncard_involutions_exp (Q := Q) helem, hInvEq]
  have habD : IsAbelianSubgroup (twoPoint H t) := twoPoint_abelian h hz hQne h2
  have hfpf : ∀ d ∈ twoPoint H t, d ≠ 1 → ∀ x ∈ Q, d * x * d⁻¹ = x → x = 1 :=
    dStab_fpf_on_Q H Q t h hz
  obtain ⟨n, hn, e, φ, hadd, hact⟩ :=
    field_coordinates_of_regular Q (twoPoint H t) h2 hab habD (le_trans inf_le_left h.normal)
      hfpf hreg
  obtain ⟨c, hcne, hc⟩ := prod_f_eq_const h hz hQne h2 C e φ hadd hact helem hreg
  obtain ⟨α, hα⟩ := exists_sq_eq_inv hn c hcne
  have hαne : α ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hα
    exact hcne (inv_eq_zero.mp hα.symm)
  refine ⟨n, hn, ?_, φ, ?_, ?_, ?_⟩
  · exact Equiv.ofBijective (fun q => α * e q) ⟨fun q₁ q₂ hq => e.injective (mul_left_cancel₀ hαne hq),
      fun a => ⟨e.symm (α⁻¹ * a), by
        show α * e (e.symm (α⁻¹ * a)) = a
        rw [Equiv.apply_symm_apply, mul_inv_cancel_left₀ hαne]⟩⟩
  · intro x y
    change α * e (x * y) = α * e x + α * e y
    rw [hadd, mul_add]
  · intro d x
    change α * e ⟨(d : G) * (x : G) * (d : G)⁻¹, mem_conj_Q h d x⟩
      = (φ d : GaloisField 2 n) * (α * e x)
    rw [hact d x]; ring
  · intro x hx
    change (α * e (C.f x)) * (α * e x) = 1
    rw [show (α * e (C.f x)) * (α * e x) = (α * α) * (e (C.f x) * e x) by ring, hα, hc x hx,
      inv_mul_cancel₀ hcne]

end Work.ZassenhausPSL2.ZData
