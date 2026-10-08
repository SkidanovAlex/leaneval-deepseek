import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.ChV3.Ctx
import Submission.Work.PGroup.lt_normalizer_inf

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# `Work.ThmF.ChV3.Prove.sylow_of_center_centralizer`

If `P ≤ G` is a finite `p`-subgroup whose centre has order exactly `p` and which equals the
centraliser of its own centre, then `P` is a Sylow `p`-subgroup of `G`.

The proof is the classical "centre / fusion" argument:
`N_G(P)` acts on `Z(P)` by conjugation, and `C_G(Z(P)) = P`.  Since `|Z(P)| = p` the group
`Z(P)` is cyclic of prime order, so `|Aut(Z(P))| = p - 1`; the action of `N_G(P)` therefore has
order dividing `p - 1`.  Now if `P` were properly contained in a `p`-subgroup `Q`, the normalizer
condition for finite `p`-groups would give a strictly larger `Q ⊓ N_G(P)`, hence an element
`x ∈ N_G(P)` of `p`-power order outside `P`; its conjugation action on `Z(P)` has order dividing
both `p`-power (as `x` has `p`-power order) and `p - 1`, hence is trivial, forcing
`x ∈ C_G(Z(P)) = P` — a contradiction.  So `P` is maximal among `p`-subgroups, i.e. a Sylow
`p`-subgroup, and `Sylow.card_eq_multiplicity` computes its order.
-/

namespace Work.ThmF.ChV3.Prove

open Work.ThmF

/-- Conjugation by an element of `N_G(P)` preserves the centre `Z(P) = centerOf P`. -/
private lemma conj_mem_centerOf {G : Type} [Group G] {P : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (P : Set G)) {z : G} (hz : z ∈ Work.ThmF.centerOf P) :
    x * z * x⁻¹ ∈ Work.ThmF.centerOf P := by
  rw [Work.ThmF.mem_centerOf] at hz ⊢
  obtain ⟨hzP, hzC⟩ := hz
  refine ⟨(Subgroup.mem_normalizer_iff.mp hx z).mp hzP, fun y hy => ?_⟩
  have hy' : x⁻¹ * y * x ∈ P := (Subgroup.mem_normalizer_iff''.mp hx y).mp hy
  calc x * z * x⁻¹ * y = x * (z * (x⁻¹ * y * x)) * x⁻¹ := by group
    _ = x * ((x⁻¹ * y * x) * z) * x⁻¹ := by rw [hzC (x⁻¹ * y * x) hy']
    _ = y * (x * z * x⁻¹) := by group

/-- `N_G(P) ≤ N_G(Z(P))`: the centre is characteristic in `P`. -/
private lemma normalizer_le_normalizer_centerOf {G : Type} [Group G] {P : Subgroup G} :
    Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer (Work.ThmF.centerOf P : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact conj_mem_centerOf hx hh
  · intro hh
    have h2 := conj_mem_centerOf (Subgroup.inv_mem _ hx) hh
    rwa [show x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h by group] at h2

/-- The conjugation action of `N_G(P)` on the centre `Z(P)`. -/
private noncomputable def conjActCenter {G : Type} [Group G] {P : Subgroup G} :
    ↥(Subgroup.normalizer (P : Set G)) →* MulAut ↥(Work.ThmF.centerOf P) :=
  (Subgroup.normalizerMonoidHom (Work.ThmF.centerOf P)).comp
    (Subgroup.inclusion (normalizer_le_normalizer_centerOf (P := P)))

/-- Any element of `N_G(P)` acting trivially on `Z(P)` lies in `C_G(Z(P)) = P`. -/
private lemma mem_of_conjActCenter_eq_one {G : Type} [Group G] {P : Subgroup G}
    (hC : Subgroup.centralizer (Work.ThmF.centerOf P : Set G) = P)
    (x : ↥(Subgroup.normalizer (P : Set G))) (hx : conjActCenter x = 1) : (x : G) ∈ P := by
  refine hC.le ?_
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have h := MulEquiv.ext_iff.mp hx ⟨z, hz⟩
  simp only [MulAut.one_apply, conjActCenter, MonoidHom.comp_apply] at h
  have h' : (x : G) * z * (x : G)⁻¹ = z := by
    have := congrArg Subtype.val h
    simpa using this
  have h4 : (x : G) * z * (x : G)⁻¹ * (x : G) = z * (x : G) :=
    congrArg (fun t => t * (x : G)) h'
  have h2 : (x : G) * z = z * (x : G) := by simpa using h4
  exact h2.symm

/-- `P` is maximal among the `p`-subgroups of `G`. -/
private lemma is_maximal_of_center_centralizer {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {P : Subgroup G} (hP : IsPGroup p ↥P)
    (hZ : Nat.card ↥(Work.ThmF.centerOf P) = p)
    (hC : Subgroup.centralizer (Work.ThmF.centerOf P : Set G) = P) :
    ∀ {Q : Subgroup G}, IsPGroup p ↥Q → P ≤ Q → Q = P := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsCyclic ↥(Work.ThmF.centerOf P) :=
    isCyclic_of_card_dvd_prime (α := ↥(Work.ThmF.centerOf P)) (by rw [hZ])
  have hmulaut : Nat.card (MulAut ↥(Work.ThmF.centerOf P)) = p - 1 := by
    rw [IsCyclic.card_mulAut (Work.ThmF.centerOf P), hZ, Nat.totient_prime hp]
  have hpd : ¬ p ∣ p - 1 := by
    intro h
    have hp2 : 2 ≤ p := hp.two_le
    have hle : p ≤ p - 1 := Nat.le_of_dvd (by omega) h
    omega
  intro Q hQ hPQ
  by_contra hne
  have hlt : P < Q := lt_of_le_of_ne hPQ (fun h => hne h.symm)
  -- the normalizer condition for the `p`-group `Q` produces an element of `Q ⊓ N_G(P)` outside `P`
  have hltN : P < Q ⊓ Subgroup.normalizer (P : Set G) :=
    Work.PGroup.lt_normalizer_inf (p := p) (P := Q) (R := P) hp hQ hlt
  obtain ⟨y, hyK, hyP⟩ := (SetLike.lt_iff_le_and_exists.mp hltN).2
  -- such an element has `p`-power order
  obtain ⟨k, hk⟩ := hQ ⟨y, hyK.1⟩
  have hy_pow : y ^ p ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hdy : orderOf y ∣ p ^ k := orderOf_dvd_iff_pow_eq_one.mpr hy_pow
  -- but its action on `Z(P)` has order dividing `p - 1`
  have h1 : orderOf (conjActCenter (P := P) ⟨y, hyK.2⟩) ∣ orderOf y := by
    rw [← Subgroup.orderOf_mk y hyK.2]
    exact orderOf_map_dvd (conjActCenter (P := P)) ⟨y, hyK.2⟩
  have h2 : orderOf (conjActCenter (P := P) ⟨y, hyK.2⟩) ∣ p - 1 := by
    rw [← hmulaut]
    exact orderOf_dvd_natCard _
  have h3 : orderOf (conjActCenter (P := P) ⟨y, hyK.2⟩) ∣ (p ^ k).gcd (p - 1) :=
    Nat.dvd_gcd (h1.trans hdy) h2
  have hcop' : (p ^ k).Coprime (p - 1) := (hp.coprime_iff_not_dvd.mpr hpd).pow_left k
  rw [hcop'.gcd_eq_one, Nat.dvd_one] at h3
  exact hyP (mem_of_conjActCenter_eq_one hC ⟨y, hyK.2⟩ (orderOf_eq_one_iff.mp h3))

theorem sylow_of_center_centralizer {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {P : Subgroup G} (hP : IsPGroup p ↥P)
    (hZ : Nat.card ↥(Work.ThmF.centerOf P) = p)
    (hC : Subgroup.centralizer (Work.ThmF.centerOf P : Set G) = P) :
    Nat.card ↥P = Work.ThmF.ChV3.pPart p (Nat.card G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard := Sylow.card_eq_multiplicity
    (Sylow.mk P hP (is_maximal_of_center_centralizer hp hP hZ hC))
  rw [Work.ThmF.ChV3.pPart]
  exact hcard

end Work.ThmF.ChV3.Prove
