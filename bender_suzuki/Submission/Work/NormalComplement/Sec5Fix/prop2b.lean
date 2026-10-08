import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.sec5_prop1
import Submission.Work.NormalComplement.prop2b_conj_into_centD
import Submission.Work.NormalComplement.sec4_P2d
import Submission.Work.NormalComplement.appI_five_b
import Submission.Work.NormalComplement.sec5_prop2
import Submission.Work.NormalComplement.appI_one
import Submission.Work.NormalComplement.appI_two
import Submission.Work.Coprime.All
import Submission.Work.ThreePoints.Basic
import Submission.Work.Fitting.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1000000

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement.Sec5Fix

/-! ## Auxiliary lemmas

These are the group-theoretic pieces of §5 Prop. 2 (b): the parity count of App. I (1), the
identification of `centD H t = C_G(t) ⊓ C_G(ut)`, Sylow conjugacy for elements of prime order,
and the App. I (5)(b) abelian-subgroup statement. -/

/-- App. I (1): if the involution `t` normalises `X` and the fixed points `X ⊓ C_G(t)` of the
conjugation action are odd, then `|X|` is odd (the number of fixed points of an involution on a
finite set has the same parity as the set). -/
theorem odd_card_inf_centralizer {G : Type*} [Group G] [Finite G]
    {X : Subgroup G} {t : G} (ht : orderOf t = 2)
    (htX : t ∈ Subgroup.normalizer (X : Set G))
    (hodd : Odd (Nat.card ↥(X ⊓ Subgroup.centralizer ({t} : Set G)))) :
    Odd (Nat.card ↥X) := by
  classical
  haveI hN : FT.Normalizes (Subgroup.zpowers t) X := ⟨Subgroup.zpowers_le.mpr htX⟩
  -- `C_G(⟨t⟩) = C_G(t)`
  have hcent : Subgroup.centralizer (Subgroup.zpowers t : Set G) =
      Subgroup.centralizer ({t} : Set G) := by
    refine le_antisymm ?_ ?_
    · exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers t))
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hxt : Commute x t := Subgroup.mem_centralizer_singleton_iff.mp hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_right hxt n).eq.symm
  -- the fixed points of the conjugation action are `X ⊓ C_G(t)`
  have hmap := FT.map_fixedPoints_conjAction (Subgroup.zpowers t) X
  rw [hcent, inf_comm] at hmap
  have h1 : Nat.card ↥(FT.fixedPoints (Subgroup.zpowers t) X) =
      Nat.card ↥(X ⊓ Subgroup.centralizer ({t} : Set G)) := by
    rw [← hmap, Subgroup.card_map_of_injective (Subgroup.subtype_injective X)]
  have hcard : Nat.card (MulAction.fixedPoints ↥(Subgroup.zpowers t) ↥X) =
      Nat.card ↥(X ⊓ Subgroup.centralizer ({t} : Set G)) := by
    rw [← h1]
    rfl
  have hpg : IsPGroup 2 ↥(Subgroup.zpowers t) := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by rw [Nat.card_zpowers, ht]; norm_num⟩
  have hmod := hpg.card_modEq_card_fixedPoints ↥X
  rw [hcard] at hmod
  refine Nat.odd_iff.mpr ?_
  rw [hmod]
  exact Nat.odd_iff.mp hodd

/-- If `u`, `t` are involutions, then `t` inverts `u * t`. -/
theorem conj_mul_inv {G : Type*} [Group G] {u t : G} (ht : orderOf t = 2) (hu : orderOf u = 2) :
    t * (u * t) * t⁻¹ = (u * t)⁻¹ := by
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t; rw [ht] at h; simpa [pow_two] using h
  have hu2 : u * u = 1 := by
    have h := pow_orderOf_eq_one u; rw [hu] at h; simpa [pow_two] using h
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ht2, inv_eq_of_mul_eq_one_right hu2]
  calc t * (u * t) * t = t * u * (t * t) := by group
    _ = t * u := by rw [ht2, mul_one]

/-- Conjugation by an involution normalises the centraliser of the product with another
involution. -/
theorem normalizedBy_centralizer_mul {G : Type*} [Group G] {u t : G} (ht : orderOf t = 2)
    (hu : orderOf u = 2) :
    NormalizedBy t (Subgroup.centralizer ({u * t} : Set G)) := by
  intro x hx
  have hxc : Commute x (u * t) := Subgroup.mem_centralizer_singleton_iff.mp hx
  have hkey : t * (u * t) * t⁻¹ = (u * t)⁻¹ := conj_mul_inv ht hu
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hcomm1 : Commute (t * x * t⁻¹) (t * (u * t) * t⁻¹) := by
    have h1 : (t * x * t⁻¹) * (t * (u * t) * t⁻¹) = t * (x * (u * t)) * t⁻¹ := by group
    have h2 : (t * (u * t) * t⁻¹) * (t * x * t⁻¹) = t * ((u * t) * x) * t⁻¹ := by group
    show (t * x * t⁻¹) * (t * (u * t) * t⁻¹) = (t * (u * t) * t⁻¹) * (t * x * t⁻¹)
    rw [h1, h2, hxc]
  have hcomm2 : Commute (t * x * t⁻¹) (u * t) := by
    have h := hcomm1.inv_right
    rw [hkey, inv_inv] at h
    exact h
  exact hcomm2

/-- `V = C_D(t)` is the intersection of `C_G(t)` with `C_G(ut)`, when `u ∈ H` is an involution
centralising `V`. -/
theorem centD_eq_inf_centralizer_mul {G : Type} [Group G] [Finite G] {H : Subgroup G} {t u : G}
    (hse : IsStronglyEmbedded H) (huH : u ∈ H) (hu2 : orderOf u = 2)
    (huC : u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G)) :
    Submission.Blueprint.centD H t =
      Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({u * t} : Set G) := by
  refine le_antisymm ?_ ?_
  · intro v hv
    have hvt : Commute v t :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hv).2
    have hvu : Commute v u := (Subgroup.mem_centralizer_iff.mp huC) v hv
    exact Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_centralizer_singleton_iff.mpr hvt,
        Subgroup.mem_centralizer_singleton_iff.mpr (hvu.mul_right hvt)⟩
  · intro y hy
    obtain ⟨hyt, hyut⟩ := Subgroup.mem_inf.mp hy
    have hytc : Commute y t := Subgroup.mem_centralizer_singleton_iff.mp hyt
    have hyutc : Commute y (u * t) := Subgroup.mem_centralizer_singleton_iff.mp hyut
    have hyu : Commute y u := by
      have h := hyutc.mul_right (Commute.inv_right hytc)
      rwa [show (u * t) * t⁻¹ = u from by group] at h
    have hyC : y ∈ Subgroup.centralizer ({u} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hyu
    have h2u : 2 ∣ orderOf u := by rw [hu2]
    have hle := Work.ThreePoints.IsStronglyEmbedded.centralizer_le (H := H) (x := u) hse huH h2u
    have hyH : y ∈ H := hle hyC
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hyH, ?_⟩, hyt⟩
    rw [Work.ThreePoints.mem_conj_iff]
    have hconv : t⁻¹ * y * t = y := by
      calc t⁻¹ * y * t = t⁻¹ * (y * t) := by group
        _ = t⁻¹ * (t * y) := by rw [hytc.eq]
        _ = y := by group
    rw [hconv]
    exact hyH

/-- Sylow conjugacy, in the form used below: if a subgroup `S ≤ H` is a Sylow `r`-subgroup of `G`
then every `r`-element of `G` lies in a conjugate of `H`. -/
theorem exists_conj_mem_of_isPGroup {G : Type*} [Group G] [Finite G]
    {H S : Subgroup G} {r : ℕ} (hr : r.Prime) (hSH : S ≤ H) (hSp : IsPGroup r S)
    (hidx : ¬ r ∣ S.index) {x : G} (hx : IsPGroup r (Subgroup.zpowers x)) :
    ∃ g : G, x ∈ H.map (MulAut.conj g).toMonoidHom := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  have hSs : ((hSp.toSylow hidx : Sylow r G) : Subgroup G) = S := IsPGroup.toSylow_coe hSp hidx
  obtain ⟨T, hT⟩ := IsPGroup.exists_le_sylow hx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (hSp.toSylow hidx : Sylow r G) T
  have hxT : x ∈ (T : Subgroup G) := hT (Subgroup.mem_zpowers x)
  have hTS : (T : Subgroup G) = S.map (MulAut.conj g).toMonoidHom := by
    have h1 : (T : Subgroup G) = MulAut.conj g • (S : Subgroup G) := by
      rw [← hg, Sylow.coe_subgroup_smul, hSs]
    rw [h1, Subgroup.pointwise_smul_def]
    rfl
  refine ⟨g, Subgroup.map_mono hSH ?_⟩
  rwa [← hTS]

/-- `Mset u t = J(C_G(ut), t)`: the elements of `C_G(ut)` inverted by `t`. -/
theorem mset_eq_kset {G : Type*} [Group G] {u t : G} :
    Work.NormalComplement.Design.Mset u t =
      Kset (Subgroup.centralizer ({u * t} : Set G)) t := rfl

/-- App. I (1)(b) with `d = 2`: `Kapp t X = J(X,t)` for `X` of odd order normalised by `t`. -/
theorem kapp_eq_mset {G : Type*} [Group G] [Finite G] {u t : G} (ht : orderOf t = 2)
    (htX : NormalizedBy t (Subgroup.centralizer ({u * t} : Set G)))
    (hodd : Odd (Nat.card ↥(Subgroup.centralizer ({u * t} : Set G)))) :
    Kapp t (Subgroup.centralizer ({u * t} : Set G)) = Work.NormalComplement.Design.Mset u t :=
  (appI_one (d := 2) Nat.prime_two ht htX (Nat.coprime_two_right.mpr hodd)).2 rfl |>.1

/-- App. I (5)(b) with `d = 2`: if `(|K+|, |F(C_X(t))|) = 1` then `Kapp t X` is the underlying
set of an abelian subgroup of `G`. -/
theorem exists_abelian_subgroup_of_coprime {G : Type*} [Group G] [Finite G]
    {X : Subgroup G} {t : G} (ht : orderOf t = 2) (htX : NormalizedBy t X)
    (hodd : Odd (Nat.card ↥X)) (hsolv : Group.IsSolvable ↥X)
    (hcop : Nat.Coprime (Kapp t X).ncard
      (Nat.card ↥(Work.Fitting.fitting ↥(Subgroup.centralizer ({t} : Set G) ⊓ X)))) :
    ∃ K : Subgroup G, (K : Set G) = Kapp t X ∧
      ∀ x ∈ K, ∀ y ∈ K, x * y = y * x := by
  classical
  have hdX : Nat.Coprime (Nat.card X) 2 := Nat.coprime_two_right.mpr hodd
  have hKm : Kapp t X = Kset X t :=
    (appI_one (d := 2) Nat.prime_two ht htX hdX).2 rfl |>.1
  obtain ⟨K, hKset, _⟩ := appI_five_b (d := 2) Nat.prime_two ht htX hdX hsolv hcop
  refine ⟨K, hKset, ?_⟩
  have hmem : ∀ x : G, x ∈ K ↔ x ∈ Kset X t := by
    intro x
    show x ∈ (K : Set G) ↔ x ∈ Kset X t
    rw [hKset, hKm]
  intro x hx y hy
  have hxy : x * y ∈ K := K.mul_mem hx hy
  have h1 : t * (x * y) * t⁻¹ = (x * y)⁻¹ := ((hmem (x * y)).mp hxy).2
  have h2 : (x * y)⁻¹ = (y * x)⁻¹ := by
    rw [← h1]
    calc t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) := by group
      _ = x⁻¹ * y⁻¹ := by rw [((hmem x).mp hx).2, ((hmem y).mp hy).2]
      _ = (y * x)⁻¹ := by group
  exact inv_injective h2

theorem prop2b (hFT : Submission.Blueprint.FeitThompsonProp)
    (hA : Submission.Blueprint.ThmAProp) (hC : Submission.Blueprint.ThmCProp)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp)
    (hIII : Work.NormalComplement.AppIIIProp)
    (hMF2 : Submission.Blueprint.BenderModelFacts2Prop)
    (hCor1 : Work.NormalComplement.Design.ChISixCor1Prop)
    (hBC : Work.NormalComplement.Design.BurnsideClassProp)
    (hBP : Work.NormalComplement.BenderPrelimProp) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) (u : G)
    (hu : u ∈ H ∧ orderOf u = 2 ∧
      u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G))
    (hf : orderOf (u * t) = 3 ∨ orderOf (u * t) = 5) :
    (∀ x ∈ Work.NormalComplement.Design.Mset u t, x ≠ 1 →
        Submission.Blueprint.fixedPts H (Subgroup.zpowers x) = ∅) ∧
      Nat.Coprime (Work.NormalComplement.Design.Mset u t).ncard
        (Nat.card ↥(Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t))) ∧
      ∃ M : Subgroup G, (M : Set G) = Work.NormalComplement.Design.Mset u t ∧
        (∀ x ∈ M, ∀ y ∈ M, x * y = y * x) := by
  classical
  haveI : Fact r.Prime := ⟨h.r_prime⟩
  have ht2 : t * t = 1 := by
    have hh := pow_orderOf_eq_one t; rw [h.invol] at hh; simpa [pow_two] using hh
  have hu2 : u * u = 1 := by
    have hh := pow_orderOf_eq_one u; rw [hu.2.1] at hh; simpa [pow_two] using hh
  -- `X = C_G(ut)` is normalised by `t` and has odd order; `V = C_X(t) = centD H t`.
  set X : Subgroup G := Subgroup.centralizer ({u * t} : Set G) with hXdef
  set V : Subgroup G := Subgroup.centralizer ({t} : Set G) ⊓ X with hVdef
  have htX : NormalizedBy t X := by
    rw [hXdef]
    exact normalizedBy_centralizer_mul h.invol hu.2.1
  have hVeq : V = Submission.Blueprint.centD H t := by
    rw [hVdef, hXdef]
    exact (centD_eq_inf_centralizer_mul h.se hu.1 hu.2.1 hu.2.2).symm
  have hVodd : Odd (Nat.card ↥V) := by
    rw [hVeq]
    exact Odd.of_dvd_nat (h.se.2.2 t h.notMem) (Subgroup.card_dvd_of_le inf_le_left)
  have hoddX : Odd (Nat.card ↥X) :=
    odd_card_inf_centralizer h.invol (mem_normalizer_of_normalizedBy htX) (by
      rw [inf_comm, ← hVdef]; exact hVodd)
  have hsolvX : Group.IsSolvable ↥X := hFT ↥X hoddX
  have hcopX : Nat.Coprime (Nat.card X) 2 := Nat.coprime_two_right.mpr hoddX
  have hKappMset : Kapp t X = Work.NormalComplement.Design.Mset u t := by
    rw [hXdef]
    exact kapp_eq_mset h.invol (hXdef ▸ htX) (hXdef ▸ hoddX)
  -- `|M| = |X : V|`
  have hMcard : (Work.NormalComplement.Design.Mset u t).ncard = (V.subgroupOf X).index := by
    have h := (appI_one (d := 2) Nat.prime_two h.invol htX hcopX).1
    rw [← hKappMset]
    exact h
  -- ## first conjunct: elements of `M#` fix no point
  have hfix : ∀ x ∈ Work.NormalComplement.Design.Mset u t, x ≠ 1 →
      Submission.Blueprint.fixedPts H (Subgroup.zpowers x) = ∅ :=
    fun x hx hx1 => fixedPts_zpowers_eq_empty_of_mem_Mset hCor1 hC4 h hu hx hx1 hf
  -- ## second conjunct: `(|M|, |F(V)|) = 1`
  have hFpow : ∀ q : ℕ, q.Prime →
      q ∣ Nat.card ↥(Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t)) →
      q = r := by
    intro q hq hdvd
    have hpg : IsPGroup r (Work.NormalComplement.Design.fitSub
        (Submission.Blueprint.centD H t)) := h.fitV_syl.1
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpg
    rw [hn] at hdvd
    exact (Nat.prime_dvd_prime_iff_eq hq h.r_prime).mp (hq.dvd_of_dvd_pow hdvd)
  have hr_not : ¬ r ∣ (Work.NormalComplement.Design.Mset u t).ncard := by
    intro hrdvd
    have hidx : r ∣ V.relIndex X := by
      rw [hMcard] at hrdvd
      exact hrdvd
    -- a `t`-invariant Sylow `r`-subgroup `R` of `X`
    obtain ⟨⟨R, hRsyl, hRn⟩, -, -⟩ :=
      appI_two (d := 2) Nat.prime_two h.invol htX hcopX (p := r) h.r_prime
    -- `R ⊄ V`
    have hRnotV : ¬ R ≤ V := by
      intro hRV
      have hdiv : r ∣ R.relIndex X := by
        have hprod : R.relIndex V * V.relIndex X = R.relIndex X :=
          Subgroup.relIndex_mul_relIndex R V X hRV inf_le_right
        rw [← hprod]
        exact dvd_mul_of_dvd_right hidx _
      exact hRsyl.2.2 hdiv
    have hRodd : Odd (Nat.card ↥R) :=
      Odd.of_dvd_nat hoddX (Subgroup.card_dvd_of_le hRsyl.2.1)
    have hcopR : Nat.Coprime (Nat.card R) 2 := Nat.coprime_two_right.mpr hRodd
    obtain ⟨-, hRcomp⟩ := appI_one (d := 2) Nat.prime_two h.invol hRn hcopR
    obtain ⟨hRKset, hRdecomp⟩ := hRcomp rfl
    -- a nontrivial element of `Kset R t ⊆ M`
    obtain ⟨z, hzR, hzV⟩ := Set.not_subset.mp hRnotV
    obtain ⟨⟨c, k⟩, ⟨hcC, hcR, hkKapp, hck⟩, -⟩ := hRdecomp z hzR
    have hkKsetR : k ∈ Kset R t := by rw [hRKset] at hkKapp; exact hkKapp
    have hkne : k ≠ 1 := by
      intro hk1
      apply hzV
      have hzc : z = c := by rw [← hck, hk1, mul_one]
      rw [hzc]
      exact ⟨hcC, hRsyl.2.1 hcR⟩
    have hkR : k ∈ R := hkKsetR.1
    have hkX : k ∈ Kset X t := Kset_mono hRsyl.2.1 hkKsetR
    have hkM : k ∈ Work.NormalComplement.Design.Mset u t := by
      rw [hXdef] at hkX
      exact hkX
    have hfixk : Submission.Blueprint.fixedPts H (Subgroup.zpowers k) = ∅ := hfix k hkM hkne
    -- but any `r`-element of `G` lies in a conjugate of `H`, hence fixes a point
    have hrK : r ∣ (Kset (twoPoint H t) t).ncard := by
      obtain ⟨a, ha1, haeq⟩ := h.K_card
      rw [haeq]
      exact dvd_mul_of_dvd_left (dvd_pow_self r (by omega)) _
    obtain ⟨Rg, hRgD, hRgp, hRgidx⟩ :=
      sec4_P2d (H := H) (t := t) hC4 h.sit h.se h.invol h.notMem r h.r_prime hrK
    have hkpg : IsPGroup r (Subgroup.zpowers k) :=
      IsPGroup.to_le hRsyl.1 (Subgroup.zpowers_le.mpr hkR)
    obtain ⟨g, hg⟩ :=
      exists_conj_mem_of_isPGroup h.r_prime (hRgD.trans inf_le_left) hRgp hRgidx hkpg
    have hmem : (QuotientGroup.mk g : G ⧸ H) ∈
        Submission.Blueprint.fixedPts H (Subgroup.zpowers k) := by
      rw [Work.DoubleTransitivity.mk_mem_fixedPts_iff]
      exact Subgroup.zpowers_le.mpr hg
    rw [hfixk] at hmem
    exact hmem
  have hcopM : Nat.Coprime (Work.NormalComplement.Design.Mset u t).ncard
      (Nat.card ↥(Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t))) := by
    refine Nat.coprime_of_dvd' ?_
    intro q hq hqM hqF
    rw [hFpow q hq hqF] at hqM
    exact absurd hqM hr_not
  -- ## third conjunct: `M` is an abelian subgroup
  have hcopK : Nat.Coprime (Kapp t X).ncard
      (Nat.card ↥(Work.Fitting.fitting ↥(Subgroup.centralizer ({t} : Set G) ⊓ X))) := by
    have h1 : Nat.card ↥(Work.Fitting.fitting ↥(Subgroup.centralizer ({t} : Set G) ⊓ X)) =
        Nat.card ↥(Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t)) := by
      rw [show Subgroup.centralizer ({t} : Set G) ⊓ X = V from rfl, hVeq,
        Work.NormalComplement.Design.fitSub,
        Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    rw [hKappMset, h1]
    exact hcopM
  have habM : ∃ M : Subgroup G, (M : Set G) = Work.NormalComplement.Design.Mset u t ∧
      (∀ x ∈ M, ∀ y ∈ M, x * y = y * x) := by
    obtain ⟨K, hK, hab⟩ := exists_abelian_subgroup_of_coprime h.invol htX hoddX hsolvX hcopK
    exact ⟨K, by rw [hK, hKappMset], hab⟩
  exact ⟨hfix, hcopM, habM⟩

end Work.NormalComplement.Sec5Fix

