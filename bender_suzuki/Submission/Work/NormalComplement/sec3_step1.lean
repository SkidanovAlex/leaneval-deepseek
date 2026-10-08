/-
# Peterfalvi I Ch. III §3 Prop. 1, step 1

This file proves `Work.NormalComplement.sec3_step1`, the first step of Peterfalvi's proof of
Ch. III §3 Proposition 1 (p.177), in the form required by the `NormalComplement` area.

Standing notation: `D = twoPoint H t = H ∩ H^t` with `t ∉ H` an involution, `V = centD H t = C_D(t)`
and `K = Kset D t = J(D,t) = {x ∈ D | t x t⁻¹ = x⁻¹}`.  The hypothesis `NoCentralizedNormal H t`
says that `C_K(X) = 1` for every `1 ≠ X ⊴ V`.

The conclusion is the paper's step 1:

* `C_V(K) = 1`;
* `(|K|, |F(V)|) = 1`;
* `K` is an abelian subgroup of `G` and a normal complement of `V` in `D`.

Arguments.

* For `C_V(K) = 1`: if `X = V ⊓ C_G(K) ≠ 1` then `X ⊴ V` and `X` centralises `K`, so the
  hypothesis gives `K = C_K(X) = 1`.  But `|K| = |Inv(H)| ≥ 2` (Peterfalvi I Ch. I §2 Prop. 1 (c)
  and Bender's theorem: a group of 2-rank `≥ 2` with a strongly embedded subgroup has at least
  two involutions in it), so `K ≠ 1`; contradiction.
* For the coprimality: let `q ∣ |F(V)|`.  Then the Sylow `q`-subgroup of the nilpotent group
  `F(V)` is nontrivial and normal in `V`, so the hypothesis gives `C_K(Q) = 1`.  The `q`-group `Q`
  acts on the set `K` by conjugation with `1` as its only fixed point, hence `|K| ≡ 1 (mod q)`
  (`Work.NormalComplement.orbit_conj_unique_fixed`) and `q ∤ |K|`.
* For the normal complement: App. I (5)(b) (`Work.NormalComplement.appI_five_b`, with `X = D`,
  `d = 2`) applies by the coprimality just proved, and produces a subgroup with underlying set
  `Kapp t D = Kset D t`.  Its elements are all inverted by `t`, and a subgroup all of whose
  elements are inverted by an involution is abelian.
-/
import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.appI_five_b
import Submission.Work.NormalComplement.appI_one
import Submission.Work.NormalComplement.appI_four
import Submission.Work.NormalComplement.appI_phi_surjective
import Submission.Work.NormalComplement.normal_pSubgroup_of_dvd_fitting
import Submission.Work.NormalComplement.orbit_conj_unique_fixed
import Submission.Work.ThmF.Bender.cardInvGeTwo
import Submission.Work.ThmF.Bender.cardKsetEqInv
import Submission.Work.Fitting.fitting_isNilpotent
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.fitting_eq_iSup_pCore
import Submission.Work.Fitting.centralizer_fitting_le

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.NormalComplement

variable {G : Type*} [Group G] [Finite G]

/-- An involution `t` normalises `D = twoPoint H t`: conjugation by `t` exchanges the two
factors `H` and `H^t` of the intersection. -/
private lemma normalizedBy_twoPoint_sec3 {H : Subgroup G} {t : G} (ht : orderOf t = 2) :
    NormalizedBy t (twoPoint H t) := by
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht] at h
    simpa [pow_two] using h
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  intro x hx
  rw [twoPoint, Subgroup.mem_inf] at hx ⊢
  obtain ⟨hxH, hxHt⟩ := hx
  rw [conj, Subgroup.mem_map] at hxHt ⊢
  obtain ⟨h, hh, hxh⟩ := hxHt
  have hx_eq : x = t * h * t⁻¹ := by rw [← hxh]; exact MulAut.conj_apply t h
  constructor
  · have hkey : t * x * t⁻¹ = h := by
      rw [hx_eq, hti]
      calc t * (t * h * t) * t = (t * t) * h * (t * t) := by group
        _ = h := by rw [ht2]; group
    rw [hkey]
    exact hh
  · exact ⟨x, hxH, MulAut.conj_apply t x⟩

theorem sec3_step1 (hFT : Submission.Blueprint.FeitThompsonProp) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G}
    (h : Work.NormalComplement.Design.Setup3 G H t W)
    (hN : Work.NormalComplement.Design.NoCentralizedNormal H t) :
    Submission.Blueprint.centD H t ⊓
        Subgroup.centralizer (Work.NormalComplement.Kset (Submission.Blueprint.twoPoint H t) t :
          Set G) = ⊥ ∧
      Nat.Coprime (Work.NormalComplement.Kset (Submission.Blueprint.twoPoint H t) t).ncard
        (Nat.card ↥(Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t))) ∧
      ∃ K : Subgroup G,
        (K : Set G) = Work.NormalComplement.Kset (Submission.Blueprint.twoPoint H t) t ∧
        Work.NormalComplement.IsNormalComplementOf K (Submission.Blueprint.centD H t)
          (Submission.Blueprint.twoPoint H t) ∧
        ∀ x ∈ K, ∀ y ∈ K, x * y = y * x := by
  classical
  -- ## Standing facts
  have ht : orderOf t = 2 := h.invol
  -- `D = twoPoint H t` has odd order, because `H` is strongly embedded and `t ∉ H`.
  have hDodd : Odd (Nat.card ↥(twoPoint H t)) := h.se.2.2 t h.notMem
  have hcopD : Nat.Coprime (Nat.card ↥(twoPoint H t)) 2 := Nat.coprime_two_right.mpr hDodd
  have htD : NormalizedBy t (twoPoint H t) := normalizedBy_twoPoint_sec3 ht
  -- `D` is solvable (odd order, Feit–Thompson).
  have hsolvD : Group.IsSolvable ↥(twoPoint H t) := hFT ↥(twoPoint H t) hDodd
  -- App. I (1) (`d = 2`) and App. I (4), with `X = D`.
  have hKapp : Kapp t (twoPoint H t) = Kset (twoPoint H t) t :=
    ((appI_one (d := 2) Nat.prime_two ht htD hcopD).2 rfl).1
  have hFour := (appI_four (d := 2) Nat.prime_two ht htD hcopD)
  -- `C_G(t) ⊓ D = V`
  have hVeq : (Subgroup.centralizer ({t} : Set G) ⊓ twoPoint H t : Subgroup G) =
      Submission.Blueprint.centD H t := by rw [centD, inf_comm]
  -- ## `V = centD H t` normalises `K = Kset D t`
  have hKV : ∀ k ∈ Kset (twoPoint H t) t, ∀ v ∈ centD H t,
      v * k * v⁻¹ ∈ Kset (twoPoint H t) t := by
    intro k hk v hv
    have hv' : v ∈ Subgroup.centralizer ({t} : Set G) ⊓ twoPoint H t := by
      rw [hVeq]; exact hv
    have h1 := hFour.2.1 k (hKapp ▸ hk) v hv'
    rwa [hKapp] at h1
  -- ## `|K| ≥ 2`
  have hKcard : 2 ≤ (Kset (twoPoint H t) t).ncard := by
    have h1 : (Kset (twoPoint H t) t).ncard = (involutions (H : Set G)).ncard :=
      Work.ThmF.Bender.cardKsetEqInv h.se ht h.notMem
    rw [h1]
    exact Work.ThmF.Bender.cardInvGeTwo h.se h.sit.1.1
  have hKne : Kset (twoPoint H t) t ≠ ({(1 : G)} : Set G) := by
    intro hEq
    have h1 : (Kset (twoPoint H t) t).ncard = 1 := by rw [hEq, Set.ncard_singleton]
    omega
  -- ## Step 1: `C_V(K) = 1`
  have hC1 : Submission.Blueprint.centD H t ⊓
      Subgroup.centralizer (Kset (twoPoint H t) t : Set G) = ⊥ := by
    by_contra hne
    set X : Subgroup G := Submission.Blueprint.centD H t ⊓
      Subgroup.centralizer (Kset (twoPoint H t) t : Set G) with hXdef
    have hXne : X ≠ ⊥ := by rw [hXdef]; exact hne
    have hXV : X ≤ Submission.Blueprint.centD H t := by rw [hXdef]; exact inf_le_left
    -- `X` is normalised by `V` (`V` preserves both `V` and `C_G(K)`)
    have hVnX : Submission.Blueprint.centD H t ≤ Subgroup.normalizer (X : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      intro v hv x hx
      have hxV : x ∈ Submission.Blueprint.centD H t := by rw [hXdef] at hx; exact hx.1
      have hxC : x ∈ Subgroup.centralizer (Kset (twoPoint H t) t : Set G) := by
        rw [hXdef] at hx; exact hx.2
      rw [hXdef, Subgroup.mem_inf]
      refine ⟨?_, ?_⟩
      · exact (Submission.Blueprint.centD H t).mul_mem
          ((Submission.Blueprint.centD H t).mul_mem hv hxV)
          ((Submission.Blueprint.centD H t).inv_mem hv)
      · rw [Subgroup.mem_centralizer_iff] at hxC ⊢
        intro k hk
        have hkv : v⁻¹ * k * v ∈ Kset (twoPoint H t) t := by
          simpa using hKV k hk v⁻¹ ((Submission.Blueprint.centD H t).inv_mem hv)
        have hcomm := hxC (v⁻¹ * k * v) hkv
        calc k * (v * x * v⁻¹) = v * ((v⁻¹ * k * v) * x) * v⁻¹ := by group
          _ = v * (x * (v⁻¹ * k * v)) * v⁻¹ := by rw [hcomm]
          _ = (v * x * v⁻¹) * k := by group
    -- the hypothesis applies, and `K` is contained in `C_G(X)`
    have hCK := hN X hXne hXV hVnX
    have hsub : Kset (twoPoint H t) t ⊆
        (Subgroup.centralizer (X : Set G) : Set G) := by
      intro k hk
      refine (Subgroup.mem_centralizer_iff (s := (X : Set G))).mpr ?_
      intro x hx
      have hxC : x ∈ (Subgroup.centralizer (Kset (twoPoint H t) t : Set G) : Set G) := by
        rw [hXdef] at hx; exact hx.2
      have hxC' := (Subgroup.mem_centralizer_iff (s := (Kset (twoPoint H t) t : Set G))).mp hxC
      exact (hxC' k hk).symm
    have hEq : Kset (twoPoint H t) t = ({(1 : G)} : Set G) := by
      have h2 := hCK
      rw [Work.NormalComplement.Design.CK, Set.inter_eq_left.mpr hsub] at h2
      exact h2
    exact hKne hEq
  -- ## Step 2: `(|K|, |F(V)|) = 1`
  have hC2 : Nat.Coprime (Kset (twoPoint H t) t).ncard
      (Nat.card ↥(Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t))) := by
    refine Nat.coprime_of_dvd' ?_
    intro q hq hqK hqF
    -- the Sylow `q`-subgroup of `F(V)` is a nontrivial normal `q`-subgroup of `V`
    obtain ⟨X, hXV, hVnX, hXpg, hXne⟩ :=
      normal_pSubgroup_of_dvd_fitting (V := Submission.Blueprint.centD H t) hq hqF
    have hCK := hN X hXne hXV hVnX
    -- the only element of `K` fixed by all of `X` is `1`
    have hfix : ∀ s ∈ Kset (twoPoint H t) t, (∀ x ∈ X, x * s * x⁻¹ = s) → s = 1 := by
      intro s hs hfixs
      have hmem : s ∈ Work.NormalComplement.Design.CK H t X := by
        refine ⟨hs, ?_⟩
        refine (Subgroup.mem_centralizer_iff (s := (X : Set G))).mpr ?_
        intro x hx
        have h1 := hfixs x hx
        calc x * s = x * s * x⁻¹ * x := by group
          _ = s * x := by rw [h1]
      rw [hCK] at hmem
      simpa using hmem
    have hinv : ∀ x ∈ X, ∀ s ∈ Kset (twoPoint H t) t,
        x * s * x⁻¹ ∈ Kset (twoPoint H t) t := by
      intro x hx s hs
      exact hKV s hs x (hXV hx)
    have h1K : (1 : G) ∈ Kset (twoPoint H t) t :=
      ⟨(twoPoint H t).one_mem, by simp⟩
    exact absurd hqK (orbit_conj_unique_fixed hq hXpg h1K hinv hfix)
  -- ## Step 3: `K` is an abelian subgroup, a normal complement of `V` in `D`
  have hfit : Nat.card ↥(Work.Fitting.fitting ↥(Subgroup.centralizer ({t} : Set G) ⊓
        twoPoint H t)) =
      Nat.card ↥(Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t)) := by
    rw [hVeq, Work.NormalComplement.Design.fitSub,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective (Submission.Blueprint.centD H t))]
  have hcopF : Nat.Coprime (Kapp t (twoPoint H t)).ncard
      (Nat.card ↥(Work.Fitting.fitting ↥(Subgroup.centralizer ({t} : Set G) ⊓
        twoPoint H t))) := by
    rw [hKapp, hfit]
    exact hC2
  obtain ⟨K, hKset, hKnc⟩ :=
    appI_five_b (d := 2) Nat.prime_two ht htD hcopD hsolvD hcopF
  refine ⟨hC1, hC2, K, ?_, ?_, ?_⟩
  · rw [hKset, hKapp]
  · rw [hVeq] at hKnc
    exact hKnc
  · -- a subgroup all of whose elements are inverted by `t` is abelian
    have hKmem : ∀ x : G, x ∈ K ↔ x ∈ Kset (twoPoint H t) t := by
      intro x
      show x ∈ (K : Set G) ↔ x ∈ Kset (twoPoint H t) t
      rw [hKset, hKapp]
    intro x hx y hy
    have hxK : x ∈ Kset (twoPoint H t) t := (hKmem x).mp hx
    have hyK : y ∈ Kset (twoPoint H t) t := (hKmem y).mp hy
    have hxyK : x * y ∈ Kset (twoPoint H t) t := (hKmem (x * y)).mp (K.mul_mem hx hy)
    have h1 : t * (x * y) * t⁻¹ = (x * y)⁻¹ := hxyK.2
    have h2 : (x * y)⁻¹ = (y * x)⁻¹ := by
      rw [← h1]
      calc t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) := by group
        _ = x⁻¹ * y⁻¹ := by rw [hxK.2, hyK.2]
        _ = (y * x)⁻¹ := by group
    exact inv_injective h2

end Work.NormalComplement
