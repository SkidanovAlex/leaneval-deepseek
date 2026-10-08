import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.Coprime.All
import Submission.Work.ThreePoints.ThmC.pPrimeCoreSub_conj
import Submission.Work.NormalComplement.card_sup_mul_card_inf
import Submission.Work.NormalComplement.Sec3Aux
import Submission.Work.NormalComplement.appI_five_d_corrected

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.NormalComplement.Sec5Fix.NF

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-! ## Elementary helpers -/

/-- `|X| ∣ |H|` for subgroups `X ≤ H`. -/
private theorem card_dvd_card_of_le {G : Type*} [Group G] [Finite G] {X H : Subgroup G}
    (h : X ≤ H) : Nat.card ↥X ∣ Nat.card ↥H := by
  have h1 : X.relIndex H * Nat.card ↥X = Nat.card ↥H := by
    have h2 := Subgroup.index_mul_card (X.subgroupOf H)
    rw [show (X.subgroupOf H).index = X.relIndex H from rfl] at h2
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv] at h2
  exact ⟨X.relIndex H, by rw [mul_comm, h1]⟩

/-- If `H` normalizes `K`, every element of `H ⊔ K` is a product `h * k`. -/
private theorem exists_mul_of_mem_sup_of_le_normalizer {G : Type*} [Group G] {H K : Subgroup G}
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, h * k = x := by
  let S : Subgroup G :=
    { carrier := {x | ∃ h ∈ H, ∃ k ∈ K, h * k = x}
      mul_mem' := by
        rintro x y ⟨h1, hh1, k1, hk1, rfl⟩ ⟨h2, hh2, k2, hk2, rfl⟩
        have hk1' : h2⁻¹ * k1 * h2 ∈ K := by
          have hh := (Subgroup.mem_normalizer_iff.mp
            ((Subgroup.normalizer (K : Set G)).inv_mem (hHK hh2)) k1).mp hk1
          simpa [inv_inv] using hh
        exact ⟨h1 * h2, H.mul_mem hh1 hh2, (h2⁻¹ * k1 * h2) * k2,
          K.mul_mem hk1' hk2, by group⟩
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
      inv_mem' := by
        rintro x ⟨h, hh, k, hk, rfl⟩
        refine ⟨h⁻¹, H.inv_mem hh, h * k⁻¹ * h⁻¹, ?_, by group⟩
        exact (Subgroup.mem_normalizer_iff.mp (hHK hh) k⁻¹).mp (K.inv_mem hk) }
  have hS : H ⊔ K ≤ S := by
    rw [Subgroup.sup_eq_closure]
    refine (Subgroup.closure_le S).mpr ?_
    rintro x (hx | hx)
    · exact ⟨x, hx, 1, K.one_mem, by simp⟩
    · exact ⟨1, H.one_mem, x, hx, by simp⟩
  exact hS hx

/-! ## The three pieces of §5 Prop. 3 -/

/-- **`V = C_D(t)` normalizes `M = {x ∈ C_G(ut) | x^t = x⁻¹}`** (Peterfalvi I Ch. III §5
Prop. 3, "`V` normalises `M`").  For `v ∈ V`, `v` commutes with both `u` (hypothesis `hu`) and
`t` (definition of `V = centD`), hence conjugation by `v` preserves the two defining conditions
of `M`. -/
private theorem centD_le_normalizer_mset {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t u : G} {M : Subgroup G}
    (hu : u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G))
    (hM : (M : Set G) = Work.NormalComplement.Design.Mset u t) :
    Submission.Blueprint.centD H t ≤ Subgroup.normalizer (M : Set G) := by
  have hMset : ∀ y : G, (y ∈ M) ↔ (y ∈ Work.NormalComplement.Design.Mset u t) := by
    intro y
    have hh := congrArg (fun S : Set G => y ∈ S) hM
    simpa using hh
  have key : ∀ w ∈ Submission.Blueprint.centD H t,
      ∀ x ∈ Work.NormalComplement.Design.Mset u t,
      w * x * w⁻¹ ∈ Work.NormalComplement.Design.Mset u t := by
    intro w hw x hx
    have hwC : w ∈ Subgroup.centralizer ({t} : Set G) := (Subgroup.mem_inf.mp hw).2
    have hwt : w * t = t * w := Subgroup.mem_centralizer_singleton_iff.mp hwC
    have hwu : w * u = u * w := (Subgroup.mem_centralizer_iff.mp hu) w hw
    obtain ⟨hxC, hxinv⟩ := hx
    have hxut : x * (u * t) = (u * t) * x :=
      Subgroup.mem_centralizer_singleton_iff.mp hxC
    have hwut : w * (u * t) = (u * t) * w := by
      have h1 : Commute w u := hwu
      have h2 : Commute w t := hwt
      exact h1.mul_right h2
    have hwut' : w⁻¹ * (u * t) = (u * t) * w⁻¹ := by
      have h1 : Commute w u := hwu
      have h2 : Commute w t := hwt
      exact h1.inv_left.mul_right h2.inv_left
    have hwtv : t * w * t⁻¹ = w := by rw [← hwt]; group
    refine ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc (w * x * w⁻¹) * (u * t) = w * x * (w⁻¹ * (u * t)) := by group
        _ = w * x * ((u * t) * w⁻¹) := by rw [hwut']
        _ = w * (x * (u * t)) * w⁻¹ := by group
        _ = w * ((u * t) * x) * w⁻¹ := by rw [hxut]
        _ = (w * (u * t)) * x * w⁻¹ := by group
        _ = ((u * t) * w) * x * w⁻¹ := by rw [hwut]
        _ = (u * t) * (w * x * w⁻¹) := by group
    · calc t * (w * x * w⁻¹) * t⁻¹ = (t * w * t⁻¹) * (t * x * t⁻¹) * (t * w * t⁻¹)⁻¹ := by
            group
        _ = w * x⁻¹ * w⁻¹ := by rw [hwtv, hxinv]
        _ = (w * x * w⁻¹)⁻¹ := by group
  intro v hv
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [hMset x, hMset (v * x * v⁻¹)]
  constructor
  · intro hx; exact key v hv x hx
  · intro hx
    have h1 := key v⁻¹ ((Submission.Blueprint.centD H t).inv_mem hv) (v * x * v⁻¹) hx
    have h2 : v⁻¹ * (v * x * v⁻¹) * v⁻¹⁻¹ = x := by group
    rwa [h2] at h1

/-- **`p ∤ |N|` when a group `P` of order `p` acts fixed-point-freely on `N`** (the arithmetic
half of Peterfalvi I Ch. III §5 Prop. 2 (d)).  `FpfOn P N` gives `C_N(P) = 1`, and the
fixed-point congruence of a `p`-group action then gives `|N| ≡ 1 (mod p)`. -/
private theorem not_dvd_card_of_fpf {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {P N : Subgroup G} (hPN : P ≤ Subgroup.normalizer (N : Set G)) (hcard : Nat.card P = p)
    (hfp : Work.NormalComplement.Design.FpfOn P (N : Set G)) : ¬ p ∣ Nat.card ↥N := by
  refine Work.NormalComplement.not_dvd_card_of_fpf_pgroup hp hPN ?_ ?_
  · haveI : Fact p.Prime := ⟨hp⟩
    rw [IsPGroup.iff_card]
    exact ⟨1, by rw [hcard, pow_one]⟩
  · intro a ha hfix
    by_contra ha1
    have hPne : P ≠ ⊥ := by
      intro hbot
      have hc : Nat.card ↥P = p := hcard
      rw [hbot, Subgroup.card_bot] at hc
      exact hp.ne_one hc.symm
    obtain ⟨x, hxP, hx1⟩ : ∃ x ∈ P, x ≠ 1 := by
      by_contra hc
      push_neg at hc
      exact hPne (Subgroup.eq_bot_iff_forall P |>.mpr (fun x hx => hc x hx))
    exact ha1 (hfp x hxP hx1 a ha (hfix x hxP))

/-- **Coprime action: `[A,P] = [[A,P],P]`** (the "`G = C_G(A)·[G,A]`" decomposition of the
coprime action), for `P` a group of prime order normalizing `A` with `(|P|,|A|) = 1`.  Since
`A = C_A(P)·[A,P]`, the commutator `[A,P]` is generated by commutators `⁅c f c⁻¹, p⁆`, `f ∈ [A,P]`. -/
private theorem commutator_eq_self_of_coprime {G : Type} [Group G] [Finite G]
    {A P : Subgroup G} (hPN : P ≤ Subgroup.normalizer (A : Set G))
    (hcop : Nat.Coprime (Nat.card P) (Nat.card A))
    (hsol : Group.IsSolvable ↥P ∨ Group.IsSolvable ↥A) :
    ⁅A, P⁆ = ⁅⁅A, P⁆, P⁆ := by
  classical
  haveI : FT.Normalizes P A := ⟨hPN⟩
  have hsplit_abs := Work.Coprime.commutator_fixedPoints_sup ↥P (G := ↥A) hcop hsol
  have hsplit : (Subgroup.centralizer (P : Set G) ⊓ A) ⊔ ⁅A, P⁆ = A := by
    have h := congrArg (Subgroup.map A.subtype) hsplit_abs
    rw [Subgroup.map_sup, Subgroup.map_top, FT.map_fixedPoints_conjAction,
      FT.commutator_conjAction] at h
    rwa [Subgroup.range_subtype] at h
  have hANF : A ≤ Subgroup.normalizer ((⁅A, P⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_left A P
  have hPNF : P ≤ Subgroup.normalizer ((⁅A, P⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_right A P
  refine le_antisymm ?_ ?_
  · refine Subgroup.commutator_le.mpr ?_
    intro a ha p hp
    have ha' : a ∈ (Subgroup.centralizer (P : Set G) ⊓ A) ⊔ ⁅A, P⁆ := by
      rw [hsplit]; exact ha
    obtain ⟨c, hc, f, hf, hcf⟩ :=
      exists_mul_of_mem_sup_of_le_normalizer (H := Subgroup.centralizer (P : Set G) ⊓ A)
        (K := ⁅A, P⁆) (inf_le_right.trans hANF) ha'
    have hcC : c ∈ Subgroup.centralizer (P : Set G) := hc.1
    have hcA : c ∈ A := hc.2
    have hcNF : c ∈ Subgroup.normalizer ((⁅A, P⁆ : Subgroup G) : Set G) := hANF hcA
    have hcp : c * p = p * c := ((Subgroup.mem_centralizer_iff.mp hcC) p hp).symm
    have hcp' : c * p * c⁻¹ = p := by rw [hcp]; group
    have hcpC : ⁅c, p⁆ = 1 := by rw [commutatorElement_def, hcp]; group
    have hkey : ⁅a, p⁆ = c * ⁅f, p⁆ * c⁻¹ := by
      rw [← hcf, commutatorElement_mul_left_eq_conj_mul, hcpC, mul_one]
    have hcF : c * f * c⁻¹ ∈ ⁅A, P⁆ := (Subgroup.mem_normalizer_iff.mp hcNF f).mp hf
    have hkey2 : c * ⁅f, p⁆ * c⁻¹ = ⁅c * f * c⁻¹, p⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc c * (f * p * f⁻¹ * p⁻¹) * c⁻¹
          = (c * f * c⁻¹) * (c * p * c⁻¹) * (c * f * c⁻¹)⁻¹ * (c * p * c⁻¹)⁻¹ := by
            group
        _ = (c * f * c⁻¹) * p * (c * f * c⁻¹)⁻¹ * p⁻¹ := by rw [hcp']
    rw [hkey, hkey2]
    exact Subgroup.commutator_mem_commutator hcF hp
  · refine Subgroup.commutator_le.mpr ?_
    intro f hf p hp
    have h1 : p * f⁻¹ * p⁻¹ ∈ ⁅A, P⁆ :=
      (Subgroup.mem_normalizer_iff.mp (hPNF hp) f⁻¹).mp ((⁅A, P⁆).inv_mem hf)
    have h2 : ⁅f, p⁆ = f * (p * f⁻¹ * p⁻¹) := by rw [commutatorElement_def]; group
    rw [h2]
    exact (⁅A, P⁆).mul_mem hf h1

/-- `N_G(M) ≤ N_G(O_{p'}(M))` for a prime `p` (`O_{p'}(M)` is characteristic in `M`). -/
private theorem normalizer_le_normalizer_pPrimeCoreSub {G : Type} [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (M : Subgroup G) :
    Subgroup.normalizer (M : Set G) ≤
      Subgroup.normalizer (Work.NormalComplement.pPrimeCoreSub p M : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hx ⊢
  have h := Work.ThreePoints.ThmC.pPrimeCoreSub_conj p hp M x
  simp only [Submission.Blueprint.conj] at h
  have hx' : Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj x)) M = M := hx
  rw [hx'] at h
  exact h.symm

/-! ## The target -/

theorem fitting_le_centralizer
    (hFT : Submission.Blueprint.FeitThompsonProp)
    (hVII : Work.NormalComplement.Design.AppVIIProp) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) (u : G)
    (hu : u ∈ H ∧ orderOf u = 2 ∧
      u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G))
    (hf : orderOf (u * t) = 3 ∨ orderOf (u * t) = 5)
    (hB : (∀ x ∈ Work.NormalComplement.Design.Mset u t, x ≠ 1 →
        Submission.Blueprint.fixedPts H (Subgroup.zpowers x) = ∅) ∧
      Nat.Coprime (Work.NormalComplement.Design.Mset u t).ncard
        (Nat.card ↥(Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t))))
    (M : Subgroup G) (hM : (M : Set G) = Work.NormalComplement.Design.Mset u t)
    (hMc : H ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (M : Set G))
    (hMd : Work.NormalComplement.pPrimeCoreSub (orderOf (u * t)) M ≠ ⊥ ∧
      Work.NormalComplement.Design.FpfOn P
        (Work.NormalComplement.pPrimeCoreSub (orderOf (u * t)) M : Set G)) :
    Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t) ≤
      Subgroup.centralizer
        ((Work.NormalComplement.pPrimeCoreSub (orderOf (u * t)) M : Subgroup G) : Set G) := by
  classical
  set V : Subgroup G := Submission.Blueprint.centD H t with hV
  set F : Subgroup G := Work.NormalComplement.Design.fitSub V with hF
  set N : Subgroup G := Work.NormalComplement.pPrimeCoreSub (orderOf (u * t)) M with hN
  have hfprime : (orderOf (u * t)).Prime := by rcases hf with hh | hh <;> rw [hh] <;> norm_num
  -- Unfolding lemmas for the local abbreviations.
  have hFV : F = Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t) := by
    rw [hF, hV]
  have hFVle : F ≤ V := by rw [hF]; exact Work.NormalComplement.fitSub_le V
  have hVNF : V ≤ Subgroup.normalizer (F : Set G) := by
    rw [hF]; exact Work.NormalComplement.fitSub_le_normalizer V
  have hBV : Nat.Coprime (Work.NormalComplement.Design.Mset u t).ncard (Nat.card ↥F) := by
    rw [hF, hV]; exact hB.2
  have hfitV : F = Work.NormalComplement.Design.Ecomm H t W ⊓ Submission.Blueprint.centD H t := by
    rw [hF, hV]; exact h.fitV
  have hFA : F = ⁅A, P⁆ := by rw [hfitV, h.E'V]
  have hFr : IsPGroup r ↥F := by
    simpa [hFV] using h.fitV_syl.1
  -- `V ≤ H`, `V ≤ D`, `P ≤ V`, `A ≤ V`
  have hVH : V ≤ H := by
    rw [hV]
    intro x hx
    exact (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).1
  have hVD : V ≤ Submission.Blueprint.twoPoint H t := by rw [hV]; exact inf_le_left
  have hPV : P ≤ V := by rw [hV]; exact h.P_le.trans inf_le_right
  have hAV : A ≤ V := by rw [hV]; exact h.A_le
  have hVNA : V ≤ Subgroup.normalizer (A : Set G) := by rw [hV]; exact h.A_normal
  have hPN_A : P ≤ Subgroup.normalizer (A : Set G) := hPV.trans hVNA
  -- `V` normalizes `M` and `N`
  have hVM : V ≤ Subgroup.normalizer (M : Set G) := by
    rw [hV]; exact centD_le_normalizer_mset hu.2.2 hM
  have hMN : Subgroup.normalizer (M : Set G) ≤ Subgroup.normalizer (N : Set G) := by
    rw [hN]; exact normalizer_le_normalizer_pPrimeCoreSub (orderOf (u * t)) hfprime M
  have hVN : V ≤ Subgroup.normalizer (N : Set G) := hVM.trans hMN
  have hFN : F ≤ Subgroup.normalizer (N : Set G) := hFVle.trans hVN
  have hPN : P ≤ Subgroup.normalizer (N : Set G) := hPV.trans hVN
  have hPNF : P ≤ Subgroup.normalizer (F : Set G) := hPV.trans hVNF
  -- Arithmetic: `p ≠ r`, `p ∤ |F|`, `|F ⊓ C(P)|` odd.
  have hpr : p ≠ r := by
    intro hpr
    have hp2 : p ∣ 2 ^ p - 1 := hpr.symm ▸ h.r_dvd
    haveI : Fact p.Prime := ⟨h.prime⟩
    have hzero : ((2 ^ p - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hp2
    have hle : (1 : ℕ) ≤ 2 ^ p := Nat.one_le_two_pow
    have hcast : ((2 ^ p - 1 : ℕ) : ZMod p) = (2 : ZMod p) ^ p - 1 := by
      rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
    rw [hcast, ZMod.pow_card] at hzero
    norm_num at hzero
  have hFcard : ∃ k, Nat.card ↥F = r ^ k := by
    haveI : Fact r.Prime := ⟨h.r_prime⟩
    exact (IsPGroup.iff_card (p := r)).mp hFr
  have hpQ : ¬ Nat.card P ∣ Nat.card ↥F := by
    obtain ⟨k, hk⟩ := hFcard
    rw [h.P_card, hk]
    intro hd
    exact hpr ((Nat.prime_dvd_prime_iff_eq h.prime h.r_prime).mp (h.prime.dvd_of_dvd_pow hd))
  have hodd : Odd (Nat.card ↥(F ⊓ Subgroup.centralizer (P : Set G))) := by
    haveI : Fact r.Prime := ⟨h.r_prime⟩
    have hXr : IsPGroup r ↥(F ⊓ Subgroup.centralizer (P : Set G)) := hFr.to_le inf_le_left
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := r)).mp hXr
    rw [hk]
    have hodd2 : Odd (2 ^ p - 1) := by
      have h2p : 2 ^ p = 2 * 2 ^ (p - 1) := by
        have hp1 : 0 < p := h.prime.pos
        have hp : p = (p - 1) + 1 := by omega
        conv_lhs => rw [hp]
        exact pow_succ' 2 (p - 1)
      refine ⟨2 ^ (p - 1) - 1, ?_⟩
      have hpos : 1 ≤ 2 ^ (p - 1) := Nat.one_le_two_pow
      rw [h2p]
      omega
    exact (Odd.of_dvd_nat hodd2 h.r_dvd).pow (n := k)
  -- `N ⊓ C(P) = ⊥`
  have hPne : P ≠ ⊥ := by
    intro hbot
    have hc : Nat.card ↥P = p := h.P_card
    rw [hbot, Subgroup.card_bot] at hc
    exact h.prime.ne_one hc.symm
  have hPne' : ∃ x ∈ P, x ≠ 1 := by
    by_contra hc
    push_neg at hc
    exact hPne (Subgroup.eq_bot_iff_forall P |>.mpr (fun x hx => hc x hx))
  have hNbot : N ⊓ Subgroup.centralizer (P : Set G) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro k hk
    obtain ⟨hkN, hkC⟩ := Subgroup.mem_inf.mp hk
    obtain ⟨x, hxP, hx1⟩ := hPne'
    have hfix : x * k * x⁻¹ = k := by
      have hh := (Subgroup.mem_centralizer_iff.mp hkC) x hxP
      rw [hh]; group
    exact hMd.2 x hxP hx1 k hkN hfix
  -- `F ⊓ P = ⊥` (`F` is an `r`-group, `P` a `p`-group, `r ≠ p`)
  have hPr : IsPGroup p ↥P := by
    haveI : Fact p.Prime := ⟨h.prime⟩
    rw [IsPGroup.iff_card]
    exact ⟨1, by rw [h.P_card, pow_one]⟩
  have hFPbot : F ⊓ P = ⊥ := by
    haveI : Fact r.Prime := ⟨h.r_prime⟩
    haveI : Fact p.Prime := ⟨h.prime⟩
    have hXr : IsPGroup r ↥(F ⊓ P) := hFr.to_le inf_le_left
    have hXp : IsPGroup p ↥(F ⊓ P) := hPr.to_le inf_le_right
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := r)).mp hXr
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card (p := p)).mp hXp
    have ha0 : a = 0 := by
      by_contra ha0
      have hdvd1 : r ∣ r ^ a := by
        simpa using pow_dvd_pow r (show 1 ≤ a from Nat.one_le_iff_ne_zero.mpr ha0)
      have hdvd : r ∣ p ^ b := by rw [← hb, ha]; exact hdvd1
      have hrp : r ∣ p := h.r_prime.dvd_of_dvd_pow hdvd
      exact hpr ((Nat.prime_dvd_prime_iff_eq h.r_prime h.prime).mp hrp).symm
    exact Subgroup.card_eq_one.mp (by rw [ha, ha0, pow_zero])
  -- Coprimality `(|N|, |F ⊔ P|) = 1`
  have hMncard : Nat.card ↥M = (M : Set G).ncard := Nat.card_coe_set_eq (M : Set G)
  have hNM : N ≤ M := by rw [hN]; exact Subgroup.map_subtype_le _
  have hdvd : Nat.card ↥N ∣ (Work.NormalComplement.Design.Mset u t).ncard := by
    have h1 : Nat.card ↥N ∣ Nat.card ↥M := card_dvd_card_of_le hNM
    rwa [hMncard, hM] at h1
  have hcopF : Nat.Coprime (Nat.card ↥N) (Nat.card ↥F) :=
    Nat.Coprime.coprime_dvd_left hdvd hBV
  have hpN : ¬ p ∣ Nat.card ↥N := not_dvd_card_of_fpf h.prime hPN h.P_card hMd.2
  have hcopp : Nat.Coprime (Nat.card ↥N) p := (h.prime.coprime_iff_not_dvd.mpr hpN).symm
  have hsupcard : Nat.card ↥(F ⊔ P) = Nat.card ↥F * p := by
    have hFK := Work.NormalComplement.card_sup_mul_card_inf (H := F) (K := P) hPNF
    rw [hFPbot, Subgroup.card_bot, mul_one, h.P_card] at hFK
    exact hFK
  have hcop : Nat.Coprime (Nat.card ↥N) (Nat.card ↥(F ⊔ P)) := by
    rw [hsupcard]; exact hcopF.mul_right hcopp
  -- Appendix VII
  have hPprime : (Nat.card P).Prime := by rw [h.P_card]; exact h.prime
  have happ := hVII hFT G N F P hFN hPN hPNF hPprime hpQ hodd hcop hNbot
  -- `p ∤ |A|`, so `(|P|,|A|) = 1`
  have hpA : ¬ p ∣ Nat.card ↥A := by
    have hPsylV : Work.NormalComplement.IsSylowIn p P V :=
      Work.NormalComplement.sylowIn_of_le_of_le h.P_syl hPV hVD
    have h1 : Nat.card ↥V = Nat.card ↥A * p := by
      have hh := Work.NormalComplement.card_sup_mul_card_inf (H := A) (K := P) hPN_A
      rw [h.A_sup, ← hV, h.A_inf, Subgroup.card_bot, mul_one, h.P_card] at hh
      exact hh
    have h2 : P.relIndex V * p = Nat.card ↥V := by
      have hh := Work.NormalComplement.relIndex_mul_card_of_le' (H := P) (K := V) hPV
      rwa [h.P_card] at hh
    have h3 : P.relIndex V = Nat.card ↥A := by
      have h4 : P.relIndex V * p = Nat.card ↥A * p := by rw [h2, h1]
      exact Nat.eq_of_mul_eq_mul_right h.prime.pos h4
    rw [← h3]
    exact hPsylV.2.2
  have hcopAP : Nat.Coprime (Nat.card P) (Nat.card A) := by
    rw [h.P_card]; exact h.prime.coprime_iff_not_dvd.mpr hpA
  have hDodd : Odd (Nat.card ↥(Submission.Blueprint.twoPoint H t)) := h.se.2.2 t h.notMem
  have hsolA : Group.IsSolvable ↥P ∨ Group.IsSolvable ↥A :=
    Or.inr (hFT ↥A (Odd.of_dvd_nat hDodd (card_dvd_card_of_le (hAV.trans hVD))))
  have hFself : F = ⁅F, P⁆ := by
    rw [hFA]
    exact commutator_eq_self_of_coprime hPN_A hcopAP hsolA
  -- Conclusion
  have hconc : F ≤ Subgroup.centralizer (N : Set G) := by
    rw [hFself, Subgroup.commutator_comm]
    exact happ
  rwa [hFV] at hconc

end Work.NormalComplement.Sec5Fix.NF
