import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.BadCountAssembly
import Submission.Work.CORE4.CentAPE
import Submission.Work.CORE4.CentKpE
import Submission.Work.CORE4.L2TorusNormE
import Submission.Work.CORE4.Case2Fibre9
import Submission.Work.CORE4.ProjOfInfBot
import Submission.Work.CORE4.Fibre9CardConj
import Submission.Work.CORE4.Fibre9ImageCard
import Submission.Work.CORE4.Fibre9SupProj
import Submission.Work.CORE4.Case2EightObjExists
import Submission.Work.CORE4.EightAeqOmega
import Submission.Work.CORE4.Case2EightA_le_FsupK0
import Submission.Work.CORE4.Case2Count11
import Submission.Work.CORE4.Case2EHcard
import Submission.Work.CORE4.Case2PerXBound9
import Submission.Work.CORE4.Case2LowerBound9
import Submission.Work.CORE4.Case2ParityQOf
import Submission.Work.CORE4.Case2KmulS0
import Submission.Work.CORE4.SevenFactsOfCtx
import Submission.Work.CORE4.Case2PrePlusOfCtx
import Submission.Work.CORE4.Case2CentCard
import Submission.Work.CORE4.Case2CountAssembly
import Submission.Work.CORE4.ConjSub.conjSub_mul
import Submission.Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot

namespace Work.CORE4

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private lemma card_subgroupOf_of_le_bcih {X Y : Subgroup G} (h : X ≤ Y) :
    Nat.card ↥(X.subgroupOf Y) = Nat.card ↥X := by
  have h1 := Subgroup.card_map_of_injective (f := Y.subtype) (K := X.subgroupOf Y)
    Y.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le h] at h1
  exact h1.symm

private lemma eq_of_le_of_card_eq_of_isCyclic_bcih {C : Subgroup G} (hC : IsCyclic ↥C)
    {X Y : Subgroup G} (hX : X ≤ C) (hY : Y ≤ C)
    (hcard : Nat.card ↥X = Nat.card ↥Y) : X = Y := by
  haveI : IsCyclic ↥C := hC
  have hcard' : Nat.card ↥(X.subgroupOf C) = Nat.card ↥(Y.subgroupOf C) := by
    rw [card_subgroupOf_of_le_bcih hX, card_subgroupOf_of_le_bcih hY, hcard]
  have hsub : X.subgroupOf C = Y.subgroupOf C :=
    (IsCyclic.subgroup_eq_iff_card_eq).mpr hcard'
  calc X = Subgroup.map C.subtype (X.subgroupOf C) :=
        (Subgroup.map_subgroupOf_eq_of_le hX).symm
    _ = Subgroup.map C.subtype (Y.subgroupOf C) := by rw [hsub]
    _ = Y := Subgroup.map_subgroupOf_eq_of_le hY

/-- **`p` divides `|K|`** for the prime `p` of §4 (8): `A ≤ F ⊔ K` has exponent `p` and order
`p²`, so it cannot lie in the cyclic `F`; an element of `A ∖ F` has a nontrivial `K`-coordinate of
order `p`. -/
lemma p_dvd_K_of_eightObj (I : Work.GW2.C4Inputs) {B : Work.GW2.BenderSetup G}
    (h : Work.GW2.Case2Ctx B) {p : ℕ}
    {P A : Subgroup G} (hp : p.Prime) (hPF : P ≤ h.D.F) (hPcard : Nat.card ↥P = p)
    (hObj : Work.GW2.Case2EightObj h.D p P A) : p ∣ Nat.card ↥h.D.K := by
  obtain ⟨hp', hPF', hPcard', hAle, hAcard, hAexp, hPAsub, huniq⟩ := hObj
  have hpF : p ∣ Nat.card ↥h.D.F := by rw [← hPcard]; exact Subgroup.card_dvd_of_le hPF
  obtain ⟨Fp, hFp_le, hFp_card, hFp_omega⟩ :=
    Work.CORE4.CyclicOmegaPrime h.D.F p h.F_cyclic hp hpF
  have hnotAF : ¬ A ≤ h.D.F := by
    intro hAF
    have hAle' : A ≤ Fp := fun a ha => (hFp_omega a (hAF ha)).mp (hAexp a ha)
    have hcard : Nat.card ↥A ≤ Nat.card ↥Fp :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hAle')
    rw [hFp_card, hAcard] at hcard
    have h2 : 2 ≤ p := hp.two_le
    nlinarith [hcard, h2]
  obtain ⟨a, haA, haF⟩ := Set.not_subset.mp hnotAF
  have hleN : h.D.F ≤ Subgroup.normalizer (h.D.K : Set G) :=
    Work.CORE4.F_le_normalizer_K_c4 I B h.D
  have haFK : a ∈ ((↑h.D.F : Set G) * (↑h.D.K : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right h.D.F h.D.K hleN]
    exact hAle haA
  obtain ⟨f, hf, k, hk, hfk⟩ := Set.mem_mul.mp haFK
  have hkne : k ≠ 1 := by
    intro hk1
    exact haF (by rw [← hfk, hk1, mul_one]; exact hf)
  have hpow : (f * k) ^ p = 1 := by rw [hfk]; exact hAexp a haA
  have hcomm : Commute f k := Work.CORE4.F_commute_K_c4 I B h.D h.pre f hf k hk
  have hkp : k ^ p = 1 := by
    rw [hcomm.mul_pow p] at hpow
    have hmem : k ^ p ∈ h.D.F ⊓ h.D.K :=
      ⟨by rw [eq_inv_of_mul_eq_one_right hpow]; exact h.D.F.inv_mem (h.D.F.pow_mem hf p),
       h.D.K.pow_mem hk p⟩
    rw [Work.CORE4.F_inf_K_eq_bot_c4 B h.D] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hord : orderOf k = p := by
    have hdvd : orderOf k ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hkp
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | hp'
    · exact absurd (orderOf_eq_one_iff.mp h1) hkne
    · exact hp'
  rw [← hord]
  exact Subgroup.orderOf_dvd_natCard h.D.K hk

/-- **`A = P ⊔ Kp`** with `Kp` the `p`-torsion of the cyclic `K`: `A` is contained in the
`p`-torsion `P ⊔ Kp` of `F ⊔ K`, and has the same order `p²`. -/
lemma exists_Kp_A_eq (I : Work.GW2.C4Inputs) {B : Work.GW2.BenderSetup G}
    (h : Work.GW2.Case2Ctx B) {p : ℕ} {P A : Subgroup G}
    (hp : p.Prime) (hPF : P ≤ h.D.F) (hPcard : Nat.card ↥P = p)
    (hObj : Work.GW2.Case2EightObj h.D p P A) :
    ∃ Kp : Subgroup G, Kp ≤ h.D.K ∧ Nat.card ↥Kp = p ∧
      (∀ x ∈ h.D.K, x ^ p = 1 ↔ x ∈ Kp) ∧ A = P ⊔ Kp := by
  have hpK : p ∣ Nat.card ↥h.D.K := p_dvd_K_of_eightObj I h hp hPF hPcard hObj
  obtain ⟨Kp, hKpK, hKpcard, hKpomega⟩ :=
    Work.CORE4.CyclicOmegaPrime h.D.K p h.pre.K_cyclic hp hpK
  obtain ⟨_, hPF', hPcard', hAle, hAcard, hAexp, hPAsub, huniq⟩ := hObj
  have hpF : p ∣ Nat.card ↥h.D.F := by rw [← hPcard]; exact Subgroup.card_dvd_of_le hPF
  obtain ⟨Fp, hFp_le, hFpcard, hFpomega⟩ :=
    Work.CORE4.CyclicOmegaPrime h.D.F p h.F_cyclic hp hpF
  have hPFp : P = Fp := by
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => (hFpomega x (hPF hx)).mp
      (Work.CORE4.pow_eq_one_of_card_eq hPcard' hx)) ?_
    rw [hPcard', hFpcard]
  have homega' : Work.CORE4.omega1 p (h.D.F ⊔ h.D.K) = Fp ⊔ Kp :=
    Work.CORE4.omega1_sup_eq_torsion (Work.CORE4.F_inf_K_eq_bot_c4 B h.D)
      (Work.CORE4.F_le_normalizer_K_c4 I B h.D)
      (fun f hf k hk => (Work.CORE4.F_commute_K_c4 I B h.D h.pre f hf k hk))
      hFp_le hKpK hFpomega hKpomega
  have homega : Work.CORE4.omega1 p (h.D.F ⊔ h.D.K) = P ⊔ Kp := by
    rw [homega', hPFp]
  have hAle' : A ≤ P ⊔ Kp := by
    intro a ha
    rw [← homega]
    exact Subgroup.subset_closure ⟨hAle ha, hAexp a ha⟩
  have hbot : P ⊓ Kp = ⊥ := by
    refine le_bot_iff.mp ?_
    calc P ⊓ Kp ≤ h.D.F ⊓ h.D.K := inf_le_inf hPF hKpK
      _ = ⊥ := Work.CORE4.F_inf_K_eq_bot_c4 B h.D
  have hPcentE : P ≤ Subgroup.centralizer (Work.GW2.layerIn h.D.M : Set G) :=
    hPF.trans (Work.GW2.Case2Pre.F_cent B h.D h.pre)
  have hKpE : Kp ≤ Work.GW2.layerIn h.D.M := hKpK.trans (Work.CORE4.K_le_layerIn B h)
  have hN : P ≤ Subgroup.normalizer (Kp : Set G) := by
    have hPcentKp : P ≤ Subgroup.centralizer (Kp : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subgroup.mem_centralizer_iff.mp (hPcentE hx) y (hKpE hy)
    exact hPcentKp.trans (Subgroup.centralizer_le_normalizer _)
  have hcard : Nat.card ↥(P ⊔ Kp) = p * p := by
    rw [Work.CORE4.card_sup_of_disjoint_normalizer hbot hN, hPcard', hKpcard]
  have hAeq : A = P ⊔ Kp := by
    refine Subgroup.eq_of_le_of_card_ge hAle' ?_
    rw [hcard, hAcard, pow_two]
  exact ⟨Kp, hKpK, hKpcard, hKpomega, hAeq⟩

/-- **The parity facts for the prime `p` of §4 (8):** `p` is odd, `p ≠ 2`, and `p` is not the
characteristic `nineP h` of the field of the layer (i.e. `p ∤ q`). -/
lemma p_parity_facts (I : Work.GW2.C4Inputs) {B : Work.GW2.BenderSetup G}
    (hbc : Work.GW2.BenderCtx G) (h : Work.GW2.Case2Ctx B) {p : ℕ} {P A : Subgroup G}
    (hp : p.Prime) (hPF : P ≤ h.D.F) (hPcard : Nat.card ↥P = p)
    (hObj : Work.GW2.Case2EightObj h.D p P A) :
    Odd p ∧ p ≠ 2 ∧ p ≠ Work.CORE4.nineP h := by
  have hpK : p ∣ Nat.card ↥h.D.K := p_dvd_K_of_eightObj I h hp hPF hPcard hObj
  have hpU : p ∣ Nat.card ↥B.U :=
    hpK.trans (Subgroup.card_dvd_of_le (Work.GW2.Case2Data.K_le_U B h.D))
  have hodd : Odd p := Odd.of_dvd_nat B.U_odd hpU
  refine ⟨hodd, ?_, ?_⟩
  · intro h2
    rw [h2] at hodd
    exact absurd hodd (by decide)
  · obtain ⟨k, k', hqodd, hq7, hkeven, hkodd, hdisj, hrel⟩ :=
      Work.CORE4.Case2ParityQOf G I hbc B h
    have hkK : k = Nat.card ↥h.D.K * Nat.card ↥B.S0 :=
      Work.CORE4.Case2KmulS0 G I hbc B h (Work.CORE4.qOf h) k k' hqodd hq7 hdisj hrel
    have hp_dvd_k : p ∣ k := by rw [hkK]; exact dvd_mul_of_dvd_left hpK _
    have hp_not_dvd_q : ¬ p ∣ Work.CORE4.qOf h := by
      intro hpq
      have h2k : p ∣ 2 * k := dvd_mul_of_dvd_right hp_dvd_k 2
      rcases hdisj with ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [h1] at h2k
        have hd : p ∣ Work.CORE4.qOf h + 1 - Work.CORE4.qOf h := Nat.dvd_sub h2k hpq
        rw [Nat.add_sub_cancel_left] at hd
        exact hp.not_dvd_one hd
      · rw [h1] at h2k
        have hd : p ∣ Work.CORE4.qOf h - (Work.CORE4.qOf h - 1) := Nat.dvd_sub hpq h2k
        have hone : Work.CORE4.qOf h - (Work.CORE4.qOf h - 1) = 1 := by omega
        rw [hone] at hd
        exact hp.not_dvd_one hd
    intro heq
    apply hp_not_dvd_q
    have hk0 : Work.CORE4.nineK h ≠ 0 := by
      intro h0
      have : Work.CORE4.qOf h = 1 := by rw [Work.CORE4.qOf, h0, pow_zero]
      omega
    rw [Work.CORE4.qOf, ← heq]
    exact dvd_pow_self p hk0

/-- **Uniqueness of the order-`p` subgroup of `C_E(Kp)`**: if `T ≤ E(M)` has order `p` and
commutes with `Kp`, then `T = Kp`.  Both are order-`p` subgroups of the cyclic group
`C_G(Kp) ⊓ E(M)`, a torus of `L₂(q)` (`L2TorusNormE`). -/
lemma eq_Kp_of_le_centralizer_Kp (I : Work.GW2.C4Inputs) {B : Work.GW2.BenderSetup G}
    (hbc : Work.GW2.BenderCtx G) (h : Work.GW2.Case2Ctx B) {p : ℕ}
    (hp : p.Prime) (hpparity : Odd p ∧ p ≠ 2 ∧ p ≠ Work.CORE4.nineP h)
    {Kp T : Subgroup G} (hKpK : Kp ≤ h.D.K) (hKpcard : Nat.card ↥Kp = p)
    (hT : T ≤ Work.GW2.layerIn h.D.M) (hTcard : Nat.card ↥T = p)
    (hcomm : T ≤ Subgroup.centralizer (Kp : Set G)) : T = Kp := by
  obtain ⟨hodd, hp2, hpF_ne⟩ := hpparity
  haveI : Fact p.Prime := ⟨hp⟩
  have hKpE : Kp ≤ Work.GW2.layerIn h.D.M := hKpK.trans (Work.CORE4.K_le_layerIn B h)
  have hcyc : IsCyclic ↥(Subgroup.centralizer (Kp : Set G) ⊓ Work.GW2.layerIn h.D.M) :=
    (Work.CORE4.L2TorusNormE I G hbc B h p Kp hp hp2 hpF_ne hKpE hKpcard).1
  haveI : IsCyclic ↥Kp := isCyclic_of_prime_card hKpcard
  have hKpcent : Kp ≤ Subgroup.centralizer (Kp : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hTle : T ≤ Subgroup.centralizer (Kp : Set G) ⊓ Work.GW2.layerIn h.D.M := le_inf hcomm hT
  have hKple : Kp ≤ Subgroup.centralizer (Kp : Set G) ⊓ Work.GW2.layerIn h.D.M :=
    le_inf hKpcent hKpE
  exact eq_of_le_of_card_eq_of_isCyclic_bcih hcyc hTle hKple (hTcard.trans hKpcard.symm)


/-- The image of a member of `𝓓` under the projection `π` commutes with `Kp`. -/
lemma proj_mem_centralizer_Kp_bcih {P E : Subgroup G} {Kp Z A : Subgroup G} {π : ↥(P ⊔ E) →* ↥E}
    (hproj : ∀ x : ↥(P ⊔ E), (x : G) * (((π x : ↥E) : G))⁻¹ ∈ P)
    (hZc : Z ≤ Subgroup.centralizer (A : Set G)) (hKpA : Kp ≤ A)
    (hPcentKp : P ≤ Subgroup.centralizer (Kp : Set G))
    {x : ↥(P ⊔ E)} (hxZ : (x : G) ∈ Z) :
    ((π x : ↥E) : G) ∈ Subgroup.centralizer (Kp : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  set Q : G := (x : G) * (((π x : ↥E) : G))⁻¹ with hQdef
  have hqP : Q ∈ P := by rw [hQdef]; exact hproj x
  have hxq : (x : G) = Q * (((π x : ↥E) : G)) := by rw [hQdef]; group
  have hxk : (x : G) * k = k * (x : G) :=
    (Subgroup.mem_centralizer_iff.mp (hZc hxZ) k (hKpA hk)).symm
  have hqk : Q * k = k * Q := (Subgroup.mem_centralizer_iff.mp (hPcentKp hqP) k hk).symm
  have step : Q * (((π x : ↥E) : G) * k) = Q * (k * (((π x : ↥E) : G))) := by
    calc Q * (((π x : ↥E) : G) * k) = (Q * (((π x : ↥E) : G))) * k := by group
      _ = (x : G) * k := by rw [← hxq]
      _ = k * (x : G) := hxk
      _ = k * (Q * (((π x : ↥E) : G))) := by rw [hxq]
      _ = (k * Q) * (((π x : ↥E) : G)) := by group
      _ = (Q * k) * (((π x : ↥E) : G)) := by rw [hqk]
      _ = Q * (k * (((π x : ↥E) : G))) := by group
  exact (mul_left_cancel step).symm

/-- Conjugating a centralizer statement: `X^g ≤ C_G(Y)` iff `X ≤ C_G(Y^{g⁻¹})`. -/
lemma conjSub_le_centralizer_iff_bcih (g : G) (X Y : Subgroup G) :
    Work.GW2.conjSub g X ≤ Subgroup.centralizer (Y : Set G) ↔
      X ≤ Subgroup.centralizer (Work.GW2.conjSub g⁻¹ Y : Set G) := by
  constructor
  · intro hh x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨y₀, hy₀, rfl⟩ := (Work.CORE4.ConjSub.mem_conjSub (g := g⁻¹) (K := Y)).mp hy
    have h1 : g * x * g⁻¹ ∈ Work.GW2.conjSub g X :=
      (Work.CORE4.ConjSub.mem_conjSub (g := g) (K := X)).mpr ⟨x, hx, rfl⟩
    have h2 : y₀ * (g * x * g⁻¹) = (g * x * g⁻¹) * y₀ :=
      Subgroup.mem_centralizer_iff.mp (hh h1) y₀ hy₀
    have hcong := congrArg (fun t => g⁻¹ * t * g⁻¹⁻¹) h2
    have h4 : g⁻¹ * (y₀ * (g * x * g⁻¹)) * g⁻¹⁻¹ = (g⁻¹ * y₀ * g⁻¹⁻¹) * x := by group
    have h5 : g⁻¹ * ((g * x * g⁻¹) * y₀) * g⁻¹⁻¹ = x * (g⁻¹ * y₀ * g⁻¹⁻¹) := by group
    rw [h4, h5] at hcong
    exact hcong
  · intro hh x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨x₀, hx₀, rfl⟩ := (Work.CORE4.ConjSub.mem_conjSub (g := g) (K := X)).mp hx
    have h1 : g⁻¹ * y * g⁻¹⁻¹ ∈ Work.GW2.conjSub g⁻¹ Y :=
      (Work.CORE4.ConjSub.mem_conjSub (g := g⁻¹) (K := Y)).mpr ⟨y, hy, rfl⟩
    have h2 : (g⁻¹ * y * g⁻¹⁻¹) * x₀ = x₀ * (g⁻¹ * y * g⁻¹⁻¹) :=
      Subgroup.mem_centralizer_iff.mp (hh hx₀) (g⁻¹ * y * g⁻¹⁻¹) h1
    have hcong := congrArg (fun t => g * t * g⁻¹) h2
    have h4 : g * ((g⁻¹ * y * g⁻¹⁻¹) * x₀) * g⁻¹ = y * (g * x₀ * g⁻¹) := by group
    have h5 : g * (x₀ * (g⁻¹ * y * g⁻¹⁻¹)) * g⁻¹ = (g * x₀ * g⁻¹) * y := by group
    rw [h4, h5] at hcong
    exact hcong

/-- **Bender 1981, §4, p. 227: the `(p₁ − 1)` half of the `Q ≠ 1` count.**

In Bender's own setting (`h' ∈ B.H = C_G(t)`, `X := conjSub h' P ≤ A`, `conjSub h' A = A`,
`X ≠ P`), the conjugates `Y` of `P` in the copy `𝓓^{h'} = conjSub h' '' 𝓓` that *centralize* `A`
are exactly the `p₁ − 1` conjugates of `P` inside `A` other than `X`; here `𝓓 = inConjSet P E(M)`
is the set of conjugates of `P` inside `W = P ⊔ E(M)` and `p₁ = Case2EightP1 P A`.

This is proved at the hypothesis level of `Work.CORE4.BadCountInH`: no use of §4 (7)/(8) beyond
`Case2EightObj`, none of `Case2EightAll`.  Route:

* `A = P ⊔ Kp` with `Kp` the `p`-torsion of the cyclic `K` (`exists_Kp_A_eq`, from
  `CyclicOmegaPrime` + `omega1_sup_eq_torsion`), so `A ≤ W = P ⊔ E(M)` and `A` is abelian;
* `Kp ↦ C_E(Kp)` has a *unique* subgroup of order `p`, namely `Kp`: `C_G(Kp) ⊓ E(M)` is cyclic
  (Bender's `l2torusNorm`, `Work.CORE4.L2TorusNormE`), and `p | |C_G(Kp) ⊓ E(M)|`;
* for `Z ∈ 𝓓` with `Z ≤ C_G(A)`: the `E(M)`-projection `πZ` (along the direct product
  `W = P × E(M)`, `Work.CORE4.ProjOfInfBot`) is an order-`p` subgroup of `C_E(Kp)` (as
  `z * (π z)⁻¹ ∈ P` commutes with `Kp`), hence `πZ = Kp`, and `Z ≤ P ⊔ πZ = P ⊔ Kp = A`
  (`Fibre9CardConj`, `Fibre9ImageCard`, `Fibre9SupProj`);
* conversely every conjugate of `P` inside `A` lies in `𝓓` and centralizes `A`, so the domain of
  the image decomposition is `{conjugates of P inside A} ∖ {P}`, of cardinality `p₁ − 1`. -/
theorem BadCountInH_first (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B)
        (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ h.D.F → Nat.card ↥P = p →
        Work.GW2.Case2EightObj h.D p P A →
        ∀ h' ∈ B.H, Work.GW2.conjSub h' P ≤ A → Work.GW2.conjSub h' P ≠ P →
          Work.GW2.conjSub h' A = A →
          {Y : Subgroup G |
              (∃ Z ∈ inConjSet P (Work.GW2.layerIn h.D.M), Y = Work.GW2.conjSub h' Z) ∧
                Y ≠ Work.GW2.conjSub h' P ∧
                Y ≤ Subgroup.centralizer (A : Set G)}.ncard ≤
            Work.GW2.Case2EightP1 P A - 1 := by
  intro G _ _ hbc B h p P A hp hPF hPcard hObj h' hh' hXA hXne hAfix
  classical
  set E : Subgroup G := Work.GW2.layerIn h.D.M with hE
  obtain ⟨Kp, hKpK, hKpcard, hKpomega, hAeq⟩ := exists_Kp_A_eq I h hp hPF hPcard hObj
  obtain ⟨hpodd, hp2, hpFne⟩ := p_parity_facts I hbc h hp hPF hPcard hObj
  have hKpA : Kp ≤ A := by rw [hAeq]; exact le_sup_right
  have hApe : A ≤ P ⊔ E := by
    rw [hAeq, hE]
    exact sup_le le_sup_left ((hKpK.trans (Work.CORE4.K_le_layerIn B h)).trans le_sup_right)
  -- `A^{h'⁻¹} = A`
  have hAfix' : Work.GW2.conjSub h'⁻¹ A = A := by
    have h1 : Work.GW2.conjSub h' (Work.GW2.conjSub h'⁻¹ A) = Work.GW2.conjSub h' A := by
      rw [← Work.CORE4.ConjSub.conjSub_mul, mul_inv_cancel, Work.CORE4.conjSub_one, hAfix]
    exact Work.CORE4.conjSub_injective h' h1
  -- `A` is commutative
  haveI : Fact p.Prime := ⟨hp⟩
  have hAcent : A ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr
      (IsPGroup.isMulCommutative_of_card_eq_prime_sq hObj.2.2.2.2.1)
  -- the projection `π : W = P ⊔ E(M) →* E(M)`
  have hPcomm : ∀ x ∈ P, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    rw [hE] at hy
    exact (Subgroup.mem_centralizer_iff.mp
      (Work.GW2.Case2Pre.F_cent B h.D h.pre (hPF hx)) y hy).symm
  have hcenterE : Subgroup.center ↥E = ⊥ := by
    obtain ⟨pF, kF, hpF, hpFodd, h7q, hφ, -⟩ := h.nine
    haveI : Fact pF.Prime := hpF
    obtain ⟨φ⟩ := hφ
    rw [hE]
    exact Work.CORE4.center_eq_bot_of_mulEquiv φ
      (Work.CORE4.center_PSL2_bot pF kF hpFodd (by omega))
  have hPEinf : P ⊓ E = ⊥ :=
    Work.CORE4.inf_eq_bot_of_le_centralizer
      (fun x hx => Subgroup.mem_centralizer_iff.mpr (fun y hy => (hPcomm x hx y hy).symm))
      hcenterE
  obtain ⟨π, hπ⟩ := Work.CORE4.ProjOfInfBot P E hPcomm hPEinf
  have hproj : ∀ x : ↥(P ⊔ E), (x : G) * (((π x : ↥E) : G))⁻¹ ∈ P :=
    Work.CORE4.proj_mul_inv_mem hPcomm π hπ
  -- `P` centralizes `Kp ≤ E`
  have hPcentKp : P ≤ Subgroup.centralizer (Kp : Set G) := by
    have hPcentE : P ≤ Subgroup.centralizer (Work.GW2.layerIn h.D.M : Set G) :=
      hPF.trans (Work.GW2.Case2Pre.F_cent B h.D h.pre)
    have hKpE : Kp ≤ Work.GW2.layerIn h.D.M := hKpK.trans (Work.CORE4.K_le_layerIn B h)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_iff.mp (hPcentE hx) y (hKpE hy)
  -- KEY: a member of `𝓓` centralizing `A` lies in `A`
  have key : ∀ Z : Subgroup G, Z ∈ inConjSet P E →
      Z ≤ Subgroup.centralizer (A : Set G) → Z ≤ A := by
    intro Z hZ hZc
    obtain ⟨hZle, hZconj⟩ := hZ
    by_cases hZP : Z = P
    · rw [hZP]; exact hObj.2.2.2.2.2.2.1
    · obtain ⟨hZcard, hZbot⟩ := Work.CORE4.Fibre9CardConj hp hPcard hZconj hZP
      set Yim : Subgroup G := Subgroup.map E.subtype ((Z.subgroupOf (P ⊔ E)).map π) with hYim
      have hYimcard : Nat.card ↥Yim = p := by
        rw [hYim, Work.CORE4.Fibre9ImageCard (P := P) (E := E) (X := Z) π hproj hZle hZbot,
          hZcard]
      have hYimE : Yim ≤ Work.GW2.layerIn h.D.M := by
        rw [hYim]; exact (Subgroup.map_subtype_le _).trans (le_of_eq hE)
      have hYimcent : Yim ≤ Subgroup.centralizer (Kp : Set G) := by
        rw [hYim]
        intro y hy
        rw [Subgroup.mem_map] at hy
        obtain ⟨e, he, rfl⟩ := hy
        rw [Subgroup.mem_map] at he
        obtain ⟨x, hx, hxval⟩ := he
        rw [Subgroup.mem_subgroupOf] at hx
        rw [← hxval]
        exact proj_mem_centralizer_Kp_bcih (P := P) (E := E) (Kp := Kp) (Z := Z) (A := A)
          hproj hZc hKpA hPcentKp hx
      have hYimKp : Yim = Kp :=
        eq_Kp_of_le_centralizer_Kp I hbc h hp ⟨hpodd, hp2, hpFne⟩ hKpK hKpcard hYimE hYimcard
          hYimcent
      calc Z ≤ P ⊔ Z := le_sup_right
        _ = P ⊔ Yim := Work.CORE4.Fibre9SupProj (P := P) (E := E) (Y := Z) π hproj hZle
        _ = P ⊔ Kp := by rw [hYimKp]
        _ = A := hAeq.symm
  -- the counted set is the image under `conjSub h'` of the centralizing members of `𝓓`
  have hset : {Y : Subgroup G |
        (∃ Z ∈ inConjSet P E, Y = Work.GW2.conjSub h' Z) ∧
          Y ≠ Work.GW2.conjSub h' P ∧ Y ≤ Subgroup.centralizer (A : Set G)}
      = Work.GW2.conjSub h' '' {Z : Subgroup G | Z ∈ inConjSet P E ∧ Z ≠ P ∧
          Z ≤ Subgroup.centralizer (A : Set G)} := by
    ext Y
    constructor
    · rintro ⟨⟨Z, hZ, rfl⟩, hYne, hYc⟩
      refine ⟨Z, ⟨hZ, fun hZP => hYne (by rw [hZP]), ?_⟩, rfl⟩
      have h2 := (conjSub_le_centralizer_iff_bcih h' Z A).mp hYc
      rwa [hAfix'] at h2
    · rintro ⟨Z, ⟨hZ, hZP, hZc⟩, rfl⟩
      refine ⟨⟨Z, hZ, rfl⟩, fun hYZ => hZP (Work.CORE4.conjSub_injective h' hYZ), ?_⟩
      have hmain : Work.GW2.conjSub h' Z ≤
          Subgroup.centralizer (Work.GW2.conjSub h' A : Set G) :=
        (conjSub_le_centralizer_iff_bcih h' Z (Work.GW2.conjSub h' A)).mpr (by
          rw [← Work.CORE4.ConjSub.conjSub_mul h'⁻¹ h' A, inv_mul_cancel,
            Work.CORE4.conjSub_one]
          exact hZc)
      rwa [hAfix] at hmain
  rw [hset]
  have himg : (Work.GW2.conjSub h' '' {Z : Subgroup G | Z ∈ inConjSet P E ∧ Z ≠ P ∧
        Z ≤ Subgroup.centralizer (A : Set G)}).ncard
      = {Z : Subgroup G | Z ∈ inConjSet P E ∧ Z ≠ P ∧
        Z ≤ Subgroup.centralizer (A : Set G)}.ncard :=
    Set.ncard_image_of_injective _ (Work.CORE4.conjSub_injective h')
  rw [himg]
  have hdom : {Z : Subgroup G | Z ∈ inConjSet P E ∧ Z ≠ P ∧
        Z ≤ Subgroup.centralizer (A : Set G)}
      = {X : Subgroup G | X ≤ A ∧ ∃ g : G, X = Work.GW2.conjSub g P} \ {P} := by
    ext Z
    constructor
    · rintro ⟨hZ, hZP, hZc⟩
      exact ⟨⟨key Z hZ hZc, hZ.2⟩, fun hZeq => hZP hZeq⟩
    · rintro ⟨⟨hZA, hZc⟩, hZP⟩
      exact ⟨⟨hZA.trans hApe, hZc⟩, hZP, hZA.trans hAcent⟩
  rw [hdom]
  have hPmem : P ∈ {X : Subgroup G | X ≤ A ∧ ∃ g : G, X = Work.GW2.conjSub g P} :=
    ⟨hObj.2.2.2.2.2.2.1, ⟨1, (Work.CORE4.conjSub_one P).symm⟩⟩
  have hsd := Set.ncard_sdiff (s := ({P} : Set (Subgroup G)))
    (t := {X : Subgroup G | X ≤ A ∧ ∃ g : G, X = Work.GW2.conjSub g P})
    (by intro x hx; rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hPmem)
  rw [hsd, Set.ncard_singleton]
  show {X : Subgroup G | X ≤ A ∧ ∃ g : G, X = Work.GW2.conjSub g P}.ncard - 1 ≤
    Work.GW2.Case2EightP1 P A - 1
  rfl


/-- **The two halves reassemble the target.**  This records the (immediate) assembly: the residual
`houtside` (Bender's p. 227 "`Q ≠ 1`" count for the members of the copy that do *not* centralize
`A`) together with the proved `Work.CORE4.BadCountInH_first` gives the target count, by the case
split on whether `Y` centralizes `A` (`Set.ncard_le_ncard` + `Set.ncard_union_le` + `add_le_add`).

The residual is *not* a consequence of the hypothesis list: see the diagnosis on
`Work.CORE4.BadCountInHOutside` (`Submission/Work/CORE4/BadCountInHOutside.lean`), whose prover
concluded that the count consumes fusion data of the pair `(E(M), E(M)^{h'})` that the hypotheses do
not supply (the identities `M^g ⊓ (P·E) = N_{P·E}(X) = P K S₀ = C_{P·E}(A)` and
`M ⊓ (X X^g E^g) = X K^g S₀ = C_{X X^g E^g}(A)`, and the normal complement `Q ⊴ N_D(X)` in
`D = C_{X X^g E^g}(Y)` with `|Q| ∣ q`), exactly as the area's own notes record for the sibling
residuals of the same count (`BadCountCtx`, `PerXInA`, `Case2CentBound9`, `Case2BadCount9`,
`Counting/BadSetBound9`, `Counting/PerXIntersectBound`). -/
theorem BadCountInH_of_badCountInHOutside (I : Work.GW2.C4Inputs)
    (houtside : ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B)
        (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ h.D.F → Nat.card ↥P = p →
        Work.GW2.Case2EightObj h.D p P A →
        ∀ h' ∈ B.H, Work.GW2.conjSub h' P ≤ A → Work.GW2.conjSub h' P ≠ P →
          Work.GW2.conjSub h' A = A →
          {Y : Subgroup G |
              (∃ Z ∈ inConjSet P (Work.GW2.layerIn h.D.M), Y = Work.GW2.conjSub h' Z) ∧
                Y ≠ Work.GW2.conjSub h' P ∧
                ¬ (Y ≤ Subgroup.centralizer (A : Set G)) ∧
                ∃ Z ∈ inConjSet P (Work.GW2.layerIn h.D.M),
                  Z ≠ Work.GW2.conjSub h' P ∧ Y ≤ Subgroup.centralizer (Z : Set G)}.ncard ≤
            ((qOf h - 1) * qOf h) / p) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B)
        (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ h.D.F → Nat.card ↥P = p →
        Work.GW2.Case2EightObj h.D p P A →
        ∀ h' ∈ B.H, Work.GW2.conjSub h' P ≤ A → Work.GW2.conjSub h' P ≠ P →
          Work.GW2.conjSub h' A = A →
          {Y : Subgroup G |
              (∃ Z ∈ inConjSet P (Work.GW2.layerIn h.D.M), Y = Work.GW2.conjSub h' Z) ∧
                Y ≠ Work.GW2.conjSub h' P ∧
                ∃ Z ∈ inConjSet P (Work.GW2.layerIn h.D.M),
                  Z ≠ Work.GW2.conjSub h' P ∧ Y ≤ Subgroup.centralizer (Z : Set G)}.ncard ≤
            (Work.GW2.Case2EightP1 P A - 1) + ((qOf h - 1) * qOf h) / p := by
  intro G _ _ hbc B h p P A hp hPF hPcard hObj h' hh' hXA hXne hAfix
  have hfirst := BadCountInH_first I G hbc B h p P A hp hPF hPcard hObj h' hh' hXA hXne hAfix
  have hsecond := houtside G hbc B h p P A hp hPF hPcard hObj h' hh' hXA hXne hAfix
  have hsub : {Y : Subgroup G |
        (∃ Z ∈ inConjSet P (Work.GW2.layerIn h.D.M), Y = Work.GW2.conjSub h' Z) ∧
          Y ≠ Work.GW2.conjSub h' P ∧
          ∃ Z ∈ inConjSet P (Work.GW2.layerIn h.D.M),
            Z ≠ Work.GW2.conjSub h' P ∧ Y ≤ Subgroup.centralizer (Z : Set G)}
      ⊆ {Y : Subgroup G |
          (∃ Z ∈ inConjSet P (Work.GW2.layerIn h.D.M), Y = Work.GW2.conjSub h' Z) ∧
            Y ≠ Work.GW2.conjSub h' P ∧ Y ≤ Subgroup.centralizer (A : Set G)} ∪
        {Y : Subgroup G |
          (∃ Z ∈ inConjSet P (Work.GW2.layerIn h.D.M), Y = Work.GW2.conjSub h' Z) ∧
            Y ≠ Work.GW2.conjSub h' P ∧ ¬ (Y ≤ Subgroup.centralizer (A : Set G)) ∧
            ∃ Z ∈ inConjSet P (Work.GW2.layerIn h.D.M),
              Z ≠ Work.GW2.conjSub h' P ∧ Y ≤ Subgroup.centralizer (Z : Set G)} := by
    intro Y hY
    by_cases hYA : Y ≤ Subgroup.centralizer (A : Set G)
    · exact Or.inl ⟨hY.1, hY.2.1, hYA⟩
    · exact Or.inr ⟨hY.1, hY.2.1, hYA, hY.2.2⟩
  calc {Y : Subgroup G |
        (∃ Z ∈ inConjSet P (Work.GW2.layerIn h.D.M), Y = Work.GW2.conjSub h' Z) ∧
          Y ≠ Work.GW2.conjSub h' P ∧
          ∃ Z ∈ inConjSet P (Work.GW2.layerIn h.D.M),
            Z ≠ Work.GW2.conjSub h' P ∧ Y ≤ Subgroup.centralizer (Z : Set G)}.ncard
      ≤ ({Y : Subgroup G |
          (∃ Z ∈ inConjSet P (Work.GW2.layerIn h.D.M), Y = Work.GW2.conjSub h' Z) ∧
            Y ≠ Work.GW2.conjSub h' P ∧ Y ≤ Subgroup.centralizer (A : Set G)} ∪
        {Y : Subgroup G |
          (∃ Z ∈ inConjSet P (Work.GW2.layerIn h.D.M), Y = Work.GW2.conjSub h' Z) ∧
            Y ≠ Work.GW2.conjSub h' P ∧ ¬ (Y ≤ Subgroup.centralizer (A : Set G)) ∧
            ∃ Z ∈ inConjSet P (Work.GW2.layerIn h.D.M),
              Z ≠ Work.GW2.conjSub h' P ∧ Y ≤ Subgroup.centralizer (Z : Set G)}).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ {Y : Subgroup G |
          (∃ Z ∈ inConjSet P (Work.GW2.layerIn h.D.M), Y = Work.GW2.conjSub h' Z) ∧
            Y ≠ Work.GW2.conjSub h' P ∧ Y ≤ Subgroup.centralizer (A : Set G)}.ncard +
        {Y : Subgroup G |
          (∃ Z ∈ inConjSet P (Work.GW2.layerIn h.D.M), Y = Work.GW2.conjSub h' Z) ∧
            Y ≠ Work.GW2.conjSub h' P ∧ ¬ (Y ≤ Subgroup.centralizer (A : Set G)) ∧
            ∃ Z ∈ inConjSet P (Work.GW2.layerIn h.D.M),
              Z ≠ Work.GW2.conjSub h' P ∧ Y ≤ Subgroup.centralizer (Z : Set G)}.ncard :=
        Set.ncard_union_le _ _
    _ ≤ (Work.GW2.Case2EightP1 P A - 1) + ((qOf h - 1) * qOf h) / p :=
        add_le_add hfirst hsecond

/-- **Bender 1981, §4, p. 227: the `Q ≠ 1` count in Bender's own setting.**

This is `Work.CORE4.BadCountCtxProp` (`Submission/Work/CORE4/BadCountAssembly.lean`) restricted to
the setting Bender actually works in: `h' ∈ B.H = C_G(t)` (his *"we can choose `g` subject to
`t^g = t`"*, supplied by the sibling leaf `Work.CORE4.Case2AmalgamSetup`), `P^{h'} = X ≤ A` and
`A^{h'} = A` (his *"Then `A^g = A`"*).

With `E := layerIn h.D.M`, `𝓓 := inConjSet P E = {X ≤ P ⊔ E : X ~ P}` of size
`(p₁ − 1) q k' + 1` (§4 (11), PROVED as `Counting.Count11Ctx`), and `𝓓^{h'} = conjSub h' '' 𝓓`, the
claim is

    #{Y ∈ 𝓓^{h'} : Y ≠ P^{h'} and ∃ Z ∈ 𝓓, Z ≠ P^{h'}, Y ≤ C_G(Z)} ≤ (p₁ − 1) + ((q − 1)/p) q,

i.e. Bender's *"not more than `((q − 1)/p)q` conjugates `Y` of `P` lying in `X × E^g` but not in
`M` … satisfy `Q ≠ 1`"*, plus the `(p₁ − 1)` members of `𝓓 ∩ 𝓓^{h'}` (which are automatically bad).

## STATUS (see `Work.CORE4.BadCountInH_first` and `BadCountInH_of_badCountInHOutside`)

The count splits by the case `Y ≤ C_G(A)` (equivalently `Y ≤ A`, equivalently `Y ⊆ M`):

* the `(p₁ − 1)` half is **PROVED** in this file (`BadCountInH_first`), at exactly this hypothesis
  level;
* the `((q − 1)/p) q` half — the members of the copy `𝓓^{h'}` that do *not* centralize `A` — is
  Bender's p. 227 "`Q ≠ 1`" count.  It is *not* derivable from this hypothesis list: Bender's proof
  of it works inside the amalgam `⟨E(M), E(M)^{h'}⟩` and uses the fusion data
  (`M^g ⊓ (P·E) = P K S₀ = C_{P·E}(A)`, `M ⊓ (X X^g E^g) = X K^g S₀ = C_{X X^g E^g}(A)`, and the
  normal complement `Q ⊴ N_D(X)` in `D = C_{X X^g E^g}(Y)` with `|Q| ∣ q`, `D` living in the
  *second* conjugate `X^g = P^{h'²}`), none of which is implied by the hypotheses; the area's
  sibling residuals of the same count and level — `BadCountCtx`, `Case2BadCount9`,
  `Case2CentBound9`, `Counting/BadSetBound9`, `Counting/PerXInA`,
  `Counting/PerXIntersectBound` — are still open or were declared under-hypothesised for exactly
  this reason.  The decomposition is recorded as `BadCountInH_of_badCountInHOutside`. -/
theorem BadCountInH (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B)
        (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ h.D.F → Nat.card ↥P = p →
        Work.GW2.Case2EightObj h.D p P A →
        ∀ h' ∈ B.H, Work.GW2.conjSub h' P ≤ A → Work.GW2.conjSub h' P ≠ P →
          Work.GW2.conjSub h' A = A →
          {Y : Subgroup G |
              (∃ Z ∈ inConjSet P (Work.GW2.layerIn h.D.M), Y = Work.GW2.conjSub h' Z) ∧
                Y ≠ Work.GW2.conjSub h' P ∧
                ∃ Z ∈ inConjSet P (Work.GW2.layerIn h.D.M),
                  Z ≠ Work.GW2.conjSub h' P ∧ Y ≤ Subgroup.centralizer (Z : Set G)}.ncard ≤
            (Work.GW2.Case2EightP1 P A - 1) + ((qOf h - 1) * qOf h) / p := by
  sorry

end Work.CORE4
