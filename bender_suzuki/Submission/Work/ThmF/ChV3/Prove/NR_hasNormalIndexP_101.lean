import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.Prove.Step9Defs
import Submission.Work.ThmF.ChV3.Prove.S1_centralizerP_eq
import Submission.Work.ThmF.ChV3.Prove.S3_T_facts
import Submission.Work.ThmF.ChV3.Prove.Center_R1_101
import Submission.Work.ThmF.ChV3.Prove.G0_hasNormalIndexP_of_fixed_elementary

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.NR_hasNormalIndexP_101` — §3 step (12), the leaf (12g)

Peterfalvi II Ch. V §3, case (10-1), leaf **(12g)**: `N_G(R)` has a normal subgroup of index
`p = |P|`.

The design (`NOTES_LEAD_bs_pass16.md` §1) routes (12g) through the generic leaf **G0**
(`G0_hasNormalIndexP_of_fixed_elementary`): a fixed vector in an elementary abelian section gives
a quotient of order `p`.  In case (10-1) one has `m = 1`, `Σ = 1`, `|R| = p²`, `|R₁| = p³`,
`|N_G(R)| = p³(p − 1)` and `C_Q(P)` of order `p − 1`, and `N_G(R) = R₁ ⋊ C_Q(P)`; the input to
`G0` is taken with

* `S = R₁`, `C = C_Q(P)`, both inside `X = N_G(R)`;
* `N = T = Z(R₁)` — here `T` is the complement of `P` in `R` given by step (11), and the
  identification `Z(R₁) = T` is the leaf `Center_R1_101`;
* `x ∈ P^#`: it lies in `R₁`, is *not* in `T` (`T ⊓ P = ⊥`) and is fixed by `C_Q(P)` modulo `T`
  because `C_Q(P) ≤ C_G(P)` centralises `P`.

The hypotheses `G0` needs are then:

* `R₁ ◁ N_G(R)` (`hR1n`), `T = Z(R₁)` is characteristic in `R₁` (`Center_R1_101`), and
  `C_Q(P) ≤ C_G(P) ≤ N_G(R)`;
* `|R₁ ⊔ C_Q(P)| = p³(p−1) = |N_G(R)|`, so `R₁ ⊔ C_Q(P) = N_G(R)`: `R₁ ⊓ C_Q(P) = 1` because
  `R₁` is a `p`-group and `|C_Q(P)| = p − 1`;
* `R₁/T = R₁/Z(R₁)` is a group of order `p²`: it is commutative (so `[R₁, R₁] ≤ T`) and of
  exponent `p` (so `a^p ∈ T` for `a ∈ R₁`) — the exponent statement uses that `R₁` is
  non-abelian, hence `R₁/Z(R₁)` is not cyclic, together with the class-two power identity
  `pow_comm_of_commutator_central`.

Only `hFT`, `hC4`, the context `c`/`h15`/`h7`/`hpf`, step (11)'s output `h11` and the `R₁` data
`hRR1`, `hR1N`, `hR1c`, `hR1n` (together with `hm1` and `hsig`) are used; `hGp`, `hcb` and `hNR`
are not needed for this leaf.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint
open Pointwise

namespace Work.ThmF.ChV3.Prove

variable {G : Type} [Group G] [Finite G]

/-! ## Three elementary group-theoretic inputs -/

/-- In a group, if `[x,y] = x y x⁻¹ y⁻¹ = c` with `c` commuting with `x`, then `x^p` commutes
with `y` whenever `c^p = 1`.

Indeed `x y x⁻¹ = c y`, and since `c` commutes with `x` an immediate induction gives
`x^k y x^{-k} = c^k y`. -/
private lemma pow_comm_of_commutator_central {p : ℕ} {x y c : G}
    (hc : c * x = x * c) (hcp : c ^ p = 1) (h : x * y * x⁻¹ * y⁻¹ = c) :
    x ^ p * y = y * x ^ p := by
  have hxy : x * y * x⁻¹ = c * y := by rw [← h]; group
  have hcentral : ∀ k : ℕ, c ^ k * x = x * c ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc c ^ (k + 1) * x = c ^ k * (c * x) := by rw [pow_succ]; group
        _ = c ^ k * (x * c) := by rw [hc]
        _ = (c ^ k * x) * c := by group
        _ = (x * c ^ k) * c := by rw [ih]
        _ = x * (c ^ k * c) := by group
        _ = x * c ^ (k + 1) := by rw [pow_succ]
  have key : ∀ k : ℕ, x ^ k * y * (x⁻¹) ^ k = c ^ k * y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc x ^ (k + 1) * y * (x⁻¹) ^ (k + 1)
          = x * (x ^ k * y * (x⁻¹) ^ k) * x⁻¹ := by rw [pow_succ', pow_succ']; group
        _ = x * (c ^ k * y) * x⁻¹ := by rw [ih]
        _ = (x * c ^ k * x⁻¹) * (x * y * x⁻¹) := by group
        _ = c ^ k * (c * y) := by rw [← hcentral k, hxy]; group
        _ = c ^ (k + 1) * y := by rw [pow_succ]; group
  have hk := key p
  rw [hcp, one_mul] at hk
  have h2 := congrArg (fun z => z * x ^ p) hk
  simp only [mul_assoc] at h2
  have hinv : (x⁻¹) ^ p * x ^ p = 1 := by rw [inv_pow, inv_mul_cancel]
  rw [hinv, mul_one] at h2
  exact h2

/-- `A ⊓ C_G(A)`, the centre of `A` viewed as a subgroup of `G`, is the centre of the group
`↥A`. -/
private lemma center_subgroupOf_inf_centralizer (A : Subgroup G) :
    (A ⊓ Subgroup.centralizer (A : Set G)).subgroupOf A = Subgroup.center ↥A := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    Subgroup.mem_center_iff]
  constructor
  · rintro ⟨-, hx⟩ g
    exact Subtype.ext (hx (g : G) g.2)
  · intro hx
    exact ⟨x.2, fun y hy => congrArg (fun z : ↥A => (z : G)) (hx ⟨y, hy⟩)⟩

/-- An element of `N_G(A)` maps the centre of `A` into itself. -/
private lemma map_conj_inf_centralizer_le (A : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G)) :
    (A ⊓ Subgroup.centralizer (A : Set G)).map (MulAut.conj g).toMonoidHom
      ≤ A ⊓ Subgroup.centralizer (A : Set G) := by
  intro x hx
  rw [Subgroup.mem_map] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  rw [Subgroup.mem_inf] at hz ⊢
  refine ⟨?_, ?_⟩
  · show g * z * g⁻¹ ∈ A
    exact (Subgroup.mem_normalizer_iff.mp hg z).mp hz.1
  · rw [Subgroup.mem_centralizer_iff] at hz ⊢
    intro a ha
    have hga : g⁻¹ * a * g ∈ A :=
      (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * a * g)).mpr (by simpa [mul_assoc] using ha)
    have hcomm := hz.2 (g⁻¹ * a * g) hga
    calc a * (g * z * g⁻¹) = g * ((g⁻¹ * a * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * a * g)) * g⁻¹ := by rw [hcomm]
      _ = (g * z * g⁻¹) * a := by group

/-- Conjugation by an element of `N_G(A)` fixes the centre of `A`. -/
private lemma map_inf_centralizer_of_mem_normalizer (A : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G)) :
    (A ⊓ Subgroup.centralizer (A : Set G)).map (MulAut.conj g).toMonoidHom
      = A ⊓ Subgroup.centralizer (A : Set G) := by
  apply le_antisymm (map_conj_inf_centralizer_le A hg)
  have hg' : g⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normalizer (A : Set G)).inv_mem hg
  have h1 := map_conj_inf_centralizer_le A hg'
  have h2 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) h1
  rwa [Subgroup.map_map,
    show (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom = MonoidHom.id G from
      MonoidHom.ext fun z => by simp [MulAut.conj_apply, mul_assoc],
    Subgroup.map_id] at h2

/-- For subgroups `A`, `B` with `A ⊓ B = ⊥`, the product map `A × B → A ⊔ B` is injective, so
`|A| |B| ≤ |A ⊔ B|` (only the *set* product is used, so no normality is needed). -/
private lemma card_mul_le_card_sup_of_inf_eq_bot {A B : Subgroup G} (hbot : A ⊓ B = ⊥) :
    Nat.card ↥A * Nat.card ↥B ≤ Nat.card ↥(A ⊔ B) := by
  have hinj : Function.Injective (fun q : ↥A × ↥B =>
      (⟨(q.1 : G) * (q.2 : G),
        Subgroup.mul_mem (A ⊔ B) (Subgroup.mem_sup_left q.1.2)
          (Subgroup.mem_sup_right q.2.2)⟩ : ↥(A ⊔ B))) := by
    intro p q hpq
    have hval : (p.1 : G) * (p.2 : G) = (q.1 : G) * (q.2 : G) := by
      simpa using congrArg (fun z : ↥(A ⊔ B) => (z : G)) hpq
    have h1 : (p.1 : G)⁻¹ * (q.1 : G) = (p.2 : G) * (q.2 : G)⁻¹ := by
      have h2 : (p.2 : G) * (q.2 : G)⁻¹ = (p.1 : G)⁻¹ * (q.1 : G) := by
        calc (p.2 : G) * (q.2 : G)⁻¹
            = (p.1 : G)⁻¹ * ((p.1 : G) * (p.2 : G)) * (q.2 : G)⁻¹ := by group
          _ = (p.1 : G)⁻¹ * ((q.1 : G) * (q.2 : G)) * (q.2 : G)⁻¹ := by rw [hval]
          _ = (p.1 : G)⁻¹ * (q.1 : G) := by group
      exact h2.symm
    have hmem : (p.1 : G)⁻¹ * (q.1 : G) ∈ A ⊓ B :=
      ⟨A.mul_mem (A.inv_mem p.1.2) q.1.2,
        by rw [h1]; exact B.mul_mem p.2.2 (B.inv_mem q.2.2)⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have hp1 : (q.1 : G) = (p.1 : G) := by
      have := congrArg (fun z => (p.1 : G) * z) hmem
      simpa using this
    have hp2 : (p.2 : G) = (q.2 : G) := by
      have h2 : (p.2 : G) * (q.2 : G)⁻¹ = 1 := by rw [← h1, hmem]
      have := congrArg (fun z => z * (q.2 : G)) h2
      simpa [mul_assoc] using this
    exact Prod.ext (Subtype.ext hp1.symm) (Subtype.ext hp2)
  have := Nat.card_le_card_of_injective _ hinj
  simpa [Nat.card_prod] using this

/-! ## The leaf (12g) -/

theorem NR_hasNormalIndexP_101 {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (h7 : Work.ThmF.ChV3.Ker H Q P t = P) (hpf : Nat.card P = orderOf (s * t))
    {T : Subgroup G} (h11 : Work.ThmF.ChV3.Step11Out H Q t P h15.R T)
    (hm1 : h15.m = 1) (hsig : Work.ThmF.ChV3.Sig H t P = ⊥)
    (hGp : Work.ThmF.ChV3.pPart (Nat.card P) (Nat.card G) = Nat.card P ^ 3)
    (hcb : ∀ x ∈ Work.ThmF.ChV3.CQ Q P, x ≠ 1 → ∀ X : Subgroup G, IsPGroup (Nat.card P) X →
      X ≤ Subgroup.centralizer ({x} : Set G) → Nat.card X ≤ Nat.card P)
    (hNR : Nat.card ↥(Work.ThmF.ChV3.NG h15.R) = Nat.card P ^ 3 * (Nat.card P - 1))
    {R1 : Subgroup G} (hRR1 : h15.R ≤ R1) (hR1N : R1 ≤ Work.ThmF.ChV3.NG h15.R)
    (hR1c : Nat.card R1 = Nat.card P ^ 3) (hR1n : Work.ThmF.ChV3.NG h15.R ≤
      Work.ThmF.ChV3.NG R1) :
    Work.ThmF.HasNormalIndexP (Nat.card P) ↥(Work.ThmF.ChV3.NG h15.R) := by
  classical
  have hp : (Nat.card P).Prime := c.P_prime
  haveI : Fact (Nat.card P).Prime := ⟨hp⟩
  -- ## `p` is odd
  have hP_twoPoint : P ≤ twoPoint H t := c.P_le.trans inf_le_left
  have hp_dvd : Nat.card P ∣ Nat.card (twoPoint H t) := Subgroup.card_dvd_of_le hP_twoPoint
  have hodd_D : Odd (Nat.card (twoPoint H t)) := split_odd_card_twoPoint c.split
  have hp_ne_two : Nat.card P ≠ 2 := by
    intro h2
    rw [h2] at hp_dvd
    exact (Nat.not_even_iff_odd.mpr hodd_D) (even_iff_two_dvd.mpr hp_dvd)
  -- ## Basic cardinalities of `R`, `C_Q(P)`, `T`
  have hcardR : Nat.card h15.R = Nat.card P ^ 2 := by
    have h := h15.hcardR
    rw [h7, ← hpf, hm1, pow_one] at h
    rw [h, pow_two]
  have hcardCQ : Nat.card ↥(Work.ThmF.ChV3.CQ Q P) = Nat.card P - 1 := by
    have h := h15.hcq
    rw [← hpf, hm1, pow_one] at h
    omega
  have hndvd : ¬ Nat.card P ∣ Nat.card P - 1 := by
    have hpos : 0 < Nat.card P := hp.pos
    intro hdvd
    have h1 : Nat.card P ∣ Nat.card P - (Nat.card P - 1) :=
      Nat.dvd_sub (dvd_refl (Nat.card P)) hdvd
    have h2 : Nat.card P - (Nat.card P - 1) = 1 := by omega
    rw [h2] at h1
    exact hp.not_dvd_one h1
  have hTleR : T ≤ h15.R := by rw [← h11.TPR]; exact le_sup_left
  have hTleR1 : T ≤ R1 := hTleR.trans hRR1
  have hPleR : P ≤ h15.R := by rw [← h11.TPR]; exact le_sup_right
  have hPleR1 : P ≤ R1 := hPleR.trans hRR1
  -- ## the leaf `Center_R1_101`: the centre of `R₁` is `T`
  obtain ⟨hcenterR1, hcardT⟩ :=
    Center_R1_101 hFT hC4 c h15 h7 hpf h11 hm1 hsig hRR1 hR1N hR1n hR1c
  have hZc_eq_T : R1 ⊓ Subgroup.centralizer (R1 : Set G) = T := by
    have hsub : (R1 ⊓ Subgroup.centralizer (R1 : Set G)).subgroupOf R1 = T.subgroupOf R1 := by
      rw [center_subgroupOf_inf_centralizer]
      exact hcenterR1
    have h1 := congrArg (Subgroup.map R1.subtype) hsub
    rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr inf_le_left, inf_eq_left.mpr hTleR1] at h1
    exact h1
  -- ## `[R₁,R₁] ≤ T`: `R₁/T = R₁/Z(R₁)` has order `p²`, hence is commutative
  have hTnorm : (T.subgroupOf R1).Normal := by
    rw [← hcenterR1]
    refine Subgroup.Normal.mk (fun n hn g => ?_)
    rw [Subgroup.mem_center_iff]
    intro y
    have hny : y * n = n * y := Subgroup.mem_center_iff.mp hn y
    have hyg : (y * g) * n = n * (y * g) := Subgroup.mem_center_iff.mp hn (y * g)
    calc y * (g * n * g⁻¹) = (y * g) * n * g⁻¹ := by group
      _ = n * (y * g) * g⁻¹ := by rw [hyg]
      _ = n * y := by group
      _ = y * n := hny.symm
      _ = g * ((g⁻¹ * y) * n) := by group
      _ = g * (n * (g⁻¹ * y)) := by rw [Subgroup.mem_center_iff.mp hn (g⁻¹ * y)]
      _ = (g * n * g⁻¹) * y := by group
  have hquotcard : Nat.card (↥R1 ⧸ (T.subgroupOf R1)) = Nat.card P ^ 2 := by
    rw [← Subgroup.index_eq_card (T.subgroupOf R1)]
    have h := Subgroup.card_mul_index (T.subgroupOf R1)
    have hc : Nat.card ↥(T.subgroupOf R1) = Nat.card ↥T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTleR1).toEquiv
    rw [hc, hcardT, hR1c] at h
    exact Nat.eq_of_mul_eq_mul_left hp.pos (by rw [h]; ring)
  haveI := hTnorm
  have hcommQ : IsMulCommutative (↥R1 ⧸ (T.subgroupOf R1)) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := Nat.card P) hquotcard
  have hab : ∀ a ∈ R1, ∀ b ∈ R1, a * b * a⁻¹ * b⁻¹ ∈ T := by
    intro a ha b hb
    have hcomm := hcommQ.is_comm.comm
      ((QuotientGroup.mk' (T.subgroupOf R1)) (⟨a, ha⟩ : ↥R1))
      ((QuotientGroup.mk' (T.subgroupOf R1)) (⟨b, hb⟩ : ↥R1))
    have h1 : (QuotientGroup.mk' (T.subgroupOf R1))
        ((⟨a, ha⟩ : ↥R1) * ⟨b, hb⟩ * (⟨a, ha⟩ : ↥R1)⁻¹ * (⟨b, hb⟩ : ↥R1)⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hcomm]
      group
    have h2 : ((⟨a, ha⟩ : ↥R1) * ⟨b, hb⟩ * (⟨a, ha⟩ : ↥R1)⁻¹ * (⟨b, hb⟩ : ↥R1)⁻¹)
        ∈ T.subgroupOf R1 := (QuotientGroup.eq_one_iff _).mp h1
    rw [Subgroup.mem_subgroupOf] at h2
    simpa using h2
  -- ## `R₁^p ≤ T`: `R₁/T = R₁/Z(R₁)` has exponent `p` (it is not cyclic: `R₁` is non-abelian,
  -- since `R₁ ⊓ C_G(P) = R` from `Center_R1_101` would otherwise force `R₁ = R`)
  have hpow : ∀ a ∈ R1, a ^ Nat.card P ∈ T := by
    intro a ha
    rw [← hZc_eq_T]
    refine Subgroup.mem_inf.mpr ⟨R1.pow_mem ha (Nat.card P), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hcT : a * y * a⁻¹ * y⁻¹ ∈ T := hab a ha y hy
    -- `c^p = 1` for `c ∈ T`, `|T| = p`
    have hcp : (a * y * a⁻¹ * y⁻¹) ^ Nat.card P = 1 := by
      haveI : Fintype ↥T := Fintype.ofFinite ↥T
      have hord : orderOf (⟨a * y * a⁻¹ * y⁻¹, hcT⟩ : ↥T) ∣ Nat.card P := by
        rw [← hcardT]
        simpa [Nat.card_eq_fintype_card] using
          orderOf_dvd_card (x := (⟨a * y * a⁻¹ * y⁻¹, hcT⟩ : ↥T))
      have hx1 : (⟨a * y * a⁻¹ * y⁻¹, hcT⟩ : ↥T) ^ Nat.card P = 1 := by
        rcases (Nat.dvd_prime hp).mp hord with h | h
        · rw [orderOf_eq_one_iff.mp h, one_pow]
        · rw [← h, pow_orderOf_eq_one]
      simpa using congrArg (fun z : ↥T => (z : G)) hx1
    -- `c` commutes with `a`
    have hca : (a * y * a⁻¹ * y⁻¹) * a = a * (a * y * a⁻¹ * y⁻¹) := by
      have hcZ : a * y * a⁻¹ * y⁻¹ ∈ R1 ⊓ Subgroup.centralizer (R1 : Set G) := by
        rw [hZc_eq_T]; exact hcT
      exact ((Subgroup.mem_centralizer_iff.mp hcZ.2) a ha).symm
    exact (pow_comm_of_commutator_central (p := Nat.card P) hca hcp
      (rfl : a * y * a⁻¹ * y⁻¹ = a * y * a⁻¹ * y⁻¹)).symm
  -- ## `N_G(R)` normalises `T`
  have hCQ_le_NG : Work.ThmF.ChV3.CQ Q P ≤ Work.ThmF.ChV3.NG h15.R :=
    (inf_le_right : Work.ThmF.ChV3.CQ Q P ≤ Work.ThmF.ChV3.CG P).trans h15.hRn
  have hNn : Work.ThmF.ChV3.NG h15.R ≤ Work.ThmF.ChV3.NG T := by
    intro x hx
    have hx' : x ∈ Subgroup.normalizer (R1 : Set G) := hR1n hx
    have hmap := map_inf_centralizer_of_mem_normalizer R1 hx'
    rw [hZc_eq_T] at hmap
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      have : (MulAut.conj x) u ∈ T.map (MulAut.conj x).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
      rwa [hmap] at this
    · intro hu
      have hx'' : x⁻¹ ∈ Subgroup.normalizer (R1 : Set G) :=
        (Subgroup.normalizer (R1 : Set G)).inv_mem hx'
      have hmap' := map_inf_centralizer_of_mem_normalizer R1 hx''
      rw [hZc_eq_T] at hmap'
      have : (MulAut.conj x⁻¹) (x * u * x⁻¹) ∈ T.map (MulAut.conj x⁻¹).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨x * u * x⁻¹, hu, rfl⟩
      rw [hmap'] at this
      convert this using 1
      rw [MulAut.conj_apply]
      group
  -- ## `R₁ ⊔ C_Q(P) = N_G(R)`: both have cardinality `p³(p−1)`
  have hR1infCQ : R1 ⊓ Work.ThmF.ChV3.CQ Q P = ⊥ := by
    have hcop : (Nat.card ↥R1).Coprime (Nat.card ↥(Work.ThmF.ChV3.CQ Q P)) := by
      rw [hR1c, hcardCQ]
      exact (hp.coprime_iff_not_dvd.mpr hndvd).pow_left 3
    exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)
  have hSC : R1 ⊔ Work.ThmF.ChV3.CQ Q P = Work.ThmF.ChV3.NG h15.R := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hR1N hCQ_le_NG) ?_
    rw [hNR]
    have hle := card_mul_le_card_sup_of_inf_eq_bot (A := R1) (B := Work.ThmF.ChV3.CQ Q P) hR1infCQ
    rw [hR1c, hcardCQ] at hle
    exact hle
  -- ## an element of `P^#`, fixed by `C_Q(P)` modulo `T`
  have hPne_bot : P ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot P).mp (by simpa using hp.one_lt)
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne_bot
  have hxP : (x : G) ∈ P := x.2
  have hx1' : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hxS : (x : G) ∈ R1 := hPleR1 hxP
  have hxN : (x : G) ∉ T := by
    intro hxT
    have : (x : G) ∈ P ⊓ T := ⟨hxP, hxT⟩
    rw [inf_comm, h11.TP, Subgroup.mem_bot] at this
    exact hx1' this
  have hfix : ∀ y ∈ Work.ThmF.ChV3.CQ Q P, y * (x : G) * y⁻¹ * (x : G)⁻¹ ∈ T := by
    intro y hy
    have hyC : y ∈ Subgroup.centralizer (P : Set G) := (Subgroup.mem_inf.mp hy).2
    have hcomm : (x : G) * y = y * (x : G) := (Subgroup.mem_centralizer_iff.mp hyC) (x : G) hxP
    have h1 : y * (x : G) * y⁻¹ = (x : G) := by
      rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
    rw [h1]
    simpa using T.one_mem
  have hC : ¬ Nat.card P ∣ Nat.card ↥(Work.ThmF.ChV3.CQ Q P) := by
    rw [hcardCQ]
    exact hndvd
  -- ## the generic leaf `G0`
  exact G0_hasNormalIndexP_of_fixed_elementary (G := G) (p := Nat.card P) hp
    (X := Work.ThmF.ChV3.NG h15.R) (S := R1) (C := Work.ThmF.ChV3.CQ Q P) (N := T)
    hR1N hCQ_le_NG hSC hR1n hNn hTleR1 (IsPGroup.of_card (n := 3) hR1c) hC hab hpow
    hxS hxN hfix

end Work.ThmF.ChV3.Prove
