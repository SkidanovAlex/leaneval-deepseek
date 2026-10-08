import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Fitting`: the Fitting subgroup, `π`-cores and `p`-length

This module sets up the basic objects of area A2 of the Feit–Thompson project
(solvability of groups of odd order).

* `IsPiNat π n` — every prime divisor of `n` lies in the set of primes `π`;
* `piCore π G = O_π(G)` — the largest normal `π`-subgroup of `G`;
* `pCore p G = O_p(G)`, `pPrimeCore p G = O_{p'}(G)`, `pPrimePCore p G = O_{p',p}(G)`;
* `fitting G = F(G)` — the Fitting subgroup, the largest normal nilpotent subgroup;
* `sectionCentralizer H K hH = C_G(K/H)` — the centralizer of the section `K/H`;
* `IsMinimalNormal N`, `IsChiefFactor H K` — minimal normal subgroups, chief factors;
* `pCoreSeries p G n` — the upper `p`-series `1 ≤ O_{p'}(G) ≤ O_{p',p}(G) ≤ ...`;
* `IsPSolvable p G`, `pLength p G` — `p`-solvability and the `p`-length.

All groups of interest are finite.  Conventions of the project: π-sets are predicates
`π : ℕ → Prop`, and conjugation of subgroups is the pointwise action `MulAut.conj g • H`.
-/

noncomputable section

open Classical

namespace Work.Fitting

variable {G : Type*} [Group G]

/-! ## `π`-numbers -/

/-- `IsPiNat π n`: every prime divisor of `n` lies in `π`. -/
def IsPiNat (π : ℕ → Prop) (n : ℕ) : Prop := ∀ p, p.Prime → p ∣ n → π p

@[simp] theorem isPiNat_one (π : ℕ → Prop) : IsPiNat π 1 :=
  fun p hp h => absurd h hp.not_dvd_one

theorem IsPiNat.mono {π π' : ℕ → Prop} (h : ∀ p, π p → π' p) {n : ℕ} (hn : IsPiNat π n) :
    IsPiNat π' n := fun p hp hd => h p (hn p hp hd)

theorem isPiNat_of_dvd {π : ℕ → Prop} {m n : ℕ} (h : m ∣ n) (hn : IsPiNat π n) :
    IsPiNat π m := fun p hp hpm => hn p hp (hpm.trans h)

theorem IsPiNat.mul {π : ℕ → Prop} {m n : ℕ} (hm : IsPiNat π m) (hn : IsPiNat π n) :
    IsPiNat π (m * n) := fun p hp hd =>
  (hp.dvd_mul.mp hd).elim (hm p hp) (hn p hp)

theorem IsPiNat.pow {π : ℕ → Prop} {n : ℕ} (hn : IsPiNat π n) (k : ℕ) :
    IsPiNat π (n ^ k) := fun p hp hd => hn p hp (hp.dvd_of_dvd_pow hd)

/-- For a prime `p`, `IsPiNat (· = p) n` means that `n` is a power of `p`. -/
theorem isPiNat_prime_iff {p n : ℕ} (hp : p.Prime) :
    IsPiNat (fun q => q = p) n ↔ ∃ k, n = p ^ k := by
  constructor
  · intro h
    rcases eq_or_ne n 0 with rfl | hn
    · have h2 : (2 : ℕ) = p := h 2 Nat.prime_two (dvd_zero 2)
      have h3 : (3 : ℕ) = p := h 3 Nat.prime_three (dvd_zero 3)
      omega
    · exact ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hn fun hq hd => h _ hq hd⟩
  · rintro ⟨k, rfl⟩
    intro q hq hd
    exact (hp.eq_one_or_self_of_dvd q (hq.dvd_of_dvd_pow hd)).resolve_left hq.ne_one

/-- For a prime `p`, `IsPiNat (· = p)` on the order of a subgroup means that it is a `p`-group. -/
theorem isPiNat_prime_iff_isPGroup {p : ℕ} [Finite G] (hp : p.Prime) (N : Subgroup G) :
    IsPiNat (fun q => q = p) (Nat.card ↥N) ↔ IsPGroup p ↥N := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [isPiNat_prime_iff hp, IsPGroup.iff_card]

/-! ## `π`-cores -/

/-- The set of normal `π`-subgroups of `G`. -/
def piCoreSet (π : ℕ → Prop) (G : Type*) [Group G] : Set (Subgroup G) :=
  {N : Subgroup G | N.Normal ∧ IsPiNat π (Nat.card ↥N)}

/-- `O_π(G)`, the maximal normal `π`-subgroup of `G`. -/
def piCore (π : ℕ → Prop) (G : Type*) [Group G] : Subgroup G := sSup (piCoreSet π G)

theorem mem_piCoreSet {π : ℕ → Prop} {N : Subgroup G} :
    N ∈ piCoreSet π G ↔ N.Normal ∧ IsPiNat π (Nat.card ↥N) := Iff.rfl

/-- `sSup` of subgroups commutes with `Subgroup.map`. -/
theorem map_sSup {K : Type*} [Group K] (f : G →* K) (S : Set (Subgroup G)) :
    (sSup S).map f = sSup (Subgroup.map f '' S) := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun N hN => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup ⟨N, hN, rfl⟩
  · refine sSup_le ?_
    rintro _ ⟨M, hM, rfl⟩
    exact Subgroup.map_mono (le_sSup hM)

theorem mem_piCoreSet_map {π : ℕ → Prop} (φ : G ≃* G) {N : Subgroup G}
    (hN : N ∈ piCoreSet π G) : N.map φ.toMonoidHom ∈ piCoreSet π G := by
  obtain ⟨hn, hc⟩ := hN
  exact ⟨hn.map _ φ.surjective, by
    rw [Subgroup.card_map_of_injective φ.injective]
    exact hc⟩

theorem image_piCoreSet (π : ℕ → Prop) (φ : G ≃* G) :
    Subgroup.map φ.toMonoidHom '' piCoreSet π G = piCoreSet π G := by
  refine le_antisymm ?_ ?_
  · rintro N ⟨M, hM, rfl⟩
    exact mem_piCoreSet_map φ hM
  · intro N hN
    refine ⟨N.map φ.symm.toMonoidHom, mem_piCoreSet_map φ.symm hN, ?_⟩
    rw [Subgroup.map_map]
    have hcomp : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id G := by ext x; simp
    rw [hcomp, Subgroup.map_id]

theorem piCore_characteristic (π : ℕ → Prop) (G : Type*) [Group G] :
    (piCore π G).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  rw [piCore, map_sSup, image_piCoreSet]

instance piCore_characteristic_inst (π : ℕ → Prop) (G : Type*) [Group G] :
    (piCore π G).Characteristic := piCore_characteristic π G

/-- A normal `π`-subgroup is contained in the `π`-core. -/
theorem le_piCore {π : ℕ → Prop} {N : Subgroup G} (hN : N.Normal)
    (h : IsPiNat π (Nat.card ↥N)) : N ≤ piCore π G := le_sSup ⟨hN, h⟩

theorem piCore_mono {π π' : ℕ → Prop} (h : ∀ p, π p → π' p) : piCore π G ≤ piCore π' G :=
  sSup_le fun _ hN => le_piCore hN.1 (hN.2.mono h)

theorem piCore_le (π : ℕ → Prop) (G : Type*) [Group G] : piCore π G ≤ ⊤ := le_top

/-- `O_p(G)`, the maximal normal `p`-subgroup of `G`. -/
def pCore (p : ℕ) (G : Type*) [Group G] : Subgroup G := piCore (fun q => q = p) G

/-- `O_{p'}(G)`, the maximal normal `p'`-subgroup of `G`. -/
def pPrimeCore (p : ℕ) (G : Type*) [Group G] : Subgroup G := piCore (fun q => q ≠ p) G

instance pCore_characteristic (p : ℕ) (G : Type*) [Group G] : (pCore p G).Characteristic :=
  piCore_characteristic_inst (fun q => q = p) G

instance pPrimeCore_characteristic (p : ℕ) (G : Type*) [Group G] :
    (pPrimeCore p G).Characteristic := piCore_characteristic_inst (fun q => q ≠ p) G

/-- `O_{p',p}(G)`: the preimage in `G` of `O_p(G/O_{p'}(G))`. -/
def pPrimePCore (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  (piCore (fun q => q = p) (G ⧸ pPrimeCore p G)).comap (QuotientGroup.mk' (pPrimeCore p G))

instance pPrimePCore_normal (p : ℕ) (G : Type*) [Group G] : (pPrimePCore p G).Normal :=
  Subgroup.normal_comap _

theorem pPrimeCore_le_pPrimePCore (p : ℕ) (G : Type*) [Group G] :
    pPrimeCore p G ≤ pPrimePCore p G := by
  intro x hx
  have h1 : (QuotientGroup.mk' (pPrimeCore p G)) x = 1 :=
    (QuotientGroup.eq_one_iff x).mpr hx
  rw [pPrimePCore, Subgroup.mem_comap, h1]
  exact Subgroup.one_mem _

/-! ## The Fitting subgroup -/

/-- The set of normal nilpotent subgroups of `G`. -/
def fittingSet (G : Type*) [Group G] : Set (Subgroup G) :=
  {N : Subgroup G | N.Normal ∧ Group.IsNilpotent ↥N}

/-- `F(G)`, the Fitting subgroup of `G`: the maximal normal nilpotent subgroup. -/
def fitting (G : Type*) [Group G] : Subgroup G := sSup (fittingSet G)

theorem mem_fittingSet {N : Subgroup G} :
    N ∈ fittingSet G ↔ N.Normal ∧ Group.IsNilpotent ↥N := Iff.rfl

/-- A normal nilpotent subgroup is contained in the Fitting subgroup. -/
theorem le_fitting {N : Subgroup G} (hN : N.Normal) (h : Group.IsNilpotent ↥N) :
    N ≤ fitting G := le_sSup ⟨hN, h⟩

/-- The supremum of normal subgroups is normal. -/
theorem normal_sSup {S : Set (Subgroup G)} (h : ∀ N ∈ S, N.Normal) : (sSup S).Normal := by
  rw [Subgroup.normal_iff_map_conj_eq]
  intro g
  rw [map_sSup]
  refine le_antisymm ?_ ?_
  · refine sSup_le ?_
    rintro N ⟨M, hM, rfl⟩
    haveI := h M hM
    rw [Subgroup.Normal.map_conj_eq]
    exact le_sSup hM
  · refine sSup_le ?_
    intro M hM
    haveI := h M hM
    have hfix : Subgroup.map (MulAut.conj g).toMonoidHom M = M :=
      Subgroup.Normal.map_conj_eq M g
    rw [← hfix]
    exact le_sSup ⟨M, hM, rfl⟩

theorem mem_fittingSet_map (φ : G ≃* G) {N : Subgroup G} (hN : N ∈ fittingSet G) :
    N.map φ.toMonoidHom ∈ fittingSet G := by
  obtain ⟨hn, hnil⟩ := hN
  haveI := hnil
  exact ⟨hn.map _ φ.surjective,
    Group.nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective N φ.toMonoidHom φ.injective)⟩

theorem image_fittingSet (φ : G ≃* G) :
    Subgroup.map φ.toMonoidHom '' fittingSet G = fittingSet G := by
  refine le_antisymm ?_ ?_
  · rintro N ⟨M, hM, rfl⟩
    exact mem_fittingSet_map φ hM
  · intro N hN
    refine ⟨N.map φ.symm.toMonoidHom, mem_fittingSet_map φ.symm hN, ?_⟩
    rw [Subgroup.map_map]
    have hcomp : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id G := by ext x; simp
    rw [hcomp, Subgroup.map_id]

theorem fitting_characteristic (G : Type*) [Group G] : (fitting G).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  rw [fitting, map_sSup, image_fittingSet]

instance fitting_characteristic_inst (G : Type*) [Group G] : (fitting G).Characteristic :=
  fitting_characteristic G

/-! ## Centralizers of sections -/

/-- `C_G(K/H)`: the elements of `G` acting trivially on the section `K/H` (`H` normal).
It is the preimage in `G` of the centralizer of `K/H` in `G/H`. -/
def sectionCentralizer (H K : Subgroup G) [H.Normal] : Subgroup G :=
  (Subgroup.centralizer (K.map (QuotientGroup.mk' H))).comap (QuotientGroup.mk' H)

/-- The center of a subgroup `H`, viewed as a subgroup of the ambient group. -/
def subgroupCenter (H : Subgroup G) : Subgroup G := (Subgroup.center ↥H).map H.subtype

/-- `C_G(K/H)` is normal when `K` is normal. -/
theorem sectionCentralizer_normal {H K : Subgroup G} [H.Normal] [K.Normal] :
    (sectionCentralizer H K).Normal := Subgroup.normal_comap _

/-- Membership in `C_G(K/H)`: the element acts trivially on the section. -/
theorem mem_sectionCentralizer_iff {H K : Subgroup G} [H.Normal] {x : G} :
    x ∈ sectionCentralizer H K ↔ QuotientGroup.mk' H x ∈
      Subgroup.centralizer (K.map (QuotientGroup.mk' H)) := Iff.rfl

/-! ## Minimal normal subgroups and chief factors -/

/-- `N` is a minimal normal subgroup of `G`. -/
def IsMinimalNormal (N : Subgroup G) : Prop :=
  N.Normal ∧ N ≠ ⊥ ∧ ∀ M : Subgroup G, M.Normal → M ≤ N → M ≠ ⊥ → M = N

/-- `K/H` is a chief factor of `G`: both are normal and there is no normal subgroup
strictly between them. -/
def IsChiefFactor (H K : Subgroup G) : Prop :=
  H.Normal ∧ K.Normal ∧ H < K ∧
    ∀ M : Subgroup G, M.Normal → H ≤ M → M ≤ K → M = H ∨ M = K

/-- A chief series of `G`: a maximal chain `⊤ = G₀ > G₁ > ... > Gₙ = ⊥` of normal subgroups. -/
structure ChiefSeries (G : Type*) [Group G] where
  /-- length of the series -/
  n : ℕ
  /-- the members of the series -/
  G_ : Fin (n + 1) → Subgroup G
  top_eq : G_ 0 = ⊤
  bot_eq : G_ (Fin.last n) = ⊥
  normal : ∀ i, (G_ i).Normal
  lt_prev : ∀ i : Fin n, G_ i.succ < G_ i.castSucc
  minimal : ∀ (i : Fin n) (M : Subgroup G), M.Normal → G_ i.succ ≤ M → M ≤ G_ i.castSucc →
    M = G_ i.succ ∨ M = G_ i.castSucc

/-! ## The upper `p`-series, `p`-solvability and `p`-length -/

/-- Auxiliary subtype-valued upper `p`-series, carrying the proof of normality. -/
private def pCoreSeriesAux (p : ℕ) (G : Type*) [Group G] : ℕ → {N : Subgroup G // N.Normal}
  | 0 => ⟨⊥, Subgroup.normal_bot⟩
  | (n + 1) =>
      let prev := pCoreSeriesAux p G n
      letI : prev.1.Normal := prev.2
      ⟨(piCore (fun q => if Even n then q ≠ p else q = p) (G ⧸ prev.1)).comap
          (QuotientGroup.mk' prev.1),
        Subgroup.normal_comap _⟩

/-- The upper `p`-series of `G`: `1 ≤ O_{p'}(G) ≤ O_{p',p}(G) ≤ O_{p',p,p'}(G) ≤ ...`. -/
def pCoreSeries (p : ℕ) (G : Type*) [Group G] (n : ℕ) : Subgroup G := (pCoreSeriesAux p G n).1

instance pCoreSeries_normal (p : ℕ) (G : Type*) [Group G] (n : ℕ) :
    (pCoreSeries p G n).Normal := (pCoreSeriesAux p G n).2

theorem pCoreSeries_zero (p : ℕ) (G : Type*) [Group G] : pCoreSeries p G 0 = ⊥ := rfl

theorem pCoreSeries_succ (p : ℕ) (G : Type*) [Group G] (n : ℕ) :
    pCoreSeries p G (n + 1) =
      (piCore (fun q => if Even n then q ≠ p else q = p)
        (G ⧸ pCoreSeries p G n)).comap (QuotientGroup.mk' (pCoreSeries p G n)) := rfl

/-- `G` is `p`-solvable if its upper `p`-series reaches `G`. -/
class IsPSolvable (p : ℕ) (G : Type*) [Group G] : Prop where
  out : ∃ n : ℕ, pCoreSeries p G n = ⊤

theorem isPSolvable_iff {p : ℕ} {G : Type*} [Group G] :
    IsPSolvable p G ↔ ∃ n : ℕ, pCoreSeries p G n = ⊤ :=
  ⟨fun h => h.out, fun h => ⟨h⟩⟩

/-- The `p`-length of `G`: the number of `p`-factors in the upper `p`-series.
The value is `0` for groups that are not `p`-solvable; use `IsPSolvable` to exclude this. -/
def pLength (p : ℕ) (G : Type*) [Group G] : ℕ :=
  if h : IsPSolvable p G then Nat.find h.out / 2 else 0


end Work.Fitting
