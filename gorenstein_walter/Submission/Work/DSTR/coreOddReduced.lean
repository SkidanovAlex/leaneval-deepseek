import Mathlib
import Submission.Work.DSTR.Defs
import Submission.Work.COPR.Coprime11i
import Submission.Work.DSTR.coreOddStep

/-!
# The reduced coprime core statement (Bender 1970 §2.4 / Bender 1981 1.10(i))

For a finite group `X`, a normal subgroup `K ⊴ X` of odd order, an involution `t ∈ X`, an odd prime
`p`, and a `p`-subgroup `P ≤ X` normalised by `C_X(t)` with `⁅P, ⟨t⟩⁆ ≤ K` and `O_p(K) = 1`, we
prove `⁅P, ⟨t⟩⁆ = ⊥`.  This is the reduced case of Bender 1981 1.10(i) (the case
`[P,t] ⊆ O(X)`, which is Bender 1970, 2.4), as used by `Work.DSTR.d110iOdd_of_coreOddReduced`.

## Structure of the proof

Write `R := ⁅P, ⟨t⟩⁆`.  The proof has two halves.

*Reduction to `R ⊆ K` in "normal form"* (`R = ⁅R, ⟨t⟩⁆`):

* `t ∈ C_X(t) ≤ N_X(P)` gives `t ∈ N_X(P)`, hence `R ≤ P` (`commutator_zpowers_le_of_mem`), so `R`
  is a `p`-group;
* conjugation by any element of `C_X(t)` preserves both `P` (by hypothesis) and `t`, hence preserves
  `R` (`centralizer_le_normalizer_commutator`);
* `R = ⁅R, ⟨t⟩⁆` (`commutator_zpowers_iterated`): Bender 1981 1.1(i) applied to the coprime action
  of the 2-group `⟨t⟩` on the odd group `P`, i.e. `Work.COPR.commutator_iterated_eq` with `p = 2`.

*The cross-characteristic core step* (Bender 1970, 2.4; Bender 1981 1.10(i)), proved in
`Submission/Work/DSTR/coreOddStep.lean` as `Work.DSTR.coreOddStep`: for a `p`-subgroup `P ≤ K`
(`p` odd) with `⁅P,⟨t⟩⁆ = P` and `C_X(t) ≤ N_X(P)`, one has `P ≤ O_p(K)`.  Applying it to `R`
(which satisfies `R ≤ K` by hypothesis) and using `O_p(K) = ⊥` gives `R = ⊥`.
-/

namespace Work.DSTR

open Subgroup
open scoped commutatorElement

/-- `t` normalises `P` as soon as the whole centraliser of `t` does. -/
private theorem mem_normalizer_of_centralizer_le {X : Type} [Group X] {t : X} {P : Subgroup X}
    (hN : Subgroup.centralizer ({t} : Set X) ≤ Subgroup.normalizer (P : Set X)) :
    t ∈ Subgroup.normalizer (P : Set X) :=
  hN (by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh])

/-- `⟨t⟩` normalises `P` as soon as `t` does. -/
private theorem zpowers_le_normalizer_of_mem {X : Type} [Group X] {t : X} {P : Subgroup X}
    (ht : t ∈ Subgroup.normalizer (P : Set X)) :
    Subgroup.zpowers t ≤ Subgroup.normalizer (P : Set X) :=
  Subgroup.zpowers_le.mpr ht

/-- **`⁅P, ⟨t⟩⁆ ≤ P`**: an element of `⟨t⟩` normalises `P`, so the commutator of `x ∈ P` with it
is `x · (y x⁻¹ y⁻¹)`, a product of two elements of `P`. -/
private theorem commutator_zpowers_le_of_mem {X : Type} [Group X] {t : X} {P : Subgroup X}
    (ht : t ∈ Subgroup.normalizer (P : Set X)) : ⁅P, Subgroup.zpowers t⁆ ≤ P := by
  have hzN : Subgroup.zpowers t ≤ Subgroup.normalizer (P : Set X) :=
    zpowers_le_normalizer_of_mem ht
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hyN : t ^ n ∈ Subgroup.normalizer (P : Set X) :=
    hzN (Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩)
  have hconj : t ^ n * x⁻¹ * (t ^ n)⁻¹ ∈ P :=
    (Subgroup.mem_normalizer_iff.mp hyN x⁻¹).mp (P.inv_mem hx)
  have hcomm : ⁅x, t ^ n⁆ = x * (t ^ n * x⁻¹ * (t ^ n)⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [hcomm]
  exact P.mul_mem hx hconj

/-- Conjugation by an element of `C_X(t)` preserves `⁅P, ⟨t⟩⁆`: it preserves `P` (hypothesis) and
fixes `t`, and conjugation commutes with the commutator construction
(`Subgroup.map_commutator`). -/
private theorem centralizer_le_normalizer_commutator {X : Type} [Group X] {t : X} {P : Subgroup X}
    (hN : Subgroup.centralizer ({t} : Set X) ≤ Subgroup.normalizer (P : Set X)) :
    Subgroup.centralizer ({t} : Set X) ≤
      Subgroup.normalizer ((⁅P, Subgroup.zpowers t⁆ : Subgroup X) : Set X) := by
  intro c hc
  set f : X →* X := (MulAut.conj c).toMonoidHom with hf
  have hf_apply : ∀ y : X, f y = c * y * c⁻¹ := fun y => MulAut.conj_apply c y
  have hf_inj : Function.Injective f := by
    intro a b hab
    exact (MulAut.conj c).injective hab
  have hcP : c ∈ Subgroup.normalizer (P : Set X) := hN hc
  have hcPinv : c⁻¹ ∈ Subgroup.normalizer (P : Set X) := Subgroup.inv_mem _ hcP
  have hct : f t = t := by
    have h1 : t * c = c * t := (Subgroup.mem_centralizer_iff.mp hc) t (by simp)
    rw [hf_apply, ← h1]
    group
  have hmapP : P.map f = P := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hf_apply]
      exact (Subgroup.mem_normalizer_iff.mp hcP y).mp hy
    · intro hx
      refine ⟨c⁻¹ * x * c, ?_, ?_⟩
      · simpa using (Subgroup.mem_normalizer_iff.mp hcPinv x).mp hx
      · rw [hf_apply]
        group
  have hmapT : (Subgroup.zpowers t).map f = Subgroup.zpowers t := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [map_zpow, hct]
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩
    · intro hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      refine ⟨t ^ n, Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩, ?_⟩
      rw [map_zpow, hct]
  have hmap : (⁅P, Subgroup.zpowers t⁆).map f = ⁅P, Subgroup.zpowers t⁆ := by
    rw [Subgroup.map_commutator, hmapP, hmapT]
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
  · intro hy
    have hfy : f y ∈ ⁅P, Subgroup.zpowers t⁆ := by rw [hf_apply]; exact hy
    rw [← hmap] at hfy
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hfy
    have hzy' : f z = f y := hzy
    have hzy'' : z = y := hf_inj hzy'
    rwa [hzy''] at hz

/-- **Bender 1981, 1.1(i) for the 2-group `⟨t⟩` acting on the odd group `P`:** if `⟨t⟩` normalises
the `p`-subgroup `P` then `⁅P, ⟨t⟩⁆ = ⁅⁅P, ⟨t⟩⁆, ⟨t⟩⁆`. -/
private theorem commutator_zpowers_iterated {X : Type} [Group X] [Finite X] {t : X}
    (ht : orderOf t = 2) {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) {P : Subgroup X} (hP : IsPGroup p P)
    (hzN : Subgroup.zpowers t ≤ Subgroup.normalizer (P : Set X)) :
    ⁅⁅P, Subgroup.zpowers t⁆, Subgroup.zpowers t⁆ = ⁅P, Subgroup.zpowers t⁆ := by
  have hcard : IsPGroup 2 ↥(Subgroup.zpowers t) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ht, pow_one]
  have hodd : Odd (Nat.card ↥P) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
    rw [hn]
    exact Odd.pow ((Fact.out : p.Prime).odd_of_ne_two hp)
  have hcop : Nat.Coprime 2 (Nat.card ↥P) := hodd.coprime_two_left
  exact Work.COPR.commutator_iterated_eq 2 (Subgroup.zpowers t) P hcard hcop hzN

/-- **The cross-characteristic core step in normal form**: a `p`-subgroup `P ≤ K` (`p` odd) with
`⁅P,⟨t⟩⁆ = P` and `C_X(t) ≤ N_X(P)` is trivial when `O_p(K) = 1`. -/
theorem coreOddStepNormalForm {X : Type} [Group X] [Finite X] {K : Subgroup X} [K.Normal]
    (hKodd : Odd (Nat.card K))
    {t : X} (ht : orderOf t = 2) {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {P : Subgroup X}
    (hP : IsPGroup p P) (hPK : P ≤ K)
    (hN : Subgroup.centralizer ({t} : Set X) ≤ Subgroup.normalizer (P : Set X))
    (hcomm : ⁅P, Subgroup.zpowers t⁆ = P)
    (hcore : Work.GW2.pCore p ↥K = ⊥) : P = ⊥ := by
  have hstep : P ≤ Work.GW2.pCoreIn p K := coreOddStep hKodd ht hp hP hPK hN hcomm
  have hbot : Work.GW2.pCoreIn p K = ⊥ := by
    rw [Work.GW2.pCoreIn, hcore, Subgroup.map_bot]
  exact le_bot_iff.mp (hbot ▸ hstep)

/-- **The reduced coprime core statement** (Bender 1970, 2.4; Bender 1981 1.10(i), the case
`[P,t] ⊆ O(X)`): `K ⊴ X` of odd order, `t` an involution, `P` an odd `p`-subgroup with
`C_X(t) ≤ N_X(P)` and `⁅P, ⟨t⟩⁆ ≤ K`, and `O_p(K) = 1`; then `⁅P, ⟨t⟩⁆ = ⊥`. -/
theorem coreOddReduced {X : Type} [Group X] [Finite X]
    {K : Subgroup X} [K.Normal] (hKodd : Odd (Nat.card K)) (hKsol : Group.IsSolvable ↥K)
    {t : X} (ht : orderOf t = 2) {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {P : Subgroup X}
    (hP : IsPGroup p P)
    (hN : Subgroup.centralizer ({t} : Set X) ≤ Subgroup.normalizer (P : Set X))
    (hO : ⁅P, Subgroup.zpowers t⁆ ≤ K) (hcore : Work.GW2.pCore p ↥K = ⊥) :
    ⁅P, Subgroup.zpowers t⁆ = ⊥ := by
  have htN : t ∈ Subgroup.normalizer (P : Set X) := mem_normalizer_of_centralizer_le hN
  set R : Subgroup X := ⁅P, Subgroup.zpowers t⁆ with hRdef
  -- `R` is a `p`-subgroup of `K` normalised by `C_X(t)` and satisfies `R = ⁅R, ⟨t⟩⁆`.
  have hRP : R ≤ P := hRdef ▸ commutator_zpowers_le_of_mem htN
  have hRpg : IsPGroup p R :=
    hP.of_injective (Subgroup.inclusion hRP) (Subgroup.inclusion_injective hRP)
  have hRN : Subgroup.centralizer ({t} : Set X) ≤ Subgroup.normalizer (R : Set X) :=
    hRdef ▸ centralizer_le_normalizer_commutator hN
  have hcommR : ⁅R, Subgroup.zpowers t⁆ = R := by
    rw [hRdef]
    exact commutator_zpowers_iterated ht hp hP (zpowers_le_normalizer_of_mem htN)
  -- the cross-characteristic core step in normal form
  have hRbot : R = ⊥ :=
    coreOddStepNormalForm hKodd ht hp hRpg (hRdef ▸ hO) hRN hcommR hcore
  rwa [hRdef] at hRbot

end Work.DSTR
