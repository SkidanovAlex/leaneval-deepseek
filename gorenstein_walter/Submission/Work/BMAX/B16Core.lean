/-
# BMAX — `Work.BMAX.B16Core`: the core of Bender 1970, 1.6

This file proves the "crux" singled out in `Bender16DGroup.lean`
(`Work.BMAX.Bender16Prop_of_crux`): under the pair hypotheses with both layers trivial and
`p ∈ π(F(A))`, the generalized Fitting subgroups of `A` and `B` are `p`-groups.

The proof follows the argument of Bender as presented in Kurzweil–Stellmacher,
*The Theory of Finite Groups*, Theorem 10.1.4 (Bender), specialised to the case in which both
`layerIn A = ⊥` and `layerIn B = ⊥` are already known (so that `F*(A) = F(A)`, `F*(B) = F(B)`
are nilpotent and no component analysis is needed).

## Structure

Write `P := O_p(A)`, `O_q := O_q(A)`, `X := ⁅B,P⁆`, `Y := ⁅X,P⁆` (and symmetrically for `B`).

* `π(F(A)) = π(F(B))` (`Work.BMAX.GWPiEq`, applied with the `BRel` relations witnessed by `⊥`),
  so a second prime `q ∈ π(F(A))`, `q ≠ p`, is also in `π(F(B))` and gives non-trivial
  `O_q(A)`, `O_q(B)`, `O_p(B)`.
* The Kurzweil–Stellmacher commutator bound `⁅Y, O_q(A)⁆ ≤ O_p(B)` (`b16c_comm_comm_pCoreIn`)
  forces `Y ≤ N(O_q(A))` (`b16c_le_normalizer_of_commutator_le`: in the direct product
  `O_q(A)·O_p(B)` the `q`-elements form a subgroup, so a `q`-element of it lying in the
  `p`-group `O_p(B)` is trivial), hence `Y ≤ A ⊓ B` by the primitivity of the coatom `A`
  (`b16c_normalizer_inf_eq`).
* Then `P ≤ O_p(B)` by the subnormal chain `P ⊴ Y·P ⊴ Y·P·X ⊴ B`
  (`b16c_le_pCoreIn_of_chain`), and symmetrically `O_p(B) ≤ O_p(A)`; so `O_p(A) = O_p(B)` is
  normal in `⟨A,B⟩ = ⊤` (`b16c_sup_eq_top`), contradicting the simplicity of `G`.

Hence `π(F(A)) = π(F(B)) = {p}` and both `F(A)`, `F(B)` are `p`-groups.
-/
import Mathlib
import Submission.Work.BMAX.Defs
import Submission.Work.BMAX.B16Aux
import Submission.Work.BMAX.FittingDedekindOfPCore
import Submission.Work.BMAX.Bender17i_dedekind_basic
import Submission.Work.BMAX.pCoreIn_eq_bot_iff_not_mem_primesOf
import Submission.Work.BMAX.GWPiEq
import Submission.OddOrder.Isaacs.Ch04_Commutators.Main.ThreeSubgroups
import Submission.Work.BMAX.pCoreIn_inf_pResidualIn_fittingIn_eq_bot
import Submission.Work.BMAX.le_normalizer_pCoreIn_zcenterIn_fittingIn

set_option linter.style.haveILetI false

open scoped commutatorElement

namespace Work.BMAX

open Subgroup

variable {G : Type} [Group G] [Finite G]

/-! ## 0. Elementary facts about a single subgroup -/

/-- `F*(K) = F(K)` when the layer of `K` is trivial. -/
theorem b16c_fstarIn_eq_fittingIn {K : Subgroup G} (hL : Work.GW2.layerIn K = ⊥) :
    Work.GW2.fstarIn K = Work.GW2.fittingIn K := by
  rw [Work.GW2.fstarIn_eq_sup K, hL, sup_bot_eq]

/-- The toolkit's `FStarProp`, transported to the ambient-group form `C_G(F*(K)) ∩ K ≤ F*(K)`
for a `D`-group `K`. -/
theorem b16c_centralizer_fstarIn_inf_le (T : Work.GW2.LocalToolkit) {K : Subgroup G}
    (hD : Work.GW2.DihOrCycSylow K) (hDG : Work.GW2.IsDGroup K) :
    Subgroup.centralizer (Work.GW2.fstarIn K : Set G) ⊓ K ≤ Work.GW2.fstarIn K := by
  intro x hx
  obtain ⟨hcen, hxK⟩ := Subgroup.mem_inf.mp hx
  have hMem : (⟨x, hxK⟩ : ↥K) ∈
      Subgroup.centralizer ((Work.GW2.fstar ↥K : Subgroup ↥K) : Set ↥K) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : (y : G) ∈ Work.GW2.fstarIn K := Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    have hcomm : (y : G) * x = x * (y : G) :=
      (Subgroup.mem_centralizer_iff.mp hcen) (y : G) hy'
    exact Subtype.ext (by simpa using hcomm)
  have h2 : (⟨x, hxK⟩ : ↥K) ∈ Work.GW2.fstar ↥K := T.fstar ↥K T.ft hD hDG hMem
  exact Subgroup.mem_map.mpr ⟨⟨x, hxK⟩, h2, rfl⟩

/-- `C_G(F(K)) ∩ K ≤ F(K)` for a `D`-group `K` with trivial layer. -/
theorem b16c_centralizer_fittingIn_inf_le (T : Work.GW2.LocalToolkit) {K : Subgroup G}
    (hD : Work.GW2.DihOrCycSylow K) (hDG : Work.GW2.IsDGroup K)
    (hL : Work.GW2.layerIn K = ⊥) :
    Subgroup.centralizer (Work.GW2.fittingIn K : Set G) ⊓ K ≤ Work.GW2.fittingIn K := by
  have h := b16c_centralizer_fstarIn_inf_le T hD hDG
  rw [b16c_fstarIn_eq_fittingIn hL] at h
  exact h

/-- The Fitting subgroup of `K`, pushed into `G`, is nilpotent. -/
theorem b16c_isNilpotent_fittingIn (K : Subgroup G) :
    Group.IsNilpotent ↥(Work.GW2.fittingIn K) := by
  have h := fittingIn_eq_fitting K
  rw [h]
  exact (Group.isNilpotent_congr
    (Subgroup.equivMapOfInjective (OddOrder.Isaacs.Ch01.fitting ↥K) K.subtype
      K.subtype_injective)).mp OddOrder.Isaacs.Ch01.fitting.isNilpotent

/-! ## 1. Coprime `p`-core and normalizer facts -/

/-- `O_p(K)` is a `p`-group. -/
theorem b16c_isPGroup_pCoreIn (p : ℕ) [Fact p.Prime] (K : Subgroup G) :
    IsPGroup p ↥(Work.GW2.pCoreIn p K) := by
  rw [pCoreIn_eq_opCore]
  exact IsPGroup.map (OddOrder.Isaacs.Ch01.opCore_isPGroup p ↥K) K.subtype

/-- A subgroup that is at the same time a `p`-group and a `q`-group, `p ≠ q`, is trivial. -/
theorem b16c_eq_bot_of_isPGroup_of_ne {H : Subgroup G} {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q) (hp : IsPGroup p ↥H) (hq : IsPGroup q ↥H) : H = ⊥ := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hq
  have heq : p ^ n = q ^ m := hn.symm.trans hm
  have hcop : (p ^ n).Coprime (q ^ m) :=
    ((Nat.coprime_primes (Fact.out) (Fact.out)).mpr hpq).pow n m
  have h1 : p ^ n = 1 := by
    have hc : (p ^ n).Coprime (p ^ n) := by rwa [← heq] at hcop
    exact (Nat.coprime_self (p ^ n)).mp hc
  exact Subgroup.card_eq_one.mp (by rw [hn, h1])

/-- Subgroups of coprime prime-power order that normalize each other commute. -/
theorem b16c_commutator_eq_bot_of_isPGroup_ne {P Q : Subgroup G} {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (hP : IsPGroup p ↥P) (hQ : IsPGroup q ↥Q)
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G)) (hQP : Q ≤ Subgroup.normalizer (P : Set G)) :
    ⁅P, Q⁆ = ⊥ := by
  have h1 : ⁅P, Q⁆ ≤ P :=
    (Subgroup.le_normalizer_iff_commutator_le_left (H := Q) (K := P)).mp hQP
  have h2 : ⁅P, Q⁆ ≤ Q :=
    (Subgroup.le_normalizer_iff_commutator_le_right (H := P) (K := Q)).mp hPQ
  exact b16c_eq_bot_of_isPGroup_of_ne hpq (hP.to_le h1) (hQ.to_le h2)

/-- The normalizer of a nontrivial normal subgroup of a coatomic subgroup of a simple group is
the coatom (the "primitivity" of a maximal subgroup). -/
theorem b16c_normalizer_eq_of_isCoatom (hG : IsSimpleGroup G) {A N : Subgroup G}
    (hA : IsCoatom A) (hNle : N ≤ A) (hNne : N ≠ ⊥)
    (hAN : A ≤ Subgroup.normalizer (N : Set G)) :
    Subgroup.normalizer (N : Set G) = A := by
  rcases lt_or_eq_of_le hAN with hlt | heq
  · have htop : Subgroup.normalizer (N : Set G) = ⊤ := hA.lt_iff.mp hlt
    have hNormal : N.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    haveI := hNormal
    rcases hG.eq_bot_or_eq_top_of_normal N with h | h
    · exact absurd h hNne
    · exact absurd (h ▸ hNle) (fun htop' => hA.ne_top (top_le_iff.mp htop'))
  · exact heq.symm

/-- `B`-version of the primitivity statement: `N_B(N) = A ⊓ B` for `1 ≠ N ⊴ A`. -/
theorem b16c_normalizer_inf_eq (hG : IsSimpleGroup G) {A B N : Subgroup G}
    (hA : IsCoatom A) (hNle : N ≤ A) (hNne : N ≠ ⊥)
    (hAN : A ≤ Subgroup.normalizer (N : Set G)) :
    Subgroup.normalizer (N : Set G) ⊓ B = A ⊓ B := by
  rw [b16c_normalizer_eq_of_isCoatom hG hA hNle hNne hAN]

/-- `F(K)` is the join of the `O_r(K)`, `r` prime. -/
theorem b16c_fittingIn_eq_iSup_pCoreIn (K : Subgroup G) :
    Work.GW2.fittingIn K = ⨆ r : Nat.Primes, Work.GW2.pCoreIn (r : ℕ) K := by
  rw [fittingIn_eq_fitting]
  rw [show OddOrder.Isaacs.Ch01.fitting ↥K
      = ⨆ r : Nat.Primes, OddOrder.Isaacs.Ch01.opCore (r : ℕ) ↥K from rfl]
  rw [Subgroup.map_iSup]
  refine iSup_congr fun r => ?_
  haveI : Fact ((r : ℕ).Prime) := ⟨r.2⟩
  exact (pCoreIn_eq_opCore (r : ℕ) K).symm

/-! ## 2. Transport lemmas -/

/-- A normal `p`-subgroup lies in the `p`-core, in the `normalizer` phrasing. -/
theorem b16c_le_pCoreIn_of_le_of_normal {X N : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hXN : X ≤ N) (hNX : N ≤ Subgroup.normalizer (X : Set G)) (hX : IsPGroup p ↥X) :
    X ≤ Work.GW2.pCoreIn p N := by
  haveI hnorm : (X.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXN).mpr hNX
  have hX' : IsPGroup p ↥(X.subgroupOf N) := IsPGroup.comap_subtype hX
  have hle : X.subgroupOf N ≤ Work.GW2.pCore p ↥N :=
    Work.BMAX.PiPart.le_pCore_of_normal_isPGroup hX'
  calc X = (X.subgroupOf N).map N.subtype := by
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hXN]
    _ ≤ (Work.GW2.pCore p ↥N).map N.subtype := Subgroup.map_mono hle
    _ = Work.GW2.pCoreIn p N := rfl

/-- Conjugation by an element of `B` fixes the ambient image of a characteristic subgroup of a
normal subgroup `N ⊴ B`. -/
theorem b16c_map_characteristic_le_normalizer {N B : Subgroup G} {K : Subgroup ↥N}
    (hK : K.Characteristic) (hNB : N ≤ B) (hBN : B ≤ Subgroup.normalizer (N : Set G)) :
    B ≤ Subgroup.normalizer (K.map N.subtype : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro b hb x hx
  have hb' : b ∈ Subgroup.normalizer (N : Set G) := hBN hb
  have hbi : b⁻¹ ∈ Subgroup.normalizer (N : Set G) := hBN (B.inv_mem hb)
  let φ : ↥N →* ↥N :=
    { toFun := fun y => ⟨b * (y : G) * b⁻¹, (Subgroup.mem_normalizer_iff.mp hb' (y : G)).mp y.2⟩
      map_one' := by ext; simp
      map_mul' := fun y z => by ext; simp only [Subgroup.coe_mul]; group }
  let φ' : ↥N →* ↥N :=
    { toFun := fun y => ⟨b⁻¹ * (y : G) * b,
        by simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp hbi (y : G)).mp y.2⟩
      map_one' := by ext; simp
      map_mul' := fun y z => by ext; simp only [Subgroup.coe_mul]; group }
  have hφφ' : ∀ y : ↥N, φ (φ' y) = y := fun y => by
    apply Subtype.ext
    show b * (b⁻¹ * (y : G) * b) * b⁻¹ = (y : G)
    group
  have hφ'φ : ∀ y : ↥N, φ' (φ y) = y := fun y => by
    apply Subtype.ext
    show b⁻¹ * (b * (y : G) * b⁻¹) * b = (y : G)
    group
  have hbij : Function.Bijective φ :=
    ⟨fun a c h => by rw [← hφ'φ a, h, hφ'φ c], fun y => ⟨φ' y, hφφ' y⟩⟩
  let ψ : ↥N ≃* ↥N := MulEquiv.ofBijective φ hbij
  have hfix : K.map ψ.toMonoidHom = K := (Subgroup.characteristic_iff_map_eq.mp hK) ψ
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  have hψy : ψ y ∈ K := hfix ▸ (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)
  refine Subgroup.mem_map.mpr ⟨ψ y, hψy, ?_⟩
  rw [← hyx]
  show ((ψ y : ↥N) : G) = b * (y : G) * b⁻¹
  rfl

/-- `O_p(N) ≤ O_p(B)` when `N ⊴ B`. -/
theorem b16c_pCoreIn_le_pCoreIn_of_le_normal {N B : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hNB : N ≤ B) (hBN : B ≤ Subgroup.normalizer (N : Set G)) :
    Work.GW2.pCoreIn p N ≤ Work.GW2.pCoreIn p B := by
  have hle : Work.GW2.pCoreIn p N ≤ B := (Subgroup.map_subtype_le _).trans hNB
  have hnorm : B ≤ Subgroup.normalizer (Work.GW2.pCoreIn p N : Set G) :=
    b16c_map_characteristic_le_normalizer
      (K := Work.GW2.pCore p ↥N)
      (Work.BMAX.PiPart.pCore_characteristic (M := ↥N) (p := p)) hNB hBN
  haveI : ((Work.GW2.pCoreIn p N).subgroupOf B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr hnorm
  have hpg : IsPGroup p ↥((Work.GW2.pCoreIn p N).subgroupOf B) :=
    IsPGroup.comap_subtype (b16c_isPGroup_pCoreIn p N)
  have hkey := Work.BMAX.PiPart.le_pCore_of_normal_isPGroup (M := ↥B) (p := p) hpg
  calc Work.GW2.pCoreIn p N = ((Work.GW2.pCoreIn p N).subgroupOf B).map B.subtype := by
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hle]
    _ ≤ (Work.GW2.pCore p ↥B).map B.subtype := Subgroup.map_mono hkey
    _ = Work.GW2.pCoreIn p B := rfl

/-- `⁅H, K⁆` computed inside `B` maps to `⁅H, K⁆` in `G`. -/
theorem b16c_map_commutator_subgroupOf {H K B : Subgroup G} (hH : H ≤ B) (hK : K ≤ B) :
    (⁅H.subgroupOf B, K.subgroupOf B⁆).map B.subtype = ⁅H, K⁆ := by
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr hH, inf_eq_left.mpr hK]

/-- The three-fold version of `b16c_map_commutator_subgroupOf`. -/
theorem b16c_map_commutator_subgroupOf3 {H₁ H₂ H₃ B : Subgroup G} (h₁ : H₁ ≤ B)
    (h₂ : H₂ ≤ B) (h₃ : H₃ ≤ B) :
    (⁅⁅H₁.subgroupOf B, H₂.subgroupOf B⁆, H₃.subgroupOf B⁆).map B.subtype = ⁅⁅H₁, H₂⁆, H₃⁆ := by
  rw [Subgroup.map_commutator, b16c_map_commutator_subgroupOf h₁ h₂,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr h₃]

/-! ## 3. Elementary commutator inclusions -/

/-- `A ⊔ B = ⊤` for two distinct coatomic subgroups. -/
theorem b16c_sup_eq_top {A B : Subgroup G} (hA : IsCoatom A) (hB : IsCoatom B) (hne : A ≠ B) :
    A ⊔ B = ⊤ := by
  rcases eq_or_lt_of_le (le_sup_left : A ≤ A ⊔ B) with h | h
  · exfalso
    have hBA : B ≤ A := le_trans le_sup_right (le_of_eq h.symm)
    exact hA.ne_top (hB.lt_iff.mp (lt_of_le_of_ne hBA (Ne.symm hne)))
  · exact hA.lt_iff.mp h

/-- `m * p * m⁻¹ = p * ⁅p⁻¹, m⁆`. -/
theorem b16c_conj_eq_mul_commutator (m p : G) : m * p * m⁻¹ = p * ⁅p⁻¹, m⁆ := by
  rw [commutatorElement_def]; group

/-- If `Subgroup.map (MulAut.conj m)` shrinks `S`, then `m` normalises `S` (an injective map
preserves the cardinality). -/
theorem b16c_mem_normalizer_of_map_conj_le {m : G} {S : Subgroup G}
    (h : Subgroup.map (MulAut.conj m : G →* G) S ≤ S) :
    m ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge h ?_
  rw [Subgroup.card_map_of_injective (K := S) (f := (MulAut.conj m : G →* G))
    (MulEquiv.injective (MulAut.conj m))]

/-- `H ≤ N(K)` from the `map`-form of invariance. -/
theorem b16c_le_normalizer_of_map_conj {H K : Subgroup G}
    (h : ∀ m ∈ H, Subgroup.map (MulAut.conj m : G →* G) K = K) :
    H ≤ Subgroup.normalizer (K : Set G) :=
  fun m hm => Subgroup.mem_normalizer_iff_map_conj_eq.mpr (h m hm)

/-- `H ≤ N(K)` from the `map`-form of shrinking. -/
theorem b16c_le_normalizer_of_map_conj_le {H K : Subgroup G}
    (h : ∀ m ∈ H, Subgroup.map (MulAut.conj m : G →* G) K ≤ K) :
    H ≤ Subgroup.normalizer (K : Set G) :=
  fun m hm => b16c_mem_normalizer_of_map_conj_le (h m hm)

/-- `P ≤ N(P)`. -/
theorem b16c_le_normalizer_self (P : Subgroup G) : P ≤ Subgroup.normalizer (P : Set G) :=
  Subgroup.le_normalizer_iff.mpr fun a ha b hb => P.mul_mem (P.mul_mem ha hb) (P.inv_mem ha)

/-- Decomposition of an element of a join `H ⊔ K` of two mutually normalizing subgroups:
every element of `H ⊔ K` is a product `a * b` with `a ∈ H`, `b ∈ K`. -/
theorem b16c_mem_sup_of_normalizer {H K : Subgroup G}
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hKH : K ≤ Subgroup.normalizer (H : Set G))
    {z : G} (hz : z ∈ H ⊔ K) : ∃ a ∈ H, ∃ b ∈ K, a * b = z := by
  let S : Subgroup G :=
    { carrier := {w : G | ∃ a ∈ H, ∃ b ∈ K, a * b = w}
      mul_mem' := fun {a b} ha hb => by
        obtain ⟨p, hp, q, hq, hpq⟩ := ha
        obtain ⟨c, hc, d, hd, hcd⟩ := hb
        refine ⟨p * (q * c * q⁻¹), H.mul_mem hp ?_, q * d, K.mul_mem hq hd, ?_⟩
        · exact (Subgroup.mem_normalizer_iff.mp (hKH hq) c).mp hc
        · rw [← hpq, ← hcd]; group
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
      inv_mem' := fun {x} hx => by
        obtain ⟨p, hp, q, hq, hpq⟩ := hx
        refine ⟨q⁻¹ * p⁻¹ * q, ?_, q⁻¹, K.inv_mem hq, ?_⟩
        · simpa only [inv_inv] using
            (Subgroup.mem_normalizer_iff.mp (hKH (K.inv_mem hq)) p⁻¹).mp (H.inv_mem hp)
        · rw [← hpq]; group }
  have hSle : H ⊔ K ≤ S := sup_le
    (fun a ha => ⟨a, ha, 1, K.one_mem, by simp⟩)
    (fun b hb => ⟨1, H.one_mem, b, hb, by simp⟩)
  exact hSle hz

/-- If `a^(q^i) = 1` then `a^(q^k) = 1` for all `k ≥ i`. -/
theorem b16c_pow_prime_le {a : G} {q i k : ℕ} (hik : i ≤ k) (h : a ^ q ^ i = 1) :
    a ^ q ^ k = 1 := by
  rw [show q ^ k = q ^ i * q ^ (k - i) from by rw [← pow_add, Nat.add_sub_of_le hik],
    pow_mul, h, one_pow]

/-- **The `O_q`-conclusion.**  Let `Q` be a `q`-group and `K` a `p`-group (`p ≠ q`) which
normalize each other, and let `Y` satisfy `⁅Y,Q⁆ ≤ K`.  Then `Y` normalizes `Q`.

Indeed `y·g·y⁻¹ = ⁅y,g⁆·g ∈ K ⊔ Q`, and `K`,`Q` commute, so writing `y·g·y⁻¹ = k·q₀` the
element `k = (y·g·y⁻¹)·q₀⁻¹` is a product of two commuting `q`-elements while lying in the
`p`-group `K`; hence `k = 1` and `y·g·y⁻¹ = q₀ ∈ Q`. -/
theorem b16c_le_normalizer_of_commutator_le {Q K Y : Subgroup G} {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q) (hQ : IsPGroup q ↥Q) (hK : IsPGroup p ↥K)
    (hQK : Q ≤ Subgroup.normalizer (K : Set G)) (hKQ : K ≤ Subgroup.normalizer (Q : Set G))
    (hcomm : ⁅Y, Q⁆ ≤ K) : Y ≤ Subgroup.normalizer (Q : Set G) := by
  have hKQbot : ⁅K, Q⁆ = ⊥ := b16c_commutator_eq_bot_of_isPGroup_ne hpq hK hQ hKQ hQK
  have hcommKQ : ∀ a ∈ K, ∀ b ∈ Q, Commute a b := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKQbot ha) b hb).symm
  rw [Subgroup.le_normalizer_iff]
  intro y hy g hg
  set v : G := y * g * y⁻¹ with hvdef
  have hvmem : v ∈ K ⊔ Q := by
    have h1 : v = ⁅y, g⁆ * g := by rw [hvdef, commutatorElement_def]; group
    rw [h1]
    exact Subgroup.mul_mem_sup (hcomm (Subgroup.commutator_mem_commutator hy hg)) hg
  obtain ⟨k, hk, q₀, hq₀, hkq⟩ := b16c_mem_sup_of_normalizer hKQ hQK hvmem
  obtain ⟨n, hn⟩ := isPGroup_iff_pow_pow_eq_one.mp hQ ⟨g, hg⟩
  have hnG : g ^ q ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hvpow : v ^ q ^ n = 1 := by
    have h3 : v = (MulAut.conj y) g := by rw [hvdef, MulAut.conj_apply]
    rw [h3]
    exact ((map_pow (MulAut.conj y : G →* G) g (q ^ n)).symm).trans (by rw [hnG, map_one])
  obtain ⟨m, hm⟩ := isPGroup_iff_pow_pow_eq_one.mp hQ ⟨q₀, hq₀⟩
  have hmG : q₀ ^ q ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hvq0 : Commute v q₀ := by
    have h1 : Commute k q₀ := hcommKQ k hk q₀ hq₀
    have h2 : v = q₀ * k := by rw [← hkq, h1.eq]
    rw [h2]
    exact ((Commute.refl q₀).mul_right h1.symm).symm
  obtain ⟨r, hr⟩ := isPGroup_iff_pow_pow_eq_one.mp hK ⟨k, hk⟩
  have hrG : k ^ p ^ r = 1 := by simpa using congrArg Subtype.val hr
  have hkpow : k ^ q ^ max n m = 1 := by
    have hkq' : k = v * q₀⁻¹ := by rw [← hkq]; group
    have hm' : (q₀⁻¹) ^ q ^ m = 1 := by rw [inv_pow, hmG, inv_one]
    rw [hkq', hvq0.inv_right.mul_pow,
      b16c_pow_prime_le (le_max_left n m) hvpow,
      b16c_pow_prime_le (le_max_right n m) hm', mul_one]
  have hk1 : k = 1 := by
    rw [← orderOf_eq_one_iff]
    exact Nat.eq_one_of_dvd_coprimes
      (Nat.coprime_pow_primes (max n m) r Fact.out Fact.out hpq.symm)
      (orderOf_dvd_of_pow_eq_one hkpow) (orderOf_dvd_of_pow_eq_one hrG)
  rw [← hkq, hk1, one_mul]
  exact hq₀

/-! ## 4. The subnormal chain `P ⊴ Y·P ⊴ Y·P·X ⊴ B` -/

/-- **The subnormal chain.**  Let `P` be a `p`-subgroup of `B`, put `X := ⁅B,P⁆` and
`Y := ⁅X,P⁆`, and suppose that `Y` normalises `P`.  Then `P ≤ O_p(B)`.

The chain is `P ⊴ Y·P ⊴ Y·P·X ⊴ B`, each step a `map (MulAut.conj ·)`-invariance: `X ◁ B`,
`Y ◁ X ⊔ P`, `m·P·m⁻¹ ≤ P·X` for `m ∈ B`, and `x·P·x⁻¹ ≤ Y·P` for `x ∈ X`. -/
theorem b16c_le_pCoreIn_of_chain {B P X Y : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hPB : P ≤ B) (hXB : X ≤ B) (hBX : B ≤ Subgroup.normalizer (X : Set G))
    (hXdef : X = ⁅B, P⁆) (hYdef : Y = ⁅X, P⁆)
    (hPY : Y ≤ Subgroup.normalizer (P : Set G)) (hP : IsPGroup p ↥P) :
    P ≤ Work.GW2.pCoreIn p B := by
  have hPBX : P ≤ Subgroup.normalizer (X : Set G) := hPB.trans hBX
  have hYB : Y ≤ B := by
    rw [hYdef]
    exact (Subgroup.commutator_le_sup X P).trans (sup_le hXB hPB)
  -- `Y` is normal in `X ⊔ P`
  have hYnorm : X ⊔ P ≤ Subgroup.normalizer (Y : Set G) := by
    rw [hYdef]
    exact sup_le (Subgroup.normalizer_commutator_ge_left X P)
      (Subgroup.normalizer_commutator_ge_right X P)
  -- `X ≤ N(Y ⊔ P)`
  have hXn : X ≤ Subgroup.normalizer (Y ⊔ P : Subgroup G) := by
    refine b16c_le_normalizer_of_map_conj_le fun x hx => ?_
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rw [Subgroup.mem_normalizer_iff_map_conj_eq.mp (hYnorm (Subgroup.mem_sup_left hx))]
      exact le_sup_left
    · intro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨q, hq, rfl⟩ := hy
      change x * q * x⁻¹ ∈ Y ⊔ P
      rw [b16c_conj_eq_mul_commutator, sup_comm]
      have h1 : ⁅q⁻¹, x⁆ ∈ Y := by
        rw [hYdef, ← Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator (P.inv_mem hq) hx
      exact Subgroup.mul_mem_sup hq h1
  -- `P ≤ N(Y ⊔ P)`
  have hPn : P ≤ Subgroup.normalizer (Y ⊔ P : Subgroup G) := by
    refine b16c_le_normalizer_of_map_conj fun q hq => ?_
    rw [Subgroup.map_sup]
    rw [Subgroup.mem_normalizer_iff_map_conj_eq.mp (hYnorm (Subgroup.mem_sup_right hq)),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (b16c_le_normalizer_self P hq)]
  -- `Y ≤ N(Y ⊔ P)`
  have hYn : Y ≤ Subgroup.normalizer (Y ⊔ P : Subgroup G) := by
    refine b16c_le_normalizer_of_map_conj fun q hq => ?_
    rw [Subgroup.map_sup]
    rw [Subgroup.mem_normalizer_iff_map_conj_eq.mp (b16c_le_normalizer_self Y hq),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPY hq)]
  -- `W := Y ⊔ P ⊔ X` is normal in `B`
  have hWn : Y ⊔ P ⊔ X ≤ Subgroup.normalizer ((Y ⊔ P : Subgroup G) : Set G) :=
    sup_le (sup_le hYn hPn) hXn
  have hBW : B ≤ Subgroup.normalizer ((Y ⊔ P ⊔ X : Subgroup G) : Set G) := by
    refine b16c_le_normalizer_of_map_conj_le fun m hm => ?_
    rw [Subgroup.map_sup, Subgroup.map_sup]
    refine sup_le (sup_le ?_ ?_) ?_
    · -- `map (conj m) Y ≤ Y ⊔ P ⊔ X`
      have hmapX : Subgroup.map (MulAut.conj m : G →* G) X = X :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hBX hm)
      have hYeq : Subgroup.map (MulAut.conj m : G →* G) Y
          = ⁅X, Subgroup.map (MulAut.conj m : G →* G) P⁆ := by
        rw [hYdef, Subgroup.map_commutator, hmapX]
      rw [hYeq]
      have hmono : ⁅X, Subgroup.map (MulAut.conj m : G →* G) P⁆ ≤ Y ⊔ X := by
        refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
        rw [Subgroup.mem_map] at hy
        obtain ⟨q, hq, rfl⟩ := hy
        change ⁅x, m * q * m⁻¹⁆ ∈ Y ⊔ X
        rw [b16c_conj_eq_mul_commutator, commutatorElement_mul_right_eq_mul_conj]
        have h1 : ⁅x, q⁆ ∈ Y := by
          rw [hYdef]; exact Subgroup.commutator_mem_commutator hx hq
        have h2 : q * ⁅x, ⁅q⁻¹, m⁆⁆ * q⁻¹ ∈ X := by
          have hx' : ⁅x, ⁅q⁻¹, m⁆⁆ ∈ X := by
            simpa using Subgroup.commutator_le_sup X X (Subgroup.commutator_mem_commutator hx
              (by rw [hXdef, ← Subgroup.commutator_comm]
                  exact Subgroup.commutator_mem_commutator (P.inv_mem hq) hm))
          exact (Subgroup.mem_normalizer_iff.mp (hPBX hq) ⁅x, ⁅q⁻¹, m⁆⁆).mp hx'
        have heq : ⁅x, q⁆ * q * ⁅x, ⁅q⁻¹, m⁆⁆ * q⁻¹
            = ⁅x, q⁆ * (q * ⁅x, ⁅q⁻¹, m⁆⁆ * q⁻¹) := by group
        rw [heq]
        exact Subgroup.mul_mem_sup h1 h2
      exact hmono.trans (sup_le (le_sup_of_le_left le_sup_left) le_sup_right)
    · -- `map (conj m) P ≤ Y ⊔ P ⊔ X`
      intro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨q, hq, rfl⟩ := hy
      change m * q * m⁻¹ ∈ Y ⊔ P ⊔ X
      rw [b16c_conj_eq_mul_commutator]
      have : ⁅q⁻¹, m⁆ ∈ X := by
        rw [hXdef, ← Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator (P.inv_mem hq) hm
      exact Subgroup.mul_mem_sup (Subgroup.mem_sup_right hq) this
    · -- `map (conj m) X ≤ Y ⊔ P ⊔ X`
      rw [Subgroup.mem_normalizer_iff_map_conj_eq.mp (hBX hm)]
      exact fun _ hx => Subgroup.mem_sup_right hx
  -- assemble the `pCore` inclusions
  have h1 : P ≤ Work.GW2.pCoreIn p (Y ⊔ P) :=
    b16c_le_pCoreIn_of_le_of_normal le_sup_right (sup_le hPY (b16c_le_normalizer_self P)) hP
  have h2 : Work.GW2.pCoreIn p (Y ⊔ P) ≤ Work.GW2.pCoreIn p (Y ⊔ P ⊔ X) :=
    b16c_pCoreIn_le_pCoreIn_of_le_normal le_sup_left hWn
  have h3 : Work.GW2.pCoreIn p (Y ⊔ P ⊔ X) ≤ Work.GW2.pCoreIn p B :=
    b16c_pCoreIn_le_pCoreIn_of_le_normal (sup_le (sup_le hYB hPB) hXB) hBW
  exact h1.trans (h2.trans h3)

/-! ## 5. The main step `O_p(M) ≤ O_p(N)` -/

/-- **The main step.**  Let `M ≠ N` be coatomic `D`-subgroups with trivial layers and
`F*(M) ≤ N`, `F*(N) ≤ M`, let `p ≠ q` be primes with `O_p(M)`, `O_q(M)`, `O_q(N)` all
non-trivial, and assume the Kurzweil–Stellmacher commutator bound
`⁅⁅⁅N,O_p(M)⁆,O_p(M)⁆, O_q(M)⁆ ≤ O_p(N)`.  Then `O_p(M) ≤ O_p(N)`:
the bound forces `Y := ⁅⁅N,O_p(M)⁆,O_p(M)⁆ ≤ N(O_q(M))`, hence `Y ≤ M ⊓ N` by the
primitivity of the coatom `M`, and then the subnormal chain
`O_p(M) ⊴ Y·O_p(M) ⊴ Y·O_p(M)⊔⁅N,O_p(M)⁆ ⊴ N` gives `O_p(M) ≤ O_p(N)`. -/
theorem b16c_step {M N : Subgroup G} (hG : IsSimpleGroup G)
    (hM : IsCoatom M) (hN : IsCoatom N) (hne : M ≠ N)
    (hDM : Work.GW2.DihOrCycSylow M) (hDGM : Work.GW2.IsDGroup M)
    (hDN : Work.GW2.DihOrCycSylow N) (hDGN : Work.GW2.IsDGroup N)
    (hMN : Work.GW2.fstarIn M ≤ N) (hNM : Work.GW2.fstarIn N ≤ M)
    (hLM : Work.GW2.layerIn M = ⊥) (hLN : Work.GW2.layerIn N = ⊥)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hMp : Work.GW2.pCoreIn p M ≠ ⊥) (hMq : Work.GW2.pCoreIn q M ≠ ⊥)
    (hNq : Work.GW2.pCoreIn q N ≠ ⊥)
    (hcore : ⁅⁅⁅N, Work.GW2.pCoreIn p M⁆, Work.GW2.pCoreIn p M⁆, Work.GW2.pCoreIn q M⁆
      ≤ Work.GW2.pCoreIn p N) :
    Work.GW2.pCoreIn p M ≤ Work.GW2.pCoreIn p N := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  set P : Subgroup G := Work.GW2.pCoreIn p M with hPdef
  set Q : Subgroup G := Work.GW2.pCoreIn q M with hQdef
  set P' : Subgroup G := Work.GW2.pCoreIn p N with hP'def
  set X : Subgroup G := ⁅N, P⁆ with hXdef
  set Y : Subgroup G := ⁅X, P⁆ with hYdef
  have hfit_le : ∀ K : Subgroup G, Work.GW2.fittingIn K ≤ K :=
    fun K => Subgroup.map_subtype_le (Work.GW2.fitting ↥K)
  have hfit_fstar : ∀ K : Subgroup G, Work.GW2.fittingIn K ≤ Work.GW2.fstarIn K :=
    fun K => by rw [Work.GW2.fstarIn_eq_sup]; exact le_sup_left
  have hPleM : P ≤ M := hPdef ▸ (Work.BMAX.pCoreIn_le_fittingIn M hp).trans (hfit_le M)
  have hQleM : Q ≤ M := hQdef ▸ (Work.BMAX.pCoreIn_le_fittingIn M hq).trans (hfit_le M)
  have hPleN : P ≤ N := (hPdef ▸ (Work.BMAX.pCoreIn_le_fittingIn M hp).trans (hfit_fstar M)).trans hMN
  have hQleN : Q ≤ N := (hQdef ▸ (Work.BMAX.pCoreIn_le_fittingIn M hq).trans (hfit_fstar M)).trans hMN
  have hP'leN : P' ≤ N := hP'def ▸ (Work.BMAX.pCoreIn_le_fittingIn N hp).trans (hfit_le N)
  have hP'leM : P' ≤ M :=
    (hP'def ▸ (Work.BMAX.pCoreIn_le_fittingIn N hp).trans (hfit_fstar N)).trans hNM
  have hpgP : IsPGroup p ↥P := hPdef ▸ b16c_isPGroup_pCoreIn p M
  have hpgP' : IsPGroup p ↥P' := hP'def ▸ b16c_isPGroup_pCoreIn p N
  have hpgQ : IsPGroup q ↥Q := hQdef ▸ b16c_isPGroup_pCoreIn q M
  have hQne : Q ≠ ⊥ := by rw [hQdef]; exact hMq
  -- the KS bound, in the abbreviations
  have hcore' : ⁅Y, Q⁆ ≤ P' := by
    rw [hYdef, hXdef, hQdef, hP'def]
    exact hcore
  -- `Y ≤ N(Q)`
  have hYleQ : Y ≤ Subgroup.normalizer (Q : Set G) :=
    b16c_le_normalizer_of_commutator_le hpq hpgQ hpgP' (hQleN.trans (le_normalizer_pCoreIn N p))
      (hP'leM.trans (le_normalizer_pCoreIn M q)) hcore'
  have hXleN : X ≤ N := by
    rw [hXdef]
    exact (Subgroup.commutator_le_sup N P).trans (sup_le le_rfl hPleN)
  have hBX : N ≤ Subgroup.normalizer (X : Set G) := by
    rw [hXdef]
    exact Subgroup.normalizer_commutator_ge_left N P
  have hYleN : Y ≤ N := by
    have h : ⁅X, P⁆ ≤ N := (Subgroup.commutator_le_sup X P).trans (sup_le hXleN hPleN)
    rwa [hYdef]
  -- hence `Y ≤ M ⊓ N = N(Q) ⊓ N`
  have hYleMN : Y ≤ M ⊓ N := by
    rw [← b16c_normalizer_inf_eq hG hM hQleM hQne (le_normalizer_pCoreIn M q)]
    exact fun x hx => ⟨hYleQ hx, hYleN hx⟩
  -- the subnormal chain
  have hPY : Y ≤ Subgroup.normalizer (P : Set G) :=
    (hYleMN.trans inf_le_left).trans (le_normalizer_pCoreIn M p)
  have hchain := b16c_le_pCoreIn_of_chain (B := N) (P := P) (X := X) (Y := Y)
    hPleN hXleN hBX hXdef hYdef hPY hpgP
  rw [hP'def]
  exact hchain

end Work.BMAX

namespace Work.BMAX

/-- The Kurzweil–Stellmacher commutator bound (proof supplied by the parallel prover of
`Submission/Work/BMAX/b16c_commutator_commutator_le_pCoreIn.lean`, reproduced here so that
this module stays self-contained). -/
theorem b16c_comm_comm_pCoreIn {G : Type} [Group G] [Finite G]
    (T : Work.GW2.LocalToolkit) (hG : IsSimpleGroup G) {M N : Subgroup G}
    (hDM : Work.GW2.DihOrCycSylow M) (hDGM : Work.GW2.IsDGroup M)
    (hDN : Work.GW2.DihOrCycSylow N) (hDGN : Work.GW2.IsDGroup N)
    (hMN : Work.GW2.fstarIn M ≤ N) (hNM : Work.GW2.fstarIn N ≤ M)
    (hLM : Work.GW2.layerIn M = ⊥) (hLN : Work.GW2.layerIn N = ⊥)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ⁅⁅⁅N, Work.GW2.pCoreIn p M⁆, Work.GW2.pCoreIn p M⁆, Work.GW2.pCoreIn q M⁆
      ≤ Work.GW2.pCoreIn p N := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  -- ## 0. Elementary containments and the normality of the two `p`-cores of `M`
  have hFM : Work.GW2.fstarIn M = Work.GW2.fittingIn M := b16c_fstarIn_eq_fittingIn hLM
  have hFN : Work.GW2.fstarIn N = Work.GW2.fittingIn N := b16c_fstarIn_eq_fittingIn hLN
  have hPleM : Work.GW2.pCoreIn p M ≤ M := Subgroup.map_subtype_le _
  have hQleM : Work.GW2.pCoreIn q M ≤ M := Subgroup.map_subtype_le _
  have hPleN : Work.GW2.pCoreIn p M ≤ N :=
    (pCoreIn_le_fittingIn M hp).trans ((le_of_eq hFM.symm).trans hMN)
  have hQleN : Work.GW2.pCoreIn q M ≤ N :=
    (pCoreIn_le_fittingIn M hq).trans ((le_of_eq hFM.symm).trans hMN)
  have hFleN : Work.GW2.fittingIn N ≤ N :=
    (le_of_eq hFN.symm).trans (Work.GW2.fstarIn_le_self N)
  have hFleM : Work.GW2.fittingIn N ≤ M := (le_of_eq hFN.symm).trans hNM
  have hMnormP : M ≤ Subgroup.normalizer ((Work.GW2.pCoreIn p M : Subgroup G) : Set G) :=
    le_normalizer_pCoreIn M p
  have hMnormQ : M ≤ Subgroup.normalizer ((Work.GW2.pCoreIn q M : Subgroup G) : Set G) :=
    le_normalizer_pCoreIn M q
  have hNnormF : N ≤ Subgroup.normalizer ((Work.GW2.fittingIn N : Subgroup G) : Set G) :=
    le_normalizer_fittingIn N
  -- `[O_p(M), O_q(M)] = 1`
  have hPQbot : ⁅Work.GW2.pCoreIn p M, Work.GW2.pCoreIn q M⁆ = ⊥ :=
    b16c_commutator_eq_bot_of_isPGroup_ne (P := Work.GW2.pCoreIn p M)
      (Q := Work.GW2.pCoreIn q M) (p := p) (q := q) hpq (b16c_isPGroup_pCoreIn p M)
      (b16c_isPGroup_pCoreIn q M) (hPleM.trans hMnormQ) (hQleM.trans hMnormP)
  have hPcenQ : Work.GW2.pCoreIn p M ≤
      Subgroup.centralizer ((Work.GW2.pCoreIn q M : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hPQbot
  -- the subgroup `X := ⁅N, O_p(M)⁆`
  have hXN : N ≤ Subgroup.normalizer ((⁅N, Work.GW2.pCoreIn p M⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_left N _
  have hXleN : ⁅N, Work.GW2.pCoreIn p M⁆ ≤ N :=
    (Subgroup.commutator_le_sup N (Work.GW2.pCoreIn p M)).trans (sup_le le_rfl hPleN)
  have hXQleX : ⁅⁅N, Work.GW2.pCoreIn p M⁆, Work.GW2.pCoreIn q M⁆ ≤
      ⁅N, Work.GW2.pCoreIn p M⁆ :=
    (Subgroup.le_normalizer_iff_commutator_le_left).mp (hQleN.trans hXN)
  have hXQleN : ⁅⁅N, Work.GW2.pCoreIn p M⁆, Work.GW2.pCoreIn q M⁆ ≤ N :=
    hXQleX.trans hXleN
  -- ## 1. `⁅N, O_p(M)⁆` commutes with `O_r(N)` for every prime `r ≠ p`
  have hkey1 : ∀ r : Nat.Primes, (r : ℕ) ≠ p → ⁅N, Work.GW2.pCoreIn p M⁆ ≤
      Subgroup.centralizer ((Work.GW2.pCoreIn (r : ℕ) N : Subgroup G) : Set G) := by
    intro r hr
    haveI : Fact (Nat.Prime (r : ℕ)) := ⟨r.2⟩
    -- `⁅P, O_r(N)⁆ = 1`
    have hPOr : ⁅Work.GW2.pCoreIn p M, Work.GW2.pCoreIn (r : ℕ) N⁆ = ⊥ :=
      b16c_commutator_eq_bot_of_isPGroup_ne (P := Work.GW2.pCoreIn p M)
        (Q := Work.GW2.pCoreIn (r : ℕ) N) (p := p) (q := (r : ℕ)) hr.symm
        (b16c_isPGroup_pCoreIn p M) (b16c_isPGroup_pCoreIn (r : ℕ) N)
        (hPleN.trans (le_normalizer_pCoreIn N (r : ℕ)))
        ((pCoreIn_le_fittingIn N r.2).trans (hFleM.trans hMnormP))
    -- `⁅O_r(N), N⁆ ≤ O_r(N)`
    have hOrN : ⁅Work.GW2.pCoreIn (r : ℕ) N, N⁆ ≤ Work.GW2.pCoreIn (r : ℕ) N :=
      (Subgroup.le_normalizer_iff_commutator_le_left (H := N)
        (K := Work.GW2.pCoreIn (r : ℕ) N)).mp (le_normalizer_pCoreIn N (r : ℕ))
    have hrot : ⁅⁅N, Work.GW2.pCoreIn p M⁆, Work.GW2.pCoreIn (r : ℕ) N⁆ = ⊥ :=
      Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := N)
        (H₂ := Work.GW2.pCoreIn p M) (H₃ := Work.GW2.pCoreIn (r : ℕ) N)
        (by rw [hPOr, Subgroup.commutator_bot_left])
        (by
          refine le_bot_iff.mp ?_
          calc ⁅⁅Work.GW2.pCoreIn (r : ℕ) N, N⁆, Work.GW2.pCoreIn p M⁆
              ≤ ⁅Work.GW2.pCoreIn (r : ℕ) N, Work.GW2.pCoreIn p M⁆ :=
                Subgroup.commutator_mono hOrN le_rfl
            _ = ⊥ := by rw [Subgroup.commutator_comm]; exact hPOr)
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hrot
  -- ## 2. `⁅⁅N, O_p(M)⁆, O_q(M)⁆` commutes with `O_r(N)` for every prime `r ≠ q`
  have hkey2 : ∀ r : Nat.Primes, (r : ℕ) ≠ q →
      ⁅⁅N, Work.GW2.pCoreIn p M⁆, Work.GW2.pCoreIn q M⁆ ≤
        Subgroup.centralizer ((Work.GW2.pCoreIn (r : ℕ) N : Subgroup G) : Set G) := by
    intro r hr
    haveI : Fact (Nat.Prime (r : ℕ)) := ⟨r.2⟩
    -- `⁅Q, O_r(N)⁆ = 1`
    have hQOr : ⁅Work.GW2.pCoreIn q M, Work.GW2.pCoreIn (r : ℕ) N⁆ = ⊥ :=
      b16c_commutator_eq_bot_of_isPGroup_ne (P := Work.GW2.pCoreIn q M)
        (Q := Work.GW2.pCoreIn (r : ℕ) N) (p := q) (q := (r : ℕ)) hr.symm
        (b16c_isPGroup_pCoreIn q M) (b16c_isPGroup_pCoreIn (r : ℕ) N)
        (hQleN.trans (le_normalizer_pCoreIn N (r : ℕ)))
        ((pCoreIn_le_fittingIn N r.2).trans (hFleM.trans hMnormQ))
    -- `⁅O_r(N), X⁆ ≤ O_r(N)`
    have hOrX : ⁅Work.GW2.pCoreIn (r : ℕ) N, ⁅N, Work.GW2.pCoreIn p M⁆⁆ ≤
        Work.GW2.pCoreIn (r : ℕ) N :=
      (Subgroup.le_normalizer_iff_commutator_le_left (H := ⁅N, Work.GW2.pCoreIn p M⁆)
        (K := Work.GW2.pCoreIn (r : ℕ) N)).mp (hXleN.trans (le_normalizer_pCoreIn N (r : ℕ)))
    have hrot : ⁅⁅⁅N, Work.GW2.pCoreIn p M⁆, Work.GW2.pCoreIn q M⁆,
        Work.GW2.pCoreIn (r : ℕ) N⁆ = ⊥ :=
      Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := ⁅N, Work.GW2.pCoreIn p M⁆)
        (H₂ := Work.GW2.pCoreIn q M) (H₃ := Work.GW2.pCoreIn (r : ℕ) N)
        (by rw [hQOr, Subgroup.commutator_bot_left])
        (by
          refine le_bot_iff.mp ?_
          calc ⁅⁅Work.GW2.pCoreIn (r : ℕ) N, ⁅N, Work.GW2.pCoreIn p M⁆⁆,
                Work.GW2.pCoreIn q M⁆
              ≤ ⁅Work.GW2.pCoreIn (r : ℕ) N, Work.GW2.pCoreIn q M⁆ :=
                Subgroup.commutator_mono hOrX le_rfl
            _ = ⊥ := by rw [Subgroup.commutator_comm]; exact hQOr)
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hrot
  -- ## 3. `⁅X, Q⁆ ≤ F(N)`
  have hXQcen : ⁅⁅N, Work.GW2.pCoreIn p M⁆, Work.GW2.pCoreIn q M⁆ ≤
      Subgroup.centralizer ((Work.GW2.fittingIn N : Subgroup G) : Set G) := by
    have hFle : Work.GW2.fittingIn N ≤
        Subgroup.centralizer ((⁅⁅N, Work.GW2.pCoreIn p M⁆, Work.GW2.pCoreIn q M⁆ :
          Subgroup G) : Set G) := by
      rw [b16c_fittingIn_eq_iSup_pCoreIn N]
      refine iSup_le fun r => ?_
      have hle : ⁅⁅N, Work.GW2.pCoreIn p M⁆, Work.GW2.pCoreIn q M⁆ ≤
          Subgroup.centralizer ((Work.GW2.pCoreIn (r : ℕ) N : Subgroup G) : Set G) := by
        by_cases hrp : (r : ℕ) = p
        · have hrq : (r : ℕ) ≠ q := by rw [hrp]; exact hpq
          exact hkey2 r hrq
        · exact hXQleX.trans (hkey1 r hrp)
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer
        (H₁ := Work.GW2.pCoreIn (r : ℕ) N)
        (H₂ := ⁅⁅N, Work.GW2.pCoreIn p M⁆, Work.GW2.pCoreIn q M⁆)).mp
        ((Subgroup.commutator_comm _ _).trans
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle))
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer
      (H₁ := ⁅⁅N, Work.GW2.pCoreIn p M⁆, Work.GW2.pCoreIn q M⁆)
      (H₂ := Work.GW2.fittingIn N)).mp
      ((Subgroup.commutator_comm _ _).trans
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hFle))
  have hXQleF : ⁅⁅N, Work.GW2.pCoreIn p M⁆, Work.GW2.pCoreIn q M⁆ ≤
      Work.GW2.fittingIn N :=
    (le_inf hXQcen hXQleN).trans (b16c_centralizer_fittingIn_inf_le T hDN hDGN hLN)
  -- ## 4. `⁅X, Q, P⁆ ≤ O_p(N)`
  have hXQP : ⁅⁅⁅N, Work.GW2.pCoreIn p M⁆, Work.GW2.pCoreIn q M⁆, Work.GW2.pCoreIn p M⁆
      ≤ Work.GW2.pCoreIn p N := by
    refine (Subgroup.commutator_mono hXQleF le_rfl).trans ?_
    have h1 : ⁅Work.GW2.fittingIn N, Work.GW2.pCoreIn p M⁆ ≤ Work.GW2.fittingIn N :=
      (Subgroup.le_normalizer_iff_commutator_le_left (H := Work.GW2.pCoreIn p M)
        (K := Work.GW2.fittingIn N)).mp (hPleN.trans hNnormF)
    have h2 : ⁅Work.GW2.fittingIn N, Work.GW2.pCoreIn p M⁆ ≤ Work.GW2.pCoreIn p M :=
      (Subgroup.le_normalizer_iff_commutator_le_right (H := Work.GW2.fittingIn N)
        (K := Work.GW2.pCoreIn p M)).mp (hFleM.trans hMnormP)
    have h3 : Work.GW2.fittingIn N ⊓ Work.GW2.pCoreIn p M ≤
        Work.GW2.pCoreIn p (Work.GW2.fittingIn N) := by
      haveI : Group.IsNilpotent ↥(Work.GW2.fittingIn N) := b16c_isNilpotent_fittingIn N
      exact le_pCoreIn_of_isPGroup_of_isNilpotent (Work.GW2.fittingIn N) inf_le_left
        ((b16c_isPGroup_pCoreIn p M).to_le inf_le_right)
    exact (le_inf h1 h2).trans (h3.trans
      (b16c_pCoreIn_le_pCoreIn_of_le_normal (N := Work.GW2.fittingIn N) (B := N) hFleN hNnormF))
  -- ## 5. The three subgroups lemma in `↥N`: `⁅⁅X, P⁆, Q⁆ ≤ O_p(N)`
  haveI : (Work.GW2.pCore p ↥N).Normal := Work.GW2.pCore_normal p ↥N
  have hstep : ⁅⁅(⁅N, Work.GW2.pCoreIn p M⁆).subgroupOf N,
        (Work.GW2.pCoreIn p M).subgroupOf N⁆,
        (Work.GW2.pCoreIn q M).subgroupOf N⁆ ≤ Work.GW2.pCore p ↥N := by
    refine OddOrder.Isaacs.Ch04.commutator_commutator_le_of_rotate
      (H₁ := (⁅N, Work.GW2.pCoreIn p M⁆).subgroupOf N)
      (H₂ := (Work.GW2.pCoreIn p M).subgroupOf N)
      (H₃ := (Work.GW2.pCoreIn q M).subgroupOf N) ?_ ?_
    · have hPQ' : ⁅(Work.GW2.pCoreIn p M).subgroupOf N,
          (Work.GW2.pCoreIn q M).subgroupOf N⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        apply Subtype.ext
        exact Subgroup.mem_centralizer_iff.mp
          (hPcenQ (Subgroup.mem_subgroupOf.mp ha)) ((b : ↥N) : G)
          (Subgroup.mem_subgroupOf.mp hb)
      rw [hPQ', Subgroup.commutator_bot_left]
      exact bot_le
    · refine (Subgroup.map_le_map_iff_of_injective (f := N.subtype)
        N.subtype_injective).mp ?_
      rw [Subgroup.map_commutator, Subgroup.map_commutator,
        Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
        Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr hQleN, inf_eq_left.mpr hXleN, inf_eq_left.mpr hPleN,
        Subgroup.commutator_comm (Work.GW2.pCoreIn q M) (⁅N, Work.GW2.pCoreIn p M⁆)]
      exact hXQP
  have hmap := Subgroup.map_mono (f := N.subtype) hstep
  rw [Subgroup.map_commutator, Subgroup.map_commutator,
    Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr hXleN, inf_eq_left.mpr hPleN, inf_eq_left.mpr hQleN] at hmap
  exact hmap


theorem B16Core {G : Type} [Group G] [Finite G]
    (T : Work.GW2.LocalToolkit) (hG : IsSimpleGroup G) {A B : Subgroup G}
    (hA : IsCoatom A) (hB : IsCoatom B) (hne : A ≠ B)
    (hDA : Work.GW2.DihOrCycSylow A) (hDGA : Work.GW2.IsDGroup A)
    (hDB : Work.GW2.DihOrCycSylow B) (hDGB : Work.GW2.IsDGroup B)
    (hAB : Work.GW2.fstarIn A ≤ B) (hBA : Work.GW2.fstarIn B ≤ A)
    (hLA : Work.GW2.layerIn A = ⊥) (hLB : Work.GW2.layerIn B = ⊥)
    (p : ℕ) (hp : p.Prime) (hpA : Work.GW2.pCoreIn p A ≠ ⊥) :
    IsPGroup p ↥(Work.GW2.fstarIn A) ∧ IsPGroup p ↥(Work.GW2.fstarIn B) := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- the two `BRel` relations, witnessed by `⊥`
  have hbotnorm : Subgroup.normalizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
    rw [Subgroup.normalizer_eq_top_iff]; infer_instance
  have hrelAB : Work.GW2.BRel A B :=
    ⟨⊥, bot_le, by rw [hbotnorm, top_inf_eq]; exact hAB⟩
  have hrelBA : Work.GW2.BRel B A :=
    ⟨⊥, bot_le, by rw [hbotnorm, top_inf_eq]; exact hBA⟩
  have hpi := Work.BMAX.GWPiEq T G hG A B hDA hDGA hDB hDGB hA hB.ne_top hrelAB hB hrelBA
  -- `π(F(A)) ∋ q ⟹ π(F(B)) ∋ q`
  have hqmem : ∀ q : ℕ, q.Prime → Work.GW2.pCoreIn q A ≠ ⊥ →
      Work.GW2.pCoreIn q B ≠ ⊥ := by
    intro q hq hqA hqB
    have hqπ : q ∉ Work.GW2.primesOf (Work.GW2.fittingIn A) := by
      rw [hpi]
      exact (Work.BMAX.pCoreIn_eq_bot_iff_not_mem_primesOf B q hq).mp hqB
    exact hqA ((Work.BMAX.pCoreIn_eq_bot_iff_not_mem_primesOf A q hq).mpr hqπ)
  have hpB : Work.GW2.pCoreIn p B ≠ ⊥ := hqmem p hp hpA
  -- every prime `q ≠ p` has trivial `q`-core in `A`
  have hstepA : ∀ q : ℕ, q.Prime → q ≠ p → Work.GW2.pCoreIn q A = ⊥ := by
    intro q hq hqp
    by_contra hqA
    have hqB : Work.GW2.pCoreIn q B ≠ ⊥ := hqmem q hq hqA
    have h1 : Work.GW2.pCoreIn p A ≤ Work.GW2.pCoreIn p B :=
      b16c_step hG hA hB hne hDA hDGA hDB hDGB hAB hBA hLA hLB hp hq hqp.symm hpA hqA hqB
        (b16c_comm_comm_pCoreIn T hG hDA hDGA hDB hDGB hAB hBA hLA hLB p q hp hq hqp.symm)
    have h2 : Work.GW2.pCoreIn p B ≤ Work.GW2.pCoreIn p A :=
      b16c_step hG hB hA (Ne.symm hne) hDB hDGB hDA hDGA hBA hAB hLB hLA hp hq hqp.symm hpB hqB hqA
        (b16c_comm_comm_pCoreIn T hG hDB hDGB hDA hDGA hBA hAB hLB hLA p q hp hq hqp.symm)
    -- `O_p(A) = O_p(B) ◁ ⟨A,B⟩ = ⊤` contradicts simplicity
    have hEq : Work.GW2.pCoreIn p A = Work.GW2.pCoreIn p B := le_antisymm h1 h2
    have htop : Subgroup.normalizer (Work.GW2.pCoreIn p A : Set G) = ⊤ := by
      rw [eq_top_iff, ← b16c_sup_eq_top hA hB hne]
      exact sup_le (le_normalizer_pCoreIn A p) (hEq ▸ le_normalizer_pCoreIn B p)
    haveI : (Work.GW2.pCoreIn p A).Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases hG.eq_bot_or_eq_top_of_normal (Work.GW2.pCoreIn p A) with h | h
    · exact hpA h
    · exact hA.ne_top (top_le_iff.mp (h ▸ Subgroup.map_subtype_le _))
  -- `q ∉ π(F(B))` for `q ≠ p` as well
  have hstepB : ∀ q : ℕ, q.Prime → q ≠ p → Work.GW2.pCoreIn q B = ⊥ := by
    intro q hq hqp
    rw [Work.BMAX.pCoreIn_eq_bot_iff_not_mem_primesOf B q hq, ← hpi]
    exact (Work.BMAX.pCoreIn_eq_bot_iff_not_mem_primesOf A q hq).mp (hstepA q hq hqp)
  refine ⟨?_, ?_⟩
  · rw [b16c_fstarIn_eq_fittingIn hLA]
    exact fittingIn_isPGroup_of_unique_pCore hp hstepA
  · rw [b16c_fstarIn_eq_fittingIn hLB]
    exact fittingIn_isPGroup_of_unique_pCore hp hstepB

end Work.BMAX
