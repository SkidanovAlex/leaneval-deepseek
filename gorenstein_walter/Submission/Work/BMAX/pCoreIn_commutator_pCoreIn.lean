/-
# `[O_q(B), O_r(A)] = 1` for two distinct primes `q ≠ r` in `π(F(A))`

This file proves

  `Work.BMAX.pCoreIn_commutator_pCoreIn`:
  `G` finite simple, `A` coatomic (maximal), `B ≠ ⊤` with `F*(A) ≤ B`, and `q ≠ r` two primes in
  `π(F(A)) = primesOf (fittingIn A)`  ⟹  `⁅O_q(B), O_r(A)⁆ = ⊥`.

## Mathematics

This is Bender 1970, §1.7 (ii) — `[O_p(B), O^p(F*(A))] = 1` for `p ∈ π(F(A))` — in the
*Fitting* case, where it reduces to the Thompson `P × K` lemma (Bender 1970, 1.1).

Write `P := O_q(A)`, `V := O_q(B)`, `R := O_r(A)`.

* `q ∈ π(F(A))` gives `P ≠ 1` (`pCoreIn_eq_bot_iff_mem_primesOf`).  Since `P ◁ A` is non-trivial
  and `A` is maximal in the simple group `G`, `C_G(P) ≤ A` (`normalizer_pCoreIn_eq`).
* `R ≤ F(A) ≤ F*(A) ≤ B` (`pCoreIn_le_fittingIn`, `fittingIn_le_fstarIn`, `hR`), and `V ◁ B`.
* `[P, R] = 1`: both are subgroups of the nilpotent group `F(A)` and their elements have coprime
  orders (`commute_of_coprime_orderOf_of_isNilpotent` of the odd-order library).
* **The `P`-fixed points of `V` centralise `R`.**  If `v ∈ V` centralises `P`, then
  `v ∈ C_G(P) ≤ A`; hence `v ∈ V ⊓ A`, and
  `⁅V ⊓ A, R⁆ ≤ V` (because `R ≤ B ≤ N_G(V)`) and `⁅V ⊓ A, R⁆ ≤ R` (because
  `V ⊓ A ≤ A ≤ N_G(R)`).  As `V` is a `q`-group and `R` an `r`-group with `q ≠ r`, it follows
  that `⁅V ⊓ A, R⁆ = ⊥`, i.e. `v` centralises `R`.
* The Thompson `P × K` lemma (Isaacs 4.31), applied with `K = R`, now gives `⁅V, R⁆ = ⊥`.

## Formalisation

The `P × K` lemma for subgroups acting by conjugation is `Work.BMAX.pcpc_thompson_PK_commutator`;
it was reproved in `pCoreIn_commutator_layerIn` because the module that originally held it does
not currently compile.
-/
import Mathlib
import Submission.Work.BMAX.Defs
import Submission.Work.BMAX.Basic
import Submission.Work.BMAX.D17Defs
import Submission.Work.BMAX.Bender17i_dedekind_basic
import Submission.Work.BMAX.LayerCentralizesFitting

namespace Work.BMAX

open Subgroup

set_option maxHeartbeats 1000000

/-! ## 0. Elementary API for `pCoreIn` and Thompson's `P × K` lemma -/

/-- `O_p(K) ≤ K`. -/
theorem pcpc_pCoreIn_le_self {G : Type} [Group G] (p : ℕ) (K : Subgroup G) :
    Work.GW2.pCoreIn p K ≤ K :=
  Subgroup.map_subtype_le (H := K) (Work.GW2.pCore p ↥K)

/-- `O_p(K)` is a `p`-group. -/
theorem pcpc_isPGroup_pCoreIn {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (K : Subgroup G) : IsPGroup p ↥(Work.GW2.pCoreIn p K) := by
  have h : IsPGroup p ↥(Work.GW2.pCore p ↥K) := by
    rw [Work.CORE2A.pCore_eq_opCore (G := ↥K) (p := p)]
    exact OddOrder.Isaacs.Ch01.opCore_isPGroup p ↥K
  rw [Work.GW2.pCoreIn]
  exact h.of_equiv (Subgroup.equivMapOfInjective (Work.GW2.pCore p ↥K) K.subtype
    K.subtype_injective)

/-- **Thompson's `P × K` lemma (Bender 1970, 1.1; Isaacs 4.31).**  Let `Q` be a `p`-group
normalised by `B`, and `P, K ≤ B` with `P` a `p`-group, `K` a `p'`-group, `P` and `K`
commuting elementwise, and `K` centralising the `P`-fixed points of `Q`.  Then `K` centralises
`Q`. -/
theorem pcpc_thompson_PK_commutator {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Q P K : Subgroup G}
    (hQB : Q ≤ B) (hPB : P ≤ B) (hKB : K ≤ B)
    (hQn : B ≤ Subgroup.normalizer (Q : Set G))
    (hQp : IsPGroup p ↥Q) (hPp : IsPGroup p ↥P) (hKc : ¬ p ∣ Nat.card ↥K)
    (hcomm : ∀ x ∈ P, ∀ y ∈ K, x * y = y * x)
    (hfix : ∀ q ∈ Q, (∀ x ∈ P, q * x = x * q) → ∀ y ∈ K, q * y = y * q) :
    ⁅Q, K⁆ = ⊥ := by
  classical
  haveI hQnB : (Q.subgroupOf B).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hQn
  -- the identification `↥(Q.subgroupOf B) ≃* ↥Q`
  let e : ↥(Q.subgroupOf B) ≃* ↥Q :=
    { toFun := fun x => ⟨(((x : ↥B) : G)), x.2⟩
      invFun := fun x => ⟨⟨(x : G), hQB x.2⟩, x.2⟩
      left_inv := fun x => by ext <;> rfl
      right_inv := fun x => by ext <;> rfl
      map_mul' := fun x y => by ext <;> rfl }
  -- the multiplication map `↥P × ↥K →* ↥B`
  let mult : ↥P × ↥K →* ↥B :=
    { toFun := fun x => ⟨(x.1 : G) * (x.2 : G), B.mul_mem (hPB x.1.2) (hKB x.2.2)⟩
      map_one' := by ext; simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        show ((x.1 : G) * (y.1 : G)) * ((x.2 : G) * (y.2 : G)) =
          (x.1 : G) * (x.2 : G) * ((y.1 : G) * (y.2 : G))
        have hxy : (y.1 : G) * (x.2 : G) = (x.2 : G) * (y.1 : G) :=
          hcomm (y.1 : G) y.1.2 (x.2 : G) x.2.2
        calc ((x.1 : G) * (y.1 : G)) * ((x.2 : G) * (y.2 : G))
            = (x.1 : G) * ((y.1 : G) * (x.2 : G)) * (y.2 : G) := by group
          _ = (x.1 : G) * ((x.2 : G) * (y.1 : G)) * (y.2 : G) := by rw [hxy]
          _ = (x.1 : G) * (x.2 : G) * ((y.1 : G) * (y.2 : G)) := by group }
  -- the conjugation action of `P × K` on `Q` (computed inside `B`)
  let φ : ↥P × ↥K →* MulAut ↥(Q.subgroupOf B) := MulAut.conjNormal.comp mult
  have he_symm_apply : ∀ x : ↥Q, e.symm x = (⟨⟨(x : G), hQB x.2⟩, x.2⟩ : ↥(Q.subgroupOf B)) :=
    fun x => rfl
  have hmult_left : ∀ x : ↥P, mult (x, 1) = (⟨(x : G), hPB x.2⟩ : ↥B) := by
    intro x
    apply Subtype.ext
    show (x : G) * 1 = (x : G)
    simp
  have hmult_right : ∀ y : ↥K, mult (1, y) = (⟨(y : G), hKB y.2⟩ : ↥B) := by
    intro y
    apply Subtype.ext
    show (1 : G) * (y : G) = (y : G)
    simp
  -- the two hypotheses of Isaacs 4.31
  have hfixφ : ∀ g : ↥(Q.subgroupOf B),
      (∀ x : ↥P, (φ (x, 1)) g = g) → ∀ y : ↥K, (φ (1, y)) g = g := by
    intro g hg y
    have hgc : ∀ x ∈ P, ((g : ↥B) : G) * x = x * ((g : ↥B) : G) := by
      intro x hx
      have hpt : MulAut.conjNormal (mult (⟨x, hx⟩, 1)) g = g := hg ⟨x, hx⟩
      rw [hmult_left ⟨x, hx⟩] at hpt
      have hpt' := congrArg (fun z : ↥(Q.subgroupOf B) => (z : ↥B)) hpt
      rw [MulAut.conjNormal_apply] at hpt'
      have hval : x * ((g : ↥B) : G) * x⁻¹ = ((g : ↥B) : G) := by
        have h := congrArg (fun z : ↥B => (z : G)) hpt'
        simpa using h
      calc ((g : ↥B) : G) * x = (x * ((g : ↥B) : G) * x⁻¹) * x := by rw [hval]
        _ = x * ((g : ↥B) : G) := by group
    have hfixg := hfix ((g : ↥B) : G) g.2 hgc (y : G) y.2
    show MulAut.conjNormal (mult (1, y)) g = g
    rw [hmult_right y]
    apply Subtype.ext
    show (((MulAut.conjNormal (⟨(y : G), hKB y.2⟩ : ↥B)) g : ↥(Q.subgroupOf B)) : ↥B) = (g : ↥B)
    rw [MulAut.conjNormal_apply]
    apply Subtype.ext
    show (y : G) * ((g : ↥B) : G) * (y : G)⁻¹ = ((g : ↥B) : G)
    rw [← hfixg]
    group
  have hthom := OddOrder.Isaacs.Ch04.isaacs_thm_4_31_external φ
    (hQp.of_equiv e.symm) hPp hKc hfixφ
  have hthom' : ∀ (y : ↥K) (b : ↥(Q.subgroupOf B)), (φ (1, y)) b = b :=
    (OddOrder.Isaacs.Ch04.actionCommutator_eq_bot_iff_acts_trivially _).mp hthom
  -- conclude
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hpt : MulAut.conjNormal (mult (1, ⟨y, hy⟩)) (e.symm ⟨k, hk⟩) = e.symm ⟨k, hk⟩ :=
    hthom' ⟨y, hy⟩ (e.symm ⟨k, hk⟩)
  rw [hmult_right ⟨y, hy⟩] at hpt
  have hpt' := congrArg (fun z : ↥(Q.subgroupOf B) => (z : ↥B)) hpt
  rw [MulAut.conjNormal_apply] at hpt'
  have hval : y * k * y⁻¹ = k := by
    have h := congrArg (fun z : ↥B => (z : G)) hpt'
    rw [he_symm_apply ⟨k, hk⟩] at h
    simpa using h
  calc y * k = (y * k * y⁻¹) * y := by group
    _ = k * y := by rw [hval]

theorem pCoreIn_commutator_pCoreIn (G : Type) [Group G] [Finite G] (hG : IsSimpleGroup G)
    (A B : Subgroup G) (hA : IsCoatom A) (hB : B ≠ ⊤) (hR : Work.GW2.fstarIn A ≤ B)
    (q r : ℕ) (hq : q.Prime) (hqpi : q ∈ Work.GW2.primesOf (Work.GW2.fittingIn A))
    (hr : r.Prime) (hrpi : r ∈ Work.GW2.primesOf (Work.GW2.fittingIn A)) (hqr : q ≠ r) :
    ⁅Work.GW2.pCoreIn q B, Work.GW2.pCoreIn r A⁆ = ⊥ := by
  classical
  haveI hqFact : Fact q.Prime := ⟨hq⟩
  haveI hrFact : Fact r.Prime := ⟨hr⟩
  -- ## containments in `B` and `p`-group facts
  have hFB : Work.GW2.fittingIn A ≤ B := (Work.GW2.fittingIn_le_fstarIn A).trans hR
  have hQB : Work.GW2.pCoreIn q B ≤ B := pcpc_pCoreIn_le_self q B
  have hPB : Work.GW2.pCoreIn q A ≤ B := (pCoreIn_le_fittingIn A hq).trans hFB
  have hKB : Work.GW2.pCoreIn r A ≤ B := (pCoreIn_le_fittingIn A hr).trans hFB
  have hQn : B ≤ Subgroup.normalizer ((Work.GW2.pCoreIn q B : Subgroup G) : Set G) :=
    le_normalizer_pCoreIn B q
  have hQp : IsPGroup q ↥(Work.GW2.pCoreIn q B) := pcpc_isPGroup_pCoreIn q B
  have hPp : IsPGroup q ↥(Work.GW2.pCoreIn q A) := pcpc_isPGroup_pCoreIn q A
  have hRp : IsPGroup r ↥(Work.GW2.pCoreIn r A) := pcpc_isPGroup_pCoreIn r A
  -- `O_q(A) ≠ 1`
  have hPne : Work.GW2.pCoreIn q A ≠ ⊥ := fun h =>
    ((pCoreIn_eq_bot_iff_mem_primesOf A hq).mp h) hqpi
  -- ## `[O_q(A), O_r(A)] = 1`: coprime elements of the nilpotent group `F(A)` commute
  have hcomm : ∀ x ∈ Work.GW2.pCoreIn q A, ∀ y ∈ Work.GW2.pCoreIn r A, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp hPp) ⟨x, hx⟩
    obtain ⟨b, hb⟩ := (IsPGroup.iff_orderOf.mp hRp) ⟨y, hy⟩
    -- the orders of `x`, `y` are powers of `q`, `r`
    have hxa : orderOf x = q ^ a := by
      have h : orderOf (↑(⟨x, hx⟩ : ↥(Work.GW2.pCoreIn q A)) : G) = q ^ a := by
        simpa using ha
      simpa using h
    have hyb : orderOf y = r ^ b := by
      have h : orderOf (↑(⟨y, hy⟩ : ↥(Work.GW2.pCoreIn r A)) : G) = r ^ b := by
        simpa using hb
      simpa using h
    haveI hFnil : Group.IsNilpotent ↥(Work.GW2.fittingIn A) := isNilpotent_fittingIn A
    have hxF : x ∈ Work.GW2.fittingIn A := pCoreIn_le_fittingIn A hq hx
    have hyF : y ∈ Work.GW2.fittingIn A := pCoreIn_le_fittingIn A hr hy
    have h1 : orderOf (⟨x, hxF⟩ : ↥(Work.GW2.fittingIn A)) = q ^ a := by
      have h : orderOf (↑(⟨x, hxF⟩ : ↥(Work.GW2.fittingIn A)) : G) = q ^ a := by
        simpa using hxa
      simpa using h
    have h2 : orderOf (⟨y, hyF⟩ : ↥(Work.GW2.fittingIn A)) = r ^ b := by
      have h : orderOf (↑(⟨y, hyF⟩ : ↥(Work.GW2.fittingIn A)) : G) = r ^ b := by
        simpa using hyb
      simpa using h
    have hcop : Nat.Coprime (orderOf (⟨x, hxF⟩ : ↥(Work.GW2.fittingIn A)))
        (orderOf (⟨y, hyF⟩ : ↥(Work.GW2.fittingIn A))) := by
      rw [h1, h2]
      exact Nat.coprime_pow_primes a b hq hr hqr
    have hc := OddOrder.GroupTheory.commute_of_coprime_orderOf_of_isNilpotent hcop
    simpa using congrArg Subtype.val hc.eq
  -- ## the `P`-fixed points of `O_q(B)` centralise `O_r(A)`
  have hfix : ∀ v ∈ Work.GW2.pCoreIn q B, (∀ x ∈ Work.GW2.pCoreIn q A, v * x = x * v) →
      ∀ y ∈ Work.GW2.pCoreIn r A, v * y = y * v := by
    intro v hvQ hvP y hyR
    -- `C_G(O_q(A)) ≤ A`
    have hvA : v ∈ A := by
      have h1 : v ∈ Subgroup.centralizer ((Work.GW2.pCoreIn q A : Subgroup G) : Set G) :=
        Subgroup.mem_centralizer_iff.mpr (fun x hx => (hvP x hx).symm)
      have h2 : v ∈ Subgroup.normalizer ((Work.GW2.pCoreIn q A : Subgroup G) : Set G) :=
        Subgroup.centralizer_le_normalizer _ h1
      rwa [normalizer_pCoreIn_eq hG hA hPne] at h2
    have hvM : v ∈ Work.GW2.pCoreIn q B ⊓ A := Subgroup.mem_inf.mpr ⟨hvQ, hvA⟩
    -- `O_q(B)` is a `q`-group and `O_r(A)` an `r`-group, `q ≠ r`
    have hbot : Work.GW2.pCoreIn q B ⊓ Work.GW2.pCoreIn r A = ⊥ :=
      (disjoint_iff.mp (IsPGroup.disjoint_of_ne q r hqr _ _ hQp hRp))
    -- `⁅O_q(B), O_r(A)⁆ ≤ O_q(B)`
    have hQRle : ⁅Work.GW2.pCoreIn q B, Work.GW2.pCoreIn r A⁆ ≤ Work.GW2.pCoreIn q B := by
      rw [Subgroup.commutator_comm]
      exact (Subgroup.le_normalizer_iff_commutator_le_right).mp (hKB.trans hQn)
    -- `⁅O_q(B) ⊓ A, O_r(A)⁆ ≤ O_r(A)`
    have hRle : ⁅Work.GW2.pCoreIn q B ⊓ A, Work.GW2.pCoreIn r A⁆ ≤ Work.GW2.pCoreIn r A :=
      (Subgroup.le_normalizer_iff_commutator_le_right).mp
        ((inf_le_right : (Work.GW2.pCoreIn q B ⊓ A : Subgroup G) ≤ A).trans
          (le_normalizer_pCoreIn A r))
    -- hence `⁅O_q(B) ⊓ A, O_r(A)⁆ ≤ O_q(B) ⊓ O_r(A) = ⊥`
    have hQle : ⁅Work.GW2.pCoreIn q B ⊓ A, Work.GW2.pCoreIn r A⁆ ≤ Work.GW2.pCoreIn q B :=
      (Subgroup.commutator_mono inf_le_left le_rfl).trans hQRle
    have hMbot : ⁅Work.GW2.pCoreIn q B ⊓ A, Work.GW2.pCoreIn r A⁆ = ⊥ :=
      le_bot_iff.mp ((le_inf hQle hRle).trans (le_of_eq hbot))
    have hcen := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hMbot
    exact ((Subgroup.mem_centralizer_iff.mp (hcen hvM)) y hyR).symm
  -- ## Thompson's `P × K` lemma with `K = O_r(A)`
  have hKc : ¬ q ∣ Nat.card ↥(Work.GW2.pCoreIn r A) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hRp
    rw [hk]
    exact fun hd => hqr ((Nat.prime_dvd_prime_iff_eq hq hr).mp (hq.dvd_of_dvd_pow hd))
  exact pcpc_thompson_PK_commutator (p := q) (B := B) (Q := Work.GW2.pCoreIn q B)
    (P := Work.GW2.pCoreIn q A) (K := Work.GW2.pCoreIn r A)
    hQB hPB hKB hQn hQp hPp hKc hcomm hfix

end Work.BMAX
