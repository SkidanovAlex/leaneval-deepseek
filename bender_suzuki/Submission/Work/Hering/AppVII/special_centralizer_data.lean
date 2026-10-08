import Mathlib
import Submission.Work.Coprime.All
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.commutator_le_frattiniIn
import Submission.Work.Hering.AppVII.part1_Q_isPGroup_and_frattini

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Peterfalvi Appendix VII: the centralizer of the acting group of prime order

Let `A = Q ⋊ P` with `Q ⊴ A`, `P ∩ Q = 1`, `|P| = p` prime, `p ∤ |Q|`, `⁅P, Q⁆ = Q`,
`Φ(Q) ≤ Z(Q)`, and the *minimality* condition

`∀ Q' ≤ Q, Q' ≠ ⊥, Q' ≠ Q → ⁅P, Q'⁆ ≤ Q' → ⁅P, Q'⁆ = ⊥`

that every proper non-trivial `P`-invariant subgroup of `Q` is centralized by `P`.
Then:

* if `Q` is abelian, `C_Q(P) = 1`;
* if `Q` is non-abelian, `C_Q(P) = Z(Q)`.

## Mathematics

The engine is the coprime action of the cyclic group `P` (of prime order `p`) on `Q`
(`p ∤ |Q|`).  Since `⁅P, Q⁆ = Q`, on the abelianization `Q / [Q,Q]` the action still has
`[Q/[Q,Q], P] = Q/[Q,Q]`, so `Q / [Q,Q]` has no non-trivial `P`-fixed vector
(`Work.Coprime.abelian_split`: for abelian `G`, `C_G(A)` and `[G,A]` are complementary).
Hence `C_Q(P) ≤ [Q,Q]`.

* If `Q` is abelian, `[Q,Q] = 1` and we are done.
* If `Q` is non-abelian, `part1_Q_isPGroup_and_frattini` gives that `Q` is a `q`-group;
  then `[Q,Q] ≤ Φ(Q) ≤ Z(Q)`, so `C_Q(P) ≤ Z(Q)`.  Conversely `Z(Q) ≤ C_Q(P)` by the
  minimality hypothesis applied to the subgroup `Z(Q) ≤ Q` (proper since `Q` is
  non-abelian).

The three general lemmas are pure coprime-action facts, independent of the application.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

open scoped Pointwise
open scoped commutatorElement

namespace Work.Hering.AppVII

/-! ## General coprime-action lemmas -/

/-- For an abelian finite group `G` with a coprime action of `A` and `[G,A] = G`, the fixed
points vanish.  (For abelian `G` the fixed points and the commutator are complementary;
if the commutator is everything, the fixed points are trivial.) -/
theorem fixedPoints_eq_bot_of_commutator_eq_top {A G : Type*} [Group A] [Group G] [Finite A]
    [Finite G] [MulDistribMulAction A G] [IsMulCommutative G]
    (hcop : (Nat.card A).Coprime (Nat.card G))
    (hcomm : FT.commutator A (⊤ : Subgroup G) = ⊤) : FT.fixedPoints A G = ⊥ := by
  have hcomp : (FT.fixedPoints A G).IsComplement' (FT.commutator A (⊤ : Subgroup G)) :=
    Work.Coprime.abelian_split A hcop
  rw [hcomm] at hcomp
  exact Subgroup.isComplement'_top_right.mp hcomp

/-- The abstract commutator `[G,A]` is transported to the quotient by a surjective,
action-compatible homomorphism: if `[G,A] = G` then `[G/N, A] = G/N`. -/
theorem map_commutator_top {A G H : Type*} [Group A] [Group G] [Group H]
    [MulDistribMulAction A G] [MulDistribMulAction A H] (f : G →* H)
    (hf : Function.Surjective f) (hact : ∀ (a : A) (x : G), f (a • x) = a • f x)
    (hG : FT.commutator A (⊤ : Subgroup G) = ⊤) :
    FT.commutator A (⊤ : Subgroup H) = ⊤ := by
  have hle : (FT.commutator A (⊤ : Subgroup G)).map f ≤ FT.commutator A (⊤ : Subgroup H) := by
    rw [Subgroup.map_le_iff_le_comap]
    refine FT.commutator_le (fun a x _ => ?_)
    rw [Subgroup.mem_comap, map_mul, map_inv, hact]
    exact FT.le_commutator a (Subgroup.mem_top (f x))
  have h1 : (FT.commutator A (⊤ : Subgroup G)).map f = (⊤ : Subgroup H) := by
    rw [hG, Subgroup.map_top_of_surjective f hf]
  exact eq_top_iff.mpr ((ge_of_eq h1).trans hle)

/-- **Fixed points lie in the derived subgroup.**  If a finite group `A` acts coprimely on a
finite group `G` with `[G,A] = G`, then `C_G(A) ≤ [G,G]`. -/
theorem fixedPoints_le_commutator_of_commutator_eq_top {A G : Type*} [Group A] [Group G]
    [Finite A] [Finite G] [MulDistribMulAction A G] (hcop : (Nat.card A).Coprime (Nat.card G))
    (hcomm : FT.commutator A (⊤ : Subgroup G) = ⊤) :
    FT.fixedPoints A G ≤ ⁅(⊤ : Subgroup G), ⊤⁆ := by
  set N : Subgroup G := ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ with hN
  haveI hNn : N.Normal := hN ▸ Subgroup.commutator_normal (⊤ : Subgroup G) (⊤ : Subgroup G)
  haveI hNi : FT.IsInvariant A N :=
    hN ▸ FT.IsInvariant.of_characteristic
      (Subgroup.commutator_characteristic (⊤ : Subgroup G) (⊤ : Subgroup G))
  haveI hMcomm : IsMulCommutative (G ⧸ N) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr (le_of_eq (commutator_def G))
  have hcop' : (Nat.card A).Coprime (Nat.card (G ⧸ N)) :=
    hcop.coprime_dvd_right (Subgroup.card_quotient_dvd_card N)
  have hcomm' : FT.commutator A (⊤ : Subgroup (G ⧸ N)) = ⊤ :=
    map_commutator_top (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
      (fun _ _ => rfl) hcomm
  have hfix : FT.fixedPoints A (G ⧸ N) = ⊥ :=
    fixedPoints_eq_bot_of_commutator_eq_top hcop' hcomm'
  have hmap := FT.map_fixedPoints_le (A := A) N
  rw [hfix] at hmap
  have hbot : (FT.fixedPoints A G).map (QuotientGroup.mk' N) = ⊥ := le_bot_iff.mp hmap
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  exact hN ▸ hbot

/-- The main statement of Appendix VII used here: the centralizer of the acting group of prime
order inside `Q` is either trivial (`Q` abelian) or the centre of `Q` (`Q` non-abelian). -/
theorem special_centralizer_data {A : Type*} [Group A] [Finite A] (P Q : Subgroup A) (hQn : Q.Normal)
    (hinf : P ⊓ Q = ⊥) (hsup : P ⊔ Q = ⊤) {p : ℕ} (hp : p.Prime) (hcardP : Nat.card ↥P = p)
    (hpQ : ¬ p ∣ Nat.card ↥Q) (hcomm : ⁅P, Q⁆ = Q)
    (hPhi : frattini ↥Q ≤ Subgroup.center ↥Q)
    (hcent : ∀ Q' : Subgroup A, Q' ≤ Q → Q' ≠ ⊥ → Q' ≠ Q → ⁅P, Q'⁆ ≤ Q' → ⁅P, Q'⁆ = ⊥) :
    (IsMulCommutative ↥Q → Q ⊓ Subgroup.centralizer (P : Set A) = ⊥) ∧
      (¬ IsMulCommutative ↥Q →
        Q ⊓ Subgroup.centralizer (P : Set A) = (Subgroup.center ↥Q).map Q.subtype) := by
  haveI : Q.Normal := hQn
  -- `P` normalizes `Q`, so it acts on `Q` by conjugation
  haveI hNorm : FT.Normalizes P Q := ⟨by rw [Subgroup.normalizer_eq_top]; exact le_top⟩
  have hcop : (Nat.card ↥P).Coprime (Nat.card ↥Q) := by
    rw [hcardP]; exact hp.coprime_iff_not_dvd.mpr hpQ
  have hmap_top : (⊤ : Subgroup ↥Q).map Q.subtype = Q := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  -- `[Q,P] = Q` in the abstract (conjugation) action of `↥P` on `↥Q`
  have htopQ : FT.commutator ↥P (⊤ : Subgroup ↥Q) = ⊤ := by
    have h1 : (FT.commutator ↥P (⊤ : Subgroup ↥Q)).map Q.subtype
        = (⊤ : Subgroup ↥Q).map Q.subtype := by
      rw [FT.commutator_conjAction P Q, Subgroup.commutator_comm, hcomm, hmap_top]
    exact Subgroup.map_injective Q.subtype_injective h1
  -- `C_Q(P)` transported to `A` is the intersection `Q ⊓ C_A(P)`
  have hC : Q ⊓ Subgroup.centralizer (P : Set A) = (FT.fixedPoints ↥P ↥Q).map Q.subtype := by
    rw [inf_comm, ← FT.map_fixedPoints_conjAction P Q]
  constructor
  · -- ## `Q` abelian: `C_Q(P) = 1`
    intro hQab
    haveI := hQab
    have hfix := fixedPoints_eq_bot_of_commutator_eq_top (A := ↥P) (G := ↥Q) hcop htopQ
    rw [hC, hfix, Subgroup.map_bot]
  · -- ## `Q` non-abelian: `C_Q(P) = Z(Q)`
    intro hQnab
    have hQne : Q ≠ ⊥ := by
      intro h
      exact hQnab (h ▸ (inferInstance : IsMulCommutative ↥(⊥ : Subgroup A)))
    have hnotcent : ⁅P, Q⁆ ≠ ⊥ := by rw [hcomm]; exact hQne
    have hPcard : (Nat.card ↥P).Prime := by rw [hcardP]; exact hp
    -- `Q` is a `q`-group
    obtain ⟨q, hq, hQp⟩ :=
      (part1_Q_isPGroup_and_frattini P Q hQn hsup hinf hPcard
        (by rw [hcardP]; exact hpQ) hnotcent hcent).1
    -- `C_Q(P) ⊆ [Q,Q]`
    have hkey : FT.fixedPoints ↥P ↥Q ≤ ⁅(⊤ : Subgroup ↥Q), (⊤ : Subgroup ↥Q)⁆ :=
      fixedPoints_le_commutator_of_commutator_eq_top hcop htopQ
    -- `[Q,Q] ⊆ Φ(Q) ⊆ Z(Q)`
    have hQQ : ⁅Q, Q⁆ ≤ (Subgroup.center ↥Q).map Q.subtype := by
      have h1 : ⁅Q, Q⁆ ≤ Work.PGroup.frattiniIn Q := Work.PGroup.commutator_le_frattiniIn hq Q hQp
      have h2 : Work.PGroup.frattiniIn Q ≤ (Subgroup.center ↥Q).map Q.subtype :=
        Subgroup.map_mono hPhi
      exact h1.trans h2
    have hC_le : Q ⊓ Subgroup.centralizer (P : Set A) ≤ (Subgroup.center ↥Q).map Q.subtype := by
      rw [hC]
      calc (FT.fixedPoints ↥P ↥Q).map Q.subtype
          ≤ (⁅(⊤ : Subgroup ↥Q), (⊤ : Subgroup ↥Q)⁆).map Q.subtype := Subgroup.map_mono hkey
        _ = ⁅Q, Q⁆ := by rw [Subgroup.map_commutator, hmap_top]
        _ ≤ (Subgroup.center ↥Q).map Q.subtype := hQQ
    -- `Z(Q) ⊆ C_Q(P)` via the minimality hypothesis
    have hZ_le : (Subgroup.center ↥Q).map Q.subtype ≤ Q ⊓ Subgroup.centralizer (P : Set A) := by
      by_cases hZbot : (Subgroup.center ↥Q).map Q.subtype = ⊥
      · rw [hZbot]; exact bot_le
      · have hZQ : (Subgroup.center ↥Q).map Q.subtype ≠ Q := by
          intro h
          have htop : Subgroup.center ↥Q = ⊤ := by
            have h1 : (Subgroup.center ↥Q).map Q.subtype = (⊤ : Subgroup ↥Q).map Q.subtype := by
              rw [h, hmap_top]
            exact Subgroup.map_injective Q.subtype_injective h1
          exact hQnab (Subgroup.center_eq_top_iff.mp htop)
        -- `P` normalizes `Z(Q)` (the centre of `Q` is characteristic in `Q`)
        have hPZ : ⁅P, (Subgroup.center ↥Q).map Q.subtype⁆
            ≤ (Subgroup.center ↥Q).map Q.subtype := by
          haveI hZinv : FT.IsInvariant ↥P (Subgroup.center ↥Q) :=
            FT.IsInvariant.of_characteristic (Subgroup.centerCharacteristic (G := ↥Q))
          rw [Subgroup.commutator_le]
          intro gp hp' h hh
          rw [commutatorElement_def]
          have hconj' : gp * h * gp⁻¹ ∈ (Subgroup.center ↥Q).map Q.subtype := by
            have hconj : (MulAut.conj gp) h ∈ (Subgroup.center ↥Q).map Q.subtype := by
              have hZmap : Subgroup.map (MulAut.conj gp).toMonoidHom
                  ((Subgroup.center ↥Q).map Q.subtype) = (Subgroup.center ↥Q).map Q.subtype := by
                have h2 := map_conj_eq_map_smul P Q
                  (fun a q => FT.conj_smul_coe P Q a q) (Subgroup.center ↥Q) (⟨gp, hp'⟩ : ↥P)
                rw [h2, hZinv.smul_eq_self]
              rw [← hZmap]
              exact Subgroup.mem_map_of_mem _ hh
            rwa [MulAut.conj_apply] at hconj
          exact Subgroup.mul_mem _ hconj' (Subgroup.inv_mem _ hh)
        have hcen := hcent _ (Subgroup.map_subtype_le _) hZbot hZQ hPZ
        refine le_inf (Subgroup.map_subtype_le _) ?_
        rw [Subgroup.le_centralizer_iff]
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcen
    exact le_antisymm hC_le hZ_le

end Work.Hering.AppVII
