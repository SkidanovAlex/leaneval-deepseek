import Mathlib
import Submission.Work.BSLit.Defs
import Submission.Work.BSLit.Wielandt.TIInfBot
import Submission.Work.BSLit.Wielandt.IsComplementOf
import Submission.Work.BSLit.Wielandt.card_map_mk_mul_card_inf
import Submission.Work.BSLit.Wielandt.map_fixedBy_mk_eq_fixedBy_quotientAction

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Wielandt's counting formula applied to the Frobenius relation: the induction

This file assembles the Frobenius case of Wielandt's counting formula from two inputs:

* `coprimeSplit` — the coprime action of `F` on `Q` splits multiplicatively over an `F`-invariant
  normal subgroup `N` with `Nat.card ↥N` coprime to `|F|`: `|C_Q(H)| = |C_N(H)| · |C_{Q ⧸ N}(H)|`
  (`Work.BSLit.fixedBy`/`Work.BSLit.quotientAction`).  Proved here from the two delivered pieces
  `card_map_mk_mul_card_inf` and `map_fixedBy_mk_eq_fixedBy_quotientAction`.
* `frobeniusFSimpleCase` (a separate module) — the `F`-simple (elementary abelian) case.

The main result is `frobeniusProduct_of_fsimple`: for a finite **solvable** group `M` acted on by
`F` with `(|F|, |M|) = 1`, subgroups `K, P ≤ F` with `K ⊔ P = ⊤`, `P` normalising `K`,
`P ⊓ P ^ k = ⊥` for `k ∈ K^#`, `|P| = p` prime, and `C_M(K) = 1`, one has

`|M| = |C_M(P)| ^ p`.

It is proved by strong induction on `|M|`: either `M` has a proper nontrivial `F`-invariant normal
subgroup `N` and one multiplies the claim for `N` (with the restricted action `restrictAction`) and
for `M ⧸ N` (with `quotientAction`) using `coprimeSplit`; or `M` is `F`-simple, hence elementary
abelian of exponent `q`, and the counting identity for the `F`-simple case applies.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.BSLit.Wielandt

open Classical

universe u

/-! ## The coprime splitting of fixed points -/

/-- **Fixed points split multiplicatively over an invariant normal subgroup (solvable case).**
Let the finite group `F` act on the finite group `Q` through `ρ` with `(|F|, |Q|) = 1`, let
`N ⊴ Q` be `F`-invariant and solvable, and let `H ≤ F`.  Then
`|C_Q(H)| = |C_N(H)| · |C_{Q ⧸ N}(H)|`. -/
theorem coprimeSplit {F Q : Type*} [Group F] [Fintype F] [Group Q] [Finite Q]
    (ρ : F →* MulAut Q) (N : Subgroup Q) [N.Normal] (hN : ∀ g : F, N.map (ρ g) = N)
    [Group.IsSolvable ↥N] (hcop : Nat.Coprime (Nat.card F) (Nat.card Q)) (H : Subgroup F) :
    Nat.card (fixedBy ρ H) = Nat.card ↥(fixedBy ρ H ⊓ N) *
      Nat.card (fixedBy (quotientAction ρ N hN) H) := by
  have h1 := card_map_mk_mul_card_inf (fixedBy ρ H) N
  have h2 := map_fixedBy_mk_eq_fixedBy_quotientAction ρ N hN hcop H
  rw [h2] at h1
  rw [h1, Nat.mul_comm]

/-! ## The action restricted to an invariant normal subgroup -/

/-- The action of `F` on an `F`-invariant normal subgroup `N ≤ M`, transported from `ρ`. -/
noncomputable def restrictAction {F M : Type*} [Group F] [Group M] (ρ : F →* MulAut M)
    (N : Subgroup M) (hN : ∀ g : F, N.map (ρ g) = N) : F →* MulAut ↥N where
  toFun g :=
    { toFun := fun x => ⟨ρ g (x : M), by
        have hx : ρ g (x : M) ∈ N.map (ρ g) := Subgroup.mem_map_of_mem (ρ g).toMonoidHom x.2
        rwa [hN g] at hx⟩
      invFun := fun x => ⟨(ρ g).symm (x : M), by
        have hx : (x : M) ∈ N.map (ρ g) := by rw [hN g]; exact x.2
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
        have hval : (ρ g).symm (x : M) = y := by
          rw [← hyx]
          exact MulEquiv.symm_apply_apply (ρ g) y
        rw [hval]
        exact hy⟩
      left_inv := fun x => by
        apply Subtype.ext
        simpa using MulEquiv.apply_symm_apply (ρ g) (x : M)
      right_inv := fun x => by
        apply Subtype.ext
        simpa using MulEquiv.symm_apply_apply (ρ g) (x : M)
      map_mul' := fun x y => Subtype.ext (by
        show ρ g ((x : M) * (y : M)) = ρ g (x : M) * ρ g (y : M)
        rw [map_mul]) }
  map_one' := by
    ext x
    show ρ 1 (x : M) = (x : M)
    rw [map_one]
    rfl
  map_mul' := fun g h => by
    ext x
    show ρ (g * h) (x : M) = ρ g (ρ h (x : M))
    rw [map_mul]
    rfl

/-- Membership in the fixed points of the restricted action. -/
theorem mem_fixedBy_restrictAction {F M : Type*} [Group F] [Group M] (ρ : F →* MulAut M)
    (N : Subgroup M) (hN : ∀ g : F, N.map (ρ g) = N) (H : Subgroup F) (x : ↥N) :
    x ∈ fixedBy (restrictAction ρ N hN) H ↔ (x : M) ∈ fixedBy ρ H := by
  rw [mem_fixedBy, mem_fixedBy]
  constructor
  · intro h g hg
    have h' := h g hg
    exact congrArg Subtype.val h'
  · intro h g hg
    apply Subtype.ext
    exact h g hg

/-- The cardinality of the fixed points of the restricted action. -/
theorem card_fixedBy_restrictAction {F M : Type*} [Group F] [Group M] (ρ : F →* MulAut M)
    (N : Subgroup M) (hN : ∀ g : F, N.map (ρ g) = N) (H : Subgroup F) :
    Nat.card ↥(fixedBy (restrictAction ρ N hN) H) = Nat.card ↥(fixedBy ρ H ⊓ N) := by
  have hiff : ∀ x : ↥N, x ∈ fixedBy (restrictAction ρ N hN) H ↔ (x : M) ∈ fixedBy ρ H :=
    mem_fixedBy_restrictAction ρ N hN H
  refine Nat.card_congr ?_
  refine
    { toFun := fun x => ⟨(x.1 : M), Subgroup.mem_inf.mpr ⟨(hiff x.1).mp x.2, x.1.2⟩⟩
      invFun := fun y => ⟨⟨(y.1 : M), (Subgroup.mem_inf.mp y.2).2⟩,
        (hiff ⟨(y.1 : M), (Subgroup.mem_inf.mp y.2).2⟩).mpr (Subgroup.mem_inf.mp y.2).1⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun y => by ext; rfl }

/-- `|K| · |P| = |K ⊔ P|` when `P` normalises `K` and `K ⊓ P = ⊥`. -/
theorem card_mul_card_sup {F : Type*} [Group F] (K P : Subgroup F)
    (hsup : K ⊔ P = ⊤)
    (hnorm : ∀ g ∈ P, ∀ k ∈ K, g * k * g⁻¹ ∈ K) (hdisj : K ⊓ P = ⊥) :
    Nat.card K * Nat.card P = Nat.card ↥(K ⊔ P) := by
  have hc : Subgroup.IsComplement' K P := IsComplementOf K P hsup hnorm hdisj
  have h1 : Nat.card ↥K * Nat.card ↥P = Nat.card F := hc.card_mul_card
  have h2 : Nat.card ↥(K ⊔ P) = Nat.card F := by
    rw [hsup]
    exact Subgroup.card_top
  rw [h1, h2]

/-! ## The induction -/

/-- **Wielandt's counting formula, Frobenius case, for solvable `M` with `C_M(K) = 1`.**
Assuming the `F`-simple (elementary abelian) case `hbase`, the formula holds for every finite
solvable `M`. -/
theorem frobeniusProduct_of_fsimple {F : Type u} [Group F] [Fintype F] {p : ℕ} (hp : p.Prime)
    (K P : Subgroup F) (hsup : K ⊔ P = ⊤) (hcardP : Nat.card P = p)
    (hnorm : ∀ g ∈ P, ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hTI : ∀ k ∈ K, k ≠ 1 → P ⊓ P.map (MulAut.conj k⁻¹).toMonoidHom = ⊥)
    (hbase : ∀ (q : ℕ) [Fact q.Prime] (M : Type u) [CommGroup M] [Finite M],
      (∀ m : M, m ^ q = 1) → (ρ : F →* MulAut M) → ¬ q ∣ Nat.card F →
      (∀ N : Subgroup M, (∀ g : F, N.map (ρ g) = N) → N = ⊥ ∨ N = ⊤) →
      (∀ m : M, (∀ k ∈ K, (ρ k) m = m) → m = 1) →
      (Nat.card (fixedBy ρ P)) ^ (Nat.card P * Nat.card K) * (Nat.card (fixedBy ρ K)) ^ Nat.card K
        = (Nat.card (fixedBy ρ ⊤)) ^ (Nat.card P * Nat.card K) * (Nat.card M) ^ Nat.card K)
    (M : Type u) [Group M] [Finite M] [Group.IsSolvable M] (ρ : F →* MulAut M)
    (hcop : Nat.Coprime (Nat.card F) (Nat.card M))
    (hCK : ∀ m : M, (∀ k ∈ K, (ρ k) m = m) → m = 1) :
    Nat.card M = (Nat.card (fixedBy ρ P)) ^ Nat.card P := by
  have key : ∀ n, ∀ (M : Type u) [Group M] [Finite M] [Group.IsSolvable M], Nat.card M = n →
      ∀ (ρ : F →* MulAut M), Nat.Coprime (Nat.card F) (Nat.card M) →
      (∀ m : M, (∀ k ∈ K, (ρ k) m = m) → m = 1) →
      Nat.card M = (Nat.card (fixedBy ρ P)) ^ Nat.card P := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro M _ _ hsol hcardM ρ hcop hCK
      by_cases hnt : Nontrivial M
      · by_cases hsimp : ∃ N : Subgroup M,
            N.Normal ∧ (∀ g : F, N.map (ρ g) = N) ∧ N ≠ ⊥ ∧ N ≠ ⊤
        · -- step: reduce to an invariant normal subgroup and its quotient
          obtain ⟨N, hNn, hNin, hNbot, hNtop⟩ := hsimp
          haveI := hNn
          -- cardinality bookkeeping
          have hcardN : Nat.card ↥N < n := by
            rw [← hcardM]
            have hpos : 0 < Nat.card ↥N := Nat.card_pos
            have hidx1 : N.index ≠ 1 := fun h1 => hNtop (Subgroup.index_eq_one.mp h1)
            have hidx0 : N.index ≠ 0 := by
              intro h0
              have h := Subgroup.index_mul_card N
              rw [h0, zero_mul] at h
              exact absurd h.symm (ne_of_gt Nat.card_pos)
            have h2 : 2 ≤ N.index := by omega
            calc Nat.card ↥N = 1 * Nat.card ↥N := (one_mul _).symm
              _ < N.index * Nat.card ↥N := Nat.mul_lt_mul_of_pos_right (by omega) hpos
              _ = Nat.card M := Subgroup.index_mul_card N
          have hcardQ : Nat.card (M ⧸ N) < n := by
            rw [← hcardM]
            have hN2 : 2 ≤ Nat.card ↥N := by
              by_contra hcon
              have hpos : 0 < Nat.card ↥N := Nat.card_pos
              have h1 : Nat.card ↥N = 1 := by omega
              haveI : Subsingleton ↥N := (Nat.card_eq_one_iff_unique.mp h1).1
              obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hNbot
              exact ha1 (Subsingleton.elim a 1)
            have hpos : 0 < Nat.card (M ⧸ N) := Nat.card_pos
            calc Nat.card (M ⧸ N) = Nat.card (M ⧸ N) * 1 := (mul_one _).symm
              _ < Nat.card (M ⧸ N) * Nat.card ↥N := Nat.mul_lt_mul_of_pos_left (by omega) hpos
              _ = Nat.card M := (Subgroup.card_eq_card_quotient_mul_card_subgroup N).symm
          -- the induction hypothesis on `N`
          have hcopN : Nat.Coprime (Nat.card F) (Nat.card ↥N) :=
            hcop.coprime_dvd_right (Subgroup.card_subgroup_dvd_card N)
          have hCKN : ∀ x : ↥N, (∀ k ∈ K, (restrictAction ρ N hNin k) x = x) → x = 1 := by
            intro x hx
            apply Subtype.ext
            refine hCK (x : M) fun k hk => ?_
            exact congrArg Subtype.val (hx k hk)
          have ihN : Nat.card ↥N =
              (Nat.card (fixedBy (restrictAction ρ N hNin) P)) ^ Nat.card P :=
            ih (Nat.card ↥N) hcardN ↥N rfl (restrictAction ρ N hNin) hcopN hCKN
          -- the induction hypothesis on `M ⧸ N`
          have hcopQ : Nat.Coprime (Nat.card F) (Nat.card (M ⧸ N)) :=
            hcop.coprime_dvd_right ⟨Nat.card ↥N, by
              rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, mul_comm]⟩
          have hCKQ : ∀ x : M ⧸ N,
              (∀ k ∈ K, (quotientAction ρ N hNin k) x = x) → x = 1 := by
            have hsp := coprimeSplit ρ N hNin hcop K
            have h1 : Nat.card ↥(fixedBy ρ K) = 1 := by
              rw [(Subgroup.eq_bot_iff_forall (fixedBy ρ K)).mpr (fun m hm => hCK m hm)]
              simp
            have h2 : Nat.card ↥(fixedBy ρ K ⊓ N) = 1 := by
              rw [(Subgroup.eq_bot_iff_forall (fixedBy ρ K ⊓ N)).mpr
                (fun m hm => hCK m (Subgroup.mem_inf.mp hm).1)]
              simp
            rw [h1, h2, one_mul] at hsp
            haveI : Subsingleton ↥(fixedBy (quotientAction ρ N hNin) K) :=
              (Nat.card_eq_one_iff_unique.mp hsp.symm).1
            intro x hx
            exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ :
              ↥(fixedBy (quotientAction ρ N hNin) K)) 1)
          have ihQ : Nat.card (M ⧸ N) =
              (Nat.card (fixedBy (quotientAction ρ N hNin) P)) ^ Nat.card P :=
            ih (Nat.card (M ⧸ N)) hcardQ (M ⧸ N) rfl (quotientAction ρ N hNin) hcopQ hCKQ
          -- combine
          have hsp := coprimeSplit ρ N hNin hcop P
          have hres := card_fixedBy_restrictAction ρ N hNin P
          calc Nat.card M = Nat.card (M ⧸ N) * Nat.card ↥N :=
                Subgroup.card_eq_card_quotient_mul_card_subgroup N
            _ = (Nat.card (fixedBy (quotientAction ρ N hNin) P)) ^ Nat.card P *
                (Nat.card (fixedBy (restrictAction ρ N hNin) P)) ^ Nat.card P := by
                  rw [ihQ, ihN]
            _ = (Nat.card (fixedBy (quotientAction ρ N hNin) P) *
                Nat.card (fixedBy (restrictAction ρ N hNin) P)) ^ Nat.card P :=
                  (mul_pow _ _ _).symm
            _ = (Nat.card (fixedBy (quotientAction ρ N hNin) P) *
                Nat.card ↥(fixedBy ρ P ⊓ N)) ^ Nat.card P := by rw [hres]
            _ = (Nat.card ↥(fixedBy ρ P ⊓ N) *
                Nat.card (fixedBy (quotientAction ρ N hNin) P)) ^ Nat.card P := by
                  rw [Nat.mul_comm]
            _ = (Nat.card (fixedBy ρ P)) ^ Nat.card P := by rw [← hsp]
        · -- base: `M` is `F`-simple, hence elementary abelian
          have hsimple_prop : ∀ N : Subgroup M, N.Normal →
              (∀ g : F, N.map (ρ g) = N) → N = ⊥ ∨ N = ⊤ := by
            intro N hNn hNin
            by_contra hc
            rw [not_or] at hc
            exact hsimp ⟨N, hNn, hNin, hc.1, hc.2⟩
          have hcommchar : (commutator M).Characteristic :=
            Subgroup.commutator_characteristic ⊤ ⊤
          have hcomminv : ∀ g : F, (commutator M).map (ρ g) = commutator M := by
            intro g
            refine le_antisymm ?_ (Subgroup.characteristic_iff_le_map.mp hcommchar (ρ g))
            have hle : commutator M ≤ (commutator M).map (ρ g).symm.toMonoidHom :=
              Subgroup.characteristic_iff_le_map.mp hcommchar (ρ g).symm
            calc (commutator M).map (ρ g)
                ≤ ((commutator M).map (ρ g).symm.toMonoidHom).map (ρ g).toMonoidHom :=
                  Subgroup.map_mono hle
              _ = (commutator M).map ((ρ g).toMonoidHom.comp
                    (ρ g).symm.toMonoidHom) :=
                  Subgroup.map_map (commutator M) (ρ g).toMonoidHom (ρ g).symm.toMonoidHom
              _ = (commutator M).map (MonoidHom.id M) := by
                  congr 1
                  ext x
                  simp
              _ = commutator M := Subgroup.map_id _
          have hcomm : IsMulCommutative M := by
            have hcases : commutator M = ⊥ ∨ commutator M = ⊤ :=
              hsimple_prop (commutator M) inferInstance hcomminv
            rcases hcases with hb | ht
            · exact (commutator_eq_bot_iff M).mp hb
            · exact absurd ht (ne_of_lt (Group.IsSolvable.commutator_lt_top_of_nontrivial M))
          letI : CommGroup M :=
            { ‹Group M› with mul_comm := fun a b => hcomm.is_comm.comm a b }
          obtain ⟨q, hqprime, hqM⟩ := Nat.exists_prime_and_dvd (n := Nat.card M) (by
            intro h1
            exact (not_subsingleton_iff_nontrivial.mpr hnt) (Nat.card_eq_one_iff_unique.mp h1).1)
          haveI : Fact q.Prime := ⟨hqprime⟩
          let powq : M →* M :=
            { toFun := fun x => x ^ q
              map_one' := by simp
              map_mul' := fun a b => Commute.mul_pow (hcomm.is_comm.comm a b) q }
          have hpoweq : ∀ x : M, powq x = x ^ q := fun x => rfl
          have hKin : ∀ g : F, (Subgroup.map powq ⊤).map (ρ g) = Subgroup.map powq ⊤ := by
            intro g
            have hcomp : (ρ g : M →* M).comp powq =
                powq.comp (ρ g : M →* M) := by
              ext x
              simp only [MonoidHom.comp_apply, hpoweq, map_pow]
            rw [Subgroup.map_map, hcomp,
              ← MonoidHom.range_eq_map (powq.comp (ρ g : M →* M)),
              MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (ρ g).surjective]
          have hrange : Subgroup.map powq ⊤ = ⊥ ∨ Subgroup.map powq ⊤ = ⊤ :=
            hsimple_prop (Subgroup.map powq ⊤) inferInstance hKin
          have hexp : ∀ m : M, m ^ q = 1 := by
            intro m
            rcases hrange with hb | ht
            · have hm : m ^ q ∈ Subgroup.map powq ⊤ := ⟨m, trivial, by rw [hpoweq]⟩
              rw [hb] at hm
              simpa using hm
            · exfalso
              have hrt : powq.range = ⊤ := by
                rw [← Subgroup.map_top powq]
                exact ht
              have hsurj : Function.Surjective powq := MonoidHom.range_eq_top.mp hrt
              have hinj : Function.Injective powq :=
                Finite.injective_iff_surjective.mpr hsurj
              obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' q hqM
              have hxq : x ^ q = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
              have hx1 : x ≠ 1 := by
                intro h1
                rw [h1, orderOf_one] at hx
                exact hqprime.ne_one hx.symm
              exact hx1 (hinj (by rw [hpoweq, hpoweq, hxq, one_pow]))
          have hqF : ¬ q ∣ Nat.card F := by
            intro hdvd
            have hdvd := Nat.dvd_gcd hdvd hqM
            rw [hcop.gcd_eq_one] at hdvd
            exact hqprime.ne_one (Nat.dvd_one.mp hdvd)
          have hsimple_child : ∀ N : Subgroup M, (∀ g : F, N.map (ρ g) = N) →
              N = ⊥ ∨ N = ⊤ :=
            fun N hNin => hsimple_prop N inferInstance hNin
          have hprod := hbase q M hexp ρ hqF hsimple_child hCK
          have hbK : Nat.card ↥(fixedBy ρ K) = 1 := by
            rw [(Subgroup.eq_bot_iff_forall (fixedBy ρ K)).mpr (fun m hm => hCK m hm)]
            simp
          have hbT : Nat.card ↥(fixedBy ρ ⊤) = 1 := by
            rw [(Subgroup.eq_bot_iff_forall (fixedBy ρ ⊤)).mpr (fun m hm => hCK m (fun k _ => hm k trivial))]
            simp
          rw [hbK, hbT] at hprod
          have hKne : Nat.card K ≠ 0 := ne_of_gt Nat.card_pos
          have hpow : (Nat.card (fixedBy ρ P) ^ Nat.card P) ^ Nat.card K =
              (Nat.card M) ^ Nat.card K := by
            rw [← pow_mul]
            have h := hprod
            simpa [hcardP] using h
          exact (Nat.pow_left_injective hKne hpow).symm
      · -- `M` is trivial
        haveI : Subsingleton M := not_nontrivial_iff_subsingleton.mp hnt
        have h1 : Nat.card M = 1 := Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
        have h2 : Nat.card ↥(fixedBy ρ P) = 1 :=
          Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
        rw [h1, h2, one_pow]
  exact key (Nat.card M) M rfl ρ hcop hCK

end Work.BSLit.Wielandt
