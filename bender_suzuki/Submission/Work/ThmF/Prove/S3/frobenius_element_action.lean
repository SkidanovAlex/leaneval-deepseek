import Mathlib
import Submission.Work.ThmF.ChV12.prop3
import Submission.Work.ThmF.ChV12.prop3_frobenius_power
import Submission.Work.ThmF.ChV12.prop3_card_fixed_pow
import Submission.Work.ThmF.Prove.step1

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.Prove.S3.frobenius_element_action`

Peterfalvi II, Ch. V §3 (step (2)): if `P ≤ V = C_D(t)` has prime order with `P ∩ W = 1` and
`|Q₀| = 2 ^ |P|`, then some `a ∈ P` acts on `K = J(D,t)` by *squaring*:
`a k a⁻¹ = k ^ 2` for every `k ∈ K`.

`Ch. V §1 Prop. 3` (`Work.ThmF.ChV12.prop3`) identifies `Q₀ = ⟨Inv H⟩` with the additive group of
a finite field `F` of cardinality `|Q₀| = 2 ^ p`, `K` with `Fˣ`, and `V = C_D(t)` with a group of
ring automorphisms of `F` with kernel `W = C_V(K)`.  Consequently:

* every `v ∈ V` acts on `K` through a ring automorphism `ρ v` of `F`, so that
  `κ (v k v⁻¹) = ρ v (κ k)` (`ksub_conj_action_eq`);
* every ring automorphism of `F = 𝔽_{2^p}` is a power of the Frobenius (`ringAut_charTwo_eq_frobenius_pow`),
  so the image `A = ρ(P) ≤ Aut F` of the prime-order group `P ∩ W = 1` is a subgroup of
  `⟨Frobenius⟩`, which has order `p` since `p` is prime and `|F| = 2^p ≥ 4`
  (`frobenius_mem_of_card_eq_prime`);
* hence `A = ⟨Frobenius⟩` and the Frobenius `x ↦ x ^ 2` is `ρ a` for some `a ∈ P`, giving
  `a k a⁻¹ = k ^ 2`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.Prove.S3

open Classical Submission.Blueprint

/-! ## A finite field of cardinality `2 ^ p` has characteristic `2` -/

/-- A finite field with `Nat.card F = 2 ^ p` has characteristic `2`: its characteristic `q` is a
prime, `Nat.card F = q ^ k`, and `q ∣ 2 ^ p` forces `q = 2`. -/
theorem charP_two_of_card_eq_two_pow {F : Type} [Field F] [Fintype F] {p : ℕ}
    (hF : Nat.card F = 2 ^ p) : CharP F 2 := by
  obtain ⟨q, hcharq⟩ := CharP.exists F
  obtain ⟨k, hqprime, hkcard⟩ := FiniteField.card F q
  have hq2 : q = 2 := by
    have hqk : q ^ (k : ℕ) = 2 ^ p := by
      rw [← hkcard, Fintype.card_eq_nat_card, hF]
    have hdvd : q ∣ 2 ^ p := by rw [← hqk]; exact dvd_pow_self q k.ne_zero
    have hdvd2 : q ∣ 2 := hqprime.dvd_of_dvd_pow hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
    · exact absurd h hqprime.ne_one
    · exact h
  exact hq2 ▸ hcharq

/-! ## A prime-order subgroup of `Aut 𝔽_{2^p}` contains the Frobenius -/

/-- Every ring automorphism of a finite field `F` of characteristic `2` is an iterate of the
Frobenius `x ↦ x ^ 2` (that is `Work.ThmF.ChV12.ringAut_charTwo_eq_frobenius_pow`), so the
subgroup `⟨x ↦ x ^ 2⟩ ≤ F ≃+* F` has order `p` when `Nat.card F = 2 ^ p` with `p` prime.  Any
subgroup `A` of order `p` therefore *equals* `⟨x ↦ x ^ 2⟩` and contains the squaring map. -/
theorem frobenius_mem_of_card_eq_prime {F : Type} [Field F] [Fintype F] {p : ℕ} (hp : p.Prime)
    (hF : Nat.card F = 2 ^ p) {A : Subgroup (F ≃+* F)} (hA : Nat.card A = p) :
    ∃ σ ∈ A, ∀ x : F, σ x = x ^ 2 := by
  haveI : CharP F 2 := charP_two_of_card_eq_two_pow hF
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (F ≃+* F) :=
    Finite.of_injective (fun e : F ≃+* F => (⇑e : F → F))
      (fun a b h => RingEquiv.ext (fun x => congrFun h x))
  let φ : F ≃+* F := frobeniusEquiv F 2
  have hφapply : ∀ x : F, φ x = x ^ 2 := fun x => frobeniusEquiv_def F 2 x
  have hpow : ∀ n : ℕ, ∀ x : F, (φ ^ n) x = x ^ 2 ^ n := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
        intro x
        rw [pow_succ, RingAut.mul_apply, ih, hφapply, ← pow_mul, Nat.mul_comm, ← pow_succ]
  have hxpow : ∀ x : F, x ^ 2 ^ p = x := by
    intro x
    by_cases hx : x = 0
    · subst hx; simp
    · have hcard : Fintype.card Fˣ = 2 ^ p - 1 := by
        rw [Fintype.card_units, Fintype.card_eq_nat_card, hF]
      have hunit : (Units.mk0 x hx) ^ (2 ^ p - 1) = 1 := by
        rw [← hcard]; exact pow_card_eq_one
      have hval : x ^ (2 ^ p - 1) = 1 := by
        have h := congrArg (fun u : Fˣ => (u : F)) hunit
        simpa using h
      calc x ^ 2 ^ p = x ^ (2 ^ p - 1 + 1) := by rw [Nat.sub_add_cancel (Nat.one_le_two_pow)]
        _ = x ^ (2 ^ p - 1) * x ^ 1 := by rw [pow_add]
        _ = x := by rw [hval, one_mul, pow_one]
  have hφp : φ ^ p = 1 := by
    ext x
    rw [hpow p x, hxpow x, RingAut.one_apply]
  have hφne : φ ≠ 1 := by
    intro h1
    have hcontra : ∀ x : F, x = 0 ∨ x = 1 := by
      intro x
      by_cases hx : x = 0
      · exact Or.inl hx
      · refine Or.inr ?_
        have h : φ x = (1 : F ≃+* F) x := by rw [h1]
        rw [RingAut.one_apply, hφapply] at h
        exact mul_left_cancel₀ hx (by rw [← pow_two, h, mul_one])
    have hsub : (Set.univ : Set F) ⊆ ({0, 1} : Set F) := by
      intro x _
      rcases hcontra x with h | h <;> simp [h]
    have hle : Nat.card F ≤ 2 := by
      have h1' : (Set.univ : Set F).ncard ≤ ({0, 1} : Set F).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_univ] at h1'
      have h2' : ({0, 1} : Set F).ncard ≤ 2 := by
        rw [show ({0, 1} : Set F) = {0} ∪ {1} from rfl]
        refine le_trans (Set.ncard_union_le _ _) ?_
        rw [Set.ncard_singleton, Set.ncard_singleton]
      exact le_trans h1' h2'
    have h4 : 4 ≤ Nat.card F := by
      rw [hF]
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp.two_le
    omega
  have horder : orderOf φ = p := orderOf_eq_prime hφp hφne
  have hAle : A ≤ Subgroup.zpowers φ := by
    intro σ hσ
    obtain ⟨i, hi⟩ := Work.ThmF.ChV12.ringAut_charTwo_eq_frobenius_pow σ
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨(i : ℤ), ?_⟩
    rw [zpow_natCast]
    ext x
    rw [hpow i x, hi x]
  have hAcard : Nat.card ↥(Subgroup.zpowers φ) = p := by
    rw [Nat.card_zpowers]; exact horder
  have hEq : A = Subgroup.zpowers φ := Subgroup.eq_of_le_of_card_ge hAle (by rw [hAcard, hA])
  exact ⟨φ, hEq ▸ Subgroup.mem_zpowers φ, fun x => hφapply x⟩

/-! ## `κ` converts conjugation by `V = C_D(t)` into the field automorphism `ρ` -/

/-- Conjugation by `v ∈ V = centD H t` on `K = Ksub H t` corresponds, under the isomorphism
`κ : K ≃* Fˣ` of Ch. V §1 Prop. 3, to the field automorphism `ρ v`.  The proof evaluates the
two conjugation actions at the element `x₀ ∈ Q₀` with `e x₀ = 1 ∈ F` and uses that
`(v k v⁻¹)(v x₀ v⁻¹)(v k v⁻¹)⁻¹ = v (k x₀ k⁻¹) v⁻¹`. -/
theorem ksub_conj_action_eq {G : Type} [Group G] {H : Subgroup G} {t : G} {F : Type} [Field F]
    (e : ↥(Work.ThmF.Q0sub H) ≃* Multiplicative F)
    (κ : ↥(Work.ThmF.Ksub H t) ≃* Fˣ)
    (ρ : ↥(centD H t) →* (F ≃+* F))
    (hactK : ∀ (k : ↥(Work.ThmF.Ksub H t)) (x : ↥(Work.ThmF.Q0sub H))
      (hx : (k : G) * x * (k : G)⁻¹ ∈ Work.ThmF.Q0sub H),
      Multiplicative.toAdd (e ⟨(k : G) * x * (k : G)⁻¹, hx⟩) = (κ k : F) * Multiplicative.toAdd (e x))
    (hactV : ∀ (v : ↥(centD H t)) (x : ↥(Work.ThmF.Q0sub H))
      (hx : (v : G) * x * (v : G)⁻¹ ∈ Work.ThmF.Q0sub H),
      Multiplicative.toAdd (e ⟨(v : G) * x * (v : G)⁻¹, hx⟩) = (ρ v) (Multiplicative.toAdd (e x))) :
    ∀ (v : ↥(centD H t)) (k : ↥(Work.ThmF.Ksub H t))
      (hk : (v : G) * k * (v : G)⁻¹ ∈ Work.ThmF.Ksub H t),
      (κ ⟨(v : G) * k * (v : G)⁻¹, hk⟩ : F) = ρ v (κ k) := by
  intro v k hk
  -- the point `x₀` with `e x₀ = 1`
  let x₀ : ↥(Work.ThmF.Q0sub H) := e.symm (Multiplicative.ofAdd (1 : F))
  have hx₀ : Multiplicative.toAdd (e x₀) = 1 := by
    simp [x₀]
  -- the two intermediate points, and the two ways of reaching `v k x₀ k⁻¹ v⁻¹`
  have hy : (k : G) * (x₀ : G) * (k : G)⁻¹ ∈ Work.ThmF.Q0sub H :=
    Work.ThmF.ChV12.conj_mem_Q0sub (Work.ThmF.ChV12.Ksub_le_H H t k.2) x₀.2
  have hyval : Multiplicative.toAdd (e ⟨(k : G) * (x₀ : G) * (k : G)⁻¹, hy⟩) = (κ k : F) := by
    rw [hactK k x₀ hy, hx₀, mul_one]
  have hx' : (v : G) * (x₀ : G) * (v : G)⁻¹ ∈ Work.ThmF.Q0sub H :=
    Work.ThmF.ChV12.conj_mem_Q0sub (Work.ThmF.ChV12.centD_le_H H t v.2) x₀.2
  have hx'val : Multiplicative.toAdd (e ⟨(v : G) * (x₀ : G) * (v : G)⁻¹, hx'⟩) = 1 := by
    rw [hactV v x₀ hx', hx₀, map_one]
  let k' : ↥(Work.ThmF.Ksub H t) := ⟨(v : G) * (k : G) * (v : G)⁻¹, hk⟩
  have hz₁ : (k' : G) * ((v : G) * (x₀ : G) * (v : G)⁻¹) * (k' : G)⁻¹ ∈ Work.ThmF.Q0sub H :=
    Work.ThmF.ChV12.conj_mem_Q0sub (Work.ThmF.ChV12.Ksub_le_H H t k'.2) hx'
  have hz₂ : (v : G) * ((k : G) * (x₀ : G) * (k : G)⁻¹) * (v : G)⁻¹ ∈ Work.ThmF.Q0sub H :=
    Work.ThmF.ChV12.conj_mem_Q0sub (Work.ThmF.ChV12.centD_le_H H t v.2) hy
  have hz₁val : Multiplicative.toAdd
      (e ⟨(k' : G) * ((v : G) * (x₀ : G) * (v : G)⁻¹) * (k' : G)⁻¹, hz₁⟩) = (κ k' : F) := by
    rw [hactK k' ⟨(v : G) * (x₀ : G) * (v : G)⁻¹, hx'⟩ hz₁, hx'val, mul_one]
  have hz₂val : Multiplicative.toAdd
      (e ⟨(v : G) * ((k : G) * (x₀ : G) * (k : G)⁻¹) * (v : G)⁻¹, hz₂⟩) = ρ v (κ k) := by
    rw [hactV v ⟨(k : G) * (x₀ : G) * (k : G)⁻¹, hy⟩ hz₂, hyval]
  have heq : (⟨(k' : G) * ((v : G) * (x₀ : G) * (v : G)⁻¹) * (k' : G)⁻¹, hz₁⟩ :
        ↥(Work.ThmF.Q0sub H))
      = ⟨(v : G) * ((k : G) * (x₀ : G) * (k : G)⁻¹) * (v : G)⁻¹, hz₂⟩ := by
    apply Subtype.ext
    show (v : G) * (k : G) * (v : G)⁻¹ * ((v : G) * (x₀ : G) * (v : G)⁻¹)
        * ((v : G) * (k : G) * (v : G)⁻¹)⁻¹
      = (v : G) * ((k : G) * (x₀ : G) * (k : G)⁻¹) * (v : G)⁻¹
    group
  have hfin : (κ k' : F) = ρ v (κ k) := by
    rw [← hz₁val, heq, hz₂val]
  exact hfin

/-! ## The main result -/

theorem frobenius_element_action {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {P : Subgroup G} (h : Submission.Blueprint.IsSplitRankOne H Q t) (hcomm : ∀ u ∈ Submission.Blueprint.involutions (H : Set G), ∀ v ∈ Submission.Blueprint.involutions (H : Set G), u * v = v * u) (hKset : ∀ k ∈ Work.ThmF.Ksub H t, k ∈ Work.ThmF.Kset H t) (hKcyc : IsCyclic ↥(Work.ThmF.Ksub H t)) (hKn : ((Work.ThmF.Ksub H t).subgroupOf (Submission.Blueprint.twoPoint H t)).Normal) (hreg : ∀ a ∈ Submission.Blueprint.involutions (H : Set G), ∀ b ∈ Submission.Blueprint.involutions (H : Set G), ∃! k, k ∈ Work.ThmF.Kset H t ∧ k * a * k⁻¹ = b) (s : G) (hs : s ∈ Submission.Blueprint.involutions (H : Set G)) (hV' : Submission.Blueprint.centD H t = Submission.Blueprint.twoPoint H t ⊓ Subgroup.centralizer ({s} : Set G)) (hPV : P ≤ Submission.Blueprint.centD H t) (hPW : P ⊓ Work.ThmF.W H t = ⊥) (hPcard : (Nat.card P).Prime) (hQ0card : Nat.card ↥(Work.ThmF.Q0sub H) = 2 ^ Nat.card P) : ∃ a ∈ P, ∀ k ∈ Work.ThmF.Ksub H t, a * k * a⁻¹ = k ^ 2 := by
  classical
  -- `Ksub H t = Kset H t`
  have hKsub : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t :=
    Set.Subset.antisymm (fun k hk => hKset k hk) (Work.ThmF.Kset_le_Ksub H t)
  -- Ch. V §1 Prop. 3: the field structure on `Q₀` and the action of `V = centD H t`
  obtain ⟨F, hFld, hFint, e, κ, ρ, hcardF, hactK, hactV, hker⟩ :=
    Work.ThmF.ChV12.prop3 H Q t h hcomm hKsub hKcyc hKn hreg s hs hV'
  letI : Field F := hFld
  letI : Fintype F := hFint
  have hFcard : Nat.card F = 2 ^ Nat.card P := by rw [hcardF, hQ0card]
  haveI : CharP F 2 := charP_two_of_card_eq_two_pow hFcard
  -- the conjugation action of `V` on `K` is the field action of `ρ`
  have hstr := ksub_conj_action_eq (H := H) (t := t) e κ ρ hactK hactV
  -- the homomorphism `P → Aut F` and the cardinality of its image
  let ψ : ↥P →* ↥(Submission.Blueprint.centD H t) :=
    { toFun := fun p => ⟨(p : G), hPV p.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl }
  let φP : ↥P →* (F ≃+* F) := ρ.comp ψ
  have hφPval : ∀ p : ↥P, φP p = ρ ⟨(p : G), hPV p.2⟩ := fun p => rfl
  have hφPinj : Function.Injective φP := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [eq_bot_iff]
    intro p hp
    rw [MonoidHom.mem_ker] at hp
    rw [Subgroup.mem_bot]
    have h2 : ψ p ∈ ρ.ker := by
      rw [MonoidHom.mem_ker]
      rw [show ψ p = ⟨(p : G), hPV p.2⟩ from rfl, ← hφPval p]
      exact hp
    rw [hker, Subgroup.mem_subgroupOf] at h2
    have h3 : (p : G) ∈ P ⊓ Work.ThmF.W H t := ⟨p.2, h2⟩
    rw [hPW, Subgroup.mem_bot] at h3
    exact Subtype.ext h3
  have hAcard : Nat.card ↥(φP.range) = Nat.card P := by
    rw [show φP.range = Subgroup.map φP ⊤ from MonoidHom.range_eq_map φP,
      Subgroup.card_map_of_injective hφPinj (K := ⊤), Subgroup.card_top]
  -- the Frobenius squaring map lies in `φP.range`
  obtain ⟨σ, hσmem, hσsq⟩ :=
    frobenius_mem_of_card_eq_prime hPcard hFcard (A := φP.range) (by rw [hAcard])
  obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp hσmem
  refine ⟨(p : G), p.2, ?_⟩
  intro k hk
  have hk' : (p : G) * k * (p : G)⁻¹ ∈ Work.ThmF.Ksub H t :=
    Work.ThmF.ChV12.conj_mem_Ksub H t (hPV p.2) k hk
  -- `κ` of the conjugate
  have h1 : (κ ⟨(p : G) * k * (p : G)⁻¹, hk'⟩ : F) = ρ ⟨(p : G), hPV p.2⟩ (κ ⟨k, hk⟩) :=
    hstr ⟨(p : G), hPV p.2⟩ ⟨k, hk⟩ hk'
  have h2 : ρ ⟨(p : G), hPV p.2⟩ (κ ⟨k, hk⟩) = (κ ⟨k, hk⟩ : F) ^ 2 := by
    rw [← hφPval p, hp]
    exact hσsq (κ ⟨k, hk⟩)
  have h3 : (κ ⟨k ^ 2, (Work.ThmF.Ksub H t).pow_mem hk 2⟩ : F) = (κ ⟨k, hk⟩ : F) ^ 2 := by
    have := map_pow κ (⟨k, hk⟩ : ↥(Work.ThmF.Ksub H t)) 2
    have h4 := congrArg (fun u : Fˣ => (u : F)) this
    simpa [Units.val_pow_eq_pow_val] using h4
  have hκeq : κ ⟨(p : G) * k * (p : G)⁻¹, hk'⟩
      = κ ⟨k ^ 2, (Work.ThmF.Ksub H t).pow_mem hk 2⟩ := by
    apply Units.ext
    rw [h1, h2, h3]
  have h5 : (⟨(p : G) * k * (p : G)⁻¹, hk'⟩ : ↥(Work.ThmF.Ksub H t))
      = ⟨k ^ 2, (Work.ThmF.Ksub H t).pow_mem hk 2⟩ := κ.injective hκeq
  exact congrArg Subtype.val h5

end Work.ThmF.Prove.S3
