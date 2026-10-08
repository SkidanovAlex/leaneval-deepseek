/-
# The Corollary of Peterfalvi I Ch. III §1 Lemma 2 (p.174)

`E ≤ W` finite, `π` the set of prime divisors of `|E|`, `E` solvable, and for every `p ∈ π` and
every `p`-subgroup `U ≠ 1` of `E`

`N_W(U) = O_{π'}(C_W(U)) · N_E(U)`  (`Work.NormalComplement.ControlHyp E W`).

Then `E` is a Hall subgroup of `W` and has a normal complement in `W`.

Route (the paper's): `E` is Hall in `W` (apply the hypothesis to a Sylow `p` of `E` together with
`isSylowIn_of_sylowIn_normalizer`); if `E ≠ 1` one picks a prime `p ∣ |E : [E,E]|` and a `p`-element
`y ∈ E ∖ [E,E]` (`primes_of_abelianization`), shows `E` is `p`-control in `W`
(`pcontrol_criterion`), and concludes `y ∉ O^p(W)` by the transfer lemma
(`pcontrol_transfer_aux`, whose product-form hypothesis is `pcontrol_prod_aux`).  Then
`W₁ = O^p(W)` is a proper normal subgroup of `W` with `W = W₁ ⊔ E`, the hypothesis descends to
`E₁ = E ⊓ W₁ ≤ W₁`, and induction on `|W|` produces a normal complement `N₀` of `E₁` in `W₁`; the
required complement of `E` in `W` is `O_{π'}(W₁) ⊇ N₀`.
-/
import Mathlib
import Submission.Work.NormalComplement.CCDefs
import Submission.Work.NormalComplement.pcontrolProd
import Submission.Work.NormalComplement.pcontrol_transfer
import Submission.Work.NormalComplement.primes_of_abelianization
import Submission.Work.NormalComplement.commutator_ne_of_solvable
import Submission.Work.NormalComplement.notMem_pResidual_sup_commutator
import Submission.Work.NormalComplement.map_pResidual_sup_commutator_subgroupOf
import Submission.Work.NormalComplement.CC.mem_sup_prod

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement

set_option maxHeartbeats 2000000

variable {G : Type} [Group G] [Finite G]

/-! ## Elementary numerical and subgroup lemmas -/

/-- A proper subgroup has strictly smaller order. -/
lemma card_lt_card_of_lt {H K : Subgroup G} (h : H < K) : Nat.card ↥H < Nat.card ↥K := by
  have hdvd : Nat.card ↥H ∣ Nat.card ↥K := by
    rw [← card_subgroupOf_eq H K h.1]
    exact Subgroup.card_subgroup_dvd_card _
  exact lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos hdvd)
    (fun heq => (ne_of_lt h) (Subgroup.eq_of_le_of_card_ge h.1 (le_of_eq heq.symm)))

/-- A divisor of `q ^ n` that is not divisible by the prime `q` is `1`. -/
lemma eq_one_of_dvd_pow_of_not_dvd {q d : ℕ} (hq : q.Prime) {n : ℕ} (hdvd : d ∣ q ^ n)
    (hnd : ¬ q ∣ d) : d = 1 := by
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hq).mp hdvd
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · rwa [hk0, pow_zero] at hk
  · exact absurd (hk ▸ dvd_pow_self q (Nat.pos_iff_ne_zero.mp hkpos)) hnd

/-- The relative index of `O^p(W)` in `W` is a power of `p`. -/
lemma relIndex_pResidual_eq_pow {p : ℕ} [Fact p.Prime] (W : Subgroup G) :
    ∃ n : ℕ, (Work.Grun.pResidual p W).relIndex W = p ^ n := by
  have hmap := Work.Grun.pResidual_eq_map_pResidual p W
  have hsub : (Work.Grun.pResidual p W).subgroupOf W = Work.NPC.Frobenius.pResidual p ↥W := by
    change Subgroup.comap W.subtype (Work.Grun.pResidual p W) = _
    rw [hmap]
    exact Subgroup.comap_map_eq_self_of_injective W.subtype_injective _
  obtain ⟨n, hn⟩ :=
    IsPGroup.exists_card_eq (Work.NPC.Frobenius.isPGroup_quotient_pResidual (G := ↥W) (p := p))
  refine ⟨n, ?_⟩
  show (Subgroup.subgroupOf (Work.Grun.pResidual p W) W).index = p ^ n
  rw [hsub, Subgroup.index_eq_card]
  exact hn

/-! ## `O_{π'}(X)` is characteristic in `X` -/

/-- Conjugation by an element of `N_G(X)` sends `O_{π'}(X)` into itself: the conjugate is again a
normal `π'`-subgroup of `X`. -/
lemma map_conj_piPrimeCoreSub_le {π : Set ℕ} {X : Subgroup G} {b : G}
    (h : b ∈ Subgroup.normalizer (X : Set G)) :
    (piPrimeCoreSub π X).map (MulAut.conj b).toMonoidHom ≤ piPrimeCoreSub π X := by
  set A : Subgroup G := piPrimeCoreSub π X with hA
  set Ab : Subgroup G := A.map (MulAut.conj b).toMonoidHom with hAb
  have hpc : piPrimeCoreSub π X = (Work.Fitting.piCore (fun q => q ∉ π) ↥X).map X.subtype := rfl
  have hAX : A ≤ X := by rw [hA]; exact Subgroup.map_subtype_le _
  have hAnorm : X ≤ Subgroup.normalizer (A : Set G) := by
    rw [hA]; exact piPrimeCoreSub_le_normalizer π X
  have hmapX : X.map (MulAut.conj b).toMonoidHom = X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp h
  have hbinv : b⁻¹ ∈ Subgroup.normalizer (X : Set G) := Subgroup.inv_mem _ h
  have hconjX : ∀ g ∈ X, b⁻¹ * g * b ∈ X := fun g hg =>
    by simpa using (Subgroup.mem_normalizer_iff.mp hbinv g).mp hg
  have hAbnorm : X ≤ Subgroup.normalizer (Ab : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro g hg m hm
    rw [hAb, Subgroup.mem_map] at hm ⊢
    obtain ⟨a, ha, rfl⟩ := hm
    refine ⟨(b⁻¹ * g * b) * a * (b⁻¹ * g * b)⁻¹,
      (Subgroup.le_normalizer_iff.mp hAnorm (b⁻¹ * g * b) (hconjX g hg)) a ha, ?_⟩
    change (MulAut.conj b) ((b⁻¹ * g * b) * a * (b⁻¹ * g * b)⁻¹)
      = g * (MulAut.conj b) a * g⁻¹
    rw [MulAut.conj_apply, MulAut.conj_apply]; group
  have hAbX : Ab ≤ X := by
    rw [hAb]
    exact (Subgroup.map_mono hAX).trans (le_of_eq hmapX)
  have hnormal : (Ab.subgroupOf X).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hAbnorm
  have hispi : Work.Fitting.IsPiNat (fun q => q ∉ π) (Nat.card ↥(Ab.subgroupOf X)) := by
    rw [card_subgroupOf_eq Ab X hAbX, hAb, Subgroup.card_map_of_injective (MulAut.conj b).injective,
      hA, hpc, Subgroup.card_map_of_injective X.subtype_injective]
    exact Work.Fitting.piCore_isPiNat ↥X (fun q => q ∉ π)
  calc Ab = Ab ⊓ X := (inf_of_le_left hAbX).symm
    _ = (Ab.subgroupOf X).map X.subtype := (Subgroup.subgroupOf_map_subtype Ab X).symm
    _ ≤ (Work.Fitting.piCore (fun q => q ∉ π) ↥X).map X.subtype :=
        Subgroup.map_mono (Work.Fitting.le_piCore hnormal hispi)
    _ = piPrimeCoreSub π X := hpc.symm

/-- Conjugation by an element of `N_G(X)` preserves `O_{π'}(X)`. -/
lemma map_conj_piPrimeCoreSub_eq {π : Set ℕ} {X : Subgroup G} {y : G}
    (h : y ∈ Subgroup.normalizer (X : Set G)) :
    (piPrimeCoreSub π X).map (MulAut.conj y).toMonoidHom = piPrimeCoreSub π X := by
  refine le_antisymm (map_conj_piPrimeCoreSub_le h) ?_
  have h2 := map_conj_piPrimeCoreSub_le (π := π) (X := X) (Subgroup.inv_mem _ h)
  calc piPrimeCoreSub π X
      = ((piPrimeCoreSub π X).map (MulAut.conj y⁻¹).toMonoidHom).map
          (MulAut.conj y).toMonoidHom := by
        rw [map_conj_map_conj, mul_inv_cancel]
        ext x
        simp
    _ ≤ (piPrimeCoreSub π X).map (MulAut.conj y).toMonoidHom := Subgroup.map_mono h2

/-! ## The hypothesis in the `O_{p'}` form -/

/-- The Corollary's hypothesis gives `N_W(U) = O_{p'}(C_W(U))·N_E(U)` for every non-trivial
`p`-subgroup `U` of `E`, `p ∈ π`. -/
theorem cc_hnorm {E W : Subgroup G} (hEW : E ≤ W) (hch : ControlHyp E W) {p : ℕ} (hp : p.Prime)
    (hpE : p ∣ Nat.card E) :
    ∀ U : Subgroup G, U ≤ E → U ≠ ⊥ → IsPGroup p U →
      Subgroup.normalizer (U : Set G) ⊓ W =
        pPrimeCoreSub p (Subgroup.centralizer (U : Set G) ⊓ W) ⊔
          (Subgroup.normalizer (U : Set G) ⊓ E) := by
  intro U hUE hUne hUp
  have h := hch p U hp hpE hUE hUne hUp
  have hNW : pPrimeCoreSub p (Subgroup.centralizer (U : Set G) ⊓ W) ⊔
      (Subgroup.normalizer (U : Set G) ⊓ E) = Subgroup.normalizer (U : Set G) ⊓ W := by
    refine le_antisymm ?_ ?_
    · refine sup_le ?_ ?_
      · exact (Subgroup.map_subtype_le _).trans
          (le_inf (inf_le_left.trans (Subgroup.centralizer_le_normalizer (U : Set G)))
            inf_le_right)
      · exact le_inf inf_le_left (inf_le_right.trans hEW)
    · conv_lhs => rw [inf_comm]
      rw [h]
      refine sup_le ?_ ?_
      · conv_lhs => rw [inf_comm]
        exact (piPrimeCoreSub_le_pPrimeCoreSub hp hpE _).trans le_sup_left
      · conv_lhs => rw [inf_comm]
        exact le_sup_right
  exact hNW.symm

/-! ## `E` is a Hall subgroup of `W` -/

/-- **First half of the Corollary**: `E` is a Hall subgroup of `W`. -/
theorem cc_hall {E W : Subgroup G} (hEW : E ≤ W) (hch : ControlHyp E W) :
    ∀ q : ℕ, q.Prime → q ∣ Nat.card E → ¬ q ∣ (E.subgroupOf W).index := by
  intro q hq hqE
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨P, -, hPsyl⟩ := exists_isSylowIn_ge (p := q) (T := ⊥) (X := E) bot_le
    (IsPGroup.of_bot (p := q))
  have hPne : P ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card ↥P = 1 := by rw [hbot]; simp
    have h1 : Nat.card ↥E = (P.subgroupOf E).index * Nat.card ↥P := by
      rw [← Subgroup.index_mul_card (P.subgroupOf E), card_subgroupOf_eq P E hPsyl.2.1]
    have hdvd : q ∣ Nat.card ↥E := hqE
    rw [h1, hcard, mul_one] at hdvd
    exact hPsyl.2.2 hdvd
  have h1 : Subgroup.normalizer (P : Set G) ⊓ W =
      pPrimeCoreSub q (Subgroup.centralizer (P : Set G) ⊓ W) ⊔
        (Subgroup.normalizer (P : Set G) ⊓ E) :=
    cc_hnorm hEW hch hq hqE P hPsyl.2.1 hPne hPsyl.1
  have hPW : IsSylowIn q P W := isSylowIn_of_sylowIn_normalizer hEW hPsyl h1
  intro hdiv
  refine hPW.2.2 ?_
  have hd : q ∣ P.relIndex W := by
    have h := Subgroup.relIndex_mul_relIndex P E W hPsyl.2.1 hEW
    exact h ▸ dvd_mul_of_dvd_right hdiv (P.relIndex E)
  simpa only [Subgroup.relIndex] using hd

/-- Coprimality of `|E|` and `[W : E]` from Hall-ness. -/
theorem cc_coprime {E W : Subgroup G}
    (h : ∀ q : ℕ, q.Prime → q ∣ Nat.card E → ¬ q ∣ (E.subgroupOf W).index) :
    Nat.Coprime (Nat.card E) (E.relIndex W) := by
  show (Nat.card E).gcd (E.relIndex W) = 1
  by_contra hne
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
  exact h q hq (hqd.trans (Nat.gcd_dvd_left _ _)) (hqd.trans (Nat.gcd_dvd_right _ _))

/-! ## The hypothesis descends to `E ⊓ O^p(W) ≤ O^p(W)` -/

/-- `O_{π'}(X) ≤ O^p(W)` for `X ≤ W`: it is a `π'`-group, hence consists of `p'`-elements of `W`
(`p ∈ π`). -/
lemma piPrimeCoreSub_le_pResidual {E W : Subgroup G} {p : ℕ} (hp : p.Prime) (hpE : p ∣ Nat.card E)
    {X : Subgroup G} (hX : X ≤ W) :
    piPrimeCoreSub {q : ℕ | q ∣ Nat.card E} X ≤ Work.Grun.pResidual p W := by
  intro x hx
  have hxA : x ∈ piPrimeCoreSub {q : ℕ | q ∣ Nat.card E} X := hx
  have hxW : x ∈ W := hX (piPrimeCoreSub_le _ _ hx)
  rw [Work.Grun.pResidual, Subgroup.mem_map]
  refine ⟨⟨x, hxW⟩, Subgroup.subset_closure ?_, rfl⟩
  show ¬ p ∣ orderOf ((⟨x, hxW⟩ : ↥W) : G)
  rw [Subgroup.orderOf_coe]
  have hdvd : orderOf (⟨x, hxW⟩ : ↥W) ∣ Nat.card ↥(piPrimeCoreSub {q : ℕ | q ∣ Nat.card E} X) := by
    rw [show orderOf (⟨x, hxW⟩ : ↥W) = orderOf x from (Subgroup.orderOf_coe _).symm]
    exact Subgroup.orderOf_dvd_natCard _ hxA
  exact fun hpd => not_dvd_card_piPrimeCoreSub hp hpE _ (hpd.trans hdvd)

/-- **The hypothesis descends to `E₁ = E ⊓ O^p(W) ≤ O^p(W)`.** -/
theorem cc_controlHyp_inf {E W : Subgroup G} (hEW : E ≤ W) (hch : ControlHyp E W) {p : ℕ}
    (hp : p.Prime) (hpE : p ∣ Nat.card E) :
    ControlHyp (E ⊓ Work.Grun.pResidual p W) (Work.Grun.pResidual p W) := by
  intro q U hq hqE₁ hUE₁ hUne hUq
  set W₁ : Subgroup G := Work.Grun.pResidual p W with hW₁
  set E₁ : Subgroup G := E ⊓ W₁ with hE₁
  set C : Subgroup G := Subgroup.centralizer (U : Set G) with hC
  have hW₁le : W₁ ≤ W := Work.Grun.pResidual_le p W
  have hE₁le : E₁ ≤ E := inf_le_left
  have hcardE₁ : Nat.card ↥E₁ ∣ Nat.card ↥E := by
    rw [← card_subgroupOf_eq E₁ E hE₁le]
    exact Subgroup.card_subgroup_dvd_card _
  have hqE : q ∣ Nat.card E := hqE₁.trans hcardE₁
  set A : Subgroup G := piPrimeCoreSub {r : ℕ | r ∣ Nat.card E} (W ⊓ C) with hA
  set A' : Subgroup G := piPrimeCoreSub {r : ℕ | r ∣ Nat.card E₁} (W₁ ⊓ C) with hA'
  set B : Subgroup G := E ⊓ Subgroup.normalizer (U : Set G) with hB
  -- the hypothesis
  have hAB : Subgroup.normalizer (U : Set G) ⊓ W = A ⊔ B :=
    (inf_comm _ _).trans (hch q U hq hqE (hUE₁.trans hE₁le) hUne hUq)
  have hBnorm : B ≤ Subgroup.normalizer (A : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine map_conj_piPrimeCoreSub_eq (π := {r : ℕ | r ∣ Nat.card E}) ?_
    have hCb : C.map (MulAut.conj b).toMonoidHom = C := map_conj_centralizer_eq hb.2
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
    have h1 : (W ⊓ C : Subgroup G).map (MulAut.conj b).toMonoidHom =
        W.map (MulAut.conj b).toMonoidHom ⊓ C.map (MulAut.conj b).toMonoidHom :=
      Subgroup.map_inf W C _ (MulAut.conj b).injective
    have h2 : W.map (MulAut.conj b).toMonoidHom = W :=
      map_conj_eq_self_of_mem (X := W) (hEW hb.1)
    exact h1.trans (by rw [h2, hCb])
  have hAle : A ≤ W₁ := hA ▸ piPrimeCoreSub_le_pResidual hp hpE inf_le_left
  have hAle' : A ≤ W₁ ⊓ C := le_inf hAle ((piPrimeCoreSub_le _ _).trans inf_le_right)
  -- `A` is a normal `π₁'`-subgroup of `W₁ ⊓ C`, hence `A ≤ A'`
  have hAleA' : A ≤ A' := by
    have hnormal : (A.subgroupOf (W₁ ⊓ C)).Normal := by
      refine Subgroup.normal_subgroupOf_of_le_normalizer ?_
      rw [hA]
      exact (le_inf (inf_le_left.trans hW₁le) inf_le_right).trans
        (piPrimeCoreSub_le_normalizer _ _)
    have hispi : Work.Fitting.IsPiNat (fun r => r ∉ ({r' : ℕ | r' ∣ Nat.card ↥E₁} : Set ℕ))
        (Nat.card ↥(A.subgroupOf (W₁ ⊓ C))) := by
      rw [card_subgroupOf_eq A _ hAle', hA]
      intro r hr hrdvd hrE₁
      exact not_dvd_card_piPrimeCoreSub (π := {r' : ℕ | r' ∣ Nat.card E}) hr
        (hrE₁.trans hcardE₁) _ hrdvd
    calc A = A ⊓ (W₁ ⊓ C) := (inf_of_le_left hAle').symm
      _ = (A.subgroupOf (W₁ ⊓ C)).map (W₁ ⊓ C).subtype :=
          (Subgroup.subgroupOf_map_subtype A _).symm
      _ ≤ (Work.Fitting.piCore (fun r => r ∉ ({r' : ℕ | r' ∣ Nat.card ↥E₁} : Set ℕ))
            ↥(W₁ ⊓ C)).map (W₁ ⊓ C).subtype :=
          Subgroup.map_mono (Work.Fitting.le_piCore hnormal hispi)
      _ = A' := rfl
  have hA'le : A' ≤ W₁ ⊓ Subgroup.normalizer (U : Set G) :=
    le_inf ((Subgroup.map_subtype_le _).trans inf_le_left)
      ((Subgroup.map_subtype_le _).trans
        (inf_le_right.trans (Subgroup.centralizer_le_normalizer (U : Set G))))
  have hE₁Nle : E₁ ⊓ Subgroup.normalizer (U : Set G) ≤ W₁ ⊓ Subgroup.normalizer (U : Set G) :=
    le_inf (inf_le_left.trans inf_le_right) inf_le_right
  refine le_antisymm ?_ (sup_le hA'le hE₁Nle)
  · intro x hx
    obtain ⟨hxW₁, hxN⟩ := Subgroup.mem_inf.mp hx
    have hxNW : x ∈ Subgroup.normalizer (U : Set G) ⊓ W := ⟨hxN, hW₁le hxW₁⟩
    rw [hAB] at hxNW
    obtain ⟨a, ha, b, hb, hxeq⟩ := Work.NormalComplement.CC.mem_sup_prod hBnorm hxNW
    have hbW₁ : b ∈ W₁ := by
      have hba : b = a⁻¹ * x := by rw [← hxeq]; group
      rw [hba]
      exact W₁.mul_mem (W₁.inv_mem (hAle ha)) hxW₁
    rw [← hxeq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hAleA' ha))
      (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨⟨hb.1, hbW₁⟩, hb.2⟩))

/-! ## The main theorem -/

/-- **The Corollary of Peterfalvi I Ch. III §1 Lemma 2.** -/
theorem controlCorollary_aux (E W : Subgroup G) (hEW : E ≤ W)
    (hsol : Group.IsSolvable ↥E) (hch : ControlHyp E W) :
    Nat.Coprime (Nat.card E) (E.relIndex W) ∧
      ∃ N : Subgroup G, N ≤ W ∧ W ≤ Subgroup.normalizer (N : Set G) ∧ N ⊓ E = ⊥ ∧
        N ⊔ E = W := by
  classical
  have hmain : ∀ n : ℕ, ∀ (E' W' : Subgroup G), Nat.card W' = n → E' ≤ W' →
      Group.IsSolvable ↥E' → ControlHyp E' W' →
      Nat.Coprime (Nat.card E') (E'.relIndex W') ∧
        ∃ N : Subgroup G, N ≤ W' ∧ W' ≤ Subgroup.normalizer (N : Set G) ∧ N ⊓ E' = ⊥ ∧
          N ⊔ E' = W' := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro E' W' hcard hE'W' hsol' hch'
      by_cases hbot : E' = ⊥
      · subst hbot
        exact ⟨by simp, W', le_rfl, Subgroup.le_normalizer, by simp, by simp⟩
      · have hhall := cc_hall hE'W' hch'
        -- a prime `q ∣ |E' : [E',E']|` and a `q`-element `y ∈ E' ∖ [E',E']`
        obtain ⟨q, hq, hqdvd⟩ : ∃ q : ℕ, q.Prime ∧ q ∣ (⁅E', E'⁆).relIndex E' := by
          refine Nat.exists_prime_and_dvd ?_
          intro h1
          have hle : E' ≤ ⁅E', E'⁆ := Subgroup.relIndex_eq_one.mp h1
          have hge : ⁅E', E'⁆ ≤ E' := Subgroup.commutator_le.mpr (fun g₁ hg₁ g₂ hg₂ => by
            rw [commutatorElement_def]
            exact E'.mul_mem (E'.mul_mem (E'.mul_mem hg₁ hg₂) (E'.inv_mem hg₁))
              (E'.inv_mem hg₂))
          exact commutator_ne_of_solvable E' hbot hsol' (le_antisymm hge hle)
        obtain ⟨y, hyE, hy', hord⟩ :=
          primes_of_abelianization G E' hbot hsol' q hq hqdvd
        have hy1 : y ≠ 1 := fun h => hy' (h ▸ Subgroup.one_mem _)
        have hqE : q ∣ Nat.card E' := hqdvd.trans (Subgroup.relIndex_dvd_card _ _)
        haveI : Fact q.Prime := ⟨hq⟩
        have hnorm := cc_hnorm hE'W' hch' hq hqE
        have htransfer : y ∉ Work.Grun.pResidual q W' := by
          refine pcontrol_transfer_aux (E := E') (W := W') ?_ hyE hy1 hord hy'
            (pcontrol_prod_aux hE'W' hqE hnorm)
            (notMem_pResidual_sup_commutator hyE hy1 hord hy') ?_
          · obtain ⟨P, -, hPsyl⟩ := exists_isSylowIn_ge (p := q) (T := ⊥) (X := E') bot_le
              (IsPGroup.of_bot (p := q))
            have hPne : P ≠ ⊥ := by
              intro hb
              have hcardP : Nat.card ↥P = 1 := by rw [hb]; simp
              have h1 : Nat.card ↥E' = (P.subgroupOf E').index * Nat.card ↥P := by
                rw [← Subgroup.index_mul_card (P.subgroupOf E'),
                  card_subgroupOf_eq P E' hPsyl.2.1]
              have hdvd : q ∣ Nat.card ↥E' := hqE
              rw [h1, hcardP, mul_one] at hdvd
              exact hPsyl.2.2 hdvd
            exact pcontrol_criterion hE'W' hqE hPsyl (hnorm P hPsyl.2.1 hPne hPsyl.1)
              (fun U hUP hUnc => hnorm U (hUP.trans hPsyl.2.1)
                (fun hb => hUnc (hb ▸ (inferInstance : IsCyclic ↥(⊥ : Subgroup G))))
                (hPsyl.1.to_le hUP))
          · intro z hz
            rw [← map_pResidual_sup_commutator_subgroupOf hE'W']
            exact Subgroup.mem_map_of_mem W'.subtype hz
        set W₁ : Subgroup G := Work.Grun.pResidual q W' with hW₁def
        have hW₁le : W₁ ≤ W' := Work.Grun.pResidual_le q W'
        have hW₁ne : W₁ ≠ W' := fun h => htransfer (h ▸ hE'W' hyE)
        have hW₁norm : W' ≤ Subgroup.normalizer (W₁ : Set G) := by
          rw [Subgroup.le_normalizer_iff]
          intro w hw z hz
          rw [hW₁def, Work.Grun.pResidual_eq_map_pResidual, Subgroup.mem_map] at hz ⊢
          obtain ⟨k, hk, rfl⟩ := hz
          refine ⟨⟨w, hw⟩ * k * ⟨w, hw⟩⁻¹, ?_, ?_⟩
          · exact (Work.NPC.Frobenius.pResidual_normal q).conj_mem k hk ⟨w, hw⟩
          · simp [MulAut.conj_apply]
        have hW₁sup : W₁ ⊔ E' = W' := by
          refine le_antisymm (sup_le hW₁le hE'W') ?_
          have hK : W₁ ⊔ E' ≤ W' := sup_le hW₁le hE'W'
          have hd1 : (W₁ ⊔ E').relIndex W' ∣ W₁.relIndex W' :=
            ⟨W₁.relIndex (W₁ ⊔ E'), by
              rw [← Subgroup.relIndex_mul_relIndex W₁ (W₁ ⊔ E') W' le_sup_left hK, mul_comm]⟩
          have hd2 : (W₁ ⊔ E').relIndex W' ∣ E'.relIndex W' :=
            ⟨E'.relIndex (W₁ ⊔ E'), by
              rw [← Subgroup.relIndex_mul_relIndex E' (W₁ ⊔ E') W' le_sup_right hK, mul_comm]⟩
          obtain ⟨m, hm⟩ := relIndex_pResidual_eq_pow (p := q) W'
          have hnot : ¬ q ∣ (W₁ ⊔ E').relIndex W' := fun h => hhall q hq hqE (dvd_trans h hd2)
          have hone : (W₁ ⊔ E').relIndex W' = 1 :=
            eq_one_of_dvd_pow_of_not_dvd hq (hm ▸ hd1) hnot
          exact Subgroup.relIndex_eq_one.mp hone
        set E₁ : Subgroup G := E' ⊓ W₁ with hE₁def
        have hE₁le : E₁ ≤ W₁ := inf_le_right
        have hlt : Nat.card ↥W₁ < Nat.card ↥W' :=
          card_lt_card_of_lt (lt_of_le_of_ne hW₁le hW₁ne)
        have hsol₁ : Group.IsSolvable ↥E₁ := by
          haveI := hsol'
          haveI : Group.IsSolvable ↥(E₁.subgroupOf E') := inferInstance
          exact Group.isSolvable_of_isSolvable_injective
            (f := (Subgroup.subgroupOfEquivOfLe (inf_le_left : E₁ ≤ E')).symm.toMonoidHom)
            (Subgroup.subgroupOfEquivOfLe (inf_le_left : E₁ ≤ E')).symm.injective
        have hch₁ : ControlHyp E₁ W₁ := cc_controlHyp_inf hE'W' hch' hq hqE
        obtain ⟨-, N₀, hN₀le, hN₀norm, hN₀inf, hN₀sup⟩ :=
          ih (Nat.card ↥W₁) (hcard ▸ hlt) E₁ W₁ rfl hE₁le hsol₁ hch₁
        -- the cardinality identity `|N₀| * |E'| = |W'|`
        have hcard₁ : Nat.card ↥N₀ * Nat.card ↥E₁ = Nat.card ↥W₁ := by
          have h := card_sup_mul_card_inf_of_le_normalizer (E₁) (N₀) (by
            refine sup_le ?_ Subgroup.le_normalizer
            exact inf_le_right.trans hN₀norm)
          rw [sup_comm, hN₀sup, inf_comm, hN₀inf, Subgroup.card_bot, mul_one, mul_comm] at h
          exact h.symm
        have hcard₂ : Nat.card ↥W' * Nat.card ↥E₁ = Nat.card ↥E' * Nat.card ↥W₁ := by
          have h := card_sup_mul_card_inf_of_le_normalizer (E') (W₁)
            (sup_le (hE'W'.trans hW₁norm) Subgroup.le_normalizer)
          rw [sup_comm, hW₁sup, ← hE₁def] at h
          exact h
        have hN₀card : Nat.card ↥N₀ * Nat.card ↥E' = Nat.card ↥W' := by
          have key : Nat.card ↥E' * Nat.card ↥N₀ * Nat.card ↥E₁ =
              Nat.card ↥W' * Nat.card ↥E₁ := by
            rw [mul_assoc, hcard₁, ← hcard₂]
          have key2 : Nat.card ↥E' * Nat.card ↥N₀ = Nat.card ↥W' :=
            Nat.mul_right_cancel Nat.card_pos key
          rwa [mul_comm] at key2
        -- `N₀ ≤ O_{π'}(W₁)`
        have hN₀leN : N₀ ≤ piPrimeCoreSub {r : ℕ | r ∣ Nat.card E'} W₁ := by
          have hnorm' : (N₀.subgroupOf W₁).Normal :=
            Subgroup.normal_subgroupOf_of_le_normalizer hN₀norm
          have hpi : Work.Fitting.IsPiNat
              (fun r => r ∉ ({r' : ℕ | r' ∣ Nat.card E'} : Set ℕ))
              (Nat.card ↥(N₀.subgroupOf W₁)) := by
            rw [card_subgroupOf_eq N₀ W₁ hN₀le]
            have hcard : Nat.card ↥N₀ = (E'.subgroupOf W').index := by
              have hidx : (E'.subgroupOf W').index * Nat.card ↥E' = Nat.card ↥W' := by
                rw [← card_subgroupOf_eq E' W' hE'W', Subgroup.index_mul_card]
              exact Nat.mul_right_cancel Nat.card_pos (hN₀card.trans hidx.symm)
            intro r hr hrdvd hrE
            exact hhall r hr hrE (hcard ▸ hrdvd)
          have hle : (N₀.subgroupOf W₁) ≤
              Work.Fitting.piCore (fun r => r ∉ ({r' : ℕ | r' ∣ Nat.card E'} : Set ℕ)) ↥W₁ :=
            Work.Fitting.le_piCore hnorm' hpi
          calc N₀ = (N₀.subgroupOf W₁).map W₁.subtype :=
                (inf_of_le_left hN₀le).symm.trans (Subgroup.subgroupOf_map_subtype N₀ W₁).symm
            _ ≤ (Work.Fitting.piCore (fun r => r ∉ ({r' : ℕ | r' ∣ Nat.card E'} : Set ℕ))
                  ↥W₁).map W₁.subtype := Subgroup.map_mono hle
            _ = piPrimeCoreSub {r : ℕ | r ∣ Nat.card E'} W₁ := rfl
        refine ⟨cc_coprime hhall, piPrimeCoreSub {r : ℕ | r ∣ Nat.card E'} W₁, ?_, ?_, ?_, ?_⟩
        · exact (piPrimeCoreSub_le _ _).trans hW₁le
        · rw [← hW₁sup]
          refine sup_le (piPrimeCoreSub_le_normalizer _ _) ?_
          intro e he
          rw [Subgroup.mem_normalizer_iff_map_conj_eq]
          exact map_conj_piPrimeCoreSub_eq (π := {r : ℕ | r ∣ Nat.card E'})
            (hW₁norm (hE'W' he))
        · have hNE : piPrimeCoreSub {r : ℕ | r ∣ Nat.card E'} W₁ ⊓ E' =
              piPrimeCoreSub {r : ℕ | r ∣ Nat.card E'} W₁ ⊓ E₁ := by
            rw [hE₁def, inf_comm E' W₁, ← inf_assoc, inf_eq_left.mpr (piPrimeCoreSub_le _ _)]
          rw [hNE]
          refine (Subgroup.eq_bot_iff_forall (H := piPrimeCoreSub {r : ℕ | r ∣ Nat.card E'} W₁ ⊓
            E₁)).mpr fun x hx => ?_
          obtain ⟨hxN, hxE₁⟩ := Subgroup.mem_inf.mp hx
          have hN : orderOf x ∣ Nat.card ↥(piPrimeCoreSub {r : ℕ | r ∣ Nat.card E'} W₁) :=
            Subgroup.orderOf_dvd_natCard _ hxN
          have hE : orderOf x ∣ Nat.card ↥E₁ := Subgroup.orderOf_dvd_natCard _ hxE₁
          by_contra hx1
          obtain ⟨r, hr, hrx⟩ := Nat.exists_prime_and_dvd
            (fun h => hx1 (orderOf_eq_one_iff.mp h))
          have hcardE₁' : Nat.card ↥E₁ ∣ Nat.card ↥E' := by
            rw [← card_subgroupOf_eq E₁ E' (inf_le_left : E₁ ≤ E')]
            exact Subgroup.card_subgroup_dvd_card _
          exact not_dvd_card_piPrimeCoreSub (π := {r' : ℕ | r' ∣ Nat.card E'}) hr
            ((hrx.trans hE).trans hcardE₁') _ (hrx.trans hN)
        · refine le_antisymm ?_ ?_
          · exact sup_le ((piPrimeCoreSub_le _ _).trans hW₁le) hE'W'
          · rw [← hW₁sup]
            refine sup_le ?_ le_sup_right
            conv_lhs => rw [← hN₀sup]
            exact sup_le (hN₀leN.trans le_sup_left) (inf_le_left.trans le_sup_right)
  exact hmain (Nat.card W) E W rfl hEW hsol hch

end Work.NormalComplement

namespace Work.NormalComplement

/-- **The Corollary of Peterfalvi I Ch. III §1 Lemma 2** (p.174), as the `Prop`
`Work.NormalComplement.ControlCorollaryProp`.  Route: `E` is a Hall subgroup of `W` (apply the
hypothesis to a Sylow `p` of `E`); assuming `E ≠ 1`, pick `p ∣ |E|` with `O^p(E) < E` and deduce
the two normaliser hypotheses of `Work.NormalComplement.pcontrol_criterion` (module
`pcontrol_criterion`), so `E` is `p`-control in `W`; the transfer Lemma 1 (formalised as
`Work.NormalComplement.pcontrol_transfer_aux`, with the product form of the control condition
supplied by `Work.NormalComplement.pcontrol_prod_aux`) then yields `W₁ ⊴ W`, `W₁ ≠ W`, `W/W₁` a
`p`-group, and `W = W₁ E` (index argument: `E` contains a Sylow `p` of `W`); induction on `|W|` for
`W₁` and `E ∩ W₁` gives the normal complement, which is `O_{π'}(W₁)`, normal in `W`. -/
theorem controlCorollary : Work.NormalComplement.ControlCorollaryProp := by
  intro G _ _ E W hEW hsol hhyp
  exact controlCorollary_aux E W hEW hsol hhyp

end Work.NormalComplement
