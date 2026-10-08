/-
# The `p`-control condition in product form

`Work.NormalComplement.pcontrol_criterion` derives the *join form* of the `p`-control condition:
for `U ≤ E` a `p`-subgroup of `E` and `x ∈ W` with `x⁻¹Ux ≤ E`, one gets `x ∈ C_G(U) ⊔ E`.

Peterfalvi's transfer argument (Ch. III §1 Lemma 1, formalized as
`Work.NormalComplement.pcontrol_transfer_aux` in
`Submission/Work/NormalComplement/pcontrol_transfer.lean`) needs the *product form*:
`x = c * e` with `c ∈ C_G(U) ∩ W`, `e ∈ E`.

Here we prove the product form from the normaliser hypothesis for **every** non-trivial
`p`-subgroup of `E` (which is what the Corollary of Ch. III §1 Lemma 2 supplies).  The induction is
the one of the paper's Lemma 2 (and of `pcontrol_criterion`), but the product information is kept
throughout:

* `N_W(U) = O_{p'}(C_W(U)) ⊔ N_E(U)`, and `O_{p'}(C_W(U))` is normalised by `N_G(U) ∩ E`, so
  `O_{p'}(C_W(U))·N_E(U)` is a subgroup and every `x ∈ N_W(U)` is a product `c·e`;
* strong induction on `|P| - |A|` (`P` a Sylow `p` of `E`): the base case (`A` a Sylow of `E`) uses
  Sylow conjugacy inside `E`; the recursion step enlarges `A` to a Sylow `S` of `N_E(A)`, uses
  `Work.NormalComplement.sylow_normalizer_transfer` (`S` is a Sylow of `N_W(A)`) and Sylow conjugacy
  in `N_W(A)`, and finishes with `Work.NormalComplement.conj_sylow_of_isCyclic` (cyclic case) or the
  product form of `N_W(A)` (non-cyclic case).
-/
import Mathlib
import Submission.Work.NormalComplement.Defs
import Submission.Work.NormalComplement.pcontrol_criterion
import Submission.Work.NormalComplement.sylow_normalizer_transfer
import Submission.Work.NormalComplement.conj_sylow_of_isCyclic
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

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- `O_{p'}(X) = pPrimeCoreSub p X` written as the image of the `pPrimeCore` of `↥X`. -/
lemma pPrimeCoreSub_eq_map (X : Subgroup G) :
    pPrimeCoreSub p X = (Work.Fitting.piCore (fun q => q ≠ p) ↥X).map X.subtype := by
  rw [pPrimeCoreSub, Work.GlaubermanZJ.pPrimeCore_eq_fitting p (Fact.out : p.Prime)]
  rfl

/-- `X` normalises `O_{p'}(X)`. -/
lemma pPrimeCoreSub_le_normalizer (X : Subgroup G) :
    X ≤ Subgroup.normalizer (pPrimeCoreSub p X : Set G) := by
  have hpc := pPrimeCoreSub_eq_map (G := G) (p := p) X
  haveI hnrm : (Work.Fitting.piCore (fun q => q ≠ p) ↥X).Normal :=
    Work.Fitting.normal_sSup (fun N hN => hN.1)
  rw [Subgroup.le_normalizer_iff]
  intro x hx y hy
  rw [hpc] at hy ⊢
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
  refine Subgroup.mem_map.mpr ⟨⟨x, hx⟩ * k * ⟨x, hx⟩⁻¹, hnrm.conj_mem k hk ⟨x, hx⟩, ?_⟩
  simp [MulAut.conj_apply]

/-- Conjugation by an element of `N_G(X)` sends `O_{p'}(X)` into itself: the conjugate
`O_{p'}(X)^b` is again a normal `p'`-subgroup of `X`. -/
lemma map_conj_pPrimeCoreSub_le {X : Subgroup G} {b : G}
    (h : b ∈ Subgroup.normalizer (X : Set G)) :
    (pPrimeCoreSub p X).map (MulAut.conj b).toMonoidHom ≤ pPrimeCoreSub p X := by
  set A : Subgroup G := pPrimeCoreSub p X with hA
  set Ab : Subgroup G := A.map (MulAut.conj b).toMonoidHom with hAb
  have hpc := pPrimeCoreSub_eq_map (G := G) (p := p) X
  have hAX : A ≤ X := by rw [hA]; exact Subgroup.map_subtype_le _
  have hAnorm : X ≤ Subgroup.normalizer (A : Set G) := by
    rw [hA]; exact pPrimeCoreSub_le_normalizer X
  have hmapX : X.map (MulAut.conj b).toMonoidHom = X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp h
  have hbinv : b⁻¹ ∈ Subgroup.normalizer (X : Set G) := Subgroup.inv_mem _ h
  have hconjX : ∀ g ∈ X, b⁻¹ * g * b ∈ X := fun g hg =>
    by simpa using (Subgroup.mem_normalizer_iff.mp hbinv g).mp hg
  -- `Ab` is a normal subgroup of `X`
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
  -- `Ab` is a `p'`-group of the same order as `O_{p'}(X)`, so it is contained in `O_{p'}(X)`
  have hnormal : (Ab.subgroupOf X).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hAbnorm
  have hispi : Work.Fitting.IsPiNat (fun q => q ≠ p) (Nat.card ↥(Ab.subgroupOf X)) := by
    rw [card_subgroupOf_eq Ab X hAbX, hAb, Subgroup.card_map_of_injective (MulAut.conj b).injective,
      hA, hpc, Subgroup.card_map_of_injective X.subtype_injective]
    exact Work.Fitting.piCore_isPiNat ↥X (fun q => q ≠ p)
  calc Ab = Ab ⊓ X := (inf_of_le_left hAbX).symm
    _ = (Ab.subgroupOf X).map X.subtype := (Subgroup.subgroupOf_map_subtype Ab X).symm
    _ ≤ (Work.Fitting.piCore (fun q => q ≠ p) ↥X).map X.subtype :=
        Subgroup.map_mono (Work.Fitting.le_piCore hnormal hispi)
    _ = pPrimeCoreSub p X := hpc.symm

/-- Conjugation by an element of `N_G(X)` preserves `O_{p'}(X)`. -/
lemma map_conj_pPrimeCoreSub_eq {X : Subgroup G} {y : G}
    (h : y ∈ Subgroup.normalizer (X : Set G)) :
    (pPrimeCoreSub p X).map (MulAut.conj y).toMonoidHom = pPrimeCoreSub p X := by
  refine le_antisymm (map_conj_pPrimeCoreSub_le h) ?_
  have h2 := map_conj_pPrimeCoreSub_le (p := p) (X := X) (Subgroup.inv_mem _ h)
  calc pPrimeCoreSub p X
      = ((pPrimeCoreSub p X).map (MulAut.conj y⁻¹).toMonoidHom).map
          (MulAut.conj y).toMonoidHom := by
        rw [map_conj_map_conj, mul_inv_cancel]
        ext x
        simp
    _ ≤ (pPrimeCoreSub p X).map (MulAut.conj y).toMonoidHom := Subgroup.map_mono h2

/-- Conjugation by an element of `N_G(U)` preserves the centralizer `C_G(U)`. -/
lemma map_conj_centralizer_eq {U : Subgroup G} {e : G}
    (he : e ∈ Subgroup.normalizer (U : Set G)) :
    (Subgroup.centralizer (U : Set G)).map (MulAut.conj e).toMonoidHom
      = Subgroup.centralizer (U : Set G) := by
  have key : ∀ f ∈ Subgroup.normalizer (U : Set G),
      (Subgroup.centralizer (U : Set G)).map (MulAut.conj f).toMonoidHom
        ≤ Subgroup.centralizer (U : Set G) := by
    intro f hf x hx
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro u hu
    have hmem : f⁻¹ * u * f ∈ U :=
      (Subgroup.mem_normalizer_iff.mp hf (f⁻¹ * u * f)).mpr (by
        show f * (f⁻¹ * u * f) * f⁻¹ ∈ U
        rw [show f * (f⁻¹ * u * f) * f⁻¹ = u from by group]
        exact hu)
    calc u * (f * c * f⁻¹) = f * ((f⁻¹ * u * f) * c) * f⁻¹ := by group
      _ = f * (c * (f⁻¹ * u * f)) * f⁻¹ := by rw [hc (f⁻¹ * u * f) hmem]
      _ = (f * c * f⁻¹) * u := by group
  refine le_antisymm (key e he) ?_
  have h2 := key e⁻¹ (Subgroup.inv_mem _ he)
  calc Subgroup.centralizer (U : Set G)
      = ((Subgroup.centralizer (U : Set G)).map (MulAut.conj e⁻¹).toMonoidHom).map
          (MulAut.conj e).toMonoidHom := by
        rw [map_conj_map_conj, mul_inv_cancel]
        ext x
        simp
    _ ≤ (Subgroup.centralizer (U : Set G)).map (MulAut.conj e).toMonoidHom :=
        Subgroup.map_mono h2

/-- `N_G(U) ∩ W` normalises `C_G(U) ∩ W`. -/
lemma normalizer_inf_le_normalizer_centralizer_inf {U W : Subgroup G} :
    Subgroup.normalizer (U : Set G) ⊓ W ≤
      Subgroup.normalizer ((Subgroup.centralizer (U : Set G) ⊓ W : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro x hx c hc
  obtain ⟨hxN, hxW⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨hcC, hcW⟩ := Subgroup.mem_inf.mp hc
  refine Subgroup.mem_inf.mpr ⟨?_, W.mul_mem (W.mul_mem hxW hcW) (W.inv_mem hxW)⟩
  have hmem : x * c * x⁻¹ ∈ (Subgroup.centralizer (U : Set G)).map
      (MulAut.conj x).toMonoidHom := Subgroup.mem_map.mpr ⟨c, hcC, rfl⟩
  rwa [map_conj_centralizer_eq hxN] at hmem

/-- Extraction of the product form from the normaliser hypothesis
`N_W(U) = O_{p'}(C_W(U)) ⊔ N_E(U)`: `N_E(U)` normalises `O_{p'}(C_W(U))`, so the join is the
product. -/
lemma exists_prod_of_mem_normalizer_eq {E U : Subgroup G} {x : G} (W : Subgroup G)
    (hEW : E ≤ W)
    (hx : x ∈ Subgroup.normalizer (U : Set G) ⊓ W)
    (heq : Subgroup.normalizer (U : Set G) ⊓ W =
      pPrimeCoreSub p (Subgroup.centralizer (U : Set G) ⊓ W) ⊔
        (Subgroup.normalizer (U : Set G) ⊓ E)) :
    ∃ c : G, c ∈ Subgroup.centralizer (U : Set G) ∧ c ∈ W ∧
      ∃ e : G, e ∈ E ∧ e ∈ Subgroup.normalizer (U : Set G) ∧ x = c * e := by
  rw [heq] at hx
  have hnorm : Subgroup.normalizer (U : Set G) ⊓ E ≤
      Subgroup.normalizer
        (pPrimeCoreSub p (Subgroup.centralizer (U : Set G) ⊓ W) : Set G) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact map_conj_pPrimeCoreSub_eq (normalizer_inf_le_normalizer_centralizer_inf ⟨he.1, hEW he.2⟩)
  obtain ⟨c, hc, e, he, hce⟩ := Work.NormalComplement.CC.mem_sup_prod hnorm hx
  have hc' : c ∈ Subgroup.centralizer (U : Set G) ⊓ W := Subgroup.map_subtype_le _ hc
  exact ⟨c, hc'.1, hc'.2, e, he.2, he.1, hce.symm⟩

/-- **Peterfalvi I Ch. III §1 Lemma 2, product form.**  Let `E ≤ W` be finite with `p ∣ |E|`, and
assume the normaliser condition `N_W(U) = O_{p'}(C_W(U))·N_E(U)` for **every** non-trivial
`p`-subgroup `U` of `E`.  Then for every `p`-subgroup `U ≤ E` and every `x ∈ W` with
`x⁻¹Ux ≤ E`, one has `x = c·e` with `c ∈ C_G(U) ∩ W` and `e ∈ E`. -/
theorem pcontrol_prod_aux {E W : Subgroup G} (hEW : E ≤ W) (hpE : p ∣ Nat.card E)
    (hnorm : ∀ U : Subgroup G, U ≤ E → U ≠ ⊥ → IsPGroup p U →
      Subgroup.normalizer (U : Set G) ⊓ W =
        pPrimeCoreSub p (Subgroup.centralizer (U : Set G) ⊓ W) ⊔
          (Subgroup.normalizer (U : Set G) ⊓ E)) :
    ∀ U : Subgroup G, U ≤ E → IsPGroup p U → ∀ x ∈ W,
      Submission.Blueprint.conj x⁻¹ U ≤ E →
      ∃ c : G, c ∈ Subgroup.centralizer (U : Set G) ∧ c ∈ W ∧ ∃ e ∈ E, x = c * e := by
  -- a Sylow `p`-subgroup `P` of `E` and the two hypotheses of `sylow_normalizer_transfer`
  obtain ⟨P, -, hPsyl⟩ := exists_isSylowIn_ge (T := ⊥) (X := E) bot_le (IsPGroup.of_bot (p := p))
  have hpEne : P ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card ↥P = 1 := by rw [hbot]; simp
    have h1 : Nat.card ↥E = (P.subgroupOf E).index * Nat.card ↥P := by
      rw [← Subgroup.index_mul_card (P.subgroupOf E), card_subgroupOf_eq P E hPsyl.2.1]
    have hdvd : p ∣ Nat.card ↥E := hpE
    rw [h1, hcard, mul_one] at hdvd
    exact hPsyl.2.2 hdvd
  have h1 : Subgroup.normalizer (P : Set G) ⊓ W =
      pPrimeCoreSub p (Subgroup.centralizer (P : Set G) ⊓ W) ⊔
        (Subgroup.normalizer (P : Set G) ⊓ E) :=
    hnorm P hPsyl.2.1 hpEne hPsyl.1
  have h2 : ∀ U : Subgroup G, U ≤ P → ¬ IsCyclic U →
      Subgroup.normalizer (U : Set G) ⊓ W =
        pPrimeCoreSub p (Subgroup.centralizer (U : Set G) ⊓ W) ⊔
          (Subgroup.normalizer (U : Set G) ⊓ E) := by
    intro U hUP hUnc
    refine hnorm U (hUP.trans hPsyl.2.1) (fun hbot => hUnc ?_) (hPsyl.1.to_le hUP)
    rw [hbot]; infer_instance
  -- the product form of the normaliser hypothesis
  have hnp : ∀ U : Subgroup G, U ≤ E → U ≠ ⊥ → IsPGroup p U → ∀ x ∈ W,
      x ∈ Subgroup.normalizer (U : Set G) →
      ∃ c : G, c ∈ Subgroup.centralizer (U : Set G) ∧ c ∈ W ∧
        ∃ e : G, e ∈ E ∧ e ∈ Subgroup.normalizer (U : Set G) ∧ x = c * e := by
    intro U hUE hUne hUp x hxW hxN
    exact exists_prod_of_mem_normalizer_eq W hEW ⟨hxN, hxW⟩ (hnorm U hUE hUne hUp)
  -- the main induction
  have hmain : ∀ n : ℕ, ∀ A : Subgroup G, A ≤ E → IsPGroup p A → A ≠ ⊥ →
      Nat.card P - Nat.card A = n → ∀ y : G, y ∈ W →
      A.map (MulAut.conj y⁻¹).toMonoidHom ≤ E →
      ∃ c : G, c ∈ Subgroup.centralizer (A : Set G) ∧ c ∈ W ∧ ∃ e ∈ E, y = c * e := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro A hAE hAp hAne hmeasure y hyW hyconj
      by_cases hmax : Nat.card A = Nat.card P
      · -- ## base case: `A` is a Sylow of `E`
        have hAsyl : IsSylowIn p A E := isSylowIn_of_le_of_card_eq hAE hAp hPsyl hmax
        have hVsyl : IsSylowIn p (A.map (MulAut.conj y⁻¹).toMonoidHom) E :=
          isSylowIn_of_le_of_card_eq hyconj (hAp.map _) hPsyl (by
            rw [Subgroup.card_map_of_injective (MulAut.conj y⁻¹).injective, hmax])
        obtain ⟨f, hfE, hf⟩ := exists_conj_eq_of_isSylowIn_of_isSylowIn hVsyl hAsyl
        have hfN : f * y⁻¹ ∈ Subgroup.normalizer (A : Set G) := by
          rw [Subgroup.mem_normalizer_iff_map_conj_eq]
          rwa [map_conj_map_conj] at hf
        have hyfN : y * f⁻¹ ∈ Subgroup.normalizer (A : Set G) ⊓ W :=
          Subgroup.mem_inf.mpr ⟨by simpa using (Subgroup.normalizer (A : Set G)).inv_mem hfN,
            W.mul_mem hyW (W.inv_mem (hEW hfE))⟩
        obtain ⟨c, hcC, hcW, e, heE, -, heq⟩ := hnp A hAE hAne hAp (y * f⁻¹) hyfN.2 hyfN.1
        exact ⟨c, hcC, hcW, e * f, E.mul_mem heE hfE,
          by calc y = (y * f⁻¹) * f := by group
            _ = (c * e) * f := by rw [heq]
            _ = c * (e * f) := by group⟩
      · -- ## recursion
        have hAltP : Nat.card A < Nat.card P :=
          lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos
            (card_dvd_card_of_isPGroup_of_isSylowIn hAE hAp hPsyl)) hmax
        obtain ⟨Q, hAQ, hQsyl⟩ := exists_isSylowIn_ge hAE hAp
        have hQcard : Nat.card Q = Nat.card P := card_eq_of_isSylowIn_of_isSylowIn hQsyl hPsyl
        have hAltQ : A < Q := lt_of_le_of_ne hAQ (fun h => hmax (by rw [h, hQcard]))
        have hleA : A ≤ Q ⊓ Subgroup.normalizer (A : Set G) := le_inf hAQ Subgroup.le_normalizer
        have hcardNQA : Nat.card A < Nat.card ↥(Q ⊓ Subgroup.normalizer (A : Set G)) := by
          have h1c : Nat.card A ∣ Nat.card ↥(Q ⊓ Subgroup.normalizer (A : Set G)) := by
            rw [← card_subgroupOf_eq A _ hleA]
            exact Subgroup.card_subgroup_dvd_card _
          refine lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos h1c) fun hc => ?_
          have heq : A = Q ⊓ Subgroup.normalizer (A : Set G) :=
            Subgroup.eq_of_le_of_card_ge hleA (le_of_eq hc.symm)
          exact (lt_inf_normalizer_of_isPGroup hAltQ hQsyl.1).2 (le_of_eq heq.symm)
        have hTle : Q ⊓ Subgroup.normalizer (A : Set G) ≤
            Subgroup.normalizer (A : Set G) ⊓ E :=
          le_inf inf_le_right (inf_le_left.trans hQsyl.2.1)
        obtain ⟨S, hNQS, hSsyl⟩ := exists_isSylowIn_ge hTle hQsyl.1.to_inf_left
        have hAS : A ≤ S := hleA.trans hNQS
        have hAltS : Nat.card A < Nat.card S := lt_of_lt_of_le hcardNQA (card_le_card_of_le hNQS)
        have hSne : S ≠ ⊥ := fun hbot => hAne (le_bot_iff.mp (hbot ▸ hAS))
        -- `S` is a Sylow of `N_W(A)`
        have hS_NWA : IsSylowIn p S (Subgroup.normalizer (A : Set G) ⊓ W) :=
          sylow_normalizer_transfer hEW hPsyl h1 h2 hAE hAp hSsyl
        -- a Sylow `S₁` of `N_E(V)`, `V = y⁻¹Ay`
        obtain ⟨S₁, -, hS₁syl⟩ := exists_isSylowIn_ge (T := ⊥)
          (X := Subgroup.normalizer ((A.map (MulAut.conj y⁻¹).toMonoidHom) : Set G) ⊓ E)
          bot_le (IsPGroup.of_bot (p := p))
        have hS₁_NWV : IsSylowIn p S₁
            (Subgroup.normalizer ((A.map (MulAut.conj y⁻¹).toMonoidHom) : Set G) ⊓ W) :=
          sylow_normalizer_transfer hEW hPsyl h1 h2 hyconj (hAp.map _) hS₁syl
        have hT2 : IsSylowIn p (S₁.map (MulAut.conj y).toMonoidHom)
            ((Subgroup.normalizer ((A.map (MulAut.conj y⁻¹).toMonoidHom) : Set G) ⊓ W).map
              (MulAut.conj y).toMonoidHom) := isSylowIn_map_conj hS₁_NWV y
        have hVmap : (A.map (MulAut.conj y⁻¹).toMonoidHom).map (MulAut.conj y).toMonoidHom
            = A := by
          rw [map_conj_map_conj, mul_inv_cancel]
          ext x
          simp
        have hmap2 : (Subgroup.normalizer ((A.map (MulAut.conj y⁻¹).toMonoidHom) : Set G) ⊓ W).map
            (MulAut.conj y).toMonoidHom = Subgroup.normalizer (A : Set G) ⊓ W := by
          rw [Subgroup.map_inf _ _ _ (MulAut.conj y).injective,
            Subgroup.map_equiv_normalizer_eq _ (MulAut.conj y),
            map_conj_eq_self_of_mem (X := W) hyW, hVmap]
        have hT2' : IsSylowIn p (S₁.map (MulAut.conj y).toMonoidHom)
            (Subgroup.normalizer (A : Set G) ⊓ W) := by
          rw [← hmap2]; exact hT2
        -- the induction hypothesis applied to `S`
        have step : ∀ z : G, z ∈ W →
            S.map (MulAut.conj z).toMonoidHom = S₁.map (MulAut.conj y).toMonoidHom →
            ∃ c : G, c ∈ Subgroup.centralizer (S : Set G) ∧ c ∈ W ∧ ∃ e ∈ E, z⁻¹ * y = c * e := by
          intro z hzW hzS
          have hwW : z⁻¹ * y ∈ W := mul_mem (inv_mem hzW) hyW
          have hwconj : S.map (MulAut.conj (z⁻¹ * y)⁻¹).toMonoidHom ≤ E := by
            have h1' : (z⁻¹ * y)⁻¹ = y⁻¹ * z := by group
            rw [h1', ← map_conj_map_conj S z y⁻¹, hzS, map_conj_inv]
            exact hS₁syl.2.1.trans inf_le_right
          have hlt' : Nat.card P - Nat.card S < n := hmeasure ▸ Nat.sub_lt_sub_left hAltP hAltS
          exact ih (Nat.card P - Nat.card S) hlt' S (hSsyl.2.1.trans inf_le_right) hSsyl.1 hSne rfl
            (z⁻¹ * y) hwW hwconj
        by_cases hcyc : IsCyclic ↥A
        · -- ## cyclic `A`: the conjugating Sylow element lies in `C_W(A)`
          obtain ⟨z, hz, hzS⟩ := conj_sylow_of_isCyclic (W := W) (U := A) (hAE.trans hEW) hcyc
            hS_NWA hT2'
          obtain ⟨c, hcC, hcW, e, heE, heq⟩ := step z hz.2 hzS
          refine ⟨z * c, ?_, mul_mem hz.2 hcW, e, heE,
            by calc y = z * (z⁻¹ * y) := by group
              _ = z * (c * e) := by rw [heq]
              _ = (z * c) * e := by group⟩
          exact Subgroup.mul_mem _ hz.1
            (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hAS) hcC)
        · -- ## non-cyclic `A`
          obtain ⟨z, hz, hzS⟩ := exists_conj_eq_of_isSylowIn_of_isSylowIn hS_NWA hT2'
          obtain ⟨c₁, hc₁C, hc₁W, e₁, he₁E, he₁N, hz_eq⟩ :=
            hnp A hAE hAne hAp z hz.2 hz.1
          obtain ⟨c₂, hc₂C, hc₂W, e₂, he₂E, heq₂⟩ := step z hz.2 hzS
          have hc₂'A : c₂ ∈ Subgroup.centralizer (A : Set G) :=
            Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hAS) hc₂C
          have he₁c₂ : e₁ * c₂ * e₁⁻¹ ∈ Subgroup.centralizer (A : Set G) := by
            rw [Subgroup.mem_centralizer_iff] at hc₂'A ⊢
            intro u hu
            have hmem : e₁⁻¹ * u * e₁ ∈ A :=
              by simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ he₁N) u).mp hu
            calc u * (e₁ * c₂ * e₁⁻¹) = e₁ * ((e₁⁻¹ * u * e₁) * c₂) * e₁⁻¹ := by group
              _ = e₁ * (c₂ * (e₁⁻¹ * u * e₁)) * e₁⁻¹ := by rw [hc₂'A (e₁⁻¹ * u * e₁) hmem]
              _ = (e₁ * c₂ * e₁⁻¹) * u := by group
          refine ⟨c₁ * (e₁ * c₂ * e₁⁻¹), Subgroup.mul_mem _ hc₁C he₁c₂,
            mul_mem hc₁W (mul_mem (mul_mem (hEW he₁E) hc₂W) (inv_mem (hEW he₁E))),
            e₁ * e₂, E.mul_mem he₁E he₂E, ?_⟩
          calc y = z * (z⁻¹ * y) := by group
            _ = (c₁ * e₁) * (c₂ * e₂) := by rw [heq₂, hz_eq]
            _ = (c₁ * (e₁ * c₂ * e₁⁻¹)) * (e₁ * e₂) := by group
  -- ## assembly
  intro U hUE hUp x hxW hconj
  by_cases hU : U = ⊥
  · subst hU
    refine ⟨x, ?_, hxW, 1, E.one_mem, by simp⟩
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have : u = 1 := by simpa using hu
    subst this
    simp
  · exact hmain (Nat.card P - Nat.card U) U hUE hUp hU rfl x hxW hconj

end Work.NormalComplement
