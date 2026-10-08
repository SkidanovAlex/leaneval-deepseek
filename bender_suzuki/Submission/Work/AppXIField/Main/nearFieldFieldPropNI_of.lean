import Mathlib
import Submission.Work.AppXIField.Defs
import Submission.Work.AppXIField.Main.Basic
import Submission.Work.ThmF.ChV3.Ctx
import Submission.Work.AppXIField.Main.sig_conjAction_cq
import Submission.Work.AppXIField.Main.exists_conjAut_R
import Submission.Work.AppXIField.Main.exists_conjAction_quot
import Submission.Work.AppXIField.Main.card_fixedPoints_sigma
import Submission.Work.AppXIField.Main.odd_orderOf_st
import Submission.Work.AppXIField.L0.field_of_free_comm_action

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Area `AppXIField`: Appendix XI Prop. 1 (2)b — `NearFieldFieldPropNI`

`Work.AppXIField.nearFieldFieldPropNI_of`: the near-field quotient `R/N` of Ch. V §3 step (2)
is a finite field of cardinality `o(st)^m = |C_Q(P)| + 1` on which `Σ = C_W(P)` acts by
automorphisms with `Fix σ_w = {0} ∪ ι(C_{C_Q(P)}(w))` (the form in which §3 steps (6), (7) and
(8) consume App. XI Prop. 1 (2)b).

The proof applies `hNFp : NearFieldAppXIPropPlus` to the standing context, obtains `m', R, N`
with `N = Ker H Q P t`, `R ≤ C_G(P)`, `C_G(P) ≤ N_G(R) ∩ N_G(N)`, `|R| = |N| · f^{m'}`,
`|C_Q(P)| + 1 = f^{m'}` (`f = o(st)`) and the fixed-point-freeness clause, puts
`V := Additive (↥R ⧸ N.subgroupOf R)` (commutative by `[R,R] ≤ N`), lets `A = C_Q(P)` and
`B = Σ = Sig H t P` act by conjugation, and applies `field_of_free_comm_action` (L0).  The fixed
points of `σ_w` are `{0} ∪ ι(C_{C_Q(P)}(w))` because `ι` is bijective onto `Fˣ`
(`|C_Q(P)| = |F| - 1`) and `σ_w (ι a) = ι (w a w⁻¹)`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
noncomputable section
open Classical LeanEval.GroupTheory.Defs Submission.Blueprint
open scoped IsMulCommutative

namespace Work.AppXIField

open Work.ThmF.ChV3

/-- **L0** (App. XI Prop. 2, first half: Schur + little Wedderburn), the area's canonical copy.
The statement is verbatim from the pass-17 design file; the proof is
`L0.field_of_free_comm_action` (`Submission/Work/AppXIField/L0/field_of_free_comm_action.lean`,
via `exists_iota_hom`, `exists_addEquiv_moduleEnd`, `exists_sigma_of_iota`).

A finite abelian group `V` (odd order) on which the finite abelian group `A` acts freely outside
`0` with `|V| ≤ 2|A|+1` is the additive group of a finite field `K`, with `A ↪ Kˣ` acting by
multiplication and `B` acting through `φ` by ring automorphisms of `K`; any two ring
automorphisms of `K` agreeing on `ι(A)` coincide. -/
theorem field_of_free_comm_action {V A B : Type} [AddCommGroup V] [Finite V] [CommGroup A]
    [Finite A] [Group B] [DistribMulAction A V] [DistribMulAction B V] (φ : B →* MulAut A)
    (hcompat : ∀ (b : B) (a : A) (v : V), b • (a • v) = (φ b a) • (b • v))
    (hV : 1 < Nat.card V) (hodd : Odd (Nat.card V))
    (hfree : ∀ (a : A) (v : V), v ≠ 0 → a • v = v → a = 1)
    (hbig : Nat.card V ≤ 2 * Nat.card A + 1) :
    ∃ (K : Type) (_ : Field K) (_ : Fintype K) (e : V ≃+ K) (ι : A →* Kˣ)
      (σ : B →* (K ≃+* K)),
      Function.Injective ι ∧ (∀ (a : A) (v : V), e (a • v) = (ι a : K) * e v) ∧
      (∀ (b : B) (a : A), σ b (ι a : K) = (ι (φ b a) : K)) ∧
      (∀ τ₁ τ₂ : K ≃+* K, (∀ a : A, τ₁ (ι a : K) = τ₂ (ι a : K)) → τ₁ = τ₂) :=
  L0.field_of_free_comm_action φ hcompat hV hodd hfree hbig

theorem nearFieldFieldPropNI_of (hNFp : NearFieldAppXIPropPlus) : NearFieldFieldPropNI := by
  intro G _ _ H Q t s r P m c hm hcq hcomm
  classical
  obtain ⟨m', R, N, hNdef, hm', hfprime, hNR, hRc, hRn, hNn, hcardR, hcq', hfpf, hcommR⟩ :=
    hNFp G H Q t s r P c
  -- ## normality, commutativity, cardinality
  have hNnorm : (N.subgroupOf R).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNR).mpr (hRc.trans hNn)
  letI : (N.subgroupOf R).Normal := hNnorm
  have hfm : orderOf (s * t) ^ m' = orderOf (s * t) ^ m := by rw [← hcq', hcq]
  have hcardV : Nat.card (QuotV G R N) = orderOf (s * t) ^ m :=
    card_quot_eq R N hNR (by rw [hcardR, hfm])
  have hoddV : Odd (Nat.card (QuotV G R N)) := by
    rw [hcardV]; exact (Main.odd_orderOf_st c hfprime).pow
  have hcommV : IsMulCommutative (↥R ⧸ N.subgroupOf R) := isMulCommutative_quot R N hcommR
  letI : IsMulCommutative (↥R ⧸ N.subgroupOf R) := hcommV
  letI : CommGroup (↥R ⧸ N.subgroupOf R) := inferInstance
  letI : AddCommGroup (QuotV G R N) := inferInstance
  letI : Finite (QuotV G R N) := inferInstance
  -- ## the conjugation actions
  have hCQR : CQ Q P ≤ Subgroup.normalizer (R : Set G) := inf_le_right.trans hRn
  have hCQN : CQ Q P ≤ Subgroup.normalizer (N : Set G) := inf_le_right.trans hNn
  have hSigR : Sig H t P ≤ Subgroup.normalizer (R : Set G) := inf_le_right.trans hRn
  have hSigN : Sig H t P ≤ Subgroup.normalizer (N : Set G) := inf_le_right.trans hNn
  obtain ⟨cR, hcR⟩ := Main.exists_conjAut_R (CQ Q P) R hCQR
  obtain ⟨cS, hcS⟩ := Main.exists_conjAut_R (Sig H t P) R hSigR
  have hcKn : ∀ (a : ↥(CQ Q P)) (x : ↥R), x ∈ N.subgroupOf R → cR a x ∈ N.subgroupOf R := by
    intro a x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [hcR a x]
    exact ((Subgroup.mem_normalizer_iff.mp (hCQN a.2)) (x : G)).mp hx
  have hcKs : ∀ (a : ↥(Sig H t P)) (x : ↥R), x ∈ N.subgroupOf R → cS a x ∈ N.subgroupOf R := by
    intro a x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [hcS a x]
    exact ((Subgroup.mem_normalizer_iff.mp (hSigN a.2)) (x : G)).mp hx
  obtain ⟨actR, hactR⟩ := Main.exists_conjAction_quot (CQ Q P) R (N.subgroupOf R) cR hcKn
  obtain ⟨actS, hactS⟩ := Main.exists_conjAction_quot (Sig H t P) R (N.subgroupOf R) cS hcKs
  letI : DistribMulAction ↥(CQ Q P) (QuotV G R N) :=
    distribMulActionAdditiveOfHom ↥(CQ Q P) (↥R ⧸ N.subgroupOf R) actR
  letI : DistribMulAction ↥(Sig H t P) (QuotV G R N) :=
    distribMulActionAdditiveOfHom ↥(Sig H t P) (↥R ⧸ N.subgroupOf R) actS
  obtain ⟨φ, hφ⟩ := Main.sig_conjAction_cq c
  -- ## the quotient map and its action
  let mkv : ↥R → QuotV G R N := fun x => Additive.ofMul (QuotientGroup.mk' (N.subgroupOf R) x)
  have hsurj : ∀ v : QuotV G R N, ∃ x : ↥R, v = mkv x := by
    intro v
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (N.subgroupOf R) (Additive.toMul v)
    refine ⟨x, ?_⟩
    have h1 : mkv x = Additive.ofMul (Additive.toMul v) := congrArg Additive.ofMul hx
    rw [h1]
    simp
  have htoMul : ∀ x : ↥R, Additive.toMul (mkv x) = QuotientGroup.mk' (N.subgroupOf R) x := by
    intro x; rfl
  have hsmulR : ∀ (a : ↥(CQ Q P)) (x : ↥R), a • mkv x = mkv (cR a x) := by
    intro a x
    show Additive.ofMul (actR a (Additive.toMul (Additive.ofMul (QuotientGroup.mk' (N.subgroupOf R) x))))
      = mkv (cR a x)
    rw [htoMul, hactR a x]
  have hsmulS : ∀ (a : ↥(Sig H t P)) (x : ↥R), a • mkv x = mkv (cS a x) := by
    intro a x
    show Additive.ofMul (actS a (Additive.toMul (Additive.ofMul (QuotientGroup.mk' (N.subgroupOf R) x))))
      = mkv (cS a x)
    rw [htoMul, hactS a x]
  -- ## freeness
  have hfree : ∀ (a : ↥(CQ Q P)) (v : QuotV G R N), v ≠ 0 → a • v = v → a = 1 := by
    intro a v hv hav
    obtain ⟨x, rfl⟩ := hsurj v
    rw [hsmulR a x] at hav
    have hxN : (x : G) ∉ N := by
      intro hxN
      refine hv ?_
      have h1 : QuotientGroup.mk' (N.subgroupOf R) x = 1 := by
        rw [QuotientGroup.mk'_apply]
        exact (QuotientGroup.eq_one_iff x).mpr (by rwa [Subgroup.mem_subgroupOf])
      show Additive.ofMul (QuotientGroup.mk' (N.subgroupOf R) x) = 0
      rw [h1]
      rfl
    have hq : QuotientGroup.mk' (N.subgroupOf R) (cR a x) = QuotientGroup.mk' (N.subgroupOf R) x :=
      Additive.ofMul.injective hav
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hq
    have hmem : (cR a x)⁻¹ * x ∈ N.subgroupOf R := QuotientGroup.eq.mp hq
    rw [Subgroup.mem_subgroupOf] at hmem
    have hval : (((cR a x)⁻¹ * x : ↥R) : G)
        = (a : G) * (x : G)⁻¹ * (a : G)⁻¹ * (x : G) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hcR a x]
      group
    rw [hval] at hmem
    exact Subtype.ext (hfpf x⁻¹ (R.inv_mem x.2) (fun h => hxN (by simpa using N.inv_mem h)) a a.2
      (by simpa using hmem))
  -- ## compatibility
  have hcompat : ∀ (b : ↥(Sig H t P)) (a : ↥(CQ Q P)) (v : QuotV G R N),
      b • (a • v) = (φ b a) • (b • v) := by
    intro b a v
    obtain ⟨x, rfl⟩ := hsurj v
    have hrepr : cR (φ b a) (cS b x) = cS b (cR a x) := by
      apply Subtype.ext
      rw [hcR (φ b a) (cS b x), hcS b (cR a x), hcR a x, hcS b x, hφ b a]
      group
    rw [hsmulR a x, hsmulS b (cR a x), hsmulS b x, hsmulR (φ b a) (cS b x), hrepr]
  -- ## the cardinality bounds
  have hV1 : 1 < Nat.card (QuotV G R N) := by
    rw [hcardV]
    have h2 : 2 ≤ orderOf (s * t) := hfprime.two_le
    calc 1 < orderOf (s * t) ^ 1 := by rw [pow_one]; omega
      _ ≤ orderOf (s * t) ^ m := Nat.pow_le_pow_right (by omega) hm
  have hbig : Nat.card (QuotV G R N) ≤ 2 * Nat.card ↥(CQ Q P) + 1 := by
    calc Nat.card (QuotV G R N) = orderOf (s * t) ^ m := hcardV
      _ = Nat.card ↥(CQ Q P) + 1 := hcq.symm
      _ ≤ 2 * Nat.card ↥(CQ Q P) + 1 := by omega
  -- ## L0
  obtain ⟨K, hK, hKt, e, ι, σ, hι, hmul, hσ, hgen⟩ :=
    field_of_free_comm_action (A := ↥(CQ Q P)) (B := ↥(Sig H t P)) φ hcompat hV1 hoddV hfree hbig
  letI : Field K := hK
  letI : Fintype K := hKt
  have hKcard : Nat.card K = orderOf (s * t) ^ m := by
    rw [← hcardV]
    exact (Nat.card_congr e.toEquiv).symm
  haveI : Fact (orderOf (s * t)).Prime := ⟨hfprime⟩
  have hchar : CharP K (orderOf (s * t)) :=
    charP_of_card_eq_prime_pow (p := orderOf (s * t)) (f := m) (by
      rw [← Nat.card_eq_fintype_card, hKcard])
  refine ⟨K, hK, hKt, hchar, ⟨hfprime⟩, σ, hKcard, ?_⟩
  intro w _
  have hcard2 : Nat.card K = Nat.card ↥(CQ Q P) + 1 := by rw [hKcard, ← hcq]
  rw [Main.card_fixedPoints_sigma ι φ σ hι hcard2 hσ w, card_fixedSubtype_CQ (w : G) (φ w) (hφ w)]

end Work.AppXIField
