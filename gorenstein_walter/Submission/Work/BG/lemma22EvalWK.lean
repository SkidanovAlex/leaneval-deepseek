import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.H0Conj
import Submission.Work.BG.CharBridge
import Submission.Work.BG.lemma22Gen
import Submission.Work.BG.invJCard
import Submission.Work.BG.s02_gram
import Submission.Work.BG.s02_lemma22CaseOne
import Submission.Work.BG.conjByH_basic
import Submission.Work.BG.Lambda
import Submission.Work.BG.s02_lamDual
import Submission.Work.BG.lambda_mul_irreducible
import Submission.Work.BG.sconjLam
import Submission.Work.BG.lemma22EvalWAux
import Submission.Work.BG.lemma22EvalWK_Jsum
import Submission.Work.BG.lemma22EvalWK_gen
import Submission.Work.BG.deltaAtTB

/-!
# `Work.BG.lemma22EvalWK` : Bender–Glauberman's Lemma 2.2, the evaluation

`Work.GW2.C16.Lemma22EvalProp D C` is the identity (BG 1981, p. 205)

`Σ_{θ ∈ Irr H} (Σ_{x ∈ J} θ(x))²/θ(1) · (θ, κ^H − ν^H)_H = 2 |J|²`,

`J = invJ C` the involutions of `H ∖ H₀`, `κ` an `s`-invariant linear character of `H₀`
trivial on `S₀`, and `ν = λ_β κ`.

Route: `Work.BG.classSum_expansion` turns the `θ`-sum into the pair sum `Σ_{x,y ∈ J} δ(xy)`
with `δ = (κ − ν)^H`; the two halves are evaluated by the index-two lemmas
`Work.BG.sum_induce_eq_two_mul_sq` / `Work.BG.sum_induce_eq_zero`, using
`Work.BG.lemma22EvalWK_Jsum` to sum an extension of an `s`-invariant `H₀`-character over
`J`, and `χ(t₁)χ(t₂) = χ(t₁t₂)`, which is `κ(t₁t₂) = 1` resp. `λ_β(t₁t₂) = -1`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

variable {G : Type} [Group G] [Finite G]


/-- `sconj` is multiplicative: it is `compHom` along the automorphism `conjMulEquiv`. -/
theorem sconj_mul (C : Sec2Ctx G) (x y : ClassFunction ↥C.P.H0 ℂ) :
    sconj C (x * y) = sconj C x * sconj C y := by
  rfl

/-- **Squares of `λ_β` under an `s`-fixed `λ_β`.**  If `λ_β` is `s`-fixed, then
`λ_β(x)² = 1` for every `x ∈ H₀`: `s x s⁻¹ x ∈ U` lies in the kernel of `λ_β`. -/
theorem lamCF_mul_self_eq_one_of_sconj (C : Sec2Ctx G) (β : quotGroup C.P →* ℂˣ)
    (hfix : sconj C (lamCF C β) = lamCF C β) (x : ↥C.P.H0) :
    lamCF C β x * lamCF C β x = 1 := by
  have hconj : lamCF C β (conjMulEquiv C.P C.s x) = lamCF C β x := by
    have h1 : (sconj C (lamCF C β)) x = (lamCF C β) x := by rw [hfix]
    simpa [sconj, conjByH_apply] using h1
  have hmemU : (conjMulEquiv C.P C.s x * x : ↥C.P.H0) ∈ C.P.U.subgroupOf C.P.H0 := by
    rw [Subgroup.mem_subgroupOf]
    have hval : ((conjMulEquiv C.P C.s x * x : ↥C.P.H0) : G)
        = (C.s : G) * (x : G) * (C.s : G)⁻¹ * (x : G) := by
      rw [Subgroup.coe_mul, conjMulEquiv_apply]
    rw [hval]
    exact C.s_inverts (x : G) x.2
  have hone : lamCF C β (conjMulEquiv C.P C.s x * x) = 1 :=
    Lambda.apply_eq_one_of_mem_U ⟨β, rfl⟩ hmemU
  rw [lamCF_mul_apply C β] at hone
  rw [hconj] at hone
  exact hone

/-- **The `s`-fixed nontrivial linear character of `H₀/U` is `-1` at `t₁t₂`.**

`(t₁t₂)U` generates the cyclic `2`-group `H₀/U` (`Work.BG.lemma22EvalWK_gen`), while
`s`-fixedness forces `λ_β² = 1`: hence `λ_β` is a nontrivial homomorphism `H₀/U → {±1}`,
which is `-1` on a generator. -/
theorem lamCF_fixed_apply_eq_neg_one (D : Work.GW2.BGData G) (C : Sec2Ctx G)
    (hC : Work.GW2.C16.Compat D C) (β : quotGroup C.P →* ℂˣ) (hβ : β ≠ 1)
    (hfix : sconj C (lamCF C β) = lamCF C β) (h : ↥C.P.H0) (hh : (h : G) = D.t1 * D.t2) :
    lamCF C β h = -1 := by
  have hsq : lamCF C β h * lamCF C β h = 1 := lamCF_mul_self_eq_one_of_sconj C β hfix h
  have hsq' : (lamCF C β h) ^ 2 = 1 := by rw [sq]; exact hsq
  have hgen := lemma22EvalWK_gen D C hC h hh
  have hne : lamCF C β h ≠ 1 := by
    intro h1
    apply hβ
    have hquot : β (quotMk C.P h) = 1 := by
      apply Units.ext
      have h2 : ((β (quotMk C.P h) : ℂˣ) : ℂ) = 1 := by
        simpa [lamCF_apply] using h1
      simpa using h2
    refine MonoidHom.ext fun x => ?_
    have hx : x ∈ Subgroup.zpowers (quotMk C.P h) := by rw [hgen]; exact Subgroup.mem_top x
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← hk, map_zpow, hquot, one_zpow, MonoidHom.one_apply]
  rcases (sq_eq_one_iff.mp hsq') with h1 | h1
  · exact absurd h1 hne
  · exact h1

/-- `compHom` along a group isomorphism is injective. -/
theorem compHom_injective_mulEquiv {K L : Type} [Group K] [Group L] (e : K ≃* L) :
    Function.Injective (ClassFunction.compHom (e : K →* L) :
      ClassFunction L ℂ → ClassFunction K ℂ) := by
  intro a b h
  ext l
  have := congrArg (fun f : ClassFunction K ℂ => f (e.symm l)) h
  simpa [ClassFunction.compHom_apply] using this

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem lemma22EvalWK {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    [Fintype ↥C.P.H] [Invertible (Nat.card ↥C.P.H : ℂ)]
    [Invertible (Nat.card ↥(Work.BG.H0in C.P) : ℂ)]
    [Fintype (OddOrder.RepresentationTheory.IrreducibleCharacter ↥C.P.H)] :
    Work.GW2.C16.Lemma22EvalProp D C := by
  intro hC κ β hκirr hκ1 hκinv hκS0 hdisj
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  haveI : Fintype ↥(H0in C.P) := Fintype.ofFinite _
  have h2 : (H0in C.P).index = 2 := by
    rw [← Subgroup.relIndex]; exact C.P.H0_relIndex
  have hs : C.s ∉ H0in C.P := fun hh => C.s_not_mem_H0 (Subgroup.mem_subgroupOf.mp hh)
  set t1 : ↥C.P.H := ⟨D.t1, hC.H_eq.symm ▸ S_le_H D D.t1_mem⟩ with ht1def
  set t2 : ↥C.P.H := ⟨D.t2, hC.H_eq.symm ▸ S_le_H D D.t2_mem⟩ with ht2def
  have ht1 : (t1 : G) = D.t1 := rfl
  have ht2 : (t2 : G) = D.t2 := rfl
  set κ' : ClassFunction ↥(H0in C.P) ℂ :=
    ClassFunction.compHom (H0inEquiv C.P).toMonoidHom κ with hκ'def
  set ν' : ClassFunction ↥(H0in C.P) ℂ :=
    ClassFunction.compHom (H0inEquiv C.P).toMonoidHom (lamCF C β * κ) with hν'def
  have hXinv : ∀ g x : ↥C.P.H, x ∈ invJ C → g * x * g⁻¹ ∈ invJ C := by
    intro g x hx
    rw [invJ_eq_XH C] at hx ⊢
    exact l22c1_XH_conj C g x hx
  have hXN : ∀ x ∈ invJ C, x ∉ H0in C.P := by
    intro x hx hmem
    rw [mem_invJ] at hx
    exact hx.2.2 (Subgroup.mem_subgroupOf.mp hmem)
  -- ### Step 1: rewrite the `θ`-sum as the pair sum over `J`
  have hstep1 :
      (∑ θ : IrreducibleCharacter ↥C.P.H,
          (∑ x ∈ invJ C, (θ : ClassFunction ↥C.P.H ℂ) x) ^ 2 /
              (θ : ClassFunction ↥C.P.H ℂ) 1 *
            ClassFunction.inner
              (indH C κ - indH C (lamCF C β * κ)) (θ : ClassFunction ↥C.P.H ℂ))
        = ∑ x ∈ invJ C, ∑ y ∈ invJ C, dcf C (κ - lamCF C β * κ) (x * y) := by
    have h := classSum_expansion (K := ↥C.P.H) (X := invJ C) hXinv
      (dcf C (κ - lamCF C β * κ))
    rw [← h]
    refine Finset.sum_congr rfl fun θ _ => ?_
    rw [indH_sub_eq_dcf C κ (lamCF C β * κ)]
  rw [hstep1, l22c1_dcf_sub C κ (lamCF C β * κ)]
  have hsplit : (∑ x ∈ invJ C, ∑ y ∈ invJ C, (dcf C κ - dcf C (lamCF C β * κ)) (x * y))
      = (∑ x ∈ invJ C, ∑ y ∈ invJ C, dcf C κ (x * y))
        - (∑ x ∈ invJ C, ∑ y ∈ invJ C, dcf C (lamCF C β * κ) (x * y)) := by
    simp only [ClassFunction.sub_apply, Finset.sum_sub_distrib]
  rw [hsplit]
  -- ### the `κ`-part
  have hκ'irr : IsIrreducibleCharacter κ' := by
    rw [hκ'def]
    exact IsIrreducibleCharacter.compHom_of_surjective (H0inEquiv C.P).surjective hκirr
  have hκ'1 : κ' 1 = 1 := by
    rw [hκ'def, ClassFunction.compHom_apply, map_one]; exact hκ1
  have hκ'inv : ClassFunction.conjBy (H := H0in C.P) C.s κ' = κ' := by
    have h := conjByH_transport C.P C.s κ
    rw [← hκ'def] at h
    rw [show conjByH C.P C.s κ = κ from hκinv] at h
    rw [hκ'def] at h
    exact h.symm
  obtain ⟨χ, hχ⟩ := exists_linear_extension h2 C.s hs κ' hκ'irr hκ'1 hκ'inv
  have hpart1 : (∑ x ∈ invJ C, ∑ y ∈ invJ C, dcf C κ (x * y))
      = 2 * (∑ x ∈ invJ C, (χ x : ℂ)) ^ 2 := by
    have hmain := sum_induce_eq_two_mul_sq (K := ↥C.P.H) (N := H0in C.P) h2 C.s hs κ' hκ'inv χ
      hχ (invJ C) hXN
    rw [← hmain]
    rfl
  have hχsum : (∑ x ∈ invJ C, (χ x : ℂ)) =
      ((Subgroup.centralizer ({D.t1} : Set G)).relIndex D.H : ℂ) * (χ t1 : ℂ) +
        ((Subgroup.centralizer ({D.t2} : Set G)).relIndex D.H : ℂ) * (χ t2 : ℂ) := by
    have h := lemma22EvalWK_Jsum D C hC (linearClassFunction χ)
    simpa [linearClassFunction_apply] using h
  -- `t₁t₂ ∈ H₀`
  have hmemtt : (t1 * t2 : ↥C.P.H) ∈ H0in C.P := by
    rw [Subgroup.mem_subgroupOf]
    rw [show ((t1 * t2 : ↥C.P.H) : G) = D.t1 * D.t2 from by rw [Subgroup.coe_mul, ht1, ht2]]
    rw [hC.H0_eq]
    exact (le_sup_right : D.S0 ≤ D.U ⊔ D.S0) (D.gen ▸ Subgroup.mem_zpowers (D.t1 * D.t2))
  have hcoc : ((⟨t1 * t2, hmemtt⟩ : ↥(H0in C.P)) : ↥C.P.H) = t1 * t2 := rfl
  have hval_eq : ∀ (y : ↥(H0in C.P)),
      ((((H0inEquiv C.P).toMonoidHom y : ↥C.P.H0)) : G) = (y : G) := fun _ => rfl
  -- `χ(t₁t₂) = 1`
  have hχtt : (χ (t1 * t2) : ℂ) = 1 := by
    have h1 : (χ ((⟨t1 * t2, hmemtt⟩ : ↥(H0in C.P)) : ↥C.P.H) : ℂ)
        = κ' ⟨t1 * t2, hmemtt⟩ := hχ ⟨t1 * t2, hmemtt⟩
    rw [hcoc] at h1
    have h2' : κ' ⟨t1 * t2, hmemtt⟩ = 1 := by
      rw [hκ'def, ClassFunction.compHom_apply]
      apply hκS0
      rw [hval_eq ⟨t1 * t2, hmemtt⟩]
      rw [show ((⟨t1 * t2, hmemtt⟩ : ↥(H0in C.P)) : G) = ((t1 * t2 : ↥C.P.H) : G) from rfl]
      rw [show ((t1 * t2 : ↥C.P.H) : G) = D.t1 * D.t2 from by rw [Subgroup.coe_mul, ht1, ht2]]
      exact (D.gen ▸ Subgroup.mem_zpowers (D.t1 * D.t2))
    rw [h1, h2']
  have hχt1sq : (χ t1 : ℂ) ^ 2 = 1 := by
    have h1 : t1 * t1 = (1 : ↥C.P.H) := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_one, ht1,
        show D.t1 * D.t1 = 1 from by rw [← pow_two]; exact t1_sq D]
    have h2' : (χ t1 : ℂ) * (χ t1 : ℂ) = 1 := by
      rw [← Units.val_mul, ← map_mul, h1, map_one, Units.val_one]
    rw [sq]; exact h2'
  have hχt2eq : (χ t2 : ℂ) = (χ t1 : ℂ) := by
    have hmul : (χ t1 : ℂ) * (χ t2 : ℂ) = 1 := by
      rw [← Units.val_mul, ← map_mul]
      exact hχtt
    have hsqt1 : (χ t1 : ℂ) * (χ t1 : ℂ) = 1 := by rw [sq] at hχt1sq; exact hχt1sq
    have hcancel : (χ t1 : ℂ) * (χ t2 : ℂ) = (χ t1 : ℂ) * (χ t1 : ℂ) := by rw [hmul, hsqt1]
    exact mul_left_cancel₀ (by simp) hcancel
  have hpart1' : (∑ x ∈ invJ C, ∑ y ∈ invJ C, dcf C κ (x * y))
      = 2 * ((invJ C).card : ℂ) ^ 2 := by
    have hcard : ((invJ C).card : ℂ)
        = ((Subgroup.centralizer ({D.t1} : Set G)).relIndex D.H : ℂ)
          + ((Subgroup.centralizer ({D.t2} : Set G)).relIndex D.H : ℂ) := by
      have h := invJCard D C hC
      have hk : (D.k : ℂ) =
          ((Subgroup.centralizer ({D.t1} : Set G)).relIndex D.H : ℂ)
          + ((Subgroup.centralizer ({D.t2} : Set G)).relIndex D.H : ℂ) := by
        simp [Work.GW2.BGData.k, Nat.cast_add]
      rw [← hk, ← h]
    rw [hpart1, hχsum, hχt2eq]
    have hsum' : ((Subgroup.centralizer ({D.t1} : Set G)).relIndex D.H : ℂ) * (χ t1 : ℂ) +
          ((Subgroup.centralizer ({D.t2} : Set G)).relIndex D.H : ℂ) * (χ t1 : ℂ)
        = (((Subgroup.centralizer ({D.t1} : Set G)).relIndex D.H : ℂ)
          + ((Subgroup.centralizer ({D.t2} : Set G)).relIndex D.H : ℂ)) * (χ t1 : ℂ) := by
      ring
    rw [hsum', mul_pow, hχt1sq, mul_one, hcard]
  -- ### the `ν`-part
  have hν'irr : IsIrreducibleCharacter ν' := by
    rw [hν'def]
    exact IsIrreducibleCharacter.compHom_of_surjective (H0inEquiv C.P).surjective
      (lambda_mul_irreducible C.P ⟨β, rfl⟩ hκirr)
  have hν'1 : ν' 1 = 1 := by
    simp [hν'def, lamCF_apply, hκ1]
  have hsconj_iff : ∀ (μ : ClassFunction ↥C.P.H0 ℂ),
      ClassFunction.conjBy (H := H0in C.P) C.s
          (ClassFunction.compHom (H0inEquiv C.P).toMonoidHom μ)
        = ClassFunction.compHom (H0inEquiv C.P).toMonoidHom μ ↔ sconj C μ = μ := by
    intro μ
    have htr := conjByH_transport C.P C.s μ
    constructor
    · intro h
      refine compHom_injective_mulEquiv (H0inEquiv C.P) ?_
      change ClassFunction.compHom (H0inEquiv C.P).toMonoidHom (conjByH C.P C.s μ)
        = ClassFunction.compHom (H0inEquiv C.P).toMonoidHom μ
      rw [htr]
      exact h
    · intro h
      rw [← htr, show conjByH C.P C.s μ = μ from h]
  have hpart2 : (∑ x ∈ invJ C, ∑ y ∈ invJ C, dcf C (lamCF C β * κ) (x * y)) = 0 := by
    rcases hdisj with hνne | ⟨hβ, hfix, hk⟩
    · -- the non-`s`-invariant case
      have hne' : ClassFunction.conjBy (H := H0in C.P) C.s ν' ≠ ν' := by
        intro h
        refine hνne ((hsconj_iff (lamCF C β * κ)).mp ?_)
        simpa [hν'def] using h
      have hmain := sum_induce_eq_zero (K := ↥C.P.H) (N := H0in C.P) h2 C.s hs ν' hν'irr hne'
        (invJ C) hXinv hXN
      rw [← hmain]
      rfl
    · -- the `s`-invariant case: `β ≠ 1`, `k₁ = k₂`
      have hinv' : ClassFunction.conjBy (H := H0in C.P) C.s ν' = ν' := by
        refine (hsconj_iff (lamCF C β * κ)).mpr ?_
        rw [sconj_mul C (lamCF C β) κ, hfix, hκinv]
      obtain ⟨χ', hχ'⟩ := exists_linear_extension h2 C.s hs ν' hν'irr hν'1 hinv'
      have hpart2' : (∑ x ∈ invJ C, ∑ y ∈ invJ C, dcf C (lamCF C β * κ) (x * y))
          = 2 * (∑ x ∈ invJ C, (χ' x : ℂ)) ^ 2 := by
        have hmain := sum_induce_eq_two_mul_sq (K := ↥C.P.H) (N := H0in C.P) h2 C.s hs ν' hinv'
          χ' hχ' (invJ C) hXN
        rw [← hmain]
        rfl
      have hχ'sum : (∑ x ∈ invJ C, (χ' x : ℂ)) =
          ((Subgroup.centralizer ({D.t1} : Set G)).relIndex D.H : ℂ) * (χ' t1 : ℂ) +
            ((Subgroup.centralizer ({D.t2} : Set G)).relIndex D.H : ℂ) * (χ' t2 : ℂ) := by
        have h := lemma22EvalWK_Jsum D C hC (linearClassFunction χ')
        simpa [linearClassFunction_apply] using h
      -- `χ'(t₁t₂) = -1`
      have hχ'tt : (χ' (t1 * t2) : ℂ) = -1 := by
        have h1 : (χ' ((⟨t1 * t2, hmemtt⟩ : ↥(H0in C.P)) : ↥C.P.H) : ℂ)
            = ν' ⟨t1 * t2, hmemtt⟩ := hχ' ⟨t1 * t2, hmemtt⟩
        rw [hcoc] at h1
        have h2' : ν' ⟨t1 * t2, hmemtt⟩ = -1 := by
          have hx0 : ((((H0inEquiv C.P).toMonoidHom ⟨t1 * t2, hmemtt⟩ : ↥C.P.H0)) : G)
              = D.t1 * D.t2 := by
            rw [hval_eq ⟨t1 * t2, hmemtt⟩]
            rw [show ((⟨t1 * t2, hmemtt⟩ : ↥(H0in C.P)) : G) = ((t1 * t2 : ↥C.P.H) : G) from rfl]
            rw [show ((t1 * t2 : ↥C.P.H) : G) = D.t1 * D.t2 from by rw [Subgroup.coe_mul, ht1, ht2]]
          have hlb : lamCF C β ((H0inEquiv C.P).toMonoidHom ⟨t1 * t2, hmemtt⟩) = -1 :=
            lamCF_fixed_apply_eq_neg_one D C hC β hβ hfix _ hx0
          have hk1' : κ ((H0inEquiv C.P).toMonoidHom ⟨t1 * t2, hmemtt⟩) = 1 := by
            apply hκS0
            rw [hx0]
            exact (D.gen ▸ Subgroup.mem_zpowers (D.t1 * D.t2))
          rw [hν'def, ClassFunction.compHom_apply, ClassFunction.mul_apply, hlb, hk1', mul_one]
        rw [h1, h2']
      have hχ't1sq : (χ' t1 : ℂ) ^ 2 = 1 := by
        have h1 : t1 * t1 = (1 : ↥C.P.H) := by
          apply Subtype.ext
          rw [Subgroup.coe_mul, Subgroup.coe_one, ht1,
            show D.t1 * D.t1 = 1 from by rw [← pow_two]; exact t1_sq D]
        have h2' : (χ' t1 : ℂ) * (χ' t1 : ℂ) = 1 := by
          rw [← Units.val_mul, ← map_mul, h1, map_one, Units.val_one]
        rw [sq]; exact h2'
      have hχ't2 : (χ' t2 : ℂ) = -((χ' t1 : ℂ)) := by
        have hmul : (χ' t1 : ℂ) * (χ' t2 : ℂ) = -1 := by
          rw [← Units.val_mul, ← map_mul]
          exact hχ'tt
        have hsqt1 : (χ' t1 : ℂ) * (χ' t1 : ℂ) = 1 := by rw [sq] at hχ't1sq; exact hχ't1sq
        have hcancel : (χ' t1 : ℂ) * (χ' t2 : ℂ) = (χ' t1 : ℂ) * (-(χ' t1 : ℂ)) := by
          rw [hmul, mul_neg, hsqt1]
        exact mul_left_cancel₀ (by simp) hcancel
      have hk' : ((Subgroup.centralizer ({D.t1} : Set G)).relIndex D.H : ℂ)
          = ((Subgroup.centralizer ({D.t2} : Set G)).relIndex D.H : ℂ) := by rw [hk]
      rw [hpart2', hχ'sum, hχ't2, hk']
      ring
  rw [hpart1', hpart2, sub_zero]

end Work.BG
