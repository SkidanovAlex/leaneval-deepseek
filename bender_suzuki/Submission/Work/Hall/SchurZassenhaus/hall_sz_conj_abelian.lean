import Mathlib
import Submission.Work.Hall.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Schur–Zassenhaus: conjugacy of complements of an abelian normal Hall subgroup

This file proves that if `N` is an abelian normal subgroup of a finite group `G` whose order is
coprime to its index (an abelian normal Hall subgroup), then any two complements `H`, `K` of `N`
are conjugate.

The argument is the classical one.  Writing `G = N ⋊ H = N ⋊ K`, for each `x : H` let
`x = β x * γ x` be the unique decomposition with `β x ∈ N` and `γ x ∈ K`.  Then `β` is a crossed
homomorphism (`1`-cocycle) for the conjugation action of `H` on `N`, and since `|H|` is coprime to
`|N|` every such crossed homomorphism is a coboundary: there is `a ∈ N` with
`β x = x * a * x⁻¹ * a⁻¹`.  Substituting into `γ x = (β x)⁻¹ * x` shows that `γ x = a * x * a⁻¹`,
whence `K = a * H * a⁻¹`.

The auxiliary lemma `exists_coboundary` is the abstract statement that `H¹(P, A) = 0` whenever the
finite group `P` acts on the finite abelian group `A` with `|A|` coprime to `|P|`.
-/

open scoped Pointwise IsMulCommutative

set_option linter.style.haveILetI false

namespace Work.Hall.SchurZassenhaus

/-- If a finite group `P` acts on a finite abelian group `A` (via `φ : P →* MulAut A`) with
`Nat.card A` coprime to `Nat.card P`, then every crossed homomorphism (1-cocycle)
`f : P → A`, i.e. every `f` with `f (x * y) = f x * φ x (f y)`, is a coboundary:
there is `a : A` with `f x = φ x a * a⁻¹` for all `x`. -/
theorem exists_coboundary {P A : Type*} [Group P] [Group A] [IsMulCommutative A]
    [Finite P] [Finite A] (φ : P →* MulAut A) (hcop : (Nat.card A).Coprime (Nat.card P))
    (f : P → A) (hf : ∀ x y, f (x * y) = f x * φ x (f y)) :
    ∃ a : A, ∀ x, f x = φ x a * a⁻¹ := by
  letI : Fintype P := Fintype.ofFinite P
  set Aprod : A := ∏ x, f x with hAprod
  have key : ∀ y : P, φ y Aprod = Aprod * (f y ^ Nat.card P)⁻¹ := by
    intro y
    have h1 : ∀ x : P, φ y (f x) = (f y)⁻¹ * f (y * x) := by
      intro x; rw [hf y x]; group
    calc φ y Aprod
        = φ y (∏ x, f x) := by rw [hAprod]
      _ = ∏ x, φ y (f x) := by rw [map_prod]
      _ = ∏ x, (f y)⁻¹ * f (y * x) := Finset.prod_congr rfl (fun x _ => h1 x)
      _ = (∏ _x : P, (f y)⁻¹) * ∏ x, f (y * x) := Finset.prod_mul_distrib
      _ = (f y)⁻¹ ^ Fintype.card P * ∏ x, f (y * x) := by
            rw [Finset.prod_const, Finset.card_univ]
      _ = (f y)⁻¹ ^ Fintype.card P * Aprod := by
            rw [hAprod]; congr 1; exact Equiv.prod_comp (Equiv.mulLeft y) f
      _ = Aprod * (f y ^ Nat.card P)⁻¹ := by
            rw [Nat.card_eq_fintype_card, inv_pow]; rw [mul_comm]
  refine ⟨(powCoprime (G := A) hcop).symm Aprod⁻¹, fun y => ?_⟩
  set a : A := (powCoprime (G := A) hcop).symm Aprod⁻¹ with ha
  have han : a ^ Nat.card P = Aprod⁻¹ := by
    rw [ha, ← powCoprime_apply (G := A) hcop]; exact Equiv.apply_symm_apply _ _
  refine (powCoprime (G := A) hcop).injective ?_
  rw [powCoprime_apply, powCoprime_apply]
  have e2 : (φ y a * a⁻¹) ^ Nat.card P = (φ y Aprod)⁻¹ * Aprod := by
    rw [mul_pow, inv_pow]
    rw [← map_pow (φ y) a (Nat.card P), han, map_inv, inv_inv]
  have e1 : f y ^ Nat.card P = (φ y Aprod)⁻¹ * Aprod := by
    rw [key y]; group
  rw [e1, e2]

/-- **Schur–Zassenhaus (abelian case)**: complements of an abelian normal Hall subgroup are
conjugate. -/
theorem hall_sz_conj_abelian {G : Type*} [Group G] [Finite G] {N H K : Subgroup G} [N.Normal]
    [IsMulCommutative N] (hc : (Nat.card N).Coprime N.index) (hH : N.IsComplement' H)
    (hK : N.IsComplement' K) : ∃ g : G, K = H.map (MulAut.conj g).toMonoidHom := by
  -- `|H|` coincides with the index of `N`, hence is coprime to `|N|`.
  have hcardH : Nat.card H = N.index := (Subgroup.IsComplement'.symm hH).index_eq_card.symm
  have hcop : (Nat.card N).Coprime (Nat.card H) := by rw [hcardH]; exact hc
  -- Unique decomposition of the elements of `H` along `G = N * K`.
  let β : H → N := fun x => (hK.existsUnique (x : G)).choose.1
  let γ : H → K := fun x => (hK.existsUnique (x : G)).choose.2
  have hβγ : ∀ x : H, (β x : G) * (γ x : G) = (x : G) :=
    fun x => (hK.existsUnique (x : G)).choose_spec.1
  have hβγ' : ∀ x : H, (x : G) = (β x : G) * (γ x : G) := fun x => (hβγ x).symm
  -- Elements of the abelian subgroup `N` commute in `G`.
  have hcommN : ∀ a b : N, (a : G) * (b : G) = (b : G) * (a : G) := by
    intro a b; simpa using congrArg (Subtype.val) (mul_comm a b)
  -- Conjugation by `x` agrees with conjugation by `γ x` on `N` (they differ by `β x ∈ N`).
  have hconj : ∀ x y : H,
      (x : G) * (β y : G) * (x : G)⁻¹ = (γ x : G) * (β y : G) * (γ x : G)⁻¹ := by
    intro x y
    have hd : (β x : G) * ((γ x : G) * (β y : G) * (γ x : G)⁻¹) * (β x : G)⁻¹
        = (γ x : G) * (β y : G) * (γ x : G)⁻¹ := by
      have hmem : (γ x : G) * (β y : G) * (γ x : G)⁻¹ ∈ N :=
        Subgroup.Normal.conj_mem (inferInstance : N.Normal) (β y : G) (β y).2 (γ x : G)
      have := hcommN (β x) ⟨_, hmem⟩
      rw [this, mul_assoc, mul_inv_cancel, mul_one]
    have key : (x : G) * (β y : G) * (x : G)⁻¹
        = (β x : G) * ((γ x : G) * (β y : G) * (γ x : G)⁻¹) * (β x : G)⁻¹ := by
      rw [hβγ' x]; group
    rw [key, hd]
  -- The conjugation action of `H` on `N`.
  let φ : H →* MulAut N := MulAut.conjNormal.comp H.subtype
  have hφapply : ∀ (x : H) (a : N), ((φ x a : N) : G) = (x : G) * (a : G) * (x : G)⁻¹ := by
    intro x a
    show ((MulAut.conjNormal (x : G)) a : G) = _
    rw [MulAut.conjNormal_apply]
  -- `β` is a crossed homomorphism.
  have hcross : ∀ x y : H, β (x * y) = β x * φ x (β y) := by
    intro x y
    have hmem : ((β x * φ x (β y) : N) : G) * ((γ x * γ y : K) : G) = ((x * y : H) : G) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hφapply, hconj x y]
      rw [show ((x * y : H) : G) = (x : G) * (y : G) from rfl, hβγ' x, hβγ' y]
      group
    have huniq := (hK.existsUnique ((x * y : H) : G)).choose_spec.2
    have hdec : ((β x * φ x (β y), γ x * γ y) : N × K) =
        (hK.existsUnique (((x * y : H) : G))).choose := huniq _ hmem
    exact (congrArg Prod.fst hdec).symm
  obtain ⟨a, hβa⟩ := exists_coboundary φ hcop β hcross
  -- Consequence for `γ`.
  have hγa : ∀ x : H, (γ x : G) = (a : G) * (x : G) * (a : G)⁻¹ := by
    intro x
    have h1 : (β x : G) = (x : G) * (a : G) * (x : G)⁻¹ * (a : G)⁻¹ := by
      rw [hβa x, Subgroup.coe_mul, Subgroup.coe_inv, hφapply]
    have h2 : (γ x : G) = (β x : G)⁻¹ * (x : G) := by
      rw [← hβγ x, inv_mul_cancel_left]
    rw [h2, h1]; group
  -- The two complements have the same order.
  have hcardK : Nat.card K = Nat.card H := by
    have h1 := hH.card_mul_card
    have h2 := hK.card_mul_card
    have hN : 0 < Nat.card N := Nat.card_pos
    exact Nat.mul_left_cancel hN (h2.trans h1.symm)
  refine ⟨(a : G), ?_⟩
  have hle : H.map (MulAut.conj (a : G)).toMonoidHom ≤ K := by
    intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    show (MulAut.conj (a : G)) x ∈ K
    rw [MulAut.conj_apply, ← hγa ⟨x, hx⟩]
    exact (γ ⟨x, hx⟩).2
  have hcard : Nat.card K = Nat.card (H.map (MulAut.conj (a : G)).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj (a : G)).toMonoidHom)
      (MulAut.conj (a : G)).injective]
    exact hcardK
  exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)).symm

end Work.Hall.SchurZassenhaus
