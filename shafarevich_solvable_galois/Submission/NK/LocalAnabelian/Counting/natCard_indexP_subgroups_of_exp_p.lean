/-
# Counting subgroups of index `p` in a finite abelian group of exponent `p`

If `A` is a finite abelian group with `a ^ p = 1` for every `a` and `p` is prime, then `A`
is an elementary abelian `p`-group, i.e. a vector space over `F_p = ZMod p`, and the number
of subgroups of index `p` is `(Nat.card A - 1) / (p - 1)`.

The proof goes through the `F_p`-vector space structure.  Subgroups of index `p` of `A`
correspond to codimension-one submodules of `Additive A`, which are exactly the kernels of
the nonzero elements of the dual `Module.Dual (ZMod p) (Additive A)`.  A finite module over
a finite field is equinumerous with its dual, so that dual has `Nat.card A` elements, hence
`Nat.card A - 1` nonzero ones; each kernel arises from exactly `p - 1` of them.
-/
import Mathlib
import Submission.NK.LocalAnabelian.Counting.natCard_eq_mul_card_of_fiber_natCard
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalAnabelian.Counting

/-- The set of nonzero elements of a finite additive group has one element less than the
group itself. -/
lemma natCard_subtype_ne_zero (M : Type*) [AddCommGroup M] [Finite M] :
    Nat.card {x : M // x ≠ 0} = Nat.card M - 1 := by
  have hM : Fintype M := Fintype.ofFinite M
  have hS : Fintype {x : M // x ≠ 0} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl (fun x : M => x = 0)]
  have h1 : Fintype.card {x : M // x = 0} = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨⟨0, rfl⟩, fun b => Subtype.ext b.2⟩
  rw [h1]

/-- A finite module over a finite field has as many linear functionals as elements:
the dual has the same dimension. -/
lemma dualNatCard_eq (p : ℕ) [Fact p.Prime] (M : Type*) [AddCommGroup M] [Module (ZMod p) M]
    [Finite M] : Nat.card (Module.Dual (ZMod p) M) = Nat.card M := by
  have hK : Module.Finite (ZMod p) M := Module.Finite.of_finite
  have h1 := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Module.Dual (ZMod p) M)
  have h2 := Module.natCard_eq_pow_finrank (K := ZMod p) (V := M)
  rw [h1, h2, Subspace.dual_finrank_eq]

/-- A nonzero linear functional on a finite module has image `⊤`, hence kernel of index
`p`. -/
lemma index_ker_of_ne_zero (p : ℕ) (hp : p.Prime) (V : Type*) [AddCommGroup V]
    [Module (ZMod p) V] [Finite V] (f : Module.Dual (ZMod p) V) (hf : f ≠ 0) :
    (f.ker).toAddSubgroup.index = p := by
  have hprime : Fact p.Prime := ⟨hp⟩
  have hfin : Module.Finite (ZMod p) V := Module.Finite.of_finite
  rw [AddSubgroup.index_eq_card]
  show Nat.card (V ⧸ LinearMap.ker f) = p
  rw [Nat.card_congr f.quotKerEquivRange.toEquiv]
  rw [Module.Dual.range_eq_top_of_ne_zero hf]
  rw [Nat.card_congr (Submodule.topEquiv (R := ZMod p) (M := ZMod p)).toEquiv]
  exact Nat.card_zmod p

/-- If `M` has prime cardinality `p`, a nonzero linear functional on `M` has trivial
kernel. -/
lemma ker_eq_bot_of_ne_zero_of_natCard_prime (p : ℕ) (hp : p.Prime) {M : Type*}
    [AddCommGroup M] [Module (ZMod p) M] (hM : Nat.card M = p)
    (g : M →ₗ[ZMod p] ZMod p) (hg : g ≠ 0) : g.ker = ⊥ := by
  have hKtop : g.ker ≠ ⊤ := by
    intro h
    apply hg
    ext x
    have hx : x ∈ g.ker := by rw [h]; trivial
    rwa [LinearMap.mem_ker] at hx
  have hcard := Submodule.card_eq_card_quotient_mul_card (g.ker)
  rw [hM] at hcard
  have hdiv : Nat.card ↥(g.ker) ∣ p := ⟨Nat.card (M ⧸ g.ker), hcard⟩
  rcases hp.eq_one_or_self_of_dvd _ hdiv with h1 | hp'
  · rw [Submodule.eq_bot_iff]
    intro x hx
    have hsub : Subsingleton ↥(g.ker) := (Nat.card_eq_one_iff_unique.mp h1).1
    exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : ↥(g.ker)) ⟨0, (g.ker).zero_mem⟩)
  · exfalso
    have hq : Nat.card (M ⧸ g.ker) = 1 := by
      rw [hp'] at hcard
      exact Nat.mul_left_cancel hp.pos (by rw [mul_one]; exact hcard.symm)
    have hii : (g.ker).toAddSubgroup.index = 1 := by
      rw [AddSubgroup.index_eq_card]
      show Nat.card (M ⧸ g.ker) = 1
      exact hq
    exact hKtop (Submodule.toAddSubgroup_injective (AddSubgroup.index_eq_one.mp hii))

/-- The map sending a nonzero linear functional to its kernel. -/
noncomputable def kerMap (p : ℕ) (hp : p.Prime) (V : Type*) [AddCommGroup V]
    [Module (ZMod p) V] [Finite V] :
    {f : Module.Dual (ZMod p) V // f ≠ 0} →
      {W : Submodule (ZMod p) V // W.toAddSubgroup.index = p} :=
  fun f => ⟨f.1.ker, index_ker_of_ne_zero p hp V f.1 f.2⟩

/-- The fibre of `kerMap` over `W` consists exactly of the nonzero functionals whose
kernel is `W`. -/
noncomputable def kerMapFiberEquiv (p : ℕ) (hp : p.Prime) (V : Type*) [AddCommGroup V]
    [Module (ZMod p) V] [Finite V] (W : Submodule (ZMod p) V) (hW : W.toAddSubgroup.index = p) :
    {a : {f : Module.Dual (ZMod p) V // f ≠ 0} // kerMap p hp V a = ⟨W, hW⟩}
      ≃ {f : Module.Dual (ZMod p) V // f ≠ 0 ∧ f.ker = W} where
  toFun a := ⟨a.1.1, a.1.2, by
    have h := congrArg Subtype.val a.2
    simpa [kerMap] using h⟩
  invFun f := ⟨⟨f.1, f.2.1⟩, by
    apply Subtype.ext
    simpa [kerMap] using f.2.2⟩
  left_inv a := Subtype.ext rfl
  right_inv f := Subtype.ext rfl

/-- Exactly `p - 1` nonzero functionals have a prescribed kernel of index `p`. -/
lemma natCard_ker_fiber (p : ℕ) (hp : p.Prime) (V : Type*) [AddCommGroup V]
    [Module (ZMod p) V] [Finite V] (W : Submodule (ZMod p) V)
    (hW : W.toAddSubgroup.index = p) :
    Nat.card {f : Module.Dual (ZMod p) V // f ≠ 0 ∧ f.ker = W} = p - 1 := by
  have hprime : Fact p.Prime := ⟨hp⟩
  have hVW : Nat.card (V ⧸ W) = p := by
    have h := AddSubgroup.index_eq_card W.toAddSubgroup
    rw [hW] at h
    exact h.symm
  have hfinVW : Finite (V ⧸ W) := Nat.finite_of_card_ne_zero (by rw [hVW]; exact hp.ne_zero)
  have hdual : Nat.card ((V ⧸ W) →ₗ[ZMod p] ZMod p) = p := by
    have h := dualNatCard_eq p (V ⧸ W)
    rw [hVW] at h
    exact h
  have hfinDual : Finite ((V ⧸ W) →ₗ[ZMod p] ZMod p) :=
    Nat.finite_of_card_ne_zero (by rw [hdual]; exact hp.ne_zero)
  have hcount : Nat.card {g : (V ⧸ W) →ₗ[ZMod p] ZMod p // g ≠ 0} = p - 1 := by
    rw [natCard_subtype_ne_zero, hdual]
  rw [← hcount]
  apply Nat.card_congr
  exact { toFun := fun f => ⟨W.liftQ f.1 f.2.2.symm.le, by
            intro h
            apply f.2.1
            rw [← Submodule.liftQ_mkQ W f.1 f.2.2.symm.le, h, LinearMap.zero_comp]⟩
          invFun := fun g => ⟨g.1.comp W.mkQ, by
              intro h
              apply g.2
              refine LinearMap.ext fun y => ?_
              obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective W y
              simpa [LinearMap.comp_apply] using LinearMap.congr_fun h x,
              by rw [LinearMap.ker_comp,
                ker_eq_bot_of_ne_zero_of_natCard_prime p hp hVW g.1 g.2,
                Submodule.comap_bot, Submodule.ker_mkQ]⟩
          left_inv := fun f => Subtype.ext (Submodule.liftQ_mkQ W f.1 f.2.2.symm.le)
          right_inv := fun g => Subtype.ext (by
              ext y
              rw [Submodule.liftQ_mkQ]) }

/-- The number of submodules of index `p` of a finite `ZMod p`-module. -/
theorem natCard_indexP_submodule (p : ℕ) (hp : p.Prime) (V : Type*) [AddCommGroup V]
    [Module (ZMod p) V] [Finite V] :
    Nat.card {W : Submodule (ZMod p) V // W.toAddSubgroup.index = p} =
      (Nat.card V - 1) / (p - 1) := by
  have hpos : 0 < p - 1 := by have h2 := hp.two_le; omega
  have hfinB : Finite {W : Submodule (ZMod p) V // W.toAddSubgroup.index = p} :=
    Finite.of_injective (fun x => (x.1 : Set V))
      (fun a b h => Subtype.ext (SetLike.coe_injective h))
  have hfib : ∀ b : {W : Submodule (ZMod p) V // W.toAddSubgroup.index = p},
      Nat.card {a : {f : Module.Dual (ZMod p) V // f ≠ 0} // kerMap p hp V a = b} = p - 1 := by
    rintro ⟨W, hW⟩
    rw [Nat.card_congr (kerMapFiberEquiv p hp V W hW)]
    exact natCard_ker_fiber p hp V W hW
  have hmain := natCard_eq_mul_card_of_fiber_natCard (kerMap p hp V) (p - 1) hpos hfib
  have hcard : Nat.card {f : Module.Dual (ZMod p) V // f ≠ 0} = Nat.card V - 1 := by
    have hprime : Fact p.Prime := ⟨hp⟩
    have hcardD : Nat.card (Module.Dual (ZMod p) V) = Nat.card V := dualNatCard_eq p V
    have hfinD : Finite (Module.Dual (ZMod p) V) :=
      Nat.finite_of_card_ne_zero
        (by rw [hcardD]; exact Nat.card_ne_zero.mpr ⟨⟨0⟩, inferInstance⟩)
    rw [natCard_subtype_ne_zero, hcardD]
  rw [hcard] at hmain
  rw [hmain]
  exact (Nat.mul_div_cancel_left _ hpos).symm

/-- **Counting index-`p` subgroups of a finite abelian group of exponent `p`.**  If every
element of the finite abelian group `A` satisfies `a ^ p = 1` with `p` prime, then the
number of subgroups of index `p` is `(Nat.card A - 1) / (p - 1)`. -/
theorem natCard_indexP_subgroups_of_exp_p (A : Type*) [CommGroup A] [Finite A] (p : ℕ)
    (hp : p.Prime) (hexp : ∀ a : A, a ^ p = 1) :
    Nat.card {C : Subgroup A // C.index = p} = (Nat.card A - 1) / (p - 1) := by
  have hmod : Module (ZMod p) (Additive A) :=
    AddCommGroup.zmodModule (fun x => by
      apply Additive.toMul.injective
      simpa using hexp (Additive.toMul x))
  have hbridge : Nat.card {C : Subgroup A // C.index = p}
      = Nat.card {W : Submodule (ZMod p) (Additive A) // W.toAddSubgroup.index = p} := by
    let e : Subgroup A ≃o Submodule (ZMod p) (Additive A) :=
      (Subgroup.toAddSubgroup).trans (AddSubgroup.toZModSubmodule p)
    have he : ∀ C : Subgroup A, (e C).toAddSubgroup.index = C.index := by
      intro C
      show (AddSubgroup.toZModSubmodule p (Subgroup.toAddSubgroup C)).toAddSubgroup.index
        = C.index
      rw [AddSubgroup.toZModSubmodule_toAddSubgroup, Subgroup.index_toAddSubgroup]
    apply Nat.card_congr
    refine Equiv.subtypeEquiv e.toEquiv (fun C => ?_)
    show C.index = p ↔ (e C).toAddSubgroup.index = p
    rw [he C]
  rw [hbridge, natCard_indexP_submodule p hp (Additive A), Nat.card_congr Additive.toMul]

end NK.LocalAnabelian.Counting
