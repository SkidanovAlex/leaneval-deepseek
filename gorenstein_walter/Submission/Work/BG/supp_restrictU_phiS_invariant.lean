import Mathlib
import Submission.Work.BG.L33DDefs

namespace OddOrder.RepresentationTheory.ClassFunction

/-- **Invariance of the inner product under an invariant automorphism.**

If a class function `f` on a finite group `H` is invariant under an automorphism `e` of `H`,
then precomposing the *second* argument of the inner product with `e` does not change the
pairing: `⟨f, a ∘ e⟩ = ⟨f, a⟩`.

This is the elementary reindexing `Σ_x f x · star (a (e x)) = Σ_y f (e⁻¹ y) · star (a y)`,
where the invariance of `f` under `e` (equivalently, under `e⁻¹`) converts `f (e⁻¹ y)` back
into `f y`. It is the class-function form of "the support of `⟨f, ·⟩` is closed under the
symmetries of `f`". -/
theorem inner_compHom_eq_of_invariant {H : Type*} [Group H] [Fintype H] {k : Type*}
    [CommRing k] [StarRing k] [Invertible (Nat.card H : k)]
    (e : H ≃* H) (f a : ClassFunction H k) (hf : ∀ x, f (e x) = f x) :
    inner f (compHom e.toMonoidHom a) = inner f a := by
  have hfix : compHom e.toMonoidHom f = f := by
    ext x; exact hf x
  have h := inner_compHom_mulEquiv e f a
  rw [hfix] at h
  exact h

end OddOrder.RepresentationTheory.ClassFunction

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Subgroup

/-- **Support of `ν|_U` is `φS`-invariant.** If `a''` pairs nontrivially with the restriction
`ν|_U` of a class function `ν` of `H₀` to `U = O(H)`, then it also pairs nontrivially with the
pullback of `a''` along the conjugation action `φS s₀` of an element `s₀ ∈ S₀` on `U`.

The mathematical point is that `s₀ ∈ S₀ ≤ H₀` acts on `U` as an automorphism by conjugation,
and `ν|_U` is invariant under it because `ν` is a class function of `H₀` (indeed, `ν` need only
be a class function, not irreducible). Thus reindexing the defining sum by the automorphism
`φS s₀` leaves `⟨ν|_U, ·⟩` unchanged, so the support of that functional is `φS s₀`-invariant. -/
theorem supp_restrictU_phiS_invariant {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) (hDC : Work.GW2.C16.Compat D C)
    [Fintype ↥C.P.H0] [Fintype ↥(Work.GW2.C16.Uin C)]
    [Invertible (Nat.card ↥(Work.GW2.C16.Uin C) : ℂ)]
    {ν : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ}
    (hν : OddOrder.RepresentationTheory.IsIrreducibleCharacter ν)
    {a'' : OddOrder.RepresentationTheory.ClassFunction ↥(Work.GW2.C16.Uin C) ℂ}
    (ha'' : OddOrder.RepresentationTheory.ClassFunction.inner
      (OddOrder.RepresentationTheory.ClassFunction.restrict (Work.GW2.C16.Uin C) ν) a'' ≠ 0)
    (s₀ : ↥(D.S)) (hs₀ : (s₀ : G) ∈ D.S0) :
    OddOrder.RepresentationTheory.ClassFunction.inner
      (OddOrder.RepresentationTheory.ClassFunction.restrict (Work.GW2.C16.Uin C) ν)
      (OddOrder.RepresentationTheory.ClassFunction.compHom
        (Work.BG.L33D.phiS D C hDC s₀).toMonoidHom a'') ≠ 0 := by
  -- `s₀ ∈ S₀ ≤ U ⊔ S₀ = H₁ D = C.P.H0`, so conjugation by `s₀` is an inner automorphism of `H₀`.
  have hs₀H0 : (s₀ : G) ∈ C.P.H0 := by
    rw [hDC.H0_eq]
    exact Subgroup.mem_sup_right hs₀
  set s₀h : ↥C.P.H0 := ⟨(s₀ : G), hs₀H0⟩ with hs₀hdef
  -- Unfolding `φS s₀` as conjugation by `s₀h` inside `H₀`.
  have hphi : ∀ u : ↥(Uin C),
      ((Work.BG.L33D.phiS D C hDC s₀ u : ↥(Uin C)) : ↥C.P.H0)
        = s₀h * (u : ↥C.P.H0) * s₀h⁻¹ := by
    intro u
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hs₀hdef]
    exact Work.BG.L33D.phiS_apply D C hDC s₀ u
  -- `ν|_U` is invariant under `φS s₀`, since `ν` is a class function of `H₀`.
  have hf : ∀ u : ↥(Uin C),
      ClassFunction.restrict (Uin C) ν (Work.BG.L33D.phiS D C hDC s₀ u)
        = ClassFunction.restrict (Uin C) ν u := by
    intro u
    show ν ((Work.BG.L33D.phiS D C hDC s₀ u : ↥(Uin C)) : ↥C.P.H0) = ν (u : ↥C.P.H0)
    rw [hphi u, ν.conj_eq (u : ↥C.P.H0) s₀h]
  have hmain := ClassFunction.inner_compHom_eq_of_invariant
    (Work.BG.L33D.phiS D C hDC s₀) (ClassFunction.restrict (Uin C) ν) a'' hf
  rw [hmain]
  exact ha''

end Work.BG
