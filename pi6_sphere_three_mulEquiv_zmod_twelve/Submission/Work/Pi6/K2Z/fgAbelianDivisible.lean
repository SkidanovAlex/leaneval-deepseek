import Mathlib
import Submission.Work.Pi6.EMZ.Defs
import Submission.Work.Pi6.EMZ.groupSubsingleton
import Submission.Work.Pi6.EMZ.finiteTrivial
import Submission.Work.StemsB.fg_abelian_decomposition
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false

/-!
# A finitely generated abelian group divisible by *every* prime is trivial

The goal of this file.  Let `A` be a finitely generated abelian group which is `p`-divisible
for every prime `p`, i.e. multiplication by `p` is onto, equivalently `A ⧸ p·A` is trivial
(`Work.Pi6.EMZ.subsingleton_quot_pH_iff`).

The structure theorem (`Work.StemsB.fg_abelian_decomposition`) writes `A ≃+ ℤ^r × F` with `F`
finite.  `2`-divisibility has no square root of the constant function `1`, so the free part dies:
`r = 0` (`Work.Pi6.EMZ.freePart_vanishes`).  Divisibility by every prime then passes to the finite
group `F`; on a finite group multiplication by `p` is onto hence injective, so `F` has no element
of prime order, and such a finite group is trivial (`Work.Pi6.EMZ.finiteTrivial`).  Hence `A = 0`.
-/

namespace Work.Pi6.K2Z

/-- **A finitely generated abelian group that is `p`-divisible for every prime `p` is trivial.** -/
theorem fgAbelianDivisible (A : Type) [AddCommGroup A] [Module.Finite ℤ A]
    (h : ∀ p : ℕ, p.Prime → Subsingleton (A ⧸ Work.Pi6.EMZ.pH p A)) :
    Subsingleton A := by
  obtain ⟨r, F, hFadd, hFfin, ⟨e⟩⟩ := Work.StemsB.fg_abelian_decomposition A
  -- `A` is `2`-divisible, so the free part of the decomposition vanishes.
  have hd2 : ∀ x : A, ∃ y : A, 2 • y = x :=
    Work.Pi6.EMZ.subsingleton_quot_pH_iff.mp (h 2 Nat.prime_two)
  have hr : r = 0 := Work.Pi6.EMZ.freePart_vanishes r F A e hd2
  subst hr
  -- Divisibility by every prime passes to the finite part `F`.
  have hdivF : ∀ (p : ℕ), p.Prime → ∀ z : F, ∃ w : F, p • w = z := by
    intro p hp z
    obtain ⟨b, hb⟩ :=
      Work.Pi6.EMZ.subsingleton_quot_pH_iff.mp (h p hp) (e.symm ((0 : Fin 0 → ℤ), z))
    refine ⟨(e b).2, ?_⟩
    have heq : ((0 : Fin 0 → ℤ), z) = p • e b := by
      rw [← map_nsmul, hb, AddEquiv.apply_symm_apply]
    have h2 := congrArg (fun t : (Fin 0 → ℤ) × F => t.2) heq
    simpa using h2.symm
  have htorF : ∀ (p : ℕ), p.Prime → ∀ x : F, p • x = 0 → x = 0 := by
    intro p hp x hx
    have hsurj : Function.Surjective (fun w : F => p • w) := fun z => hdivF p hp z
    have hinj : Function.Injective (fun w : F => p • w) :=
      Finite.injective_iff_surjective.mpr hsurj
    exact hinj (by simpa using hx)
  have hsubF : Subsingleton F :=
    Work.Pi6.EMZ.finiteTrivial F (hdivF 2 Nat.prime_two) (fun p hp _ => hdivF p hp) (fun p hp _ => htorF p hp)
  -- Hence `A = 0`.
  refine ⟨fun a b => ?_⟩
  have h1 : e a = e b := by
    refine Prod.ext ?_ ?_
    · exact funext fun i => i.elim0
    · exact hsubF.elim _ _
  exact e.injective h1

end Work.Pi6.K2Z
