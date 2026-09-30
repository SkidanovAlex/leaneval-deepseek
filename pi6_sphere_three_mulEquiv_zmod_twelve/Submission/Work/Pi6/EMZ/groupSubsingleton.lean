import Mathlib
import Submission.Work.Pi6.EMZ.Defs
import Submission.Work.StemsB.fg_abelian_decomposition
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Pi6.EMZ

noncomputable section

/-- **The free summand of a finitely generated abelian group dies when the group is
`2`-divisible.**  `ℤ ^ r` has no square root of the constant function `1` as soon as `r ≥ 1`,
so a `2`-divisible group isomorphic to `ℤ ^ r × F` must have `r = 0`. -/
theorem freePart_vanishes (r : ℕ) (F : Type) [AddCommGroup F] (G : Type) [AddCommGroup G]
    (e : G ≃+ ((Fin r → ℤ) × F)) (h : ∀ x : G, ∃ y : G, 2 • y = x) : r = 0 := by
  by_contra hr
  have hi : 0 < r := Nat.pos_of_ne_zero hr
  obtain ⟨z, hz⟩ := h (e.symm ((fun _ : Fin r => (1 : ℤ)), (0 : F)))
  -- `2 • e z = (fun _ => 1, 0)`, so the `⟨0, hi⟩`-entry of `e z` is a square root of `1` in `ℤ`
  have hEq : ((2 : ℕ) • e z).1 ⟨0, hi⟩ = 1 := by
    rw [← map_nsmul, hz, AddEquiv.apply_symm_apply]
  have hfour : ((2 : ℕ) • e z).1 ⟨0, hi⟩ = (2 : ℤ) * (e z).1 ⟨0, hi⟩ := by
    simp [Prod.smul_fst, Pi.smul_apply]
  rw [hfour] at hEq
  obtain h1 | h1 := Int.eq_one_or_neg_one_of_mul_eq_one hEq <;> omega

/-- **A finite abelian group with no element of prime order is trivial.**  If `x ≠ 0` then its
additive order `n` is `> 1`; for a prime `p ∣ n`, written `n = p * m`, the element `m • x` has
additive order exactly `p`, so it is a nonzero element killed by `p`. -/
theorem finite_pTorsionFree_zero (F : Type) [AddCommGroup F] [Finite F]
    (h : ∀ p : ℕ, p.Prime → ∀ x : F, p • x = 0 → x = 0) : Subsingleton F := by
  have hzero : ∀ x : F, x = 0 := by
    intro x
    by_contra hx
    have hne1 : addOrderOf x ≠ 1 := fun h1 => hx (AddMonoid.addOrderOf_eq_one_iff.mp h1)
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne1
    obtain ⟨m, hm⟩ := hpdvd
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · rw [h0, mul_zero] at hm
        exact absurd hm (ne_of_gt (addOrderOf_pos x))
      · exact h0
    have hydv : addOrderOf (m • x) = p := by
      rw [addOrderOf_nsmul, hm, Nat.gcd_eq_right (dvd_mul_left m p)]
      exact Nat.mul_div_cancel p hmpos
    have hpk : p • (m • x) = 0 := by
      rw [← addOrderOf_dvd_iff_nsmul_eq_zero, hydv]
    have h1 : addOrderOf (m • x) = 1 :=
      AddMonoid.addOrderOf_eq_one_iff.mpr (h p hp (m • x) hpk)
    rw [hydv] at h1
    exact hp.ne_one h1
  exact ⟨fun a b => by rw [hzero a, hzero b]⟩

/-- **A finitely generated abelian group that is `p`-divisible for every prime `p` is trivial.**
Write `G ≃+ ℤ ^ r × F` with `F` finite.  `2`-divisibility kills the free part (`r = 0`) and,
transported to `F`, forces multiplication by every prime to be injective on the finite group `F`;
hence `F` has no elements of prime order and is trivial. -/
theorem groupSubsingleton (G : Type) [AddCommGroup G] [Module.Finite ℤ G]
    (h2 : Subsingleton (G ⧸ Work.Pi6.EMZ.pH 2 G))
    (hdiv : ∀ p : ℕ, p.Prime → p ≠ 2 → Subsingleton (G ⧸ Work.Pi6.EMZ.pH p G))
    (htor : ∀ p : ℕ, p.Prime → p ≠ 2 → Subsingleton (Work.Pi6.EMZ.torsP p G)) :
    Subsingleton G := by
  obtain ⟨r, F, hFadd, hFfin, ⟨e⟩⟩ := Work.StemsB.fg_abelian_decomposition G
  have hd2 : ∀ x : G, ∃ y : G, 2 • y = x := subsingleton_quot_pH_iff.mp h2
  have hdp : ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ x : G, ∃ y : G, p • y = x :=
    fun p hp hp2 => subsingleton_quot_pH_iff.mp (hdiv p hp hp2)
  have hr : r = 0 := freePart_vanishes r F G e hd2
  subst hr
  -- `F` inherits the `p`-divisibility of `G`
  have hsurjF : ∀ (p : ℕ), p.Prime → ∀ z : F, ∃ w : F, p • w = z := by
    intro p hp z
    have hsz : ∀ a : G, ∃ b : G, p • b = a := by
      rcases eq_or_ne p 2 with h | h
      · subst h
        exact hd2
      · exact hdp p hp h
    obtain ⟨b, hb⟩ := hsz (e.symm ((0 : Fin 0 → ℤ), z))
    refine ⟨(e b).2, ?_⟩
    have heq : ((0 : Fin 0 → ℤ), z) = p • e b := by
      rw [← map_nsmul, hb, AddEquiv.apply_symm_apply]
    have hfin := congrArg (fun t : (Fin 0 → ℤ) × F => t.2) heq
    simpa using hfin.symm
  -- so on the finite group `F` multiplication by a prime is injective
  have hinjF : ∀ (p : ℕ), p.Prime → ∀ x : F, p • x = 0 → x = 0 := by
    intro p hp x hx
    have hsurj : Function.Surjective (fun w : F => p • w) := fun z => hsurjF p hp z
    have hinj : Function.Injective (fun w : F => p • w) :=
      Finite.injective_iff_surjective.mpr hsurj
    exact hinj (by simpa using hx)
  have hsubF : Subsingleton F := finite_pTorsionFree_zero F hinjF
  -- hence `G` is trivial
  have hz : ∀ g : G, g = 0 := by
    intro g
    have h : e g = 0 := by
      refine Prod.ext ?_ ?_
      · exact funext fun i => i.elim0
      · exact hsubF.elim _ _
    exact e.injective (by simpa using h)
  exact ⟨fun a b => by rw [hz a, hz b]⟩

end

end Work.Pi6.EMZ
