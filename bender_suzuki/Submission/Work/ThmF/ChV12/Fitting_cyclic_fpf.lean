import Mathlib
import Submission.Work.Fitting.Main
import Submission.Work.PSU3.StageA.appX_prop_public
import Submission.Work.ThmF.Tools.appX_fpf_fitting
import Submission.Work.ThmF.Tools.appX_cyclic_fitting

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.ThmF.ChV12

/-- A finite group of exponent `2` has order a power of `2`. -/
theorem card_eq_two_pow_of_mul_self_eq_one {A : Type} [Group A] [Finite A]
    (hA2 : ∀ x : A, x * x = 1) : ∃ k : ℕ, Nat.card A = 2 ^ k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 A := fun g => ⟨(1 : ℕ), by
    show g ^ (2 ^ 1) = 1
    rw [pow_one, pow_two]
    exact hA2 g⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  exact ⟨k, hk⟩

/-- **Huppert's Appendix X step, for each `p`-core.**

Let `D` be a finite group of odd order acting faithfully on a finite elementary abelian
`2`-group `A`, transitively on the nonidentity elements.  Then for every prime `ℓ` dividing
`|D|` the `ℓ`-core `O_ℓ(D)` is cyclic and acts fixed-point-freely on `A`.

This is Huppert's special case of the Lemma of Peterfalvi II, Appendix X
(`Work.PSU3.StageA.appX_prop_public`), applied to `O_ℓ(D) ≤ D`: the `ℓ`-core is an `ℓ`-group
of odd order, of order coprime to `|A|` (a power of `2`), and its point stabilisers all have
the same cardinality because they are conjugate in `D` (the `ℓ`-core being normal in `D` while
`D` is transitive on `A^#`). -/
theorem pCore_isCyclic_and_fpf_of_transitive {D A : Type} [Group D] [Finite D] [Group A]
    [Finite A] (hA2 : ∀ x : A, x * x = 1) (hAc : ∀ x y : A, x * y = y * x)
    (hodd : Odd (Nat.card D)) (ρ : D →* MulAut A) (hfaith : Function.Injective ρ)
    (htrans : ∀ a b : A, a ≠ 1 → b ≠ 1 → ∃ d : D, ρ d a = b) :
    ∀ ℓ ∈ (Nat.card D).primeFactors,
      IsCyclic ↥(Work.Fitting.pCore ℓ D) ∧
        (∀ x : ↥(Work.Fitting.pCore ℓ D), x ≠ 1 → ∀ a : A, (ρ x.1) a = a → a = 1) := by
  classical
  haveI hAcomm : IsMulCommutative A := isMulCommutative_iff.mpr hAc
  obtain ⟨k, hk⟩ := card_eq_two_pow_of_mul_self_eq_one hA2
  intro ℓ hℓ
  have hℓprime : ℓ.Prime := Nat.prime_of_mem_primeFactors hℓ
  have hℓodd : Odd ℓ := by
    refine hℓprime.odd_of_ne_two ?_
    intro h2
    exact (Nat.not_even_iff_odd.mpr hodd)
      (even_iff_two_dvd.mpr (h2 ▸ (Nat.mem_primeFactors.mp hℓ).2.1))
  -- `|O_ℓ(D)|` is a power of the odd prime `ℓ`, `|A|` is a power of `2`: the orders are coprime
  have hcop : (Nat.card ↥(Work.Fitting.pCore ℓ D)).Coprime (Nat.card A) := by
    haveI : Fact ℓ.Prime := ⟨hℓprime⟩
    obtain ⟨n, hn⟩ := (Work.Fitting.isPGroup_pCore (G := D) hℓprime).exists_card_eq
    rw [hn, hk]
    exact Nat.Coprime.pow_left n (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hℓodd))
  -- the point stabilisers in `O_ℓ(D)` are conjugate in `D`, hence have the same cardinality
  have hconst : ∀ a b : A, a ≠ 1 → b ≠ 1 →
      Nat.card {x : ↥(Work.Fitting.pCore ℓ D) |
        ((ρ.comp (Work.Fitting.pCore ℓ D).subtype) x) a = a} =
      Nat.card {y : ↥(Work.Fitting.pCore ℓ D) |
        ((ρ.comp (Work.Fitting.pCore ℓ D).subtype) y) b = b} := by
    intro a b ha hb
    obtain ⟨d, hd⟩ := htrans a b ha hb
    haveI : (Work.Fitting.pCore ℓ D).Normal := inferInstance
    refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conjNormal d).toEquiv ?_)
    intro x
    have hval : (((MulAut.conjNormal d).toEquiv x : ↥(Work.Fitting.pCore ℓ D)) : D) =
        d * (x : D) * d⁻¹ := MulAut.conjNormal_apply d x
    have hd1 : (ρ d⁻¹) b = a := by
      apply (ρ d).injective
      have h1 : (ρ d) ((ρ d⁻¹) b) = b := by
        rw [← MulAut.mul_apply A (ρ d) (ρ d⁻¹) b, ← map_mul, mul_inv_cancel, map_one]
        rfl
      rw [h1, ← hd]
    change (ρ (x : D)) a = a ↔
      (ρ ((((MulAut.conjNormal d).toEquiv x : ↥(Work.Fitting.pCore ℓ D)) : D))) b = b
    rw [hval]
    have hkey : (ρ (d * (x : D) * d⁻¹)) b = (ρ d) ((ρ (x : D)) a) := by
      rw [map_mul, map_mul]
      simp only [MulAut.mul_apply A]
      rw [hd1]
    rw [hkey]
    constructor
    · intro h; rw [h]; exact hd
    · intro h
      exact (ρ d).injective (h.trans hd.symm)
  have hfaithP : Function.Injective (ρ.comp (Work.Fitting.pCore ℓ D).subtype) :=
    fun x y hxy => Subtype.ext (hfaith (by simpa using hxy))
  have hres := Work.PSU3.StageA.appX_prop_public hℓprime hℓodd
    (Work.Fitting.isPGroup_pCore hℓprime) hcop
    (ρ.comp (Work.Fitting.pCore ℓ D).subtype) hfaithP hconst
  exact ⟨hres.1, fun x hx a hxa => hres.2 x hx a (by simpa using hxa)⟩

/-- **Peterfalvi II, Appendix X (Step (8) of the odd-order case).**

`D` is a finite group of odd order acting faithfully on a finite elementary abelian `2`-group
`A` transitively on the nonidentity elements.  Then the Fitting subgroup `F(D)` is cyclic and
acts fixed-point-freely on `A`.

Huppert's Appendix X Lemma applied to each `p`-core bounds the cyclic pieces
(`pCore_isCyclic_and_fpf_of_transitive`), and the two structure lemmas
`Work.ThmF.Tools.appX_cyclic_fitting` / `appX_fpf_fitting` assemble them: `F(D)` is the product
of the `O_ℓ(D)`, `ℓ ∣ |D|`, which are cyclic of pairwise coprime order, and a nonidentity
element of `F(D)` has a nonidentity power of prime order inside some `O_ℓ(D)`. -/
theorem Fitting_cyclic_fpf {D A : Type} [Group D] [Finite D] [Group A] [Finite A]
    (hA2 : ∀ x : A, x * x = 1)
    (hAc : ∀ x y : A, x * y = y * x)
    (hodd : Odd (Nat.card D))
    (ρ : D →* MulAut A) (hfaith : Function.Injective ρ)
    (htrans : ∀ a b : A, a ≠ 1 → b ≠ 1 → ∃ d : D, ρ d a = b) :
    IsCyclic ↥(Work.Fitting.fitting D) ∧
      (∀ d ∈ Work.Fitting.fitting D, d ≠ 1 → ∀ a : A, ρ d a = a → a = 1) := by
  classical
  have key := pCore_isCyclic_and_fpf_of_transitive hA2 hAc hodd ρ hfaith htrans
  refine ⟨Work.ThmF.Tools.appX_cyclic_fitting (fun ℓ hℓ => (key ℓ hℓ).1), ?_⟩
  refine Work.ThmF.Tools.appX_fpf_fitting ρ ?_
  intro ℓ hℓ x hx hne a ha
  exact (key ℓ hℓ).2 ⟨x, hx⟩ (fun h => hne (congrArg Subtype.val h)) a ha

end Work.ThmF.ChV12
