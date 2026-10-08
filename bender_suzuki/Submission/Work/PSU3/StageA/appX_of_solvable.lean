import Mathlib
import Submission.Work.Fitting.Main
import Submission.Work.ThmF.Tools.appX_card_E
import Submission.Work.ThmF.Tools.appX_cyclic_fitting
import Submission.Work.ThmF.Tools.appX_fpf_fitting
import Submission.Work.ThmF.Tools.appX_commutator_le_fitting
import Submission.Work.PSU3.StageA.appX_prop_public

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Appendix X for an odd *solvable* group (Feit–Thompson-free form)

`Work.PSU3.StageA.appX_of_solvable` is the Proposition of Appendix X of Peterfalvi II (p. 281)
with the odd order theorem *replaced by its conclusion* for the acting group: instead of a
global `hFT : FeitThompsonProp` one assumes directly `hDsolv : Group.IsSolvable D`.

*Let `D` be a finite solvable group of odd order acting faithfully on an elementary abelian
`p`-group `E` and transitively on `E^#`.  Then `F(D)` is cyclic, acts fixed-point-freely on `E`,
and `D/F(D)` is abelian (`[D,D] ≤ F(D)`).*

This is the form in which the input is needed by `Work.PSU3.StageA.Ksub_eq_Kset_of_W_bot`
(via `Work.ThmF.ChV12.Ksub_cyclic_normal`): there the acting group is `D = twoPoint H t`, of odd
order, and the single use of `FeitThompsonProp` inside the Appendix X argument is exactly the
instance `Group.IsSolvable ↥(twoPoint H t)`.

## Proof

The argument is the assembly of `Work.ThmF.Tools.appX`, with the single use of
`FeitThompsonProp` (`haveI : Group.IsSolvable D := hFT D hoddD`) replaced by the hypothesis
`hDsolv`, and with Huppert's step exposed as the public lemma
`Work.PSU3.StageA.appX_prop_public`:

* if `E` is trivial then `ρ` is injective into a subsingleton, so `D` is trivial;
* otherwise `|E| = 2 ^ k` (`Work.ThmF.Tools.appX_card_E`), and for every prime `ℓ ∣ |D|` the
  `ℓ`-core `O_ℓ(D)` is cyclic and acts fixed-point-freely on `E`: apply `appX_prop_public` to
  `O_ℓ(D) ≤ D` (an `ℓ`-group of odd order, coprime to `|E|`, with constant stabiliser
  cardinalities because `O_ℓ(D) ⊴ D` and `D` is transitive on `E^#`);
* `F(D)` is cyclic because it is the product of the cyclic `O_ℓ(D)` of pairwise coprime order
  (`Work.ThmF.Tools.appX_cyclic_fitting`);
* `F(D)` acts fixed-point-freely because every nonidentity element of `F(D)` has a nontrivial
  power of prime order lying in some `O_ℓ(D)` (`Work.ThmF.Tools.appX_fpf_fitting`);
* `[D,D] ≤ F(D)` because `F(D)` is cyclic, so `Aut F(D)` is abelian, while `C_D(F(D)) ≤ F(D)` by
  self-centralisation of the Fitting subgroup in a solvable group
  (`Work.ThmF.Tools.appX_commutator_le_fitting`).
-/

namespace Work.PSU3.StageA

theorem appX_of_solvable {D E : Type} [Group D] [Finite D] [Group E] [Finite E] (hDsolv : Group.IsSolvable D) (hoddD : Odd (Nat.card D)) {p : ℕ} (hp : p.Prime) (hEab : ∀ x y : E, x * y = y * x) (hEexp : ∀ x : E, x ^ p = 1) (ρ : D →* MulAut E) (hfaith : Function.Injective ρ) (htrans : ∀ a b : E, a ≠ 1 → b ≠ 1 → ∃ d : D, ρ d a = b) : IsCyclic ↥(Work.Fitting.fitting D) ∧ (∀ d ∈ Work.Fitting.fitting D, d ≠ 1 → ∀ a : E, ρ d a = a → a = 1) ∧ (∀ x y : D, x * y * x⁻¹ * y⁻¹ ∈ Work.Fitting.fitting D) := by
  classical
  haveI hEcomm : IsMulCommutative E := isMulCommutative_iff.mpr hEab
  rcases subsingleton_or_nontrivial E with hE1 | hEnt
  · -- ## Case `E` trivial: then `D` is trivial
    haveI := hE1
    have hSub : Subsingleton (MulAut E) :=
      ⟨fun f g => MulEquiv.ext fun x => Subsingleton.elim _ _⟩
    haveI : Subsingleton D := ⟨fun x y => hfaith (hSub.elim (ρ x) (ρ y))⟩
    haveI : Subsingleton ↥(Work.Fitting.fitting D) :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    refine ⟨isCyclic_of_subsingleton, ?_, ?_⟩
    · intro d _ hd
      exact absurd (Subsingleton.elim d 1) hd
    · intro x y
      rw [Subsingleton.elim x 1, Subsingleton.elim y 1]
      simpa using (Work.Fitting.fitting D).one_mem
  · -- ## Case `E` nontrivial: `|E|` is a power of `2`
    haveI := hEnt
    obtain ⟨k, hk⟩ := Work.ThmF.Tools.appX_card_E hoddD hp hEab hEexp ρ hfaith htrans
    -- Every `O_ℓ(D)`, `ℓ` a prime divisor of `|D|`, is cyclic and acts fixed-point-freely.
    have key : ∀ ℓ ∈ (Nat.card D).primeFactors,
        IsCyclic ↥(Work.Fitting.pCore ℓ D) ∧
        (∀ x : ↥(Work.Fitting.pCore ℓ D), x ≠ 1 → ∀ a : E, (ρ x.1) a = a → a = 1) := by
      intro ℓ hℓ
      have hℓprime : ℓ.Prime := Nat.prime_of_mem_primeFactors hℓ
      have hℓodd : Odd ℓ := by
        refine hℓprime.odd_of_ne_two ?_
        intro h2
        exact (Nat.not_even_iff_odd.mpr hoddD)
          (even_iff_two_dvd.mpr (h2 ▸ (Nat.mem_primeFactors.mp hℓ).2.1))
      -- `|O_ℓ(D)|` is a power of `ℓ`, `|E|` a power of `2`, and `ℓ` is odd: coprime
      have hcop : (Nat.card ↥(Work.Fitting.pCore ℓ D)).Coprime (Nat.card E) := by
        haveI : Fact ℓ.Prime := ⟨hℓprime⟩
        obtain ⟨n, hn⟩ := (Work.Fitting.isPGroup_pCore (G := D) hℓprime).exists_card_eq
        rw [hn, hk]
        exact Nat.Coprime.pow_left n (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hℓodd))
      -- the stabilisers of all nonidentity elements have the same cardinality
      have hconst : ∀ a b : E, a ≠ 1 → b ≠ 1 →
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
            rw [← MulAut.mul_apply E (ρ d) (ρ d⁻¹) b, ← map_mul, mul_inv_cancel, map_one]
            rfl
          rw [h1, ← hd]
        change (ρ (x : D)) a = a ↔
          (ρ ((((MulAut.conjNormal d).toEquiv x : ↥(Work.Fitting.pCore ℓ D)) : D))) b = b
        rw [hval]
        have hkey : (ρ (d * (x : D) * d⁻¹)) b = (ρ d) ((ρ (x : D)) a) := by
          rw [map_mul, map_mul]
          simp only [MulAut.mul_apply E]
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
    have hcycF : IsCyclic ↥(Work.Fitting.fitting D) :=
      Work.ThmF.Tools.appX_cyclic_fitting (fun ℓ hℓ => (key ℓ hℓ).1)
    haveI : Group.IsSolvable D := hDsolv
    refine ⟨hcycF, ?_, ?_⟩
    · refine Work.ThmF.Tools.appX_fpf_fitting ρ ?_
      intro ℓ hℓ x hx hne a ha
      exact (key ℓ hℓ).2 ⟨x, hx⟩ (fun h => hne (congrArg Subtype.val h)) a ha
    · exact Work.ThmF.Tools.appX_commutator_le_fitting hcycF

end Work.PSU3.StageA
