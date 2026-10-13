import Mathlib
import Submission.Work.DSEQ0.SurjBasic
import Submission.Work.DSEQ0.DAcyclic_one
import Submission.Work.DSEQ0.FAcyclic_succ
import Submission.Work.DSEQ0.GrAcyclic_self

/-!
# `Work.DSEQ0.surj_tuple_vanishing`

The vanishing of the Čech (surjection) complex above degree `Fintype.card ι`, in the concrete
form needed by the image-size filtration of the Čech complex.

Given `n ≥ Fintype.card ι` and an `M`-valued function `a` on `(n+1)`-tuples into `ι`
which vanishes on non-surjective tuples and is a cocycle for the alternating coboundary
`cob`, we produce a function `b` on `n`-tuples, vanishing on non-surjective tuples, with
`cob b = a`.

This is `Hⁿ(F (card ι)) = 0` for `n ≥ card ι`, where `F m` is the image-size filtration
of the full (unnormalised) complex `D k := (Fin (k+1) → ι) → M`.  The proof is by strong
induction on the cardinality (`surjTV_FAcyclic_card`), using the pieces established by the
team in this directory:

* `cob_cob` — `cob ∘ cob = 0` (in `Submission.Work.DSEQ0.cob_cob`);
* `DAcyclic_one` — `D` is acyclic above degree `1` (the "prepend a base point"
  contracting homotopy);
* `GrAcyclic_self` — the graded pieces `F m / F (m+1) ≅ ⊕_{|T| = m} (surjection complex on T)`
  are acyclic above `m`, by the induction hypothesis applied to the `m`-element subsets `T`;
* `FAcyclic_succ` — the elementary long-exact-sequence chase
  `0 → F (m+1) → F m → F m / F (m+1) → 0`.

The full-complex acyclicity `DAcyclic_one` is *not* enough on its own: its contracting
homotopy ("prepend a base point") does not preserve the subcomplexes `F m`, which is
exactly why the filtration and `GrAcyclic_self` are needed.
-/

open Classical Finset

namespace Work.DSEQ0

universe u

/-- `F 1 = F 0 = D` when `1 ≤ card ι`: the acyclicity of the full complex `D` above degree
`1` gives that of the subcomplex `F 1`. -/
theorem surjTV_FAcyclic_one {ι : Type u} [Fintype ι] {M : Type u} [AddCommGroup M]
    (hι : 1 ≤ Fintype.card ι) : @FAcyclic ι M _ 1 1 := by
  have hne : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hD : @DAcyclic ι M _ 1 := DAcyclic_one (M := M) hne
  intro k hk f hf hc
  obtain ⟨h, hh⟩ := hD k hk f hc
  refine ⟨h, ?_, hh⟩
  intro g hg
  exact absurd (one_le_imgCard (by omega : 0 < k + 1) g) (by omega)

/-- The crux, in the form used for the induction: the subcomplex `F (card X)` of the
surjection complex over the finite type `X` is acyclic above degree `Fintype.card X`. -/
theorem surjTV_FAcyclic_card {M : Type u} [AddCommGroup M] :
    ∀ s : ℕ, ∀ (X : Type u) [Fintype X], Fintype.card X = s → @FAcyclic X M _ s s := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro X instX hX
    rcases Nat.eq_zero_or_pos s with hs0 | hspos
    · subst hs0
      haveI : IsEmpty X := Fintype.card_eq_zero_iff.mp hX
      intro k hk f hf hc
      refine ⟨fun _ => 0, fun g hg => rfl, ?_⟩
      funext x
      exact (IsEmpty.false (x 0)).elim
    · have hR : ∀ m, 1 ≤ m → m ≤ s → @FAcyclic X M _ m m :=
        Nat.le_induction (m := 1) (P := fun m (_ : 1 ≤ m) => m ≤ s → @FAcyclic X M _ m m)
          (fun hs1 => surjTV_FAcyclic_one (M := M) (by omega))
          (fun n hn ihn hns => by
            have hFm : @FAcyclic X M _ n n := ihn (by omega)
            have hGr : @GrAcyclic X M _ n n :=
              GrAcyclic_self (M := M) n hn (fun Y _ hY => ih n (by omega) Y hY)
            exact FAcyclic_succ (M := M) n hn hFm hGr)
      exact hR s hspos (le_refl s)

/-- A supported cocycle on the "surjective tuples" complex with constant coefficients is a
supported coboundary, as soon as the degree is at least the size of the target.

Concretely: `a` is a function on all `(n+1)`-tuples from `ι` (i.e. a degree-`n` cochain) which
vanishes on non-surjective tuples, and whose alternating coboundary (sum over the `n+2`
deletions `x ∘ Fin.succAbove k`, with signs) vanishes.  If `Fintype.card ι ≤ n` then it is the
coboundary of a degree-`(n-1)` cochain `b` which also vanishes on non-surjective tuples.

This is the "surjection complex" with constant coefficients `M`: its homology is `M` in degree
`card ι - 1` and vanishes in all higher degrees, which is what the image-size filtration of the
Čech complex needs.

Suggested route: filter by the number of occurrences of a fixed element `i₀ ∈ ι` (`F^p = {b |
b g = 0 unless #{k : g k = i₀} ≥ p}`); the graded pieces are `p`-fold décalages of the same
statement for `ι ∖ {i₀}`, so an induction on `Fintype.card ι` plus the long exact sequences of
the filtration gives the result.  Equivalently: the semisimplicial set of surjections onto a
`card ι`-element set has the homology of a `(card ι - 1)`-sphere. -/
theorem surj_tuple_vanishing {ι : Type u} [Fintype ι] {M : Type u} [AddCommGroup M] (n : ℕ)
    (hn : Fintype.card ι ≤ n) (a : (Fin (n + 1) → ι) → M)
    (hsupp : ∀ g, ¬ Function.Surjective g → a g = 0)
    (ha : ∀ x : Fin (n + 2) → ι,
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) • a (x ∘ Fin.succAbove k) = 0) :
    ∃ b : (Fin n → ι) → M,
      (∀ g, ¬ Function.Surjective g → b g = 0) ∧
      ∀ x : Fin (n + 1) → ι,
        ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) • b (x ∘ Fin.succAbove k) = a x := by
  have hA : @FAcyclic ι M _ (Fintype.card ι) (Fintype.card ι) :=
    surjTV_FAcyclic_card (Fintype.card ι) ι rfl
  have hinf : inF (Fintype.card ι) a := inF_of_card a hsupp
  rcases n with _ | m
  · have hcard0 : Fintype.card ι = 0 := by omega
    haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hcard0
    refine ⟨fun _ => 0, fun g hg => rfl, ?_⟩
    intro x
    exact (IsEmpty.false (x 0)).elim
  · have hcob : cob (m + 1) a = 0 := by
      funext x
      change (∑ j : Fin (m + 1 + 2), (-1 : ℤ) ^ (j : ℕ) • a (x ∘ Fin.succAbove j)) = 0
      exact ha x
    obtain ⟨h, hh_inf, hh_cob⟩ := hA m (by omega) a hinf hcob
    refine ⟨h, inF_card_of h hh_inf, ?_⟩
    intro x
    exact congrFun hh_cob x

end Work.DSEQ0
