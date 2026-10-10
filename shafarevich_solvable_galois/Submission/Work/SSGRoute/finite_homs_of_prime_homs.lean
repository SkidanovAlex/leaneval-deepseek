import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.GroupTheory.Perm.Cycle.Type
import Submission.Work.SSGRoute.fiber_finite_of_quotient
import Submission.Work.SSGRoute.primeCard_homs_finite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.SSGRoute

/-- **Combinatorics.** A map into a finite type whose fibres are finite has finite domain.

This is the "sigma-type finiteness" step: `α` surjects onto the sigma type of its fibres over `β`,
and the sigma type is finite because `β` and each fibre are. -/
theorem finite_of_finite_fiber {α β : Type*} [Finite β] (f : α → β)
    (h : ∀ b, Finite (f ⁻¹' {b})) : Finite α := by
  haveI : ∀ b, Finite ↥(f ⁻¹' {b}) := h
  haveI : Finite (Sigma fun b => ↥(f ⁻¹' {b})) := inferInstance
  refine Finite.of_surjective (fun s : (Sigma fun b => ↥(f ⁻¹' {b})) => (s.2 : α)) ?_
  intro a
  exact ⟨⟨f a, ⟨a, rfl⟩⟩, rfl⟩

/-- **The main induction.**  For a finite abelian group `S`, the open-kernel homomorphisms
`G →* S` form a finite set, by strong induction on `Nat.card S`.

If `S` is trivial we are done.  Otherwise Cauchy's theorem produces `x ≠ 1` of prime order `l`;
with `N := Subgroup.zpowers x` (of cardinality `l`), the reduction `S →* S ⧸ N` has finite
codomain by the induction hypothesis (`Nat.card (S ⧸ N) = Nat.card S / l < Nat.card S`), and each
fibre is finite by the prime-order case (`primeCard_homs_finite`) combined with
`fiber_finite_of_quotient`.  `finite_of_finite_fiber` then finishes. -/
theorem homs_finite_aux {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (h : ∀ l : ℕ, l.Prime → Finite {χ : G →* Multiplicative (ZMod l) // IsOpen (χ.ker : Set G)}) :
    ∀ n : ℕ, ∀ (S : Type*) [CommGroup S] [Finite S], Nat.card S = n →
      Finite {χ : G →* S // IsOpen (χ.ker : Set G)} := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih S _ _ hn
  by_cases hsmall : Nat.card S ≤ 1
  · haveI : Subsingleton S := Finite.card_le_one_iff_subsingleton.mp hsmall
    haveI : Subsingleton {χ : G →* S // IsOpen (χ.ker : Set G)} :=
      ⟨fun a b => Subtype.ext (MonoidHom.ext fun g => Subsingleton.elim (a.1 g) (b.1 g))⟩
    exact Finite.of_subsingleton
  · have hsmall1 : 1 < Nat.card S := not_le.mp hsmall
    have hne : Nat.card S ≠ 1 := ne_of_gt hsmall1
    obtain ⟨l, hl, hldvd⟩ := Nat.exists_prime_and_dvd hne
    haveI : Fact l.Prime := ⟨hl⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' l hldvd
    let N : Subgroup S := Subgroup.zpowers x
    have hNcard : Nat.card N = l := by
      show Nat.card (Subgroup.zpowers x) = l
      rw [Nat.card_zpowers, hx]
    have hNprime : (Nat.card N).Prime := by rw [hNcard]; exact hl
    have hcard_eq : Nat.card (S ⧸ N) * Nat.card N = n := by
      rw [← Subgroup.card_eq_card_quotient_mul_card_subgroup N, hn]
    haveI : Nonempty (S ⧸ N) := ⟨1⟩
    have hQpos : 0 < Nat.card (S ⧸ N) := Nat.card_pos
    have hlN2 : 1 < Nat.card N := by rw [hNcard]; exact hl.one_lt
    have hlt : Nat.card (S ⧸ N) < n := by
      have h1 : Nat.card (S ⧸ N) * 1 < Nat.card (S ⧸ N) * Nat.card N :=
        mul_lt_mul_of_pos_left hlN2 hQpos
      rw [mul_one, hcard_eq] at h1
      exact h1
    haveI hE : Finite {ψ : G →* S ⧸ N // IsOpen (ψ.ker : Set G)} :=
      ih (Nat.card (S ⧸ N)) hlt (S ⧸ N) rfl
    let Φ : {χ : G →* S // IsOpen (χ.ker : Set G)} →
            {ψ : G →* S ⧸ N // IsOpen (ψ.ker : Set G)} :=
      fun χ => ⟨(QuotientGroup.mk' N).comp χ.1, by
        refine Subgroup.isOpen_mono ?_ χ.2
        intro g hg
        rw [MonoidHom.mem_ker] at hg
        simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, hg, map_one]⟩
    have hfiber : ∀ ψ : {ψ : G →* S ⧸ N // IsOpen (ψ.ker : Set G)},
        Finite (Φ ⁻¹' {ψ}) := by
      intro ψ
      by_cases hmem : ∃ χ₀ : {χ : G →* S // IsOpen (χ.ker : Set G)}, Φ χ₀ = ψ
      · obtain ⟨χ₀, hχ₀⟩ := hmem
        haveI hNfin : Finite {δ : G →* N // IsOpen (δ.ker : Set G)} :=
          primeCard_homs_finite h N hNprime
        haveI hB : Finite {χ : G →* S // IsOpen (χ.ker : Set G) ∧
            (QuotientGroup.mk' N).comp χ = (QuotientGroup.mk' N).comp χ₀.1} :=
          fiber_finite_of_quotient N χ₀.1 χ₀.2 hNfin
        refine Finite.of_injective
          (fun d : Φ ⁻¹' {ψ} =>
            (⟨d.1.1, d.1.2, ?_⟩ : {χ : G →* S // IsOpen (χ.ker : Set G) ∧
              (QuotientGroup.mk' N).comp χ = (QuotientGroup.mk' N).comp χ₀.1})) ?_
        · have hd : Φ d.1 = ψ := Set.mem_singleton_iff.mp d.2
          have hh : Φ d.1 = Φ χ₀ := by rw [hd, hχ₀]
          simpa using congrArg Subtype.val hh
        · intro a b hab
          have h1 : a.1.1 = b.1.1 := by
            have h2 := congrArg Subtype.val hab
            simpa using h2
          exact Subtype.ext (Subtype.ext h1)
      · haveI : Subsingleton (Φ ⁻¹' {ψ}) :=
          ⟨fun d _ => (hmem ⟨d.1, Set.mem_singleton_iff.mp d.2⟩).elim⟩
        exact Finite.of_subsingleton
    exact finite_of_finite_fiber Φ hfiber

/-- **Finitely many open-kernel homomorphisms into a finite abelian group, from the prime cyclic
case.**  If for every prime `l` there are only finitely many open-kernel homomorphisms
`G →* Multiplicative (ZMod l)`, then the same holds for every finite abelian target.

Suggested route.
* *Prime order groups*: transfer the hypothesis to an arbitrary `CommGroup` `T` with
  `Nat.card T = l` prime, using `isCyclic_of_prime_card` and
  `zmodCyclicMulEquiv : Multiplicative (ZMod (Nat.card T)) ≃* T` (both in
  `Mathlib/GroupTheory/SpecificGroups/Cyclic.lean`; the open-kernel condition transports along a
  `MulEquiv` because `ker (e ∘ f) = ker f` for injective `e`).
* *Strong induction on `Nat.card`* for a finite abelian `S`: if `|S| ≥ 2`, Cauchy's theorem
  (`Nat.exists_prime_and_dvd`, `exists_prime_orderOf_dvd_card'`) gives `x ≠ 1` of prime order `l`;
  set `N := Subgroup.zpowers x`, so `Nat.card ↥N = l` (`Nat.card_zpowers`).  Reduce along
  `QuotientGroup.mk' N : S →* S ⧸ N`: the base `Nat.card (S ⧸ N) = Nat.card S / l < Nat.card S` is
  finite by induction, and the fibre over a fixed reduction is either empty or injects into
  `{δ : G →* ↥N // IsOpen δ.ker}` (via `χ ↦ χ * χ₀⁻¹` for a chosen `χ₀` in the fibre; the kernel of
  this difference contains `ker χ ⊓ ker χ₀`, which is open), which is finite by the prime-order
  case.  `Sigma`-type finiteness (`Fintype.ofFinite` on the base and on each fibre) then finishes.
* The last step applies the induction to `S := Multiplicative M`. -/
theorem finite_homs_of_prime_homs {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (h : ∀ l : ℕ, l.Prime → Finite {χ : G →* Multiplicative (ZMod l) // IsOpen (χ.ker : Set G)})
    (M : Type*) [AddCommGroup M] [Finite M] :
    Finite {χ : G →* Multiplicative M // IsOpen (χ.ker : Set G)} :=
  homs_finite_aux h (Nat.card (Multiplicative M)) (Multiplicative M) rfl

end Work.SSGRoute
