import Mathlib
import Submission.Work.BW.BWGradedBase
import Submission.Work.BW.primLen_ne_top
import Submission.Work.BW.ideal_length_quotient_covBy
import Submission.Work.BW.maximalIdeal_mul_le_of_covBy

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Work.BW

/-- **Saturated step chain of a `p`-primary ideal.**
Let `R` be Noetherian, `p` a prime and `Q` a `p`-primary ideal (`Q.radical = p`). Then there is a
strictly increasing chain of ideals `Q = I 0 < I 1 < ... < I k = ⊤` whose length is the local
length `locLenAt p hp Q`, such that every step is annihilated by `p` (`p * I (i+1) ≤ I i`), each
step lowers the `p`-local length by exactly one, and every `I i` is `p`-saturated (i.e. it is the
contraction of its extension to `R_p`).

Route: `Q` is `p`-primary, hence `p` is a minimal prime of `Q` (`Ideal.radical_minimalPrimes`,
`Ideal.minimalPrimes_eq_subsingleton_self`) and `Q` is `p`-saturated; `locLenAt p hp Q ≠ ⊤` by the
general lemma `Work.BW.primLen_ne_top_aux` (in `Submission.Work.BW.primLen_ne_top`; note that the
`MR N`-specialised `Work.BW.primLen_ne_top` is NOT applicable). So the `A = Localization.AtPrime p`-module
`A ⧸ Q·A` has finite length (`Module.length_ne_top_iff`), hence by Mathlib's
`isFiniteLength_iff_exists_compositionSeries` it admits a composition series `s` with head `⊥`, last `⊤`
and `s.length = Module.length A (A ⧸ Q·A)` (`Module.length_compositionSeries`). Take
`I i := ((s i).comap (Submodule.mkQ (Q.map (algebraMap R A)))).comap (algebraMap R A)`.
Then `I 0 = Q`, `I k = ⊤`, strict monotonicity comes from strictness of `s` plus injectivity of the two
comaps (ideals of a localization are extensions of their contractions), `p * I (i+1) ≤ I i` comes from the
covBy step of `s` having a simple quotient over the local ring `A` (a simple module over a local ring is
killed by the maximal ideal), and `locLenAt p hp (I i.castSucc) = locLenAt p hp (I i.succ) + 1` from
additivity of `Module.length` on the short exact sequence of the step (simple quotient has length `1`). -/
theorem primary_cut_step_chain {R : Type*} [CommRing R] [IsNoetherianRing R]
    (p Q : Ideal R) (hp : p.IsPrime) (hQ : Q.IsPrimary) (hrad : Q.radical = p) :
    ∃ (k : ℕ) (I : Fin (k + 1) → Ideal R),
      I 0 = Q ∧ I (Fin.last k) = ⊤ ∧
      (∀ i j : Fin (k + 1), i < j → I i < I j) ∧
      ((k : ℕ∞) = Work.BW.locLenAt p hp Q) ∧
      (∀ i : Fin k, p * I i.succ ≤ I i.castSucc) ∧
      (∀ i : Fin k, Work.BW.locLenAt p hp (I i.castSucc) = Work.BW.locLenAt p hp (I i.succ) + 1) ∧
      (∀ i : Fin (k + 1),
        ((I i).map (algebraMap R (Localization.AtPrime p))).comap
          (algebraMap R (Localization.AtPrime p)) = I i) := by
  -- `p` is prime, so it is a minimal prime of its own radical and hence of `Q`.
  haveI : p.IsPrime := hp
  have hpmin : p ∈ Q.minimalPrimes := by
    rw [← Ideal.radical_minimalPrimes (I := Q), hrad, Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton p
  -- Work in the local ring `A = R_p`; `JL = Q·A` is the extension of `Q`.
  let A := Localization.AtPrime p
  let JL : Ideal A := Q.map (algebraMap R A)
  -- The localised quotient has finite length, since `p` is minimal over `Q`.
  have hlen_ne : Module.length A (A ⧸ JL) ≠ ⊤ := by
    have h := primLen_ne_top_aux (R := R) Q p hpmin
    simpa [A, JL] using h
  have hfin : IsFiniteLength A (A ⧸ JL) := Module.length_ne_top_iff.mp hlen_ne
  -- Jordan–Hölder: a composition series of `A ⧸ Q·A` of length `locLenAt p hp Q`.
  obtain ⟨s, hs1, hs2⟩ := isFiniteLength_iff_exists_compositionSeries.mp hfin
  -- The corresponding chain of ideals of `A` (containing `Q·A`) and of `R` (its contractions).
  let M : Fin (s.length + 1) → Ideal A := fun i => (s i).comap (Submodule.mkQ JL)
  let I : Fin (s.length + 1) → Ideal R := fun i => (M i).under R
  -- Ideals of a localization are extensions of their contractions.
  have hM_map : ∀ i : Fin (s.length + 1), (I i).map (algebraMap R A) = M i := fun i =>
    IsLocalization.map_under (M := p.primeCompl) A (M i)
  -- Contraction along the surjection `A → A ⧸ Q·A` turns the cover steps of `s` into cover steps.
  have hM_covBy : ∀ i : Fin s.length, M i.castSucc ⋖ M i.succ := fun i =>
    Submodule.comap_covBy_of_surjective (Submodule.mkQ_surjective JL) (s.step i)
  have hM_strict : StrictMono (fun i : Fin (s.length + 1) => M i) := by
    intro i j hij
    refine lt_of_le_of_ne (Submodule.comap_mono (s.strictMono hij).le) ?_
    intro heq
    exact (s.strictMono hij).ne
      (Submodule.comap_injective_of_surjective (Submodule.mkQ_surjective JL) heq)
  -- `Q` is saturated at `p`: it is primary with radical `p`.
  have hunder : (JL).under R = Q := by
    have hQle : Q ≤ p := hrad ▸ Ideal.le_radical
    have hdisj : Disjoint (p.primeCompl : Set R) (Q : Set R) :=
      Set.disjoint_left.mpr fun x hx hxQ => hx (hQle hxQ)
    exact IsLocalization.under_map_of_isPrimary_disjoint (M := p.primeCompl) A hQ hdisj
  refine ⟨s.length, I, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `I 0 = Q`
    have hM0 : M 0 = JL := by
      show (s 0).comap (Submodule.mkQ JL) = JL
      rw [show s 0 = ⊥ from hs1, Submodule.comap_bot, Submodule.ker_mkQ]
    rw [show I 0 = (M 0).under R from rfl, hM0]
    exact hunder
  · -- `I k = ⊤`
    have hMlast : M (Fin.last s.length) = ⊤ := by
      show (s (Fin.last s.length)).comap (Submodule.mkQ JL) = ⊤
      rw [show s (Fin.last s.length) = ⊤ from hs2, Submodule.comap_top]
    rw [show I (Fin.last s.length) = (M (Fin.last s.length)).under R from rfl, hMlast]
    exact Ideal.comap_top
  · -- strict monotonicity of the chain
    intro i j hij
    refine lt_of_le_of_ne ?_ ?_
    · exact Ideal.comap_mono (hM_strict hij).le
    · intro heq
      have h2 : M i = M j := by rw [← hM_map i, ← hM_map j, heq]
      exact (hM_strict hij).ne h2
  · -- the length of the chain is the `p`-local length of `Q`
    have h := Module.length_compositionSeries s hs1 hs2
    simpa [A, JL, Work.BW.locLenAt] using h
  · -- each step is annihilated by `p`
    intro i
    rw [Ideal.mul_le]
    intro x hx y hy
    have hx' : algebraMap R A x ∈ IsLocalRing.maximalIdeal A := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (R := R) p A]
      exact Ideal.mem_map_of_mem (algebraMap R A) hx
    have hy' : algebraMap R A y ∈ M i.succ := (Ideal.mem_under R (M i.succ)).mp hy
    have hmem : algebraMap R A x * algebraMap R A y ∈ M i.castSucc :=
      maximalIdeal_mul_le_of_covBy (hM_covBy i) (Ideal.mul_mem_mul hx' hy')
    rw [← map_mul] at hmem
    exact (Ideal.mem_under R (M i.castSucc)).mpr hmem
  · -- each step lowers the local length by exactly one
    intro i
    have h1 : Module.length A (A ⧸ M i.castSucc) = Module.length A (A ⧸ M i.succ) + 1 :=
      ideal_length_quotient_covBy (hM_covBy i)
    show Module.length A (A ⧸ (I i.castSucc).map (algebraMap R A)) =
      Module.length A (A ⧸ (I i.succ).map (algebraMap R A)) + 1
    rw [hM_map i.castSucc, hM_map i.succ]
    exact h1
  · -- every `I i` is `p`-saturated: equal to the contraction of its extension
    intro i
    rw [hM_map i]

end Work.BW
