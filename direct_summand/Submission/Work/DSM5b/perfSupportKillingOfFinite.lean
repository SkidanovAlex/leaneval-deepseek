import Mathlib
import Submission.Work.DSM5b.PerfComplexDefs
import Submission.Work.DSM5b.H0Defs
import Submission.Work.DSM5b.Basic
import Submission.Work.DSM5b.phiPC_properties
import Submission.Work.DSM5b.rootKillTransport
import Submission.Work.DSM5b.perfSupport
import Submission.Work.DSM5b.honestKillFree
import Submission.Work.DSM5b.honestCohomologyVanishing
import Submission.Work.DSM5b.subringKillTransportN

/-!
# `Work.DSM5b.perfSupportKillingOfFinite` — the large-`E` uniform orbit bound

The node of `Submission/Work/DSM5b/orbitUniform.lean`, `Work.DSM5b.perfSupportKilling`, is proved
here from three ingredients:

* **support** `Work.DSM5b.perfSupport`: each component of the cycle is honest over a finitely
  generated subring after a high enough `p`-power;
* **Noetherian uniform honest killing** over that subring
  (`Work.DSM5b.honestKillCoordNoethOfFree`, given the finiteness in the generator form and the
  unconditional vanishing `Work.DSM5b.honestCohomologyVanishing`): one exponent `N` kills every
  honest cycle over the subring, which is Noetherian by Mathlib's `is_noetherian_subring_closure`;
* **transport** `Work.DSM5b.subringKillTransportN`, which carries that *same* exponent `N` to the
  `R₀`-generated subcomplex of the perfected complex `PCX p t ·`.

The finiteness is an explicit hypothesis, so that this file closes the moment the peer
`Work.DSM5b.honestCohomologyFinite` lands.
-/

set_option maxHeartbeats 1000000

namespace Work.DSM5b

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2
open Work.DSM5b.Work.DSM5b

universe a

/-- Adjoining a generating set is monotone in the base subring. -/
lemma mem_adjoin_mono_subring {R : Type a} [CommRing R] {A : Type a} [CommRing A] [Algebra R A]
    {S T : Subring R} (h : S ≤ T) (s : Set A) {x : A} :
    x ∈ Algebra.adjoin ↥S s → x ∈ Algebra.adjoin ↥T s := by
  intro hx
  rw [Algebra.mem_adjoin_iff] at hx ⊢
  refine Subring.closure_mono ?_ hx
  rintro y (hy | hy)
  · obtain ⟨r, rfl⟩ := hy
    exact Or.inl ⟨⟨(r : R), h r.2⟩, rfl⟩
  · exact Or.inr hy

/-- **The large-`E` uniform orbit bound, from the Noetherian finiteness.** -/
theorem perfSupportKillingOfFinite (p : ℕ) [Fact p.Prime] {R : Type a} [CommRing R] [CharP R p]
    [PerfectRing R p] {ι : Type a} [Finite ι] [DecidableEq ι] (t : ι → R) (T : R) (j₀ : ι)
    (e : ℕ) (hj₀ : t j₀ = T ^ e)
    (hfin : ∀ (A : Type a) [CommRing A] [IsNoetherianRing A] (u : ι → A) (U : A) (k₀ : ι)
      (ee : ℕ), u k₀ = U ^ ee → ∀ q : ℕ, ∃ (k : ℕ) (f : Fin k → HCX u (q + 1)),
        (∀ i, HCd u (q + 1) (f i) = 0) ∧
        ∀ z : HCX u (q + 1), HCd u (q + 1) z = 0 →
          ∃ c : Fin k → A, ∃ y : HCX u q, z = (∑ i, c i • f i) + HCd u q y) :
    ∀ (n : ℕ) (z : PCX p t (n + 1)), PCd p t (n + 1) z = 0 →
      ∃ E₀ N : ℕ, ∀ E : ℕ, E₀ ≤ E →
        T ^ N • phiPow p t (n + 1) E z ∈ LinearMap.range (PCd p t n) := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  intro n z hz
  -- (1) support, componentwise
  have hsup : ∀ τ : Fin (n + 2) → ι, ∃ (m : ℕ) (c : Fin m → R) (E : ℕ), ∀ E' : ℕ, E ≤ E' →
      ((phiPow p t (n + 1) E' z) τ : Localization.Away (tS t (tupRng τ))) ∈
        Algebra.adjoin (Subring.closure (Set.range t ∪ {T} ∪ Set.range c))
          (chartGens t (tupRng τ)) := by
    intro τ
    obtain ⟨m, c, E, hE⟩ := perfSupport p t T (tupRng τ) (z τ) (z τ).2
    exact ⟨m, c, E, fun E' hE' => by
      simpa only [phiPow_apply_val] using hE E' hE'⟩
  choose m c E hE using hsup
  -- (2) combine the finitely many supports into one subring `R₀`
  let cc : (Σ τ : Fin (n + 2) → ι, Fin (m τ)) → R := fun i => c i.1 i.2
  let R₀ : Subring R := Subring.closure (Set.range t ∪ {T} ∪ Set.range cc)
  have ht₀ : ∀ i, t i ∈ R₀ := fun i =>
    Subring.subset_closure (Or.inl (Or.inl ⟨i, rfl⟩))
  have hT₀ : T ∈ R₀ := Subring.subset_closure (Or.inl (Or.inr rfl))
  have hmono : ∀ τ : Fin (n + 2) → ι,
      Subring.closure (Set.range t ∪ {T} ∪ Set.range (c τ)) ≤ R₀ := by
    intro τ
    refine Subring.closure_mono ?_
    intro x hx
    rcases hx with (hx | hx) | hx
    · exact Or.inl (Or.inl hx)
    · exact Or.inl (Or.inr hx)
    · obtain ⟨j, rfl⟩ := hx
      exact Or.inr ⟨⟨τ, j⟩, rfl⟩
  let E₀ : ℕ := Finset.univ.sup E
  have hR : ∀ E : ℕ, E₀ ≤ E → ∀ τ : Fin (n + 2) → ι,
      ((phiPow p t (n + 1) E z) τ : Localization.Away (tS t (tupRng τ))) ∈
        Algebra.adjoin R₀ (chartGens t (tupRng τ)) := by
    intro E hE0 τ
    have h1 : ((phiPow p t (n + 1) E z) τ : Localization.Away (tS t (tupRng τ))) ∈
        Algebra.adjoin (Subring.closure (Set.range t ∪ {T} ∪ Set.range (c τ)))
          (chartGens t (tupRng τ)) :=
      hE τ E (le_trans (Finset.le_sup (Finset.mem_univ τ)) hE0)
    exact mem_adjoin_mono_subring (hmono τ) (chartGens t (tupRng τ)) h1
  -- (3) Noetherian uniform honest killing over `R₀`
  haveI : IsNoetherianRing ↥R₀ := by
    have hset : (Set.range t ∪ {T} ∪ Set.range cc : Set R).Finite :=
      (Set.finite_range t |>.union (Set.finite_singleton T)).union (Set.finite_range cc)
    exact is_noetherian_subring_closure _ hset
  have hj₀' : (⟨t j₀, ht₀ j₀⟩ : R₀) = (⟨T, hT₀⟩ : R₀) ^ e := by
    apply Subtype.ext
    simpa using hj₀
  obtain ⟨N, hN⟩ := honestKillCoordNoethOfFree (fun i => (⟨t i, ht₀ i⟩ : R₀))
    (⟨T, hT₀⟩ : R₀) j₀ e hj₀'
    (fun q => hfin ↥R₀ (fun i => (⟨t i, ht₀ i⟩ : R₀)) (⟨T, hT₀⟩ : R₀) j₀ e hj₀' q)
    (fun k hk => honestCohomologyVanishing (fun i => (⟨t i, ht₀ i⟩ : R₀)) k hk)
  refine ⟨E₀, N, fun E hE0 => ?_⟩
  exact subringKillTransportN p t T R₀ ht₀ hT₀ j₀ e hj₀ N hN n (phiPow p t (n + 1) E z)
    (hR E hE0) (by rw [PCd_phiPow, hz, phiPow_zero_zero])

end Work.DSM5b
