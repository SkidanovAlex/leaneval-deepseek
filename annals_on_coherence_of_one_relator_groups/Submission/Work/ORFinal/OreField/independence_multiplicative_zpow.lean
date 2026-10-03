import Mathlib
import Submission.Work.ORFinal.AnalyticInput
import Submission.Work.ORBridgeLinnell.Bridge
import Submission.Work.ORLinnell.Laurent.existsUnique_laurent_rep

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORFinal.OreField

/-- The `ℤ`-power of the image of `s` in the envelope is the image of `s ^ z`: this is merely
`gen E` being a monoid homomorphism into the units of `U(G)`. -/
theorem gen_zpow_coe {G : Type*} [Group G] (E : Work.ORVonNeumann.StarRegularEnvelope G)
    (s : G) (z : ℤ) :
    ((((Work.ORBridgeLinnell.gen E s) ^ z : E.Uˣ)) : E.U)
      = ((Work.ORBridgeLinnell.gen E (s ^ z) : E.Uˣ) : E.U) := by
  rw [← map_zpow (Work.ORBridgeLinnell.gen E) s z]

/-- **Linnell independence in the `ℤ`-power form.**  If `s : G` has infinite order modulo `N`
and the exponents `z i` are pairwise distinct, then a `D N`-linear combination of the powers
`(gen E s) ^ (z i)` which vanishes has all coefficients `0`.  This is `independence_D` (Linnell
independence **(I1)** of the M1 bridge) applied to the group elements `s ^ (z i)`, which are
pairwise distinct modulo `N` precisely because `s` has infinite order there. -/
theorem independence_gen_zpow {K : Type*} [Field K] {G : Type*} [Group G]
    (E : Work.ORVonNeumann.StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U]
    (hφK : ∀ k : K, (algebraMap K E.U) k = (algebraMap ℂ E.U) (φK k))
    {N : Subgroup G} (s : G) (hs0 : ∀ k : ℤ, s ^ k ∈ N → k = 0)
    (n : ℕ) (z : Fin n → ℤ) (hz : Function.Injective z)
    (a : Fin n → E.U) (ha : ∀ i, a i ∈ Work.ORBridgeLinnell.D E φK N)
    (hsum : ∑ i, a i * ((((Work.ORBridgeLinnell.gen E s) ^ (z i)) : E.Uˣ) : E.U) = 0) :
    ∀ i, a i = 0 := by
  have hsum' : ∑ i, a i * ((Work.ORBridgeLinnell.gen E (s ^ (z i)) : E.Uˣ) : E.U) = 0 := by
    rw [← hsum]
    exact Finset.sum_congr rfl (fun i _ => by rw [gen_zpow_coe E s (z i)])
  refine Work.ORBridgeLinnell.independence_D E φK hφK N n (fun i => s ^ (z i)) ?_ a ha hsum'
  intro i j hij
  have h1 : s ^ (z i - z j) ∈ N := by
    rwa [zpow_sub]
  exact hz (sub_eq_zero.mp (hs0 _ h1))

/-- **Independence of the `ℤ`-powers of a generator of an extension by `ℤ`.**

Let `N ≤ Γ ≤ G` with `Γ/N` infinite cyclic, generated up to `N` by `s : Γ` (hypothesis `hs`),
and let `E` be the analytic envelope of `G`, `φK : K →+* ℂ` a field embedding.  Then a
`D N`-linear combination of the powers `(gen E s) ^ j` (`j : ℤ`) which vanishes in `U(G)` has
all coefficients `0`.  This is the `Multiplicative ℤ`-indexed form of Linnell independence used
in the Ore-field lemma: the powers of `s` are pairwise distinct modulo `N` because `Γ/N ≅ ℤ`. -/
theorem independence_multiplicative_zpow {K : Type*} [Field K] {G : Type*} [Group G]
    (E : Work.ORVonNeumann.StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U]
    (hφK : ∀ k : K, (algebraMap K E.U) k = (algebraMap ℂ E.U) (φK k))
    {N Γ : Subgroup G} (hN : N ≤ Γ) (hφ : Work.ORLinnell.IsExtensionByZ N Γ) (s : Γ)
    (hs : ∀ h : Γ, ∃ j : ℤ, h * s ^ (-j) ∈ N.subgroupOf Γ)
    (c : Multiplicative ℤ →₀ ↥(Work.ORBridgeLinnell.D E φK N))
    (h : c.sum (fun i d => (d : E.U) *
        ((((Work.ORBridgeLinnell.gen E (s : G)) ^ (Multiplicative.toAdd i)) : E.Uˣ) : E.U)) = 0) :
    c = 0 := by
  classical
  -- `s` has infinite order modulo `N`, as an element of `Γ` and hence of `G`.
  have hs0 : ∀ k : ℤ, s ^ k ∈ N.subgroupOf Γ → k = 0 :=
    Work.ORLinnell.Laurent.sPow_mem_subgroupOf hφ s hs
  have hs0' : ∀ k : ℤ, (s : G) ^ k ∈ N → k = 0 := by
    intro k hk
    exact hs0 k ((Subgroup.mem_subgroupOf).mpr (by rw [Subgroup.coe_zpow]; exact hk))
  -- Enumerate the support of `c`.
  let e : ↥c.support ≃ Fin c.support.card := Finset.equivFin c.support
  -- Rewrite the given finsupp sum as a sum over `Fin c.support.card`.
  have hA : c.sum (fun i d => (d : E.U) *
        ((((Work.ORBridgeLinnell.gen E (s : G)) ^ (Multiplicative.toAdd i)) : E.Uˣ) : E.U))
      = ∑ x ∈ c.support, (c x : E.U) *
        ((((Work.ORBridgeLinnell.gen E (s : G)) ^ (Multiplicative.toAdd x)) : E.Uˣ) : E.U) :=
    Finsupp.sum_of_support_subset c (Finset.Subset.refl _) _ (by intro i _; simp)
  have hB : (∑ x ∈ c.support, (c x : E.U) *
        ((((Work.ORBridgeLinnell.gen E (s : G)) ^ (Multiplicative.toAdd x)) : E.Uˣ) : E.U))
      = ∑ x : ↥c.support, (c (x : Multiplicative ℤ) : E.U) *
        ((((Work.ORBridgeLinnell.gen E (s : G)) ^
          (Multiplicative.toAdd (x : Multiplicative ℤ))) : E.Uˣ) : E.U) :=
    Finset.sum_subtype c.support (fun _ => Iff.rfl) _
  have hC : (∑ x : ↥c.support, (c (x : Multiplicative ℤ) : E.U) *
        ((((Work.ORBridgeLinnell.gen E (s : G)) ^
          (Multiplicative.toAdd (x : Multiplicative ℤ))) : E.Uˣ) : E.U))
      = ∑ i : Fin c.support.card, (c ((e.symm i : ↥c.support) : Multiplicative ℤ) : E.U) *
        ((((Work.ORBridgeLinnell.gen E (s : G)) ^
          (Multiplicative.toAdd ((e.symm i : ↥c.support) : Multiplicative ℤ))) : E.Uˣ) : E.U) :=
    Fintype.sum_equiv e _ _ (by intro x; simp)
  have hsum : (∑ i : Fin c.support.card,
        (c ((e.symm i : ↥c.support) : Multiplicative ℤ) : E.U) *
        ((((Work.ORBridgeLinnell.gen E (s : G)) ^
          (Multiplicative.toAdd ((e.symm i : ↥c.support) : Multiplicative ℤ))) : E.Uˣ) : E.U)) = 0 := by
    rw [← hC, ← hB, ← hA]
    exact h
  -- Linnell independence at the exponents `Multiplicative.toAdd (e.symm i)`.
  have hind := independence_gen_zpow E φK hφK (s : G) hs0' c.support.card
    (fun i : Fin c.support.card =>
      Multiplicative.toAdd ((e.symm i : ↥c.support) : Multiplicative ℤ))
    (by
      intro i j hij
      exact e.symm.injective (Subtype.ext (Multiplicative.toAdd.injective hij)))
    (fun i : Fin c.support.card => (c ((e.symm i : ↥c.support) : Multiplicative ℤ) : E.U))
    (fun i => (c ((e.symm i : ↥c.support) : Multiplicative ℤ)).2)
    hsum
  have hc0 : ∀ i : Fin c.support.card,
      c ((e.symm i : ↥c.support) : Multiplicative ℤ) = 0 :=
    fun i => Subtype.ext (by simpa using hind i)
  refine Finsupp.ext (fun j => ?_)
  by_cases hj : j ∈ c.support
  · have h3 : c ((e.symm (e ⟨j, hj⟩) : ↥c.support) : Multiplicative ℤ) = 0 := hc0 (e ⟨j, hj⟩)
    rwa [show ((e.symm (e ⟨j, hj⟩) : ↥c.support) : Multiplicative ℤ) = j from by simp] at h3
  · by_contra hne
    exact hj ((Finsupp.mem_support_iff).mpr hne)

end Work.ORFinal.OreField
