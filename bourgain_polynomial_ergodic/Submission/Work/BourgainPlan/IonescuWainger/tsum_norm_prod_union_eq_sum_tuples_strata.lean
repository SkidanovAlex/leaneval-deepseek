import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.tsum_norm_prod_union_eq_sum_tuples
import Submission.Work.BourgainPlan.IonescuWainger.sigmaStrataFinset_union_add
import Submission.Work.BourgainPlan.IonescuWainger.tsum_prod_shift_mul_conj_eq_zero_of_petal_l2_strata

/-!
# The Pythagoras step of Tao's `ortho-apply`(i), strata form

This is the strata analogue of `tsum_norm_prod_union_eq_sum_tuples.lean`: the major-arc system is
that of Tao's strata `Σ_A = sigmaStrataFinset A` rather than the exact-denominator sets
`Σ_A = sigmaAFinset A`.  The proof is the same port verbatim; the three ingredients are the
direct-sum decomposition `sigmaStrataFinset_union_add`, the generic tuple bookkeeping
`prod_sum_attach`, and the strata orthogonality
`tsum_prod_shift_mul_conj_eq_zero_of_petal_l2_strata` (transported from `Fin (n+1)` to `Fin r`).
-/

open Finset MeasureTheory
open scoped BigOperators ENNReal lp

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-- **Tao's `ortho`(iii) with core, for `Fin r`-indexed tuples of Tao's strata** (`r ≥ 1`).  The
`Fin r` form of `tsum_prod_shift_mul_conj_eq_zero_of_petal_l2_strata`: since `r = (r - 1) + 1`, the
capstone is applied along `finCongr` and the products reindexed by `Equiv.prod_comp`. -/
theorem tsum_prod_shift_orthogonal_fin_strata {S A₀ : Finset ℕ} {r : ℕ} (hr : 1 ≤ r)
    (h2 : ∀ q ∈ S, 2 ≤ q) (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    (hA₀ : A₀ ⊆ S) {P : Fin r → Finset ℕ} (hP : ∀ i, P i ⊆ S)
    (hdisjP : ∀ i j : Fin r, i ≠ j → Disjoint (P i) (P j))
    (hdisjA : ∀ i, Disjoint A₀ (P i))
    {f : Circle → ℤ → ℂ} (hf : ∀ δ, Memℓp (f δ) 2) {ε : ℝ}
    (hF : ∀ δ, HasFreqSupport (f δ) (hf δ) (arcSet δ ε))
    (hsmall : 2 * (r : ℝ) * ε * ((QA A₀ * (∏ i, QA (P i)) : ℕ) : ℝ) < 1) :
    ∀ α β : ((i : Fin r) → ↥(sigmaStrataFinset (P i))), α ≠ β →
      ∑' m : ℤ, (∏ i, (∑ γ ∈ sigmaStrataFinset A₀, f (γ + (α i).1) m))
        * star (∏ i, (∑ γ ∈ sigmaStrataFinset A₀, f (γ + (β i).1) m)) = 0 := by
  intro α β hne
  set n := r - 1 with hn
  have hsucc : n + 1 = r := Nat.sub_add_cancel hr
  let e : Fin (n + 1) ≃ Fin r := finCongr hsucc
  have hmain := tsum_prod_shift_mul_conj_eq_zero_of_petal_l2_strata (n := n) (S := S) (A₀ := A₀)
    h2 hS hA₀ (P := fun j : Fin (n + 1) => P (e j)) (fun j => hP (e j))
    (fun i j hij => hdisjP (e i) (e j) (fun hh => hij (e.injective hh)))
    (fun j => hdisjA (e j)) hf hF
    (α := fun j => (α (e j)).1) (β := fun j => (β (e j)).1)
    (fun j => (α (e j)).2) (fun j => (β (e j)).2)
    (by
      by_contra hc
      push Not at hc
      apply hne
      funext i
      refine Subtype.ext ?_
      have h := hc (e.symm i)
      rwa [Equiv.apply_symm_apply] at h)
    (by
      have hprod : (∏ j : Fin (n + 1), QA (P (e j))) = ∏ i : Fin r, QA (P i) :=
        Equiv.prod_comp e (fun i => QA (P i))
      rw [hprod, hsucc]
      exact hsmall)
  refine (tsum_congr (fun m => ?_)).trans hmain
  rw [← Equiv.prod_comp e (fun i => ∑ γ ∈ sigmaStrataFinset A₀, f (γ + (α i).1) m),
    ← Equiv.prod_comp e (fun i => ∑ γ ∈ sigmaStrataFinset A₀, f (γ + (β i).1) m)]

/-- The Pythagoras step of Tao's `ortho-apply`(i) in Tao's strata convention: for a sunflower with
core `A₀` and pairwise disjoint petals `P : Fin r → Finset ℕ` inside a pairwise coprime `S` of
integers `≥ 2`, a band-limited system `f`, and the per-tuple smallness
`2 r ε Q_{A₀} ∏_i Q_{P i} < 1`,

`Σ_m ‖∏_i f_{Σ_{A₀ ∪ P i}}(m)‖² = Σ_{α : Π_i Σ_{P i}} Σ_m ‖∏_i f_{Σ_{A₀} + α_i}(m)‖²`,

where `f_{Σ_B} = Σ_{δ ∈ Σ_B} f_δ` is the sum over Tao's stratum `Σ_B = sigmaStrataFinset B`.

Route: port `Work.BourgainPlan.IonescuWainger.tsum_norm_prod_union_eq_sum_tuples` (same directory)
verbatim, replacing `sigmaAFinset` by `sigmaStrataFinset` everywhere.  Three ingredients, all
present: (a) the pointwise expansion of each factor,
`∑ δ ∈ sigmaStrataFinset (A₀ ∪ P i), f δ m = ∑ a ∈ sigmaStrataFinset (P i), ∑ γ ∈ sigmaStrataFinset A₀, f (γ + a) m`,
is exactly `Work.BourgainPlan.IonescuWainger.sigmaStrataFinset_union_add`
(`sigmaStrataFinset_union_add.lean`, proved); (b) the distribution of the product over `i` into the
tuple sum is the generic `prod_sum_attach`; (c) the pairwise orthogonality of the tuple products
`g α = fun m => ∏ i, ∑ γ ∈ sigmaStrataFinset A₀, f (γ + (α i).1) m` for `α ≠ β` is the strata petal
orthogonality `Work.BourgainPlan.IonescuWainger.tsum_prod_shift_mul_conj_eq_zero_of_petal_l2_strata`
(proved), transported from `Fin (n+1)` to `Fin r` exactly as `tsum_prod_shift_orthogonal_fin` does
(`hr : 1 ≤ r`, `n := r - 1`, `finCongr`); the `ℓ²`-membership of each `g α` is
`memℓp_prod_of_memℓp`.  Then `tsum_norm_sq_sum_of_orthogonal` (generic, proved) gives the identity. -/
theorem tsum_norm_prod_union_eq_sum_tuples_strata {S A₀ : Finset ℕ} {r : ℕ} (hr : 1 ≤ r)
    (h2 : ∀ q ∈ S, 2 ≤ q) (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    (hA₀ : A₀ ⊆ S) {P : Fin r → Finset ℕ} (hP : ∀ i, P i ⊆ S)
    (hdisjP : ∀ i j : Fin r, i ≠ j → Disjoint (P i) (P j))
    (hdisjA : ∀ i, Disjoint A₀ (P i))
    {f : Work.BourgainPlan.IonescuWainger.Circle → ℤ → ℂ} (hf : ∀ δ, Memℓp (f δ) 2) {ε : ℝ}
    (hF : ∀ δ, Work.BourgainPlan.IonescuWainger.HasFreqSupport (f δ) (hf δ)
      (Work.BourgainPlan.IonescuWainger.arcSet δ ε))
    (hsmall : 2 * (r : ℝ) * ε * ((Work.BourgainPlan.IonescuWainger.QA A₀ *
      (∏ i, Work.BourgainPlan.IonescuWainger.QA (P i)) : ℕ) : ℝ) < 1) :
    ∑' m : ℤ, ‖∏ i,
        (∑ δ ∈ Work.BourgainPlan.IonescuWainger.sigmaStrataFinset (A₀ ∪ P i), f δ m)‖ ^ 2
      = ∑ α : (i : Fin r) → ↥(Work.BourgainPlan.IonescuWainger.sigmaStrataFinset (P i)),
          ∑' m : ℤ, ‖∏ i, (∑ γ ∈ Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A₀,
            f (γ + (α i).1) m)‖ ^ 2 := by
  classical
  -- the shifted major-arc tuple products `g α = Π_i f_{Σ_{A₀} + α i}`
  let g : ((i : Fin r) → ↥(sigmaStrataFinset (P i))) → ℤ → ℂ :=
    fun α m => ∏ i, (∑ γ ∈ sigmaStrataFinset A₀, f (γ + (α i).1) m)
  -- pointwise, the product expands as the sum over the tuples
  have hpoint : ∀ m : ℤ, (∏ i, ∑ δ ∈ sigmaStrataFinset (A₀ ∪ P i), f δ m)
      = ∑ α : ((i : Fin r) → ↥(sigmaStrataFinset (P i))), g α m := by
    intro m
    have h1 : (∏ i, ∑ δ ∈ sigmaStrataFinset (A₀ ∪ P i), f δ m)
        = ∏ i, ∑ a ∈ sigmaStrataFinset (P i), ∑ γ ∈ sigmaStrataFinset A₀, f (γ + a) m :=
      Finset.prod_congr rfl (fun i _ =>
        sigmaStrataFinset_union_add h2 hS hA₀ (hP i) (hdisjA i) f m)
    rw [h1]
    exact prod_sum_attach (t := fun i => sigmaStrataFinset (P i))
      (g := fun i a => ∑ γ ∈ sigmaStrataFinset A₀, f (γ + a) m)
  -- each tuple product is square summable
  have hg : ∀ α : ((i : Fin r) → ↥(sigmaStrataFinset (P i))), Memℓp (g α) 2 := by
    intro α
    have hfac : ∀ i : Fin r, Memℓp (fun m => ∑ γ ∈ sigmaStrataFinset A₀, f (γ + (α i).1) m) 2 :=
      fun i => Memℓp.finsetSum (sigmaStrataFinset A₀) (fun γ _ => hf (γ + (α i).1))
    exact memℓp_prod_of_memℓp (ι := Fin r) ⟨0, hr⟩ hfac
  -- the tuple products are pairwise orthogonal
  have horth : ∀ α β : ((i : Fin r) → ↥(sigmaStrataFinset (P i))), α ≠ β →
      ∑' m : ℤ, g α m * star (g β m) = 0 :=
    fun α β hne =>
      tsum_prod_shift_orthogonal_fin_strata hr h2 hS hA₀ hP hdisjP hdisjA hf hF hsmall α β hne
  have h1 : (∑' m : ℤ, ‖∏ i, (∑ δ ∈ sigmaStrataFinset (A₀ ∪ P i), f δ m)‖ ^ 2)
      = ∑' m : ℤ, ‖∑ α : ((i : Fin r) → ↥(sigmaStrataFinset (P i))), g α m‖ ^ 2 :=
    tsum_congr (fun m => by rw [hpoint m])
  rw [h1, tsum_norm_sq_sum_of_orthogonal (g := g) hg horth]

end Work.BourgainPlan.IonescuWainger
