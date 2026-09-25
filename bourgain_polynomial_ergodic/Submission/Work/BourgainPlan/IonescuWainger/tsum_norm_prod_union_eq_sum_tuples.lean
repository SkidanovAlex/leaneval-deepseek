import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.ShiftPetalOrtho
import Submission.Work.BourgainPlan.IonescuWainger.tsum_norm_sq_sum_of_orthogonal
import Submission.Work.BourgainPlan.IonescuWainger.sigmaAFinset_union_add
import Submission.Work.BourgainPlan.IonescuWainger.coe_sigmaAFinset

/-!
# The Pythagoras step of Tao's `ortho-apply`(i): expanding the major-arc product into tuples

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066, §4,
Theorem `ortho-apply`(i) (the Pythagoras step of the proof), and its ℓ²-band-limited
implementation in this workspace (`tsum_prod_shift_mul_conj_eq_zero_of_petal_l2`,
`tsum_norm_sq_sum_of_orthogonal`).

The major-arc system `f_{Σ_{A₀ ∪ P i}} = Σ_{δ ∈ Σ_{A₀ ∪ P i}} f δ` of a sunflower with core `A₀`
and pairwise disjoint petals `P i` decomposes, by the direct-sum identity
`Σ_{A₀ ∪ P i} = Σ_{A₀} ⊕ Σ_{P i}` (`sigmaAFinset_union_add`), as the sum over `α i ∈ Σ_{P i}` of
the *shifted* major-arc functions `f_{Σ_{A₀} + α i} = Σ_{γ ∈ Σ_{A₀}} f (γ + α i)`.  Consequently
the pointwise product of the `r` systems is a sum over the tuples
`α : Π i, Σ_{P i}` of the products `Π i, f_{Σ_{A₀} + α i}`.

Since the tuples are pairwise orthogonal in ℓ²(ℤ) (`tsum_prod_shift_mul_conj_eq_zero_of_petal_l2`,
which is Tao's `ortho`(iii) with a core), Pythagoras
(`tsum_norm_sq_sum_of_orthogonal`) turns the squared ℓ²-norm of the product into the sum of the
squared ℓ²-norms of the tuple products:

`Σ_m ‖Π_i f_{Σ_{A₀ ∪ P i}}(m)‖² = Σ_α Σ_m ‖Π_i f_{Σ_{A₀} + α_i}(m)‖²`.

## Main declarations

* `Work.BourgainPlan.IonescuWainger.prod_sum_attach` — a product of sums is the sum over the
  dependent tuples of the products (the `Finset.pi`/subtype bookkeeping);
* `Work.BourgainPlan.IonescuWainger.memℓp_prod_of_memℓp` — a finite pointwise product of `ℓ²(ℤ)`
  sequences is `ℓ²` (the `ℓ² ⊆ ℓ^∞` bound absorbs all but one factor into a summable one);
* `Work.BourgainPlan.IonescuWainger.tsum_prod_shift_orthogonal_fin` — the orthogonality of the
  shifted tuple products for `Fin r` (transport of the `Fin (n+1)` capstone along `finCongr`);
* `Work.BourgainPlan.IonescuWainger.tsum_norm_prod_union_eq_sum_tuples` — the target identity.
-/

open Finset MeasureTheory
open scoped BigOperators ENNReal lp

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-- **A product of finite sums is the sum over the dependent tuples of the products.**  For a
finite index type `ι` and finsets `t i`,

`∏ i, ∑ j ∈ t i, g i j = ∑ x : ((i : ι) → ↥(t i)), ∏ i, g i (x i).1`,

the `Finset.pi`-type bookkeeping behind the expansion of the major-arc product into the tuple
sums `∑ α : Π i, Σ_{P i}, Π i, f_{Σ_{A₀} + α i}`. -/
theorem prod_sum_attach {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : ι → Type*}
    (t : (i : ι) → Finset (κ i)) (g : (i : ι) → κ i → ℂ) :
    (∏ i, ∑ j ∈ t i, g i j) = ∑ x : ((i : ι) → ↥(t i)), ∏ i, g i (x i).1 := by
  classical
  rw [Finset.prod_univ_sum]
  refine (Finset.sum_bij (fun (y : (i : ι) → ↥(t i)) (_ : y ∈ Finset.univ) => fun i => (y i).1)
    ?_ ?_ ?_ ?_).symm
  · intro y _
    exact Fintype.mem_piFinset.mpr (fun i => (y i).2)
  · intro y₁ _ y₂ _ h
    funext i
    exact Subtype.ext (congr_fun h i)
  · intro x hx
    refine ⟨fun i => ⟨x i, (Fintype.mem_piFinset.mp hx) i⟩, Finset.mem_univ _, ?_⟩
    rfl
  · intro y _
    rfl

/-- **A finite pointwise product of `ℓ²(ℤ)` sequences is `ℓ²`.**  Each factor is bounded by its
`ℓ²`-norm (as `ℓ² ⊆ ℓ^∞` for the counting measure), so all factors except one may be bounded by
constants and the remaining squared modulus is summable. -/
theorem memℓp_prod_of_memℓp {ι : Type*} [Fintype ι] [DecidableEq ι] (i₀ : ι) {h : ι → ℤ → ℂ}
    (hh : ∀ i, Memℓp (h i) 2) :
    Memℓp (fun m : ℤ => ∏ i, h i m) 2 := by
  classical
  refine memℓp_gen (p := 2) ?_
  simp only [ENNReal.toReal_ofNat]
  have hsq : ∀ i, Summable fun m : ℤ => ‖h i m‖ ^ 2 := by
    intro i
    have := (memℓp_gen_iff (p := 2) (by norm_num)).mp (hh i)
    simpa [Real.rpow_two] using this
  have hbound : ∀ i m, ‖h i m‖ ^ 2 ≤ ∑' j, ‖h i j‖ ^ 2 := fun i m =>
    (hsq i).le_tsum m (fun j _ => sq_nonneg _)
  have hmain : Summable fun m : ℤ =>
      (∏ i ∈ Finset.univ.erase i₀, (∑' j, ‖h i j‖ ^ 2)) * ‖h i₀ m‖ ^ 2 :=
    (hsq i₀).mul_left _
  rw [show (fun m : ℤ => ‖∏ i, h i m‖ ^ (2:ℝ)) = (fun m => ∏ i, ‖h i m‖ ^ 2) from by
    funext m; rw [Real.rpow_two, norm_prod, ← Finset.prod_pow]]
  refine Summable.of_nonneg_of_le (fun m => Finset.prod_nonneg fun i _ => sq_nonneg _)
    (fun m => ?_) hmain
  rw [← Finset.prod_erase_mul Finset.univ (fun i => ‖h i m‖ ^ 2) (Finset.mem_univ i₀)]
  exact mul_le_mul_of_nonneg_right
    (Finset.prod_le_prod₀ (fun i _ => sq_nonneg _) (fun i _ => hbound i m)) (sq_nonneg _)

/-- **Tao's `ortho`(iii) with core, for `Fin r`-indexed tuples** (`r ≥ 1`).  The `Fin r` form of
`tsum_prod_shift_mul_conj_eq_zero_of_petal_l2`: since `r = (r - 1) + 1`, the capstone is applied
along `finCongr` and the products reindexed by `Equiv.prod_comp`. -/
theorem tsum_prod_shift_orthogonal_fin {S A₀ : Finset ℕ} {r : ℕ} (hr : 1 ≤ r)
    (h2 : ∀ q ∈ S, 2 ≤ q) (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    (hA₀ : A₀ ⊆ S) {P : Fin r → Finset ℕ} (hP : ∀ i, P i ⊆ S)
    (hdisjP : ∀ i j : Fin r, i ≠ j → Disjoint (P i) (P j))
    (hdisjA : ∀ i, Disjoint A₀ (P i))
    {f : Circle → ℤ → ℂ} (hf : ∀ δ, Memℓp (f δ) 2) {ε : ℝ}
    (hF : ∀ δ, HasFreqSupport (f δ) (hf δ) (arcSet δ ε))
    (hsmall : 2 * (r : ℝ) * ε * ((QA A₀ * (∏ i, QA (P i)) : ℕ) : ℝ) < 1) :
    ∀ α β : ((i : Fin r) → ↥(sigmaAFinset (P i))), α ≠ β →
      ∑' m : ℤ, (∏ i, (∑ γ ∈ sigmaAFinset A₀, f (γ + (α i).1) m))
        * star (∏ i, (∑ γ ∈ sigmaAFinset A₀, f (γ + (β i).1) m)) = 0 := by
  intro α β hne
  set n := r - 1 with hn
  have hsucc : n + 1 = r := Nat.sub_add_cancel hr
  let e : Fin (n + 1) ≃ Fin r := finCongr hsucc
  have hzero : ∀ i, (0 : ℕ) ∉ P i := fun i h0 => by have := h2 0 (hP i h0); omega
  have hmain := tsum_prod_shift_mul_conj_eq_zero_of_petal_l2 (n := n) (S := S) (A₀ := A₀)
    h2 hS hA₀ (P := fun j : Fin (n + 1) => P (e j)) (fun j => hP (e j))
    (fun i j hij => hdisjP (e i) (e j) (fun hh => hij (e.injective hh)))
    (fun j => hdisjA (e j)) hf hF
    (α := fun j => (α (e j)).1) (β := fun j => (β (e j)).1)
    (fun j => by rw [← coe_sigmaAFinset (hzero (e j))]; exact (α (e j)).2)
    (fun j => by rw [← coe_sigmaAFinset (hzero (e j))]; exact (β (e j)).2)
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
  rw [← Equiv.prod_comp e (fun i => ∑ γ ∈ sigmaAFinset A₀, f (γ + (α i).1) m),
    ← Equiv.prod_comp e (fun i => ∑ γ ∈ sigmaAFinset A₀, f (γ + (β i).1) m)]

/-- **The Pythagoras step of Tao's `ortho-apply`(i).**  For a sunflower with core `A₀` and
pairwise disjoint petals `P i` (`i : Fin r`, `r ≥ 1`) inside a set `S` of pairwise coprime integers
`≥ 2`, and a band-limited `ℓ²(ℤ)`-system `f` (each `f δ` supported in the arc `arcSet δ ε`), under
the smallness condition `2 r ε Q_{A₀} ∏_i Q_{P i} < 1` the squared `ℓ²`-norm of the product of the
major-arc systems `f_{Σ_{A₀ ∪ P i}}` equals the sum, over the tuples `α : Π i, Σ_{P i}`, of the
squared `ℓ²`-norms of the products `Π i, f_{Σ_{A₀} + α i}`.

This is the expansion

`‖Π_i f_{Σ_{A₀ ∪ P i}}‖_{ℓ²}² = Σ_{α ∈ Π_i Σ_{P i}} ‖Π_i f_{Σ_{A₀} + α_i}‖_{ℓ²}²`

obtained by decomposing each factor along `Σ_{A₀ ∪ P i} = ⊔_α (Σ_{A₀} + α)` and applying
Pythagoras to the pairwise orthogonal tuple products. -/
theorem tsum_norm_prod_union_eq_sum_tuples {S A₀ : Finset ℕ} {r : ℕ} (hr : 1 ≤ r)
    (h2 : ∀ q ∈ S, 2 ≤ q) (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    (hA₀ : A₀ ⊆ S) {P : Fin r → Finset ℕ} (hP : ∀ i, P i ⊆ S)
    (hdisjP : ∀ i j : Fin r, i ≠ j → Disjoint (P i) (P j))
    (hdisjA : ∀ i, Disjoint A₀ (P i))
    {f : Circle → ℤ → ℂ} (hf : ∀ δ, Memℓp (f δ) 2) {ε : ℝ}
    (hF : ∀ δ, HasFreqSupport (f δ) (hf δ) (arcSet δ ε))
    (hsmall : 2 * (r : ℝ) * ε * ((QA A₀ * (∏ i, QA (P i)) : ℕ) : ℝ) < 1) :
    ∑' m : ℤ, ‖∏ i, (∑ δ ∈ sigmaAFinset (A₀ ∪ P i), f δ m)‖ ^ 2
      = ∑ α : (i : Fin r) → ↥(sigmaAFinset (P i)),
          ∑' m : ℤ, ‖∏ i, (∑ γ ∈ sigmaAFinset A₀, f (γ + (α i).1) m)‖ ^ 2 := by
  classical
  -- the shifted major-arc tuple products `g α = Π_i f_{Σ_{A₀} + α i}`
  let g : ((i : Fin r) → ↥(sigmaAFinset (P i))) → ℤ → ℂ :=
    fun α m => ∏ i, (∑ γ ∈ sigmaAFinset A₀, f (γ + (α i).1) m)
  -- pointwise, the product expands as the sum over the tuples
  have hpoint : ∀ m : ℤ, (∏ i, ∑ δ ∈ sigmaAFinset (A₀ ∪ P i), f δ m)
      = ∑ α : ((i : Fin r) → ↥(sigmaAFinset (P i))), g α m := by
    intro m
    have h1 : (∏ i, ∑ δ ∈ sigmaAFinset (A₀ ∪ P i), f δ m)
        = ∏ i, ∑ a ∈ sigmaAFinset (P i), ∑ γ ∈ sigmaAFinset A₀, f (γ + a) m :=
      Finset.prod_congr rfl (fun i _ => sigmaAFinset_union_add h2 hS hA₀ (hP i) (hdisjA i) f m)
    rw [h1]
    exact prod_sum_attach (t := fun i => sigmaAFinset (P i))
      (g := fun i a => ∑ γ ∈ sigmaAFinset A₀, f (γ + a) m)
  -- each tuple product is square summable
  have hg : ∀ α : ((i : Fin r) → ↥(sigmaAFinset (P i))), Memℓp (g α) 2 := by
    intro α
    have hfac : ∀ i : Fin r, Memℓp (fun m => ∑ γ ∈ sigmaAFinset A₀, f (γ + (α i).1) m) 2 :=
      fun i => Memℓp.finsetSum (sigmaAFinset A₀) (fun γ _ => hf (γ + (α i).1))
    exact memℓp_prod_of_memℓp (ι := Fin r) ⟨0, hr⟩ hfac
  -- the tuple products are pairwise orthogonal
  have horth : ∀ α β : ((i : Fin r) → ↥(sigmaAFinset (P i))), α ≠ β →
      ∑' m : ℤ, g α m * star (g β m) = 0 :=
    fun α β hne => tsum_prod_shift_orthogonal_fin hr h2 hS hA₀ hP hdisjP hdisjA hf hF hsmall α β hne
  have h1 : (∑' m : ℤ, ‖∏ i, (∑ δ ∈ sigmaAFinset (A₀ ∪ P i), f δ m)‖ ^ 2)
      = ∑' m : ℤ, ‖∑ α : ((i : Fin r) → ↥(sigmaAFinset (P i))), g α m‖ ^ 2 :=
    tsum_congr (fun m => by rw [hpoint m])
  rw [h1, tsum_norm_sq_sum_of_orthogonal (g := g) hg horth]

end Work.BourgainPlan.IonescuWainger
