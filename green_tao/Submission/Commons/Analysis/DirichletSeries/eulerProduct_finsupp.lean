import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Separation.CompletelyRegular

namespace Commons.Analysis.DirichletSeries

open Finset
open scoped BigOperators Topology

/-! ## Helper: `Finsupp` as a sigma over its support with nonzero values -/

section FinsuppSigma

variable {ι α : Type*}

/-- Reconstruct a finitely supported function from a finset `s` and nonzero values on `s`. -/
noncomputable def finsuppMk [DecidableEq ι] [Zero α]
    (s : Finset ι) (g : ↥s → {a : α // a ≠ 0}) : ι →₀ α :=
  Finsupp.onFinset s (fun i => if h : i ∈ s then (g ⟨i, h⟩).1 else 0)
    (fun i hi => by
      by_cases h : i ∈ s
      · exact h
      · exact absurd (dif_neg h) hi)

lemma finsuppMk_apply [DecidableEq ι] [Zero α]
    (s : Finset ι) (g : ↥s → {a : α // a ≠ 0}) (i : ι) :
    finsuppMk s g i = if h : i ∈ s then (g ⟨i, h⟩).1 else 0 :=
  Finsupp.onFinset_apply

lemma finsuppMk_support [DecidableEq ι] [Zero α] [DecidableEq α]
    (s : Finset ι) (g : ↥s → {a : α // a ≠ 0}) :
    (finsuppMk s g).support = s := by
  rw [finsuppMk, Finsupp.support_onFinset]
  ext a
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨-, h⟩
    by_contra ha
    exact h (dif_neg ha)
  · intro ha
    exact ⟨ha, by rw [dif_pos ha]; exact (g ⟨a, ha⟩).2⟩

lemma finsuppMk_val [DecidableEq ι] [Zero α]
    (s : Finset ι) (g : ↥s → {a : α // a ≠ 0}) (i : ↥s) :
    finsuppMk s g i.1 = (g i).1 := by
  rw [finsuppMk_apply, dif_pos i.2]

noncomputable def finsuppEquivSigma [DecidableEq ι] [Zero α] [DecidableEq α] :
    (ι →₀ α) ≃ (Σ s : Finset ι, (↥s → {a : α // a ≠ 0})) where
  toFun f := ⟨f.support, fun i => ⟨f i.1, Finsupp.mem_support_iff.1 i.2⟩⟩
  invFun x := finsuppMk x.1 x.2
  left_inv f := by
    ext i
    rw [finsuppMk_apply]
    by_cases h : i ∈ f.support
    · rw [dif_pos h]
    · rw [dif_neg h]
      have : f i = 0 := by
        by_contra hne
        exact h (Finsupp.mem_support_iff.2 hne)
      rw [this]
  right_inv x := by
    obtain ⟨s, g⟩ := x
    have hsupp : (finsuppMk s g).support = s := finsuppMk_support s g
    apply Sigma.ext hsupp
    apply Function.hfunext (congrArg (fun t : Finset ι => (↥t : Sort _)) hsupp)
    intro a a' ha
    rw [heq_iff_eq]
    apply Subtype.ext
    have hcoe : (a : ι) = (a' : ι) :=
      (Subtype.heq_iff_coe_eq (fun x => by rw [hsupp])).1 ha
    have hamem : (a : ι) ∈ s := hcoe ▸ a'.2
    change finsuppMk s g (a : ι) = (g a').1
    rw [finsuppMk_apply, dif_pos hamem]
    rw [show (⟨(a : ι), hamem⟩ : ↥s) = a' from Subtype.ext hcoe]

lemma finsuppEquivSigma_symm_apply [DecidableEq ι] [Zero α] [DecidableEq α]
    (s : Finset ι) (g : ↥s → {a : α // a ≠ 0}) :
    (finsuppEquivSigma (ι := ι) (α := α)).symm ⟨s, g⟩ = finsuppMk s g := rfl

lemma finsuppMk_prod [DecidableEq ι] [Zero α] [DecidableEq α] {M : Type*} [CommMonoid M]
    (w : ι → α → M) (s : Finset ι) (g : ↥s → {a : α // a ≠ 0}) :
    ∏ i ∈ (finsuppMk s g).support, w i ((finsuppMk s g) i) = ∏ i : ↥s, w i.1 (g i).1 := by
  rw [finsuppMk_support]
  rw [← Finset.prod_coe_sort s (fun i => w i ((finsuppMk s g) i))]
  refine Finset.prod_congr rfl ?_
  intro i _
  rw [finsuppMk_val]

end FinsuppSigma

section SumHelpers

variable {α : Type*} [Fintype α] [DecidableEq α] [Zero α]

/-- Split a sum over `α` into the value at `0` and the sum over the nonzero values. -/
lemma sum_univ_eq_add_sum_ne_zero {M : Type*} [AddCommMonoid M] (f : α → M) :
    ∑ a, f a = f 0 + ∑ a : {a : α // a ≠ 0}, f a.1 := by
  conv_lhs => rw [← Finset.insert_erase (Finset.mem_univ (0 : α))]
  rw [Finset.sum_insert (Finset.notMem_erase (0 : α) Finset.univ)]
  congr 1
  exact Finset.sum_subtype (Finset.univ.erase (0 : α))
    (by intro x; simp [Finset.mem_erase]) f

/-- `Finset.prod_univ_sum` in the special case that the inner finsets are all `univ`. -/
lemma prod_univ_comm {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] {M : Type*} [CommSemiring M]
    (f : ∀ i, κ i → M) :
    ∏ i, ∑ j, f i j = ∑ x : ∀ i, κ i, ∏ i, f i (x i) := by
  rw [Finset.prod_univ_sum (fun _ => Finset.univ) f, Fintype.piFinset_univ]

/-- The local `Summable`-datum of the Euler product, expressed over nonzero values. -/
lemma sum_norm_sub_ite_eq_sum_ne_zero {ι : Type*} (v : ι → α → ℂ)
    (h1 : ∀ n, v n 0 = 1) (n : ι) :
    (∑ a : α, ‖v n a - (if a = 0 then 1 else 0)‖)
      = ∑ a : {a : α // a ≠ 0}, ‖v n a.1‖ := by
  rw [sum_univ_eq_add_sum_ne_zero (fun a => ‖v n a - (if a = 0 then 1 else 0)‖)]
  have h0 : ‖v n 0 - (if (0 : α) = 0 then (1 : ℂ) else 0)‖ = 0 := by
    rw [if_pos rfl, h1 n, sub_self, norm_zero]
  rw [h0, zero_add]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [if_neg a.2, sub_zero]

end SumHelpers

/-- General Euler product for finitely supported local data. -/
theorem hasSum_finsupp_prod {ι : Type*} [DecidableEq ι]
    (α : Type*) [Fintype α] [DecidableEq α] [Zero α]
    (v : ι → α → ℂ) (h1 : ∀ n, v n 0 = 1)
    (hsum : Summable (fun n : ι => ∑ a : α, ‖v n a - (if a = 0 then 1 else 0)‖)) :
    HasSum (fun f : ι →₀ α => ∏ n ∈ f.support, v n (f n))
      (∏' n : ι, ∑ a : α, v n a) := by
  classical
  let r : ι → ℂ := fun i => ∑ a : {a : α // a ≠ 0}, v i a.1
  let R : ι → ℝ := fun i => ∑ a : α, ‖v i a - (if a = 0 then 1 else 0)‖
  have hRsum : Summable R := hsum
  have hRnn : ∀ i, 0 ≤ R i := fun i => Finset.sum_nonneg (fun a _ => norm_nonneg _)
  have hrnorm : Summable (fun i => ‖r i‖) := by
    refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_) hRsum
    rw [show R i = ∑ a : {a : α // a ≠ 0}, ‖v i a.1‖ from sum_norm_sub_ite_eq_sum_ne_zero v h1 i]
    exact norm_sum_le _ _
  have hfibernorm : ∀ s : Finset ι,
      (∑' g : ↥s → {a : α // a ≠ 0}, ∏ i : ↥s, ‖v i.1 (g i).1‖) = ∏ i ∈ s, R i := by
    intro s
    rw [tsum_fintype]
    rw [← prod_univ_comm (fun (i : ↥s) (b : {a : α // a ≠ 0}) => ‖v i.1 b.1‖)]
    rw [← Finset.prod_coe_sort s (fun i => R i)]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    exact (sum_norm_sub_ite_eq_sum_ne_zero v h1 i.1).symm
  have houter : Summable (fun s : Finset ι => ∏ i ∈ s, R i) :=
    summable_finsetProd_of_summable_nonneg hRnn hRsum
  let F : (ι →₀ α) → ℂ := fun f => ∏ n ∈ f.support, v n (f n)
  let f : (Σ s : Finset ι, (↥s → {a : α // a ≠ 0})) → ℂ :=
    fun x => ∏ i ∈ (finsuppMk x.1 x.2).support, v i ((finsuppMk x.1 x.2) i)
  have hnormf : (fun x : Σ s : Finset ι, (↥s → {a : α // a ≠ 0}) =>
      ∏ i : ↥x.1, ‖v i.1 (x.2 i).1‖) = fun x => ‖f x‖ := by
    funext x
    show (∏ i : ↥x.1, ‖v i.1 (x.2 i).1‖)
        = ‖∏ i ∈ (finsuppMk x.1 x.2).support, v i ((finsuppMk x.1 x.2) i)‖
    rw [norm_prod]
    exact (finsuppMk_prod (fun i a => ‖v i a‖) x.1 x.2).symm
  have hG : Summable (fun x : Σ s : Finset ι, (↥s → {a : α // a ≠ 0}) =>
      ∏ i : ↥x.1, ‖v i.1 (x.2 i).1‖) := by
    refine (summable_sigma_of_nonneg
      (fun x => Finset.prod_nonneg (fun i _ => norm_nonneg _))).mpr ⟨?_, ?_⟩
    · intro s
      exact Summable.of_finite
    · refine houter.congr (fun s => ?_)
      exact (hfibernorm s).symm
  have hfsum : Summable f := by
    refine Summable.of_norm ?_
    rw [← hnormf]
    exact hG
  have hsumr : Summable (fun s : Finset ι => ∏ i ∈ s, r i) :=
    summable_finsetProd_of_summable_norm hrnorm
  have hfiber : ∀ s : Finset ι,
      (∑' g : ↥s → {a : α // a ≠ 0}, f ⟨s, g⟩) = ∏ i ∈ s, r i := by
    intro s
    rw [tsum_fintype]
    simp_rw [show ∀ g : ↥s → {a : α // a ≠ 0}, f ⟨s, g⟩ = ∏ i : ↥s, v i.1 (g i).1 from
      fun g => finsuppMk_prod v s g]
    rw [← prod_univ_comm (fun (i : ↥s) (b : {a : α // a ≠ 0}) => v i.1 b.1)]
    rw [← Finset.prod_coe_sort s (fun i => r i)]
  have htsum : ∑' x, f x = ∏' i, ∑ a, v i a := by
    rw [Summable.tsum_sigma' (fun s => Summable.of_finite) hfsum]
    simp_rw [hfiber]
    rw [← tprod_one_add hsumr]
    refine tprod_congr (fun i => ?_)
    rw [sum_univ_eq_add_sum_ne_zero (v i), h1 i]
  have hfhas : HasSum f (∏' i, ∑ a, v i a) := by
    rw [← htsum]
    exact hfsum.hasSum
  have hcomp : f = F ∘ ⇑(finsuppEquivSigma (ι := ι) (α := α)).symm := by
    funext x
    show (∏ i ∈ (finsuppMk x.1 x.2).support, v i ((finsuppMk x.1 x.2) i))
        = (∏ n ∈ ((finsuppEquivSigma (ι := ι) (α := α)).symm x).support,
            v n (((finsuppEquivSigma (ι := ι) (α := α)).symm x) n))
    rfl
  rw [hcomp] at hfhas
  exact (Equiv.hasSum_iff (finsuppEquivSigma (ι := ι) (α := α)).symm).mp hfhas

/-- Euler product for finitely supported local data. -/
theorem eulerProduct_finsupp (α : Type*) [Fintype α] [DecidableEq α] [Zero α]
    (v : ℕ → α → ℂ) (h1 : ∀ n, v n 0 = 1)
    (hzero : ∀ n : ℕ, ¬ n.Prime → ∀ a : α, a ≠ 0 → v n a = 0)
    (hsum : Summable (fun n : ℕ => ∑ a : α, ‖v n a - (if a = 0 then 1 else 0)‖)) :
    HasSum (fun f : ℕ →₀ α => ∏ n ∈ f.support, v n (f n))
      (∏' n : ℕ, ∑ a : α, v n a) := by
  have _hzero := hzero
  exact hasSum_finsupp_prod (ι := ℕ) α v h1 hsum

end Commons.Analysis.DirichletSeries