import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod
import Submission.Commons.Analysis.InnerProductSpace.iMulti_sum_swap_expansion

set_option linter.style.haveILetI false

namespace Commons.Analysis.InnerProductSpace

open scoped BigOperators

/-- A family of strictly more than `finrank K M` vectors of a finite module `M` over a division
ring is linearly dependent. -/
lemma not_linearIndependent_of_finrank_lt {K M : Type*} [DivisionRing K] [AddCommGroup M]
    [Module K M] [Module.Finite K M] {k : ℕ} (hk : Module.finrank K M < k) (w : Fin k → M) :
    ¬ LinearIndependent K w := by
  intro hw
  have hspan : Submodule.span K (Set.range w) ≤ (⊤ : Submodule K M) := le_top
  have h1 := Submodule.finrank_mono hspan
  rw [finrank_top] at h1
  have h2 : Module.finrank K ↥(Submodule.span K (Set.range w)) = k := by
    rw [Module.finrank_eq_card_basis (Module.Basis.span hw)]
    simp
  omega

/-- If strictly more than `finrank K U` members of a family lie in a submodule `U`, then the
exterior product of the family vanishes: the members lying in `U` are linearly dependent, hence
so is the whole family, and an alternating map vanishes on a dependent family. -/
lemma iMulti_eq_zero_of_card_lt_mem_submodule {K E : Type*} [Field K] [AddCommGroup E]
    [Module K E] [Module.Finite K E] {i : ℕ} (U : Submodule K E) (z : Fin i → E)
    (T : Finset (Fin i)) (hT : Module.finrank K U < T.card) (hz : ∀ k ∈ T, z k ∈ U) :
    exteriorPower.ιMulti K i z = 0 := by
  classical
  let φ : Fin T.card ↪o Fin i := T.orderEmbOfFin rfl
  let w : Fin T.card → U := fun j => ⟨z (φ j), hz (φ j) (Finset.orderEmbOfFin_mem T rfl j)⟩
  have hw : ¬ LinearIndependent K w := not_linearIndependent_of_finrank_lt hT w
  have hcomp : ¬ LinearIndependent K (⇑U.subtype ∘ w) :=
    fun h => hw (LinearIndependent.of_comp U.subtype h)
  have hzφ : ¬ LinearIndependent K (z ∘ (fun j => φ j)) := by
    simpa [Function.comp_def, w] using hcomp
  have hzz : ¬ LinearIndependent K z :=
    fun h => hzφ (h.comp (fun j => φ j) φ.injective)
  exact AlternatingMap.map_linearDependent (exteriorPower.ιMulti K i) z hzz

/-- If every vector of a family `y : Fin i → E` of vectors of norm at most `1` lies within
distance `δ` of a subspace `U ≤ E` of rank `s`, then the norm of their exterior product is at
most `2 ^ i * δ ^ (i - s)`.  (Vectors close to `U`: expanding `y k = p k + r k` with
`p k ∈ U`, `‖r k‖ ≤ δ`, every wedge term with at most `i - s - 1` factors `r k` contains `s + 1`
factors from the `s`-dimensional space `U` and hence vanishes; the remaining `≤ 2 ^ i` terms are
bounded by `δ ^ (i - s)` using `exteriorPower_norm_wedge_le_prod`.) -/
theorem norm_iMulti_le_pow_of_dist_le_subspace
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {s i : ℕ} (U : Submodule ℝ E) (hU : Module.finrank ℝ U = s)
    (y : Fin i → E) (hy : ∀ k, ‖y k‖ ≤ 1) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hdist : ∀ k, ∃ p ∈ U, ‖y k - p‖ ≤ δ) :
    ‖exteriorPower.ιMulti ℝ i y‖ ≤ (2 : ℝ) ^ i * δ ^ (i - s) := by
  classical
  let p : Fin i → E := fun k => U.starProjection (y k)
  let q : Fin i → E := fun k => y k - p k
  have hpU : ∀ k, p k ∈ U := fun k => Submodule.starProjection_apply_mem U (y k)
  have hpn : ∀ k, ‖p k‖ ≤ 1 := fun k =>
    le_trans (Submodule.norm_starProjection_apply_le U (y k)) (hy k)
  have hqn : ∀ k, ‖q k‖ ≤ δ := fun k => by
    obtain ⟨a, haU, ha⟩ := hdist k
    calc ‖q k‖ = ⨅ x : U, ‖y k - (x : E)‖ := Submodule.starProjection_minimal (U := U) (y k)
      _ ≤ ‖y k - a‖ := ciInf_le
          (show BddBelow (Set.range (fun x : U => ‖y k - (x : E)‖)) from
            ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩)
          ⟨a, haU⟩
      _ ≤ δ := ha
  have hy_eq : y = fun k => p k + q k := by
    funext k
    simp [q, p]
  set z : Finset (Fin i) → ⋀[ℝ]^i E :=
    fun T => exteriorPower.ιMulti ℝ i (fun k => if k ∈ T then q k else p k) with hzdef
  have hexp : exteriorPower.ιMulti ℝ i y = ∑ T : Finset (Fin i), z T := by
    rw [hy_eq]
    exact iMulti_sum_swap_expansion p q
  have hzvo : ∀ T : Finset (Fin i), ¬ (s + T.card ≥ i) → z T = 0 := by
    intro T hT
    have hcard : Module.finrank ℝ U < Tᶜ.card := by
      rw [hU, Finset.card_compl, Fintype.card_fin]
      omega
    refine iMulti_eq_zero_of_card_lt_mem_submodule U _ Tᶜ hcard ?_
    intro k hk
    have hkT : k ∉ T := by simpa using hk
    simpa [hkT] using hpU k
  have hzbound : ∀ T : Finset (Fin i), ‖z T‖ ≤ δ ^ (i - s) := by
    intro T
    by_cases hT : s + T.card ≥ i
    · have hstep : ∀ k : Fin i, ‖(if k ∈ T then q k else p k)‖ ≤ if k ∈ T then δ else 1 := by
        intro k
        by_cases hk : k ∈ T
        · simp only [if_pos hk]; exact hqn k
        · simp only [if_neg hk]; exact hpn k
      calc ‖z T‖ ≤ ∏ k : Fin i, ‖(if k ∈ T then q k else p k)‖ :=
            exteriorPower_norm_wedge_le_prod _
        _ ≤ ∏ k : Fin i, (if k ∈ T then δ else (1 : ℝ)) :=
            Finset.prod_le_prod (fun k _ => norm_nonneg _) (fun k _ => hstep k)
        _ = δ ^ T.card := by
            rw [Finset.prod_ite_mem (s := (Finset.univ : Finset (Fin i))) (t := T)
              (f := fun _ => δ)]
            simp [Finset.prod_const]
        _ ≤ δ ^ (i - s) :=
            pow_le_pow_of_le_one hδ0 hδ1 (by omega)
    · rw [hzvo T hT, norm_zero]
      exact pow_nonneg hδ0 _
  calc ‖exteriorPower.ιMulti ℝ i y‖
      = ‖∑ T : Finset (Fin i), z T‖ := by rw [hexp]
    _ ≤ ∑ T : Finset (Fin i), ‖z T‖ := norm_sum_le _ _
    _ = ∑ T ∈ (Finset.univ.filter (fun T : Finset (Fin i) => s + T.card ≥ i)), ‖z T‖ := by
        refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
        intro T _ hT
        exact norm_eq_zero.mpr (hzvo T (by simpa using hT))
    _ ≤ ∑ T ∈ (Finset.univ.filter (fun T : Finset (Fin i) => s + T.card ≥ i)), δ ^ (i - s) :=
        Finset.sum_le_sum (fun T _ => hzbound T)
    _ = ((Finset.univ.filter (fun T : Finset (Fin i) => s + T.card ≥ i)).card : ℝ) *
          δ ^ (i - s) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ i * δ ^ (i - s) := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hδ0 _)
        have h1 : (Finset.univ.filter (fun T : Finset (Fin i) => s + T.card ≥ i)).card ≤ 2 ^ i :=
          le_trans (Finset.card_filter_le _ _)
            (by rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin])
        exact_mod_cast h1

end Commons.Analysis.InnerProductSpace