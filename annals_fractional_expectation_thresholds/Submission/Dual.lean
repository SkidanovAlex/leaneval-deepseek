import Mathlib.Probability.Distributions.SetBernoulli
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Sequences
import ChallengeDeps
import Submission.Prob
import Submission.Minimals
import Submission.Qpos
import Submission.Lbound


open ProbabilityTheory MeasureTheory unitInterval Set Filter
open scoped ENNReal NNReal BigOperators unitInterval Topology
open FractionalExpectationThresholds

attribute [local instance] Classical.propDecidable

namespace Submission
namespace FET

universe u
variable {X : Type u} [Fintype X]

/-! ## Talagrand duality: tools

All helper lemmas are self-contained; the final theorem is `talagrand_dual` below.
-/

/-- The `T`-shadow sum of `ν` (`ν(⟨T⟩)`). -/
noncomputable def tdSpread (ν : Set X → ℝ) (T : Set X) : ℝ :=
  ∑ E : Set X, if T ⊆ E then ν E else 0

/-- Mass of `ν` inside the family `𝓕`. -/
noncomputable def tdMassIn (𝓕 : Set (Set X)) (ν : Set X → ℝ) : ℝ :=
  ∑ E : Set X, if E ∈ 𝓕 then ν E else 0

lemma tdSpread_eq_filter (ν : Set X → ℝ) (T : Set X) :
    tdSpread ν T = ∑ E ∈ (Finset.univ : Finset (Set X)).filter (fun E => T ⊆ E), ν E := by
  classical
  rw [tdSpread]
  exact (Finset.sum_filter (s := (Finset.univ : Finset (Set X))) (f := fun E : Set X => ν E) (p := fun E => T ⊆ E)).symm

lemma tdMassIn_eq_filter (𝓕 : Set (Set X)) (ν : Set X → ℝ) :
    tdMassIn 𝓕 ν = ∑ E ∈ (Finset.univ : Finset (Set X)).filter (fun E => E ∈ 𝓕), ν E := by
  classical
  rw [tdMassIn]
  exact (Finset.sum_filter (s := (Finset.univ : Finset (Set X))) (f := fun E : Set X => ν E) (p := fun E => E ∈ 𝓕)).symm

/-- Spread is nonnegative for nonnegative `ν`. -/
lemma tdSpread_nonneg {ν : Set X → ℝ} (hν : ∀ E, 0 ≤ ν E) (T : Set X) : 0 ≤ tdSpread ν T := by
  classical
  rw [tdSpread_eq_filter]
  exact Finset.sum_nonneg (fun E hE => hν E)

/-- Spread is monotone in `ν`. -/
lemma tdSpread_mono {ν ν' : Set X → ℝ} (h : ∀ E, ν E ≤ ν' E) (T : Set X) :
    tdSpread ν T ≤ tdSpread ν' T := by
  classical
  rw [tdSpread_eq_filter, tdSpread_eq_filter]
  exact Finset.sum_le_sum (fun E hE => h E)

/-- Spread of the pointwise restriction of `ν` to `𝓕` is at most the spread of `ν`. -/
lemma tdSpread_restrict_le {ν : Set X → ℝ} (hν : ∀ E, 0 ≤ ν E) (𝓕 : Set (Set X)) (T : Set X) :
    tdSpread (fun E => if E ∈ 𝓕 then ν E else 0) T ≤ tdSpread ν T := by
  classical
  rw [tdSpread_eq_filter, tdSpread_eq_filter]
  exact Finset.sum_le_sum (fun E hE => by
    by_cases hE𝓕 : E ∈ 𝓕
    · simp [hE𝓕]
    · simp [hE𝓕, hν E])

/-- Spread of a scaled function. -/
lemma tdSpread_smul (c : ℝ) (ν : Set X → ℝ) (T : Set X) :
    tdSpread (fun E => c * ν E) T = c * tdSpread ν T := by
  classical
  rw [tdSpread_eq_filter, tdSpread_eq_filter]
  rw [← Finset.mul_sum]

/-- Mass in `𝓕` of the restriction of `ν` to `𝓕` equals the total mass in `𝓕`. -/
lemma tdMassIn_restrict (𝓕 : Set (Set X)) (ν : Set X → ℝ) :
    tdMassIn 𝓕 (fun E => if E ∈ 𝓕 then ν E else 0) = tdMassIn 𝓕 ν := by
  classical
  rw [tdMassIn_eq_filter, tdMassIn_eq_filter]
  apply Finset.sum_congr rfl
  intro E hE
  simp [(Finset.mem_filter.mp hE).2]

/-- For a measure with total mass 1 supported on 𝓕: the total of the restricted measure is the
mass in 𝓕. -/
lemma tdSum_restrict (𝓕 : Set (Set X)) (ν : Set X → ℝ) :
    (∑ E : Set X, if E ∈ 𝓕 then ν E else 0) = tdMassIn 𝓕 ν := by
  classical
  rw [tdMassIn_eq_filter]
  rw [← Finset.sum_filter]

/-- trivial: 1/(1/2) = 2. -/
lemma td_half_inv : (2 : ℝ)⁻¹ = (1 / 2 : ℝ) := by norm_num

/-- q_f ≥ p for weakly p-small families. -/
lemma qf_ge_of_weakly_small (𝓕 : Set (Set X)) (p : I) (hp : IsWeaklySmall p 𝓕) :
    (p : ℝ) ≤ (q_f 𝓕 : ℝ) := by
  classical
  unfold q_f
  exact le_csSup ⟨(1 : I), by intro q hq; exact (q : I).2.2⟩ hp

/-- If `q_f < p` then 𝓕 is not weakly `p`-small. -/
lemma not_weakly_small_of_qf_lt (𝓕 : Set (Set X)) (p : I)
    (hp : (q_f 𝓕 : ℝ) < (p : ℝ)) : ¬ IsWeaklySmall p 𝓕 := by
  intro hws
  have hle := qf_ge_of_weakly_small 𝓕 p hws
  linarith

/-- 𝓕 is nonempty under `2 ≤ l 𝓕`. -/
lemma nonempty_of_two_le_l (𝓕 : Set (Set X)) (hl : 2 ≤ l 𝓕) : (𝓕 : Set (Set X)).Nonempty := by
  classical
  by_contra h
  have hF : 𝓕 = ∅ := by
    ext S
    by_cases hS : S ∈ 𝓕
    · exfalso; exact h ⟨S, hS⟩
    · simp [hS]
  have hl0 : l 𝓕 = 0 := by
    simp [l, hF]
  omega

end FET
end Submission

namespace Submission
namespace FET

universe u
variable {X : Type u} [Fintype X]


/-! ## Finite-dimensional Farkas machinery

We work in the ambient normed space `tdE := (Set X → ℝ) × ℝ`.  For `p ∈ (0,1)` define the
upward "spread cone" `tdCone 𝓕`; the key dichotomy is that a point `w₀ = (p^·, -1/2)` outside
the closure of the cone yields (by separation) a covering witness `g`. -/

noncomputable section
abbrev tdE (X : Type u) [Fintype X] := (Set X → ℝ) × ℝ

/-- `w₀ = (p^·, -1/2)` in `tdE`. -/
noncomputable def tdW0 (pv : ℝ) : tdE X := ((fun T : Set X => pv ^ T.ncard), -((1 / 2 : ℝ)))

/-- The upward cone of (approximate) spread vectors with `𝓕`-mass constraints. -/
noncomputable def tdCone (𝓕 : Set (Set X)) : Set (tdE X) :=
  {z | ∃ ν : Set X → ℝ, (∀ E : Set X, 0 ≤ ν E) ∧
       (∀ T : Set X, tdSpread ν T ≤ z.1 T) ∧
       (-tdMassIn 𝓕 ν ≤ z.2)}


/-- Spread of a pointwise sum. -/
lemma tdSpread_add (ν ν' : Set X → ℝ) (T : Set X) :
    tdSpread (fun E => ν E + ν' E) T = tdSpread ν T + tdSpread ν' T := by
  classical
  rw [tdSpread_eq_filter, tdSpread_eq_filter, tdSpread_eq_filter]
  exact Finset.sum_add_distrib

/-- Mass in 𝓕 of a pointwise sum. -/
lemma tdMassIn_add (𝓕 : Set (Set X)) (ν ν' : Set X → ℝ) :
    tdMassIn 𝓕 (fun E => ν E + ν' E) = tdMassIn 𝓕 ν + tdMassIn 𝓕 ν' := by
  classical
  rw [tdMassIn_eq_filter, tdMassIn_eq_filter, tdMassIn_eq_filter]
  exact Finset.sum_add_distrib

/-- Mass in 𝓕 of a scaled function. -/
lemma tdMassIn_smul (𝓕 : Set (Set X)) (c : ℝ) (ν : Set X → ℝ) :
    tdMassIn 𝓕 (fun E => c * ν E) = c * tdMassIn 𝓕 ν := by
  classical
  rw [tdMassIn_eq_filter, tdMassIn_eq_filter]
  rw [Finset.mul_sum]

lemma tdCone_zero_mem (𝓕 : Set (Set X)) : (0, 0) ∈ tdCone 𝓕 := by
  refine ⟨(0 : Set X → ℝ), ?_, ?_, ?_⟩
  · intro E; simp
  · intro T; simp [tdSpread]
  · simp [tdMassIn]

lemma tdCone_add_mem (𝓕 : Set (Set X)) {z z' : tdE X} (hz : z ∈ tdCone 𝓕) (hz' : z' ∈ tdCone 𝓕) :
    z + z' ∈ tdCone 𝓕 := by
  rcases hz with ⟨ν, hν0, hν, hνm⟩
  rcases hz' with ⟨ν', hν'0, hν', hν'm⟩
  refine ⟨fun E => ν E + ν' E, ?_, ?_, ?_⟩
  · intro E; exact add_nonneg (hν0 E) (hν'0 E)
  · intro T
    rw [tdSpread_add]
    exact add_le_add (hν T) (hν' T)
  · rw [tdMassIn_add]
    have hz2 : (z + z').2 = z.2 + z'.2 := by simp
    rw [hz2]
    linarith

lemma tdCone_smul_mem (𝓕 : Set (Set X)) {z : tdE X} (hz : z ∈ tdCone 𝓕) {c : ℝ} (hc : 0 ≤ c) :
    c • z ∈ tdCone 𝓕 := by
  rcases hz with ⟨ν, hν0, hν, hνm⟩
  refine ⟨fun E => c * ν E, ?_, ?_, ?_⟩
  · intro E; exact mul_nonneg hc (hν0 E)
  · intro T
    rw [tdSpread_smul]
    exact mul_le_mul_of_nonneg_left (hν T) hc
  · rw [tdMassIn_smul]
    have hz2 : (c • z).2 = c * z.2 := by simp
    rw [hz2]
    linarith [mul_le_mul_of_nonneg_left hνm hc]

/-- Canonical basis vector `δ_T = (1_{T'=T}, 0)`. -/
noncomputable def tdDelta (T : Set X) : tdE X :=
  ((fun T' : Set X => if T' = T then 1 else 0), (0 : ℝ))

/-- Second-coordinate unit `(0, 1)`. -/
noncomputable def tdOne : tdE X := ((0 : Set X → ℝ), (1 : ℝ))

/-- Generator of the spread-cone indexed by `E ∈ 𝓕`. -/
noncomputable def tdGen (E : Set X) : tdE X :=
  ((fun T' : Set X => if T' ⊆ E then 1 else 0), -(1 : ℝ))

lemma tdCone_convex (𝓕 : Set (Set X)) : Convex ℝ (tdCone 𝓕) := by
  rw [convex_iff_forall_pos]
  intro x hx y hy a b ha hb hab
  have hx' : a • x ∈ tdCone 𝓕 := tdCone_smul_mem 𝓕 hx (le_of_lt ha)
  have hy' : b • y ∈ tdCone 𝓕 := tdCone_smul_mem 𝓕 hy (le_of_lt hb)
  exact tdCone_add_mem 𝓕 hx' hy'

/-- Spread of the point mass at `E`. -/
lemma tdSpread_singleton (E T' : Set X) :
    tdSpread (fun E' : Set X => if E' = E then (1 : ℝ) else 0) T' = if T' ⊆ E then (1 : ℝ) else 0 := by
  classical
  by_cases hsub : T' ⊆ E
  · rw [if_pos hsub]
    rw [tdSpread_eq_filter]
    calc
      (∑ E' ∈ (Finset.univ : Finset (Set X)).filter (fun E' => T' ⊆ E'), if E' = E then (1 : ℝ) else 0)
          = if E ∈ (Finset.univ : Finset (Set X)).filter (fun E' => T' ⊆ E') then (1 : ℝ) else 0 := by
              simp [Finset.sum_ite_eq]
      _ = (1 : ℝ) := by simp [hsub]
  · rw [if_neg hsub]
    rw [tdSpread_eq_filter]
    apply Finset.sum_eq_zero
    intro E' hE'
    have hTE' : T' ⊆ E' := (Finset.mem_filter.mp hE').2
    by_cases hE'E : E' = E
    · exfalso; exact hsub (hE'E ▸ hTE')
    · simp [hE'E]

/-- Mass in `𝓕` of the point mass at `E`. -/
lemma tdMassIn_singleton (𝓕 : Set (Set X)) (E : Set X) :
    tdMassIn 𝓕 (fun E' : Set X => if E' = E then (1 : ℝ) else 0) = if E ∈ 𝓕 then (1 : ℝ) else 0 := by
  classical
  rw [tdMassIn_eq_filter]
  calc
    (∑ E' ∈ (Finset.univ : Finset (Set X)).filter (fun E' => E' ∈ 𝓕), if E' = E then (1 : ℝ) else 0)
        = if E ∈ (Finset.univ : Finset (Set X)).filter (fun E' => E' ∈ 𝓕) then (1 : ℝ) else 0 := by
            simp [Finset.sum_ite_eq]
    _ = if E ∈ 𝓕 then (1 : ℝ) else 0 := by simp

lemma tdCone_delta_mem (𝓕 : Set (Set X)) (T : Set X) : tdDelta T ∈ tdCone 𝓕 := by
  refine ⟨(0 : Set X → ℝ), ?_, ?_, ?_⟩
  · intro E; simp
  · intro T'
    rw [tdSpread_eq_filter]
    by_cases hT : T' = T
    · simp [hT, tdDelta]
    · simp [hT, tdDelta]
  · simp [tdMassIn, tdDelta]

lemma tdCone_unit_mem (𝓕 : Set (Set X)) : tdOne ∈ tdCone 𝓕 := by
  refine ⟨(0 : Set X → ℝ), ?_, ?_, ?_⟩
  · intro E; simp
  · intro T'
    rw [tdSpread_eq_filter]
    simp [tdOne]
  · simp [tdMassIn, tdOne]

lemma tdCone_gen_mem (𝓕 : Set (Set X)) {E : Set X} (hE : E ∈ 𝓕) : tdGen E ∈ tdCone 𝓕 := by
  classical
  refine ⟨(fun E' : Set X => if E' = E then 1 else 0), ?_, ?_, ?_⟩
  · intro E'; by_cases h : E' = E <;> simp [h]
  · intro T'
    rw [tdSpread_singleton]
    simp [tdGen]
  · rw [tdMassIn_singleton]
    simp [hE, tdGen]

/-- Injection of the function coordinate into the ambient product space. -/
noncomputable def tdInl : (Set X → ℝ) →ₗ[ℝ] tdE X where
  toFun := fun x => (x, 0)
  map_add' := by intro x y; ext <;> simp
  map_smul' := by intro a x; ext <;> simp

/-- Injection of the real coordinate into the ambient product space. -/
noncomputable def tdInr : ℝ →ₗ[ℝ] tdE X where
  toFun := fun t => (0, t)
  map_add' := by intro x y; ext <;> simp
  map_smul' := by intro a x; ext <;> simp

/-- Function-level basis identity: `pv^· = Σ_T pv^|T| · 1_{·=T}`. -/
lemma td_pow_fun_decomp (pv : ℝ) :
    (fun T0 : Set X => pv ^ T0.ncard) =
      ∑ T : Set X, pv ^ T.ncard • (fun T' : Set X => if T' = T then 1 else 0) := by
  classical
  funext T0
  simp [Finset.sum_ite_eq]

/-- Function-level basis identity: `1_{·⊆E} = Σ_{T⊆E} 1_{·=T}`. -/
lemma td_ind_fun_decomp (E : Set X) :
    (fun T0 : Set X => if T0 ⊆ E then 1 else 0) =
      ∑ T ∈ (Finset.univ : Finset (Set X)).filter (fun T => T ⊆ E),
        (fun T' : Set X => if T' = T then 1 else 0) := by
  classical
  funext T0
  rw [Finset.sum_apply]
  by_cases h : T0 ⊆ E
  · rw [if_pos h]
    simp [Finset.sum_ite_eq, h]
  · rw [if_neg h]
    symm
    apply Finset.sum_eq_zero
    intro T hT
    have hTsub : T ⊆ E := (Finset.mem_filter.mp hT).2
    by_cases hEq : T0 = T
    · exfalso; exact h (hEq ▸ hTsub)
    · simp [hEq]

/-- A separating functional over the cone is nonnegative on the cone. -/
lemma td_sep_fun_nonneg (𝓕 : Set (Set X)) (pv : ℝ) (hpv0 : 0 < pv)
    (hW : tdW0 pv ∉ closure (tdCone 𝓕)) :
    ∃ f : StrongDual ℝ (tdE X),
      (∀ z ∈ tdCone 𝓕, 0 ≤ f z) ∧ f (tdW0 pv) < 0 := by
  classical
  obtain ⟨f, u, v, hfw0u, huv, hfv⟩ :=
    geometric_hahn_banach_compact_closed
      (s := ({tdW0 pv} : Set (tdE X))) (t := closure (tdCone 𝓕))
      (convex_singleton _) (isCompact_singleton : IsCompact ({tdW0 pv} : Set (tdE X)))
      (tdCone_convex 𝓕).closure isClosed_closure (by exact Set.disjoint_singleton_left.mpr hW)
  have hcl0 : (0 : tdE X) ∈ closure (tdCone 𝓕) := subset_closure (tdCone_zero_mem 𝓕)
  have hv0 : v < 0 := by
    have h : v < f (0 : tdE X) := hfv 0 hcl0
    simpa using h
  have hfw0 : f (tdW0 pv) < 0 := by
    have hltu : f (tdW0 pv) < u := by simpa using (hfw0u (tdW0 pv) (by simp))
    linarith
  have hFnonneg : ∀ z ∈ tdCone 𝓕, 0 ≤ f z := by
    intro z hz
    by_contra hzneg
    have hzl : f z < 0 := lt_of_not_ge hzneg
    have htnz : f z ≠ 0 := ne_of_lt hzl
    let t : ℝ := (v - 1) / f z + 1
    have ht0 : 0 < t := by
      have hv1 : v - 1 < 0 := by linarith
      have hd : 0 < (v - 1) / f z := div_pos_of_neg_of_neg hv1 hzl
      dsimp [t]
      linarith
    have htm : t • z ∈ tdCone 𝓕 := tdCone_smul_mem 𝓕 hz (le_of_lt ht0)
    have hvt : v < f (t • z) := hfv (t • z) (subset_closure htm)
    have hcalc : f (t • z) = v - 1 + f z := by
      calc
        f (t • z) = t * f z := by simpa using map_smul f t z
        _ = v - 1 + f z := by
          dsimp [t]
          field_simp [htnz]
    linarith
  exact ⟨f, hFnonneg, hfw0⟩


/-- First coordinate of a sum of scaled `tdDelta`s. -/
lemma td_fst_sum_smul (c : Set X → ℝ) :
    (∑ T : Set X, c T • tdDelta T).1 = ∑ T : Set X, c T • (tdDelta T).1 := by
  calc
    (∑ T : Set X, c T • tdDelta T).1 = ∑ T : Set X, (c T • tdDelta T).1 := by
      exact map_sum (AddMonoidHom.fst (Set X → ℝ) ℝ) (fun T : Set X => c T • tdDelta T) (Finset.univ)
    _ = ∑ T : Set X, c T • (tdDelta T).1 := by
      apply Finset.sum_congr rfl
      intro T hT
      simp

/-- Second coordinate of a sum of scaled `tdDelta`s is zero. -/
lemma td_snd_sum_smul_zero (c : Set X → ℝ) :
    (∑ T : Set X, c T • tdDelta T).2 = 0 := by
  calc
    (∑ T : Set X, c T • tdDelta T).2 = ∑ T : Set X, (c T • tdDelta T).2 := by
      exact map_sum (AddMonoidHom.snd (Set X → ℝ) ℝ) (fun T : Set X => c T • tdDelta T) (Finset.univ)
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro T hT
      simp [tdDelta]

/-- `tdW0 pv` in the `tdDelta`-basis. -/
lemma td_w0_decomp (pv : ℝ) :
    tdW0 pv = (∑ T : Set X, pv ^ T.ncard • tdDelta T) + (-((1 / 2 : ℝ))) • tdOne := by
  classical
  apply Prod.ext
  · have h1 : ((tdW0 pv : tdE X)).1 = (fun T0 : Set X => pv ^ T0.ncard) := by
      simp [tdW0]
    have h2 : (fun T0 : Set X => pv ^ T0.ncard) = (∑ T : Set X, pv ^ T.ncard • tdDelta T).1 := by
      calc
        (fun T0 : Set X => pv ^ T0.ncard) = ∑ T : Set X, pv ^ T.ncard • (tdDelta T).1 := by
          funext T0
          simp [tdDelta, Finset.sum_ite_eq]
        _ = (∑ T : Set X, pv ^ T.ncard • tdDelta T).1 :=
          (td_fst_sum_smul (fun T : Set X => pv ^ T.ncard)).symm
    have h3 : (∑ T : Set X, pv ^ T.ncard • tdDelta T).1 =
        ((∑ T : Set X, pv ^ T.ncard • tdDelta T) + (-((1 / 2 : ℝ))) • tdOne).1 := by
      simp [tdOne]
    exact h1.trans (h2.trans h3)
  · have h1 : ((tdW0 pv : tdE X)).2 = -((1 / 2 : ℝ)) := by
      simp [tdW0]
    have h2 : -((1 / 2 : ℝ)) =
        ((∑ T : Set X, pv ^ T.ncard • tdDelta T) + (-((1 / 2 : ℝ))) • tdOne).2 := by
      simp [tdOne, td_snd_sum_smul_zero]
    exact h1.trans h2

/-- The generator `tdGen E` in the `tdDelta`-basis. -/
lemma td_gen_decomp (E : Set X) :
    tdGen E = (∑ T ∈ (Finset.univ : Finset (Set X)).filter (fun T => T ⊆ E), tdDelta T) +
      (-(1 : ℝ)) • tdOne := by
  classical
  apply Prod.ext
  · have h1 : ((tdGen E : tdE X)).1 = (fun T0 : Set X => if T0 ⊆ E then 1 else 0) := by
      simp [tdGen]
    have h2 : (fun T0 : Set X => if T0 ⊆ E then 1 else 0) =
        (∑ T ∈ (Finset.univ : Finset (Set X)).filter (fun T => T ⊆ E), tdDelta T).1 := by
      calc
        (fun T0 : Set X => if T0 ⊆ E then 1 else 0) =
            ∑ T ∈ (Finset.univ : Finset (Set X)).filter (fun T => T ⊆ E), (tdDelta T).1 := by
          funext T0
          rw [Finset.sum_apply]
          by_cases h : T0 ⊆ E
          · rw [if_pos h]
            simp [tdDelta, Finset.sum_ite_eq, h]
          · rw [if_neg h]
            symm
            apply Finset.sum_eq_zero
            intro T hT
            have hTsub : T ⊆ E := (Finset.mem_filter.mp hT).2
            by_cases hEq : T0 = T
            · exfalso; exact h (hEq ▸ hTsub)
            · simp [tdDelta, hEq]
        _ = (∑ T ∈ (Finset.univ : Finset (Set X)).filter (fun T => T ⊆ E), tdDelta T).1 := by
          exact (map_sum (AddMonoidHom.fst (Set X → ℝ) ℝ) (fun T : Set X => tdDelta T)
            ((Finset.univ : Finset (Set X)).filter (fun T => T ⊆ E))).symm
    have h3 : (∑ T ∈ (Finset.univ : Finset (Set X)).filter (fun T => T ⊆ E), tdDelta T).1 =
        ((∑ T ∈ (Finset.univ : Finset (Set X)).filter (fun T => T ⊆ E), tdDelta T) +
          (-(1 : ℝ)) • tdOne).1 := by
      simp [tdOne]
    exact h1.trans (h2.trans h3)
  · have h1 : ((tdGen E : tdE X)).2 = -1 := by
      simp [tdGen]
    have hz : (∑ T ∈ (Finset.univ : Finset (Set X)).filter (fun T => T ⊆ E), tdDelta T).2 = 0 := by
      calc
        (∑ T ∈ (Finset.univ : Finset (Set X)).filter (fun T => T ⊆ E), tdDelta T).2
            = ∑ T ∈ (Finset.univ : Finset (Set X)).filter (fun T => T ⊆ E), (tdDelta T).2 := by
                exact map_sum (AddMonoidHom.snd (Set X → ℝ) ℝ) (fun T : Set X => tdDelta T)
                  ((Finset.univ : Finset (Set X)).filter (fun T => T ⊆ E))
        _ = 0 := by
                apply Finset.sum_eq_zero
                intro T hT
                simp [tdDelta]
    have h2 : -1 =
        ((∑ T ∈ (Finset.univ : Finset (Set X)).filter (fun T => T ⊆ E), tdDelta T) +
          (-(1 : ℝ)) • tdOne).2 := by
      simp [tdOne, hz]
    exact h1.trans h2

/-- Preimage of a linear functional applied to a sum of scaled generators. -/
lemma td_map_sum_scaled (f : StrongDual ℝ (tdE X)) (c : Set X → ℝ) :
    f (∑ T : Set X, c T • tdDelta T) = ∑ T : Set X, c T * f (tdDelta T) := by
  calc
    f (∑ T : Set X, c T • tdDelta T) = ∑ T : Set X, f (c T • tdDelta T) := by
      exact map_sum f (fun T : Set X => c T • tdDelta T) (Finset.univ)
    _ = ∑ T : Set X, c T * f (tdDelta T) := by
      apply Finset.sum_congr rfl
      intro T hT
      simpa using map_smul f (c T) (tdDelta T)

/-- A real certificate from separation (covering + cost `≤ 1/2`). -/
lemma td_sep_core (𝓕 : Set (Set X)) (pv : ℝ) (hpv0 : 0 < pv)
    (hW : tdW0 pv ∉ closure (tdCone 𝓕)) :
    ∃ g : Set X → ℝ, (∀ S : Set X, 0 ≤ g S) ∧
      (∀ E ∈ 𝓕, (1 : ℝ) ≤ (∑ S : Set X, if S ⊆ E then g S else 0)) ∧
      ((∑ S : Set X, g S * pv ^ S.ncard) ≤ (1 / 2 : ℝ)) := by
  classical
  obtain ⟨f, hf0, hfw0⟩ := td_sep_fun_nonneg 𝓕 pv hpv0 hW
  let φ : Set X → ℝ := fun S => f (tdDelta S)
  let c : ℝ := f tdOne
  have hφ0 : ∀ S, 0 ≤ φ S := by
    intro S
    exact hf0 (tdDelta S) (tdCone_delta_mem 𝓕 S)
  have hc0 : 0 ≤ c := by
    exact hf0 tdOne (tdCone_unit_mem 𝓕)
  have hdecomp : f (tdW0 pv) = (∑ T : Set X, pv ^ T.ncard * φ T) - (1 / 2 : ℝ) * c := by
    rw [td_w0_decomp]
    rw [map_add, map_sum]
    simp_rw [map_smul]
    simp [φ, c]
    ring
  have hfw0neg : f (tdW0 pv) < 0 := hfw0
  have hcost : (∑ T : Set X, pv ^ T.ncard * φ T) < (1 / 2 : ℝ) * c := by linarith
  have hcpos : 0 < c := by
    by_contra hcnot
    have hcle0 : c ≤ 0 := le_of_not_gt hcnot
    have hcz : c = 0 := le_antisymm hcle0 hc0
    have hsumlt : (∑ T : Set X, pv ^ T.ncard * φ T) < 0 := by
      have := hcost
      rw [hcz] at this
      simpa using this
    have hsumge : 0 ≤ ∑ T : Set X, pv ^ T.ncard * φ T := by
      exact Finset.sum_nonneg (fun T hT => mul_nonneg (pow_nonneg (le_of_lt hpv0) _) (hφ0 T))
    linarith
  have hdecompgen : ∀ E ∈ 𝓕,
      f (tdGen E) = (∑ T ∈ (Finset.univ : Finset (Set X)).filter (fun T => T ⊆ E), φ T) - c := by
    intro E hE
    rw [td_gen_decomp]
    rw [map_add, map_sum]
    simp_rw [map_smul]
    simp [φ, c]
    ring
  have hcover_φ : ∀ E ∈ 𝓕, c ≤ ∑ T ∈ (Finset.univ : Finset (Set X)).filter (fun T => T ⊆ E), φ T := by
    intro E hE
    have h := hf0 (tdGen E) (tdCone_gen_mem 𝓕 hE)
    have hd := hdecompgen E hE
    linarith
  let g : Set X → ℝ := fun S => φ S / c
  refine ⟨g, ?_, ?_, ?_⟩
  · intro S
    exact div_nonneg (hφ0 S) (le_of_lt hcpos)
  · intro E hE
    have hcov : c ≤ ∑ S ∈ (Finset.univ : Finset (Set X)).filter (fun S => S ⊆ E), φ S := hcover_φ E hE
    rw [show (∑ S : Set X, if S ⊆ E then g S else 0) =
        ∑ S ∈ (Finset.univ : Finset (Set X)).filter (fun S => S ⊆ E), g S by
          rw [← Finset.sum_filter]]
    rw [show (∑ S ∈ (Finset.univ : Finset (Set X)).filter (fun S => S ⊆ E), g S) =
        (∑ S ∈ (Finset.univ : Finset (Set X)).filter (fun S => S ⊆ E), φ S) / c by
          rw [Finset.sum_div]]
    exact (le_div_iff₀ hcpos).mpr (by simpa using hcov)
  · calc
      (∑ S : Set X, g S * pv ^ S.ncard) = (∑ S : Set X, (φ S * pv ^ S.ncard) / c) := by
        apply Finset.sum_congr rfl
        intro S hS
        simp [g, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      _ = (∑ S : Set X, φ S * pv ^ S.ncard) / c := by
        rw [Finset.sum_div]
      _ ≤ (1 / 2 : ℝ) := by
        have hle : (∑ S : Set X, φ S * pv ^ S.ncard) ≤ (1 / 2 : ℝ) * c := by
          simpa [mul_comm] using (le_of_lt hcost)
        calc
          (∑ S : Set X, φ S * pv ^ S.ncard) / c ≤ ((1 / 2 : ℝ) * c) / c :=
            div_le_div_of_nonneg_right hle (le_of_lt hcpos)
          _ = (1 / 2 : ℝ) := by
            field_simp [ne_of_gt hcpos]

/-- Feasibility of the spread-linear-program at value `pv`: a nonneg function with spread at
most `pv^·` and `𝓕`-mass at least `1/2`. -/
noncomputable def tdFeasible (𝓕 : Set (Set X)) (pv : ℝ) : Prop :=
  ∃ ν : Set X → ℝ, (∀ E : Set X, 0 ≤ ν E) ∧
    (∀ T : Set X, tdSpread ν T ≤ pv ^ T.ncard) ∧
    ((1 / 2 : ℝ) ≤ tdMassIn 𝓕 ν)

/-- Norm of a function whose coordinates are bounded by `C`. -/
lemma td_norm_le_of_coord_le (ν : Set X → ℝ) (C : ℝ) (hC : 0 ≤ C) (h : ∀ E : Set X, |ν E| ≤ C) :
    ‖ν‖ ≤ C := by
  rw [Pi.norm_def]
  have hsup : (Finset.univ : Finset (Set X)).sup (fun E : Set X => ‖ν E‖₊) ≤ (⟨C, hC⟩ : ℝ≥0) := by
    apply Finset.sup_le
    intro E hE
    have hE2 : (‖ν E‖₊ : ℝ) ≤ C := by simpa using h E
    exact_mod_cast hE2
  exact_mod_cast hsup

/-- Evaluation at a coordinate is continuous. -/
lemma td_eval_cont (E : Set X) : Continuous (fun ν : Set X → ℝ => ν E) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro y hy
  have hb : |y E - x E| ≤ ‖y - x‖ := by
    have h := norm_le_pi_norm (y - x) E
    simpa [Real.norm_eq_abs] using h
  have hd : ‖y - x‖ < ε := by simpa [dist_eq_norm] using hy
  have : |y E - x E| < ε := lt_of_le_of_lt hb hd
  simpa [Real.norm_eq_abs, dist_eq_norm] using this

/-- `[0,2]^{2^X}` is compact in the sup norm. -/
lemma td_box_compact : IsCompact ({ν : Set X → ℝ | ∀ E, ν E ∈ Set.Icc (0 : ℝ) 2} : Set (Set X → ℝ)) := by
  refine Metric.isCompact_of_isClosed_isBounded ?hc ?hb
  · rw [show {ν : Set X → ℝ | ∀ E, ν E ∈ Set.Icc 0 2} =
        ⋂ E : Set X, {ν : Set X → ℝ | ν E ∈ Set.Icc (0 : ℝ) 2} by ext ν; simp]
    exact isClosed_iInter (fun E => (isClosed_Icc.preimage (td_eval_cont E)))
  · refine Metric.isBounded_iff.mpr ?_
    refine ⟨4, ?_⟩
    intro a ha b hb
    have ha2 : ‖a‖ ≤ 2 := by
      apply td_norm_le_of_coord_le a 2 (by norm_num)
      intro E
      exact abs_le.mpr ⟨le_trans (by norm_num : (-2 : ℝ) ≤ 0) (Set.mem_Icc.mp (ha E)).1, (Set.mem_Icc.mp (ha E)).2⟩
    have hb2 : ‖b‖ ≤ 2 := by
      apply td_norm_le_of_coord_le b 2 (by norm_num)
      intro E
      exact abs_le.mpr ⟨le_trans (by norm_num : (-2 : ℝ) ≤ 0) (Set.mem_Icc.mp (hb E)).1, (Set.mem_Icc.mp (hb E)).2⟩
    calc
      dist a b = ‖a - b‖ := by rw [dist_eq_norm]
      _ ≤ ‖a‖ + ‖b‖ := norm_sub_le a b
      _ ≤ 4 := by linarith


/-- Contrapositive of separation: no feasible vector gives weak `p`-smallness. -/
lemma td_fstEval_cont (T : Set X) : Continuous (fun z : tdE X => z.1 T) := by
  exact (td_eval_cont T).comp continuous_fst

/-- Spreads converge along a convergent sequence of functions. -/
lemma td_seq_limit_spread (w : ℕ → Set X → ℝ) (wstar : Set X → ℝ) (T : Set X)
    (hw : Tendsto w atTop (𝓝 wstar)) :
    Tendsto (fun n : ℕ => tdSpread (w n) T) atTop (𝓝 (tdSpread wstar T)) := by
  classical
  have hcoord : ∀ E : Set X, Tendsto (fun n : ℕ => w n E) atTop (𝓝 (wstar E)) := by
    intro E
    exact ((td_eval_cont E).tendsto wstar).comp hw
  have hconv : Tendsto (fun n : ℕ => ∑ E : Set X, (if T ⊆ E then w n E else 0)) atTop
      (𝓝 (∑ E : Set X, if T ⊆ E then wstar E else 0)) := by
    apply tendsto_finset_sum (s := (Finset.univ : Finset (Set X)))
    intro E hE
    by_cases hTE : T ⊆ E
    · have hc : Tendsto (fun n : ℕ => w n E) atTop (𝓝 (wstar E)) := hcoord E
      simpa [hTE] using hc
    · simpa [hTE]
  simpa [tdSpread] using hconv

/-- Masses converge along a convergent sequence of functions. -/
lemma td_seq_limit_mass (𝓕 : Set (Set X)) (w : ℕ → Set X → ℝ) (wstar : Set X → ℝ)
    (hw : Tendsto w atTop (𝓝 wstar)) :
    Tendsto (fun n : ℕ => tdMassIn 𝓕 (w n)) atTop (𝓝 (tdMassIn 𝓕 wstar)) := by
  classical
  have hcoord : ∀ E : Set X, Tendsto (fun n : ℕ => w n E) atTop (𝓝 (wstar E)) := by
    intro E
    exact ((td_eval_cont E).tendsto wstar).comp hw
  have hconv : Tendsto (fun n : ℕ => ∑ E : Set X, (if E ∈ 𝓕 then w n E else 0)) atTop
      (𝓝 (∑ E : Set X, if E ∈ 𝓕 then wstar E else 0)) := by
    apply tendsto_finset_sum (s := (Finset.univ : Finset (Set X)))
    intro E hE
    by_cases hE𝓕 : E ∈ 𝓕
    · have hc : Tendsto (fun n : ℕ => w n E) atTop (𝓝 (wstar E)) := hcoord E
      simpa [hE𝓕] using hc
    · simpa [hE𝓕]
  simpa [tdMassIn] using hconv

/-- `w₀ ∉ closure cone` unless a feasible vector exists. -/
lemma td_w0_not_mem_closure_of_not_feasible (𝓕 : Set (Set X)) (pv : ℝ) (hpv0 : 0 < pv)
    (h : ¬ tdFeasible 𝓕 pv) : tdW0 pv ∉ closure (tdCone 𝓕) := by
  classical
  intro hWcl
  have happrox : ∀ n : ℕ, ∃ z : tdE X, z ∈ tdCone 𝓕 ∧ dist (tdW0 pv) z < (1 : ℝ) / (n + 1) := by
    intro n
    have hε : 0 < (1 : ℝ) / (n + 1) := by positivity
    simpa using (Metric.mem_closure_iff.mp hWcl ((1 : ℝ) / (n + 1))) hε
  let z : ℕ → tdE X := fun n => Classical.choose (happrox n)
  have hzK : ∀ n : ℕ, z n ∈ tdCone 𝓕 := fun n => (Classical.choose_spec (happrox n)).1
  have hzd : ∀ n : ℕ, dist (tdW0 pv) (z n) < (1 : ℝ) / (n + 1) := fun n =>
    (Classical.choose_spec (happrox n)).2
  have hwit : ∀ n : ℕ, ∃ ν : Set X → ℝ, (∀ E : Set X, 0 ≤ ν E) ∧
      (∀ T : Set X, tdSpread ν T ≤ (z n).1 T) ∧ (-tdMassIn 𝓕 ν ≤ (z n).2) := fun n => hzK n
  let ν : ℕ → Set X → ℝ := fun n => Classical.choose (hwit n)
  have hν0 : ∀ (n : ℕ) (E : Set X), 0 ≤ ν n E := by
    intro n E
    exact (Classical.choose_spec (hwit n)).1 E
  have hνsp : ∀ (n : ℕ) (T : Set X), tdSpread (ν n) T ≤ (z n).1 T := by
    intro n T
    exact (Classical.choose_spec (hwit n)).2.1 T
  have hνm : ∀ n : ℕ, -tdMassIn 𝓕 (ν n) ≤ (z n).2 := by
    intro n
    exact (Classical.choose_spec (hwit n)).2.2
  -- z converges to w₀
  have hdistlim : Tendsto (fun n : ℕ => dist (z n) (tdW0 pv)) atTop (𝓝 (0 : ℝ)) := by
    have hlow : (fun n : ℕ => (0 : ℝ)) ≤ (fun n : ℕ => dist (z n) (tdW0 pv)) := by
      intro n
      exact dist_nonneg
    have hhigh : (fun n : ℕ => dist (z n) (tdW0 pv)) ≤ (fun n : ℕ => (1 : ℝ) / (n + 1)) := by
      intro n
      exact le_of_lt (by simpa [dist_comm] using hzd n)
    have hseq : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 (0 : ℝ)) := by
      have h1 : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
        tendsto_inv_atTop_zero.comp ((tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)))
      simpa using h1
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds : Tendsto (fun n : ℕ => (0 : ℝ)) atTop (𝓝 (0 : ℝ))) hseq hlow hhigh
  have hztend : Tendsto z atTop (𝓝 (tdW0 pv)) := by
    exact (tendsto_iff_dist_tendsto_zero (f := z) (x := atTop) (a := tdW0 pv)).2 hdistlim
  -- witnesses eventually land in the box
  have hw0e : Tendsto (fun n : ℕ => (z n).1 (∅ : Set X)) atTop (𝓝 ((tdW0 pv).1 (∅ : Set X))) := by
    exact ((td_fstEval_cont (∅ : Set X)).tendsto (tdW0 pv)).comp hztend
  have hw0e2 : Tendsto (fun n : ℕ => (z n).1 (∅ : Set X)) atTop (𝓝 (1 : ℝ)) := by
    simpa [tdW0] using hw0e
  have hw0e_lt : ∀ᶠ n in atTop, (z n).1 (∅ : Set X) < 2 := by
    have hmem : {x : ℝ | x < 2} ∈ 𝓝 (1 : ℝ) := isOpen_Iio.mem_nhds (by norm_num)
    exact hw0e2.eventually hmem
  have hw0e_lt' : ∀ᶠ n in atTop, (z n).1 (∅ : Set X) < 2 := hw0e_lt
  let B : Set (Set X → ℝ) := {w : Set X → ℝ | ∀ E : Set X, w E ∈ Set.Icc (0 : ℝ) 2}
  let y : ℕ → Set X → ℝ := fun n => ν (n + 1)
  have hylim_box : ∀ᶠ n in atTop, y n ∈ B := by
    rw [eventually_atTop]
    rcases (eventually_atTop.1 hw0e_lt) with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    dsimp [B, y]
    intro E
    have hzn : (z (n + 1)).1 (∅ : Set X) < 2 := hN (n + 1) (by omega)
    have hνE : ν (n + 1) E ≤ tdSpread (ν (n + 1)) (∅ : Set X) := by
      rw [tdSpread_eq_filter]
      have hmem : E ∈ (Finset.univ : Finset (Set X)).filter (fun E0 : Set X => (∅ : Set X) ⊆ E0) := by
        simp
      exact Finset.single_le_sum (fun E0 hE0 => hν0 (n + 1) E0) hmem
    have hsp : tdSpread (ν (n + 1)) (∅ : Set X) ≤ (z (n + 1)).1 (∅ : Set X) :=
      hνsp (n + 1) ∅
    constructor
    · exact hν0 (n + 1) E
    · have hle : ν (n + 1) E ≤ (z (n + 1)).1 (∅ : Set X) := le_trans hνE hsp
      linarith
  have hfreq : ∃ᶠ n in atTop, y n ∈ B := by
    exact hylim_box.frequently
  obtain ⟨wstar, hwstarB, φ, hφmono, hφlim⟩ := td_box_compact.tendsto_subseq' hfreq
  have hy0 : ∀ E : Set X, 0 ≤ wstar E := by
    intro E
    exact (Set.mem_Icc.mp (hwstarB E)).1
  have hφplus : Tendsto (fun n : ℕ => (φ n : ℕ) + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hφmono.tendsto_atTop
  have hzφ : Tendsto (fun n : ℕ => z (φ n + 1)) atTop (𝓝 (tdW0 pv)) := hztend.comp hφplus
  have hspread_le : ∀ T : Set X, tdSpread wstar T ≤ pv ^ T.ncard := by
    intro T
    have hf : Tendsto (fun n : ℕ => tdSpread (y (φ n)) T) atTop (𝓝 (tdSpread wstar T)) :=
      td_seq_limit_spread (fun n : ℕ => y (φ n)) wstar T hφlim
    have hg : Tendsto (fun n : ℕ => (z (φ n + 1)).1 T) atTop (𝓝 (pv ^ T.ncard)) := by
      have hc : Tendsto (fun n : ℕ => (z (φ n + 1)).1 T) atTop
          (𝓝 ((tdW0 pv).1 T)) := ((td_fstEval_cont T).tendsto (tdW0 pv)).comp hzφ
      simpa [tdW0] using hc
    have hevent : (fun n : ℕ => tdSpread (y (φ n)) T) ≤ᶠ[atTop]
        (fun n : ℕ => (z (φ n + 1)).1 T) := by
      exact Eventually.of_forall (fun n => by
        simpa [y] using hνsp (φ n + 1) T)
    exact le_of_tendsto_of_tendsto hf hg hevent
  have hmlower : ∀ n : ℕ, -(z (φ n + 1)).2 ≤ tdMassIn 𝓕 (y (φ n)) := by
    intro n
    have h1 : -tdMassIn 𝓕 (y (φ n)) ≤ (z (φ n + 1)).2 := by
      simpa [y] using hνm (φ n + 1)
    linarith
  have hmass_ge : (1 / 2 : ℝ) ≤ tdMassIn 𝓕 wstar := by
    have hf : Tendsto (fun n : ℕ => -(z (φ n + 1)).2) atTop (𝓝 (1 / 2 : ℝ)) := by
      have hsnd : Tendsto (fun n : ℕ => (z (φ n + 1)).2) atTop
          (𝓝 ((tdW0 pv).2)) := (continuous_snd.tendsto (tdW0 pv)).comp hzφ
      have hneg : Tendsto (fun n : ℕ => -(z (φ n + 1)).2) atTop (𝓝 (-(tdW0 pv).2)) := hsnd.neg
      simpa [tdW0] using hneg
    have hg : Tendsto (fun n : ℕ => tdMassIn 𝓕 (y (φ n))) atTop (𝓝 (tdMassIn 𝓕 wstar)) :=
      td_seq_limit_mass 𝓕 (fun n : ℕ => y (φ n)) wstar hφlim
    have hevent : (fun n : ℕ => -(z (φ n + 1)).2) ≤ᶠ[atTop]
        (fun n : ℕ => tdMassIn 𝓕 (y (φ n))) := by
      exact Eventually.of_forall hmlower
    exact le_of_tendsto_of_tendsto hf hg hevent
  exact h ⟨wstar, hy0, hspread_le, hmass_ge⟩

lemma td_farkas (𝓕 : Set (Set X)) (pv : ℝ) (hpv0 : 0 < pv) (hpv1 : pv ≤ 1)
    (h : ¬ tdFeasible 𝓕 pv) : IsWeaklySmall (⟨pv, le_of_lt hpv0, hpv1⟩ : I) 𝓕 := by
  classical
  have hW : tdW0 pv ∉ closure (tdCone 𝓕) := td_w0_not_mem_closure_of_not_feasible 𝓕 pv hpv0 h
  rcases td_sep_core 𝓕 pv hpv0 hW with ⟨g, hg0, hcover, hcost⟩
  let g' : Set X → ℝ≥0 := fun S => ⟨g S, hg0 S⟩
  refine ⟨g', ?_, ?_⟩
  · intro E hE
    have hfilter : (1 : ℝ) ≤
        (∑ S ∈ (Finset.univ : Finset (Set X)).filter (fun S => S ⊆ E), (g' S : ℝ)) := by
      calc
        (1 : ℝ) ≤ (∑ S : Set X, if S ⊆ E then g S else 0) := hcover E hE
        _ = (∑ S : Set X, if S ⊆ E then (g' S : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro S hS
          by_cases hS2 : S ⊆ E
          · rw [if_pos hS2, if_pos hS2]
            rfl
          · rw [if_neg hS2, if_neg hS2]
        _ = (∑ S ∈ (Finset.univ : Finset (Set X)).filter (fun S => S ⊆ E), (g' S : ℝ)) := by
          rw [← Finset.sum_filter]
    have hcast : (1 : ℝ≥0) ≤
        (∑ S ∈ (Finset.univ : Finset (Set X)).filter (fun S => S ⊆ E), g' S) := by
      exact_mod_cast hfilter
    simpa using hcast
  · have hc2 : (∑ S : Set X, (g' S : ℝ) * pv ^ S.ncard) ≤ (1 / 2 : ℝ) := by
      have hEq : (∑ S : Set X, (g' S : ℝ) * pv ^ S.ncard) =
          (∑ S : Set X, g S * pv ^ S.ncard) := by
        apply Finset.sum_congr rfl
        intro S hS
        change (g S : ℝ) * pv ^ S.ncard = g S * pv ^ S.ncard
        rfl
      rw [hEq]
      exact hcost
    simpa using hc2

/-- No feasible vector with the given parameters is what we use contrapositively. -/
lemma td_feasible_of_not_weak (𝓕 : Set (Set X)) (p : I) (hp0 : 0 < (p : ℝ))
    (hnot : ¬ IsWeaklySmall p 𝓕) : tdFeasible 𝓕 (p : ℝ) := by
  classical
  by_contra hf
  exact hnot (td_farkas 𝓕 (p : ℝ) hp0 p.2.2 hf)

/-- If 𝓕 is not weakly `p`-small, then it supports a probability measure concentrated on 𝓕
which is `(2p)`-spread. -/
lemma td_spread_measure_of_not_weak (𝓕 : Set (Set X)) (p : I) (hp0 : 0 < (p : ℝ))
    (hnot : ¬ IsWeaklySmall p 𝓕) :
    ∃ ν : Set X → ℝ, (∀ E : Set X, 0 ≤ ν E) ∧
      (∀ E : Set X, ν E ≠ 0 → E ∈ 𝓕) ∧ (∑ E : Set X, ν E) = 1 ∧
      (∀ T : Set X, tdSpread ν T ≤ 2 * (p : ℝ) ^ T.ncard) := by
  classical
  rcases td_feasible_of_not_weak 𝓕 p hp0 hnot with ⟨ν, hν0, hνspread, hνmass⟩
  let ν0 : Set X → ℝ := fun E => if E ∈ 𝓕 then ν E else 0
  let M : ℝ := ∑ E : Set X, ν0 E
  have hMge : (1 / 2 : ℝ) ≤ M := by
    dsimp [M, ν0]
    rw [tdSum_restrict]
    exact hνmass
  have hMpos : 0 < M := by linarith
  let μ : Set X → ℝ := fun E => ν0 E / M
  refine ⟨μ, ?_, ?_, ?_, ?_⟩
  · intro E
    by_cases hE𝓕 : E ∈ 𝓕
    · dsimp [μ, ν0]
      simp [hE𝓕]
      exact div_nonneg (hν0 E) (le_of_lt hMpos)
    · dsimp [μ, ν0]
      simp [hE𝓕]
  · intro E hEμ
    by_contra hEnot
    have hμ0 : μ E = 0 := by
      dsimp [μ, ν0]
      simp [hEnot]
    exact hEμ hμ0
  · -- total mass is 1
    calc
      (∑ E : Set X, μ E) = (∑ E : Set X, ν0 E) / M := by
        rw [Finset.sum_div]
      _ = 1 := by
        have hz : (∑ E : Set X, ν0 E) ≠ 0 := by
          dsimp [M] at hMpos
          exact ne_of_gt hMpos
        exact div_self hz
  · -- spread bound
    intro T
    have hT0 : 0 ≤ (p : ℝ) ^ T.ncard := pow_nonneg (le_of_lt hp0) _
    have hsp_restrict : tdSpread ν0 T ≤ tdSpread ν T := tdSpread_restrict_le hν0 𝓕 T
    have hMle : (1 / M : ℝ) ≤ 2 := by
      -- from 1/2 ≤ M
      have htwo : (1 : ℝ) / M ≤ 2 := by
        exact (div_le_iff₀ hMpos).mpr (by nlinarith [hMge])
      simpa [one_div] using htwo
    calc
      tdSpread μ T = tdSpread ν0 T / M := by
        rw [tdSpread_eq_filter, tdSpread_eq_filter]
        rw [Finset.sum_div]
      _ ≤ tdSpread ν T / M := div_le_div_of_nonneg_right hsp_restrict (le_of_lt hMpos)
      _ ≤ (p : ℝ) ^ T.ncard / M := div_le_div_of_nonneg_right (hνspread T) (le_of_lt hMpos)
      _ = (p : ℝ) ^ T.ncard * (1 / M) := by ring
      _ ≤ (p : ℝ) ^ T.ncard * 2 := mul_le_mul_of_nonneg_left hMle hT0
      _ = 2 * (p : ℝ) ^ T.ncard := by ring

/-- Choose a minimal element of `𝓕` below `E` (or `∅` if `E ∉ 𝓕`). -/
noncomputable def tdPickMin (𝓕 : Set (Set X)) : Set X → Set X :=
  fun E => if hE : E ∈ 𝓕 then Classical.choose (exists_minimal_subset hE) else ∅

lemma tdPickMin_subset (𝓕 : Set (Set X)) (E : Set X) : tdPickMin 𝓕 E ⊆ E := by
  classical
  unfold tdPickMin
  by_cases hE : E ∈ 𝓕
  · rw [dif_pos hE]
    exact (Classical.choose_spec (exists_minimal_subset hE)).2.1
  · rw [dif_neg hE]
    intro x hx
    simp at hx

lemma tdPickMin_minimal (𝓕 : Set (Set X)) {E : Set X} (hE : E ∈ 𝓕) :
    IsMinimalElem 𝓕 (tdPickMin 𝓕 E) := by
  classical
  unfold tdPickMin
  rw [dif_pos hE]
  exact (Classical.choose_spec (exists_minimal_subset hE)).elim
    (fun hF _ => ⟨hF, (Classical.choose_spec (exists_minimal_subset hE)).2.2⟩)

/-- Moving mass down to minimal elements: total mass and nonnegativity preserved, shadow sums
do not increase. -/
lemma td_push_minimal (𝓕 : Set (Set X)) {ν : Set X → ℝ} (hν0 : ∀ E : Set X, 0 ≤ ν E)
    (hsupp : ∀ E : Set X, ν E ≠ 0 → E ∈ 𝓕) :
    ∃ νm : Set X → ℝ,
      (∀ E : Set X, 0 ≤ νm E) ∧ (∀ E : Set X, νm E ≠ 0 → IsMinimalElem 𝓕 E) ∧
      ((∑ E : Set X, νm E) = ∑ E : Set X, ν E) ∧
      (∀ T : Set X, tdSpread νm T ≤ tdSpread ν T) := by
  classical
  let νm : Set X → ℝ := fun M => ∑ E : Set X, if tdPickMin 𝓕 E = M then ν E else 0
  refine ⟨νm, ?_, ?_, ?_, ?_⟩
  · intro M
    dsimp [νm]
    exact Finset.sum_nonneg (fun E hE => by
      by_cases h : tdPickMin 𝓕 E = M
      · simp [h, hν0 E]
      · simp [h])
  · -- support
    intro M hM
    have hget : ∃ E : Set X, tdPickMin 𝓕 E = M ∧ ν E ≠ 0 := by
      by_contra hnone
      apply hM
      dsimp [νm]
      apply Finset.sum_eq_zero
      intro E hE
      by_cases h : tdPickMin 𝓕 E = M
      · by_cases hν : ν E = 0
        · simp [h, hν]
        · exfalso
          exact hnone ⟨E, h, hν⟩
      · simp [h]
    rcases hget with ⟨E, hpick, hνE⟩
    have hE𝓕 : E ∈ 𝓕 := hsupp E hνE
    have hmin : IsMinimalElem 𝓕 (tdPickMin 𝓕 E) := tdPickMin_minimal (𝓕 := 𝓕) hE𝓕
    simpa [hpick] using hmin
  · -- total mass preserved
    calc
      (∑ M : Set X, νm M) = (∑ M : Set X, ∑ E : Set X, if tdPickMin 𝓕 E = M then ν E else 0) := by
        rfl
      _ = (∑ E : Set X, ∑ M : Set X, if tdPickMin 𝓕 E = M then ν E else 0) := by
        rw [Finset.sum_comm]
      _ = (∑ E : Set X, ν E) := by
        apply Finset.sum_congr rfl
        intro E hE
        simp
  · -- shadow sum only decreases
    intro T
    calc
      tdSpread νm T = (∑ M : Set X, if T ⊆ M then νm M else 0) := by
        rfl
      _ = (∑ M : Set X, ∑ E : Set X,
            if T ⊆ M then (if tdPickMin 𝓕 E = M then ν E else 0) else 0) := by
        apply Finset.sum_congr rfl
        intro M hM
        by_cases hTM : T ⊆ M
        · simp [hTM, νm]
        · simp [hTM, νm]
      _ = (∑ E : Set X, ∑ M : Set X,
            if T ⊆ M then (if tdPickMin 𝓕 E = M then ν E else 0) else 0) := by
        rw [Finset.sum_comm]
      _ = (∑ E : Set X, if T ⊆ tdPickMin 𝓕 E then ν E else 0) := by
        apply Finset.sum_congr rfl
        intro E hE
        by_cases hEν : ν E = 0
        · -- the inner sum vanishes
          have hsum0 : (∑ M : Set X,
              if T ⊆ M then (if tdPickMin 𝓕 E = M then ν E else 0) else 0) = 0 := by
            apply Finset.sum_eq_zero
            intro M hM
            simp [hEν]
          rw [hsum0]
          simp [hEν]
        · by_cases hT : T ⊆ tdPickMin 𝓕 E
          · have hsum : (∑ M : Set X,
                if T ⊆ M then (if tdPickMin 𝓕 E = M then ν E else 0) else 0) = ν E := by
              calc
                (∑ M : Set X, if T ⊆ M then (if tdPickMin 𝓕 E = M then ν E else 0) else 0)
                    = (∑ M : Set X, if tdPickMin 𝓕 E = M then ν E else 0) := by
                        apply Finset.sum_congr rfl
                        intro M hM
                        by_cases hMp : tdPickMin 𝓕 E = M
                        · have hTM' : T ⊆ M := hMp ▸ hT
                          simp [hTM']
                        · simp [hMp]
                _ = ν E := by simp
            rw [hsum]
            simp [hT]
          · have hsum0 : (∑ M : Set X,
                if T ⊆ M then (if tdPickMin 𝓕 E = M then ν E else 0) else 0) = 0 := by
              apply Finset.sum_eq_zero
              intro M hM
              by_cases hMp : tdPickMin 𝓕 E = M
              · have hnotTM : ¬ T ⊆ M := by
                  intro hTM'
                  exact hT (by simpa [hMp] using hTM')
                simp [hMp, hnotTM]
              · simp [hMp]
            rw [hsum0]
            simp [hT]
      _ ≤ (∑ E : Set X, if T ⊆ E then ν E else 0) := by
        apply Finset.sum_le_sum
        intro E hE
        by_cases hEν : ν E = 0
        · simp [hEν]
        · have hE0 : 0 ≤ ν E := hν0 E
          have hpick : tdPickMin 𝓕 E ⊆ E := tdPickMin_subset 𝓕 E
          by_cases hTp : T ⊆ tdPickMin 𝓕 E
          · have hTE : T ⊆ E := subset_trans hTp hpick
            simp [hTp, hTE]
          · by_cases hTE : T ⊆ E
            · simp [hTp, hTE, hE0]
            · simp [hTp, hTE]

/-- Continuity of the total-mass functional. -/
lemma td_sum_cont : Continuous (fun ν : Set X → ℝ => ∑ E : Set X, ν E) := by
  classical
  exact continuous_finset_sum (Finset.univ : Finset (Set X)) (fun E hE => td_eval_cont E)

/-- Continuity of the spread functional. -/
lemma td_spread_cont (T : Set X) : Continuous (fun ν : Set X → ℝ => tdSpread ν T) := by
  classical
  -- tdSpread ν T = ∑ E, if T ⊆ E then ν E else 0
  have hcont : Continuous (fun ν : Set X → ℝ =>
      ∑ E : Set X, (if T ⊆ E then ν E else 0)) := by
    refine continuous_finset_sum (Finset.univ : Finset (Set X)) (fun E hE => ?_)
    by_cases hTE : T ⊆ E
    · simpa [hTE] using td_eval_cont E
    · simpa [hTE] using (continuous_const : Continuous fun ν : Set X → ℝ => (0 : ℝ))
  simpa [tdSpread] using hcont

/-- The probability simplex on subsets is compact. -/
lemma td_simplex_compact : IsCompact ({ν : Set X → ℝ | (∀ E : Set X, 0 ≤ ν E) ∧
    (∑ E : Set X, ν E) = 1} : Set (Set X → ℝ)) := by
  refine Metric.isCompact_of_isClosed_isBounded ?hc ?hb
  · -- closed
    rw [show {ν : Set X → ℝ | (∀ E : Set X, 0 ≤ ν E) ∧ (∑ E : Set X, ν E) = 1} =
        (⋂ E : Set X, {ν : Set X → ℝ | 0 ≤ ν E}) ∩ {ν : Set X → ℝ | (∑ E : Set X, ν E) = 1} by
          ext ν; simp [and_assoc]]
    exact (isClosed_iInter (fun E => (isClosed_Ici.preimage (td_eval_cont E)))).inter
      (isClosed_singleton.preimage td_sum_cont)
  · -- bounded
    refine Metric.isBounded_iff.mpr ?_
    refine ⟨2, ?_⟩
    intro a ha b hb
    have ha1 : ‖a‖ ≤ 1 := by
      apply td_norm_le_of_coord_le a 1 (by norm_num)
      intro E
      have haE : 0 ≤ a E := ha.1 E
      have hsum : a E ≤ ∑ E0 : Set X, a E0 := by
        exact Finset.single_le_sum (fun E0 hE0 => ha.1 E0) (Finset.mem_univ E)
      have hb1 : (∑ E0 : Set X, a E0) = 1 := ha.2
      have hle : a E ≤ 1 := by
        rw [hb1] at hsum
        exact hsum
      exact le_trans (le_of_eq (abs_of_nonneg haE)) hle
    have hbb1 : ‖b‖ ≤ 1 := by
      apply td_norm_le_of_coord_le b 1 (by norm_num)
      intro E
      have hbE : 0 ≤ b E := hb.1 E
      have hsum : b E ≤ ∑ E0 : Set X, b E0 := by
        exact Finset.single_le_sum (fun E0 hE0 => hb.1 E0) (Finset.mem_univ E)
      have hbb : (∑ E0 : Set X, b E0) = 1 := hb.2
      have hle : b E ≤ 1 := by
        rw [hbb] at hsum
        exact hsum
      exact le_trans (le_of_eq (abs_of_nonneg hbE)) hle
    calc
      dist a b = ‖a - b‖ := by rw [dist_eq_norm]
      _ ≤ ‖a‖ + ‖b‖ := norm_sub_le a b
      _ ≤ 2 := by linarith

/-- Existence of a probability measure on `𝓕` which is `(2q)`-spread. -/
lemma td_exists_on_F (𝓕 : Set (Set X)) (hFne : (𝓕 : Set (Set X)).Nonempty)
    (q : ℝ) (hq0 : 0 < q) (hq : (q_f 𝓕 : ℝ) ≤ q) :
    ∃ ν : Set X → ℝ, (∀ E : Set X, 0 ≤ ν E) ∧
      (∀ E : Set X, ν E ≠ 0 → E ∈ 𝓕) ∧ (∑ E : Set X, ν E) = 1 ∧
      (∀ T : Set X, tdSpread ν T ≤ (2 * q) ^ T.ncard) := by
  classical
  by_cases h12 : (1 / 2 : ℝ) ≤ q
  · -- 2q ≥ 1: a point mass works
    rcases hFne with ⟨T0, hT0⟩
    rcases exists_minimal_subset hT0 with ⟨M, hM𝓕, hMT0, hMmin⟩
    let ν : Set X → ℝ := fun E => if E = M then 1 else 0
    refine ⟨ν, ?_, ?_, ?_, ?_⟩
    · intro E; by_cases h : E = M <;> simp [ν, h]
    · intro E hE
      have : E = M := by
        by_contra h
        simp [ν, h] at hE
      simpa [this] using hM𝓕
    · calc
        (∑ E : Set X, ν E) = (∑ E : Set X, if E = M then 1 else 0) := by rfl
        _ = 1 := by simp
    · intro T
      have hq2 : 1 ≤ 2 * q := by linarith
      have hle1 : 1 ≤ (2 * q) ^ T.ncard := by
        exact one_le_pow₀ hq2
      have hsp : tdSpread ν T ≤ 1 := by
        rw [tdSpread_eq_filter]
        by_cases hMf : M ∈ (Finset.univ : Finset (Set X)).filter (fun E : Set X => T ⊆ E)
        · calc
            (∑ E ∈ (Finset.univ : Finset (Set X)).filter (fun E : Set X => T ⊆ E), ν E) = 1 := by
              calc
                (∑ E ∈ (Finset.univ : Finset (Set X)).filter (fun E : Set X => T ⊆ E), ν E)
                    = (∑ E ∈ (Finset.univ : Finset (Set X)).filter (fun E : Set X => T ⊆ E), if E = M then 1 else 0) := by
                        apply Finset.sum_congr rfl
                        intro E hE
                        by_cases h : E = M <;> simp [ν, h]
                _ = 1 := by
                  simp [Finset.sum_ite_eq, hMf]
          _ ≤ 1 := le_rfl
        · calc
            (∑ E ∈ (Finset.univ : Finset (Set X)).filter (fun E : Set X => T ⊆ E), ν E) = 0 := by
              apply Finset.sum_eq_zero
              intro E hE
              by_cases h : E = M
              · exfalso
                exact hMf (by simpa [h] using hE)
              · simp [ν, h]
          _ ≤ 1 := by norm_num
      exact le_trans hsp hle1
  · -- q < 1/2 : approximation
    have hq12 : q < 1 / 2 := by linarith
    have h2q1 : 2 * q < 1 := by linarith
    let pk : ℕ → ℝ := fun k => q * (1 + ((k + 1 : ℕ) : ℝ)⁻¹)
    have hpkpos : ∀ k : ℕ, 0 < pk k := by
      intro k
      dsimp [pk]
      positivity
    have hpkgt : ∀ k : ℕ, q < pk k := by
      intro k
      dsimp [pk]
      have hpos : 0 < ((k + 1 : ℕ) : ℝ)⁻¹ := by positivity
      nlinarith
    have hpklt1 : ∀ k : ℕ, pk k < 1 := by
      intro k
      dsimp [pk]
      have hfrac : ((k + 1 : ℕ) : ℝ)⁻¹ ≤ 1 := by
        have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k + 1)
        have hk0 : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
        exact (inv_le_one₀ hk0).2 hk
      nlinarith
    have hpkdec : ∀ {k j : ℕ}, k ≤ j → pk j ≤ pk k := by
      intro k j hkj
      dsimp [pk]
      have hdiv : ((j + 1 : ℕ) : ℝ)⁻¹ ≤ ((k + 1 : ℕ) : ℝ)⁻¹ := by
        have hle : ((k + 1 : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
          exact_mod_cast (by omega : k + 1 ≤ j + 1)
        have hposj : 0 < ((j + 1 : ℕ) : ℝ) := by positivity
        have hposk : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
        exact (inv_le_inv₀ hposj hposk).2 hle
      nlinarith
    have hpklim : Tendsto pk atTop (𝓝 q) := by
      have h0 : Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
        tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
      have h1 : Tendsto (fun k : ℕ => (1 : ℝ) + ((k + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 (1 : ℝ)) := by
        simpa using h0.const_add (1 : ℝ)
      have h2 : Tendsto (fun k : ℕ => q * (1 + ((k + 1 : ℕ) : ℝ)⁻¹)) atTop (𝓝 (q * 1)) :=
        h1.const_mul q
      simpa [pk] using h2
    let pI : ℕ → I := fun k => ⟨pk k, le_of_lt (hpkpos k), le_of_lt (hpklt1 k)⟩
    have hnotw : ∀ k : ℕ, ¬ IsWeaklySmall (pI k) 𝓕 := by
      intro k
      exact not_weakly_small_of_qf_lt 𝓕 (pI k) (by dsimp [pI]; linarith [hq, hpkgt k])
    have hmeas : ∀ k : ℕ, ∃ ν : Set X → ℝ, (∀ E : Set X, 0 ≤ ν E) ∧
        (∀ E : Set X, ν E ≠ 0 → E ∈ 𝓕) ∧ (∑ E : Set X, ν E) = 1 ∧
        (∀ T : Set X, tdSpread ν T ≤ 2 * (pk k) ^ T.ncard) := by
      intro k
      rcases td_spread_measure_of_not_weak 𝓕 (pI k) (hpkpos k) (hnotw k) with ⟨ν, h0, h1, h2, h3⟩
      refine ⟨ν, h0, h1, h2, ?_⟩
      intro T
      simpa [pI] using h3 T
    let mu : ℕ → Set X → ℝ := fun k => Classical.choose (hmeas k)
    have hmu0 : ∀ (k : ℕ) (E : Set X), 0 ≤ mu k E := by
      intro k E
      exact (Classical.choose_spec (hmeas k)).1 E
    have hmusup : ∀ (k : ℕ) (E : Set X), mu k E ≠ 0 → E ∈ 𝓕 := by
      intro k E
      exact (Classical.choose_spec (hmeas k)).2.1 E
    have hmusum : ∀ k : ℕ, (∑ E : Set X, mu k E) = 1 := by
      intro k
      exact (Classical.choose_spec (hmeas k)).2.2.1
    have hmusp : ∀ (k : ℕ) (T : Set X), tdSpread (mu k) T ≤ 2 * (pk k) ^ T.ncard := by
      intro k T
      exact (Classical.choose_spec (hmeas k)).2.2.2 T
    let S : Set (Set X → ℝ) := {ν : Set X → ℝ | (∀ E : Set X, 0 ≤ ν E) ∧ (∑ E : Set X, ν E) = 1}
    have hmuS : ∀ k : ℕ, mu k ∈ S := by
      intro k
      dsimp [S]
      exact ⟨hmu0 k, hmusum k⟩
    obtain ⟨ν, hνS, φ, hφmono, hφlim⟩ := td_simplex_compact.tendsto_subseq hmuS
    have hν0 : ∀ E : Set X, 0 ≤ ν E := fun E => (hνS.1 E)
    have hνsum : (∑ E : Set X, ν E) = 1 := hνS.2
    have hνsup : ∀ E : Set X, ν E ≠ 0 → E ∈ 𝓕 := by
      intro E hE
      by_contra hnot
      have hzero : ∀ k : ℕ, mu k E = 0 := by
        intro k
        by_contra hne
        exact hnot (hmusup k E hne)
      -- limit: ν E = 0
      have hlim : Tendsto (fun j : ℕ => mu (φ j) E) atTop (𝓝 (ν E)) :=
        ((td_eval_cont E).tendsto ν).comp hφlim
      have hcon0 : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (0 : ℝ)) := tendsto_const_nhds
      have heq : (fun j : ℕ => mu (φ j) E) =ᶠ[atTop] (fun _ : ℕ => (0 : ℝ)) :=
        Eventually.of_forall (fun j => hzero (φ j))
      have hcon : Tendsto (fun j : ℕ => mu (φ j) E) atTop (𝓝 (0 : ℝ)) :=
        hcon0.congr' heq.symm
      have hEq : ν E = 0 := tendsto_nhds_unique hlim hcon
      exact hE (by simpa [hEq])
    have hφlim' : Tendsto (fun j : ℕ => mu (φ j)) atTop (𝓝 ν) := hφlim
    have hspread_all : ∀ (T : Set X) (k : ℕ), tdSpread ν T ≤ 2 * (pk k) ^ T.ncard := by
      intro T k
      have hf : Tendsto (fun j : ℕ => tdSpread (mu (φ j)) T) atTop (𝓝 (tdSpread ν T)) :=
        td_seq_limit_spread (fun j : ℕ => mu (φ j)) ν T hφlim'
      have hg : Tendsto (fun j : ℕ => (2 : ℝ) * (pk k) ^ T.ncard) atTop
          (𝓝 ((2 : ℝ) * (pk k) ^ T.ncard)) := by
            exact tendsto_const_nhds
      have hevent : (fun j : ℕ => tdSpread (mu (φ j)) T) ≤ᶠ[atTop]
          (fun j : ℕ => (2 : ℝ) * (pk k) ^ T.ncard) := by
        exact (eventually_ge_atTop k).mono (fun j hj => by
          have hφj : k ≤ φ j := by
            have hm : j ≤ φ j := hφmono.id_le j
            omega
          have hbound : tdSpread (mu (φ j)) T ≤ 2 * (pk (φ j)) ^ T.ncard := hmusp (φ j) T
          have hdec : pk (φ j) ≤ pk k := hpkdec hφj
          have hpwk : 0 ≤ pk k ^ T.ncard := pow_nonneg (le_of_lt (hpkpos k)) _
          have hpow : (pk (φ j)) ^ T.ncard ≤ (pk k) ^ T.ncard :=
            pow_le_pow_left₀ (le_of_lt (hpkpos (φ j))) hdec _
          nlinarith)
      exact le_of_tendsto_of_tendsto hf hg hevent
    have h2q : ∀ T : Set X, tdSpread ν T ≤ 2 * q ^ T.ncard := by
      intro T
      have hf : Tendsto (fun _ : ℕ => tdSpread ν T) atTop (𝓝 (tdSpread ν T)) := by
            exact tendsto_const_nhds
      have hg : Tendsto (fun k : ℕ => 2 * (pk k) ^ T.ncard) atTop (𝓝 (2 * q ^ T.ncard)) := by
        have hpow : Tendsto (fun k : ℕ => (pk k) ^ T.ncard) atTop (𝓝 (q ^ T.ncard)) :=
          (continuous_pow T.ncard).tendsto q |>.comp hpklim
        exact hpow.const_mul 2
      have hevent : (fun _ : ℕ => tdSpread ν T) ≤ᶠ[atTop]
          (fun k : ℕ => 2 * (pk k) ^ T.ncard) := by
        exact Eventually.of_forall (fun k => hspread_all T k)
      exact le_of_tendsto_of_tendsto hf hg hevent
    refine ⟨ν, hν0, hνsup, hνsum, ?_⟩
    intro T
    by_cases hT0 : T = ∅
    · have hsp : tdSpread ν T = 1 := by
        rw [hT0]
        rw [tdSpread_eq_filter]
        have hf : (Finset.univ : Finset (Set X)).filter (fun E : Set X => (∅ : Set X) ⊆ E) =
            Finset.univ := by
          ext E; simp
        rw [hf]
        exact hνsum
      rw [hT0]
      simp
      simpa [hT0] using hsp.le
    · -- T ≠ ∅
      have ht : (1 : ℕ) ≤ T.ncard := by
        have hTne : T ≠ (∅ : Set X) := hT0
        have hpos : 0 < T.ncard := by
          have hf := Set.ncard_pos (s := T)
          exact hf.2 (Set.nonempty_iff_ne_empty.mpr hTne)
        omega
      have hqT : 0 ≤ q ^ T.ncard := pow_nonneg (le_of_lt hq0) _
      have hb : 2 * q ^ T.ncard ≤ (2 * q) ^ T.ncard := by
        have h2le : (2 : ℝ) ≤ (2 : ℝ) ^ T.ncard := by
          have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ (2 : ℝ)) ht
          simpa using hpow
        calc
          2 * q ^ T.ncard ≤ (2 : ℝ) ^ T.ncard * q ^ T.ncard :=
            mul_le_mul_of_nonneg_right h2le hqT
          _ = (2 * q) ^ T.ncard := by rw [mul_pow]
      exact le_trans (h2q T) hb

/-- Duality: `q_f(𝓕) ≤ q` yields a `(2q)`-spread probability measure on minimal elements. -/
theorem talagrand_dual {𝓕 : Set (Set X)} (h𝓕 : IsUpperSet 𝓕) (hl : 2 ≤ l 𝓕)
    (q : ℝ) (hq0 : 0 < q) (hq : (q_f 𝓕 : ℝ) ≤ q) :
    ∃ ν : Set X → ℝ,
      (∀ S : Set X, 0 ≤ ν S) ∧
      (∑ S : Set X, ν S) = 1 ∧
      (∀ S : Set X, ν S ≠ 0 → IsMinimalElem 𝓕 S) ∧
      (∀ T : Set X, (∑ E : Set X, if T ⊆ E then ν E else 0) ≤ (2 * q) ^ T.ncard) := by
  classical
  have hFne : (𝓕 : Set (Set X)).Nonempty := nonempty_of_two_le_l 𝓕 hl
  rcases td_exists_on_F 𝓕 hFne q hq0 hq with ⟨ν, hν0, hνsup, hνsum, hνspread⟩
  rcases td_push_minimal 𝓕 hν0 hνsup with ⟨νm, hm0, hmmin, hmsum, hmspread⟩
  refine ⟨νm, hm0, ?_, hmmin, ?_⟩
  · rw [hmsum]
    exact hνsum
  · intro T
    exact le_trans (hmspread T) (hνspread T)
