import Mathlib
import Submission.Work.C17y.gen_van
import Submission.Work.C17y.gen_stab
import Submission.Work.C17y.dstable_const
import Submission.Work.GenShared.adjoint_eq_sum

/-!
# The generic period-independence theorem

`periods_indep_gen` :  for an order-two operator `p₂ y'' + p₁ y' + p₀ y` whose Riccati equation has
no rational solution (`hric`) and whose adjoint has no rational solution with right-hand side in the
span of the `rᵢ` (`hadj`), the functions `y₁, y₁', J₀, …, J_{k-1}` (with `Jᵢ' = rᵢ y₁`) are linearly
independent over `ℂ[x]` on the ball:  every relation
`A y₁ + B y₁' + Σ Cᵢ Jᵢ = 0` with polynomial coefficients is trivial.

The proof is the differential-module argument:  the coefficient tuples `n` for which the relation
function vanishes off a finite set form a `K`-submodule `Nsub` (`K = ℂ(x)`), stable under the
connection `Dv`.  Then

* `Nsub ⊓ Msub = ⊥` (`Msub` = tuples with vanishing integral block):  a nontrivial element of
  `Nsub ⊓ Msub` is a pair `(a,b)` with `a y₁ + b y₁' = 0`; differentiating once and applying Cramer
  either forces `y₁ ≡ 0` or produces a rational solution `-a/b` of the Riccati equation of `p₂`,
  contradicting `hric`;
* `V := proj3 '' Nsub` is a `dRat`-stable subspace of `K^k`, so by `Work.C17y.dstable_const` it
  contains a nonzero constant vector `c`;  lifting gives `n ∈ Nsub` with constant integral block, and
  `∂n ∈ Nsub ⊓ Msub = ⊥`, which is exactly the adjoint equation `L*(b/p₂) = Σ cᵢ rᵢ` — contradicting
  `hadj`.
-/

namespace Work.C17y

open Complex Metric
open scoped Topology
open Submission.CDT (dRat)
open Work.GenShared (Rval Rreg W Dv Wev hasDerivAt_rval adjoint_eq_sum)

noncomputable section

/-- The finite exceptional set used in the `Nsub ⊓ Msub = ⊥` argument. -/
def badFinset2 {k : ℕ} (p2 : Polynomial ℂ) (hp2 : p2 ≠ 0) (rd : Fin k → Polynomial ℂ)
    (hrd : ∀ i, rd i ≠ 0) (F F' : Finset ℂ) (n n' : W k) (ZD : Finset ℂ) : Finset ℂ :=
  ((((((F ∪ F') ∪ (polesSet_finite n).toFinset) ∪ (polesSet_finite n').toFinset)
    ∪ (Polynomial.finite_setOfPred_isRoot hp2).toFinset)
    ∪ (Finset.univ.biUnion fun i : Fin k =>
        (Polynomial.finite_setOfPred_isRoot (hrd i)).toFinset))
    ∪ ZD)

lemma notMem_badFinset2 {k : ℕ} {p2 : Polynomial ℂ} (hp2 : p2 ≠ 0) {rd : Fin k → Polynomial ℂ}
    (hrd : ∀ i, rd i ≠ 0) {F F' : Finset ℂ} {n n' : W k} {ZD : Finset ℂ} {z : ℂ} :
    z ∉ badFinset2 p2 hp2 rd hrd F F' n n' ZD ↔
      (z ∉ F ∧ z ∉ F' ∧ z ∉ (polesSet_finite n).toFinset ∧ z ∉ (polesSet_finite n').toFinset
        ∧ z ∉ (Polynomial.finite_setOfPred_isRoot hp2).toFinset
        ∧ z ∉ (Finset.univ.biUnion fun i : Fin k =>
            (Polynomial.finite_setOfPred_isRoot (hrd i)).toFinset)
        ∧ z ∉ ZD) := by
  rw [badFinset2]
  simp only [Finset.mem_union, not_or, and_assoc]

/-- **`Nsub ⊓ Msub = ⊥`**, the Shidlovsky/Riccati step. -/
theorem inf_Msub_eq_bot {k : ℕ} (p2 p1 p0 : Polynomial ℂ) (rn rd : Fin k → Polynomial ℂ)
    (hp2 : p2 ≠ 0) (hrd : ∀ i, rd i ≠ 0)
    (hric : ∀ u : RatFunc ℂ,
      algebraMap (Polynomial ℂ) (RatFunc ℂ) p2 * (Submission.CDT.dRat u + u ^ 2)
        + algebraMap (Polynomial ℂ) (RatFunc ℂ) p1 * u
        + algebraMap (Polynomial ℂ) (RatFunc ℂ) p0 ≠ 0)
    {x0 : ℂ} {δ : ℝ} (hδ : 0 < δ) {y1 : ℂ → ℂ}
    (hy1d : DifferentiableOn ℂ y1 (Metric.ball x0 δ))
    (hy1ne : ∃ z ∈ Metric.ball x0 δ, y1 z ≠ 0)
    (hode : ∀ w ∈ Metric.ball x0 δ,
      p2.eval w * deriv (deriv y1) w + p1.eval w * deriv y1 w + p0.eval w * y1 w = 0)
    {J : Fin k → ℂ → ℂ} (hJd : ∀ i, DifferentiableOn ℂ (J i) (Metric.ball x0 δ))
    (hJderiv : ∀ i, ∀ w ∈ Metric.ball x0 δ,
      HasDerivAt (J i) ((rn i).eval w / (rd i).eval w * y1 w) w) :
    Nsub x0 δ y1 J ⊓ Msub = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro n hn
  rw [Submodule.mem_inf] at hn
  obtain ⟨hnN, hnM⟩ := hn
  have hnM' : n.2.2 = 0 := hnM
  obtain ⟨a, b, c⟩ := n
  simp only at hnM'
  subst hnM'
  -- `∂n ∈ Nsub`
  have hdv := van_dv p2 p1 p0 rn rd hp2 hrd hy1d hJd hode hJderiv hnN
  obtain ⟨F, hF⟩ := hnN
  obtain ⟨F', hF'⟩ := hdv
  -- the two components of `∂n`
  set A₂ : RatFunc ℂ := dRat a - (algebraMap (Polynomial ℂ) (RatFunc ℂ) p0
      / algebraMap (Polynomial ℂ) (RatFunc ℂ) p2) * b with hA₂
  set B₂ : RatFunc ℂ := a + dRat b - (algebraMap (Polynomial ℂ) (RatFunc ℂ) p1
      / algebraMap (Polynomial ℂ) (RatFunc ℂ) p2) * b with hB₂
  have hdv_comp : Dv p2 p1 p0 rn rd (a, b, 0) = (A₂, B₂, fun _ : Fin k => 0) := by
    rw [hA₂, hB₂]
    ext i <;> simp [Dv]
  -- the determinant of the Cramer system
  set Ddet : RatFunc ℂ := a * B₂ - b * A₂ with hDdet
  by_cases hD : Ddet = 0
  · -- ## The determinant vanishes
    rcases eq_or_ne b 0 with hb | hb
    · -- `b = 0`: the determinant is `a²`
      subst hb
      have hD' : a ^ 2 = 0 := by
        have := hD
        rw [hDdet] at this
        simpa [hA₂, hB₂] using this
      have ha : a = 0 := mul_self_eq_zero.mp (by simpa [pow_two] using hD')
      subst ha
      rfl
    · -- `b ≠ 0`: the Riccati equation of `p₂` has the rational solution `-a/b`
      have hD' : a * (a + dRat b - (algebraMap (Polynomial ℂ) (RatFunc ℂ) p1
              / algebraMap (Polynomial ℂ) (RatFunc ℂ) p2) * b)
            - b * (dRat a - (algebraMap (Polynomial ℂ) (RatFunc ℂ) p0
              / algebraMap (Polynomial ℂ) (RatFunc ℂ) p2) * b) = 0 := by
        have := hD
        rw [hDdet, hA₂, hB₂] at this
        exact this
      obtain ⟨u, hu⟩ := exists_riccati_of_det_eq_zero p2 p1 p0 hp2 a b hb hD'
      exact absurd hu (hric u)
  · -- ## The determinant does not vanish: Cramer forces `y₁ ≡ 0`
    exfalso
    set ZD : Finset ℂ := (Polynomial.finite_setOfPred_isRoot (RatFunc.num_ne_zero hD)).toFinset
      with hZD
    have hkey : ∀ z ∈ Metric.ball x0 δ,
        z ∉ (badFinset2 p2 hp2 rd hrd F F' (a, b, 0)
              (Dv p2 p1 p0 rn rd (a, b, 0)) ZD : Set ℂ) → y1 z = 0 := by
      intro z hz hzS
      obtain ⟨hzF, hzF', hzP, hzP', hp2z, hzrd, hzZD⟩ :=
        (notMem_badFinset2 hp2 hrd).mp (notMem_coe hzS)
      -- regularity at `z`
      have hzPset : z ∉ polesSet (a, b, 0) :=
        fun h => hzP ((Set.Finite.mem_toFinset (polesSet_finite (a, b, 0))).mpr h)
      obtain ⟨hza, hzb, -⟩ := not_mem_polesSet hzPset
      have hzP'set : z ∉ polesSet (A₂, B₂, fun _ : Fin k => 0) := by
        rw [← hdv_comp]
        exact fun h => hzP' ((Set.Finite.mem_toFinset (polesSet_finite _)).mpr h)
      obtain ⟨hza', hzb', -⟩ := not_mem_polesSet hzP'set
      -- the two equations
      have h1 : Rval a z * y1 z + Rval b z * deriv y1 z = 0 := by
        have := hF z hz (fun h => hzF (Finset.mem_coe.mpr h))
        simpa [Wev, Rval_zero] using this
      have h2 : Rval A₂ z * y1 z + Rval B₂ z * deriv y1 z = 0 := by
        have := hF' z hz (fun h => hzF' (Finset.mem_coe.mpr h))
        rw [hdv_comp] at this
        simpa [Wev, Rval_zero] using this
      -- the determinant does not vanish
      have hdetval : Rval a z * Rval B₂ z - Rval b z * Rval A₂ z ≠ 0 := by
        intro h0
        have hDval : Rval Ddet z = 0 := by
          rw [hDdet]
          rw [Rval_sub (a * B₂) (b * A₂) z (Work.GenShared.rreg_mul hza hzb')
              (Work.GenShared.rreg_mul hzb hza'),
            Rval_mul a B₂ z hza hzb', Rval_mul b A₂ z hzb hza']
          exact h0
        have hDne : Rval Ddet z ≠ 0 := by
          rw [Rval]
          exact div_ne_zero
            (fun h => hzZD ((mem_zeroFinset Ddet.num (RatFunc.num_ne_zero hD) z).mpr h))
            (by
              rw [hDdet]
              exact Work.GenShared.rreg_sub (Work.GenShared.rreg_mul hza hzb')
                (Work.GenShared.rreg_mul hzb hza'))
        exact hDne hDval
      have hcramer : (Rval a z * Rval B₂ z - Rval b z * Rval A₂ z) * y1 z = 0 := by
        linear_combination (Rval B₂ z) * h1 - (Rval b z) * h2
      exact (mul_eq_zero.mp hcramer).resolve_left hdetval
    have hzero : ∀ z ∈ Metric.ball x0 δ, y1 z = 0 :=
      eq_zero_of_forall_zero_of_notMem hy1d.continuousOn hkey
    obtain ⟨z₀, hz₀, hz₀ne⟩ := hy1ne
    exact hz₀ne (hzero z₀ hz₀)


/-- **The generic period-independence theorem.** -/
theorem periods_indep_gen {k : ℕ} (p2 p1 p0 : Polynomial ℂ) (hp2 : p2 ≠ 0)
    (rn rd : Fin k → Polynomial ℂ) (hrd : ∀ i, rd i ≠ 0)
    (hric : ∀ u : RatFunc ℂ,
      algebraMap (Polynomial ℂ) (RatFunc ℂ) p2 * (Submission.CDT.dRat u + u ^ 2)
        + algebraMap (Polynomial ℂ) (RatFunc ℂ) p1 * u
        + algebraMap (Polynomial ℂ) (RatFunc ℂ) p0 ≠ 0)
    (hadj : ∀ (β : RatFunc ℂ) (c : Fin k → ℂ),
      Submission.CDT.dRat
            (Submission.CDT.dRat (algebraMap (Polynomial ℂ) (RatFunc ℂ) p2 * β))
          - Submission.CDT.dRat (algebraMap (Polynomial ℂ) (RatFunc ℂ) p1 * β)
          + algebraMap (Polynomial ℂ) (RatFunc ℂ) p0 * β
        = ∑ i, (algebraMap ℂ (RatFunc ℂ) (c i)) *
            (algebraMap (Polynomial ℂ) (RatFunc ℂ) (rn i)
              / algebraMap (Polynomial ℂ) (RatFunc ℂ) (rd i)) →
      β = 0 ∧ c = 0)
    (x0 : ℂ) {δ : ℝ} (hδ : 0 < δ)
    (y1 : ℂ → ℂ) (hy1d : DifferentiableOn ℂ y1 (Metric.ball x0 δ))
    (hy1ne : ∃ z ∈ Metric.ball x0 δ, y1 z ≠ 0)
    (hode : ∀ z ∈ Metric.ball x0 δ,
      p2.eval z * deriv (deriv y1) z + p1.eval z * deriv y1 z + p0.eval z * y1 z = 0)
    (J : Fin k → ℂ → ℂ) (hJd : ∀ i, DifferentiableOn ℂ (J i) (Metric.ball x0 δ))
    (hJderiv : ∀ i, ∀ z ∈ Metric.ball x0 δ,
      HasDerivAt (J i) ((rn i).eval z / (rd i).eval z * y1 z) z)
    (A B : Polynomial ℂ) (C : Fin k → Polynomial ℂ)
    (hrel : ∀ z ∈ Metric.ball x0 δ,
      A.eval z * y1 z + B.eval z * deriv y1 z + ∑ i, (C i).eval z * J i z = 0) :
    A = 0 ∧ B = 0 ∧ C = 0 := by
  set n₀ : W k := ((algebraMap (Polynomial ℂ) (RatFunc ℂ) A),
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) B),
      (fun i => algebraMap (Polynomial ℂ) (RatFunc ℂ) (C i))) with hn₀
  have hn₀N : n₀ ∈ Nsub x0 δ y1 J := by
    refine ⟨∅, fun z hz _ => ?_⟩
    rw [hn₀]
    simpa only [Wev, Rval_algebraMap] using hrel z hz
  have hinf := inf_Msub_eq_bot p2 p1 p0 rn rd hp2 hrd hric hδ hy1d hy1ne hode hJd hJderiv
  by_cases hn : n₀ = 0
  · refine ⟨?_, ?_, ?_⟩
    · have h := congrArg Prod.fst hn
      exact IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ) (by simpa [hn₀] using h)
    · have h := congrArg (fun w : W k => w.2.1) hn
      exact IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ) (by simpa [hn₀] using h)
    · funext i
      have h := congrArg (fun w : W k => w.2.2 i) hn
      exact IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ) (by simpa [hn₀] using h)
  · exfalso
    have hNne : Nsub x0 δ y1 J ≠ ⊥ := by
      intro h
      have hmem : n₀ ∈ (⊥ : Submodule (RatFunc ℂ) (W k)) := by
        rw [← h]; exact hn₀N
      exact hn (by simpa using hmem)
    set V : Submodule (RatFunc ℂ) (Fin k → RatFunc ℂ) := (Nsub x0 δ y1 J).map proj3 with hV
    have hVne : V ≠ ⊥ := by
      intro hVbot
      have hNle : Nsub x0 δ y1 J ≤ Msub := by
        intro m hm
        have hmV : proj3 m ∈ V := Submodule.mem_map.mpr ⟨m, hm, rfl⟩
        rw [hVbot] at hmV
        show m.2.2 = 0
        exact hmV
      exact hNne (by rw [← inf_eq_left.mpr hNle, hinf])
    have hVstab : ∀ v ∈ V, (fun j => Submission.CDT.dRat (v j)) ∈ V := by
      intro v hv
      obtain ⟨m, hmN, rfl⟩ := Submodule.mem_map.mp hv
      refine Submodule.mem_map.mpr ⟨Dv p2 p1 p0 rn rd m,
        van_dv p2 p1 p0 rn rd hp2 hrd hy1d hJd hode hJderiv hmN, ?_⟩
      rfl
    obtain ⟨c, hcne, hcV⟩ := dstable_const V hVstab hVne
    obtain ⟨m, hmN, hmproj⟩ := Submodule.mem_map.mp hcV
    obtain ⟨a, b, cc⟩ := m
    -- `∂m ∈ Nsub ⊓ Msub = ⊥`
    have hdv' : Dv p2 p1 p0 rn rd (a, b, cc) ∈ Nsub x0 δ y1 J :=
      van_dv p2 p1 p0 rn rd hp2 hrd hy1d hJd hode hJderiv hmN
    have hdvM : Dv p2 p1 p0 rn rd (a, b, cc) ∈ Msub := by
      show (Dv p2 p1 p0 rn rd (a, b, cc)).2.2 = 0
      have h3 : (Dv p2 p1 p0 rn rd (a, b, cc)).2.2
          = fun i => Submission.CDT.dRat (cc i) := rfl
      have hcc : cc = fun i => algebraMap ℂ (RatFunc ℂ) (c i) := hmproj
      rw [h3, hcc]
      funext i
      show Submission.CDT.dRat (algebraMap ℂ (RatFunc ℂ) (c i)) = 0
      rw [show ((algebraMap ℂ (RatFunc ℂ) (c i)) : RatFunc ℂ)
          = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C (c i)) from by
            rw [Polynomial.C_eq_algebraMap,
              ← IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) (RatFunc ℂ)],
        Submission.CDT.dRat_algebraMap, Polynomial.derivative_C, map_zero]
    have hz0 : Dv p2 p1 p0 rn rd (a, b, cc) = 0 := by
      have hmem : Dv p2 p1 p0 rn rd (a, b, cc) ∈ Nsub x0 δ y1 J ⊓ Msub :=
        Submodule.mem_inf.mpr ⟨hdv', hdvM⟩
      rwa [hinf, Submodule.mem_bot] at hmem
    have h1 : Submission.CDT.dRat a
        - (algebraMap (Polynomial ℂ) (RatFunc ℂ) p0
            / algebraMap (Polynomial ℂ) (RatFunc ℂ) p2) * b
        + ∑ i, cc i * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (rn i)
            / algebraMap (Polynomial ℂ) (RatFunc ℂ) (rd i)) = 0 := by
      have h := congrArg Prod.fst hz0
      simpa [Dv] using h
    have h2 : a + Submission.CDT.dRat b
        - (algebraMap (Polynomial ℂ) (RatFunc ℂ) p1
            / algebraMap (Polynomial ℂ) (RatFunc ℂ) p2) * b = 0 := by
      have h := congrArg (fun w : W k => w.2.1) hz0
      simpa [Dv] using h
    have h1' : Submission.CDT.dRat a
        - (algebraMap (Polynomial ℂ) (RatFunc ℂ) p0
            / algebraMap (Polynomial ℂ) (RatFunc ℂ) p2) * b
        + ∑ i, (algebraMap ℂ (RatFunc ℂ) (c i)) * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (rn i)
            / algebraMap (Polynomial ℂ) (RatFunc ℂ) (rd i)) = 0 := by
      have hcc : cc = fun i => algebraMap ℂ (RatFunc ℂ) (c i) := hmproj
      rw [hcc] at h1
      exact h1
    have hadj' := adjoint_eq_sum p2 p1 p0 rn rd hp2 a b
      (fun i => algebraMap ℂ (RatFunc ℂ) (c i)) h1' h2
    exact hcne (hadj (b * (algebraMap (Polynomial ℂ) (RatFunc ℂ) p2)⁻¹) c hadj').2

end

end Work.C17y
