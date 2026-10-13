import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.ODE.ExistUnique
import Submission.Work.FTS.Galerkin.Ode.hasDerivWithinAt_glue

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedVariables false

namespace Work.FTS.RegPkgGal.R7d

open Set Metric Filter
open scoped Topology

/-! ## Auxiliary facts

The proof below builds a solution of `ẋ = f(t,x)` on `[0,T]` by a fixed-step Picard iteration over
the windows of a partition of `[0,T]`, gluing the local solutions.  The helpers are (i) the
"singleton" form of the within-derivative (the zeroth window has length `0`), (ii)
Picard–Lindelöf on an arbitrary set `S` that contains the closed ball of radius `a` about the
centre (the box `S` of the statement is *not* a ball, but it contains one, with room given by the
strict inclusions), and (iii) the predicate carried by the `n`-th approximation. -/

/-- The derivative of any function within the singleton `{0}`. -/
private theorem hasDerivWithinAt_singleton_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : ℝ → E) (v : E) : HasDerivWithinAt g v ({0} : Set ℝ) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have h : ({0} : Set ℝ) \ {0} = ∅ := by ext x; simp
  rw [h, nhdsWithin_empty]
  exact Filter.tendsto_bot

/-- **Picard–Lindelöf on a set containing a ball about the centre.** If `f` is Lipschitz in `x`
and bounded on `S`, continuous in `t` on `S`, and `S` contains the closed ball of radius `a` about
`x₀`, then `f` is Picard–Lindelöf on the window `[tmin, tmax]` with centre `x₀`, provided
`L * (tmax - tmin) ≤ a`. -/
private theorem isPicardLindelof_of_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E → E} {S : Set E} {x₀ : E} {tmin tmax a L K : ℝ}
    (ha : 0 ≤ a) (hL : 0 < L) (hK : 0 ≤ K)
    (hball : Metric.closedBall x₀ a ⊆ S)
    (hlip : ∀ t ∈ Set.Icc tmin tmax, LipschitzOnWith ⟨K, hK⟩ (f t) S)
    (hbdd : ∀ t ∈ Set.Icc tmin tmax, ∀ x ∈ S, ‖f t x‖ ≤ L)
    (htcont : ∀ x ∈ S, ContinuousOn (fun t => f t x) (Set.Icc tmin tmax))
    (htle : tmin ≤ tmax) (htmax : L * max (tmax - tmin) 0 ≤ a) :
    IsPicardLindelof f ⟨tmin, le_rfl, htle⟩ x₀ (Real.toNNReal a) 0 (Real.toNNReal L)
      (Real.toNNReal K) := by
  have hball' : Metric.closedBall x₀ (Real.toNNReal a) ⊆ S := by
    rw [show (Real.toNNReal a : ℝ) = a from Real.coe_toNNReal _ ha]
    exact hball
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [show Real.toNNReal K = ⟨K, hK⟩ from Real.toNNReal_of_nonneg hK]
    exact (hlip t ht).mono hball'
  · intro x hx
    exact htcont x (hball' hx)
  · intro t ht x hx
    rw [show (Real.toNNReal L : ℝ) = L from Real.coe_toNNReal _ hL.le]
    exact hbdd t ht x (hball' hx)
  · rw [show (Real.toNNReal L : ℝ) = L from Real.coe_toNNReal _ hL.le,
      show (Real.toNNReal a : ℝ) = a from Real.coe_toNNReal _ ha, NNReal.coe_zero, sub_zero]
    have htv : (⟨tmin, le_rfl, htle⟩ : ↑(Set.Icc tmin tmax)).1 = tmin := rfl
    rw [htv, sub_self]
    exact htmax

/-- The predicate carried by the `n`-th approximation: it solves `ẋ = f(t,x)` on `[0,s]` with
`α 0 = u₀`. -/
private structure IsSol (f : ℝ → ℝ × ℝ → ℝ × ℝ) (u₀ : ℝ × ℝ) (s : ℝ)
    (α : ℝ → ℝ × ℝ) : Prop where
  init : α 0 = u₀
  sol : ∀ t ∈ Set.Icc (0:ℝ) s, HasDerivWithinAt α (f t (α t)) (Set.Icc (0:ℝ) s) t

/-- Picard–Lindelöf with an a priori bound, on a finite time horizon `[0,T]` and on an
axis-parallel box: `f` is Lipschitz in `x` (const `Klip`) and bounded (`L`) on the outer box
`Icc zlo' zhi' ×ˢ Icc θlo' θhi'`, continuous in `t` there, the inner box `Icc zlo zhi ×ˢ Icc θlo θhi`
sits strictly inside the outer one (`zlo' < zlo`, `zhi < zhi'`, `θlo' < θlo`, `θhi < θhi'`), the
starting point `u₀` lies in the inner box, and *every* solution through `u₀` on any `[0,T']` with
`T' ≤ T` stays in the inner box (the a priori estimate). Then a solution exists on all of `[0,T]`.
Intended proof: a finite iteration over windows of length `δ = ε/(2L)` with
`ε = min (zlo-zlo') (zhi'-zhi) (θlo-θlo') (θhi'-θhi)`, each step being Mathlib's
`IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt` with centre `α (nδ)` and radius `ε/2`,
glued by `HasDerivWithinAt.union` (there is a ready-made glue lemma
`Work.FTS.Galerkin.Ode.hasDerivWithinAt_glue` in this workspace, and the sibling proof
`Work.FTS.Galerkin.exists_global_solution_of_bound` does the same iteration for the
`[0,∞)`/ball case and is a good template). -/
theorem ode_box_existence
    (f : ℝ → ℝ × ℝ → ℝ × ℝ) (u₀ : ℝ × ℝ) {T L Klip : ℝ}
    {zlo zhi θlo θhi zlo' zhi' θlo' θhi' : ℝ}
    (hT : 0 ≤ T) (hL : 0 < L) (hKlip : 0 ≤ Klip)
    (hu₀ : u₀.1 ∈ Set.Icc zlo zhi ∧ u₀.2 ∈ Set.Icc θlo θhi)
    (hzi : zlo' < zlo) (hzs : zhi < zhi') (hti : θlo' < θlo) (hts : θhi < θhi')
    (hlip : ∀ t ∈ Set.Icc (0:ℝ) T, LipschitzOnWith ⟨Klip, hKlip⟩ (f t)
      (Set.Icc zlo' zhi' ×ˢ Set.Icc θlo' θhi'))
    (hbdd : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ x ∈ Set.Icc zlo' zhi' ×ˢ Set.Icc θlo' θhi', ‖f t x‖ ≤ L)
    (htcont : ∀ x ∈ Set.Icc zlo' zhi' ×ˢ Set.Icc θlo' θhi',
      ContinuousOn (fun t => f t x) (Set.Icc (0:ℝ) T))
    (htraj : ∀ T' ∈ Set.Icc (0:ℝ) T, ∀ α : ℝ → ℝ × ℝ, α 0 = u₀ →
      (∀ t ∈ Set.Icc (0:ℝ) T', HasDerivWithinAt α (f t (α t)) (Set.Icc (0:ℝ) T') t) →
      ∀ t ∈ Set.Icc (0:ℝ) T', (α t).1 ∈ Set.Icc zlo zhi ∧ (α t).2 ∈ Set.Icc θlo θhi) :
    ∃ α : ℝ → ℝ × ℝ, α 0 = u₀ ∧
      ∀ t ∈ Set.Icc (0:ℝ) T, HasDerivWithinAt α (f t (α t)) (Set.Icc (0:ℝ) T) t := by
  classical
  -- ### The margin `ε` between the inner and the outer box
  obtain ⟨hzi', hzs', hti', hts'⟩ :
      0 < zlo - zlo' ∧ 0 < zhi' - zhi ∧ 0 < θlo - θlo' ∧ 0 < θhi' - θhi :=
    ⟨by linarith, by linarith, by linarith, by linarith⟩
  set ε : ℝ := min (min (zlo - zlo') (zhi' - zhi)) (min (θlo - θlo') (θhi' - θhi)) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]; exact lt_min (lt_min hzi' hzs') (lt_min hti' hts')
  have hεle1 : ε ≤ zlo - zlo' := by
    rw [hεdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hεle2 : ε ≤ zhi' - zhi := by
    rw [hεdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hεle3 : ε ≤ θlo - θlo' := by
    rw [hεdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hεle4 : ε ≤ θhi' - θhi := by
    rw [hεdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  -- ### The ball of radius `ε` about a point of the inner box lies in the outer box
  have hball : ∀ x ∈ Set.Icc zlo zhi ×ˢ Set.Icc θlo θhi,
      Metric.closedBall x ε ⊆ Set.Icc zlo' zhi' ×ˢ Set.Icc θlo' θhi' := by
    rintro x ⟨hx1, hx2⟩ y hy
    rw [Metric.mem_closedBall, Prod.dist_eq, Real.dist_eq, Real.dist_eq] at hy
    have h1 : -ε ≤ y.1 - x.1 := (abs_le.mp (le_trans (le_max_left _ _) hy)).1
    have h2 : y.1 - x.1 ≤ ε := (abs_le.mp (le_trans (le_max_left _ _) hy)).2
    have h3 : -ε ≤ y.2 - x.2 := (abs_le.mp (le_trans (le_max_right _ _) hy)).1
    have h4 : y.2 - x.2 ≤ ε := (abs_le.mp (le_trans (le_max_right _ _) hy)).2
    rw [Set.mem_Icc] at hx1 hx2
    constructor
    · rw [Set.mem_Icc]; exact ⟨by linarith [hx1.1], by linarith [hx1.2]⟩
    · rw [Set.mem_Icc]; exact ⟨by linarith [hx2.1], by linarith [hx2.2]⟩
  -- ### The number of steps and the step length
  obtain ⟨N, hN⟩ : ∃ N : ℕ, T * L / ε < (N : ℝ) := exists_nat_gt _
  have hNpos : (0:ℝ) < (N:ℝ) :=
    lt_of_le_of_lt (div_nonneg (mul_nonneg hT hL.le) hεpos.le) hN
  have hNne : (N:ℝ) ≠ 0 := hNpos.ne'
  set δ : ℝ := T / N with hδdef
  have hδnn : 0 ≤ δ := by rw [hδdef]; exact div_nonneg hT hNpos.le
  have hNδ : (N:ℝ) * δ = T := by
    rw [hδdef]
    field_simp
  have hNL : T * L ≤ (N:ℝ) * ε := by
    have h2 : (T * L / ε) * ε < (N:ℝ) * ε := mul_lt_mul_of_pos_right hN hεpos
    rw [div_mul_cancel₀ _ hεpos.ne'] at h2
    linarith
  have hLδ : L * δ ≤ ε := by
    have h3 : L * δ = T * L / (N:ℝ) := by rw [hδdef]; ring
    rw [h3, div_le_iff₀ hNpos]
    linarith
  -- ### The induction: a solution on `[0, (min n N) δ]` for every `n`
  have hkey : ∀ n : ℕ, ∃ α : ℝ → ℝ × ℝ,
      IsSol f u₀ (((min n N : ℕ) : ℝ) * δ) α := by
    intro n
    induction n with
    | zero =>
      have h0 : (((min 0 N : ℕ)) : ℝ) * δ = 0 := by
        rw [Nat.min_eq_left (Nat.zero_le N)]; simp
      refine ⟨fun _ => u₀, rfl, ?_⟩
      intro t ht
      rw [h0] at ht ⊢
      rw [Set.Icc_self, Set.mem_singleton_iff] at ht
      rw [Set.Icc_self, ht]
      exact hasDerivWithinAt_singleton_zero _ _
    | succ k ih =>
      by_cases hk : k < N
      · -- ### one Picard step on the window `[kδ, (k+1)δ]`
        have hkmin : min k N = k := Nat.min_eq_left hk.le
        have hk1min : min (k + 1) N = k + 1 := Nat.min_eq_left (Nat.succ_le_of_lt hk)
        rw [hk1min]
        obtain ⟨α, hα0, hαsol⟩ := ih
        rw [hkmin] at hαsol
        set t₀ : ℝ := (k:ℝ) * δ with ht₀def
        have hαsol' : ∀ t ∈ Set.Icc (0:ℝ) t₀,
            HasDerivWithinAt α (f t (α t)) (Set.Icc (0:ℝ) t₀) t := by
          rw [ht₀def]; exact hαsol
        have ht0nn : 0 ≤ t₀ := by rw [ht₀def]; positivity
        have ht0T : t₀ ≤ T := by
          have h1 : (k:ℝ) ≤ (N:ℝ) := by exact_mod_cast hk.le
          calc t₀ = (k:ℝ) * δ := ht₀def
            _ ≤ (N:ℝ) * δ := mul_le_mul_of_nonneg_right h1 hδnn
            _ = T := hNδ
        have hxk : α t₀ ∈ Set.Icc zlo zhi ×ˢ Set.Icc θlo θhi :=
          Set.mem_prod.mpr (htraj t₀ ⟨ht0nn, ht0T⟩ α hα0 hαsol' t₀ ⟨ht0nn, le_rfl⟩)
        have hcast : (((k + 1 : ℕ)) : ℝ) * δ = t₀ + δ := by
          rw [ht₀def]; push_cast; ring
        have hle : t₀ ≤ t₀ + δ := by linarith [hδnn]
        have hwin : Set.Icc t₀ (t₀ + δ) ⊆ Set.Icc (0:ℝ) T := by
          intro t ht
          refine ⟨le_trans ht0nn ht.1, ?_⟩
          have h1 : (((k + 1 : ℕ)) : ℝ) ≤ (N:ℝ) := by
            exact_mod_cast (Nat.succ_le_of_lt hk)
          calc t ≤ t₀ + δ := ht.2
            _ = (((k + 1 : ℕ)) : ℝ) * δ := hcast.symm
            _ ≤ (N:ℝ) * δ := mul_le_mul_of_nonneg_right h1 hδnn
            _ = T := hNδ
        have hpl : IsPicardLindelof f ⟨t₀, le_rfl, hle⟩ (α t₀) (Real.toNNReal ε) 0
            (Real.toNNReal L) (Real.toNNReal Klip) := by
          refine isPicardLindelof_of_subset hεpos.le hL hKlip (hball (α t₀) hxk) ?_ ?_ ?_ hle ?_
          · intro t ht; exact hlip t (hwin ht)
          · intro t ht x hx; exact hbdd t (hwin ht) x hx
          · intro x hx; exact (htcont x hx).mono hwin
          · rw [show t₀ + δ - t₀ = δ from by ring, max_eq_left hδnn]
            exact hLδ
        obtain ⟨γ, hγ0, hγd⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt
          (x := α t₀) (hx := Metric.mem_closedBall_self (by simp))
        have hglue : ∀ t ∈ Set.Icc (0:ℝ) (t₀ + δ),
            HasDerivWithinAt (fun y : ℝ => if y ≤ t₀ then α y else γ y)
              (f t (if t ≤ t₀ then α t else γ t)) (Set.Icc (0:ℝ) (t₀ + δ)) t :=
          Work.FTS.Galerkin.Ode.hasDerivWithinAt_glue (f := α) (g := γ) (a := 0) (b := t₀)
            (c := t₀ + δ) ht0nn hle hγ0.symm
            (v := fun x => f x (if x ≤ t₀ then α x else γ x))
            (fun x hxm => by
              have h := hαsol' x hxm
              have hif : (if x ≤ t₀ then α x else γ x) = α x := ite_eq_left hxm.2
              rwa [← hif] at h)
            (fun x hxm => by
              have h := hγd x hxm
              have hif : (if x ≤ t₀ then α x else γ x) = γ x := by
                by_cases hxb : x ≤ t₀
                · rw [ite_eq_left hxb]
                  have hxeq : x = t₀ := le_antisymm hxb hxm.1
                  rw [hxeq]
                  exact hγ0.symm
                · exact ite_eq_right hxb
              rwa [← hif] at h)
        refine ⟨fun y : ℝ => if y ≤ t₀ then α y else γ y, ?_, ?_⟩
        · show (if (0:ℝ) ≤ t₀ then α 0 else γ 0) = u₀
          rw [ite_eq_left ht0nn]
          exact hα0
        · intro t ht
          rw [hcast] at ht ⊢
          exact hglue t ht
      · -- ### beyond `N` steps the interval is already full: keep the approximation
        have hkN : N ≤ k := Nat.le_of_not_lt hk
        have hm1 : min k N = N := Nat.min_eq_right hkN
        have hm2 : min (k + 1) N = N := Nat.min_eq_right (le_trans hkN (Nat.le_succ k))
        rw [hm2]
        obtain ⟨α, hα⟩ := ih
        rw [hm1] at hα
        exact ⟨α, hα⟩
  -- ### The `N`-th approximation is the required global solution
  obtain ⟨α, hα0, hαsol⟩ := hkey N
  rw [Nat.min_self N] at hαsol
  rw [hNδ] at hαsol
  exact ⟨α, hα0, hαsol⟩

end Work.FTS.RegPkgGal.R7d
