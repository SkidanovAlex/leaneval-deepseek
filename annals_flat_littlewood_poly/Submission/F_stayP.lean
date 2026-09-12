import Mathlib
import Submission.LMProbs
import Submission.LMMeas
import Submission.LMAux
import Submission.F_gauss
import Submission.F_chernoff
import Submission.F_freshlin

/-!
The Lovett--Meka walk stays inside the polytope with high probability.

Context: `Xn n T δ γ x0 v c ω t` is the walk position after `t` steps (each step
adds γ times a standard Gaussian projected orthogonally to the frozen constraints).
`Proj n T δ γ x0 v c ω s` is the projected increment used to go from time `s` to
`s+1`; `Xn_succ` says
  Xn n T δ γ x0 v c ω (s+1) = Xn n T δ γ x0 v c ω s + γ • Proj n T δ γ x0 v c ω s
for s < T.

`basis n i` is the i-th coordinate vector with `‖basis n i‖ = 1`.
`walkProj_row_zero`: if j ∈ frozenRows δ x0 v c x then vin (walkProj v A B g) (v j) = 0.
`walkProj_coord_zero`: for i ∈ frozenVars δ x, (walkProj v A B g) i = 0.

PART A: `step_cross_prob_le`: for a fixed direction w (`‖w‖ ≠ 0`), the probability
that the s-th projected increment has a component of size ≥ δ‖w‖/γ along w is at
most 2·exp(-δ²/(2γ²)).

PART B: `stay_in_polytope_prob_le`: the walk stays in the polytope
`inPolytope x0 v c` for all times `t ≤ T` with probability at least
1 - 2·T·(n + |ι|)·exp(-δ²/(2γ²)).

The union bound is taken over the finitely many times `s < T` and the
`n + |ι|` constraint directions (coordinate axes and row vectors `v j`).
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory ProbabilityTheory

noncomputable section
open Classical

namespace Submission.Discrepancy

/-- Membership in the polytope P (coordinate box and discrepancy bounds). -/
def inPolytope {n : ℕ} {ι : Type*} [Fintype ι] (x0 : Vec n) (v : ι → Vec n) (c : ι → ℝ)
    (x : Vec n) : Prop :=
  (∀ i : Fin n, |x i| ≤ 1) ∧ (∀ j : ι, |vin (x - x0) (v j)| ≤ c j * ‖v j‖)

lemma basis_norm (n : ℕ) (i : Fin n) : ‖basis n i‖ = 1 := by
  simp [basis]

lemma basis_norm_ne_zero (n : ℕ) (i : Fin n) : ‖basis n i‖ ≠ 0 := by
  rw [basis_norm]
  norm_num

lemma oracle_prefix_eq {n T : ℕ} (ω : Omega n T) (s : ℕ) (hs : s < T) :
    oracle n T ω s = oracle n (s + 1) (first T (s + 1) (Nat.succ_le_of_lt hs) ω) s := by
  unfold oracle
  rw [dif_pos hs, dif_pos (Nat.lt_succ_self s)]
  rfl

lemma Xn_prefix_eq {n T : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (ω : Omega n T) (s t : ℕ) (hts : t ≤ s) (hsT : s < T) :
    Xn n T δ γ x0 v c ω t = Xn n (s + 1) δ γ x0 v c (first T (s + 1) (Nat.succ_le_of_lt hsT) ω) t := by
  unfold Xn
  apply xseq_congr
  intro u hu
  have huT : u < T := lt_trans hu (lt_of_le_of_lt hts hsT)
  have hu1 : u < s + 1 := lt_trans hu (Nat.lt_succ_of_le hts)
  unfold oracle
  rw [dif_pos huT, dif_pos hu1]
  rfl

lemma Proj_prefix_eq {n T : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (ω : Omega n T) (s : ℕ) (hs : s < T) :
    Proj n T δ γ x0 v c ω s = Proj n (s + 1) δ γ x0 v c (first T (s + 1) (Nat.succ_le_of_lt hs) ω) s := by
  unfold Proj AVn BVn
  rw [Xn_prefix_eq (n := n) (T := T) (ι := ι) δ γ x0 v c ω s s (le_refl s) hs]
  rw [oracle_prefix_eq (n := n) (T := T) ω s hs]

lemma oracle_snoc {n s : ℕ} (p : Omega n s) (g : Vec n) :
    oracle n (s + 1) (Fin.snoc (α := fun _ : Fin (s + 1) => Vec n) p g) s = g := by
  unfold oracle
  rw [dif_pos (Nat.lt_succ_self s)]
  have hlast : (⟨s, Nat.lt_succ_self s⟩ : Fin (s + 1)) = Fin.last s := by
    apply Fin.ext
    simp [Fin.last]
  rw [hlast]
  simp [Fin.snoc_last]

lemma Proj_snoc {n : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (s : ℕ) (p : Omega n s) (g : Vec n) :
    Proj n (s + 1) δ γ x0 v c (Fin.snoc (α := fun _ : Fin (s + 1) => Vec n) p g) s =
      walkProj v (frozenVars δ (Xn n s δ γ x0 v c p s))
        (frozenRows δ x0 v c (Xn n s δ γ x0 v c p s)) g := by
  unfold Proj AVn BVn
  rw [Xn_snoc (n := n) (T := s) δ γ x0 v c g p s (le_refl s)]
  rw [oracle_snoc (n := n) (s := s) p g]

lemma measurable_first (n : ℕ) (T t : ℕ) (ht : t ≤ T) :
    Measurable (first (n := n) T t ht) := by
  rw [measurable_pi_iff]
  intro i
  change Measurable (fun ω : Omega n T => ω (⟨i.val, by omega⟩ : Fin T))
  exact measurable_pi_apply (⟨i.val, by omega⟩ : Fin T)

lemma prefix_measureReal {n T t : ℕ} (ht : t ≤ T) (E : Set (Omega n t))
    (hE : MeasurableSet E) :
    (mu n T).real {ω : Omega n T | first T t ht ω ∈ E} = (mu n t).real E := by
  have hfirst : Measurable (first (n := n) T t ht) := measurable_first n T t ht
  have hmap : (mu n T).map (first (n := n) T t ht) = mu n t := by
    apply MeasureTheory.Measure.ext
    intro E0 hE0
    rw [MeasureTheory.Measure.map_apply hfirst hE0]
    have hF : Measurable (E0.indicator (fun _ : Omega n t => (1 : ENNReal))) :=
      Measurable.indicator measurable_const hE0
    have hlin := lintegral_first n T t ht (E0.indicator (fun _ : Omega n t => (1 : ENNReal))) hF
    calc
      (mu n T) (first T t ht ⁻¹' E0)
          = ∫⁻ ω : Omega n T, (E0.indicator (fun _ : Omega n t => (1 : ENNReal))) (first T t ht ω) ∂(mu n T) := by
            rw [show (fun ω : Omega n T => (E0.indicator (fun _ : Omega n t => (1 : ENNReal))) (first T t ht ω)) =
                (first T t ht ⁻¹' E0).indicator (fun _ : Omega n T => (1 : ENNReal)) by
              funext ω
              simp [Set.indicator]]
            rw [lintegral_indicator_const (s := first T t ht ⁻¹' E0) (hfirst hE0) (1 : ENNReal)]
            simp
      _ = ∫⁻ q : Omega n t, (E0.indicator (fun _ : Omega n t => (1 : ENNReal))) q ∂(mu n t) := hlin
      _ = (mu n t) E0 := by
            rw [lintegral_indicator_const (s := E0) hE0 (1 : ENNReal)]
            simp
  rw [show {ω : Omega n T | first T t ht ω ∈ E} = first T t ht ⁻¹' E by rfl]
  rw [← MeasureTheory.map_measureReal_apply (μ := mu n T) (f := first T t ht) hfirst hE]
  rw [hmap]



lemma Proj_cell_sum {n T : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (ω : Omega n T) (t : ℕ) :
    Proj n T δ γ x0 v c ω t =
      ∑ A : Finset (Fin n), ∑ B : Finset ι,
        if frozenVars δ (Xn n T δ γ x0 v c ω t) = A ∧ frozenRows δ x0 v c (Xn n T δ γ x0 v c ω t) = B then
          walkProj v A B (oracle n T ω t) else 0 := by
  unfold Proj AVn BVn
  rw [Finset.sum_eq_single (frozenVars δ (Xn n T δ γ x0 v c ω t))]
  · rw [Finset.sum_eq_single (frozenRows δ x0 v c (Xn n T δ γ x0 v c ω t))]
    · simp
    · intro B hB hne
      by_cases hB2 : frozenRows δ x0 v c (Xn n T δ γ x0 v c ω t) = B
      · exact (hne hB2.symm).elim
      · simp [hB2]
    · intro hB
      exact (hB (Finset.mem_univ _)).elim
  · intro A hA hne
    rw [Finset.sum_eq_zero]
    intro B hB
    by_cases hA2 : frozenVars δ (Xn n T δ γ x0 v c ω t) = A
    · exact (hne hA2.symm).elim
    · simp [hA2]
  · intro hA
    exact (hA (Finset.mem_univ _)).elim

/-- Measurability of the projection at time t. -/
lemma measurable_Proj {n T : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (t : ℕ) (ht : t < T) :
    Measurable (fun ω : Omega n T => Proj n T δ γ x0 v c ω t) := by
  have htle : t ≤ T := le_of_lt ht
  have hX : Measurable (fun ω : Omega n T => Xn n T δ γ x0 v c ω t) :=
    measurable_Xn (n := n) (ι := ι) (T := T) (t := t) htle δ γ x0 v c
  have hor : Measurable (fun ω : Omega n T => oracle n T ω t) := by
    rw [show (fun ω : Omega n T => oracle n T ω t) = (fun ω : Omega n T => ω (⟨t, ht⟩ : Fin T)) by
      funext ω
      simp [oracle, ht]]
    exact measurable_pi_apply (⟨t, ht⟩ : Fin T)
  rw [show (fun ω : Omega n T => Proj n T δ γ x0 v c ω t) = fun ω =>
      ∑ A : Finset (Fin n), ∑ B : Finset ι,
        if frozenVars δ (Xn n T δ γ x0 v c ω t) = A ∧ frozenRows δ x0 v c (Xn n T δ γ x0 v c ω t) = B then
          walkProj v A B (oracle n T ω t) else 0 by
    funext ω
    exact Proj_cell_sum (n := n) (T := T) (ι := ι) δ γ x0 v c ω t]
  exact Finset.measurable_sum (Finset.univ : Finset (Finset (Fin n))) (by
    intro A hA
    exact Finset.measurable_sum (Finset.univ : Finset (Finset ι)) (by
      intro B hB
      have hcell : MeasurableSet {ω : Omega n T |
          frozenVars δ (Xn n T δ γ x0 v c ω t) = A ∧
            frozenRows δ x0 v c (Xn n T δ γ x0 v c ω t) = B} := by
        have h1 : MeasurableSet {ω : Omega n T | frozenVars δ (Xn n T δ γ x0 v c ω t) = A} := by
          rw [show {ω : Omega n T | frozenVars δ (Xn n T δ γ x0 v c ω t) = A} =
              (fun ω : Omega n T => Xn n T δ γ x0 v c ω t) ⁻¹' {x : Vec n | frozenVars δ x = A} by
            ext ω; simp]
          exact (measurableSet_frozenVars_eq δ A).preimage hX
        have h2 : MeasurableSet {ω : Omega n T | frozenRows δ x0 v c (Xn n T δ γ x0 v c ω t) = B} := by
          rw [show {ω : Omega n T | frozenRows δ x0 v c (Xn n T δ γ x0 v c ω t) = B} =
              (fun ω : Omega n T => Xn n T δ γ x0 v c ω t) ⁻¹' {x : Vec n | frozenRows δ x0 v c x = B} by
            ext ω; simp]
          exact (measurableSet_frozenRows_eq δ x0 v c B).preimage hX
        exact h1.inter h2
      refine Measurable.ite hcell ?_ (by simp)
      exact (continuous_walkProj v A B).measurable.comp hor))



lemma measurableSet_cross {n T : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (w : Vec n) (a : ℝ) (s : ℕ) (hs : s < T) :
    MeasurableSet {ω : Omega n T | a ≤ |vin (Proj n T δ γ x0 v c ω s) w|} := by
  have hproj : Measurable (fun ω : Omega n T => Proj n T δ γ x0 v c ω s) :=
    measurable_Proj (n := n) (T := T) (ι := ι) δ γ x0 v c s hs
  have hvin : Measurable (fun ω : Omega n T => vin (Proj n T δ γ x0 v c ω s) w) :=
    (measurable_vin n w).comp hproj
  have habs : Measurable (fun ω : Omega n T => |vin (Proj n T δ γ x0 v c ω s) w|) := hvin.abs
  rw [show {ω : Omega n T | a ≤ |vin (Proj n T δ γ x0 v c ω s) w|} =
      (fun ω : Omega n T => |vin (Proj n T δ γ x0 v c ω s) w|) ⁻¹' Set.Ici a by
    ext ω
    simp]
  exact (measurableSet_Ici (a := a)).preimage habs



lemma step_cross_fiber_le {n : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (v : ι → Vec n)
    (A : Finset (Fin n)) (B : Finset ι) (hγ : 0 < γ) (hδ : 0 < δ) (w : Vec n) (hw : ‖w‖ ≠ 0) :
    (stdGaussian (Vec n)).real {g : Vec n | δ * ‖w‖ / γ ≤
        |vin (walkProj v A B g) w|} ≤ 2 * Real.exp (-(δ ^ 2) / (2 * γ ^ 2)) := by
  let Z : Vec n → ℝ := fun g => vin (walkProj v A B g) w
  let a : ℝ := δ * ‖w‖ / γ
  have hZmeas : Measurable Z := by
    dsimp [Z]
    exact (measurable_vin n w).comp (continuous_walkProj v A B).measurable
  have hσsq : 0 < ‖w‖ ^ 2 := sq_pos_of_ne_zero hw
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact div_nonneg (mul_nonneg hδ.le (norm_nonneg w)) hγ.le
  have hint : ∀ t : ℝ, Integrable (fun g : Vec n => Real.exp (t * Z g)) (stdGaussian (Vec n)) := by
    intro t
    have hEq : (fun g : Vec n => Real.exp (t * Z g)) =ᵐ[stdGaussian (Vec n)]
        (fun g : Vec n => Real.exp (t * vin g (walkProj v A B w))) := by
      filter_upwards with g
      have hz : Z g = vin g (walkProj v A B w) := by
        dsimp [Z]
        exact proj_adjoint v A B g w
      rw [hz]
    exact (integrable_mgf_exp n (walkProj v A B w) t).congr hEq.symm
  have hmgf : ∀ t : ℝ, (∫ g : Vec n, Real.exp (t * Z g) ∂(stdGaussian (Vec n))) ≤
      Real.exp (t ^ 2 * ‖w‖ ^ 2 / 2) := by
    intro t
    have hb := fresh_step_bound (n := n) (ι := ι) v A B t (1 : ℝ) w
    calc
      (∫ g : Vec n, Real.exp (t * Z g) ∂(stdGaussian (Vec n)))
          ≤ Real.exp (t ^ 2 * 1 ^ 2 * ‖w‖ ^ 2 / 2) := by
              simpa [Z] using hb
      _ = Real.exp (t ^ 2 * ‖w‖ ^ 2 / 2) := by ring_nf
  have hmain := prob_abs_ge_le_of_mgf (μ := stdGaussian (Vec n)) (Z := Z) hZmeas
    (‖w‖ ^ 2) hσsq hint hmgf a ha0
  have hset : {g : Vec n | a ≤ |Z g|} = {g : Vec n | δ * ‖w‖ / γ ≤
      |vin (walkProj v A B g) w|} := by
    ext g
    simp [Z, a]
  have hcalc : -(a ^ 2) / (2 * ‖w‖ ^ 2) = -(δ ^ 2) / (2 * γ ^ 2) := by
    dsimp [a]
    field_simp [hw, hγ.ne']
  calc
    (stdGaussian (Vec n)).real {g : Vec n | δ * ‖w‖ / γ ≤
        |vin (walkProj v A B g) w|}
        ≤ 2 * Real.exp (-(a ^ 2) / (2 * ‖w‖ ^ 2)) := by
            rw [← hset]
            exact hmain
    _ = 2 * Real.exp (-(δ ^ 2) / (2 * γ ^ 2)) := by
            rw [hcalc]



lemma map_snoc_curry_inverse (n s : ℕ) :
    ((mu n (s+1)).map (fun ω : Omega n (s+1) => (ω (Fin.last s), Fin.init ω))).map
      (fun y : Vec n × Omega n s => Fin.snoc (α := fun _ : Fin (s+1) => Vec n) y.2 y.1) = mu n (s+1) := by
  have hpeel : Measurable (fun ω : Omega n (s+1) => (ω (Fin.last s), Fin.init ω)) := by
    rw [show (fun ω : Omega n (s+1) => (ω (Fin.last s), Fin.init ω)) = peelEquiv n s by
      funext ω
      exact (peelEquiv_apply n s ω).symm]
    exact (peelEquiv n s).measurable
  have hsnoc : Measurable (fun y : Vec n × Omega n s =>
      Fin.snoc (α := fun _ : Fin (s+1) => Vec n) y.2 y.1) := measurable_snoc_curry n s
  rw [MeasureTheory.Measure.map_map hsnoc hpeel]
  have hid : (fun y : Vec n × Omega n s => Fin.snoc (α := fun _ : Fin (s+1) => Vec n) y.2 y.1) ∘
      (fun ω : Omega n (s+1) => (ω (Fin.last s), Fin.init ω)) = id := by
    funext ω
    change Fin.snoc (α := fun _ : Fin (s+1) => Vec n)
        (Fin.init (α := fun _ : Fin (s+1) => Vec n) ω) (ω (Fin.last s)) = ω
    exact Fin.snoc_init_self (α := fun _ : Fin (s+1) => Vec n) ω
  rw [hid, MeasureTheory.Measure.map_id]

/-- Measure of a set on `Omega n (s+1)` as an integral over the prefix `p` of the
Gaussian measure of the fibers over the fresh coordinate. -/
lemma measure_snoc_form (n s : ℕ) (E1 : Set (Omega n (s+1))) (hE1 : MeasurableSet E1) :
    (mu n (s+1)) E1 = ∫⁻ p : Omega n s,
      (stdGaussian (Vec n)) {g : Vec n | Fin.snoc (α := fun _ : Fin (s+1) => Vec n) p g ∈ E1} ∂(mu n s) := by
  let ν : Measure (Vec n × Omega n s) := (stdGaussian (Vec n)).prod (mu n s)
  let φ : Vec n × Omega n s → Omega n (s+1) := fun y =>
    Fin.snoc (α := fun _ : Fin (s+1) => Vec n) y.2 y.1
  have hνeq : ν = (mu n (s+1)).map (fun ω : Omega n (s+1) => (ω (Fin.last s), Fin.init ω)) := by
    dsimp [ν]
    exact (peel_measurePreserving n s).symm
  have hφm : Measurable φ := by
    dsimp [φ]
    exact measurable_snoc_curry n s
  have hφν : ν.map φ = mu n (s+1) := by
    rw [hνeq]
    exact map_snoc_curry_inverse n s
  have hpre : MeasurableSet (φ ⁻¹' E1) := hφm hE1
  calc
    (mu n (s+1)) E1 = (ν.map φ) E1 := by rw [← hφν]
    _ = ν (φ ⁻¹' E1) := by
        rw [MeasureTheory.Measure.map_apply hφm hE1]
    _ = ∫⁻ p : Omega n s, (stdGaussian (Vec n)) {g : Vec n | (g, p) ∈ φ ⁻¹' E1} ∂(mu n s) := by
        dsimp [ν]
        rw [MeasureTheory.Measure.prod_apply_symm (μ := stdGaussian (Vec n)) (ν := mu n s)
          (s := φ ⁻¹' E1) hpre]
        apply lintegral_congr
        intro p
        apply congrArg (stdGaussian (Vec n))
        ext g
        simp
    _ = ∫⁻ p : Omega n s, (stdGaussian (Vec n)) {g : Vec n |
          Fin.snoc (α := fun _ : Fin (s+1) => Vec n) p g ∈ E1} ∂(mu n s) := by
        apply lintegral_congr
        intro p
        apply congrArg (stdGaussian (Vec n))
        ext g
        simp [φ]



lemma step_cross_prob_le {n T : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (hγ : 0 < γ) (hδ : 0 < δ) {w : Vec n} (hw : ‖w‖ ≠ 0) {s : ℕ} (hs : s < T) :
    (mu n T).real {ω : Omega n T | δ * ‖w‖ / γ ≤ |vin (Proj n T δ γ x0 v c ω s) w|} ≤
      2 * Real.exp (-(δ ^ 2) / (2 * γ ^ 2)) := by
  let a : ℝ := δ * ‖w‖ / γ
  let e : ℝ := Real.exp (-(δ ^ 2) / (2 * γ ^ 2))
  have ht : s + 1 ≤ T := Nat.succ_le_of_lt hs
  let E1 : Set (Omega n (s+1)) := {q : Omega n (s+1) | a ≤ |vin (Proj n (s+1) δ γ x0 v c q s) w|}
  have hE1meas : MeasurableSet E1 := by
    dsimp [E1]
    exact measurableSet_cross (n := n) (T := s+1) (ι := ι) δ γ x0 v c w a s (Nat.lt_succ_self s)
  have hset_eq : {ω : Omega n T | δ * ‖w‖ / γ ≤ |vin (Proj n T δ γ x0 v c ω s) w|} =
      {ω : Omega n T | first T (s+1) ht ω ∈ E1} := by
    ext ω
    dsimp [E1, a]
    rw [Proj_prefix_eq (n := n) (T := T) (ι := ι) δ γ x0 v c ω s hs]
  have hred : (mu n T).real {ω : Omega n T | δ * ‖w‖ / γ ≤ |vin (Proj n T δ γ x0 v c ω s) w|}
      = (mu n (s+1)).real E1 := by
    rw [hset_eq]
    exact prefix_measureReal (n := n) (T := T) (t := s+1) ht E1 hE1meas
  have hbound : (mu n (s+1)).real E1 ≤ 2 * e := by
    have hmain : (mu n (s+1)) E1 ≤ ENNReal.ofReal (2 * e) := by
      calc
        (mu n (s+1)) E1 = ∫⁻ p : Omega n s, (stdGaussian (Vec n)) {g : Vec n |
              Fin.snoc (α := fun _ : Fin (s+1) => Vec n) p g ∈ E1} ∂(mu n s) :=
              measure_snoc_form n s E1 hE1meas
        _ ≤ ∫⁻ p : Omega n s, ENNReal.ofReal (2 * e) ∂(mu n s) := by
            apply lintegral_mono
            intro p
            change (stdGaussian (Vec n)) {g : Vec n |
              Fin.snoc (α := fun _ : Fin (s+1) => Vec n) p g ∈ E1} ≤ ENNReal.ofReal (2 * e)
            have hsetfib : {g : Vec n | Fin.snoc (α := fun _ : Fin (s+1) => Vec n) p g ∈ E1} =
                {g : Vec n | a ≤ |vin (walkProj v (frozenVars δ (Xn n s δ γ x0 v c p s))
                    (frozenRows δ x0 v c (Xn n s δ γ x0 v c p s)) g) w|} := by
              ext g
              dsimp [E1]
              rw [Proj_snoc (n := n) (ι := ι) δ γ x0 v c s p g]
            have hfib : (stdGaussian (Vec n)).real {g : Vec n |
                  Fin.snoc (α := fun _ : Fin (s+1) => Vec n) p g ∈ E1} ≤ 2 * e := by
              rw [hsetfib]
              dsimp [e, a]
              exact step_cross_fiber_le (n := n) (ι := ι) δ γ v
                (frozenVars δ (Xn n s δ γ x0 v c p s))
                (frozenRows δ x0 v c (Xn n s δ γ x0 v c p s)) hγ hδ w hw
            rw [← MeasureTheory.ofReal_measureReal (μ := stdGaussian (Vec n)) (s := {g : Vec n |
                  Fin.snoc (α := fun _ : Fin (s+1) => Vec n) p g ∈ E1})]
            exact ENNReal.ofReal_le_ofReal hfib
        _ = ENNReal.ofReal (2 * e) := by
            rw [lintegral_const]
            rw [MeasureTheory.IsProbabilityMeasure.measure_univ]
            simp
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hmain
  calc
    (mu n T).real {ω : Omega n T | δ * ‖w‖ / γ ≤ |vin (Proj n T δ γ x0 v c ω s) w|}
        = (mu n (s+1)).real E1 := hred
    _ ≤ 2 * e := hbound



/-- Membership in the polytope P (coordinate box and discrepancy bounds). -/
lemma Xn_zero {n T : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (ω : Omega n T) : Xn n T δ γ x0 v c ω 0 = x0 := by
  rfl

lemma inPolytope_x0 {n : ℕ} {ι : Type*} [Fintype ι] (x0 : Vec n) (v : ι → Vec n) (c : ι → ℝ)
    (hx0 : ∀ i : Fin n, |x0 i| ≤ 1) (hc : ∀ j : ι, 0 ≤ c j) :
    inPolytope x0 v c x0 := by
  constructor
  · exact hx0
  · intro j
    rw [show x0 - x0 = 0 by simp]
    simp [vin]
    exact mul_nonneg (hc j) (norm_nonneg _)

lemma Xn_succ_val {n T : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (ω : Omega n T) (t : ℕ) (ht : t < T) :
    Xn n T δ γ x0 v c ω (t + 1) = Xn n T δ γ x0 v c ω t + γ • Proj n T δ γ x0 v c ω t := by
  rw [Xn_succ (n := n) (T := T) δ γ x0 v c ω t ht]

lemma Xn_add_one {n T : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (ω : Omega n T) (t : ℕ) (ht : t < T) :
    Xn n T δ γ x0 v c ω (t + 1) = Xn n T δ γ x0 v c ω t + γ • Proj n T δ γ x0 v c ω t :=
  Xn_succ_val (n := n) (T := T) δ γ x0 v c ω t ht

lemma coord_succ_val {n T : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (ω : Omega n T) (t : ℕ) (ht : t < T) (i : Fin n) :
    (Xn n T δ γ x0 v c ω (t + 1)) i = (Xn n T δ γ x0 v c ω t) i
      + γ * (Proj n T δ γ x0 v c ω t) i := by
  rw [Xn_add_one (n := n) (T := T) δ γ x0 v c ω t ht]
  simp

lemma row_succ_val {n T : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (ω : Omega n T) (t : ℕ) (ht : t < T) (j : ι) :
    vin (Xn n T δ γ x0 v c ω (t + 1) - x0) (v j) =
      vin (Xn n T δ γ x0 v c ω t - x0) (v j)
        + γ * vin (Proj n T δ γ x0 v c ω t) (v j) := by
  rw [Xn_add_one (n := n) (T := T) δ γ x0 v c ω t ht]
  have hb : vin (Xn n T δ γ x0 v c ω t + γ • Proj n T δ γ x0 v c ω t - x0) (v j)
      = vin (Xn n T δ γ x0 v c ω t - x0) (v j)
        + γ * vin (Proj n T δ γ x0 v c ω t) (v j) := by
    simp [vin, inner_add_left, inner_smul_left, inner_sub_left, inner_sub_right,
      inner_add_right]
    ring
  exact hb

lemma frozen_coord_proj_zero {n T : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n)
    (v : ι → Vec n) (c : ι → ℝ) (ω : Omega n T) (t : ℕ) {i : Fin n}
    (hi : i ∈ frozenVars δ (Xn n T δ γ x0 v c ω t)) :
    (Proj n T δ γ x0 v c ω t) i = 0 := by
  unfold Proj AVn BVn
  exact walkProj_coord_zero v (frozenVars δ (Xn n T δ γ x0 v c ω t))
    (frozenRows δ x0 v c (Xn n T δ γ x0 v c ω t)) (oracle n T ω t) hi

lemma frozen_row_proj_zero {n T : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n)
    (v : ι → Vec n) (c : ι → ℝ) (ω : Omega n T) (t : ℕ) {j : ι}
    (hj : j ∈ frozenRows δ x0 v c (Xn n T δ γ x0 v c ω t)) :
    vin (Proj n T δ γ x0 v c ω t) (v j) = 0 := by
  unfold Proj AVn BVn
  exact walkProj_row_zero v (frozenVars δ (Xn n T δ γ x0 v c ω t))
    (frozenRows δ x0 v c (Xn n T δ γ x0 v c ω t)) (oracle n T ω t) hj

lemma coord_abs_mem_frozen {n : ℕ} (δ : ℝ) (x : Vec n) (i : Fin n) :
    i ∈ frozenVars δ x ↔ 1 - δ ≤ |x i| := by
  simp [frozenVars]

lemma row_abs_mem_frozen {n : ℕ} {ι : Type*} [Fintype ι] (δ : ℝ) (x0 : Vec n) (v : ι → Vec n) (c : ι → ℝ)
    (x : Vec n) (j : ι) :
    j ∈ frozenRows δ x0 v c x ↔ (c j - δ) * ‖v j‖ ≤ |vin (x - x0) (v j)| := by
  simp [frozenRows]



lemma coord_cross {n T : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (hγ : 0 < γ) (hδ : 0 < δ) (ω : Omega n T) (t : ℕ) (ht : t < T) (i : Fin n)
    (hprev : inPolytope x0 v c (Xn n T δ γ x0 v c ω t))
    (hnext : 1 < |(Xn n T δ γ x0 v c ω (t + 1)) i|) :
    δ * ‖basis n i‖ / γ ≤ |vin (Proj n T δ γ x0 v c ω t) (basis n i)| := by
  let A : Vec n := Xn n T δ γ x0 v c ω t
  let Pj : Vec n := Proj n T δ γ x0 v c ω t
  have hprev_coord : |A i| ≤ 1 := hprev.1 i
  have hnotf : ¬ (1 - δ ≤ |A i|) := by
    intro hf
    have hiA : i ∈ frozenVars δ A := (coord_abs_mem_frozen δ A i).2 hf
    have hzero : Pj i = 0 := frozen_coord_proj_zero (n := n) (T := T) (ι := ι) δ γ x0 v c ω t hiA
    have hsame : (Xn n T δ γ x0 v c ω (t + 1)) i = A i := by
      rw [coord_succ_val (n := n) (T := T) (ι := ι) δ γ x0 v c ω t ht i]
      dsimp [A, Pj]
      rw [hzero, mul_zero, add_zero]
    rw [hsame] at hnext
    linarith
  have hprev_lt : |A i| < 1 - δ := lt_of_not_ge hnotf
  have htri : |(Xn n T δ γ x0 v c ω (t + 1)) i| ≤ |A i| + γ * |Pj i| := by
    rw [coord_succ_val (n := n) (T := T) (ι := ι) δ γ x0 v c ω t ht i]
    calc
      |A i + γ * Pj i| ≤ |A i| + |γ * Pj i| := abs_add_le _ _
      _ = |A i| + γ * |Pj i| := by rw [abs_mul, abs_of_pos hγ]
  have hδlt : δ < γ * |Pj i| := by
    dsimp [A, Pj] at hprev_lt htri hnext
    nlinarith
  have hδlt' : δ < |Pj i| * γ := by
    rw [mul_comm]
    exact hδlt
  have hdiv : δ / γ < |Pj i| := (div_lt_iff₀ hγ).mpr hδlt'
  have hmem : |vin Pj (basis n i)| = |Pj i| := by
    have hv : vin Pj (basis n i) = Pj i := by
      rw [show vin Pj (basis n i) = vin (basis n i) Pj by
        unfold vin
        rw [real_inner_comm]]
      exact vin_basis n i Pj
    rw [hv]
  rw [basis_norm, hmem]
  norm_num
  exact le_of_lt (by simpa [Pj] using hdiv)



lemma row_cross {n T : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (hγ : 0 < γ) (hδ : 0 < δ) (ω : Omega n T) (t : ℕ) (ht : t < T) (j : ι)
    (hprev : inPolytope x0 v c (Xn n T δ γ x0 v c ω t))
    (hnext : c j * ‖v j‖ < |vin (Xn n T δ γ x0 v c ω (t + 1) - x0) (v j)|) :
    δ * ‖v j‖ / γ ≤ |vin (Proj n T δ γ x0 v c ω t) (v j)| := by
  have hprev_row : |vin (Xn n T δ γ x0 v c ω t - x0) (v j)| ≤ c j * ‖v j‖ := hprev.2 j
  have hnotmem : j ∉ frozenRows δ x0 v c (Xn n T δ γ x0 v c ω t) := by
    intro hmem
    have hzero : vin (Proj n T δ γ x0 v c ω t) (v j) = 0 :=
      frozen_row_proj_zero (n := n) (T := T) (ι := ι) δ γ x0 v c ω t hmem
    have hN : vin (Xn n T δ γ x0 v c ω (t + 1) - x0) (v j) =
        vin (Xn n T δ γ x0 v c ω t - x0) (v j) := by
      rw [row_succ_val (n := n) (T := T) (ι := ι) δ γ x0 v c ω t ht j]
      rw [hzero, mul_zero, add_zero]
    rw [hN] at hnext
    linarith
  have hnf : ¬ (c j - δ) * ‖v j‖ ≤ |vin (Xn n T δ γ x0 v c ω t - x0) (v j)| := by
    intro hle
    exact hnotmem ((row_abs_mem_frozen (n := n) (ι := ι) δ x0 v c (Xn n T δ γ x0 v c ω t) j).2 hle)
  have htri : |vin (Xn n T δ γ x0 v c ω (t + 1) - x0) (v j)| ≤
      |vin (Xn n T δ γ x0 v c ω t - x0) (v j)| + γ * |vin (Proj n T δ γ x0 v c ω t) (v j)| := by
    have hsucc := row_succ_val (n := n) (T := T) (ι := ι) δ γ x0 v c ω t ht j
    calc
      |vin (Xn n T δ γ x0 v c ω (t + 1) - x0) (v j)|
          = |vin (Xn n T δ γ x0 v c ω t - x0) (v j) + γ * vin (Proj n T δ γ x0 v c ω t) (v j)| := by
              rw [hsucc]
      _ ≤ |vin (Xn n T δ γ x0 v c ω t - x0) (v j)| + |γ * vin (Proj n T δ γ x0 v c ω t) (v j)| :=
              abs_add_le _ _
      _ = |vin (Xn n T δ γ x0 v c ω t - x0) (v j)| + γ * |vin (Proj n T δ γ x0 v c ω t) (v j)| := by
              rw [abs_mul, abs_of_pos hγ]
  by_cases hneg : (c j - δ) * ‖v j‖ ≤ 0
  · exfalso
    apply hnf
    exact le_trans hneg (abs_nonneg _)
  · have hpvlt : |vin (Xn n T δ γ x0 v c ω t - x0) (v j)| < (c j - δ) * ‖v j‖ := lt_of_not_ge hnf
    have hδlt : δ * ‖v j‖ < γ * |vin (Proj n T δ γ x0 v c ω t) (v j)| := by
      nlinarith
    have hδlt' : δ * ‖v j‖ < |vin (Proj n T δ γ x0 v c ω t) (v j)| * γ := by
      calc
        δ * ‖v j‖ < γ * |vin (Proj n T δ γ x0 v c ω t) (v j)| := hδlt
        _ = |vin (Proj n T δ γ x0 v c ω t) (v j)| * γ := by rw [mul_comm]
    have hdiv : δ * ‖v j‖ / γ < |vin (Proj n T δ γ x0 v c ω t) (v j)| := (div_lt_iff₀ hγ).mpr hδlt'
    exact le_of_lt hdiv






lemma exists_cross_step {n T : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n)
    (v : ι → Vec n) (c : ι → ℝ) (hγ : 0 < γ) (hδ : 0 < δ)
    (hx0 : ∀ i : Fin n, |x0 i| ≤ 1) (hc : ∀ j : ι, 0 ≤ c j)
    (ω : Omega n T) :
    (¬ ∀ t : ℕ, t ≤ T → inPolytope x0 v c (Xn n T δ γ x0 v c ω t)) →
      ∃ s : ℕ, s < T ∧
        ((∃ i : Fin n, δ * ‖basis n i‖ / γ ≤ |vin (Proj n T δ γ x0 v c ω s) (basis n i)|) ∨
         (∃ j : ι, δ * ‖v j‖ / γ ≤ |vin (Proj n T δ γ x0 v c ω s) (v j)|)) := by
  let X : ℕ → Vec n := fun t => Xn n T δ γ x0 v c ω t
  intro hbad
  have hP0 : inPolytope x0 v c (X 0) := by
    dsimp [X]
    exact inPolytope_x0 (n := n) (ι := ι) x0 v c hx0 hc
  have hQ : ∃ t : ℕ, t ≤ T ∧ ¬ inPolytope x0 v c (X t) := by
    by_contra h
    apply hbad
    intro t ht
    by_contra hP
    exact h ⟨t, ht, hP⟩
  let m : ℕ := Nat.find hQ
  have hmQ : m ≤ T ∧ ¬ inPolytope x0 v c (X m) := Nat.find_spec hQ
  have hmpos : 0 < m := by
    by_contra h
    have hm0 : m = 0 := by omega
    apply hmQ.2
    have hX : X m = X 0 := by rw [hm0]
    rw [hX]
    exact hP0
  have hprevP : inPolytope x0 v c (X (m - 1)) := by
    by_contra hP
    have hq : m - 1 ≤ T ∧ ¬ inPolytope x0 v c (X (m - 1)) := ⟨by omega, hP⟩
    exact (Nat.find_min hQ (by omega : m - 1 < m)) hq
  have hsT : m - 1 < T := by omega
  have hcases : (∃ i : Fin n, 1 < |(X m) i|) ∨
      (∃ j : ι, c j * ‖v j‖ < |vin (X m - x0) (v j)|) := by
    by_contra h
    have hcoord : ∀ i : Fin n, |(X m) i| ≤ 1 := by
      intro i
      by_contra hle
      apply h
      left
      exact ⟨i, lt_of_not_ge hle⟩
    have hrow : ∀ j : ι, |vin (X m - x0) (v j)| ≤ c j * ‖v j‖ := by
      intro j
      by_contra hle
      apply h
      right
      exact ⟨j, lt_of_not_ge hle⟩
    exact hmQ.2 ⟨hcoord, hrow⟩
  rcases hcases with ⟨i, hi⟩ | ⟨j, hj⟩
  · refine ⟨m - 1, hsT, Or.inl ⟨i, ?_⟩⟩
    apply coord_cross (n := n) (T := T) (ι := ι) δ γ x0 v c hγ hδ ω (m - 1) hsT i
    · simpa [X] using hprevP
    · have hmeq : (m - 1) + 1 = m := by omega
      rw [hmeq]
      change 1 < |(Xn n T δ γ x0 v c ω m) i| at hi
      exact hi
  · refine ⟨m - 1, hsT, Or.inr ⟨j, ?_⟩⟩
    apply row_cross (n := n) (T := T) (ι := ι) δ γ x0 v c hγ hδ ω (m - 1) hsT j
    · simpa [X] using hprevP
    · have hmeq : (m - 1) + 1 = m := by omega
      rw [hmeq]
      change c j * ‖v j‖ < |vin (Xn n T δ γ x0 v c ω m - x0) (v j)| at hj
      exact hj


lemma stay_in_polytope_prob_le2 {n T : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n)
    (v : ι → Vec n) (c : ι → ℝ) (hγ : 0 < γ) (hδ : 0 < δ)
    (hx0 : ∀ i : Fin n, |x0 i| ≤ 1) (hc : ∀ j : ι, 0 ≤ c j) (hne : ∀ j : ι, ‖v j‖ ≠ 0) :
    (mu n T).real {ω : Omega n T | ¬ (∀ t : ℕ, t ≤ T → inPolytope x0 v c (Xn n T δ γ x0 v c ω t))} ≤
      2 * (T : ℝ) * ((n : ℝ) + (Fintype.card ι : ℝ)) * Real.exp (-(δ ^ 2) / (2 * γ ^ 2)) := by
  let e : ℝ := Real.exp (-(δ ^ 2) / (2 * γ ^ 2))
  let Bad : Set (Omega n T) := {ω | ¬ (∀ t : ℕ, t ≤ T → inPolytope x0 v c (Xn n T δ γ x0 v c ω t))}
  let S : Vec n → ℕ → Set (Omega n T) := fun w s => {ω | δ * ‖w‖ / γ ≤
    |vin (Proj n T δ γ x0 v c ω s) w|}
  let A : ℕ → Set (Omega n T) := fun s => (⋃ i : Fin n, S (basis n i) s) ∪ (⋃ j : ι, S (v j) s)
  have hcont : Bad ⊆ ⋃ s ∈ Finset.range T, A s := by
    intro ω hω
    have hbadω : ¬ (∀ t : ℕ, t ≤ T → inPolytope x0 v c (Xn n T δ γ x0 v c ω t)) := by
      simpa [Bad] using hω
    rcases exists_cross_step (n := n) (T := T) (ι := ι) δ γ x0 v c hγ hδ hx0 hc ω hbadω with
      ⟨s, hsT, hcase⟩
    rw [Set.mem_iUnion]
    refine ⟨s, ?_⟩
    rw [Set.mem_iUnion]
    refine ⟨Finset.mem_range.mpr hsT, ?_⟩
    rcases hcase with ⟨i, hi⟩ | ⟨j, hj⟩
    · apply Set.mem_union_left
      exact Set.mem_iUnion.mpr ⟨i, by simpa [S] using hi⟩
    · apply Set.mem_union_right
      exact Set.mem_iUnion.mpr ⟨j, by simpa [S] using hj⟩
  have hA : ∀ s : ℕ, s < T → (mu n T).real (A s) ≤ (∑ i : Fin n, 2 * e) + (∑ j : ι, 2 * e) := by
    intro s hs
    dsimp [A]
    calc
      (mu n T).real ((⋃ i : Fin n, S (basis n i) s) ∪ (⋃ j : ι, S (v j) s))
          ≤ (mu n T).real (⋃ i : Fin n, S (basis n i) s) + (mu n T).real (⋃ j : ι, S (v j) s) :=
              measureReal_union_le _ _
      _ ≤ (∑ i : Fin n, (mu n T).real (S (basis n i) s)) +
            (∑ j : ι, (mu n T).real (S (v j) s)) := by
              exact add_le_add (measureReal_iUnion_fintype_le (μ := mu n T)
                (fun i : Fin n => S (basis n i) s))
                (measureReal_iUnion_fintype_le (μ := mu n T) (fun j : ι => S (v j) s))
      _ ≤ (∑ i : Fin n, 2 * e) + (∑ j : ι, 2 * e) := by
              exact add_le_add
                (Finset.sum_le_sum (s := Finset.univ) (fun i hi =>
                  step_cross_prob_le (n := n) (T := T) (ι := ι) δ γ x0 v c hγ hδ
                    (w := basis n i) (basis_norm_ne_zero n i) (s := s) hs))
                (Finset.sum_le_sum (s := Finset.univ) (fun j hj =>
                  step_cross_prob_le (n := n) (T := T) (ι := ι) δ γ x0 v c hγ hδ
                    (w := v j) (hne j) (s := s) hs))
  have hmain : (mu n T).real Bad ≤
      (∑ s ∈ Finset.range T, ((∑ i : Fin n, 2 * e) + (∑ j : ι, 2 * e))) := by
    calc
      (mu n T).real Bad ≤ (mu n T).real (⋃ s ∈ Finset.range T, A s) := by
        exact measureReal_mono hcont (MeasureTheory.measure_ne_top (mu n T) (⋃ s ∈ Finset.range T, A s))
      _ ≤ ∑ s ∈ Finset.range T, (mu n T).real (A s) :=
            measureReal_biUnion_finset_le (Finset.range T) A
      _ ≤ ∑ s ∈ Finset.range T, ((∑ i : Fin n, 2 * e) + (∑ j : ι, 2 * e)) := by
        apply Finset.sum_le_sum
        intro s hs
        exact hA s (Finset.mem_range.mp hs)
  have harith : (∑ s ∈ Finset.range T, ((∑ i : Fin n, 2 * e) + (∑ j : ι, 2 * e))) =
      2 * (T : ℝ) * ((n : ℝ) + (Fintype.card ι : ℝ)) * e := by
    simp [Finset.sum_const, nsmul_eq_mul]
    ring
  have hfin : (mu n T).real Bad ≤ 2 * (T : ℝ) * ((n : ℝ) + (Fintype.card ι : ℝ)) * e :=
    hmain.trans_eq harith
  simpa [Bad, e] using hfin



lemma stay_in_polytope_prob_le {n T : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n)
    (v : ι → Vec n) (c : ι → ℝ) (hγ : 0 < γ) (hδ : 0 < δ)
    (hx0 : ∀ i : Fin n, |x0 i| ≤ 1) (hc : ∀ j : ι, 0 ≤ c j) (hne : ∀ j : ι, ‖v j‖ ≠ 0) :
    (mu n T).real {ω : Omega n T | ¬ (∀ t : ℕ, t ≤ T → inPolytope x0 v c (Xn n T δ γ x0 v c ω t))} ≤
      2 * (T : ℝ) * ((n : ℝ) + (Fintype.card ι : ℝ)) * Real.exp (-(δ ^ 2) / (2 * γ ^ 2)) := by
  let e : ℝ := Real.exp (-(δ ^ 2) / (2 * γ ^ 2))
  let Bad : Set (Omega n T) := {ω | ¬ (∀ t : ℕ, t ≤ T → inPolytope x0 v c (Xn n T δ γ x0 v c ω t))}
  let S : Vec n → ℕ → Set (Omega n T) := fun w s => {ω | δ * ‖w‖ / γ ≤
    |vin (Proj n T δ γ x0 v c ω s) w|}
  let A : ℕ → Set (Omega n T) := fun s => (⋃ i : Fin n, S (basis n i) s) ∪ (⋃ j : ι, S (v j) s)
  have hcont : Bad ⊆ ⋃ s ∈ Finset.range T, A s := by
    intro ω hω
    have hbadω : ¬ (∀ t : ℕ, t ≤ T → inPolytope x0 v c (Xn n T δ γ x0 v c ω t)) := by
      simpa [Bad] using hω
    rcases exists_cross_step (n := n) (T := T) (ι := ι) δ γ x0 v c hγ hδ hx0 hc ω hbadω with
      ⟨s, hsT, hcase⟩
    rw [Set.mem_iUnion]
    refine ⟨s, ?_⟩
    rw [Set.mem_iUnion]
    refine ⟨Finset.mem_range.mpr hsT, ?_⟩
    rcases hcase with ⟨i, hi⟩ | ⟨j, hj⟩
    · apply Set.mem_union_left
      exact Set.mem_iUnion.mpr ⟨i, by simpa [S] using hi⟩
    · apply Set.mem_union_right
      exact Set.mem_iUnion.mpr ⟨j, by simpa [S] using hj⟩
  have hA : ∀ s : ℕ, s < T → (mu n T).real (A s) ≤ (∑ i : Fin n, 2 * e) + (∑ j : ι, 2 * e) := by
    intro s hs
    dsimp [A]
    calc
      (mu n T).real ((⋃ i : Fin n, S (basis n i) s) ∪ (⋃ j : ι, S (v j) s))
          ≤ (mu n T).real (⋃ i : Fin n, S (basis n i) s) + (mu n T).real (⋃ j : ι, S (v j) s) :=
              measureReal_union_le _ _
      _ ≤ (∑ i : Fin n, (mu n T).real (S (basis n i) s)) +
            (∑ j : ι, (mu n T).real (S (v j) s)) := by
              exact add_le_add (measureReal_iUnion_fintype_le (μ := mu n T)
                (fun i : Fin n => S (basis n i) s))
                (measureReal_iUnion_fintype_le (μ := mu n T) (fun j : ι => S (v j) s))
      _ ≤ (∑ i : Fin n, 2 * e) + (∑ j : ι, 2 * e) := by
              exact add_le_add
                (Finset.sum_le_sum (s := Finset.univ) (fun i hi =>
                  step_cross_prob_le (n := n) (T := T) (ι := ι) δ γ x0 v c hγ hδ
                    (w := basis n i) (basis_norm_ne_zero n i) (s := s) hs))
                (Finset.sum_le_sum (s := Finset.univ) (fun j hj =>
                  step_cross_prob_le (n := n) (T := T) (ι := ι) δ γ x0 v c hγ hδ
                    (w := v j) (hne j) (s := s) hs))
  have hmain : (mu n T).real Bad ≤
      (∑ s ∈ Finset.range T, ((∑ i : Fin n, 2 * e) + (∑ j : ι, 2 * e))) := by
    calc
      (mu n T).real Bad ≤ (mu n T).real (⋃ s ∈ Finset.range T, A s) := by
        exact measureReal_mono hcont (MeasureTheory.measure_ne_top (mu n T) (⋃ s ∈ Finset.range T, A s))
      _ ≤ ∑ s ∈ Finset.range T, (mu n T).real (A s) :=
            measureReal_biUnion_finset_le (Finset.range T) A
      _ ≤ ∑ s ∈ Finset.range T, ((∑ i : Fin n, 2 * e) + (∑ j : ι, 2 * e)) := by
        apply Finset.sum_le_sum
        intro s hs
        exact hA s (Finset.mem_range.mp hs)
  have harith : (∑ s ∈ Finset.range T, ((∑ i : Fin n, 2 * e) + (∑ j : ι, 2 * e))) =
      2 * (T : ℝ) * ((n : ℝ) + (Fintype.card ι : ℝ)) * e := by
    simp [Finset.sum_const, nsmul_eq_mul]
    ring
  have hfin : (mu n T).real Bad ≤ 2 * (T : ℝ) * ((n : ℝ) + (Fintype.card ι : ℝ)) * e :=
    hmain.trans_eq harith
  simpa [Bad, e] using hfin


end Discrepancy

end Submission
