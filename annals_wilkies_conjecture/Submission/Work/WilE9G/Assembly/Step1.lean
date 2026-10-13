/-
  Subproject WilE9G / Assembly — the maximisation step of the covering argument.

  For a semi-pfaffian set `X`, a point `z₀ ∈ X.set`, a point `w ∈ comp(X, z₀)`, a basic `B` of `X`
  which holds at `w` and a direction `c`, the maximiser of the weight
  `Φ_B · e^{c·(y,t)}` (with `Φ_B = ∏_{g ∈ B.pos} g`) on the component of the fibre
  `comp(X,z₀) ∩ {π = π w}` through `w`, cut down by `B`:

  * it exists (`exists_maximiser`), lies in the component and in `B`, and dominates the weight on
    the whole of `component ∩ B`.

  This is the "barrier" step of the design (`WilE9G/STATUS.md` §3.3): `Φ_B` is positive on the
  piece of `B`, nonnegative on its closure, so the maximiser cannot escape to the boundary of the
  basic (where some `g ∈ B.pos` would vanish and `Φ_B` would drop to `0`).
-/
import Mathlib
import Submission.Work.WilE9G.All
import Submission.Work.WilE9G.Lagrange.lagStratum_good

set_option autoImplicit false
noncomputable section
open Classical Topology Filter MeasureTheory
namespace Work.WilE9G.Assembly
open WilkiesDesign WilkiesDesign.E Work.WilE9G Work.WilE9G.Lagrange

variable {n m : ℕ}

/-- The base projection to the first `n` coordinates is the first `n` coordinates of `stratProj`. -/
theorem projBase_eq_init_stratProj (w : Fin (n + (1 + m)) → ℝ) :
    projBase (Nat.le_add_right n (1 + m)) w = Fin.init (Work.WilE9.Sharp.stratProj w) := by
  funext i
  show w (Fin.castLE (Nat.le_add_right n (1 + m)) i)
    = w (Work.WilE9.Sharp.stratInj (Fin.castAdd m (Fin.castSucc i)))
  exact congrArg w (Fin.ext rfl)

theorem continuous_projBase' {N n : ℕ} (hn : n ≤ N) : Continuous (projBase hn) :=
  continuous_pi fun i => continuous_apply _

/-- The weight of the maximisation: `Φ_B · e^{c·(y,t)}`, as a real-valued function. -/
def weight (X : SemiPf (n + (1 + m))) (B : Basic (n + (1 + m)) X.r) (c : Fin (1 + m) → ℝ)
    (z : Fin (n + (1 + m)) → ℝ) : ℝ :=
  eaEval X.c B.pos.prod z * Real.exp (∑ l : Fin (1 + m), c l * z (Fin.natAdd n l))

theorem continuous_weight (X : SemiPf (n + (1 + m))) (B : Basic (n + (1 + m)) X.r)
    (c : Fin (1 + m) → ℝ) : Continuous (weight X B c) := by
  refine Continuous.mul (lagStratum_continuous_eaEval X.c B.pos.prod) (Real.continuous_exp.comp ?_)
  exact continuous_finsetSum _ fun l _ => Continuous.mul continuous_const (continuous_apply _)

/-- The weight is positive at a point of the basic. -/
theorem weight_holds_pos (X : SemiPf (n + (1 + m))) (B : Basic (n + (1 + m)) X.r)
    (c : Fin (1 + m) → ℝ) {z : Fin (n + (1 + m)) → ℝ} (hz : B.holds X.c z) :
    0 < weight X B c z := by
  have hprod : 0 < eaEval X.c B.pos.prod z := by
    have h : (B.pos.map (fun g => eaEval X.c g z)).prod > 0 := by
      refine List.prod_pos ?_
      intro g hg
      obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
      exact hz.2 g₀ hg₀
    simpa only [eaEval, map_list_prod] using h
  exact mul_pos hprod (Real.exp_pos _)

/-- If `Φ_B` is positive and all the inequalities of `B` are nonnegative, then all of them are
positive. -/
theorem pos_of_prod_pos (X : SemiPf (n + (1 + m))) (B : Basic (n + (1 + m)) X.r)
    {z : Fin (n + (1 + m)) → ℝ} (hpos : ∀ g ∈ B.pos, 0 ≤ eaEval X.c g z)
    (hprod : 0 < eaEval X.c B.pos.prod z) : ∀ g ∈ B.pos, 0 < eaEval X.c g z := by
  intro g hg
  rcases lt_or_eq_of_le (hpos g hg) with h | h
  · exact h
  · exfalso
    have hzero : eaEval X.c B.pos.prod z = 0 := by
      have h' : (B.pos.map (fun g' => eaEval X.c g' z)).prod = 0 := by
        rw [List.prod_eq_zero_iff]
        exact List.mem_map.mpr ⟨g, hg, h.symm⟩
      simpa only [eaEval, map_list_prod] using h'
    rw [hzero] at hprod
    exact lt_irrefl _ hprod

/-- **The maximiser of the weight on a component cut by a basic.** -/
theorem exists_maximiser (X : SemiPf (n + (1 + m))) (z₀ : Fin (n + (1 + m)) → ℝ)
    (hz₀ : z₀ ∈ X.set) (w : Fin (n + (1 + m)) → ℝ) (hw : w ∈ connectedComponentIn X.set z₀)
    (B : Basic (n + (1 + m)) X.r) (hBmem : B ∈ X.basics) (hB : B.holds X.c w)
    (c : Fin (1 + m) → ℝ) :
    ∃ w' : Fin (n + (1 + m)) → ℝ,
      w' ∈ connectedComponentIn (compFibre X z₀ (projBase (Nat.le_add_right n (1 + m)) w)) w ∧
      B.holds X.c w' ∧
      (∀ z, z ∈ connectedComponentIn (compFibre X z₀ (projBase (Nat.le_add_right n (1 + m)) w)) w →
        B.holds X.c z → weight X B c z ≤ weight X B c w') := by
  classical
  set x : Fin n → ℝ := projBase (Nat.le_add_right n (1 + m)) w with hx
  set K : Set (Fin (n + (1 + m)) → ℝ) := connectedComponentIn (compFibre X z₀ x) w with hK
  have hwbase : Fin.init (Work.WilE9.Sharp.stratProj w) = x := by
    rw [← projBase_eq_init_stratProj w]
  have hwcf : w ∈ compFibre X z₀ x := ⟨hw, hwbase⟩
  have hwK : w ∈ K := mem_connectedComponentIn hwcf
  set D : Set (Fin (n + (1 + m)) → ℝ) := K ∩ {z | B.holds X.c z} with hD
  have hwD : w ∈ D := ⟨hwK, hB⟩
  have hKsub : K ⊆ X.set := fun z hz =>
    connectedComponentIn_subset X.set z₀ (connectedComponentIn_subset (compFibre X z₀ x) w hz).1
  have hDcube : D ⊆ cubeC (n + (1 + m)) :=
    fun z hz => SemiPf_set_subset_cubeC X (hKsub hz.1)
  have hAcube : closure D ⊆ cubeC (n + (1 + m)) :=
    closure_minimal hDcube (isClosed_cubeC _)
  have hAcomp : IsCompact (closure D) :=
    (isCompact_cubeC _).of_isClosed_subset isClosed_closure hAcube
  obtain ⟨w', hw'A, hw'max⟩ := hAcomp.exists_isMaxOn ⟨w, subset_closure hwD⟩
    (continuous_weight X B c).continuousOn
  have hDsubeq : ∀ f ∈ B.eqs, D ⊆ {z | eaEval X.c f z = 0} := fun f hf z hz => hz.2.1 f hf
  have hDsubpos : ∀ g ∈ B.pos, D ⊆ {z | 0 ≤ eaEval X.c g z} :=
    fun g hg z hz => le_of_lt (hz.2.2 g hg)
  have heqs : ∀ f ∈ B.eqs, eaEval X.c f w' = 0 := fun f hf =>
    (isClosed_eq (lagStratum_continuous_eaEval X.c f) continuous_const).closure_subset
      (closure_mono (hDsubeq f hf) hw'A)
  have hpos : ∀ g ∈ B.pos, 0 ≤ eaEval X.c g w' := fun g hg =>
    (isClosed_le continuous_const (lagStratum_continuous_eaEval X.c g)).closure_subset
      (closure_mono (hDsubpos g hg) hw'A)
  have hmaxw : weight X B c w ≤ weight X B c w' := hw'max (subset_closure hwD)
  have hw'pos : 0 < weight X B c w' := lt_of_lt_of_le (weight_holds_pos X B c hB) hmaxw
  have hprod : 0 < eaEval X.c B.pos.prod w' := by
    rcases mul_pos_iff.mp hw'pos with h | h
    · exact h.1
    · exact absurd h.2 (not_lt.mpr (Real.exp_pos _).le)
  have hB' : B.holds X.c w' := ⟨heqs, pos_of_prod_pos X B hpos hprod⟩
  have hw'cube : w' ∈ cubeC (n + (1 + m)) := hAcube hw'A
  have hw'X : w' ∈ X.set := ⟨hw'cube, B, hBmem, hB'⟩
  have hw'clK : w' ∈ closure K := closure_mono Set.inter_subset_left hw'A
  have hKcomp : K ⊆ connectedComponentIn X.set z₀ := fun z hz =>
    (connectedComponentIn_subset (compFibre X z₀ x) w hz).1
  have hw'comp : w' ∈ connectedComponentIn X.set z₀ :=
    mem_of_mem_closure_of_mem_connectedComponentIn hz₀ (closure_mono hKcomp hw'clK) hw'X
  have hKbase : K ⊆ {z | projBase (Nat.le_add_right n (1 + m)) z = x} := fun z hz => by
    change projBase (Nat.le_add_right n (1 + m)) z = x
    rw [projBase_eq_init_stratProj z]
    exact (connectedComponentIn_subset (compFibre X z₀ x) w hz).2
  have hw'base : projBase (Nat.le_add_right n (1 + m)) w' = x :=
    closure_minimal hKbase
      (isClosed_eq (continuous_projBase' _) continuous_const) hw'clK
  have hw'init : Fin.init (Work.WilE9.Sharp.stratProj w') = x := by
    rw [← projBase_eq_init_stratProj w']
    exact hw'base
  have hw'cf : w' ∈ compFibre X z₀ x := ⟨hw'comp, hw'init⟩
  have hw'K : w' ∈ K := mem_of_mem_closure_of_mem_connectedComponentIn hwcf hw'clK hw'cf
  refine ⟨w', hw'K, hB', fun z hzK hzB => hw'max (subset_closure ⟨hzK, hzB⟩)⟩

end Work.WilE9G.Assembly
