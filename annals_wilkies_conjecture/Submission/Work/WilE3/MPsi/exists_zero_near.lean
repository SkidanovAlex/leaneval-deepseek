import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE3.Defs

namespace Work.WilE3.MPsi

open Classical Topology Filter
open WilkiesDesign.E

/-- Auxiliary: the evaluation `eaEval c Q` of an EA polynomial is continuous in the point.  It is
the composition of `MvPolynomial.eval` with the continuous map
`x ↦ Sum.elim x (fun j => exp (ℓ_j x))`. -/
theorem ezn_continuous_eaEval {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r) :
    Continuous fun x : Fin k → ℝ => eaEval c Q x := by
  apply (MvPolynomial.continuous_eval Q).comp
  refine continuous_pi (fun s => ?_)
  cases s with
  | inl i => simpa using (continuous_apply i : Continuous fun x : Fin k → ℝ => x i)
  | inr j => exact Real.continuous_exp.comp (by unfold EAChain.ell; fun_prop)

/-- Auxiliary: the common zero set of a finite list of continuous equations is closed.  The list is
consumed by induction on its head. -/
theorem ezn_isClosed_zeroSet {k r : ℕ} (c : EAChain k r) (eqs : List (EAPoly k r)) :
    IsClosed {x : Fin k → ℝ | ∀ f ∈ eqs, eaEval c f x = 0} := by
  induction eqs with
  | nil => simp
  | cons a L ih =>
    have h : {x : Fin k → ℝ | ∀ f ∈ a :: L, eaEval c f x = 0}
        = {x : Fin k → ℝ | eaEval c a x = 0} ∩
          {x : Fin k → ℝ | ∀ f ∈ L, eaEval c f x = 0} := by
      ext x
      constructor
      · intro hx
        exact ⟨hx a (by simp), fun f hf => hx f (by simp [hf])⟩
      · rintro ⟨ha, hL⟩ f hf
        rcases List.mem_cons.mp hf with rfl | hf
        · exact ha
        · exact hL f hf
    rw [h]
    exact (isClosed_eq (ezn_continuous_eaEval c a) continuous_const).inter ih

/-- The residual Łojasiewicz inequality `HasLoj` for the equations of `B` at a point `y` of their
common zero set gives, near `y`, a point of the zero set at distance controlled by the residual:
`dist z' z ^ q ≤ C * ∑ |f z|`.  (Namespace `Work.WilE3.MPsi`.)
`Z = {x | ∀ f ∈ eqs, eaEval c f x = 0}` is closed and contains `y`, so
`IsClosed.exists_infDist_eq_dist` produces `z'` with `dist z' z = infDist z Z`. -/
theorem exists_zero_near {k r : ℕ} (c : EAChain k r) (eqs : List (EAPoly k r)) (y : Fin k → ℝ) (q : ℕ)
    (hq : 0 < q)
    (hL : Work.WilE3.HasLoj (fun x => (eqs.map fun f => |eaEval c f x|).sum)
      {x | ∀ f ∈ eqs, eaEval c f x = 0} y q)
    (hy : ∀ f ∈ eqs, eaEval c f y = 0) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ z : Fin k → ℝ, dist z y < δ →
      ∃ z' : Fin k → ℝ, (∀ f ∈ eqs, eaEval c f z' = 0) ∧
        dist z' z ^ q ≤ C * (eqs.map fun f => |eaEval c f z|).sum := by
  obtain ⟨C₀, hC₀pos, hC₀ev⟩ := hL
  -- the Łojasiewicz inequality holds on a ball of radius `δ` around `y`
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hC₀ev
  -- `Z` is closed and contains `y`, so the point of `Z` nearest to `z` exists
  have hZclosed : IsClosed {x : Fin k → ℝ | ∀ f ∈ eqs, eaEval c f x = 0} :=
    ezn_isClosed_zeroSet c eqs
  have hZne : ({x : Fin k → ℝ | ∀ f ∈ eqs, eaEval c f x = 0} : Set (Fin k → ℝ)).Nonempty :=
    ⟨y, hy⟩
  refine ⟨C₀⁻¹, δ, inv_pos.mpr hC₀pos, hδpos, fun z hz => ?_⟩
  have hres : (0 : ℝ) ≤ (eqs.map fun f => |eaEval c f z|).sum :=
    List.sum_nonneg fun b hb => by
      obtain ⟨d, -, rfl⟩ := List.mem_map.mp hb
      exact abs_nonneg _
  obtain ⟨z', hz'Z, hdist⟩ := hZclosed.exists_infDist_eq_dist hZne z
  refine ⟨z', hz'Z, ?_⟩
  have hdist' : dist z' z = Metric.infDist z {x : Fin k → ℝ | ∀ f ∈ eqs, eaEval c f x = 0} := by
    rw [hdist, dist_comm]
  have h1 : C₀ * Metric.infDist z {x : Fin k → ℝ | ∀ f ∈ eqs, eaEval c f x = 0} ^ q ≤
      (eqs.map fun f => |eaEval c f z|).sum := by
    have h := hδ hz
    rwa [abs_of_nonneg hres] at h
  calc dist z' z ^ q
      = Metric.infDist z {x : Fin k → ℝ | ∀ f ∈ eqs, eaEval c f x = 0} ^ q := by rw [hdist']
    _ ≤ C₀⁻¹ * (eqs.map fun f => |eaEval c f z|).sum :=
        (le_inv_mul_iff₀ hC₀pos).mpr h1

end Work.WilE3.MPsi
