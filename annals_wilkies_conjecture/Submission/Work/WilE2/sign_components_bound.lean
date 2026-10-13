import Mathlib
import Submission.Work.WilE2.atomSetDegree
import Submission.Work.WilE2.posVariety_pdist_bound
import Submission.Work.WilE2.VcbTopology
import Submission.Work.WilE2.card_le_card_of_hits
import Submission.Work.WilE2.coverBound_of_pdist_bound

set_option autoImplicit false

namespace Work.WilE2

open Classical
open WilkiesDesign WilkiesDesign.E

noncomputable section

/-!
  ## The sign-assignment step (Gabrielov–Vorobjov Thm 3.4 / Thm 3.7)

  Given `VarietyBound F` — a polynomial bound on the number of components of `{f = 0} ∩ cube` for
  every finite family of EA functions in format `≤ F` — we bound the number of components of a
  *basic* set `Z = cubeC k ∩ {f = 0} ∩ {g > 0}` by a polynomial in the degree datum `B.deg`, and
  produce a hitting set of those components inside `Z`.

  The argument has three parts.

  * The reduction `hits_of_atomSet_hits` (module `atomSetDefs`) turns the several-inequalities case
    into the single-atom set `atomSet c B = cubeC k ∩ {B.eqs = 0} ∩ {G > 0}`, `G = ∏ B.pos`.

  * The single-inequality case is `Work.WilE2.posVariety_pdist_bound`: adding *one* strict
    inequality to a variety costs only a polynomial factor in the degree datum.

  * `VarietyBound` supplies the variety bound, and the degree bookkeeping
    (`atomSet_degree_le`, `list_toFinset_sum_le`) shows that both the equation family and the level
    atoms fit below `B.deg + 1`.  The resulting "pairwise distinct components" bound is converted
    into a hitting set by `coverBound_of_pdist_bound` and `coverBound_hits`.
-/

/-- Monotonicity of `Polynomial.eval` at natural arguments. -/
theorem eval_mono_nat_deg {p : Polynomial ℕ} {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum fun k _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h k)

/-- Adding the level equation `G - δ` to a family does not increase the degree datum beyond
`∑ atomDeg f + atomDeg G`. -/
theorem sum_atomDeg_level_le {k r : ℕ} (f : Finset (EAPoly k r)) (G : EAPoly k r) (δ : ℝ) :
    (∑ h ∈ f ∪ {G - MvPolynomial.C δ}, atomDeg h) ≤ (∑ h ∈ f, atomDeg h) + atomDeg G := by
  have hset : f ∪ {G - MvPolynomial.C δ} = insert (G - MvPolynomial.C δ) f := by
    ext x
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
    tauto
  rw [hset]
  have h2 : (∑ h ∈ insert (G - MvPolynomial.C δ) f, atomDeg h) ≤
      (∑ h ∈ f, atomDeg h) + atomDeg (G - MvPolynomial.C δ) := by
    by_cases hmem : (G - MvPolynomial.C δ) ∈ f
    · rw [Finset.insert_eq_of_mem hmem]; omega
    · rw [Finset.sum_insert hmem]; omega
  linarith [h2, atomDeg_sub_C_le G δ]

/-- The single-atom set of a basic set with no positivity atom is the variety itself. -/
theorem atomSet_eq_Xset_of_pos_nil {k r : ℕ} (c : EAChain k r) (B : Basic k r)
    (hpos : B.pos = []) : atomSet c B = cubeC k ∩ Zset c B.eqs.toFinset := by
  have hG : posProd B = 1 := by simp [posProd, hpos]
  rw [atomSet_eq_posVarietySet c B, hG]
  ext x
  simp [eaEval_one]

theorem sign_components_bound (F : ℕ) (hvar : Work.WilE2.VarietyBound F) :
    ∃ p : Polynomial ℕ, ∀ (k r : ℕ) (c : WilkiesDesign.E.EAChain k r)
      (B : WilkiesDesign.E.Basic k r), k + r ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval (WilkiesDesign.E.Basic.deg B) ∧
        (↑s : Set (Fin k → ℝ)) ⊆
          WilkiesDesign.E.cubeC k ∩ {x | WilkiesDesign.E.Basic.holds c B x} ∧
        ∀ x ∈ WilkiesDesign.E.cubeC k ∩ {x | WilkiesDesign.E.Basic.holds c B x}, ∃ y ∈ s,
          connectedComponentIn
              (WilkiesDesign.E.cubeC k ∩ {x | WilkiesDesign.E.Basic.holds c B x}) x
            = connectedComponentIn
              (WilkiesDesign.E.cubeC k ∩ {x | WilkiesDesign.E.Basic.holds c B x}) y := by
  obtain ⟨p0, hp0⟩ := posVariety_pdist_bound F hvar
  obtain ⟨pvar, hpvar⟩ := hvar
  refine ⟨(pvar + p0).comp (Polynomial.X + Polynomial.C 1) + 1, ?_⟩
  intro k r c B hkr
  classical
  have hpeval : ∀ D : ℕ,
      ((pvar + p0).comp (Polynomial.X + Polynomial.C 1) + 1).eval D
        = pvar.eval (D + 1) + p0.eval (D + 1) + 1 := by
    intro D
    rw [Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_one]
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
  have hdeg_eq : Basic.deg B = (B.eqs.map atomDeg).sum + (B.pos.map atomDeg).sum := by
    rw [show Basic.deg B = ((B.eqs ++ B.pos).map atomDeg).sum from rfl, List.map_append,
      List.sum_append]
  have hpdistb : ∀ s : Finset (Fin k → ℝ), (↑s : Set (Fin k → ℝ)) ⊆ atomSet c B →
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y →
        connectedComponentIn (atomSet c B) x ≠ connectedComponentIn (atomSet c B) y) →
      s.card ≤ ((pvar + p0).comp (Polynomial.X + Polynomial.C 1) + 1).eval (Basic.deg B) := by
    intro s hs hdist
    rw [hpeval]
    by_cases hpos : B.pos = []
    · -- no positivity atom: the single-atom set is the variety itself
      have hset := atomSet_eq_Xset_of_pos_nil c B hpos
      obtain ⟨SV, hSVcard, hSVsub, hSVhits⟩ := hpvar k r c B.eqs.toFinset hkr
      have h1 : s.card ≤ SV.card :=
        card_le_card_of_hits hSVsub hSVhits (by rw [hset] at hs; exact hs)
          (by rw [hset] at hdist; exact hdist)
      have h3 : (∑ h ∈ B.eqs.toFinset, atomDeg h) ≤ (B.eqs.map atomDeg).sum :=
        list_toFinset_sum_le B.eqs atomDeg
      have h5 : (B.pos.map atomDeg).sum = 0 := by rw [hpos]; simp
      have h2 : pvar.eval (∑ h ∈ B.eqs.toFinset, atomDeg h) ≤ pvar.eval (Basic.deg B + 1) := by
        apply eval_mono_nat_deg
        rw [hdeg_eq, h5, add_zero]
        omega
      calc s.card ≤ SV.card := h1
        _ ≤ pvar.eval (∑ h ∈ B.eqs.toFinset, atomDeg h) := hSVcard
        _ ≤ pvar.eval (Basic.deg B + 1) := h2
        _ ≤ pvar.eval (Basic.deg B + 1) + p0.eval (Basic.deg B + 1) + 1 := by omega
    · -- the single-inequality bound
      have hseteq := atomSet_eq_posVarietySet c B
      have hs' : ∀ x ∈ s, x ∈ cubeC k ∩ Zset c B.eqs.toFinset ∩
          {x | 0 < eaEval c (posProd B) x} := by
        intro x hx
        rw [← hseteq]
        exact hs hx
      have hdist' : ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
          connectedComponentIn (cubeC k ∩ Zset c B.eqs.toFinset ∩
            {x | 0 < eaEval c (posProd B) x}) x ≠
          connectedComponentIn (cubeC k ∩ Zset c B.eqs.toFinset ∩
            {x | 0 < eaEval c (posProd B) x}) y := by
        intro x hx y hy hxy
        rw [← hseteq]
        exact hdist x hx y hy hxy
      have h := hp0 k r c B.eqs.toFinset (posProd B) hkr s hs' hdist'
      have hdeg := atomSet_degree_le B
      have h2 : p0.eval ((∑ h ∈ B.eqs.toFinset, atomDeg h) + atomDeg (posProd B)) ≤
          p0.eval (Basic.deg B + 1) := eval_mono_nat_deg hdeg
      calc s.card ≤ p0.eval ((∑ h ∈ B.eqs.toFinset, atomDeg h) + atomDeg (posProd B)) := h
        _ ≤ p0.eval (Basic.deg B + 1) := h2
        _ ≤ pvar.eval (Basic.deg B + 1) + p0.eval (Basic.deg B + 1) + 1 := by omega
  obtain ⟨S, hSsub, hScard, hShit⟩ :=
    coverBound_hits (coverBound_of_pdist_bound hpdistb)
  obtain ⟨s', hs'card, hs'sub, hs'hit⟩ := hits_of_atomSet_hits c B S hSsub hShit
  exact ⟨s', le_trans hs'card hScard, hs'sub, hs'hit⟩

end

end Work.WilE2
