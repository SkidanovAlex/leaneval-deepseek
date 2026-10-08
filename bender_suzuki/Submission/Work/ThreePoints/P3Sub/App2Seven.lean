import Mathlib
import Submission.Work.DoubleTransitivity.Action

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Peterfalvi, Appendix II (7) — the first assertion

The source (Peterfalvi I, Appendix II (7), p. 204): if `X` acts on `E`, `H = X_a`, `D = X_a ∩ X_b`
has a normal complement `Q` in `H`, and `Y ≤ D` fixes at least three points, then `C_Q(Y)` acts
regularly on `E_Y \ {a}`.

This module proves the *regularity* assertion (the only part of App. II (7) used by
`Work.ThreePoints.P3Sub`), in the following slightly more general form: `E0 ⊆ E` is a set (the
`N`-orbit of `a` in the applications), `Q` acts sharply transitively from `b` onto
`E0 \ {a}`, `Q ⊴ N ∩ H`, and `Y ≤ D ∩ N`; then `C_Q(Y)` acts regularly on `E_Y \ {a}`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThreePoints

open Work.DoubleTransitivity

variable {G E : Type} [Group G] [MulAction G E]

theorem app2_7 [Fintype E] {E0 : Set E} {a b : E} (ha : a ∈ E0) (hb : b ∈ E0) (hab : a ≠ b)
    {N Q D Y : Subgroup G}
    (hQa : Q ≤ MulAction.stabilizer G a)
    (hQn : N ⊓ MulAction.stabilizer G a ≤ Subgroup.normalizer (Q : Set G))
    (hreg : ∀ c ∈ E0 \ ({a} : Set E), ∃! q : ↥Q, (q : G) • b = c)
    (hD : D ≤ MulAction.stabilizer G a ⊓ MulAction.stabilizer G b)
    (hY : Y ≤ MulAction.stabilizer G a ⊓ MulAction.stabilizer G b)
    (hYN : Y ≤ N)
    (hYE0 : (fixedBySub Y : Set E) ⊆ E0) :
    IsRegularOnSub (Q ⊓ Subgroup.centralizer (Y : Set G))
      ((fixedBySub Y : Set E) \ ({a} : Set E)) := by
  classical
  set Z : Subgroup G := Q ⊓ Subgroup.centralizer (Y : Set G) with hZdef
  -- `b` is fixed by `Y`, and `b ∈ E0 \ {a}`
  have hbY : b ∈ (fixedBySub Y : Set E) :=
    mem_fixedBySub.mpr fun z hz => MulAction.mem_stabilizer_iff.mp ((le_inf_iff.mp hY).2 hz)
  have hbE0 : b ∈ E0 \ ({a} : Set E) := ⟨hb, by simpa using hab.symm⟩
  have hbS : b ∈ (fixedBySub Y : Set E) \ ({a} : Set E) := ⟨hbY, by simpa using hab.symm⟩
  -- uniqueness of the element of `Q` carrying `b` to a given point of `E0 \ {a}`
  have huniq : ∀ c ∈ E0 \ ({a} : Set E), ∀ q₁ : ↥Q, ∀ q₂ : ↥Q,
      (q₁ : G) • b = c → (q₂ : G) • b = c → q₁ = q₂ := by
    intro c hc q₁ q₂ h₁ h₂
    obtain ⟨q, -, hq⟩ := hreg c hc
    rw [hq q₁ h₁, hq q₂ h₂]
  -- such an element centralises `Y`
  have hmemZ : ∀ c ∈ E0 \ ({a} : Set E), c ∈ (fixedBySub Y : Set E) → ∀ q : ↥Q,
      (q : G) • b = c → (q : G) ∈ Z := by
    intro c hc hcfix q hqb
    refine Subgroup.mem_inf.mpr ⟨q.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyN : y ∈ N := hYN hy
    have hya : y ∈ MulAction.stabilizer G a := (le_inf_iff.mp hY).1 hy
    have hyb : y • b = b := MulAction.mem_stabilizer_iff.mp ((le_inf_iff.mp hY).2 hy)
    have hyQ : y ∈ Subgroup.normalizer (Q : Set G) := hQn ⟨hyN, hya⟩
    have hconj : y * (q : G) * y⁻¹ ∈ Q :=
      ((Subgroup.mem_set_normalizer_iff.mp hyQ) (q : G)).mp q.2
    have hcY : y • c = c := mem_fixedBySub.mp hcfix y hy
    have hyinv : y⁻¹ • b = b := by
      calc y⁻¹ • b = y⁻¹ • (y • b) := by rw [hyb]
        _ = b := inv_smul_smul y b
    have hval : (y * (q : G) * y⁻¹) • b = c := by
      rw [mul_smul, mul_smul, hyinv, hqb, hcY]
    have heq : y * (q : G) * y⁻¹ = (q : G) :=
      congrArg Subtype.val (huniq c hc ⟨y * (q : G) * y⁻¹, hconj⟩ q hval hqb)
    have hcomm : y * (q : G) = (q : G) * y := by
      have h := congrArg (fun t : G => t * y) heq
      simpa [mul_assoc] using h
    exact hcomm
  constructor
  · -- `C_Q(Y)` is transitive on `E_Y \ {a}`
    intro c hc d hd
    have hcE : c ∈ E0 \ ({a} : Set E) := ⟨hYE0 hc.1, hc.2⟩
    have hdE : d ∈ E0 \ ({a} : Set E) := ⟨hYE0 hd.1, hd.2⟩
    obtain ⟨qc, hqc, hqcu⟩ := hreg c hcE
    obtain ⟨qd, hqd, hqdu⟩ := hreg d hdE
    have hqcZ : (qc : G) ∈ Z := hmemZ c hcE hc.1 qc hqc
    have hqdZ : (qd : G) ∈ Z := hmemZ d hdE hd.1 qd hqd
    refine ⟨(qd : G) * (qc : G)⁻¹, Z.mul_mem hqdZ (Z.inv_mem hqcZ), ?_⟩
    show ((qd : G) * (qc : G)⁻¹) • c = d
    have h1 : (qc : G)⁻¹ • c = b := by
      rw [← hqc]
      exact inv_smul_smul (qc : G) b
    rw [mul_smul, h1, hqd]
  · -- `C_Q(Y)` acts freely on `E_Y \ {a}`
    intro z hz hfix
    have hzQ : z ∈ Q := (Subgroup.mem_inf.mp hz).1
    have h := huniq b hbE0 ⟨z, hzQ⟩ 1 (hfix b hbS) (one_smul G b)
    exact congrArg Subtype.val h

end Work.ThreePoints
