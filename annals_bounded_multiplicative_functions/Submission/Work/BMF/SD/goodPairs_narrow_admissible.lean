import Mathlib
import Submission.Work.BMF.SD.sd3_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

/-- Arithmetic core. If a source `q₁` is large relative to `X` (`q₁ ≥ (1+ρ)X/10`) and the
prime `q₂ ≥ 1` satisfies `q₂ ≤ b' ≤ (1+ρ)a'` with `a' > 0`, `X ≥ 0`, then the rescaled
point `q₁/q₂` is still at least `X/(10 a')`. -/
lemma div_ge_of_bounds {q1 : ℝ} {q2 : ℕ} {X ρ a' b' : ℝ}
    (ha' : 0 < a') (hX : 0 ≤ X)
    (hb' : b' ≤ (1 + ρ) * a') (hq1 : (1 + ρ) * X / 10 ≤ q1)
    (hq2 : 0 < (q2 : ℝ)) (hq2b : (q2 : ℝ) ≤ b') :
    X / (10 * a') ≤ q1 / (q2 : ℝ) := by
  have hXa : 0 ≤ X / (10 * a') := div_nonneg hX (by positivity)
  have h1 : X / (10 * a') * (q2 : ℝ) ≤ X / (10 * a') * b' :=
    mul_le_mul_of_nonneg_left hq2b hXa
  have h2 : X / (10 * a') * b' ≤ X / (10 * a') * ((1 + ρ) * a') :=
    mul_le_mul_of_nonneg_left hb' hXa
  have h3 : X / (10 * a') * ((1 + ρ) * a') = (1 + ρ) * X / 10 := by
    field_simp
  have key : X / (10 * a') * (q2 : ℝ) ≤ q1 := by
    have h4 := le_trans h1 (le_trans h2 (le_of_eq h3))
    linarith
  rw [le_div_iff₀ hq2]
  exact key

/-- The `goodPairs` on a narrow source family `S` (all sources `≥ (1+ρ)X/10`) sit inside those
on a larger family `T`, restricted to rescaled points `q.1/q.2 ≥ X/(10 a')`: a good pair over `S`
has source `≥ (1+ρ)X/10` and prime `≤ b' ≤ (1+ρ)a'`, so its ratio is at least `X/(10a')`. -/
theorem goodPairs_narrow_admissible {f : ℕ → ℂ} {pol : ℝ → Polynomial ℝ} {η H X ρ a' b' : ℝ}
    {S T : Finset ℝ} (hST : S ⊆ T) (hρ : 0 < ρ) (hX : 0 < X) (ha' : 0 < a')
    (hb' : b' ≤ (1 + ρ) * a') (hlow : ∀ y ∈ S, (1 + ρ) * X / 10 ≤ y) :
    Work.BMF.goodPairs f pol η H a' b' S ⊆
      (Work.BMF.goodPairs f pol η H a' b' T).filter
        (fun q => X / (10 * a') ≤ q.1 / (q.2 : ℝ)) := by
  intro q hq
  rw [Work.BMF.mem_goodPairs] at hq
  obtain ⟨hyS, hp, hcond⟩ := hq
  rw [Finset.mem_filter, Work.BMF.mem_goodPairs]
  refine ⟨⟨hST hyS, hp, hcond⟩, ?_⟩
  have hp' : q.2 ∈ (Finset.Icc ⌈a'⌉₊ ⌊b'⌋₊).filter Nat.Prime := by
    simpa [Work.BMF.primesIn, Work.BMF.natIcc] using hp
  obtain ⟨hIcc, hprime⟩ := Finset.mem_filter.mp hp'
  obtain ⟨_, huppq2⟩ := Finset.mem_Icc.mp hIcc
  have hq2pos : (0 : ℝ) < (q.2 : ℝ) := by exact_mod_cast hprime.pos
  have hfloor2 : 0 < ⌊b'⌋₊ := by
    have := hprime.two_le
    omega
  have hb'pos : (0 : ℝ) ≤ b' := by
    have h1 : (1 : ℝ) ≤ b' := (Nat.floor_pos).mp hfloor2
    linarith
  have hq2b : (q.2 : ℝ) ≤ b' := (Nat.le_floor_iff hb'pos).mp huppq2
  exact div_ge_of_bounds ha' hX.le hb' (hlow q.1 hyS) hq2pos hq2b

end Work.BMF.SD
