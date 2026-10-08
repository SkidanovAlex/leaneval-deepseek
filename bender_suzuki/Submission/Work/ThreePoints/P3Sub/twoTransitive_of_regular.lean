import Mathlib
import Submission.Work.DoubleTransitivity.Action

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints.P3Sub

open Work.DoubleTransitivity

/-- If `F` acts transitively on `S`, stabilises `S`, fixes `a`, and contains a subgroup `Z`
that fixes `a` and is transitive on `S \ {a}`, then `F` acts 2-transitively on `S`.

Concretely:

* `F_a` is transitive on `S \ {a}`, because `Z ≤ F_a` and `Z` is transitive on `S \ {a}`;
* hence, conjugating by an element carrying `a` to `x`, each point stabiliser `F_x`
  (`x ∈ S`) is transitive on `S \ {x}`;
* combine: move the first point with `F`, then move the second with the stabiliser of the
  image of the first point. -/
theorem twoTransitive_of_regular {G E : Type} [Group G] [MulAction G E]
    (F Z : Subgroup G) (S : Set E) (a : E)
    (ha : a ∈ S)
    (hFstable : ∀ f ∈ F, ∀ x ∈ S, f • x ∈ S)
    (hZle : Z ≤ F)
    (hZa : Z ≤ MulAction.stabilizer G a)
    (hZtr : ∀ c ∈ S, c ≠ a → ∀ d ∈ S, d ≠ a → ∃ z ∈ Z, z • c = d)
    (htrans : ∀ x ∈ S, ∃ f ∈ F, f • a = x) :
    Work.DoubleTransitivity.IsTwoTransitiveOnSub F S := by
  -- `F_a` is transitive on `S \ {a}`.
  have hFa : ∀ x ∈ S, x ≠ a → ∀ y ∈ S, y ≠ a → ∃ f ∈ F, f • a = a ∧ f • x = y := by
    intro x hx hxa y hy hya
    obtain ⟨z, hz, hzx⟩ := hZtr x hx hxa y hy hya
    exact ⟨z, hZle hz, (MulAction.mem_stabilizer_iff).mp (hZa hz), hzx⟩
  -- `F` is transitive on `S`.
  have htrans' : ∀ x ∈ S, ∀ y ∈ S, ∃ f ∈ F, f • x = y := by
    intro x hx y hy
    obtain ⟨fx, hfx, hfxa⟩ := htrans x hx
    obtain ⟨fy, hfy, hfya⟩ := htrans y hy
    exact ⟨fy * fx⁻¹, F.mul_mem hfy (F.inv_mem hfx), by
      rw [mul_smul, ← hfxa, inv_smul_smul, hfya]⟩
  -- The point stabiliser `F_x` is transitive on `S \ {x}` for every `x ∈ S`.
  have hstab : ∀ x ∈ S, ∀ u ∈ S, u ≠ x → ∀ v ∈ S, v ≠ x →
      ∃ f ∈ F, f • x = x ∧ f • u = v := by
    intro x hx u hu hux v hv hvx
    obtain ⟨g, hg, hga⟩ := htrans x hx
    have hu' : g⁻¹ • u ∈ S := hFstable g⁻¹ (F.inv_mem hg) u hu
    have hu'ne : g⁻¹ • u ≠ a := by
      intro h
      apply hux
      calc u = g • (g⁻¹ • u) := (smul_inv_smul g u).symm
        _ = g • a := by rw [h]
        _ = x := hga
    have hv' : g⁻¹ • v ∈ S := hFstable g⁻¹ (F.inv_mem hg) v hv
    have hv'ne : g⁻¹ • v ≠ a := by
      intro h
      apply hvx
      calc v = g • (g⁻¹ • v) := (smul_inv_smul g v).symm
        _ = g • a := by rw [h]
        _ = x := hga
    obtain ⟨k, hk, hka, hkuv⟩ := hFa (g⁻¹ • u) hu' hu'ne (g⁻¹ • v) hv' hv'ne
    refine ⟨g * k * g⁻¹, F.mul_mem (F.mul_mem hg hk) (F.inv_mem hg), ?_, ?_⟩
    · rw [mul_smul, mul_smul, ← hga, inv_smul_smul, hka, hga]
    · rw [mul_smul, mul_smul, hkuv, smul_inv_smul]
  intro c hc d hd hcd c' hc' d' hd' hc'd'
  -- Move `c` to `c'`.
  obtain ⟨p, hp, hpc⟩ := htrans' c hc c' hc'
  -- `p • d` is again in `S` and different from `c'`.
  have hpd : p • d ∈ S := hFstable p hp d hd
  have hpdne : p • d ≠ c' := by
    intro h
    have h1 : p • d = p • c := by rw [h, hpc]
    have h2 : d = c := by
      have := congrArg (fun z => p⁻¹ • z) h1
      simpa using this
    exact hcd h2.symm
  -- Fix `c'` while moving `p • d` to `d'`.
  obtain ⟨f, hf, hfc', hfe⟩ := hstab c' hc' (p • d) hpd hpdne d' hd' hc'd'.symm
  exact ⟨f * p, F.mul_mem hf hp, by rw [mul_smul, hpc, hfc'], by rw [mul_smul, hfe]⟩

end Work.ThreePoints.P3Sub
