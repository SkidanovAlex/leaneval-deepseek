import Mathlib
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.stabParabOrEllip
import Submission.Work.Mostow.stabFlatActionCanon
import Submission.Work.Mostow.flatLinNorm
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.boundedOrbitFixed
import Submission.Work.Mostow.properAction
import Submission.Work.Mostow.cuspZ2
import Submission.Work.Mostow.bieberbach

namespace Work.Mostow

/-! # Auxiliary material for the elliptic rotation gap -/


open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped Topology

noncomputable section

variable {n : ℕ}

/-- The stabiliser of the boundary point `ξ` inside `Γ`, as a subgroup of `PO n 1`. -/
def xiStab (Γ : Subgroup (PO n 1)) (ξ : E n) (hA : POActionProp n) (hξ : ξ ∈ Sph n) :
    Subgroup (PO n 1) where
  carrier := {g | g ∈ Γ ∧ bd g ξ = ξ}
  mul_mem' := by
    intro a b ha hb
    obtain ⟨-, -, -, -, -, -, -, -, -, hbdmul, -, -⟩ := hA
    exact ⟨Γ.mul_mem ha.1 hb.1, by rw [hbdmul a b ξ hξ, hb.2, ha.2]⟩
  one_mem' := by
    obtain ⟨-, -, -, -, -, -, -, -, hbdone, -, -, -⟩ := hA
    exact ⟨Γ.one_mem, hbdone ξ hξ⟩
  inv_mem' := by
    intro a ha
    obtain ⟨-, -, -, -, -, -, -, -, hbdone, hbdmul, -, -⟩ := hA
    refine ⟨Γ.inv_mem ha.1, ?_⟩
    have h := hbdmul a⁻¹ a ξ hξ
    rw [inv_mul_cancel, hbdone ξ hξ, ha.2] at h
    exact h.symm

@[simp] lemma mem_xiStab {Γ : Subgroup (PO n 1)} {ξ : E n} {hA : POActionProp n}
    {hξ : ξ ∈ Sph n} {g : PO n 1} : g ∈ xiStab Γ ξ hA hξ ↔ g ∈ Γ ∧ bd g ξ = ξ := Iff.rfl

/-- The action of a discrete subgroup of `PO n 1` on `ℍⁿ` is proper: for a compact `K` and a
point `u₀`, the set of `γ ∈ Γ` with `γ • u₀ ∈ K` is finite. -/
theorem finite_smul_mem_compact (hA : POActionProp n) (hI : HypIsometryProp n)
    {Γ : Subgroup (PO n 1)} (hdisc : IsDiscrete (SetLike.coe Γ)) (u₀ : E n) {K : Set (E n)}
    (hK : IsCompact K) : {γ : Γ | (γ : PO n 1) • u₀ ∈ K}.Finite := by
  have hId : HypIsoData n := HypIsoData.ofProp hI
  have hdl : ∀ (x : E n) (M : ℝ), ‖x‖ ≤ M →
      hdist (0 : E n) x ≤ Real.arcosh (Real.sqrt (1 + M ^ 2)) := by
    intro x M hx
    have h0 : hdist (0 : E n) x = Real.arcosh (tpart x) := by rw [hdist]; simp [tpart]
    rw [h0]
    rw [Real.arcosh_le_arcosh (tpart_pos x) (Real.sqrt_pos.2 (by nlinarith [sq_nonneg M]))]
    rw [tpart]
    apply Real.sqrt_le_sqrt
    nlinarith [hx, norm_nonneg x, sq_nonneg (M - ‖x‖)]
  by_cases hne : K.Nonempty
  · obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x ∈ K, ‖x‖ ≤ M := exists_norm_le_of_isCompact hK
    set R : ℝ := Real.arcosh (Real.sqrt (1 + M ^ 2)) + hdist (0 : E n) u₀ with hRdef
    refine (finite_nearStab (POBasic.ofProp hA) (HypIsoData.ofProp hI) hdisc R).subset ?_
    intro γ hγ
    have hx : ‖(γ : PO n 1) • u₀‖ ≤ M := hM _ hγ
    have hstep1 : hdist (0 : E n) ((γ : PO n 1) • u₀) ≤ Real.arcosh (Real.sqrt (1 + M ^ 2)) :=
      hdl _ M hx
    have hstep2 : hdist ((γ : PO n 1) • u₀) ((γ : PO n 1) • (0 : E n)) = hdist u₀ (0 : E n) :=
      hId.isom_smul _ _ _
    have htri := hId.triangle (0 : E n) ((γ : PO n 1) • u₀) ((γ : PO n 1) • (0 : E n))
    show hdist (0 : E n) ((γ : PO n 1) • (0 : E n)) ≤ R
    calc hdist (0 : E n) ((γ : PO n 1) • (0 : E n))
        ≤ hdist (0 : E n) ((γ : PO n 1) • u₀) +
            hdist ((γ : PO n 1) • u₀) ((γ : PO n 1) • (0 : E n)) := htri
      _ = hdist (0 : E n) ((γ : PO n 1) • u₀) + hdist u₀ (0 : E n) := by rw [hstep2]
      _ ≤ Real.arcosh (Real.sqrt (1 + M ^ 2)) + hdist (0 : E n) u₀ := by
            rw [hId.symm u₀ (0 : E n)]; linarith [hstep1]
      _ = R := by rw [hRdef]
  · have hKe : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [hKe]
    exact Set.finite_empty

/-- Elements of the stabiliser of `ξ` inside `Γ` preserve the horosphere levels at `ξ`
(they have vanishing Busemann cocycle by `hvan`). -/
lemma xiStab_lev (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1))
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ parFixed Γ → bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0)
    (ξ : E n) (hξ : ξ ∈ parFixed Γ) (g : xiStab Γ ξ hA hξ.1) :
    ∀ u : E n, lev ξ ((g : PO n 1) • u) = lev ξ u := by
  intro u
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  have hb : bCocy (g : PO n 1) ξ = 0 := hvan ⟨(g : PO n 1), g.2.1⟩ ξ hξ g.2.2
  have h := hI'.busemann_cocycle (g : PO n 1) ξ u hξ.1
  rw [g.2.2] at h
  have hb' : busemann ξ ((g : PO n 1) • (0 : E n)) = 0 := by
    simpa only [bCocy, g.2.2] using hb
  rw [hb', add_zero] at h
  rw [lev_eq_exp hξ.1 ((g : PO n 1) • u), lev_eq_exp hξ.1 u, h]
