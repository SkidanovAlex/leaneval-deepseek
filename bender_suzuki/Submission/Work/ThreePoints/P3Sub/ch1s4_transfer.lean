import Mathlib
import Submission.Work.DoubleTransitivity.Action

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints.P3Sub

/-!
# Transfer of 2-transitivity along the orbit map

The base set `S ⊆ G ⧸ H` is contained in (indeed, by `hSmul`/`htrans`, equal to) the
`L`-orbit of the coset of `1`.  Writing every element of `S` as `l • (1 : G ⧸ H)` with
`l : ↥L` identifies this orbit with the left-coset space `↥L ⧸ ((L ⊓ H).subgroupOf L)`:
the stabiliser of `1 : G ⧸ H` inside `L` is exactly `(L ⊓ H).subgroupOf L`.  The
identification is `L`-equivariant, so 2-pretransitivity of `L` on `↥L ⧸ ((L ⊓ H).subgroupOf L)`
transfers to 2-transitivity of `L` on `S`.
-/

/-- The two points `l₁ • 1` and `l₂ • 1` of the orbit of `1 : G ⧸ H` (under `L`) coincide
if and only if `l₁` and `l₂` lie in the same left coset modulo `(L ⊓ H).subgroupOf L`. -/
lemma smul_base_eq_iff {G : Type} [Group G] {H L : Subgroup G} (l1 l2 : ↥L) :
    ((l1 : G) • (QuotientGroup.mk (1 : G) : G ⧸ H) =
        (l2 : G) • (QuotientGroup.mk (1 : G) : G ⧸ H))
    ↔ ((QuotientGroup.mk l1 : ↥L ⧸ (L ⊓ H).subgroupOf L) = QuotientGroup.mk l2) := by
  rw [show (l1 : G) • (QuotientGroup.mk (1 : G) : G ⧸ H)
        = (QuotientGroup.mk (l1 : G) : G ⧸ H) from by simp,
      show (l2 : G) • (QuotientGroup.mk (1 : G) : G ⧸ H)
        = (QuotientGroup.mk (l2 : G) : G ⧸ H) from by simp]
  rw [QuotientGroup.eq, QuotientGroup.eq]
  rw [Subgroup.mem_subgroupOf]
  rw [Subgroup.mem_inf]
  constructor
  · intro h
    refine ⟨?_, h⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact mul_mem (inv_mem l1.property) l2.property
  · intro h
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h.2

theorem ch1s4_transfer {G : Type} [Group G] {H L : Subgroup G} {S : Set (G ⧸ H)}
    (h2 : MulAction.IsMultiplyPretransitive ↥L (↥L ⧸ (L ⊓ H).subgroupOf L) 2)
    (h1S : (QuotientGroup.mk (1 : G) : G ⧸ H) ∈ S)
    (hSmul : ∀ l : L, ∀ ω ∈ S, (l : G) • ω ∈ S)
    (htrans : ∀ ω ∈ S, ∃ l : L, (l : G) • (QuotientGroup.mk (1 : G) : G ⧸ H) = ω) :
    Work.DoubleTransitivity.IsTwoTransitiveOnSub L S := by
  intro c hc d hd hcd c' hc' d' hd' hcd'
  obtain ⟨lc, hlc⟩ := htrans c hc
  obtain ⟨ld, hld⟩ := htrans d hd
  obtain ⟨lc', hlc'⟩ := htrans c' hc'
  obtain ⟨ld', hld'⟩ := htrans d' hd'
  have hne1 : (QuotientGroup.mk lc : ↥L ⧸ (L ⊓ H).subgroupOf L) ≠ QuotientGroup.mk ld := by
    intro h
    apply hcd
    rw [← hlc, ← hld]
    exact (smul_base_eq_iff lc ld).mpr h
  have hne2 : (QuotientGroup.mk lc' : ↥L ⧸ (L ⊓ H).subgroupOf L) ≠ QuotientGroup.mk ld' := by
    intro h
    apply hcd'
    rw [← hlc', ← hld']
    exact (smul_base_eq_iff lc' ld').mpr h
  obtain ⟨g, hg1, hg2⟩ := (MulAction.is_two_pretransitive_iff.mp h2) hne1 hne2
  refine ⟨(g : G), g.property, ?_, ?_⟩
  · have hg1' : (QuotientGroup.mk (g * lc) : ↥L ⧸ (L ⊓ H).subgroupOf L)
        = QuotientGroup.mk lc' := by
      rw [← hg1, MulAction.Quotient.smul_mk, smul_eq_mul]
    rw [← hlc, ← hlc']
    calc (g : G) • ((lc : G) • (QuotientGroup.mk (1 : G) : G ⧸ H))
        = ((g : G) * (lc : G)) • (QuotientGroup.mk (1 : G) : G ⧸ H) := by rw [mul_smul]
      _ = (((g * lc : ↥L) : G)) • (QuotientGroup.mk (1 : G) : G ⧸ H) := by
            simp only [Subgroup.coe_mul]
      _ = (lc' : G) • (QuotientGroup.mk (1 : G) : G ⧸ H) := (smul_base_eq_iff (g * lc) lc').mpr hg1'
  · have hg2' : (QuotientGroup.mk (g * ld) : ↥L ⧸ (L ⊓ H).subgroupOf L)
        = QuotientGroup.mk ld' := by
      rw [← hg2, MulAction.Quotient.smul_mk, smul_eq_mul]
    rw [← hld, ← hld']
    calc (g : G) • ((ld : G) • (QuotientGroup.mk (1 : G) : G ⧸ H))
        = ((g : G) * (ld : G)) • (QuotientGroup.mk (1 : G) : G ⧸ H) := by rw [mul_smul]
      _ = (((g * ld : ↥L) : G)) • (QuotientGroup.mk (1 : G) : G ⧸ H) := by
            simp only [Subgroup.coe_mul]
      _ = (ld' : G) • (QuotientGroup.mk (1 : G) : G ⧸ H) := (smul_base_eq_iff (g * ld) ld').mpr hg2'

end Work.ThreePoints.P3Sub
