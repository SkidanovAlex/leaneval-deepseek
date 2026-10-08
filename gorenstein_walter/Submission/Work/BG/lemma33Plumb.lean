import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.S_le_H
import Submission.Work.GLUE.Defs

/-!
# Area BG: plumbing for the first case of Bender–Glauberman Lemma 3.3

The conjugation action of the Sylow `2`-subgroup `D.S` on `U = O(H)`, its fixed-point
subgroup `C_U(S)`, and the elementary facts about them used by `Work.BG.lemma33Case1`.

Everything lives in the namespace `Work.BG.L33` so that it can be imported alongside other
attempts at Lemma 3.3 without name clashes.
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG

namespace L33

variable {G : Type} [Group G] [Finite G]

/-- `D.H` normalizes `D.U = O(D.H)`. -/
theorem H_le_normalizer_U (D : BGData G) : D.H ≤ Subgroup.normalizer D.U := by
  have fwd : ∀ (g : G), g ∈ D.H → ∀ x ∈ D.U, g * x * g⁻¹ ∈ D.U := by
    intro g hg x hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have hconj : (⟨g, hg⟩ : ↥D.H) * y * (⟨g, hg⟩ : ↥D.H)⁻¹ ∈ Work.GW2.oddCore D.H :=
      (inferInstance : (Work.GW2.oddCore D.H).Normal).conj_mem y hy (⟨g, hg⟩ : ↥D.H)
    rw [← hyx]
    exact Subgroup.mem_map.mpr
      ⟨(⟨g, hg⟩ : ↥D.H) * y * (⟨g, hg⟩ : ↥D.H)⁻¹, hconj, rfl⟩
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fwd h hh x
  · intro hx
    have h2 : h⁻¹ * (h * x * h⁻¹) * h ∈ D.U := by
      have h3 := fwd h⁻¹ (D.H.inv_mem hh) (h * x * h⁻¹) hx
      simpa using h3
    have heq : h⁻¹ * (h * x * h⁻¹) * h = x := by group
    rwa [heq] at h2

/-- Conjugation by an element of `D.S` preserves `D.U`. -/
theorem S_conj_mem_U (D : BGData G) {s x : G} (hs : s ∈ (D.S : Subgroup G)) (hx : x ∈ D.U) :
    s * x * s⁻¹ ∈ D.U := by
  have hsH : s ∈ D.H := S_le_H D hs
  have hnorm : s ∈ Subgroup.normalizer D.U := H_le_normalizer_U D hsH
  rw [Subgroup.mem_normalizer_iff] at hnorm
  exact (hnorm x).mp hx

/-- Conjugation by `s ∈ D.S` as an automorphism of `↥D.U`. -/
noncomputable def conjAutU (D : BGData G) (s : G) (hs : s ∈ (D.S : Subgroup G)) :
    MulAut ↥D.U where
  toFun u := ⟨s * (u : G) * s⁻¹, S_conj_mem_U D hs u.2⟩
  invFun u := ⟨s⁻¹ * (u : G) * s, by
    have h3 := S_conj_mem_U D (inv_mem hs : s⁻¹ ∈ (D.S : Subgroup G)) u.2
    simpa using h3⟩
  left_inv u := by
    refine Subtype.ext ?_
    simp only [Subtype.coe_mk]
    group
  right_inv u := by
    refine Subtype.ext ?_
    simp only [Subtype.coe_mk]
    group
  map_mul' u v := by
    refine Subtype.ext ?_
    simp only [Subtype.coe_mk, Subgroup.coe_mul]
    group

/-- The conjugation action of the Sylow `2`-subgroup `D.S` on `D.U = O(D.H)`. -/
noncomputable def phiS (D : BGData G) : ↥D.S →* MulAut ↥D.U where
  toFun s := conjAutU D (s : G) s.2
  map_one' := by
    ext u
    simp [conjAutU]
  map_mul' a b := by
    ext u
    show ((a * b : ↥D.S) : G) * (u : G) * (((a * b : ↥D.S) : G))⁻¹
      = ((a : G) * ((b : G) * (u : G) * (b : G)⁻¹) * (a : G)⁻¹)
    rw [Subgroup.coe_mul]
    group

/-- Unfolding of the action: `φ s` is conjugation by `s` in `G`. -/
theorem phiS_apply (D : BGData G) (s : ↥D.S) (u : ↥D.U) :
    ((phiS D s u : ↥D.U) : G) = (s : G) * (u : G) * (s : G)⁻¹ := rfl

/-- The fixed points of the `S`-action are `C_U(S)`. -/
theorem mem_fixedSubgroupS_phiS (D : BGData G) (u : ↥D.U) :
    u ∈ fixedSubgroupS (phiS D) ↔ ∀ s : ↥D.S, (s : G) * (u : G) * (s : G)⁻¹ = (u : G) := by
  rw [mem_fixedSubgroupS]
  constructor
  · intro h s
    have h' := congrArg (fun x : ↥D.U => (x : G)) (h s)
    simpa [phiS_apply D s u] using h'
  · intro h s
    refine Subtype.ext ?_
    rw [phiS_apply D s u]
    exact h s

/-- `D.S` is contained in the centralizer of every element of `C_U(S)`. -/
theorem S_le_centralizer_of_mem_fixed (D : BGData G) {u : ↥D.U}
    (hu : u ∈ fixedSubgroupS (phiS D)) :
    (D.S : Subgroup G) ≤ Subgroup.centralizer ({(u : G)} : Set G) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  have h := (mem_fixedSubgroupS_phiS D u).mp hu ⟨g, hg⟩
  have h1 : g * (u : G) = (u : G) * g := by
    calc g * (u : G) = (g * (u : G) * g⁻¹) * g := by group
      _ = (u : G) * g := by rw [h]
  exact h1.symm

end L33

end Work.BG
