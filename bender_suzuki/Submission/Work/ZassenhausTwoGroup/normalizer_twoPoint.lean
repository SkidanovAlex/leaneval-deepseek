import Mathlib
import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.ZassenhausTwoGroup.isTI_Q
import Submission.Work.ThreePoints.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausTwoGroup.normalizer_twoPoint`

In the split rank-one Zassenhaus set-up (`IsSplitRankOne H Q t`, `IsZassenhaus H`, `t` an
involution outside `H`) with nontrivial two-point stabiliser `D = H ⊓ Hᵗ`, the normaliser of
`D` is `D · ⟨t⟩`: the Weyl element `t` inverts `D` and no other element normalises it.

The argument is the classical geometry of `Ω = G ⧸ H` (Peterfalvi I Ch. I §2, II Ch. VII §1):

* `D` fixes both the point `∞ = H` (because `D ≤ H`) and the point `tH` (because
  `D ≤ Hᵗ`), and it has no further fixed point: a nontrivial `d ∈ D` fixing a third point
  would be the identity by the Zassenhaus condition.  Hence `Fix(D) = {∞, tH}`
  (`mem_fixedPts_twoPoint`); this is exactly where both `IsZassenhaus` and `D ≠ ⊥` are used.
* The normaliser of `D` permutes `Fix(D)` (`smul_mem_fixedPts_normalizer`).
* So `g ∈ N_G(D)` either fixes `∞` (then also `tH`, hence lies in `H ⊓ Hᵗ = D`) or sends
  `∞` to `tH` (then `t⁻¹g` fixes `∞`, hence lies in `D`) — and in either case
  `g ∈ D ⊔ ⟨t⟩`.  The reverse inclusion holds because `t` normalises `D`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausTwoGroup

open IsTIQ

variable {G : Type} [Group G]

/-- **The normaliser permutes the fixed points.**  If `g` normalises `X`, then `g` carries the
set `fixedPts H X` of points of `Ω = G ⧸ H` fixed by `X` into itself. -/
theorem smul_mem_fixedPts_normalizer {H X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) {ω : G ⧸ H}
    (hω : ω ∈ fixedPts H X) : g • ω ∈ fixedPts H X := by
  refine Work.ThreePoints.mem_fixedPts.mpr ?_
  intro x hx
  have hconj : g⁻¹ * x * g ∈ X := (Subgroup.mem_normalizer_iff''.mp hg x).mp hx
  calc x • (g • ω) = (x * g) • ω := by rw [mul_smul]
    _ = (g * (g⁻¹ * x * g)) • ω := by rw [show x * g = g * (g⁻¹ * x * g) from by group]
    _ = g • ((g⁻¹ * x * g) • ω) := by rw [mul_smul]
    _ = g • ω := by rw [Work.ThreePoints.mem_fixedPts.mp hω (g⁻¹ * x * g) hconj]

/-- **Peterfalvi I Ch. I §2** (rank-one form).  In the Zassenhaus set-up the two-point
stabiliser `D = H ⊓ Hᵗ` (supposed nontrivial) fixes exactly the two points `∞ = H` and `t · ∞`
of `Ω = G ⧸ H`. -/
theorem mem_fixedPts_twoPoint {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H) (hD : twoPoint H t ≠ ⊥) (ω : G ⧸ H) :
    ω ∈ fixedPts H (twoPoint H t) ↔ ω = basePt H ∨ ω = ((t : G) : G ⧸ H) := by
  constructor
  · intro hω
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hω1, hωt⟩ := hcon
    have hex : ∃ d : G, d ∈ twoPoint H t ∧ d ≠ 1 := by
      by_contra h'
      rw [not_exists] at h'
      refine hD ((Subgroup.eq_bot_iff_forall (twoPoint H t)).mpr ?_)
      intro x hx
      by_contra hx1
      exact h' x ⟨hx, hx1⟩
    obtain ⟨d, hdmem, hdne⟩ := hex
    have h1 : d • basePt H = basePt H :=
      smul_basePt_of_mem H (Subgroup.mem_inf.mp hdmem).1
    have h2 : d • ((t : G) : G ⧸ H) = ((t : G) : G ⧸ H) :=
      (mem_twoPoint_iff_smul H t d).mp hdmem |>.2
    have h3 : d • ω = ω := Work.ThreePoints.mem_fixedPts.mp hω d hdmem
    have hne1 : basePt H ≠ ((t : G) : G ⧸ H) := ((basePt_ne_iff H t).mpr h.not_mem).symm
    have hne2 : basePt H ≠ ω := fun hh => hω1 hh.symm
    have hne3 : ((t : G) : G ⧸ H) ≠ ω := fun hh => hωt hh.symm
    exact hdne (hz (basePt H) ((t : G) : G ⧸ H) ω hne1 hne2 hne3 d h1 h2 h3)
  · rintro (rfl | rfl)
    · refine Work.ThreePoints.mem_fixedPts.mpr ?_
      intro d hd
      exact smul_basePt_of_mem H (Subgroup.mem_inf.mp hd).1
    · refine Work.ThreePoints.mem_fixedPts.mpr ?_
      intro d hd
      exact (mem_twoPoint_iff_smul H t d).mp hd |>.2

/-- **The normaliser of the two-point stabiliser.**  In the split rank-one Zassenhaus set-up
with `D = twoPoint H t ≠ ⊥`, one has `N_G(D) = D ⋊ ⟨t⟩`. -/
theorem normalizer_twoPoint {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hz : Submission.Blueprint.IsZassenhaus H)
    (hD : Submission.Blueprint.twoPoint H t ≠ ⊥) :
    Subgroup.normalizer (Submission.Blueprint.twoPoint H t : Set G) =
      Submission.Blueprint.twoPoint H t ⊔ Subgroup.zpowers t := by
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← h.invol]
    exact pow_orderOf_eq_one t
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hkey : ∀ y : G, t⁻¹ * (t⁻¹ * y * t) * t = y := by
    intro y
    rw [hti]
    calc t * (t * y * t) * t = t * t * y * (t * t) := by group
      _ = y := by rw [ht2, one_mul, mul_one]
  -- `t` normalises `D = H ⊓ Hᵗ` (in fact inverts it)
  have htN : t ∈ Subgroup.normalizer (twoPoint H t : Set G) := by
    rw [Subgroup.mem_normalizer_iff'']
    intro y
    simp only [Submission.Blueprint.twoPoint, Subgroup.mem_inf, mem_conj_iff_inv, hkey]
    tauto
  apply le_antisymm
  · intro g hg
    -- an element of `N_G(D)` fixing `∞` lies in `D`
    have key : ∀ a : G, a ∈ Subgroup.normalizer (twoPoint H t : Set G) →
        a • basePt H = basePt H → a ∈ twoPoint H t ⊔ Subgroup.zpowers t := by
      intro a ha habase
      have haH : a ∈ H := (smul_basePt_eq_iff H a).mp habase
      have hStep : a • ((t : G) : G ⧸ H) = ((t : G) : G ⧸ H) := by
        have h2 : a • ((t : G) : G ⧸ H) ∈ fixedPts H (twoPoint H t) :=
          smul_mem_fixedPts_normalizer ha
            ((mem_fixedPts_twoPoint h hz hD _).mpr (Or.inr rfl))
        rcases (mem_fixedPts_twoPoint h hz hD _).mp h2 with h' | h'
        · -- `a` would send `t • ∞` to `∞ = a • ∞`, so `t ∈ H`: absurd
          exfalso
          have ht' : ((t : G) : G ⧸ H) = basePt H := by
            calc ((t : G) : G ⧸ H) = a⁻¹ • (a • ((t : G) : G ⧸ H)) :=
                  (inv_smul_smul a _).symm
              _ = a⁻¹ • basePt H := by rw [h']
              _ = a⁻¹ • (a • basePt H) := by rw [habase]
              _ = basePt H := inv_smul_smul a _
          have htfix : t • basePt H = basePt H := by
            rw [smul_basePt]
            exact ht'
          exact h.not_mem ((smul_basePt_eq_iff H t).mp htfix)
        · exact h'
      exact Subgroup.mem_sup_left ((mem_twoPoint_iff_smul H t a).mpr ⟨haH, hStep⟩)
    have hbase : basePt H ∈ fixedPts H (twoPoint H t) :=
      (mem_fixedPts_twoPoint h hz hD _).mpr (Or.inl rfl)
    rcases (mem_fixedPts_twoPoint h hz hD _).mp (smul_mem_fixedPts_normalizer hg hbase) with
      hgbase | hgt
    · exact key g hg hgbase
    · -- `g` swaps `∞` and `t • ∞`: `t⁻¹ g` fixes `∞`, so it lies in `D`
      have hstep : (t⁻¹ * g) • basePt H = basePt H := by
        rw [mul_smul, hgt, ← smul_basePt H t, inv_smul_smul]
      have hmemN : t⁻¹ * g ∈ Subgroup.normalizer (twoPoint H t : Set G) :=
        Subgroup.mul_mem (Subgroup.normalizer (twoPoint H t : Set G))
          ((Subgroup.normalizer (twoPoint H t : Set G)).inv_mem htN) hg
      have hmem : t⁻¹ * g ∈ twoPoint H t ⊔ Subgroup.zpowers t := key (t⁻¹ * g) hmemN hstep
      have hg_eq : g = t * (t⁻¹ * g) := by group
      rw [hg_eq]
      exact (twoPoint H t ⊔ Subgroup.zpowers t).mul_mem
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers t)) hmem
  · exact sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr htN)

end Work.ZassenhausTwoGroup
