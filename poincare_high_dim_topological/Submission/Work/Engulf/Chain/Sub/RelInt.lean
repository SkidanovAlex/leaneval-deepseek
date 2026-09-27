import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Generic.Basic
import Submission.Work.PL.Generic.Hull
import Submission.Work.PL.Generic.mem_hullOf
import Submission.Work.PL.Generic.eq_of_sum_smul_eq_of_affineIndependent
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.Chain.Sub.Basic

/-!
# `Submission.Work.Engulf.Chain.Sub.RelInt`

Convex-combination form of membership in `PL.simp`, and the characterisation of `RelInt` (the
relative interior of a face of a simplicial complex) by strictly positive barycentric weights.

Used by `Work.Engulf.Chain.E5` to transport the dimension bound `Cfg.dimH` from the coarse
complex to a fine subdivision, and to transport `SmoothChart`.
-/

open Set Metric PL

namespace Work.Engulf.Chain

variable {N : ℕ}

/-- Membership in `PL.simp s` as a convex combination of the vertices. -/
theorem mem_simp_iff {s : Finset (PL.E N)} {x : PL.E N} :
    x ∈ PL.simp s ↔ ∃ w : PL.E N → ℝ, (∀ v ∈ s, 0 ≤ w v) ∧ (∑ v ∈ s, w v = 1) ∧
      (∑ v ∈ s, w v • v = x) := by
  rw [show PL.simp s = Work.PL.Generic.hullOf (id : PL.E N → PL.E N) s from by
    rw [Work.PL.Generic.hullOf_eq_simp]; simp]
  exact Work.PL.Generic.mem_hullOf _ _ _

/-- `p` lies in the relative interior of the face `s` of `K` iff it is a convex combination of
the vertices of `s` with strictly positive weights. -/
theorem relInt_iff_weights {K : PL.Cx N} {s : Finset (PL.E N)} (hs : s ∈ K.faces) {p : PL.E N} :
    RelInt K s p ↔ ∃ a : PL.E N → ℝ, (∀ v ∈ s, 0 < a v) ∧ (∑ v ∈ s, a v = 1) ∧
      (∑ v ∈ s, a v • v = p) := by
  classical
  constructor
  · intro h
    obtain ⟨hp, hproper⟩ := h
    obtain ⟨w, hw0, hw1, hw2⟩ := mem_simp_iff.1 hp
    refine ⟨fun v => if v ∈ s then w v else 0, ?_, ?_, ?_⟩
    · intro v hv
      have hwv : 0 < w v := by
        rcases lt_or_eq_of_le (hw0 v hv) with hlt | heq
        · exact hlt
        · exfalso
          have hwne : (s.erase v).Nonempty := by
            rw [Finset.nonempty_iff_ne_empty]
            intro hem
            have hsub : s ⊆ {v} := by
              intro u hu
              by_contra huv
              have huv' : u ≠ v := fun h => huv (Finset.mem_singleton.mpr h)
              have : u ∈ s.erase v := Finset.mem_erase.mpr ⟨huv', hu⟩
              rw [hem] at this
              simpa using this
            have hs_eq : s = {v} :=
              Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hv)
            have : w v = 1 := by
              rw [← hw1, hs_eq]
              simp
            rw [this] at heq
            exact absurd heq (by norm_num)
          have hmem : s.erase v ∈ K.faces :=
            K.down_closed hs (Finset.erase_subset v s) hwne
          have hssub : s.erase v ⊂ s := Finset.erase_ssubset hv
          have hp' : p ∈ PL.simp (s.erase v) := by
            refine mem_simp_iff.2 ⟨w, fun u hu => hw0 u (Finset.erase_subset v s hu), ?_, ?_⟩
            · have := Finset.sum_erase_add s w hv
              rw [hw1, ← heq, add_zero] at this
              exact this
            · have := Finset.sum_erase_add s (fun u => w u • u) hv
              rw [hw2, ← heq, zero_smul, add_zero] at this
              exact this
          exact hproper _ hmem hssub hp'
      show 0 < (if v ∈ s then w v else 0)
      rw [if_pos hv]
      exact hwv
    · have hc : (∑ v ∈ s, (if v ∈ s then w v else 0)) = ∑ v ∈ s, w v :=
        Finset.sum_congr rfl (fun v hv => by show (if v ∈ s then w v else 0) = w v; rw [if_pos hv])
      rw [hc, hw1]
    · have hc : (∑ v ∈ s, (if v ∈ s then w v else 0) • v) = ∑ v ∈ s, w v • v :=
        Finset.sum_congr rfl (fun v hv => by show (if v ∈ s then w v else 0) • v = w v • v; rw [if_pos hv])
      rw [hc, hw2]
  · rintro ⟨a, ha0, ha1, ha2⟩
    constructor
    · exact mem_simp_iff.2 ⟨a, fun v hv => le_of_lt (ha0 v hv), ha1, ha2⟩
    · intro s' hs' hss' hp'
      obtain ⟨b, hb0, hb1, hb2⟩ := mem_simp_iff.1 hp'
      have hss : s' ⊆ s := hss'.1
      have hb1' : (∑ v ∈ s, (if v ∈ s' then b v else 0)) = 1 := by
        have hc : (∑ v ∈ s, (if v ∈ s' then b v else 0)) = ∑ v ∈ s', b v := by
          rw [← Finset.sum_subset hss (fun v _ hv => by simp [hv])]
          exact Finset.sum_congr rfl (fun v hv => by
            show (if v ∈ s' then b v else 0) = b v; rw [if_pos hv])
        rw [hc, hb1]
      have hb2' : (∑ v ∈ s, (if v ∈ s' then b v else 0) • v) = p := by
        have hc : (∑ v ∈ s, (if v ∈ s' then b v else 0) • v) = ∑ v ∈ s', b v • v := by
          rw [← Finset.sum_subset hss (fun v _ hv => by simp [hv])]
          exact Finset.sum_congr rfl (fun v hv => by
            show (if v ∈ s' then b v else 0) • v = b v • v; rw [if_pos hv])
        rw [hc, hb2]
      have hsum : (∑ v ∈ s, a v • (id : PL.E N → PL.E N) v)
          = ∑ v ∈ s, (if v ∈ s' then b v else 0) • (id : PL.E N → PL.E N) v := by
        simpa using ha2.trans hb2'.symm
      have huniq := Work.PL.Generic.eq_of_sum_smul_eq_of_affineIndependent
        (y := id) (K.indep hs) ha1 hb1' hsum
      obtain ⟨v, hv, hvs'⟩ := Finset.exists_of_ssubset hss'
      have hzero : a v = 0 := by
        rw [huniq v hv]
        simp [hvs']
      have hpos := ha0 v hv
      rw [hzero] at hpos
      exact absurd hpos (lt_irrefl 0)

/-- The barycenter of a face lies in its relative interior. -/
theorem relInt_centerMass {K : PL.Cx N} {s : Finset (PL.E N)} (hs : s ∈ K.faces) :
    RelInt K s ((s.card : ℝ)⁻¹ • ∑ v ∈ s, v) := by
  classical
  have hne : s.Nonempty := K.nonempty_of_mem_faces hs
  have hcard : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hne)
  rw [relInt_iff_weights hs]
  refine ⟨fun v => if v ∈ s then (s.card : ℝ)⁻¹ else 0, ?_, ?_, ?_⟩
  · intro v hv
    show 0 < (if v ∈ s then (s.card : ℝ)⁻¹ else 0)
    rw [if_pos hv]
    exact inv_pos.mpr (Nat.cast_pos.mpr (Finset.card_pos.mpr hne))
  · have hc : (∑ v ∈ s, (if v ∈ s then (s.card : ℝ)⁻¹ else 0))
        = (s.card : ℝ) * (s.card : ℝ)⁻¹ := by
      rw [Finset.sum_congr rfl (fun v hv => by
        show (if v ∈ s then (s.card : ℝ)⁻¹ else 0) = (s.card : ℝ)⁻¹; rw [if_pos hv]),
        Finset.sum_const, nsmul_eq_mul]
    rw [hc, mul_inv_cancel₀ hcard]
  · have hc : (∑ v ∈ s, (if v ∈ s then (s.card : ℝ)⁻¹ else 0) • v)
        = (s.card : ℝ)⁻¹ • ∑ v ∈ s, v := by
      rw [Finset.sum_congr rfl (fun v hv => by
        show (if v ∈ s then (s.card : ℝ)⁻¹ else 0) • v = (s.card : ℝ)⁻¹ • v
        rw [if_pos hv]), Finset.smul_sum]
    rw [hc]

/-- `RelInt` points of a coarse face: a point of `simp e` lying in the relative interior of `e`
lies in `simp t` only if `e ⊆ t`. -/
theorem subset_of_relInt_mem {K : PL.Cx N} {e t : Finset (PL.E N)} (he : e ∈ K.faces)
    (ht : t ∈ K.faces) {p : PL.E N} (hp : RelInt K e p) (hpt : p ∈ PL.simp t) : e ⊆ t := by
  have hinter : p ∈ PL.simp (e ∩ t) := by
    rw [← simp_inter he ht]; exact ⟨hp.1, hpt⟩
  have hne : (e ∩ t).Nonempty := (simp_nonempty_iff.1 ⟨p, hinter⟩)
  have hmem : e ∩ t ∈ K.faces := K.down_closed he Finset.inter_subset_left hne
  by_contra hcon
  have hss : e ∩ t ⊂ e :=
    Finset.ssubset_iff_subset_ne.2 ⟨Finset.inter_subset_left, fun heq => hcon (heq ▸ Finset.inter_subset_right)⟩
  exact hp.2 _ hmem hss hinter

end Work.Engulf.Chain
