import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.mem_pairSideNear_of_nearArc
import Submission.Work.Top.continuousOn_rayPt
import Submission.Work.ELTop.rayPt_add_int

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELTop

/-!
# `Work.ELTop.paramRay_subset_pairSideNear`

The whole ray of an angle `θ` lying in the *near arc* of a co-landing pair `P` is contained in
the near side `pairSideNear P` of `P`.

The near arc of `P` is the cyclic arc from `P.b` to `P.a`, of length
`Work.EL.arcLen P.b P.a = Int.fract (P.a - P.b)`, and `pairSideNear P` is by definition the
connected component of the complement of the pair curve `pairCurve P = R(P.a) ∪ {P.y} ∪ R(P.b)`
which contains the ray point at the midpoint of that arc.  Accordingly the hypothesis
`Work.EL.InArc θ P.b (P.a + 1)` says exactly that `θ` lies in the near arc: the angle `P.a + 1`
represents the same point of the circle as `P.a`, whence
`Work.EL.arcLen P.b (P.a + 1) = Work.EL.arcLen P.b P.a`.

The proof is the same explicit path as in `Work.ELTop.mem_pairSideNear_of_nearArc`:

* the piece of the ray of angle `θ` between the levels `2` and `t`;
* the equipotential arc of level `2` between the angles `mid` and `θ`,

but the arc hypothesis has to be *normalized* first: `θ` is replaced by the representative
`θ₀ = θ - ⌊θ - P.b⌋` lying literally in `Ioo P.b (P.b + arcLen P.b P.a)`.  The ray points are
`1`-periodic in the angle (`rayPt_add_int`), so this does not change the ray, and it makes the
equipotential arc between `mid` and `θ₀` stay inside the open near arc, where no angle is
congruent modulo `ℤ` to `P.a` or to `P.b`.  No Jordan curve theorem is used (the argument only
needs the maximality of a connected component), so the hypothesis `hJ` is not needed.
-/

/-! ## Angular arithmetic -/

/-- The length of the cyclic arc from `u` to `v` does not change when the endpoint `v` is
shifted by `1`: the angles `v` and `v + 1` represent the same point of the circle. -/
theorem arcLen_add_one_at (u v : ℝ) : Work.EL.arcLen u (v + 1) = Work.EL.arcLen u v := by
  have h : v + 1 - u = (v - u) + 1 := by ring
  rw [Work.EL.arcLen, Work.EL.arcLen, h, Int.fract_add_one]

/-- No angle of the open cyclic arc from `u` to `v` (of length `arcLen u v`) is congruent
modulo `ℤ` to either endpoint: writing `x = u + s` with `0 < s < fract (v - u)`, the only
integer in the interval `(0, 1)` is `0` (excluded), and `v - u` itself differs from `fract (v - u)`
by the integer `⌊v - u⌋`, which cannot be absorbed while staying strictly inside the arc. -/
theorem nearArc_ne_endpoints {u v x : ℝ} (hx : x ∈ Set.Ioo u (u + Work.EL.arcLen u v)) :
    (∀ k : ℤ, x ≠ u + (k : ℝ)) ∧ (∀ k : ℤ, x ≠ v + (k : ℝ)) := by
  have hδ1 : Work.EL.arcLen u v < 1 := Work.EL.arcLen_lt_one u v
  have hxu_pos : 0 < x - u := by linarith [hx.1]
  have hxu_lt : x - u < Work.EL.arcLen u v := by linarith [hx.2]
  constructor
  · intro k hk
    have h0 : (k : ℝ) = x - u := by rw [hk]; ring
    have h1 : (0 : ℝ) < (k : ℝ) := by linarith
    have h2 : (k : ℝ) < 1 := by linarith
    have h1' : (0 : ℤ) < k := by exact_mod_cast h1
    have h2' : k < (1 : ℤ) := by exact_mod_cast h2
    omega
  · intro k hk
    have hk' : x - u = (v - u) + (k : ℝ) := by rw [hk]; ring
    have h1 : Int.fract (x - u) = Work.EL.arcLen u v := by
      rw [hk', Int.fract_add_intCast, Work.EL.arcLen]
    have h2 : Int.fract (x - u) = x - u := by
      rw [Int.fract_eq_self]
      exact ⟨le_of_lt hxu_pos, lt_trans hxu_lt hδ1⟩
    rw [h2] at h1
    linarith

/-! ## The main geometric step -/

/-- A ray point of angle `θ` at a level `t > 1`, where `θ` lies *literally* in the open near arc
`Ioo P.b (P.b + arcLen P.b P.a)`, lies in the near side of `P`. -/
theorem mem_pairSideNear_of_mem_nearArc {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (P : Work.EL.CoPair hN) {θ t : ℝ}
    (hθ : θ ∈ Set.Ioo P.b (P.b + Work.EL.arcLen P.b P.a)) (ht : 1 < t) :
    Work.EL.rayPt hN θ t ∈ Work.EL.pairSideNear P := by
  have hδpos : 0 < Work.EL.arcLen P.b P.a := by linarith [hθ.1, hθ.2]
  have hθne := nearArc_ne_endpoints hθ
  set mid : ℝ := P.b + Work.EL.arcLen P.b P.a / 2 with hmid
  have hmid_mem : mid ∈ Set.Ioo P.b (P.b + Work.EL.arcLen P.b P.a) := by
    rw [Set.mem_Ioo, hmid]
    constructor <;> linarith
  -- the path: a piece of the ray of angle `θ` and an equipotential arc of level `2`
  set S : Set ℂ := (fun s : ℝ => Work.EL.rayPt hN θ s) '' Set.uIcc (2 : ℝ) t
      ∪ (fun s : ℝ => Work.EL.rayPt hN s 2) '' Set.uIcc mid θ with hS
  have hcont1 : ContinuousOn (fun s : ℝ => Work.EL.rayPt hN θ s) (Set.uIcc (2 : ℝ) t) :=
    (Work.Top.continuousOn_rayPt hN θ).mono (fun s hs => by
      rcases Set.mem_uIcc.mp hs with ⟨h2, -⟩ | ⟨ht', -⟩
      · exact lt_of_lt_of_le (by norm_num) h2
      · exact lt_of_lt_of_le ht ht')
  have hcont2 : ContinuousOn (fun s : ℝ => Work.EL.rayPt hN s 2) (Set.uIcc mid θ) :=
    (continuous_rayPt_angle hN (R := 2) (by norm_num)).continuousOn
  have hpre1 : IsPreconnected ((fun s : ℝ => Work.EL.rayPt hN θ s) '' Set.uIcc (2 : ℝ) t) :=
    (isPreconnected_uIcc (a := (2 : ℝ)) (b := t)).image _ hcont1
  have hpre2 : IsPreconnected ((fun s : ℝ => Work.EL.rayPt hN s 2) '' Set.uIcc mid θ) :=
    (isPreconnected_uIcc (a := mid) (b := θ)).image _ hcont2
  have hpre : IsPreconnected S := by
    rw [hS]
    exact IsPreconnected.union (Work.EL.rayPt hN θ 2)
      ⟨2, Set.left_mem_uIcc, rfl⟩ ⟨θ, Set.right_mem_uIcc, rfl⟩ hpre1 hpre2
  -- the path avoids the pair curve
  have hS_sub : S ⊆ (Work.EL.pairCurve P)ᶜ := by
    intro z hz
    rw [Set.mem_compl_iff, Work.EL.mem_pairCurve_iff]
    simp only [not_or]
    rw [hS] at hz
    rcases hz with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
    · -- a point of the ray of angle `θ`
      have hs1 : 1 < s := by
        rcases Set.mem_uIcc.mp hs with ⟨h2, -⟩ | ⟨ht', -⟩
        · linarith
        · linarith
      obtain ⟨hA, hB⟩ := hθne
      refine ⟨notMem_paramRay_of_ne_int hN hB hs1, ?_,
        notMem_paramRay_of_ne_int hN hA hs1⟩
      change Work.EL.rayPt hN θ s ≠ P.y
      intro hzy
      exact (Work.EL.paramRay_subset_compl hN θ (Work.EL.rayPt_mem_paramRay hN hs1))
        (hzy.symm ▸ landsN_mem_K hN P.lands_a)
    · -- a point of the equipotential arc of level `2`
      have hs_mem : s ∈ Set.Ioo P.b (P.b + Work.EL.arcLen P.b P.a) := by
        rcases Set.mem_uIcc.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨lt_of_lt_of_le hmid_mem.1 h1, lt_of_le_of_lt h2 hθ.2⟩
        · exact ⟨lt_of_lt_of_le hθ.1 h1, lt_of_le_of_lt h2 hmid_mem.2⟩
      obtain ⟨hA, hB⟩ := nearArc_ne_endpoints hs_mem
      refine ⟨notMem_paramRay_of_ne_int hN hB (by norm_num), ?_,
        notMem_paramRay_of_ne_int hN hA (by norm_num)⟩
      change Work.EL.rayPt hN s 2 ≠ P.y
      intro hzy
      exact (Work.EL.paramRay_subset_compl hN s
        (Work.EL.rayPt_mem_paramRay hN (by norm_num : (1 : ℝ) < 2)))
        (hzy.symm ▸ landsN_mem_K hN P.lands_a)
  -- the two endpoints of the path
  have hx_mem : Work.EL.rayPt hN mid 2 ∈ S := by
    rw [hS]
    exact Or.inr ⟨mid, Set.left_mem_uIcc, rfl⟩
  have hyt_mem : Work.EL.rayPt hN θ t ∈ S := by
    rw [hS]
    exact Or.inl ⟨t, Set.right_mem_uIcc, rfl⟩
  have hmem : Work.EL.rayPt hN θ t ∈
      connectedComponentIn (Work.EL.pairCurve P)ᶜ (Work.EL.rayPt hN mid 2) :=
    IsPreconnected.subset_connectedComponentIn hpre hx_mem hS_sub hyt_mem
  show Work.EL.rayPt hN θ t ∈ connectedComponentIn (Work.EL.pairCurve P)ᶜ
    (Work.EL.rayPt hN (P.b + Work.EL.arcLen P.b P.a / 2) 2)
  exact hmem

/-! ## The requested statement -/

theorem paramRay_subset_pairSideNear {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hJ : Work.Top.JordanForm) (P : Work.EL.CoPair hN) {θ : ℝ}
    (hθ : Work.EL.InArc θ P.b (P.a + 1)) : Work.EL.paramRay hN θ ⊆ Work.EL.pairSideNear P := by
  intro z hz
  obtain ⟨hzc, t, ht, hΦ⟩ := hz
  -- every point of a ray is a ray point, at the level given by the potential
  have hzt : z = Work.EL.rayPt hN θ t :=
    Work.Top.NakaneData.injOn_Phi hN hzc (Work.Top.NakaneData.rayPt_notMem hN ht)
      (by rw [hΦ, Work.Top.NakaneData.Phi_rayPt hN ht])
  rw [hzt]
  -- normalize the angle modulo `1` so that it lies literally in the open near arc
  set j : ℤ := ⌊θ - P.b⌋ with hj
  set θ₀ : ℝ := θ - (j : ℝ) with hθ₀
  have harc : Work.EL.arcLen P.b (P.a + 1) = Work.EL.arcLen P.b P.a :=
    arcLen_add_one_at P.b P.a
  have hfrac : θ₀ - P.b = Int.fract (θ - P.b) := by
    have hff := Int.floor_add_fract (θ - P.b)
    rw [← hj] at hff
    rw [hθ₀]
    linarith
  have hθ₀mem : θ₀ ∈ Set.Ioo P.b (P.b + Work.EL.arcLen P.b P.a) := by
    rw [Set.mem_Ioo]
    exact ⟨by linarith [hfrac, hθ.1], by linarith [hfrac, hθ.2, harc]⟩
  have hkey : Work.EL.rayPt hN θ₀ t ∈ Work.EL.pairSideNear P :=
    mem_pairSideNear_of_mem_nearArc hN P hθ₀mem ht
  have hperiod : Work.EL.rayPt hN θ t = Work.EL.rayPt hN θ₀ t := by
    have h1 : θ = θ₀ + (j : ℝ) := by rw [hθ₀]; ring
    rw [h1, rayPt_add_int hN θ₀ t j]
  rwa [hperiod]

end Work.ELTop
