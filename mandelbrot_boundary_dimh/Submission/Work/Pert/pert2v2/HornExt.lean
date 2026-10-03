import Mathlib
import Submission.Work.Pert.AsmDefs
import Submission.Work.Pert.MaxDom
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.RBlock2.hornmap_end_limit

/-!
# `Work.Pert.pert2v2.HornExt` — the extended horn map `Ef = Φp ∘ Φm⁻¹` on the half plane

`NOTES_pert2v2_session30.md` §14.1 item 1.  `pert2v2.end_const_le_seg` (the paper's (A.4.4)) needs a
function `Ef` on the half plane `{y ≤ Im}` which is `1`-periodic up to the shift,
differentiable as `Ef - id`, has end limit `cp - cm`, and agrees with `Φp ∘ Φm⁻¹` at level `0`.

The paper's `tilde E_f = Φ_{+,f} ∘ Φ_{-,f}^{-1}` is defined on the *gate image* `Φ_{-,f}(Q_f^+)` and
extended by `tilde E_f (w+1) = tilde E_f w + 1`.  Here the gate image is `Φm '' Q`
(`Q = Qm Ξ' α`) and the extension is by the `ℤ`-saturation:

  `Ef w = Φp (invOn Φm Q (w - n)) + n`   for any `n : ℤ` with `w - n ∈ Φm '' Q`.

Well-definedness is the *only* extra input, and it is exactly the statement that the two gate
coordinates share their level structure:

  `SameLevelStructure Φm Φp Q := ∀ ς ς' ∈ Q, ∀ k : ℤ, Φm ς' = Φm ς + k → Φp ς' = Φp ς + k`.

In the design this is discharged from `Work.Pert.FatouOrbit`'s walk structure for `Φm` together with
`Φp`'s Abel equation along that walk, i.e. it *is* the design's domain restriction `(GW)`: the walk
of a gate point of `Q = Qm Ξ' α` up to its landing point stays in the waist `Qm ∩ Qp` (see
`pert2v2.GateWalk`, `NOTES_pert2v2_session20.md` §3).
-/

namespace Work.Pert.pert2v2

open MandelDim Complex Set Filter
open scoped Topology

noncomputable section

/-- **The level structure of the pair `(Φm, Φp)` on `Q`**: equal `Φm`-values up to an integer shift
give equal `Φp`-values up to the same shift. -/
def SameLevelStructure (Φm Φp : ℂ → ℂ) (Q : Set ℂ) : Prop :=
  ∀ ς : ℂ, ς ∈ Q → ∀ ς' : ℂ, ς' ∈ Q → ∀ k : ℤ,
    Φm ς' = Φm ς + (k : ℂ) → Φp ς' = Φp ς + (k : ℂ)

/-- The `ℤ`-extension of the horn map `Φp ∘ Φm⁻¹`: at a point `w` with a gate representative
`w - n ∈ Φm '' Q`, the value is `Φp (Φm⁻¹ (w - n)) + n`. -/
noncomputable def Ef (Φm Φp : ℂ → ℂ) (Q : Set ℂ) (w : ℂ) : ℂ := by
  classical
  exact if h : ∃ n : ℤ, w - (n : ℂ) ∈ Φm '' Q then
    Φp (Work.Pert.invOn Φm Q (w - ((Classical.choose h : ℤ) : ℂ)))
      + ((Classical.choose h : ℤ) : ℂ)
  else 0

variable {Φm Φp : ℂ → ℂ} {Q : Set ℂ}

/-- Unfolding `Ef` at a point with a gate representative. -/
theorem Ef_eq_of_level {w : ℂ} (h : ∃ n : ℤ, w - (n : ℂ) ∈ Φm '' Q) :
    Ef Φm Φp Q w
      = Φp (Work.Pert.invOn Φm Q (w - ((Classical.choose h : ℤ) : ℂ)))
        + ((Classical.choose h : ℤ) : ℂ) := by
  classical
  rw [Ef, dite_eq_left h]

/-- **Well-definedness of `Ef`**: the value does not depend on the chosen gate representative. -/
theorem Ef_level_value_eq (hcomp : SameLevelStructure Φm Φp Q) {w : ℂ} {n n' : ℤ}
    (hn : w - (n : ℂ) ∈ Φm '' Q) (hn' : w - (n' : ℂ) ∈ Φm '' Q) :
    Φp (Work.Pert.invOn Φm Q (w - (n : ℂ))) + (n : ℂ)
      = Φp (Work.Pert.invOn Φm Q (w - (n' : ℂ))) + (n' : ℂ) := by
  set ς := Work.Pert.invOn Φm Q (w - (n : ℂ)) with hς
  set ς' := Work.Pert.invOn Φm Q (w - (n' : ℂ)) with hς'
  have hςQ : ς ∈ Q := Work.Pert.invOn_mem hn
  have hς'Q : ς' ∈ Q := Work.Pert.invOn_mem hn'
  have hval : Φm ς = w - (n : ℂ) := Work.Pert.invOn_spec hn
  have hval' : Φm ς' = w - (n' : ℂ) := Work.Pert.invOn_spec hn'
  have hk : Φm ς' = Φm ς + ((n - n' : ℤ) : ℂ) := by
    rw [hval', hval]; push_cast; ring
  have hcs := hcomp ς hςQ ς' hς'Q (n - n') hk
  rw [hcs]
  push_cast
  ring

/-- **The `Ef` value from a supplied gate representative**: if `Φm ς + n = w` with `ς ∈ Q`, then
`Ef w = Φp ς + n`.  This is the form the downstream consumers use. -/
theorem Ef_apply (hcomp : SameLevelStructure Φm Φp Q) (hinj : Set.InjOn Φm Q)
    {w ς : ℂ} {n : ℤ} (hς : ς ∈ Q) (hwn : Φm ς + (n : ℂ) = w) :
    Ef Φm Φp Q w = Φp ς + (n : ℂ) := by
  classical
  have hmem : w - (n : ℂ) ∈ Φm '' Q := by
    rw [← hwn]; exact ⟨ς, hς, by ring⟩
  have hex : ∃ m : ℤ, w - (m : ℂ) ∈ Φm '' Q := ⟨n, hmem⟩
  have hspec : w - ((Classical.choose hex : ℤ) : ℂ) ∈ Φm '' Q := Classical.choose_spec hex
  rw [Ef_eq_of_level hex]
  have hval := Ef_level_value_eq (Φm := Φm) (Φp := Φp) (Q := Q) hcomp hspec hmem
  have hζ : Work.Pert.invOn Φm Q (w - (n : ℂ)) = ς :=
    Work.Pert.invOn_eq hinj hmem hς (by rw [← hwn]; ring)
  rw [hζ] at hval
  exact hval

/-- `Ef` at a gate value: at level `0` it is `Φp`. -/
theorem Ef_apply_of_mem (hcomp : SameLevelStructure Φm Φp Q) (hinj : Set.InjOn Φm Q)
    {ς : ℂ} (hς : ς ∈ Q) : Ef Φm Φp Q (Φm ς) = Φp ς := by
  have h := Ef_apply (Q := Q) hcomp hinj (w := Φm ς) (n := 0) hς (by simp)
  simpa using h

/-- **`Ef` shifts by `1` where the gate image is `ℤ`-dense.**  This is the `hper` hypothesis of
`pert2v2.end_const_le_seg`. -/
theorem Ef_add_one (hcomp : SameLevelStructure Φm Φp Q) (hinj : Set.InjOn Φm Q) {y : ℝ}
    (hcov : ∀ w : ℂ, y ≤ w.im → ∃ n : ℤ, w - (n : ℂ) ∈ Φm '' Q)
    {w : ℂ} (hw : y ≤ w.im) : Ef Φm Φp Q (w + 1) = Ef Φm Φp Q w + 1 := by
  classical
  obtain ⟨n, hn⟩ := hcov w hw
  set ς := Work.Pert.invOn Φm Q (w - (n : ℂ)) with hς
  have hςQ : ς ∈ Q := Work.Pert.invOn_mem hn
  have hςΦ : Φm ς = w - (n : ℂ) := Work.Pert.invOn_spec hn
  rw [Ef_apply (Q := Q) hcomp hinj (ς := ς) (n := (n + 1 : ℤ)) hςQ (by rw [hςΦ]; push_cast; ring),
    Ef_apply (Q := Q) hcomp hinj (ς := ς) (n := n) hςQ (by rw [hςΦ]; ring)]
  push_cast
  ring

/-- Iterating `Φp`'s Abel equation along a walk that stays in `Qp`. -/
theorem PhiP_iterate_eq {F Φp : ℂ → ℂ} {Qp : Set ℂ}
    (hAbel : ∀ z : ℂ, z ∈ Qp → F z ∈ Qp → Φp (F z) = Φp z + 1)
    {z : ℂ} {K : ℕ} (hz : ∀ j : ℕ, j ≤ K → F^[j] z ∈ Qp) :
    ∀ k : ℕ, k ≤ K → Φp (F^[k] z) = Φp z + (k : ℂ) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have hm' : m ≤ K := le_trans (Nat.le_succ m) hm
    have h1 : F (F^[m] z) ∈ Qp := by
      have h2 := hz (m + 1) hm
      rwa [show F^[m + 1] z = F (F^[m] z) from Function.iterate_succ_apply' F m z] at h2
    rw [Function.iterate_succ_apply', hAbel _ (hz m hm') h1, ih hm']
    push_cast; ring

/-- **`SameLevelStructure` from `Φm`'s walk structure.**  If `Φm`'s walk structure on `Q` lands on
`z'` whenever `Φm z'` is `Φm z` shifted by a natural number, the whole walk stays in `Qp`, and `Φp`
satisfies its Abel equation on `Qp`, then `(Φm, Φp)` share their level structure on `Q` — the input
`Ef_level_value_eq` needs for well-definedness of `Ef`.  (In the design `Q = Qm Ξ' α`,
`Qp = Qp Ξ' α`, and "the walk stays in `Qp`" is the `(GW)` domain restriction, `pert2v2.GateWalk`.) -/
theorem sameLevelStructure_of_walk {F Φm Φp : ℂ → ℂ} {Q Qp : Set ℂ}
    (hwalk : ∀ z : ℂ, z ∈ Q → ∀ z' : ℂ, z' ∈ Q → ∀ k : ℕ, Φm z' = Φm z + (k : ℂ) →
      (∀ j : ℕ, j ≤ k → F^[j] z ∈ Qp) ∧ F^[k] z = z')
    (hAbelP : ∀ z : ℂ, z ∈ Qp → F z ∈ Qp → Φp (F z) = Φp z + 1) :
    SameLevelStructure Φm Φp Q := by
  intro ς hς ς' hς' k hk
  rcases lt_or_ge k 0 with hkneg | hkpos
  · -- `k < 0`: walk the other way
    have hcast : (((-k).toNat : ℕ) : ℂ) = -(k : ℂ) := by
      have h : (((-k).toNat : ℕ) : ℤ) = -k := Int.toNat_of_nonneg (by omega)
      exact_mod_cast h
    have hk' : Φm ς = Φm ς' + (((-k).toNat : ℕ) : ℂ) := by
      rw [hcast, hk]; ring
    obtain ⟨hwalkQp, hland⟩ := hwalk ς' hς' ς hς (-k).toNat hk'
    have hΦp := PhiP_iterate_eq hAbelP hwalkQp ((-k).toNat) le_rfl
    rw [hland, hcast] at hΦp
    linear_combination -hΦp
  · -- `k ≥ 0`: walk forward
    have hcast : ((k.toNat : ℕ) : ℂ) = (k : ℂ) := by
      have h : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hkpos
      exact_mod_cast h
    have hk' : Φm ς' = Φm ς + (((k.toNat : ℕ)) : ℂ) := by
      rw [hcast]; exact hk
    obtain ⟨hwalkQp, hland⟩ := hwalk ς hς ς' hς' k.toNat hk'
    have hΦp := PhiP_iterate_eq hAbelP hwalkQp k.toNat le_rfl
    rw [hland, hcast] at hΦp
    exact hΦp

/-- **The transport**: at a gate representative `ς` (`Φm ς + n = w`), the difference `Ef - id` is
the difference of the two gate coordinates, with the shift cancelling:

  `Ef w - w = Φp ς - Φm ς`.

This is what lets the *proved* `Work.Pert.RBlock2.hornmap_end_limit` (whose conclusion is the end
limit of `Φp ∘ Φm⁻¹`) be read off for `Ef`. -/
theorem Ef_sub_id_eq (hcomp : SameLevelStructure Φm Φp Q) (hinj : Set.InjOn Φm Q)
    {w ς : ℂ} {n : ℤ} (hς : ς ∈ Q) (hwn : Φm ς + (n : ℂ) = w) :
    Ef Φm Φp Q w - w = Φp ς - Φm ς := by
  rw [Ef_apply (Q := Q) hcomp hinj hς hwn, ← hwn]
  ring

/-- The `ℤ`-shift form of `Ef`'s periodicity relation, from its `+1` form on a half plane. -/
theorem Ef_add_int {y : ℝ}
    (hper : ∀ u : ℂ, y ≤ u.im → Ef Φm Φp Q (u + 1) = Ef Φm Φp Q u + 1) :
    ∀ (k : ℤ) (u : ℂ), y ≤ u.im → Ef Φm Φp Q (u + (k : ℂ)) = Ef Φm Φp Q u + (k : ℂ) := by
  have hfwd : ∀ (m : ℕ) (u : ℂ), y ≤ u.im →
      Ef Φm Φp Q (u + (m : ℂ)) = Ef Φm Φp Q u + (m : ℂ) := by
    intro m
    induction m with
    | zero => intro u _; simp
    | succ k ih =>
      intro u hu
      have h1 : u + ((k + 1 : ℕ) : ℂ) = (u + (k : ℂ)) + 1 := by push_cast; ring
      rw [h1, hper _ (by simpa using hu), ih u hu]
      push_cast; ring
  have hbwd : ∀ (m : ℕ) (u : ℂ), y ≤ u.im →
      Ef Φm Φp Q (u - (m : ℂ)) = Ef Φm Φp Q u - (m : ℂ) := by
    intro m
    induction m with
    | zero => intro u _; simp
    | succ k ih =>
      intro u hu
      have h1 : u - ((k + 1 : ℕ) : ℂ) = (u - (k : ℂ)) - 1 := by push_cast; ring
      have h2 : ((u - (k : ℂ)) - 1) + 1 = u - (k : ℂ) := by ring
      have hstep := hper ((u - (k : ℂ)) - 1) (by simpa using hu)
      rw [h2] at hstep
      have hgoal : Ef Φm Φp Q ((u - (k : ℂ)) - 1) = Ef Φm Φp Q (u - (k : ℂ)) - 1 :=
        eq_sub_iff_add_eq.mpr hstep.symm
      rw [h1, hgoal, ih u hu]
      push_cast; ring
  intro k u hu
  rcases lt_or_ge k 0 with hk | hk
  · have hcast : (((-k).toNat : ℕ) : ℂ) = -(k : ℂ) := by
      have h : (((-k).toNat : ℕ) : ℤ) = -k := Int.toNat_of_nonneg (by omega)
      exact_mod_cast h
    have hkey : u + (k : ℂ) = u - (((-k).toNat : ℕ) : ℂ) := by rw [hcast]; ring
    rw [hkey, hbwd ((-k).toNat) u hu, hcast]
    ring
  · have hcast : ((k.toNat : ℕ) : ℂ) = (k : ℂ) := by
      have h : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk
      exact_mod_cast h
    rw [← hcast, hfwd k.toNat u hu]

/-- **`hlim` for `Ef`, by instantiating the proved `hornmap_end_limit`.**  The hypotheses are
literally those of `Work.Pert.RBlock2.hornmap_end_limit` (a window `|Re| ≤ 1` inside the gate, the
preimage window `hζre`, properness `hproper`, and the two end asymptotics), plus the coverage
`hcovAll` of the half plane by the gate saturation (the design's `waist_cover_pinned_v2`-type input,
which makes `Ef`'s `+1`-relation hold on the whole half plane).  The new work is only the transport
`Ef_sub_id_eq` and the shift `Ef_add_int`. -/
theorem Ef_tendsto_upperEnd {Ξ : ℝ} {α cm cp : ℂ} {B : ℝ}
    (hcomp : SameLevelStructure Φm Φp (Work.Pert.Qm Ξ α))
    (hinj : Set.InjOn Φm (Work.Pert.Qm Ξ α)) (hB : 0 < B)
    (hcovAll : ∀ (y : ℝ) (w : ℂ), y ≤ w.im → ∃ n : ℤ, w - (n : ℂ) ∈ Φm '' (Work.Pert.Qm Ξ α))
    (hcover : ∀ Y : ℝ, ∃ Yc : ℝ, ∀ w : ℂ, Yc ≤ w.im → 0 ≤ w.re → w.re ≤ 1 →
      w ∈ Φm '' (Work.Pert.Qm Ξ α) ∧
        Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) w ∈ Work.Pert.Qp Ξ α)
    (hζre : ∀ Y : ℝ, ∃ Yc : ℝ, ∀ w : ℂ, Yc ≤ w.im → 0 ≤ w.re → w.re ≤ 1 →
      |(Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) w).re| ≤ B)
    (hproper : ∀ R : ℝ, ∃ N : ℝ, ∀ ζ ∈ Work.Pert.Qm Ξ α, ζ.im ≤ R → (Φm ζ).im ≤ N)
    (hEndm : ∀ ε > 0, ∃ Y' : ℝ, ∀ z ∈ Work.Pert.Qm Ξ α, Y' < z.im → |z.re| ≤ B →
      ‖Φm z - z - cm‖ < ε)
    (hEndp : ∀ ε > 0, ∃ Y' : ℝ, ∀ z ∈ Work.Pert.Qp Ξ α, Y' < z.im → |z.re| ≤ B →
      ‖Φp z - z - cp‖ < ε) :
    Tendsto (fun w : ℂ => Ef Φm Φp (Work.Pert.Qm Ξ α) w - w)
      MandelDim.upperEnd (𝓝 (cp - cm)) := by
  classical
  -- (1) the window form, from `hornmap_end_limit` and the transport at level `0`
  have hwin : ∀ ε > 0, ∃ Y : ℝ, ∀ w : ℂ, Y ≤ w.im → 0 ≤ w.re → w.re ≤ 1 →
      ‖Ef Φm Φp (Work.Pert.Qm Ξ α) w - w - (cp - cm)‖ < ε := by
    intro ε hε
    obtain ⟨Y, hY⟩ := Work.Pert.RBlock2.hornmap_end_limit (Φm := Φm) (Φp := Φp)
      hB hinj hcover hζre hproper hEndm hEndp ε hε
    obtain ⟨Yc, hYc⟩ := hcover 0
    refine ⟨max Y Yc, fun w hw hw0 hw1 => ?_⟩
    have hwY : Y ≤ w.im := le_trans (le_max_left Y Yc) hw
    have hwYc : Yc ≤ w.im := le_trans (le_max_right Y Yc) hw
    obtain ⟨hmem, -⟩ := hYc w hwYc hw0 hw1
    have hEf : Ef Φm Φp (Work.Pert.Qm Ξ α) w
        = Φp (Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) w) := by
      have hsub := Ef_sub_id_eq (Q := Work.Pert.Qm Ξ α) hcomp hinj
        (ς := Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) w) (n := 0)
        (Work.Pert.invOn_mem hmem) (by rw [Work.Pert.invOn_spec hmem])
      rw [Work.Pert.invOn_spec hmem] at hsub
      rw [sub_eq_iff_eq_add] at hsub
      simpa using hsub
    rw [hEf]
    exact hY w hwY hw0 hw1
  -- (2) remove the `Re`-window by an integer shift
  rw [MandelDim.upperEnd, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨Y₀, hY₀⟩ := hwin ε hε
  have hper : ∀ u : ℂ, max Y₀ 1 ≤ u.im →
      Ef Φm Φp (Work.Pert.Qm Ξ α) (u + 1) = Ef Φm Φp (Work.Pert.Qm Ξ α) u + 1 :=
    fun u hu => Ef_add_one hcomp hinj (y := max Y₀ 1) (fun w hw => hcovAll (max Y₀ 1) w hw) hu
  have hshift := Ef_add_int (Φm := Φm) (Φp := Φp) (Q := Work.Pert.Qm Ξ α) (y := max Y₀ 1) hper
  rw [Filter.eventually_comap, Filter.eventually_atTop]
  refine ⟨max Y₀ 1 + 1, fun b hb x hxb => ?_⟩
  have hbx : b ≤ x.im := le_of_eq hxb.symm
  have hxy : max Y₀ 1 ≤ x.im :=
    le_trans (le_add_of_nonneg_right (by norm_num : (0:ℝ) ≤ 1)) (le_trans hb hbx)
  -- put `x` into the window `0 ≤ Re ≤ 1` by an integer shift
  obtain ⟨k, hk0, hk1⟩ : ∃ k : ℤ, (k : ℝ) ≤ x.re ∧ x.re < (k : ℝ) + 1 :=
    ⟨⌊x.re⌋, Int.floor_le x.re, Int.lt_floor_add_one x.re⟩
  set u : ℂ := x - (k : ℂ) with hu
  have huim : u.im = x.im := by simp [hu]
  have hure0 : 0 ≤ u.re := by
    have h : u.re = x.re - (k : ℝ) := by simp [hu]
    rw [h]; linarith
  have hure1 : u.re ≤ 1 := by
    have h : u.re = x.re - (k : ℝ) := by simp [hu]
    rw [h]; linarith
  have huy : max Y₀ 1 ≤ u.im := by rw [huim]; exact hxy
  have hux : x = u + (k : ℂ) := by rw [hu]; ring
  have hEfx : Ef Φm Φp (Work.Pert.Qm Ξ α) x
      = Ef Φm Φp (Work.Pert.Qm Ξ α) u + (k : ℂ) := by
    rw [hux]; exact hshift k u huy
  have hident : Ef Φm Φp (Work.Pert.Qm Ξ α) x - x - (cp - cm)
      = Ef Φm Φp (Work.Pert.Qm Ξ α) u - u - (cp - cm) := by
    rw [hEfx, hux]; ring
  rw [dist_eq_norm, hident]
  exact hY₀ u (le_trans (le_max_left Y₀ 1) huy) hure0 hure1

end

end Work.Pert.pert2v2
