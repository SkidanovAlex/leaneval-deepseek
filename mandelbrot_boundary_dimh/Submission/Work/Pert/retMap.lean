import Mathlib
import Submission.Work.Pert.AsmDefs
import Submission.Work.Pert.Basic

/-!
# PERT · `Work.Pert.retMap`: the structure of the lifted return map `R̃_f = Φ ∘ T_f ∘ Φ⁻¹`

The residual clause of `Work.Pert.crux_norm` is, after the algebra of
`NOTES_crux_norm_route_session10.md` §1, exactly the (4.2.4) comparison
`Ẽ_f(w) ≈ d.E w`, where `Ẽ_f = Φp ∘ Φm⁻¹` is the paper's `Φ₊,f ∘ Φ₋,f⁻¹`.  The two facts about
`Ẽ_f` used in that reduction are proved here, for a *general* Fatou coordinate `Φ` of `F` on a `T`-invariant set `Q`
(`F ∘ T_f = T_f ∘ F`):

* `retOf_add_one` — **`T`-equivariance**: `Ẽ (w+1) = Ẽ w + 1` (so `Ẽ - id` is `1`-periodic); this is
  what makes the `m`, `m'` of the statement cancel;
* `retOf_add_const` — **pinning shift**: replacing `Φ` by `Φ + c` replaces `Ẽ` by
  `Ẽ (· - c) + c`.  (Consequently the residual of `crux_norm` is invariant under `c ∈ ℤ` — which is
  exactly the freedom the statement's `∃ k : ℤ` provides — and is *not* invariant for non-integer
  `c`, since the coverage points `z_w = Φ⁻¹ w` move with `c`.  See the note.)
-/

namespace Work.Pert

open MandelDim Complex Set

noncomputable section

/-- **`T`-equivariance of the lifted return map.**  If `F` commutes with the deck translation
`Tt α`, `Φ` is a Fatou coordinate of `F` on `Q` (Abel + injectivity), and the points
`z = invOn Φ Q w`, `F z`, `Tt α z`, `F (Tt α z)` all lie in `Q` while `w + 1 ∈ Φ '' Q`, then
`Ẽ (w + 1) = Ẽ w + 1`. -/
theorem retOf_add_one {F Φ : ℂ → ℂ} {Q : Set ℂ} {α w : ℂ}
    (hcomm : ∀ z : ℂ, F (Tt α z) = Tt α (F z))
    (hinj : Set.InjOn Φ Q)
    (hab : ∀ z ∈ Q, F z ∈ Q → Φ (F z) = Φ z + 1)
    (hw : w ∈ Φ '' Q) (hw1 : w + 1 ∈ Φ '' Q)
    (hFz : F (invOn Φ Q w) ∈ Q)
    (hTz : Tt α (invOn Φ Q w) ∈ Q) (hFTz : F (Tt α (invOn Φ Q w)) ∈ Q) :
    retOf Φ Q α (w + 1) = retOf Φ Q α w + 1 := by
  set z : ℂ := invOn Φ Q w with hz
  have hzQ : z ∈ Q := invOn_mem hw
  have hΦz : Φ z = w := invOn_spec hw
  have hΦFz : Φ (F z) = w + 1 := by rw [hab z hzQ hFz, hΦz]
  have hinv1 : invOn Φ Q (w + 1) = F z := invOn_eq hinj hw1 hFz hΦFz
  have h1 : retOf Φ Q α (w + 1) = Φ (Tt α (F z)) := by
    rw [retOf, hinv1]
  have h2 : Φ (Tt α (F z)) = Φ (Tt α z) + 1 := by
    rw [← hcomm z]; exact hab (Tt α z) hTz hFTz
  have h3 : retOf Φ Q α w = Φ (Tt α z) := retOf_eq hinj hw hzQ hΦz
  rw [h1, h2, h3]

/-- **`Ẽ - id` is `1`-periodic** (immediate from `retOf_add_one`). -/
theorem retOf_sub_id_add_one {F Φ : ℂ → ℂ} {Q : Set ℂ} {α w : ℂ}
    (hcomm : ∀ z : ℂ, F (Tt α z) = Tt α (F z))
    (hinj : Set.InjOn Φ Q)
    (hab : ∀ z ∈ Q, F z ∈ Q → Φ (F z) = Φ z + 1)
    (hw : w ∈ Φ '' Q) (hw1 : w + 1 ∈ Φ '' Q)
    (hFz : F (invOn Φ Q w) ∈ Q)
    (hTz : Tt α (invOn Φ Q w) ∈ Q) (hFTz : F (Tt α (invOn Φ Q w)) ∈ Q) :
    retOf Φ Q α (w + 1) - (w + 1) = retOf Φ Q α w - w := by
  rw [retOf_add_one hcomm hinj hab hw hw1 hFz hTz hFTz]
  ring

/-- **Pinning shift.**  Replacing the Fatou coordinate `Φ` by `Φ + c` conjugates the lifted return
map by the translation `w ↦ w - c`: `Ẽ_{Φ+c} w = Ẽ_Φ (w - c) + c`.  (The coverage points move with
`c`, so `crux_norm`'s residual is invariant only for integer `c`.) -/
theorem retOf_add_const {Φ : ℂ → ℂ} {Q : Set ℂ} {α c w : ℂ} (hinj : Set.InjOn Φ Q)
    (hwc : w - c ∈ Φ '' Q) :
    retOf (fun z => Φ z + c) Q α w = retOf Φ Q α (w - c) + c := by
  have hwc' : ∃ z ∈ Q, Φ z + c = w :=
    ⟨invOn Φ Q (w - c), invOn_mem hwc, by rw [invOn_spec hwc]; ring⟩
  have hinjc : Set.InjOn (fun z => Φ z + c) Q := by
    intro a ha b hb hab'
    exact hinj ha hb (add_right_cancel hab')
  have hmem : invOn (fun z => Φ z + c) Q w = invOn Φ Q (w - c) := by
    refine invOn_eq hinjc hwc' (invOn_mem hwc) ?_
    rw [invOn_spec hwc]; ring
  rw [retOf, hmem, retOf]

end

end Work.Pert
