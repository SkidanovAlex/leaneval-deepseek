import Mathlib

namespace Work.SimplyConnected.ABS

/-- In a simply connected subset `s` of a topological space `X`, any two paths `p` and `q`
with the same endpoints and whose ranges are contained in `s` are homotopic (in `X`). -/
theorem homotopic_of_isSimplyConnected_of_range_subset {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsSimplyConnected s) {a b : X} (ha : a ∈ s) (hb : b ∈ s)
    (p q : Path a b) (hp : ∀ t, p t ∈ s) (hq : ∀ t, q t ∈ s) :
    Path.Homotopic p q := by
  -- view `p` and `q` as paths in the subtype `s`
  let p' : Path (⟨a, ha⟩ : s) (⟨b, hb⟩ : s) :=
    { toContinuousMap := ⟨fun t => (⟨p t, hp t⟩ : s), Continuous.subtype_mk p.continuous hp⟩
      source' := by simp [Path.source]
      target' := by simp [Path.target] }
  let q' : Path (⟨a, ha⟩ : s) (⟨b, hb⟩ : s) :=
    { toContinuousMap := ⟨fun t => (⟨q t, hq t⟩ : s), Continuous.subtype_mk q.continuous hq⟩
      source' := by simp [Path.source]
      target' := by simp [Path.target] }
  -- `s` is simply connected, so `p'` and `q'` are homotopic inside `s`
  have h : Path.Homotopic p' q' := @SimplyConnectedSpace.paths_homotopic s _ hs _ _ p' q'
  -- push the homotopy forward along the inclusion `s ↪ X`
  have hmap := h.map (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X))
  have hp_eq : p'.map continuous_subtype_val = p := by ext t; rfl
  have hq_eq : q'.map continuous_subtype_val = q := by ext t; rfl
  simpa [hp_eq, hq_eq] using hmap

end Work.SimplyConnected.ABS
