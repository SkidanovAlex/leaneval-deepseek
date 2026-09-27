import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.H0_countable_fibre
import Submission.Work.EQ.isOpen_image_connectedComponent_of_isLocalHomeomorph
import Submission.Work.EQ.dense_range_rat_cast_complex

namespace Work.EQ

open Set Filter _root_.Topology

/-- **There are only countably many regular values (Rychlik Thm 11, step (141)).**  The set of
`c` such that some connected component of `H0` has `ψ = ψ₁ψ₂ ≡ c` on it is countable: each such
component contains a point whose `ψ₁`-value lies in the countable dense set `ℚ + ℚ·I` of `ℂ`
(because `ψ₁` of a component is open, being the image under the local homeomorphism `ψ₁` of an open
set), and each such point is determined by the value `c` (its `ψ`-value), so the regular values
inject into the union of the countable many countable fibres of `ψ₁`. -/
theorem countable_regular_values {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r)
    (hét : IsLocalHomeomorph (fun q : H0 a h => (q : ChainData).2.1)) :
    Set.Countable {c : ℂ | ∃ p ∈ H0 a h,
      ∀ q ∈ connectedComponentIn (H0 a h) p, q.2.1 * q.2.2 = c} := by
  classical
  set φ : H0 a h → ℂ := fun q => (q : ChainData).2.1 with hφdef
  have hétφ : IsLocalHomeomorph φ := by rw [hφdef]; exact hét
  -- the countable dense set `ℚ + ℚ·I ⊆ ℂ`
  set S : Set ℂ := Set.range (fun x : ℚ × ℚ => (x.1 : ℂ) + (x.2 : ℂ) * Complex.I) with hSdef
  have hSc : S.Countable := Set.countable_range _
  have hSd : Dense S := by rw [hSdef]; exact dense_range_rat_cast_complex
  -- the fibre of `ψ₁` over a point of `S` contributes only countably many values
  have hTu : ∀ u ∈ S, ({c : ℂ | ∃ p ∈ H0 a h, p.2.1 = u ∧
      ∀ q ∈ connectedComponentIn (H0 a h) p, q.2.1 * q.2.2 = c} : Set ℂ).Countable := by
    intro u _
    refine Set.Countable.mono ?_ (Set.Countable.image (H0_countable_fibre ha0 ha1 hh u)
      (fun p : ChainData => p.2.1 * p.2.2))
    rintro c ⟨p, hp, hpu, hc⟩
    exact ⟨p, ⟨hp, hpu⟩, hc p (mem_connectedComponentIn hp)⟩
  refine Set.Countable.mono ?_ (Set.Countable.biUnion hSc hTu)
  -- every regular value is caught by a component meeting `S`
  rintro c ⟨p, hp, hc⟩
  have hopen : IsOpen (φ '' connectedComponent (⟨p, hp⟩ : H0 a h)) :=
    isOpen_image_connectedComponent_of_isLocalHomeomorph hétφ ⟨p, hp⟩
  have hne : (φ '' connectedComponent (⟨p, hp⟩ : H0 a h)).Nonempty :=
    ⟨φ ⟨p, hp⟩, ⟨⟨p, hp⟩, mem_connectedComponent, rfl⟩⟩
  -- density of `S`: the component, whose `φ`-image is open and nonempty, meets `S`
  obtain ⟨u, ⟨huU, huS⟩⟩ := hSd.inter_open_nonempty _ hopen hne
  obtain ⟨q, hq, hqu⟩ := huU
  -- `q` is a point of the component of `p` whose `ψ₁`-value lies in `S`
  have hmemq : (q : ChainData) ∈ connectedComponentIn (H0 a h) p := by
    rw [connectedComponentIn_eq_image hp]
    exact mem_image_of_mem _ hq
  have heq : connectedComponentIn (H0 a h) p = connectedComponentIn (H0 a h) (q : ChainData) :=
    connectedComponentIn_eq hmemq
  refine Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨huS, ?_⟩⟩
  refine ⟨(q : ChainData), q.2, ?_, ?_⟩
  · show (q : ChainData).2.1 = u
    rw [← hqu]
  · intro q' hq'
    have hq'' : q' ∈ connectedComponentIn (H0 a h) p := by rw [heq]; exact hq'
    exact hc q' hq''

end Work.EQ
