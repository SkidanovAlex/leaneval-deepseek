import Mathlib
import Submission.Work.Whitney.CutPush.BigonData
import Submission.Work.Whitney.CutPush.gauge_isometry_of_two_frames
import Submission.Work.Drive.Push.localGraphFunction
import Submission.Work.Drive.Push.smoothCollarTrivialisation
import Submission.Work.Whitney.CutPush.exists_collar_trivialisation
import Submission.Work.Whitney.CutPush.spine_composite
import Submission.Work.Drive.Push.spineUnknottingLocal
import Submission.Work.Drive.Push.spineAlignment
import Submission.Work.Drive.Push.flattenAlignedSpine

namespace Work.Drive.Push

open scoped Manifold ContDiff
open Topology Set

/-- **The tube flattening along the smooth spine `γ₂`** — the first half of the Whitney bigon push
that the residual `Work.Whitney.CutPush.collarOneSidedness` (and hence
`Work.Drive.Push.collarConfinementSmooth`, hence `Work.Drive.hasPushSignedSmooth`) needs: an open
*tube* `U` around the arc `γ₂ '' Icc 0 1` inside `W`, and a global `C^∞` diffeomorphism `A` of
`ℝ^{2n}` carrying `f '' U` into a fixed `n`-plane `K`.

This is `Work.Whitney.CutPush.tube_flattening` (`CutPush/tube_flattening.lean`), instantiated at the
spine `γ₂` (smooth on `ℝ`, injective on `[0,1]` by `HasBigonData.inj₂`, and avoiding `p₁, q₁` — so
that `f` is injective on an open neighbourhood `O ⊆ W` of the arc, by `HasBigonData.clean` + `sep`),
with a thin tube `U₀ ⊆ O`.  The construction is split into the two halves
`Work.Drive.Push.alignedSpine` (straighten the arc, align the tangent planes along it to a fixed
plane) and `Work.Drive.Push.flattenAlignedSpine` (graph function + fibred shear); see
`Drive/Push/NOTES_tubeFlattening_route.md`. -/
theorem tubeFlattening {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (W : Set M)
    (p₁ p₂ q₁ q₂ : M) (γ₁ γ₂ : ℝ → M)
    (h : Work.Whitney.CutPush.HasBigonData n M f W p₁ p₂ q₁ q₂ γ₁ γ₂)
    (hγ₂sm : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₂)
    (hγ₂imm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      Function.Injective (mfderiv (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) γ₂ t)) :
    ∃ (U : Set M) (A Ainv : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n)))
      (K : Submodule ℝ (EuclideanSpace ℝ (Fin (2 * n)))),
      IsOpen U ∧ closure U ⊆ W ∧ γ₂ '' Set.Icc (0 : ℝ) 1 ⊆ U ∧
      p₁ ∉ U ∧ q₁ ∉ U ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ainv ∧
      Function.LeftInverse Ainv A ∧ Function.RightInverse Ainv A ∧
      Module.finrank ℝ K = n ∧ (∀ x : M, x ∈ U → A (f x) ∈ K) := by
  have hf := h.smooth
  have himm := h.immersed
  -- ## the two crossings are not on the arc `γ₂ '' Icc 0 1`
  have hp₁arc : p₁ ∉ γ₂ '' Set.Icc (0 : ℝ) 1 := by
    rintro ⟨t, ht, htp⟩
    have hdisj : (0 : ℝ) = 0 ∧ t = 0 ∨ (0 : ℝ) = 1 ∧ t = 1 :=
      h.disj 0 (by norm_num) t ht (by rw [h.arc₁₀, htp])
    rcases hdisj with ⟨-, ht0⟩ | ⟨h01, -⟩
    · rw [ht0, h.arc₂₀] at htp
      exact h.ne₁₂ htp.symm
    · norm_num at h01
  have hq₁arc : q₁ ∉ γ₂ '' Set.Icc (0 : ℝ) 1 := by
    rintro ⟨t, ht, htp⟩
    have hdisj : (1 : ℝ) = 0 ∧ t = 0 ∨ (1 : ℝ) = 1 ∧ t = 1 :=
      h.disj 1 (by norm_num) t ht (by rw [h.arc₁₁, htp])
    rcases hdisj with ⟨h10, -⟩ | ⟨-, ht1⟩
    · norm_num at h10
    · rw [ht1, h.arc₂₁] at htp
      exact h.ne₃₄ htp.symm
  -- ## an open tube `U₀` on which `f` is injective
  obtain ⟨U₀, hU₀o, hU₀arc, hU₀cl, hp₁U₀, hq₁U₀, hU₀inj⟩ :=
    Work.Whitney.CutPush.exists_tube_injOn h.clean h.isOpen_W γ₂ h.cont₂
      (fun t ht => h.arcW₂ t ht) hp₁arc hq₁arc
  -- ## the alignment half
  obtain ⟨A₁, A₁i, A₂, A₂i, K, a, e, hA₁, hA₁i, hA₁l, hA₁r, hA₂, hA₂i, hA₂l, hA₂r,
    he, hKfin, haff, hrange⟩ :
    ∃ (A₁ A₁i A₂ A₂i : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n)))
      (K : Submodule ℝ (EuclideanSpace ℝ (Fin (2 * n))))
      (a e : EuclideanSpace ℝ (Fin (2 * n))),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A₁ ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A₁i ∧
      Function.LeftInverse A₁i A₁ ∧ Function.RightInverse A₁i A₁ ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A₂ ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A₂i ∧
      Function.LeftInverse A₂i A₂ ∧ Function.RightInverse A₂i A₂ ∧
      e ≠ 0 ∧ Module.finrank ℝ K = n ∧
      (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → A₂ (A₁ (f (γ₂ t))) = a + t • e) ∧
      (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
        LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
          (fun y : M => A₂ (A₁ (f y))) (γ₂ t)).toLinearMap = K) :=
    Work.Drive.Push.spineAlignment hn f hf himm γ₂ hγ₂sm hγ₂imm h.inj₂ U₀ hU₀o hU₀arc hU₀inj
  -- ## the graph-function half
  set F : M → EuclideanSpace ℝ (Fin (2 * n)) := fun y => A₂ (A₁ (f y)) with hFdef
  have hFsm : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) F :=
    hA₂.contMDiff.comp (hA₁.contMDiff.comp hf)
  have hA₁fsm : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : M => A₁ (f y)) := hA₁.contMDiff.comp hf
  have hA₁fimm : ∀ y : M, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) (fun y : M => A₁ (f y)) y) :=
    Work.Whitney.CutPush.mfderiv_comp_injective f hf himm A₁ A₁i hA₁ hA₁i hA₁l
  have hFimm : ∀ y : M, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) F y) := by
    intro y
    exact Work.Whitney.CutPush.mfderiv_comp_injective (fun z : M => A₁ (f z)) hA₁fsm hA₁fimm
      A₂ A₂i hA₂ hA₂i hA₂l y
  obtain ⟨U, A₃, A₃i, hUo, hUarc, hA₃, hA₃i, hA₃l, hA₃r, hflat⟩ :
    ∃ (U : Set M) (A Ain : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n))),
      IsOpen U ∧ γ₂ '' Set.Icc (0 : ℝ) 1 ⊆ U ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ain ∧
      Function.LeftInverse Ain A ∧ Function.RightInverse Ain A ∧
      (∀ x : M, x ∈ U → A (F x) ∈ K) :=
    Work.Drive.Push.flattenAlignedSpine hn F hFsm hFimm γ₂ hγ₂sm K hKfin a e he haff hrange
  -- ## assembly
  refine ⟨U ∩ U₀, fun y => A₃ (A₂ (A₁ y)), fun y => A₁i (A₂i (A₃i y)), K, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, hKfin, ?_⟩
  · exact hUo.inter hU₀o
  · exact (closure_mono Set.inter_subset_right).trans hU₀cl
  · exact fun x hx => ⟨hUarc hx, hU₀arc hx⟩
  · exact fun hx => hp₁U₀ hx.2
  · exact fun hx => hq₁U₀ hx.2
  · exact hA₃.comp (hA₂.comp hA₁)
  · exact hA₁i.comp (hA₂i.comp hA₃i)
  · intro y
    show A₁i (A₂i (A₃i (A₃ (A₂ (A₁ y))))) = y
    rw [hA₃l (A₂ (A₁ y)), hA₂l (A₁ y), hA₁l y]
  · intro y
    show A₃ (A₂ (A₁ (A₁i (A₂i (A₃i y))))) = y
    rw [hA₁r (A₂i (A₃i y)), hA₂r (A₃i y), hA₃r y]
  · intro x hx
    exact hflat x hx.1

end Work.Drive.Push
