import Mathlib
import Submission.Work.Drive.Push.spineAlignment
import Submission.Work.Drive.Push.flattenAlignedSpine
import Submission.Work.Whitney.CutPush.exists_collar_trivialisation
import Submission.Work.Drive.Whitney.tubeFlatteningFirst

/-!
# Flattening one sheet along the arc: the one-arc tube

`Work.Drive.PushDisc.sheetOneTubeFlattening` is the *one-arc* half of the tube flattening: given the
immersion `f : M → ℝ^{2n}` (`n ≥ 3`), an open `W` with compact closure, a "clean" pair structure
only through `p₁ ↔ p₂` and `q₁ ↔ q₂`, the arc `γ₁` from `p₁` to `q₁` (inside `W`, injective,
immersed, avoiding `p₂` and `q₂`), there is an open tube `U` around the arc, with `closure U ⊆ W`
and avoiding `p₂`, `q₂`, and a diffeomorphism `A` of `ℝ^{2n}` together with an `n`-plane `K` such
that `A (f x) ∈ K` for every `x ∈ U`.

The proof is a two-half assembly, both halves already in the library:

* `Work.Whitney.CutPush.exists_tube_injOn` produces the tube `U₀` (open, contains the arc,
  `closure U₀ ⊆ W`, avoids `p₂` and `q₂`, and `f` is injective on it) — this is where the clean
  hypothesis is spent, with the roles of `p₁` / `q₁` interchanged so that the *opposite* double
  points are the ones removed;
* `Work.Drive.Push.spineAlignment` straightens the arc and aligns the tangent planes of `f` along
  it to a fixed `n`-plane `K` (needs only openness and injectivity of `f` on `U₀`);
* `Work.Drive.Push.flattenAlignedSpine` flattens the aligned tube onto `K`;
* intersecting the two tubes gives the result.
-/

namespace Work.Drive.PushDisc

set_option maxHeartbeats 1000000

theorem sheetOneTubeFlattening {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y, Function.Injective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (W : Set M) (hWopen : IsOpen W) (hWcpt : IsCompact (closure W))
    (p₁ p₂ q₁ q₂ : M) (hW₁ : p₁ ∈ W) (hW₃ : q₁ ∈ W)
    (hp₁p₂ : p₁ ≠ p₂)
    (hfp : f p₁ = f p₂)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨ (y = q₂ ∧ z = q₁))
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (γ₁ : ℝ → M) (hγ₁ : Continuous γ₁) (hγ₁0 : γ₁ 0 = p₁) (hγ₁1 : γ₁ 1 = q₁)
    (hγW₁ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ∈ W)
    (hγ₁inj : Set.InjOn γ₁ (Set.Icc (0 : ℝ) 1))
    (hγ₁smooth : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₁)
    (hγ₁imm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → Function.Injective (mfderiv
      (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) γ₁ t))
    (hp₂arc : p₂ ∉ γ₁ '' Set.Icc (0 : ℝ) 1) (hq₂arc : q₂ ∉ γ₁ '' Set.Icc (0 : ℝ) 1) :
    ∃ (U : Set M) (A Ainv : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n)))
      (K : Submodule ℝ (EuclideanSpace ℝ (Fin (2 * n)))),
      IsOpen U ∧ closure U ⊆ W ∧ γ₁ '' Set.Icc (0 : ℝ) 1 ⊆ U ∧ p₂ ∉ U ∧ q₂ ∉ U ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ainv ∧
      Function.LeftInverse Ainv A ∧ Function.RightInverse Ainv A ∧
      Module.finrank ℝ K = n ∧ (∀ x : M, x ∈ U → A (f x) ∈ K) := by
  classical
  -- ## `p₂` and `q₂` are the points to be removed: interchange the roles of the two double points
  have hclean' : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₂ ∧ z = p₁) ∨ (y = p₁ ∧ z = p₂) ∨ (y = q₂ ∧ z = q₁) ∨
        (y = q₁ ∧ z = q₂) := by
    intro y z hy hz hyz
    rcases hclean y z hy hz hyz with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  -- ## the tube around the arc: open, inside `W` (even its closure), avoiding `p₂`, `q₂`, and
  --     with `f` injective on it
  obtain ⟨U₀, hU₀o, hU₀arc, hU₀cl, hp₂U₀, hq₂U₀, hU₀inj⟩ :=
    Work.Whitney.CutPush.exists_tube_injOn hclean' hWopen γ₁ hγ₁
      (fun t ht => hγW₁ t ht) hp₂arc hq₂arc
  -- ## first half: straighten the arc and align the tangent planes of `f` along it
  obtain ⟨A₁, A₁i, A₂, A₂i, K, a, e, hA₁, hA₁i, hA₁l, hA₁r, hA₂, hA₂i, hA₂l, hA₂r,
    he, hKfin, haff, hrange⟩ :=
    Work.Drive.Push.spineAlignment hn f hf himm γ₁ hγ₁smooth hγ₁imm hγ₁inj U₀ hU₀o hU₀arc hU₀inj
  -- ## second half: flatten the aligned sheet onto the plane `K`
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
  obtain ⟨U, A₃, A₃i, hUo, hUarc, hA₃, hA₃i, hA₃l, hA₃r, hflat⟩ :=
    Work.Drive.Push.flattenAlignedSpine hn F hFsm hFimm γ₁ hγ₁smooth K hKfin a e he haff hrange
  -- ## assembly: intersect the two tubes
  refine ⟨U ∩ U₀, fun y => A₃ (A₂ (A₁ y)), fun y => A₁i (A₂i (A₃i y)), K, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, hKfin, ?_⟩
  · exact hUo.inter hU₀o
  · exact (closure_mono Set.inter_subset_right).trans hU₀cl
  · exact fun x hx => ⟨hUarc hx, hU₀arc hx⟩
  · exact fun hx => hp₂U₀ hx.2
  · exact fun hx => hq₂U₀ hx.2
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

end Work.Drive.PushDisc
