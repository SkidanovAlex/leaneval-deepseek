import Mathlib
import Submission.Work.Whitney.PushDefs
import Submission.Work.Whitney.cancellation_of_pushData
import Submission.Work.Whitney.clean_region_of_arcs
import Submission.Work.Whitney.exists_disjoint_arcs_avoiding_finite
import Submission.Work.Whitney.ncard_doubleSet_cancel
import Submission.Work.Whitney.EndgameAux
import Submission.Work.Whitney.PairDet
import Submission.Work.Whitney.pairDet_ne_zero_iff
import Submission.Work.Whitney.ArcFraming
import Submission.Work.Whitney.exists_isArcChain
import Submission.Work.Whitney.exists_simple_transverse_immersion
import Submission.Work.Embedding.exists_embedding_of_components
import Submission.Work.Whitney.isEmbedding_of_injective_of_compactSpace

/-!
# The Whitney endgame, without orientations

This file isolates the endgame of Whitney's strong embedding theorem in a form that uses **no
orientation** of the manifold `M`: neither a global oriented atlas
(`Work.Whitney.IsSmoothOrientedAtlas`) nor the sign comparison
(`Work.Whitney.OppositeSign`, `Work.Whitney.OppositeType`) appears in any statement below.

The reason this is possible is that the *construction* of the Whitney move in this workspace
(`Work.Whitney.ambient_push_data_full`, `Work.Whitney.cancellation_of_pushData`) is already
orientation-free: the docstring of `Work.Whitney.ambient_push_data_full` records that "the arcs
`γ₁, γ₂` and the sign condition are not used: the geometric content is purely local at the two
double points".  The sign conditions were only ever used to *choose* between two insertion
variants; with the push available, the endgame needs no such choice: it inserts an arbitrary
partner and cancels the pair.

Consequently the whole of the compact case for `n ≥ 3` is proved for an **arbitrary** compact
manifold (orientable or not) from the two interfaces below.

## The interfaces

* `Work.Whitney.HasPushNF` — the Whitney push.  This is
  `Work.Whitney.HasAmbientPushData f W p₁ p₂ q₁ q₂`, with the irrelevant hypotheses
  (`A`, `hA`, `hsign`) of `Work.Whitney.HasAmbientPush` dropped.  It is the *only* remaining
  geometric input of the compact case: its proof is the construction of
  `Work.Whitney.exists_local_push_cut_full` plus the (already written) assembly of
  `Work.Whitney.ambient_push_data_full`.

* `Work.Whitney.HasInsertionNF` — the insertion step: glue one double point into an immersion at a
  clean point, preserving the two invariants `SimpleDP` ("every double point has exactly two
  preimages") and `TransDP'` ("every double point is transverse, certified by two smooth charts").
  Its proof is `Work.Whitney.exists_insertedDoublePoint` with the oriented atlas `A` replaced by
  `chartAt` (the only role of `A` in that proof is to supply one chart near the clean point and to
  *choose* the sign; the construction itself is atlas-free).

## What is proved here

* `Work.Whitney.hasCancelNF_of_hasPushNF` — the push gives the cancellation (this is immediate from
  the already proved `Work.Whitney.cancellation_of_pushData`, whose hypotheses are orientation-free);
* `Work.Whitney.exists_reduce_double_points_NF` — insertion + cancellation remove one double point
  while preserving the invariants;
* `Work.Whitney.exists_embedding_of_reduce_NF` — the iteration;
* `Work.Whitney.exists_embedding_of_compact_connected_NF`,
  `Work.Whitney.exists_embedding_of_compact_NF` — the compact case (`n ≥ 3`, arbitrary
  orientability), modulo the two interfaces.
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology

set_option linter.unusedVariables false

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

/-- **Transversality of every double point, certified by two smooth charts.**  This is
`Work.Whitney.TransDP A f` without the atlas: the charts are existentially chosen, and are required
to be smooth (`Work.Whitney.IsSmoothChart`) so that the `pairDet`-statements are meaningful. -/
def TransDP' (f : M → EuclideanSpace ℝ (Fin (2 * n))) : Prop :=
  ∀ p : M × M, p ∈ doubleSet f →
    ∃ c₁ c₂ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
      IsSmoothChart c₁ ∧ IsSmoothChart c₂ ∧
      p.1 ∈ c₁.source ∧ p.2 ∈ c₂.source ∧ pairDet f c₁ c₂ p.1 p.2 ≠ 0

/-- **Intrinsic transversality gives a chart certificate.**  The charts are the canonical charts
`chartAt`, which are smooth (`Work.Whitney.isSmoothChart_chartAt`). -/
theorem transDP'_of_range {f : M → EuclideanSpace ℝ (Fin (2 * n))}
    (hf : ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f)
    (h : ∀ p : M × M, p ∈ doubleSet f →
      (mfderiv (𝓡 n) (𝓡 (2 * n)) f p.1).range ⊔
        (mfderiv (𝓡 n) (𝓡 (2 * n)) f p.2).range = ⊤) :
    TransDP' f := by
  have htop : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  intro p hp
  have hp₁ : p.1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p.1).source := mem_chart_source _ p.1
  have hp₂ : p.2 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p.2).source := mem_chart_source _ p.2
  have hc₁ := isSmoothChart_chartAt (n := n) p.1
  have hc₂ := isSmoothChart_chartAt (n := n) p.2
  refine ⟨chartAt (EuclideanSpace ℝ (Fin n)) p.1, chartAt (EuclideanSpace ℝ (Fin n)) p.2,
    hc₁, hc₂, hp₁, hp₂, ?_⟩
  rw [pairDet_ne_zero_iff f _ _ p.1 p.2 hp₁ hp₂
    ((hc₁.1.contMDiffAt ((chartAt (EuclideanSpace ℝ (Fin n)) p.1).open_source.mem_nhds hp₁)).mdifferentiableAt htop)
    ((hc₂.1.contMDiffAt ((chartAt (EuclideanSpace ℝ (Fin n)) p.2).open_source.mem_nhds hp₂)).mdifferentiableAt htop)
    ((hc₁.2.contMDiffAt ((chartAt (EuclideanSpace ℝ (Fin n)) p.1).open_target.mem_nhds
      ((chartAt (EuclideanSpace ℝ (Fin n)) p.1).map_source hp₁))).mdifferentiableAt htop)
    ((hc₂.2.contMDiffAt ((chartAt (EuclideanSpace ℝ (Fin n)) p.2).open_target.mem_nhds
      ((chartAt (EuclideanSpace ℝ (Fin n)) p.2).map_source hp₂))).mdifferentiableAt htop)
    ((hf p.1).mdifferentiableAt htop) ((hf p.2).mdifferentiableAt htop)]
  exact h p hp

/-- **The local Whitney push at one double point.**  This is *verbatim* the statement of
`Work.Whitney.exists_local_push_cut_full` (`Submission/Work/Whitney/exists_local_push_cut_full.lean`),
which is atlas-free and sign-free as it stands: at a transverse double point `f p₁ = f p₂` of an
immersion, with a clean region `W` (the second pair `(r₁,r₂)` being the *other* double point of
`W`, invisible to the construction), there is a closed cut `K ∋ p₁`, an open support `S` around
`f p₂` and a diffeomorphism `ψ` (inverse `σ`) of `ℝ^{2n}`, the identity off `S`, which moves the
sheet over `W ∖ K` off the rest of the image.

This is the *entire* remaining mathematical input of the compact case (`n ≥ 3`): it is where the
finger/tongue construction of the Whitney move lives.  The isolated proof obligations of
`Work.Whitney.exists_local_push_cut_full` are the files
`Submission/Work/Whitney/local_push_cut_transverse_full.lean` and
`Submission/Work/Whitney/local_push_cut_nontransverse_full.lean`. -/
def LocalPushNTrans (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M] : Prop :=
  ∀ (hn : 3 ≤ n) (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f)
    (himm : ∀ y, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) f y))
    (W : Set M) (hWopen : IsOpen W) (hWcpt : IsCompact (closure W))
    (p₁ p₂ r₁ r₂ : M) (hp₁p₂ : p₁ ≠ p₂) (hr₁r₂ : r₁ ≠ r₂)
    (hfp : f p₁ = f p₂) (hfr : f r₁ = f r₂)
    (hpre : ∀ y : M, f y = f p₂ → y = p₁ ∨ y = p₂)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = r₁ ∧ z = r₂) ∨ (y = r₂ ∧ z = r₁))
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (hp₁ : p₁ ∈ W) (hp₂ : p₂ ∈ W)
    (htrans : (mfderiv (𝓡 n) (𝓡 (2 * n)) f p₁).range ⊔
      (mfderiv (𝓡 n) (𝓡 (2 * n)) f p₂).range = ⊤)
    (R : ℝ) (hR : 0 < R)
    (hcleanR : ∀ y z : M, ‖f y - f p₂‖ < R → ‖f z - f p₂‖ < R → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = r₁ ∧ z = r₂) ∨ (y = r₂ ∧ z = r₁)),
    ∃ (K : Set M) (S : Set (EuclideanSpace ℝ (Fin (2 * n))))
      (ψ σ : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n))),
      IsClosed K ∧ IsOpen S ∧ p₁ ∈ K ∧ p₂ ∉ K ∧ K ⊆ W ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) σ ∧
      Function.LeftInverse σ ψ ∧ Function.RightInverse σ ψ ∧
      (∀ y, ψ y ≠ y → y ∈ S) ∧ S ⊆ Metric.ball (f p₂) (2 * R) ∧
      f '' frontier K ⊆ (closure S)ᶜ ∧
      (∀ y, ‖ψ y - y‖ ≤ 3 * R) ∧
      (∀ z ∈ K, ‖f z - f p₂‖ < R) ∧
      (∀ x : M, x ∈ W → x ∉ K → ∀ z : M, ψ (f x) = f z → z ∈ W ∧ z ∉ K) ∧
      σ (f p₂) ∉ f '' (Set.univ : Set M)

/-- **The Whitney push, atlas-free.**  Given a compact `M` (`n ≥ 3`), a smooth immersion `f`, an
open clean region `W` with compact closure on which `f` is injective except at exactly two double
points `(p₁,p₂)`, `(q₁,q₂)`, and the two bigon arcs, the target-side push data
(`Work.Whitney.HasAmbientPushData`) exists.

This is `Work.Whitney.HasAmbientPush` with the oriented atlas `A` and the sign hypothesis dropped:
by the docstring of `Work.Whitney.ambient_push_data_full` neither is used in the construction. -/
def HasPushNF (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M] : Prop :=
  ∀ (hn : 3 ≤ n) (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f)
    (himm : ∀ y, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) f y))
    (W : Set M) (hWopen : IsOpen W) (hWcpt : IsCompact (closure W))
    (p₁ p₂ q₁ q₂ : M)
    (hW₁ : p₁ ∈ W) (hW₂ : p₂ ∈ W) (hW₃ : q₁ ∈ W) (hW₄ : q₂ ∈ W)
    (hp₁p₂ : p₁ ≠ p₂) (hq₁q₂ : q₁ ≠ q₂)
    (hp₁q₁ : p₁ ≠ q₁) (hp₁q₂ : p₁ ≠ q₂) (hp₂q₁ : p₂ ≠ q₁) (hp₂q₂ : p₂ ≠ q₂)
    (hfp : f p₁ = f p₂) (hfq : f q₁ = f q₂)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁))
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (γ₁ γ₂ : ℝ → M) (hγ₁ : Continuous γ₁) (hγ₂ : Continuous γ₂)
    (hγ₁0 : γ₁ 0 = p₁) (hγ₁1 : γ₁ 1 = q₁) (hγ₂0 : γ₂ 0 = p₂) (hγ₂1 : γ₂ 1 = q₂)
    (hγW₁ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ∈ W)
    (hγW₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t ∈ W)
    (hγ₁inj : Set.InjOn γ₁ (Set.Icc (0 : ℝ) 1))
    (hγ₂inj : Set.InjOn γ₂ (Set.Icc (0 : ℝ) 1))
    (hγdisj : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      γ₁ s = γ₂ t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hγend : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      f (γ₁ s) = f (γ₂ t) → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)),
    HasAmbientPushData f W p₁ p₂ q₁ q₂

/-- **The Whitney cancellation, atlas-free.**  This is `Work.Whitney.HasCancellation` with the
oriented atlas and the sign hypothesis dropped. -/
def HasCancelNF (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M] : Prop :=
  ∀ (hn : 3 ≤ n) (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f)
    (himm : ∀ y, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) f y))
    (W : Set M) (hWopen : IsOpen W) (hWcpt : IsCompact (closure W))
    (p₁ p₂ q₁ q₂ : M)
    (hW₁ : p₁ ∈ W) (hW₂ : p₂ ∈ W) (hW₃ : q₁ ∈ W) (hW₄ : q₂ ∈ W)
    (hp₁p₂ : p₁ ≠ p₂) (hq₁q₂ : q₁ ≠ q₂)
    (hp₁q₁ : p₁ ≠ q₁) (hp₁q₂ : p₁ ≠ q₂) (hp₂q₁ : p₂ ≠ q₁) (hp₂q₂ : p₂ ≠ q₂)
    (hfp : f p₁ = f p₂) (hfq : f q₁ = f q₂)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁))
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (γ₁ γ₂ : ℝ → M) (hγ₁ : Continuous γ₁) (hγ₂ : Continuous γ₂)
    (hγ₁0 : γ₁ 0 = p₁) (hγ₁1 : γ₁ 1 = q₁) (hγ₂0 : γ₂ 0 = p₂) (hγ₂1 : γ₂ 1 = q₂)
    (hγW₁ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ∈ W)
    (hγW₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t ∈ W)
    (hγ₁inj : Set.InjOn γ₁ (Set.Icc (0 : ℝ) 1))
    (hγ₂inj : Set.InjOn γ₂ (Set.Icc (0 : ℝ) 1))
    (hγdisj : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      γ₁ s = γ₂ t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hγend : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      f (γ₁ s) = f (γ₂ t) → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)),
    ∃ (f' : M → EuclideanSpace ℝ (Fin (2 * n))),
      ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f' ∧
      (∀ y, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) f' y)) ∧
      (∀ y : M, y ∉ W → f' y = f y) ∧
      doubleSet f' = doubleSet f \ {(p₁, p₂), (p₂, p₁), (q₁, q₂), (q₂, q₁)} ∧
      (∀ (u v : M), u ∉ W → v ∉ W →
        ∀ (c₁ c₂ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))),
          u ∈ c₁.source → v ∈ c₂.source →
          pairDet f' c₁ c₂ u v = pairDet f c₁ c₂ u v)

/-- **The push gives the cancellation.**  Immediate from the already proved
`Work.Whitney.cancellation_of_pushData`, whose hypotheses are orientation-free. -/
theorem hasCancelNF_of_hasPushNF {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (h : HasPushNF n M) : HasCancelNF n M := by
  intro hn f hf himm W hWopen hWcpt p₁ p₂ q₁ q₂ hW₁ hW₂ hW₃ hW₄ hp₁p₂ hq₁q₂
    hp₁q₁ hp₁q₂ hp₂q₁ hp₂q₂ hfp hfq hclean hsep γ₁ γ₂ hγ₁ hγ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1
    hγW₁ hγW₂ hγ₁inj hγ₂inj hγdisj hγend
  obtain ⟨W₀, O, ψ, σ, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅,
    h₁₆⟩ := h hn f hf himm W hWopen hWcpt p₁ p₂ q₁ q₂ hW₁ hW₂ hW₃ hW₄ hp₁p₂ hq₁q₂
      hp₁q₁ hp₁q₂ hp₂q₁ hp₂q₂ hfp hfq hclean hsep γ₁ γ₂ hγ₁ hγ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1
      hγW₁ hγW₂ hγ₁inj hγ₂inj hγdisj hγend
  exact cancellation_of_pushData hn f hf himm W hWopen p₁ p₂ q₁ q₂ hW₁ hW₂ hW₃ hW₄ hclean hsep
    W₀ O ψ σ h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₂ h₁₃ h₁₀ h₁₁ h₁₄ h₁₅ h₁₆


/-- **A single double point inserted into `f`, atlas-free.**  This is
`Work.Whitney.InsertedDoublePoint` with the oriented atlas and the sign field removed; every
remaining field is orientation-free. -/
structure InsertedDP {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (p₁ p₂ : M)
    (f' : M → EuclideanSpace ℝ (Fin (2 * n))) (p' q' : M) : Prop where
  contMDiff : ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f'
  injective_mfderiv : ∀ y, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) f' y)
  doubleSet_eq : doubleSet f' = doubleSet f ∪ {(p', q'), (q', p')}
  finite_doubleSet : (doubleSet f').Finite
  simple_new : ∀ z : M, f' z = f' p' → z = p' ∨ z = q'
  simple_old : ∀ z : M, f' z = f' p₁ → z = p₁ ∨ z = p₂
  distinct : p' ≠ q' ∧ p' ≠ p₁ ∧ p' ≠ p₂ ∧ q' ≠ p₁ ∧ q' ≠ p₂ ∧ p₁ ≠ p₂
  new_not_old : (p', q') ∉ doubleSet f

/-- **The interface of the insertion step, atlas-free.** -/
def HasInsertionNF (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M] : Prop :=
  ∀ (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f)
    (himm : ∀ y, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) f y))
    (hfin : (doubleSet f).Finite)
    (hsimple : SimpleDP f) (htrans : TransDP' f)
    (p₁ p₂ : M) (hp₁p₂ : p₁ ≠ p₂) (hfp : f p₁ = f p₂),
    ∃ (f' : M → EuclideanSpace ℝ (Fin (2 * n))) (p' q' : M),
      InsertedDP f p₁ p₂ f' p' q' ∧ SimpleDP f' ∧ TransDP' f'

/-- **The interface of the reduction step**, atlas-free: one double point is removed while the two
invariants are preserved. -/
def HasReduceNF (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M] : Prop :=
  ∀ (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f)
    (himm : ∀ y, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) f y))
    (hfin : (doubleSet f).Finite)
    (hsimple : SimpleDP f) (htrans : TransDP' f)
    (p₁ p₂ : M) (hp₁p₂ : p₁ ≠ p₂) (hfp : f p₁ = f p₂),
    ∃ f'' : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f'' ∧
      (∀ y, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) f'' y)) ∧
      (doubleSet f'').Finite ∧
      (doubleSet f'').ncard + 2 = (doubleSet f).ncard ∧
      SimpleDP f'' ∧ TransDP' f''

/-- **The reduction step of the Whitney endgame, atlas-free.** -/
theorem exists_reduce_double_points_NF {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M]
    (hins : HasInsertionNF n M) (hcancel : HasCancelNF n M)
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f)
    (himm : ∀ y, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) f y))
    (hfin : (doubleSet f).Finite)
    (hsimple : SimpleDP f) (htrans : TransDP' f)
    (p₁ p₂ : M) (hp₁p₂ : p₁ ≠ p₂) (hfp : f p₁ = f p₂) :
    ∃ f'' : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f'' ∧
      (∀ y, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) f'' y)) ∧
      (doubleSet f'').Finite ∧
      (doubleSet f'').ncard + 2 = (doubleSet f).ncard ∧
      SimpleDP f'' ∧ TransDP' f'' := by
  classical
  -- ## Step 1: insert a double point at a clean point.
  obtain ⟨f', p', q', hins', hsimple', htrans'⟩ :=
    hins f hf himm hfin hsimple htrans p₁ p₂ hp₁p₂ hfp
  have hf'c := hins'.contMDiff
  have hf'imm := hins'.injective_mfderiv
  have hds := hins'.doubleSet_eq
  have hf'fin := hins'.finite_doubleSet
  have hnewold := hins'.new_not_old
  obtain ⟨hp'q', hp'p₁, hp'p₂, hq'p₁, hq'p₂, -⟩ := hins'.distinct
  -- `(p₁,p₂)` and `(p',q')` are double points of `f'`
  have hmem₁₂ : (p₁, p₂) ∈ doubleSet f' := by
    rw [hds]; left; rw [mem_doubleSet]; exact ⟨hp₁p₂, hfp⟩
  have hmem' : (p', q') ∈ doubleSet f' := by rw [hds]; right; simp
  have hfp' : f' p₁ = f' p₂ := (mem_doubleSet.mp hmem₁₂).2
  have hfq' : f' p' = f' q' := (mem_doubleSet.mp hmem').2
  have hs₁ : ∀ z : M, f' z = f' p₁ → z = p₁ ∨ z = p₂ := fun z hz => hsimple' _ hmem₁₂ z hz
  have hs₂ : ∀ z : M, f' z = f' p' → z = p' ∨ z = q' := fun z hz => hsimple' _ hmem' z hz
  -- the finite set of double point preimages of `f'`
  set D : Set M := {y : M | ∃ z : M, z ≠ y ∧ f' z = f' y} with hDdef
  have hDmem : ∀ y : M, y ∈ D ↔ ∃ z : M, z ≠ y ∧ f' z = f' y := fun y => Iff.rfl
  have hDfin : D.Finite := by
    have h1 : D = Prod.fst '' (doubleSet f') := by
      ext y
      constructor
      · rintro ⟨z, hzy, hfz⟩
        exact ⟨(y, z), ⟨hzy.symm, hfz.symm⟩, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w.2, hw.1.symm, hw.2.symm⟩
    rw [h1]
    exact hf'fin.image Prod.fst
  have hp₁D : p₁ ∈ D := (hDmem p₁).mpr ⟨p₂, hp₁p₂.symm, hfp'.symm⟩
  have hp₂D : p₂ ∈ D := (hDmem p₂).mpr ⟨p₁, hp₁p₂, hfp'⟩
  have hp'D : p' ∈ D := (hDmem p').mpr ⟨q', hp'q'.symm, hfq'.symm⟩
  have hq'D : q' ∈ D := (hDmem q').mpr ⟨p', hp'q', hfq'⟩
  -- ## Step 2: the two arcs of the bigon, avoiding all other double points.
  obtain ⟨γ₁, γ₂, hγ₁c, hγ₂c, hγ₁0, hγ₁1, hγ₂0, hγ₂1, hγ₁inj, hγ₂inj,
    hγ₁D, hγ₂D, hγdisj⟩ :=
    exists_disjoint_arcs_avoiding_finite (n := n) hn D hDfin p₁ p₂ p' q'
      hp₁p₂ hp'q' hp'p₁.symm hq'p₁.symm hp'p₂.symm hq'p₂.symm
  -- the endpoints are the only points of the arcs which lie in `D`
  have hend₁ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t = p₁ → t = 0 := by
    intro t ht h
    have hD : γ₁ t ∈ D := by rw [h]; exact hp₁D
    rcases hγ₁D t ht hD with h0 | h1
    · exact h0
    · exfalso
      subst h1
      rw [hγ₁1] at h
      exact hp'p₁ h
  have hend₁' : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t = p' → t = 1 := by
    intro t ht h
    have hD : γ₁ t ∈ D := by rw [h]; exact hp'D
    rcases hγ₁D t ht hD with h0 | h1
    · exfalso
      subst h0
      rw [hγ₁0] at h
      exact hp'p₁ h.symm
    · exact h1
  have hne₁p₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ≠ p₂ := by
    intro t ht h
    have hD : γ₁ t ∈ D := by rw [h]; exact hp₂D
    rcases hγ₁D t ht hD with h0 | h1
    · subst h0; rw [hγ₁0] at h; exact hp₁p₂ h
    · subst h1; rw [hγ₁1] at h; exact hp'p₂ h
  have hne₁q' : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ≠ q' := by
    intro t ht h
    have hD : γ₁ t ∈ D := by rw [h]; exact hq'D
    rcases hγ₁D t ht hD with h0 | h1
    · subst h0; rw [hγ₁0] at h; exact hq'p₁ h.symm
    · subst h1; rw [hγ₁1] at h; exact hp'q' h
  have hend₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t = p₂ → t = 0 := by
    intro t ht h
    have hD : γ₂ t ∈ D := by rw [h]; exact hp₂D
    rcases hγ₂D t ht hD with h0 | h1
    · exact h0
    · exfalso
      subst h1
      rw [hγ₂1] at h
      exact hq'p₂ h
  have hend₂' : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t = q' → t = 1 := by
    intro t ht h
    have hD : γ₂ t ∈ D := by rw [h]; exact hq'D
    rcases hγ₂D t ht hD with h0 | h1
    · exfalso
      subst h0
      rw [hγ₂0] at h
      exact hq'p₂ h.symm
    · exact h1
  -- ## Step 3: the clean region containing the arcs.
  obtain ⟨W, hWopen, hWcpt, hW₁, hW₂, hW₃, hW₄, hWchar, hWclean, hWsep, _⟩ :=
    exists_clean_region f' hf'fin p₁ p₂ p' q'
      hp₁p₂ hp'q' hp'p₁.symm hq'p₁.symm hp'p₂.symm hq'p₂.symm hfp' hfq'
      (fun z hz => hs₁ z hz) (fun z hz => hs₂ z hz)
  -- ## Step 4: the arcs lie in the clean region.
  have hmemW : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ∈ W := by
    intro t ht
    rcases eq_or_ne t 0 with h0 | h0
    · rw [h0, hγ₁0]; exact hW₁
    rcases eq_or_ne t 1 with h1 | h1
    · rw [h1, hγ₁1]; exact hW₃
    have hnotD : γ₁ t ∉ D := by
      intro hD
      rcases hγ₁D t ht hD with h | h
      · exact h0 h
      · exact h1 h
    rw [hWchar]
    exact Or.inl (by simpa [hDmem] using hnotD)
  have hmemW₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t ∈ W := by
    intro t ht
    rcases eq_or_ne t 0 with h0 | h0
    · rw [h0, hγ₂0]; exact hW₂
    rcases eq_or_ne t 1 with h1 | h1
    · rw [h1, hγ₂1]; exact hW₄
    have hnotD : γ₂ t ∉ D := by
      intro hD
      rcases hγ₂D t ht hD with h | h
      · exact h0 h
      · exact h1 h
    rw [hWchar]
    exact Or.inl (by simpa [hDmem] using hnotD)
  -- ## Step 5: the two image arcs meet only in the two double points (`hγend`).
  have hγend : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      f' (γ₁ s) = f' (γ₂ t) → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    intro s hs t ht heq
    rcases hWclean (γ₁ s) (γ₂ t) (hmemW s hs) (hmemW₂ t ht) heq with
      h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hγdisj s hs t ht h
    · exact Or.inl ⟨hend₁ s hs h1, hend₂ t ht h2⟩
    · exact absurd h1 (hne₁p₂ s hs)
    · exact Or.inr ⟨hend₁' s hs h1, hend₂' t ht h2⟩
    · exact absurd h1 (hne₁q' s hs)
  -- ## Step 6: cancel the pair `((p₁,p₂), (p',q'))`.
  obtain ⟨f'', hf''c, hf''imm, hout, hds'', hagree⟩ :=
    hcancel hn f' hf'c hf'imm W hWopen hWcpt p₁ p₂ p' q'
      hW₁ hW₂ hW₃ hW₄ hp₁p₂ hp'q' hp'p₁.symm hq'p₁.symm hp'p₂.symm hq'p₂.symm
      hfp' hfq' hWclean hWsep γ₁ γ₂ hγ₁c hγ₂c hγ₁0 hγ₁1 hγ₂0 hγ₂1
      hmemW hmemW₂ hγ₁inj hγ₂inj hγdisj hγend
  -- ## Step 7: the invariants survive.
  have hsub : doubleSet f'' ⊆ doubleSet f' := by rw [hds'']; exact Set.sdiff_subset
  have hsimple'' : SimpleDP f'' := by
    intro p hp z hz
    by_cases hzp : z = p.1
    · exact Or.inl hzp
    have hmem : (z, p.1) ∈ doubleSet f'' := by
      rw [mem_doubleSet]; exact ⟨hzp, hz⟩
    exact hsimple' p (hsub hp) z (mem_doubleSet.mp (hsub hmem)).2
  -- the double points of `f''` lie outside the clean region
  have hfst : ∀ a b : M, (a, b) ∈ doubleSet f'' → a ∉ W := by
    intro a b hab hW
    have hab' : (a, b) ∈ doubleSet f' := hsub hab
    obtain ⟨habne, habeq⟩ := mem_doubleSet.mp hab'
    have hnot4 : (a, b) ∉ ({(p₁, p₂), (p₂, p₁), (p', q'), (q', p')} : Set (M × M)) := by
      intro h4
      rw [hds''] at hab
      exact hab.2 h4
    rw [hWchar] at hW
    rcases hW with hW | hW | hW | hW | hW
    · exact hW ⟨b, habne.symm, habeq.symm⟩
    · -- `a = p₁`
      have h := hs₁ b (by rw [← habeq, hW])
      rcases h with h2 | h2
      · exact habne (by rw [hW, h2])
      · exact hnot4 (by simp [hW, h2])
    · -- `a = p₂`
      have h := hs₁ b (by rw [← habeq, hW, hfp'])
      rcases h with h2 | h2
      · exact hnot4 (by simp [hW, h2])
      · exact habne (by rw [hW, h2])
    · -- `a = p'`
      have h := hs₂ b (by rw [← habeq, hW])
      rcases h with h2 | h2
      · exact habne (by rw [hW, h2])
      · exact hnot4 (by simp [hW, h2])
    · -- `a = q'`
      have h := hs₂ b (by rw [← habeq, hW, hfq'])
      rcases h with h2 | h2
      · exact hnot4 (by simp [hW, h2])
      · exact habne (by rw [hW, h2])
  have hnotW : ∀ p : M × M, p ∈ doubleSet f'' → p.1 ∉ W ∧ p.2 ∉ W := fun p hp =>
    ⟨hfst p.1 p.2 hp, hfst p.2 p.1 (by rw [mem_doubleSet] at hp ⊢; exact ⟨hp.1.symm, hp.2.symm⟩)⟩
  have htrans'' : TransDP' f'' := by
    intro p hp
    obtain ⟨c₁, c₂, hc₁, hc₂, hp₁c, hp₂c, hpd⟩ := htrans' p (hsub hp)
    obtain ⟨hnotW₁, hnotW₂⟩ := hnotW p hp
    exact ⟨c₁, c₂, hc₁, hc₂, hp₁c, hp₂c,
      by rw [hagree p.1 p.2 hnotW₁ hnotW₂ c₁ c₂ hp₁c hp₂c]; exact hpd⟩
  -- ## Step 8: the cardinality bookkeeping.
  refine ⟨f'', hf''c, hf''imm, ?_, ?_, hsimple'', htrans''⟩
  · rw [hds'']; exact hf'fin.sdiff
  · have h1 : (doubleSet f'').ncard + 4 = (doubleSet f').ncard :=
      ncard_doubleSet_cancel f' f'' p₁ p₂ p' q'
        hp₁p₂ hp'q' hp'p₁.symm hq'p₁.symm hp'p₂.symm hq'p₂.symm hfp' hfq' hf'fin hds''
    have h2 : (doubleSet f').ncard = (doubleSet f).ncard + 2 :=
      ncard_doubleSet_insert f f' p' q' hp'q' hnewold hfin hds
    omega

/-- The reduction interface follows from the insertion and cancellation interfaces. -/
theorem hasReduceNF_of {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M]
    (hn : 3 ≤ n) (hins : HasInsertionNF n M) (hcancel : HasCancelNF n M) :
    HasReduceNF n M :=
  fun f hf himm hfin hsimple htrans p₁ p₂ hp₁p₂ hfp =>
    exists_reduce_double_points_NF (M := M) hn hins hcancel f hf himm hfin hsimple htrans
      p₁ p₂ hp₁p₂ hfp

/-- **The endgame, atlas-free.**  If every simple double point can be removed (together with a
freshly inserted partner), then any smooth immersion of a compact connected `n`-manifold
(`n ≥ 3`) with finitely many simple transverse double points can be improved to a smooth
embedding. -/
theorem exists_embedding_of_reduce_NF {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M]
    (hred : HasReduceNF n M)
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f)
    (himm : ∀ y, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) f y))
    (hfin : (doubleSet f).Finite) (hsimple : SimpleDP f) (htrans : TransDP' f) :
    ∃ e : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ e ∧
      IsEmbedding e ∧
      ∀ x : M, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) e x) := by
  classical
  suffices H : ∀ k : ℕ, ∀ f : M → EuclideanSpace ℝ (Fin (2 * n)),
      (doubleSet f).ncard = k →
      ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f →
      (∀ y, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) f y)) →
      (doubleSet f).Finite → SimpleDP f → TransDP' f →
      ∃ e : M → EuclideanSpace ℝ (Fin (2 * n)),
        ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ e ∧
        IsEmbedding e ∧
        ∀ x : M, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) e x) from
    H (doubleSet f).ncard f rfl hf himm hfin hsimple htrans
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro f hk hf himm hfin hsimple htrans
    by_cases hempty : (doubleSet f).Nonempty
    · obtain ⟨P, hP⟩ := hempty
      obtain ⟨hPne, hPeq⟩ := mem_doubleSet.mp hP
      obtain ⟨f'', hf''c, hf''imm, hf''fin, hcard, hsimple'', htrans''⟩ :=
        hred f hf himm hfin hsimple htrans P.1 P.2 hPne hPeq
      have hk' : (doubleSet f'').ncard < k := by omega
      exact ih (doubleSet f'').ncard hk' f'' rfl hf''c hf''imm hf''fin hsimple'' htrans''
    · have hinj : Function.Injective f := by
        intro x y hxy
        by_contra hne
        exact hempty ⟨(x, y), by rw [mem_doubleSet]; exact ⟨hne, hxy⟩⟩
      exact ⟨f, hf, isEmbedding_of_injective_of_compactSpace f hf hinj, himm⟩

/-- **The compact connected branch of Whitney's strong embedding theorem, atlas-free.**  A compact
connected smooth `n`-manifold (`n ≥ 3`), *without any orientability hypothesis*, admits a smooth
embedding into `ℝ^{2n}` with injective derivative, given the push and the insertion and the
existence of an immersion with finitely many simple transverse double points in general position. -/
theorem exists_embedding_of_compact_connected_NF {n : ℕ} (hn : 3 ≤ n) {M : Type*}
    [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M]
    (hpush : HasPushNF n M) (hins : HasInsertionNF n M)
    (hgen : ∃ g : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ g ∧
      (∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) g x)) ∧
      (doubleSet g).Finite ∧ SimpleDP g ∧
      (∀ p : M × M, p ∈ doubleSet g →
        (mfderiv (𝓡 n) (𝓡 (2 * n)) g p.1).range ⊔
        (mfderiv (𝓡 n) (𝓡 (2 * n)) g p.2).range = ⊤)) :
    ∃ e : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ e ∧
      IsEmbedding e ∧
      ∀ x : M, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) e x) := by
  obtain ⟨g, hg, hgimm, hgfin, hgsimple, hgtrans⟩ := hgen
  exact exists_embedding_of_reduce_NF hn (hasReduceNF_of hn hins (hasCancelNF_of_hasPushNF hpush))
    g hg hgimm hgfin hgsimple (transDP'_of_range hg hgtrans)

/-- **The compact branch of Whitney's strong embedding theorem, atlas-free.**  A compact smooth
`n`-manifold (`n ≥ 3`), *orientable or not*, admits a smooth embedding into `ℝ^{2n}` with injective
derivative, given the push and the insertion on each compact open submanifold.  The general
position input is supplied by `Work.Whitney.exists_simple_transverse_immersion`. -/
theorem exists_embedding_of_compact_NF {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (hpush : ∀ (U : TopologicalSpace.Opens M) [CompactSpace U], HasPushNF n U)
    (hins : ∀ (U : TopologicalSpace.Opens M) [CompactSpace U], HasInsertionNF n U) :
    ∃ e : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ e ∧
      IsEmbedding e ∧
      ∀ x : M, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) e x) := by
  classical
  refine Work.Embedding.exists_embedding_of_components (n := n) (by omega) ?_
  intro U hUconn hUcpt
  haveI : CompactSpace U := isCompact_iff_compactSpace.mp hUcpt
  haveI : ConnectedSpace U := isConnected_iff_connectedSpace.mp hUconn
  exact exists_embedding_of_compact_connected_NF hn (hpush U) (hins U)
    (exists_simple_transverse_immersion (n := n) hn)

end Work.Whitney
