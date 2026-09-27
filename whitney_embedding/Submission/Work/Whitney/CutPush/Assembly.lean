import Mathlib
import Submission.Work.Whitney.CutPush.Localisation
import Submission.Work.Whitney.CutPush.Model
import Submission.Work.Whitney.PushSigned
import Submission.Work.Whitney.CutPush.Frontier

/-!
# The cut push: the interface and its assembly

This module isolates the *geometric* content of the signed cut (collar) push from its
*topological* content, and proves the latter.

`Work.Whitney.CutPush.HasCutPushData` is the interface: a single ambient diffeomorphism pair
`(ψ, σ)` of the target (the "finger" of the Whitney move), the two closed *cuts* `K_P ∋ p₁`,
`K_Q ∋ q₁`, its open support `V`, and the clauses the finger has to satisfy --- the frontier clause
and the cut clause on `W \ (K_P ∪ K_Q)`, and the non-attainment of the two double point values.

From this data, `hasPushSigned_of_hasCutPushData` produces `Work.Whitney.HasAmbientPushData`:
taking `W₀ := W \ (K_P ∪ K_Q)`, `O := (closure V)ᶜ` and `ψ`, `σ` as given, the frontier clause
becomes the fixed-region clause and the cut clause becomes the placement clause (via
`Work.Whitney.CutPush.placement_of_cutForm`).

The proof of `HasCutPushData` is the remaining geometric input of the compact case: the Whitney
finger sweeping the collar of the arc `γ₂` across the bigon, where the framing hypothesis
`OppositeType f γ₁ γ₂ p₁ p₂ q₁ q₂` enters.  See `Submission/Work/Whitney/CutPush/README.md` for the
obstructions that determine the shape of the support (`§4`), the construction (`§6`) and why the
single collar push is the right interface (`§7`).

Both halves of the history are represented here: an earlier version of this module used *two*
fingers `ψ_P ∘ ψ_Q` with their own cuts; the single-push form above is the one the construction
actually produces, and it is what the requester's `Work.Whitney.hasCutPushData_holds` consumes.
-/

namespace Work.Whitney.CutPush

open scoped Manifold ContDiff
open Topology

set_option linter.unusedVariables false


/-- **The geometric input of the signed cut push: the collar push.**

For every set of data of `Work.Whitney.HasPushSigned` (in particular for every pair of double
points of opposite type along the two arcs) there are

* closed cuts `K_P ∋ p₁`, `K_Q ∋ q₁`, inside `W`, with `p₂, q₂ ∉ K_P ∪ K_Q`;
* an open support `V` of the target and a pair `(ψ, σ)` of mutually inverse `C^∞`
  self-diffeomorphisms of the target, `ψ` the identity off `V`;

such that `f '' frontier (W \ (K_P ∪ K_Q))` avoids `closure V` (the *frontier clause*, i.e. `ψ` is
the identity on a neighbourhood of the image of the frontier), the *cut clause*
`ψ (f x) = f z → z ∈ W \ (K_P ∪ K_Q) ∨ z = p₁ ∨ z = q₁` holds for `x ∈ W \ (K_P ∪ K_Q)`, and the
two values `f p₂`, `f q₂` are not attained by `ψ` on the pushed sheet.

This is the "finger move" of Whitney's trick, in the shape that the construction actually has: a
*single* push whose support is a collar enclosing both double points (so that its total algebraic
intersection number with the other sheets is `1 + (-1) = 0`, the opposite-type hypothesis).  Note
that the support cannot be bounded by a ball around one double point: see `README.md` §4 for the
linking obstruction which refutes every such interface (and §7 for why "apply
`Work.Whitney.local_push_manifold` twice" stops one ingredient short, so that the single collar push
is the right interface). -/
def HasCutPushData (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M] : Prop :=
  ∀ (hn : 3 ≤ n) (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
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
    (htransP : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₁).range ⊔
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₂).range = ⊤)
    (htransQ : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f q₁).range ⊔
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f q₂).range = ⊤)
    (γ₁ γ₂ : ℝ → M) (hγ₁ : Continuous γ₁) (hγ₂ : Continuous γ₂)
    (hγ₁0 : γ₁ 0 = p₁) (hγ₁1 : γ₁ 1 = q₁) (hγ₂0 : γ₂ 0 = p₂) (hγ₂1 : γ₂ 1 = q₂)
    (hγW₁ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ∈ W)
    (hγW₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t ∈ W)
    (hγ₁inj : Set.InjOn γ₁ (Set.Icc (0 : ℝ) 1))
    (hγ₂inj : Set.InjOn γ₂ (Set.Icc (0 : ℝ) 1))
    (hγdisj : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      γ₁ s = γ₂ t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hγend : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      f (γ₁ s) = f (γ₂ t) → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hsign : OppositeType f γ₁ γ₂ p₁ p₂ q₁ q₂),
    ∃ (K_P K_Q : Set M) (V : Set (EuclideanSpace ℝ (Fin (2 * n))))
      (ψ σ : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n))),
      IsClosed K_P ∧ IsClosed K_Q ∧ K_P ⊆ W ∧ K_Q ⊆ W ∧
      p₁ ∈ K_P ∧ q₁ ∈ K_Q ∧ p₂ ∉ K_P ∧ p₂ ∉ K_Q ∧ q₂ ∉ K_P ∧ q₂ ∉ K_Q ∧
      IsOpen V ∧
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) σ ∧
      (∀ y, σ (ψ y) = y) ∧ (∀ y, ψ (σ y) = y) ∧
      (∀ y, y ∉ V → ψ y = y) ∧
      (∀ x : M, x ∈ frontier (W \ (K_P ∪ K_Q)) → f x ∉ closure V) ∧
      (∀ x : M, x ∈ W \ (K_P ∪ K_Q) → ∀ z : M,
        ψ (f x) = f z → z ∈ W \ (K_P ∪ K_Q) ∨ z = p₁ ∨ z = q₁) ∧
      f p₂ ∉ ψ '' (f '' (W \ (K_P ∪ K_Q))) ∧
      f q₂ ∉ ψ '' (f '' (W \ (K_P ∪ K_Q)))


/-- **The assembly: the collar push gives the signed push.**  Taking `W₀ := W \ (K_P ∪ K_Q)`,
`O := (closure V)ᶜ`, and `ψ`, `σ` as given, all clauses of `Work.Whitney.HasAmbientPushData` follow:
openness and the position of the four points are immediate, the fixed-region clause is the frontier
clause in the form `f '' frontier W₀ ⊆ O`, and the placement clause is the given cut clause in the
form of `Work.Whitney.CutPush.placement_of_cutForm`. -/
theorem hasPushSigned_of_hasCutPushData {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (h : HasCutPushData n M) : Work.Whitney.HasPushSigned n M := by
  intro hn f hf himm W hWopen hWcpt p₁ p₂ q₁ q₂ hW₁ hW₂ hW₃ hW₄ hp₁p₂ hq₁q₂
    hp₁q₁ hp₁q₂ hp₂q₁ hp₂q₂ hfp hfq hclean hsep htransP htransQ γ₁ γ₂ hγ₁ hγ₂ hγ₁0 hγ₁1
    hγ₂0 hγ₂1 hγW₁ hγW₂ hγ₁inj hγ₂inj hγdisj hγend hsign
  obtain ⟨K_P, K_Q, V, ψ, σ, hKPcl, hKQcl, hKPW, hKQW, hp₁KP, hq₁KQ, hp₂KP, hp₂KQ, hq₂KP,
    hq₂KQ, hVo, hψsm, hσsm, hσψ, hψσ, hfix, hfront, hcut, hne₁, hne₂⟩ :=
    h hn f hf himm W hWopen hWcpt p₁ p₂ q₁ q₂ hW₁ hW₂ hW₃ hW₄ hp₁p₂ hq₁q₂
      hp₁q₁ hp₁q₂ hp₂q₁ hp₂q₂ hfp hfq hclean hsep htransP htransQ γ₁ γ₂ hγ₁ hγ₂ hγ₁0 hγ₁1
      hγ₂0 hγ₂1 hγW₁ hγW₂ hγ₁inj hγ₂inj hγdisj hγend hsign
  set W₀ : Set M := W \ (K_P ∪ K_Q) with hW₀def
  have hW₀open : IsOpen W₀ := hWopen.sdiff (hKPcl.union hKQcl)
  have hW₀sub : W₀ ⊆ W := fun x hx => hx.1
  have hp₂W₀ : p₂ ∈ W₀ := ⟨hW₂, by simp [hp₂KP, hp₂KQ]⟩
  have hq₂W₀ : q₂ ∈ W₀ := ⟨hW₄, by simp [hq₂KP, hq₂KQ]⟩
  have hp₁W₀ : p₁ ∉ W₀ := fun hx => hx.2 (Or.inl hp₁KP)
  have hq₁W₀ : q₁ ∉ W₀ := fun hx => hx.2 (Or.inr hq₁KQ)
  have hOopen : IsOpen ((closure V)ᶜ) := isClosed_closure.isOpen_compl
  have hfrontO : f '' frontier W₀ ⊆ (closure V)ᶜ := by
    rintro y ⟨x, hx, rfl⟩
    exact hfront x hx
  have hψid : ∀ y ∈ (closure V)ᶜ, ψ y = y := fun y hy => hfix y (fun h => hy (subset_closure h))
  have hplace : ψ '' (f '' W₀) ⊆ f '' W₀ ∪ (f '' (Set.univ : Set M))ᶜ :=
    placement_of_cutForm hp₂W₀ hq₂W₀ hfp hfq fun x hx z hz => hcut x hx z hz
  refine ⟨W₀, (closure V)ᶜ, ψ, σ, hW₀open, hW₀sub, hp₂W₀, hq₂W₀, hp₁W₀, hq₁W₀, hOopen,
    hfrontO, hψid, hσψ, hψσ, hψsm, hσsm, hplace, ?_, ?_⟩
  · exact hne₁
  · exact hne₂

end Work.Whitney.CutPush
