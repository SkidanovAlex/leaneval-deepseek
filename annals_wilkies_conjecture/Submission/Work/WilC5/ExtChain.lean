/-
  WilC5 — the Zorn step for Sacks' extension property.

  `Work.WilC5.HasExtProp L T` (Sacks' quantifier-elimination test, `ExtQE.lean`) is proved by
  Zorn's lemma: the partial data are pairs `(A, σ)` where `A` is a substructure of `M` modelling
  `T`, `A ⊇ A₀`, and `σ : A → N` is an embedding extending `σ₀ : A₀ → N`.

  This module holds that partial order and its basic API, so that the chain/union step and the
  final assembly can refer to one notion:

  * `ExtPair T A₀ σ₀` — the type of such partial extensions;
  * its `Preorder` (larger domains, compatible embeddings);
  * `ExtPair.base` — the initial element `(A₀, σ₀)`, available as soon as every substructure of
    `M` models `T`;
  * `ExtPair.le_dom_of_le`, `ExtPair.le_emb` and `ExtPair.compat_of_chain` — the compatibility
    lemmas used when taking unions along a chain.
-/
import Mathlib
import Submission.Work.WilC5.ExtQE

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC5

open FirstOrder Language

/-- **A partial extension of an embedding.**  `p : ExtPair T A₀ σ₀` consists of a substructure
`p.dom ⊇ A₀` of `M` which is a model of `T`, together with an embedding `p.emb : p.dom → N`
extending the given embedding `σ₀ : A₀ → N`. -/
structure ExtPair {L : FirstOrder.Language.{0, 0}} (T : L.Theory) {M N : Type}
    [L.Structure M] [L.Structure N] (A₀ : L.Substructure M) (σ₀ : L.Embedding A₀ N) where
  dom : L.Substructure M
  emb : L.Embedding dom N
  le_dom : A₀ ≤ dom
  agrees : ∀ a : A₀, emb ⟨(a : M), le_dom a.2⟩ = σ₀ a
  models : (dom : Type) ⊨ T

namespace ExtPair

variable {L : FirstOrder.Language.{0, 0}} {T : L.Theory}
variable {M N : Type} [L.Structure M] [L.Structure N]
variable {A₀ : L.Substructure M} {σ₀ : L.Embedding A₀ N}

/-- `p ≤ q` means that `q` extends `p`: `q.dom ⊇ p.dom` and `q.emb` restricts to `p.emb`. -/
abbrev le (p q : ExtPair T A₀ σ₀) : Prop :=
  ∃ h : p.dom ≤ q.dom, ∀ a : p.dom, q.emb ⟨(a : M), h a.2⟩ = p.emb a

instance instLE : LE (ExtPair T A₀ σ₀) := ⟨le⟩

instance instPreorder : Preorder (ExtPair T A₀ σ₀) :=
  { instLE with
    le_refl := fun p => ⟨le_refl p.dom, fun a => congrArg p.emb (Subtype.ext rfl)⟩
    le_trans := fun p q r hpq hqr => by
      rcases hpq with ⟨h1, h2⟩
      rcases hqr with ⟨h3, h4⟩
      refine ⟨h1.trans h3, fun a => ?_⟩
      have h4' := h4 (⟨(a : M), h1 a.2⟩ : q.dom)
      have h2' := h2 a
      simp only at h4' h2'
      rw [h4', h2']
    lt := fun p q => p ≤ q ∧ ¬ q ≤ p
    lt_iff_le_not_ge := fun _ _ => Iff.rfl }

/-- The domain of an extension is a larger substructure. -/
theorem le_dom_of_le {p q : ExtPair T A₀ σ₀} (h : p ≤ q) : p.dom ≤ q.dom := h.choose

/-- The embedding of an extension restricts to the smaller one. -/
theorem le_emb {p q : ExtPair T A₀ σ₀} (h : p ≤ q) (a : p.dom) (hq : (a : M) ∈ q.dom) :
    q.emb ⟨(a : M), hq⟩ = p.emb a := by
  have h' := h.choose_spec a
  convert h' using 2

/-- Any two members of a chain of partial extensions agree on the intersection of their domains. -/
theorem compat_of_chain {c : Set (ExtPair T A₀ σ₀)} (hc : IsChain (· ≤ ·) c)
    {A B : ExtPair T A₀ σ₀} (hA : A ∈ c) (hB : B ∈ c) {x : M}
    (hxA : x ∈ A.dom) (hxB : x ∈ B.dom) : A.emb ⟨x, hxA⟩ = B.emb ⟨x, hxB⟩ := by
  rcases eq_or_ne A B with h | h
  · subst h; rfl
  · rcases hc hA hB h with hle | hle
    · exact (le_emb hle ⟨x, hxA⟩ hxB).symm
    · exact le_emb hle ⟨x, hxB⟩ hxA

/-- The initial element of the Zorn poset: the identity extension of `σ₀` to `A₀`.  It exists as
soon as every substructure of `M` is a model of `T` (`hmod`), which is how the test is applied. -/
def base (hmod : ∀ A : L.Substructure M, (A : Type) ⊨ T) : ExtPair T A₀ σ₀ where
  dom := A₀
  emb := σ₀
  le_dom := le_refl A₀
  agrees := fun a => congrArg σ₀ (Subtype.ext rfl)
  models := hmod A₀

/-- The base element is below every element (they all extend `(A₀, σ₀)`). -/
theorem base_le (hmod : ∀ A : L.Substructure M, (A : Type) ⊨ T)
    (p : ExtPair T A₀ σ₀) : base (σ₀ := σ₀) hmod ≤ p :=
  ⟨p.le_dom, fun a => p.agrees a⟩

end ExtPair

end Work.WilC5
