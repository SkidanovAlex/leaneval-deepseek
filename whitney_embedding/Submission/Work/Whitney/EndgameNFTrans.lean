import Mathlib
import Submission.Work.Whitney.EndgameNF
import Submission.Work.Whitney.hasAmbientPushData_of_localPushTrans
import Submission.Work.Whitney.hasInsertionNF

/-!
# The `Trans`-variant of the endgame (transversality-carrying inputs)

`Work.Whitney.LocalPushNTrans` (the cut form of the local Whitney push at a *transverse* double
point, proved in `Submission/Work/Whitney/localPushNTrans_holds.lean`) requires the two double
points to be transverse.  The endgame interfaces of `Submission/Work/Whitney/EndgameNF.lean`
(`HasPushNF`, `HasCancelNF`, ...) do **not** carry that hypothesis, so they cannot be instantiated
from it.  This file repeats the endgame with the transversality of the two double points carried
along, and derives the extra hypotheses from the `TransDP'` certificate produced by the insertion
step (`Work.Whitney.trans_of_transDP'`).

Everything else is verbatim the `EndgameNF` development.
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology

set_option linter.unusedVariables false

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

/-- **Intrinsic transversality at a double point, from the chart certificate `TransDP'`.** -/
theorem trans_of_transDP' {f : M → EuclideanSpace ℝ (Fin (2 * n))}
    (hf : ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f)
    (h : TransDP' f) (p : M × M) (hp : p ∈ doubleSet f) :
    (mfderiv (𝓡 n) (𝓡 (2 * n)) f p.1).range ⊔
      (mfderiv (𝓡 n) (𝓡 (2 * n)) f p.2).range = ⊤ := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hp₁, hp₂, hpd⟩ := h p hp
  have htop : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  rw [← pairDet_ne_zero_iff f c₁ c₂ p.1 p.2 hp₁ hp₂
    ((hc₁.1.contMDiffAt (c₁.open_source.mem_nhds hp₁)).mdifferentiableAt htop)
    ((hc₂.1.contMDiffAt (c₂.open_source.mem_nhds hp₂)).mdifferentiableAt htop)
    ((hc₁.2.contMDiffAt (c₁.open_target.mem_nhds (c₁.map_source hp₁))).mdifferentiableAt htop)
    ((hc₂.2.contMDiffAt (c₂.open_target.mem_nhds (c₂.map_source hp₂))).mdifferentiableAt htop)
    ((hf p.1).mdifferentiableAt htop) ((hf p.2).mdifferentiableAt htop)]
  exact hpd

/-- **The Whitney push, atlas-free.**  Given a compact `M` (`n ≥ 3`), a smooth immersion `f`, an
open clean region `W` with compact closure on which `f` is injective except at exactly two double
points `(p₁,p₂)`, `(q₁,q₂)`, and the two bigon arcs, the target-side push data
(`Work.Whitney.HasAmbientPushData`) exists.

This is `Work.Whitney.HasAmbientPush` with the oriented atlas `A` and the sign hypothesis dropped:
by the docstring of `Work.Whitney.ambient_push_data_full` neither is used in the construction. -/
def HasPushNFT (n : ℕ) (M : Type*) [TopologicalSpace M]
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
    (htransP : (mfderiv (𝓡 n) (𝓡 (2 * n)) f p₁).range ⊔
      (mfderiv (𝓡 n) (𝓡 (2 * n)) f p₂).range = ⊤)
    (htransQ : (mfderiv (𝓡 n) (𝓡 (2 * n)) f q₁).range ⊔
      (mfderiv (𝓡 n) (𝓡 (2 * n)) f q₂).range = ⊤)
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


/-- **The `Trans`-variant of the push interface, from the local push at a transverse double
point.**  This is exactly the child theorem `Work.Whitney.hasAmbientPushData_of_localPushTrans`,
whose conclusion is the body of `HasPushNFT`. -/
theorem hasPushNFT_of_localPushNTrans {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (h : LocalPushNTrans n M) : HasPushNFT n M :=
  hasAmbientPushData_of_localPushTrans h

/-- The transversality-free push interface gives the `Trans`-variant. -/
theorem hasPushNFT_of_hasPushNF {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (h : HasPushNF n M) : HasPushNFT n M := by
  intro hn f hf himm W hWopen hWcpt p₁ p₂ q₁ q₂ hW₁ hW₂ hW₃ hW₄ hp₁p₂ hq₁q₂
    hp₁q₁ hp₁q₂ hp₂q₁ hp₂q₂ hfp hfq hclean hsep htransP htransQ γ₁ γ₂ hγ₁ hγ₂ hγ₁0 hγ₁1
    hγ₂0 hγ₂1 hγW₁ hγW₂ hγ₁inj hγ₂inj hγdisj hγend
  exact h hn f hf himm W hWopen hWcpt p₁ p₂ q₁ q₂ hW₁ hW₂ hW₃ hW₄ hp₁p₂ hq₁q₂
    hp₁q₁ hp₁q₂ hp₂q₁ hp₂q₂ hfp hfq hclean hsep γ₁ γ₂ hγ₁ hγ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1
    hγW₁ hγW₂ hγ₁inj hγ₂inj hγdisj hγend

/-- **The Whitney cancellation, atlas-free.**  This is `Work.Whitney.HasCancellation` with the
oriented atlas and the sign hypothesis dropped. -/
def HasCancelNFT (n : ℕ) (M : Type*) [TopologicalSpace M]
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
    (htransP : (mfderiv (𝓡 n) (𝓡 (2 * n)) f p₁).range ⊔
      (mfderiv (𝓡 n) (𝓡 (2 * n)) f p₂).range = ⊤)
    (htransQ : (mfderiv (𝓡 n) (𝓡 (2 * n)) f q₁).range ⊔
      (mfderiv (𝓡 n) (𝓡 (2 * n)) f q₂).range = ⊤)
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
theorem hasCancelNFT_of_hasPushNFT {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (h : HasPushNFT n M) : HasCancelNFT n M := by
  intro hn f hf himm W hWopen hWcpt p₁ p₂ q₁ q₂ hW₁ hW₂ hW₃ hW₄ hp₁p₂ hq₁q₂
    hp₁q₁ hp₁q₂ hp₂q₁ hp₂q₂ hfp hfq hclean hsep htransP htransQ γ₁ γ₂ hγ₁ hγ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1
    hγW₁ hγW₂ hγ₁inj hγ₂inj hγdisj hγend
  obtain ⟨W₀, O, ψ, σ, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅,
    h₁₆⟩ := h hn f hf himm W hWopen hWcpt p₁ p₂ q₁ q₂ hW₁ hW₂ hW₃ hW₄ hp₁p₂ hq₁q₂
      hp₁q₁ hp₁q₂ hp₂q₁ hp₂q₂ hfp hfq hclean hsep htransP htransQ γ₁ γ₂ hγ₁ hγ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1
      hγW₁ hγW₂ hγ₁inj hγ₂inj hγdisj hγend
  exact cancellation_of_pushData hn f hf himm W hWopen p₁ p₂ q₁ q₂ hW₁ hW₂ hW₃ hW₄ hclean hsep
    W₀ O ψ σ h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₂ h₁₃ h₁₀ h₁₁ h₁₄ h₁₅ h₁₆



/-- **The interface of the reduction step**, atlas-free: one double point is removed while the two
invariants are preserved. -/
def HasReduceNFT (n : ℕ) (M : Type*) [TopologicalSpace M]
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
theorem exists_reduce_double_points_NFT {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M]
    (hins : HasInsertionNF n M) (hcancel : HasCancelNFT n M)
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
  have htransP' : (mfderiv (𝓡 n) (𝓡 (2 * n)) f' p₁).range ⊔
      (mfderiv (𝓡 n) (𝓡 (2 * n)) f' p₂).range = ⊤ :=
    trans_of_transDP' hf'c htrans' (p₁, p₂) hmem₁₂
  have htransQ' : (mfderiv (𝓡 n) (𝓡 (2 * n)) f' p').range ⊔
      (mfderiv (𝓡 n) (𝓡 (2 * n)) f' q').range = ⊤ :=
    trans_of_transDP' hf'c htrans' (p', q') hmem'
  obtain ⟨f'', hf''c, hf''imm, hout, hds'', hagree⟩ :=
    hcancel hn f' hf'c hf'imm W hWopen hWcpt p₁ p₂ p' q'
      hW₁ hW₂ hW₃ hW₄ hp₁p₂ hp'q' hp'p₁.symm hq'p₁.symm hp'p₂.symm hq'p₂.symm
      hfp' hfq' hWclean hWsep htransP' htransQ' γ₁ γ₂ hγ₁c hγ₂c hγ₁0 hγ₁1 hγ₂0 hγ₂1
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
theorem hasReduceNFT_of {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M]
    (hn : 3 ≤ n) (hins : HasInsertionNF n M) (hcancel : HasCancelNFT n M) :
    HasReduceNFT n M :=
  fun f hf himm hfin hsimple htrans p₁ p₂ hp₁p₂ hfp =>
    exists_reduce_double_points_NFT (M := M) hn hins hcancel f hf himm hfin hsimple htrans
      p₁ p₂ hp₁p₂ hfp


/-- **The endgame, atlas-free.**  If every simple double point can be removed (together with a
freshly inserted partner), then any smooth immersion of a compact connected `n`-manifold
(`n ≥ 3`) with finitely many simple transverse double points can be improved to a smooth
embedding. -/
theorem exists_embedding_of_reduce_NFT {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M]
    (hred : HasReduceNFT n M)
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
theorem exists_embedding_of_compact_connected_NFT {n : ℕ} (hn : 3 ≤ n) {M : Type*}
    [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M]
    (hpush : HasPushNFT n M) (hins : HasInsertionNF n M)
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
  exact exists_embedding_of_reduce_NFT hn (hasReduceNFT_of hn hins (hasCancelNFT_of_hasPushNFT hpush))
    g hg hgimm hgfin hgsimple (transDP'_of_range hg hgtrans)


/-- **The compact branch of Whitney's strong embedding theorem, atlas-free.**  A compact smooth
`n`-manifold (`n ≥ 3`), *orientable or not*, admits a smooth embedding into `ℝ^{2n}` with injective
derivative, given the push and the insertion on each compact open submanifold.  The general
position input is supplied by `Work.Whitney.exists_simple_transverse_immersion`. -/
theorem exists_embedding_of_compact_NFT {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (hpush : ∀ (U : TopologicalSpace.Opens M) [CompactSpace U], HasPushNFT n U)
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
  exact exists_embedding_of_compact_connected_NFT hn (hpush U) (hins U)
    (exists_simple_transverse_immersion (n := n) hn)

end Work.Whitney
