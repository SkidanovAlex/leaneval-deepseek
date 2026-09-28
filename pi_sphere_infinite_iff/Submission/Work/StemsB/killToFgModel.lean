import Mathlib
import Submission.Work.RatHurewicz.S3Inputs
import Submission.Work.Serre.Models
import Submission.Work.Serre.attachIncl_piMap_bijective_of_compress
import Submission.Work.Serre.attachIncl_pi0_bijective
import Submission.Work.Serre.CWModel.Gen
import Submission.Work.Serre.CWModel.sphereExtend
import Submission.Work.RatHurewicz.killFamily_subsingleton
import Submission.Work.Serre.serrePostnikovTower
import Submission.Work.Serre.rangeWhiteheadInclInt

/-!
# Killing the homotopy groups of a finite model over a range model

`Work.StemsB.killToFgModel` is the second geometric input of the reduction of
`Work.RatHurewicz.RangeModelRatAcyclic` to its finitely generated case: a map `φ : W → Z` from a
space `W` with `π_i(W) = 0` for `i < k` and finitely generated `π_k`, into a range model `Z` of
`K(A,k)` (`π_i(Z) = 0` for `i ≤ 2k-1`, `i ≠ k`), factors through a range model of `K(A',k)` with
`A'` finitely generated.

The construction is the classical killing tower: attach one `(m+1)`-cell per element of `π_m` (for
`m = k+1, …, 2k-1`) successively, extending the map to `Z` at each step (the attaching maps become
null-homotopic in `Z` because `π_m(Z) = 0`).  The homotopy groups `π_i` for `i ≤ k` are unchanged
(compression), so the resulting space still has `π_k` finitely generated and `π_i = 0` for `i < k`.
-/

open scoped Topology Topology.Homotopy unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.StemsB

noncomputable section

set_option maxHeartbeats 4000000

open Work.RatHurewicz

/-! ## Auxiliary lemmas -/

theorem subsingleton_of_surjective {α β : Type*} (f : α → β) (hf : Function.Surjective f)
    (hα : Subsingleton α) : Subsingleton β := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨a', rfl⟩ := hf a
  obtain ⟨b', rfl⟩ := hf b
  rw [Subsingleton.elim a' b']

/-- **Transport of homotopy groups along an equality of the cube index.** -/
noncomputable def indexCastMulEquiv {X : Type} [TopologicalSpace X] (x : X) {n m : ℕ} (h : n = m)
    [Nontrivial (Fin n)] [Nontrivial (Fin m)] :
    HomotopyGroup (Fin n) X x ≃* HomotopyGroup (Fin m) X x := by
  subst h
  exact MulEquiv.refl _

/-- **The canonical identification** `G ≃* Multiplicative (Additive G)`. -/
noncomputable def canonMulEquiv (G : Type) [CommGroup G] : G ≃* Multiplicative (Additive G) :=
  { toFun := fun g => Multiplicative.ofAdd (Additive.ofMul g)
    invFun := fun m => Additive.ofMul.symm (Multiplicative.ofAdd.symm m)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }

/-- `π_k` of `Y` at `y₀` is finitely generated. -/
def PiKFg (k : ℕ) (hk : 2 ≤ k) (Y : Type) [TopologicalSpace Y] (y₀ : Y) : Prop :=
  letI : k.AtLeastTwo := ⟨hk⟩
  Module.Finite ℤ (Additive (HomotopyGroup (Fin k) Y y₀))

/-! ## The one-step extension -/

/-- **Extension over the cells that kill `π_{m+1}`.**  If `π_{m+1}` of the target is trivial at
`g y₀`, then `g` extends over `attachCells m Y (π_{m+1}(Y,y₀)) (killFamily m Y y₀)`. -/
theorem killFamily_extend (m : ℕ) (Y : Type) [TopologicalSpace Y] (y₀ : Y)
    (Z : Type) [TopologicalSpace Z] (g : C(Y, Z))
    (h : Subsingleton (HomotopyGroup (Fin (m + 1)) Z (g y₀))) :
    ∃ (g' : C(Work.RatHurewicz.attachCells m Y (HomotopyGroup (Fin (m + 1)) Y y₀)
        (Work.RatHurewicz.killFamily m Y y₀), Z)),
      g'.comp (Work.RatHurewicz.attachIncl m Y (HomotopyGroup (Fin (m + 1)) Y y₀)
        (Work.RatHurewicz.killFamily m Y y₀)) = g := by
  classical
  have hnull : ∀ α : HomotopyGroup (Fin (m + 1)) Y y₀,
      (g.comp (Work.RatHurewicz.killFamily m Y y₀ α)).Homotopic
        (ContinuousMap.const (Work.RatHurewicz.cellSphere m) (g y₀)) := by
    intro α
    have hker : Work.Serre.piMapN g (m + 1) y₀ α = 1 := Subsingleton.elim _ _
    have hn : 1 ≤ m + 1 := by omega
    have hcube : GenLoop.Homotopic (Work.StemsB.genLoopMap g (m + 1) (Quotient.out α))
        (GenLoop.const (N := Fin (m + 1)) (X := Z) (x := g y₀)) := by
      have h1 : (Quotient.mk _ (Work.StemsB.genLoopMap g (m + 1) (Quotient.out α)) :
            HomotopyGroup (Fin (m + 1)) Z (g y₀))
          = Quotient.mk (GenLoop.Homotopic.setoid (Fin (m + 1)) (g y₀))
              (GenLoop.const (N := Fin (m + 1)) (X := Z) (x := g y₀)) := by
        rw [← Work.Serre.piMapN_apply_mk, Quotient.out_eq α, hker]
        exact HomotopyGroup.one_def (N := Fin (m + 1)) (X := Z) (x := g y₀)
      exact Quotient.exact h1
    have h2 := Work.Serre.CWModel.cubeLift_homotopic hn hcube
    rw [Work.RatHurewicz.cubeLift_genLoopMap, Work.Serre.CWModel.cubeLift_const] at h2
    exact h2
  let G : (α : HomotopyGroup (Fin (m + 1)) Y y₀) → C(Work.RatHurewicz.cellDisk m, Z) := fun α =>
    Classical.choose (Work.Serre.CWModel.sphereExtend (g.comp (Work.RatHurewicz.killFamily m Y y₀ α))
      (hnull α).some.toContinuousMap (g y₀) (hnull α).some.map_zero_left (hnull α).some.map_one_left)
  have hG : ∀ (α : HomotopyGroup (Fin (m + 1)) Y y₀) (z : Work.RatHurewicz.cellSphere m),
      G α (Work.RatHurewicz.cellSphereToDisk m z) = g (Work.RatHurewicz.killFamily m Y y₀ α z) := by
    intro α z
    have hspec := Classical.choose_spec (Work.Serre.CWModel.sphereExtend
      (g.comp (Work.RatHurewicz.killFamily m Y y₀ α))
      (hnull α).some.toContinuousMap (g y₀) (hnull α).some.map_zero_left (hnull α).some.map_one_left)
    exact congrFun (congrArg DFunLike.coe hspec) z
  refine ⟨Work.Serre.CWModel.attachG m Y (HomotopyGroup (Fin (m + 1)) Y y₀)
    (Work.RatHurewicz.killFamily m Y y₀) g G hG, ?_⟩
  ext y
  exact Work.Serre.CWModel.attachG_incl m Y (HomotopyGroup (Fin (m + 1)) Y y₀)
    (Work.RatHurewicz.killFamily m Y y₀) g G hG y

/-! ## The killing tower -/

/-- **The killing tower.**  From a space `Y` which is `(k-1)`-connected with finitely generated
`π_k`, mapping to `Z`, kill `π_{k+1}, …, π_{k+n}` successively. -/
theorem killTower (k : ℕ) (hk : 2 ≤ k) (Z : Type) [TopologicalSpace Z] (z₀ : Z)
    (hZc : ∀ i : ℕ, i ≤ 2 * k - 1 → i ≠ k → ∀ z : Z, Subsingleton (HomotopyGroup (Fin i) Z z)) :
    ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] (y₀ : Y) (g : C(Y, Z)),
      PiKFg k hk Y y₀ →
      (∀ i : ℕ, i < k → Subsingleton (HomotopyGroup (Fin i) Y y₀)) →
      k + n ≤ 2 * k - 1 →
      ∃ (P : Type) (_ : TopologicalSpace P) (p₀ : P) (h : C(P, Z)) (χ : C(Y, P)),
        h.comp χ = g ∧
        (∀ i : ℕ, i < k → Subsingleton (HomotopyGroup (Fin i) P p₀)) ∧
        (∀ i : ℕ, k < i → i ≤ k + n → Subsingleton (HomotopyGroup (Fin i) P p₀)) ∧
        PiKFg k hk P p₀ := by
  intro n
  induction n with
  | zero =>
    intro Y _ y₀ g hK hY0 hle
    refine ⟨Y, inferInstance, y₀, g, ContinuousMap.id Y, ?_, hY0, ?_, hK⟩
    · ext y; rfl
    · intro i hi hle'
      omega
  | succ n ih =>
    intro Y _ y₀ g hK hY0 hle
    obtain ⟨Y₁, instY₁, y₁, g₁, χ₁, hχ₁, hlo₁, hmid₁, hK₁⟩ := ih Y y₀ g hK hY0 (by omega)
    have hle' : k + n + 1 ≤ 2 * k - 1 := hle
    have hne : k + n + 1 ≠ k := by omega
    obtain ⟨g₂, hg₂⟩ := killFamily_extend (k + n) Y₁ y₁ Z g₁ (hZc (k + n + 1) hle' hne (g₁ y₁))
    let ι := HomotopyGroup (Fin (k + n + 1)) Y₁ y₁
    let f : ι → C(Work.RatHurewicz.cellSphere (k + n), Y₁) := Work.RatHurewicz.killFamily (k + n) Y₁ y₁
    let Y₂ : Type := Work.RatHurewicz.attachCells (k + n) Y₁ ι f
    letI : TopologicalSpace Y₂ := inferInstance
    let χ₂ : C(Y₁, Y₂) := Work.RatHurewicz.attachIncl (k + n) Y₁ ι f
    have hpres : ∀ i : ℕ, 1 ≤ i → i ≤ k + n → Function.Bijective (Work.StemsB.πmap χ₂ (i - 1) y₁) :=
      fun i hi1 hin => Work.Serre.attachIncl_piMap_bijective_of_compress (k + n) Y₁ ι f y₁ i hi1 hin
    have hpres0 : Function.Bijective (HomotopyGroup.map (N := Fin 0) χ₂) :=
      Work.Serre.attachIncl_pi0_bijective (k + n) Y₁ ι f y₁
    have hkill : Subsingleton (HomotopyGroup (Fin (k + n + 1)) Y₂ (χ₂ y₁)) :=
      Work.RatHurewicz.killFamily_subsingleton (k + n) Y₁ y₁
    refine ⟨Y₂, inferInstance, χ₂ y₁, g₂, χ₂.comp χ₁, ?_, ?_, ?_, ?_⟩
    · rw [← ContinuousMap.comp_assoc, hg₂, hχ₁]
    · intro i hi
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · subst h0
        exact subsingleton_of_surjective _ hpres0.2 (hlo₁ 0 hi)
      · have hsi : i - 1 + 1 = i := Nat.sub_add_cancel hpos
        have hb := hpres i hpos (by omega)
        have h1 : Subsingleton (HomotopyGroup (Fin (i - 1 + 1)) Y₁ y₁) := by
          simpa only [hsi] using hlo₁ i hi
        have h2 := subsingleton_of_surjective (Work.StemsB.πmap χ₂ (i - 1) y₁) hb.2 h1
        simpa only [hsi] using h2
    · intro i hki hle2
      rcases lt_or_eq_of_le (by omega : i ≤ k + n + 1) with hlt | heq
      · have hsi : i - 1 + 1 = i := Nat.sub_add_cancel (by omega : 1 ≤ i)
        have hb := hpres i (by omega) (by omega)
        have h1 : Subsingleton (HomotopyGroup (Fin (i - 1 + 1)) Y₁ y₁) := by
          simpa only [hsi] using hmid₁ i hki (by omega)
        have h2 := subsingleton_of_surjective (Work.StemsB.πmap χ₂ (i - 1) y₁) hb.2 h1
        simpa only [hsi] using h2
      · subst heq
        exact hkill
    · letI : k.AtLeastTwo := ⟨hk⟩
      letI : (k - 1 + 1).AtLeastTwo := ⟨by omega⟩
      have hsk : k - 1 + 1 = k := Nat.sub_add_cancel (by omega : 1 ≤ k)
      have hb := hpres k (by omega) (by omega)
      have h1 : Module.Finite ℤ (Additive (HomotopyGroup (Fin (k - 1 + 1)) Y₁ y₁)) := by
        haveI : Module.Finite ℤ (Additive (HomotopyGroup (Fin k) Y₁ y₁)) := by
          simpa only [PiKFg] using hK₁
        exact Module.Finite.equiv (indexCastMulEquiv y₁ hsk).symm.toAdditive.toIntLinearEquiv
      haveI := h1
      have hMe : HomotopyGroup (Fin (k - 1 + 1)) Y₁ y₁ ≃*
          HomotopyGroup (Fin (k - 1 + 1)) Y₂ (χ₂ y₁) :=
        MulEquiv.ofBijective (Work.StemsB.πmap χ₂ (k - 1) y₁) hb
      have h2 : Module.Finite ℤ (Additive (HomotopyGroup (Fin (k - 1 + 1)) Y₂ (χ₂ y₁))) :=
        Module.Finite.equiv hMe.toAdditive.toIntLinearEquiv
      have h3 : Module.Finite ℤ (Additive (HomotopyGroup (Fin k) Y₂ (χ₂ y₁))) := by
        haveI := h2
        exact Module.Finite.equiv (indexCastMulEquiv (χ₂ y₁) hsk).toAdditive.toIntLinearEquiv
      simpa only [PiKFg] using h3

/-! ## The target -/

/-- **A map from a finite model into a range model factors through a finitely generated range
model.** -/
theorem killToFgModel
    (k : ℕ) (hk : 2 ≤ k)
    (Z : Type) [TopologicalSpace Z] (z₀ : Z)
    (hZ : ∀ i : ℕ, i ≤ 2 * k - 1 → i ≠ k → Subsingleton (HomotopyGroup (Fin i) Z z₀))
    (W : Type) [TopologicalSpace W] (w₀ : W) (φ : C(W, Z))
    (hW0 : ∀ i : ℕ, i < k → Subsingleton (HomotopyGroup (Fin i) W w₀))
    (hWk : PiKFg k hk W w₀) :
    ∃ (A : Type) (_ : AddCommGroup A) (_ : Module.Finite ℤ A)
      (Z' : Type) (_ : TopologicalSpace Z') (z₀' : Z') (ψ : C(Z', Z)) (χ : C(W, Z')),
      ψ.comp χ = φ ∧ Work.Serre.IsEMSpaceUpTo A k (by omega) (2 * k - 1) Z' z₀' := by
  -- `Z` is connected, and the vanishing of its homotopy groups transports to every point
  haveI hpi0 : Subsingleton (HomotopyGroup (Fin 0) Z z₀) := hZ 0 (by omega) (by omega)
  haveI hconn0 : Subsingleton (ZerothHomotopy Z) := by
    refine ⟨fun a b => ?_⟩
    exact (HomotopyGroup.pi0EquivZerothHomotopy (X := Z) (x := z₀)).symm.injective
      (Subsingleton.elim _ _)
  haveI : PathConnectedSpace Z :=
    pathConnectedSpace_iff_zerothHomotopy.mpr ⟨⟨ZerothHomotopy.mk z₀⟩, hconn0⟩
  have hZc : ∀ i : ℕ, i ≤ 2 * k - 1 → i ≠ k → ∀ z : Z, Subsingleton (HomotopyGroup (Fin i) Z z) := by
    intro i hi hne z
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      refine ⟨fun a b => ?_⟩
      exact (HomotopyGroup.pi0EquivZerothHomotopy (X := Z) (x := z)).injective
        (Subsingleton.elim _ _)
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
      exact Work.Serre.subsingleton_homotopyGroup_of_joined
        (PathConnectedSpace.joined z z₀).symm j (hZ (j + 1) (by omega) (by omega))
  obtain ⟨P, instP, p₀, h, χ, hχ, hlo, hmid, hKP⟩ :=
    killTower k hk Z z₀ hZc (k - 1) W w₀ φ hWk hW0 (by omega)
  letI : k.AtLeastTwo := ⟨hk⟩
  refine ⟨Additive (HomotopyGroup (Fin k) P p₀), inferInstance, ?_, P, instP, p₀, h, χ, hχ, ?_⟩
  · simpa only [PiKFg] using hKP
  · refine ⟨⟨canonMulEquiv _⟩, ?_⟩
    intro i hik hdisj
    rcases hdisj with hlt | hle
    · exact hlo i hlt
    · rcases lt_or_ge i k with hlt' | hge
      · exact hlo i hlt'
      · exact hmid i (lt_of_le_of_ne hge (Ne.symm hik)) (by omega)

end

end Work.StemsB
