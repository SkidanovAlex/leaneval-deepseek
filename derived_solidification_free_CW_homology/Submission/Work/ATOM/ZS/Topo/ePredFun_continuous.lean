import Mathlib
import Submission.Work.ATOM.ZS.Topo.Defs
import Submission.Work.ATOM.ZS.Level
import Submission.Work.ATOM.ZS.Data

/-!
# Continuity of `ẽ : (ℕ∪{∞}) × S ⟶ S`

This file proves that the underlying function `Work.ATOM.ePredFun` of `ẽ`
(`(0,x) ↦ s₀`, `(k+1,x) ↦ e_k x`, `(∞,x) ↦ x`) is continuous, i.e. is the underlying function of
a morphism of light profinite sets `(ℕ∪{∞}) ⊗ S ⟶ S`.

## Route

`S` is the limit of the tower `S.diagram` with projections `S.proj m`.  We

1. show that `S.proj m ∘ ẽ` is *continuous*; since `S.component m` is discrete this is proved by
   covering `(ℕ∪{∞}) × S` by the open sets `{k} × S` (`k ∈ ℕ`) together with the cofinite open set
   `({∞} ∪ {k ≥ m+1}) × S`, on each of which `S.proj m ∘ ẽ` agrees with a manifestly continuous
   function.  On the last set we use that `S.proj m ∘ e_n = S.proj m` for `n ≥ m`
   (`proj_e_apply`), which is the "eventual constancy" of the tower;
2. assemble these into a cone over `S.diagram` with cone point `(ℕ∪{∞}) ⊗ S` and lift it along
   `S.asLimit` to a morphism `ePredMap`; finally
3. identify the underlying function of `ePredMap` with `ePredFun` using that the projections
   `S.proj m` separate the points of `S`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open OnePoint

set_option linter.unusedSectionVars false

noncomputable section

namespace Work.ATOM.ZS.Topo

section
variable (S : LightProfinite.{0}) [Infinite S]

/-! ## 1. Eventual constancy of the idempotents `e_n = σ_n ∘ π_n` -/

/-- For `m ≤ n` the `m`-th projection does not see `e_n`: `proj m ∘ e_n = proj m`. -/
private lemma proj_e_apply (m n : ℕ) (h : m ≤ n) (x : ↥S) :
    S.proj m (e S n x) = S.proj m x := by
  rw [e_apply, proj_sig_apply, leg_of_le S n m h]
  exact congrFun (S.proj_comp_transitionMapLE' h) x

private lemma continuous_proj (m : ℕ) : Continuous (fun x : ↥S => S.proj m x) :=
  ContinuousMap.continuous _

private lemma continuous_e (n : ℕ) : Continuous (fun x : ↥S => e S n x) :=
  ContinuousMap.continuous _

/-- On `{∞} × S` and on `{k} × S` for `k ≥ m+1`, the `m`-th projection of `ẽ` is just `proj m` of
the second coordinate. -/
private lemma proj_ePred_eq (m : ℕ) {q : OnePoint ℕ}
    (hq : q = ∞ ∨ ∃ k : ℕ, m + 1 ≤ k ∧ q = (k : OnePoint ℕ)) (x : ↥S) :
    S.proj m (ePredFun S (q, x)) = S.proj m x := by
  rcases hq with rfl | ⟨k, hk, rfl⟩
  · rw [ePredFun_infty]
  · cases k with
    | zero => omega
    | succ k' =>
      rw [ePredFun_succ k' x]
      exact proj_e_apply S m k' (by omega) x

/-! ## 2. The open cover of `(ℕ∪{∞}) × S` -/

/-- The open cover of `(ℕ∪{∞}) × S` used below: the pieces `{k} × S` (`k ∈ ℕ`) together with the
cofinite piece `({∞} ∪ {k ≥ m+1}) × S`. -/
private def cover (m : ℕ) (i : ℕ ⊕ Unit) : Set ↥(NS S) :=
  match i with
  | .inl k => Prod.fst ⁻¹' ({(k : OnePoint ℕ)} : Set (OnePoint ℕ))
  | .inr _ => Prod.fst ⁻¹' ({∞} ∪ ((↑) '' {k : ℕ | m + 1 ≤ k}) : Set (OnePoint ℕ))

private lemma mem_cover_inl (m k : ℕ) (p : ↥(NS S)) :
    p ∈ cover S m (Sum.inl k) ↔ p.1 = (k : OnePoint ℕ) := by
  show p.1 ∈ ({(k : OnePoint ℕ)} : Set (OnePoint ℕ)) ↔ _
  simp

private lemma mem_cover_inr (m : ℕ) (u : Unit) (p : ↥(NS S)) :
    p ∈ cover S m (Sum.inr u) ↔
      p.1 = ∞ ∨ ∃ k : ℕ, m + 1 ≤ k ∧ p.1 = (k : OnePoint ℕ) := by
  show p.1 ∈ ({∞} ∪ ((↑) '' {k : ℕ | m + 1 ≤ k}) : Set (OnePoint ℕ)) ↔ _
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro (h | ⟨k, hk, hk'⟩)
    exacts [Or.inl h, Or.inr ⟨k, hk, hk'.symm⟩]
  · rintro (h | ⟨k, hk, hk'⟩)
    exacts [Or.inl h, Or.inr ⟨k, hk, hk'.symm⟩]

/-- The cofinite neighbourhood of `∞` in `ℕ∪{∞}` is open. -/
private lemma isOpen_cofinite (m : ℕ) :
    IsOpen ({∞} ∪ ((↑) '' {k : ℕ | m + 1 ≤ k}) : Set (OnePoint ℕ)) := by
  have hmem : (∞ : OnePoint ℕ) ∈ ({∞} ∪ ((↑) '' {k : ℕ | m + 1 ≤ k}) : Set (OnePoint ℕ)) :=
    Set.mem_union_left _ rfl
  refine (OnePoint.isOpen_iff_of_mem hmem).mpr ?_
  have hcomp : ((↑) ⁻¹' ({∞} ∪ ((↑) '' {k : ℕ | m + 1 ≤ k}) : Set (OnePoint ℕ)))ᶜ
      = {k : ℕ | k < m + 1} := by
    ext k
    simp
  rw [hcomp]
  exact ⟨(Set.finite_Iio (m + 1)).isClosed, (Set.finite_Iio (m + 1)).isCompact⟩

private lemma isOpen_cover (m : ℕ) (i : ℕ ⊕ Unit) : IsOpen (cover S m i) := by
  cases i with
  | inl k => exact ((isClopen_singleton_some k).isOpen).preimage continuous_fst
  | inr u => exact (isOpen_cofinite m).preimage continuous_fst

private lemma mem_cover (m : ℕ) (q : OnePoint ℕ) (x : ↥S) :
    ∃ i : ℕ ⊕ Unit, ((q, x) : ↥(NS S)) ∈ cover S m i := by
  rcases q with _ | k
  · exact ⟨Sum.inr (), (mem_cover_inr S m () (∞, x)).mpr (Or.inl rfl)⟩
  · exact ⟨Sum.inl k, (mem_cover_inl S m k ((k : OnePoint ℕ), x)).mpr rfl⟩

private lemma cover_iUnion_univ (m : ℕ) : (⋃ i, cover S m i) = Set.univ := by
  refine Set.eq_univ_of_forall (fun p => ?_)
  obtain ⟨q, x⟩ := p
  exact Set.mem_iUnion.mpr (mem_cover S m q x)

/-! ## 3. Continuity of `proj m ∘ ẽ` -/

private lemma continuousOn_cover (m : ℕ) (i : ℕ ⊕ Unit) :
    ContinuousOn (fun p : ↥(NS S) => S.proj m (ePredFun S p)) (cover S m i) := by
  cases i with
  | inl k =>
    cases k with
    | zero =>
      have hcont : Continuous (fun _ : ↥(NS S) => S.proj m (levelData S).s₀) := continuous_const
      refine hcont.continuousOn.congr ?_
      intro p hp
      obtain ⟨q, x⟩ := p
      rw [mem_cover_inl S m 0 (q, x)] at hp
      have hq : q = ((0 : ℕ) : OnePoint ℕ) := hp
      show S.proj m (ePredFun S ((q, x) : ↥(NS S))) = S.proj m (levelData S).s₀
      rw [hq]
      exact congrArg (S.proj m) (ePredFun_zero x)
    | succ k' =>
      have hcont : Continuous (fun p : ↥(NS S) => S.proj m (e S k' p.2)) :=
        (continuous_proj S m).comp ((continuous_e S k').comp continuous_snd)
      refine hcont.continuousOn.congr ?_
      intro p hp
      obtain ⟨q, x⟩ := p
      rw [mem_cover_inl S m (k' + 1) (q, x)] at hp
      have hq : q = ((k' + 1 : ℕ) : OnePoint ℕ) := hp
      show S.proj m (ePredFun S ((q, x) : ↥(NS S))) = S.proj m (e S k' x)
      rw [hq]
      exact congrArg (S.proj m) (ePredFun_succ k' x)
  | inr u =>
    have hcont : Continuous (fun p : ↥(NS S) => S.proj m p.2) :=
      (continuous_proj S m).comp continuous_snd
    refine hcont.continuousOn.congr ?_
    intro p hp
    obtain ⟨q, x⟩ := p
    rw [mem_cover_inr S m u (q, x)] at hp
    show S.proj m (ePredFun S ((q, x) : ↥(NS S))) = S.proj m x
    exact proj_ePred_eq S m hp x

private lemma continuous_legFun (m : ℕ) :
    Continuous (fun p : ↥(NS S) => S.proj m (ePredFun S p)) :=
  continuous_of_continuousOn_iUnion_of_isOpen (fun i => continuousOn_cover S m i)
    (fun i => isOpen_cover S m i) (cover_iUnion_univ S m)

/-! ## 4. The cone over `S.diagram` and the induced map -/

private noncomputable def legMap (m : ℕ) : NS S ⟶ S.component m :=
  ConcreteCategory.ofHom ⟨fun p => S.proj m (ePredFun S p), continuous_legFun S m⟩

private lemma legMap_comp_transitionMap (m : ℕ) :
    legMap S (m + 1) ≫ S.transitionMap m = legMap S m := by
  apply ConcreteCategory.hom_ext
  intro p
  exact congrFun (S.proj_comp_transitionMap' m) (ePredFun S p)

private noncomputable def coneAt : Cone S.diagram where
  pt := NS S
  π := NatTrans.ofOpSequence (fun m => legMap S m) (fun m => by
    simp only [Functor.const_obj_map]
    exact (legMap_comp_transitionMap S m).symm)

/-- The morphism `(ℕ∪{∞}) ⊗ S ⟶ S` underlying `ẽ`. -/
private noncomputable def ePredMap : NS S ⟶ S := S.asLimit.lift (coneAt S)

/-! ## 5. The projections separate the points of `S` -/

private lemma eq_of_proj_eq {x y : ↥S} (h : ∀ m : ℕ, S.proj m x = S.proj m y) : x = y := by
  have hpt : (ptAt x : pt ⟶ S) = ptAt y := by
    apply S.asLimit.hom_ext
    intro j
    apply ConcreteCategory.hom_ext
    intro z
    show S.proj (Opposite.unop j) x = S.proj (Opposite.unop j) y
    exact h (Opposite.unop j)
  have h2 := congrFun (congrArg (fun (g : pt ⟶ S) => ⇑g) hpt) (PUnit.unit : ↥pt)
  show x = y
  exact h2

private lemma continuous_ePredMap : Continuous (fun p : ↥(NS S) => ⇑(ePredMap S) p) :=
  ContinuousMap.continuous _

end

/-- Continuity of `ẽ : (ℕ∪{∞}) × S ⟶ S` (`Work.ATOM.ePredFun`): `(0,x) ↦ s₀`, `(k+1,x) ↦ e_k x`,
`(∞,x) ↦ x`.  Route: build the map as `S.asLimit.lift` of the cone whose `m`-th leg is the
locally constant function `p ↦ proj m (ẽ p)` (using `Work.ATOM.levelData` and the leg lemmas
`Work.ATOM.leg_succ`, `Work.ATOM.e_apply` of `Submission/Work/ATOM/ZS/Level.lean`), then show the
underlying function is `ePredFun`. -/
theorem ePredFun_continuous (S : LightProfinite.{0}) [Infinite S] :
    Continuous (Work.ATOM.ePredFun S) := by
  have hF : ⇑(ePredMap S) = Work.ATOM.ePredFun S := by
    funext p
    refine eq_of_proj_eq S (fun m => ?_)
    exact congrFun (congrArg (fun (g : NS S ⟶ S.component m) => ⇑g)
      (S.asLimit.fac (coneAt S) ⟨m⟩)) p
  rw [← hF]
  exact continuous_ePredMap S

end Work.ATOM.ZS.Topo
