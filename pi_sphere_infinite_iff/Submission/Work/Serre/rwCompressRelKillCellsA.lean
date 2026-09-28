import Mathlib
import Submission.Work.Serre.serreAttachKillPi
import Submission.Work.Serre.serrePostnikovTower
import Submission.Work.Serre.cylRelPi
import Submission.Work.Serre.pathConnectedSpace_homotopyFibre
import Submission.Work.Serre.RangeOne.subsingletonRelPiRange
import Submission.Work.RatHurewicz.compression_of_relPiVanishing
import Submission.Work.RatHurewicz.compressRel_attachCells_range
import Submission.Work.RatHurewicz.pair_les
import Submission.Work.RatHurewicz.CompressRelToRelPi
import Submission.Work.Serre.RangeOne.Comparison

/-!
# `rwCompressRelKillCellsA` — compression of `(KillCells (n+1) W, killIncl '' A)`

The target of this file is the compression property of the pair
`(KillCells (n+1) W, killIncl (n+1) W '' A)` in dimensions `≤ n + 2`, assuming that `A ⊆ W`
meets every path component of `W` and that the inclusion `A ↪ W` induces a bijection on `π_q` for
every `q ≤ n + 1` (unshifted indexing: `q = 0` is `π_0`).

The mathematical content: `KillCells (n+1) W` is `W` with an `(n+3)`-cell attached along *every*
map `S^{n+2} → W`.  Hence

* `π_i(W) → π_i(KillCells (n+1) W)` is bijective for `i ≤ n + 1` and `π_{n+2}` of the attachment
  is trivial (`Work.Serre.killCells_step`), while
* the inclusion `A ↪ W` is a `π_q`-bijection for `q ≤ n + 1` (hypothesis).

So the composite `A ↪ W ↪ KillCells (n+1) W` is a `π_q`-isomorphism for `q ≤ n + 1` with one
extra degree of surjectivity (`π_{n+2}(KillCells (n+1) W) = 0`), which by the long exact sequence
of the pair gives the vanishing of the relative homotopy groups
`π_j(KillCells (n+1) W, killIncl '' A)` for `j ≤ n + 2`
(`Work.Serre.subsingleton_relPi_of_piMapN`), and hence the compression property in dimension
`n + 2` (`Work.RatHurewicz.compression_of_relPiVanishing`).

## Structure of the file

* `Work.Serre.homotopyFibreFst_comp_homotopic_const` — the composite `i ∘ homotopyFibreFst i a₀` is
  null-homotopic (the path coordinate supplies the homotopy);
* `Work.Serre.subsingleton_relPi_of_piMapN` — the general exactness statement: injectivity of
  `π_q(i)` for `q ≤ n + 1` and surjectivity for `q ≤ n + 2` force `RelHomotopyGroup i a₀ k = 0` for
  `k ≤ n + 1`;
* the application lemmas
  `Work.Serre.piMapN_killIncl_comp_setIncl_bijective`,
  `Work.Serre.piMapN_killIncl_comp_setIncl_surjective`,
  `Work.Serre.exists_joined_killIncl_image`
  and the target `Work.Serre.rwCompressRelKillCellsA`.
-/

open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

/-! ## A general exactness statement for relative homotopy groups -/

/-- **The composite `i ∘ homotopyFibreFst i a₀` is null-homotopic.**  A point of the homotopy fibre
of `i : C(A, X)` at `a₀` is a pair `(a, γ)` with `γ` a path in `X` from `i a₀` to `i a`; the
homotopy `(p, t) ↦ γ t` runs from the constant map at `i a₀` to `i ∘ homotopyFibreFst`. -/
theorem homotopyFibreFst_comp_homotopic_const {X : Type} [TopologicalSpace X] {A : Type}
    [TopologicalSpace A] (i : C(A, X)) (a₀ : A) :
    ∃ y : X, (ContinuousMap.const (Work.RatHurewicz.homotopyFibre i a₀) y).Homotopic
      (i.comp (Work.RatHurewicz.homotopyFibreFst i a₀)) := by
  refine ⟨i a₀, ⟨{ toContinuousMap := ?_, map_zero_left := ?_, map_one_left := ?_ }⟩⟩
  · refine ⟨fun q : unitInterval × Work.RatHurewicz.homotopyFibre i a₀ => q.2.1.2.1 q.1, ?_⟩
    have hp : Continuous fun p : Work.RatHurewicz.homotopyFibre i a₀ => p.1.2.1 :=
      continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)
    exact continuous_eval.comp ((hp.comp continuous_snd).prodMk continuous_fst)
  · intro p
    exact p.1.2.2
  · intro p
    exact p.2

/-- **Vanishing of the relative homotopy groups of a pair, from the π-isomorphisms of the
inclusion, one degree of surjectivity beyond the isomorphism range.**

Let `i : C(A, X)` and `a₀ : A`.  Assume `piMapN i q a₀ : π_q(A) → π_q(X)` is *injective* for every
`q ≤ n + 1` and *surjective* for every `q ≤ n + 2`.  Then the relative homotopy groups
`RelHomotopyGroup i a₀ k = π_k(homotopyFibre i a₀)` are trivial for `k ≤ n + 1`.

Matching the `(n+1)`-connected case: `RelHomotopyGroup i a₀ k` is the classical `π_{k+1}(X, A, a₀)`,
so the conclusion says `π_j(X, A, a₀) = 0` for `j ≤ n + 2`, and the hypotheses are that
`π_j(i)` is injective for `j ≤ n + 1` and surjective for `j ≤ n + 2` (for `j ≤ n + 1` this is
`π_j(A) ≅ π_j(X)`).

Proof: for `k ≥ 2` the long exact sequence of the pair (`Work.RatHurewicz.pair_les`) gives, at
`π_{k+1}(X)`, that the connecting map `d : π_{k+1}(X) → RelHomotopyGroup i a₀ k` is zero (the map
`π_{k+1}(A) → π_{k+1}(X)` is onto), and at `RelHomotopyGroup i a₀ k` that the projection
`homotopyFibreFst` is injective where it can be, so an element of the relative group is
`d` of something and hence `1`.  The injectivity input for the projection is the triviality of the
composite `π_{k}(fibre) → π_k(A) → π_k(X)` (`Work.Serre.πmap_eq_one_of_homotopic_const` applied to
`i ∘ homotopyFibreFst`, which is null-homotopic).  The low degrees `k = 0, 1` are the
connectivity statements for the homotopy fibre
(`Work.Serre.pathConnectedSpace_homotopyFibre`, `Work.Serre.subsingleton_pi_one_homotopyFibre`). -/
theorem subsingleton_relPi_of_piMapN {X : Type} [TopologicalSpace X] {A : Type}
    [TopologicalSpace A] (i : C(A, X)) (a₀ : A) (n : ℕ)
    (hinj : ∀ q : ℕ, q ≤ n + 1 → Function.Injective (Work.Serre.piMapN i q a₀))
    (hsurj : ∀ q : ℕ, q ≤ n + 2 → Function.Surjective (Work.Serre.piMapN i q a₀)) :
    ∀ k : ℕ, k ≤ n + 1 → Subsingleton (Work.RatHurewicz.RelHomotopyGroup i a₀ k) := by
  classical
  -- the `πmap` indexing of the hypotheses (`πmap i m` is `piMapN i (m+1)`)
  have hinj' : ∀ m : ℕ, m ≤ n → Function.Injective (⇑(Work.StemsB.πmap i m a₀)) :=
    fun m hm => hinj (m + 1) (by omega)
  have hsurj' : ∀ m : ℕ, m ≤ n + 1 → Function.Surjective (⇑(Work.StemsB.πmap i m a₀)) :=
    fun m hm => hsurj (m + 1) (by omega)
  -- the composite `i ∘ homotopyFibreFst` is null-homotopic
  have hnull : ∃ y : X, (i.comp (Work.RatHurewicz.homotopyFibreFst i a₀)).Homotopic
      (ContinuousMap.const (Work.RatHurewicz.homotopyFibre i a₀) y) :=
    (homotopyFibreFst_comp_homotopic_const i a₀).imp (fun y hy => hy.symm)
  -- hence the projection of the homotopy fibre is trivial on `π_{m+1}` for `m ≤ n`
  have hfst : ∀ (m : ℕ), m ≤ n → ∀ a : HomotopyGroup (Fin (m + 1))
      (Work.RatHurewicz.homotopyFibre i a₀) (Work.RatHurewicz.homotopyFibreBasepoint i a₀),
      (Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst i a₀) m
        (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) a = 1 := by
    intro m hm a
    refine hinj' m hm ?_
    have hc : (Work.StemsB.πmap (i.comp (Work.RatHurewicz.homotopyFibreFst i a₀)) m
        (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) a
        = (Work.StemsB.πmap i m a₀)
          ((Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst i a₀) m
            (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) a) :=
      Work.StemsB.πmap_comp_apply (Work.RatHurewicz.homotopyFibreFst i a₀) i m
        (Work.RatHurewicz.homotopyFibreBasepoint i a₀) a
    rw [← hc]
    exact πmap_eq_one_of_homotopic_const _ m _ hnull a
  intro k hk
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- `k = 0`: the homotopy fibre is path connected
    subst hk0
    have hpc : PathConnectedSpace (Work.RatHurewicz.homotopyFibre i a₀) := by
      refine pathConnectedSpace_homotopyFibre i a₀ ?_ (hsurj 1 (by omega))
      intro a ha
      exact joined_of_piMapN_zero_injective i a₀ (hinj 0 (by omega)) ha
    haveI : Subsingleton (ZerothHomotopy (Work.RatHurewicz.homotopyFibre i a₀)) :=
      (pathConnectedSpace_iff_zerothHomotopy.mp hpc).2
    exact ⟨fun u v => (HomotopyGroup.pi0EquivZerothHomotopy
      (X := Work.RatHurewicz.homotopyFibre i a₀)
      (x := Work.RatHurewicz.homotopyFibreBasepoint i a₀)).injective
        (Subsingleton.elim _ _)⟩
  · rcases eq_or_lt_of_le (show 1 ≤ k from hkpos) with hk1 | hk2
    · -- `k = 1`
      subst hk1
      refine subsingleton_pi_one_homotopyFibre i a₀ (hinj 1 (by omega)) ?_
      exact piMap_fibreIncl_eq_one_of_surjective i a₀ (hsurj 2 (by omega))
    · -- `k ≥ 2`: the exactness of the pair sequence
      have hk1' : 1 ≤ k := by omega
      obtain ⟨del, d, _h1, _h2, h3, h4⟩ :=
        Work.RatHurewicz.pair_les i a₀ (k - 1) (by omega)
      -- the connecting map `π_{k+1}(X) → π_k(F)` is trivial
      have hd : ∀ z : HomotopyGroup (Fin ((k - 1) + 2)) X (i a₀), d z = 1 :=
        fun z => (h3 z).mpr (hsurj' ((k - 1) + 1) (by omega) z)
      -- the projection `π_k(F) → π_k(A)` is trivial
      have hkey : ∀ y : Work.RatHurewicz.RelHomotopyGroup i a₀ ((k - 1) + 1), y = 1 := by
        intro y
        obtain ⟨z, hz⟩ := (h4 y).mp (hfst (k - 1) (by omega) y)
        rw [← hz, hd z]
      rw [show k = (k - 1) + 1 from (Nat.sub_add_cancel hk1').symm]
      exact ⟨fun y y' => by rw [hkey y, hkey y']⟩


/-! ## The application: the pair `(KillCells (n+1) W, killIncl '' A)` -/

/-- **The composite `A ↪ W ↪ KillCells (n+1) W` is a bijection on `π_q` for `q ≤ n + 1`.**  This is
`Work.Serre.piMapN_comp` together with the two inputs: the inclusion `A ↪ W` is a `π_q`-bijection
for `q ≤ n + 1` (hypothesis), and the inclusion `W ↪ KillCells (n+1) W` is one for `q ≤ n + 1`
(`Work.Serre.killCells_step`, the attached cells having dimension `n + 3 > n + 2 ≥ q`). -/
theorem piMapN_killIncl_comp_setIncl_bijective (n : ℕ) {W : Type} [TopologicalSpace W] (A : Set W)
    (hpi : ∀ (q : ℕ), q ≤ n + 1 → ∀ a : ↥A,
      Function.Bijective (Work.Serre.piMapN (Work.RatHurewicz.setIncl A) q a)) :
    ∀ (q : ℕ), q ≤ n + 1 → ∀ a : ↥A,
      Function.Bijective (Work.Serre.piMapN
        ((Work.Serre.killIncl (n + 1) W).comp (Work.RatHurewicz.setIncl A)) q a) := by
  intro q hq a
  have hfact : (Work.Serre.piMapN
        ((Work.Serre.killIncl (n + 1) W).comp (Work.RatHurewicz.setIncl A)) q a)
      = (Work.Serre.piMapN (Work.Serre.killIncl (n + 1) W) q ((Work.RatHurewicz.setIncl A) a)) ∘
        (Work.Serre.piMapN (Work.RatHurewicz.setIncl A) q a) := by
    funext x
    exact Work.Serre.piMapN_comp (Work.RatHurewicz.setIncl A) (Work.Serre.killIncl (n + 1) W) q a x
  rw [hfact]
  exact ((killCells_step (n + 1) W).1 q hq (a : W)).comp (hpi q hq a)

/-- **The composite `A ↪ W ↪ KillCells (n+1) W` is onto on `π_{n+2}`**, the one degree of
surjectivity beyond the isomorphism range: for `q ≤ n + 1` it is a bijection, and
`π_{n+2}(KillCells (n+1) W)` is trivial (`Work.Serre.killCells_step`, the cells attached along
*every* `S^{n+2} → W` kill `π_{n+2}`). -/
theorem piMapN_killIncl_comp_setIncl_surjective (n : ℕ) {W : Type} [TopologicalSpace W]
    (A : Set W)
    (hpi : ∀ (q : ℕ), q ≤ n + 1 → ∀ a : ↥A,
      Function.Bijective (Work.Serre.piMapN (Work.RatHurewicz.setIncl A) q a)) :
    ∀ (q : ℕ), q ≤ n + 2 → ∀ a : ↥A,
      Function.Surjective (Work.Serre.piMapN
        ((Work.Serre.killIncl (n + 1) W).comp (Work.RatHurewicz.setIncl A)) q a) := by
  intro q hq a
  have hfact : (Work.Serre.piMapN
        ((Work.Serre.killIncl (n + 1) W).comp (Work.RatHurewicz.setIncl A)) q a)
      = (Work.Serre.piMapN (Work.Serre.killIncl (n + 1) W) q ((Work.RatHurewicz.setIncl A) a)) ∘
        (Work.Serre.piMapN (Work.RatHurewicz.setIncl A) q a) := by
    funext x
    exact Work.Serre.piMapN_comp (Work.RatHurewicz.setIncl A) (Work.Serre.killIncl (n + 1) W) q a x
  by_cases hle : q ≤ n + 1
  · rw [hfact]
    exact ((killCells_step (n + 1) W).1 q hle (a : W)).2.comp (hpi q hle a).2
  · have hq' : q = n + 2 := by omega
    subst hq'
    rw [hfact]
    have hsub : Subsingleton (HomotopyGroup (Fin (n + 2)) (Work.Serre.KillCells (n + 1) W)
        ((Work.Serre.killIncl (n + 1) W) (a : W))) := (killCells_step (n + 1) W).2.1 _
    intro z
    exact ⟨Classical.arbitrary _, hsub.elim _ z⟩

/-- **Every point of `KillCells (n+1) W` is joined to a point of `killIncl '' A`**, given that every
point of `W` is joined to a point of `A`: every point of the attachment is joined to a point of `W`
(`Work.Serre.killCells_step`). -/
theorem exists_joined_killIncl_image (n : ℕ) {W : Type} [TopologicalSpace W] (A : Set W)
    (hconn0 : ∀ w : W, ∃ a : ↥A, Nonempty (Path w a)) :
    ∀ y : Work.Serre.KillCells (n + 1) W, ∃ a : ↥A,
      Nonempty (Path y (Work.Serre.killIncl (n + 1) W (a : W))) := by
  intro y
  obtain ⟨w, hw⟩ := (killCells_step (n + 1) W).2.2 y
  obtain ⟨a, ha⟩ := hconn0 w
  exact ⟨a, hw.trans (Joined.map ha (Work.Serre.killIncl (n + 1) W).continuous)⟩

/-- Compression of the pair `(KillCells (n+1) W, killIncl '' A)` in dimensions `≤ n + 2`. -/
theorem rwCompressRelKillCellsA (n : ℕ) {W : Type} [TopologicalSpace W] (A : Set W)
    (hconn0 : ∀ w : W, ∃ a : ↥A, Nonempty (Path w a))
    (hpi : ∀ (q : ℕ), q ≤ n + 1 → ∀ a : ↥A,
      Function.Bijective (Work.Serre.piMapN (Work.RatHurewicz.setIncl A) q a)) :
    ∀ d : ℕ, d ≤ n + 2 →
      Work.RatHurewicz.CompressRel (Work.Serre.KillCells (n + 1) W)
        {z : Work.Serre.KillCells (n + 1) W | ∃ a : ↥A, Work.Serre.killIncl (n + 1) W (a : W) = z}
        d := by
  classical
  -- the composite `A ↪ W ↪ KillCells (n+1) W`, whose range is the target subspace
  let g : C(↥A, Work.Serre.KillCells (n + 1) W) :=
    (Work.Serre.killIncl (n + 1) W).comp (Work.RatHurewicz.setIncl A)
  -- `g` is an embedding, so the pair `(range g ⊆ KillCells (n+1) W)` has the same relative
  -- homotopy groups as the pair of the *map* `g`
  have hkiEmb : Topology.IsEmbedding (⇑(Work.Serre.killIncl (n + 1) W) :
      W → Work.Serre.KillCells (n + 1) W) :=
    Topology.IsEmbedding.mk
      (Work.RatHurewicz.isInducing_attachIncl (n + 1) W (KillIdx (n + 1) W) (fun h => h))
      (Work.RatHurewicz.AttachRange.attachIncl_injective (n + 1) W (KillIdx (n + 1) W)
        (fun h => h))
  have hgEmb : Topology.IsEmbedding (g : ↥A → Work.Serre.KillCells (n + 1) W) :=
    Topology.IsEmbedding.comp (f := ⇑(Work.RatHurewicz.setIncl A))
      (g := ⇑(Work.Serre.killIncl (n + 1) W)) hkiEmb Topology.IsEmbedding.subtypeVal
  -- the relative homotopy groups of the map `g` vanish up to degree `n + 1`
  have hrel : ∀ a : ↥A, ∀ k : ℕ, k ≤ n + 1 →
      Subsingleton (Work.RatHurewicz.RelHomotopyGroup g a k) := by
    intro a k hk
    exact subsingleton_relPi_of_piMapN g a n
      (fun q hq => (piMapN_killIncl_comp_setIncl_bijective n A hpi q hq a).1)
      (fun q hq => piMapN_killIncl_comp_setIncl_surjective n A hpi q hq a) k hk
  -- hence the relative homotopy groups of the pair `(KillCells (n+1) W, killIncl '' A)`
  have hvan : ∀ b : ↥(Set.range (g : ↥A → Work.Serre.KillCells (n + 1) W)),
      ∀ k : ℕ, k ≤ n + 1 → Subsingleton (Work.RatHurewicz.RelHomotopyGroup
        (Work.RatHurewicz.setIncl (Set.range (g : ↥A → Work.Serre.KillCells (n + 1) W))) b k) := by
    intro b k hk
    have hb : b = (⟨g (hgEmb.toHomeomorph.symm b), hgEmb.toHomeomorph.symm b, rfl⟩ :
        ↥(Set.range (g : ↥A → Work.Serre.KillCells (n + 1) W))) := by
      refine Subtype.ext ?_
      exact (congrArg Subtype.val
        (Homeomorph.apply_symm_apply hgEmb.toHomeomorph b)).symm
    rw [hb]
    exact Work.Serre.RangeOne.subsingleton_relPi_of_homeoRange g hgEmb.toHomeomorph
      (fun a => rfl) (hgEmb.toHomeomorph.symm b) k (hrel _ k hk)
  -- and every point of the attachment is joined to a point of `killIncl '' A`
  have hconn : ∀ y : Work.Serre.KillCells (n + 1) W,
      ∃ b : ↥(Set.range (g : ↥A → Work.Serre.KillCells (n + 1) W)),
        Nonempty (Path y (b : Work.Serre.KillCells (n + 1) W)) := by
    intro y
    obtain ⟨a, ha⟩ := exists_joined_killIncl_image n A hconn0 y
    exact ⟨⟨g a, a, rfl⟩, ha⟩
  intro d hd
  exact Work.RatHurewicz.compression_of_relPiVanishing (n + 1) hconn hvan d hd

end

end Work.Serre
