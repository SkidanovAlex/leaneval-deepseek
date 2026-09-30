import Mathlib
import Submission.Work.RatHurewicz.S3Inputs
import Submission.Work.RatHurewicz.exists_killed_tower
import Submission.Work.RatHurewicz.pair_les
import Submission.Work.RatHurewicz.excisionTransfer
import Submission.Work.StemsB.PiMap

/-!
# The tower data of the truncation step (area RATHUREWICZ)

This module discharges `Work.RatHurewicz.TowerStepData`, the second of the two inputs of
`Submission/Work/RatHurewicz/S3Assembly.lean`, from the truncation tower of
`Work.RatHurewicz.exists_killed_tower`.

Given `X` with `π_j(X) = 0` for `j < k` (and `k ≥ 2`) and a degree `n+1 > k`, the tower
`Y_0 = X ⊆ Y_1 ⊆ ⋯` (one attachment step per homotopy degree, one cell per element) is run up to
stage `2k-1-k`, and the map `inc : X → Z := Y_{2k-1-k}` is the composite inclusion.  It has the
three properties:

* **the fibre is `k`-connected**: the compression property of the pair `(Z, range inc)` gives the
  vanishing of the relative groups `π_j(Z, X)` for `j ≤ k+1`, which is
  `Work.RatHurewicz.subsingleton_relPi_of_compressRel` together with
  `Work.RatHurewicz.subsingleton_relPi_of_isEmbedding` — the same step as in
  `Work.RatHurewicz.exists_killed_tower`;
* **`Z` is a range model of `K(π_k X, k)` up to `2k-1`**: the degrees `k < j ≤ 2k-1` are the killing
  recorded by the tower, and the degrees `j < k` follow from `π_j(X) = 0`, because compression
  pushes based `j`-cubes of `Z` into the range of `inc`, which is homeomorphic to `X`
  (`Work.RatHurewicz.bijective_πmap_setIncl_of_compressRel`), while in degree `0` the same
  compression joins every point of `Z` to the image of `X`;
* **the fibre inclusion is surjective on `π_{n+1}`**: the long exact sequence of the pair
  (`Work.RatHurewicz.pair_les`) at `π_{n+1}(X)` reads
  `π_{n+1}(Z) → π_{n+1}(F) → π_{n+1}(X) → π_{n+1}(Z)`, and `π_{n+1}(Z) = 0` by the range model
  property, so exactness makes the middle map onto.
-/

open scoped Topology

namespace Work.RatHurewicz

noncomputable section

/-! ## Degree zero: compression into a set joins every point to it -/

/-- **Every point of `Y` is joined to `A`** when the pair `(Y,A)` compresses in dimension zero: the
compression of the constant `0`-cube at `y` is a path from `y` into `A`. -/
theorem joined_of_compressRel_zero {Y : Type} [TopologicalSpace Y] {A : Set Y}
    (h : CompressRel Y A 0) (y : Y) : ∃ a : ↥A, Joined y (a : Y) := by
  have hb : ∀ x : ICube 0, x ∈ Cube.boundary (Fin 0) →
      (ContinuousMap.const (ICube 0) y) x ∈ A := fun x hx => by
    obtain ⟨i, -⟩ := hx
    exact i.elim0
  have hx₀ : ICube 0 := fun i => i.elim0
  obtain ⟨G, hG0, _hGb, hG1⟩ := h (ContinuousMap.const (ICube 0) y) hb
  let γ : Path y (G (hx₀, 1)) :=
    { toContinuousMap := ⟨fun t => G (hx₀, t),
        G.continuous.comp (continuous_const.prodMk continuous_id)⟩
      source' := hG0 hx₀
      target' := rfl }
  exact ⟨⟨G (hx₀, 1), hG1 hx₀⟩, ⟨γ⟩⟩

/-- **Dimension-zero compression makes `Y` connected** as soon as `A` is. -/
theorem subsingleton_zerothHomotopy_of_compressRel_zero {Y : Type} [TopologicalSpace Y] {A : Set Y}
    (h : CompressRel Y A 0) (hA : Subsingleton (ZerothHomotopy ↥A)) :
    Subsingleton (ZerothHomotopy Y) := by
  refine ⟨fun u v => ?_⟩
  induction u using ZerothHomotopy.rec with
  | mk y =>
    induction v using ZerothHomotopy.rec with
    | mk y' =>
      obtain ⟨a, ha⟩ := joined_of_compressRel_zero h y
      obtain ⟨a', ha'⟩ := joined_of_compressRel_zero h y'
      have hAA : Joined a a' :=
        Quotient.exact (Subsingleton.elim (ZerothHomotopy.mk a) (ZerothHomotopy.mk a'))
      exact ZerothHomotopy.sound ((ha.trans (hAA.map continuous_subtype_val)).trans ha'.symm).somePath

/-! ## Transport of the vanishing of homotopy groups to the range of an embedding -/

/-- **The homotopy groups of `X` and of the range of an embedding `f : X → Y`** vanish
simultaneously: the range of an embedding is homeomorphic to `X`, and a homotopy equivalence induces
an isomorphism of homotopy groups (`Work.Stems.mulEquiv_of_homotopyEquiv`). -/
theorem subsingleton_homotopyGroup_range_of_isEmbedding {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (x₀ : X) (hf : Topology.IsEmbedding (f : X → Y)) (j : ℕ)
    [Nonempty (Fin j)] (h : Subsingleton (HomotopyGroup (Fin j) X x₀)) :
    Subsingleton (HomotopyGroup (Fin j) ↥(Set.range (f : X → Y)) ⟨f x₀, x₀, rfl⟩) := by
  have hbase : hf.toHomeomorph x₀ = (⟨f x₀, x₀, rfl⟩ : Set.range (f : X → Y)) :=
    Subtype.ext (by simp)
  obtain ⟨e⟩ := Work.Stems.mulEquiv_of_homotopyEquiv (N := Fin j)
    hf.toHomeomorph.toHomotopyEquiv x₀
  have h' : Subsingleton (HomotopyGroup (Fin j) ↥(Set.range (f : X → Y))
      (hf.toHomeomorph.toHomotopyEquiv.toFun x₀)) :=
    ⟨fun u v => e.symm.injective (h.elim (e.symm u) (e.symm v))⟩
  rwa [show hf.toHomeomorph.toHomotopyEquiv.toFun x₀ = hf.toHomeomorph x₀ from rfl, hbase] at h'

/-! ## The tower data -/

/-- **The tower data of the truncation step.** -/
theorem towerStepData : TowerStepData := by
  intro k n hk hkn hr X _ x₀ hconn
  let st := towerState (x₀ := x₀) (k := k) hk (2 * k - 1 - k)
  -- the range model condition
  have hmodel : IsRangeKModel k (2 * k - 1) (st.incl x₀) := by
    intro j hj hjne
    rcases lt_or_gt_of_ne hjne with hlt | hgt
    · -- `j < k`: compression pushes cubes of `Z` into the range of `inc`, which is `X`
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · -- `j = 0`: `Z` is connected
        subst hj0
        haveI hπ0 : Subsingleton (HomotopyGroup (Fin 0) X x₀) := hconn 0 (by omega)
        haveI hXZ : Subsingleton (ZerothHomotopy X) :=
          (HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x₀)).surjective.subsingleton
        have hAZ : Subsingleton (ZerothHomotopy ↥(Set.range (st.incl : X → st.Y))) := by
          have key : ∀ a : Set.range (st.incl : X → st.Y),
              ZerothHomotopy.mk a = ZerothHomotopy.mk
                (⟨st.incl x₀, x₀, rfl⟩ : Set.range (st.incl : X → st.Y)) := by
            intro a
            have hj : Joined a.2.choose x₀ :=
              Quotient.exact (Subsingleton.elim (ZerothHomotopy.mk a.2.choose)
                (ZerothHomotopy.mk x₀))
            have h1 : Joined (⟨st.incl a.2.choose, a.2.choose, rfl⟩ : Set.range (st.incl : X → st.Y))
                ⟨st.incl x₀, x₀, rfl⟩ :=
              hj.map (f := fun x => (⟨st.incl x, x, rfl⟩ : Set.range (st.incl : X → st.Y)))
                (by fun_prop)
            have h2 : a = (⟨st.incl a.2.choose, a.2.choose, rfl⟩ : Set.range (st.incl : X → st.Y)) :=
              Subtype.ext a.2.choose_spec.symm
            rw [h2]
            exact ZerothHomotopy.sound h1.somePath
          refine ⟨fun u v => ?_⟩
          induction u using ZerothHomotopy.rec with
          | mk a =>
            induction v using ZerothHomotopy.rec with
            | mk b => rw [key a, key b]
        haveI hYZ : Subsingleton (ZerothHomotopy st.Y) :=
          subsingleton_zerothHomotopy_of_compressRel_zero (st.compress 0 (by omega)) hAZ
        exact (HomotopyGroup.pi0EquivZerothHomotopy (X := st.Y) (x := st.incl x₀)).symm.surjective.subsingleton
      · -- `1 ≤ j < k`
        have hA : Subsingleton (HomotopyGroup (Fin (j - 1 + 1))
            ↥(Set.range (st.incl : X → st.Y)) ⟨st.incl x₀, x₀, rfl⟩) :=
          subsingleton_homotopyGroup_range_of_isEmbedding (j := j - 1 + 1) st.incl x₀ st.emb
            (hconn (j - 1 + 1) (by omega))
        have hbij := bijective_πmap_setIncl_of_compressRel
          (A := Set.range (st.incl : X → st.Y)) ⟨st.incl x₀, x₀, rfl⟩ (k + 1)
          (fun d hd => st.compress d (by omega)) (j - 1) (by omega)
        have hS : Subsingleton (HomotopyGroup (Fin (j - 1 + 1)) st.Y (st.incl x₀)) := by
          haveI := hA
          exact hbij.2.subsingleton
        rwa [show j - 1 + 1 = j from by omega] at hS
    · -- `k < j`: the killing recorded by the tower
      exact st.killed j hgt (by omega)
  -- the fibre is `k`-connected
  have hfib : ∀ j : ℕ, j ≤ k → Subsingleton (HomotopyGroup (Fin j) (homotopyFibre st.incl x₀)
      (homotopyFibreBasepoint st.incl x₀)) := by
    intro j hj
    have hset : Subsingleton (RelHomotopyGroup
        (setIncl (Set.range (st.incl : X → st.Y))) ⟨st.incl x₀, x₀, rfl⟩ j) :=
      subsingleton_relPi_of_compressRel (Y := st.Y) (A := Set.range (st.incl : X → st.Y)) k
        ⟨st.incl x₀, x₀, rfl⟩ st.compress j hj
    exact subsingleton_relPi_of_isEmbedding st.incl x₀ st.emb j hset
  refine ⟨st.Y, st.inst, st.incl, hmodel, hfib, ?_⟩
  -- the fibre inclusion is onto in degree `n+1`
  have hs' : Function.Surjective (Work.StemsB.πmap (homotopyFibreFst st.incl x₀) (n - 1 + 1)
      (homotopyFibreBasepoint st.incl x₀)) := by
    intro a
    have hZ : Subsingleton (HomotopyGroup (Fin ((n - 1 + 1) + 1)) st.Y (st.incl x₀)) :=
      hmodel ((n - 1 + 1) + 1) (by omega) (by omega)
    obtain ⟨del, d, -, h2, -, -⟩ := pair_les st.incl x₀ (n - 1) (by omega)
    exact (h2 a).mp (hZ.elim _ 1)
  have hidx : n - 1 + 1 = n := by omega
  exact hidx ▸ hs'

end

end Work.RatHurewicz
