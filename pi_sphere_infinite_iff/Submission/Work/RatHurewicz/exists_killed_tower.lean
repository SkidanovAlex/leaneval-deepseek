import Mathlib
import Submission.Work.RatHurewicz.AttachCells
import Submission.Work.RatHurewicz.AttachKill
import Submission.Work.RatHurewicz.attachCells_piMap_bijective
import Submission.Work.RatHurewicz.killFamily_subsingleton
import Submission.Work.RatHurewicz.compressRel_attachCells_range
import Submission.Work.RatHurewicz.attachIncl_isOpenMap_range
import Submission.Work.RatHurewicz.CompressRelToRelPi

/-!
# The truncation tower: killing `π_{> k}` without changing `π_{≤ k}`

Area **RATHUREWICZ**, C0/K1 of the Serre blueprint (`Submission/Work/Drive/SERRE_BLUEPRINT.md`).
This file iterates the single-step cell attachment `Work.RatHurewicz.attachCells` (killing
`π_{i+1}` by attaching one `(i+2)`-cell per element) over the range `i = k, …, N-1` and assembles
the two properties of the resulting map:

* `Work.RatHurewicz.fibreHomeoOfIsEmbedding` / `subsingleton_relPi_of_isEmbedding` — the abstract
  transport of the vanishing of relative homotopy groups from the inclusion of the range of an
  embedding to the embedding itself;
* `Work.RatHurewicz.compressRel_attachIncl_comp` — the one-step compression transfer: given the
  compression property of the pair `(Y, range g)`, the attachment of `(n+2)`-cells to `Y` inherits
  the compression property of `(Y', range (attachIncl ∘ g))`;
* `Work.RatHurewicz.TowerState`, `initState`, `stepState`, `towerState` — the tower of spaces
  `Y_0 = X ⊆ Y_1 ⊆ ⋯ ⊆ Y_{N-k}` with `Y_{s+1} := attachCells (k+s) Y_s π_{k+s+1}(Y_s) killFamily`,
  carrying the compression property, the `IsEmbedding` of the composite inclusion and the record of
  which homotopy groups have been killed;
* `Work.RatHurewicz.exists_killed_tower` — the assembled statement.
-/

set_option linter.style.haveILetI false

open scoped Topology Topology.Homotopy unitInterval
open Work.StemsB (PathSpace evalOne)

namespace Work.RatHurewicz

noncomputable section

/-! ## Step 0: the homotopy fibres of an embedding and of the inclusion of its range -/

/-- **The homotopy fibres of an embedding and of the inclusion of its range are homeomorphic.**
Both are spaces of pairs `(point, path)` with the *same* path space, and the first coordinates are
identified by the homeomorphism `Topology.IsEmbedding.toHomeomorph`. -/
def fibreHomeoOfIsEmbedding {A X : Type} [TopologicalSpace A] [TopologicalSpace X]
    (f : C(A, X)) (a₀ : A) (hf : Topology.IsEmbedding (f : A → X)) :
    (homotopyFibre f a₀) ≃ₜ
    (homotopyFibre (setIncl (Set.range (f : A → X))) ⟨f a₀, a₀, rfl⟩) where
  toFun p :=
    ⟨(⟨f p.1.1, p.1.1, rfl⟩, p.1.2), by
      show (evalOne X (f a₀)) p.1.2
        = setIncl (Set.range (f : A → X)) ⟨f p.1.1, p.1.1, rfl⟩
      have h1 : (setIncl (Set.range (f : A → X)) ⟨f p.1.1, p.1.1, rfl⟩ : X) = f p.1.1 := rfl
      rw [h1]
      exact p.2⟩
  invFun q := ⟨(hf.toHomeomorph.symm q.1.1, q.1.2), by
      show (evalOne X (f a₀)) q.1.2 = f (hf.toHomeomorph.symm q.1.1)
      have h1 : f (hf.toHomeomorph.symm q.1.1)
          = ((hf.toHomeomorph (hf.toHomeomorph.symm q.1.1) : Set.range (f : A → X)) : X) := rfl
      rw [h1, Homeomorph.apply_symm_apply]
      exact q.2⟩
  left_inv p := by
    refine Subtype.ext (Prod.ext ?_ rfl)
    exact hf.toHomeomorph.symm_apply_apply p.1.1
  right_inv q := by
    refine Subtype.ext (Prod.ext (Subtype.ext ?_) rfl)
    exact congrArg Subtype.val (hf.toHomeomorph.apply_symm_apply q.1.1)
  continuous_toFun := Continuous.subtype_mk
    (Continuous.prodMk
      (Continuous.subtype_mk
        (f.continuous.comp (continuous_fst.comp continuous_subtype_val))
        (fun p => ⟨p.1.1, rfl⟩))
      (continuous_snd.comp continuous_subtype_val))
    (fun p => by
      show (evalOne X (f a₀)) p.1.2
        = setIncl (Set.range (f : A → X)) ⟨f p.1.1, p.1.1, rfl⟩
      have h1 : (setIncl (Set.range (f : A → X)) ⟨f p.1.1, p.1.1, rfl⟩ : X) = f p.1.1 := rfl
      rw [h1]
      exact p.2)
  continuous_invFun := Continuous.subtype_mk
    (Continuous.prodMk
      (hf.toHomeomorph.symm.continuous.comp (continuous_fst.comp continuous_subtype_val))
      (continuous_snd.comp continuous_subtype_val))
    (fun q => by
      show (evalOne X (f a₀)) q.1.2 = f (hf.toHomeomorph.symm q.1.1)
      have h1 : f (hf.toHomeomorph.symm q.1.1)
          = ((hf.toHomeomorph (hf.toHomeomorph.symm q.1.1) : Set.range (f : A → X)) : X) := rfl
      rw [h1, Homeomorph.apply_symm_apply]
      exact q.2)

/-- **Transport of the vanishing of relative homotopy groups from the inclusion of the range.**
If `f : C(A,X)` is an embedding and the relative homotopy group of the pair `(range f ⊆ X)`
(i.e. of `setIncl (range f)`) vanishes in degree `j`, then so does the relative homotopy group of
`f` itself (the homotopy group of the homotopy fibre of `f`).  This is the general form of
`Work.RatHurewicz.subsingleton_relPi_attachIncl_of_range`. -/
theorem subsingleton_relPi_of_isEmbedding {A X : Type} [TopologicalSpace A] [TopologicalSpace X]
    (f : C(A, X)) (a₀ : A) (hf : Topology.IsEmbedding (f : A → X)) (j : ℕ)
    (h : Subsingleton (RelHomotopyGroup (setIncl (Set.range (f : A → X)))
      ⟨f a₀, a₀, rfl⟩ j)) :
    Subsingleton (RelHomotopyGroup f a₀ j) := by
  have hbase : (fibreHomeoOfIsEmbedding f a₀ hf) (homotopyFibreBasepoint f a₀)
      = homotopyFibreBasepoint (setIncl (Set.range (f : A → X))) ⟨f a₀, a₀, rfl⟩ := rfl
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    have hZ : Subsingleton (ZerothHomotopy (homotopyFibre
        (setIncl (Set.range (f : A → X))) ⟨f a₀, a₀, rfl⟩)) := by
      haveI := h
      refine ⟨fun u v => ?_⟩
      let ex := homotopyGroupEquivZerothHomotopyOfIsEmpty (N := Fin 0)
        (X := homotopyFibre (setIncl (Set.range (f : A → X))) ⟨f a₀, a₀, rfl⟩)
        (homotopyFibreBasepoint (setIncl (Set.range (f : A → X))) ⟨f a₀, a₀, rfl⟩)
      exact ex.symm.injective (Subsingleton.elim (ex.symm u) (ex.symm v))
    have hZ' : Subsingleton (ZerothHomotopy (homotopyFibre f a₀)) :=
      subsingleton_zerothHomotopy_of_homotopyEquiv
        (fibreHomeoOfIsEmbedding f a₀ hf).toHomotopyEquiv hZ
    haveI := hZ'
    refine ⟨fun u v => ?_⟩
    let ex := homotopyGroupEquivZerothHomotopyOfIsEmpty (N := Fin 0)
      (X := homotopyFibre f a₀) (homotopyFibreBasepoint f a₀)
    exact ex.injective (Subsingleton.elim (ex u) (ex v))
  · haveI : Nonempty (Fin j) := ⟨⟨0, hj⟩⟩
    obtain ⟨me⟩ := Work.Stems.mulEquiv_of_homotopyEquiv (N := Fin j)
      (fibreHomeoOfIsEmbedding f a₀ hf).toHomotopyEquiv (homotopyFibreBasepoint f a₀)
    have hbase' : (fibreHomeoOfIsEmbedding f a₀ hf).toHomotopyEquiv.toFun
        (homotopyFibreBasepoint f a₀)
        = homotopyFibreBasepoint (setIncl (Set.range (f : A → X))) ⟨f a₀, a₀, rfl⟩ := hbase
    have h' : Subsingleton (HomotopyGroup (Fin j)
        (homotopyFibre (setIncl (Set.range (f : A → X))) ⟨f a₀, a₀, rfl⟩)
        ((fibreHomeoOfIsEmbedding f a₀ hf).toHomotopyEquiv.toFun
          (homotopyFibreBasepoint f a₀))) := hbase' ▸ h
    haveI := h'
    exact ⟨fun a b => me.injective (Subsingleton.elim (me a) (me b))⟩

/-! ## Step 1: the one-step compression transfer -/

/-- **Attaching `(n+2)`-cells preserves the compression property of the range of a map.**
If every map of pairs `(I^d, ∂I^d) → (Y, range g)` is homotopic, relative to the boundary, into
`range g`, then every map of pairs `(I^d, ∂I^d) → (attachCells n Y ι f, range (attachIncl ∘ g))` is
homotopic, relative to the boundary, into `range (attachIncl ∘ g)`.

First compress the cube into `range attachIncl` (`Work.RatHurewicz.compressRel_attachCells_range`,
available since `d ≤ n+1`), factor the end map through the homeomorphism
`Work.RatHurewicz.rangeHomeo : Y ≃ₜ range attachIncl`, apply the compression of `g` there and
re-attach.  The boundary condition is preserved because both compressions are relative to the
boundary and `attachIncl` is injective. -/
theorem compressRel_attachIncl_comp {X : Type} [TopologicalSpace X]
    (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) (g : C(X, Y)) (d : ℕ) (hd : d ≤ n + 1)
    (hg : CompressRel Y (Set.range (g : X → Y)) d) :
    CompressRel (attachCells n Y ι f)
      (Set.range (((attachIncl n Y ι f).comp g) : X → attachCells n Y ι f)) d := by
  intro φ hφ
  obtain ⟨G₁, hG₁0, hG₁b, hG₁1⟩ :=
    compressRel_attachCells_range n Y ι f d hd φ
      (fun x hx => by obtain ⟨x', hx'⟩ := hφ x hx; exact ⟨g x', hx'⟩)
  have hc₁ : Continuous fun x : ICube d =>
      (⟨G₁ (x, 1), hG₁1 x⟩ : ↥(Set.range (attachIncl n Y ι f))) :=
    Continuous.subtype_mk (G₁.continuous.comp (continuous_id.prodMk continuous_const))
      (fun x => hG₁1 x)
  let φ₁ : C(ICube d, Y) :=
    ⟨fun x => (rangeHomeo n Y ι f).symm ⟨G₁ (x, 1), hG₁1 x⟩,
      (rangeHomeo n Y ι f).symm.continuous.comp hc₁⟩
  have key1 : ∀ x : ICube d, attachIncl n Y ι f (φ₁ x) = G₁ (x, 1) := fun x =>
    rangeHomeo_symm_apply_attachIncl n Y ι f ⟨G₁ (x, 1), hG₁1 x⟩
  have hbnd₁ : ∀ x, x ∈ Cube.boundary (Fin d) → φ₁ x ∈ Set.range (g : X → Y) := by
    intro x hx
    obtain ⟨a, ha⟩ := hφ x hx
    refine ⟨a, AttachRange.attachIncl_injective n Y ι f ?_⟩
    rw [key1 x, hG₁b x hx 1]
    exact ha
  obtain ⟨G₂, hG₂0, hG₂b, hG₂1⟩ := hg φ₁ hbnd₁
  refine ⟨⟨fun p : ICube d × I =>
    if (2 : ℝ) * (p.2 : ℝ) ≤ 1 then G₁ (p.1, clampI (2 * (p.2 : ℝ)))
    else attachIncl n Y ι f (G₂ (p.1, clampI (2 * (p.2 : ℝ) - 1))), ?_⟩, ?_, ?_, ?_⟩
  · refine Continuous.if_le ?_ ?_ ?_ ?_ ?_
    · exact G₁.continuous.comp (continuous_fst.prodMk (continuous_clampI.comp (by fun_prop)))
    · exact (attachIncl n Y ι f).continuous.comp
        (G₂.continuous.comp (continuous_fst.prodMk (continuous_clampI.comp (by fun_prop))))
    · exact continuous_const.mul (continuous_subtype_val.comp continuous_snd)
    · exact continuous_const
    · intro p hp
      have h1 : clampI (2 * (p.2 : ℝ)) = (1 : I) := by rw [hp, clampI_one']
      have h2 : clampI (2 * (p.2 : ℝ) - 1) = (0 : I) := by
        have h2' : 2 * (p.2 : ℝ) - 1 = 0 := by rw [hp]; norm_num
        rw [h2', clampI_zero']
      rw [h1, h2, hG₂0 p.1]
      exact (key1 p.1).symm
  · intro x
    change (if (2 : ℝ) * (((0 : I)) : ℝ) ≤ 1 then G₁ (x, clampI (2 * (((0 : I)) : ℝ)))
      else attachIncl n Y ι f (G₂ (x, clampI (2 * (((0 : I)) : ℝ) - 1)))) = φ x
    rw [if_pos (by norm_num), show (2 : ℝ) * (((0 : I)) : ℝ) = 0 by norm_num, clampI_zero']
    exact hG₁0 x
  · intro x hx t
    change (if (2 : ℝ) * (t : ℝ) ≤ 1 then G₁ (x, clampI (2 * (t : ℝ)))
      else attachIncl n Y ι f (G₂ (x, clampI (2 * (t : ℝ) - 1)))) = φ x
    by_cases hle : (2 : ℝ) * (t : ℝ) ≤ 1
    · rw [if_pos hle]; exact hG₁b x hx _
    · rw [if_neg hle, hG₂b x hx, key1 x]
      exact hG₁b x hx 1
  · intro x
    change (if (2 : ℝ) * (((1 : I)) : ℝ) ≤ 1 then G₁ (x, clampI (2 * (((1 : I)) : ℝ)))
      else attachIncl n Y ι f (G₂ (x, clampI (2 * (((1 : I)) : ℝ) - 1))))
      ∈ Set.range ((attachIncl n Y ι f).comp g)
    rw [if_neg (by norm_num : ¬ (2 : ℝ) * (((1 : I)) : ℝ) ≤ 1),
      show 2 * (((1 : I)) : ℝ) - 1 = 1 by norm_num, clampI_one']
    obtain ⟨a, ha⟩ := hG₂1 x
    exact ⟨a, congrArg (attachIncl n Y ι f) ha⟩

/-! ## Step 2: the tower of spaces -/

/-- **The state of the truncation tower at stage `s`** (the space `Y_s` obtained after `s`
attachments, starting from `X`): the total space, its topology, the composite inclusion from `X`
(which is an embedding), the compression property of the pair `(Y_s, range incl)` in the range
`d ≤ k+1`, and the record of the homotopy groups already killed, `π_j(Y_s) = 0` for
`k < j ≤ k + s`. -/
structure TowerState (X : Type) [TopologicalSpace X] (x₀ : X) (k : ℕ) (s : ℕ) where
  Y : Type
  inst : TopologicalSpace Y
  incl : @ContinuousMap X Y _ inst
  emb : @Topology.IsEmbedding X Y _ inst incl
  compress : ∀ d, d ≤ k + 1 → @CompressRel Y inst (Set.range incl) d
  killed : ∀ j, k < j → j ≤ k + s → Subsingleton (HomotopyGroup (Fin j) Y (incl x₀))

attribute [instance] TowerState.inst

/-- The initial stage `Y_0 = X`: the identity embedding, the trivial compression (`range id` is
everything, so the constant homotopy compresses) and no killing yet. -/
def initState {X : Type} [TopologicalSpace X] (x₀ : X) (k : ℕ) : TowerState X x₀ k 0 where
  Y := X
  inst := inferInstance
  incl := ContinuousMap.id X
  emb := Topology.IsEmbedding.id
  compress := by
    intro d hd f hf
    refine ⟨f.comp ContinuousMap.fst, fun x => rfl, fun x hx t => rfl, fun x => ?_⟩
    exact ⟨f x, rfl⟩
  killed := by intro j hj hj2; omega

/-- **One step of the tower**: attach one `(k+s+2)`-cell per element of `π_{k+s+1}(Y_s)`.

The compression property is transferred by `Work.RatHurewicz.compressRel_attachIncl_comp`; the
composite inclusion stays an embedding because `attachIncl` is one; the killed groups are those of
the previous stage (which survive by `Work.RatHurewicz.attachCells_piMap_bijective`, since the
attached cells have dimension `k+s+2 > j` for `j ≤ k+s`, and `j > k ≥ 2`) together with the newly
killed `π_{k+s+1}` (`Work.RatHurewicz.killFamily_subsingleton`). -/
def stepState {X : Type} [TopologicalSpace X] {x₀ : X} {k : ℕ} (hk : 2 ≤ k)
    {s : ℕ} (st : TowerState X x₀ k s) : TowerState X x₀ k (s + 1) :=
  let ι := HomotopyGroup (Fin (k + s + 1)) st.Y (st.incl x₀)
  let f : ι → C(cellSphere (k + s), st.Y) := killFamily (k + s) st.Y (st.incl x₀)
  { Y := attachCells (k + s) st.Y ι f
    inst := inferInstance
    incl := (attachIncl (k + s) st.Y ι f).comp st.incl
    emb := by
      have hAtt : Topology.IsEmbedding ⇑(attachIncl (k + s) st.Y ι f) :=
        ⟨isInducing_attachIncl (k + s) st.Y ι f,
          AttachRange.attachIncl_injective (k + s) st.Y ι f⟩
      exact hAtt.comp st.emb
    compress := fun d hd =>
      compressRel_attachIncl_comp (k + s) st.Y ι f st.incl d (by omega) (st.compress d hd)
    killed := by
      intro j hj hjle
      by_cases hle : j ≤ k + s
      · have hjj : j - 1 + 1 = j := by omega
        have hbij := attachCells_piMap_bijective (k + s) st.Y ι f (st.incl x₀) (j - 1)
          (by omega) (by omega)
        haveI : Subsingleton (HomotopyGroup (Fin (j - 1 + 1)) st.Y (st.incl x₀)) :=
          hjj.symm ▸ st.killed j hj hle
        exact hjj ▸ hbij.2.subsingleton
      · have hje : j = k + s + 1 := by omega
        subst hje
        exact killFamily_subsingleton (k + s) st.Y (st.incl x₀) }

/-- The tower of spaces `Y_s`, `s = 0, …, N-k`, with `Y_0 = X` and one attachment at each step. -/
def towerState {X : Type} [TopologicalSpace X] {x₀ : X} {k : ℕ} (hk : 2 ≤ k) :
    (s : ℕ) → TowerState X x₀ k s
  | 0 => initState x₀ k
  | s + 1 => stepState hk (towerState hk s)

/-! ## Step 3: the assembled theorem -/

/-- **The truncation tower: killing `π_{> k}` without changing `π_{≤ k}`.**

For a space `X`, a base point `x₀ : X` and integers `2 ≤ k ≤ N`, there are a space `Z`, a base point
`inc x₀` (the image of `x₀` under the structure map) and a continuous map `inc : X → Z` such that

* the homotopy fibre of `inc` is `k`-connected, i.e. `RelHomotopyGroup inc x₀ j` is trivial for
  `j ≤ k` (in this area's indexing `RelHomotopyGroup inc x₀ j` is the classical `π_{j+1}(Z,X)`, so
  this says that every `π_i(Z,X)` vanishes for `i ≤ k+1`: `inc` is an isomorphism on `π_{≤ k}` in
  the sense of the long exact sequence of the pair), and
* `π_j(Z)` is trivial for `k < j ≤ N` — the higher homotopy of `X` is killed in the bounded range
  `≤ N`.

**Construction.**  Iterate the cell attachment: `Y_0 := X`,
`Y_{s+1} := attachCells (k+s) Y_s (HomotopyGroup (Fin (k+s+1)) Y_s y_s) (killFamily …)`,
`y_{s+1} := attachIncl … y_s`, and `inc :=` the composite of the inclusions.  The first clause
follows from the compression property of the pair `(Y_{N-k}, range inc)` maintained by
`Work.RatHurewicz.compressRel_attachIncl_comp` via
`Work.RatHurewicz.subsingleton_relPi_of_compressRel` and
`Work.RatHurewicz.subsingleton_relPi_of_isEmbedding`; the second from
`Work.RatHurewicz.killFamily_subsingleton` and
`Work.RatHurewicz.attachCells_piMap_bijective`. -/
theorem exists_killed_tower (X : Type) [TopologicalSpace X] (x₀ : X) (k N : ℕ) (hk : 2 ≤ k)
    (hN : k ≤ N) :
    ∃ (Z : Type) (_ : TopologicalSpace Z) (inc : C(X, Z)),
      (∀ j : ℕ, j ≤ k → Subsingleton (RelHomotopyGroup inc x₀ j)) ∧
        (∀ j : ℕ, k < j → j ≤ N → Subsingleton (HomotopyGroup (Fin j) Z (inc x₀))) := by
  let st := towerState (x₀ := x₀) (k := k) hk (N - k)
  refine ⟨st.Y, st.inst, st.incl, ?_, ?_⟩
  · intro j hj
    have hset : Subsingleton (RelHomotopyGroup
        (setIncl (Set.range (st.incl : X → st.Y))) ⟨st.incl x₀, x₀, rfl⟩ j) :=
      subsingleton_relPi_of_compressRel (Y := st.Y) (A := Set.range (st.incl : X → st.Y)) k
        ⟨st.incl x₀, x₀, rfl⟩ st.compress j hj
    exact subsingleton_relPi_of_isEmbedding st.incl x₀ st.emb j hset
  · intro j hj hjN
    exact st.killed j hj (by omega)

end

end Work.RatHurewicz
